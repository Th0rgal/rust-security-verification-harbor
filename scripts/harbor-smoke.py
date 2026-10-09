#!/usr/bin/env python3
"""Harbor 0.9.0 Docker E2E of both Lean-native reference tasks."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import uuid

ROOT=Path(__file__).resolve().parents[1]
CHALLENGE_PROBLEMS=('zk-clearing',)
ALL_PROBLEMS=('authorization','settlement','settlement-modular','settlement-engine','goldilocks','whirlpool','plonky3','succinct','openpql','ruint','zk-clearing')
p=argparse.ArgumentParser()
p.add_argument('--harbor',default='harbor')
p.add_argument('--problem',choices=('challenge','all')+ALL_PROBLEMS,default='challenge')
p.add_argument('--output',type=Path,default=ROOT/'evidence/v3/harbor')
a=p.parse_args()
if a.output.exists(): raise SystemExit('use a fresh output directory')
a.output=a.output.resolve(); a.output.mkdir(parents=True)
subprocess.run(['docker','compose','version'],check=True)
version=subprocess.check_output([a.harbor,'--version'],text=True).strip()
if version!='0.9.0': raise SystemExit('Harbor 0.9.0 required')
summary={'harbor_version':version,'trials':{}}
selected=CHALLENGE_PROBLEMS if a.problem=='challenge' else (ALL_PROBLEMS if a.problem=='all' else (a.problem,))
with tempfile.TemporaryDirectory(prefix='lean-native-harbor-') as raw:
    family=Path(raw)/'family'
    subprocess.run([sys.executable,str(ROOT/'scripts/make-family.py'),str(family),'--problem',a.problem],check=True)
    prompts=[]
    for problem in selected:
        for variant in ('vulnerable','safe'):
            task_name=problem+'-'+variant
            task=family/task_name
            prompts.append(hashlib.sha256((task/'instruction.md').read_bytes()).hexdigest())
            token=uuid.uuid4().hex[:12]
            agent='security-v3-smoke-agent:'+token
            verifier='security-v3-smoke-verifier:'+token
            for tag,folder in ((agent,'environment'),(verifier,'tests')):
                subprocess.run(['docker','build','-t',tag,'-f',str(task/folder/'Dockerfile'),str(task/folder)],check=True)
            manifest=task/'task.toml'
            text=manifest.read_text().replace('[environment]','[environment]\ndocker_image = "'+agent+'"')
            text=text.replace('[verifier.environment]','[verifier.environment]\ndocker_image = "'+verifier+'"')
            manifest.write_text(text)
            label='reference-'+task_name
            subprocess.run([a.harbor,'run','-p',str(task),'-a','oracle','-e','docker','-n','1',
                            '--job-name',label,'--jobs-dir',str(a.output),'--quiet'],check=True)
            files=list((a.output/label).glob('*/result.json'))
            if len(files)!=1: raise RuntimeError('expected exactly one result')
            result=json.loads(files[0].read_text())
            rewards=(result.get('verifier_result') or {}).get('rewards',{})
            if result.get('exception_info') or rewards.get('reward')!=1:
                raise RuntimeError({'rewards':rewards,'exception':result.get('exception_info')})
            details=json.loads((files[0].parent/'verifier/details.json').read_text())
            if details['status']!='ok' or details['reward']!=1: raise RuntimeError(details)
            for rel,actual in details['artifact_sha256'].items():
                intended=hashlib.sha256((task/'solution'/rel).read_bytes()).hexdigest()
                if actual!=intended: raise RuntimeError('artifact changed during separate-verifier copy: '+rel)
            (a.output/(label+'-details.json')).write_text(json.dumps(details,indent=2)+'\n')
            summary['trials'][task_name]={'reward':1,'prompt_sha256':prompts[-1],'checkpoints':details['checkpoints']}
            print(label+': PASS 1.00',flush=True)
    assert len(set(prompts))==1
(a.output/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')

