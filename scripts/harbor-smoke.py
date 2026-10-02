#!/usr/bin/env python3
"""Harbor 0.9.0 Docker E2E: reference, immutable GLM, and focused tasks."""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import uuid

ROOT = Path(__file__).resolve().parents[1]
p = argparse.ArgumentParser()
p.add_argument('--harbor', default='harbor')
p.add_argument('--agent-image', default='security-agent:v2')
p.add_argument('--verifier-image', default='security-verifier:v2')
p.add_argument('--output', type=Path, default=ROOT/'evidence/harbor')
a = p.parse_args()
subprocess.run(['docker','compose','version'], check=True)
a.output = a.output.resolve()
if a.output.exists():
    raise SystemExit(f'use a fresh output directory: {a.output}')
a.output.mkdir(parents=True)
summary = {'harbor_version':subprocess.check_output([a.harbor,'--version'],text=True).strip(), 'trials':{}}
if summary['harbor_version'] != '0.9.0': raise SystemExit('Harbor 0.9.0 required')


def image_id(name):
    return subprocess.check_output(['docker','image','inspect',name,'--format','{{.Id}}'],text=True).strip()


agent_id, verifier_id = image_id(a.agent_image), image_id(a.verifier_image)
summary['images'] = {'agent':agent_id,'verifier':verifier_id}


def trial(task, label, expected, agent):
    # Harbor 0.9.0 downs prebuilt images with --rmi all. Disposable tags keep
    # the caller's canonical tags intact across trials and repeat executions.
    token = uuid.uuid4().hex[:12]
    tags = [f'security-smoke-agent:{token}', f'security-smoke-verifier:{token}']
    for source, tag in zip((agent,verifier_id),tags):
        subprocess.run(['docker','tag',source,tag],check=True)
    try:
        manifest = task/'task.toml'
        text = manifest.read_text().replace('[environment]',f'[environment]\ndocker_image = "{tags[0]}"')
        text = text.replace('[verifier.environment]',f'[verifier.environment]\ndocker_image = "{tags[1]}"')
        manifest.write_text(text)
        subprocess.run([a.harbor,'run','-p',str(task),'-a','oracle','-e','docker','-n','1',
                        '--job-name',label,'--jobs-dir',str(a.output),'--quiet'],check=True)
        results = list((a.output/label).glob('*/result.json'))
        if len(results) != 1: raise RuntimeError(f'{label}: expected one result, found {results}')
        result = json.loads(results[0].read_text())
        rewards = (result.get('verifier_result') or {}).get('rewards',{})
        if result.get('exception_info') or rewards.get('reward') != expected:
            raise RuntimeError(f'{label}: reward={rewards}, exception={result.get("exception_info")}')
        details = json.loads((results[0].parent/'verifier/details.json').read_text())
        if details['status'] != 'ok' or details['reward'] != expected: raise RuntimeError(details)
        # The separate verifier must receive verbatim solution artifacts.
        for name, rel in [('spec','spec.json'),('counterexample','counterexample.json'),('patch','src/lib.rs'),('proof','Proof.lean')]:
            actual = details['checkpoints'][name].get('artifact_sha256')
            if actual:
                intended = hashlib.sha256((task/'solution'/rel).read_bytes()).hexdigest()
                if actual != intended: raise RuntimeError(f'{label}: {name} changed during artifact copy')
        (a.output/(label+'-details.json')).write_text(json.dumps(details,indent=2)+'\n')
        summary['trials'][label] = {'reward':expected,'exception':None,'task_checksum':result['task_checksum'],
                                  'profile':details['profile'],'agent_image':agent,'verifier_image':verifier_id,
                                  'statuses':{k:v['status'] for k,v in details['checkpoints'].items()},
                                  'artifact_sha256':{k:v.get('artifact_sha256') for k,v in details['checkpoints'].items()}}
        print(f'Harbor 0.9.0 {label}: reward={expected:.2f}', flush=True)
    finally:
        for tag in tags:
            subprocess.run(['docker','image','rm',tag],stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL)


with tempfile.TemporaryDirectory(prefix='harbor-semantic-v2-') as raw:
    raw = Path(raw)
    for label, expected in [('reference',1.0),('glm',.6)]:
        task = raw/label
        shutil.copytree(ROOT/'task',task,ignore=shutil.ignore_patterns('.lake','__pycache__','target','LocalProof.lean'))
        if label == 'glm':
            fixture = ROOT/'scripts/fixtures/glm-5.3-flash/submission'
            for rel in ('spec.json','counterexample.json','src/lib.rs','Proof.lean'):
                shutil.copy(fixture/rel,task/'solution'/rel)
        trial(task,label,expected,agent_id)
    family = raw/'family'
    subprocess.run([sys.executable,str(ROOT/'scripts/make-family.py'),str(family)],check=True)
    # Build the actual discovery agent image; it starts from Rust, without Lean.
    discovery_tag = 'security-discovery:v2'
    task = family/'overflow-specify'
    subprocess.run(['docker','build','-t',discovery_tag,'-f',str(task/'environment/Dockerfile'),str(task/'environment')],check=True)
    discovery_id = image_id(discovery_tag)
    summary['images']['discovery'] = discovery_id
    subprocess.run(['docker','run','--rm','--network','none',discovery_tag,'python3','-c',
                    'from pathlib import Path; import shutil; assert not Path("/workspace/lean").exists(); assert shutil.which("lean") is None'],check=True)
    for profile in ('specify','refute','repair','prove'):
        trial(family/('overflow-'+profile),profile,1.0,discovery_id if profile in ('specify','refute') else agent_id)
    # Focused partial credit must also survive the full Harbor path.
    task = raw/'glm-specify'
    shutil.copytree(family/'overflow-specify',task)
    # Remove the previous disposable image lines before trial() injects new ones.
    manifest = task/'task.toml'
    manifest.write_text('\n'.join(line for line in manifest.read_text().splitlines() if not line.startswith('docker_image = '))+'\n')
    shutil.copy(ROOT/'scripts/fixtures/glm-5.3-flash/submission/spec.json',task/'solution/spec.json')
    trial(task,'glm-specify',.5,discovery_id)
(a.output/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
