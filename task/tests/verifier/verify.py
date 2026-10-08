#!/usr/bin/env python3
"""Independent semantic checkpoints; isolated, fail-closed verification."""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import random
import re
import shutil
import signal
import subprocess
import sys
import tempfile
import time

import spec
import rust_symbolic
from isolation import restrict

MAX = spec.MAX
WEIGHTS = {'spec': .25, 'verdict': .15, 'proof': .25, 'response': .35}
STATUSES = ('pass', 'partial', 'fail', 'missing', 'unknown', 'timeout', 'unsupported', 'infrastructure_error')
MAX_ARTIFACT_BYTES = 65536


def read_artifact(path):
    # No links, directories, devices, or attacker-chosen verifier dependencies.
    if path.is_symlink() or path.parent.is_symlink(): raise ValueError('symlink artifact rejected')
    if not path.exists(): raise FileNotFoundError(str(path))
    if not path.is_file() or path.stat().st_size > MAX_ARTIFACT_BYTES:
        raise ValueError('artifact must be a regular file <=64 KiB')
    return path.read_text()


def json_object(text):
    def pairs(items):
        obj = {}
        for k, v in items:
            if k in obj: raise ValueError('duplicate JSON key: ' + k)
            obj[k] = v
        return obj
    obj = json.loads(text, object_pairs_hook=pairs,
                     parse_constant=lambda _: (_ for _ in ()).throw(ValueError('non-finite JSON')))
    if not isinstance(obj, dict): raise ValueError('expected JSON object')
    return obj


def run(cmd, cwd, timeout=120, *, env=None, sandbox=False, read_paths=()):
    def child():
        if sandbox:
            restrict(str(cwd), list(read_paths))
    with tempfile.TemporaryFile() as stdout, tempfile.TemporaryFile() as stderr:
        proc = subprocess.Popen(cmd, cwd=cwd, stdout=stdout, stderr=stderr, env=env,
                                start_new_session=True, preexec_fn=child if sandbox else None)
        try:
            proc.wait(timeout=timeout)
        except subprocess.TimeoutExpired:
            os.killpg(proc.pid, signal.SIGKILL); proc.wait(); raise
        finally:
            # Also terminate descendants if elaboration tried to leave a worker running.
            try: os.killpg(proc.pid, signal.SIGKILL)
            except ProcessLookupError: pass
        stdout.seek(0); stderr.seek(0)
        return subprocess.CompletedProcess(cmd, proc.returncode,
                                           stdout.read(65536).decode(errors='replace'),
                                           stderr.read(65536).decode(errors='replace'))


DRIVER = '''extern crate submitted;
use submitted::{authorize, Authorization};
fn main() {
    let args: Vec<u64> = std::env::args().skip(1).map(|x| x.parse().unwrap()).collect();
    let result: Option<Authorization> = authorize(args[0], args[1], args[2]);
    match result {
        Some(v) => { let total: u64 = v.total_debit; println!("some:{}", total); }
        None => println!("none"),
    }
}
'''


def compile_probe(source, tmp):
    rustc = shutil.which('rustc')
    if not rustc: raise RuntimeError('rustc unavailable')
    (tmp/'lib.rs').write_text(source); (tmp/'driver.rs').write_text(DRIVER)
    for cmd in ([rustc, '--edition=2021', '--crate-name', 'submitted', '--crate-type=rlib', '-O', '-C', 'overflow-checks=off', 'lib.rs'],
                [rustc, '--edition=2021', '-O', 'driver.rs', '--extern', 'submitted=libsubmitted.rlib', '-o', 'probe']):
        result = run(cmd, tmp)
        if result.returncode: raise ValueError('Rust compilation/API failed: ' + result.stderr[-2500:])
    return tmp/'probe'


def read_problem(verifier):
    path = verifier/'problem.txt'
    if not path.exists(): return 'authorization'
    problem = path.read_text().strip()
    if problem not in spec.PROBLEMS:
        raise RuntimeError('invalid trusted problem')
    return problem


def check_counterexample(text, verifier, problem=None):
    if problem is None: problem = read_problem(verifier)
    obj = json_object(text)
    if set(obj) != {'balance', 'amount', 'fee'}: raise ValueError('requires exactly balance, amount, fee')
    inputs = [obj[k] for k in ('balance', 'amount', 'fee')]
    if any(type(x) is not int or not 0 <= x <= MAX for x in inputs): raise ValueError('inputs must be u64 JSON integers')
    balance, amount, fee = inputs
    pristine = (verifier/'pristine/lib.rs').read_text()
    with tempfile.TemporaryDirectory(prefix='security-witness-') as raw:
        tmp = Path(raw); probe = compile_probe(pristine, tmp)
        result = run([str(probe), *map(str, inputs)], tmp, 5)
    math_total = spec.expected_debit_py(amount, fee, problem)
    observed = result.stdout.strip()
    if problem == 'authorization':
        expected = f'some:{(amount+fee) & MAX}'
        exploited = math_total > balance and result.returncode == 0 and observed == expected
    else:
        exploited = (math_total > balance and result.returncode == 0 and
                     observed.startswith('some:') and 0 <= int(observed.split(':', 1)[1]) <= balance)
    return {'status': 'pass' if exploited else 'fail', 'inputs': obj,
            'mathematical_total': math_total, 'pristine_observation': observed,
            'pristine_sha256': hashlib.sha256(pristine.encode()).hexdigest(),
            'reason': 'pristine release Rust authorizes an unaffordable mathematical total' if exploited else 'not a reproduced security violation'}


def check_patch(source, problem='authorization'):
    # Parse before compiling: unsupported production Rust is never executed.
    universal = rust_symbolic.check(source, problem=problem)
    with tempfile.TemporaryDirectory(prefix='security-patch-') as raw:
        tmp = Path(raw); probe = compile_probe(source, tmp)
        cases = [(0,0,0), (109,100,10), (110,100,10), (MAX,MAX,0), (0,MAX,1),
                 (MAX,MAX,1), (42,MAX-4,5), (MAX,0,MAX), (1,0,1), (0,0,1)]
        if problem.startswith('settlement'):
            cases += [
                (1660206966635476, 1617, 18446744073709540000),
                (1660206966635477, 1617, 18446744073709540000),
                (1660206966633860, 0, 18446744073709550000),
                (1660206966643861, 10000, 18446744073709550000),
            ]
        elif problem == 'goldilocks':
            cases += [
                (18446744069414584318, 0, 8589934592),
                (18446744069414584320, 0, 4294967296),
                (MAX, 1, 8589934592),
            ]
        elif problem == 'whirlpool':
            cases += [
                (MAX, 18446744073708551617, 999999),
                (MAX, 18446744073708551616, 999999),
            ]
        elif problem == 'plonky3':
            cases += [
                (4294967297, 4294967297, 1069547520),
                (2013265920, 0, 1069547520),
            ]
        elif problem == 'succinct':
            cases += [
                (128, 0, 128),
                (384, 0, 128),
                (3072, 0, 0x8080_8080_8080_8080),
            ]
        elif problem == 'openpql':
            cases += [
                (1, 2, MAX),
                (2, 2, MAX),
                (MAX // 2, 0, MAX),
            ]
        elif problem == 'ruint':
            cases += [
                (65533, 65535, 16384),
                (65534, 65535, 16384),
                (98301, 65534, 21845),
            ]
        # Include an SMT counterexample, so a universal failure is reproduced in Rust.
        if 'counterexample' in universal:
            cases.append(tuple(universal['counterexample'][k] for k in ('balance','amount','fee')))
        rng = random.Random(0xC0FFEE)
        for _ in range(128):
            amount, fee = rng.randrange(2**64), rng.randrange(2**64)
            balance = rng.randrange(2**64)
            math_tot = spec.expected_debit_py(amount, fee, problem)
            cases += [(balance,amount,fee), (min(math_tot, MAX),amount,fee)]
        concrete = {'status': 'pass', 'cases': len(cases)}
        for balance, amount, fee in cases:
            result = run([str(probe), str(balance), str(amount), str(fee)], tmp, 5)
            math_tot = spec.expected_debit_py(amount, fee, problem)
            expected = f'some:{math_tot}' if math_tot <= balance else 'none'
            if result.returncode or result.stdout.strip() != expected:
                concrete = {'status':'fail', 'inputs':dict(balance=balance, amount=amount, fee=fee),
                            'expected':expected, 'observed':result.stdout.strip(), 'returncode':result.returncode}
                break
    return {'status': universal['status'] if concrete['status']=='pass' else 'fail',
            'checks': {'compile_api': {'status':'pass'}, 'universal_equivalence':universal, 'concrete_defense':concrete}}



ALLOWED_IMPORT_PREFIXES = (
    'SecurityChallenge',
    'Lean',
    'Std',
    'Init',
    'Mathlib',
    'Batteries',
    'Aesop',
    'Qq',
)


def _is_allowed_import(mod):
    return any(mod == p or mod.startswith(p + '.') for p in ALLOWED_IMPORT_PREFIXES)


def _extra_lean_paths():
    paths = []
    deps_root = Path('/opt/rvb-deps')
    if deps_root.is_dir():
        top_lib = deps_root / '.lake/build/lib/lean'
        if top_lib.is_dir():
            paths.append(str(top_lib))
        pkgs = deps_root / 'packages'
        if pkgs.is_dir():
            for pkg_lib in sorted(pkgs.glob('*/.lake/build/lib/lean')):
                if pkg_lib.is_dir():
                    paths.append(str(pkg_lib))
    return paths


def clean_source(text, allowed_prefixes=ALLOWED_IMPORT_PREFIXES):
    # Ignore nested Lean comments for policy checks. Lean still receives source
    # and is authoritative for syntax/type checking; this is not its parser.
    text = re.sub(r'--[^\n]*', '', text)
    while '/-' in text:
        start=text.index('/-'); pos=start+2; depth=1
        while depth and pos<len(text):
            if text.startswith('/-',pos): depth+=1; pos+=2
            elif text.startswith('-/',pos): depth-=1; pos+=2
            else: pos+=1
        if depth: raise ValueError('unterminated Lean comment')
        text=text[:start]+' '+text[pos:]
    extra_imports = []
    for line in text.splitlines():
        if line.strip().startswith('import '):
            mods = line.split()[1:]
            if not mods or any(not any(m == p or m.startswith(p + '.') for p in allowed_prefixes) for m in mods):
                raise ValueError('forbidden Lean import')
            for m in mods:
                if m not in extra_imports:
                    extra_imports.append(m)
    # Additional imports cannot be smuggled inside another command.
    remaining=re.sub(r'^\s*import [^\n]*', '', text, flags=re.M)
    if re.search(r'\b(import|sorry|sorryAx|admit|axiom|unsafe|initialize|builtin_initialize|native_decide|implemented_by|extern|syntax|macro|elab)\b',remaining):
        raise ValueError('forbidden axiom/import/unsafe elaboration extension')
    return remaining, extra_imports

class LeanSession:
    """Compile in isolation, freeze .olean files, independently replay kernels.
    Each stage gets a fresh directory and only previously frozen dependencies.
    The trusted precompiled auditor imports serialized declarations as data.
    """
    def __init__(self, verifier):
        self.verifier=verifier
        self.api=verifier/'api'
        if not (self.api/'SecurityChallenge.olean').exists(): self.api=verifier/'.lake/build/lib/lean'
        self.lean=shutil.which('lean'); self.checker=shutil.which('leanchecker')
        if not self.lean or not self.checker: raise RuntimeError('Lean/leanchecker unavailable')
        if not (self.api/'SpecAudit.olean').exists(): raise RuntimeError('trusted Lean API/auditor not built')
        version=run([self.lean,'--version'],verifier,15)
        if 'version 4.31.0,' not in version.stdout: raise RuntimeError('Lean 4.31.0 required')
        self.prefix=Path(self.lean).resolve().parent.parent
        self.problem=read_problem(verifier)
        self.extra_lean_paths=_extra_lean_paths()
        self.frozen={}

    def stage(self,module,text,mode):
        cleaned, extra_imports = clean_source(text)
        import_block = ''.join(f'import {m}\n' for m in extra_imports if m != 'SecurityChallenge')
        if module=='CandidateProof':
            if re.search(r'\b(theorem|def|opaque|constant|namespace|section|end|export|attribute|set_option)\b',cleaned) or '#' in cleaned:
                raise ValueError('Proof.lean must be a proof term')
            text='import SecurityChallenge\nimport CandidateSpec\nimport CandidateAudit\nimport Lean\nimport Std\n'+import_block+'open SecurityChallenge\ntheorem auditEvidence : AuditClaim candidateSpec verdict := (\n'+cleaned+'\n)\n'
        else:
            text='import SecurityChallenge\n'+import_block+cleaned+'\n'
        with tempfile.TemporaryDirectory(prefix='lean-native-') as raw:
            tmp=Path(raw)
            for name,data in self.frozen.items(): (tmp/name).write_bytes(data)
            (tmp/(module+'.lean')).write_text(text)
            lean_path_entries = [str(self.api.resolve()), str(tmp)] + self.extra_lean_paths
            env={'PATH':str(Path(self.lean).parent)+':/usr/bin:/bin','HOME':str(tmp),
                 'LEAN_PATH':':'.join(lean_path_entries),'TMPDIR':str(tmp)}
            reads=[str(self.prefix),str(self.api.resolve()),'/usr/lib','/lib','/lib64','/dev/null','/dev/urandom']
            if Path('/opt/rvb-deps').exists():
                reads.append('/opt/rvb-deps')
            try:
                compiled=run([self.lean,'-j1','-M4096','-o',module+'.olean',module+'.lean'],tmp,120,env=env,sandbox=True,read_paths=reads)
            except subprocess.SubprocessError as exc:
                raise RuntimeError('Lean sandbox infrastructure unavailable: '+str(exc)) from exc
            artifact=tmp/(module+'.olean')
            if compiled.returncode or not artifact.is_file():
                return {'status':'fail','reason':'Lean compilation rejected artifact','diagnostic':(compiled.stdout+compiled.stderr)[-4000:]}
            if artifact.is_symlink() or artifact.stat().st_size>32*1024**2: raise ValueError('invalid Lean artifact')
            data=artifact.read_bytes()
            # Delete every file emitted by untrusted elaboration. Restore only
            # known frozen dependencies and the single serialized declaration.
            for item in tmp.iterdir():
                if item.is_dir() and not item.is_symlink(): shutil.rmtree(item)
                else: item.unlink()
            for name,previous in self.frozen.items(): (tmp/name).write_bytes(previous)
            artifact.write_bytes(data)
            replay=run([self.checker,module],tmp,120,env=env,sandbox=True,read_paths=reads)
            if replay.returncode:
                return {'status':'fail','reason':'independent kernel replay rejected artifact','diagnostic':(replay.stdout+replay.stderr)[-4000:]}
            auditor=self.verifier/'SpecAudit.lean'
            audited=run([self.lean,'-j1','-M4096','--run',str(auditor.resolve()),mode],tmp,120,
                        env=env,sandbox=True,read_paths=reads+[str(auditor.resolve())])
            if audited.returncode:
                return {'status':'fail','reason':'type/axiom audit rejected artifact','diagnostic':(audited.stdout+audited.stderr)[-4000:]}
            result=json_object(audited.stdout.strip())
            self.frozen[module+'.olean']=data
            if mode=='spec': return spec.check(result, problem=self.problem)
            return {'status':'pass',**result}

def capture(check):
    try: return check()
    except FileNotFoundError as exc: return {'status':'missing','reason':str(exc)}
    except spec.Unsupported as exc: return {'status':'unsupported','reason':str(exc)}
    except subprocess.TimeoutExpired as exc: return {'status':'timeout','reason':str(exc)}
    except (ValueError,RecursionError) as exc: return {'status':'fail','reason':str(exc)}
    except Exception as exc: return {'status':'infrastructure_error','reason':str(exc)}

def unexpected_safe_artifacts(submission):
    return [rel for rel in ('counterexample.json','src/lib.rs')
            if (submission/rel).exists() or (submission/rel).is_symlink()
            or (submission/rel).parent.is_symlink()]

def grade(workspace,verifier,profile=None):
    submission=workspace/'submission'
    if submission.is_symlink(): return {'version':3,'status':'fail','reward':0,'reason':'submission symlink'}
    # Variant and problem belong to the pristine verifier, never to submitted files.
    variant=(verifier/'variant.txt').read_text().strip()
    if variant not in ('safe','vulnerable'): raise RuntimeError('invalid trusted variant')
    problem=read_problem(verifier)
    session=None
    checks={}
    artifacts={}
    def artifact(rel):
        t=read_artifact(submission/rel)
        if not t.strip(): raise FileNotFoundError('empty '+rel)
        artifacts[rel]=hashlib.sha256(t.encode()).hexdigest()
        return t
    def lean_stage(module,rel,mode):
        nonlocal session
        if session is None: session=LeanSession(verifier)
        return session.stage(module,artifact(rel),mode)
    start=time.monotonic()
    checks['spec']=capture(lambda:lean_stage('CandidateSpec','Spec.lean','spec'))
    checks['verdict']=capture(lambda:lean_stage('CandidateAudit','Audit.lean','verdict'))
    verdict=checks['verdict'].get('verdict')
    if verdict is not None:
        checks['verdict']['status']='pass' if verdict==variant else 'fail'
        checks['verdict']['reason']='compared with pristine implementation'
    checks['proof']=capture(lambda:lean_stage('CandidateProof','Proof.lean','proof'))
    # Correctness of the spec and diagnostic theorem are intentionally separate.
    # A proof about an inadequate spec is reported as such, not silently upgraded.
    checks['proof']['scope']='AuditClaim of the submitted spec and submitted verdict over the visible original model'
    checks['proof']['spec_semantically_complete']=checks['spec']['status']=='pass'
    if variant=='vulnerable':
        witness=capture(lambda:check_counterexample(artifact('counterexample.json'),verifier))
        patch=capture(lambda:check_patch(artifact('src/lib.rs'), problem=problem))
        score=.15*(witness['status']=='pass')+.20*(patch['status']=='pass')
        checks['response']={'status':'pass' if score==.35 else 'partial' if score else 'fail',
                            'credit_fraction':score/.35,'checks':{'counterexample':witness,'patch':patch}}
        if any(r['status']=='infrastructure_error' for r in (witness,patch)):
            checks['response']['status']='infrastructure_error'
    else:
        original=capture(lambda:check_patch((verifier/'pristine/lib.rs').read_text(), problem=problem))
        # Safe responses require absence, so inspect metadata only. Never read
        # optional attacker files (binary/oversized/device/symlink) at all.
        unwanted=unexpected_safe_artifacts(submission)
        justified=verdict=='safe' and checks['proof']['status']=='pass' and original['status']=='pass'
        # No score for merely omitting files, and no score for a bare "safe".
        checks['response']={'status':'pass' if justified and not unwanted else 'fail',
                            'checks':{'original_universal_conformance':original},
                            'unnecessary_artifacts':unwanted,'reason':'safe response requires Lean evidence and universal original Rust verification'}
        if original['status']=='infrastructure_error': checks['response']['status']='infrastructure_error'
        if not justified: checks['verdict']['status']='fail' if checks['verdict']['status']=='pass' else checks['verdict']['status']
    for name,r in checks.items():
        r['passed']=r['status']=='pass'
        r['score']=round(WEIGHTS[name]*r.get('credit_fraction',float(r['passed'])),4)
    reward=round(sum(r['score'] for r in checks.values()),4)
    return {'version':3,'problem':problem,'variant':variant,'status':'infrastructure_error' if any(r['status']=='infrastructure_error' for r in checks.values()) else 'ok',
            'reward':reward,'weights':WEIGHTS,'checkpoints':checks,'artifact_sha256':artifacts,
            'elapsed_seconds':round(time.monotonic()-start,3),'scoring':'independent semantic facets; safe verdict requires proof + universal original Rust'}

def main():
    p=argparse.ArgumentParser()
    p.add_argument('--workspace',type=Path,required=True)
    p.add_argument('--verifier',type=Path,required=True)
    p.add_argument('--logs',type=Path,required=True)
    args=p.parse_args()
    details=grade(args.workspace.resolve(),args.verifier.resolve())
    args.logs.mkdir(parents=True,exist_ok=True)
    (args.logs/'reward.txt').write_text(f"{details['reward']:.4f}\n")
    (args.logs/'details.json').write_text(json.dumps(details,indent=2)+'\n')
    print(json.dumps(details,indent=2))
    return 0

if __name__=='__main__': sys.exit(main())
