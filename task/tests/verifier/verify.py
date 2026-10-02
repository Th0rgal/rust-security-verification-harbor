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
WEIGHTS = {'spec': .20, 'counterexample': .25, 'patch': .25, 'proof': .30}
PROFILES = {'specify':'spec', 'refute':'counterexample', 'repair':'patch', 'prove':'proof'}
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
            if os.getuid() == 0:
                os.setgroups([]); os.setgid(65534); os.setuid(65534)
    if sandbox and os.getuid() == 0:
        os.chown(cwd, 65534, 65534)
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


def check_counterexample(text, verifier):
    obj = json_object(text)
    if set(obj) != {'balance', 'amount', 'fee'}: raise ValueError('requires exactly balance, amount, fee')
    inputs = [obj[k] for k in ('balance', 'amount', 'fee')]
    if any(type(x) is not int or not 0 <= x <= MAX for x in inputs): raise ValueError('inputs must be u64 JSON integers')
    balance, amount, fee = inputs
    pristine = (verifier/'pristine/lib.rs').read_text()
    with tempfile.TemporaryDirectory(prefix='security-witness-') as raw:
        tmp = Path(raw); probe = compile_probe(pristine, tmp)
        result = run([str(probe), *map(str, inputs)], tmp, 5)
    expected = f'some:{(amount+fee) & MAX}'
    exploited = amount+fee > balance and result.returncode == 0 and result.stdout.strip() == expected
    return {'status': 'pass' if exploited else 'fail', 'inputs': obj,
            'mathematical_total': amount+fee, 'pristine_observation': result.stdout.strip(),
            'pristine_sha256': hashlib.sha256(pristine.encode()).hexdigest(),
            'reason': 'pristine release Rust authorizes an unaffordable mathematical total' if exploited else 'not a reproduced security violation'}


def check_patch(source):
    # Parse before compiling: unsupported production Rust is never executed.
    universal = rust_symbolic.check(source)
    with tempfile.TemporaryDirectory(prefix='security-patch-') as raw:
        tmp = Path(raw); probe = compile_probe(source, tmp)
        cases = [(0,0,0), (109,100,10), (110,100,10), (MAX,MAX,0), (0,MAX,1),
                 (MAX,MAX,1), (42,MAX-4,5), (MAX,0,MAX), (1,0,1), (0,0,1)]
        # Include an SMT counterexample, so a universal failure is reproduced in Rust.
        if 'counterexample' in universal:
            cases.append(tuple(universal['counterexample'][k] for k in ('balance','amount','fee')))
        rng = random.Random(0xC0FFEE)
        for _ in range(128):
            amount, fee = rng.randrange(2**64), rng.randrange(2**64)
            balance = rng.randrange(2**64)
            cases += [(balance,amount,fee), (min(amount+fee, MAX),amount,fee)]
        concrete = {'status': 'pass', 'cases': len(cases)}
        for balance, amount, fee in cases:
            result = run([str(probe), str(balance), str(amount), str(fee)], tmp, 5)
            expected = f'some:{amount+fee}' if amount+fee <= balance else 'none'
            if result.returncode or result.stdout.strip() != expected:
                concrete = {'status':'fail', 'inputs':dict(balance=balance, amount=amount, fee=fee),
                            'expected':expected, 'observed':result.stdout.strip(), 'returncode':result.returncode}
                break
    return {'status': universal['status'] if concrete['status']=='pass' else 'fail',
            'checks': {'compile_api': {'status':'pass'}, 'universal_equivalence':universal, 'concrete_defense':concrete}}


SIGNATURE = '''theorem patched_authorize_sound (balance amount fee total : Nat)
    (h : repairedAuthorize balance amount fee = some total) :
    amount + fee = total ∧ total ≤ balance'''
HEADER = 'import SecurityChallenge\nimport Lean\nimport Std\nopen SecurityChallenge\n'
ALLOWED_IMPORTS = {'SecurityChallenge', 'Lean', 'Std', 'Lean.Elab.Tactic.Omega'}


def proof_term(text):
    # Strip nested Lean comments; string contents stay intact for Lean's parser.
    text = re.sub(r'--[^\n]*', '', text)
    while '/-' in text:
        start = text.index('/-'); pos = start+2; depth = 1
        while depth and pos < len(text):
            if text.startswith('/-',pos): depth+=1; pos+=2
            elif text.startswith('-/',pos): depth-=1; pos+=2
            else: pos+=1
        if depth: raise ValueError('unterminated Lean comment')
        text = text[:start] + ' ' + text[pos:]
    text = text.strip()
    while text.startswith('import '):
        line, _, text = text.partition('\n')
        if any(name not in ALLOWED_IMPORTS for name in line.split()[1:]): raise ValueError('forbidden Lean import')
        text = text.strip()
    if not text: raise FileNotFoundError('empty proof')
    # Declaration escapes are outside a proof term. No tactic (including omega)
    # is required. Executable metaprograms run inside the OS sandbox.
    banned = r'\b(sorry|sorryAx|admit|axiom|import|theorem|def|opaque|constant|constants|unsafe|initialize|builtin_initialize|native_decide|implemented_by|extern|syntax|macro|elab|attribute|set_option|namespace|section|end|export)\b'
    if re.search(banned, text) or '#' in text:
        raise ValueError('forbidden axiom, declaration, import, or unsafe proof escape')
    return text


def check_proof(text, verifier):
    term = proof_term(text)
    lean = shutil.which('lean'); checker = shutil.which('leanchecker')
    if not lean or not checker: raise RuntimeError('Lean/leanchecker unavailable')
    version = run([lean, '--version'], verifier, 15)
    if 'version 4.31.0,' not in version.stdout: raise RuntimeError('Lean 4.31.0 is required')
    api = verifier/'api'
    if not (api/'SecurityChallenge.olean').exists():
        api = verifier/'.lake/build/lib/lean'
    if not (api/'SecurityChallenge.olean').exists(): raise RuntimeError('trusted Lean API not built')
    prefix = Path(lean).resolve().parent.parent
    with tempfile.TemporaryDirectory(prefix='security-proof-') as raw:
        tmp = Path(raw)
        (tmp/'Candidate.lean').write_text(HEADER + SIGNATURE + ' := (\n' + term + '\n)\n')
        env = {'PATH': str(Path(lean).parent) + ':/usr/bin:/bin', 'HOME': str(tmp),
               'LEAN_PATH': str(api.resolve()) + ':' + str(tmp), 'TMPDIR': str(tmp)}
        reads = [str(prefix), str(api.resolve()), '/usr/lib', '/lib', '/lib64', '/dev/null', '/dev/urandom']
        try:
            candidate = run([lean, '-j1', '-M2048', '-o', 'Candidate.olean', 'Candidate.lean'], tmp, 120,
                            env=env, sandbox=True, read_paths=reads)
        except subprocess.SubprocessError as exc:
            raise RuntimeError('proof sandbox unavailable: ' + str(exc)) from exc
        if candidate.returncode or not (tmp/'Candidate.olean').is_file():
            return {'status':'fail', 'reason':'Lean rejected proof', 'diagnostic':(candidate.stdout+candidate.stderr)[-4000:]}
        serialized = tmp/'Candidate.olean'
        if serialized.is_symlink() or serialized.stat().st_size > 32*1024**2:
            raise ValueError('invalid serialized proof artifact')
        # Candidate cannot shadow trusted modules or leave executable extensions.
        frozen = serialized.read_bytes()
        for item in tmp.iterdir():
            if item.is_dir() and not item.is_symlink(): shutil.rmtree(item)
            else: item.unlink()
        serialized.write_bytes(frozen)
        # Independent kernel replay defeats tactic-side environment mutations.
        replay = run([checker, 'Candidate'], tmp, 120, env=env, sandbox=True, read_paths=reads)
        if replay.returncode:
            return {'status':'fail', 'reason':'independent kernel replay rejected proof', 'diagnostic':(replay.stdout+replay.stderr)[-4000:]}
        audit_file = verifier/'ProofAudit.lean'
        if not audit_file.is_file(): raise RuntimeError('trusted proof auditor unavailable')
        audit = run([lean, '-j1', '--run', str(audit_file.resolve())], tmp, 120,
                    env=env, sandbox=True, read_paths=reads+[str(audit_file.resolve())])
        if audit.returncode or 'AUDITED_AXIOMS' not in audit.stdout:
            return {'status':'fail', 'reason':'theorem type/axiom audit failed', 'diagnostic':(audit.stdout+audit.stderr)[-4000:]}
        return {'status':'pass', 'reason':'Lean kernel + independent replay + exact type + transitive axiom audit',
                'axioms':audit.stdout.strip(), 'allowed_imports':sorted(ALLOWED_IMPORTS), 'model':'opaque certified API (independent of submitted Rust)'}


def grade(workspace, verifier, profile='integrated'):
    weights = WEIGHTS if profile == 'integrated' else {k: float(k == PROFILES[profile]) for k in WEIGHTS}
    submission = workspace/'submission'
    checks = {'spec': ('spec.json', lambda t: spec.check(json_object(t))),
              'counterexample': ('counterexample.json', lambda t: check_counterexample(t, verifier)),
              'patch': ('src/lib.rs', check_patch),
              'proof': ('Proof.lean', lambda t: check_proof(t, verifier))}
    details = {'version':2, 'status':'ok', 'statuses':list(STATUSES), 'checkpoints':{},
               'scoring':'independent, no cascade locks', 'weights':weights, 'profile':profile}
    for name, (rel, check) in checks.items():
        start = time.monotonic(); source = None
        try:
            if submission.is_symlink(): raise ValueError('symlink submission rejected')
            source = read_artifact(submission/rel)
            if not source.strip() or (name in ('spec','counterexample') and source.strip() == '{}'):
                raise FileNotFoundError('empty artifact')
            result = check(source)
        except FileNotFoundError as exc: result = {'status':'missing','reason':str(exc)}
        except spec.Unsupported as exc: result = {'status':'unsupported','reason':str(exc)}
        except subprocess.TimeoutExpired as exc: result = {'status':'timeout','reason':str(exc)}
        except (ValueError, RecursionError) as exc: result = {'status':'fail','reason':str(exc)}
        except Exception as exc: result = {'status':'infrastructure_error','reason':str(exc)}
        result['passed'] = result['status']=='pass'
        result['score'] = round(weights[name] * result.get('credit_fraction', float(result['passed'])), 4)
        result['elapsed_seconds'] = round(time.monotonic()-start, 3)
        if source is not None: result['artifact_sha256'] = hashlib.sha256(source.encode()).hexdigest()
        details['checkpoints'][name] = result
    details['reward'] = round(sum(x['score'] for x in details['checkpoints'].values()), 2)
    if any(x['status']=='infrastructure_error' and weights[k] > 0 for k,x in details['checkpoints'].items()): details['status']='infrastructure_error'
    return details


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--workspace', type=Path, required=True); p.add_argument('--verifier',type=Path,required=True)
    p.add_argument('--logs',type=Path,required=True)
    p.add_argument('--profile',choices=['integrated',*PROFILES],default='integrated'); args = p.parse_args()
    details = grade(args.workspace.resolve(), args.verifier.resolve(), args.profile)
    args.logs.mkdir(parents=True,exist_ok=True)
    (args.logs/'reward.txt').write_text(f"{details['reward']:.2f}\n")
    (args.logs/'details.json').write_text(json.dumps(details,indent=2)+'\n')
    print(json.dumps(details,indent=2)); return 0

if __name__ == '__main__': sys.exit(main())
