"""Typed contract facets over mathematical integers; missing clauses earn no credit."""
import re
import z3

MAX = 2**64 - 1
VARIABLES = ('balance', 'amount', 'fee')
FACETS = ('affordability_safety', 'total_debit', 'explicit_overflow', 'completeness')

class Unsupported(ValueError):
    pass


def solver():
    if z3.get_version_string() != '4.13.3':
        raise RuntimeError('expected pinned Z3 4.13.3, got ' + z3.get_version_string())
    s = z3.Solver()
    s.set(timeout=10000, random_seed=0)
    return s


def query(constraint, variables):
    s = solver()
    s.add(*[z3.And(v >= 0, v <= MAX) for v in variables.values()], constraint)
    verdict = s.check()
    if verdict == z3.unsat:
        return {'status': 'pass', 'reason': 'unsat (no counterexample)'}
    if verdict == z3.sat:
        m = s.model()
        return {'status': 'fail', 'counterexample': {k: m.eval(v, model_completion=True).as_long() for k, v in variables.items()}}
    reason = s.reason_unknown()
    return {'status': 'timeout' if 'timeout' in reason else 'unknown', 'reason': reason}


def contract(obj, variables):
    if not isinstance(obj, dict):
        raise ValueError('spec must be an object')
    if set(obj) == {'property', 'arithmetic', 'on_overflow'} and isinstance(obj['property'], str):
        if obj['arithmetic'] != 'mathematical_unsigned' or obj['on_overflow'] != 'reject':
            raise ValueError('legacy arithmetic/policy must be mathematical_unsigned/reject')
        old = re.sub(r'\s+', '', obj['property'])
        if old not in ('authorized_total_le_balance', 'amount+fee<=balance'):
            raise Unsupported('unrecognized legacy property; use typed DSL v2')
        # This historical property only expresses affordability. Do not infer
        # an exact output or an iff contract from its name or mathematical add.
        return variables['amount'] + variables['fee'] <= variables['balance'], None, True, False, 'legacy-partial'
    fields = {'version', 'accept', 'total_debit', 'on_overflow', 'completeness'}
    if not {'version', 'accept'} <= set(obj) <= fields or type(obj['version']) is not int or obj['version'] != 2:
        raise ValueError('DSL requires version:2 and accept; optional total_debit, on_overflow, completeness')
    if 'on_overflow' in obj and obj['on_overflow'] != 'reject':
        raise ValueError('on_overflow must be reject')
    if 'completeness' in obj and obj['completeness'] != 'iff':
        raise ValueError('completeness must be iff')
    count = 0
    def expr(node, depth=0):
        nonlocal count
        count += 1
        if count > 64 or depth > 12:
            raise ValueError('DSL exceeds 64 nodes or depth 12')
        if type(node) is bool:
            return z3.BoolVal(node), 'bool'
        if type(node) is int:
            if not 0 <= node <= 2**128 - 1:
                raise ValueError('constant outside unsigned u128')
            return z3.IntVal(node), 'nat'
        if isinstance(node, str) and node in variables:
            return variables[node], 'nat'
        if not isinstance(node, dict) or set(node) != {'op', 'args'}:
            raise ValueError('expression is bool, unsigned integer, input name, or {op,args}')
        op, args = node['op'], node['args']
        arities = {'add': 2, 'le': 2, 'lt': 2, 'eq': 2, 'and': 2, 'or': 2, 'not': 1}
        if not isinstance(op, str) or op not in arities or not isinstance(args, list) or len(args) != arities[op]:
            raise ValueError('unknown operator or invalid arity')
        typed = [expr(x, depth+1) for x in args]
        expected = 'bool' if op in ('and', 'or', 'not') else 'nat'
        if any(t != expected for _, t in typed):
            raise ValueError('type mismatch in ' + op)
        a = [v for v, _ in typed]
        if op == 'add': return a[0] + a[1], 'nat'
        if op == 'le': return a[0] <= a[1], 'bool'
        if op == 'lt': return a[0] < a[1], 'bool'
        if op == 'eq': return a[0] == a[1], 'bool'
        if op == 'and': return z3.And(*a), 'bool'
        if op == 'or': return z3.Or(*a), 'bool'
        return z3.Not(a[0]), 'bool'
    term, kind = expr(obj['accept'])
    if kind != 'bool': raise ValueError('accept must be boolean')
    total = None
    if 'total_debit' in obj:
        total, kind = expr(obj['total_debit'])
        if kind != 'nat': raise ValueError('total_debit must be a mathematical unsigned expression')
    return term, total, 'on_overflow' in obj, 'completeness' in obj, 'dsl-v2'


def check(obj):
    variables = {k: z3.Int(k) for k in VARIABLES}
    try:
        p, total, overflow, complete, adapter = contract(obj, variables)
    except Unsupported as exc:
        return {'status': 'unsupported', 'credit_fraction': 0, 'checks': {'syntax_type': {'status': 'unsupported', 'reason': str(exc)}}}
    except ValueError as exc:
        return {'status': 'fail', 'credit_fraction': 0, 'checks': {'syntax_type': {'status': 'fail', 'reason': str(exc)}}}
    expected = variables['amount'] + variables['fee']
    ref = expected <= variables['balance']
    sat = query(p, variables)
    nonvacuity = dict(sat)
    nonvacuity['status'] = {'fail': 'pass', 'pass': 'fail'}.get(sat['status'], sat['status'])
    nonvacuity['reason'] = 'acceptance has a model' if sat['status'] == 'fail' else sat.get('reason', '')
    if 'counterexample' in nonvacuity:
        nonvacuity['example'] = nonvacuity.pop('counterexample')
    checks = {'syntax_type': {'status': 'pass', 'adapter': adapter},
              'satisfiability_nonvacuity': nonvacuity,
              'reference_validity': query(z3.And(ref, z3.Not(p)), variables),
              'safety_adequacy': query(z3.And(p, z3.Not(ref)), variables),
              'equivalence_completeness': query(p != ref, variables),
              'total_debit': query(z3.And(p, total != expected), variables) if total is not None else {'status':'missing', 'reason':'no exact successful output clause'},
              'explicit_overflow': query(z3.And(p, expected > MAX), variables) if overflow else {'status':'missing', 'reason':'no explicit overflow rejection clause'},
              'completeness_declaration': {'status':'pass' if complete else 'missing', 'reason':'explicit iff clause' if complete else 'acceptance predicate alone does not assert a complete contract'}}
    # Reject vacuity as evidence for any universally quantified facet. Reference
    # validity is diagnostic; a strict but safe predicate may earn safety credit.
    def conjunction(*names):
        statuses = [checks[n]['status'] for n in names]
        return next((s for s in statuses if s != 'pass'), 'pass')
    facets = {'affordability_safety': conjunction('satisfiability_nonvacuity', 'safety_adequacy'),
              'total_debit': conjunction('satisfiability_nonvacuity', 'total_debit'),
              'explicit_overflow': conjunction('satisfiability_nonvacuity', 'explicit_overflow'),
              'completeness': conjunction('satisfiability_nonvacuity', 'completeness_declaration', 'equivalence_completeness')}
    fraction = sum(s == 'pass' for s in facets.values()) / len(FACETS)
    uncertain = next((c['status'] for c in checks.values() if c['status'] in ('unknown','timeout')), None)
    return {'status': uncertain or ('pass' if fraction == 1 else 'partial' if fraction else 'fail'),
            'credit_fraction': fraction, 'facets': {k:{'status':v, 'credit_fraction':.25 if v=='pass' else 0} for k,v in facets.items()},
            'backend': 'z3-4.13.3 mathematical integers; full u64 input domain', 'checks': checks}
