"""Semantic grading of audited Lean expression trees over bounded UInt64 inputs."""
import z3

MAX = 2**64 - 1
class Unsupported(ValueError):
    pass

def solver():
    if z3.get_version_string() != '4.13.3':
        raise RuntimeError('expected pinned Z3 4.13.3')
    s = z3.Solver()
    s.set(timeout=10000, random_seed=0)
    return s

def query(constraint, variables):
    s = solver()
    s.add(*[z3.And(v >= 0, v <= MAX) for v in variables.values()], constraint)
    verdict = s.check()
    if verdict == z3.unsat:
        return {'status':'pass', 'reason':'unsat: no counterexample in the full u64 domain'}
    if verdict == z3.sat:
        m=s.model()
        return {'status':'fail', 'counterexample':{k:m.eval(v,model_completion=True).as_long() for k,v in variables.items()}}
    reason=s.reason_unknown()
    return {'status':'timeout' if 'timeout' in reason else 'unknown','reason':reason}

def expression(tree, variables):
    count=0
    def go(n, depth=0):
        nonlocal count
        count += 1
        if count > 512 or depth > 64: raise Unsupported('expression size/depth budget')
        if not isinstance(n,dict): raise ValueError('invalid trusted AST')
        if set(n)=={'var'}:
            i=n['var']
            if type(i) is not int or not 0 <= i < len(variables): raise ValueError('invalid variable')
            return variables[i], 'nat'
        if set(n)=={'nat'}:
            v=n['nat']
            if type(v) is not int or not 0 <= v < 2**256: raise Unsupported('constant budget')
            return z3.IntVal(v), 'nat'
        if set(n)!= {'op','args'}: raise ValueError('invalid trusted AST fields')
        op,args=n['op'],n['args']
        arities={'true':0,'false':0,'add':2,'sub':2,'mul':2,'div':2,'mod':2,'le':2,'lt':2,'eq':2,'and':2,'or':2,'not':1,'iff':2,'implies':2,'if':3}
        if op not in arities or not isinstance(args,list) or len(args)!=arities[op]: raise Unsupported('unsupported operation')
        terms=[go(x,depth+1) for x in args]
        vals=[x[0] for x in terms]; kinds=[x[1] for x in terms]
        if op in ('true','false'): return z3.BoolVal(op=='true'),'prop'
        if op in ('add','sub','mul','div','mod','le','lt') and kinds!=['nat','nat']: raise ValueError('invalid numeric AST type')
        if op in ('and','or','iff','implies') and kinds!=['prop','prop']: raise ValueError('invalid logical AST type')
        if op=='not' and kinds!=['prop']: raise ValueError('invalid not AST type')
        if op=='eq' and (len(set(kinds))!=1): raise ValueError('invalid equality AST type')
        if op=='if' and (kinds[0]!='prop' or kinds[1]!=kinds[2]): raise ValueError('invalid conditional AST type')
        if op=='add': return vals[0]+vals[1],'nat'
        if op=='sub': return z3.If(vals[0]>=vals[1], vals[0]-vals[1], 0),'nat'
        if op=='mul':
            v0,v1=z3.simplify(vals[0]),z3.simplify(vals[1])
            if not (z3.is_int_value(v0) or z3.is_int_value(v1)): raise Unsupported('nonlinear multiplication')
            return vals[0]*vals[1],'nat'
        if op in ('div','mod'):
            d=z3.simplify(vals[1])
            if not z3.is_int_value(d) or d.as_long()<=0: raise Unsupported('division/modulo requires positive constant divisor')
            return (vals[0]/d if op=='div' else vals[0]%d),'nat'
        if op=='le': return vals[0]<=vals[1],'prop'
        if op=='lt': return vals[0]<vals[1],'prop'
        if op=='eq': return vals[0]==vals[1],'prop'
        if op=='and': return z3.And(*vals),'prop'
        if op=='or': return z3.Or(*vals),'prop'
        if op=='not': return z3.Not(vals[0]),'prop'
        if op=='iff': return vals[0]==vals[1],'prop'
        if op=='implies': return z3.Implies(*vals),'prop'
        if op=='if': return z3.If(*vals),kinds[1]
        raise Unsupported(op)
    value,kind=go(tree)
    if kind!='prop': raise ValueError('spec component must have type Prop')
    return value

def expected_debit_z3(amount, fee, problem='authorization'):
    if problem=='authorization':
        return amount+fee
    if problem=='settlement' or problem.startswith('settlement-'):
        gross_fee=(amount+fee+9999)/10000
        rebate=gross_fee/10
        return amount+(gross_fee-rebate)
    raise ValueError(f'unknown problem: {problem}')

def expected_debit_py(amount, fee, problem='authorization'):
    if problem=='authorization':
        return amount+fee
    if problem=='settlement' or problem.startswith('settlement-'):
        gross_fee=(amount+fee+9999)//10000
        rebate=gross_fee//10
        return amount+(gross_fee-rebate)
    raise ValueError(f'unknown problem: {problem}')

def check(obj, problem='authorization'):
    if 'unsupported' in obj:
        return {'status':'unsupported','credit_fraction':0,'kernel_valid':True,'reason':obj['unsupported']}
    v={k:z3.Int(k) for k in ('balance','amount','fee','total')}
    b,a,f,t=v.values()
    accepts_error=obj['accepts'].get('unsupported')
    output_error=obj['output'].get('unsupported')
    try: accepts=expression(obj['accepts'],list(v.values())) if accepts_error is None else None
    except Unsupported as exc: accepts_error=str(exc); accepts=None
    try: output=expression(obj['output'],list(v.values())) if output_error is None else None
    except Unsupported as exc: output_error=str(exc); output=None
    expected_total=expected_debit_z3(a,f,problem)
    wanted=expected_total <= b
    unsupported=lambda reason: {'status':'unsupported','reason':reason}
    safety=query(z3.And(accepts,z3.Not(wanted)),v) if accepts is not None else unsupported(accepts_error)
    complete=query(z3.And(wanted,z3.Not(accepts)),v) if accepts is not None else unsupported(accepts_error)
    ready=accepts is not None and output is not None
    reason=accepts_error or output_error
    exact=query(z3.And(accepts,output,t!=expected_total),v) if ready else unsupported(reason)
    # Existence is quantified over *bounded* UInt64 results. No sampling.
    exists=z3.Exists([t],z3.And(t>=0,t<=MAX,output)) if ready else None
    existence=query(z3.And(accepts,z3.Not(exists)),{k:x for k,x in v.items() if k!='total'}) if ready else unsupported(reason)
    nonvacuity=query(accepts,v) if accepts is not None else unsupported(accepts_error)
    if nonvacuity['status']=='fail':
        nonvacuity={'status':'pass','accepted_example':nonvacuity['counterexample']}
    elif nonvacuity['status']=='pass':
        nonvacuity={'status':'fail','reason':'acceptance predicate is empty'}
    u=z3.Int('other_total')
    other=z3.substitute(output,(t,u)) if ready else None
    functional=query(z3.And(accepts,output,other,t!=u),dict(v,other_total=u)) if ready else unsupported(reason)
    # Exactness is intentionally conditional on acceptance; outputs for a
    # rejected input have no meaning in an Option-valued API.
    coherence_status=next((r['status'] for r in (nonvacuity,existence) if r['status']!='pass'),'pass')
    exact_status=next((r['status'] for r in (nonvacuity,existence,exact,functional) if r['status']!='pass'),'pass')
    facets={'safety':safety,'completeness':complete,
            'output_exactness':{'status':exact_status,'exact_implication':exact,'functionality':functional,
                                'nonvacuity':nonvacuity,'output_existence':existence},
            'existence_coherence':{'status':coherence_status,'nonvacuity':nonvacuity,'output_existence':existence}}
    passed=sum(r['status']=='pass' for r in facets.values())
    weights={k:.25 for k in facets}
    credit=sum(weights[k] for k,r in facets.items() if r['status']=='pass')
    unresolved=[r['status'] for r in facets.values() if r['status'] in ('timeout','unknown','unsupported')]
    status='pass' if passed==4 else 'partial' if credit else unresolved[0] if unresolved else 'fail'
    return {'status':status,'credit_fraction':round(credit,4),'kernel_valid':True,'facets':facets,
            'overflow':'included in safety: mathematical sum <= UInt64 balance <= MAX',
            'vacuity':'raw implication may hold vacuously; exactness and coherence credit require nonempty acceptance and an output for every accepted input',
            'backend':'audited Lean Expr -> typed arithmetic AST -> Z3 4.13.3'}
