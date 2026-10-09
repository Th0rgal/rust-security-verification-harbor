"""Semantic grading of audited Lean expression trees over bounded UInt64 inputs."""
import math
import z3

MAX = 2**64 - 1
GOLDILOCKS_P = 0xFFFF_FFFF_0000_0001
WHIRLPOOL_DENOM = 1_000_000
PLONKY3_P = 2013265921
PLONKY3_R_INV = 943718400
SUCCINCT_L8 = 0x0101_0101_0101_0101
SUCCINCT_H8 = 0x8080_8080_8080_8080
SUCCINCT_M16 = 0x00FF_00FF_00FF_00FF
SUCCINCT_L16 = 0x0001_0001_0001_0001
RUINT_MG10_D = 0x8003
RUINT_MG10_V = 0xFFF4
PROBLEMS = (
    'authorization',
    'settlement',
    'settlement-modular',
    'settlement-engine',
    'goldilocks',
    'whirlpool',
    'plonky3',
    'succinct',
    'openpql',
    'ruint',
    'zk-clearing',
)

class Unsupported(ValueError):
    pass

def solver(timeout=10000):
    if z3.get_version_string() != '4.13.3':
        raise RuntimeError('expected pinned Z3 4.13.3')
    s = z3.Solver()
    s.set(timeout=timeout, random_seed=0)
    return s

def _has_de_bruijn(e):
    if z3.is_var(e) or z3.is_quantifier(e):
        return True
    if not z3.is_app(e):
        return False
    return any(_has_de_bruijn(e.arg(i)) for i in range(e.num_args()))

def _extract_linear(e):
    s = z3.simplify(e)
    if z3.is_int_value(s):
        return s.as_long(), {}
    if not z3.is_app(s):
        return 0, {s.get_id(): (1, s)}
    k = s.decl().kind()
    if k == z3.Z3_OP_ADD:
        c_tot = 0
        terms = {}
        for i in range(s.num_args()):
            c_i, t_i = _extract_linear(s.arg(i))
            c_tot += c_i
            for vid, (cf, vexpr) in t_i.items():
                terms[vid] = (terms.get(vid, (0, vexpr))[0] + cf, vexpr)
                if terms[vid][0] == 0:
                    del terms[vid]
        return c_tot, terms
    if k == z3.Z3_OP_SUB and s.num_args() == 2:
        c0, t0 = _extract_linear(s.arg(0))
        c1, t1 = _extract_linear(s.arg(1))
        terms = dict(t0)
        for vid, (cf, vexpr) in t1.items():
            terms[vid] = (terms.get(vid, (0, vexpr))[0] - cf, vexpr)
            if terms[vid][0] == 0:
                del terms[vid]
        return c0 - c1, terms
    if k == z3.Z3_OP_UMINUS and s.num_args() == 1:
        c0, t0 = _extract_linear(s.arg(0))
        return -c0, {vid: (-cf, vexpr) for vid, (cf, vexpr) in t0.items()}
    if k == z3.Z3_OP_MUL and s.num_args() == 2:
        a0, a1 = z3.simplify(s.arg(0)), z3.simplify(s.arg(1))
        if z3.is_int_value(a0):
            m = a0.as_long()
            c1, t1 = _extract_linear(a1)
            return m * c1, {vid: (m * cf, vexpr) for vid, (cf, vexpr) in t1.items() if m * cf != 0}
        if z3.is_int_value(a1):
            m = a1.as_long()
            c0, t0 = _extract_linear(a0)
            return m * c0, {vid: (m * cf, vexpr) for vid, (cf, vexpr) in t0.items() if m * cf != 0}
    return 0, {s.get_id(): (1, s)}

def _needs_divmod_purification(expr):
    seen = set()
    stack = [expr]
    while stack:
        e = stack.pop()
        eid = e.get_id()
        if eid in seen:
            continue
        seen.add(eid)
        if z3.is_quantifier(e):
            stack.append(e.body())
            continue
        if not z3.is_app(e):
            continue
        if e.decl().kind() in (z3.Z3_OP_IDIV, z3.Z3_OP_MOD) and e.num_args() == 2:
            c_simp = z3.simplify(e.arg(1))
            if z3.is_int_value(c_simp) and (c_simp.as_long() >= 1_000_000 or c_simp.as_long() in (128, 256, 32771, 65536)):
                return True
        for i in range(e.num_args()):
            stack.append(e.arg(i))
    return False

def _scan_var_divisors(expr):
    var_divs = {name: set() for name in ('balance', 'amount', 'fee')}
    var_ids = {z3.Int(name).get_id(): name for name in var_divs}
    seen = set()
    stack = [expr]
    while stack:
        e = stack.pop()
        eid = e.get_id()
        if eid in seen:
            continue
        seen.add(eid)
        if z3.is_quantifier(e):
            stack.append(e.body())
            continue
        if not z3.is_app(e):
            continue
        if e.decl().kind() in (z3.Z3_OP_IDIV, z3.Z3_OP_MOD) and e.num_args() == 2:
            c_simp = z3.simplify(e.arg(1))
            if z3.is_int_value(c_simp):
                dval = c_simp.as_long()
                lhs = z3.simplify(e.arg(0))
                if lhs.get_id() in var_ids:
                    var_divs[var_ids[lhs.get_id()]].add(dval)
                elif z3.is_app(lhs) and lhs.decl().kind() == z3.Z3_OP_IDIV and lhs.num_args() == 2:
                    inner = z3.simplify(lhs.arg(0))
                    if inner.get_id() in var_ids:
                        var_divs[var_ids[inner.get_id()]].add(dval)
        for i in range(e.num_args()):
            stack.append(e.arg(i))
    return var_divs

def purify_divmod(expr):
    if not _needs_divmod_purification(expr):
        return expr
    keep_alive = [expr]
    extra = []
    dm_cache = {}
    bounds = {}
    rem_defs = {}
    quot_defs = {}
    var_splits = {}
    pow2_var_splits = {}
    monty_rels = []
    monty_q_ids = set()
    monty_u0_vids = set()
    var_divs = _scan_var_divisors(expr)
    for name in ('balance', 'amount', 'fee', 'total', 'other_total'):
        v = z3.Int(name)
        keep_alive.append(v)
        bounds[v.get_id()] = (0, MAX)
        if name in var_divs and 256 in var_divs[name]:
            bvars = [z3.Int(f'_byte_{name}_{i}') for i in range(8)]
            keep_alive.extend(bvars)
            for bv in bvars:
                bounds[bv.get_id()] = (0, 255)
                extra.append(z3.And(bv >= 0, bv < 256))
            decomp = z3.simplify(sum(bvars[i] * (1 << (8 * i)) for i in range(8)))
            keep_alive.append(decomp)
            pow2_var_splits[v.get_id()] = decomp
            extra.append(v == decomp)
        elif name in var_divs and 65536 in var_divs[name]:
            lvars = [z3.Int(f'_limb_{name}_{i}') for i in range(4)]
            keep_alive.extend(lvars)
            for lv in lvars:
                bounds[lv.get_id()] = (0, 65535)
                extra.append(z3.And(lv >= 0, lv < 65536))
            decomp = z3.simplify(sum(lvars[i] * (1 << (16 * i)) for i in range(4)))
            keep_alive.append(decomp)
            pow2_var_splits[v.get_id()] = decomp
            extra.append(v == decomp)
    memo = {}
    idx = [0]

    def _cache_bound(e, res):
        keep_alive.append(e)
        bounds[e.get_id()] = res
        return res

    def get_bounds(e):
        keep_alive.append(e)
        eid = e.get_id()
        if eid in bounds:
            return bounds[eid]
        if z3.is_int_value(e):
            v = e.as_long()
            return (v, v)
        if not z3.is_app(e):
            return (None, None)
        k = e.decl().kind()
        direct = (None, None)
        if k == z3.Z3_OP_ADD:
            bs = [get_bounds(e.arg(i)) for i in range(e.num_args())]
            if all(lo is not None and hi is not None for lo, hi in bs):
                direct = (sum(lo for lo, _ in bs), sum(hi for _, hi in bs))
        elif k == z3.Z3_OP_SUB and e.num_args() == 2:
            (l0, h0), (l1, h1) = get_bounds(e.arg(0)), get_bounds(e.arg(1))
            if None not in (l0, h0, l1, h1):
                direct = (l0 - h1, h0 - l1)
        elif k == z3.Z3_OP_UMINUS and e.num_args() == 1:
            l0, h0 = get_bounds(e.arg(0))
            if l0 is not None and h0 is not None:
                direct = (-h0, -l0)
        elif k == z3.Z3_OP_MUL and e.num_args() >= 2:
            cur_lo, cur_hi = get_bounds(e.arg(0))
            if cur_lo is not None and cur_hi is not None:
                for i in range(1, e.num_args()):
                    li, hi = get_bounds(e.arg(i))
                    if li is None or hi is None:
                        cur_lo, cur_hi = None, None
                        break
                    prods = (cur_lo * li, cur_lo * hi, cur_hi * li, cur_hi * hi)
                    cur_lo, cur_hi = min(prods), max(prods)
                if cur_lo is not None and cur_hi is not None:
                    direct = (cur_lo, cur_hi)
        elif k == z3.Z3_OP_ITE:
            cond, t_br, f_br = e.arg(0), e.arg(1), e.arg(2)
            # Pattern: If(x >= 128, x, x + 128) or If(128 <= x, x, x + 128) on byte x in [0, 255]
            if z3.is_app(cond) and cond.num_args() == 2:
                ck = cond.decl().kind()
                ca0, ca1 = cond.arg(0), cond.arg(1)
                if ck == z3.Z3_OP_GE and z3.is_int_value(ca1) and ca1.as_long() == 128:
                    xl, xh = get_bounds(ca0)
                    if xl == 0 and xh == 255 and z3.eq(t_br, ca0):
                        return _cache_bound(e, (128, 255))
                if ck == z3.Z3_OP_LE and z3.is_int_value(ca0) and ca0.as_long() == 128:
                    xl, xh = get_bounds(ca1)
                    if xl == 0 and xh == 255 and z3.eq(t_br, ca1):
                        return _cache_bound(e, (128, 255))
                if ck in (z3.Z3_OP_GE, z3.Z3_OP_LE, z3.Z3_OP_GT, z3.Z3_OP_LT):
                    (l0, h0), (l1, h1) = get_bounds(ca0), get_bounds(ca1)
                    if None not in (l0, h0, l1, h1):
                        if (ck == z3.Z3_OP_GE and l0 >= h1) or (ck == z3.Z3_OP_LE and h0 <= l1) or (ck == z3.Z3_OP_GT and l0 > h1) or (ck == z3.Z3_OP_LT and h0 < l1):
                            return _cache_bound(e, get_bounds(t_br))
                        if (ck == z3.Z3_OP_GE and h0 < l1) or (ck == z3.Z3_OP_LE and l0 > h1) or (ck == z3.Z3_OP_GT and h0 <= l1) or (ck == z3.Z3_OP_LT and l0 >= h1):
                            return _cache_bound(e, get_bounds(f_br))
            (l1, h1), (l2, h2) = get_bounds(t_br), get_bounds(f_br)
            if None not in (l1, h1, l2, h2):
                direct = (min(l1, l2), max(h1, h2))
        if k in (z3.Z3_OP_ADD, z3.Z3_OP_SUB) and quot_defs:
            c0, terms = _extract_linear(e)
            if any(vid in quot_defs for vid in terms):
                M = 1
                for vid in terms:
                    if vid in quot_defs:
                        M = math.lcm(M, quot_defs[vid][0])
                scaled = z3.IntVal(c0 * M)
                for vid, (cf, vexpr) in terms.items():
                    if vid in quot_defs:
                        m_q, num_q = quot_defs[vid]
                        scaled = scaled + z3.IntVal(cf * (M // m_q)) * num_q
                    else:
                        scaled = scaled + z3.IntVal(cf * M) * vexpr
                sc_c0, sc_terms = _extract_linear(scaled)
                lo_s, hi_s = sc_c0, sc_c0
                ok_s = True
                for vid, (cf, vexpr) in sc_terms.items():
                    keep_alive.append(vexpr)
                    vl, vh = get_bounds(vexpr)
                    if vl is None or vh is None:
                        ok_s = False
                        break
                    lo_s += cf * (vl if cf >= 0 else vh)
                    hi_s += cf * (vh if cf >= 0 else vl)
                if ok_s:
                    q_lo, q_hi = lo_s // M, hi_s // M
                    if None not in direct:
                        direct = (max(direct[0], q_lo), min(direct[1], q_hi))
                    else:
                        direct = (q_lo, q_hi)
        if None not in direct:
            return _cache_bound(e, direct)
        return (None, None)

    def expand_rems(e):
        c0, terms = _extract_linear(e)
        changed = False
        acc = z3.IntVal(c0)
        for vid, (cf, vexpr) in terms.items():
            if vid in rem_defs:
                acc = acc + z3.IntVal(cf) * rem_defs[vid]
                changed = True
            else:
                acc = acc + z3.IntVal(cf) * vexpr
        return z3.simplify(acc) if changed else e

    def expand_var_splits(e, c_val):
        is_pow2 = c_val > 0 and (c_val & (c_val - 1)) == 0
        c0, terms = _extract_linear(e)
        changed = False
        acc = z3.IntVal(c0)
        for vid, (cf, vexpr) in terms.items():
            if is_pow2 and vid in pow2_var_splits:
                acc = acc + z3.IntVal(cf) * pow2_var_splits[vid]
                changed = True
            elif (vid, c_val) in var_splits:
                acc = acc + z3.IntVal(cf) * var_splits[(vid, c_val)]
                changed = True
            elif not is_pow2 and vid in var_splits and c_val not in (32771, 2013265921):
                acc = acc + z3.IntVal(cf) * var_splits[vid]
                changed = True
            else:
                acc = acc + z3.IntVal(cf) * vexpr
        return z3.simplify(acc) if changed else e

    def _linear_key(e, c_val):
        c0, terms = _extract_linear(e)
        return (c_val, c0, tuple((vid, terms[vid][0]) for vid in sorted(terms)))

    def get_qr(a, c_val, c_expr):
        lo_raw, hi_raw = get_bounds(a)
        a_s = z3.simplify(a)
        keep_alive.append(a_s)
        lo, hi = get_bounds(a_s)
        if lo_raw is not None and hi_raw is not None:
            lo = max(lo, lo_raw) if lo is not None else lo_raw
            hi = min(hi, hi_raw) if hi is not None else hi_raw
            _cache_bound(a_s, (lo, hi))
        if lo is not None and hi is not None and lo // c_val == hi // c_val:
            q_const = lo // c_val
            r_exact = a_s if q_const == 0 else z3.simplify(a_s - z3.IntVal(q_const * c_val))
            keep_alive.append(r_exact)
            _cache_bound(r_exact, (lo - q_const * c_val, hi - q_const * c_val))
            return (z3.IntVal(q_const), r_exact)
        if lo is not None and hi is not None and -c_val < lo < 0 and hi == 0:
            q_exact = z3.If(a_s == 0, z3.IntVal(0), z3.IntVal(-1))
            r_exact = z3.If(a_s == 0, z3.IntVal(0), z3.simplify(a_s + c_expr))
            keep_alive.extend((q_exact, r_exact))
            _cache_bound(q_exact, (-1, 0))
            _cache_bound(r_exact, (0, c_val - 1))
            return (q_exact, r_exact)
        if z3.is_app(a_s) and a_s.decl().kind() == z3.Z3_OP_ITE:
            cond, t_br, f_br = a_s.arg(0), a_s.arg(1), a_s.arg(2)
            qt, rt = get_qr(t_br, c_val, c_expr)
            qf, rf = get_qr(f_br, c_val, c_expr)
            q_ite = z3.If(cond, qt, qf)
            r_ite = z3.If(cond, rt, rf)
            _cache_bound(r_ite, (0, c_val - 1))
            if lo is not None and hi is not None:
                _cache_bound(q_ite, (lo // c_val, hi // c_val))
            return (q_ite, r_ite)
        a_exp = expand_rems(a_s)
        keep_alive.append(a_exp)
        c0, terms = _extract_linear(a_exp)
        if all(cf % c_val == 0 for cf, _ in terms.values()) and (len(terms) > 0 or c0 != 0):
            q_exact = z3.IntVal(c0 // c_val)
            for cf, vexpr in terms.values():
                q_exact = q_exact + z3.IntVal(cf // c_val) * vexpr
            q_exact = z3.simplify(q_exact)
            r_exact = z3.IntVal(c0 % c_val)
            keep_alive.extend((q_exact, r_exact))
            if lo is not None and hi is not None:
                _cache_bound(q_exact, (lo // c_val, hi // c_val))
            return (q_exact, r_exact)
        a_vexp = expand_var_splits(a_exp, c_val)
        keep_alive.append(a_vexp)
        c0_v, terms_v = _extract_linear(a_vexp)
        if c_val == 2013265921 and monty_rels:
            for u0_terms, u0_expr, q_mu, r_mu in monty_rels:
                first_vid, first_u0_cf = next(iter(u0_terms.items()))
                if first_vid not in terms_v:
                    continue
                cf_first = terms_v[first_vid][0]
                if cf_first % (943718400 * first_u0_cf) != 0:
                    continue
                k_m = cf_first // (943718400 * first_u0_cf)
                if k_m != 0 and all(
                    vid in terms_v and terms_v[vid][0] == k_m * 943718400 * u0_cf
                    for vid, u0_cf in u0_terms.items()
                ):
                    hi_part = z3.simplify(z3.IntVal(-1069547521) * u0_expr + z3.IntVal(2013265921) * q_mu)
                    q_mult = z3.IntVal(c0_v // c_val) + z3.IntVal(k_m) * (
                        z3.IntVal(943718400) * r_mu + z3.IntVal(2013265919) * hi_part
                    )
                    rem_expr = z3.IntVal(c0_v % c_val) + z3.IntVal(k_m) * hi_part
                    for vid in sorted(terms_v):
                        if vid in u0_terms:
                            continue
                        cf, vexpr = terms_v[vid]
                        d, m = cf // c_val, cf % c_val
                        if 2 * m > c_val:
                            m -= c_val
                            d += 1
                        q_mult = q_mult + z3.IntVal(d) * vexpr
                        rem_expr = rem_expr + z3.IntVal(m) * vexpr
                    rem_s = z3.simplify(rem_expr)
                    keep_alive.append(rem_s)
                    m_key = _linear_key(rem_s, c_val)
                    if m_key not in dm_cache:
                        idx[0] += 1
                        q_sub = z3.Int(f'_dm_q_{idx[0]}')
                        r_sub = z3.Int(f'_dm_r_{idx[0]}')
                        keep_alive.extend((q_sub, r_sub))
                        extra.append(z3.And(rem_s == c_expr * q_sub + r_sub, r_sub >= 0, r_sub < c_expr, z3.Implies(rem_s >= 0, q_sub >= 0)))
                        _cache_bound(r_sub, (0, c_val - 1))
                        dm_cache[m_key] = (q_sub, r_sub)
                    q_sub, r_sub = dm_cache[m_key]
                    res_pair = (z3.simplify(q_mult + q_sub), r_sub)
                    dm_cache[_linear_key(a_s, c_val)] = res_pair
                    return res_pair
        is_monty_mu = (
            c_val == 4294967296
            and c0_v == 0
            and len(terms_v) > 0
            and all(cf > 0 and cf % 2281701377 == 0 for cf, _ in terms_v.values())
        )
        has_monty_hi_terms = (
            c_val == 2013265921
            and any(vid in monty_q_ids for vid in terms_v)
            and any(vid in monty_u0_vids for vid in terms_v)
        )
        if not is_monty_mu and (
            any(
                (2 * cf > c_val or 2 * cf <= -c_val)
                and not (has_monty_hi_terms and (vid in monty_q_ids or vid in monty_u0_vids))
                for vid, (cf, _) in terms_v.items()
            )
            or c0_v >= c_val
            or c0_v < 0
        ):
            q_mult = z3.IntVal(c0_v // c_val)
            rem_expr = z3.IntVal(c0_v % c_val)
            reduced_any = (c0_v >= c_val or c0_v < 0)
            for vid in sorted(terms_v):
                cf, vexpr = terms_v[vid]
                if (2 * cf > c_val or 2 * cf <= -c_val) and not (
                    has_monty_hi_terms and (vid in monty_q_ids or vid in monty_u0_vids)
                ):
                    m = cf % c_val
                    if 2 * m > c_val:
                        m -= c_val
                    d = (cf - m) // c_val
                    q_mult = q_mult + z3.IntVal(d) * vexpr
                    rem_expr = rem_expr + z3.IntVal(m) * vexpr
                    reduced_any = True
                else:
                    rem_expr = rem_expr + z3.IntVal(cf) * vexpr
            if reduced_any:
                rem_s = z3.simplify(rem_expr)
                keep_alive.append(rem_s)
                if _linear_key(rem_s, c_val) != _linear_key(a_s, c_val):
                    q_sub, r_sub = get_qr(rem_s, c_val, c_expr)
                    q_tot = z3.simplify(q_mult + q_sub)
                    keep_alive.append(q_tot)
                    if lo is not None and hi is not None:
                        _cache_bound(q_tot, (lo // c_val, hi // c_val))
                    return (q_tot, r_sub)
        target_s = a_vexp if (is_monty_mu or has_monty_hi_terms) else a_s
        key = _linear_key(target_s, c_val)
        if key not in dm_cache:
            idx[0] += 1
            q = z3.Int(f'_dm_q_{idx[0]}')
            r = z3.Int(f'_dm_r_{idx[0]}')
            keep_alive.extend((q, r))
            conds = [target_s == c_expr * q + r, r >= 0, r < c_expr, z3.Implies(target_s >= 0, q >= 0)]
            if lo is not None and hi is not None:
                q_lo, q_hi = lo // c_val, hi // c_val
                conds += [q >= z3.IntVal(q_lo), q <= z3.IntVal(q_hi)]
                _cache_bound(q, (q_lo, q_hi))
            extra.append(z3.And(*conds))
            _cache_bound(r, (0, c_val - 1))
            def_base = a_vexp if (is_monty_mu or has_monty_hi_terms) else a_exp
            q_num = z3.simplify(def_base - r)
            keep_alive.append(q_num)
            quot_defs[q.get_id()] = (c_val, q_num)
            if z3.is_const(target_s) and target_s.decl().kind() == z3.Z3_OP_UNINTERPRETED:
                var_splits[(target_s.get_id(), c_val)] = c_expr * q + r
                if target_s.get_id() not in var_splits:
                    var_splits[target_s.get_id()] = c_expr * q + r
            else:
                r_def = z3.simplify(def_base - c_expr * q)
                keep_alive.append(r_def)
                rem_defs[r.get_id()] = r_def
                if is_monty_mu:
                    u0_terms = {vid: cf // 2281701377 for vid, (cf, _) in terms_v.items()}
                    u0_expr = z3.simplify(
                        sum(z3.IntVal(cf // 2281701377) * vexpr for vid, (cf, vexpr) in sorted(terms_v.items()))
                    )
                    keep_alive.append(u0_expr)
                    monty_rels.append((u0_terms, u0_expr, q, r))
                    monty_q_ids.add(q.get_id())
                    monty_u0_vids.update(u0_terms.keys())
            dm_cache[key] = (q, r)
        return dm_cache[key]

    def walk(e):
        keep_alive.append(e)
        eid = e.get_id()
        if eid in memo:
            return memo[eid]
        if z3.is_quantifier(e):
            n_vars = e.num_vars()
            bound_consts = [z3.Const(f'_qvar_{eid}_{i}', e.var_sort(n_vars - 1 - i)) for i in range(n_vars)]
            inst_body = z3.substitute_vars(e.body(), *bound_consts)
            bound_ids = {c.get_id() for c in bound_consts}
            def mentions_bound(x):
                if x.get_id() in bound_ids:
                    return True
                if not z3.is_app(x):
                    return False
                return any(mentions_bound(x.arg(j)) for j in range(x.num_args()))
            def walk_q(x):
                if not mentions_bound(x):
                    return walk(x)
                if not z3.is_app(x) or x.num_args() == 0:
                    return x
                ch = [walk_q(x.arg(j)) for j in range(x.num_args())]
                return x.decl()(*ch) if ch != [x.arg(j) for j in range(x.num_args())] else x
            new_body = walk_q(inst_body)
            res = z3.Exists(bound_consts, new_body) if e.is_exists() else z3.ForAll(bound_consts, new_body)
            keep_alive.append(res)
            memo[eid] = res
            return res
        if not z3.is_app(e) or e.num_args() == 0:
            memo[eid] = e
            return e
        ch = [walk(e.arg(i)) for i in range(e.num_args())]
        k = e.decl().kind()
        if k == z3.Z3_OP_ITE and ch[0].decl().kind() in (z3.Z3_OP_GE, z3.Z3_OP_LT, z3.Z3_OP_LE, z3.Z3_OP_GT):
            c_lhs, c_rhs = ch[0].arg(0), ch[0].arg(1)
            (l0, h0), (l1, h1) = get_bounds(c_lhs), get_bounds(c_rhs)
            if None not in (l0, h0, l1, h1):
                ck = ch[0].decl().kind()
                if (ck == z3.Z3_OP_GE and h0 < l1) or (ck == z3.Z3_OP_LE and l0 > h1) or (ck == z3.Z3_OP_GT and h0 <= l1) or (ck == z3.Z3_OP_LT and l0 >= h1):
                    memo[eid] = ch[2]
                    return ch[2]
                if (ck == z3.Z3_OP_GE and l0 >= h1) or (ck == z3.Z3_OP_LE and h0 <= l1) or (ck == z3.Z3_OP_GT and l0 > h1) or (ck == z3.Z3_OP_LT and h0 < l1):
                    memo[eid] = ch[1]
                    return ch[1]
        if k in (z3.Z3_OP_IDIV, z3.Z3_OP_MOD) and len(ch) == 2 and not _has_de_bruijn(ch[0]):
            c_simp = z3.simplify(ch[1])
            if z3.is_int_value(c_simp) and c_simp.as_long() > 0:
                q, r = get_qr(ch[0], c_simp.as_long(), c_simp)
                res = q if k == z3.Z3_OP_IDIV else r
                keep_alive.append(res)
                get_bounds(res)
                memo[eid] = res
                return res
        res = e.decl()(*ch) if ch != [e.arg(i) for i in range(e.num_args())] else e
        keep_alive.append(res)
        get_bounds(res)
        memo[eid] = res
        return res
    def _mentions_int_const(root, target):
        seen_c = set()
        stk = [root]
        while stk:
            cur = stk.pop()
            cid = cur.get_id()
            if cid in seen_c:
                continue
            seen_c.add(cid)
            if z3.is_quantifier(cur):
                stk.append(cur.body())
                continue
            if not z3.is_app(cur):
                continue
            if z3.is_int_value(cur) and cur.as_long() == target:
                return True
            for i in range(cur.num_args()):
                stk.append(cur.arg(i))
        return False

    for name in ('balance', 'amount', 'fee'):
        for pre_d in (10000, 1000000):
            if name in var_divs and pre_d in var_divs[name]:
                get_qr(z3.Int(name), pre_d, z3.IntVal(pre_d))
    if _mentions_int_const(expr, 2281701377):
        _, u0_pre = get_qr(z3.Int('amount'), 4294967296, z3.IntVal(4294967296))
        get_qr(u0_pre * z3.IntVal(2281701377), 4294967296, z3.IntVal(4294967296))
    purified = walk(expr)
    return z3.And(purified, *extra) if extra else purified

def query(constraint, variables):
    bounds = [z3.And(v >= 0, v <= MAX) for v in variables.values()]
    full = z3.And(*bounds, constraint)
    s = solver(timeout=9000)
    s.add(purify_divmod(full))
    verdict = s.check()
    if verdict == z3.unknown:
        s = solver(timeout=1000)
        s.add(full)
        verdict = s.check()
    if verdict == z3.unsat:
        return {'status':'pass', 'reason':'unsat: no counterexample in the full u64 domain'}
    if verdict == z3.sat:
        m=s.model()
        return {'status':'fail', 'counterexample':{k:m.eval(v,model_completion=True).as_long() for k,v in variables.items()}}
    reason=s.reason_unknown()
    return {'status':'timeout' if 'timeout' in reason else 'unknown','reason':reason}

def _is_pow2_mask(val):
    return val > 0 and (val & (val + 1)) == 0

def _byte_at_z3(x, i):
    return (x / (1 << (8 * i))) % 256

def _mentions_byte_div(e):
    seen = set()
    stack = [e]
    while stack:
        cur = stack.pop()
        cid = cur.get_id()
        if cid in seen or not z3.is_app(cur):
            continue
        seen.add(cid)
        if cur.decl().kind() in (z3.Z3_OP_IDIV, z3.Z3_OP_MOD) and cur.num_args() == 2:
            d = z3.simplify(cur.arg(1))
            if z3.is_int_value(d) and d.as_long() == 256:
                return True
        for i in range(cur.num_args()):
            stack.append(cur.arg(i))
    return False

def _bitand_z3(a, b):
    sa, sb = z3.simplify(a), z3.simplify(b)
    if z3.is_int_value(sb):
        m = sb.as_long()
        if m == 0: return z3.IntVal(0)
        if _is_pow2_mask(m): return a % (m + 1)
        if m == SUCCINCT_H8:
            return sum(z3.If(_byte_at_z3(a, i) >= 128, 128, 0) * (1 << (8 * i)) for i in range(8))
        if m == SUCCINCT_M16:
            return sum(_byte_at_z3(a, i) * (1 << (8 * i)) for i in (0, 2, 4, 6))
    if z3.is_int_value(sa):
        m = sa.as_long()
        if m == 0: return z3.IntVal(0)
        if _is_pow2_mask(m): return b % (m + 1)
        if m == SUCCINCT_H8:
            return sum(z3.If(_byte_at_z3(b, i) >= 128, 128, 0) * (1 << (8 * i)) for i in range(8))
        if m == SUCCINCT_M16:
            return sum(_byte_at_z3(b, i) * (1 << (8 * i)) for i in (0, 2, 4, 6))
    return z3.BV2Int(z3.Int2BV(a, 128) & z3.Int2BV(b, 128))

def _bitor_z3(a, b):
    sa, sb = z3.simplify(a), z3.simplify(b)
    if z3.is_int_value(sa) and sa.as_long() == 0: return b
    if z3.is_int_value(sb) and sb.as_long() == 0: return a
    if z3.is_int_value(sb) and sb.as_long() == SUCCINCT_H8:
        return sum(z3.If(_byte_at_z3(a, i) >= 128, _byte_at_z3(a, i), _byte_at_z3(a, i) + 128) * (1 << (8 * i)) for i in range(8))
    if z3.is_int_value(sa) and sa.as_long() == SUCCINCT_H8:
        return sum(z3.If(_byte_at_z3(b, i) >= 128, _byte_at_z3(b, i), _byte_at_z3(b, i) + 128) * (1 << (8 * i)) for i in range(8))
    for shift in (32, 64):
        base = 1 << shift
        if z3.is_true(z3.simplify(a % base == 0)):
            return z3.If(z3.And(b >= 0, b < base), a + b, z3.BV2Int(z3.Int2BV(a, 128) | z3.Int2BV(b, 128)))
        if z3.is_true(z3.simplify(b % base == 0)):
            return z3.If(z3.And(a >= 0, a < base), b + a, z3.BV2Int(z3.Int2BV(a, 128) | z3.Int2BV(b, 128)))
    if _mentions_byte_div(sa) or _mentions_byte_div(sb):
        return sum((z3.If(z3.Or(_byte_at_z3(a, i) >= 128, _byte_at_z3(b, i) >= 128), 128, 0) + (_byte_at_z3(a, i) % 128)) * (1 << (8 * i)) for i in range(8))
    return z3.BV2Int(z3.Int2BV(a, 128) | z3.Int2BV(b, 128))

def _bitxor_z3(a, b):
    return z3.BV2Int(z3.Int2BV(a, 128) ^ z3.Int2BV(b, 128))

def expression(tree, variables):
    count=0
    def go(n, depth=0):
        nonlocal count
        count += 1
        if count > 16384 or depth > 128: raise Unsupported('expression size/depth budget')
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
        arities={
            'true':0,'false':0,'add':2,'sub':2,'mul':2,'div':2,'mod':2,
            'pow':2,'bitand':2,'bitor':2,'bitxor':2,'shl':2,'shr':2,
            'le':2,'lt':2,'eq':2,'and':2,'or':2,'not':1,'iff':2,'implies':2,'if':3
        }
        if op not in arities or not isinstance(args,list) or len(args)!=arities[op]: raise Unsupported('unsupported operation')
        terms=[go(x,depth+1) for x in args]
        vals=[x[0] for x in terms]; kinds=[x[1] for x in terms]
        if op in ('true','false'): return z3.BoolVal(op=='true'),'prop'
        if op in ('add','sub','mul','div','mod','pow','bitand','bitor','bitxor','shl','shr','le','lt') and kinds!=['nat','nat']:
            raise ValueError('invalid numeric AST type')
        if op in ('and','or','iff','implies') and kinds!=['prop','prop']: raise ValueError('invalid logical AST type')
        if op=='not' and kinds!=['prop']: raise ValueError('invalid not AST type')
        if op=='eq' and (len(set(kinds))!=1): raise ValueError('invalid equality AST type')
        if op=='if' and (kinds[0]!='prop' or kinds[1]!=kinds[2]): raise ValueError('invalid conditional AST type')
        if op=='add': return vals[0]+vals[1],'nat'
        if op=='sub': return z3.If(vals[0]>=vals[1], vals[0]-vals[1], 0),'nat'
        if op=='mul': return vals[0]*vals[1],'nat'
        if op=='pow':
            b_s, e_s = z3.simplify(vals[0]), z3.simplify(vals[1])
            if not z3.is_int_value(e_s) or not 0 <= e_s.as_long() <= 128:
                raise Unsupported('pow requires constant exponent <= 128')
            exp = e_s.as_long()
            if z3.is_int_value(b_s):
                res_val = b_s.as_long() ** exp
                if res_val >= 2**256: raise Unsupported('constant budget')
                return z3.IntVal(res_val), 'nat'
            if exp > 4: raise Unsupported('variable base power exponent > 4')
            acc = z3.IntVal(1)
            for _ in range(exp): acc = acc * vals[0]
            return acc, 'nat'
        if op in ('shl', 'shr'):
            k_s = z3.simplify(vals[1])
            if not z3.is_int_value(k_s) or not 0 <= k_s.as_long() <= 128:
                raise Unsupported('shift requires constant shift amount <= 128')
            factor = 1 << k_s.as_long()
            return (vals[0] * factor if op == 'shl' else vals[0] / factor), 'nat'
        if op == 'bitand': return _bitand_z3(vals[0], vals[1]), 'nat'
        if op == 'bitor': return _bitor_z3(vals[0], vals[1]), 'nat'
        if op == 'bitxor': return _bitxor_z3(vals[0], vals[1]), 'nat'
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
    if problem=='goldilocks':
        return (amount / 2) + ((amount + fee * (1 << 64)) % GOLDILOCKS_P)
    if problem=='whirlpool':
        return (amount / 2) + ((amount + fee * (1 << 64) + (WHIRLPOOL_DENOM - 1)) / WHIRLPOOL_DENOM)
    if problem=='plonky3':
        b = 1 << 32
        x = (amount % b) + (fee % PLONKY3_P) * b
        return amount + ((x * PLONKY3_R_INV) % PLONKY3_P)
    if problem=='succinct':
        bs = [_byte_at_z3(fee, i) for i in range(8)]
        active = sum(z3.If(bi > 0, 1, 0) for bi in bs)
        bsum = sum(bs)
        return (amount / 2) + active * 256 + bsum
    if problem=='openpql':
        b0 = (fee % 65536) + 1
        b1 = ((fee / 65536) % 65536) + 1
        b2 = ((fee / (1 << 32)) % 65536) + 1
        b3 = ((fee / (1 << 48)) % 65536) + 1
        a0 = amount % 65536
        a1 = (amount / 65536) % 65536
        a2 = (amount / (1 << 32)) % 65536
        a3 = (amount / (1 << 48)) % 65536
        d0 = z3.If(a0 < b0, a0, b0 - 1)
        d1 = z3.If(a1 < b1, a1, b1 - 1)
        d2 = z3.If(a2 < b2, a2, b2 - 1)
        d3 = z3.If(a3 < b3, a3, b3 - 1)
        o2 = b3
        o1 = b2 * o2
        o0 = b1 * o1
        idx = d0 * o0 + d1 * o1 + d2 * o2 + d3
        return (amount / 2) + (idx / 2)
    if problem=='ruint':
        b = 1 << 16
        u1 = fee % RUINT_MG10_D
        u0 = amount % b
        u = u1 * b + u0
        return (amount / 2) + (u / RUINT_MG10_D)
    if problem=='zk-clearing':
        gross_fee = (amount + fee + 9999) / 10000
        net_bps_fee = gross_fee - (gross_fee / 10)
        b16 = 1 << 16
        blob_quot = ((fee % RUINT_MG10_D) * b16 + (amount % b16)) / RUINT_MG10_D
        bs = [_byte_at_z3(fee, i) for i in range(8)]
        active = sum(z3.If(bi > 0, 1, 0) for bi in bs)
        bsum = sum(bs)
        calldata_surcharge = active * 256 + bsum
        b32 = 1 << 32
        x = (amount % b32) + (fee % PLONKY3_P) * b32
        prover_levy = (x * PLONKY3_R_INV) % PLONKY3_P
        return amount + net_bps_fee + blob_quot + calldata_surcharge + prover_levy
    raise ValueError(f'unknown problem: {problem}')

def expected_debit_py(amount, fee, problem='authorization'):
    if problem=='authorization':
        return amount+fee
    if problem=='settlement' or problem.startswith('settlement-'):
        gross_fee=(amount+fee+9999)//10000
        rebate=gross_fee//10
        return amount+(gross_fee-rebate)
    if problem=='goldilocks':
        return (amount // 2) + ((amount + (fee << 64)) % GOLDILOCKS_P)
    if problem=='whirlpool':
        return (amount // 2) + ((amount + (fee << 64) + (WHIRLPOOL_DENOM - 1)) // WHIRLPOOL_DENOM)
    if problem=='plonky3':
        b = 1 << 32
        x = (amount % b) + (fee % PLONKY3_P) * b
        return amount + ((x * PLONKY3_R_INV) % PLONKY3_P)
    if problem=='succinct':
        bs = [(fee >> (8 * i)) & 0xFF for i in range(8)]
        active = sum(1 if bi > 0 else 0 for bi in bs)
        bsum = sum(bs)
        return (amount // 2) + active * 256 + bsum
    if problem=='openpql':
        bs = [((fee >> (16 * i)) & 0xFFFF) + 1 for i in range(4)]
        as_ = [(amount >> (16 * i)) & 0xFFFF for i in range(4)]
        ds = [as_[i] if as_[i] < bs[i] else bs[i] - 1 for i in range(4)]
        o2 = bs[3]
        o1 = bs[2] * o2
        o0 = bs[1] * o1
        idx = ds[0] * o0 + ds[1] * o1 + ds[2] * o2 + ds[3]
        return (amount // 2) + (idx // 2)
    if problem=='ruint':
        b = 1 << 16
        u1 = fee % RUINT_MG10_D
        u0 = amount % b
        u = u1 * b + u0
        return (amount // 2) + (u // RUINT_MG10_D)
    if problem=='zk-clearing':
        gross_fee = (amount + fee + 9999) // 10000
        net_bps_fee = gross_fee - (gross_fee // 10)
        b16 = 1 << 16
        blob_quot = ((fee % RUINT_MG10_D) * b16 + (amount % b16)) // RUINT_MG10_D
        bs = [(fee >> (8 * i)) & 0xFF for i in range(8)]
        active = sum(1 if bi > 0 else 0 for bi in bs)
        bsum = sum(bs)
        calldata_surcharge = active * 256 + bsum
        b32 = 1 << 32
        x = (amount % b32) + (fee % PLONKY3_P) * b32
        prover_levy = (x * PLONKY3_R_INV) % PLONKY3_P
        return amount + net_bps_fee + blob_quot + calldata_surcharge + prover_levy
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
