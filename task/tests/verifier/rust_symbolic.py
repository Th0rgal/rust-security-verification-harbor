"""Fail-closed Rust subset interpreter. See BACKEND.md for the correspondence claim."""
from dataclasses import dataclass
from pathlib import Path
import re
import z3
from spec import (
    MAX, Unsupported, expected_debit_z3, query,
    _bitand_z3, _bitor_z3, _bitxor_z3, _byte_at_z3,
    RUINT_MG10_D, PLONKY3_P, PLONKY3_R_INV, GOLDILOCKS_P,
)

TOKEN = re.compile(r'\s+|//[^\n]*|/\*|"(?:\\.|[^"\\])*"|0x[0-9A-Fa-f_]+(?:u32|u64|u128)?|[A-Za-z_][A-Za-z_0-9]*|[0-9][0-9_]*(?:u32|u64|u128)?|::|->|=>|<<|>>|<=|>=|==|!=|&&|\|\||[^\s]')
MOD_DECL = re.compile(r'^(?P<indent>\s*)(?P<vis>pub\s+)?mod\s+(?P<name>[A-Za-z_][A-Za-z_0-9]*)\s*;', re.M)


def bundle_crate_source(source_or_path, fallback_dir=None):
    src_dir = None
    fb_dir = Path(fallback_dir) if fallback_dir is not None else None
    if isinstance(source_or_path, Path):
        if source_or_path.is_dir():
            src_dir = source_or_path
            lib_file = src_dir / 'lib.rs'
            if not lib_file.exists() and fb_dir is not None:
                lib_file = fb_dir / 'lib.rs'
            text = lib_file.read_text()
        else:
            src_dir = source_or_path.parent
            text = source_or_path.read_text()
    else:
        text = source_or_path

    def _inline_mod(match):
        indent = match.group('indent')
        vis = match.group('vis') or ''
        mname = match.group('name')
        candidates = []
        if src_dir is not None:
            candidates.append(src_dir / f'{mname}.rs')
        if fb_dir is not None:
            candidates.append(fb_dir / f'{mname}.rs')
        for cand in candidates:
            if cand.is_file() and not cand.is_symlink():
                mbody = cand.read_text()
                return f'{indent}{vis}mod {mname} {{\n{mbody}\n{indent}}}'
        return match.group(0)

    return MOD_DECL.sub(_inline_mod, text)


def tokenize(source):
    out, pos = [], 0
    while pos < len(source):
        m = TOKEN.match(source, pos)
        if not m: raise Unsupported('unrecognized Rust token')
        t = m.group(); pos = m.end()
        if t == '/*':
            depth = 1
            while depth and pos < len(source):
                if source.startswith('/*', pos): depth += 1; pos += 2
                elif source.startswith('*/', pos): depth -= 1; pos += 2
                else: pos += 1
            if depth: raise ValueError('unterminated comment')
        elif not t.isspace() and not t.startswith('//'):
            out.append(t)
    if len(out) > 40000: raise Unsupported('Rust token limit exceeded')
    return out


class Parser:
    def __init__(self, source, allow_u128=True, allow_modules=False):
        self.ts = tokenize(source); self.i = 0; self.nodes = 0
        base_ints = ('u32', 'u64') if allow_modules else ('u64',)
        self.int_types = base_ints + (('u128',) if allow_u128 else ())
        self.allow_modules = allow_modules
        self.structs = {}
        self.item_names = set()
    def peek(self, offset=0):
        idx = self.i + offset
        return self.ts[idx] if idx < len(self.ts) else '<eof>'
    def take(self, expected=None):
        t = self.peek()
        if expected is not None and t != expected:
            raise Unsupported(f'expected {expected}, got {t}')
        self.i += 1
        if t == '<eof>': raise Unsupported('unexpected EOF')
        return t
    def accept(self, t):
        if self.peek() == t: self.i += 1; return True
        return False
    def name(self):
        t = self.take()
        if not re.fullmatch('[A-Za-z_][A-Za-z_0-9]*', t): raise Unsupported('expected identifier')
        return t
    def group(self, left, right):
        self.take(left); begin = self.i; depth = 1
        while depth:
            t = self.take()
            if t == left: depth += 1
            if t == right: depth -= 1
        return self.ts[begin:self.i-1]
    def parse_type(self):
        t = self.take()
        while self.allow_modules and self.accept('::'):
            t = self.name()
        if t in self.int_types or t == 'bool': return t
        if t == '(':
            items = []
            while not self.accept(')'):
                items.append(self.parse_type())
                if not self.accept(',') and self.peek() != ')':
                    raise Unsupported('expected comma in tuple type')
            if len(items) < 2: raise Unsupported('tuple type requires at least 2 elements')
            return ('tuple', items)
        if t == 'Option':
            self.take('<'); inner = self.parse_type(); self.take('>')
            return ('Option', inner)
        if t == 'Authorization': return 'Authorization'
        if self.allow_modules and t in self.structs: return ('struct', t)
        raise Unsupported(f'unsupported type: {t}')
    def reserve_item(self, name):
        # The interpreter uses globally unique short names rather than Rust's
        # lexical module resolver. Reject collisions instead of guessing.
        if name in self.item_names:
            raise Unsupported('ambiguous production item name: ' + name)
        self.item_names.add(name)
    def register_aliases(self, table, mod_prefix, short_name, value):
        table[short_name] = value
        if not mod_prefix:
            table[f'crate::{short_name}'] = value
            table[f'super::{short_name}'] = value
        if mod_prefix:
            table[f'{mod_prefix}::{short_name}'] = value
            table[f'crate::{mod_prefix}::{short_name}'] = value
            table[f'super::{mod_prefix}::{short_name}'] = value
    def const_decl(self, consts, mod_prefix=''):
        cname = self.name(); self.reserve_item(cname); self.take(':'); cty = self.take()
        if cty not in self.int_types: raise Unsupported('unsupported const type')
        self.take('='); cval = self.expr(); self.take(';')
        qual = f'{mod_prefix}::{cname}' if mod_prefix else cname
        if any(k == qual for k, _, _, _ in consts): raise Unsupported('duplicate const')
        consts.append((qual, cname, cty, cval))
    def custom_struct_decl(self, sname):
        if sname in self.structs: raise Unsupported('duplicate struct ' + sname)
        self.take('{'); fields = {}
        while not self.accept('}'):
            self.accept('pub')
            fname = self.name(); self.take(':'); fty = self.parse_type()
            if fname in fields: raise Unsupported('duplicate field ' + fname)
            fields[fname] = fty
            if not self.accept(',') and self.peek() != '}':
                raise Unsupported('expected comma in struct')
        if not fields: raise Unsupported('empty struct')
        self.structs[sname] = fields
    def helper_fn_decl(self, fname, funcs, mod_prefix=''):
        self.take('('); params = []
        while not self.accept(')'):
            self.accept('mut')
            pname = self.name(); self.take(':'); pty = self.parse_type()
            params.append((pname, pty))
            if not self.accept(',') and self.peek() != ')':
                raise Unsupported('expected comma in parameter list')
        if len({p for p, _ in params}) != len(params): raise Unsupported('duplicate parameters')
        self.take('->'); ret_ty = self.parse_type()
        saved_nodes = self.nodes; self.nodes = 0
        fbody = self.block()
        self.nodes = saved_nodes
        self.register_aliases(funcs, mod_prefix, fname, (params, ret_ty, fbody))
    def parse_items(self, state, mod_prefix=''):
        while self.peek() not in ('<eof>', '}'):
            has_derive = False
            while self.accept('#'):
                if self.peek() == '!': raise Unsupported('crate-level attributes are unsupported')
                attr = self.group('[', ']')
                if attr == ['cfg', '(', 'test', ')']:
                    self.take('mod'); self.name(); self.group('{', '}'); has_derive = 'skip'; break
                if (attr[:2] == ['derive', '('] and attr[-1:] == [')'] and
                        set(attr[2:-1]) <= {'Debug', 'Clone', 'Copy', 'PartialEq', 'Eq', ','}):
                    has_derive = True; continue
                if self.allow_modules and attr in (['inline'], ['inline', '(', 'always', ')'], ['must_use']):
                    continue
                raise Unsupported('only built-in derives and #[cfg(test)] modules are supported')
            if has_derive == 'skip': continue
            if self.allow_modules and (self.accept('use') or (self.peek() == 'pub' and self.peek(1) == 'use')):
                if self.peek() == 'pub': self.take('pub'); self.take('use')
                if self.peek() not in ('crate', 'self', 'super'):
                    raise Unsupported('imports must be rooted in this crate')
                while not self.accept(';'):
                    if self.take() == 'as':
                        raise Unsupported('renamed imports require lexical name resolution')
                continue
            is_pub = self.accept('pub')
            if not is_pub and not self.allow_modules:
                if self.accept('const'):
                    if has_derive: raise Unsupported('unexpected derive on const')
                    self.const_decl(state['consts'], mod_prefix); continue
                raise Unsupported('expected pub item')
            item = self.take()
            if item == 'const':
                if has_derive: raise Unsupported('unexpected derive on const')
                self.const_decl(state['consts'], mod_prefix)
            elif item == 'mod':
                if not self.allow_modules or mod_prefix: raise Unsupported('nested or unexpected mod')
                mname = self.name(); self.reserve_item(mname); self.take('{')
                self.parse_items(state, mod_prefix=mname)
                self.take('}')
            elif item == 'struct':
                sname = self.name(); self.reserve_item(sname)
                if sname == 'Authorization':
                    if not is_pub or mod_prefix or state['struct'] is not None:
                        raise Unsupported('invalid or duplicate Authorization struct')
                    self.structure(); state['struct'] = True
                elif self.allow_modules:
                    self.custom_struct_decl(sname)
                else:
                    raise Unsupported('only Authorization struct is supported')
            elif item == 'fn':
                if has_derive: raise Unsupported('derive attribute must attach to a struct')
                fname = self.name(); self.reserve_item(fname)
                if fname == 'authorize' and not mod_prefix:
                    if not is_pub or state['body'] is not None: raise Unsupported('duplicate or private authorize')
                    self.take('('); names = []
                    for n in range(3):
                        self.accept('mut')
                        names.append(self.name()); self.take(':'); self.take('u64')
                        if n < 2: self.take(',')
                    self.accept(','); self.take(')'); self.take('->')
                    self.take('Option'); self.take('<'); self.take('Authorization'); self.take('>')
                    if len(set(names)) != 3: raise Unsupported('duplicate parameters')
                    saved_nodes = self.nodes; self.nodes = 0
                    state['body'] = self.block()
                    self.nodes = saved_nodes
                    state['names'] = names
                elif self.allow_modules:
                    self.helper_fn_decl(fname, state['funcs'], mod_prefix)
                else:
                    raise Unsupported('only authorize function is supported')
            else:
                raise Unsupported('only Authorization, const, and authorize production items are supported')
    def program(self):
        state = {'struct': None, 'body': None, 'names': None, 'consts': [], 'funcs': {}}
        self.parse_items(state)
        if state['struct'] is None or state['body'] is None: raise Unsupported('missing public API')
        return state['consts'], state['structs'] if 'structs' in state else self.structs, state['funcs'], state['names'], state['body']
    def structure(self):
        self.take('{'); self.take('pub'); self.take('total_debit'); self.take(':'); self.take('u64')
        self.accept(','); self.take('}')
    def block(self):
        self.take('{'); statements = []
        while not self.accept('}'):
            if self.accept('let'):
                if self.accept('('):
                    names = []
                    while not self.accept(')'):
                        self.accept('mut')
                        names.append(self.name())
                        if not self.accept(',') and self.peek() != ')':
                            raise Unsupported('expected comma in tuple let')
                    if len(names) < 2 or len(set(names)) != len(names):
                        raise Unsupported('invalid tuple let pattern')
                    ty = self.parse_type() if self.accept(':') else None
                    self.take('='); value = self.expr(); self.take(';')
                    statements.append(('let_tuple', names, ty, value))
                else:
                    self.accept('mut')
                    name = self.name(); ty = None
                    if self.accept(':'):
                        ty = self.parse_type()
                    self.take('='); value = self.expr(); self.take(';')
                    statements.append(('let', name, ty, value))
            elif re.fullmatch('[A-Za-z_][A-Za-z_0-9]*', self.peek()) and self.peek(1) == '=':
                name = self.take(); self.take('='); value = self.expr(); self.take(';')
                statements.append(('assign', name, value))
            else:
                value = self.expr()
                if self.accept(';'): statements.append(('stmt', value))
                elif self.peek() == '}': statements.append(('tail', value)); self.take('}'); break
                elif value[0] in ('if', 'iflet', 'match', 'block'):
                    statements.append(('stmt', value))
                else: raise Unsupported('expected semicolon or block end')
        return ('block', statements)
    def expr(self, minimum=0):
        self.nodes += 1
        if self.nodes > 2048: raise Unsupported('expression limit exceeded')
        t = self.take()
        if t == '(':
            first = self.expr()
            if self.accept(','):
                items = [first]
                while not self.accept(')'):
                    items.append(self.expr())
                    if not self.accept(',') and self.peek() != ')':
                        raise Unsupported('expected comma in tuple expression')
                left = ('tuple', items)
            else:
                self.take(')')
                left = first
        elif t == '{':
            self.i -= 1; left = self.block()
        elif t == 'return': left = ('return', self.expr())
        elif t == '!': left = ('not', self.expr(80))
        elif t == 'if':
            binding = None
            if self.accept('let'):
                self.take('Some'); self.take('('); binding = self.name(); self.take(')'); self.take('=')
            cond = self.expr(); yes = self.block()
            no = ('unit',)
            if self.accept('else'):
                no = self.expr() if self.peek() == 'if' else self.block()
            left = ('iflet', binding, cond, yes, no) if binding else ('if', cond, yes, no)
        elif t == 'match':
            cond = self.expr(); self.take('{'); arms = {}
            while not self.accept('}'):
                tag = self.take(); binding = None
                if tag == 'Some': self.take('('); binding = self.name(); self.take(')')
                elif tag != 'None': raise Unsupported('match supports Some/None only')
                if tag in arms: raise Unsupported('duplicate match arm')
                self.take('=>'); arm = self.expr(); arms[tag] = (binding, arm)
                if not self.accept(',') and self.peek() != '}' and arm[0] != 'block':
                    raise Unsupported('missing match comma')
            if set(arms) != {'Some', 'None'}: raise Unsupported('non-exhaustive match')
            left = ('match', cond, arms)
        elif t == 'Authorization':
            self.take('{'); self.take('total_debit')
            val = self.expr() if self.accept(':') else ('var', 'total_debit')
            self.accept(','); self.take('}'); left = ('auth', val)
        elif t == 'Some':
            self.take('('); val = self.expr(); self.take(')'); left = ('some', val)
        elif t == 'None': left = ('none',)
        elif t in ('true', 'false'): left = ('bool', t == 'true')
        elif re.fullmatch(r'0x[0-9A-Fa-f_]+(?:u32|u64|u128)?', t):
            m = re.fullmatch(r'0x([0-9A-Fa-f_]+)(u32|u64|u128)?', t)
            if m[2] and m[2] not in self.int_types: raise Unsupported('unsupported integer width')
            left = ('num', int(m[1].replace('_', ''), 16), m[2])
        elif re.fullmatch(r'[0-9][0-9_]*(?:u32|u64|u128)?', t):
            m = re.fullmatch(r'([0-9_]+)(u32|u64|u128)?', t)
            if m[2] and m[2] not in self.int_types: raise Unsupported('unsupported integer width')
            left = ('num', int(m[1].replace('_', '')), m[2])
        elif t in ('u32', 'u64', 'u128') and self.accept('::'):
            if t not in self.int_types: raise Unsupported('unsupported integer width')
            item = self.take()
            width = 32 if t == 'u32' else 64 if t == 'u64' else 128
            if item == 'MAX': left = ('num', 2**width - 1, t)
            elif item == 'from' and t in ('u64', 'u128'):
                self.take('('); val = self.expr(); self.take(')'); left = ('cast', val, t)
            else: raise Unsupported('unsupported associated item')
        elif re.fullmatch('[A-Za-z_][A-Za-z_0-9]*', t):
            ident = t
            while self.allow_modules and self.accept('::'):
                ident = f'{ident}::{self.name()}'
            last_seg = ident.split('::')[-1]
            if self.allow_modules and last_seg in self.structs and self.peek() == '{':
                if '::' in ident:
                    raise Unsupported('qualified struct constructors require lexical resolution')
                self.take('{'); fvals = []
                while not self.accept('}'):
                    fname = self.name()
                    fexpr = self.expr() if self.accept(':') else ('var', fname)
                    fvals.append((fname, fexpr))
                    if not self.accept(',') and self.peek() != '}':
                        raise Unsupported('expected comma in struct literal')
                left = ('struct', last_seg, fvals)
            elif self.allow_modules and self.accept('('):
                args = []
                while not self.accept(')'):
                    args.append(self.expr())
                    if not self.accept(',') and self.peek() != ')':
                        raise Unsupported('expected comma in call arguments')
                left = ('call', ident, args)
            else:
                left = ('var', ident)
        else: raise Unsupported('unsupported expression: ' + t)
        precedence = {
            '||': 10, '&&': 20,
            '==': 30, '!=': 30, '<': 40, '>': 40, '<=': 40, '>=': 40,
            '|': 42, '^': 44, '&': 46, '<<': 48, '>>': 48,
            '+': 50, '-': 50, '*': 60, '/': 60, '%': 60,
        }
        while True:
            t = self.peek()
            if t == '.' and 90 >= minimum:
                self.take()
                if re.fullmatch(r'[0-9]+', self.peek()):
                    idx_tok = self.take()
                    left = ('tuple_index', left, int(idx_tok))
                    continue
                member = self.name()
                if self.accept('('):
                    arg = self.expr(); self.take(')')
                    if member not in ('checked_add', 'checked_sub', 'checked_mul', 'checked_div', 'checked_rem',
                                      'wrapping_add', 'wrapping_sub', 'wrapping_mul',
                                      'overflowing_add', 'overflowing_sub', 'overflowing_mul',
                                      'saturating_add', 'saturating_sub', 'div_ceil', 'then_some'):
                        raise Unsupported('unsupported method ' + member)
                    left = ('method', member, left, arg)
                elif self.allow_modules:
                    left = ('field', left, member)
                else:
                    raise Unsupported('field access unsupported')
            elif t == '?' and 90 >= minimum:
                self.take(); left = ('try', left)
            elif t == 'as' and 70 >= minimum:
                self.take(); ty = self.take()
                if ty not in self.int_types: raise Unsupported('unsupported cast')
                left = ('cast', left, ty)
            elif t in precedence and precedence[t] >= minimum:
                self.take(); left = ('binary', t, left, self.expr(precedence[t]+1))
            else: break
        return left


@dataclass
class Value:
    ty: object
    data: object = None


def _int_width(ty):
    if ty == 'u32': return 32
    if ty == 'u64': return 64
    if ty == 'u128': return 128
    raise Unsupported(f'expected integer type, got {ty}')


def check_val_type(v, expected_ty):
    if expected_ty in ('u32', 'u64', 'u128', 'bool'):
        return typed(v, expected_ty)
    if expected_ty == 'Authorization':
        if v.ty != 'auth': raise Unsupported('expected Authorization value')
        return v
    if isinstance(expected_ty, tuple) and expected_ty[0] == 'tuple':
        if not (isinstance(v.ty, tuple) and v.ty[0] == 'tuple' and len(v.data) == len(expected_ty[1])):
            raise Unsupported('tuple type mismatch')
        checked_items = [check_val_type(item, ety) for item, ety in zip(v.data, expected_ty[1])]
        return Value(('tuple', [c.ty for c in checked_items]), checked_items)
    if isinstance(expected_ty, tuple) and expected_ty[0] == 'struct':
        if v.ty != expected_ty: raise Unsupported(f'expected struct {expected_ty[1]}, got {v.ty}')
        return v
    if isinstance(expected_ty, tuple) and expected_ty[0] == 'Option':
        if v.ty == 'none': return v
        if v.ty == 'some':
            return Value('some', check_val_type(v.data, expected_ty[1]))
        raise Unsupported('expected Option value')
    raise Unsupported(f'unsupported type annotation: {expected_ty}')


def typed(v, ty):
    if v.ty == 'literal' and ty in ('u32', 'u64', 'u128'):
        w = _int_width(ty)
        if not 0 <= v.data < 2**w: raise Unsupported('literal out of range')
        return Value(ty, z3.IntVal(v.data))
    if v.ty != ty: raise Unsupported(f'type mismatch: {v.ty} vs {ty}')
    return v


def pair(a, b):
    if a.ty == 'literal' and b.ty == 'literal':
        raise Unsupported('two untyped integer operands require an explicit integer suffix')
    elif a.ty == 'literal': a = typed(a, b.ty)
    elif b.ty == 'literal': b = typed(b, a.ty)
    if a.ty != b.ty or a.ty not in ('u32', 'u64', 'u128'): raise Unsupported('integer operands required')
    return a, b, 2**_int_width(a.ty)


def _merge_ite_values(condition, v_true, v_false):
    if v_true.ty != v_false.ty:
        return None
    if v_true.ty in ('u32', 'u64', 'u128', 'bool'):
        return Value(v_true.ty, z3.If(condition, v_true.data, v_false.data))
    if isinstance(v_true.ty, tuple) and v_true.ty[0] == 'tuple' and len(v_true.data) == len(v_false.data):
        items = []
        for tv, fv in zip(v_true.data, v_false.data):
            mv = _merge_ite_values(condition, tv, fv)
            if mv is None:
                return None
            items.append(mv)
        return Value(v_true.ty, items)
    if isinstance(v_true.ty, tuple) and v_true.ty[0] == 'struct' and set(v_true.data) == set(v_false.data):
        fields = {}
        for k in v_true.data:
            mv = _merge_ite_values(condition, v_true.data[k], v_false.data[k])
            if mv is None:
                return None
            fields[k] = mv
        return Value(v_true.ty, fields)
    return None


class Interpreter:
    def __init__(self, structs=None, funcs=None, const_env=None, problem='authorization'):
        self.steps = 0
        self.structs = structs or {}
        self.funcs = funcs or {}
        self.const_env = const_env or {}
        self.call_depth = 0
        self.problem = problem
        self.stage_counterexample = None
    def _record_stage_cex(self, cond, vdict, fallback_res):
        if self.stage_counterexample is not None:
            return
        if 'amount' in vdict and 'fee' in vdict:
            gl_res = (vdict['amount'] + vdict['fee'] * (1 << 64)) % GOLDILOCKS_P
            rb = query(z3.And(cond, vdict['amount'] <= (1 << 62), gl_res <= (1 << 62)), vdict)
            if rb['status'] == 'fail':
                self.stage_counterexample = rb['counterexample']
                return
        if 'amount' in vdict:
            rb = query(z3.And(cond, vdict['amount'] <= (1 << 62)), vdict)
            if rb['status'] == 'fail':
                self.stage_counterexample = rb['counterexample']
                return
        if fallback_res['status'] == 'fail':
            cex = dict(fallback_res['counterexample'])
            cex.setdefault('amount', 0)
            self.stage_counterexample = cex
    def _apply_stage_cut(self, fname, out):
        if self.problem != 'zk-clearing' or len(out) != 1:
            return out
        g, rval = out[0]
        if rval.ty == 'return' or not (isinstance(rval.ty, tuple) and rval.ty[0] == 'struct'):
            return out
        short = fname.split('::')[-1]
        a_var, f_var = z3.Int('amount'), z3.Int('fee')
        if short == 'evaluate_settlement_fee' and rval.ty[1] == 'FeeQuote':
            t_gross = (a_var + f_var + 9999) / 10000
            t_reb = t_gross / 10
            t_net = t_gross - t_reb
            cond = z3.Or(
                rval.data['gross_fee'].data != t_gross,
                rval.data['rebate'].data != t_reb,
                rval.data['net_fee'].data != t_net,
            )
            res = query(cond, {'amount': a_var, 'fee': f_var})
            if res['status'] == 'pass':
                nd = dict(rval.data)
                nd['gross_fee'] = Value('u64', t_gross)
                nd['rebate'] = Value('u64', t_reb)
                nd['net_fee'] = Value('u64', t_net)
                return [(g, Value(rval.ty, nd))]
            self._record_stage_cex(cond, {'amount': a_var, 'fee': f_var}, res)
        elif short == 'quote_flash_lp_retention' and rval.ty[1] == 'PoolReserveQuote':
            t_flash = (a_var + f_var + 4999) / 5000
            t_cut = t_flash / 4
            t_lp = t_flash - t_cut
            cond = z3.Or(
                rval.data['treasury_cut'].data != t_cut,
                rval.data['lp_retention'].data != t_lp,
            )
            res = query(cond, {'amount': a_var, 'fee': f_var})
            if res['status'] == 'pass':
                nd = dict(rval.data)
                nd['treasury_cut'] = Value('u64', t_cut)
                nd['lp_retention'] = Value('u64', t_lp)
                return [(g, Value(rval.ty, nd))]
            self._record_stage_cex(cond, {'amount': a_var, 'fee': f_var}, res)
        elif short == 'quote_blob_gas_slots' and rval.ty[1] == 'BlobSlotQuote':
            b16 = 1 << 16
            u1 = f_var % RUINT_MG10_D
            u0 = a_var % b16
            u = u1 * b16 + u0
            t_q = u / RUINT_MG10_D
            t_r = u % RUINT_MG10_D
            cond = z3.Or(
                rval.data['slot_quotient'].data != t_q,
                rval.data['slot_remainder'].data != t_r,
            )
            res = query(cond, {'amount': a_var, 'fee': f_var})
            if res['status'] == 'pass':
                nd = dict(rval.data)
                nd['high_limb'] = Value('u64', u1)
                nd['low_limb'] = Value('u64', u0)
                nd['slot_quotient'] = Value('u64', t_q)
                nd['slot_remainder'] = Value('u64', t_r)
                return [(g, Value(rval.ty, nd))]
            self._record_stage_cex(cond, {'amount': a_var, 'fee': f_var}, res)
        elif short == 'quote_calldata_lane_surcharge' and rval.ty[1] == 'CalldataLaneQuote':
            bs = [_byte_at_z3(f_var, i) for i in range(8)]
            t_nz = sum(z3.If(bi > 0, 1, 0) for bi in bs)
            t_sum = sum(bs)
            t_sur = t_nz * 256 + t_sum
            cond = z3.Or(
                rval.data['surcharge'].data != t_sur,
                rval.data['active_lanes'].data != t_nz,
                rval.data['byte_weight_sum'].data != t_sum,
            )
            res = query(cond, {'fee': f_var})
            if res['status'] == 'pass':
                nd = dict(rval.data)
                nd['active_lanes'] = Value('u64', t_nz)
                nd['byte_weight_sum'] = Value('u64', t_sum)
                nd['surcharge'] = Value('u64', t_sur)
                return [(g, Value(rval.ty, nd))]
            self._record_stage_cex(cond, {'fee': f_var}, res)
        elif short == 'quote_prover_transcript_levy' and rval.ty[1] == 'ProverLevyQuote':
            b32 = 1 << 32
            t_pack = (a_var % b32) + (f_var % PLONKY3_P) * b32
            t_levy = (t_pack * PLONKY3_R_INV) % PLONKY3_P
            cond = z3.Or(
                rval.data['prover_levy'].data != t_levy,
                rval.data['packed_transcript'].data != t_pack,
            )
            res = query(cond, {'amount': a_var, 'fee': f_var})
            if res['status'] == 'pass':
                nd = dict(rval.data)
                nd['packed_transcript'] = Value('u64', t_pack)
                nd['prover_levy'] = Value('u64', t_levy)
                return [(g, Value(rval.ty, nd))]
            self._record_stage_cex(cond, {'amount': a_var, 'fee': f_var}, res)
        elif short == 'quote_bridge_verifier_fee' and rval.ty[1] == 'GoldilocksQuote':
            t_res = (a_var + f_var * (1 << 64)) % GOLDILOCKS_P
            cond = z3.Or(
                rval.data['canonical_residue'].data != t_res,
                rval.data['bridge_fee'].data != t_res,
            )
            res = query(cond, {'amount': a_var, 'fee': f_var})
            if res['status'] == 'pass':
                nd = dict(rval.data)
                nd['canonical_residue'] = Value('u64', t_res)
                nd['bridge_fee'] = Value('u64', t_res)
                return [(g, Value(rval.ty, nd))]
            self._record_stage_cex(cond, {'amount': a_var, 'fee': f_var}, res)
        return out
    def evaluate(self, e, env, guard):
        self.steps += 1
        if self.steps > 65536: raise Unsupported('symbolic expansion limit exceeded')
        k = e[0]
        if k == 'block':
            active = [(guard, dict(env))]; completed = []
            for stmt in e[1]:
                next_active = []
                for g, local in active:
                    kind = stmt[0]
                    rhs = stmt[3] if kind in ('let', 'let_tuple') else stmt[2] if kind == 'assign' else stmt[1]
                    for h, val in self.evaluate(rhs, local, g):
                        if val.ty == 'return': completed.append((h, val)); continue
                        if kind == 'tail': completed.append((h, val)); continue
                        new_env = dict(local)
                        if kind == 'let':
                            if stmt[2]: val = check_val_type(val, stmt[2])
                            if val.ty == 'literal': raise Unsupported('integer let needs explicit type annotation')
                            new_env[stmt[1]] = val
                        elif kind == 'let_tuple':
                            names, ty_ann = stmt[1], stmt[2]
                            if ty_ann: val = check_val_type(val, ty_ann)
                            if not (isinstance(val.ty, tuple) and val.ty[0] == 'tuple' and len(val.data) == len(names)):
                                raise Unsupported('let tuple destructuring requires matching tuple value')
                            for nm, elem in zip(names, val.data):
                                if elem.ty == 'literal': raise Unsupported('tuple element needs explicit type')
                                new_env[nm] = elem
                        elif kind == 'assign':
                            target_name = stmt[1]
                            if target_name not in new_env: raise Unsupported('assignment to unbound variable ' + target_name)
                            expected_ty = new_env[target_name].ty
                            new_env[target_name] = check_val_type(val, expected_ty)
                        next_active.append((h, new_env))
                active = next_active
            return completed + [(g, Value('unit')) for g, _ in active]
        if k == 'var':
            name = e[1]
            if name in env: return [(guard, env[name])]
            if name in self.const_env: return [(guard, self.const_env[name])]
            raise Unsupported('unbound name: ' + name)
        if k == 'num':
            val = Value('literal', e[1]); val = typed(val, e[2]) if e[2] else val
            return [(guard, val)]
        if k == 'bool': return [(guard, Value('bool', z3.BoolVal(e[1])))]
        if k in ('none', 'unit'): return [(guard, Value(k))]
        if k == 'tuple':
            items = e[1]
            active = [(guard, [])]
            for item_expr in items:
                next_active = []
                for g, acc in active:
                    if isinstance(acc, Value) and acc.ty == 'return':
                        next_active.append((g, acc)); continue
                    for h, v in self.evaluate(item_expr, env, g):
                        if v.ty == 'return': next_active.append((h, v)); continue
                        next_active.append((h, acc + [v]))
                active = next_active
            out = []
            for g, acc in active:
                if isinstance(acc, Value) and acc.ty == 'return': out.append((g, acc))
                else: out.append((g, Value(('tuple', [x.ty for x in acc]), acc)))
            return out
        if k == 'tuple_index':
            target, idx = e[1], e[2]
            out = []
            for g, val in self.evaluate(target, env, guard):
                if val.ty == 'return': out.append((g, val)); continue
                if not (isinstance(val.ty, tuple) and val.ty[0] == 'tuple' and 0 <= idx < len(val.data)):
                    raise Unsupported(f'invalid tuple index .{idx}')
                out.append((g, val.data[idx]))
            return out
        if k == 'struct':
            sname, fexprs = e[1], e[2]
            if sname not in self.structs: raise Unsupported('unknown struct ' + sname)
            schema = self.structs[sname]
            if {fn for fn, _ in fexprs} != set(schema): raise Unsupported('struct field mismatch for ' + sname)
            active = [(guard, {})]
            for fname, fexpr in fexprs:
                next_active = []
                for g, fdict in active:
                    for h, fval in self.evaluate(fexpr, env, g):
                        if fval.ty == 'return': next_active.append((h, fval)); continue
                        checked = check_val_type(fval, schema[fname])
                        nd = dict(fdict); nd[fname] = checked
                        next_active.append((h, nd))
                active = next_active
            out = []
            for g, item in active:
                if isinstance(item, Value) and item.ty == 'return': out.append((g, item))
                else: out.append((g, Value(('struct', sname), item)))
            return out
        if k == 'field':
            target, fname = e[1], e[2]
            out = []
            for g, val in self.evaluate(target, env, guard):
                if val.ty == 'return': out.append((g, val)); continue
                if val.ty == 'auth' and fname == 'total_debit':
                    out.append((g, Value('u64', val.data)))
                elif isinstance(val.ty, tuple) and val.ty[0] == 'struct' and fname in val.data:
                    out.append((g, val.data[fname]))
                else:
                    raise Unsupported(f'invalid field access .{fname}')
            return out
        if k == 'call':
            fname, arg_exprs = e[1], e[2]
            fn_def = self.funcs.get(fname)
            if not fn_def: raise Unsupported('unknown function ' + fname)
            params, ret_ty, fbody = fn_def
            if len(arg_exprs) != len(params): raise Unsupported('argument count mismatch in ' + fname)
            if self.call_depth >= 8: raise Unsupported('call depth limit exceeded')
            active = [(guard, [])]
            for (_, pty), aexpr in zip(params, arg_exprs):
                next_active = []
                for g, alist in active:
                    if isinstance(alist, Value) and alist.ty == 'return':
                        next_active.append((g, alist)); continue
                    for h, aval in self.evaluate(aexpr, env, g):
                        if aval.ty == 'return': next_active.append((h, aval)); continue
                        checked = check_val_type(aval, pty)
                        next_active.append((h, alist + [checked]))
                active = next_active
            out = []
            self.call_depth += 1
            try:
                for g, alist in active:
                    if isinstance(alist, Value) and alist.ty == 'return':
                        out.append((g, alist)); continue
                    callee_env = dict(self.const_env)
                    for (pname, _), aval in zip(params, alist):
                        callee_env[pname] = aval
                    for h, rval in self.evaluate(fbody, callee_env, g):
                        if rval.ty == 'return': rval = rval.data
                        out.append((h, check_val_type(rval, ret_ty)))
            finally:
                self.call_depth -= 1
            return self._apply_stage_cut(fname, out)
        if k in ('some', 'auth', 'return', 'try', 'cast', 'not'):
            out = []
            for g, val in self.evaluate(e[1], env, guard):
                if val.ty == 'return': out.append((g, val)); continue
                if k == 'some': val = Value('some', val)
                elif k == 'auth': val = Value('auth', typed(val, 'u64').data)
                elif k == 'return': val = Value('return', val)
                elif k == 'try':
                    if val.ty == 'none': val = Value('return', Value('none'))
                    elif val.ty == 'some': val = val.data
                    else: raise Unsupported('? requires Option')
                elif k == 'cast':
                    target_ty = e[2]
                    if val.ty == 'literal': val = typed(val, target_ty)
                    elif val.ty in ('u32', 'u64', 'u128'):
                        src_w, dst_w = _int_width(val.ty), _int_width(target_ty)
                        val = Value(target_ty, val.data if dst_w >= src_w else (val.data % 2**dst_w))
                    else: raise Unsupported('integer cast required')
                elif k == 'not': val = Value('bool', z3.Not(typed(val, 'bool').data))
                out.append((g, val))
            return out
        if k in ('if', 'iflet', 'match'):
            cond = e[1] if k in ('if', 'match') else e[2]; out = []
            for g, val in self.evaluate(cond, env, guard):
                if val.ty == 'return': out.append((g, val)); continue
                if k == 'if':
                    condition = typed(val, 'bool').data
                    tp = self.evaluate(e[2], env, z3.And(g, condition))
                    fp = self.evaluate(e[3], env, z3.And(g, z3.Not(condition)))
                    merged_val = (
                        _merge_ite_values(condition, tp[0][1], fp[0][1])
                        if len(tp) == 1 and len(fp) == 1
                        else None
                    )
                    if merged_val is not None:
                        out.append((g, merged_val))
                    else:
                        out += tp + fp
                else:
                    if val.ty not in ('some', 'none'): raise Unsupported('Option pattern required')
                    local = dict(env)
                    if k == 'iflet':
                        if val.ty == 'some': local[e[1]] = val.data
                        arm = e[3] if val.ty == 'some' else e[4]
                    else:
                        name, arm = e[2]['Some' if val.ty == 'some' else 'None']
                        if name: local[name] = val.data
                    out += self.evaluate(arm, local, g)
            return out
        if k in ('binary', 'method'):
            op = e[1]; out = []
            for g, a in self.evaluate(e[2], env, guard):
                if a.ty == 'return': out.append((g, a)); continue
                rhs_guard = g
                if op in ('&&', '||'):
                    condition = typed(a, 'bool').data
                    short = z3.Not(condition) if op == '&&' else condition
                    out.append((z3.And(g, short), Value('bool', z3.BoolVal(op == '||'))))
                    rhs_guard = z3.And(g, z3.Not(short))
                for h, b in self.evaluate(e[3], env, rhs_guard):
                    if b.ty == 'return': out.append((h, b)); continue
                    if op in ('&&', '||'):
                        out.append((h, typed(b, 'bool'))); continue
                    if op == 'then_some':
                        condition = typed(a, 'bool').data
                        out += [(z3.And(h, condition), Value('some', b)), (z3.And(h, z3.Not(condition)), Value('none'))]
                        continue
                    if op in ('<<', '>>'):
                        a_typed = typed(a, b.ty) if a.ty == 'literal' and b.ty in ('u32', 'u64', 'u128') else a
                        if a_typed.ty not in ('u32', 'u64', 'u128'):
                            raise Unsupported('shift LHS requires explicit integer type')
                        w = _int_width(a_typed.ty)
                        mod_w = 1 << w
                        shift_expr = z3.IntVal(b.data) if b.ty == 'literal' else b.data
                        ys = z3.simplify(shift_expr)
                        if not z3.is_int_value(ys) or not 0 <= ys.as_long() < w:
                            raise Unsupported('shift requires constant shift amount within type width')
                        factor = 1 << ys.as_long()
                        res = (a_typed.data * factor) % mod_w if op == '<<' else (a_typed.data / factor)
                        out.append((h, Value(a_typed.ty, res)))
                        continue
                    a1, b1, modulus = pair(a, b); x, y = a1.data, b1.data
                    if op in ('checked_add', 'checked_sub'):
                        result = x+y if op == 'checked_add' else x-y
                        ok = z3.And(result >= 0, result < modulus)
                        out += [(z3.And(h, ok), Value('some', Value(a1.ty, result))),
                                (z3.And(h, z3.Not(ok)), Value('none'))]
                    elif op == 'checked_mul':
                        result = x*y
                        ok = z3.And(result >= 0, result < modulus)
                        out += [(z3.And(h, ok), Value('some', Value(a1.ty, result))),
                                (z3.And(h, z3.Not(ok)), Value('none'))]
                    elif op in ('overflowing_add', 'overflowing_sub', 'overflowing_mul'):
                        if op == 'overflowing_add':
                            raw = x + y
                            wrapped = z3.If(raw >= modulus, raw - modulus, raw)
                            ovf = raw >= modulus
                        elif op == 'overflowing_sub':
                            wrapped = z3.If(x >= y, x - y, x + modulus - y)
                            ovf = x < y
                        else:
                            raw = x * y
                            wrapped = raw % modulus
                            ovf = raw >= modulus
                        tup = Value(('tuple', [a1.ty, 'bool']), [Value(a1.ty, wrapped), Value('bool', ovf)])
                        out.append((h, tup))
                    elif op in ('checked_div', 'checked_rem'):
                        ys = z3.simplify(y)
                        if not z3.is_int_value(ys): raise Unsupported('division/modulo requires constant divisor')
                        if ys.as_long() == 0:
                            out.append((h, Value('none')))
                        else:
                            res = x / ys if op == 'checked_div' else x % ys
                            out.append((h, Value('some', Value(a1.ty, res))))
                    elif op in ('+', '-', 'wrapping_add', 'wrapping_sub'):
                        if op in ('+', 'wrapping_add'):
                            raw = x + y
                            wrapped = z3.If(raw >= modulus, raw - modulus, raw)
                        else:
                            wrapped = z3.If(x >= y, x - y, x + modulus - y)
                        out.append((h, Value(a1.ty, wrapped)))
                    elif op in ('*', 'wrapping_mul'):
                        out.append((h, Value(a1.ty, (x*y) % modulus)))
                    elif op == '&':
                        out.append((h, Value(a1.ty, _bitand_z3(x, y) % modulus)))
                    elif op == '|':
                        out.append((h, Value(a1.ty, _bitor_z3(x, y) % modulus)))
                    elif op == '^':
                        out.append((h, Value(a1.ty, _bitxor_z3(x, y) % modulus)))
                    elif op in ('/', '%', 'div_ceil'):
                        ys = z3.simplify(y)
                        if not z3.is_int_value(ys): raise Unsupported('division/modulo requires constant divisor')
                        if ys.as_long() > 0:
                            if op == '/': res = x / ys
                            elif op == '%': res = x % ys
                            else: res = z3.If(x == 0, z3.IntVal(0), ((x - 1) / ys) + 1)
                            out.append((h, Value(a1.ty, res)))
                    elif op == 'saturating_add': out.append((h, Value(a1.ty, z3.If(x+y < modulus, x+y, modulus-1))))
                    elif op == 'saturating_sub': out.append((h, Value(a1.ty, z3.If(x >= y, x-y, z3.IntVal(0)))))
                    else:
                        comparison = {'<': lambda: x<y, '>': lambda: x>y, '<=': lambda: x<=y, '>=': lambda: x>=y,
                                      '==': lambda: x==y, '!=': lambda: x!=y}
                        if op not in comparison: raise Unsupported('unsupported operator')
                        out.append((h, Value('bool', comparison[op]())))
            return out
        raise Unsupported('unsupported AST node ' + k)


def check(source, problem='authorization', fallback_dir=None):
    source = bundle_crate_source(source, fallback_dir=fallback_dir)
    is_extended = (
        problem == 'settlement'
        or problem.startswith('settlement-')
        or problem in ('goldilocks', 'whirlpool', 'plonky3', 'succinct', 'openpql', 'ruint', 'zk-clearing')
    )
    consts, structs, funcs, names, body = Parser(
        source, allow_u128=not is_extended, allow_modules=is_extended
    ).program()
    const_env = {}
    boot_interp = Interpreter(structs=structs, funcs=funcs, const_env=const_env, problem=problem)
    for qual, cname, cty, cexpr in consts:
        cpaths = boot_interp.evaluate(cexpr, const_env, z3.BoolVal(True))
        if len(cpaths) != 1: raise Unsupported('const expression must be unconditional')
        cval = typed(cpaths[0][1], cty)
        csimp = z3.simplify(cval.data)
        if not z3.is_int_value(csimp): raise Unsupported('const must fold to an integer constant')
        v = Value(cty, csimp)
        const_env[qual] = v
        const_env[cname] = v
        const_env[f'crate::{qual}'] = v
        const_env[f'super::{qual}'] = v
    interp = Interpreter(structs=structs, funcs=funcs, const_env=const_env, problem=problem)
    env = dict(const_env)
    variables = {k: z3.Int(k) for k in ('balance', 'amount', 'fee')}
    for n, v in zip(names, variables.values()):
        env[n] = Value('u64', v)
    paths = interp.evaluate(body, env, z3.BoolVal(True))
    expected = expected_debit_z3(variables['amount'], variables['fee'], problem)
    accepted = expected <= variables['balance']
    mismatches = []
    for guard, val in paths:
        if val.ty == 'return': val = val.data
        if val.ty == 'none': mismatch = accepted
        elif val.ty == 'some' and val.data.ty == 'auth':
            mismatch = z3.Or(z3.Not(accepted), val.data.data != expected)
        else: raise Unsupported('authorize must return Option<Authorization> on every path')
        mismatches.append(z3.And(guard, mismatch))
    # Require both path coverage and correct Some/None and exact total.
    counterexample = z3.Or(z3.Not(z3.Or(*[g for g, _ in paths])), *mismatches)
    result = None
    if interp.stage_counterexample:
        pin = [variables[k] == val for k, val in interp.stage_counterexample.items() if k in variables]
        if pin:
            seeded = query(z3.And(counterexample, *pin), variables)
            if seeded['status'] == 'fail':
                result = seeded
    if result is None:
        result = query(counterexample, variables)
    prop = ('Some iff mathematical amount+fee<=balance; Some.total_debit=amount+fee'
            if problem == 'authorization' else
            f'Some iff mathematical {problem} debit<=balance; Some.total_debit={problem} debit')
    result.update(backend='bounded Rust subset / Z3 4.13.3; exact full u64 input domain', paths=len(paths),
                  property=prop)
    return result

