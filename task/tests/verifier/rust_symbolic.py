"""Fail-closed Rust subset interpreter. See BACKEND.md for the correspondence claim."""
from dataclasses import dataclass
import re
import z3
from spec import MAX, Unsupported, expected_debit_z3, query

TOKEN = re.compile(r'\s+|//[^\n]*|/\*|"(?:\\.|[^"\\])*"|[A-Za-z_][A-Za-z_0-9]*|[0-9][0-9_]*(?:u64|u128)?|::|->|=>|<=|>=|==|!=|&&|\|\||[^\s]')


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
    if len(out) > 12000: raise Unsupported('Rust token limit exceeded')
    return out


class Parser:
    def __init__(self, source, allow_u128=True, allow_modules=False):
        self.ts = tokenize(source); self.i = 0; self.nodes = 0
        self.int_types = ('u64', 'u128') if allow_u128 else ('u64',)
        self.allow_modules = allow_modules
        self.structs = {}
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
        if t in self.int_types or t == 'bool': return t
        if t == 'Option':
            self.take('<'); inner = self.parse_type(); self.take('>')
            return ('Option', inner)
        if t == 'Authorization': return 'Authorization'
        if self.allow_modules and t in self.structs: return ('struct', t)
        raise Unsupported(f'unsupported type: {t}')
    def register_aliases(self, table, mod_prefix, short_name, value):
        table[short_name] = value
        if mod_prefix:
            table[f'{mod_prefix}::{short_name}'] = value
            table[f'crate::{mod_prefix}::{short_name}'] = value
            table[f'super::{mod_prefix}::{short_name}'] = value
    def const_decl(self, consts, mod_prefix=''):
        cname = self.name(); self.take(':'); cty = self.take()
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
                while not self.accept(';'): self.take()
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
                mname = self.name(); self.take('{')
                self.parse_items(state, mod_prefix=mname)
                self.take('}')
            elif item == 'struct':
                sname = self.name()
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
                fname = self.name()
                if fname == 'authorize' and not mod_prefix:
                    if not is_pub or state['body'] is not None: raise Unsupported('duplicate or private authorize')
                    self.take('('); names = []
                    for n in range(3):
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
                name = self.name(); ty = None
                if self.accept(':'):
                    ty = self.parse_type()
                self.take('='); value = self.expr(); self.take(';')
                statements.append(('let', name, ty, value))
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
        if self.nodes > 1024: raise Unsupported('expression limit exceeded')
        t = self.take()
        if t == '(':
            left = self.expr(); self.take(')')
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
        elif re.fullmatch(r'[0-9][0-9_]*(?:u64|u128)?', t):
            m = re.fullmatch(r'([0-9_]+)(u64|u128)?', t)
            if m[2] and m[2] not in self.int_types: raise Unsupported('unsupported integer width')
            left = ('num', int(m[1].replace('_', '')), m[2])
        elif t in ('u64', 'u128') and self.accept('::'):
            if t not in self.int_types: raise Unsupported('unsupported integer width')
            item = self.take()
            if item == 'MAX': left = ('num', 2**(64 if t == 'u64' else 128)-1, t)
            elif item == 'from' and t == 'u128':
                self.take('('); val = self.expr(); self.take(')'); left = ('cast', val, 'u128')
            else: raise Unsupported('unsupported associated item')
        elif re.fullmatch('[A-Za-z_][A-Za-z_0-9]*', t):
            ident = t
            while self.allow_modules and self.accept('::'):
                ident = f'{ident}::{self.name()}'
            last_seg = ident.split('::')[-1]
            if self.allow_modules and last_seg in self.structs and self.peek() == '{':
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
        precedence = {'||': 10, '&&': 20, '==': 30, '!=': 30, '<': 40, '>': 40, '<=': 40, '>=': 40, '+': 50, '-': 50, '*': 60, '/': 60, '%': 60}
        while True:
            t = self.peek()
            if t == '.' and 90 >= minimum:
                self.take(); member = self.name()
                if self.accept('('):
                    arg = self.expr(); self.take(')')
                    if member not in ('checked_add', 'checked_sub', 'checked_mul', 'checked_div', 'checked_rem',
                                      'wrapping_add', 'wrapping_sub', 'wrapping_mul', 'saturating_add', 'saturating_sub',
                                      'div_ceil', 'then_some'):
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


def check_val_type(v, expected_ty):
    if expected_ty in ('u64', 'u128', 'bool'):
        return typed(v, expected_ty)
    if expected_ty == 'Authorization':
        if v.ty != 'auth': raise Unsupported('expected Authorization value')
        return v
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
    if v.ty == 'literal' and ty in ('u64', 'u128'):
        if not 0 <= v.data < 2**(64 if ty == 'u64' else 128): raise Unsupported('literal out of range')
        return Value(ty, z3.IntVal(v.data))
    if v.ty != ty: raise Unsupported(f'type mismatch: {v.ty} vs {ty}')
    return v


def pair(a, b):
    if a.ty == 'literal' and b.ty == 'literal':
        # Rust can default an uncontextualized literal expression to i32.
        # Guessing u64 here would miss signed negative intermediates. Require
        # an explicit suffix or an already typed operand instead.
        raise Unsupported('two untyped integer operands require an explicit u64/u128 suffix')
    elif a.ty == 'literal': a = typed(a, b.ty)
    elif b.ty == 'literal': b = typed(b, a.ty)
    if a.ty != b.ty or a.ty not in ('u64', 'u128'): raise Unsupported('integer operands required')
    return a, b, 2**(64 if a.ty == 'u64' else 128)


class Interpreter:
    def __init__(self, structs=None, funcs=None, const_env=None):
        self.steps = 0
        self.structs = structs or {}
        self.funcs = funcs or {}
        self.const_env = const_env or {}
        self.call_depth = 0
    def evaluate(self, e, env, guard):
        self.steps += 1
        if self.steps > 8192: raise Unsupported('symbolic expansion limit exceeded')
        k = e[0]
        if k == 'block':
            active = [(guard, dict(env))]; completed = []
            for stmt in e[1]:
                next_active = []
                for g, local in active:
                    rhs = stmt[3] if stmt[0] == 'let' else stmt[1]
                    for h, val in self.evaluate(rhs, local, g):
                        if val.ty == 'return': completed.append((h, val)); continue
                        if stmt[0] == 'tail': completed.append((h, val)); continue
                        new_env = dict(local)
                        if stmt[0] == 'let':
                            if stmt[2]: val = check_val_type(val, stmt[2])
                            # Rust defaults unconstrained integer lets to i32, outside this subset.
                            if val.ty == 'literal': raise Unsupported('integer let needs u64/u128 annotation')
                            new_env[stmt[1]] = val
                        next_active.append((h, new_env))
                active = next_active
            return completed + [(g, Value('unit')) for g, _ in active]
        if k == 'var':
            name = e[1]
            if name in env: return [(guard, env[name])]
            if name in self.const_env: return [(guard, self.const_env[name])]
            short = name.split('::')[-1]
            if short in self.const_env: return [(guard, self.const_env[short])]
            raise Unsupported('unbound name: ' + name)
        if k == 'num':
            val = Value('literal', e[1]); val = typed(val, e[2]) if e[2] else val
            return [(guard, val)]
        if k == 'bool': return [(guard, Value('bool', z3.BoolVal(e[1])))]
        if k in ('none', 'unit'): return [(guard, Value(k))]
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
            fn_def = self.funcs.get(fname) or self.funcs.get(fname.split('::')[-1])
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
            return out
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
                    if val.ty == 'literal': val = typed(val, e[2])
                    elif val.ty in ('u64', 'u128'): val = Value(e[2], val.data % 2**(64 if e[2] == 'u64' else 128))
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
                    out += self.evaluate(e[2], env, z3.And(g, condition))
                    out += self.evaluate(e[3], env, z3.And(g, z3.Not(condition)))
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
                    a1, b1, modulus = pair(a, b); x, y = a1.data, b1.data
                    if op in ('checked_add', 'checked_sub'):
                        result = x+y if op == 'checked_add' else x-y
                        ok = z3.And(result >= 0, result < modulus)
                        out += [(z3.And(h, ok), Value('some', Value(a1.ty, result))),
                                (z3.And(h, z3.Not(ok)), Value('none'))]
                    elif op == 'checked_mul':
                        xs, ys = z3.simplify(x), z3.simplify(y)
                        if not (z3.is_int_value(xs) or z3.is_int_value(ys)):
                            raise Unsupported('nonlinear multiplication')
                        result = x*y
                        ok = z3.And(result >= 0, result < modulus)
                        out += [(z3.And(h, ok), Value('some', Value(a1.ty, result))),
                                (z3.And(h, z3.Not(ok)), Value('none'))]
                    elif op in ('checked_div', 'checked_rem'):
                        ys = z3.simplify(y)
                        if not z3.is_int_value(ys): raise Unsupported('division/modulo requires constant divisor')
                        if ys.as_long() == 0:
                            out.append((h, Value('none')))
                        else:
                            res = x / ys if op == 'checked_div' else x % ys
                            out.append((h, Value('some', Value(a1.ty, res))))
                    elif op in ('+', '-', 'wrapping_add', 'wrapping_sub'):
                        out.append((h, Value(a1.ty, ((x+y) if op in ('+', 'wrapping_add') else (x-y)) % modulus)))
                    elif op in ('*', 'wrapping_mul'):
                        xs, ys = z3.simplify(x), z3.simplify(y)
                        if not (z3.is_int_value(xs) or z3.is_int_value(ys)):
                            raise Unsupported('nonlinear multiplication')
                        out.append((h, Value(a1.ty, (x*y) % modulus)))
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


def check(source, problem='authorization'):
    is_settlement = (problem == 'settlement' or problem.startswith('settlement-'))
    consts, structs, funcs, names, body = Parser(
        source, allow_u128=not is_settlement, allow_modules=is_settlement
    ).program()
    const_env = {}
    boot_interp = Interpreter(structs=structs, funcs=funcs, const_env=const_env)
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
    interp = Interpreter(structs=structs, funcs=funcs, const_env=const_env)
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
    result = query(counterexample, variables)
    prop = ('Some iff mathematical amount+fee<=balance; Some.total_debit=amount+fee'
            if problem == 'authorization' else
            'Some iff mathematical settlement debit<=balance; Some.total_debit=settlement debit')
    result.update(backend='bounded Rust subset / Z3 4.13.3; exact full u64 input domain', paths=len(paths),
                  property=prop)
    return result

