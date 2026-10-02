"""Fail-closed Rust subset interpreter. See BACKEND.md for the correspondence claim."""
from dataclasses import dataclass
import re
import z3
from spec import MAX, Unsupported, query

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
    def __init__(self, source):
        self.ts = tokenize(source); self.i = 0; self.nodes = 0
    def peek(self): return self.ts[self.i] if self.i < len(self.ts) else '<eof>'
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
    def program(self):
        struct = None; body = None; names = None
        while self.peek() != '<eof>':
            if self.accept('#'):
                attr = self.group('[', ']')
                if attr == ['cfg', '(', 'test', ')']:
                    self.take('mod'); self.name(); self.group('{', '}'); continue
                if not (attr[:2] == ['derive', '('] and attr[-1:] == [')'] and
                        set(attr[2:-1]) <= {'Debug', 'Clone', 'Copy', 'PartialEq', 'Eq', ','}):
                    raise Unsupported('only built-in derives and #[cfg(test)] modules are supported')
                # An attribute must attach to the one Authorization struct.
                self.take('pub'); self.take('struct')
                if struct is not None: raise Unsupported('duplicate struct')
                self.take('Authorization'); self.structure(); struct = True
                continue
            self.take('pub'); item = self.take()
            if item == 'struct':
                if struct is not None: raise Unsupported('duplicate struct')
                self.take('Authorization'); self.structure(); struct = True
            elif item == 'fn':
                if body is not None: raise Unsupported('duplicate function')
                self.take('authorize'); self.take('('); names = []
                for n in range(3):
                    names.append(self.name()); self.take(':'); self.take('u64')
                    if n < 2: self.take(',')
                self.accept(','); self.take(')'); self.take('->')
                self.take('Option'); self.take('<'); self.take('Authorization'); self.take('>')
                if len(set(names)) != 3: raise Unsupported('duplicate parameters')
                body = self.block()
            else: raise Unsupported('only Authorization and authorize production items are supported')
        if struct is None or body is None: raise Unsupported('missing public API')
        return names, body
    def structure(self):
        self.take('{'); self.take('pub'); self.take('total_debit'); self.take(':'); self.take('u64')
        self.accept(','); self.take('}')
    def block(self):
        self.take('{'); statements = []
        while not self.accept('}'):
            if self.accept('let'):
                name = self.name(); ty = None
                if self.accept(':'):
                    ty = self.take()
                    if ty not in ('u64', 'u128'): raise Unsupported('unsupported let type')
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
        if self.nodes > 512: raise Unsupported('expression limit exceeded')
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
            left = ('num', int(m[1].replace('_', '')), m[2])
        elif t in ('u64', 'u128') and self.accept('::'):
            item = self.take()
            if item == 'MAX': left = ('num', 2**(64 if t == 'u64' else 128)-1, t)
            elif item == 'from' and t == 'u128':
                self.take('('); val = self.expr(); self.take(')'); left = ('cast', val, 'u128')
            else: raise Unsupported('unsupported associated item')
        elif re.fullmatch('[A-Za-z_][A-Za-z_0-9]*', t): left = ('var', t)
        else: raise Unsupported('unsupported expression: ' + t)
        precedence = {'||': 10, '&&': 20, '==': 30, '!=': 30, '<': 40, '>': 40, '<=': 40, '>=': 40, '+': 50, '-': 50}
        while True:
            t = self.peek()
            if t == '.' and 90 >= minimum:
                self.take(); method = self.name(); self.take('('); arg = self.expr(); self.take(')')
                if method not in ('checked_add', 'checked_sub', 'wrapping_add', 'wrapping_sub', 'saturating_add', 'then_some'):
                    raise Unsupported('unsupported method ' + method)
                left = ('method', method, left, arg)
            elif t == '?' and 90 >= minimum:
                self.take(); left = ('try', left)
            elif t == 'as' and 70 >= minimum:
                self.take(); ty = self.take()
                if ty not in ('u64', 'u128'): raise Unsupported('unsupported cast')
                left = ('cast', left, ty)
            elif t in precedence and precedence[t] >= minimum:
                self.take(); left = ('binary', t, left, self.expr(precedence[t]+1))
            else: break
        return left


@dataclass
class Value:
    ty: str
    data: object = None


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
    def __init__(self): self.steps = 0
    def evaluate(self, e, env, guard):
        self.steps += 1
        if self.steps > 4096: raise Unsupported('symbolic expansion limit exceeded')
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
                            if stmt[2]: val = typed(val, stmt[2])
                            # Rust defaults unconstrained integer lets to i32, outside this subset.
                            if val.ty == 'literal': raise Unsupported('integer let needs u64/u128 annotation')
                            new_env[stmt[1]] = val
                        next_active.append((h, new_env))
                active = next_active
            return completed + [(g, Value('unit')) for g, _ in active]
        if k == 'var':
            if e[1] not in env: raise Unsupported('unbound name: ' + e[1])
            return [(guard, env[e[1]])]
        if k == 'num':
            val = Value('literal', e[1]); val = typed(val, e[2]) if e[2] else val
            return [(guard, val)]
        if k == 'bool': return [(guard, Value('bool', z3.BoolVal(e[1])))]
        if k in ('none', 'unit'): return [(guard, Value(k))]
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
                    elif op in ('+', '-', 'wrapping_add', 'wrapping_sub'):
                        out.append((h, Value(a1.ty, ((x+y) if op in ('+', 'wrapping_add') else (x-y)) % modulus)))
                    elif op == 'saturating_add': out.append((h, Value(a1.ty, z3.If(x+y < modulus, x+y, modulus-1))))
                    else:
                        comparison = {'<': lambda: x<y, '>': lambda: x>y, '<=': lambda: x<=y, '>=': lambda: x>=y,
                                      '==': lambda: x==y, '!=': lambda: x!=y}
                        if op not in comparison: raise Unsupported('unsupported operator')
                        out.append((h, Value('bool', comparison[op]())))
            return out
        raise Unsupported('unsupported AST node ' + k)


def check(source):
    names, body = Parser(source).program()
    variables = {k: z3.Int(k) for k in ('balance', 'amount', 'fee')}
    env = {n: Value('u64', v) for n, v in zip(names, variables.values())}
    paths = Interpreter().evaluate(body, env, z3.BoolVal(True))
    expected = variables['amount'] + variables['fee']
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
    result.update(backend='bounded Rust subset / Z3 4.13.3; exact full u64 input domain', paths=len(paths),
                  property='Some iff mathematical amount+fee<=balance; Some.total_debit=amount+fee')
    return result
