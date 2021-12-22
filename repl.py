import lark
import readline
import traceback
import z3
from z3lang.errors import *
from z3lang.expr import Expr
from z3lang.grammar import grammar

class Bool:
    def __init__(self):
        self.sort = z3.BoolSort()

    def var(self, x):
        return z3.Bool(x)

    def restrictions(self, z):
        return []

    def subst(self, substitutions):
        return self

    def __repr__(self):
        return 'bool'

class Int:
    def __init__(self):
        self.sort = z3.IntSort()

    def var(self, x):
        return z3.Int(x)

    def restrictions(self, z):
        return []

    def subst(self, substitutions):
        return self

    def __repr__(self):
        return 'int'

class Range:
    def __init__(self, upper):
        self.sort = z3.IntSort()
        self.upper = upper

    def var(self, x):
        return z3.Int(x)

    def restrictions(self, z):
        return [z >= 0, z < self.upper]

    def subst(self, substitutions):
        if len(substitutions) == 0:
            return self
        else:
            return Range(z3.substitute(self.upper, *substitutions))

    def __repr__(self):
        return f'range {self.upper}'

# Not a type in the usual sense, so no restrictions specified and `func` instead of `var`.
class Func:
    def __init__(self, args, ret):
        self.args = args
        self.ret = ret

    def func(self, f):
        return z3.Function(f, *([t.sort for x,t in self.args] + [self.ret.sort]))

    def __repr__(self):
        return f'{self.args} -> {self.ret}'

class StackFrame:
    def __init__(self, env, name, functype):
        self.env = env
        self.name = name
        self.functype = functype
        self.equations = []
        self.substitutions = []

class Session:
    def __init__(self):
        self.env = {}
        self.solver = z3.Solver()
        self.stack = []
        self.B = Bool()
        self.Z = Int()
        self.builtins = {
            'lt': (Func([('a', self.Z), ('b', self.Z)], self.B), lambda a,b:a<b),
            'le': (Func([('a', self.Z), ('b', self.Z)], self.B), lambda a,b:a<=b),
            'gt': (Func([('a', self.Z), ('b', self.Z)], self.B), lambda a,b:a>b),
            'ge': (Func([('a', self.Z), ('b', self.Z)], self.B), lambda a,b:a>=b),
            'add': (Func([('a', self.Z), ('b', self.Z)], self.Z), lambda a,b:a+b),
            'sub': (Func([('a', self.Z), ('b', self.Z)], self.Z), lambda a,b:a-b),
            'mul': (Func([('a', self.Z), ('b', self.Z)], self.Z), lambda a,b:a*b),
            'neg': (Func([('a', self.Z)], self.Z), lambda a:-a),
        }

    def typecheck(self, e):
        if isinstance(e, lark.Token):
            if e.type == 'CNAME':
                if e.value in self.env:
                    t = self.env[e.value]
                    return t, t.var(e.value)
                else:
                    raise VarNotDefined(e.value)
            elif e.type == 'INT':
                return self.Z, z3.IntVal(int(e.value))
            elif e.type == 'TRUE':
                return self.B, z3.BoolVal(True)
            elif e.type == 'FALSE':
                return self.B, z3.BoolVal(False)
            else:
                raise Unimplemented(f'token {e.type}')
        else:
            if e.data in ['eq','ne']:
                e0, e1 = e.children
                t0,z0 = self.typecheck(e0)
                t1,z1 = self.typecheck(e1)
                if t0.sort != t1.sort:
                    raise TypeException(f'{e.data} operator type mismatch: {t0} vs {t1}')
                if e.data == 'eq':
                    return self.B, z0 == z1
                elif e.data == 'ne':
                    return self.B, z0 != z1
            elif e.data in self.builtins:
                xs = e.children
                ft,pyfunc = self.builtins[e.data]
                zs = self.func_zs(ft, xs)
                return ft.ret, pyfunc(*zs)
            elif e.data == 'call':
                f = e.children[0]
                xs = e.children[1:]
                if f not in self.env:
                    raise FuncNotDefined(f)
                ft = self.env[f]
                zs = self.func_zs(ft, xs)
                return ft.ret, ft.func(f)(*zs)
            else:
                raise Unimplemented(f'tree {e.data}')

    def func_zs(self, ft, xs):
        if not isinstance(ft, Func):
            raise NotAFunction(f)
        if len(ft.args) != len(xs):
            raise ArgCountMismatch(f'Expected {len(ft.args)} arguments, got {len(xs)}')
        zs = []
        substitutions = []
        for e,(x,t) in zip(xs, ft.args):
            z = self.instance(e, t.subst(substitutions))
            zs.append(z)
            substitutions.append((t.var(x),z))
        return zs

    def instance(self, e, t):
        t1, z = self.typecheck(e)
        if t1.sort != t.sort:
            raise TypeException(f'Expected {t}, got {t1}')
        restrictions = t.restrictions(z)
        if len(restrictions) > 0:
            self.solver.push()
            try:
                self.solver.add(z3.Not(z3.And(*[r for r in restrictions])))
                if self.solver.check() == z3.sat:
                    print(self.solver.model())
                    raise PreconditionException()
            finally:
                self.solver.pop()
        return z

    def assign(self, x, e):
        if x in self.env:
            raise VarAlreadyDefined(x)
        t,z = self.typecheck(e)
        self.env[x] = t
        self.solver.add(t.var(x) == z)

        func_name = '.'.join([s.name for s in self.stack] + [x])
        xcall = self.add_equation(func_name, z)
        self.add_substitution(t, x, xcall)

    def ret(self, e):
        if len(self.stack) == 0:
            raise NotInFunction()

        z = self.instance(e, self.stack[-1].functype.ret)
        func_name = '.'.join((s.name for s in self.stack))
        self.add_equation(func_name, z)

    def add_equation(self, func_name, zorig):
        z = self.perform_substitution(zorig)
        var_list = []
        for s in self.stack:
            for x,t in s.functype.args:
                var_list.append(t.var(x))
        func = self.stack[-1].functype.func(func_name)
        func_with_vars = func(*var_list)
        if len(var_list) > 0:
            eq = z3.ForAll(var_list, func_with_vars == z)
        else:
            eq = func_with_vars == z
        self.stack[-1].equations.append(eq)
        return func_with_vars

    def add_substitution(self, t, x, z):
        if len(self.stack) == 0:
            raise NotInFunction()
        self.stack[-1].substitutions.append((t.var(x), z))

    def perform_substitution(self, z):
        if len(self.stack) == 0:
            raise NotInFunction()
        return z3.substitute(z, self.stack[-1].substitutions)

    def lookup_type(self, tname):
        if isinstance(tname, lark.Token):
            if tname.type == 'Z':
                return self.Z
            elif tname.type == 'B':
                return self.B
            else:
                raise Unimplemented(f'type token {tname}')
        elif isinstance(tname, lark.Tree):
            if tname.data == 'range':
                e, = tname.children
                t,z = self.typecheck(e)
                if t.sort != self.Z.sort:
                    raise TypeException(f'Range type mismatch: {t}')
                return Range(z)
            else:
                raise Unimplemented(f'type tree {tname}')

    def assign_arg(self, x, t):
        if x in self.env:
            raise VarAlreadyDefined(x)
        self.env[x] = t
        for item in t.restrictions(t.var(x)):
            self.solver.add(item)

    def assertion(self, e):
        t,z = self.typecheck(e)
        if t.sort != self.B.sort:
            raise TypeException(f'Assertion type mismatch: expected bool, got {t}')
        self.solver.push()
        try:
            self.solver.add(z3.Not(z))
            if self.solver.check() == z3.unsat:
                neg_model = None
            else:
                neg_model = self.solver.model()
        finally:
            self.solver.pop()
        self.solver.push()
        try:
            self.solver.add(z)
            if self.solver.check() == z3.unsat:
                pos_model = None
            else:
                pos_model = self.solver.model()
        finally:
            self.solver.pop()

        if neg_model != None and pos_model != None:
            print('not necessarily')
            print(neg_model)
            raise AssertionException()
        elif neg_model != None and pos_model == None:
            print('no')
            raise AssertionException()
        elif neg_model == None and pos_model != None:
            print('ok')
        else:
            print('unreachable')

    def pushfn(self, f, args, ret):
        if f in self.env:
            raise VarAlreadyDefined(f)

        self.solver.push()
        try:
            r = self.lookup_type(ret)
            self.stack.append(StackFrame(dict(self.env), f, Func([], r)))
            for arg in args:
                xtoken, tname = arg.children
                x = xtoken.value
                t = self.lookup_type(tname)
                self.stack[-1].functype.args.append((x,t))
                self.assign_arg(x, t)

        except Exception as e:
            self.solver.pop()
            raise e

    def get_possible_values(self, t, z, maximum):
        self.solver.push()
        try:
            var = t.var('.result')
            self.solver.add(var == z)
            result = []
            for i in range(maximum):
                if self.solver.check() == z3.sat:
                    m = self.solver.model()
                    value = m[var]
                    if value != None:
                        result.append(value)
                        self.solver.add(var != value)
                    else:
                        return result, True    # satisfiable but no value reported for var
                else:
                    return result, False
            return result, False
        finally:
            self.solver.pop()

    def sample(self, e):
        t,z = self.typecheck(e)
        print(f'Type: {t}')
        maximum = 21
        values, mystery = self.get_possible_values(t, z, maximum)
        string = '{'
        string += ', '.join(str(v) for v in values[:maximum-1])
        if mystery:
            string += '???'
        elif len(values) == maximum:
            string += '...'
        string += '}'
        print(string)

    def pop(self):
        if len(self.stack) == 0:
            raise StackEmpty()
        sf = self.stack.pop()
        self.env = sf.env
        self.solver.pop()
        if sf.name in self.env:
            raise VarAlreadyDefined(f'Function name {sf.name} already defined')
        self.env[sf.name] = sf.functype
        if len(sf.equations) > 0:
            if len(self.stack) != 0:
                raise Unimplemented('Can currently only return from outermost function')
            for eq in sf.equations:
                print(f'Adding equation: {eq}')
                self.solver.add(eq)

    def print_env(self):
        for x in sorted(self.env.keys()):
            print(f'{x:10} {self.env[x]}')

    def process_statement(self, ast):
        if ast.data == 'assignment':
            x, e = ast.children
            self.assign(x, e)
        elif ast.data == 'assertion':
            e, = ast.children
            self.assertion(e)
        elif ast.data == 'pushfn':
            f = ast.children[0].value
            args = ast.children[1:-1]
            ret = ast.children[-1]
            self.pushfn(f, args, ret)
        elif ast.data == 'pop':
            self.pop()
        elif ast.data == 'return':
            e, = ast.children
            self.ret(e)
        elif ast.data == 'sample':
            e, = ast.children
            self.sample(e)
        elif ast.data == 'env':
            self.print_env()
        else:
            raise Unimplemented(f'statement {ast.data}')

    def parse_and_process(self, text):
        global grammar
        try:
            ast = grammar.parse(text)
            self.process_statement(ast)
        except lark.exceptions.UnexpectedInput as ex:
            raise Mistake(ex)

    def prompt(self):
        stack = ''.join((f'{s.name} ' for s in self.stack))
        return f'{stack}>> '

def main():
    global grammar
    session = Session()
    while True:
        text = input(session.prompt())
        try:
            session.parse_and_process(text)
        except Mistake as ex:
            traceback.print_exc()

if __name__ == '__main__':
    main()
