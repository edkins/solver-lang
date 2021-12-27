import io
import lark
import z3
from z3lang.errors import *
from z3lang.expr import Expr
from z3lang.grammar import grammar
from z3lang.misc import or_zs
from z3lang.types import *

class StackFrame:
    def __init__(self, env, name, functype):
        self.env = env
        self.name = name
        self.functype = functype
        self.equations = []
        self.substitutions = []

def int_arg(name):
    return Arg(name, Z)

def bool_arg(name):
    return Arg(name, B)

class Session:
    def __init__(self, output):
        self.output = output
        self.env = {}
        self.solver = z3.Solver()
        self.stack = []
        self.builtins = {
            'lt': (Func([int_arg('a'), int_arg('b')], B), lambda a,b:a<b),
            'le': (Func([int_arg('a'), int_arg('b')], B), lambda a,b:a<=b),
            'gt': (Func([int_arg('a'), int_arg('b')], B), lambda a,b:a>b),
            'ge': (Func([int_arg('a'), int_arg('b')], B), lambda a,b:a>=b),
            'add': (Func([int_arg('a'), int_arg('b')], Z), lambda a,b:a+b),
            'sub': (Func([int_arg('a'), int_arg('b')], Z), lambda a,b:a-b),
            'mul': (Func([int_arg('a'), int_arg('b')], Z), lambda a,b:a*b),
            'neg': (Func([int_arg('a')], Z), lambda a:-a),
        }
        self.solver.add(length_func(CommonSort.list(CommonListSort.empty)) == 0)
        x = z3.Const('.x', CommonSort)
        xs = z3.Const('.xs', CommonListSort)
        self.solver.add(z3.ForAll([x,xs], length_func(CommonSort.list(CommonListSort.cons(x,xs))) == length_func(CommonSort.list(xs)) + 1))

    def typecheck_coerce(self, e, typ, substitutions, excep):
        ex0 = self.typecheck(e)

        ex, restrictions = ex0.coerce_restrictions(typ)

        for restriction in restrictions:
            self.solver.push()
            try:
                self.solver.add(z3.Not(z3.substitute(restriction, substitutions)))
                if self.solver.check() == z3.sat:
                    print(self.solver.model())
                    raise excep()
            finally:
                self.solver.pop()
        return ex

    def typecheck(self, e):
        if isinstance(e, lark.Token):
            if e.type == 'CNAME':
                if e.value in self.env:
                    result = self.env[e.value]
                    if isinstance(result, Func):
                        raise IsAFunction(e.value)
                    return result
                else:
                    raise VarNotDefined(e.value)
            elif e.type == 'INT':
                return Expr(Z, z3.IntVal(int(e.value)))
            elif e.type == 'TRUE':
                return Expr(B, z3.BoolVal(True))
            elif e.type == 'FALSE':
                return Expr(B, z3.BoolVal(False))
            else:
                raise Unimplemented(f'token {e.type}')
        else:
            if e.data in ['eq','ne']:
                e0, e1 = e.children
                ex0 = self.typecheck(e0)
                ex1 = self.typecheck(e1)
                if e.data == 'eq':
                    return ex0.eq(ex1, negate=False)
                elif e.data == 'ne':
                    return ex0.eq(ex1, negate=True)
            elif e.data in self.builtins:
                xs = e.children
                ft,pyfunc = self.builtins[e.data]
                zs = self.func_zs(ft, xs)
                return Expr(ft.ret, pyfunc(*zs))
            elif e.data == 'call':
                f = e.children[0]
                xs = e.children[1:]
                if f not in self.env:
                    raise FuncNotDefined(f)
                ft = self.env[f]
                zs = self.func_zs(ft, xs)
                return Expr(ft.ret, ft.func(f)(*zs))
            elif e.data == 'listing':
                exs = [self.typecheck(e0) for e0 in e.children]
                ts = [ex.typ for ex in exs]
                t = TupleType(ts)
                z = listing_zs([ex.to_common_z() for ex in exs])
                return Expr(t, z)
            else:
                raise Unimplemented(f'tree {e.data}')

    def func_zs(self, ft, xs):
        if not isinstance(ft, Func):
            raise NotAFunction(f)
        if len(ft.args) != len(xs):
            raise ArgCountMismatch(f'Expected {len(ft.args)} arguments, got {len(xs)}')
        zs = []
        substitutions = []
        for e,arg in zip(xs, ft.args):
            v = arg.var()
            ex = self.typecheck_coerce(e, arg.typ, substitutions=substitutions, excep=PreconditionException)
            zs.append(ex.z)
            substitutions.append((v,ex.z))
        for pre in ft.extra_preconditions():
            self.check_precondition(pre, substitutions)
        return zs

    def check_precondition(self, pre, substitutions):
        self.solver.push()
        try:
            self.solver.add(z3.Not(z3.substitute(pre, substitutions)))
            if self.solver.check() == z3.sat:
                print(self.solver.model())
                raise PreconditionException()
        finally:
            self.solver.pop()

    def check_postcondition(self, post):
        self.solver.push()
        try:
            self.solver.add(z3.Not(post))
            if self.solver.check() == z3.sat:
                print(self.solver.model())
                raise PostconditionException()
        finally:
            self.solver.pop()

    def assign(self, x, e):
        if x in self.env:
            raise VarAlreadyDefined(x)
        ex = self.typecheck(e)
        v = ex.typ.var(x)
        self.env[x] = Expr(ex.typ, v)
        self.solver.add(v == ex.z)
        func_name = '.'.join([s.name for s in self.stack] + [x])
        if len(self.stack) > 0:
            xcall = self.add_equation(func_name, ex.z)
            self.stack[-1].substitutions.append((v, xcall))

    def ret(self, e):
        if len(self.stack) == 0:
            raise NotInFunction()

        ex = self.typecheck_coerce(e, self.stack[-1].functype.ret, substitutions=[], excep=PostconditionException)

        func_name = '.'.join([s.name for s in self.stack])
        self.add_equation(func_name, ex.z)

    def add_equation(self, func_name, zorig):
        if len(self.stack) == 0:
            raise NotInFunction()

        z = self.perform_substitution(zorig)
        var_list = []
        for s in self.stack:
            for arg in s.functype.args:
                var_list.append(arg.var())
        func = self.stack[-1].functype.func(func_name)
        func_with_vars = func(*var_list)
        if len(var_list) > 0:
            eq = z3.ForAll(var_list, func_with_vars == z)
        else:
            eq = func_with_vars == z
        self.stack[-1].equations.append(eq)
        return func_with_vars

    def perform_substitution(self, z):
        if len(self.stack) == 0:
            raise NotInFunction()
        return z3.substitute(z, self.stack[-1].substitutions)

    def lookup_type(self, tname):
        if isinstance(tname, lark.Token):
            if tname.type == 'Z':
                return Z
            elif tname.type == 'B':
                return B
            else:
                raise Unimplemented(f'type token {tname}')
        elif isinstance(tname, lark.Tree):
            if tname.data == 'range':
                e, = tname.children
                ex = self.typecheck_coerce(e, Z, substitutions=[], excep=UnexpectedException)
                return range_type(ex.z)
            elif tname.data == 'tuple':
                ts = [self.lookup_type(e) for e in tname.children]
                return TupleType(ts)
            elif tname.data == 'array':
                t = self.lookup_type(tname.children[0])
                return ArrayType(t)
            else:
                raise Unimplemented(f'type tree {tname}')

    def assign_arg(self, arg):
        if arg.name in self.env:
            raise VarAlreadyDefined(x)
        self.env[arg.name] = arg.expr()
        for item in arg.restrictions():
            self.solver.add(item)

    def assertion(self, e):
        ex = self.typecheck_coerce(e, B, substitutions=[], excep=UnexpectedException)
        self.solver.push()
        try:
            self.solver.add(z3.Not(ex.z))
            if self.solver.check() == z3.unsat:
                neg_model = None
            else:
                neg_model = self.solver.model()
        finally:
            self.solver.pop()
        self.solver.push()
        try:
            self.solver.add(ex.z)
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

    def unreachable(self):
        if self.solver.check() == z3.sat:
            raise ReachabilityException()
        else:
            print('ok')

    def pushfn(self, f, args, ret):
        if f in self.env:
            raise VarAlreadyDefined(f)

        self.solver.push()
        try:
            r = self.lookup_type(ret)
            self.stack.append(StackFrame(dict(self.env), f, Func([], r)))
            for arg in args:
                xtoken, tname = arg.children
                arg = Arg(xtoken.value, self.lookup_type(tname))
                self.stack[-1].functype.args.append(arg)
                self.assign_arg(arg)

        except Exception as e:
            self.solver.pop()
            raise e

    def get_possible_values(self, expr, maximum):
        self.solver.push()
        try:
            var = expr.typ.var('.result')
            self.solver.add(var == expr.z)
            result = []
            for i in range(maximum):
                if self.solver.check() == z3.sat:
                    m = self.solver.model()
                    value = m[var]
                    if value == None:
                        return result, True    # satisfiable but no value reported for var
                    result.append(value)
                    self.solver.add(var != value)
                else:
                    return result, False
            return result, False
        finally:
            self.solver.pop()

    def sample(self, e):
        ex = self.typecheck(e)
        self.output.write(f'Type: {ex.typ}\n')
        maximum = 21
        values, mystery = self.get_possible_values(ex, maximum)
        string = '{'
        string += ', '.join(str(v) for v in values[:maximum-1])
        if mystery:
            string += '???'
        elif len(values) == maximum:
            string += '...'
        string += '}'
        self.output.write(string)
        self.output.write('\n')

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
            self.assign(x.value, e)
        elif ast.data == 'assertion':
            e, = ast.children
            self.assertion(e)
        elif ast.data == 'unreachable':
            self.unreachable()
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

def run_script(script):
    with io.StringIO() as output:
        session = Session(output)
        for text in script.split('\n'):
            stripped = text.strip()
            if stripped != '':
                session.parse_and_process(stripped)
        return output.getvalue()
