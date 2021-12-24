import z3

class ExactType:
    def __init__(self, sorts, name):
        self.sorts = sorts
        self.name = name

    def __repr__(self):
        return self.name

    def varnames(self, x):
        n = len(self.sorts)
        if n == 0:
            return []
        elif n == 1:
            return [x]
        else:
            return [f'{x}.{i}' for i in range(n)]

    def vars(self, x):
        names = self.varnames(x)
        return [z3.Const(names[i], self.sorts[i]) for i in range(len(names))]

B = ExactType([z3.BoolSort()], 'bool')
Z = ExactType([z3.IntSort()], 'int')

class Arg:
    def __init__(self, name, typ, restrictions):
        self.name = name
        self.typ = typ
        self.restrictions = restrictions

    def vars(self):
        return self.typ.vars(self.name)

    def expr(self):
        from z3lang.expr import Expr
        return Expr(self.typ, *self.vars())

    def __repr__(self):
        return f'{self.name}:{self.typ} {self.restrictions}'

def bool_arg(name):
    return Arg(name, B, [])

def int_arg(name):
    return Arg(name, Z, [])

def range_arg(name, upper):
    return Arg(name, Z, [z3.Int(name) >= 0, z3.Int(name) < upper])


class Func:
    def __init__(self, args, ret):
        self.args = args
        self.ret = ret

    def func(self, f, retsort):
        sorts = []
        for arg in self.args:
            sorts += arg.typ.sorts
        sorts.append(retsort)
        return z3.Function(f, *sorts)

    def funcs(self, f):
        result = []
        for name,sort in zip(self.ret.typ.varnames(f), self.ret.typ.sorts):
            result.append(self.func(name, sort))
        return result

    def preconditions(self):
        result = []
        for arg in self.args:
            for restriction in arg.restrictions:
                result.append(restriction)
        return result

    def postconditions(self, retval):
        result = []
        vs = retval.typ.vars('.ret')
        substitutions = [(vs[i], retval.zs[i]) for i in range(len(vs))]
        for restriction in self.ret.restrictions:
            result.append(z3.substitute(restriction, substitutions))
        return result

    def __repr__(self):
        return f'{self.args} -> {self.ret}'
