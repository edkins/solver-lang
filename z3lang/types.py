import z3

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
