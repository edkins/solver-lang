import z3

class BaseType:
    def var(self, x):
        return z3.Const(x, self.sort())

    def restrictions(self, name):
        return self.z_restrictions(self.var(name))

class BoolType(BaseType):
    def __repr__(self):
        return 'B'

    def sort(self):
        return z3.BoolSort()

    def z_restrictions(self, z):
        return []

    def next_restriction_var(self):
        return 0

    def might_be(self, kind):
        return kind == 'bool'

class IntType(BaseType):
    def __repr__(self):
        return 'Z'

    def sort(self):
        return z3.IntSort()

    def z_restrictions(self, z):
        return []

    def next_restriction_var(self):
        return 0

    def might_be(self, kind):
        return kind == 'int'

class RestrictedType(BaseType):
    def __init__(self, underlying, it_restrictions, next_var):
        self.underlying = underlying
        self.it_restrictions = it_restrictions
        self.next_var = next_var

    def __repr__(self):
        return f'{self.underlying} {self.it_restrictions}'

    def sort(self):
        return self.underlying.sort()

    def z_restrictions(self, z):
        restrictions = list(self.underlying.z_restrictions(z))
        substitutions = [self.var('.it'), z]
        for r in self.it_restrictions:
            restrictions.append(z3.substitute(r, substitute))
        return restrictions

    def next_restriction_var(self):
        return self.next_var

    def might_be(self, kind):
        return self.underlying.might_be(kind)

class TupleType(BaseType):
    def __init__(self, members):
        self.members = members

    def __repr__(self):
        return 'tuple[' + ','.join((str(m) for m in self.members)) + ']'

    def sort(self):
        return z3.TupleSort(str(self), [m.sort() for m in self.members])

    def z_restrictions(self, z):
        restrictions = []
        sort = self.sort()
        for i in range(len(self.members)):
            restrictions += self.members[i].z_restrictions(sort.accessor(0,i)(z))
        return restrictions

    def next_restriction_var(self):
        return max((m.next_restriction_var() for m in self.members))

    def might_be(self, kind):
        return kind == 'listing'

class ArrayType(BaseType):
    def __init__(self, element):
        self.element = element

    def __repr__(self):
        return f'array {self.element}'

    def sort(self):
        return z3.SeqSort(self.element.sort())

    def z_restrictions(self, z):
        x = z3.Var(self.element.next_restriction_var(), IntSort())
        restrictions = []
        for r in self.element.z_restrictions(z[x]):
            restrictions.add(z3.ForAll([x], z3.Implies(z3.And(x >= 0, x < z3.Length(z)), r)))
        return restrictions

    def next_restriction_var(self):
        return self.element.next_restriction_var() + 1

    def might_be(self, kind):
        return kind == 'listing'

B = BoolType()
Z = IntType()

def range_type(upper):
    return RestrictedType(Z, [z3.Int('.it') >= 0, z3.Int('.it') < upper])

class Arg:
    def __init__(self, name, typ):
        self.name = name
        self.typ = typ

    def var(self):
        return self.typ.var(self.name)

    def expr(self):
        from z3lang.expr import Expr
        return Expr(self.typ, *self.vars())

    def restrictions(self):
        return self.typ.restrictions(self.name)

    def __repr__(self):
        return f'{self.name}:{self.typ}'

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
        for name,sort in zip(self.ret.varnames(f), self.ret.sorts):
            result.append(self.func(name, sort))
        return result

    def preconditions(self):
        result = []
        for arg in self.args:
            for restriction in arg.restrictions():
                result.append(restriction)
        return result

    def postconditions(self, retval):
        return self.ret.zs_restrictions(retval.zs)

    def __repr__(self):
        return f'{self.args} -> {self.ret}'
