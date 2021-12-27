import z3

def create_common_sorts():
    common = z3.Datatype('Common')
    common_list = z3.Datatype('CommonList')
    common.declare('bool', ('boolval', z3.BoolSort()))
    common.declare('int', ('intval', z3.IntSort()))
    common.declare('list', ('listval', common_list))
    common_list.declare('empty')
    common_list.declare('cons', ('head', common), ('tail', common_list))
    common, common_list = z3.CreateDatatypes(common, common_list)

    length = z3.Function('length', common, z3.IntSort())
    subscript = z3.Function('subscript', common, z3.IntSort(), common)

    return common, common_list, length, subscript

CommonSort, CommonListSort, length_func, subscript_func = create_common_sorts()

def common_fixed_subscript(z, i):
    zl = CommonSort.listval(z)
    for _ in range(i):
        zl = CommonListSort.tail(zl)
    return CommonListSort.head(zl)

def common_is_list_of_fixed_length(z, n):
    def commonlist_is_length(zl, length):
        if length == 0:
            return CommonListSort.is_empty(zl)
        else:
            return z3.And(CommonListSort.is_cons(zl), commonlist_is_length(CommonListSort.tail(zl), length-1))

    return z3.And(CommonSort.is_list(z), commonlist_is_length(CommonSort.listval(z), n))

def listing_zs(zs):
    def make_commonlist(zs0):
        if len(zs0) == 0:
            return CommonListSort.empty
        else:
            return CommonListSort.cons(zs0[0], make_commonlist(zs0[1:]))

    return CommonSort.list(make_commonlist(zs))

class BaseType:
    def var(self, x):
        return z3.Const(x, self.sort())

    def restrictions(self, name):
        return self.z_restrictions(self.var(name))

class BoolType(BaseType):
    def __repr__(self):
        return 'bool'

    def sort(self):
        return z3.BoolSort()

    def z_restrictions(self, z):
        return []

    def next_restriction_var(self):
        return 0

    def to_common(self, z):
        return CommonSort.bool(z)

    def from_common(self, z):
        return CommonSort.boolval(z), [CommonSort.is_bool(z)]

class IntType(BaseType):
    def __repr__(self):
        return 'int'

    def sort(self):
        return z3.IntSort()

    def z_restrictions(self, z):
        return []

    def next_restriction_var(self):
        return 0

    def might_be(self, kind):
        return kind == 'int'

    def to_common(self, z):
        return CommonSort.int(z)

    def from_common(self, z):
        return CommonSort.intval(z), [CommonSort.is_int(z)]

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
        substitutions = [(self.var('.it'), z)]
        for r in self.it_restrictions:
            restrictions.append(z3.substitute(r, substitutions))
        return restrictions

    def next_restriction_var(self):
        return self.next_var

    def to_common(self, z):
        return self.underlying.to_common(z)

    def from_common(self, z):
        result, restrictions = self.underlying.from_common(z)
        substitutions = [(self.var('.it'), result)]
        restrictions = list(restrictions)
        for r in self.it_restrictions:
            restrictions.append(z3.substitute(r, substitutions))
        return result, restrictions

class TupleType(BaseType):
    def __init__(self, members):
        self.members = members

    def __repr__(self):
        return 'tuple[' + ','.join((str(m) for m in self.members)) + ']'

    def sort(self):
        return CommonSort

    def z_restrictions(self, z):
        restrictions = [common_is_list_of_fixed_length(z, len(self.members))]
        for i in range(len(self.members)):
            restrictions += self.members[i].from_common(common_fixed_subscript(z,i))[1]
        return restrictions

    def next_restriction_var(self):
        return max((m.next_restriction_var() for m in self.members))

    def to_common(self, z):
        return z

    def from_common(self, z):
        return z, self.z_restrictions(z)

class ArrayType(BaseType):
    def __init__(self, element):
        self.element = element

    def __repr__(self):
        return f'array {self.element}'

    def sort(self):
        return CommonSort

    def z_restrictions(self, z):
        x = z3.Int(f'.x{self.element.next_restriction_var()}')
        restrictions = [CommonSort.is_list(z)]
        for r in self.element.from_common(subscript_func(z,x))[1]:
            restrictions.append(z3.ForAll([x], z3.Implies(z3.And(x >= 0, x < length_func(z)), r)))
        return restrictions

    def next_restriction_var(self):
        return self.element.next_restriction_var() + 1

    def to_common(self, z):
        return z

    def from_common(self, z):
        return z, self.z_restrictions(z)

B = BoolType()
Z = IntType()

def range_type(upper):
    return RestrictedType(Z, [z3.Int('.it') >= 0, z3.Int('.it') < upper], 0)

class Arg:
    def __init__(self, name, typ):
        self.name = name
        self.typ = typ

    def var(self):
        return self.typ.var(self.name)

    def expr(self):
        from z3lang.expr import Expr
        return Expr(self.typ, self.var())

    def restrictions(self):
        return self.typ.restrictions(self.name)

    def __repr__(self):
        return f'{self.name}:{self.typ}'

class Func:
    def __init__(self, args, ret):
        self.args = args
        self.ret = ret

    def func(self, f):
        sorts = []
        for arg in self.args:
            sorts.append(arg.typ.sort())
        sorts.append(self.ret.sort())
        return z3.Function(f, *sorts)

    def extra_preconditions(self):
        return []

    def ectra_postconditions(self, retval):
        return []

    def __repr__(self):
        return f'{self.args} -> {self.ret}'
