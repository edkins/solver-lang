import z3
from z3lang.misc import and_zs, sequence_zs

class BaseType:
    def var(self, x):
        return z3.Const(x, self.sort())

    def restrictions(self, name):
        return self.z_restrictions(self.var(name))

class ImpossibleType(BaseType):
    def __repr__(self):
        return '!'

    def sort(self):
        return z3.BoolSort()

    def z_restrictions(self, z):
        return z3.BoolVal(False)

class BoolType(BaseType):
    def __repr__(self):
        return 'bool'

    def sort(self):
        return z3.BoolSort()

    def z_restrictions(self, z):
        if z.sort() != z3.BoolSort():
            raise UnexpectedException(f'Unexpected sort encountered')
        return []

class IntType(BaseType):
    def __repr__(self):
        return 'int'

    def sort(self):
        return z3.IntSort()

    def z_restrictions(self, z):
        if z.sort() != z3.IntSort():
            raise UnexpectedException(f'Unexpected sort encountered')
        return []

class RestrictedType(BaseType):
    def __init__(self, underlying, it_restrictions):
        self.underlying = underlying
        self.it_restrictions = it_restrictions

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

def get_tuple_sort_arity(sort):
    if isinstance(sort, z3.DatatypeSortRef) and sort.num_constructors() == 1:
        return sort.constructor(0).arity()
    else:
        return None

class TupleType(BaseType):
    def __init__(self, members):
        self.members = members

    def __repr__(self):
        return 'tuple[' + ','.join((str(m) for m in self.members)) + ']'

    def sort(self):
        return z3.TupleSort(str(self), [m.sort() for m in self.members])[0]

    def z_restrictions(self, z):
        restrictions = []
        n = len(self.members)
        if get_tuple_sort_arity(z.sort()) == n:
            for i in range(n):
                restrictions += self.members[i].z_restrictions(z.sort().accessor(0,i)(z))
            return restrictions
        elif isinstance(z.sort(), z3.SeqSortRef):
            restrictions.append(z3.Length(z) == n)
            for i in range(n):
                restrictions += self.members[i].z_restrictions(z[i])
            return restrictions
        else:
            raise UnexpectedException('Unexpected sort encountered')

    def listing(self, zs):
        if len(zs) != len(self.members):
            raise UnexpectedException(f'Expecting {len(self.members)} zs, got {len(zs)}')
        return self.sort().constructor(0)(*zs)

class ArrayType(BaseType):
    def __init__(self, element):
        self.element = element

    def __repr__(self):
        return f'array {self.element}'

    def sort(self):
        return z3.SeqSort(self.element.sort())

    def z_restrictions(self, z):
        arity = get_tuple_sort_arity(z.sort())
        if isinstance(z.sort(), z3.SeqSortRef):
            x = z3.Int('.x')
            for r in self.element.z_restrictions(z[x]):
                restrictions.append(z3.ForAll([x], z3.Implies(z3.And(x >= 0, x < z3.Length(z)), r)))
            return restrictions
        elif arity != None:
            for i in range(arity):
                restrictions.append(self.element.z_restrictions(z.sort().accessor(0,i)(z)))
            return restrictions
        else:
            raise UnexpectedException(f'Unexpected sort encountered')

B = BoolType()
Z = IntType()

def restricted_type(underlying, it_restrictions):
    if isinstance(underlying, ImpossibleType):
        return ImpossibleType()
    if len(it_restrictions) == 0:
        return underlying
    if isinstance(underlying, RestrictedType):
        return RestrictedType(underlying.it_restrictions + it_restrictions)
    return RestrictedType(underlying, it_restrictions)

def tuple_type(members):
    for m in members:
        if isinstance(m, ImpossibleType):
            return ImpossibleType()
    return TupleType(members)

def array_type(element):
    return ArrayType(element)

def range_type(upper):
    return RestrictedType(Z, [z3.Int('.it') >= 0, z3.Int('.it') < upper])

def intersect(t0, t1):
    if isinstance(t0, BoolType) and isinstance(t1, BoolType):
        return BoolType()

    if isinstance(t0, IntType) and isinstance(t1, IntType):
        return IntType()

    if isinstance(t0, RestrictedType):
        t = intersect(t0.underlying, t1)
        return restricted_type(t, t0.z_restrictions(t.var('.it')))

    if isinstance(t1, RestrictedType):
        t = intersect(t0, t1.underlying)
        return restricted_type(t, t1.z_restrictions(t.var('.it')))

    if isinstance(t0, TupleType) and isinstance(t1, TupleType) and len(t0.members) == len(t1.members):
        return tuple_type([intersect(m0,m1) for m0,m1 in zip(t0.members, t1.members)])

    if isinstance(t0, ArrayType) and isinstance(t1, ArrayType):
        return array_type(intersect(t0.element, t1.element))

    if isinstance(t0, TupleType) and isinstance(t1, ArrayType):
        return tuple_type([intersect(m,t1.element) for m in t0.members])

    if isinstance(t0, ArrayType) and isinstance(t1, TupleType):
        return tuple_type([intersect(t0.element,m) for m in t1.members])

    return ImpossibleType()

def equality(z0, z1):
    if z0.sort() == z1.sort():
        return z0 == z1

    if isinstance(z0.sort(), z3.SeqSortRef) and isinstance(z1.sort(), z3.SeqSortRef):
        x = z3.Int('.x')
        for r in self.element.z_restrictions(z[x]):
            restrictions.append(z3.ForAll([x], z3.Implies(z3.And(x >= 0, x < z3.Length(z)), r)))
        
        eq = equality(z0[x], z1[x])
        return z3.And(z3.Length(z0) == z3.Length(z1), z3.ForAll([x], z3.Implies(z3.And(x >= 0, x < z3.Length(z0)), eq)))

    arity0 = get_tuple_sort_arity(z0.sort())
    arity1 = get_tuple_sort_arity(z1.sort())
    if arity0 != None and arity1 != None and arity0 == arity1:
        return and_zs([equality(z0.sort().accessor(0,i)(z0), z1.sort().accessor(0,i)(z1)) for i in range(arity0)])

    if arity0 != None and isinstance(z1.sort(), z3.SeqSortRef):
        return sequence_zs(z1.sort().basis(), [z0.sort().accessor(0,i)(z0) for i in range(arity0)]) == z1

    if isinstance(z0.sort(), z3.SeqSortRef) and arity1 != None:
        return z0 == sequence_zs(z0.sort().basis(), [z1.sort().accessor(0,i)(z1) for i in range(arity1)])

    return z3.BoolVal(False)

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
