import z3
from z3lang.misc import and_zs, sequence_zs
from z3lang.errors import TypeException, UnexpectedException

class BaseType:
    def var(self, x):
        return z3.Const(x, self.sort())

    def restrictions(self, name):
        return self.coerce_restrictions(self.var(name))[1]

    def coerce_restrictions(self, z):
        if not self._accepts_sort(z.sort()):
            raise TypeException()
        result, restrictions = self._coerce_restrictions(z)
        if self.sort() == z.sort():
            result = z
        return result, restrictions

class ImpossibleType(BaseType):
    def __repr__(self):
        return '!'

    def sort(self):
        return z3.BoolSort()

    def sort_default(self):
        return z3.BoolVal(False)

    def _coerce_restrictions(self, z):
        raise UnexpectedException('Unreachable for ImpossibleType')

    def _accepts_sort(self, sort):
        return False

class BoolType(BaseType):
    def __repr__(self):
        return 'bool'

    def sort(self):
        return z3.BoolSort()

    def sort_default(self):
        return z3.BoolVal(False)

    def _coerce_restrictions(self, z):
        return z, []

    def _accepts_sort(self, sort):
        return sort == z3.BoolSort()

class IntType(BaseType):
    def __repr__(self):
        return 'int'

    def sort(self):
        return z3.IntSort()

    def sort_default(self):
        return z3.IntVal(0)

    def _coerce_restrictions(self, z):
        return z, []

    def _accepts_sort(self, sort):
        return sort == z3.IntSort()

class RestrictedType(BaseType):
    def __init__(self, underlying, it_restrictions):
        self.underlying = underlying
        self.it_restrictions = it_restrictions

    def __repr__(self):
        return f'{self.underlying} {self.it_restrictions}'

    def sort(self):
        return self.underlying.sort()

    def sort_default(self):
        return self.underlying.sort_default()

    def coerce_restrictions(self, z):
        if not self._accepts_sort(z.sort()):
            return self.sort_default(), z3.BoolVal(False)
        result, restrictions = self.underlying.coerce_restrictions(z)
        restrictions = list(restrictions)
        substitutions = [(self.var('.it'), z)]
        for r in self.it_restrictions:
            restrictions.append(z3.substitute(r, substitutions))
        return result, restrictions

    def _accepts_sort(self, sort):
        return self.underlying._accepts_sort(sort)

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

    def sort_default(self):
        return self.listing([m.sort_default() for m in self.members])

    def coerce_restrictions(self, z):
        restrictions = []
        n = len(self.members)
        if get_tuple_sort_arity(z.sort()) == n:
            xs = []
            for i in range(n):
                x, rs = self.members[i].coerce_restrictions(z.sort().accessor(0,i)(z))
                restrictions += rs
                xs.append(x)
            return self.listing(xs), restrictions
        elif isinstance(z.sort(), z3.SeqSortRef):
            restrictions.append(z3.Length(z) == n)
            xs = []
            for i in range(n):
                x, rs = self.members[i].coerce_restrictions(z[i])
                restrictions += rs
                xs.append(x)
            return self.listing(xs), restrictions
        else:
            raise UnexpectedException('Unexpected sort encountered')

    def listing(self, zs):
        if len(zs) != len(self.members):
            raise UnexpectedException(f'Expecting {len(self.members)} zs, got {len(zs)}')
        return self.sort().constructor(0)(*zs)

    def _accepts_sort(self, sort):
        n = len(self.members)
        if get_tuple_sort_arity(sort) == n:
            for i in range(n):
                if not self.members[i]._accepts_sort(sort.constructor(0).domain(i)):
                    return False
            return True
        elif isinstance(sort, z3.SeqSortRef):
            for i in range(n):
                if not self.members[i]._accepts_sort(sort.basis()):
                    return False
            return True
        else:
            return False

class ArrayType(BaseType):
    def __init__(self, element):
        self.element = element

    def __repr__(self):
        return f'array {self.element}'

    def sort(self):
        return z3.SeqSort(self.element.sort())

    def sort_default(self):
        return z3.Empty(self.sort())

    def _coerce_restrictions(self, z):
        arity = get_tuple_sort_arity(z.sort())
        if isinstance(z.sort(), z3.SeqSortRef):
            x = z3.Int('.x')
            restrictions = []
            y,rs = self.element.coerce_restrictions(z[x])
            for r in rs:
                restrictions.append(z3.ForAll([x], z3.Implies(z3.And(x >= 0, x < z3.Length(z)), r)))
            if self.element.sort() == z[x].sort():
                return z, restrictions
            else:
                return z3.Map(z3.Lambda([x], y), z), restrictions
        elif arity != None:
            restrictions = []
            ys = []
            for i in range(arity):
                y,rs = self.element.coerce_restrictions(z.sort().accessor(0,i)(z))
                restrictions += rs
                ys.append(y)
            return sequence_zs(self.element.sort(), ys), restrictions
        else:
            raise UnexpectedException(f'Unexpected sort encountered {z.sort()} for {self}')

    def _accepts_sort(self, sort):
        arity = get_tuple_sort_arity(sort)
        if isinstance(sort, z3.SeqSortRef):
            return self.element._accepts_sort(sort.basis())
        elif arity != None:
            for i in range(arity):
                if not self.element._accepts_sort(sort.constructor(0).domain(i)):
                    return False
            return True
        else:
            return False

B = BoolType()
Z = IntType()

def restricted_type(underlying, it_restrictions):
    if isinstance(underlying, ImpossibleType):
        return ImpossibleType()
    if len(it_restrictions) == 0:
        return underlying
    if isinstance(underlying, RestrictedType):
        return RestrictedType(underlying.underlying, underlying.it_restrictions + it_restrictions)
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
        return restricted_type(t, t0.coerce_restrictions(t0.var('.it'))[1])

    if isinstance(t1, RestrictedType):
        t = intersect(t0, t1.underlying)
        return restricted_type(t, t1.coerce_restrictions(t1.var('.it'))[1])

    if isinstance(t0, TupleType) and isinstance(t1, TupleType) and len(t0.members) == len(t1.members):
        return tuple_type([intersect(m0,m1) for m0,m1 in zip(t0.members, t1.members)])

    if isinstance(t0, ArrayType) and isinstance(t1, ArrayType):
        return array_type(intersect(t0.element, t1.element))

    if isinstance(t0, TupleType) and isinstance(t1, ArrayType):
        return tuple_type([intersect(m,t1.element) for m in t0.members])

    if isinstance(t0, ArrayType) and isinstance(t1, TupleType):
        return tuple_type([intersect(t0.element,m) for m in t1.members])

    return ImpossibleType()

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
