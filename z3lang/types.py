import z3
from z3lang.misc import and_zs, or_zs, sequence_zs
from z3lang.errors import *

class BaseType:
    def var(self, x):
        return z3.Const(x, self.sort())

    def restrictions(self, name):
        return self.coerce_restrictions(self.var(name))[1]

    def coerce_restrictions(self, z):
        if not self._accepts_sort(z.sort()):
            raise TypeException()

        count = get_union_sort_count(z.sort())
        if count != None:
            restriction_options = []
            result = None
            for i in range(count):
                z_opt = z.sort().accessor(i,0)(z)
                if self._accepts_sort(z_opt.sort()):
                    result_opt, rs = self._coerce_restrictions(z_opt)
                    precondition = z.sort().recognizer(i)(z)
                    restriction_options.append(and_zs([precondition] + rs))
                    if self.sort() == z_opt.sort():
                        result_opt = z_opt
                    if result == None:
                        result = result_opt
                    else:
                        result = z3.If(precondition, result_opt, result)
            if result == None:
                raise TypeException(f'Error with sorts when enumerating options')
            restrictions = [or_zs(restriction_options)]
        else:
            result, restrictions = self._coerce_restrictions(z)
        if self.sort() == z.sort():
            result = z
        return result, restrictions

    # Overridden
    def len_restrictions(self, z):
        raise TypeException(f'{self} has no len')

    # Overridden
    def lookup_type_restrictions(self, z, index):
        raise TypeException(f'{self} cannot be indexed')

class ImpossibleType(BaseType):
    def __repr__(self):
        return '!'

    def sort(self):
        return z3.BoolSort()

    def _coerce_restrictions(self, z):
        raise UnexpectedException('Unreachable for ImpossibleType')

    def _accepts_sort(self, sort):
        return False

    def _is_subtype_of(self, t):
        return True

class BoolType(BaseType):
    def __repr__(self):
        return 'bool'

    def sort(self):
        return z3.BoolSort()

    def _coerce_restrictions(self, z):
        return z, []

    def _accepts_sort(self, sort):
        return any((sort_option == z3.BoolSort() for sort_option in get_sort_options(sort)))

    def _is_subtype_of(self, t):
        return isinstance(t, BoolType) or (isinstance(t, UnionType) and any((isinstance(o, BoolType) for o in t.options)))

class IntType(BaseType):
    def __repr__(self):
        return 'int'

    def sort(self):
        return z3.IntSort()

    def _coerce_restrictions(self, z):
        return z, []

    def _accepts_sort(self, sort):
        return any((sort_option == z3.IntSort() for sort_option in get_sort_options(sort)))

    def _is_subtype_of(self, t):
        return isinstance(t, IntType) or (isinstance(t, UnionType) and any((isinstance(o, IntType) for o in t.options)))

class RestrictedType(BaseType):
    def __init__(self, underlying, it_restrictions):
        self.underlying = underlying
        self.it_restrictions = it_restrictions

    def __repr__(self):
        return f'{self.underlying} {self.it_restrictions}'

    def sort(self):
        return self.underlying.sort()

    def _coerce_restrictions(self, z):
        result, restrictions = self.underlying.coerce_restrictions(z)
        restrictions = list(restrictions)
        substitutions = [(self.var('.it'), z)]
        for r in self.it_restrictions:
            restrictions.append(z3.substitute(r, substitutions))
        return result, restrictions

    def _accepts_sort(self, sort):
        return self.underlying._accepts_sort(sort)

    def len_restrictions(self, z):
        return self.underlying.len_restrictions(z)

    def lookup_type_restrictions(self, z, index):
        return self.underlying.lookup_type_restrictions(z, index)

    def _is_subtype_of(self, t):
        # TODO: this doesn't cover all the cases for restricted types
        return self.underlying._is_subtype_of(t)

def get_tuple_sort_arity(sort):
    if isinstance(sort, z3.DatatypeSortRef) and sort.num_constructors() == 1:
        return sort.constructor(0).arity()
    else:
        return None

def get_union_sort_count(sort):
    if isinstance(sort, z3.DatatypeSortRef) and sort.num_constructors() > 1:
        return sort.num_constructors()
    else:
        return None

def get_sort_options(sort):
    count = get_union_sort_count(sort)
    if count == None:
        return [sort]
    else:
        return [sort.constructor(i).domain(0) for i in range(count)]

class TupleType(BaseType):
    def __init__(self, members):
        self.members = members

    def __repr__(self):
        return 'tuple[' + ','.join((str(m) for m in self.members)) + ']'

    def sort(self):
        return z3.TupleSort(str(self), [m.sort() for m in self.members])[0]

    def _coerce_restrictions(self, z):
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
        for sort_option in get_sort_options(sort):
            ok = True
            if get_tuple_sort_arity(sort_option) == n:
                for i in range(n):
                    if not self.members[i]._accepts_sort(sort_option.constructor(0).domain(i)):
                        ok = False
            elif isinstance(sort_option, z3.SeqSortRef):
                for i in range(n):
                    if not self.members[i]._accepts_sort(sort_option.basis()):
                        ok = False
            else:
                ok = False
            if ok:
                return True
        return False

    def len_restrictions(self, z):
        return z3.IntVal(len(self.members)), []

    def lookup_type_restrictions(self, z, index):
        n = len(self.members)
        if z3.is_int_value(index):
            i = index.as_long()
            if i >= 0 and i < n:
                return z.sort().accessor(0,i)(z), self.members[i], []
            else:
                raise PreconditionException(f'Fixed index {i} out of range 0..{n}')
        elif n == 0:
            raise PreconditionException(f'Indexing empty tuple')
        else:
            result = z.sort().accessor(0,0)(z)
            for i in range(1, n):
                result = z3.If(index == i, z.sort().accessor(0,i)(z), result)
            return result, union_type(self.members), [index >= 0, index < n]

    def _is_subtype_of(self, t):
        if isinstance(t, UnionType):
            t_options = t.options
        else:
            t_options = [t]

        for t_o in t_options:
            ok = True
            if not isinstance(t_o, TupleType):
                ok = False
            elif len(t_o.members) != len(self.members):
                ok = False
            else:
                for i in range(len(self.members)):
                    if not self.members[i]._is_subtype_of(t_o.members[i]):
                        ok = False
            if ok:
                return True
        return False

class ArrayType(BaseType):
    def __init__(self, element):
        self.element = element

    def __repr__(self):
        return f'array {self.element}'

    def sort(self):
        return z3.SeqSort(self.element.sort())

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
        for sort_option in get_sort_options(sort):
            ok = True
            arity = get_tuple_sort_arity(sort)
            if isinstance(sort, z3.SeqSortRef):
                ok = self.element._accepts_sort(sort.basis())
            elif arity != None:
                for i in range(arity):
                    if not self.element._accepts_sort(sort.constructor(0).domain(i)):
                        ok = False
            else:
                ok = False
            if ok:
                return True
        return False

    def len_restrictions(self, z):
        return z3.Length(z), []

    def lookup_type_restrictions(self, z, index):
        return z[index], self.element, [index >= 0, index < z3.Length(z)]

    def _is_subtype_of(self, t):
        if isinstance(t, UnionType):
            t_options = t.options
        else:
            t_options = [t]

        for t_o in t_options:
            if isinstance(t_o, ArrayType) and self.element._is_subtype_of(t_o.element):
                return True
        return False

class UnionType(BaseType):
    def __init__(self, options):
        if len(options) < 2:
            raise UnexpectedException('Must have at least two options')
        self.options = options

    def __repr__(self):
        return 'union[' + ','.join((str(m) for m in self.options)) + ']'

    def sort(self):
        return z3.DisjointSum(str(self), [m.sort() for m in self.options])[0]

    def _coerce_restrictions(self, z):
        n = len(self.options)
        union_count = get_union_sort_count(z.sort())
        restrictions = []
        result = None
        if union_count != None:
            for src_i in range(union_count):
                src = z.sort().accessor(src_i, 0)(z)
                restriction_options = []
                precondition = z.sort().recognizer(src_i)(z)
                for i in range(n):
                    dest_t = self.options[i]
                    if dest_t._accepts_sort(src.sort()):
                        coerced, rs = dest_t.coerce_restrictions(src)
                        restriction_options.append(and_zs(rs))
                        yesval = self.sort().constructor(i)(src)
                        if result == None:
                            result = yesval
                        else:
                            result = z3.If(and_zs([precondition] + rs), yesval, result)
                restrictions.append(z3.Implies(precondition, or_zs(restriction_options)))
        else:
            restriction_options = []
            for i in range(n):
                dest_t = self.options[i]
                if dest_t._accepts_sort(z.sort()):
                    coerced, rs = dest_t.coerce_restrictions(z)
                    restriction_options.append(and_zs(rs))
                    yesval = self.sort().constructor(i)(z)
                    if result == None:
                        result = yesval
                    else:
                        result = z3.If(and_zs(rs), yesval, result)
            restrictions.append(or_zs(restriction_options))
        if result == None:
            raise UnexpectedException('Error coercing into union type')
        return result, restrictions

    def _accepts_sort(self, sort):
        for sort_option in get_sort_options(sort):
            ok = False
            for option in self.options:
                if option._accepts_sort(sort_option):
                    return True
        return False

    def _is_subtype_of(self, t):
        if isinstance(t, UnionType):
            for option in self.options:
                ok = False
                for t_option in t.options:
                    if option._is_subtype_of(t_option):
                        ok = True
                if not ok:
                    return False
            return True
        else:
            for option in self.options:
                if not option._is_subtype_of(t):
                    return False
            return True

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

def union_type(orig_options):
    squashed_options = []
    for orig_option in orig_options:
        if isinstance(orig_option, ImpossibleType):
            option_options = []
        elif isinstance(orig_option, UnionType):
            option_options = orig_option.options
        else:
            option_options = [orig_option]

        for option in option_options:
            want = True
            for i in range(len(squashed_options)):
                if squashed_options[i]._is_subtype_of(option):
                    squashed_options[i] = None
                elif option._is_subtype_of(squashed_options[i]):
                    want = False
            if want:
                squashed_options.append(option)
            squashed_options = [opt for opt in squashed_options if opt != None]

    if len(squashed_options) == 0:
        return ImpossibleType()
    elif len(squashed_options) == 1:
        return squashed_options[0]
    else:
        return UnionType(squashed_options)

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
