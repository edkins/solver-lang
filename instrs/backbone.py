from __future__ import annotations
import z3
from instrs.errors import *
from instrs.misc import sequence_zs
from typing import Optional, Any

class BBType:
    # Overridden
    def z3sort(self) -> z3.SortRef:
        raise UnexpectedException()

    def z3var(self, name) -> z3.ExprRef:
        return z3.Const(name, self.z3sort())

    # Overridden by BBUnion
    def get_options(self) -> list[BBType]:
        return [self]

    # Overridden by BBUnion
    def z3accessor(self, i:int, z:z3.ExprRef) -> z3.ExprRef:
        if z.sort() != self.z3sort():
            raise UnexpectedException(f'z is wrong sort, expected {self.z3sort()} got {z.sort()}')
        elif i == 0:
            return z
        else:
            raise UnexpectedException('Index out of range')

    # Overridden by BBUnion
    def z3recognizer(self, i:int, z:z3.ExprRef) -> z3.ExprRef:
        if i == 0:
            return z3.BoolVal(True)
        else:
            raise UnexpectedException('Index out of range')

    def z3eq(self, z0:z3.ExprRef, z1:z3.ExprRef) -> z3.ExprRef:
        if z0.sort() != self.z3sort() or z1.sort() != self.z3sort():
            raise UnexpectedException('z0 or z1 is the wrong sort in eq')
        return z0 == z1

    # Overridden
    def z3_to_python(self, z:z3.ExprRef) -> Any:
        raise UnexpectedException()

class BBInt(BBType):
    def z3sort(self) -> z3.SortRef:
        return z3.IntSort()

    def __eq__(self, other) -> bool:
        return isinstance(other, BBInt)

    def __repr__(self) -> str:
        return 'int'

    def z3_to_python(self, z:z3.ExprRef) -> int:
        if isinstance(z, z3.IntNumRef):
            return z.as_long()
        else:
            raise UnexpectedException('not a const int')

class BBBool(BBType):
    def z3sort(self) -> z3.SortRef:
        return z3.BoolSort()

    def __eq__(self, other) -> bool:
        return isinstance(other, BBBool)

    def __repr__(self) -> str:
        return 'bool'

    def z3_to_python(self, z:z3.ExprRef) -> bool:
        if z.sort() != self.z3sort():
            raise UnexpectedException('wrong sort')
        elif z3.is_true(z):
            return True
        elif z3.is_false(z):
            return False
        else:
            raise UnexpectedException('not a const bool')

class BBArray(BBType):
    def __init__(self, element:BBType):
        self.sort = z3.SeqSort(element.z3sort())
        self.element = element

    def z3sort(self) -> z3.SortRef:
        return self.sort

    def __eq__(self, other) -> bool:
        return isinstance(other, BBArray) and self.element == other.element

    def __repr__(self) -> str:
        return f'array[{self.element}]'

    def z3_to_python(self, z:z3.ExprRef) -> Any:
        if not isinstance(z, z3.SeqRef):
            raise UnexpectedException(f'Expected SeqRef at this point, got {type(z)}')
        n = z3.simplify(z3.Length(z)).as_long()
        return [self.element.z3_to_python(z3.simplify(z[i])) for i in range(n)]

class BBTuple(BBType):
    def __init__(self, members:list[BBType]):
        self.members = tuple(members)
        self.sort = z3.TupleSort(str(self), [m.z3sort() for m in members])[0]

    def z3sort(self) -> z3.DatatypeSortRef:
        return self.sort

    def __repr__(self) -> str:
        return f'tuple[{",".join((str(m) for m in self.members))}]'

    def __eq__(self, other) -> bool:
        return isinstance(other, BBTuple) and self.members == other.members

    def z3tuple(self, zs:list[z3.ExprRef]) -> z3.ExprRef:
        if len(zs) != len(self.members):
            raise UnexpectedException(f'Expecting {len(self.members)} items for tuple, got {len(zs)}')
        return self.z3sort().constructor(0)(*zs)

    def tuple_len(self) -> int:
        return len(self.members)

    def z3member(self, i:int, z:z3.ExprRef) -> z3.ExprRef:
        return self.z3sort().accessor(0,i)(z)

    def z3_to_python(self, z:z3.ExprRef) -> tuple:
        if z.sort() != self.z3sort():
            raise UnexpectedException('wrong sort')
        return tuple((self.members[i].z3_to_python(z3.simplify(self.z3member(i,z))) for i in range(len(self.members))))


class BBUnion(BBType):
    def __init__(self, options:list[BBType]):
        if len(options) < 2:
            raise UnexpectedException('Must have at least two options for BBUnion')
        for opt in options:
            if isinstance(opt, BBUnion):
                raise UnexpectedException('Cannot take union of unions. Use flat_union instead')
        self.options = tuple(options)
        self.sort = z3.DisjointSum(str(self), [m.z3sort() for m in self.options])[0]

    def z3sort(self) -> z3.DatatypeSortRef:
        return self.sort

    def __repr__(self) -> str:
        return f'union[{",".join((str(m) for m in self.options))}]'

    def get_options(self) -> list[BBType]:
        return list(self.options)

    def __eq__(self, other) -> bool:
        return isinstance(other, BBUnion) and self.options == other.options

    def z3accessor(self, i:int, z:z3.ExprRef) -> z3.ExprRef:
        sort = self.z3sort()
        if z.sort() != sort:
            raise UnexpectedException('z is wrong sort, expected {sort} got {z.sort()}')
        elif i >= 0 and i < len(self.options):
            return sort.accessor(i,0)(z)
        else:
            raise UnexpectedException('Index out of range')

    def z3recognizer(self, i:int, z:z3.ExprRef) -> z3.ExprRef:
        sort = self.z3sort()
        if z.sort() != sort:
            raise UnexpectedException('z is wrong sort, expected {sort} got {z.sort()}')
        elif i >= 0 and i < len(self.options):
            return sort.recognizer(i)(z)
        else:
            raise UnexpectedException('Index out of range')

    def z3constructor(self, i:int, z:z3.ExprRef) -> z3.ExprRef:
        if i >= 0 and i < len(self.options):
            if z.sort() != self.options[i].z3sort():
                raise UnexpectedException('z is wrong sort, expected {self.options[i].z3sort()} got {z.sort()}')
            return self.z3sort().constructor(i)(z)
        else:
            raise UnexpectedException('Index out of range')

    def z3_to_python(self, z:z3.ExprRef) -> Any:
        if z.sort() != self.z3sort():
            raise UnexpectedException('wrong sort')
        for i in range(len(self.options)):
            if z3.is_true(z3.simplify(self.z3recognizer(i,z))):
                return self.options[i].z3_to_python(z3.simplify(self.z3accessor(i,z)))
        raise UnexpectedException('Not a const sum value')


BBZ = BBInt()
BBB = BBBool()

def pairwise_union(t0: BBType, t1: BBType) -> Optional[BBType]:
    if isinstance(t0, BBUnion) or isinstance(t1, BBUnion):
        raise UnexpectedException('Not expecting union types here')
    elif t0 == t1:
        return t1
    elif isinstance(t0, BBTuple) and isinstance(t1, BBTuple):
        if t0.tuple_len() != t1.tuple_len():
            return None
        ts = [flat_union([m0, m1]) for m0, m1 in zip(t0.members, t1.members)]
        return BBTuple(ts)
    elif isinstance(t0, BBArray) and isinstance(t1, BBArray):
        return BBArray(flat_union([t0.element, t1.element]))
    elif isinstance(t0, BBArray) and isinstance(t1, BBTuple):
        element = flat_union([t0.element] + list(t1.members))
        return BBArray(element)
    elif isinstance(t0, BBTuple) and isinstance(t1, BBArray):
        element = flat_union([t1.element] + list(t0.members))
        return BBArray(element)
    else:
        return None

def flat_union(bbs: list[BBType]) -> BBType:
    stuff = flat_union_rearrange(bbs)
    if len(stuff) == 0:
        raise NoOptionsException()
    elif len(stuff) == 1:
        return stuff[0][0]
    else:
        return BBUnion([s[0] for s in stuff])

def flat_union_rearrange(bbs: list[BBType]) -> list[tuple[BBType,list[tuple[int,int]]]]:
    result:list[BBType] = []
    result_order:list[list[tuple[int,int]]] = []
    for j in range(len(bbs)):
        opts = bbs[j].get_options()
        for k in range(len(opts)):
            addition = opts[k]
            addition_order = [(j,k)]
            i = 0
            while i < len(result):
                u = pairwise_union(result[i], addition)
                if isinstance(u, BBType):
                    result.pop(i)
                    addition_order += result_order.pop(i)
                    addition = u
                else:
                    i += 1
            result.append(addition)
            result_order.append(addition_order)

    if len(result) != len(result_order):
        raise UnexpectedException('oops')
    stuff = list(zip(result, result_order))
    stuff.sort(key=lambda s:str(s[0]))     # sort options alphabetically so that union[int,str]==union[str,int]
    return stuff
