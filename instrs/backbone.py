from __future__ import annotations
import z3
from instrs.errors import *
from instrs.misc import sequence_zs
from typing import Optional, Any

class BBType:
    def __init__(self, sort:z3.SortRef):
        self.sort = sort

    def z3sort(self) -> z3.SortRef:
        return self.sort

    def z3var(self, name) -> z3.ExprRef:
        return z3.Const(name, self.z3sort())

    # Overridden by BBUnion
    def get_options(self) -> list[BBType]:
        return [self]

    # Overridden by BBUnion
    def z3accessor(self, i:int, z:z3.ExprRef) -> z3.ExprRef:
        if z.sort() != self.z3sort():
            raise UnexpectedException('z is wrong sort, expected {self.z3sort()} got {z.sort()}')
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

    def z3coerce(self, t:BBType, z:z3.ExprRef) -> z3.ExprRef:
        if t == self:
            return z
        else:
            t_opts = t.get_options()
            result = None
            for i in range(len(t_opts)):
                result_opt = self.z3coerce_actual(t, t.z3accessor(i,z))
                if result == None:
                    result = result_opt
                else:
                    result = z3.If(t.z3recognizer(i,z), result_opt, result)
            if isinstance(result, z3.ExprRef):
                return result
            else:
                raise UnexpectedException('No result')

    # Overridden
    def z3coerce_actual(self, t:BBType, z:z3.ExprRef) -> z3.ExprRef:
        raise TypeException('Cannot coerce {t} to {self}')

    # Overridden
    def z3_to_python(self, z:z3.ExprRef) -> Any:
        raise UnexpectedException()

class BBInt(BBType):
    def __init__(self):
        BBType.__init__(self, z3.IntSort())

    def __eq__(self, other) -> bool:
        return isinstance(other, BBInt)

    def __repr__(self) -> str:
        return 'int'

    def z3_to_python(self, z:z3.ExprRef) -> int:
        if z.sort() != self.z3sort():
            raise UnexpectedException('wrong sort')
        return z.as_long()

class BBBool(BBType):
    def __init__(self):
        BBType.__init__(self, z3.BoolSort())

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
        BBType.__init__(self, z3.SeqSort(element.z3sort()))
        self.element = element

    def __eq__(self, other) -> bool:
        return isinstance(other, BBArray) and self.element == other.element

    def __repr__(self) -> str:
        return f'array[{self.element}]'

    def z3coerce_actual(self, t:BBType, z:z3.ExprRef) -> z3.ExprRef:
        if isinstance(t, BBArray):
            x = t.z3var('.x')
            name = 'coerce[{self},{t}]'
            f = z3.RecFunction(name, t.z3sort(), self.z3sort())
            zc = self.element.z3coerce(t.element, z[0])
            z3.RecAddDefinition(f, [x], z3.If(
                x == z3.Empty(t.z3sort()),
                z3.Empty(self.z3sort()),
                z3.Concat(z3.Unit(zc), f(z3.SubSeq(x, 1, z3.Length(x)-1)))))
            return f(z)
        elif isinstance(t, BBTuple):
            zs = []
            for i in range(t.tuple_len()):
                z = self.element.z3coerce(t.members[i], t.z3member(i,z))
                zs.append(z)
            return sequence_zs(self.z3sort(), zs)
        else:
            raise TypeException('Cannot coerce {t} to {self}')

    def z3_to_python(self, z:z3.ExprRef) -> Any:
        if z.sort() != self.z3sort():
            raise UnexpectedException('wrong sort')
        n = z3.simplify(z3.Length(z)).as_long()
        return [self.element.z3_to_python(z3.simplify(z[i])) for i in range(n)]

class BBTuple(BBType):
    def __init__(self, members:list[BBType]):
        self.members = tuple(members)
        BBType.__init__(self, z3.TupleSort(str(self), [m.z3sort() for m in members])[0])

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

    def z3coerce_actual(self, t:BBType, z:z3.ExprRef) -> z3.ExprRef:
        if isinstance(t, BBTuple):
            if t.tuple_len() != self.tuple_len():
                raise TypeException('Cannot coerce {t} to {self} (tuples are different lengths)')
            zs = []
            for i in range(t.tuple_len()):
                z = self.members[i].z3coerce(t.members[i], t.z3member(i,z))
                zs.append(z)
            return self.z3tuple(zs)
        elif isinstance(t, BBArray):
            raise UnexpectedException('Cannot currently coerce {t} to {self} (unknown array length)')
        else:
            raise TypeException('Cannot coerce {t} to {self}')

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
        BBType.__init__(self, z3.DisjointSum(str(self), [m.z3sort() for m in self.options])[0])

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

    def z3coerce_actual(self, t:BBType, z:z3.ExprRef) -> z3.ExprRef:
        opts = self.get_options()
        for i in range(len(opts)):
            try:
                zc = opts[i].z3coerce(t, z)
                return self.z3constructor(i, zc)
            except TypeException:
                pass
        raise TypeException('Cannot coerce {t} to {self} (no options match)')

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

def flat_union(bbs: list[BBType]):
    result:list[BBType] = []
    for bb in bbs:
        for opt in bb.get_options():
            addition = opt
            i = 0
            while i < len(result):
                u = pairwise_union(result[i], addition)
                if isinstance(u, BBType):
                    result.pop(i)
                    addition = u
                else:
                    i += 1
            result.append(addition)

    if len(result) == 0:
        raise NoOptionsException()
    elif len(result) == 1:
        return result[0]
    else:
        result.sort(key=str)     # sort options alphabetically so that union[int,str]==union[str,int]
        return BBUnion(result)
