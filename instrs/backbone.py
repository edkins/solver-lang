import z3
from instrs.errors import *

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

    # Overridden
    def z3eq_is_eq(self) -> bool:
        return True

    def z3eq(self, z0:z3.ExprRef, z1:z3.ExprRef) -> z3.ExprRef:
        if z0.sort() != self.z3sort() or z1.sort() != self.z3sort():
            raise UnexpectedException('z0 or z1 is the wrong sort in eq')
        if self.z3eq_is_eq():
            return z0 == z1
        else:
            return self.z3eq_structural(z0, z1)

    # Overridden
    def z3eq_structural(self, z0:z3.ExprRef, z1:z3.ExprRef) -> z3.ExprRef:
        raise UnexpectedException()

class BBInt(BBType):
    def __init__(self):
        BBType.__init__(self, z3.IntSort())

    def __eq__(self, other) -> bool:
        return isinstance(other, BBInt)

    def __repr__(self) -> str:
        return 'int'

class BBBool(BBType):
    def __init__(self):
        BBType.__init__(self, z3.BoolSort())

    def __eq__(self, other) -> bool:
        return isinstance(other, BBBool)

    def __repr__(self) -> str:
        return 'bool'

class BBArray(BBType):
    def __init__(self, element:BBType):
        BBType.__init__(self, z3.SeqSort(element.z3sort()))
        self.element = element

    def __eq__(self, other) -> bool:
        return isinstance(other, BBArray) and self.element == other.element

    def __repr__(self) -> str:
        return f'array[{self.element}]'

    def z3eq_is_eq(self) -> bool:
        return self.element.z3eq_is_eq()

    def z3eq_structural(self, z0:z3.ExprRef, z1:z3.ExprRef) -> z3.ExprRef:
        i = z3.Int('.i')
        return z3.And(z3.Length(z0) == z1.Length(z1), z3.ForAll([i], z3.Implies(z3.And(i >= 0, i < z3.Length(z0)), self.element.z3eq(z0[i], z1[i]))))

class BBTuple(BBType):
    def __init__(self, members:list[BBType]):
        self.members = tuple(members)
        BBType.__init__(self, z3.TupleSort(str(self), [m.z3sort() for m in members]))

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

    def z3eq_is_eq(self) -> bool:
        return all((m.z3eq_is_eq() for m in self.members))

    def z3eq_structural(self, z0:z3.ExprRef, z1:z3.ExprRef) -> z3.ExprRef:
        return and_zs([self.members[i].z3eq(self.z3member(i,z0), self.z3member(i,z1)) for i in range(len(self.members))])

class BBUnion(BBType):
    def __init__(self, options:list[BBType]):
        if len(options) < 2:
            raise UnexpectedException('Must have at least two options for BBUnion')
        for opt in options:
            if isinstance(opt, BBUnion):
                raise UnexpectedException('Cannot take union of unions. Use flat_union instead')
        self.options = tuple(options)
        BBType.__init__(self, z3.DisjointSum(str(self), [m.z3sort() for m in self.options]))

    def __repr__(self) -> str:
        return f'union[{",".join((str(m) for m in self.options))}]'

    def get_options(self) -> list[BBType]:
        return list(self.options)

    def __eq__(self, other) -> bool:
        return isinstance(other, BBUnion) and self.options == other.options

    def z3accessor(self, i:int, z:z3.ExprRef) -> list[z3.ExprRef]:
        sort = self.z3sort()
        if z.sort() != sort:
            raise UnexpectedException('z is wrong sort, expected {sort} got {z.sort()}')
        elif i >= 0 and i < len(self.options):
            return [sort.accessor(i,0)(z) for i in range(len(self.options))]
        else:
            raise UnexpectedException('Index out of range')

    def z3recognizer(self, i:int, z:z3.ExprRef) -> z3.ExprRef:
        if i >= 0 and i < len(self.options):
            return self.z3sort().recognizer(i)(z)
        else:
            raise UnexpectedException('Index out of range')

BBZ = BBInt()
BBB = BBBool()

def flat_union(bbs: list[BBType]):
    result = []
    for bb in bbs:
        for opt in bb.get_options():
            if opt not in result:
                result.append(opt)
    if len(result) == 0:
        raise NoOptionsException()
    elif len(result) == 1:
        return result[0]
    else:
        result.sort(key=str)     # sort options alphabetically so that union[int,str]==union[str,int]
        return BBUnion(result)
