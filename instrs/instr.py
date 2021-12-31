from typing import Union, Callable
from instrs.backbone import *
from instrs.errors import *
import z3

class Reg:
    def __init__(self, name):
        self.name = name

Val = Union[Reg, int, bool]

class RegFile:
    def __init__(self, solver:z3.Solver):
        self.regs:dict[str,BBType] = {}
        self.solver = solver

    def get(self, v:Val) -> tuple[z3.ExprRef, BBType]:
        if isinstance(v, int):
            return z3.IntVal(v), BBZ
        elif isinstance(v, bool):
            return z3.BoolVal(v), BBB
        elif isinstance(v, Reg):
            if v in self.regs:
                bb = self.regs[v.name]
                return bb.z3var(v.name), bb
            else:
                raise NoSuchRegException(v.name)
        else:
            raise UnexpectedException('Unrecognized value class')

    def put(self, r:Reg, z:z3.ExprRef, bb:BBType):
        if r in self.regs:
            raise RegAlreadySetException(r.name)
        if bb.z3sort() != z.sort():
            raise UnexpectedException(f'backbone type sort {bb.z3sort()} does not match z3 expr sort {z.sort()}')
        self.regs[r.name] = bb
        self.solver.add(bb.z3var(r.name) == z)

    def put_union(self, r:Reg, bb:BBType, u:z3.ExprRef, ut:BBType, c:Callable[[int,z3.ExprRef],z3.ExprRef]):
        if r in self.regs:
            raise RegAlreadySetException(r.name)
        if ut.z3sort() != u.sort():
            raise UnexpectedException()

        self.regs[r.name] = bb
        ts = ut.get_options()
        for i in range(len(ts)):
            z0 = ut.z3accessor(i,u)
            z1 = c(i,z0)
            if bb.z3sort() != z1.sort():
                raise UnexpectedException(f'backbone type sort {bb.z3sort()} does not match z3 expr sort {z1.sort()}')
            self.solver.add(z3.Implies(ut.z3recognizer(i,u), bb.z3var(r.name) == z1))

    def check(self, z:z3.ExprRef, msg:str):
        if self.satisfiable(z3.Not(z)):
            raise AssertionException(msg)

    def satisfiable(self, z:z3.ExprRef):
        if z.sort() != z3.BoolSort():
            raise UnexpectedException(f'Assertion sort must be boolean, got {z.sort()}')
        self.solver.push()
        try:
            self.solver.add(z)
            return self.solver.check() == z3.sat
        finally:
            self.solver.pop()

    def get_possible_index_values(self, z:z3.ExprRef, maximum:int) -> list[int]:
        if z.sort() != z3.IntSort():
            raise UnexpectedException(f'Index sort must be int, got {z.sort()}')
        if maximum <= 0:
            raise OutOfBoundsException('Empty tuple')
        if self.satisfiable(z < z3.IntVal(0)):
            raise OutOfBoundsException('Negative index')
        if self.satisfiable(z >= z3.IntVal(maximum)):
            raise OutOfBoundsException('Index beyond length of tuple')
        results = []
        for index in range(maximum):
            if self.satisfiable(z == z3.IntVal(index)):
                results.append(index)
        if len(results) == 0:
            raise UnexpectedException('Unreachable in get_possible_index_values')
        return results


class Instr:
    pass

class Add(Instr):
    def __init__(self, dest:Reg, r0:Val, r1:Val):
        self.dest = dest
        self.r0 = r0
        self.r1 = r1

    def exec(self, rf:RegFile):
        z0,t0 = rf.get(self.r0)
        z1,t1 = rf.get(self.r1)
        if t0 != BBZ or t1 != BBZ:
            raise TypeException('Can only add ints')
        rf.put(self.dest, BBZ, z0 + z1)

class Sub(Instr):
    def __init__(self, dest:Reg, r0:Val, r1:Val):
        self.dest = dest
        self.r0 = r0
        self.r1 = r1

    def exec(self, rf:RegFile):
        z0,t0 = rf.get(self.r0)
        z1,t1 = rf.get(self.r1)
        if t0 != BBZ or t1 != BBZ:
            raise TypeException('Can only subtract ints')
        rf.put(self.dest, BBZ, z0 - z1)

class Mul(Instr):
    def __init__(self, dest:Reg, r0:Val, r1:Val):
        self.dest = dest
        self.r0 = r0
        self.r1 = r1

    def exec(self, rf:RegFile):
        z0,t0 = rf.get(self.r0)
        z1,t1 = rf.get(self.r1)
        if t0 != BBZ or t1 != BBZ:
            raise TypeException('Can only multiply ints')
        rf.put(self.dest, BBZ, z0 * z1)

class Neg(Instr):
    def __init__(self, dest:Reg, r:Val):
        self.dest = dest
        self.r = r

    def exec(self, rf:RegFile):
        z,t = rf.get(self.r)
        if t != BBZ:
            raise TypeException('Can only negate integers')
        rf.put(self.dest, BBZ, -z)

class Lt(Instr):
    def __init__(self, dest:Reg, r0:Val, r1:Val):
        self.dest = dest
        self.r0 = r0
        self.r1 = r1

    def exec(self, rf:RegFile):
        z0,t0 = rf.get(self.r0)
        z1,t1 = rf.get(self.r1)
        if t0 != BBZ or t1 != BBZ:
            raise TypeException('Can only compare ints')
        rf.put(self.dest, BBB, z0 < z1)

class Le(Instr):
    def __init__(self, dest:Reg, r0:Val, r1:Val):
        self.dest = dest
        self.r0 = r0
        self.r1 = r1

    def exec(self, rf:RegFile):
        z0,t0 = rf.get(self.r0)
        z1,t1 = rf.get(self.r1)
        if t0 != BBZ or t1 != BBZ:
            raise TypeException('Can only compare ints')
        rf.put(self.dest, BBB, z0 <= z1)

class Listing(Instr):
    def __init__(self, dest:Reg, rs:list[Val]):
        self.dest = dest
        self.rs = rs

    def exec(self, rf:RegFile):
        zs = []
        ts = []
        for r in self.rs:
            z,t = rf.get(r)
            zs.append(z)
            ts.append(t)
        bb = BBTuple(ts)
        rf.put(self.dest, bb, bb.z3tuple(zs))

class Len(Instr):
    def __init__(self, dest:Reg, r:Val):
        self.dest = dest
        self.r = r

    def exec(self, rf:RegFile):
        zu,tu = rf.get(self.r)
        ts = tu.get_options()
        n = len(ts)
        def munge(i:int,z:z3.ExprRef):
            t = ts[i]
            if z.sort() != t.z3sort():
                raise UnexpectedException('sort mismatch')
            if isinstance(t, BBTuple):
                return z3.IntVal(t.tuple_len())
            elif isinstance(t, BBArray):
                return z3.Length(z)
            else:
                raise TypeException(f'Cannot take length of {t}')

        rf.put_union(self.dest, BBZ, zu, tu, munge)

class Lookup(Instr):
    def __init__(self, dest:Reg, r0:Val, r1:Val):
        self.dest = dest
        self.r0 = r0
        self.r1 = r1

    def exec(self, rf:RegFile):
        zu,tu = rf.get(self.r0)
        zi,ti = rf.get(self.r1)
        if ti != BBZ:
            raise TypeException('Index must be an integer')

        ts = tu.get_options()
        result_type_options = []
        possible_indices = [None] * len(ts)
        for i in range(len(ts)):
            t = ts[i]
            if isinstance(t, BBTuple):
                indices = rf.get_possible_index_values(zi, t.tuple_len())
                possible_indices[i] = indices
                for index in indices:
                    result_type_options.append(t.members[index])
            elif isinstance(t, BBArray):
                result_type_options.append(t.element)
            else:
                raise TypeException(f'Cannot index into type {t}')

        result_type = flat_union(type_options)
        n = len(ts)
        def munge(i:int,z:z3.ExprRef):
            t = ts[i]
            if z.sort() != t.z3sort():
                raise UnexpectedException('sort mismatch')
            if isinstance(t, BBTuple):
                indices = possible_indices[i]
                result = t.z3member(indices[0], z)
                for index in indices[1:]:
                    result = z3.If(zi == z3.IntVal(index), t.z3member(index,z), result)
                return result
            elif isinstance(t, BBArray):
                rf.check(zi >= 0, 'Index must be nonnegative')
                rf.check(z3.Impl(tu.z3recognizer(i), zi < z3.Length(z)), 'Index must be less than length of array')
                return z[zi]
            else:
                raise TypeException(f'Cannot index into type {t}')

        rf.put_union(self.dest, result_type, zu, tu, munge)
