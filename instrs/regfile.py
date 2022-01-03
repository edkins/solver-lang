from typing import Union, Callable
import z3
from instrs.backbone import *

class Reg:
    def __init__(self, name:str):
        self.name = name

    def __repr__(self):
        return self.name

Val = Union[Reg, int, bool]

class StackFrame:
    def __init__(self):
        self.vars:set[str] = set()

class RegRemapping:
    def __init__(self, outer:set[str], prefix:str):
        self.outer = set(outer)
        self.prefix = prefix

    def reg(self, r:Reg) -> Reg:
        if r.name in self.outer:
            return r
        else:
            return Reg(self.prefix + r.name)

    def val(self, v:Val) -> Val:
        if isinstance(v, Reg):
            return self.reg(v)
        else:
            return v

class RegFile:
    def __init__(self, solver:z3.Solver):
        self.regs:dict[str,BBType] = {}
        self.funcs:set[str] = set()
        self.solver = solver
        self.stack = [StackFrame()]

    def push(self):
        self.solver.push()
        self.stack.append(StackFrame())

    def pop(self):
        if len(self.stack) <= 1:
            raise StackEmptyException()
        for x in self.stack.pop().vars:
            del self.regs[x]

    def get(self, v:Val) -> tuple[z3.ExprRef, BBType]:
        if isinstance(v, bool):
            return z3.BoolVal(v), BBB
        elif isinstance(v, int):
            return z3.IntVal(v), BBZ
        elif isinstance(v, Reg):
            if v.name in self.regs:
                bb = self.regs[v.name]
                return bb.z3var(v.name), bb
            else:
                raise NoSuchRegException(v.name)
        else:
            raise UnexpectedException('Unrecognized value class')

    def get_coerce(self, v:Val, bb:BBType) -> z3.ExprRef:
        z,t = self.get(v)
        return self.coerce(bb, t, z)

    def coerce(self, dt:BBType, t:BBType, z:z3.ExprRef) -> z3.ExprRef:
        if t == dt:
            return z
        else:
            t_opts = t.get_options()
            result = None
            for i in range(len(t_opts)):
                try:
                    t_opt = t_opts[i]
                    z_opt = t.z3accessor(i,z)
                    if t_opt == dt:
                        result_opt = z_opt
                    elif isinstance(dt, BBArray):
                        result_opt = self.coerce_array(dt, t_opt, z_opt)
                    elif isinstance(dt, BBTuple):
                        result_opt = self.coerce_tuple(dt, t_opt, z_opt)
                    elif isinstance(dt, BBUnion):
                        result_opt = self.coerce_union(dt, t_opt, z_opt)
                    else:
                        raise TypeException(f'Cannot coerce {t_opt} to {dt}')

                    if result == None:
                        result = result_opt
                    else:
                        result = z3.If(t.z3recognizer(i,z), result_opt, result)
                except TypeException as e:
                    try:
                        self.check(z3.Not(t.z3recognizer(i,z)), f'union type check')
                    except AssertionException as e1:
                        raise e
            if isinstance(result, z3.ExprRef):
                return result
            else:
                raise UnexpectedException('No result')

    def coerce_array(self, dt:BBArray, t:BBType, z:z3.ExprRef) -> z3.ExprRef:
        if isinstance(t, BBArray):
            if not isinstance(z, z3.SeqRef):
                raise UnexpectedException(f'Expected SeqRef at this point, got {type(z)}')
            x = t.z3var('.x')
            name = 'coerce[{dt},{t}]'
            f = z3.RecFunction(name, t.z3sort(), dt.z3sort())
            zc = self.coerce(dt.element, t.element, z[0])
            z3.RecAddDefinition(f, [x], z3.If(
                x == z3.Empty(t.z3sort()),
                z3.Empty(dt.z3sort()),
                z3.Concat(z3.Unit(zc), f(z3.SubSeq(x, 1, z3.Length(x)-1)))))
            return f(z)
        elif isinstance(t, BBTuple):
            zs = []
            for i in range(t.tuple_len()):
                z0 = self.coerce(dt.element, t.members[i], t.z3member(i,z))
                zs.append(z0)
            return sequence_zs(dt.z3sort(), zs)
        else:
            raise TypeException('Cannot coerce {t} to {dt}')

    def coerce_tuple(self, dt:BBTuple, t:BBType, z:z3.ExprRef) -> z3.ExprRef:
        if isinstance(t, BBTuple):
            if t.tuple_len() != dt.tuple_len():
                raise TypeException(f'Cannot coerce {t} to {dt} (tuples are different lengths)')
            zs = []
            for i in range(t.tuple_len()):
                zs.append(self.coerce(dt.members[i], t.members[i], t.z3member(i,z)))
            return dt.z3tuple(zs)
        elif isinstance(t, BBArray):
            if not isinstance(z, z3.SeqRef):
                raise UnexpectedException(f'Expecting SeqRef, got {type(z)}')
            self.check(z3.Length(z) == z3.IntVal(dt.tuple_len()), 'Array length')
            zs = []
            for i in range(dt.tuple_len()):
                zs.append(self.coerce(dt.members[i], t.element, z[i]))
            return dt.z3tuple(zs)
        else:
            raise TypeException(f'Cannot coerce {t} to {self}')

    def coerce_union(self, dt:BBUnion, t:BBType, z:z3.ExprRef) -> z3.ExprRef:
        opts = dt.get_options()
        for i in range(len(opts)):
            try:
                zc = self.coerce(opts[i], t, z)
                return dt.z3constructor(i, zc)
            except TypeException:
                pass
        raise TypeException('Cannot coerce {t} to {dt} (no options match)')

    def put(self, r:Reg, bb:BBType, z:z3.ExprRef):
        if r.name in self.regs:
            raise RegAlreadySetException(r.name)
        if bb.z3sort() != z.sort():
            raise UnexpectedException(f'backbone type sort {bb.z3sort()} does not match z3 expr sort {z.sort()}')
        self.regs[r.name] = bb
        self.stack[-1].vars.add(r.name)
        self.solver.add(bb.z3var(r.name) == z)

    def put_union(self, r:Reg, bb:BBType, u:z3.ExprRef, ut:BBType, c:Callable[[int,z3.ExprRef],z3.ExprRef]):
        if r in self.regs:
            raise RegAlreadySetException(r.name)
        if ut.z3sort() != u.sort():
            raise UnexpectedException()

        self.regs[r.name] = bb
        self.stack[-1].vars.add(r.name)
        ts = ut.get_options()
        for i in range(len(ts)):
            z0 = ut.z3accessor(i,u)
            z1 = c(i,z0)
            if bb.z3sort() != z1.sort():
                raise UnexpectedException(f'backbone type sort {bb.z3sort()} does not match z3 expr sort {z1.sort()}')
            self.solver.add(z3.Implies(ut.z3recognizer(i,u), bb.z3var(r.name) == z1))

    def put_arg(self, r:Reg, bb:BBType):
        if r.name in self.regs:
            raise RegAlreadySetException(r.name)
        self.regs[r.name] = bb
        self.stack[-1].vars.add(r.name)

    def check(self, z:z3.ExprRef, msg:str):
        if self.satisfiable(z3.Not(z)):
            raise AssertionException(msg)

    def assume(self, z:z3.ExprRef):
        self.solver.add(z)

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

    def get_reg_python_value(self, r:Optional[Val]) -> tuple[Any,bool,BBType]:
        if isinstance(r, Reg):
            z,t = self.get(r)
            self.solver.push()
            try:
                if self.solver.check() == z3.sat:
                    value = self.solver.model()[z]
                    self.solver.push()
                    try:
                        self.solver.add(z != value)
                        more = self.solver.check() == z3.sat
                        return t.z3_to_python(value), more, t
                    finally:
                        self.solver.pop()
                else:
                    raise UnexpectedException('Unreachable')
            finally:
                self.solver.pop()
        elif isinstance(r, bool):
            return r, False, BBB
        elif isinstance(r, int):
            return r, False, BBZ
        elif r == None:
            return r, False, BBTuple([])
        else:
            raise Unimplemented("Don't know what this is")

