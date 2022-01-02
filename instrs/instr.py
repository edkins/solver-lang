from __future__ import annotations
from typing import Union, Callable, Any, Optional
import logging
import z3
from instrs.backbone import *
from instrs.errors import *
from instrs.misc import sequence_zs

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

class Instr:
    # Overridden
    def exec(self, rf:RegFile):
        raise UnexpectedException()

    # Overridden
    def remap(self, m:RegRemapping) -> Instr:
        raise UnexpectedException()

class Mov(Instr):
    def __init__(self, dest:Reg, r:Val):
        self.dest = dest
        self.r = r

    def __repr__(self):
        return f'{self.dest} <- {self.r}'

    def exec(self, rf:RegFile):
        z,t = rf.get(self.r)
        rf.put(self.dest, t, z)

    def remap(self, m:RegRemapping) -> Instr:
        return Mov(m.reg(self.dest), m.val(self.r))

class Add(Instr):
    def __init__(self, dest:Reg, r0:Val, r1:Val):
        self.dest = dest
        self.r0 = r0
        self.r1 = r1

    def __repr__(self):
        return f'{self.dest} <- {self.r0} + {self.r1}'

    def exec(self, rf:RegFile):
        z0 = rf.get_coerce(self.r0, BBZ)
        z1 = rf.get_coerce(self.r1, BBZ)
        if not isinstance(z0, z3.ArithRef) or not isinstance(z1, z3.ArithRef):
            raise UnexpectedException(f'Expected ArithRef, got {type(z0)} and {type(z1)}')
        rf.put(self.dest, BBZ, z0 + z1)

    def remap(self, m:RegRemapping) -> Instr:
        return Add(m.reg(self.dest), m.val(self.r0), m.val(self.r1))

class Sub(Instr):
    def __init__(self, dest:Reg, r0:Val, r1:Val):
        self.dest = dest
        self.r0 = r0
        self.r1 = r1

    def __repr__(self):
        return f'{self.dest} <- {self.r0} - {self.r1}'

    def exec(self, rf:RegFile):
        z0 = rf.get_coerce(self.r0, BBZ)
        z1 = rf.get_coerce(self.r1, BBZ)
        if not isinstance(z0, z3.ArithRef) or not isinstance(z1, z3.ArithRef):
            raise UnexpectedException(f'Expected ArithRef, got {type(z0)} and {type(z1)}')
        rf.put(self.dest, BBZ, z0 - z1)

    def remap(self, m:RegRemapping) -> Instr:
        return Sub(m.reg(self.dest), m.val(self.r0), m.val(self.r1))

class Mul(Instr):
    def __init__(self, dest:Reg, r0:Val, r1:Val):
        self.dest = dest
        self.r0 = r0
        self.r1 = r1

    def __repr__(self):
        return f'{self.dest} <- {self.r0} * {self.r1}'

    def exec(self, rf:RegFile):
        z0 = rf.get_coerce(self.r0, BBZ)
        z1 = rf.get_coerce(self.r1, BBZ)
        if not isinstance(z0, z3.ArithRef) or not isinstance(z1, z3.ArithRef):
            raise UnexpectedException(f'Expected ArithRef, got {type(z0)} and {type(z1)}')
        rf.put(self.dest, BBZ, z0 * z1)

    def remap(self, m:RegRemapping) -> Instr:
        return Mul(m.reg(self.dest), m.val(self.r0), m.val(self.r1))

class Neg(Instr):
    def __init__(self, dest:Reg, r:Val):
        self.dest = dest
        self.r = r

    def __repr__(self):
        return f'{self.dest} <- -{self.r}'

    def exec(self, rf:RegFile):
        z = rf.get_coerce(self.r, BBZ)
        if not isinstance(z, z3.ArithRef):
            raise UnexpectedException(f'Expected ArithRef, got {type(z)}')
        rf.put(self.dest, BBZ, -z)

    def remap(self, m:RegRemapping) -> Instr:
        return Neg(m.reg(self.dest), m.val(self.r))

class Lt(Instr):
    def __init__(self, dest:Reg, r0:Val, r1:Val):
        self.dest = dest
        self.r0 = r0
        self.r1 = r1

    def __repr__(self):
        return f'{self.dest} <- {self.r0} < {self.r1}'

    def exec(self, rf:RegFile):
        z0 = rf.get_coerce(self.r0, BBZ)
        z1 = rf.get_coerce(self.r1, BBZ)
        if not isinstance(z0, z3.ArithRef) or not isinstance(z1, z3.ArithRef):
            raise UnexpectedException(f'Expected ArithRef, got {type(z0)} and {type(z1)}')
        rf.put(self.dest, BBB, z0 < z1)

    def remap(self, m:RegRemapping) -> Instr:
        return Lt(m.reg(self.dest), m.val(self.r0), m.val(self.r1))

class Le(Instr):
    def __init__(self, dest:Reg, r0:Val, r1:Val):
        self.dest = dest
        self.r0 = r0
        self.r1 = r1

    def __repr__(self):
        return f'{self.dest} <- {self.r0} <= {self.r1}'

    def exec(self, rf:RegFile):
        z0 = rf.get_coerce(self.r0, BBZ)
        z1 = rf.get_coerce(self.r1, BBZ)
        if not isinstance(z0, z3.ArithRef) or not isinstance(z1, z3.ArithRef):
            raise UnexpectedException(f'Expected ArithRef, got {type(z0)} and {type(z1)}')
        rf.put(self.dest, BBB, z0 <= z1)

    def remap(self, m:RegRemapping) -> Instr:
        return Le(m.reg(self.dest), m.val(self.r0), m.val(self.r1))

class Eq(Instr):
    def __init__(self, dest:Reg, r0:Val, r1:Val, ne:bool):
        self.dest = dest
        self.r0 = r0
        self.r1 = r1
        self.ne = ne

    def __repr__(self):
        return f'{self.dest} <- {self.r0} {"!=" if self.ne else "=="} {self.r1}'

    def exec(self, rf:RegFile):
        z0,t0 = rf.get(self.r0)
        z1,t1 = rf.get(self.r1)
        t = flat_union([t0, t1])
        z0c = rf.coerce(t, t0, z0)
        z1c = rf.coerce(t, t1, z1)
        result = t.z3eq(z0c, z1c)
        if self.ne:
            rf.put(self.dest, BBB, z3.Not(result))
        else:
            rf.put(self.dest, BBB, result)

    def remap(self, m:RegRemapping) -> Instr:
        return Eq(m.reg(self.dest), m.val(self.r0), m.val(self.r1), self.ne)

class Listing(Instr):
    def __init__(self, dest:Reg, rs:list[Val]):
        self.dest = dest
        self.rs = rs

    def __repr__(self):
        return f'{self.dest} <- {self.rs}'

    def exec(self, rf:RegFile):
        zs = []
        ts = []
        for r in self.rs:
            z,t = rf.get(r)
            zs.append(z)
            ts.append(t)
        bb = BBTuple(ts)
        rf.put(self.dest, bb, bb.z3tuple(zs))

    def remap(self, m:RegRemapping) -> Instr:
        return Listing(m.reg(self.dest), [m.val(r) for r in self.rs])

class Len(Instr):
    def __init__(self, dest:Reg, r:Val):
        self.dest = dest
        self.r = r

    def __repr__(self):
        return f'{self.dest} <- len {self.r}'

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

    def remap(self, m:RegRemapping) -> Instr:
        return Len(m.reg(self.dest), m.val(self.r))

class Lookup(Instr):
    def __init__(self, dest:Reg, r0:Val, r1:Val):
        self.dest = dest
        self.r0 = r0
        self.r1 = r1

    def __repr__(self):
        return f'{self.dest} <- {self.r0}[{self.r1}]'

    def exec(self, rf:RegFile):
        zu,tu = rf.get(self.r0)
        zi = rf.get_coerce(self.r1, BBZ)

        ts = tu.get_options()
        result_type_options = []
        possible_indices:list[list[int]] = [[] for i in range(len(ts))]
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

        result_type = flat_union(result_type_options)
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
                if not isinstance(z, z3.SeqRef):
                    raise UnexpectedException(f'Expected SeqRef got {type(z)}')
                rf.check(zi >= z3.IntVal(0), 'Index must be nonnegative')
                rf.check(z3.Implies(tu.z3recognizer(i,z), zi < z3.Length(z)), 'Index must be less than length of array')
                return z[zi]
            else:
                raise TypeException(f'Cannot index into type {t}')

        rf.put_union(self.dest, result_type, zu, tu, munge)

    def remap(self, m:RegRemapping) -> Instr:
        return Lookup(m.reg(self.dest), m.val(self.r0), m.val(self.r1))

class Arr(Instr):
    def __init__(self, dest:Reg, r:Val):
        self.dest = dest
        self.r = r

    def __repr__(self):
        return f'{self.dest} <- arr {self.r}'

    def exec(self, rf:RegFile):
        zu,tu = rf.get(self.r)
        ts = tu.get_options()

        element_types:list[BBType] = []
        for t in ts:
            if isinstance(t, BBTuple):
                element_types += t.members
            elif isinstance(t, BBArray):
                element_types.append(t.element)
            else:
                raise TypeException(f'Can only convert arrays and tuples to arr, not {t}')
        if len(element_types) == 0:
            # No possibilities for contents - so must be empty tuple
            rtype = BBTuple([])
            rf.put(self.dest, rtype, rtype.z3tuple([]))
            return
        element_type = flat_union(element_types)
        result_type = BBArray(element_type)

        def munge(i:int,z:z3.ExprRef):
            t = ts[i]
            if z.sort() != t.z3sort():
                raise UnexpectedException('sort mismatch')
            if isinstance(t, BBTuple):
                zs = []
                for j in range(t.tuple_len()):
                    zc = rf.coerce(element_type, t.members[j], t.z3member(j,z))
                    zs.append(zc)
                return sequence_zs(element_type.z3sort(), zs)
            elif isinstance(t, BBArray):
                return z
            else:
                raise TypeException(f'Cannot take length of {t}')

        rf.put_union(self.dest, result_type, zu, tu, munge)

    def remap(self, m:RegRemapping) -> Instr:
        return Arr(m.reg(self.dest), m.val(self.r))

class Assert(Instr):
    def __init__(self, r:Val, msg:str):
        self.r = r
        self.msg = msg

    def __repr__(self):
        return f'assert {self.r}'

    def exec(self, rf:RegFile):
        z = rf.get_coerce(self.r, BBB)
        rf.check(z, self.msg)

    def remap(self, m:RegRemapping) -> Instr:
        return Assert(m.val(self.r), self.msg)

class Precondition(Instr):
    def __init__(self, r:Val):
        self.r = r

    def __repr__(self):
        return f'precondition {self.r}'

    def exec(self, rf:RegFile):
        z = rf.get_coerce(self.r, BBB)
        rf.assume(z)

    def remap(self, m:RegRemapping) -> Instr:
        return Precondition(m.val(self.r))


class Unreachable(Instr):
    def __repr__(self):
        return 'unreachable'

    def exec(self, rf:RegFile):
        rf.check(z3.BoolVal(False), 'unreachable')

    def remap(self, m:RegRemapping) -> Instr:
        return Unreachable()

class Fn(Instr):
    def __repr__(self):
        return 'fn'

    def exec(self, rf:RegFile):
        rf.push()

    def remap(self, m:RegRemapping) -> Instr:
        return Fn()

class Arg(Instr):
    def __init__(self, dest:Reg, typ:BBType):
        self.dest = dest
        self.typ = typ

    def __repr__(self):
        return f'arg {self.dest} : {self.typ}'

    def exec(self, rf:RegFile):
        rf.put_arg(self.dest, self.typ)

    def remap(self, m:RegRemapping) -> Instr:
        return Arg(m.reg(self.dest), self.typ)

class Coerce(Instr):
    def __init__(self, dest:Reg, r:Val, typ:BBType):
        self.dest = dest
        self.r = r
        self.typ = typ

    def __repr__(self):
        return f'{self.dest} <- coerce[{self.typ}] {self.r}'

    def exec(self, rf:RegFile):
        z = rf.get_coerce(self.r, self.typ)
        rf.put(self.dest, self.typ, z)

    def remap(self, m:RegRemapping) -> Instr:
        return Coerce(m.reg(self.dest), m.val(self.r), self.typ)

class Ret(Instr):
    def __init__(self, r:Val):
        self.r = r

    def __repr__(self):
        return f'ret {self.r}'

    def exec(self, rf:RegFile):
        z,t = rf.get(self.r)
        rf.pop()

    def remap(self, m:RegRemapping) -> Instr:
        return Ret(m.val(self.r))
