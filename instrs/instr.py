from __future__ import annotations
from typing import Union, Callable, Any, Optional
import logging
import z3
from instrs.backbone import *
from instrs.errors import *
from instrs.misc import sequence_zs
from instrs.regfile import *
from instrs.low_level_expr import LLExpr

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

class Expr(Instr):
    def __init__(self, dest:Reg, e:LLExpr):
        self.dest = dest
        self.e = e

    def __repr__(self):
        return f'{self.dest} <- {self.e} : {self.e.bbtype()}'

    def exec(self, rf:RegFile):
        z = self.e.z3expr(rf, [])
        rf.put(self.dest, self.e.bbtype(), z)

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

class Append(Instr):
    def __init__(self, dest:Reg, r0:Val, r1:Val):
        self.dest = dest
        self.r0 = r0
        self.r1 = r1

    def __repr__(self):
        return f'{self.dest} <- {self.r0} ++ {self.r1}'

    def exec(self, rf:RegFile):
        z0,t0 = rf.get(self.r0)
        z1,t1 = rf.get(self.r1)
        if isinstance(t0, BBArray) and isinstance(t1, BBArray):
            t = flat_union([t0, t1])
            z0c = rf.coerce(t, t0, z0)
            z1c = rf.coerce(t, t1, z1)
            rf.put(self.dest, t, z3.Concat(z0c, z1c))
        else:
            raise Unimplemented("Can currently only append arrays")

    def remap(self, m:RegRemapping) -> Instr:
        return Append(m.reg(self.dest), m.val(self.r0), m.val(self.r1))

class Assert(Instr):
    def __init__(self, e:LLExpr, msg:str):
        if e.bbtype() != BBB:
            raise UnexpectedException(f'Assertion condition must be bool, got {e.bbtype()}')
        self.e = e
        self.msg = msg

    def __repr__(self):
        return f'assert {self.e} "{self.msg}"'

    def exec(self, rf:RegFile):
        z = self.e.z3expr(rf, [])
        rf.check(z, self.msg)

    def remap(self, m:RegRemapping) -> Instr:
        return Assert(self.e.remap(m), self.msg)

class Precondition(Instr):
    def __init__(self, e:LLExpr):
        if e.bbtype() != BBB:
            raise UnexpectedException(f'Precondition should be bool, got {e.bbtype()}')
        self.e = e

    def __repr__(self):
        return f'precondition {self.e}'

    def exec(self, rf:RegFile):
        z = self.e.z3expr(rf, [])
        rf.assume(z)

    def remap(self, m:RegRemapping) -> Instr:
        return Precondition(self.e.remap(m))


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
