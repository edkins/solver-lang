from typing import Union, Callable
import z3
from instrs.backbone import *
from instrs.misc import and_zs

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
        result, check = self.coerce_check(dt, t, z)
        self.check(check, "coerce")
        return result

    def coerce_check(self, dt:BBType, t:BBType, z:z3.ExprRef) -> tuple[z3.ExprRef, z3.BoolRef]:
        if t == dt:
            return z, z3.BoolVal(True)
        else:
            t_opts = t.get_options()
            result = None
            check = z3.BoolVal(True)
            for i in range(len(t_opts)):
                try:
                    t_opt = t_opts[i]
                    z_opt = t.z3accessor(i,z)
                    if t_opt == dt:
                        result_opt = z_opt
                        check_opt = z3.BoolVal(True)
                    elif isinstance(dt, BBArray):
                        result_opt, check_opt = self.coerce_array(dt, t_opt, z_opt)
                    elif isinstance(dt, BBTuple):
                        result_opt, check_opt = self.coerce_tuple(dt, t_opt, z_opt)
                    elif isinstance(dt, BBUnion):
                        result_opt, check_opt = self.coerce_union(dt, t_opt, z_opt)
                    else:
                        raise TypeException(f'Cannot coerce {t_opt} to {dt}')

                    if result == None:
                        result = result_opt
                    else:
                        result = z3.If(t.z3recognizer(i,z), result_opt, result)
                    check = z3.If(t.z3recognizer(i,z), check_opt, check)
                except TypeException as e:
                    try:
                        check = z3.And(z3.Not(t.z3recognizer(i,z)), check)
                    except AssertionException as e1:
                        raise e
            if isinstance(result, z3.ExprRef) and isinstance(check, z3.BoolRef):
                return result, check
            else:
                raise TypeException('No result')

    def coerce_array(self, dt:BBArray, t:BBType, z:z3.ExprRef) -> tuple[z3.ExprRef,z3.BoolRef]:
        if isinstance(t, BBArray):
            x = t.z3var('.x')
            if not isinstance(x, z3.SeqRef):
                raise UnexpectedException(f'Expected SeqRef at this point, got {type(x)}')
            zc,cc = self.coerce_check(dt.element, t.element, x[0])

            name = 'coerce[{dt},{t}]'
            f = z3.RecFunction(name, t.z3sort(), dt.z3sort())
            z3.RecAddDefinition(f, [x], z3.If(
                x == z3.Empty(t.z3sort()),
                z3.Empty(dt.z3sort()),
                z3.Concat(z3.Unit(zc), f(z3.SubSeq(x, 1, z3.Length(x)-1)))))

            cname = 'coerce_check[{dt},{t}]'
            cf = z3.RecFunction(cname, t.z3sort(), z3.BoolSort())
            z3.RecAddDefinition(cf, [x], z3.If(
                x == z3.Empty(t.z3sort()),
                z3.BoolVal(True),
                z3.And(cc, cf(z3.SubSeq(x, 1, z3.Length(x)-1)))))
            return f(z), cf(z)
        elif isinstance(t, BBTuple):
            zs = []
            cs = []
            for i in range(t.tuple_len()):
                zc,cc = self.coerce_check(dt.element, t.members[i], t.z3member(i,z))
                zs.append(zc)
                cs.append(cc)
            return sequence_zs(dt.z3sort(), zs), and_zs(cs)
        else:
            raise TypeException('Cannot coerce {t} to {dt}')

    def coerce_tuple(self, dt:BBTuple, t:BBType, z:z3.ExprRef) -> tuple[z3.ExprRef,z3.BoolRef]:
        if isinstance(t, BBTuple):
            if t.tuple_len() != dt.tuple_len():
                raise TypeException(f'Cannot coerce {t} to {dt} (tuples are different lengths)')
            zs = []
            cs = []
            for i in range(t.tuple_len()):
                zc,cc = self.coerce_check(dt.members[i], t.members[i], t.z3member(i,z))
                zs.append(zc)
                cs.append(cc)
            return dt.z3tuple(zs), and_zs(cs)
        elif isinstance(t, BBArray):
            if not isinstance(z, z3.SeqRef):
                raise UnexpectedException(f'Expecting SeqRef, got {type(z)}')
            cs = [z3.Length(z) == z3.IntVal(dt.tuple_len())]
            zs = []
            for i in range(dt.tuple_len()):
                zc, cc = self.coerce_check(dt.members[i], t.element, z[i])
                zs.append(zc)
                cs.append(cc)
            return dt.z3tuple(zs), and_zs(cs)
        else:
            raise TypeException(f'Cannot coerce {t} to {self}')

    def coerce_union(self, dt:BBUnion, t:BBType, z:z3.ExprRef) -> tuple[z3.ExprRef,z3.BoolRef]:
        opts = dt.get_options()
        for i in range(len(opts)):
            try:
                zc,cc = self.coerce_check(opts[i], t, z)
                return dt.z3constructor(i, zc), cc
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

