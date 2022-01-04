from __future__ import annotations
import z3
from instrs.regfile import RegFile, Reg, RegRemapping, Val
from instrs.misc import and_zs, or_zs
from instrs.errors import UnexpectedException
from instrs.backbone import *

class LLExpr:
    # Overridden
    def remap(self, m:RegRemapping) -> LLExpr:
        raise UnexpectedException()

    # Overridden
    def unused_var(self) -> int:
        raise UnexpectedException()

    # Overridden by LLBoolVal
    def is_literal_true(self) -> bool:
        return False

    # Overridden by LLBoolVal
    def is_literal_false(self) -> bool:
        return False

    # Overridden
    def z3expr(self, rf:RegFile, s:list[tuple[LLVar,z3.ExprRef]]) -> z3.ExprRef:
        raise UnexpectedException()

    def z3int(self, rf:RegFile, s:list[tuple[LLVar,z3.ExprRef]]) -> z3.ArithRef:
        result = self.z3expr(rf,s)
        if isinstance(result, z3.ArithRef):
            return result
        else:
            raise UnexpectedException(f'Expected ArithRef, got {type(result)}')

    def z3bool(self, rf:RegFile, s:list[tuple[LLVar,z3.ExprRef]]) -> z3.BoolRef:
        result = self.z3expr(rf,s)
        if isinstance(result, z3.BoolRef):
            return result
        else:
            raise UnexpectedException(f'Expected BoolRef, got {type(result)}')

    # Overridden
    def bbtype(self) -> BBType:
        raise UnexpectedException()

class LLBoolVal(LLExpr):
    def __init__(self, val:bool):
        self.val = val

    def z3expr(self, rf:RegFile, s:list[tuple[LLVar,z3.ExprRef]]) -> z3.BoolRef:
        return z3.BoolVal(self.val)

    def remap(self, m:RegRemapping) -> LLBoolVal:
        return self

    def is_literal_true(self) -> bool:
        return self.val

    def is_literal_false(self) -> bool:
        return not self.val

    def __repr__(self) -> str:
        return str(self.val)

    def unused_var(self) -> int:
        return 0

    def bbtype(self) -> BBType:
        return BBB

class LLIntVal(LLExpr):
    def __init__(self, n:int):
        self.n = n

    def z3expr(self, rf:RegFile, s:list[tuple[LLVar,z3.ExprRef]]) -> z3.ArithRef:
        return z3.IntVal(self.n)

    def remap(self, m:RegRemapping) -> LLIntVal:
        return self

    def __repr__(self) -> str:
        return str(self.n)

    def unused_var(self) -> int:
        return 0

    def bbtype(self) -> BBType:
        return BBZ

class LLVar(LLExpr):
    def __init__(self, number:int, bb:BBType):
        self.number = number
        self.bb = bb

    def z3expr(self, rf:RegFile, s:list[tuple[LLVar,z3.ExprRef]]) -> z3.ExprRef:
        for x,z in s:
            if self.number == x.number:
                if self.bb == x.bb:
                    return z
                else:
                    raise UnexpectedException(f'Substitution: var {self} has wrong type. Expecting {self.bb}, got {x.bb}')
        raise UnexpectedException(f'Substitution: unexpected var {self}')

    def remap(self, m:RegRemapping) -> LLVar:
        return self

    def __repr__(self) -> str:
        return f'.x{self.number}'

    def unused_var(self) -> int:
        return self.number + 1

    def bbtype(self) -> BBType:
        return self.bb

class LLReg(LLExpr):
    def __init__(self, r:Reg, bb:BBType):
        self.r = r
        self.bb = bb

    def z3expr(self, rf:RegFile, s:list[tuple[LLVar,z3.ExprRef]]) -> z3.ExprRef:
        z,t = rf.get(self.r)
        if t != self.bb:
            raise UnexpectedException(f'Expecting backbone type {self.bb}, got {t}')
        return z

    def remap(self, m:RegRemapping) -> LLReg:
        return LLReg(m.reg(self.r), self.bb)

    def __repr__(self) -> str:
        return str(self.r)

    def unused_var(self) -> int:
        return 0

    def bbtype(self) -> BBType:
        return self.bb

class LLLt(LLExpr):
    def __init__(self, a:LLExpr, b:LLExpr):
        self.a = a
        self.b = b
 
    def z3expr(self, rf:RegFile, s:list[tuple[LLVar,z3.ExprRef]]) -> z3.BoolRef:
        return self.a.z3int(rf,s) < self.b.z3int(rf,s)

    def remap(self, m:RegRemapping) -> LLLt:
        return LLLt(self.a.remap(m), self.b.remap(m))

    def __repr__(self):
        return f'({self.a} < {self.b})'

    def unused_var(self) -> int:
        return max(self.a.unused_var(), self.b.unused_var())

    def bbtype(self) -> BBType:
        return BBB

class LLLe(LLExpr):
    def __init__(self, a:LLExpr, b:LLExpr):
        self.a = a
        self.b = b

    def z3expr(self, rf:RegFile, s:list[tuple[LLVar,z3.ExprRef]]) -> z3.BoolRef:
        return self.a.z3int(rf,s) <= self.b.z3int(rf,s)

    def remap(self, m:RegRemapping) -> LLLe:
        return LLLe(self.a.remap(m), self.b.remap(m))

    def __repr__(self):
        return f'({self.a} <= {self.b})'

    def unused_var(self) -> int:
        return max(self.a.unused_var(), self.b.unused_var())

    def bbtype(self) -> BBType:
        return BBB

class LLAnd(LLExpr):
    def __init__(self, es:list[LLExpr]):
        self.es = tuple(es)

    def z3expr(self, rf:RegFile, s:list[tuple[LLVar,z3.ExprRef]]) -> z3.BoolRef:
        return and_zs([e.z3bool(rf,s) for e in self.es])

    def remap(self, m:RegRemapping) -> LLAnd:
        return LLAnd([e.remap(m) for e in self.es])

    def __repr__(self):
        return '(' + '&&'.join((str(e) for e in self.es)) + ')'

    def unused_var(self) -> int:
        return max(*[e.unused_var() for e in self.es])

    def bbtype(self) -> BBType:
        return BBB

class LLOr(LLExpr):
    def __init__(self, es:list[LLExpr]):
        self.es = tuple(es)

    def z3expr(self, rf:RegFile, s:list[tuple[LLVar,z3.ExprRef]]) -> z3.BoolRef:
        return or_zs([e.z3bool(rf,s) for e in self.es])

    def remap(self, m:RegRemapping) -> LLOr:
        return LLOr([e.remap(m) for e in self.es])

    def __repr__(self):
        return '(' + '||'.join((str(e) for e in self.es)) + ')'

    def unused_var(self) -> int:
        return max(*[e.unused_var() for e in self.es])

    def bbtype(self) -> BBType:
        return BBB

class LLImplies(LLExpr):
    def __init__(self, a:LLExpr, b:LLExpr):
        self.a = a
        self.b = b

    def z3expr(self, rf:RegFile, s:list[tuple[LLVar,z3.ExprRef]]) -> z3.BoolRef:
        return z3.Implies(self.a.z3bool(rf,s), self.b.z3bool(rf,s))

    def remap(self, m:RegRemapping) -> LLImplies:
        return LLImplies(self.a.remap(m), self.b.remap(m))

    def __repr__(self):
        return f'({self.a} -> {self.b})'

    def unused_var(self) -> int:
        return max(self.a.unused_var(), self.b.unused_var())

    def bbtype(self) -> BBType:
        return BBB

class LLForAll(LLExpr):
    def __init__(self, v:LLVar, e:LLExpr):
        self.v = v
        self.e = e

    def z3expr(self, rf:RegFile, s:list[tuple[LLVar,z3.ExprRef]]) -> z3.BoolRef:
        for v,z in s:
            if v == self.v:
                raise UnexpectedException('Cannot substitute bound var {self.v} in forall')

        s1 = s + [(self.v, z3.Const(f'.x{self.v.number}', self.v.bbtype().z3sort()))]
        return z3.ForAll([self.v.z3expr(rf,s1)], self.e.z3expr(rf,s1))

    def remap(self, m:RegRemapping) -> LLForAll:
        return LLForAll(self.v.remap(m), self.e.remap(m))

    def __repr__(self):
        return f'(forall {self.v}:{self.e})'

    def unused_var(self) -> int:
        return max(self.v.unused_var(), self.e.unused_var())

    def bbtype(self) -> BBType:
        return BBB

class LLTupleMember(LLExpr):
    def __init__(self, e:LLExpr, i:int):
        self.e = e
        self.i = i

    def z3expr(self, rf:RegFile, s:list[tuple[LLVar,z3.ExprRef]]) -> z3.ExprRef:
        bb = self.e.bbtype()
        if isinstance(bb, BBTuple):
            return bb.z3member(self.i, self.e.z3expr(rf,s))
        else:
            raise UnexpectedException(f'Expecting BBTuple, got {bb}')

    def remap(self, m:RegRemapping) -> LLTupleMember:
        return LLTupleMember(self.e.remap(m), self.i)

    def unused_var(self) -> int:
        return self.e.unused_var()

    def bbtype(self) -> BBType:
        bb = self.e.bbtype()
        if isinstance(bb, BBTuple):
            return bb.members[self.i]
        else:
            raise UnexpectedException(f'Expecting BBTuple, got {bb}')

class LLArrayElement(LLExpr):
    def __init__(self, a:LLExpr, b:LLExpr):
        self.a = a
        self.b = b

    def z3expr(self, rf:RegFile, s:list[tuple[LLVar,z3.ExprRef]]) -> z3.ExprRef:
        seq = self.a.z3expr(rf,s)
        if isinstance(seq, z3.SeqRef):
            return seq[self.b.z3expr(rf,s)]
        else:
            raise UnexpectedException(f'Expecting SeqRef, got {type(seq)}')

    def remap(self, m:RegRemapping) -> LLArrayElement:
        return LLArrayElement(self.a.remap(m), self.b.remap(m))

    def unused_var(self) -> int:
        return max(self.a.unused_var(), self.b.unused_var())

    def bbtype(self) -> BBType:
        bb = self.a.bbtype()
        if isinstance(bb, BBArray):
            return bb.element
        else:
            raise UnexpectedException(f'Expecting BBArray, got {bb}')

class LLArrayLength(LLExpr):
    def __init__(self, e:LLExpr):
        self.e = e

    def z3expr(self, rf:RegFile, s:list[tuple[LLVar,z3.ExprRef]]) -> z3.ExprRef:
        return z3.Length(self.e.z3expr(rf,s))

    def remap(self, m:RegRemapping) -> LLArrayLength:
        return LLArrayLength(self.e.remap(m))

    def unused_var(self) -> int:
        return self.e.unused_var()

    def bbtype(self) -> BBType:
        return BBZ

class LLUnion(LLExpr):
    def __init__(self, u:LLExpr, xs:list[LLVar], opts:list[LLExpr]):
        if len(xs) != len(opts):
            raise UnexpectedException(f'Got {len(xs)} vars and {len(opts)} options')
        if len(opts) == 0:
            raise UnexpectedException('Expecting options, got 0')
        self.u = u
        self.xs = tuple(xs)
        self.opts = tuple(opts)

    def z3expr(self, rf:RegFile, s:list[tuple[LLVar,z3.ExprRef]]) -> z3.ExprRef:
        bb = self.u.bbtype()
        if not isinstance(bb, BBUnion):
            raise UnexpectedException(f'Expecting union type, got {bb}')

        for x in self.xs:
            for y,z in s:
                if x.number == y.number:
                    raise UnexpectedException(f'Duplicated substitution variable {x}')

        result = None
        uz = self.u.z3expr(rf, s)
        for i in range(len(self.opts)):
            s1 = s + [(self.xs[i], bb.z3accessor(i, uz))]
            result_opt = self.opts[i].z3expr(rf, s1)
            if isinstance(result, z3.ExprRef):
                result = z3.If(bb.z3recognizer(i, uz), result_opt, result)
            else:
                result = result_opt

        if isinstance(result, z3.ExprRef):
            return result
        else:
            raise UnexpectedException()

    def remap(self, m:RegRemapping) -> LLUnion:
        return LLUnion(self.u.remap(m), [x.remap(m) for x in self.xs], [o.remap(m) for o in self.opts])

    def unused_var(self) -> int:
        return max(self.u.unused_var(), *[x.unused_var() for x in self.xs], *[o.unused_var() for o in self.opts]) 

    def bbtype(self) -> BBType:
        result = self.opts[0].bbtype()
        for o in self.opts[1:]:
            if o.bbtype() != result:
                raise UnexpectedException(f'Conflicting union result types: {result} vs {o.bbtype()}')
        return result

class LLCoerce(LLExpr):
    def __init__(self, bb:BBType, e:LLExpr):
        self.bb = bb
        self.e = e

    def z3expr(self, rf:RegFile, s:list[tuple[LLVar,z3.ExprRef]]) -> z3.ExprRef:
        z0 = self.e.z3expr(rf, s)
        z, c = rf.coerce_check(self.bb, self.e.bbtype(), z0)
        return z

    def remap(self, m:RegRemapping) -> LLCoerce:
        return LLCoerce(self.bb, self.e.remap(m))

    def unused_var(self) -> int:
        return self.e.unused_var()

    def bbtype(self) -> BBType:
        return self.bb

def ll_and(xs:list[LLExpr]) -> LLExpr:
    xs_squashed:list[LLExpr] = []
    for x in xs:
        if x.is_literal_true():
            pass
        elif isinstance(x, LLAnd):
            xs_squashed += x.es
        else:
            xs_squashed.append(x)

    if len(xs_squashed) == 0:
        return LLBoolVal(True)
    elif len(xs_squashed) == 1:
        return xs_squashed[0]
    else:
        return LLAnd(xs_squashed)

def ll_or(xs:list[LLExpr]) -> LLExpr:
    xs_squashed:list[LLExpr] = []
    for x in xs:
        if x.is_literal_false():
            pass
        elif isinstance(x, LLOr):
            xs_squashed += x.es
        else:
            xs_squashed.append(x)

    if len(xs_squashed) == 0:
        return LLBoolVal(False)
    elif len(xs_squashed) == 1:
        return xs_squashed[0]
    else:
        return LLOr(xs_squashed)

def ll_implies(a:LLExpr, b:LLExpr) -> LLExpr:
    if b.is_literal_true():
        return LLBoolVal(True)
    else:
        return LLImplies(a, b)

def ll_value(v:Val, bb:BBType) -> LLExpr:
    if isinstance(v, bool):
        if bb == BBB:
            return LLBoolVal(v)
        else:
            raise UnexpectedException(f'Expecting bool type, got {bb}')
    elif isinstance(v, int):
        if bb == BBZ:
            return LLIntVal(v)
        else:
            raise UnexpectedException(f'Expecting int type, got {bb}')
    elif isinstance(v, Reg):
        return LLReg(v, bb)
    else:
        raise UnexpectedException()
