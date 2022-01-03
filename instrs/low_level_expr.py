from __future__ import annotations
import z3
from instrs.regfile import RegFile, Reg, RegRemapping
from instrs.misc import and_zs
from instrs.errors import UnexpectedException

class LLBool:
    # Overridden
    def z3expr(self, rf:RegFile) -> z3.BoolRef:
        raise UnexpectedException()

    # Overridden
    def remap(self, m:RegRemapping) -> LLBool:
        raise UnexpectedException()

    # Overridden
    def is_literal_true(self) -> bool:
        return False

class LLInt:
    # Overridden
    def z3expr(self, rf:RegFile) -> z3.ArithRef:
        raise UnexpectedException()

    # Overridden
    def remap(self, m:RegRemapping) -> LLInt:
        raise UnexpectedException()

class LLTrue(LLBool):
    def z3expr(self, rf:RegFile) -> z3.BoolRef:
        return z3.BoolVal(True)

    def remap(self, m:RegRemapping) -> LLTrue:
        return self

    def is_literal_true(self) -> bool:
        return True

    def __repr__(self) -> str:
        return 'true'

class LLIntVal(LLInt):
    def __init__(self, n:int):
        self.n = n

    def z3expr(self, rf:RegFile) -> z3.ArithRef:
        return z3.IntVal(self.n)

    def remap(self, m:RegRemapping) -> LLIntVal:
        return self

    def __repr__(self) -> str:
        return str(self.n)

class LLIntVar(LLInt):
    def __init__(self, name:str):
        self.name = name

    def z3expr(self, rf:RegFile) -> z3.ArithRef:
        return z3.Int(self.name)

    def remap(self, m:RegRemapping) -> LLIntVar:
        return self

    def __repr__(self) -> str:
        return self.name

class LLIntReg(LLInt):
    def __init__(self, r:Reg):
        self.r = r

    def z3expr(self, rf:RegFile) -> z3.ArithRef:
        result = rf.get(self.r)
        if isinstance(result, z3.ArithRef):
            return result
        else:
            raise UnexpectedException('Register {self.r} is not an int')

    def remap(self, m:RegRemapping) -> LLIntReg:
        return LLIntReg(m.reg(self.r))

    def __repr__(self) -> str:
        return str(self.r)

class LLLt(LLBool):
    def __init__(self, a:LLInt, b:LLInt):
        self.a = a
        self.b = b
 
    def z3expr(self, rf:RegFile) -> z3.BoolRef:
        return self.a.z3expr(rf) < self.b.z3expr(rf)

    def remap(self, m:RegRemapping) -> LLLt:
        return LLLt(self.a.remap(m), self.b.remap(m))

    def __repr__(self):
        return f'({self.a} < {self.b})'

class LLLe(LLBool):
    def __init__(self, a:LLInt, b:LLInt):
        self.a = a
        self.b = b

    def z3expr(self, rf:RegFile) -> z3.BoolRef:
        return self.a.z3expr(rf) <= self.b.z3expr(rf)

    def remap(self, m:RegRemapping) -> LLLe:
        return LLLe(self.a.remap(m), self.b.remap(m))

    def __repr__(self):
        return f'({self.a} <= {self.b})'

class LLAnd(LLBool):
    def __init__(self, *es:LLBool):
        self.es = es

    def z3expr(self, rf:RegFile) -> z3.BoolRef:
        return and_zs([e.z3expr(rf) for e in self.es])

    def remap(self, m:RegRemapping) -> LLAnd:
        return LLAnd(*[e.remap(m) for e in self.es])

    def __repr__(self):
        return 'and(' + ','.join((str(e) for e in self.es)) + ')'

class LLForAllInt(LLBool):
    def __init__(self, v:LLIntVar, e:LLBool):
        self.v = v
        self.e = e

    def z3expr(self, rf:RegFile) -> z3.BoolRef:
        return z3.ForAll([self.v.z3expr(rf)], self.e.z3expr(rf))

    def remap(self, m:RegRemapping) -> LLForAllInt:
        return LLForAllInt(self.v.remap(m), self.e.remap(m))

    def __repr__(self):
        return f'(forall {self.v}:{self.e})'
