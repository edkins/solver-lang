import z3
from z3lang.errors import *
from z3lang.types import *
from z3lang.misc import eq_zs, and_zs

class Expr:
    def __init__(self, typ, z):
        sort = typ.sort()
        if z.sort() != sort:
            raise UnexpectedException(f'Sort mismatch in Expr.__init__ {z.sort()} vs {sort}')

        self.typ = typ
        self.z = z
        
    def eq(self, other, negate=False):
        value = z3.BoolVal(False)
        if self.typ.interp == other.typ.interp and self.typ.sorts == other.typ.sorts:
            value = eq_zs(self.zs, other.zs)
        elif isinstance(self.typ.interp, TupleInterp) and isinstance(other.typ.interp, ArrayInterp):
            n = len(self.typ.interp.interps)
            zs = [n == z3.Length(other.zs[0])]
            sort = self.typ.sorts[0]
            for i in range(n):
                zs.append(sort.accessor(0,i)(self.zs[0]) == other.zs[0][z3.IntVal(i)])
            value = and_zs(zs)
            print(value)
        elif isinstance(self.typ.interp, ArrayInterp) and isinstance(other.typ.interp, TupleInterp):
            return other.eq(self)
        if negate:
            value = z3.Not(value)
        return Expr(B, value)
