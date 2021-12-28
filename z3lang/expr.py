import z3
from z3lang.errors import *
from z3lang.types import *
from z3lang.misc import eq_zs, and_zs

class Expr:
    def __init__(self, typ, z):
        if typ.sort() != z.sort():
            raise UnexpectedException(f'Sort mismatch in Expr.__init__ {typ.sort()} vs {sort}')

        self.typ = typ
        self.z = z

    def eq(self, other, negate=False):
        newtype = intersect(self.typ, other.typ)
        z0, r0 = newtype.coerce_restrictions(self.z)
        z1, r1 = newtype.coerce_restrictions(other.z)
        result = and_zs([z0 == z1] + r0 + r1)
        if negate:
            return Expr(B, z3.Not(result))
        else:
            return Expr(B, result)

    def coerce_restrictions(self, typ):
        newtype = intersect(self.typ, typ)
        z, restrictions = newtype.coerce_restrictions(self.z)
        return Expr(newtype, z), restrictions
