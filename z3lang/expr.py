import z3
from z3lang.errors import *
from z3lang.types import *
from z3lang.misc import eq_zs, and_zs

class Expr:
    def __init__(self, typ, z):
        if not typ.accepts_sort(z.sort()):
            raise UnexpectedException(f'Sort mismatch in Expr.__init__ {typ} doesn\'t accept {sort}')

        self.typ = typ
        self.z = z

    def eq(self, other, negate=False):
        newtype = intersect(self.typ, other.typ)
        z = equality(self.z, other.z)
        if negate:
            return Expr(B, z3.Not(z))
        else:
            return Expr(B, z)

    def coerce_restrictions(self, typ):
        newtype = intersect(self.typ, typ)
        if newtype.accepts_sort(self.z.sort()):
            restrictions = newtype.z_restrictions(self.z)
            return Expr(newtype, self.z), restrictions
        else:
            raise TypeException(f'Sort {self.z.sort()} not acceptable for type {newtype}')
