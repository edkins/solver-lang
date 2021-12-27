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

    def to_common_z(self):
        return self.typ.to_common(self.z)

    def eq(self, other, negate=False):
        if negate:
            return Expr(B, self.to_common_z() != other.to_common_z())
        else:
            return Expr(B, self.to_common_z() == other.to_common_z())

    def coerce_restrictions(self, typ):
        z, restrictions = typ.from_common(self.typ.to_common(self.z))
        return Expr(typ, z), restrictions
