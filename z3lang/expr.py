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

    def __repr__(self):
        return f'{self.z}:{self.typ}'

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
        z, restrictions = typ.coerce_restrictions(self.z)
        return Expr(typ, z), restrictions

    def len_restrictions(self):
        if self.z.sort() != self.typ.sort():
            raise UnexpectedException()
        z, restrictions = self.typ.len_restrictions(self.z)
        return Expr(Z, z), restrictions

    def lookup_restrictions(self, index):
        if self.z.sort() != self.typ.sort():
            raise UnexpectedException()
        if index.typ.sort() != z3.IntSort():
            raise UnexpectedException()
        z, typ, restrictions = self.typ.lookup_type_restrictions(self.z, index.z)
        return Expr(typ, z), restrictions
