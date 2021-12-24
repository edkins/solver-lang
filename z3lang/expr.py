import z3
from z3lang.errors import *
from z3lang.types import *
from z3lang.misc import eq_zs

class Expr:
    def __init__(self, typ, *zs):
        sorts = typ.sorts
        if len(sorts) != len(zs):
            raise UnexpectedException(f'Element count mismatch in Expr.__init__ {len(sots)} vs {len(zs)}')
        for sort,z in zip(sorts,zs):
            if z.sort() != sort:
                raise UnexpectedException(f'Sort mismatch in Expr.__init__ {z.sort()} vs {sort}')

        self.typ = typ
        self.zs = zs
        
    def eq(self, other, negate=False):
        value = z3.BoolVal(False)
        if self.typ == B:
            if other.typ == B:
                value = eq_zs(self.zs, other.zs)
        elif self.typ == Z:
            if other.typ == Z:
                value = eq_zs(self.zs, other.zs)
        else:
            raise Unimplemented(f'Unable to compute equality for type {self.typ}')

        if negate:
            value = z3.Not(value)
        return Expr(B, value)

    def coerce(self, typ):
        if self.typ == typ:
            return self
        raise TypeException(f'Unable to coerce {self.typ} to {typ}')
