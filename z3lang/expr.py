import z3
from z3lang.errors import *
from z3lang.types import *
from z3lang.misc import eq_zs

class Expr:
    def __init__(self, typ, *zs):
        sorts = typ.sorts
        if len(sorts) != len(zs):
            raise UnexpectedException(f'Element count mismatch in Expr.__init__ {len(sorts)} vs {len(zs)}')
        for sort,z in zip(sorts,zs):
            if z.sort() != sort:
                raise UnexpectedException(f'Sort mismatch in Expr.__init__ {z.sort()} vs {sort}')

        self.typ = typ
        self.zs = zs
        
    def eq(self, other, negate=False):
        value = z3.BoolVal(False)
        if self.typ.interp == other.typ.interp:
            if self.typ.sorts == other.typ.sorts:
                value = eq_zs(self.zs, other.zs)

        if negate:
            value = z3.Not(value)
        return Expr(B, value)
