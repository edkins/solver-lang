from z3lang.errors import *

class Expr:
    def __init__(self, typ, zs):
        sorts = self.typ.sorts()
        if len(sorts) != len(zs):
            raise UnexpectedException(f'Element count mismatch in Expr.__init__ {len(sots)} vs {len(zs)}')
        for sort,z in zip(sorts,zs):
            if z.sort() != sort:
                raise UnexpectedException(f'Sort mismatch in Expr.__init__ {z.sort()} vs {sort}')

        self.typ = typ
        self.zs = zs
        
