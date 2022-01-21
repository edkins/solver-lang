import z3
from thin2.errors import *

Type = z3.SortRef
Expr = z3.ExprRef
Range = tuple[int,int]

def and_zs(zs: list[Expr]) -> Expr:
    if len(zs) == 0:
        return z3.BoolVal(True)
    elif len(zs) == 1:
        return zs[0]
    else:
        return z3.And(*zs)

    
def validity(solver: z3.Solver, stmt: Expr) -> bool:
    solver.push()
    try:
        solver.add(z3.Not(stmt))
        return solver.check() == z3.unsat
    finally:
        solver.pop()
        
    
class Result:
    def __init__(self, r:Range, ok:bool):
        self.start = r[0]
        self.end = r[1]
        self.ok = ok

    def __repr__(self):
        return f'range {self.start} {self.end} {"ok" if self.ok else "bad"}\n'

class Statement:
    pass

class Var:
    def __init__(self, name: str, typ: Type):
        self.name = name
        self.typ = typ

    def as_expr(self) -> Expr:
        return z3.Const(self.name, self.typ)

    def alt_expr(self) -> Expr:
        return z3.Const(self.name + "'", self.typ)

class Introduce(Statement):
    def __init__(self, xs:list[Var], exprs:list[Expr], unique:bool, r:Range):
        if len(xs) == 0:
            raise UnexpectedException()
        self.xs = tuple(xs)
        self.exprs = tuple(exprs)
        self.unique = unique
        self.r = r

    def validate_into(self, solver: z3.Solver, results: list[Statement]):
        anded = and_zs(self.exprs)
        xs = [x.as_expr() for x in self.xs]
        stmt = z3.Exists(xs, anded)
        valid = validity(solver, stmt)
        if self.unique:
            xs2 = [x.alt_expr() for x in self.xs]
            pairs = list(zip(xs, xs2))
            anded2 = z3.substitute(anded, pairs)
            xs_eq_xs2 = and_zs([x == x2 for (x,x2) in pairs])
            stmt2 = z3.ForAll(xs + xs2, z3.Implies(z3.And(anded, anded2), xs_eq_xs2))
            valid = valid and validity(solver, stmt2)
        if valid:
            for expr in self.exprs:
                solver.add(expr)
        results.append(Result(self.r, valid))

class BareExpr(Statement):
    def __init__(self, expr:Expr, r:Range):
        self.expr = expr
        self.r = r

    def validate_into(self, solver: z3.Solver, results: list[Statement]):
        valid = validity(solver, self.expr)
        results.append(Result(self.r, valid))
        
class Erroneous(Statement):
    def __init__(self, r:Range):
        self.r = r

    def validate_into(self, solver: z3.Solver, results: list[Statement]):
        results.append(Result(self.r, False))
        
class Script:
    def __init__(self, statements: list[Statement]):
        self.statements = statements

    def validate(self) -> list[Result]:
        results:list[Result] = []
        solver = z3.Solver()
        for statement in self.statements:
            statement.validate_into(solver, results)
        return results
