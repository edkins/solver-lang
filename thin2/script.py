import z3

Type = z3.SortRef
Expr = z3.ExprRef
Range = tuple[int,int]

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

class Introduce(Statement):
    def __init__(self, xs:list[Var], exprs:list[Expr], unique:bool, r:Range):
        self.xs = tuple(xs)
        self.exprs = tuple(exprs)
        self.unique = unique
        self.r = r

    def validate_into(self, results: list[Statement]):
        results.append(Result(self.r, True))

class BareExpr(Statement):
    def __init__(self, expr:Expr, r:Range):
        self.expr = expr
        self.r = r

    def validate_into(self, results: list[Statement]):
        results.append(Result(self.r, True))
        
class Erroneous(Statement):
    def __init__(self, r:Range):
        self.r = r

    def validate_into(self, results: list[Statement]):
        results.append(Result(self.r, False))
        
class Script:
    def __init__(self, statements: list[Statement]):
        self.statements = statements

    def validate(self) -> list[Result]:
        results:list[Result] = []
        for statement in self.statements:
            statement.validate_into(results)
        return results
