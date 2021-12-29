from typing import Any

class Expr:
    def __repr__(self):
        result = str(self.f)
        if len(self.xs) > 0:
            result += str(self.xs)
        if self.typ != None:
            result += f':{self.typ}'
        return result

    def __eq__(self, other):
        return isinstance(other, Expr) and self.f == other.f and self.xs == other.xs and self.typ == other.typ

class Int(Expr):
    def __init__(self, f:int):
        self.f = f
        self.xs = []
        self.typ = None

class Var(Expr):
    def __init__(self, f:str):
        self.f = f
        self.xs = []
        self.typ = None

class Call(Expr):
    def __init__(self, f:str, *xs:Any):
        self.f = f
        self.xs = list(xs)
        self.typ = None

class Builtin(Expr):
    def __init__(self, f:str, *xs:Any):
        self.f = f
        self.xs = list(xs)
        self.typ = None

class Type:
    def __init__(self, name:str, type_args:list, expr_args:list[Expr]):
        self.name = name
        self.type_args = type_args
        self.expr_args = expr_args

    def __repr__(self):
        result = f'{self.name}{"".join(" "+str(a) for a in self.type_args)}'
        if len(self.expr_args) > 0:
            result += str(self.expr_args)
        return result

    def __eq__(self, other):
        return isinstance(other, Type) and self.name == other.name and self.type_args == other.type_args and self.expr_args == other.expr_args

class Statement:
    pass

class Def(Statement):
    def __init__(self, f:str, args:list[tuple[str,Type]], ret:Type, body:list[Statement]):
        self.f = f
        self.args = args
        self.ret = ret
        self.body = body

    def __repr__(self):
        result = f'fn {self.f}('
        result += ','.join((f'x:{typ}' for x,typ in self.args))
        result += f') -> {self.ret} {{ {self.body} }}'
        return result

class Assign(Statement):
    def __init__(self, x:str, e:Expr):
        self.x = x
        self.e = e
        self.typ = None

    def __repr__(self):
        result = f'{self.x} = {self.e}'
        if self.typ != None:
            result += f':{self.typ}'
        return result

class Assert(Statement):
    def __init__(self, e:Expr):
        self.e = e

    def __repr__(self):
        return f'assert {self.e}'

class Return(Statement):
    def __init__(self, e:Expr):
        self.e = e
        self.typ = None

    def __repr__(self):
        result = f'return {self.e}'
        if self.typ != None:
            result += f':{self.typ}'
        return result
