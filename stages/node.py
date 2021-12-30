from __future__ import annotations
from typing import Any, Union, Optional

class Expr:
    def __init__(self):
        self.xs:list[Expr] = []
        self.typ:Optional[Type] = None

    def __repr__(self):
        result = str(self.f)
        if len(self.xs) > 0:
            result += str(self.xs)
        if self.typ != None:
            result += f':{self.typ}'
        return result

    def __eq__(self, other):
        return isinstance(other, Expr) and self.f == other.f and self.xs == other.xs and self.typ == other.typ

    # Overridden
    def clone(self):
        raise Unimplemented()

class Int(Expr):
    def __init__(self, f:int):
        self.f = f
        self.xs:list[Expr] = []
        self.typ = None

    def clone(self):
        result = Int(self.f)
        result.typ = self.typ.clone()
        return result

class Var(Expr):
    def __init__(self, f:str):
        self.f = f
        self.xs:list[Expr] = []
        self.typ = None

    def clone(self):
        result = Int(self.f)
        result.typ = self.typ.clone()
        return result

class Call(Expr):
    def __init__(self, f:str, *xs:Expr):
        self.f = f
        self.xs = list(xs)
        self.typ = None

    def clone(self):
        result = Call(f, [x.clone() for x in self.xs])
        result.typ = self.typ.clone()
        return result

class Builtin(Expr):
    def __init__(self, f:str, *xs:Expr):
        self.f = f
        self.xs = list(xs)
        self.typ = None

    def clone(self):
        result = Call(f, [x.clone() for x in self.xs])
        result.typ = self.typ.clone()
        return result

class Type:
    def __init__(self, name:str, type_args:list[Type], expr_args:list[Expr]):
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

    def clone(self):
        return Type(self.name, [t.clone() for t in self.type_args], [e.clone() for e in self.expr_args])

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
        self.typ:Optional[Type] = None

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
        self.typ:Optional[Type] = None

    def __repr__(self):
        result = f'return {self.e}'
        if self.typ != None:
            result += f':{self.typ}'
        return result
