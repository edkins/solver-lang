import lark
from typing import Union
from instrs.instr import *

Ast = Union[str,lark.Tree]

def token_value(ast: Ast) -> str:
    if isinstance(ast, lark.Token):
        return ast.value
    else:
        raise UnexpectedException()

def binop(name:str, dest:Reg, v0:Val, v1:Val) -> Instr:
    if name == 'eq':
        return Eq(dest, v0, v1, ne=False)
    elif name == 'ne':
        return Eq(dest, v0, v1, ne=True)
    elif name == 'lt':
        return Lt(dest, v0, v1)
    elif name == 'le':
        return Le(dest, v0, v1)
    elif name == 'gt':
        return Lt(dest, v1, v0)
    elif name == 'ge':
        return Le(dest, v1, v0)
    elif name == 'add':
        return Add(dest, v0, v1)
    elif name == 'sub':
        return Sub(dest, v0, v1)
    elif name == 'mul':
        return Mul(dest, v0, v1)
    elif name == 'lookup':
        return Lookup(dest, v0, v1)
    else:
        raise Unimplemented(f'Binop {name}')

def unary(name:str, dest:Reg, v:Val) -> Instr:
    if name == 'neg':
        return Neg(dest, v)
    elif name == 'len':
        return Len(dest, v)
    else:
        raise Unimplemented(f'Unary {name}')

class InstrBuilder:
    def __init__(self):
        self.tempnum = 0
        self.instrs:list[Instr] = []

    def next_temporary(self) -> Reg:
        result = Reg(f't{self.tempnum}')
        self.tempnum += 1
        return result

    def visit_expr(self, ast: Ast) -> Val:
        if isinstance(ast, lark.Token):
            if ast.type == 'CNAME':
                return Reg(ast.value)
            elif ast.type == 'INT':
                return int(ast.value)
            elif ast.type == 'TRUE':
                return True
            elif ast.type == 'FALSE':
                return False
            else:
                raise Unimplemented(f'Unimplemented expression token {ast.type}')
        elif isinstance(ast, lark.Tree):
            if ast.data in ['eq','ne','lt','le','gt','ge','add','sub','mul','lookup']:
                e0, e1 = ast.children
                v0 = self.visit_expr(e0)
                v1 = self.visit_expr(e1)
                dest = self.next_temporary()
                self.instrs.append(binop(ast.data, dest, v0, v1))
                return dest
            elif ast.data in ['neg','len']:
                e0, = ast.children
                v0 = self.visit_expr(e0)
                dest = self.next_temporary()
                self.instrs.append(unary(ast.data, dest, v0))
                return dest
            elif ast.data == 'call':
                f = token_value(ast.children[0])
                vs = []
                for e in ast.children[1:]:
                    vs.append(self.visit_expr(e))
                raise Unimplemented()
            elif ast.data == 'listing':
                vs = []
                for e in ast.children:
                    vs.append(self.visit_expr(e))
                dest = self.next_temporary()
                self.instrs.append(Listing(dest, vs))
                return dest
            else:
                raise Unimplemented(f'Unimplemented expression tree {ast.data}')
        else:
            raise Unimplemented('Unimplemented expression non-tree non-token')

