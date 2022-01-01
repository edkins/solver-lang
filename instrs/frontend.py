import lark
from typing import Union, Optional
from instrs.backbone import *
from instrs.instr import *
from instrs.errors import *

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
    elif name == 'arr':
        return Arr(dest, v)
    else:
        raise Unimplemented(f'Unary {name}')

class InstrBuilder:
    def __init__(self, is_repl:bool):
        self.tempnum = 0
        self.instrs:list[Instr] = []
        self.is_repl = is_repl

    def rollback(self, pos:int):
        if pos >= 0 and pos <= len(self.instrs):
            self.instrs = self.instrs[:pos]
        else:
            raise UnexpectedException('pos out of range')

    def target_or_next_temporary(self, target:Optional[Reg]) -> Reg:
        if isinstance(target, Reg):
            return target
        result = Reg(f'.t{self.tempnum}')
        self.tempnum += 1
        return result

    def visit_type(self, ast: Ast) -> BBType:
        if isinstance(ast, lark.Token):
            if ast.value == 'int':
                return BBZ
            elif ast.value == 'bool':
                return BBB
            else:
                raise Unimplemented(f'Unimplemented type token {ast.value}')
        elif isinstance(ast, lark.Tree):
            if ast.data == 'range':
                return BBZ
            elif ast.data == 'tuple':
                ts = [self.visit_type(e) for e in ast.children]
                return BBTuple(ts)
            elif ast.data == 'array':
                t = self.visit_type(ast.children[0])
                return BBArray(t)
            elif ast.data == 'union':
                ts = [self.visit_type(e) for e in ast.children]
                return flat_union(ts)
            else:
                raise Unimplemented(f'Unimplemented type tree {ast.data}')
        else:
            raise Unimplemented('Unimplemented type non-tree non-token')


    def visit_args(self, args: list[Ast]):
        for arg in args:
            if isinstance(arg, lark.Tree):
                x, t = arg.children
                name = token_value(x)
                typ = self.visit_type(t)
                self.emit(Arg(Reg(name), typ))
            else:
                raise Unimplemented('Unimplemented arg non-tree')

    def visit_statement(self, ast: Ast) -> Optional[Val]:
        if isinstance(ast, lark.Tree):
            if ast.data == 'assign':
                x, e = ast.children
                name = token_value(x)
                self.visit_expr(e, Reg(name))
                return Reg(name)
            elif ast.data == 'assert':
                e, = ast.children
                val = self.visit_expr(e, None)
                self.emit(Assert(val))
                return None
            elif ast.data == 'pushfn':
                f = token_value(ast.children[0])
                args = ast.children[1:-1]
                ret = ast.children[-1]
                self.emit(Push())
                self.visit_args(args)
                self.emit(RetType(self.visit_type(ret)))
                return None
            elif ast.data == 'pop':
                self.emit(Pop())
                return None
            elif ast.data == 'return':
                e, = ast.children
                val = self.visit_expr(e, None)
                self.emit(Ret(val))
                return None
            elif ast.data == 'sample':
                if not self.is_repl:
                    raise ModeException('Bare expression only allowed in repl mode')
                e, = ast.children
                val = self.visit_expr(e, None)
                return val
            else:
                raise Unimplemented('Unimplemented statement tree {ast.data}')
        else:
            raise Unimplemented('Unimplemented statement non-tree')

    
    def emit(self, instr:Instr):
        #print(instr)
        self.instrs.append(instr)


    def visit_expr(self, ast: Ast, target:Optional[Reg]) -> Val:
        if isinstance(ast, lark.Token):
            if ast.type == 'CNAME':
                result:Val = Reg(ast.value)
            elif ast.type == 'INT':
                result = int(ast.value)
            elif ast.type == 'TRUE':
                result = True
            elif ast.type == 'FALSE':
                result = False
            else:
                raise Unimplemented(f'Unimplemented expression token {ast.type}')

            if isinstance(target, Reg):
                self.emit(Mov(target, result))
                return target
            else:
                return result
        elif isinstance(ast, lark.Tree):
            if ast.data in ['eq','ne','lt','le','gt','ge','add','sub','mul','lookup']:
                e0, e1 = ast.children
                v0 = self.visit_expr(e0,None)
                v1 = self.visit_expr(e1,None)
                dest = self.target_or_next_temporary(target)
                self.emit(binop(ast.data, dest, v0, v1))
                return dest
            elif ast.data in ['neg','len','arr']:
                e0, = ast.children
                v0 = self.visit_expr(e0,None)
                dest = self.target_or_next_temporary(target)
                self.emit(unary(ast.data, dest, v0))
                return dest
            elif ast.data == 'call':
                f = token_value(ast.children[0])
                vs = []
                for e in ast.children[1:]:
                    vs.append(self.visit_expr(e,None))
                raise Unimplemented()
            elif ast.data == 'listing':
                vs = []
                for e in ast.children:
                    vs.append(self.visit_expr(e,None))
                dest = self.target_or_next_temporary(target)
                self.emit(Listing(dest, vs))
                return dest
            else:
                raise Unimplemented(f'Unimplemented expression tree {ast.data}')
        else:
            raise Unimplemented('Unimplemented expression non-tree non-token')

