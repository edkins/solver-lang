from typing import Union, Optional
import lark
import z3
from thin2.grammar import grammar
from thin2.errors import UnexpectedException
from thin2.script import *

Ast = Union[str,lark.Tree]
Env = dict[str,Var]

def parse_expr(ast: Ast, env: Env) -> tuple[Optional[Expr],Range]:
    if isinstance(ast, lark.Tree):
        raise UnimplementedException()
    elif isinstance(ast, lark.Token):
        r = (ast.start_pos, ast.end_pos)
        if ast.type == 'CNAME':
            if ast.value in env:
                return env[ast.value].as_expr(), r
            else:
                return None, r
        elif ast.type == 'INT':
            return z3.IntVal(int(ast.value)), r
        elif ast.type == 'TRUE':
            return z3.BoolVal(True), r
        elif ast.type == 'FALSE':
            return z3.BoolVal(False), r

def parse_type(ast: Ast) -> Type:
    if isinstance(ast, lark.Tree):
        if ast.data == 'inttype':
            return z3.IntSort()
        elif ast.data == 'booltype':
            return z3.BoolSort()
    raise UnexpectedException()

def parse_nametype(ast: Ast) -> tuple[Var,Range]:
    if isinstance(ast, lark.Tree) and ast.data == 'nametype':
        name, _colon, typ = ast.children
        return Var(name.value, parse_type(typ)), (name.start_pos, name.end_pos)
    raise UnexpectedException()
        
def parse_statement(ast: Ast, env:Env) -> tuple[Statement]:
    if isinstance(ast, lark.Tree):
        if ast.data == 'def':
            _def, nametypes, _open, exprs, _close = ast.children
            xs:list[Var] = []
            for nametype in nametypes.children:
                x,r = parse_nametype(nametype)
                if x.name in env:
                    return Erroneous(r)
                env[x.name] = x
            es:list[Expr] = []
            for ch in exprs.children:
                e,r = parse_expr(ch, env)
                if isinstance(e,Expr):
                    es.append(e)
                else:
                    return Erroneous(r)

            return Def(xs, es, (_def.start_pos, _close.end_pos))
    raise UnexpectedException()

def parse_script(ast: Ast) -> Script:
    env = dict()
    statements = []
    for child in ast.children:
        statements.append(parse_statement(child, env))
    return Script(statements)
