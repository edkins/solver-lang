from typing import Union, Optional
import lark
import z3
from thin2.grammar import grammar
from thin2.errors import UnexpectedException, UnimplementedException
from thin2.script import *

Ast = Union[str,lark.Tree]
Env = dict[str,Var]

def binop(typ:str, a:Expr, b:Expr) -> Optional[Expr]:
    if typ == 'eq':
        if a.sort() == b.sort():
            return a == b
        else:
            return None
    elif typ == 'ne':
        if a.sort() == b.sort():
            return a != b
        else:
            return None
    elif typ == 'lt':
        if a.sort() == z3.IntSort() and b.sort() == z3.IntSort():
            return a < b
        else:
            return None
    elif typ == 'le':
        if a.sort() == z3.IntSort() and b.sort() == z3.IntSort():
            return a <= b
        else:
            return None
    elif typ == 'gt':
        if a.sort() == z3.IntSort() and b.sort() == z3.IntSort():
            return a > b
        else:
            return None
    elif typ == 'ge':
        if a.sort() == z3.IntSort() and b.sort() == z3.IntSort():
            return a >= b
        else:
            return None
    elif typ == 'add':
        if a.sort() == z3.IntSort() and b.sort() == z3.IntSort():
            return a + b
        else:
            return None
    elif typ == 'sub':
        if a.sort() == z3.IntSort() and b.sort() == z3.IntSort():
            return a - b
        else:
            return None
    elif typ == 'mul':
        if a.sort() == z3.IntSort() and b.sort() == z3.IntSort():
            return a * b
        else:
            return None
    raise UnexpectedException()

def parse_expr(ast: Ast, env: Env) -> tuple[Optional[Expr],Range]:
    if isinstance(ast, lark.Tree):
        if ast.data in ['eq','ne','lt','le','gt','ge','add','sub','mul']:
            c0, c1 = ast.children
            e0, r0 = parse_expr(c0, env)
            if not isinstance(e0, Expr):
                return None, r0
            e1, r1 = parse_expr(c1, env)
            if not isinstance(e1, Expr):
                return None, r1
            return binop(ast.data, e0, e1), (r0[0], r1[1])
        elif ast.data == 'neg':
            c0, = ast.children
            e0, r0 = parse_expr(c0, env)
            if not isinstance(e0, Expr) or e0.sort() != z3.IntSort():
                return None, r0
            return -e0, r0
        elif ast.data == 'paren':
            _o, e, _c = ast.children
            ex, r = parse_expr(e, env)
            return ex, (_o.start_pos, _c.end_pos)
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

def parse_inner_statement(ast: Ast, env:Env) -> tuple[Optional[Expr],Range]:
    if isinstance(ast, lark.Tree):
        if ast.data == 'bare_expr':
            e, _nl = ast.children
            ex,r = parse_expr(e, env)
            if ex.sort() == z3.BoolSort():
                return ex,r
            else:
                return None,r
    raise UnexpectedException(str(ast))

def parse_statement(ast: Ast, env:Env) -> Statement:
    if isinstance(ast, lark.Tree):
        if ast.data in ['def','introduce']:
            _def, nametypes, _open, _nl0, exprs, _close, _nl1 = ast.children
            xs:list[Var] = []
            for nametype in nametypes.children:
                x,r = parse_nametype(nametype)
                if x.name in env:
                    return Erroneous(r)
                env[x.name] = x
                xs.append(x)
            es:list[Expr] = []
            for ch in exprs.children:
                if not (isinstance(ch, lark.Tree) and ch.data == 'blank'):
                    e,r = parse_inner_statement(ch, env)
                    if isinstance(e,Expr):
                        es.append(e)
                    else:
                        return Erroneous(r)

            return Introduce(xs, es, ast.data == 'def', (_def.start_pos, _close.end_pos))
        elif ast.data == 'bare_expr':
            ex, _nl = ast.children
            e,r = parse_expr(ex, env)
            if isinstance(e,Expr) and e.sort() == z3.BoolSort():
                return BareExpr(e,r)
            else:
                return Erroneous(r)
    raise UnexpectedException(str(ast))

def parse_script(ast: Ast) -> Script:
    env = dict()
    statements = []
    for child in ast.children:
        statements.append(parse_statement(child, env))
    return Script(statements)
