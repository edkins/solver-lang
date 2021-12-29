import lark
from stages.errors import *
from stages.node import *
from typing import Union

Ast = Union[lark.Tree,lark.Token]

def to_expr(ast: Ast) -> Expr:
    if isinstance(ast, lark.Token):
        if ast.type == 'CNAME':
            return Expr(ast.value)
        elif ast.type == 'INT':
            return Expr(ast.value)
        elif ast.type == 'TRUE':
            return Expr('.true')
        elif ast.type == 'FALSE':
            return Expr('.false')
        else:
            raise Unimplemented(f'Unimplemented expression token {ast.type}')
    elif isinstance(ast, lark.Tree):
        if ast.data in ['eq','ne','lt','le','gt','ge','add','sub','mul','lookup']:
            e0, e1 = ast.children
            return Expr(f'.{ast.data}', to_expr(e0), to_expr(e1))
        elif ast.data in ['neg','len']:
            e0, = ast.children
            return Expr(f'.{ast.data}', to_expr(e0))
        elif ast.data == 'call':
            f = ast.children[0].value
            xs = ast.children[1:]
            return Expr(f, *[to_expr(x) for x in xs])
        elif ast.data == 'listing':
            xs = ast.children
            return Expr('.listing', *[to_expr(x) for x in xs])
        else:
            raise Unimplemented(f'Unimplemented expression tree {ast.data}')
    else:
        raise Unimplemented('Unimplemented expression non-tree non-token')

def to_statement(ast: Ast) -> Statement:
    if isinstance(ast, lark.Tree):
        if ast.data == 'assign':
            x, e = ast.children
            return Assign(x.value, to_expr(e))
        elif ast.data == 'assert':
            e, = ast.children
            return Assert(to_expr(e))
        elif ast.data == 'unreachable':
            return Assert(Expr(".false"))
        elif ast.data == 'return':
            e, = ast.children
            return Return(to_expr(e))
        elif ast.data == 'fn':
            e0, e1, e2, e3 = ast.children
            f = e0.value
            args = to_args(e1)
            ret = to_type(e2)
            body = to_statements(e3)
            return Def(f, args, ret, body)
        else:
            raise Unimplemented(f'Unimplemented statement tree {ast.data}')
    else:
        raise Unimplemented('Unimplemented statement non-tree')

def to_statements(ast: Ast) -> list[Statement]:
    if isinstance(ast, lark.Tree) and ast.data == 'statements':
        return [to_statement(e) for e in ast.children]
    else:
        raise Unimplemented('Unimplemented statements')

def to_args(ast: Ast) -> list[tuple[str,Type]]:
    if isinstance(ast, lark.Tree) and ast.data == 'args':
        result = []
        for arg in ast.children:
            if isinstance(arg, lark.Tree) and arg.data == 'arg':
                e0, e1 = arg.children
                result.append((e0.value, to_type(e1)))
            else:
                raise Unimplemented('Unimplemented arg')
        return result
    else:
        raise Unimplemented('Unimplemented args')

def to_type(ast: Ast) -> Type:
    if isinstance(ast, lark.Token):
        if ast.value in ['int','bool']:
            return Type(ast.value, [], [])
        else:
            raise Unimplemented(f'Unimplemented type token {ast}')
    elif isinstance(ast, lark.Tree):
        if ast.data == 'range':
            e, = ast.children
            return Type('range', [], [to_expr(e)])
        elif ast.data in ['tuple','union']:
            ts = ast.children
            return Type(ast.data, [to_type(t) for t in ts], [])
        elif ast.data == 'array':
            t, = ast.children
            return Type('array', [to_type(t)], [])
        elif ast.data == 'vec':
            t,e = ast.children
            return Type('vec', [to_type(t)], [to_expr(e)])
        else:
            raise Unimplemented(f'Unimplemented type tree {ast}')
    else:
        raise Unimplemented('Unimplemented type non-tree non-token')
