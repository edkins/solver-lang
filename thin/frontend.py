import lark
import z3
from typing import Union, TextIO
from thin.errors import *

Ast = Union[str,lark.Tree]

def token_value(ast: Ast) -> str:
    if isinstance(ast, lark.Token):
        return ast.value
    else:
        raise UnexpectedException()

class Env:
    def __init__(self):
        self.env:dict[str, z3.SortRef] = {}

    def process_int(self, ast: Ast) -> z3.ArithRef:
        result = self.process_expr(ast)
        if not z3.is_int(result):
            raise TypeException('Expecting int')
        if not isinstance(result, z3.ArithRef):
            raise UnexpectedException('Expecting int to be ArithRef')
        return result

    def process_bool(self, ast: Ast) -> z3.BoolRef:
        result = self.process_expr(ast)
        if not z3.is_bool(result):
            raise TypeException('Expecting bool')
        if not isinstance(result, z3.BoolRef):
            raise UnexpectedException('Expecting bool to be BoolRef')
        return result

    def process_expr(self, ast: Ast) -> z3.ExprRef:
        if isinstance(ast, lark.Tree):
            if ast.data == 'var':
                x = token_value(ast.children[0])
                if x not in self.env:
                    raise UndeclaredException(x)
                return z3.Const(x, self.env[x])
            elif ast.data == 'int':
                n = int(token_value(ast.children[0]))
                return z3.IntVal(n)
            elif ast.data == 'true':
                return z3.BoolVal(True)
            elif ast.data == 'false':
                return z3.BoolVal(False)
            elif ast.data == 'eq':
                return self.process_expr(ast.children[0]) == self.process_expr(ast.children[1])
            elif ast.data == 'ne':
                return self.process_expr(ast.children[0]) != self.process_expr(ast.children[1])
            elif ast.data == 'lt':
                return self.process_int(ast.children[0]) < self.process_int(ast.children[1])
            elif ast.data == 'le':
                return self.process_int(ast.children[0]) <= self.process_int(ast.children[1])
            elif ast.data == 'gt':
                return self.process_int(ast.children[0]) > self.process_int(ast.children[1])
            elif ast.data == 'ge':
                return self.process_int(ast.children[0]) >= self.process_int(ast.children[1])
            elif ast.data == 'add':
                return self.process_int(ast.children[0]) + self.process_int(ast.children[1])
            elif ast.data == 'sub':
                return self.process_int(ast.children[0]) - self.process_int(ast.children[1])
            elif ast.data == 'mul':
                return self.process_int(ast.children[0]) * self.process_int(ast.children[1])
            elif ast.data == 'neg':
                return -self.process_int(ast.children[0])
            else:
                raise Unimplemented(ast.data)

    def process_type(self, ast: Ast) -> z3.SortRef:
        if isinstance(ast, lark.Tree):
            if ast.data == 'inttype':
                return z3.IntSort()
            elif ast.data == 'booltype':
                return z3.BoolSort()
            else:
                raise Unimplemented(ast.data)
        else:
            raise Unimplemented()

    def process_statement(self, ast: Ast, solver:z3.Solver, out:TextIO):
        if isinstance(ast, lark.Tree):
            if ast.data == 'bare_expr':
                e, = ast.children
                result = self.process_bool(e)
                solver.add(result)
            elif ast.data == 'decl':
                t,xtok = ast.children
                x = token_value(xtok)
                if x in self.env:
                    raise ConflictException(x)
                self.env[x] = self.process_type(t)
            elif ast.data == 'reset':
                self.env = {}
                solver.reset()
            elif ast.data == 'model':
                if solver.check() == z3.sat:
                    out.write(str(solver.model()) + '\n')
                else:
                    out.write('unsatisfiable\n')
            else:
                raise Unimplemented(ast.data)
        else:
            raise Unimplemented()
