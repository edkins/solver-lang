import lark
import z3
from typing import TextIO
from thin.grammar import grammar
from thin.errors import *
from thin.frontend import Env

class Session:
    def __init__(self, out:TextIO, is_repl:bool):
        self.out = out
        self.env = Env()
        self.solver = z3.Solver()

    def prompt(self) -> str:
        if self.solver.check() == z3.sat:
            return 'sat > '
        else:
            return 'unsat > '

    def parse_and_process(self, text: str):
        if text.strip() == '':
            return
        try:
            ast = grammar.parse(text)
        except lark.exceptions.UnexpectedInput as ex:
            raise ParseException()

        self.env.process_statement(ast, self.solver, self.out)
