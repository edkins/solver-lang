import z3
from typing import TextIO
from instrs.instr import RegFile
from instrs.grammar import grammar
from instrs.frontend import InstrBuilder
from instrs.errors import Mistake

class Session:
    def __init__(self, out:TextIO):
        self.out = out
        self.rf = RegFile(z3.Solver())
        self.instr_builder = InstrBuilder()
        self.pos = 0

    def prompt(self) -> str:
        return '>> '

    def parse_and_process(self, text:str):
        ast = grammar.parse(text)
        self.instr_builder.visit_statement(ast)
        i = self.pos
        n = len(self.instr_builder.instrs)
        while i < n:
            instr = self.instr_builder.instrs[i]
            print(instr)
            try:
                instr.exec(self.rf)
                i += 1
            except Mistake as e:
                self.instr_builder.rollback(self.pos)
                raise e
        self.pos = len(self.instr_builder.instrs)
