import z3
import lark
import logging
import io
from typing import TextIO
from instrs.instr import RegFile
from instrs.grammar import grammar
from instrs.frontend import InstrBuilder
from instrs.errors import Mistake, ParseException

class Session:
    def __init__(self, out:TextIO, is_repl:bool):
        self.out = out
        self.rf = RegFile(z3.Solver())
        self.instr_builder = InstrBuilder(is_repl)
        self.pos = 0

    def prompt(self) -> str:
        return '>> '

    def parse_and_process(self, text:str):
        try:
            ast = grammar.parse(text)
        except lark.exceptions.UnexpectedInput as ex:
            raise ParseException(ex)
        dest = self.instr_builder.visit_statement(ast)
        i = self.pos
        n = len(self.instr_builder.instrs)
        while i < n:
            instr = self.instr_builder.instrs[i]
            logging.info(instr)
            try:
                instr.exec(self.rf)
                i += 1
            except Mistake as e:
                self.instr_builder.rollback(self.pos)
                raise e
        self.pos = len(self.instr_builder.instrs)
        value, more, t = self.rf.get_reg_python_value(dest)
        self.out.write(f'{value}{"..." if more else ""} : {t}\n')

def run_script(script:str) -> str:
    with io.StringIO() as output:
        session = Session(output, True)
        for text in script.split('\n'):
            stripped = text.strip()
            if stripped != '':
                session.parse_and_process(stripped)
        return output.getvalue()
