from typing import Union
import lark
from thin2.grammar import grammar
from thin2.errors import UnexpectedException

class Result:
    def __init__(self, start:int, end:int, ok:bool):
        self.start = start
        self.end = end
        self.ok = ok

    def __repr__(self):
        return f'range {self.start} {self.end} {"ok" if self.ok else "bad"}\n'

Ast = Union[str,lark.Tree]

def visit_statement(ast: Ast, results:list[Result]):
    all_tokens = list(ast.scan_values(lambda v:isinstance(v,lark.Token)))
    start_pos = min((t.start_pos for t in all_tokens))
    end_pos = max((t.end_pos for t in all_tokens))
    results.append(Result(start_pos, end_pos, True))
    
def visit_statements(ast: Ast, results:list[Result]):
    if isinstance(ast, lark.Tree):
        for child in ast.children:
            visit_statement(child, results)
    else:
        raise UnexpectedException('Expecting tree')
                
def process(text: str) -> str:
    try:
        ast = grammar.parse(text)
        results: list[Result] = []
        visit_statements(ast, results)
    except lark.exceptions.UnexpectedInput as ex:
        results = [Result(0, len(text), False)]
    return ''.join((str(r) for r in results))
    
