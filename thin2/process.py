import lark
from thin2.grammar import grammar
from thin2.frontend import parse_script
from thin2.script import Result

def process(text: str) -> str:
    try:
        ast = grammar.parse(text)
        script = parse_script(ast)
        results = script.validate()
    except lark.exceptions.UnexpectedInput as ex:
        results = [Result((0, len(text)), False)]
    return ''.join((str(r) for r in results))
    
