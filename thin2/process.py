import lark
from thin2.grammar import grammar
from thin2.frontend import parse_script
from thin2.script import Result

def process(text: str) -> str:
    errors:list[Result] = []
    try:
        def handle_error(e: lark.exceptions.UnexpectedInput) -> bool:
            if isinstance(e, lark.exceptions.UnexpectedToken) and isinstance(e.token.start_pos, int) and isinstance(e.token.end_pos, int):
                errors.append(Result((e.token.start_pos, e.token.end_pos), False))
            elif isinstance(e, lark.exceptions.UnexpectedCharacters):
                errors.append(Result((e.pos_in_stream, e.pos_in_stream + 1), False))
            return True

        ast = grammar.parse(text, on_error = handle_error)
        script = parse_script(ast)
        results = script.validate()
    except lark.exceptions.UnexpectedInput as ex:
        if len(errors) == 0:
            results = [Result((0, len(text)), False)]
        else:
            results = errors
    return ''.join((str(r) for r in sorted(results, key=lambda res:res.start, reverse=True)))
    
