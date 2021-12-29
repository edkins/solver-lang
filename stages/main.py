from stages.grammar import grammar
from stages.to_node import to_statements

def run_script(text: str):
    ast = grammar.parse(text)
    statements = to_statements(ast)
    print(statements)
