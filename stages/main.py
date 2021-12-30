from stages.grammar import grammar
from stages.to_node import to_statements
from stages.order_check import order_check_program
from stages.annotate import annotate_program

def run_script(text: str):
    ast = grammar.parse(text)
    print('AST processing')
    statements = to_statements(ast)
    print(statements)
    print('Order checking')
    order_check_program(statements)
    print(statements)
    print('Annotating')
    annotate_program(statements)
    print(statements)
