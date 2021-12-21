import lark
import readline
import z3

grammar = lark.Lark('''
?start: assignment
           | assertion

assignment: CNAME "=" expr

assertion: "assert" expr

?expr: INT
      | CNAME
      | equality

equality: expr "==" expr

%import common.CNAME
%import common.INT
%import common.WS

%ignore WS
''')

class Bool:
    def __init__(self):
        self.sort = z3.BoolSort()

    def var(self, x):
        return z3.Bool(x)

class Int:
    def __init__(self):
        self.sort = z3.IntSort()

    def var(self, x):
        return z3.Int(x)

class TypeException(Exception):
    pass

class VarNotDefined(Exception):
    pass

class VarAlreadyDefined(Exception):
    pass

class Unimplemented(Exception):
    pass

class Session:
    def __init__(self):
        self.env = {}
        self.solver = z3.Solver()
        self.B = Bool()
        self.Z = Int()

    def typecheck(self, e):
        if isinstance(e, lark.Token):
            if e.type == 'CNAME':
                if e.value in self.env:
                    t = self.env[e.value]
                    return t, t.var(e.value)
                else:
                    raise VarNotDefined(e.value)
            elif e.type == 'INT':
                return self.Z, int(e.value)
            else:
                raise Unimplemented(f'token {e.type}')
        else:
            if e.data == 'equality':
                e0, e1 = e.children
                t0,z0 = self.typecheck(e0)
                t1,z1 = self.typecheck(e1)
                if t0 == t1:
                    return self.B, z0 == z1
                else:
                    raise TypeException(f'Type mismatch in equality: {t0} vs {t1}')
            else:
                raise Unimplemented(f'tree {e.data}')

    def assign(self, x, e):
        if x in self.env:
            raise VarAlreadyDefined(x)
        t,z = self.typecheck(e)
        self.env[x] = t
        self.solver.add(t.var(x) == z)

    def process_statement(self, ast):
        if ast.data == 'assignment':
            x, e = ast.children
            self.assign(x, e)
        elif ast.data == 'assertion':
            e, = ast.children
            t, z = self.typecheck(e)
            if t != self.B:
                raise TypeException(f'Assertion must be boolean expression, got {t}')
            self.solver.push()
            self.solver.add(z3.Not(z))
            if self.solver.check() == z3.unsat:
                print('ok')
            else:
                print('not necessarily')
                print(self.solver.model())
            self.solver.pop()
        else:
            raise Unimplemented(f'statement {ast.data}')

def main():
    global grammar
    session = Session()
    while True:
        text = input('>> ')
        ast = grammar.parse(text)
        session.process_statement(ast)

if __name__ == '__main__':
    main()
