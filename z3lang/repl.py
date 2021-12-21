import lark
import readline
import traceback
import z3

grammar = lark.Lark('''
?start: assignment
           | assertion
           | pushfn
           | pop

assignment: CNAME "=" expr

assertion: "assert" expr

pushfn: "fn" CNAME "(" argcomma* arg? ")" "->" type "{"

pop: "}"


?argcomma: arg ","

arg: CNAME ":" type

?type: "int" -> int
      | "bool" -> bool
      | range

range: "range" expr


?expr: INT
      | CNAME
      | equality
      | lessthan

equality: expr "==" expr

lessthan: expr "<" expr

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

    def restrictions(self, z):
        return []

class Int:
    def __init__(self):
        self.sort = z3.IntSort()

    def var(self, x):
        return z3.Int(x)

    def restrictions(self, z):
        return []

class Range:
    def __init__(self, upper):
        self.sort = z3.IntSort()
        self.upper = upper

    def var(self, x):
        return z3.Int(x)

    def restrictions(self, z):
        return [z >= 0, z < self.upper]


class Mistake(Exception):
    pass

class TypeException(Mistake):
    pass

class VarNotDefined(Mistake):
    pass

class VarAlreadyDefined(Mistake):
    pass

class StackEmpty(Mistake):
    pass

class Unimplemented(Mistake):
    pass

class Session:
    def __init__(self):
        self.env = {}
        self.solver = z3.Solver()
        self.stack = []
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
                if t0.sort != t1.sort:
                    raise TypeException(f'Equality type mismatch: {t0} vs {t1}')
                return self.B, z0 == z1
            elif e.data == 'lessthan':
                e0, e1 = e.children
                t0,z0 = self.typecheck(e0)
                t1,z1 = self.typecheck(e1)
                if t0.sort != self.Z.sort or t1.sort != self.Z.sort:
                    raise TypeException(f'Lessthan type mismatch: {t0} vs {t1}')
                return self.B, z0 < z1
            else:
                raise Unimplemented(f'tree {e.data}')

    def expect_type(self, e, t):
        t1, z = self.typecheck(e)
        if t1 != t:
            raise TypeException(f'Expected type {t}, got {t1}')
        return z

    def assign(self, x, e):
        if x in self.env:
            raise VarAlreadyDefined(x)
        t,z = self.typecheck(e)
        self.env[x] = t
        self.solver.add(t.var(x) == z)

    def lookup_type(self, tname):
        if tname.data == 'int':
            return self.Z
        elif tname.data == 'bool':
            return self.B
        elif tname.data == 'range':
            e, = tname.children
            z = self.expect_type(e, self.Z)
            return Range(z)
        else:
            raise Unimplemented(f'type {tname}')

    def assign_arg(self, x, tname):
        if x in self.env:
            raise VarAlreadyDefined(x)
        t = self.lookup_type(tname)
        self.env[x] = t
        for item in t.restrictions(t.var(x)):
            self.solver.add(item)

    def assertion(self, e):
        z = self.expect_type(e, self.B)
        self.solver.push()
        self.solver.add(z3.Not(z))
        if self.solver.check() == z3.unsat:
            print('ok')
        else:
            print('not necessarily')
            print(self.solver.model())
        self.solver.pop()

    def pushfn(self, f, args, ret):
        if f in self.env:
            raise VarAlreadyDefined(f)
        self.stack.append(f)
        self.solver.push()
        for arg in args:
            x, tname = arg.children
            self.assign_arg(x, tname)

    def pop(self):
        if len(self.stack) == 0:
            raise StackEmpty()

    def process_statement(self, ast):
        if ast.data == 'assignment':
            x, e = ast.children
            self.assign(x, e)
        elif ast.data == 'assertion':
            e, = ast.children
            self.assertion(e)
        elif ast.data == 'pushfn':
            f = ast.children[0]
            args = ast.children[1:-1]
            ret = ast.children[-1]
            self.pushfn(f, args, ret)
        elif ast.data == 'pop':
            self.pop()
        else:
            raise Unimplemented(f'statement {ast.data}')

    def parse_and_process(self, text):
        global grammar
        try:
            ast = grammar.parse(text)
            self.process_statement(ast)
        except lark.exceptions.UnexpectedInput as ex:
            raise Mistake(ex)

def main():
    global grammar
    session = Session()
    while True:
        text = input('>> ')
        try:
            session.parse_and_process(text)
        except Mistake as ex:
            traceback.print_exc()

if __name__ == '__main__':
    main()
