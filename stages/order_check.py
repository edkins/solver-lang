from stages.errors import *
from stages.node import *

class BareEnvItem:
    pass

class BareVarEnvItem(BareEnvItem):
    pass

class BareFuncEnvItem(BareEnvItem):
    pass

class DefiningFuncEnvItem(BareEnvItem):
    pass

class DefiningVarEnvItem(BareEnvItem):
    pass

class BareEnv:
    def __init__(self, items: dict[str,BareEnvItem]):
        self.items = dict(items)

    def clone(self) -> Any:
        return BareEnv(self.items)

    def is_var(self, x:str) -> bool:
        return isinstance(self.items.get(x), BareVarEnvItem)

    def is_fn(self, f:str) -> bool:
        return isinstance(self.items.get(f), BareFuncEnvItem)

    def start_defining_fn(self, f:str):
        item = self.items.get(f)
        if item == None:
            self.items[f] = DefiningFuncEnvItem()
        elif isinstance(item, BareFuncEnvItem) or isinstance(item, DefiningFuncEnvItem):
            raise FuncAlreadyDefinedException(f)
        elif isinstance(item, BareVarEnvItem) or isinstance(item, DefiningVarEnvItem):
            raise VarFuncCollisionException(f)
        else:
            raise UnexpectedException()

    def finish_defining_fn(self, f:str):
        item = self.items.get(f)
        if isinstance(item, DefiningFuncEnvItem):
            self.items[f] = BareFuncEnvItem()
        else:
            raise UnexpectedException(f'Expected DefiningFuncEnvItem got {item}')

    def start_defining_var(self, x:str):
        item = self.items.get(x)
        if item == None:
            self.items[x] = DefiningVarEnvItem()
        elif isinstance(item, BareFuncEnvItem) or isinstance(item, DefiningFuncEnvItem):
            raise VarFuncCollisionException(x)
        elif isinstance(item, BareVarEnvItem) or isinstance(item, DefiningVarEnvItem):
            raise VarAlreadyDefinedException(x)
        else:
            raise UnexpectedException()

    def finish_defining_var(self, x:str):
        item = self.items.get(x)
        if isinstance(item, DefiningVarEnvItem):
            self.items[x] = BareVarEnvItem()
        else:
            raise UnexpectedException(f'Expected DefiningVarEnvItem got {item}')

    def order_check_expr(self, e: Expr):
        if e.typ != None:
            raise UnexpectedException('Node already type-annotated')

        if isinstance(e, Int):
            if len(e.xs) > 0:
                raise UnexpectedException('Int node should not have children')
        elif isinstance(e, Var):
            if not self.is_var(e.f):
                raise VarNotDefinedException(e.f)
            if len(e.xs) > 0:
                raise UnexpectedException('Var node should not have children')
        elif isinstance(e, Call):
            if not self.is_fn(e.f):
                raise FuncNotDefinedException(e.f)
            for x in e.xs:
                self.order_check_expr(x)
        elif isinstance(e, Builtin):
            for x in e.xs:
                self.order_check_expr(x)
        else:
            raise Unimplemented('Order check not implemented for this node class')

    def order_check_type(self, typ: Type):
        for t in typ.type_args:
            self.order_check_type(t)
        for e in typ.expr_args:
            self.order_check_expr(e)

    def order_check_statement(self, statement: Statement, toplevel: bool):
        if isinstance(statement, Def):
            self.start_defining_fn(statement.f)
            inner = self.clone()
            for x,typ in statement.args:
                inner.start_defining_var(x)
                inner.order_check_type(typ)
                inner.finish_defining_var(x)
            inner.order_check_type(statement.ret)
            inner.order_check_statements(statement.body, False)
            self.finish_defining_fn(statement.f)
        elif isinstance(statement, Assign):
            if statement.typ != None:
                raise UnexpectedException('Node already type-annotated')
            self.start_defining_var(x)
            self.order_check_expr(statement.e)
            self.finish_defining_var(x)
        elif isinstance(statement, Assert):
            self.order_check_expr(statement.e)
        elif isinstance(statement, Return):
            if statement.typ != None:
                raise UnexpectedException('Node already type-annotated')
            if toplevel:
                raise TopLevelReturnException()
            self.order_check_expr(statement.e)
        else:
            raise Unimplemented('Order check not implemented for this statement class')

    def order_check_statements(self, statements: list[Statement], toplevel: bool):
        for statement in statements:
            self.order_check_statement(statement, toplevel)

def order_check_program(statements: list[Statement]):
    BareEnv({}).order_check_statements(statements, True)
