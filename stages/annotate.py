from stages.node import *
from stages.errors import *
from typing import Optional

def int_type() -> Type:
    return Type('int',[],[])

def bool_type() -> Type:
    return Type('bool',[],[])

def impossible_type() -> Type:
    return Type('!',[],[])

def tuple_type(ts: list[Type]) -> Type:
    return Type('tuple',ts,[])

def type_options(t: Type) -> list[Type]:
    if t.name == 'union':
        result = []
        for t1 in t.type_args:
            result += type_options(t1)
        return result
    else:
        return [t]

def collapsed_union_type(ts: list[Type]) -> Type:
    result = []
    for t1 in ts:
        for t in type_options(t1):
            if t not in result:
                result.append(t)

    if len(result) == 0:
        return impossible_type()
    elif len(result) == 1:
        return result[0]
    else:
        return Type('union',result,[])

def get_element_type(t: Type, index: Optional[int]) -> Type:
    result = []
    for t1 in type_options(t):
        if t1.name in ['array','vec']:
            result.append(t1.type_args[0])
        elif t1.name == 'tuple':
            if isinstance(index, int):
                if index >= 0 and index < len(t1.type_args):    # TODO: if out of range, provide error hint
                    result.append(t1.type_args[index])
            else:
                result += t1.type_args   # TODO: if empty, provide error hint as to why
    return collapsed_union_type(result)

def extract_int(e: Expr) -> Optional[int]:
    if isinstance(e, Int):
        return e.f
    else:
        return None

class ExprEnv:
    def __init__(self, items: dict[str,Expr]):
        self.items = dict(items)

    def define_var(self, x:str, e:Expr):
        if x in self.items:
            raise UnexpectedException('Var {x} already defined. This should already have been checked')
        if e.typ == None:
            raise UnexpectedException('Expr has no type annotation')
        self.items[x] = e

    def subst_type(self, typ:Type) -> Type:
        type_args = [self.subst_type(t) for t in typ.type_args]
        expr_args = [self.subst_expr(e) for e in typ.expr_args]
        return Type(typ.name, type_args, expr_args)

    def subst_expr(self, e:Expr) -> Expr:
        if not isinstance(e.typ, Type):
            raise UnexpectedException('Expression node has no type annotation')
        if isinstance(e, Int):
            return e.clone()
        elif isinstance(e, Var):
            if e.f in self.items:
                return self.items[e.f].clone()
            else:
                # Assume it's a constant available in the original environment, and leave unchanged
                return e.clone()
        elif isinstance(e, Call):
            xs = [self.subst_expr(x) for x in e.xs]
            result = Call(e.f, *xs)
            result.typ = self.subst_type(e.typ)
            return result
        elif isinstance(e, Builtin):
            xs = [self.subst_expr(x) for x in e.xs]
            reuslt = Builtin(e.f, *xs)
            result.typ = self.subst_type(e.typ)
            return result
        else:
            raise Unimplemented('Unrecognized expression class for subst')

class EnvItem:
    pass

class VarEnvItem(EnvItem):
    def __init__(self, typ:Type):
        self.typ = typ

class FnEnvItem(EnvItem):
    def __init__(self, args:list[tuple[str,Type]], ret:Type):
        self.args = args
        self.ret = ret

class TypeEnv:
    def __init__(self, items: dict[str,EnvItem]):
        self.items = dict(items)

    def clone(self):
        return TypeEnv(self.items)

    def get_var_type(self, x:str) -> Type:
        item = self.items.get(x)
        if isinstance(item, VarEnvItem):
            return item.typ
        else:
            raise UnexpectedException('Var {x} not defined. This should already have been checked')

    def get_fn_type(self, f:str) -> FnEnvItem:
        item = self.items.get(f)
        if isinstance(item, FnEnvItem):
            return item
        else:
            raise UnexpectedException('Func {f} not defined. This should already have been checked')

    def define_var(self, x:str, typ:Type):
        if x in self.items:
            raise UnexpectedException('Item {x} already defined. This should already have been checked')
        self.items[x] = VarEnvItem(typ)

    def define_fn(self, f:str, args:list[tuple[str,Type]], ret:Type):
        if f in self.items:
            raise UnexpectedException('Item {f} already defined. This should already have been checked')
        self.items[f] = FnEnvItem(args, ret)

    def annotate_type(self, typ: Type):
        for t in typ.type_args:
            self.annotate_type(t)
        for e in typ.expr_args:
            self.annotate_expr(e)

    def annotate_expr(self, e: Expr):
        if e.typ != None:
            raise UnexpectedException('Node already type-annotated')

        for xe in e.xs:
            self.annotate_expr(xe)

        if isinstance(e, Int):
            if len(e.xs) != 0:
                raise UnexpectedException(f'Integer with {len(e.xs)} args')
            e.typ = int_type()
        elif isinstance(e, Builtin):
            if e.f in ['.false','.true']:
                e.typ = bool_type()
                if len(e.xs) != 0:
                    raise UnexpectedException(f'Boolean const builtin with {len(e.xs)} args')
            elif e.f in ['.eq','.ne','.lt','.le','.gt','.ge']:
                e.typ = bool_type()
                if len(e.xs) != 2:
                    raise UnexpectedException(f'Boolean binop builtin with {len(e.xs)} args')
            elif e.f in ['.neg','.len']:
                e.typ = int_type()
                if len(e.xs) != 1:
                    raise UnexpectedException(f'Integer unary builtin with {len(e.xs)} args')
            elif e.f in ['.add','.sub','.mul']:
                e.typ = int_type()
                if len(e.xs) != 2:
                    raise UnexpectedException(f'Integer binop builtin with {len(e.xs)} args')
            elif e.f == '.lookup':
                if len(e.xs) != 2:
                    raise UnexpectedException(f'Lookup builtin with {len(e.xs)} args')
                if not isinstance(e.xs[0].typ, Type):
                    raise UnexpectedException('Should be annotated')
                e.typ = get_element_type(e.xs[0].typ, extract_int(e.xs[1]))
            elif e.f == '.listing':
                e.typ = tuple_type([x.get_type() for x in e.xs])
            else:
                raise Unimplemented(f'No type annotation known for {e.f}')
        elif isinstance(e, Var):
            if len(e.xs) != 0:
                raise UnexpectedException(f'Var with {len(e.xs)} args')
            e.typ = self.get_var_type(e.f)
        elif isinstance(e, Call):
            fn_type = self.get_fn_type(e.f)
            if len(fn_type.args) != len(e.xs):
                raise ArgCountMismatchException(f'Expected {len(fn_type.args)} arguments, got {len(e.xs)}')
            expr_env = ExprEnv({})
            for (x,ignored_type), xe in zip(fn_type.args, e.xs):
                expr_env.define_var(x, xe)      # note that xe is annotated with its type here, not its expected type within the function (ignored_type)
            e.typ = expr_env.subst_type(fn_type.ret)
        else:
            raise Unimplemented('Unrecognized expression class for annotate')

    def annotate_statement(self, statement: Statement, ret:Optional[Type]):
        if isinstance(statement, Def):
            inner = self.clone()
            for x,typ in statement.args:
                inner.annotate_type(typ)
                inner.define_var(x,typ)
            inner.annotate_type(statement.ret)
            inner.annotate_statements(statement.body, statement.ret)
            self.define_fn(statement.f, statement.args, statement.ret)
        elif isinstance(statement, Assign):
            if statement.typ != None:
                raise UnexpectedException('Node already type-annotated')
            self.annotate_expr(statement.e)
            statement.typ = statement.e.get_type()
            self.define_var(statement.x, statement.typ)
        elif isinstance(statement, Assert):
            self.annotate_expr(statement.e)
        elif isinstance(statement, Return):
            if statement.typ != None:
                raise UnexpectedException('Node already type-annotated')
            if ret == None:
                raise TopLevelReturnException()
            self.annotate_expr(statement.e)
            statement.typ = ret
        else:
            raise Unimplemented('Unrecognized statement class for annotate')

    def annotate_statements(self, statements: list[Statement], ret:Optional[Type]):
        for statement in statements:
            self.annotate_statement(statement, ret)

def annotate_program(statements: list[Statement]):
    TypeEnv({}).annotate_statements(statements, None)
