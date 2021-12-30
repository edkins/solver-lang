from stages.node import *
from stages.errors import *
from stages.annotation import int_type, ExprEnv

def coerce_expr(e:Expr, typ:Type) -> Expr:
    if e.typ == typ:
        return e
    raise TypeException()

def type_check_expr(e:Expr):
    for xe in e.xs:
        type_check_expr(xe)

    if isinstance(e, Int):
        pass
    elif isinstance(e, Var):
        pass
    elif isinstance(e, Builtin):
        if e.f in ['.false','.true']:
            pass
        elif e.f in ['.eq','.ne']:
            pass     # Can compare anything to anything else for equality
        elif e.f in ['.lt','.le','.gt','.ge','.add','.sub','.mul']:
            e.xs[0] = coerce_expr(e.xs[0], int_type())
            e.xs[1] = coerce_expr(e.xs[1], int_type())
        elif e.f == '.neg':
            e.xs[0] = coerce_expr(e.xs[0], int_type())
        elif e.f == '.len':
            e.xs[0] = coerce_to_list(e.xs[0])
        elif e.f == '.lookup':
            e.xs[0] = coerce_to_list(e.xs[0])
            e.xs[1] = coerce_expr(e.xs[1], int_type())
        elif e.f == '.listing':
            pass     # anything can be put in a list
    elif isinstance(e, Call):
        fn_type = e.get_fn_type()
        if len(fn_type.args) != len(e.xs):
            raise UnexpectedException('Should already have checked for correct arg count')
        expr_env = ExprEnv({})
        for i in range(len(e.xs)):
            x,typ = fn_type.args[i]
            expr_env.define_var(x, e.xs[i])
            e.typ = expr_env.subst_type(fn_type.ret)

