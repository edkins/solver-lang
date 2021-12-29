from stages.node import *
from typing import Optional

def int_type():
    return Type('int',[],[])

def bool_type():
    return Type('bool',[],[])

def impossible_type():
    return Type('!',[],[])

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
            if index == None:
                result += t1.type_args   # TODO: if empty, provide error hint as to why
            elif index >= 0 and index < len(t1.type_args):    # TODO: if out of range, provide error hint
                result.append(t1.type_args[index])
    return collapsed_union_type(result)

def extract_int(e: Expr) -> Optional[int]:
    if isinstance(e, Int):
        return e.f
    else:
        return None

class EnvItem:
    pass

class VarEnvItem(EnvItem):
    def __init__(self, typ):
        self.typ = typ

class FnEnvItem(EnvItem):
    def __init__(self, args, ret):
        self.args = args
        self.ret = ret

class Env:
    def __init__(self, items: dict[str,EnvItem]):
        self.items = dict(items)

    def annotate_expr(e: Expr):
        if e.typ != None:
            raise UnexpectedException('Node already type-annotated')

        for x in e.xs:
            self.annotate_expr(x)

        if isinstance(e, Int):
            e.typ = int_type()
        elif isinstance(e, Builtin):
            if e.f in ['.false','.true','.eq','.ne','.lt','.le','.gt','.ge']:
                e.typ = bool_type()
            elif e.f in ['.add','.sub','.mul','.neg','.len']:
                e.typ = int_type()
            elif e.f == '.lookup':
                e.typ = get_element_type(e.xs[0].typ, extract_int(e.xs[1]))
            else:
                raise Unimplemented(f'No type annotation known for {e.f}')
