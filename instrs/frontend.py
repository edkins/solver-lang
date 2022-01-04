from __future__ import annotations
import lark
from typing import Union, Optional
from instrs.backbone import *
from instrs.instr import *
from instrs.errors import *
from instrs.regfile import *
from instrs.low_level_expr import *

Ast = Union[str,lark.Tree]

class FEType:
    # Overridden
    def bbtype(self) -> BBType:
        raise UnexpectedException()

    # Overridden
    def opt_condition(self, val:LLExpr, i:int) -> LLExpr:
        raise UnexpectedException()

    def condition(self, val:LLExpr) -> LLExpr:
        bb = self.bbtype()
        if val.bbtype() != bb:
            raise UnexpectedException(f'Condition: expecting {bb} got {val.bbtype()}')
        if isinstance(bb, BBUnion):
            varnum = val.unused_var()
            xs = [LLVar(varnum,opt) for opt in bb.options]
            conds = [self.opt_condition(xs[i],i) for i in range(len(bb.options))]
            return LLUnion(val, xs, conds)
        else:
            return self.opt_condition(val,0)

class FEInt(FEType):
    def bbtype(self) -> BBType:
        return BBZ

    def opt_condition(self, val:LLExpr, i:int) -> LLExpr:
        return LLBoolVal(True)

class FEBool(FEType):
    def bbtype(self) -> BBType:
        return BBB

    def opt_condition(self, val:LLExpr, i:int) -> LLExpr:
        return LLBoolVal(True)

class FERange(FEType):
    def __init__(self, upper:Val):
        self.upper = ll_value(upper, BBZ)

    def bbtype(self) -> BBType:
        return BBZ

    def opt_condition(self, val:LLExpr, i:int) -> LLExpr:
        return ll_and([LLLe(LLIntVal(0), val), LLLt(val, self.upper)])

class FETuple(FEType):
    def __init__(self, members:list[FEType]):
        self.members = tuple(members)

    def bbtype(self) -> BBType:
        return BBTuple([m.bbtype() for m in self.members])

    def opt_condition(self, val:LLExpr, i:int) -> LLExpr:
        return ll_and([self.members[i].condition(LLTupleMember(val, i)) for i in range(len(self.members))])

class FEArray(FEType):
    def __init__(self, element:FEType):
        self.element = element

    def bbtype(self) -> BBType:
        return BBArray(self.element.bbtype())

    def opt_condition(self, val:LLExpr, i:int) -> LLExpr:
        x = LLVar(val.unused_var(), BBZ)
        in_range = ll_and([LLLe(LLIntVal(0), x), LLLt(x, LLArrayLength(val))])
        return LLForAll(x, ll_implies(in_range, self.element.condition(LLArrayElement(val, x))))

# TODO: deal with empty union
class FEUnion(FEType):
    def __init__(self, options:list[FEType]):
        if len(options) == 0:
            raise Unimplemented('Cannot currently handle empty union')
        self.options = tuple(options)
        self.stuff = flat_union_rearrange([o.bbtype() for o in self.options])

    def bbtype(self) -> BBType:
        if len(self.stuff) == 0:
            raise UnexpectedException('Cannot handle empty union')
        elif len(self.stuff) == 1:
            return self.stuff[0][0]
        else:
            return BBUnion([s[0] for s in self.stuff])

    def opt_condition(self, val:LLExpr, i:int) -> LLExpr:
        conds = []
        bb,pairs = self.stuff[i]
        for j,k in pairs:
            valc = LLCoerce(self.options[j].bbtype().get_options()[k], val)
            conds.append(self.options[j].opt_condition(valc,k))
        return ll_or(conds)


def token_value(ast: Ast) -> str:
    if isinstance(ast, lark.Token):
        return ast.value
    else:
        raise UnexpectedException()

def binop(name:str, dest:Reg, v0:Val, v1:Val) -> Instr:
    if name == 'eq':
        return Eq(dest, v0, v1, ne=False)
    elif name == 'ne':
        return Eq(dest, v0, v1, ne=True)
    elif name == 'lt':
        return Lt(dest, v0, v1)
    elif name == 'le':
        return Le(dest, v0, v1)
    elif name == 'gt':
        return Lt(dest, v1, v0)
    elif name == 'ge':
        return Le(dest, v1, v0)
    elif name == 'add':
        return Add(dest, v0, v1)
    elif name == 'sub':
        return Sub(dest, v0, v1)
    elif name == 'mul':
        return Mul(dest, v0, v1)
    elif name == 'lookup':
        return Lookup(dest, v0, v1)
    elif name == 'append':
        return Append(dest, v0, v1)
    else:
        raise Unimplemented(f'Binop {name}')

def unary(name:str, dest:Reg, v:Val) -> Instr:
    if name == 'neg':
        return Neg(dest, v)
    elif name == 'len':
        return Len(dest, v)
    elif name == 'arr':
        return Arr(dest, v)
    else:
        raise Unimplemented(f'Unary {name}')

class FuncInfo:
    def __init__(self, entrypoint:int, argcount:int, ret:FEType, outers:set[str]):
        self.entrypoint = entrypoint
        self.argcount = argcount
        self.ret = ret
        self.outers = set(outers)
        self.finished = False

class InstrBuilder:
    def __init__(self, is_repl:bool):
        self.tempnum = 0
        self.instrs:list[Instr] = []
        self.is_repl = is_repl
        self.func_infos:dict[str,FuncInfo] = {}
        self.current_func:Optional[str] = None
        self.outers:set[str] = set()

    def rollback(self, pos:int):
        if pos >= 0 and pos <= len(self.instrs):
            self.instrs = self.instrs[:pos]
        else:
            raise UnexpectedException('pos out of range')

    def target_or_next_temporary(self, target:Optional[Reg]) -> Reg:
        if isinstance(target, Reg):
            return target
        result = Reg(f'.t{self.tempnum}')
        self.tempnum += 1
        return result

    def visit_type(self, ast: Ast) -> FEType:
        if isinstance(ast, lark.Token):
            if ast.value == 'int':
                return FEInt()
            elif ast.value == 'bool':
                return FEBool()
            else:
                raise Unimplemented(f'Unimplemented type token {ast.value}')
        elif isinstance(ast, lark.Tree):
            if ast.data == 'range':
                upper = self.visit_expr(ast.children[0], None)
                return FERange(upper)
            elif ast.data == 'tuple':
                ts = [self.visit_type(e) for e in ast.children]
                return FETuple(ts)
            elif ast.data == 'array':
                t = self.visit_type(ast.children[0])
                return FEArray(t)
            elif ast.data == 'union':
                ts = [self.visit_type(e) for e in ast.children]
                return FEUnion(ts)
            else:
                raise Unimplemented(f'Unimplemented type tree {ast.data}')
        else:
            raise Unimplemented('Unimplemented type non-tree non-token')

    def visit_args(self, args: list[Ast]):
        for arg in args:
            if isinstance(arg, lark.Tree):
                x, t = arg.children
                name = token_value(x)
                typ = self.visit_type(t)
                self.emit(Arg(Reg(name), typ.bbtype()))
                expr = typ.condition(ll_value(Reg(name), typ.bbtype()))
                self.emit(Precondition(expr))
            else:
                raise Unimplemented('Unimplemented arg non-tree')

    def visit_statement(self, ast: Ast) -> Optional[Val]:
        if isinstance(ast, lark.Tree):
            if ast.data == 'assign':
                x, e = ast.children
                name = token_value(x)
                if self.current_func == None:
                    self.outers.add(name)
                self.visit_expr(e, Reg(name))
                return Reg(name)
            elif ast.data == 'assert':
                e, = ast.children
                val = self.visit_expr(e, None)
                self.emit(Assert(ll_value(val, BBB),'assert'))
                return None
            elif ast.data == 'pushfn':
                f = token_value(ast.children[0])
                args = ast.children[1:-1]
                ret = ast.children[-1]
                if f in self.func_infos:
                    raise FuncAlreadyDefinedException(f)
                self.current_func = f
                func_info = FuncInfo(len(self.instrs), len(args), self.visit_type(ret), self.outers)
                self.func_infos[f] = func_info
                self.emit(Fn())
                self.visit_args(args)
                return None
            elif ast.data == 'pop':
                if not isinstance(self.current_func, str):
                    raise StackEmptyException()
                if not self.func_infos[self.current_func].finished:
                    raise IncompleteFunctionException('Missing return statement in function')
                self.current_func = None
                return None
            elif ast.data == 'return':
                if not isinstance(self.current_func, str):
                    raise NotInFunctionException('Cannot return at top level')
                if self.func_infos[self.current_func].finished:
                    raise DuplicateReturnStatementException()
                e, = ast.children
                val = self.visit_expr(e, None)
                val2 = self.target_or_next_temporary(None)
                rtype = self.func_infos[self.current_func].ret
                self.emit(Coerce(val2, val, rtype.bbtype()))
                cond = rtype.condition(ll_value(val2, rtype.bbtype()))
                self.emit(Assert(cond, "postcondition"))
                self.emit(Ret(val2))
                self.func_infos[self.current_func].finished = True
                return None
            elif ast.data == 'unreachable':
                if not isinstance(self.current_func, str):
                    raise NotInFunctionException('Top level cannot be unreachable')
                self.emit(Unreachable())
                self.func_infos[self.current_func].finished = True
                return None
            elif ast.data == 'sample':
                if not self.is_repl:
                    raise ModeException('Bare expression only allowed in repl mode')
                e, = ast.children
                val = self.visit_expr(e, None)
                return val
            else:
                raise Unimplemented('Unimplemented statement tree {ast.data}')
        else:
            raise Unimplemented('Unimplemented statement non-tree')

    
    def emit(self, instr:Instr):
        #print(instr)
        self.instrs.append(instr)


    def visit_expr(self, ast: Ast, target:Optional[Reg]) -> Val:
        if isinstance(ast, lark.Token):
            if ast.type == 'CNAME':
                result:Val = Reg(ast.value)
            elif ast.type == 'INT':
                result = int(ast.value)
            elif ast.type == 'TRUE':
                result = True
            elif ast.type == 'FALSE':
                result = False
            else:
                raise Unimplemented(f'Unimplemented expression token {ast.type}')

            if isinstance(target, Reg):
                self.emit(Mov(target, result))
                return target
            else:
                return result
        elif isinstance(ast, lark.Tree):
            if ast.data in ['eq','ne','lt','le','gt','ge','add','sub','mul','lookup','append']:
                e0, e1 = ast.children
                v0 = self.visit_expr(e0,None)
                v1 = self.visit_expr(e1,None)
                dest = self.target_or_next_temporary(target)
                self.emit(binop(ast.data, dest, v0, v1))
                return dest
            elif ast.data in ['neg']:
                e0, = ast.children
                v0 = self.visit_expr(e0,None)
                dest = self.target_or_next_temporary(target)
                self.emit(unary(ast.data, dest, v0))
                return dest
            elif ast.data in ['len','arr']:
                zzz,e0 = ast.children
                v0 = self.visit_expr(e0,None)
                dest = self.target_or_next_temporary(target)
                self.emit(unary(ast.data, dest, v0))
                return dest
            elif ast.data == 'call':
                f = token_value(ast.children[0])
                if f not in self.func_infos:
                    raise FuncNotDefinedException(f)
                vs = []
                for e in ast.children[1:]:
                    vs.append(self.visit_expr(e,None))
                if self.func_infos[f].argcount != len(vs):
                    raise ArgCountMismatchException(f'Expected {self.func_infos[f].argcount} arguments, got {len(vs)}')
                i = self.func_infos[f].entrypoint
                prefix = f'c{self.tempnum}$'
                self.tempnum += 1
                remapping = RegRemapping(self.func_infos[f].outers, prefix)
                while True:
                    instr = self.instrs[i].remap(remapping)
                    if isinstance(instr, Fn):
                        pass
                    elif isinstance(instr, Arg):
                        if len(vs) == 0:
                            raise UnexpectedException('too few args')
                        self.emit(Coerce(instr.dest, vs.pop(0), instr.typ))
                    elif isinstance(instr, Precondition):
                        self.emit(Assert(instr.e, 'precondition'))
                    elif isinstance(instr, Ret):
                        if len(vs) != 0:
                            raise UnexpectedException('too many args')
                        return instr.r
                    elif isinstance(instr, Unreachable):
                        raise UnexpectedException("Shouldn't be inside call to unreachable function")
                    else:
                        self.emit(instr)
                    i += 1
            elif ast.data == 'listing':
                vs = []
                for e in ast.children:
                    vs.append(self.visit_expr(e,None))
                dest = self.target_or_next_temporary(target)
                self.emit(Listing(dest, vs))
                return dest
            else:
                raise Unimplemented(f'Unimplemented expression tree {ast.data}')
        else:
            raise Unimplemented('Unimplemented expression non-tree non-token')

