import lark
from typing import Union, Optional
from instrs.backbone import *
from instrs.instr import *
from instrs.errors import *

Ast = Union[str,lark.Tree]

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
    def __init__(self, entrypoint:int, argcount:int, ret:BBType, ret_register:Reg, outers:set[str]):
        self.entrypoint = entrypoint
        self.argcount = argcount
        self.ret = ret
        self.ret_register = ret_register
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

    def visit_type_bb(self, ast: Ast) -> BBType:
        if isinstance(ast, lark.Token):
            if ast.value == 'int':
                return BBZ
            elif ast.value == 'bool':
                return BBB
            else:
                raise Unimplemented(f'Unimplemented type token {ast.value}')
        elif isinstance(ast, lark.Tree):
            if ast.data == 'range':
                return BBZ
            elif ast.data == 'tuple':
                ts = [self.visit_type_bb(e) for e in ast.children]
                return BBTuple(ts)
            elif ast.data == 'array':
                t = self.visit_type_bb(ast.children[0])
                return BBArray(t)
            elif ast.data == 'union':
                ts = [self.visit_type_bb(e) for e in ast.children]
                return flat_union(ts)
            else:
                raise Unimplemented(f'Unimplemented type tree {ast.data}')
        else:
            raise Unimplemented('Unimplemented type non-tree non-token')

    def emit_condition(self, r:Val, post:bool):
        if post:
            self.emit(Postcondition(r))
        else:
            self.emit(Precondition(r))

    def visit_type_cond(self, ast: Ast, val:Optional[Val], post:bool):
        if isinstance(ast, lark.Token):
            if ast.value == 'int':
                pass
            elif ast.value == 'bool':
                pass
            else:
                raise Unimplemented(f'Unimplemented type token {ast.value}')
        elif isinstance(ast, lark.Tree):
            if ast.data == 'range':
                upper = self.visit_expr(ast.children[0],None)
                if isinstance(val, int) or isinstance(val, Reg):
                    t0 = self.target_or_next_temporary(None)
                    t1 = self.target_or_next_temporary(None)
                    self.emit(Le(t0, 0, val))
                    self.emit_condition(t0, post)
                    self.emit(Lt(t1, val, upper))
                    self.emit_condition(t1, post)
                else:
                    raise Unimplemented('Cannot currently put range inside other thing')
            elif ast.data == 'tuple':
                for e in ast.children:
                    self.visit_type_cond(e,None,post)
            elif ast.data == 'array':
                self.visit_type_cond(ast.children[0],None,post)
            elif ast.data == 'union':
                for e in ast.children:
                    self.visit_type_cond(e,None,post)
            else:
                raise Unimplemented(f'Unimplemented type tree {ast.data}')
        else:
            raise Unimplemented('Unimplemented type non-tree non-token')


    def visit_args(self, args: list[Ast]):
        for arg in args:
            if isinstance(arg, lark.Tree):
                x, t = arg.children
                name = token_value(x)
                typ = self.visit_type_bb(t)
                self.emit(Arg(Reg(name), typ))
                self.visit_type_cond(t, Reg(name), False)
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
                self.emit(Assert(val,'assert'))
                return None
            elif ast.data == 'pushfn':
                f = token_value(ast.children[0])
                args = ast.children[1:-1]
                ret = ast.children[-1]
                if f in self.func_infos:
                    raise FuncAlreadyDefinedException(f)
                self.current_func = f
                ret_register = self.target_or_next_temporary(None)
                func_info = FuncInfo(len(self.instrs), len(args), self.visit_type_bb(ret), ret_register, self.outers)
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
                val2 = self.func_infos[self.current_func].ret_register
                self.emit(Coerce(val2, val, self.func_infos[self.current_func].ret))
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
            if ast.data in ['eq','ne','lt','le','gt','ge','add','sub','mul','lookup']:
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
                        self.emit(Mov(instr.dest, vs.pop(0)))
                    elif isinstance(instr, Precondition):
                        self.emit(Assert(instr.r, 'precondition'))
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

