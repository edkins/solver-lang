import ctypes
from typing import Any

class Z3Exception(Exception):
    value: Any
    def __init__(self, value) -> None: ...

class ContextObj(ctypes.c_void_p):
    def __init__(self, context) -> None: ...
    def from_param(obj): ...

class Config(ctypes.c_void_p):
    def __init__(self, config) -> None: ...
    def from_param(obj): ...

class Symbol(ctypes.c_void_p):
    def __init__(self, symbol) -> None: ...
    def from_param(obj): ...

class Sort(ctypes.c_void_p):
    def __init__(self, sort) -> None: ...
    def from_param(obj): ...

class FuncDecl(ctypes.c_void_p):
    def __init__(self, decl) -> None: ...
    def from_param(obj): ...

class Ast(ctypes.c_void_p):
    def __init__(self, ast) -> None: ...
    def from_param(obj): ...

class Pattern(ctypes.c_void_p):
    def __init__(self, pattern) -> None: ...
    def from_param(obj): ...

class Model(ctypes.c_void_p):
    def __init__(self, model) -> None: ...
    def from_param(obj): ...

class Literals(ctypes.c_void_p):
    def __init__(self, literals) -> None: ...
    def from_param(obj): ...

class Constructor(ctypes.c_void_p):
    def __init__(self, constructor) -> None: ...
    def from_param(obj): ...

class ConstructorList(ctypes.c_void_p):
    def __init__(self, constructor_list) -> None: ...
    def from_param(obj): ...

class GoalObj(ctypes.c_void_p):
    def __init__(self, goal) -> None: ...
    def from_param(obj): ...

class TacticObj(ctypes.c_void_p):
    def __init__(self, tactic) -> None: ...
    def from_param(obj): ...

class ProbeObj(ctypes.c_void_p):
    def __init__(self, probe) -> None: ...
    def from_param(obj): ...

class ApplyResultObj(ctypes.c_void_p):
    def __init__(self, obj) -> None: ...
    def from_param(obj): ...

class StatsObj(ctypes.c_void_p):
    def __init__(self, statistics) -> None: ...
    def from_param(obj): ...

class SolverObj(ctypes.c_void_p):
    def __init__(self, solver) -> None: ...
    def from_param(obj): ...

class SolverCallbackObj(ctypes.c_void_p):
    def __init__(self, solver) -> None: ...
    def from_param(obj): ...

class FixedpointObj(ctypes.c_void_p):
    def __init__(self, fixedpoint) -> None: ...
    def from_param(obj): ...

class OptimizeObj(ctypes.c_void_p):
    def __init__(self, optimize) -> None: ...
    def from_param(obj): ...

class ModelObj(ctypes.c_void_p):
    def __init__(self, model) -> None: ...
    def from_param(obj): ...

class AstVectorObj(ctypes.c_void_p):
    def __init__(self, vector) -> None: ...
    def from_param(obj): ...

class AstMapObj(ctypes.c_void_p):
    def __init__(self, ast_map) -> None: ...
    def from_param(obj): ...

class Params(ctypes.c_void_p):
    def __init__(self, params) -> None: ...
    def from_param(obj): ...

class ParamDescrs(ctypes.c_void_p):
    def __init__(self, paramdescrs) -> None: ...
    def from_param(obj): ...

class FuncInterpObj(ctypes.c_void_p):
    def __init__(self, f) -> None: ...
    def from_param(obj): ...

class FuncEntryObj(ctypes.c_void_p):
    def __init__(self, e) -> None: ...
    def from_param(obj): ...

class RCFNumObj(ctypes.c_void_p):
    def __init__(self, e) -> None: ...
    def from_param(obj): ...