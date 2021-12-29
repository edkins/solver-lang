class UnexpectedException(Exception):
    pass

class Mistake(Exception):
    pass

class Unimplemented(Mistake):
    pass

class AssertionException(Mistake):
    pass

class TypeException(Mistake):
    pass

class PreconditionException(Mistake):
    pass

class PostconditionException(Mistake):
    pass

class ReachabilityException(Mistake):
    pass

class IncompleteFunctionException(Mistake):
    pass

class FuncAlreadyDefinedException(Mistake):
    pass

class VarAlreadyDefinedException(Mistake):
    pass

class VarFuncCollisionException(Mistake):
    pass

class VarNotDefinedException(Mistake):
    pass

class FuncNotDefinedException(Mistake):
    pass

class TopLevelReturnException(Mistake):
    pass
