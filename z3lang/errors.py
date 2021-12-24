class Mistake(Exception):
    pass

class TypeException(Mistake):
    pass

class AssertionException(Mistake):
    pass

class PreconditionException(Mistake):
    pass

class PostconditionException(Mistake):
    pass

class VarNotDefined(Mistake):
    pass

class FuncNotDefined(Mistake):
    pass

class VarAlreadyDefined(Mistake):
    pass

class NotAFunction(Mistake):
    pass

class IsAFunction(Mistake):
    pass

class ArgCountMismatch(Mistake):
    pass

class NotInFunction(Mistake):
    pass

class StackEmpty(Mistake):
    pass

class Unimplemented(Mistake):
    pass



class UnexpectedException(Exception):
    pass
