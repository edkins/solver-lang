class UnexpectedException(Exception):
    pass

class Mistake(Exception):
    pass

class Unimplemented(Mistake):
    pass

class TypeException(Mistake):
    pass

class NoSuchRegException(Mistake):
    pass

class RegAlreadySetException(Mistake):
    pass

class NoOptionsException(Mistake):
    pass

class AssertionException(Mistake):
    pass

class OutOfBoundsException(Mistake):
    pass

class VarAlreadyDefinedException(Mistake):
    pass

class ParseException(Mistake):
    pass

class ModeException(Mistake):
    pass

class StackEmptyException(Mistake):
    pass

class NotInFunctionException(Mistake):
    pass

class FuncAlreadyDefinedException(Mistake):
    pass

class FuncNotDefinedException(Mistake):
    pass

class ArgCountMismatchException(Mistake):
    pass

class DuplicateReturnStatementException(Mistake):
    pass

class ReachabilityException(Mistake):
    pass
