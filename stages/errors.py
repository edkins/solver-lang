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
