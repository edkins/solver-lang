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
