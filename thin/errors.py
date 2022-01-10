class UnexpectedException(Exception):
    pass

class Mistake(Exception):
    pass

class Unimplemented(Mistake):
    pass

class ParseException(Mistake):
    pass

class TypeException(Mistake):
    pass

class ConflictException(Mistake):
    pass

class UndeclaredException(Mistake):
    pass
