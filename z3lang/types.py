import z3

def n_varnames(x, n):
    if n == 0:
        return []
    elif n == 1:
        return [x]
    else:
        return [f'{x}.{i}' for i in range(n)]

class Type:
    def __init__(self, sorts, name, it_restrictions, interp):
        self.sorts = sorts
        self.name = name
        self.it_restrictions = it_restrictions
        self.interp = interp

    def __repr__(self):
        return self.name

    def varnames(self, x):
        n = len(self.sorts)
        return n_varnames(x, n)

    def vars_named(self, names):
        if len(names) != len(self.sorts):
            raise UnexpectedException(f'Expecting {len(self.sorts)} names, got {len(names)}')
        return [z3.Const(names[i], self.sorts[i]) for i in range(len(names))]

    def vars(self, x):
        names = self.varnames(x)
        return self.vars_named(names)

    def zs_restrictions(self, zs):
        if len(zs) != len(self.sorts):
            raise UnexpectedException(f'Expected {len(self.sorts)} exprs, got {len(exprs)}')
        substitutions = list(zip(self.vars('.it'), zs))
        return [z3.substitute(r, substitutions) for r in self.it_restrictions]

    def restrictions(self, name):
        return self.zs_restrictions(self.vars(name))

B = Type([z3.BoolSort()], 'bool', [], None)
Z = Type([z3.IntSort()], 'int', [], None)

def range_type(upper):
    return Type([z3.IntSort()], f'range {upper}', [z3.Int('.it') >= 0, z3.Int('.it') < upper], None)

class TupleInterp:
    def __init__(self, interps):
        self.interps = interps

    def __eq__(self, other):
        return isinstance(other, TupleInterp) and self.interps == other.interps

def tuple_type(ts):
    name = 'tuple[' + ','.join((t.name for t in ts)) + ']'
    interp = TupleInterp([t.interp for t in ts])
    sorts = []
    restrictions = []
    n = sum((len(t.sorts) for t in ts))
    our_varnames = n_varnames('.it', n)
    count = 0
    for t in ts:
        sorts += t.sorts
        restrictions += t.zs_restrictions(t.vars_named(our_varnames[count:count+len(t.sorts)]))
        count += len(t.sorts)

    tuple_sort = z3.TupleSort(name, sorts)[0]
    return Type([tuple_sort], name, restrictions, interp)

def array_type(t):
    if len(t.sorts) != 1:
        raise Unimplemented('Can only construct arrays of things with 1 sort')
    if len(t.it_restrictions) != 0:
        raise Unimplemented('Cannot currently construct arrays on things with restrictions')
    return Type([z3.SeqSort(t.sorts[0])], f'array {t}', [], None)

class Arg:
    def __init__(self, name, typ):
        self.name = name
        self.typ = typ

    def vars(self):
        return self.typ.vars(self.name)

    def expr(self):
        from z3lang.expr import Expr
        return Expr(self.typ, *self.vars())

    def restrictions(self):
        return self.typ.restrictions(self.name)

    def __repr__(self):
        return f'{self.name}:{self.typ}'

class Func:
    def __init__(self, args, ret):
        self.args = args
        self.ret = ret

    def func(self, f, retsort):
        sorts = []
        for arg in self.args:
            sorts += arg.typ.sorts
        sorts.append(retsort)
        return z3.Function(f, *sorts)

    def funcs(self, f):
        result = []
        for name,sort in zip(self.ret.varnames(f), self.ret.sorts):
            result.append(self.func(name, sort))
        return result

    def preconditions(self):
        result = []
        for arg in self.args:
            for restriction in arg.restrictions():
                result.append(restriction)
        return result

    def postconditions(self, retval):
        return self.ret.zs_restrictions(retval.zs)

    def __repr__(self):
        return f'{self.args} -> {self.ret}'
