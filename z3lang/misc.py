import z3

def or_zs(zs):
    if len(zs) == 0:
        return z3.BoolVal(False)
    elif len(zs) == 1:
        return zs[0]
    else:
        return z3.Or(*zs)

def and_zs(zs):
    if len(zs) == 0:
        return z3.BoolVal(True)
    elif len(zs) == 1:
        return zs[0]
    else:
        return z3.And(*zs)

def eq_zs(zs0, zs1):
    if len(zs0) != len(zs1):
        raise UnexpectedException(f'eq_zs: lengths are {zs0} and {zs1}')
    return and_zs([z0 == z1 for z0,z1 in zip(zs0,zs1)])

def sequence_zs(sort, zs):
    if len(zs) == 0:
        return z3.Empty(sort)
    elif len(zs) == 1:
        return z3.Unit(zs[0])
    else:
        return z3.Concat(*[z3.Unit(z) for z in zs])
