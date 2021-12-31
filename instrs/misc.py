import z3

def and_zs(zs: list[z3.ExprRef]) -> z3.ExprRef:
    if len(zs) == 0:
        return z3.BoolVal(True)
    elif len(zs) == 1:
        return zs[0]
    else:
        return z3.And(*zs)
