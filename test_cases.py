from z3lang.session import run_script
from z3lang.errors import *
import pytest

def test_square():
    run_script("""
fn square(x:int) -> int {
    return x * x
}

assert square(-2) == 4
""")

def test_square_print():
    assert run_script("""
fn square(x:int) -> int {
    return x * x
}

square(-2)
""") == """Type: int
{[4]}
"""


def test_square_assertion_failure():
    with pytest.raises(AssertionException):
        run_script("""
    fn square(x:int) -> int {
        return x * x
    }

    assert square(-2) == 5
    """)

def test_square_nonneg():
    run_script("""
fn square(x:int) -> int {
    return x * x
}

fn f(x:int) -> int {
    assert square(x) >= 0
    return 0
}
""")

def test_range_unreachable():
    run_script("""
fn f(x:range 0) -> int {
    unreachable
}
""")

def test_range_reachable():
    with pytest.raises(ReachabilityException):
        run_script("""
    fn f(x:range 5) -> int {
        unreachable
    }
    """)

def test_multiple_statements():
    run_script("""
fn f(x:int) -> int {
    y = -x
    return x * y
}

assert f(3) == -9
""")

def test_range_ret():
    run_script("""
fn f(x:range 3) -> range 3 {
    return x * x - x
}

assert f(2) == 2
""")

def test_out_of_range_ret():
    with pytest.raises(PostconditionException):
        run_script("""
fn f(x:range 3) -> range 2 {
    return x * x - x
}
""")

def test_range_precondition():
    with pytest.raises(PreconditionException):
        run_script("""
    fn f(x:range 3) -> range 3 {
        return x * x - x
    }

    assert f(4) == 12
    """)

def test_dependent():
    run_script("""
fn f(x:range 5, y:range x) -> range 8 {
    return x + y
}
assert f(4,3) == 7
""")

def test_tuple_eq():
    run_script("""
assert [1,true,[2,3]] == [1,true,[2,3]]
""")

def test_tuple_ret():
    run_script("""
fn combine(x:int, y:bool) -> tuple[int,bool] {
    return [x,y]
}
assert combine(4,true) == [4,true]
""")

def test_array_ret():
    run_script("""
fn combine(x:int, y:int) -> array int {
    return [x,y]
}
assert combine(4,5) == [4,5]
assert [4,5] == combine(4,5)
""")
