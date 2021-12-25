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
    return x *y
}

assert f(3) == -9
""")

