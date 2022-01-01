from instrs.session import run_script
from instrs.errors import *
import pytest

def test_num_eq():
    assert "True : bool\n" == run_script("42 == 42")

def test_num_neq():
    assert "False : bool\n" == run_script("32 == 42")

def test_tuple_eq():
    assert "True : bool\n" == run_script("[1,true] == [1,true]")

def test_tuple_neq():
    assert "False : bool\n" == run_script("[1,true] == [1,false]")

def test_tuple_neq_len():
    assert "False : bool\n" == run_script("[1,true] == [1]")

def test_tuple_neq_empty():
    assert "False : bool\n" == run_script("[] == [1]")

def test_empty_tuple():
    assert "() : tuple[]\n" == run_script("[]")

def test_singleton_tuple():
    assert "(1,) : tuple[int]\n" == run_script("[1]")

def test_singleton_array():
    assert "[1] : array[int]\n" == run_script("arr[1]")

def test_pair_array():
    assert "[1, 2] : array[int]\n" == run_script("arr[1,2]")

def test_mismatched_pair_array():
    assert "[1, False] : array[union[bool,int]]\n" == run_script("arr[1,false]")

def test_mismatched_array_of_arrays():
    assert "[[1], [False]] : array[array[union[bool,int]]]\n" == run_script("arr[arr[1],arr[false]]")

def test_array_of_tuple_and_array():
    assert "[[1], [2, 3]] : array[array[int]]\n" == run_script("arr[arr[1],[2,3]]")

def test_array_of_tuple_and_longer_tuple():
    assert "[(1,), (2, 3)] : array[union[tuple[int,int],tuple[int]]]\n" == run_script("arr[[1],[2,3]]")

def test_not_actually_empty_array():
    assert "() : tuple[]\n" == run_script("arr[]")

def test_mismatched_eq():
    assert "False : bool\n" == run_script("1 == true")

def test_mismatched_tuple_eq():
    assert "False : bool\n" == run_script("1 == [1]")

def test_tuple_eq_array():
    assert "True : bool\n" == run_script("[1] == arr[1]")

def test_assert_true():
    run_script("""
x = 1
assert x == 1
""")

def test_assert_false():
    with pytest.raises(AssertionException):
        run_script("""
    x = 1
    assert x == 2
    """)

'''
def test_square():
    run_script("""
fn square(x:int) -> int {
    return x * x
}

assert square(-2) == 4
""")

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

def test_no_return():
    with pytest.raises(IncompleteFunctionException):
        run_script("""
fn f() -> int {
}
""")

def test_array_eq():
    run_script("""
fn combine(x:int, y:int) -> array int {
    return [x,y]
}
assert combine(4,5) == combine(4,5)
""")

def test_mismatched_array_element():
    with pytest.raises(TypeException):
        run_script("""
fn int_tuple(x:int) -> tuple[int] {
    return [x]
}
fn array_tuple(x:array int) -> tuple[array int] {
    return [x]
}
assert int_tuple(0) == array_tuple(0)
""")

def test_lists_of_lists():
    run_script("""
fn int_tuple(x:int) -> tuple[int] {
    return [x]
}
fn int_array(x:int) -> array int {
    return [x]
}
fn tuple_tuple(x:tuple[int]) -> tuple[tuple[int]] {
    return [x]
}
fn tuple_array(x:tuple[int]) -> array tuple[int] {
    return [x]
}
fn array_tuple(x:array int) -> tuple[array int] {
    return [x]
}
fn array_array(x:array int) -> array (array int) {
    return [x]
}
assert int_tuple(0) == int_tuple(0)
assert int_tuple(0) == int_array(0)
assert tuple_tuple(int_tuple(0)) == tuple_tuple(int_tuple(0))
assert tuple_tuple(int_tuple(0)) == tuple_tuple(int_array(0))
assert tuple_array(int_tuple(0)) == tuple_array(int_tuple(0))
assert tuple_array(int_tuple(0)) == tuple_array(int_array(0))
assert array_tuple(int_tuple(0)) == array_tuple(int_tuple(0))
assert array_tuple(int_tuple(0)) == array_tuple(int_array(0))
assert array_array(int_tuple(0)) == array_array(int_tuple(0))
assert array_array(int_tuple(0)) == array_array(int_array(0))
""")

def test_tuple_fixed_index():
    run_script("""
assert [1,false][0] == 1
assert [1,false][1] == false
""")

def test_tuple_var_index():
    run_script("""
fn f(i:range 3) -> int {
    assert [1,2,3][i] < 4
    return i
}
""")

def test_union_actually_int():
    run_script("""
fn f() -> union[int,bool] {
    return 34
}
assert f() + 1 == 35
""")

'''
