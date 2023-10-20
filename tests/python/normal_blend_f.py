from typing import List, Union

from mypy.nodes import Statement

from metalift.frontend.llvm import Driver
from metalift.ir import And, Bool, BoolLit, Call, Choose, Eq, Expr, FnDecl,FnDeclRecursive, Ge, Gt, Int, IntLit, Ite, Le, ListT, Lt, Var, Add, Mul, Sub, Implies
from tests.python.utils.utils import codegen

VECTORADD = "vector_add"
SCALARMUL = "scalar_mul"

def ml_list_get(lst, i):
    return Call("list_get", Int(), lst, i)

def ml_list_head(lst):
    return ml_list_get(lst, IntLit(0))

def ml_list_tail(lst, i):
    return Call("list_tail", ListT(Int()), lst, i)

def ml_list_prepend(e, lst):
    return Call("list_prepend", ListT(Int()), e, lst)

def ml_list_length(lst):
    return Call("list_length", Int(), lst)

def ml_list_empty():
    return Call("list_empty", ListT(Int()))

def ml_list_take(lst, i):
    return Call("list_take", ListT(Int()), lst, i)

def call_vector_add(left, right):
    return Call(VECTORADD, ListT(Int()), left, right)

def call_scalar_mul(left, right):
    return Call(SCALARMUL, ListT(Int()), left, right)

def target_lang() -> List[Union[FnDecl, FnDeclRecursive]]:
    x = Var("x", ListT(Int()))
    y = Var("y", ListT(Int()))
    a = Var("a", Int())
    b = Var("b", Int())

    def vector_add_body(left, right):
        vec_size = ml_list_length(left)
        cur = Add(ml_list_head(left), ml_list_head(right))
        left_rest = ml_list_tail(left, IntLit(1))
        right_rest = ml_list_tail(right, IntLit(1))
        recursed = call_vector_add(left_rest, right_rest)
        general_answer = ml_list_prepend(cur, recursed)
        return Ite(Lt(vec_size, IntLit(1)), ml_list_empty(), general_answer)
    vector_add = FnDeclRecursive(VECTORADD, ListT(Int()), vector_add_body(x, y), x, y)

    def scalar_mul_body(scalar, arr):
        vec_size = ml_list_length(arr)
        cur = Mul(scalar, ml_list_head(arr))
        arr_rest = ml_list_tail(arr, IntLit(1))
        recursed = call_scalar_mul(scalar, arr_rest)
        general_answer = ml_list_prepend(cur, recursed)
        return Ite(Lt(vec_size, IntLit(1)), ml_list_empty(), general_answer)
    scalar_mul = FnDeclRecursive(SCALARMUL, ListT(Int()), scalar_mul_body(a, x), a, x)

    return [vector_add, scalar_mul]

def ps_grammar(writes: List[Var], reads: List[Var]) -> Expr:
    # reads = [in_lst]
    #print("reads: ")
    #print(*reads)
    base = reads[0]
    active = reads[1]
    opacity = reads[2]
    #print("ps writes:")
    #print(*writes)
    ret_val = writes[0]
    # give answer using reads[[#]]
    #Call("list_eq", Bool(), ret_val, )
    return Implies(And(Eq(ml_list_length(base), ml_list_length(active)), Gt(ml_list_length(base), IntLit(0))),
        Call("list_eq", Bool(), ret_val, call_vector_add(call_scalar_mul(opacity, active), call_scalar_mul(Sub(IntLit(1), opacity), base))))

def inv_grammar(writes: List[Var], reads: List[Var]) -> Expr:
    print("writes: ")
    print(*writes)
    #return BoolLit(True)
    base = reads[0]
    active = reads[1]
    opacity = reads[2]
    agg_result = writes[0]
    ref_tmp = writes[1]
    i = writes[2]

    return Implies(And(Eq(ml_list_length(base), ml_list_length(active)),
                           Gt(ml_list_length(base), IntLit(0))),
                       And(Ge(i, IntLit(0)),
                           Le(i, ml_list_length(active)),
                           Eq(agg_result,
                              call_vector_add(call_scalar_mul(opacity, ml_list_take(active, i)),
                                    call_scalar_mul(Sub(IntLit(1), opacity), ml_list_take(base, i)))
                              )))

if __name__ == "__main__":
    driver = Driver()
    test = driver.analyze(
        "tests/llvm/normal_blend_f.ll",
        "tests/llvm/normal_blend_f.loops",
        "test",
        target_lang,
        inv_grammar,
        ps_grammar
    )

    base_var = driver.variable("base", ListT(Int()))
    active_var = driver.variable("active", ListT(Int()))
    opacity_var = driver.variable("opacity", Int())

    test(base_var, active_var, opacity_var)

    driver.synthesize(noVerify=True)

    print("\n\ngenerated code:" + test.codegen(codegen))