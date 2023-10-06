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

def ps_grammar(ret_val: Var, writes: List[Var], reads: List[Var]) -> Expr:
    # reads = [in_lst]
    print("reads: ")
    print(*reads)
    base = reads[0]
    active = reads[1]
    opacity = reads[2]
    # give answer using reads[[#]]
    #Call("list_eq", Bool(), ret_val, )
    return Implies(And(Eq(ml_list_length(base), ml_list_length(active)), Gt(ml_list_length(base), IntLit(0))),
        Call("list_eq", Bool(), ret_val, call_vector_add(call_scalar_mul(opacity, active), call_scalar_mul(Sub(IntLit(1), opacity), base))))

def inv_grammar(v: Var, writes: List[Var], reads: List[Var]) -> Expr:
    print("writes: ")
    print(*writes)
    print(v)
    #return BoolLit(True)
    base = reads[0]
    active = reads[1]
    opacity = reads[2]
    out = call_vector_add(call_scalar_mul(opacity, active), call_scalar_mul(Sub(IntLit(1), opacity), base))
    def invariant(base, active, out, opacity, pixel):
        return And(Ge(pixel, IntLit(0)),
            Le(pixel, ml_list_length(active)),
            Eq(ml_list_take(out, pixel),
                call_vector_add(call_scalar_mul(opacity, ml_list_take(active, pixel)),
                    call_scalar_mul(Sub(IntLit(1), opacity), ml_list_take(base, pixel)))))
    if v.name() == "i":
        return Implies(And(Eq(ml_list_length(base), ml_list_length(active)), Gt(ml_list_length(base), IntLit(0))), invariant(base, active, out, opacity, v))
    elif v.name() == "ref.tmp":
        return BoolLit(True)
    else:
        return Implies(And(Eq(ml_list_length(base), ml_list_length(active)), Gt(ml_list_length(base), IntLit(0))), BoolLit(True))
    ## This grammar func could be called with v as `i` or `out_lst`, and we really only want to generate this grammar once.
    #if v.name() != "i":
    #    return BoolLit(True)

    ## writes = [out_lst, i]
    ## reads = [in]
    #out_lst, i = writes[0], writes[1]
    #in_lst = reads[0]
    #lst = Choose(in_lst, out_lst, Call("Select", ListT(Int()), in_lst))
    #lst_inv_cond = Choose(
    #    Call(
    #        "list_eq",
    #        Bool(),
    #        Call(
    #            "list_append",
    #            ListT(Int()),
    #            lst,
    #            Call(
    #                "Select",
    #                ListT(Int()),
    #                Call("list_tail", ListT(Int()), lst, i),
    #            ),
    #        ),
    #        lst,
    #    ),
    #    Call(
    #        "list_eq",
    #        Bool(),
    #        Call(
    #            "list_concat",
    #            ListT(Int()),
    #            out_lst,
    #            Call("list_tail", ListT(Int()), lst, i),
    #        ),
    #        lst,
    #    ),
    #)

    #in_lst_length = Call("list_length", Int(), in_lst)
    #i_bound_in_lst_length_cond = Choose(
    #    Ge(i, in_lst_length),
    #    Le(i, in_lst_length),
    #    Gt(i, in_lst_length),
    #    Lt(i, in_lst_length),
    #    Eq(i, in_lst_length),
    #)
    #i_bound_int_lit = Choose(IntLit(0), IntLit(1))
    #i_bound_int_lit_cond = Choose(
    #    Ge(i, i_bound_int_lit),
    #    Le(i, i_bound_int_lit),
    #    Gt(i, i_bound_int_lit),
    #    Lt(i, i_bound_int_lit),
    #    Eq(i, i_bound_int_lit),
    #)
    #return Choose(And(And(i_bound_int_lit_cond, i_bound_in_lst_length_cond), lst_inv_cond))

if __name__ == "__main__":
    driver = Driver()
    test = driver.analyze(
        "tests/llvm/normalBlendf.ll",
        "tests/llvm/normalBlendf.loops",
        "test",
        target_lang,
        inv_grammar,
        ps_grammar
    )

    base_var = driver.variable("base", ListT(Int()))
    active_var = driver.variable("active", ListT(Int()))
    opacity_var = driver.variable("opacity", Int())

    test(base_var, active_var, opacity_var)

    def wrap_inv(modifiedVar_to_expr):
        assert "agg.result" in modifiedVar_to_expr
        assert "ref.tmp" in modifiedVar_to_expr
        assert "i" in modifiedVar_to_expr
        Implies(BoolLit(True), modifiedVar_to_expr["i"])

    comb_invariants = {
        "test_inv0": wrap_inv,
    }
    driver.synthesize(comb_invariants)

    print("\n\ngenerated code:" + test.codegen(codegen))