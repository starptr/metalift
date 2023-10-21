from typing import List, Union

from mypy.nodes import Statement

from metalift.frontend.llvm import Driver
from metalift.ir import And, Bool, BoolLit, Call, Choose, Eq, Expr, FnDecl,FnDeclRecursive, Ge, Gt, Int, IntLit, Ite, Le, ListT, Lt, Var, Add, Mul, Sub, Implies
from tests.python.utils.utils import codegen

from gaudi_common import *

def ps_grammar(writes: List[Var], reads: List[Var]) -> Expr:
    # reads = [in_lst]
    print("reads: ")
    print(*reads)
    print("writes: ")
    print(*writes)
    input = reads[0]
    weight = reads[1]
    epsilon = reads[2]
    hidden_size = reads[3]
    #print("ps writes:")
    #print(*writes)
    ret_val = writes[0]

    an_arr = Choose(input, weight)
    an_int = Choose(epsilon, hidden_size, IntLit(-1), IntLit(0), IntLit(1), IntLit(2), IntLit(3))

    computed_arr = Choose(an_arr2_to_arr(an_arr, an_arr), an_int_and_arr_to_arr(an_int, an_arr))

    return Implies(And(Eq(ml_list_length(input), ml_list_length(weight)),
                       Gt(ml_list_length(input), IntLit(0))),
        Eq(ret_val,
            an_arr_to_int(computed_arr)))

    # Answer
    return Implies(And(Eq(ml_list_length(input), ml_list_length(weight)),
                       Gt(ml_list_length(input), IntLit(0))),
        Eq(ret_val,
            call_reduce_sum(call_scalar_mul(IntLit(2), input))))

def inv_grammar(writes: List[Var], reads: List[Var]) -> Expr:
    print("reads: ")
    print(*reads)
    print("writes: ")
    print(*writes)
    #return BoolLit(True)
    input = reads[0]
    weight = reads[1]
    epsilon = reads[2]
    hidden_size = reads[3]
    variance = writes[0]
    i = writes[1]

    an_int = Choose(epsilon, hidden_size, IntLit(-1), IntLit(0), IntLit(1), IntLit(2), IntLit(3), i, variance)
    an_arr = Choose(input, weight)
    an_arr = Choose(an_arr, ml_list_take(an_arr, an_int))

    computed_arr = Choose(an_arr2_to_arr(an_arr, an_arr), an_int_and_arr_to_arr(an_int, an_arr))

    return Implies(And(Eq(ml_list_length(input), ml_list_length(weight)),
                           Gt(ml_list_length(input), IntLit(0))),
                       And(Ge(i, IntLit(0)),
                           Le(i, ml_list_length(input)),
                           Eq(an_int,
                              an_arr_to_int(computed_arr)
                           )))

    # Answer
    return Implies(And(Eq(ml_list_length(input), ml_list_length(weight)),
                           Gt(ml_list_length(input), IntLit(0))),
                       And(Ge(i, IntLit(0)),
                           Le(i, ml_list_length(input)),
                           Eq(variance,
                              call_reduce_sum(call_scalar_mul(IntLit(2), ml_list_take(input, i)))
                           )))

if __name__ == "__main__":
    def print_line():
        print("--------------------------------------------")
        print("--------------------------------------------")
        print("--------------------------------------------")
    print_line()

    driver = Driver()
    layernorm_kernels_1 = driver.analyze(
        "tests/llvm/vllm_cuda.ll",
        "tests/llvm/vllm_cuda.loops",
        "layernorm_kernels_1",
        target_lang,
        inv_grammar,
        ps_grammar
    )
    input_var = driver.variable("input", ListT(Int()))
    weight_var = driver.variable("weight", ListT(Int()))
    epsilon_var = driver.variable("epsilon", Int())
    hidden_size_var = driver.variable("hidden_size", Int())

    layernorm_kernels_1(input_var, weight_var, epsilon_var, hidden_size_var)
    driver.synthesize(noVerify=True)

    print("\n\ngenerated code:" + layernorm_kernels_1.codegen(codegen))