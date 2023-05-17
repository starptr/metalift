from functools import reduce
from metalift.ir import *
from metalift.analysis import CodeInfo, analyze
from metalift.synthesis_common import SynthesisFailed

from metalift.synthesize_auto import synthesize

LIST_BOUND = 4

CONV2D2X2 = "conv2d2x2"
CONV2D2X2_HELPER = "conv2d2x2_helper"
CONV2D2X2_INNER = "conv2d2x2_inner"
DOTPROD2X2 = "dotprod_2x2"
SLICE_COPY_2X2 = "slide_copy_2x2"

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

def ml_list_list_get(lst, i):
    return Call("list_list_get", ListT(Int()), lst, i)

def ml_list_list_length(lst):
    return Call("list_list_length", Int(), lst)

def ml_list_list_prepend(e, lst):
    return Call("list_list_prepend", ListT(ListT(Int())), e, lst)

def ml_list_list_empty():
    return Call("list_list_empty", ListT(ListT(Int())))

def ml_min(a, b):
    return Ite(Lt(a, b), a, b)

def ml_dotprod2x2(mat, kernel, i, j):
    return Call(DOTPROD2X2, Int(), mat, kernel, i, j)

def ml_conv2d2x2(mat, kernel):
    return Call(CONV2D2X2, ListT(ListT(Int())), mat, kernel)

def ml_conv2d2x2_helper(mat, kernel, i, stopping):
    return Call(CONV2D2X2_HELPER, ListT(ListT(Int())), mat, kernel, i, stopping)

def ml_conv2d2x2_inner(mat, kernel, i, j, stopping):
    return Call(CONV2D2X2_INNER, ListT(Int()), mat, kernel, i, j, stopping)

def grammar(ci: CodeInfo):
    name = ci.name
    print("NAME: ", name)
    print("INV VARS MV HERE")
    print(*ci.modifiedVars)
    print("MV len: ", len(ci.modifiedVars))
    print("INV VARS RV HERE")
    print(*ci.readVars)

    unknown_const = Choose(IntLit(0), IntLit(1), IntLit(2))
    kernel_r1 = ml_list_prepend(unknown_const, ml_list_prepend(unknown_const, ml_list_empty()))
    kernel_r2 = kernel_r1
    kernel = ml_list_list_prepend(kernel_r1, ml_list_list_prepend(kernel_r2, ml_list_list_empty()))

    if name.startswith("inv0"):
        return Synth(name, Eq(ci.readVars[0], ci.modifiedVars[2]), *ci.modifiedVars, *ci.readVars)
    elif name.startswith("inv1"):
        return Synth(name, Eq(ci.readVars[0], ci.modifiedVars[2]), *ci.modifiedVars, *ci.readVars)
    else:
        an_output = ci.modifiedVars[0]
        an_input = ci.readVars[0]
        valid = And(Gt(ml_list_list_length(an_input), IntLit(1)),
                    Gt(ml_list_length(ml_list_list_get(an_input, IntLit(0))), IntLit(1)))
        ans = ml_conv2d2x2(an_input, kernel)
        check_ans = Eq(ans, an_output)
        summary = Implies(valid, check_ans)
        return Synth(name, summary, *ci.modifiedVars, *ci.readVars)

def targetLang():
    mat = Var("mat", ListT(ListT(Int())))
    kernel = Var("kernel", ListT(ListT(Int())))
    i = Var("i", Int())
    j = Var("j", Int())
    stopping = Var("stopping", Int())

    def dotprod2x2_body(mat, kernel, i, j):
        row1 = ml_list_list_get(mat, i)
        row2 = ml_list_list_get(mat, Add(i, IntLit(1)))
        a = ml_list_get(row1, j)
        b = ml_list_get(row1, Add(j, IntLit(1)))
        c = ml_list_get(row2, j)
        d = ml_list_get(row2, Add(j, IntLit(1)))

        krow1 = ml_list_list_get(kernel, IntLit(0))
        krow2 = ml_list_list_get(kernel, IntLit(1))
        ka = ml_list_get(krow1, IntLit(0))
        kb = ml_list_get(krow1, IntLit(1))
        kc = ml_list_get(krow2, IntLit(0))
        kd = ml_list_get(krow2, IntLit(1))

        pa = Mul(a, ka)
        pb = Mul(b, kb)
        pc = Mul(c, kc)
        pd = Mul(d, kd)
        return Add(Add(pa, pb), Add(pc, pd))
    dotprod2x2 = FnDecl(DOTPROD2X2, Int(), dotprod2x2_body(mat, kernel, i, j), mat, kernel, i, j)

    def conv2d2x2Helper_body(mat, kernel, i, stopping):
        last_valid_i = Sub(stopping, IntLit(1))
        base_case_or = lambda general_case: Ite(Gt(i, last_valid_i), ml_list_empty(), general_case)

        last_valid_j = Sub(ml_list_length(ml_list_list_get(mat, IntLit(0))), ml_list_length(ml_list_list_get(kernel, IntLit(0))))
        cur_row = ml_conv2d2x2_inner(mat, kernel, i, IntLit(0), Add(last_valid_j, IntLit(1)))
        recursed_row = ml_conv2d2x2_helper(mat, kernel, Add(i, IntLit(1)), stopping)
        general_answer = ml_list_list_prepend(cur_row, recursed_row)

        return base_case_or(general_answer)
    conv2d2x2_helper = FnDeclRecursive(CONV2D2X2_HELPER, ListT(ListT(Int())), conv2d2x2Helper_body(mat, kernel, i, stopping), mat, kernel, i, stopping)

    def conv2d2x2Inner_body(mat, kernel, i, j, stopping):
        last_valid_j = Sub(stopping, IntLit(1))
        base_case_2_or = lambda general_case: Ite(Gt(j, last_valid_j), ml_list_empty(), general_case)

        cur_term = ml_dotprod2x2(mat, kernel, i, j)
        recursed = ml_conv2d2x2_inner(mat, kernel, i, Add(j, IntLit(1)), stopping)
        general_answer_2 = ml_list_prepend(cur_term, recursed)
        return base_case_2_or(general_answer_2)
    conv2d2x2_inner = FnDeclRecursive(CONV2D2X2_INNER, ListT(Int()), conv2d2x2Inner_body(mat, kernel, i, j, stopping), mat, kernel, i, j, stopping)

    def conv2d2x2_body(mat, kernel):
        last_valid_i = Sub(ml_list_list_length(mat), ml_list_list_length(kernel)) # TODO: subtract kernel
        return ml_conv2d2x2_helper(mat, kernel, IntLit(0), Add(last_valid_i, IntLit(1)))
    conv2d2x2 = FnDeclRecursive(CONV2D2X2, ListT(ListT(Int())), conv2d2x2_body(mat, kernel), mat, kernel)

    return [dotprod2x2, conv2d2x2, conv2d2x2_inner, conv2d2x2_helper]

def runner(basename):
    filename = f"tests/{basename}.ll"
    fnName = "test"
    loopsFile = f"tests/{basename}.loops"
    cvcPath = "cvc5"

    (vars, invAndPs, preds, vc, loopAndPsInfo) = analyze(filename, fnName, loopsFile)

    candidates = []

    invAndPs = [grammar(ci) for ci in loopAndPsInfo]
    lang = targetLang()
    candidates = synthesize(basename, lang, vars, invAndPs, preds, vc, loopAndPsInfo, cvcPath, listBound=LIST_BOUND, noVerify=True)

    for c in candidates:
        print(c)

runner("conv2d")
