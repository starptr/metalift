from metalift.ir import *
from metalift.analysis import CodeInfo, analyze
from metalift.synthesis_common import SynthesisFailed

from metalift.synthesize_auto import synthesize

LIST_BOUND = 4

CONV2D2X2 = "conv2d2x2"
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

def ml_min(a, b):
    return Ite(Lt(a, b), a, b)

def ml_dotprod2x2(mat, kernel, i, j):
    return Call(DOTPROD2X2, Int(), mat, kernel, i, j)

def ml_conv2d2x2(mat, kernel, i, j):
    return Call(CONV2D2X2, ListT(ListT(Int())), mat, kernel, i, j)

def targetLang():
    mat = Var("mat", ListT(ListT(Int())))
    kernel = Var("kernel", ListT(ListT(Int())))
    i = Var("i", Int())
    j = Var("j", Int())

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

    def conv2d2x2_body(mat, kernel, i, j):
        last_valid_i = ml_list_list_length(mat)
        last_valid_j = ml_list_length(ml_list_list_get(mat, IntLit(0)))
        base_case_or = lambda general_case: Ite(Gt(i, last_valid_i), ml_list_empty(), general_case)
        base_case_2_or = lambda general_case: Ite(Gt(j, last_valid_j), ml_list_empty(), general_case)

        cur_term = ml_dotprod2x2(mat, kernel, i, j)
        recursed = ml_conv2d2x2(mat, kernel, i, Add(j, IntLit(1)))
        general_answer_2 = ml_list_prepend(cur_term, recursed)

        cur_row = base_case_2_or(general_answer_2)
        recursed_row = ml_conv2d2x2(mat, kernel, Add(i, IntLit(1)), j)
        general_answer = ml_list_list_prepend(cur_row, recursed_row)

        return base_case_or(general_answer)
    conv2d2x2 = FnDeclRecursive(CONV2D2X2, ListT(ListT(Int())), conv2d2x2_body(mat, kernel, i, j), mat, kernel, i, j)

    return [dotprod2x2, conv2d2x2]
