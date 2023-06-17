from functools import reduce
from metalift.ir import *
from metalift.analysis import CodeInfo, analyze
from metalift.synthesis_common import SynthesisFailed

from metalift.synthesize_auto import synthesize

LIST_BOUND = 4

CONV2D2X2 = "conv2d2x2"
CONV2D2X2_2 = "conv2d2x2_2"
CONV2D2X2_HELPER = "conv2d2x2_helper"
CONV2D2X2_HELPER2 = "conv2d2x2_helper2"
CONV2D2X2_INNER = "conv2d2x2_inner"
CONV2D2X2_INNER2 = "conv2d2x2_inner2"
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

def ml_list_list_take(lst, i):
    return Call("list_list_take", ListT(ListT(Int())), lst, i)

def ml_min(a, b):
    return Ite(Lt(a, b), a, b)

def ml_dotprod2x2(mat, kernel, i, j):
    return Call(DOTPROD2X2, Int(), mat, kernel, i, j)

def ml_conv2d2x2(mat, kernel):
    return Call(CONV2D2X2, ListT(ListT(Int())), mat, kernel)

def ml_conv2d2x2_2(mat, kernel):
    return Call(CONV2D2X2_2, ListT(ListT(Int())), mat, kernel)

def ml_conv2d2x2_helper(mat, kernel, i, stopping):
    return Call(CONV2D2X2_HELPER, ListT(ListT(Int())), mat, kernel, i, stopping)

def ml_conv2d2x2_helper2(mat, kernel, i, j):
    return Call(CONV2D2X2_HELPER2, ListT(ListT(Int())), mat, kernel, i, j)

def ml_conv2d2x2_inner(mat, kernel, i, j, stopping):
    return Call(CONV2D2X2_INNER, ListT(Int()), mat, kernel, i, j, stopping)

def ml_conv2d2x2_inner2(mat, kernel, i, j):
    return Call(CONV2D2X2_INNER2, ListT(Int()), mat, kernel, i, j)

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

    const_kernel_r1 = ml_list_prepend(IntLit(-1), ml_list_prepend(IntLit(1), ml_list_empty()))
    const_kernel_r2 = ml_list_prepend(IntLit(-1), ml_list_prepend(IntLit(1), ml_list_empty()))
    const_kernel = ml_list_list_prepend(const_kernel_r1, ml_list_list_prepend(const_kernel_r2, ml_list_list_empty()))

    if name.startswith("inv0"):
        an_output_i32 = Choose(ci.modifiedVars[1], ci.modifiedVars[3])
        an_output_list = ci.modifiedVars[0]
        an_output_nlist = ci.modifiedVars[2]
        an_input_nlist = ci.readVars[0]
        #valid = Gt(ml_list_list_length(an_input_nlist), IntLit(1))
        #preloop = Ge(an_output_i32, IntLit(0))
        #postloop = Lt(an_output_i32, ml_list_list_length(an_input_nlist))
        #induction = Eq(an_output_nlist, ml_conv2d2x2_helper(an_input_nlist,
        #                                                    kernel,
        #                                                    IntLit(0),
        #                                                    Add(an_output_i32, IntLit(1))))
        #summary = Implies(valid, And(preloop, And(postloop, induction)))
        #return Synth(name, summary, *ci.modifiedVars, *ci.readVars)
        valid = Eq(ml_list_list_length(an_input_nlist), IntLit(3))
        preloop = Ge(an_output_i32, IntLit(0))
        postloop = Lt(an_output_i32, ml_list_length(an_input_nlist))
        mat = ml_list_list_take(an_input_nlist, Add(an_output_i32, IntLit(1)))

        outer_conv = ml_conv2d2x2_2(mat, const_kernel)
        induction = Eq(an_output_nlist, outer_conv)
        summary = Implies(valid, And(preloop, And(postloop, induction)))
        return Synth(name, summary, *ci.modifiedVars, *ci.readVars)

    elif name.startswith("inv1"):
        an_output_i32 = Choose(ci.modifiedVars[1], ci.modifiedVars[3])
        an_output_list = ci.modifiedVars[0]
        an_output_nlist = ci.modifiedVars[2]
        an_input_nlist = ci.readVars[0]
        length = ml_list_length(ml_list_list_get(an_input_nlist, an_output_i32))
        #valid = Gt(length, IntLit(1))
        #preloop = Ge(an_output_i32, IntLit(0))
        #postloop = Lt(an_output_i32, length)
        #preloop_outer = Ge(an_output_i32, IntLit(0))
        #postloop_outer = Lt(an_output_i32, ml_list_list_length(an_input_nlist))
        #induction = Eq(an_output_list, ml_conv2d2x2_inner(an_input_nlist,
        #                                                   kernel,
        #                                                   an_output_i32,
        #                                                   an_output_i32,
        #                                                   Add(an_output_i32, IntLit(1))))
        #summary = Implies(valid, And(preloop, And(postloop, And(preloop_outer, And(postloop_outer, induction)))))
        #return Synth(name, summary, *ci.modifiedVars, *ci.readVars)
        #return Synth(name, Eq(ci.readVars[0], ci.modifiedVars[2]), *ci.modifiedVars, *ci.readVars)
        valid = Eq(ml_list_list_length(an_input_nlist), IntLit(3))
        preloop1 = Ge(an_output_i32, IntLit(0))
        preloop2 = Ge(an_output_i32, IntLit(0)) # TODO: might have to explicitly different from preloop1
        postloop1 = Lt(an_output_i32, ml_list_length(ml_list_list_get(an_input_nlist, IntLit(0))))
        postloop2 = Lt(an_output_i32, Sub(ml_list_list_length(an_input_nlist), IntLit(1)))

        mat = ml_list_list_take(an_input_nlist, Add(an_output_i32, IntLit(1)))
        outer_conv = ml_conv2d2x2_2(mat, const_kernel)
        induction1 = Eq(an_output_nlist, outer_conv)

        inner_mat_part1 = ml_list_take(ml_list_list_get(an_input_nlist, an_output_i32), Add(an_output_i32, IntLit(1)))
        inner_mat_part2 = ml_list_take(ml_list_list_get(an_input_nlist, Add(an_output_i32, IntLit(1))), Add(an_output_i32, IntLit(1)))
        mat = ml_list_list_prepend(inner_mat_part1, ml_list_list_prepend(inner_mat_part2, ml_list_list_empty()))
        inner_conv = ml_conv2d2x2_inner2(mat, const_kernel, IntLit(0), IntLit(0))
        induction2 = Eq(an_output_list, inner_conv)
        summary_rhs = And(preloop1, And(preloop2, And(postloop1, And(postloop2, And(induction1, And(induction2))))))
        summary = Implies(valid, summary_rhs)
        return Synth(name, summary, *ci.modifiedVars, *ci.readVars)
    else:
        an_output = ci.modifiedVars[0]
        an_input = ci.readVars[0]
        #valid = And(Gt(ml_list_list_length(an_input), IntLit(1)),
        #            Gt(ml_list_length(ml_list_list_get(an_input, IntLit(0))), IntLit(1)))
        #ans = ml_conv2d2x2(an_input, kernel)
        #check_ans = Eq(ans, an_output)
        #summary = Implies(valid, check_ans)
        #return Synth(name, summary, *ci.modifiedVars, *ci.readVars)
        valid = Eq(ml_list_list_length(an_input), IntLit(3))
        ans = ml_conv2d2x2_2(an_input, kernel)
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

    def conv2d2x2Helper2_body(mat, kernel, i, j):
        cond = Or(Lt(i, IntLit(0)), Ge(i, Sub(ml_list_list_length(mat), IntLit(1))))
        
        cur_term = ml_conv2d2x2_inner2(mat, kernel, i, j)
        recursed = ml_conv2d2x2_helper2(mat, kernel, Add(i, IntLit(1)), IntLit(0))
        general_answer = ml_list_list_prepend(cur_term, recursed)
        return Ite(cond, ml_list_list_empty(), general_answer)
    conv2d2x2_helper2 = FnDeclRecursive(CONV2D2X2_HELPER2, ListT(ListT(Int())), conv2d2x2Helper2_body(mat, kernel, i, j), mat, kernel, i, j)

    def conv2d2x2Inner_body(mat, kernel, i, j, stopping):
        last_valid_j = Sub(stopping, IntLit(1))
        base_case_2_or = lambda general_case: Ite(Gt(j, last_valid_j), ml_list_empty(), general_case)

        cur_term = ml_dotprod2x2(mat, kernel, i, j)
        recursed = ml_conv2d2x2_inner(mat, kernel, i, Add(j, IntLit(1)), stopping)
        general_answer_2 = ml_list_prepend(cur_term, recursed)
        return base_case_2_or(general_answer_2)
    conv2d2x2_inner = FnDeclRecursive(CONV2D2X2_INNER, ListT(Int()), conv2d2x2Inner_body(mat, kernel, i, j, stopping), mat, kernel, i, j, stopping)

    def conv2d2x2Inner2_body(mat, kernel, i, j):
        cond = Or(Lt(j, IntLit(0)), Ge(j, Sub(ml_list_length(ml_list_list_get(mat, i)), IntLit(1))))

        cur_term = ml_dotprod2x2(mat, kernel, i, j)
        recursed = ml_conv2d2x2_inner2(mat, kernel, i, Add(j, IntLit(1)))
        general_answer = ml_list_prepend(cur_term, recursed)
        return Ite(cond, ml_list_empty(), general_answer)
    conv2d2x2_inner2 = FnDeclRecursive(CONV2D2X2_INNER2, ListT(Int()), conv2d2x2Inner2_body(mat, kernel, i, j), mat, kernel, i, j)

    def conv2d2x2_body(mat, kernel):
        last_valid_i = Sub(ml_list_list_length(mat), ml_list_list_length(kernel)) # TODO: subtract kernel
        return ml_conv2d2x2_helper(mat, kernel, IntLit(0), Add(last_valid_i, IntLit(1)))
    conv2d2x2 = FnDeclRecursive(CONV2D2X2, ListT(ListT(Int())), conv2d2x2_body(mat, kernel), mat, kernel)

    def conv2d2x2_2_body(mat, kernel):
        return ml_conv2d2x2_helper2(mat, kernel, IntLit(0), IntLit(0))
    conv2d2x2_2 = FnDeclRecursive(CONV2D2X2_2, ListT(ListT(Int())), conv2d2x2_2_body(mat, kernel), mat, kernel)

    return [dotprod2x2, conv2d2x2, conv2d2x2_2, conv2d2x2_inner, conv2d2x2_inner2, conv2d2x2_helper, conv2d2x2_helper2]

def codeGenToGemmini(summary: FnDecl):
    kernel_vals = []
    def eval(expr):
        nonlocal kernel_vals
        if isinstance(expr, ValueRef):
            return expr.name
        elif isinstance(expr, Eq):
            left = expr.e1()
            right = expr.e2()
            if isinstance(left, Call):
                return f"{eval(left)}"
            else:
                return f"{eval(right)}"
        elif isinstance(expr, FnDecl) or isinstance(expr, FnDeclRecursive):
            arg = eval(expr.arguments()[0])
            body = eval(expr.body()) # Sets kernel_vals
            macros = f"#define KER_LEN {len(kernel_vals)}\n" \
                    f"#define LEN @@@RUNNER_LEN@@@\n" \
                    f"#define SLIDES ((LEN) - (KER_LEN) + 1)\n"
            helpers = \
                    """
                    void print1d(elem_t Out[1][SLIDES]) {
                      for (int j = 0; j < SLIDES; j++) {
                        printf("%d, ", Out[0][j]);
                      }
                      printf("\\n");
                    }

                    void naive_conv1d(elem_t input[2][LEN], elem_t output[1][SLIDES]) {
                      for (int i = 0; i < LEN; i++) {
                        input[0][i] = i;
                      }
                      
                      for (int i = 0; i < SLIDES; i++) {
                        output[0][i] = input[0][i] + input[0][i+1];
                      }
                    }
                    """
            #kernel_assignments = [f"weights[0][{i}] = {weight};" for i, weight in enumerate(kernel_vals)]
            #kernel_assignments = "\n".join(kernel_assignments)
            kernel_assignments = ""
            for i, row in enumerate(kernel_vals):
                for j, weight in enumerate(row):
                    kernel_assignments += f"weights[{i}][{j}] = {weight};\n"
            #kernel_zeros = f"for (int i = 1; i < KER_LEN; i++) {{\n" \
            #        f"for (int j = 0; j < KER_LEN; j++) {{\n" \
            #        f"weights[i][j] = 0;\n" \
            #        f"}}\n" \
            #        f"}}\n"
            kernel_zeros = ""
            code = f"{macros}\n" \
                    f"{helpers}\n" \
                    f"void runner(elem_t In[KER_LEN][LEN], elem_t Out[1][SLIDES]) {{\n" \
                    f"static elem_t weights[KER_LEN][KER_LEN];\n" \
                    f"{kernel_assignments}\n" \
                    f"{kernel_zeros}\n" \
                    f"{body}\n" \
                    f"}}"
            return code
            #return f"tiled_conv_auto(1, 1, LEN, 1," \
            #        f"1, 1, SLIDES," \
            #        f"1, 1, 1, 0, 2," \
            #        f"false, false, false, false, false," \
            #        f"(elem_t*)In," \
            #        f"(elem_t*)weights," \
            #        f"NULL," \
            #        f"(elem_t*)Out," \
            #        f"0, 0, 0, 0, 0, WS);"
            #return f"def {expr.name()}({', '.join([eval(arg) for arg in expr.arguments()])}):\n    " \
            #        f"return {eval(expr.body())}"
        elif isinstance(expr, Call):
            eval_args = []
            for a in expr.arguments():
                eval_args.append(eval(a))
            name = expr.name()
            if name == CONV2D2X2_2:
                name = "tiled_conv_auto"
                assert(len(eval_args) == 2)

                code = f"{name}(\n" \
                        f"1, LEN, LEN, 1,\n" \
                        f"1, SLIDES, SLIDES,\n" \
                        f"1, 1, 1, 0, KER_LEN,\n" \
                        f"false, false, false, false, false,\n" \
                        f"(elem_t*)In,\n" \
                        f"(elem_t*)weights,\n" \
                        f"NULL,\n" \
                        f"(elem_t*)Out,\n" \
                        f"0, 0, 0, 0, 0, WS);\n"
                return code
                #input = f"torch.tensor([[{eval_args[0]}]]).float().to(mps_device)"
                #kernel = f"torch.tensor([[{eval_args[1]}]]).float().to(mps_device)"
                #return f"{name}({input}, {kernel})"
            elif name == "list_empty":
                return f"list_empty()"
            elif name == "list_list_empty":
                return f"list_list_empty()"
            elif name == "list_list_prepend":
                def flatten_prepends_outer(expr):
                    name = expr.name()
                    if name == "list_list_empty":
                        return []
                    assert(name == "list_list_prepend")
                    arguments = expr.arguments()
                    assert(len(arguments) == 2)
                    car = eval(arguments[0])
                    cdr = flatten_prepends_outer(arguments[1])
                    return [car] + cdr
                flattened = flatten_prepends_outer(expr)
                if len(flattened) == 2:
                    kernel_vals = flattened
                return f"[{', '.join(flattened)}]"

            elif name == "list_prepend":
                def flatten_prepends(expr):
                    name = expr.name()
                    # Base case
                    if name == "list_empty":
                        return []
                    # General case
                    assert(name == "list_prepend")
                    arguments = expr.arguments()
                    assert(len(arguments) == 2)
                    car = eval(arguments[0])
                    cdr = flatten_prepends(arguments[1])
                    return [car] + cdr
                flattened = flatten_prepends(expr)
                #if len(flattened) == 2:
                #    kernel_vals = flattened
                return f"[{', '.join(flattened)}]"
            raise NotImplementedError(f"codegen not implemented for function call {name}")
        elif isinstance(expr, Lit):
            return str(expr.val())
        elif isinstance(expr, Var):
            return expr.name()
        elif isinstance(expr, Implies):
            left = expr.args[0]
            right = expr.args[1]
            return eval(right)
            return f"not ({eval(left)}) or ({eval(right)})"
        else:
            raise NotImplementedError(f"codegen not implemented for {expr}")
    return eval(summary)

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
        if c.args[0] != "test":
            continue
        inner = codeGenToGemmini(c)
        code = \
"""
#include <stdint.h>
#include <stddef.h>
#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#ifndef BAREMETAL
#include <sys/mman.h>
#endif
#include "include/gemmini_testutils.h"
""" + \
inner + \
"""
int main() {
#ifndef BAREMETAL
    if (mlockall(MCL_CURRENT | MCL_FUTURE) != 0) {
      perror("mlockall failed");
      exit(1);
    }
#endif

  printf("Size of DIM: %d\\n", DIM);
  printf("Flush Gemmini TLB of stale virtual addresses\\n");
  gemmini_flush(0);

  static elem_t In[2][LEN];
  static elem_t Out[1][SLIDES];
  for (int j = 0; j < LEN; j++) {
    In[0][j] = j;
  }

  uint64_t start_cpu = read_cycles();
  naive_conv1d(In, Out);
  uint64_t end_cpu = read_cycles();
  printf("CPU conv took %llu cycles\\n", end_cpu - start_cpu);

  uint64_t start_g = read_cycles();
  runner(In, Out);
  uint64_t end_g = read_cycles();
  printf("Hardware conv took %llu cycles\\n", end_g - start_g);

  //print1d(Out);
  exit(0);
}
"""
        LEN = 5 # I get to set this in this in the string above
        code = code.replace('@@@RUNNER_LEN@@@', str(LEN))
        print(code)

runner("conv2d")
