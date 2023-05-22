import shutil
import time
from functools import reduce

# modified runner to check larger arrays

from metalift.ir import *
from metalift.analysis import CodeInfo, analyze
from metalift.synthesis_common import SynthesisFailed

from metalift.synthesize_auto import synthesize

LIST_BOUND = 3

MUL1D = "elementwise_mul"
SAME_LEN = "same_length"
CONV1D1X2 = "conv1d1x2"
DOTPROD2D = "dotprod_2d"
DOTPROD = "dotprod"

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

def ml_min(a, b):
    return Ite(Lt(a, b), a, b)

def ml_dotprod2d(x, y):
    return Call(DOTPROD2D, Int(), x, y)

def ml_dotprod(x, y):
    return Call(DOTPROD, Int(), x, y)

def ml_conv1d1x2(vec, kernel):
    return Call(CONV1D1X2, ListT(Int()), vec, kernel)

def grammar(ci: CodeInfo, kernel_size=2):
    name = ci.name

    print("INV VARS MV HERE")
    print(*ci.modifiedVars)
    print("INV VARS RV HERE")
    print(*ci.readVars)

    unknown_const = Choose(*[IntLit(coef) for coef in range(-3, 3 + 1)])
    y = reduce(lambda acc, _cur: ml_list_prepend(unknown_const, acc), range(kernel_size), ml_list_empty())

    if name.startswith("inv"):
        # Invariant
        # The invariant enforces 3 properties.

        an_input = Choose(*ci.readVars)
        an_output_i32 = ci.modifiedVars[1]
        an_output_list = ci.modifiedVars[0]

        valid = Gt(ml_list_length(an_input), IntLit(1))
        # This enforces the pre-loop invariant condition, that the looping index
        # is always at least 0.
        preloop = Ge(an_output_i32, IntLit(0))
        # This enforces the post-loop invariant condition, that the looping
        # index is at most the last index of the list.
        postloop = Le(an_output_i32, Sub(ml_list_length(an_input), IntLit(1)))
        # This enforces the inductive property, that if the output so far is
        # the convolution of the input and kernel so far, then it will continue
        # being the convolution of the input and kernel.
        induction = Eq(an_output_list,
                       ml_conv1d1x2(ml_list_take(an_input, Add(an_output_i32, IntLit(1))),
                                    y))
        summary = Implies(valid, And(preloop, And(postloop, induction)))

        return Synth(name, summary, *ci.modifiedVars, *ci.readVars)
    else:
        # Post condition
        # We require that, when the input and kernel lists are the same size,
        # that the output list is what we expect (the 1D convolution of the
        # kernel over the input).
        an_input = ci.readVars[0]
        an_output = Choose(*ci.modifiedVars)
        x = ci.readVars[0]
        valid = Gt(ml_list_length(x), IntLit(1))
        ans = ml_conv1d1x2(an_input, y)
        check_ans = Eq(ans, an_output)
        summary = Implies(valid, check_ans)
        return Synth(name, summary, *ci.modifiedVars, *ci.readVars)

def targetLang(kernel_size=2):
    x = Var("x", ListT(Int()))
    y = Var("y", ListT(Int()))

    # Ignores the rest of x if y is shorter
    # TODO: just take idx 1
    def dotprod2d_body(x, y):
        element1 = Mul(ml_list_head(x), ml_list_head(y))
        x_rest = ml_list_tail(x, IntLit(1))
        y_rest = ml_list_tail(y, IntLit(1))
        element2 = Mul(ml_list_head(x_rest), ml_list_head(y_rest))
        return Add(element1, element2)
    dotprod2d = FnDecl(DOTPROD2D, Int(), dotprod2d_body(x, y), x, y)

    def dotprod_body(x, y):
        kernel_size = ml_list_length(y)
        cur_prod = Mul(ml_list_head(x), ml_list_head(y))
        x_rest = ml_list_tail(x, IntLit(1))
        y_rest = ml_list_tail(y, IntLit(1))
        recursed = ml_dotprod(x_rest, y_rest)
        return Ite(Lt(kernel_size, IntLit(2)), cur_prod, Add(cur_prod, recursed))
    dotprod = FnDeclRecursive(DOTPROD, Int(), dotprod_body(x, y), x, y)

    # TODO: handle input size < 2
    # TODO: for size < 2, don't call dotprod
    def conv1d1x2_body(vec, kernel):
        nonlocal kernel_size
        vec_size = ml_list_length(x)
        kernel_size = IntLit(kernel_size)
        cur_prod = ml_dotprod(vec, kernel)
        vec_rest = ml_list_tail(vec, IntLit(1))
        recursed = ml_conv1d1x2(vec_rest, kernel)
        general_answer = ml_list_prepend(cur_prod, recursed)
        return Ite(Lt(vec_size, kernel_size), ml_list_empty(), general_answer)
    conv1d1x2 = FnDeclRecursive(CONV1D1X2, ListT(Int()), conv1d1x2_body(x, y), x, y)

    return [dotprod2d, dotprod, conv1d1x2]

def codeGenToPytorch(summary: FnDecl):
    def eval(expr):
        if isinstance(expr, ValueRef):
            return expr.name
        elif isinstance(expr, Eq):
            left = expr.e1()
            right = expr.e2()
            if isinstance(left, Call):
                return f"({eval(left)})"
            else:
                return f"({eval(right)})"
        elif isinstance(expr, FnDecl) or isinstance(expr, FnDeclRecursive):
            return f"def {expr.name()}({', '.join([eval(arg) for arg in expr.arguments()])}):\n    " \
                    f"return {eval(expr.body())}"
        elif isinstance(expr, Call):
            eval_args = []
            for a in expr.arguments():
                eval_args.append(eval(a))
            name = expr.name()
            if name == CONV1D1X2:
                name = "torch.nn.functional.conv1d"
                assert(len(eval_args) == 2)
                input = f"torch.tensor([[{eval_args[0]}]]).float().to(mps_device)"
                kernel = f"torch.tensor([[{eval_args[1]}]]).float().to(mps_device)"
                return f"{name}({input}, {kernel})"
            elif name == "list_empty":
                return f"list_empty()"
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
                #print(flattened)
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

def codeGenToPytorchWithEnv(summary: FnDecl):
    inner = codeGenToPytorch(summary)
    code = \
"""
import torch
mps_device = torch.device("mps")
""" + \
inner + \
"""
l = [i for i in range(100000)]
o = test(None, l)
print(o)
"""
    return code

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
            kernel_assignments = [f"weights[0][{i}] = {weight};" for i, weight in enumerate(kernel_vals)]
            kernel_assignments = "\n".join(kernel_assignments)
            kernel_zeros = f"for (int i = 1; i < KER_LEN; i++) {{\n" \
                    f"for (int j = 0; j < KER_LEN; j++) {{\n" \
                    f"weights[i][j] = 0;\n" \
                    f"}}\n" \
                    f"}}\n"
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
            if name == CONV1D1X2:
                name = "tiled_conv_auto"
                assert(len(eval_args) == 2)

                code = f"{name}(\n" \
                        f"1, 1, LEN, 1,\n" \
                        f"1, 1, SLIDES,\n" \
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
                if len(flattened) == 2:
                    kernel_vals = flattened
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

def write_to_disk_for_millennium(fname, contents):
    with open(f"/scratch/metaliftDeps/chipyard/generators/gemmini/software/gemmini-rocc-tests/bareMetalC/{fname}.c", "w") as file:
        file.write(contents)

def write_to_disk_torch(fname, contents):
    with open(f"/home/metalift/{fname}.py", "w") as file:
        file.write(contents)

def runner(basename):
    filename = f"tests/{basename}.ll"
    fnName = "test"
    loopsFile = f"tests/{basename}.loops"
    cvcPath = "cvc5"

    (vars, invAndPs, preds, vc, loopAndPsInfo) = analyze(filename, fnName, loopsFile, log=False)


    candidates = []
    kernel_len = 1
    for kernel_size in range(1, LIST_BOUND):
        kernel_len = kernel_size
        invAndPs = [grammar(ci, kernel_size) for ci in loopAndPsInfo]
        lang = targetLang(kernel_size)
        try:
            start_time = time.time()
            candidates = synthesize(basename, lang, vars, invAndPs, preds, vc, loopAndPsInfo, cvcPath, listBound=LIST_BOUND, noVerify=True)
            end_time = time.time()
            print(f"Synthesis took {end_time - start_time} seconds")
            break
        except SynthesisFailed:
            print("Synthesis failed")

    for c in candidates:
        if c.args[0] != "test":
            continue
        print(c.args[0])
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
        write_to_disk_for_millennium(f"{basename}_synth", code)
        write_to_disk_torch(f"{basename}_synth", codeGenToPytorchWithEnv(c))

# # Expected:
# import torch
# mps_device = torch.device("mps")
# def test(i27, arg):
#     return (torch.nn.functional.conv1d(torch.tensor([[arg]]).float().to(mps_device), torch.tensor([[[1, 1]]]).float().to(mps_device)))
# l = [i for i in range(100000)]
# o = test(None, l)
# print(o)
runner("conv1d")

# # Expected:
# import torch
# mps_device = torch.device("mps")
# def test(i27, arg):
#     return (torch.nn.functional.conv1d(torch.tensor([[arg]]).float().to(mps_device), torch.tensor([[[2, -1]]]).float().to(mps_device)))
# l = [i for i in range(100000)]
# o = test(None, l)
# print(o)
runner("conv1d_2")
