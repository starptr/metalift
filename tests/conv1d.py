import shutil
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

def ml_conv1d1x2(vec, kernel, stride):
    return Call(CONV1D1X2, ListT(Int()), vec, kernel, stride)

def grammar(ci: CodeInfo, kernel_size=2):
    name = ci.name

    print("INV VARS MV HERE")
    print(*ci.modifiedVars)
    print("INV VARS RV HERE")
    print(*ci.readVars)

    unknown_const = Choose(*[IntLit(coef) for coef in range(-3, 3 + 1)])
    stride = Choose(IntLit(1), IntLit(2), IntLit(3), IntLit(4))
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
                                    y,
                                    stride))
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
        ans = ml_conv1d1x2(an_input, y, stride)
        check_ans = Eq(ans, an_output)
        summary = Implies(valid, check_ans)
        return Synth(name, summary, *ci.modifiedVars, *ci.readVars)

def targetLang(kernel_size=2):
    x = Var("x", ListT(Int()))
    y = Var("y", ListT(Int()))
    s = Var("s", ListT(Int()))

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
    def conv1d1x2_body(vec, kernel, stride):
        nonlocal kernel_size
        vec_size = ml_list_length(x)
        kernel_size = IntLit(kernel_size)
        cur_prod = ml_dotprod(vec, kernel)
        vec_rest = ml_list_tail(vec, stride)
        recursed = ml_conv1d1x2(vec_rest, kernel, stride)
        general_answer = ml_list_prepend(cur_prod, recursed)
        return Ite(Lt(vec_size, kernel_size), ml_list_empty(), general_answer)
    conv1d1x2 = FnDeclRecursive(CONV1D1X2, ListT(Int()), conv1d1x2_body(x, y, s), x, y, s)

    return [dotprod2d, dotprod, conv1d1x2]

def codeGen(summary: FnDecl):
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
                assert(len(eval_args) == 3)
                input = f"torch.tensor([[{eval_args[0]}]]).float().to(mps_device)"
                kernel = f"torch.tensor([[{eval_args[1]}]]).float().to(mps_device)"
                stride_arg = f"stride={eval_args[2]}"
                return f"{name}({input}, {kernel}, {stride_arg})"
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
    for kernel_size in range(1, LIST_BOUND):
        invAndPs = [grammar(ci, kernel_size) for ci in loopAndPsInfo]
        lang = targetLang(kernel_size)
        try:
            candidates = synthesize(basename, lang, vars, invAndPs, preds, vc, loopAndPsInfo, cvcPath, listBound=LIST_BOUND, noVerify=True)
            break
        except SynthesisFailed:
            print("Synthesis failed")

    for c in candidates:
        if c.args[0] != "test":
            continue
        print(c.args[0])
        inner = codeGen(c)
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
        # # Expected:
        # import torch
        # mps_device = torch.device("mps")
        # def test(i27, arg):
        #     return (torch.nn.functional.conv1d(torch.tensor([[arg]]).float().to(mps_device), torch.tensor([[[1, 1]]]).float().to(mps_device)))
        # l = [i for i in range(100000)]
        # o = test(None, l)
        # print(o)
        print(code)

runner("conv1d")
# TODO: fix this
#runner("conv1d_2")
