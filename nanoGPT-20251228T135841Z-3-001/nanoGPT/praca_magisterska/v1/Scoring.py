import sys
from pathlib import Path

# adjust if your path differs
PROJECT_ROOT = Path.home() / "PycharmProjects" / "Magisterka"
PKG_ROOT = PROJECT_ROOT / "nanoGPT-20251228T135841Z-3-001" / "nanoGPT"

sys.path.insert(0, str(PKG_ROOT))

from praca_magisterska.v1.Proofs import *
how_many_times_was = dict()
def variables_order(f):
    if isinstance(f,Lie) or isinstance(f,Truth):
        return []
    if isinstance(f,Atom):
        return [f]
    else:
        ans = []
        for i in f.Interior:
            ans += variables_order(i)
        return ans

def contains_TF(f):
    if isinstance(f,Truth) or isinstance(f,Lie):
        return True
    if isinstance(f,Atom):
        return False
    else:
        ans  = False
        for i in f.Interior:
            ans = ans or contains_TF(i)
        return ans

def subformulas(f):
    if not isinstance(f,Formula):
        raise TypeError("Bad argument")
    if isinstance(f,Atom) or isinstance(f,Truth) or isinstance(f,Lie):
        return []
    ans = []
    for i in f.Interior:
        ans.append(i)
        ans += subformulas(i)
    return ans

def AbstractionSimple(t,x,Expr):
    if t == Expr:
        return parse_infix(x)
    if isinstance(Expr,Truth) or isinstance(Expr,Lie) or isinstance(Expr,Atom):
        return Expr
    ExprAns = copy.deepcopy(Expr)
    for i in range(Expr.Interior.__len__()):
        ExprAns.Interior[i] = AbstractionSimple(t,x,ExprAns.Interior[i])
    return ExprAns

def normalise(f):
    vars = variables_order(f)
    i = 0
    new_vars = dict()
    for x in vars:
        if not to_infix(x) in new_vars.keys():
            new_vars[to_infix(x)] = "x" + str(i)
            i += 1
    ans = copy.deepcopy(f)
    for old in new_vars.keys():
        new = new_vars[old]
        ans = AbstractionSimple(parse_infix(old), new, ans)
    return ans

def homomorphic(f):
    f_norm = normalise(f)
    sub_forms = subformulas(f_norm)
    ans = []
    new_var = "x"+str(to_infix(f_norm).__len__())
    for i in sub_forms:
        if not (isinstance(i,Atom) or isinstance(i,Truth) or isinstance(i,Lie)):
            new_elem  = AbstractionSimple(i, new_var,f_norm)
            ans.append(normalise(new_elem))
            ans += homomorphic(ans[-1])
    print(ans.__len__())
    return ans

def can_be_simplified(f):
    if not isTautology(f):
        return None
    f_norm = normalise(f)
    new_var = "x"+str(to_infix(f_norm).__len__())
    sub_forms = subformulas(f_norm)
    for i in sub_forms:
        if not (isinstance(i,Atom) or isinstance(i,Truth) or isinstance(i,Lie)):
            if isTautology(i) == Truth():
                new_candidate = AbstractionSimple(i, "T",f_norm)###
                return can_be_simplified(new_candidate) + np.log(to_infix(f_norm).__len__()-to_infix(normalise(i)).__len__())
            if isTautology(Negation(i)) == Truth():
                new_candidate = AbstractionSimple(i, "⊥",f_norm)###
                return can_be_simplified(new_candidate) + np.log(to_infix(f_norm).__len__()-to_infix(normalise(i)).__len__())
            new_candidate  = AbstractionSimple(i, new_var,f_norm)
            if isTautology(new_candidate):
                return can_be_simplified(new_candidate) + np.log(abs(to_infix(f_norm).__len__()-to_infix(normalise(i)).__len__())+1)
    return 0

def score(lp):
    global how_many_times_was
    ans = 0
    if can_be_simplified(lp.conclusion) != None:
        ans -= can_be_simplified(lp.conclusion) *10
    if normalise(lp.conclusion) in how_many_times_was.keys():
        ans -= how_many_times_was[normalise(lp.conclusion)]*5
    ans -= lp.assumptions.formulas.__len__()
    ans += np.log(to_infix(normalise(lp.conclusion)).__len__())
    if isinstance(lp.conclusion,Implication) or isinstance(lp.conclusion,Iff):
        if lp.conclusion.Left() == lp.conclusion.Right():
            ans -= 1000
    return ans