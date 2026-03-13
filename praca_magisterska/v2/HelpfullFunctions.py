import sys
from pathlib import Path

# adjust if your path differs
PROJECT_ROOT = Path.home() / "PycharmProjects" / "Magisterka"
PKG_ROOT = PROJECT_ROOT / "nanoGPT-20251228T135841Z-3-001" / "nanoGPT"

sys.path.insert(0, str(PKG_ROOT))

from praca_magisterska.v1 import TermAndFormulas
from praca_magisterska.v2.TermAndFormulas import *
from praca_magisterska.v2.ContextsAndLP import *


def FreeVariables(Expr):
    print()
    if not (isinstance(Expr, Formula) or isinstance(Expr,Context)) or isinstance(Expr,Term):
        raise TypeError("Bad arguments")
    if isinstance(Expr, Variable):
        return {Expr}
    if isinstance(Expr, Atom):
        ans = set()
        for i in Expr.Arguments:
            ans =ans.union(FreeVariables(i))
        return ans
    if (isinstance(Expr, Truth) or
        isinstance(Expr, Lie)):
        return set()
    if (isinstance(Expr, Negation) or
        isinstance(Expr, Conjunction) or
        isinstance(Expr,Disjunction) or
        isinstance(Expr,Implication) or
        isinstance(Expr,Iff)):
        ans = set()
        for i in Expr.Interior:
            ans = ans.union(FreeVariables(i))
        return ans
    if isinstance(Expr, TermAndFormulas.Context):
        ans = set()
        for i in Expr.formulas:
            ans = ans.union(FreeVariables(i))
        return ans

def tokenize(s: str):
    s = s.replace(" ", "")
    tokens = []
    i = 0
    while i < len(s):
        if s[i] in "()¬∧∨":
            tokens.append(s[i]); i += 1
        elif s.startswith("→", i):
            tokens.append("→"); i += 1
        elif s.startswith("↔", i):
            tokens.append("↔"); i += 1
        elif s[i] in ["⊤","⊥"]:
            tokens.append(s[i]); i += 1
        else:
            # identyfikatory (zmienne/predykaty jednosymb. dla prostoty)
            j = i
            while j < len(s) and s[j] not in ["⊤","⊥","¬","∧","∨","→","↔","(",")"]: # ta linia naprawiona reszta komórki później
                j += 1
            tokens.append(s[i:j]); i = j
    return tokens

# Priorytety i łączność
# wyższa liczba = wyższy priorytet
PREC = {
    "¬": 5,
    "∧": 4,
    "∨": 3,
    "→": 2,
    "↔": 1,
}
RIGHT_ASSOC = {"¬", "→"}  # ~ i -> prawostronnie (typowo -> jest right-assoc)

def is_op(t): return t in PREC
def is_unary(t): return t == "¬"

# Shunting-yard: infix -> RPN
def to_rpn(tokens):
    out, ops = [], []
    prev = None
    for t in tokens:
        if t == "(":
            ops.append(t)
        elif t == ")":
            while ops and ops[-1] != "(":
                out.append(ops.pop())
            if not ops: raise ValueError("Brakujący '('")
            ops.pop()
        elif is_op(t):
            # rozróżnienie ~ unarny vs binarny można dodać wg kontekstu prev
            while ops and ops[-1] != "(" and (
                (PREC[ops[-1]] > PREC[t]) or
                (PREC[ops[-1]] == PREC[t] and t not in RIGHT_ASSOC)
            ):
                out.append(ops.pop())
            ops.append(t)
        else:
            # operand: zmienna/stała T/⊥
            out.append(t)
        prev = t
    while ops:
        op = ops.pop()
        if op in ("(", ")"): raise ValueError("Niezamknięty nawias")
        out.append(op)
    return out

TruthRelation = TermAndFormulas.Relation("\'", [1])
# Budowa AST z RPN
def rpn_to_ast(rpn):
    global TruthRelation
    VariablesDict = dict()
    for i in rpn:
        if i not in ["⊤","⊥","¬","∧","∨","→","↔","(",")"]:
            if not i in VariablesDict.keys():
                v = TermAndFormulas.Variable(i)
                VariablesDict[i] = v
    st = []
    for t in rpn:
        if t == "⊤":
            st.append(TermAndFormulas.Truth())
        elif t == "⊥":
            st.append(TermAndFormulas.Lie())
        elif t == "¬":
            a = st.pop()
            st.append(Negation(a))
        elif t in ["∧","∨","→","↔"]:
            b = st.pop(); a = st.pop()
            if t == "∧": st.append(TermAndFormulas.Conjunction(a, b))
            elif t == "∨": st.append(TermAndFormulas.Disjunction(a, b))
            elif t == "→": st.append(TermAndFormulas.Implication(a, b))
            else: st.append(TermAndFormulas.Iff(a, b))
        else:
            st.append(TermAndFormulas.Atom(TruthRelation, VariablesDict[t]))
    if len(st) != 1: raise ValueError("Błędne wyrażenie")
    return st[0]

def parse_infix(s: str):
    tokenized = tokenize(s)
    rpn = to_rpn(tokenized)
    return rpn_to_ast(rpn)

def split_once(s: str, sep: str):
    i = s.find(sep)
    if i == -1:
        return [s]
    prefix = s[:i]
    postfix = s[i+len(sep):]
    return [prefix, postfix]
split_once("Ala ma kota", " m")




def atoms(f):
    if not isinstance(f, TermAndFormulas.Formula):
        raise TypeError("Bad argument")
    if isinstance(f, TermAndFormulas.Truth) or isinstance(f, TermAndFormulas.Lie):
        return ContextsAndLP.Context()
    if isinstance(f, TermAndFormulas.Atom):
        return ContextsAndLP.Context(f)
    else:
        ans = ContextsAndLP.Context()
        for i in f.Interior:
            ans = ans + atoms(i)
    return ans

def next_values(values):
    keys = values.keys()
    keys = sorted(keys,key = str)
    idx = values.__len__()
    for i in range(values.__len__()-1,-1,-1):
        if values[keys[i]] == TermAndFormulas.Truth():
            values[keys[i]] = TermAndFormulas.Lie()
            idx = i + 1
            break
    for i in range(idx, values.__len__(),1):
        values[keys[i]] = TermAndFormulas.Truth()
    return values


def isTautology(f):
    if not isinstance(f, TermAndFormulas.Formula):
        raise TypeError("Bad argument")
    k = atoms(f)
    vals = dict()
    for i in k:
        vals[i] = TermAndFormulas.Truth()
    for i in range(2**vals.__len__()):
        keys = vals.keys()
        keys = sorted(keys,key = str)
        s = ""
        for i in keys:
            s += vals[i].__str__()

        if f.evaluate(vals) == TermAndFormulas.Lie():
            return TermAndFormulas.Lie()
        vals = next_values(vals)
    return TermAndFormulas.Truth()
import random
def randomFormula(depth, variables, TruthLieIncluded = True):
    depth = random.randint(0,depth)
    if depth == 0:
        if TruthLieIncluded:
            f = random.choice(variables+["⊥","⊤"])
        else:
            f = random.choice(variables)
        return parse_infix(f)
    else:
        f = random.choice([TermAndFormulas.Negation, TermAndFormulas.Conjunction, TermAndFormulas.Disjunction,
                           TermAndFormulas.Implication, TermAndFormulas.Iff])
        l = randomFormula(random.randint(1,depth)-1, variables,TruthLieIncluded)
        r = randomFormula(random.randint(1,depth)-1, variables,TruthLieIncluded)
        if f == TermAndFormulas.Negation:
            return TermAndFormulas.Negation(l)
        else:
            return f(l,r)

def SubstitutionSimple(t,x,Expr):
    if isinstance(Expr,Atom) or isinstance(Expr,Truth) or isinstance(Expr,Lie):
        if Expr == parse_infix(x):
             return t
        else:
            return Expr
    l = SubstitutionSimple(t,x,Expr.Left())
    if isinstance(Expr, TermAndFormulas.Negation):
        return TermAndFormulas.Negation(l)
    r = SubstitutionSimple(t,x,Expr.Right())
    if isinstance(Expr, TermAndFormulas.Conjunction):
        return TermAndFormulas.Conjunction(l, r)
    if isinstance(Expr, TermAndFormulas.Disjunction):
        return TermAndFormulas.Disjunction(l, r)
    if isinstance(Expr, TermAndFormulas.Implication):
        return TermAndFormulas.Implication(l, r)
    if isinstance(Expr, TermAndFormulas.Iff):
        return TermAndFormulas.Iff(l, r)

def randomTautology(depth, variables):
    global formulas
    i = random.choice([0,1])
    if i == 0:
        ans = TermAndFormulas.Disjunction(randomFormula(depth, variables), randomFormula(depth, variables))
        while not isTautology(ans):
            ans = TermAndFormulas.Disjunction(randomFormula(depth, variables), ans)
        return ans
    else:
        t = randomFormula(depth,variables)
        Expr = random.choice(formulas)
        while atoms(Expr).formulas == []:
            Expr = random.choice(formulas)
        x = (random.choice(atoms(Expr).formulas)).Arguments[0].name
        ans = SubstitutionSimple(t,x,Expr)
        return ans

def to_infix(f):
    if isinstance(f, TermAndFormulas.Truth):
        return "⊤"
    elif isinstance(f, TermAndFormulas.Lie):
        return "⊥"
    elif isinstance(f, TermAndFormulas.Atom):
        return f.Arguments[0].name
    else:
        args = []
        for i in f.Interior:
            s = to_infix(i)
            if not (isinstance(i, TermAndFormulas.Truth) or isinstance(i, TermAndFormulas.Lie) or isinstance(i,
                                                                                                             TermAndFormulas.Atom) or isinstance(i,
                                                                                                                                                 TermAndFormulas.Negation)):
                s = "(" + s +")"
            args.append(s)
        if isinstance(f, TermAndFormulas.Negation):
            return "¬" + args[0]
        if isinstance(f, TermAndFormulas.Conjunction):
            return args[0] +" ∧ "+ args[1]
        if isinstance(f, TermAndFormulas.Disjunction):
            return args[0] +" ∨ "+ args[1]
        if isinstance(f, TermAndFormulas.Implication):
            return args[0] +" → "+ args[1]
        if isinstance(f, TermAndFormulas.Iff):
            return args[0] +" ↔ "+ args[1]

