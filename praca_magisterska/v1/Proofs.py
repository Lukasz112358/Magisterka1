import sys
from pathlib import Path

# adjust if your path differs
PROJECT_ROOT = Path.home() / "PycharmProjects" / "Magisterka"
PKG_ROOT = PROJECT_ROOT / "nanoGPT-20251228T135841Z-3-001" / "nanoGPT"

sys.path.insert(0, str(PKG_ROOT))

from praca_magisterska.v1.Rules import *
from praca_magisterska.v2.HelpfullFunctions import *

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

TruthRelation = Relation("\'",[1])
# Budowa AST z RPN
def rpn_to_ast(rpn):
    global TruthRelation
    VariablesDict = dict()
    for i in rpn:
        if i not in ["⊤","⊥","¬","∧","∨","→","↔","(",")"]:
            if not i in VariablesDict.keys():
                v = Variable(i)
                VariablesDict[i] = v
    st = []
    for t in rpn:
        if t == "⊤":
            st.append(Truth())
        elif t == "⊥":
            st.append(Lie())
        elif t == "¬":
            a = st.pop()
            st.append(Negation(a))
        elif t in ["∧","∨","→","↔"]:
            b = st.pop(); a = st.pop()
            if t == "∧": st.append(Conjunction(a,b))
            elif t == "∨": st.append(Disjunction(a,b))
            elif t == "→": st.append(Implication(a,b))
            else: st.append(Iff(a,b))
        else:
            st.append(Atom(TruthRelation,VariablesDict[t]))
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


def oracle(x):
    def ans(*args,**kwargs):
        return x
    return ans

import regex as re
def check_proof(x):
    proof_text = x.splitlines()
    for i in range(proof_text.__len__()):
        proof_text[i] = proof_text[i].split("  ")
        line = []
        for j in proof_text[i]:
            line += j.split(".")
        proof_text[i] = line
        proof_text[i] = list(filter(lambda x: x!= '',proof_text[i]))
    proof_text = list(filter(lambda x: x!= [],proof_text))

    #print("------------------------------------------------------------")
    #for i in proof_text:
    #    print(i)
    #print("------------------------------------------------------------")

    for i in range(proof_text.__len__()):
        #print(i)
        #print(proof_text[i])
        proof_text[i][1] = parse_infix(proof_text[i][1])
        proof_text[i][2] = proof_text[i][2].lstrip()
        proof_text[i][2] = split_once(proof_text[i][2],", ")

    LittleProblems = []
    Assumptions = [LittleProblem(Context(),Truth()),-1]
    for i in range(proof_text.__len__()):
        #print()
        #print(proof_text[i])
        #print(i)
        #print(i,"---------------------------------------")
        #print(proof_text[i][1])
        if proof_text[i][2][0] == "assumption":
            context = Context(proof_text[i][1])
            conclusion = proof_text[i][1]
            LittleProblems.append(LittleProblem(context, conclusion))

        elif proof_text[i][2][0] == "weakening":
            #print(i, proof_text[i][2])
            idx = int(proof_text[i][2][1]) - 1
            context = Context(proof_text[i][1]) + LittleProblems[idx].assumptions
            conclusion = proof_text[i][1]
            LittleProblems.append(LittleProblem(context, conclusion))
            #Assumptions.append([LittleProblem(context, conclusion),i])
        elif proof_text[i][2][0] == "∨-introduction":
            arg_idx = int(proof_text[i][2][1]) -1
            arg1 = proof_text[arg_idx][1]
            if arg1 == proof_text[i][1].Left():
                arg2 = proof_text[i][1].Right()
                rule = DisjunctionIntroduction1(oracle_top_down=oracle(arg2))
                correct = rule.top_down([LittleProblems[arg_idx]])
            else:
                arg2 = proof_text[i][1].Left()
                rule = DisjunctionIntroduction2(oracle_top_down=oracle(arg2))
                #print(arg_idx)
                #print("\n\n\n\n\n")
                #for j in LittleProblems:
                #    print(j)
                correct = rule.top_down([LittleProblems[arg_idx]])
            if correct.conclusion != proof_text[i][1]:
                raise TypeError("Bad proof")
            LittleProblems.append(correct)
        elif proof_text[i][2][0] == "¬-elimination":
            idxs = proof_text[i][2][1].split(",")
            left = int(idxs[0]) - 1
            right= int(idxs[1]) - 1
            lp1 = LittleProblems[left]
            lp2 = LittleProblems[right]
            rule = NegationElimination()
            LittleProblems.append(rule.top_down([lp1,lp2]))
            if LittleProblems[-1].conclusion != proof_text[i][1]:
                raise TypeError("Bad proof")
        elif proof_text[i][2][0] == "¬-introduction":
            idxs = proof_text[i][2][1].split("–")
            left = int(idxs[0]) - 1
            right= int(idxs[1]) - 1
            phi = proof_text[left][1]
            rule = NegationIntroduction(oracle_top_down=oracle(phi))
            lp = rule.top_down([LittleProblems[right]])
            if lp.conclusion != proof_text[i][1]:
                raise TypeError("Bad proof")
            LittleProblems.append(lp)
        elif proof_text[i][2][0] == "∧-introduction":
            idxs = proof_text[i][2][1].split(",")
            left = int(idxs[0]) - 1
            right= int(idxs[1]) - 1
            lp1 = LittleProblems[left]
            lp2 = LittleProblems[right]
            rule = ConjunctionIntroduction()
            lp = rule.top_down([lp1,lp2])
            if lp.conclusion != proof_text[i][1]:
                raise TypeError("Bad proof")
            LittleProblems.append(lp)
        elif proof_text[i][2][0] == "→-introduction":
            idxs = proof_text[i][2][1].split("–")
            #print(idxs)
            left = int(idxs[0]) - 1
            right= int(idxs[1]) - 1
            phi = proof_text[left][1]
            lp1 = LittleProblems[right]
            #print(lp1)
            rule = ImplicationIntroduction(oracle_top_down=oracle(phi))
            lp = rule.top_down([lp1])
            if lp.conclusion != proof_text[i][1]:
                raise TypeError("Bad proof")
            LittleProblems.append(lp)
        elif proof_text[i][2][0] == "RAA":
            idxs = proof_text[i][2][1].split("–")
            #print(idxs)
            left = int(idxs[0]) - 1
            right= int(idxs[1]) - 1
            neg_phi = proof_text[left][1]
            lp1 = LittleProblems[right]
            rule = ReductionAdAbsurdum(top_down_oracle=oracle(neg_phi))
            lp = rule.top_down([lp1])
            if lp.conclusion != proof_text[i][1]:
                raise TypeError("Bad proof")
            LittleProblems.append(lp)

        elif proof_text[i][2][0] == "TND":
            phi = proof_text[i][1].Left()
            rule = TertioNonDatur(oracle=oracle(phi))
            lp = rule.top_down([])
            if lp.conclusion != proof_text[i][1]:
                raise TypeError("Bad proof")
            LittleProblems.append(lp)
        elif proof_text[i][2][0] == "∨-elimination":
            idxs = proof_text[i][2][1].split(",")
            lp1 = LittleProblems[int(idxs[0])-1]
            lp2 = LittleProblems[int(idxs[1])-1]
            lp3 = LittleProblems[int(idxs[2])-1]
            rule = DisjunctionElimination()
            lp = rule.top_down([lp1,lp2,lp3])
            if lp.conclusion != proof_text[i][1]:
                raise TypeError("Bad proof")
            LittleProblems.append(lp)
        #    idxs = proof_text[i][2][1].split(",")
        #    for j in range(idxs.__len__()):
        #        idxs[j] = idxs[j].split("–")
        #        for k in range(idxs[j].__len__()):
        #            idxs[j][k] = int(idxs[j][k])-1
        #    lp1 = LittleProblems[idxs[0][0]]
        #    lp2 = LittleProblems[idxs[1][1]]
        #    lp3 = LittleProblems[idxs[2][1]]
        #    rule = DisjunctionElimination()
        #    lp = rule.top_down([lp1,lp2,lp3])
        #    if lp.conclusion != proof_text[i][1]:
        #        raise TypeError("Bad proof")
        #    LittleProblems.append(lp)
        #    phi = LittleProblems[idxs[1][0]].conclusion
        #    psi = LittleProblems[idxs[2][0]].conclusion
        #    phi_or_psi = LittleProblems[idxs[0][0]].conclusion
        #    if Disjunction(phi,psi) != phi_or_psi:
        #        raise TypeError("Bad proof")


        elif proof_text[i][2][0] == "¬¬-elimination":
            #print(proof_text[i][2][1])
            idx = int(proof_text[i][2][1]) -1
            lp1 = LittleProblems[idx]
            rule = NegationOfNegation()
            lp = rule.top_down([lp1])
            if lp.conclusion != proof_text[i][1]:
                raise TypeError("Bad proof")
            LittleProblems.append(lp)
        elif proof_text[i][2][0] == "∧-elimination":
            ans_conclusion = proof_text[i][1]
            idx = int(proof_text[i][2][1])-1
            phi_and_psi = LittleProblems[idx].conclusion
            if ans_conclusion == phi_and_psi.Left():
                rule = ConjunctionElimination1()
                lp = rule.top_down([LittleProblems[idx]])
            else:
                rule = ConjunctionElimination2()
                lp = rule.top_down([LittleProblems[idx]])
            if lp.conclusion != proof_text[i][1]:
                raise TypeError("Bad proof")
            LittleProblems.append(lp)
        elif proof_text[i][2][0] == "↔-elimination":
            idxs = proof_text[i][2][1].split(",")
            for j in range(2):
                idxs[j] = int(idxs[j])-1
            if LittleProblems[idxs[1]].conclusion == LittleProblems[idxs[0]].conclusion.Left():
                rule = IffElimination1()
                lp = rule.top_down([LittleProblems[idxs[0]], LittleProblems[idxs[1]]])
            else:
                rule = IffElimination2()
                lp = rule.top_down([LittleProblems[idxs[0]], LittleProblems[idxs[1]]])
            if lp.conclusion != proof_text[i][1]:
                raise TypeError("Bad proof")
            LittleProblems.append(lp)
        elif proof_text[i][2][0] == "⊤-introduction":
            rule = TruthIntroduction()
            lp = rule.top_down([])
            if lp.conclusion != proof_text[i][1]:
                raise TypeError("Bad proof")
            LittleProblems.append(lp)
        elif proof_text[i][2][0] == "→-elimination":
            idxs = proof_text[i][2][1].split(",")
            #print(idxs)
            left = int(idxs[0]) - 1
            right= int(idxs[1]) - 1
            lp1 = LittleProblems[left]
            lp2 = LittleProblems[right]
            rule = ImplicationElimination()
            lp = rule.top_down([lp1,lp2])
            if lp.conclusion != proof_text[i][1]:
                raise TypeError("Bad proof")
            LittleProblems.append(lp)
        elif proof_text[i][2][0] == "⊥-elimination":
            phi = proof_text[i][1]
            idx = int(proof_text[i][2][1])-1
            lp1 = LittleProblems[idx]
            rule = LieElimination(top_down_oracle=oracle(phi))
            lp = rule.top_down([lp1])
            if lp.conclusion != proof_text[i][1]:
                raise TypeError("Bad proof")
            LittleProblems.append(lp)
        elif proof_text[i][2][0] == "↔-introduction":
            idxs = proof_text[i][2][1]
            idxs = idxs.split(",")
            idxs[0] = int(idxs[0]) - 1
            idxs[1] = int(idxs[1]) - 1
            lp1 = LittleProblems[idxs[0]]
            lp2 = LittleProblems[idxs[1]]
            rule = IffIntroduction()
            lp = rule.top_down([lp1,lp2])
            if lp.conclusion != proof_text[i][1]:
                raise TypeError("Bad proof")
            LittleProblems.append(lp)

            #idxs = proof_text[i][2][1]
            #idxs = idxs.split(",")
            #idxs[0] = idxs[0].split("–")
            #idxs[1] = idxs[1].split("–")
            #idxs[0][0] = int(idxs[0][0]) - 1
            #idxs[0][1] = int(idxs[0][1]) - 1
            #idxs[1][0] = int(idxs[1][0]) - 1
            #idxs[1][1] = int(idxs[1][1]) - 1
            #phi = proof_text[idxs[0][0]][1]
            #psi = proof_text[idxs[1][0]][1]
            #lp1 = LittleProblems[idxs[0][1]]
            #lp2 = LittleProblems[idxs[1][1]]
            #if (lp1.conclusion != psi) or (lp2.conclusion != phi):
            #    raise TypeError("Bad proof")
            #rule = IffIntroduction()
            #lp = rule.top_down([lp1,lp2])
            #if lp.conclusion != proof_text[i][1]:
            #    raise TypeError("Bad proof")
            #LittleProblems.append(lp)
        else:
            raise TypeError("Unknown rule")
    return LittleProblems


def RandomProofLine(variables, proof_so_far, proof_so_far_structure,in_which_context_is_formula, which_conclusion_is_formula,depth, next_rule=None,TruthLieIncluded = True,is_final = False):
    #global in_which_context_is_formula
    #proof_so_far_structure = check_proof(proof_so_far)
    proof_so_far = proof_so_far.splitlines()
    x = str((proof_so_far.__len__() + 1)) + ". "
    if next_rule == None:
        next_rule = random.choice(["assumption",
                                   "weakening",
                                   "∨-introduction",
                                   "¬-elimination",
                                   "¬-introduction",
                                   "∧-introduction",
                                   "→-introduction",
                                   "RAA",
                                   "TND",
                                   "∨-elimination",
                                   "¬¬-elimination",
                                   "∧-elimination",
                                   "↔-elimination",
                                   "⊤-introduction",
                                   "→-elimination",
                                   "⊥-elimination",
                                   "↔-introduction"
                                   ])

    # pomiar czasu wykonania poszczególnych gałęzi next_rule
    y = ""
    z = ""
    if next_rule == "assumption":
        conclusion = randomFormula(depth, variables,TruthLieIncluded = TruthLieIncluded)
        y = to_infix(conclusion)
        context = Context(conclusion)
        y_structure = LittleProblem(context, conclusion)
        z = "   assumption"
        if is_final:
            for i in y_structure.assumptions.formulas:
                if i in in_which_context_is_formula.keys():
                    in_which_context_is_formula[i].append(proof_so_far.__len__())
                else:
                    in_which_context_is_formula[i] = [proof_so_far.__len__()]
            if y_structure.conclusion in which_conclusion_is_formula.keys():
                which_conclusion_is_formula[y_structure.conclusion].append(proof_so_far.__len__())
            else:
                which_conclusion_is_formula[y_structure.conclusion] = [proof_so_far.__len__()]
        return (x + y + z), y_structure
    elif next_rule == "weakening":
        if proof_so_far_structure.__len__() == 0:
            return ""
        candidate = random.randint(0, proof_so_far_structure.__len__() - 1)
        context = proof_so_far_structure[candidate].assumptions
        conclusion = randomFormula(depth, variables,TruthLieIncluded = TruthLieIncluded)
        context += Context(conclusion)
        y = to_infix(conclusion)
        y_structure = LittleProblem(context, conclusion)
        z = "    weakening, " + str(candidate + 1)
        if is_final:
            for i in y_structure.assumptions.formulas:
                if i in in_which_context_is_formula.keys():
                    in_which_context_is_formula[i].append(proof_so_far.__len__())
                else:
                    in_which_context_is_formula[i] = [proof_so_far.__len__()]
            if y_structure.conclusion in which_conclusion_is_formula.keys():
                which_conclusion_is_formula[y_structure.conclusion].append(proof_so_far.__len__())
            else:
                which_conclusion_is_formula[y_structure.conclusion] = [proof_so_far.__len__()]
        return (x + y + z), y_structure
    elif next_rule == "∨-introduction":
        if proof_so_far_structure.__len__() == 0:
            return ""
        candidate = random.randint(0, proof_so_far_structure.__len__() - 1)
        version = random.choice([1, 2])
        if version == 1:
            conclusion = Disjunction(proof_so_far_structure[candidate].conclusion, randomFormula(depth, variables,TruthLieIncluded = TruthLieIncluded))
            context = proof_so_far_structure[candidate].assumptions
            y_structure = LittleProblem(context, conclusion)
        else:
            conclusion = Disjunction(randomFormula(depth, variables,TruthLieIncluded = TruthLieIncluded), proof_so_far_structure[candidate].conclusion)
            context = proof_so_far_structure[candidate].assumptions
            y_structure = LittleProblem(context, conclusion)
        y = to_infix(conclusion)
        z = "    ∨-introduction, " + str(candidate + 1)
        if is_final:
            for i in y_structure.assumptions.formulas:
                if i in in_which_context_is_formula.keys():
                    in_which_context_is_formula[i].append(proof_so_far.__len__())
                else:
                    in_which_context_is_formula[i] = [proof_so_far.__len__()]
            if y_structure.conclusion in which_conclusion_is_formula.keys():
                which_conclusion_is_formula[y_structure.conclusion].append(proof_so_far.__len__())
            else:
                which_conclusion_is_formula[y_structure.conclusion] = [proof_so_far.__len__()]
        return (x + y + z), y_structure



    elif next_rule == "¬-elimination":
        candidates = []
        for i in range(proof_so_far_structure.__len__()):
            if isinstance(proof_so_far_structure[i].conclusion, Negation):
                phi = proof_so_far_structure[i].conclusion.Left()
                if which_conclusion_is_formula.get(phi,[]) != []:
                    candidates.append(i)
        if candidates == []:
            return ""
        def weight(x):
            phi = proof_so_far_structure[x].conclusion.Left()
            ans = which_conclusion_is_formula.get(phi,[]).__len__()
            return ans
        i = random.choices(candidates, weights=[weight(c) for c in candidates])[0]
        phi = proof_so_far_structure[i].conclusion.Left()
        j = random.choice(which_conclusion_is_formula.get(phi,[]))
        rule = NegationElimination()
        l = proof_so_far_structure[i]
        r = proof_so_far_structure[j]
        y_structure = rule.top_down([l, r])
        y = to_infix(y_structure.conclusion)
        z = "    ¬-elimination, " + str(i + 1) + ", " + str(j + 1)
        if is_final:
            for i in y_structure.assumptions.formulas:
                if i in in_which_context_is_formula.keys():
                    in_which_context_is_formula[i].append(proof_so_far.__len__())
                else:
                    in_which_context_is_formula[i] = [proof_so_far.__len__()]
            if y_structure.conclusion in which_conclusion_is_formula.keys():
                which_conclusion_is_formula[y_structure.conclusion].append(proof_so_far.__len__())
            else:
                which_conclusion_is_formula[y_structure.conclusion] = [proof_so_far.__len__()]
        return (x + y + z), y_structure



    elif next_rule == "¬-introduction":
        candidates = []
        for i in range(proof_so_far_structure.__len__()):
            if isinstance(proof_so_far_structure[i].conclusion, Lie):
                candidates.append(i)
        if candidates == []:
            return ""
        i = random.choice(candidates)
        rule = NegationIntroduction()
        phi = rule.oracle_top_down(proof_so_far_structure[i])
        candidates = []
        for j in range(proof_so_far_structure.__len__()):
            if proof_so_far_structure[j].conclusion == phi:
                candidates.append(j)
        j = random.choice(candidates)
        rule = NegationIntroduction(oracle_top_down=oracle(phi))
        y_structure = rule.top_down([proof_so_far_structure[i]])
        y = to_infix(y_structure.conclusion)
        z = "    ¬-introduction, " + str(j + 1) + "–" + str(i + 1)
        if is_final:
            for i in y_structure.assumptions.formulas:
                if i in in_which_context_is_formula.keys():
                    in_which_context_is_formula[i].append(proof_so_far.__len__())
                else:
                    in_which_context_is_formula[i] = [proof_so_far.__len__()]
            if y_structure.conclusion in which_conclusion_is_formula.keys():
                which_conclusion_is_formula[y_structure.conclusion].append(proof_so_far.__len__())
            else:
                which_conclusion_is_formula[y_structure.conclusion] = [proof_so_far.__len__()]
        return (x + y + z), y_structure
    elif next_rule == "∧-introduction":
        if proof_so_far == []:
            return ""
        i = random.randint(0, proof_so_far.__len__() - 1)
        j = random.randint(0, proof_so_far.__len__() - 1)
        rule = ConjunctionIntroduction()
        y_structure = rule.top_down([proof_so_far_structure[i], proof_so_far_structure[j]])
        y = to_infix(y_structure.conclusion)
        z = "    ∧-introduction, " + str(i + 1) + ", " + str(j + 1)
        if is_final:
            for i in y_structure.assumptions.formulas:
                if i in in_which_context_is_formula.keys():
                    in_which_context_is_formula[i].append(proof_so_far.__len__())
                else:
                    in_which_context_is_formula[i] = [proof_so_far.__len__()]
            if y_structure.conclusion in which_conclusion_is_formula.keys():
                which_conclusion_is_formula[y_structure.conclusion].append(proof_so_far.__len__())
            else:
                which_conclusion_is_formula[y_structure.conclusion] = [proof_so_far.__len__()]
        return (x + y + z), y_structure

    elif next_rule == "→-introduction":
        candidates = []
        for i in range(proof_so_far_structure.__len__()):
            if proof_so_far_structure[i].assumptions.formulas.__len__() != 0:
                candidates.append(i)
        if candidates == []:
            return ""
        i = random.choice(candidates)
        l = random.choice(proof_so_far_structure[i].assumptions.formulas)

        candidates = []
        #for j in range(i + 1):
        #    if proof_so_far_structure[j].conclusion == l:
        #        candidates.append(j)
        j = random.choice(which_conclusion_is_formula.get(l,[]))
        rule = ImplicationIntroduction(oracle_top_down=oracle(l))
        y_structure = rule.top_down([proof_so_far_structure[i]])
        y = to_infix(y_structure.conclusion)
        z = "    →-introduction, " + str(j + 1) + "–" + str(i + 1)
        if is_final:
            for i in y_structure.assumptions.formulas:
                if i in in_which_context_is_formula.keys():
                    in_which_context_is_formula[i].append(proof_so_far.__len__())
                else:
                    in_which_context_is_formula[i] = [proof_so_far.__len__()]
            if y_structure.conclusion in which_conclusion_is_formula.keys():
                which_conclusion_is_formula[y_structure.conclusion].append(proof_so_far.__len__())
            else:
                which_conclusion_is_formula[y_structure.conclusion] = [proof_so_far.__len__()]
        return (x + y + z), y_structure


    elif next_rule == "RAA":
        candidates = []
        for i in range(proof_so_far_structure.__len__()):
            if isinstance(proof_so_far_structure[i].conclusion, Lie):
                for j in proof_so_far_structure[i].assumptions.formulas:
                    if isinstance(j, Negation):
                        candidates.append(i)
        if candidates == []:
            return ""
        i = random.choice(candidates)
        rule = ReductionAdAbsurdum()
        y_structure = rule.top_down([proof_so_far_structure[i]])
        candidates = []
        for j in range(i + 1):
            if proof_so_far_structure[j].conclusion == Negation(y_structure.conclusion):
                candidates.append(j)
        j = random.choice(candidates)
        y = to_infix(y_structure.conclusion)
        z = "    RAA, " + str(j + 1) + "–" + str(i + 1)
        if is_final:
            for i in y_structure.assumptions.formulas:
                if i in in_which_context_is_formula.keys():
                    in_which_context_is_formula[i].append(proof_so_far.__len__())
                else:
                    in_which_context_is_formula[i] = [proof_so_far.__len__()]
            if y_structure.conclusion in which_conclusion_is_formula.keys():
                which_conclusion_is_formula[y_structure.conclusion].append(proof_so_far.__len__())
            else:
                which_conclusion_is_formula[y_structure.conclusion] = [proof_so_far.__len__()]
        return (x + y + z), y_structure
    elif next_rule == "TND":
        rule = TertioNonDatur(oracle=oracle(randomFormula(depth, variables)))
        y_structure = rule.top_down([])
        y = to_infix(y_structure.conclusion)
        z = "    TND"
        if is_final:
            for i in y_structure.assumptions.formulas:
                if i in in_which_context_is_formula.keys():
                    in_which_context_is_formula[i].append(proof_so_far.__len__())
                else:
                    in_which_context_is_formula[i] = [proof_so_far.__len__()]
            if y_structure.conclusion in which_conclusion_is_formula.keys():
                which_conclusion_is_formula[y_structure.conclusion].append(proof_so_far.__len__())
            else:
                which_conclusion_is_formula[y_structure.conclusion] = [proof_so_far.__len__()]
        return (x + y + z), y_structure
    elif next_rule == "∨-elimination":




        '''
        candidates = []
        for i in range(proof_so_far_structure.__len__()):
            if isinstance(proof_so_far_structure[i].conclusion, Disjunction):
                dis = proof_so_far_structure[i].conclusion
                if (dis.Left() in in_which_context_is_formula.keys()) and (dis.Right() in in_which_context_is_formula.keys()):
                    candidates1 = in_which_context_is_formula[dis.Left()]
                    candidates2 = in_which_context_is_formula[dis.Right()]
                else:
                    candidates1 = []
                    candidates2 = []
                for j in candidates1:
                    candidates2_filtered = set(candidates2).intersection(set(which_conclusion_is_formula[proof_so_far_structure[j].conclusion]))
                    if candidates2_filtered != set():
                        candidates.append([i, j, candidates2_filtered])
        '''
        candidates_dis = []
        for i , I in enumerate(proof_so_far_structure):
            if isinstance(I.conclusion, Disjunction):
                if in_which_context_is_formula.get(I.conclusion.Left(),[]).__len__() + in_which_context_is_formula.get(I.conclusion.Right(),[]).__len__() != 0:
                    candidates_dis.append([i,in_which_context_is_formula.get(I.conclusion.Left(),[]).__len__()+in_which_context_is_formula.get(I.conclusion.Right(),[]).__len__()])
        candidates_rho = []
        for i in which_conclusion_is_formula.keys():
            candidates_rho.append([i,which_conclusion_is_formula[i].__len__()])
        if candidates_rho == [] or candidates_dis == []:
            return ""
        for i in range(10000):
            dis_idx = random.choices(candidates_dis, weights=[c[1] for c in candidates_dis], k=1)[0][0]
            rho = random.choices(candidates_rho, weights=[c[1] for c in candidates_rho], k=1)[0][0]
            dis = proof_so_far_structure[dis_idx].conclusion
            phi = dis.Left()
            psi = dis.Right()
            phi_candidates = set(in_which_context_is_formula.get(phi,[])).intersection(set(which_conclusion_is_formula.get(rho,[])))
            psi_candidates = set(in_which_context_is_formula.get(psi,[])).intersection(set(which_conclusion_is_formula.get(rho,[])))
            if phi_candidates != set() and psi_candidates != set():
                idxs = [dis_idx,random.choice(list(phi_candidates)),random.choice(list(psi_candidates))]
                break
            if i == 9999:
                return ""


        #idxs = random.choices(candidates, weights=[len(c[2]) for c in candidates], k=1)[0]
        #idxs[2] = random.choice(list(idxs[2]))
        rule = DisjunctionElimination()
        y_structure = rule.top_down([proof_so_far_structure[idxs[0]], proof_so_far_structure[idxs[1]], proof_so_far_structure[idxs[2]]])
        y = to_infix(y_structure.conclusion)
        z = f"    ∨-elimination, {idxs[0] + 1}, {idxs[1] + 1}, {idxs[2] + 1}"
        if is_final:
            for i in y_structure.assumptions.formulas:
                if i in in_which_context_is_formula.keys():
                    in_which_context_is_formula[i].append(proof_so_far.__len__())
                else:
                    in_which_context_is_formula[i] = [proof_so_far.__len__()]
            if y_structure.conclusion in which_conclusion_is_formula.keys():
                which_conclusion_is_formula[y_structure.conclusion].append(proof_so_far.__len__())
            else:
                which_conclusion_is_formula[y_structure.conclusion] = [proof_so_far.__len__()]
        return (x + y + z), y_structure
        #candidates = []
        #for i in range(proof_so_far_structure.__len__()):
        #    candidates_pairs = []
        #    if isinstance(proof_so_far_structure[i].conclusion, Disjunction):
        #        dis = proof_so_far_structure[i].conclusion
        #        if (dis.Left() in in_which_context_is_formula.keys()) and (dis.Right() in in_which_context_is_formula.keys()):
        #            candidates1 = in_which_context_is_formula[dis.Left()]
        #            candidates2 = in_which_context_is_formula[dis.Right()]
        #        else:
        #            candidates1 = []
        #            candidates2 = []
        #        candidates11 = []
        #        candidates21 = []
        #        for j in range(proof_so_far_structure.__len__()):
        #            if dis.Left() in proof_so_far_structure[j].assumptions.formulas:
        #                candidates11.append(j)
        #            if dis.Right() in proof_so_far_structure[j].assumptions.formulas:
        #                candidates21.append(j)
        #        for j in candidates1:
        #            for k in candidates2:
        #                if proof_so_far_structure[j].conclusion == proof_so_far_structure[k].conclusion:
        #                    candidates_pairs.append([j, k])
        #        if candidates_pairs.__len__() != 0:
        #            candidates.append([i, candidates_pairs])
        #if candidates == []:
        #    return ""
        #I = random.choice(candidates)
        #i = I[0]
        #km = random.choice(I[1])
        #k = km[0]
        #m = km[1]
        #candidates = []
        #for j in range(proof_so_far_structure.__len__()):
        #    if proof_so_far_structure[j].conclusion == proof_so_far_structure[i].conclusion.Left():
        #        candidates.append(j)
        #j = random.choice(candidates)
        #candidates = []
        #for l in range(proof_so_far_structure.__len__()):
        #    proof_so_far_structure[l].conclusion, "x", proof_so_far_structure[i].conclusion.Right()
        #    if proof_so_far_structure[l].conclusion == proof_so_far_structure[i].conclusion.Right():
        #        candidates.append(l)
        #l = random.choice(candidates)
        #rule = DisjunctionElimination()
        #y_structure = rule.top_down([proof_so_far_structure[i],
        #                             proof_so_far_structure[k],
        #                             proof_so_far_structure[m]])
        #y = to_infix(y_structure.conclusion)
        #z = f"    ∨-elimination, {i + 1}, {j + 1}–{k + 1}, {l + 1}–{m + 1}"
        #return (x + y + z), y_structure
    elif next_rule == "¬¬-elimination":
        candidates = []
        for i in range(proof_so_far_structure.__len__()):
            if isinstance(proof_so_far_structure[i].conclusion, Negation):
                if isinstance(proof_so_far_structure[i].conclusion.Left(), Negation):
                    candidates.append(i)
        if candidates == []:
            return ""
        i = random.choice(candidates)
        rule = NegationOfNegation()
        y_structure = rule.top_down([proof_so_far_structure[i]])
        y = to_infix(y_structure.conclusion)
        z = f"    ¬¬-elimination, {i + 1}"
        if is_final:
            for i in y_structure.assumptions.formulas:
                if i in in_which_context_is_formula.keys():
                    in_which_context_is_formula[i].append(proof_so_far.__len__())
                else:
                    in_which_context_is_formula[i] = [proof_so_far.__len__()]
            if y_structure.conclusion in which_conclusion_is_formula.keys():
                which_conclusion_is_formula[y_structure.conclusion].append(proof_so_far.__len__())
            else:
                which_conclusion_is_formula[y_structure.conclusion] = [proof_so_far.__len__()]
        return (x + y + z), y_structure
    elif next_rule == "∧-elimination":
        candidates = []
        for i in range(proof_so_far_structure.__len__()):
            if isinstance(proof_so_far_structure[i].conclusion, Conjunction):
                candidates.append(i)
        if candidates == []:
            return ""
        i = random.choice(candidates)
        which_one = random.choice([0, 1])
        if which_one == 0:
            rule = ConjunctionElimination1()
        else:
            rule = ConjunctionElimination2()
        y_structure = rule.top_down([proof_so_far_structure[i]])
        y = to_infix(y_structure.conclusion)
        z = f"    ∧-elimination, {i + 1}"
        if is_final:
            for i in y_structure.assumptions.formulas:
                if i in in_which_context_is_formula.keys():
                    in_which_context_is_formula[i].append(proof_so_far.__len__())
                else:
                    in_which_context_is_formula[i] = [proof_so_far.__len__()]
            if y_structure.conclusion in which_conclusion_is_formula.keys():
                which_conclusion_is_formula[y_structure.conclusion].append(proof_so_far.__len__())
            else:
                which_conclusion_is_formula[y_structure.conclusion] = [proof_so_far.__len__()]
        return (x + y + z), y_structure





    elif next_rule == "↔-elimination":
        candidates = []
        which_one = random.choice([0, 1])
        for i in range(proof_so_far_structure.__len__()):
            if isinstance(proof_so_far_structure[i].conclusion, Iff):
                if which_one == 0:
                    if which_conclusion_is_formula.get(proof_so_far_structure[i].conclusion.Left(), []) != []:
                        candidates.append(i)
                else:
                    if which_conclusion_is_formula.get(proof_so_far_structure[i].conclusion.Right(), []) != []:
                        candidates.append(i)
        if candidates == []:
            return ""
        def weight(x):
            if which_one == 0:
                phi = proof_so_far_structure[x].conclusion.Left()
            else:
                phi = proof_so_far_structure[x].conclusion.Right()
            ans = which_conclusion_is_formula.get(phi,[]).__len__()
            return ans

        i = random.choices(candidates, weights=[weight(c) for c in candidates])[0]
        phi = proof_so_far_structure[i].conclusion.Left() if which_one == 0 else proof_so_far_structure[i].conclusion.Right()
        j = random.choice(which_conclusion_is_formula[phi])
        if which_one == 0:
            rule = IffElimination1()
        else:
            rule = IffElimination2()
        lp1 = proof_so_far_structure[i]
        lp2 = proof_so_far_structure[j]
        y_structure = rule.top_down([lp1, lp2])
        y = to_infix(y_structure.conclusion)
        z = f"    ↔-elimination, {i + 1}, {j + 1}"
        if is_final:
            for i in y_structure.assumptions.formulas:
                if i in in_which_context_is_formula.keys():
                    in_which_context_is_formula[i].append(proof_so_far.__len__())
                else:
                    in_which_context_is_formula[i] = [proof_so_far.__len__()]
            if y_structure.conclusion in which_conclusion_is_formula.keys():
                which_conclusion_is_formula[y_structure.conclusion].append(proof_so_far.__len__())
            else:
                which_conclusion_is_formula[y_structure.conclusion] = [proof_so_far.__len__()]
        return (x + y + z), y_structure




    elif next_rule == "⊤-introduction":
        rule = TruthIntroduction()
        y_structure = rule.top_down([])
        y = to_infix(y_structure.conclusion)
        z = f"    ⊤-introduction"
        if is_final:
            for i in y_structure.assumptions.formulas:
                if i in in_which_context_is_formula.keys():
                    in_which_context_is_formula[i].append(proof_so_far.__len__())
                else:
                    in_which_context_is_formula[i] = [proof_so_far.__len__()]
            if y_structure.conclusion in which_conclusion_is_formula.keys():
                which_conclusion_is_formula[y_structure.conclusion].append(proof_so_far.__len__())
            else:
                which_conclusion_is_formula[y_structure.conclusion] = [proof_so_far.__len__()]
        return (x + y + z), y_structure



    elif next_rule == "→-elimination":
        candidates = []
        for i in range(proof_so_far_structure.__len__()):
            if isinstance(proof_so_far_structure[i].conclusion, Implication):
                phi = proof_so_far_structure[i].conclusion.Left()
                if which_conclusion_is_formula.get(phi,[]) != []:
                    candidates.append(i)
        if candidates == []:
            return ""
        def weight(x):
            phi = proof_so_far_structure[x].conclusion.Left()
            ans = which_conclusion_is_formula.get(phi,[]).__len__()
            return ans
        i = random.choices(candidates, weights=[weight(c) for c in candidates])[0]
        phi = proof_so_far_structure[i].conclusion.Left()
        j = random.choice(which_conclusion_is_formula.get(phi,[]))
        rule = ImplicationElimination()
        y_structure = rule.top_down([proof_so_far_structure[i], proof_so_far_structure[j]])
        y = to_infix(y_structure.conclusion)
        z = f"    →-elimination, {i + 1}, {j + 1}"
        if is_final:
            for i in y_structure.assumptions.formulas:
                if i in in_which_context_is_formula.keys():
                    in_which_context_is_formula[i].append(proof_so_far.__len__())
                else:
                    in_which_context_is_formula[i] = [proof_so_far.__len__()]
            if y_structure.conclusion in which_conclusion_is_formula.keys():
                which_conclusion_is_formula[y_structure.conclusion].append(proof_so_far.__len__())
            else:
                which_conclusion_is_formula[y_structure.conclusion] = [proof_so_far.__len__()]
        return (x + y + z), y_structure



    elif next_rule == "⊥-elimination":
        candidates = []
        for i in range(proof_so_far_structure.__len__()):
            if proof_so_far_structure[i].conclusion == Lie():
                candidates.append(i)
        if candidates == []:
            return ""
        i = random.choice(candidates)
        rule = LieElimination()
        y_structure = rule.top_down([proof_so_far_structure[i]])
        y = to_infix(y_structure.conclusion)
        z = f"    ⊥-elimination, {i + 1}"
        if is_final:
            for i in y_structure.assumptions.formulas:
                if i in in_which_context_is_formula.keys():
                    in_which_context_is_formula[i].append(proof_so_far.__len__())
                else:
                    in_which_context_is_formula[i] = [proof_so_far.__len__()]
            if y_structure.conclusion in which_conclusion_is_formula.keys():
                which_conclusion_is_formula[y_structure.conclusion].append(proof_so_far.__len__())
            else:
                which_conclusion_is_formula[y_structure.conclusion] = [proof_so_far.__len__()]
        return (x + y + z), y_structure
    elif next_rule == "↔-introduction":
        candidates = []
        '''
        for i in range(proof_so_far_structure.__len__()):
            if proof_so_far_structure[i].conclusion in in_which_context_is_formula.keys():
                for j in in_which_context_is_formula[proof_so_far_structure[i].conclusion]:
                    lp1 = proof_so_far_structure[i]
                    lp2 = proof_so_far_structure[j]
                    if lp1.conclusion in lp2.assumptions.formulas:
                        if lp2.conclusion in lp1.assumptions.formulas:
                            candidates.append([i, j])
        if candidates == []:
            return ""
        '''

        for k in range(1000):
            i = random.choice(range(proof_so_far_structure.__len__()))
            j = random.choice(range(proof_so_far_structure.__len__()))
            if i in in_which_context_is_formula.get(proof_so_far_structure[j].conclusion,[]):
                if j in in_which_context_is_formula.get(proof_so_far_structure[i].conclusion,[]):
                    break
            if k == 999:
                return ""

        #idxs = candidates[random.randint(0, candidates.__len__() - 1)]
        #i,j = idxs[0],idxs[1]
        lp1 = proof_so_far_structure[i]
        lp2 = proof_so_far_structure[j]

        rule = IffIntroduction()
        y_structure = rule.top_down([lp1,lp2])
        y = to_infix(y_structure.conclusion)
        z = f"    ↔-introduction, {i + 1}, {j + 1}"
        if is_final:
            for i in y_structure.assumptions.formulas:
                if i in in_which_context_is_formula.keys():
                    in_which_context_is_formula[i].append(proof_so_far.__len__())
                else:
                    in_which_context_is_formula[i] = [proof_so_far.__len__()]
            if y_structure.conclusion in which_conclusion_is_formula.keys():
                which_conclusion_is_formula[y_structure.conclusion].append(proof_so_far.__len__())
            else:
                which_conclusion_is_formula[y_structure.conclusion] = [proof_so_far.__len__()]
        return (x + y + z), y_structure

        #candidates = []
        #for i in range(proof_so_far_structure.__len__()):
        #    if proof_so_far_structure[i].conclusion in in_which_context_is_formula.keys():
        #        for j in in_which_context_is_formula[proof_so_far_structure[i].conclusion]:
        #            lp1 = proof_so_far_structure[i]
        #            lp2 = proof_so_far_structure[j]
        #            if lp1.conclusion in lp2.assumptions.formulas:
        #                if lp2.conclusion in lp1.assumptions.formulas:
        #                    candidates.append([i, j])
        #if candidates == []:
        #    return ""
        #I = random.choice(candidates)
        #l = I[1]
        #j = I[0]
        #candidates = []
        #psi = proof_so_far_structure[j].conclusion
        #phi = proof_so_far_structure[l].conclusion
        #for i in range(j + 1):
        #    if proof_so_far_structure[i].conclusion == phi:
        #        candidates.append(i)
        #i = random.choice(candidates)
        #candidates = []
        #for k in range(l + 1):
        #    if proof_so_far_structure[k].conclusion == psi:
        #        candidates.append(k)
        #k = random.choice(candidates)
        #rule = IffIntroduction()
        #lp1 = proof_so_far_structure[j]
        #lp2 = proof_so_far_structure[l]
        #y_structure = rule.top_down([lp1, lp2])
        #y = to_infix(y_structure.conclusion)
        #z = f"    ↔-introduction, {i + 1}–{j + 1}, {k + 1}–{l + 1}"
        #return (x + y + z), y_structure
    return ""





import re
def extract_proof(proof, line_number):
    if  isinstance(proof, str):
        proof = proof.splitlines()
    idxs = set()
    idxs.add(line_number-1)
    new_idxs = set()#te które mamy w zbiorze, ale nie mamy jeszcze ich sąsiadów
    new_idxs.add(line_number-1)
    while new_idxs.__len__() != 0:
        i = random.choice(list(new_idxs))
        new_idxs.remove(i)
        newest_idxs = re.findall(r"\d+",proof[i])
        for j in newest_idxs:
            if not int(j)-1 in idxs:
                idxs.add(int(j)-1)
                new_idxs.add(int(j)-1)
    idxs = sorted(list(idxs))
    ans = ""
    for i in idxs:
        ans += proof[i] +"\n"
    ans = ans.splitlines()
    for i in range(ans.__len__()):
        ans[i] = re.split(r"([. ,–])",ans[i])
    new_idxs = dict()
    for i in range(idxs.__len__()):
        new_idxs[str(idxs[i]+1)] = str(i+1)
    for i in range(ans.__len__()):
        for j in range(ans[i].__len__()):
            if ans[i][j] in new_idxs.keys():
                ans[i][j] = new_idxs[ans[i][j]]
    for i in range(ans.__len__()):
        new_line = ""
        for j in ans[i]:
            new_line += j
        ans[i] = new_line
    final_ans = ""
    for i in ans:
        final_ans += i
        final_ans += "\n"
    return final_ans[:-1]