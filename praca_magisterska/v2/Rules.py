import sys
from pathlib import Path

# adjust if your path differs
PROJECT_ROOT = Path.home() / "PycharmProjects" / "Magisterka"
PKG_ROOT = PROJECT_ROOT / "nanoGPT-20251228T135841Z-3-001" / "nanoGPT"

sys.path.insert(0, str(PKG_ROOT))

from praca_magisterska.v1.TermAndFormulas import *
from abc import abstractmethod
from praca_magisterska.v1.ContextsAndLP import *
import numpy as np
from praca_magisterska.v2.HelpfullFunctions import *
import random
class Rule:
    @abstractmethod
    def __init__(self,a,b):
        idx = -1
        pass
    @abstractmethod
    def bottom_up(self ,x):
        pass
    @abstractmethod
    def top_down(self ,x):
        pass
    def default_weakening_oracle_bottom_up(x,*args):
        return 0

    def default_oracle_phi_bottom_up(x,*args):
        if not(isinstance(x,LittleProblem)):
            raise TypeError("Bad arguments")
        return TermAndFormulas.Truth()
    def default_oracle_phi_top_down_generate(x,*args):
        if not(isinstance(x,LittleProblem)):
            raise TypeError("Bad arguments")
        return TermAndFormulas.Truth()
    def default_oracle_phi_top_down_choose(x,*args):
        if not(isinstance(x,LittleProblem)):
            raise TypeError("Bad arguments")
        return random.choice(x.assumptions.formulas)

    def default_oracle_2assumptions_bottom_up(x,*args):
        if not(isinstance(x, LittleProblem)):
            raise TypeError("Bad arguments")
        ans1 = Context()
        ans2 = Context()
        choice_codes = np.random.choice([-1,0,1], x.assumptions.formulas.__len__())
        for i in range(choice_codes.__len__()):
            if choice_codes[i] == -1:
                ans2 += x.assumptions.formulas[i]
            if choice_codes[i] == 0:
                ans1 += x.assumptions.formulas[i]
                ans2 += x.assumptions.formulas[i]
            if choice_codes[i] == 1:
                ans1 += x.assumptions.formulas[i]
        return ans1,ans2

    def default_oracle_3assumptions_bottom_up(x,*args):
        if not(isinstance(x, ContextsAndLP.LittleProblem)):
            raise TypeError("Bad arguments")
        ans1 = Context()
        ans2 = Context()
        ans3 = Context()
        choice_codes = np.random.choice([1,2,3,12,13,23,123], x.assumptions.formulas.__len__())
        for i in range(choice_codes.__len__()):
            if choice_codes[i] in [1,12,13,123]:
                ans1 += x.assumptions.formulas[i]
            if choice_codes[i] in [2,12,23,123]:
                ans2 += x.assumptions.formulas[i]
            if choice_codes[i] in [3,13,23,123]:
                ans3 += x.assumptions.formulas[i]
        return ans1,ans2,ans3

    def default_oracle_top_down_phi_from_nothing():
        print("default_oracle_top_down_phi_from_nothing")
        return Truth()

    def default_oracle_variable_choose(x,*args):
        if not isinstance(x,LittleProblem):
            raise TypeError("Bad arguments")
        v = Variable("v")
        variables = FreeVariables(x.conclusion)
        variables = variables.difference(FreeVariables(x.assumptions))
        variables.add(v)
        return random.choice(list(variables))

    def default_oracle_term(x,*args):
        if not isinstance(x,LittleProblem):
            raise TypeError("Bad arguments")
        v = Variable("v")
        return v

    def default_oracle_term_from_nothing():
        print("default_oracle_term_from_nothing")
        return Variable("v")
    def default_oracle_context():
        print("default_oracle_context")
        return Context()


class Assumption(Rule):
    def __init__(self,
                 oracle = Rule.default_oracle_top_down_phi_from_nothing):
        self.idx = 0
        self.oracle = oracle
    def bottom_up(self ,x):
        if (x.assumptions[0] == x.conclusion) and len(x.assumptions.formulas) == 1:
            return []
        else:
            raise TypeError("Bad arguments")
    def top_down(self,x):
        if x != []:
            raise TypeError("Bad arguments")
        phi = self.oracle()
        return LittleProblem(Context(phi),phi)

class Weakening(Rule):
    def __init__(self,
                 oracle_bottom_up = Rule.default_oracle_phi_top_down_choose,
                 oracle_top_down = Rule.default_oracle_phi_top_down_generate):
        self.idx = 1
        self.oracle_bottom_up = oracle_bottom_up
        self.oracle_top_down = oracle_top_down
    def bottom_up(self ,x): #może zwrócić coś nieprawdziwego
        #number_to_remove = self.oracle_bottom_up(x)
        #assumptions = Context(*(x.assumptions.formulas[:number_to_remove] +
        #                      x.assumptions.formulas[number_to_remove+1:]))
        #ans = [LittleProblem(assumptions,x.conclusion)]
        if not isinstance(x,LittleProblem):
            raise TypeError("Bad arguments")
        psi = self.oracle_bottom_up(x)
        if not psi in x.assumptions.formulas:
            raise TypeError("Bad arguments")
        ans_context =  x.assumptions - Context(psi)
        ans_conclusion = x.conclusion
        return LittleProblem(ans_context,ans_conclusion)
    def top_down(self,x):
        if not x.__len__() == 1:
            raise TypeError("Bad arguments")
        if not(isinstance(x[0],LittleProblem)):
            raise TypeError("Bad arguments")

        psi = self.oracle_top_down(x[0])
        if not isinstance(psi,Formula):
            raise TypeError("Bad arguments")
        phi = x[0].conclusion
        Gamma = x[0].assumptions
        return LittleProblem(Gamma + psi, phi)

class ImplicationIntroduction(Rule):
    def __init__(self,
                 oracle_top_down = Rule.default_oracle_phi_top_down_choose):
        self.idx = 2
        self.oracle_top_down = oracle_top_down
    def bottom_up(self ,x): #może zwrócić coś nieprawdziwego
        if not isinstance(x,LittleProblem):
            raise TypeError("Bad arguments")
        if isinstance(x.conclusion,Implication):
            ans_conclusion = x.conclusion.Right()
            ans_assumptions = x.assumptions + x.conclusion.Left()
            return [LittleProblem(ans_assumptions,ans_conclusion)]
        else:
            raise TypeError("Bad arguments")
    def top_down(self,x):
        if not x.__len__() == 1:
            raise TypeError("Bad arguments")
        if not(isinstance(x[0],LittleProblem)):
            raise TypeError("Bad arguments")
        phi = self.oracle_top_down(x[0])
        if not isinstance(phi,Formula):
            raise TypeError("Bad arguments")
        if not phi in x[0].assumptions.formulas:
            raise TypeError("Bad arguments")
        psi = x[0].conclusion
        Gamma = x[0].assumptions - phi
        return LittleProblem(Gamma, Implication(phi,psi))

class NegationIntroduction(Rule):
    def __init__(self,
                 oracle_top_down = Rule.default_oracle_phi_top_down_choose
                 ):
        self.idx = 3
        self.oracle_top_down = oracle_top_down
    def bottom_up(self ,x):
        if isinstance(x.conclusion,Negation):
            ans_conclusion = Lie()
            ans_assumptions = x.assumptions + x.conclusion
            return [LittleProblem(ans_assumptions,ans_conclusion)]
        else:
            raise TypeError("Bad arguments")
    def top_down(self,x):
        if x.__len__() != 1:
            raise TypeError("Bad arguments")
        if not isinstance(x[0],LittleProblem):
            raise TypeError("Bad arguments")
        if not(isinstance(x[0].conclusion,Lie)):
            raise TypeError("Bad arguments")
        if x[0].assumptions.formulas.__len__() == 0:
            raise TypeError("Bad arguments")
        phi = self.oracle_top_down(x[0])
        if not isinstance(phi,Formula):
            raise TypeError("Bad arguments")
        if not phi in x[0].assumptions.formulas:
            raise TypeError("Bad arguments")
        Gamma = x[0].assumptions - phi
        return LittleProblem(Gamma, Negation(phi))

class ImplicationElimination(Rule): #Trzeba przetestować!!!!
    def __init__(self,
                 oracle_assumptions_bottom_up = Rule.default_oracle_2assumptions_bottom_up,
                 oracle_phi_bottom_up =  Rule.default_oracle_phi_bottom_up
                 ):
        self.idx = 4
        self.oracle_assumptions_bottom_up = oracle_assumptions_bottom_up
        self.oracle_phi_bottom_up = oracle_phi_bottom_up
    def bottom_up(self ,x):
        if not(isinstance(x,LittleProblem)):
            raise TypeError("Bad arguments")
        Gamma1, Gamma2 = self.oracle_assumptions_bottom_up(x)
        for i in (Gamma1+Gamma2).formulas:
            if not i in x.assumptions.formulas:
                raise TypeError("Bad arguments")
        for i in x.assumptions.formulas:
            if not i in (Gamma1+Gamma2).formulas:
                raise TypeError("Bad arguments")
        phi = self.oracle_phi_bottom_up(x)
        if not isinstance(phi,Formula):
            raise TypeError("Bad arguments")
        psi = x.conclusion
        ans1 = LittleProblem(Gamma1,Implication(phi,psi))
        ans2 = LittleProblem(Gamma2,phi)
        return [ans1,ans2]
    def top_down(self,x):
        if x.__len__() != 2:
            raise TypeError("Bad arguments")
        if not (isinstance(x[0],LittleProblem) and  isinstance(x[1],LittleProblem)):
            raise TypeError("Bad arguments")
        if  not(isinstance(x[0].conclusion,Implication)):
            raise TypeError("Bad arguments")
        if x[0].conclusion.Left() != x[1].conclusion:
            raise TypeError("Bad arguments")
        psi = x[0].conclusion.Right()
        ans_assumptions = x[0].assumptions + x[1].assumptions
        return LittleProblem(ans_assumptions,psi)

class NegationElimination(Rule):
    def __init__(self,
                 oracle_assumptions_bottom_up = Rule.default_oracle_2assumptions_bottom_up,
                 oracle_phi_bottom_up =  Rule.default_oracle_phi_bottom_up
                 ):
        self.idx = 5
        self.oracle_assumptions_bottom_up = oracle_assumptions_bottom_up
        self.oracle_phi_bottom_up = oracle_phi_bottom_up
    def bottom_up(self ,x):
        if not(isinstance(x,LittleProblem)):
            raise TypeError("Bad arguments")
        if not(isinstance(x.conclusion,Lie)):
            raise TypeError("Bad arguments")
        Gamma1, Gamma2 = self.oracle_assumptions_bottom_up(x)
        for i in (Gamma1+Gamma2).formulas:
            if not i in x.assumptions.formulas:
                raise TypeError("Bad arguments")
        for i in x.assumptions.formulas:
            if not i in (Gamma1+Gamma2).formulas:
                raise TypeError("Bad arguments")
        phi = self.oracle_phi_bottom_up(x)
        if not isinstance(phi,Formula):
            raise TypeError("Bad arguments")
        ans1 = LittleProblem(Gamma1,Negation(phi))
        ans2 = LittleProblem(Gamma2,phi)
        return [ans1,ans2]
    def top_down(self,x):
        if x.__len__() != 2:
            raise TypeError("Bad arguments")
        if not (isinstance(x[0],LittleProblem) and isinstance(x[1],LittleProblem)):
            raise TypeError("Bad arguments")
        if not isinstance(x[0].conclusion,Negation):
            raise TypeError("Bad arguments")
        if x[0].conclusion.Left() != x[1].conclusion:
            raise TypeError("Bad arguments")
        Gamma = x[0].assumptions + x[1].assumptions
        return LittleProblem(Gamma,Lie())

class ConjunctionIntroduction(Rule):
    def __init__(self,
                 oracle_bottom_up = Rule.default_oracle_2assumptions_bottom_up):
        self.idx = 6
        self.oracle_bottom_up = oracle_bottom_up
    def bottom_up(self ,x):
        if not isinstance(x,LittleProblem):
            raise TypeError("Bad arguments")
        if not isinstance(x.conclusion,Conjunction):
            raise TypeError("Bad arguments")
        Gamma1, Gamma2 = self.oracle_bottom_up(x)
        for i in (Gamma1+Gamma2).formulas:
            if not i in x.assumptions.formulas:
                raise TypeError("Bad arguments")
        for i in x.assumptions.formulas:
            if not i in (Gamma1+Gamma2).formulas:
                raise TypeError("Bad arguments")
        ans1 = LittleProblem(Gamma1,x.conclusion.Left())
        ans2 = LittleProblem(Gamma2,x.conclusion.Right())
        return [ans1,ans2]
    def top_down(self,x):
        if x.__len__() != 2:
            raise TypeError("Bad arguments")
        if not (isinstance(x[0],LittleProblem) and isinstance(x[1],LittleProblem)):
            raise TypeError("Bad arguments")
        assumptions = x[0].assumptions + x[1].assumptions
        conclusion = Conjunction(x[0].conclusion,x[1].conclusion)
        return LittleProblem(assumptions,conclusion)

class DisjunctionIntroduction1(Rule):
    def __init__(self,
                 oracle_top_down = Rule.default_oracle_phi_top_down_generate):
        self.idx = 7
        self.oracle_top_down = oracle_top_down
    def bottom_up(self ,x):
        if not isinstance(x,LittleProblem):
            raise TypeError("Bad arguments")
        if not isinstance(x.conclusion,Disjunction):
            raise TypeError("Bad arguments")
        ans = LittleProblem(x.assumptions,x.conclusion.Left())
        return [ans]
    def top_down(self,x):
        if x.__len__() != 1:
            raise TypeError("Bad arguments")
        if not isinstance(x[0],LittleProblem):
            raise TypeError("Bad arguments")
        psi = self.oracle_top_down(x[0])
        if not isinstance(psi,Formula):
            raise TypeError("Bad arguments")
        phi = x[0].conclusion
        Gamma = x[0].assumptions
        return LittleProblem(Gamma,Disjunction(phi,psi))

class DisjunctionIntroduction2(Rule):
    def __init__(self,
                 oracle_top_down = Rule.default_oracle_phi_top_down_generate):
        self.idx = 8
        self.oracle_top_down = oracle_top_down
    def bottom_up(self ,x):
        if not isinstance(x,LittleProblem):
            raise TypeError("Bad arguments")
        if not isinstance(x.conclusion,Disjunction):
            raise TypeError("Bad arguments")
        ans = LittleProblem(x.assumptions,x.conclusion.Right())
        return [ans]
    def top_down(self,x):
        if x.__len__() != 1:
            raise TypeError("Bad arguments")
        if not isinstance(x[0],LittleProblem):
            raise TypeError("Bad arguments")
        phi = self.oracle_top_down(x[0])
        if not isinstance(phi,Formula):
            raise TypeError("Bad arguments")
        psi = x[0].conclusion
        Gamma = x[0].assumptions
        return LittleProblem(Gamma,Disjunction(phi,psi))

class TruthIntroduction(Rule):
    def __init__(self):
        self.idx = 9
    def bottom_up(self ,x):
        if not isinstance(x,LittleProblem):
            raise TypeError("Bad arguments")
        if not isinstance(x.conclusion,Truth):
            raise TypeError("Bad arguments")
        if not x.assumptions.formulas.__len__() == 0:
            raise TypeError("Bad arguments")
        else:
            return []
    def top_down(self,x):
        if x != []:
            raise TypeError("Bad arguments")
        return LittleProblem(Context(),Truth())

class ConjunctionElimination1(Rule):
    def __init__(self,
                 oracle_psi_bottom_up = Rule.default_oracle_phi_bottom_up):
        self.idx = 10
        self.oracle_psi_bottom_up = oracle_psi_bottom_up
    def bottom_up(self ,x):
        ans_assumptions = x.assumptions
        psi = self.oracle_psi_bottom_up(x)
        if not isinstance(psi,Formula):
            raise TypeError("Bad arguments")
        ans_conclusion = Conjunction(x.conclusion,psi)
        return [LittleProblem(ans_assumptions,ans_conclusion)]
    def top_down(self,x):
        if x.__len__() != 1:
            raise TypeError("Bad arguments")
        if not isinstance(x[0],LittleProblem):
            raise TypeError("Bad arguments")
        if not isinstance(x[0].conclusion,Conjunction):
            raise TypeError("Bad arguments")
        Lambda = x[0].assumptions
        phi = x[0].conclusion.Left()
        return LittleProblem(Lambda,phi)

class ConjunctionElimination2(Rule):
    def __init__(self,
                 oracle_phi_bottom_up = Rule.default_oracle_phi_bottom_up):
        self.idx = 11
        self.oracle_phi_bottom_up = oracle_phi_bottom_up
    def bottom_up(self ,x):
        ans_assumptions = x.assumptions
        phi = self.oracle_phi_bottom_up(x)
        if not isinstance(phi,Formula):
            raise TypeError("Bad arguments")
        ans_conclusion = Conjunction(phi,x.conclusion)
        return [LittleProblem(ans_assumptions,ans_conclusion)]
    def top_down(self,x):
        if x.__len__() != 1:
            raise TypeError("Bad arguments")
        if not isinstance(x[0],LittleProblem):
            raise TypeError("Bad arguments")
        if not isinstance(x[0].conclusion,Conjunction):
            raise TypeError("Bad arguments")
        Lambda = x[0].assumptions
        psi = x[0].conclusion.Right()
        return LittleProblem(Lambda,psi)

class DisjunctionElimination(Rule):
    def __init__(self,
                 oracle_phi_bottom_up = Rule.default_oracle_phi_bottom_up,
                 oracle_psi_bottom_up = Rule.default_oracle_phi_bottom_up,
                 oracle_assumptions_bottom_up = Rule.default_oracle_3assumptions_bottom_up):
        self.idx = 12
        self.oracle_psi_bottom_up = oracle_psi_bottom_up
        self.oracle_assumptions_bottom_up = oracle_assumptions_bottom_up
        self.oracle_phi_bottom_up = oracle_phi_bottom_up
    def bottom_up(self ,x):
        Gamma1 , Gamma2 , Gamma3 = self.oracle_assumptions_bottom_up(x)
        for i in (Gamma1+Gamma2+Gamma3).formulas:
            if not i in x.assumptions.formulas:
                raise TypeError("Bad arguments")
        for i in x.assumptions.formulas:
            if not i in (Gamma1+Gamma2+Gamma3).formulas:
                raise TypeError("Bad arguments")
        phi = self.oracle_phi_bottom_up(x)
        if not isinstance(phi,Formula):
            raise TypeError("Bad arguments")
        psi = self.oracle_psi_bottom_up(x)
        if not isinstance(psi,Formula):
            raise TypeError("Bad arguments")
        rho = x.conclusion
        conclusion1 = Disjunction(phi,psi)
        conclusion2 = rho
        conclusion3 = rho
        ans1 = LittleProblem(Gamma1,conclusion1)
        ans2 = LittleProblem(Gamma2 + phi , conclusion2)
        ans3 = LittleProblem(Gamma3 + psi , conclusion3)
        return [ans1,ans2,ans3]
    def top_down(self,x):
        if x.__len__() != 3:
            raise TypeError("Bad arguments")
        if not (isinstance(x[0],LittleProblem) and isinstance(x[1],LittleProblem) and isinstance(x[2],LittleProblem)):
            raise TypeError("Bad arguments")
        if (x[1].assumptions.formulas.__len__() == 0) or (x[2].assumptions.formulas.__len__() == 0):
            raise TypeError("Bad arguments")
        if not isinstance(x[0].conclusion,Disjunction):
            raise TypeError("Bad arguments")
        if x[1].conclusion != x[2].conclusion:
            raise TypeError("Bad arguments")
        phi = x[0].conclusion.Left()
        psi = x[0].conclusion.Right()
        if not phi in x[1].assumptions.formulas:
            raise TypeError("Bad arguments")
        if not psi in x[2].assumptions.formulas:
            raise TypeError("Bad arguments")
        Gamma1 = x[0].assumptions
        Gamma2 = x[1].assumptions - phi
        Gamma3 = x[2].assumptions - psi
        rho = x[1].conclusion
        return LittleProblem(Gamma1+Gamma2+Gamma3,rho)

class LieElimination(Rule):
    def __init__(self,
                 top_down_oracle = Rule.default_oracle_phi_top_down_generate):
        self.idx = 13
        self.top_down_oracle = top_down_oracle
    def bottom_up(self ,x):
        if not isinstance(x,LittleProblem):
            raise TypeError("Bad arguments")
        ans = LittleProblem(x.assumptions,Lie())
        return [ans]
    def top_down(self,x):
        if x.__len__() != 1:
            raise TypeError("Bad arguments")
        if not isinstance(x[0],LittleProblem):
            raise TypeError("Bad arguments")
        if not isinstance(x[0].conclusion,Lie):
            raise TypeError("Bad arguments")
        Gamma = x[0].assumptions
        phi = self.top_down_oracle(x[0])
        if not isinstance(phi,Formula):
            raise TypeError("Bad arguments")
        return LittleProblem(Gamma,phi)

class IffIntroduction(Rule):
    def __init__(self,
                 oracle_assumptions_bottom_up = Rule.default_oracle_2assumptions_bottom_up):
        self.idx = 14
        self.oracle_assumptions_bottom_up = oracle_assumptions_bottom_up
    def bottom_up(self ,x):
        if not isinstance(x,LittleProblem):
            raise TypeError("Bad arguments")
        if not isinstance(x.conclusion,Iff):
            raise TypeError("Bad arguments")
        Gamma1,Gamma2 = self.oracle_assumptions_bottom_up(x)
        for i in (Gamma1+Gamma2).formulas:
            if not i in x.assumptions.formulas:
                raise TypeError("Bad arguments")
        for i in x.assumptions.formulas:
            if not i in (Gamma1+Gamma2).formulas:
                raise TypeError("Bad arguments")
        phi = x.conclusion.Right()
        psi = x.conclusion.Left()
        ans1 = LittleProblem(Gamma1+phi,psi)
        ans2 = LittleProblem(Gamma2+psi,phi)
        return [ans1,ans2]
    def top_down(self,x):
        if x.__len__() != 2:
            raise TypeError("Bad arguments")
        if not (isinstance(x[0],LittleProblem) and isinstance(x[1],LittleProblem)):
            raise TypeError("Bad arguments")
        if not x[0].conclusion in x[1].assumptions.formulas:
            raise TypeError("Bad arguments")
        if not x[1].conclusion in x[0].assumptions.formulas:
            raise TypeError("Bad arguments")
        psi = x[0].conclusion
        phi = x[1].conclusion
        Gamma1 = x[0].assumptions - phi
        Gamma2 = x[1].assumptions - psi
        assumptions = Gamma1 + Gamma2
        conclusion = Iff(phi,psi)
        return LittleProblem(assumptions,conclusion)

class IffElimination1(Rule):
    def __init__(self,
                 oracle_assumptions_bottom_up = Rule.default_oracle_2assumptions_bottom_up,
                 oracle_phi_bottom_up = Rule.default_oracle_phi_bottom_up):
        self.idx= 15
        self.oracle_assumptions_bottom_up = oracle_assumptions_bottom_up
        self.oracle_phi_bottom_up = oracle_phi_bottom_up
    def bottom_up(self ,x):
        if not isinstance(x,LittleProblem):
            raise TypeError("Bad arguments")
        Gamma1,Gamma2 = self.oracle_assumptions_bottom_up(x)
        for i in (Gamma1+Gamma2).formulas:
            if not i in x.assumptions.formulas:
                raise TypeError("Bad arguments")
        for i in x.assumptions.formulas:
            if not i in (Gamma1+Gamma2).formulas:
                raise TypeError("Bad arguments")
        psi = x.conclusion
        phi = self.oracle_phi_bottom_up(x)
        ans1 = LittleProblem(Gamma1,Iff(phi,psi))
        ans2 = LittleProblem(Gamma2,phi)
        return [ans1,ans2]
    def top_down(self,x):
        if x.__len__() != 2:
            raise TypeError("Bad arguments")
        if not (isinstance(x[0],LittleProblem) and isinstance(x[1],LittleProblem)):
            raise TypeError("Bad arguments")
        if not isinstance(x[0].conclusion,Iff):
            raise TypeError("Bad arguments")
        if x[0].conclusion.Left() != x[1].conclusion:
            raise TypeError("Bad arguments")
        Gamma1 = x[0].assumptions
        Gamma2 = x[1].assumptions
        psi = x[0].conclusion.Right()
        return LittleProblem(Gamma1 + Gamma2 , psi)

class IffElimination2(Rule):
    def __init__(self,
                 oracle_assumptions_bottom_up = Rule.default_oracle_2assumptions_bottom_up,
                 oracle_psi_bottom_up = Rule.default_oracle_phi_bottom_up):
        self.idx= 16
        self.oracle_assumptions_bottom_up = oracle_assumptions_bottom_up
        self.oracle_psi_bottom_up = oracle_psi_bottom_up
    def bottom_up(self ,x):
        if not isinstance(x,LittleProblem):
            raise TypeError("Bad arguments")
        Gamma1,Gamma2 = self.oracle_assumptions_bottom_up(x)
        for i in (Gamma1+Gamma2).formulas:
            if not i in x.assumptions.formulas:
                raise TypeError("Bad arguments")
        for i in x.assumptions.formulas:
            if not i in (Gamma1+Gamma2).formulas:
                raise TypeError("Bad arguments")
        phi = x.conclusion
        psi = self.oracle_psi_bottom_up(x)
        ans1 = LittleProblem(Gamma1,Iff(phi,psi))
        ans2 = LittleProblem(Gamma2,psi)
        return [ans1,ans2]
    def top_down(self,x):
        if x.__len__() != 2:
            raise TypeError("Bad arguments")
        if not (isinstance(x[0],LittleProblem) and isinstance(x[1],LittleProblem)):
            raise TypeError("Bad arguments")
        if not isinstance(x[0].conclusion,Iff):
            raise TypeError("Bad arguments")
        if x[0].conclusion.Right() != x[1].conclusion:
            raise TypeError("Bad arguments")
        Gamma1 = x[0].assumptions
        Gamma2 = x[1].assumptions
        phi = x[0].conclusion.Left()
        return LittleProblem(Gamma1 + Gamma2 , phi)

class ReductionAdAbsurdum(Rule):
    def __init__(self,
                 top_down_oracle = Rule.default_oracle_phi_top_down_choose):
        self.idx = 17
        self.top_down_oracle = top_down_oracle
    def bottom_up(self ,x):
        if not isinstance(x,LittleProblem):
            return TypeError("Bad arguments")
        phi = x.conclusion
        assumptions = x.assumptions + Negation(phi)
        conclusion = Lie()
        return [LittleProblem(assumptions,conclusion)]
    def top_down(self,x):
        if x.__len__() != 1:
            raise TypeError("Bad arguments")
        if not isinstance(x[0],LittleProblem):
            raise TypeError("Bad arguments")
        if not isinstance(x[0].conclusion,Lie):
            raise TypeError("Bad arguments")
        too_choose_assumptions = []
        for i in x[0].assumptions.formulas:
            if isinstance(i,Negation):
                too_choose_assumptions.append(i)
        if too_choose_assumptions.__len__() == 0:
            raise TypeError("Bad arguments")
        to_choose = LittleProblem(Context(*too_choose_assumptions),Truth())
        neg_phi = self.top_down_oracle(to_choose)
        if not neg_phi in to_choose.assumptions.formulas:
            raise TypeError("Bad arguments")
        phi = neg_phi.Left()
        Gamma = x[0].assumptions - Negation(phi)
        return LittleProblem(Gamma,phi)

class NegationOfNegation(Rule):
    def __init__(self):
        self.idx = 18
    def bottom_up(self ,x):
        assumptions = x.assumptions
        conclusion = Negation(Negation(x.conclusion))
        return [LittleProblem(assumptions,conclusion)]
    def top_down(self,x):
        if x.__len__() != 1:
            raise TypeError("Bad arguments")
        if not isinstance(x[0],LittleProblem):
            raise TypeError("Bad arguments")
        if not isinstance(x[0].conclusion,Negation):
            raise TypeError("Bad arguments")
        if not isinstance(x[0].conclusion.Left(),Negation):
            raise TypeError("Bad arguments")
        phi = x[0].conclusion.Left().Left()
        Gamma = x[0].assumptions
        return LittleProblem(Gamma,phi)

class TertioNonDatur(Rule):
    def __init__(self,
                 oracle = Rule.default_oracle_top_down_phi_from_nothing):
        self.idx = 19
        self.oracle = oracle
    def bottom_up(self ,x):
        if not isinstance(x,LittleProblem):
            raise TypeError("Bad arguments")
        if x.assumptions.formulas.__len__() != 0:
            raise TypeError("Bad arguments")
        if not isinstance(x.conclusion,Disjunction):
            raise TypeError("Bad arguments")
        if not isinstance(x.conclusion.Right(),Negation):
            raise TypeError("Bad arguments")
        if x.conclusion.Right().Left() != x.conclusion.Left():
            raise TypeError("Bad arguments")
        return []
    def top_down(self,x):
        if x != []:
            raise TypeError("Bad arguments")
        phi = self.oracle()
        if not isinstance(phi,Formula):
            raise TypeError("Bad arguments")
        conclusion = Disjunction(phi,Negation(phi))
        return LittleProblem(Context(),conclusion)


