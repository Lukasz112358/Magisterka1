#%%
from re import findall

from praca_magisterska.v1.Scoring import normalise, how_many_times_was
from praca_magisterska.v2.ContextsAndLP import LittleProblem
from praca_magisterska.v2.TermAndFormulas import *
from praca_magisterska.v2.ContextsAndLP import *
from praca_magisterska.v2.HelpfullFunctions import *
import re


from typing import List




#%%
import sys
from pathlib import Path

# adjust if your path differs
PROJECT_ROOT = Path.home() / "PycharmProjects" / "Magisterka"
PKG_ROOT = PROJECT_ROOT / "nanoGPT-20251228T135841Z-3-001" / "nanoGPT"

sys.path.insert(0, str(PKG_ROOT))


class Rule:
    @abstractmethod
    def __init__(self,a,b):
        idx = -1
        pass
    @abstractmethod
    def bottom_up(self ,*args):
        pass
    @abstractmethod
    def top_down(self ,*args):
        pass
    def __str__(self):
        return self.__class__.__name__
    def __repr__(self):
        return self.__class__.__name__

#%% md
# REGUŁY
#%%
class Assumption(Rule):
    def __init__(self):
        self.idx = 0
    def top_down(self,x,phi = Truth(),BaseContext = []):
        if not x == []:
            raise TypeError("Bad arguments")
        if not isinstance(phi,Formula):
            raise TypeError("Bad arguments")
        if not isinstance(BaseContext,list):
            raise TypeError("Bad arguments")
        for i in BaseContext:
            if not isinstance(i, Formula):
                raise TypeError("Bad arguments")
        Left = Context(BaseContext , [phi])
        Right = phi
        return LittleProblem(Left,Right)
    def bottom_up(self ,x):
        if not isinstance(x,LittleProblem):
            raise TypeError("Bad arguments")
        phi = x.conclusion
        if x.assumptions.additional_context.__len__() == 0:
            if not phi in x.assumptions.BaseContext :
                raise TypeError("Bad arguments")
        elif x.assumptions.additional_context.__len__() == 1:
            if not phi in x.assumptions.additional_context:
                raise TypeError("Bad arguments")
        else:
            raise TypeError("Bad arguments")
        return []
class Weakening(Rule): #Najpierw formuła , potem kontekst
    def __init__(self):
        self.idx = 1
    def top_down(self, x, psi=Truth()):
        if not isinstance(x, list):
            raise TypeError("Bad arguments")
        if not x.__len__() == 1:
            raise TypeError("Bad arguments")
        lp = x[0]
        if not isinstance(lp, LittleProblem):
            raise TypeError("Bad arguments")
        if not isinstance(psi, Formula):
            raise TypeError("Bad arguments")
        Left = lp.assumptions + psi
        Right = lp.conclusion
        return LittleProblem(Left, Right)

    def bottom_up(self, x,psi = Truth()):
        if not isinstance(x, LittleProblem):
            raise TypeError("Bad arguments")
        if not isinstance(psi, Formula):
            raise TypeError("Bad arguments")
        if not psi in x.assumptions:
            raise TypeError("Bad arguments")
        Left = x.assumptions - psi
        Right = x.conclusion
        return [LittleProblem(Left, Right)]
class ImplicationIntroduction(Rule):
    def __init__(self):
        self.idx = 2
    def top_down(self,x,phi = Truth):
        if not isinstance(x, list):
            raise TypeError("Bad arguments")
        if x.__len__() != 1:
            raise TypeError("Bad arguments")
        if not isinstance(x[0],LittleProblem):
            raise TypeError("Bad arguments")
        if not phi in x[0].assumptions:
            raise TypeError("Bad arguments")
        psi = x[0].conclusion
        Gamma = x[0].assumptions - phi
        return LittleProblem(Gamma, Implication(phi,psi))
    def bottom_up(self ,x):
        if not isinstance(x,LittleProblem):
            raise TypeError("Bad arguments")
        if isinstance(x.conclusion,Implication):
            ans_conclusion = x.conclusion.Right()
            ans_assumptions = x.assumptions + x.conclusion.Left()
            return [LittleProblem(ans_assumptions,ans_conclusion)]
        else:
            raise TypeError("Bad arguments")
class NegationIntroduction(Rule):
    def __init__(self):
        self.idx = 3

    def top_down(self, x, phi = Truth()):
        #print(x)
        if not isinstance(x, list):
            raise TypeError("Bad arguments")
        if x.__len__() != 1:
            raise TypeError("Bad arguments")
        if not isinstance(x[0], LittleProblem):
            raise TypeError("Bad arguments")
        if not isinstance(phi, Formula):
            raise TypeError("Bad arguments")
        if not isinstance(x[0].conclusion, Lie):
            raise TypeError("Bad arguments")
        if not phi in x[0].assumptions:
            raise TypeError("Bad arguments")
        Gamma = x[0].assumptions - phi
        return LittleProblem(Gamma, Negation(phi))

    def bottom_up(self, x):
        if not isinstance(x, LittleProblem):
            raise TypeError("Bad arguments")
        if not isinstance(x.conclusion, Negation):
            raise TypeError("Bad arguments")
        phi = x.conclusion.Left()
        Gamma = x.assumptions
        return [LittleProblem(Gamma + phi, Lie())]
class ImplicationElimination(Rule):  # (→E)
    def __init__(self):
        self.idx = 4
    def top_down(self,x):
        if not isinstance(x,list):
            raise TypeError("Bad arguments")
        if x.__len__() != 2:
            raise TypeError("Bad arguments")
        if not (isinstance(x[0],LittleProblem) and isinstance(x[1],LittleProblem)):
            raise TypeError("Bad arguments")
        if  set(x[0].assumptions.base_context) != set(x[1].assumptions.base_context):
            raise TypeError("Bad arguments")
        if not isinstance(x[0].conclusion,Implication):
            raise TypeError("Bad arguments")
        if x[0].conclusion.Left() != x[1].conclusion:
            raise TypeError("Bad arguments")
        Gamma1 = x[0].assumptions
        Gamma2 = x[1].assumptions
        psi = x[0].conclusion.Right()
        return LittleProblem(Gamma1 + Gamma2 , psi)
    def bottom_up(self, x,Gamma1 = Context([],[]),Gamma2= Context([],[]),phi = Truth()):
        if not isinstance(x, LittleProblem):
            raise TypeError("Bad arguments")
        if not isinstance(Gamma1, Context):
            raise TypeError("Bad arguments")
        if not isinstance(Gamma2, Context):
            raise TypeError("Bad arguments")
        if not isinstance(phi, Formula):
            raise TypeError("Bad arguments")
        if not Gamma1 + Gamma2 == x.assumptions:
            raise TypeError("Bad arguments")
        psi = x.conclusion
        First = LittleProblem(Gamma1,Implication(phi,psi))
        Second = LittleProblem(Gamma2,phi)
        return [First,Second]
class NegationElimination(Rule):
    def __init__(self):
        self.idx = 5
    def top_down(self , x):
        if not isinstance(x, list):
            raise TypeError("Bad arguments")
        if x.__len__() != 2:
            raise TypeError("Bad arguments")
        if not isinstance(x[0], LittleProblem) and isinstance(x[1], LittleProblem):
            raise TypeError("Bad arguments")
        if  set(x[0].assumptions.base_context) != set(x[1].assumptions.base_context):
            raise TypeError("Bad arguments")
        if not isinstance(x[0].conclusion, Negation):
            raise TypeError("Bad arguments")
        phi = x[0].conclusion.Left()
        if x[1].conclusion != phi:
            raise TypeError("Bad arguments")
        Gamma1 = x[0].assumptions
        Gamma2 = x[1].assumptions
        return LittleProblem(Gamma1 + Gamma2 , Lie())
    def bottom_up(self ,x,Gamma1 = Context([],[]),Gamma2= Context([],[]),phi = Truth()):
        if not isinstance(x, LittleProblem):
            raise TypeError("Bad arguments")
        if not isinstance(Gamma1, Context):
            raise TypeError("Bad arguments")
        if not isinstance(Gamma2, Context):
            raise TypeError("Bad arguments")
        if not isinstance(phi, Formula):
            raise TypeError("Bad arguments")
        if not Gamma1 + Gamma2 == x.assumptions:
            raise TypeError("Bad arguments")
        if not x.conclusion == Lie():
            raise TypeError("Bad arguments")
        First = LittleProblem(Gamma1,Negation(phi))
        Second = LittleProblem(Gamma2,phi)
        return [First,Second]
class ConjunctionIntroduction(Rule):
    def __init__(self):
        self.idx = 6
    def top_down(self , x):
        if not isinstance(x, list):
            raise TypeError("Bad arguments")
        if x.__len__() != 2:
            raise TypeError("Bad arguments")
        if not isinstance(x[0], LittleProblem) and isinstance(x[1], LittleProblem):
            raise TypeError("Bad arguments")
        if  set(x[0].assumptions.base_context) != set(x[1].assumptions.base_context):
            raise TypeError("Bad arguments")
        Gamma1 = x[0].assumptions
        Gamma2 = x[1].assumptions
        phi = x[0].conclusion
        psi = x[1].conclusion
        return LittleProblem(Gamma1 + Gamma2 , Conjunction(phi,psi))
    def bottom_up(self ,x,Gamma1 = Context([],[]),Gamma2= Context([],[])):
        if not isinstance(x, LittleProblem):
            raise TypeError("Bad arguments")
        if not isinstance(Gamma1, Context):
            raise TypeError("Bad arguments")
        if not isinstance(Gamma2, Context):
            raise TypeError("Bad arguments")
        if not Gamma1 + Gamma2 == x.assumptions:
            raise TypeError("Bad arguments")
        if not isinstance(x.conclusion,Conjunction):
            raise TypeError("Bad arguments")
        phi = x.conclusion.Left()
        psi = x.conclusion.Right()
        First = LittleProblem(Gamma1,phi)
        Second = LittleProblem(Gamma2,psi)
        return [First,Second]
class DisjunctionIntroduction1(Rule):
    def __init__(self):
        self.idx = 7
    def top_down(self, x, psi=Truth()):
        if not isinstance(x, list):
            raise TypeError("Bad arguments")
        if not x.__len__() == 1:
            raise TypeError("Bad arguments")
        lp = x[0]
        if not isinstance(lp, LittleProblem):
            raise TypeError("Bad arguments")
        if not isinstance(psi, Formula):
            raise TypeError("Bad arguments")
        Left = lp.assumptions
        Right = Disjunction(lp.conclusion,psi)
        return LittleProblem(Left, Right)
    def bottom_up(self, x):
        if not isinstance(x, LittleProblem):
            raise TypeError("Bad arguments")
        if not isinstance(x.conclusion, Disjunction):
            raise TypeError("Bad arguments")
        Left = x.assumptions
        Right = x.conclusion.Left()
        return [LittleProblem(Left, Right)]
class DisjunctionIntroduction2(Rule):
    def __init__(self):
        self.idx = 8
    def top_down(self, x, phi=Truth()):
        if not isinstance(x, list):
            raise TypeError("Bad arguments")
        if not x.__len__() == 1:
            raise TypeError("Bad arguments")
        lp = x[0]
        if not isinstance(lp, LittleProblem):
            raise TypeError("Bad arguments")
        if not isinstance(phi, Formula):
            raise TypeError("Bad arguments")
        Left = lp.assumptions
        Right = Disjunction(phi,lp.conclusion)
        return LittleProblem(Left, Right)
    def bottom_up(self, x):
        if not isinstance(x, LittleProblem):
            raise TypeError("Bad arguments")
        if not isinstance(x.conclusion, Disjunction):
            raise TypeError("Bad arguments")
        Left = x.assumptions
        Right = x.conclusion.Right()
        return [LittleProblem(Left, Right)]
class TruthIntroduction(Rule):
    def __init__(self):
        self.idx = 9
    def top_down(self,x,BaseContext = []):
        if not x == []:
            raise TypeError("Bad arguments")
        if not isinstance(BaseContext,list):
            raise TypeError("Bad arguments")
        for i in BaseContext:
            if not isinstance(i, Formula):
                raise TypeError("Bad arguments")
        Left = Context(BaseContext ,[])
        Right = Truth()
        return LittleProblem(Left,Right)
    def bottom_up(self ,x):
        if not isinstance(x,LittleProblem):
            raise TypeError("Bad arguments")
        if not x.assumptions.additional_context == []:
            raise TypeError("Bad arguments")
        if not x.conclusion == Truth():
            raise TypeError("Bad arguments")
        return []

class ConjunctionElimination1(Rule):
    def __init__(self):
        self.idx = 10
    def top_down(self ,x):
        if not isinstance(x,list):
            raise TypeError("Bad arguments")
        if x.__len__() != 1:
            raise TypeError("Bad arguments")
        if not isinstance(x[0],LittleProblem):
            raise TypeError("Bad arguments")
        if not isinstance(x[0].conclusion,Conjunction):
            raise TypeError("Bad arguments")
        phi = x[0].conclusion.Left()
        Gamma = x[0].assumptions
        return LittleProblem(Gamma , phi)
    def bottom_up(self,x,psi  = Truth()):
        if not isinstance(x, LittleProblem):
            raise TypeError("Bad arguments")
        if not isinstance(psi, Formula):
            raise TypeError("Bad arguments")
        phi = x.conclusion
        Gamma = x.assumptions
        return [LittleProblem(Gamma,Conjunction(phi,psi))]

class ConjunctionElimination2(Rule):
    def __init__(self):
        self.idx = 11
    def top_down(self ,x):
        if not isinstance(x,list):
            raise TypeError("Bad arguments")
        if x.__len__() != 1:
            raise TypeError("Bad arguments")
        if not isinstance(x[0],LittleProblem):
            raise TypeError("Bad arguments")
        if not isinstance(x[0].conclusion,Conjunction):
            raise TypeError("Bad arguments")
        psi = x[0].conclusion.Right()
        Gamma = x[0].assumptions
        return LittleProblem(Gamma , psi)
    def bottom_up(self,x,phi  = Truth()):
        if not isinstance(x, LittleProblem):
            raise TypeError("Bad arguments")
        if not isinstance(phi, Formula):
            raise TypeError("Bad arguments")
        psi = x.conclusion
        Gamma = x.assumptions
        return [LittleProblem(Gamma,Conjunction(phi,psi))]

class DisjunctionElimination(Rule):
    def __init__(self):
        self.idx = 12
    def top_down(self ,x):
        if not isinstance(x,list):
            raise TypeError("Bad arguments")
        if x.__len__() != 3:
            raise TypeError("Bad arguments")
        if not (isinstance(x[0],LittleProblem) and isinstance(x[1],LittleProblem)) and isinstance(x[2],LittleProblem):
            raise TypeError("Bad arguments")
        if  set(x[0].assumptions.base_context) != set(x[1].assumptions.base_context):
            raise TypeError("Bad arguments")
        if  set(x[0].assumptions.base_context) != set(x[2].assumptions.base_context):
            raise TypeError("Bad arguments")
        if  set(x[1].assumptions.base_context) != set(x[2].assumptions.base_context):
            raise TypeError("Bad arguments")
        if not isinstance(x[0].conclusion,Disjunction):
            raise TypeError("Bad arguments")
        phi = x[0].conclusion.Left()
        psi = x[0].conclusion.Right()
        if not phi in x[1].assumptions:
            raise TypeError("Bad arguments")
        if not psi in x[2].assumptions:
            raise TypeError("Bad arguments")
        Gamma1 = x[0].assumptions
        Gamma2 = x[1].assumptions - phi
        Gamma3 = x[2].assumptions - psi
        if not x[1].conclusion == x[2].conclusion:
            raise TypeError("Bad arguments")
        rho = x[1].conclusion
        return LittleProblem(Gamma1 + Gamma2 + Gamma3 , rho)
    def bottom_up(self,x,Gamma1 = Context([],[]),Gamma2= Context([],[]),Gamma3= Context([],[]),phi = Truth(),psi = Truth()):
        if not isinstance(x, LittleProblem):
            raise TypeError("Bad arguments")
        if not isinstance(Gamma1, Context):
            raise TypeError("Bad arguments")
        if not isinstance(Gamma2, Context):
            raise TypeError("Bad arguments")
        if not isinstance(Gamma3, Context):
            raise TypeError("Bad arguments")
        if not Gamma1 + Gamma2 + Gamma3 == x.assumptions:
            raise TypeError("Bad arguments")
        rho = x.conclusion
        First  = LittleProblem(Gamma1,Disjunction(phi,psi))
        Second = LittleProblem(Gamma2+phi,rho)
        Third  = LittleProblem(Gamma3+psi,rho)
        return [First,Second,Third]
class LieElimination(Rule):
    def __init__(self):
        self.idx = 13
    def top_down(self,x,phi = Truth()):
        if not isinstance(x,list):
            raise TypeError("Bad arguments")
        if not x.__len__() == 1:
            raise TypeError("Bad arguments")
        if not isinstance(x[0],LittleProblem):
            raise TypeError("Bad arguments")
        if not isinstance(x[0].conclusion,Lie):
            raise TypeError("Bad arguments")
        if not isinstance(phi, Formula):
            raise TypeError("Bad arguments")
        Gamma = x[0].assumptions
        return LittleProblem(Gamma, phi)
    def bottom_up(self ,x):
        if not isinstance(x,LittleProblem):
            raise TypeError("Bad arguments")
        return [LittleProblem(x.assumptions,Lie())]
class IffIntroduction(Rule):
    def __init__(self):
        self.idx = 14
    def top_down(self,x):
        if not isinstance(x,list):
            raise TypeError("Bad arguments")
        if not x.__len__() == 2:
            raise TypeError("Bad arguments")
        if not (isinstance(x[0],LittleProblem) and isinstance(x[1],LittleProblem)):
            raise TypeError("Bad arguments")
        if  set(x[0].assumptions.base_context) != set(x[1].assumptions.base_context):
            raise TypeError("Bad arguments")
        psi = x[0].conclusion
        phi = x[1].conclusion
        if not (psi in x[1].assumptions and phi in x[0].assumptions):
            raise TypeError("Bad arguments")
        Gamma1 = x[0].assumptions - psi
        Gamma2 = x[1].assumptions - phi
        return LittleProblem(Gamma1 + Gamma2 , Iff(phi,psi))
    def bottom_up(self,x, Gamma1 = Context([],[]),Gamma2= Context([],[])):
        if not isinstance(x, LittleProblem):
            raise TypeError("Bad arguments")
        if not isinstance(Gamma1, Context):
            raise TypeError("Bad arguments")
        if not isinstance(Gamma2, Context):
            raise TypeError("Bad arguments")
        if not isinstance(x.conclusion,Iff):
            raise TypeError("Bad arguments")
        phi = x.conclusion.Left()
        psi = x.conclusion.Right()
        if not Gamma1 + Gamma2== x.assumptions:
            raise TypeError("Bad arguments")
        First = LittleProblem(Gamma1+phi,psi)
        Second = LittleProblem(Gamma2+psi,phi)
        return [First,Second]

class IffElimination1(Rule):  # (→E)
    def __init__(self):
        self.idx = 15
    def top_down(self,x):
        if not isinstance(x,list):
            raise TypeError("Bad arguments")
        if x.__len__() != 2:
            raise TypeError("Bad arguments")
        if not (isinstance(x[0],LittleProblem) and isinstance(x[1],LittleProblem)):
            raise TypeError("Bad arguments")
        if  set(x[0].assumptions.base_context) != set(x[1].assumptions.base_context):
            raise TypeError("Bad arguments")
        if not isinstance(x[0].conclusion,Iff):
            raise TypeError("Bad arguments")
        if x[0].conclusion.Left() != x[1].conclusion:
            raise TypeError("Bad arguments")
        Gamma1 = x[0].assumptions
        Gamma2 = x[1].assumptions
        psi = x[0].conclusion.Right()
        return LittleProblem(Gamma1 + Gamma2 , psi)
    def bottom_up(self, x,Gamma1 = Context([],[]),Gamma2= Context([],[]),phi = Truth()):
        if not isinstance(x, LittleProblem):
            raise TypeError("Bad arguments")
        if not isinstance(Gamma1, Context):
            raise TypeError("Bad arguments")
        if not isinstance(Gamma2, Context):
            raise TypeError("Bad arguments")
        if not isinstance(phi, Formula):
            raise TypeError("Bad arguments")
        if not Gamma1 + Gamma2 == x.assumptions:
            raise TypeError("Bad arguments")
        psi = x.conclusion
        First = LittleProblem(Gamma1,Iff(phi,psi))
        Second = LittleProblem(Gamma2,phi)
        return [First,Second]
class IffElimination2(Rule):  # (→E)
    def __init__(self):
        self.idx = 16
    def top_down(self,x):
        if not isinstance(x,list):
            raise TypeError("Bad arguments")
        if x.__len__() != 2:
            raise TypeError("Bad arguments")
        if not (isinstance(x[0],LittleProblem) and isinstance(x[1],LittleProblem)):
            raise TypeError("Bad arguments")
        if  set(x[0].assumptions.base_context) != set(x[1].assumptions.base_context):
            raise TypeError("Bad arguments")
        if not isinstance(x[0].conclusion,Iff):
            raise TypeError("Bad arguments")
        if x[0].conclusion.Right() != x[1].conclusion:
            raise TypeError("Bad arguments")
        Gamma1 = x[0].assumptions
        Gamma2 = x[1].assumptions
        phi = x[0].conclusion.Left()
        return LittleProblem(Gamma1 + Gamma2 , phi)
    def bottom_up(self, x,Gamma1 = Context([],[]),Gamma2= Context([],[]),psi = Truth()):
        if not isinstance(x, LittleProblem):
            raise TypeError("Bad arguments")
        if not isinstance(Gamma1, Context):
            raise TypeError("Bad arguments")
        if not isinstance(Gamma2, Context):
            raise TypeError("Bad arguments")
        if not isinstance(psi, Formula):
            raise TypeError("Bad arguments")
        if not Gamma1 + Gamma2 == x.assumptions:
            raise TypeError("Bad arguments")
        phi = x.conclusion
        First = LittleProblem(Gamma1,Iff(phi,psi))
        Second = LittleProblem(Gamma2,psi)
        return [First,Second]
class RAA(Rule):
    def __init__(self):
        self.idx = 17
    def top_down(self,x,phi = Truth()):
        if not isinstance(x,list):
            raise TypeError("Bad arguments")
        if x.__len__() != 1:
            raise TypeError("Bad arguments")
        if not isinstance(x[0],LittleProblem):
            raise TypeError("Bad arguments")
        if not isinstance(x[0].conclusion,Lie):
            raise TypeError("Bad arguments")
        if not isinstance(phi, Formula):
            raise TypeError("Bad arguments")
        if not Negation(phi) in x[0].assumptions:
            raise TypeError("Bad arguments")
        Gamma = x[0].assumptions - Negation(phi)
        return LittleProblem(Gamma,phi)
    def bottom_up(self,x):
        if not isinstance(x, LittleProblem):
            raise TypeError("Bad arguments")
        phi = x.conclusion
        Gamma = x.assumptions
        Left = Gamma + Negation(phi)
        Right = Lie()
        return [LittleProblem(Left,Right)]
class NegationOfNegation(Rule):
    def __init__(self):
        self.idx = 18
    def top_down(self,x):
        if not isinstance(x,list):
            raise TypeError("Bad arguments")
        if x.__len__() != 1:
            raise TypeError("Bad arguments")
        if not isinstance(x[0],LittleProblem):
            raise TypeError("Bad arguments")
        if not isinstance(x[0].conclusion,Negation):
            raise TypeError("Bad arguments")
        if not isinstance(x[0].conclusion.Left(),Negation):
            raise TypeError("Bad arguments")
        phi = x[0].conclusion.Left().Left()
        return LittleProblem(x[0].assumptions,phi)
    def bottom_up(self,x):
        if not isinstance(x, LittleProblem):
            raise TypeError("Bad arguments")
        phi = x.conclusion
        return [LittleProblem(x.assumptions,Negation(Negation(phi)))]
class TND(Rule):
    def __init__(self):
        self.idx = 19
    def top_down(self ,x,phi = Truth(),BaseContext = []):
        if not x == []:
            raise TypeError("Bad arguments")
        if not isinstance(BaseContext,list):
            raise TypeError("Bad arguments")
        for i in BaseContext:
            if not isinstance(i, Formula):
                raise TypeError("Bad arguments")
        if not isinstance(phi, Formula):
            raise TypeError("Bad arguments")
        Right = Disjunction(phi,Negation(phi))
        Left = Context(BaseContext,[])
        return LittleProblem(Left,Right)
    def bottom_up(self,x):
        if not isinstance(x, LittleProblem):
            raise TypeError("Bad arguments")
        if not isinstance(x.conclusion,Disjunction):
            raise TypeError("Bad arguments")
        if not Negation(x.conclusion.Left()) == x.conclusion.Right():
            raise TypeError("Bad arguments")
        if not x.assumptions.additional_context == []:
            raise TypeError("Bad arguments")
        return []
class FromContext(Rule):
    def __init__(self):
        self.idx = 20
    def top_down(self ,x,phi = Truth()):
        if not isinstance(x,list):
            raise TypeError("Bad arguments")
        if x.__len__() != 1:
            raise TypeError("Bad arguments")
        if not isinstance(x[0],LittleProblem):
            raise TypeError("Bad arguments")
        if not isinstance(phi, Formula):
            raise TypeError("Bad arguments")
        if not (phi in x[0].assumptions.base_context or phi in x[0].assumptions.additional_context):
            raise TypeError("Bad arguments")
        return LittleProblem(x[0].assumptions,phi)
    def bottom_up(self,x,phi = Truth()):
        if not isinstance(x, LittleProblem):
            raise TypeError("Bad arguments")
        if not isinstance(phi, Formula):
            raise TypeError("Bad arguments")
        if not (phi in x.assumptions.base_context or phi in x.assumptions.additional_context):
            raise TypeError("Bad arguments")
        return [LittleProblem(x.assumptions,phi)]

class FromWeakenContext(Rule):
    def __init__(self):
        self.idx = 20
    def top_down(self ,x,phi = Truth()):
        if not isinstance(x,list):
            raise TypeError("Bad arguments")
        if x.__len__() != 1:
            raise TypeError("Bad arguments")
        if not isinstance(x[0],LittleProblem):
            raise TypeError("Bad arguments")
        if not isinstance(phi, Formula):
            raise TypeError("Bad arguments")
        return LittleProblem(x[0].assumptions+phi,phi)
    def bottom_up(self,x,phi = Truth()):
        pass
#%% md
# STRUCTURE OF LINE I PARSOWANIE ZWYKLYCH DOWODOW
#%%
def to_infix_LP(LP: LittleProblem) -> str:
    ans = ""
    for i in LP.assumptions.base_context:
        ans += to_infix(i) + ", "
    ans = ans[:-2]
    ans += " ; "
    for i in LP.assumptions.additional_context:
        ans += to_infix(i) + ", "
    ans = ans[:-2]
    ans += " ⊢ " + to_infix(LP.conclusion)
    return ans

#SPRAWDZIC TO!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
#DODAC ZAPIS STRINGA
#WEAKENING NIE DZIAŁA JAK SIE ODWOŁUJE DO LP.CONCLUSION
class structure_of_line_top_down:
    def __init__(self,Key: int, args_keys: list[int], rule: Rule,Proof_so_far:dict,formula_text : str ,BaseContext: list = []):
        self.Key = Key
        self.args_keys = args_keys
        self.rule = rule
        self.formula_text_parsed = parse_infix(formula_text)
        match rule:
            case Assumption():
                phi = parse_infix(formula_text)
                self.LP = rule.top_down([],phi = phi, BaseContext = BaseContext)

            case Weakening():#Najpierw formuła potem kontekst. 2.phi Weakening i, j
                psi = Proof_so_far[args_keys[0]].LP.conclusion
                x = [Proof_so_far[args_keys[1]].LP]
                self.LP = rule.top_down(x,psi)

            case ImplicationIntroduction():
                phi = Proof_so_far[args_keys[0]].LP.conclusion
                x = [Proof_so_far[args_keys[1]].LP]
                self.LP = rule.top_down(x,phi=phi)

            case NegationIntroduction():
                x = [Proof_so_far[args_keys[1]].LP]
                phi = Proof_so_far[args_keys[0]].LP.conclusion
                self.LP = rule.top_down(x,phi=phi)

            case ImplicationElimination():
                x = [Proof_so_far[args_keys[0]].LP,Proof_so_far[args_keys[1]].LP]
                self.LP = rule.top_down(x)

            case NegationElimination():
                x = [Proof_so_far[args_keys[0]].LP,Proof_so_far[args_keys[1]].LP]
                self.LP = rule.top_down(x)

            case ConjunctionIntroduction():
                x = [Proof_so_far[args_keys[0]].LP,Proof_so_far[args_keys[1]].LP]
                self.LP = rule.top_down(x)

            case DisjunctionIntroduction1():
                psi = parse_infix(formula_text).Right()
                x = [Proof_so_far[args_keys[0]].LP]
                self.LP = rule.top_down(x,psi=psi)

            case DisjunctionIntroduction2():
                phi = parse_infix(formula_text).Left()
                x = [Proof_so_far[args_keys[0]].LP]
                self.LP = rule.top_down(x,phi=phi)

            case TruthIntroduction():
                x = []
                self.LP = rule.top_down(x,BaseContext = BaseContext)

            case ConjunctionElimination1():
                x = [Proof_so_far[args_keys[0]].LP]
                self.LP = rule.top_down(x)

            case ConjunctionElimination2():
                x = [Proof_so_far[args_keys[0]].LP]
                self.LP = rule.top_down(x)

            case DisjunctionElimination():
                x = [Proof_so_far[args_keys[0]].LP ,Proof_so_far[args_keys[1]].LP ,Proof_so_far[args_keys[2]].LP]
                self.LP = rule.top_down(x)

            case LieElimination():
                x = [Proof_so_far[args_keys[0]].LP]
                phi = parse_infix(formula_text)
                self.LP = rule.top_down(x,phi=phi)

            case IffIntroduction():
                x = [Proof_so_far[args_keys[0]].LP,Proof_so_far[args_keys[1]].LP]
                self.LP = rule.top_down(x)

            case IffElimination1():
                x = [Proof_so_far[args_keys[0]].LP,Proof_so_far[args_keys[1]].LP]
                #print(rule.top_down(x),"----")
                self.LP = rule.top_down(x)

            case IffElimination2():
                x = [Proof_so_far[args_keys[0]].LP,Proof_so_far[args_keys[1]].LP]
                self.LP = rule.top_down(x)

            case RAA():
                phi_neg = Proof_so_far[args_keys[0]].LP.conclusion
                if not isinstance(phi_neg,Negation):
                    raise TypeError("Bad arguments")
                phi = phi_neg.Left()
                x = [Proof_so_far[args_keys[1]].LP]
                self.LP = rule.top_down(x,phi=phi)

            case NegationOfNegation():
                x = [Proof_so_far[args_keys[0]].LP]
                self.LP = rule.top_down(x)

            case TND():
                x = []
                phi = parse_infix(formula_text).Left()
                self.LP = rule.top_down(x,phi=phi,BaseContext = BaseContext)
            case FromContext():
                if args_keys[0] == 0:
                    x = [LittleProblem(Context(BaseContext,[]),Truth())]
                else:
                    x = [Proof_so_far[args_keys[0]].LP]
                phi = parse_infix(formula_text)
                self.LP = rule.top_down(x,phi)
            case FromWeakenContext():
                if args_keys[0] == 0:
                    x = [LittleProblem(Context(BaseContext,[]),Truth())]
                else:
                    x = [Proof_so_far[args_keys[0]].LP]
                phi = parse_infix(formula_text)
                self.LP = rule.top_down(x,phi)
            case _:
                raise TypeError("Bad rule")


    def __str__(self):
        return str(self.Key) +" "+ str(self.args_keys) + " "+to_infix_LP(self.LP) +" "+ str(self.rule)
    def __repr__(self):
        return repr(self.Key) +" "+ repr(self.args_keys) +" "+ repr(self.LP) +" "+ repr(self.rule)
#%%
def parseProof(proof,base_context = []):
    text_splited = []
    proof = proof.split("\n")
    for i in proof:
        i_splited = i.split(".")
        i_splited = [i_splited[0]] + i_splited[1].split("  ")
        i_splited = list(filter(lambda x: x!= '',i_splited))
        ii = i_splited[:2]
        for I in i_splited[2:]:
            ii += i_splited[2].split(",")
        i_splited = list(filter(lambda x: x!= '',i_splited))
        i_splited_final = []
        for j in i_splited:
            i_splited_final += j.split("–")
        i_splited = i_splited_final
        i_splited_final = []
        for j in i_splited:
            i_splited_final += j.split(",")
        i_splited_final = list(filter(lambda x: x!= '',i_splited_final))
        for I in range(i_splited_final.__len__()):
            i_splited_final[I] = i_splited_final[I].replace(" ", "")
            i_splited_final[I] = i_splited_final[I].replace(",","")
        text_splited.append(i_splited_final)
    for i in range(len(text_splited)):
        idxs = []
        for j in range(len(text_splited[i])):
            if j == 0:
                text_splited[i][j] = int(text_splited[i][j])
            elif j == 1:
                pass
            elif j == 2:
                text_splited[i][j] = text_splited[i][j].replace(" ", "")
                match text_splited[i][j]:
                    case 'assumption':
                        text_splited[i][j] = Assumption()
                    case "weakening":
                        text_splited[i][j] = Weakening()
                    case "→-introduction":
                        text_splited[i][j] = ImplicationIntroduction()
                    case "¬-introduction":
                        text_splited[i][j] = NegationIntroduction()
                    case "→-elimination":
                        text_splited[i][j] = ImplicationElimination()
                    case "¬-elimination":
                        text_splited[i][j] = NegationElimination()
                    case "∧-introduction":
                        text_splited[i][j] = ConjunctionIntroduction()
                    case "∨-introduction1":
                        text_splited[i][j] = DisjunctionIntroduction1()
                    case "∨-introduction2":
                        text_splited[i][j] = DisjunctionIntroduction2()
                    case "⊤-introduction":
                        text_splited[i][j] = TruthIntroduction()
                    case "∧-elimination1":
                        text_splited[i][j] = ConjunctionElimination1()
                    case "∧-elimination2":
                        text_splited[i][j] = ConjunctionElimination2()
                    case "∨-elimination":
                        text_splited[i][j] = DisjunctionElimination()
                    case "⊥-elimination":
                        text_splited[i][j] = LieElimination()
                    case "↔-introduction":
                        text_splited[i][j] = IffIntroduction()
                    case "↔-elimination1":
                        text_splited[i][j] = IffElimination1()
                    case "↔-elimination2":
                        text_splited[i][j] = IffElimination2()
                    case "RAA":
                        text_splited[i][j] = RAA()
                    case "¬¬-elimination":
                        text_splited[i][j] = NegationOfNegation()
                    case "TND":
                        text_splited[i][j] = TND()
                    case "context":
                        text_splited[i][j] = FromContext()
                    case "contextWeak":
                        text_splited[i][j] = FromWeakenContext()
                    case _:

                        raise TypeError("Bad rule")
            else:
                idxs.append(int(text_splited[i][j]))
                if j == len(text_splited[i]) - 1:
                    text_splited[i][3] = idxs
                    text_splited[i] = text_splited[i][:4]
    ans = dict()
    for i in text_splited:
        #print(i)
        if len(i)  == 3:
            ans[i[0]] = structure_of_line_top_down(i[0],[],i[2],ans,formula_text=i[1],BaseContext=base_context)
            #print(to_infix_LP(ans[i[0]].LP),"---")
            #print(ans[i[0]])
            if ans[i[0]].LP.conclusion != parse_infix(i[1]):
                raise ValueError("Bad proof")

        else:

            ans[i[0]] = structure_of_line_top_down(i[0],i[3],i[2],ans,formula_text=i[1],BaseContext=base_context)
            #print(to_infix_LP(ans[i[0]].LP),"---")
            #print(ans[i[0]])
            if ans[i[0]].LP.conclusion != parse_infix(i[1]):
                raise ValueError("Bad proof")
        #print()
    return ans
proof = """1. s   assumption
2. ¬s   assumption
3. s    weakening, 2, 1
4. q    context, 0"""

parsedProof = parseProof(proof,base_context=[parse_infix("p"),parse_infix("q")])
print(parsedProof)


#%%
to_infix(Iff(Lie(),Lie()))
#%%
def remade_proof_line_text(proof_line: structure_of_line_top_down):
    match proof_line.rule:
        case Assumption():
            return str(proof_line.Key)+". "+ to_infix(proof_line.LP.conclusion) +"    assumption"
        case Weakening():
            return str(proof_line.Key)+". "+ to_infix(proof_line.LP.conclusion) +"    weakening, " + str(proof_line.args_keys[0]) +", " + str(proof_line.args_keys[1])
        case ImplicationIntroduction():
            return str(proof_line.Key) + ". " + to_infix(proof_line.LP.conclusion) +"    →-introduction, "+ str(proof_line.args_keys[0]) +"–" + str(proof_line.args_keys[1])
        case NegationIntroduction():
            return str(proof_line.Key) + ". " + to_infix(proof_line.LP.conclusion) +"    ¬-introduction, "+ str(proof_line.args_keys[0]) +"–" + str(proof_line.args_keys[1])
        case ImplicationElimination():
            return str(proof_line.Key)+". "+ to_infix(proof_line.LP.conclusion) +"    →-elimination, " + str(proof_line.args_keys[0]) +", " + str(proof_line.args_keys[1])
        case NegationElimination():
             return str(proof_line.Key)+". "+ to_infix(proof_line.LP.conclusion) +"    ¬-elimination, " + str(proof_line.args_keys[0]) +", " + str(proof_line.args_keys[1])
        case ConjunctionIntroduction():
            return str(proof_line.Key)+". "+ to_infix(proof_line.LP.conclusion) +"    ∧-introduction, " + str(proof_line.args_keys[0]) +", " + str(proof_line.args_keys[1])
        case DisjunctionIntroduction1():
            return str(proof_line.Key)+". "+ to_infix(proof_line.LP.conclusion) +"    ∨-introduction1, " + str(proof_line.args_keys[0])
        case DisjunctionIntroduction2():
            return str(proof_line.Key)+". "+ to_infix(proof_line.LP.conclusion) +"    ∨-introduction2, " + str(proof_line.args_keys[0])
        case TruthIntroduction():
            return str(proof_line.Key)+". "+ to_infix(proof_line.LP.conclusion) +"    ⊤-introduction"
        case ConjunctionElimination1():
            return str(proof_line.Key)+". "+ to_infix(proof_line.LP.conclusion) +"    ∧-elimination1, " + str(proof_line.args_keys[0])
        case ConjunctionElimination2():
            return str(proof_line.Key)+". "+ to_infix(proof_line.LP.conclusion) +"    ∧-elimination2, " + str(proof_line.args_keys[0])
        case DisjunctionElimination():
            return str(proof_line.Key)+". "+ to_infix(proof_line.LP.conclusion) +"    ∨-elimination, " + str(proof_line.args_keys[0]) +", " + str(proof_line.args_keys[1]) +", " + str(proof_line.args_keys[2])
        case LieElimination():
            return str(proof_line.Key)+". "+ to_infix(proof_line.LP.conclusion) +"    ⊥-elimination, " + str(proof_line.args_keys[0])
        case IffIntroduction():
            return str(proof_line.Key)+". "+ to_infix(proof_line.LP.conclusion) +"    ↔-introduction, " + str(proof_line.args_keys[0]) +", " + str(proof_line.args_keys[1])
        case IffElimination1():
            return str(proof_line.Key)+". "+ to_infix(proof_line.LP.conclusion) +"    ↔-elimination1, " + str(proof_line.args_keys[0]) +", " + str(proof_line.args_keys[1])
        case IffElimination2():
            return str(proof_line.Key)+". "+ to_infix(proof_line.LP.conclusion) +"    ↔-elimination2, " + str(proof_line.args_keys[0]) +", " + str(proof_line.args_keys[1])
        case RAA():
            return str(proof_line.Key)+". "+ to_infix(proof_line.LP.conclusion) +"    RAA, " + str(proof_line.args_keys[0]) +"–" + str(proof_line.args_keys[1])
        case NegationOfNegation():
            return str(proof_line.Key)+". "+ to_infix(proof_line.LP.conclusion) +"    ¬¬-elimination, " + str(proof_line.args_keys[0])
        case TND():
            return str(proof_line.Key)+". "+ to_infix(proof_line.LP.conclusion) +"    TND"
        case FromContext():
            return str(proof_line.Key)+". "+ to_infix(proof_line.LP.conclusion) +"    context, " + str(proof_line.args_keys[0])
        case FromWeakenContext():
            return str(proof_line.Key)+". "+ to_infix(proof_line.LP.conclusion) +"    contextWeak, " + str(proof_line.args_keys[0])
        case _:
            raise TypeError("Bad rule")

'''
match proof_line.rule:
    case Assumption():
    case Weakening():
    case ImplicationIntroduction():
    case NegationIntroduction():
    case ImplicationElimination():
    case NegationElimination():
    case ConjunctionIntroduction():
    case DisjunctionIntroduction1():
    case DisjunctionIntroduction2():
    case TruthIntroduction():
    case ConjunctionElimination1():
    case ConjunctionElimination2():
    case DisjunctionElimination():
    case LieElimination():
    case IffIntroduction():
    case IffElimination1():
    case IffElimination2():
    case RAA():
    case NegationOfNegation():
    case TND():
    case FromContext():
    case FromWeakenContext():
    case _:
'''
#%% md
# SPRAWDZANIE TAUTOLOGICZOŚĆI LP
#%%
def basing_context_of_LP(x:LittleProblem):
   base_context = x.assumptions.base_context + x.assumptions.additional_context
   return LittleProblem(Context(base_context,[]),x.conclusion)

def evaluate_formula(f,values):
    if isinstance(f,Truth):
        return True
    if isinstance(f,Lie):
        return False
    if isinstance(f,Atom):
        return values[f]
    if isinstance(f,Negation):
        return not evaluate_formula(f.Left(),values)
    if isinstance(f,Conjunction):
        return evaluate_formula(f.Left(),values) and evaluate_formula(f.Right(),values)
    if isinstance(f,Disjunction):
        return evaluate_formula(f.Left(),values) or evaluate_formula(f.Right(),values)
    if isinstance(f,Implication):
        return (not evaluate_formula(f.Left(),values)) or evaluate_formula(f.Right(),values)
    if isinstance(f,Iff):
        return evaluate_formula(f.Left(),values) == evaluate_formula(f.Right(),values)

evaluate_formula(Iff(parse_infix("s"),parse_infix("s")),{parse_infix("s"):True,parse_infix("q"):False})

def formula_free_variables(f):
    if not isinstance(f,Formula):
        raise TypeError("Bad arguments")
    if isinstance(f,Lie) or isinstance(f,Truth):
        return []
    if isinstance(f,Atom):
        return [f]
    else:
        ans = []
        for i in f.Interior:
            ans += formula_free_variables(i)
        return list(set(ans))

def free_variables_LP(f):
    if not isinstance(f,LittleProblem):
        raise TypeError("Bad arguments")
    ans = formula_free_variables(f.conclusion)
    for i in f.assumptions.base_context:
        ans += formula_free_variables(i)
    for i in f.assumptions.additional_context:
        ans += formula_free_variables(i)
    return list(set(ans))
#free_variables_LP(parsedProof[25].LP)

def all_possibilities(l):
    if len(l) == 0:
        return [dict()]
    else:
        ans = []
        old_dicts = all_possibilities(l[1:])
        for i in old_dicts:
            x1 = i.copy()
            x1[l[0]] = True
            x2 = i.copy()
            x2[l[0]] = False
            ans += [x1,x2]
        return ans
all_possibilities(formula_free_variables(parse_infix("p ∨ q ∨ r ∨ w ∨ z ∨ x ∨ c")))

def is_LP_tautology(LP):
    possibilities = all_possibilities(free_variables_LP(LP))
    assumptions = LP.assumptions.base_context + LP.assumptions.additional_context
    for i in possibilities:
        interesting = True
        for j in assumptions:
            if not evaluate_formula(j,i):
                interesting = False
                break
        if interesting:
            if not evaluate_formula(LP.conclusion,i):
                return False

    return True

def is_tautology(f):
    return is_LP_tautology(LittleProblem(Context([],[]),f))

print(is_LP_tautology(LittleProblem(
    Context([],[]),
parse_infix("p"))))
#%% md

#%% md
# GENEROWANIE KORPUSU PROSTE- PRZYGOTOWANIE
#%%
formulas_str = '''((p → q) ∧ p) → q
((p → q) ∧ ¬q) → ¬p
((p ∨ q) → r) → (p → r)
((p ∨ q) → r) → (q → r)
(p ∧ q) → p
q → (p ∨ q)
p → (q → p)
(¬p → q) → (p ∨ q)
((p → r) ∧ (q → r) ∧ (p ∨ q)) → r
((p ∧ q) → r) → (p → (q → r))
((p → (q → r)) → ((p ∧ q) → r))
((p → ¬p) → ¬p)
¬(p ∧ ¬p)
(p ∨ ¬p)
((p → q) ∧ (q → r)) → (p → r)
(((p → q) → p) → p)
((¬p → p) → p)
p ↔ p
(p ∨ q ∨ r) → (¬p → ((q ∨ r) ∧ ¬p))
(p → q) ↔ ((p ∧ q) → p)
((p ∨ q) → r) → ((p → r) ∨ (q → r))
((p → q) ∧ (r → s)) → (p ∧ r → q ∨ r)
(p ∨ q ∨ r) → (((p ∨ q) ∧ ¬r) ∨ ((r ∧ p) ∧ q))
(((p ∨ q) ∧ ¬r) ∨ ((r ∧ p) ∧ q)) → (p ∨ q ∨ r)
((p ∨ q) ↔ (r ∨ s)) → (((p ↔ r) ∨ (q ↔ s)))
((p ↔ r) ∨ (q ↔ s)) → ((p ∨ q) ↔ (r ∨ s))
((p ∧ q) ∧ (r ∧ s)) → (((p ↔ r) ∧ (q ↔ s)))
((p → q) → r) → (((p → q) → (p → r)))
((p ∨ q) ∧ ¬p) → q
((p → q) → (p ∧ r → q))
((p → q) → (p → (q ∨ r)))
(p → q) → (p ∨ q)
((p ∨ q) ∧ ((p → q) → q)) → p
¬(p ∧ (¬p ∧ q))
(p → ¬q) ∧ (q → r)
((p → q) ∧ (q → p)) → (p ∨ q)
((p ∨ q) → (p ∨ ¬q)) → (p ∨ q)
((p → q) ∨ (p → ¬q)) → (p → q)
((p → q) ∧ (q → r)) → (p → r)
((p → q) ∧ (r → s)) → ((p ∨ r) → (q ∨ s))
((p ∧ q) → r) → ((p → r) ∧ (q → r))
((p → q) ∧ (r → s)) → ((p ∧ r) → (q ∧ s))
((p ∧ q) ∧ (r ∨ s)) → (p ∧ q ∧ r)
((¬p → q) ∧ (q → p)) → (p ∧ ¬q)
(((p → q) → r) → ((r → p) → (q → p)))
(((p → q) ∨ (p → r)) ∨ ((p → s))) → (p → (q ∨ r ∨ s))
((p → q) ∧ (r → s)) → (p ∧ r → s ∧ q)
((p → q) ∧ (r → q) ∧ (s → q)) → (p ∧ r ∧ s → q)
((p ∧ q) ∧ (p ∧ q → r)) → (¬p ∧ ¬q → ¬r)
((¬p → q) ∨ (p ∨ ¬q)) → ((p → q) ∨ r)
(((p ∨ q) ∧ (r ∨ s)) → (((p → q) ∨ (p → r)) ∨ ((q → s) ∨ (q → p))))
(((p → q) ∧ (r → s) ∧ (t → u)) → (p ∧ r ∧ t → q ∧ s ∧ u))
((p ↔ q) ∧ p) → q
((¬p → ¬q) → (¬p → q)) → p'''
formulas_str = formulas_str.splitlines()
formulas = []
for i in formulas_str:
    f = parse_infix(i)
    if is_tautology(f):
        formulas.append(f)
    if is_tautology(Negation(f)):
        formulas.append(Negation(f))
print(formulas.__len__())


#%%
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
        f = random.choice([Negation,Conjunction,Disjunction,Implication,Iff])
        l = randomFormula(random.randint(1,depth)-1, variables,TruthLieIncluded)
        r = randomFormula(random.randint(1,depth)-1, variables,TruthLieIncluded)
        if f == Negation:
            return Negation(l)
        else:
            return f(l,r)
print(randomFormula(2,["a","b"]))

def SubstitutionSimple(t,x,Expr):
    if isinstance(Expr,Atom) or isinstance(Expr,Truth) or isinstance(Expr,Lie):
        if Expr == parse_infix(x):
             return t
        else:
            return Expr
    l = SubstitutionSimple(t,x,Expr.Left())
    if isinstance(Expr,Negation):
        return Negation(l)
    r = SubstitutionSimple(t,x,Expr.Right())
    if isinstance(Expr,Conjunction):
        return Conjunction(l,r)
    if isinstance(Expr,Disjunction):
        return Disjunction(l,r)
    if isinstance(Expr,Implication):
        return Implication(l,r)
    if isinstance(Expr,Iff):
        return Iff(l,r)
t = randomFormula(0,["a","b"])
print(to_infix(formulas[0]))
print(to_infix(SubstitutionSimple(t,"p",formulas[0])))
def randomTautology(depth, variables):
    global formulas
    i = random.choice([0,1])
    if i == 0:
        ans = Disjunction(randomFormula(depth,variables),randomFormula(depth, variables))
        while not is_tautology(ans):
            ans = Disjunction(randomFormula(depth,variables),ans)
        return ans
    else:
        t = randomFormula(depth,variables)
        Expr = random.choice(formulas)
        while formula_free_variables(Expr) == []:
            Expr = random.choice(formulas)
        x = (random.choice(formula_free_variables(Expr))).Arguments[0].name
        ans = SubstitutionSimple(t,x,Expr)
        return ans
print(to_infix(randomTautology(10000,["a","b","c","d","e","f","g","h","i","j","k","l"])))
#%%
parseProof("""1. p    assumption
            2. q    contextWeak, 1""")
#%% md
# DOWODY BAZOWE
#%%
proofs = [
    ("((p → q) ∧ p) → q",
"""1. (p → q) ∧ p  assumption
2. p → q  ∧-elimination1, 1
3. p  ∧-elimination2, 1
4. q  →-elimination, 2, 3
5. ((p → q) ∧ p) → q  →-introduction, 1, 4"""),

    ("((p → q) ∧ ¬q) → ¬p",
"""1. (p → q) ∧ ¬q  assumption
2. p → q  ∧-elimination1, 1
3. ¬q  ∧-elimination2, 1
4. p  assumption
5. q  →-elimination, 2, 4
6. ⊥  ¬-elimination, 3, 5
7. ¬p  ¬-introduction, 4, 6
8. ((p → q) ∧ ¬q) → ¬p  →-introduction, 1, 7"""),

    ("((p ∨ q) → r) → (p → r)",
"""1. (p ∨ q) → r  assumption
2. p  assumption
3. p ∨ q  ∨-introduction1, 2
4. r  →-elimination, 1, 3
5. p → r  →-introduction, 2, 4
6. ((p ∨ q) → r) → (p → r)  →-introduction, 1, 5"""),

    ("((p ∨ q) → r) → (q → r)",
"""1. (p ∨ q) → r  assumption
2. q  assumption
3. p ∨ q  ∨-introduction2, 2
4. r  →-elimination, 1, 3
5. q → r  →-introduction, 2, 4
6. ((p ∨ q) → r) → (q → r)  →-introduction, 1, 5"""),

    ("(p ∧ q) → p",
"""1. p ∧ q  assumption
2. p  ∧-elimination1, 1
3. (p ∧ q) → p  →-introduction, 1, 2"""),

    ("q → (p ∨ q)",
"""1. q  assumption
2. p ∨ q  ∨-introduction2, 1
3. q → (p ∨ q)  →-introduction, 1, 2"""),

    ("p → (q → p)",
"""1. p  assumption
2. q  assumption
3. p  weakening,   2, 1
4. p  context,   3
5. q → p  →-introduction,   2, 4
6. p → (q → p)  →-introduction,   1, 5"""),

    ("(¬p → q) → (p ∨ q)",
"""1. ¬p → q  assumption
2. p ∨ ¬p  TND
3. p  assumption
4. p ∨ q  ∨-introduction1, 3
5. ¬p  assumption
6. q  →-elimination, 1, 5
7. p ∨ q  ∨-introduction2, 6
8. p ∨ q  ∨-elimination, 2, 4, 7
9. (¬p → q) → (p ∨ q)  →-introduction, 1, 8"""),

    ("(((p → r) ∧ (q → r)) ∧ (p ∨ q)) → r",
"""1. ((p → r) ∧ (q → r)) ∧ (p ∨ q)  assumption
2. (p → r) ∧ (q → r)  ∧-elimination1, 1
3. p ∨ q  ∧-elimination2, 1
4. p → r  ∧-elimination1, 2
5. q → r  ∧-elimination2, 2
6. p  assumption
7. r  →-elimination, 4, 6
8. q  assumption
9. r  →-elimination, 5, 8
10. r  ∨-elimination, 3, 7, 9
11. (((p → r) ∧ (q → r)) ∧ (p ∨ q)) → r  →-introduction, 1, 10"""),

    ("((p ∧ q) → r) → (p → (q → r))",
"""1. (p ∧ q) → r  assumption
2. p  assumption
3. q  assumption
4. p ∧ q  ∧-introduction,   2, 3
5. r  →-elimination,   1, 4
6. q → r  →-introduction,   3, 5
7. p → (q → r)  →-introduction,   2, 6
8. ((p ∧ q) → r) → (p → (q → r))  →-introduction,   1, 7"""),

    ("(p → (q → r)) → ((p ∧ q) → r)",
"""1. p → (q → r)  assumption
2. p ∧ q  assumption
3. p  ∧-elimination1, 2
4. q  ∧-elimination2, 2
5. q → r  →-elimination, 1, 3
6. r  →-elimination, 5, 4
7. (p ∧ q) → r  →-introduction, 2, 6
8. (p → (q → r)) → ((p ∧ q) → r)  →-introduction, 1, 7"""),

    ("(p → ¬p) → ¬p",
"""1. p → ¬p  assumption
2. p  assumption
3. ¬p  →-elimination, 1, 2
4. ⊥  ¬-elimination, 3, 2
5. ¬p  ¬-introduction, 2, 4
6. (p → ¬p) → ¬p  →-introduction, 1, 5"""),

    ("¬(p ∧ ¬p)",
"""1. p ∧ ¬p  assumption
2. p  ∧-elimination1, 1
3. ¬p  ∧-elimination2, 1
4. ⊥  ¬-elimination, 3, 2
5. ¬(p ∧ ¬p)  ¬-introduction, 1, 4"""),

    ("p ∨ ¬p",
"""1. p ∨ ¬p  TND"""),

    ("((p → q) ∧ (q → r)) → (p → r)",
"""1. (p → q) ∧ (q → r)  assumption
2. p → q  ∧-elimination1, 1
3. q → r  ∧-elimination2, 1
4. p  assumption
5. q  →-elimination, 2, 4
6. r  →-elimination, 3, 5
7. p → r  →-introduction, 4, 6
8. ((p → q) ∧ (q → r)) → (p → r)  →-introduction, 1, 7"""),

    ("((p → q) → p) → p",
"""1. (p → q) → p  assumption
2. p ∨ ¬p  TND
3. p  assumption
4. p  context,   3
5. ¬p  assumption
6. p  assumption
7. ¬p  context,   5
8. ⊥  ¬-elimination,   7, 6
9. q  ⊥-elimination,   8
10. p → q  →-introduction,   6, 9
11. p  →-elimination,   1, 10
12. p  ∨-elimination,   2, 4, 11
13. ((p → q) → p) → p  →-introduction,   1, 12"""),

    ("(¬p → p) → p",
"""1. ¬p → p  assumption
2. p ∨ ¬p  TND
3. p  assumption
4. p  context,   3
5. ¬p  assumption
6. p  →-elimination,   1, 5
7. p  ∨-elimination,   2, 4, 6
8. (¬p → p) → p  →-introduction,   1, 7"""),

    ("p ↔ p",
"""1. p  assumption
2. p  context,   1
3. p  assumption
4. p  context,   3
5. p ↔ p  ↔-introduction,   2, 4"""),

    ("((p ∨ q) ∨ r) → (¬p → ((q ∨ r) ∧ ¬p))",
"""1. (p ∨ q) ∨ r  assumption
2. ¬p  assumption
3. p ∨ q  assumption
4. p  assumption
5. ¬p  context,   2
6. ⊥  ¬-elimination,   5, 4
7. q ∨ r  ⊥-elimination,   6
8. q  assumption
9. q ∨ r  ∨-introduction1,   8
10. q ∨ r  ∨-elimination,   3, 7, 9
11. r  assumption
12. q ∨ r  ∨-introduction2,   11
13. q ∨ r  ∨-elimination,   1, 10, 12
14. ¬p  context,   13
15. (q ∨ r) ∧ ¬p  ∧-introduction,   13, 14
16. ¬p → ((q ∨ r) ∧ ¬p)  →-introduction,   2, 15
17. ((p ∨ q) ∨ r) → (¬p → ((q ∨ r) ∧ ¬p))  →-introduction,   1, 16"""),

    ("((p ∨ q) → r) → ((p → r) ∨ (q → r))",
"""1. (p ∨ q) → r  assumption
2. p  assumption
3. p ∨ q  ∨-introduction1, 2
4. r  →-elimination, 1, 3
5. p → r  →-introduction, 2, 4
6. (p → r) ∨ (q → r)  ∨-introduction1, 5
7. ((p ∨ q) → r) → ((p → r) ∨ (q → r))  →-introduction, 1, 6"""),

    ("((p → q) ∧ (r → s)) → ((p ∧ r) → (q ∨ r))",
"""1. (p → q) ∧ (r → s)  assumption
2. p → q  ∧-elimination1, 1
3. p ∧ r  assumption
4. p  ∧-elimination1, 3
5. q  →-elimination, 2, 4
6. q ∨ r  ∨-introduction1, 5
7. (p ∧ r) → (q ∨ r)  →-introduction, 3, 6
8. ((p → q) ∧ (r → s)) → ((p ∧ r) → (q ∨ r))  →-introduction, 1, 7"""),

    ("(((p ∨ q) ∧ ¬r) ∨ ((r ∧ p) ∧ q)) → ((p ∨ q) ∨ r)",
"""1. ((p ∨ q) ∧ ¬r) ∨ ((r ∧ p) ∧ q)  assumption
2. (p ∨ q) ∧ ¬r  assumption
3. p ∨ q  ∧-elimination1, 2
4. (p ∨ q) ∨ r  ∨-introduction1, 3
5. ((r ∧ p) ∧ q)  assumption
6. r ∧ p  ∧-elimination1, 5
7. r  ∧-elimination1, 6
8. (p ∨ q) ∨ r  ∨-introduction2, 7
9. (p ∨ q) ∨ r  ∨-elimination, 1, 4, 8
10. (((p ∨ q) ∧ ¬r) ∨ ((r ∧ p) ∧ q)) → ((p ∨ q) ∨ r)  →-introduction, 1, 9"""),

    ("((p ∧ q) ∧ (r ∧ s)) → ((p ↔ r) ∧ (q ↔ s))",
"""1. (p ∧ q) ∧ (r ∧ s)  assumption
2. p ∧ q  ∧-elimination1,   1
3. r ∧ s  ∧-elimination2,   1
4. p  ∧-elimination1,   2
5. q  ∧-elimination2,   2
6. r  ∧-elimination1,   3
7. s  ∧-elimination2,   3
8. p  assumption
9. r  weakening,   8, 6
10. r  assumption
11. p  weakening,   10, 4
12. p ↔ r  ↔-introduction,   9, 11
13. p ∨ ¬p  TND
14. ¬p  assumption
15. p  weakening,   14, 4
16. ⊥  ¬-elimination,   14, 15
17. ⊥  weakening,   6, 16
18. p ↔ r  ⊥-elimination,   17
19. p ↔ r  ∨-elimination,   13, 12, 18
20. r ∨ ¬r  TND
21. ¬r  assumption
22. r  weakening,   21, 6
23. ⊥  ¬-elimination,   21, 22
24. p ↔ r  ⊥-elimination,   23
25. p ↔ r  ∨-elimination,   20, 19, 24
26. q  assumption
27. s  weakening,   26, 7
28. s  assumption
29. q  weakening,   28, 5
30. q ↔ s  ↔-introduction,   27, 29
31. q ∨ ¬q  TND
32. ¬q  assumption
33. q  weakening,   32, 5
34. ⊥  ¬-elimination,   32, 33
35. ⊥  weakening,   7, 34
36. q ↔ s  ⊥-elimination,   35
37. q ↔ s  ∨-elimination,   31, 30, 36
38. s ∨ ¬s  TND
39. ¬s  assumption
40. s  weakening,   39, 7
41. ⊥  ¬-elimination,   39, 40
42. q ↔ s  ⊥-elimination,   41
43. q ↔ s  ∨-elimination,   38, 37, 42
44. (p ↔ r) ∧ (q ↔ s)  ∧-introduction,   25, 43
45. ((p ∧ q) ∧ (r ∧ s)) → ((p ↔ r) ∧ (q ↔ s))  →-introduction,   1, 44"""),

    ("((p → q) → r) → ((p → q) → (p → r))",
"""1. (p → q) → r  assumption
2. p → q  assumption
3. r  →-elimination,   1, 2
4. p  assumption
5. r  weakening,   4, 3
6. p → r  →-introduction,   4, 5
7. (p → q) → (p → r)  →-introduction,   2, 6
8. ((p → q) → r) → ((p → q) → (p → r))  →-introduction,   1, 7"""),

    ("((p ∨ q) ∧ ¬p) → q",
"""1. (p ∨ q) ∧ ¬p  assumption
2. p ∨ q  ∧-elimination1,   1
3. ¬p  ∧-elimination2,   1
4. p  assumption
5. ⊥  ¬-elimination,   3, 4
6. q  ⊥-elimination,   5
7. q  assumption
8. q  ∨-elimination,   2, 6, 7
9. ((p ∨ q) ∧ ¬p) → q  →-introduction,   1, 8"""),

    ("(p → q) → ((p ∧ r) → q)",
"""1. p → q  assumption
2. p ∧ r  assumption
3. p  ∧-elimination1, 2
4. q  →-elimination, 1, 3
5. (p ∧ r) → q  →-introduction, 2, 4
6. (p → q) → ((p ∧ r) → q)  →-introduction, 1, 5"""),

    ("(p → q) → (p → (q ∨ r))",
"""1. p → q  assumption
2. p  assumption
3. q  →-elimination, 1, 2
4. q ∨ r  ∨-introduction1, 3
5. p → (q ∨ r)  →-introduction, 2, 4
6. (p → q) → (p → (q ∨ r))  →-introduction, 1, 5"""),

    ("¬(p ∧ (¬p ∧ q))",
"""1. p ∧ (¬p ∧ q)  assumption
2. p  ∧-elimination1, 1
3. ¬p ∧ q  ∧-elimination2, 1
4. ¬p  ∧-elimination1, 3
5. ⊥  ¬-elimination, 4, 2
6. ¬(p ∧ (¬p ∧ q))  ¬-introduction, 1, 5"""),

    ("((p → q) ∧ (q → r)) → (p → r)",
"""1. (p → q) ∧ (q → r)  assumption
2. p → q  ∧-elimination1, 1
3. q → r  ∧-elimination2, 1
4. p  assumption
5. q  →-elimination, 2, 4
6. r  →-elimination, 3, 5
7. p → r  →-introduction, 4, 6
8. ((p → q) ∧ (q → r)) → (p → r)  →-introduction, 1, 7"""),

    ("((p → q) ∧ (r → s)) → ((p ∨ r) → (q ∨ s))",
"""1. (p → q) ∧ (r → s)  assumption
2. p → q  ∧-elimination1, 1
3. r → s  ∧-elimination2, 1
4. p ∨ r  assumption
5. p  assumption
6. q  →-elimination, 2, 5
7. q ∨ s  ∨-introduction1, 6
8. r  assumption
9. s  →-elimination, 3, 8
10. q ∨ s  ∨-introduction2, 9
11. q ∨ s  ∨-elimination, 4, 7, 10
12. (p ∨ r) → (q ∨ s)  →-introduction, 4, 11
13. ((p → q) ∧ (r → s)) → ((p ∨ r) → (q ∨ s))  →-introduction, 1, 12"""),

    ("((p → q) ∧ (r → s)) → ((p ∧ r) → (q ∧ s))",
"""1. (p → q) ∧ (r → s)  assumption
2. p → q  ∧-elimination1, 1
3. r → s  ∧-elimination2, 1
4. p ∧ r  assumption
5. p  ∧-elimination1, 4
6. r  ∧-elimination2, 4
7. q  →-elimination, 2, 5
8. s  →-elimination, 3, 6
9. q ∧ s  ∧-introduction, 7, 8
10. (p ∧ r) → (q ∧ s)  →-introduction, 4, 9
11. ((p → q) ∧ (r → s)) → ((p ∧ r) → (q ∧ s))  →-introduction, 1, 10"""),

    ("((p → q) → r) → ((r → p) → (q → p))",
"""1. (p → q) → r  assumption
2. r → p  assumption
3. q  assumption
4. p ∨ ¬p  TND
5. p  assumption
6. p  context,   5
7. ¬p  assumption
8. p  assumption
9. q  weakening,   8, 3
10. q  weakening,   7, 9
11. p → q  →-introduction,   8, 10
12. r  →-elimination,   1, 11
13. p  →-elimination,   2, 12
14. p  ∨-elimination,   4, 6, 13
15. q → p  →-introduction,   3, 14
16. (r → p) → (q → p)  →-introduction,   2, 15
17. ((p → q) → r) → ((r → p) → (q → p))  →-introduction,   1, 16"""),

    ("(((p → q) ∨ (p → r)) ∨ (p → s)) → (p → ((q ∨ r) ∨ s))",
"""1. ((p → q) ∨ (p → r)) ∨ (p → s)  assumption
2. p  assumption
3. (p → q) ∨ (p → r)  assumption
4. p → q  assumption
5. q  →-elimination,    4, 2
6. q ∨ r  ∨-introduction1,    5
7. (q ∨ r) ∨ s  ∨-introduction1,    6
8. p → r  assumption
9. r  →-elimination,    8, 2
10. q ∨ r  ∨-introduction2,    9
11. (q ∨ r) ∨ s  ∨-introduction1,    10
12. (q ∨ r) ∨ s  ∨-elimination,    3, 7, 11
13. p → s  assumption
14. s  →-elimination,    13, 2
15. (q ∨ r) ∨ s  ∨-introduction2,    14
16. (q ∨ r) ∨ s  ∨-elimination,    1, 12, 15
17. p → ((q ∨ r) ∨ s)  →-introduction,    2, 16
18. (((p → q) ∨ (p → r)) ∨ (p → s)) → (p → ((q ∨ r) ∨ s))  →-introduction,    1, 17"""),

    ("((p → q) ∧ (r → s)) → ((p ∧ r) → (s ∧ q))",
"""1. (p → q) ∧ (r → s)  assumption
2. p → q  ∧-elimination1,    1
3. r → s  ∧-elimination2,    1
4. p ∧ r  assumption
5. p  ∧-elimination1,    4
6. r  ∧-elimination2,    4
7. q  →-elimination,    2, 5
8. s  →-elimination,    3, 6
9. s ∧ q  ∧-introduction,    8, 7
10. (p ∧ r) → (s ∧ q)  →-introduction,    4, 9
11. ((p → q) ∧ (r → s)) → ((p ∧ r) → (s ∧ q))  →-introduction,    1, 10"""),

    ("(((p → q) ∧ (r → q)) ∧ (s → q)) → (((p ∧ r) ∧ s) → q)",
"""1. ((p → q) ∧ (r → q)) ∧ (s → q)  assumption
2. s → q  ∧-elimination2,    1
3. (p ∧ r) ∧ s  assumption
4. s  ∧-elimination2,    3
5. q  →-elimination,    2, 4
6. ((p ∧ r) ∧ s) → q  →-introduction,    3, 5
7. (((p → q) ∧ (r → q)) ∧ (s → q)) → (((p ∧ r) ∧ s) → q)  →-introduction,    1, 6"""),

    ("((p ∧ q) ∧ ((p ∧ q) → r)) → ((¬p ∧ ¬q) → ¬r)",
"""1. (p ∧ q) ∧ ((p ∧ q) → r)  assumption
2. p ∧ q  ∧-elimination1,    1
3. ¬p ∧ ¬q  assumption
4. r  assumption
5. p  ∧-elimination1,    2
6. ¬p  ∧-elimination1,    3
7. ⊥  ¬-elimination,    6, 5
8. ⊥  weakening,   4, 7
9. ¬r  ¬-introduction,   4, 8
10. (¬p ∧ ¬q) → ¬r  →-introduction,   3, 9
11. ((p ∧ q) ∧ ((p ∧ q) → r)) → ((¬p ∧ ¬q) → ¬r)  →-introduction,   1, 10"""),

    ("((p ∨ q) ∧ (r ∨ s)) → (((p → q) ∨ (p → r)) ∨ ((q → s) ∨ (q → p)))",
"""1. (p ∨ q) ∧ (r ∨ s)  assumption
2. r ∨ s  ∧-elimination2,   1
3. r  assumption
4. p  assumption
5. r  weakening, 4, 3
6. p → r  →-introduction, 4, 5
7. (p → q) ∨ (p → r)  ∨-introduction2, 6
8. ((p → q) ∨ (p → r)) ∨ ((q → s) ∨ (q → p))  ∨-introduction1, 7
9. s  assumption
10. q  assumption
11. s  weakening, 10, 9
12. q → s  →-introduction, 10, 11
13. (q → s) ∨ (q → p)  ∨-introduction1, 12
14. ((p → q) ∨ (p → r)) ∨ ((q → s) ∨ (q → p))  ∨-introduction2, 13
15. ((p → q) ∨ (p → r)) ∨ ((q → s) ∨ (q → p))  ∨-elimination, 2, 8, 14
16. ((p ∨ q) ∧ (r ∨ s)) → (((p → q) ∨ (p → r)) ∨ ((q → s) ∨ (q → p)))  →-introduction, 1, 15"""),

    ("(((p → q) ∧ (r → s)) ∧ (t → u)) → (((p ∧ r) ∧ t) → ((q ∧ s) ∧ u))",
"""1. ((p → q) ∧ (r → s)) ∧ (t → u)  assumption
2. (p → q) ∧ (r → s)  ∧-elimination1, 1
3. t → u  ∧-elimination2, 1
4. p → q  ∧-elimination1, 2
5. r → s  ∧-elimination2, 2
6. (p ∧ r) ∧ t  assumption
7. p ∧ r  ∧-elimination1, 6
8. t  ∧-elimination2, 6
9. p  ∧-elimination1, 7
10. r  ∧-elimination2, 7
11. q  →-elimination, 4, 9
12. s  →-elimination, 5, 10
13. u  →-elimination, 3, 8
14. q ∧ s  ∧-introduction, 11, 12
15. (q ∧ s) ∧ u  ∧-introduction, 14, 13
16. ((p ∧ r) ∧ t) → ((q ∧ s) ∧ u)  →-introduction, 6, 15
17. (((p → q) ∧ (r → s)) ∧ (t → u)) → (((p ∧ r) ∧ t) → ((q ∧ s) ∧ u))  →-introduction, 1, 16"""),

    ("((p ↔ q) ∧ p) → q",
"""1. (p ↔ q) ∧ p    assumption
2. p ↔ q  ∧-elimination1, 1
3. p  ∧-elimination2, 1
4. q  ↔-elimination1, 2, 3
5. ((p ↔ q) ∧ p) → q  →-introduction, 1, 4"""),
]
proofs = [  #dodalem
    (formula, "\n".join(  #dodalem
        f"{m.group(1)}{m.group(2)}    {re.sub(r'\s*,\s*', ', ', m.group(3))}" if (m := re.match(r'^(\d+\.\s*)(.*?)\s{2,}(\S.*)$', line)) else line  #dodalem
        for line in proof.splitlines()  #dodalem
    ))  #dodalem
    for formula, proof in proofs  #dodalem
]  #dodalem

print(len(proofs) == len(formulas))
for i in range(len(proofs)):
    print(proofs[i][1])
    print()

#%%
def replace_full_numbers_not_after_letter(text, old, new):  #dodalem
    if not isinstance(text, str):  #dodalem
        raise TypeError("Bad arguments")  #dodalem
    if len(old) != len(new):  #dodalem
        raise ValueError("old and new must have the same length")  #dodalem
    old_s = [str(x) for x in old]  #dodalem
    new_s = [str(x) for x in new]  #dodalem
    if not all(x.isdigit() for x in old_s + new_s):  #dodalem
        raise ValueError("all values in old/new must be whole numbers")  #dodalem
    if len(set(old_s)) != len(old_s):  #dodalem
        raise ValueError("values in old must be unique")  #dodalem
    if len(old_s) == 0:  #dodalem
        return text  #dodalem
    mapping = {old_s[i]: new_s[i] for i in range(len(old_s))}  #dodalem
    alternatives = "|".join(sorted((re.escape(x) for x in old_s), key=len, reverse=True))  #dodalem
    pattern = rf'(?<!\d)(?<![^\W\d_])({alternatives})(?!\d)'  #dodalem
    return re.sub(pattern, lambda m: mapping[m.group(1)], text)  #dodalem

def replace_full_number_not_after_letter(text, old, new):  #dodalem
    return replace_full_numbers_not_after_letter(text, [old], [new])  #dodalem
print(proofs[0][1])
p = proofs[0][1]
print(replace_full_numbers_not_after_letter(p, [1, 2,3,4], [11, 12, 13, 14]))
#%%
BigProof = ""
for i in range(len(proofs)):
    new_lines_number = len(proofs[i][1].splitlines())
    old_lines_number = len(BigProof.splitlines())
    new_proof_part = proofs[i][1]
    old_ids = list(range(1, new_lines_number + 1))  #dodalem
    new_ids = list(range(old_lines_number + 1, old_lines_number + new_lines_number + 1))  #dodalem
    new_proof_part = replace_full_numbers_not_after_letter(new_proof_part, old_ids, new_ids)  #dodalem
    if BigProof != "":
        BigProof += "\n"
    BigProof += new_proof_part
def int_from_start(s: str):
    m = re.match(r'\d+', s)
    return int(m.group()) if m else None
from tqdm import tqdm
def is_well_numbered(proof:str):
    #print("^^^^^^^^^^^^^^^^^^",proof,"___________________________")
    for i in tqdm(range(len(proof.splitlines()))):
        if int_from_start(proof.splitlines()[i]) != i+1:
            raise Exception("Nieprawidlowe numerywanie wierszy")
    return True



BigProof += "\n376. ¬¬p    assumption"
BigProof += "\n377. ¬¬¬p    assumption"
BigProof += "\n378. ⊥    ¬-elimination, 377, 376"

print(is_well_numbered(BigProof))

#%%

#%% md
# GENEROWANIE KORPUSU BEZ ZAŁOŻEŃ
#%%
class idxs_set_bundle_without_assumptions:
    def __init__(self,proof_text):
        parsedProof = parseProof(proof_text)
        self.idxs_by_conclusion_type = dict()
        self.idxs_by_conclusion = dict()
        self.idxs_by_assumption = dict()
        self.idxs_by_conclusion_type["Truth"] = set()
        self.idxs_by_conclusion_type["Lie"] = set()
        self.idxs_by_conclusion_type["Atom"] = set()
        self.idxs_by_conclusion_type["Negation"] = set()
        self.idxs_by_conclusion_type["Disjunction"] = set()
        self.idxs_by_conclusion_type["Conjunction"] = set()
        self.idxs_by_conclusion_type["Implication"] = set()
        self.idxs_by_conclusion_type["Iff"] = set()
        self.idxs_by_conclusion_type["DoubleNegation"] = set()
        self.RAA_candidates = set()
        for i in parsedProof.keys():
            LPtemp =  parsedProof[i].LP
            if isinstance(LPtemp.conclusion, Lie):
                self.idxs_by_conclusion_type["Lie"].add(i)
                for j in LPtemp.assumptions.additional_context:
                    if isinstance(j, Negation):
                        self.RAA_candidates.add(i)
            if isinstance(LPtemp.conclusion, Truth):
                self.idxs_by_conclusion_type["Truth"].add(i)
            if isinstance(LPtemp.conclusion, Atom):
                self.idxs_by_conclusion_type["Atom"].add(i)
            if isinstance(LPtemp.conclusion, Negation):
                self.idxs_by_conclusion_type["Negation"].add(i)
                if isinstance(LPtemp.conclusion.Interior[0], Negation):
                    self.idxs_by_conclusion_type["DoubleNegation"].add(i)
            if isinstance(LPtemp.conclusion, Disjunction):
                self.idxs_by_conclusion_type["Disjunction"].add(i)
            if isinstance(LPtemp.conclusion, Conjunction):
                self.idxs_by_conclusion_type["Conjunction"].add(i)
            if isinstance(LPtemp.conclusion, Implication):
                self.idxs_by_conclusion_type["Implication"].add(i)
            if isinstance(LPtemp.conclusion, Iff):
                self.idxs_by_conclusion_type["Iff"].add(i)
            if not to_infix(LPtemp.conclusion) in self.idxs_by_conclusion.keys():
                self.idxs_by_conclusion[to_infix(LPtemp.conclusion)] = {i}
            else:
                self.idxs_by_conclusion[to_infix(LPtemp.conclusion)].add(i)

            for j in LPtemp.assumptions:
                if not to_infix(j) in self.idxs_by_assumption.keys():
                    self.idxs_by_assumption[to_infix(j)] = {i}
                else:
                    self.idxs_by_assumption[to_infix(j)].add(i)


    def add_line(self,line: structure_of_line_top_down):
        if isinstance(line.LP.conclusion, Lie):
            self.idxs_by_conclusion_type["Lie"].add(line.Key)
            for j in line.LP.assumptions.additional_context:
                if isinstance(j, Negation):
                    self.RAA_candidates.add(line.Key)
        if isinstance(line.LP.conclusion, Truth):
            self.idxs_by_conclusion_type["Truth"].add(line.Key)
        if isinstance(line.LP.conclusion, Atom):
            self.idxs_by_conclusion_type["Atom"].add(line.Key)
        if isinstance(line.LP.conclusion, Negation):
            self.idxs_by_conclusion_type["Negation"].add(line.Key)
            if isinstance(line.LP.conclusion.Interior[0], Negation):
                self.idxs_by_conclusion_type["DoubleNegation"].add(line.Key)
        if isinstance(line.LP.conclusion, Disjunction):
            self.idxs_by_conclusion_type["Disjunction"].add(line.Key)
        if isinstance(line.LP.conclusion, Conjunction):
            self.idxs_by_conclusion_type["Conjunction"].add(line.Key)
        if isinstance(line.LP.conclusion, Implication):
            self.idxs_by_conclusion_type["Implication"].add(line.Key)
        if isinstance(line.LP.conclusion, Iff):
            self.idxs_by_conclusion_type["Iff"].add(line.Key)

        if not to_infix(line.LP.conclusion) in self.idxs_by_conclusion.keys():
            self.idxs_by_conclusion[to_infix(line.LP.conclusion)] = {line.Key}
        else:
            self.idxs_by_conclusion[to_infix(line.LP.conclusion)].add(line.Key)

        for j in line.LP.assumptions:
            if not to_infix(j) in self.idxs_by_assumption.keys():
                self.idxs_by_assumption[to_infix(j)] = {line.Key}
            else:
                self.idxs_by_assumption[to_infix(j)].add(line.Key)






#%%
class idxs_list_bundle_without_assumptions:
    def __init__(self,proof_text):
        parsedProof = parseProof(proof_text)
        self.idxs_by_conclusion_type = dict()
        self.idxs_by_conclusion = dict()
        self.idxs_by_assumption = dict()
        self.idxs_by_conclusion_type["Truth"] = []
        self.idxs_by_conclusion_type["Lie"] = []
        self.idxs_by_conclusion_type["Atom"] = []
        self.idxs_by_conclusion_type["Negation"] = []
        self.idxs_by_conclusion_type["Disjunction"] = []
        self.idxs_by_conclusion_type["Conjunction"] = []
        self.idxs_by_conclusion_type["Implication"] = []
        self.idxs_by_conclusion_type["Iff"] = []
        self.idxs_by_conclusion_type["DoubleNegation"] = []
        self.RAA_candidates = []
        for i in parsedProof.keys():
            LPtemp =  parsedProof[i].LP
            if isinstance(LPtemp.conclusion, Lie):
                self.idxs_by_conclusion_type["Lie"].append(i)
                for j in LPtemp.assumptions.additional_context:
                    if isinstance(j, Negation):
                        self.RAA_candidates.append(i)
            if isinstance(LPtemp.conclusion, Truth):
                self.idxs_by_conclusion_type["Truth"].append(i)
            if isinstance(LPtemp.conclusion, Atom):
                self.idxs_by_conclusion_type["Atom"].append(i)
            if isinstance(LPtemp.conclusion, Negation):
                self.idxs_by_conclusion_type["Negation"].append(i)
                if isinstance(LPtemp.conclusion.Interior[0], Negation):
                    self.idxs_by_conclusion_type["DoubleNegation"].append(i)
            if isinstance(LPtemp.conclusion, Disjunction):
                self.idxs_by_conclusion_type["Disjunction"].append(i)
            if isinstance(LPtemp.conclusion, Conjunction):
                self.idxs_by_conclusion_type["Conjunction"].append(i)
            if isinstance(LPtemp.conclusion, Implication):
                self.idxs_by_conclusion_type["Implication"].append(i)
            if isinstance(LPtemp.conclusion, Iff):
                self.idxs_by_conclusion_type["Iff"].append(i)
            if not to_infix(LPtemp.conclusion) in self.idxs_by_conclusion.keys():
                self.idxs_by_conclusion[to_infix(LPtemp.conclusion)] = [i]
            else:
                self.idxs_by_conclusion[to_infix(LPtemp.conclusion)].append(i)

            for j in LPtemp.assumptions:
                if not to_infix(j) in self.idxs_by_assumption.keys():
                    self.idxs_by_assumption[to_infix(j)] = [i]
                else:
                    self.idxs_by_assumption[to_infix(j)].append(i)


    def add_line(self,line: structure_of_line_top_down):
        if isinstance(line.LP.conclusion, Lie):
            self.idxs_by_conclusion_type["Lie"].append(line.Key)
            for j in line.LP.assumptions.additional_context:
                if isinstance(j, Negation):
                    self.RAA_candidates.append(line.Key)
        if isinstance(line.LP.conclusion, Truth):
            self.idxs_by_conclusion_type["Truth"].append(line.Key)
        if isinstance(line.LP.conclusion, Atom):
            self.idxs_by_conclusion_type["Atom"].append(line.Key)
        if isinstance(line.LP.conclusion, Negation):
            self.idxs_by_conclusion_type["Negation"].append(line.Key)
            if isinstance(line.LP.conclusion.Interior[0], Negation):
                self.idxs_by_conclusion_type["DoubleNegation"].append(line.Key)
        if isinstance(line.LP.conclusion, Disjunction):
            self.idxs_by_conclusion_type["Disjunction"].append(line.Key)
        if isinstance(line.LP.conclusion, Conjunction):
            self.idxs_by_conclusion_type["Conjunction"].append(line.Key)
        if isinstance(line.LP.conclusion, Implication):
            self.idxs_by_conclusion_type["Implication"].append(line.Key)
        if isinstance(line.LP.conclusion, Iff):
            self.idxs_by_conclusion_type["Iff"].append(line.Key)

        if not to_infix(line.LP.conclusion) in self.idxs_by_conclusion.keys():
            self.idxs_by_conclusion[to_infix(line.LP.conclusion)] = [line.Key]
        else:
            self.idxs_by_conclusion[to_infix(line.LP.conclusion)].append(line.Key)
        for j in line.LP.assumptions:
            if not to_infix(j) in self.idxs_by_assumption.keys():
                self.idxs_by_assumption[to_infix(j)] = [line.Key]
            else:
                self.idxs_by_assumption[to_infix(j)].append(line.Key)

#%%
class idxs_bundle_without_assumptions:
    def __init__(self,proof_text):
        self.SBundle = idxs_set_bundle_without_assumptions(proof_text)
        self.LBundle = idxs_list_bundle_without_assumptions(proof_text)
    def add_line(self,line: structure_of_line_top_down):
        self.SBundle.add_line(line)
        self.LBundle.add_line(line)

idxs_boundle = idxs_bundle_without_assumptions(BigProof)
print(idxs_boundle.LBundle.idxs_by_conclusion_type["DoubleNegation"])
for i in idxs_boundle.LBundle.idxs_by_assumption.keys():
    print(i)
print(idxs_boundle.LBundle.idxs_by_assumption[to_infix(parse_infix("p"))])
print(BigProof)
print(idxs_boundle.LBundle.idxs_by_conclusion_type["DoubleNegation"])

#%%
from tqdm import tqdm
def generate_long_proofv1(proof,
                          how_many_new_lines = 1,
                          variables = list("qwertyuiopasdfghjklzxcvbnm"),
                          depth = 20
                          ):
    rules = [Assumption(),
             Weakening(),
             ImplicationIntroduction(),
             NegationIntroduction(),
             ImplicationElimination(),
             NegationElimination(),
             ConjunctionIntroduction(),
             DisjunctionIntroduction1(),
             DisjunctionIntroduction2(),
             TruthIntroduction(),
             ConjunctionElimination1(),
             ConjunctionElimination2(),
             DisjunctionElimination(),
             LieElimination(),
             IffIntroduction(),
             IffElimination1(),
             IffElimination2(),
             RAA(),
             NegationOfNegation(),
             TND(),
             FromContext(),
             FromWeakenContext()]
    rule = random.choice(rules)
    Proof_so_far = parseProof(proof)
    idxs_boundle = idxs_bundle_without_assumptions(proof)
    Key = len(Proof_so_far)

    for I in tqdm(range(how_many_new_lines)):
        Key += 1
        rule = random.choice(rules)
        match rule:
            case Assumption():
                args_keys = []
                formula_text = to_infix(randomFormula(depth,variables,TruthLieIncluded=True))
            case Weakening():
                args_keys = [random.randint(1,len(Proof_so_far)),
                             random.randint(1,len(Proof_so_far))]
                LP = Proof_so_far[args_keys[1]].LP
                phi = LP.conclusion
                formula_text = to_infix(phi)
            case ImplicationIntroduction():
                args_keys = [None,None]
                while args_keys[1] == None:
                    candidate = random.randint(1,len(Proof_so_far))
                    if not Proof_so_far[candidate].LP.assumptions.additional_context == []:
                        args_keys[1] = candidate
                phi = Proof_so_far[args_keys[1]].LP.conclusion
                psi = random.choice(Proof_so_far[args_keys[1]].LP.assumptions.additional_context)
                args_keys[0] = random.choice(idxs_boundle.LBundle.idxs_by_conclusion[to_infix(psi)])
                formula_text = to_infix(Implication(phi,psi))
            case NegationIntroduction():
                args_keys = [None,None]
                while args_keys[0] == None or args_keys[1] == None:
                    args_keys[1] = random.choice(idxs_boundle.LBundle.idxs_by_conclusion_type["Lie"])
                    phi = random.choice(Proof_so_far[args_keys[1]].LP.assumptions.additional_context)
                    args_keys[0] = random.choice(idxs_boundle.LBundle.idxs_by_conclusion[to_infix(phi)])
                formula_text = to_infix(Negation(phi))
            case ImplicationElimination():
                args_keys = [None,None]
                while args_keys[0] == None or args_keys[1] == None:
                    args_keys[0] = random.choice(idxs_boundle.LBundle.idxs_by_conclusion_type["Implication"])
                    phi = Proof_so_far[args_keys[0]].LP.conclusion.Interior[0]
                    if to_infix(phi) in idxs_boundle.LBundle.idxs_by_conclusion.keys():
                        args_keys[1] = random.choice(idxs_boundle.LBundle.idxs_by_conclusion[to_infix(phi)])
                formula_text = to_infix(Proof_so_far[args_keys[0]].LP.conclusion)
            case NegationElimination():
                args_keys = [None,None]
                while args_keys[0] == None or args_keys[1] == None:
                    args_keys[0] = random.choice(idxs_boundle.LBundle.idxs_by_conclusion_type["Negation"])
                    phi = Proof_so_far[args_keys[0]].LP.conclusion.Interior[0]
                    if to_infix(phi) in idxs_boundle.LBundle.idxs_by_conclusion.keys():
                        args_keys[1] = random.choice(idxs_boundle.LBundle.idxs_by_conclusion[to_infix(phi)])
                formula_text = to_infix(Lie())
            case ConjunctionIntroduction():
                args_keys = [random.randint(1,len(Proof_so_far)),
                             random.randint(1,len(Proof_so_far))]
                phi = Proof_so_far[args_keys[0]].LP.conclusion
                psi = Proof_so_far[args_keys[1]].LP.conclusion
                formula_text = to_infix(Conjunction(phi,psi))
            case DisjunctionIntroduction1():
                args_keys = [random.randint(1,len(Proof_so_far))]
                phi = Proof_so_far[args_keys[0]].LP.conclusion
                psi = randomFormula(depth,variables,TruthLieIncluded=True)
                formula_text = to_infix(Disjunction(phi,psi))
            case DisjunctionIntroduction2():
                args_keys = [random.randint(1,len(Proof_so_far))]
                psi = Proof_so_far[args_keys[0]].LP.conclusion
                phi = randomFormula(depth,variables,TruthLieIncluded=True)
                formula_text = to_infix(Disjunction(phi,psi))
            case TruthIntroduction():
                args_keys = []
                formula_text = to_infix(Truth())
            case ConjunctionElimination1():
                args_keys = [random.choice(idxs_boundle.LBundle.idxs_by_conclusion_type["Conjunction"])]
                phi = Proof_so_far[args_keys[0]].LP.conclusion.Interior[0]
                formula_text = to_infix(phi)
            case ConjunctionElimination2():
                args_keys = [random.choice(idxs_boundle.LBundle.idxs_by_conclusion_type["Conjunction"])]
                psi = Proof_so_far[args_keys[0]].LP.conclusion.Interior[1]
                formula_text = to_infix(psi)
            case DisjunctionElimination():
                args_keys = [None,None,None]
                while args_keys[0] == None or args_keys[1] == None or args_keys[2] == None:
                    args_keys[0] = random.choice(idxs_boundle.LBundle.idxs_by_conclusion_type["Disjunction"])
                    phi_text = to_infix(Proof_so_far[args_keys[0]].LP.conclusion.Interior[0])
                    psi_text = to_infix(Proof_so_far[args_keys[0]].LP.conclusion.Interior[1])
                    rho_candidates1 = set()
                    rho_candidates2 = set()
                    if phi_text in idxs_boundle.LBundle.idxs_by_assumption.keys():
                        for j in idxs_boundle.LBundle.idxs_by_assumption[phi_text]:
                            rho_candidates1.add(Proof_so_far[j].LP.conclusion)

                    if psi_text in idxs_boundle.LBundle.idxs_by_assumption.keys():
                        for j in idxs_boundle.LBundle.idxs_by_assumption[psi_text]:
                            rho_candidates2.add(Proof_so_far[j].LP.conclusion)

                    if rho_candidates1 & rho_candidates2 != set():
                        rho = random.choice(list(rho_candidates1 & rho_candidates2))
                        args_keys[1] = random.choice(list(
                            idxs_boundle.SBundle.idxs_by_conclusion[to_infix(rho)] &
                            idxs_boundle.SBundle.idxs_by_assumption[phi_text] ))
                        args_keys[2] = random.choice(list(
                            idxs_boundle.SBundle.idxs_by_conclusion[to_infix(rho)] &
                            idxs_boundle.SBundle.idxs_by_assumption[psi_text] ))
                formula_text = to_infix(rho)



            case LieElimination():
                args_keys = [random.choice(idxs_boundle.LBundle.idxs_by_conclusion_type["Lie"])]
                phi = randomFormula(depth,variables,TruthLieIncluded=True)
                formula_text = to_infix(phi)


            case IffIntroduction():
                args_keys = [None,None]
                while args_keys[0] == None or args_keys[1] == None:
                    args_keys[0] = random.randint(1,len(Proof_so_far))
                    psi = Proof_so_far[args_keys[0]].LP.conclusion
                    phi_candidates = Proof_so_far[args_keys[0]].LP.assumptions.additional_context.copy()
                    while phi_candidates != []:
                        phi = random.choice(phi_candidates)
                        phi_candidates.remove(phi)
                        if to_infix(phi) in idxs_boundle.SBundle.idxs_by_conclusion.keys() and to_infix(psi) in idxs_boundle.SBundle.idxs_by_assumption.keys():
                            if idxs_boundle.SBundle.idxs_by_conclusion[to_infix(phi)] & idxs_boundle.SBundle.idxs_by_assumption[to_infix(psi)] != set():
                                args_keys[1] = random.choice(list(idxs_boundle.SBundle.idxs_by_conclusion[to_infix(phi)] & idxs_boundle.SBundle.idxs_by_assumption[to_infix(psi)]))
                                break
                formula_text = to_infix(Iff(phi,psi))

            case IffElimination1():
                args_keys = [None,None]
                while args_keys[0] == None or args_keys[1] == None:
                    args_keys[0] = random.choice(idxs_boundle.LBundle.idxs_by_conclusion_type["Iff"])
                    phi = Proof_so_far[args_keys[0]].LP.conclusion.Interior[0]
                    psi = Proof_so_far[args_keys[0]].LP.conclusion.Interior[1]
                    if to_infix(phi) in idxs_boundle.LBundle.idxs_by_conclusion.keys():
                        args_keys[1] = random.choice(idxs_boundle.LBundle.idxs_by_conclusion[to_infix(phi)])
                formula_text = to_infix(psi)
            case IffElimination2():
                args_keys = [None,None]
                while args_keys[0] == None or args_keys[1] == None:
                    args_keys[0] = random.choice(idxs_boundle.LBundle.idxs_by_conclusion_type["Iff"])
                    phi = Proof_so_far[args_keys[0]].LP.conclusion.Interior[0]
                    psi = Proof_so_far[args_keys[0]].LP.conclusion.Interior[1]
                    if to_infix(psi) in idxs_boundle.LBundle.idxs_by_conclusion.keys():
                        args_keys[1] = random.choice(idxs_boundle.LBundle.idxs_by_conclusion[to_infix(psi)])
                formula_text = to_infix(phi)
            case RAA():
                args_keys = [None,None]
                while args_keys[0] == None or args_keys[1] == None:
                    args_keys[1] = random.choice(idxs_boundle.LBundle.RAA_candidates)
                    neg_phi_candidates = []
                    for j in Proof_so_far[args_keys[1]].LP.assumptions.additional_context:
                        if isinstance(j,Negation):
                            if to_infix(j) in idxs_boundle.LBundle.idxs_by_conclusion.keys():
                                neg_phi_candidates.append(j)
                    if neg_phi_candidates != []:
                        neg_phi = random.choice(neg_phi_candidates)
                        phi = neg_phi.Interior[0]
                        args_keys[0] = random.choice(idxs_boundle.LBundle.idxs_by_conclusion[to_infix(neg_phi)])
                formula_text = to_infix(phi)
            case NegationOfNegation():
                random.choice(idxs_boundle.LBundle.idxs_by_conclusion_type["DoubleNegation"])
                args_keys = [random.choice(idxs_boundle.LBundle.idxs_by_conclusion_type["DoubleNegation"])]
                LP = Proof_so_far[args_keys[0]].LP
                phi = LP.conclusion.Interior[0].Interior[0]
                formula_text = to_infix(phi)
            case TND():
                args_keys = []
                phi = randomFormula(depth,variables,TruthLieIncluded=True)
                formula_text = to_infix(Disjunction(phi,Negation(phi)))
            case FromContext():
                args_keys = []
                while True:
                    args_keys = [random.randint(1,len(Proof_so_far))]
                    if Proof_so_far[args_keys[0]].LP.assumptions.additional_context != []:
                        break
                phi = random.choice(Proof_so_far[args_keys[0]].LP.assumptions.additional_context)
                formula_text = to_infix(phi)
            case FromWeakenContext():
                args_keys = [random.randint(1,len(Proof_so_far))]
                phi = randomFormula(depth,variables,TruthLieIncluded=True)
                formula_text = to_infix(phi)
            case _:
                raise TypeError("Bad rule")
        if Key == Proof_so_far.__len__()+1:
            new_line_structure = structure_of_line_top_down(Key,args_keys,rule,Proof_so_far,formula_text)
            idxs_boundle.add_line(new_line_structure)
            proof = proof + "\n"+ remade_proof_line_text(new_line_structure)
            Proof_so_far[Key] = new_line_structure

    return proof
print(parseProof(BigProof).__len__())
long_proof = BigProof

long_proof = generate_long_proofv1(long_proof,how_many_new_lines=100)
parsedProof = parseProof(long_proof)
number_of_tautologies = 0
for i in parsedProof:
    if parsedProof[i].rule not in [TruthIntroduction(),TND()]:
        if parsedProof[i].LP.assumptions.additional_context == []:
            number_of_tautologies += 1
#is_well_numbered(long_proof)
print(number_of_tautologies)
#%%
print(long_proof[-1])
if isinstance(long_proof, str):
    long_proof = long_proof.splitlines()
table = []
for i in parsedProof.keys():
    if parsedProof[i].rule not in [Assumption(),TruthIntroduction(),TND()]:
        table.append([i,parsedProof[i].LP.assumptions.additional_context.__len__()])
    else:
        print(long_proof[i].split()[-1])
print(table)
#%%
def FreeVariables(Expr):
    if not isinstance(Expr, Formula):
        raise TypeError("Bad arguments")
    if isinstance(Expr, Variable):
        return {Expr}
    if isinstance(Expr, Atom):
        return {Expr}
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

for i in table:
    if i[1] == 0:
        if FreeVariables(parsedProof[i[0]].LP.conclusion) != set():
            print(i,to_infix(parsedProof[i[0]].LP.conclusion))
#%%
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
for i in table:
    if i[1] == 0:
        if FreeVariables(parsedProof[i[0]].LP.conclusion) != set():
            if not contains_TF(parsedProof[i[0]].LP.conclusion):
                print(i,to_infix(parsedProof[i[0]].LP.conclusion))
#%%
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

proofs_table = []

for i in table:
    if i[1] == 0:
        if FreeVariables(parsedProof[i[0]].LP.conclusion) != set():
            if not contains_TF(parsedProof[i[0]].LP.conclusion):
                if not isinstance(parsedProof[i[0]].rule ,TND):
                    if not isinstance(parsedProof[i[0]].rule ,Assumption):
                        extracted_proof = extract_proof(long_proof,i[0])
                        if extracted_proof.splitlines().__len__() > 2:
                            next_proof = extract_proof(long_proof,i[0])
                            parsed_next_proof = parseProof(next_proof)
                            if parsed_next_proof[parsed_next_proof.__len__()].LP.assumptions.additional_context != []:
                                raise TypeError("Bad proof")
                            proofs_table.append(next_proof)

#%%
proofs_table = []
from concurrent.futures import ProcessPoolExecutor, as_completed
import multiprocessing as mp
from copy import deepcopy


def one_job(job_id, big_proof):
    local_proofs_table = []
    local_prints = []

    print(job_id)

    # dla bezpieczeństwa, żeby procesy nie grzebały w tym samym obiekcie
    long_proof = deepcopy(big_proof)
    long_proof = generate_long_proofv1(long_proof, how_many_new_lines=30000)

    parsedProof = parseProof(long_proof)

    if isinstance(long_proof, str):
        long_proof_lines = long_proof.splitlines()
    else:
        long_proof_lines = long_proof

    table = []
    for i in parsedProof.keys():
        if parsedProof[i].rule not in [Assumption(), TruthIntroduction(), TND()]:
            table.append((i, len(parsedProof[i].LP.assumptions.additional_context)))
        else:
            local_prints.append(long_proof_lines[i].split()[-1])

    for idx, add_ctx_len in table:
        if add_ctx_len == 0:
            conclusion = parsedProof[idx].LP.conclusion
            rule = parsedProof[idx].rule

            if FreeVariables(conclusion) != set():
                if not contains_TF(conclusion):
                    if not isinstance(rule, TND):
                        if not isinstance(rule, Assumption):
                            extracted_proof = extract_proof(long_proof_lines, idx)

                            if len(extracted_proof.splitlines()) > 2:
                                next_proof = extracted_proof

                                if len(extracted_proof) <= 1024:
                                    parsed_next_proof = parseProof(next_proof)

                                    if parsed_next_proof[len(parsed_next_proof)].LP.assumptions.additional_context != []:
                                        raise TypeError("Bad proof")

                                    local_proofs_table.append(next_proof)

    return job_id, local_proofs_table, local_prints


def run_parallel(big_proof, total_jobs=200, workers=20):
    proofs_table = []

    # na Linuksie zwykle najlepsze do takich rzeczy
    ctx = mp.get_context("fork")

    with ProcessPoolExecutor(max_workers=workers, mp_context=ctx) as executor:
        futures = [executor.submit(one_job, i, big_proof) for i in range(total_jobs)]

        for future in as_completed(futures):
            job_id, local_proofs, local_prints = future.result()

            for x in local_prints:
                print(x)

            proofs_table.extend(local_proofs)

    return proofs_table

#proofs_table = run_parallel(BigProof, total_jobs=300, workers=20)

#%%
import gc
import multiprocessing as mp
from copy import deepcopy
from concurrent.futures import ProcessPoolExecutor

_BIG_PROOF = None

def init_worker(big_proof):
    global _BIG_PROOF
    _BIG_PROOF = big_proof

def one_job(job_id):
    global _BIG_PROOF

    local_proofs_table = []
    local_prints = []

    print(job_id)

    long_proof = deepcopy(_BIG_PROOF)
    long_proof = generate_long_proofv1(long_proof, how_many_new_lines=30000)

    parsedProof = parseProof(long_proof)

    if isinstance(long_proof, str):
        long_proof_lines = long_proof.splitlines()
    else:
        long_proof_lines = long_proof

    table = []
    for i in parsedProof.keys():
        if parsedProof[i].rule not in [Assumption(), TruthIntroduction(), TND()]:
            table.append((i, len(parsedProof[i].LP.assumptions.additional_context)))
        else:
            local_prints.append(long_proof_lines[i].split()[-1])

    for idx, add_ctx_len in table:
        if add_ctx_len == 0:
            conclusion = parsedProof[idx].LP.conclusion
            rule = parsedProof[idx].rule

            if FreeVariables(conclusion) != set():
                if not contains_TF(conclusion):
                    if not isinstance(rule, TND):
                        if not isinstance(rule, Assumption):
                            extracted_proof = extract_proof(long_proof_lines, idx)

                            if len(extracted_proof.splitlines()) > 2:
                                if len(extracted_proof) <= 1024:
                                    parsed_next_proof = parseProof(extracted_proof)

                                    if parsed_next_proof[len(parsed_next_proof)].LP.assumptions.additional_context != []:
                                        raise TypeError("Bad proof")

                                    local_proofs_table.append(extracted_proof)

    del parsedProof, long_proof, long_proof_lines, table
    gc.collect()

    return job_id, local_proofs_table, local_prints


def run_parallel(big_proof, total_jobs=200, workers=20):
    proofs_table = []
    ctx = mp.get_context("fork")

    with ProcessPoolExecutor(
        max_workers=workers,
        mp_context=ctx,
        initializer=init_worker,
        initargs=(big_proof,),
    ) as executor:
        for job_id, local_proofs, local_prints in executor.map(one_job, range(total_jobs), chunksize=1):
            for x in local_prints:
                print(x)
            proofs_table.extend(local_proofs)

            del job_id, local_proofs, local_prints
            gc.collect()

    gc.collect()
    return proofs_table


#%%
'''
for i in range(100):
    proofs_table = run_parallel(BigProof, total_jobs=100, workers=20)
    with open("proofs_raw.txt", "a", encoding="utf-8") as f:
        print("--------------------------------------------------------------------------------------------------------------------------------\n--------------------------------------------------------------------------------------------------------------------------------\n--------------------------------------------------------------------------------------------------------------------------------\n--------------------------------------------------------------------------------------------------------------------------------\n--------------------------------------------------------------------------------------------------------------------------------\n--------------------------------------------------------------------------------------------------------------------------------\n--------------------------------------------------------------------------------------------------------------------------------\n--------------------------------------------------------------------------------------------------------------------------------\n--------------------------------------------------------------------------------------------------------------------------------\n--------------------------------------------------------------------------------------------------------------------------------\n--------------------------------------------------------------------------------------------------------------------------------\n--------------------------------------------------------------------------------------------------------------------------------\n--------------------------------------------------------------------------------------------------------------------------------\n--------------------------------------------------------------------------------------------------------------------------------\n--------------------------------------------------------------------------------------------------------------------------------\n--------------------------------------------------------------------------------------------------------------------------------\n--------------------------------------------------------------------------------------------------------------------------------\n--------------------------------------------------------------------------------------------------------------------------------\n--------------------------------------------------------------------------------------------------------------------------------\n--------------------------------------------------------------------------------------------------------------------------------\n--------------------------------------------------------------------------------------------------------------------------------\n--------------------------------------------------------------------------------------------------------------------------------\n--------------------------------------------------------------------------------------------------------------------------------\n--------------------------------------------------------------------------------------------------------------------------------\n--------------------------------------------------------------------------------------------------------------------------------\n")
        for j in proofs_table:
            f.write(j + "\n\n")
    proofs_table.clear()
    del proofs_table
    gc.collect()

'''
#%%
'''
for I in range(30):
    print(I)
    long_proof = BigProof
    long_proof = generate_long_proofv1(long_proof,how_many_new_lines=100000)
    parsedProof = parseProof(long_proof)
    if isinstance(long_proof, str):
        long_proof = long_proof.splitlines()
    table = []
    for i in parsedProof.keys():
        if parsedProof[i].rule not in [Assumption(),TruthIntroduction(),TND()]:
            table.append([i,parsedProof[i].LP.assumptions.additional_context.__len__()])
        else:
            print(long_proof[i].split()[-1])

    for i in table:
        if i[1] == 0:
            if FreeVariables(parsedProof[i[0]].LP.conclusion) != set():
                if not contains_TF(parsedProof[i[0]].LP.conclusion):
                    if not isinstance(parsedProof[i[0]].rule ,TND):
                        if not isinstance(parsedProof[i[0]].rule ,Assumption):
                            extracted_proof = extract_proof(long_proof,i[0])
                            if extracted_proof.splitlines().__len__() > 2:
                                next_proof = extract_proof(long_proof,i[0])
                                if extracted_proof.__len__() <= 1024:
                                    parsed_next_proof = parseProof(next_proof)
                                    if parsed_next_proof[parsed_next_proof.__len__()].LP.assumptions.additional_context != []:
                                        raise TypeError("Bad proof")
                                    proofs_table.append(next_proof)
'''
#%%
with open("proofs_raw.txt", "r") as f:
    text = f.read()
print(text.__len__())
#%%
proofs_table = text.split("\n\n")
print(proofs_table.__len__())
#%%
'''
with open("proofs_raw.txt", "a", encoding="utf-8") as f:
    for i in proofs_table:
        print(i)
        f.write(i + "\n\n")
'''
#%%
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

normalise(Iff(Truth(),parse_infix("x")))
#%%
for idx, proof_text in enumerate(proofs_table[:20]):
    try:
        print(proofs_table[idx])
        print()
        parseProof(proof_text)
    except Exception as e:
        print("Błąd w proofie:", idx)
        print("Cały proof:")
        print(repr(proof_text))
        print("Linie:")
        for k, line in enumerate(proof_text.splitlines()):
            print(k, repr(line))
        raise
#%%
proofs_table = list(filter(lambda a: a != "", proofs_table))
#%%
'''
proofs_simplified_dict = dict()
for i in tqdm(range(len(proofs_table))):
    dict_key = parseProof(proofs_table[i])
    l = len(dict_key)
    dict_key = dict_key[len(dict_key)]
    dict_key = normalise(dict_key.LP.conclusion)
    if dict_key in proofs_simplified_dict.keys():
        proofs_simplified_dict[dict_key].append([i,l])
    else:
        proofs_simplified_dict[dict_key]= [[i,l]]
'''


from concurrent.futures import ProcessPoolExecutor
from tqdm import tqdm
import os
def worker(args):
    i, proof_text = args
    global bad_proof
    parsed = parseProof(proof_text)
    l = parsed.__len__()
    dict_key = parsed[parsed.__len__()]
    dict_key = normalise(dict_key.LP.conclusion)
    return i, l, dict_key

proofs_simplified_dict = dict()
'''
with ProcessPoolExecutor(max_workers=os.cpu_count()) as executor:
    results = executor.map(worker, enumerate(proofs_table), chunksize=20)
    for i, l, dict_key in tqdm(results, total=len(proofs_table)):
        try:
            if dict_key in proofs_simplified_dict:
                proofs_simplified_dict[dict_key].append([i, l])
            else:
                proofs_simplified_dict[dict_key] = [[i, l]]
        except Exception as e:
            print(i, l, dict_key)
            raise e
'''
#%%
for i in proofs_simplified_dict:
    print(to_infix(i),proofs_simplified_dict[i])

#%%
important_idxs = []
for i in tqdm(proofs_simplified_dict,total = proofs_simplified_dict.__len__()):
    idxs = proofs_simplified_dict[i]
    important_idx = idxs[0]
    for j in idxs:
        if j[1] < important_idx[1]:
            important_idx = j
    important_idxs.append(important_idx)
#%%
'''
with open("proofs_normalised.txt", "w", encoding="utf-8") as f:
    for i in proofs_table:
        print(i)
        f.write(i + "\n\n")
'''
#%% md
# Modelowanie korpusu
#%%
'''
with open("proofs_normalised.txt", "r", encoding="utf-8") as f:
    text = f.read()

proofs_table  = text.strip().split("\n\n")

for i in tqdm(range(len(proofs_table))):
    print(proofs_table[i])
    parsed = parseProof(proofs_table[i])
'''
#%%
'''
proofs_simplified_dict = dict()
for i in tqdm(range(len(proofs_table))):
    dict_key = parseProof(proofs_table[i])
    l = dict_key.__len__()
    dict_key = dict_key[dict_key.__len__()]
    dict_key = normalise(dict_key.LP.conclusion)
    if dict_key in proofs_simplified_dict.keys():
        proofs_simplified_dict[dict_key].append([i,l])
    else:
        proofs_simplified_dict[dict_key]= [[i,l]]
'''
#%%
'''
important_idxs = []
for i in proofs_simplified_dict:
    idxs = proofs_simplified_dict[i]
    important_idx = idxs[0]
    for j in idxs:
        if j[1] < important_idx[1]:
            important_idx = j
    important_idxs.append(important_idx)
'''
#%%
'''
with open("proofs_normalised.txt", "w", encoding="utf-8") as f:
    for i in tqdm(important_idxs,tota:
        proof = proofs_table[i[0]]
        proof_parsed = parseProof(proof)
        thesis = proof_parsed[len(proof_parsed)].LP.conclusion
        f.write("Prove that: " + to_infix(thesis)+"\n")
        f.write(proofs_table[i[0]] + "\n\n")
'''
#%%

for i in tqdm(important_idxs,total = important_idxs.__len__()):
    proof = proofs_table[i[0]]
    proof_parsed = parseProof(proof)
    thesis = proof_parsed[len(proof_parsed)].LP.assumptions
    if not thesis == Context([],[]):
        print(1)

#%% md
# SMASHED PROBLEM TODO
#%%
def is_LP_tautology(LP):
    possibilities = all_possibilities(free_variables_LP(LP))
    assumptions = LP.assumptions.base_context + LP.assumptions.additional_context
    for i in possibilities:
        interesting = True
        for j in assumptions:
            if not evaluate_formula(j,i):
                interesting = False
                break
        if interesting:
            if not evaluate_formula(LP.conclusion,i):
                return False

    return True
class smashed_problem:
    def __init__(self,
                 problem:LittleProblem,
                 subproblems:list[LittleProblem],
                 rule:Rule):
        self.problem = problem
        self.subproblems = subproblems
        self.rule = rule
    def __str__(self):
        ans = to_infix_LP(self.problem) + " ["
        for i in self.subproblems:
            ans += to_infix_LP(i) + " . "
        if ans[-1] != '[':
            ans = ans[:-3]
        ans += "] "
        ans += str(self.rule)
        return ans

#%%
def smash_with_proof(line,proof_so_far):
    subproblems = []
    args_keys = []
    match line.rule:
        case Assumption():
            args_keys = []
        case Weakening():
            args_keys = [line.args_keys[1]]
        case ImplicationIntroduction():
            args_keys = [line.args_keys[1]]
        case NegationIntroduction():
            args_keys = [line.args_keys[1]]
        case ImplicationElimination():
            args_keys = [line.args_keys[0],line.args_keys[1]]
        case NegationElimination():
            args_keys = [line.args_keys[0],line.args_keys[1]]
        case ConjunctionIntroduction():
            args_keys = [line.args_keys[0],line.args_keys[1]]
        case DisjunctionIntroduction1():
            args_keys = [line.args_keys[0]]
        case DisjunctionIntroduction2():
            args_keys = [line.args_keys[0]]
        case TruthIntroduction():
            args_keys = []
        case ConjunctionElimination1():
            args_keys = [line.args_keys[0]]
        case ConjunctionElimination2():
            args_keys = [line.args_keys[0]]
        case DisjunctionElimination():
            args_keys = [line.args_keys[0],line.args_keys[1],line.args_keys[2]]
        case LieElimination():
            args_keys = [line.args_keys[0]]
        case IffIntroduction():
            args_keys = [line.args_keys[0],line.args_keys[1]]
        case IffElimination1():
            args_keys = [line.args_keys[0],line.args_keys[1]]
        case IffElimination2():
            args_keys = [line.args_keys[0],line.args_keys[1]]
        case RAA():
            args_keys = [line.args_keys[1]]
        case NegationOfNegation():
            args_keys = [line.args_keys[0]]
        case TND():
            args_keys = []
        case FromContext():
            args_keys = [line.args_keys[0]]
        case FromWeakenContext():
            args_keys = [line.args_keys[0]]
    for i in args_keys:
        if i != 0:
            subproblems.append(proof_so_far[i])
        else:
            base_context = proof_so_far[1].LP.assumptions.base_context
            context = Context(base_context,[])
            subproblems.append(LittleProblem(context,Truth()))

    for i in range(subproblems.__len__()):
        subproblems[i] = basing_context_of_LP(subproblems[i].LP)
    problem = line.LP
    rule = line.rule
    return smashed_problem(problem,subproblems,rule)

#%%
def is_smashed_correctly(SP):
    if not isinstance(SP,smashed_problem):
        raise TypeError("Bad arguments")
    if not isinstance(SP.problem,LittleProblem):
        raise TypeError("Bad arguments")
    if not isinstance(SP.subproblems,list):
        raise TypeError("Bad arguments")
    for i in SP.subproblems:
        if not isinstance(i,LittleProblem):
            raise TypeError("Bad arguments")
        if not i.assumptions.additional_context == []:
            raise TypeError("Bad arguments")
    if not isinstance(SP.rule,Rule):
        raise TypeError("Bad arguments")
    unnormalised_subproblems = []
    def unnormalize_subproblem(x):
        base_context = SP.problem.assumptions.base_context
        additional_context = []
        for i in x.assumptions.base_context:
            if i not in base_context:
                additional_context += [i]
        for i in x.assumptions.additional_context:
            if i not in base_context:
                additional_context += [i]
        conclusion = x.conclusion
        return LittleProblem(Context(base_context,additional_context),conclusion)
    for i in SP.subproblems:
        if not is_LP_tautology(i):
            raise ValueError("Bad arguments")
        unnormalised_subproblems.append(unnormalize_subproblem(i))
    match SP.rule:
        case Assumption():
            BaseContext = SP.problem.assumptions.base_context
            phi = SP.problem.conclusion
            return SP.problem == SP.rule.top_down(unnormalised_subproblems,BaseContext = BaseContext,phi = phi)
        case Weakening():
            assumptions_thesis = SP.problem.assumptions.base_context + SP.problem.assumptions.additional_context
            assumptions_conclusion = SP.subproblems[0].assumptions.base_context + SP.subproblems[0].assumptions.additional_context
            psi = None
            for i in assumptions_thesis:
                if i not in assumptions_conclusion:
                    psi = i
                    break
            if psi is None:
                psi = assumptions_thesis[-1]
            return SP.problem == SP.rule.top_down(unnormalised_subproblems,psi=psi)
        case ImplicationIntroduction():
            phi = SP.problem.conclusion.Left()
            return SP.problem == SP.rule.top_down(unnormalised_subproblems,phi=phi)
        case NegationIntroduction():
            phi = SP.problem.conclusion.Left()
            return SP.problem == SP.rule.top_down(unnormalised_subproblems,phi=phi)
        case ImplicationElimination():
            return SP.problem == SP.rule.top_down(unnormalised_subproblems)
        case NegationElimination():
            return SP.problem == SP.rule.top_down(unnormalised_subproblems)
        case ConjunctionIntroduction():
            return SP.problem == SP.rule.top_down(unnormalised_subproblems)
        case DisjunctionIntroduction1():
            psi = SP.problem.conclusion.Right()
            return SP.problem == SP.rule.top_down(unnormalised_subproblems,psi=psi)
        case DisjunctionIntroduction2():
            phi = SP.problem.conclusion.Left()
            return SP.problem == SP.rule.top_down(unnormalised_subproblems,phi = phi)
        case TruthIntroduction():
            BaseContext = SP.problem.assumptions.base_context
            return SP.problem == SP.rule.top_down(unnormalised_subproblems,BaseContext)
        case ConjunctionElimination1():
            return SP.problem == SP.rule.top_down(unnormalised_subproblems)
        case ConjunctionElimination2():
            return SP.problem == SP.rule.top_down(unnormalised_subproblems)
        case DisjunctionElimination():
            return SP.problem == SP.rule.top_down(unnormalised_subproblems)
        case LieElimination():
            phi = SP.problem.conclusion
            return SP.problem == SP.rule.top_down(unnormalised_subproblems,phi=phi)
        case IffIntroduction():
            return SP.problem == SP.rule.top_down(unnormalised_subproblems)
        case IffElimination1():
            return SP.problem == SP.rule.top_down(unnormalised_subproblems)
        case IffElimination2():
            return SP.problem == SP.rule.top_down(unnormalised_subproblems)
        case RAA():
            phi = SP.problem.conclusion
            return SP.problem == SP.rule.top_down(unnormalised_subproblems,phi=phi)
        case NegationOfNegation():
            phi = SP.problem.conclusion
            return SP.problem == SP.rule.top_down(unnormalised_subproblems)
        case TND():
            BaseContext = SP.problem.assumptions.base_context
            phi = SP.problem.conclusion.Left()
            return SP.problem == SP.rule.top_down(unnormalised_subproblems,phi=phi,BaseContext = BaseContext)
        case FromContext():
            phi = SP.problem.conclusion
            #print(SP.problem," | ", SP.rule.top_down(unnormalised_subproblems,phi=phi))
            return SP.problem == SP.rule.top_down(unnormalised_subproblems,phi=phi)
        case FromWeakenContext():
            phi = SP.problem.conclusion
            return SP.problem == SP.rule.top_down(unnormalised_subproblems,phi=phi)
        case _:
            pass

proof = """1. b   assumption
2. y ∨ ¬y    TND
3. b    weakening, 2, 1"""
parsedProof = parseProof(proof)


for i in parsedProof.keys():
    print(smash_with_proof(parsedProof[i],parsedProof))
    print(is_smashed_correctly(smash_with_proof(parsedProof[i],parsedProof)))
#%%
with open("proofs_normalised.txt", "r", encoding="utf-8") as f:
    text = f.read()
text = [p.strip() for p in re.split(r'\n\s*\n', text.strip()) if p.strip()]
for i in enumerate(text):
    first, *rest = i[1].split("\n", 1)
    #print(first,i[0])
    first = first[12:]
    rest = rest[0] if rest else ""
    text[i[0]] = [first, rest]


smashed_problems = []
#%%
'''
from tqdm import tqdm
for i in tqdm(range(len(text))):
    parsedProof = parseProof(text[i][1])
    for j in parsedProof.keys():
        SP = smash_with_proof(parsedProof[j],parsedProof)
        #print(SP)
        if not is_smashed_correctly(SP):
            raise TypeError("Bad smashed")
'''
#%%

def to_infix_LP_simple(LP: LittleProblem) -> str:
    ans = ""
    for i in LP.assumptions.base_context:
        ans += to_infix(i) + ", "
    for i in LP.assumptions.additional_context:
        ans += to_infix(i) + ", "
    if ans != "":
        ans = ans[:-2]
    ans += " ⊢ " + to_infix(LP.conclusion)

    return ans

def pretty_print_smashed_problem(x:smashed_problem):
    ans = "Smash: "
    ans += to_infix_LP_simple(x.problem)
    ans += "\nWith: "
    ans += x.rule.__str__()
    ans += "\nTo: "
    for i in x.subproblems:
        ans += to_infix_LP_simple(i)
        ans += ",\n"
    if x.subproblems != []:
        ans = ans[:-2]
    return ans
'''
NEW_CORPUS_SMASH = ""
for i in tqdm(range(len(text))):
    proof = parseProof(text[i][1])
    for j in proof.keys():
        NEW_CORPUS_SMASH += pretty_print_smashed_problem(smash_with_proof(proof[j], proof))
        NEW_CORPUS_SMASH += "\n\n"
'''
#%%
from concurrent.futures import ProcessPoolExecutor
from tqdm import tqdm
import os


def to_infix_LP_simple(LP: LittleProblem) -> str:
    ans = ""
    for i in LP.assumptions.base_context:
        ans += to_infix(i) + ", "
    for i in LP.assumptions.additional_context:
        ans += to_infix(i) + ", "
    if ans != "":
        ans = ans[:-2]
    ans += " ⊢ " + to_infix(LP.conclusion)
    return ans


def pretty_print_smashed_problem(x: smashed_problem):
    ans = "Smash: "
    ans += to_infix_LP_simple(x.problem)
    ans += "\nWith: "
    ans += x.rule.__str__()
    ans += "\nTo: "
    for i in x.subproblems:
        ans += to_infix_LP_simple(i)
        ans += ",\n"
    if x.subproblems != []:
        ans = ans[:-2]
    return ans




#%%
def check_smash_from_text(smash):
    smash = smash.splitlines()
    main_problem_unparsed = smash[0][7:]
    main_problem_unparsed = main_problem_unparsed.lstrip(" ")
    main_problem_unparsed = main_problem_unparsed.split("⊢")
    main_problem_unparsed[0] = main_problem_unparsed[0].split(",")
    if main_problem_unparsed[0] == [""]:
        main_problem_unparsed[0] = []
    base_context = []
    for i in main_problem_unparsed[0]:
        base_context.append(parse_infix(i))
    print(main_problem_unparsed[1])
    main_conclusion = parse_infix(main_problem_unparsed[1])
    goal = LittleProblem(Context(base_context,[]),conclusion=main_conclusion)
    rule_unparsed = smash[1][6:]
    rule_unparsed = rule_unparsed.lstrip(" ")
    rule_unparsed = rule_unparsed.rstrip(" ")
    rule = None
    match rule_unparsed:
        case 'Assumption':
            rule = Assumption()
        case "Weakening":
            rule = Weakening()
        case "ImplicationIntroduction":
            rule = ImplicationIntroduction()
        case "NegationIntroduction":
            rule = NegationIntroduction()
        case "ImplicationElimination":
            rule = ImplicationElimination()
        case "NegationElimination":
            rule = NegationElimination()
        case "ConjunctionIntroduction":
            rule = ConjunctionIntroduction()
        case "DisjunctionIntroduction1":
            rule = DisjunctionIntroduction1()
        case "DisjunctionIntroduction2":
            rule = DisjunctionIntroduction2()
        case "TruthIntroduction":
            rule = TruthIntroduction()
        case "ConjunctionElimination1":
            rule = ConjunctionElimination1()
        case "ConjunctionElimination2":
            rule = ConjunctionElimination2()
        case "DisjunctionElimination":
            rule = DisjunctionElimination()
        case "LieElimination":
            rule = LieElimination()
        case "IffIntroduction":
            rule = IffIntroduction()
        case "IffElimination1":
            rule = IffElimination1()
        case "IffElimination2":
            rule = IffElimination2()
        case "RAA":
            rule = RAA()
        case "NegationOfNegation":
            rule = NegationOfNegation()
        case "TND":
            rule = TND()
        case "FromContext":
            rule = FromContext()
        case "FromWeakenContext":
            rule = FromWeakenContext()
    if rule == None:
        raise TypeError("Bad rule")
    smash[2] = smash[2].rstrip(" ")
    smash[2]= smash[2].rstrip(",")
    for i in range(3,len(smash)):
        smash[i] = smash[i].rstrip(" ")
        smash[i] = smash[i].rstrip(",")


    subproblems= []
    if not smash[2] == "To:":
        subproblems.append(smash[2][3:])
        for i in range(3,len(smash)):
            subproblems.append(smash[i])


    for i in range(len(subproblems)):
        subproblems[i] = subproblems[i].split("⊢")
        subproblems[i][0] = subproblems[i][0].split(",")
        subproblems[i][1] = parse_infix(subproblems[i][1])
        for j in range(len(subproblems[i][0])):
            subproblems[i][0][j] = subproblems[i][0][j].rstrip(" ")
        if subproblems[i][0] == [""]:
            subproblems[i][0] = []
        for j in range(len(subproblems[i][0])):
            subproblems[i][0][j] = parse_infix(subproblems[i][0][j])
        subproblems[i] = LittleProblem(Context(subproblems[i][0],[]),conclusion=subproblems[i][1])
    SP = smashed_problem(goal,subproblems,rule)
    if not is_smashed_correctly(SP):
        raise TypeError("Bad smashed problem")
    return SP

with open("new_corpus_smash.txt", "r", encoding="utf-8") as f:
    text = f.read()
text = [p.strip() for p in re.split(r'\n\s*\n', text.strip()) if p.strip()]

#%%
def process_one(proof_text: str) -> str:
    proof = parseProof(proof_text)
    parts = []
    for j in proof.keys():
        parts.append(pretty_print_smashed_problem(smash_with_proof(proof[j], proof)))
    for i in parts:
        check_smash_from_text(i)
    return "\n\n".join(parts)


prompt = '''1. (p → q) ∧ p    assumption
2. p → q    ∧-elimination1, 1
3. (p → q) ∧ ¬q    assumption
4. p → q    ∧-elimination1, 3
5. ¬q    ∧-elimination2, 3
6. p    assumption
7. q    →-elimination, 4, 6
8. ⊥    ¬-elimination, 5, 7
9. ¬p    ¬-introduction, 6, 8
10. ((p → q) ∧ ¬q) → ¬p    →-introduction, 3, 9'''

'''
with open("proofs_raw.txt", "r", encoding="utf-8") as f:
    text = f.read()
text = [p.strip() for p in re.split(r'\n\s*\n', text.strip()) if p.strip()]


with ProcessPoolExecutor(max_workers=os.cpu_count()) as executor:
    smashed_proofs = list(
        tqdm(
            executor.map(
                process_one,
                text,
                chunksize=320
            ),
            total=len(text)
        )
    )
'''
#%%
''''
text = "\n\n".join(smashed_proofs)
with open("NEW_CORPUS_SMASHTosecondTraining.txt", "w", encoding="utf-8") as f:
    f.write(text)
'''
#%% md
# Trening

#%%
len(text)
#%% md
with open("proofs_normalised.txt", "r", encoding="utf-8") as f:

#%%
with open("new_corpus_smash.txt", "r", encoding="utf-8") as f:
    text = f.read()
#%%

import pickle
import re
import shutil
import subprocess
import sys
from pathlib import Path

import numpy as np


def train_nanogpt_on_file(
    file_name: str,
    dataset_name: str | None = None,
    out_dir: str | None = None,
    train_split: float = 0.9,
    max_iters: int = 20000,
    eval_interval: int = 1000,
    log_interval: int = 1,
    batch_size: int = 12,
    block_size: int = 1024,
    n_layer: int = 6,
    n_head: int = 6,
    n_embd: int = 384,
    num_params = 2478690,
    learning_rate: float = 2e-2,
    compile_model: bool = False,
    device: str | None = None,
):
    project_root = Path(globals().get('PROJECT_ROOT', Path.cwd()))
    pkg_root = Path(globals().get('PKG_ROOT', project_root / 'nanoGPT-20251228T135841Z-3-001' / 'nanoGPT'))

    def estimate_num_params(n_layer: int, n_head: int, n_embd: int, vocab_size: int, block_size: int) -> int:
        return (
            vocab_size * n_embd
            + block_size * n_embd
            + n_layer * (12 * n_embd * n_embd + 2 * n_embd)
            + 2 * n_embd
        )

    def choose_model_size_for_target(target: int, vocab_size: int, block_size: int) -> tuple[int, int, int, int]:
        best = None
        for embd in range(128, 2049, 64):
            for layers in range(2, 49):
                for heads in range(2, 33):
                    if embd % heads != 0:
                        continue
                    params = estimate_num_params(layers, heads, embd, vocab_size, block_size)
                    cand = (abs(params - target), params, layers, heads, embd)
                    if best is None or cand < best:
                        best = cand
        if best is None:
            raise ValueError("Nie udało się dobrać konfiguracji modelu dla num_params.")
        _, params, layers, heads, embd = best
        return layers, heads, embd, params

    if not (pkg_root / 'train.py').exists():
        alt_pkg_root = project_root / 'nanoGPT'
        if (alt_pkg_root / 'train.py').exists():
            pkg_root = alt_pkg_root
        else:
            raise FileNotFoundError(f'Nie znaleziono train.py w {pkg_root} ani {alt_pkg_root}.')

    src = Path(file_name).expanduser()
    if not src.is_absolute():
        from_project = (project_root / src).resolve()
        from_cwd = (Path.cwd() / src).resolve()
        src = from_project if from_project.exists() else from_cwd

    if not src.exists():
        raise FileNotFoundError(f'Nie znaleziono pliku wejsciowego: {src}')

    if dataset_name is None:
        dataset_name = re.sub(r'[^0-9A-Za-z_]+', '_', src.stem).strip('_') or 'custom_char'

    data_dir = pkg_root / 'data' / dataset_name
    data_dir.mkdir(parents=True, exist_ok=True)
    input_txt = data_dir / 'input.txt'
    shutil.copy2(src, input_txt)

    text = input_txt.read_text(encoding='utf-8')
    if len(text) < 2:
        raise ValueError('Plik wejsciowy jest zbyt krotki do podzialu train/val.')

    chars = sorted(set(text))
    vocab_size = len(chars)
    if vocab_size > 65535:
        raise ValueError('Za duzo unikalnych znakow dla kodowania uint16.')

    stoi = {ch: i for i, ch in enumerate(chars)}
    itos = {i: ch for i, ch in enumerate(chars)}

    ids = np.array([stoi[ch] for ch in text], dtype=np.uint16)
    print(ids.__len__())
    split_idx = int(len(ids) * train_split)
    split_idx = max(1, min(len(ids) - 1, split_idx))

    train_ids = ids[:split_idx]
    val_ids = ids[split_idx:]

    train_ids.tofile(data_dir / 'train.bin')
    val_ids.tofile(data_dir / 'val.bin')

    meta = {'vocab_size': vocab_size, 'itos': itos, 'stoi': stoi}
    with open(data_dir / 'meta.pkl', 'wb') as f:
        pickle.dump(meta, f)
    print(ids.__len__()/20)
    if num_params is not None:
        n_layer, n_head, n_embd, estimated_params = choose_model_size_for_target(
            num_params, vocab_size, block_size
        )
        print(f'Wybrana konfiguracja pod num_params={num_params}:')
        print(f'  n_layer={n_layer}, n_head={n_head}, n_embd={n_embd}')
        print(f'  szacowana liczba parametrów: {estimated_params}')
    else:
        estimated_params = estimate_num_params(n_layer, n_head, n_embd, vocab_size, block_size)
        print(f'Szacowana liczba parametrów: {estimated_params}')
# ... existing code ...

    if out_dir is None:
        model_out_dir = pkg_root / f'out-{dataset_name}'
    else:
        model_out_dir = Path(out_dir)
        if not model_out_dir.is_absolute():
            model_out_dir = pkg_root / model_out_dir

    if device is None:
        device = 'cuda' if shutil.which('nvidia-smi') else 'cpu'

    print(f'Plik wejsciowy: {src.resolve()}')
    print(f'Model bedzie zapisany w: {model_out_dir.resolve()}')
    print(f'Dataset nanoGPT: {dataset_name}')

    cmd = [
        sys.executable,
        'train.py',
        f'--dataset={dataset_name}',
        f'--out_dir={model_out_dir}',
        f'--max_iters={max_iters}',
        f'--eval_interval={eval_interval}',
        f'--log_interval={log_interval}',
        f'--batch_size={batch_size}',
        f'--block_size={block_size}',
        f'--n_layer={n_layer}',
        f'--n_head={n_head}',
        f'--n_embd={n_embd}',
        f'--learning_rate={learning_rate}',
        f'--device={device}',
        f'--compile={compile_model}',
        '--always_save_checkpoint=True'

    ]

    process = subprocess.Popen(
        cmd,
        cwd=str(pkg_root),
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        bufsize=1,
    )

    if process.stdout is None:
        raise RuntimeError('Nie udalo sie przechwycic logow treningu.')

    for line in process.stdout:
        print(line, end='')

    return_code = process.wait()
    if return_code != 0:
        raise RuntimeError(f'Trening nanoGPT zakonczyl sie kodem {return_code}.')

    return model_out_dir

#%%
'''
def finetune_nanogpt_on_file(
    file_name: str,
    base_model: str,
    dataset_name: str | None = None,
    out_dir: str | None = None,
    train_split: float = 0.9,
    max_iters: int = 20000,
    eval_interval: int = 1000,
    log_interval: int = 1,
    batch_size: int = 12,
    block_size: int = 1024,
    learning_rate: float = 1e-3,
    compile_model: bool = False,
    device: str | None = None,
):
    project_root = Path(globals().get('PROJECT_ROOT', Path.cwd()))
    pkg_root = Path(globals().get('PKG_ROOT', project_root / 'nanoGPT-20251228T135841Z-3-001' / 'nanoGPT'))

    if not (pkg_root / 'train.py').exists():
        alt_pkg_root = project_root / 'nanoGPT'
        if (alt_pkg_root / 'train.py').exists():
            pkg_root = alt_pkg_root
        else:
            raise FileNotFoundError(f'Nie znaleziono train.py w {pkg_root} ani {alt_pkg_root}.')

    src = Path(file_name).expanduser()
    if not src.is_absolute():
        from_project = (project_root / src).resolve()
        from_cwd = (Path.cwd() / src).resolve()
        src = from_project if from_project.exists() else from_cwd
    if not src.exists():
        raise FileNotFoundError(f'Nie znaleziono pliku wejsciowego: {src}')

    base_model_path = Path(base_model).expanduser()
    if not base_model_path.is_absolute():
        from_project = (project_root / base_model_path).resolve()
        from_cwd = (Path.cwd() / base_model_path).resolve()
        from_pkg = (pkg_root / base_model_path).resolve()
        if from_project.exists():
            base_model_path = from_project
        elif from_cwd.exists():
            base_model_path = from_cwd
        else:
            base_model_path = from_pkg
    print(base_model_path)
    ckpt_src = base_model_path / 'ckpt.pt' if base_model_path.is_dir() else base_model_path
    print(ckpt_src)
    if ckpt_src.name != 'ckpt.pt':
        raise ValueError('Argument base_model musi wskazywac katalog modelu albo plik ckpt.pt.')
    if not ckpt_src.exists():
        raise FileNotFoundError(f'Nie znaleziono checkpointu: {ckpt_src}')
    source_out_dir = ckpt_src.parent

    import torch

    checkpoint = torch.load(ckpt_src, map_location='cpu')
    checkpoint_cfg = checkpoint.get('config', {})
    checkpoint_model_args = checkpoint.get('model_args', {})
    checkpoint_dataset = checkpoint_cfg.get('dataset')
    checkpoint_block_size = checkpoint_model_args.get('block_size')
    checkpoint_vocab_size = checkpoint_model_args.get('vocab_size')

    if checkpoint_dataset is None:
        raise ValueError('Checkpoint nie zawiera nazwy datasetu w config[\'dataset\'].')

    source_meta_path = pkg_root / 'data' / checkpoint_dataset / 'meta.pkl'
    if not source_meta_path.exists():
        raise FileNotFoundError(f'Nie znaleziono tokenizera modelu: {source_meta_path}')

    with open(source_meta_path, 'rb') as f:
        source_meta = pickle.load(f)

    stoi = source_meta.get('stoi')
    itos = source_meta.get('itos')
    vocab_size = source_meta.get('vocab_size')
    if not isinstance(stoi, dict) or not isinstance(itos, dict):
        raise ValueError('Niepoprawny format source meta.pkl (brak stoi/itos).')

    if checkpoint_vocab_size is not None and vocab_size != checkpoint_vocab_size:
        raise ValueError(
            'Niezgodny vocab_size miedzy checkpointem a tokenizerem: '
            f'{checkpoint_vocab_size} != {vocab_size}'
        )

    text = src.read_text(encoding='utf-8')
    if len(text) < 2:
        raise ValueError('Plik wejsciowy jest zbyt krotki do podzialu train/val.')

    unknown_chars = sorted({ch for ch in text if ch not in stoi})
    if unknown_chars:
        preview = ''.join(unknown_chars[:20])
        raise ValueError(
            f'Tekst zawiera {len(unknown_chars)} znakow spoza tokenizera modelu. '
            f'Przyklad: {preview!r}'
        )

    ids = np.array([stoi[ch] for ch in text], dtype=np.uint16)
    split_idx = int(len(ids) * train_split)
    split_idx = max(1, min(len(ids) - 1, split_idx))
    train_ids = ids[:split_idx]
    val_ids = ids[split_idx:]

    if dataset_name is None:
        base_dataset = re.sub(r'[^0-9A-Za-z_]+', '_', src.stem).strip('_') or 'custom_char'
        dataset_name = f'{base_dataset}_finetune'

    data_dir = pkg_root / 'data' / dataset_name
    data_dir.mkdir(parents=True, exist_ok=True)
    input_txt = data_dir / 'input.txt'
    shutil.copy2(src, input_txt)
    train_ids.tofile(data_dir / 'train.bin')
    val_ids.tofile(data_dir / 'val.bin')

    meta = {
        'vocab_size': vocab_size,
        'itos': itos,
        'stoi': stoi,
    }
    with open(data_dir / 'meta.pkl', 'wb') as f:
        pickle.dump(meta, f)

    if out_dir is None:
        model_out_dir = source_out_dir
    else:
        model_out_dir = Path(out_dir)
        if not model_out_dir.is_absolute():
            model_out_dir = pkg_root / model_out_dir
    model_out_dir.mkdir(parents=True, exist_ok=True)

    ckpt_dst = model_out_dir / 'ckpt.pt'
    if ckpt_dst.resolve() != ckpt_src.resolve():
        shutil.copy2(ckpt_src, ckpt_dst)

    if block_size is None:
        block_size = checkpoint_block_size
    if block_size is None:
        raise ValueError('Nie mozna ustalic block_size z checkpointu. Podaj block_size recznie.')
    if checkpoint_block_size is not None and block_size > checkpoint_block_size:
        raise ValueError(
            f'block_size={block_size} nie moze byc wiekszy niz block_size modelu ({checkpoint_block_size}).'
        )

    if device is None:
        device = 'cuda' if shutil.which('nvidia-smi') else 'cpu'

    print(f'Plik wejsciowy: {src.resolve()}')
    print(f'Checkpoint bazowy: {ckpt_src.resolve()}')
    print(f'Model bedzie zapisany w: {model_out_dir.resolve()}')
    print(f'Dataset nanoGPT: {dataset_name}')

    cmd = [
        sys.executable,
        'train.py',
        f'--dataset={dataset_name}',
        f'--out_dir={model_out_dir}',
        '--init_from=resume',
        f'--max_iters={max_iters}',
        f'--eval_interval={eval_interval}',
        f'--log_interval={log_interval}',
        f'--batch_size={batch_size}',
        f'--block_size={block_size}',
        f'--learning_rate={learning_rate}',
        f'--device={device}',
        f'--compile={compile_model}',
        '--always_save_checkpoint=True',
    ]

    process = subprocess.Popen(
        cmd,
        cwd=str(pkg_root),
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        bufsize=1,
    )

    if process.stdout is None:
        raise RuntimeError('Nie udalo sie przechwycic logow treningu.')

    for line in process.stdout:
        print(line, end='')

    return_code = process.wait()
    if return_code != 0:
        raise RuntimeError(f'Dotrenowanie nanoGPT zakonczyl sie kodem {return_code}.')

    return model_out_dir
'''
def finetune_nanogpt_on_file(
    file_name: str,
    base_model: str,
    dataset_name: str | None = None,
    out_dir: str | None = None,
    train_split: float = 0.9,
    max_iters: int = 20000,
    eval_interval: int = 1000,
    log_interval: int = 1,
    batch_size: int = 12,
    block_size: int = 1024,
    learning_rate: float = 1e-3,
    compile_model: bool = False,
    device: str | None = None,
):
    project_root = Path(globals().get('PROJECT_ROOT', Path.cwd()))
    pkg_root = Path(globals().get('PKG_ROOT', project_root / 'nanoGPT-20251228T135841Z-3-001' / 'nanoGPT'))

    if not (pkg_root / 'train.py').exists():
        alt_pkg_root = project_root / 'nanoGPT'
        if (alt_pkg_root / 'train.py').exists():
            pkg_root = alt_pkg_root
        else:
            raise FileNotFoundError(f'Nie znaleziono train.py w {pkg_root} ani {alt_pkg_root}.')

    src = Path(file_name).expanduser()
    if not src.is_absolute():
        from_project = (project_root / src).resolve()
        from_cwd = (Path.cwd() / src).resolve()
        src = from_project if from_project.exists() else from_cwd
    if not src.exists():
        raise FileNotFoundError(f'Nie znaleziono pliku wejsciowego: {src}')

    base_model_path = Path(base_model).expanduser()
    if not base_model_path.is_absolute():
        from_project = (project_root / base_model_path).resolve()
        from_cwd = (Path.cwd() / base_model_path).resolve()
        from_pkg = (pkg_root / base_model_path).resolve()
        if from_project.exists():
            base_model_path = from_project
        elif from_cwd.exists():
            base_model_path = from_cwd
        else:
            base_model_path = from_pkg

    ckpt_src = base_model_path / 'ckpt.pt' if base_model_path.is_dir() else base_model_path
    if ckpt_src.name != 'ckpt.pt':
        raise ValueError('Argument base_model musi wskazywac katalog modelu albo plik ckpt.pt.')
    if not ckpt_src.exists():
        raise FileNotFoundError(f'Nie znaleziono checkpointu: {ckpt_src}')
    source_out_dir = ckpt_src.parent

    import torch

    checkpoint = torch.load(ckpt_src, map_location='cpu')
    checkpoint_cfg = checkpoint.get('config', {})
    checkpoint_model_args = checkpoint.get('model_args', {})
    checkpoint_dataset = checkpoint_cfg.get('dataset')
    checkpoint_block_size = checkpoint_model_args.get('block_size')
    checkpoint_vocab_size = checkpoint_model_args.get('vocab_size')

    if checkpoint_dataset is None:
        raise ValueError('Checkpoint nie zawiera nazwy datasetu w config[\'dataset\'].')

    source_meta_path = pkg_root / 'data' / checkpoint_dataset / 'meta.pkl'
    if not source_meta_path.exists():
        raise FileNotFoundError(f'Nie znaleziono tokenizera modelu: {source_meta_path}')

    with open(source_meta_path, 'rb') as f:
        source_meta = pickle.load(f)

    stoi = source_meta.get('stoi')
    itos = source_meta.get('itos')
    vocab_size = source_meta.get('vocab_size')
    if not isinstance(stoi, dict) or not isinstance(itos, dict):
        raise ValueError('Niepoprawny format source meta.pkl (brak stoi/itos).')

    if checkpoint_vocab_size is not None and vocab_size != checkpoint_vocab_size:
        raise ValueError(
            'Niezgodny vocab_size miedzy checkpointem a tokenizerem: '
            f'{checkpoint_vocab_size} != {vocab_size}'
        )

    text = src.read_text(encoding='utf-8')
    if len(text) < 2:
        raise ValueError('Plik wejsciowy jest zbyt krotki do podzialu train/val.')

    unknown_chars = sorted({ch for ch in text if ch not in stoi})
    if unknown_chars:
        preview = ''.join(unknown_chars[:20])
        raise ValueError(
            f'Tekst zawiera {len(unknown_chars)} znakow spoza tokenizera modelu. '
            f'Przyklad: {preview!r}'
        )

    ids = np.array([stoi[ch] for ch in text], dtype=np.uint16)
    split_idx = int(len(ids) * train_split)
    split_idx = max(1, min(len(ids) - 1, split_idx))
    train_ids = ids[:split_idx]
    val_ids = ids[split_idx:]

    if dataset_name is None:
        base_dataset = re.sub(r'[^0-9A-Za-z_]+', '_', src.stem).strip('_') or 'custom_char'
        dataset_name = f'{base_dataset}_finetune'

    data_dir = pkg_root / 'data' / dataset_name
    data_dir.mkdir(parents=True, exist_ok=True)
    input_txt = data_dir / 'input.txt'
    shutil.copy2(src, input_txt)
    train_ids.tofile(data_dir / 'train.bin')
    val_ids.tofile(data_dir / 'val.bin')

    meta = {
        'vocab_size': vocab_size,
        'itos': itos,
        'stoi': stoi,
    }
    with open(data_dir / 'meta.pkl', 'wb') as f:
        pickle.dump(meta, f)

    if out_dir is None:
        model_out_dir = source_out_dir
    else:
        model_out_dir = Path(out_dir)
        if not model_out_dir.is_absolute():
            model_out_dir = pkg_root / model_out_dir
    model_out_dir.mkdir(parents=True, exist_ok=True)

    ckpt_dst = model_out_dir / 'ckpt.pt'
    if ckpt_dst.resolve() != ckpt_src.resolve():
        shutil.copy2(ckpt_src, ckpt_dst)

    if block_size is None:
        block_size = checkpoint_block_size
    if block_size is None:
        raise ValueError('Nie mozna ustalic block_size z checkpointu. Podaj block_size recznie.')
    if checkpoint_block_size is not None and block_size > checkpoint_block_size:
        raise ValueError(
            f'block_size={block_size} nie moze byc wiekszy niz block_size modelu ({checkpoint_block_size}).'
        )

    if device is None:
        device = 'cuda' if shutil.which('nvidia-smi') else 'cpu'

    print(f'Plik wejsciowy: {src.resolve()}')
    print(f'Checkpoint bazowy: {ckpt_src.resolve()}')
    print(f'Model bedzie zapisany w: {model_out_dir.resolve()}')
    print(f'Dataset nanoGPT: {dataset_name}')

    cmd = [
        sys.executable,
        'train.py',
        f'--dataset={dataset_name}',
        f'--out_dir={model_out_dir}',
        '--init_from=resume',
        f'--max_iters={max_iters}',
        f'--eval_interval={eval_interval}',
        f'--log_interval={log_interval}',
        f'--batch_size={batch_size}',
        f'--block_size={block_size}',
        f'--learning_rate={learning_rate}',
        f'--device={device}',
        f'--compile={compile_model}',
        '--always_save_checkpoint=True',
    ]

    process = subprocess.Popen(
        cmd,
        cwd=str(pkg_root),
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        bufsize=1,
    )

    if process.stdout is None:
        raise RuntimeError('Nie udalo sie przechwycic logow treningu.')

    for line in process.stdout:
        print(line, end='')

    return_code = process.wait()
    if return_code != 0:
        raise RuntimeError(f'Dotrenowanie nanoGPT zakonczyl sie kodem {return_code}.')

    return model_out_dir
#%%
'''
finetune_nanogpt_on_file(
    "NEW_CORPUS_SMASHTosecondTraining.txt",
    "out-NEW_CORPUS_SMASH",
    device="cuda",
    batch_size=12,
    block_size=1024,
    max_iters=14200,
    eval_interval=20,
    learning_rate=0.0001
)
finetune_nanogpt_on_file(
    "corpus_smash_finetune1.txt",
    "out-NEW_CORPUS_SMASH",
    device="cuda",
    batch_size=12,
    block_size=1024,
    max_iters=14000,
    eval_interval=20,
    learning_rate=0.0001
)
train_nanogpt_on_file(
    "NEW_CORPUS_SMASHTosecondTraining.txt",
    device="cuda",
    n_layer=24,
    n_head=24,
    n_embd=768,
    batch_size=12,
    block_size=1024,
    max_iters=1000,
    eval_interval=200,
    learning_rate=0.01,
    num_params = 100000000
)


finetune_nanogpt_on_file(
    "NEW_CORPUS_PROVING.txt",
    "out-NEW_CORPUS_PROVING",
    device="cuda",
    batch_size=12,
    block_size=1024,
    max_iters=10000,
    eval_interval=20,
    learning_rate=0.0002
)
finetune_nanogpt_on_file(
    "corpus_inverted.txt",
    "out-corpus_inverted.txt",
    device="cuda",
    batch_size=12,
    block_size=1024,
    max_iters=10000,
    eval_interval=20,
    learning_rate=0.0005
)
finetune_nanogpt_on_file(
    "new_corpus_proving2.txt",
    "out-new_corpus_proving2",
    device="cuda",
    batch_size=12,
    block_size=1024,
    max_iters=10000,
    eval_interval=20,
    learning_rate=0.0001
)

finetune_nanogpt_on_file(
    "new_corpus_proving2.txt",
    "out-new_corpus_proving2",
    device="cuda",
    batch_size=12,
    block_size=1024,
    max_iters=100000,
    eval_interval=1,
    learning_rate=0.0000000001
)
'''
#%%
'''
finetune_nanogpt_on_file(
    "corpus_inverted.txt",
    "out-corpus_inverted",
    device="cuda",
    batch_size=12,
    block_size=1024,
    max_iters=5000,
    eval_interval=20,
    learning_rate=0.01
)
finetune_nanogpt_on_file(
    "new_corpus_proving2.txt",
    "out-new_corpus_proving2",
    device="cuda",
    batch_size=12,
    block_size=1024,
    max_iters=10000,
    eval_interval=20,
    learning_rate=0.0005
)
'''
#%%
def almost_equal(x:LittleProblem,y:LittleProblem):
    return basing_context_of_LP(x) == basing_context_of_LP(y)

def extract_proof(proof:str,LP:LittleProblem,BaseContext = []):
    '''
    BaseContext to kontekst bazowy w którym dzieje się proof
    '''
    parsedProof = parseProof(proof,base_context=BaseContext)
    goal_idx = -1
    for i in parsedProof.keys():
        if almost_equal(parsedProof[i].LP,LP):
            goal_idx = i
            break
    if goal_idx == -1:
        raise TypeError("Cannot extract")
    important_lines = [goal_idx]
    def next_elems():

        ans = []
        for i in parsedProof.keys():
            if not i in important_lines:
                for j in  important_lines:
                    if i in parsedProof[j].args_keys:
                        ans.append(i)
                        break

        return ans
    next_elems_values = next_elems()
    while next_elems_values != []:
        important_lines += next_elems_values
        next_elems_values = next_elems()
    important_lines.sort()
    ans = ""
    proof = proof.splitlines()
    for i in proof:
        idx = int(i.split(".")[0])
        if idx in important_lines:
            ans += i
            ans += "\n"
    ans = ans[:-1]
    return ans
    def replace_indexed_numbers(ls: List[str], li: List[int]) -> List[str]:
        mapping = {int(li[i]): str(i+1) for i in range(len(li))}
        if not mapping:
            return ls[:]

        alts = "|".join(
            re.escape(str(n)) for n in sorted(mapping.keys(), key=lambda x: (-len(str(x)), x))
        )

        pattern = re.compile(
            rf'(?:(, |–)({alts})(?!\d))|(?:(?<!\d)({alts})(?!\d)(?=\.))'
        )

        def repl(m: re.Match) -> str:
            if m.group(2) is not None:  # gałąź z prefiksem
                prefix = m.group(1)
                num = m.group(2)
                return prefix + mapping[int(num)]
            else:  # gałąź z kropką po liczbie
                num = m.group(3)
                return mapping[int(num)]

        ans_lines = [pattern.sub(repl, s) for s in ls]
        ans = "\n".join(ans_lines)
        return ans

    return replace_indexed_numbers(ans.splitlines(),important_lines)

def give_all_extraction_text(proof:str,BaseContext = []):
    parsedProof = parseProof(proof,base_context = BaseContext)
    ANS = ""
    for i in parsedProof.keys():
        goal = parsedProof[i].LP
        temporary_context = deepcopy(BaseContext)
        for j in goal.assumptions.base_context:
            if not j in BaseContext:
                temporary_context.append(j)
        for j in goal.assumptions.additional_context:
            if not j in BaseContext:
                temporary_context.append(j)
        goal.assumptions.base_context = temporary_context#?
        goal.assumptions.additional_context = []#?
        extracted = extract_proof(proof,goal,temporary_context)
        parseProof(extracted,temporary_context)
        #extracted = simpliffy_with_context(extracted,temporary_context)
        parseProof(extracted,base_context = temporary_context)
        ans = "Prove that: " + to_infix(goal.conclusion)
        if temporary_context != []:
            ans += "\nassuming that: "
            for j in temporary_context:
                ans += to_infix(j)
                ans += ",\n"
            ans = ans[:-2]
        ans += ("\n"+extracted)
        ANS += ans
        ANS += "\n\n"
    return ANS

extracted_proofs = give_all_extraction_text('''1. (p → q) ∧ p    assumption
2. p → q    ∧-elimination1, 1
3. (p ∧ q) ∧ (r ∧ s)    assumption
4. p ∧ q    ∧-elimination1, 3
5. r ∧ s    ∧-elimination2, 3
6. q    ∧-elimination2, 4
7. s    ∧-elimination2, 5
8. q    assumption
9. s    weakening, 8, 7
10. s    assumption
11. q    weakening, 10, 6
12. q ↔ s    ↔-introduction, 9, 11
13. q ∨ ¬q    TND
14. ¬q    assumption
15. q    weakening, 14, 6
16. ⊥    ¬-elimination, 14, 15
17. ⊥    weakening, 7, 16
18. q ↔ s    ⊥-elimination, 17
19. q ↔ s    ∨-elimination, 13, 12, 18
20. s ∨ ¬s    TND
21. ¬s    assumption
22. s    weakening, 21, 7
23. ⊥    ¬-elimination, 21, 22
24. q ↔ s    ⊥-elimination, 23
25. q ↔ s    ∨-elimination, 20, 19, 24
26. ((p ∧ q) ∧ (r ∧ s)) → (q ↔ s)    →-introduction, 3–25'''
)

print(extracted_proofs)
#%%
[int(x[1]) for x in re.findall(r"(–|, )(\d+)", "1564bjnlk –111  –112, 3")]

text = "1564bjnlk –111  –112, 3"
def replace_nth_number(text: str, n: int, x: int, pattern: str = r"(–|, )(\d+)") -> str:
    counter = {"i": 0}
    def repl(match):
        i = counter["i"]
        counter["i"] += 1
        if i == n:
            return match.group(1) + str(x)
        return match.group(0)

    return re.sub(pattern, repl, text)
replace_nth_number(text, 1, 2)
for i in range(1,10):
    print(i)
#%%
def simpliffy_with_context(proof,context):
    def find_line_idx(idx, lines):
        for i in range(len(lines)):
            if lines[i].split(".")[0] == str(idx):
                return i

    parsedProof = parseProof(proof,context)
    proof_text = proof.splitlines()
    for i in parsedProof.keys():
        if parsedProof[i].LP.conclusion in context:
            if parsedProof[i].LP.assumptions.additional_context == []:
                line_conclusion_idx = find_line_idx(i,proof_text)
                new_line = str(i)+". "+ to_infix(parsedProof[i].LP.conclusion)+"    context, 0"
                proof_text[line_conclusion_idx] = new_line
            else:
                line_conclusion_idx = find_line_idx(i,proof_text)
                line_assumption_idx = -1
                for j in parsedProof[i].args_keys:
                    if int(i) > int(j) and parsedProof[i].LP.assumptions == parsedProof[j].LP.assumptions:
                        line_assumption_idx = j
                        break
                if line_assumption_idx != -1:
                    new_line = str(i)+". "+ to_infix(parsedProof[i].LP.conclusion)+"    contextWeak, "+str(line_assumption_idx)
                    proof_text[line_conclusion_idx] = new_line
    ans = ""
    for i in proof_text:
        ans += i
        ans += "\n"
    ans = ans[:-1]
    parsedProof = parseProof(ans,base_context = context)
    important_lines = [list(parsedProof.keys())[-1]]
    def next_elems():

        ans = []
        for i in parsedProof.keys():
            if not i in important_lines:
                for j in  important_lines:
                    if i in parsedProof[j].args_keys:
                        ans.append(i)
                        break

        return ans
    next_elems_values = next_elems()
    while next_elems_values != []:
        important_lines += next_elems_values
        next_elems_values = next_elems()
    important_lines.sort()
    proof = ans.splitlines()
    ans = ""

    for i in proof:
        idx = int(i.split(".")[0])
        if idx in important_lines:
            ans += i
            ans += "\n"
    ans = ans[:-1]

    def replace_indexed_numbers(ls: List[str], li: List[int]) -> List[str]:
        mapping = {int(li[i]): str(i+1) for i in range(len(li))}
        if not mapping:
            return ls[:]
        alts = "|".join(
            re.escape(str(n)) for n in sorted(mapping.keys(), key=lambda x: (-len(str(x)), x))
        )
        pattern = re.compile(
            rf'(?:(, |–)({alts})(?!\d))|(?:(?<!\d)({alts})(?!\d)(?=\.))'
        )

        def repl(m: re.Match) -> str:
            if m.group(2) is not None:  # gałąź z prefiksem
                prefix = m.group(1)
                num = m.group(2)
                return prefix + mapping[int(num)]
            else:  # gałąź z kropką po liczbie
                num = m.group(3)
                return mapping[int(num)]

        ans_lines = [pattern.sub(repl, s) for s in ls]
        ans = "\n".join(ans_lines)
        return ans
    return replace_indexed_numbers(ans.splitlines(),important_lines)
#%%
def give_all_extraction_text(proof:str,BaseContext = []):
    parsedProof = parseProof(proof,base_context = BaseContext)
    ANS = ""
    for i in parsedProof.keys():
        goal = parsedProof[i].LP
        temporary_context = deepcopy(BaseContext)
        for j in goal.assumptions.base_context:
            if not j in BaseContext:
                temporary_context.append(j)
        for j in goal.assumptions.additional_context:
            if not j in BaseContext:
                temporary_context.append(j)
        goal.assumptions.base_context = temporary_context#?
        goal.assumptions.additional_context = []#?
        extracted = extract_proof(proof,goal,temporary_context)
        parseProof(extracted,temporary_context)
        extracted = simpliffy_with_context(extracted,temporary_context)
        parseProof(extracted,base_context = temporary_context)
        ans = "Prove that: " + to_infix(goal.conclusion)
        if temporary_context != []:
            ans += "\nassuming that: "
            for j in temporary_context:
                ans += to_infix(j)
                ans += ",\n"
            ans = ans[:-2]
        ans += ("\n"+extracted)
        ANS += ans
        ANS += "\n\n"
    return ANS
print(proof)

#%%
extracted_proofs = give_all_extraction_text('''1. (p → q) ∧ p    assumption
2. p → q    ∧-elimination1, 1
3. (p ∧ q) ∧ (r ∧ s)    assumption
4. p ∧ q    ∧-elimination1, 3
5. r ∧ s    ∧-elimination2, 3
6. q    ∧-elimination2, 4
7. s    ∧-elimination2, 5
8. q    assumption
9. s    weakening, 8, 7
10. s    assumption
11. q    weakening, 10, 6
12. q ↔ s    ↔-introduction, 9, 11
13. q ∨ ¬q    TND
14. ¬q    assumption
15. q    weakening, 14, 6
16. ⊥    ¬-elimination, 14, 15
17. ⊥    weakening, 7, 16
18. q ↔ s    ⊥-elimination, 17
19. q ↔ s    ∨-elimination, 13, 12, 18'''
)

print(extracted_proofs)

#%%
proof = '''3. (p ∧ q) ∧ (r ∧ s)   context, 0
4. p ∧ q    ∧-elimination1, 3
5. r ∧ s    ∧-elimination2, 3
6. q    ∧-elimination2, 4
7. s   context, 0
8. q    assumption
9. s   context, 0
10. s   context, 0
11. q    weakening, 10, 6'''

'''12. q ↔ s    ↔-introduction, 9, 11'''

c = [parse_infix("s"),parse_infix("(p∧q)∧(r∧s)")]
parseProof(proof,base_context = c)
#%%
('''1. (p → q) ∧ p    assumption
2. p → q    ∧-elimination1, 1
3. (p ∧ q) ∧ (r ∧ s)    assumption
4. p ∧ q    ∧-elimination1, 3
5. r ∧ s    ∧-elimination2, 3
6. q    ∧-elimination2, 4
7. s    ∧-elimination2, 5
8. q    assumption
9. s    weakening, 8, 7
10. s    assumption
11. q    weakening, 10, 6
12. q ↔ s    ↔-introduction, 9, 11
13. q ∨ ¬q    TND
14. ¬q    assumption
15. q    weakening, 14, 6
16. ⊥    ¬-elimination, 14, 15
17. ⊥    weakening, 7, 16
18. q ↔ s    ⊥-elimination, 17
19. q ↔ s    ∨-elimination, 13, 12, 18'''
)

print(extracted_proofs)
#%%
def check_proof_with_assumptions(proof,debug = False):
    proof = proof.splitlines()
    thesis_conclusion = parse_infix(proof[0][12:])
    base_context = []
    if proof[1][0] == "a":
        if proof[1][-1] == ",":
            base_context.append(parse_infix(proof[1][15:-1]))
            j = 2
            while proof[j][0] != "1":
                if proof[j][-1] == ",":
                    base_context.append(parse_infix(proof[j][:-1]))
                else:
                    base_context.append(parse_infix(proof[j]))
                j += 1
        else:
            base_context.append(parse_infix(proof[1][15:]))
    proof = "\n".join(proof[1+len(base_context):])
    parsedProof = parseProof(proof,base_context)
    if debug == True:
        print(parsedProof)

    if parsedProof[len(parsedProof)].LP != LittleProblem(Context(base_context,[]) , thesis_conclusion):
        raise TypeError("Bad proof")
    return parsedProof
#%%

#with open("new_corpus_proving2.txt", "r", encoding="utf-8") as f:

with open("proofs_normalised.txt", "r", encoding="utf-8") as f:
    text = f.read()
text = [p.strip() for p in re.split(r'\n\s*\n', text.strip()) if p.strip()]

#%%
poofs = []

'''
for i in tqdm(range(len(text))):
    proof_with_goal = text[i]
    proof = "\n".join(proof_with_goal.splitlines()[1:])
    proofs_extracted_text = give_all_extraction_text(proof)
    proofs_extracted = [p.strip() for p in re.split(r'\n\s*\n', proofs_extracted_text.strip()) if p.strip()]
    for j in proofs_extracted:
        proofs.append(j)
    for j in range(len(proofs_extracted)):
        print(proofs_extracted[j])
        print()
        check_proof_with_assumptions(proofs_extracted[j])
'''

import re
from concurrent.futures import ProcessPoolExecutor
from itertools import chain
from tqdm.auto import tqdm


def _extract_and_check_one(proof_with_goal):
    proof = "\n".join(proof_with_goal.splitlines()[1:])
    proofs_extracted_text = give_all_extraction_text(proof)
    proofs_extracted = [
        p.strip()
        for p in re.split(r'\n\s*\n', proofs_extracted_text.strip())
        if p.strip()
    ]

    # walidacja
    for p in proofs_extracted:
        check_proof_with_assumptions(p)

    return proofs_extracted


poofs = []
'''
with ProcessPoolExecutor() as ex:
    results = list(tqdm(ex.map(_extract_and_check_one, text), total=len(text)))

poofs = list(chain.from_iterable(results))
'''
#%%
proofs = []
'''
for i in tqdm(results,total = len(results)):
    proofs += i

'''
#%%
len(proofs)
#%%
def replace_one_idx(proof, line_number, number_in_line, new_number):#numery linii numeruję od 1, numery w linii od 0
    def line_idx(line):
        return int(re.match(r"\d+", s).group())
    proof = proof.splitlines()
    def replace_nth_number(text: str, n: int, x: int, pattern: str = r"(–|, )(\d+)") -> str:
        counter = {"i": 0}

        def repl(match):
            i = counter["i"]
            counter["i"] += 1
            if i == n:
                return match.group(1) + str(x)
            return match.group(0)
        return re.sub(pattern, repl, text)
    for i in range(len(proof)):
        if proof[i].startswith(str(line_number) + ". "):
            proof[i] = replace_nth_number(proof[i], number_in_line, new_number)
    return "\n".join(proof)


def replace_one_number_by_smallest_number(proof,line_number,number_in_line):
    max_iter = len(proof.splitlines())
    for i in range(0,max_iter+1):
        proof = replace_one_idx(proof,line_number,number_in_line,i)
        try:
            check_proof_with_assumptions(proof)
            return proof
        except:
            pass


def replace_all_number_by_smallest_number(proof):
    number_of_numbers = []
    proof_sole = ""
    proof_splited = proof.splitlines()
    for i in range(len(proof_splited)):
        if proof_splited[i][0] in ["1","2","3","4","5","6","7","8","9"]:
            proof_sole += proof_splited[i]
            proof_sole += "\n"
    proof_sole = proof_sole[:-1]

    proof_splited = proof_sole.splitlines()
    for i in proof_splited:
        number_of_numbers.append(len([x for x in re.findall(r"(–|, )(\d+)", i)]))
    for i in range(len(proof_splited),0,-1):
        for j in range(number_of_numbers[i-1]):
            proof = replace_one_number_by_smallest_number(proof,i,j)
    return proof


proof = '''Prove that: p → q
assuming that: p → q
1. p → q    context, 0'''

check_proof_with_assumptions(proof)
print(replace_one_number_by_smallest_number(proof,3,0))
print(replace_all_number_by_smallest_number(proof))


#%%
'''
with open("NEW_CORPUS_PROVING.txt", "w", encoding="utf-8") as f:
    f.write(bp)

with open("NEW_CORPUS_PROVING.txt", "r", encoding="utf-8") as f:
    text = f.read()

proofs = [p.strip() for p in re.split(r'\n\n', text.strip()) if p.strip()]
'''
#%%
'''
from concurrent.futures import ProcessPoolExecutor
from tqdm.auto import tqdm
import os

with ProcessPoolExecutor(max_workers=os.cpu_count()) as executor:
    proofs_with_optimized_numbers = list(
        tqdm(
            executor.map(
                replace_all_number_by_smallest_number,
                proofs, #text
                chunksize=320
            ),
            total=len(proofs)
        )
    )
'''
#%%
'''
different = 0
for i in range(len(text)):
    if text[i] != proofs_with_optimized_numbers[i]:
        different += 1
print(different/len(text))
'''
#%%
'''
def is_taken_from_context(proof):
    proofParsed = check_proof_with_assumptions(proof)
    base_context = proofParsed[1].LP.assumptions.base_context
    goal = proofParsed[len(proofParsed)].LP.conclusion
    if  goal in base_context:
        return True
    else:
        return False

proofs_without_trivial = []

for i in tqdm(range(len(proofs_with_optimized_numbers))):
    if not is_taken_from_context(proofs_with_optimized_numbers[i]):
        proofs_without_trivial.append(proofs_with_optimized_numbers[i])



from concurrent.futures import ProcessPoolExecutor
from tqdm.auto import tqdm


def is_taken_from_context(proof):
    proofParsed = check_proof_with_assumptions(proof)
    base_context = proofParsed[1].LP.assumptions.base_context
    goal = proofParsed[len(proofParsed)].LP.conclusion
    return goal in base_context


with ProcessPoolExecutor(max_workers=15) as ex:
    mask = list(tqdm(
        ex.map(is_taken_from_context, proofs_with_optimized_numbers, chunksize=50),
        total=len(proofs_with_optimized_numbers)
    ))

proofs_without_trivial = [
    proof
    for proof, taken in zip(proofs_with_optimized_numbers, mask)
    if not taken
]
'''
#%%
'''
def remove_extra_lines_at_the_end(proof):
    parsedProof = check_proof_with_assumptions(proof)
    smallest_last_idx = len(parsedProof)
    for i in parsedProof.keys():
        if parsedProof[i].LP == parsedProof[smallest_last_idx].LP:
            if i < smallest_last_idx:
                smallest_last_idx = i
    ans = ""
    splitted_proof = proof.splitlines()
    current_idx = 0
    for i in range(len(splitted_proof)):
        ans += splitted_proof[i]
        if current_idx >= 1:
            current_idx += 1
        if splitted_proof[i][0] == "1" and current_idx == 0:
            current_idx += 1
        if current_idx == smallest_last_idx:
            check_proof_with_assumptions(ans)
            return ans
        ans += "\n"



proofs_without_extra_lines_at_the_end = []

for i in tqdm(range(len(proofs_without_trivial))):
    proofs_without_extra_lines_at_the_end.append(remove_extra_lines_at_the_end(proofs_without_trivial[i]))
'''
#%%
from concurrent.futures import ProcessPoolExecutor
from tqdm.auto import tqdm
'''

def remove_extra_lines_at_the_end(proof):
    parsedProof = check_proof_with_assumptions(proof)
    smallest_last_idx = len(parsedProof)

    for i in parsedProof.keys():
        if parsedProof[i].LP == parsedProof[smallest_last_idx].LP:
            if i < smallest_last_idx:
                smallest_last_idx = i

    ans = ""
    splitted_proof = proof.splitlines()
    current_idx = 0

    for i in range(len(splitted_proof)):
        ans += splitted_proof[i]

        if current_idx >= 1:
            current_idx += 1

        if splitted_proof[i][0] == "1" and current_idx == 0:
            current_idx += 1

        if current_idx == smallest_last_idx:
            check_proof_with_assumptions(ans)
            return ans

        ans += "\n"


with ProcessPoolExecutor(max_workers=30) as ex:
    proofs_without_extra_lines_at_the_end = list(
        tqdm(
            ex.map(remove_extra_lines_at_the_end, proofs_without_trivial, chunksize=50),
            total=len(proofs_without_trivial)
        )
    )
'''
#%%
def extract_proof_with_assumptions(proof):
    proof_splitted = proof.splitlines()
    ans = ""
    for i in range(len(proof_splitted)):
        if proof_splitted[i][0] == '1':
            break
        ans += proof_splitted[i]
        ans += "\n"
    neighbours = dict()
    line_text = dict()
    for i in range(len(proof_splitted)):
        if proof_splitted[i][0] in ['1','2','3','4','5','6','7','8','9']:
            idx = int(re.findall(r"(\d+)(\.)",proof_splitted[i])[0][0])
            line_text[idx] = proof_splitted[i]
            neighbours[idx] = [int(x[1]) for  x  in re.findall(r"(–|, )(\d+)",proof_splitted[i])]
            neighbours[idx] = [x for x in neighbours[idx] if x != 0]
    idxs = {len(neighbours)}
    new_idxs = {len(neighbours)}
    while new_idxs != set():
        i = random.choice(list(new_idxs))
        new_idxs.remove(i)
        for j in neighbours[i]:
            if not j in idxs:
                idxs.add(j)
                new_idxs.add(j)
    for i in range(len(proof_splitted)):
        if proof_splitted[i][0] in ['1','2','3','4','5','6','7','8','9']:
            idx = int(re.findall(r"(\d+)(\.)",proof_splitted[i])[0][0])
            if idx in idxs:
                ans += line_text[idx]
                ans += "\n"
    ans = ans[:-1]
    old_numbers = sorted(list(idxs))
    new_numbers = list(range(1,len(old_numbers)+1))
    def replace_selected_numbers(s, old_numbers, new_numbers):
        if len(old_numbers) != len(new_numbers):
            raise ValueError("old_numbers i new_numbers muszą mieć tę samą długość")
        mapping = {str(old): str(new) for old, new in zip(old_numbers, new_numbers)}
        pattern = r'(?:(?<=–)\d+|(?<=, )\d+|\d+(?=\.))'
        def repl(match):
            num = match.group(0)
            return mapping.get(num, num)
        return re.sub(pattern, repl, s)
    ans = replace_selected_numbers(ans, old_numbers, new_numbers)
    check_proof_with_assumptions(ans)
    return ans




proof = replace_all_number_by_smallest_number('''Prove that: p → ((z ↔ (d ∧ z)) ∨ p)
1. (p → q) ∧ p    assumption
2. p → q    ∧-elimination1, 1
3. p → ¬p    assumption
4. p    assumption
5. ¬p    →-elimination, 3, 4
6. ⊥    ¬-elimination, 5, 4
7. ¬p    ¬-introduction, 4, 6
8. p ∧ ¬p    assumption
9. p    ∧-elimination1, 8
10. ¬p    assumption
11. p    assumption
12. ¬p    context, 10
13. ⊥    ¬-elimination, 12, 11
14. ¬p    assumption
15. ¬¬¬p    assumption
16. ¬p    ¬¬-elimination, 15
17. ⊥    ¬-elimination, 14, 9
18. p    RAA, 16–13
19. p    RAA, 7–17
20. (z ↔ (d ∧ z)) ∨ p    ∨-introduction2, 18
21. p → ((z ↔ (d ∧ z)) ∨ p)    →-introduction, 19–20''')
print(proof)
print()
print(extract_proof_with_assumptions(proof))
#%%
'''
proofs_extracted = []

for i in tqdm(range(len(proofs_without_extra_lines_at_the_end))):
    proofs_extracted.append(extract_proof_with_assumptions(proofs_without_extra_lines_at_the_end[i]))
'''
#%%
from concurrent.futures import ProcessPoolExecutor
from tqdm.auto import tqdm

'''
with ProcessPoolExecutor(max_workers=30) as ex:
    proofs_extracted = list(
        tqdm(
            ex.map(
                extract_proof_with_assumptions,
                proofs_without_extra_lines_at_the_end,
                chunksize=50
            ),
            total=len(proofs_without_extra_lines_at_the_end)
        )
    )
'''
#%%
'''
TEXT = "\n\n".join(proofs_extracted)

with open("NEW_CORPUS_PROVING.txt", "w", encoding="utf-8") as f:
    f.write(TEXT)
'''
#%%
'''
TEXT = ""
for i in tqdm(range(len(text))):
    proof = "\n".join(text[i].splitlines()[1:])
    TEXT += give_all_extraction_text(proof).strip("\n")
    TEXT += "\n\n"

with open("new_corpus_proving.txt", "w", encoding="utf-8") as f:
    f.write(TEXT)
'''
'''
from multiprocessing import Pool
from tqdm.auto import tqdm

def _extract_one(proof_with_goal):
    proof = "\n".join(proof_with_goal.splitlines()[1:])
    return give_all_extraction_text(proof).strip("\n")

if __name__ == "__main__":
    with Pool(processes=15) as pool:
        with open("new_corpus_proving.txt", "w", encoding="utf-8") as f:
            for part in tqdm(pool.imap(_extract_one, text, chunksize=1), total=len(text)):
                f.write(part)
                f.write("\n\n")
'''
#%%
'''
with open("new_corpus_proving2.txt", "r", encoding="utf-8") as f:
    text = f.read()

text = text.split("\n\n")

for i in tqdm(range(len(text))):
    check_proof_with_assumptions(text[i])
'''
#%% md
# Finetuning
#%%
'''
with open("NEW_CORPUS_SMASHTosecondTraining.txt") as f:
    text =  f.read()
text.rstrip("\n")
smashes = text.split("\n\n")

smashes_gruped = dict()
for i in tqdm(smashes,total=len(smashes)):
    #print(i)
    #print()
    if i != '':
        key = i.splitlines()[1]
        if key in smashes_gruped.keys():
            smashes_gruped[key].append(i)
        else:
            smashes_gruped[key] = [i]

print(len(text))
'''
#%%
'''
num_of_smashes = 0
for i in smashes_gruped.keys():
    num_of_smashes += len(smashes_gruped[i])
print(num_of_smashes/len(smashes_gruped))
'''
#%%
'''
new_smashes = []
import random
for i in tqdm(range(1000000 * len(smashes_gruped))):
    key = random.choice(list(smashes_gruped.keys()))
    elem = random.choice(smashes_gruped[key])
    new_smashes.append(elem)
finetune_corpus_smash_1  = "\n\n".join(new_smashes)

with open("corpus_smash_finetune1.txt", "w", encoding="utf-8") as f:
    f.write(finetune_corpus_smash_1)
'''
#%%

#with open("corpus_smash_finetune1.txt", "w", encoding="utf-8") as f:
#    f.write(finetune_corpus_smash_1)
'''
finetune_nanogpt_on_file(
    "corpus_smash_finetune1.txt",
    "out-NEW_CORPUS_SMASH",
    device="cuda",
    batch_size=24,
    block_size=1024,
    max_iters=1000000,
    eval_interval=20,
    learning_rate=0.0001
)
'''
#%%
len('Prove that: ((p ∨ q) → r) → ((p → r) ∨ (q → r))')
#%%
with open("new_corpus_proving2.txt") as f:
    text =  f.read()
text.rstrip("\n")
proves = text.split("\n\n")

narrow_proofs = []

for i in range(len(proves)):
    if len(proves[i].splitlines()[0]) < 50:
        narrow_proofs.append(proves[i])

finetune_corpus_proving_1  = "\n\n".join(narrow_proofs)
'''
with open("corpus_proving_finetune1.txt", "w", encoding="utf-8") as f:
    f.write(finetune_corpus_proving_1)
'''
#%%
'''
finetune_nanogpt_on_file(
    "corpus_smash_finetune1.txt",
    "out-new_corpus_smash",
    device="cuda",
    batch_size=24,
    block_size=1024,
    max_iters=170000,
    eval_interval=20,
    learning_rate=0.01
)
finetune_nanogpt_on_file(
    "corpus_smash_finetune1.txt",
    "out-new_corpus_smash",
    device="cuda",
    batch_size=24,
    block_size=1024,
    max_iters=190000,
    eval_interval=20,
    learning_rate=0.001
)
finetune_nanogpt_on_file(
    "corpus_smash_finetune1.txt",
    "out-new_corpus_smash",
    device="cuda",
    batch_size=24,
    block_size=1024,
    max_iters=230000,
    eval_interval=20,
    learning_rate=0.0001
)
finetune_nanogpt_on_file(
    "corpus_smash_finetune1.txt",
    "out-new_corpus_smash",
    device="cuda",
    batch_size=24,
    block_size=1024,
    max_iters=300000,
    eval_interval=20,
    learning_rate=0.00001
)
'''
#%% md
# STRATEGIA 1 i 2

#%%

def FreeVariablesFormula(x):
    if not isinstance(x, Formula):
        raise TypeError("Not Formula")
    if isinstance(x, Truth) or isinstance(x, Lie):
        return []
    elif isinstance(x, Atom):
        return [x]
    else:
        ans = []
        for i in x.Interior:
            ans = list(set(ans).union(set(FreeVariablesFormula(i))))
        return ans

def FreeVariablesLP(x):
    if not isinstance(x, LittleProblem):
        raise TypeError("Bad argument")
    ans = FreeVariablesFormula(x.conclusion)
    for i in x.assumptions.base_context:
        ans = list(set(ans).union(set(FreeVariablesFormula(i))))
    for i in x.assumptions.additional_context:
        ans = list(set(ans).union(set(FreeVariablesFormula(i))))
    return ans
PROJECT_ROOT = Path.home() / "PycharmProjects" / "Magisterka"
PKG_ROOT = PROJECT_ROOT / "nanoGPT-20251228T135841Z-3-001"
sys.path.insert(0, str(PKG_ROOT))
sys.path.insert(0, str(PROJECT_ROOT))
print(sys.path)
sys.path.insert(0, str(PROJECT_ROOT))
from nanoGPT.model import GPTConfig, GPT
print(GPT)
from dataclasses import dataclass
from typing import Callable
import torch
@dataclass
class NanoGPTBundle:
    model: GPT
    encode: Callable[[str], list[int]]
    device: str
    device_type: str
    ptdtype: torch.dtype

from dataclasses import dataclass
from typing import Callable, Optional
import os
import pickle
import torch
import tiktoken



@dataclass
class NanoGPTBundle:
    model: GPT
    encode: Callable[[str], list[int]]
    decode_token: Callable[[int], str]         # <-- NOWE: id -> tekst tokenu
    decode_ids: Callable[[list[int]], str]     # <-- NOWE: lista id -> tekst
    device: str
    device_type: str
    ptdtype: torch.dtype


def load_nanogpt_bundle(
    out_dir: str,
    *,
    device: Optional[str] = None,
    dtype: Optional[str] = None,
) -> NanoGPTBundle:
    if device is None:
        device = "cuda" if torch.cuda.is_available() else "cpu"
    requested_device = device
    requested_device_type = "cuda" if "cuda" in requested_device else "cpu"

    if dtype is None:
        if requested_device_type == "cuda" and torch.cuda.is_bf16_supported():
            dtype = "bfloat16"
        elif requested_device_type == "cuda":
            dtype = "float16"
        else:
            dtype = "float32"

    ptdtype = {"float32": torch.float32, "float16": torch.float16, "bfloat16": torch.bfloat16}[dtype]
    project_root = os.path.abspath(globals().get("PROJECT_ROOT", os.getcwd()))
    raw_pkg_roots = [
        globals().get("PKG_ROOT"),
        os.path.join(project_root, "nanoGPT-20251228T135841Z-3-001", "nanoGPT"),
        os.path.join(project_root, "nanoGPT"),
    ]
    pkg_roots = []
    for root in raw_pkg_roots:
        if not root:
            continue
        root_abs = os.path.abspath(os.path.expanduser(str(root)))
        if root_abs in pkg_roots:
            continue
        if os.path.exists(os.path.join(root_abs, "train.py")):
            pkg_roots.append(root_abs)
    if not pkg_roots:
        raise FileNotFoundError("Nie znaleziono katalogu nanoGPT z train.py.")

    out_dir_path = os.path.expanduser(out_dir)
    ckpt_candidates = []
    if os.path.isabs(out_dir_path):
        ckpt_candidates.append(out_dir_path if out_dir_path.endswith("ckpt.pt") else os.path.join(out_dir_path, "ckpt.pt"))
    else:
        for root in pkg_roots:
            base = os.path.join(root, out_dir_path)
            ckpt_candidates.append(base if out_dir_path.endswith("ckpt.pt") else os.path.join(base, "ckpt.pt"))
        project_base = os.path.join(project_root, out_dir_path)
        ckpt_candidates.append(project_base if out_dir_path.endswith("ckpt.pt") else os.path.join(project_base, "ckpt.pt"))

    ckpt_path = next((p for p in ckpt_candidates if os.path.exists(p)), None)
    if ckpt_path is None:
        raise FileNotFoundError(
            "Nie znaleziono checkpointu. Sprawdzane sciezki: " + "; ".join(ckpt_candidates)
        )

    real_ckpt_path = os.path.realpath(ckpt_path)
    ckpt_pkg_root = next(
        (root for root in pkg_roots if os.path.commonpath([real_ckpt_path, os.path.realpath(root)]) == os.path.realpath(root)),
        None,
    )
    if ckpt_pkg_root is None:
        inferred_root = os.path.dirname(os.path.dirname(real_ckpt_path))
        if os.path.exists(os.path.join(inferred_root, "train.py")):
            ckpt_pkg_root = inferred_root
        else:
            ckpt_pkg_root = pkg_roots[0]

    checkpoint = torch.load(real_ckpt_path, map_location="cpu", weights_only=False)

    gptconf = GPTConfig(**checkpoint["model_args"])
    model = GPT(gptconf)

    state_dict = checkpoint["model"]
    unwanted_prefix = "_orig_mod."
    for k in list(state_dict.keys()):
        if k.startswith(unwanted_prefix):
            state_dict[k[len(unwanted_prefix):]] = state_dict.pop(k)

    model.load_state_dict(state_dict)
    active_device = requested_device
    active_device_type = requested_device_type
    active_ptdtype = ptdtype
    try:
        model.eval().to(active_device)
    except Exception as e:
        msg = str(e)
        if requested_device_type == "cuda" and ("CUDA error" in msg or "device-side assert triggered" in msg):
            print("Uwaga: CUDA jest w blednym stanie. Przelaczam model na CPU. Zrestartuj kernel, aby wrocic na CUDA.")
            active_device = "cpu"
            active_device_type = "cpu"
            active_ptdtype = torch.float32
            model.eval().to(active_device)
        else:
            raise

    # --- encoder/decoder ---
    encode = None
    decode_token = None
    decode_ids = None

    dataset = checkpoint.get("config", {}).get("dataset")
    model_vocab_size = checkpoint.get("model_args", {}).get("vocab_size")
    if dataset:
        meta_path = os.path.join(ckpt_pkg_root, "data", dataset, "meta.pkl")
        if os.path.exists(meta_path):
            with open(meta_path, "rb") as f:
                meta = pickle.load(f)
            stoi, itos = meta["stoi"], meta["itos"]

            def encode(s: str) -> list[int]:
                return [stoi[c] for c in s]

            def decode_token(i: int) -> str:
                return itos[i]

            def decode_ids(ids: list[int]) -> str:
                return "".join(itos[i] for i in ids)

    if encode is None:
        if model_vocab_size not in (50257, 50304):
            raise FileNotFoundError(
                f"Nie znaleziono meta.pkl dla datasetu={dataset!r} (oczekiwano w {os.path.join(ckpt_pkg_root, 'data', str(dataset), 'meta.pkl')}). "
                f"Model ma vocab_size={model_vocab_size}, wiec fallback do tiktoken (GPT-2) bylby niepoprawny."
            )
        enc = tiktoken.get_encoding("gpt2")

        def encode(s: str) -> list[int]:
            return enc.encode(s, allowed_special={"<|endoftext|>"})

        def decode_token(i: int) -> str:
            return enc.decode([i])

        def decode_ids(ids: list[int]) -> str:
            return enc.decode(ids)

    return NanoGPTBundle(
        model=model,
        encode=encode,
        decode_token=decode_token,
        decode_ids=decode_ids,
        device=active_device,
        device_type=active_device_type,
        ptdtype=active_ptdtype,
    )

bundle_proving = load_nanogpt_bundle("out-NEW_CORPUS_PROVING")
bundle_smashing = load_nanogpt_bundle("out-NEW_CORPUS_SMASH")

#%%
import numpy as np
import torch
from typing import Optional
from tqdm import tqdm


@torch.no_grad()
def next_token_distribution_from_bundle(
    bundle: NanoGPTBundle,
    prompt: str,
    *,
    temperature: float = 1.0,
    top_k: Optional[int] = None,
) -> np.ndarray:
    x = torch.tensor(bundle.encode(prompt), dtype=torch.long, device=bundle.device)[None, :]

    with torch.autocast(
        device_type=bundle.device_type,
        dtype=bundle.ptdtype,
        enabled=(bundle.device_type == "cuda" and bundle.ptdtype != torch.float32),
    ):
        logits, _ = bundle.model(x)

    # logits: [1, T, V]
    next_logits = logits[0, -1, :] / temperature

    if top_k is not None:
        values, indices = torch.topk(next_logits, top_k)
        probs = torch.softmax(values, dim=-1)  # <-- TU powstają prawdopodobieństwa (dla top_k)
        return np.array([(int(i), float(p)) for i, p in zip(indices, probs)], dtype=float)

    probs = torch.softmax(next_logits, dim=-1)  # <-- TU powstają prawdopodobieństwa (dla całego vocab)
    return np.array([(int(i), float(probs[i])) for i in range(probs.shape[0])], dtype=float)




import random
import numpy as np

def random_next_token(
    bundle: NanoGPTBundle,
    prompt: str,
    verbose: bool = False,
    temperature: float = 1.0,
    randomize: float = 0.0,
    acceptable_tokens=None,
):
    source = next_token_distribution_from_bundle(
        bundle,
        prompt,
        temperature=temperature
    )
    token_ids = source[:,0]
    probs = source[:,1]
    decoded_tokens = [bundle.decode_token(tok_id) for tok_id in token_ids]
    # filtrowanie po acceptable_tokens
    # jeśli acceptable_tokens is None albo zawiera None, to wszystko dozwolone
    if acceptable_tokens is not None and None not in acceptable_tokens:
        acceptable_tokens_set = set(acceptable_tokens)

        filtered = [
            (tok_id, prob, tok_str)
            for tok_id, prob, tok_str in zip(token_ids, probs, decoded_tokens)
            if tok_str in acceptable_tokens_set
        ]

        if len(filtered) == 0:
            raise ValueError("Żaden token nie pasuje do acceptable_tokens")

        token_ids = np.array([x[0] for x in filtered], dtype=int)
        probs = np.array([x[1] for x in filtered], dtype=float)

        decoded_tokens = [x[2] for x in filtered]

        prob_sum = probs.sum()
        if prob_sum <= 0:
            raise ValueError("Suma prawdopodobieństw po filtracji wynosi 0")
        probs = probs / prob_sum

    if verbose:
        verbose_table = []
        for tok_str, prob in zip(decoded_tokens, probs):
            verbose_table.append([tok_str, prob])
        verbose_table.sort(key=lambda x: x[1], reverse=True)
        for i in verbose_table[:10]:
            print(i)

    return bundle.decode_token(random.choices(token_ids, weights=probs)[0])


def last_token_probability_from_bundle(
    bundle: NanoGPTBundle,
    prompt: str,
    *,
    temperature: float = 1.0,
    top_k: Optional[int] = None,
):
    distribution = next_token_distribution_from_bundle(bundle, prompt[:-1], temperature=temperature, top_k=top_k)
    key = bundle.encode(prompt[-1])[0]
    return distribution[key][1]
prompt = "Pro"
print(next_token_distribution_from_bundle(bundle_proving,prompt,temperature=1))
random_next_token(bundle_proving, prompt, temperature=1.0, randomize=0.0, acceptable_tokens=['v','e'])
#%%
print("1","2")
#%%
def next_line(
    bundle: NanoGPTBundle,
    prompt: str,
    *,
    temperature: float = 1.0,
    temperature_begin_line : float = 10,
    multiplier_begin_line : float = 0.66666666,
    top_k: Optional[int] = None,
    is_first_proof_line = False
)->str:
    ans = prompt
    next_token = None
    if is_first_proof_line:
        next_token = "1"
        ans += next_token

    while next_token != "\n":
        next_token = random_next_token(bundle,ans,temperature=temperature)
        ans += next_token
    return ans.splitlines()[-1]
prompt = '''Smash:  ⊢ (a ∧ b) → (¬a → c)
'''

#%%
def next_line_smart(
        bundle: NanoGPTBundle,
        prompt: str,
        *,
        temperature: float = 1.0
):
    next_token = None
    prompt = prompt.rstrip("\n")
    prompt = prompt.rstrip(" ")
    prompt_splitted = prompt.splitlines()
    if prompt[0] == 'P':
        formulas = []
        formulas.append(parse_infix(prompt_splitted[0][11:]))
        acceptable_vars = None
        if len(prompt_splitted) == 1:
            acceptable_vars = formula_free_variables(formulas[0])
            acceptable_vars = [to_infix(x) for x in acceptable_vars]
        elif prompt_splitted[1][0] == 'a':
            if prompt_splitted[1][-1] == ',':
                formulas.append(parse_infix(prompt_splitted[1][14:-1]))
            else:
                formulas.append(parse_infix(prompt_splitted[1][14:]))
            for i in range(2,len(prompt_splitted)):
                if prompt_splitted[i][0] != '1':
                    if prompt_splitted[i][-1] == ',':
                        formulas.append(parse_infix(prompt_splitted[i][:-1]))
                    else:
                        formulas.append(parse_infix(prompt_splitted[i]))
                else:
                    break
        ans = ''
        if not prompt_splitted[-1][0] in  ['1','2','3','4','5','6','7','8','9']:
            ans = "1. "
        else:
            idx = str(int(re.findall(r"\d+",prompt_splitted[-1])[0])+1)
            ans = idx + ". "
        old_ans = ans
        if acceptable_vars is None:
            acceptable_vars = free_variables_LP(LittleProblem(Context(formulas,[]),Truth()))
            acceptable_vars = [to_infix(x) for x in acceptable_vars]

        acceptable_tokens = acceptable_vars + [' ','¬','∨','∧','→','↔','(',')','⊤','⊥']
        while not (ans[-1] == ' ' and ans[-2] == ' '):
            next_token = random_next_token(bundle,prompt+"\n"+ans,temperature=temperature)
            if next_token in acceptable_tokens:
                ans += next_token
            #else:
            #    ans = old_ans
        ans += "  "
        while next_token != "\n":
            next_token = random_next_token(bundle,prompt+"\n"+ans,temperature=temperature)
            ans+=next_token
        return ans
    if prompt[0] == 'S':
        lp_text = prompt_splitted[0][6:]
        
        acceptable_vars = list(set(findall(r"[a-z]",lp_text)))
        ans = ""
        if len(prompt_splitted) == 1:
            ans = "With: "
            while next_token != '\n':
                next_token = random_next_token(bundle,prompt+"\n"+ans,temperature=temperature)
                ans+=next_token

        if len(prompt_splitted) == 2:
            ans = "To: "
        acceptable_tokens = acceptable_vars + [' ','¬','∨','∧','→','↔','(',')','⊤','⊥',',','⊢','\n']
        old_ans = ans
        while next_token != "\n":
            next_token = random_next_token(bundle,prompt+"\n"+ans,temperature=temperature)
            #print(ans + next_token,";")
            if next_token in acceptable_tokens:
                ans += next_token
            else:
                ans = old_ans
        return ans

prompt = "Smash: ⊢ ((a ∧ b) ∧ ((c ∧ d) ∧ e)) → ((a ∧ d) ∧ e)"

prompt +=("\n" + next_line_smart(bundle_smashing,prompt,temperature=1))
print(prompt)
prompt +=( next_line_smart(bundle_smashing,prompt,temperature=1))
print(prompt)
#%%
def is_ready_to_check_smash(prompt):
    if not isinstance(prompt,str):
        raise TypeError("Bad argument")
    prompt = prompt.rstrip("\n")
    prompt = prompt.splitlines()
    if len(prompt) < 3:
        return False
    else:
        return prompt[-1][-1] != ","

prompt = '''Smash: ¬¬k ⊢ k ∧ k
With: ConjunctionIntroduction
To: ¬¬k ⊢ k,
¬¬k ⊢ k'''
is_ready_to_check_smash(prompt)
prompt
#%%
def silliest_generate_smash(bundle : NanoGPTBundle,
                           prompt : str,
                            max_iter : int = 50):
    c = True
    for i in range(max_iter) :
        #print(i)
        while not is_ready_to_check_smash(prompt):
            try:
                nl = next_line_smart(bundle,prompt)
                prompt = prompt  + "\n" + nl
                prompt = prompt.rstrip("\n")
                print(prompt)
                print()
            except:
                pass
        try:
            print(prompt)
            print()
            ans_structure = check_smash_from_text(prompt)
            break
        except Exception:
            prompt = prompt.splitlines()[0]

    return prompt
prompt = "Smash: (a ∧ b) ∧ ((c ∧ d) ∧ e) ⊢ (a ∧ d) ∧ e"
bundle_smash = load_nanogpt_bundle("out-NEW_CORPUS_SMASH")
silliest_generate_smash(bundle_smash,prompt)

#%%
prompt = '''Smash: ⊢ (a ∧ b) ∧ ((c ∧ d) ∧ e) → ((a ∧ d) ∧ e)
With: ImplicationIntroduction
To: (a ∧ b) ∧ ((c ∧ d) ∧ e) ⊢ (a ∧ d) ∧ e'''

check_smash_from_text(prompt)
#%%
#pr = None
def silliest_generate_proof(bundle : NanoGPTBundle,
                            prompt : str,
                            temperature : float = 1.0,
                            max_new_lines : int = 1,
                            max_failed_attempts : int = 1000,
                            is_first_proof_line = False):
    global pr
    pr = prompt
    prompt_str = prompt.rstrip("\n") + "\n"  #dodalem
    prompt = [line for line in prompt_str.splitlines() if line.strip() != ""]  #dodalem
    thesis_conclusion = parse_infix(prompt[0][12:])
    base_context = []
    if len(prompt) > 1:
        if prompt[1][0] == "a":
            if prompt[1][-1] == ",":
                base_context.append(parse_infix(prompt[1][15:-1]))
                j = 2
                while j < len(prompt) and prompt[j][0] != "1":
                    if prompt[j][-1] == ",":
                        base_context.append(parse_infix(prompt[j][:-1]))
                    else:
                        base_context.append(parse_infix(prompt[j]))
                    j += 1
            else:
                base_context.append(parse_infix(prompt[1][15:]))
    if thesis_conclusion in base_context:
        ans = ""
        for i in range(len(prompt)):
            if i[0] != "1":
                ans += prompt[i] + "\n"
            else:
                break
        new_line = "1. " + to_infix(thesis_conclusion)+"    context, 0"
        ans += new_line
        check_proof_with_assumptions(ans)
        return ans
    goal = LittleProblem(Context(base_context,[]) , thesis_conclusion)
    acceptable_variables =FreeVariablesLP(goal)
    existing_proof = ""  #dodalem
    for i in range(len(goal.assumptions.base_context)+1,len(prompt)):
        existing_proof += prompt[i] + "\n"  #dodalem
    added_proof = ""  #dodalem
    last_parsed_line = None
    new_lines = 0
    failed_attempts = 0
    #print(to_infix_LP(goal))
    while last_parsed_line != goal and new_lines < max_new_lines:
        #global pr
        #pr = prompt_str + added_proof
        nl =  next_line_smart(bundle,prompt_str+added_proof,temperature=temperature)
        #print([nl],failed_attempts)

        nl= nl.rstrip("\n")
        nl= nl.lstrip("\n")
        #print(nl)
        #print(nl)
        is_first_proof_line = False#dodalem
        #print(nl)
        failed_attempts += 1
        if failed_attempts > max_failed_attempts:
            break
        stripped_nl = nl.strip()
        if stripped_nl == "":
            continue
        if "." not in stripped_nl or not stripped_nl.split(".", 1)[0].isdigit():
            continue
        try:
            temporary_added_proof = added_proof + nl + "\n"  #dodalem
            temporary_proof = existing_proof + temporary_added_proof  #dodalem
            parsedProof = parseProof(temporary_proof[:-1],base_context)
            last_parsed_line = parsedProof[len(parsedProof)].LP
            last_parsed_variables = FreeVariablesLP(last_parsed_line)
            for i in last_parsed_variables:
                if i not in acceptable_variables:
                    raise Exception("Nieprawidlowe zmienne w tym wierszu")
            for i in range(1,len(parsedProof)):
                if last_parsed_line == parsedProof[i].LP:
                    raise(Exception("Repetition"))
            new_lines += 1
            added_proof = temporary_added_proof
            new_lines += 1
            failed_attempts = 0
        except Exception:
            pass
    return prompt_str+added_proof  #dodalem


prompt = '''Prove that: (a ∧ b) → (¬a → c)'''


#print(silliest_generate_proof(bundle_proving,prompt,temperature=0.3,max_new_lines=40,is_first_proof_line=True))
#%%
def prompt_probability_normalised(bundle, prompt,temperature=1,top_k=None):
    temporal_prompt = prompt.splitlines()[0] + "\n"
    ans_unnormalised = 0
    proof = ""
    lines_of_goal = 1
    for i in range(len(prompt.splitlines())):
        if prompt.splitlines()[i][0] == "1":
            lines_of_goal  = i
    for i in prompt.splitlines()[lines_of_goal:]:
        proof += i+"\n"
    for i in proof:
        temporal_prompt += i
        #print(temporal_prompt)
        ans_unnormalised  += np.log(last_token_probability_from_bundle(bundle,temporal_prompt,temperature=temperature,top_k=top_k))
        #print(ans_unnormalised)
    return ans_unnormalised/len(proof)

#X = silliest_generate_proof(bundle_proving,prompt,temperature=0.1,max_new_lines=1)

#print(prompt_probability_normalised(bundle_proving,X))

def soft_max(x):
    return np.exp(x)/np.sum(np.exp(x))

soft_max([1,2])
import re

def int_from_start(s: str):
    m = re.match(r'\d+', s)
    return int(m.group()) if m else None

def is_well_numbered(proof:str):
    for i in range(len(proof.splitlines())):
        if int_from_start(proof.splitlines()[i]) != i+1:
            raise Exception("Nieprawidlowe numerywanie wierszy")
    return True
#%%
prr = None
def find_proof_little_smarter(
    bundle: NanoGPTBundle,
    prompt: str,
    *,
    temperature: float = 1.0,
    max_iter: int = 10000,
    max_failed_attempts: int = 20,
):
    global pr
    #pr = prompt
    def extract_proof_part(full_prompt: str):  #dodalem
        lines = [line for line in full_prompt.splitlines() if line.strip() != ""]  #dodalem
        first_proof_idx = None  #dodalem
        for idx, line in enumerate(lines):  #dodalem
            if int_from_start(line) == 1:  #dodalem
                first_proof_idx = idx  #dodalem
                break  #dodalem
        if first_proof_idx is None:  #dodalem
            return ""  #dodalem
        return "\n".join(lines[first_proof_idx:]) + "\n"  #dodalem
    prompt_str = prompt.rstrip("\n") + "\n"  #dodalem
    prompt = [line for line in prompt_str.splitlines() if line.strip() != ""]  #dodalem
    thesis_conclusion = parse_infix(prompt[0][12:])
    base_context = []
    if len(prompt) > 1:
        if prompt[1][0] == "a":
            if prompt[1][-1] == ",":
                base_context.append(parse_infix(prompt[1][15:-1]))
                j = 2
                while j < len(prompt) and prompt[j][0] != "1":
                    if prompt[j][-1] == ",":
                        base_context.append(parse_infix(prompt[j][:-1]))
                    else:
                        base_context.append(parse_infix(prompt[j]))
                    j += 1
            else:
                base_context.append(parse_infix(prompt[1][15:]))
    goal = LittleProblem(Context(base_context,[]) , thesis_conclusion)
    acceptable_variables =FreeVariablesLP(goal)
    prompts = [prompt_str]
    probabilities_wild = [1.0]
    probabilities = np.array(probabilities_wild)
    I = 0
    while I < max_iter:
        prompt_str = random.choices(prompts,weights=probabilities)[0]
        prompt_str = prompt_str.rstrip("\n") + "\n"  #dodalem
        I += 1
        print(I)
        try:
            global prr
            prr = prompt_str
            new_prompt_str = silliest_generate_proof(bundle,prompt_str,temperature=temperature,max_new_lines=1,max_failed_attempts=max_failed_attempts)
            print(1)
            print("-----------------------------------------------------------------------------------------------------")
            print(prr)
            print("=====================================================================================================")
            print(new_prompt_str)
            print("-----------------------------------------------------------------------------------------------------")
            new_proof = extract_proof_part(new_prompt_str)  #dodalem
            if new_proof == "":  #dodalem
                raise Exception("Brak linii dowodu")  #dodalem
            #print(new_proof)  #dodalem
            #print(new_proof)
            is_well_numbered(new_proof[:-1])

            #print("ok")
            parsedProof = parseProof(new_proof[:-1],base_context)
            if parsedProof[len(parsedProof)].LP == goal:
                return new_prompt_str
            elif not new_prompt_str in prompts:
                probabilities_wild.append(prompt_probability_normalised(bundle,new_prompt_str))
                def mean(x):
                    ans = 0
                    for i in x:
                        ans += i
                    return ans/len(x)
                probabilities_wild[0] = mean(probabilities_wild[1:])
                probabilities = soft_max(probabilities_wild)
                prompts.append(new_prompt_str)
        except Exception as e:
            print("[find_proof_little_smarter]", type(e).__name__, e)
    return prompts,probabilities
prompt = "Prove that: (a ∧ b) → (¬a → c)"
'''
ans = find_proof_little_smarter(bundle_proving,prompt,max_iter=100)
'''
#%%
#check_proof_with_assumptions(
'''Prove that: (a ∧ b) → (¬a → c)
1. a ∧ b    assumption
2. ¬a    assumption
3. a    ∧-elimination1, 1
4. ⊥    ¬-elimination, 2, 3
5. ¬a → c    ⊥-elimination, 4
6. (a ∧ b) → (¬a → c)    →-introduction, 1–5'''#)

#%%
parseProof('''1. a ∧ b    assumption
2. ¬a    assumption
3. a    ∧-elimination1, 1
4. ⊥    ¬-elimination, 2, 3
5. ¬a → c    ⊥-elimination, 4
6. (a ∧ b) → (¬a → c)    →-introduction, 1–5''')
#%% md
# strategia 3
#%%
def prompts_to_prove_from_smashed_problem(SP : smashed_problem):
    ANS = []
    for i in SP.subproblems:
        ans = "Prove that: " + to_infix(i.conclusion) + "\n"
        if i.assumptions.base_context != []:
            #print(i.assumptions.base_context)
            ans += "assuming that: "
            for j in range(len(i.assumptions.base_context)-1,-1,-1):
                ans += to_infix(i.assumptions.base_context[j]) + ",\n"
            ans = ans[:-2] + "\n"
        ANS.append(ans)
    return ANS

def prompt_to_prove_from_little_problem(LP : LittleProblem):
    ans = "Prove that: " + to_infix(LP.conclusion) + "\n"
    if LP.assumptions.base_context != []:
        #print(LP.assumptions.base_context)
        ans += "assuming that: "
        for j in range(len(LP.assumptions.base_context)-1,-1,-1):
            ans += to_infix(LP.assumptions.base_context[j]) + ",\n"
        ans = ans[:-2] + "\n"
    if LP.assumptions.additional_context != []:
        raise Exception("Nieprawidlowe dodatkowe konteksty")
    return ans
#%%
class node:
    def __init__(self,
                 Interior,
                 Parent = None,
                 Children = [],
                 Text : str = "",
                 Value : bool = False,
                 Probability: float = 1.0):
        if not (isinstance(Interior,smashed_problem) or isinstance(Interior,LittleProblem)):
            raise TypeError("Bad argument")
        if isinstance(Interior,smashed_problem):
            if not (Parent == None):
                if isinstance(Parent,node):
                    if not isinstance(Parent.Interior,LittleProblem):
                        raise TypeError("Bad argument")
                else:
                    raise TypeError("Bad argument")
            for i in Children:
                if not isinstance(i,node):
                    raise TypeError("Bad argument")
                elif not isinstance(i.Interior,LittleProblem):
                    raise TypeError("Bad argument")
        elif isinstance(Interior,LittleProblem):
            if not (Parent == None):
                if isinstance(Parent,node):
                    if not isinstance(Parent.Interior,smashed_problem):
                        raise TypeError("Bad argument")
                else:
                    raise TypeError("Bad argument")
            for i in Children:
                if not isinstance(i,node):
                    raise TypeError("Bad argument")
                elif not isinstance(i.Interior,smashed_problem):
                    raise TypeError("Bad argument")
        else:
            raise TypeError("Bad argument")

        self.Interior = Interior
        self.Parent = Parent
        self.Children = Children
        if Text == None:
            if isinstance(Interior,LittleProblem):
                Text = prompt_to_prove_from_little_problem(Interior)
        self.Text = Text
        self.Value = Value
        self.Probability = Probability


    def Smash_Leaf(self,
                   bundle_smashing : NanoGPTBundle,
                   deg : int = 1):
        if isinstance(self.Interior,smashed_problem):
            raise Exception("not LP")
        if self.Children != []:
            raise Exception("not leaf")
        prompt = "Smash: " + to_infix_LP(self.Interior) + "\n"
        weights = dict()
        for i in range(deg):
            print(i,"-----")
            SPText  = silliest_generate_smash(bundle_smashing,prompt)
            weights_sum = 0
            if len(SPText.splitlines()) != 1:
                if SPText in weights.keys():
                    weights[SPText] += 1
                    weights_sum += 1
                else:
                    weights[SPText] = 1
                    weights_sum += 1
        if weights_sum == 0:
            return None
        for i in weights.keys():
            self.Children.append(
                node(
                check_smash_from_text(i),
                Parent=self,
                Children=[],
                Text=i,
                Value=False,
                Probability=weights[i]/weights_sum
            ))
        for i in self.Children:
            grand_children_interiors = i.Interior.subproblems
            for j in grand_children_interiors:
                i.Children.append(
                    node(
                    j,
                    Parent=i,
                    Children=[],
                    Text=prompt_to_prove_from_little_problem(j),
                    Value=False,
                    Probability=1.0
                ))
            if i.Children == []:
                i.Value = True
                ancestor = i.Parent
                while ancestor != None:
                    print("ok")
                    if isinstance(ancestor.Interior,smashed_problem):
                        value = True
                        for j in ancestor.Children:
                            value = value and j.Value
                        ancestor.Value = value
                    if isinstance(ancestor.Interior,LittleProblem):
                        value = False
                        for j in ancestor.Children:
                            value = value or j.Value
                        ancestor.Value = value
                    ancestor = ancestor.Parent

    def RunLeaf(self,
                bundle_proving : NanoGPTBundle,
                bundle_smashing : NanoGPTBundle,
                temperature : float = 1.0,
                max_iter : int = 20,
                deg : int = 1,
                max_failed_attempts : int = 20):
        if isinstance(self.Interior,smashed_problem):
            raise Exception("not LP")
        if self.Children != []:
            raise Exception("not leaf")
        prompt = prompt_to_prove_from_little_problem(self.Interior)
        proof = find_proof_little_smarter(bundle_proving,prompt,temperature=temperature,max_iter=max_iter,max_failed_attempts=max_failed_attempts)
        if isinstance(proof,str):
            self.Value = True
            self.Text = proof
            ancestor = self.Parent
            while ancestor != None:
                print("ok")
                if isinstance(ancestor.Interior,smashed_problem):
                    value = True
                    for i in ancestor.Children:
                        value = value and i.Value
                    ancestor.Value = value
                if isinstance(ancestor.Interior,LittleProblem):
                    value = False
                    for i in ancestor.Children:
                        value = value or i.Value
                    ancestor.Value = value
                ancestor = ancestor.Parent
            return True
        else:
            self.Smash_Leaf(bundle_smashing,deg)
            return False


    def TryNode(self,
                bundle_proving : NanoGPTBundle,
                bundle_smashing : NanoGPTBundle,
                temperature : float = 1.0,
                max_iter : int = 20,
                deg : int = 10,
                max_failed_attempts : int = 20):

        if self.Value == True:
            return True
        if isinstance(self.Interior,LittleProblem) and self.Children == []:
            return self.RunLeaf(bundle_proving,bundle_smashing,temperature=temperature,max_iter=max_iter,deg=deg,max_failed_attempts=max_failed_attempts)
        elif isinstance(self.Interior,LittleProblem):
            weights = []
            for i in self.Children:
                weights.append(i.Probability)
            next_step = random.choices(self.Children,weights=weights)[0]
            return next_step.TryNode(bundle_proving,bundle_smashing,temperature=temperature,max_iter=max_iter,deg=deg,max_failed_attempts=max_failed_attempts)
        elif isinstance(self.Interior,smashed_problem):
            for i in self.Children:
                if not i.TryNode(bundle_proving,bundle_smashing,temperature=temperature,max_iter=max_iter,deg=deg,max_failed_attempts=max_failed_attempts):
                    return False
            return True


    def to_str(self):
        ans = ""
        if isinstance(self.Interior,smashed_problem):
            ans += str(self.Interior)
        else:
            #print(self.Text)
            ans += self.Text
        ans += "\n"
        if self.Children != [] and self.Interior == []:
            ans += "\t."
        else:
            for i in self.Children:
                little_ans = i.to_str()
                little_ans = "\t" + little_ans
                little_ans = little_ans.replace("\n","\n\t")
                ans += little_ans
        return ans
#%%

n = node(LittleProblem(Context([],[]),parse_infix("(a ∧ b) ∧ c ∧ d ∧ e) → ((a ∧ d) ∧ e)")),
    Parent = None,
    Children = [],
    Text = "",
    Value = False,
    Probability = 1.0)

for i in range(20):
    print(i,"----------------------------------------------------------------------------------------")
    if n.TryNode(bundle_proving,bundle_smashing,temperature=1.0,max_iter=10,deg=5):
        break

print(n.Children)
#%%
bundle_smashing = load_nanogpt_bundle("out-NEW_CORPUS_SMASH")
n = node(LittleProblem(Context([],[]),parse_infix("((a ∧ b) ∧ ((c ∧ d) ∧ e)) → ((a ∧ d) ∧ e)")),
    Parent = None,
    Children = [],
    Text = "",
    Value = False,
    Probability = 1.0)

for i in range(20):
    print(i,"----------------------------------------------------------------------------------------")
    if n.TryNode(bundle_proving,bundle_smashing,temperature=1.0,max_iter=10,deg=5):
        break

print(n.Children)
#%%
find_proof_little_smarter(bundle_proving,pr,temperature=1.0,max_iter=50,max_failed_attempts=20)
#%%
next_line_smart(bundle_proving,'Prove that: ((a ∧ b) ∧ ((c ∧ d) ∧ e)) → ((a ∧ d) ∧ e)\n',temperature=1)
#%%
silliest_generate_smash(bundle_smash,"Smash: ⊢ ((a ∧ b) ∧ ((c ∧ d) ∧ e)) → ((a ∧ d) ∧ e)")

#%%
silliest_generate_smash(bundle_smash,"Smash: (a ∧ b) ∧ ((c ∧ d) ∧ e) ⊢ (a ∧ d) ∧ e")
#%%
find_proof_little_smarter(bundle_proving,prompt,temperature=1.0,max_iter=50,max_failed_attempts=20)
#%%
silliest_generate_smash(bundle_smashing,"Smash: ((a ∧ b) ∧ ((c ∧ d) ∧ e)) → ((a ∧ d) ∧ e)")
#%% md
ma tendencje do dawania za długich formuł po rozbiciu
#%%
with open("NEW_CORPUS_SMASHTosecondTraining.txt", "r", encoding="utf-8") as f:
    text = f.read()
text = [p.strip() for p in re.split(r'\n\s*\n', text.strip()) if p.strip()]
#%%
def is_shorter_after_smash(prompt):
    signs = {'¬','∧', '∨', '→','↔'}
    prompt_splitted = prompt.splitlines()
    if len(prompt_splitted) < 3:
        return False
    thesis_before_smash = prompt_splitted[0].split('⊢')[1]
    thesis_before_smash_length = sum(1 for c in thesis_before_smash if c in signs)
    thesiss_after_smash_length = [0]
    for i in range(2,len(prompt_splitted)):
        if not '⊢' in prompt_splitted[i]:
            return thesis_before_smash_length >= max(thesiss_after_smash_length) 
        thesis_after_smash = prompt_splitted[i].split('⊢')[1]
        thesiss_after_smash_length.append(sum(1 for c in thesis_after_smash if c in signs))
    return thesis_before_smash_length > max(thesiss_after_smash_length)
#%%
finetune_corpus_smash_shorted = []
for i in tqdm(text,total =len(text)):
    if is_shorter_after_smash(i):
        finetune_corpus_smash_shorted.append(i)
#%%
text = "\n\n".join(finetune_corpus_smash_shorted)
#%% md
# Korpus "odwrócony"
#%%
def goal_part(proof):
    return proof.split("\n1.")[0]
def proof_part(proof):
    return "1."+proof.split("\n1.")[1]
#%%
print(goal_part('''Prove that: ¬q
assuming that: (p → q) ∧ ¬q
1. (p → q) ∧ ¬q    context, 0
2. ¬q    ∧-elimination2, 1''') + "\n"+
    proof_part('''Prove that: ¬q
assuming that: (p → q) ∧ ¬q
1. (p → q) ∧ ¬q    context, 0
2. ¬q    ∧-elimination2, 1'''))
#%%
def invert_line(line_old):
    idx = line_old.split(". ")[0]
    formula = (line_old.split(". ")[1]).split('    ')[0]
    rule = (line_old.split(". ")[1]).split('    ')[1]
    return idx + ". " + rule + "    " + formula

def revert_line(line_new):
    idx = line_new.split(". ")[0]
    rule = (line_new.split(". ")[1]).split('    ')[0]
    formula = (line_new.split(". ")[1]).split('    ')[1]
    return idx + ". " + formula + "    " + rule
revert_line(invert_line('1. (p → q) ∧ ¬q    context, 0'))

#%%

#%%
def invert_proof(proof_old):
    gp = goal_part(proof_old)
    pp = proof_part(proof_old)
    pp_splitted = pp.splitlines()
    for i in range(len(pp_splitted)):
        pp_splitted[i] = invert_line(pp_splitted[i])
    pp = "\n".join(pp_splitted)
    return gp + "\n"+pp

def revert_proof(proof_old):
    gp = goal_part(proof_old)
    pp = proof_part(proof_old)
    pp_splitted = pp.splitlines()
    for i in range(len(pp_splitted)):
        pp_splitted[i] = revert_line(pp_splitted[i])
    pp = "\n".join(pp_splitted)
    return gp + "\n"+pp
print(
invert_proof('''Prove that: q
assuming that: p,
(p → q) ∧ ¬q
1. (p → q) ∧ ¬q    context, 0
2. p → q    ∧-elimination1, 1
3. p    context, 0
4. q    →-elimination, 2, 3'''))
#%%
with open("NEW_CORPUS_PROVING.txt", "r", encoding="utf-8") as f:
    text = f.read()

proofs_table  = text.strip().split("\n\n")
#%%
from tqdm import tqdm
for i in tqdm(range(len(proofs_table))):
    proofs_table[i] = invert_proof(proofs_table[i])
#%%
text = "\n\n".join(proofs_table)

#%%
'''
with open("corpus_inverted.txt", "w", encoding="utf-8") as f:
    f.write(text)
'''
#%%
with open("corpus_inverted.txt", "r", encoding="utf-8") as f:
    text = f.read()

proofs_table  = text.strip().split("\n")
def rule_from_inverted_line(line):
    if line == "":
        return None
    if not line[0] in ['1','2','3','4','5','6','7','8','9']:
        return None
    else:
        rule = line.split(".")[1]
        rule = rule.split("    ")[0]
        rule = rule.split(",")[0]
        return rule
#%%
for i in proofs_table:
    print(rule_from_inverted_line(i))
#%%
how_many_times_was = dict()
for i in proofs_table:
    if rule_from_inverted_line(i) != None:
        if rule_from_inverted_line(i) in how_many_times_was.keys():
            how_many_times_was[rule_from_inverted_line(i)] += 1
        else:
            how_many_times_was[rule_from_inverted_line(i)] = 1
#%%
def next_line_smart_inverted(
        bundle: NanoGPTBundle,
        prompt: str,
        *,
        temperature: float = 1.0
):
    next_token = None
    prompt = prompt.rstrip("\n")
    prompt = prompt.rstrip(" ")
    prompt_splitted = prompt.splitlines()
    if prompt[0] == 'P':
        formulas = []
        formulas.append(parse_infix(prompt_splitted[0][11:]))
        acceptable_vars = None
        if len(prompt_splitted) == 1:
            acceptable_vars = formula_free_variables(formulas[0])
            acceptable_vars = [to_infix(x) for x in acceptable_vars]
        elif prompt_splitted[1][0] == 'a':
            if prompt_splitted[1][-1] == ',':
                formulas.append(parse_infix(prompt_splitted[1][14:-1]))
            else:
                formulas.append(parse_infix(prompt_splitted[1][14:]))
            for i in range(2,len(prompt_splitted)):
                if prompt_splitted[i][0] != '1':
                    if prompt_splitted[i][-1] == ',':
                        formulas.append(parse_infix(prompt_splitted[i][:-1]))
                    else:
                        formulas.append(parse_infix(prompt_splitted[i]))
                else:
                    break
        ans = ''
        if not prompt_splitted[-1][0] in  ['1','2','3','4','5','6','7','8','9']:
            ans = "1. "
        else:
            idx = str(int(re.findall(r"\d+",prompt_splitted[-1])[0])+1)
            ans = idx + ". "
        old_ans = ans
        if acceptable_vars is None:
            acceptable_vars = free_variables_LP(LittleProblem(Context(formulas,[]),Truth()))
            acceptable_vars = [to_infix(x) for x in acceptable_vars]

        acceptable_tokens = acceptable_vars + [' ','¬','∨','∧','→','↔','(',')','⊤','⊥',"\n"]
        while next_token != "\n":
            while not (ans[-1] == ' ' and ans[-2] == ' '):
                next_token = random_next_token(bundle,prompt+"\n"+ans,temperature=temperature)
                ans+=next_token
            ans += "  "
            while next_token != "\n":
                next_token = random_next_token(bundle,prompt+"\n"+ans,temperature=temperature)
                if next_token in acceptable_tokens:
                    ans += next_token
                else:
                    ans = old_ans
                    break
        return ans
    if prompt[0] == 'S':
        lp_text = prompt_splitted[0][6:]
        acceptable_vars = list(set(findall(r"[a-z]",lp_text)))
        ans = ""
        if len(prompt_splitted) == 1:
            ans = "With: "
            while next_token != '\n':
                next_token = random_next_token(bundle,prompt+"\n"+ans,temperature=temperature)
                ans+=next_token

        if len(prompt_splitted) == 2:
            ans = "To: "
        acceptable_tokens = acceptable_vars + [' ','¬','∨','∧','→','↔','(',')','⊤','⊥',',','⊢','\n']
        old_ans = ans
        while next_token != "\n":
            next_token = random_next_token(bundle,prompt+"\n"+ans,temperature=temperature)
            print(ans + next_token,";")
            if next_token in acceptable_tokens:
                ans += next_token
            else:
                ans = old_ans
        return ans
#%%
bundle_proving = load_nanogpt_bundle("out-corpus_inverted")
bundle_smashing = load_nanogpt_bundle("out-new_corpus_smash")
#%%
prompt = '''Prove that: ((p ∨ q) ∧ ¬p) → q
1. assumption    (p ∨ q) ∧ ¬p
2. ∧-elimination1, 1    p ∨ q
3. ∧-elimination2, 1    ¬p
4. assumption    p
'''
next_line_smart_inverted(bundle_proving,prompt)
#%%
def check_inverted_proof_with_assumptions(proof):
    reverted = revert_proof(proof)
    return check_proof_with_assumptions(reverted)

def parse_inverted_proof_with_assumptions(proof):
    assumptions = goal_part(proof).splitlines()[1:]
    assumptions[0] = assumptions[0][14:]

    for i in range(len(assumptions)):
        if assumptions[i][-1] == ',':
            assumptions[i]= assumptions[i][:-1]
    assumptions = [parse_infix(i) for i in assumptions]
    reverted = revert_proof(proof)
    return parseProof(proof_part(reverted),assumptions)


parse_inverted_proof_with_assumptions('''Prove that: q
assuming that: (p ∨ q) ∧ ¬p,
p
1. context, 0    (p ∨ q) ∧ ¬p
2. ∧-elimination2, 1    ¬p
3. context, 0    p
4. ¬-elimination, 2, 3    ⊥''')



def thesis_conclusion_from_proof_with_assumptions(proof):
    return parse_infix(prompt.splitlines()[0][12:])

def base_context_from_proof_with_assumptions(proof):
    if not proof.splitlines()[1][0] == 'a':
        return []
    assumptions = goal_part(proof).splitlines()[1:]
    assumptions[0] = assumptions[0][14:]
    for i in range(len(assumptions)):
        if assumptions[i][-1] == ',':
            assumptions[i]= assumptions[i][:-1]
    print(assumptions)
    assumptions = [parse_infix(i) for i in assumptions]
    return assumptions

#%%
prompt = '''Prove that: q
assuming that: (p ∨ q) ∧ ¬p,
p
1. context, 0    (p ∨ q) ∧ ¬p
2. ∧-elimination2, 1    ¬p
3. context, 0    p
4. ¬-elimination, 2, 3    ⊥'''
thesis_conclusion_from_proof_with_assumptions(prompt)
#%%
def silliest_generate_proof_inverted(bundle : NanoGPTBundle,
                            prompt : str,
                            temperature : float = 1.0,
                            max_new_lines : int = 1,
                            max_failed_attempts : int = 200,
                            is_first_proof_line = False):
    prompt_str = prompt.rstrip("\n") + "\n"  #dodalem
    prompt = [line for line in prompt_str.splitlines() if line.strip() != ""]  #dodalem
    thesis_conclusion = thesis_conclusion_from_proof_with_assumptions(prompt_str)
    print(prompt_str)
    base_context = base_context_from_proof_with_assumptions(prompt_str)
    if thesis_conclusion in base_context:
        ans = goal_part(prompt_str)
        new_line = "1. " +"context, 0    " + to_infix(thesis_conclusion)
        ans += new_line
        check_proof_with_assumptions(ans)
        return ans
    goal = LittleProblem(Context(base_context,[]) , thesis_conclusion)

    existing_proof = proof_part(prompt_str)
    added_proof = ""  #dodalem
    last_parsed_line = None
    new_lines = 0
    failed_attempts = 0

    while last_parsed_line != goal and new_lines < max_new_lines:
        nl =  next_line_smart_inverted(bundle,prompt_str+added_proof,temperature=temperature)
        print(nl)
        nl= nl.rstrip("\n")
        nl= nl.lstrip("\n")
        failed_attempts += 1
        if failed_attempts > max_failed_attempts:
            break
        stripped_nl = nl.strip()
        if stripped_nl == "":
            continue
        if "." not in stripped_nl or not stripped_nl.split(".", 1)[0].isdigit():
            continue
        try:
            temporary_added_proof = added_proof + nl + "\n"  #dodalem
            temporary_proof = existing_proof + temporary_added_proof  #dodalem
            parsedProof = parse_inverted_proof_with_assumptions(temporary_proof[:-1],base_context)
            last_parsed_line = parsedProof[len(parsedProof)].LP
            for i in range(1,len(parsedProof)):
                if last_parsed_line == parsedProof[i].LP:
                    raise(Exception("Repetition"))
            new_lines += 1
            added_proof = temporary_added_proof
            new_lines += 1
            failed_attempts = 0
        except Exception:
            pass
    return prompt_str+added_proof  #dodalem
#%%
silliest_generate_proof_inverted(bundle_proving,'''Prove that: ((p ∨ q) ∧ ¬p) → q
1. assumption    (p ∨ q) ∧ ¬p
2. ∧-elimination1, 1    p ∨ q
3. ∧-elimination2, 1    ¬p
4. assumption    p
5. ¬-elimination, 3, 4    ⊥''')