import sys
from pathlib import Path

# adjust if your path differs
PROJECT_ROOT = Path.home() / "PycharmProjects" / "Magisterka"
PKG_ROOT = PROJECT_ROOT / "nanoGPT-20251228T135841Z-3-001" / "nanoGPT"

sys.path.insert(0, str(PKG_ROOT))

from praca_magisterska.v1 import TermAndFormulas
import copy
from abc import abstractmethod

class Term():
    @abstractmethod
    def __init__(self):
        pass

relationId = 0
class Relation:
    def __init__(self, name:str, arity:[int]):
        global relationId
        self.name = name
        arity.sort()
        self.arity = arity
        self.id = relationId
        relationId += 1
    def __str__(self):
        return(self.name)
    def __repr__(self):
        return "R" + str(self.id)
    def __eq__(self,other):
        if not isinstance(other,Relation):
            raise TypeError("Bad argument type")
        return self.id == other.id

variableId = 0
class Variable(Term):
    def __init__(self,name:str):
        global variableId
        self.name = name
        self.id = variableId
        variableId += 1
    def __eq__(self,other):
        if not isinstance(other,Variable):
            raise TypeError("Bad argument type")
        return self.name == other.name
    def __str__(self):
        return self.name
    def __repr__(self):
        return self.name
        #return "V"+str(self.id)
    def __hash__(self):
        return hash(self.__str__())
        #return hash(self.__repr__())


class Formula:
    def which_type(self):
        if isinstance(self,Truth):
            return "Truth"
        if isinstance(self,Lie):
            return "Lie"
        if isinstance(self,Atom):
            return "Atom"
        if isinstance(self,Negation):
            return "Negation"
        if isinstance(self,Conjunction):
            return "Conjunction"
        if isinstance(self,Disjunction):
            return "Disjunction"
        if isinstance(self,Implication):
            return "Implication"
        if isinstance(self,Iff):
            return "Iff"
    def __eq__(self,other):
        if isinstance(other,Term):
            return False
        if not isinstance(other,Formula):
            raise TypeError("Bad argument")
        if self.which_type() != other.which_type():
            return False
        return True
    @abstractmethod
    def __str__(self):
        pass
    @abstractmethod
    def __repr__(self):
        pass
    @abstractmethod
    def __init__(self):
        self.Interior = []
    def __eq__(self,other):
        if not isinstance(other,Formula):
            raise TypeError("Bad argument")
        return self.__repr__() == other.__repr__()
    def is_simple(self):
        if self.which_type() == "Truth":
            return True
        if self.which_type() == "Lie":
            return True
        if self.which_type() == "Atom":
            return True
        if self.which_type() == "Negation":
            return True
        return False
    #simpliffying methods
    def Left(self):
        return self.Interior[0]
    def Right(self):
        return self.Interior[1]
    #def Content(self):

    #    return self.Interior[0]
    def __hash__(self):
        return hash(self.__str__())
        #return hash(self.__repr__())

class Truth(Formula):
    def __init__(self):
        return None
    def __eq__(self,other):
        if not isinstance(other,Truth):
            return False
        else:
            return True
    def __str__(self):
        return "T"
    def __repr__(self):
        return "T"
    __hash__ = Formula.__hash__
    def evaluate(self,values):
        return Truth()

class Lie(Formula):
    def __init__(self):
        return None
    def __eq__(self,other):
        if not isinstance(other,Lie):
            return False
        else:
            return True
    def __str__(self):
        return "⊥"
    def __repr__(self):
        return "⊥"
    __hash__ = Formula.__hash__
    def evaluate(self,values):
        return Lie()

class Atom(Formula):
    @staticmethod
    def are_args_ok(args):
        if not type(args[0]) == Relation:
            return False
        for i in args[0].arity:
            if len(args) == i+1:
                for j in args[1:]:
                    if not isinstance(j,Term):
                        return False
                return True
        return False
    def __init__(self,*args):
        if not Atom.are_args_ok(args):
            raise TypeError("Bad arguments")
        self.Relation = args[0]
        self.Arguments = args[1:]
    def __eq__(self, other):
        if super().__eq__(other):
            if not (self.Relation == other.Relation and
                    len(self.Arguments) == len(other.Arguments)):
                return False
            else:
                ans = True
                for i in zip(self.Arguments, other.Arguments):
                    if i[0] != i[1]:
                        return False
                return True
        else:
            return False
    def __str__(self):
        ans = self.Relation.__str__()
        ans +="("
        for i in self.Arguments:
            ans += i.__str__()
            ans += ","
        ans = ans[:-1]
        ans += ")"
        return ans
    def __repr__(self):
        ans = self.Relation.__repr__()
        ans +="("
        for i in self.Arguments:
            ans += i.__repr__()
            ans += ","
        ans = ans[:-1]
        ans += ")"
        return ans
    __hash__ = Formula.__hash__
    def evaluate(self,values):
        return values[self]

class Negation(Formula):
    @staticmethod
    def are_args_ok(args):
        return (len(args) == 1) and isinstance(args[0], Formula)
    def __init__(self,*args):
        if not Negation.are_args_ok(args):
            raise TypeError("Bad arguments")
        self.Interior = [args[0]]
    def __eq__(self, other):
        if super().__eq__(other):
            return self.Interior[0] == other.Interior[0]
        else:
            return False
    def __str__(self):
        if self.Interior[0].is_simple():
            return "¬" + self.Interior[0].__str__()
        else:
            return "¬(" + self.Interior[0].__str__() +")"
    def __repr__(self):
        if self.Interior[0].is_simple():
            return "¬" + self.Interior[0].__repr__()
        else:
            return "¬(" + self.Interior[0].__repr__() +")"
    __hash__ = Formula.__hash__
    def evaluate(self,values):
        v = self.Interior[0].evaluate(values)
        if v == Truth():
            return Lie()
        else:
            return Truth()

class Conjunction(Formula):
    @staticmethod
    def are_args_ok(args):
        for i in args:
            if not isinstance(i, Formula):
                return False
        return True
    def __init__(self,*args):
        if not Conjunction.are_args_ok(args):
            raise TypeError("Bad arguments")
        self.Interior = list(args)
    def __eq__(self, other):
        if super().__eq__(other) and len(self.Interior) == len(other.Interior):
            for i in zip(self.Interior, other.Interior):
                if i[0] != i[1]:
                    return False
            return True
        else:
            return False
    def __str__(self):
        def str(f:Formula):
            if f.is_simple():
                return f.__str__()
            else:
                return "(" + f.__str__() + ")"
        ans = ""
        for i in self.Interior:
            ans += str(i) + " ∧ "
        return ans[:-3]
    def __repr__(self):
        def repr(f:Formula):
            if f.is_simple():
                return f.__repr__()
            else:
                return "(" + f.__repr__() + ")"
        ans = ""
        for i in self.Interior:
            ans += repr(i) + " ∧ "
        return ans[:-3]
    __hash__=Formula.__hash__
    def evaluate(self,values):
        for i in self.Interior:
            if i.evaluate(values) == Lie():
                return Lie()
        return Truth()

class Disjunction(Formula):
    @staticmethod
    def are_args_ok(args):
        for i in args:
            if not isinstance(i, Formula):
                return False
        return True
    def __init__(self,*args):
        if not Disjunction.are_args_ok(args):
            raise TypeError("Bad arguments")
        self.Interior = list(args)
    def __eq__(self, other):
        if super().__eq__(other) and len(self.Interior) == len(other.Interior):
            for i in zip(self.Interior, other.Interior):
                if i[0] != i[1]:
                    return False
            return True
        else:
            return False
    def __str__(self):
        def str(f:Formula):
            if f.is_simple():
                return f.__str__()
            else:
                return "(" + f.__str__() + ")"
        ans = ""
        for i in self.Interior:
            ans += str(i) + " ∨ "
        return ans[:-3]
    def __repr__(self):
        def repr(f:Formula):
            if f.is_simple():
                return f.__repr__()
            else:
                return "(" + f.__repr__() + ")"
        ans = ""
        for i in self.Interior:
            ans += repr(i) + " ∨ "
        return ans[:-3]
    __hash__=Formula.__hash__
    def evaluate(self,values):
        for i in self.Interior:
            if i.evaluate(values) == Truth():
                return Truth()
        return Lie()

class Implication(Formula):
    @staticmethod
    def are_args_ok(args):
        if len(args) != 2:
            raise TypeError("Bad arguments")
        return isinstance(args[0], Formula) and isinstance(args[1], Formula)
    def __init__(self,*args):
        if not Implication.are_args_ok(args):
            raise TypeError("Bad arguments")
        self.Interior = list(args)
    def __eq__(self, other):
        if super().__eq__(other) and len(self.Interior) == len(other.Interior):
            return self.Interior[0] == other.Interior[0] and self.Interior[1] == other.Interior[1]
        else:
            return False
    def __str__(self):
        def str(f:Formula):
            if f.is_simple():
                return f.__str__()
            else:
                return "(" + f.__str__() + ")"
        return str(self.Interior[0]) + " → " + str(self.Interior[1])
    def __repr__(self):
        def repr(f:Formula):
            if f.is_simple():
                return f.__repr__()
            else:
                return "(" + f.__repr__() + ")"
        return repr(self.Interior[0]) + " → " + repr(self.Interior[1])
    __hash__=Formula.__hash__
    def evaluate(self,values):
        if self.Left().evaluate(values) == Lie():
            return Truth()
        else:
            return self.Right().evaluate(values)

class Iff(Formula):
    @staticmethod
    def are_args_ok(args):
        if len(args) != 2:
            raise TypeError("Bad arguments")
        return isinstance(args[0], Formula) and isinstance(args[1], Formula)
    def __init__(self,*args):
        if not Iff.are_args_ok(args):
            raise TypeError("Bad arguments")
        self.Interior = list(args)
    def __eq__(self, other):
        if super().__eq__(other) and len(self.Interior) == len(other.Interior):
            for i in zip(self.Interior, other.Interior):
                if i[0] != i[1]:
                    return False
            return True
        else:
            return False
    def __str__(self):
        def str(f:Formula):
            if f.is_simple():
                return f.__str__()
            else:
                return "(" + f.__str__() + ")"
        return str(self.Interior[0]) + " ↔ " + str(self.Interior[1])
    def __repr__(self):
        def repr(f:Formula):
            if f.is_simple():
                return f.__repr__()
            else:
                return "(" + f.__repr__() + ")"
        return repr(self.Interior[0]) + " ↔ " + repr(self.Interior[1])
    __hash__=Formula.__hash__
    def evaluate(self,values):
        if self.Left().evaluate(values) == self.Right().evaluate(values):
            return Truth()
        else:
            return Lie()
