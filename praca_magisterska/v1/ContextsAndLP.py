import sys
from pathlib import Path

# adjust if your path differs
PROJECT_ROOT = Path.home() / "PycharmProjects" / "Magisterka"
PKG_ROOT = PROJECT_ROOT / "nanoGPT-20251228T135841Z-3-001" / "nanoGPT"

sys.path.insert(0, str(PKG_ROOT))

from praca_magisterska.v1 import TermAndFormulas
from praca_magisterska.v1 import TermAndFormulas

class Context:
    def __init__(self, *args):
        for i in args:
            if not isinstance(i, TermAndFormulas.Formula):
                raise TypeError("Bad arguments")

        self.formulas = list(set(args))


    def __str__(self):
        ans = ""
        for i in self.formulas:
            ans += i.__str__() + ", "
        ans = ans[:-2]
        return ans
    def __repr__(self):
        ans = ""
        for i in self.formulas:
            ans += i.__repr__() + ", "
        ans = ans[:-2]
        return ans
    @staticmethod
    def union(x,y):
        if not isinstance(x,Context) or not isinstance(y,Context):
            raise TypeError("Bad arguments")
        set1 = set(x.formulas)
        set2 = set(y.formulas)
        set3  = set1.union(set2)
        return Context(*list(set3))
    @staticmethod
    def remove(x,y):
        ans  = Context(*x.formulas)
        if isinstance(y, TermAndFormulas.Formula):
            for i in ans.formulas:
                if i == y:
                    #print(i)
                    ans.formulas.remove(i)
        elif isinstance(y,Context):
            for i in y.formulas:
                for j in ans.formulas:
                    if i == j:
                        ans.formulas.remove(j)
        else:
            raise TypeError("Bad arguments")
        return ans

    def __getitem__(self, index):
        return self.formulas[index]
    def __contains__(self, formula : TermAndFormulas.Formula):
        for i in self.formulas:
            if i ==  formula:
                return True
        return False
    def __add__(self,other):
        if isinstance(other, TermAndFormulas.Formula):
            return Context.union(self,Context(other))
        if isinstance(other,Context):
            return Context.union(self,other)
        else:
            raise TypeError("Bad arguments")
    def __sub__(self,other):
        if isinstance(other, TermAndFormulas.Formula):
            return Context.remove(self,Context(other))
        elif isinstance(other,Context):
            return Context.remove(self,other)
        else:
            raise TypeError("Bad arguments")

    def __eq__(self, other):
        if isinstance(other, Context):
            return set(self.formulas) == set(other.formulas)
        else:
            raise TypeError("Bad arguments")


class LittleProblem:
    def __init__(self,assumptions,conclusion):
        if not isinstance(assumptions,Context):
            raise TypeError("Bad arguments")
        if not isinstance(conclusion, TermAndFormulas.Formula):
            raise TypeError("Bad arguments")
        self.assumptions = assumptions
        self.conclusion = conclusion
    def __str__(self):
        ans = self.assumptions.__str__()
        ans += " ⊢ "
        ans += self.conclusion.__str__()
        return ans
    def __repr__(self):
        ans = self.assumptions.__repr__()
        ans += " ⊢ "
        ans += self.conclusion.__repr__()
        return ans

print(1)