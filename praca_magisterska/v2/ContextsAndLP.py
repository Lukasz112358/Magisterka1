import sys
from pathlib import Path

# adjust if your path differs
PROJECT_ROOT = Path.home() / "PycharmProjects" / "Magisterka"
PKG_ROOT = PROJECT_ROOT / "nanoGPT-20251228T135841Z-3-001" / "nanoGPT"

sys.path.insert(0, str(PKG_ROOT))

#from praca_magisterska.v2 import TermAndFormulas
from praca_magisterska.v2 import TermAndFormulas

class Context:
    @staticmethod
    def _unique_preserving_order(formulas):
        return list(dict.fromkeys(formulas))

    def __init__(self, base_context, additional_context):
        if not isinstance(base_context,list) or not isinstance(additional_context,list):
            raise TypeError("Bad arguments")
        for i in base_context:
            if not isinstance(i, TermAndFormulas.Formula):
                raise TypeError("Bad arguments")
        for i in additional_context:
            if not isinstance(i, TermAndFormulas.Formula):
                raise TypeError("Bad arguments")

        self.base_context = Context._unique_preserving_order(base_context)
        self.additional_context = []
        for i in additional_context:
            if not i in self.base_context:
                self.additional_context.append(i)
        self.additional_context = Context._unique_preserving_order(self.additional_context)


    def __str__(self):
        ans = ""
        for i in self.base_context:
            ans += i.__str__() + ", "
        if not ans =="":
            ans = ans[:-2]
        ans += " ; "
        for i in self.additional_context:
            ans += i.__str__() + ", "
        if not ans[-2]== ";":
            return ans[:-2]
        else:
            return ans + " "
    def __repr__(self):
        ans = ""
        for i in self.base_context:
            ans += i.__repr__() + ", "
        if not ans == "":
            ans = ans[:-2]
        ans += " ; "
        for i in self.additional_context:
            ans += i.__repr__() + ", "
        if not ans[-2] == ";":
            return ans[:-2]
        else:
            return ans + " "
    @staticmethod
    def union(x,y):
        if not isinstance(x,Context) or not isinstance(y,Context):
            raise TypeError("Bad arguments")
        if set(x.base_context) != set(y.base_context):
            raise TypeError("Bad arguments")
        set1 = set(x.additional_context)
        set2 = set(y.additional_context)
        set3  = set1.union(set2)
        return Context(x.base_context,Context._unique_preserving_order(list(set3)))
    @staticmethod
    def remove(x,y):
        ans  = Context(x.base_context,x.additional_context)
        if isinstance(y, TermAndFormulas.Formula):
            for i in ans.additional_context:
                if i == y:
                    #print(i)
                    ans.additional_context.remove(i)
        elif isinstance(y,Context):
            for i in y.additional_context:
                for j in ans.additional_context:
                    if i == j:
                        ans.additional_context.remove(j)
        else:
            raise TypeError("Bad arguments")
        return ans

    def __getitem__(self, index):
        formulas = self.base_context + self.additional_context
        return formulas[index]
    def __contains__(self, formula : TermAndFormulas.Formula):
        formulas = self.base_context + self.additional_context
        for i in formulas:
            if i ==  formula:
                return True
        return False
    def __add__(self,other):
        if isinstance(other, TermAndFormulas.Formula):
            other_context = Context(self.base_context,[other])
            return Context.union(self,other_context)
        if isinstance(other,Context):
            return Context.union(self,other)
        else:
            raise TypeError("Bad arguments")
    def __sub__(self,other):
        return Context.remove(self,other)

    def __eq__(self, other):
        if isinstance(other, Context):
            return (set(self.base_context) == set(other.base_context)) and (set(self.additional_context) == set(other.additional_context))
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
    def __eq__(self, other):
        if isinstance(other, LittleProblem):
            return (self.assumptions == other.assumptions) and (self.conclusion == other.conclusion)
        else:
            return False
print(1)
