import json
import ast
from pathlib import Path

NOTEBOOK = "pracav4.ipynb"      # zmień na nazwę notebooka
OUTPUT = "praca_core.py"

def keep(node):
    return isinstance(node, (
        ast.Import,
        ast.ImportFrom,
        ast.FunctionDef,
        ast.AsyncFunctionDef,
        ast.ClassDef,
    ))

with open(NOTEBOOK, "r", encoding="utf-8") as f:
    nb = json.load(f)

out = [
    "# Auto-generated from notebook\n",
    "# imports + functions + classes only\n\n",
]

for cell in nb["cells"]:
    if cell.get("cell_type") != "code":
        continue

    src = cell.get("source", "")
    if isinstance(src, list):
        src = "".join(src)

    try:
        tree = ast.parse(src)
    except SyntaxError:
        continue

    for node in tree.body:
        if keep(node):
            out.append(ast.unparse(node))
            out.append("\n\n")

Path(OUTPUT).write_text("".join(out), encoding="utf-8")
print(f"Zapisano {OUTPUT}")
