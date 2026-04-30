import sys
from pathlib import Path

PROJECT_ROOT = Path("/home/lukasz/PycharmProjects/Magisterka").resolve()
sys.path.insert(0, str(PROJECT_ROOT))
sys.path.insert(0, str(PROJECT_ROOT / "nanoGPT"))

import import_ipynb
from praca_core import *


import os
import gc
import time
import pickle
import signal
import psutil
import multiprocessing as mp
from queue import Empty
from tqdm.auto import tqdm

def normalise_smashed_problem(SP_text):
    SP = check_smash_from_text(SP_text)
    match SP.rule:
        case Assumption():
            return SP_text
        case Weakening():
            return SP_text
        case ImplicationIntroduction():
            return SP_text
        case NegationIntroduction():
            return SP_text
        case ImplicationElimination():
            SP.subproblems[0].assumptions = SP.problem.assumptions
            SP.subproblems[1].assumptions = SP.problem.assumptions
            is_smashed_correctly(SP)
            return pretty_print_smashed_problem(SP)
        case NegationElimination():
            SP.subproblems[0].assumptions = SP.problem.assumptions
            SP.subproblems[1].assumptions = SP.problem.assumptions
            is_smashed_correctly(SP)
            return pretty_print_smashed_problem(SP)
        case ConjunctionIntroduction():
            SP.subproblems[0].assumptions = SP.problem.assumptions
            SP.subproblems[1].assumptions = SP.problem.assumptions
            is_smashed_correctly(SP)
            return pretty_print_smashed_problem(SP)
        case DisjunctionIntroduction1():
            return SP_text
        case DisjunctionIntroduction2():
            return SP_text
        case TruthIntroduction():
            return SP_text
        case ConjunctionElimination1():
            return SP_text
        case ConjunctionElimination2():
            return SP_text
        case DisjunctionElimination():
            phi = SP.subproblems[0].conclusion.Left()
            psi = SP.subproblems[0].conclusion.Right()
            SP.subproblems[0].assumptions = SP.problem.assumptions
            SP.subproblems[1].assumptions.base_context = SP.problem.assumptions.base_context + [phi]
            SP.subproblems[2].assumptions.base_context = SP.problem.assumptions.base_context + [psi]
            is_smashed_correctly(SP)
            return pretty_print_smashed_problem(SP)
        case LieElimination():
            return SP_text
        case IffIntroduction():
            phi = SP.problem.conclusion.Left()
            psi = SP.problem.conclusion.Right()
            SP.subproblems[0].assumptions.base_context = SP.problem.assumptions.base_context + [phi]
            SP.subproblems[1].assumptions.base_context = SP.problem.assumptions.base_context + [psi]
            is_smashed_correctly(SP)
            return pretty_print_smashed_problem(SP)
        case IffElimination1():
            SP.subproblems[0].assumptions = SP.problem.assumptions
            SP.subproblems[1].assumptions = SP.problem.assumptions
            is_smashed_correctly(SP)
            return pretty_print_smashed_problem(SP)
        case IffElimination2():
            SP.subproblems[0].assumptions = SP.problem.assumptions
            SP.subproblems[1].assumptions = SP.problem.assumptions
            is_smashed_correctly(SP)
            return pretty_print_smashed_problem(SP)
        case RAA():
            return SP_text
        case NegationOfNegation():
            return SP_text
        case TND():
            return SP_text
        case FromContext():
            return SP_text
        case FromWeakenContext():
            return SP_text



from concurrent.futures import ProcessPoolExecutor, as_completed
from tqdm import tqdm
import os





from concurrent.futures import ProcessPoolExecutor
from tqdm import tqdm
import os

from concurrent.futures import ProcessPoolExecutor
from tqdm import tqdm
import os
import sys


def _worker(proof_text):
    return normalise_smashed_problem(proof_text)


if __name__ == "__main__":
    file_name = "iffsIntro.txt"
    print(file_name)
    with open(file_name, "r", encoding="utf-8") as f:
        text = f.read()

    text = text.strip("\n")
    proofs_table = text.split("\n\n")

    with ProcessPoolExecutor(max_workers=os.cpu_count()) as ex:
        proofs_table = list(
            tqdm(
                ex.map(_worker, proofs_table, chunksize=20),
                total=len(proofs_table),
                desc="Normalising",
                file=sys.stdout,
                ncols=100
            )
        )

    with open("NEW_CORPUS_SMASH_NORMALISED_WITHOUT_GOOD_IFFS.txt", "a", encoding="utf-8") as f:
        f.write("\n\n".join(proofs_table))
    with open("NEW_CORPUS_SMASH_NORMALISED_WITHOUT_GOOD_IFFS.txt", "a", encoding="utf-8") as f:
        f.write("\n\n")