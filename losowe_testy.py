import praca_core
import re
# Auto-generated from notebook
# imports + functions + classes only
from transformers.models import phi


from praca_core import *
from praca_magisterska.v2.ContextsAndLP import LittleProblem

from praca_magisterska.v2.TermAndFormulas import *

from praca_magisterska.v2.ContextsAndLP import *

from praca_magisterska.v2.HelpfullFunctions import *

import re

from typing import List

import sys

from pathlib import Path

from concurrent.futures import ProcessPoolExecutor

from itertools import chain

from tqdm.auto import tqdm

from nanoGPT.model import GPTConfig, GPT

from dataclasses import dataclass

import torch

from dataclasses import dataclass

from typing import Callable, Optional

import os

import pickle

import torch

import tiktoken

import numpy as np

import torch

from typing import Optional

import random

import numpy as np

from tqdm import tqdm

with open("KORPUSY/korpus_bez_założeń.txt", "r", encoding="utf-8") as f:
    proofs1 = f.read()
print("ok")
with open("NEW_CORPUS_PROVING.txt", "r") as f:
    text = f.read()

text = text.split("\n\n")

proofs2 = []
for i in tqdm(text,total= len(text)):
    if i.splitlines()[1][0] == '1':
        next_elem = "\n".join(i.splitlines()[1:])
        next_elem = next_elem.strip("\n")
        proofs2.append(next_elem)

print("ok")
proofs = proofs2 + proofs1.split("\n\n")
print("ok")
proofs_normalised = set()

def one_proof_to_normalised_infix(proof_text):
    try:
        parsed = parseProof(proof_text.strip("\n"))
        conclusion = parsed[len(parsed)].LP.conclusion
        return to_infix(normalise(conclusion))
    except:
        pass


def parallel_normalise_proofs(proofs, max_workers=None):
    proofs_normalised = set()

    with ProcessPoolExecutor(max_workers=max_workers) as executor:
        for formula in tqdm(
            executor.map(one_proof_to_normalised_infix, proofs),
            total=len(proofs)
        ):
            proofs_normalised.add(formula)

    return proofs_normalised

proofs_normalised = parallel_normalise_proofs(proofs)

for i in range(100):
    while True:
        f = randomFormula(30,list("abcpqr"),TruthLieIncluded=False)
        if is_tautology(f):
            if not to_infix(normalise(f)) in proofs_normalised:
                print(to_infix(f))
                break

for i in range(100):
    while True:
        f = randomFormula(100,list("abcpqr"),TruthLieIncluded=False)
        if is_tautology(f):
            if not to_infix(normalise(f)) in proofs_normalised:
                print(to_infix(f))
                break