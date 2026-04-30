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


if __name__ == "__main__":
    for I in range(50):
        print(I)
        iffs = parallel_random_iffs(4_000)
        for i in tqdm(range(len(iffs))):
            iffs[i] = pretty_print_smashed_problem(iffs[i])
        iffs = "\n\n".join(iffs)
        with open("iffsIntro.txt", "a", encoding="utf-8") as f:
            f.write(iffs)
            f.write("\n\n")