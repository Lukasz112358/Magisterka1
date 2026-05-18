import sys
from pathlib import Path

PROJECT_ROOT = Path("/home/lukasz/PycharmProjects/Magisterka").resolve()
sys.path.insert(0, str(PROJECT_ROOT))
sys.path.insert(0, str(PROJECT_ROOT / "nanoGPT"))

import import_ipynb
from praca_core_bez_sprawdzania_tautologicznosci import *


import os
import gc
import time
import pickle
import signal
import psutil
import multiprocessing as mp
from queue import Empty
from tqdm.auto import tqdm





TIMEOUT_SECONDS = 300
RAM_LIMIT_GB = 20
SAVE_EVERY = 1
ANSWERS_PATH = "answers_losowe_bez_sprawdzania.pkl"


def worker(i, q):
    try:
        proc = psutil.Process(os.getpid())
        ram_limit = RAM_LIMIT_GB * 1024**3

        bundle_proving = load_nanogpt_bundle("out-NEW_CORPUS_PROVING")

        start = time.monotonic()

        def check_limits():
            if time.monotonic() - start > TIMEOUT_SECONDS:
                raise TimeoutError("timeout")
            if proc.memory_info().rss > ram_limit:
                raise MemoryError("RAM limit exceeded")

        # jeśli procedure nie przyjmuje check_limits, to tego nie przekażesz
        # ale worker i tak jest zabijany z zewnątrz po timeout
        result = procedure(
            i,
            bundle_proving,
            bundle_smashing,
            temperature=1.0,
            max_iter=50,
            deg=5,
            max_failed_attempts=2,
            tries_number=10
        )

        q.put(("ok", result))

    except Exception as e:
        q.put(("err", f"{type(e).__name__}: {e}"))

    finally:
        gc.collect()


def run_one(i):
    ctx = mp.get_context("spawn")
    q = ctx.Queue()
    p = ctx.Process(target=worker, args=(i, q))
    p.start()

    proc = psutil.Process(p.pid)
    deadline = time.monotonic() + TIMEOUT_SECONDS
    ram_limit = RAM_LIMIT_GB * 1024**3

    while p.is_alive():
        if time.monotonic() > deadline:
            p.terminate()
            p.join()
            return None, "timeout"

        try:
            if proc.memory_info().rss > ram_limit:
                p.terminate()
                p.join()
                return None, "ram"
        except psutil.NoSuchProcess:
            break

        time.sleep(0.5)

    p.join()

    try:
        status, result = q.get_nowait()
    except Empty:
        return None, "no_result"

    if status == "ok":
        return result, None
    else:
        return None, result


def save_answers():
    with open(ANSWERS_PATH, "wb") as f:
        pickle.dump(answers, f)

tests ='''(c ∧ ¬c) ∨ (c → c)
(b ∨ (c ↔ (b ∨ c))) ∧ ((q ∨ q) ∨ (q ↔ q))
((r ∨ b) ∧ (p → ¬q)) ∨ (b → p)
(r ∨ p) ∨ (¬r ∨ (¬b ∧ p))
(p ∨ ¬(¬r ∧ (p ∧ b))) ∨ ¬(p ↔ p)
(q ∧ r) ∨ (¬(r ↔ q) ∨ (q ∨ (q → b)))
¬c ∨ (((p ∨ b) ∧ q) → (((((q ∧ a) ∧ (r ∧ c)) ∧ b) ∧ p) → c))
(¬a → ¬p) ∨ ((a ↔ a) ∨ a)
b → ((p → (b → b)) ↔ (c ↔ c))
(c ∨ (r → p)) ∨ (p → ((c ∧ a) ∧ (r ∧ b)))
((q ∨ (a → r)) ∨ c) ∨ (q → (c ∧ r))
(q ∧ ((b → q) ↔ r)) → (c → (a → c))
((q ∧ r) → q) → ((b → b) ∨ ¬p)
b ↔ (b ∧ (r ↔ r))
(c ∨ c) → ((q ∧ p) → c)
(b → c) ∨ ((a → p) → (c → p))
(¬p → ((p ∨ a) ∧ (r ↔ c))) ∨ ((c → c) ∨ (b ∧ b))
(a ↔ b) ∨ (c ↔ (c ∨ c))
(p ↔ (p ∧ r)) ∨ ((q → ((b → r) ∧ p)) ∨ p)
(p ∨ b) ↔ (b ∨ p)
((((c → c) ↔ (p ↔ b)) → ((b ↔ q) → c)) ∧ c) → ((q ∨ r) → (r → r))
(a → q) ∨ (a ∧ a)
((r ∧ p) ∨ (r → r)) ∨ ((q ↔ r) ↔ r)
((a → c) ↔ q) ∨ (c ∨ ((q ∧ (b ∧ c)) → q))
((¬p ∨ c) → (b ↔ b)) ∨ (¬c ↔ ¬a)
(¬b ∨ q) ∨ (c ∨ (r → (c → r)))
(((p ∧ a) ∨ a) ∧ a) → a
b ∨ (b → p)
(a ∨ (c → (a ∨ c))) ∨ (c → c)
p ∨ ((((b → a) ↔ p) ∨ (b ∨ c)) → (c → c))
(q → (q → (p ↔ p))) ∨ (p → r)
¬¬((p ↔ r) → (p ↔ r))
(q ↔ ((r → r) ↔ ¬q)) → (((b ∨ q) ∨ ((r ∧ c) ↔ r)) → (a ↔ c))
((r ∨ ¬(r ∨ c)) ↔ (q ∨ (c → c))) ∨ (¬c → ((p ∨ b) ∧ ¬b))
¬(r ↔ r) ↔ ¬(a ↔ a)
(((a ∨ c) ↔ r) → ((¬r ∨ (a ∨ c)) ∧ ((a ∧ p) → (c ∧ a)))) ∨ (a ∨ ¬b)
(p → q) → ((p ∨ q) → q)
(r ∧ (b ∧ r)) → (b → b)
(c ∧ (a ↔ p)) → (c ↔ c)
(¬r ∨ p) ∨ r
(c ↔ c) ∨ ¬(c ∨ (q ∨ q))
(p ∧ p) ↔ p
(q ∧ ¬q) → ¬(b ∧ (q ∧ q))
q → ((b ∨ b) ↔ b)
(((p ↔ p) ∧ (r ↔ p)) ↔ p) ↔ (r ∧ r)
(r ∨ r) ∨ ((c ∧ c) ∨ (c → c))
(c ∧ b) → (((b → p) ↔ c) ∨ b)
(((r → r) ∧ (b ∧ q)) ∨ (q ∧ ((r ∧ c) ∧ p))) → ((a ∨ c) ∨ q)
(b ∨ (b → a)) ∨ (b ∧ (a ∨ a))
(c ∧ (q ↔ c)) ∨ (¬c → (c → a))
¬q → (r → (r ∧ r))
¬(¬(p → p) ∧ ((p ∧ (p → r)) ↔ q))
c → (a → (¬r ∨ r))
r ∨ (r → (p ↔ b))
(c ∨ (r → r)) ∨ ¬(p ∨ a)
¬r ↔ (¬r ∧ (a ↔ a))
q → ((a → (q ∨ q)) ∨ p)
(q ∨ (b ↔ b)) ∨ (¬¬r ∨ r)
((b ∧ c) → (c ∨ p)) ∨ ((c ∧ c) ↔ ¬c)
(b → (a ∧ c)) → ((¬p ∧ b) → c)
(b ∧ c) → ((q ∨ q) → q)
((r → r) ∨ (((r → b) ∨ a) → (p ∧ b))) ∨ (p ∨ b)
¬¬(b ↔ p) ∨ ((((q → c) ↔ (p ↔ c)) ↔ (q ∧ c)) → (((c ∨ p) → b) → ((p → a) ∨ b)))
((¬(c ∧ c) ∨ b) → (b ∨ b)) ∨ ((q ∨ r) ∨ (r → (b ∨ q)))
(p → r) ∨ ¬(r ↔ p)
(c → c) ↔ (¬a → (r ↔ r))
((¬a ∨ (b ∨ p)) ∨ a) ∨ (((q ↔ p) ∧ q) ↔ ((((b ∨ b) ∧ (p → p)) ↔ (a → c)) → p))
(c ∨ q) ∨ (((c ↔ r) ∨ (a → (r ∨ a))) ∨ r)
¬b ∨ (b ∨ r)
(p ∧ (¬q → (b → p))) ∨ ((b ↔ b) ∨ r)
¬((p ∧ b) → (b ↔ b)) → (q ∨ q)
¬(p → r) → (r → c)
(r ∨ r) ∨ ((((c ∧ a) ∧ (b ∨ c)) → a) ∨ ((a ∧ c) ∧ c))
(¬(r ∨ c) → p) ∨ (¬a → ¬a)
¬a ∨ (c → (c ↔ a))
¬q ∨ (p → q)
(c ∧ c) ↔ c
(((b → q) ∨ a) ↔ b) → b
(((p → c) ∨ b) → p) → (a ↔ a)
(a → a) ∨ ((p ↔ p) → a)
(b ↔ ((r ∧ b) ∨ c)) ∨ ((c ∨ c) ↔ c)
((q → q) ∨ (r ∧ b)) ∨ (b → b)
(a → p) ∨ a
((r ∨ a) ∨ ¬p) ∨ ((p ∨ c) ∧ (a → r))
(a → b) ∨ a
(b ∨ b) ↔ ¬¬b
(r ∧ p) → ((a → ¬r) ∨ ((c ∧ p) ∨ a))
((q → q) ∨ ¬c) ∨ (((r ∨ b) ∨ q) ∧ ¬p)
(c ↔ ¬r) → (b → b)
((q → a) ∨ c) ∨ (q ∨ ¬p)
¬p → ((r ∧ c) ∨ (b ↔ b))
¬(q ∨ b) → ((c ↔ c) ∨ (p ↔ b))
((a ∨ b) ∧ (r ∨ a)) → (¬c ∨ c)
¬((c → (b ↔ a)) ∨ ((r ↔ q) ∨ c)) → ¬c
((c ∨ q) ∨ (q → a)) ∨ (p ↔ r)
((p ↔ c) → (p → c)) ∨ ((a ↔ r) ∨ ¬q)
(p ∨ ¬b) ∨ (c → (q → ¬p))
(a ∨ p) → ¬¬(r → r)
r → ((b ∨ p) ∨ ¬b)
(b ∧ ¬(q ∨ r)) → (r → (a ∧ ((q ∧ q) ↔ (b ↔ r))))
r ∨ ¬(q ∧ r)
¬(q ∨ r) → ¬(r ∨ r)
((a ↔ (c ∧ r)) → (q ∨ b)) ∨ ¬(b ∨ (p ∧ q))
(a → ¬p) ∨ (p ∨ (a ∨ p))
((¬q ∨ q) ↔ c) ↔ c
(b ↔ b) ∨ (((b ∨ c) → a) ↔ r)
((r → q) ∧ r) ∨ ((q → r) ∨ ((b → (c → q)) → (p ∨ q)))
((c ↔ b) ∧ ((r ∨ (p → (b ↔ p))) ∨ ((b ↔ p) ∨ (c ∧ a)))) ∨ ((p ∨ c) ∨ (r → (p → q)))
¬(q ↔ ¬q)
(((q ∨ a) → r) ∨ (q → ¬r)) ∨ ¬(a ∨ c)
((c ∨ (q ↔ q)) ∨ r) ∨ (¬c ∨ (p ∧ (q ∨ a)))
((p → (q ∧ p)) ∨ (b ∨ p)) ∨ (a ∧ (a ∨ (b ↔ q)))
((b ↔ b) ∧ r) → (((p → p) ∨ ((r → b) ∨ (r ∨ c))) ∧ (p → r))
¬b → (¬¬(b → q) ∨ ¬q)
(a ∧ (c ↔ a)) → ((c ↔ p) → c)
((b ↔ c) ∨ p) ∨ ((q ∨ b) ∨ (¬(c ↔ (q ↔ c)) ∨ (c ∨ q)))
((q ∨ a) ∧ (p ∧ (p ∨ ¬a))) → ¬¬(a ∨ p)
(b → c) ∨ (¬b ↔ c)
(q ∨ p) ∨ (¬(¬p ↔ (q ∨ q)) ∨ ((c ↔ r) ↔ (a ↔ c)))
(¬((r ∨ b) ∧ (b ↔ ¬q)) → ¬(a ↔ q)) ∨ ((q ↔ (b → (r ∧ b))) → a)
(p ∨ (p ↔ q)) ∨ ((q ∨ (q ↔ p)) ∨ (a ∨ q))
((((b ∧ a) ∨ (r ∧ b)) ∧ ¬r) ∧ ¬a) → ((b → q) ↔ q)
(¬c ∧ c) → (a ↔ c)
(p ↔ (c ↔ a)) ∨ ((r ∨ a) ∨ (r ∨ (q ↔ q)))
((c ∨ r) ∨ ¬c) ∨ ((p ↔ c) → r)
((((c ↔ a) → p) ∧ (q ∨ (c → p))) → (b ↔ (r ∧ (r ↔ c)))) ∨ ¬(¬q ↔ q)
(r ↔ q) ∨ ((r ∨ q) ∧ (r ↔ r))
(r ∨ (q ∧ b)) → (¬b → (¬q ∨ r))
(((r ∨ a) ∧ q) ∨ ((a → a) ∨ r)) ↔ (c → c)
((¬(a ∨ r) → (a ↔ (a ∨ p))) → (p → p)) ∨ ¬(a ∨ (b ∨ p))
r → (¬c → (a ↔ a))
((¬(b ∨ c) → (c ↔ a)) ∨ ((b ∧ p) → ((b ∧ p) ↔ (r ↔ a)))) ∨ ((c ↔ c) ↔ ((b ∨ r) ∨ (¬(c ∧ r) ↔ a)))
¬((r ↔ b) → (r → r)) → (((q ∧ b) ∨ c) → (((c ∨ r) → (c ∨ (c ∨ q))) ∧ p))
(a → (r ↔ r)) ∨ ((¬(c ↔ c) ∧ (c ∧ ¬a)) ↔ (¬a ∧ p))
((q ∧ a) ∨ ¬r) ∨ (r ∨ q)
¬(a → (a ∨ b)) → (((¬b ↔ (c ∨ (r → q))) ∧ q) → (q ∧ (p ↔ (b ∨ b))))
(b → r) ∨ (r → b)
(¬c ∧ (r ∨ (r → p))) ∨ ((a → p) → ((c ∧ a) ↔ a))
((b → (a ∧ a)) ∧ ¬((a ↔ r) ∧ ¬(p ∨ r))) ∨ (((p ∨ a) → p) ∨ p)
(r ∧ (q ↔ a)) ∨ (p ∨ (¬a → (a ↔ p)))
((b → p) ↔ (a ∧ a)) ∨ (((a → r) ∧ r) ↔ r)
¬((q ∨ p) ∨ a) → ¬a
((c ∧ q) ∧ (p ∧ (r ∧ c))) → c
((¬c ∨ b) → (a → (c → c))) ∨ (r ↔ c)
(p → c) ∨ p
((c ∨ q) ∨ (a ∨ b)) ∨ ((b → a) → ¬(c ∧ r))
((p ∨ (r ∧ b)) ∨ ¬(c ∧ q)) → ((c ∨ (b ∧ c)) → ((c ∧ c) ∨ ((a ∨ p) ∨ (a ∧ r))))
((a ∨ a) ∨ ¬¬r) ∨ ((r ↔ c) → ¬(r ∨ c))
((b ∨ a) → (c ∨ c)) → (b ↔ (b ∧ c))
(c → r) → ((p ↔ p) ∨ ((c → a) → (q → a)))
((¬¬c → (b ↔ ¬q)) → (((c ∧ q) ∧ p) → ¬(¬(r ∨ r) ↔ (c → r)))) ∨ ¬¬c
q → ((¬(c → b) → ((q → q) ↔ c)) ∨ p)
(((r ↔ p) → (¬b ↔ q)) ↔ ¬q) ∨ ((p → ((¬q → (¬q ∧ (c ∧ ¬p))) ∧ r)) → ((p ∧ b) → ((q ∨ b) ∨ b)))
p ∨ ((q ∧ r) → (¬c ∨ (q ∧ (c ∧ c))))
(c → q) ∨ c
((c ↔ b) → ((p ↔ r) ↔ a)) → ((c ∧ r) → r)
((p ↔ q) → (((r → c) ∧ c) ↔ ¬((r → a) ∨ ¬q))) ∨ ((b ∨ c) → (r ∨ c))
b → ((b ∨ c) ↔ (c → c))
(((q ↔ p) ∧ p) ∧ ((a ∨ r) ↔ (c → ¬q))) → (((q ∧ (p ∧ ¬p)) → b) ↔ (c ∨ (q ∨ b)))
(((r ↔ r) ↔ (q → b)) → (a ∧ ¬q)) → (a ∨ (b → q))
(¬(a ↔ r) ∧ (((p ∧ c) ↔ p) ∧ p)) → c
((p ∨ (b ∨ q)) ∨ a) ∨ ((a ↔ c) ↔ ((((a ∧ p) ∨ (c ∧ c)) ∧ (b ↔ q)) ↔ q))
((p ∧ r) ∨ (b ∧ ¬a)) → ((r → p) ∨ ¬p)
¬¬q ∨ (¬(r ∨ c) → (r → (q → b)))
¬p ∨ ((p ∨ b) ↔ (q ∨ p))
(p ∧ r) → (((p ∧ r) → (r ∨ (p ∨ p))) ∨ (b ∨ p))
(q → (c ∨ q)) ∨ ¬((c ↔ q) → ¬q)
(q ∨ q) → (((r ∧ q) ↔ r) ∧ q)
(((b → q) ∨ (r ∨ a)) ∨ ¬((a ∧ b) ∨ q)) ∨ ((r → p) → (q → a))
((b ∨ r) ∨ (b ∧ q)) ∨ (b → c)
(((a ∧ r) ∨ (r → ((b ↔ r) → q))) ∨ (c → c)) ∨ ((b → (b → (q → c))) ∨ ((r ↔ c) ↔ (r ∨ q)))
q ∨ (q → ¬p)
(p → (((p ∧ b) ∧ (p ↔ p)) → p)) ∨ (c → q)
(¬b ∨ (c ∨ a)) ∨ ((r → b) ↔ (q ↔ q))
¬(c ∧ a) ∨ ((b → b) ∧ (r ∨ c))
(p ∨ (r ∨ p)) ∨ ((r ∧ b) → ((c ∧ a) → (p ↔ r)))
((a ∧ b) ∨ ¬b) ∨ (((a ∨ ¬a) ∨ a) ∨ a)
¬(¬r → c) → (r → q)
(c → (q ∧ b)) ∨ c
(q → (((b ∧ b) ∧ ¬b) → (b → q))) ∨ (¬a ∧ ((b ∨ (p ∨ c)) → (r ∧ r)))
((b ∨ ¬b) → ¬(q ∧ (a ∧ (a ∧ q)))) ∨ ((¬q ∨ (q ↔ p)) ∨ (¬c ∨ ¬(q → p)))
((p ∨ (q → (a → r))) ∨ q) ∨ p
(r ↔ a) ∨ (¬q → (a ∨ r))
¬¬((p ↔ c) ∧ p) → (q → p)
(a → ((p ∧ c) ∨ (r ∨ a))) ∨ ¬((c ↔ b) ∧ c)
¬(q ∨ p) ∨ ((q ∧ b) → (r ∨ q))
¬¬p ∨ ¬p
((c → ¬r) ↔ (¬r ∧ b)) ∨ (r ∨ (q ↔ q))
(q ↔ (r → r)) ∨ ¬(c ∧ q)
(r → (a → a)) → (b ↔ b)
((q ↔ a) ↔ q) ↔ a
(¬((q ↔ (c ∧ c)) → (r → (r ∨ b))) → (¬c ∧ (b ∧ a))) ∧ ((a → c) ∨ (a ∨ r))
(¬¬q ↔ ((q ∧ b) ∧ ¬(b ↔ c))) ∨ (¬q ∨ (p → p))
(c ↔ (c ∨ p)) → (c ∨ (r ↔ r))
((c ↔ p) → (c ↔ b)) ∨ ((q ∧ b) → ¬p)
¬((a ∨ p) ↔ ((r → r) ∨ (q → p))) → ((c → (p ∧ b)) ∨ ((c → p) ↔ a))
¬(r → (q ∨ r)) → c
¬((b ∧ (((c → p) → q) ∧ ¬a)) ∧ ((b ∧ a) ∧ b))
((p ∨ ¬q) ∧ c) → ¬¬c
((a ↔ b) ∧ q) → (q → q)'''.splitlines()


answers = dict()
for i in tests:
    answers[i] = None

bundle_proving = load_nanogpt_bundle("out-NEW_CORPUS_PROVING")
bundle_smashing = load_nanogpt_bundle("out-NEW_CORPUS_SMASH")


if __name__ == "__main__":
    for counter, i in enumerate(tqdm(tests), start=1):
        if answers[i] is not None:
            continue

        result, err = run_one(i)

        if err is not None:
            print(f"{i}: {err}")
            answers[i] = False
        else:
            answers[i] = result

        if counter % SAVE_EVERY == 0:
            save_answers()

    save_answers()
