#!/usr/bin/env python3
"""Standard-library replay of the finite facts behind the compared statements of Challenge.lean (the
finder/checker split: the Lean development is the trust chain, this script a second implementation). Exact
rationals; nothing imported beyond fractions, itertools, random and sys. Every schedule is computed from the
definitions as Challenge.lean states them: a list schedule gives each job a machine of least load among the earlier
jobs, and every tie-breaking is enumerated as a separate branch; the optimum is the minimum over all m^n
assignments. Checks: the bounds m*C_LS <= (2m - 1)*C_OPT (every order, every branch) and 3m*C_LPT <= (4m - 1)*C_OPT
(the sorted order, every branch) on every nonincreasing instance of a small exhaustive sweep and on random rational
instances, with the ratio 7/6 attained at m = 2; the key lemma (every branch, every job k, every assignment tau of
the sweep); Graham's family 2m-1, 2m-1, ..., m+1, m+1, m, m, m for m = 1..10 (the sum 3m^2, the pairing of makespan
3m, the first-2m pairing of loads 3m - 1, every load 3m - 1 after 2m jobs and makespan 4m - 1 on every branch, the
explicit order whose list schedule has makespan 3m, the position-to-index map as a bijection); the unit-job family
for m = 1..8 (the assignment of makespan m, every load m - 1 after the units and makespan 2m - 1 on every branch); the
brute-force optima of both families for m <= 3; and the instance (9, 5, 5, 4, 4, 4) on three machines, whose LPT
makespan 13 exceeds the optimum 12 (so the hypothesis of the optimality theorem is needed). Ends with VERDICT: PASS
or VERDICT: FAIL; no check uses assert; exit status 0 on PASS only.

    python -I scripts/check_lpt.py
"""

from fractions import Fraction as F
from itertools import product, permutations
import random
import sys

random.seed(20261011)
FAILS = []
CHECKS = 0


def check(label, ok):
    global CHECKS
    CHECKS += 1
    if not ok:
        FAILS.append(label)
        print("FAIL", label)


# ---------------------------------------------------------------- the definitions, replayed

def loads_of(p, sigma, m):
    L = [F(0)] * m
    for j, i in enumerate(sigma):
        L[i] += p[j]
    return L


def makespan(p, sigma, m):
    return max(loads_of(p, sigma, m))


def opt(p, m):
    return min(makespan(p, sigma, m) for sigma in product(range(m), repeat=len(p)))


def branches(p, m):
    """Every list schedule of p in the index order: one assignment per tie-breaking branch."""
    out = []

    def go(k, loads, sigma):
        if k == len(p):
            out.append(tuple(sigma))
            return
        lo = min(loads)
        for i in range(m):
            if loads[i] == lo:
                loads[i] += p[k]
                sigma.append(i)
                go(k + 1, loads, sigma)
                sigma.pop()
                loads[i] -= p[k]

    go(0, [F(0)] * m, [])
    return out


def lowest_index(p, m):
    loads = [F(0)] * m
    sigma = []
    for x in p:
        i = min(range(m), key=lambda i: (loads[i], i))
        loads[i] += x
        sigma.append(i)
    return tuple(sigma)


def is_list_schedule(p, sigma, m):
    loads = [F(0)] * m
    for k, i in enumerate(sigma):
        if any(loads[i] > loads[i2] for i2 in range(m)):
            return False
        loads[i] += p[k]
    return True


def key_lemma(p, sigma, k, tau, m):
    """T = the largest tau-load from the jobs of index <= k; if T < 3 p_k then L_k + p_k <= T."""
    T = max(sum((p[j] for j in range(k + 1) if tau[j] == i), F(0)) for i in range(m))
    if T < 3 * p[k]:
        return loads_of(p[:k], sigma[:k], m)[sigma[k]] + p[k] <= T
    return True


# ---------------------------------------------------------------- the bounds and the key lemma

def sweep():
    worst = {}
    sizes = {1: 4, 2: 5, 3: 4}
    for m in (1, 2, 3):
        for n in range(0, sizes[m] + 1):
            for raw in product(range(0, 5), repeat=n):
                if any(raw[j] < raw[j + 1] for j in range(n - 1)):
                    continue
                p = [F(x) for x in raw]
                c_opt = opt(p, m)
                bs = branches(p, m)
                cs = {makespan(p, s, m) for s in bs}
                check(f"tie-independent makespan m={m} p={raw}", len(cs) == 1)
                check(f"branches are list schedules m={m} p={raw}", all(is_list_schedule(p, s, m) for s in bs))
                c = cs.pop()
                check(f"LPT bound m={m} p={raw}", 3 * m * c <= (4 * m - 1) * c_opt)
                if c_opt > 0:
                    worst[m] = max(worst.get(m, F(0)), F(c, 1) / c_opt)
                if 0 < n:
                    for s in bs:
                        for k in range(n):
                            for tau in product(range(m), repeat=n):
                                check(f"key lemma m={m} p={raw} s={s} k={k} tau={tau}", key_lemma(p, s, k, tau, m))
                for perm in set(permutations(range(n))):
                    q = [p[j] for j in perm]
                    for s in branches(q, m):
                        check(f"list bound m={m} q={q}", m * makespan(q, s, m) <= (2 * m - 1) * c_opt)
    check("the worst LPT ratio at m = 2 in the sweep is 7/6, the family's", worst[2] == F(7, 6))
    print("sweep: worst LPT ratios", {m: str(r) for m, r in worst.items()})


def random_instances():
    for _ in range(200):
        m = random.randint(1, 4)
        n = random.randint(0, 6)
        p = sorted([F(random.randint(0, 30), random.randint(1, 3)) for _ in range(n)], reverse=True)
        c_opt = opt(p, m)
        for s in branches(p, m):
            check(f"random LPT bound m={m} p={p}", 3 * m * makespan(p, s, m) <= (4 * m - 1) * c_opt)
            for k in range(n):
                tau = tuple(random.randrange(m) for _ in range(n))
                check(f"random key lemma m={m} p={p} k={k}", key_lemma(p, s, k, tau, m))
        q = p[:]
        random.shuffle(q)
        for s in branches(q, m):
            check(f"random list bound m={m} q={q}", m * makespan(q, s, m) <= (2 * m - 1) * c_opt)


# ---------------------------------------------------------------- Graham's family

def graham_jobs(m):
    return [F(2 * m - 1 - j // 2) if j < 2 * m else F(m) for j in range(2 * m + 1)]


def tau0(m, j):
    return min(j, 2 * m - 3 - j) if j < 2 * m - 2 else m - 1


def tau_prime(m, j):
    return min(j, 2 * m - 1 - j) if j < 2 * m else 0


def ol_index(m, i):
    if i < m - 1:
        return 2 * i
    if i == m - 1:
        return 2 * m - 2
    if i == m:
        return 2 * m - 1
    if i < 2 * m:
        return 2 * (i - m - 1) + 1
    return 2 * m


def ol_machine(m, i):
    if i < m - 1:
        return i
    if i <= m:
        return m - 1
    if i < 2 * m:
        return 2 * m - 1 - i
    return m - 1


def graham_family():
    for m in range(1, 11):
        p = graham_jobs(m)
        n = 2 * m + 1
        check(f"family antitone m={m}", all(p[j] >= p[j + 1] for j in range(n - 1)))
        check(f"family sum m={m}", sum(p) == 3 * m * m)
        check(f"family pairing loads 3m m={m}", loads_of(p, [tau0(m, j) for j in range(n)], m) == [F(3 * m)] * m)
        check(f"family prefix pairing loads 3m-1 m={m}",
              loads_of(p[:2 * m], [tau_prime(m, j) for j in range(2 * m)], m) == [F(3 * m - 1)] * m)
        check(f"family key-lemma hypothesis m={m}", all(3 * m - 1 < 3 * p[k] for k in range(2 * m)))
        bs = branches(p, m) if m <= 4 else [lowest_index(p, m)]
        for s in bs:
            check(f"family loads after 2m jobs m={m}", loads_of(p[:2 * m], s[:2 * m], m) == [F(3 * m - 1)] * m)
            check(f"family LPT makespan 4m-1 m={m}", makespan(p, s, m) == 4 * m - 1)
        idx = [ol_index(m, i) for i in range(n)]
        check(f"order map bijective m={m}", sorted(idx) == list(range(n)))
        q = [p[idx[i]] for i in range(n)]
        sched = tuple(ol_machine(m, i) for i in range(n))
        check(f"explicit order is a list schedule m={m}", is_list_schedule(q, sched, m))
        check(f"explicit order makespan 3m m={m}", makespan(q, sched, m) == 3 * m)
        for s in (branches(q, m) if m <= 4 else []):
            check(f"explicit order every branch 3m m={m}", makespan(q, s, m) == 3 * m)
        if m <= 3:
            check(f"family brute-force optimum m={m}", opt(p, m) == 3 * m)
    print("Graham's family: m = 1..10 (every branch to m = 4)")


# ---------------------------------------------------------------- the unit-job family

def unit_jobs(m):
    return [F(1)] * (m * (m - 1)) + [F(m)]


def tau1(m, j):
    return (j % (m - 1)) if j < m * (m - 1) else m - 1


def unit_family():
    for m in range(1, 9):
        p = unit_jobs(m)
        n = m * (m - 1) + 1
        check(f"units optimal assignment m={m}", makespan(p, [tau1(m, j) for j in range(n)], m) == m)
        bs = branches(p, m) if m <= 4 else [lowest_index(p, m)]
        for s in bs:
            check(f"units loads after units m={m}", loads_of(p[:-1], s[:-1], m) == [F(m - 1)] * m)
            check(f"units list makespan 2m-1 m={m}", makespan(p, s, m) == 2 * m - 1)
        if m <= 3:
            check(f"units brute-force optimum m={m}", opt(p, m) == m)
    print("the unit-job family: m = 1..8 (every branch to m = 4)")


def remark():
    p = [F(x) for x in (9, 5, 5, 4, 4, 4)]
    cs = {makespan(p, s, 3) for s in branches(p, 3)}
    check("(9,5,5,4,4,4): every LPT branch has makespan 13", cs == {13})
    check("(9,5,5,4,4,4): the optimum is 12", opt(p, 3) == 12)
    print("(9, 5, 5, 4, 4, 4) on three machines: LPT 13 on every branch, optimum 12")


if __name__ == "__main__":
    sweep()
    random_instances()
    graham_family()
    unit_family()
    remark()
    print(f"{CHECKS} checks, {len(FAILS)} failures")
    print("VERDICT: PASS" if not FAILS else "VERDICT: FAIL")
    sys.exit(0 if not FAILS else 1)
