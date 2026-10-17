#!/usr/bin/env python3
"""Standard-library replay of the finite facts behind the compared statements of Challenge.lean (the
finder/checker split: the Lean development is the trust chain, this script a second implementation). Exact
rationals; nothing imported beyond fractions, itertools, random and sys. Every schedule is computed from the
definitions as Challenge.lean states them: a list schedule gives each job a machine of least load among the earlier
jobs, and every tie-breaking is enumerated as a separate branch; the optimum is the minimum over all m^n
assignments. Checks: the bounds m*C_LS <= (2m - 1)*C_OPT (every order, every branch) and 3m*C_LPT <= (4m - 1)*C_OPT
(the sorted order, every branch) on every nonincreasing instance of a small exhaustive sweep and on random rational
instances, with the ratio 7/6 attained at m = 2; the key lemma (every branch, every job k, every assignment tau of
the sweep; one assignment drawn per job and branch on the random instances); Graham's family 2m-1, 2m-1, ..., m+1,
m+1, m, m, m for m = 1..10 (the sum 3m^2, the pairing of makespan 3m, the first-2m pairing of loads 3m - 1, every load
3m - 1 after 2m jobs and makespan 4m - 1 on every branch for m <= 4 and on the lowest-index branch for m = 5..10, the
explicit order whose list schedule has makespan 3m, the position-to-index map as a bijection); the unit-job family
for m = 1..8 (the assignment of makespan m, every load m - 1 after the units and makespan 2m - 1 on every branch for
m <= 4 and on the lowest-index branch for m = 5..8); the brute-force optima of both families for m <= 3; the instance
(9, 5, 5, 4, 4, 4) on three machines, whose LPT makespan 13 exceeds the optimum 12 with every job at least a third of
12 (the explicit list schedule 0, 1, 2, 1, 2, 0 and the assignment 0, 1, 1, 2, 2, 2); Chen's property (c + 1) p_k <=
OPT for the (c + 1)-th job placed on a machine and the Coffman-Sethi form q m C <= ((q + 1) m - 1) OPT for a machine
with q jobs attaining the makespan, on every branch of the sweep and of random instances; the optimum over lists (the
least makespan over every order and every branch equals the optimum) on the sweep; the critical job's certificates
min(C, 3 p_k) <= OPT and C <= 3 p_k => C = OPT, the equality structure and the other-machine bound q (m - 1) C <=
((q + 1)(m - 1) - 1) OPT, on every branch of the sweep (every assignment tau for n <= 4) and of random instances with
up to five machines, with a dynamic-programming optimum checked against brute force; Dosa's theorem on the integer
boxes m = 2 (n <= 7, lengths <= 6) and m = 3 (n <= 8, lengths <= 5): equality 3m C = (4m - 1) OPT on some branch iff
on every branch iff the instance is a positive multiple of Graham's 2m + 1 jobs, the counting proof's structure at
every optimal assignment, the integer scale, a zero job appended; the families for a fixed number of jobs (Graham's
jobs then r small jobs: LPT 4m - 1 on every branch, optimum 3m + ceil(r/m) eps; a times Graham's jobs then r unit
jobs: LPT max((4m - 1) a, 3ma + ceil(r/m)), optimum 3ma + ceil(r/m)) for m = 2..4; the five-machine instance 90, 90,
80, 80, 70, 70, 60, 60, 50, 50, 50, 1 (LPT 190 on every branch, optimum 151); and negative controls for the
other-machine bound's hypotheses. Ends with VERDICT: PASS or VERDICT: FAIL; no check uses assert; exit status 0 on
PASS only.

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


def graham_order(m, i):
    """The job at position i of the order 2m-1, ..., m+1, m, m, 2m-1, ..., m+1, m; mirrors the Challenge definition grahamOrder."""
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
        idx = [graham_order(m, i) for i in range(n)]
        check(f"order map bijective m={m}", sorted(idx) == list(range(n)))
        q = [p[idx[i]] for i in range(n)]
        check(f"order lengths closed form m={m}",
              q == [F(2 * m - 1 - i) if i < m - 1 else F(m) if i <= m else F(3 * m - i) if i < 2 * m else F(m)
                    for i in range(n)])
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
    sched = (0, 1, 2, 1, 2, 0)
    check("(9,5,5,4,4,4): 0,1,2,1,2,0 is a list schedule", is_list_schedule(p, sched, 3))
    check("(9,5,5,4,4,4): its loads are 13, 9, 9", loads_of(p, sched, 3) == [F(13), F(9), F(9)])
    check("(9,5,5,4,4,4): 0,1,1,2,2,2 has makespan 12", makespan(p, (0, 1, 1, 2, 2, 2), 3) == 12)
    check("(9,5,5,4,4,4): every job is at least a third of 12", all(12 <= 3 * x for x in p))
    print("(9, 5, 5, 4, 4, 4) on three machines: LPT 13 on every branch, optimum 12")


# ---------------------------------------------------------------- Chen's property, the Coffman-Sethi form, the optimum over lists

def position_and_card(p, sigma, m):
    """Every LPT branch of a sorted p: (c + 1) p_k <= OPT for the (c + 1)-th job k on its machine, and
    q m C <= ((q + 1) m - 1) OPT for every machine with q jobs attaining the makespan C."""
    c_opt = opt(p, m)
    count = [0] * m
    for k in range(len(p)):
        count[sigma[k]] += 1
        check(f"Chen's property m={m} p={p} s={sigma} k={k}", count[sigma[k]] * p[k] <= c_opt)
    loads = loads_of(p, sigma, m)
    c = max(loads)
    for i in range(m):
        if loads[i] == c:
            q = count[i]
            check(f"Coffman-Sethi form m={m} p={p} s={sigma} i={i}", q * m * c <= ((q + 1) * m - 1) * c_opt)


def lifted():
    sizes = {1: 4, 2: 5, 3: 4}
    for m in (1, 2, 3):
        for n in range(1, sizes[m] + 1):
            for raw in product(range(0, 5), repeat=n):
                if any(raw[j] < raw[j + 1] for j in range(n - 1)):
                    continue
                p = [F(x) for x in raw]
                for s in branches(p, m):
                    position_and_card(p, s, m)
                # the optimum over lists: the least makespan over every order and every branch is the optimum
                best = min(makespan([p[j] for j in perm], s, m)
                           for perm in set(permutations(range(n))) for s in branches([p[j] for j in perm], m))
                check(f"optimum over lists m={m} p={raw}", best == opt(p, m))
    for _ in range(150):
        m = random.randint(1, 4)
        n = random.randint(1, 6)
        p = sorted([F(random.randint(0, 30), random.randint(1, 3)) for _ in range(n)], reverse=True)
        for s in branches(p, m):
            position_and_card(p, s, m)
    print("Chen's property, the Coffman-Sethi form and the optimum over lists replayed on the sweep and random instances")


# ---------------------------------------------------------------- the critical job, Dosa's theorem, the fixed job count

def opt_states(p, m):
    """The optimum by dynamic programming over sorted load vectors: every assignment is represented by the multiset of
    its loads, and adding a job to either of two equal loads gives the same multiset."""
    states = {tuple([F(0)] * m)}
    for x in p:
        new = set()
        for st in states:
            for i in range(m):
                if i > 0 and st[i] == st[i - 1]:
                    continue
                loads = list(st)
                loads[i] += x
                new.add(tuple(sorted(loads)))
        states = new
    return min(max(st) for st in states)


def certificates(p, sigma, m, c_opt, taus=()):
    """Every critical job k (completion = makespan C) of a list schedule of a sorted p: min(C, 3 p_k) <= OPT (and
    <= C(tau) for every tau given); C <= 3 p_k forces C = OPT; the other-machine bound q (m - 1) C <= ((q + 1)(m - 1) - 1)
    OPT for a machine i != sigma_k with q jobs before k when q + 2 <= m; and, when 3m C = (4m - 1) C(tau), the forced
    structure: 3 p_k = C(tau), every load before k equal, every tau-load equal to C(tau), no job after k."""
    n = len(p)
    loads = loads_of(p, sigma, m)
    c = max(loads)
    count = [0] * m
    for k in range(n):
        before = loads_of(p[:k], sigma[:k], m)
        if before[sigma[k]] + p[k] == c:
            check(f"critical min m={m} p={p} s={sigma} k={k}", min(c, 3 * p[k]) <= c_opt)
            for tau in taus:
                check(f"critical min vs tau m={m} p={p} s={sigma} k={k} tau={tau}", min(c, 3 * p[k]) <= makespan(p, tau, m))
            if c <= 3 * p[k]:
                check(f"observed third m={m} p={p} s={sigma} k={k}", c == c_opt)
            for i in range(m):
                if i != sigma[k] and count[i] + 2 <= m:
                    q = count[i]
                    check(f"other-machine bound m={m} p={p} s={sigma} k={k} i={i}",
                          q * (m - 1) * c <= ((q + 1) * (m - 1) - 1) * c_opt)
            if m >= 2:
                for tau in taus:
                    T = makespan(p, tau, m)
                    if 3 * m * c == (4 * m - 1) * T:
                        tl = loads_of(p, tau, m)
                        check(f"equality structure m={m} p={p} s={sigma} k={k} tau={tau}",
                              3 * p[k] == T and all(b == before[sigma[k]] for b in before)
                              and all(x == T for x in tl) and all(p[j] == 0 for j in range(k + 1, n)))
        count[sigma[k]] += 1


def is_graham_multiple(raw, m):
    if len(raw) != 2 * m + 1 or raw[-1] <= 0:
        return False
    a = F(raw[-1], m)
    return [F(x) for x in raw] == [a * g for g in graham_jobs(m)]


def dosa_structure(p, sigma, tau, m):
    """At an equality instance: the facts the counting proof of Dosa's theorem rests on."""
    n = len(p)
    k = n - 1
    t = p[k]
    T = makespan(p, tau, m)
    A = loads_of(p[:k], sigma[:k], m)[sigma[k]]
    d = t / m
    check(f"Dosa: T = 3t, A = 3t - t/m m={m} p={p}", T == 3 * t and A == 3 * t - d)
    fibers = [[j for j in range(k) if sigma[j] == i] for i in range(m)]
    check(f"Dosa: two jobs per machine before k, sum A m={m} p={p} s={sigma}",
          all(len(f) == 2 and sum(p[j] for j in f) == A for f in fibers))
    tfibers = [[j for j in range(n) if tau[j] == i] for i in range(m)]
    check(f"Dosa: tau-machines are pairs of sum 3t or triples of t m={m} p={p} tau={tau}",
          all((len(f) == 2 and sum(p[j] for j in f) == 3 * t) or (len(f) == 3 and all(p[j] == t for j in f))
              for f in tfibers))
    check(f"Dosa: every job in [t, 2t - t/m] m={m} p={p}", all(t <= p[j] <= 2 * t - d for j in range(n)))
    values = set(p) | {A - x for x in p} | {3 * t - x for x in p}
    c = lambda x: sum(1 for j in range(n) if p[j] == x)
    cp = lambda x: sum(1 for j in range(k) if p[j] == x)
    check(f"Dosa: count symmetry under the sigma-pairing m={m} p={p}", all(cp(x) == cp(A - x) for x in values))
    check(f"Dosa: count symmetry under the tau-pairing m={m} p={p}",
          all(c(x) == c(3 * t - x) for x in values if x != t and x != 2 * t))
    check(f"Dosa: two jobs of each length t + i t/m before k m={m} p={p}", all(cp(t + i * d) == 2 for i in range(m)))


def dosa_sweep():
    """Every nonincreasing positive integer instance of the boxes, every LPT branch, the optimum: equality
    3m C = (4m - 1) OPT holds on some branch iff on every branch iff the instance is a positive multiple of Graham's
    2m + 1 jobs; in particular the inequality is strict for every n != 2m + 1; at every equality instance and every
    optimal tau the structure of the counting proof holds."""
    from itertools import combinations_with_replacement
    boxes = {2: (7, 6), 3: (8, 5)}
    found = {}
    for m, (nmax, vmax) in boxes.items():
        found[m] = []
        for n in range(1, nmax + 1):
            for raw in combinations_with_replacement(range(vmax, 0, -1), n):
                p = [F(x) for x in raw]
                c_opt = opt_states(p, m)
                bs = branches(p, m)
                eqs = [3 * m * makespan(p, s, m) == (4 * m - 1) * c_opt for s in bs]
                graham = is_graham_multiple(raw, m)
                check(f"Dosa: equality iff Graham multiple m={m} p={raw}", any(eqs) == graham)
                check(f"Dosa: every branch agrees m={m} p={raw}", all(eqs) == any(eqs))
                if n != 2 * m + 1:
                    check(f"strict for n != 2m + 1 m={m} p={raw}", not any(eqs))
                if graham:
                    found[m].append(raw)
                    opts = [tau for tau in product(range(m), repeat=n) if makespan(p, tau, m) == c_opt]
                    for s in bs:
                        for tau in opts:
                            dosa_structure(p, s, tau, m)
                    # an integer equality instance is an integer multiple of Graham's (its scale is p_n / m)
                    check(f"Dosa: integer scale m={m} p={raw}", F(raw[-1], m).denominator == 1)
                    # a zero job appended keeps the ratio: the positive-length hypothesis is needed
                    q = p + [F(0)]
                    check(f"Dosa: a zero job appended keeps equality m={m} p={raw}",
                          all(3 * m * makespan(q, s, m) == (4 * m - 1) * c_opt for s in branches(q, m))
                          and opt_states(q, m) == c_opt)
    check("Dosa: the equality instances of the boxes", found == {2: [(6, 6, 4, 4, 4), (3, 3, 2, 2, 2)],
                                                                  3: [(5, 5, 4, 4, 3, 3, 3)]})
    print("Dosa's theorem: equality exactly at", {m: [tuple(int(x) for x in r) for r in v] for m, v in found.items()})


def critical_sweep():
    """The certificates and the equality structure on the nonnegative sweep (every branch, every assignment tau for
    n <= 4), the DP optimum against the brute-force optimum, and the other-machine bound on random instances with
    up to five machines."""
    sizes = {1: 4, 2: 5, 3: 4}
    for m in (1, 2, 3):
        for n in range(1, sizes[m] + 1):
            for raw in product(range(0, 5), repeat=n):
                if any(raw[j] < raw[j + 1] for j in range(n - 1)):
                    continue
                p = [F(x) for x in raw]
                c_opt = opt(p, m)
                check(f"DP optimum m={m} p={raw}", opt_states(p, m) == c_opt)
                taus = list(product(range(m), repeat=n)) if n <= 4 else ()
                for s in branches(p, m):
                    certificates(p, s, m, c_opt, taus)
    for _ in range(150):
        m = random.randint(2, 5)
        n = random.randint(1, 8)
        p = sorted([F(random.randint(0, 30), random.randint(1, 3)) for _ in range(n)], reverse=True)
        c_opt = opt_states(p, m)
        for s in branches(p, m):
            certificates(p, s, m, c_opt)
    print("the critical job's certificates and the other-machine bound replayed on the sweep and random instances")


def fixed_count():
    """Graham's jobs followed by r jobs of a common length eps < 1/r: every LPT branch has makespan 4m - 1 and the
    optimum is 3m + ceil(r/m) eps (so the ratio tends to 4/3 - 1/(3m) with eps, for every fixed n = 2m + 1 + r); a
    times Graham's jobs followed by r unit jobs: LPT max((4m - 1) a, 3ma + ceil(r/m)) on every branch, optimum
    3ma + ceil(r/m); the five-machine instance 90, 90, 80, 80, 70, 70, 60, 60, 50, 50, 50, 1: LPT 190 on every
    branch, optimum 151, and 190/151 exceeds 4/3 - 1/(3(m - 1)) = 5/4."""
    for m in range(2, 5):
        for r in range(1, 5):
            eps = F(1, 2 * r)
            p = graham_jobs(m) + [eps] * r
            check(f"small tail antitone m={m} r={r}", all(p[j] >= p[j + 1] for j in range(len(p) - 1)))
            check(f"small tail LPT 4m - 1 on every branch m={m} r={r}",
                  all(makespan(p, s, m) == 4 * m - 1 for s in branches(p, m)))
            check(f"small tail optimum m={m} r={r}", opt_states(p, m) == 3 * m + (-(-r // m)) * eps)
    for m in range(2, 5):
        for a in range(1, 4):
            for r in range(0, 9):
                p = [a * g for g in graham_jobs(m)] + [F(1)] * r
                bs = branches(p, m) if r <= 3 else [lowest_index(p, m)]
                want = max((4 * m - 1) * a, 3 * m * a + (-(-r // m)))
                check(f"unit padding LPT m={m} a={a} r={r}", all(makespan(p, s, m) == want for s in bs))
                check(f"unit padding optimum m={m} a={a} r={r}", opt_states(p, m) == 3 * m * a + (-(-r // m)))
    p = [F(x) for x in (90, 90, 80, 80, 70, 70, 60, 60, 50, 50, 50, 1)]
    check("five machines: LPT 190 on every branch", all(makespan(p, s, 5) == 190 for s in branches(p, 5)))
    check("five machines: optimum 151", opt_states(p, 5) == 151)
    check("five machines: 190/151 > 5/4", F(190, 151) > F(5, 4))
    # negative controls for the other-machine bound's hypotheses: with the count taken over all jobs of the other
    # machine (the unit job lands there after the critical job) the inequality fails here at q = 3, m = 5 = q + 2 ...
    s = lowest_index(p, 5)
    counts = [sum(1 for j in range(len(p)) if s[j] == i) for i in range(5)]
    check("five machines: the critical job is job 10 on the lowest-index branch",
          loads_of(p[:10], s[:10], 5)[s[10]] + p[10] == 190 and s[11] != s[10] and counts[s[11]] == 3)
    check("five machines: the bound fails with the count taken after the critical job", not (3 * 4 * 190 <= 15 * 151))
    # ... and on Graham's 3, 3, 2, 2, 2 with two machines, q = 1 = m - 1 (q + 2 <= m fails) the bound would read C <= OPT
    g = graham_jobs(2)
    check("two machines: q + 2 <= m is needed", all(makespan(g, s, 2) == 7 for s in branches(g, 2)) and opt(g, 2) == 6
          and all(sum(1 for j in range(4) if s[j] != s[4]) >= 1 for s in branches(g, 2)) and not (1 * 1 * 7 <= (2 * 1 - 1) * 6))
    print("the fixed-count families, the five-machine instance and the negative controls replayed")


if __name__ == "__main__":
    sweep()
    random_instances()
    graham_family()
    unit_family()
    remark()
    lifted()
    critical_sweep()
    dosa_sweep()
    fixed_count()
    print(f"{CHECKS} checks, {len(FAILS)} failures")
    print("VERDICT: PASS" if not FAILS else "VERDICT: FAIL")
    sys.exit(0 if not FAILS else 1)
