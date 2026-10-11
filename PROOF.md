# The proofs, with the Lean names

The definitions are in `GrahamLPT/Defs.lean`, identical to those of `Challenge.lean`. Each Challenge theorem is the
`_internal` theorem of the same name in the module named in VERIFICATION.md, restated in `Solution.lean`. Write
`L_k := loadBefore p σ k (σ k)`, the load of job `k`'s machine from the jobs before `k`, which in a list schedule is the
least load before `k` (`IsListSchedule`); `C(σ) := makespan p σ`. The finite facts are replayed by `scripts/check_lpt.py`.

1. **The ground floor** (`GrahamLPT/Basic.lean`). `loadBefore` at `0` is `0` and grows by `p k` on `σ k` at step `k`
   (`bs_loadBefore_zero`, `bs_loadBefore_succ`); at or beyond `n` it is the load (`bs_loadBefore_of_le`); the loads before
   `k` sum to the lengths of the jobs before `k` and the loads to the total (`bs_sum_loadBefore`, `bs_sum_load`, by
   `Finset.sum_fiberwise`); for nonnegative lengths `loadBefore` is nonnegative, monotone in the cutoff and at most the load
   (`bs_loadBefore_mono`, `bs_loadBefore_le_load`); a machine with no job has load `0`
   (`bs_load_eq_zero`, `bs_loadBefore_eq_zero`) and a machine with a job has a last job `k`, its load being
   `loadBefore p σ k i + p k` (`bs_exists_last_job_before` by `Finset.exists_max_image` on the fiber, then
   `bs_exists_last_job` at the cutoff `n`). In a list schedule `m · L_k ≤ Σ_{j<k} p_j`, the least of `m` loads being at
   most their sum (`bs_mul_loadBefore_le`). The makespan is the `sup'` of the loads: every load is at most it
   (`load_le_makespan`, `Finset.le_sup'`), `makespan ≤ c` iff every load is (`bs_makespan_le_iff`), some load attains it
   (`bs_exists_load_eq_makespan`), hence `p j ≤ C(σ)` for nonnegative lengths (`le_makespan_of_nonneg`, the single term
   `p j` of the fiber of `σ j`) and `Σ p ≤ m · C(σ)` (`sum_le_mul_makespan`); the optimum is the `inf'` over all
   assignments, so it is at most every makespan (`optMakespan_le`) and attained (`exists_makespan_eq_optMakespan`).
   Relabeling the jobs by a permutation changes no load (`bs_load_comp`: `load` as `∑ j, if σ j = i then p j else 0`
   reindexed by `Equiv.sum_comp`), hence no makespan (`makespan_comp`). A list schedule exists: the greedy loads
   `bs_gLoads k` are built by recursion on `k`, adding the `k`-th length to a minimizer `bs_argmin` of the current loads
   (`Classical.choose` of `Finset.exists_min_image`), the assignment `σ j := bs_argmin (bs_gLoads j)` reproduces them
   (`bs_loadBefore_greedy`), and the minimizer property is `IsListSchedule` (`exists_isListSchedule`); an LPT schedule
   exists by sorting (`π := Tuple.sort (fun j => -p j)`, `Tuple.monotone_sort`, so `p ∘ π` is antitone) and taking a list
   schedule `σ'` of `p ∘ π` with `σ := σ' ∘ π.symm` (`exists_isLPTSchedule`).
2. **Graham 1966** (`ListBound.lean`). For a list schedule and any job `k`, `m(L_k + p_k) ≤ Σ p + (m − 1) p_k`
   (`lb_mul_le`: `m · L_k ≤ Σ_{j<k} p_j` and `Σ_{j<k} p_j + p_k ≤ Σ p`, `bs_sum_filter_add_le`). Take a heaviest machine;
   if it has no job, `C(σ) = 0` and the right side is nonnegative; otherwise its last job `k` gives `C(σ) = L_k + p_k`, and
   `Σ p ≤ m · C(τ)`, `p_k ≤ C(τ)` give `m · C(σ) ≤ (2m − 1) · C(τ)` (`listSchedule_bound`); at an optimal `τ`, dividing by
   `m`, `C(σ) ≤ (2 − 1/m) · optMakespan` (`listSchedule_le_optMakespan`).
3. **The key lemma** (`Key.lean`). `p` nonincreasing and nonnegative, `σ` a list schedule, `τ` any assignment whose loads
   from the jobs of index `≤ k` are at most `T`, and `T < 3 p_k`: then `L_k + p_k ≤ T` (`key_lemma`). Suppose not. Every
   machine holds a job before `k` (else `L_k = 0` and `p_k ≤ T`, the single term of `τ k`'s fiber). No `τ`-machine holds
   three jobs of index `≤ k`: their lengths are `≥ p_k`, so three give `≥ 3 p_k > T` (`key_card_mul_le_sum`). Let `B` be
   the jobs of index `≤ k` with `p_j ≥ L_k`: such a `j` shares its `τ`-machine with no other job `j'` of index `≤ k`, since
   `p_j + p_{j'} ≥ L_k + p_k > T`; so `τ` is injective on `B`, and the `τ`-fibers of `B`'s machines within the jobs
   `≤ k` are singletons. Counting the jobs `≤ k` by `τ`-fibers: `k + 1 ≤ |B| + 2(m − |B|)`. Counting the jobs `< k` by
   `σ`-fibers, with `s` the machines holding exactly one of them: `k ≥ s + 2(m − s)`. A machine holding exactly one job
   `j` before `k` has `loadBefore p σ k i = p_j ≥ L_k`, so `j ∈ B`, and distinct machines give distinct jobs: `s ≤ |B|`.
   Together `k ≥ 2m − s ≥ 2m − |B| ≥ k + 1`. Consequences: when every job is longer than a third of `C(τ)`, every
   machine's load, `0` or `L_k + p_k` for its last job `k`, is at most `C(τ)` (`key_optimal_sorted`), and the LPT form
   follows by relabeling (`lpt_optimal_of_third_lt`); at an optimal `τ` this is equality (`lpt_eq_optMakespan_of_third_lt`).
4. **Graham 1969** (`LPTBound.lean`). For a list schedule of a nonincreasing `p`, take a heaviest machine; with no job
   the bound is trivial; otherwise `C(σ) = L_k + p_k` for its last job `k`. If `3 p_k ≤ C(τ)`: `m · L_k ≤ Σ_{j<k} p_j ≤
   Σ p − p_k ≤ m · C(τ) − p_k`, so `3m(L_k + p_k) ≤ 3m · C(τ) + 3(m − 1) p_k ≤ (4m − 1) · C(τ)`. If `C(τ) < 3 p_k`: the
   key lemma with `T := C(τ)` (every `τ`-load from the jobs `≤ k` is at most the full load, at most `C(τ)`) gives
   `C(σ) ≤ C(τ) ≤ ((4m − 1)/(3m)) · C(τ)` (`lb2_bound_sorted`). Relabeling gives `lpt_bound` for every LPT schedule;
   at an optimal `τ`, `C(σ) ≤ (4/3 − 1/(3m)) · optMakespan` (`lpt_le_optMakespan`).
5. **The unit-job family** (`TightList.lean`). `unitJobs m` is `1` below index `m(m − 1)` and `m` at it
   (`tl_unitJobs_apply_lt`, `tl_unitJobs_apply_last`). For a list schedule, the invariant `m · loadBefore k i ≤ k + m − 1`
   holds for `k ≤ m(m − 1)` by induction on `k` (`tl_loadBefore_le`: the job `k` is a unit job, it lands on a least load
   `L_k` with `m · L_k ≤ k`, and every other machine's load is unchanged); before `k ≤ m(m − 1)` every load is the
   cardinality of a fiber (`tl_loadBefore_eq_card`), so at `k = m(m − 1)` each load is an integer `c` with
   `m · c ≤ m(m − 1) + m − 1`, hence `c ≤ m − 1` (`tl_nat_le`), while the loads sum to `m(m − 1)`: every load is `m − 1`
   (`tl_loadBefore_units`, `Finset.sum_eq_sum_iff_of_le`). The last job, of length `m`, lands on a load `m − 1`, so some
   load is `2m − 1`; the bound `m · C ≤ (2m − 1) · m` at an assignment of makespan `m` gives the other inequality
   (`unitJobs_listSchedule_makespan`). That assignment sends unit job `j` to machine `⌊j/m⌋` and the long job to machine
   `m − 1`: machine `i < m − 1` carries the unit jobs with `⌊j/m⌋ = i`, at most `m` of them, and machine `m − 1` only the
   long job (`tl_exists_makespan_eq`); every assignment has makespan at least `m`, the long job's length
   (`tl_le_makespan`), so the optimum is `m` (`unitJobs_optMakespan`).
6. **Graham's family** (`TightLPT.lean`). `grahamJobs m j = 2m − 1 − ⌊j/2⌋` for `j < 2m` and `m` at `j = 2m`
   (`tg_grahamJobs_apply_lt`, `tg_grahamJobs_apply_last`), so every length lies in `[m, 2m − 1]` (`tg_le_grahamJobs`) and
   the sequence is nonincreasing (`grahamJobs_antitone`); the sum is `3m²` (`tg_grahamJobs_sum`, from
   `Σ_{j<2k} (c − ⌊j/2⌋) = 2kc − k(k − 1)` by induction, `tg_sum_range_aux`). The pairs `j, 2m − 1 − j` of the first `2m`
   jobs sum to `3m − 1` and the pairs `j, 2m − 3 − j` of the first `2m − 2` jobs to `3m` (`tg_pair`, `tg_pair'`, by the
   parity of `j`). The pairing `τ₀` (`j ↦ min(j, 2m − 3 − j)` for `j < 2m − 2`, the three jobs of length `m` on the last
   machine) has every load `3m` (`tg_exists_opt`: the fibers are explicit pairs and one triple), and `3m² ≤ m · C(τ)` gives
   `3m ≤ C(τ)` for every `τ` (`tg_le_makespan`), so the optimum is `3m` (`grahamJobs_optMakespan`). The pairing `τ'`
   (`j ↦ min(j, 2m − 1 − j)`) of the first `2m` jobs has every load `3m − 1` before the cutoff `2m`
   (`tg_exists_prefix_pairing`); since `3m − 1 < 3m ≤ 3 p_k` for every `k < 2m`, the key lemma with `T = 3m − 1` bounds
   every machine's load before `2m` by `3m − 1`, and these loads sum to `3m² − m`, so every one is `3m − 1`
   (`tg_loadBefore_two_mul`). Hence every list schedule of the family in its own order has makespan `4m − 1`: the last job
   lands on a load `3m − 1`, and the LPT bound at `τ₀` gives `3m · C ≤ (4m − 1) · 3m` (`tg_listSchedule_makespan`). For an
   LPT schedule, the relabeling `π` has `grahamJobs m ∘ π` nonincreasing, hence equal to `grahamJobs m`
   (`tg_comp_eq`, `Tuple.unique_antitone`), so `σ ∘ π` is a list schedule of the family in its own order and
   `makespan_comp` transfers `4m − 1` (`grahamJobs_lpt_makespan`).
7. **The optimum of Graham's family as a list schedule** (`OptList.lean`). The order
   `2m − 1, …, m + 1, m, m, 2m − 1, …, m + 1, m` is the relabeling `ol_index` (position `i < m − 1` to index `2i`,
   positions `m − 1, m` to `2m − 2, 2m − 1`, position `m + 1 + a` to `2a + 1`, position `2m` to `2m`), a bijection
   (`ol_index_bijective`, injective by cases). The schedule `ol_machine` sends position `i < m − 1` to machine `i`,
   positions `m − 1`, `m` and `2m` to the last machine, and position `m + 1 + a` to machine `m − 2 − a`. The load of
   machine `b` before position `k` is an explicit sum over a fiber of at most three positions (`ol_loadBefore`: for
   `b < m − 1` the positions `b` and `2m − 1 − b`, carrying `2m − 1 − b` and `m + 1 + b`; for the last machine the
   positions `m − 1`, `m`, `2m`, carrying `m` each), computed as a natural number `ol_loadN`; at every step the machine
   chosen has the least such load (`ol_listN`, a case split closed by `omega`), so `ol_machine` is a list schedule of the
   reordered family (`ol_isListSchedule`), and every final load is `3m` (`ol_load`, `ol_makespan`). With
   `π := Equiv.ofBijective (ol_index m)` and `σ := ol_machine m ∘ π.symm`, `makespan_comp` gives the Challenge
   statement (`grahamJobs_exists_optimal_listSchedule`).
8. **The least constants** (`Ratio.lean`). Membership of `2 − 1/m` in the set of valid constants is `listSchedule_bound`
   divided by `m`; for any constant `c` in the set, the unit-job family with a list schedule (`exists_isListSchedule`) and an
   optimal `τ` gives `2m − 1 ≤ c · m` (`isLeast_listSchedule_ratio`). Likewise `4/3 − 1/(3m)` with `lpt_bound`, and
   Graham's family with an LPT schedule (`exists_isLPTSchedule`) and an optimal `τ`: `4m − 1 ≤ c · 3m` (`isLeast_lpt_ratio`).
9. **The optimum over lists** (`ListOptimum.lean`). Given an assignment `τ`, run each of its machines without idle time in
   index order: job `j` starts at `s j := loadBefore p τ j (τ j)` and ends at `s j + p j ≤ C(τ)`, and two jobs of one
   machine do not overlap. Sort the jobs by start time (`π := Tuple.sort s`) and take any list schedule `σ'` of `p ∘ π`.
   In an order by nondecreasing start times, a list schedule starts every job `k` of positive length no later than `s k`
   (`lo_core`, by strong induction): otherwise every machine's load before `k` exceeds `s k`, so each machine of the list
   schedule carries an earlier job still running at time `s k` (`lo_exists_cover`); by induction those jobs started no
   later than their own `τ`-start times, so under `τ` they are all running at time `s k` as well — `m` distinct jobs on
   `m` machines, one of them on `τ k`'s machine, overlapping `k`, which is impossible. Hence every load of the list
   schedule is at most `C(τ)` (`lo_makespan_le`), and `makespan_comp` transfers to `σ := σ' ∘ π.symm`
   (`exists_listSchedule_le`); at an optimal `τ` this makes `optMakespan` the least makespan over the list schedules of all
   orders (`isLeast_listSchedule_makespan`).
10. **The third cannot be weakened** (`Counter.lean`). For `9, 5, 5, 4, 4, 4` on three machines the assignment `0, 1, 2, 1, 2, 0`
   is a list schedule (the eighteen inequalities by `fin_cases` and `norm_num`), hence an LPT schedule with `π = 1`, and
   its loads are `13, 9, 9` (`nine_five_four_lpt_thirteen`). Every assignment has makespan at least `12`: if the job `9`
   shares its machine the load is at least `13`; otherwise the three `4`s either share one machine (`12`) or two of them
   share a machine and the third sits on another, and then a `5` on the first gives `13` or both `5`s on the second give
   `14` (`cx_twelve_le_makespan`); the assignment `0, 1, 1, 2, 2, 2` has makespan `12` (`nine_five_four_optMakespan`).
   Every job is at least `12/3`, so the instance is the witness (`lpt_third_le_not_optimal`).
11. **Chen's property and the Coffman–Sethi form** (`CoffmanSethi.lean`). Fix the job `k` of positive length `P := p k`
   in a list schedule of a nonincreasing `p`; every earlier job is at least `P`. Weigh a job `x` by `⌊x/P⌋` (`cs_fl` sums
   the weights of a machine's jobs before a cutoff, `cs_cnt` counts them). For two machines `h, g`, the restriction of the
   schedule to them is again a list schedule, and the invariant `cs_Inv` holds along it: with `D` the load difference, `Φ`
   the weight of `h` minus the count of `g`, and `y` the last job placed, `⌊D/P⌋ ≤ Φ` when `D ≥ 0`, and `−1 ≤ Φ` with
   `⌊(D + y)/P⌋ − 1 ≤ Φ` when `D < 0` (`cs_inv_all`, by the two placement cases `cs_inv_istep`, `cs_inv_hstep`; the
   `y`-dependent clause is what a plain floor potential lacks). Taking `g := σ k`, the least-loaded machine when `k` is
   placed, every machine weighs at least `c`, the number of jobs before `k` on `σ k` (`cs_cnt_le_fl_of_min`). If
   `C(τ) < (c + 1) P`, each `τ`-machine weighs at most `⌊load/P⌋ ≤ c`, so the jobs up to `k` weigh at most `mc`; but they
   weigh at least `mc + 1` (job `k` itself weighs `1`): contradiction, so `(c + 1) P ≤ C(τ)` (`cs_job_le`,
   `lpt_job_position_le`). For a machine `i` attaining the makespan with `k ≥ 1` jobs, its last job `q` is the `k`-th on
   it, so `k · p_q ≤ C(τ)`, and `m · C(σ) = m(L_q + p_q) ≤ Σ p + (m − 1) p_q ≤ m · C(τ) + (m − 1) C(τ)/k` gives
   `km · C(σ) ≤ ((k + 1)m − 1) · C(τ)` (`cs_bound`; `k = 0` is the empty machine); relabeling gives the LPT form
   (`lpt_bound_of_card`).
12. **The critical job** (`Certificates.lean`). Fix a list schedule `σ` of a nonincreasing nonnegative `p` and a job `k`
   whose completion `L_k + p_k` is the makespan. If `C(τ) < 3 p_k`, the key lemma with `T := C(τ)` (every `τ`-load from
   the jobs `≤ k` is at most `C(τ)`; `ct_key_le`) gives `C(σ) = L_k + p_k ≤ C(τ)`; otherwise `3 p_k ≤ C(τ)`: so
   `min(C(σ), 3 p_k) ≤ C(τ)` (`lpt_critical_min_le`), and when `C(σ) ≤ 3 p_k` an optimal `τ` gives
   `C(σ) ≤ optMakespan ≤ C(σ)` (`lpt_eq_optMakespan_of_critical_third`). Equality `3m · C(σ) = (4m − 1) · C(τ)` with
   `m ≥ 2` (`lpt_eq_bound_structure`): if `C(τ) = 0` then `C(σ) = 0`, every job is `0` and every load vanishes; if
   `C(τ) > 0` then `C(σ) > C(τ)`, so the key lemma gives `3 p_k ≤ C(τ)`, and the chain `m · L_k ≤ Σ_{j<k} p_j ≤ Σ p − p_k
   ≤ m · C(τ) − p_k` gives `3m · C(σ) ≤ 3m · C(τ) + 3(m − 1) p_k`, whence `C(τ) ≤ 3 p_k` (`ct_eq_scalar`); so
   `3 p_k = C(τ)` and the chain is tight: the loads before `k`, each at least `L_k`, sum to `m · L_k`, so all equal `L_k`;
   the loads of `τ`, each at most `C(τ)`, sum to `m · C(τ)`, so all equal `C(τ)`; and the jobs after `k` sum to `0`
   (`Finset.sum_eq_zero_iff_of_nonneg`). The other-machine bound (`lpt_bound_of_other_card`): write `s := L_k`,
   `P := p_k`; a machine `i ≠ σ k` holding at least `q ≥ 1` jobs before `k` has a last one among them, `j₀`, which is
   at least the `q`-th job on `i`, so Chen's property gives `q · P ≤ q · p_{j₀} ≤ C(τ)` (`p_k ≤ p_{j₀}`); the loads sum
   to `Σ p ≤ m · C(τ)` and are at least `s + P` on `σ k`, `q · P` on `i` (`key_card_mul_le_sum`) and `s` elsewhere, so
   `(m − 1) s + (q + 1) P ≤ m · C(τ)`, i.e. `(m − 1) C(σ) ≤ m · C(τ) + (m − q − 2) P`; multiplying by `q` and using
   `(m − q − 2) q P ≤ (m − q − 2) C(τ)` (the one use of `q + 2 ≤ m`) gives `q (m − 1) C(σ) ≤ ((q + 1)(m − 1) − 1) C(τ)`
   (`ct_other_scalar`); `q = 0` reads `0 ≤ (m − 2) C(τ)`.
13. **Dósa's theorem** (`GrahamScaled.lean`, `Equality.lean`, `LPTForm.lean`). *Scaling and relabeling.* Multiplying
   every length by `a ≥ 0` multiplies every load, the makespan and the optimum by `a` (`gs_loadBefore_smul`,
   `gs_load_smul`, `gs_makespan_smul`, `gs_optMakespan_smul`), and for `a > 0` preserves the list-schedule property
   (`gs_isListSchedule_smul_iff`); relabeling the jobs by a permutation preserves the optimum (`gs_optMakespan_comp`:
   `σ ↦ σ ∘ π` permutes the assignments). *Sufficiency* (`lpt_eq_bound_of_graham`): an equivalence
   `e : Fin n ≃ Fin (2m + 1)` forces `n = 2m + 1`; with `p = a · grahamJobs m ∘ e` and `π` the sorting permutation of an
   LPT schedule `σ`, `grahamJobs m ∘ (e ∘ π) = (1/a)(p ∘ π)` is nonincreasing and `σ ∘ π` is a list schedule of it, so
   `σ ∘ e.symm` is an LPT schedule of `grahamJobs m`, of makespan `4m − 1` (`grahamJobs_lpt_makespan`); hence
   `C(σ) = a(4m − 1)` and `optMakespan = 3m · a`. *Necessity, the sorted form* (`graham_of_listSchedule_eq_bound`;
   `p` positive and nonincreasing, `σ` a list schedule, `m ≥ 2`, `3m · C(σ) = (4m − 1) · optMakespan`). Take an optimal
   `τ`, `T := C(τ) > 0`, a heaviest machine of `σ` and its last job `k`, so that `C(σ) = L_k + p_k`. By 12, `3 p_k = T`,
   every load before `k` is `L_k`, every load of `τ` is `T`, and no positive job follows `k`: `k` is the last index.
   Write `t := p_k = T/3`, `δ := t/m`; the equality gives `L_k = 3t − δ =: A`. Every job before `k` is at least `t`;
   each machine of `σ` holds, among the jobs before `k`, at least one (`A > 0`), at most two (three would exceed `A`),
   and not exactly one (a single job of length `A` would sit alone on its `τ`-machine, whose load is `T > A`, since every
   other job exceeds `T − A = δ`): so exactly two, and `k = 2m`, `n = 2m + 1`. A job before `k` and its partner sum to
   `A`, so every job lies in `[t, 2t − δ]`; each machine of `τ` therefore holds two jobs summing to `3t` or three jobs
   of length `t`, and since `2m + 1` is odd some machine holds a triple. Counting the jobs of each length `x` before
   `k` (`c' x`) and overall (`c x = c' x + [x = t]`): the `σ`-pairs give `c' x = c' (A − x)` for every `x`, the
   `τ`-pairs give `c x = c (3t − x)` for `x ∉ {t, 2t}` (the triple contributes nothing there); along the chain
   `t + iδ ↦ 2t − iδ ↦ t + (i − 1)δ` these give `c' (t + iδ) = c' t` for `0 ≤ i < m`, with `c' t ≥ 2` from the triple
   and `m · c' t ≤ 2m` from the `m` disjoint fibers, so each is `2` and they exhaust the `2m` jobs: the lengths are
   `t` three times and `t + iδ` twice for `1 ≤ i < m`, the fiber counts of `δ · grahamJobs m`. Two nonincreasing
   functions on `Fin (2m + 1)` with the same fiber counts are equal (`List.ofFn` of each is sorted and the two are
   permutations of each other: `Fin.univ_val_map`, `Multiset.count_map`, `List.Perm.eq_of_sortedGE`), so
   `p = δ · grahamJobs m` with `a := δ = T/(3m)`. *The LPT form* (`graham_of_lpt_eq_bound`): the sorting permutation
   `π` transports the equality to `p ∘ π` (`makespan_comp`, `gs_optMakespan_comp`); the sorted form gives `a`,
   `h : n = 2m + 1` and `p (π j) = a · grahamJobs m (Fin.cast h j)`, and `e := π.symm.trans (finCongr h)`. The two-way
   statement (`lpt_eq_bound_iff_graham`) is this with `exists_isLPTSchedule` and sufficiency; for `n ≠ 2m + 1` equality
   is impossible, an equivalence `Fin n ≃ Fin (2m + 1)` forcing `n = 2m + 1`, so `lpt_bound` is strict
   (`lpt_lt_bound_of_card_ne`).
14. **A fixed number of jobs** (`FixedCount.lean`). `fc_jobs m n ε` is Graham's `2m + 1` jobs followed by `n − 2m − 1`
   jobs of length `ε` (`fc_len`), positive for `ε > 0` (`fc_jobs_pos`) and nonincreasing for `ε ≤ m` (`fc_antitone`).
   The pairs `j, 2m − 1 − j` of the first `2m` jobs sum to `3m − 1` (`fc_pair`) and those jobs to `3m² − m`
   (`fc_sum_lt`), so the pairing `j ↦ min(j, 2m − 1 − j)` has every load `3m − 1` before `2m` (`fc_exists_prefix_pairing`);
   for a list schedule in the family's order the key lemma at `T = 3m − 1 < 3m ≤ 3 p_k`, `k < 2m`, bounds every load
   before `2m` by `3m − 1`, and the sum forces equality (`fc_loadBefore_two_mul`), so the job `2m`, of length `m`, makes
   a load `4m − 1` and the makespan is at least `4m − 1` (`fc_le_makespan_listSchedule`); the sorting permutation of an
   LPT schedule leaves the lengths unchanged (`fc_comp_eq`, `Tuple.unique_antitone`), so every LPT schedule has makespan
   at least `4m − 1` (`fc_le_makespan_lpt`). The assignment pairing the first `2m − 2` jobs as `j ↦ min(j, 2m − 3 − j)`,
   the three jobs of length `m` together and the small jobs on one machine has makespan at most `3m + nε`
   (`fc_exists_opt`), so `optMakespan ≤ 3m + nε` (`fc_optMakespan_le`), and a positive instance has a positive optimum
   (`fc_optMakespan_pos`). Hence (`isLUB_lpt_ratio_of_card`): every ratio is at most `4/3 − 1/(3m)` (`lpt_le_optMakespan`);
   for `m = 1` every ratio is `1`; for `m ≥ 2` and `b < 4/3 − 1/(3m)`, a small `ε` makes `(4m − 1)/(3m + nε) > b`, and
   the family's ratio is at least that.
