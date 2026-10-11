# The proofs, with the Lean names

The definitions are in `GrahamLPT/Defs.lean`, identical to those of `Challenge.lean`. Each Challenge theorem is the
`_internal` theorem of the same name in the module named in VERIFICATION.md, restated in `Solution.lean`. Write
`L_k := loadBefore p σ k (σ k)`, the load of job `k`'s machine from the jobs before `k`, which in a list schedule is the
least load before `k` (`IsListSchedule`); `C(σ) := makespan p σ`. The finite facts are replayed by `scripts/check_lpt.py`.

1. **The ground floor** (`GrahamLPT/Basic.lean`). `loadBefore` at `0` is `0` and grows by `p k` on `σ k` at step `k`
   (`bs_loadBefore_zero`, `bs_loadBefore_succ`); at or beyond `n` it is the load (`bs_loadBefore_of_le`); the loads before
   `k` sum to the lengths of the jobs before `k` and the loads to the total (`bs_sum_loadBefore`, `bs_sum_load`, by
   `Finset.sum_fiberwise`); for nonnegative lengths `loadBefore` is nonnegative, monotone in the cutoff and at most the load
   (`bs_loadBefore_nonneg`, `bs_loadBefore_mono`, `bs_loadBefore_le_load`); a machine with no job has load `0`
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
10. **The third is sharp** (`Counter.lean`). For `9, 5, 5, 4, 4, 4` on three machines the assignment `0, 1, 2, 1, 2, 0`
   is a list schedule (the eighteen inequalities by `fin_cases` and `norm_num`), hence an LPT schedule with `π = 1`, and
   its loads are `13, 9, 9` (`nine_five_four_lpt_thirteen`). Every assignment has makespan at least `12`: if the job `9`
   shares its machine the load is at least `13`; otherwise the three `4`s either share one machine (`12`) or two of them
   share a machine and the third sits on another, and then a `5` on the first gives `13` or both `5`s on the second give
   `14` (`cx_twelve_le_makespan`); the assignment `0, 1, 1, 2, 2, 2` has makespan `12` (`nine_five_four_optMakespan`).
   Every job is at least `12/3`, so the instance is the sharpness witness (`lpt_third_le_not_optimal`).
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
