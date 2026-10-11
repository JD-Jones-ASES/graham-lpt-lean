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
5. **The unit-job family** (`TightList.lean`). *[filled after the lane's report]*
6. **Graham's family** (`TightLPT.lean`). *[filled after the lane's report]*
7. **The optimum of Graham's family as a list schedule** (`OptList.lean`). *[filled after the lane's report]*
8. **The least constants** (`Ratio.lean`). Membership of `2 − 1/m` in the set of valid constants is `listSchedule_bound`
   divided by `m`; for any constant `c` in the set, the unit-job family with a list schedule (`exists_isListSchedule`) and an
   optimal `τ` gives `2m − 1 ≤ c · m` (`isLeast_listSchedule_ratio`). Likewise `4/3 − 1/(3m)` with `lpt_bound`, and
   Graham's family with an LPT schedule (`exists_isLPTSchedule`) and an optimal `τ`: `4m − 1 ≤ c · 3m` (`isLeast_lpt_ratio`).
