# Graham's bounds for list scheduling and LPT on identical machines: 2 − 1/m, 4/3 − 1/(3m) and their tight instances

`n` jobs of nonnegative real lengths `p : Fin n → ℝ` are run without interruption on `m ≥ 1` identical machines. An
assignment `σ : Fin n → Fin m` loads machine `i` with `Σ_{σ j = i} p j`; its makespan is the largest load;
`optMakespan m p` is the least makespan over all `m^n` assignments. A *list schedule* (`IsListSchedule`, in the index
order) gives each job a machine whose load from the earlier jobs is least, under any tie-breaking; an *LPT schedule*
(`IsLPTSchedule`) is a list schedule of the jobs in some nonincreasing order of length (R. L. Graham, *Bounds for
certain multiprocessing anomalies*, Bell System Tech. J. 45 (1966) 1563–1581; *Bounds on multiprocessing timing
anomalies*, SIAM J. Appl. Math. 17 (1969) 416–429; both restated with their examples in his survey *Bounds on
multiprocessing anomalies and related packing algorithms*, AFIPS Spring Joint Computer Conference (1972) 205–217).
Graham's rule gives a free processor the longest remaining task, a task wanted by several simultaneously free
processors going to the lower-indexed one; the makespan does not depend on the tie-breaking, so every statement
quantifies over every tie-breaking.

[Challenge.lean](Challenge.lean) states nine definitions and forty-one theorems; [Solution.lean](Solution.lean)
proves them, kernel-only; the table in [VERIFICATION.md](VERIFICATION.md) names each:

- **list scheduling** (Graham 1966, his Theorem for the same number of processors and no precedence constraints, whose
  proof bounds a list schedule by the average load plus `1 − 1/m` of the longest task): every list schedule `σ` and
  every assignment `τ` satisfy `m · C(σ) ≤ (2m − 1) · C(τ)`, so `C(σ) ≤ (2 − 1/m) · optMakespan`
  (`listSchedule_bound`, `listSchedule_le_optMakespan`); the `m(m − 1)` unit jobs followed by one job of length `m`
  (Graham's example for his theorem on scheduling the `k` largest tasks optimally first, at `k = 0`, as his 1972
  survey restates it on p. 209; Lenstra–Shmoys, *Elements of Scheduling*, Chapter 9, p. 188) have optimum `m`, and
  every list schedule of them in that order has makespan `2m − 1` (`unitJobs_optMakespan`,
  `unitJobs_listSchedule_makespan`), so `2 − 1/m` is the least constant (`isLeast_listSchedule_ratio`);
- **LPT** (Graham 1969, Theorem 2; announced in the closing remarks of the 1966 paper): every LPT schedule `σ` and
  every assignment `τ` satisfy `3m · C(σ) ≤ (4m − 1) · C(τ)`, so `C(σ) ≤ (4/3 − 1/(3m)) · optMakespan` (`lpt_bound`,
  `lpt_le_optMakespan`); when every job is longer than a third of `C(τ)`, every LPT schedule is at least as good as
  `τ`, so LPT is optimal when every job exceeds a third of the optimum — the case of Graham's proof in which the last
  task exceeds a third of the optimum (Lenstra–Shmoys's case (ii), p. 189), stated as a theorem
  (`lpt_optimal_of_third_lt`, `lpt_eq_optMakespan_of_third_lt`); Graham's `2m + 1` jobs
  `2m − 1, 2m − 1, 2m − 2, 2m − 2, …, m + 1, m + 1, m, m, m` (his pp. 425–426) are in nonincreasing order, have optimum
  `3m`, attained by a list schedule in the order `2m − 1, …, m + 1, m, m, 2m − 1, …, m + 1, m` (the permutation
  `grahamOrder`: `grahamOrder_bijective`, `grahamJobs_grahamOrder`), and every LPT schedule of them has makespan
  `4m − 1`, for every `m ≥ 1` (`grahamJobs_antitone`, `grahamJobs_optMakespan`, `grahamJobs_exists_optimal_listSchedule`,
  `grahamJobs_lpt_makespan`), so `4/3 − 1/(3m)` is the least constant (`isLeast_lpt_ratio`);
- **the elementary facts:** list and LPT schedules exist, the optimum is at most every makespan and is attained, every
  load, every job and the average load are at most the makespan, and relabeling the jobs preserves the makespan
  (`exists_isListSchedule`, `exists_isLPTSchedule`, `optMakespan_le`, `exists_makespan_eq_optMakespan`,
  `load_le_makespan`, `le_makespan_of_nonneg`, `sum_le_mul_makespan`, `makespan_comp`);
- **the optimum over lists:** every assignment is matched or improved by a list schedule in some order, so Graham's
  `ω₀`, the least finishing time over all lists, equals the optimum over all assignments (`exists_listSchedule_le`,
  `isLeast_listSchedule_makespan`);
- **the third cannot be weakened:** on three machines the jobs `9, 5, 5, 4, 4, 4`, each at least a third of the
  optimum `12`, have an LPT schedule of makespan `13` (`nine_five_four_lpt_thirteen`, `nine_five_four_optMakespan`,
  `lpt_third_le_not_optimal`), so neither `n ≤ 2m` jobs nor a weak third makes LPT optimal (Graham's 1972 survey,
  Figure 16, prints J. H. Spencer's `6, 3, 3, 2, 2, 2` for the same purpose: decreasing list `7`, optimum `6`);
- **the position of a job on its machine:** in a list schedule of a nonincreasing `p`, the `(c + 1)`-th job `k` placed
  on a machine has `(c + 1) · p_k ≤ C(τ)` for every assignment `τ` (`lpt_job_position_le`; the property of Chen 1993,
  *A note on LPT scheduling*, as Della Croce–Scatamacchia 2020 restate it, Proposition 2; proved here by an invariant on
  pairs of machines), hence the Coffman–Sethi form: a machine attaining the makespan of an LPT schedule with `q` jobs
  gives `q·m · C(σ) ≤ ((q + 1)m − 1) · C(τ)` (`lpt_bound_of_card`; Coffman–Sethi 1976 as corrected by Chen 1993, as
  Della Croce–Scatamacchia 2020 restate it, Proposition 3; the literature states it for `q ≥ 3`, for `m ≥ 2` it is
  weaker than `lpt_bound` at `q ≤ 2`, and neither its attainment nor Chen's `4/3 − 1/(3(m − 1))` at `q = 2` is proved
  here). Chen's and Coffman–Sethi's papers were not read; their statements are taken from that survey;
- **the critical job:** for a job `k` whose completion time is the makespan of a list schedule of a nonincreasing `p`,
  the smaller of `C(σ)` and `3 p_k` is at most `C(τ)` for every `τ`, and `C(σ) ≤ 3 p_k` certifies that the schedule is
  optimal (`lpt_critical_min_le`, `lpt_eq_optMakespan_of_critical_third`); equality `3m · C(σ) = (4m − 1) · C(τ)` on
  `m ≥ 2` machines forces `3 p_k = C(τ)`, equal loads before `k`, every load of `τ` equal to `C(τ)` and no positive job
  after `k` (`lpt_eq_bound_structure`); and when another machine holds `q` jobs before `k` and `q + 2 ≤ m`,
  `q(m − 1) · C(σ) ≤ ((q + 1)(m − 1) − 1) · C(τ)` (`lpt_bound_of_other_card`; Della Croce–Scatamacchia 2020,
  Proposition 4, proved there by a linear program, here from Chen's property);
- **Graham's example is the only tight one** (G. Dósa, *Graham's example is the only tight one for P||Cmax*, Annales
  Univ. Sci. Budapest. Sect. Math. 47 (2004) 207–210, Theorem 2): every positive multiple of Graham's `2m + 1` jobs, in
  any order, attains the bound (`lpt_eq_bound_of_graham`); conversely, for a nonempty positive instance on `m ≥ 2` machines, a list
  schedule of it in nonincreasing order attains `3m · C(σ) = (4m − 1) · optMakespan` only when `n = 2m + 1` and the
  instance is a positive multiple of `grahamJobs m` (`graham_of_listSchedule_eq_bound`), and an LPT schedule of it in any
  order only when the instance is a positive multiple of Graham's jobs in some order (`graham_of_lpt_eq_bound`,
  `lpt_eq_bound_iff_graham`), so with any number of jobs other than `2m + 1` the inequality is strict
  (`lpt_lt_bound_of_card_ne`); proved by counting the jobs of each machine in the two schedules, not by Dósa's
  minimal-counterexample argument;
- **a fixed number of jobs:** for every `n ≥ 2m + 1`, `4/3 − 1/(3m)` is still the supremum of `C(σ)/optMakespan` over
  the LPT schedules of the positive instances with `n` jobs (`isLUB_lpt_ratio_of_card`; the proof approaches it with
  Graham's jobs followed by `n − 2m − 1` jobs of a common small length). Dósa's Remark 1 states a strict gap for
  every `n ≠ 2m + 1`; it can therefore hold at most for `n < 2m + 1`, which is not formalized here.

Lengths are nonnegative where a bound is stated (Graham 1969 takes positive lengths, 1966 nonnegative ones) and
positive in Dósa's theorem (a zero job appended to Graham's instance keeps the ratio; replayed, not formalized). The proof of the LPT bound is by
counting, not by his exchange argument: with `k` the job ending a heaviest machine, the average-load bound settles
`3 p_k ≤ C(τ)`, and otherwise a count of the jobs up to `k` — every machine of `τ` holds at most two of them, those at
least as long as the least load sit alone, each single-job machine of `σ` contributes one of them — shows that `k`'s
machine ends by `C(τ)` ([PROOF.md](PROOF.md)). Not claimed: Chen's `k = 2` bound; Graham's bound
`1 + (1 − 1/m)/(1 + ⌊k/m⌋)` for scheduling the `k` largest jobs optimally first; the supremum of the ratio for fewer
than `2m + 1` jobs; precedence constraints; any "first". The nearest formal work: the Isabelle AFP's
`Approximation_Algorithms` (Eßmann–Nipkow–Robillard–Sulejmani) proves a `3/2` bound for sorted greedy and `2` for
greedy; two Lean repositories (AshishKumar4/armada, coproduct-opensource/nucleus) prove `m · C ≤ Σ p + (m − 1) · p_max`
over lists of naturals; fbz321/LLM-FOR-SCHEDULING names the LPT ratio as a stub. No code is shared with any of them.

## Verifying

Lean `v4.35.0-rc2` with Mathlib at the same tag (pinned by `lake-manifest.json`). `python scripts/verify.py` runs the
pins, the source guard and its controls, the definition and statement checks, the standard-library replay
(`scripts/check_lpt.py`: every list schedule of a small exhaustive sweep and of random instances, as separate
tie-breaking branches, against the brute-force optimum; the key lemma; both families for `m` up to 10 and 8; the
critical job's certificates; Dósa's theorem on integer boxes; the families for a fixed number of jobs; 889,121 checks,
also under `python -O`), the metadata check, the build with the axiom audit (`Test/Axioms.lean` rejects any axiom
beyond `propext`, `Classical.choice`, `Quot.sound`), the module-resolution check, the `pp.all` elaboration checks of
the definitions, of every constant named under them (none module-private) and of the theorem types, and Palomar's
core-notation audit, and ends with `VERIFY: PASS`
(`--skip-build` leaves out the Lean steps and ends with `VERIFY (source/replay only)`, which does not check the proofs).
[PROOF.md](PROOF.md) gives the proofs with the Lean names; [DISCLOSURE.md](DISCLOSURE.md) says how the repository was made.

License: [MIT](LICENSE) for the Lean files and scripts; `scripts/core_notation_audit.lean` is Palomar's, under its MIT
licence ([LICENSES/PalomarSubmission-MIT.txt](LICENSES/PalomarSubmission-MIT.txt)). The papers are cited, not copied.
