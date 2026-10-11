# Verification

All thirty-nine statements of Challenge.lean have proofs. The local build, the axiom audit, the source guard and its
controls, the definition and statement checks, the standard-library replay of the finite facts behind the compared
statements, the metadata check, the module-resolution check, the elaboration checks and Palomar's core-notation audit of
the statements pass; `python scripts/verify.py` runs them all and ends with `VERIFY: PASS`. The checks below were last run
on the tree of the final commit (the counts are printed by verify.py); a build log is evidence for that tree only.
Theorems are numbered as in `comparator.json`, which is also their order in Challenge.lean. `comparator.json` lists no
`definition_names`: a name there is a definition hole whose value the Solution supplies; the eight definitions here are
fully specified in the Challenge, so the comparator checks the Solution's values against them.

## Formal scope

| # | Statement | Proved in |
| --- | --- | --- |
| 1 | `exists_isListSchedule` — A list schedule exists (the lowest-index tie-breaking, for instance) | GrahamLPT/Basic.lean |
| 2 | `exists_isLPTSchedule` — An LPT schedule exists | GrahamLPT/Basic.lean |
| 3 | `optMakespan_le` — The optimal makespan is at most the makespan of every assignment | GrahamLPT/Basic.lean |
| 4 | `exists_makespan_eq_optMakespan` — The optimal makespan is attained | GrahamLPT/Basic.lean |
| 5 | `load_le_makespan` — Every machine load is at most the makespan | GrahamLPT/Basic.lean |
| 6 | `le_makespan_of_nonneg` — For nonnegative lengths every job is at most the makespan | GrahamLPT/Basic.lean |
| 7 | `sum_le_mul_makespan` — The total length is at most `m` times the makespan | GrahamLPT/Basic.lean |
| 8 | `makespan_comp` — Relabeling the jobs by a permutation changes neither the loads nor the makespan | GrahamLPT/Basic.lean |
| 9 | `listSchedule_bound` — Graham's bound for list scheduling: for nonnegative lengths, every list schedule `σ` and every assignment `τ` satisfy `m · C(σ) ≤ (2m − 1) · C(τ)` | GrahamLPT/ListBound.lean |
| 10 | `listSchedule_le_optMakespan` — Every list schedule is within the factor `2 − 1/m` of the optimum | GrahamLPT/ListBound.lean |
| 11 | `unitJobs_optMakespan` — The `m(m − 1)` unit jobs with one job of length `m` have optimal makespan `m` | GrahamLPT/TightList.lean |
| 12 | `unitJobs_listSchedule_makespan` — Every list schedule of the unit jobs followed by the job of length `m` has makespan `2m − 1` | GrahamLPT/TightList.lean |
| 13 | `isLeast_listSchedule_ratio` — `2 − 1/m` is the least constant `c` with `C(σ) ≤ c · C(τ)` for every list schedule `σ` of every nonnegative instance on `m` machines and every assignment `τ` | GrahamLPT/Ratio.lean |
| 14 | `lpt_bound` — Graham's bound for LPT: for nonnegative lengths, every LPT schedule `σ` and every assignment `τ` satisfy `3m · C(σ) ≤ (4m − 1) · C(τ)` | GrahamLPT/LPTBound.lean |
| 15 | `lpt_le_optMakespan` — Every LPT schedule is within the factor `4/3 − 1/(3m)` of the optimum | GrahamLPT/LPTBound.lean |
| 16 | `lpt_optimal_of_third_lt` — When every job is longer than a third of the makespan of `τ`, every LPT schedule is at least as good as `τ` | GrahamLPT/Key.lean |
| 17 | `lpt_eq_optMakespan_of_third_lt` — LPT is optimal when every job is longer than a third of the optimal makespan | GrahamLPT/Key.lean |
| 18 | `grahamJobs_antitone` — Graham's instance is listed in nonincreasing order | GrahamLPT/TightLPT.lean |
| 19 | `grahamJobs_optMakespan` — Graham's instance has optimal makespan `3m` | GrahamLPT/TightLPT.lean |
| 20 | `grahamJobs_exists_optimal_listSchedule` — The optimum `3m` of Graham's instance is attained by a list schedule, in the order `2m − 1, …, m + 1, m, m, 2m − 1, …, m + 1, m` | GrahamLPT/OptList.lean |
| 21 | `grahamJobs_lpt_makespan` — Every LPT schedule of Graham's instance has makespan `4m − 1`: the bound `4/3 − 1/(3m)` is attained for every `m` | GrahamLPT/TightLPT.lean |
| 22 | `isLeast_lpt_ratio` — `4/3 − 1/(3m)` is the least constant `c` with `C(σ) ≤ c · C(τ)` for every LPT schedule `σ` of every nonnegative instance on `m` machines and every assignment `τ` | GrahamLPT/Ratio.lean |
| 23 | `exists_listSchedule_le` — Graham's `ω₀` is attained: for nonnegative lengths, every assignment `τ` is matched or improved by a list schedule in some order (the jobs listed by their start times when each machine of `τ` runs its jobs in index order) | GrahamLPT/ListOptimum.lean |
| 24 | `isLeast_listSchedule_makespan` — The optimal makespan is the least makespan over the list schedules in all orders: Graham's `ω₀`, the least finishing time over all lists, equals the optimum over all assignments | GrahamLPT/ListOptimum.lean |
| 25 | `nine_five_four_lpt_thirteen` — On three machines the assignment `0, 1, 2, 1, 2, 0` of the jobs `9, 5, 5, 4, 4, 4` is an LPT schedule (the identity order, lowest-index ties) of makespan `13` | GrahamLPT/Counter.lean |
| 26 | `nine_five_four_optMakespan` — The jobs `9, 5, 5, 4, 4, 4` have optimal makespan `12` on three machines (`9 | 5, 5 | 4, 4, 4`) | GrahamLPT/Counter.lean |
| 27 | `lpt_third_le_not_optimal` — The strict third in `lpt_optimal_of_third_lt` cannot be weakened to `≤`, and `n ≤ 2m` jobs do not make LPT optimal: an instance on three machines whose six jobs are each at least a third of the optimal makespan, with an LPT schedule longer than the optimum | GrahamLPT/Counter.lean |
| 28 | `lpt_job_position_le` — In a list schedule of a nonincreasing `p`, a job `k` that is the `(c + 1)`-th job placed on its machine satisfies `(c + 1) · p k ≤ C(τ)` for every assignment `τ` (the property Chen 1993 derives the bounds from, as Della Croce and Scatamacchia restate it; proved here by an invariant on pairs of machines) | GrahamLPT/CoffmanSethi.lean |
| 29 | `lpt_bound_of_card` — The Coffman–Sethi form of the LPT bound: if a machine `i` attaining the makespan of an LPT schedule holds `q` jobs, then `q·m · C(σ) ≤ ((q + 1)m − 1) · C(τ)` for every assignment `τ` (Coffman–Sethi 1976 as corrected by Chen 1993, as Della Croce and Scatamacchia restate it; the literature states it for `q ≥ 3`; for `m ≥ 2` it is weaker than `lpt_bound` at `q ≤ 2`, and its attainment is not proved here) | GrahamLPT/CoffmanSethi.lean |
| 30 | `lpt_critical_min_le` — The critical job's certificate: in a list schedule of a nonincreasing `p`, for a job `k` whose completion time is the makespan, the smaller of `C(σ)` and `3 p_k` is at most `C(τ)` for every assignment `τ` (the key lemma read as a lower bound on every comparison schedule) | GrahamLPT/Certificates.lean |
| 31 | `lpt_eq_optMakespan_of_critical_third` — The observed-third certificate: when a critical job `k` is at least a third of the makespan it completes, the list schedule is optimal (`lpt_eq_optMakespan_of_third_lt` asks every job to exceed a third of the unknown optimum) | GrahamLPT/Certificates.lean |
| 32 | `lpt_eq_bound_structure` — Equality in Graham's LPT bound against `τ` on `m ≥ 2` machines, with `k` a critical job, forces the four inequalities of its proof to be equalities: `3 p_k = C(τ)`, every machine of `σ` carries the least load before `k`, every machine of `τ` carries exactly `C(τ)`, and every job after `k` has length `0` | GrahamLPT/Certificates.lean |
| 33 | `lpt_bound_of_other_card` — Della Croce–Scatamacchia's Proposition 4, from Chen's property: if a machine `i` other than the critical job's holds at least `q` jobs before the critical job `k`, and `q + 2 ≤ m`, then `q(m − 1) · C(σ) ≤ ((q + 1)(m − 1) − 1) · C(τ)` for every assignment `τ` | GrahamLPT/Certificates.lean |
| 34 | `lpt_eq_bound_of_graham` — Every positive multiple of Graham's instance, in any order, attains the bound: every LPT schedule has makespan `(4m − 1) a` against the optimum `3m a` | GrahamLPT/GrahamScaled.lean |
| 35 | `graham_of_listSchedule_eq_bound` — Dósa's theorem (2004), the sorted form: a list schedule of a nonempty nonincreasing positive `p` on `m ≥ 2` machines attains Graham's bound against the optimum only for Graham's instance: then `n = 2m + 1` and `p` is a positive multiple of `grahamJobs m` | GrahamLPT/Equality.lean |
| 36 | `graham_of_lpt_eq_bound` — Dósa's theorem for LPT schedules: on `m ≥ 2` machines, an LPT schedule of a nonempty positive instance attains Graham's bound against the optimum only when the instance is a positive multiple of Graham's `2m + 1` jobs in some order | GrahamLPT/LPTForm.lean |
| 37 | `lpt_eq_bound_iff_graham` — Graham's example is the only tight one (Dósa 2004): for a nonempty positive instance on `m ≥ 2` machines, some LPT schedule attains Graham's bound `3m · C(σ) = (4m − 1) · optMakespan` if and only if the instance is a positive multiple of Graham's `2m + 1` jobs in some order (and then every LPT schedule attains it, `lpt_eq_bound_of_graham`) | GrahamLPT/LPTForm.lean |
| 38 | `lpt_lt_bound_of_card_ne` — With any number of jobs other than `2m + 1`, no LPT schedule of a nonempty positive instance on `m ≥ 2` machines attains Graham's bound: the inequality is strict | GrahamLPT/LPTForm.lean |
| 39 | `isLUB_lpt_ratio_of_card` — For every fixed number `n ≥ 2m + 1` of jobs, Graham's constant `4/3 − 1/(3m)` is still the supremum of `C(σ)/optMakespan` over the LPT schedules of the positive instances with `n` jobs: Graham's jobs followed by `n − 2m − 1` jobs of a common small length approach it (and, for `m ≥ 2`, attain it only at `n = 2m + 1`, `lpt_lt_bound_of_card_ne`) | GrahamLPT/FixedCount.lean |

## What is checked

- **The build.** `lake build` of `GrahamLPT`, `Challenge`, `Solution` and `Test` at Lean `v4.35.0-rc2`, Mathlib
  `065356127b1dc0016f66b7283ce0ce2c4055aa55`; every file has a `module` header; the lakefile sets no options.
- **The axiom audit.** `Test/Axioms.lean` walks every constant of the environment named under `GrahamLPT.`,
  `_private.GrahamLPT.` and `_private.Solution.` (273 constants at the final commit, floor 250) and fails on
  any axiom beyond `propext`, `Classical.choice`, `Quot.sound`; no `native_decide`, no `decide +kernel`.
- **The source guard** (`scripts/check-source.py`, exercised by `scripts/check_source_guard.py`): no `sorry`, `axiom`,
  `native_decide`, `implemented_by`, `extern`, `set_option` or debug option outside comments and strings in the
  development, the Solution and the Test; no control bytes in the scripts.
- **Statements.** `scripts/check_definitions.py` compares every definition block of Challenge.lean with
  `GrahamLPT/Defs.lean` character for character and the imports; `scripts/check_statements.py` compares every theorem
  header of Challenge.lean with Solution.lean; verify.py prints every definition with `pp.all` from both modules and
  requires identical output, prints every compared theorem's type from the Challenge and from the Solution and requires
  identical output, and runs Palomar's `core_notation_audit.lean` on every compared declaration (47 rows: the
  thirty-nine theorems and the eight definitions, exit 0).
- **The replay.** `scripts/check_lpt.py` (standard library only, exact rationals, 889,111 checks, `VERDICT: PASS`,
  also under `python -O`): every list schedule of every nonincreasing instance of a small exhaustive sweep and of random
  rational instances, as separate tie-breaking branches, against the brute-force optimum — the bounds `m·C_LS ≤
  (2m − 1)·C_OPT` (every order) and `3m·C_LPT ≤ (4m − 1)·C_OPT`, the ratio `7/6` attained at `m = 2`, and the key lemma
  for every job and every assignment on the sweep (one assignment drawn per job and branch on the random instances);
  Graham's family for `m = 1..10` (the sum `3m²`, the pairing of makespan `3m`, the pairing of the first `2m` jobs with
  loads `3m − 1`, every load `3m − 1` after `2m` jobs and makespan `4m − 1` on every branch for `m ≤ 4` and on the
  lowest-index branch for `m = 5..10`, the explicit order whose list schedule has makespan `3m`, the position map as a
  bijection); the unit-job family for `m = 1..8` (every branch for `m ≤ 4`, the lowest-index branch beyond); the
  brute-force optima of both families for `m ≤ 3`; the instance `(9, 5, 5, 4, 4, 4)` with its explicit list schedule
  and optimal assignment; Chen's property and the Coffman–Sethi form on every branch of the sweep and of random
  instances; the optimum over lists on the sweep; the critical job's certificates, the equality structure and the
  other-machine bound on every branch of the sweep (every assignment for `n ≤ 4`) and of random instances with up to
  five machines, with a dynamic-programming optimum checked against brute force; Dósa's theorem on the integer boxes
  `m = 2` (`n ≤ 7`, lengths `≤ 6`) and `m = 3` (`n ≤ 8`, lengths `≤ 5`): equality on some branch iff on every branch
  iff the instance is a positive multiple of Graham's `2m + 1` jobs, the counting proof's structure at every optimal
  assignment, the integer scale, a zero job appended; the families for a fixed number of jobs (Graham's jobs then `r`
  small jobs: LPT `4m − 1` on every branch, optimum `3m + ⌈r/m⌉ε`; `a` times Graham's jobs then `r` unit jobs: LPT
  `max((4m − 1)a, 3ma + ⌈r/m⌉)`, optimum `3ma + ⌈r/m⌉`) for `m = 2..4`; the five-machine instance
  `90, 90, 80, 80, 70, 70, 60, 60, 50, 50, 50, 1` (LPT `190` on every branch, optimum `151`); and negative controls for
  the other-machine bound's hypotheses.
- **Metadata.** `formalization.yaml` parses, its title is within 300 characters, its `status.main_results` and
  `alignment` list the compared theorems in `comparator.json`'s order with every status `proved`, and its
  `responsible_maintainers` is nonempty; the schema check runs only when `scripts/formalization.schema.json` is present
  (it is not shipped) and then needs `jsonschema`; `comparator.json` lists no definition holes and no original-proof
  source is declared.
- **Module resolution.** `scripts/check_module_resolution.py` (under `lake env`) checks that `Challenge` and `Solution`
  resolve to this repository's files first on `LEAN_SRC_PATH`.

## What is not checked here

The statements' faithfulness to the papers is argued in `formalization.yaml` (fidelity) and PROOF.md, not checked
mechanically. Chen's `k = 2` bound `4/3 − 1/(3(m − 1))`, the supremum of the LPT ratio for fewer than `2m + 1` jobs,
Dósa's theorem for nonnegative lengths and anything about precedence constraints are outside the formal scope.
