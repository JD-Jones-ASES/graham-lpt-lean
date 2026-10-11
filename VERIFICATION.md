# Verification

All twenty-two statements of Challenge.lean have proofs. The local build, the axiom audit, the source guard and its
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

## What is checked

- **The build.** `lake build` of `GrahamLPT`, `Challenge`, `Solution` and `Test` at Lean `v4.35.0-rc2`, Mathlib
  `065356127b1dc0016f66b7283ce0ce2c4055aa55`; every file has a `module` header; the lakefile sets no options.
- **The axiom audit.** `Test/Axioms.lean` walks every constant of the environment named under `GrahamLPT.`,
  `_private.GrahamLPT.` and `_private.Solution.` (151 constants at the final commit, floor 120) and fails on
  any axiom beyond `propext`, `Classical.choice`, `Quot.sound`; no `native_decide`, no `decide +kernel`.
- **The source guard** (`scripts/check-source.py`, exercised by `scripts/check_source_guard.py`): no `sorry`, `axiom`,
  `native_decide`, `implemented_by`, `extern`, `set_option` or debug option outside comments and strings in the
  development, the Solution and the Test; no control bytes in the scripts.
- **Statements.** `scripts/check_definitions.py` compares every definition block of Challenge.lean with
  `GrahamLPT/Defs.lean` character for character and the imports; `scripts/check_statements.py` compares every theorem
  header of Challenge.lean with Solution.lean; verify.py prints every definition with `pp.all` from both modules and
  requires identical output, prints every compared theorem's type from the Challenge and from the Solution and requires
  identical output, and runs Palomar's `core_notation_audit.lean` on every compared declaration (30 rows: the
  twenty-two theorems and the eight definitions, exit 0).
- **The replay.** `scripts/check_lpt.py` (standard library only, exact rationals, 651,683 checks, `VERDICT: PASS`,
  also under `python -O`): every list schedule of every nonincreasing instance of a small exhaustive sweep and of random
  rational instances, as separate tie-breaking branches, against the brute-force optimum — the bounds `m·C_LS ≤
  (2m − 1)·C_OPT` (every order) and `3m·C_LPT ≤ (4m − 1)·C_OPT`, the ratio `7/6` attained at `m = 2`, and the key lemma
  for every job and every assignment; Graham's family for `m = 1..10` (the sum `3m²`, the pairing of makespan `3m`,
  the pairing of the first `2m` jobs with loads `3m − 1`, every load `3m − 1` after `2m` jobs and makespan `4m − 1` on
  every branch, the explicit order whose list schedule has makespan `3m`, the position map as a bijection); the
  unit-job family for `m = 1..8`; the brute-force optima of both families for `m ≤ 3`; the instance `(9, 5, 5, 4, 4, 4)`.
- **Metadata.** `formalization.yaml` parses, its title is within 300 characters, its `status.main_results` and
  `alignment` list the compared theorems in `comparator.json`'s order with every status `proved`, and it validates
  against schema v0.4 when `jsonschema` is installed; `comparator.json` lists no definition holes and no original-proof
  source is declared.
- **Module resolution.** `scripts/check_module_resolution.py` (under `lake env`) checks that `Challenge` and `Solution`
  resolve to this repository's files first on `LEAN_SRC_PATH`.

## What is not checked here

The statements' faithfulness to Graham's papers is argued in `formalization.yaml` (fidelity) and PROOF.md, not checked
mechanically. The equality of Graham's optimum over lists with the optimum over assignments in general (the entry
proves it for his instance only), the Coffman–Sethi refinement and anything about precedence constraints are outside the
formal scope.
