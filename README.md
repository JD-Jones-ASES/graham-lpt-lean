# Graham's bounds for list scheduling and LPT on identical machines: `m·C_LS ≤ (2m − 1)·C_OPT` and `3m·C_LPT ≤ (4m − 1)·C_OPT` under every tie-breaking, both equality families for every `m`, and the optimality of LPT when every job exceeds a third of the optimum

`n` jobs of nonnegative real lengths `p : Fin n → ℝ` are run without interruption on `m ≥ 1` identical machines. An
assignment `σ : Fin n → Fin m` loads machine `i` with `Σ_{σ j = i} p j`; its makespan is the largest load;
`optMakespan m p` is the least makespan over all `m^n` assignments. A *list schedule* (`IsListSchedule`, in the index
order) gives each job a machine whose load from the earlier jobs is least, under any tie-breaking; an *LPT schedule*
(`IsLPTSchedule`) is a list schedule of the jobs in some nonincreasing order of length (R. L. Graham, *Bounds for
certain multiprocessing anomalies*, Bell System Tech. J. 45 (1966) 1563–1581; *Bounds on multiprocessing timing
anomalies*, SIAM J. Appl. Math. 17 (1969) 416–429).

[Challenge.lean](Challenge.lean) states eight definitions and twenty-two theorems; [Solution.lean](Solution.lean)
proves them, kernel-only; the table in [VERIFICATION.md](VERIFICATION.md) names each:

- **list scheduling** (Graham 1966, his Theorem with `n = n′` and no precedence constraints): every list schedule `σ`
  and every assignment `τ` satisfy `m · C(σ) ≤ (2m − 1) · C(τ)`, so `C(σ) ≤ (2 − 1/m) · optMakespan`
  (`listSchedule_bound`, `listSchedule_le_optMakespan`); the `m(m − 1)` unit jobs followed by one job of length `m`
  have optimum `m`, and every list schedule of them in that order has makespan `2m − 1` (`unitJobs_optMakespan`,
  `unitJobs_listSchedule_makespan`), so `2 − 1/m` is the least constant (`isLeast_listSchedule_ratio`);
- **LPT** (Graham 1969, Theorem 2; announced in the closing remarks of the 1966 paper): every LPT schedule `σ` and
  every assignment `τ` satisfy `3m · C(σ) ≤ (4m − 1) · C(τ)`, so `C(σ) ≤ (4/3 − 1/(3m)) · optMakespan` (`lpt_bound`,
  `lpt_le_optMakespan`); when every job is longer than a third of `C(τ)`, every LPT schedule is at least as good as
  `τ`, so LPT is optimal when every job exceeds a third of the optimum (`lpt_optimal_of_third_lt`,
  `lpt_eq_optMakespan_of_third_lt`); Graham's `2m + 1` jobs `2m − 1, 2m − 1, 2m − 2, 2m − 2, …, m + 1, m + 1, m, m, m`
  (his pp. 425–426) are in nonincreasing order, have optimum `3m`, attained by a list schedule in the order
  `2m − 1, …, m + 1, m, m, 2m − 1, …, m + 1, m`, and every LPT schedule of them has makespan `4m − 1`, for every
  `m ≥ 1` (`grahamJobs_antitone`, `grahamJobs_optMakespan`, `grahamJobs_exists_optimal_listSchedule`,
  `grahamJobs_lpt_makespan`), so `4/3 − 1/(3m)` is the least constant (`isLeast_lpt_ratio`);
- **the elementary facts:** list and LPT schedules exist, the optimum is at most every makespan and is attained, every
  load, every job and the average load are at most the makespan, and relabeling the jobs preserves the makespan
  (`exists_isListSchedule`, `exists_isLPTSchedule`, `optMakespan_le`, `exists_makespan_eq_optMakespan`,
  `load_le_makespan`, `le_makespan_of_nonneg`, `sum_le_mul_makespan`, `makespan_comp`).

Graham's `ω₀` is the least finishing time over all lists; `optMakespan` is the least over all assignments, which is at
most `ω₀`, so the bounds here are the stronger form, and for his instance the optimum `3m` is attained by a list. The
proof of the LPT bound is by counting, not by his exchange argument: with `k` the job ending a heaviest machine, the
average-load bound settles `3 p_k ≤ C(τ)`, and otherwise a count of the jobs up to `k` — every machine of `τ` holds at most
two of them, those at least as long as the least load sit alone, each single-job machine of `σ` contributes one of them —
shows that `k`'s machine ends by `C(τ)` ([PROOF.md](PROOF.md)). Not claimed: the equality `ω₀ = optMakespan` in general;
Coffman–Sethi's refinement; precedence constraints; any "first". The nearest formal work: the Isabelle AFP's
`Approximation_Algorithms` (Eßmann–Nipkow–Robillard–Sulejmani) proves a `3/2` bound for sorted greedy and `2` for
greedy; two Lean repositories (AshishKumar4/armada, coproduct-opensource/nucleus) prove `m · C ≤ Σ p + (m − 1) · p_max`
over lists of naturals; fbz321/LLM-FOR-SCHEDULING names the LPT ratio as a stub. No code is shared with any of them.

## Verifying

Lean `v4.35.0-rc2` with Mathlib at the same tag (pinned by `lake-manifest.json`). `python scripts/verify.py` runs the
pins, the source guard and its controls, the definition and statement checks, the standard-library replay
(`scripts/check_lpt.py`: every list schedule of a small exhaustive sweep and of random instances, as separate
tie-breaking branches, against the brute-force optimum; the key lemma; both families for `m` up to 10 and 8; 651,683
checks, also under `python -O`), the metadata check, the build with the axiom audit (`Test/Axioms.lean` rejects any
axiom beyond `propext`, `Classical.choice`, `Quot.sound`), the module-resolution check, the `pp.all` elaboration checks
of the definitions and of the theorem types, and Palomar's core-notation audit, and ends with `VERIFY: PASS`
(`--skip-build` leaves out the Lean steps and ends with `VERIFY (source/replay only)`, which does not check the proofs).
[PROOF.md](PROOF.md) gives the proofs with the Lean names; [DISCLOSURE.md](DISCLOSURE.md) says how the repository was made.

License: [MIT](LICENSE) for the Lean files and scripts; `scripts/core_notation_audit.lean` is Palomar's, under its MIT
licence ([LICENSES/PalomarSubmission-MIT.txt](LICENSES/PalomarSubmission-MIT.txt)). The papers are cited, not copied.
