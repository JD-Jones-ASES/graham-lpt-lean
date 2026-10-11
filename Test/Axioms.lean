module

import Solution
import Lean.Util.CollectAxioms

/-!
# Axiom audit

A module file importing `Solution` (not `Challenge.lean`). Walks every constant of the environment
whose name begins with `GrahamLPT.`, `_private.GrahamLPT.` or `_private.Solution.` (the public declarations of
this development; the private auxiliaries that Lean generates are not enumerated under the module
system, but `collectAxioms` reaches every private constant a public proof refers to, including a
private `axiom`), and collects the axioms each depends on. Anything outside `propext`,
`Classical.choice`, `Quot.sound` is reported with `logError`, which fails `lake build`. The audit
also fails if it matched fewer constants than the floor below (so a renamed namespace cannot make it
pass vacuously) or if any of the compared theorems is missing from the environment.
-/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut checked : Nat := 0
  let mut rejected : Nat := 0
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for (name, _) in env.constants.toList do
    let label := name.toString
    if label.startsWith "GrahamLPT." || label.startsWith "_private.GrahamLPT." ||
        label.startsWith "_private.Solution." then
      checked := checked + 1
      let axs ← collectAxioms name
      for ax in axs do
        unless allowed.contains ax do
          rejected := rejected + 1
          logError m!"Unexpected axiom dependency: {name} -> {ax}"
  unless checked ≥ 120 do
    logError m!"Axiom audit matched only {checked} project constants; expected at least 120"
  for n in [`GrahamLPT.exists_isListSchedule, `GrahamLPT.exists_isLPTSchedule,
      `GrahamLPT.optMakespan_le, `GrahamLPT.exists_makespan_eq_optMakespan,
      `GrahamLPT.load_le_makespan, `GrahamLPT.le_makespan_of_nonneg,
      `GrahamLPT.sum_le_mul_makespan, `GrahamLPT.makespan_comp, `GrahamLPT.listSchedule_bound,
      `GrahamLPT.listSchedule_le_optMakespan, `GrahamLPT.unitJobs_optMakespan,
      `GrahamLPT.unitJobs_listSchedule_makespan, `GrahamLPT.isLeast_listSchedule_ratio,
      `GrahamLPT.lpt_bound, `GrahamLPT.lpt_le_optMakespan, `GrahamLPT.lpt_optimal_of_third_lt,
      `GrahamLPT.lpt_eq_optMakespan_of_third_lt, `GrahamLPT.grahamJobs_antitone,
      `GrahamLPT.grahamJobs_optMakespan, `GrahamLPT.grahamJobs_exists_optimal_listSchedule,
      `GrahamLPT.grahamJobs_lpt_makespan, `GrahamLPT.isLeast_lpt_ratio,
      `GrahamLPT.exists_listSchedule_le, `GrahamLPT.isLeast_listSchedule_makespan,
      `GrahamLPT.nine_five_four_lpt_thirteen, `GrahamLPT.nine_five_four_optMakespan,
      `GrahamLPT.lpt_third_le_not_optimal, `GrahamLPT.lpt_job_position_le,
      `GrahamLPT.lpt_bound_of_card, `GrahamLPT.lpt_critical_min_le,
      `GrahamLPT.lpt_eq_optMakespan_of_critical_third, `GrahamLPT.lpt_eq_bound_structure,
      `GrahamLPT.lpt_bound_of_other_card, `GrahamLPT.lpt_eq_bound_of_graham,
      `GrahamLPT.graham_of_listSchedule_eq_bound, `GrahamLPT.graham_of_lpt_eq_bound,
      `GrahamLPT.lpt_eq_bound_iff_graham, `GrahamLPT.lpt_lt_bound_of_card_ne,
      `GrahamLPT.isLUB_lpt_ratio_of_card] do
    unless env.contains n do
      logError m!"Compared theorem is missing from the environment: {n}"
  logInfo m!"Audited {checked} project constants; unexpected axiom dependencies: {rejected}."
