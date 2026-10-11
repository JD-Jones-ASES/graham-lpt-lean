module

public import GrahamLPT.ListBound

/-!
# TightList

The unit-job family: optimum `m`, list-schedule makespan `2m − 1` (ARCH.md §5). Lane `tightlist`. Helpers carry the prefix `tl_`; the `_internal` twins of the Challenge theorems are closed in `Solution.lean`.
-/

@[expose] public section

namespace GrahamLPT

open Finset

theorem tl_unitJobs_apply_lt (m : ℕ) (j : Fin (m * (m - 1) + 1)) (h : (j : ℕ) < m * (m - 1)) :
    unitJobs m j = 1 := sorry

theorem tl_unitJobs_apply_last (m : ℕ) (j : Fin (m * (m - 1) + 1)) (h : m * (m - 1) ≤ (j : ℕ)) :
    unitJobs m j = m := sorry

theorem tl_unitJobs_nonneg (m : ℕ) (j : Fin (m * (m - 1) + 1)) : 0 ≤ unitJobs m j := sorry

/-- The invariant of a list schedule of the unit jobs: `m · loadBefore k i ≤ k + m − 1` for `k ≤ m(m − 1)`. -/
theorem tl_loadBefore_le (m : ℕ) [NeZero m] (σ : Fin (m * (m - 1) + 1) → Fin m)
    (hσ : IsListSchedule (unitJobs m) σ) (k : ℕ) (hk : k ≤ m * (m - 1)) (i : Fin m) :
    (m : ℝ) * loadBefore (unitJobs m) σ k i ≤ k + m - 1 := sorry

/-- Every load after the unit jobs is `m − 1`. -/
theorem tl_loadBefore_units (m : ℕ) [NeZero m] (σ : Fin (m * (m - 1) + 1) → Fin m)
    (hσ : IsListSchedule (unitJobs m) σ) (i : Fin m) :
    loadBefore (unitJobs m) σ (m * (m - 1)) i = m - 1 := sorry

/-- An assignment of makespan `m`: the unit jobs spread `m` per machine over `m − 1` machines, the long job alone. -/
theorem tl_exists_makespan_eq (m : ℕ) [NeZero m] :
    ∃ τ : Fin (m * (m - 1) + 1) → Fin m, makespan (unitJobs m) τ = m := sorry

theorem tl_le_makespan (m : ℕ) [NeZero m] (τ : Fin (m * (m - 1) + 1) → Fin m) :
    (m : ℝ) ≤ makespan (unitJobs m) τ := sorry

/-- The `m(m − 1)` unit jobs with one job of length `m` have optimal makespan `m`. -/
theorem unitJobs_optMakespan_internal (m : ℕ) [NeZero m] : optMakespan m (unitJobs m) = m := sorry

/-- Every list schedule of the unit jobs followed by the job of length `m` has makespan `2m − 1`. -/
theorem unitJobs_listSchedule_makespan_internal (m : ℕ) [NeZero m] (σ : Fin (m * (m - 1) + 1) → Fin m)
    (hσ : IsListSchedule (unitJobs m) σ) : makespan (unitJobs m) σ = 2 * m - 1 := sorry

end GrahamLPT
