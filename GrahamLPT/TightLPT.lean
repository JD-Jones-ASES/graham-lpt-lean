module

public import GrahamLPT.LPTBound

/-!
# TightLPT

Graham's family: optimum `3m`, LPT makespan `4m − 1` (ARCH.md §6). Lane `tightlpt`. Helpers carry the prefix `tg_`; the `_internal` twins of the Challenge theorems are closed in `Solution.lean`.
-/

@[expose] public section

namespace GrahamLPT

open Finset

theorem tg_grahamJobs_apply_lt (m : ℕ) (j : Fin (2 * m + 1)) (h : (j : ℕ) < 2 * m) :
    grahamJobs m j = 2 * (m : ℝ) - 1 - (((j : ℕ) / 2 : ℕ) : ℝ) := sorry

theorem tg_grahamJobs_apply_last (m : ℕ) (j : Fin (2 * m + 1)) (h : 2 * m ≤ (j : ℕ)) : grahamJobs m j = m := sorry

theorem tg_grahamJobs_nonneg (m : ℕ) (j : Fin (2 * m + 1)) : 0 ≤ grahamJobs m j := sorry

theorem tg_le_grahamJobs (m : ℕ) (j : Fin (2 * m + 1)) : (m : ℝ) ≤ grahamJobs m j := sorry

theorem tg_grahamJobs_le (m : ℕ) (j : Fin (2 * m + 1)) : grahamJobs m j ≤ 2 * m - 1 ∨ m = 0 := sorry

theorem tg_grahamJobs_sum (m : ℕ) : ∑ j, grahamJobs m j = 3 * (m : ℝ) ^ 2 := sorry

/-- The pairs `j, 2m − 1 − j` of the first `2m` jobs sum to `3m − 1`. -/
theorem tg_pair (m : ℕ) (j : Fin (2 * m + 1)) (h : (j : ℕ) < 2 * m) :
    grahamJobs m j + grahamJobs m ⟨2 * m - 1 - j, by omega⟩ = 3 * m - 1 := sorry

/-- The pairs `j, 2m − 3 − j` of the first `2m − 2` jobs sum to `3m`. -/
theorem tg_pair' (m : ℕ) (j : Fin (2 * m + 1)) (h : (j : ℕ) < 2 * m - 2) :
    grahamJobs m j + grahamJobs m ⟨2 * m - 3 - j, by omega⟩ = 3 * m := sorry

/-- The pairing `τ₀` (`j ↦ min (j, 2m − 3 − j)` for `j < 2m − 2`, the three jobs of length `m` on the last machine)
has every load `3m`. -/
theorem tg_exists_opt (m : ℕ) [NeZero m] :
    ∃ τ : Fin (2 * m + 1) → Fin m, ∀ i, load (grahamJobs m) τ i = 3 * m := sorry

theorem tg_le_makespan (m : ℕ) [NeZero m] (τ : Fin (2 * m + 1) → Fin m) :
    3 * (m : ℝ) ≤ makespan (grahamJobs m) τ := sorry

/-- The pairing `τ'` (`j ↦ min (j, 2m − 1 − j)`) of the first `2m` jobs has every load `3m − 1` before index `2m`. -/
theorem tg_exists_prefix_pairing (m : ℕ) [NeZero m] :
    ∃ τ : Fin (2 * m + 1) → Fin m, ∀ i, loadBefore (grahamJobs m) τ (2 * m) i = 3 * m - 1 := sorry

/-- Every list schedule of Graham's instance in its own order has every load `3m − 1` after the first `2m` jobs
(the key lemma at `T = 3m − 1`, then the sum `m(3m − 1)`). -/
theorem tg_loadBefore_two_mul (m : ℕ) [NeZero m] (σ : Fin (2 * m + 1) → Fin m)
    (hσ : IsListSchedule (grahamJobs m) σ) (i : Fin m) :
    loadBefore (grahamJobs m) σ (2 * m) i = 3 * m - 1 := sorry

/-- Every list schedule of Graham's instance in its own order has makespan `4m − 1`. -/
theorem tg_listSchedule_makespan (m : ℕ) [NeZero m] (σ : Fin (2 * m + 1) → Fin m)
    (hσ : IsListSchedule (grahamJobs m) σ) : makespan (grahamJobs m) σ = 4 * m - 1 := sorry

/-- An antitone relabeling of Graham's instance leaves the lengths unchanged (`Tuple.unique_antitone`). -/
theorem tg_comp_eq (m : ℕ) (π : Equiv.Perm (Fin (2 * m + 1))) (h : Antitone (grahamJobs m ∘ π)) :
    grahamJobs m ∘ π = grahamJobs m := sorry

/-- Graham's instance is listed in nonincreasing order. -/
theorem grahamJobs_antitone_internal (m : ℕ) : Antitone (grahamJobs m) := sorry

/-- Graham's instance has optimal makespan `3m`. -/
theorem grahamJobs_optMakespan_internal (m : ℕ) [NeZero m] : optMakespan m (grahamJobs m) = 3 * m := sorry

/-- Every LPT schedule of Graham's instance has makespan `4m − 1`: the bound `4/3 − 1/(3m)` is attained for every `m`. -/
theorem grahamJobs_lpt_makespan_internal (m : ℕ) [NeZero m] (σ : Fin (2 * m + 1) → Fin m)
    (hσ : IsLPTSchedule (grahamJobs m) σ) : makespan (grahamJobs m) σ = 4 * m - 1 := sorry

end GrahamLPT
