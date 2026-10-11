module

public import GrahamLPT.TightLPT

/-!
# GrahamScaled

Scaling and relabeling of instances, and the sufficiency half of Dósa's theorem: every positive multiple of Graham's instance in any order attains the bound (ARCH.md §2). Lane `suff`; helpers carry the prefix `gs_`.
-/

@[expose] public section

namespace GrahamLPT

open Finset

/-- Scaling the lengths by `a ≥ 0` scales the loads before `k`. -/
theorem gs_loadBefore_smul {m n : ℕ} (p : Fin n → ℝ) (a : ℝ) (σ : Fin n → Fin m) (k : ℕ) (i : Fin m) :
    loadBefore (fun j => a * p j) σ k i = a * loadBefore p σ k i := sorry

/-- Scaling the lengths by `a ≥ 0` scales the makespan. -/
theorem gs_makespan_smul {m n : ℕ} [NeZero m] (p : Fin n → ℝ) (a : ℝ) (ha : 0 ≤ a) (σ : Fin n → Fin m) :
    makespan (fun j => a * p j) σ = a * makespan p σ := sorry

/-- Scaling the lengths by `a ≥ 0` scales the optimal makespan. -/
theorem gs_optMakespan_smul {m n : ℕ} [NeZero m] (p : Fin n → ℝ) (a : ℝ) (ha : 0 ≤ a) :
    optMakespan m (fun j => a * p j) = a * optMakespan m p := sorry

/-- A list schedule of `p` is a list schedule of `a · p` for `a > 0`, and conversely. -/
theorem gs_isListSchedule_smul_iff {m n : ℕ} (p : Fin n → ℝ) (a : ℝ) (ha : 0 < a) (σ : Fin n → Fin m) :
    IsListSchedule (fun j => a * p j) σ ↔ IsListSchedule p σ := sorry

/-- Relabeling the jobs by a permutation preserves the optimal makespan. -/
theorem gs_optMakespan_comp {m n : ℕ} [NeZero m] (p : Fin n → ℝ) (π : Equiv.Perm (Fin n)) :
    optMakespan m (p ∘ π) = optMakespan m p := sorry

/-- Every positive multiple of Graham's instance, in any order, attains the bound: every LPT schedule has makespan
`(4m − 1) a` against the optimum `3m a`. -/
theorem lpt_eq_bound_of_graham_internal {m n : ℕ} [NeZero m] (p : Fin n → ℝ) (a : ℝ) (ha : 0 < a)
    (e : Fin n ≃ Fin (2 * m + 1)) (he : ∀ j, p j = a * grahamJobs m (e j)) (σ : Fin n → Fin m)
    (hσ : IsLPTSchedule p σ) : 3 * m * makespan p σ = (4 * m - 1) * optMakespan m p := sorry

end GrahamLPT
