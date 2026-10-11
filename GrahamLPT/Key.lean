module

public import GrahamLPT.Basic

/-!
# Key

The key lemma by counting, and the optimality of LPT when every job exceeds a third of the optimum (ARCH.md §3). Lane `key`. Helpers carry the prefix `key_`; the `_internal` twins of the Challenge theorems are closed in `Solution.lean`.
-/

@[expose] public section

namespace GrahamLPT

open Finset

/-- The key lemma (ARCH.md §3; README (i)): `p` nonincreasing and nonnegative, `σ` a list schedule, `τ` any assignment
whose loads from the jobs of index `≤ k` are at most `T`, and `T < 3 p_k`: then the machine of `k` ends by `T`. -/
theorem key_lemma {m n : ℕ} (p : Fin n → ℝ) (hp : ∀ j, 0 ≤ p j) (hanti : Antitone p) (σ : Fin n → Fin m)
    (hσ : IsListSchedule p σ) (k : Fin n) (τ : Fin n → Fin m) (T : ℝ)
    (hT : ∀ i, loadBefore p τ (k + 1) i ≤ T) (h3 : T < 3 * p k) :
    loadBefore p σ k (σ k) + p k ≤ T := sorry

/-- The sorted form of `lpt_optimal_of_third_lt`. -/
theorem key_optimal_sorted {m n : ℕ} [NeZero m] (p : Fin n → ℝ) (hp : ∀ j, 0 ≤ p j) (hanti : Antitone p)
    (σ : Fin n → Fin m) (hσ : IsListSchedule p σ) (τ : Fin n → Fin m) (h : ∀ j, makespan p τ < 3 * p j) :
    makespan p σ ≤ makespan p τ := sorry

/-- When every job is longer than a third of the makespan of `τ`, every LPT schedule is at least as good as `τ`. -/
theorem lpt_optimal_of_third_lt_internal {m n : ℕ} [NeZero m] (p : Fin n → ℝ) (hp : ∀ j, 0 ≤ p j)
    (σ : Fin n → Fin m) (hσ : IsLPTSchedule p σ) (τ : Fin n → Fin m)
    (h : ∀ j, makespan p τ < 3 * p j) : makespan p σ ≤ makespan p τ := sorry

/-- LPT is optimal when every job is longer than a third of the optimal makespan. -/
theorem lpt_eq_optMakespan_of_third_lt_internal {m n : ℕ} [NeZero m] (p : Fin n → ℝ) (hp : ∀ j, 0 ≤ p j)
    (σ : Fin n → Fin m) (hσ : IsLPTSchedule p σ) (h : ∀ j, optMakespan m p < 3 * p j) :
    makespan p σ = optMakespan m p := sorry

end GrahamLPT
