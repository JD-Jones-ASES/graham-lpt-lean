module

public import GrahamLPT.Basic

/-!
# ListBound

Graham's 1966 bound for list scheduling (ARCH.md §2). Lane `listbound`. Helpers carry the prefix `lb_`; the `_internal` twins of the Challenge theorems are closed in `Solution.lean`.
-/

@[expose] public section

namespace GrahamLPT

open Finset

/-- The makespan of a list schedule, through the last job `k` of a heaviest machine:
`m · (L_k + p_k) ≤ Σ p + (m − 1) · p_k`. -/
theorem lb_mul_le {m n : ℕ} (p : Fin n → ℝ) (hp : ∀ j, 0 ≤ p j) (σ : Fin n → Fin m) (hσ : IsListSchedule p σ)
    (k : Fin n) : (m : ℝ) * (loadBefore p σ k (σ k) + p k) ≤ ∑ j, p j + (m - 1) * p k := sorry

/-- Graham's bound for list scheduling: for nonnegative lengths, every list schedule `σ` and every assignment `τ`
satisfy `m · C(σ) ≤ (2m − 1) · C(τ)`. -/
theorem listSchedule_bound_internal {m n : ℕ} [NeZero m] (p : Fin n → ℝ) (hp : ∀ j, 0 ≤ p j)
    (σ : Fin n → Fin m) (hσ : IsListSchedule p σ) (τ : Fin n → Fin m) :
    (m : ℝ) * makespan p σ ≤ (2 * m - 1) * makespan p τ := sorry

/-- Every list schedule is within the factor `2 − 1/m` of the optimum. -/
theorem listSchedule_le_optMakespan_internal {m n : ℕ} [NeZero m] (p : Fin n → ℝ) (hp : ∀ j, 0 ≤ p j)
    (σ : Fin n → Fin m) (hσ : IsListSchedule p σ) :
    makespan p σ ≤ (2 - 1 / m) * optMakespan m p := sorry

end GrahamLPT
