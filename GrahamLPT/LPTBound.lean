module

public import GrahamLPT.Key

/-!
# LPTBound

Graham's 1969 bound for LPT (ARCH.md §4). Lane `lptbound`. Helpers carry the prefix `lb2_`; the `_internal` twins of the Challenge theorems are closed in `Solution.lean`.
-/

@[expose] public section

namespace GrahamLPT

open Finset

/-- The sorted form of `lpt_bound`. -/
theorem lb2_bound_sorted {m n : ℕ} [NeZero m] (p : Fin n → ℝ) (hp : ∀ j, 0 ≤ p j) (hanti : Antitone p)
    (σ : Fin n → Fin m) (hσ : IsListSchedule p σ) (τ : Fin n → Fin m) :
    3 * (m : ℝ) * makespan p σ ≤ (4 * m - 1) * makespan p τ := sorry

/-- Graham's bound for LPT: for nonnegative lengths, every LPT schedule `σ` and every assignment `τ` satisfy
`3m · C(σ) ≤ (4m − 1) · C(τ)`. -/
theorem lpt_bound_internal {m n : ℕ} [NeZero m] (p : Fin n → ℝ) (hp : ∀ j, 0 ≤ p j)
    (σ : Fin n → Fin m) (hσ : IsLPTSchedule p σ) (τ : Fin n → Fin m) :
    3 * (m : ℝ) * makespan p σ ≤ (4 * m - 1) * makespan p τ := sorry

/-- Every LPT schedule is within the factor `4/3 − 1/(3m)` of the optimum. -/
theorem lpt_le_optMakespan_internal {m n : ℕ} [NeZero m] (p : Fin n → ℝ) (hp : ∀ j, 0 ≤ p j)
    (σ : Fin n → Fin m) (hσ : IsLPTSchedule p σ) :
    makespan p σ ≤ (4 / 3 - 1 / (3 * m)) * optMakespan m p := sorry

end GrahamLPT
