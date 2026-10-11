module

public import GrahamLPT.TightList
public import GrahamLPT.TightLPT

/-!
# Ratio

The least constants, `2 − 1/m` and `4/3 − 1/(3m)` (ARCH.md §8). Lane `ratio`. Helpers carry the prefix `rt_`; the `_internal` twins of the Challenge theorems are closed in `Solution.lean`.
-/

@[expose] public section

namespace GrahamLPT

open Finset

/-- `2 − 1/m` is the least constant `c` with `C(σ) ≤ c · C(τ)` for every list schedule `σ` of every
nonnegative instance on `m` machines and every assignment `τ`. -/
theorem isLeast_listSchedule_ratio_internal (m : ℕ) [NeZero m] :
    IsLeast {c : ℝ | ∀ (n : ℕ) (p : Fin n → ℝ) (σ τ : Fin n → Fin m), (∀ j, 0 ≤ p j) →
      IsListSchedule p σ → makespan p σ ≤ c * makespan p τ} (2 - 1 / m) := sorry

/-- `4/3 − 1/(3m)` is the least constant `c` with `C(σ) ≤ c · C(τ)` for every LPT schedule `σ` of every nonnegative
instance on `m` machines and every assignment `τ`. -/
theorem isLeast_lpt_ratio_internal (m : ℕ) [NeZero m] :
    IsLeast {c : ℝ | ∀ (n : ℕ) (p : Fin n → ℝ) (σ τ : Fin n → Fin m), (∀ j, 0 ≤ p j) →
      IsLPTSchedule p σ → makespan p σ ≤ c * makespan p τ} (4 / 3 - 1 / (3 * m)) := sorry

end GrahamLPT
