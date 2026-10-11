module

public import GrahamLPT.LPTBound
public import GrahamLPT.TightLPT

/-!
# FixedCount

The supremum of the LPT ratio for a fixed number `n ≥ 2m + 1` of jobs: Graham's jobs followed by small jobs (ARCH.md §5). Lane `fixed`; helpers carry the prefix `fc_`.
-/

@[expose] public section

namespace GrahamLPT

open Finset


/-- For every fixed number `n ≥ 2m + 1` of jobs, Graham's constant `4/3 − 1/(3m)` is still the supremum of
`C(σ)/optMakespan` over the LPT schedules of the positive instances with `n` jobs: Graham's jobs followed by
`n − 2m − 1` jobs of a common small length approach it (and attain it only at `n = 2m + 1`,
`lpt_lt_bound_of_card_ne`). -/
theorem isLUB_lpt_ratio_of_card_internal {m n : ℕ} [NeZero m] (hn : 2 * m + 1 ≤ n) :
    IsLUB {r : ℝ | ∃ (p : Fin n → ℝ) (σ : Fin n → Fin m), (∀ j, 0 < p j) ∧ IsLPTSchedule p σ ∧
      r = makespan p σ / optMakespan m p} (4 / 3 - 1 / (3 * m)) := sorry

end GrahamLPT
