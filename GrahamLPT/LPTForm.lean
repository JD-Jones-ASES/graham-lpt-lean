module

public import GrahamLPT.Equality
public import GrahamLPT.GrahamScaled

/-!
# LPTForm

Dósa's theorem for LPT schedules, the two-way statement, and the strict inequality for every job count other than `2m + 1` (ARCH.md §4). Lane `lptform`; helpers carry the prefix `lf_`.
-/

@[expose] public section

namespace GrahamLPT

open Finset


/-- Dósa's theorem for LPT schedules: on `m ≥ 2` machines, an LPT schedule of a positive instance attains Graham's
bound against the optimum only when the instance is a positive multiple of Graham's `2m + 1` jobs in some order. -/
theorem graham_of_lpt_eq_bound_internal {m n : ℕ} [NeZero m] (hm : 2 ≤ m) (hn : 0 < n) (p : Fin n → ℝ) (hp : ∀ j, 0 < p j)
    (σ : Fin n → Fin m) (hσ : IsLPTSchedule p σ) (heq : 3 * m * makespan p σ = (4 * m - 1) * optMakespan m p) :
    ∃ (a : ℝ) (e : Fin n ≃ Fin (2 * m + 1)), 0 < a ∧ ∀ j, p j = a * grahamJobs m (e j) := sorry

/-- Graham's example is the only tight one (Dósa 2004): for a positive instance on `m ≥ 2` machines, some LPT
schedule attains Graham's bound `3m · C(σ) = (4m − 1) · optMakespan` if and only if the instance is a positive
multiple of Graham's `2m + 1` jobs in some order (and then every LPT schedule attains it,
`lpt_eq_bound_of_graham`). -/
theorem lpt_eq_bound_iff_graham_internal {m n : ℕ} [NeZero m] (hm : 2 ≤ m) (hn : 0 < n) (p : Fin n → ℝ)
    (hp : ∀ j, 0 < p j) :
    (∃ σ : Fin n → Fin m, IsLPTSchedule p σ ∧ 3 * m * makespan p σ = (4 * m - 1) * optMakespan m p) ↔
      ∃ (a : ℝ) (e : Fin n ≃ Fin (2 * m + 1)), 0 < a ∧ ∀ j, p j = a * grahamJobs m (e j) := sorry

/-- With any number of jobs other than `2m + 1`, no LPT schedule of a positive instance on `m ≥ 2` machines attains
Graham's bound: the inequality is strict. -/
theorem lpt_lt_bound_of_card_ne_internal {m n : ℕ} [NeZero m] (hm : 2 ≤ m) (hn : 0 < n) (hn' : n ≠ 2 * m + 1)
    (p : Fin n → ℝ) (hp : ∀ j, 0 < p j) (σ : Fin n → Fin m) (hσ : IsLPTSchedule p σ) :
    3 * m * makespan p σ < (4 * m - 1) * optMakespan m p := sorry

end GrahamLPT
