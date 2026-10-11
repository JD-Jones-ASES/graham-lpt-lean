module

public import GrahamLPT.Certificates

/-!
# EqualityB

The necessity half of Dósa's theorem, sorted form, by the lane's own route (ARCH.md §3 states the target; the route is the lane's). Lane `necfree`; the main theorem is `eqb_main`, helpers carry the prefix `eqb_`.
-/

@[expose] public section

namespace GrahamLPT

open Finset

/-- Dósa's theorem, the sorted form, by this lane's own route (the same statement as
`graham_of_listSchedule_eq_bound_internal` in `Equality.lean`). -/
theorem eqb_main {m n : ℕ} [NeZero m] (hm : 2 ≤ m) (hn : 0 < n) (p : Fin n → ℝ)
    (hp : ∀ j, 0 < p j) (hanti : Antitone p) (σ : Fin n → Fin m) (hσ : IsListSchedule p σ)
    (heq : 3 * m * makespan p σ = (4 * m - 1) * optMakespan m p) :
    ∃ (a : ℝ) (h : n = 2 * m + 1), 0 < a ∧ ∀ j, p j = a * grahamJobs m (Fin.cast h j) := sorry

end GrahamLPT
