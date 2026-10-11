module

public import GrahamLPT.Certificates

/-!
# Equality

The necessity half of Dósa's theorem, sorted form: equality forces `n = 2m + 1` and Graham's instance up to a positive scale (ARCH.md §3, the counting route). Lane `neccount`; helpers carry the prefix `eq_`.
-/

@[expose] public section

namespace GrahamLPT

open Finset


/-- Dósa's theorem (2004), the sorted form: a list schedule of a nonincreasing positive `p` on `m ≥ 2` machines
attains Graham's bound against the optimum only for Graham's instance: then `n = 2m + 1` and `p` is a positive
multiple of `grahamJobs m`. -/
theorem graham_of_listSchedule_eq_bound_internal {m n : ℕ} [NeZero m] (hm : 2 ≤ m) (hn : 0 < n) (p : Fin n → ℝ)
    (hp : ∀ j, 0 < p j) (hanti : Antitone p) (σ : Fin n → Fin m) (hσ : IsListSchedule p σ)
    (heq : 3 * m * makespan p σ = (4 * m - 1) * optMakespan m p) :
    ∃ (a : ℝ) (h : n = 2 * m + 1), 0 < a ∧ ∀ j, p j = a * grahamJobs m (Fin.cast h j) := sorry

end GrahamLPT
