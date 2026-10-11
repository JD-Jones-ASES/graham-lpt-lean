module

public import GrahamLPT

/-!
# Solution

Each statement of `Challenge.lean`, restated verbatim and closed by the internal theorem of the same
name with the suffix `_internal` (the modules of `GrahamLPT/`; VERIFICATION.md names the module of
each theorem). This module does not import `Challenge.lean`; the definitions come from
`GrahamLPT/Defs.lean`, which restates those of the Challenge character for character.
-/

@[expose] public section

namespace GrahamLPT

open Finset

theorem exists_isListSchedule {m n : ℕ} [NeZero m] (p : Fin n → ℝ) :
    ∃ σ : Fin n → Fin m, IsListSchedule p σ :=
  exists_isListSchedule_internal p

theorem exists_isLPTSchedule {m n : ℕ} [NeZero m] (p : Fin n → ℝ) :
    ∃ σ : Fin n → Fin m, IsLPTSchedule p σ :=
  exists_isLPTSchedule_internal p

theorem optMakespan_le {m n : ℕ} [NeZero m] (p : Fin n → ℝ) (τ : Fin n → Fin m) :
    optMakespan m p ≤ makespan p τ :=
  optMakespan_le_internal p τ

theorem exists_makespan_eq_optMakespan {m n : ℕ} [NeZero m] (p : Fin n → ℝ) :
    ∃ τ : Fin n → Fin m, makespan p τ = optMakespan m p :=
  exists_makespan_eq_optMakespan_internal p

theorem load_le_makespan {m n : ℕ} [NeZero m] (p : Fin n → ℝ) (σ : Fin n → Fin m) (i : Fin m) :
    load p σ i ≤ makespan p σ :=
  load_le_makespan_internal p σ i

theorem le_makespan_of_nonneg {m n : ℕ} [NeZero m] (p : Fin n → ℝ) (hp : ∀ j, 0 ≤ p j)
    (σ : Fin n → Fin m) (j : Fin n) : p j ≤ makespan p σ :=
  le_makespan_of_nonneg_internal p hp σ j

theorem sum_le_mul_makespan {m n : ℕ} [NeZero m] (p : Fin n → ℝ) (σ : Fin n → Fin m) :
    ∑ j, p j ≤ (m : ℝ) * makespan p σ :=
  sum_le_mul_makespan_internal p σ

theorem makespan_comp {m n : ℕ} [NeZero m] (p : Fin n → ℝ) (σ : Fin n → Fin m) (π : Equiv.Perm (Fin n)) :
    makespan (p ∘ π) (σ ∘ π) = makespan p σ :=
  makespan_comp_internal p σ π

theorem listSchedule_bound {m n : ℕ} [NeZero m] (p : Fin n → ℝ) (hp : ∀ j, 0 ≤ p j)
    (σ : Fin n → Fin m) (hσ : IsListSchedule p σ) (τ : Fin n → Fin m) :
    (m : ℝ) * makespan p σ ≤ (2 * m - 1) * makespan p τ :=
  listSchedule_bound_internal p hp σ hσ τ

theorem listSchedule_le_optMakespan {m n : ℕ} [NeZero m] (p : Fin n → ℝ) (hp : ∀ j, 0 ≤ p j)
    (σ : Fin n → Fin m) (hσ : IsListSchedule p σ) :
    makespan p σ ≤ (2 - 1 / m) * optMakespan m p :=
  listSchedule_le_optMakespan_internal p hp σ hσ

theorem unitJobs_optMakespan (m : ℕ) [NeZero m] : optMakespan m (unitJobs m) = m :=
  unitJobs_optMakespan_internal m

theorem unitJobs_listSchedule_makespan (m : ℕ) [NeZero m] (σ : Fin (m * (m - 1) + 1) → Fin m)
    (hσ : IsListSchedule (unitJobs m) σ) : makespan (unitJobs m) σ = 2 * m - 1 :=
  unitJobs_listSchedule_makespan_internal m σ hσ

theorem isLeast_listSchedule_ratio (m : ℕ) [NeZero m] :
    IsLeast {c : ℝ | ∀ (n : ℕ) (p : Fin n → ℝ) (σ τ : Fin n → Fin m), (∀ j, 0 ≤ p j) →
      IsListSchedule p σ → makespan p σ ≤ c * makespan p τ} (2 - 1 / m) :=
  isLeast_listSchedule_ratio_internal m

theorem lpt_bound {m n : ℕ} [NeZero m] (p : Fin n → ℝ) (hp : ∀ j, 0 ≤ p j)
    (σ : Fin n → Fin m) (hσ : IsLPTSchedule p σ) (τ : Fin n → Fin m) :
    3 * (m : ℝ) * makespan p σ ≤ (4 * m - 1) * makespan p τ :=
  lpt_bound_internal p hp σ hσ τ

theorem lpt_le_optMakespan {m n : ℕ} [NeZero m] (p : Fin n → ℝ) (hp : ∀ j, 0 ≤ p j)
    (σ : Fin n → Fin m) (hσ : IsLPTSchedule p σ) :
    makespan p σ ≤ (4 / 3 - 1 / (3 * m)) * optMakespan m p :=
  lpt_le_optMakespan_internal p hp σ hσ

theorem lpt_optimal_of_third_lt {m n : ℕ} [NeZero m] (p : Fin n → ℝ) (hp : ∀ j, 0 ≤ p j)
    (σ : Fin n → Fin m) (hσ : IsLPTSchedule p σ) (τ : Fin n → Fin m)
    (h : ∀ j, makespan p τ < 3 * p j) : makespan p σ ≤ makespan p τ :=
  lpt_optimal_of_third_lt_internal p hp σ hσ τ h

theorem lpt_eq_optMakespan_of_third_lt {m n : ℕ} [NeZero m] (p : Fin n → ℝ) (hp : ∀ j, 0 ≤ p j)
    (σ : Fin n → Fin m) (hσ : IsLPTSchedule p σ) (h : ∀ j, optMakespan m p < 3 * p j) :
    makespan p σ = optMakespan m p :=
  lpt_eq_optMakespan_of_third_lt_internal p hp σ hσ h

theorem grahamJobs_antitone (m : ℕ) : Antitone (grahamJobs m) :=
  grahamJobs_antitone_internal m

theorem grahamJobs_optMakespan (m : ℕ) [NeZero m] : optMakespan m (grahamJobs m) = 3 * m :=
  grahamJobs_optMakespan_internal m

theorem grahamJobs_exists_optimal_listSchedule (m : ℕ) [NeZero m] :
    ∃ π : Equiv.Perm (Fin (2 * m + 1)), ∃ σ : Fin (2 * m + 1) → Fin m,
      IsListSchedule (grahamJobs m ∘ π) (σ ∘ π) ∧ makespan (grahamJobs m) σ = 3 * m :=
  grahamJobs_exists_optimal_listSchedule_internal m

theorem grahamJobs_lpt_makespan (m : ℕ) [NeZero m] (σ : Fin (2 * m + 1) → Fin m)
    (hσ : IsLPTSchedule (grahamJobs m) σ) : makespan (grahamJobs m) σ = 4 * m - 1 :=
  grahamJobs_lpt_makespan_internal m σ hσ

theorem isLeast_lpt_ratio (m : ℕ) [NeZero m] :
    IsLeast {c : ℝ | ∀ (n : ℕ) (p : Fin n → ℝ) (σ τ : Fin n → Fin m), (∀ j, 0 ≤ p j) →
      IsLPTSchedule p σ → makespan p σ ≤ c * makespan p τ} (4 / 3 - 1 / (3 * m)) :=
  isLeast_lpt_ratio_internal m

theorem exists_listSchedule_le {m n : ℕ} [NeZero m] (p : Fin n → ℝ) (hp : ∀ j, 0 ≤ p j) (τ : Fin n → Fin m) :
    ∃ (π : Equiv.Perm (Fin n)) (σ : Fin n → Fin m),
      IsListSchedule (p ∘ π) (σ ∘ π) ∧ makespan p σ ≤ makespan p τ :=
  exists_listSchedule_le_internal p hp τ

theorem isLeast_listSchedule_makespan {m n : ℕ} [NeZero m] (p : Fin n → ℝ) (hp : ∀ j, 0 ≤ p j) :
    IsLeast ((fun σ : Fin n → Fin m => makespan p σ) ''
      {σ | ∃ π : Equiv.Perm (Fin n), IsListSchedule (p ∘ π) (σ ∘ π)}) (optMakespan m p) :=
  isLeast_listSchedule_makespan_internal p hp

theorem nine_five_four_lpt_thirteen :
    IsLPTSchedule (![9, 5, 5, 4, 4, 4] : Fin 6 → ℝ) (![0, 1, 2, 1, 2, 0] : Fin 6 → Fin 3) ∧
      makespan (![9, 5, 5, 4, 4, 4] : Fin 6 → ℝ) (![0, 1, 2, 1, 2, 0] : Fin 6 → Fin 3) = 13 :=
  nine_five_four_lpt_thirteen_internal

theorem nine_five_four_optMakespan : optMakespan 3 (![9, 5, 5, 4, 4, 4] : Fin 6 → ℝ) = 12 :=
  nine_five_four_optMakespan_internal

theorem lpt_third_le_not_optimal :
    ∃ (p : Fin 6 → ℝ) (σ : Fin 6 → Fin 3), (∀ j, 0 ≤ p j) ∧ IsLPTSchedule p σ ∧
      (∀ j, optMakespan 3 p ≤ 3 * p j) ∧ optMakespan 3 p < makespan p σ :=
  lpt_third_le_not_optimal_internal

theorem lpt_job_position_le {m n : ℕ} [NeZero m] (p : Fin n → ℝ) (hp : ∀ j, 0 ≤ p j) (hanti : Antitone p)
    (σ : Fin n → Fin m) (hσ : IsListSchedule p σ) (k : Fin n) (τ : Fin n → Fin m) :
    (((univ.filter (fun j : Fin n => (j : ℕ) < k ∧ σ j = σ k)).card : ℝ) + 1) * p k ≤ makespan p τ :=
  lpt_job_position_le_internal p hp hanti σ hσ k τ

theorem lpt_bound_of_card {m n : ℕ} [NeZero m] (p : Fin n → ℝ) (hp : ∀ j, 0 ≤ p j)
    (σ : Fin n → Fin m) (hσ : IsLPTSchedule p σ) (τ : Fin n → Fin m) (i : Fin m)
    (hi : load p σ i = makespan p σ) :
    ((univ.filter (fun j : Fin n => σ j = i)).card : ℝ) * m * makespan p σ ≤
      (((univ.filter (fun j : Fin n => σ j = i)).card + 1) * m - 1) * makespan p τ :=
  lpt_bound_of_card_internal p hp σ hσ τ i hi

end GrahamLPT
