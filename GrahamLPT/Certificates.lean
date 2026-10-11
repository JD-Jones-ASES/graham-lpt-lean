module

public import GrahamLPT.Key
public import GrahamLPT.LPTBound
public import GrahamLPT.CoffmanSethi

/-!
# Certificates

The critical job's certificates: the smaller of `C(σ)` and `3 p_k` bounds every comparison schedule, the observed third certifies optimality, equality in Graham's bound forces its proof's inequalities to be equalities, and Della Croce–Scatamacchia's Proposition 4 from Chen's property (ARCH.md §1). Lane `certs`; helpers carry the prefix `ct_`.
-/

@[expose] public section

namespace GrahamLPT

open Finset


/-- The critical job's certificate: in a list schedule of a nonincreasing `p`, for a job `k` whose completion time is
the makespan, the smaller of `C(σ)` and `3 p_k` is at most `C(τ)` for every assignment `τ` (the key lemma read as a
lower bound on every comparison schedule). -/
theorem lpt_critical_min_le_internal {m n : ℕ} [NeZero m] (p : Fin n → ℝ) (hp : ∀ j, 0 ≤ p j) (hanti : Antitone p)
    (σ : Fin n → Fin m) (hσ : IsListSchedule p σ) (k : Fin n) (hk : makespan p σ = loadBefore p σ k (σ k) + p k)
    (τ : Fin n → Fin m) : min (makespan p σ) (3 * p k) ≤ makespan p τ := sorry

/-- The observed-third certificate: when a critical job `k` is at least a third of the makespan it completes, the list
schedule is optimal (`lpt_eq_optMakespan_of_third_lt` asks every job to exceed a third of the unknown optimum). -/
theorem lpt_eq_optMakespan_of_critical_third_internal {m n : ℕ} [NeZero m] (p : Fin n → ℝ) (hp : ∀ j, 0 ≤ p j)
    (hanti : Antitone p) (σ : Fin n → Fin m) (hσ : IsListSchedule p σ) (k : Fin n)
    (hk : makespan p σ = loadBefore p σ k (σ k) + p k) (h3 : makespan p σ ≤ 3 * p k) :
    makespan p σ = optMakespan m p := sorry

/-- Equality in Graham's LPT bound against `τ` on `m ≥ 2` machines, with `k` a critical job, forces the four
inequalities of its proof to be equalities: `3 p_k = C(τ)`, every machine of `σ` carries the least load before `k`,
every machine of `τ` carries exactly `C(τ)`, and every job after `k` has length `0`. -/
theorem lpt_eq_bound_structure_internal {m n : ℕ} [NeZero m] (hm : 2 ≤ m) (p : Fin n → ℝ) (hp : ∀ j, 0 ≤ p j)
    (hanti : Antitone p) (σ : Fin n → Fin m) (hσ : IsListSchedule p σ) (k : Fin n)
    (hk : makespan p σ = loadBefore p σ k (σ k) + p k) (τ : Fin n → Fin m)
    (heq : 3 * m * makespan p σ = (4 * m - 1) * makespan p τ) :
    3 * p k = makespan p τ ∧ (∀ i, loadBefore p σ k i = loadBefore p σ k (σ k)) ∧
      (∀ i, load p τ i = makespan p τ) ∧ ∀ j : Fin n, (k : ℕ) < j → p j = 0 := sorry

/-- Della Croce–Scatamacchia's Proposition 4, from Chen's property: if a machine `i` other than the critical job's
holds at least `q` jobs before the critical job `k`, and `q + 2 ≤ m`, then
`q(m − 1) · C(σ) ≤ ((q + 1)(m − 1) − 1) · C(τ)` for every assignment `τ`. -/
theorem lpt_bound_of_other_card_internal {m n : ℕ} [NeZero m] (p : Fin n → ℝ) (hp : ∀ j, 0 ≤ p j) (hanti : Antitone p)
    (σ : Fin n → Fin m) (hσ : IsListSchedule p σ) (k : Fin n) (hk : makespan p σ = loadBefore p σ k (σ k) + p k)
    (i : Fin m) (hi : i ≠ σ k) (q : ℕ) (hq : q ≤ (univ.filter (fun j : Fin n => (j : ℕ) < k ∧ σ j = i)).card)
    (hqm : q + 2 ≤ m) (τ : Fin n → Fin m) :
    (q : ℝ) * (m - 1) * makespan p σ ≤ ((q + 1) * (m - 1) - 1) * makespan p τ := sorry

end GrahamLPT
