module

public import GrahamLPT.Defs

/-!
# Basic

Loads, makespans, the existence of list and LPT schedules, the attained optimum, relabeling (ARCH.md §1). Lane `basic`. Helpers carry the prefix `bs_`; the `_internal` twins of the Challenge theorems are closed in `Solution.lean`.
-/

@[expose] public section

namespace GrahamLPT

open Finset

/-- No job has index below `0`. -/
theorem bs_loadBefore_zero {m n : ℕ} (p : Fin n → ℝ) (σ : Fin n → Fin m) (i : Fin m) :
    loadBefore p σ 0 i = 0 := sorry

/-- Adding the job `k`. -/
theorem bs_loadBefore_succ {m n : ℕ} (p : Fin n → ℝ) (σ : Fin n → Fin m) (k : Fin n) (i : Fin m) :
    loadBefore p σ (k + 1) i = loadBefore p σ k i + if σ k = i then p k else 0 := sorry

/-- At or beyond the last index, `loadBefore` is the load. -/
theorem bs_loadBefore_of_le {m n : ℕ} (p : Fin n → ℝ) (σ : Fin n → Fin m) (k : ℕ) (hk : n ≤ k) (i : Fin m) :
    loadBefore p σ k i = load p σ i := sorry

/-- The loads before `k` sum to the lengths of the jobs before `k`. -/
theorem bs_sum_loadBefore {m n : ℕ} (p : Fin n → ℝ) (σ : Fin n → Fin m) (k : ℕ) :
    ∑ i, loadBefore p σ k i = ∑ j ∈ univ.filter (fun j : Fin n => (j : ℕ) < k), p j := sorry

/-- The loads sum to the total length. -/
theorem bs_sum_load {m n : ℕ} (p : Fin n → ℝ) (σ : Fin n → Fin m) : ∑ i, load p σ i = ∑ j, p j := sorry

/-- The lengths of the jobs before `k`, plus `p k`, are at most the total (nonnegative lengths). -/
theorem bs_sum_filter_add_le {n : ℕ} (p : Fin n → ℝ) (hp : ∀ j, 0 ≤ p j) (k : Fin n) :
    ∑ j ∈ univ.filter (fun j : Fin n => (j : ℕ) < k), p j + p k ≤ ∑ j, p j := sorry

theorem bs_loadBefore_nonneg {m n : ℕ} (p : Fin n → ℝ) (hp : ∀ j, 0 ≤ p j) (σ : Fin n → Fin m) (k : ℕ)
    (i : Fin m) : 0 ≤ loadBefore p σ k i := sorry

theorem bs_loadBefore_mono {m n : ℕ} (p : Fin n → ℝ) (hp : ∀ j, 0 ≤ p j) (σ : Fin n → Fin m) {k k' : ℕ}
    (h : k ≤ k') (i : Fin m) : loadBefore p σ k i ≤ loadBefore p σ k' i := sorry

theorem bs_loadBefore_le_load {m n : ℕ} (p : Fin n → ℝ) (hp : ∀ j, 0 ≤ p j) (σ : Fin n → Fin m) (k : ℕ)
    (i : Fin m) : loadBefore p σ k i ≤ load p σ i := sorry

/-- The load of a machine with no job is `0`. -/
theorem bs_load_eq_zero {m n : ℕ} (p : Fin n → ℝ) (σ : Fin n → Fin m) (i : Fin m) (h : ∀ j, σ j ≠ i) :
    load p σ i = 0 := sorry

/-- A machine with a job has a last job `k`, and its load is the load before `k` plus `p k`. -/
theorem bs_exists_last_job {m n : ℕ} (p : Fin n → ℝ) (σ : Fin n → Fin m) (i : Fin m) (h : ∃ j, σ j = i) :
    ∃ k : Fin n, σ k = i ∧ load p σ i = loadBefore p σ k i + p k := sorry

/-- With a cutoff `c`: a machine with a job of index below `c` has a last such job. -/
theorem bs_exists_last_job_before {m n : ℕ} (p : Fin n → ℝ) (σ : Fin n → Fin m) (c : ℕ) (i : Fin m)
    (h : ∃ j : Fin n, (j : ℕ) < c ∧ σ j = i) :
    ∃ k : Fin n, (k : ℕ) < c ∧ σ k = i ∧ loadBefore p σ c i = loadBefore p σ k i + p k := sorry

/-- A machine with no job of index below `c` has load `0` before `c`. -/
theorem bs_loadBefore_eq_zero {m n : ℕ} (p : Fin n → ℝ) (σ : Fin n → Fin m) (c : ℕ) (i : Fin m)
    (h : ∀ j : Fin n, (j : ℕ) < c → σ j ≠ i) : loadBefore p σ c i = 0 := sorry

/-- In a list schedule, `m` times the least load before `k` is at most the total length of the jobs before `k`. -/
theorem bs_mul_loadBefore_le {m n : ℕ} (p : Fin n → ℝ) (σ : Fin n → Fin m) (hσ : IsListSchedule p σ)
    (k : Fin n) : (m : ℝ) * loadBefore p σ k (σ k) ≤ ∑ j ∈ univ.filter (fun j : Fin n => (j : ℕ) < k), p j := sorry

theorem bs_makespan_le_iff {m n : ℕ} [NeZero m] (p : Fin n → ℝ) (σ : Fin n → Fin m) (c : ℝ) :
    makespan p σ ≤ c ↔ ∀ i, load p σ i ≤ c := sorry

theorem bs_exists_load_eq_makespan {m n : ℕ} [NeZero m] (p : Fin n → ℝ) (σ : Fin n → Fin m) :
    ∃ i, load p σ i = makespan p σ := sorry

theorem bs_makespan_nonneg {m n : ℕ} [NeZero m] (p : Fin n → ℝ) (hp : ∀ j, 0 ≤ p j) (σ : Fin n → Fin m) :
    0 ≤ makespan p σ := sorry

/-- Relabeling the jobs by a permutation changes no load. -/
theorem bs_load_comp {m n : ℕ} (p : Fin n → ℝ) (σ : Fin n → Fin m) (π : Equiv.Perm (Fin n)) (i : Fin m) :
    load (p ∘ π) (σ ∘ π) i = load p σ i := sorry

/-- The optimal makespan is at least `(Σ p)/m` and at least every job. -/
theorem bs_sum_le_mul_optMakespan {m n : ℕ} [NeZero m] (p : Fin n → ℝ) :
    ∑ j, p j ≤ (m : ℝ) * optMakespan m p := sorry

theorem bs_le_optMakespan_of_nonneg {m n : ℕ} [NeZero m] (p : Fin n → ℝ) (hp : ∀ j, 0 ≤ p j) (j : Fin n) :
    p j ≤ optMakespan m p := sorry

/-- A list schedule exists (the lowest-index tie-breaking, for instance). -/
theorem exists_isListSchedule_internal {m n : ℕ} [NeZero m] (p : Fin n → ℝ) :
    ∃ σ : Fin n → Fin m, IsListSchedule p σ := sorry

/-- An LPT schedule exists. -/
theorem exists_isLPTSchedule_internal {m n : ℕ} [NeZero m] (p : Fin n → ℝ) :
    ∃ σ : Fin n → Fin m, IsLPTSchedule p σ := sorry

/-- The optimal makespan is at most the makespan of every assignment. -/
theorem optMakespan_le_internal {m n : ℕ} [NeZero m] (p : Fin n → ℝ) (τ : Fin n → Fin m) :
    optMakespan m p ≤ makespan p τ := sorry

/-- The optimal makespan is attained. -/
theorem exists_makespan_eq_optMakespan_internal {m n : ℕ} [NeZero m] (p : Fin n → ℝ) :
    ∃ τ : Fin n → Fin m, makespan p τ = optMakespan m p := sorry

/-- Every machine load is at most the makespan. -/
theorem load_le_makespan_internal {m n : ℕ} [NeZero m] (p : Fin n → ℝ) (σ : Fin n → Fin m) (i : Fin m) :
    load p σ i ≤ makespan p σ := sorry

/-- For nonnegative lengths every job is at most the makespan. -/
theorem le_makespan_of_nonneg_internal {m n : ℕ} [NeZero m] (p : Fin n → ℝ) (hp : ∀ j, 0 ≤ p j)
    (σ : Fin n → Fin m) (j : Fin n) : p j ≤ makespan p σ := sorry

/-- The total length is at most `m` times the makespan. -/
theorem sum_le_mul_makespan_internal {m n : ℕ} [NeZero m] (p : Fin n → ℝ) (σ : Fin n → Fin m) :
    ∑ j, p j ≤ (m : ℝ) * makespan p σ := sorry

/-- Relabeling the jobs by a permutation changes neither the loads nor the makespan. -/
theorem makespan_comp_internal {m n : ℕ} [NeZero m] (p : Fin n → ℝ) (σ : Fin n → Fin m) (π : Equiv.Perm (Fin n)) :
    makespan (p ∘ π) (σ ∘ π) = makespan p σ := sorry

end GrahamLPT
