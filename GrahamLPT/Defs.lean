module

public import Mathlib

/-!
# Definitions

The definitions of `Challenge.lean`, restated character for character (the registry's comparator judges the
elaborated constants; `scripts/check_definitions.py` compares the text and `scripts/verify.py` the `pp.all`
output). The development's modules import this file; `Solution.lean` restates the Challenge's theorems over it
and never imports `Challenge.lean`.
-/

@[expose] public section

namespace GrahamLPT

open Finset

/-- The load of machine `i` from the jobs of index below `k` under the assignment `σ`. -/
def loadBefore {m n : ℕ} (p : Fin n → ℝ) (σ : Fin n → Fin m) (k : ℕ) (i : Fin m) : ℝ :=
  ∑ j ∈ univ.filter (fun j : Fin n => (j : ℕ) < k ∧ σ j = i), p j

/-- The load of machine `i`: the total length of the jobs assigned to it. -/
def load {m n : ℕ} (p : Fin n → ℝ) (σ : Fin n → Fin m) (i : Fin m) : ℝ :=
  ∑ j ∈ univ.filter (fun j : Fin n => σ j = i), p j

/-- The makespan of an assignment: its largest machine load. -/
def makespan {m n : ℕ} [NeZero m] (p : Fin n → ℝ) (σ : Fin n → Fin m) : ℝ :=
  univ.sup' univ_nonempty (load p σ)

/-- The optimal makespan: the least makespan over all assignments of the `n` jobs to the `m` machines. -/
def optMakespan (m : ℕ) [NeZero m] {n : ℕ} (p : Fin n → ℝ) : ℝ :=
  univ.inf' univ_nonempty (fun σ : Fin n → Fin m => makespan p σ)

/-- A list schedule in the index order: each job `k` goes to a machine whose load from the jobs before `k` is least,
under any tie-breaking. -/
def IsListSchedule {m n : ℕ} (p : Fin n → ℝ) (σ : Fin n → Fin m) : Prop :=
  ∀ k : Fin n, ∀ i : Fin m, loadBefore p σ k (σ k) ≤ loadBefore p σ k i

/-- An LPT schedule: a list schedule of the jobs taken in some nonincreasing order of length. -/
def IsLPTSchedule {m n : ℕ} (p : Fin n → ℝ) (σ : Fin n → Fin m) : Prop :=
  ∃ π : Equiv.Perm (Fin n), Antitone (p ∘ π) ∧ IsListSchedule (p ∘ π) (σ ∘ π)

/-- Graham's instance for LPT: the `2m + 1` lengths `2m − 1, 2m − 1, 2m − 2, 2m − 2, …, m + 1, m + 1, m, m, m`. -/
def grahamJobs (m : ℕ) : Fin (2 * m + 1) → ℝ := fun j =>
  if (j : ℕ) < 2 * m then 2 * (m : ℝ) - 1 - (((j : ℕ) / 2 : ℕ) : ℝ) else (m : ℝ)

/-- Graham's instance for list scheduling: `m(m − 1)` unit jobs followed by one job of length `m`. -/
def unitJobs (m : ℕ) : Fin (m * (m - 1) + 1) → ℝ := fun j =>
  if (j : ℕ) < m * (m - 1) then 1 else (m : ℝ)

end GrahamLPT
