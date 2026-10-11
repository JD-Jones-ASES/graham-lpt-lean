module

public import Mathlib

/-!
# Graham's bounds for list scheduling and LPT on identical machines: `m·C_LS ≤ (2m − 1)·C_OPT` and
`3m·C_LPT ≤ (4m − 1)·C_OPT` under every tie-breaking, both equality families for every `m`, and the
optimality of LPT when every job exceeds a third of the optimum

R. L. Graham, *Bounds for certain multiprocessing anomalies*, Bell System Tech. J. 45 (1966) 1563–1581, and
*Bounds on multiprocessing timing anomalies*, SIAM J. Appl. Math. 17 (1969) 416–429, both restated with their
examples in his survey *Bounds on multiprocessing anomalies and related packing algorithms*, AFIPS Spring Joint
Computer Conference (1972) 205–217. `n` jobs of nonnegative lengths
`p : Fin n → ℝ` are run without interruption on `m ≥ 1` identical machines. An assignment `σ : Fin n → Fin m` gives
machine `i` the load `Σ_{σ j = i} p j`; the makespan of `σ` is its largest load; `optMakespan m p` is the least makespan
over all `m^n` assignments. *List scheduling* takes the jobs in a fixed order and gives each one a machine whose load from
the earlier jobs is least, ties broken arbitrarily (`IsListSchedule`, in the index order); *LPT* (longest processing time
first) is list scheduling in a nonincreasing order of length (`IsLPTSchedule`: some relabeling `π` of the jobs makes
`p ∘ π` nonincreasing and `σ ∘ π` a list schedule). Graham's rule gives a free processor the longest remaining task, a
task wanted by several simultaneously free processors going to the lower-indexed one (1966, §1.1; Lenstra–Shmoys use the
higher index); for independent tasks that is list scheduling of the sorted list, and the makespan does not depend on the
tie-breaking, so the statements quantify over every list schedule.

This file states, and `Solution.lean` proves (kernel-only):

* every list schedule `σ` and every assignment `τ` satisfy `m · C(σ) ≤ (2m − 1) · C(τ)` (Graham 1966, his Theorem for
  the same number of processors and no precedence constraints, whose proof bounds a list schedule by the average load
  plus `1 − 1/m` of the longest task, hence by `2 − 1/m` times the makespan of any assignment), so
  `C(σ) ≤ (2 − 1/m) · optMakespan m p` (`listSchedule_bound`, `listSchedule_le_optMakespan`); the `m(m − 1)` unit jobs
  followed by one job of length `m` (Graham's example for his theorem on scheduling the `k` largest tasks optimally
  first, at `k = 0`, as his 1972 survey restates it on p. 209; Lenstra–Shmoys, *Elements of Scheduling*, Chapter 9,
  p. 188) have optimal makespan `m`, and every list schedule of them in that order has makespan `2m − 1`
  (`unitJobs_optMakespan`, `unitJobs_listSchedule_makespan`), so `2 − 1/m` is the least constant
  (`isLeast_listSchedule_ratio`);
* every LPT schedule `σ` and every assignment `τ` satisfy `3m · C(σ) ≤ (4m − 1) · C(τ)` (Graham 1969, Theorem 2;
  announced in the closing remarks of the 1966 paper), so `C(σ) ≤ (4/3 − 1/(3m)) · optMakespan m p` (`lpt_bound`,
  `lpt_le_optMakespan`); LPT is optimal when every job is longer than a third of the optimal makespan — the case of
  Graham's proof in which the last task exceeds a third of the optimum, Lenstra–Shmoys's case (ii) (p. 189), stated as a
  theorem (`lpt_optimal_of_third_lt`, `lpt_eq_optMakespan_of_third_lt`); Graham's `2m + 1` jobs
  `2m − 1, 2m − 1, 2m − 2, 2m − 2, …, m + 1, m + 1, m, m, m` (1969, pp. 425–426: `α_k = 2m − ⌊(k + 1)/2⌋` for
  `k = 1, …, 2m` and `α_{2m+1} = m`) have optimal makespan `3m`, attained by a list schedule, while every LPT schedule
  of them has makespan `4m − 1`, for every `m ≥ 1` (`grahamJobs_antitone`, `grahamJobs_optMakespan`,
  `grahamJobs_exists_optimal_listSchedule`, `grahamJobs_lpt_makespan`), so `4/3 − 1/(3m)` is the least constant
  (`isLeast_lpt_ratio`);
* the elementary facts the bounds rest on: list schedules and LPT schedules exist, the optimum is attained, and every
  load, every job and the average load `(Σ p)/m` are at most the makespan (`exists_isListSchedule`,
  `exists_isLPTSchedule`, `optMakespan_le`, `exists_makespan_eq_optMakespan`, `load_le_makespan`,
  `le_makespan_of_nonneg`, `sum_le_mul_makespan`, `makespan_comp`).

Graham's `ω₀` is the least finishing time over all lists; `optMakespan` is the least over all assignments, which is at
most `ω₀`, so the bounds here are in the stronger form; for his instance the optimum `3m` is attained by a list. The
proof of the LPT bound here is not Graham's exchange argument: when the job `k` that ends a heaviest machine satisfies
`3 p_k ≤ C(τ)`, the average-load bound gives the ratio directly; otherwise a counting argument shows that `k`'s machine
ends by `C(τ)` (every job before `k` at least as long as `k`, every `τ`-machine holding at most two of the jobs up to
`k`, and the jobs at least as long as the least load sitting alone on their `τ`-machines). All lengths are real, and
nonnegative where a bound is stated (Graham 1969 takes positive lengths, 1966 nonnegative ones); the statements are
division-free where a ratio is meant.
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

/-! ## The elementary facts -/

/-- A list schedule exists (the lowest-index tie-breaking, for instance). -/
theorem exists_isListSchedule {m n : ℕ} [NeZero m] (p : Fin n → ℝ) :
    ∃ σ : Fin n → Fin m, IsListSchedule p σ := sorry

/-- An LPT schedule exists. -/
theorem exists_isLPTSchedule {m n : ℕ} [NeZero m] (p : Fin n → ℝ) :
    ∃ σ : Fin n → Fin m, IsLPTSchedule p σ := sorry

/-- The optimal makespan is at most the makespan of every assignment. -/
theorem optMakespan_le {m n : ℕ} [NeZero m] (p : Fin n → ℝ) (τ : Fin n → Fin m) :
    optMakespan m p ≤ makespan p τ := sorry

/-- The optimal makespan is attained. -/
theorem exists_makespan_eq_optMakespan {m n : ℕ} [NeZero m] (p : Fin n → ℝ) :
    ∃ τ : Fin n → Fin m, makespan p τ = optMakespan m p := sorry

/-- Every machine load is at most the makespan. -/
theorem load_le_makespan {m n : ℕ} [NeZero m] (p : Fin n → ℝ) (σ : Fin n → Fin m) (i : Fin m) :
    load p σ i ≤ makespan p σ := sorry

/-- For nonnegative lengths every job is at most the makespan. -/
theorem le_makespan_of_nonneg {m n : ℕ} [NeZero m] (p : Fin n → ℝ) (hp : ∀ j, 0 ≤ p j)
    (σ : Fin n → Fin m) (j : Fin n) : p j ≤ makespan p σ := sorry

/-- The total length is at most `m` times the makespan. -/
theorem sum_le_mul_makespan {m n : ℕ} [NeZero m] (p : Fin n → ℝ) (σ : Fin n → Fin m) :
    ∑ j, p j ≤ (m : ℝ) * makespan p σ := sorry

/-- Relabeling the jobs by a permutation changes neither the loads nor the makespan. -/
theorem makespan_comp {m n : ℕ} [NeZero m] (p : Fin n → ℝ) (σ : Fin n → Fin m) (π : Equiv.Perm (Fin n)) :
    makespan (p ∘ π) (σ ∘ π) = makespan p σ := sorry

/-! ## Graham 1966: list scheduling -/

/-- Graham's bound for list scheduling: for nonnegative lengths, every list schedule `σ` and every assignment `τ`
satisfy `m · C(σ) ≤ (2m − 1) · C(τ)`. -/
theorem listSchedule_bound {m n : ℕ} [NeZero m] (p : Fin n → ℝ) (hp : ∀ j, 0 ≤ p j)
    (σ : Fin n → Fin m) (hσ : IsListSchedule p σ) (τ : Fin n → Fin m) :
    (m : ℝ) * makespan p σ ≤ (2 * m - 1) * makespan p τ := sorry

/-- Every list schedule is within the factor `2 − 1/m` of the optimum. -/
theorem listSchedule_le_optMakespan {m n : ℕ} [NeZero m] (p : Fin n → ℝ) (hp : ∀ j, 0 ≤ p j)
    (σ : Fin n → Fin m) (hσ : IsListSchedule p σ) :
    makespan p σ ≤ (2 - 1 / m) * optMakespan m p := sorry

/-- The `m(m − 1)` unit jobs with one job of length `m` have optimal makespan `m`. -/
theorem unitJobs_optMakespan (m : ℕ) [NeZero m] : optMakespan m (unitJobs m) = m := sorry

/-- Every list schedule of the unit jobs followed by the job of length `m` has makespan `2m − 1`. -/
theorem unitJobs_listSchedule_makespan (m : ℕ) [NeZero m] (σ : Fin (m * (m - 1) + 1) → Fin m)
    (hσ : IsListSchedule (unitJobs m) σ) : makespan (unitJobs m) σ = 2 * m - 1 := sorry

/-- `2 − 1/m` is the least constant `c` with `C(σ) ≤ c · C(τ)` for every list schedule `σ` of every
nonnegative instance on `m` machines and every assignment `τ`. -/
theorem isLeast_listSchedule_ratio (m : ℕ) [NeZero m] :
    IsLeast {c : ℝ | ∀ (n : ℕ) (p : Fin n → ℝ) (σ τ : Fin n → Fin m), (∀ j, 0 ≤ p j) →
      IsListSchedule p σ → makespan p σ ≤ c * makespan p τ} (2 - 1 / m) := sorry

/-! ## Graham 1969: LPT -/

/-- Graham's bound for LPT: for nonnegative lengths, every LPT schedule `σ` and every assignment `τ` satisfy
`3m · C(σ) ≤ (4m − 1) · C(τ)`. -/
theorem lpt_bound {m n : ℕ} [NeZero m] (p : Fin n → ℝ) (hp : ∀ j, 0 ≤ p j)
    (σ : Fin n → Fin m) (hσ : IsLPTSchedule p σ) (τ : Fin n → Fin m) :
    3 * (m : ℝ) * makespan p σ ≤ (4 * m - 1) * makespan p τ := sorry

/-- Every LPT schedule is within the factor `4/3 − 1/(3m)` of the optimum. -/
theorem lpt_le_optMakespan {m n : ℕ} [NeZero m] (p : Fin n → ℝ) (hp : ∀ j, 0 ≤ p j)
    (σ : Fin n → Fin m) (hσ : IsLPTSchedule p σ) :
    makespan p σ ≤ (4 / 3 - 1 / (3 * m)) * optMakespan m p := sorry

/-- When every job is longer than a third of the makespan of `τ`, every LPT schedule is at least as good as `τ`. -/
theorem lpt_optimal_of_third_lt {m n : ℕ} [NeZero m] (p : Fin n → ℝ) (hp : ∀ j, 0 ≤ p j)
    (σ : Fin n → Fin m) (hσ : IsLPTSchedule p σ) (τ : Fin n → Fin m)
    (h : ∀ j, makespan p τ < 3 * p j) : makespan p σ ≤ makespan p τ := sorry

/-- LPT is optimal when every job is longer than a third of the optimal makespan. -/
theorem lpt_eq_optMakespan_of_third_lt {m n : ℕ} [NeZero m] (p : Fin n → ℝ) (hp : ∀ j, 0 ≤ p j)
    (σ : Fin n → Fin m) (hσ : IsLPTSchedule p σ) (h : ∀ j, optMakespan m p < 3 * p j) :
    makespan p σ = optMakespan m p := sorry

/-- Graham's instance is listed in nonincreasing order. -/
theorem grahamJobs_antitone (m : ℕ) : Antitone (grahamJobs m) := sorry

/-- Graham's instance has optimal makespan `3m`. -/
theorem grahamJobs_optMakespan (m : ℕ) [NeZero m] : optMakespan m (grahamJobs m) = 3 * m := sorry

/-- The optimum `3m` of Graham's instance is attained by a list schedule, in the order
`2m − 1, …, m + 1, m, m, 2m − 1, …, m + 1, m`. -/
theorem grahamJobs_exists_optimal_listSchedule (m : ℕ) [NeZero m] :
    ∃ π : Equiv.Perm (Fin (2 * m + 1)), ∃ σ : Fin (2 * m + 1) → Fin m,
      IsListSchedule (grahamJobs m ∘ π) (σ ∘ π) ∧ makespan (grahamJobs m) σ = 3 * m := sorry

/-- Every LPT schedule of Graham's instance has makespan `4m − 1`: the bound `4/3 − 1/(3m)` is attained for every `m`. -/
theorem grahamJobs_lpt_makespan (m : ℕ) [NeZero m] (σ : Fin (2 * m + 1) → Fin m)
    (hσ : IsLPTSchedule (grahamJobs m) σ) : makespan (grahamJobs m) σ = 4 * m - 1 := sorry

/-- `4/3 − 1/(3m)` is the least constant `c` with `C(σ) ≤ c · C(τ)` for every LPT schedule `σ` of every nonnegative
instance on `m` machines and every assignment `τ`. -/
theorem isLeast_lpt_ratio (m : ℕ) [NeZero m] :
    IsLeast {c : ℝ | ∀ (n : ℕ) (p : Fin n → ℝ) (σ τ : Fin n → Fin m), (∀ j, 0 ≤ p j) →
      IsLPTSchedule p σ → makespan p σ ≤ c * makespan p τ} (4 / 3 - 1 / (3 * m)) := sorry

end GrahamLPT
