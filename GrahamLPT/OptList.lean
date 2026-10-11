module

public import GrahamLPT.TightLPT

/-!
# OptList

The optimum of Graham's family attained by a list schedule (ARCH.md §7). Lane `optlist`. Helpers carry the prefix `ol_`; the `_internal` twins of the Challenge theorems are closed in `Solution.lean`.
-/

@[expose] public section

namespace GrahamLPT

open Finset

/-- The position-to-index map of the order `2m − 1, …, m + 1, m, m, 2m − 1, …, m + 1, m`: position `i < m − 1` to
index `2i`, positions `m − 1, m` to `2m − 2, 2m − 1`, position `m + 1 + a` (`a < m − 1`) to `2a + 1`, position `2m` to
`2m`. -/
def ol_index (m : ℕ) (i : Fin (2 * m + 1)) : Fin (2 * m + 1) :=
  if (i : ℕ) < m - 1 then ⟨2 * i, by omega⟩
  else if (i : ℕ) = m - 1 then ⟨2 * m - 2, by omega⟩
  else if (i : ℕ) = m then ⟨2 * m - 1, by omega⟩
  else if (i : ℕ) < 2 * m then ⟨2 * ((i : ℕ) - m - 1) + 1, by omega⟩
  else ⟨2 * m, by omega⟩

theorem ol_index_bijective (m : ℕ) : Function.Bijective (ol_index m) := sorry

/-- The machine of each position: `i` for `i < m − 1`; the last machine for positions `m − 1`, `m` and `2m`;
`m − 2 − a` for position `m + 1 + a`. -/
def ol_machine (m : ℕ) [NeZero m] (i : Fin (2 * m + 1)) : Fin m :=
  if (i : ℕ) < m - 1 then ⟨i, by omega⟩
  else if (i : ℕ) ≤ m then ⟨m - 1, by have := NeZero.pos m; omega⟩
  else if (i : ℕ) < 2 * m then ⟨2 * m - 2 - i, by omega⟩
  else ⟨m - 1, by have := NeZero.pos m; omega⟩

/-- In the explicit order, the schedule `ol_machine` is a list schedule. -/
theorem ol_isListSchedule (m : ℕ) [NeZero m] :
    IsListSchedule (grahamJobs m ∘ ol_index m) (ol_machine m) := sorry

/-- Its makespan is `3m`. -/
theorem ol_makespan (m : ℕ) [NeZero m] : makespan (grahamJobs m ∘ ol_index m) (ol_machine m) = 3 * m := sorry

/-- The optimum `3m` of Graham's instance is attained by a list schedule, in the order
`2m − 1, …, m + 1, m, m, 2m − 1, …, m + 1, m`. -/
theorem grahamJobs_exists_optimal_listSchedule_internal (m : ℕ) [NeZero m] :
    ∃ π : Equiv.Perm (Fin (2 * m + 1)), ∃ σ : Fin (2 * m + 1) → Fin m,
      IsListSchedule (grahamJobs m ∘ π) (σ ∘ π) ∧ makespan (grahamJobs m) σ = 3 * m := sorry

end GrahamLPT
