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
  if h₁ : (i : ℕ) < m - 1 then ⟨2 * i, by omega⟩
  else if h₂ : (i : ℕ) = m - 1 then ⟨2 * m - 2, by omega⟩
  else if h₃ : (i : ℕ) = m then ⟨2 * m - 1, by omega⟩
  else if h₄ : (i : ℕ) < 2 * m then ⟨2 * ((i : ℕ) - m - 1) + 1, by omega⟩
  else ⟨2 * m, by omega⟩

theorem ol_index_bijective (m : ℕ) : Function.Bijective (ol_index m) := by
  rw [← Finite.injective_iff_bijective]
  intro a b h
  have ha := a.isLt
  have hb := b.isLt
  simp only [ol_index] at h
  rw [Fin.ext_iff]
  split_ifs at h <;> simp only [Fin.mk.injEq] at h <;> omega

/-- The machine of each position, as a natural number: `i` for `i < m − 1`; the last machine `m − 1` for positions
`m − 1`, `m` and `2m`; `2m − 1 − i` (that is, `m − 2 − a`) for position `m + 1 + a`. -/
def ol_machN (m i : ℕ) : ℕ :=
  if i < m - 1 then i else if i ≤ m then m - 1 else if i < 2 * m then 2 * m - 1 - i else m - 1

/-- The machine of each position: `i` for `i < m − 1`; the last machine for positions `m − 1`, `m` and `2m`;
`m − 2 − a` (that is, `2m − 1 − i`) for position `i = m + 1 + a`, the least loaded one at that step. -/
def ol_machine (m : ℕ) [NeZero m] (i : Fin (2 * m + 1)) : Fin m :=
  ⟨ol_machN m i, by have := NeZero.pos m; unfold ol_machN; split_ifs <;> omega⟩

/-- The length of the job at each position, as a natural number. -/
def ol_qN (m i : ℕ) : ℕ :=
  if i < m - 1 then 2 * m - 1 - i else if i ≤ m then m else if i < 2 * m then 3 * m - i else m

/-- The load of machine `b` from the positions below `k`, as a natural number. -/
def ol_loadN (m k b : ℕ) : ℕ :=
  if b < m - 1 then (if b < k then 2 * m - 1 - b else 0) + (if 2 * m - 1 - b < k then m + 1 + b else 0)
  else (if m - 1 < k then m else 0) + (if m < k then m else 0) + (if 2 * m < k then m else 0)

theorem ol_q (m : ℕ) [NeZero m] (j : Fin (2 * m + 1)) : grahamJobs m (ol_index m j) = (ol_qN m j : ℝ) := by
  have hj := j.isLt
  have hm := NeZero.pos m
  simp only [ol_index]
  split_ifs with h₁ h₂ h₃ h₄
  · have hA : 2 * (j : ℕ) < 2 * m := by omega
    have hc : (2 * (j : ℕ)) / 2 = j := by omega
    simp only [grahamJobs, ol_qN, h₁, hA, hc, ite_true]
    have : ((2 * m - 1 - j : ℕ) : ℝ) + (j : ℝ) + 1 = 2 * (m : ℝ) := by
      exact_mod_cast (show 2 * m - 1 - (j : ℕ) + (j : ℕ) + 1 = 2 * m by omega)
    linarith
  · have hA : 2 * m - 2 < 2 * m := by omega
    have hle : (j : ℕ) ≤ m := by omega
    have hc : (2 * m - 2) / 2 = m - 1 := by omega
    simp only [grahamJobs, ol_qN, h₁, hle, hA, hc, ite_true, ite_false]
    have : ((m - 1 : ℕ) : ℝ) + 1 = (m : ℝ) := by exact_mod_cast (show m - 1 + 1 = m by omega)
    linarith
  · have hA : 2 * m - 1 < 2 * m := by omega
    have hle : (j : ℕ) ≤ m := by omega
    have hc : (2 * m - 1) / 2 = m - 1 := by omega
    simp only [grahamJobs, ol_qN, h₁, hle, hA, hc, ite_true, ite_false]
    have : ((m - 1 : ℕ) : ℝ) + 1 = (m : ℝ) := by exact_mod_cast (show m - 1 + 1 = m by omega)
    linarith
  · have hA : 2 * ((j : ℕ) - m - 1) + 1 < 2 * m := by omega
    have hle : ¬ (j : ℕ) ≤ m := by omega
    have hc : (2 * ((j : ℕ) - m - 1) + 1) / 2 = (j : ℕ) - m - 1 := by omega
    simp only [grahamJobs, ol_qN, h₁, hle, h₄, hA, hc, ite_true, ite_false]
    have : ((3 * m - j : ℕ) : ℝ) + (((j : ℕ) - m - 1 : ℕ) : ℝ) + 1 = 2 * (m : ℝ) := by
      exact_mod_cast (show 3 * m - (j : ℕ) + ((j : ℕ) - m - 1) + 1 = 2 * m by omega)
    linarith
  · have hA : ¬ 2 * m < 2 * m := by omega
    have hle : ¬ (j : ℕ) ≤ m := by omega
    simp only [grahamJobs, ol_qN, h₁, hle, h₄, hA, ite_false]

theorem ol_loadBefore (m : ℕ) [NeZero m] (k : ℕ) (b : Fin m) :
    loadBefore (grahamJobs m ∘ ol_index m) (ol_machine m) k b = (ol_loadN m k b : ℝ) := by
  have hm := NeZero.pos m
  have hbm := b.isLt
  by_cases hb : (b : ℕ) < m - 1
  · have hfib : univ.filter (fun j : Fin (2 * m + 1) => (j : ℕ) < k ∧ ol_machine m j = b) =
        ({⟨b, by omega⟩, ⟨2 * m - 1 - b, by omega⟩} : Finset (Fin (2 * m + 1))).filter
          (fun j : Fin (2 * m + 1) => (j : ℕ) < k) := by
      ext j
      have hj := j.isLt
      simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton, Fin.ext_iff, ol_machine,
        ol_machN]
      split_ifs <;> omega
    rw [loadBefore, hfib, sum_filter, sum_pair (by simp only [ne_eq, Fin.ext_iff]; omega)]
    simp only [Function.comp_apply, ol_q]
    have e1 : ol_qN m b = 2 * m - 1 - b := by unfold ol_qN; rw [ite_eq_left hb]
    have e2 : ol_qN m (2 * m - 1 - b) = m + 1 + b := by unfold ol_qN; split_ifs <;> omega
    rw [e1, e2]
    unfold ol_loadN
    rw [ite_eq_left hb]
    split_ifs <;> push_cast [Nat.cast_add] <;> ring
  · have hb' : (b : ℕ) = m - 1 := by omega
    have hfib : univ.filter (fun j : Fin (2 * m + 1) => (j : ℕ) < k ∧ ol_machine m j = b) =
        ({⟨m - 1, by omega⟩, ⟨m, by omega⟩, ⟨2 * m, by omega⟩} : Finset (Fin (2 * m + 1))).filter
          (fun j : Fin (2 * m + 1) => (j : ℕ) < k) := by
      ext j
      have hj := j.isLt
      simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton, Fin.ext_iff, ol_machine,
        ol_machN]
      split_ifs <;> omega
    have hnot : (⟨m - 1, by omega⟩ : Fin (2 * m + 1)) ∉ ({⟨m, by omega⟩, ⟨2 * m, by omega⟩} : Finset _) := by
      simp only [mem_insert, mem_singleton, Fin.ext_iff]
      omega
    rw [loadBefore, hfib, sum_filter, sum_insert hnot,
      sum_pair (by simp only [ne_eq, Fin.ext_iff]; omega)]
    simp only [Function.comp_apply, ol_q]
    have e1 : ol_qN m (m - 1) = m := by unfold ol_qN; split_ifs <;> omega
    have e2 : ol_qN m m = m := by unfold ol_qN; split_ifs <;> omega
    have e3 : ol_qN m (2 * m) = m := by unfold ol_qN; split_ifs <;> omega
    rw [e1, e2, e3]
    unfold ol_loadN
    rw [ite_eq_right hb]
    split_ifs <;> push_cast [Nat.cast_add] <;> ring

theorem ol_listN (m k b : ℕ) (hk : k ≤ 2 * m) (hb : b < m) :
    ol_loadN m k (ol_machN m k) ≤ ol_loadN m k b := by
  unfold ol_loadN ol_machN
  split_ifs <;> omega

/-- In the explicit order, the schedule `ol_machine` is a list schedule. -/
theorem ol_isListSchedule (m : ℕ) [NeZero m] :
    IsListSchedule (grahamJobs m ∘ ol_index m) (ol_machine m) := by
  intro k i
  rw [ol_loadBefore, ol_loadBefore]
  exact_mod_cast ol_listN m k i (by have := k.isLt; omega) i.isLt

theorem ol_load (m : ℕ) [NeZero m] (b : Fin m) :
    load (grahamJobs m ∘ ol_index m) (ol_machine m) b = 3 * (m : ℝ) := by
  rw [← bs_loadBefore_of_le _ _ (2 * m + 1) le_rfl, ol_loadBefore]
  have hb := b.isLt
  have : ol_loadN m (2 * m + 1) b = 3 * m := by unfold ol_loadN; split_ifs <;> omega
  rw [this]
  push_cast
  ring

/-- Its makespan is `3m`. -/
theorem ol_makespan (m : ℕ) [NeZero m] :
    makespan (grahamJobs m ∘ ol_index m) (ol_machine m) = 3 * m := by
  apply le_antisymm
  · rw [bs_makespan_le_iff]
    intro i
    rw [ol_load]
  · rw [← ol_load m ⟨0, NeZero.pos m⟩]
    exact load_le_makespan_internal _ _ _

/-- The optimum `3m` of Graham's instance is attained by a list schedule, in the order
`2m − 1, …, m + 1, m, m, 2m − 1, …, m + 1, m`. -/
theorem grahamJobs_exists_optimal_listSchedule_internal (m : ℕ) [NeZero m] :
    ∃ π : Equiv.Perm (Fin (2 * m + 1)), ∃ σ : Fin (2 * m + 1) → Fin m,
      IsListSchedule (grahamJobs m ∘ π) (σ ∘ π) ∧ makespan (grahamJobs m) σ = 3 * m := by
  let π : Equiv.Perm (Fin (2 * m + 1)) := Equiv.ofBijective _ (ol_index_bijective m)
  have hπ : (π : Fin (2 * m + 1) → Fin (2 * m + 1)) = ol_index m := rfl
  have hσ : (ol_machine m ∘ π.symm) ∘ π = ol_machine m := by
    funext j
    simp
  refine ⟨π, ol_machine m ∘ π.symm, ?_, ?_⟩
  · rw [hσ, hπ]
    exact ol_isListSchedule m
  · rw [← makespan_comp_internal (grahamJobs m) (ol_machine m ∘ π.symm) π, hσ, hπ]
    exact ol_makespan m

end GrahamLPT
