module

public import GrahamLPT.Basic

/-!
# CoffmanSethi

Chen's property of LPT schedules (Chen 1993, Prop. 2 as quoted by Della Croce–Scatamacchia 2020): in an LPT
schedule the `j`-th job placed on a machine has length at most `C(τ)/j` for every assignment `τ`; hence, when a
machine attaining the makespan holds `k` jobs, `k·m·C(σ) ≤ ((k + 1)m − 1)·C(τ)` (the Coffman–Sethi form).
Stretch lane `coffman`. Helpers carry the prefix `cs_`.

The route (this development). Fix `P > 0` below every job placed so far and weigh a job `x` by `⌊x/P⌋`. For two
machines `h, g` write `D` for the load of `h` minus the load of `g`, `Φ` for the weight of `h` minus the number of
jobs on `g`, and `y` for the last job placed. The invariant `cs_Inv` (`D ≥ 0 → ⌊D/P⌋ ≤ Φ`;
`D < 0 → −1 ≤ Φ ∧ ⌊(D + y)/P⌋ − 1 ≤ Φ`) holds at every step of a list schedule in nonincreasing order, since a job
joins a least-loaded machine. With `g` the machine receiving job `k`, every machine weighs at least the number of
jobs on `g` before `k`; summing over the machines and comparing with `τ`, where a machine's weight is below `j`
when its load is below `j·p_k`, gives `j · p_k ≤ C(τ)`.
-/

@[expose] public section

namespace GrahamLPT

open Finset

/-- The number of jobs of index below `k` on machine `i`, as an integer. -/
def cs_cnt {m n : ℕ} (σ : Fin n → Fin m) (k : ℕ) (i : Fin m) : ℤ :=
  ∑ j ∈ univ.filter (fun j : Fin n => (j : ℕ) < k ∧ σ j = i), (1 : ℤ)

/-- The weight `Σ ⌊p_j / P⌋` of the jobs of index below `k` on machine `i`. -/
noncomputable def cs_fl {m n : ℕ} (p : Fin n → ℝ) (P : ℝ) (σ : Fin n → Fin m) (k : ℕ) (i : Fin m) : ℤ :=
  ∑ j ∈ univ.filter (fun j : Fin n => (j : ℕ) < k ∧ σ j = i), ⌊p j / P⌋

/-- The two-machine invariant: `D` a load difference, `y` the last job, `Φ` a weight minus a count. -/
def cs_Inv (P D y : ℝ) (Φ : ℤ) : Prop :=
  (0 ≤ D → ⌊D / P⌋ ≤ Φ) ∧ (D < 0 → -1 ≤ Φ ∧ ⌊(D + y) / P⌋ - 1 ≤ Φ)

theorem cs_sum_succ {M : Type*} [AddCommMonoid M] {m n : ℕ} (f : Fin n → M) (σ : Fin n → Fin m) (k : Fin n)
    (i : Fin m) :
    ∑ j ∈ univ.filter (fun j : Fin n => (j : ℕ) < (k : ℕ) + 1 ∧ σ j = i), f j =
      (∑ j ∈ univ.filter (fun j : Fin n => (j : ℕ) < k ∧ σ j = i), f j) + if σ k = i then f k else 0 := by
  by_cases h : σ k = i
  · have e : univ.filter (fun j : Fin n => (j : ℕ) < (k : ℕ) + 1 ∧ σ j = i) =
        insert k (univ.filter (fun j : Fin n => (j : ℕ) < k ∧ σ j = i)) := by
      ext j
      simp only [mem_filter, mem_univ, true_and, mem_insert]
      constructor
      · rintro ⟨h1, h2⟩
        by_cases hjk : j = k
        · exact Or.inl hjk
        · have : (j : ℕ) ≠ k := fun e => hjk (Fin.ext e)
          exact Or.inr ⟨by omega, h2⟩
      · rintro (rfl | ⟨h1, h2⟩)
        · exact ⟨by omega, h⟩
        · exact ⟨by omega, h2⟩
    rw [e, sum_insert (by simp), ite_eq_left h, add_comm]
  · have e : univ.filter (fun j : Fin n => (j : ℕ) < (k : ℕ) + 1 ∧ σ j = i) =
        univ.filter (fun j : Fin n => (j : ℕ) < k ∧ σ j = i) := by
      ext j
      simp only [mem_filter, mem_univ, true_and]
      constructor
      · rintro ⟨h1, h2⟩
        have hjk : j ≠ k := fun e => h (e ▸ h2)
        have : (j : ℕ) ≠ k := fun e => hjk (Fin.ext e)
        exact ⟨by omega, h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨by omega, h2⟩
    rw [e, ite_eq_right h, add_zero]

theorem cs_sum_fiber {M : Type*} [AddCommMonoid M] {m n : ℕ} (f : Fin n → M) (σ : Fin n → Fin m) (k : ℕ) :
    ∑ i, ∑ j ∈ univ.filter (fun j : Fin n => (j : ℕ) < k ∧ σ j = i), f j =
      ∑ j ∈ univ.filter (fun j : Fin n => (j : ℕ) < k), f j := by
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [ite_and]
  by_cases h : (j : ℕ) < k
  · simp [h, Finset.sum_ite_eq]
  · simp [h]

theorem cs_inv_mono {P D y y' : ℝ} {Φ : ℤ} (hP : 0 < P) (h : cs_Inv P D y Φ) (hy : y' ≤ y) :
    cs_Inv P D y' Φ := by
  refine ⟨h.1, fun hD => ⟨(h.2 hD).1, ?_⟩⟩
  have h1 : ⌊(D + y') / P⌋ ≤ ⌊(D + y) / P⌋ :=
    Int.floor_le_floor (div_le_div_of_nonneg_right (by linarith) hP.le)
  have := (h.2 hD).2
  omega

theorem cs_inv_self {P y : ℝ} {Φ : ℤ} (hΦ : 0 ≤ Φ) : cs_Inv P 0 y Φ := by
  refine ⟨fun _ => by simpa using hΦ, fun h => absurd h (lt_irrefl 0)⟩

/-- The receiving machine is the second of the pair (`D ≥ 0`): it gains a job of length `x ≥ P`. -/
theorem cs_inv_istep {P D y x : ℝ} {Φ : ℤ} (hP : 0 < P) (hx : P ≤ x) (hD : 0 ≤ D) (h : cs_Inv P D y Φ) :
    cs_Inv P (D - x) x (Φ - 1) := by
  have h0 := h.1 hD
  have hf0 : 0 ≤ ⌊D / P⌋ := Int.floor_nonneg.2 (div_nonneg hD hP.le)
  refine ⟨fun hD' => ?_, fun _ => ⟨by omega, ?_⟩⟩
  · have h1 : (D - x) / P ≤ D / P - 1 := by
      rw [div_sub_one hP.ne', div_le_div_iff_of_pos_right hP]
      linarith
    have h2 : ⌊(D - x) / P⌋ ≤ ⌊D / P - 1⌋ := Int.floor_le_floor h1
    rw [Int.floor_sub_one] at h2
    omega
  · have e : D - x + x = D := by ring
    rw [e]
    omega

/-- The receiving machine is the first of the pair (`D ≤ 0`): it gains a job `x` with `P ≤ x ≤ y`. -/
theorem cs_inv_hstep {P D y x : ℝ} {Φ : ℤ} (hP : 0 < P) (hx : P ≤ x) (hxy : x ≤ y) (hD : D ≤ 0)
    (h : cs_Inv P D y Φ) : cs_Inv P (D + x) x (Φ + ⌊x / P⌋) := by
  have hf1 : 1 ≤ ⌊x / P⌋ := by
    rw [Int.le_floor, Int.cast_one, le_div_iff₀ hP]
    linarith
  rcases hD.lt_or_eq with hD | hD
  · obtain ⟨hm1, hy⟩ := h.2 hD
    refine ⟨fun hD' => ?_, fun hD' => ⟨by omega, ?_⟩⟩
    · have h1 : ⌊(D + x) / P⌋ ≤ ⌊(D + y) / P⌋ :=
        Int.floor_le_floor (div_le_div_of_nonneg_right (by linarith) hP.le)
      omega
    · have h1 : ⌊(D + x + x) / P⌋ ≤ ⌊x / P⌋ :=
        Int.floor_le_floor (div_le_div_of_nonneg_right (by linarith) hP.le)
      omega
  · subst hD
    have h0 := h.1 le_rfl
    simp only [zero_div, Int.floor_zero] at h0
    refine ⟨fun _ => ?_, fun hD' => absurd hD' (by linarith)⟩
    rw [zero_add]
    omega

theorem cs_cnt_le_fl {m n : ℕ} (p : Fin n → ℝ) {P : ℝ} (hP : 0 < P) (σ : Fin n → Fin m) (k : ℕ)
    (hk : ∀ j : Fin n, (j : ℕ) < k → P ≤ p j) (i : Fin m) : cs_cnt σ k i ≤ cs_fl p P σ k i := by
  unfold cs_cnt cs_fl
  refine Finset.sum_le_sum fun j hj => ?_
  simp only [mem_filter, mem_univ, true_and] at hj
  rw [Int.le_floor, Int.cast_one, le_div_iff₀ hP, one_mul]
  exact hk j hj.1

theorem cs_cnt_zero {m n : ℕ} (σ : Fin n → Fin m) (i : Fin m) : cs_cnt σ 0 i = 0 := by
  simp [cs_cnt]

theorem cs_fl_zero {m n : ℕ} (p : Fin n → ℝ) (P : ℝ) (σ : Fin n → Fin m) (i : Fin m) : cs_fl p P σ 0 i = 0 := by
  simp [cs_fl]

/-- The invariant along a list schedule in nonincreasing order, for every pair of machines. -/
theorem cs_inv_all {m n : ℕ} (p : Fin n → ℝ) (hanti : Antitone p) (σ : Fin n → Fin m)
    (hσ : IsListSchedule p σ) {P : ℝ} (hP : 0 < P) :
    ∀ k : ℕ, k ≤ n → (∀ j : Fin n, (j : ℕ) < k → P ≤ p j) → ∀ h g : Fin m, ∀ y : ℝ,
      (∀ j : Fin n, (j : ℕ) + 1 = k → y ≤ p j) →
      cs_Inv P (loadBefore p σ k h - loadBefore p σ k g) y (cs_fl p P σ k h - cs_cnt σ k g) := by
  intro k
  induction k with
  | zero =>
    intro _ _ h g y _
    rw [bs_loadBefore_zero, bs_loadBefore_zero, cs_fl_zero, cs_cnt_zero, sub_self, sub_self]
    exact cs_inv_self le_rfl
  | succ k ih =>
    intro hk hPk h g y hy
    set kk : Fin n := ⟨k, by omega⟩ with hkk
    have hkv : (kk : ℕ) = k := rfl
    have hPk' : ∀ j : Fin n, (j : ℕ) < k → P ≤ p j := fun j hj => hPk j (by omega)
    have hx : P ≤ p kk := hPk kk (by simp [kk])
    have hyx : y ≤ p kk := hy kk (by simp [kk])
    have IH := ih (by omega) hPk' h g (p kk) (fun j hj => hanti (show j ≤ kk from Fin.le_def.2 (by omega)))
    by_cases hhg : h = g
    · subst hhg
      rw [sub_self]
      refine cs_inv_self ?_
      have := cs_cnt_le_fl p hP σ (k + 1) hPk h
      omega
    have eL : ∀ i, loadBefore p σ (k + 1) i = loadBefore p σ k i + if σ kk = i then p kk else 0 :=
      fun i => bs_loadBefore_succ p σ kk i
    have eF : ∀ i, cs_fl p P σ (k + 1) i = cs_fl p P σ k i + if σ kk = i then ⌊p kk / P⌋ else 0 :=
      fun i => cs_sum_succ (fun j => ⌊p j / P⌋) σ kk i
    have eC : ∀ i, cs_cnt σ (k + 1) i = cs_cnt σ k i + if σ kk = i then 1 else 0 :=
      fun i => cs_sum_succ (fun _ => (1 : ℤ)) σ kk i
    have hmin : ∀ i, loadBefore p σ k (σ kk) ≤ loadBefore p σ k i := fun i => hσ kk i
    rw [eL h, eL g, eF h, eC g]
    by_cases h1 : σ kk = h
    · have h2 : σ kk ≠ g := fun e => hhg (h1.symm.trans e)
      rw [ite_eq_left h1, ite_eq_right h2, ite_eq_left h1, ite_eq_right h2, add_zero, add_zero]
      have hD : loadBefore p σ k h - loadBefore p σ k g ≤ 0 := by
        have := hmin g
        rw [h1] at this
        linarith
      have := cs_inv_hstep hP hx le_rfl hD IH
      have e1 : loadBefore p σ k h + p kk - loadBefore p σ k g =
          loadBefore p σ k h - loadBefore p σ k g + p kk := by ring
      have e2 : cs_fl p P σ k h + ⌊p kk / P⌋ - cs_cnt σ k g =
          cs_fl p P σ k h - cs_cnt σ k g + ⌊p kk / P⌋ := by ring
      rw [e1, e2]
      exact cs_inv_mono hP this hyx
    · rw [ite_eq_right h1, ite_eq_right h1, add_zero, add_zero]
      by_cases h2 : σ kk = g
      · rw [ite_eq_left h2, ite_eq_left h2]
        have hD : 0 ≤ loadBefore p σ k h - loadBefore p σ k g := by
          have := hmin h
          rw [h2] at this
          linarith
        have := cs_inv_istep hP hx hD IH
        have e1 : loadBefore p σ k h - (loadBefore p σ k g + p kk) =
            loadBefore p σ k h - loadBefore p σ k g - p kk := by ring
        have e2 : cs_fl p P σ k h - (cs_cnt σ k g + 1) = cs_fl p P σ k h - cs_cnt σ k g - 1 := by ring
        rw [e1, e2]
        exact cs_inv_mono hP this hyx
      · rw [ite_eq_right h2, ite_eq_right h2, add_zero, add_zero]
        exact cs_inv_mono hP IH hyx

/-- Every machine weighs at least the number of jobs on the machine that receives job `k`, before `k`. -/
theorem cs_cnt_le_fl_of_min {m n : ℕ} (p : Fin n → ℝ) (hanti : Antitone p) (σ : Fin n → Fin m)
    (hσ : IsListSchedule p σ) {P : ℝ} (hP : 0 < P) (k : Fin n) (hk : ∀ j : Fin n, (j : ℕ) < k → P ≤ p j)
    (h : Fin m) : cs_cnt σ k (σ k) ≤ cs_fl p P σ k h := by
  have hI := cs_inv_all p hanti σ hσ hP k k.isLt.le hk h (σ k) P (fun j hj => hk j (by omega))
  have hD : 0 ≤ loadBefore p σ k h - loadBefore p σ k (σ k) := sub_nonneg.2 (hσ k h)
  have h1 := hI.1 hD
  have h2 : 0 ≤ ⌊(loadBefore p σ k h - loadBefore p σ k (σ k)) / P⌋ := Int.floor_nonneg.2 (div_nonneg hD hP.le)
  omega

end GrahamLPT
