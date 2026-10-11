# ARCH — the module map of `graham-lpt-lean` (desk, 2026-10-11; stripped before registration)

The pinned statements are `Challenge.lean` (read-only for lanes); the definitions are restated in `GrahamLPT/Defs.lean`
(read-only). Each module below holds the `_internal` twins of its Challenge theorems and the desk's pinned helpers, all
`sorry` in the skeleton; `Solution.lean` closes every Challenge theorem by its twin. The desk's exact replay of every
hypothesis is the bench's `probe.py` (`bench/rt-073-graham-lpt/`, 7,327,865 checks, PROBE: PASS; README.md there is the
pre-registration with the proofs in prose, items (i)–(vi)).

Conventions. Jobs `p : Fin n → ℝ`, machines `Fin m` with `[NeZero m]` where a makespan is involved; `loadBefore p σ k i`
is the load of machine `i` from the jobs of index `< k` (`k : ℕ`; a `Fin n` is coerced), `load p σ i` the full load,
`makespan p σ = univ.sup' univ_nonempty (load p σ)`, `optMakespan m p = univ.inf' univ_nonempty (makespan p ·)`.
`IsListSchedule p σ : ∀ k i, loadBefore p σ k (σ k) ≤ loadBefore p σ k i`; `IsLPTSchedule p σ : ∃ π, Antitone (p ∘ π) ∧
IsListSchedule (p ∘ π) (σ ∘ π)`. Write `L_k := loadBefore p σ k (σ k)` (the least load before `k` in a list schedule).

## §1 Basic (lane `basic`) — the ground floor, imported by everyone
`bs_loadBefore_zero`, `bs_loadBefore_succ` (`Finset.filter` of `j < k + 1 ∧ σ j = i` is the filter of `j < k ∧ σ j = i`
with `k` added when `σ k = i`: `Finset.filter_or`/`Finset.sum_filter` or `Finset.sum_ite`, or prove through
`∑ j, if (j:ℕ) < k ∧ σ j = i then p j else 0` by `Finset.sum_filter` and split the `if` with `omega` on indices),
`bs_loadBefore_of_le` (the index condition is vacuous: `Finset.filter_congr`), `bs_sum_loadBefore` and `bs_sum_load`
(`Finset.sum_fiberwise` / `Finset.sum_comm` with `Finset.sum_ite_eq`), `bs_sum_filter_add_le` (`Finset.sum_le_sum_of_subset_of_nonneg`
with `insert k (filter (· < k))`, or `Finset.add_sum_erase`), `bs_loadBefore_nonneg`, `bs_loadBefore_mono`,
`bs_loadBefore_le_load` (`Finset.sum_le_sum_of_subset_of_nonneg`, the filters nested), `bs_load_eq_zero`, `bs_loadBefore_eq_zero`
(empty filter), `bs_exists_last_job` and `bs_exists_last_job_before` (`Finset.exists_max_image` on the nonempty fiber; the fiber
below the cutoff splits as the fiber below `k` plus `k`), `bs_mul_loadBefore_le` (`m · L_k ≤ Σ_i loadBefore k i` since `L_k ≤`
every term: `Finset.card_nsmul_le_sum` or `Finset.sum_le_sum` with `Finset.sum_const`, then `bs_sum_loadBefore`),
`bs_makespan_le_iff` (`Finset.sup'_le_iff`), `bs_exists_load_eq_makespan` (`Finset.exists_mem_eq_sup'`), `bs_makespan_nonneg`,
`bs_load_comp` (`Finset.sum_equiv π` or `Equiv.sum_comp` after rewriting the filter: `σ (π j) = i ↔ j ∈ π⁻¹ (fiber)`; or write
`load` as `∑ j, if σ j = i then p j else 0` by `Finset.sum_filter` and use `Equiv.sum_comp`), `bs_sum_le_mul_optMakespan`
and `bs_le_optMakespan_of_nonneg` (through an optimal `τ`).
The Challenge twins: `load_le_makespan` (`Finset.le_sup'`); `le_makespan_of_nonneg` (`p j ≤ load p σ (σ j)`: a single term
of a nonnegative sum, `Finset.single_le_sum`); `sum_le_mul_makespan` (`bs_sum_load`, each load `≤ makespan`, `Finset.sum_le_sum`,
`Finset.sum_const`, `Finset.card_univ`, `Fintype.card_fin`); `makespan_comp` (`bs_load_comp` under `sup'`, `Finset.sup'_congr`);
`optMakespan_le` (`Finset.inf'_le`); `exists_makespan_eq_optMakespan` (`Finset.exists_mem_eq_inf'`); `exists_isListSchedule`:
build the greedy state by recursion on `k : ℕ` — `greedyLoads 0 = 0`, `greedyAssign k := ` a minimizer of `greedyLoads k` on
`univ` (`Finset.exists_min_image univ _ univ_nonempty`, `Classical.choose`), `greedyLoads (k+1) = greedyLoads k + Pi.single
(greedyAssign k) (if h : k < n then p ⟨k, h⟩ else 0)`; set `σ j := greedyAssign j` and prove `loadBefore p σ k = greedyLoads k`
by induction on `k` with `bs_loadBefore_succ` (for `k ≥ n` both sides stop changing); `exists_isLPTSchedule`: `π := Tuple.sort
(fun j => -p j)` (Mathlib `Tuple.monotone_sort` gives `Monotone ((-p) ∘ π)`, hence `Antitone (p ∘ π)`), a list schedule `σ'` of
`p ∘ π` by the previous theorem, `σ := σ' ∘ π.symm` (so `σ ∘ π = σ'`: `Equiv.self_comp_symm`-style `funext`/`simp`).

## §2 ListBound (lane `listbound`) — Graham 1966
`lb_mul_le`: `m · L_k ≤ Σ_{j<k} p` (`bs_mul_loadBefore_le`) and `Σ_{j<k} p + p_k ≤ Σ p` (`bs_sum_filter_add_le`), so
`m(L_k + p_k) ≤ Σ p − p_k + m p_k`; `linarith`. `listSchedule_bound`: take `i` with `load p σ i = makespan p σ`
(`bs_exists_load_eq_makespan`); if no job sits on `i`, the makespan is `0 ≤ (2m − 1)·C(τ)` (`bs_makespan_nonneg`, `2m − 1 ≥ 1`);
else its last job `k` (`bs_exists_last_job`) gives `C(σ) = L_k + p_k` — careful: `loadBefore p σ k i` with `σ k = i` is `L_k` —
then `lb_mul_le`, `sum_le_mul_makespan` for `τ` and `le_makespan_of_nonneg` for `p_k ≤ C(τ)`; `linarith` (`(m : ℝ) ≥ 1` from
`NeZero.pos`, `Nat.one_le_cast`). `listSchedule_le_optMakespan`: the bound at an optimal `τ` (`exists_makespan_eq_optMakespan`),
divide by `m > 0` (`le_div_iff₀`-style or `nlinarith`-free: multiply out `(2 − 1/m) · O = ((2m − 1)/m) · O`, `field_simp`).

## §3 Key (lane `key`) — the key lemma, by counting (README (i))
`key_lemma`: by contradiction, suppose `T < L_k + p_k`. (a) Every machine `i` has a job before `k`: else `loadBefore p σ k i = 0`
(`bs_loadBefore_eq_zero`), so `L_k ≤ 0`, so `L_k = 0` (nonneg), so `L_k + p_k = p_k ≤ loadBefore p τ (k+1) (τ k) ≤ T` (the single
term `p k` of the `τ`-fiber below `k + 1`: `Finset.single_le_sum`), contradiction. (b) Let `A := univ.filter (fun j : Fin n =>
(j:ℕ) < k)` (card `k`: `Finset.card_filter`/`Fin.card_filter_lt`-style, or show `A.card = k` via `Finset.card_eq_of_equiv` with
`Fin k`), fibered by `σ`: `a i := (A.filter (σ · = i)).card ≥ 1` (by (a)); `S := univ.filter (fun i => a i = 1)`, `s := S.card`;
then `k = Σ_i a_i ≥ s + 2(m − s)` (`Finset.card_eq_sum_card_fiberwise`, `Finset.sum_le_sum` with `a_i ≥ 2` off `S`,
`Finset.sum_ite`/split over `S` and its complement). (c) `B := univ.filter (fun j : Fin n => (j:ℕ) ≤ k ∧ L_k ≤ p j)`. For `j ∈ B`
and `j' ≠ j` with `(j':ℕ) ≤ k` and `τ j' = τ j`: `loadBefore p τ (k+1) (τ j) ≥ p j + p j' ≥ L_k + p k > T` (two terms of a
nonnegative sum: `Finset.add_le_sum`-style via `Finset.sum_le_sum_of_subset_of_nonneg` on `{j, j'}`, `Finset.sum_pair`; `p j' ≥ p k`
by `hanti` since `j' ≤ k`), contradiction with `hT`; so `τ` is injective on `B` and the `τ`-fiber of any `j ∈ B` within
`A' := univ.filter (fun j : Fin n => (j:ℕ) ≤ k)` is `{j}`. Any `τ`-fiber within `A'` has at most two elements (three distinct
jobs `≤ k` give `≥ 3 p_k > T`: `Finset.sum_le_sum_of_subset_of_nonneg` on a 3-subset, `Finset.card_eq_three`). Hence
`k + 1 = A'.card = Σ_i b_i ≤ |τ(B)| · 1 + (m − |τ(B)|) · 2` with `|τ(B)| = B.card` (`Finset.card_image_of_injOn`), i.e.
`k + 1 ≤ 2m − B.card`. (d) For `i ∈ S` the unique job `j_i ∈ A` with `σ j_i = i` has `loadBefore p σ k i = p j_i` (the fiber is
`{j_i}`: `Finset.card_eq_one`, `Finset.sum_singleton`), and `L_k ≤ loadBefore p σ k i` (`hσ`), so `j_i ∈ B`; `i ↦ j_i` is
injective (`σ j_i = i`), so `s ≤ B.card` (`Finset.card_le_card_of_injOn`). (e) `k ≥ 2m − s ≥ 2m − B.card ≥ k + 1`: `omega`.
`key_optimal_sorted`: every machine's load is `0` or `L_k + p_k` for its last job `k` (`bs_exists_last_job`), and
`loadBefore p τ (k+1) i ≤ load p τ i ≤ makespan p τ` (`bs_loadBefore_le_load`, `load_le_makespan`), `h k` gives `3 p_k > C(τ)`,
so `key_lemma` gives `≤ C(τ)`; `bs_makespan_le_iff`. `lpt_optimal_of_third_lt`: unpack `hσ = ⟨π, hπ, hlist⟩`; apply the sorted
form to `p ∘ π`, `σ ∘ π`, `τ ∘ π` (`h (π j)`) and rewrite both sides with `makespan_comp`. `lpt_eq_optMakespan_of_third_lt`:
`le_antisymm` of the previous theorem at an optimal `τ` and `optMakespan_le`.

## §4 LPTBound (lane `lptbound`) — Graham 1969 (README (ii))
`lb2_bound_sorted`: take `i` with `load p σ i = makespan p σ`; no job on `i`: `0 ≤ RHS`; else its last job `k`, `C(σ) = L_k + p_k`.
Case `3 p_k ≤ C(τ)`: `m L_k ≤ Σ_{j<k} p ≤ Σ p − p_k ≤ m C(τ) − p_k` (`bs_mul_loadBefore_le`, `bs_sum_filter_add_le`,
`sum_le_mul_makespan`), so `3m(L_k + p_k) ≤ 3m C(τ) + 3(m − 1) p_k ≤ 3m C(τ) + (m − 1) C(τ)`; `linarith` with `(m:ℝ) ≥ 1`.
Case `C(τ) < 3 p_k`: `key_lemma` with `T := C(τ)` (`hT` from `bs_loadBefore_le_load` and `load_le_makespan`) gives
`L_k + p_k ≤ C(τ)`, and `3m · C(τ) ≤ (4m − 1) C(τ)` since `C(τ) ≥ 0` and `m ≥ 1`. `lpt_bound`: unpack `π`, apply to
`p ∘ π`, `σ ∘ π`, `τ ∘ π`, `makespan_comp` twice. `lpt_le_optMakespan`: at an optimal `τ`, `(4/3 − 1/(3m)) · O = ((4m − 1)/(3m)) · O`
(`field_simp`, `ring`), then divide (`m > 0`).

## §5 TightList (lane `tightlist`) — the unit-job family (README (v))
`tl_unitJobs_apply_*`, `tl_unitJobs_nonneg` by `unfold unitJobs; split_ifs; norm_num`. `tl_loadBefore_le` by induction on `k`:
`k = 0` is `0 ≤ m − 1`; step `k → k + 1` (`k < m(m − 1)`, so `⟨k, _⟩ : Fin _` and `unitJobs m ⟨k, _⟩ = 1`): `bs_loadBefore_succ`;
for `i = σ k`: `m · L_k ≤ Σ_{j<k} unitJobs = k` (`bs_mul_loadBefore_le`; the filtered sum of ones has value `k`:
`Finset.sum_const`, the card of `{j : Fin _ | (j:ℕ) < k}` is `k` — prove `card = k` via `Finset.card_eq_of_equiv` or by
`Fin.card_filter_val_lt`-style lemmas; search `Fin.card_filter_lt`), so `m(L_k + 1) ≤ k + m`; for `i ≠ σ k` monotone in `k`.
`tl_loadBefore_units`: at `k = m(m − 1)` the loads are nonnegative integers (`loadBefore` of unit jobs is the cardinality of the
fiber: `Finset.sum_const` after `Finset.sum_congr` with `tl_unitJobs_apply_lt`), each `≤ m − 1` (from `m · c ≤ m(m − 1) + m − 1 =
m² − 1` with `c : ℕ`, `omega` after `Nat.cast` lemmas), summing to `m(m − 1)` (`bs_sum_loadBefore`); so all equal `m − 1`
(`Finset.sum_eq_sum_iff_of_le` or: if some `c_i < m − 1` then `Σ < m(m − 1)` by `Finset.sum_lt_sum`). `unitJobs_listSchedule_makespan`:
`≤` from `listSchedule_bound` at `τ` of makespan `m` (`tl_exists_makespan_eq`) — `m · C ≤ (2m − 1) m` — and `≥`: the last job
`⟨m(m − 1), _⟩` of length `m` lands on a machine of load `m − 1` (`tl_loadBefore_units`, `bs_loadBefore_succ`,
`bs_loadBefore_of_le`), so some load is `2m − 1` (`load_le_makespan`). `tl_exists_makespan_eq`: `τ j := if h : (j:ℕ) < m(m − 1)
then ⟨j % (m − 1), _⟩ else ⟨m − 1, _⟩` (inside the branch `m ≥ 2`, so `Nat.mod_lt`); machine `i < m − 1` carries the unit jobs
`{j < m(m − 1) : j % (m − 1) = i}`, exactly `m` of them (the image of `t ↦ i + t(m − 1)`, `t < m`: `Finset.card_image_of_injective`
or count by `Nat.count`/`Nat.card_multiples`-style lemmas; search `Nat.filter_modEq_card`/`Nat.card_filter_mod_eq`); machine
`m − 1` carries only the long job (for `m ≥ 2`; for `m = 1` the unique job of length `1`). `tl_le_makespan`:
`le_makespan_of_nonneg` at the long job. `unitJobs_optMakespan`: `le_antisymm` (`optMakespan_le` at `τ`; `tl_le_makespan` at an
optimal `τ`).

## §6 TightLPT (lane `tightlpt`) — Graham's family (README (iv))
`tg_grahamJobs_apply_*`, nonneg, `tg_le_grahamJobs` (`j/2 ≤ m − 1` for `j < 2m`: `omega` after `Nat.div_le_iff`-style facts,
cast with `push_cast`, `Nat.cast_sub` guarded by `m ≥ 1` or by cases on `m = 0`), `tg_grahamJobs_le`. `grahamJobs_antitone`:
`j ≤ j'` gives `j/2 ≤ j'/2` (`Nat.div_le_div_right`), and the last job `m ≤ 2m − 1 − (j/2)` for `j < 2m`. `tg_grahamJobs_sum`:
`Finset.sum_fin_eq_sum_range`-style (`Fin.sum_univ_eq_sum_range`), split the last term, pair `2a, 2a + 1` by induction on `m`
(`Finset.sum_range_succ`; value `2(2m − 1 − a)` summed over `a < m` is `2(2m² − m − m(m − 1)/2) = 3m² − m`, so the total is
`3m² − m + m`); or `Finset.sum_range_succ` induction with `grahamJobs (m)` re-expressed — note `grahamJobs m` depends on `m`
in every term, so induct on an auxiliary `Σ_{j < 2k} (c − j/2)` with `c` fixed. `tg_pair`, `tg_pair'`: unfold, cases on the
parity of `j` (`Nat.even_or_odd`, `obtain ⟨a, rfl | rfl⟩ := Nat.even_or_odd' j`), `omega` for the `ℕ` divisions, `push_cast`,
`ring`/`linarith`. `tg_exists_opt`: `τ₀ j := if h : (j:ℕ) < 2m − 2 then ⟨min j (2m − 3 − j), _⟩ else ⟨m − 1, _⟩`; the fiber of
`i < m − 1` is `{⟨i, _⟩, ⟨2m − 3 − i, _⟩}` (`Finset.ext`, `Fin.ext_iff`, `omega` through the `dite`), the fiber of `m − 1` is
`{2m − 2, 2m − 1, 2m}`; `Finset.sum_pair`/`Finset.sum_insert` and `tg_pair'`, `tg_grahamJobs_apply_last`. `tg_le_makespan`:
`tg_grahamJobs_sum` and `sum_le_mul_makespan`: `3m² ≤ m · C`, divide by `m > 0`. `grahamJobs_optMakespan`: `le_antisymm`
(`optMakespan_le` at `τ₀` with `bs_makespan_le_iff`/`exists_load_eq`; `tg_le_makespan`). `tg_exists_prefix_pairing`: `τ' j :=
if h : (j:ℕ) < 2m then ⟨min j (2m − 1 − j), _⟩ else ⟨0, _⟩`; the fiber of `i` below the cutoff `2m` is `{i, 2m − 1 − i}`, `tg_pair`.
`tg_loadBefore_two_mul`: for each `k < 2m`, `key_lemma` with `τ'` and `T := 3m − 1` (`hT`: `loadBefore τ' (k+1) i ≤ loadBefore τ'
(2m) i = 3m − 1` by `bs_loadBefore_mono`; `h3`: `3m − 1 < 3 · grahamJobs m k` from `tg_le_grahamJobs`) gives `L_k + p_k ≤ 3m − 1`;
every machine's load before `2m` is `0` or `L_k + p_k` for its last job `k < 2m` (`bs_exists_last_job_before`,
`bs_loadBefore_eq_zero`) — but `0 < 3m − 1` cannot occur, since … it can: handle it by the sum: all loads `≤ 3m − 1` and
`Σ_i loadBefore (2m) i = Σ_{j<2m} grahamJobs = 3m² − m = m(3m − 1)` (`bs_sum_loadBefore`, `tg_grahamJobs_sum` minus the last
job), so every load is exactly `3m − 1` (`Finset.sum_lt_sum` contradiction). `tg_listSchedule_makespan`: `≤` from `lpt_bound` with
`⟨1, grahamJobs_antitone, hσ⟩` at `τ₀` (`3m · C ≤ (4m − 1) · 3m`); `≥`: the last job `⟨2m, _⟩` lands on a machine of load `3m − 1`
(`bs_loadBefore_succ`, `bs_loadBefore_of_le`, `tg_grahamJobs_apply_last`), so `4m − 1 ≤ C`. `tg_comp_eq`: `Tuple.unique_antitone h
(by simpa using grahamJobs_antitone m : Antitone (grahamJobs m ∘ (1 : Equiv.Perm _)))`. `grahamJobs_lpt_makespan`: unpack `π`;
`tg_comp_eq` turns `IsListSchedule (grahamJobs m ∘ π) (σ ∘ π)` into `IsListSchedule (grahamJobs m) (σ ∘ π)`;
`tg_listSchedule_makespan` and `makespan_comp`.

## §7 OptList (lane `optlist`) — the optimum attained by a list (README (iv), the explicit order)
`ol_index_bijective`: injective by cases on the five branches (`Fin.ext_iff`, `omega`; the images are the evens below `2m − 2`,
`2m − 2`, `2m − 1`, the odds below `2m − 1`, and `2m`), surjective by `Finite.injective_iff_surjective`/`Fintype.bijective_iff_injective_and_card`.
`ol_isListSchedule`: for each position `k`, compute every `loadBefore (grahamJobs m ∘ ol_index m) (ol_machine m) k i` as a
sum over an explicit fiber of at most two positions (`Finset.ext` + `omega` over the branches of `ol_machine` and `ol_index`, then
`Finset.sum_pair`/`sum_singleton`/`sum_empty` and `tg_grahamJobs_apply_*`): before position `i < m − 1` the fibers are `{i'}` for
`i' < i` (load `2m − 1 − i' > 0`) and empty otherwise (load `0` — the least, attained at machine `i`); before `m − 1`: machine `m − 1`
is empty; before `m`: machine `m − 1` has load `m`, machine `b < m − 1` has `2m − 1 − b ≥ m + 1`; before `m + 1 + a` (`a < m − 1`):
machine `m − 2 − a` has `m + 1 + a`, machines `b < m − 2 − a` have `2m − 1 − b > m + 1 + a`, machines `m − 2 − a' ` for `a' < a` have
`3m`, machine `m − 1` has `2m ≥ m + 1 + a`; before `2m`: machine `m − 1` has `2m`, the others `3m`. `ol_makespan`: the final loads are
`3m` on every machine (the same fibers at cutoff `2m + 1`, `bs_loadBefore_of_le`), `bs_makespan_le_iff` and `load_le_makespan`.
`grahamJobs_exists_optimal_listSchedule`: `π := Equiv.ofBijective _ (ol_index_bijective m)`, `σ := ol_machine m ∘ π.symm`;
`σ ∘ π = ol_machine m` and `grahamJobs m ∘ π = grahamJobs m ∘ ol_index m` (`Equiv.ofBijective_apply`), then `makespan_comp`
in reverse: `makespan (grahamJobs m) σ = makespan (grahamJobs m ∘ π) (σ ∘ π) = 3m`.

## §8 Ratio (lane `ratio`) — the least constants (README (vi))
`isLeast_listSchedule_ratio`: membership from `listSchedule_bound` (`m · C(σ) ≤ (2m − 1) C(τ)` and `(2 − 1/m) · C(τ) =
((2m − 1)/m) · C(τ)`, divide by `m > 0`: `le_div_iff₀`, `div_mul_eq_mul_div`, `field_simp`); lower bound: for `c` in the set,
instantiate at `n := m(m − 1) + 1`, `p := unitJobs m`, a list schedule `σ` (`exists_isListSchedule`), an optimal `τ`
(`exists_makespan_eq_optMakespan`, `unitJobs_optMakespan`): `2m − 1 = C(σ) ≤ c · m` (`unitJobs_listSchedule_makespan`), so
`c ≥ (2m − 1)/m = 2 − 1/m` (`tl_unitJobs_nonneg` for the nonnegativity hypothesis). `isLeast_lpt_ratio`: likewise with `lpt_bound`,
`grahamJobs`, an LPT schedule (`exists_isLPTSchedule`), `grahamJobs_lpt_makespan`, `grahamJobs_optMakespan`: `4m − 1 ≤ c · 3m`.

## Rules (binding; the preamble has the rest)
1. Lanes edit only their own module; the Challenge, Defs and Solution are read-only; helpers carry the lane prefix.
2. A pin that is false as stated is not edited: prove the nearest correct statement under a new name and report the defect.
3. One `bash scripts/lane-build.sh GrahamLPT.<Module>` per call; never `lake build` directly; never the library root.
4. No `sorry`, `axiom`, `native_decide`, `set_option`, `mutual`, `unsafe`, `partial` in any shipped module; `decide` on tiny goals only.
5. Do not prove extras for other lanes; what a neighbour needs is already pinned (the audit strips unreferenced declarations).
6. Report ≤ 60 lines: proved, unproved (with the obstacle), defects, the final commit hash on `desk/<lane>`.
