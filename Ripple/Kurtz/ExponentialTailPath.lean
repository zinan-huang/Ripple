/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Ripple.CTMC.FrozenRandomIndexDoob

/-!
# Pathwise reading of the exponential martingale for density-dependent chains

This file is the pathwise half of the exponential martingale tail bound for the frozen
martingale part of a canonical density-dependent CTMC (FIX-KURTZ2 §3, Lemma 2.6, Theorem 3.1,
equations (3.2)–(3.4)).  Nothing here is probabilistic beyond one almost-sure event
`DensityDepCTMC.GoodRecords`; everything else is a statement about one record trajectory.

Notation.  For a record trajectory `ω` with path `path = M.canonicalPathMap ω`, the sojourn starts
are `τ k = path.sojournStart k = Σ_{j<k} H_{j+1}` (`τ 0 = 0`, `τ (k+1) = path.times k`), the states
are `Y k = path.stateSeq k = (ω k).2`, and `X u = path.frozenStateAt u` is the frozen readout.

* `CTMCPath.integral_Icc_frozen_eq_sum_sojourn`: the time integral of `h (X u)` over `[0, s]`
  split along the sojourns (piecewise-constant integrand).
* `DensityDepCTMC.GoodRecords`: the almost-sure record event (nonnegative holding times,
  positive holding times and genuine jumps with positive rate from non-absorbing states, frozen
  records after absorption, absorption or escape beyond the horizon, simplex invariance).
* `DensityDepCTMC.GoodRecords.exists_sojourn`: for every clock time `s ∈ [0, T]` there is a
  sojourn index `n` describing the readout on `[0, s]`.
* `DensityDepCTMC.expCompReal_split`: the compensator of the lattice tilt `θ x_i` splits as
  `θ N F_i(x/N) + κ` with `0 ≤ κ ≤ λ(x) θ² J²` when `|θ| J ≤ 1` (equation (3.2)).
* `DensityDepCTMC.GoodRecords.pathwise_identity` and `…pathExpSum_bound`: the pathwise identity
  `A(s) = A_n(T) − (s − τ_n) c(Y_n)` and the endpoint bound (3.4).
* `DensityDepCTMC.GoodRecords.frozen_martingale_coord_le_pathExpSum_max`: equation (3.3)–(3.4)
  for the frozen martingale part: `θ N M_i(s) − T N Λ θ² J² ≤ max (A_n(T), A_{n+1}(T) + |θ| J)`.

The exponential sum `pathExpSum` is the record-index functional `A_n(T)` written with the sojourn
starts; `pathExpSum_eq_clamped` identifies it with the clamped form used by the martingale module.
-/

namespace Ripple.CTMC

open MeasureTheory Set Finset

/-! ### Splitting a time integral along sojourns -/

section Path

variable {S : Type*}

/-- If the frozen readout is `stateSeq k` on `[τ k, τ (k+1))`, then it is `stateSeq k` at every
`u` with `τ k ≤ u < τ (k+1)` (monotone sojourn starts); this is the first-future-jump description
of `frozenStateAt`. -/
theorem CTMCPath.frozenStateAt_eq_stateSeq_of_sojourn (path : CTMCPath S)
    (hmono : Monotone path.sojournStart) (k : ℕ) {u : ℝ}
    (h1 : path.sojournStart k ≤ u) (h2 : u < path.sojournStart (k + 1)) :
    path.frozenStateAt u = path.stateSeq k := by
  refine path.frozenStateAt_eq_stateSeq_of_first_time_gt u k h2 ?_
  intro j hj
  have hjk : j + 1 ≤ k := Finset.mem_range.mp hj
  have : path.sojournStart (j + 1) ≤ path.sojournStart k := hmono hjk
  change ¬ u < path.sojournStart (j + 1)
  exact not_lt.mpr (this.trans h1)

/-- Time integral of a function of the frozen readout over `[0, s]`, split along the sojourns
`[τ k, τ (k+1))`, `k < n`, and the final piece `[τ n, s]`. -/
theorem CTMCPath.integral_Icc_frozen_eq_sum_sojourn (path : CTMCPath S) (h : S → ℝ)
    (hmono : Monotone path.sojournStart) {n : ℕ} {s : ℝ}
    (hint : IntegrableOn (fun u => h (path.frozenStateAt u)) (Icc 0 s) volume)
    (hns : path.sojournStart n ≤ s)
    (hk : ∀ k < n, ∀ u ∈ Ico (path.sojournStart k) (path.sojournStart (k + 1)),
      path.frozenStateAt u = path.stateSeq k)
    (hn : ∀ u ∈ Icc (path.sojournStart n) s, path.frozenStateAt u = path.stateSeq n) :
    ∫ u in Icc 0 s, h (path.frozenStateAt u) =
      ∑ k ∈ range n, (path.sojournStart (k + 1) - path.sojournStart k) * h (path.stateSeq k) +
        (s - path.sojournStart n) * h (path.stateSeq n) := by
  have hτ0 : path.sojournStart 0 = 0 := rfl
  have hτnn : ∀ k, 0 ≤ path.sojournStart k := fun k => hτ0 ▸ hmono (Nat.zero_le k)
  have hs0 : 0 ≤ s := (hτnn n).trans hns
  set f : ℝ → ℝ := fun u => h (path.frozenStateAt u) with hf
  have hII : ∀ a b, 0 ≤ a → a ≤ b → b ≤ s → IntervalIntegrable f volume a b := by
    intro a b ha hab hbs
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
    exact hint.mono_set (Ioc_subset_Icc_self.trans (Icc_subset_Icc ha hbs))
  -- the completed sojourns
  have hpiece : ∀ k < n, ∫ u in path.sojournStart k..path.sojournStart (k + 1), f u =
      (path.sojournStart (k + 1) - path.sojournStart k) * h (path.stateSeq k) := by
    intro k hkn
    have hle : path.sojournStart k ≤ path.sojournStart (k + 1) := hmono (Nat.le_succ k)
    have hae : ∀ᵐ u ∂volume, u ∉ ({path.sojournStart (k + 1)} : Set ℝ) :=
      measure_eq_zero_iff_ae_notMem.mp (measure_singleton _)
    have hcongr : ∫ u in path.sojournStart k..path.sojournStart (k + 1), f u =
        ∫ u in path.sojournStart k..path.sojournStart (k + 1), h (path.stateSeq k) := by
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [hae] with u hu hmem
      rw [Set.uIoc_of_le hle] at hmem
      have hu' : u ≠ path.sojournStart (k + 1) := by simpa using hu
      exact congrArg h (hk k hkn u ⟨hmem.1.le, lt_of_le_of_ne hmem.2 hu'⟩)
    rw [hcongr, intervalIntegral.integral_const, smul_eq_mul]
  have hlast : ∫ u in path.sojournStart n..s, f u = (s - path.sojournStart n) * h (path.stateSeq n) := by
    have hcongr : ∫ u in path.sojournStart n..s, f u =
        ∫ u in path.sojournStart n..s, h (path.stateSeq n) := by
      refine intervalIntegral.integral_congr fun u hu => ?_
      rw [Set.uIcc_of_le hns] at hu
      exact congrArg h (hn u hu)
    rw [hcongr, intervalIntegral.integral_const, smul_eq_mul]
  have hprefix : ∀ m ≤ n, ∫ u in (0 : ℝ)..path.sojournStart m, f u =
      ∑ k ∈ range m, (path.sojournStart (k + 1) - path.sojournStart k) * h (path.stateSeq k) := by
    intro m
    induction m with
    | zero => intro _; simp [hτ0]
    | succ m ih =>
      intro hm
      have hmn : m ≤ n := Nat.le_of_succ_le hm
      have hmle : path.sojournStart (m + 1) ≤ s := (hmono hm).trans hns
      rw [Finset.sum_range_succ, ← ih hmn, ← hpiece m (Nat.lt_of_succ_le hm)]
      exact (intervalIntegral.integral_add_adjacent_intervals
        (hII 0 _ le_rfl (hτnn m) ((hmono (Nat.le_succ m)).trans hmle))
        (hII _ _ (hτnn m) (hmono (Nat.le_succ m)) hmle)).symm
  calc ∫ u in Icc 0 s, f u = ∫ u in (0 : ℝ)..s, f u := by
        rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hs0]
    _ = (∫ u in (0 : ℝ)..path.sojournStart n, f u) + ∫ u in path.sojournStart n..s, f u :=
        (intervalIntegral.integral_add_adjacent_intervals
          (hII 0 _ le_rfl (hτnn n) hns) (hII _ _ (hτnn n) hns le_rfl)).symm
    _ = _ := by rw [hprefix n le_rfl, hlast]

end Path

namespace DensityDepCTMC

variable {d : ℕ} (M : DensityDepCTMC d)

/-! ### Record-trajectory readouts -/

@[simp]
theorem canonicalPathMap_stateSeq (ω : M.canonicalRecordΩ) (n : ℕ) :
    (M.canonicalPathMap ω).stateSeq n = (ω n).2 :=
  QMatrix.recordTrajectoryToPath_stateSeq ω n

theorem canonicalPathMap_times (ω : M.canonicalRecordΩ) (n : ℕ) :
    (M.canonicalPathMap ω).times n = ∑ k ∈ range (n + 1), (ω (k + 1)).1 :=
  rfl

/-- `τ k = Σ_{j<k} H_{j+1}`: the sojourn starts of the canonical path are the partial sums of
the sampled holding times. -/
theorem canonicalPathMap_sojournStart (ω : M.canonicalRecordΩ) (k : ℕ) :
    (M.canonicalPathMap ω).sojournStart k = ∑ j ∈ range k, (ω (j + 1)).1 := by
  cases k with
  | zero => simp [CTMCPath.sojournStart]
  | succ k => rfl

theorem canonicalPathMap_sojournStart_zero (ω : M.canonicalRecordΩ) :
    (M.canonicalPathMap ω).sojournStart 0 = 0 := rfl

theorem canonicalPathMap_sojournStart_succ (ω : M.canonicalRecordΩ) (k : ℕ) :
    (M.canonicalPathMap ω).sojournStart (k + 1) =
      (M.canonicalPathMap ω).sojournStart k + (ω (k + 1)).1 := by
  rw [canonicalPathMap_sojournStart, canonicalPathMap_sojournStart, Finset.sum_range_succ]

theorem canonicalPathMap_times_eq_sojournStart (ω : M.canonicalRecordΩ) (k : ℕ) :
    (M.canonicalPathMap ω).times k = (M.canonicalPathMap ω).sojournStart (k + 1) := rfl

/-- The frozen readout of the canonical path is measurable in clock time. -/
theorem measurable_canonicalPathMap_frozenStateAt_section (ω : M.canonicalRecordΩ) :
    Measurable fun u : ℝ => (M.canonicalPathMap ω).frozenStateAt u :=
  M.measurable_prod_canonicalPathMap_frozenStateAt.comp (measurable_id.prodMk measurable_const)

/-- A function of the frozen readout is integrable on every compact time interval. -/
theorem integrableOn_comp_frozenStateAt (ω : M.canonicalRecordΩ)
    (h : (Fin d → Fin (M.N + 1)) → ℝ) (a b : ℝ) :
    IntegrableOn (fun u : ℝ => h ((M.canonicalPathMap ω).frozenStateAt u)) (Icc a b) volume := by
  have hmeas : Measurable fun u : ℝ => h ((M.canonicalPathMap ω).frozenStateAt u) :=
    (Measurable.of_discrete (f := h)).comp (M.measurable_canonicalPathMap_frozenStateAt_section ω)
  refine IntegrableOn.of_bound measure_Icc_lt_top hmeas.aestronglyMeasurable (∑ x, |h x|) ?_
  filter_upwards with u
  rw [Real.norm_eq_abs]
  exact Finset.single_le_sum (f := fun x => |h x|) (fun x _ => abs_nonneg _) (Finset.mem_univ _)

/-! ### The good record event -/

/-- The almost-sure record event used by the pathwise reading (FIX-KURTZ2 R1, Lemma 2.4's
`Ω_T` together with the model identities): nonnegative holding times; from a non-absorbing state
the next holding time is positive, the next state differs and has positive rate; from an
absorbing state the next record is `(0, same state)`; the chain is absorbed or has a jump time
beyond `T`; record `0` is `(0, x₀)`; every visited state is in the simplex. -/
structure GoodRecords (x₀ : Fin d → Fin (M.N + 1)) (T : ℝ) (ω : M.canonicalRecordΩ) : Prop where
  hold_nonneg : ∀ n, 0 ≤ (ω (n + 1)).1
  hold_pos : ∀ n, ¬ M.toQMatrix.IsAbsorbing (ω n).2 → 0 < (ω (n + 1)).1
  state_ne : ∀ n, ¬ M.toQMatrix.IsAbsorbing (ω n).2 → (ω (n + 1)).2 ≠ (ω n).2
  rate_pos : ∀ n, ¬ M.toQMatrix.IsAbsorbing (ω n).2 →
    0 < M.toQMatrix.rate (ω n).2 (ω (n + 1)).2
  state_eq : ∀ n, M.toQMatrix.IsAbsorbing (ω n).2 → (ω (n + 1)).2 = (ω n).2
  hold_zero : ∀ n, M.toQMatrix.IsAbsorbing (ω n).2 → (ω (n + 1)).1 = 0
  absorb_or_escape : (∃ a, M.toQMatrix.IsAbsorbing (ω a).2) ∨
    (∃ n, T < (M.canonicalPathMap ω).times n)
  record_zero : ω 0 = (0, x₀)
  inSimplex : ∀ n, M.InSimplex (ω n).2

/-- The good record event has probability one. -/
theorem goodRecords_ae (x₀ : Fin d → Fin (M.N + 1)) (hcons : M.ConservativeJumps)
    (hinit : M.InSimplex x₀) {T : ℝ} (hT : 0 < T) :
    ∀ᵐ ω ∂M.canonicalRecordMeasure x₀, M.GoodRecords x₀ T ω := by
  filter_upwards [M.toQMatrix.canonicalRecordMeasure_all_next_holdingTime_nonneg_ae x₀,
    M.toQMatrix.canonicalRecordMeasure_all_next_holdingTime_pos_ae_of_nonabsorbing x₀,
    M.toQMatrix.canonicalRecordMeasure_all_next_state_ne_current_ae_of_nonabsorbing x₀,
    M.toQMatrix.canonicalRecordMeasure_all_next_rate_pos_ae_of_nonabsorbing x₀,
    M.toQMatrix.canonicalRecordMeasure_all_next_state_eq_current_ae_of_absorbing x₀,
    M.toQMatrix.canonicalRecordMeasure_all_next_holdingTime_eq_zero_ae_of_absorbing x₀,
    M.canonical_absorption_or_nonExplosive_ae x₀ hinit hT,
    M.toQMatrix.canonicalRecordMeasure_record_zero_eq_init_ae x₀,
    M.canonicalPathMap_stateSeq_inSimplex_ae_of_conservative x₀ hcons hinit]
    with ω h1 h2 h3 h4 h5 h6 h7 h8 h9
  refine ⟨h1, fun n hn => h2 n (by simpa using hn), fun n hn => by simpa using h3 n (by simpa using hn),
    fun n hn => by simpa using h4 n (by simpa using hn),
    fun n hn => by simpa using h5 n (by simpa using hn), fun n hn => h6 n (by simpa using hn),
    ?_, h8, fun n => by simpa using h9 n⟩
  rcases h7 with ⟨a, ha⟩ | h
  · exact Or.inl ⟨a, by simpa using ha⟩
  · exact Or.inr h

namespace GoodRecords

variable {M} {x₀ : Fin d → Fin (M.N + 1)} {T : ℝ} {ω : M.canonicalRecordΩ}

theorem sojournStart_mono (hg : M.GoodRecords x₀ T ω) :
    Monotone (M.canonicalPathMap ω).sojournStart := by
  refine monotone_nat_of_le_succ fun k => ?_
  rw [M.canonicalPathMap_sojournStart_succ]
  linarith [hg.hold_nonneg k]

theorem sojournStart_nonneg (hg : M.GoodRecords x₀ T ω) (k : ℕ) :
    0 ≤ (M.canonicalPathMap ω).sojournStart k :=
  (M.canonicalPathMap_sojournStart_zero ω) ▸ hg.sojournStart_mono (Nat.zero_le k)

/-- After an absorbing record, every later record is `(0, same state)`. -/
theorem stay_of_absorbing (hg : M.GoodRecords x₀ T ω) {a : ℕ}
    (ha : M.toQMatrix.IsAbsorbing (ω a).2) :
    ∀ m, a ≤ m → (ω m).2 = (ω a).2 ∧ (ω (m + 1)).1 = 0 := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => exact ⟨rfl, hg.hold_zero a ha⟩
  | succ m _ ih =>
    have habs : M.toQMatrix.IsAbsorbing (ω m).2 := ih.1 ▸ ha
    have h1 : (ω (m + 1)).2 = (ω a).2 := (hg.state_eq m habs).trans ih.1
    exact ⟨h1, hg.hold_zero (m + 1) (h1 ▸ ha)⟩

theorem sojournStart_eq_of_absorbing (hg : M.GoodRecords x₀ T ω) {a : ℕ}
    (ha : M.toQMatrix.IsAbsorbing (ω a).2) :
    ∀ m, a ≤ m → (M.canonicalPathMap ω).sojournStart m = (M.canonicalPathMap ω).sojournStart a := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => rfl
  | succ m hm ih =>
    rw [M.canonicalPathMap_sojournStart_succ, (hg.stay_of_absorbing ha m hm).2, add_zero, ih]

/-- **Sojourn description of the frozen readout on `[0, s]`.** For `s ∈ [0, T]` there is a
sojourn index `n` with `τ n ≤ s`, `X s = Y n`, `X = Y k` on `[τ k, τ (k+1))` for `k < n`,
`X = Y n` on `[τ n, s]`, and either `s ≤ min (τ (n+1)) T` or `Y n` is absorbing with
`τ (n+1) = τ n`. -/
theorem exists_sojourn (hg : M.GoodRecords x₀ T ω) {s : ℝ} (hs : s ∈ Icc 0 T) :
    ∃ n : ℕ, (M.canonicalPathMap ω).sojournStart n ≤ s ∧
      (M.canonicalPathMap ω).frozenStateAt s = (ω n).2 ∧
      (∀ k < n, ∀ u ∈ Ico ((M.canonicalPathMap ω).sojournStart k)
        ((M.canonicalPathMap ω).sojournStart (k + 1)),
        (M.canonicalPathMap ω).frozenStateAt u = (ω k).2) ∧
      (∀ u ∈ Icc ((M.canonicalPathMap ω).sojournStart n) s,
        (M.canonicalPathMap ω).frozenStateAt u = (ω n).2) ∧
      (s ≤ min ((M.canonicalPathMap ω).sojournStart (n + 1)) T ∨
        (M.toQMatrix.IsAbsorbing (ω n).2 ∧
          (M.canonicalPathMap ω).sojournStart (n + 1) = (M.canonicalPathMap ω).sojournStart n)) := by
  classical
  have hmono : Monotone (M.canonicalPathMap ω).sojournStart := hg.sojournStart_mono
  have hstate : ∀ k, (M.canonicalPathMap ω).stateSeq k = (ω k).2 :=
    fun k => M.canonicalPathMap_stateSeq ω k
  have hIco : ∀ k, ∀ u ∈ Ico ((M.canonicalPathMap ω).sojournStart k)
      ((M.canonicalPathMap ω).sojournStart (k + 1)),
      (M.canonicalPathMap ω).frozenStateAt u = (ω k).2 := by
    intro k u hu
    rw [← hstate]
    exact (M.canonicalPathMap ω).frozenStateAt_eq_stateSeq_of_sojourn hmono k hu.1 hu.2
  by_cases hex : ∃ m, s < (M.canonicalPathMap ω).times m
  · -- a future jump exists: the first one gives the sojourn index
    refine ⟨Nat.find hex, ?_, ?_, fun k _ u hu => hIco k u hu, ?_, Or.inl ?_⟩
    · rcases hfind : Nat.find hex with _ | k
      · exact hs.1
      · have hk : ¬ s < (M.canonicalPathMap ω).times k :=
          Nat.find_min hex (by rw [hfind]; exact Nat.lt_succ_self k)
        exact not_lt.mp hk
    · rw [← hstate]
      exact (M.canonicalPathMap ω).frozenStateAt_eq_stateSeq_of_first_time_gt s _
        (Nat.find_spec hex) fun k hk => Nat.find_min hex (Finset.mem_range.mp hk)
    · intro u hu
      exact hIco _ u ⟨hu.1, lt_of_le_of_lt hu.2 (Nat.find_spec hex)⟩
    · exact le_min (Nat.find_spec hex).le hs.2
  · -- no future jump: the chain is absorbed; take the first absorbing index
    push_neg at hex
    have habs : ∃ a, M.toQMatrix.IsAbsorbing (ω a).2 := by
      rcases hg.absorb_or_escape with h | ⟨m, hm⟩
      · exact h
      · exact absurd (lt_of_lt_of_le hm (hex m)) (not_lt.mpr hs.2)
    have hn_abs : M.toQMatrix.IsAbsorbing (ω (Nat.find habs)).2 := Nat.find_spec habs
    have hlt : ∀ k < Nat.find habs, ¬ M.toQMatrix.IsAbsorbing (ω k).2 :=
      fun k hk => Nat.find_min habs hk
    have hstay := hg.stay_of_absorbing hn_abs
    have hτ := hg.sojournStart_eq_of_absorbing hn_abs
    have hτn : (M.canonicalPathMap ω).sojournStart (Nat.find habs) ≤ s := by
      rcases hn' : Nat.find habs with _ | k
      · exact hs.1
      · exact hex k
    have hno : ∀ u, (M.canonicalPathMap ω).sojournStart (Nat.find habs) ≤ u →
        ∀ m, ¬ u < (M.canonicalPathMap ω).times m := by
      intro u hu m
      change ¬ u < (M.canonicalPathMap ω).sojournStart (m + 1)
      rcases le_or_gt (m + 1) (Nat.find habs) with hmn | hmn
      · exact not_lt.mpr ((hmono hmn).trans hu)
      · rw [hτ (m + 1) hmn.le]
        exact not_lt.mpr hu
    have hstable : (M.canonicalPathMap ω).stateSeq (Nat.find habs) =
        (M.canonicalPathMap ω).stateSeq (Nat.find habs + 1) := by
      rw [hstate, hstate, hg.state_eq _ hn_abs]
    have hmin : ∀ k ∈ Finset.range (Nat.find habs),
        (M.canonicalPathMap ω).stateSeq k ≠ (M.canonicalPathMap ω).stateSeq (k + 1) := by
      intro k hk
      rw [hstate, hstate]
      exact (hg.state_ne k (hlt k (Finset.mem_range.mp hk))).symm
    refine ⟨Nat.find habs, hτn, ?_, fun k _ u hu => hIco k u hu, ?_, Or.inr ⟨hn_abs, ?_⟩⟩
    · rw [← hstate]
      exact (M.canonicalPathMap ω).frozenStateAt_eq_stateSeq_of_first_stable s _ (hno s hτn)
        hstable hmin
    · intro u hu
      rw [← hstate]
      exact (M.canonicalPathMap ω).frozenStateAt_eq_stateSeq_of_first_stable u _ (hno u hu.1)
        hstable hmin
    · rw [M.canonicalPathMap_sojournStart_succ, (hstay _ le_rfl).2, add_zero]

/-- On the good event every frozen state on `[0, T]` is a visited state, hence in the simplex. -/
theorem inSimplex_frozenStateAt (hg : M.GoodRecords x₀ T ω) {s : ℝ} (hs : s ∈ Icc 0 T) :
    M.InSimplex ((M.canonicalPathMap ω).frozenStateAt s) := by
  obtain ⟨n, -, hX, -⟩ := hg.exists_sojourn hs
  rw [hX]
  exact hg.inSimplex n

/-- On the good event the frozen readout at time `0` is the initial state. -/
theorem frozenStateAt_zero (hg : M.GoodRecords x₀ T ω) (hT : 0 ≤ T) :
    (M.canonicalPathMap ω).frozenStateAt 0 = (ω 0).2 := by
  obtain ⟨n, hτn, hX, -⟩ := hg.exists_sojourn (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl, hT⟩)
  rw [hX]
  rcases n with _ | n
  · rfl
  · -- `τ (n+1) ≤ 0` forces the first holding time to vanish, so `x₀` is absorbing
    have hzero : ∑ j ∈ range (n + 1), (ω (j + 1)).1 = 0 := by
      rw [← M.canonicalPathMap_sojournStart]
      exact le_antisymm hτn (hg.sojournStart_nonneg _)
    have h1 : (ω (0 + 1)).1 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun j _ => hg.hold_nonneg j).mp hzero 0
        (Finset.mem_range.mpr (Nat.succ_pos n))
    have habs : M.toQMatrix.IsAbsorbing (ω 0).2 := by
      by_contra h
      exact absurd h1 (ne_of_gt (hg.hold_pos 0 h))
    exact (hg.stay_of_absorbing habs (n + 1) (Nat.zero_le _)).1

end GoodRecords

/-! ### The compensator of the lattice tilt -/

theorem toQMatrix_rate_of_ne {x y : Fin d → Fin (M.N + 1)} (h : y ≠ x) :
    M.toQMatrix.rate x y = M.offDiagRate x y := by
  show M.qMatrixRate x y = M.offDiagRate x y
  simp [qMatrixRate, Ne.symm h]

theorem toQMatrix_rate_nonneg_of_ne {x y : Fin d → Fin (M.N + 1)} (h : y ≠ x) :
    0 ≤ M.toQMatrix.rate x y :=
  M.toQMatrix.rate_nonneg x y (Ne.symm h)

/-- The first moment of the lattice jump distribution in coordinate `i` is `N F_i(x/N)` on the
simplex under boundary compatibility (the generator drift identity in lattice units). -/
theorem sum_rate_mul_coord_sub (hBC : M.BoundaryCompatibleOnSimplex)
    {x : Fin d → Fin (M.N + 1)} (hx : M.InSimplex x) (i : Fin d) :
    ∑ y ∈ univ.filter (· ≠ x), M.toQMatrix.rate x y * ((y i : ℝ) - (x i : ℝ)) =
      (M.N : ℝ) * M.rateSpec.drift (M.scaledState x) i := by
  have hN : (M.N : ℝ) ≠ 0 := by exact_mod_cast M.hN.ne'
  have h1 : ∑ y ∈ univ.filter (· ≠ x), M.toQMatrix.rate x y * ((y i : ℝ) - (x i : ℝ)) =
      ∑ y, M.offDiagRate x y * ((y i : ℝ) - (x i : ℝ)) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun y _ => ?_
    by_cases hyx : y ≠ x
    · rw [if_pos hyx, M.toQMatrix_rate_of_ne hyx]
    · push_neg at hyx
      subst hyx
      simp [offDiagRate]
  have h2 : M.generatorDrift x i = ∑ y, M.offDiagRate x y * (((y i : ℝ) - (x i : ℝ)) / M.N) := by
    simp only [generatorDrift, Pi.sub_apply, scaledState, sub_div]
  rw [h1, ← M.generatorDrift_eq_rateSpec_drift_of_boundaryCompatibleOnSimplex hBC hx, h2,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  field_simp

/-- The nonlinear part `κ` of the lattice-tilt compensator: `Σ_{y≠x} q(x,y) p(θ (y_i − x_i))`
with `p(r) = e^r − 1 − r`. -/
noncomputable def latticeKappa (x : Fin d → Fin (M.N + 1)) (i : Fin d) (θ : ℝ) : ℝ :=
  ∑ y ∈ univ.filter (· ≠ x), M.toQMatrix.rate x y *
    (Real.exp (θ * ((y i : ℝ) - (x i : ℝ))) - 1 - θ * ((y i : ℝ) - (x i : ℝ)))

/-- The real compensator rate `c(x) = Σ_{y≠x} q(x,y)(e^{φ(y)−φ(x)} − 1)` of an observable `φ`
(the same expression as `QMatrix.expCompRateReal` for `Q = M.toQMatrix`). -/
noncomputable def expCompReal (φ : (Fin d → Fin (M.N + 1)) → ℝ) (x : Fin d → Fin (M.N + 1)) :
    ℝ :=
  ∑ y ∈ univ.filter (· ≠ x), M.toQMatrix.rate x y * (Real.exp (φ y - φ x) - 1)

theorem expCompReal_of_absorbing (φ : (Fin d → Fin (M.N + 1)) → ℝ) {x : Fin d → Fin (M.N + 1)}
    (hx : M.toQMatrix.IsAbsorbing x) : M.expCompReal φ x = 0 := by
  unfold expCompReal
  refine Finset.sum_eq_zero fun y hy => ?_
  rw [QMatrix.IsAbsorbing.rate_eq_zero M.toQMatrix hx y (Ne.symm (Finset.mem_filter.mp hy).2),
    zero_mul]

/-- **Compensator split (FIX-KURTZ2 (3.2)).** On the simplex, the compensator of the lattice
tilt `φ(x) = θ x_i` is `θ N F_i(x/N) + κ(x)`. -/
theorem expCompReal_split (hBC : M.BoundaryCompatibleOnSimplex)
    {x : Fin d → Fin (M.N + 1)} (hx : M.InSimplex x) (i : Fin d) (θ : ℝ) :
    M.expCompReal (fun z => θ * (z i : ℝ)) x =
      θ * M.N * M.rateSpec.drift (M.scaledState x) i + M.latticeKappa x i θ := by
  unfold expCompReal latticeKappa
  rw [mul_assoc, ← M.sum_rate_mul_coord_sub hBC hx i, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  have hΔ : θ * (y i : ℝ) - θ * (x i : ℝ) = θ * ((y i : ℝ) - (x i : ℝ)) := by ring
  simp only [hΔ]
  ring

theorem latticeKappa_nonneg (x : Fin d → Fin (M.N + 1)) (i : Fin d) (θ : ℝ) :
    0 ≤ M.latticeKappa x i θ := by
  unfold latticeKappa
  refine Finset.sum_nonneg fun y hy => ?_
  refine mul_nonneg (M.toQMatrix_rate_nonneg_of_ne (Finset.mem_filter.mp hy).2) ?_
  linarith [Real.add_one_le_exp (θ * ((y i : ℝ) - (x i : ℝ)))]

/-- `κ(x) ≤ λ(x) θ² J²` when `|θ| J ≤ 1` and every jump from `x` moves coordinate `i` by at
most `J`. -/
theorem latticeKappa_le (x : Fin d → Fin (M.N + 1)) (i : Fin d) {θ J : ℝ}
    (hJ : ∀ y, 0 < M.offDiagRate x y → |(y i : ℝ) - (x i : ℝ)| ≤ J) (hθ : |θ| * J ≤ 1) :
    M.latticeKappa x i θ ≤ M.exitRateAt x * (θ ^ 2 * J ^ 2) := by
  unfold latticeKappa
  have hexit : M.exitRateAt x = ∑ y ∈ univ.filter (· ≠ x), M.toQMatrix.rate x y := rfl
  rw [hexit, Finset.sum_mul]
  refine Finset.sum_le_sum fun y hy => ?_
  have hyx : y ≠ x := (Finset.mem_filter.mp hy).2
  have hr := M.toQMatrix_rate_nonneg_of_ne hyx
  rcases hr.lt_or_eq with hpos | hzero
  · have hΔ := hJ y (M.offDiagRate_pos_of_toQMatrix_rate_pos hpos)
    have hJ0 : 0 ≤ J := (abs_nonneg _).trans hΔ
    have habs : |θ * ((y i : ℝ) - (x i : ℝ))| ≤ 1 := by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left hΔ (abs_nonneg θ)).trans hθ
    have h1 := Real.abs_exp_sub_one_sub_id_le habs
    have h2 : (θ * ((y i : ℝ) - (x i : ℝ))) ^ 2 ≤ θ ^ 2 * J ^ 2 := by
      rw [mul_pow]
      refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg θ)
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hΔ 2
    exact mul_le_mul_of_nonneg_left ((le_abs_self _).trans (h1.trans h2)) hr
  · rw [← hzero, zero_mul, zero_mul]

/-! ### Uniform constants for the canonical family `DensityDepCTMC.mk N hN Γ` -/

/-- A uniform bound `J ≥ 1` for the coordinate displacement of every realizable jump. -/
theorem _root_.Ripple.Kurtz.RateSpec.exists_coord_jump_bound (Γ : Ripple.Kurtz.RateSpec d) :
    ∃ J ≥ (1 : ℝ), ∀ (N : ℕ) (hN : 0 < N) (x y : Fin d → Fin (N + 1)) (i : Fin d),
      0 < (DensityDepCTMC.mk N hN Γ).offDiagRate x y → |(y i : ℝ) - (x i : ℝ)| ≤ J := by
  refine ⟨max Γ.jumpNormBound 1, le_max_right _ _, ?_⟩
  intro N hN x y i hpos
  obtain ⟨ℓ, hℓ, hdiff⟩ := (DensityDepCTMC.mk N hN Γ).exists_jump_of_offDiagRate_pos hpos
  have hcast : (y i : ℝ) - (x i : ℝ) = (ℓ i : ℝ) := by
    have := congrArg (Int.cast : ℤ → ℝ) (hdiff i)
    push_cast at this
    exact this
  rw [hcast]
  refine le_trans ?_ (le_max_left _ _)
  have := norm_le_pi_norm (fun j => (ℓ j : ℝ)) i
  rw [Real.norm_eq_abs] at this
  exact this.trans (Γ.jump_norm_le_bound hℓ)

/-- A uniform exit-rate bound `λ(x) ≤ N Λ` for the canonical family. -/
theorem _root_.Ripple.Kurtz.RateSpec.exists_exitRate_bound_uniform (Γ : Ripple.Kurtz.RateSpec d) :
    ∃ Λ > (0 : ℝ), ∀ (N : ℕ) (hN : 0 < N) (x : Fin d → Fin (N + 1)),
      (DensityDepCTMC.mk N hN Γ).exitRateAt x ≤ N * Λ := by
  obtain ⟨B, hBpos, hB⟩ := Γ.exists_rate_bound_on_ball 1 zero_lt_one
  refine ⟨(Γ.jumps.card : ℝ) * B + 1, by positivity, ?_⟩
  intro N hN x
  refine ((DensityDepCTMC.mk N hN Γ).exitRateAt_le_rate_sum x).trans ?_
  have hNnn : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  refine mul_le_mul_of_nonneg_left ?_ hNnn
  calc ∑ ℓ ∈ Γ.jumps, Γ.rate ℓ ((DensityDepCTMC.mk N hN Γ).scaledState x)
      ≤ ∑ _ℓ ∈ Γ.jumps, B := by
        refine Finset.sum_le_sum fun ℓ hℓ => ?_
        exact (le_abs_self _).trans
          (hB ℓ hℓ _ ((DensityDepCTMC.mk N hN Γ).scaledState_norm_le x))
    _ = (Γ.jumps.card : ℝ) * B := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (Γ.jumps.card : ℝ) * B + 1 := by linarith

/-! ### The record-index exponential sum and the pathwise identity -/

/-- `A_n(T)`: the exponential sum of the first `n` record steps for the observable `φ` at the
horizon `T`, written with the sojourn starts `τ k`:
`Σ_{k<n} [1{τ_{k+1} ≤ T} (φ(Y_{k+1}) − φ(Y_k)) − (τ_{k+1} ∧ T − τ_k ∧ T) c(Y_k)]`. -/
noncomputable def pathExpSum (φ : (Fin d → Fin (M.N + 1)) → ℝ) (T : ℝ) (n : ℕ)
    (ω : M.canonicalRecordΩ) : ℝ :=
  ∑ k ∈ range n,
    ((if (M.canonicalPathMap ω).sojournStart (k + 1) ≤ T then φ (ω (k + 1)).2 - φ (ω k).2 else 0) -
      (min ((M.canonicalPathMap ω).sojournStart (k + 1)) T -
        min ((M.canonicalPathMap ω).sojournStart k) T) * M.expCompReal φ (ω k).2)

theorem pathExpSum_succ (φ : (Fin d → Fin (M.N + 1)) → ℝ) (T : ℝ) (n : ℕ)
    (ω : M.canonicalRecordΩ) :
    M.pathExpSum φ T (n + 1) ω = M.pathExpSum φ T n ω +
      ((if (M.canonicalPathMap ω).sojournStart (n + 1) ≤ T then φ (ω (n + 1)).2 - φ (ω n).2
          else 0) -
        (min ((M.canonicalPathMap ω).sojournStart (n + 1)) T -
          min ((M.canonicalPathMap ω).sojournStart n) T) * M.expCompReal φ (ω n).2) := by
  unfold pathExpSum
  rw [Finset.sum_range_succ]

/-- With nonnegative holding times, `pathExpSum` is the clamped record-index sum of the
exponential-martingale module (`max u 0`, `max h 0` clamps are identities). -/
theorem pathExpSum_eq_clamped (φ : (Fin d → Fin (M.N + 1)) → ℝ) (T : ℝ) (n : ℕ)
    (ω : M.canonicalRecordΩ) (hnn : ∀ k, 0 ≤ (ω (k + 1)).1) :
    M.pathExpSum φ T n ω = ∑ k ∈ range n,
      ((if max (∑ j ∈ range k, (ω (j + 1)).1) 0 + (ω (k + 1)).1 ≤ T then
          φ (ω (k + 1)).2 - φ (ω k).2 else 0) -
        (min (max (∑ j ∈ range k, (ω (j + 1)).1) 0 + max (ω (k + 1)).1 0) T -
          min (max (∑ j ∈ range k, (ω (j + 1)).1) 0) T) * M.expCompReal φ (ω k).2) := by
  unfold pathExpSum
  refine Finset.sum_congr rfl fun k _ => ?_
  have hτ : 0 ≤ ∑ j ∈ range k, (ω (j + 1)).1 := Finset.sum_nonneg fun j _ => hnn j
  rw [max_eq_left hτ, max_eq_left (hnn k), M.canonicalPathMap_sojournStart_succ,
    M.canonicalPathMap_sojournStart]

namespace GoodRecords

variable {M} {x₀ : Fin d → Fin (M.N + 1)} {T : ℝ} {ω : M.canonicalRecordΩ}

/-- **Pathwise identity (FIX-KURTZ2 Lemma 2.6, (2.10)–(2.11)).** On the good event, for
`s ∈ [0, T]` with sojourn index `n`: `φ(X s) − φ(X 0) − ∫_0^s c(X u) du = A_n(T) − (s − τ_n) c(Y_n)`,
together with the sojourn alternative of `exists_sojourn`. -/
theorem pathwise_identity (hg : M.GoodRecords x₀ T ω) (φ : (Fin d → Fin (M.N + 1)) → ℝ)
    {s : ℝ} (hs : s ∈ Icc 0 T) :
    ∃ n : ℕ, (M.canonicalPathMap ω).sojournStart n ≤ s ∧
      (M.canonicalPathMap ω).frozenStateAt s = (ω n).2 ∧
      (s ≤ min ((M.canonicalPathMap ω).sojournStart (n + 1)) T ∨
        (M.toQMatrix.IsAbsorbing (ω n).2 ∧
          (M.canonicalPathMap ω).sojournStart (n + 1) = (M.canonicalPathMap ω).sojournStart n)) ∧
      φ ((M.canonicalPathMap ω).frozenStateAt s) - φ ((M.canonicalPathMap ω).frozenStateAt 0) -
          ∫ u in Icc 0 s, M.expCompReal φ ((M.canonicalPathMap ω).frozenStateAt u) =
        M.pathExpSum φ T n ω -
          (s - (M.canonicalPathMap ω).sojournStart n) * M.expCompReal φ (ω n).2 := by
  obtain ⟨n, hτn, hX, hk, hn, halt⟩ := hg.exists_sojourn hs
  refine ⟨n, hτn, hX, halt, ?_⟩
  have hmono : Monotone (M.canonicalPathMap ω).sojournStart := hg.sojournStart_mono
  have hstate : ∀ k, (M.canonicalPathMap ω).stateSeq k = (ω k).2 :=
    fun k => M.canonicalPathMap_stateSeq ω k
  have hsplit := (M.canonicalPathMap ω).integral_Icc_frozen_eq_sum_sojourn (M.expCompReal φ) hmono
    (M.integrableOn_comp_frozenStateAt ω (M.expCompReal φ) 0 s) hτn
    (fun k hkn u hu => (hk k hkn u hu).trans (hstate k).symm)
    (fun u hu => (hn u hu).trans (hstate n).symm)
  simp only [hstate] at hsplit
  have hsum : M.pathExpSum φ T n ω = ∑ k ∈ range n,
      ((φ (ω (k + 1)).2 - φ (ω k).2) -
        ((M.canonicalPathMap ω).sojournStart (k + 1) - (M.canonicalPathMap ω).sojournStart k) *
          M.expCompReal φ (ω k).2) := by
    unfold pathExpSum
    refine Finset.sum_congr rfl fun k hk => ?_
    have hkn : k < n := Finset.mem_range.mp hk
    have h1 : (M.canonicalPathMap ω).sojournStart (k + 1) ≤ T :=
      ((hmono hkn).trans hτn).trans hs.2
    have h0 : (M.canonicalPathMap ω).sojournStart k ≤ T := (hmono (Nat.le_succ k)).trans h1
    rw [if_pos h1, min_eq_left h1, min_eq_left h0]
  have htel : ∑ k ∈ range n, (φ (ω (k + 1)).2 - φ (ω k).2) = φ (ω n).2 - φ (ω 0).2 :=
    Finset.sum_range_sub (fun k => φ (ω k).2) n
  rw [hX, hg.frozenStateAt_zero (hs.1.trans hs.2), hsplit, hsum, Finset.sum_sub_distrib, htel]
  ring

/-- **Endpoint bound (FIX-KURTZ2 (3.4)).** On the good event, if every record step changes `φ`
by at most `G`, then for `s ∈ [0, T]` the pathwise exponent is at most
`max (A_n(T)) (A_{n+1}(T) + G)` for the sojourn index `n` of `s`. -/
theorem pathExpSum_bound (hg : M.GoodRecords x₀ T ω) (φ : (Fin d → Fin (M.N + 1)) → ℝ)
    {G : ℝ} (hG : ∀ k, |φ (ω (k + 1)).2 - φ (ω k).2| ≤ G) {s : ℝ} (hs : s ∈ Icc 0 T) :
    ∃ n : ℕ,
      φ ((M.canonicalPathMap ω).frozenStateAt s) - φ ((M.canonicalPathMap ω).frozenStateAt 0) -
          ∫ u in Icc 0 s, M.expCompReal φ ((M.canonicalPathMap ω).frozenStateAt u) ≤
        max (M.pathExpSum φ T n ω) (M.pathExpSum φ T (n + 1) ω + G) := by
  obtain ⟨n, hτn, -, halt, hid⟩ := hg.pathwise_identity φ hs
  refine ⟨n, ?_⟩
  rw [hid, M.pathExpSum_succ]
  have hG0 : 0 ≤ G := (abs_nonneg _).trans (hG 0)
  have hΔ : -G ≤ φ (ω (n + 1)).2 - φ (ω n).2 := (abs_le.mp (hG n)).1
  have hminn : min ((M.canonicalPathMap ω).sojournStart n) T =
      (M.canonicalPathMap ω).sojournStart n :=
    min_eq_left (hτn.trans hs.2)
  rw [hminn]
  set c := M.expCompReal φ (ω n).2 with hc
  set A := M.pathExpSum φ T n ω with hA
  set τn := (M.canonicalPathMap ω).sojournStart n with hτn_def
  rcases halt with hle | ⟨habs, hτ⟩
  · -- `τ n ≤ s ≤ e := min τ(n+1) T`: the exponent is affine in `s`, so bounded by an endpoint
    set e := min ((M.canonicalPathMap ω).sojournStart (n + 1)) T with he
    have hse : s - τn ≤ e - τn := by linarith
    have hs0 : 0 ≤ s - τn := by linarith
    have hind : -G ≤ (if (M.canonicalPathMap ω).sojournStart (n + 1) ≤ T then
        φ (ω (n + 1)).2 - φ (ω n).2 else 0) := by
      split_ifs
      · exact hΔ
      · linarith
    rcases le_or_gt 0 c with hc0 | hc0
    · refine le_max_of_le_left ?_
      nlinarith [mul_nonneg hs0 hc0]
    · refine le_max_of_le_right ?_
      nlinarith [mul_nonneg (sub_nonneg.mpr hse) (neg_nonneg.mpr hc0.le)]
  · -- absorbed at `Y n`: `c = 0` and the exponent equals `A_n(T)`
    have hc0 : c = 0 := M.expCompReal_of_absorbing φ habs
    rw [hc0]
    simp

/-- The step bound for the lattice tilt `φ(x) = θ x_i`: on the good event every record step
changes `φ` by at most `|θ| J`. -/
theorem abs_step_le (hg : M.GoodRecords x₀ T ω) {J : ℝ} (hJ0 : 0 ≤ J)
    (hJ : ∀ x y, 0 < M.offDiagRate x y → ∀ i : Fin d, |(y i : ℝ) - (x i : ℝ)| ≤ J)
    (i : Fin d) (θ : ℝ) (k : ℕ) :
    |θ * ((ω (k + 1)).2 i : ℝ) - θ * ((ω k).2 i : ℝ)| ≤ |θ| * J := by
  rw [← mul_sub, abs_mul]
  by_cases habs : M.toQMatrix.IsAbsorbing (ω k).2
  · rw [hg.state_eq k habs, sub_self, abs_zero, mul_zero]
    exact mul_nonneg (abs_nonneg θ) hJ0
  · have hpos := M.offDiagRate_pos_of_toQMatrix_rate_pos (hg.rate_pos k habs)
    exact mul_le_mul_of_nonneg_left (hJ _ _ hpos i) (abs_nonneg θ)

/-- **Equations (3.3)–(3.4) for the frozen martingale part.** On the good event, under boundary
compatibility, with `J` a coordinate jump bound and `Λ` an exit-rate bound (`λ(x) ≤ N Λ`), for
`|θ| J ≤ 1` and `s ∈ [0, T]`:
`θ N M_i(s) − T N Λ θ² J² ≤ max (A_n(T)) (A_{n+1}(T) + |θ| J)` for the sojourn index `n` of `s`,
where `A_n(T) = pathExpSum (θ ·_i) T n`. -/
theorem frozen_martingale_coord_le_pathExpSum_max (hg : M.GoodRecords x₀ T ω)
    (hBC : M.BoundaryCompatibleOnSimplex) {J Λ : ℝ} (hJ0 : 0 ≤ J)
    (hJ : ∀ x y, 0 < M.offDiagRate x y → ∀ i : Fin d, |(y i : ℝ) - (x i : ℝ)| ≤ J)
    (hΛ : ∀ x, M.exitRateAt x ≤ M.N * Λ) (i : Fin d) {θ : ℝ} (hθ : |θ| * J ≤ 1)
    {s : ℝ} (hs : s ∈ Icc 0 T) :
    ∃ n : ℕ, θ * M.N * M.frozenMartingalePart M.canonicalPathMap s ω i -
        T * M.N * Λ * θ ^ 2 * J ^ 2 ≤
      max (M.pathExpSum (fun x => θ * (x i : ℝ)) T n ω)
        (M.pathExpSum (fun x => θ * (x i : ℝ)) T (n + 1) ω + |θ| * J) := by
  set φ : (Fin d → Fin (M.N + 1)) → ℝ := fun x => θ * (x i : ℝ) with hφ
  obtain ⟨n, hbound⟩ := hg.pathExpSum_bound φ (G := |θ| * J)
    (fun k => hg.abs_step_le hJ0 hJ i θ k) hs
  refine ⟨n, le_trans ?_ hbound⟩
  have hNpos : (0 : ℝ) < M.N := by exact_mod_cast M.hN
  have hN : (M.N : ℝ) ≠ 0 := hNpos.ne'
  have hΛ0 : 0 ≤ Λ :=
    (mul_nonneg_iff_of_pos_left hNpos).mp ((M.exitRateAt_nonneg x₀).trans (hΛ x₀))
  -- the compensator along the path splits into the drift part and `κ`
  have hsplit_pt : ∀ u ∈ Icc (0 : ℝ) s,
      M.expCompReal φ ((M.canonicalPathMap ω).frozenStateAt u) =
        θ * M.N * M.rateSpec.drift (M.frozenDensityProcess M.canonicalPathMap u ω) i +
          M.latticeKappa ((M.canonicalPathMap ω).frozenStateAt u) i θ := by
    intro u hu
    have hu' : u ∈ Icc 0 T := ⟨hu.1, hu.2.trans hs.2⟩
    exact M.expCompReal_split hBC (hg.inSimplex_frozenStateAt hu') i θ
  have hint_drift : IntegrableOn
      (fun u => θ * M.N * M.rateSpec.drift (M.frozenDensityProcess M.canonicalPathMap u ω) i)
      (Icc 0 s) volume :=
    M.integrableOn_comp_frozenStateAt ω
      (fun x => θ * M.N * M.rateSpec.drift (M.scaledState x) i) 0 s
  have hint_kappa : IntegrableOn (fun u => M.latticeKappa ((M.canonicalPathMap ω).frozenStateAt u) i θ)
      (Icc 0 s) volume :=
    M.integrableOn_comp_frozenStateAt ω (fun x => M.latticeKappa x i θ) 0 s
  have hint_eq : ∫ u in Icc 0 s, M.expCompReal φ ((M.canonicalPathMap ω).frozenStateAt u) =
      θ * M.N * (∫ u in Icc 0 s,
          M.rateSpec.drift (M.frozenDensityProcess M.canonicalPathMap u ω) i) +
        ∫ u in Icc 0 s, M.latticeKappa ((M.canonicalPathMap ω).frozenStateAt u) i θ := by
    rw [setIntegral_congr_fun measurableSet_Icc hsplit_pt, integral_add hint_drift hint_kappa,
      integral_const_mul]
  -- the `κ` integral is between `0` and `s N Λ θ² J²`
  have hkappa_le : ∫ u in Icc 0 s, M.latticeKappa ((M.canonicalPathMap ω).frozenStateAt u) i θ ≤
      T * M.N * Λ * θ ^ 2 * J ^ 2 := by
    have hpt : ∀ u ∈ Icc (0 : ℝ) s, M.latticeKappa ((M.canonicalPathMap ω).frozenStateAt u) i θ ≤
        M.N * Λ * (θ ^ 2 * J ^ 2) := by
      intro u _
      refine (M.latticeKappa_le _ i (fun y hy => hJ _ y hy i) hθ).trans ?_
      exact mul_le_mul_of_nonneg_right (hΛ _) (by positivity)
    calc ∫ u in Icc 0 s, M.latticeKappa ((M.canonicalPathMap ω).frozenStateAt u) i θ
        ≤ ∫ _u in Icc 0 s, M.N * Λ * (θ ^ 2 * J ^ 2) :=
          setIntegral_mono_on hint_kappa (integrableOn_const measure_Icc_lt_top.ne)
            measurableSet_Icc hpt
      _ = s * (M.N * Λ * (θ ^ 2 * J ^ 2)) := by
          rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hs.1,
            intervalIntegral.integral_const, smul_eq_mul, sub_zero]
      _ ≤ T * (M.N * Λ * (θ ^ 2 * J ^ 2)) :=
          mul_le_mul_of_nonneg_right hs.2 (by positivity)
      _ = T * M.N * Λ * θ ^ 2 * J ^ 2 := by ring
  -- the martingale part in lattice units
  have hmart : θ * M.N * M.frozenMartingalePart M.canonicalPathMap s ω i =
      φ ((M.canonicalPathMap ω).frozenStateAt s) - φ ((M.canonicalPathMap ω).frozenStateAt 0) -
        θ * M.N * ∫ u in Icc 0 s,
          M.rateSpec.drift (M.frozenDensityProcess M.canonicalPathMap u ω) i := by
    simp only [frozenMartingalePart, frozenInitialCondition, frozenDensityProcess, Pi.sub_apply,
      hφ]
    field_simp
  rw [hint_eq, hmart]
  linarith

end GoodRecords

end DensityDepCTMC

end Ripple.CTMC
