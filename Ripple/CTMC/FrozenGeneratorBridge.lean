/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/

import Ripple.CTMC.FrozenRandomIndexDoob

/-!
# Generator-centered finite-clock bridge

This file contains the dimension-generic deterministic bridge from the
generator-centered frozen martingale to the finite clock skeleton used by the
Doob L2 estimate.  It is independent of any concrete reaction network.
-/

namespace Ripple.CTMC

open Ripple.Kurtz MeasureTheory

private theorem norm_sub_sq_le_four_thirds_add_four'
    {E : Type*} [NormedAddCommGroup E] (x y : E) :
    ‖x - y‖ ^ 2 ≤ (4 / 3 : ℝ) * ‖x‖ ^ 2 + 4 * ‖y‖ ^ 2 := by
  have htri_sq : ‖x - y‖ ^ 2 ≤ (‖x‖ + ‖y‖) ^ 2 :=
    sq_le_sq' (by nlinarith [norm_nonneg (x - y), norm_nonneg x, norm_nonneg y])
      (norm_sub_le x y)
  exact htri_sq.trans (by nlinarith [sq_nonneg (‖x‖ - 3 * ‖y‖)])

private theorem norm_affine_sq_le_max_sq'
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x y : E) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    ‖(1 - θ) • x + θ • y‖ ^ 2 ≤ max (‖x‖ ^ 2) (‖y‖ ^ 2) := by
  let R : ℝ := max ‖x‖ ‖y‖
  have hR_nonneg : 0 ≤ R := (norm_nonneg x).trans (le_max_left _ _)
  have hnorm_le : ‖(1 - θ) • x + θ • y‖ ≤ R := by
    calc ‖(1 - θ) • x + θ • y‖
        ≤ ‖(1 - θ) • x‖ + ‖θ • y‖ := norm_add_le _ _
      _ = (1 - θ) * ‖x‖ + θ * ‖y‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_nonneg (sub_nonneg.mpr hθ1), abs_of_nonneg hθ0]
      _ ≤ (1 - θ) * R + θ * R := by gcongr <;> [exact le_max_left _ _; exact le_max_right _ _]
      _ = R := by ring
  have hsq_le := sq_le_sq' ((neg_nonpos.mpr hR_nonneg).trans (norm_nonneg _)) hnorm_le
  suffices R ^ 2 = max (‖x‖ ^ 2) (‖y‖ ^ 2) by simpa [this] using hsq_le
  by_cases hxy : ‖x‖ ≤ ‖y‖
  · have hsxy := sq_le_sq' ((neg_nonpos.mpr (norm_nonneg y)).trans (norm_nonneg x)) hxy
    simp [R, max_eq_right hxy, max_eq_right hsxy]
  · have hyx : ‖y‖ ≤ ‖x‖ := le_of_not_ge hxy
    have hsyx := sq_le_sq' ((neg_nonpos.mpr (norm_nonneg x)).trans (norm_nonneg y)) hyx
    simp [R, max_eq_left hyx, max_eq_left hsyx]

/-- When the clock hasn't expired at step k (sojournStart k ≤ T), the clock-truncated
skeleton equals the untruncated time-compensated martingale. Generic — no BC needed. -/
private theorem frozenClockSkeletonVec_eq_frozenTimeCompensated
    {d : ℕ} [NeZero d] (M : DensityDepCTMC d) (T : ℝ) (records : M.canonicalRecordΩ)
    (k : ℕ)
    (hstrict_prefix : ∀ n < k,
      (M.canonicalPathMap records).times n < (M.canonicalPathMap records).times (n + 1))
    (hpos : 0 < (M.canonicalPathMap records).times 0)
    (hstart : (M.canonicalPathMap records).sojournStart k ≤ T) :
    M.frozenClockSkeletonVec T k records =
      fun i => M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap records) i k := by
  let path := M.canonicalPathMap records
  ext i
  change M.canonicalFrozenClockTruncatedMartingale T i k records = _
  rw [← M.frozenClockTruncatedMartingale_canonicalPathMap_eq T i k records]
  induction k with
  | zero => simp [DensityDepCTMC.frozenClockTruncatedMartingale,
                   DensityDepCTMC.frozenTimeCompensatedJumpMartingale,
                   DensityDepCTMC.scaledJumpSum]
  | succ k ih =>
      have hend_le_T : path.sojournEnd k ≤ T := by
        simpa [CTMCPath.sojournEnd, CTMCPath.sojournStart] using hstart
      have hstart_le_end : path.sojournStart k ≤ path.sojournEnd k := by
        cases k with
        | zero =>
            simpa [CTMCPath.sojournStart, CTMCPath.sojournEnd] using le_of_lt hpos
        | succ k =>
            simpa [CTMCPath.sojournStart, CTMCPath.sojournEnd]
              using le_of_lt (hstrict_prefix k (by omega))
      have hprev : path.sojournStart k ≤ T := le_trans hstart_le_end hend_le_T
      have ih' := ih (fun n hn => hstrict_prefix n (Nat.lt_trans hn (Nat.lt_succ_self k))) hprev
      have hsoj_le : path.sojournTime k ≤ max 0 (T - path.sojournStart k) := by
        rw [max_eq_right (by linarith)]
        simp only [CTMCPath.sojournTime]; linarith
      have hmin : min (path.sojournTime k) (max 0 (T - path.sojournStart k)) =
          path.sojournTime k := min_eq_left hsoj_le
      calc M.frozenClockTruncatedMartingale path i T (k + 1)
          = M.frozenClockTruncatedMartingale path i T k +
              M.truncatedCenteredCoordIncrement (path.stateSeq k) i
                (max 0 (T - path.sojournStart k))
                (path.sojournTime k, path.stateSeq (k + 1)) := by
              rw [M.frozenClockTruncatedMartingale_succ]
        _ = M.frozenTimeCompensatedJumpMartingale path i k +
              ((M.scaledState (path.stateSeq (k + 1)) -
                  M.scaledState (path.stateSeq k)) i -
                M.generatorDrift (path.stateSeq k) i * path.sojournTime k) := by
              rw [ih']
              congr 1
              simp [DensityDepCTMC.truncatedCenteredCoordIncrement, hsoj_le, hmin]
        _ = M.frozenTimeCompensatedJumpMartingale path i (k + 1) := by
              linarith [M.frozenTimeCompensatedJumpMartingale_succ_sub path i k]

/-- **M* at any time = skeleton(jumpCount) - genDrift · elapsed.**
Analogue of `frozenMartingalePart_apply_eq_frozenTimeCompensated_sub_current`
but for `frozenGeneratorMartingalePart` — no hDrift (BC) hypothesis needed,
since M* already uses generatorDrift. -/
private theorem frozenGeneratorMP_apply_eq_timeCompensated_sub_current
    {d : ℕ} [NeZero d] (M : DensityDepCTMC d)
    (path : CTMCPath (Fin d → Fin (M.N + 1)))
    (hstrict : ∀ n, path.times n < path.times (n + 1))
    (hpos : 0 < path.times 0) {t : ℝ} (ht : 0 ≤ t)
    (hfuture : ∃ n, t < path.times n)
    (i : Fin d) :
    M.frozenGeneratorMartingalePart (fun _ : Unit => path) t Unit.unit i =
      M.frozenTimeCompensatedJumpMartingale path i (path.jumpCount t) -
        M.generatorDrift (path.stateSeq (path.jumpCount t)) i *
          path.currentSojournElapsed t := by
  let j := path.jumpCount t
  have hstate_t :
      path.frozenStateAt t = path.stateSeq j :=
    DensityDepCTMC.frozenStateAt_eq_stateSeq_jumpCount_of_mem_currentSojourn
      path hstrict hfuture
      ⟨path.sojournStart_jumpCount_le_of_exists ht hfuture, le_rfl⟩
  have hstate_zero : path.frozenStateAt 0 = path.stateSeq 0 :=
    path.frozenStateAt_eq_stateSeq_of_first_time_gt 0 0 hpos
      (fun k hk => by simp [Finset.mem_range] at hk)
  have htel := M.scaledState_stateSeq_eq_init_add_scaledJumpSum path j
  have htel_i :
      M.scaledState (path.stateSeq j) i - M.scaledState (path.stateSeq 0) i =
        M.scaledJumpSum path j i := by
    have h := congr_fun htel i
    simp only [Pi.add_apply] at h
    rw [CTMCPath.stateSeq_zero]
    linarith
  let f : (Fin d → Fin (M.N + 1)) → ℝ :=
    fun x => (M.generatorDrift x) i
  have hclock :=
    M.frozen_sum_observable_mul_sojournTime_add_currentSojourn_eq_setIntegral
      path hstrict hpos f ht hfuture
  have hintegral_eq :
      ∫ u in Set.Icc (0 : ℝ) t,
          (M.generatorDrift (path.frozenStateAt u)) i =
        (∑ k ∈ Finset.range j,
          M.generatorDrift (path.stateSeq k) i * path.sojournTime k) +
          M.generatorDrift (path.stateSeq j) i *
            path.currentSojournElapsed t := by
    simp only [f] at hclock
    rw [← hclock]
  simp only [DensityDepCTMC.frozenGeneratorMartingalePart,
    DensityDepCTMC.frozenDensityProcess, DensityDepCTMC.frozenInitialCondition,
    DensityDepCTMC.frozenTimeCompensatedJumpMartingale, Pi.sub_apply]
  rw [hstate_t, hstate_zero, hintegral_eq]
  simp [DensityDepCTMC.scaledState] at htel_i ⊢
  linarith

/-- Convert M* between canonical pathMap and Unit pathMap. -/
private lemma frozenGeneratorMP_canonical_eq
    {d : ℕ} [NeZero d] (M : DensityDepCTMC d)
    (records : M.canonicalRecordΩ) (s : ℝ) (i : Fin d) :
    M.frozenGeneratorMartingalePart M.canonicalPathMap s records i =
    M.frozenGeneratorMartingalePart (fun _ : Unit => M.canonicalPathMap records) s () i := by
  simp only [DensityDepCTMC.frozenGeneratorMartingalePart,
    DensityDepCTMC.frozenDensityProcess, DensityDepCTMC.frozenInitialCondition,
    DensityDepCTMC.scaledState, Pi.sub_apply]

/-- **Per-cell pointwise bound: M*(s) norm² ≤ (4/3)·skeletonSupSq + 4·jumpSqSum.**
Given s in cell k with sojournStart(k+1) ≤ T and globally strictly increasing times. -/
private theorem frozenGeneratorMP_cell_sq_le_bridge
    {d : ℕ} [NeZero d] (M : DensityDepCTMC d) (T : ℝ)
    (records : M.canonicalRecordΩ) {s : ℝ} (hs0 : 0 ≤ s) {k n : ℕ}
    (hstrict : ∀ m,
      (M.canonicalPathMap records).times m < (M.canonicalPathMap records).times (m + 1))
    (hpos : 0 < (M.canonicalPathMap records).times 0)
    (hstart_le : (M.canonicalPathMap records).sojournStart k ≤ s)
    (hs_lt_next : s < (M.canonicalPathMap records).sojournStart (k + 1))
    (hnext_le_T : (M.canonicalPathMap records).sojournStart (k + 1) ≤ T)
    (hk1_le_n : k + 1 ≤ n) :
    ‖M.frozenGeneratorMartingalePart M.canonicalPathMap s records‖ ^ 2 ≤
      (4 / 3 : ℝ) * M.frozenClockSkeletonSupSq T n records +
        4 * M.frozenTruncatedJumpSqSum T n records := by
  let path := M.canonicalPathMap records
  -- Establish θ ∈ [0,1] for the affine decomposition
  have hτ_pos : 0 < path.sojournTime k := by
    simp only [CTMCPath.sojournTime, CTMCPath.sojournEnd]
    cases k with
    | zero => simpa [CTMCPath.sojournStart] using hpos
    | succ k => simpa [CTMCPath.sojournStart] using hstrict k
  have helapsed_nonneg : 0 ≤ s - path.sojournStart k := sub_nonneg.mpr hstart_le
  have helapsed_lt_τ : s - path.sojournStart k < path.sojournTime k := by
    simp only [CTMCPath.sojournTime, CTMCPath.sojournEnd, CTMCPath.sojournStart]
    cases k with
    | zero => simpa [CTMCPath.sojournStart] using hs_lt_next
    | succ k => simpa [CTMCPath.sojournStart] using hs_lt_next
  set θ := (s - path.sojournStart k) / path.sojournTime k with hθ_def
  have hθ0 : 0 ≤ θ := div_nonneg helapsed_nonneg (le_of_lt hτ_pos)
  have hθ1 : θ ≤ 1 := (div_le_one hτ_pos).mpr (le_of_lt helapsed_lt_τ)
  -- The skeleton values using existing identity
  have hstart_le_T : path.sojournStart k ≤ T := le_trans (le_trans hstart_le (le_of_lt hs_lt_next)) hnext_le_T
  have hskel_k := frozenClockSkeletonVec_eq_frozenTimeCompensated M T records k
    (fun m _hm => hstrict m) hpos hstart_le_T
  have hskel_k1 := frozenClockSkeletonVec_eq_frozenTimeCompensated M T records (k + 1)
    (fun m _hm => hstrict m) hpos hnext_le_T
  -- Define the jump vector and the right endpoint
  set jumpVec : Fin d → ℝ := fun i =>
    (M.scaledState (path.stateSeq (k + 1)) - M.scaledState (path.stateSeq k)) i with hjumpVec_def
  set rightEnd : Fin d → ℝ := M.frozenClockSkeletonVec T (k + 1) records - jumpVec
    with hrightEnd_def
  -- M*(s) = (1-θ) • skeleton(k) + θ • rightEnd (vector identity via funext)
  have hfuture : ∃ n, s < path.times n := ⟨k, by
    cases k with
    | zero => simpa [CTMCPath.sojournStart] using hs_lt_next
    | succ k => simpa [CTMCPath.sojournStart] using hs_lt_next⟩
  have htimes_mono : ∀ a b : ℕ, a ≤ b → path.times a ≤ path.times b := by
    intro a b hab
    induction hab with
    | refl => exact le_refl _
    | step _ ih => exact le_trans ih (le_of_lt (hstrict _))
  have hcount : path.jumpCount s = k := by
    rw [CTMCPath.jumpCount_eq_iff]
    left
    constructor
    · cases k with
      | zero => simpa [CTMCPath.sojournStart] using hs_lt_next
      | succ k => simpa [CTMCPath.sojournStart] using hs_lt_next
    · intro j hj
      exact not_lt.mpr (by
        cases k with
        | zero => omega
        | succ k =>
            have : path.times j ≤ path.sojournStart (k + 1) := by
              simpa [CTMCPath.sojournStart] using htimes_mono j k (by omega)
            exact le_trans this hstart_le)
  have haffine : M.frozenGeneratorMartingalePart M.canonicalPathMap s records =
      (1 - θ) • M.frozenClockSkeletonVec T k records + θ • rightEnd := by
    ext i
    have hid := frozenGeneratorMP_apply_eq_timeCompensated_sub_current M path hstrict hpos hs0 hfuture i
    simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
    rw [frozenGeneratorMP_canonical_eq M records s i, hid,
        CTMCPath.currentSojournElapsed_eq, hcount]
    have hskel_k_i : (M.frozenClockSkeletonVec T k records) i =
        M.frozenTimeCompensatedJumpMartingale path i k := congr_fun hskel_k i
    have hskel_k1_i : (M.frozenClockSkeletonVec T (k + 1) records) i =
        M.frozenTimeCompensatedJumpMartingale path i (k + 1) := congr_fun hskel_k1 i
    have hincrement := DensityDepCTMC.frozenTimeCompensatedJumpMartingale_succ_sub M path i k
    have hjumpVec_i : jumpVec i =
        (M.scaledState (path.stateSeq (k + 1)) - M.scaledState (path.stateSeq k)) i := rfl
    have hrightEnd_i : rightEnd i =
        M.frozenTimeCompensatedJumpMartingale path i (k + 1) -
          (M.scaledState (path.stateSeq (k + 1)) - M.scaledState (path.stateSeq k)) i := by
      show (M.frozenClockSkeletonVec T (k + 1) records - jumpVec) i = _
      simp only [Pi.sub_apply, hskel_k1_i, hjumpVec_i]
    rw [hskel_k_i, hrightEnd_i]
    have hτ_ne : path.sojournTime k ≠ 0 := ne_of_gt hτ_pos
    have hθ_eq : θ = (s - path.sojournStart k) / path.sojournTime k := rfl
    have hθτ : θ * path.sojournTime k = s - path.sojournStart k := by
      rw [hθ_eq, div_mul_cancel₀ _ hτ_ne]
    set a := M.frozenTimeCompensatedJumpMartingale path i k
    set b := M.frozenTimeCompensatedJumpMartingale path i (k + 1)
    set c := (M.scaledState (path.stateSeq (k + 1)) - M.scaledState (path.stateSeq k)) i
    set g := M.generatorDrift (path.stateSeq k) i
    set τ := path.sojournTime k with hτ_def'
    set e := s - path.sojournStart k
    have hba : b - a = c - g * τ := hincrement
    have hθe : θ * τ = e := hθτ
    have step1 : b - c = a - g * τ := by linarith
    have step2 : θ * (b - c) = θ * (a - g * τ) := by rw [step1]
    have step3 : θ * g * τ = g * e := by
      have : θ * g * τ = g * (θ * τ) := by ring
      rw [this, hθe]
    nlinarith [step2]
  -- Apply segment bound
  rw [haffine]
  calc ‖(1 - θ) • M.frozenClockSkeletonVec T k records + θ • rightEnd‖ ^ 2
      ≤ max (‖M.frozenClockSkeletonVec T k records‖ ^ 2) (‖rightEnd‖ ^ 2) :=
        norm_affine_sq_le_max_sq' _ _ hθ0 hθ1
    _ ≤ (4 / 3 : ℝ) * M.frozenClockSkeletonSupSq T n records +
          4 * M.frozenTruncatedJumpSqSum T n records := by
        apply max_le
        · -- skeleton(k)² ≤ (4/3)·skeletonSupSq + 4·jumpSqSum
          have hk_in : k ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
          have hle_sup := Finset.le_sup' (s := Finset.range (n + 1))
            (f := fun j => ‖M.frozenClockSkeletonVec T j records‖ ^ 2) hk_in
          simp only [DensityDepCTMC.frozenClockSkeletonSupSq] at hle_sup ⊢
          nlinarith [M.frozenTruncatedJumpSqSum_nonneg T n records,
                     sq_nonneg ‖M.frozenClockSkeletonVec T k records‖]
        · -- ‖rightEnd‖² = ‖skeleton(k+1) - jumpVec‖² ≤ (4/3)·‖S_{k+1}‖² + 4·‖J_k‖²
          have hdefect : ‖rightEnd‖ ^ 2 ≤
              (4 / 3 : ℝ) * ‖M.frozenClockSkeletonVec T (k + 1) records‖ ^ 2 +
                4 * ‖jumpVec‖ ^ 2 := by
            rw [hrightEnd_def]
            exact norm_sub_sq_le_four_thirds_add_four'
              (M.frozenClockSkeletonVec T (k + 1) records) jumpVec
          have hk1_in : k + 1 ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
          have hskel_le := Finset.le_sup' (s := Finset.range (n + 1))
            (f := fun j => ‖M.frozenClockSkeletonVec T j records‖ ^ 2) hk1_in
          have hjump_le : ‖jumpVec‖ ^ 2 ≤ M.frozenTruncatedJumpSqSum T n records := by
            have hjumpVec_eq : jumpVec = M.scaledState (path.stateSeq (k + 1)) -
                M.scaledState (path.stateSeq k) := by ext i; simp [jumpVec]
            rw [hjumpVec_eq]
            have hk_in : k ∈ Finset.range n := Finset.mem_range.mpr (by omega)
            have hstart_le_T' : path.sojournStart k ≤ T :=
              le_trans (le_trans hstart_le (le_of_lt hs_lt_next)) hnext_le_T
            have hclock_rem :
                QMatrix.historyClockRemaining T k (Preorder.frestrictLe k records) =
                  max 0 (T - path.sojournStart k) := by
              unfold path
              simp [QMatrix.historyClockRemaining,
                QMatrix.historySojournStart_frestrictLe,
                DensityDepCTMC.canonicalPathMap]
            have hsoj_le_clock : (records (k + 1)).1 ≤
                QMatrix.historyClockRemaining T k (Preorder.frestrictLe k records) := by
              rw [hclock_rem, max_eq_right (by linarith : (0 : ℝ) ≤ T - path.sojournStart k)]
              rw [← DensityDepCTMC.canonicalClockTail_sojournTime_eq_record M records k]
              unfold CTMCPath.sojournTime CTMCPath.sojournEnd
              show path.times k - path.sojournStart k ≤ T - path.sojournStart k
              linarith [show path.sojournStart (k + 1) = path.times k from by
                cases k <;> simp [CTMCPath.sojournStart]]
            have hmem : (records (k + 1)).1 ∈
                Set.Iic (QMatrix.historyClockRemaining T k (Preorder.frestrictLe k records)) :=
              Set.mem_Iic.mpr hsoj_le_clock
            have hterm_eq :
                M.truncatedJumpSqIncrementFromHistory T k
                  (Preorder.frestrictLe k records) (records (k + 1)) =
                ‖M.scaledState (path.stateSeq (k + 1)) -
                  M.scaledState (path.stateSeq k)‖ ^ 2 := by
              unfold DensityDepCTMC.truncatedJumpSqIncrementFromHistory
              simp only [Set.indicator_of_mem hmem, one_mul]
              have h1 : (records (k + 1)).2 = path.stateSeq (k + 1) :=
                (QMatrix.recordTrajectoryToPath_stateSeq records (k + 1)).symm
              have h2 : QMatrix.currentStateFromHistory k (Preorder.frestrictLe k records) =
                  path.stateSeq k :=
                DensityDepCTMC.canonicalClockTail_currentState_eq_stateSeq M records k
              rw [h1, h2]
            calc ‖M.scaledState (path.stateSeq (k + 1)) -
                    M.scaledState (path.stateSeq k)‖ ^ 2
                = M.truncatedJumpSqIncrementFromHistory T k
                    (Preorder.frestrictLe k records) (records (k + 1)) := hterm_eq.symm
              _ ≤ M.frozenTruncatedJumpSqSum T n records := by
                  unfold DensityDepCTMC.frozenTruncatedJumpSqSum
                  exact Finset.single_le_sum
                    (fun j _hj => DensityDepCTMC.truncatedJumpSqIncrementFromHistory_nonneg M T records j)
                    hk_in
          simp only [DensityDepCTMC.frozenClockSkeletonSupSq] at hskel_le ⊢
          nlinarith

/-- **Last-sojourn bound:** when s is in the last sojourn (sojournStart(k) ≤ s ≤ T < sojournStart(k+1)),
M*(s) is affine between skeleton(k) and skeleton(k+1), so ‖M*(s)‖² ≤ max(‖skel(k)‖², ‖skel(k+1)‖²). -/
private theorem frozenGeneratorMP_last_cell_sq_le_max
    {d : ℕ} [NeZero d] (M : DensityDepCTMC d) (T : ℝ)
    (records : M.canonicalRecordΩ) {s : ℝ} (hs0 : 0 ≤ s) {k : ℕ}
    (hstrict : ∀ m,
      (M.canonicalPathMap records).times m < (M.canonicalPathMap records).times (m + 1))
    (hpos : 0 < (M.canonicalPathMap records).times 0)
    (hstart_le : (M.canonicalPathMap records).sojournStart k ≤ s)
    (hsT : s ≤ T)
    (hT_lt_next : T < (M.canonicalPathMap records).sojournStart (k + 1)) :
    ‖M.frozenGeneratorMartingalePart M.canonicalPathMap s records‖ ^ 2 ≤
      max (‖M.frozenClockSkeletonVec T k records‖ ^ 2)
          (‖M.frozenClockSkeletonVec T (k + 1) records‖ ^ 2) := by
  let path := M.canonicalPathMap records
  have hstart_le_T : path.sojournStart k ≤ T := le_trans hstart_le hsT
  have hs_lt_next : s < path.sojournStart (k + 1) := lt_of_le_of_lt hsT hT_lt_next
  have hfuture_s : ∃ n, s < path.times n := ⟨k, by
    cases k with
    | zero => simpa [CTMCPath.sojournStart] using hs_lt_next
    | succ k => simpa [CTMCPath.sojournStart] using hs_lt_next⟩
  have hcount : path.jumpCount s = k := by
    rw [CTMCPath.jumpCount_eq_iff]; left; constructor
    · cases k with
      | zero => simpa [CTMCPath.sojournStart] using hs_lt_next
      | succ k => simpa [CTMCPath.sojournStart] using hs_lt_next
    · intro j hj
      have htimes_mono : ∀ a b : ℕ, a ≤ b → path.times a ≤ path.times b := by
        intro a b hab; induction hab with
        | refl => exact le_refl _
        | step _ ih => exact le_trans ih (le_of_lt (hstrict _))
      exact not_lt.mpr (by
        cases k with
        | zero => omega
        | succ k =>
            exact le_trans (by simpa [CTMCPath.sojournStart] using htimes_mono j k (by omega)) hstart_le)
  -- M*(s,i) = timeCompensated(k,i) - genDrift(stateSeq(k),i) * elapsed
  have hid := fun i => frozenGeneratorMP_apply_eq_timeCompensated_sub_current M path hstrict hpos hs0 hfuture_s i
  -- skeleton(k) = timeCompensated(k)
  have hskel_k := frozenClockSkeletonVec_eq_frozenTimeCompensated M T records k
    (fun m _hm => hstrict m) hpos hstart_le_T
  -- skeleton(k+1) - skeleton(k) = -genDrift * (T - sojournStart(k))
  have hclock_nonneg : (0 : ℝ) ≤ T - path.sojournStart k := sub_nonneg.mpr hstart_le_T
  have h_soj_gt_clock : ¬ path.sojournTime k ≤ max 0 (T - path.sojournStart k) := by
    rw [max_eq_right hclock_nonneg]; push_neg
    simp only [CTMCPath.sojournTime, CTMCPath.sojournEnd]
    cases k with
    | zero =>
        simpa [CTMCPath.sojournStart] using hT_lt_next
    | succ k =>
        simpa [CTMCPath.sojournStart] using hT_lt_next
  have h_not_le : ¬ path.sojournTime k ≤ T - path.sojournStart k := by
    rwa [max_eq_right hclock_nonneg] at h_soj_gt_clock
  have h_incr : ∀ i, M.frozenClockSkeletonVec T (k + 1) records i -
      M.frozenClockSkeletonVec T k records i =
      -M.generatorDrift (path.stateSeq k) i * (T - path.sojournStart k) := by
    intro i
    show M.canonicalFrozenClockTruncatedMartingale T i (k + 1) records -
        M.canonicalFrozenClockTruncatedMartingale T i k records =
      -M.generatorDrift (path.stateSeq k) i * (T - path.sojournStart k)
    rw [M.canonicalFrozenClockTruncatedMartingale_succ_sub T i k records]
    have h_soj_eq : path.sojournTime k = (records (k + 1)).1 :=
      M.canonicalClockTail_sojournTime_eq_record records k
    have h_clock_eq : QMatrix.historyClockRemaining T k (Preorder.frestrictLe k records) =
        T - path.sojournStart k := by
      simp only [QMatrix.historyClockRemaining,
        QMatrix.historySojournStart_frestrictLe]
      have : (QMatrix.recordTrajectoryToPath records).sojournStart k =
          path.sojournStart k := rfl
      rw [this, max_eq_right hclock_nonneg]
    simp only [DensityDepCTMC.truncatedCenteredCoordIncrementFromHistory,
      M.canonicalClockTail_currentState_eq_stateSeq records k, h_clock_eq]
    show M.truncatedCenteredCoordIncrement (path.stateSeq k) i
        (T - path.sojournStart k) (records (k + 1)) =
      -M.generatorDrift (path.stateSeq k) i * (T - path.sojournStart k)
    rw [DensityDepCTMC.truncatedCenteredCoordIncrement, ← h_soj_eq, if_neg h_not_le]
    simp only [zero_mul, zero_sub, min_eq_right (not_le.mp h_not_le).le]
    ring
  -- Express M*(s) as affine combination of skeleton(k) and skeleton(k+1)
  by_cases hT_eq : T = path.sojournStart k
  · -- Degenerate: s = T = sojournStart(k), M*(s) = skeleton(k)
    have hs_eq : s = path.sojournStart k := le_antisymm (by linarith) hstart_le
    have : M.frozenGeneratorMartingalePart M.canonicalPathMap s records =
        M.frozenClockSkeletonVec T k records := by
      ext i
      rw [frozenGeneratorMP_canonical_eq M records s i, hid i,
        CTMCPath.currentSojournElapsed_eq, hcount, hs_eq, sub_self, mul_zero, sub_zero]
      exact (congr_fun hskel_k i).symm
    rw [this]; exact le_max_left _ _
  · have hT_gt : path.sojournStart k < T := lt_of_le_of_ne hstart_le_T (Ne.symm hT_eq)
    set θ := (s - path.sojournStart k) / (T - path.sojournStart k) with hθ_def
    have hθ0 : 0 ≤ θ := div_nonneg (sub_nonneg.mpr hstart_le) (sub_nonneg.mpr (le_of_lt hT_gt))
    have hθ1 : θ ≤ 1 := (div_le_one (sub_pos.mpr hT_gt)).mpr (sub_le_sub_right hsT _)
    have haffine : M.frozenGeneratorMartingalePart M.canonicalPathMap s records =
        (1 - θ) • M.frozenClockSkeletonVec T k records +
          θ • M.frozenClockSkeletonVec T (k + 1) records := by
      ext i
      simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
      rw [frozenGeneratorMP_canonical_eq M records s i, hid i,
          CTMCPath.currentSojournElapsed_eq, hcount]
      have hskel_k_i := congr_fun hskel_k i
      have h_incr_i := h_incr i
      have hT_ne : T - path.sojournStart k ≠ 0 := ne_of_gt (sub_pos.mpr hT_gt)
      have hθτ : θ * (T - path.sojournStart k) = s - path.sojournStart k := by
        rw [hθ_def, div_mul_cancel₀ _ hT_ne]
      have hpath_eq : M.frozenTimeCompensatedJumpMartingale path i k =
          M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap records) i k := rfl
      have hmul : M.generatorDrift (path.stateSeq k) i * (s - path.sojournStart k) =
          θ * (M.generatorDrift (path.stateSeq k) i * (T - path.sojournStart k)) := by
        rw [← mul_assoc, mul_comm θ, mul_assoc, hθτ]
      linear_combination -hskel_k_i - θ * h_incr_i - hmul
    rw [haffine]
    exact norm_affine_sq_le_max_sq' _ _ hθ0 hθ1

private theorem gammaBridge_times_le_of_prefix
    {S : Type*} (path : CTMCPath S) {a b K : ℕ}
    (hab : a ≤ b) (hbK : b ≤ K)
    (hstrict_prefix : ∀ n < K, path.times n < path.times (n + 1)) :
    path.times a ≤ path.times b := by
  induction hab with
  | refl => exact le_rfl
  | step hab ih =>
      exact le_trans (ih (Nat.le_of_succ_le hbK))
        (le_of_lt (hstrict_prefix _ (Nat.lt_of_succ_le hbK)))

private theorem gammaBridge_jumpCount_eq_of_live_sojourn
    {S : Type*} (path : CTMCPath S) {k : ℕ} {s : ℝ}
    (hstrict_prefix : ∀ n < k, path.times n < path.times (n + 1))
    (hstart : path.sojournStart k ≤ s)
    (hend : s < path.sojournStart (k + 1)) :
    path.jumpCount s = k := by
  classical
  rw [path.jumpCount_eq_iff s k]
  left
  constructor
  · cases k with
    | zero =>
        simpa [CTMCPath.sojournStart] using hend
    | succ k =>
        simpa [CTMCPath.sojournStart] using hend
  · intro j hj
    cases j with
    | zero =>
        have htime0_le : path.times 0 ≤ s := by
          cases k with
          | zero => omega
          | succ k =>
              have hle : path.sojournStart 1 ≤ path.sojournStart (Nat.succ k) := by
                simpa [CTMCPath.sojournStart] using
                  gammaBridge_times_le_of_prefix path
                    (Nat.zero_le k) (Nat.le_succ k) hstrict_prefix
              exact le_trans hle hstart
        exact not_lt.mpr htime0_le
    | succ j =>
        have hle_succ : path.times (j + 1) ≤ path.sojournStart k := by
          cases k with
          | zero => omega
          | succ k =>
              simpa [CTMCPath.sojournStart] using
                gammaBridge_times_le_of_prefix path
                  (by omega : j + 1 ≤ k) (Nat.le_succ k) hstrict_prefix
        exact not_lt.mpr (le_trans hle_succ hstart)

private theorem gammaBridge_sojournStart_nonneg_of_prefix
    {S : Type*} (path : CTMCPath S) (k : ℕ)
    (hpos : 0 < path.times 0)
    (hstrict_prefix : ∀ n < k, path.times n < path.times (n + 1)) :
    0 ≤ path.sojournStart k := by
  cases k with
  | zero =>
      simp [CTMCPath.sojournStart]
  | succ k =>
      have hmono : path.times 0 ≤ path.times k :=
        gammaBridge_times_le_of_prefix path
          (Nat.zero_le k) (Nat.le_succ k) hstrict_prefix
      simpa [CTMCPath.sojournStart] using le_trans (le_of_lt hpos) hmono

private theorem strictCompletionThrough_frozenGeneratorMP_eq_of_lt_succ
    {d : ℕ} [NeZero d] (M : DensityDepCTMC d) (records : M.canonicalRecordΩ)
    (n : ℕ) {s : ℝ} (hs0 : 0 ≤ s)
    (hs_lt : s < (M.canonicalPathMap records).sojournStart (n + 1)) :
    M.frozenGeneratorMartingalePart M.canonicalPathMap s records =
      M.frozenGeneratorMartingalePart
        (fun _ : Unit => DensityDepCTMC.strictCompletionThrough (M.canonicalPathMap records) n)
        s Unit.unit := by
  classical
  let path := M.canonicalPathMap records
  let path' := DensityDepCTMC.strictCompletionThrough path n
  have hstate_eq : ∀ t : ℝ, t ≤ s → path'.frozenStateAt t = path.frozenStateAt t := by
    intro t ht
    exact DensityDepCTMC.strictCompletionThrough_frozenStateAt_eq_of_lt_succ
      path n (lt_of_le_of_lt ht hs_lt)
  have hstate_s : path'.frozenStateAt s = path.frozenStateAt s :=
    hstate_eq s le_rfl
  have hstate_0 : path'.frozenStateAt 0 = path.frozenStateAt 0 :=
    hstate_eq 0 hs0
  ext i
  simp only [DensityDepCTMC.frozenGeneratorMartingalePart,
    DensityDepCTMC.frozenDensityProcess,
    DensityDepCTMC.frozenInitialCondition, Pi.sub_apply]
  have hintegral :
      (∫ t in Set.Icc (0 : ℝ) s,
          M.generatorDrift (path.frozenStateAt t) i) =
        ∫ t in Set.Icc (0 : ℝ) s,
          M.generatorDrift (path'.frozenStateAt t) i := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
    intro t ht
    simpa [hstate_eq t ht.2]
  change
      (↑((path.frozenStateAt s i) : ℕ) : ℝ) / ↑M.N -
            (↑((path.frozenStateAt 0 i) : ℕ) : ℝ) / ↑M.N -
          ∫ t in Set.Icc (0 : ℝ) s,
            M.generatorDrift (path.frozenStateAt t) i =
        (↑((path'.frozenStateAt s i) : ℕ) : ℝ) / ↑M.N -
            (↑((path'.frozenStateAt 0 i) : ℕ) : ℝ) / ↑M.N -
          ∫ t in Set.Icc (0 : ℝ) s,
            M.generatorDrift (path'.frozenStateAt t) i
  rw [hstate_s, hstate_0, hintegral]

private theorem strictCompletionThrough_frozenTimeCompensated_eq
    {d : ℕ} [NeZero d] (M : DensityDepCTMC d)
    (path : CTMCPath (Fin d → Fin (M.N + 1)))
    (i : Fin d) (n : ℕ) :
    M.frozenTimeCompensatedJumpMartingale
        (DensityDepCTMC.strictCompletionThrough path n) i n =
      M.frozenTimeCompensatedJumpMartingale path i n := by
  classical
  simp only [DensityDepCTMC.frozenTimeCompensatedJumpMartingale]
  have hscaled :
      M.scaledJumpSum (DensityDepCTMC.strictCompletionThrough path n) n i =
        M.scaledJumpSum path n i := by
    simp only [DensityDepCTMC.scaledJumpSum]
    refine Finset.sum_congr rfl ?_
    intro k hk
    rw [DensityDepCTMC.strictCompletionThrough_stateSeq_eq,
      DensityDepCTMC.strictCompletionThrough_stateSeq_eq]
  have hsum :
      (∑ k ∈ Finset.range n,
          M.generatorDrift ((DensityDepCTMC.strictCompletionThrough path n).stateSeq k) i *
            (DensityDepCTMC.strictCompletionThrough path n).sojournTime k) =
        ∑ k ∈ Finset.range n,
          M.generatorDrift (path.stateSeq k) i * path.sojournTime k := by
    refine Finset.sum_congr rfl ?_
    intro k hk
    have hk_le : k ≤ n := le_of_lt (Finset.mem_range.mp hk)
    rw [DensityDepCTMC.strictCompletionThrough_stateSeq_eq,
      DensityDepCTMC.strictCompletionThrough_sojournTime_eq_of_le path (n := n) (m := k) hk_le]
  rw [hscaled, hsum]

private theorem strictCompletionThrough_frozenTimeCompensated_eq_succ
    {d : ℕ} [NeZero d] (M : DensityDepCTMC d)
    (path : CTMCPath (Fin d → Fin (M.N + 1)))
    (i : Fin d) (n : ℕ) :
    M.frozenTimeCompensatedJumpMartingale
        (DensityDepCTMC.strictCompletionThrough path n) i (n + 1) =
      M.frozenTimeCompensatedJumpMartingale path i (n + 1) := by
  classical
  let path' := DensityDepCTMC.strictCompletionThrough path n
  have hbase :
      M.frozenTimeCompensatedJumpMartingale path' i n =
        M.frozenTimeCompensatedJumpMartingale path i n := by
    simpa [path'] using
      strictCompletionThrough_frozenTimeCompensated_eq M path i n
  have hinc' := M.frozenTimeCompensatedJumpMartingale_succ_sub path' i n
  have hinc := M.frozenTimeCompensatedJumpMartingale_succ_sub path i n
  have hinc_eq :
      M.frozenTimeCompensatedJumpMartingale path' i (n + 1) -
          M.frozenTimeCompensatedJumpMartingale path' i n =
        M.frozenTimeCompensatedJumpMartingale path i (n + 1) -
          M.frozenTimeCompensatedJumpMartingale path i n := by
    rw [hinc', hinc]
    have hs0 : path'.stateSeq n = path.stateSeq n := by
      simpa [path'] using DensityDepCTMC.strictCompletionThrough_stateSeq_eq path n n
    have hs1 : path'.stateSeq (n + 1) = path.stateSeq (n + 1) := by
      simpa [path'] using DensityDepCTMC.strictCompletionThrough_stateSeq_eq path n (n + 1)
    have ht : path'.sojournTime n = path.sojournTime n := by
      simpa [path'] using
        DensityDepCTMC.strictCompletionThrough_sojournTime_eq_of_le path (n := n) (m := n) le_rfl
    have hj : path'.jumps n = path.jumps n := by
      simpa [CTMCPath.stateSeq] using hs1
    simp [hs0, hj, ht]
  linarith

private theorem frozenClockSkeletonVec_eq_frozenTimeCompensated_weak
    {d : ℕ} [NeZero d] (M : DensityDepCTMC d) (T : ℝ) (records : M.canonicalRecordΩ)
    (k : ℕ)
    (hstrict_prefix : ∀ n, n + 1 < k →
      (M.canonicalPathMap records).times n <
        (M.canonicalPathMap records).times (n + 1))
    (hpos : 0 < (M.canonicalPathMap records).times 0)
    (hstart : (M.canonicalPathMap records).sojournStart k ≤ T) :
    M.frozenClockSkeletonVec T k records =
      fun i => M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap records) i k := by
  classical
  let path := M.canonicalPathMap records
  ext i
  change M.canonicalFrozenClockTruncatedMartingale T i k records = _
  rw [← M.frozenClockTruncatedMartingale_canonicalPathMap_eq T i k records]
  induction k with
  | zero =>
      simp [DensityDepCTMC.frozenClockTruncatedMartingale,
        DensityDepCTMC.frozenTimeCompensatedJumpMartingale,
        DensityDepCTMC.scaledJumpSum]
  | succ k ih =>
      have hend_le_T : path.sojournEnd k ≤ T := by
        simpa [CTMCPath.sojournEnd, CTMCPath.sojournStart] using hstart
      have hstart_le_end : path.sojournStart k ≤ path.sojournEnd k := by
        cases k with
        | zero =>
            simpa [CTMCPath.sojournStart, CTMCPath.sojournEnd] using le_of_lt hpos
        | succ k =>
            simpa [CTMCPath.sojournStart, CTMCPath.sojournEnd]
              using le_of_lt (hstrict_prefix k (by omega))
      have hprev : path.sojournStart k ≤ T := le_trans hstart_le_end hend_le_T
      have ih' := ih (fun n hn => hstrict_prefix n (by omega)) hprev
      have hsoj_le : path.sojournTime k ≤ max 0 (T - path.sojournStart k) := by
        rw [max_eq_right (by linarith)]
        simp only [CTMCPath.sojournTime]
        linarith
      have hmin : min (path.sojournTime k) (max 0 (T - path.sojournStart k)) =
          path.sojournTime k := min_eq_left hsoj_le
      calc M.frozenClockTruncatedMartingale path i T (k + 1)
          = M.frozenClockTruncatedMartingale path i T k +
              M.truncatedCenteredCoordIncrement (path.stateSeq k) i
                (max 0 (T - path.sojournStart k))
                (path.sojournTime k, path.stateSeq (k + 1)) := by
              rw [M.frozenClockTruncatedMartingale_succ]
        _ = M.frozenTimeCompensatedJumpMartingale path i k +
              ((M.scaledState (path.stateSeq (k + 1)) -
                  M.scaledState (path.stateSeq k)) i -
                M.generatorDrift (path.stateSeq k) i * path.sojournTime k) := by
              rw [ih']
              congr 1
              simp [DensityDepCTMC.truncatedCenteredCoordIncrement, hsoj_le, hmin]
        _ = M.frozenTimeCompensatedJumpMartingale path i (k + 1) := by
              linarith [M.frozenTimeCompensatedJumpMartingale_succ_sub path i k]

private theorem frozenGeneratorMP_apply_eq_timeCompensated_sub_current_prefix_cell
    {d : ℕ} [NeZero d] (M : DensityDepCTMC d) (T : ℝ)
    (records : M.canonicalRecordΩ) {s : ℝ} (hs0 : 0 ≤ s) {k : ℕ}
    (hstrict_prefix : ∀ n < k,
      (M.canonicalPathMap records).times n <
        (M.canonicalPathMap records).times (n + 1))
    (hpos : 0 < (M.canonicalPathMap records).times 0)
    (hstart_le : (M.canonicalPathMap records).sojournStart k ≤ s)
    (hs_lt_next : s < (M.canonicalPathMap records).sojournStart (k + 1))
    (i : Fin d) :
    M.frozenGeneratorMartingalePart M.canonicalPathMap s records i =
      M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap records) i k -
        M.generatorDrift ((M.canonicalPathMap records).stateSeq k) i *
          (s - (M.canonicalPathMap records).sojournStart k) := by
  classical
  let path := M.canonicalPathMap records
  let path' := DensityDepCTMC.strictCompletionThrough path k
  have hcomp := DensityDepCTMC.strictCompletionThrough_strict
    path k hpos hstrict_prefix
  have hstart_eq : path'.sojournStart k = path.sojournStart k := by
    simpa [path'] using
      DensityDepCTMC.strictCompletionThrough_sojournStart_eq_of_le path k k le_rfl
  have hnext_eq : path'.sojournStart (k + 1) = path.sojournStart (k + 1) := by
    simpa [path'] using
      DensityDepCTMC.strictCompletionThrough_sojournStart_succ_eq path k
  have hstart_le' : path'.sojournStart k ≤ s := by
    rw [hstart_eq]
    exact hstart_le
  have hs_lt_next' : s < path'.sojournStart (k + 1) := by
    rw [hnext_eq]
    exact hs_lt_next
  have hcount' : path'.jumpCount s = k :=
    gammaBridge_jumpCount_eq_of_live_sojourn path'
      (fun n _hn => hcomp.2 n) hstart_le' hs_lt_next'
  have hfuture' : ∃ n, s < path'.times n := by
    refine ⟨k, ?_⟩
    have hs_time : s < path.times k := by
      simpa [CTMCPath.sojournStart] using hs_lt_next
    have htime_eq : path'.times k = path.times k := by
      simp [path', DensityDepCTMC.strictCompletionThrough]
    simpa [htime_eq] using hs_time
  have htransfer :
      M.frozenGeneratorMartingalePart M.canonicalPathMap s records =
        M.frozenGeneratorMartingalePart (fun _ : Unit => path') s Unit.unit := by
    simpa [path, path'] using
      strictCompletionThrough_frozenGeneratorMP_eq_of_lt_succ M records k hs0 hs_lt_next
  have happly :=
    frozenGeneratorMP_apply_eq_timeCompensated_sub_current
      M path' hcomp.2 hcomp.1 hs0 hfuture' i
  have htimecomp :
      M.frozenTimeCompensatedJumpMartingale path' i k =
        M.frozenTimeCompensatedJumpMartingale path i k := by
    simpa [path'] using strictCompletionThrough_frozenTimeCompensated_eq M path i k
  have hstate_k : path'.stateSeq k = path.stateSeq k := by
    simpa [path'] using DensityDepCTMC.strictCompletionThrough_stateSeq_eq path k k
  calc
    M.frozenGeneratorMartingalePart M.canonicalPathMap s records i
        = M.frozenGeneratorMartingalePart (fun _ : Unit => path') s Unit.unit i := by
            rw [htransfer]
    _ = M.frozenTimeCompensatedJumpMartingale path' i k -
          M.generatorDrift (path'.stateSeq k) i *
            (s - path'.sojournStart k) := by
            simpa [hcount', CTMCPath.currentSojournElapsed] using happly
    _ = M.frozenTimeCompensatedJumpMartingale path i k -
          M.generatorDrift (path.stateSeq k) i *
            (s - path.sojournStart k) := by
            rw [htimecomp, hstate_k, hstart_eq]

private theorem frozenGeneratorMP_cell_sq_le_bridge_prefix_unused
    {d : ℕ} [NeZero d] (M : DensityDepCTMC d) (T : ℝ)
    (records : M.canonicalRecordΩ) {s : ℝ} (hs0 : 0 ≤ s) {k n : ℕ}
    (hstrict_prefix : ∀ m < k,
      (M.canonicalPathMap records).times m < (M.canonicalPathMap records).times (m + 1))
    (hpos : 0 < (M.canonicalPathMap records).times 0)
    (hstart_le : (M.canonicalPathMap records).sojournStart k ≤ s)
    (hs_lt_next : s < (M.canonicalPathMap records).sojournStart (k + 1))
    (hnext_le_T : (M.canonicalPathMap records).sojournStart (k + 1) ≤ T)
    (hk1_le_n : k + 1 ≤ n) :
    ‖M.frozenGeneratorMartingalePart M.canonicalPathMap s records‖ ^ 2 ≤
      (4 / 3 : ℝ) * M.frozenClockSkeletonSupSq T n records +
        4 * M.frozenTruncatedJumpSqSum T n records := by
  let path := M.canonicalPathMap records
  have hτ_pos : 0 < path.sojournTime k := by
    simp only [CTMCPath.sojournTime, CTMCPath.sojournEnd]
    cases k with
    | zero =>
        simpa [CTMCPath.sojournStart] using lt_of_le_of_lt hstart_le hs_lt_next
    | succ k =>
        simpa [CTMCPath.sojournStart] using lt_of_le_of_lt hstart_le hs_lt_next
  have helapsed_nonneg : 0 ≤ s - path.sojournStart k := sub_nonneg.mpr hstart_le
  have helapsed_lt_τ : s - path.sojournStart k < path.sojournTime k := by
    simp only [CTMCPath.sojournTime, CTMCPath.sojournEnd, CTMCPath.sojournStart]
    cases k with
    | zero => simpa [CTMCPath.sojournStart] using hs_lt_next
    | succ k => simpa [CTMCPath.sojournStart] using hs_lt_next
  set θ := (s - path.sojournStart k) / path.sojournTime k with hθ_def
  have hθ0 : 0 ≤ θ := div_nonneg helapsed_nonneg (le_of_lt hτ_pos)
  have hθ1 : θ ≤ 1 := (div_le_one hτ_pos).mpr (le_of_lt helapsed_lt_τ)
  have hstart_le_T : path.sojournStart k ≤ T :=
    le_trans (le_trans hstart_le (le_of_lt hs_lt_next)) hnext_le_T
  have hskel_k := frozenClockSkeletonVec_eq_frozenTimeCompensated_weak M T records k
    (fun m hm => hstrict_prefix m (by omega)) hpos hstart_le_T
  have hskel_k1 := frozenClockSkeletonVec_eq_frozenTimeCompensated_weak M T records (k + 1)
    (fun m hm => hstrict_prefix m (by omega)) hpos hnext_le_T
  set jumpVec : Fin d → ℝ := fun i =>
    (M.scaledState (path.stateSeq (k + 1)) - M.scaledState (path.stateSeq k)) i with hjumpVec_def
  set rightEnd : Fin d → ℝ := M.frozenClockSkeletonVec T (k + 1) records - jumpVec
    with hrightEnd_def
  have haffine : M.frozenGeneratorMartingalePart M.canonicalPathMap s records =
      (1 - θ) • M.frozenClockSkeletonVec T k records + θ • rightEnd := by
    ext i
    have hid := frozenGeneratorMP_apply_eq_timeCompensated_sub_current_prefix_cell
      M T records hs0 hstrict_prefix hpos hstart_le hs_lt_next i
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    rw [hid]
    have hskel_k_i : (M.frozenClockSkeletonVec T k records) i =
        M.frozenTimeCompensatedJumpMartingale path i k := congr_fun hskel_k i
    have hskel_k1_i : (M.frozenClockSkeletonVec T (k + 1) records) i =
        M.frozenTimeCompensatedJumpMartingale path i (k + 1) := congr_fun hskel_k1 i
    have hincrement := DensityDepCTMC.frozenTimeCompensatedJumpMartingale_succ_sub M path i k
    have hjumpVec_i : jumpVec i =
        (M.scaledState (path.stateSeq (k + 1)) - M.scaledState (path.stateSeq k)) i := rfl
    have hrightEnd_i : rightEnd i =
        M.frozenTimeCompensatedJumpMartingale path i (k + 1) -
          (M.scaledState (path.stateSeq (k + 1)) - M.scaledState (path.stateSeq k)) i := by
      show (M.frozenClockSkeletonVec T (k + 1) records - jumpVec) i = _
      simp only [Pi.sub_apply, hskel_k1_i, hjumpVec_i]
    rw [hskel_k_i, hrightEnd_i]
    have hτ_ne : path.sojournTime k ≠ 0 := ne_of_gt hτ_pos
    have hθ_eq : θ = (s - path.sojournStart k) / path.sojournTime k := rfl
    have hθτ : θ * path.sojournTime k = s - path.sojournStart k := by
      rw [hθ_eq, div_mul_cancel₀ _ hτ_ne]
    set a := M.frozenTimeCompensatedJumpMartingale path i k
    set b := M.frozenTimeCompensatedJumpMartingale path i (k + 1)
    set c := (M.scaledState (path.stateSeq (k + 1)) - M.scaledState (path.stateSeq k)) i
    set g := M.generatorDrift (path.stateSeq k) i
    set τ := path.sojournTime k
    set e := s - path.sojournStart k
    have hba : b - a = c - g * τ := hincrement
    have hθe : θ * τ = e := hθτ
    have step1 : b - c = a - g * τ := by linarith
    have step2 : θ * (b - c) = θ * (a - g * τ) := by rw [step1]
    have step3 : θ * g * τ = g * e := by
      have : θ * g * τ = g * (θ * τ) := by ring
      rw [this, hθe]
    nlinarith [step2]
  rw [haffine]
  calc ‖(1 - θ) • M.frozenClockSkeletonVec T k records + θ • rightEnd‖ ^ 2
      ≤ max (‖M.frozenClockSkeletonVec T k records‖ ^ 2) (‖rightEnd‖ ^ 2) :=
        norm_affine_sq_le_max_sq' _ _ hθ0 hθ1
    _ ≤ (4 / 3 : ℝ) * M.frozenClockSkeletonSupSq T n records +
          4 * M.frozenTruncatedJumpSqSum T n records := by
        apply max_le
        · have hk_in : k ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
          have hle_sup := Finset.le_sup' (s := Finset.range (n + 1))
            (f := fun j => ‖M.frozenClockSkeletonVec T j records‖ ^ 2) hk_in
          simp only [DensityDepCTMC.frozenClockSkeletonSupSq] at hle_sup ⊢
          nlinarith [M.frozenTruncatedJumpSqSum_nonneg T n records,
                     sq_nonneg ‖M.frozenClockSkeletonVec T k records‖]
        · have hdefect : ‖rightEnd‖ ^ 2 ≤
              (4 / 3 : ℝ) * ‖M.frozenClockSkeletonVec T (k + 1) records‖ ^ 2 +
                4 * ‖jumpVec‖ ^ 2 := by
            rw [hrightEnd_def]
            exact norm_sub_sq_le_four_thirds_add_four'
              (M.frozenClockSkeletonVec T (k + 1) records) jumpVec
          have hk1_in : k + 1 ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
          have hskel_le := Finset.le_sup' (s := Finset.range (n + 1))
            (f := fun j => ‖M.frozenClockSkeletonVec T j records‖ ^ 2) hk1_in
          have hjump_le : ‖jumpVec‖ ^ 2 ≤ M.frozenTruncatedJumpSqSum T n records := by
            have hjumpVec_eq : jumpVec = M.scaledState (path.stateSeq (k + 1)) -
                M.scaledState (path.stateSeq k) := by ext i; simp [jumpVec]
            rw [hjumpVec_eq]
            have hk_in : k ∈ Finset.range n := Finset.mem_range.mpr (by omega)
            have hclock_rem :
                QMatrix.historyClockRemaining T k (Preorder.frestrictLe k records) =
                  max 0 (T - path.sojournStart k) := by
              unfold path
              simp [QMatrix.historyClockRemaining,
                QMatrix.historySojournStart_frestrictLe,
                DensityDepCTMC.canonicalPathMap]
            have hsoj_le_clock : (records (k + 1)).1 ≤
                QMatrix.historyClockRemaining T k (Preorder.frestrictLe k records) := by
              rw [hclock_rem, max_eq_right (by linarith : (0 : ℝ) ≤ T - path.sojournStart k)]
              rw [← DensityDepCTMC.canonicalClockTail_sojournTime_eq_record M records k]
              unfold CTMCPath.sojournTime CTMCPath.sojournEnd
              show path.times k - path.sojournStart k ≤ T - path.sojournStart k
              linarith [show path.sojournStart (k + 1) = path.times k from by
                cases k <;> simp [CTMCPath.sojournStart]]
            have hmem : (records (k + 1)).1 ∈
                Set.Iic (QMatrix.historyClockRemaining T k (Preorder.frestrictLe k records)) :=
              Set.mem_Iic.mpr hsoj_le_clock
            have hterm_eq :
                M.truncatedJumpSqIncrementFromHistory T k
                  (Preorder.frestrictLe k records) (records (k + 1)) =
                ‖M.scaledState (path.stateSeq (k + 1)) -
                  M.scaledState (path.stateSeq k)‖ ^ 2 := by
              unfold DensityDepCTMC.truncatedJumpSqIncrementFromHistory
              simp only [Set.indicator_of_mem hmem, one_mul]
              have h1 : (records (k + 1)).2 = path.stateSeq (k + 1) :=
                (QMatrix.recordTrajectoryToPath_stateSeq records (k + 1)).symm
              have h2 : QMatrix.currentStateFromHistory k (Preorder.frestrictLe k records) =
                  path.stateSeq k :=
                DensityDepCTMC.canonicalClockTail_currentState_eq_stateSeq M records k
              rw [h1, h2]
            calc ‖M.scaledState (path.stateSeq (k + 1)) -
                    M.scaledState (path.stateSeq k)‖ ^ 2
                = M.truncatedJumpSqIncrementFromHistory T k
                    (Preorder.frestrictLe k records) (records (k + 1)) := hterm_eq.symm
              _ ≤ M.frozenTruncatedJumpSqSum T n records := by
                  unfold DensityDepCTMC.frozenTruncatedJumpSqSum
                  exact Finset.single_le_sum
                    (fun j _hj => DensityDepCTMC.truncatedJumpSqIncrementFromHistory_nonneg M T records j)
                    hk_in
          simp only [DensityDepCTMC.frozenClockSkeletonSupSq] at hskel_le ⊢
          nlinarith

private theorem frozenGeneratorMP_last_cell_sq_le_max_prefix
    {d : ℕ} [NeZero d] (M : DensityDepCTMC d) (T : ℝ)
    (records : M.canonicalRecordΩ) {s : ℝ} (hs0 : 0 ≤ s) {k : ℕ}
    (hstrict_prefix : ∀ m < k,
      (M.canonicalPathMap records).times m < (M.canonicalPathMap records).times (m + 1))
    (hpos : 0 < (M.canonicalPathMap records).times 0)
    (hstart_le : (M.canonicalPathMap records).sojournStart k ≤ s)
    (hsT : s ≤ T)
    (hT_lt_next : T < (M.canonicalPathMap records).sojournStart (k + 1)) :
    ‖M.frozenGeneratorMartingalePart M.canonicalPathMap s records‖ ^ 2 ≤
      max (‖M.frozenClockSkeletonVec T k records‖ ^ 2)
          (‖M.frozenClockSkeletonVec T (k + 1) records‖ ^ 2) := by
  let path := M.canonicalPathMap records
  have hstart_le_T : path.sojournStart k ≤ T := le_trans hstart_le hsT
  have hs_lt_next : s < path.sojournStart (k + 1) := lt_of_le_of_lt hsT hT_lt_next
  have hid := fun i => frozenGeneratorMP_apply_eq_timeCompensated_sub_current_prefix_cell
    M T records hs0 hstrict_prefix hpos hstart_le hs_lt_next i
  have hskel_k := frozenClockSkeletonVec_eq_frozenTimeCompensated_weak M T records k
    (fun m hm => hstrict_prefix m (by omega)) hpos hstart_le_T
  have hclock_nonneg : (0 : ℝ) ≤ T - path.sojournStart k := sub_nonneg.mpr hstart_le_T
  have h_soj_gt_clock : ¬ path.sojournTime k ≤ max 0 (T - path.sojournStart k) := by
    rw [max_eq_right hclock_nonneg]; push_neg
    simp only [CTMCPath.sojournTime, CTMCPath.sojournEnd]
    cases k with
    | zero =>
        simpa [CTMCPath.sojournStart] using hT_lt_next
    | succ k =>
        simpa [CTMCPath.sojournStart] using hT_lt_next
  have h_not_le : ¬ path.sojournTime k ≤ T - path.sojournStart k := by
    rwa [max_eq_right hclock_nonneg] at h_soj_gt_clock
  have h_incr : ∀ i, M.frozenClockSkeletonVec T (k + 1) records i -
      M.frozenClockSkeletonVec T k records i =
      -M.generatorDrift (path.stateSeq k) i * (T - path.sojournStart k) := by
    intro i
    show M.canonicalFrozenClockTruncatedMartingale T i (k + 1) records -
        M.canonicalFrozenClockTruncatedMartingale T i k records =
      -M.generatorDrift (path.stateSeq k) i * (T - path.sojournStart k)
    rw [M.canonicalFrozenClockTruncatedMartingale_succ_sub T i k records]
    have h_soj_eq : path.sojournTime k = (records (k + 1)).1 :=
      M.canonicalClockTail_sojournTime_eq_record records k
    have h_clock_eq : QMatrix.historyClockRemaining T k (Preorder.frestrictLe k records) =
        T - path.sojournStart k := by
      simp only [QMatrix.historyClockRemaining,
        QMatrix.historySojournStart_frestrictLe]
      have : (QMatrix.recordTrajectoryToPath records).sojournStart k =
          path.sojournStart k := rfl
      rw [this, max_eq_right hclock_nonneg]
    simp only [DensityDepCTMC.truncatedCenteredCoordIncrementFromHistory,
      M.canonicalClockTail_currentState_eq_stateSeq records k, h_clock_eq]
    show M.truncatedCenteredCoordIncrement (path.stateSeq k) i
        (T - path.sojournStart k) (records (k + 1)) =
      -M.generatorDrift (path.stateSeq k) i * (T - path.sojournStart k)
    rw [DensityDepCTMC.truncatedCenteredCoordIncrement, ← h_soj_eq, if_neg h_not_le]
    simp only [zero_mul, zero_sub, min_eq_right (not_le.mp h_not_le).le]
    ring
  by_cases hT_eq : T = path.sojournStart k
  · have hs_eq : s = path.sojournStart k := le_antisymm (by linarith) hstart_le
    have : M.frozenGeneratorMartingalePart M.canonicalPathMap s records =
        M.frozenClockSkeletonVec T k records := by
      ext i
      rw [hid i, hs_eq, sub_self, mul_zero, sub_zero]
      exact (congr_fun hskel_k i).symm
    rw [this]; exact le_max_left _ _
  · have hT_gt : path.sojournStart k < T := lt_of_le_of_ne hstart_le_T (Ne.symm hT_eq)
    set θ := (s - path.sojournStart k) / (T - path.sojournStart k) with hθ_def
    have hθ0 : 0 ≤ θ := div_nonneg (sub_nonneg.mpr hstart_le) (sub_nonneg.mpr (le_of_lt hT_gt))
    have hθ1 : θ ≤ 1 := (div_le_one (sub_pos.mpr hT_gt)).mpr (sub_le_sub_right hsT _)
    have haffine : M.frozenGeneratorMartingalePart M.canonicalPathMap s records =
        (1 - θ) • M.frozenClockSkeletonVec T k records +
          θ • M.frozenClockSkeletonVec T (k + 1) records := by
      ext i
      simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
      rw [hid i]
      have hskel_k_i := congr_fun hskel_k i
      have h_incr_i := h_incr i
      have hT_ne : T - path.sojournStart k ≠ 0 := ne_of_gt (sub_pos.mpr hT_gt)
      have hθτ : θ * (T - path.sojournStart k) = s - path.sojournStart k := by
        rw [hθ_def, div_mul_cancel₀ _ hT_ne]
      have hmul : M.generatorDrift (path.stateSeq k) i * (s - path.sojournStart k) =
          θ * (M.generatorDrift (path.stateSeq k) i * (T - path.sojournStart k)) := by
        rw [← mul_assoc, mul_comm θ, mul_assoc, hθτ]
      linear_combination -hskel_k_i - θ * h_incr_i - hmul
    rw [haffine]
    exact norm_affine_sq_le_max_sq' _ _ hθ0 hθ1

private theorem frozenGeneratorMP_last_cell_sq_le_bridge_prefix
    {d : ℕ} [NeZero d] (M : DensityDepCTMC d) (T : ℝ)
    (records : M.canonicalRecordΩ) {s : ℝ} (hs0 : 0 ≤ s) {k n : ℕ}
    (hstrict_prefix : ∀ m < k,
      (M.canonicalPathMap records).times m < (M.canonicalPathMap records).times (m + 1))
    (hpos : 0 < (M.canonicalPathMap records).times 0)
    (hstart_le : (M.canonicalPathMap records).sojournStart k ≤ s)
    (hsT : s ≤ T)
    (hT_lt_next : T < (M.canonicalPathMap records).sojournStart (k + 1))
    (hk1_le_n : k + 1 ≤ n) :
    ‖M.frozenGeneratorMartingalePart M.canonicalPathMap s records‖ ^ 2 ≤
      (4 / 3 : ℝ) * M.frozenClockSkeletonSupSq T n records +
        4 * M.frozenTruncatedJumpSqSum T n records := by
  calc
    ‖M.frozenGeneratorMartingalePart M.canonicalPathMap s records‖ ^ 2
        ≤ max (‖M.frozenClockSkeletonVec T k records‖ ^ 2)
              (‖M.frozenClockSkeletonVec T (k + 1) records‖ ^ 2) := by
            exact frozenGeneratorMP_last_cell_sq_le_max_prefix M T records hs0
              hstrict_prefix hpos hstart_le hsT hT_lt_next
    _ ≤ (4 / 3 : ℝ) * M.frozenClockSkeletonSupSq T n records +
          4 * M.frozenTruncatedJumpSqSum T n records := by
        apply max_le
        · have hk_in : k ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
          have := Finset.le_sup' (s := Finset.range (n + 1))
            (f := fun j => ‖M.frozenClockSkeletonVec T j records‖ ^ 2) hk_in
          simp only [DensityDepCTMC.frozenClockSkeletonSupSq] at this ⊢
          nlinarith [M.frozenTruncatedJumpSqSum_nonneg T n records]
        · have hk1_in : k + 1 ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
          have := Finset.le_sup' (s := Finset.range (n + 1))
            (f := fun j => ‖M.frozenClockSkeletonVec T j records‖ ^ 2) hk1_in
          simp only [DensityDepCTMC.frozenClockSkeletonSupSq] at this ⊢
          nlinarith [M.frozenTruncatedJumpSqSum_nonneg T n records]

private theorem gammaBridge_locate_time_liveCell_or_absorbedTail
    {S : Type*} (path : CTMCPath S) (a : ℕ) {T s : ℝ}
    (hs : 0 ≤ s ∧ s ≤ T) :
    (∃ k, k < a ∧
      path.sojournStart k ≤ s ∧
      s < path.sojournStart (k + 1) ∧
      s ≤ min T (path.sojournStart (k + 1))) ∨
      path.sojournStart a ≤ s := by
  classical
  by_cases htail : path.sojournStart a ≤ s
  · exact Or.inr htail
  · have hslt_a : s < path.sojournStart a := lt_of_not_ge htail
    have hex : ∃ n : ℕ, n ≤ a ∧ s < path.sojournStart n :=
      ⟨a, le_rfl, hslt_a⟩
    let n : ℕ := Nat.find hex
    have hn_le_a : n ≤ a := by
      simpa [n] using (Nat.find_spec hex).1
    have hn_slt : s < path.sojournStart n := by
      simpa [n] using (Nat.find_spec hex).2
    have hn_ne_zero : n ≠ 0 := by
      intro hzero
      have hslt0 : s < 0 := by
        simpa [hzero] using hn_slt
      linarith
    have hn_pos : 0 < n := Nat.pos_of_ne_zero hn_ne_zero
    let k : ℕ := n - 1
    have hk_succ : k + 1 = n := by
      dsimp [k]
      exact Nat.succ_pred_eq_of_pos hn_pos
    have hk_lt_a : k < a := by omega
    have hk_start_le : path.sojournStart k ≤ s := by
      by_contra hnot
      have hk_lt_n : k < n := by omega
      have hk_witness : k ≤ a ∧ s < path.sojournStart k :=
        ⟨le_trans (le_of_lt hk_lt_a) le_rfl, lt_of_not_ge hnot⟩
      have hfind_le : n ≤ k := by
        simpa [n] using Nat.find_min' hex hk_witness
      omega
    have hs_lt_next : s < path.sojournStart (k + 1) := by
      simpa [hk_succ] using hn_slt
    have hs_le_min : s ≤ min T (path.sojournStart (k + 1)) :=
      le_min hs.2 (le_of_lt hs_lt_next)
    exact Or.inl ⟨k, hk_lt_a, hk_start_le, hs_lt_next, hs_le_min⟩

private theorem gammaBridge_clockTail_times_eq_sum_range
    {d : ℕ} [NeZero d] (M : DensityDepCTMC d) (records : M.canonicalRecordΩ) (m : ℕ) :
    (M.canonicalPathMap records).times m =
      ∑ k ∈ Finset.range (m + 1), (records (k + 1)).1 := by
  simpa [DensityDepCTMC.canonicalPathMap] using
    (QMatrix.recordTrajectoryToPath_times
      (S := Fin d → Fin (M.N + 1)) records m)

private theorem gammaBridge_clockTail_sojournStart_eq_sum_range
    {d : ℕ} [NeZero d] (M : DensityDepCTMC d) (records : M.canonicalRecordΩ) (a : ℕ) :
    (M.canonicalPathMap records).sojournStart a =
      ∑ k ∈ Finset.range a, (records (k + 1)).1 := by
  cases a with
  | zero =>
      simp [CTMCPath.sojournStart]
  | succ a =>
      change (M.canonicalPathMap records).times a =
        ∑ k ∈ Finset.range (a + 1), (records (k + 1)).1
      exact gammaBridge_clockTail_times_eq_sum_range M records a

private theorem gammaBridge_sum_range_succ_le_absorb_prefix_sum
    {f : ℕ → ℝ} {a m : ℕ}
    (hnonneg_before : ∀ k, k < a → 0 ≤ f k)
    (hzero_tail : ∀ k, a ≤ k → f k = 0) :
    (∑ k ∈ Finset.range (m + 1), f k) ≤
      ∑ k ∈ Finset.range a, f k := by
  classical
  have hsplit :
      (∑ k ∈ Finset.range (m + 1), f k) =
        ∑ k ∈ (Finset.range (m + 1)).filter (fun k => k < a), f k := by
    symm
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl ?_
    intro k _hk
    by_cases hka : k < a
    · simp [hka]
    · have hak : a ≤ k := le_of_not_gt hka
      simp [hka, hzero_tail k hak]
  rw [hsplit]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (by
      intro k hk
      exact Finset.mem_range.mpr (Finset.mem_filter.mp hk).2)
    (by
      intro k hk _hnot
      exact hnonneg_before k (Finset.mem_range.mp hk))

private theorem gammaBridge_absorbed_from_firstAbsIdx
    {d : ℕ} [NeZero d] (M : DensityDepCTMC d) (records : M.canonicalRecordΩ)
    (a : ℕ)
    (haAbs : M.toQMatrix.IsAbsorbing ((M.canonicalPathMap records).stateSeq a))
    (hstayAbs : ∀ n,
      M.toQMatrix.IsAbsorbing ((M.canonicalPathMap records).stateSeq n) →
        (M.canonicalPathMap records).stateSeq (n + 1) =
          (M.canonicalPathMap records).stateSeq n)
    (hzeroAbs : ∀ n,
      M.toQMatrix.IsAbsorbing ((M.canonicalPathMap records).stateSeq n) →
        (records (n + 1)).1 = 0) :
    (∀ m, a ≤ m → (M.canonicalPathMap records).stateSeq m =
        (M.canonicalPathMap records).stateSeq a) ∧
      (∀ m, a ≤ m → (records (m + 1)).1 = 0) := by
  classical
  let path := M.canonicalPathMap records
  have hstate : ∀ m, a ≤ m → path.stateSeq m = path.stateSeq a := by
    intro m hm
    induction hm with
    | refl => rfl
    | @step m _ ih =>
        have hmAbs : M.toQMatrix.IsAbsorbing (path.stateSeq m) := by
          simpa [ih] using haAbs
        calc
          path.stateSeq (m + 1) = path.stateSeq m := by
            simpa [path] using hstayAbs m hmAbs
          _ = path.stateSeq a := ih
  refine ⟨hstate, ?_⟩
  intro m hm
  have hmAbs : M.toQMatrix.IsAbsorbing (path.stateSeq m) := by
    simpa [hstate m hm] using haAbs
  exact hzeroAbs m hmAbs

private theorem gammaBridge_time_le_firstAbsIdx_sojournStart_from_records
    {d : ℕ} [NeZero d] (M : DensityDepCTMC d) (records : M.canonicalRecordΩ) (a : ℕ)
    (hhold_nonneg_before : ∀ k, k < a → 0 ≤ (records (k + 1)).1)
    (hhold_zero_tail : ∀ k, a ≤ k → (records (k + 1)).1 = 0) :
    ∀ m, (M.canonicalPathMap records).times m ≤
      (M.canonicalPathMap records).sojournStart a := by
  intro m
  let f : ℕ → ℝ := fun k => (records (k + 1)).1
  have hsum_le :
      (∑ k ∈ Finset.range (m + 1), f k) ≤
        ∑ k ∈ Finset.range a, f k :=
    gammaBridge_sum_range_succ_le_absorb_prefix_sum
      (f := f) hhold_nonneg_before hhold_zero_tail
  calc
    (M.canonicalPathMap records).times m
        = ∑ k ∈ Finset.range (m + 1), f k := by
            simpa [f] using gammaBridge_clockTail_times_eq_sum_range M records m
    _ ≤ ∑ k ∈ Finset.range a, f k := hsum_le
    _ = (M.canonicalPathMap records).sojournStart a := by
            simpa [f] using
              (gammaBridge_clockTail_sojournStart_eq_sum_range M records a).symm

private theorem gammaBridge_time_le_firstAbsIdx_sojournStart
    {d : ℕ} [NeZero d] (M : DensityDepCTMC d) (records : M.canonicalRecordΩ) (a : ℕ)
    (hnot_abs_before : ∀ k, k < a →
      ¬ M.toQMatrix.IsAbsorbing ((M.canonicalPathMap records).stateSeq k))
    (hhold_pos : ∀ n,
      ¬ M.toQMatrix.IsAbsorbing
          (QMatrix.currentStateFromHistory
            (S := Fin d → Fin (M.N + 1)) n (Preorder.frestrictLe n records)) →
        0 < (records (n + 1)).1)
    (hhold_zero_tail : ∀ k, a ≤ k →
      (M.canonicalPathMap records).sojournTime k = 0) :
    ∀ m, (M.canonicalPathMap records).times m ≤
      (M.canonicalPathMap records).sojournStart a := by
  refine gammaBridge_time_le_firstAbsIdx_sojournStart_from_records
    M records a ?_ ?_
  · intro k hk
    have hcur_nonabs :
        ¬ M.toQMatrix.IsAbsorbing
          (QMatrix.currentStateFromHistory
            (S := Fin d → Fin (M.N + 1)) k (Preorder.frestrictLe k records)) := by
      rw [DensityDepCTMC.canonicalClockTail_currentState_eq_stateSeq M records k]
      exact hnot_abs_before k hk
    exact le_of_lt (hhold_pos k hcur_nonabs)
  · intro k hk
    have h := hhold_zero_tail k hk
    rwa [DensityDepCTMC.canonicalClockTail_sojournTime_eq_record M records k] at h

private theorem gammaBridge_no_time_gt_of_firstAbsIdx_sojournStart_le
    {d : ℕ} [NeZero d] (M : DensityDepCTMC d) (records : M.canonicalRecordΩ) (a : ℕ)
    (hnot_abs_before : ∀ k, k < a →
      ¬ M.toQMatrix.IsAbsorbing ((M.canonicalPathMap records).stateSeq k))
    (hhold_pos : ∀ n,
      ¬ M.toQMatrix.IsAbsorbing
          (QMatrix.currentStateFromHistory
            (S := Fin d → Fin (M.N + 1)) n (Preorder.frestrictLe n records)) →
        0 < (records (n + 1)).1)
    (hhold_zero_tail : ∀ k, a ≤ k →
      (M.canonicalPathMap records).sojournTime k = 0)
    {t : ℝ} (ht : (M.canonicalPathMap records).sojournStart a ≤ t) :
    ∀ m, ¬ t < (M.canonicalPathMap records).times m := by
  intro m htm
  have hm := gammaBridge_time_le_firstAbsIdx_sojournStart
    M records a hnot_abs_before hhold_pos hhold_zero_tail m
  linarith

private theorem gammaBridge_frozenStateAt_eq_stateSeq_of_firstAbsIdx_tail
    {d : ℕ} [NeZero d] (M : DensityDepCTMC d) (records : M.canonicalRecordΩ) (a : ℕ)
    (hnot_abs_before : ∀ k, k < a →
      ¬ M.toQMatrix.IsAbsorbing ((M.canonicalPathMap records).stateSeq k))
    (hhold_pos : ∀ n,
      ¬ M.toQMatrix.IsAbsorbing
          (QMatrix.currentStateFromHistory
            (S := Fin d → Fin (M.N + 1)) n (Preorder.frestrictLe n records)) →
        0 < (records (n + 1)).1)
    (hstate_tail : ∀ m, a ≤ m →
      (M.canonicalPathMap records).stateSeq m =
        (M.canonicalPathMap records).stateSeq a)
    (hhold_zero_tail : ∀ k, a ≤ k →
      (M.canonicalPathMap records).sojournTime k = 0)
    (hnext_ne : ∀ n,
      ¬ M.toQMatrix.IsAbsorbing
          (QMatrix.currentStateFromHistory
            (S := Fin d → Fin (M.N + 1)) n (Preorder.frestrictLe n records)) →
        (records (n + 1)).2 ≠
          QMatrix.currentStateFromHistory
            (S := Fin d → Fin (M.N + 1)) n (Preorder.frestrictLe n records))
    {t : ℝ} (htail : (M.canonicalPathMap records).sojournStart a ≤ t) :
    (M.canonicalPathMap records).frozenStateAt t =
      (M.canonicalPathMap records).stateSeq a := by
  classical
  let path := M.canonicalPathMap records
  have hno : ∀ m, ¬ t < path.times m := by
    simpa [path] using
      gammaBridge_no_time_gt_of_firstAbsIdx_sojournStart_le
        M records a hnot_abs_before hhold_pos hhold_zero_tail htail
  have hstable : path.stateSeq a = path.stateSeq (a + 1) := by
    simpa [path] using (hstate_tail (a + 1) (Nat.le_succ a)).symm
  have hmin : ∀ k ∈ Finset.range a,
      path.stateSeq k ≠ path.stateSeq (k + 1) := by
    intro k hk hsame
    have hklt : k < a := Finset.mem_range.mp hk
    have hcur :
        QMatrix.currentStateFromHistory
            (S := Fin d → Fin (M.N + 1)) k (Preorder.frestrictLe k records) =
          path.stateSeq k := by
      simpa [path] using DensityDepCTMC.canonicalClockTail_currentState_eq_stateSeq M records k
    have hnonabs_cur :
        ¬ M.toQMatrix.IsAbsorbing
          (QMatrix.currentStateFromHistory
            (S := Fin d → Fin (M.N + 1)) k (Preorder.frestrictLe k records)) := by
      rw [hcur]
      exact hnot_abs_before k hklt
    have hnext_state :
        path.stateSeq (k + 1) = (records (k + 1)).2 := by
      simpa [path, DensityDepCTMC.canonicalPathMap,
        QMatrix.recordTrajectoryToPath_stateSeq]
    have hrecord_eq :
        (records (k + 1)).2 =
          QMatrix.currentStateFromHistory
            (S := Fin d → Fin (M.N + 1)) k (Preorder.frestrictLe k records) := by
      calc
        (records (k + 1)).2 = path.stateSeq (k + 1) := hnext_state.symm
        _ = path.stateSeq k := hsame.symm
        _ = QMatrix.currentStateFromHistory
            (S := Fin d → Fin (M.N + 1)) k
            (Preorder.frestrictLe k records) := hcur.symm
    exact hnext_ne k hnonabs_cur hrecord_eq
  exact path.frozenStateAt_eq_stateSeq_of_first_stable t a hno hstable hmin

private theorem gammaBridge_frozenGeneratorMP_tail_eq_start
    {d : ℕ} [NeZero d] (M : DensityDepCTMC d) (records : M.canonicalRecordΩ) (a : ℕ)
    (hnot_abs_before : ∀ k, k < a →
      ¬ M.toQMatrix.IsAbsorbing ((M.canonicalPathMap records).stateSeq k))
    (hhold_pos : ∀ n,
      ¬ M.toQMatrix.IsAbsorbing
          (QMatrix.currentStateFromHistory
            (S := Fin d → Fin (M.N + 1)) n (Preorder.frestrictLe n records)) →
        0 < (records (n + 1)).1)
    (hstate_tail : ∀ m, a ≤ m →
      (M.canonicalPathMap records).stateSeq m =
        (M.canonicalPathMap records).stateSeq a)
    (hhold_zero_tail : ∀ k, a ≤ k →
      (M.canonicalPathMap records).sojournTime k = 0)
    (hnext_ne : ∀ n,
      ¬ M.toQMatrix.IsAbsorbing
          (QMatrix.currentStateFromHistory
            (S := Fin d → Fin (M.N + 1)) n (Preorder.frestrictLe n records)) →
        (records (n + 1)).2 ≠
          QMatrix.currentStateFromHistory
            (S := Fin d → Fin (M.N + 1)) n (Preorder.frestrictLe n records))
    (hdrift_abs : M.generatorDrift ((M.canonicalPathMap records).stateSeq a) = 0)
    {s : ℝ} (htail : (M.canonicalPathMap records).sojournStart a ≤ s) :
    M.frozenGeneratorMartingalePart M.canonicalPathMap s records =
      M.frozenGeneratorMartingalePart M.canonicalPathMap
        ((M.canonicalPathMap records).sojournStart a) records := by
  classical
  let path := M.canonicalPathMap records
  have hstart_nonneg : 0 ≤ path.sojournStart a := by
    have hsum :
        0 ≤ ∑ k ∈ Finset.range a, (records (k + 1)).1 := by
      refine Finset.sum_nonneg ?_
      intro k hk
      have hklt : k < a := Finset.mem_range.mp hk
      have hcur_nonabs :
          ¬ M.toQMatrix.IsAbsorbing
            (QMatrix.currentStateFromHistory
              (S := Fin d → Fin (M.N + 1)) k (Preorder.frestrictLe k records)) := by
        rw [DensityDepCTMC.canonicalClockTail_currentState_eq_stateSeq M records k]
        exact hnot_abs_before k hklt
      exact le_of_lt (hhold_pos k hcur_nonabs)
    simpa [path] using
      (by
        simpa using
          (gammaBridge_clockTail_sojournStart_eq_sum_range M records a).symm ▸ hsum)
  have hs_nonneg : 0 ≤ s := le_trans hstart_nonneg htail
  have hstate_s :
      path.frozenStateAt s = path.stateSeq a :=
    gammaBridge_frozenStateAt_eq_stateSeq_of_firstAbsIdx_tail
      M records a hnot_abs_before hhold_pos hstate_tail hhold_zero_tail
      hnext_ne htail
  have hstate_start :
      path.frozenStateAt (path.sojournStart a) = path.stateSeq a :=
    gammaBridge_frozenStateAt_eq_stateSeq_of_firstAbsIdx_tail
      M records a hnot_abs_before hhold_pos hstate_tail hhold_zero_tail
      hnext_ne le_rfl
  have hdensity_s :
      M.frozenDensityProcess M.canonicalPathMap s records =
        M.scaledState (path.stateSeq a) := by
    ext i
    simp [DensityDepCTMC.frozenDensityProcess,
      DensityDepCTMC.scaledState, path, hstate_s]
  have hdensity_start :
      M.frozenDensityProcess M.canonicalPathMap (path.sojournStart a) records =
        M.scaledState (path.stateSeq a) := by
    ext i
    simp [DensityDepCTMC.frozenDensityProcess,
      DensityDepCTMC.scaledState, path, hstate_start]
  ext i
  let f : ℝ → ℝ := fun u =>
    M.generatorDrift ((M.canonicalPathMap records).frozenStateAt u) i
  have hsubset :
      Set.Icc (0 : ℝ) (path.sojournStart a) ⊆ Set.Icc (0 : ℝ) s := by
    intro u hu
    exact ⟨hu.1, le_trans hu.2 htail⟩
  have hzero_diff : ∀ u ∈ Set.Icc (0 : ℝ) s \ Set.Icc (0 : ℝ) (path.sojournStart a),
      f u = 0 := by
    intro u hu
    have htail_u : path.sojournStart a ≤ u := by
      have hu0 : 0 ≤ u := hu.1.1
      have hnot_small : ¬ (0 ≤ u ∧ u ≤ path.sojournStart a) := hu.2
      exact le_of_not_gt fun hlt =>
        hnot_small ⟨hu0, le_of_lt hlt⟩
    have hstate_u :
        path.frozenStateAt u = path.stateSeq a :=
      gammaBridge_frozenStateAt_eq_stateSeq_of_firstAbsIdx_tail
        M records a hnot_abs_before hhold_pos hstate_tail hhold_zero_tail
        hnext_ne htail_u
    simpa [f, path, hstate_u] using congr_fun hdrift_abs i
  have hintegral :
      (∫ u in Set.Icc (0 : ℝ) s, f u) =
        ∫ u in Set.Icc (0 : ℝ) (path.sojournStart a), f u := by
    exact MeasureTheory.setIntegral_eq_of_subset_of_forall_diff_eq_zero
      measurableSet_Icc hsubset hzero_diff
  simp only [DensityDepCTMC.frozenGeneratorMartingalePart, Pi.sub_apply]
  rw [hdensity_s, hdensity_start]
  change
      M.scaledState (path.stateSeq a) i -
          M.frozenInitialCondition M.canonicalPathMap records i -
        (∫ u in Set.Icc (0 : ℝ) s, f u) =
      M.scaledState (path.stateSeq a) i -
          M.frozenInitialCondition M.canonicalPathMap records i -
        (∫ u in Set.Icc (0 : ℝ) (path.sojournStart a), f u)
  rw [hintegral]

private theorem gammaBridge_frozenGeneratorMP_cell_sq_le_bridge_prefix
    {d : ℕ} [NeZero d] (M : DensityDepCTMC d) (T : ℝ)
    (records : M.canonicalRecordΩ) {s : ℝ} (hs0 : 0 ≤ s) {k n : ℕ}
    (hstrict_prefix : ∀ m < k,
      (M.canonicalPathMap records).times m < (M.canonicalPathMap records).times (m + 1))
    (hpos : 0 < (M.canonicalPathMap records).times 0)
    (hstart_le : (M.canonicalPathMap records).sojournStart k ≤ s)
    (hs_lt_next : s < (M.canonicalPathMap records).sojournStart (k + 1))
    (hnext_le_T : (M.canonicalPathMap records).sojournStart (k + 1) ≤ T)
    (hk1_le_n : k + 1 ≤ n) :
    ‖M.frozenGeneratorMartingalePart M.canonicalPathMap s records‖ ^ 2 ≤
      (4 / 3 : ℝ) * M.frozenClockSkeletonSupSq T n records +
        4 * M.frozenTruncatedJumpSqSum T n records := by
  let path := M.canonicalPathMap records
  have hstart_lt_end : path.sojournStart k < path.sojournStart (k + 1) :=
    lt_of_le_of_lt hstart_le hs_lt_next
  have hτ_pos : 0 < path.sojournTime k := by
    cases k with
    | zero =>
        simpa [CTMCPath.sojournStart, CTMCPath.sojournTime, CTMCPath.sojournEnd]
          using hstart_lt_end
    | succ k =>
        simpa [CTMCPath.sojournStart, CTMCPath.sojournTime, CTMCPath.sojournEnd]
          using hstart_lt_end
  have helapsed_nonneg : 0 ≤ s - path.sojournStart k := sub_nonneg.mpr hstart_le
  have helapsed_lt_τ : s - path.sojournStart k < path.sojournTime k := by
    simp only [CTMCPath.sojournTime, CTMCPath.sojournEnd, CTMCPath.sojournStart]
    cases k with
    | zero => simpa [CTMCPath.sojournStart] using hs_lt_next
    | succ k => simpa [CTMCPath.sojournStart] using hs_lt_next
  set θ := (s - path.sojournStart k) / path.sojournTime k with hθ_def
  have hθ0 : 0 ≤ θ := div_nonneg helapsed_nonneg (le_of_lt hτ_pos)
  have hθ1 : θ ≤ 1 := (div_le_one hτ_pos).mpr (le_of_lt helapsed_lt_τ)
  have hstart_le_T : path.sojournStart k ≤ T :=
    le_trans (le_trans hstart_le (le_of_lt hs_lt_next)) hnext_le_T
  have hskel_k := frozenClockSkeletonVec_eq_frozenTimeCompensated_weak M T records k
    (fun m hm => hstrict_prefix m (by omega)) hpos hstart_le_T
  have hskel_k1 := frozenClockSkeletonVec_eq_frozenTimeCompensated_weak M T records (k + 1)
    (fun m hm => hstrict_prefix m (by omega)) hpos hnext_le_T
  set jumpVec : Fin d → ℝ := fun i =>
    (M.scaledState (path.stateSeq (k + 1)) - M.scaledState (path.stateSeq k)) i with hjumpVec_def
  set rightEnd : Fin d → ℝ := M.frozenClockSkeletonVec T (k + 1) records - jumpVec
    with hrightEnd_def
  have haffine : M.frozenGeneratorMartingalePart M.canonicalPathMap s records =
      (1 - θ) • M.frozenClockSkeletonVec T k records + θ • rightEnd := by
    ext i
    have hid := frozenGeneratorMP_apply_eq_timeCompensated_sub_current_prefix_cell
      M T records hs0 hstrict_prefix hpos hstart_le hs_lt_next i
    simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
    rw [hid]
    have hskel_k_i : (M.frozenClockSkeletonVec T k records) i =
        M.frozenTimeCompensatedJumpMartingale path i k := congr_fun hskel_k i
    have hskel_k1_i : (M.frozenClockSkeletonVec T (k + 1) records) i =
        M.frozenTimeCompensatedJumpMartingale path i (k + 1) := congr_fun hskel_k1 i
    have hincrement := DensityDepCTMC.frozenTimeCompensatedJumpMartingale_succ_sub M path i k
    have hjumpVec_i : jumpVec i =
        (M.scaledState (path.stateSeq (k + 1)) - M.scaledState (path.stateSeq k)) i := rfl
    have hrightEnd_i : rightEnd i =
        M.frozenTimeCompensatedJumpMartingale path i (k + 1) -
          (M.scaledState (path.stateSeq (k + 1)) - M.scaledState (path.stateSeq k)) i := by
      show (M.frozenClockSkeletonVec T (k + 1) records - jumpVec) i = _
      simp only [Pi.sub_apply, hskel_k1_i, hjumpVec_i]
    rw [hskel_k_i, hrightEnd_i]
    have hτ_ne : path.sojournTime k ≠ 0 := ne_of_gt hτ_pos
    have hθ_eq : θ = (s - path.sojournStart k) / path.sojournTime k := rfl
    have hθτ : θ * path.sojournTime k = s - path.sojournStart k := by
      rw [hθ_eq, div_mul_cancel₀ _ hτ_ne]
    set a := M.frozenTimeCompensatedJumpMartingale path i k
    set b := M.frozenTimeCompensatedJumpMartingale path i (k + 1)
    set c := (M.scaledState (path.stateSeq (k + 1)) - M.scaledState (path.stateSeq k)) i
    set g := M.generatorDrift (path.stateSeq k) i
    set τ := path.sojournTime k
    set e := s - path.sojournStart k
    have hba : b - a = c - g * τ := hincrement
    have hθe : θ * τ = e := hθτ
    have step1 : b - c = a - g * τ := by linarith
    have step2 : θ * (b - c) = θ * (a - g * τ) := by rw [step1]
    have step3 : θ * g * τ = g * e := by
      have : θ * g * τ = g * (θ * τ) := by ring
      rw [this, hθe]
    nlinarith [step2]
  rw [haffine]
  calc ‖(1 - θ) • M.frozenClockSkeletonVec T k records + θ • rightEnd‖ ^ 2
      ≤ max (‖M.frozenClockSkeletonVec T k records‖ ^ 2) (‖rightEnd‖ ^ 2) :=
        norm_affine_sq_le_max_sq' _ _ hθ0 hθ1
    _ ≤ (4 / 3 : ℝ) * M.frozenClockSkeletonSupSq T n records +
          4 * M.frozenTruncatedJumpSqSum T n records := by
        apply max_le
        · have hk_in : k ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
          have hle_sup := Finset.le_sup' (s := Finset.range (n + 1))
            (f := fun j => ‖M.frozenClockSkeletonVec T j records‖ ^ 2) hk_in
          simp only [DensityDepCTMC.frozenClockSkeletonSupSq] at hle_sup ⊢
          nlinarith [M.frozenTruncatedJumpSqSum_nonneg T n records,
                     sq_nonneg ‖M.frozenClockSkeletonVec T k records‖]
        · have hdefect : ‖rightEnd‖ ^ 2 ≤
              (4 / 3 : ℝ) * ‖M.frozenClockSkeletonVec T (k + 1) records‖ ^ 2 +
                4 * ‖jumpVec‖ ^ 2 := by
            rw [hrightEnd_def]
            exact norm_sub_sq_le_four_thirds_add_four'
              (M.frozenClockSkeletonVec T (k + 1) records) jumpVec
          have hk1_in : k + 1 ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
          have hskel_le := Finset.le_sup' (s := Finset.range (n + 1))
            (f := fun j => ‖M.frozenClockSkeletonVec T j records‖ ^ 2) hk1_in
          have hjump_le : ‖jumpVec‖ ^ 2 ≤ M.frozenTruncatedJumpSqSum T n records := by
            have hjumpVec_eq : jumpVec = M.scaledState (path.stateSeq (k + 1)) -
                M.scaledState (path.stateSeq k) := by ext i; simp [jumpVec]
            rw [hjumpVec_eq]
            have hk_in : k ∈ Finset.range n := Finset.mem_range.mpr (by omega)
            have hclock_rem :
                QMatrix.historyClockRemaining T k (Preorder.frestrictLe k records) =
                  max 0 (T - path.sojournStart k) := by
              unfold path
              simp [QMatrix.historyClockRemaining,
                QMatrix.historySojournStart_frestrictLe,
                DensityDepCTMC.canonicalPathMap]
            have hsoj_le_clock : (records (k + 1)).1 ≤
                QMatrix.historyClockRemaining T k (Preorder.frestrictLe k records) := by
              rw [hclock_rem, max_eq_right (by linarith : (0 : ℝ) ≤ T - path.sojournStart k)]
              rw [← DensityDepCTMC.canonicalClockTail_sojournTime_eq_record M records k]
              unfold CTMCPath.sojournTime CTMCPath.sojournEnd
              show path.times k - path.sojournStart k ≤ T - path.sojournStart k
              linarith [show path.sojournStart (k + 1) = path.times k from by
                cases k <;> simp [CTMCPath.sojournStart]]
            have hmem : (records (k + 1)).1 ∈
                Set.Iic (QMatrix.historyClockRemaining T k (Preorder.frestrictLe k records)) :=
              Set.mem_Iic.mpr hsoj_le_clock
            have hterm_eq :
                M.truncatedJumpSqIncrementFromHistory T k
                  (Preorder.frestrictLe k records) (records (k + 1)) =
                ‖M.scaledState (path.stateSeq (k + 1)) -
                  M.scaledState (path.stateSeq k)‖ ^ 2 := by
              unfold DensityDepCTMC.truncatedJumpSqIncrementFromHistory
              simp only [Set.indicator_of_mem hmem, one_mul]
              have h1 : (records (k + 1)).2 = path.stateSeq (k + 1) :=
                (QMatrix.recordTrajectoryToPath_stateSeq records (k + 1)).symm
              have h2 : QMatrix.currentStateFromHistory k (Preorder.frestrictLe k records) =
                  path.stateSeq k :=
                DensityDepCTMC.canonicalClockTail_currentState_eq_stateSeq M records k
              rw [h1, h2]
            calc ‖M.scaledState (path.stateSeq (k + 1)) -
                    M.scaledState (path.stateSeq k)‖ ^ 2
                = M.truncatedJumpSqIncrementFromHistory T k
                    (Preorder.frestrictLe k records) (records (k + 1)) := hterm_eq.symm
              _ ≤ M.frozenTruncatedJumpSqSum T n records := by
                  unfold DensityDepCTMC.frozenTruncatedJumpSqSum
                  exact Finset.single_le_sum
                    (fun j _hj => DensityDepCTMC.truncatedJumpSqIncrementFromHistory_nonneg M T records j)
                    hk_in
          simp only [DensityDepCTMC.frozenClockSkeletonSupSq] at hskel_le ⊢
          nlinarith

private theorem gammaBridge_frozenGeneratorMP_last_cell_sq_le_max_prefix
    {d : ℕ} [NeZero d] (M : DensityDepCTMC d) (T : ℝ)
    (records : M.canonicalRecordΩ) {s : ℝ} (hs0 : 0 ≤ s) {k : ℕ}
    (hstrict_prefix : ∀ m < k,
      (M.canonicalPathMap records).times m < (M.canonicalPathMap records).times (m + 1))
    (hpos : 0 < (M.canonicalPathMap records).times 0)
    (hstart_le : (M.canonicalPathMap records).sojournStart k ≤ s)
    (hsT : s ≤ T)
    (hT_lt_next : T < (M.canonicalPathMap records).sojournStart (k + 1)) :
    ‖M.frozenGeneratorMartingalePart M.canonicalPathMap s records‖ ^ 2 ≤
      max (‖M.frozenClockSkeletonVec T k records‖ ^ 2)
          (‖M.frozenClockSkeletonVec T (k + 1) records‖ ^ 2) := by
  let path := M.canonicalPathMap records
  have hstart_le_T : path.sojournStart k ≤ T := le_trans hstart_le hsT
  have hs_lt_next : s < path.sojournStart (k + 1) := lt_of_le_of_lt hsT hT_lt_next
  have hid := fun i => frozenGeneratorMP_apply_eq_timeCompensated_sub_current_prefix_cell
    M T records hs0 hstrict_prefix hpos hstart_le hs_lt_next i
  have hskel_k := frozenClockSkeletonVec_eq_frozenTimeCompensated_weak M T records k
    (fun m hm => hstrict_prefix m (by omega)) hpos hstart_le_T
  have hclock_nonneg : (0 : ℝ) ≤ T - path.sojournStart k := sub_nonneg.mpr hstart_le_T
  have h_soj_gt_clock : ¬ path.sojournTime k ≤ max 0 (T - path.sojournStart k) := by
    rw [max_eq_right hclock_nonneg]; push_neg
    simp only [CTMCPath.sojournTime, CTMCPath.sojournEnd]
    cases k with
    | zero =>
        simpa [CTMCPath.sojournStart] using hT_lt_next
    | succ k =>
        simpa [CTMCPath.sojournStart] using hT_lt_next
  have h_not_le : ¬ path.sojournTime k ≤ T - path.sojournStart k := by
    rwa [max_eq_right hclock_nonneg] at h_soj_gt_clock
  have h_incr : ∀ i, M.frozenClockSkeletonVec T (k + 1) records i -
      M.frozenClockSkeletonVec T k records i =
      -M.generatorDrift (path.stateSeq k) i * (T - path.sojournStart k) := by
    intro i
    show M.canonicalFrozenClockTruncatedMartingale T i (k + 1) records -
        M.canonicalFrozenClockTruncatedMartingale T i k records =
      -M.generatorDrift (path.stateSeq k) i * (T - path.sojournStart k)
    rw [M.canonicalFrozenClockTruncatedMartingale_succ_sub T i k records]
    have h_soj_eq : path.sojournTime k = (records (k + 1)).1 :=
      M.canonicalClockTail_sojournTime_eq_record records k
    have h_clock_eq : QMatrix.historyClockRemaining T k (Preorder.frestrictLe k records) =
        T - path.sojournStart k := by
      simp only [QMatrix.historyClockRemaining,
        QMatrix.historySojournStart_frestrictLe]
      have : (QMatrix.recordTrajectoryToPath records).sojournStart k =
          path.sojournStart k := rfl
      rw [this, max_eq_right hclock_nonneg]
    simp only [DensityDepCTMC.truncatedCenteredCoordIncrementFromHistory,
      M.canonicalClockTail_currentState_eq_stateSeq records k, h_clock_eq]
    show M.truncatedCenteredCoordIncrement (path.stateSeq k) i
        (T - path.sojournStart k) (records (k + 1)) =
      -M.generatorDrift (path.stateSeq k) i * (T - path.sojournStart k)
    rw [DensityDepCTMC.truncatedCenteredCoordIncrement, ← h_soj_eq, if_neg h_not_le]
    simp only [zero_mul, zero_sub, min_eq_right (not_le.mp h_not_le).le]
    ring
  by_cases hT_eq : T = path.sojournStart k
  · have hs_eq : s = path.sojournStart k := le_antisymm (by linarith) hstart_le
    have : M.frozenGeneratorMartingalePart M.canonicalPathMap s records =
        M.frozenClockSkeletonVec T k records := by
      ext i
      rw [hid i, hs_eq, sub_self, mul_zero, sub_zero]
      exact (congr_fun hskel_k i).symm
    rw [this]
    exact le_max_left _ _
  · have hT_gt : path.sojournStart k < T := lt_of_le_of_ne hstart_le_T (Ne.symm hT_eq)
    set θ := (s - path.sojournStart k) / (T - path.sojournStart k) with hθ_def
    have hθ0 : 0 ≤ θ := div_nonneg (sub_nonneg.mpr hstart_le) (sub_nonneg.mpr (le_of_lt hT_gt))
    have hθ1 : θ ≤ 1 := (div_le_one (sub_pos.mpr hT_gt)).mpr (sub_le_sub_right hsT _)
    have haffine : M.frozenGeneratorMartingalePart M.canonicalPathMap s records =
        (1 - θ) • M.frozenClockSkeletonVec T k records +
          θ • M.frozenClockSkeletonVec T (k + 1) records := by
      ext i
      simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
      rw [hid i]
      have hskel_k_i := congr_fun hskel_k i
      have h_incr_i := h_incr i
      have hT_ne : T - path.sojournStart k ≠ 0 := ne_of_gt (sub_pos.mpr hT_gt)
      have hθτ : θ * (T - path.sojournStart k) = s - path.sojournStart k := by
        rw [hθ_def, div_mul_cancel₀ _ hT_ne]
      have hmul : M.generatorDrift (path.stateSeq k) i * (s - path.sojournStart k) =
          θ * (M.generatorDrift (path.stateSeq k) i * (T - path.sojournStart k)) := by
        rw [← mul_assoc, mul_comm θ, mul_assoc, hθτ]
      linear_combination -hskel_k_i - θ * h_incr_i - hmul
    rw [haffine]
    exact norm_affine_sq_le_max_sq' _ _ hθ0 hθ1

private theorem frozenGeneratorMP_at_sojournStart_eq_frozenTimeCompensated
    {d : ℕ} [NeZero d] (M : DensityDepCTMC d)
    (path : CTMCPath (Fin d → Fin (M.N + 1)))
    (hstrict : ∀ n, path.times n < path.times (n + 1))
    (hpos : 0 < path.times 0) (n : ℕ) :
    M.frozenGeneratorMartingalePart (fun _ : Unit => path)
        (path.sojournStart n) Unit.unit =
      fun i => M.frozenTimeCompensatedJumpMartingale path i n := by
  ext i
  have hstart_nonneg : 0 ≤ path.sojournStart n :=
    gammaBridge_sojournStart_nonneg_of_prefix path n hpos
      (fun m _hm => hstrict m)
  have hnext : path.sojournStart n < path.sojournStart (n + 1) := by
    cases n with
    | zero =>
        simpa [CTMCPath.sojournStart] using hpos
    | succ n =>
        simpa [CTMCPath.sojournStart] using hstrict n
  have hfuture : ∃ m, path.sojournStart n < path.times m := by
    cases n with
    | zero =>
        exact ⟨0, by simpa [CTMCPath.sojournStart] using hpos⟩
    | succ n =>
        exact ⟨n + 1, by simpa [CTMCPath.sojournStart] using hstrict n⟩
  have hcount :
      path.jumpCount (path.sojournStart n) = n :=
    gammaBridge_jumpCount_eq_of_live_sojourn path
      (fun m _hm => hstrict m) le_rfl hnext
  have hid :=
    frozenGeneratorMP_apply_eq_timeCompensated_sub_current
      M path hstrict hpos hstart_nonneg hfuture i
  have helapsed :
      path.currentSojournElapsed (path.sojournStart n) = 0 := by
    rw [CTMCPath.currentSojournElapsed_eq, hcount, sub_self]
  calc
    M.frozenGeneratorMartingalePart (fun _ : Unit => path)
        (path.sojournStart n) Unit.unit i
        = M.frozenTimeCompensatedJumpMartingale path i
            (path.jumpCount (path.sojournStart n)) -
          M.generatorDrift (path.stateSeq (path.jumpCount (path.sojournStart n))) i *
            path.currentSojournElapsed (path.sojournStart n) := hid
    _ = M.frozenTimeCompensatedJumpMartingale path i n := by
          rw [hcount, helapsed, mul_zero, sub_zero]

private theorem gammaBridge_firstAbsIdx_start_sq_le_bridge
    {d : ℕ} [NeZero d] (M : DensityDepCTMC d) (T : ℝ)
    (records : M.canonicalRecordΩ) (a : ℕ)
    (haAbs : M.toQMatrix.IsAbsorbing ((M.canonicalPathMap records).stateSeq a))
    (hnot_abs_before : ∀ k, k < a →
      ¬ M.toQMatrix.IsAbsorbing ((M.canonicalPathMap records).stateSeq k))
    (hhold_pos : ∀ n,
      ¬ M.toQMatrix.IsAbsorbing
          (QMatrix.currentStateFromHistory
            (S := Fin d → Fin (M.N + 1)) n (Preorder.frestrictLe n records)) →
        0 < (records (n + 1)).1)
    (hstate_abs : ∀ n,
      M.toQMatrix.IsAbsorbing
          (QMatrix.currentStateFromHistory
            (S := Fin d → Fin (M.N + 1)) n (Preorder.frestrictLe n records)) →
        (records (n + 1)).2 =
          QMatrix.currentStateFromHistory
            (S := Fin d → Fin (M.N + 1)) n (Preorder.frestrictLe n records))
    (hhold_zero_abs : ∀ n,
      M.toQMatrix.IsAbsorbing
          (QMatrix.currentStateFromHistory
            (S := Fin d → Fin (M.N + 1)) n (Preorder.frestrictLe n records)) →
        (records (n + 1)).1 = 0)
    (hnext_ne : ∀ n,
      ¬ M.toQMatrix.IsAbsorbing
          (QMatrix.currentStateFromHistory
            (S := Fin d → Fin (M.N + 1)) n (Preorder.frestrictLe n records)) →
        (records (n + 1)).2 ≠
          QMatrix.currentStateFromHistory
            (S := Fin d → Fin (M.N + 1)) n (Preorder.frestrictLe n records))
    (hstartT : (M.canonicalPathMap records).sojournStart a ≤ T) :
    ‖M.frozenGeneratorMartingalePart M.canonicalPathMap
        ((M.canonicalPathMap records).sojournStart a) records‖ ^ 2 ≤
      (4 / 3 : ℝ) * M.frozenClockSkeletonSupSq T (a + 1) records +
        4 * M.frozenTruncatedJumpSqSum T (a + 1) records := by
  classical
  let path := M.canonicalPathMap records
  have hbound_nonneg :
      0 ≤ (4 / 3 : ℝ) * M.frozenClockSkeletonSupSq T (a + 1) records +
          4 * M.frozenTruncatedJumpSqSum T (a + 1) records := by
    have := M.frozenClockSkeletonSupSq_nonneg T (a + 1) records
    have := M.frozenTruncatedJumpSqSum_nonneg T (a + 1) records
    nlinarith
  by_cases ha0 : a = 0
  · have hstart0 : path.sojournStart a = 0 := by
      simp [path, ha0, CTMCPath.sojournStart]
    have hzero :
        M.frozenGeneratorMartingalePart M.canonicalPathMap
            (path.sojournStart a) records = 0 := by
      rw [hstart0]
      ext i
      simp [DensityDepCTMC.frozenGeneratorMartingalePart,
        DensityDepCTMC.frozenInitialCondition]
    rw [hzero]
    simpa using hbound_nonneg
  · have ha_pos : 0 < a := Nat.pos_of_ne_zero ha0
    let liveLast : ℕ := a - 1
    have ha_eq : a = liveLast + 1 := by
      simpa [liveLast] using (Nat.succ_pred_eq_of_pos ha_pos).symm
    have hlive_lt_a : liveLast < a := by
      omega
    have hcur_live :
        QMatrix.currentStateFromHistory
            (S := Fin d → Fin (M.N + 1)) liveLast
            (Preorder.frestrictLe liveLast records) =
          path.stateSeq liveLast := by
      simpa [path] using
        DensityDepCTMC.canonicalClockTail_currentState_eq_stateSeq
          M records liveLast
    have hlive_soj_pos : 0 < path.sojournTime liveLast := by
      rw [DensityDepCTMC.canonicalClockTail_sojournTime_eq_record
        M records liveLast]
      exact hhold_pos liveLast (by
        rw [hcur_live]
        exact hnot_abs_before liveLast hlive_lt_a)
    obtain ⟨hpos0, hstrict_prefix⟩ :=
      DensityDepCTMC.canonical_positive_sojourn_prefix_strict
        M records hhold_pos hstate_abs hhold_zero_abs hlive_soj_pos
    let path' := DensityDepCTMC.strictCompletionThrough path liveLast
    have hcomp := DensityDepCTMC.strictCompletionThrough_strict
      path liveLast hpos0 hstrict_prefix
    have hstart_eq : path'.sojournStart a = path.sojournStart a := by
      rw [ha_eq]
      simpa [path'] using
        DensityDepCTMC.strictCompletionThrough_sojournStart_succ_eq
          path liveLast
    have hstate_tail_path : ∀ n,
        M.toQMatrix.IsAbsorbing (path.stateSeq n) →
          path.stateSeq (n + 1) = path.stateSeq n := by
      intro n hn
      have hcur :=
        DensityDepCTMC.canonicalClockTail_currentState_eq_stateSeq
          M records n
      have hnext := hstate_abs n (by
        rw [hcur]
        exact hn)
      simpa [path, DensityDepCTMC.canonicalPathMap,
        QMatrix.recordTrajectoryToPath_stateSeq, hcur] using hnext
    have hhold_zero_record : ∀ n,
        M.toQMatrix.IsAbsorbing (path.stateSeq n) →
          (records (n + 1)).1 = 0 := by
      intro n hn
      have hcur :=
        DensityDepCTMC.canonicalClockTail_currentState_eq_stateSeq
          M records n
      exact hhold_zero_abs n (by
        rw [hcur]
        exact hn)
    obtain ⟨hstate_tail, hhold_zero_tail_record⟩ :=
      gammaBridge_absorbed_from_firstAbsIdx
        M records a haAbs hstate_tail_path hhold_zero_record
    have hhold_zero_tail : ∀ k, a ≤ k → path.sojournTime k = 0 := by
      intro k hk
      rw [DensityDepCTMC.canonicalClockTail_sojournTime_eq_record
        M records k]
      exact hhold_zero_tail_record k hk
    have hstart_pos : 0 < path.sojournStart a := by
      have htime0_le : path.times 0 ≤ path.times liveLast :=
        gammaBridge_times_le_of_prefix path
          (Nat.zero_le liveLast) le_rfl hstrict_prefix
      rw [ha_eq]
      simpa [CTMCPath.sojournStart] using
        lt_of_lt_of_le hpos0 htime0_le
    have hstate_path_start :
        path.frozenStateAt (path.sojournStart a) = path.stateSeq a :=
      gammaBridge_frozenStateAt_eq_stateSeq_of_firstAbsIdx_tail
        M records a hnot_abs_before hhold_pos
        hstate_tail hhold_zero_tail hnext_ne (by simp [path])
    have hstate_path'_start :
        path'.frozenStateAt (path.sojournStart a) = path.stateSeq a := by
      have htime_a : path.sojournStart a < path'.times a := by
        rw [ha_eq]
        change path.times liveLast < path'.times (liveLast + 1)
        have hpath'_live : path'.times liveLast = path.times liveLast := by
          simp [path', DensityDepCTMC.strictCompletionThrough]
        rw [← hpath'_live]
        exact hcomp.2 liveLast
      have hmin : ∀ j ∈ Finset.range a,
          ¬ path.sojournStart a < path'.times j := by
        intro j hj hlt
        have hj_le_live : j ≤ liveLast := by
          have hjlt : j < liveLast + 1 := by
            simpa [ha_eq] using Finset.mem_range.mp hj
          omega
        have hpath'_j : path'.times j = path.times j := by
          simp [path', DensityDepCTMC.strictCompletionThrough, hj_le_live]
        have htimes_le : path.times j ≤ path.times liveLast :=
          gammaBridge_times_le_of_prefix path
            hj_le_live le_rfl hstrict_prefix
        have hle_start : path'.times j ≤ path.sojournStart a := by
          rw [hpath'_j, ha_eq]
          simpa [CTMCPath.sojournStart] using htimes_le
        exact not_lt.mpr hle_start hlt
      have hstate' :=
        path'.frozenStateAt_eq_stateSeq_of_first_time_gt
          (path.sojournStart a) a htime_a hmin
      have hstateSeq_eq : path'.stateSeq a = path.stateSeq a := by
        simpa [path'] using
          DensityDepCTMC.strictCompletionThrough_stateSeq_eq
            path liveLast a
      rw [hstate', hstateSeq_eq]
    have hstate_eq : ∀ t ∈ Set.Icc (0 : ℝ) (path.sojournStart a),
        path'.frozenStateAt t = path.frozenStateAt t := by
      intro t ht
      by_cases hlt : t < path.sojournStart a
      · simpa [path'] using
          DensityDepCTMC.strictCompletionThrough_frozenStateAt_eq_of_lt_succ
            path liveLast (by simpa [ha_eq] using hlt)
      · have ht_eq : t = path.sojournStart a :=
          le_antisymm ht.2 (le_of_not_gt hlt)
        subst t
        rw [hstate_path'_start, hstate_path_start]
    have hEndpointTransfer :
        M.frozenGeneratorMartingalePart M.canonicalPathMap
            (path.sojournStart a) records =
          M.frozenGeneratorMartingalePart (fun _ : Unit => path')
            (path.sojournStart a) Unit.unit := by
      ext i
      simp only [DensityDepCTMC.frozenGeneratorMartingalePart,
        DensityDepCTMC.frozenDensityProcess,
        DensityDepCTMC.frozenInitialCondition, Pi.sub_apply]
      have hintegral :
          (∫ t in Set.Icc (0 : ℝ) (path.sojournStart a),
              M.generatorDrift (path.frozenStateAt t) i) =
            ∫ t in Set.Icc (0 : ℝ) (path.sojournStart a),
              M.generatorDrift (path'.frozenStateAt t) i := by
        apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
        intro t ht
        simpa [hstate_eq t ht]
      have h0_state : path'.frozenStateAt 0 = path.frozenStateAt 0 :=
        hstate_eq 0 ⟨le_rfl, le_of_lt hstart_pos⟩
      change
          (↑((path.frozenStateAt (path.sojournStart a) i) : ℕ) : ℝ) / ↑M.N -
                (↑((path.frozenStateAt 0 i) : ℕ) : ℝ) / ↑M.N -
              ∫ t in Set.Icc (0 : ℝ) (path.sojournStart a),
                M.generatorDrift (path.frozenStateAt t) i =
            (↑((path'.frozenStateAt (path.sojournStart a) i) : ℕ) : ℝ) / ↑M.N -
                (↑((path'.frozenStateAt 0 i) : ℕ) : ℝ) / ↑M.N -
              ∫ t in Set.Icc (0 : ℝ) (path.sojournStart a),
                M.generatorDrift (path'.frozenStateAt t) i
      rw [hstate_path'_start, hstate_path_start, h0_state, hintegral]
    have hEndpoint' :
        M.frozenGeneratorMartingalePart (fun _ : Unit => path')
            (path.sojournStart a) Unit.unit =
          fun i => M.frozenTimeCompensatedJumpMartingale path' i a := by
      have h :=
        frozenGeneratorMP_at_sojournStart_eq_frozenTimeCompensated
          M path' hcomp.2 hcomp.1 a
      simpa [path', hstart_eq] using h
    have hmp_eq :
        M.frozenGeneratorMartingalePart M.canonicalPathMap
            (path.sojournStart a) records =
          fun i => M.frozenTimeCompensatedJumpMartingale path i a := by
      calc
        M.frozenGeneratorMartingalePart M.canonicalPathMap
            (path.sojournStart a) records
            = M.frozenGeneratorMartingalePart (fun _ : Unit => path')
                (path.sojournStart a) Unit.unit := hEndpointTransfer
        _ = (fun i => M.frozenTimeCompensatedJumpMartingale path' i a) := hEndpoint'
        _ = (fun i => M.frozenTimeCompensatedJumpMartingale path i a) := by
              ext i
              rw [ha_eq]
              exact strictCompletionThrough_frozenTimeCompensated_eq_succ
                M path i liveLast
    have hstrict_weak : ∀ n, n + 1 < a →
        path.times n < path.times (n + 1) := by
      intro n hn
      exact hstrict_prefix n (by omega)
    have hskel_eq :
        M.frozenClockSkeletonVec T a records =
          fun i => M.frozenTimeCompensatedJumpMartingale path i a := by
      simpa [path] using
        frozenClockSkeletonVec_eq_frozenTimeCompensated_weak
          M T records a hstrict_weak hpos0 hstartT
    rw [hmp_eq, ← hskel_eq]
    have ha_mem : a ∈ Finset.range (a + 1 + 1) :=
      Finset.mem_range.mpr (by omega)
    have hsup := Finset.le_sup' (s := Finset.range (a + 1 + 1))
      (f := fun j => ‖M.frozenClockSkeletonVec T j records‖ ^ 2) ha_mem
    simp only [DensityDepCTMC.frozenClockSkeletonSupSq] at hsup ⊢
    nlinarith [M.frozenTruncatedJumpSqSum_nonneg T (a + 1) records]

/-- **Bridge bound for M*: ∀ᵐ records, ∃ n, sup_{s∈[0,T]} ‖M*(s)‖² ≤ (4/3)·skeleton(n) + 4·jump(n).**
The bridge for the generator-centered martingale. No BoundaryCompatibility needed. -/
theorem frozenGeneratorMP_bridge_ae
    {d : ℕ} [NeZero d] (M : DensityDepCTMC d)
    (x₀ : Fin d → Fin (M.N + 1))
    (hinit : M.InSimplex x₀) {T : ℝ} (hTpos : 0 < T) :
    ∀ᵐ records ∂M.canonicalRecordMeasure x₀,
      ∃ n, (⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
        ‖M.frozenGeneratorMartingalePart M.canonicalPathMap s records‖ ^ 2) ≤
      (4 / 3 : ℝ) * M.frozenClockSkeletonSupSq T n records +
        4 * M.frozenTruncatedJumpSqSum T n records := by
  have h_ae_hold : ∀ᵐ records ∂M.canonicalRecordMeasure x₀, ∀ n,
      ¬M.toQMatrix.IsAbsorbing
          (QMatrix.currentStateFromHistory n (Preorder.frestrictLe n records)) →
        0 < (records (n + 1)).1 :=
    M.toQMatrix.canonicalRecordMeasure_all_next_holdingTime_pos_ae_of_nonabsorbing x₀
  filter_upwards [h_ae_hold,
    M.toQMatrix.canonicalRecordMeasure_all_next_state_eq_current_ae_of_absorbing x₀,
    M.toQMatrix.canonicalRecordMeasure_all_next_holdingTime_eq_zero_ae_of_absorbing x₀,
    M.toQMatrix.canonicalRecordMeasure_all_next_state_ne_current_ae_of_nonabsorbing x₀,
    M.canonical_absorption_or_nonExplosive_ae x₀ hinit hTpos]
    with records hhold hstate_abs hhold_zero hnext_ne hdisj
  let path := M.canonicalPathMap records
  by_cases habsorb : ∃ a, M.toQMatrix.IsAbsorbing (path.stateSeq a)
  · -- Absorbed case: M* is constant after absorption, bound holds
    classical
    let a : ℕ := Nat.find habsorb
    have haAbs : M.toQMatrix.IsAbsorbing (path.stateSeq a) := by
      simpa [a] using Nat.find_spec habsorb
    have hnot_before : ∀ k, k < a →
        ¬ M.toQMatrix.IsAbsorbing (path.stateSeq k) := by
      intro k hk
      exact Nat.find_min habsorb hk
    have hstate_tail_path : ∀ n,
        M.toQMatrix.IsAbsorbing (path.stateSeq n) →
          path.stateSeq (n + 1) = path.stateSeq n := by
      intro n hn
      have hcur :=
        DensityDepCTMC.canonicalClockTail_currentState_eq_stateSeq
          M records n
      have hnext := hstate_abs n (by
        rw [hcur]
        exact hn)
      simpa [path, DensityDepCTMC.canonicalPathMap,
        QMatrix.recordTrajectoryToPath_stateSeq, hcur] using hnext
    have hhold_zero_record : ∀ n,
        M.toQMatrix.IsAbsorbing (path.stateSeq n) →
          (records (n + 1)).1 = 0 := by
      intro n hn
      have hcur :=
        DensityDepCTMC.canonicalClockTail_currentState_eq_stateSeq
          M records n
      exact hhold_zero n (by
        rw [hcur]
        exact hn)
    obtain ⟨hstate_tail, hhold_zero_tail_record⟩ :=
      gammaBridge_absorbed_from_firstAbsIdx
        M records a haAbs hstate_tail_path hhold_zero_record
    have hhold_zero_tail : ∀ k, a ≤ k → path.sojournTime k = 0 := by
      intro k hk
      rw [DensityDepCTMC.canonicalClockTail_sojournTime_eq_record
        M records k]
      exact hhold_zero_tail_record k hk
    have hdrift_abs : M.generatorDrift (path.stateSeq a) = 0 := by
      ext i
      exact M.generatorDrift_eq_zero_of_exitRateAt_zero
        (by simpa [DensityDepCTMC.exitRateAt] using haAbs) i
    refine ⟨a + 1, ?_⟩
    have hRHS_nonneg :
        0 ≤ (4 / 3 : ℝ) * M.frozenClockSkeletonSupSq T (a + 1) records +
            4 * M.frozenTruncatedJumpSqSum T (a + 1) records := by
      have := M.frozenClockSkeletonSupSq_nonneg T (a + 1) records
      have := M.frozenTruncatedJumpSqSum_nonneg T (a + 1) records
      nlinarith
    refine Real.iSup_le (fun s => ?_) hRHS_nonneg
    refine Real.iSup_le (fun ⟨hs0, hsT⟩ => ?_) hRHS_nonneg
    have hloc :=
      gammaBridge_locate_time_liveCell_or_absorbedTail
        path a (T := T) (s := s) ⟨hs0, hsT⟩
    cases hloc with
    | inl hcell =>
        rcases hcell with ⟨k, hk_lt_a, hstart_le, hs_lt_next, _hs_le_min⟩
        have hstrict_prefix : ∀ m < k,
            path.times m < path.times (m + 1) := by
          intro m hm
          have hm1_lt_a : m + 1 < a := by omega
          have hnabs := hnot_before (m + 1) hm1_lt_a
          have hcur :=
            DensityDepCTMC.canonicalClockTail_currentState_eq_stateSeq
              M records (m + 1)
          have hhold_m1 := hhold (m + 1) (by
            rw [hcur]
            exact hnabs)
          have hsoj_pos : 0 < path.sojournTime (m + 1) := by
            rw [DensityDepCTMC.canonicalClockTail_sojournTime_eq_record
              M records (m + 1)]
            exact hhold_m1
          simpa [CTMCPath.sojournTime, CTMCPath.sojournEnd,
            CTMCPath.sojournStart] using hsoj_pos
        have hpos : 0 < path.times 0 := by
          have ha_pos : 0 < a := by omega
          have hnabs0 := hnot_before 0 ha_pos
          have hcur0 :=
            DensityDepCTMC.canonicalClockTail_currentState_eq_stateSeq
              M records 0
          have hhold0 := hhold 0 (by
            rw [hcur0]
            exact hnabs0)
          have hsoj0 : 0 < path.sojournTime 0 := by
            rw [DensityDepCTMC.canonicalClockTail_sojournTime_eq_record
              M records 0]
            exact hhold0
          simpa [CTMCPath.sojournTime, CTMCPath.sojournEnd,
            CTMCPath.sojournStart] using hsoj0
        by_cases hnext_le_T : path.sojournStart (k + 1) ≤ T
        · exact gammaBridge_frozenGeneratorMP_cell_sq_le_bridge_prefix
            M T records hs0 hstrict_prefix hpos
            hstart_le hs_lt_next hnext_le_T (by omega)
        · exact frozenGeneratorMP_last_cell_sq_le_bridge_prefix
            M T records hs0 hstrict_prefix hpos hstart_le hsT
            (lt_of_not_ge hnext_le_T) (by omega)
    | inr htail =>
        have htail_eq :=
          gammaBridge_frozenGeneratorMP_tail_eq_start
            M records a hnot_before hhold hstate_tail hhold_zero_tail
            hnext_ne hdrift_abs htail
        rw [htail_eq]
        exact gammaBridge_firstAbsIdx_start_sq_le_bridge
          M T records a haAbs hnot_before hhold hstate_abs hhold_zero
          hnext_ne (le_trans htail hsT)
  · -- Non-absorbed case: global strict mono
    push_neg at habsorb
    have hsoj_pos : ∀ n, 0 < path.sojournTime n := by
      intro n
      have hnabs := habsorb n
      have hcur := DensityDepCTMC.canonicalClockTail_currentState_eq_stateSeq M records n
      have hhold_n := hhold n (by rw [hcur]; exact hnabs)
      show 0 < path.sojournTime n
      simp only [path, DensityDepCTMC.canonicalPathMap,
        QMatrix.recordTrajectoryToPath_sojournTime]
      exact hhold_n
    have hpos : 0 < path.times 0 := by
      have := hsoj_pos 0
      simp [CTMCPath.sojournTime, CTMCPath.sojournEnd, CTMCPath.sojournStart] at this
      exact this
    have hstrict : ∀ m, path.times m < path.times (m + 1) := by
      intro m
      have h := hsoj_pos (m + 1)
      simp [CTMCPath.sojournTime, CTMCPath.sojournEnd, CTMCPath.sojournStart] at h
      linarith
    rcases hdisj with ⟨a, habsorbed⟩ | ⟨n₀, hT_lt⟩
    · exact absurd habsorbed (habsorb a)
    · -- Use n = path.jumpCount T + 1 as witness
      have hfuture_T : ∃ n, T < path.times n := ⟨n₀, hT_lt⟩
      set kT := path.jumpCount T with hkT_def
      refine ⟨kT + 1, ?_⟩
      have hRHS_nonneg : (0 : ℝ) ≤ (4 / 3 : ℝ) * M.frozenClockSkeletonSupSq T (kT + 1) records +
          4 * M.frozenTruncatedJumpSqSum T (kT + 1) records := by
        have := M.frozenClockSkeletonSupSq_nonneg T (kT + 1) records
        have := M.frozenTruncatedJumpSqSum_nonneg T (kT + 1) records
        linarith
      refine Real.iSup_le (fun s => ?_) hRHS_nonneg
      refine Real.iSup_le (fun ⟨hs0, hsT⟩ => ?_) hRHS_nonneg
      have hfuture_s : ∃ n, s < path.times n :=
        ⟨n₀, lt_of_le_of_lt hsT hT_lt⟩
      have hk_le : path.jumpCount s ≤ kT :=
        path.jumpCount_mono hstrict hsT hfuture_s hfuture_T
      by_cases hcompleted : path.sojournStart (path.jumpCount s + 1) ≤ T
      · exact frozenGeneratorMP_cell_sq_le_bridge M T records hs0 hstrict hpos
          (path.sojournStart_jumpCount_le_of_exists hs0 hfuture_s)
          (by simpa [CTMCPath.sojournStart] using path.lt_times_jumpCount_of_exists hfuture_s)
          hcompleted (by omega)
      · push_neg at hcompleted
        have hk_eq : path.jumpCount s = kT := by
          refine le_antisymm hk_le ?_
          by_contra h; push_neg at h
          have hle_T : path.times (path.jumpCount s) ≤ T :=
            path.times_le_of_lt_jumpCount hfuture_T h
          have : path.sojournStart (path.jumpCount s + 1) ≤ T := by
            simpa [CTMCPath.sojournStart] using hle_T
          linarith
        calc ‖M.frozenGeneratorMartingalePart M.canonicalPathMap s records‖ ^ 2
            ≤ max (‖M.frozenClockSkeletonVec T kT records‖ ^ 2)
                  (‖M.frozenClockSkeletonVec T (kT + 1) records‖ ^ 2) := by
              exact frozenGeneratorMP_last_cell_sq_le_max M T records hs0 hstrict hpos
                (hk_eq ▸ path.sojournStart_jumpCount_le_of_exists hs0 hfuture_s)
                hsT (hk_eq ▸ hcompleted)
          _ ≤ (4 / 3 : ℝ) * M.frozenClockSkeletonSupSq T (kT + 1) records +
                4 * M.frozenTruncatedJumpSqSum T (kT + 1) records := by
              apply max_le
              · have hk_in : kT ∈ Finset.range (kT + 1 + 1) := Finset.mem_range.mpr (by omega)
                have := Finset.le_sup' (s := Finset.range (kT + 1 + 1))
                  (f := fun j => ‖M.frozenClockSkeletonVec T j records‖ ^ 2) hk_in
                simp only [DensityDepCTMC.frozenClockSkeletonSupSq] at this ⊢
                nlinarith [M.frozenTruncatedJumpSqSum_nonneg T (kT + 1) records]
              · have hk1_in : kT + 1 ∈ Finset.range (kT + 1 + 1) := Finset.mem_range.mpr (by omega)
                have := Finset.le_sup' (s := Finset.range (kT + 1 + 1))
                  (f := fun j => ‖M.frozenClockSkeletonVec T j records‖ ^ 2) hk1_in
                simp only [DensityDepCTMC.frozenClockSkeletonSupSq] at this ⊢
                nlinarith [M.frozenTruncatedJumpSqSum_nonneg T (kT + 1) records]

end Ripple.CTMC
