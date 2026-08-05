/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.MultiProductiveProperStage

/-!
# State-dependent proper-stage errors

The uniform proper-stage bounds replace every initial competitor gap by the
minimum gap `D` and then multiply by the number of species.  This file keeps
the actual initial gap against each competitor.  The resulting finite sums
are the starting point for removing the spurious species coefficient from
the paper's Lemma 12 and Theorem 5.
-/

namespace Tri.Multi

open scoped BigOperators ENNReal

variable {m n : ℕ}

/-! ## A stage-local safety potential -/

/-- The five fixed-pair jump masses satisfy the linear-base MGF inequality at
any upper bound `S` on the current plurality count. -/
theorem pairDeltaMass_five_linear_mgf_of_count_le
    (c : Config m n) (h3 : 3 ≤ n)
    (X Y : Species m) (hXY : X ≠ Y)
    (S d : ℕ) (hS : 0 < S) (hxS : count c X ≤ S)
    (hgap : HasPairwiseGap c X d) :
    pairDeltaMass c h3 X Y (-2) +
        pairDeltaMass c h3 X Y (-1) * pairGapLinearBase S d +
        pairDeltaMass c h3 X Y 0 * pairGapLinearBase S d ^ 2 +
        pairDeltaMass c h3 X Y 1 * pairGapLinearBase S d ^ 3 +
        pairDeltaMass c h3 X Y 2 * pairGapLinearBase S d ^ 4 ≤
      pairGapLinearBase S d ^ 2 := by
  apply five_jump_mgf_core
  · exact pairDeltaMass_five_sum c h3 X Y
  · exact pairGapLinearBase_le_one S d hS
  · rw [pairDeltaMass_neg_one_eq_thirdPartyDownMass_sum
        c h3 X Y hXY,
      pairDeltaMass_one_eq_thirdPartyUpMass_sum
        c h3 X Y hXY]
    exact thirdPartyDownMass_sum_le_up_mul_linearBase_of_count_le
      c h3 X Y hXY S d hS hxS hgap
  · rw [pairDeltaMass_neg_two_eq_directedFireMass
        c h3 X Y hXY,
      pairDeltaMass_two_eq_directedFireMass
        c h3 X Y hXY]
    exact reverse_directedFireMass_le_linearBase_sq_of_count_le
      c h3 X Y hXY S d hS hxS (hgap Y (Ne.symm hXY))

/-- The productive-event fixed-pair safety potential remains a
supermartingale while `count X ≤ S` and the global protected gap holds. -/
theorem productiveStep_pairGapLinearPotential_conserve_of_count_le
    (c : Config m n) (h3 : 3 ≤ n)
    (X Y : Species m) (hXY : X ≠ Y)
    (S d : ℕ) (hS : 0 < S) (hd2 : 2 ≤ d)
    (hxS : count c X ≤ S)
    (hgap : HasPairwiseGap c X d) :
    expect (productiveStep h3 c)
        (pairGapPotential (pairGapLinearBase S d) X Y) ≤
      pairGapPotential (pairGapLinearBase S d) X Y c :=
  productiveStep_conserve_of_multiStep_conserve c h3 _
    (ENNReal.pow_ne_top
      (ne_top_of_le_ne_top ENNReal.one_ne_top
        (pairGapLinearBase_le_one S d hS))) <| by
      have hXYgap := hgap Y (Ne.symm hXY)
      have hg2 : 2 ≤ pairGapNat c X Y := by
        unfold pairGapNat
        omega
      rw [expect_multiStep_pairGapPotential
        c h3 X Y (pairGapLinearBase S d) hg2]
      unfold pairGapPotential
      exact five_jump_geometric_of_core hg2
        (pairDeltaMass_five_linear_mgf_of_count_le
          c h3 X Y hXY S d hS hxS hgap)

/-- The common proper-stage stop conserves the fixed-pair safety potential
at the stage-local scale `S`. -/
theorem productiveInvolvingStageDeadlineStop_pair_local_linear_conserve
    (h3 : 3 ≤ n) (X Y : Species m) (hXY : X ≠ Y)
    (S d target K : ℕ) (hS : 0 < S) (hd2 : 2 ≤ d)
    (q : Config m n × ℕ) :
    expect
        (productiveInvolvingStageDeadlineStop h3 X S d target K q)
        (fun z =>
          pairGapPotential (pairGapLinearBase S d) X Y z.1) ≤
      pairGapPotential (pairGapLinearBase S d) X Y q.1 := by
  classical
  unfold productiveInvolvingStageDeadlineStop
  split_ifs with hlive
  · rw [← expect_map, productiveInvolvingCount_map_fst]
    exact productiveStep_pairGapLinearPotential_conserve_of_count_le
      q.1 h3 X Y hXY S d hS hd2 hlive.2.1 hlive.1
  · simp only [expect_pure]
    exact le_rfl

/-- Fixed-competitor completion-(a) mass with the actual initial pair gap and
the stage-local scale retained. -/
theorem productiveInvolvingStageDeadlineStop_pair_failure_local_linear_le
    (h3 : 3 ≤ n) (X Y : Species m) (hXY : X ≠ Y)
    (S d target K : ℕ) (hS : 0 < S) (hd2 : 2 ≤ d)
    (T : ℕ) (q0 : Config m n × ℕ) :
    (∑' q : Config m n × ℕ,
      if pairGapNat q.1 X Y < d then
        iter
          (productiveInvolvingStageDeadlineStop h3 X S d target K)
          T q0 q
      else 0) ≤
      pairGapLinearBase S d ^ pairGapNat q0.1 X Y /
        pairGapLinearBase S d ^ (d - 1) := by
  let u := pairGapLinearBase S d
  let V : Config m n × ℕ → ℝ≥0∞ := fun q =>
    pairGapPotential u X Y q.1
  let Bad : Config m n × ℕ → Prop := fun q =>
    pairGapNat q.1 X Y < d
  have hu1 : u ≤ 1 := by
    dsimp only [u]
    exact pairGapLinearBase_le_one S d hS
  have hu0 : u ≠ 0 := by
    dsimp only [u]
    exact pairGapLinearBase_ne_zero S d hS
  have hutop : u ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top hu1
  have htheta0 : u ^ (d - 1) ≠ 0 :=
    pow_ne_zero _ hu0
  have hthetaTop : u ^ (d - 1) ≠ ⊤ :=
    ENNReal.pow_ne_top hutop
  have hstep : ∀ q,
      expect
          (productiveInvolvingStageDeadlineStop h3 X S d target K q) V ≤
        V q := by
    intro q
    exact productiveInvolvingStageDeadlineStop_pair_local_linear_conserve
      h3 X Y hXY S d target K hS hd2 q
  have hbad : ∀ q, Bad q → u ^ (d - 1) ≤ V q := by
    intro q hq
    dsimp only [Bad] at hq
    dsimp only [V, pairGapPotential]
    exact pow_le_pow_right_of_le_one' hu1 (by omega)
  simpa only [Bad, V, u, pairGapPotential] using
    stopped_bad_mass_le
      (productiveInvolvingStageDeadlineStop h3 X S d target K)
      V Bad (u ^ (d - 1)) htheta0 hthetaTop
      hstep hbad T q0

/-- Global completion-(a) mass as a sum of the exact initial fixed-pair
quotients at the local stage scale. -/
theorem productiveInvolvingStageDeadlineStop_global_failure_local_linear_le
    (h3 : 3 ≤ n) (X : Species m)
    (S d target K : ℕ) (hS : 0 < S) (hd2 : 2 ≤ d)
    (T : ℕ) (q0 : Config m n × ℕ) :
    globalPairGapFailureMass
        ((iter
          (productiveInvolvingStageDeadlineStop h3 X S d target K)
          T q0).map Prod.fst)
        X d ≤
      ∑ Y ∈ Finset.univ.erase X,
        pairGapLinearBase S d ^ pairGapNat q0.1 X Y /
          pairGapLinearBase S d ^ (d - 1) := by
  calc
    globalPairGapFailureMass
        ((iter
          (productiveInvolvingStageDeadlineStop h3 X S d target K)
          T q0).map Prod.fst)
        X d ≤
      ∑ Y ∈ Finset.univ.erase X,
        ∑' c : Config m n,
          if pairGapNat c X Y < d then
            ((iter
              (productiveInvolvingStageDeadlineStop h3 X S d target K)
              T q0).map Prod.fst) c
          else 0 :=
      globalPairGapFailureMass_le_pair_sum _ X d (by omega)
    _ = ∑ Y ∈ Finset.univ.erase X,
        ∑' q : Config m n × ℕ,
          if pairGapNat q.1 X Y < d then
            iter
              (productiveInvolvingStageDeadlineStop h3 X S d target K)
              T q0 q
          else 0 := by
      apply Finset.sum_congr rfl
      intro Y _hY
      exact pairGapFailureMass_map_fst _ X Y d
    _ ≤ ∑ Y ∈ Finset.univ.erase X,
        pairGapLinearBase S d ^ pairGapNat q0.1 X Y /
          pairGapLinearBase S d ^ (d - 1) := by
      apply Finset.sum_le_sum
      intro Y hY
      have hYX : Y ≠ X := (Finset.mem_erase.mp hY).1
      exact
        productiveInvolvingStageDeadlineStop_pair_failure_local_linear_le
          h3 X Y (Ne.symm hYX) S d target K hS hd2 T q0

/-! ## The exact completion-(c) quotient -/

/-- Fixed-competitor completion-(c) tail before replacing the actual initial
gap by the minimum stage gap. -/
theorem
    productiveInvolvingStageDeadlineStop_fixed_pair_quotient_tail_of_target_le
    (h3 : 3 ≤ n) (X Y : Species m) (hXY : X ≠ Y)
    (D x0 target T : ℕ) (hD4 : 4 ≤ D) (hDx0 : D ≤ x0)
    (htarget : 1 ≤ target) (htargetLe : target ≤ properPairTarget D)
    (c0 : Config m n) :
    (∑' q : Config m n × ℕ,
      if pairGapNat q.1 X Y < target ∧ x0 ≤ 2 * q.2 then
        iter
          (productiveInvolvingStageDeadlineStop h3 X
            (properStageScale x0) (D / 2) target
            (properInvolvingTarget x0))
          T (c0, 0) q
      else 0) ≤
      pairProperProgressTilt (properStageScale x0) (D / 2) ^
          pairGapNat c0 X Y /
        (pairProperProgressTilt (properStageScale x0) (D / 2) ^
            (target - 1) *
          (pairProperProgressFactor
            (properStageScale x0) (D / 2))⁻¹ ^
              properInvolvingTarget x0) := by
  let q0 : ProductivePairJointState m n :=
    { config := c0, involving := 0, relevant := 0 }
  let S := properStageScale x0
  let d := D / 2
  let K := properInvolvingTarget x0
  let w := pairProperProgressTilt S d
  let φ := pairProperProgressFactor S d
  have hq0 : q0.CounterInv := by
    simp [q0, ProductivePairJointState.CounterInv]
  have htail :=
    productivePairJointStageDeadlineStop_involving_tail
      h3 X Y hXY S d target K T
      (properStageScale_pos x0 (by omega)) (by omega)
      (three_halfGap_le_properStageScale D x0 hDx0)
      htarget q0 hq0
  have hmap :=
    iter_productivePairJointStageDeadlineStop_map_involving
      h3 X Y S d target K T q0
  have hcommon :
      (∑' q : Config m n × ℕ,
        if pairGapNat q.1 X Y < target ∧ K ≤ q.2 then
          iter (productiveInvolvingStageDeadlineStop
            h3 X S d target K) T q0.toInvolving q
        else 0) =
      ∑' z : ProductivePairJointState m n,
        if pairGapNat z.config X Y < target ∧ K ≤ z.involving then
          iter (productivePairJointStageDeadlineStop
            h3 X Y S d target K) T q0 z
        else 0 := by
    let Bad : Config m n × ℕ → Prop := fun q =>
      pairGapNat q.1 X Y < target ∧ K ≤ q.2
    calc
      (∑' q : Config m n × ℕ,
          if pairGapNat q.1 X Y < target ∧ K ≤ q.2 then
            iter (productiveInvolvingStageDeadlineStop
              h3 X S d target K) T q0.toInvolving q
          else 0) =
        expect
          (iter (productiveInvolvingStageDeadlineStop
            h3 X S d target K) T q0.toInvolving)
          (fun q => (if Bad q then 1 else 0 : ℝ≥0∞)) := by
        unfold expect
        apply tsum_congr
        intro q
        by_cases hq : Bad q <;> simp [Bad, hq]
      _ = expect
          ((iter (productivePairJointStageDeadlineStop
            h3 X Y S d target K) T q0).map
              ProductivePairJointState.toInvolving)
          (fun q => (if Bad q then 1 else 0 : ℝ≥0∞)) := by
        rw [hmap]
      _ = expect
          (iter (productivePairJointStageDeadlineStop
            h3 X Y S d target K) T q0)
          (fun z => (if Bad z.toInvolving then 1 else 0 : ℝ≥0∞)) := by
        rw [expect_map]
      _ = ∑' z : ProductivePairJointState m n,
          if pairGapNat z.config X Y < target ∧ K ≤ z.involving then
            iter (productivePairJointStageDeadlineStop
              h3 X Y S d target K) T q0 z
          else 0 := by
        unfold expect
        apply tsum_congr
        intro z
        by_cases hz : Bad z.toInvolving
        · have hz' :
              pairGapNat z.config X Y < target ∧ K ≤ z.involving := by
            simpa [Bad, ProductivePairJointState.toInvolving] using hz
          simp [hz, hz']
        · have hz' :
              ¬ (pairGapNat z.config X Y < target ∧
                K ≤ z.involving) := by
            simpa [Bad, ProductivePairJointState.toInvolving] using hz
          simp [hz, hz']
  have htargetPred :
      target - 1 ≤ properPairTarget D - 1 :=
    Nat.sub_le_sub_right htargetLe 1
  have hw1 : w ≤ 1 := by
    dsimp only [w]
    exact pairProperProgressTilt_le_one S d
      (properStageScale_pos x0 (by omega))
  have hpowDen :
      w ^ (properPairTarget D - 1) ≤ w ^ (target - 1) :=
    pow_le_pow_right_of_le_one' hw1 htargetPred
  have hden :
      w ^ (properPairTarget D - 1) * (φ⁻¹) ^ K ≤
        w ^ (target - 1) * (φ⁻¹) ^ K := by
    simpa [mul_comm] using
      (mul_le_mul_right hpowDen ((φ⁻¹) ^ K))
  have _hcap :
      w ^ pairGapNat c0 X Y /
          (w ^ (target - 1) * (φ⁻¹) ^ K) ≤
        w ^ pairGapNat c0 X Y /
          (w ^ (properPairTarget D - 1) * (φ⁻¹) ^ K) :=
    ENNReal.div_le_div_left hden _
  simpa only [properInvolvingTarget_le_iff, q0,
    ProductivePairJointState.toInvolving,
    ProductivePairJointState.toRelevant,
    pairProgressPotential, pow_zero, mul_one,
    S, d, K, w, φ] using hcommon.le.trans htail

/-- The all-competitor completion-(c) mass is bounded by the sum of the exact
initial fixed-pair quotients. -/
theorem productiveInvolvingStageDeadlineStop_global_capped_quotient_tail
    (h3 : 3 ≤ n) (X : Species m)
    (D x0 T : ℕ) (hD4 : 4 ≤ D) (hDx0 : D ≤ x0)
    (hDn : D ≤ n)
    (c0 : Config m n) :
    globalProperTargetFailureMass
        (iter
          (productiveInvolvingStageDeadlineStop h3 X
            (properStageScale x0) (D / 2) (properStageTarget D n)
            (properInvolvingTarget x0))
          T (c0, 0))
        X (properStageTarget D n) (properInvolvingTarget x0) ≤
      ∑ Y ∈ Finset.univ.erase X,
        pairProperProgressTilt (properStageScale x0) (D / 2) ^
            pairGapNat c0 X Y /
          (pairProperProgressTilt (properStageScale x0) (D / 2) ^
              (properStageTarget D n - 1) *
            (pairProperProgressFactor
              (properStageScale x0) (D / 2))⁻¹ ^
                properInvolvingTarget x0) := by
  calc
    globalProperTargetFailureMass
        (iter
          (productiveInvolvingStageDeadlineStop h3 X
            (properStageScale x0) (D / 2) (properStageTarget D n)
            (properInvolvingTarget x0))
          T (c0, 0))
        X (properStageTarget D n) (properInvolvingTarget x0) ≤
      ∑ Y ∈ Finset.univ.erase X,
        ∑' q : Config m n × ℕ,
          if pairGapNat q.1 X Y < properStageTarget D n ∧
              properInvolvingTarget x0 ≤ q.2 then
            iter
              (productiveInvolvingStageDeadlineStop h3 X
                (properStageScale x0) (D / 2)
                (properStageTarget D n)
                (properInvolvingTarget x0))
              T (c0, 0) q
          else 0 :=
      globalProperTargetFailureMass_le_pair_sum
        _ X (properStageTarget D n) (properInvolvingTarget x0)
        (properStageTarget_pos D n (by omega) hDn)
    _ ≤ ∑ Y ∈ Finset.univ.erase X,
        pairProperProgressTilt (properStageScale x0) (D / 2) ^
            pairGapNat c0 X Y /
          (pairProperProgressTilt (properStageScale x0) (D / 2) ^
              (properStageTarget D n - 1) *
            (pairProperProgressFactor
              (properStageScale x0) (D / 2))⁻¹ ^
                properInvolvingTarget x0) := by
      apply Finset.sum_le_sum
      intro Y hY
      have hYX : Y ≠ X := (Finset.mem_erase.mp hY).1
      simpa only [properInvolvingTarget_le_iff] using
        productiveInvolvingStageDeadlineStop_fixed_pair_quotient_tail_of_target_le
          h3 X Y (Ne.symm hYX) D x0 (properStageTarget D n) T
          hD4 hDx0
          (properStageTarget_pos D n (by omega) hDn)
          (properStageTarget_le_pairTarget D n) c0

/-! ## One complete state-dependent proper stage -/

/-- Exact state-dependent error for one proper stage. -/
noncomputable def productiveProperStageStateError
    (X : Species m) (D x0 : ℕ) (c0 : Config m n) : ℝ≥0∞ :=
  (∑ Y ∈ Finset.univ.erase X,
      pairGapLinearBase (properStageScale x0) (D / 2) ^
          pairGapNat c0 X Y /
        pairGapLinearBase (properStageScale x0) (D / 2) ^
          (D / 2 - 1)) +
    (∑ Y ∈ Finset.univ.erase X,
      pairProperProgressTilt (properStageScale x0) (D / 2) ^
          pairGapNat c0 X Y /
        (pairProperProgressTilt (properStageScale x0) (D / 2) ^
            (properStageTarget D n - 1) *
          (pairProperProgressFactor
            (properStageScale x0) (D / 2))⁻¹ ^
              properInvolvingTarget x0)) +
    ENNReal.ofReal (Real.exp (-(x0 : ℝ) / 8))

/-- One full proper stage with both all-competitor union bounds retaining the
actual initial pair gaps. -/
theorem productiveProperStage_progress_state
    (h3 : 3 ≤ n) (X : Species m)
    (D x0 : ℕ) (hD4 : 4 ≤ D) (hDx0 : D ≤ x0)
    (c0 : Config m n) (hx0 : count c0 X = x0) :
    let p :=
      iter
        (productiveInvolvingStageDeadlineStop h3 X
          (properStageScale x0) (D / 2) (properStageTarget D n)
          (properInvolvingTarget x0))
        (2 * n) (c0, 0)
    globalPairGapFailureMass (p.map Prod.fst)
        X (properStageTarget D n) ≤
      productiveProperStageStateError X D x0 c0 := by
  classical
  dsimp only
  let p :=
    iter
      (productiveInvolvingStageDeadlineStop h3 X
        (properStageScale x0) (D / 2) (properStageTarget D n)
        (properInvolvingTarget x0))
      (2 * n) (c0, 0)
  have hx0n : x0 ≤ n := by
    rw [← hx0]
    have htotal := count_add_zSum c0 X
    omega
  have hDn : D ≤ n := hDx0.trans hx0n
  have hS : 0 < properStageScale x0 :=
    properStageScale_pos x0 (by omega)
  have hdecomp :=
    productiveProperStage_failure_decomposition
      h3 X D x0 (2 * n) c0 hx0
  have ha :=
    productiveInvolvingStageDeadlineStop_global_failure_local_linear_le
      h3 X (properStageScale x0) (D / 2)
      (properStageTarget D n) (properInvolvingTarget x0)
      hS (by omega) (2 * n) (c0, 0)
  have hc :=
    productiveInvolvingStageDeadlineStop_global_capped_quotient_tail
      h3 X D x0 (2 * n) hD4 hDx0 hDn c0
  have hb :=
    productiveProperStage_completion_b
      h3 X D x0 hD4 c0 hx0
  unfold productiveProperStageStateError
  simpa only [p] using
    hdecomp.trans (add_le_add (add_le_add ha hc) hb)

end Tri.Multi

#print axioms Tri.Multi.productiveProperStage_progress_state
