/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.MultiProductiveStageCompletion

/-!
# Proper-stage no-backsliding on the common deadline process

Completion (a) is controlled on the same process as completions (b) and (c).
Additional stage boundaries only freeze the chain, so every fixed-competitor
linear-base gap potential remains a supermartingale.
-/

namespace Tri.Multi

open scoped BigOperators ENNReal

variable {m n : ℕ}

/-- Forgetting the involvement counter recovers one productive physical
step. -/
theorem productiveInvolvingCount_map_fst
    (h3 : 3 ≤ n) (X : Species m) (q : Config m n × ℕ) :
    (productiveInvolvingCount h3 X q).map Prod.fst =
      productiveStep h3 q.1 := by
  classical
  by_cases hprod : productiveMass q.1 h3 ≠ 0
  · rw [show productiveInvolvingCount h3 X q =
        (productiveSamplePMF q.1 h3 hprod).map fun t =>
          (sampleNext q.1 t,
            if IsXInvolvingSample X t then q.2 + 1 else q.2) by
        unfold productiveInvolvingCount
        simp [hprod]]
    rw [productiveStep_of_mass_ne_zero h3 q.1 hprod, PMF.map_comp]
    congr 1
  · rw [show productiveInvolvingCount h3 X q = PMF.pure q by
        unfold productiveInvolvingCount
        simp [hprod]]
    rw [PMF.pure_map]
    unfold productiveStep
    simp [hprod]

/-- A fixed-competitor linear-base safety potential is conserved by the
common proper-stage deadline stop. -/
theorem productiveInvolvingStageDeadlineStop_pair_linear_conserve
    (h3 : 3 ≤ n) (X Y : Species m) (hXY : X ≠ Y)
    (S d target K : ℕ) (hd2 : 2 ≤ d)
    (q : Config m n × ℕ) :
    expect
        (productiveInvolvingStageDeadlineStop h3 X S d target K q)
        (fun z =>
          pairGapPotential (pairGapLinearBase n d) X Y z.1) ≤
      pairGapPotential (pairGapLinearBase n d) X Y q.1 := by
  classical
  unfold productiveInvolvingStageDeadlineStop
  split_ifs with hlive
  · rw [← expect_map, productiveInvolvingCount_map_fst]
    exact productiveStep_pairGapLinearPotential_conserve
      q.1 h3 X Y hXY d hd2 hlive.1
  · simp only [expect_pure]
    exact le_rfl

/-- Fixed-competitor completion-(a) mass on the common stage process. -/
theorem productiveInvolvingStageDeadlineStop_pair_failure_linear_le
    (h3 : 3 ≤ n) (X Y : Species m) (hXY : X ≠ Y)
    (S d target K : ℕ) (hd2 : 2 ≤ d)
    (T : ℕ) (q0 : Config m n × ℕ) :
    (∑' q : Config m n × ℕ,
      if pairGapNat q.1 X Y < d then
        iter
          (productiveInvolvingStageDeadlineStop h3 X S d target K)
          T q0 q
      else 0) ≤
      pairGapLinearBase n d ^ pairGapNat q0.1 X Y /
        pairGapLinearBase n d ^ (d - 1) := by
  let u := pairGapLinearBase n d
  let V : Config m n × ℕ → ℝ≥0∞ := fun q =>
    pairGapPotential u X Y q.1
  let Bad : Config m n × ℕ → Prop := fun q =>
    pairGapNat q.1 X Y < d
  have hu1 : u ≤ 1 :=
    pairGapLinearBase_le_one n d (by omega)
  have hu0 : u ≠ 0 :=
    pairGapLinearBase_ne_zero n d (by omega)
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
    exact productiveInvolvingStageDeadlineStop_pair_linear_conserve
      h3 X Y hXY S d target K hd2 q
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

/-- A fixed-pair bad mass can be evaluated before or after forgetting the
involvement counter. -/
theorem pairGapFailureMass_map_fst
    (p : PMF (Config m n × ℕ)) (X Y : Species m) (d : ℕ) :
    (∑' c : Config m n,
      if pairGapNat c X Y < d then (p.map Prod.fst) c else 0) =
      ∑' q : Config m n × ℕ,
        if pairGapNat q.1 X Y < d then p q else 0 := by
  let Bad : Config m n → Prop := fun c => pairGapNat c X Y < d
  calc
    (∑' c : Config m n,
        if pairGapNat c X Y < d then (p.map Prod.fst) c else 0) =
      expect (p.map Prod.fst)
        (fun c => (if Bad c then 1 else 0 : ℝ≥0∞)) := by
      unfold expect
      apply tsum_congr
      intro c
      by_cases hc : Bad c <;> simp [Bad, hc]
    _ = expect p
        (fun q => (if Bad q.1 then 1 else 0 : ℝ≥0∞)) := by
      rw [expect_map]
    _ = ∑' q : Config m n × ℕ,
        if pairGapNat q.1 X Y < d then p q else 0 := by
      unfold expect
      apply tsum_congr
      intro q
      by_cases hq : Bad q.1 <;> simp [Bad, hq]

/-- Global completion-(a) bound before scalar instantiation. -/
theorem productiveInvolvingStageDeadlineStop_global_failure_linear_le
    (h3 : 3 ≤ n) (X : Species m)
    (S d target K : ℕ) (hd2 : 2 ≤ d)
    (T : ℕ) (q0 : Config m n × ℕ) :
    globalPairGapFailureMass
        ((iter
          (productiveInvolvingStageDeadlineStop h3 X S d target K)
          T q0).map Prod.fst)
        X d ≤
      ∑ Y ∈ Finset.univ.erase X,
        pairGapLinearBase n d ^ pairGapNat q0.1 X Y /
          pairGapLinearBase n d ^ (d - 1) := by
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
        pairGapLinearBase n d ^ pairGapNat q0.1 X Y /
          pairGapLinearBase n d ^ (d - 1) := by
      apply Finset.sum_le_sum
      intro Y hY
      have hYX : Y ≠ X := (Finset.mem_erase.mp hY).1
      exact productiveInvolvingStageDeadlineStop_pair_failure_linear_le
        h3 X Y (Ne.symm hYX) S d target K hd2 T q0

/-- A buffered initial gap gives one common completion-(a) power. -/
theorem productiveInvolvingStageDeadlineStop_global_failure_linear_le_of_buffer
    (h3 : 3 ≤ n) (X : Species m)
    (S d target K b : ℕ) (hd2 : 2 ≤ d)
    (T : ℕ) (c0 : Config m n)
    (hinit : HasPairwiseGap c0 X (d + b)) :
    globalPairGapFailureMass
        ((iter
          (productiveInvolvingStageDeadlineStop h3 X S d target K)
          T (c0, 0)).map Prod.fst)
        X d ≤
      (m : ℝ≥0∞) * pairGapLinearBase n d ^ (b + 1) := by
  let u := pairGapLinearBase n d
  have hu1 : u ≤ 1 :=
    pairGapLinearBase_le_one n d (by omega)
  have hu0 : u ≠ 0 :=
    pairGapLinearBase_ne_zero n d (by omega)
  have hutop : u ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top hu1
  have htheta0 : u ^ (d - 1) ≠ 0 :=
    pow_ne_zero _ hu0
  have hthetaTop : u ^ (d - 1) ≠ ⊤ :=
    ENNReal.pow_ne_top hutop
  calc
    globalPairGapFailureMass
        ((iter
          (productiveInvolvingStageDeadlineStop h3 X S d target K)
          T (c0, 0)).map Prod.fst)
        X d ≤
      ∑ Y ∈ Finset.univ.erase X,
        u ^ pairGapNat c0 X Y / u ^ (d - 1) := by
      simpa only [u] using
        productiveInvolvingStageDeadlineStop_global_failure_linear_le
          h3 X S d target K hd2 T (c0, 0)
    _ ≤ ∑ Y ∈ Finset.univ.erase X, u ^ (b + 1) := by
      apply Finset.sum_le_sum
      intro Y hY
      have hYX : Y ≠ X := (Finset.mem_erase.mp hY).1
      have hgap := hinit Y hYX
      have hnat : d + b ≤ pairGapNat c0 X Y := by
        unfold pairGapNat
        omega
      have hpow :
          u ^ pairGapNat c0 X Y ≤ u ^ (d + b) :=
        pow_le_pow_right_of_le_one' hu1 hnat
      calc
        u ^ pairGapNat c0 X Y / u ^ (d - 1) ≤
            u ^ (d + b) / u ^ (d - 1) :=
          ENNReal.div_le_div_right hpow _
        _ = u ^ (b + 1) := by
          rw [show d + b = (d - 1) + (b + 1) by omega,
            pow_add, mul_comm, mul_div_assoc,
            ENNReal.div_self htheta0 hthetaTop, mul_one]
    _ = ((Finset.univ.erase X).card : ℝ≥0∞) * u ^ (b + 1) := by
      simp
    _ ≤ (m : ℝ≥0∞) * u ^ (b + 1) := by
      gcongr
      simp

/-- Exact exponential envelope for completion (a) on the common deadline
process. -/
theorem productiveInvolvingStageDeadlineStop_global_failure_linear_exp
    (h3 : 3 ≤ n) (X : Species m)
    (S d target K b : ℕ) (hd2 : 2 ≤ d)
    (T : ℕ) (c0 : Config m n)
    (hinit : HasPairwiseGap c0 X (d + b)) :
    globalPairGapFailureMass
        ((iter
          (productiveInvolvingStageDeadlineStop h3 X S d target K)
          T (c0, 0)).map Prod.fst)
        X d ≤
      (m : ℝ≥0∞) *
        ENNReal.ofReal
          (Real.exp (-(((b + 1 : ℕ) : ℝ) * (d : ℝ) /
            (2 * (n : ℝ) + (d : ℝ))))) := by
  calc
    globalPairGapFailureMass
        ((iter
          (productiveInvolvingStageDeadlineStop h3 X S d target K)
          T (c0, 0)).map Prod.fst)
        X d ≤
      (m : ℝ≥0∞) * pairGapLinearBase n d ^ (b + 1) :=
        productiveInvolvingStageDeadlineStop_global_failure_linear_le_of_buffer
          h3 X S d target K b hd2 T c0 hinit
    _ ≤ (m : ℝ≥0∞) *
        ENNReal.ofReal
          (Real.exp (-(((b + 1 : ℕ) : ℝ) * (d : ℝ) /
            (2 * (n : ℝ) + (d : ℝ))))) :=
      mul_le_mul_right
        (pairGapLinearBase_pow_le_exp n d (b + 1) (by omega)) _

/-- Paper-shaped completion-(a) bound on the common proper-stage process. -/
theorem productiveProperStage_completion_a
    (h3 : 3 ≤ n) (X : Species m)
    (D x0 : ℕ) (hD4 : 4 ≤ D) (hDn : D ≤ n)
    (c0 : Config m n) (hinit : HasPairwiseGap c0 X D) :
    globalPairGapFailureMass
        ((iter
          (productiveInvolvingStageDeadlineStop h3 X
            (properStageScale x0) (D / 2) (properStageTarget D n)
            (properInvolvingTarget x0))
          (2 * n) (c0, 0)).map Prod.fst)
        X (D / 2) ≤
      (m : ℝ≥0∞) *
        ENNReal.ofReal
          (Real.exp (-((D : ℝ) ^ 2 / (18 * (n : ℝ))))) := by
  let d := D / 2
  let b := D - d
  have hd2 : 2 ≤ d := by
    dsimp only [d]
    omega
  have hdb : d + b = D := by
    dsimp only [d, b]
    omega
  have hbase :=
    productiveInvolvingStageDeadlineStop_global_failure_linear_exp
      h3 X (properStageScale x0) d (properStageTarget D n)
      (properInvolvingTarget x0) b hd2 (2 * n) c0
      (by simpa [hdb] using hinit)
  have hdNat : D ≤ 3 * d := by
    dsimp only [d]
    omega
  have hbNat : D ≤ 2 * (b + 1) := by
    dsimp only [b, d]
    omega
  have hdenNat : 2 * n + d ≤ 3 * n := by
    dsimp only [d]
    omega
  have hnumNat : D ^ 2 ≤ 6 * (b + 1) * d := by
    have hmul := Nat.mul_le_mul hbNat hdNat
    calc
      D ^ 2 = D * D := by ring
      _ ≤ 2 * (b + 1) * (3 * d) := hmul
      _ = 6 * (b + 1) * d := by ring
  have hnR : (0 : ℝ) < n := by
    exact_mod_cast (by omega : 0 < n)
  have hdenR : (2 : ℝ) * n + d ≤ 3 * n := by
    exact_mod_cast hdenNat
  have hnumR :
      (D : ℝ) ^ 2 ≤ 6 * (b + 1 : ℕ) * d := by
    exact_mod_cast hnumNat
  have hscalar :
      (D : ℝ) ^ 2 / (18 * (n : ℝ)) ≤
        ((b + 1 : ℕ) : ℝ) * (d : ℝ) /
          (2 * (n : ℝ) + (d : ℝ)) := by
    calc
      (D : ℝ) ^ 2 / (18 * (n : ℝ)) ≤
          (6 * ((b + 1 : ℕ) : ℝ) * (d : ℝ)) /
            (18 * (n : ℝ)) := by
        gcongr
      _ = ((b + 1 : ℕ) : ℝ) * (d : ℝ) /
            (3 * (n : ℝ)) := by
        field_simp
        ring
      _ ≤ ((b + 1 : ℕ) : ℝ) * (d : ℝ) /
            (2 * (n : ℝ) + (d : ℝ)) := by
        apply div_le_div_of_nonneg_left
        · positivity
        · positivity
        · exact hdenR
  exact hbase.trans <| by
    gcongr

end Tri.Multi

#print axioms Tri.Multi.productiveInvolvingCount_map_fst
#print axioms Tri.Multi.productiveInvolvingStageDeadlineStop_pair_failure_linear_le
#print axioms Tri.Multi.productiveProperStage_completion_a
