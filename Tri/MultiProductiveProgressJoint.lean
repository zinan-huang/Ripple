/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.MultiProductiveProgressStep

/-!
# Joint involvement and fixed-pair counters

Completion (c) of a proper stage is phrased using productive reactions
involving the distinguished species `X`, whereas the four-jump progress
potential uses all reactions that change the fixed gap `X-Y`.  This file puts
both counters on the same full-state sample path.
-/

namespace Tri.Multi

open scoped BigOperators ENNReal

variable {m n : ℕ}

/-- Every productive reaction involving `X` changes the gap between `X` and
any distinct fixed competitor `Y`. -/
theorem samplePairDelta_ne_zero_of_isXInvolving
    {c : Config m n} (X Y : Species m) (hXY : X ≠ Y)
    (t : TripleSample c) (ht : IsXInvolvingSample X t) :
  samplePairDelta t X Y ≠ 0 := by
  obtain ⟨Z, hZX, hfire | hfire⟩ := ht
  · let p : FirePair t := ⟨(X, Z), hfire⟩
    have hclass : classify t = some p :=
      classify_eq_some_of_fire t p
    rw [samplePairDelta, hclass]
    change directedPairDelta X Z X Y ≠ 0
    by_cases hZY : Z = Y
    · subst Z
      simp [directedPairDelta, speciesDelta, hZX]
    · simp [directedPairDelta, speciesDelta,
        Ne.symm hXY, Ne.symm hZY]
  · let p : FirePair t := ⟨(Z, X), hfire⟩
    have hclass : classify t = some p :=
      classify_eq_some_of_fire t p
    rw [samplePairDelta, hclass]
    change directedPairDelta Z X X Y ≠ 0
    by_cases hZY : Z = Y
    · subst Z
      simp [directedPairDelta, speciesDelta, hXY]
    · simp [directedPairDelta, speciesDelta,
        Ne.symm hXY, Ne.symm hZX, Ne.symm hZY]

/-- Full productive-event state carrying both the completion-(c) involvement
counter and the fixed-pair relevant-jump counter. -/
structure ProductivePairJointState (m n : ℕ) where
  config : Config m n
  involving : ℕ
  relevant : ℕ

/-- Pathwise relation between the completion-(c) clock and every fixed-pair
relevant clock. -/
def ProductivePairJointState.CounterInv
    (q : ProductivePairJointState m n) : Prop :=
  q.involving ≤ q.relevant

/-- Forget the fixed-pair counter. -/
def ProductivePairJointState.toInvolving
    (q : ProductivePairJointState m n) : Config m n × ℕ :=
  (q.config, q.involving)

/-- Forget the distinguished-species involvement counter. -/
def ProductivePairJointState.toRelevant
    (q : ProductivePairJointState m n) : Config m n × ℕ :=
  (q.config, q.relevant)

/-- The conditioned productive-event kernel with both counters driven by the
same physical sample. -/
noncomputable def productivePairJointCount
    (h3 : 3 ≤ n) (X Y : Species m) :
    ProductivePairJointState m n → PMF (ProductivePairJointState m n) := by
  classical
  exact fun q => by
    by_cases hprod : productiveMass q.config h3 ≠ 0
    · exact (productiveSamplePMF q.config h3 hprod).map fun t =>
        { config := sampleNext q.config t
          involving :=
            if IsXInvolvingSample X t then q.involving + 1
            else q.involving
          relevant :=
            if samplePairDelta t X Y = 0 then q.relevant
            else q.relevant + 1 }
    · exact PMF.pure q

/-- One productive sample preserves the pathwise counter ordering. -/
theorem ProductivePairJointState.counterInv_next
    (X Y : Species m) (hXY : X ≠ Y)
    (q : ProductivePairJointState m n) (hq : q.CounterInv)
    (t : TripleSample q.config) :
    (if IsXInvolvingSample X t then q.involving + 1
      else q.involving) ≤
      (if samplePairDelta t X Y = 0 then q.relevant
      else q.relevant + 1) := by
  by_cases hXt : IsXInvolvingSample X t
  · have hdelta :=
      samplePairDelta_ne_zero_of_isXInvolving X Y hXY t hXt
    simpa [hXt, hdelta] using hq
  · by_cases hdelta : samplePairDelta t X Y = 0
    · simpa [hXt, hdelta] using hq
    · simp [hXt, hdelta]
      unfold ProductivePairJointState.CounterInv at hq
      omega

/-- A joint counted step preserves the counter ordering on its support. -/
theorem productivePairJointCount_counterInv_of_apply_ne_zero
    (h3 : 3 ≤ n) (X Y : Species m) (hXY : X ≠ Y)
    (q : ProductivePairJointState m n) (hq : q.CounterInv)
    (z : ProductivePairJointState m n)
    (hqz : productivePairJointCount h3 X Y q z ≠ 0) :
    z.CounterInv := by
  classical
  by_cases hprod : productiveMass q.config h3 ≠ 0
  · rw [show productivePairJointCount h3 X Y q =
        (productiveSamplePMF q.config h3 hprod).map fun t =>
          { config := sampleNext q.config t
            involving :=
              if IsXInvolvingSample X t then q.involving + 1
              else q.involving
            relevant :=
              if samplePairDelta t X Y = 0 then q.relevant
              else q.relevant + 1 } by
        unfold productivePairJointCount
        simp [hprod]] at hqz
    rw [PMF.map_apply, Ne, ENNReal.tsum_eq_zero] at hqz
    push Not at hqz
    obtain ⟨t, ht⟩ := hqz
    let zt : ProductivePairJointState m n :=
      { config := sampleNext q.config t
        involving :=
          if IsXInvolvingSample X t then q.involving + 1
          else q.involving
        relevant :=
          if samplePairDelta t X Y = 0 then q.relevant
          else q.relevant + 1 }
    by_cases hzt : z = zt
    · subst z
      simpa only [ProductivePairJointState.CounterInv, zt] using
        q.counterInv_next X Y hXY hq t
    · simp [zt, hzt] at ht
  · rw [show productivePairJointCount h3 X Y q = PMF.pure q by
        unfold productivePairJointCount
        simp [hprod]] at hqz
    simp only [PMF.pure_apply] at hqz
    by_cases hzq : z = q
    · simpa [hzq] using hq
    · simp [hzq] at hqz

/-- The completion-(c) involvement count never exceeds the fixed-pair
relevant count along any supported finite productive path. -/
theorem productivePairJoint_iter_counterInv
    (h3 : 3 ≤ n) (X Y : Species m) (hXY : X ≠ Y)
    (T : ℕ) (q z : ProductivePairJointState m n)
    (hq : q.CounterInv)
    (hqz : iter (productivePairJointCount h3 X Y) T q z ≠ 0) :
    z.CounterInv := by
  induction T generalizing q with
  | zero =>
      simp only [iter, PMF.pure_apply] at hqz
      by_cases hzq : z = q
      · simpa [hzq] using hq
      · simp [hzq] at hqz
  | succ T ih =>
      rw [iter_succ, PMF.bind_apply] at hqz
      by_contra hzInv
      apply hqz
      rw [ENNReal.tsum_eq_zero]
      intro a
      by_cases hqa : productivePairJointCount h3 X Y q a = 0
      · simp [hqa]
      · have haInv :=
          productivePairJointCount_counterInv_of_apply_ne_zero
            h3 X Y hXY q hq a hqa
        have hiaz : iter (productivePairJointCount h3 X Y) T a z = 0 := by
          by_contra hne
          exact hzInv (ih a haInv hne)
        simp [hiaz]

/-- The involvement marginal is exactly the existing productive involvement
counter kernel. -/
theorem productivePairJointCount_map_involving
    (h3 : 3 ≤ n) (X Y : Species m)
    (q : ProductivePairJointState m n) :
    (productivePairJointCount h3 X Y q).map
        ProductivePairJointState.toInvolving =
      productiveInvolvingCount h3 X q.toInvolving := by
  classical
  by_cases hprod : productiveMass q.config h3 ≠ 0
  · rw [show productivePairJointCount h3 X Y q =
        (productiveSamplePMF q.config h3 hprod).map fun t =>
          { config := sampleNext q.config t
            involving :=
              if IsXInvolvingSample X t then q.involving + 1
              else q.involving
            relevant :=
              if samplePairDelta t X Y = 0 then q.relevant
              else q.relevant + 1 } by
        unfold productivePairJointCount
        simp [hprod]]
    rw [show productiveInvolvingCount h3 X q.toInvolving =
        (productiveSamplePMF q.config h3 hprod).map fun t =>
          (sampleNext q.config t,
            if IsXInvolvingSample X t then q.involving + 1
            else q.involving) by
        unfold productiveInvolvingCount
        simp [hprod, ProductivePairJointState.toInvolving]]
    rw [PMF.map_comp]
    apply congrArg
      (fun f => PMF.map f (productiveSamplePMF q.config h3 hprod))
    funext t
    rfl
  · rw [show productivePairJointCount h3 X Y q = PMF.pure q by
        unfold productivePairJointCount
        simp [hprod]]
    rw [show productiveInvolvingCount h3 X q.toInvolving =
        PMF.pure q.toInvolving by
        unfold productiveInvolvingCount
        simp [hprod, ProductivePairJointState.toInvolving]]
    exact PMF.pure_map _ _

/-- The relevant-jump marginal is exactly the existing fixed-pair counter
kernel. -/
theorem productivePairJointCount_map_relevant
    (h3 : 3 ≤ n) (X Y : Species m)
    (q : ProductivePairJointState m n) :
    (productivePairJointCount h3 X Y q).map
        ProductivePairJointState.toRelevant =
      productivePairRelevantCount h3 X Y q.toRelevant := by
  classical
  by_cases hprod : productiveMass q.config h3 ≠ 0
  · rw [show productivePairJointCount h3 X Y q =
        (productiveSamplePMF q.config h3 hprod).map fun t =>
          { config := sampleNext q.config t
            involving :=
              if IsXInvolvingSample X t then q.involving + 1
              else q.involving
            relevant :=
              if samplePairDelta t X Y = 0 then q.relevant
              else q.relevant + 1 } by
        unfold productivePairJointCount
        simp [hprod]]
    rw [show productivePairRelevantCount h3 X Y q.toRelevant =
        (productiveSamplePMF q.config h3 hprod).map fun t =>
          (sampleNext q.config t,
            if samplePairDelta t X Y = 0 then q.relevant
            else q.relevant + 1) by
        unfold productivePairRelevantCount
        simp [hprod, ProductivePairJointState.toRelevant]]
    rw [PMF.map_comp]
    apply congrArg
      (fun f => PMF.map f (productiveSamplePMF q.config h3 hprod))
    funext t
    rfl
  · rw [show productivePairJointCount h3 X Y q = PMF.pure q by
        unfold productivePairJointCount
        simp [hprod]]
    rw [show productivePairRelevantCount h3 X Y q.toRelevant =
        PMF.pure q.toRelevant by
        unfold productivePairRelevantCount
        simp [hprod, ProductivePairJointState.toRelevant]]
    exact PMF.pure_map _ _

/-- Joint counter kernel stopped on exactly the same safety/success boundary
as the fixed-pair progress kernel. -/
noncomputable def productivePairJointStop
    (h3 : 3 ≤ n) (X Y : Species m) (d target : ℕ) :
    ProductivePairJointState m n → PMF (ProductivePairJointState m n) := by
  classical
  exact fun q =>
    if HasPairwiseGap q.config X d ∧
        pairGapNat q.config X Y < target then
      productivePairJointCount h3 X Y q
    else
      PMF.pure q

/-- The stopped joint kernel also preserves counter ordering on its support. -/
theorem productivePairJointStop_counterInv_of_apply_ne_zero
    (h3 : 3 ≤ n) (X Y : Species m) (hXY : X ≠ Y)
    (d target : ℕ)
    (q : ProductivePairJointState m n) (hq : q.CounterInv)
    (z : ProductivePairJointState m n)
    (hqz : productivePairJointStop h3 X Y d target q z ≠ 0) :
    z.CounterInv := by
  classical
  unfold productivePairJointStop at hqz
  by_cases hlive :
      HasPairwiseGap q.config X d ∧ pairGapNat q.config X Y < target
  · rw [if_pos hlive] at hqz
    exact productivePairJointCount_counterInv_of_apply_ne_zero
      h3 X Y hXY q hq z hqz
  · rw [if_neg hlive] at hqz
    simp only [PMF.pure_apply] at hqz
    by_cases hzq : z = q
    · simpa [hzq] using hq
    · simp [hzq] at hqz

/-- Counter ordering holds along every supported finite stopped path. -/
theorem productivePairJointStop_iter_counterInv
    (h3 : 3 ≤ n) (X Y : Species m) (hXY : X ≠ Y)
    (d target T : ℕ) (q z : ProductivePairJointState m n)
    (hq : q.CounterInv)
    (hqz : iter (productivePairJointStop h3 X Y d target) T q z ≠ 0) :
    z.CounterInv := by
  induction T generalizing q with
  | zero =>
      simp only [iter, PMF.pure_apply] at hqz
      by_cases hzq : z = q
      · simpa [hzq] using hq
      · simp [hzq] at hqz
  | succ T ih =>
      rw [iter_succ, PMF.bind_apply] at hqz
      by_contra hzInv
      apply hqz
      rw [ENNReal.tsum_eq_zero]
      intro a
      by_cases hqa : productivePairJointStop h3 X Y d target q a = 0
      · simp [hqa]
      · have haInv :=
          productivePairJointStop_counterInv_of_apply_ne_zero
            h3 X Y hXY d target q hq a hqa
        have hiaz :
            iter (productivePairJointStop h3 X Y d target) T a z = 0 := by
          by_contra hne
          exact hzInv (ih a haInv hne)
        simp [hiaz]

end Tri.Multi

#print axioms Tri.Multi.samplePairDelta_ne_zero_of_isXInvolving
#print axioms Tri.Multi.productivePairJointCount_map_involving
#print axioms Tri.Multi.productivePairJointCount_map_relevant
#print axioms Tri.Multi.productivePairJoint_iter_counterInv
#print axioms Tri.Multi.productivePairJointStop_iter_counterInv
