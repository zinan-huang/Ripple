/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.MultiProductiveStageDeadline

/-!
# Count bounds from the involvement clock

Only productive reactions involving `X` can change `count(X)`, and each such
reaction changes it by one.  Consequently the involvement counter controls
both deviations of the current count from its stage-start value.
-/

namespace Tri.Multi

open scoped BigOperators ENNReal

variable {m n : ℕ}

/-- An `X`-involving productive sample changes `count(X)` by exactly one. -/
theorem count_sampleNext_of_isXInvolving
    {c : Config m n} (X : Species m) (t : TripleSample c)
    (ht : IsXInvolvingSample X t) :
    count (sampleNext c t) X = count c X + 1 ∨
      count (sampleNext c t) X + 1 = count c X := by
  obtain ⟨Y, hYX, hfire | hfire⟩ := ht
  · let p : FirePair t := ⟨(X, Y), hfire⟩
    have hclass : classify t = some p :=
      classify_eq_some_of_fire t p
    left
    unfold sampleNext
    rw [hclass]
    exact count_transfer_winner _ _ _ p.2.1 _
  · let p : FirePair t := ⟨(Y, X), hfire⟩
    have hclass : classify t = some p :=
      classify_eq_some_of_fire t p
    right
    have hXpos :
        0 < count c X :=
      count_pos_of_multiplicity_pos t X (by
        rw [p.2.2.2]
        omega)
    unfold sampleNext
    rw [hclass]
    change count (transfer c Y X hfire.1 hXpos) X + 1 = count c X
    rw [count_transfer_loser]
    omega

/-- A productive sample not involving `X` leaves `count(X)` unchanged. -/
theorem count_sampleNext_of_not_isXInvolving
    {c : Config m n} (X : Species m) (t : TripleSample c)
    (ht : ¬ IsXInvolvingSample X t) :
    count (sampleNext c t) X = count c X := by
  classical
  cases hclass : classify t with
  | none =>
      unfold sampleNext
      rw [hclass]
  | some p =>
      have hwinner : p.1.1 ≠ X := by
        intro h
        subst X
        apply ht
        exact ⟨p.1.2, Ne.symm p.2.1, Or.inl p.2⟩
      have hloser : p.1.2 ≠ X := by
        intro h
        subst X
        apply ht
        exact ⟨p.1.1, p.2.1, Or.inr p.2⟩
      have hloserPos :
          0 < count c p.1.2 :=
        count_pos_of_multiplicity_pos t p.1.2 (by
          rw [p.2.2.2]
          omega)
      unfold sampleNext
      rw [hclass]
      exact count_transfer_of_ne c p.1.1 p.1.2 X
        p.2.1 hloserPos (Ne.symm hwinner) (Ne.symm hloser)

/-- Pathwise count envelope carried by the `X`-involvement clock. -/
def ProductiveInvolvingCountInv
    (X : Species m) (x0 : ℕ) (q : Config m n × ℕ) : Prop :=
  count q.1 X ≤ x0 + q.2 ∧ x0 ≤ count q.1 X + q.2

theorem productiveInvolvingCountInv_next
    (X : Species m) (x0 : ℕ) (q : Config m n × ℕ)
    (hq : ProductiveInvolvingCountInv X x0 q)
    (t : TripleSample q.1) :
    ProductiveInvolvingCountInv X x0
      (sampleNext q.1 t,
        if IsXInvolvingSample X t then q.2 + 1 else q.2) := by
  unfold ProductiveInvolvingCountInv at hq ⊢
  by_cases hXt : IsXInvolvingSample X t
  · have hc := count_sampleNext_of_isXInvolving X t hXt
    rcases hc with hc | hc <;> simp only [hXt, if_true] <;> omega
  · have hc := count_sampleNext_of_not_isXInvolving X t hXt
    simp only [hXt, if_false, hc]
    exact hq

/-- One productive involving-count step preserves the count envelope on its
support. -/
theorem productiveInvolvingCount_inv_of_apply_ne_zero
    (h3 : 3 ≤ n) (X : Species m) (x0 : ℕ)
    (q : Config m n × ℕ) (hq : ProductiveInvolvingCountInv X x0 q)
    (z : Config m n × ℕ)
    (hqz : productiveInvolvingCount h3 X q z ≠ 0) :
    ProductiveInvolvingCountInv X x0 z := by
  classical
  by_cases hprod : productiveMass q.1 h3 ≠ 0
  · rw [show productiveInvolvingCount h3 X q =
        (productiveSamplePMF q.1 h3 hprod).map fun t =>
          (sampleNext q.1 t,
            if IsXInvolvingSample X t then q.2 + 1 else q.2) by
        unfold productiveInvolvingCount
        simp [hprod]] at hqz
    rw [PMF.map_apply, Ne, ENNReal.tsum_eq_zero] at hqz
    push Not at hqz
    obtain ⟨t, ht⟩ := hqz
    let zt : Config m n × ℕ :=
      (sampleNext q.1 t,
        if IsXInvolvingSample X t then q.2 + 1 else q.2)
    by_cases hzt : z = zt
    · subst z
      exact productiveInvolvingCountInv_next X x0 q hq t
    · simp [zt, hzt] at ht
  · rw [show productiveInvolvingCount h3 X q = PMF.pure q by
        unfold productiveInvolvingCount
        simp [hprod]] at hqz
    simp only [PMF.pure_apply] at hqz
    by_cases hzq : z = q
    · simpa [hzq] using hq
    · simp [hzq] at hqz

/-- Before the completion-(c) deadline, the count envelope implies both
paper stage count bounds. -/
theorem productiveInvolvingCountInv_bounds_before_target
    (X : Species m) (x0 : ℕ) (q : Config m n × ℕ)
    (hq : ProductiveInvolvingCountInv X x0 q)
    (hk : q.2 < properInvolvingTarget x0) :
    x0 ≤ 2 * count q.1 X ∧ count q.1 X ≤ properStageScale x0 := by
  unfold ProductiveInvolvingCountInv at hq
  unfold properInvolvingTarget at hk
  unfold properStageScale
  omega

/-- The common deadline-stopped involving process preserves the count
envelope on one supported step. -/
theorem productiveInvolvingStageDeadlineStop_inv_of_apply_ne_zero
    (h3 : 3 ≤ n) (X : Species m) (x0 S d target K : ℕ)
    (q : Config m n × ℕ) (hq : ProductiveInvolvingCountInv X x0 q)
    (z : Config m n × ℕ)
    (hqz :
      productiveInvolvingStageDeadlineStop h3 X S d target K q z ≠ 0) :
    ProductiveInvolvingCountInv X x0 z := by
  classical
  unfold productiveInvolvingStageDeadlineStop at hqz
  by_cases hlive :
      HasPairwiseGap q.1 X d ∧ count q.1 X ≤ S ∧
        ¬ HasPairwiseGap q.1 X target ∧ q.2 < K
  · rw [if_pos hlive] at hqz
    exact productiveInvolvingCount_inv_of_apply_ne_zero
      h3 X x0 q hq z hqz
  · rw [if_neg hlive] at hqz
    simp only [PMF.pure_apply] at hqz
    by_cases hzq : z = q
    · simpa [hzq] using hq
    · simp [hzq] at hqz

/-- The count envelope holds on every supported finite path of the common
deadline process. -/
theorem productiveInvolvingStageDeadlineStop_iter_inv
    (h3 : 3 ≤ n) (X : Species m) (x0 S d target K T : ℕ)
    (q z : Config m n × ℕ)
    (hq : ProductiveInvolvingCountInv X x0 q)
    (hqz :
      iter (productiveInvolvingStageDeadlineStop h3 X S d target K)
        T q z ≠ 0) :
    ProductiveInvolvingCountInv X x0 z := by
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
      by_cases hqa :
          productiveInvolvingStageDeadlineStop h3 X S d target K q a = 0
      · simp [hqa]
      · have haInv :=
          productiveInvolvingStageDeadlineStop_inv_of_apply_ne_zero
            h3 X x0 S d target K q hq a hqa
        have hiaz :
            iter (productiveInvolvingStageDeadlineStop
              h3 X S d target K) T a z = 0 := by
          by_contra hne
          exact hzInv (ih a haInv hne)
        simp [hiaz]

end Tri.Multi

#print axioms Tri.Multi.count_sampleNext_of_isXInvolving
#print axioms Tri.Multi.count_sampleNext_of_not_isXInvolving
#print axioms Tri.Multi.productiveInvolvingCount_inv_of_apply_ne_zero
#print axioms Tri.Multi.productiveInvolvingCountInv_bounds_before_target
#print axioms Tri.Multi.productiveInvolvingStageDeadlineStop_iter_inv
