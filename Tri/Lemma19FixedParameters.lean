/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Lemma16To19CorrectedError

/-!
# Fixed parameters for the positive-gap ladder

A constant label radius is sufficient for the current Lemma 19 ladder
interface.  This file chooses the reaction and safety parameters explicitly
and constructs the decreasing gap reserve by structural recursion, without
natural-number subtraction.
-/

namespace Tri

noncomputable section

/-- The reverse linear schedule `base + (m - j) * step`, implemented without
natural-number subtraction.  It remains at `base` past the diagonal. -/
def reverseLinearReserve (step base : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => base
  | m + 1, 0 =>
      reverseLinearReserve step base m 0 + step
  | m + 1, j + 1 =>
      reverseLinearReserve step base m j

@[simp] theorem reverseLinearReserve_zero
    (step base m : ℕ) :
    reverseLinearReserve step base m 0 =
      base + m * step := by
  induction m with
  | zero =>
      simp [reverseLinearReserve]
  | succ m ih =>
      rw [reverseLinearReserve, ih]
      ring

@[simp] theorem reverseLinearReserve_diag
    (step base m : ℕ) :
    reverseLinearReserve step base m m = base := by
  induction m with
  | zero =>
      simp [reverseLinearReserve]
  | succ m ih =>
      simpa [reverseLinearReserve] using ih

theorem reverseLinearReserve_step
    (step base m j : ℕ)
    (hj : j < m) :
    reverseLinearReserve step base m j =
      reverseLinearReserve step base m (j + 1) +
        step := by
  induction m generalizing j with
  | zero =>
      omega
  | succ m ih =>
      cases j with
      | zero =>
          simp [reverseLinearReserve]
      | succ j =>
          simpa [reverseLinearReserve] using
            ih j (by omega)

/-- Constant label radius for all positive-gap rungs. -/
def lemma19FixedRho (R : ℕ) (_j : ℕ) : ℕ :=
  R

/-- The smallest simple reaction parameter paying both the cubic mean and
the common exponential envelope. -/
def lemma19FixedReaction
    (scale : ℕ → ℕ) (j : ℕ) : ℕ :=
  2 * scale j

/-- Safety allowance paying the reaction-direction error. -/
def lemma19FixedSafety
    (cStar R : ℕ) (_j : ℕ) : ℕ :=
  2 * cStar * R

/-- Half of the deliberately even reserve drop at one rung. -/
def lemma19FixedHalfDrop
    (cStar R : ℕ) : ℕ :=
  (4 * cStar + 1) * R + 1

/-- An even reserve drop dominating the exact label and safety cost. -/
def lemma19FixedDrop
    (cStar R : ℕ) : ℕ :=
  2 * lemma19FixedHalfDrop cStar R

/-- Initial decisive reserve induced by `m` positive-gap rungs. -/
def lemma19FixedDdec
    (m Dlate cStar R : ℕ) : ℕ :=
  Dlate + m * lemma19FixedHalfDrop cStar R

/-- Reverse gap schedule from twice the decisive reserve to twice the late
reserve. -/
def lemma19FixedTargetGap
    (m Dlate cStar R j : ℕ) : ℕ :=
  reverseLinearReserve
    (lemma19FixedDrop cStar R) (2 * Dlate) m j

theorem lemma19FixedTargetGap_zero
    (m Dlate cStar R : ℕ) :
    lemma19FixedTargetGap m Dlate cStar R 0 =
      2 * lemma19FixedDdec m Dlate cStar R := by
  rw [lemma19FixedTargetGap,
    reverseLinearReserve_zero]
  unfold lemma19FixedDrop lemma19FixedDdec
  ring

theorem lemma19FixedTargetGap_final
    (m Dlate cStar R : ℕ) :
    lemma19FixedTargetGap m Dlate cStar R m =
      2 * Dlate := by
  exact reverseLinearReserve_diag _ _ _

theorem lemma19FixedTargetGap_budget
    (m Dlate cStar R j : ℕ)
    (hj : j < m) :
    lemma19FixedTargetGap
          m Dlate cStar R (j + 1) +
          (lemma19FixedRho R j + 1) +
          2 * lemma19FixedSafety cStar R j
      ≤ lemma19FixedTargetGap
          m Dlate cStar R j := by
  simp only [lemma19FixedTargetGap]
  rw [reverseLinearReserve_step _ _ _ _ hj]
  have hcost :
      (lemma19FixedRho R j + 1) +
          2 * lemma19FixedSafety cStar R j =
        lemma19FixedHalfDrop cStar R := by
    unfold lemma19FixedRho lemma19FixedSafety
      lemma19FixedHalfDrop
    ring
  have hhalf :
      lemma19FixedHalfDrop cStar R ≤
        lemma19FixedDrop cStar R := by
    unfold lemma19FixedDrop
    omega
  calc
    reverseLinearReserve
            (lemma19FixedDrop cStar R)
            (2 * Dlate) m (j + 1) +
          (lemma19FixedRho R j + 1) +
          2 * lemma19FixedSafety cStar R j =
        reverseLinearReserve
            (lemma19FixedDrop cStar R)
            (2 * Dlate) m (j + 1) +
          ((lemma19FixedRho R j + 1) +
            2 * lemma19FixedSafety cStar R j) := by
      ring
    _ =
        reverseLinearReserve
            (lemma19FixedDrop cStar R)
            (2 * Dlate) m (j + 1) +
          lemma19FixedHalfDrop cStar R := by
      rw [hcost]
    _ ≤
        reverseLinearReserve
            (lemma19FixedDrop cStar R)
            (2 * Dlate) m (j + 1) +
          lemma19FixedDrop cStar R :=
      Nat.add_le_add_left hhalf _

theorem lemma19FixedReaction_pos
    (scale : ℕ → ℕ) (j : ℕ)
    (ha : 0 < scale j) :
    0 < lemma19FixedReaction scale j := by
  unfold lemma19FixedReaction
  omega

theorem lemma19FixedReaction_mean
    (n : ℕ) (scale : ℕ → ℕ) (j : ℕ)
    (htarget : 2 * scale j ≤ n) :
    (2 * scale j) ^ 3 ≤
      lemma19FixedReaction scale j * n ^ 2 := by
  have hsquare :
      (2 * scale j) ^ 2 ≤ n ^ 2 :=
    Nat.pow_le_pow_left htarget 2
  unfold lemma19FixedReaction
  calc
    (2 * scale j) ^ 3 =
        (2 * scale j) * (2 * scale j) ^ 2 := by
      ring
    _ ≤ (2 * scale j) * n ^ 2 :=
      Nat.mul_le_mul_left (2 * scale j) hsquare

theorem lemma19FixedReaction_active
    (q cStar : ℕ) (scale : ℕ → ℕ) (j : ℕ)
    (hcStar : 2 ≤ cStar)
    (hq : q ≤ scale j) :
    15 * q ≤
      4 * cStar *
        lemma19FixedReaction scale j := by
  have h15 : 15 * q ≤ 15 * scale j :=
    Nat.mul_le_mul_left 15 hq
  have h16 : 15 * scale j ≤ 16 * scale j := by
    omega
  have hc : 16 ≤ 8 * cStar := by
    omega
  have hca :
      16 * scale j ≤ (8 * cStar) * scale j :=
    Nat.mul_le_mul_right (scale j) hc
  unfold lemma19FixedReaction
  calc
    15 * q ≤ 15 * scale j := h15
    _ ≤ 16 * scale j := h16
    _ ≤ (8 * cStar) * scale j := hca
    _ = 4 * cStar * (2 * scale j) := by
      ring

theorem lemma19FixedSafety_direction
    (q cStar R : ℕ) (scale : ℕ → ℕ) (j : ℕ)
    (hcStar : 2 ≤ cStar)
    (hroot :
      q * (scale j + 1) ≤ R ^ 2) :
    3 * q * cStar *
          lemma19FixedReaction scale j
      ≤ (lemma19FixedSafety cStar R j) ^ 2 := by
  have hqa :
      q * scale j ≤ q * (scale j + 1) :=
    Nat.mul_le_mul_left q (by omega)
  have hscaled :
      6 * cStar * (q * scale j) ≤
        6 * cStar * R ^ 2 :=
    Nat.mul_le_mul_left (6 * cStar)
      (hqa.trans hroot)
  have hc : 6 * cStar ≤ 4 * cStar * cStar := by
    nlinarith
  have hcScaled :
      6 * cStar * R ^ 2 ≤
        (4 * cStar * cStar) * R ^ 2 :=
    Nat.mul_le_mul_right (R ^ 2) hc
  unfold lemma19FixedReaction lemma19FixedSafety
  calc
    3 * q * cStar * (2 * scale j) =
        6 * cStar * (q * scale j) := by
      ring
    _ ≤ 6 * cStar * R ^ 2 := hscaled
    _ ≤ (4 * cStar * cStar) * R ^ 2 :=
      hcScaled
    _ = (2 * cStar * R) ^ 2 := by
      ring

/-- The semantic and exponential-envelope obligations supplied by the fixed
reaction, safety, and reverse-reserve choices. -/
structure Lemma19FixedParameterFacts
    (n q cStar m Dlate R : ℕ)
    (scale : ℕ → ℕ) : Prop where
  hr :
    ∀ j < m,
      0 < lemma19FixedReaction scale j
  hmean :
    ∀ j < m,
      (2 * scale j) ^ 3 ≤
        lemma19FixedReaction scale j * n ^ 2
  hqa :
    ∀ j < m,
      q * (scale j + 1) ≤
        (lemma19FixedRho R j) ^ 2
  hgap0 :
    lemma19FixedTargetGap
        m Dlate cStar R 0 =
      2 * lemma19FixedDdec
        m Dlate cStar R
  hbudget :
    ∀ j < m,
      lemma19FixedTargetGap
            m Dlate cStar R (j + 1) +
            (lemma19FixedRho R j + 1) +
            2 * lemma19FixedSafety cStar R j
        ≤ lemma19FixedTargetGap
            m Dlate cStar R j
  hfinalGap :
    lemma19FixedTargetGap
        m Dlate cStar R m =
      2 * Dlate
  hactive :
    ∀ j < m,
      15 * q ≤
        4 * cStar *
          lemma19FixedReaction scale j
  hdirection :
    ∀ j < m,
      3 * q * cStar *
          lemma19FixedReaction scale j
        ≤ (lemma19FixedSafety cStar R j) ^ 2

theorem lemma19FixedParameterFacts
    (n q cStar m Dlate R : ℕ)
    (scale : ℕ → ℕ)
    (hcStar : 2 ≤ cStar)
    (ha : ∀ j < m, 0 < scale j)
    (htarget :
      ∀ j < m, 2 * scale j ≤ n)
    (hq : ∀ j < m, q ≤ scale j)
    (hroot :
      ∀ j < m,
        q * (scale j + 1) ≤ R ^ 2) :
    Lemma19FixedParameterFacts
      n q cStar m Dlate R scale := by
  refine
    { hr := ?_
      hmean := ?_
      hqa := ?_
      hgap0 :=
        lemma19FixedTargetGap_zero _ _ _ _
      hbudget := ?_
      hfinalGap :=
        lemma19FixedTargetGap_final _ _ _ _
      hactive := ?_
      hdirection := ?_ }
  · intro j hj
    exact lemma19FixedReaction_pos
      scale j (ha j hj)
  · intro j hj
    exact lemma19FixedReaction_mean
      n scale j (htarget j hj)
  · intro j hj
    simpa [lemma19FixedRho] using hroot j hj
  · intro j hj
    exact lemma19FixedTargetGap_budget
      m Dlate cStar R j hj
  · intro j hj
    exact lemma19FixedReaction_active
      q cStar scale j hcStar (hq j hj)
  · intro j hj
    exact lemma19FixedSafety_direction
      q cStar R scale j hcStar (hroot j hj)

end

end Tri

#print axioms Tri.reverseLinearReserve_zero
#print axioms Tri.reverseLinearReserve_diag
#print axioms Tri.reverseLinearReserve_step
#print axioms Tri.lemma19FixedTargetGap_zero
#print axioms Tri.lemma19FixedTargetGap_final
#print axioms Tri.lemma19FixedTargetGap_budget
#print axioms Tri.lemma19FixedReaction_mean
#print axioms Tri.lemma19FixedReaction_active
#print axioms Tri.lemma19FixedSafety_direction
#print axioms Tri.lemma19FixedParameterFacts
