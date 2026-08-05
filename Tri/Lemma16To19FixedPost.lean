/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Lemma19FixedParameters
import Tri.Lemma19FixedWindow
import Tri.Lemma17FixedLandingTo18

/-!
# Fixed post-critical parameters for the activation route

The fixed seventeen-stage window and the fixed reaction, safety, and reserve
parameters are packaged with the error-envelope hypotheses used by the final
activation headline.
-/

namespace Tri

noncomputable section

/-- All post-critical hypotheses that are supplied by the fixed choices. -/
structure Lemma16To19FixedPostFacts
    (n q cStar Dlate R : ℕ) : Prop where
  hscale0 :
    theorem6FixedPostScale
        (theorem6FixedCriticalScale n) 0 =
      2 * theorem6FixedCriticalScale n
  hgap0 :
    lemma19FixedTargetGap theorem6FixedPostStages
        Dlate cStar R 0 =
      2 * lemma19FixedDdec theorem6FixedPostStages
        Dlate cStar R
  hdouble :
    ∀ j < theorem6FixedPostStages,
      theorem6FixedPostScale
          (theorem6FixedCriticalScale n) (j + 1) =
        2 * theorem6FixedPostScale
          (theorem6FixedCriticalScale n) j
  ha :
    ∀ j < theorem6FixedPostStages,
      4 ≤ theorem6FixedPostScale
        (theorem6FixedCriticalScale n) j
  hquarter :
    ∀ j < theorem6FixedPostStages,
      4 * theorem6FixedPostScale
          (theorem6FixedCriticalScale n) j ≤ n
  htarget :
    ∀ j < theorem6FixedPostStages,
      2 * theorem6FixedPostScale
          (theorem6FixedCriticalScale n) j ≤ n
  hmean :
    ∀ j < theorem6FixedPostStages,
      (2 * theorem6FixedPostScale
          (theorem6FixedCriticalScale n) j) ^ 3 ≤
        lemma19FixedReaction
            (theorem6FixedPostScale
              (theorem6FixedCriticalScale n)) j *
          n ^ 2
  hqa :
    ∀ j < theorem6FixedPostStages,
      q * (theorem6FixedPostScale
          (theorem6FixedCriticalScale n) j + 1) ≤
        (lemma19FixedRho R j) ^ 2
  hlabelRoom :
    ∀ j < theorem6FixedPostStages,
      5 * (theorem6FixedPostScale
          (theorem6FixedCriticalScale n) j + 1) ≤
        n + 1
  hbudget :
    ∀ j < theorem6FixedPostStages,
      lemma19FixedTargetGap theorem6FixedPostStages
            Dlate cStar R (j + 1) +
          (lemma19FixedRho R j + 1) +
          2 * lemma19FixedSafety cStar R j ≤
        lemma19FixedTargetGap theorem6FixedPostStages
          Dlate cStar R j
  hfinalScale :
    4 ≤ theorem6FixedPostScale
      (theorem6FixedCriticalScale n)
      theorem6FixedPostStages
  hstageRoomFinal :
    theorem6FixedPostScale
          (theorem6FixedCriticalScale n)
          theorem6FixedPostStages + 4 ≤ n
  hquarterFinal :
    n ≤
      4 * theorem6FixedPostScale
        (theorem6FixedCriticalScale n)
        theorem6FixedPostStages
  hfinalGap :
    lemma19FixedTargetGap theorem6FixedPostStages
        Dlate cStar R theorem6FixedPostStages =
      2 * Dlate
  hscaleLeFinal :
    ∀ j ≤ theorem6FixedPostStages,
      theorem6FixedPostScale
          (theorem6FixedCriticalScale n) j ≤
        theorem6FixedPostScale
          (theorem6FixedCriticalScale n)
          theorem6FixedPostStages
  hPostWindow :
    4 * theorem6FixedPostScale
          (theorem6FixedCriticalScale n)
          theorem6FixedPostStages + 7 ≤
      n + 3 * theorem6FixedCriticalScale n
  hPostQaGlobal :
    q * (theorem6FixedPostScale
          (theorem6FixedCriticalScale n)
          theorem6FixedPostStages + 2) ≤
      R ^ 2
  herrorR :
    ∀ j < theorem6FixedPostStages,
      0 <
        lemma19FixedReaction
          (theorem6FixedPostScale
            (theorem6FixedCriticalScale n)) j
  herrorQa :
    ∀ j < theorem6FixedPostStages,
      q ≤ theorem6FixedPostScale
        (theorem6FixedCriticalScale n) j
  herrorActive :
    ∀ j < theorem6FixedPostStages,
      15 * q ≤
        4 * cStar *
          lemma19FixedReaction
            (theorem6FixedPostScale
              (theorem6FixedCriticalScale n)) j
  herrorDirection :
    ∀ j < theorem6FixedPostStages,
      3 * q * cStar *
          lemma19FixedReaction
            (theorem6FixedPostScale
              (theorem6FixedCriticalScale n)) j ≤
        (lemma19FixedSafety cStar R j) ^ 2

/-- The fixed decisive reserve contains the constant post-stage radius, and
the final pool multiplier can therefore serve as the global radius. -/
theorem lemma19FixedRadius_le_global
    (Dlate cStar R : ℕ) :
    R ≤
      60 * theorem6FixedPoolMultiplier *
        lemma19FixedDdec theorem6FixedPostStages
          Dlate cStar R := by
  have hhalf :
      R ≤ lemma19FixedHalfDrop cStar R := by
    unfold lemma19FixedHalfDrop
    nlinarith
  have hreserve :
      lemma19FixedHalfDrop cStar R ≤
        lemma19FixedDdec theorem6FixedPostStages
          Dlate cStar R := by
    unfold lemma19FixedDdec theorem6FixedPostStages
    omega
  have hmult :
      lemma19FixedDdec theorem6FixedPostStages
          Dlate cStar R ≤
        60 * theorem6FixedPoolMultiplier *
          lemma19FixedDdec theorem6FixedPostStages
            Dlate cStar R := by
    have hfactor :
        1 ≤ 60 * theorem6FixedPoolMultiplier := by
      norm_num [theorem6FixedPoolMultiplier,
        theorem6FixedCStarSq, theorem6FixedCStar]
    simpa [mul_assoc] using
      Nat.mul_le_mul_right
        (lemma19FixedDdec theorem6FixedPostStages
          Dlate cStar R) hfactor
  exact hhalf.trans (hreserve.trans hmult)

/-- A terminal-scale radius bound also pays the global post-window radius. -/
theorem lemma19FixedPostQaGlobal
    (n q Dlate cStar R : ℕ)
    (hrootFinal :
      q * (theorem6FixedPostScale
          (theorem6FixedCriticalScale n)
          theorem6FixedPostStages + 2) ≤
        R ^ 2) :
    q * (theorem6FixedPostScale
          (theorem6FixedCriticalScale n)
          theorem6FixedPostStages + 2) ≤
      (60 * theorem6FixedPoolMultiplier *
        lemma19FixedDdec theorem6FixedPostStages
          Dlate cStar R) ^ 2 := by
  exact hrootFinal.trans
    (Nat.pow_le_pow_left
      (lemma19FixedRadius_le_global Dlate cStar R) 2)

/-- The last ordinary Lemma 17 error scale supplies the base bound for every
fixed post-critical scale. -/
theorem lemma16To19FixedPost_qBase
    (n q P : ℕ)
    (hq : q ≤ P)
    (hbelow : theorem6FixedCStarSq * P < n) :
    q ≤ 2 * theorem6FixedCriticalScale n := by
  obtain ⟨k, hk, hPk⟩ :=
    theorem6FixedCriticalScale_dyadic_gap n P hbelow
  omega

/-- The fixed post-critical certificate follows from one base-scale bound and
one radius bound at the terminal scale. -/
theorem lemma16To19FixedPostFacts_of_large
    (n q cStar Dlate R : ℕ)
    (hn : 0 < n)
    (hlarge :
      theorem6FixedCStarSq *
          (theorem6FixedCStarSq + 6) ≤ n)
    (hcStar : 2 ≤ cStar)
    (hqBase :
      q ≤ 2 * theorem6FixedCriticalScale n)
    (hrootFinal :
      q * (theorem6FixedPostScale
          (theorem6FixedCriticalScale n)
          theorem6FixedPostStages + 2) ≤
        R ^ 2) :
    Lemma16To19FixedPostFacts
      n q cStar Dlate R := by
  obtain ⟨e, W⟩ :=
    lemma19FixedWindowFacts_of_large n hn hlarge
  have hq0 :
      q ≤ theorem6FixedPostScale
        (theorem6FixedCriticalScale n) 0 := by
    rw [W.hscale0]
    exact hqBase
  have hqLive :
      ∀ j < theorem6FixedPostStages,
        q ≤ theorem6FixedPostScale
          (theorem6FixedCriticalScale n) j := by
    intro j hj
    exact common_q_le_scale_of_double
      q theorem6FixedPostStages
      (theorem6FixedPostScale
        (theorem6FixedCriticalScale n))
      hq0 W.hdouble j (by omega)
  have hrootLive :
      ∀ j < theorem6FixedPostStages,
        q * (theorem6FixedPostScale
            (theorem6FixedCriticalScale n) j + 1) ≤
          R ^ 2 := by
    intro j hj
    calc
      q * (theorem6FixedPostScale
            (theorem6FixedCriticalScale n) j + 1)
          ≤ q * (theorem6FixedPostScale
              (theorem6FixedCriticalScale n)
              theorem6FixedPostStages + 1) :=
        Nat.mul_le_mul_left q
          (Nat.add_le_add_right
            (W.hmonotone j (by omega)) 1)
      _ ≤ q * (theorem6FixedPostScale
              (theorem6FixedCriticalScale n)
              theorem6FixedPostStages + 2) :=
        Nat.mul_le_mul_left q (by omega)
      _ ≤ R ^ 2 := hrootFinal
  have P :=
    lemma19FixedParameterFacts
      n q cStar theorem6FixedPostStages
      Dlate R
      (theorem6FixedPostScale
        (theorem6FixedCriticalScale n))
      hcStar
      (by
        intro j hj
        exact lt_of_lt_of_le (by omega) (W.ha j hj))
      W.htarget hqLive hrootLive
  exact
    { hscale0 := W.hscale0
      hgap0 := P.hgap0
      hdouble := W.hdouble
      ha := W.ha
      hquarter := W.hquarter
      htarget := W.htarget
      hmean := P.hmean
      hqa := P.hqa
      hlabelRoom := W.hlabelRoom
      hbudget := P.hbudget
      hfinalScale := W.hfinal
      hstageRoomFinal := W.hstageRoomFinal
      hquarterFinal := W.hquarterFinal
      hfinalGap := P.hfinalGap
      hscaleLeFinal := W.hmonotone
      hPostWindow := W.hPostWindow
      hPostQaGlobal := hrootFinal
      herrorR := P.hr
      herrorQa := hqLive
      herrorActive := P.hactive
      herrorDirection := P.hdirection }

end

end Tri

#print axioms Tri.lemma16To19FixedPostFacts_of_large
#print axioms Tri.lemma19FixedRadius_le_global
#print axioms Tri.lemma19FixedPostQaGlobal
#print axioms Tri.lemma16To19FixedPost_qBase
