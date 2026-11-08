/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Lemma19GapLadderParameters
import Tri.Lemma19PostWindow
import Tri.Lemma17CriticalLandingTo18

/-!
# Fixed post-critical parameters for the activation route

The fixed seventeen-stage window and the fixed reaction, safety, and reserve
parameters are packaged with the error-envelope hypotheses used by the final
activation headline.
-/

namespace Tri

noncomputable section

/-- All post-critical hypotheses that are supplied by the fixed choices. -/
structure Lemma16To19PostFacts
    (n q cStar Dlate R : ℕ) : Prop where
  hscale0 :
    theorem6PostScale
        (theorem6CriticalScale n) 0 =
      2 * theorem6CriticalScale n
  hgap0 :
    lemma19TargetGap theorem6PostStages
        Dlate cStar R 0 =
      2 * lemma19Ddec theorem6PostStages
        Dlate cStar R
  hdouble :
    ∀ j < theorem6PostStages,
      theorem6PostScale
          (theorem6CriticalScale n) (j + 1) =
        2 * theorem6PostScale
          (theorem6CriticalScale n) j
  ha :
    ∀ j < theorem6PostStages,
      4 ≤ theorem6PostScale
        (theorem6CriticalScale n) j
  hquarter :
    ∀ j < theorem6PostStages,
      4 * theorem6PostScale
          (theorem6CriticalScale n) j ≤ n
  htarget :
    ∀ j < theorem6PostStages,
      2 * theorem6PostScale
          (theorem6CriticalScale n) j ≤ n
  hmean :
    ∀ j < theorem6PostStages,
      (2 * theorem6PostScale
          (theorem6CriticalScale n) j) ^ 3 ≤
        lemma19Reaction
            (theorem6PostScale
              (theorem6CriticalScale n)) j *
          n ^ 2
  hqa :
    ∀ j < theorem6PostStages,
      q * (theorem6PostScale
          (theorem6CriticalScale n) j + 1) ≤
        (lemma19Rho R j) ^ 2
  hlabelRoom :
    ∀ j < theorem6PostStages,
      5 * (theorem6PostScale
          (theorem6CriticalScale n) j + 1) ≤
        n + 1
  hbudget :
    ∀ j < theorem6PostStages,
      lemma19TargetGap theorem6PostStages
            Dlate cStar R (j + 1) +
          (lemma19Rho R j + 1) +
          2 * lemma19Safety cStar R j ≤
        lemma19TargetGap theorem6PostStages
          Dlate cStar R j
  hfinalScale :
    4 ≤ theorem6PostScale
      (theorem6CriticalScale n)
      theorem6PostStages
  hstageRoomFinal :
    theorem6PostScale
          (theorem6CriticalScale n)
          theorem6PostStages + 4 ≤ n
  hquarterFinal :
    n ≤
      4 * theorem6PostScale
        (theorem6CriticalScale n)
        theorem6PostStages
  hfinalGap :
    lemma19TargetGap theorem6PostStages
        Dlate cStar R theorem6PostStages =
      2 * Dlate
  hscaleLeFinal :
    ∀ j ≤ theorem6PostStages,
      theorem6PostScale
          (theorem6CriticalScale n) j ≤
        theorem6PostScale
          (theorem6CriticalScale n)
          theorem6PostStages
  hPostWindow :
    4 * theorem6PostScale
          (theorem6CriticalScale n)
          theorem6PostStages + 7 ≤
      n + 3 * theorem6CriticalScale n
  hPostQaGlobal :
    q * (theorem6PostScale
          (theorem6CriticalScale n)
          theorem6PostStages + 2) ≤
      R ^ 2
  herrorR :
    ∀ j < theorem6PostStages,
      0 <
        lemma19Reaction
          (theorem6PostScale
            (theorem6CriticalScale n)) j
  herrorQa :
    ∀ j < theorem6PostStages,
      q ≤ theorem6PostScale
        (theorem6CriticalScale n) j
  herrorActive :
    ∀ j < theorem6PostStages,
      15 * q ≤
        4 * cStar *
          lemma19Reaction
            (theorem6PostScale
              (theorem6CriticalScale n)) j
  herrorDirection :
    ∀ j < theorem6PostStages,
      3 * q * cStar *
          lemma19Reaction
            (theorem6PostScale
              (theorem6CriticalScale n)) j ≤
        (lemma19Safety cStar R j) ^ 2

/-- The fixed decisive reserve contains the constant post-stage radius, and
the final pool multiplier can therefore serve as the global radius. -/
theorem lemma19Radius_le_global
    (Dlate cStar R : ℕ) :
    R ≤
      60 * theorem6PoolMultiplier *
        lemma19Ddec theorem6PostStages
          Dlate cStar R := by
  have hhalf :
      R ≤ lemma19HalfDrop cStar R := by
    unfold lemma19HalfDrop
    nlinarith
  have hreserve :
      lemma19HalfDrop cStar R ≤
        lemma19Ddec theorem6PostStages
          Dlate cStar R := by
    unfold lemma19Ddec theorem6PostStages
    omega
  have hmult :
      lemma19Ddec theorem6PostStages
          Dlate cStar R ≤
        60 * theorem6PoolMultiplier *
          lemma19Ddec theorem6PostStages
            Dlate cStar R := by
    have hfactor :
        1 ≤ 60 * theorem6PoolMultiplier := by
      norm_num [theorem6PoolMultiplier,
        theorem6CStarSq, theorem6CStar]
    simpa [mul_assoc] using
      Nat.mul_le_mul_right
        (lemma19Ddec theorem6PostStages
          Dlate cStar R) hfactor
  exact hhalf.trans (hreserve.trans hmult)

/-- A terminal-scale radius bound also pays the global post-window radius. -/
theorem lemma19PostQaGlobal
    (n q Dlate cStar R : ℕ)
    (hrootFinal :
      q * (theorem6PostScale
          (theorem6CriticalScale n)
          theorem6PostStages + 2) ≤
        R ^ 2) :
    q * (theorem6PostScale
          (theorem6CriticalScale n)
          theorem6PostStages + 2) ≤
      (60 * theorem6PoolMultiplier *
        lemma19Ddec theorem6PostStages
          Dlate cStar R) ^ 2 := by
  exact hrootFinal.trans
    (Nat.pow_le_pow_left
      (lemma19Radius_le_global Dlate cStar R) 2)

/-- The last ordinary Lemma 17 error scale supplies the base bound for every
fixed post-critical scale. -/
theorem lemma16To19Post_qBase
    (n q P : ℕ)
    (hq : q ≤ P)
    (hbelow : theorem6CStarSq * P < n) :
    q ≤ 2 * theorem6CriticalScale n := by
  obtain ⟨k, hk, hPk⟩ :=
    theorem6CriticalScale_dyadic_gap n P hbelow
  omega

/-- The fixed post-critical certificate follows from one base-scale bound and
one radius bound at the terminal scale. -/
theorem lemma16To19PostFacts_of_large
    (n q cStar Dlate R : ℕ)
    (hn : 0 < n)
    (hlarge :
      theorem6CStarSq *
          (theorem6CStarSq + 6) ≤ n)
    (hcStar : 2 ≤ cStar)
    (hqBase :
      q ≤ 2 * theorem6CriticalScale n)
    (hrootFinal :
      q * (theorem6PostScale
          (theorem6CriticalScale n)
          theorem6PostStages + 2) ≤
        R ^ 2) :
    Lemma16To19PostFacts
      n q cStar Dlate R := by
  obtain ⟨e, W⟩ :=
    lemma19WindowFacts_of_large n hn hlarge
  have hq0 :
      q ≤ theorem6PostScale
        (theorem6CriticalScale n) 0 := by
    rw [W.hscale0]
    exact hqBase
  have hqLive :
      ∀ j < theorem6PostStages,
        q ≤ theorem6PostScale
          (theorem6CriticalScale n) j := by
    intro j hj
    exact common_q_le_scale_of_double
      q theorem6PostStages
      (theorem6PostScale
        (theorem6CriticalScale n))
      hq0 W.hdouble j (by omega)
  have hrootLive :
      ∀ j < theorem6PostStages,
        q * (theorem6PostScale
            (theorem6CriticalScale n) j + 1) ≤
          R ^ 2 := by
    intro j hj
    calc
      q * (theorem6PostScale
            (theorem6CriticalScale n) j + 1)
          ≤ q * (theorem6PostScale
              (theorem6CriticalScale n)
              theorem6PostStages + 1) :=
        Nat.mul_le_mul_left q
          (Nat.add_le_add_right
            (W.hmonotone j (by omega)) 1)
      _ ≤ q * (theorem6PostScale
              (theorem6CriticalScale n)
              theorem6PostStages + 2) :=
        Nat.mul_le_mul_left q (by omega)
      _ ≤ R ^ 2 := hrootFinal
  have P :=
    lemma19ParameterFacts
      n q cStar theorem6PostStages
      Dlate R
      (theorem6PostScale
        (theorem6CriticalScale n))
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

#print axioms Tri.lemma16To19PostFacts_of_large
#print axioms Tri.lemma19Radius_le_global
#print axioms Tri.lemma19PostQaGlobal
#print axioms Tri.lemma16To19Post_qBase
