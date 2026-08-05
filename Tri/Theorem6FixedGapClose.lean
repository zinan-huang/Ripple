/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Theorem6FixedDecisiveApply

/-!
# Close the fixed activation gap bridge

The terminal radius is used for the square-paying gap `F`.  Twice the global
decisive pool radius is used for the shrink allowance `H`.  The fixed critical
scale occupies less than half of the initial inactive pool, so this `H`
automatically pays the multiplicative shrink condition.
-/

namespace Tri

open scoped ENNReal

noncomputable section

/-- Global radius multiplier appearing in the decisive-to-gap bridge. -/
def theorem6FixedGapCost
    (cStar R : ℕ) : ℕ :=
  60 * theorem6FixedPoolMultiplier *
    lemma19FixedDdec theorem6FixedPostStages
      (4 * R) cStar R

/-- Twice the global radius pays the loss from removing the fixed critical
source scale from the initial inactive pool. -/
def theorem6FixedGapSafety
    (cStar R : ℕ) : ℕ :=
  2 * theorem6FixedGapCost cStar R

/-- Public square-root-sized majority gap for the fixed Theorem 6
specialization. -/
def theorem6FixedPaperGap
    (q n : ℕ) : ℕ :=
  (8 * 17_528_751_390_721) *
      (Nat.sqrt (q * n) + 1) +
    4_278_190_080

/-- Exact affine form of the radius plus the fixed safety gap. -/
theorem theorem6FixedGapSafety_affine
    (R : ℕ) :
    R +
        theorem6FixedGapSafety
          theorem6FixedCStar R =
      17_528_751_390_721 * R +
        4_278_190_080 := by
  norm_num [theorem6FixedGapSafety,
    theorem6FixedGapCost,
    theorem6FixedPoolMultiplier,
    lemma19FixedDdec, theorem6FixedPostStages,
    lemma19FixedHalfDrop, theorem6FixedCStarSq,
    theorem6FixedCStar]
  ring

/-- The square-root envelope on the terminal radius pays the public fixed
majority gap. -/
theorem theorem6FixedGapSafety_le_paperGap
    {R q n : ℕ}
    (hR :
      R ≤ 8 * (Nat.sqrt (q * n) + 1)) :
    R +
        theorem6FixedGapSafety
          theorem6FixedCStar R ≤
      theorem6FixedPaperGap q n := by
  rw [theorem6FixedGapSafety_affine]
  unfold theorem6FixedPaperGap
  calc
    17_528_751_390_721 * R +
          4_278_190_080 ≤
        17_528_751_390_721 *
            (8 * (Nat.sqrt (q * n) + 1)) +
          4_278_190_080 :=
      Nat.add_le_add_right
        (Nat.mul_le_mul_left
          17_528_751_390_721 hR)
        4_278_190_080
    _ =
        (8 * 17_528_751_390_721) *
            (Nat.sqrt (q * n) + 1) +
          4_278_190_080 := by
      ring

/-- The source pool remaining after the fixed critical scale contains at
least half of the initial inactive pool. -/
theorem lemma16To19FixedGapComplement_half
    {n γ cStar a Dlate R19 : ℕ}
    {s : InfectionRevealPhysicalState n}
    (I : InfectionInitialParams s a)
    (O : Lemma16To19FixedPostFacts
      n (theorem6Q n γ) cStar Dlate R19) :
    I.B + I.R ≤
      2 * (lemma16To19FixedGapComplement I O + 1) := by
  have hpost :=
    O.hquarter 0 (by
      norm_num [theorem6FixedPostStages])
  have hscale :=
    O.ha 0 (by
      norm_num [theorem6FixedPostStages])
  rw [O.hscale0] at hpost hscale
  have hgap :=
    lemma16To19FixedGapComplement_spec I O
  have hnu := I.hnu
  have hRB := I.hRB
  omega

/-- The explicit twofold safety radius satisfies the exact gap-shrink
condition for the canonical additive complement. -/
theorem lemma16To19FixedGapShrink_explicit
    {n γ cStar a Dlate R19 : ℕ}
    {s : InfectionRevealPhysicalState n}
    (I : InfectionInitialParams s a)
    (O : Lemma16To19FixedPostFacts
      n (theorem6Q n γ) cStar Dlate R19)
    (K : ℕ) :
    K * (I.B + I.R) ≤
      (2 * K) *
        (lemma16To19FixedGapComplement I O + 1) := by
  calc
    K * (I.B + I.R) ≤
        K *
          (2 * (lemma16To19FixedGapComplement I O + 1)) :=
      Nat.mul_le_mul_left K
        (lemma16To19FixedGapComplement_half I O)
    _ =
        (2 * K) *
          (lemma16To19FixedGapComplement I O + 1) := by
      ring

/-- Complete fixed activation headline under one explicit initial-majority
margin and the remaining scalar construction conditions. -/
theorem lemma16_to_19_fixed_landing_coarse_headline_closed
    {n γ cStar R : ℕ}
    {hn : 0 < n}
    {hcStar : 0 < cStar}
    {s : InfectionRevealPhysicalState n}
    (I : InfectionInitialParams s
      (theorem6InitialScale n γ))
    (hN : 0 < theorem6Q n γ * n)
    (hlarge :
      theorem6FixedCStarSq *
          (theorem6FixedCStarSq + 6) ≤ n)
    (hγ : 2 ≤ γ)
    (hcStar16 : 640 ≤ cStar)
    (hqLarge : 8192 ≤ theorem6Q n γ)
    (S : Theorem6InitialScaleFacts n γ)
    (hbias :
      38 * cStar *
          theorem6InitialRadius
            (theorem6Q n γ)
            (theorem6InitialScale n γ) ≤
        theorem6InitialScale n γ)
    (hfit :
      ∀ j ≤ lemma17FixedStageCount n
          (theorem6InitialScale n γ) S.hpositive,
        76 * cStar *
            lemma17FixedReactionLower n
              (theorem6Q n γ) cStar
              (lemma17FixedScale
                (theorem6InitialScale n γ) j) ≤
          lemma17FixedScale
            (theorem6InitialScale n γ) j)
    (hRlt : R < n)
    (hSq : theorem6Q n γ * n ≤ R ^ 2)
    (hLanding :
      lemma17FixedLandingRho
          (theorem6InitialRadius
            (theorem6Q n γ)
            (theorem6InitialScale n γ))
          (lemma17FixedStageCount n
            (theorem6InitialScale n γ) S.hpositive) ≤
        R)
    (hguard :
      60 *
          lemma19FixedDdec theorem6FixedPostStages
            (4 * R) cStar R ≤
        theorem6FixedCriticalScale n)
    (hfit18 :
      1200 * cStar *
          lemma17FixedReactionLower n
            (theorem6Q n γ) cStar
            (theorem6FixedCriticalScale n) ≤
        7 * theorem6FixedCriticalScale n)
    (hmargin :
      I.R +
          (R + theorem6FixedGapSafety cStar R) ≤
        I.B) :
    terminalFailureMass
        (iter
          (freeze
            (InfectionActivationGapRangeGood n R)
            (infectionStateStep n (by
              rw [theorem6FixedCStar_sq] at hlarge
              omega)))
          ((2 * cStar + 8192) * theorem6Q n γ * n)
          (infectionRevealPhysicalForget s))
        (InfectionActivationGapRangeGood n R)
      ≤ infectionActivationFinalError
          (theorem6Q n γ) := by
  let P :=
    theorem6FixedPrefixFacts
      n γ cStar hN hcStar S hqLarge hbias hfit
  let O :=
    lemma16To19FixedPostFacts_explicit
      n γ cStar
      (theorem6InitialScale n γ)
      (theorem6InitialRadius
        (theorem6Q n γ)
        (theorem6InitialScale n γ))
      R hn
      (le_trans (by norm_num : 2 ≤ 640) hcStar16)
      S.hpositive hlarge P hSq
  have hmajor0 : I.R ≤ I.B := by
    omega
  have hlast :
      lemma17FixedRho
          (theorem6InitialRadius
            (theorem6Q n γ)
            (theorem6InitialScale n γ))
          (lemma17FixedStageCount n
            (theorem6InitialScale n γ) S.hpositive) ≤
        R := by
    unfold lemma17FixedLandingRho at hLanding
    omega
  have hLadderGap :
      I.R +
          lemma17FixedRho
            (theorem6InitialRadius
              (theorem6Q n γ)
              (theorem6InitialScale n γ))
            (lemma17FixedStageCount n
              (theorem6InitialScale n γ) S.hpositive) ≤
        I.B := by
    omega
  have hInitialGap :
      I.R +
          (R + theorem6FixedGapSafety cStar R) ≤
        I.B :=
    hmargin
  have hGapShrink :
      theorem6FixedGapCost cStar R *
            (I.B + I.R) ≤
        theorem6FixedGapSafety cStar R *
          (lemma16To19FixedGapComplement I O + 1) := by
    exact
      lemma16To19FixedGapShrink_explicit I O
        (theorem6FixedGapCost cStar R)
  have hGapQa :
      theorem6Q n γ *
          (theorem6FixedCriticalScale n + 1) ≤
        R ^ 2 := by
    obtain ⟨e, W⟩ :=
      lemma19FixedWindowFacts_of_large n hn hlarge
    have hpost :=
      W.hquarter 0 (by
        norm_num [theorem6FixedPostStages])
    have hscale :=
      W.ha 0 (by
        norm_num [theorem6FixedPostStages])
    rw [W.hscale0] at hpost hscale
    exact
      (Nat.mul_le_mul_left (theorem6Q n γ)
        (by omega)).trans hSq
  exact
    lemma16_to_19_fixed_landing_coarse_headline_complete_of_decisive
      (hn := hn)
      (hcStar := hcStar)
      I hN hlarge hγ hcStar16 hqLarge S hbias hfit
      hRlt hSq hLanding hguard hfit18
      R (theorem6FixedGapSafety cStar R)
      hmajor0 hLadderGap hInitialGap
      (by
        simpa [theorem6FixedGapCost,
          theorem6FixedGapSafety] using hGapShrink)
      hGapQa

end

end Tri

#print axioms Tri.lemma16To19FixedGapComplement_half
#print axioms Tri.lemma16To19FixedGapShrink_explicit
#print axioms Tri.theorem6FixedGapSafety_affine
#print axioms Tri.theorem6FixedGapSafety_le_paperGap
#print axioms
  Tri.lemma16_to_19_fixed_landing_coarse_headline_closed
