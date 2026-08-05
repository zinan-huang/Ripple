/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Lemma16To19FixedMasterApply

/-!
# Additive complements for the fixed activation bridges

The two source-pool complements are chosen from proved room inequalities.
Their public specifications use only addition; no truncated natural
subtraction is exposed.
-/

namespace Tri

noncomputable section

/-- The last ordinary Lemma 17 scale fits strictly inside the initial inactive
pool, so it has an additive complement there. -/
theorem lemma16To19FixedLadderComplement_exists
    {n γ cStar a rho : ℕ}
    {hn : 0 < n}
    {hcStar : 0 < cStar}
    {ha : 0 < a}
    {s : InfectionRevealPhysicalState n}
    (I : InfectionInitialParams s a)
    (P : Lemma17FixedPrefixFacts
      n (theorem6Q n γ) cStar a rho hn hcStar ha) :
    ∃ u : ℕ,
      I.B + I.R =
        u +
            lemma17FixedScaleWithLanding a
              (lemma17FixedStageCount n a ha)
              (theorem6FixedCriticalScale n)
              (lemma17FixedStageCount n a ha) +
          1 := by
  have hbelow := P.hbelow
  rw [theorem6FixedCStar_sq] at hbelow
  have hscale := P.hscalePredLower
  have hnu := I.hnu
  have hRB := I.hRB
  have hroom :
      lemma17FixedScaleWithLanding a
            (lemma17FixedStageCount n a ha)
            (theorem6FixedCriticalScale n)
            (lemma17FixedStageCount n a ha) +
          1 ≤
        I.B + I.R := by
    omega
  obtain ⟨u, hu⟩ :=
    Nat.exists_eq_add_of_le hroom
  exact ⟨u, by omega⟩

/-- Canonical additive complement of the last ordinary prefix scale. -/
noncomputable def lemma16To19FixedLadderComplement
    {n γ cStar a rho : ℕ}
    {hn : 0 < n}
    {hcStar : 0 < cStar}
    {ha : 0 < a}
    {s : InfectionRevealPhysicalState n}
    (I : InfectionInitialParams s a)
    (P : Lemma17FixedPrefixFacts
      n (theorem6Q n γ) cStar a rho hn hcStar ha) : ℕ :=
  Classical.choose
    (lemma16To19FixedLadderComplement_exists I P)

theorem lemma16To19FixedLadderComplement_spec
    {n γ cStar a rho : ℕ}
    {hn : 0 < n}
    {hcStar : 0 < cStar}
    {ha : 0 < a}
    {s : InfectionRevealPhysicalState n}
    (I : InfectionInitialParams s a)
    (P : Lemma17FixedPrefixFacts
      n (theorem6Q n γ) cStar a rho hn hcStar ha) :
    I.B + I.R =
      lemma16To19FixedLadderComplement I P +
          lemma17FixedScaleWithLanding a
            (lemma17FixedStageCount n a ha)
            (theorem6FixedCriticalScale n)
            (lemma17FixedStageCount n a ha) +
        1 :=
  Classical.choose_spec
    (lemma16To19FixedLadderComplement_exists I P)

/-- The fixed critical scale also fits inside the initial inactive pool. -/
theorem lemma16To19FixedGapComplement_exists
    {n γ cStar a Dlate R19 : ℕ}
    {s : InfectionRevealPhysicalState n}
    (I : InfectionInitialParams s a)
    (O : Lemma16To19FixedPostFacts
      n (theorem6Q n γ) cStar Dlate R19) :
    ∃ u : ℕ,
      I.B + I.R =
        u + theorem6FixedCriticalScale n + 1 := by
  have hpost :=
    O.hquarter 0 (by
      norm_num [theorem6FixedPostStages])
  have hscale :=
    O.ha 0 (by
      norm_num [theorem6FixedPostStages])
  rw [O.hscale0] at hpost hscale
  have hnu := I.hnu
  have hRB := I.hRB
  have hroom :
      theorem6FixedCriticalScale n + 1 ≤
        I.B + I.R := by
    omega
  obtain ⟨u, hu⟩ :=
    Nat.exists_eq_add_of_le hroom
  exact ⟨u, by omega⟩

/-- Canonical additive complement of the fixed critical scale. -/
noncomputable def lemma16To19FixedGapComplement
    {n γ cStar a Dlate R19 : ℕ}
    {s : InfectionRevealPhysicalState n}
    (I : InfectionInitialParams s a)
    (O : Lemma16To19FixedPostFacts
      n (theorem6Q n γ) cStar Dlate R19) : ℕ :=
  Classical.choose
    (lemma16To19FixedGapComplement_exists I O)

theorem lemma16To19FixedGapComplement_spec
    {n γ cStar a Dlate R19 : ℕ}
    {s : InfectionRevealPhysicalState n}
    (I : InfectionInitialParams s a)
    (O : Lemma16To19FixedPostFacts
      n (theorem6Q n γ) cStar Dlate R19) :
    I.B + I.R =
      lemma16To19FixedGapComplement I O +
        theorem6FixedCriticalScale n + 1 :=
  Classical.choose_spec
    (lemma16To19FixedGapComplement_exists I O)

/-- Apply the simultaneous fixed certificate assembly with both source-pool
complements chosen canonically. -/
noncomputable def
    lemma16_to_19_fixed_landing_coarse_headline_complete_of_bridge
    {n γ cStar a rho Dlate R19 Dlabel Mlate targetGap : ℕ}
    {hn : 0 < n}
    {hcStar : 0 < cStar}
    {ha : 0 < a}
    {s : InfectionRevealPhysicalState n}
    (I : InfectionInitialParams s a)
    (ha2 : 2 ≤ a)
    (hlarge :
      theorem6FixedCStarSq *
          (theorem6FixedCStarSq + 6) ≤ n)
    (hγ : 2 ≤ γ)
    (hcStar16 : 640 ≤ cStar)
    (hqLarge : 8192 ≤ theorem6Q n γ)
    (P : Lemma17FixedPrefixFacts
      n (theorem6Q n γ) cStar a rho hn hcStar ha)
    (O : Lemma16To19FixedPostFacts
      n (theorem6Q n γ) cStar Dlate R19)
    (E : Lemma18FixedParameterFacts
      n (theorem6Q n γ) cStar
      (lemma19FixedDdec theorem6FixedPostStages
        Dlate cStar R19)
      (lemma17FixedLandingRho rho
        (lemma17FixedStageCount n a ha))
      hn hcStar)
    (T : Lemma16To19FixedLateFacts
      n (theorem6Q n γ) Dlate Dlabel Mlate targetGap) :=
  lemma16_to_19_fixed_landing_coarse_headline_complete_of_fixedFacts
    I ha2 hlarge hγ hcStar16 hqLarge P O E T
    (uLadder :=
      lemma16To19FixedLadderComplement I P)
    (uGap :=
      lemma16To19FixedGapComplement I O)
    (hLadderBR :=
      lemma16To19FixedLadderComplement_spec I P)
    (hGapBR :=
      lemma16To19FixedGapComplement_spec I O)

end

end Tri

#print axioms Tri.lemma16To19FixedLadderComplement_exists
#print axioms Tri.lemma16To19FixedLadderComplement_spec
#print axioms Tri.lemma16To19FixedGapComplement_exists
#print axioms Tri.lemma16To19FixedGapComplement_spec
#print axioms
  Tri.lemma16_to_19_fixed_landing_coarse_headline_complete_of_bridge
