/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Lemma16To19Certificates

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
theorem lemma16To19LadderComplement_exists
    {n γ cStar a rho : ℕ}
    {hn : 0 < n}
    {hcStar : 0 < cStar}
    {ha : 0 < a}
    {s : InfectionRevealPhysicalState n}
    (I : InfectionInitialParams s a)
    (P : Lemma17PrefixFacts
      n (theorem6Q n γ) cStar a rho hn hcStar ha) :
    ∃ u : ℕ,
      I.B + I.R =
        u +
            lemma17ScaleWithLanding a
              (lemma17StageCount n a ha)
              (theorem6CriticalScale n)
              (lemma17StageCount n a ha) +
          1 := by
  have hbelow := P.hbelow
  rw [theorem6CStar_sq] at hbelow
  have hscale := P.hscalePredLower
  have hnu := I.hnu
  have hRB := I.hRB
  have hroom :
      lemma17ScaleWithLanding a
            (lemma17StageCount n a ha)
            (theorem6CriticalScale n)
            (lemma17StageCount n a ha) +
          1 ≤
        I.B + I.R := by
    omega
  obtain ⟨u, hu⟩ :=
    Nat.exists_eq_add_of_le hroom
  exact ⟨u, by omega⟩

/-- Canonical additive complement of the last ordinary prefix scale. -/
noncomputable def lemma16To19LadderComplement
    {n γ cStar a rho : ℕ}
    {hn : 0 < n}
    {hcStar : 0 < cStar}
    {ha : 0 < a}
    {s : InfectionRevealPhysicalState n}
    (I : InfectionInitialParams s a)
    (P : Lemma17PrefixFacts
      n (theorem6Q n γ) cStar a rho hn hcStar ha) : ℕ :=
  Classical.choose
    (lemma16To19LadderComplement_exists I P)

theorem lemma16To19LadderComplement_spec
    {n γ cStar a rho : ℕ}
    {hn : 0 < n}
    {hcStar : 0 < cStar}
    {ha : 0 < a}
    {s : InfectionRevealPhysicalState n}
    (I : InfectionInitialParams s a)
    (P : Lemma17PrefixFacts
      n (theorem6Q n γ) cStar a rho hn hcStar ha) :
    I.B + I.R =
      lemma16To19LadderComplement I P +
          lemma17ScaleWithLanding a
            (lemma17StageCount n a ha)
            (theorem6CriticalScale n)
            (lemma17StageCount n a ha) +
        1 :=
  Classical.choose_spec
    (lemma16To19LadderComplement_exists I P)

/-- The fixed critical scale also fits inside the initial inactive pool. -/
theorem lemma16To19GapComplement_exists
    {n γ cStar a Dlate R19 : ℕ}
    {s : InfectionRevealPhysicalState n}
    (I : InfectionInitialParams s a)
    (O : Lemma16To19PostFacts
      n (theorem6Q n γ) cStar Dlate R19) :
    ∃ u : ℕ,
      I.B + I.R =
        u + theorem6CriticalScale n + 1 := by
  have hpost :=
    O.hquarter 0 (by
      norm_num [theorem6PostStages])
  have hscale :=
    O.ha 0 (by
      norm_num [theorem6PostStages])
  rw [O.hscale0] at hpost hscale
  have hnu := I.hnu
  have hRB := I.hRB
  have hroom :
      theorem6CriticalScale n + 1 ≤
        I.B + I.R := by
    omega
  obtain ⟨u, hu⟩ :=
    Nat.exists_eq_add_of_le hroom
  exact ⟨u, by omega⟩

/-- Canonical additive complement of the fixed critical scale. -/
noncomputable def lemma16To19GapComplement
    {n γ cStar a Dlate R19 : ℕ}
    {s : InfectionRevealPhysicalState n}
    (I : InfectionInitialParams s a)
    (O : Lemma16To19PostFacts
      n (theorem6Q n γ) cStar Dlate R19) : ℕ :=
  Classical.choose
    (lemma16To19GapComplement_exists I O)

theorem lemma16To19GapComplement_spec
    {n γ cStar a Dlate R19 : ℕ}
    {s : InfectionRevealPhysicalState n}
    (I : InfectionInitialParams s a)
    (O : Lemma16To19PostFacts
      n (theorem6Q n γ) cStar Dlate R19) :
    I.B + I.R =
      lemma16To19GapComplement I O +
        theorem6CriticalScale n + 1 :=
  Classical.choose_spec
    (lemma16To19GapComplement_exists I O)

/-- Apply the simultaneous fixed certificate assembly with both source-pool
complements chosen canonically. -/
noncomputable def
    lemma16_to_19_critical_landing_coarse_linear_clock_complete_of_poolComplements
    {n γ cStar a rho Dlate R19 Dlabel Mlate targetGap : ℕ}
    {hn : 0 < n}
    {hcStar : 0 < cStar}
    {ha : 0 < a}
    {s : InfectionRevealPhysicalState n}
    (I : InfectionInitialParams s a)
    (ha2 : 2 ≤ a)
    (hlarge :
      theorem6CStarSq *
          (theorem6CStarSq + 6) ≤ n)
    (hγ : 2 ≤ γ)
    (hcStar16 : 640 ≤ cStar)
    (hqLarge : 8192 ≤ theorem6Q n γ)
    (P : Lemma17PrefixFacts
      n (theorem6Q n γ) cStar a rho hn hcStar ha)
    (O : Lemma16To19PostFacts
      n (theorem6Q n γ) cStar Dlate R19)
    (E : Lemma18ParameterFacts
      n (theorem6Q n γ) cStar
      (lemma19Ddec theorem6PostStages
        Dlate cStar R19)
      (lemma17LandingRho rho
        (lemma17StageCount n a ha))
      hn hcStar)
    (T : Lemma16To19LateFacts
      n (theorem6Q n γ) Dlate Dlabel Mlate targetGap) :=
  lemma16_to_19_critical_landing_coarse_linear_clock_complete_of_parameterFacts
    I ha2 hlarge hγ hcStar16 hqLarge P O E T
    (uLadder :=
      lemma16To19LadderComplement I P)
    (uGap :=
      lemma16To19GapComplement I O)
    (hLadderBR :=
      lemma16To19LadderComplement_spec I P)
    (hGapBR :=
      lemma16To19GapComplement_spec I O)

end

end Tri

#print axioms Tri.lemma16To19LadderComplement_exists
#print axioms Tri.lemma16To19LadderComplement_spec
#print axioms Tri.lemma16To19GapComplement_exists
#print axioms Tri.lemma16To19GapComplement_spec
#print axioms
  Tri.lemma16_to_19_critical_landing_coarse_linear_clock_complete_of_poolComplements
