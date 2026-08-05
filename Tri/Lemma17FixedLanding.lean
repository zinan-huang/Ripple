/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Lemma17CustomLanding
import Tri.Lemma19FixedWindow

/-!
# Landing at the fixed critical scale

The least fixed-square multiple lies between the last dyadic predecessor and
its double.  This file records that bracket, the additive landing witness,
and the population-room inequalities used by the custom final Lemma 17
stage.
-/

namespace Tri

open scoped ENNReal

noncomputable section

/-- Minimality of the fixed critical scale against any supplied cover. -/
theorem theorem6FixedCriticalScale_le
    (n a : ℕ)
    (ha : n ≤ theorem6FixedCStarSq * a) :
    theorem6FixedCriticalScale n ≤ a := by
  exact Nat.find_min'
    (theorem6FixedCriticalScale_exists n) ha

/-- A dyadic predecessor bracket passes to the least fixed critical scale. -/
theorem theorem6FixedCriticalScale_between_dyadic
    (n P : ℕ)
    (hbelow : theorem6FixedCStarSq * P < n)
    (habove : n ≤ theorem6FixedCStarSq * (2 * P)) :
    P < theorem6FixedCriticalScale n ∧
      theorem6FixedCriticalScale n ≤ 2 * P := by
  constructor
  · by_contra hnot
    have hSP :
        theorem6FixedCriticalScale n ≤ P := by
      omega
    have hcover :=
      theorem6FixedCriticalScale_spec n
    have hmul :
        theorem6FixedCStarSq *
            theorem6FixedCriticalScale n ≤
          theorem6FixedCStarSq * P :=
      Nat.mul_le_mul_left theorem6FixedCStarSq hSP
    omega
  · exact theorem6FixedCriticalScale_le
      n (2 * P) habove

/-- The strict left bracket gives a positive additive landing gap. -/
theorem theorem6FixedCriticalScale_dyadic_gap
    (n P : ℕ)
    (hbelow : theorem6FixedCStarSq * P < n) :
    ∃ k,
      0 < k ∧
      P + k = theorem6FixedCriticalScale n := by
  have hlt :
      P < theorem6FixedCriticalScale n := by
    by_contra hnot
    have hSP :
        theorem6FixedCriticalScale n ≤ P := by
      omega
    have hcover :=
      theorem6FixedCriticalScale_spec n
    have hmul :
        theorem6FixedCStarSq *
            theorem6FixedCriticalScale n ≤
          theorem6FixedCStarSq * P :=
      Nat.mul_le_mul_left theorem6FixedCStarSq hSP
    omega
  obtain ⟨k, hk⟩ :=
    Nat.exists_eq_add_of_le hlt.le
  exact ⟨k, by omega, hk.symm⟩

/-- Arithmetic obligations for the custom edge from a dyadic predecessor to
the fixed critical scale. -/
structure Lemma17FixedLandingFacts
    (n P : ℕ) : Prop where
  htargetLower :
    P < theorem6FixedCriticalScale n
  htargetUpper :
    theorem6FixedCriticalScale n ≤ 2 * P
  hquarter :
    4 * P ≤ n
  htarget :
    theorem6FixedCriticalScale n ≤ n
  htargetRoom :
    theorem6FixedCriticalScale n + 4 ≤ n
  hlabelRoom :
    5 * (P + 1) ≤ n + 1
  hgap :
    ∃ k,
      0 < k ∧
      P + k = theorem6FixedCriticalScale n

/-- The fixed square is large enough that the dyadic bracket alone supplies
all landing capacity inequalities. -/
theorem lemma17FixedLandingFacts
    (n P : ℕ)
    (hbelow : theorem6FixedCStarSq * P < n)
    (habove : n ≤ theorem6FixedCStarSq * (2 * P)) :
    Lemma17FixedLandingFacts n P := by
  have hrange :=
    theorem6FixedCriticalScale_between_dyadic
      n P hbelow habove
  have hbelowN : 1048576 * P < n := by
    simpa using hbelow
  have hquarter : 4 * P ≤ n := by
    omega
  have htargetRoom :
      theorem6FixedCriticalScale n + 4 ≤ n := by
    omega
  have hlabelRoom :
      5 * (P + 1) ≤ n + 1 := by
    omega
  exact
    { htargetLower := hrange.1
      htargetUpper := hrange.2
      hquarter := hquarter
      htarget := by omega
      htargetRoom := htargetRoom
      hlabelRoom := hlabelRoom
      hgap :=
        theorem6FixedCriticalScale_dyadic_gap
          n P hbelow }

/-- The custom one-stage estimate specialized to the least fixed critical
scale.  Only the genuine stochastic parameter conditions remain explicit;
the target and population-room obligations come from the fixed bracket. -/
theorem lemma17GapBoundary_fixed_target_stage
    (n q cStar P rho rhoNext r : ℕ)
    (h3 : 3 ≤ n)
    (hcStar : 128 ≤ cStar)
    (hcTwo : 2 ≤ cStar)
    (hP : 4 ≤ P)
    (hbelow : theorem6FixedCStarSq * P < n)
    (habove : n ≤ theorem6FixedCStarSq * (2 * P))
    (hrho : 1 ≤ rho)
    (hroot : 19 * rho ≤ 14 * rhoNext)
    (hbias : 38 * cStar * rho ≤ P)
    (hactiveScale : 76 * cStar * r ≤ P)
    (hmean :
      (theorem6FixedCriticalScale n) ^ 3 ≤
        r * n ^ 2)
    (hqa : q * (P + 1) ≤ rho ^ 2)
    (s : InfectionRevealPhysicalState n)
    (hs : Lemma17GapBoundaryGood P cStar rho s)
    (hmajor :
      s.inactive.yIds.card ≤
        s.inactive.xIds.card) :
    terminalFailureMass
        (lemma17TargetLandingKernel n h3 cStar
          (theorem6FixedCriticalScale n) rho s)
        (Lemma17GapBoundaryGood
          (theorem6FixedCriticalScale n)
          cStar rhoNext)
      ≤ lemma17StageError P q cStar rho r := by
  have hfixed :=
    lemma17FixedLandingFacts n P hbelow habove
  exact
    lemma17GapBoundary_target_stage
      n q cStar P (theorem6FixedCriticalScale n)
      rho rhoNext r h3 hcStar hcTwo hP
      hfixed.hquarter hfixed.htargetLower
      hfixed.htargetUpper hfixed.htarget hrho
      hroot hbias hactiveScale hmean hqa
      hfixed.hlabelRoom s hs hmajor

/-- Bind an arbitrary prefix law to the fixed custom landing.  The prefix
boundary error, its final inactive-majority anchor, and the one-stage landing
error are each charged exactly once. -/
theorem lemma17Prefix_then_fixed_target_closed
    (n q cStar P rho rhoNext r : ℕ)
    (εPrefix εMajor : ℝ≥0∞)
    (p : PMF (InfectionRevealPhysicalState n))
    (h3 : 3 ≤ n)
    (hcStar : 128 ≤ cStar)
    (hcTwo : 2 ≤ cStar)
    (hP : 4 ≤ P)
    (hbelow : theorem6FixedCStarSq * P < n)
    (habove : n ≤ theorem6FixedCStarSq * (2 * P))
    (hrho : 1 ≤ rho)
    (hroot : 19 * rho ≤ 14 * rhoNext)
    (hbias : 38 * cStar * rho ≤ P)
    (hactiveScale : 76 * cStar * r ≤ P)
    (hmean :
      (theorem6FixedCriticalScale n) ^ 3 ≤
        r * n ^ 2)
    (hqa : q * (P + 1) ≤ rho ^ 2)
    (hprefix :
      terminalFailureMass p
          (Lemma17GapBoundaryGood P cStar rho) ≤
        εPrefix)
    (hanchor :
      terminalFailureMass p
          (fun z =>
            Lemma17GapBoundaryGood P cStar rho z →
              z.inactive.yIds.card ≤
                z.inactive.xIds.card) ≤
        εMajor) :
    terminalFailureMass
        (p.bind
          (lemma17TargetLandingKernel
            n h3 cStar
              (theorem6FixedCriticalScale n) rho))
        (Lemma17GapBoundaryGood
          (theorem6FixedCriticalScale n)
          cStar rhoNext)
      ≤
        εPrefix + εMajor +
          lemma17StageError P q cStar rho r := by
  classical
  let Boundary :
      InfectionRevealPhysicalState n → Prop :=
    Lemma17GapBoundaryGood P cStar rho
  let Anchor :
      InfectionRevealPhysicalState n → Prop :=
    fun z =>
      Boundary z →
        z.inactive.yIds.card ≤ z.inactive.xIds.card
  let Target :
      InfectionRevealPhysicalState n → Prop :=
    Lemma17GapBoundaryGood
      (theorem6FixedCriticalScale n) cStar rhoNext
  have hgood :
      terminalFailureMass p
          (fun z => Boundary z ∧ Anchor z) ≤
        εPrefix + εMajor := by
    exact
      (terminalFailureMass_inter_le p Boundary Anchor).trans
        (add_le_add
          (by simpa [Boundary] using hprefix)
          (by simpa [Anchor, Boundary] using hanchor))
  have hcustom :
      ∀ z, p z ≠ 0 →
        (fun z => Boundary z ∧ Anchor z) z →
        terminalFailureMass
            (lemma17TargetLandingKernel
              n h3 cStar
                (theorem6FixedCriticalScale n) rho z)
            Target ≤
          lemma17StageError P q cStar rho r := by
    intro z _ hz
    have hmajor := hz.2 hz.1
    simpa [Target] using
      lemma17GapBoundary_fixed_target_stage
        n q cStar P rho rhoNext r h3 hcStar hcTwo
        hP hbelow habove hrho hroot hbias
        hactiveScale hmean hqa z hz.1 hmajor
  exact
    terminalFailureMass_bind_le_add_of_support
      p
      (lemma17TargetLandingKernel
        n h3 cStar (theorem6FixedCriticalScale n) rho)
      (fun z => Boundary z ∧ Anchor z)
      Target
      (εPrefix + εMajor)
      (lemma17StageError P q cStar rho r)
      hgood hcustom

end

end Tri

#print axioms Tri.theorem6FixedCriticalScale_between_dyadic
#print axioms Tri.lemma17FixedLandingFacts
#print axioms Tri.lemma17GapBoundary_fixed_target_stage
#print axioms Tri.lemma17Prefix_then_fixed_target_closed
