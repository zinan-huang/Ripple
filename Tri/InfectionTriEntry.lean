/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Lemma16To19
import Tri.InfectionFullActive
import Tri.Theorem1bFinal

/-!
# Ordinary-Tri handoff after physical activation

The positive-gap endpoint of Lemma 19 is converted to the initial condition of
Theorem 1(b).  The proved ordinary-Tri theorem is also exposed in the
reachability form consumed by the fully-active infection handoff.
-/

namespace Tri

open scoped ENNReal

noncomputable section

/-- A fully activated physical state whose active `X` count satisfies the
ordinary-Tri initial-gap condition. -/
def InfectionTriEntry
    (n γ : ℕ) (s : InfectionRevealPhysicalState n) : Prop :=
  n ≤ s.coarse.1.active ∧
    AssemblyInitial n γ s.coarse.1.ax

noncomputable instance infectionTriEntryDecidable
    (n γ : ℕ) :
    DecidablePred (InfectionTriEntry n γ) :=
  Classical.decPred _

/-- The positive-gap endpoint of Lemma 19 is a valid ordinary-Tri entry. -/
theorem lemma19PhysicalStageRangeGood_to_infectionTriEntry
    (n γ targetGap : ℕ)
    (s : InfectionRevealPhysicalState n)
    (hs : Lemma19PhysicalStageRangeGood n targetGap s)
    (hgapSq :
      γ * n * Nat.log 2 n ≤ targetGap ^ 2) :
    InfectionTriEntry n γ s := by
  unfold Lemma19PhysicalStageRangeGood at hs
  have hinv := s.coarse.2
  simp only [InfectionCfg.Inv, InfectionCfg.total,
    InfectionCfg.active, InfectionCfg.inactive] at hinv
  have hactive :
      s.coarse.1.active =
        s.coarse.1.ax + s.coarse.1.ay := rfl
  refine ⟨hs.1, ?_⟩
  constructor
  · omega
  · refine ⟨targetGap, ?_, hgapSq⟩
    omega

/-- The proved Theorem 1(b) in the reachability form consumed by the
fully-active infection handoff. -/
theorem theorem1b_reaches_top :
    ∃ C n₀ : ℕ, ∃ c : ℝ,
      0 < C ∧ 0 < c ∧ 3 ≤ n₀ ∧
      ∀ n γ : ℕ,
        n₀ ≤ n →
        1 ≤ γ →
        6 * γ * Nat.log 2 n ≤ n →
        Reaches
          (triChain n)
          (C * γ * n * Nat.log 2 n)
          (AssemblyInitial n γ)
          (fun x => n ≤ x)
          ((n : ℝ≥0∞)⁻¹ ^ (c * (γ : ℝ))) := by
  rcases theorem1b with
    ⟨C, n₀, c, hC, hc, hn₀, hmain⟩
  refine ⟨C, n₀, c, hC, hc, hn₀, ?_⟩
  intro n γ hn hγ hsize x₀ hx₀
  have hmajor :=
    hmain n γ x₀ hn hγ hsize hx₀.1 hx₀.2
  calc
    (∑' z, if n ≤ z then 0
        else iter (triChain n)
          (C * γ * n * Nat.log 2 n) x₀ z)
        =
      terminalFailureMass
        (iter (triChain n)
          (C * γ * n * Nat.log 2 n) x₀)
        (fun z => n ≤ z) := rfl
    _ ≤
      terminalFailureMass
        (iter (triChain n)
          (C * γ * n * Nat.log 2 n) x₀)
        (IsXMajority n) := by
          apply terminalFailureMass_mono
          intro z hz
          simpa [IsXMajority] using hz.ge
    _ ≤ (n : ℝ≥0∞)⁻¹ ^ (c * (γ : ℝ)) := hmajor

/-- Once the physical activation analysis reaches `InfectionTriEntry`, the
remaining infection dynamics reaches all-`X` consensus by Theorem 1(b). -/
theorem theorem1b_infection_from_triEntry :
    ∃ C n₀ : ℕ, ∃ c : ℝ,
      0 < C ∧ 0 < c ∧ 3 ≤ n₀ ∧
      ∀ n γ : ℕ, ∀ h3 : 3 ≤ n,
        n₀ ≤ n →
        1 ≤ γ →
        6 * γ * Nat.log 2 n ≤ n →
        Reaches
          (infectionStateStep n h3)
          (C * γ * n * Nat.log 2 n)
          (fun s : InfectionState n =>
            s.1.AllActive ∧ AssemblyInitial n γ s.1.ax)
          InfectionXConsensus
          ((n : ℝ≥0∞)⁻¹ ^ (c * (γ : ℝ))) := by
  rcases theorem1b_reaches_top with
    ⟨C, n₀, c, hC, hc, hn₀, hmain⟩
  refine ⟨C, n₀, c, hC, hc, hn₀, ?_⟩
  intro n γ h3 hn hγ hsize
  simpa only using
    infectionReaches_consensus_of_triReaches
      n h3 (hmain n γ hn hγ hsize)

end

end Tri

#print axioms Tri.lemma19PhysicalStageRangeGood_to_infectionTriEntry
#print axioms Tri.theorem1b_reaches_top
#print axioms Tri.theorem1b_infection_from_triEntry
