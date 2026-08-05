/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Lemma16To19Headline

/-!
# Theorem 6 handoff after the common-parameter activation headline

The activation chain is a first-hitting estimate.  This module connects that
estimate to the proved ordinary-Tri convergence theorem without pretending
that the intermediate good set is occupied at a prescribed deterministic
time.
-/

namespace Tri

open scoped ENNReal

noncomputable section

/-- The common-parameter Lemma 16--19 headline, once instantiated, composes
with Theorem 1(b) to give `X`-consensus for the original unpaused infection
chain. -/
theorem lemma16To19_headline_then_theorem1b :
    ∃ C n₀ : ℕ, ∃ c : ℝ,
      0 < C ∧ 0 < c ∧ 3 ≤ n₀ ∧
      ∀ n γ q cStar rGap : ℕ,
        ∀ h3 : 3 ≤ n,
        ∀ s : InfectionRevealPhysicalState n,
        n₀ ≤ n →
        1 ≤ γ →
        6 * γ * Nat.log 2 n ≤ n →
        γ * Nat.log 2 n ≤ q →
        0 < q →
        q * n ≤ 16 * rGap ^ 2 →
        terminalFailureMass
            (iter
              (freeze
                (InfectionActivationGapRangeGood n
                  (lemma19CommonTargetGap rGap))
                (infectionStateStep n h3))
              ((2 * cStar + 8192) * q * n)
              (infectionRevealPhysicalForget s))
            (InfectionActivationGapRangeGood n
              (lemma19CommonTargetGap rGap))
          ≤ infectionActivationFinalError q →
        terminalFailureMass
            (iter
              (infectionStateStep n h3)
              (((2 * cStar + 8192) * q * n) +
                C * γ * n * Nat.log 2 n)
              (infectionRevealPhysicalForget s))
            InfectionXConsensus
          ≤
            infectionActivationFinalError q +
              (n : ℝ≥0∞)⁻¹ ^ (c * (γ : ℝ)) := by
  rcases infectionRawHit_then_theorem1b with
    ⟨C, n₀, c, hC, hc, hn₀, hcontinue⟩
  refine ⟨C, n₀, c, hC, hc, hn₀, ?_⟩
  intro n γ q cStar rGap h3 s
    hn hγ hsize hγq hq hGapScale hactivate
  have hgapSq :
      γ * n * Nat.log 2 n ≤
        (lemma19CommonTargetGap rGap) ^ 2 := by
    have hqn :
        γ * n * Nat.log 2 n ≤ q * n := by
      calc
        γ * n * Nat.log 2 n =
            (γ * Nat.log 2 n) * n := by ac_rfl
        _ ≤ q * n := Nat.mul_le_mul_right n hγq
    exact hqn.trans
      (lemma19Common_gap_sq n q rGap hGapScale)
  have hTactivate :
      0 < (2 * cStar + 8192) * q * n := by
    positivity
  exact
    hcontinue n γ
      (lemma19CommonTargetGap rGap)
      ((2 * cStar + 8192) * q * n)
      h3 s (infectionActivationFinalError q)
      hn hγ hsize hgapSq hTactivate hactivate

end

end Tri

#print axioms Tri.lemma16To19_headline_then_theorem1b
