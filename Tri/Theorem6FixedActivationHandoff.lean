/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Lemma16To19FixedComplete
import Tri.Lemma16To19Raw

/-!
# Theorem 6 handoff after the fixed activation headline

The fixed route exposes its terminal gap directly rather than through the
older common-parameter wrapper.  This module connects that quantitative
activation hit to the existing Theorem 1(b) continuation.
-/

namespace Tri

open scoped ENNReal

noncomputable section

/-- Any fixed-route activation headline with the common exponent parameter
composes with the already-proved ordinary-Tri convergence theorem. -/
theorem lemma16To19_fixed_headline_then_theorem1b :
    ∃ C n₀ : ℕ, ∃ c : ℝ,
      0 < C ∧ 0 < c ∧ 3 ≤ n₀ ∧
      ∀ n γ q cStar targetGap : ℕ,
        ∀ h3 : 3 ≤ n,
        ∀ s : InfectionRevealPhysicalState n,
        n₀ ≤ n →
        1 ≤ γ →
        6 * γ * Nat.log 2 n ≤ n →
        γ * Nat.log 2 n ≤ q →
        0 < q →
        q * n ≤ targetGap ^ 2 →
        terminalFailureMass
            (iter
              (freeze
                (InfectionActivationGapRangeGood n targetGap)
                (infectionStateStep n h3))
              ((2 * cStar + 8192) * q * n)
              (infectionRevealPhysicalForget s))
            (InfectionActivationGapRangeGood n targetGap)
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
  intro n γ q cStar targetGap h3 s
    hn hγ hsize hγq hq hgapSq hactivate
  have hgapSq' :
      γ * n * Nat.log 2 n ≤ targetGap ^ 2 := by
    have hqn :
        γ * n * Nat.log 2 n ≤ q * n := by
      calc
        γ * n * Nat.log 2 n =
            (γ * Nat.log 2 n) * n := by ac_rfl
        _ ≤ q * n := Nat.mul_le_mul_right n hγq
    exact hqn.trans hgapSq
  have hTactivate :
      0 < (2 * cStar + 8192) * q * n := by
    positivity
  exact
    hcontinue n γ targetGap
      ((2 * cStar + 8192) * q * n)
      h3 s (infectionActivationFinalError q)
      hn hγ hsize hgapSq' hTactivate hactivate

end

end Tri

#print axioms Tri.lemma16To19_fixed_headline_then_theorem1b
