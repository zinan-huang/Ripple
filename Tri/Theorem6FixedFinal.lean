/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Theorem6FixedActivationHandoff
import Tri.Theorem6FixedDecisivePolynomial
import Tri.Theorem6FixedGapClose
import Tri.Theorem6FixedInitialBias
import Tri.Theorem6FixedInitialScale
import Tri.Theorem6FixedPrefixPolynomial
import Tri.Theorem6FixedGuard
import Tri.Theorem6FixedErrorPower
import Tri.Theorem6FixedHorizon
import Tri.Theorem6FixedSizeDominance

/-!
# Theorem 6 after the fixed activation construction

The explicit fixed activation headline is composed with the already-proved
ordinary-Tri continuation.  The paper constant `cStar = 1024` is fixed in the
public specialization.
-/

namespace Tri

open scoped ENNReal

noncomputable section

/-- The complete fixed activation construction followed by Theorem 1(b),
assuming the three explicit finite-size guards. -/
theorem theorem6_fixed_of_size_guards :
    ∃ C n₀ : ℕ, ∃ c : ℝ,
      0 < C ∧ 0 < c ∧ 3 ≤ n₀ ∧
      ∀ n γ : ℕ,
        ∀ hn : 0 < n,
        ∀ s : InfectionRevealPhysicalState n,
        ∀ hseedActive : s.coarse.1.active = 1,
        n₀ ≤ n →
        2 ≤ γ →
        ∀ hsize : 6 * γ * Nat.log 2 n ≤ n,
        ∀ hqLarge : 8192 ≤ theorem6Q n γ,
        ∀ hcubeGuard :
          theorem6FixedCStarSq *
              (4_179_180 *
                  theorem6FifthRoot n γ ^ 3 +
                1_020) ≤
            n,
        ∀ hsqrtGuard :
          theorem6FixedCStarSq *
              (4_179_180 *
                  (8 *
                    (Nat.sqrt
                        (theorem6Q n γ * n) +
                      1)) +
                1_020) ≤
            n,
        s.initialR +
            theorem6FixedPaperGap
              (theorem6Q n γ) n ≤
          s.initialB →
        terminalFailureMass
            (iter
              (infectionStateStep n (by
                have hsize' :
                    6 * theorem6Q n γ ≤ n := by
                  simpa [theorem6Q, mul_assoc] using hsize
                omega))
              (theorem6FixedHorizonCoeff C *
                γ * n * Nat.log 2 n)
              (infectionRevealPhysicalForget s))
            InfectionXConsensus
          ≤
            2 * ((n : ℝ≥0∞)⁻¹ ^
              (c * (γ : ℝ))) := by
  rcases lemma16To19_fixed_headline_then_theorem1b with
    ⟨C, n₀, c, hC, hc, hn₀, hcontinue⟩
  let cFinal :=
    min theorem6FixedActivationExponent c
  have hcFinal : 0 < cFinal := by
    exact lt_min
      theorem6FixedActivationExponent_pos hc
  refine ⟨C, n₀, cFinal, hC, hcFinal, hn₀, ?_⟩
  intro n γ hn s hseedActive hn₀n hγ hsize
    hqLarge hcubeGuard hsqrtGuard
  intro hmargin
  have h3 : 3 ≤ n := hn₀.trans hn₀n
  have hq : 0 < theorem6Q n γ := by
    omega
  have hN : 0 < theorem6Q n γ * n :=
    Nat.mul_pos hq hn
  have hseed :
      32 * theorem6Q n γ ^ 6 ≤ n ^ 4 :=
    theorem6FixedSeed_of_cube_size
      hN hcubeGuard
  have hcriticalSeparation :
      theorem6FixedCStarSq ^ 5 <
        theorem6Q n γ * n :=
    theorem6FixedCriticalSeparation_of_cube_size
      hN hqLarge hcubeGuard
  let S :=
    theorem6InitialScaleFacts_of_size_separation
      hN (by omega) hseed hcriticalSeparation
  have hlarge :
      theorem6FixedCStarSq *
          (theorem6FixedCStarSq + 6) ≤ n :=
    theorem6FixedLarge_of_cube_size hcubeGuard
  have hbiasSize :
      38 * theorem6FixedCStar *
          theorem6FifthRoot n γ *
            (theorem6FifthRoot n γ ^ 2 + 2) ≤
        n :=
    theorem6FixedInitialBiasSize_of_cube_size
      hcubeGuard
  have hactiveFit :
      285 * theorem6Q n γ +
          76 * theorem6FixedCStar ≤
        theorem6InitialScale n γ :=
    theorem6FixedPrefixActive_of_cube_size
      S hN hcubeGuard
  let R :=
    theorem6FixedTerminalRadius n γ S.hpositive
  let I : InfectionInitialParams s
      (theorem6InitialScale n γ) :=
    InfectionInitialParams.mkOfQuarter
      s hseedActive S.hpositive S.hquarter
  have hLanding :
      lemma17FixedLandingRho
          (theorem6InitialRadius
            (theorem6Q n γ)
            (theorem6InitialScale n γ))
          (lemma17FixedStageCount n
            (theorem6InitialScale n γ) S.hpositive) ≤
        R := by
    exact theorem6FixedTerminalRadius_landing
      n γ S.hpositive
  have hSq :
      theorem6Q n γ * n ≤ R ^ 2 := by
    exact theorem6FixedTerminalRadius_sq
      n γ S.hpositive
  have hguard :
      60 *
          lemma19FixedDdec theorem6FixedPostStages
            (4 * R) theorem6FixedCStar R ≤
        theorem6FixedCriticalScale n := by
    exact
      theorem6FixedDecisiveGuard_of_sqrt_size
        S hN hsqrtGuard
  have hRlt : R < n := by
    exact theorem6FixedTerminalRadius_lt_of_guard
      S.hpositive hn hlarge hguard
  have hRsqrt :
      R ≤
        8 * (Nat.sqrt (theorem6Q n γ * n) + 1) := by
    exact theorem6FixedTerminalRadius_le_sqrt
      S hN
  have hmarginInternal :
      s.initialR +
          (R +
            theorem6FixedGapSafety
              theorem6FixedCStar R) ≤
        s.initialB := by
    exact
      (Nat.add_le_add_left
        (theorem6FixedGapSafety_le_paperGap hRsqrt)
        s.initialR).trans hmargin
  have hbias :
      38 * theorem6FixedCStar *
          theorem6InitialRadius
            (theorem6Q n γ)
            (theorem6InitialScale n γ) ≤
        theorem6InitialScale n γ :=
    theorem6InitialRadius_bias_of_size
      S hN hbiasSize
  have hfit :
      ∀ j ≤ lemma17FixedStageCount n
          (theorem6InitialScale n γ) S.hpositive,
        76 * theorem6FixedCStar *
            lemma17FixedReactionLower n
              (theorem6Q n γ) theorem6FixedCStar
              (lemma17FixedScale
                (theorem6InitialScale n γ) j) ≤
          lemma17FixedScale
            (theorem6InitialScale n γ) j :=
    lemma17FixedReactionLower_fit_of_fixed_bracket
      n (theorem6Q n γ)
      (theorem6InitialScale n γ)
      (lemma17FixedStageCount n
        (theorem6InitialScale n γ) S.hpositive)
      hn hqLarge hactiveFit
      (lemma17FixedStageCount_below
        n (theorem6InitialScale n γ) S.hpositive
        S.hbelow)
  have hfit18 :
      1200 * theorem6FixedCStar *
          lemma17FixedReactionLower n
            (theorem6Q n γ) theorem6FixedCStar
            (theorem6FixedCriticalScale n) ≤
        7 * theorem6FixedCriticalScale n :=
    theorem6FixedCriticalReactionLower_fit_of_polynomial_capacity
      hn (by norm_num [theorem6FixedCStar])
      (theorem6FixedDecisiveActive_of_cube_size
        hN hcubeGuard)
      (theorem6FixedDecisiveMean_of_cube_size
        hn hcubeGuard)
  have hactivate :
      terminalFailureMass
          (iter
            (freeze
              (InfectionActivationGapRangeGood n R)
              (infectionStateStep n h3))
            ((2 * theorem6FixedCStar + 8192) *
              theorem6Q n γ * n)
            (infectionRevealPhysicalForget s))
          (InfectionActivationGapRangeGood n R) ≤
        infectionActivationFinalError
          (theorem6Q n γ) :=
    lemma16_to_19_fixed_landing_coarse_headline_closed
      (hn := hn)
      (hcStar := by
        norm_num [theorem6FixedCStar])
      I hN hlarge hγ
      (by norm_num [theorem6FixedCStar])
      hqLarge S hbias hfit
      hRlt hSq hLanding hguard hfit18 hmarginInternal
  have hmain :=
    hcontinue n γ (theorem6Q n γ)
      theorem6FixedCStar R h3 s
      hn₀n (by omega) hsize
      (by simp [theorem6Q]) hq hSq hactivate
  rw [theorem6FixedHorizon_eq] at hmain
  exact hmain.trans (by
    simpa [cFinal] using
      theorem6FixedError_le_two_power
        n γ c h3 (by omega))

end

end Tri

#print axioms Tri.theorem6_fixed_of_size_guards
