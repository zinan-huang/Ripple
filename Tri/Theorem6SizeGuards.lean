/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Theorem6ActivationToTheorem1b
import Tri.Theorem6DecisivePolynomial
import Tri.Theorem6GapClose
import Tri.Theorem6InitialBias
import Tri.Theorem6InitialScaleSize
import Tri.Theorem6PrefixPolynomial
import Tri.Theorem6Guard
import Tri.Theorem6ErrorPower
import Tri.Theorem6Horizon
import Tri.Theorem6SizeDominance

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
theorem theorem6_of_size_guards :
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
          theorem6CStarSq *
              (4_179_180 *
                  theorem6FifthRoot n γ ^ 3 +
                1_020) ≤
            n,
        ∀ hsqrtGuard :
          theorem6CStarSq *
              (4_179_180 *
                  (8 *
                    (Nat.sqrt
                        (theorem6Q n γ * n) +
                      1)) +
                1_020) ≤
            n,
        s.initialR +
            theorem6PaperGap
              (theorem6Q n γ) n ≤
          s.initialB →
        terminalFailureMass
            (iter
              (infectionStateStep n (by
                have hsize' :
                    6 * theorem6Q n γ ≤ n := by
                  simpa [theorem6Q, mul_assoc] using hsize
                omega))
              (theorem6HorizonCoeff C *
                γ * n * Nat.log 2 n)
              (infectionRevealPhysicalForget s))
            InfectionXConsensus
          ≤
            2 * ((n : ℝ≥0∞)⁻¹ ^
              (c * (γ : ℝ))) := by
  rcases lemma16To19_criticalLanding_then_theorem1b with
    ⟨C, n₀, c, hC, hc, hn₀, hcontinue⟩
  let cFinal :=
    min theorem6ActivationExponent c
  have hcFinal : 0 < cFinal := by
    exact lt_min
      theorem6ActivationExponent_pos hc
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
    theorem6Seed_of_cube_size
      hN hcubeGuard
  have hcriticalSeparation :
      theorem6CStarSq ^ 5 <
        theorem6Q n γ * n :=
    theorem6CriticalSeparation_of_cube_size
      hN hqLarge hcubeGuard
  let S :=
    theorem6InitialScaleFacts_of_size_separation
      hN (by omega) hseed hcriticalSeparation
  have hlarge :
      theorem6CStarSq *
          (theorem6CStarSq + 6) ≤ n :=
    theorem6Large_of_cube_size hcubeGuard
  have hbiasSize :
      38 * theorem6CStar *
          theorem6FifthRoot n γ *
            (theorem6FifthRoot n γ ^ 2 + 2) ≤
        n :=
    theorem6InitialBiasSize_of_cube_size
      hcubeGuard
  have hactiveFit :
      285 * theorem6Q n γ +
          76 * theorem6CStar ≤
        theorem6InitialScale n γ :=
    theorem6PrefixActive_of_cube_size
      S hN hcubeGuard
  let R :=
    theorem6TerminalRadius n γ S.hpositive
  let I : InfectionInitialParams s
      (theorem6InitialScale n γ) :=
    InfectionInitialParams.mkOfQuarter
      s hseedActive S.hpositive S.hquarter
  have hLanding :
      lemma17LandingRho
          (theorem6InitialRadius
            (theorem6Q n γ)
            (theorem6InitialScale n γ))
          (lemma17StageCount n
            (theorem6InitialScale n γ) S.hpositive) ≤
        R := by
    exact theorem6TerminalRadius_landing
      n γ S.hpositive
  have hSq :
      theorem6Q n γ * n ≤ R ^ 2 := by
    exact theorem6TerminalRadius_sq
      n γ S.hpositive
  have hguard :
      60 *
          lemma19Ddec theorem6PostStages
            (4 * R) theorem6CStar R ≤
        theorem6CriticalScale n := by
    exact
      theorem6DecisiveGuard_of_sqrt_size
        S hN hsqrtGuard
  have hRlt : R < n := by
    exact theorem6TerminalRadius_lt_of_guard
      S.hpositive hn hlarge hguard
  have hRsqrt :
      R ≤
        8 * (Nat.sqrt (theorem6Q n γ * n) + 1) := by
    exact theorem6TerminalRadius_le_sqrt
      S hN
  have hmarginInternal :
      s.initialR +
          (R +
            theorem6GapSafety
              theorem6CStar R) ≤
        s.initialB := by
    exact
      (Nat.add_le_add_left
        (theorem6GapSafety_le_paperGap hRsqrt)
        s.initialR).trans hmargin
  have hbias :
      38 * theorem6CStar *
          theorem6InitialRadius
            (theorem6Q n γ)
            (theorem6InitialScale n γ) ≤
        theorem6InitialScale n γ :=
    theorem6InitialRadius_bias_of_size
      S hN hbiasSize
  have hfit :
      ∀ j ≤ lemma17StageCount n
          (theorem6InitialScale n γ) S.hpositive,
        76 * theorem6CStar *
            lemma17ReactionLower n
              (theorem6Q n γ) theorem6CStar
              (lemma17Scale
                (theorem6InitialScale n γ) j) ≤
          lemma17Scale
            (theorem6InitialScale n γ) j :=
    lemma17ReactionLower_fit_of_critical_bracket
      n (theorem6Q n γ)
      (theorem6InitialScale n γ)
      (lemma17StageCount n
        (theorem6InitialScale n γ) S.hpositive)
      hn hqLarge hactiveFit
      (lemma17StageCount_below
        n (theorem6InitialScale n γ) S.hpositive
        S.hbelow)
  have hfit18 :
      1200 * theorem6CStar *
          lemma17ReactionLower n
            (theorem6Q n γ) theorem6CStar
            (theorem6CriticalScale n) ≤
        7 * theorem6CriticalScale n :=
    theorem6CriticalReactionLower_fit_of_polynomial_capacity
      hn (by norm_num [theorem6CStar])
      (theorem6DecisiveActive_of_cube_size
        hN hcubeGuard)
      (theorem6DecisiveMean_of_cube_size
        hn hcubeGuard)
  have hactivate :
      terminalFailureMass
          (iter
            (freeze
              (InfectionActivationGapRangeGood n R)
              (infectionStateStep n h3))
            ((2 * theorem6CStar + 8192) *
              theorem6Q n γ * n)
            (infectionRevealPhysicalForget s))
          (InfectionActivationGapRangeGood n R) ≤
        infectionActivationTotalError
          (theorem6Q n γ) :=
    lemma16_to_19_critical_landing_coarse_linear_clock_closed
      (hn := hn)
      (hcStar := by
        norm_num [theorem6CStar])
      I hN hlarge hγ
      (by norm_num [theorem6CStar])
      hqLarge S hbias hfit
      hRlt hSq hLanding hguard hfit18 hmarginInternal
  have hmain :=
    hcontinue n γ (theorem6Q n γ)
      theorem6CStar R h3 s
      hn₀n (by omega) hsize
      (by simp [theorem6Q]) hq hSq hactivate
  rw [theorem6Horizon_eq] at hmain
  exact hmain.trans (by
    simpa [cFinal] using
      theorem6Error_le_two_power
        n γ c h3 (by omega))

end

end Tri

#print axioms Tri.theorem6_of_size_guards
