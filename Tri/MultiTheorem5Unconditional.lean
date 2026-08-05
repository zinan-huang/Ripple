/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.MultiProductivePhase0LadderUnconditional
import Tri.MultiTheorem1bHandoff
import Tri.HitThenReaches
import Tri.Theorem4EntryHeadline

/-!
# Unconditional multi-species plurality consensus

The state-dependent phase-0 estimate removes the coefficient-absorption
premise that was missing from the printed proof.  This file compresses the
remaining logarithmic number of phase-0 rungs and composes them with the
already proved aggregate binary handoff.
-/

namespace Tri.Multi

open scoped ENNReal

variable {m n : ℕ}

/-- A fixed binary-log threshold above which the phase-0 rung coefficient is
absorbed by half of the state-dependent exponential rate. -/
def theorem5Phase0LogThreshold : ℕ :=
  866 * (4 * properStageHeadlineDenominator) ^ 2

/-- The common logarithmic threshold is large enough to invoke the
state-dependent proper-substage estimate on every phase-zero rung. -/
theorem theorem5Phase0LogThreshold_ge_headline :
    properStageHeadlineThreshold ≤ theorem5Phase0LogThreshold := by
  norm_num [theorem5Phase0LogThreshold, properStageHeadlineThreshold,
    properStageHeadlineDenominator]

/-- The common logarithmic threshold also supplies the minimum binary-log
size required when converting the exponential estimate to a population
power. -/
theorem theorem5Phase0LogThreshold_ge_128 :
    128 ≤ theorem5Phase0LogThreshold := by
  norm_num [theorem5Phase0LogThreshold, properStageHeadlineDenominator]

/-- The logarithmic rung coefficient is absorbed by half of the
state-dependent exponential rate. -/
theorem phase0_log_coefficient_le_exp
    (L gamma : ℕ)
    (hL : theorem5Phase0LogThreshold ≤ L)
    (hgamma : 1 ≤ gamma) :
    ((433 * (L + 1) : ℕ) : ℝ) ≤
      Real.exp
        (((gamma * L : ℕ) : ℝ) /
          (2 * properStageHeadlineDenominator)) := by
  let A : ℝ := 4 * properStageHeadlineDenominator
  let y : ℝ := (L : ℝ) / A
  have hLpos : 0 < L := by
    have hT : 0 < theorem5Phase0LogThreshold := by
      norm_num [theorem5Phase0LogThreshold,
        properStageHeadlineDenominator]
    omega
  have hApos : 0 < A := by
    dsimp only [A]
    norm_num [properStageHeadlineDenominator]
  have hthresholdR :
      (866 : ℝ) * A ^ 2 ≤ (L : ℝ) := by
    have hcast :
        (theorem5Phase0LogThreshold : ℝ) ≤ (L : ℝ) := by
      exact_mod_cast hL
    simpa [theorem5Phase0LogThreshold, A] using hcast
  have hLoneR : ((L + 1 : ℕ) : ℝ) ≤ 2 * (L : ℝ) := by
    exact_mod_cast (show L + 1 ≤ 2 * L by omega)
  have hquadratic :
      ((433 * (L + 1) : ℕ) : ℝ) ≤ y ^ 2 := by
    dsimp only [y]
    rw [div_pow, le_div_iff₀ (sq_pos_of_pos hApos)]
    push_cast
    have hcoeff :
        (433 : ℝ) * ((L : ℝ) + 1) ≤ 866 * (L : ℝ) := by
      push_cast at hLoneR
      nlinarith
    have hcoeffA :=
      mul_le_mul_of_nonneg_right hcoeff (sq_nonneg A)
    have hthresholdL :=
      mul_le_mul_of_nonneg_right hthresholdR
        (show (0 : ℝ) ≤ L by positivity)
    calc
      433 * ((L : ℝ) + 1) * A ^ 2 ≤
          (866 * (L : ℝ)) * A ^ 2 := hcoeffA
      _ = (866 * A ^ 2) * (L : ℝ) := by ring
      _ ≤ (L : ℝ) * (L : ℝ) := hthresholdL
      _ = (L : ℝ) ^ 2 := by ring
  have hy0 : 0 ≤ y := by
    dsimp only [y]
    positivity
  have hyExp : y ≤ Real.exp y :=
    (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1)).trans
      (Real.add_one_le_exp y)
  have hySqExp : y ^ 2 ≤ Real.exp y * Real.exp y := by
    simpa [pow_two] using mul_self_le_mul_self hy0 hyExp
  have hgammaL : L ≤ gamma * L := by
    nlinarith
  calc
    ((433 * (L + 1) : ℕ) : ℝ) ≤ y ^ 2 := hquadratic
    _ ≤ Real.exp y * Real.exp y := hySqExp
    _ = Real.exp (2 * y) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ = Real.exp
        ((L : ℝ) / (2 * properStageHeadlineDenominator)) := by
      congr 1
      dsimp only [y, A]
      ring
    _ ≤ Real.exp
        (((gamma * L : ℕ) : ℝ) /
          (2 * properStageHeadlineDenominator)) := by
      apply Real.exp_le_exp.mpr
      have hgammaLR : (L : ℝ) ≤ gamma * L := by
        exact_mod_cast hgammaL
      push_cast
      exact div_le_div_of_nonneg_right hgammaLR (by positivity)

/-! ## Compressing the complete phase-zero error

One raw rung contributes 432 copies of the proper-substage exponential plus
one clock tail. The clock tail fits a 433rd copy, after which the logarithmic
number of rungs is absorbed into half of the exponential rate.
-/

/-- One unconditional raw phase-0 rung is at most `433` copies of the common
state-dependent exponential. -/
theorem phase0LadderUnconditionalStageError_le
    (g : ℕ) :
    phase0LadderUnconditionalStageError g ≤
      (433 : ℝ≥0∞) *
        ENNReal.ofReal
          (Real.exp
            (-((g : ℝ) / properStageHeadlineDenominator))) := by
  let e : ℝ≥0∞ :=
    ENNReal.ofReal
      (Real.exp
        (-((g : ℝ) / properStageHeadlineDenominator)))
  have hclock :
      ENNReal.ofReal (Real.exp (-(g : ℝ))) ≤ e := by
    dsimp only [e]
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    have hC : (1 : ℝ) ≤ properStageHeadlineDenominator := by
      norm_num [properStageHeadlineDenominator]
    have hg0 : (0 : ℝ) ≤ g := by positivity
    apply neg_le_neg
    exact (div_le_iff₀ (by positivity :
      (0 : ℝ) < properStageHeadlineDenominator)).2 <| by
        nlinarith
  change
    (144 : ℝ≥0∞) *
        ((3 : ℝ≥0∞) * e) +
      ENNReal.ofReal (Real.exp (-(g : ℝ))) ≤
        (433 : ℝ≥0∞) * e
  calc
    _ ≤ (144 : ℝ≥0∞) * (3 * e) + e :=
      add_le_add le_rfl hclock
    _ = (433 : ℝ≥0∞) * e := by ring

/-- The whole unconditional phase-0 error is an inverse population power. -/
theorem phase0LadderUnconditionalError_le_power
    (n gamma : ℕ)
    (hlog : theorem5Phase0LogThreshold ≤ Nat.log 2 n)
    (hgamma : 1 ≤ gamma) :
    ((Nat.log 2 n + 1 : ℕ) : ℝ≥0∞) *
        phase0LadderUnconditionalStageError
          (gamma * Nat.log 2 n) ≤
      (n : ℝ≥0∞)⁻¹ ^
        ((gamma : ℝ) /
          (2 * properStageHeadlineDenominator)) := by
  let L := Nat.log 2 n
  let g := gamma * L
  let e : ℝ≥0∞ :=
    ENNReal.ofReal
      (Real.exp
        (-((g : ℝ) / properStageHeadlineDenominator)))
  have hn : 0 < n := by
    have hlog128 : 128 ≤ Nat.log 2 n :=
      theorem5Phase0LogThreshold_ge_128.trans hlog
    have hlog1 : 1 ≤ Nat.log 2 n := by omega
    have hnne : n ≠ 0 := by
      intro hn0
      subst n
      norm_num at hlog1
    exact Nat.pos_of_ne_zero hnne
  have hstage :=
    phase0LadderUnconditionalStageError_le g
  have hcoeffReal :=
    phase0_log_coefficient_le_exp L gamma hlog hgamma
  have hreal :
      ((433 * (L + 1) : ℕ) : ℝ) *
          Real.exp
            (-((g : ℝ) / properStageHeadlineDenominator)) ≤
        Real.exp
          (-((g : ℝ) /
            (2 * properStageHeadlineDenominator))) := by
    calc
      _ ≤ Real.exp
            ((g : ℝ) /
              (2 * properStageHeadlineDenominator)) *
          Real.exp
            (-((g : ℝ) / properStageHeadlineDenominator)) :=
        mul_le_mul_of_nonneg_right hcoeffReal (Real.exp_nonneg _)
      _ = Real.exp
          (-((g : ℝ) /
            (2 * properStageHeadlineDenominator))) := by
        rw [← Real.exp_add]
        congr 1
        ring
  have hfinite :
      ((L + 1 : ℕ) : ℝ≥0∞) *
          phase0LadderUnconditionalStageError g ≤
        ENNReal.ofReal
          (Real.exp
            (-((g : ℝ) /
              (2 * properStageHeadlineDenominator)))) := by
    calc
      ((L + 1 : ℕ) : ℝ≥0∞) *
            phase0LadderUnconditionalStageError g ≤
          ((L + 1 : ℕ) : ℝ≥0∞) * ((433 : ℝ≥0∞) * e) :=
        by
          simpa [mul_comm] using
            mul_le_mul_right hstage ((L + 1 : ℕ) : ℝ≥0∞)
      _ = ((433 * (L + 1) : ℕ) : ℝ≥0∞) * e := by
        push_cast
        ring
      _ = ENNReal.ofReal
          (((433 * (L + 1) : ℕ) : ℝ) *
            Real.exp
              (-((g : ℝ) / properStageHeadlineDenominator))) := by
        exact natCast_mul_ofReal_eq_of_nonneg _ _
      _ ≤ ENNReal.ofReal
          (Real.exp
            (-((g : ℝ) /
              (2 * properStageHeadlineDenominator)))) :=
        ENNReal.ofReal_le_ofReal hreal
  have hlogle :=
    Tri.Byzantine.theorem4RealLog_le_natLog
      (theorem5Phase0LogThreshold_ge_128.trans hlog)
  have hrate :
      Real.log (n : ℝ) *
          ((gamma : ℝ) /
            (2 * properStageHeadlineDenominator)) ≤
        (g : ℝ) /
          (2 * properStageHeadlineDenominator) := by
    calc
      Real.log (n : ℝ) *
            ((gamma : ℝ) /
              (2 * properStageHeadlineDenominator)) ≤
          (L : ℝ) *
            ((gamma : ℝ) /
              (2 * properStageHeadlineDenominator)) :=
        mul_le_mul_of_nonneg_right hlogle (by positivity)
      _ = (g : ℝ) /
          (2 * properStageHeadlineDenominator) := by
        dsimp only [g, L]
        push_cast
        ring
  simpa only [L, g] using hfinite.trans
    (Tri.Byzantine.theorem4_ofReal_exp_neg_le_inv_rpow
      n hn
      ((g : ℝ) / (2 * properStageHeadlineDenominator))
      ((gamma : ℝ) / (2 * properStageHeadlineDenominator))
      hrate)

/-! ## Theorem 5 statement and end-to-end assembly -/

/-- **Unconditional corrected Theorem 5.**

For every paper-range population and species count, a plurality gap at the
square-root scale reaches consensus within the stated
`O(m n log n + gamma n log n)` horizon.  The failure probability is
`n^{-Omega(gamma)}` with no coefficient-absorption premise. -/
def Theorem5_statement : Prop :=
    ∃ C n₀ : ℕ, ∃ c : ℝ,
      0 < C ∧ 0 < c ∧ 3 ≤ n₀ ∧
      ∀ m n gamma d : ℕ, ∀ X : Species m, ∀ h3 : 3 ≤ n,
        n₀ ≤ n →
        1 ≤ gamma →
        4 ≤ d →
        d ≤ n →
        3 * d ≤ n →
        6 ≤ gamma * Nat.log 2 n →
        6 * gamma * Nat.log 2 n ≤ n →
        m * (gamma * Nat.log 2 n) ≤ n →
        gamma * n * Nat.log 2 n ≤ d ^ 2 →
        Reaches
          (fun q : Config m n => multiStep q h3)
          (((Nat.log 2 n + 1) * phase0LadderStageHorizon m n) +
            C * gamma * n * Nat.log 2 n)
          (fun q => HasPairwiseGap q X d)
          (fun q => ConsensusOn q X)
          ((2 : ℝ≥0∞) *
            (n : ℝ≥0∞)⁻¹ ^ (c * (gamma : ℝ)))

/-- Assemble the unconditional phase-zero exit with the aggregate binary
handoff. Frozen hitting preserves any consensus reached early, and choosing
the final exponent as the minimum of the two phase exponents puts both error
terms under one common population power. -/
theorem theorem5_multi_reaches_consensus_unconditional :
    Theorem5_statement := by
  unfold Theorem5_statement
  rcases theorem1b_multi_aggregate_reaches_consensus with
    ⟨C, n₁, c₁, hC, hc₁, hn₁, haggregate⟩
  let n₀ := max n₁ (2 ^ theorem5Phase0LogThreshold)
  let c₀ : ℝ := 1 / (2 * properStageHeadlineDenominator)
  let c : ℝ := min c₁ c₀
  have hc₀ : 0 < c₀ := by
    norm_num [c₀, properStageHeadlineDenominator]
  have hc : 0 < c := lt_min hc₁ hc₀
  have hn₀ : 3 ≤ n₀ := by
    dsimp only [n₀]
    exact hn₁.trans (le_max_left _ _)
  refine ⟨C, n₀, c, hC, hc, hn₀, ?_⟩
  intro m n gamma d X h3 hn hgamma hd4 hdn hclockd
    hscale hsize hm hgapSq
  have hn₁n : n₁ ≤ n :=
    (le_max_left n₁ (2 ^ theorem5Phase0LogThreshold)).trans hn
  have hpow :
      2 ^ theorem5Phase0LogThreshold ≤ n :=
    (le_max_right n₁ (2 ^ theorem5Phase0LogThreshold)).trans hn
  have hlog :
      theorem5Phase0LogThreshold ≤ Nat.log 2 n :=
    Nat.le_log_of_pow_le (by norm_num) hpow
  have hgLarge :
      properStageHeadlineThreshold ≤ gamma * Nat.log 2 n := by
    calc
      properStageHeadlineThreshold ≤ theorem5Phase0LogThreshold :=
        theorem5Phase0LogThreshold_ge_headline
      _ ≤ Nat.log 2 n := hlog
      _ ≤ gamma * Nat.log 2 n := by nlinarith
  let K : Config m n → PMF (Config m n) :=
    fun q => multiStep q h3
  let T₁ : ℕ :=
    (Nat.log 2 n + 1) * phase0LadderStageHorizon m n
  let T₂ : ℕ :=
    C * gamma * n * Nat.log 2 n
  let ε₁ : ℝ≥0∞ :=
    ((Nat.log 2 n + 1 : ℕ) : ℝ≥0∞) *
      phase0LadderUnconditionalStageError
        (gamma * Nat.log 2 n)
  let ε₂ : ℝ≥0∞ :=
    (n : ℝ≥0∞)⁻¹ ^ (c₁ * (gamma : ℝ))
  have hmPos : 0 < m := by
    have := X.isLt
    omega
  have hT₁ : 0 < T₁ := by
    dsimp only [T₁, phase0LadderStageHorizon]
    positivity
  have hT₂ : 0 < T₂ := by
    dsimp only [T₂]
    have hgammaPos : 0 < gamma := by omega
    have hnPos : 0 < n := by omega
    have hlogPos : 0 < Nat.log 2 n := by
      have hTpos : 0 < theorem5Phase0LogThreshold := by
        norm_num [theorem5Phase0LogThreshold,
          properStageHeadlineDenominator]
      omega
    positivity
  have hhit :
      ∀ q, HasPairwiseGap q X d →
        terminalFailureMass
          (iter (freeze (Phase0LadderExit X d) K) T₁ q)
          (Phase0LadderExit X d) ≤ ε₁ := by
    intro q hq
    simpa only [K, T₁, ε₁] using
      phase0Ladder_raw_exit_unconditional
        h3 X d (gamma * Nat.log 2 n) hgLarge hscale
        hd4 hdn hclockd hm
        (by
          calc
            (gamma * Nat.log 2 n) * n =
                gamma * n * Nat.log 2 n := by ring
            _ ≤ d ^ 2 := hgapSq)
        q hq
  have hpost :
      Reaches K T₂
        (Phase0LadderExit X d)
        (fun q => ConsensusOn q X) ε₂ := by
    intro q hq
    rcases hq with hcons | hhandoff
    · have habs : K q = PMF.pure q := by
        exact multiStep_consensus q X hcons h3
      have hiter : iter K T₂ q = PMF.pure q := by
        induction T₂ with
        | zero => rfl
        | succ T ih =>
            rw [iter_succ, habs, PMF.pure_bind, ih]
      rw [hiter]
      change terminalFailureMass (PMF.pure q)
        (fun z => ConsensusOn z X) ≤ ε₂
      rw [terminalFailureMass_pure]
      simp [hcons]
    · exact
        haggregate m n gamma d X h3 hn₁n hgamma
          hsize q ⟨hhandoff, hgapSq⟩
  have habs :
      ∀ q, ConsensusOn q X → K q = PMF.pure q := by
    intro q hq
    exact multiStep_consensus q X hq h3
  have hcomp :
      Reaches K (T₁ + T₂)
        (fun q => HasPairwiseGap q X d)
        (fun q => ConsensusOn q X) (ε₁ + ε₂) :=
    Reaches.comp_of_frozen_hit
      K hT₁ hT₂ hhit hpost habs
  have hphase0 :
      ε₁ ≤
        (n : ℝ≥0∞)⁻¹ ^
          (c₀ * (gamma : ℝ)) := by
    have hp :=
      phase0LadderUnconditionalError_le_power n gamma hlog hgamma
    dsimp only [ε₁, c₀]
    convert hp using 1
    ring_nf
  have hnOne : (n : ℝ≥0∞)⁻¹ ≤ 1 := by
    rw [ENNReal.inv_le_one]
    exact_mod_cast (show 1 ≤ n by omega)
  have hcLeft : c ≤ c₀ := min_le_right _ _
  have hcRight : c ≤ c₁ := min_le_left _ _
  have hphase0' :
      ε₁ ≤ (n : ℝ≥0∞)⁻¹ ^ (c * (gamma : ℝ)) :=
    hphase0.trans <|
      ENNReal.rpow_le_rpow_of_exponent_ge hnOne <| by
        have hgammaR : (0 : ℝ) ≤ gamma := by positivity
        exact mul_le_mul_of_nonneg_right hcLeft hgammaR
  have hpost' :
      ε₂ ≤ (n : ℝ≥0∞)⁻¹ ^ (c * (gamma : ℝ)) := by
    dsimp only [ε₂]
    exact ENNReal.rpow_le_rpow_of_exponent_ge hnOne <| by
      have hgammaR : (0 : ℝ) ≤ gamma := by positivity
      exact mul_le_mul_of_nonneg_right hcRight hgammaR
  apply Reaches.mono_error
    (by simpa only [K, T₁, T₂, ε₁, ε₂, c] using hcomp)
  calc
    ε₁ + ε₂ ≤
        (n : ℝ≥0∞)⁻¹ ^ (c * (gamma : ℝ)) +
          (n : ℝ≥0∞)⁻¹ ^ (c * (gamma : ℝ)) :=
      add_le_add hphase0' hpost'
    _ = (2 : ℝ≥0∞) *
        (n : ℝ≥0∞)⁻¹ ^ (c * (gamma : ℝ)) := by ring

/-- Canonical theorem name exposing the fully quantified corrected statement
used by the paper-facing audit. -/
theorem theorem5 : Theorem5_statement :=
  theorem5_multi_reaches_consensus_unconditional

end Tri.Multi

#print axioms Tri.Multi.phase0LadderUnconditionalError_le_power
#print axioms Tri.Multi.theorem5_multi_reaches_consensus_unconditional
#print axioms Tri.Multi.theorem5
