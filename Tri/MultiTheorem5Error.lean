/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.MultiTheorem5

/-!
# An honest headline error for multi-species consensus

The phase-0 proof has an explicit species union-bound coefficient
`288m + 144`.  It can be absorbed into the paper's exponential only under an
explicit growth condition.  This file records that condition and compresses
the exact finite ladder sum to a uniform exponential envelope.
-/

namespace Tri.Multi

open scoped ENNReal

variable {m n : ℕ}

/-- A uniform error envelope for all phase-0 ladder rungs. -/
noncomputable def phase0LadderHeadlineError
    (n gamma : ℕ) : ℝ≥0∞ :=
  ((3 * (Nat.log 2 n + 1) : ℕ) : ℝ≥0∞) *
    ENNReal.ofReal
      (Real.exp
        (-(((gamma * Nat.log 2 n : ℕ) : ℝ) / 165888)))

/-- Under the explicit coefficient-absorption condition, every phase-0 rung
costs at most three copies of the common exponential error. -/
theorem phase0LadderStageError_le_headline
    (m n gamma d D : ℕ)
    (hn : 0 < n)
    (hdD : d ≤ D)
    (hgapSq : gamma * n * Nat.log 2 n ≤ d ^ 2)
    (hmexp : (((288 * m + 144 : ℕ) : ℝ)) ≤
      Real.exp ((((gamma * Nat.log 2 n : ℕ) : ℝ) / 165888))) :
    phase0LadderStageError m n gamma D ≤
      (3 : ℝ≥0∞) *
        ENNReal.ofReal
          (Real.exp
            (-(((gamma * Nat.log 2 n : ℕ) : ℝ) / 165888))) := by
  let g : ℕ := gamma * Nat.log 2 n
  let e : ℝ≥0∞ :=
    ENNReal.ofReal (Real.exp (-((g : ℝ) / 165888)))
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hg0 : (0 : ℝ) ≤ (g : ℝ) := by positivity
  have hstageN : g * n ≤ D ^ 2 := by
    calc
      g * n = gamma * n * Nat.log 2 n := by
        simp only [g]
        ring
      _ ≤ d ^ 2 := hgapSq
      _ ≤ D ^ 2 := by
        exact Nat.pow_le_pow_left hdD 2
  have hstageR : ((g : ℝ) * (n : ℝ)) ≤ (D : ℝ) ^ 2 := by
    exact_mod_cast hstageN
  have hrate82944 :
      (g : ℝ) / 82944 ≤
        (D : ℝ) ^ 2 / (82944 * (n : ℝ)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hexp82944 :
      Real.exp (-((D : ℝ) ^ 2 / (82944 * (n : ℝ)))) ≤
        Real.exp (-((g : ℝ) / 82944)) :=
    Real.exp_le_exp.mpr (neg_le_neg hrate82944)
  have habsorb :
      (((288 * m + 144 : ℕ) : ℝ)) *
          Real.exp (-((g : ℝ) / 82944)) ≤
        Real.exp (-((g : ℝ) / 165888)) := by
    calc
      _ ≤ Real.exp ((g : ℝ) / 165888) *
          Real.exp (-((g : ℝ) / 82944)) :=
        mul_le_mul_of_nonneg_right hmexp (Real.exp_nonneg _)
      _ = _ := by
        rw [← Real.exp_add]
        congr 1
        ring
  have hfirstReal :
      (((288 * m + 144 : ℕ) : ℝ)) *
          Real.exp (-((D : ℝ) ^ 2 / (82944 * (n : ℝ)))) ≤
        Real.exp (-((g : ℝ) / 165888)) :=
    (mul_le_mul_of_nonneg_left hexp82944 (by positivity)).trans habsorb
  have hfirst :
      (144 : ℝ≥0∞) * productiveAmplificationError m n D ≤ e := by
    rw [productiveAmplificationError_144]
    rw [show ((288 * m + 144 : ℕ) : ℝ≥0∞) =
          ENNReal.ofReal ((288 * m + 144 : ℕ) : ℝ) from
        (ENNReal.ofReal_natCast _).symm,
      ← ENNReal.ofReal_mul
        (show (0 : ℝ) ≤ (288 * m + 144 : ℕ) by positivity)]
    exact ENNReal.ofReal_le_ofReal hfirstReal
  have hrate18 :
      (g : ℝ) / 18 ≤
        (D : ℝ) ^ 2 / (18 * (n : ℝ)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hexp18 :
      Real.exp (-((D : ℝ) ^ 2 / (18 * (n : ℝ)))) ≤
        Real.exp (-((g : ℝ) / 18)) :=
    Real.exp_le_exp.mpr (neg_le_neg hrate18)
  have hmReal : (m : ℝ) ≤ Real.exp ((g : ℝ) / 165888) := by
    calc
      (m : ℝ) ≤ ((288 * m + 144 : ℕ) : ℝ) := by
        exact_mod_cast (show m ≤ 288 * m + 144 by omega)
      _ ≤ Real.exp ((g : ℝ) / 165888) := hmexp
  have hsecondReal :
      (m : ℝ) *
          Real.exp (-((D : ℝ) ^ 2 / (18 * (n : ℝ)))) ≤
        Real.exp (-((g : ℝ) / 165888)) := by
    calc
      _ ≤ Real.exp ((g : ℝ) / 165888) *
          Real.exp (-((D : ℝ) ^ 2 / (18 * (n : ℝ)))) :=
        mul_le_mul_of_nonneg_right hmReal (Real.exp_nonneg _)
      _ ≤ Real.exp ((g : ℝ) / 165888) *
          Real.exp (-((g : ℝ) / 18)) :=
        mul_le_mul_of_nonneg_left hexp18 (Real.exp_nonneg _)
      _ = Real.exp ((g : ℝ) / 165888 - (g : ℝ) / 18) := by
        rw [← Real.exp_add]
        congr 1
      _ ≤ Real.exp (-((g : ℝ) / 165888)) := by
        apply Real.exp_le_exp.mpr
        nlinarith
  have hsecond :
      (m : ℝ≥0∞) *
          ENNReal.ofReal
            (Real.exp (-((D : ℝ) ^ 2 / (18 * (n : ℝ))))) ≤ e := by
    rw [show (m : ℝ≥0∞) = ENNReal.ofReal (m : ℝ) from
        (ENNReal.ofReal_natCast _).symm,
      ← ENNReal.ofReal_mul (show (0 : ℝ) ≤ m by positivity)]
    exact ENNReal.ofReal_le_ofReal hsecondReal
  have hthird :
      ENNReal.ofReal (Real.exp (-((g : ℝ)))) ≤ e := by
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    nlinarith
  change
    (144 : ℝ≥0∞) * productiveAmplificationError m n D +
        (m : ℝ≥0∞) *
          ENNReal.ofReal
            (Real.exp (-((D : ℝ) ^ 2 / (18 * (n : ℝ))))) +
        ENNReal.ofReal (Real.exp (-((g : ℝ)))) ≤
      (3 : ℝ≥0∞) * e
  calc
    _ ≤ e + e + e := add_le_add (add_le_add hfirst hsecond) hthird
    _ = (3 : ℝ≥0∞) * e := by ring

/-- The whole phase-0 ladder has a uniform explicit exponential envelope. -/
theorem phase0LadderErrorSum_le_headline
    (m n gamma d : ℕ)
    (hn : 0 < n)
    (hdn : d ≤ n)
    (hgapSq : gamma * n * Nat.log 2 n ≤ d ^ 2)
    (hmexp : (((288 * m + 144 : ℕ) : ℝ)) ≤
      Real.exp ((((gamma * Nat.log 2 n : ℕ) : ℝ) / 165888))) :
    (∑ j ∈ Finset.range (Nat.log 2 n + 1),
        phase0LadderStageError m n gamma
          (phase0LadderScale d n j)) ≤
      phase0LadderHeadlineError n gamma := by
  let e : ℝ≥0∞ :=
    ENNReal.ofReal
      (Real.exp
        (-(((gamma * Nat.log 2 n : ℕ) : ℝ) / 165888)))
  calc
    (∑ j ∈ Finset.range (Nat.log 2 n + 1),
        phase0LadderStageError m n gamma
          (phase0LadderScale d n j)) ≤
      ∑ j ∈ Finset.range (Nat.log 2 n + 1),
        (3 : ℝ≥0∞) * e := by
          apply Finset.sum_le_sum
          intro j hj
          exact phase0LadderStageError_le_headline
            m n gamma d (phase0LadderScale d n j)
            hn (phase0LadderScale_ge d n hdn j) hgapSq hmexp
    _ = phase0LadderHeadlineError n gamma := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      simp only [phase0LadderHeadlineError, e]
      push_cast
      ring

/-- Multi-species consensus with the phase-0 finite sum compressed to its
uniform exponential envelope.  The extra `hmexp` premise is exactly the
coefficient-absorption condition omitted by the paper. -/
theorem theorem5_multi_reaches_consensus_headline :
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
        (((288 * m + 144 : ℕ) : ℝ)) ≤
          Real.exp ((((gamma * Nat.log 2 n : ℕ) : ℝ) / 165888)) →
        Reaches
          (fun q : Config m n => multiStep q h3)
          (((Nat.log 2 n + 1) * phase0LadderStageHorizon m n) +
            C * gamma * n * Nat.log 2 n)
          (fun q => HasPairwiseGap q X d)
          (fun q => ConsensusOn q X)
          (phase0LadderHeadlineError n gamma +
            (n : ℝ≥0∞)⁻¹ ^ (c * (gamma : ℝ))) := by
  rcases theorem5_multi_reaches_consensus with
    ⟨C, n₀, c, hC, hc, hn₀, hmain⟩
  refine ⟨C, n₀, c, hC, hc, hn₀, ?_⟩
  intro m n gamma d X h3 hn hgamma hd4 hdn hclockd
    hscale hsize hm hgapSq hmexp
  apply Reaches.mono_error
    (hmain m n gamma d X h3 hn hgamma hd4 hdn hclockd
      hscale hsize hm hgapSq)
  exact add_le_add
    (phase0LadderErrorSum_le_headline
      m n gamma d (by omega) hdn hgapSq hmexp)
    le_rfl

end Tri.Multi

#print axioms Tri.Multi.phase0LadderStageError_le_headline
#print axioms Tri.Multi.phase0LadderErrorSum_le_headline
#print axioms Tri.Multi.theorem5_multi_reaches_consensus_headline
