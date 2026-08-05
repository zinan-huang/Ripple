/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.ByzantinePhase1Rung
import Tri.Ladder
import Tri.Phase1Refactored

/-!
# Byzantine Phase-I ladder interface

This module packages the fixed-`z` Bellman comparison proved in
`Tri.ByzantinePhase1Rung` with the dyadic Phase-I checkpoint schedule.  The
probabilistic scalar estimates for the reference rungs can be supplied rung by
rung; this file proves the exact `Reaches.chain` composition and the
history-dependent Bellman transfer from the reference hit probability to every
adaptive strategy.
-/

namespace Tri.Byzantine

open scoped ENNReal

variable {n B z : ℕ}

/-- Phase-I dyadic gap scale `d_j = min(2^j d₀, ⌈n/2⌉)`.

The ceiling is necessary for odd populations: capping at `⌊n/2⌋` can never
imply the handoff `3n ≤ 4x` when `n ≡ 3 (mod 4)`. -/
def phase1DyadicScale (n d₀ j : ℕ) : ℕ :=
  min (2 ^ j * d₀) ((n + 1) / 2)

/-- A floor-log rung budget with one endpoint rung included; it is the
convenient natural-number upper count used by callers that instantiate the
dyadic ladder. -/
def phase1DyadicRungCount (n d₀ : ℕ) : ℕ :=
  Nat.log 2 (n / (2 * d₀)) + 1

/-- Raw Phase-I horizon budget used by the paper-facing statement. -/
def phase1RawHorizon (C₁ γ n : ℕ) : ℕ :=
  C₁ * γ * n * Nat.log 2 n

/-- Productive reference quota for `J` Phase-I rungs. -/
def phase1ProductiveHorizon (n J : ℕ) : ℕ :=
  J * (5 * n)

/-- Checkpoint saying the signed honest gap is at least `d_j`, written without
natural subtraction: `n + d_j ≤ 2x`. -/
def Phase1DyadicCheckpoint
    (n d₀ j : ℕ) (q : Phase1Level n B z) : Prop :=
  n + phase1DyadicScale n d₀ j ≤ 2 * State.x q.1

instance phase1DyadicCheckpointDecidable
    (n d₀ j : ℕ) :
    DecidablePred (Phase1DyadicCheckpoint (B := B) (z := z) n d₀ j) := by
  intro q
  unfold Phase1DyadicCheckpoint
  infer_instance

/-- Phase-I upper checkpoint `Δ ≥ n/2`, equivalently `x ≥ 3n/4`. -/
def Phase1HalfTarget (q : Phase1Level n B z) : Prop :=
  3 * n ≤ 4 * State.x q.1

instance phase1HalfTargetDecidable :
    DecidablePred (Phase1HalfTarget (n := n) (B := B) (z := z)) := by
  intro q
  unfold Phase1HalfTarget
  infer_instance

/-- Lower failure boundary for a rung anchored at gap `d`. -/
def Phase1LowerFailure (d : ℕ) (q : Phase1Level n B z) : Prop :=
  4 * State.x q.1 < 2 * n + d

instance phase1LowerFailureDecidable (d : ℕ) :
    DecidablePred (Phase1LowerFailure (n := n) (B := B) (z := z) d) := by
  intro q
  unfold Phase1LowerFailure
  infer_instance

theorem phase1LowerFailure_lower
    {d : ℕ} ⦃q r : Phase1Level n B z⦄
    (hqr : q ≤ r) (hr : Phase1LowerFailure d r) :
    Phase1LowerFailure d q := by
  unfold Phase1LowerFailure at *
  change State.x q.1 ≤ State.x r.1 at hqr
  omega

theorem phase1HalfTarget_upper
    ⦃q r : Phase1Level n B z⦄
    (hqr : q ≤ r) (hq : Phase1HalfTarget q) :
    Phase1HalfTarget r := by
  unfold Phase1HalfTarget at *
  change State.x q.1 ≤ State.x r.1 at hqr
  omega

/-- Sum of the displayed per-rung reference errors. -/
noncomputable def phase1DyadicLadderError
    (J : ℕ) (ε : ℕ → ℝ≥0∞) : ℝ≥0∞ :=
  ∑ j ∈ Finset.range J, ε j

theorem phase1ProductiveHorizon_sum (n J : ℕ) :
    (∑ _j ∈ Finset.range J, 5 * n) = phase1ProductiveHorizon n J := by
  simp [phase1ProductiveHorizon, Nat.mul_comm, Nat.mul_left_comm]

/-- A caller-supplied raw budget `C₁ γ n lg n` covers the displayed productive
quota whenever its coefficient absorbs the rung count. -/
theorem phase1ProductiveHorizon_le_raw
    {C₁ γ n J : ℕ}
    (hJ : 5 * J ≤ C₁ * γ * Nat.log 2 n) :
    phase1ProductiveHorizon n J ≤ phase1RawHorizon C₁ γ n := by
  unfold phase1ProductiveHorizon phase1RawHorizon
  nlinarith [Nat.mul_le_mul_right n hJ]

/-- First dyadic-square exponent attached to a Phase-I reference ladder. -/
noncomputable def phase1DyadicEnvelopeScale (n d₀ : ℕ) : ℝ :=
  (d₀ : ℝ) ^ 2 / (96 * (n : ℝ))

/-- The `ENNReal` envelope attached to Byzantine reference rung `j`. -/
noncomputable def phase1DyadicRungEnvelope
    (n d₀ j : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal
    (phase1EnvelopeTerm (phase1DyadicEnvelopeScale n d₀) j)

/-- The dyadic presentation of the rung envelope:
`2 exp(-(2^j d₀)^2/(96n))`. -/
theorem phase1DyadicRungEnvelope_eq_gap (n d₀ j : ℕ) :
    phase1DyadicRungEnvelope n d₀ j =
      ENNReal.ofReal
        (2 * Real.exp
          (-(((2 ^ j * d₀ : ℕ) : ℝ) ^ 2 / (96 * (n : ℝ))))) := by
  unfold phase1DyadicRungEnvelope phase1EnvelopeTerm
    phase1DyadicEnvelopeScale
  norm_num only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  congr 3
  have hpow : (4 : ℝ) ^ j = (2 : ℝ) ^ (j * 2) := by
    calc
      (4 : ℝ) ^ j = ((2 : ℝ) ^ 2) ^ j := by norm_num
      _ = (2 : ℝ) ^ (2 * j) := by rw [← pow_mul]
      _ = (2 : ℝ) ^ (j * 2) := by rw [Nat.mul_comm]
  rw [hpow]
  ring

/-- The Lemma-6 common error is an admissible error for the corresponding
Byzantine dyadic rung.  After the denominator repair this is equality, stated
in the direction consumed by `Reaches.mono_error`. -/
theorem lemma6_error_le_phase1DyadicRungEnvelope (n d₀ j : ℕ) :
    (2 : ℝ≥0∞) *
        ENNReal.ofReal
          (Real.exp
            (-(((2 ^ j * d₀ : ℕ) : ℝ) ^ 2 /
              (96 * (n : ℝ))))) ≤
      phase1DyadicRungEnvelope n d₀ j := by
  -- After unfolding the envelope and splitting `ofReal (2 * e)`, the two sides
  -- differ only by `ENNReal.ofReal 2` versus the numeral `2`.
  rw [phase1DyadicRungEnvelope_eq_gap,
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
    ENNReal.ofReal_ofNat]

/-- Sum of the canonical dyadic-square reference rung envelopes. -/
noncomputable def phase1DyadicEnvelopeError
    (n d₀ J : ℕ) : ℝ≥0∞ :=
  ∑ j ∈ Finset.range J, phase1DyadicRungEnvelope n d₀ j

/-- If the initial dyadic exponent is large enough, the whole dyadic-square
error sum is controlled by four times the first exponential term. -/
theorem phase1DyadicEnvelopeError_le_first
    (n d₀ J : ℕ)
    (hscale : Real.log 2 / 3 ≤ phase1DyadicEnvelopeScale n d₀) :
    phase1DyadicEnvelopeError n d₀ J ≤
      ENNReal.ofReal
        (4 * Real.exp (-phase1DyadicEnvelopeScale n d₀)) := by
  rw [phase1DyadicEnvelopeError]
  change (∑ j ∈ Finset.range J,
      ENNReal.ofReal
        (phase1EnvelopeTerm (phase1DyadicEnvelopeScale n d₀) j)) ≤ _
  rw [← ENNReal.ofReal_sum_of_nonneg]
  · exact ENNReal.ofReal_le_ofReal
      (phase1Envelope_sum_le hscale J)
  · intro j _hj
    unfold phase1EnvelopeTerm
    positivity

/-- The first envelope scale dominates the paper seed radicand divided by
`96n` once `d₀² ≥ γ n lg n`. -/
theorem phase1DyadicEnvelopeScale_ge_natLog
    (n γ d₀ : ℕ) (hn : 0 < n)
    (hd₀ : γ * n * Nat.log 2 n ≤ d₀ ^ 2) :
    (γ : ℝ) * (Nat.log 2 n : ℝ) / 96 ≤
      phase1DyadicEnvelopeScale n d₀ := by
  have hdReal :
      (γ : ℝ) * (n : ℝ) * (Nat.log 2 n : ℝ) ≤
        (d₀ : ℝ) ^ 2 := by
    exact_mod_cast hd₀
  have hnReal : (0 : ℝ) < n := by exact_mod_cast hn
  unfold phase1DyadicEnvelopeScale
  calc
    (γ : ℝ) * (Nat.log 2 n : ℝ) / 96 =
        ((γ : ℝ) * (n : ℝ) * (Nat.log 2 n : ℝ)) /
          (96 * (n : ℝ)) := by field_simp
    _ ≤ (d₀ : ℝ) ^ 2 / (96 * (n : ℝ)) :=
      (div_le_div_iff_of_pos_right (by positivity)).mpr hdReal

/-- The paper seed premise and a base-two logarithm of at least twenty-four put
the first exponent above the geometric-summation threshold. -/
theorem phase1DyadicEnvelopeScale_ge_log_two_div_three
    {n γ d₀ : ℕ}
    (hlog : 24 ≤ Nat.log 2 n) (hγ : 1 ≤ γ)
    (hd₀ : γ * n * Nat.log 2 n ≤ d₀ ^ 2) :
    Real.log 2 / 3 ≤ phase1DyadicEnvelopeScale n d₀ := by
  have hlog12 : 12 ≤ Nat.log 2 n := hlog.trans' (by norm_num)
  have hn : 0 < n := by
    have := phase1_log_twelve_implies_size hlog12
    omega
  have hlogTwo : Real.log 2 ≤ (3 : ℝ) / 4 := by
    exact Real.log_two_lt_d9.le.trans (by norm_num)
  have hquarter : Real.log 2 / 3 ≤ (1 : ℝ) / 4 := by
    nlinarith
  have hmulNat : 24 ≤ γ * Nat.log 2 n := by
    calc
      24 = 1 * 24 := by norm_num
      _ ≤ γ * Nat.log 2 n := Nat.mul_le_mul hγ hlog
  have hmulReal : (24 : ℝ) ≤
      (γ : ℝ) * (Nat.log 2 n : ℝ) := by
    exact_mod_cast hmulNat
  calc
    Real.log 2 / 3 ≤ (1 : ℝ) / 4 := hquarter
    _ ≤ (γ : ℝ) * (Nat.log 2 n : ℝ) / 96 := by nlinarith
    _ ≤ phase1DyadicEnvelopeScale n d₀ :=
      phase1DyadicEnvelopeScale_ge_natLog n γ d₀ hn hd₀

/-- Halving the existing `48/34` floor-log margin gives the exact `96/68`
margin needed by the relaxed Byzantine envelope. -/
theorem phase1_natLog_div_ninetysix_ge_log_div_sixtyeight {n : ℕ}
    (hlog : 46 ≤ Nat.log 2 n) :
    Real.log (n : ℝ) / 68 ≤ (Nat.log 2 n : ℝ) / 96 := by
  have h := phase1_natLog_div_fortyeight_ge_log_div_thirtyfour hlog
  nlinarith

/-- Four times the first dyadic exponential is bounded by the coefficient-`4`,
exponent-`1/68` power law. -/
theorem phase1DyadicFirstEnvelope_le_power
    (n γ d₀ : ℕ)
    (hlog : 24 ≤ Nat.log 2 n)
    (hd₀ : γ * n * Nat.log 2 n ≤ d₀ ^ 2)
    (hmargin : Real.log (n : ℝ) / 68 ≤
      (Nat.log 2 n : ℝ) / 96) :
    ENNReal.ofReal
        (4 * Real.exp (-phase1DyadicEnvelopeScale n d₀)) ≤
      4 * (n : ℝ≥0∞)⁻¹ ^ ((1 / 68 : ℝ) * (γ : ℝ)) := by
  have hlog12 : 12 ≤ Nat.log 2 n := hlog.trans' (by norm_num)
  have hnNat : 0 < n := by
    have := phase1_log_twelve_implies_size hlog12
    omega
  have hnReal : (0 : ℝ) < n := by exact_mod_cast hnNat
  have hmarginMul :
      (γ : ℝ) * (Real.log (n : ℝ) / 68) ≤
        (γ : ℝ) * ((Nat.log 2 n : ℝ) / 96) :=
    mul_le_mul_of_nonneg_left hmargin (by positivity)
  have htarget :
      Real.log (n : ℝ) * ((1 / 68 : ℝ) * (γ : ℝ)) ≤
        phase1DyadicEnvelopeScale n d₀ := by
    calc
      Real.log (n : ℝ) * ((1 / 68 : ℝ) * (γ : ℝ)) =
          (γ : ℝ) * (Real.log (n : ℝ) / 68) := by ring
      _ ≤ (γ : ℝ) * ((Nat.log 2 n : ℝ) / 96) := hmarginMul
      _ = (γ : ℝ) * (Nat.log 2 n : ℝ) / 96 := by ring
      _ ≤ phase1DyadicEnvelopeScale n d₀ :=
        phase1DyadicEnvelopeScale_ge_natLog n γ d₀ hnNat hd₀
  have hexp :
      Real.exp (-phase1DyadicEnvelopeScale n d₀) ≤
        ((n : ℝ)⁻¹) ^ ((1 / 68 : ℝ) * (γ : ℝ)) := by
    calc
      Real.exp (-phase1DyadicEnvelopeScale n d₀) ≤
          Real.exp
            (-Real.log (n : ℝ) * ((1 / 68 : ℝ) * (γ : ℝ))) :=
        Real.exp_le_exp.mpr (by nlinarith)
      _ = ((n : ℝ)⁻¹) ^ ((1 / 68 : ℝ) * (γ : ℝ)) := by
        rw [Real.rpow_def_of_pos (inv_pos.mpr hnReal), Real.log_inv]
  calc
    ENNReal.ofReal (4 * Real.exp (-phase1DyadicEnvelopeScale n d₀)) ≤
        ENNReal.ofReal
          (4 * ((n : ℝ)⁻¹) ^ ((1 / 68 : ℝ) * (γ : ℝ))) :=
      ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_left hexp (by norm_num))
    _ = 4 * (n : ℝ≥0∞)⁻¹ ^ ((1 / 68 : ℝ) * (γ : ℝ)) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
      norm_num only [ENNReal.ofReal_ofNat]
      rw [← ENNReal.ofReal_rpow_of_pos (inv_pos.mpr hnReal),
        ENNReal.ofReal_inv_of_pos hnReal, ENNReal.ofReal_natCast]

/-- The dyadic-square ladder error has the relaxed polynomial tail whenever
the paper seed and explicit floor-log margin are available. -/
theorem phase1DyadicEnvelopeError_le_power
    (n γ d₀ J : ℕ)
    (hlog : 24 ≤ Nat.log 2 n) (hγ : 1 ≤ γ)
    (hd₀ : γ * n * Nat.log 2 n ≤ d₀ ^ 2)
    (hmargin : Real.log (n : ℝ) / 68 ≤
      (Nat.log 2 n : ℝ) / 96) :
    phase1DyadicEnvelopeError n d₀ J ≤
      4 * (n : ℝ≥0∞)⁻¹ ^ ((1 / 68 : ℝ) * (γ : ℝ)) := by
  exact
    (phase1DyadicEnvelopeError_le_first n d₀ J
      (phase1DyadicEnvelopeScale_ge_log_two_div_three
        hlog hγ hd₀)).trans
      (phase1DyadicFirstEnvelope_le_power n γ d₀ hlog hd₀ hmargin)

/-- Threshold-only version of the relaxed dyadic-square polynomial tail. -/
theorem phase1DyadicEnvelopeError_le_power_of_log_ge_fortysix
    (n γ d₀ J : ℕ)
    (hlog : 46 ≤ Nat.log 2 n) (hγ : 1 ≤ γ)
    (hd₀ : γ * n * Nat.log 2 n ≤ d₀ ^ 2) :
    phase1DyadicEnvelopeError n d₀ J ≤
      4 * (n : ℝ≥0∞)⁻¹ ^ ((1 / 68 : ℝ) * (γ : ℝ)) := by
  exact phase1DyadicEnvelopeError_le_power n γ d₀ J
    (hlog.trans' (by norm_num)) hγ hd₀
    (phase1_natLog_div_ninetysix_ge_log_div_sixtyeight hlog)
/-- The initial signed-gap equality places the state at dyadic checkpoint
zero. -/
theorem phase1DyadicCheckpoint_zero_of_gap
    {d₀ : ℕ} {q : Phase1Level n B z}
    (hgap : n + d₀ ≤ 2 * State.x q.1) :
    Phase1DyadicCheckpoint (B := B) (z := z) n d₀ 0 q := by
  unfold Phase1DyadicCheckpoint phase1DyadicScale
  have hscale : min (2 ^ 0 * d₀) (n / 2) ≤ d₀ := by
    simp
  omega

/-- If every reference rung reaches the next dyadic checkpoint in `5n`
productive steps, the reference ladder reaches checkpoint `J` in `5nJ`
productive steps with the summed error. -/
theorem phase1_reference_ladder_chain
    (h3 : 3 ≤ n) (d₀ J : ℕ) (ε : ℕ → ℝ≥0∞)
    (hrungs :
      ∀ j < J,
        Reaches (phase1ReferenceStep (n := n) (B := B) (z := z) h3)
          (5 * n)
          (Phase1DyadicCheckpoint (B := B) (z := z) n d₀ j)
          (Phase1DyadicCheckpoint (B := B) (z := z) n d₀ (j + 1))
          (ε j)) :
    Reaches (phase1ReferenceStep (n := n) (B := B) (z := z) h3)
      (phase1ProductiveHorizon n J)
      (Phase1DyadicCheckpoint (B := B) (z := z) n d₀ 0)
      (Phase1DyadicCheckpoint (B := B) (z := z) n d₀ J)
      (phase1DyadicLadderError J ε) := by
  let P : ℕ → Phase1Level n B z → Prop :=
    fun j => Phase1DyadicCheckpoint (B := B) (z := z) n d₀ j
  let T : ℕ → ℕ := fun _ => 5 * n
  have hchain :=
    Reaches.chain
      (K := phase1ReferenceStep (n := n) (B := B) (z := z) h3)
      (P := P) (T := T) (ε := ε) hrungs
  simpa [P, T, phase1DyadicLadderError,
    phase1ProductiveHorizon_sum n J] using hchain

/-- If the final dyadic scale is at least `n/2`, the final dyadic checkpoint
implies the Phase-I half-gap target. -/
theorem phase1DyadicCheckpoint_implies_half
    {d₀ J : ℕ}
    (hfinal : n ≤ 2 * phase1DyadicScale n d₀ J)
    {q : Phase1Level n B z}
    (hq : Phase1DyadicCheckpoint (B := B) (z := z) n d₀ J q) :
    Phase1HalfTarget q := by
  unfold Phase1DyadicCheckpoint Phase1HalfTarget at *
  omega

/-- Reference ladder form targeted at the Phase-I half-gap boundary. -/
theorem phase1_reference_ladder_to_half
    (h3 : 3 ≤ n) (d₀ J : ℕ) (ε : ℕ → ℝ≥0∞)
    (hfinal : n ≤ 2 * phase1DyadicScale n d₀ J)
    (hrungs :
      ∀ j < J,
        Reaches (phase1ReferenceStep (n := n) (B := B) (z := z) h3)
          (5 * n)
          (Phase1DyadicCheckpoint (B := B) (z := z) n d₀ j)
          (Phase1DyadicCheckpoint (B := B) (z := z) n d₀ (j + 1))
          (ε j)) :
    Reaches (phase1ReferenceStep (n := n) (B := B) (z := z) h3)
      (phase1ProductiveHorizon n J)
      (Phase1DyadicCheckpoint (B := B) (z := z) n d₀ 0)
      (Phase1HalfTarget (n := n) (B := B) (z := z))
      (phase1DyadicLadderError J ε) := by
  exact
    (phase1_reference_ladder_chain
      (n := n) (B := B) (z := z) h3 d₀ J ε hrungs).mono_post
      (by
        intro q hq
        exact phase1DyadicCheckpoint_implies_half
          (n := n) (B := B) (z := z) hfinal hq)

/-- Reference Phase-I ladder with the canonical dyadic-square rung envelopes. -/
theorem phase1_reference_dyadic_ladder_to_half
    (h3 : 3 ≤ n) (d₀ J : ℕ)
    (hfinal : n ≤ 2 * phase1DyadicScale n d₀ J)
    (hrungs :
      ∀ j < J,
        Reaches (phase1ReferenceStep (n := n) (B := B) (z := z) h3)
          (5 * n)
          (Phase1DyadicCheckpoint (B := B) (z := z) n d₀ j)
          (Phase1DyadicCheckpoint (B := B) (z := z) n d₀ (j + 1))
          (phase1DyadicRungEnvelope n d₀ j)) :
    Reaches (phase1ReferenceStep (n := n) (B := B) (z := z) h3)
      (phase1ProductiveHorizon n J)
      (Phase1DyadicCheckpoint (B := B) (z := z) n d₀ 0)
      (Phase1HalfTarget (n := n) (B := B) (z := z))
      (phase1DyadicEnvelopeError n d₀ J) := by
  simpa [phase1DyadicEnvelopeError] using
    phase1_reference_ladder_to_half
      (n := n) (B := B) (z := z) h3 d₀ J
      (fun j => phase1DyadicRungEnvelope n d₀ j) hfinal hrungs

/-- Reference Phase-I ladder with the dyadic-square error compressed to the
paper-style power envelope. -/
theorem phase1_reference_dyadic_ladder_to_half_power
    (h3 : 3 ≤ n) (γ d₀ J : ℕ)
    (hfinal : n ≤ 2 * phase1DyadicScale n d₀ J)
    (hlog : 24 ≤ Nat.log 2 n) (hγ : 1 ≤ γ)
    (hd₀ : γ * n * Nat.log 2 n ≤ d₀ ^ 2)
    (hmargin : Real.log (n : ℝ) / 68 ≤
      (Nat.log 2 n : ℝ) / 96)
    (hrungs :
      ∀ j < J,
        Reaches (phase1ReferenceStep (n := n) (B := B) (z := z) h3)
          (5 * n)
          (Phase1DyadicCheckpoint (B := B) (z := z) n d₀ j)
          (Phase1DyadicCheckpoint (B := B) (z := z) n d₀ (j + 1))
          (phase1DyadicRungEnvelope n d₀ j)) :
    Reaches (phase1ReferenceStep (n := n) (B := B) (z := z) h3)
      (phase1ProductiveHorizon n J)
      (Phase1DyadicCheckpoint (B := B) (z := z) n d₀ 0)
      (Phase1HalfTarget (n := n) (B := B) (z := z))
      (4 * (n : ℝ≥0∞)⁻¹ ^ ((1 / 68 : ℝ) * (γ : ℝ))) := by
  exact
    (phase1_reference_dyadic_ladder_to_half
      (n := n) (B := B) (z := z) h3 d₀ J hfinal hrungs).mono_error
      (phase1DyadicEnvelopeError_le_power n γ d₀ J hlog hγ hd₀ hmargin)

/-- Threshold-only power-envelope form for the reference Phase-I ladder. -/
theorem phase1_reference_dyadic_ladder_to_half_power_of_log_ge_fortysix
    (h3 : 3 ≤ n) (γ d₀ J : ℕ)
    (hfinal : n ≤ 2 * phase1DyadicScale n d₀ J)
    (hlog : 46 ≤ Nat.log 2 n) (hγ : 1 ≤ γ)
    (hd₀ : γ * n * Nat.log 2 n ≤ d₀ ^ 2)
    (hrungs :
      ∀ j < J,
        Reaches (phase1ReferenceStep (n := n) (B := B) (z := z) h3)
          (5 * n)
          (Phase1DyadicCheckpoint (B := B) (z := z) n d₀ j)
          (Phase1DyadicCheckpoint (B := B) (z := z) n d₀ (j + 1))
          (phase1DyadicRungEnvelope n d₀ j)) :
    Reaches (phase1ReferenceStep (n := n) (B := B) (z := z) h3)
      (phase1ProductiveHorizon n J)
      (Phase1DyadicCheckpoint (B := B) (z := z) n d₀ 0)
      (Phase1HalfTarget (n := n) (B := B) (z := z))
      (4 * (n : ℝ≥0∞)⁻¹ ^ ((1 / 68 : ℝ) * (γ : ℝ))) := by
  exact
    phase1_reference_dyadic_ladder_to_half_power
      (n := n) (B := B) (z := z) h3 γ d₀ J hfinal
      (hlog.trans' (by norm_num)) hγ hd₀
      (phase1_natLog_div_ninetysix_ge_log_div_sixtyeight hlog)
      hrungs

/-- Bellman transfer for a stopped Phase-I hit: the controlled
history-dependent kernel hits at least as often as the fixed paper-worst
reference kernel. -/
theorem phase1_bellman_hit_transfer
    (σ : Strategy n B) (h3 : 3 ≤ n) (d T : ℕ)
    (hist : History n B) (q : Phase1Level n B z) :
    stoppedReferenceHit
        (Phase1LowerFailure (n := n) (B := B) (z := z) d)
        (Phase1HalfTarget (n := n) (B := B) (z := z))
        (phase1ReferenceStep (n := n) (B := B) (z := z) h3)
        T q ≤
      stoppedControlledHit
        (Phase1LowerFailure (n := n) (B := B) (z := z) d)
        (Phase1HalfTarget (n := n) (B := B) (z := z))
        (phase1ControlledStep (n := n) (B := B) (z := z) σ h3)
        T hist q := by
  exact
    hitProb_ge_reference_of_kernel_stochDom
      (Phase1LowerFailure (n := n) (B := B) (z := z) d)
      (Phase1HalfTarget (n := n) (B := B) (z := z))
      (phase1ReferenceStep (n := n) (B := B) (z := z) h3)
      (phase1ControlledStep (n := n) (B := B) (z := z) σ h3)
      (@phase1LowerFailure_lower (n := n) (B := B) (z := z) d)
      (@phase1HalfTarget_upper (n := n) (B := B) (z := z))
      (phase1ReferenceStep_mono (n := n) (B := B) (z := z) h3)
      (phase1_reference_le_controlled (n := n) (B := B) (z := z) σ h3)
      T hist q

/-- Error-form Bellman transfer: any reference lower bound on hitting
probability immediately holds for every adaptive controlled strategy. -/
theorem phase1_controlled_hit_of_reference
    (σ : Strategy n B) (h3 : 3 ≤ n) (d T : ℕ)
    (hist : History n B) (q : Phase1Level n B z) (ε : ℝ≥0∞)
    (href :
      1 ≤
        stoppedReferenceHit
            (Phase1LowerFailure (n := n) (B := B) (z := z) d)
            (Phase1HalfTarget (n := n) (B := B) (z := z))
            (phase1ReferenceStep (n := n) (B := B) (z := z) h3)
            T q + ε) :
    1 ≤
      stoppedControlledHit
          (Phase1LowerFailure (n := n) (B := B) (z := z) d)
          (Phase1HalfTarget (n := n) (B := B) (z := z))
          (phase1ControlledStep (n := n) (B := B) (z := z) σ h3)
          T hist q + ε := by
  exact href.trans
    (by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_right
          (phase1_bellman_hit_transfer
            (n := n) (B := B) (z := z) σ h3 d T hist q) ε)

namespace Phase1LadderExample

private def s : State 4 0 := by
  refine ⟨(⟨3, by decide⟩, ⟨0, by decide⟩), ?_⟩
  decide

private def q : Phase1Level 4 0 0 :=
  ⟨s, by rfl⟩

private def sigma : Strategy 4 0 :=
  { choose := fun _ _ => Control.neutral }

example :
    stoppedReferenceHit
        (Phase1LowerFailure (n := 4) (B := 0) (z := 0) 2)
        (Phase1HalfTarget (n := 4) (B := 0) (z := 0))
        (phase1ReferenceStep (n := 4) (B := 0) (z := 0) (by norm_num))
        1 q ≤
      stoppedControlledHit
        (Phase1LowerFailure (n := 4) (B := 0) (z := 0) 2)
        (Phase1HalfTarget (n := 4) (B := 0) (z := 0))
        (phase1ControlledStep
          (n := 4) (B := 0) (z := 0) sigma (by norm_num))
        1 [] q := by
  exact
    phase1_bellman_hit_transfer
      (n := 4) (B := 0) (z := 0)
      sigma (by norm_num) 2 1 [] q

end Phase1LadderExample

end Tri.Byzantine

#print axioms Tri.Byzantine.phase1_reference_ladder_chain
#print axioms Tri.Byzantine.phase1_reference_ladder_to_half
#print axioms Tri.Byzantine.phase1ProductiveHorizon_sum
#print axioms Tri.Byzantine.phase1ProductiveHorizon_le_raw
#print axioms Tri.Byzantine.phase1DyadicRungEnvelope_eq_gap
#print axioms Tri.Byzantine.phase1DyadicEnvelopeError_le_first
#print axioms Tri.Byzantine.phase1DyadicEnvelopeScale_ge_natLog
#print axioms Tri.Byzantine.phase1DyadicEnvelopeScale_ge_log_two_div_three
#print axioms Tri.Byzantine.phase1DyadicFirstEnvelope_le_power
#print axioms Tri.Byzantine.phase1DyadicEnvelopeError_le_power
#print axioms Tri.Byzantine.phase1DyadicEnvelopeError_le_power_of_log_ge_fortysix
#print axioms Tri.Byzantine.phase1DyadicCheckpoint_zero_of_gap
#print axioms Tri.Byzantine.phase1_reference_dyadic_ladder_to_half
#print axioms Tri.Byzantine.phase1_reference_dyadic_ladder_to_half_power
#print axioms Tri.Byzantine.phase1_reference_dyadic_ladder_to_half_power_of_log_ge_fortysix
#print axioms Tri.Byzantine.phase1_bellman_hit_transfer
#print axioms Tri.Byzantine.phase1_controlled_hit_of_reference
