import Ripple.BoundedUniversality.BGP.SelectorReplicatorConcSchedule
import Ripple.BoundedUniversality.BGP.SelectorReplicatorHStartStructural
import Ripple.BoundedUniversality.BGP.SelectorWriteReach
import Ripple.BoundedUniversality.BGP.SelectorZWriteDischarge
import Ripple.BoundedUniversality.BGP.BGPParams38

/-!
Ripple.BoundedUniversality.BGP.SelectorReplicatorRadiiDecay
---------------------------------------
Schedule-only decay facts for the faithfulness radii.

This file deliberately keeps the actual finite-window producers as hypotheses:
`δhold` must be bounded by the offphase envelope supplied from the hold-drift
estimate, and the z-write lower bound `Λ` must dominate the explicit
write-integral lower bound.  The asymptotic work here is only the scalar
exponential decay/growth.
-/

noncomputable section

namespace Ripple.BoundedUniversality.BGP

open Filter MachineInstance
open scoped Topology

/-- Coarse scalar prefactor for the offphase hold envelope.

The original development used the numeric prefactor `4000`.  The headline
`hoff` outlet also has to pay finite-state read/recovery constants; keeping the
same exponential rate but allowing a polynomial-in-cardinality prefactor makes
that scalar outlet dischargeable without changing the asymptotic statement. -/
def selectorReplicatorHoldEnvelopeCoeff : ℝ :=
  4000 + (Fintype.card UniversalLocalView : ℝ) ^ 4

theorem selectorReplicatorHoldEnvelopeCoeff_ge_4000 :
    (4000 : ℝ) ≤ selectorReplicatorHoldEnvelopeCoeff := by
  unfold selectorReplicatorHoldEnvelopeCoeff
  have hpow :
      0 ≤ (Fintype.card UniversalLocalView : ℝ) ^ 4 := by
    positivity
  linarith

theorem selectorReplicatorHoldEnvelopeCoeff_ge_eight :
    (8 : ℝ) ≤ selectorReplicatorHoldEnvelopeCoeff := by
  exact le_trans (by norm_num : (8 : ℝ) ≤ 4000)
    selectorReplicatorHoldEnvelopeCoeff_ge_4000

theorem selectorReplicatorHoldEnvelopeCoeff_nonneg :
    0 ≤ selectorReplicatorHoldEnvelopeCoeff := by
  exact le_trans (by norm_num : (0 : ℝ) ≤ 8)
    selectorReplicatorHoldEnvelopeCoeff_ge_eight

/-- Explicit offphase envelope for the z-hold leakage after the write/read
time.  The rate is the concrete `bgpParams38` gap
`cμ * (1/2)^L - cα = 200`. -/
def selectorReplicatorHoldEnvelope (j : ℕ) : ℝ :=
  selectorReplicatorHoldEnvelopeCoeff *
    Real.exp (-((bgpParams38.cμ * (1 / 2 : ℝ) ^ bgpParams38.L - bgpParams38.cα) *
      (2 * Real.pi * (j : ℝ) + Real.pi)))

theorem selectorReplicatorHoldEnvelope_nonneg (j : ℕ) :
    0 ≤ selectorReplicatorHoldEnvelope j := by
  unfold selectorReplicatorHoldEnvelope
  exact mul_nonneg selectorReplicatorHoldEnvelopeCoeff_nonneg (Real.exp_pos _).le

/-- The explicit hold envelope tends to zero. -/
theorem selectorReplicatorHoldEnvelope_tendsto_zero :
    Tendsto selectorReplicatorHoldEnvelope atTop (𝓝 0) := by
  have hlin : Tendsto (fun j : ℕ => (2 * Real.pi) * (j : ℝ) + Real.pi) atTop atTop := by
    have hbase : Tendsto (fun j : ℕ => (2 * Real.pi) * (j : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.const_mul_atTop (by positivity : (0 : ℝ) < 2 * Real.pi)
    exact Filter.tendsto_atTop_add_const_right atTop Real.pi hbase
  have hscaled :
      Tendsto (fun j : ℕ =>
        (bgpParams38.cμ * (1 / 2 : ℝ) ^ bgpParams38.L - bgpParams38.cα) *
          (2 * Real.pi * (j : ℝ) + Real.pi))
        atTop atTop :=
    hlin.const_mul_atTop bgpParams38_chi_regime
  have hneg :
      Tendsto (fun j : ℕ =>
        -((bgpParams38.cμ * (1 / 2 : ℝ) ^ bgpParams38.L - bgpParams38.cα) *
          (2 * Real.pi * (j : ℝ) + Real.pi)))
        atTop atBot :=
    Filter.tendsto_neg_atBot_iff.mpr hscaled
  have hexp :
      Tendsto
        (fun j : ℕ => Real.exp
          (-((bgpParams38.cμ * (1 / 2 : ℝ) ^ bgpParams38.L - bgpParams38.cα) *
            (2 * Real.pi * (j : ℝ) + Real.pi))))
        atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hneg
  have hmul :
      Tendsto
        (fun j : ℕ =>
          selectorReplicatorHoldEnvelopeCoeff *
            Real.exp
              (-((bgpParams38.cμ * (1 / 2 : ℝ) ^ bgpParams38.L - bgpParams38.cα) *
                (2 * Real.pi * (j : ℝ) + Real.pi))))
        atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hexp
  exact hmul

/-- Hold-drift radii vanish once they are eventually trapped between zero and
the concrete offphase envelope.  The trapping premise is the place where
`flag_drift_bound_of_offphase_envelope_repl` feeds this scalar fact. -/
theorem solMURepl_offphase_deltaHold_tendsto_zero
    {δhold : ℕ → ℕ → ℝ} (w : ℕ)
    (hδhold_nonneg : ∀ᶠ j in atTop, 0 ≤ δhold w j)
    (hδhold_le :
      ∀ᶠ j in atTop, δhold w j ≤ selectorReplicatorHoldEnvelope j) :
    Tendsto (δhold w) atTop (𝓝 0) := by
  refine squeeze_zero' hδhold_nonneg hδhold_le selectorReplicatorHoldEnvelope_tendsto_zero

/-- The explicit z-write lower bound for the concrete `M_U` parameters. -/
def solMUReplWriteIntLower (j : ℕ) : ℝ :=
  writeIntegralLbd 1 (3 / 8) ((1 - Real.sqrt 2 / 2) / 2) j

/-- The explicit z-write lower bound tends to infinity. -/
theorem solMURepl_writeIntLower_tendsto_atTop :
    Tendsto solMUReplWriteIntLower atTop atTop := by
  have h := writeIntegralLbd_tendsto_atTop
      (cμ := (1 : ℝ)) (cα := (3 / 8 : ℝ))
      (rmax := (1 - Real.sqrt 2 / 2) / 2)
      (by nlinarith [write_rate_pos])
  exact h

/-- Any write-integral lower-bound sequence that eventually dominates the
explicit schedule lower bound diverges.  In applications, `Λ w j` is chosen so
that `Λ w j ≤ ∫ A * α * bGateZ`; the separate finite-window producer supplies
the domination of this explicit lower bound. -/
theorem solMURepl_writeInt_tendsto_atTop
    {Λ : ℕ → ℕ → ℝ} (w : ℕ)
    (hΛ_lower : ∀ᶠ j in atTop, solMUReplWriteIntLower j ≤ Λ w j) :
    Tendsto (Λ w) atTop atTop := by
  exact tendsto_atTop_mono' atTop hΛ_lower solMURepl_writeIntLower_tendsto_atTop

/-- If `Λ → ∞` and the initial z-write mismatch radius is eventually bounded
and nonnegative, then `exp(-Λ) * Bz0 → 0`. -/
theorem solMURepl_expNegLambda_Bz0_tendsto_zero
    {Λ Bz0 : ℕ → ℕ → ℝ} (w : ℕ) {Bz0max : ℝ}
    (hΛ : Tendsto (Λ w) atTop atTop)
    (hBz0_nonneg : ∀ᶠ j in atTop, 0 ≤ Bz0 w j)
    (hBz0_bdd : ∀ᶠ j in atTop, Bz0 w j ≤ Bz0max) :
    Tendsto (fun j : ℕ => selectorZWriteContraction (Λ w) (Bz0 w) j)
      atTop (𝓝 0) := by
  have hneg : Tendsto (fun j : ℕ => -(Λ w j)) atTop atBot :=
    Filter.tendsto_neg_atBot_iff.mpr hΛ
  have hexp : Tendsto (fun j : ℕ => Real.exp (-(Λ w j))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hneg
  have hupper :
      Tendsto (fun j : ℕ => Real.exp (-(Λ w j)) * Bz0max) atTop (𝓝 0) := by
    simpa using hexp.mul tendsto_const_nhds
  refine squeeze_zero' ?_ ?_ hupper
  · filter_upwards [hBz0_nonneg] with j hBz0
    simpa [selectorZWriteContraction] using
      (mul_nonneg (Real.exp_pos (-(Λ w j))).le hBz0)
  · filter_upwards [hBz0_bdd] with j hBz0
    simpa [selectorZWriteContraction] using
      (mul_le_mul_of_nonneg_left hBz0 (Real.exp_pos (-(Λ w j))).le)

/-- Direct application of the explicit z-write lower-bound growth to the
bounded-prefactor contraction term. -/
theorem solMURepl_expNegLambda_Bz0_tendsto_zero_of_writeInt
    {Λ Bz0 : ℕ → ℕ → ℝ} (w : ℕ) {Bz0max : ℝ}
    (hΛ_lower : ∀ᶠ j in atTop, solMUReplWriteIntLower j ≤ Λ w j)
    (hBz0_nonneg : ∀ᶠ j in atTop, 0 ≤ Bz0 w j)
    (hBz0_bdd : ∀ᶠ j in atTop, Bz0 w j ≤ Bz0max) :
    Tendsto (fun j : ℕ => selectorZWriteContraction (Λ w) (Bz0 w) j)
      atTop (𝓝 0) :=
  solMURepl_expNegLambda_Bz0_tendsto_zero w
    (solMURepl_writeInt_tendsto_atTop w hΛ_lower) hBz0_nonneg hBz0_bdd

#print axioms selectorReplicatorHoldEnvelope_tendsto_zero
#print axioms solMURepl_offphase_deltaHold_tendsto_zero
#print axioms solMURepl_writeIntLower_tendsto_atTop
#print axioms solMURepl_writeInt_tendsto_atTop
#print axioms solMURepl_expNegLambda_Bz0_tendsto_zero
#print axioms solMURepl_expNegLambda_Bz0_tendsto_zero_of_writeInt

end Ripple.BoundedUniversality.BGP
