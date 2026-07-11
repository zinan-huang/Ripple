/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Doty Lemma 6.16: total dyadic-mass cancellation core

This is the total-mass sibling of `Lemma617Minority`.  It reuses the same
kernel-native cancellation clock and the same phase-3 same-exponent rectangle.
The only difference is the deterministic readout: after `D` same-exponent
cancellations, total dyadic mass has dropped by `2 * D * 2^{-h}`.

The file deliberately keeps the phase-3 row inputs explicit: count floors,
same-exponent counter support, and the mass-drop readout are hypotheses of the
per-row theorem.  The six-row wrapper is only the union-bound composition.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Phase3SameExpRect
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace ExactMajority
namespace Lemma616TotalMass

variable {Ω : Type*}

noncomputable def totalMassBad (mu : Ω → ℝ) (h : ℕ) (rho M : ℝ) : Set Ω :=
  {x | rho * M * (2 : ℝ) ^ (-(h : ℤ)) < mu x}

def sixUnion (S0 S1 S2 S3 S4 S5 : Set Ω) : Set Ω :=
  Lemma617Minority.sixUnion S0 S1 S2 S3 S4 S5

def sixSum (a0 a1 a2 a3 a4 a5 : ℝ≥0∞) : ℝ≥0∞ :=
  Lemma617Minority.sixSum a0 a1 a2 a3 a4 a5

namespace Constants

noncomputable section

def rho_early : ℝ := 1 / 10
def rho_lm5 : ℝ := 1 / 10
def rho_lm4 : ℝ := 13 / 125
def rho_lm3 : ℝ := 13 / 100
def rho_lm2 : ℝ := 53 / 250
def rho_lm1 : ℝ := 51 / 125
def rho_l : ℝ := 101 / 125

def d_lm5 : ℝ := 1 / 20
def d_lm4 : ℝ := 6 / 125
def d_lm3 : ℝ := 39 / 1000
def d_lm2 : ℝ := 3 / 125
def d_lm1 : ℝ := 1 / 125
def d_l : ℝ := 1 / 250

def a_lm5 : ℝ := 9 / 80
def b_lm5 : ℝ := 843 / 10000
def a_lm4 : ℝ := 1 / 8
def b_lm4 : ℝ := 359 / 5000
def a_lm3 : ℝ := 77 / 500
def b_lm3 : ℝ := 127 / 2500
def a_lm2 : ℝ := 23 / 100
def b_lm2 : ℝ := 67 / 2500
def a_lm1 : ℝ := 103 / 250
def b_lm1 : ℝ := 11 / 1250
def a_l : ℝ := 101 / 125
def b_l : ℝ := 3 / 625

end

end Constants

section StatedFirst

variable {L K : ℕ}

/-- The Lemma-6.16 same-exponent per-row total-mass tail.  The only
deterministic readout needed beyond the 6.17 cancellation clock is that each
counted cancellation removes `2 * 2^{-h}` total dyadic mass. -/
theorem perRow_totalMass_tail
    (σ : Sign) (idx : Fin (L + 1)) (mu : Config (AgentState L K) → ℝ)
    (C : Config (AgentState L K) → ℕ)
    (A0 B0 n D T h : ℕ) (prevRho d rho M : ℝ) (x0 : Config (AgentState L K))
    (hC0 : C x0 = 0)
    (hn : 2 ≤ n) (hD : D < B0) (hBA : B0 ≤ A0)
    (hqle :
      ∀ i : Fin D, CancelClockConcentration.twoSidedQ A0 B0 n D i ≤ 1)
    (hcard : ∀ x, C x < D → x.card = n)
    (hstep :
      ∀ x, C x < D →
        ∀ᵐ y ∂((NonuniformMajority L K).transitionKernel x),
          C y = C x ∨ C y = C x + 1)
    (hAfloor :
      ∀ x (_ : C x < D),
        ((A0 - C x : ℕ) : ℝ) ≤ Phase3SameExpRect.majorityCount (L := L) (K := K) σ idx x)
    (hBfloor :
      ∀ x (_ : C x < D),
        ((B0 - C x : ℕ) : ℝ) ≤ Phase3SameExpRect.minorityCount (L := L) (K := K) σ idx x)
    (hCinc :
      ∀ x (_ : C x < D),
        ∀ p ∈ Phase3SameExpRect.sameExpCancelPairs (L := L) (K := K) x σ idx,
          C ((NonuniformMajority L K).scheduledStep x p) = C x + 1)
    (hT :
      CancelClockConcentration.integratedInvRateClock D
        (CancelClockConcentration.twoSidedQ A0 B0 n D) D ≤ (T : ℝ))
    (hM : 0 ≤ M)
    (hDmass : d * M ≤ (D : ℝ))
    (hcoeff : 2 * prevRho - 2 * d ≤ rho)
    (hdrop :
      ∀ x,
        mu x ≤ (2 * prevRho) * M * (2 : ℝ) ^ (-(h : ℤ)) -
          2 * (C x : ℝ) * (2 : ℝ) ^ (-(h : ℤ))) :
    (CancelClockConcentration.stoppedKernel
        (NonuniformMajority L K).transitionKernel C D ^ T) x0
        (totalMassBad mu h rho M)
      ≤ ENNReal.ofReal (Real.exp
          (-(((T : ℝ) -
              CancelClockConcentration.integratedInvRateClock D
                (CancelClockConcentration.twoSidedQ A0 B0 n D) D) ^ 2)
            / (2 * (T : ℝ) *
                (CancelClockConcentration.invRateSlack D
                  (CancelClockConcentration.twoSidedQ A0 B0 n D)) ^ 2))) := by
  let scale : ℝ := (2 : ℝ) ^ (-(h : ℤ))
  have hscale : 0 ≤ scale := by
    unfold scale
    positivity
  have hprod : 0 ≤ M * scale := mul_nonneg hM hscale
  have hcoeff_scaled :
      (2 * prevRho - 2 * d) * M * scale ≤ rho * M * scale := by
    have h := mul_le_mul_of_nonneg_right hcoeff hprod
    simpa [mul_assoc] using h
  have hreadout :
      ∀ x, D ≤ C x → mu x ≤ rho * M * (2 : ℝ) ^ (-(h : ℤ)) := by
    intro x hx
    have hDleR : (D : ℝ) ≤ C x := by
      exact_mod_cast hx
    have hdC : d * M ≤ (C x : ℝ) := hDmass.trans hDleR
    have hcancel :
        2 * (d * M) * scale ≤ 2 * (C x : ℝ) * scale := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hdC (by norm_num)) hscale
    have htarget :
        (2 * prevRho) * M * scale - 2 * (C x : ℝ) * scale
          ≤ (2 * prevRho - 2 * d) * M * scale := by
      calc
        (2 * prevRho) * M * scale - 2 * (C x : ℝ) * scale
            ≤ (2 * prevRho) * M * scale - 2 * (d * M) * scale := by
              linarith
        _ = (2 * prevRho - 2 * d) * M * scale := by ring
    have hdropx := hdrop x
    unfold scale at hdropx htarget hcoeff_scaled
    exact hdropx.trans (htarget.trans hcoeff_scaled)
  have hsubset : totalMassBad mu h rho M ⊆ {x | C x < D} := by
    intro x hx
    change C x < D
    by_contra hnot
    have hDle : D ≤ C x := le_of_not_gt hnot
    exact (not_lt_of_ge (hreadout x hDle)) hx
  calc
    (CancelClockConcentration.stoppedKernel
        (NonuniformMajority L K).transitionKernel C D ^ T) x0
        (totalMassBad mu h rho M)
        ≤ (CancelClockConcentration.stoppedKernel
            (NonuniformMajority L K).transitionKernel C D ^ T) x0 {x | C x < D} :=
          measure_mono hsubset
    _ ≤ ENNReal.ofReal (Real.exp
          (-(((T : ℝ) -
              CancelClockConcentration.integratedInvRateClock D
                (CancelClockConcentration.twoSidedQ A0 B0 n D) D) ^ 2)
            / (2 * (T : ℝ) *
                (CancelClockConcentration.invRateSlack D
                  (CancelClockConcentration.twoSidedQ A0 B0 n D)) ^ 2))) :=
          Phase3SameExpRect.perRow_cancelClock_tail_sameExp
            (L := L) (K := K) (σ := σ) (h := idx) (C := C)
            (A0 := A0) (B0 := B0) (n := n) (D := D) (T := T)
            (x0 := x0) hC0 hn hD hBA hqle hcard hstep hAfloor hBfloor hCinc hT

/-- Six-row Lemma-6.16 total-mass wrapper. -/
theorem totalMass_le [MeasurableSpace Ω]
    (P : Measure Ω) (mu : Ω → ℝ) (ell : ℕ) (M : ℝ) (n : ℕ)
    (Row0 Row1 Row2 Row3 Row4 Row5 : Set Ω)
    (ε0 ε1 ε2 ε3 ε4 ε5 : ℝ≥0∞)
    (hcover :
      totalMassBad mu ell Constants.rho_l M
        ⊆ sixUnion Row0 Row1 Row2 Row3 Row4 Row5)
    (h0 : P Row0 ≤ ε0) (h1 : P Row1 ≤ ε1) (h2 : P Row2 ≤ ε2)
    (h3 : P Row3 ≤ ε3) (h4 : P Row4 ≤ ε4) (h5 : P Row5 ≤ ε5)
    (hbudget :
      sixSum ε0 ε1 ε2 ε3 ε4 ε5 ≤ ENNReal.ofReal (1 / (2 * (n : ℝ) ^ 2))) :
    P (totalMassBad mu ell Constants.rho_l M)
      ≤ ENNReal.ofReal (1 / (2 * (n : ℝ) ^ 2)) := by
  calc
    P (totalMassBad mu ell Constants.rho_l M)
        ≤ P (sixUnion Row0 Row1 Row2 Row3 Row4 Row5) := measure_mono hcover
    _ ≤ sixSum (P Row0) (P Row1) (P Row2) (P Row3) (P Row4) (P Row5) := by
          simpa [sixUnion, sixSum] using
            (Lemma617Minority.measure_sixUnion_le P Row0 Row1 Row2 Row3 Row4 Row5)
    _ ≤ sixSum ε0 ε1 ε2 ε3 ε4 ε5 := by
          unfold sixSum Lemma617Minority.sixSum
          exact add_le_add h0
            (add_le_add h1
              (add_le_add h2
                (add_le_add h3 (add_le_add h4 h5))))
    _ ≤ ENNReal.ofReal (1 / (2 * (n : ℝ) ^ 2)) := hbudget

/-- Export for the Lemma-6.15 carry: `rho_{ell-1}=0.408`, and after four
`0.001` slack charges the carried start is `0.412`. -/
theorem rho_lm1_export :
    Constants.rho_lm1 = (0.408 : ℝ) ∧
      Constants.rho_lm1 + 4 * (1 / 1000 : ℝ) = (0.412 : ℝ) := by
  constructor
  · norm_num [Constants.rho_lm1]
  · norm_num [Constants.rho_lm1]

end StatedFirst

namespace Constants

noncomputable section

theorem row_lm5_table_closes :
    2 * rho_early - 2 * d_lm5 = rho_lm5 := by
  norm_num [rho_early, rho_lm5, d_lm5]

theorem row_lm4_table_closes :
    2 * rho_lm5 - 2 * d_lm4 = rho_lm4 := by
  norm_num [rho_lm5, d_lm4, rho_lm4]

theorem row_lm3_table_closes :
    2 * rho_lm4 - 2 * d_lm3 = rho_lm3 := by
  norm_num [rho_lm4, d_lm3, rho_lm3]

theorem row_lm2_table_closes :
    2 * rho_lm3 - 2 * d_lm2 = rho_lm2 := by
  norm_num [rho_lm3, d_lm2, rho_lm2]

theorem row_lm1_table_closes :
    2 * rho_lm2 - 2 * d_lm1 = rho_lm1 := by
  norm_num [rho_lm2, d_lm1, rho_lm1]

theorem row_l_table_closes :
    2 * rho_lm1 - 2 * d_l = rho_l := by
  norm_num [rho_lm1, d_l, rho_l]

theorem rho_lm3_eq_013 :
    rho_lm3 = (0.13 : ℝ) := by
  norm_num [rho_lm3]

theorem rho_lm1_eq_0408 :
    rho_lm1 = (0.408 : ℝ) := by
  norm_num [rho_lm1]

theorem rho_l_eq_0808 :
    rho_l = (0.808 : ℝ) := by
  norm_num [rho_l]

/-- The Lemma-6.15 start constant: `0.408 + 4*0.001 = 0.412`. -/
theorem rho_lm1_plus_phi_slack_eq_0412 :
    rho_lm1 + 4 * (1 / 1000 : ℝ) = (0.412 : ℝ) := by
  norm_num [rho_lm1]

end

end Constants

section PerRow

variable [MeasurableSpace Ω] [DiscreteMeasurableSpace Ω] [DiscreteMeasurableSpace (ℕ × Ω)]

omit [MeasurableSpace Ω] [DiscreteMeasurableSpace Ω] [DiscreteMeasurableSpace (ℕ × Ω)] in
/-- If the deterministic row readout says every state with at least `D`
cancellations has the target total mass, the bad total-mass event is contained
in the active cancellation event. -/
theorem totalMassBad_subset_active_of_readout
    (mu : Ω → ℝ) (C : Ω → ℕ) (h D : ℕ) (rho M : ℝ)
    (hreadout :
      ∀ x, D ≤ C x → mu x ≤ rho * M * (2 : ℝ) ^ (-(h : ℤ))) :
    totalMassBad mu h rho M ⊆ {x | C x < D} := by
  intro x hx
  change C x < D
  by_contra hnot
  have hDle : D ≤ C x := le_of_not_gt hnot
  exact (not_lt_of_ge (hreadout x hDle)) hx

omit [MeasurableSpace Ω] [DiscreteMeasurableSpace Ω] [DiscreteMeasurableSpace (ℕ × Ω)] in
/-- Cancellation-count readout for total mass.  If `C x` counted cancellations
have each removed `2 * 2^{-h}` mass from an initial coefficient
`startCoeff`, and `D` represents at least `d * M` cancellations, then reaching
`D` implies the coefficient `startCoeff - 2*d`. -/
theorem totalMass_readout_of_cancel_drop
    (mu : Ω → ℝ) (C : Ω → ℕ) (D h : ℕ) (startCoeff d M : ℝ)
    (hDmass : d * M ≤ (D : ℝ))
    (hdrop :
      ∀ x,
        mu x ≤ startCoeff * M * (2 : ℝ) ^ (-(h : ℤ)) -
          2 * (C x : ℝ) * (2 : ℝ) ^ (-(h : ℤ))) :
    ∀ x, D ≤ C x →
      mu x ≤ (startCoeff - 2 * d) * M * (2 : ℝ) ^ (-(h : ℤ)) := by
  intro x hDle
  let scale : ℝ := (2 : ℝ) ^ (-(h : ℤ))
  have hscale : 0 ≤ scale := by
    unfold scale
    positivity
  have hDleR : (D : ℝ) ≤ C x := by
    exact_mod_cast hDle
  have hdC : d * M ≤ (C x : ℝ) := hDmass.trans hDleR
  have hcancel :
      2 * (d * M) * scale ≤ 2 * (C x : ℝ) * scale := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hdC (by norm_num)) hscale
  have htarget :
      startCoeff * M * scale - 2 * (C x : ℝ) * scale
        ≤ (startCoeff - 2 * d) * M * scale := by
    calc
      startCoeff * M * scale - 2 * (C x : ℝ) * scale
          ≤ startCoeff * M * scale - 2 * (d * M) * scale := by
            linarith
      _ = (startCoeff - 2 * d) * M * scale := by ring
  exact (hdrop x).trans htarget

/-- Protocol-free per-row total-mass tail: cancellation concentration plus the
row readout gives the target total-mass bound. -/
theorem perRow_totalMassBad_tail
    (K : Kernel Ω Ω) [IsMarkovKernel K]
    (mu : Ω → ℝ) (C A B : Ω → ℕ)
    (A0 B0 n D T h : ℕ) (rho M : ℝ) (x0 : Ω)
    (hC0 : C x0 = 0)
    (hn : 2 ≤ n) (hD : D < B0) (hBA : B0 ≤ A0)
    (hqle :
      ∀ i : Fin D, CancelClockConcentration.twoSidedQ A0 B0 n D i ≤ 1)
    (hstep :
      ∀ x, C x < D → ∀ᵐ y ∂(K x), C y = C x ∨ C y = C x + 1)
    (hAfloor :
      ∀ x (_ : C x < D), ((A0 - C x : ℕ) : ℝ) ≤ A x)
    (hBfloor :
      ∀ x (_ : C x < D), ((B0 - C x : ℕ) : ℝ) ≤ B x)
    (hpair :
      ∀ x (_ : C x < D),
        (2 * (A x : ℝ) * (B x : ℝ)) / ((n : ℝ) * (n - 1 : ℕ))
          ≤ (K x).real {y | C y = C x + 1})
    (hT :
      CancelClockConcentration.integratedInvRateClock D
        (CancelClockConcentration.twoSidedQ A0 B0 n D) D ≤ (T : ℝ))
    (hreadout :
      ∀ x, D ≤ C x → mu x ≤ rho * M * (2 : ℝ) ^ (-(h : ℤ))) :
    (CancelClockConcentration.stoppedKernel K C D ^ T) x0
        (totalMassBad mu h rho M)
      ≤ ENNReal.ofReal (Real.exp
          (-(((T : ℝ) -
              CancelClockConcentration.integratedInvRateClock D
                (CancelClockConcentration.twoSidedQ A0 B0 n D) D) ^ 2)
            / (2 * (T : ℝ) *
                (CancelClockConcentration.invRateSlack D
                  (CancelClockConcentration.twoSidedQ A0 B0 n D)) ^ 2))) := by
  calc
    (CancelClockConcentration.stoppedKernel K C D ^ T) x0
        (totalMassBad mu h rho M)
        ≤ (CancelClockConcentration.stoppedKernel K C D ^ T) x0 {x | C x < D} :=
          measure_mono
            (totalMassBad_subset_active_of_readout
              (mu := mu) (C := C) (h := h) (D := D)
              (rho := rho) (M := M) hreadout)
    _ ≤ ENNReal.ofReal (Real.exp
          (-(((T : ℝ) -
              CancelClockConcentration.integratedInvRateClock D
                (CancelClockConcentration.twoSidedQ A0 B0 n D) D) ^ 2)
            / (2 * (T : ℝ) *
                (CancelClockConcentration.invRateSlack D
                  (CancelClockConcentration.twoSidedQ A0 B0 n D)) ^ 2))) :=
          Lemma617Minority.perRow_cancelClock_tail
            (K := K) (C := C) (A := A) (B := B)
            (A0 := A0) (B0 := B0) (n := n) (D := D) (T := T)
            (x0 := x0) hC0 hn hD hBA hqle hstep hAfloor hBfloor hpair hT

/-- Per-row total-mass tail with the coefficient recurrence exposed.  The row
readout may be proved at the sharper coefficient `2*prevRho - 2*d`; the row
table only has to prove `2*prevRho - 2*d <= rho`. -/
theorem perRow_totalMassBad_tail_of_coeff_readout
    (K : Kernel Ω Ω) [IsMarkovKernel K]
    (mu : Ω → ℝ) (C A B : Ω → ℕ)
    (A0 B0 n D T h : ℕ) (prevRho d rho M : ℝ) (x0 : Ω)
    (hC0 : C x0 = 0)
    (hn : 2 ≤ n) (hD : D < B0) (hBA : B0 ≤ A0)
    (hqle :
      ∀ i : Fin D, CancelClockConcentration.twoSidedQ A0 B0 n D i ≤ 1)
    (hstep :
      ∀ x, C x < D → ∀ᵐ y ∂(K x), C y = C x ∨ C y = C x + 1)
    (hAfloor :
      ∀ x (_ : C x < D), ((A0 - C x : ℕ) : ℝ) ≤ A x)
    (hBfloor :
      ∀ x (_ : C x < D), ((B0 - C x : ℕ) : ℝ) ≤ B x)
    (hpair :
      ∀ x (_ : C x < D),
        (2 * (A x : ℝ) * (B x : ℝ)) / ((n : ℝ) * (n - 1 : ℕ))
          ≤ (K x).real {y | C y = C x + 1})
    (hT :
      CancelClockConcentration.integratedInvRateClock D
        (CancelClockConcentration.twoSidedQ A0 B0 n D) D ≤ (T : ℝ))
    (hM : 0 ≤ M)
    (hcoeff : 2 * prevRho - 2 * d ≤ rho)
    (hreadout :
      ∀ x, D ≤ C x →
        mu x ≤ (2 * prevRho - 2 * d) * M * (2 : ℝ) ^ (-(h : ℤ))) :
    (CancelClockConcentration.stoppedKernel K C D ^ T) x0
        (totalMassBad mu h rho M)
      ≤ ENNReal.ofReal (Real.exp
          (-(((T : ℝ) -
              CancelClockConcentration.integratedInvRateClock D
                (CancelClockConcentration.twoSidedQ A0 B0 n D) D) ^ 2)
            / (2 * (T : ℝ) *
                (CancelClockConcentration.invRateSlack D
                  (CancelClockConcentration.twoSidedQ A0 B0 n D)) ^ 2))) := by
  let scale : ℝ := (2 : ℝ) ^ (-(h : ℤ))
  have hscale : 0 ≤ scale := by
    unfold scale
    positivity
  have hprod : 0 ≤ M * scale := mul_nonneg hM hscale
  have hcoeff_scaled :
      (2 * prevRho - 2 * d) * M * scale ≤ rho * M * scale := by
    have h := mul_le_mul_of_nonneg_right hcoeff hprod
    simpa [mul_assoc] using h
  have hreadout_target :
      ∀ x, D ≤ C x → mu x ≤ rho * M * (2 : ℝ) ^ (-(h : ℤ)) := by
    intro x hx
    have hxread := hreadout x hx
    unfold scale at hcoeff_scaled
    exact hxread.trans hcoeff_scaled
  exact perRow_totalMassBad_tail
    (K := K) (mu := mu) (C := C) (A := A) (B := B)
    (A0 := A0) (B0 := B0) (n := n) (D := D) (T := T) (h := h)
    (rho := rho) (M := M) (x0 := x0)
    hC0 hn hD hBA hqle hstep hAfloor hBfloor hpair hT hreadout_target

end PerRow

section SameExpPerRow

variable {L K : ℕ}

/-- Phase-3 same-exponent per-row total-mass tail.  This is the Lemma-6.16
row core with the H3 ordered-pair bridge supplied by `Phase3SameExpRect`. -/
theorem perRow_totalMassBad_tail_sameExp
    (σ : Sign) (idx : Fin (L + 1)) (mu : Config (AgentState L K) → ℝ)
    (C : Config (AgentState L K) → ℕ)
    (A0 B0 n D T h : ℕ) (rho M : ℝ) (x0 : Config (AgentState L K))
    (hC0 : C x0 = 0)
    (hn : 2 ≤ n) (hD : D < B0) (hBA : B0 ≤ A0)
    (hqle :
      ∀ i : Fin D, CancelClockConcentration.twoSidedQ A0 B0 n D i ≤ 1)
    (hcard : ∀ x, C x < D → x.card = n)
    (hstep :
      ∀ x, C x < D →
        ∀ᵐ y ∂((NonuniformMajority L K).transitionKernel x),
          C y = C x ∨ C y = C x + 1)
    (hAfloor :
      ∀ x (_ : C x < D),
        ((A0 - C x : ℕ) : ℝ) ≤ Phase3SameExpRect.majorityCount (L := L) (K := K) σ idx x)
    (hBfloor :
      ∀ x (_ : C x < D),
        ((B0 - C x : ℕ) : ℝ) ≤ Phase3SameExpRect.minorityCount (L := L) (K := K) σ idx x)
    (hCinc :
      ∀ x (_ : C x < D),
        ∀ p ∈ Phase3SameExpRect.sameExpCancelPairs (L := L) (K := K) x σ idx,
          C ((NonuniformMajority L K).scheduledStep x p) = C x + 1)
    (hT :
      CancelClockConcentration.integratedInvRateClock D
        (CancelClockConcentration.twoSidedQ A0 B0 n D) D ≤ (T : ℝ))
    (hreadout :
      ∀ x, D ≤ C x → mu x ≤ rho * M * (2 : ℝ) ^ (-(h : ℤ))) :
    (CancelClockConcentration.stoppedKernel
        (NonuniformMajority L K).transitionKernel C D ^ T) x0
        (totalMassBad mu h rho M)
      ≤ ENNReal.ofReal (Real.exp
          (-(((T : ℝ) -
              CancelClockConcentration.integratedInvRateClock D
                (CancelClockConcentration.twoSidedQ A0 B0 n D) D) ^ 2)
            / (2 * (T : ℝ) *
                (CancelClockConcentration.invRateSlack D
                  (CancelClockConcentration.twoSidedQ A0 B0 n D)) ^ 2))) := by
  calc
    (CancelClockConcentration.stoppedKernel
        (NonuniformMajority L K).transitionKernel C D ^ T) x0
        (totalMassBad mu h rho M)
        ≤ (CancelClockConcentration.stoppedKernel
            (NonuniformMajority L K).transitionKernel C D ^ T) x0 {x | C x < D} :=
          measure_mono
            (totalMassBad_subset_active_of_readout
              (mu := mu) (C := C) (h := h) (D := D)
              (rho := rho) (M := M) hreadout)
    _ ≤ ENNReal.ofReal (Real.exp
          (-(((T : ℝ) -
              CancelClockConcentration.integratedInvRateClock D
                (CancelClockConcentration.twoSidedQ A0 B0 n D) D) ^ 2)
            / (2 * (T : ℝ) *
                (CancelClockConcentration.invRateSlack D
                  (CancelClockConcentration.twoSidedQ A0 B0 n D)) ^ 2))) :=
          Phase3SameExpRect.perRow_cancelClock_tail_sameExp
            (L := L) (K := K) (σ := σ) (h := idx) (C := C)
            (A0 := A0) (B0 := B0) (n := n) (D := D) (T := T)
            (x0 := x0) hC0 hn hD hBA hqle hcard hstep hAfloor hBfloor hCinc hT

/-- Same-exponent per-row tail with the 6.16 coefficient recurrence exposed. -/
theorem perRow_totalMassBad_tail_sameExp_of_coeff_readout
    (σ : Sign) (idx : Fin (L + 1)) (mu : Config (AgentState L K) → ℝ)
    (C : Config (AgentState L K) → ℕ)
    (A0 B0 n D T h : ℕ) (prevRho d rho M : ℝ) (x0 : Config (AgentState L K))
    (hC0 : C x0 = 0)
    (hn : 2 ≤ n) (hD : D < B0) (hBA : B0 ≤ A0)
    (hqle :
      ∀ i : Fin D, CancelClockConcentration.twoSidedQ A0 B0 n D i ≤ 1)
    (hcard : ∀ x, C x < D → x.card = n)
    (hstep :
      ∀ x, C x < D →
        ∀ᵐ y ∂((NonuniformMajority L K).transitionKernel x),
          C y = C x ∨ C y = C x + 1)
    (hAfloor :
      ∀ x (_ : C x < D),
        ((A0 - C x : ℕ) : ℝ) ≤ Phase3SameExpRect.majorityCount (L := L) (K := K) σ idx x)
    (hBfloor :
      ∀ x (_ : C x < D),
        ((B0 - C x : ℕ) : ℝ) ≤ Phase3SameExpRect.minorityCount (L := L) (K := K) σ idx x)
    (hCinc :
      ∀ x (_ : C x < D),
        ∀ p ∈ Phase3SameExpRect.sameExpCancelPairs (L := L) (K := K) x σ idx,
          C ((NonuniformMajority L K).scheduledStep x p) = C x + 1)
    (hT :
      CancelClockConcentration.integratedInvRateClock D
        (CancelClockConcentration.twoSidedQ A0 B0 n D) D ≤ (T : ℝ))
    (hM : 0 ≤ M)
    (hcoeff : 2 * prevRho - 2 * d ≤ rho)
    (hreadout :
      ∀ x, D ≤ C x →
        mu x ≤ (2 * prevRho - 2 * d) * M * (2 : ℝ) ^ (-(h : ℤ))) :
    (CancelClockConcentration.stoppedKernel
        (NonuniformMajority L K).transitionKernel C D ^ T) x0
        (totalMassBad mu h rho M)
      ≤ ENNReal.ofReal (Real.exp
          (-(((T : ℝ) -
              CancelClockConcentration.integratedInvRateClock D
                (CancelClockConcentration.twoSidedQ A0 B0 n D) D) ^ 2)
            / (2 * (T : ℝ) *
                (CancelClockConcentration.invRateSlack D
                  (CancelClockConcentration.twoSidedQ A0 B0 n D)) ^ 2))) := by
  let scale : ℝ := (2 : ℝ) ^ (-(h : ℤ))
  have hscale : 0 ≤ scale := by
    unfold scale
    positivity
  have hprod : 0 ≤ M * scale := mul_nonneg hM hscale
  have hcoeff_scaled :
      (2 * prevRho - 2 * d) * M * scale ≤ rho * M * scale := by
    have h := mul_le_mul_of_nonneg_right hcoeff hprod
    simpa [mul_assoc] using h
  have hreadout_target :
      ∀ x, D ≤ C x → mu x ≤ rho * M * (2 : ℝ) ^ (-(h : ℤ)) := by
    intro x hx
    have hxread := hreadout x hx
    unfold scale at hcoeff_scaled
    exact hxread.trans hcoeff_scaled
  exact perRow_totalMassBad_tail_sameExp
    (L := L) (K := K) (σ := σ) (idx := idx) (mu := mu) (C := C)
    (A0 := A0) (B0 := B0) (n := n) (D := D) (T := T) (h := h)
    (rho := rho) (M := M) (x0 := x0)
    hC0 hn hD hBA hqle hcard hstep hAfloor hBfloor hCinc hT hreadout_target

/-- Same-exponent per-row tail where the readout is obtained from the counted
cancellations removing total mass. -/
theorem perRow_totalMassBad_tail_sameExp_of_cancel_drop
    (σ : Sign) (idx : Fin (L + 1)) (mu : Config (AgentState L K) → ℝ)
    (C : Config (AgentState L K) → ℕ)
    (A0 B0 n D T h : ℕ) (prevRho d rho M : ℝ) (x0 : Config (AgentState L K))
    (hC0 : C x0 = 0)
    (hn : 2 ≤ n) (hD : D < B0) (hBA : B0 ≤ A0)
    (hqle :
      ∀ i : Fin D, CancelClockConcentration.twoSidedQ A0 B0 n D i ≤ 1)
    (hcard : ∀ x, C x < D → x.card = n)
    (hstep :
      ∀ x, C x < D →
        ∀ᵐ y ∂((NonuniformMajority L K).transitionKernel x),
          C y = C x ∨ C y = C x + 1)
    (hAfloor :
      ∀ x (_ : C x < D),
        ((A0 - C x : ℕ) : ℝ) ≤ Phase3SameExpRect.majorityCount (L := L) (K := K) σ idx x)
    (hBfloor :
      ∀ x (_ : C x < D),
        ((B0 - C x : ℕ) : ℝ) ≤ Phase3SameExpRect.minorityCount (L := L) (K := K) σ idx x)
    (hCinc :
      ∀ x (_ : C x < D),
        ∀ p ∈ Phase3SameExpRect.sameExpCancelPairs (L := L) (K := K) x σ idx,
          C ((NonuniformMajority L K).scheduledStep x p) = C x + 1)
    (hT :
      CancelClockConcentration.integratedInvRateClock D
        (CancelClockConcentration.twoSidedQ A0 B0 n D) D ≤ (T : ℝ))
    (hM : 0 ≤ M)
    (hDmass : d * M ≤ (D : ℝ))
    (hcoeff : 2 * prevRho - 2 * d ≤ rho)
    (hdrop :
      ∀ x,
        mu x ≤ (2 * prevRho) * M * (2 : ℝ) ^ (-(h : ℤ)) -
          2 * (C x : ℝ) * (2 : ℝ) ^ (-(h : ℤ))) :
    (CancelClockConcentration.stoppedKernel
        (NonuniformMajority L K).transitionKernel C D ^ T) x0
        (totalMassBad mu h rho M)
      ≤ ENNReal.ofReal (Real.exp
          (-(((T : ℝ) -
              CancelClockConcentration.integratedInvRateClock D
                (CancelClockConcentration.twoSidedQ A0 B0 n D) D) ^ 2)
            / (2 * (T : ℝ) *
                (CancelClockConcentration.invRateSlack D
                  (CancelClockConcentration.twoSidedQ A0 B0 n D)) ^ 2))) := by
  have hreadout :
      ∀ x, D ≤ C x →
        mu x ≤ (2 * prevRho - 2 * d) * M * (2 : ℝ) ^ (-(h : ℤ)) :=
    totalMass_readout_of_cancel_drop
      (mu := mu) (C := C) (D := D) (h := h) (startCoeff := 2 * prevRho)
      (d := d) (M := M) hDmass hdrop
  exact perRow_totalMassBad_tail_sameExp_of_coeff_readout
    (L := L) (K := K) (σ := σ) (idx := idx) (mu := mu) (C := C)
    (A0 := A0) (B0 := B0) (n := n) (D := D) (T := T) (h := h)
    (prevRho := prevRho) (d := d) (rho := rho) (M := M) (x0 := x0)
    hC0 hn hD hBA hqle hcard hstep hAfloor hBfloor hCinc hT hM hcoeff hreadout

end SameExpPerRow

section SixRows

variable [MeasurableSpace Ω]

/-- Union bound for the six Lemma 6.16 rows. -/
theorem measure_sixUnion_le
    (P : Measure Ω) (S0 S1 S2 S3 S4 S5 : Set Ω) :
    P (sixUnion S0 S1 S2 S3 S4 S5)
      ≤ sixSum (P S0) (P S1) (P S2) (P S3) (P S4) (P S5) := by
  simpa [sixUnion, sixSum] using
    (Lemma617Minority.measure_sixUnion_le P S0 S1 S2 S3 S4 S5)

/-- Six-row chain: if the final total-mass bad event is covered by the six row
failures and the row tails fit the global budget, then the final 6.16 target
holds with that budget. -/
theorem sixRow_chain
    (P : Measure Ω) (mu : Ω → ℝ) (ell : ℕ) (M : ℝ)
    (Row0 Row1 Row2 Row3 Row4 Row5 : Set Ω)
    (ε0 ε1 ε2 ε3 ε4 ε5 target : ℝ≥0∞)
    (hcover :
      totalMassBad mu ell Constants.rho_l M
        ⊆ sixUnion Row0 Row1 Row2 Row3 Row4 Row5)
    (h0 : P Row0 ≤ ε0) (h1 : P Row1 ≤ ε1) (h2 : P Row2 ≤ ε2)
    (h3 : P Row3 ≤ ε3) (h4 : P Row4 ≤ ε4) (h5 : P Row5 ≤ ε5)
    (hbudget : sixSum ε0 ε1 ε2 ε3 ε4 ε5 ≤ target) :
    P (totalMassBad mu ell Constants.rho_l M) ≤ target := by
  calc
    P (totalMassBad mu ell Constants.rho_l M)
        ≤ P (sixUnion Row0 Row1 Row2 Row3 Row4 Row5) := measure_mono hcover
    _ ≤ sixSum (P Row0) (P Row1) (P Row2) (P Row3) (P Row4) (P Row5) :=
          measure_sixUnion_le P Row0 Row1 Row2 Row3 Row4 Row5
    _ ≤ sixSum ε0 ε1 ε2 ε3 ε4 ε5 := by
          unfold sixSum Lemma617Minority.sixSum
          exact add_le_add h0
            (add_le_add h1
              (add_le_add h2
                (add_le_add h3 (add_le_add h4 h5))))
    _ ≤ target := hbudget

end SixRows

#print axioms totalMassBad_subset_active_of_readout
#print axioms totalMass_readout_of_cancel_drop
#print axioms perRow_totalMass_tail
#print axioms perRow_totalMassBad_tail
#print axioms perRow_totalMassBad_tail_of_coeff_readout
#print axioms perRow_totalMassBad_tail_sameExp
#print axioms perRow_totalMassBad_tail_sameExp_of_coeff_readout
#print axioms perRow_totalMassBad_tail_sameExp_of_cancel_drop
#print axioms sixRow_chain
#print axioms totalMass_le
#print axioms Constants.row_lm5_table_closes
#print axioms Constants.row_lm4_table_closes
#print axioms Constants.row_lm3_table_closes
#print axioms Constants.row_lm2_table_closes
#print axioms Constants.row_lm1_table_closes
#print axioms Constants.row_l_table_closes
#print axioms Constants.rho_lm3_eq_013
#print axioms Constants.rho_lm1_eq_0408
#print axioms Constants.rho_lm1_plus_phi_slack_eq_0412
#print axioms rho_lm1_export
#print axioms Constants.rho_l_eq_0808

end Lemma616TotalMass
end ExactMajority
