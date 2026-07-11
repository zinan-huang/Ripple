/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Doty Lemma 6.17: minority dyadic-mass cancellation core

This file is the protocol-free part of the Lemma 6.17 landing.  It applies
`CancelClockConcentration` to the same-exponent majority/minority cancellation
counter and packages the six-row failure union.  The remaining protocol bridge
is explicit in the row hypotheses: the caller must provide the same-exponent
counter support, count floors, ordered-pair success lower bound, and the
deterministic readout from `D` cancellations to the target minority mass.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.CancelClockConcentration
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace ExactMajority
namespace Lemma617Minority

variable {Ω : Type*}

noncomputable def minorityBad (βminus : Ω → ℝ) (h : ℕ) (ξ M : ℝ) : Set Ω :=
  {x | ξ * M * (2 : ℝ) ^ (-(h : ℤ)) < βminus x}

def sixUnion (S0 S1 S2 S3 S4 S5 : Set Ω) : Set Ω :=
  S0 ∪ (S1 ∪ (S2 ∪ (S3 ∪ (S4 ∪ S5))))

def sixSum (a0 a1 a2 a3 a4 a5 : ℝ≥0∞) : ℝ≥0∞ :=
  a0 + (a1 + (a2 + (a3 + (a4 + a5))))

section PerRow

variable [MeasurableSpace Ω] [DiscreteMeasurableSpace Ω] [DiscreteMeasurableSpace (ℕ × Ω)]

/-- Per-row cancellation concentration for the same-exponent two-sided count
floors.  This is the reusable kernel-native row core for Lemma 6.17. -/
theorem perRow_cancelClock_tail
    (K : Kernel Ω Ω) [IsMarkovKernel K]
    (C A B : Ω → ℕ) (A0 B0 n D T : ℕ) (x0 : Ω)
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
        (CancelClockConcentration.twoSidedQ A0 B0 n D) D ≤ (T : ℝ)) :
    (CancelClockConcentration.stoppedKernel K C D ^ T) x0 {x | C x < D}
      ≤ ENNReal.ofReal (Real.exp
          (-(((T : ℝ) -
              CancelClockConcentration.integratedInvRateClock D
                (CancelClockConcentration.twoSidedQ A0 B0 n D) D) ^ 2)
            / (2 * (T : ℝ) *
                (CancelClockConcentration.invRateSlack D
                  (CancelClockConcentration.twoSidedQ A0 B0 n D)) ^ 2))) := by
  let q := CancelClockConcentration.twoSidedQ A0 B0 n D
  have hqpos : ∀ i : Fin D, 0 < q i := by
    intro i
    simpa [q] using
      (CancelClockConcentration.twoSidedQ_pos (A₀ := A0) (B₀ := B0)
        (n := n) (D := D) hD hBA hn i)
  have hsucc :
      ∀ x (hx : C x < D),
        q ⟨C x, hx⟩ ≤ (K x).real {y | C y = C x + 1} := by
    simpa [q] using
      (CancelClockConcentration.twoSided_success_lower_bound
        (K := K) (C := C) (A := A) (B := B)
        (A₀ := A0) (B₀ := B0) (n := n) (D := D)
        hn hAfloor hBfloor hpair)
  simpa [q] using
    (CancelClockConcentration.cancelClock_concentration_stoppedKernel_canonicalL
      (K := K) (C := C) (D := D) (q := q) (x₀ := x0)
      hC0 hqpos (by simpa [q] using hqle) hstep hsucc T
      (by simpa [q] using hT))

omit [MeasurableSpace Ω] [DiscreteMeasurableSpace Ω] [DiscreteMeasurableSpace (ℕ × Ω)] in
/-- If the deterministic row readout says every state with at least `D`
cancellations has the target minority mass, the bad minority event is contained
in the active cancellation event. -/
theorem minorityBad_subset_active_of_readout
    (βminus : Ω → ℝ) (C : Ω → ℕ) (h D : ℕ) (ξ M : ℝ)
    (hreadout :
      ∀ x, D ≤ C x → βminus x ≤ ξ * M * (2 : ℝ) ^ (-(h : ℤ))) :
    minorityBad βminus h ξ M ⊆ {x | C x < D} := by
  intro x hx
  change C x < D
  by_contra hnot
  have hDle : D ≤ C x := le_of_not_gt hnot
  exact (not_lt_of_ge (hreadout x hDle)) hx

/-- Per-row minority-mass tail: cancellation concentration plus the row readout
gives the whp row target. -/
theorem perRow_minorityBad_tail
    (K : Kernel Ω Ω) [IsMarkovKernel K]
    (βminus : Ω → ℝ) (C A B : Ω → ℕ)
    (A0 B0 n D T h : ℕ) (ξ M : ℝ) (x0 : Ω)
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
      ∀ x, D ≤ C x → βminus x ≤ ξ * M * (2 : ℝ) ^ (-(h : ℤ))) :
    (CancelClockConcentration.stoppedKernel K C D ^ T) x0
        (minorityBad βminus h ξ M)
      ≤ ENNReal.ofReal (Real.exp
          (-(((T : ℝ) -
              CancelClockConcentration.integratedInvRateClock D
                (CancelClockConcentration.twoSidedQ A0 B0 n D) D) ^ 2)
            / (2 * (T : ℝ) *
                (CancelClockConcentration.invRateSlack D
                  (CancelClockConcentration.twoSidedQ A0 B0 n D)) ^ 2))) := by
  calc
    (CancelClockConcentration.stoppedKernel K C D ^ T) x0
        (minorityBad βminus h ξ M)
        ≤ (CancelClockConcentration.stoppedKernel K C D ^ T) x0 {x | C x < D} :=
          measure_mono
            (minorityBad_subset_active_of_readout
              (βminus := βminus) (C := C) (h := h) (D := D)
              (ξ := ξ) (M := M) hreadout)
    _ ≤ ENNReal.ofReal (Real.exp
          (-(((T : ℝ) -
              CancelClockConcentration.integratedInvRateClock D
                (CancelClockConcentration.twoSidedQ A0 B0 n D) D) ^ 2)
            / (2 * (T : ℝ) *
                (CancelClockConcentration.invRateSlack D
                  (CancelClockConcentration.twoSidedQ A0 B0 n D)) ^ 2))) :=
          perRow_cancelClock_tail
            (K := K) (C := C) (A := A) (B := B)
            (A0 := A0) (B0 := B0) (n := n) (D := D) (T := T)
            (x0 := x0) hC0 hn hD hBA hqle hstep hAfloor hBfloor hpair hT

/-- Per-row minority tail with the arithmetic recurrence exposed.  The row
readout may be proved at the sharper coefficient `b - d + leak`; the numeric
row table only has to prove `b - d + leak <= xi`. -/
theorem perRow_minorityBad_tail_of_coeff_readout
    (K : Kernel Ω Ω) [IsMarkovKernel K]
    (βminus : Ω → ℝ) (C A B : Ω → ℕ)
    (A0 B0 n D T h : ℕ) (b d leak ξ M : ℝ) (x0 : Ω)
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
    (hcoeff : b - d + leak ≤ ξ)
    (hreadout :
      ∀ x, D ≤ C x →
        βminus x ≤ (b - d + leak) * M * (2 : ℝ) ^ (-(h : ℤ))) :
    (CancelClockConcentration.stoppedKernel K C D ^ T) x0
        (minorityBad βminus h ξ M)
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
      (b - d + leak) * M * scale ≤ ξ * M * scale := by
    have h := mul_le_mul_of_nonneg_right hcoeff hprod
    simpa [mul_assoc] using h
  have hreadout_target :
      ∀ x, D ≤ C x → βminus x ≤ ξ * M * (2 : ℝ) ^ (-(h : ℤ)) := by
    intro x hx
    have hxread := hreadout x hx
    unfold scale at hcoeff_scaled
    exact hxread.trans hcoeff_scaled
  exact perRow_minorityBad_tail
    (K := K) (βminus := βminus) (C := C) (A := A) (B := B)
    (A0 := A0) (B0 := B0) (n := n) (D := D) (T := T) (h := h)
    (ξ := ξ) (M := M) (x0 := x0)
    hC0 hn hD hBA hqle hstep hAfloor hBfloor hpair hT hreadout_target

end PerRow

section SixRows

variable [MeasurableSpace Ω]

/-- Union bound for the six Lemma 6.17 rows. -/
theorem measure_sixUnion_le
    (μ : Measure Ω) (S0 S1 S2 S3 S4 S5 : Set Ω) :
    μ (sixUnion S0 S1 S2 S3 S4 S5)
      ≤ sixSum (μ S0) (μ S1) (μ S2) (μ S3) (μ S4) (μ S5) := by
  unfold sixUnion sixSum
  calc
    μ (S0 ∪ (S1 ∪ (S2 ∪ (S3 ∪ (S4 ∪ S5)))))
        ≤ μ S0 + μ (S1 ∪ (S2 ∪ (S3 ∪ (S4 ∪ S5)))) :=
          measure_union_le _ _
    _ ≤ μ S0 + (μ S1 + μ (S2 ∪ (S3 ∪ (S4 ∪ S5)))) := by
          gcongr
          exact measure_union_le _ _
    _ ≤ μ S0 + (μ S1 + (μ S2 + μ (S3 ∪ (S4 ∪ S5)))) := by
          gcongr
          exact measure_union_le _ _
    _ ≤ μ S0 + (μ S1 + (μ S2 + (μ S3 + μ (S4 ∪ S5)))) := by
          gcongr
          exact measure_union_le _ _
    _ ≤ μ S0 + (μ S1 + (μ S2 + (μ S3 + (μ S4 + μ S5)))) := by
          gcongr
          exact measure_union_le _ _

/-- Six-row chain: if the final bad event is covered by the six row failures
and the row tails fit the global budget, then the final minority target holds
with that budget. -/
theorem sixRow_chain
    (μ : Measure Ω) (βminus : Ω → ℝ) (ell : ℕ) (M : ℝ)
    (Row0 Row1 Row2 Row3 Row4 Row5 : Set Ω)
    (ε0 ε1 ε2 ε3 ε4 ε5 target : ℝ≥0∞)
    (hcover :
      minorityBad βminus ell (1 / 250 : ℝ) M
        ⊆ sixUnion Row0 Row1 Row2 Row3 Row4 Row5)
    (h0 : μ Row0 ≤ ε0) (h1 : μ Row1 ≤ ε1) (h2 : μ Row2 ≤ ε2)
    (h3 : μ Row3 ≤ ε3) (h4 : μ Row4 ≤ ε4) (h5 : μ Row5 ≤ ε5)
    (hbudget : sixSum ε0 ε1 ε2 ε3 ε4 ε5 ≤ target) :
    μ (minorityBad βminus ell (1 / 250 : ℝ) M) ≤ target := by
  calc
    μ (minorityBad βminus ell (1 / 250 : ℝ) M)
        ≤ μ (sixUnion Row0 Row1 Row2 Row3 Row4 Row5) := measure_mono hcover
    _ ≤ sixSum (μ Row0) (μ Row1) (μ Row2) (μ Row3) (μ Row4) (μ Row5) :=
          measure_sixUnion_le μ Row0 Row1 Row2 Row3 Row4 Row5
    _ ≤ sixSum ε0 ε1 ε2 ε3 ε4 ε5 := by
          unfold sixSum
          exact add_le_add h0
            (add_le_add h1
              (add_le_add h2
                (add_le_add h3 (add_le_add h4 h5))))
    _ ≤ target := hbudget

/-- Final Lemma 6.17 wrapper.  The six row events are the explicit carried
phase-3 inputs; the conclusion itself is not a premise. -/
theorem minorityMass_le
    (μ : Measure Ω) (βminus : Ω → ℝ) (ell : ℕ) (M : ℝ) (n : ℕ)
    (Row0 Row1 Row2 Row3 Row4 Row5 : Set Ω)
    (ε0 ε1 ε2 ε3 ε4 ε5 : ℝ≥0∞)
    (hcover :
      minorityBad βminus ell (1 / 250 : ℝ) M
        ⊆ sixUnion Row0 Row1 Row2 Row3 Row4 Row5)
    (h0 : μ Row0 ≤ ε0) (h1 : μ Row1 ≤ ε1) (h2 : μ Row2 ≤ ε2)
    (h3 : μ Row3 ≤ ε3) (h4 : μ Row4 ≤ ε4) (h5 : μ Row5 ≤ ε5)
    (hbudget :
      sixSum ε0 ε1 ε2 ε3 ε4 ε5 ≤ ENNReal.ofReal (1 / (2 * (n : ℝ) ^ 2))) :
    μ (minorityBad βminus ell (1 / 250 : ℝ) M)
      ≤ ENNReal.ofReal (1 / (2 * (n : ℝ) ^ 2)) := by
  exact sixRow_chain
    (μ := μ) (βminus := βminus) (ell := ell) (M := M)
    (Row0 := Row0) (Row1 := Row1) (Row2 := Row2)
    (Row3 := Row3) (Row4 := Row4) (Row5 := Row5)
    (ε0 := ε0) (ε1 := ε1) (ε2 := ε2)
    (ε3 := ε3) (ε4 := ε4) (ε5 := ε5)
    (target := ENNReal.ofReal (1 / (2 * (n : ℝ) ^ 2)))
    hcover h0 h1 h2 h3 h4 h5 hbudget

end SixRows

namespace Constants

noncomputable section

def xi_lm5 : ℝ := 7 / 160
def xi_lm4 : ℝ := 3 / 80
def xi_lm3 : ℝ := 267 / 10000
def xi_lm2 : ℝ := 29 / 2000
def xi_lm1 : ℝ := 7 / 1250
def xi_l : ℝ := 1 / 250

def leakBelow : ℝ := 3 / 2500
def leakAbove : ℝ := 1 / 500
def leakTotal : ℝ := leakBelow + leakAbove
/-- Largest uniform off-row minority leakage coefficient that closes all 6.17
cancellation rows.  The binding row is `ell-2`. -/
def eta617Max : ℝ := 27 / 10000
/-- Minority-specific off-row leakage budget supplied by the stopped 6.11
leakage theorem.  This is strictly smaller than the uniform maximum above. -/
def leakMinority : ℝ := 3 / 1250

def b_lm4 : ℝ := 843 / 10000
def d_lm4 : ℝ := 1 / 20
def b_lm3 : ℝ := 359 / 5000
def d_lm3 : ℝ := 6 / 125
def b_lm2 : ℝ := 127 / 2500
def d_lm2 : ℝ := 39 / 1000
def b_lm1 : ℝ := 67 / 2500
def d_lm1 : ℝ := 3 / 125
def b_l : ℝ := 11 / 1250
def d_l : ℝ := 1 / 125

theorem row_lm4_table_closes :
    b_lm4 - d_lm4 + leakTotal = xi_lm4 := by
  norm_num [b_lm4, d_lm4, leakTotal, leakBelow, leakAbove, xi_lm4]

theorem leakMinority_le_eta617Max :
    leakMinority ≤ eta617Max := by
  norm_num [leakMinority, eta617Max]

theorem eta617Max_is_uniformly_sufficient_lm4 :
    b_lm4 - d_lm4 + eta617Max ≤ xi_lm4 := by
  norm_num [b_lm4, d_lm4, eta617Max, xi_lm4]

theorem eta617Max_is_uniformly_sufficient_lm3 :
    b_lm3 - d_lm3 + eta617Max ≤ xi_lm3 := by
  norm_num [b_lm3, d_lm3, eta617Max, xi_lm3]

theorem eta617Max_is_uniformly_sufficient_lm2 :
    b_lm2 - d_lm2 + eta617Max ≤ xi_lm2 := by
  norm_num [b_lm2, d_lm2, eta617Max, xi_lm2]

theorem eta617Max_is_uniformly_sufficient_lm1 :
    b_lm1 - d_lm1 + eta617Max ≤ xi_lm1 := by
  norm_num [b_lm1, d_lm1, eta617Max, xi_lm1]

theorem eta617Max_is_uniformly_sufficient_l :
    b_l - d_l + eta617Max ≤ xi_l := by
  norm_num [b_l, d_l, eta617Max, xi_l]

theorem row_lm4_table_closes_repaired :
    b_lm4 - d_lm4 + leakMinority ≤ xi_lm4 := by
  norm_num [b_lm4, d_lm4, leakMinority, xi_lm4]

theorem row_lm3_table_excess :
    b_lm3 - d_lm3 + leakTotal = xi_lm3 + 3 / 10000 := by
  norm_num [b_lm3, d_lm3, leakTotal, leakBelow, leakAbove, xi_lm3]

theorem row_lm3_table_closes_repaired :
    b_lm3 - d_lm3 + leakMinority ≤ xi_lm3 := by
  norm_num [b_lm3, d_lm3, leakMinority, xi_lm3]

theorem row_lm3_table_not_closed :
    ¬ b_lm3 - d_lm3 + leakTotal ≤ xi_lm3 := by
  norm_num [b_lm3, d_lm3, leakTotal, leakBelow, leakAbove, xi_lm3]

theorem row_lm2_table_excess :
    b_lm2 - d_lm2 + leakTotal = xi_lm2 + 1 / 2000 := by
  norm_num [b_lm2, d_lm2, leakTotal, leakBelow, leakAbove, xi_lm2]

theorem row_lm2_table_closes_repaired :
    b_lm2 - d_lm2 + leakMinority ≤ xi_lm2 := by
  norm_num [b_lm2, d_lm2, leakMinority, xi_lm2]

theorem row_lm2_table_not_closed :
    ¬ b_lm2 - d_lm2 + leakTotal ≤ xi_lm2 := by
  norm_num [b_lm2, d_lm2, leakTotal, leakBelow, leakAbove, xi_lm2]

theorem row_lm1_table_excess :
    b_lm1 - d_lm1 + leakTotal = xi_lm1 + 1 / 2500 := by
  norm_num [b_lm1, d_lm1, leakTotal, leakBelow, leakAbove, xi_lm1]

theorem row_lm1_table_closes_repaired :
    b_lm1 - d_lm1 + leakMinority ≤ xi_lm1 := by
  norm_num [b_lm1, d_lm1, leakMinority, xi_lm1]

theorem row_lm1_table_not_closed :
    ¬ b_lm1 - d_lm1 + leakTotal ≤ xi_lm1 := by
  norm_num [b_lm1, d_lm1, leakTotal, leakBelow, leakAbove, xi_lm1]

theorem row_l_table_closes :
    b_l - d_l + leakTotal = xi_l := by
  norm_num [b_l, d_l, leakTotal, leakBelow, leakAbove, xi_l]

theorem row_l_table_closes_repaired :
    b_l - d_l + leakMinority ≤ xi_l := by
  norm_num [b_l, d_l, leakMinority, xi_l]

end

end Constants

#print axioms perRow_cancelClock_tail
#print axioms perRow_minorityBad_tail
#print axioms perRow_minorityBad_tail_of_coeff_readout
#print axioms sixRow_chain
#print axioms minorityMass_le
#print axioms Constants.leakMinority_le_eta617Max
#print axioms Constants.eta617Max_is_uniformly_sufficient_lm2
#print axioms Constants.row_lm4_table_closes_repaired
#print axioms Constants.row_lm3_table_closes_repaired
#print axioms Constants.row_lm2_table_closes_repaired
#print axioms Constants.row_lm1_table_closes_repaired
#print axioms Constants.row_l_table_closes_repaired
#print axioms Constants.row_lm3_table_not_closed
#print axioms Constants.row_lm2_table_not_closed
#print axioms Constants.row_lm1_table_not_closed

end Lemma617Minority
end ExactMajority
