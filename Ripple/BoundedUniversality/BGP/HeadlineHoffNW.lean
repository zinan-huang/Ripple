import Ripple.BoundedUniversality.BGP.HeadlineUnconditional
import Ripple.BoundedUniversality.BGP.SelectorReplicatorHoffP

/-!
# Diagonal NW Hoff field-integral assembly

This file deliberately avoids the all-inner-word carrier
`SelectorMUCycleHoffFieldIntegralResidual (bgpHeadlineSolFamNW wg)`.
Every physical statement binds one word `w`, which simultaneously selects
`bgpParamsNW w`, `bgpHeadlineSolFamNW w`, and the diagonal solution input `w`.
-/

noncomputable section

namespace Ripple.BoundedUniversality.BGP

open Set MachineInstance UniversalMachine Filter
open scoped BigOperators Topology

/-- Exact type of the concrete diagonal NW box-input package needed only for
halt-coordinate `[0,1]` trapping on the middle z-off interval. -/
abbrev Paper3HeadlineHoffBoxInputsNW (w : ℕ) :=
  MUReplicatorBoxInputsP
    (p := bgpParamsNW w)
    bgpHeadlineEta bgpHeadlineEta_pos
    bgpHeadlineM bgpHeadlineKappa (bgpWarmGainQNW w)
    (bgpHeadlineSolFamNW w)

/-- The diagonal NW absolute halt-coordinate field integrand. -/
noncomputable def bgpHeadlineHoffIntegrandNW (w : ℕ) (τ : ℝ) : ℝ :=
  selectorMUHoffIntegrandP
    (p := bgpParamsNW w) (bgpHeadlineSolFamNW w) w τ

/-- Actual left-edge field cap at the diagonal NW family. -/
noncomputable def bgpHeadlineHoffCapLeftFieldNW (w j : ℕ) : ℝ :=
  ∫ τ in (selectorMUInterReadStart j)..(selectorMUZOffStart j),
    bgpHeadlineHoffIntegrandNW w τ

/-- Actual right-edge field cap at the diagonal NW family. -/
noncomputable def bgpHeadlineHoffCapRightFieldNW (w j : ℕ) : ℝ :=
  ∫ τ in (selectorMUZOffEnd j)..(selectorMUNextWriteStart j),
    bgpHeadlineHoffIntegrandNW w τ

theorem bgpHeadlineHoffCapLeftFieldNW_nonneg (w j : ℕ) :
    0 ≤ bgpHeadlineHoffCapLeftFieldNW w j := by
  unfold bgpHeadlineHoffCapLeftFieldNW
  apply intervalIntegral.integral_nonneg
    (selectorMUInterReadStart_le_zOffStart j)
  intro τ _hτ
  exact selectorMUHoffIntegrandP_nonneg
    (p := bgpParamsNW w) (bgpHeadlineSolFamNW w) w τ

theorem bgpHeadlineHoffCapRightFieldNW_nonneg (w j : ℕ) :
    0 ≤ bgpHeadlineHoffCapRightFieldNW w j := by
  unfold bgpHeadlineHoffCapRightFieldNW
  apply intervalIntegral.integral_nonneg
    (selectorMUZOffEnd_le_nextWriteStart j)
  intro τ _hτ
  exact selectorMUHoffIntegrandP_nonneg
    (p := bgpParamsNW w) (bgpHeadlineSolFamNW w) w τ

/-- Diagonal-only NW field-integral residual.  There is no free pair `(wg,w)`:
the same `w` selects the parameter pack, solution family, and solution input. -/
structure Paper3HeadlineHoffFieldIntegralResidualNW : Prop where
  hfieldInt :
    ∀ w j,
      selectorMUHaltEncConst (solMUReplStaticCfg w) j →
      ∀ t ∈ Icc (selectorMUInterReadStart j)
          (selectorMUNextWriteStart j),
        (∫ τ in (selectorMUInterReadStart j)..t,
          bgpHeadlineHoffIntegrandNW w τ) ≤
            selectorReplicatorHoldEnvelope j

/-! ## A small rate-free prefix-integral helper -/

private theorem intervalIntegral_prefix_le_full_of_nonneg
    {f : ℝ → ℝ} {a t b : ℝ}
    (hat : a ≤ t) (htb : t ≤ b)
    (hf_cont : Continuous f)
    (hf_nonneg : ∀ x, 0 ≤ f x) :
    (∫ x in a..t, f x) ≤ ∫ x in a..b, f x := by
  have hI₁ : IntervalIntegrable f MeasureTheory.volume a t :=
    hf_cont.intervalIntegrable a t
  have hI₂ : IntervalIntegrable f MeasureTheory.volume t b :=
    hf_cont.intervalIntegrable t b
  have hadd := intervalIntegral.integral_add_adjacent_intervals hI₁ hI₂
  have htail : 0 ≤ ∫ x in t..b, f x := by
    apply intervalIntegral.integral_nonneg htb
    intro x _hx
    exact hf_nonneg x
  linarith

/-! ## NW middle cap -/

/-- Firewall identity
`cμ·(1/2)^L-cα = 200·bgpScaleW w`, inserted into the P-generic envelope.

This is the only theorem that unfolds the P-generic middle envelope.  All later
uses rewrite through this theorem rather than simplifying the definition under an
integral. -/
theorem selectorMUHoffMiddleEnvelopeP_NW_eq (w : ℕ) (τ : ℝ) :
    selectorMUHoffMiddleEnvelopeP (bgpParamsNW w) τ =
      Real.exp (-(200 * (bgpScaleW w : ℝ) * τ)) := by
  unfold selectorMUHoffMiddleEnvelopeP
  rw [bgpParamsNW_A_eq, bgpParamsNW_chi_leak_eq]
  ring

private theorem selectorMUHoffMiddleEnvelopeP_NW_integral_eq
    (w : ℕ) (a b : ℝ) :
    (∫ τ in a..b, selectorMUHoffMiddleEnvelopeP (bgpParamsNW w) τ) =
      ∫ τ in a..b, Real.exp (-(200 * (bgpScaleW w : ℝ) * τ)) := by
  have hfun :
      (fun τ : ℝ => selectorMUHoffMiddleEnvelopeP (bgpParamsNW w) τ) =
        (fun τ : ℝ => Real.exp (-(200 * (bgpScaleW w : ℝ) * τ))) := by
    funext τ
    exact selectorMUHoffMiddleEnvelopeP_NW_eq w τ
  rw [hfun]

/-- Full middle-window physical envelope cap at the word-coupled NW rate.

The cap is intentionally stored in closed exponential form.  This prevents `simp`
from trying to unfold the generic P-envelope in later interval-integral proofs. -/
noncomputable def selectorMUHoffMiddleEnvelopeFullCapNW (w j : ℕ) : ℝ :=
  ∫ τ in (selectorMUZOffStart j)..(selectorMUZOffEnd j),
    Real.exp (-(200 * (bgpScaleW w : ℝ) * τ))

theorem selectorMUHoffMiddleEnvelopeFullCapNW_nonneg (w j : ℕ) :
    0 ≤ selectorMUHoffMiddleEnvelopeFullCapNW w j := by
  unfold selectorMUHoffMiddleEnvelopeFullCapNW
  apply intervalIntegral.integral_nonneg
    (selectorMUZOffStart_le_zOffEnd j)
  intro τ _hτ
  exact (Real.exp_pos _).le

/-- Sharp infinite-tail upper bound for the finite NW middle cap. -/
theorem selectorMUHoffMiddleEnvelopeFullCapNW_le_tail (w j : ℕ) :
    selectorMUHoffMiddleEnvelopeFullCapNW w j ≤
      (1 / (200 * (bgpScaleW w : ℝ))) *
        Real.exp (-(200 * (bgpScaleW w : ℝ) *
          (2 * Real.pi * (j : ℝ) + Real.pi))) := by
  have hr : 0 < 200 * (bgpScaleW w : ℝ) := by
    nlinarith [bgpScaleWR_pos w]
  have hab : selectorMUZOffStart j ≤ selectorMUZOffEnd j :=
    selectorMUZOffStart_le_zOffEnd j
  change
    (∫ τ in (selectorMUZOffStart j)..(selectorMUZOffEnd j),
      Real.exp (-(200 * (bgpScaleW w : ℝ) * τ))) ≤
      (1 / (200 * (bgpScaleW w : ℝ))) *
        Real.exp (-(200 * (bgpScaleW w : ℝ) *
          (2 * Real.pi * (j : ℝ) + Real.pi)))
  have h := integral_const_mul_exp_neg_le_left
    (r := 200 * (bgpScaleW w : ℝ))
    (C := 1)
    (a := selectorMUZOffStart j)
    (b := selectorMUZOffEnd j)
    hr (by norm_num) hab
  simpa only [selectorMUZOffStart, one_mul] using h

/-- The NW infinite-tail currency is below the old `200`-rate tail currency.
This is an upper-bound comparison only; the RHS is not definitionally the old
finite cap. -/
theorem selectorMUHoffMiddleEnvelopeFullCapNW_tail_le_old_tail (w j : ℕ) :
    (1 / (200 * (bgpScaleW w : ℝ))) *
        Real.exp (-(200 * (bgpScaleW w : ℝ) *
          (2 * Real.pi * (j : ℝ) + Real.pi))) ≤
      (1 / 200 : ℝ) *
        Real.exp (-(200 * (2 * Real.pi * (j : ℝ) + Real.pi))) := by
  let S : ℝ := (bgpScaleW w : ℝ)
  let T : ℝ := 2 * Real.pi * (j : ℝ) + Real.pi
  have hS₁ : (1 : ℝ) ≤ S := by
    exact bgpScaleWR_ge_one w
  have hT₀ : 0 ≤ T := by
    dsimp only [T]
    nlinarith [Real.pi_pos, (Nat.cast_nonneg j : (0:ℝ) ≤ (j:ℝ))]
  have hcoef : 1 / (200 * S) ≤ (1 / 200 : ℝ) := by
    have hden : (200 : ℝ) ≤ 200 * S := by nlinarith
    exact one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 200) hden
  have hexp : Real.exp (-(200 * S * T)) ≤ Real.exp (-(200 * T)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  calc
    (1 / (200 * S)) * Real.exp (-(200 * S * T))
        ≤ (1 / 200 : ℝ) * Real.exp (-(200 * S * T)) :=
      mul_le_mul_of_nonneg_right hcoef (Real.exp_pos _).le
    _ ≤ (1 / 200 : ℝ) * Real.exp (-(200 * T)) :=
      mul_le_mul_of_nonneg_left hexp (by norm_num)

/-- Compatibility rewrite used only to compare with the frozen old-budget cap.
The upstream rewrite lemma `selectorMUHoffMiddleEnvelope_eq_exp` is private inside
`SelectorReplicatorHoffEdgeBudget`; this local firewall is the public-draft
replacement. -/
private theorem selectorMUHoffMiddleEnvelope_eq_exp200_for_NW_compare
    (τ : ℝ) :
    selectorMUHoffMiddleEnvelope τ = Real.exp (-(200 * τ)) := by
  change
    bgpParams38.A *
        Real.exp (-((bgpParams38.cμ * (1 / 2 : ℝ) ^ bgpParams38.L -
          bgpParams38.cα) * τ)) =
      Real.exp (-(200 * τ))
  have hA : bgpParams38.A = (1 : ℝ) := by
    norm_num [bgpParams38]
  have hrate :
      bgpParams38.cμ * (1 / 2 : ℝ) ^ bgpParams38.L - bgpParams38.cα = 200 := by
    norm_num [bgpParams38]
  rw [hA, hrate]
  ring

private theorem selectorMUHoffMiddleEnvelope_continuous_for_NW_compare :
    Continuous selectorMUHoffMiddleEnvelope := by
  have hfun : selectorMUHoffMiddleEnvelope =
      (fun τ : ℝ => Real.exp (-(200 * τ))) := by
    funext τ
    exact selectorMUHoffMiddleEnvelope_eq_exp200_for_NW_compare τ
  rw [hfun]
  fun_prop

/-- Correct finite-window comparison: compare the NW and old middle-envelope
integrands pointwise on the same interval. -/
theorem selectorMUHoffMiddleEnvelopeFullCapNW_le_old_middle_budget
    (w j : ℕ) :
    selectorMUHoffMiddleEnvelopeFullCapNW w j ≤
      selectorMUHoffMiddleEnvelopeFullCap j := by
  have hab : selectorMUZOffStart j ≤ selectorMUZOffEnd j :=
    selectorMUZOffStart_le_zOffEnd j
  have hstart₀ : 0 ≤ selectorMUZOffStart j := by
    unfold selectorMUZOffStart
    positivity
  have hS₁ : (1 : ℝ) ≤ (bgpScaleW w : ℝ) := bgpScaleWR_ge_one w
  unfold selectorMUHoffMiddleEnvelopeFullCapNW
  unfold selectorMUHoffMiddleEnvelopeFullCap
  apply intervalIntegral.integral_mono_on hab
  · have hcont : Continuous fun τ : ℝ =>
        Real.exp (-(200 * (bgpScaleW w : ℝ) * τ)) := by
      fun_prop
    exact hcont.intervalIntegrable _ _
  · exact selectorMUHoffMiddleEnvelope_continuous_for_NW_compare.intervalIntegrable _ _
  · intro τ hτ
    rw [selectorMUHoffMiddleEnvelope_eq_exp200_for_NW_compare]
    apply Real.exp_le_exp.mpr
    have hτ₀ : 0 ≤ τ := le_trans hstart₀ hτ.1
    nlinarith

/-- Scalar P-envelope residual used by the already-landed generic middle-field
engine.  Its first `ℕ` argument is irrelevant because the middle scalar envelope
depends only on the parameter pack. -/
private noncomputable def bgpHeadlineHoffMiddleEnvelopeResidualNW (w : ℕ) :
    SelectorMUHoffMiddleEnvelopeResidualP (bgpParamsNW w) where
  capMid := fun _ j => selectorMUHoffMiddleEnvelopeFullCapNW w j
  henvInt := by
    intro _ j t ht
    have heq := selectorMUHoffMiddleEnvelopeP_NW_integral_eq w
      (selectorMUZOffStart j) t
    rw [heq]
    exact intervalIntegral_prefix_le_full_of_nonneg
      ht.1 ht.2
      (by fun_prop)
      (by
        intro τ
        exact (Real.exp_pos _).le)

/-- Middle physical field integral.  This is independent of S2/S4; the only
state input is the standard halt-coordinate box package. -/
theorem bgpHeadlineHoff_middle_fieldIntegral_NW
    (boxInputsNW : ∀ w, Paper3HeadlineHoffBoxInputsNW w)
    (w j : ℕ) :
    ∀ t ∈ Icc (selectorMUZOffStart j) (selectorMUZOffEnd j),
      (∫ τ in (selectorMUZOffStart j)..t,
        bgpHeadlineHoffIntegrandNW w τ) ≤
          selectorMUHoffMiddleEnvelopeFullCapNW w j := by
  have hA : 0 ≤ (bgpParamsNW w).A := by
    rw [bgpParamsNW_A_eq]
    norm_num
  have hcμ : 0 ≤ (bgpParamsNW w).cμ := (bgpParamsNW_cμ_pos w).le
  have h := selectorMUHoff_middle_offphase_of_envelopeP
    (p := bgpParamsNW w)
    (sol := bgpHeadlineSolFamNW w)
    hA hcμ (boxInputsNW w)
    (bgpHeadlineHoffMiddleEnvelopeResidualNW w)
  intro t ht
  simpa [bgpHeadlineHoffIntegrandNW] using h w j t ht

/-! ## Diagonal rate-free left/middle/right split -/

private theorem bgpHeadlineHoff_hsplitInt_of_caps_NW
    (capLeft capRight : ℕ → ℕ → ℝ)
    (hleft : ∀ w j,
      bgpHeadlineHoffCapLeftFieldNW w j ≤ capLeft w j)
    (hmiddle : ∀ w j, ∀ t ∈
      Icc (selectorMUZOffStart j) (selectorMUZOffEnd j),
      (∫ τ in (selectorMUZOffStart j)..t,
        bgpHeadlineHoffIntegrandNW w τ) ≤
          selectorMUHoffMiddleEnvelopeFullCapNW w j)
    (hright : ∀ w j,
      selectorMUHaltEncConst (solMUReplStaticCfg w) j →
      bgpHeadlineHoffCapRightFieldNW w j ≤ capRight w j) :
    ∀ w j,
      selectorMUHaltEncConst (solMUReplStaticCfg w) j →
      ∀ t ∈ Icc (selectorMUInterReadStart j)
          (selectorMUNextWriteStart j),
        (∫ τ in (selectorMUInterReadStart j)..t,
          bgpHeadlineHoffIntegrandNW w τ) ≤
            capLeft w j + selectorMUHoffMiddleEnvelopeFullCapNW w j +
              capRight w j := by
  intro w j henc t ht
  let f : ℝ → ℝ := bgpHeadlineHoffIntegrandNW w
  have hf_cont : Continuous f := by
    simpa [f, bgpHeadlineHoffIntegrandNW] using
      selectorMUHoffIntegrandP_continuous
        (p := bgpParamsNW w) (sol := bgpHeadlineSolFamNW w) w
  have hf_nonneg : ∀ τ, 0 ≤ f τ := by
    intro τ
    simpa [f, bgpHeadlineHoffIntegrandNW] using
      selectorMUHoffIntegrandP_nonneg
        (p := bgpParamsNW w) (bgpHeadlineSolFamNW w) w τ
  have hI : ∀ x y : ℝ, IntervalIntegrable f MeasureTheory.volume x y :=
    fun x y => hf_cont.intervalIntegrable x y
  have hmid₀ : 0 ≤ selectorMUHoffMiddleEnvelopeFullCapNW w j :=
    selectorMUHoffMiddleEnvelopeFullCapNW_nonneg w j
  have hright₀ : 0 ≤ capRight w j :=
    le_trans (bgpHeadlineHoffCapRightFieldNW_nonneg w j)
      (hright w j henc)
  change (∫ τ in (selectorMUInterReadStart j)..t, f τ) ≤
    capLeft w j + selectorMUHoffMiddleEnvelopeFullCapNW w j + capRight w j
  by_cases ht_left : t ≤ selectorMUZOffStart j
  · have hprefix :
        (∫ τ in (selectorMUInterReadStart j)..t, f τ) ≤
          bgpHeadlineHoffCapLeftFieldNW w j := by
      have hp := intervalIntegral_prefix_le_full_of_nonneg
        ht.1 ht_left hf_cont hf_nonneg
      simpa [bgpHeadlineHoffCapLeftFieldNW, f] using hp
    have hcap := le_trans hprefix (hleft w j)
    linarith
  · have hZ0t : selectorMUZOffStart j ≤ t := le_of_not_ge ht_left
    by_cases ht_mid : t ≤ selectorMUZOffEnd j
    · have hleft_full :
          (∫ τ in (selectorMUInterReadStart j)..(selectorMUZOffStart j), f τ) ≤
            capLeft w j := by
        simpa [bgpHeadlineHoffCapLeftFieldNW, f] using hleft w j
      have hmid_t :
          (∫ τ in (selectorMUZOffStart j)..t, f τ) ≤
            selectorMUHoffMiddleEnvelopeFullCapNW w j := by
        simpa [f] using hmiddle w j t ⟨hZ0t, ht_mid⟩
      have hadd := intervalIntegral.integral_add_adjacent_intervals
        (hI (selectorMUInterReadStart j) (selectorMUZOffStart j))
        (hI (selectorMUZOffStart j) t)
      calc
        (∫ τ in (selectorMUInterReadStart j)..t, f τ)
            = (∫ τ in (selectorMUInterReadStart j)..(selectorMUZOffStart j), f τ) +
              (∫ τ in (selectorMUZOffStart j)..t, f τ) := hadd.symm
        _ ≤ capLeft w j + selectorMUHoffMiddleEnvelopeFullCapNW w j :=
          add_le_add hleft_full hmid_t
        _ ≤ capLeft w j + selectorMUHoffMiddleEnvelopeFullCapNW w j +
              capRight w j := by linarith
    · have hZ1t : selectorMUZOffEnd j ≤ t := le_of_not_ge ht_mid
      have hleft_full :
          (∫ τ in (selectorMUInterReadStart j)..(selectorMUZOffStart j), f τ) ≤
            capLeft w j := by
        simpa [bgpHeadlineHoffCapLeftFieldNW, f] using hleft w j
      have hmid_full :
          (∫ τ in (selectorMUZOffStart j)..(selectorMUZOffEnd j), f τ) ≤
            selectorMUHoffMiddleEnvelopeFullCapNW w j := by
        simpa [f] using hmiddle w j (selectorMUZOffEnd j)
          ⟨selectorMUZOffStart_le_zOffEnd j, le_rfl⟩
      have hright_partial :
          (∫ τ in (selectorMUZOffEnd j)..t, f τ) ≤ capRight w j := by
        have hp :
            (∫ τ in (selectorMUZOffEnd j)..t, f τ) ≤
              bgpHeadlineHoffCapRightFieldNW w j := by
          have hp' := intervalIntegral_prefix_le_full_of_nonneg
            hZ1t ht.2 hf_cont hf_nonneg
          simpa [bgpHeadlineHoffCapRightFieldNW, f] using hp'
        exact le_trans hp (hright w j henc)
      have hadd₁ := intervalIntegral.integral_add_adjacent_intervals
        (hI (selectorMUInterReadStart j) (selectorMUZOffStart j))
        (hI (selectorMUZOffStart j) (selectorMUZOffEnd j))
      have hadd₂ := intervalIntegral.integral_add_adjacent_intervals
        (hI (selectorMUInterReadStart j) (selectorMUZOffEnd j))
        (hI (selectorMUZOffEnd j) t)
      have hdecomp :
          (∫ τ in (selectorMUInterReadStart j)..(selectorMUZOffEnd j), f τ) =
            (∫ τ in (selectorMUInterReadStart j)..(selectorMUZOffStart j), f τ) +
            (∫ τ in (selectorMUZOffStart j)..(selectorMUZOffEnd j), f τ) :=
        hadd₁.symm
      calc
        (∫ τ in (selectorMUInterReadStart j)..t, f τ)
            = (∫ τ in (selectorMUInterReadStart j)..(selectorMUZOffEnd j), f τ) +
              (∫ τ in (selectorMUZOffEnd j)..t, f τ) := hadd₂.symm
        _ = ((∫ τ in (selectorMUInterReadStart j)..(selectorMUZOffStart j), f τ) +
              (∫ τ in (selectorMUZOffStart j)..(selectorMUZOffEnd j), f τ)) +
              (∫ τ in (selectorMUZOffEnd j)..t, f τ) := by rw [hdecomp]
        _ ≤ (capLeft w j + selectorMUHoffMiddleEnvelopeFullCapNW w j) +
              capRight w j :=
          add_le_add (add_le_add hleft_full hmid_full) hright_partial
        _ = capLeft w j + selectorMUHoffMiddleEnvelopeFullCapNW w j +
              capRight w j := by ring

/-! ## Incremental constructors -/

/-- Core constructor exposing all five logical inputs.  This is useful while
pieces are landed independently. -/
def bgpHeadlineHoffFieldIntegralResidualNW_of_caps_core
    (capLeft capRight : ℕ → ℕ → ℝ)
    (hleft : ∀ w j,
      bgpHeadlineHoffCapLeftFieldNW w j ≤ capLeft w j)
    (hmiddle : ∀ w j, ∀ t ∈
      Icc (selectorMUZOffStart j) (selectorMUZOffEnd j),
      (∫ τ in (selectorMUZOffStart j)..t,
        bgpHeadlineHoffIntegrandNW w τ) ≤
          selectorMUHoffMiddleEnvelopeFullCapNW w j)
    (hright : ∀ w j,
      selectorMUHaltEncConst (solMUReplStaticCfg w) j →
      bgpHeadlineHoffCapRightFieldNW w j ≤ capRight w j)
    (hmiddle_old : ∀ w j,
      selectorMUHoffMiddleEnvelopeFullCapNW w j ≤
        selectorMUHoffMiddleEnvelopeFullCap j)
    (hedge : ∀ w j,
      selectorMUHaltEncConst (solMUReplStaticCfg w) j →
      capLeft w j + capRight w j ≤ selectorMUHoffEdgeBudget3992 j) :
    Paper3HeadlineHoffFieldIntegralResidualNW where
  hfieldInt := by
    intro w j henc t ht
    have hsplit := bgpHeadlineHoff_hsplitInt_of_caps_NW
      capLeft capRight hleft hmiddle hright w j henc t ht
    have hsum :
        capLeft w j + selectorMUHoffMiddleEnvelopeFullCapNW w j + capRight w j ≤
          selectorMUHoffMiddleEnvelopeFullCap j +
            selectorMUHoffEdgeBudget3992 j := by
      calc
        capLeft w j + selectorMUHoffMiddleEnvelopeFullCapNW w j + capRight w j
            = selectorMUHoffMiddleEnvelopeFullCapNW w j +
                (capLeft w j + capRight w j) := by ring
        _ ≤ selectorMUHoffMiddleEnvelopeFullCap j +
              selectorMUHoffEdgeBudget3992 j :=
          add_le_add (hmiddle_old w j) (hedge w j henc)
    have hhold :
        selectorMUHoffMiddleEnvelopeFullCap j +
            selectorMUHoffEdgeBudget3992 j ≤
          selectorReplicatorHoldEnvelope j := by
      simpa [selectorMUHoffEdgeBudget3992] using
        selectorMUHoffMiddleEnvelopeFullCap_add_edgeBudget_le_holdEnvelope j
    exact le_trans hsplit (le_trans hsum hhold)

/-- Main incremental constructor.  The middle field and middle-old comparison
are discharged internally; only the two S4 edge caps and their fixed edge-budget
allocation remain hypotheses. -/
def bgpHeadlineHoffFieldIntegralResidualNW_of_caps
    (boxInputsNW : ∀ w, Paper3HeadlineHoffBoxInputsNW w)
    (capLeft capRight : ℕ → ℕ → ℝ)
    (hleft : ∀ w j,
      bgpHeadlineHoffCapLeftFieldNW w j ≤ capLeft w j)
    (hright : ∀ w j,
      selectorMUHaltEncConst (solMUReplStaticCfg w) j →
      bgpHeadlineHoffCapRightFieldNW w j ≤ capRight w j)
    (hedge : ∀ w j,
      selectorMUHaltEncConst (solMUReplStaticCfg w) j →
      capLeft w j + capRight w j ≤ selectorMUHoffEdgeBudget3992 j) :
    Paper3HeadlineHoffFieldIntegralResidualNW :=
  bgpHeadlineHoffFieldIntegralResidualNW_of_caps_core
    capLeft capRight hleft
    (bgpHeadlineHoff_middle_fieldIntegral_NW boxInputsNW)
    hright
    selectorMUHoffMiddleEnvelopeFullCapNW_le_old_middle_budget
    hedge

/-! ## Final pointwise Hoff drift -/

/-- Convert the diagonal field-integral record into the exact pointwise
`p_hoff` output. -/
theorem bgpHeadlineHoffNW
    (R : Paper3HeadlineHoffFieldIntegralResidualNW) :
    ∀ w j,
      selectorMUHaltEncConst (solMUReplStaticCfg w) j →
      ∀ t ∈ Icc (selectorMUInterReadStart j)
          (selectorMUNextWriteStart j),
        |((bgpHeadlineSolFamNW w) w).z t haltCoordU -
          ((bgpHeadlineSolFamNW w) w).z
            (selectorMUInterReadStart j) haltCoordU| ≤
          selectorReplicatorHoldEnvelope j := by
  intro w j henc t ht
  have ha₀ : 0 ≤ selectorMUInterReadStart j := by
    unfold selectorMUInterReadStart selectorMUWriteReadTime
    positivity
  have hdom : ∀ s ∈ Icc (selectorMUInterReadStart j)
      (selectorMUNextWriteStart j), s ∈ selectorSchedule.domain := by
    intro s hs
    exact selectorSchedule_domain_of_nonneg_structural s
      (le_trans ha₀ hs.1)
  exact flag_drift_bound_on_interval_repl
    ((bgpHeadlineSolFamNW w) w) haltCoordU
    (selectorMUInterReadStart_le_nextWriteStart j)
    hdom
    (selector_replicator_gateZ_integrand_continuous
      ((bgpHeadlineSolFamNW w) w))
    (by
      intro s hs
      simpa [bgpHeadlineHoffIntegrandNW, selectorMUHoffIntegrandP] using
        R.hfieldInt w j henc s hs)
    t ht

end Ripple.BoundedUniversality.BGP
