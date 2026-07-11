import Ripple.BoundedUniversality.BGP.SelectorReplicatorActiveQSSP
import Ripple.BoundedUniversality.BGP.RelaxationToolkit

/-!
# Generic toolkit for the S4 edge leaves

This file contains only parameter-generic analytic lemmas used by the S4
leaf dossier.  It deliberately avoids headline/private `paper3*` suppliers.
-/

noncomputable section

namespace Ripple.BoundedUniversality.BGP

open MachineInstance UniversalMachine Set
open scoped BigOperators Topology

/-- Parameter-generic window form of active-QSS derivative RHS continuity:
if the active sink stays strictly positive on `[a,b]`, the quotient defining
`selectorMU_activeQSSDerivRHSP` is continuous on that interval. -/
theorem selectorMU_activeQSSDerivRHS_continuousOn_of_sink_posP
    {p : DynGateParams} {eta : ℚ} {heta : 0 < eta}
    {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamilyP p eta heta Mcy κ₀ g₀}
    (w : ℕ) (c v : UniversalLocalView) {a b : ℝ}
    (hsink_pos : ∀ τ ∈ Icc a b,
      0 < selectorMU_activeSinkP eta heta sol w c v τ) :
    ContinuousOn
      (fun τ : ℝ => selectorMU_activeQSSDerivRHSP eta heta sol w c v τ)
      (Icc a b) := by
  let card : ℝ := (Fintype.card UniversalLocalView : ℝ)
  have hcr := selectorMU_activeCr_continuous Mcy κ₀
  have hcrD := selectorMU_activeCrDeriv_continuous Mcy κ₀
  have hk := selectorMU_activeSink_continuousP eta heta sol w c v
  have hkD := selectorMU_activeSinkDerivRHS_continuousP eta heta sol w c v
  have hden_ne : ∀ τ ∈ Icc a b,
      selectorMU_activeSinkP eta heta sol w c v τ ^ 2 ≠ 0 := by
    intro τ hτ
    exact pow_ne_zero 2 (ne_of_gt (hsink_pos τ hτ))
  have hnum : Continuous fun τ : ℝ =>
      (selectorMU_activeCrDeriv Mcy κ₀ τ * card⁻¹) *
        selectorMU_activeSinkP eta heta sol w c v τ -
      (selectorMU_activeCr Mcy κ₀ τ * card⁻¹) *
        selectorMU_activeSinkDerivRHSP eta heta sol w c v τ :=
    ((hcrD.mul continuous_const).mul hk).sub
      ((hcr.mul continuous_const).mul hkD)
  have hden : Continuous fun τ : ℝ =>
      selectorMU_activeSinkP eta heta sol w c v τ ^ 2 := hk.pow 2
  simpa [selectorMU_activeQSSDerivRHSP, card] using
    hnum.continuousOn.div hden.continuousOn hden_ne

/-- The absolute active-QSS derivative RHS is interval-integrable on any
window where the P-generic active sink is strictly positive. -/
theorem selectorMU_activeQSSDerivRHS_abs_intervalIntegrable_of_sink_posP
    {p : DynGateParams} {eta : ℚ} {heta : 0 < eta}
    {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamilyP p eta heta Mcy κ₀ g₀}
    (w : ℕ) (c v : UniversalLocalView) {a b : ℝ} (hab : a ≤ b)
    (hsink_pos : ∀ τ ∈ Icc a b,
      0 < selectorMU_activeSinkP eta heta sol w c v τ) :
    IntervalIntegrable
      (fun τ : ℝ =>
        |selectorMU_activeQSSDerivRHSP eta heta sol w c v τ|)
      MeasureTheory.volume a b := by
  have hcont :=
    selectorMU_activeQSSDerivRHS_continuousOn_of_sink_posP
      (sol := sol) w c v hsink_pos
  exact hcont.abs.intervalIntegrable_of_Icc hab

/-- Pointwise exponential decay of `|f|` on `[a,b]` gives the standard
left-anchored integral cap. -/
theorem integral_abs_le_const_mul_exp_neg_of_continuousOn
    {f : ℝ → ℝ} {r C a b : ℝ}
    (hr : 0 < r) (hC : 0 ≤ C) (hab : a ≤ b)
    (hf_cont : ContinuousOn f (Icc a b))
    (hbound : ∀ τ ∈ Icc a b,
      |f τ| ≤ C * Real.exp (-(r * τ))) :
    (∫ τ in a..b, |f τ|) ≤
      (C / r) * Real.exp (-(r * a)) := by
  have hleft :
      IntervalIntegrable (fun τ : ℝ => |f τ|) MeasureTheory.volume a b :=
    hf_cont.abs.intervalIntegrable_of_Icc hab
  have hright_cont : Continuous fun τ : ℝ =>
      C * Real.exp (-(r * τ)) :=
    continuous_const.mul
      (Real.continuous_exp.comp
        ((continuous_const.mul continuous_id).neg))
  have hmono :
      (∫ τ in a..b, |f τ|) ≤
        ∫ τ in a..b, C * Real.exp (-(r * τ)) :=
    intervalIntegral.integral_mono_on hab hleft
      (hright_cont.intervalIntegrable a b) hbound
  exact le_trans hmono
    (integral_const_mul_exp_neg_le_left hr hC hab)

/-- Same as `integral_abs_le_const_mul_exp_neg_of_continuousOn`, with the
final scalar comparison supplied externally. -/
theorem integral_abs_le_of_exp_decay_budget
    {f : ℝ → ℝ} {r C a b B : ℝ}
    (hr : 0 < r) (hC : 0 ≤ C) (hab : a ≤ b)
    (hf_cont : ContinuousOn f (Icc a b))
    (hbound : ∀ τ ∈ Icc a b,
      |f τ| ≤ C * Real.exp (-(r * τ)))
    (hbudget : (C / r) * Real.exp (-(r * a)) ≤ B) :
    (∫ τ in a..b, |f τ|) ≤ B :=
  le_trans
    (integral_abs_le_const_mul_exp_neg_of_continuousOn
      hr hC hab hf_cont hbound)
    hbudget

/-- Sum of per-index exponentially decaying absolute integrals. -/
theorem finset_sum_integral_abs_le_exp_decay
    {ι : Type*} (s : Finset ι) {F : ι → ℝ → ℝ}
    {C : ι → ℝ} {r a b : ℝ}
    (hr : 0 < r) (hab : a ≤ b)
    (hC : ∀ i ∈ s, 0 ≤ C i)
    (hF_cont : ∀ i ∈ s, ContinuousOn (F i) (Icc a b))
    (hbound : ∀ i ∈ s, ∀ τ ∈ Icc a b,
      |F i τ| ≤ C i * Real.exp (-(r * τ))) :
    s.sum (fun i => ∫ τ in a..b, |F i τ|) ≤
      ((s.sum C) / r) * Real.exp (-(r * a)) := by
  calc
    s.sum (fun i => ∫ τ in a..b, |F i τ|)
        ≤ s.sum (fun i => (C i / r) * Real.exp (-(r * a))) := by
          refine Finset.sum_le_sum ?_
          intro i hi
          exact integral_abs_le_const_mul_exp_neg_of_continuousOn
            hr (hC i hi) hab (hF_cont i hi) (hbound i hi)
    _ = ((s.sum C) / r) * Real.exp (-(r * a)) := by
          rw [← Finset.sum_mul, ← Finset.sum_div]

/-- Budgeted form of `finset_sum_integral_abs_le_exp_decay`. -/
theorem finset_sum_integral_abs_le_exp_decay_budget
    {ι : Type*} (s : Finset ι) {F : ι → ℝ → ℝ}
    {C : ι → ℝ} {r a b B : ℝ}
    (hr : 0 < r) (hab : a ≤ b)
    (hC : ∀ i ∈ s, 0 ≤ C i)
    (hF_cont : ∀ i ∈ s, ContinuousOn (F i) (Icc a b))
    (hbound : ∀ i ∈ s, ∀ τ ∈ Icc a b,
      |F i τ| ≤ C i * Real.exp (-(r * τ)))
    (hbudget : ((s.sum C) / r) * Real.exp (-(r * a)) ≤ B) :
    s.sum (fun i => ∫ τ in a..b, |F i τ|) ≤ B :=
  le_trans
    (finset_sum_integral_abs_le_exp_decay s hr hab hC hF_cont hbound)
    hbudget

/-- Uniform-coefficient wrapper for finite sums of exponentially decaying
absolute integrals. -/
theorem finset_sum_integral_abs_le_uniform_exp_decay
    {ι : Type*} (s : Finset ι) {F : ι → ℝ → ℝ}
    {C r a b : ℝ}
    (hr : 0 < r) (hC : 0 ≤ C) (hab : a ≤ b)
    (hF_cont : ∀ i ∈ s, ContinuousOn (F i) (Icc a b))
    (hbound : ∀ i ∈ s, ∀ τ ∈ Icc a b,
      |F i τ| ≤ C * Real.exp (-(r * τ))) :
    s.sum (fun i => ∫ τ in a..b, |F i τ|) ≤
      ((s.card : ℝ) * C / r) * Real.exp (-(r * a)) := by
  have h :=
    finset_sum_integral_abs_le_exp_decay
      (s := s) (F := F) (C := fun _ => C)
      hr hab (fun i hi => hC) hF_cont hbound
  simpa using h

/-- Two-times budget wrapper for the S4 forcing leaves. -/
theorem two_mul_finset_sum_integral_abs_le_exp_decay_budget
    {ι : Type*} (s : Finset ι) {F : ι → ℝ → ℝ}
    {C : ι → ℝ} {r a b B : ℝ}
    (hr : 0 < r) (hab : a ≤ b)
    (hC : ∀ i ∈ s, 0 ≤ C i)
    (hF_cont : ∀ i ∈ s, ContinuousOn (F i) (Icc a b))
    (hbound : ∀ i ∈ s, ∀ τ ∈ Icc a b,
      |F i τ| ≤ C i * Real.exp (-(r * τ)))
    (hbudget :
      2 * (((s.sum C) / r) * Real.exp (-(r * a))) ≤ B) :
    2 * s.sum (fun i => ∫ τ in a..b, |F i τ|) ≤ B := by
  have hsum :=
    finset_sum_integral_abs_le_exp_decay s hr hab hC hF_cont hbound
  exact le_trans (mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : ℝ) ≤ 2))
    hbudget

/-- Filtered finite sums are bounded by full sums when the summand is
nonnegative. -/
theorem finset_sum_filter_le_univ_sum_of_nonneg
    {ι : Type*} [Fintype ι] (p : ι → Prop) [DecidablePred p]
    {f : ι → ℝ} (hf_nonneg : ∀ i : ι, 0 ≤ f i) :
    (Finset.univ.filter p).sum f ≤ Finset.univ.sum f := by
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.filter_subset p Finset.univ)
    (by
      intro i _hi hnot
      exact hf_nonneg i)

/-- Integral/sum commute for a finite family of continuous functions.  This
is a small wrapper around `intervalIntegral.integral_finsetSum` in the shape
used by S4 forcing reductions. -/
theorem integral_finset_sum_of_continuous
    {ι : Type*} (s : Finset ι) {F : ι → ℝ → ℝ}
    {a b : ℝ}
    (hF_cont : ∀ i ∈ s, Continuous (F i)) :
    (∫ τ in a..b, s.sum (fun i => F i τ)) =
      s.sum (fun i => ∫ τ in a..b, F i τ) := by
  rw [intervalIntegral.integral_finsetSum]
  intro i hi
  exact (hF_cont i hi).intervalIntegrable a b

/-- A time-local Duhamel source bound from an exponential supersolution.

Unlike `forward_reset_integral_mul_decay_le`, the comparison coefficient is
not frozen at the left endpoint.  If `C * exp (-c t)` is a supersolution of
`y' = -gap * cg * y + reset`, then the reset convolution at the physical
time `t` retains the same running exponential decay. -/
theorem forward_reset_integral_mul_decay_le_exp_supersolution
    {a t gap c C : ℝ} {G cg reset : ℝ → ℝ}
    (hat : a ≤ t) (hgap : 0 < gap) (hc : 0 < c) (hC : 0 ≤ C)
    (hGcont : Continuous G)
    (hGder : ∀ s ∈ Icc a t, HasDerivAt G (cg s) s)
    (hcg_cont : Continuous cg) (hreset_cont : Continuous reset)
    (hmajor : ∀ s ∈ Icc a t,
      reset s ≤ (gap * cg s - c) * (C * Real.exp (-(c * s)))) :
    (∫ s in a..t,
        Real.exp (gap * (G s - G a)) * reset s) *
        Real.exp (-(gap * (G t - G a))) ≤
      C * Real.exp (-(c * t)) := by
  let E : ℝ → ℝ := fun s => Real.exp (gap * (G s - G a))
  let H : ℝ → ℝ := fun s => E s * (C * Real.exp (-(c * s)))
  have hEcont : Continuous E := by
    dsimp [E]
    exact Real.continuous_exp.comp
      (continuous_const.mul (hGcont.sub continuous_const))
  have hdec_cont : Continuous fun s : ℝ => C * Real.exp (-(c * s)) := by
    fun_prop
  have hHcont : Continuous H := hEcont.mul hdec_cont
  have hHder : ∀ s ∈ Set.uIcc a t,
      HasDerivAt H
        (E s * ((gap * cg s - c) * (C * Real.exp (-(c * s))))) s := by
    intro s hs
    have hsIcc : s ∈ Icc a t := by
      rwa [Set.uIcc_of_le hat] at hs
    have hE := (((hGder s hsIcc).sub_const (G a)).const_mul gap).exp
    have hdec_arg : HasDerivAt (fun x : ℝ => -(c * x)) (-c) s := by
      simpa using ((hasDerivAt_id s).const_mul c).neg
    have hdec := (hdec_arg.exp).const_mul C
    have hprod := hE.mul hdec
    convert hprod using 1 <;> simp only [E, H]
    ring
  have hreset_weight_cont : Continuous fun s : ℝ => E s * reset s :=
    hEcont.mul hreset_cont
  have hmajor_weight_cont : Continuous fun s : ℝ =>
      E s * ((gap * cg s - c) * (C * Real.exp (-(c * s)))) := by
    fun_prop
  have hpoint : ∀ s ∈ Icc a t,
      E s * reset s ≤
        E s * ((gap * cg s - c) * (C * Real.exp (-(c * s)))) := by
    intro s hs
    exact mul_le_mul_of_nonneg_left (hmajor s hs) (Real.exp_pos _).le
  have hmono :
      (∫ s in a..t, E s * reset s) ≤
        ∫ s in a..t,
          E s * ((gap * cg s - c) * (C * Real.exp (-(c * s)))) :=
    intervalIntegral.integral_mono_on hat
      (hreset_weight_cont.intervalIntegrable a t)
      (hmajor_weight_cont.intervalIntegrable a t) hpoint
  have hFTC :
      (∫ s in a..t,
          E s * ((gap * cg s - c) * (C * Real.exp (-(c * s))))) =
        H t - H a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hHder
      (hmajor_weight_cont.intervalIntegrable a t)
  have hHa_nonneg : 0 ≤ H a := by
    dsimp [H, E]
    positivity
  have hint_le : (∫ s in a..t, E s * reset s) ≤ H t := by
    rw [hFTC] at hmono
    linarith
  have hterminal_nonneg :
      0 ≤ Real.exp (-(gap * (G t - G a))) := (Real.exp_pos _).le
  have hmul := mul_le_mul_of_nonneg_right hint_le hterminal_nonneg
  have hcancel :
      E t * Real.exp (-(gap * (G t - G a))) = 1 := by
    dsimp [E]
    rw [← Real.exp_add]
    simp
  calc
    (∫ s in a..t, Real.exp (gap * (G s - G a)) * reset s) *
          Real.exp (-(gap * (G t - G a)))
        ≤ H t * Real.exp (-(gap * (G t - G a))) := hmul
    _ = (E t * Real.exp (-(gap * (G t - G a)))) *
          (C * Real.exp (-(c * t))) := by
        dsimp [H]
        ring
    _ = C * Real.exp (-(c * t)) := by rw [hcancel, one_mul]

/-- Homogeneous counterpart of the running exponential supersolution.  A
pointwise lower bound `c ≤ gap * cg` turns the integrating factor from `a`
to `t` into physical-time decay without freezing the right endpoint. -/
theorem exp_neg_G_sub_le_exp_mul_exp_neg_of_rate_le
    {a t gap c : ℝ} {G cg : ℝ → ℝ}
    (hat : a ≤ t)
    (hGder : ∀ s ∈ Icc a t, HasDerivAt G (cg s) s)
    (hcg_cont : Continuous cg)
    (hrate : ∀ s ∈ Icc a t, c ≤ gap * cg s) :
    Real.exp (-(gap * (G t - G a))) ≤
      Real.exp (c * a) * Real.exp (-(c * t)) := by
  have hmono :
      (∫ s in a..t, c) ≤ ∫ s in a..t, gap * cg s := by
    apply intervalIntegral.integral_mono_on hat
    · exact continuous_const.intervalIntegrable a t
    · exact (continuous_const.mul hcg_cont).intervalIntegrable a t
    · exact hrate
  have hFTC : (∫ s in a..t, cg s) = G t - G a := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s hs => hGder s (by rwa [Set.uIcc_of_le hat] at hs))
      (hcg_cont.intervalIntegrable a t)
  have hclock : c * (t - a) ≤ gap * (G t - G a) := by
    rw [intervalIntegral.integral_const,
      intervalIntegral.integral_const_mul, hFTC] at hmono
    simpa [smul_eq_mul, mul_comm] using hmono
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  linarith

end Ripple.BoundedUniversality.BGP
