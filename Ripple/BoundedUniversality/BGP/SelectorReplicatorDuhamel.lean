import Ripple.BoundedUniversality.BGP.SelectorReplicatorConcSchedule
import Ripple.BoundedUniversality.BGP.BGPParams38

/-!
Ripple.BoundedUniversality.BGP.SelectorReplicatorDuhamel
-------------------------------------
Duhamel reset residual for the concrete replicator schedule.

This file proves the schedule-only part of the concrete reset residual decay.
The margin `gap` remains an input: it belongs to the separate tube/winner stage.
-/

noncomputable section

namespace Ripple.BoundedUniversality.BGP

open Filter
open Set MachineInstance
open scoped BigOperators Topology

/-- The actual forward reset coefficient over the concrete `M_U` write window. -/
def solMUReplForwardResetIntegral
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    {cfg : ℕ → ℕ → UConf}
    (inputs : SelectorReplicatorConcInputs sol cfg) (w j : ℕ) : ℝ :=
  ∫ t in (selectorMUWriteStartTime j)..(selectorMUWriteReadTime j),
    Real.exp (inputs.gap w j *
      ((sol w).G t - (sol w).G (selectorMUWriteStartTime j))) *
      (((1 + Real.cos t) / 2) ^ Mcy * (κ₀ : ℝ))

/-- The actual forward reset coefficient over the concrete prefix select window
`[2πj+π/6, 2πj+π/2]`. -/
def solMUReplPreForwardResetIntegral
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    {cfg : ℕ → ℕ → UConf}
    (inputs : SelectorReplicatorConcInputs sol cfg) (w j : ℕ) : ℝ :=
  ∫ t in (selectorMUWriteStartTime j)..(selectorMUWriteHoldTime j),
    Real.exp (inputs.gap w j *
      ((sol w).G t - (sol w).G (selectorMUWriteStartTime j))) *
      (((1 + Real.cos t) / 2) ^ Mcy * (κ₀ : ℝ))

/-- Scalar Duhamel comparison for a nonnegative bad-mass variable.

This is the integrating-factor comparison behind the two-safe prewrite
bad-mass estimate: if `B' ≤ -gap * cg * B + cr * Creset` and `G' = cg`,
then the usual Duhamel upper bound holds. -/
theorem badMass_scalar_duhamel_bound
    (B cr cg G : ℝ → ℝ) {a b gap Creset : ℝ}
    (_hab : a ≤ b)
    (_hgap_pos : 0 < gap)
    (hB_cont : ContinuousOn B (Icc a b))
    (hGcont : Continuous G)
    (hcr_cont : Continuous cr)
    (hGder : ∀ t ∈ Ico a b, HasDerivWithinAt G (cg t) (Ici t) t)
    (hBder_le : ∀ t ∈ Ico a b,
      ∃ dB : ℝ,
        HasDerivWithinAt B dB (Ici t) t ∧
          dB ≤ -gap * cg t * B t + cr t * Creset) :
    ∀ t ∈ Icc a b,
      B t ≤ B a * Real.exp (-(gap * (G t - G a))) +
        (∫ s in a..t,
          Real.exp (gap * (G s - G a)) * cr s * Creset) *
          Real.exp (-(gap * (G t - G a))) := by
  classical
  let E : ℝ → ℝ := fun t => Real.exp (gap * (G t - G a))
  let Q : ℝ → ℝ := fun t => B t * E t
  let H : ℝ → ℝ := fun t =>
    B a + ∫ s in a..t, E s * cr s * Creset
  let dB : ℝ → ℝ := fun t =>
    if ht : t ∈ Ico a b then Classical.choose (hBder_le t ht) else 0
  have hEcont : Continuous E := by
    dsimp [E]
    exact Real.continuous_exp.comp
      (continuous_const.mul (hGcont.sub continuous_const))
  have hf_cont : Continuous fun s => E s * cr s * Creset := by
    exact (hEcont.mul hcr_cont).mul continuous_const
  have hQcont : ContinuousOn Q (Icc a b) := by
    dsimp [Q]
    exact hB_cont.mul hEcont.continuousOn
  have hHcont : ContinuousOn H (Icc a b) := by
    have hprim : Continuous (fun u => ∫ s in a..u, E s * cr s * Creset) :=
      continuous_iff_continuousAt.mpr fun t =>
        (intervalIntegral.integral_hasDerivAt_right
          (hf_cont.intervalIntegrable a t)
          (hf_cont.stronglyMeasurableAtFilter _ _) hf_cont.continuousAt).continuousAt
    dsimp [H]
    exact (continuous_const.add hprim).continuousOn
  have hEder : ∀ t ∈ Ico a b,
      HasDerivWithinAt E (E t * (gap * cg t)) (Ici t) t := by
    intro t ht
    have h := (((hGder t ht).sub_const (G a)).const_mul gap).exp
    simpa [E, mul_comm, mul_left_comm, mul_assoc] using h
  have hBder : ∀ t ∈ Ico a b,
      HasDerivWithinAt B (dB t) (Ici t) t := by
    intro t ht
    have hspec := Classical.choose_spec (hBder_le t ht)
    change HasDerivWithinAt B
      (if ht' : t ∈ Ico a b then Classical.choose (hBder_le t ht') else 0)
      (Ici t) t
    rw [dif_pos ht]
    exact hspec.1
  have hBder_bound : ∀ t ∈ Ico a b,
      dB t ≤ -gap * cg t * B t + cr t * Creset := by
    intro t ht
    have hspec := Classical.choose_spec (hBder_le t ht)
    change
      (if ht' : t ∈ Ico a b then Classical.choose (hBder_le t ht') else 0)
        ≤ -gap * cg t * B t + cr t * Creset
    rw [dif_pos ht]
    exact hspec.2
  have hQder : ∀ t ∈ Ico a b,
      HasDerivWithinAt Q
        (dB t * E t + B t * (E t * (gap * cg t))) (Ici t) t := by
    intro t ht
    simpa [Q] using (hBder t ht).mul (hEder t ht)
  have hHder : ∀ t ∈ Ico a b,
      HasDerivWithinAt H (E t * cr t * Creset) (Ici t) t := by
    intro t ht
    have hftc : HasDerivAt (fun u => ∫ s in a..u, E s * cr s * Creset)
        (E t * cr t * Creset) t :=
      intervalIntegral.integral_hasDerivAt_right
        (hf_cont.intervalIntegrable a t)
        (hf_cont.stronglyMeasurableAtFilter _ _) hf_cont.continuousAt
    exact (hftc.const_add (B a)).hasDerivWithinAt
  have hder_le : ∀ t ∈ Ico a b,
      dB t * E t + B t * (E t * (gap * cg t)) ≤
        E t * cr t * Creset := by
    intro t ht
    have hE_nonneg : 0 ≤ E t := (Real.exp_pos _).le
    have hmul := mul_le_mul_of_nonneg_right (hBder_bound t ht) hE_nonneg
    calc
      dB t * E t + B t * (E t * (gap * cg t))
          = B t * (E t * (gap * cg t)) + dB t * E t := by ring
      _ ≤ B t * (E t * (gap * cg t)) +
            (-gap * cg t * B t + cr t * Creset) * E t := by
            exact add_le_add_right hmul _
      _ = (-gap * cg t * B t + cr t * Creset) * E t +
              B t * (E t * (gap * cg t)) := by ring
      _ = E t * cr t * Creset := by ring
  have hQa : Q a ≤ H a := by
    dsimp [Q, H, E]
    simp
  have hQ_le_H : ∀ x, x ∈ Icc a b → Q x ≤ H x :=
    image_le_of_deriv_right_le_deriv_boundary
      hQcont hQder hQa hHcont hHder hder_le
  intro t ht
  have hQt := hQ_le_H t ht
  have hEpos : 0 < E t := Real.exp_pos _
  have hdiv : B t ≤ H t / E t := by
    exact (le_div_iff₀ hEpos).mpr (by simpa [Q] using hQt)
  have hrewrite :
      H t / E t =
        B a * Real.exp (-(gap * (G t - G a))) +
          (∫ s in a..t,
            Real.exp (gap * (G s - G a)) * cr s * Creset) *
            Real.exp (-(gap * (G t - G a))) := by
    dsimp [H, E]
    rw [Real.exp_neg]
    ring
  exact hdiv.trans_eq hrewrite

/-- Antiderivative bound for a forward reset integral multiplied by the backward
decay.  If `reset ≤ C * cg` on `[a,b]` and `G' = cg`, then
`exp (-gap*(G b-G a)) * ∫ exp (gap*(G-G a))*reset ≤ C/gap`.

This is the Duhamel cancellation used below; the proof is an FTC computation
with primitive `exp (gap*(G t-G a))`. -/
theorem forward_reset_integral_mul_decay_le
    {a b gap C : ℝ} {G cg reset : ℝ → ℝ}
    (hab : a ≤ b) (hgap : 0 < gap) (hC : 0 ≤ C)
    (hGcont : Continuous G)
    (hGder : ∀ t ∈ Icc a b, HasDerivAt G (cg t) t)
    (hcg_cont : Continuous cg) (hreset_cont : Continuous reset)
    (hreset_nonneg : ∀ t ∈ Icc a b, 0 ≤ reset t)
    (hreset_bound : ∀ t ∈ Icc a b, reset t ≤ C * cg t) :
    0 ≤
        (∫ t in a..b, Real.exp (gap * (G t - G a)) * reset t) *
          Real.exp (-(gap * (G b - G a))) ∧
      (∫ t in a..b, Real.exp (gap * (G t - G a)) * reset t) *
          Real.exp (-(gap * (G b - G a))) ≤ C / gap := by
  set F : ℝ → ℝ := fun t => Real.exp (gap * (G t - G a)) with hFdef
  have hFcont : Continuous F := by
    simpa [hFdef] using
      Real.continuous_exp.comp (continuous_const.mul (hGcont.sub continuous_const))
  have hFder : ∀ t ∈ uIcc a b, HasDerivAt F (gap * cg t * F t) t := by
    intro t ht
    have htIcc : t ∈ Icc a b := by
      rwa [uIcc_of_le hab] at ht
    have h := (((hGder t htIcc).sub_const (G a)).const_mul gap).exp
    convert h using 1
    simp only [hFdef]; ring
  have hcont_der : Continuous fun t => gap * cg t * F t :=
    (continuous_const.mul hcg_cont).mul hFcont
  have hFTC :
      (∫ t in a..b, gap * cg t * F t) = F b - F a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hFder
      (hcont_der.intervalIntegrable a b)
  have hF_nonneg : ∀ t, 0 ≤ F t := fun t => (Real.exp_pos _).le
  have hreset_int :
      IntervalIntegrable (fun t => F t * reset t) MeasureTheory.volume a b :=
    (hFcont.mul hreset_cont).intervalIntegrable a b
  have hmajor_int :
      IntervalIntegrable (fun t => (C / gap) * (gap * cg t * F t))
        MeasureTheory.volume a b :=
    (continuous_const.mul hcont_der).intervalIntegrable a b
  have hpoint :
      ∀ t ∈ Icc a b, F t * reset t ≤ (C / gap) * (gap * cg t * F t) := by
    intro t ht
    calc
      F t * reset t ≤ F t * (C * cg t) :=
        mul_le_mul_of_nonneg_left (hreset_bound t ht) (hF_nonneg t)
      _ = (C / gap) * (gap * cg t * F t) := by
        field_simp [hgap.ne']
  have hbase :
      (∫ t in a..b, F t * reset t) ≤
        (C / gap) * (F b - F a) := by
    calc
      (∫ t in a..b, F t * reset t)
          ≤ ∫ t in a..b, (C / gap) * (gap * cg t * F t) :=
        intervalIntegral.integral_mono_on hab hreset_int hmajor_int hpoint
      _ = (C / gap) * ∫ t in a..b, gap * cg t * F t := by
        rw [intervalIntegral.integral_const_mul]
      _ = (C / gap) * (F b - F a) := by rw [hFTC]
  have hnonneg_int :
      0 ≤ ∫ t in a..b, F t * reset t :=
    intervalIntegral.integral_nonneg hab
      (fun t ht => mul_nonneg (hF_nonneg t) (hreset_nonneg t ht))
  have hdecay_nonneg : 0 ≤ Real.exp (-(gap * (G b - G a))) :=
    (Real.exp_pos _).le
  refine ⟨mul_nonneg hnonneg_int hdecay_nonneg, ?_⟩
  have hprod :
      (∫ t in a..b, F t * reset t) *
          Real.exp (-(gap * (G b - G a))) ≤
        ((C / gap) * (F b - F a)) *
          Real.exp (-(gap * (G b - G a))) :=
    mul_le_mul_of_nonneg_right hbase hdecay_nonneg
  have hrewrite :
      ((C / gap) * (F b - F a)) *
          Real.exp (-(gap * (G b - G a))) =
        (C / gap) * (1 - Real.exp (-(gap * (G b - G a)))) := by
    have hcancel :
        Real.exp (gap * (G b - G a)) *
            Real.exp (-(gap * (G b - G a))) = 1 := by
      rw [← Real.exp_add, show gap * (G b - G a) + -(gap * (G b - G a)) = 0 by ring,
        Real.exp_zero]
    simp [hFdef]
    linear_combination (C / gap) * hcancel
  calc
    (∫ t in a..b, F t * reset t) *
        Real.exp (-(gap * (G b - G a)))
        ≤ ((C / gap) * (F b - F a)) *
          Real.exp (-(gap * (G b - G a))) := hprod
    _ = (C / gap) * (1 - Real.exp (-(gap * (G b - G a)))) := hrewrite
    _ ≤ C / gap := by
      have hCgap : 0 ≤ C / gap := div_nonneg hC hgap.le
      have hexp : 0 ≤ Real.exp (-(gap * (G b - G a))) := (Real.exp_pos _).le
      nlinarith [mul_nonneg hCgap hexp]

/-- Backward-decay integral bound for an arbitrary nonnegative weight.

If `weight ≤ C * cg` and `G' = cg`, then
`∫ weight * exp(-gap * (G-G a)) ≤ C/gap`.  This is the homogeneous part of the
same Duhamel cancellation used in `forward_reset_integral_mul_decay_le`, but
with the backward kernel kept inside the integral. -/
theorem forward_weight_decay_integral_le
    {a b gap C : ℝ} {G cg weight : ℝ → ℝ}
    (hab : a ≤ b) (hgap : 0 < gap) (hC : 0 ≤ C)
    (hGcont : Continuous G)
    (hGder : ∀ t ∈ Icc a b, HasDerivAt G (cg t) t)
    (hcg_cont : Continuous cg) (hweight_cont : Continuous weight)
    (hweight_nonneg : ∀ t ∈ Icc a b, 0 ≤ weight t)
    (hweight_bound : ∀ t ∈ Icc a b, weight t ≤ C * cg t) :
    0 ≤
        (∫ t in a..b,
          weight t * Real.exp (-(gap * (G t - G a)))) ∧
      (∫ t in a..b,
          weight t * Real.exp (-(gap * (G t - G a)))) ≤ C / gap := by
  set F : ℝ → ℝ := fun t => Real.exp (-(gap * (G t - G a))) with hFdef
  have hFcont : Continuous F := by
    simpa [hFdef] using
      Real.continuous_exp.comp
        ((continuous_const.mul (hGcont.sub continuous_const)).neg)
  have hFder : ∀ t ∈ uIcc a b, HasDerivAt F (-(gap * cg t * F t)) t := by
    intro t ht
    have htIcc : t ∈ Icc a b := by
      rwa [uIcc_of_le hab] at ht
    have h := ((((hGder t htIcc).sub_const (G a)).const_mul gap).neg).exp
    convert h using 1
    · simp [hFdef]
      ring
  have hnegF_der : ∀ t ∈ uIcc a b,
      HasDerivAt (fun x => -F x) (gap * cg t * F t) t := by
    intro t ht
    have h := (hFder t ht).neg
    convert h using 1
    ring
  have hcont_der : Continuous fun t => gap * cg t * F t :=
    (continuous_const.mul hcg_cont).mul hFcont
  have hFTC :
      (∫ t in a..b, gap * cg t * F t) = F a - F b := by
    have hsub :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt hnegF_der
        (hcont_der.intervalIntegrable a b)
    calc
      (∫ t in a..b, gap * cg t * F t) = -F b - -F a := hsub
      _ = F a - F b := by ring
  have hF_nonneg : ∀ t, 0 ≤ F t := fun t => (Real.exp_pos _).le
  have hweight_int :
      IntervalIntegrable (fun t => weight t * F t) MeasureTheory.volume a b :=
    (hweight_cont.mul hFcont).intervalIntegrable a b
  have hmajor_int :
      IntervalIntegrable (fun t => (C / gap) * (gap * cg t * F t))
        MeasureTheory.volume a b :=
    (continuous_const.mul hcont_der).intervalIntegrable a b
  have hpoint :
      ∀ t ∈ Icc a b, weight t * F t ≤ (C / gap) * (gap * cg t * F t) := by
    intro t ht
    calc
      weight t * F t ≤ (C * cg t) * F t :=
        mul_le_mul_of_nonneg_right (hweight_bound t ht) (hF_nonneg t)
      _ = (C / gap) * (gap * cg t * F t) := by
        field_simp [hgap.ne']
  have hbase :
      (∫ t in a..b, weight t * F t) ≤
        (C / gap) * (F a - F b) := by
    calc
      (∫ t in a..b, weight t * F t)
          ≤ ∫ t in a..b, (C / gap) * (gap * cg t * F t) :=
        intervalIntegral.integral_mono_on hab hweight_int hmajor_int hpoint
      _ = (C / gap) * ∫ t in a..b, gap * cg t * F t := by
        rw [intervalIntegral.integral_const_mul]
      _ = (C / gap) * (F a - F b) := by rw [hFTC]
  have hnonneg_int :
      0 ≤ ∫ t in a..b, weight t * F t :=
    intervalIntegral.integral_nonneg hab
      (fun t ht => mul_nonneg (hweight_nonneg t ht) (hF_nonneg t))
  refine ⟨by simpa [F, hFdef, mul_comm] using hnonneg_int, ?_⟩
  have hFa : F a = 1 := by
    simp [hFdef]
  have hFb_nonneg : 0 ≤ F b := hF_nonneg b
  have hCgap : 0 ≤ C / gap := div_nonneg hC hgap.le
  have hbase' :
      (∫ t in a..b, weight t * F t) ≤ C / gap := by
    calc
      (∫ t in a..b, weight t * F t) ≤ (C / gap) * (F a - F b) := hbase
      _ ≤ C / gap := by
        rw [hFa]
        nlinarith [mul_nonneg hCgap hFb_nonneg]
  simpa [F, hFdef, mul_comm] using hbase'

/-- Square version of the backward-decay integral bound.

If `weight ≤ C * cg` and `G' = cg`, then the square of a transported amplitude
`D * exp(-gap*(G-G a))` has integral mass at most `D^2 * C/(2*gap)`. -/
theorem forward_weight_decay_square_integral_le
    {a b gap C D : ℝ} {G cg weight : ℝ → ℝ}
    (hab : a ≤ b) (hgap : 0 < gap) (hC : 0 ≤ C)
    (hGcont : Continuous G)
    (hGder : ∀ t ∈ Icc a b, HasDerivAt G (cg t) t)
    (hcg_cont : Continuous cg) (hweight_cont : Continuous weight)
    (hweight_nonneg : ∀ t ∈ Icc a b, 0 ≤ weight t)
    (hweight_bound : ∀ t ∈ Icc a b, weight t ≤ C * cg t) :
    0 ≤
        (∫ t in a..b,
          weight t * (D * Real.exp (-(gap * (G t - G a)))) ^ 2) ∧
      (∫ t in a..b,
          weight t * (D * Real.exp (-(gap * (G t - G a)))) ^ 2) ≤
        D ^ 2 * (C / (2 * gap)) := by
  let F : ℝ → ℝ := fun t =>
    weight t * Real.exp (-((2 * gap) * (G t - G a)))
  let squareFun : ℝ → ℝ := fun t =>
    weight t * (D * Real.exp (-(gap * (G t - G a)))) ^ 2
  have hgap2 : 0 < 2 * gap := by positivity
  have hbase :=
    forward_weight_decay_integral_le
      (a := a) (b := b) (gap := 2 * gap) (C := C)
      (G := G) (cg := cg) (weight := weight)
      hab hgap2 hC hGcont hGder hcg_cont hweight_cont
      hweight_nonneg hweight_bound
  have hF_cont : Continuous F := by
    dsimp [F]
    exact hweight_cont.mul
      (Real.continuous_exp.comp
        ((continuous_const.mul (hGcont.sub continuous_const)).neg))
  have hsquare_cont : Continuous squareFun := by
    dsimp [squareFun]
    exact hweight_cont.mul
      ((continuous_const.mul
        (Real.continuous_exp.comp
          ((continuous_const.mul (hGcont.sub continuous_const)).neg))).pow 2)
  have hsquare_nonneg : ∀ t ∈ Icc a b, 0 ≤ squareFun t := by
    intro t ht
    dsimp [squareFun]
    exact mul_nonneg (hweight_nonneg t ht) (sq_nonneg _)
  have hsquare_int_nonneg :
      0 ≤ ∫ t in a..b, squareFun t :=
    intervalIntegral.integral_nonneg hab hsquare_nonneg
  have hpoint : ∀ t : ℝ, squareFun t = D ^ 2 * F t := by
    intro t
    have hexp_sq :
        Real.exp (-(gap * (G t - G a))) ^ 2 =
          Real.exp (-((2 * gap) * (G t - G a))) := by
      rw [sq, ← Real.exp_add]
      congr 1
      ring
    dsimp [squareFun, F]
    rw [mul_pow, hexp_sq]
    ring
  have hint_eq :
      (∫ t in a..b, squareFun t) = D ^ 2 * ∫ t in a..b, F t := by
    calc
      (∫ t in a..b, squareFun t)
          = ∫ t in a..b, D ^ 2 * F t := by
              refine intervalIntegral.integral_congr ?_
              intro t _ht
              rw [hpoint t]
      _ = D ^ 2 * ∫ t in a..b, F t := by
              rw [intervalIntegral.integral_const_mul]
  refine ⟨by simpa [squareFun] using hsquare_int_nonneg, ?_⟩
  calc
    (∫ t in a..b,
        weight t * (D * Real.exp (-(gap * (G t - G a)))) ^ 2)
        = D ^ 2 * ∫ t in a..b, F t := by
            simpa [squareFun] using hint_eq
    _ ≤ D ^ 2 * (C / (2 * gap)) :=
            mul_le_mul_of_nonneg_left
              (by simpa [F] using hbase.2)
              (sq_nonneg D)

/-- Prefix-reset convolution estimate with the backward Duhamel kernel.

For `K(t)=∫_a^t exp(gap*(G-G a))*reset`, the product
`K(t)*exp(-gap*(G t-G a))` satisfies
`Y' = reset - gap*cg*K*exp(-gap*(G-G a))`.  Hence the weighted convolution by
`cg` is bounded by `(1/gap) * ∫ reset`. -/
theorem forward_prefix_reset_decay_integral_le
    {a b gap : ℝ} {G cg reset : ℝ → ℝ}
    (hab : a ≤ b) (hgap : 0 < gap)
    (hGcont : Continuous G)
    (hGder : ∀ t ∈ Icc a b, HasDerivAt G (cg t) t)
    (hcg_cont : Continuous cg) (hreset_cont : Continuous reset)
    (hcg_nonneg : ∀ t ∈ Icc a b, 0 ≤ cg t)
    (hreset_nonneg : ∀ t ∈ Icc a b, 0 ≤ reset t) :
    0 ≤
        (∫ t in a..b,
          cg t *
            (∫ s in a..t,
              Real.exp (gap * (G s - G a)) * reset s) *
            Real.exp (-(gap * (G t - G a)))) ∧
      (∫ t in a..b,
          cg t *
            (∫ s in a..t,
              Real.exp (gap * (G s - G a)) * reset s) *
            Real.exp (-(gap * (G t - G a)))) ≤
        (1 / gap) * ∫ s in a..b, reset s := by
  let F : ℝ → ℝ := fun t => Real.exp (gap * (G t - G a))
  let D : ℝ → ℝ := fun t => Real.exp (-(gap * (G t - G a)))
  let K : ℝ → ℝ := fun t => ∫ s in a..t, F s * reset s
  let J : ℝ → ℝ := fun t => cg t * K t * D t
  let Y : ℝ → ℝ := fun t => K t * D t
  have hFcont : Continuous F := by
    dsimp [F]
    exact Real.continuous_exp.comp
      (continuous_const.mul (hGcont.sub continuous_const))
  have hDcont : Continuous D := by
    dsimp [D]
    exact Real.continuous_exp.comp
      ((continuous_const.mul (hGcont.sub continuous_const)).neg)
  have hFK_cont : Continuous fun t => F t * reset t := hFcont.mul hreset_cont
  have hKcont : Continuous K := by
    dsimp [K]
    exact continuous_iff_continuousAt.mpr fun t =>
      (intervalIntegral.integral_hasDerivAt_right
        (hFK_cont.intervalIntegrable a t)
        (hFK_cont.stronglyMeasurableAtFilter _ _) hFK_cont.continuousAt).continuousAt
  have hJcont : Continuous J := by
    dsimp [J]
    exact (hcg_cont.mul hKcont).mul hDcont
  have hYcont : Continuous Y := hKcont.mul hDcont
  have hKder : ∀ t : ℝ, HasDerivAt K (F t * reset t) t := by
    intro t
    dsimp [K]
    exact intervalIntegral.integral_hasDerivAt_right
      (hFK_cont.intervalIntegrable a t)
      (hFK_cont.stronglyMeasurableAtFilter _ _) hFK_cont.continuousAt
  have hDder : ∀ t ∈ uIcc a b, HasDerivAt D (-(gap * cg t * D t)) t := by
    intro t ht
    have htIcc : t ∈ Icc a b := by
      rwa [uIcc_of_le hab] at ht
    have h := ((((hGder t htIcc).sub_const (G a)).const_mul gap).neg).exp
    convert h using 1
    · simp [D]
      ring
  have hYder : ∀ t ∈ uIcc a b,
      HasDerivAt Y (reset t - gap * J t) t := by
    intro t ht
    have hmul := (hKder t).mul (hDder t ht)
    convert hmul using 1
    dsimp [Y, J]
    have hcancel : F t * D t = 1 := by
      dsimp [F, D]
      rw [← Real.exp_add,
        show gap * (G t - G a) + -(gap * (G t - G a)) = 0 by ring,
        Real.exp_zero]
    calc
      reset t - gap * (cg t * K t * D t)
          = reset t * (F t * D t) - gap * (cg t * K t * D t) := by
            rw [hcancel]
            ring
      _ = F t * reset t * D t + K t * -(gap * cg t * D t) := by
            ring
  have hder_cont : Continuous fun t => reset t - gap * J t :=
    hreset_cont.sub (continuous_const.mul hJcont)
  have hFTC :
      (∫ t in a..b, reset t - gap * J t) = Y b - Y a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hYder
      (hder_cont.intervalIntegrable a b)
  have hreset_int : IntervalIntegrable reset MeasureTheory.volume a b :=
    hreset_cont.intervalIntegrable a b
  have hgapJ_int : IntervalIntegrable (fun t => gap * J t) MeasureTheory.volume a b :=
    (continuous_const.mul hJcont).intervalIntegrable a b
  have hsplit :
      (∫ t in a..b, reset t - gap * J t) =
        (∫ t in a..b, reset t) - ∫ t in a..b, gap * J t := by
    rw [intervalIntegral.integral_sub hreset_int hgapJ_int]
  have hconst :
      (∫ t in a..b, gap * J t) = gap * ∫ t in a..b, J t := by
    rw [intervalIntegral.integral_const_mul]
  have hmain :
      gap * (∫ t in a..b, J t) =
        (∫ t in a..b, reset t) - (Y b - Y a) := by
    rw [← hconst]
    linarith
  have hK_nonneg : ∀ t ∈ Icc a b, 0 ≤ K t := by
    intro t ht
    dsimp [K, F]
    apply intervalIntegral.integral_nonneg ht.1
    intro s hs
    exact mul_nonneg (Real.exp_pos _).le
      (hreset_nonneg s ⟨hs.1, le_trans hs.2 ht.2⟩)
  have hJ_nonneg : ∀ t ∈ Icc a b, 0 ≤ J t := by
    intro t ht
    dsimp [J, D]
    exact mul_nonneg (mul_nonneg (hcg_nonneg t ht) (hK_nonneg t ht))
      (Real.exp_pos _).le
  have hJint_nonneg :
      0 ≤ ∫ t in a..b, J t :=
    intervalIntegral.integral_nonneg hab hJ_nonneg
  have hYa : Y a = 0 := by
    dsimp [Y, K]
    simp
  have hYb_nonneg : 0 ≤ Y b := by
    dsimp [Y, D]
    have hb : b ∈ Icc a b := ⟨hab, le_rfl⟩
    exact mul_nonneg (hK_nonneg b hb) (Real.exp_pos _).le
  have hmul_le :
      gap * (∫ t in a..b, J t) ≤ ∫ t in a..b, reset t := by
    rw [hmain, hYa]
    nlinarith [hYb_nonneg]
  have hle_div :
      (∫ t in a..b, J t) ≤ (∫ t in a..b, reset t) / gap :=
    (le_div_iff₀ hgap).mpr (by simpa [mul_comm] using hmul_le)
  refine ⟨by simpa [J, D, K, mul_assoc] using hJint_nonneg, ?_⟩
  calc
    (∫ t in a..b,
        cg t *
          (∫ s in a..t, Real.exp (gap * (G s - G a)) * reset s) *
          Real.exp (-(gap * (G t - G a))))
        = ∫ t in a..b, J t := by
          refine intervalIntegral.integral_congr ?_
          intro t _ht
          rfl
    _ ≤ (∫ t in a..b, reset t) / gap := hle_div
    _ = (1 / gap) * ∫ s in a..b, reset s := by ring

/-- Weighted form of `forward_prefix_reset_decay_integral_le`.

If `weight ≤ C * cg`, the same prefix-reset convolution with `weight` is
bounded by `(C/gap) * ∫ reset`. -/
theorem forward_weight_prefix_reset_decay_integral_le
    {a b gap C : ℝ} {G cg weight reset : ℝ → ℝ}
    (hab : a ≤ b) (hgap : 0 < gap) (hC : 0 ≤ C)
    (hGcont : Continuous G)
    (hGder : ∀ t ∈ Icc a b, HasDerivAt G (cg t) t)
    (hcg_cont : Continuous cg) (hweight_cont : Continuous weight)
    (hreset_cont : Continuous reset)
    (hcg_nonneg : ∀ t ∈ Icc a b, 0 ≤ cg t)
    (hreset_nonneg : ∀ t ∈ Icc a b, 0 ≤ reset t)
    (hweight_nonneg : ∀ t ∈ Icc a b, 0 ≤ weight t)
    (hweight_bound : ∀ t ∈ Icc a b, weight t ≤ C * cg t) :
    0 ≤
        (∫ t in a..b,
          weight t *
            (∫ s in a..t,
              Real.exp (gap * (G s - G a)) * reset s) *
            Real.exp (-(gap * (G t - G a)))) ∧
      (∫ t in a..b,
          weight t *
            (∫ s in a..t,
              Real.exp (gap * (G s - G a)) * reset s) *
            Real.exp (-(gap * (G t - G a)))) ≤
        (C / gap) * ∫ s in a..b, reset s := by
  let K : ℝ → ℝ := fun t =>
    ∫ s in a..t, Real.exp (gap * (G s - G a)) * reset s
  let D : ℝ → ℝ := fun t => Real.exp (-(gap * (G t - G a)))
  let left : ℝ → ℝ := fun t => weight t * K t * D t
  let right : ℝ → ℝ := fun t => (C * cg t) * K t * D t
  let cgKernel : ℝ → ℝ := fun t => cg t * K t * D t
  have hFcont : Continuous fun t => Real.exp (gap * (G t - G a)) * reset t := by
    exact (Real.continuous_exp.comp
      (continuous_const.mul (hGcont.sub continuous_const))).mul hreset_cont
  have hKcont : Continuous K := by
    dsimp [K]
    exact continuous_iff_continuousAt.mpr fun t =>
      (intervalIntegral.integral_hasDerivAt_right
        (hFcont.intervalIntegrable a t)
        (hFcont.stronglyMeasurableAtFilter _ _) hFcont.continuousAt).continuousAt
  have hDcont : Continuous D := by
    dsimp [D]
    exact Real.continuous_exp.comp
      ((continuous_const.mul (hGcont.sub continuous_const)).neg)
  have hleft_cont : Continuous left := (hweight_cont.mul hKcont).mul hDcont
  have hright_cont : Continuous right :=
    ((continuous_const.mul hcg_cont).mul hKcont).mul hDcont
  have hK_nonneg : ∀ t ∈ Icc a b, 0 ≤ K t := by
    intro t ht
    dsimp [K]
    apply intervalIntegral.integral_nonneg ht.1
    intro s hs
    exact mul_nonneg (Real.exp_pos _).le
      (hreset_nonneg s ⟨hs.1, le_trans hs.2 ht.2⟩)
  have hpoint : ∀ t ∈ Icc a b, left t ≤ right t := by
    intro t ht
    dsimp [left, right, D]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hweight_bound t ht) (hK_nonneg t ht))
      (Real.exp_pos _).le
  have hmono :
      (∫ t in a..b, left t) ≤ ∫ t in a..b, right t :=
    intervalIntegral.integral_mono_on hab
      (hleft_cont.intervalIntegrable a b)
      (hright_cont.intervalIntegrable a b)
      hpoint
  have hbase :=
    forward_prefix_reset_decay_integral_le
      (a := a) (b := b) (gap := gap) (G := G) (cg := cg) (reset := reset)
      hab hgap hGcont hGder hcg_cont hreset_cont hcg_nonneg hreset_nonneg
  have hright_eq :
      (∫ t in a..b, right t) =
        C * ∫ t in a..b, cgKernel t := by
    dsimp [right, cgKernel]
    calc
      (∫ t in a..b, C * cg t * K t * D t)
          = ∫ t in a..b, C * (cg t * K t * D t) := by
            refine intervalIntegral.integral_congr ?_
            intro t _ht
            ring
      _ = C * ∫ t in a..b, cg t * K t * D t := by
            rw [intervalIntegral.integral_const_mul]
  have hcgKernel_base :
      (∫ t in a..b, cgKernel t) ≤
        (1 / gap) * ∫ s in a..b, reset s := by
    calc
      (∫ t in a..b, cgKernel t)
          = ∫ t in a..b,
              cg t *
                (∫ s in a..t,
                  Real.exp (gap * (G s - G a)) * reset s) *
                Real.exp (-(gap * (G t - G a))) := by
            refine intervalIntegral.integral_congr ?_
            intro t _ht
            rfl
      _ ≤ (1 / gap) * ∫ s in a..b, reset s := hbase.2
  have hleft_nonneg :
      0 ≤ ∫ t in a..b, left t := by
    apply intervalIntegral.integral_nonneg hab
    intro t ht
    dsimp [left, D]
    exact mul_nonneg (mul_nonneg (hweight_nonneg t ht) (hK_nonneg t ht))
      (Real.exp_pos _).le
  refine ⟨?_, ?_⟩
  · exact hleft_nonneg
  · calc
      (∫ t in a..b, weight t * K t * D t)
          = ∫ t in a..b, left t := rfl
      _ ≤ ∫ t in a..b, right t := hmono
      _ = C * ∫ t in a..b, cgKernel t := hright_eq
      _ ≤ C * ((1 / gap) * ∫ s in a..b, reset s) :=
            mul_le_mul_of_nonneg_left hcgKernel_base hC
      _ = (C / gap) * ∫ s in a..b, reset s := by ring

/-- Square-integral version of the prefix-reset convolution estimate.

If `reset ≤ C * cg`, the Duhamel prefix
`Y(t) = (∫_a^t exp(gap*(G-G a))*reset) * exp(-gap*(G t-G a))`
is pointwise at most `C / gap`.  Combining this with the linear
`cg * Y` estimate gives a q-free `L^2(cg dt)` bound. -/
theorem forward_prefix_reset_decay_square_integral_le
    {a b gap C : ℝ} {G cg reset : ℝ → ℝ}
    (hab : a ≤ b) (hgap : 0 < gap) (hC : 0 ≤ C)
    (hGcont : Continuous G)
    (hGder : ∀ t ∈ Icc a b, HasDerivAt G (cg t) t)
    (hcg_cont : Continuous cg) (hreset_cont : Continuous reset)
    (hcg_nonneg : ∀ t ∈ Icc a b, 0 ≤ cg t)
    (hreset_nonneg : ∀ t ∈ Icc a b, 0 ≤ reset t)
    (hreset_bound : ∀ t ∈ Icc a b, reset t ≤ C * cg t) :
    0 ≤
        (∫ t in a..b,
          cg t *
            ((∫ s in a..t,
              Real.exp (gap * (G s - G a)) * reset s) *
              Real.exp (-(gap * (G t - G a)))) ^ 2) ∧
      (∫ t in a..b,
          cg t *
            ((∫ s in a..t,
              Real.exp (gap * (G s - G a)) * reset s) *
              Real.exp (-(gap * (G t - G a)))) ^ 2) ≤
        (C / gap) * ((1 / gap) * ∫ s in a..b, reset s) := by
  let K : ℝ → ℝ := fun t =>
    ∫ s in a..t, Real.exp (gap * (G s - G a)) * reset s
  let D : ℝ → ℝ := fun t => Real.exp (-(gap * (G t - G a)))
  let Y : ℝ → ℝ := fun t => K t * D t
  let squareKernel : ℝ → ℝ := fun t => cg t * (Y t) ^ 2
  let linearKernel : ℝ → ℝ := fun t => cg t * Y t
  have hresetExp_cont : Continuous fun s : ℝ =>
      Real.exp (gap * (G s - G a)) * reset s := by
    exact (Real.continuous_exp.comp
      (continuous_const.mul (hGcont.sub continuous_const))).mul hreset_cont
  have hK_cont : Continuous K := by
    dsimp [K]
    exact continuous_iff_continuousAt.mpr fun t =>
      (intervalIntegral.integral_hasDerivAt_right
        (hresetExp_cont.intervalIntegrable a t)
        (hresetExp_cont.stronglyMeasurableAtFilter _ _)
        hresetExp_cont.continuousAt).continuousAt
  have hD_cont : Continuous D := by
    dsimp [D]
    exact Real.continuous_exp.comp
      ((continuous_const.mul (hGcont.sub continuous_const)).neg)
  have hY_cont : Continuous Y := hK_cont.mul hD_cont
  have hsquare_cont : Continuous squareKernel := by
    dsimp [squareKernel]
    exact hcg_cont.mul (hY_cont.pow 2)
  have hlinear_cont : Continuous linearKernel := by
    dsimp [linearKernel]
    exact hcg_cont.mul hY_cont
  have hY_nonneg : ∀ t ∈ Icc a b, 0 ≤ Y t := by
    intro t ht
    have hK_nonneg : 0 ≤ K t := by
      dsimp [K]
      apply intervalIntegral.integral_nonneg ht.1
      intro s hs
      exact mul_nonneg (Real.exp_pos _).le
        (hreset_nonneg s ⟨hs.1, le_trans hs.2 ht.2⟩)
    dsimp [Y, D]
    exact mul_nonneg hK_nonneg (Real.exp_pos _).le
  have hY_le : ∀ t ∈ Icc a b, Y t ≤ C / gap := by
    intro t ht
    have hpoint :=
      forward_reset_integral_mul_decay_le
        (a := a) (b := t) (gap := gap) (C := C)
        (G := G) (cg := cg) (reset := reset)
        ht.1 hgap hC hGcont
        (fun s hs => hGder s ⟨hs.1, le_trans hs.2 ht.2⟩)
        hcg_cont hreset_cont
        (fun s hs => hreset_nonneg s ⟨hs.1, le_trans hs.2 ht.2⟩)
        (fun s hs => hreset_bound s ⟨hs.1, le_trans hs.2 ht.2⟩)
    simpa [Y, K, D] using hpoint.2
  have hCgap_nonneg : 0 ≤ C / gap := div_nonneg hC hgap.le
  have hpoint_square : ∀ t ∈ Icc a b,
      squareKernel t ≤ (C / gap) * linearKernel t := by
    intro t ht
    have hy_nonneg := hY_nonneg t ht
    have hy_le := hY_le t ht
    have hy_sq : (Y t) ^ 2 ≤ (C / gap) * Y t := by
      calc
        (Y t) ^ 2 = (Y t) * (Y t) := by ring
        _ ≤ (C / gap) * Y t :=
            mul_le_mul_of_nonneg_right hy_le hy_nonneg
    have hcg_t_nonneg := hcg_nonneg t ht
    dsimp [squareKernel, linearKernel]
    calc
      cg t * (Y t) ^ 2 ≤ cg t * ((C / gap) * Y t) :=
        mul_le_mul_of_nonneg_left hy_sq hcg_t_nonneg
      _ = (C / gap) * (cg t * Y t) := by ring
  have hsquare_nonneg : ∀ t ∈ Icc a b, 0 ≤ squareKernel t := by
    intro t ht
    dsimp [squareKernel]
    exact mul_nonneg (hcg_nonneg t ht) (sq_nonneg _)
  have hsquare_int_nonneg :
      0 ≤ ∫ t in a..b, squareKernel t :=
    intervalIntegral.integral_nonneg hab hsquare_nonneg
  have hmono :
      (∫ t in a..b, squareKernel t) ≤
        ∫ t in a..b, (C / gap) * linearKernel t :=
    intervalIntegral.integral_mono_on hab
      (hsquare_cont.intervalIntegrable a b)
      ((continuous_const.mul hlinear_cont).intervalIntegrable a b)
      hpoint_square
  have hlinear :=
    forward_prefix_reset_decay_integral_le
      (a := a) (b := b) (gap := gap)
      (G := G) (cg := cg) (reset := reset)
      hab hgap hGcont hGder hcg_cont hreset_cont hcg_nonneg hreset_nonneg
  refine ⟨?_, ?_⟩
  · simpa [squareKernel, Y, K, D] using hsquare_int_nonneg
  · calc
      (∫ t in a..b,
          cg t *
            ((∫ s in a..t,
              Real.exp (gap * (G s - G a)) * reset s) *
              Real.exp (-(gap * (G t - G a)))) ^ 2)
          = ∫ t in a..b, squareKernel t := by
              rfl
      _ ≤ ∫ t in a..b, (C / gap) * linearKernel t := hmono
      _ = (C / gap) * ∫ t in a..b, linearKernel t := by
              rw [intervalIntegral.integral_const_mul]
      _ ≤ (C / gap) * ((1 / gap) * ∫ s in a..b, reset s) :=
              mul_le_mul_of_nonneg_left
                (by simpa [linearKernel, Y, K, D, mul_assoc] using hlinear.2)
                hCgap_nonneg

/-- Splitting a Duhamel reset integral at a hold time.  The prefix contribution is
kept with the stronger decay at `bH`; the tail is shifted to base point `bH`
and discharged by `forward_reset_integral_mul_decay_le`. -/
theorem hold_tail_split_decay_le
    {a bH t gap C R0 : ℝ} {G cg reset : ℝ → ℝ}
    (habH : a ≤ bH) (hbHt : bH ≤ t) (hgap : 0 < gap) (hC : 0 ≤ C) (hR0 : 0 ≤ R0)
    (hGcont : Continuous G)
    (hGder : ∀ s ∈ Icc a t, HasDerivAt G (cg s) s)
    (hcg_cont : Continuous cg) (hreset_cont : Continuous reset)
    (hreset_nonneg : ∀ s ∈ Icc a t, 0 ≤ reset s)
    (_hcg_nonneg : ∀ s ∈ Icc bH t, 0 ≤ cg s)
    (hreset_bound : ∀ s ∈ Icc bH t, reset s ≤ C * cg s)
    (hG_mono : G bH ≤ G t) :
    (R0 + ∫ s in a..t, Real.exp (gap * (G s - G a)) * reset s) *
        Real.exp (-(gap * (G t - G a))) ≤
      (R0 + ∫ s in a..bH, Real.exp (gap * (G s - G a)) * reset s) *
        Real.exp (-(gap * (G bH - G a))) + C / gap := by
  let fA : ℝ → ℝ := fun s => Real.exp (gap * (G s - G a)) * reset s
  let fH : ℝ → ℝ := fun s => Real.exp (gap * (G s - G bH)) * reset s
  have hfA_cont : Continuous fA := by
    dsimp [fA]
    exact (Real.continuous_exp.comp
      (continuous_const.mul (hGcont.sub continuous_const))).mul hreset_cont
  have hsplit :
      (∫ s in a..bH, fA s) + (∫ s in bH..t, fA s) =
        ∫ s in a..t, fA s :=
    intervalIntegral.integral_add_adjacent_intervals
      (hfA_cont.intervalIntegrable a bH)
      (hfA_cont.intervalIntegrable bH t)
  have hIab_nonneg :
      0 ≤ ∫ s in a..bH, fA s := by
    apply intervalIntegral.integral_nonneg habH
    intro s hs
    exact mul_nonneg (Real.exp_pos _).le
      (hreset_nonneg s ⟨hs.1, le_trans hs.2 hbHt⟩)
  have hhold_coeff_nonneg :
      0 ≤ R0 + ∫ s in a..bH, fA s :=
    add_nonneg hR0 hIab_nonneg
  have hdecay_le :
      Real.exp (-(gap * (G t - G a))) ≤
        Real.exp (-(gap * (G bH - G a))) := by
    refine Real.exp_le_exp.mpr ?_
    have hdelta : G bH - G a ≤ G t - G a := by linarith
    have hmul : gap * (G bH - G a) ≤ gap * (G t - G a) :=
      mul_le_mul_of_nonneg_left hdelta hgap.le
    linarith
  have hhold :
      (R0 + ∫ s in a..bH, fA s) * Real.exp (-(gap * (G t - G a))) ≤
        (R0 + ∫ s in a..bH, fA s) * Real.exp (-(gap * (G bH - G a))) :=
    mul_le_mul_of_nonneg_left hdecay_le hhold_coeff_nonneg
  have htail_shift :
      (∫ s in bH..t, fA s) * Real.exp (-(gap * (G t - G a))) =
        (∫ s in bH..t, fH s) * Real.exp (-(gap * (G t - G bH))) := by
    have hIshift :
        (∫ s in bH..t, fA s) =
          Real.exp (gap * (G bH - G a)) * ∫ s in bH..t, fH s := by
      calc
        (∫ s in bH..t, fA s)
            = ∫ s in bH..t,
                Real.exp (gap * (G bH - G a)) * fH s := by
                refine intervalIntegral.integral_congr ?_
                intro s _hs
                dsimp [fA, fH]
                rw [show gap * (G s - G a) =
                    gap * (G s - G bH) + gap * (G bH - G a) by ring,
                  Real.exp_add]
                ring
        _ = Real.exp (gap * (G bH - G a)) *
              ∫ s in bH..t, fH s := by
              rw [intervalIntegral.integral_const_mul]
    have hexp :
        Real.exp (gap * (G bH - G a)) *
            Real.exp (-(gap * (G t - G a))) =
          Real.exp (-(gap * (G t - G bH))) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hIshift]
    calc
      (Real.exp (gap * (G bH - G a)) * ∫ s in bH..t, fH s) *
          Real.exp (-(gap * (G t - G a)))
          = (∫ s in bH..t, fH s) *
              (Real.exp (gap * (G bH - G a)) *
                Real.exp (-(gap * (G t - G a)))) := by ring
      _ = (∫ s in bH..t, fH s) *
              Real.exp (-(gap * (G t - G bH))) := by rw [hexp]
  have htail_forward := forward_reset_integral_mul_decay_le
    (a := bH) (b := t) (gap := gap) (C := C)
    (G := G) (cg := cg) (reset := reset)
    hbHt hgap hC hGcont
    (fun s hs => hGder s ⟨le_trans habH hs.1, hs.2⟩)
    hcg_cont hreset_cont
    (fun s hs => hreset_nonneg s ⟨le_trans habH hs.1, hs.2⟩)
    hreset_bound
  have htail :
      (∫ s in bH..t, fA s) * Real.exp (-(gap * (G t - G a))) ≤ C / gap := by
    rw [htail_shift]
    exact htail_forward.2
  calc
    (R0 + ∫ s in a..t, Real.exp (gap * (G s - G a)) * reset s) *
        Real.exp (-(gap * (G t - G a)))
        =
      ((R0 + ∫ s in a..bH, fA s) + ∫ s in bH..t, fA s) *
        Real.exp (-(gap * (G t - G a))) := by
          rw [← hsplit]
          dsimp [fA]
          ring
    _ =
      (R0 + ∫ s in a..bH, fA s) * Real.exp (-(gap * (G t - G a))) +
        (∫ s in bH..t, fA s) * Real.exp (-(gap * (G t - G a))) := by
          ring
    _ ≤
      (R0 + ∫ s in a..bH, fA s) * Real.exp (-(gap * (G bH - G a))) + C / gap :=
        add_le_add hhold htail
    _ =
      (R0 + ∫ s in a..bH, Real.exp (gap * (G s - G a)) * reset s) *
          Real.exp (-(gap * (G bH - G a))) + C / gap := by
          dsimp [fA]

/-- Standalone concrete forward-integral Duhamel residual.  The reset/gate
ratio is carried as the schedule-only inequality
`reset ≤ Cratio*exp(-cα*a_j)*cg`; the conclusion itself is the residual limit. -/
theorem solMURepl_forwardResetIntegral_duhamel_tendsto_zero
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    {cfg : ℕ → ℕ → UConf}
    (inputs : SelectorReplicatorConcInputs sol cfg) (w : ℕ)
    {gap0 Cratio : ℝ}
    (hgap0 : 0 < gap0)
    (hgap_lb : ∀ᶠ j in atTop, gap0 ≤ inputs.gap w j)
    (hκ₀_nonneg : 0 ≤ (κ₀ : ℝ))
    (hCratio_nonneg : 0 ≤ Cratio)
    (hratio_bound : ∀ j, ∀ t ∈
      Icc (selectorMUWriteStartTime j) (selectorMUWriteReadTime j),
        (((1 + Real.cos t) / 2) ^ Mcy * (κ₀ : ℝ)) ≤
          (Cratio * Real.exp (-(bgpParams38.cα * selectorMUWriteStartTime j))) *
            (((1 + Real.sin t) / 2) ^ Mcy *
              ((g₀ : ℝ) * Real.exp (bgpParams38.cα * t)))) :
    Tendsto
      (fun j =>
        solMUReplForwardResetIntegral inputs w j *
          Real.exp
            (-(inputs.gap w j *
              ((sol w).G (selectorMUWriteReadTime j)
                - (sol w).G (selectorMUWriteStartTime j)))))
      atTop (𝓝 0) := by
  have hcα : 0 < bgpParams38.cα := by norm_num [bgpParams38]
  have hstart_atTop :
      Tendsto (fun j : ℕ => selectorMUWriteStartTime j) atTop atTop := by
    have hlin : Tendsto (fun j : ℕ => (2 * Real.pi) * (j : ℝ)) atTop atTop :=
      Filter.Tendsto.const_mul_atTop (by positivity : (0 : ℝ) < 2 * Real.pi)
        tendsto_natCast_atTop_atTop
    have hadd :
        Tendsto (fun j : ℕ => (2 * Real.pi) * (j : ℝ) + Real.pi / 6) atTop atTop := by
      exact Filter.tendsto_atTop_add_const_right atTop (Real.pi / 6) hlin
    simpa [selectorMUWriteStartTime, mul_assoc] using hadd
  have hscaled :
      Tendsto (fun j : ℕ => bgpParams38.cα * selectorMUWriteStartTime j) atTop atTop :=
    hstart_atTop.const_mul_atTop hcα
  have hdecay :
      Tendsto (fun j : ℕ =>
        Real.exp (-(bgpParams38.cα * selectorMUWriteStartTime j))) atTop (𝓝 0) := by
    have hneg :
        Tendsto (fun j : ℕ => -(bgpParams38.cα * selectorMUWriteStartTime j))
          atTop atBot :=
      Filter.tendsto_neg_atBot_iff.mpr hscaled
    exact Real.tendsto_exp_atBot.comp hneg
  have hupper :
      Tendsto (fun j : ℕ =>
        (Cratio / gap0) *
          Real.exp (-(bgpParams38.cα * selectorMUWriteStartTime j))) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hdecay
  refine squeeze_zero' ?_ ?_ hupper
  · filter_upwards [hgap_lb] with j hgapj
    have hgap_pos : 0 < inputs.gap w j := lt_of_lt_of_le hgap0 hgapj
    have hCj_nonneg :
        0 ≤ Cratio * Real.exp (-(bgpParams38.cα * selectorMUWriteStartTime j)) :=
      mul_nonneg hCratio_nonneg (Real.exp_pos _).le
    have hreset_nonneg :
        ∀ t ∈ Icc (selectorMUWriteStartTime j) (selectorMUWriteReadTime j),
          0 ≤ (((1 + Real.cos t) / 2) ^ Mcy * (κ₀ : ℝ)) := by
      intro t _ht
      have hcos : 0 ≤ (1 + Real.cos t) / 2 := by
        nlinarith [Real.neg_one_le_cos t]
      exact mul_nonneg (pow_nonneg hcos Mcy) hκ₀_nonneg
    have hbound := forward_reset_integral_mul_decay_le
      (a := selectorMUWriteStartTime j)
      (b := selectorMUWriteReadTime j)
      (gap := inputs.gap w j)
      (C := Cratio * Real.exp (-(bgpParams38.cα * selectorMUWriteStartTime j)))
      (G := (sol w).G)
      (cg := fun t =>
        ((1 + Real.sin t) / 2) ^ Mcy *
          ((g₀ : ℝ) * Real.exp (bgpParams38.cα * t)))
      (reset := fun t => ((1 + Real.cos t) / 2) ^ Mcy * (κ₀ : ℝ))
      (selectorMUWriteStart_le_read j) hgap_pos hCj_nonneg
      (sol w).cont_G
      (fun t ht => (sol w).G_hasDeriv t (selectorMU_hdom_writeStart w j t ht))
      (by fun_prop) (by fun_prop) hreset_nonneg
      (fun t ht => by simpa [mul_assoc] using hratio_bound j t ht)
    simpa [solMUReplForwardResetIntegral] using hbound.1
  · filter_upwards [hgap_lb] with j hgapj
    have hgap_pos : 0 < inputs.gap w j := lt_of_lt_of_le hgap0 hgapj
    have hCj_nonneg :
        0 ≤ Cratio * Real.exp (-(bgpParams38.cα * selectorMUWriteStartTime j)) :=
      mul_nonneg hCratio_nonneg (Real.exp_pos _).le
    have hreset_nonneg :
        ∀ t ∈ Icc (selectorMUWriteStartTime j) (selectorMUWriteReadTime j),
          0 ≤ (((1 + Real.cos t) / 2) ^ Mcy * (κ₀ : ℝ)) := by
      intro t _ht
      have hcos : 0 ≤ (1 + Real.cos t) / 2 := by
        nlinarith [Real.neg_one_le_cos t]
      exact mul_nonneg (pow_nonneg hcos Mcy) hκ₀_nonneg
    have hbound := forward_reset_integral_mul_decay_le
      (a := selectorMUWriteStartTime j)
      (b := selectorMUWriteReadTime j)
      (gap := inputs.gap w j)
      (C := Cratio * Real.exp (-(bgpParams38.cα * selectorMUWriteStartTime j)))
      (G := (sol w).G)
      (cg := fun t =>
        ((1 + Real.sin t) / 2) ^ Mcy *
          ((g₀ : ℝ) * Real.exp (bgpParams38.cα * t)))
      (reset := fun t => ((1 + Real.cos t) / 2) ^ Mcy * (κ₀ : ℝ))
      (selectorMUWriteStart_le_read j) hgap_pos hCj_nonneg
      (sol w).cont_G
      (fun t ht => (sol w).G_hasDeriv t (selectorMU_hdom_writeStart w j t ht))
      (by fun_prop) (by fun_prop) hreset_nonneg
      (fun t ht => by simpa [mul_assoc] using hratio_bound j t ht)
    have hle_gap :
        (Cratio * Real.exp (-(bgpParams38.cα * selectorMUWriteStartTime j))) /
            inputs.gap w j ≤
          (Cratio * Real.exp (-(bgpParams38.cα * selectorMUWriteStartTime j))) / gap0 := by
      have hinv : 1 / inputs.gap w j ≤ 1 / gap0 :=
        one_div_le_one_div_of_le hgap0 hgapj
      have hmul := mul_le_mul_of_nonneg_left hinv hCj_nonneg
      simpa [div_eq_mul_inv, one_div, mul_assoc] using hmul
    have hrewrite :
        (Cratio * Real.exp (-(bgpParams38.cα * selectorMUWriteStartTime j))) / gap0 =
          (Cratio / gap0) *
            Real.exp (-(bgpParams38.cα * selectorMUWriteStartTime j)) := by
      field_simp [hgap0.ne']
    calc
      solMUReplForwardResetIntegral inputs w j *
          Real.exp
            (-(inputs.gap w j *
              ((sol w).G (selectorMUWriteReadTime j)
                - (sol w).G (selectorMUWriteStartTime j))))
          ≤
            (Cratio * Real.exp (-(bgpParams38.cα * selectorMUWriteStartTime j))) /
              inputs.gap w j := by
              simpa [solMUReplForwardResetIntegral] using hbound.2
      _ ≤
            (Cratio * Real.exp (-(bgpParams38.cα * selectorMUWriteStartTime j))) /
              gap0 := hle_gap
      _ =
            (Cratio / gap0) *
              Real.exp (-(bgpParams38.cα * selectorMUWriteStartTime j)) := hrewrite

/-- Standalone concrete prefix-integral Duhamel residual over
`[selectorMUWriteStartTime j, selectorMUWriteHoldTime j] = [π/6,π/2]`.

This is the settled-window residual discharge used before the z-write starts:
the forward reset coefficient itself may grow, but after multiplying by the
backward concentration factor it is bounded by
`(Cratio / gap0) * exp (-cα * selectorMUWriteStartTime j)`, hence vanishes. -/
theorem solMURepl_preForwardResetIntegral_duhamel_tendsto_zero
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    {cfg : ℕ → ℕ → UConf}
    (inputs : SelectorReplicatorConcInputs sol cfg) (w : ℕ)
    {gap0 Cratio : ℝ}
    (hgap0 : 0 < gap0)
    (hgap_lb : ∀ᶠ j in atTop, gap0 ≤ inputs.gap w j)
    (hκ₀_nonneg : 0 ≤ (κ₀ : ℝ))
    (hCratio_nonneg : 0 ≤ Cratio)
    (hratio_bound : ∀ j, ∀ t ∈
      Icc (selectorMUWriteStartTime j) (selectorMUWriteHoldTime j),
        (((1 + Real.cos t) / 2) ^ Mcy * (κ₀ : ℝ)) ≤
          (Cratio * Real.exp (-(bgpParams38.cα * selectorMUWriteStartTime j))) *
            (((1 + Real.sin t) / 2) ^ Mcy *
              ((g₀ : ℝ) * Real.exp (bgpParams38.cα * t)))) :
    Tendsto
      (fun j =>
        solMUReplPreForwardResetIntegral inputs w j *
          Real.exp
            (-(inputs.gap w j *
              ((sol w).G (selectorMUWriteHoldTime j)
                - (sol w).G (selectorMUWriteStartTime j)))))
      atTop (𝓝 0) := by
  have hcα : 0 < bgpParams38.cα := by norm_num [bgpParams38]
  have hstart_atTop :
      Tendsto (fun j : ℕ => selectorMUWriteStartTime j) atTop atTop := by
    have hlin : Tendsto (fun j : ℕ => (2 * Real.pi) * (j : ℝ)) atTop atTop :=
      Filter.Tendsto.const_mul_atTop (by positivity : (0 : ℝ) < 2 * Real.pi)
        tendsto_natCast_atTop_atTop
    have hadd :
        Tendsto (fun j : ℕ => (2 * Real.pi) * (j : ℝ) + Real.pi / 6) atTop atTop := by
      exact Filter.tendsto_atTop_add_const_right atTop (Real.pi / 6) hlin
    simpa [selectorMUWriteStartTime, mul_assoc] using hadd
  have hscaled :
      Tendsto (fun j : ℕ => bgpParams38.cα * selectorMUWriteStartTime j) atTop atTop :=
    hstart_atTop.const_mul_atTop hcα
  have hdecay :
      Tendsto (fun j : ℕ =>
        Real.exp (-(bgpParams38.cα * selectorMUWriteStartTime j))) atTop (𝓝 0) := by
    have hneg :
        Tendsto (fun j : ℕ => -(bgpParams38.cα * selectorMUWriteStartTime j))
          atTop atBot :=
      Filter.tendsto_neg_atBot_iff.mpr hscaled
    exact Real.tendsto_exp_atBot.comp hneg
  have hupper :
      Tendsto (fun j : ℕ =>
        (Cratio / gap0) *
          Real.exp (-(bgpParams38.cα * selectorMUWriteStartTime j))) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hdecay
  refine squeeze_zero' ?_ ?_ hupper
  · filter_upwards [hgap_lb] with j hgapj
    have hgap_pos : 0 < inputs.gap w j := lt_of_lt_of_le hgap0 hgapj
    have hCj_nonneg :
        0 ≤ Cratio * Real.exp (-(bgpParams38.cα * selectorMUWriteStartTime j)) :=
      mul_nonneg hCratio_nonneg (Real.exp_pos _).le
    have hreset_nonneg :
        ∀ t ∈ Icc (selectorMUWriteStartTime j) (selectorMUWriteHoldTime j),
          0 ≤ (((1 + Real.cos t) / 2) ^ Mcy * (κ₀ : ℝ)) := by
      intro t _ht
      have hcos : 0 ≤ (1 + Real.cos t) / 2 := by
        nlinarith [Real.neg_one_le_cos t]
      exact mul_nonneg (pow_nonneg hcos Mcy) hκ₀_nonneg
    have hbound := forward_reset_integral_mul_decay_le
      (a := selectorMUWriteStartTime j)
      (b := selectorMUWriteHoldTime j)
      (gap := inputs.gap w j)
      (C := Cratio * Real.exp (-(bgpParams38.cα * selectorMUWriteStartTime j)))
      (G := (sol w).G)
      (cg := fun t =>
        ((1 + Real.sin t) / 2) ^ Mcy *
          ((g₀ : ℝ) * Real.exp (bgpParams38.cα * t)))
      (reset := fun t => ((1 + Real.cos t) / 2) ^ Mcy * (κ₀ : ℝ))
      (selectorMUWriteStart_le_hold j) hgap_pos hCj_nonneg
      (sol w).cont_G
      (fun t ht => (sol w).G_hasDeriv t (selectorMU_hdom_writeHold w j t ht))
      (by fun_prop) (by fun_prop) hreset_nonneg
      (fun t ht => by simpa [mul_assoc] using hratio_bound j t ht)
    simpa [solMUReplPreForwardResetIntegral] using hbound.1
  · filter_upwards [hgap_lb] with j hgapj
    have hgap_pos : 0 < inputs.gap w j := lt_of_lt_of_le hgap0 hgapj
    have hCj_nonneg :
        0 ≤ Cratio * Real.exp (-(bgpParams38.cα * selectorMUWriteStartTime j)) :=
      mul_nonneg hCratio_nonneg (Real.exp_pos _).le
    have hreset_nonneg :
        ∀ t ∈ Icc (selectorMUWriteStartTime j) (selectorMUWriteHoldTime j),
          0 ≤ (((1 + Real.cos t) / 2) ^ Mcy * (κ₀ : ℝ)) := by
      intro t _ht
      have hcos : 0 ≤ (1 + Real.cos t) / 2 := by
        nlinarith [Real.neg_one_le_cos t]
      exact mul_nonneg (pow_nonneg hcos Mcy) hκ₀_nonneg
    have hbound := forward_reset_integral_mul_decay_le
      (a := selectorMUWriteStartTime j)
      (b := selectorMUWriteHoldTime j)
      (gap := inputs.gap w j)
      (C := Cratio * Real.exp (-(bgpParams38.cα * selectorMUWriteStartTime j)))
      (G := (sol w).G)
      (cg := fun t =>
        ((1 + Real.sin t) / 2) ^ Mcy *
          ((g₀ : ℝ) * Real.exp (bgpParams38.cα * t)))
      (reset := fun t => ((1 + Real.cos t) / 2) ^ Mcy * (κ₀ : ℝ))
      (selectorMUWriteStart_le_hold j) hgap_pos hCj_nonneg
      (sol w).cont_G
      (fun t ht => (sol w).G_hasDeriv t (selectorMU_hdom_writeHold w j t ht))
      (by fun_prop) (by fun_prop) hreset_nonneg
      (fun t ht => by simpa [mul_assoc] using hratio_bound j t ht)
    have hle_gap :
        (Cratio * Real.exp (-(bgpParams38.cα * selectorMUWriteStartTime j))) /
            inputs.gap w j ≤
          (Cratio * Real.exp (-(bgpParams38.cα * selectorMUWriteStartTime j))) / gap0 := by
      have hinv : 1 / inputs.gap w j ≤ 1 / gap0 :=
        one_div_le_one_div_of_le hgap0 hgapj
      have hmul := mul_le_mul_of_nonneg_left hinv hCj_nonneg
      simpa [div_eq_mul_inv, one_div, mul_assoc] using hmul
    have hrewrite :
        (Cratio * Real.exp (-(bgpParams38.cα * selectorMUWriteStartTime j))) / gap0 =
          (Cratio / gap0) *
            Real.exp (-(bgpParams38.cα * selectorMUWriteStartTime j)) := by
      field_simp [hgap0.ne']
    calc
      solMUReplPreForwardResetIntegral inputs w j *
          Real.exp
            (-(inputs.gap w j *
              ((sol w).G (selectorMUWriteHoldTime j)
                - (sol w).G (selectorMUWriteStartTime j))))
          ≤
            (Cratio * Real.exp (-(bgpParams38.cα * selectorMUWriteStartTime j))) /
              inputs.gap w j := by
              simpa [solMUReplPreForwardResetIntegral] using hbound.2
      _ ≤
            (Cratio * Real.exp (-(bgpParams38.cα * selectorMUWriteStartTime j))) /
              gap0 := hle_gap
      _ =
            (Cratio / gap0) *
              Real.exp (-(bgpParams38.cα * selectorMUWriteStartTime j)) := hrewrite

/-- Discharge a carried prefix `Kreset` residual when `Kreset` is the actual
forward reset integral over `[π/6,π/2]`. -/
theorem solMURepl_preKreset_duhamel_tendsto_zero
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    {cfg : ℕ → ℕ → UConf}
    (inputs : SelectorReplicatorConcInputs sol cfg) (w : ℕ)
    {Kreset : ℕ → ℝ} {gap0 Cratio : ℝ}
    (hgap0 : 0 < gap0)
    (hgap_lb : ∀ᶠ j in atTop, gap0 ≤ inputs.gap w j)
    (hKreset_eq : ∀ j, Kreset j = solMUReplPreForwardResetIntegral inputs w j)
    (hκ₀_nonneg : 0 ≤ (κ₀ : ℝ))
    (hCratio_nonneg : 0 ≤ Cratio)
    (hratio_bound : ∀ j, ∀ t ∈
      Icc (selectorMUWriteStartTime j) (selectorMUWriteHoldTime j),
        (((1 + Real.cos t) / 2) ^ Mcy * (κ₀ : ℝ)) ≤
          (Cratio * Real.exp (-(bgpParams38.cα * selectorMUWriteStartTime j))) *
            (((1 + Real.sin t) / 2) ^ Mcy *
              ((g₀ : ℝ) * Real.exp (bgpParams38.cα * t)))) :
    Tendsto
      (fun j =>
        Kreset j *
          Real.exp
            (-(inputs.gap w j *
              ((sol w).G (selectorMUWriteHoldTime j)
                - (sol w).G (selectorMUWriteStartTime j)))))
      atTop (𝓝 0) := by
  have hstandalone :=
    solMURepl_preForwardResetIntegral_duhamel_tendsto_zero
      (inputs := inputs) (w := w) hgap0 hgap_lb hκ₀_nonneg
      hCratio_nonneg hratio_bound
  refine hstandalone.congr' ?_
  filter_upwards [] with j
  simp [hKreset_eq j]

#print axioms solMUReplForwardResetIntegral
#print axioms solMUReplPreForwardResetIntegral
#print axioms forward_reset_integral_mul_decay_le
#print axioms solMURepl_forwardResetIntegral_duhamel_tendsto_zero
#print axioms solMURepl_preForwardResetIntegral_duhamel_tendsto_zero
#print axioms solMURepl_preKreset_duhamel_tendsto_zero

/-- Discharge the εmixDuhamelResidual using the pre-integral Duhamel decay.
The pre-integral version uses the write-hold endpoint, matching the
εmixDuhamelResidual definition (which also uses writeHold). -/
theorem solMURepl_duhamel_tendsto_zero
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    {cfg : ℕ → ℕ → UConf}
    (inputs : SelectorReplicatorConcInputs sol cfg) (w : ℕ)
    {gap0 Cratio : ℝ}
    (hgap0 : 0 < gap0)
    (hgap_lb : ∀ᶠ j in atTop, gap0 ≤ inputs.gap w j)
    (hKreset_eq : ∀ j, inputs.Kreset w j = solMUReplPreForwardResetIntegral inputs w j)
    (hκ₀_nonneg : 0 ≤ (κ₀ : ℝ))
    (hCratio_nonneg : 0 ≤ Cratio)
    (hratio_bound : ∀ j, ∀ t ∈
      Icc (selectorMUWriteStartTime j) (selectorMUWriteHoldTime j),
        (((1 + Real.cos t) / 2) ^ Mcy * (κ₀ : ℝ)) ≤
          (Cratio * Real.exp (-(bgpParams38.cα * selectorMUWriteStartTime j))) *
            (((1 + Real.sin t) / 2) ^ Mcy *
              ((g₀ : ℝ) * Real.exp (bgpParams38.cα * t)))) :
    Tendsto (fun j => εmixDuhamelResidual inputs w j) atTop (𝓝 0) := by
  have hstandalone :=
    solMURepl_preForwardResetIntegral_duhamel_tendsto_zero
      (inputs := inputs) (w := w) hgap0 hgap_lb hκ₀_nonneg
      hCratio_nonneg hratio_bound
  refine hstandalone.congr' ?_
  filter_upwards [] with j
  simp [εmixDuhamelResidual, hKreset_eq j]

end Ripple.BoundedUniversality.BGP
