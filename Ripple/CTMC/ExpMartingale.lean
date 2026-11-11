/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Ripple.CTMC.CanonicalLaw
import Mathlib.MeasureTheory.Integral.DivergenceTheorem

/-!
# The exponential martingale of a finite continuous-time Markov chain

For a finite Q-matrix `q` and a bounded tilt `g : ℝ → S → S → ℂ` with `g s x x = 0`, the process

`Z_n(t) = exp (Σ_{k<n} [1{T_{k+1} ≤ t} g(T_{k+1}, Y_k, Y_{k+1}) − ∫_{T_k∧t}^{T_{k+1}∧t} c(s, Y_k) ds])`,

`c(s, x) = Σ_{y≠x} q(x,y) (e^{g(s,x,y)} − 1)`, is a martingale in the record index `n` under the
canonical record law (`QMatrix.canonicalRecordMeasure`), so `E Z_n(t) = 1`.  Here `T_k` are the
jump times and `Y_k` the states of the jump-hold records.  (FIX-KURTZ2 §2, Lemmas 2.1–2.2; this
is the discrete-index form of the exponential martingale of Darling–Norris 2008, §4, and of the
characteristic-function martingale behind Kurtz's 1971 central limit theorem.)

The one-step identity `QMatrix.integral_cexp_expStepExponent` is the calculus fact
`∫_0^w φ(h) e^{−∫_0^h φ} dh + e^{−∫_0^w φ} = 1`, applied to the exponential holding time.
The martingale identity `QMatrix.integral_mul_cexp_expSum_succ` (Lemma 2.2) follows from the
Ionescu-Tulcea identity `canonicalRecordMeasure_history_next`; `QMatrix.integral_cexp_expSum`
gives `E Z_n(t) = 1`.  For a real time-constant tilt `φ(y) − φ(x)` (`realTilt`, `realExpSum`),
`QMatrix.martingale_exp_realExpSum` packages `Z_n` as a Mathlib martingale for the canonical
record filtration and `QMatrix.ville_realExpSum` is Ville's maximal inequality
`P(∃ n, Z_n(t) ≥ a) ≤ 1/a` (Lemma 2.3).

The integration limits are clamped (`max u 0`, `max r.1 0`), so every quantity is bounded for every
record sequence; almost surely holding times are nonnegative and the clamps change nothing.
-/

namespace Ripple.CTMC

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Interval

/-! ### A calculus identity -/

/-- Continuity at a point of a finite sum of functions. -/
theorem continuousAt_finset_sum' {ι α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    [AddCommMonoid β] [ContinuousAdd β] (s : Finset ι) {f : ι → α → β} {a : α}
    (h : ∀ i ∈ s, ContinuousAt (f i) a) : ContinuousAt (fun x => ∑ i ∈ s, f i x) a :=
  tendsto_finsetSum s h

/-- Bounded measurable functions are interval integrable. -/
theorem intervalIntegrable_of_bounded_measurable {f : ℝ → ℂ} (hfm : Measurable f) {C : ℝ}
    (hC : ∀ s, ‖f s‖ ≤ C) (a b : ℝ) : IntervalIntegrable f volume a b := by
  refine (intervalIntegrable_const (c := C)).mono_fun' hfm.aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun s => hC s

/-- **FTC for `Ψ(h) = exp(−∫_a^{a+h} f)`.** If `f` is bounded, measurable, and continuous off a
countable set, then `∫_0^w f(a+h) Ψ(h) dh = 1 − Ψ(w)`. -/
theorem integral_mul_cexp_neg_primitive {f : ℝ → ℂ} (hfm : Measurable f) {C : ℝ}
    (hC : ∀ s, ‖f s‖ ≤ C) {D : Set ℝ} (hD : D.Countable)
    (hc : ∀ s, s ∉ D → ContinuousAt f s) (a : ℝ) {w : ℝ} (hw : 0 ≤ w) :
    ∫ h in (0 : ℝ)..w, f (a + h) * Complex.exp (-∫ s in a..(a + h), f s) =
      1 - Complex.exp (-∫ s in a..(a + w), f s) := by
  have hint := intervalIntegrable_of_bounded_measurable hfm hC
  set P : ℝ → ℂ := fun h => ∫ s in a..(a + h), f s with hPdef
  set G : ℝ → ℂ := fun h => -Complex.exp (-P h) with hGdef
  have hPcont : Continuous P := by
    have : Continuous fun u => ∫ s in a..u, f s :=
      intervalIntegral.continuous_primitive (fun x y => hint x y) a
    exact this.comp (continuous_const.add continuous_id)
  have hGcont : Continuous G := (Complex.continuous_exp.comp hPcont.neg).neg
  have hderiv : ∀ h, a + h ∉ D →
      HasDerivAt G (f (a + h) * Complex.exp (-P h)) h := by
    intro h hh
    have hF : HasDerivAt (fun u => ∫ s in a..u, f s) (f (a + h)) (a + h) :=
      intervalIntegral.integral_hasDerivAt_right (hint a (a + h))
        hfm.stronglyMeasurable.stronglyMeasurableAtFilter (hc (a + h) hh)
    have hlin : HasDerivAt (fun h : ℝ => a + h) 1 h := (hasDerivAt_id h).const_add a
    have hP : HasDerivAt P (f (a + h)) h := by
      have := hF.scomp h hlin
      simpa [hPdef, Function.comp_def] using this
    have hE := (hP.neg).cexp
    have hG := hE.neg
    convert hG using 1
    simp only [Pi.neg_apply]
    ring
  have hDc : ((fun s => s - a) '' D).Countable := hD.image _
  have hmeasG' : Measurable fun h => f (a + h) * Complex.exp (-P h) :=
    (hfm.comp (measurable_const.add measurable_id)).mul
      (Complex.continuous_exp.comp hPcont.neg).measurable
  have hboundG' : ∀ h, ‖f (a + h) * Complex.exp (-P h)‖ ≤
      C * Real.exp (‖P h‖) := by
    intro h
    rw [norm_mul]
    have h1 : ‖f (a + h)‖ ≤ C := hC _
    have h2 : ‖Complex.exp (-P h)‖ ≤ Real.exp ‖P h‖ := by
      rw [Complex.norm_exp]
      exact Real.exp_le_exp.mpr ((Complex.re_le_norm _).trans (le_of_eq (norm_neg _)))
    exact mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)
  have hG'int : IntervalIntegrable (fun h => f (a + h) * Complex.exp (-P h)) volume 0 w := by
    have hPb : ∃ K, ∀ h ∈ Set.uIcc (0 : ℝ) w, ‖P h‖ ≤ K := by
      obtain ⟨K, hK⟩ := (isCompact_uIcc (a := (0 : ℝ)) (b := w)).exists_bound_of_continuousOn
        hPcont.continuousOn
      exact ⟨K, hK⟩
    obtain ⟨K, hK⟩ := hPb
    refine (intervalIntegrable_const (c := C * Real.exp K)).mono_fun'
      hmeasG'.aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_uIoc).mpr (Filter.Eventually.of_forall ?_)
    intro h hh
    refine (hboundG' h).trans ?_
    have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (hK h (Set.uIoc_subset_uIcc hh))) hC0
  have hFTC := integral_eq_of_hasDerivAt_off_countable_of_le G
    (fun h => f (a + h) * Complex.exp (-P h)) hw hDc hGcont.continuousOn
    (fun h hh => hderiv h (by
      intro hmem
      exact hh.2 ⟨a + h, hmem, by ring⟩))
    hG'int
  rw [hFTC]
  simp only [hGdef, hPdef, add_zero, intervalIntegral.integral_same, neg_zero,
    Complex.exp_zero]
  ring

/-! ### The tilt and its compensator -/

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Hypotheses on a tilt `g(s, x, y)`: vanishing on the diagonal, measurable and bounded in time,
continuous in time off a countable set `D`. -/
structure IsExpTilt (g : ℝ → S → S → ℂ) (D : Set ℝ) : Prop where
  diag : ∀ s x, g s x x = 0
  meas : ∀ x y, Measurable fun s => g s x y
  bdd : ∃ C, ∀ s x y, ‖g s x y‖ ≤ C
  countable : D.Countable
  cont : ∀ x y s, s ∉ D → ContinuousAt (fun s => g s x y) s

namespace QMatrix

/-- The compensator rate `c(s, x) = Σ_{y≠x} q(x,y) (e^{g(s,x,y)} − 1)`. -/
noncomputable def expCompRate (Q : QMatrix S) (g : ℝ → S → S → ℂ) (s : ℝ) (x : S) : ℂ :=
  ∑ y ∈ Finset.univ.filter (· ≠ x), (Q.rate x y : ℂ) * (Complex.exp (g s x y) - 1)

/-- The exponent of one jump-hold step from time `u` and state `x` with record `r = (h, y)`,
observed at the horizon `t`: the tilt of the jump if it happens by time `t`, minus the compensator
over `[u ∧ t, (u + h) ∧ t]` (with `u, h` clamped at `0`). -/
noncomputable def expStepExponent (Q : QMatrix S) (g : ℝ → S → S → ℂ) (t u : ℝ) (x : S)
    (r : ℝ × S) : ℂ :=
  (if max u 0 + r.1 ≤ t then g (max u 0 + r.1) x r.2 else 0) -
    ∫ s in (min (max u 0) t)..(min (max u 0 + max r.1 0) t), Q.expCompRate g s x

/-- A uniform bound for the compensator rate. -/
noncomputable def expCompBound (Q : QMatrix S) (C : ℝ) : ℝ :=
  ∑ x, ∑ y ∈ Finset.univ.filter (· ≠ x), |Q.rate x y| * (Real.exp C + 1)

theorem norm_cexp_sub_one_le {z : ℂ} {C : ℝ} (hz : ‖z‖ ≤ C) :
    ‖Complex.exp z - 1‖ ≤ Real.exp C + 1 := by
  calc ‖Complex.exp z - 1‖ ≤ ‖Complex.exp z‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = Real.exp z.re + 1 := by rw [Complex.norm_exp, norm_one]
    _ ≤ Real.exp C + 1 := by
        gcongr
        exact (Complex.re_le_norm z).trans hz

theorem norm_expCompRate_le (Q : QMatrix S) {g : ℝ → S → S → ℂ} {C : ℝ}
    (hC : ∀ s x y, ‖g s x y‖ ≤ C) (s : ℝ) (x : S) :
    ‖Q.expCompRate g s x‖ ≤ Q.expCompBound C := by
  unfold expCompRate expCompBound
  calc ‖∑ y ∈ Finset.univ.filter (· ≠ x), (Q.rate x y : ℂ) * (Complex.exp (g s x y) - 1)‖
      ≤ ∑ y ∈ Finset.univ.filter (· ≠ x), ‖(Q.rate x y : ℂ) * (Complex.exp (g s x y) - 1)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ y ∈ Finset.univ.filter (· ≠ x), |Q.rate x y| * (Real.exp C + 1) := by
        refine Finset.sum_le_sum fun y _ => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        gcongr
        exact norm_cexp_sub_one_le (hC s x y)
    _ ≤ ∑ x', ∑ y ∈ Finset.univ.filter (· ≠ x'), |Q.rate x' y| * (Real.exp C + 1) :=
        Finset.single_le_sum (f := fun x' => ∑ y ∈ Finset.univ.filter (· ≠ x'),
          |Q.rate x' y| * (Real.exp C + 1))
          (fun x' _ => Finset.sum_nonneg fun y _ => by positivity) (Finset.mem_univ x)

theorem expCompBound_nonneg (Q : QMatrix S) (C : ℝ) : 0 ≤ Q.expCompBound C :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity

theorem measurable_expCompRate (Q : QMatrix S) {g : ℝ → S → S → ℂ}
    (hg : ∀ x y, Measurable fun s => g s x y) (x : S) :
    Measurable fun s => Q.expCompRate g s x := by
  unfold expCompRate
  refine Finset.measurable_sum _ fun y _ => ?_
  exact measurable_const.mul ((Complex.measurable_exp.comp (hg x y)).sub measurable_const)

theorem continuousAt_expCompRate (Q : QMatrix S) {g : ℝ → S → S → ℂ} {D : Set ℝ}
    (hg : ∀ x y s, s ∉ D → ContinuousAt (fun s => g s x y) s) (x : S) {s : ℝ} (hs : s ∉ D) :
    ContinuousAt (fun s => Q.expCompRate g s x) s := by
  unfold expCompRate
  refine continuousAt_finset_sum' _ fun y _ => ?_
  exact continuousAt_const.mul
    ((Complex.continuous_exp.continuousAt.comp (hg x y s hs)).sub continuousAt_const)

/-- The integral term of a step exponent is bounded by `expCompBound · |t|`. -/
theorem norm_integral_expCompRate_le (Q : QMatrix S) {g : ℝ → S → S → ℂ} {C : ℝ}
    (hC : ∀ s x y, ‖g s x y‖ ≤ C) (t v h : ℝ) (hv : 0 ≤ v) (hh : 0 ≤ h) (x : S) :
    ‖∫ s in (min v t)..(min (v + h) t), Q.expCompRate g s x‖ ≤ Q.expCompBound C * |t| := by
  refine (intervalIntegral.norm_integral_le_of_norm_le_const
    (fun s _ => Q.norm_expCompRate_le hC s x)).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (Q.expCompBound_nonneg C)
  rw [abs_le]
  constructor
  · rcases le_total v t with hvt | hvt
    · rw [min_eq_left hvt]
      have : v ≤ min (v + h) t := le_min (by linarith) hvt
      have : -|t| ≤ 0 := neg_nonpos.mpr (abs_nonneg t)
      linarith
    · rw [min_eq_right hvt, min_eq_right (by linarith)]
      simp
  · rcases le_total v t with hvt | hvt
    · rw [min_eq_left hvt]
      have : min (v + h) t ≤ t := min_le_right _ _
      have : t ≤ |t| := le_abs_self t
      linarith
    · rw [min_eq_right hvt, min_eq_right (by linarith)]
      simp

/-- The norm of `exp` of a step exponent is bounded uniformly. -/
theorem norm_cexp_expStepExponent_le (Q : QMatrix S) {g : ℝ → S → S → ℂ} {C : ℝ}
    (hC : ∀ s x y, ‖g s x y‖ ≤ C) (t u : ℝ) (x : S) (r : ℝ × S) :
    ‖Complex.exp (Q.expStepExponent g t u x r)‖ ≤ Real.exp (C + Q.expCompBound C * |t|) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  refine (Complex.re_le_norm _).trans ?_
  unfold expStepExponent
  refine (norm_sub_le _ _).trans ?_
  gcongr
  · split_ifs
    · exact hC _ _ _
    · simpa using (norm_nonneg (g 0 x x)).trans (hC 0 x x)
  · exact Q.norm_integral_expCompRate_le hC t (max u 0) (max r.1 0) (le_max_right _ _)
      (le_max_right _ _) x

/-! ### The one-step identity -/

section OneStep

variable [Countable S] [MeasurableSpace S] [MeasurableSingletonClass S]

/-- Complex expectation against the embedded jump-chain row is the finite PMF sum. -/
theorem integral_embeddedStepMeasure_eq_sum_complex (Q : QMatrix S) {x : S}
    (h : ¬Q.IsAbsorbing x) (f : S → ℂ) :
    ∫ y, f y ∂Q.embeddedStepMeasure x = ∑ y, ((Q.jumpProb x y).toReal : ℂ) * f y := by
  rw [QMatrix.embeddedStepMeasure, PMF.integral_eq_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Q.embeddedDTMC_step_of_nonabsorbing h y, Complex.real_smul]

/-- Integrals over `Ioc 0 w` against the exponential law, by its density. -/
theorem setIntegral_expMeasure_Ioc {r : ℝ} (hr : 0 < r) {w : ℝ} (hw : 0 ≤ w) (f : ℝ → ℂ) :
    ∫ h in Set.Ioc 0 w, f h ∂expMeasure r =
      ∫ h in (0 : ℝ)..w, ((r * Real.exp (-(r * h)) : ℝ) : ℂ) * f h := by
  rw [intervalIntegral.integral_of_le hw, expMeasure, gammaMeasure,
    setIntegral_withDensity_eq_setIntegral_toReal_smul
      (show Measurable (gammaPDF 1 r) from (measurable_gammaPDFReal 1 r).ennreal_ofReal)
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) f measurableSet_Ioc]
  refine setIntegral_congr_fun measurableSet_Ioc fun h hh => ?_
  have h0 : 0 ≤ h := hh.1.le
  simp only [gammaPDF_of_nonneg h0, Real.rpow_one, Real.Gamma_one, div_one, sub_self,
    Real.rpow_zero, mul_one, Complex.real_smul]
  rw [ENNReal.toReal_ofReal (by positivity)]

/-- **One-step identity (FIX-KURTZ2 Lemma 2.1).** The expected `exp` of a step exponent under the
jump-hold kernel at `x` is `1`. -/
theorem integral_cexp_expStepExponent (Q : QMatrix S) {g : ℝ → S → S → ℂ} {D : Set ℝ}
    (hg : IsExpTilt g D) (t u : ℝ) (x : S) :
    ∫ r, Complex.exp (Q.expStepExponent g t u x r) ∂(Q.jumpHoldStepKernel x) = 1 := by
  obtain ⟨C, hC⟩ := hg.bdd
  set v := max u 0 with hv
  have hv0 : 0 ≤ v := le_max_right _ _
  by_cases habs : Q.IsAbsorbing x
  · rw [Q.jumpHoldStepKernel_apply, Q.jumpHoldStepMeasureTotal_of_absorbing habs,
      integral_dirac]
    simp [expStepExponent, hg.diag, ← hv]
  rw [Q.jumpHoldStepKernel_apply, Q.jumpHoldStepMeasureTotal_of_nonabsorbing habs]
  have hlam : 0 < Q.exitRate x := Q.exitRate_pos_of_nonabsorbing habs
  set lam := Q.exitRate x with hlamdef
  haveI := Q.isProbabilityMeasure_holdingTimeMeasure habs
  haveI := Q.isProbabilityMeasure_embeddedStepMeasure x
  -- integrability of the integrand on the product law
  have hmeas_step : Measurable fun r : ℝ × S => Complex.exp (Q.expStepExponent g t u x r) := by
    refine Complex.measurable_exp.comp ?_
    unfold expStepExponent
    refine Measurable.sub ?_ ?_
    · refine measurable_from_prod_countable_left fun y => ?_
      refine Measurable.ite (measurableSet_le (measurable_const.add measurable_id)
        measurable_const) ?_ measurable_const
      exact (hg.meas x y).comp (measurable_const.add measurable_id)
    · have hcont : Continuous fun h : ℝ =>
          ∫ s in (min v t)..(min (v + max h 0) t), Q.expCompRate g s x := by
        have hprim : Continuous fun b => ∫ s in (min v t)..b, Q.expCompRate g s x :=
          intervalIntegral.continuous_primitive (fun a b =>
            intervalIntegrable_of_bounded_measurable (Q.measurable_expCompRate hg.meas x)
              (fun s => Q.norm_expCompRate_le hC s x) a b) _
        exact hprim.comp ((continuous_const.add (continuous_id.max continuous_const)).min
          continuous_const)
      exact hcont.measurable.comp measurable_fst
  have hbound := Q.norm_cexp_expStepExponent_le hC t u x
  haveI : IsProbabilityMeasure (Q.jumpHoldStepMeasure habs) :=
    Q.isProbabilityMeasure_jumpHoldStepMeasure habs
  have hint : Integrable (fun r : ℝ × S => Complex.exp (Q.expStepExponent g t u x r))
      (Q.jumpHoldStepMeasure habs) :=
    (integrable_const (Real.exp (C + Q.expCompBound C * |t|))).mono'
      hmeas_step.aestronglyMeasurable (Filter.Eventually.of_forall hbound)
  rw [QMatrix.jumpHoldStepMeasure, integral_prod _ hint]
  -- inner integral over the next state
  set φ : ℝ → ℂ := fun s => ∑ y ∈ Finset.univ.filter (· ≠ x),
    (Q.rate x y : ℂ) * Complex.exp (g s x y) with hφdef
  have hφ_eq : ∀ s, φ s = Q.expCompRate g s x + lam := by
    intro s
    simp only [hφdef, expCompRate, hlamdef, QMatrix.exitRate, Complex.ofReal_sum]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    ring
  by_cases hut : t ≤ v
  · -- the horizon has passed: the exponent vanishes for positive holding times
    have hzero : ∀ᵐ h ∂Q.holdingTimeMeasure habs,
        ∫ y, Complex.exp (Q.expStepExponent g t u x (h, y)) ∂Q.embeddedStepMeasure x = 1 := by
      filter_upwards [Q.holdingTimeMeasure_pos_ae habs] with h hh
      have : ∀ y, Q.expStepExponent g t u x (h, y) = 0 := by
        intro y
        simp only [expStepExponent, ← hv]
        rw [if_neg (by linarith), min_eq_right hut, min_eq_right (by
          have := le_max_right h 0; linarith)]
        simp
      simp [this]
    rw [integral_congr_ae hzero]
    simp
  push_neg at hut
  set w := t - v with hwdef
  have hw : 0 < w := by linarith
  -- the inner integral, pointwise for positive holding times
  set I : ℝ → ℂ := fun h => ∫ s in v..(v + h), Q.expCompRate g s x with hIdef
  have hinner_le : ∀ h, 0 < h → h ≤ w →
      ∫ y, Complex.exp (Q.expStepExponent g t u x (h, y)) ∂Q.embeddedStepMeasure x =
        ((lam : ℂ))⁻¹ * (φ (v + h) * Complex.exp (-I h)) := by
    intro h hh hhw
    rw [Q.integral_embeddedStepMeasure_eq_sum_complex habs]
    have hstep : ∀ y, Q.expStepExponent g t u x (h, y) = g (v + h) x y - I h := by
      intro y
      simp only [expStepExponent, ← hv, hIdef]
      rw [if_pos (by linarith), min_eq_left hut.le, max_eq_left hh.le,
        min_eq_left (by linarith)]
    simp only [hstep, hφdef, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun y _ => ?_
    by_cases hyx : y ≠ x
    · rw [if_pos hyx, QMatrix.jumpProb, if_neg (Ne.symm hyx),
        ENNReal.toReal_ofReal (div_nonneg (Q.rate_nonneg x y (Ne.symm hyx)) hlam.le),
        Complex.exp_sub]
      push_cast
      field_simp
      rw [mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, mul_one]
    · push_neg at hyx
      subst hyx
      simp [QMatrix.jumpProb]
  have hinner_gt : ∀ h, w < h →
      ∫ y, Complex.exp (Q.expStepExponent g t u x (h, y)) ∂Q.embeddedStepMeasure x =
        Complex.exp (-I w) := by
    intro h hh
    have hstep : ∀ y, Q.expStepExponent g t u x (h, y) = -I w := by
      intro y
      simp only [expStepExponent, ← hv, hIdef, hwdef]
      rw [if_neg (by linarith), min_eq_left hut.le, max_eq_left (by linarith),
        min_eq_right (by linarith)]
      simp
    simp [hstep]
  -- split the outer integral
  set F : ℝ → ℂ := fun h =>
    ∫ y, Complex.exp (Q.expStepExponent g t u x (h, y)) ∂Q.embeddedStepMeasure x with hFdef
  have hFint : Integrable F (Q.holdingTimeMeasure habs) := hint.integral_prod_left
  have hIoi : ∫ h, F h ∂Q.holdingTimeMeasure habs =
      ∫ h in Set.Ioi 0, F h ∂Q.holdingTimeMeasure habs := by
    rw [setIntegral_eq_integral_of_ae_compl_eq_zero]
    have hzero := Q.holdingTimeMeasure_Iic_zero habs
    rw [ae_iff] at *
    refine measure_mono_null (fun h hh => ?_) hzero
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_Ioi, not_lt] at hh
    exact (Classical.not_imp.mp hh).1
  rw [hIoi, ← Set.Ioc_union_Ioi_eq_Ioi hw.le,
    setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hFint.integrableOn
      hFint.integrableOn]
  -- the tail part
  have htail : ∫ h in Set.Ioi w, F h ∂Q.holdingTimeMeasure habs =
      (Real.exp (-(lam * w)) : ℂ) * Complex.exp (-I w) := by
    rw [setIntegral_congr_fun measurableSet_Ioi (fun h hh => hinner_gt h hh), setIntegral_const,
      Complex.real_smul]
    congr 1
    rw [Q.holdingTimeMeasure_real_Ioi_eq habs hw.le]
  -- the body part
  have hbody : ∫ h in Set.Ioc 0 w, F h ∂Q.holdingTimeMeasure habs =
      ∫ h in (0 : ℝ)..w, φ (v + h) * Complex.exp (-∫ s in v..(v + h), φ s) := by
    rw [setIntegral_congr_fun measurableSet_Ioc (fun h hh => hinner_le h hh.1 hh.2)]
    rw [QMatrix.holdingTimeMeasure, setIntegral_expMeasure_Ioc hlam hw.le]
    refine intervalIntegral.integral_congr fun h hh => ?_
    have hφint : ∫ s in v..(v + h), φ s = I h + lam * h := by
      simp only [hφ_eq, hIdef]
      rw [intervalIntegral.integral_add, intervalIntegral.integral_const]
      · simp
        ring
      · exact intervalIntegrable_of_bounded_measurable (Q.measurable_expCompRate hg.meas x)
          (fun s => Q.norm_expCompRate_le hC s x) _ _
      · exact intervalIntegrable_const
    rw [hφint, neg_add, Complex.exp_add]
    push_cast
    have hlam' : (lam : ℂ) ≠ 0 := by exact_mod_cast hlam.ne'
    field_simp
  -- the calculus identity
  have hφmeas : Measurable φ := by
    refine Finset.measurable_sum _ fun y _ => ?_
    exact measurable_const.mul (Complex.measurable_exp.comp (hg.meas x y))
  have hφbound : ∀ s, ‖φ s‖ ≤ Q.expCompBound C + |lam| := by
    intro s
    rw [hφ_eq]
    refine (norm_add_le _ _).trans ?_
    gcongr
    · exact Q.norm_expCompRate_le hC s x
    · rw [Complex.norm_real, Real.norm_eq_abs]
  have hφcont : ∀ s, s ∉ D → ContinuousAt φ s := by
    intro s hs
    refine continuousAt_finset_sum' _ fun y _ => ?_
    exact continuousAt_const.mul (Complex.continuous_exp.continuousAt.comp (hg.cont x y s hs))
  have hcalc := integral_mul_cexp_neg_primitive hφmeas hφbound hg.countable hφcont v hw.le
  have hφw : ∫ s in v..(v + w), φ s = I w + lam * w := by
    simp only [hφ_eq, hIdef]
    rw [intervalIntegral.integral_add, intervalIntegral.integral_const]
    · simp
      ring
    · exact intervalIntegrable_of_bounded_measurable (Q.measurable_expCompRate hg.meas x)
        (fun s => Q.norm_expCompRate_le hC s x) _ _
    · exact intervalIntegrable_const
  rw [hbody, htail, hcalc, hφw, neg_add, Complex.exp_add]
  push_cast
  rw [show (-(lam * w : ℂ)) = -((lam : ℂ) * w) by ring]
  ring_nf

end OneStep

/-! ### The exponential functional along a record trajectory -/

/-- The `k`-th jump time `T_k = H_1 + ⋯ + H_k` of a record trajectory (`T_0 = 0`). -/
noncomputable def recTime (ω : (n : ℕ) → JumpHoldTrajectorySpace S n) (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range k, (ω (j + 1)).1

/-- `log Z_n(t)`: the sum of the first `n` step exponents along the record trajectory `ω`. -/
noncomputable def expSum (Q : QMatrix S) (g : ℝ → S → S → ℂ) (t : ℝ) (n : ℕ)
    (ω : (n : ℕ) → JumpHoldTrajectorySpace S n) : ℂ :=
  ∑ k ∈ Finset.range n, Q.expStepExponent g t (recTime ω k) (ω k).2 (ω (k + 1))

/-- The time-constant real tilt `g(s, x, y) = φ(y) − φ(x)` of an observable `φ`. -/
noncomputable def realTilt (φ : S → ℝ) : ℝ → S → S → ℂ :=
  fun _ x y => ((φ y - φ x : ℝ) : ℂ)

/-- The real compensator rate of an observable: `Σ_{y≠x} q(x,y) (e^{φ(y)−φ(x)} − 1)`. -/
noncomputable def expCompRateReal (Q : QMatrix S) (φ : S → ℝ) (x : S) : ℝ :=
  ∑ y ∈ Finset.univ.filter (· ≠ x), Q.rate x y * (Real.exp (φ y - φ x) - 1)

theorem expCompRate_realTilt (Q : QMatrix S) (φ : S → ℝ) (s : ℝ) (x : S) :
    Q.expCompRate (realTilt φ) s x = (Q.expCompRateReal φ x : ℂ) := by
  simp only [expCompRate, expCompRateReal, realTilt, Complex.ofReal_sum, Complex.ofReal_mul,
    Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_exp]


/-! ### The real, time-constant specialisation -/

/-- The real step exponent of the time-constant tilt `φ(y) − φ(x)`: the tilt of the jump if it
happens by time `t`, minus the length of the clamped sojourn window times the real compensator
rate. -/
noncomputable def realStepExponent (Q : QMatrix S) (φ : S → ℝ) (t u : ℝ) (x : S) (r : ℝ × S) :
    ℝ :=
  (if max u 0 + r.1 ≤ t then φ r.2 - φ x else 0) -
    (min (max u 0 + max r.1 0) t - min (max u 0) t) * Q.expCompRateReal φ x

/-- `log Z_n(t)` for the real time-constant tilt of an observable `φ`. -/
noncomputable def realExpSum (Q : QMatrix S) (φ : S → ℝ) (t : ℝ) (n : ℕ)
    (ω : (n : ℕ) → JumpHoldTrajectorySpace S n) : ℝ :=
  ∑ k ∈ Finset.range n, Q.realStepExponent φ t (recTime ω k) (ω k).2 (ω (k + 1))

theorem expStepExponent_realTilt (Q : QMatrix S) (φ : S → ℝ) (t u : ℝ) (x : S) (r : ℝ × S) :
    Q.expStepExponent (realTilt φ) t u x r = ((Q.realStepExponent φ t u x r : ℝ) : ℂ) := by
  unfold expStepExponent realStepExponent
  simp_rw [expCompRate_realTilt]
  rw [intervalIntegral.integral_const, Complex.real_smul]
  split_ifs <;> simp [realTilt]

theorem expSum_realTilt (Q : QMatrix S) (φ : S → ℝ) (t : ℝ) (n : ℕ)
    (ω : (n : ℕ) → JumpHoldTrajectorySpace S n) :
    Q.expSum (realTilt φ) t n ω = ((Q.realExpSum φ t n ω : ℝ) : ℂ) := by
  unfold expSum realExpSum
  rw [Complex.ofReal_sum]
  exact Finset.sum_congr rfl fun k _ => Q.expStepExponent_realTilt φ t _ _ _

theorem realExpSum_succ (Q : QMatrix S) (φ : S → ℝ) (t : ℝ) (n : ℕ)
    (ω : (n : ℕ) → JumpHoldTrajectorySpace S n) :
    Q.realExpSum φ t (n + 1) ω =
      Q.realExpSum φ t n ω + Q.realStepExponent φ t (recTime ω n) (ω n).2 (ω (n + 1)) := by
  unfold realExpSum
  rw [Finset.sum_range_succ]

theorem expSum_succ (Q : QMatrix S) (g : ℝ → S → S → ℂ) (t : ℝ) (n : ℕ)
    (ω : (n : ℕ) → JumpHoldTrajectorySpace S n) :
    Q.expSum g t (n + 1) ω =
      Q.expSum g t n ω + Q.expStepExponent g t (recTime ω n) (ω n).2 (ω (n + 1)) := by
  unfold expSum
  rw [Finset.sum_range_succ]

omit [DecidableEq S] in
/-- A time-constant real tilt satisfies the tilt hypotheses with no exceptional set. -/
theorem isExpTilt_realTilt (φ : S → ℝ) : IsExpTilt (realTilt φ) ∅ where
  diag := fun _ x => by simp only [realTilt, sub_self, Complex.ofReal_zero]
  meas := fun _ _ => measurable_const
  bdd := by
    have hC : ∀ x, |φ x| ≤ ∑ y, |φ y| := fun x =>
      Finset.single_le_sum (f := fun y => |φ y|) (fun _ _ => abs_nonneg _) (Finset.mem_univ x)
    refine ⟨2 * ∑ y, |φ y|, fun _ x y => ?_⟩
    simp only [realTilt, Complex.norm_real, Real.norm_eq_abs]
    calc |φ y - φ x| ≤ |φ y| + |φ x| := abs_sub _ _
      _ ≤ (∑ y, |φ y|) + ∑ y, |φ y| := add_le_add (hC y) (hC x)
      _ = 2 * ∑ y, |φ y| := by ring
  countable := Set.countable_empty
  cont := fun _ _ _ _ => continuousAt_const

/-- At an absorbing state every outgoing rate vanishes, so the real compensator rate is zero. -/
theorem expCompRateReal_eq_zero_of_absorbing (Q : QMatrix S) (φ : S → ℝ) {x : S}
    (hx : Q.IsAbsorbing x) : Q.expCompRateReal φ x = 0 := by
  unfold expCompRateReal
  refine Finset.sum_eq_zero fun y hy => ?_
  rw [QMatrix.IsAbsorbing.rate_eq_zero Q hx y (Finset.mem_filter.mp hy).2.symm, zero_mul]

/-! ### Bounds on the exponential sums -/

theorem re_expStepExponent_le (Q : QMatrix S) {g : ℝ → S → S → ℂ} {C : ℝ}
    (hC : ∀ s x y, ‖g s x y‖ ≤ C) (t u : ℝ) (x : S) (r : ℝ × S) :
    (Q.expStepExponent g t u x r).re ≤ C + Q.expCompBound C * |t| := by
  refine (Complex.re_le_norm _).trans ?_
  unfold expStepExponent
  refine (norm_sub_le _ _).trans ?_
  gcongr
  · split_ifs
    · exact hC _ _ _
    · simpa using (norm_nonneg (g 0 x x)).trans (hC 0 x x)
  · exact Q.norm_integral_expCompRate_le hC t (max u 0) (max r.1 0) (le_max_right _ _)
      (le_max_right _ _) x

theorem re_expSum_le (Q : QMatrix S) {g : ℝ → S → S → ℂ} {C : ℝ}
    (hC : ∀ s x y, ‖g s x y‖ ≤ C) (t : ℝ) (n : ℕ)
    (ω : (n : ℕ) → JumpHoldTrajectorySpace S n) :
    (Q.expSum g t n ω).re ≤ n * (C + Q.expCompBound C * |t|) := by
  unfold expSum
  rw [Complex.re_sum]
  calc ∑ k ∈ Finset.range n, (Q.expStepExponent g t (recTime ω k) (ω k).2 (ω (k + 1))).re
      ≤ ∑ _k ∈ Finset.range n, (C + Q.expCompBound C * |t|) :=
        Finset.sum_le_sum fun k _ => Q.re_expStepExponent_le hC t _ _ _
    _ = n * (C + Q.expCompBound C * |t|) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

theorem norm_cexp_expSum_le (Q : QMatrix S) {g : ℝ → S → S → ℂ} {C : ℝ}
    (hC : ∀ s x y, ‖g s x y‖ ≤ C) (t : ℝ) (n : ℕ)
    (ω : (n : ℕ) → JumpHoldTrajectorySpace S n) :
    ‖Complex.exp (Q.expSum g t n ω)‖ ≤ Real.exp (n * (C + Q.expCompBound C * |t|)) := by
  rw [Complex.norm_exp]
  exact Real.exp_le_exp.mpr (Q.re_expSum_le hC t n ω)

/-! ### Measurability

The step exponent is a Borel function of `(u, r)` for each state `x` (the jump term is measurable
in `(u, h)` for each next state `y` and the next state ranges over the countable `S`; the
compensator term is continuous in `(u, h)`).  Composed with the record coordinates, which are
measurable for the canonical record filtration at the index they are read from, `expSum g t n` is
measurable for `canonicalRecordFiltration n`. -/

section Measurability

variable [Countable S] [MeasurableSpace S] [MeasurableSingletonClass S]

omit [Countable S] [MeasurableSpace S] [MeasurableSingletonClass S] in
theorem continuous_intervalIntegral_expCompRate (Q : QMatrix S) {g : ℝ → S → S → ℂ} {C : ℝ}
    (hgm : ∀ x y, Measurable fun s => g s x y) (hC : ∀ s x y, ‖g s x y‖ ≤ C) (x : S) :
    Continuous fun p : ℝ × ℝ => ∫ s in p.1..p.2, Q.expCompRate g s x := by
  have hint : ∀ a b, IntervalIntegrable (fun s => Q.expCompRate g s x) volume a b := fun a b =>
    intervalIntegrable_of_bounded_measurable (Q.measurable_expCompRate hgm x)
      (fun s => Q.norm_expCompRate_le hC s x) a b
  have hP : Continuous fun b => ∫ s in (0 : ℝ)..b, Q.expCompRate g s x :=
    intervalIntegral.continuous_primitive hint 0
  have heq : ∀ a b : ℝ, ∫ s in a..b, Q.expCompRate g s x =
      (∫ s in (0 : ℝ)..b, Q.expCompRate g s x) - ∫ s in (0 : ℝ)..a, Q.expCompRate g s x :=
    fun a b => (intervalIntegral.integral_interval_sub_left (hint 0 b) (hint 0 a)).symm
  have h2 : Continuous fun p : ℝ × ℝ =>
      (∫ s in (0 : ℝ)..p.2, Q.expCompRate g s x) - ∫ s in (0 : ℝ)..p.1, Q.expCompRate g s x :=
    (hP.comp continuous_snd).sub (hP.comp continuous_fst)
  exact h2.congr fun p => (heq p.1 p.2).symm

/-- Joint measurability of the step exponent in the start time and the next record. -/
theorem measurable_expStepExponent (Q : QMatrix S) {g : ℝ → S → S → ℂ} {D : Set ℝ}
    (hg : IsExpTilt g D) (t : ℝ) (x : S) :
    Measurable fun q : ℝ × (ℝ × S) => Q.expStepExponent g t q.1 x q.2 := by
  obtain ⟨C, hC⟩ := hg.bdd
  have h1 : Measurable fun q : (ℝ × ℝ) × S =>
      (if max q.1.1 0 + q.1.2 ≤ t then g (max q.1.1 0 + q.1.2) x q.2 else 0 : ℂ) := by
    refine measurable_from_prod_countable_left fun y => ?_
    refine Measurable.ite (measurableSet_le
      ((measurable_fst.max measurable_const).add measurable_snd) measurable_const) ?_
      measurable_const
    exact (hg.meas x y).comp ((measurable_fst.max measurable_const).add measurable_snd)
  have h2 : Continuous fun q : ℝ × ℝ =>
      ∫ s in (min (max q.1 0) t)..(min (max q.1 0 + max q.2 0) t), Q.expCompRate g s x := by
    have hg' : Continuous fun q : ℝ × ℝ =>
        (min (max q.1 0) t, min (max q.1 0 + max q.2 0) t) :=
      ((continuous_fst.max continuous_const).min continuous_const).prodMk
        (((continuous_fst.max continuous_const).add (continuous_snd.max continuous_const)).min
          continuous_const)
    exact (Q.continuous_intervalIntegral_expCompRate hg.meas hC x).comp hg'
  have h3 : Measurable fun q : (ℝ × ℝ) × S => Q.expStepExponent g t q.1.1 x (q.1.2, q.2) := by
    unfold expStepExponent
    exact h1.sub (h2.measurable.comp measurable_fst)
  have h4 := h3.comp (MeasurableEquiv.prodAssoc (α := ℝ) (β := ℝ) (γ := S)).symm.measurable
  exact h4

/-- `expSum g t n` is measurable for the canonical record filtration at index `n`. -/
theorem measurable_expSum_canonicalRecordFiltration (Q : QMatrix S) {g : ℝ → S → S → ℂ}
    {D : Set ℝ} (hg : IsExpTilt g D) (t : ℝ) (n : ℕ) :
    Measurable[QMatrix.canonicalRecordFiltration (S := S) n] (Q.expSum g t n) := by
  unfold expSum
  refine Finset.measurable_sum _ fun k hk => ?_
  have hk' : k + 1 ≤ n := Finset.mem_range.mp hk
  have hrec : Measurable[QMatrix.canonicalRecordFiltration (S := S) n]
      fun ω : (m : ℕ) → JumpHoldTrajectorySpace S m => recTime ω k := by
    unfold recTime
    refine Finset.measurable_sum _ fun j hj => ?_
    have hj' : j + 1 ≤ n := by have := Finset.mem_range.mp hj; omega
    exact (QMatrix.measurable_record_canonicalRecordFiltration_le (S := S) hj').fst
  have hnext : Measurable[QMatrix.canonicalRecordFiltration (S := S) n]
      fun ω : (m : ℕ) → JumpHoldTrajectorySpace S m => ω (k + 1) :=
    QMatrix.measurable_record_canonicalRecordFiltration_le (S := S) hk'
  have hcur : Measurable[QMatrix.canonicalRecordFiltration (S := S) n]
      fun ω : (m : ℕ) → JumpHoldTrajectorySpace S m => (ω k).2 :=
    (QMatrix.measurable_record_canonicalRecordFiltration_le (S := S) (by omega)).snd
  have hF : Measurable fun p : (ℝ × (ℝ × S)) × S => Q.expStepExponent g t p.1.1 p.2 p.1.2 :=
    measurable_from_prod_countable_left fun x => Q.measurable_expStepExponent hg t x
  exact hF.comp ((hrec.prodMk hnext).prodMk hcur)

theorem measurable_expSum (Q : QMatrix S) {g : ℝ → S → S → ℂ} {D : Set ℝ}
    (hg : IsExpTilt g D) (t : ℝ) (n : ℕ) : Measurable (Q.expSum g t n) :=
  (Q.measurable_expSum_canonicalRecordFiltration hg t n).mono
    ((QMatrix.canonicalRecordFiltration (S := S)).le n) le_rfl

theorem measurable_realExpSum_canonicalRecordFiltration (Q : QMatrix S) (φ : S → ℝ) (t : ℝ)
    (n : ℕ) :
    Measurable[QMatrix.canonicalRecordFiltration (S := S) n] (Q.realExpSum φ t n) := by
  have h := Q.measurable_expSum_canonicalRecordFiltration (isExpTilt_realTilt φ) t n
  have heq : Q.realExpSum φ t n = fun ω => (Q.expSum (realTilt φ) t n ω).re := by
    funext ω
    rw [Q.expSum_realTilt, Complex.ofReal_re]
  rw [heq]
  exact Complex.measurable_re.comp h

end Measurability

/-! ### The record-index martingale identity (FIX-KURTZ2 Lemma 2.2) -/

section Martingale

variable [Countable S] [MeasurableSpace S] [MeasurableSingletonClass S]

/-- The jump time `T_k` read from a finite record history through index `n` (for `k ≤ n`). -/
noncomputable def histRecTime (n : ℕ) (hist : (i : Finset.Iic n) → JumpHoldTrajectorySpace S i)
    (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range k, if h : j + 1 ≤ n then (hist ⟨j + 1, Finset.mem_Iic.mpr h⟩).1 else 0

/-- `log Z_n(t)` read from a finite record history through index `n`. -/
noncomputable def histExpSum (Q : QMatrix S) (g : ℝ → S → S → ℂ) (t : ℝ) (n : ℕ)
    (hist : (i : Finset.Iic n) → JumpHoldTrajectorySpace S i) : ℂ :=
  ∑ k ∈ Finset.range n, if h : k + 1 ≤ n then
    Q.expStepExponent g t (histRecTime n hist k) (hist ⟨k, Finset.mem_Iic.mpr (by omega)⟩).2
      (hist ⟨k + 1, Finset.mem_Iic.mpr h⟩)
  else 0

omit [Fintype S] [DecidableEq S] [Countable S] [MeasurableSpace S] [MeasurableSingletonClass S] in
theorem histRecTime_frestrictLe (n : ℕ) (ω : (m : ℕ) → JumpHoldTrajectorySpace S m) {k : ℕ}
    (hk : k ≤ n) : histRecTime n (Preorder.frestrictLe n ω) k = recTime ω k := by
  unfold histRecTime recTime
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j + 1 ≤ n := by have := Finset.mem_range.mp hj; omega
  rw [dif_pos hj']
  rfl

theorem histExpSum_frestrictLe (Q : QMatrix S) (g : ℝ → S → S → ℂ) (t : ℝ) (n : ℕ)
    (ω : (m : ℕ) → JumpHoldTrajectorySpace S m) :
    Q.histExpSum g t n (Preorder.frestrictLe n ω) = Q.expSum g t n ω := by
  unfold histExpSum expSum
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k + 1 ≤ n := Finset.mem_range.mp hk
  rw [dif_pos hk', histRecTime_frestrictLe n ω (by omega)]
  rfl

omit [Fintype S] [DecidableEq S] [Countable S] [MeasurableSingletonClass S] in
theorem measurable_histRecTime (n k : ℕ) :
    Measurable fun hist : (i : Finset.Iic n) → JumpHoldTrajectorySpace S i => histRecTime n hist k := by
  unfold histRecTime
  refine Finset.measurable_sum _ fun j _ => ?_
  split_ifs
  · exact (measurable_pi_apply _).fst
  · exact measurable_const

theorem measurable_histExpSum (Q : QMatrix S) {g : ℝ → S → S → ℂ} {D : Set ℝ}
    (hg : IsExpTilt g D) (t : ℝ) (n : ℕ) :
    Measurable (Q.histExpSum g t n) := by
  unfold histExpSum
  refine Finset.measurable_sum _ fun k _ => ?_
  split_ifs with h
  · have hF : Measurable fun p : (ℝ × (ℝ × S)) × S => Q.expStepExponent g t p.1.1 p.2 p.1.2 :=
      measurable_from_prod_countable_left fun x => Q.measurable_expStepExponent hg t x
    exact hF.comp (((measurable_histRecTime n k).prodMk (measurable_pi_apply _)).prodMk
      (measurable_pi_apply _).snd)
  · exact measurable_const

omit [Countable S] [MeasurableSpace S] [MeasurableSingletonClass S] in
theorem re_histExpSum_le (Q : QMatrix S) {g : ℝ → S → S → ℂ} {C : ℝ}
    (hC : ∀ s x y, ‖g s x y‖ ≤ C) (t : ℝ) (n : ℕ)
    (hist : (i : Finset.Iic n) → JumpHoldTrajectorySpace S i) :
    (Q.histExpSum g t n hist).re ≤ n * (C + Q.expCompBound C * |t|) := by
  unfold histExpSum
  rw [Complex.re_sum]
  calc _ ≤ ∑ _k ∈ Finset.range n, (C + Q.expCompBound C * |t|) := by
        refine Finset.sum_le_sum fun k hk => ?_
        rw [dif_pos (show k + 1 ≤ n from Finset.mem_range.mp hk)]
        exact Q.re_expStepExponent_le hC t _ _ _
    _ = n * (C + Q.expCompBound C * |t|) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- **Martingale identity (FIX-KURTZ2 Lemma 2.2).** For a bounded measurable function `ξ` of the
record history through `n`, `E[ξ Z_{n+1}(t)] = E[ξ Z_n(t)]`.  Proof: by the Ionescu-Tulcea
identity `canonicalRecordMeasure_history_next`, the joint law of (history, next record) is the
history law composed with the jump-hold kernel at the current state, and the inner integral of the
step factor is `1` by `integral_cexp_expStepExponent`. -/
theorem integral_mul_cexp_expSum_succ (Q : QMatrix S) {g : ℝ → S → S → ℂ} {D : Set ℝ}
    (hg : IsExpTilt g D) (t : ℝ) (s₀ : S) (n : ℕ)
    {ξ : ((i : Finset.Iic n) → JumpHoldTrajectorySpace S i) → ℂ} (hξm : Measurable ξ) {Cξ : ℝ}
    (hξ : ∀ h, ‖ξ h‖ ≤ Cξ) :
    ∫ ω, ξ (Preorder.frestrictLe n ω) * Complex.exp (Q.expSum g t (n + 1) ω)
        ∂Q.canonicalRecordMeasure s₀ =
      ∫ ω, ξ (Preorder.frestrictLe n ω) * Complex.exp (Q.expSum g t n ω)
        ∂Q.canonicalRecordMeasure s₀ := by
  obtain ⟨C, hC⟩ := hg.bdd
  set μ := Q.canonicalRecordMeasure s₀ with hμ
  set κ := Q.jumpHoldTrajectoryStepKernel (S := S) n with hκ
  haveI : ProbabilityTheory.IsMarkovKernel κ := Q.isMarkovKernel_jumpHoldTrajectoryStepKernel n
  set K := C + Q.expCompBound C * |t| with hK
  -- the history-only factor and the step factor
  set Ψ : ((i : Finset.Iic n) → JumpHoldTrajectorySpace S i) → ℂ :=
    fun hist => ξ hist * Complex.exp (Q.histExpSum g t n hist) with hΨ
  set Φ : ((i : Finset.Iic n) → JumpHoldTrajectorySpace S i) × JumpHoldTrajectorySpace S (n + 1) → ℂ :=
    fun p => Ψ p.1 * Complex.exp (Q.expStepExponent g t (histRecTime n p.1 n)
      (QMatrix.currentStateFromHistory (S := S) n p.1) p.2) with hΦ
  have hΨm : Measurable Ψ :=
    hξm.mul (Complex.measurable_exp.comp (Q.measurable_histExpSum hg t n))
  have hΨb : ∀ hist, ‖Ψ hist‖ ≤ Cξ * Real.exp (n * K) := by
    intro hist
    rw [hΨ, norm_mul, Complex.norm_exp]
    exact mul_le_mul (hξ hist) (Real.exp_le_exp.mpr (Q.re_histExpSum_le hC t n hist))
      (Real.exp_pos _).le ((norm_nonneg _).trans (hξ hist))
  have hΦm : Measurable Φ := by
    refine (hΨm.comp measurable_fst).mul (Complex.measurable_exp.comp ?_)
    have hF : Measurable fun p : (ℝ × (ℝ × S)) × S => Q.expStepExponent g t p.1.1 p.2 p.1.2 :=
      measurable_from_prod_countable_left fun x => Q.measurable_expStepExponent hg t x
    exact hF.comp ((((measurable_histRecTime n n).comp measurable_fst).prodMk
      measurable_snd).prodMk ((QMatrix.measurable_currentStateFromHistory (S := S) n).comp
        measurable_fst))
  have hΦb : ∀ p, ‖Φ p‖ ≤ Cξ * Real.exp (n * K) * Real.exp K := by
    intro p
    rw [hΦ, norm_mul]
    refine mul_le_mul (hΨb p.1) ?_ (norm_nonneg _) ?_
    · rw [Complex.norm_exp]
      exact Real.exp_le_exp.mpr (Q.re_expStepExponent_le hC t _ _ _)
    · exact (norm_nonneg _).trans (hΨb p.1)
  -- the left side is `∫ Φ ∘ π`
  set π : ((m : ℕ) → JumpHoldTrajectorySpace S m) →
      ((i : Finset.Iic n) → JumpHoldTrajectorySpace S i) × JumpHoldTrajectorySpace S (n + 1) :=
    fun ω => (Preorder.frestrictLe n ω, ω (n + 1)) with hπ
  have hπm : Measurable π := (Preorder.measurable_frestrictLe n).prodMk (measurable_pi_apply _)
  have hleft : ∀ ω, ξ (Preorder.frestrictLe n ω) * Complex.exp (Q.expSum g t (n + 1) ω) =
      Φ (π ω) := by
    intro ω
    simp only [hΦ, hΨ, hπ, Q.expSum_succ, Complex.exp_add, Q.histExpSum_frestrictLe,
      histRecTime_frestrictLe n ω le_rfl, QMatrix.currentStateFromHistory_frestrictLe,
      QMatrix.recordTrajectoryToPath_stateSeq]
    ring
  have hright : ∀ ω, ξ (Preorder.frestrictLe n ω) * Complex.exp (Q.expSum g t n ω) =
      Ψ (Preorder.frestrictLe n ω) := by
    intro ω
    simp only [hΨ, Q.histExpSum_frestrictLe]
  simp_rw [hleft, hright]
  rw [← integral_map hπm.aemeasurable hΦm.aestronglyMeasurable,
    ← integral_map (Preorder.measurable_frestrictLe n).aemeasurable hΨm.aestronglyMeasurable]
  have hnext := Q.canonicalRecordMeasure_history_next s₀ n
  rw [show μ.map π = μ.map (fun ω => (Preorder.frestrictLe n ω, ω (n + 1))) from rfl, hnext]
  haveI : IsFiniteMeasure (μ.map (Preorder.frestrictLe n) ⊗ₘ κ) := by
    rw [← hnext]
    infer_instance
  have hΦint : Integrable Φ (μ.map (Preorder.frestrictLe n) ⊗ₘ κ) :=
    (integrable_const (Cξ * Real.exp (n * K) * Real.exp K)).mono' hΦm.aestronglyMeasurable
      (Filter.Eventually.of_forall hΦb)
  rw [Measure.integral_compProd hΦint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun hist => ?_)
  simp only [hΦ]
  rw [integral_const_mul, hκ, QMatrix.jumpHoldTrajectoryStepKernel_apply,
    Q.integral_cexp_expStepExponent hg, mul_one]

/-- `E Z_n(t) = 1` for every record index `n`. -/
theorem integral_cexp_expSum (Q : QMatrix S) {g : ℝ → S → S → ℂ} {D : Set ℝ}
    (hg : IsExpTilt g D) (t : ℝ) (s₀ : S) (n : ℕ) :
    ∫ ω, Complex.exp (Q.expSum g t n ω) ∂Q.canonicalRecordMeasure s₀ = 1 := by
  induction n with
  | zero => simp [expSum]
  | succ n ih =>
    have h := Q.integral_mul_cexp_expSum_succ hg t s₀ n (ξ := fun _ => (1 : ℂ))
      measurable_const (Cξ := 1) (fun _ => by simp)
    simpa using h.trans (by simpa using ih)

/-! ### The real exponential martingale and Ville's inequality (Lemma 2.3) -/

theorem integral_mul_exp_realExpSum_succ (Q : QMatrix S) (φ : S → ℝ) (t : ℝ) (s₀ : S) (n : ℕ)
    {ξ : ((i : Finset.Iic n) → JumpHoldTrajectorySpace S i) → ℝ} (hξm : Measurable ξ) {Cξ : ℝ}
    (hξ : ∀ h, ‖ξ h‖ ≤ Cξ) :
    ∫ ω, ξ (Preorder.frestrictLe n ω) * Real.exp (Q.realExpSum φ t (n + 1) ω)
        ∂Q.canonicalRecordMeasure s₀ =
      ∫ ω, ξ (Preorder.frestrictLe n ω) * Real.exp (Q.realExpSum φ t n ω)
        ∂Q.canonicalRecordMeasure s₀ := by
  have h := Q.integral_mul_cexp_expSum_succ (isExpTilt_realTilt φ) t s₀ n
    (ξ := fun hist => ((ξ hist : ℝ) : ℂ)) (Complex.measurable_ofReal.comp hξm) (Cξ := Cξ)
    (fun hist => by simpa using hξ hist)
  simp_rw [Q.expSum_realTilt, ← Complex.ofReal_exp, ← Complex.ofReal_mul,
    integral_complex_ofReal] at h
  exact_mod_cast h

omit [Countable S] [MeasurableSpace S] [MeasurableSingletonClass S] in
theorem norm_exp_realExpSum_le (Q : QMatrix S) (φ : S → ℝ) (t : ℝ) (n : ℕ)
    (ω : (n : ℕ) → JumpHoldTrajectorySpace S n) :
    ‖Real.exp (Q.realExpSum φ t n ω)‖ ≤
      Real.exp (n * (2 * ∑ y, |φ y| + Q.expCompBound (2 * ∑ y, |φ y|) * |t|)) := by
  have hC : ∀ s x y, ‖realTilt φ s x y‖ ≤ 2 * ∑ y, |φ y| := by
    intro s x y
    have hC' : ∀ x, |φ x| ≤ ∑ y, |φ y| := fun x =>
      Finset.single_le_sum (f := fun y => |φ y|) (fun _ _ => abs_nonneg _) (Finset.mem_univ x)
    simp only [realTilt, Complex.norm_real, Real.norm_eq_abs]
    calc |φ y - φ x| ≤ |φ y| + |φ x| := abs_sub _ _
      _ ≤ (∑ y, |φ y|) + ∑ y, |φ y| := add_le_add (hC' y) (hC' x)
      _ = 2 * ∑ y, |φ y| := by ring
  have h := Q.norm_cexp_expSum_le hC t n ω
  rw [Q.expSum_realTilt, ← Complex.ofReal_exp, Complex.norm_real] at h
  exact h

/-- The real exponential functional `Z_n = exp(log Z_n)` is a Mathlib martingale for the canonical
record filtration. -/
theorem martingale_exp_realExpSum (Q : QMatrix S) (φ : S → ℝ) (t : ℝ) (s₀ : S) :
    MeasureTheory.Martingale (fun n ω => Real.exp (Q.realExpSum φ t n ω))
      (QMatrix.canonicalRecordFiltration (S := S)) (Q.canonicalRecordMeasure s₀) := by
  set μ := Q.canonicalRecordMeasure s₀ with hμ
  have hadp : MeasureTheory.StronglyAdapted (QMatrix.canonicalRecordFiltration (S := S))
      (fun n ω => Real.exp (Q.realExpSum φ t n ω)) := fun n =>
    (Real.measurable_exp.comp
      (Q.measurable_realExpSum_canonicalRecordFiltration φ t n)).stronglyMeasurable
  have hmeas : ∀ n, Measurable fun ω => Real.exp (Q.realExpSum φ t n ω) := fun n =>
    (hadp n).measurable.mono ((QMatrix.canonicalRecordFiltration (S := S)).le n) le_rfl
  have hint : ∀ n, Integrable (fun ω => Real.exp (Q.realExpSum φ t n ω)) μ := fun n =>
    (integrable_const _).mono' (hmeas n).aestronglyMeasurable
      (Filter.Eventually.of_forall (Q.norm_exp_realExpSum_le φ t n))
  refine MeasureTheory.martingale_of_setIntegral_eq_succ hadp hint fun n s hs => ?_
  rw [QMatrix.canonicalRecordFiltration_apply_eq_comap_frestrictLe (S := S) n,
    MeasurableSpace.measurableSet_comap] at hs
  obtain ⟨A, hA, rfl⟩ := hs
  have hA' : MeasurableSet (Preorder.frestrictLe n ⁻¹' A) :=
    (Preorder.measurable_frestrictLe n) hA
  have hind : ∀ k ω, (Preorder.frestrictLe n ⁻¹' A).indicator
      (fun ω => Real.exp (Q.realExpSum φ t k ω)) ω =
      A.indicator (fun _ => (1 : ℝ)) (Preorder.frestrictLe n ω) *
        Real.exp (Q.realExpSum φ t k ω) := by
    intro k ω
    by_cases hω : Preorder.frestrictLe n ω ∈ A
    · simp [Set.indicator_of_mem hω,
        Set.indicator_of_mem (show ω ∈ Preorder.frestrictLe n ⁻¹' A from hω)]
    · simp [Set.indicator_of_notMem hω,
        Set.indicator_of_notMem (show ω ∉ Preorder.frestrictLe n ⁻¹' A from hω)]
  rw [← integral_indicator hA', ← integral_indicator hA']
  simp_rw [hind]
  exact (Q.integral_mul_exp_realExpSum_succ φ t s₀ n (measurable_const.indicator hA) (Cξ := 1)
    (fun h => by
      calc ‖A.indicator (fun _ => (1 : ℝ)) h‖ ≤ ‖(1 : ℝ)‖ := norm_indicator_le_norm_self _ _
        _ = 1 := norm_one)).symm

theorem integral_exp_realExpSum (Q : QMatrix S) (φ : S → ℝ) (t : ℝ) (s₀ : S) (n : ℕ) :
    ∫ ω, Real.exp (Q.realExpSum φ t n ω) ∂Q.canonicalRecordMeasure s₀ = 1 := by
  have h := Q.integral_cexp_expSum (isExpTilt_realTilt φ) t s₀ n
  simp_rw [Q.expSum_realTilt, ← Complex.ofReal_exp, integral_complex_ofReal] at h
  exact_mod_cast h

/-- **Ville's maximal inequality (FIX-KURTZ2 Lemma 2.3).** For the real exponential martingale
`Z_n(t) = exp(log Z_n(t))` and every `a > 0`, `P(∃ n, Z_n(t) ≥ a) ≤ 1/a`. -/
theorem ville_realExpSum (Q : QMatrix S) (φ : S → ℝ) (t : ℝ) (s₀ : S) {a : ℝ} (ha : 0 < a) :
    Q.canonicalRecordMeasure s₀ {ω | ∃ n, a ≤ Real.exp (Q.realExpSum φ t n ω)} ≤
      ENNReal.ofReal (1 / a) := by
  set μ := Q.canonicalRecordMeasure s₀ with hμ
  set Z : ℕ → ((n : ℕ) → JumpHoldTrajectorySpace S n) → ℝ :=
    fun n ω => Real.exp (Q.realExpSum φ t n ω) with hZ
  have hmart := Q.martingale_exp_realExpSum φ t s₀
  have hZpos : ∀ n ω, 0 < Z n ω := fun n ω => Real.exp_pos _
  set aNN : NNReal := ⟨a, ha.le⟩ with haNN
  have haNN_coe : ((aNN : NNReal) : ℝ) = a := rfl
  have haNN_ennreal : ((aNN : NNReal) : ENNReal) = ENNReal.ofReal a := by
    rw [ENNReal.ofReal, Real.toNNReal_of_nonneg ha.le]
    rfl
  have hfin : ∀ n, μ {ω | ∃ k ≤ n, a ≤ Z k ω} ≤ ENNReal.ofReal (1 / a) := by
    intro n
    have hset : {ω | ∃ k ≤ n, a ≤ Z k ω} =
        {ω | ((aNN : NNReal) : ℝ) ≤
          (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one fun k => Z k ω} := by
      ext ω
      simp only [Set.mem_setOf_eq, haNN_coe, Finset.le_sup'_iff, Finset.mem_range,
        Nat.lt_succ_iff]
    rw [hset]
    have h := MeasureTheory.maximal_ineq hmart.submartingale (fun k ω => (hZpos k ω).le)
      (ε := aNN) n
    have hint : Integrable (Z n) μ := hmart.integrable n
    have hle : ∫ ω in {ω | ((aNN : NNReal) : ℝ) ≤
        (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one fun k => Z k ω}, Z n ω ∂μ ≤
        ∫ ω, Z n ω ∂μ :=
      setIntegral_le_integral hint (Filter.Eventually.of_forall fun ω => (hZpos n ω).le)
    rw [Q.integral_exp_realExpSum φ t s₀ n] at hle
    have h1 : (ENNReal.ofReal a) * μ {ω | ((aNN : NNReal) : ℝ) ≤
        (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one fun k => Z k ω} ≤ 1 := by
      rw [← haNN_ennreal]
      refine h.trans ?_
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal hle
    rw [ENNReal.ofReal_div_of_pos ha, ENNReal.ofReal_one]
    rw [ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.ofReal_pos.mpr ha).ne')
      (Or.inl ENNReal.ofReal_ne_top), mul_comm]
    exact h1
  have hunion : {ω | ∃ n, a ≤ Z n ω} = ⋃ n, {ω | ∃ k ≤ n, a ≤ Z k ω} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨n, hn⟩
      exact ⟨n, n, le_rfl, hn⟩
    · rintro ⟨n, k, _, hk⟩
      exact ⟨k, hk⟩
  have hmono : Monotone fun n => {ω | ∃ k ≤ n, a ≤ Z k ω} := by
    intro m n hmn ω hω
    obtain ⟨k, hk, h⟩ := hω
    exact ⟨k, hk.trans hmn, h⟩
  change μ {ω | ∃ n, a ≤ Z n ω} ≤ _
  rw [hunion]
  exact le_of_tendsto' (tendsto_measure_iUnion_atTop hmono) hfin

end Martingale

end QMatrix

end Ripple.CTMC
