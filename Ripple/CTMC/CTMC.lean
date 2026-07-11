/-
  Ripple.CTMC.CTMC — Continuous-Time Markov Chains

  A CTMC on a finite state space S is specified by a Q-matrix
  (infinitesimal generator). The process is constructed via
  jump-and-hold: exponential holding times + embedded DTMC.

  We define:
  - Q-matrix (generator matrix)
  - Embedded DTMC (jump chain)
  - Holding time rates
  - The CTMC process (jump-and-hold construction)
  - Transition semigroup P(t) = exp(tQ)
  - Kolmogorov forward equation: P'(t) = P(t)Q
-/

import Ripple.CTMC.DTMC
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.Kernel.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

open scoped ENNReal

namespace ProbabilityTheory

open MeasureTheory Real Set

/-- First moment of the exponential distribution with positive rate. -/
theorem integral_expMeasure_id {r : ℝ} (hr : 0 < r) :
    ∫ x : ℝ, x ∂expMeasure r = r⁻¹ := by
  rw [expMeasure, gammaMeasure]
  rw [integral_withDensity_eq_integral_toReal_smul]
  · simp only [smul_eq_mul]
    calc
      ∫ x : ℝ, (gammaPDF 1 r x).toReal * x ∂volume
          = ∫ x : ℝ, (Set.Ioi (0 : ℝ)).indicator
              (fun x : ℝ => r * Real.exp (-(r * x)) * x) x ∂volume := by
            apply integral_congr_ae
            filter_upwards with x
            by_cases hx : 0 < x
            · have hxle : 0 ≤ x := le_of_lt hx
              have hpdf_nonneg : 0 ≤ r * Real.exp (-(r * x)) :=
                mul_nonneg hr.le (Real.exp_pos _).le
              simp [Set.indicator, hx, gammaPDF, gammaPDFReal, hxle,
                Real.Gamma_one, hpdf_nonneg]
            · have hnot : x ∉ Set.Ioi (0 : ℝ) := by simpa [Set.mem_Ioi] using hx
              by_cases hxle : 0 ≤ x
              · have hx0 : x = 0 := le_antisymm (le_of_not_gt hx) hxle
                simp [Set.indicator, gammaPDF, gammaPDFReal, hx0]
              · simp [Set.indicator, hnot, gammaPDF, gammaPDFReal, hxle]
      _ = ∫ x in Set.Ioi (0 : ℝ), r * Real.exp (-(r * x)) * x ∂volume := by
            rw [integral_indicator measurableSet_Ioi]
      _ = ∫ x in Set.Ioi (0 : ℝ),
            r * (x ^ ((2 : ℝ) - 1) * Real.exp (-(r * x))) ∂volume := by
            apply setIntegral_congr_fun measurableSet_Ioi
            intro x hx
            simp [show (2 : ℝ) - 1 = 1 by norm_num, mul_comm, mul_left_comm]
      _ = r * ∫ x in Set.Ioi (0 : ℝ),
            x ^ ((2 : ℝ) - 1) * Real.exp (-(r * x)) ∂volume := by
            rw [integral_const_mul]
      _ = r * ((1 / r) ^ (2 : ℝ) * Real.Gamma (2 : ℝ)) := by
            rw [Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (r := r)
              (by norm_num) hr]
      _ = r⁻¹ := by
            have hG2 : Real.Gamma (2 : ℝ) = 1 := by
              rw [show (2 : ℝ) = 1 + 1 by norm_num,
                Real.Gamma_add_one one_ne_zero, Real.Gamma_one]
              norm_num
            rw [hG2, mul_one, Real.rpow_two]
            field_simp [hr.ne']
  · exact (measurable_gammaPDFReal 1 r).ennreal_ofReal
  · filter_upwards with x
    simp [gammaPDF]

/-- The identity random variable is integrable under a positive-rate
exponential law. -/
theorem integrable_id_expMeasure {r : ℝ} (hr : 0 < r) :
    Integrable (fun x : ℝ => x) (expMeasure r) := by
  by_contra hnot
  have hmean := integral_expMeasure_id hr
  rw [integral_undef hnot] at hmean
  have hinv_pos : 0 < r⁻¹ := inv_pos.mpr hr
  linarith

/-- Second moment of the exponential distribution with positive rate. -/
theorem integral_expMeasure_sq {r : ℝ} (hr : 0 < r) :
    ∫ x : ℝ, x ^ 2 ∂expMeasure r = 2 * (1 / r) ^ 2 := by
  rw [expMeasure, gammaMeasure]
  rw [integral_withDensity_eq_integral_toReal_smul]
  · simp only [smul_eq_mul]
    calc
      ∫ x : ℝ, (gammaPDF 1 r x).toReal * x ^ 2 ∂volume
          = ∫ x : ℝ, (Set.Ioi (0 : ℝ)).indicator
              (fun x : ℝ => r * Real.exp (-(r * x)) * x ^ 2) x ∂volume := by
            apply integral_congr_ae
            filter_upwards with x
            by_cases hx : 0 < x
            · have hxle : 0 ≤ x := le_of_lt hx
              have hpdf_nonneg : 0 ≤ r * Real.exp (-(r * x)) :=
                mul_nonneg hr.le (Real.exp_pos _).le
              simp [Set.indicator, hx, gammaPDF, gammaPDFReal, hxle,
                Real.Gamma_one, hpdf_nonneg]
            · have hnot : x ∉ Set.Ioi (0 : ℝ) := by simpa [Set.mem_Ioi] using hx
              by_cases hxle : 0 ≤ x
              · have hx0 : x = 0 := le_antisymm (le_of_not_gt hx) hxle
                simp [Set.indicator, gammaPDF, gammaPDFReal, hx0]
              · simp [Set.indicator, hnot, gammaPDF, gammaPDFReal, hxle]
      _ = ∫ x in Set.Ioi (0 : ℝ), r * Real.exp (-(r * x)) * x ^ 2 ∂volume := by
            rw [integral_indicator measurableSet_Ioi]
      _ = ∫ x in Set.Ioi (0 : ℝ),
            r * (x ^ ((3 : ℝ) - 1) * Real.exp (-(r * x))) ∂volume := by
            apply setIntegral_congr_fun measurableSet_Ioi
            intro x hx
            simp [show (3 : ℝ) - 1 = 2 by norm_num, mul_comm, mul_left_comm]
      _ = r * ∫ x in Set.Ioi (0 : ℝ),
            x ^ ((3 : ℝ) - 1) * Real.exp (-(r * x)) ∂volume := by
            rw [integral_const_mul]
      _ = r * ((1 / r) ^ (3 : ℝ) * Real.Gamma (3 : ℝ)) := by
            rw [Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 3) (r := r)
              (by norm_num) hr]
      _ = 2 * (1 / r) ^ 2 := by
            have hG3 : Real.Gamma (3 : ℝ) = 2 := by
              rw [show (3 : ℝ) = 2 + 1 by norm_num,
                Real.Gamma_add_one (by norm_num : (2 : ℝ) ≠ 0)]
              have hG2 : Real.Gamma (2 : ℝ) = 1 := by
                rw [show (2 : ℝ) = 1 + 1 by norm_num,
                  Real.Gamma_add_one one_ne_zero, Real.Gamma_one]
                norm_num
              rw [hG2]
              norm_num
            rw [hG3]
            rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num]
            rw [Real.rpow_natCast]
            field_simp [hr.ne']
  · exact (measurable_gammaPDFReal 1 r).ennreal_ofReal
  · filter_upwards with x
    simp [gammaPDF]

/-- The squared identity random variable is integrable under a positive-rate
exponential law. -/
theorem integrable_sq_expMeasure {r : ℝ} (hr : 0 < r) :
    Integrable (fun x : ℝ => x ^ 2) (expMeasure r) := by
  by_contra hnot
  have hsecond := integral_expMeasure_sq hr
  rw [integral_undef hnot] at hsecond
  have hdiv_pos : 0 < 1 / r := div_pos zero_lt_one hr
  have hsecond_pos : 0 < 2 * (1 / r) ^ 2 := by
    nlinarith [sq_pos_of_pos hdiv_pos]
  linarith

end ProbabilityTheory

namespace Ripple.CTMC

open scoped ENNReal Matrix
open NormedSpace

/-- A Q-matrix (infinitesimal generator) for a finite-state CTMC.
`q s t` is the rate of transitioning from s to t (for s ≠ t).
The diagonal satisfies q(s,s) = -Σ_{t≠s} q(s,t). -/
structure QMatrix (S : Type*) [Fintype S] [DecidableEq S] where
  /-- Off-diagonal transition rates. -/
  rate : S → S → ℝ
  /-- Off-diagonal rates are nonneg. -/
  rate_nonneg : ∀ s t, s ≠ t → 0 ≤ rate s t
  /-- Diagonal is minus the sum of off-diagonal rates. -/
  rate_diag : ∀ s, rate s s = -∑ t ∈ Finset.univ.filter (· ≠ s), rate s t

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Total exit rate from state s. -/
noncomputable def QMatrix.exitRate (Q : QMatrix S) (s : S) : ℝ :=
  ∑ t ∈ Finset.univ.filter (· ≠ s), Q.rate s t

/-- Exit rate is nonneg. -/
theorem QMatrix.exitRate_nonneg (Q : QMatrix S) (s : S) :
    0 ≤ Q.exitRate s :=
  Finset.sum_nonneg fun t ht => Q.rate_nonneg s t (Finset.mem_filter.mp ht).2.symm

/-- Diagonal entry equals negative exit rate. -/
theorem QMatrix.diag_eq_neg_exitRate (Q : QMatrix S) (s : S) :
    Q.rate s s = -Q.exitRate s :=
  Q.rate_diag s

/-- A state is absorbing if its exit rate is zero. -/
def QMatrix.IsAbsorbing (Q : QMatrix S) (s : S) : Prop :=
  Q.exitRate s = 0

/-- Absorbing states have zero off-diagonal rates. -/
theorem QMatrix.IsAbsorbing.rate_eq_zero (Q : QMatrix S) {s : S}
    (h : Q.IsAbsorbing s) (t : S) (hne : s ≠ t) : Q.rate s t = 0 := by
  have hnn := Q.rate_nonneg s t hne
  have hsum : ∑ u ∈ Finset.univ.filter (· ≠ s), Q.rate s u = 0 := h
  exact le_antisymm
    (Finset.single_le_sum (fun u hu => Q.rate_nonneg s u (Finset.mem_filter.mp hu).2.symm)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ t, hne.symm⟩) |>.trans hsum.le)
    hnn

/-- Row sum is zero: Σ_t q(s,t) = 0. -/
theorem QMatrix.row_sum_zero (Q : QMatrix S) (s : S) :
    ∑ t, Q.rate s t = 0 := by
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ s)]
  rw [Q.diag_eq_neg_exitRate, exitRate, Finset.filter_ne']
  linarith

/-- Normalized jump probability: q(s,t)/exitRate(s) for s ≠ t, 0 for s = t.
When the exit rate is zero (absorbing state), this returns 0 everywhere. -/
noncomputable def QMatrix.jumpProb (Q : QMatrix S) (s t : S) : ℝ≥0∞ :=
  if s = t then 0
  else ENNReal.ofReal (Q.rate s t / Q.exitRate s)

/-- Jump probabilities sum to 1 for non-absorbing states. -/
theorem QMatrix.jumpProb_sum (Q : QMatrix S) (s : S) (h : Q.exitRate s ≠ 0) :
    ∑ t, Q.jumpProb s t = 1 := by
  have h_pos : 0 < Q.exitRate s := lt_of_le_of_ne (Q.exitRate_nonneg s) (Ne.symm h)
  simp only [jumpProb]
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ s), if_pos rfl, zero_add]
  rw [Finset.sum_congr rfl (fun t ht =>
    if_neg (Finset.ne_of_mem_erase ht).symm)]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun t ht => div_nonneg
    (Q.rate_nonneg s t (Finset.ne_of_mem_erase ht).symm)
    (le_of_lt h_pos))]
  rw [← Finset.sum_div]
  have : ∑ t ∈ Finset.univ.erase s, Q.rate s t = Q.exitRate s := by
    rw [exitRate, ← Finset.filter_ne']
  rw [this, div_self (ne_of_gt h_pos), ENNReal.ofReal_one]

/-- The embedded DTMC: jump chain of the CTMC.
For non-absorbing states, jumps with probability q(s,t)/exitRate(s).
For absorbing states, stays put. -/
noncomputable def QMatrix.embeddedDTMC (Q : QMatrix S) [Countable S] :
    DTMC S where
  step s :=
    if h : Q.exitRate s = 0 then
      PMF.pure s
    else
      PMF.ofFintype (Q.jumpProb s) (Q.jumpProb_sum s h)

/-- Jump probability from s to itself is always 0. -/
theorem QMatrix.jumpProb_self (Q : QMatrix S) (s : S) :
    Q.jumpProb s s = 0 := by
  simp [jumpProb]

/-- A positive off-diagonal rate gives positive embedded jump probability. -/
theorem QMatrix.jumpProb_pos_of_rate_pos (Q : QMatrix S) {s t : S}
    (hst : s ≠ t) (hrate : 0 < Q.rate s t) :
    0 < Q.jumpProb s t := by
  have hmem : t ∈ Finset.univ.filter (· ≠ s) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ t, hst.symm⟩
  have hle : Q.rate s t ≤ Q.exitRate s :=
    Finset.single_le_sum
      (fun u hu => Q.rate_nonneg s u (Finset.mem_filter.mp hu).2.symm) hmem
  have hexit_pos : 0 < Q.exitRate s := hrate.trans_le hle
  rw [jumpProb, if_neg hst]
  exact ENNReal.ofReal_pos.mpr (div_pos hrate hexit_pos)

/-- Zero off-diagonal rate gives zero embedded jump probability. -/
theorem QMatrix.jumpProb_eq_zero_of_rate_eq_zero (Q : QMatrix S) {s t : S}
    (hst : s ≠ t) (hrate : Q.rate s t = 0) :
    Q.jumpProb s t = 0 := by
  rw [jumpProb, if_neg hst, hrate, zero_div, ENNReal.ofReal_zero]

/-- For non-absorbing states, the embedded DTMC step equals jumpProb. -/
theorem QMatrix.embeddedDTMC_step_of_nonabsorbing (Q : QMatrix S) [Countable S]
    {s : S} (h : ¬Q.IsAbsorbing s) (t : S) :
    Q.embeddedDTMC.step s t = Q.jumpProb s t := by
  have hne : Q.exitRate s ≠ 0 := h
  simp only [embeddedDTMC, dif_neg hne, PMF.ofFintype_apply]

/-- For absorbing states, the embedded DTMC stays put. -/
theorem QMatrix.embeddedDTMC_step_of_absorbing (Q : QMatrix S) [Countable S]
    {s : S} (h : Q.IsAbsorbing s) (t : S) :
    Q.embeddedDTMC.step s t = if t = s then 1 else 0 := by
  simp only [embeddedDTMC, IsAbsorbing] at h ⊢
  simp [h, PMF.pure_apply]

/-- The embedded jump chain has no self-jump from a non-absorbing state. -/
theorem QMatrix.embeddedDTMC_step_self_of_nonabsorbing (Q : QMatrix S) [Countable S]
    {s : S} (h : ¬Q.IsAbsorbing s) :
    Q.embeddedDTMC.step s s = 0 := by
  rw [Q.embeddedDTMC_step_of_nonabsorbing h s, Q.jumpProb_self]

/-- Positive off-diagonal generator rate gives positive one-step probability
in the embedded jump chain. -/
theorem QMatrix.embeddedDTMC_step_pos_of_rate_pos (Q : QMatrix S) [Countable S]
    {s t : S} (hst : s ≠ t) (hrate : 0 < Q.rate s t) :
    0 < Q.embeddedDTMC.step s t := by
  have hnabs : ¬Q.IsAbsorbing s := by
    intro h
    have hz := QMatrix.IsAbsorbing.rate_eq_zero Q h t hst
    linarith
  rw [Q.embeddedDTMC_step_of_nonabsorbing hnabs t]
  exact Q.jumpProb_pos_of_rate_pos hst hrate

/-- Zero off-diagonal generator rate gives zero one-step probability in the
embedded jump chain, for non-absorbing sources. -/
theorem QMatrix.embeddedDTMC_step_eq_zero_of_rate_eq_zero
    (Q : QMatrix S) [Countable S] {s t : S}
    (hsrc : ¬Q.IsAbsorbing s) (hst : s ≠ t) (hrate : Q.rate s t = 0) :
    Q.embeddedDTMC.step s t = 0 := by
  rw [Q.embeddedDTMC_step_of_nonabsorbing hsrc t]
  exact Q.jumpProb_eq_zero_of_rate_eq_zero hst hrate

/-- The embedded jump-chain row as a probability measure.  This is the
measure-valued form used by kernel/product-measure constructions. -/
noncomputable def QMatrix.embeddedStepMeasure (Q : QMatrix S)
    [Countable S] [MeasurableSpace S] (s : S) : MeasureTheory.Measure S :=
  (Q.embeddedDTMC.step s).toMeasure

/-- The embedded jump-chain row measure is a probability measure. -/
theorem QMatrix.isProbabilityMeasure_embeddedStepMeasure (Q : QMatrix S)
    [Countable S] [MeasurableSpace S] (s : S) :
    MeasureTheory.IsProbabilityMeasure (Q.embeddedStepMeasure s) := by
  dsimp [embeddedStepMeasure]
  infer_instance

/-- Singleton masses of the embedded row measure recover the embedded DTMC
probabilities. -/
theorem QMatrix.embeddedStepMeasure_singleton (Q : QMatrix S)
    [Countable S] [MeasurableSpace S] [MeasurableSingletonClass S]
    (s t : S) :
    Q.embeddedStepMeasure s {t} = Q.embeddedDTMC.step s t := by
  simp [embeddedStepMeasure]

/-- Expectation against the embedded jump-chain row is the finite PMF sum. -/
theorem QMatrix.integral_embeddedStepMeasure_eq_sum (Q : QMatrix S)
    [Countable S] [MeasurableSpace S] [MeasurableSingletonClass S]
    {s : S} (h : ¬Q.IsAbsorbing s) (f : S → ℝ) :
    ∫ t, f t ∂Q.embeddedStepMeasure s =
      ∑ t, (Q.jumpProb s t).toReal * f t := by
  rw [QMatrix.embeddedStepMeasure]
  rw [PMF.integral_eq_sum]
  apply Finset.sum_congr rfl
  intro t _ht
  rw [Q.embeddedDTMC_step_of_nonabsorbing h t]
  simp

/-- Multiplying the embedded jump expectation by the exit rate recovers the
off-diagonal generator-weighted sum. -/
theorem QMatrix.exitRate_mul_integral_embeddedStepMeasure_eq_sum_rate
    (Q : QMatrix S) [Countable S] [MeasurableSpace S] [MeasurableSingletonClass S]
    {s : S} (h : ¬Q.IsAbsorbing s) (f : S → ℝ) :
    Q.exitRate s * (∫ t, f t ∂Q.embeddedStepMeasure s) =
      ∑ t ∈ Finset.univ.filter (fun t => t ≠ s), Q.rate s t * f t := by
  have hexit_pos : 0 < Q.exitRate s :=
    lt_of_le_of_ne (Q.exitRate_nonneg s) (Ne.symm h)
  rw [Q.integral_embeddedStepMeasure_eq_sum h f]
  rw [Finset.mul_sum]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro t _ht
  by_cases hts : t ≠ s
  · have hst : s ≠ t := Ne.symm hts
    rw [if_pos hts]
    rw [QMatrix.jumpProb, if_neg hst]
    rw [ENNReal.toReal_ofReal]
    · field_simp [ne_of_gt hexit_pos]
    · exact div_nonneg (Q.rate_nonneg s t hst) (le_of_lt hexit_pos)
  · rw [if_neg hts]
    have hst_eq : s = t := (not_ne_iff.mp hts).symm
    rw [QMatrix.jumpProb, if_pos hst_eq]
    simp

/-- Positive generator rate gives positive singleton mass in the embedded row
measure. -/
theorem QMatrix.embeddedStepMeasure_singleton_pos_of_rate_pos
    (Q : QMatrix S) [Countable S] [MeasurableSpace S] [MeasurableSingletonClass S]
    {s t : S} (hst : s ≠ t) (hrate : 0 < Q.rate s t) :
    0 < Q.embeddedStepMeasure s {t} := by
  rw [Q.embeddedStepMeasure_singleton]
  exact Q.embeddedDTMC_step_pos_of_rate_pos hst hrate

/-- A non-absorbing embedded row puts zero mass on staying at the current
state. -/
theorem QMatrix.embeddedStepMeasure_singleton_self_of_nonabsorbing
    (Q : QMatrix S) [Countable S] [MeasurableSpace S] [MeasurableSingletonClass S]
    {s : S} (h : ¬Q.IsAbsorbing s) :
    Q.embeddedStepMeasure s {s} = 0 := by
  rw [Q.embeddedStepMeasure_singleton]
  exact Q.embeddedDTMC_step_self_of_nonabsorbing h

/-- A non-absorbing embedded jump-chain sample differs from the current state
almost surely. -/
theorem QMatrix.embeddedStepMeasure_ne_self_ae_of_nonabsorbing
    (Q : QMatrix S) [Countable S] [MeasurableSpace S] [MeasurableSingletonClass S]
    {s : S} (h : ¬Q.IsAbsorbing s) :
    ∀ᵐ u ∂Q.embeddedStepMeasure s, u ≠ s := by
  have hzero := Q.embeddedStepMeasure_singleton_self_of_nonabsorbing h
  have hnot : ∀ᵐ u ∂Q.embeddedStepMeasure s, u ∉ ({s} : Set S) :=
    MeasureTheory.measure_eq_zero_iff_ae_notMem.mp hzero
  filter_upwards [hnot] with u hu
  simpa using hu

/-- A non-absorbing embedded row samples only positive-rate target states
almost surely.  The zero-rate targets have zero singleton mass in the embedded
jump-chain measure. -/
theorem QMatrix.embeddedStepMeasure_rate_pos_ae_of_nonabsorbing
    (Q : QMatrix S) [Countable S] [MeasurableSpace S] [MeasurableSingletonClass S]
    {s : S} (h : ¬Q.IsAbsorbing s) :
    ∀ᵐ t ∂Q.embeddedStepMeasure s, 0 < Q.rate s t := by
  let bad : Finset S := Finset.univ.filter (fun t => ¬ 0 < Q.rate s t)
  have hbad_zero : Q.embeddedStepMeasure s (bad : Set S) = 0 := by
    rw [QMatrix.embeddedStepMeasure]
    rw [PMF.toMeasure_apply_finset]
    apply Finset.sum_eq_zero
    intro t ht
    have htbad : ¬ 0 < Q.rate s t := (Finset.mem_filter.mp ht).2
    rw [Q.embeddedDTMC_step_of_nonabsorbing h t]
    by_cases hst : s = t
    · rw [QMatrix.jumpProb, if_pos hst]
    · have hrate_nonneg : 0 ≤ Q.rate s t := Q.rate_nonneg s t hst
      have hrate_le : Q.rate s t ≤ 0 := le_of_not_gt htbad
      have hrate0 : Q.rate s t = 0 := le_antisymm hrate_le hrate_nonneg
      rw [QMatrix.jumpProb, if_neg hst, hrate0, zero_div, ENNReal.ofReal_zero]
  have hae_not : ∀ᵐ t ∂Q.embeddedStepMeasure s, t ∉ (bad : Set S) :=
    MeasureTheory.measure_eq_zero_iff_ae_notMem.mp hbad_zero
  filter_upwards [hae_not] with t ht
  have : ¬ ¬ 0 < Q.rate s t := by
    intro hnot
    exact ht (Finset.mem_filter.mpr ⟨Finset.mem_univ t, hnot⟩)
  exact not_not.mp this

/-! ## Holding-time law -/

/-- A non-absorbing state has strictly positive exit rate. -/
theorem QMatrix.exitRate_pos_of_nonabsorbing (Q : QMatrix S) {s : S}
    (h : ¬Q.IsAbsorbing s) :
    0 < Q.exitRate s :=
  lt_of_le_of_ne (Q.exitRate_nonneg s) (Ne.symm h)

/-- Exponential holding-time law at a non-absorbing state.  Absorbing states
are deliberately excluded: in the jump-and-hold construction they do not have
a next finite holding time. -/
noncomputable def QMatrix.holdingTimeMeasure (Q : QMatrix S) {s : S}
    (_h : ¬Q.IsAbsorbing s) : MeasureTheory.Measure ℝ :=
  ProbabilityTheory.expMeasure (Q.exitRate s)

/-- The non-absorbing holding-time law is a probability measure. -/
theorem QMatrix.isProbabilityMeasure_holdingTimeMeasure (Q : QMatrix S) {s : S}
    (h : ¬Q.IsAbsorbing s) :
    MeasureTheory.IsProbabilityMeasure (Q.holdingTimeMeasure h) :=
  ProbabilityTheory.isProbabilityMeasure_expMeasure (Q.exitRate_pos_of_nonabsorbing h)

/-- The holding time at a non-absorbing state has mean `1 / exitRate`. -/
theorem QMatrix.integral_holdingTimeMeasure_eq_inv_exitRate (Q : QMatrix S) {s : S}
    (h : ¬Q.IsAbsorbing s) :
    ∫ t : ℝ, t ∂Q.holdingTimeMeasure h = (Q.exitRate s)⁻¹ :=
  ProbabilityTheory.integral_expMeasure_id (Q.exitRate_pos_of_nonabsorbing h)

/-- Holding time at a non-absorbing state is integrable. -/
theorem QMatrix.integrable_holdingTimeMeasure_id (Q : QMatrix S) {s : S}
    (h : ¬Q.IsAbsorbing s) :
    MeasureTheory.Integrable (fun t : ℝ => t) (Q.holdingTimeMeasure h) :=
  ProbabilityTheory.integrable_id_expMeasure (Q.exitRate_pos_of_nonabsorbing h)

/-- The holding time at a non-absorbing state has second moment
`2 / exitRate^2`. -/
theorem QMatrix.integral_holdingTimeMeasure_sq_eq_two_mul_inv_sq (Q : QMatrix S) {s : S}
    (h : ¬Q.IsAbsorbing s) :
    ∫ t : ℝ, t ^ 2 ∂Q.holdingTimeMeasure h = 2 * (1 / Q.exitRate s) ^ 2 :=
  ProbabilityTheory.integral_expMeasure_sq (Q.exitRate_pos_of_nonabsorbing h)

/-- The squared holding time at a non-absorbing state is integrable. -/
theorem QMatrix.integrable_holdingTimeMeasure_sq (Q : QMatrix S) {s : S}
    (h : ¬Q.IsAbsorbing s) :
    MeasureTheory.Integrable (fun t : ℝ => t ^ 2) (Q.holdingTimeMeasure h) :=
  ProbabilityTheory.integrable_sq_expMeasure (Q.exitRate_pos_of_nonabsorbing h)

/-- CDF of the non-absorbing holding-time law. -/
theorem QMatrix.cdf_holdingTimeMeasure_eq (Q : QMatrix S) {s : S}
    (h : ¬Q.IsAbsorbing s) (t : ℝ) :
    ProbabilityTheory.cdf (Q.holdingTimeMeasure h) t =
      if 0 ≤ t then 1 - Real.exp (-(Q.exitRate s * t)) else 0 :=
  ProbabilityTheory.cdf_expMeasure_eq (Q.exitRate_pos_of_nonabsorbing h) t

/-- A non-absorbing exponential holding-time law assigns zero mass to
non-positive times. -/
theorem QMatrix.holdingTimeMeasure_Iic_zero (Q : QMatrix S) {s : S}
    (h : ¬Q.IsAbsorbing s) :
    Q.holdingTimeMeasure h (Set.Iic 0) = 0 := by
  letI := Q.isProbabilityMeasure_holdingTimeMeasure h
  have hcdf := Q.cdf_holdingTimeMeasure_eq h 0
  have hreal : (Q.holdingTimeMeasure h).real (Set.Iic 0) = 0 := by
    rw [← ProbabilityTheory.cdf_eq_real (Q.holdingTimeMeasure h) 0]
    simpa using hcdf
  exact (MeasureTheory.measureReal_eq_zero_iff).mp hreal

/-- A non-absorbing exponential holding-time sample is positive almost surely. -/
theorem QMatrix.holdingTimeMeasure_pos_ae (Q : QMatrix S) {s : S}
    (h : ¬Q.IsAbsorbing s) :
    ∀ᵐ t ∂Q.holdingTimeMeasure h, 0 < t := by
  have hzero := Q.holdingTimeMeasure_Iic_zero h
  have hnot : ∀ᵐ t ∂Q.holdingTimeMeasure h, t ∉ Set.Iic 0 :=
    MeasureTheory.measure_eq_zero_iff_ae_notMem.mp hzero
  filter_upwards [hnot] with t ht
  exact lt_of_not_ge ht

/-- Real-valued tail probability for a non-absorbing exponential holding-time
law. -/
theorem QMatrix.holdingTimeMeasure_real_Ioi_eq (Q : QMatrix S) {s : S}
    (h : ¬Q.IsAbsorbing s) {δ : ℝ} (hδ : 0 ≤ δ) :
    (Q.holdingTimeMeasure h).real (Set.Ioi δ) =
      Real.exp (-(Q.exitRate s * δ)) := by
  let μ := Q.holdingTimeMeasure h
  letI := Q.isProbabilityMeasure_holdingTimeMeasure h
  have hcdf := Q.cdf_holdingTimeMeasure_eq h δ
  have hreal_iic : μ.real (Set.Iic δ) =
      1 - Real.exp (-(Q.exitRate s * δ)) := by
    rw [← ProbabilityTheory.cdf_eq_real μ δ]
    simpa [μ, hδ] using hcdf
  rw [show Set.Ioi δ = (Set.Iic δ)ᶜ by
    ext x
    simp]
  rw [MeasureTheory.measureReal_compl measurableSet_Iic, hreal_iic]
  simp

/-- A non-absorbing exponential holding-time law assigns positive mass to
every positive tail. -/
theorem QMatrix.holdingTimeMeasure_Ioi_pos (Q : QMatrix S) {s : S}
    (h : ¬Q.IsAbsorbing s) {δ : ℝ} (hδ : 0 ≤ δ) :
    0 < Q.holdingTimeMeasure h (Set.Ioi δ) := by
  let μ := Q.holdingTimeMeasure h
  letI := Q.isProbabilityMeasure_holdingTimeMeasure h
  have hreal_pos : 0 < μ.real (Set.Ioi δ) := by
    rw [Q.holdingTimeMeasure_real_Ioi_eq h hδ]
    exact Real.exp_pos _
  have hne : μ (Set.Ioi δ) ≠ 0 :=
    (MeasureTheory.measureReal_ne_zero_iff (by finiteness)).mp hreal_pos.ne'
  exact lt_of_le_of_ne (zero_le') (Ne.symm hne)

/-- One-step jump-hold law from a non-absorbing state: exponential holding
time paired independently with the embedded next-state row. -/
noncomputable def QMatrix.jumpHoldStepMeasure (Q : QMatrix S)
    [Countable S] [MeasurableSpace S] {s : S} (h : ¬Q.IsAbsorbing s) :
    MeasureTheory.Measure (ℝ × S) :=
  (Q.holdingTimeMeasure h).prod (Q.embeddedStepMeasure s)

/-- The one-step jump-hold law is a probability measure. -/
theorem QMatrix.isProbabilityMeasure_jumpHoldStepMeasure (Q : QMatrix S)
    [Countable S] [MeasurableSpace S] {s : S} (h : ¬Q.IsAbsorbing s) :
    MeasureTheory.IsProbabilityMeasure (Q.jumpHoldStepMeasure h) := by
  letI := Q.isProbabilityMeasure_holdingTimeMeasure h
  letI := Q.isProbabilityMeasure_embeddedStepMeasure s
  dsimp [jumpHoldStepMeasure]
  infer_instance

/-- The holding-time marginal of the non-absorbing one-step jump-hold law is
the exponential holding-time law. -/
theorem QMatrix.jumpHoldStepMeasure_map_fst (Q : QMatrix S)
    [Countable S] [MeasurableSpace S] {s : S} (h : ¬Q.IsAbsorbing s) :
    (Q.jumpHoldStepMeasure h).map Prod.fst = Q.holdingTimeMeasure h := by
  unfold jumpHoldStepMeasure
  letI := Q.isProbabilityMeasure_embeddedStepMeasure s
  simp

/-- The next-state marginal of the non-absorbing one-step jump-hold law is
the embedded jump-chain row measure. -/
theorem QMatrix.jumpHoldStepMeasure_map_snd (Q : QMatrix S)
    [Countable S] [MeasurableSpace S] {s : S} (h : ¬Q.IsAbsorbing s) :
    (Q.jumpHoldStepMeasure h).map Prod.snd = Q.embeddedStepMeasure s := by
  unfold jumpHoldStepMeasure
  letI := Q.isProbabilityMeasure_holdingTimeMeasure h
  simp

/-- The sampled holding time in a non-absorbing jump-hold step is positive
almost surely. -/
theorem QMatrix.jumpHoldStepMeasure_holdingTime_pos_ae (Q : QMatrix S)
    [Countable S] [MeasurableSpace S] {s : S} (h : ¬Q.IsAbsorbing s) :
    ∀ᵐ r ∂Q.jumpHoldStepMeasure h, 0 < r.1 := by
  have hpos := Q.holdingTimeMeasure_pos_ae h
  rw [← Q.jumpHoldStepMeasure_map_fst h] at hpos
  exact MeasureTheory.ae_of_ae_map measurable_fst.aemeasurable hpos

/-- The sampled next state in a non-absorbing jump-hold step differs from the
current state almost surely. -/
theorem QMatrix.jumpHoldStepMeasure_next_ne_self_ae (Q : QMatrix S)
    [Countable S] [MeasurableSpace S] [MeasurableSingletonClass S]
    {s : S} (h : ¬Q.IsAbsorbing s) :
    ∀ᵐ r ∂Q.jumpHoldStepMeasure h, r.2 ≠ s := by
  have hne := Q.embeddedStepMeasure_ne_self_ae_of_nonabsorbing h
  rw [← Q.jumpHoldStepMeasure_map_snd h] at hne
  exact MeasureTheory.ae_of_ae_map measurable_snd.aemeasurable hne

/-- In a non-absorbing jump-hold step, the sampled next state has positive
generator rate from the current state almost surely. -/
theorem QMatrix.jumpHoldStepMeasure_next_rate_pos_ae (Q : QMatrix S)
    [Countable S] [MeasurableSpace S] [MeasurableSingletonClass S]
    {s : S} (h : ¬Q.IsAbsorbing s) :
    ∀ᵐ r ∂Q.jumpHoldStepMeasure h, 0 < Q.rate s r.2 := by
  have hpos := Q.embeddedStepMeasure_rate_pos_ae_of_nonabsorbing h
  rw [← Q.jumpHoldStepMeasure_map_snd h] at hpos
  exact MeasureTheory.ae_of_ae_map measurable_snd.aemeasurable hpos

/-- Total one-step jump-hold law.  Non-absorbing states use the genuine
exponential-hold/jump product law; absorbing states are represented by the
terminal marker `(0, s)`. -/
noncomputable def QMatrix.jumpHoldStepMeasureTotal (Q : QMatrix S)
    [Countable S] [MeasurableSpace S] (s : S) : MeasureTheory.Measure (ℝ × S) :=
  by
    classical
    exact if h : Q.IsAbsorbing s then MeasureTheory.Measure.dirac (0, s)
      else Q.jumpHoldStepMeasure h

/-- At an absorbing state, the total one-step jump-hold law is the terminal
marker. -/
theorem QMatrix.jumpHoldStepMeasureTotal_of_absorbing (Q : QMatrix S)
    [Countable S] [MeasurableSpace S] {s : S} (h : Q.IsAbsorbing s) :
    Q.jumpHoldStepMeasureTotal s = MeasureTheory.Measure.dirac (0, s) := by
  classical
  simp [jumpHoldStepMeasureTotal, h]

/-- At a non-absorbing state, the total one-step jump-hold law is the genuine
one-step product law. -/
theorem QMatrix.jumpHoldStepMeasureTotal_of_nonabsorbing (Q : QMatrix S)
    [Countable S] [MeasurableSpace S] {s : S} (h : ¬Q.IsAbsorbing s) :
    Q.jumpHoldStepMeasureTotal s = Q.jumpHoldStepMeasure h := by
  classical
  simp [jumpHoldStepMeasureTotal, h]

/-- The total one-step jump-hold law is always a probability measure. -/
theorem QMatrix.isProbabilityMeasure_jumpHoldStepMeasureTotal (Q : QMatrix S)
    [Countable S] [MeasurableSpace S] (s : S) :
    MeasureTheory.IsProbabilityMeasure (Q.jumpHoldStepMeasureTotal s) := by
  by_cases h : Q.IsAbsorbing s
  · rw [Q.jumpHoldStepMeasureTotal_of_absorbing h]
    infer_instance
  · rw [Q.jumpHoldStepMeasureTotal_of_nonabsorbing h]
    exact Q.isProbabilityMeasure_jumpHoldStepMeasure h

/-- The total one-step jump-hold law as a Markov kernel from current state to
the next hold/jump record. -/
noncomputable def QMatrix.jumpHoldStepKernel (Q : QMatrix S)
    [Countable S] [MeasurableSpace S] [MeasurableSingletonClass S] :
    ProbabilityTheory.Kernel S (ℝ × S) where
  toFun s := Q.jumpHoldStepMeasureTotal s
  measurable' :=
    MeasureTheory.Measure.measurable_of_measurable_coe _ fun A _hA =>
      measurable_of_countable fun s => Q.jumpHoldStepMeasureTotal s A

/-- Applying the total jump-hold kernel recovers the total one-step law. -/
theorem QMatrix.jumpHoldStepKernel_apply (Q : QMatrix S)
    [Countable S] [MeasurableSpace S] [MeasurableSingletonClass S] (s : S) :
    Q.jumpHoldStepKernel s = Q.jumpHoldStepMeasureTotal s :=
  rfl

/-- The total jump-hold kernel is Markov. -/
theorem QMatrix.isMarkovKernel_jumpHoldStepKernel (Q : QMatrix S)
    [Countable S] [MeasurableSpace S] [MeasurableSingletonClass S] :
    ProbabilityTheory.IsMarkovKernel Q.jumpHoldStepKernel where
  isProbabilityMeasure s := Q.isProbabilityMeasure_jumpHoldStepMeasureTotal s

/-! ## Transition Semigroup -/

section TransitionSemigroup

attribute [local instance] Matrix.normedAddCommGroup

open NormedSpace in
/-- The transition matrix P(t) = exp(tQ).
For finite state spaces, this is a matrix exponential. -/
noncomputable def QMatrix.transitionProb (Q : QMatrix S) (t : ℝ) (s u : S) : ℝ :=
  exp (t • (Matrix.of Q.rate)) s u

/-- Kolmogorov forward equation: P'(t) = P(t)·Q.
The transition probabilities satisfy a system of linear ODEs.
Holds for all t ∈ ℝ (not just t ≥ 0) since exp is entire. -/
theorem QMatrix.kolmogorov_forward (Q : QMatrix S) (s u : S) :
    ∀ t ≥ 0, HasDerivAt (fun t => Q.transitionProb t s u)
      (∑ v, Q.transitionProb t s v * Q.rate v u) t := by
  intro t _ht
  open scoped Matrix.Norms.Operator in
  have hmat : HasDerivAt (fun t => exp (t • (Matrix.of Q.rate : Matrix S S ℝ)))
      (exp (t • (Matrix.of Q.rate : Matrix S S ℝ)) * Matrix.of Q.rate) t :=
    hasDerivAt_exp_smul_const (Matrix.of Q.rate) t
  have hrow := hasDerivAt_pi.mp hmat s
  have hentry := hasDerivAt_pi.mp hrow u
  simp only [transitionProb, Matrix.mul_apply, Matrix.of_apply] at hentry ⊢
  exact hentry

/-- Kolmogorov forward at any t (no t ≥ 0 restriction). -/
theorem QMatrix.kolmogorov_forward' (Q : QMatrix S) (s u : S) (t : ℝ) :
    HasDerivAt (fun t => Q.transitionProb t s u)
      (∑ v, Q.transitionProb t s v * Q.rate v u) t := by
  open scoped Matrix.Norms.Operator in
  have hmat := hasDerivAt_exp_smul_const (Matrix.of Q.rate : Matrix S S ℝ) t
  have hrow := hasDerivAt_pi.mp hmat s
  have hentry := hasDerivAt_pi.mp hrow u
  simp only [transitionProb, Matrix.mul_apply, Matrix.of_apply] at hentry ⊢
  exact hentry

/-- Kolmogorov backward at any t (no t ≥ 0 restriction). -/
theorem QMatrix.kolmogorov_backward' (Q : QMatrix S) (s u : S) (t : ℝ) :
    HasDerivAt (fun t => Q.transitionProb t s u)
      (∑ v, Q.rate s v * Q.transitionProb t v u) t := by
  open scoped Matrix.Norms.Operator in
  have hmat := hasDerivAt_exp_smul_const' (Matrix.of Q.rate : Matrix S S ℝ) t
  have hrow := hasDerivAt_pi.mp hmat s
  have hentry := hasDerivAt_pi.mp hrow u
  simp only [transitionProb, Matrix.mul_apply, Matrix.of_apply] at hentry ⊢
  exact hentry

/-- Q commutes with P(t): Q·P(t) = P(t)·Q entry-wise.
Follows from uniqueness of derivative: forward and backward give the same. -/
theorem QMatrix.commute_transitionProb (Q : QMatrix S) (s u : S) (t : ℝ) :
    ∑ v, Q.rate s v * Q.transitionProb t v u =
    ∑ v, Q.transitionProb t s v * Q.rate v u :=
  (Q.kolmogorov_backward' s u t).unique (Q.kolmogorov_forward' s u t)

/-- Kolmogorov backward equation: P'(t) = Q·P(t).
Equivalently, d/dt P(t)_{su} = ∑_v Q_{sv} · P(t)_{vu}. -/
theorem QMatrix.kolmogorov_backward (Q : QMatrix S) (s u : S) :
    ∀ t ≥ 0, HasDerivAt (fun t => Q.transitionProb t s u)
      (∑ v, Q.rate s v * Q.transitionProb t v u) t := by
  intro t _ht
  open scoped Matrix.Norms.Operator in
  have hmat : HasDerivAt (fun t => exp (t • (Matrix.of Q.rate : Matrix S S ℝ)))
      (Matrix.of Q.rate * exp (t • (Matrix.of Q.rate : Matrix S S ℝ))) t :=
    hasDerivAt_exp_smul_const' (Matrix.of Q.rate) t
  have hrow := hasDerivAt_pi.mp hmat s
  have hentry := hasDerivAt_pi.mp hrow u
  simp only [transitionProb, Matrix.mul_apply, Matrix.of_apply] at hentry ⊢
  exact hentry

/-- P(0) = I: at time zero, the transition matrix is the identity.
Follows from exp(0) = 1. -/
theorem QMatrix.transitionProb_zero (Q : QMatrix S) (s u : S) :
    Q.transitionProb 0 s u = if s = u then 1 else 0 := by
  simp only [transitionProb, zero_smul]
  open scoped Matrix.Norms.Operator in
  rw [exp_zero]
  simp [Matrix.one_apply]

/-- P'(0) = Q: the derivative of P(t) at t=0 is the generator.
This is the defining relationship between P(t) and Q. -/
theorem QMatrix.transitionProb_deriv_zero (Q : QMatrix S) (s u : S) :
    HasDerivAt (fun t => Q.transitionProb t s u) (Q.rate s u) 0 := by
  have h := Q.kolmogorov_backward' s u 0
  have : ∑ v, Q.rate s v * Q.transitionProb 0 v u = Q.rate s u := by
    simp only [Q.transitionProb_zero]
    rw [Finset.sum_eq_single u]
    · simp
    · intro v _ hvu; simp [hvu]
    · intro h; exact absurd (Finset.mem_univ u) h
  rwa [this] at h

/-- The semigroup property: P(s+t) = P(s) · P(t).
Follows from exp((s+t)Q) = exp(sQ) · exp(tQ) since sQ and tQ commute. -/
theorem QMatrix.transitionProb_add (Q : QMatrix S) (s t : ℝ) (x y : S) :
    Q.transitionProb (s + t) x y =
      ∑ z, Q.transitionProb s x z * Q.transitionProb t z y := by
  simp only [transitionProb, add_smul]
  open scoped Matrix.Norms.Operator in
  have hcomm : Commute (s • Matrix.of Q.rate) (t • Matrix.of Q.rate) :=
    (Commute.refl (Matrix.of Q.rate)).smul_right t |>.smul_left s
  have hexp : NormedSpace.exp (s • Matrix.of Q.rate + t • Matrix.of Q.rate)
      = NormedSpace.exp (s • Matrix.of Q.rate) * NormedSpace.exp (t • Matrix.of Q.rate) :=
    exp_add_of_commute hcomm
  rw [hexp]
  simp [Matrix.mul_apply]

/-- Row sums of P(t) are 1: the transition matrix is stochastic.
Proof: f(t) = ∑_u P(t)(s,u) has f'(t) = 0 (by Kolmogorov forward + row_sum_zero)
and f(0) = 1 (by transitionProb_zero). -/
theorem QMatrix.transitionProb_row_sum (Q : QMatrix S) (s : S) (t : ℝ) :
    ∑ u, Q.transitionProb t s u = 1 := by
  have hderiv : ∀ t₀ : ℝ, HasDerivAt (fun t => ∑ u, Q.transitionProb t s u) 0 t₀ := by
    intro t₀
    have hsum := HasDerivAt.sum (u := Finset.univ) fun u _hu =>
      Q.kolmogorov_forward' s u t₀
    simp only [Finset.sum_comm (f := fun u v => Q.transitionProb t₀ s v * Q.rate v u)] at hsum
    simp only [← Finset.mul_sum, Q.row_sum_zero, mul_zero, Finset.sum_const_zero] at hsum
    convert hsum using 1
    ext t₁
    exact (Finset.sum_apply t₁ Finset.univ (fun u t => Q.transitionProb t s u)).symm
  have hdiff : Differentiable ℝ (fun t => ∑ u, Q.transitionProb t s u) :=
    fun t₀ => (hderiv t₀).differentiableAt
  have hconst := is_const_of_deriv_eq_zero hdiff
    (fun t₀ => (hderiv t₀).deriv)
  have hat0 : ∑ u, Q.transitionProb 0 s u = 1 := by
    simp [Q.transitionProb_zero]
  linarith [hconst t 0]

/-- P(t)(s,u) is differentiable in t. -/
theorem QMatrix.transitionProb_differentiable (Q : QMatrix S) (s u : S) :
    Differentiable ℝ (fun t => Q.transitionProb t s u) :=
  fun t => (Q.kolmogorov_forward' s u t).differentiableAt

/-- P(t)(s,u) is continuous in t. -/
theorem QMatrix.transitionProb_continuous (Q : QMatrix S) (s u : S) :
    Continuous (fun t => Q.transitionProb t s u) :=
  (Q.transitionProb_differentiable s u).continuous

/-- Each row of P(t) is continuous in t. -/
theorem QMatrix.transitionProb_continuous_row (Q : QMatrix S) (s : S) :
    Continuous (fun t => fun u => Q.transitionProb t s u) :=
  continuous_pi (fun u => Q.transitionProb_continuous s u)

/-- P(t) is invertible (exp of any element is a unit). -/
theorem QMatrix.transitionProb_isUnit (Q : QMatrix S) (t : ℝ) :
    IsUnit (NormedSpace.exp (t • (Matrix.of Q.rate : Matrix S S ℝ))) := by
  open scoped Matrix.Norms.Operator in
  exact Matrix.isUnit_exp _

/-- P(-t) = P(t)⁻¹: the inverse of the transition matrix is P at negative time. -/
theorem QMatrix.transitionProb_neg (Q : QMatrix S) (t : ℝ) :
    NormedSpace.exp ((-t) • (Matrix.of Q.rate : Matrix S S ℝ)) =
      (NormedSpace.exp (t • (Matrix.of Q.rate : Matrix S S ℝ)))⁻¹ := by
  open scoped Matrix.Norms.Operator in
  rw [neg_smul]
  exact Matrix.exp_neg _

/-- The derivative of P(t)(s,u) at any time t₀ in terms of the forward equation. -/
theorem QMatrix.transitionProb_deriv (Q : QMatrix S) (s u : S) (t : ℝ) :
    deriv (fun t => Q.transitionProb t s u) t =
      ∑ v, Q.transitionProb t s v * Q.rate v u :=
  (Q.kolmogorov_forward' s u t).deriv

/-- Linear approximation: P(t)(s,u) = δ_{su} + t·Q(s,u) + o(t) as t → 0.
This is the formal statement that P(t) = I + tQ + o(t). -/
theorem QMatrix.transitionProb_linearApprox (Q : QMatrix S) (s u : S) :
    (fun t => Q.transitionProb t s u - (if s = u then 1 else 0) - t * Q.rate s u) =o[nhds 0]
      fun t => t := by
  have hderiv := Q.transitionProb_deriv_zero s u
  rw [hasDerivAt_iff_isLittleO_nhds_zero] at hderiv
  simp only [Q.transitionProb_zero] at hderiv
  convert hderiv using 1
  ext t; simp [smul_eq_mul]

/-- P(t) at t = 0 for diagonal: P(0)(s,s) = 1. -/
theorem QMatrix.transitionProb_zero_diag (Q : QMatrix S) (s : S) :
    Q.transitionProb 0 s s = 1 := by
  simp [Q.transitionProb_zero]

/-- P(t) at t = 0 for off-diagonal: P(0)(s,u) = 0 when s ≠ u. -/
theorem QMatrix.transitionProb_zero_offdiag (Q : QMatrix S) (s u : S) (hne : s ≠ u) :
    Q.transitionProb 0 s u = 0 := by
  simp [Q.transitionProb_zero, hne]

/-- For small t, the diagonal P(t)(s,s) is close to 1, hence positive.
P(t)(s,s) > 0 for all t in some neighborhood of 0. -/
theorem QMatrix.transitionProb_diag_eventually_pos (Q : QMatrix S) (s : S) :
    ∀ᶠ t in nhds (0 : ℝ), 0 < Q.transitionProb t s s := by
  have hcont := Q.transitionProb_continuous s s
  have h0 := Q.transitionProb_zero_diag s
  have hmem : Set.Ioi (0 : ℝ) ∈ nhds (Q.transitionProb 0 s s) := by
    rw [h0]; exact Ioi_mem_nhds one_pos
  exact hcont.continuousAt.preimage_mem_nhds hmem

/-- Off-diagonal: if Q(s,u) > 0 (direct transition exists), then
P(t)(s,u) > 0 for all sufficiently small t > 0.
Follows from P(0)(s,u) = 0 and P'(0)(s,u) = Q(s,u) > 0 via isLittleO. -/
theorem QMatrix.transitionProb_pos_of_rate_pos (Q : QMatrix S) {s u : S} (hne : s ≠ u)
    (hrate : 0 < Q.rate s u) :
    ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < Q.transitionProb t s u := by
  have hderiv := Q.transitionProb_deriv_zero s u
  have h0 : Q.transitionProb 0 s u = 0 := Q.transitionProb_zero_offdiag s u hne
  rw [hasDerivAt_iff_isLittleO_nhds_zero] at hderiv
  simp only [zero_add, h0, sub_zero, smul_eq_mul] at hderiv
  filter_upwards [self_mem_nhdsWithin,
    (hderiv.bound (half_pos hrate)).filter_mono nhdsWithin_le_nhds] with t ht_pos ht
  have ht_pos' : (0 : ℝ) < t := ht_pos
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos ht_pos'] at ht
  nlinarith [(abs_le.mp ht).1, mul_pos (half_pos hrate) ht_pos']

end TransitionSemigroup

/-! ## Stationary Distributions -/

/-- A distribution π on S (nonneg, sums to 1). -/
structure Distribution (S : Type*) [Fintype S] where
  prob : S → ℝ
  nonneg : ∀ s, 0 ≤ prob s
  sum_one : ∑ s, prob s = 1

/-- π is a stationary distribution if πQ = 0 (equivalently, ∑_s π(s)·q(s,t) = 0 for all t). -/
def QMatrix.IsStationary (Q : QMatrix S) (π : Distribution S) : Prop :=
  ∀ t, ∑ s, π.prob s * Q.rate s t = 0

/-- Detailed balance: π(s)·q(s,t) = π(t)·q(t,s) for all s ≠ t. -/
def QMatrix.DetailedBalance (Q : QMatrix S) (π : Distribution S) : Prop :=
  ∀ s t, s ≠ t → π.prob s * Q.rate s t = π.prob t * Q.rate t s

/-- Detailed balance implies stationarity. -/
theorem QMatrix.DetailedBalance.isStationary (Q : QMatrix S) (π : Distribution S)
    (hdb : Q.DetailedBalance π) : Q.IsStationary π := by
  intro t
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ t)]
  have hdiag : π.prob t * Q.rate t t = -∑ s ∈ Finset.univ.erase t, π.prob t * Q.rate t s := by
    rw [Q.diag_eq_neg_exitRate, exitRate, ← Finset.filter_ne']
    ring_nf
    rw [Finset.mul_sum]
  rw [hdiag]
  have hbal : ∑ s ∈ Finset.univ.erase t, π.prob s * Q.rate s t =
      ∑ s ∈ Finset.univ.erase t, π.prob t * Q.rate t s := by
    apply Finset.sum_congr rfl
    intro s hs
    exact hdb s t (Finset.ne_of_mem_erase hs)
  linarith

attribute [local instance] Matrix.normedAddCommGroup

/-- If π is stationary (πQ = 0), then πP(t) = π:
∑_s π(s) P(t)(s,u) = π(u) for all u, t.
Proof: g(t) = ∑_s π(s) P(t)(s,u) has g'(t) = 0 (by Kolmogorov backward + πQ=0)
and g(0) = π(u) (by P(0) = I). -/
theorem QMatrix.IsStationary.preservedByTransition (Q : QMatrix S) (π : Distribution S)
    (hstat : Q.IsStationary π) (u : S) (t : ℝ) :
    ∑ s, π.prob s * Q.transitionProb t s u = π.prob u := by
  have hderiv : ∀ t₀ : ℝ, HasDerivAt
      (fun t => ∑ s, π.prob s * Q.transitionProb t s u) 0 t₀ := by
    intro t₀
    have hentry : ∀ s, HasDerivAt (fun t => π.prob s * Q.transitionProb t s u)
        (π.prob s * ∑ v, Q.rate s v * Q.transitionProb t₀ v u) t₀ := by
      intro s
      have := (hasDerivAt_const t₀ (π.prob s)).mul (Q.kolmogorov_backward' s u t₀)
      simp only [zero_mul, zero_add] at this
      exact this
    have hsum := HasDerivAt.sum fun s (_ : s ∈ Finset.univ) => hentry s
    have key : ∑ s, π.prob s * ∑ v, Q.rate s v * Q.transitionProb t₀ v u = 0 := by
      calc ∑ s, π.prob s * ∑ v, Q.rate s v * Q.transitionProb t₀ v u
          = ∑ s, ∑ v, π.prob s * (Q.rate s v * Q.transitionProb t₀ v u) := by
            congr 1; ext s; rw [Finset.mul_sum]
        _ = ∑ v, ∑ s, π.prob s * (Q.rate s v * Q.transitionProb t₀ v u) :=
            Finset.sum_comm
        _ = ∑ v, (∑ s, π.prob s * Q.rate s v) * Q.transitionProb t₀ v u := by
            congr 1; ext v; rw [Finset.sum_mul]; congr 1; ext s; ring
        _ = 0 := by
            apply Finset.sum_eq_zero; intro v _
            rw [hstat v, zero_mul]
    rw [key] at hsum
    convert hsum using 1
    ext t₁
    exact (Finset.sum_apply t₁ Finset.univ
      (fun s t => π.prob s * Q.transitionProb t s u)).symm
  have hdiff : Differentiable ℝ (fun t => ∑ s, π.prob s * Q.transitionProb t s u) :=
    fun t₀ => (hderiv t₀).differentiableAt
  have hconst := is_const_of_deriv_eq_zero hdiff (fun t₀ => (hderiv t₀).deriv)
  have hat0 : ∑ s, π.prob s * Q.transitionProb 0 s u = π.prob u := by
    simp [Q.transitionProb_zero, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ]
  linarith [hconst t 0]

/-! ## Uniformization -/

section Uniformization

variable [Nonempty S]
attribute [local instance] Matrix.normedAddCommGroup

/-- The uniformization rate: maximum exit rate over all states. -/
noncomputable def QMatrix.uniformRate (Q : QMatrix S) : ℝ :=
  Finset.univ.sup' ⟨Classical.arbitrary S, Finset.mem_univ _⟩ Q.exitRate

/-- The uniformization rate bounds all exit rates. -/
theorem QMatrix.exitRate_le_uniformRate (Q : QMatrix S) (s : S) :
    Q.exitRate s ≤ Q.uniformRate := by
  exact Finset.le_sup' Q.exitRate (Finset.mem_univ s)

/-- The uniformization rate gives a state-uniform lower bound on
non-absorbing exponential holding-time tails. -/
theorem QMatrix.holdingTimeMeasure_real_Ioi_ge_uniformRate
    (Q : QMatrix S) {s : S} (h : ¬Q.IsAbsorbing s) {δ : ℝ} (hδ : 0 ≤ δ) :
    Real.exp (-(Q.uniformRate * δ)) ≤
      (Q.holdingTimeMeasure h).real (Set.Ioi δ) := by
  rw [Q.holdingTimeMeasure_real_Ioi_eq h hδ]
  exact Real.exp_le_exp.mpr
    (neg_le_neg (mul_le_mul_of_nonneg_right (Q.exitRate_le_uniformRate s) hδ))

/-- The uniformized transition matrix: U = I + Q/λ.
This has nonneg entries when λ ≥ max exit rate. -/
noncomputable def QMatrix.uniformizedMatrix (Q : QMatrix S) (uRate : ℝ) : S → S → ℝ :=
  fun s t => (if s = t then 1 else 0) + Q.rate s t / uRate

/-- Diagonal entries of the uniformized matrix are in [0,1] when λ ≥ uniformRate > 0. -/
theorem QMatrix.uniformizedMatrix_diag_nonneg (Q : QMatrix S) {uRate : ℝ} (hpos : 0 < uRate)
    (hge : Q.uniformRate ≤ uRate) (s : S) :
    0 ≤ Q.uniformizedMatrix uRate s s := by
  unfold uniformizedMatrix
  simp only [ite_true]
  rw [Q.diag_eq_neg_exitRate, neg_div]
  have h1 : Q.exitRate s / uRate ≤ 1 :=
    (div_le_one hpos).mpr (le_trans (Q.exitRate_le_uniformRate s) hge)
  linarith

omit [Nonempty S] in
/-- Off-diagonal entries of the uniformized matrix are nonneg when λ > 0. -/
theorem QMatrix.uniformizedMatrix_offdiag_nonneg (Q : QMatrix S) {uRate : ℝ} (hpos : 0 < uRate)
    (s t : S) (hst : s ≠ t) :
    0 ≤ Q.uniformizedMatrix uRate s t := by
  simp only [uniformizedMatrix, if_neg hst, zero_add]
  exact div_nonneg (Q.rate_nonneg s t hst) (le_of_lt hpos)

omit [Nonempty S] in
/-- Row sums of the uniformized matrix equal 1. -/
theorem QMatrix.uniformizedMatrix_row_sum (Q : QMatrix S) (uRate : ℝ)
    (s : S) : ∑ t, Q.uniformizedMatrix uRate s t = 1 := by
  simp only [uniformizedMatrix]
  rw [Finset.sum_add_distrib, ← Finset.sum_div]
  simp [Q.row_sum_zero]

/-- All entries of the uniformized matrix are nonneg when uRate ≥ uniformRate > 0. -/
theorem QMatrix.uniformizedMatrix_nonneg (Q : QMatrix S) {uRate : ℝ} (hpos : 0 < uRate)
    (hge : Q.uniformRate ≤ uRate) (s t : S) :
    0 ≤ Q.uniformizedMatrix uRate s t := by
  by_cases h : s = t
  · subst h; exact Q.uniformizedMatrix_diag_nonneg hpos hge s
  · exact Q.uniformizedMatrix_offdiag_nonneg hpos s t h

end Uniformization

/-! ## Matrix Nonnegativity -/

omit [DecidableEq S] in
/-- Product of entry-wise nonneg matrices has nonneg entries. -/
theorem Matrix.mul_nonneg_entries {M N : Matrix S S ℝ}
    (hM : ∀ i j, 0 ≤ M i j) (hN : ∀ i j, 0 ≤ N i j) :
    ∀ i j, 0 ≤ (M * N) i j := by
  intro i j
  simp only [Matrix.mul_apply]
  exact Finset.sum_nonneg fun k _ => mul_nonneg (hM i k) (hN k j)

/-- Powers of entry-wise nonneg matrices have nonneg entries. -/
theorem Matrix.pow_nonneg_entries {M : Matrix S S ℝ} (hM : ∀ i j, 0 ≤ M i j) (n : ℕ) :
    ∀ i j, 0 ≤ (M ^ n) i j := by
  induction n with
  | zero =>
    intro i j; simp only [pow_zero, Matrix.one_apply]
    split <;> linarith
  | succ k ih =>
    rw [pow_succ]
    exact Matrix.mul_nonneg_entries ih hM

omit [Fintype S] [DecidableEq S] in
/-- Scalar multiple of nonneg matrix by nonneg scalar has nonneg entries. -/
theorem Matrix.smul_nonneg_entries {M : Matrix S S ℝ} (hM : ∀ i j, 0 ≤ M i j)
    {c : ℝ} (hc : 0 ≤ c) : ∀ i j, 0 ≤ (c • M) i j := by
  intro i j; simp only [Matrix.smul_apply, smul_eq_mul]; exact mul_nonneg hc (hM i j)

/-- exp of a nonneg matrix has nonneg entries.
Proof: exp(A) = Σ (n!)⁻¹ • A^n entry-wise (by HasSum.map with continuous entry evaluation),
each term has nonneg entries, and limits of nonneg sequences are nonneg. -/
theorem Matrix.exp_nonneg_entries [Nonempty S]
    {A : Matrix S S ℝ} (hA : ∀ i j, 0 ≤ A i j) (s u : S) :
    0 ≤ NormedSpace.exp A s u := by
  open scoped Matrix.Norms.Operator in
  have hsum := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) A
  have hentry : HasSum (fun n => ((n.factorial⁻¹ : ℝ) • A ^ n) s u)
      (NormedSpace.exp A s u) :=
    hsum.map (Matrix.entryAddMonoidHom ℝ s u) (continuous_apply_apply s u)
  rw [← hentry.tsum_eq]
  exact tsum_nonneg fun n => by
    simp only [Matrix.smul_apply, smul_eq_mul]
    exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg' n.factorial))
      (Matrix.pow_nonneg_entries hA n s u)

/-! ## Transition Probability Nonnegativity -/

section TransitionNonneg

variable [Nonempty S]
attribute [local instance] Matrix.normedAddCommGroup
open scoped Matrix.Norms.Operator

/-- P(t)(s,u) ≥ 0 for all t ≥ 0. The transition matrix is substochastic.
Proof via diagonal shift: tQ = M + cI where M = tQ + μtI has nonneg entries
and c = -μt. Then exp(tQ) = exp(M) · exp(cI) = e^c · exp(M), both factors nonneg. -/
theorem QMatrix.transitionProb_nonneg (Q : QMatrix S) (s u : S) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ Q.transitionProb t s u := by
  set μ := Q.uniformRate with hμ_def
  set Qm := (Matrix.of Q.rate : Matrix S S ℝ) with hQm
  set c := -(t * μ) with hc_def
  set M := t • Qm - c • (1 : Matrix S S ℝ) with hM_def
  -- M has nonneg entries
  have hM_nonneg : ∀ i j, 0 ≤ M i j := by
    intro i j
    simp only [hM_def, hc_def, Matrix.sub_apply, Matrix.smul_apply, hQm,
      Matrix.of_apply, Matrix.one_apply, smul_eq_mul, neg_mul]
    by_cases h : i = j
    · subst h
      rw [if_pos rfl, mul_one, Q.diag_eq_neg_exitRate]
      have := Q.exitRate_le_uniformRate i
      nlinarith
    · rw [if_neg h, mul_zero]; linarith [mul_nonneg ht (Q.rate_nonneg i j h)]
  -- tQ = M + c·I
  have hdecomp : t • Qm = M + c • (1 : Matrix S S ℝ) := by
    simp [hM_def, sub_add_cancel]
  have hcomm : Commute M (c • (1 : Matrix S S ℝ)) := by
    change M * (c • 1) = (c • 1) * M
    rw [mul_smul_comm, mul_one, smul_mul_assoc, one_mul]
  -- exp(tQ) = exp(M) · exp(c·I)
  have hexp : exp (t • Qm) = exp M * exp (c • (1 : Matrix S S ℝ)) := by
    rw [hdecomp]; exact exp_add_of_commute hcomm
  have hscalar : exp (c • (1 : Matrix S S ℝ)) =
      (Real.exp c) • (1 : Matrix S S ℝ) := by
    have h1 : c • (1 : Matrix S S ℝ) = Matrix.diagonal (fun _ => c) :=
      Matrix.smul_one_eq_diagonal c
    have h2 : NormedSpace.exp (fun _ : S => c) = fun _ : S => NormedSpace.exp c := by
      rw [show (fun _ : S => c) = algebraMap ℝ (S → ℝ) c from by
        ext; simp only [Algebra.algebraMap_eq_smul_one, Pi.smul_apply, Pi.one_apply,
          smul_eq_mul, mul_one]]
      rw [← NormedSpace.algebraMap_exp_comm]
      ext; simp only [Algebra.algebraMap_eq_smul_one, Pi.smul_apply, Pi.one_apply,
        smul_eq_mul, mul_one]
    rw [h1, Matrix.exp_diagonal, h2]
    ext i j; simp only [Matrix.diagonal_apply, Matrix.smul_apply, Matrix.one_apply,
      smul_eq_mul, ← Real.exp_eq_exp_ℝ]
    split <;> simp_all
  -- exp(tQ) = exp(c) • exp(M) — rearrange
  have hfinal : exp (t • Qm) s u = Real.exp c * (exp M s u) := by
    rw [hexp, hscalar, mul_smul_comm, mul_one]
    simp only [Matrix.smul_apply, smul_eq_mul]
  simp only [transitionProb]
  rw [hfinal]
  exact mul_nonneg (Real.exp_nonneg _) (Matrix.exp_nonneg_entries hM_nonneg s u)

/-- P(t)(s,u) ≤ 1 for all t ≥ 0.
Follows from row sums = 1, nonnegativity, and single term ≤ sum. -/
theorem QMatrix.transitionProb_le_one (Q : QMatrix S) (s u : S) {t : ℝ} (ht : 0 ≤ t) :
    Q.transitionProb t s u ≤ 1 := by
  have hrow := Q.transitionProb_row_sum s t
  have hnneg : ∀ v, 0 ≤ Q.transitionProb t s v := fun v => Q.transitionProb_nonneg s v ht
  calc Q.transitionProb t s u
      ≤ ∑ v, Q.transitionProb t s v :=
        Finset.single_le_sum (fun v _ => hnneg v) (Finset.mem_univ u)
    _ = 1 := hrow

/-- The transition matrix P(t) is (row) stochastic for t ≥ 0:
all entries are nonneg and each row sums to 1. -/
theorem QMatrix.transitionProb_stochastic (Q : QMatrix S) (s : S) {t : ℝ} (ht : 0 ≤ t) :
    (∀ u, 0 ≤ Q.transitionProb t s u) ∧ ∑ u, Q.transitionProb t s u = 1 :=
  ⟨fun u => Q.transitionProb_nonneg s u ht, Q.transitionProb_row_sum s t⟩

/-- P(t)(s,u) ∈ [0,1] for t ≥ 0. -/
theorem QMatrix.transitionProb_mem_Icc (Q : QMatrix S) (s u : S) {t : ℝ} (ht : 0 ≤ t) :
    Q.transitionProb t s u ∈ Set.Icc 0 1 :=
  ⟨Q.transitionProb_nonneg s u ht, Q.transitionProb_le_one s u ht⟩

omit [Nonempty S] in
/-- For non-absorbing state s, P(t)(s,s) < 1 for sufficiently small t > 0.
Mass flows to other states since Q(s,s) = -exitRate(s) < 0. -/
theorem QMatrix.transitionProb_diag_lt_one (Q : QMatrix S) {s : S}
    (hna : ¬Q.IsAbsorbing s) :
    ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), Q.transitionProb t s s < 1 := by
  have hderiv := Q.transitionProb_deriv_zero s s
  have hrate_neg : Q.rate s s < 0 := by
    rw [Q.diag_eq_neg_exitRate]
    exact neg_lt_zero.mpr (lt_of_le_of_ne (Q.exitRate_nonneg s) (Ne.symm hna))
  have h1 : Q.transitionProb 0 s s = 1 := Q.transitionProb_zero_diag s
  rw [hasDerivAt_iff_isLittleO_nhds_zero] at hderiv
  simp only [zero_add, h1, smul_eq_mul] at hderiv
  filter_upwards [self_mem_nhdsWithin,
    (hderiv.bound (show (0 : ℝ) < -Q.rate s s / 2 by linarith)).filter_mono
      nhdsWithin_le_nhds] with t ht_pos ht
  have ht_pos' : (0 : ℝ) < t := ht_pos
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos ht_pos'] at ht
  nlinarith [(abs_le.mp ht).2, mul_pos (show (0:ℝ) < -Q.rate s s / 2 by linarith) ht_pos']

end TransitionNonneg

/-! ## Irreducibility -/

/-- A CTMC is irreducible if P(t)(s,u) > 0 for all s, u and some t > 0. -/
def QMatrix.Irreducible (Q : QMatrix S) : Prop :=
  ∀ s u, ∃ t, 0 < t ∧ 0 < Q.transitionProb t s u

/-- An absorbing chain (all exit rates zero) has trivial transition: P(t) = I. -/
theorem QMatrix.transitionProb_of_all_absorbing (Q : QMatrix S)
    (hall : ∀ s, Q.IsAbsorbing s) (t : ℝ) (s u : S) :
    Q.transitionProb t s u = if s = u then 1 else 0 := by
  have hrate : Q.rate = fun _ _ => 0 := by
    ext x y
    by_cases h : x = y
    · rw [h, Q.diag_eq_neg_exitRate, hall y, neg_zero]
    · exact QMatrix.IsAbsorbing.rate_eq_zero Q (hall x) y h
  have : t • (Matrix.of Q.rate : Matrix S S ℝ) = 0 := by
    ext i j
    simp only [Matrix.smul_apply, Matrix.of_apply, hrate, smul_zero, Matrix.zero_apply]
  simp only [transitionProb, this]
  open scoped Matrix.Norms.Operator in
  rw [NormedSpace.exp_zero]
  simp [Matrix.one_apply]

/-- Direct transition rate positivity implies eventual transition probability positivity. -/
theorem QMatrix.irreducible_of_all_rates_pos (Q : QMatrix S)
    (hpos : ∀ s u, s ≠ u → 0 < Q.rate s u) : Q.Irreducible := by
  intro s u
  by_cases h : s = u
  · subst h
    have hcont := Q.transitionProb_continuous s s
    have h0 := Q.transitionProb_zero_diag s
    have hmem := hcont.continuousAt.preimage_mem_nhds
      (show Set.Ioi (0 : ℝ) ∈ nhds (Q.transitionProb 0 s s) by rw [h0]; exact Ioi_mem_nhds one_pos)
    obtain ⟨ε, hε_pos, hε_sub⟩ := Metric.mem_nhds_iff.mp hmem
    refine ⟨ε / 2, half_pos hε_pos, ?_⟩
    have hmem' : ε / 2 ∈ Metric.ball (0 : ℝ) ε :=
      Metric.mem_ball.mpr (by rw [dist_zero_right, Real.norm_eq_abs,
        abs_of_pos (half_pos hε_pos)]; linarith)
    exact hε_sub hmem'
  · have hderiv := Q.transitionProb_deriv_zero s u
    have h0 : Q.transitionProb 0 s u = 0 := Q.transitionProb_zero_offdiag s u h
    rw [hasDerivAt_iff_isLittleO_nhds_zero] at hderiv
    simp only [zero_add, h0, sub_zero, smul_eq_mul] at hderiv
    have hrate := hpos s u h
    obtain ⟨δ, hδ_pos, hδ_sub⟩ := Metric.eventually_nhds_iff.mp (hderiv.bound (half_pos hrate))
    refine ⟨δ / 2, half_pos hδ_pos, ?_⟩
    have hδ2 : (0 : ℝ) < δ / 2 := half_pos hδ_pos
    have hdist : dist (δ / 2) (0 : ℝ) < δ := by
      rw [dist_zero_right, Real.norm_eq_abs, abs_of_pos hδ2]; linarith
    have hbd := hδ_sub hdist
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hδ2] at hbd
    nlinarith [(abs_le.mp hbd).1, mul_pos (half_pos hrate) hδ2]

/-- Diagonal entry of exp(A) is ≥ 1 for entry-wise nonneg A.
The n=0 term of the series is I(s,s) = 1; all other terms are nonneg. -/
theorem Matrix.exp_diag_ge_one [Nonempty S]
    {A : Matrix S S ℝ} (hA : ∀ i j, 0 ≤ A i j) (s : S) :
    1 ≤ NormedSpace.exp A s s := by
  open scoped Matrix.Norms.Operator in
  have hsum := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) A
  have hentry : HasSum (fun n => ((n.factorial⁻¹ : ℝ) • A ^ n) s s)
      (NormedSpace.exp A s s) :=
    hsum.map (Matrix.entryAddMonoidHom ℝ s s) (continuous_apply_apply s s)
  set f := fun n => ((↑n.factorial : ℝ)⁻¹ • A ^ n) s s with hf_def
  have hnn : ∀ n, 0 ≤ f n := fun n => by
    simp only [hf_def, Matrix.smul_apply, smul_eq_mul]
    exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg' n.factorial))
      (Matrix.pow_nonneg_entries hA n s s)
  rw [← hentry.tsum_eq, hentry.summable.tsum_eq_zero_add]
  have hfirst : f 0 = 1 := by simp [hf_def]
  have htail : 0 ≤ ∑' n, f (n + 1) := tsum_nonneg fun n => hnn (n + 1)
  linarith

/-- P(t)(s,s) > 0 for all t ≥ 0 and all states s.
Via diagonal shift: P(t)(s,s) = e^{-μt} · exp(M)(s,s) where M is nonneg,
so exp(M)(s,s) ≥ 1 and e^{-μt} > 0. -/
theorem QMatrix.transitionProb_diag_pos (Q : QMatrix S) [Nonempty S]
    (s : S) {t : ℝ} (ht : 0 ≤ t) :
    0 < Q.transitionProb t s s := by
  set μ := Q.uniformRate with hμ_def
  set Qm := (Matrix.of Q.rate : Matrix S S ℝ) with hQm
  set c := -(t * μ) with hc_def
  set M := t • Qm - c • (1 : Matrix S S ℝ) with hM_def
  have hM_nonneg : ∀ i j, 0 ≤ M i j := by
    intro i j
    simp only [hM_def, hc_def, Matrix.sub_apply, Matrix.smul_apply, hQm,
      Matrix.of_apply, Matrix.one_apply, smul_eq_mul, neg_mul]
    by_cases h : i = j
    · subst h
      rw [if_pos rfl, mul_one, Q.diag_eq_neg_exitRate]
      have := Q.exitRate_le_uniformRate i
      nlinarith
    · rw [if_neg h, mul_zero]; linarith [mul_nonneg ht (Q.rate_nonneg i j h)]
  have hcomm : Commute M (c • (1 : Matrix S S ℝ)) := by
    change M * (c • 1) = (c • 1) * M
    rw [mul_smul_comm, mul_one, smul_mul_assoc, one_mul]
  open scoped Matrix.Norms.Operator in
  have hexp : exp (t • Qm) = exp M * exp (c • (1 : Matrix S S ℝ)) := by
    rw [show t • Qm = M + c • (1 : Matrix S S ℝ) from by simp [hM_def, sub_add_cancel]]
    exact exp_add_of_commute hcomm
  have hscalar : exp (c • (1 : Matrix S S ℝ)) =
      (Real.exp c) • (1 : Matrix S S ℝ) := by
    have h1 : c • (1 : Matrix S S ℝ) = Matrix.diagonal (fun _ => c) :=
      Matrix.smul_one_eq_diagonal c
    have h2 : NormedSpace.exp (fun _ : S => c) = fun _ : S => NormedSpace.exp c := by
      rw [show (fun _ : S => c) = algebraMap ℝ (S → ℝ) c from by
        ext; simp only [Algebra.algebraMap_eq_smul_one, Pi.smul_apply, Pi.one_apply,
          smul_eq_mul, mul_one]]
      rw [← NormedSpace.algebraMap_exp_comm]
      ext; simp only [Algebra.algebraMap_eq_smul_one, Pi.smul_apply, Pi.one_apply,
        smul_eq_mul, mul_one]
    rw [h1, Matrix.exp_diagonal, h2]
    ext i j; simp only [Matrix.diagonal_apply, Matrix.smul_apply, Matrix.one_apply,
      smul_eq_mul, ← Real.exp_eq_exp_ℝ]
    split <;> simp_all
  have hfinal : exp (t • Qm) s s = Real.exp c * (exp M s s) := by
    rw [hexp, hscalar, mul_smul_comm, mul_one]
    simp only [Matrix.smul_apply, smul_eq_mul]
  simp only [transitionProb]
  rw [hfinal]
  exact mul_pos (Real.exp_pos _) (lt_of_lt_of_le zero_lt_one (Matrix.exp_diag_ge_one hM_nonneg s))

/-! ## Ergodic Properties -/

attribute [local instance] Matrix.normedAddCommGroup

/-- Column sums of P(t) are 1: ∑_s P(t)(s,u) = Fintype.card S · average.
For the identity, this sum at t=0 equals 1 (only the s=u term). -/
theorem QMatrix.transitionProb_col_sum_at_zero (Q : QMatrix S) (u : S) :
    ∑ s, Q.transitionProb 0 s u = 1 := by
  simp [Q.transitionProb_zero, Finset.sum_ite_eq', Finset.mem_univ]

/-- Symmetry: Q is reversible w.r.t. π if and only if detailed balance holds.
This is a definitional equivalence. -/
theorem QMatrix.reversible_iff_detailedBalance (Q : QMatrix S) (π : Distribution S) :
    Q.DetailedBalance π ↔ ∀ s t, s ≠ t → π.prob s * Q.rate s t = π.prob t * Q.rate t s :=
  Iff.rfl

/-- Semigroup iteration: P(nt) = P(t)^n. -/
theorem QMatrix.transitionProb_nsmul (Q : QMatrix S) (n : ℕ) (t : ℝ) (s u : S) :
    Q.transitionProb (n * t) s u =
      (NormedSpace.exp (t • (Matrix.of Q.rate : Matrix S S ℝ)) ^ n) s u := by
  simp only [transitionProb]
  have : (↑n * t) • (Matrix.of Q.rate : Matrix S S ℝ) = n • (t • Matrix.of Q.rate) := by
    induction n with
    | zero => simp
    | succ k ih =>
      push_cast
      rw [add_mul, one_mul, add_smul, ih, add_smul, one_smul, add_comm]
  rw [this]
  open scoped Matrix.Norms.Operator in
  rw [Matrix.exp_nsmul]

/-! ## Time-Reversed Q-Matrix -/

/-- The time-reversed Q-matrix with respect to a positive stationary distribution π.
Q̃(s,t) = π(t)/π(s) · Q(t,s) for s ≠ t. Requires stationarity so that
the diagonal entries are well-defined (equal -exitRate). -/
noncomputable def QMatrix.timeReverse (Q : QMatrix S) (π : Distribution S)
    (hpos : ∀ s, 0 < π.prob s) (_hstat : Q.IsStationary π) : QMatrix S where
  rate s t :=
    if s = t then -∑ u ∈ Finset.univ.filter (· ≠ s), π.prob u / π.prob s * Q.rate u s
    else π.prob t / π.prob s * Q.rate t s
  rate_nonneg := by
    intro s t hst
    simp only [if_neg hst]
    apply mul_nonneg
    · exact div_nonneg (le_of_lt (hpos t)) (le_of_lt (hpos s))
    · exact Q.rate_nonneg t s (Ne.symm hst)
  rate_diag := by
    intro s
    simp only [ite_true]
    congr 1; apply Finset.sum_congr rfl; intro t ht
    have : ¬(s = t) := (Finset.mem_filter.mp ht).2.symm
    simp only [if_neg this]

/-- The time-reversed Q-matrix has the same exit rates as the original
when π is a positive stationary distribution. -/
theorem QMatrix.timeReverse_exitRate (Q : QMatrix S) (π : Distribution S)
    (hpos : ∀ s, 0 < π.prob s) (hstat : Q.IsStationary π) (s : S) :
    (Q.timeReverse π hpos hstat).exitRate s = Q.exitRate s := by
  simp only [exitRate, timeReverse]
  have step1 : ∀ t ∈ Finset.univ.filter (· ≠ s),
      (if s = t then -∑ u ∈ Finset.univ.filter (· ≠ s), π.prob u / π.prob s * Q.rate u s
       else π.prob t / π.prob s * Q.rate t s) =
      π.prob t / π.prob s * Q.rate t s := by
    intro t ht
    exact if_neg (Finset.mem_filter.mp ht).2.symm
  rw [Finset.sum_congr rfl step1]
  have hπs : π.prob s ≠ 0 := ne_of_gt (hpos s)
  have key : ∑ t ∈ Finset.univ.filter (· ≠ s), π.prob t * Q.rate t s =
      π.prob s * Q.exitRate s := by
    have := hstat s
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ s)] at this
    rw [Q.diag_eq_neg_exitRate, ← Finset.filter_ne'] at this
    linarith
  have step2 : ∑ t ∈ Finset.univ.filter (· ≠ s), π.prob t / π.prob s * Q.rate t s =
      (∑ t ∈ Finset.univ.filter (· ≠ s), π.prob t * Q.rate t s) / π.prob s := by
    rw [Finset.sum_div]
    congr 1; ext t; ring
  rw [step2, key, mul_div_cancel_left₀ _ hπs]; rfl

/-- Under detailed balance, the time-reversed Q-matrix equals the original. -/
theorem QMatrix.timeReverse_eq_of_detailedBalance (Q : QMatrix S) (π : Distribution S)
    (hpos : ∀ s, 0 < π.prob s) (hdb : Q.DetailedBalance π) :
    (Q.timeReverse π hpos (hdb.isStationary Q π)).rate = Q.rate := by
  ext s t
  by_cases h : s = t
  · subst h
    simp only [timeReverse, ite_true]
    rw [Q.diag_eq_neg_exitRate, exitRate]
    congr 1
    apply Finset.sum_congr rfl
    intro u hu
    have hne : u ≠ s := (Finset.mem_filter.mp hu).2
    have hdb' := hdb u s hne
    have hπs : π.prob s ≠ 0 := ne_of_gt (hpos s)
    field_simp
    linarith
  · simp only [timeReverse, if_neg h]
    have hπs : π.prob s ≠ 0 := ne_of_gt (hpos s)
    have hdb' := hdb t s (Ne.symm h)
    field_simp
    linarith

/-! ## Uniqueness: Q is determined by P(t) -/

/-- The Q-matrix is the derivative of P(t) at t=0.
Two Q-matrices giving the same semigroup must be equal. -/
theorem QMatrix.eq_of_transitionProb_eq (Q₁ Q₂ : QMatrix S)
    (h : ∀ t s u, Q₁.transitionProb t s u = Q₂.transitionProb t s u) :
    Q₁.rate = Q₂.rate := by
  ext s u
  have h1 := Q₁.transitionProb_deriv_zero s u
  have h2 := Q₂.transitionProb_deriv_zero s u
  rw [show (fun t => Q₁.transitionProb t s u) = (fun t => Q₂.transitionProb t s u) from
    funext (fun t => h t s u)] at h1
  exact h1.unique h2

/-! ## Absorbing State Transitions -/

attribute [local instance] Matrix.normedAddCommGroup

/-- For an absorbing state s, P(t)(s,u) = δ_{su} for all t.
The s-th row of Q is all zeros, so by Kolmogorov backward P'(t)(s,·) = 0,
hence P(t)(s,·) = P(0)(s,·) = I(s,·). -/
theorem QMatrix.transitionProb_absorbing (Q : QMatrix S) {s : S} (h : Q.IsAbsorbing s)
    (u : S) (t : ℝ) : Q.transitionProb t s u = if s = u then 1 else 0 := by
  have hrow : ∀ v, Q.rate s v = 0 := by
    intro v
    by_cases hv : s = v
    · subst hv; rw [Q.diag_eq_neg_exitRate, h, neg_zero]
    · exact QMatrix.IsAbsorbing.rate_eq_zero Q h v hv
  have hderiv : ∀ t₀, HasDerivAt (fun t => Q.transitionProb t s u) 0 t₀ := by
    intro t₀
    have hkb := Q.kolmogorov_backward' s u t₀
    simp only [hrow, zero_mul, Finset.sum_const_zero] at hkb
    exact hkb
  have hdiff : Differentiable ℝ (fun t => Q.transitionProb t s u) :=
    fun t₀ => (hderiv t₀).differentiableAt
  have hconst := is_const_of_deriv_eq_zero hdiff (fun t₀ => (hderiv t₀).deriv)
  linarith [hconst t 0, Q.transitionProb_zero s u]

/-- An absorbing state stays put: P(t)(s,s) = 1 for all t. -/
theorem QMatrix.transitionProb_absorbing_diag (Q : QMatrix S) {s : S}
    (h : Q.IsAbsorbing s) (t : ℝ) : Q.transitionProb t s s = 1 := by
  rw [Q.transitionProb_absorbing h s t, if_pos rfl]

/-- An absorbing state has zero off-diagonal transition: P(t)(s,u) = 0 for u ≠ s. -/
theorem QMatrix.transitionProb_absorbing_offdiag (Q : QMatrix S) {s u : S}
    (h : Q.IsAbsorbing s) (hne : s ≠ u) (t : ℝ) : Q.transitionProb t s u = 0 := by
  rw [Q.transitionProb_absorbing h u t, if_neg hne]

/-! ## CTMC Reachability -/

/-- State u is reachable from s if P(t)(s,u) > 0 for some t > 0. -/
def QMatrix.Reachable (Q : QMatrix S) (s u : S) : Prop :=
  ∃ t, 0 < t ∧ 0 < Q.transitionProb t s u

/-- Reachability is reflexive: every state reaches itself via P(0)(s,s) = 1.
In fact P(t)(s,s) > 0 for all t > 0 (by transitionProb_diag_pos). -/
theorem QMatrix.reachable_self [Nonempty S] (Q : QMatrix S) (s : S) :
    Q.Reachable s s := by
  exact ⟨1, one_pos, Q.transitionProb_diag_pos s (le_of_lt one_pos)⟩

/-- Direct transition rate > 0 implies reachability. -/
theorem QMatrix.reachable_of_rate_pos (Q : QMatrix S) {s u : S} (hne : s ≠ u)
    (hrate : 0 < Q.rate s u) : Q.Reachable s u := by
  have hderiv := Q.transitionProb_deriv_zero s u
  have h0 : Q.transitionProb 0 s u = 0 := Q.transitionProb_zero_offdiag s u hne
  rw [hasDerivAt_iff_isLittleO_nhds_zero] at hderiv
  simp only [zero_add, h0, sub_zero, smul_eq_mul] at hderiv
  obtain ⟨δ, hδ_pos, hδ_sub⟩ := Metric.eventually_nhds_iff.mp (hderiv.bound (half_pos hrate))
  refine ⟨δ / 2, half_pos hδ_pos, ?_⟩
  have hδ2 : (0 : ℝ) < δ / 2 := half_pos hδ_pos
  have hdist : dist (δ / 2) (0 : ℝ) < δ := by
    rw [dist_zero_right, Real.norm_eq_abs, abs_of_pos hδ2]; linarith
  have hbd := hδ_sub hdist
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hδ2] at hbd
  nlinarith [(abs_le.mp hbd).1, mul_pos (half_pos hrate) hδ2]

/-- Reachability is transitive: s → u and u → w implies s → w.
Via Chapman-Kolmogorov: P(s₁+s₂)(s,w) = ∑_v P(s₁)(s,v) P(s₂)(v,w) ≥ P(s₁)(s,u) P(s₂)(u,w). -/
theorem QMatrix.reachable_trans [Nonempty S] (Q : QMatrix S) {s u w : S}
    (hsu : Q.Reachable s u) (huw : Q.Reachable u w) : Q.Reachable s w := by
  obtain ⟨t₁, ht₁_pos, ht₁⟩ := hsu
  obtain ⟨t₂, ht₂_pos, ht₂⟩ := huw
  refine ⟨t₁ + t₂, add_pos ht₁_pos ht₂_pos, ?_⟩
  rw [Q.transitionProb_add t₁ t₂ s w]
  calc 0 < Q.transitionProb t₁ s u * Q.transitionProb t₂ u w :=
          mul_pos ht₁ ht₂
    _ ≤ ∑ z, Q.transitionProb t₁ s z * Q.transitionProb t₂ z w :=
          Finset.single_le_sum
            (fun z _ => mul_nonneg
              (Q.transitionProb_nonneg s z (le_of_lt ht₁_pos))
              (Q.transitionProb_nonneg z w (le_of_lt ht₂_pos)))
            (Finset.mem_univ u)

/-- Communication: two states communicate if each is reachable from the other. -/
def QMatrix.Communicates (Q : QMatrix S) (s u : S) : Prop :=
  Q.Reachable s u ∧ Q.Reachable u s

/-- Communication is symmetric. -/
theorem QMatrix.communicates_symm (Q : QMatrix S) {s u : S}
    (h : Q.Communicates s u) : Q.Communicates u s :=
  ⟨h.2, h.1⟩

/-- Communication is reflexive for nonempty state space. -/
theorem QMatrix.communicates_refl [Nonempty S] (Q : QMatrix S) (s : S) :
    Q.Communicates s s :=
  ⟨Q.reachable_self s, Q.reachable_self s⟩

/-- Communication is transitive. -/
theorem QMatrix.communicates_trans [Nonempty S] (Q : QMatrix S) {s u w : S}
    (hsu : Q.Communicates s u) (huw : Q.Communicates u w) :
    Q.Communicates s w :=
  ⟨Q.reachable_trans hsu.1 huw.1, Q.reachable_trans huw.2 hsu.2⟩

/-- Irreducible ↔ all states communicate. -/
theorem QMatrix.irreducible_iff_communicates [Nonempty S] (Q : QMatrix S) :
    Q.Irreducible ↔ ∀ s u, Q.Communicates s u := by
  constructor
  · intro hirr s u
    exact ⟨hirr s u, hirr u s⟩
  · intro hcomm s u
    exact (hcomm s u).1

/-- Irreducible chains have positive transition probabilities between any pair. -/
theorem QMatrix.Irreducible.reachable (Q : QMatrix S) (hirr : Q.Irreducible) (s u : S) :
    Q.Reachable s u :=
  hirr s u

/-- An absorbing state is not reachable from a different state in an irreducible chain.
Contrapositively: irreducible chains with ≥ 2 states have no absorbing states. -/
theorem QMatrix.Irreducible.not_absorbing [Nonempty S] (Q : QMatrix S)
    (hirr : Q.Irreducible) {s : S} (hs : Q.IsAbsorbing s)
    {u : S} (hne : u ≠ s) : False := by
  obtain ⟨t, ht_pos, ht⟩ := hirr s u
  have := Q.transitionProb_absorbing_offdiag hs hne.symm t
  linarith

/-! ## Diagonal Exponential Bound -/

/-- P(t)(s,s) ≥ exp(-μ · t) for t ≥ 0, where μ is the uniform rate.
The diagonal shift gives P(t)(s,s) = exp(-μt) · exp(M)(s,s) with exp(M)(s,s) ≥ 1. -/
theorem QMatrix.transitionProb_diag_lower_bound [Nonempty S]
    (Q : QMatrix S) (s : S) {t : ℝ} (ht : 0 ≤ t) :
    Real.exp (-(Q.uniformRate) * t) ≤ Q.transitionProb t s s := by
  set μ := Q.uniformRate with hμ_def
  set Qm := (Matrix.of Q.rate : Matrix S S ℝ) with hQm
  set c := -(t * μ) with hc_def
  set M := t • Qm - c • (1 : Matrix S S ℝ) with hM_def
  have hM_nonneg : ∀ i j, 0 ≤ M i j := by
    intro i j
    simp only [hM_def, hc_def, Matrix.sub_apply, Matrix.smul_apply, hQm,
      Matrix.of_apply, Matrix.one_apply, smul_eq_mul, neg_mul]
    by_cases h : i = j
    · subst h
      rw [if_pos rfl, mul_one, Q.diag_eq_neg_exitRate]
      have := Q.exitRate_le_uniformRate i
      nlinarith
    · rw [if_neg h, mul_zero]; linarith [mul_nonneg ht (Q.rate_nonneg i j h)]
  have hcomm : Commute M (c • (1 : Matrix S S ℝ)) := by
    change M * (c • 1) = (c • 1) * M
    rw [mul_smul_comm, mul_one, smul_mul_assoc, one_mul]
  open scoped Matrix.Norms.Operator in
  have hexp : exp (t • Qm) = exp M * exp (c • (1 : Matrix S S ℝ)) := by
    rw [show t • Qm = M + c • (1 : Matrix S S ℝ) from by simp [hM_def, sub_add_cancel]]
    exact exp_add_of_commute hcomm
  have hscalar : exp (c • (1 : Matrix S S ℝ)) =
      (Real.exp c) • (1 : Matrix S S ℝ) := by
    have h1 : c • (1 : Matrix S S ℝ) = Matrix.diagonal (fun _ => c) :=
      Matrix.smul_one_eq_diagonal c
    have h2 : NormedSpace.exp (fun _ : S => c) = fun _ : S => NormedSpace.exp c := by
      rw [show (fun _ : S => c) = algebraMap ℝ (S → ℝ) c from by
        ext; simp only [Algebra.algebraMap_eq_smul_one, Pi.smul_apply, Pi.one_apply,
          smul_eq_mul, mul_one]]
      rw [← NormedSpace.algebraMap_exp_comm]
      ext; simp only [Algebra.algebraMap_eq_smul_one, Pi.smul_apply, Pi.one_apply,
        smul_eq_mul, mul_one]
    rw [h1, Matrix.exp_diagonal, h2]
    ext i j; simp only [Matrix.diagonal_apply, Matrix.smul_apply, Matrix.one_apply,
      smul_eq_mul, ← Real.exp_eq_exp_ℝ]
    split <;> simp_all
  have hfinal : exp (t • Qm) s s = Real.exp c * (exp M s s) := by
    rw [hexp, hscalar, mul_smul_comm, mul_one]
    simp only [Matrix.smul_apply, smul_eq_mul]
  simp only [transitionProb]
  rw [hfinal]
  have hge1 := Matrix.exp_diag_ge_one hM_nonneg s
  have hc_eq : -μ * t = c := by rw [hc_def]; ring
  calc Real.exp (-μ * t) = Real.exp c := by rw [hc_eq]
    _ ≤ Real.exp c * exp M s s := le_mul_of_one_le_right (Real.exp_nonneg _) hge1

/-! ## Transition Matrix Properties -/

/-- The transition matrix is symmetric when Q is symmetric. -/
theorem QMatrix.transitionProb_symm (Q : QMatrix S) (hsymm : ∀ s u, Q.rate s u = Q.rate u s)
    (s u : S) (t : ℝ) : Q.transitionProb t s u = Q.transitionProb t u s := by
  simp only [transitionProb]
  set A := t • (Matrix.of Q.rate : Matrix S S ℝ)
  have hA_symm : Aᵀ = A := by
    ext i j; simp [A, Matrix.transpose_apply, Matrix.of_apply, hsymm i j]
  open scoped Matrix.Norms.Operator in
  have h_exp_symm : (exp A)ᵀ = exp A := by rw [← Matrix.exp_transpose, hA_symm]
  have h1 : (exp A)ᵀ s u = exp A s u := congr_fun (congr_fun h_exp_symm s) u
  rw [Matrix.transpose_apply] at h1
  exact h1.symm

/-- The derivative of the row sum is zero: d/dt ∑_u P(t)(s,u) = 0.
This is the infinitesimal form of the stochastic property. -/
theorem QMatrix.transitionProb_row_sum_deriv (Q : QMatrix S) (s : S) (t : ℝ) :
    HasDerivAt (fun t => ∑ u, Q.transitionProb t s u) 0 t := by
  have hsum := HasDerivAt.sum (u := Finset.univ) fun u _hu =>
    Q.kolmogorov_forward' s u t
  simp only [Finset.sum_comm (f := fun u v => Q.transitionProb t s v * Q.rate v u)] at hsum
  simp only [← Finset.mul_sum, Q.row_sum_zero, mul_zero, Finset.sum_const_zero] at hsum
  convert hsum using 1
  ext t₁
  exact (Finset.sum_apply t₁ Finset.univ (fun u t => Q.transitionProb t s u)).symm

/-- The exit rate from the current state determines the diagonal decay rate at t = 0:
P'(0)(s,s) = -exitRate(s). -/
theorem QMatrix.transitionProb_diag_deriv_zero (Q : QMatrix S) (s : S) :
    HasDerivAt (fun t => Q.transitionProb t s s) (-Q.exitRate s) 0 := by
  have := Q.transitionProb_deriv_zero s s
  rwa [Q.diag_eq_neg_exitRate] at this

/-- P(t) converges to I uniformly as t → 0: for every ε > 0, there exists δ > 0
such that |P(t)(s,u) - δ_{su}| < ε for all |t| < δ and all s, u. -/
theorem QMatrix.transitionProb_tendsto_identity (Q : QMatrix S) (s u : S) :
    Filter.Tendsto (fun t => Q.transitionProb t s u)
      (nhds 0) (nhds (if s = u then 1 else 0)) := by
  rw [← Q.transitionProb_zero s u]
  exact (Q.transitionProb_continuous s u).continuousAt.tendsto

/-- Tight diagonal lower bound: P(t)(s,s) ≥ exp(-exitRate(s)·t) for t ≥ 0.
Proof via Gronwall: g(t) = P(t)(s,s)·exp(exitRate·t) satisfies g'(t) ≥ 0
(using Kolmogorov backward + nonnegativity of off-diagonal terms), so g(t) ≥ g(0) = 1. -/
theorem QMatrix.transitionProb_diag_tight_bound [Nonempty S]
    (Q : QMatrix S) (s : S) {t : ℝ} (ht : 0 ≤ t) :
    Real.exp (-(Q.exitRate s) * t) ≤ Q.transitionProb t s s := by
  set exitR := Q.exitRate s with hexitR_def
  set g := fun t => Q.transitionProb t s s * Real.exp (exitR * t) with hg_def
  have hg_hasderiv : ∀ t₀ : ℝ, HasDerivAt g
      ((∑ v, Q.rate s v * Q.transitionProb t₀ v s) * Real.exp (exitR * t₀) +
       Q.transitionProb t₀ s s * (exitR * Real.exp (exitR * t₀))) t₀ := by
    intro t₀
    have hP := Q.kolmogorov_backward' s s t₀
    have hE : HasDerivAt (fun t => Real.exp (exitR * t)) (exitR * Real.exp (exitR * t₀)) t₀ := by
      have hlin : HasDerivAt (fun t => exitR * t) exitR t₀ :=
        ((hasDerivAt_id t₀).const_mul exitR).congr_deriv (mul_one exitR)
      exact ((Real.hasDerivAt_exp (exitR * t₀)).comp t₀ hlin).congr_deriv (mul_comm _ _)
    exact hg_def ▸ hP.mul hE
  have hg_deriv_eq : ∀ t₀ : ℝ, deriv g t₀ =
      (∑ v ∈ Finset.univ.erase s,
        Q.rate s v * Q.transitionProb t₀ v s) * Real.exp (exitR * t₀) := by
    intro t₀
    have hd := (hg_hasderiv t₀).deriv
    rw [hd]
    set offDiag := ∑ v ∈ Finset.univ.erase s,
      Q.rate s v * Q.transitionProb t₀ v s
    set P := Q.transitionProb t₀ s s
    set E := Real.exp (exitR * t₀)
    have hsplit : ∑ v, Q.rate s v * Q.transitionProb t₀ v s =
        Q.rate s s * P + offDiag := by
      rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ s)]
    rw [hsplit, Q.diag_eq_neg_exitRate, show -Q.exitRate s = -exitR from rfl]
    ring
  have hg_diff : Differentiable ℝ g := by
    intro t₀; exact (hg_hasderiv t₀).differentiableAt
  have hg_cont : ContinuousOn g (Set.Ici 0) := hg_diff.continuous.continuousOn
  have hg_mono : MonotoneOn g (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici (0 : ℝ)) hg_cont
    · exact hg_diff.differentiableOn.mono interior_subset
    · intro t₀ ht₀
      rw [hg_deriv_eq]
      apply mul_nonneg
      · apply Finset.sum_nonneg
        intro v hv
        have hne : s ≠ v := (Finset.mem_erase.mp hv).1.symm
        exact mul_nonneg (Q.rate_nonneg s v hne)
          (Q.transitionProb_nonneg v s (interior_subset ht₀))
      · exact Real.exp_nonneg _
  have hg0 : g 0 = 1 := by simp [hg_def, Q.transitionProb_zero_diag]
  have hle : g 0 ≤ g t := hg_mono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht) ht
  rw [hg0] at hle
  simp only [hg_def] at hle
  have hexp_pos : 0 < Real.exp (exitR * t) := Real.exp_pos _
  have key : Real.exp (-exitR * t) * Real.exp (exitR * t) = 1 := by
    rw [neg_mul, ← Real.exp_add, neg_add_cancel, Real.exp_zero]
  exact le_of_mul_le_mul_right (by linarith [key]) hexp_pos

/-! ## Off-Diagonal Bounds -/

/-- Sum of off-diagonal transition probabilities: ∑_{u≠s} P(t)(s,u) = 1 - P(t)(s,s). -/
theorem QMatrix.transitionProb_offdiag_sum (Q : QMatrix S) (s : S) (t : ℝ) :
    ∑ u ∈ Finset.univ.erase s, Q.transitionProb t s u = 1 - Q.transitionProb t s s := by
  have hrow := Q.transitionProb_row_sum s t
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ s)] at hrow
  linarith

/-- Off-diagonal upper bound: P(t)(s,u) ≤ 1 - P(t)(s,s) for s ≠ u.
A single off-diagonal entry is bounded by the total off-diagonal mass. -/
theorem QMatrix.transitionProb_offdiag_le [Nonempty S]
    (Q : QMatrix S) {s u : S} (hne : s ≠ u) {t : ℝ} (ht : 0 ≤ t) :
    Q.transitionProb t s u ≤ 1 - Q.transitionProb t s s := by
  rw [← Q.transitionProb_offdiag_sum s t]
  exact Finset.single_le_sum
    (fun v _ => Q.transitionProb_nonneg s v ht)
    (Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_univ u⟩)

/-- Off-diagonal upper bound via exit rate: P(t)(s,u) ≤ 1 - exp(-exitRate(s)·t) for s ≠ u. -/
theorem QMatrix.transitionProb_offdiag_upper [Nonempty S]
    (Q : QMatrix S) {s u : S} (hne : s ≠ u) {t : ℝ} (ht : 0 ≤ t) :
    Q.transitionProb t s u ≤ 1 - Real.exp (-(Q.exitRate s) * t) := by
  have hle := Q.transitionProb_offdiag_le hne ht
  have hbound := Q.transitionProb_diag_tight_bound s ht
  linarith

/-! ## Generator Trace -/

/-- Trace of the Q-matrix: ∑_s Q(s,s) = -∑_s exitRate(s). -/
theorem QMatrix.trace_eq_neg_sum_exitRate (Q : QMatrix S) :
    ∑ s, Q.rate s s = -∑ s, Q.exitRate s := by
  simp_rw [diag_eq_neg_exitRate, Finset.sum_neg_distrib]

/-- The Q-matrix has nonpositive trace (sum of diagonal entries ≤ 0). -/
theorem QMatrix.trace_nonpos (Q : QMatrix S) :
    ∑ s, Q.rate s s ≤ 0 := by
  rw [Q.trace_eq_neg_sum_exitRate]
  exact neg_nonpos.mpr (Finset.sum_nonneg fun s _ => Q.exitRate_nonneg s)

/-- The Q-matrix trace is zero iff all states are absorbing. -/
theorem QMatrix.trace_eq_zero_iff (Q : QMatrix S) :
    ∑ s, Q.rate s s = 0 ↔ ∀ s, Q.IsAbsorbing s := by
  rw [Q.trace_eq_neg_sum_exitRate, neg_eq_zero]
  constructor
  · intro h s
    exact le_antisymm
      (Finset.single_le_sum (fun s _ => Q.exitRate_nonneg s) (Finset.mem_univ s) |>.trans h.le)
      (Q.exitRate_nonneg s)
  · intro h; exact Finset.sum_eq_zero fun s _ => h s

/-! ## Transition Probability Asymptotics -/

/-- Off-diagonal transition probability is bounded by exit rate times t for small t. -/
theorem QMatrix.transitionProb_offdiag_linear_bound (Q : QMatrix S) {s u : S}
    (hne : s ≠ u) : (fun t => Q.transitionProb t s u - t * Q.rate s u) =o[nhds 0]
    fun t => t := by
  have := Q.transitionProb_linearApprox s u
  simp only [if_neg hne] at this
  convert this using 1
  ext t; ring

/-! ## Additional Properties -/

/-- The derivative of the off-diagonal entry P(t)(s,u) at t=0 equals Q(s,u). -/
theorem QMatrix.transitionProb_offdiag_deriv_zero (Q : QMatrix S) {s u : S}
    (_hne : s ≠ u) :
    HasDerivAt (fun t => Q.transitionProb t s u) (Q.rate s u) 0 :=
  Q.transitionProb_deriv_zero s u

/-- P(t)(s,s) < 1 for non-absorbing s and any t > 0.
Proof by contradiction: if P(t₀)(s,s) = 1 for t₀ > 0, then P(t₀)(s,u) = 0 for u ≠ s,
so P'(t₀)(s,s) = Q(s,s) = -exitRate(s) < 0 by forward equation. This means P exceeds 1
just before t₀, contradicting P(t)(s,s) ≤ 1. -/
theorem QMatrix.transitionProb_diag_lt_one_of_pos [Nonempty S]
    (Q : QMatrix S) {s : S} (hna : ¬Q.IsAbsorbing s) {t : ℝ} (ht : 0 < t) :
    Q.transitionProb t s s < 1 := by
  by_contra h
  push Not at h
  have hle := Q.transitionProb_le_one s s (le_of_lt ht)
  have heq : Q.transitionProb t s s = 1 := le_antisymm hle h
  have hoff : ∀ u, u ≠ s → Q.transitionProb t s u = 0 := by
    intro u hne
    have hnn := Q.transitionProb_nonneg s u (le_of_lt ht)
    have hrow := Q.transitionProb_row_sum s t
    have hsplit := Finset.add_sum_erase Finset.univ
      (fun v => Q.transitionProb t s v) (Finset.mem_univ s)
    have hu_le := Finset.single_le_sum
      (fun v _ => Q.transitionProb_nonneg s v (le_of_lt ht))
      (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ u⟩)
    linarith
  have hderiv := Q.kolmogorov_forward' s s t
  have hderiv_val : ∑ v, Q.transitionProb t s v * Q.rate v s =
      Q.rate s s := by
    rw [Finset.sum_eq_single s]
    · rw [heq, one_mul]
    · intro v _ hvs; rw [hoff v hvs, zero_mul]
    · intro h; exact absurd (Finset.mem_univ s) h
  rw [hderiv_val] at hderiv
  have hrate_neg : Q.rate s s < 0 := by
    rw [Q.diag_eq_neg_exitRate]
    exact neg_lt_zero.mpr (lt_of_le_of_ne (Q.exitRate_nonneg s) (Ne.symm hna))
  rw [hasDerivAt_iff_isLittleO_nhds_zero] at hderiv
  have heps : (0 : ℝ) < -Q.rate s s / 2 := by linarith
  have hbound := hderiv.bound heps
  obtain ⟨δ, hδ_pos, hδ_sub⟩ := Metric.eventually_nhds_iff.mp hbound
  set ε := min (δ / 2) (t / 2) with hε_def
  have hε_pos : 0 < ε := lt_min (half_pos hδ_pos) (half_pos ht)
  have hdist : dist (-ε) (0 : ℝ) < δ := by
    rw [dist_zero_right, Real.norm_eq_abs, abs_neg, abs_of_pos hε_pos]
    linarith [min_le_left (δ / 2) (t / 2)]
  have hbd := hδ_sub hdist
  simp only [smul_eq_mul, norm_neg, Real.norm_eq_abs, abs_of_pos hε_pos] at hbd
  have ht_eps : 0 ≤ t + -ε := by linarith [min_le_right (δ / 2) (t / 2)]
  have hle1 := Q.transitionProb_le_one s s ht_eps
  have key := (abs_le.mp hbd).1
  nlinarith [heq, mul_neg_of_neg_of_pos hrate_neg hε_pos]

/-- For non-absorbing s and t > 0, the off-diagonal sum ∑_{u≠s} P(t)(s,u) is positive. -/
theorem QMatrix.transitionProb_offdiag_sum_pos [Nonempty S]
    (Q : QMatrix S) {s : S} (hna : ¬Q.IsAbsorbing s) {t : ℝ} (ht : 0 < t) :
    0 < ∑ u ∈ Finset.univ.erase s, Q.transitionProb t s u := by
  have hlt := Q.transitionProb_diag_lt_one_of_pos hna ht
  have hrow := Q.transitionProb_row_sum s t
  have hsplit := Finset.add_sum_erase Finset.univ
    (fun v => Q.transitionProb t s v) (Finset.mem_univ s)
  linarith

/-- Non-absorbing states have positive exit probability at any t > 0. -/
theorem QMatrix.exit_prob_pos [Nonempty S]
    (Q : QMatrix S) {s : S} (hna : ¬Q.IsAbsorbing s) {t : ℝ} (ht : 0 < t) :
    0 < 1 - Q.transitionProb t s s := by
  linarith [Q.transitionProb_diag_lt_one_of_pos hna ht]

/-- Absorbing states stay put: P(t)(s,s) = 1 for all t ≥ 0 when s is absorbing. -/
theorem QMatrix.transitionProb_absorbing_one [Nonempty S]
    (Q : QMatrix S) {s : S} (h : Q.IsAbsorbing s) {t : ℝ} (_ht : 0 ≤ t) :
    Q.transitionProb t s s = 1 := by
  rw [Q.transitionProb_absorbing_diag h t]

/-! ## Positivity Extension -/

/-- If P(t₀)(s,u) > 0 for some t₀ > 0, then P(t)(s,u) > 0 for all t ≥ t₀.
Uses Chapman-Kolmogorov: P(t)(s,u) ≥ P(t-t₀)(s,s) · P(t₀)(s,u). -/
theorem QMatrix.transitionProb_pos_extend [Nonempty S]
    (Q : QMatrix S) {s u : S} {t₀ : ℝ} (ht₀ : 0 < t₀)
    (hpos : 0 < Q.transitionProb t₀ s u) {t : ℝ} (ht : t₀ ≤ t) :
    0 < Q.transitionProb t s u := by
  have htt₀ : 0 ≤ t - t₀ := by linarith
  have hkey : Q.transitionProb t s u =
      ∑ v, Q.transitionProb (t - t₀) s v * Q.transitionProb t₀ v u := by
    have := Q.transitionProb_add (t - t₀) t₀ s u
    rwa [sub_add_cancel] at this
  rw [hkey]
  calc 0 < Q.transitionProb (t - t₀) s s * Q.transitionProb t₀ s u :=
        mul_pos (Q.transitionProb_diag_pos s htt₀) hpos
    _ ≤ ∑ v, Q.transitionProb (t - t₀) s v * Q.transitionProb t₀ v u :=
        Finset.single_le_sum
          (fun v _ => mul_nonneg (Q.transitionProb_nonneg s v htt₀)
            (Q.transitionProb_nonneg v u (le_of_lt ht₀)))
          (Finset.mem_univ s)

/-- For direct neighbors (Q(s,u) > 0), P(t)(s,u) > 0 for ALL t > 0.
Small t: linear approximation P(t) ≈ t·Q(s,u).
Large t: CK extension via diagonal. -/
theorem QMatrix.transitionProb_pos_of_direct_rate [Nonempty S]
    (Q : QMatrix S) {s u : S} (hne : s ≠ u) (hrate : 0 < Q.rate s u)
    {t : ℝ} (ht : 0 < t) : 0 < Q.transitionProb t s u := by
  have hderiv := Q.transitionProb_deriv_zero s u
  have h0 : Q.transitionProb 0 s u = 0 := Q.transitionProb_zero_offdiag s u hne
  rw [hasDerivAt_iff_isLittleO_nhds_zero] at hderiv
  simp only [zero_add, h0, sub_zero, smul_eq_mul] at hderiv
  obtain ⟨δ, hδ_pos, hδ_sub⟩ := Metric.eventually_nhds_iff.mp (hderiv.bound (half_pos hrate))
  by_cases hsmall : t < δ
  · have hdist : dist t (0 : ℝ) < δ := by
      rwa [dist_zero_right, Real.norm_eq_abs, abs_of_pos ht]
    have hbd := hδ_sub hdist
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos ht] at hbd
    nlinarith [(abs_le.mp hbd).1, mul_pos (half_pos hrate) ht]
  · push Not at hsmall
    have hδ2_pos : 0 < δ / 2 := half_pos hδ_pos
    have hδ2_lt : dist (δ / 2) (0 : ℝ) < δ := by
      rw [dist_zero_right, Real.norm_eq_abs, abs_of_pos hδ2_pos]; linarith
    have hbd2 := hδ_sub hδ2_lt
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hδ2_pos] at hbd2
    have hpos2 : 0 < Q.transitionProb (δ / 2) s u := by
      nlinarith [(abs_le.mp hbd2).1, mul_pos (half_pos hrate) hδ2_pos]
    exact Q.transitionProb_pos_extend hδ2_pos hpos2 (by linarith)

/-- If all off-diagonal rates are positive, then P(t)(s,u) > 0 for all t > 0 and all s, u.
Covers the important case of fully connected transition graphs (common in CRN applications). -/
theorem QMatrix.transitionProb_pos_of_all_rates_pos [Nonempty S]
    (Q : QMatrix S) (hall : ∀ s u, s ≠ u → 0 < Q.rate s u)
    (s u : S) {t : ℝ} (ht : 0 < t) : 0 < Q.transitionProb t s u := by
  by_cases h : s = u
  · subst h; exact Q.transitionProb_diag_pos s (le_of_lt ht)
  · exact Q.transitionProb_pos_of_direct_rate h (hall s u h) ht

/-- Irreducible chains with all off-diagonal rates positive: every transition probability
is positive for t > 0. This is a special case but covers most CRN applications. -/
theorem QMatrix.irreducible_of_all_rates_pos' [Nonempty S]
    (Q : QMatrix S) (hall : ∀ s u, s ≠ u → 0 < Q.rate s u) :
    Q.Irreducible := by
  intro s u
  by_cases h : s = u
  · subst h; exact Q.reachable_self s
  · exact ⟨1, one_pos, Q.transitionProb_pos_of_all_rates_pos hall s u one_pos⟩

/-! ## Additional Stationary Distribution Results -/

/-- If π satisfies detailed balance with Q, then π is also a left null vector of Q
at each state: ∑_s π(s) Q(s,u) = 0. This is just DetailedBalance.isStationary
restated. -/
theorem QMatrix.DetailedBalance.null_vector (Q : QMatrix S) (π : Distribution S)
    (hdb : Q.DetailedBalance π) (u : S) :
    ∑ s, π.prob s * Q.rate s u = 0 :=
  hdb.isStationary Q π u

/-- Symmetric Q-matrices satisfy detailed balance with the uniform distribution.
More precisely: if Q(s,u) = Q(u,s) for all s,u, then for any distribution π,
the detailed balance condition π(s)Q(s,u) = π(u)Q(u,s) holds whenever π is uniform. -/
theorem QMatrix.symm_detailed_balance (Q : QMatrix S)
    (hsymm : ∀ s u, Q.rate s u = Q.rate u s)
    (π : Distribution S) (hunif : ∀ s u, π.prob s = π.prob u) :
    Q.DetailedBalance π := by
  intro s u _
  rw [hsymm s u, hunif s u]

/-- Column sum of Q equals zero when Q is symmetric (since row sums are zero). -/
theorem QMatrix.col_sum_zero_of_symm (Q : QMatrix S)
    (hsymm : ∀ s u, Q.rate s u = Q.rate u s) (u : S) :
    ∑ s, Q.rate s u = 0 := by
  have : ∑ s, Q.rate s u = ∑ s, Q.rate u s := by
    congr 1; ext s; exact hsymm s u
  rw [this, Q.row_sum_zero]

/-- Off-diagonal rate positive implies the state is not absorbing. -/
theorem QMatrix.not_absorbing_of_rate_pos (Q : QMatrix S) {s u : S}
    (hne : s ≠ u) (hrate : 0 < Q.rate s u) : ¬Q.IsAbsorbing s := by
  intro h
  have h0 := QMatrix.IsAbsorbing.rate_eq_zero Q h u hne
  linarith

/-! ## Transition Probability Bounds -/

/-- Lower bound on transition probability via CK: for any intermediate state v,
P(t₁+t₂)(s,u) ≥ P(t₁)(s,v) · P(t₂)(v,u). -/
theorem QMatrix.transitionProb_CK_lower_bound [Nonempty S]
    (Q : QMatrix S) (s v u : S) {t₁ t₂ : ℝ} (ht₁ : 0 ≤ t₁) (ht₂ : 0 ≤ t₂) :
    Q.transitionProb t₁ s v * Q.transitionProb t₂ v u ≤
    Q.transitionProb (t₁ + t₂) s u := by
  rw [Q.transitionProb_add t₁ t₂ s u]
  exact Finset.single_le_sum
    (fun w _ => mul_nonneg (Q.transitionProb_nonneg s w ht₁)
      (Q.transitionProb_nonneg w u ht₂))
    (Finset.mem_univ v)

/-- The product of diagonal entries bounds the return probability:
P(t₁+t₂)(s,s) ≥ P(t₁)(s,s) · P(t₂)(s,s). (Submultiplicativity of diagonal.) -/
theorem QMatrix.transitionProb_diag_submult [Nonempty S]
    (Q : QMatrix S) (s : S) {t₁ t₂ : ℝ} (ht₁ : 0 ≤ t₁) (ht₂ : 0 ≤ t₂) :
    Q.transitionProb t₁ s s * Q.transitionProb t₂ s s ≤
    Q.transitionProb (t₁ + t₂) s s :=
  Q.transitionProb_CK_lower_bound s s s ht₁ ht₂

/-- Diagonal transition probability is log-superadditive:
log P(t₁+t₂)(s,s) ≥ log P(t₁)(s,s) + log P(t₂)(s,s). -/
theorem QMatrix.transitionProb_diag_log_superadd [Nonempty S]
    (Q : QMatrix S) (s : S) {t₁ t₂ : ℝ} (ht₁ : 0 ≤ t₁) (ht₂ : 0 ≤ t₂) :
    Real.log (Q.transitionProb t₁ s s) + Real.log (Q.transitionProb t₂ s s) ≤
    Real.log (Q.transitionProb (t₁ + t₂) s s) := by
  rw [← Real.log_mul (ne_of_gt (Q.transitionProb_diag_pos s ht₁))
    (ne_of_gt (Q.transitionProb_diag_pos s ht₂))]
  exact Real.log_le_log (mul_pos (Q.transitionProb_diag_pos s ht₁)
    (Q.transitionProb_diag_pos s ht₂)) (Q.transitionProb_diag_submult s ht₁ ht₂)

/-! ## Transition Probability: Long-time Behavior -/

/-- For non-absorbing s, the diagonal P(t)(s,s) is strictly less than 1
and bounded below by exp(-exitRate·t), giving precise control on the
diagonal's long-time decay. -/
theorem QMatrix.transitionProb_diag_sandwich [Nonempty S]
    (Q : QMatrix S) {s : S} (hna : ¬Q.IsAbsorbing s) {t : ℝ} (ht : 0 < t) :
    Real.exp (-(Q.exitRate s) * t) ≤ Q.transitionProb t s s ∧
    Q.transitionProb t s s < 1 :=
  ⟨Q.transitionProb_diag_tight_bound s (le_of_lt ht),
   Q.transitionProb_diag_lt_one_of_pos hna ht⟩

/-! ## Irreducible Positivity -/

/-- Graph reachability via positive rates: there exists a directed path
s = v₀ → v₁ → ... → vₖ = u where Q(vᵢ, vᵢ₊₁) > 0. -/
inductive QMatrix.GraphPath (Q : QMatrix S) : S → S → Prop where
  | refl (s : S) : Q.GraphPath s s
  | step {s v u : S} (hne : s ≠ v) (hrate : 0 < Q.rate s v)
      (rest : Q.GraphPath v u) : Q.GraphPath s u

/-- Graph path implies P(t)(s,u) > 0 for all t > 0.
Induction on path structure, using transitionProb_pos_of_direct_rate for edges
and CK for composition. -/
theorem QMatrix.GraphPath.transitionProb_pos [Nonempty S]
    {Q : QMatrix S} {s u : S} (hp : Q.GraphPath s u) :
    ∀ {t : ℝ}, 0 < t → 0 < Q.transitionProb t s u := by
  induction hp with
  | refl s => intro t ht; exact Q.transitionProb_diag_pos s (le_of_lt ht)
  | @step a b c hab hrab _rest ih =>
    intro t ht
    have ht2 : 0 < t / 2 := half_pos ht
    have hfirst := Q.transitionProb_pos_of_direct_rate hab hrab ht2
    have hsecond := ih ht2
    have hkey := Q.transitionProb_CK_lower_bound a b c (le_of_lt ht2) (le_of_lt ht2)
    rw [show t / 2 + t / 2 = t from add_halves t] at hkey
    linarith [mul_pos hfirst hsecond]

/-- If all off-diagonal rates are positive, P(t)(s,u) > 0 for all t > 0 and all s, u.
This is a corollary of GraphPath.transitionProb_pos with 1-step paths. -/
theorem QMatrix.transitionProb_pos_of_all_rates_pos' [Nonempty S]
    (Q : QMatrix S) (hall : ∀ s u, s ≠ u → 0 < Q.rate s u)
    (s u : S) {t : ℝ} (ht : 0 < t) : 0 < Q.transitionProb t s u := by
  by_cases h : s = u
  · subst h; exact Q.transitionProb_diag_pos s (le_of_lt ht)
  · exact (QMatrix.GraphPath.step h (hall s u h) (.refl u)).transitionProb_pos ht

/-! ## Transition Matrix Algebra -/

/-- P(t) maps distributions to distributions: if ∑_s π(s) = 1 and π ≥ 0,
then ∑_s π(s) P(t)(s,u) ∈ [0,1] for each u. -/
theorem QMatrix.transitionProb_preserves_nonneg [Nonempty S]
    (Q : QMatrix S) (π : S → ℝ) (hnn : ∀ s, 0 ≤ π s)
    (u : S) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ ∑ s, π s * Q.transitionProb t s u :=
  Finset.sum_nonneg fun s _ => mul_nonneg (hnn s) (Q.transitionProb_nonneg s u ht)

/-- P(t) preserves the total mass: ∑_u ∑_s π(s) P(t)(s,u) = ∑_s π(s). -/
theorem QMatrix.transitionProb_preserves_mass (Q : QMatrix S) (π : S → ℝ) (t : ℝ) :
    ∑ u, ∑ s, π s * Q.transitionProb t s u = ∑ s, π s := by
  rw [Finset.sum_comm]
  congr 1; ext s
  rw [← Finset.mul_sum]
  rw [Q.transitionProb_row_sum s t, mul_one]

/-- If the transition probabilities agree on a single column at all times,
then the rates to that column agree.
Contrapositive: different rates produce different transition probabilities. -/
theorem QMatrix.rate_determined_by_transitionProb (Q₁ Q₂ : QMatrix S)
    (s u : S) (h : ∀ t, Q₁.transitionProb t s u = Q₂.transitionProb t s u) :
    Q₁.rate s u = Q₂.rate s u := by
  have h1 := Q₁.transitionProb_deriv_zero s u
  have h2 := Q₂.transitionProb_deriv_zero s u
  have hfun : (fun t => Q₁.transitionProb t s u) = (fun t => Q₂.transitionProb t s u) :=
    funext h
  rw [hfun] at h1
  exact h1.unique h2

/-- Two Q-matrices that generate the same transition semigroup must be equal. -/
theorem QMatrix.ext_of_transitionProb_eq (Q₁ Q₂ : QMatrix S)
    (h : ∀ t s u, Q₁.transitionProb t s u = Q₂.transitionProb t s u) :
    Q₁.rate = Q₂.rate := by
  ext s u
  exact Q₁.rate_determined_by_transitionProb Q₂ s u (fun t => h t s u)

/-! ## Diagonal Decay Rate -/

/-- The diagonal decay rate: lim_{t→0+} (1 - P(t)(s,s))/t = exitRate(s).
Formally: P(t)(s,s) = 1 - exitRate(s)·t + o(t). -/
theorem QMatrix.transitionProb_diag_linear_approx (Q : QMatrix S) (s : S) :
    (fun t => Q.transitionProb t s s - (1 - Q.exitRate s * t)) =o[nhds 0]
    fun t => t := by
  have hla := Q.transitionProb_linearApprox s s
  have : (fun t => Q.transitionProb t s s - (1 - Q.exitRate s * t)) =
      (fun t => Q.transitionProb t s s - 1 - t * Q.rate s s) := by
    ext t; rw [Q.diag_eq_neg_exitRate]; ring
  rw [this]
  convert hla using 1
  ext t; simp only [ite_true]

end Ripple.CTMC
