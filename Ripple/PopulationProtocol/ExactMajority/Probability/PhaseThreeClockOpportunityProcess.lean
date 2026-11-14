-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockOpportunityProcess.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockTickWeightAlgebra
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockPrefixMaximal

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators MeasureTheory ProbabilityTheory

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockOpportunityProcess

open PhaseThreeScalar PhaseThreeClockTickWeightAlgebra PhaseThreeClockPrefixMaximal

variable {Ω : Type*} {m₀ : MeasurableSpace Ω}
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ℱ : Filtration ℕ m₀}

theorem integrable_of_nonneg_bound {f : Ω → ℝ} {M : ℝ}
    (hf : StronglyMeasurable f) (hbound : ∀ ω, 0 ≤ f ω ∧ f ω ≤ M) :
    Integrable f μ := by
  refine Integrable.of_bound hf.aestronglyMeasurable M ?_
  exact ae_of_all _ (fun ω => by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hbound ω).1] using (hbound ω).2)

theorem conditional_affine_upper
    {U V P Q I J : Ω → ℝ} {m : MeasurableSpace Ω}
    (hm : m ≤ m₀) (hU : StronglyMeasurable[m] U)
    (hP : StronglyMeasurable[m] P) (hQ : StronglyMeasurable[m] Q)
    (hUi : Integrable U μ) (hVi : Integrable V μ)
    (hIi : Integrable I μ) (hJi : Integrable J μ)
    (hPI : Integrable (fun ω => P ω * I ω) μ)
    (hQJ : Integrable (fun ω => Q ω * J ω) μ)
    (hstep : V ≤ᵐ[μ] fun ω => U ω + P ω * I ω - Q ω * J ω) :
    μ[V | m] ≤ᵐ[μ] fun ω =>
      U ω + P ω * μ[I | m] ω - Q ω * μ[J | m] ω := by
  have hcur : μ[U | m] = U := condExp_of_stronglyMeasurable hm hU hUi
  have hmono := condExp_mono (m := m) hVi ((hUi.add hPI).sub hQJ) hstep
  have hadd := condExp_add hUi hPI m
  have hsub := condExp_sub (hUi.add hPI) hQJ m
  have hpull := condExp_mul_of_stronglyMeasurable_left hP hPI hIi
  have hqpull := condExp_mul_of_stronglyMeasurable_left hQ hQJ hJi
  filter_upwards [hmono, hadd, hsub, hpull, hqpull] with ω hmω ha hs hp hq
  have ha' : μ[fun ω => U ω + P ω * I ω | m] ω =
      U ω + μ[fun ω => P ω * I ω | m] ω := by
    simpa only [Pi.add_apply, hcur] using ha
  have hs' : μ[fun ω => U ω + P ω * I ω - Q ω * J ω | m] ω =
      μ[fun ω => U ω + P ω * I ω | m] ω -
        μ[fun ω => Q ω * J ω | m] ω := by
    simpa only [Pi.sub_apply, Pi.add_apply] using hs
  have hp' : μ[fun ω => P ω * I ω | m] ω = P ω * μ[I | m] ω := by
    simpa only [Pi.mul_apply] using hp
  have hq' : μ[fun ω => Q ω * J ω | m] ω = Q ω * μ[J | m] ω := by
    simpa only [Pi.mul_apply] using hq
  change μ[V | m] ω ≤ U ω + P ω * μ[I | m] ω - Q ω * μ[J | m] ω
  have hm' : μ[V | m] ω ≤
      μ[fun ω => U ω + P ω * I ω - Q ω * J ω | m] ω := hmω
  rwa [hs', ha', hp', hq'] at hm'

def opportunityCompensator (d J : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  ∑ u ∈ Finset.range t, d u ω * J u ω

@[simp] theorem opportunityCompensator_zero (d J : ℕ → Ω → ℝ) (ω : Ω) :
    opportunityCompensator d J 0 ω = 0 := by simp [opportunityCompensator]

theorem opportunityCompensator_succ (d J : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    opportunityCompensator d J (t + 1) ω =
      opportunityCompensator d J t ω + d t ω * J t ω := by
  simp only [opportunityCompensator, Finset.sum_range_succ]

theorem opportunityCompensator_nonneg (d J : ℕ → Ω → ℝ)
    (hd : ∀ t ω, 0 ≤ d t ω) (hJ : ∀ t ω, J t ω = 0 ∨ J t ω = 1)
    (t : ℕ) (ω : Ω) : 0 ≤ opportunityCompensator d J t ω := by
  apply Finset.sum_nonneg
  intro u _
  have hj : 0 ≤ J u ω := by rcases hJ u ω with h | h <;> simp only [h] <;> norm_num
  exact mul_nonneg (hd u ω) hj

theorem opportunityCompensator_stronglyMeasurable (d J : ℕ → Ω → ℝ)
    (hd : ∀ t, StronglyMeasurable[ℱ t] (d t))
    (hJ : ∀ t, StronglyMeasurable[ℱ (t + 1)] (J t)) (t : ℕ) :
    StronglyMeasurable[ℱ t] (opportunityCompensator d J t) := by
  unfold opportunityCompensator
  refine (Finset.range t).stronglyMeasurable_fun_sum ?_
  intro u hu
  have hut : u + 1 ≤ t := Nat.succ_le_of_lt (Finset.mem_range.mp hu)
  exact ((hd u).mono (ℱ.mono (by omega : u ≤ t))).mul
    ((hJ u).mono (ℱ.mono hut))

theorem opportunity_supermartingale
    (Z b d P J : ℕ → Ω → ℝ) (M B : ℕ → ℝ)
    (hZ : ∀ t, StronglyMeasurable[ℱ t] (Z t))
    (hb : ∀ t, StronglyMeasurable[ℱ t] (b t))
    (hd : ∀ t, StronglyMeasurable[ℱ t] (d t))
    (hZbound : ∀ t ω, 0 ≤ Z t ω ∧ Z t ω ≤ M t)
    (hbbound : ∀ t ω, 0 ≤ b t ω ∧ b t ω ≤ B t)
    (hdnonneg : ∀ t ω, 0 ≤ d t ω)
    (hP : ∀ t, StronglyMeasurable[ℱ (t + 1)] (P t))
    (hJ : ∀ t, StronglyMeasurable[ℱ (t + 1)] (J t))
    (hPzeroOne : ∀ t ω, P t ω = 0 ∨ P t ω = 1)
    (hJzeroOne : ∀ t ω, J t ω = 0 ∨ J t ω = 1)
    (hPJ : ∀ t ω, P t ω ≤ J t ω)
    (hstep : ∀ t, Z (t + 1) ≤ᵐ[μ] fun ω =>
      Z t ω * (Real.exp (-d t ω * J t ω) * (1 + b t ω * P t ω)))
    (hrate : ∀ t, ∀ᵐ ω ∂μ,
      b t ω * (μ[P t | ℱ t]) ω ≤ (μ[J t | ℱ t]) ω * d t ω) :
    Supermartingale Z ℱ μ := by
  have hZi (t : ℕ) : Integrable (Z t) μ :=
    integrable_of_nonneg_bound ((hZ t).mono (ℱ.le t)) (hZbound t)
  refine supermartingale_nat hZ hZi ?_
  intro t
  let U : Ω → ℝ := fun ω => Z t ω * Real.exp (-d t ω) * b t ω
  let V : Ω → ℝ := fun ω => Z t ω * (1 - Real.exp (-d t ω))
  have he (ω : Ω) : 0 ≤ Real.exp (-d t ω) ∧ Real.exp (-d t ω) ≤ 1 :=
    ⟨Real.exp_nonneg _, Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hdnonneg t ω))⟩
  have hUs : StronglyMeasurable[ℱ t] U := by
    have hz := hZ t
    have hb' := hb t
    have hd' := hd t
    unfold U
    exact (hz.mul (Real.continuous_exp.comp_stronglyMeasurable hd'.neg)).mul hb'
  have hVs : StronglyMeasurable[ℱ t] V := by
    have hz := hZ t
    have hd' := hd t
    unfold V
    exact hz.mul (stronglyMeasurable_const.sub (Real.continuous_exp.comp_stronglyMeasurable hd'.neg))
  have hUb (ω : Ω) : 0 ≤ U ω ∧ U ω ≤ M t * B t := by
    have hz := hZbound t ω
    have hb' := hbbound t ω
    have hze : 0 ≤ Z t ω * Real.exp (-d t ω) ∧
        Z t ω * Real.exp (-d t ω) ≤ M t :=
      ⟨mul_nonneg hz.1 (he ω).1,
        (mul_le_mul_of_nonneg_left (he ω).2 hz.1).trans (by simpa using hz.2)⟩
    exact ⟨mul_nonneg hze.1 hb'.1, mul_le_mul hze.2 hb'.2 hb'.1 (hz.1.trans hz.2)⟩
  have hVb (ω : Ω) : 0 ≤ V ω ∧ V ω ≤ M t := by
    have hz := hZbound t ω
    have hdiff : 0 ≤ 1 - Real.exp (-d t ω) := sub_nonneg.mpr (he ω).2
    have hdiffle : 1 - Real.exp (-d t ω) ≤ 1 := by linarith [(he ω).1]
    exact ⟨mul_nonneg hz.1 hdiff,
      (mul_le_mul_of_nonneg_left hdiffle hz.1).trans (by simpa using hz.2)⟩
  have hPi : Integrable (P t) μ :=
    bernoulli_integrable hP (fun u => ae_of_all _ (hPzeroOne u)) t
  have hJi : Integrable (J t) μ :=
    bernoulli_integrable hJ (fun u => ae_of_all _ (hJzeroOne u)) t
  have hUPi : Integrable (fun ω => U ω * P t ω) μ := by
    apply integrable_of_nonneg_bound (M := M t * B t)
      ((hUs.mono (ℱ.le t)).mul ((hP t).mono (ℱ.le (t + 1))))
    intro ω
    rcases hPzeroOne t ω with h | h
    · simp only [Pi.mul_apply, h, mul_zero, le_refl, true_and]
      exact mul_nonneg ((hZbound t ω).1.trans (hZbound t ω).2)
        ((hbbound t ω).1.trans (hbbound t ω).2)
    · simpa only [Pi.mul_apply, h, mul_one] using hUb ω
  have hVJi : Integrable (fun ω => V ω * J t ω) μ := by
    apply integrable_of_nonneg_bound (M := M t)
      ((hVs.mono (ℱ.le t)).mul ((hJ t).mono (ℱ.le (t + 1))))
    intro ω
    rcases hJzeroOne t ω with h | h
    · simp only [Pi.mul_apply, h, mul_zero, le_refl, true_and]
      exact (hZbound t ω).1.trans (hZbound t ω).2
    · simpa only [Pi.mul_apply, h, mul_one] using hVb ω
  have hs : Z (t + 1) ≤ᵐ[μ] fun ω => Z t ω + U ω * P t ω - V ω * J t ω := by
    filter_upwards [hstep t] with ω hω
    have hid := tick_weight_affine_identity (P t ω) (J t ω) (b t ω) (d t ω)
      (hPzeroOne t ω) (hJzeroOne t ω) (hPJ t ω)
    rw [hid] at hω
    exact hω.trans_eq (by dsimp only [U, V]; ring)
  have hce := conditional_affine_upper (ℱ.le t) (hZ t) hUs hVs
    (hZi t) (hZi (t + 1)) hPi hJi hUPi hVJi hs
  have hJpos : ∀ᵐ ω ∂μ, 0 ≤ J t ω := ae_of_all _ (fun ω => by
    rcases hJzeroOne t ω with h | h <;> simp only [h] <;> norm_num)
  filter_upwards [hce, condExp_nonneg (m := ℱ t) hJpos, hrate t] with ω hc hj hr
  have hmean := tick_weight_mean_le_one ((μ[J t | ℱ t]) ω)
    ((μ[P t | ℱ t]) ω) (b t ω) (d t ω) hj hr
  have hmul := mul_le_mul_of_nonneg_left hmean (hZbound t ω).1
  have hid :
      Z t ω + U ω * (μ[P t | ℱ t]) ω - V ω * (μ[J t | ℱ t]) ω =
      Z t ω * (1 + (Real.exp (-d t ω) - 1) * (μ[J t | ℱ t]) ω +
        Real.exp (-d t ω) * b t ω * (μ[P t | ℱ t]) ω) := by
    dsimp only [U, V]
    ring
  exact hc.trans (by rw [hid]; simpa only [mul_one] using hmul)

theorem prefix_crossing_tail
    {Z : ℕ → Ω → ℝ} (hZ : Supermartingale Z ℱ μ)
    (hZnonneg : ∀ t ω, 0 ≤ Z t ω)
    (E : Set Ω) (hE : MeasurableSet[ℱ 0] E)
    (epsilon c : ℝ) (hepsilon : 0 ≤ epsilon) (hc : 0 ≤ c)
    (hstart : ∀ ω ∈ E, Z 0 ω ≤ epsilon)
    (B : Set Ω) (hcross : ∀ ω ∈ B, ∃ t, 1 ≤ c * Z t ω) :
    μ (E ∩ B) ≤ ENNReal.ofReal (c * epsilon) * μ E := by
  have hscaled : Supermartingale (fun t ω => c * Z t ω) ℱ μ := by
    simpa only [Pi.smul_apply, smul_eq_mul] using hZ.smul_nonneg hc
  apply (measure_mono ?_).trans
    (prefix_maximal hscaled (fun t ω => mul_nonneg hc (hZnonneg t ω))
      E hE (c * epsilon) (mul_nonneg hc hepsilon)
      (fun ω he => mul_le_mul_of_nonneg_left (hstart ω he) hc))
  rintro ω ⟨he, hb⟩
  exact ⟨he, hcross ω hb⟩

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockOpportunityProcess

end
