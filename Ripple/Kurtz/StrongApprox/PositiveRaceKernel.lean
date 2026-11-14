-- Ripple/Kurtz/StrongApprox/PositiveRaceKernel.lean
import Mathlib
import Ripple.Kurtz.StrongApprox.ExponentialRaceResidual

noncomputable section

namespace Ripple.Kurtz.StrongApprox.ExponentialRace

open MeasureTheory ProbabilityTheory Set Finset Filter
open scoped ENNReal BigOperators

variable {κ τ : Type*}

open Classical in
/-- A measurable tie-breaking winner. Ties are irrelevant because the union of
strict-winner cells is conull. -/
noncomputable def raceWinner [Fintype κ] [Nonempty κ]
    (r : κ → ℝ) (E : κ → ℝ) : κ :=
  if h : ∃ a, strictClockWin r a E then Classical.choose h
  else Classical.choice inferInstance

/-- On a strict-winner cell the measurable tie breaker selects that winner. -/
theorem raceWinner_eq_of_strict [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (r : κ → ℝ) (a : κ) (E : κ → ℝ)
    (ha : strictClockWin r a E) :
    raceWinner r E = a := by
  unfold raceWinner
  rw [dif_pos ⟨a, ha⟩]
  let b := Classical.choose (show ∃ c, strictClockWin r c E from ⟨a, ha⟩)
  have hb : strictClockWin r b E :=
    Classical.choose_spec (show ∃ c, strictClockWin r c E from ⟨a, ha⟩)
  change b = a
  by_contra hba
  exact (ha b hba).asymm (hb a (Ne.symm hba))

variable [Fintype κ] [DecidableEq κ]
  [MeasurableSpace κ] [MeasurableSingletonClass κ] [Nonempty κ]

theorem raceWinner_eq_iff (r : κ → ℝ) (a : κ) (E : κ → ℝ) :
    raceWinner r E = a ↔
      strictClockWin r a E ∨
        ((¬ ∃ b, strictClockWin r b E) ∧ a = Classical.choice inferInstance) := by
  by_cases h : ∃ b, strictClockWin r b E
  · have hw : raceWinner r E = Classical.choose h := by
      unfold raceWinner
      rw [dif_pos h]
    constructor
    · intro hE
      left
      rw [hw] at hE
      rw [← hE]
      exact Classical.choose_spec h
    · rintro (ha | ⟨hn, _⟩)
      · exact raceWinner_eq_of_strict r a E ha
      · exact absurd h hn
  · have hw : raceWinner r E = Classical.choice inferInstance := by
      unfold raceWinner
      rw [dif_neg h]
    constructor
    · intro hE
      right
      exact ⟨h, hE.symm.trans hw⟩
    · rintro (ha | ⟨_, ha⟩)
      · exact absurd ⟨a, ha⟩ h
      · rw [hw, ha]

@[fun_prop]
theorem measurable_raceWinner (r : κ → ℝ) :
    Measurable (raceWinner r) := by
  refine measurable_to_countable' fun a => ?_
  have hset : raceWinner r ⁻¹' {a} =
      {E | strictClockWin r a E} ∪
        ((⋃ b, {E : κ → ℝ | strictClockWin r b E})ᶜ ∩
          {_E : κ → ℝ | a = Classical.choice inferInstance}) := by
    ext E
    simp only [Set.mem_preimage, Set.mem_singleton_iff, raceWinner_eq_iff,
      Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_iUnion,
      Set.mem_setOf_eq, not_exists]
  rw [hset]
  refine (strictClockWin_measurableSet r a).union ?_
  exact (MeasurableSet.iUnion fun b => strictClockWin_measurableSet r b).compl.inter
    (MeasurableSet.const (a = Classical.choice inferInstance))

/-- Physical waiting time selected by the weighted race. -/
noncomputable def raceWait (r : κ → ℝ) (E : κ → ℝ) : ℝ :=
  E (raceWinner r E) / r (raceWinner r E)

@[fun_prop]
theorem measurable_raceWait (r : κ → ℝ) :
    Measurable (raceWait r) := by
  have hrewrite : raceWait r = fun E : κ → ℝ =>
      ∑ a, if raceWinner r E = a then E a / r a else 0 := by
    funext E
    classical
    simp [raceWait]
  rw [hrewrite]
  apply Finset.measurable_sum
  intro a _ha
  exact Measurable.ite
    ((measurable_raceWinner r) (measurableSet_singleton a))
    (by fun_prop : Measurable fun E : κ → ℝ => E a / r a) measurable_const

/-- The measurable holding-time/winner output of a positive exponential race. -/
noncomputable def racePair (r : κ → ℝ) (E : κ → ℝ) : ℝ × κ :=
  (raceWait r E, raceWinner r E)

@[fun_prop]
theorem measurable_racePair (r : κ → ℝ) :
    Measurable (racePair r) :=
  (measurable_raceWait r).prodMk (measurable_raceWinner r)

private theorem strictWinnerCells_pairwise (r : κ → ℝ) :
    Pairwise fun a b : κ => Disjoint
      {E : κ → ℝ | strictClockWin r a E}
      {E : κ → ℝ | strictClockWin r b E} := by
  intro a b hab
  rw [Set.disjoint_left]
  intro E ha hb
  exact (ha b hab.symm).asymm (hb a hab)

/-- Strict-winner cells form a conull measurable partition. -/
theorem clockLaw_decompose_strictWinners
    (r : κ → ℝ) (hr : ∀ a, 0 < r a) :
    clockLaw κ = Measure.sum fun a : κ =>
      (clockLaw κ).restrict {E | strictClockWin r a E} := by
  let S : κ → Set (κ → ℝ) := fun a => {E | strictClockWin r a E}
  have hS (a : κ) : MeasurableSet (S a) :=
    strictClockWin_measurableSet r a
  have hdisj : Pairwise fun a b => Disjoint (S a) (S b) :=
    strictWinnerCells_pairwise r
  have hcell (a : κ) :
      clockLaw κ (S a) = ENNReal.ofReal (r a / rateTotal r) := by
    exact strictClockWin_measure_of_rates r hr a
  have hmass : clockLaw κ (⋃ a, S a) = 1 := by
    rw [measure_iUnion hdisj hS, tsum_fintype]
    simp_rw [hcell]
    have hsum : ∑ i, r i / rateTotal r = 1 := sum_normalizedRate r hr
    rw [← ENNReal.ofReal_sum_of_nonneg
      (fun a _ => div_nonneg (hr a).le (rateTotal_pos r hr).le), hsum]
    norm_num
  have hUnion : ∀ᵐ E ∂clockLaw κ, E ∈ ⋃ a, S a :=
    (mem_ae_iff_prob_eq_one (MeasurableSet.iUnion hS)).2 hmass
  calc
    clockLaw κ = (clockLaw κ).restrict (⋃ a, S a) :=
      (Measure.restrict_eq_self_of_ae_mem hUnion).symm
    _ = Measure.sum fun a : κ => (clockLaw κ).restrict (S a) :=
      Measure.restrict_iUnion hdisj hS

/-- Winner distribution of a positive finite rate vector. -/
noncomputable def winnerPMF (r : κ → ℝ) (hr : ∀ a, 0 < r a) : PMF κ :=
  ⟨fun a => ENNReal.ofReal (r a / rateTotal r), by
    have hsum : ∑ i, r i / rateTotal r = 1 := sum_normalizedRate r hr
    rw [ENNReal.summable.hasSum_iff, tsum_fintype,
      ← ENNReal.ofReal_sum_of_nonneg
        (fun a _ => div_nonneg (hr a).le (rateTotal_pos r hr).le), hsum]
    norm_num⟩

@[simp]
theorem winnerPMF_apply (r : κ → ℝ) (hr : ∀ a, 0 < r a) (a : κ) :
    winnerPMF r hr a = ENNReal.ofReal (r a / rateTotal r) := rfl

/-- Atomic expansion of the winner PMF. -/
theorem winnerPMF_toMeasure_eq_sum
    (r : κ → ℝ) (hr : ∀ a, 0 < r a) :
    (winnerPMF r hr).toMeasure =
      Measure.sum fun a : κ =>
        ENNReal.ofReal (r a / rateTotal r) • Measure.dirac a := by
  apply Measure.ext_of_singleton
  intro a
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton a),
    Measure.sum_apply _ (measurableSet_singleton a), tsum_fintype,
    Finset.sum_eq_single a]
  · simp [winnerPMF_apply]
  · intro b _ hb
    simp [hb.symm]
  · intro h
    exact absurd (Finset.mem_univ a) h

/-- On a fixed strict-winner cell, the complete race output is winner mass
multiplied by `Exp(sum r)` and a point mass at the winner. -/
theorem racePair_restrict_law
    (r : κ → ℝ) (hr : ∀ a, 0 < r a) (a : κ) :
    Measure.map (racePair r)
        ((clockLaw κ).restrict {E | strictClockWin r a E}) =
      ENNReal.ofReal (r a / rateTotal r) •
        ((expMeasure (rateTotal r)).prod (Measure.dirac a)) := by
  letI : IsProbabilityMeasure (expMeasure (rateTotal r)) :=
    isProbabilityMeasure_expMeasure (rateTotal_pos r hr)
  have hcongr :
      racePair r =ᵐ[(clockLaw κ).restrict {E | strictClockWin r a E}]
        fun E => (E a / r a, a) := by
    filter_upwards
      [ae_restrict_mem (strictClockWin_measurableSet r a)] with E hE
    simp [racePair, raceWait, raceWinner_eq_of_strict r a E hE]
  rw [Measure.map_congr hcongr]
  change Measure.map ((fun u : ℝ => (u, a)) ∘
      (fun E : κ → ℝ => E a / r a))
      ((clockLaw κ).restrict {E | strictClockWin r a E}) = _
  rw [← Measure.map_map measurable_prodMk_right (by fun_prop),
    winnerWait_restrict_law_of_rates r hr a,
    Measure.map_smul,
    ← Measure.prod_dirac]

/-- Complete law of a finite positive-rate exponential race. -/
theorem racePair_law
    (r : κ → ℝ) (hr : ∀ a, 0 < r a) :
    Measure.map (racePair r) (clockLaw κ) =
      (expMeasure (rateTotal r)).prod (winnerPMF r hr).toMeasure := by
  letI : IsProbabilityMeasure (expMeasure (rateTotal r)) :=
    isProbabilityMeasure_expMeasure (rateTotal_pos r hr)
  conv_lhs => rw [clockLaw_decompose_strictWinners r hr]
  rw [Measure.map_sum (measurable_racePair r).aemeasurable]
  simp_rw [racePair_restrict_law r hr]
  have hmove (a : κ) :
      ENNReal.ofReal (r a / rateTotal r) •
          ((expMeasure (rateTotal r)).prod (Measure.dirac a)) =
        (expMeasure (rateTotal r)).prod
          (ENNReal.ofReal (r a / rateTotal r) • Measure.dirac a) := by
    rw [Measure.prod_smul_right]
  simp_rw [hmove]
  rw [← Measure.prod_sum_right,
    ← winnerPMF_toMeasure_eq_sum r hr]

omit [DecidableEq κ] [MeasurableSpace κ] [MeasurableSingletonClass κ] [Nonempty κ] in
/-- Any injectively indexed finite subfamily of iid unit exponential clocks
is again an iid unit exponential vector. -/
theorem clockSubfamily_law
    [Fintype τ] [MeasurableSpace τ] [MeasurableSingletonClass τ]
    (f : τ → κ) (hf : Function.Injective f) :
    (clockLaw κ).map (fun E a => E (f a)) = clockLaw τ := by
  letI : IsProbabilityMeasure (expMeasure (1 : ℝ)) :=
    isProbabilityMeasure_expMeasure zero_lt_one
  have hall : iIndepFun
      (fun i : κ => fun E : κ → ℝ => E i) (clockLaw κ) := by
    unfold clockLaw
    exact iIndepFun_pi (X := fun _ => id)
      (fun _ => measurable_id.aemeasurable)
  have hsub := hall.precomp hf
  calc
    (clockLaw κ).map (fun E a => E (f a)) =
        Measure.pi fun a : τ =>
          (clockLaw κ).map (fun E => E (f a)) :=
      hsub.map_fun_eq_pi_map
        (fun a => (measurable_pi_apply (f a)).aemeasurable)
    _ = Measure.pi (fun _ : τ => expMeasure 1) := by
      congr 1
      funext a
      simpa [clockLaw] using
        (MeasureTheory.measurePreserving_eval
          (fun _ : κ => expMeasure 1) (f a)).map_eq
    _ = clockLaw τ := rfl

end Ripple.Kurtz.StrongApprox.ExponentialRace

end
