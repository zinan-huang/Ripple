-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockThinning.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockProbabilityFloors
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockPrefixTails

/-!
# Clock-contact thinning on the original pair-log law

The Clock labels are frozen in a finite mask. Their next-contact probability
is exactly C(C-1)/(m(m-1)), even when the virtual labelling differs from the
actual labelling. The upper and lower tails retain any prefix event as a
probability factor. The final wrappers use StageEventSpec.clockContacts.

These are the two scalar thinning estimates of PHASE3 P10. Their application
to the still-unconstructed front and hour passage times is a separate task.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal BigOperators MeasureTheory ProbabilityTheory

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockThinning

open TimeTheorem PairLog PairLogAuxiliary PhaseThreeScalar
  PhaseThreeClockVirtual PhaseThreeClockGatedLaw
  PhaseThreeClockProbabilityFloors PhaseThreeClockPrefixTails

variable {L K m : ℕ}

/-- The numerator uses natural subtraction, so masks of size zero or one
have rate zero without an additional side condition. -/
def clockMaskRate (m C : ℕ) : ℝ :=
  ((C * (C - 1) : ℕ) : ℝ) / ((m : ℝ) * ((m : ℝ) - 1))

def maskContact (init : Cfg L K) (C : Finset (Fin init.card))
    (k : ℕ) (ω : Ω L K) : Prop :=
  ∃ i j, drawLabels init ω k = some (i, j) ∧ i ∈ C ∧ j ∈ C

noncomputable def maskTickIndicator (init : Cfg L K)
    (C : Finset (Fin init.card)) (t : ℕ) (ω : Ω L K) : ℝ := by
  classical
  exact if maskContact init C (t + 1) ω then 1 else 0

def maskTickCount (init : Cfg L K) (C : Finset (Fin init.card))
    (s N : ℕ) (ω : Ω L K) : ℝ :=
  bernoulliCount (fun u => maskTickIndicator init C (s + u)) N ω

noncomputable def maskContacts (init : Cfg L K) (C : Finset (Fin init.card))
    (u v : ℕ) (ω : Ω L K) : ℕ := by
  classical
  exact ((Finset.Ioc u v).filter (fun k => maskContact init C k ω)).card

theorem goodPairs_clockMask_card (f : Fin m → AgentState L K)
    (C : Finset (Fin m)) :
    (goodPairs (fun _ i j => i ∈ C ∧ j ∈ C) f).card =
      C.card * (C.card - 1) := by
  classical
  have h :
      goodPairs (fun _ i j => i ∈ C ∧ j ∈ C) f = C.offDiag := by
    ext ij
    simp [goodPairs, Finset.mem_offDiag, and_assoc, and_left_comm, and_comm]
  rw [h, Finset.offDiag_card, Nat.mul_sub_one]

theorem maskTickIndicator_stronglyMeasurable (init : Cfg L K)
    (C : Finset (Fin init.card)) (t : ℕ) :
    StronglyMeasurable[pairLogFiltration L K (t + 1)]
      (maskTickIndicator init C t) := by
  have h := stronglyMeasurable_aux_pair_indicator init virtualRule
    (fun _ i j => i ∈ C ∧ j ∈ C) t
  convert h using 1
  funext ω
  simp only [maskTickIndicator, maskContact]
  split_ifs <;> rfl

theorem maskTickIndicator_zero_one (init : Cfg L K)
    (C : Finset (Fin init.card)) (t : ℕ) :
    ∀ ω, maskTickIndicator init C t ω = 0 ∨ maskTickIndicator init C t ω = 1 := by
  classical
  intro ω
  by_cases h : maskContact init C (t + 1) ω <;>
    simp [maskTickIndicator, h]

theorem maskTickIndicator_conditional_law (init : Cfg L K)
    (hc : 2 ≤ init.card) (C : Finset (Fin init.card)) (t : ℕ) :
    (law init)[maskTickIndicator init C t | pairLogFiltration L K t] =ᵐ[law init]
      fun _ => clockMaskRate init.card C.card := by
  have h := aux_pair_conditional_probability init hc virtualRule
    (fun _ i j => i ∈ C ∧ j ∈ C) t
  refine (condExp_congr_ae (Filter.EventuallyEq.of_eq ?_)).trans (h.trans ?_)
  · funext ω
    simp only [maskTickIndicator, maskContact]
    split_ifs <;> rfl
  · filter_upwards with ω
    simp [goodPairs_clockMask_card, clockMaskRate]

theorem clockMaskRate_eq_real (m C : ℕ) (hC : 1 ≤ C) :
    clockMaskRate m C = (C : ℝ) * ((C : ℝ) - 1) /
      ((m : ℝ) * ((m : ℝ) - 1)) := by
  simp only [clockMaskRate, Nat.cast_mul, Nat.cast_sub hC, Nat.cast_one]

/-- The conversion from Clock-parallel time to global parallel time has
factor (m-1)/(C-1). -/
theorem clockMaskRate_parallel_ratio (m C : ℕ) (hm : 2 ≤ m) (hC : 2 ≤ C) :
    ((C : ℝ) / (m : ℝ)) / clockMaskRate m C =
      ((m : ℝ) - 1) / ((C : ℝ) - 1) := by
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hCR : (2 : ℝ) ≤ (C : ℝ) := by exact_mod_cast hC
  have hm0 : (m : ℝ) ≠ 0 := by linarith
  have hC0 : (C : ℝ) ≠ 0 := by linarith
  have hm1 : (m : ℝ) - 1 ≠ 0 := by linarith
  have hC1 : (C : ℝ) - 1 ≠ 0 := by linarith
  rw [clockMaskRate_eq_real m C (by omega)]
  field_simp [hm0, hC0, hm1, hC1] <;> ring

theorem maskTickCount_succ (init : Cfg L K) (C : Finset (Fin init.card))
    (s N : ℕ) (ω : Ω L K) :
    maskTickCount init C s (N + 1) ω =
      maskTickCount init C s N ω + maskTickIndicator init C (s + N) ω := by
  simp only [maskTickCount, bernoulliCount, Finset.sum_range_succ]

theorem maskTickCount_eq_contacts (init : Cfg L K)
    (C : Finset (Fin init.card)) (s N : ℕ) (ω : Ω L K) :
    maskTickCount init C s N ω = (maskContacts init C s (s + N) ω : ℝ) := by
  classical
  induction N with
  | zero =>
      simp [maskTickCount, bernoulliCount, maskContacts]
  | succ N ih =>
      have hinterval :
          Finset.Ioc s (s + (N + 1)) =
            insert (s + N + 1) (Finset.Ioc s (s + N)) := by
        ext k
        simp only [Finset.mem_Ioc, Finset.mem_insert]
        omega
      have hnot :
          s + N + 1 ∉
            (Finset.Ioc s (s + N)).filter (fun k => maskContact init C k ω) := by
        simp only [Finset.mem_filter, Finset.mem_Ioc]
        omega
      rw [maskTickCount_succ, ih]
      change (maskContacts init C s (s + N) ω : ℝ) +
        (if maskContact init C (s + N + 1) ω then 1 else 0) = _
      by_cases h : maskContact init C (s + N + 1) ω <;>
        simp [maskContacts, hinterval, Finset.filter_insert, h, hnot, add_comm]

/-- A fixed label mask has its Bernoulli exponential tail after every
deterministic prefix, on the original law. -/
theorem prefix_maskTick_exponential_tail (init : Cfg L K)
    (hc : 2 ≤ init.card) (C : Finset (Fin init.card)) (s N : ℕ)
    (E : Set (Ω L K)) (hE : MeasurableSet[pairLogFiltration L K s] E)
    (θ r : ℝ) :
    (law init).real (E ∩ {ω | θ * r ≤ θ * maskTickCount init C s N ω}) ≤
      Real.exp ((Real.exp θ - 1) * clockMaskRate init.card C.card * (N : ℝ) -
        θ * r) * (law init).real E := by
  have hI : ∀ u,
      StronglyMeasurable[shiftedFiltration (pairLogFiltration L K) s (u + 1)]
        (maskTickIndicator init C (s + u)) := by
    intro u
    simpa only [shiftedFiltration_apply, Nat.add_assoc] using
      maskTickIndicator_stronglyMeasurable init C (s + u)
  have hz : ∀ u, ∀ᵐ ω ∂law init,
      maskTickIndicator init C (s + u) ω = 0 ∨
        maskTickIndicator init C (s + u) ω = 1 :=
    fun u => ae_of_all _ (maskTickIndicator_zero_one init C (s + u))
  have hcond : ∀ u,
      (law init)[maskTickIndicator init C (s + u) |
        shiftedFiltration (pairLogFiltration L K) s u] =ᵐ[law init]
        fun _ => clockMaskRate init.card C.card :=
    fun u => maskTickIndicator_conditional_law init hc C (s + u)
  have hEs : MeasurableSet[shiftedFiltration (pairLogFiltration L K) s 0] E := by
    simpa only [shiftedFiltration_apply, Nat.add_zero] using hE
  exact prefix_bernoulli_exponential_tail hI hz hcond E hEs θ r N

theorem log_four_thirds_lower : (5 / 18 : ℝ) ≤ Real.log (4 / 3 : ℝ) := by
  have h := Real.le_log_one_add_of_nonneg
    (x := (1 / 3 : ℝ)) (by norm_num)
  norm_num at h
  linarith

/-- PHASE3 P10, upper contact tail: expected contacts at most 3r/4. -/
theorem prefix_maskTick_upper_tail (init : Cfg L K)
    (hc : 2 ≤ init.card) (C : Finset (Fin init.card)) (s N : ℕ)
    (E : Set (Ω L K)) (hE : MeasurableSet[pairLogFiltration L K s] E)
    (r : ℝ) (hr : 0 ≤ r)
    (hmean : clockMaskRate init.card C.card * (N : ℝ) ≤ 3 * r / 4) :
    (law init).real (E ∩ {ω | r ≤ maskTickCount init C s N ω}) ≤
      Real.exp (-r / 36) * (law init).real E := by
  have hθ : 0 ≤ Real.log (4 / 3 : ℝ) := by
    linarith [log_four_thirds_lower]
  have hsub : E ∩ {ω | r ≤ maskTickCount init C s N ω} ⊆
      E ∩ {ω | Real.log (4 / 3 : ℝ) * r ≤
        Real.log (4 / 3 : ℝ) * maskTickCount init C s N ω} := by
    rintro ω ⟨hω, hrω⟩
    exact ⟨hω, mul_le_mul_of_nonneg_left hrω hθ⟩
  have htail := prefix_maskTick_exponential_tail init hc C s N E hE
    (Real.log (4 / 3 : ℝ)) r
  have hlog := mul_le_mul_of_nonneg_right log_four_thirds_lower hr
  have hexp :
      (Real.exp (Real.log (4 / 3 : ℝ)) - 1) *
          clockMaskRate init.card C.card * (N : ℝ) -
        Real.log (4 / 3 : ℝ) * r ≤ -r / 36 := by
    rw [Real.exp_log (by norm_num : (0 : ℝ) < 4 / 3)]
    nlinarith
  exact (measureReal_mono hsub).trans (htail.trans
    (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hexp)
      ENNReal.toReal_nonneg))

/-- PHASE3 P10, lower contact tail: expected contacts at least 2r. -/
theorem prefix_maskTick_lower_tail (init : Cfg L K)
    (hc : 2 ≤ init.card) (C : Finset (Fin init.card)) (s N : ℕ)
    (E : Set (Ω L K)) (hE : MeasurableSet[pairLogFiltration L K s] E)
    (r : ℝ) (hr : 0 ≤ r)
    (hmean : 2 * r ≤ clockMaskRate init.card C.card * (N : ℝ)) :
    (law init).real (E ∩ {ω | maskTickCount init C s N ω < r}) ≤
      Real.exp (-r / 4) * (law init).real E := by
  have hθ : -Real.log (2 : ℝ) ≤ 0 :=
    neg_nonpos.mpr (Real.log_nonneg (by norm_num))
  have hsub : E ∩ {ω | maskTickCount init C s N ω < r} ⊆
      E ∩ {ω | (-Real.log (2 : ℝ)) * r ≤
        (-Real.log (2 : ℝ)) * maskTickCount init C s N ω} := by
    rintro ω ⟨hω, hrω⟩
    exact ⟨hω, mul_le_mul_of_nonpos_left hrω.le hθ⟩
  have htail := prefix_maskTick_exponential_tail init hc C s N E hE
    (-Real.log (2 : ℝ)) r
  have hexact : Real.exp (-Real.log (2 : ℝ)) = (1 : ℝ) / 2 := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have hlog : Real.log (2 : ℝ) ≤ (3 / 4 : ℝ) := by
    linarith [PhaseThreeModel.Numeric.log_two_bounds.2]
  have hprod := mul_le_mul_of_nonneg_right hlog hr
  have hexp :
      (Real.exp (-Real.log (2 : ℝ)) - 1) *
          clockMaskRate init.card C.card * (N : ℝ) -
        (-Real.log (2 : ℝ)) * r ≤ -r / 4 := by
    rw [hexact]
    nlinarith
  exact (measureReal_mono hsub).trans (htail.trans
    (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hexp)
      ENNReal.toReal_nonneg))

/-- Exact conversion to the reviewed physical-label contact count. -/
theorem maskContacts_seed_eq_stageEvent {n : ℕ} (init : InputCfg n)
    (ω : InputLog n) (S u v : ℕ) :
    maskContacts init (clockSet (labelsAt init ω S)) u v ω =
      StageEventSpec.clockContacts init ω S u v := by
  classical
  simp only [maskContacts, maskContact, clockSet, Finset.mem_filter,
    Finset.mem_univ, true_and, StageEventSpec.clockContacts,
    StageEventSpec.clockContact, StageEventSpec.fixedRole]

theorem prefix_stageEvent_clockContacts_upper_tail {n : ℕ}
    (init : InputCfg n) (hc : 2 ≤ init.card)
    (C : Finset (Fin init.card)) (S s N : ℕ)
    (E : Set (InputLog n))
    (hE : MeasurableSet[pairLogFiltration _ _ s] E)
    (hmask : ∀ ω ∈ E, clockSet (labelsAt init ω S) = C)
    (r : ℝ) (hr : 0 ≤ r)
    (hmean : clockMaskRate init.card C.card * (N : ℝ) ≤ 3 * r / 4) :
    (law init).real
        (E ∩ {ω | r ≤ (StageEventSpec.clockContacts init ω S s (s + N) : ℝ)}) ≤
      Real.exp (-r / 36) * (law init).real E := by
  have hsub : E ∩ {ω | r ≤
        (StageEventSpec.clockContacts init ω S s (s + N) : ℝ)} ⊆
      E ∩ {ω | r ≤ maskTickCount init C s N ω} := by
    rintro ω ⟨hω, hrω⟩
    refine ⟨hω, ?_⟩
    simp only [Set.mem_setOf_eq] at hrω ⊢
    rw [maskTickCount_eq_contacts, ← hmask ω hω, maskContacts_seed_eq_stageEvent]
    exact hrω
  exact (measureReal_mono hsub).trans
    (prefix_maskTick_upper_tail init hc C s N E hE r hr hmean)

theorem prefix_stageEvent_clockContacts_lower_tail {n : ℕ}
    (init : InputCfg n) (hc : 2 ≤ init.card)
    (C : Finset (Fin init.card)) (S s N : ℕ)
    (E : Set (InputLog n))
    (hE : MeasurableSet[pairLogFiltration _ _ s] E)
    (hmask : ∀ ω ∈ E, clockSet (labelsAt init ω S) = C)
    (r : ℝ) (hr : 0 ≤ r)
    (hmean : 2 * r ≤ clockMaskRate init.card C.card * (N : ℝ)) :
    (law init).real
        (E ∩ {ω | (StageEventSpec.clockContacts init ω S s (s + N) : ℝ) < r}) ≤
      Real.exp (-r / 4) * (law init).real E := by
  have hsub : E ∩ {ω |
        (StageEventSpec.clockContacts init ω S s (s + N) : ℝ) < r} ⊆
      E ∩ {ω | maskTickCount init C s N ω < r} := by
    rintro ω ⟨hω, hrω⟩
    refine ⟨hω, ?_⟩
    simp only [Set.mem_setOf_eq] at hrω ⊢
    rw [maskTickCount_eq_contacts, ← hmask ω hω, maskContacts_seed_eq_stageEvent]
    exact hrω
  exact (measureReal_mono hsub).trans
    (prefix_maskTick_lower_tail init hc C s N E hE r hr hmean)


/-! ## Original-law ENNReal versions -/

/-- For a finite measure, a real-valued weighted estimate is exactly the
corresponding ENNReal estimate. The events need not be measurable. -/
theorem measure_le_of_real_weighted_bound {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (A E : Set α) (r : ℝ)
    (hr : 0 ≤ r) (h : μ.real A ≤ r * μ.real E) :
    μ A ≤ ENNReal.ofReal r * μ E := by
  calc
    μ A = ENNReal.ofReal ((μ A).toReal) :=
      (ENNReal.ofReal_toReal (measure_ne_top μ A)).symm
    _ ≤ ENNReal.ofReal (r * (μ E).toReal) := ENNReal.ofReal_le_ofReal h
    _ = ENNReal.ofReal r * μ E := by
      rw [ENNReal.ofReal_mul hr, ENNReal.ofReal_toReal (measure_ne_top μ E)]

theorem prefix_stageEvent_clockContacts_upper_tail_ennreal {n : ℕ}
    (init : InputCfg n) (hc : 2 ≤ init.card)
    (C : Finset (Fin init.card)) (S s N : ℕ)
    (E : Set (InputLog n))
    (hE : MeasurableSet[pairLogFiltration _ _ s] E)
    (hmask : ∀ ω ∈ E, clockSet (labelsAt init ω S) = C)
    (r : ℝ) (hr : 0 ≤ r)
    (hmean : clockMaskRate init.card C.card * (N : ℝ) ≤ 3 * r / 4) :
    law init
        (E ∩ {ω | r ≤ (StageEventSpec.clockContacts init ω S s (s + N) : ℝ)}) ≤
      ENNReal.ofReal (Real.exp (-r / 36)) * law init E :=
  measure_le_of_real_weighted_bound (law init) _ E _ (Real.exp_nonneg _)
    (prefix_stageEvent_clockContacts_upper_tail
      init hc C S s N E hE hmask r hr hmean)

theorem prefix_stageEvent_clockContacts_lower_tail_ennreal {n : ℕ}
    (init : InputCfg n) (hc : 2 ≤ init.card)
    (C : Finset (Fin init.card)) (S s N : ℕ)
    (E : Set (InputLog n))
    (hE : MeasurableSet[pairLogFiltration _ _ s] E)
    (hmask : ∀ ω ∈ E, clockSet (labelsAt init ω S) = C)
    (r : ℝ) (hr : 0 ≤ r)
    (hmean : 2 * r ≤ clockMaskRate init.card C.card * (N : ℝ)) :
    law init
        (E ∩ {ω | (StageEventSpec.clockContacts init ω S s (s + N) : ℝ) < r}) ≤
      ENNReal.ofReal (Real.exp (-r / 4)) * law init E :=
  measure_le_of_real_weighted_bound (law init) _ E _ (Real.exp_nonneg _)
    (prefix_stageEvent_clockContacts_lower_tail
      init hc C S s N E hE hmask r hr hmean)

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockThinning

end
