-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockNextFrontBirth.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockFirstPositive

/-!
# Birth of the next front from an observed finite front

A frozen mask of labels already at level ell stays at or above ell on the
homogeneous virtual continuation. If level ell+1 is still empty, a contact
between any two frozen labels creates its first positive element. The
fixed-mask original-law MGF therefore gives the prefix-weighted failure
exp(-q_A N/2), with q_A=|A|(|A|-1)/(m(m-1)).

The infinite-birth failure has measure zero whenever the observed front
contains at least two labels. No shape barrier or future-success event is
used. Pointwise Clock-minute monotonicity is proved here; monotonicity of
front counts alone would not justify freezing the labels.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal BigOperators MeasureTheory ProbabilityTheory

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockNextFrontBirth

open TimeTheorem PairLog PairLogAuxiliary PhaseThreeScalar
  PhaseThreeClockVirtual PhaseThreeClockGatedLaw PhaseThreeClockGatedLevelOne
  PhaseThreeClockEmbedding PhaseThreeClockEmbeddingBridge
  PhaseThreeClockThinning PhaseThreeClockPrefixTails PhaseThreeClockFirstPositive

variable {L m : ℕ}

theorem homogeneousStart_of_time (init : Cfg L 256) (ω : Ω L 256)
    (u : ℕ) (hu : HomogeneousStart init ω u) (t : ℕ) (hut : u ≤ t) :
    HomogeneousStart init ω t :=
  ⟨virtualLabels_phase_three_of_time init ω u hu.1 t hut,
    virtualLabels_carrier_of_time init ω u hu.2 t hut⟩

theorem virtualRule_clock_left_effMinute_mono (s t : AgentState L 256)
    (hs : s.phase.val = 3) (ht : t.phase.val = 3)
    (hr : s.role = .clock) (hsmall : s.smallBias.val = 3) :
    effMinute s ≤ effMinute (virtualRule s t).1 := by
  by_cases htr : t.role = .clock
  · obtain ⟨-, -, hs', -, hminute, -⟩ :=
      virtualRule_active_clock_pair s t hs ht hr htr
    have hm : s.minute.val ≤ (virtualRule s t).1.minute.val := by
      rw [hminute]
      split_ifs with hne hcap
      · exact le_max_left _ _
      · omega
      · exact le_rfl
    simpa only [effMinute, hs, hs', le_refl, if_true] using hm
  · have hepi := ClockRealKernel.phaseEpidemicUpdate_eq_self_p3 s t hs ht
    have hnb : (phaseEpidemicUpdate L 256 s t).1.phase.val ≠ 10 ∧
        (phaseEpidemicUpdate L 256 s t).2.phase.val ≠ 10 := by
      rw [hepi]
      simp [hs, ht]
    exact (virtualRule_clock_nonclock s t
      ⟨hr, by omega, hs.le, hsmall⟩ htr (by omega) ht.le hnb).2.1.ge

theorem virtualRule_clock_right_effMinute_mono (s t : AgentState L 256)
    (hs : s.phase.val = 3) (ht : t.phase.val = 3)
    (hr : t.role = .clock) (hsmall : t.smallBias.val = 3) :
    effMinute t ≤ effMinute (virtualRule s t).2 := by
  by_cases hsr : s.role = .clock
  · obtain ⟨-, -, -, ht', -, hminute⟩ :=
      virtualRule_active_clock_pair s t hs ht hsr hr
    have hm : t.minute.val ≤ (virtualRule s t).2.minute.val := by
      rw [hminute]
      split_ifs with hne
      · exact le_max_right _ _
      · exact le_rfl
    simpa only [effMinute, ht, ht', le_refl, if_true] using hm
  · have hepi := ClockRealKernel.phaseEpidemicUpdate_eq_self_p3 s t hs ht
    have hnb : (phaseEpidemicUpdate L 256 s t).1.phase.val ≠ 10 ∧
        (phaseEpidemicUpdate L 256 s t).2.phase.val ≠ 10 := by
      rw [hepi]
      simp [hs, ht]
    exact (virtualRule_nonclock_clock s t
      ⟨hr, by omega, ht.le, hsmall⟩ hsr (by omega) hs.le hnb).2.1.ge

theorem ruleUpdate_clock_effMinute_mono (f : Fin m → AgentState L 256)
    (hphase : ∀ k, (f k).phase.val = 3)
    (hcarrier : ∀ k, nonMainCarrierSmallBiasZeroAgent (f k))
    (i j k : Fin m) (hk : (f k).role = .clock) :
    effMinute (f k) ≤ effMinute (ruleUpdate virtualRule f i j k) := by
  by_cases hkj : k = j
  · subst k
    simpa only [ruleUpdate, Function.update_self] using
      virtualRule_clock_right_effMinute_mono (f i) (f j) (hphase i) (hphase j)
        hk (hcarrier j (Or.inr (Or.inr hk)))
  · by_cases hki : k = i
    · subst k
      simpa only [ruleUpdate, Function.update_of_ne hkj, Function.update_self] using
        virtualRule_clock_left_effMinute_mono (f i) (f j) (hphase i) (hphase j)
          hk (hcarrier i (Or.inr (Or.inr hk)))
    · simp only [ruleUpdate, Function.update_of_ne hkj, Function.update_of_ne hki,
        le_refl]

theorem clock_effMinute_step_mono (init : Cfg L 256) (ω : Ω L 256)
    (t : ℕ) (ht : HomogeneousStart init ω t)
    (i : Fin init.card) (hi : (virtualLabels init ω t i).role = .clock) :
    effMinute (virtualLabels init ω t i) ≤
      effMinute (virtualLabels init ω (t + 1) i) := by
  rw [virtualLabels_succ]
  cases hd : drawLabels init ω (t + 1) with
  | none => exact le_rfl
  | some ij =>
      rcases ij with ⟨j, k⟩
      exact ruleUpdate_clock_effMinute_mono _ ht.1 ht.2 j k i hi

theorem aboveSet_step_subset (init : Cfg L 256) (ω : Ω L 256)
    (t : ℕ) (ht : HomogeneousStart init ω t) (ℓ : ℕ) :
    aboveSet (virtualLabels init ω t) ℓ ⊆
      aboveSet (virtualLabels init ω (t + 1)) ℓ := by
  intro i hi
  simp only [aboveSet, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  refine ⟨?_, hi.2.trans (clock_effMinute_step_mono init ω t ht i hi.1)⟩
  rw [roles_fixed_from_homogeneous init ω t ht (t + 1) (by omega)]
  exact hi.1

theorem aboveSet_mono_from_homogeneous (init : Cfg L 256) (ω : Ω L 256)
    (u : ℕ) (hu : HomogeneousStart init ω u) (s t : ℕ)
    (hus : u ≤ s) (hst : s ≤ t) (ℓ : ℕ) :
    aboveSet (virtualLabels init ω s) ℓ ⊆
      aboveSet (virtualLabels init ω t) ℓ := by
  induction t, hst using Nat.le_induction with
  | base => exact fun _ hi => hi
  | succ t hst ih =>
      intro i hi
      exact aboveSet_step_subset init ω t
        (homogeneousStart_of_time init ω u hu t (hus.trans hst)) ℓ (ih hi)

theorem effMinute_lt_of_front_zero (f : Fin m → AgentState L 256)
    (r : ℕ) (hz : frontCount f r = 0)
    (i : Fin m) (hi : (f i).role = .clock) :
    effMinute (f i) < r := by
  by_contra hn
  have hip : i ∈ aboveSet f r := by
    simp only [aboveSet, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hi, by omega⟩
  have hp : 0 < frontCount f r := Finset.card_pos.mpr ⟨i, hip⟩
  omega

theorem gatedTick_succ_of_zero_front (f : Fin m → AgentState L 256)
    (ℓ : ℕ) (hphase : ∀ k, (f k).phase.val = 3)
    (hz : frontCount f (ℓ + 1) = 0) (i j : Fin m)
    (hi : i ∈ aboveSet f ℓ) (hj : j ∈ aboveSet f ℓ) :
    GatedTick (ℓ + 1) f i j := by
  simp only [aboveSet, Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
  have him : effMinute (f i) = ℓ := by
    have h := effMinute_lt_of_front_zero f (ℓ + 1) hz i hi.1
    omega
  have hjm : effMinute (f j) = ℓ := by
    have h := effMinute_lt_of_front_zero f (ℓ + 1) hz j hj.1
    omega
  refine ⟨Or.inr (Or.inr ⟨?_, ?_⟩), Or.inl (hphase i).ge⟩
  · simp [exactSet, hi.1, him]
  · simp [exactSet, hj.1, hjm]

theorem frozenFrontTickCount_zero_of_next_front_zero (init : Cfg L 256)
    (ω : Ω L 256) (A : Finset (Fin init.card)) (u N ℓ : ℕ)
    (hcap : ℓ + 1 ≤ 256 * (L + 1))
    (hu : HomogeneousStart init ω u)
    (hmask : A ⊆ aboveSet (virtualLabels init ω u) ℓ)
    (hzero : frontCount (virtualLabels init ω (u + N)) (ℓ + 1) = 0) :
    maskTickCount init A u N ω = 0 := by
  classical
  unfold maskTickCount bernoulliCount
  apply Finset.sum_eq_zero
  intro t ht
  have htN : t < N := Finset.mem_range.mp ht
  have henv := homogeneous_clockEnvironment init ω u hu (u + t) (by omega)
  have hnext := homogeneous_clockEnvironment init ω u hu (u + t + 1) (by omega)
  have hz : frontCount (virtualLabels init ω (u + t)) (ℓ + 1) = 0 := by
    have h := frontCount_mono_from_homogeneous init ω u hu (u + t) (u + N)
      (by omega) (by omega) (ℓ + 1) (by omega) hcap
    omega
  by_cases hcontact : maskContact init A (u + t + 1) ω
  · exfalso
    obtain ⟨i, j, hd, hi, hj⟩ := hcontact
    have hsub := aboveSet_mono_from_homogeneous init ω u hu u (u + t)
      le_rfl (by omega) ℓ
    have hg := gatedTick_succ_of_zero_front (virtualLabels init ω (u + t)) ℓ
      (virtualLabels_phase_three_of_time init ω u hu.1 (u + t) (by omega))
      hz i j (hsub (hmask hi)) (hsub (hmask hj))
    have hstep := frontCount_virtualLabels_succ_of_phase_range init ω (u + t) i j hd
      henv.phase_range (fun k hk => (henv.clock_regime k hk).small)
      (fun k => (hnext.phase_range k).2) (ℓ + 1) (by omega) hcap
    rw [if_pos hg, hz] at hstep
    have hle := frontCount_mono_from_homogeneous init ω u hu (u + t + 1) (u + N)
      (by omega) (by omega) (ℓ + 1) (by omega) hcap
    omega
  · simp only [maskTickIndicator, if_neg hcontact]

theorem next_front_failure_measurable (init : Cfg L 256) (u N ℓ : ℕ)
    (E : Set (Ω L 256)) (hE : MeasurableSet[pairLogFiltration L 256 u] E) :
    MeasurableSet[pairLogFiltration L 256 (u + N)]
      (E ∩ {ω | frontCount (virtualLabels init ω (u + N)) (ℓ + 1) = 0}) := by
  refine (((pairLogFiltration L 256).mono (by omega : u ≤ u + N)) _ hE).inter ?_
  exact (show MeasurableSet {f : Fin init.card → AgentState L 256 |
      frontCount f (ℓ + 1) = 0} from (Set.to_countable _).measurableSet).preimage
        (measurable_virtualLabels init (u + N))

theorem next_front_prefix_real_tail (init : Cfg L 256)
    (hc : 2 ≤ init.card) (A : Finset (Fin init.card)) (u N ℓ : ℕ)
    (hcap : ℓ + 1 ≤ 256 * (L + 1))
    (E : Set (Ω L 256)) (hE : MeasurableSet[pairLogFiltration L 256 u] E)
    (hstart : ∀ ω ∈ E, HomogeneousStart init ω u)
    (hmask : ∀ ω ∈ E, A ⊆ aboveSet (virtualLabels init ω u) ℓ) :
    (law init).real (E ∩
      {ω | frontCount (virtualLabels init ω (u + N)) (ℓ + 1) = 0}) ≤
      Real.exp (-clockMaskRate init.card A.card * (N : ℝ) / 2) * (law init).real E := by
  have hsub : E ∩ {ω | frontCount (virtualLabels init ω (u + N)) (ℓ + 1) = 0} ⊆
      E ∩ {ω | (-Real.log (2 : ℝ)) * 0 ≤
        (-Real.log (2 : ℝ)) * maskTickCount init A u N ω} := by
    rintro ω ⟨hω, hz⟩
    refine ⟨hω, ?_⟩
    simp only [Set.mem_setOf_eq, frozenFrontTickCount_zero_of_next_front_zero init ω A u N ℓ
      hcap (hstart ω hω) (hmask ω hω) hz, mul_zero, le_refl]
  have ht := prefix_maskTick_exponential_tail init hc A u N E hE
    (-Real.log (2 : ℝ)) 0
  have hexp : Real.exp (-Real.log (2 : ℝ)) = (1 : ℝ) / 2 := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have harg :
      (Real.exp (-Real.log (2 : ℝ)) - 1) * clockMaskRate init.card A.card * (N : ℝ) -
          (-Real.log (2 : ℝ)) * 0 =
        -clockMaskRate init.card A.card * (N : ℝ) / 2 := by
    rw [hexp]
    ring
  exact (measureReal_mono hsub).trans (by simpa only [harg] using ht)

theorem next_front_prefix_tail (init : Cfg L 256)
    (hc : 2 ≤ init.card) (A : Finset (Fin init.card)) (u N ℓ : ℕ)
    (hcap : ℓ + 1 ≤ 256 * (L + 1))
    (E : Set (Ω L 256)) (hE : MeasurableSet[pairLogFiltration L 256 u] E)
    (hstart : ∀ ω ∈ E, HomogeneousStart init ω u)
    (hmask : ∀ ω ∈ E, A ⊆ aboveSet (virtualLabels init ω u) ℓ) :
    law init (E ∩ {ω | frontCount (virtualLabels init ω (u + N)) (ℓ + 1) = 0}) ≤
      ENNReal.ofReal (Real.exp (-clockMaskRate init.card A.card * (N : ℝ) / 2)) *
        law init E :=
  measure_le_of_real_weighted_bound (law init) _ E _ (Real.exp_nonneg _)
    (next_front_prefix_real_tail init hc A u N ℓ hcap E hE hstart hmask)

theorem next_front_never_positive_prefix_null (init : Cfg L 256)
    (hc : 2 ≤ init.card) (A : Finset (Fin init.card)) (hA : 2 ≤ A.card)
    (u ℓ : ℕ) (hcap : ℓ + 1 ≤ 256 * (L + 1))
    (E : Set (Ω L 256)) (hE : MeasurableSet[pairLogFiltration L 256 u] E)
    (hstart : ∀ ω ∈ E, HomogeneousStart init ω u)
    (hmask : ∀ ω ∈ E, A ⊆ aboveSet (virtualLabels init ω u) ℓ) :
    law init (E ∩ {ω | ∀ N, frontCount
      (virtualLabels init ω (u + N)) (ℓ + 1) = 0}) = 0 := by
  let D : Set (Ω L 256) := E ∩ {ω | ∀ N, frontCount
    (virtualLabels init ω (u + N)) (ℓ + 1) = 0}
  let a : ℝ := (law init).real D
  have hmR : (2 : ℝ) ≤ (init.card : ℝ) := by exact_mod_cast hc
  have hAR : (2 : ℝ) ≤ (A.card : ℝ) := by exact_mod_cast hA
  have hq : 0 < clockMaskRate init.card A.card := by
    rw [clockMaskRate_eq_real init.card A.card (by omega)]
    exact div_pos (mul_pos (by linarith) (by linarith))
      (mul_pos (by linarith) (by linarith))
  have hEprob : (law init).real E ≤ 1 := by
    calc
      (law init).real E ≤ (law init).real Set.univ :=
        measureReal_mono (Set.subset_univ E)
      _ = 1 := by simp
  have hbound (N : ℕ) :
      a ≤ Real.exp (-clockMaskRate init.card A.card * (N : ℝ) / 2) := by
    have hsub : D ⊆ E ∩
        {ω | frontCount (virtualLabels init ω (u + N)) (ℓ + 1) = 0} :=
      fun _ hω => ⟨hω.1, hω.2 N⟩
    have hmul := mul_le_mul_of_nonneg_left hEprob
      (Real.exp_nonneg (-clockMaskRate init.card A.card * (N : ℝ) / 2))
    rw [mul_one] at hmul
    exact (measureReal_mono hsub).trans
      ((next_front_prefix_real_tail init hc A u N ℓ hcap E hE hstart hmask).trans hmul)
  have ha : a = 0 := by
    apply le_antisymm ?_ (by dsimp only [a]; positivity)
    by_contra hnot
    have hpos : 0 < a := lt_of_not_ge hnot
    obtain ⟨N, hN⟩ := exists_nat_gt (-2 * Real.log a / clockMaskRate init.card A.card)
    have hprod : -2 * Real.log a < (N : ℝ) * clockMaskRate init.card A.card :=
      (div_lt_iff₀ hq).1 hN
    have harg : -clockMaskRate init.card A.card * (N : ℝ) / 2 < Real.log a := by
      nlinarith
    have hexp : Real.exp (-clockMaskRate init.card A.card * (N : ℝ) / 2) < a := by
      simpa only [Real.exp_log hpos] using Real.exp_lt_exp.mpr harg
    exact (not_lt_of_ge (hbound N)) hexp
  calc
    law init (E ∩ {ω | ∀ N, frontCount
        (virtualLabels init ω (u + N)) (ℓ + 1) = 0}) = ENNReal.ofReal a :=
      (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
    _ = 0 := by rw [ha, ENNReal.ofReal_zero]

/-- Remove the random mask by a finite, hence countable, null union.
The initial front is observed at u; no future event is used as a prefix. -/
theorem next_front_never_positive_null (init : Cfg L 256)
    (hc : 2 ≤ init.card) (u ℓ : ℕ) (hcap : ℓ + 1 ≤ 256 * (L + 1)) :
    law init {ω | HomogeneousStart init ω u ∧
      2 ≤ frontCount (virtualLabels init ω u) ℓ ∧
      ¬ ∃ N, 0 < frontCount (virtualLabels init ω (u + N)) (ℓ + 1)} = 0 := by
  classical
  let E : Finset (Fin init.card) → Set (Ω L 256) :=
    fun A => {ω | HomogeneousStart init ω u ∧
      A ⊆ aboveSet (virtualLabels init ω u) ℓ}
  let D : Finset (Fin init.card) → Set (Ω L 256) :=
    fun A => E A ∩ {ω | 2 ≤ A.card ∧
      ¬ ∃ N, 0 < frontCount (virtualLabels init ω (u + N)) (ℓ + 1)}
  have hEm (A : Finset (Fin init.card)) :
      MeasurableSet[pairLogFiltration L 256 u] (E A) := by
    exact (show MeasurableSet {f : Fin init.card → AgentState L 256 |
        ((∀ i, (f i).phase.val = 3) ∧
          ∀ i, nonMainCarrierSmallBiasZeroAgent (f i)) ∧ A ⊆ aboveSet f ℓ} from
      (Set.to_countable _).measurableSet).preimage (measurable_virtualLabels init u)
  have hnull (A : Finset (Fin init.card)) : law init (D A) = 0 := by
    by_cases hA : 2 ≤ A.card
    · apply le_antisymm ?_ zero_le
      calc
        law init (D A) ≤ law init (E A ∩
            {ω | ∀ N, frontCount (virtualLabels init ω (u + N)) (ℓ + 1) = 0}) := by
          apply measure_mono
          rintro ω ⟨he, -, hnever⟩
          refine ⟨he, fun N => ?_⟩
          by_contra hn
          exact hnever ⟨N, by omega⟩
        _ = 0 := next_front_never_positive_prefix_null init hc A hA u ℓ hcap
          (E A) (hEm A) (fun _ hω => hω.1) (fun _ hω => hω.2)
    · simp only [D, hA, false_and, Set.setOf_false, Set.inter_empty, measure_empty]
  apply le_antisymm ?_ zero_le
  calc
    law init {ω | HomogeneousStart init ω u ∧
        2 ≤ frontCount (virtualLabels init ω u) ℓ ∧
        ¬ ∃ N, 0 < frontCount (virtualLabels init ω (u + N)) (ℓ + 1)} ≤
        law init (⋃ A, D A) := by
      apply measure_mono
      rintro ω ⟨hu, hcount, hnever⟩
      exact Set.mem_iUnion.mpr
        ⟨aboveSet (virtualLabels init ω u) ℓ, ⟨hu, fun _ hi => hi⟩, hcount, hnever⟩
    _ ≤ ∑' A, law init (D A) := measure_iUnion_le _
    _ = 0 := by simp only [hnull, tsum_zero]

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockNextFrontBirth

end
