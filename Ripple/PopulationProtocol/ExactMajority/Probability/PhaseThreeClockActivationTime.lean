-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockActivationTime.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockActivationTails
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockActivationSeed
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockFirstPositiveSplice

/-!
# The genuine virtual full-activation passage and its observed fibres

The passage is the first absolute raw time at or after s at which every
label has phase at least three. Its finite fibres are observable, and its
deadline tail follows from the actual activation drift under law init.

A finite threshold-activation fibre becomes a homogeneous Phase-3 clock
start when the current phase cap is observed on that same fibre. This is
an observed-state guard, not conditioning on future clock success.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal BigOperators MeasureTheory ProbabilityTheory

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockActivationTime

open TimeTheorem PairLog PhaseThreeClockProducer PhaseThreeClockSeedTails
  PhaseThreeClockVirtual PhaseThreeClockGatedLaw PhaseThreeClockActivationLaw
  PhaseThreeClockActivationSeed PhaseThreeClockActivationTails
  PhaseThreeClockEmbeddingBridge
  PhaseThreeClockFirstPositive PhaseThreeClockFirstPositiveSplice
  PhaseThreeClockPrefixTails PhaseThreeClockPotentialTail

variable {L K : ℕ}

open Classical in
/-- The first full threshold-activation time after s, in absolute raw time. -/
def activationTime (init : Cfg L K) (s : ℕ) (ω : Ω L K) : WithTop ℕ :=
  if h : ∃ u, s ≤ u ∧ PhaseThreeClockActivationLaw.activeCount (virtualLabels init ω u) = init.card
  then ((Nat.find h : ℕ) : WithTop ℕ) else ⊤

theorem activationTime_le_iff (init : Cfg L K) (s N : ℕ) (ω : Ω L K) :
    activationTime init s ω ≤ (N : WithTop ℕ) ↔
      ∃ u ≤ N, s ≤ u ∧ PhaseThreeClockActivationLaw.activeCount (virtualLabels init ω u) = init.card := by
  classical
  unfold activationTime
  split_ifs with h
  · constructor
    · intro hle
      have hu : Nat.find h ≤ N := by exact_mod_cast hle
      exact ⟨Nat.find h, hu, Nat.find_spec h⟩
    · rintro ⟨u, hu, hs, ha⟩
      have hle : Nat.find h ≤ N := (Nat.find_min' h ⟨hs, ha⟩).trans hu
      exact_mod_cast hle
  · constructor
    · intro hle
      exact absurd hle (by simp)
    · rintro ⟨u, -, hs, ha⟩
      exact absurd ⟨u, hs, ha⟩ h

theorem seed_le_activationTime (init : Cfg L K) (s : ℕ) (ω : Ω L K) :
    (s : WithTop ℕ) ≤ activationTime init s ω := by
  classical
  unfold activationTime
  split_ifs with h
  · exact_mod_cast (Nat.find_spec h).1
  · exact le_top

theorem activationTime_finite_state (init : Cfg L K) (s u : ℕ) (ω : Ω L K)
    (hu : activationTime init s ω = (u : WithTop ℕ)) :
    s ≤ u ∧ PhaseThreeClockActivationLaw.activeCount (virtualLabels init ω u) = init.card := by
  classical
  unfold activationTime at hu
  split_ifs at hu with h
  · have heq : Nat.find h = u := WithTop.coe_injective hu
    simpa only [heq] using Nat.find_spec h
  · exact absurd hu WithTop.top_ne_coe

theorem activationTime_before (init : Cfg L K) (s u : ℕ) (ω : Ω L K)
    (hu : activationTime init s ω = (u : WithTop ℕ)) :
    ∀ v, s ≤ v → v < u → PhaseThreeClockActivationLaw.activeCount (virtualLabels init ω v) < init.card := by
  intro v hsv hvu
  have hle := activeCount_le_card (virtualLabels init ω v)
  by_contra hnot
  have heq : PhaseThreeClockActivationLaw.activeCount (virtualLabels init ω v) = init.card := by omega
  have hτ := (activationTime_le_iff init s v ω).2 ⟨v, le_rfl, hsv, heq⟩
  rw [hu] at hτ
  have huv : u ≤ v := by exact_mod_cast hτ
  omega

theorem full_activation_measurable (init : Cfg L K) (u : ℕ) :
    MeasurableSet[pairLogFiltration L K u]
      {ω | PhaseThreeClockActivationLaw.activeCount (virtualLabels init ω u) = init.card} :=
  (show MeasurableSet {f : Fin init.card → AgentState L K | PhaseThreeClockActivationLaw.activeCount f = init.card} from
    (Set.to_countable _).measurableSet).preimage (measurable_virtualLabels init u)

theorem activationTime_isStoppingTime (init : Cfg L K) (s : ℕ) :
    IsStoppingTime (pairLogFiltration L K) (activationTime init s) := by
  intro N
  have hm : MeasurableSet[pairLogFiltration L K N]
      (⋃ u, {ω | u ≤ N ∧ s ≤ u ∧ PhaseThreeClockActivationLaw.activeCount (virtualLabels init ω u) = init.card}) := by
    refine MeasurableSet.iUnion fun u => ?_
    by_cases hu : u ≤ N
    · by_cases hs : s ≤ u
      · have ha : MeasurableSet[pairLogFiltration L K N]
            {ω | PhaseThreeClockActivationLaw.activeCount (virtualLabels init ω u) = init.card} :=
          ((pairLogFiltration L K).mono hu) _ (full_activation_measurable init u)
        simpa only [hu, hs, true_and] using ha
      · simp only [hs, and_false, false_and, Set.setOf_false, MeasurableSet.empty]
    · simp only [hu, false_and, Set.setOf_false, MeasurableSet.empty]
  convert hm using 1
  ext ω
  simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
  exact activationTime_le_iff init s N ω

theorem activationTime_pastTime (init : Cfg L K) (s : ℕ) :
    PhaseOneDrain.PairLogPastTime (activationTime init s) :=
  fun u => (activationTime_isStoppingTime init s).measurableSet_eq_of_countable u

/-- Monotonicity makes the passage failure exactly the current count failure. -/
theorem activationTime_gt_iff (init : Cfg L K) (s N : ℕ) (hSN : s ≤ N)
    (ω : Ω L K) :
    (N : WithTop ℕ) < activationTime init s ω ↔
      PhaseThreeClockActivationLaw.activeCount (virtualLabels init ω N) < init.card := by
  constructor
  · intro hτ
    have hle := activeCount_le_card (virtualLabels init ω N)
    by_contra hnot
    have heq : PhaseThreeClockActivationLaw.activeCount (virtualLabels init ω N) = init.card := by omega
    have hhit := (activationTime_le_iff init s N ω).2 ⟨N, le_rfl, hSN, heq⟩
    exact (not_lt_of_ge hhit) hτ
  · intro hcount
    apply lt_of_not_ge
    intro hhit
    obtain ⟨u, huN, -, hfull⟩ := (activationTime_le_iff init s N ω).1 hhit
    have hmono : PhaseThreeClockActivationLaw.activeCount (virtualLabels init ω u) ≤
        PhaseThreeClockActivationLaw.activeCount (virtualLabels init ω N) :=
      activeCount_virtualLabels_mono init ω huN
    omega

theorem activationTime_prefix_tail (init : Cfg L K) (hc : 2 ≤ init.card)
    (s : ℕ) (E : Set (Ω L K))
    (hE : MeasurableSet[pairLogFiltration L K s] E)
    (hseed : E ⊆ hasActiveAt init s) :
    law init (E ∩ {ω | ((s + activationHorizon init.card : ℕ) : WithTop ℕ) <
      activationTime init s ω}) ≤
      ENNReal.ofReal (1 / (init.card : ℝ) ^ 5) * law init E := by
  have heq : {ω | ((s + activationHorizon init.card : ℕ) : WithTop ℕ) <
        activationTime init s ω} =
      activationFailure init s (activationHorizon init.card) := by
    ext ω
    exact activationTime_gt_iff init s _ (by omega) ω
  rw [heq]
  exact activation_prefix_calibrated init hc s E hE hseed

/-- The uncalibrated geometric tail, for every deterministic elapsed time. -/
theorem activationTime_prefix_real_bound (init : Cfg L K) (hc : 2 ≤ init.card)
    (s N : ℕ) (E : Set (Ω L K))
    (hE : MeasurableSet[pairLogFiltration L K s] E)
    (hseed : E ⊆ hasActiveAt init s) :
    (law init).real (E ∩ {ω | ((s + N : ℕ) : WithTop ℕ) < activationTime init s ω}) ≤
      (init.card : ℝ) ^ 2 * (1 - 1 / (init.card : ℝ)) ^ N * (law init).real E := by
  let B : Set (Ω L K) := hasActiveAt init s ∩
    {ω | ((s + N : ℕ) : WithTop ℕ) < activationTime init s ω}
  have hZb : ∀ t, ∀ᵐ ω ∂law init,
      0 ≤ activePotential init s t ω ∧ activePotential init s t ω ≤ 1 :=
    fun t => ae_of_all _ (activePotential_bounds init hc s t)
  have hEs : MeasurableSet[shiftedFiltration (pairLogFiltration L K) s 0] E := by
    simpa only [shiftedFiltration_apply, Nat.add_zero] using hE
  have hB : ∀ ω ∈ B, 1 ≤ (init.card : ℝ) ^ 2 * activePotential init s N ω := by
    rintro ω ⟨hω, hτ⟩
    rw [activePotential, Set.indicator_of_mem hω]
    have hlt := (activationTime_gt_iff init s (s + N) (by omega) ω).1 hτ
    exact activationWeight_boundary _ _ (by exact_mod_cast hc)
      (by exact_mod_cast activeCount_pos_of_seed init s N ω hω)
      (by exact_mod_cast (by omega :
        PhaseThreeClockActivationLaw.activeCount (virtualLabels init ω (s + N)) + 1 ≤ init.card))
  have htail := prefix_potential_tail
    (activePotential_stronglyMeasurable init s) hZb
    (activation_contraction_nonneg init.card hc)
    (activePotential_conditional_drift init hc s)
    E hEs N B ((init.card : ℝ) ^ 2) (sq_nonneg _) hB
  have heq : E ∩ B = E ∩
      {ω | ((s + N : ℕ) : WithTop ℕ) < activationTime init s ω} := by
    ext ω
    constructor
    · exact fun h => ⟨h.1, h.2.2⟩
    · exact fun h => ⟨h.1, hseed h.1, h.2⟩
  simpa only [heq] using htail

/-- A seeded virtual population reaches full threshold activation in
finite time almost surely, still under the original pair-log law. -/
theorem activationTime_infinite_prefix_null (init : Cfg L K) (hc : 2 ≤ init.card)
    (s : ℕ) (E : Set (Ω L K))
    (hE : MeasurableSet[pairLogFiltration L K s] E)
    (hseed : E ⊆ hasActiveAt init s) :
    law init (E ∩ {ω | activationTime init s ω = ⊤}) = 0 := by
  let A : Set (Ω L K) := E ∩ {ω | activationTime init s ω = ⊤}
  let a : ℝ := (law init).real A
  have hmpos : (0 : ℝ) < (init.card : ℝ) := by exact_mod_cast (by omega : 0 < init.card)
  have hEprob : (law init).real E ≤ 1 := by
    calc
      (law init).real E ≤ (law init).real Set.univ :=
        measureReal_mono (Set.subset_univ E)
      _ = 1 := by simp
  have hbound (N : ℕ) :
      a ≤ (init.card : ℝ) ^ 2 * Real.exp (-(N : ℝ) / (init.card : ℝ)) := by
    have hsub : A ⊆ E ∩
        {ω | ((s + N : ℕ) : WithTop ℕ) < activationTime init s ω} := by
      rintro ω ⟨hω, ht⟩
      refine ⟨hω, ?_⟩
      show ((s + N : ℕ) : WithTop ℕ) < activationTime init s ω
      rw [show activationTime init s ω = ⊤ from ht]
      simp
    have hmul : 0 ≤ (init.card : ℝ) ^ 2 *
        (1 - 1 / (init.card : ℝ)) ^ N :=
      mul_nonneg (sq_nonneg _)
        (pow_nonneg (activation_contraction_nonneg init.card hc) N)
    calc
      a ≤ (init.card : ℝ) ^ 2 * (1 - 1 / (init.card : ℝ)) ^ N * (law init).real E :=
        (measureReal_mono hsub).trans
          (activationTime_prefix_real_bound init hc s N E hE hseed)
      _ ≤ (init.card : ℝ) ^ 2 * (1 - 1 / (init.card : ℝ)) ^ N := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hEprob hmul
      _ ≤ (init.card : ℝ) ^ 2 * Real.exp (-(N : ℝ) / (init.card : ℝ)) :=
        mul_le_mul_of_nonneg_left (activation_contraction_pow_le_exp init.card N hc)
          (sq_nonneg _)
  have ha : a = 0 := by
    apply le_antisymm ?_ (by dsimp only [a]; positivity)
    by_contra hnot
    have hpos : 0 < a := lt_of_not_ge hnot
    obtain ⟨N, hN⟩ := exists_nat_gt
      ((init.card : ℝ) * (2 * Real.log (init.card : ℝ) - Real.log a))
    have hdiv :
        2 * Real.log (init.card : ℝ) - Real.log a <
          (N : ℝ) / (init.card : ℝ) := by
      apply (lt_div_iff₀ hmpos).2
      simpa only [mul_comm] using hN
    have harg :
        2 * Real.log (init.card : ℝ) - (N : ℝ) / (init.card : ℝ) < Real.log a := by
      linarith
    have hexp : Real.exp (2 * Real.log (init.card : ℝ)) = (init.card : ℝ) ^ 2 := by
      change Real.exp ((2 : ℕ) * Real.log (init.card : ℝ)) = _
      rw [Real.exp_nat_mul, Real.exp_log hmpos]
    have hlast :
        (init.card : ℝ) ^ 2 * Real.exp (-(N : ℝ) / (init.card : ℝ)) < a := by
      calc
        (init.card : ℝ) ^ 2 * Real.exp (-(N : ℝ) / (init.card : ℝ)) =
            Real.exp (2 * Real.log (init.card : ℝ) - (N : ℝ) / (init.card : ℝ)) := by
          rw [← hexp, ← Real.exp_add]
          congr 1
          ring
        _ < a := by simpa only [Real.exp_log hpos] using Real.exp_lt_exp.mpr harg
    exact (not_lt_of_ge (hbound N)) hlast
  calc
    law init (E ∩ {ω | activationTime init s ω = ⊤}) = ENNReal.ofReal a :=
      (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
    _ = 0 := by rw [ha, ENNReal.ofReal_zero]

variable {n : ℕ}

/-- The observed seed event supplies the positive-activation premise. -/
theorem seed_activationTime_prefix_tail (init : InputCfg n) (hc : 2 ≤ init.card)
    (s : ℕ) (E : Set (InputLog n))
    (hE : MeasurableSet[pairLogFiltration _ _ s] E)
    (hseed : E ⊆ seedPrefix init s) :
    law init (E ∩ {ω | ((s + activationHorizon init.card : ℕ) : WithTop ℕ) <
      activationTime init s ω}) ≤
      ENNReal.ofReal (1 / (init.card : ℝ) ^ 5) * law init E :=
  activationTime_prefix_tail init hc s E hE
    (fun ω hω => positive_activation_at_seedPrefix init ω s (hseed hω))

/-- An observed full-activation fibre with the current phase cap. -/
def safeActivationFibre (init : InputCfg n) (s u : ℕ) : Set (InputLog n) :=
  (seedPrefix init s ∩ {ω | activationTime init s ω = (u : WithTop ℕ)}) ∩
    {ω | ∀ i, (virtualLabels init ω u i).phase.val ≤ 3}

theorem safeActivationFibre_order (init : InputCfg n) (s u : ℕ)
    (ω : InputLog n) (hω : ω ∈ safeActivationFibre init s u) :
    s ≤ u :=
  (activationTime_finite_state init s u ω hω.1.2).1

theorem safeActivationFibre_measurable (init : InputCfg n) (s u : ℕ) :
    MeasurableSet[pairLogFiltration _ _ u] (safeActivationFibre init s u) := by
  by_cases hsu : s ≤ u
  · have hcap : MeasurableSet[pairLogFiltration _ _ u]
        {ω | ∀ i, (virtualLabels init ω u i).phase.val ≤ 3} :=
      (show MeasurableSet {f : Fin init.card →
          AgentState (PhaseThreeModel.Numeric.hourIndex n) 256 |
            ∀ i, (f i).phase.val ≤ 3} from
        (Set.to_countable _).measurableSet).preimage (measurable_virtualLabels init u)
    exact ((((pairLogFiltration _ _).mono hsu) _ (seedPrefix_measurable init s)).inter
      (activationTime_pastTime init s u)).inter hcap
  · have hempty : safeActivationFibre init s u = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro ω hω
      exact hsu (safeActivationFibre_order init s u ω hω)
    rw [hempty]
    exact MeasurableSpace.measurableSet_empty _

theorem safeActivationFibre_dense (init : InputCfg n) (hn : 9 ≤ n)
    (s u : ℕ) (ω : InputLog n) (hω : ω ∈ safeActivationFibre init s u) :
    DenseHomogeneousStart init ω u := by
  have hstate := activationTime_finite_state init s u ω hω.1.2
  exact dense_start_data_of_seedPrefix_full_activation init hn ω s u
    hω.1.1 hstate.1 hstate.2 hω.2

/-- The first-positive deadline starts at the genuine activation passage,
on its observed finite fibres, with the fibre probability preserved. -/
theorem first_positive_at_activation_fibre_tail (init : InputCfg n)
    (hn : 9 ≤ n) (hc : 2 ≤ init.card) (s u : ℕ) :
    law init (safeActivationFibre init s u ∩
      {ω | (firstPositiveHorizon init.card : WithTop ℕ) < firstPositiveTime init u ω}) ≤
      ENNReal.ofReal (1 / (init.card : ℝ) ^ 10) *
        law init (safeActivationFibre init s u) :=
  first_positive_dense_prefix_tail init hc u (safeActivationFibre init s u)
    (safeActivationFibre_measurable init s u)
    (fun ω hω => safeActivationFibre_dense init hn s u ω hω)

theorem first_positive_at_activation_fibre_failure_measurable
    (init : InputCfg n) (s u : ℕ) :
    MeasurableSet[pairLogFiltration _ _ (u + firstPositiveHorizon init.card)]
      (safeActivationFibre init s u ∩
        {ω | (firstPositiveHorizon init.card : WithTop ℕ) <
          firstPositiveTime init u ω}) :=
  first_positive_failure_measurable init u (firstPositiveHorizon init.card)
    (safeActivationFibre init s u) (safeActivationFibre_measurable init s u)


/-- On an actual AsyncEntry path, the virtual passage is exactly the
genuine all-Phase-3 time. This is a pathwise identity, not a conditioned law. -/
theorem activationTime_eq_of_asyncEntry (init : InputCfg n) (ω : InputLog n)
    (s T : ℕ) (hentry : StageEventSpec.AsyncEntry init ω s T) :
    activationTime init s ω = (T : WithTop ℕ) := by
  have heq := virtualLabels_eq_labelsAt_through_asyncEntry init ω s T hentry
  have hle : activationTime init s ω ≤ (T : WithTop ℕ) := by
    apply (activationTime_le_iff init s T ω).2
    refine ⟨T, le_rfl, hentry.order, ?_⟩
    apply (activeCount_eq_card_iff _).2
    intro i
    rw [heq T le_rfl]
    exact (hentry.advanced_profile.all_three _ (labelsAt_mem_trace init ω T i)).ge
  apply le_antisymm hle
  by_contra hnot
  have hlt : activationTime init s ω < (T : WithTop ℕ) := lt_of_not_ge hnot
  obtain ⟨u, hu⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_lt hlt)
  have huT : u < T := by
    exact WithTop.coe_lt_coe.mp (hu.trans_lt hlt)
  have hstate := activationTime_finite_state init s u ω hu.symm
  apply hentry.all_first.2 u huT
  intro a ha
  have hamem : a ∈ labelCfg (labelsAt init ω u) := by
    rw [show labelCfg (labelsAt init ω u) = trace init ω u from labelsAt_config init ω u]
    exact ha
  obtain ⟨i, -, hi⟩ := Multiset.mem_map.mp hamem
  have hp := (activeCount_eq_card_iff _).1 hstate.2 i
  rw [heq u huT.le, hi] at hp
  exact hp

theorem mem_safeActivationFibre_of_asyncEntry (init : InputCfg n)
    (ω : InputLog n) (s T : ℕ)
    (hentry : StageEventSpec.AsyncEntry init ω s T) :
    ω ∈ safeActivationFibre init s T := by
  refine ⟨⟨⟨(seedTime_eq_iff init 3 ω s).2 hentry.first_phase_seed,
    hentry.seed_profile⟩, activationTime_eq_of_asyncEntry init ω s T hentry⟩, ?_⟩
  intro i
  rw [virtualLabels_eq_labelsAt_through_asyncEntry init ω s T hentry T le_rfl]
  exact (hentry.advanced_profile.all_three _ (labelsAt_mem_trace init ω T i)).le

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockActivationTime

end
