-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockFirstPositive.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockEmbeddingBridge
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockThinning

/-!
# Creation of a positive Clock front after observed homogeneous activation

The initial event is observed at a deterministic raw time u. It supplies
homogeneous Phase 3, the neutral non-Main carrier invariant, and the physical
Clock mask at u. These state conditions hold at a successful all-Phase-3
entry endpoint. The result does not assume future clock success.

If the level-one front is still zero at u+N, every Clock-contact indicator
between u and u+N is zero: a Clock pair at a zero front would create a
positive minute. The original-law fixed-mask MGF therefore gives the
prefix-weighted tail exp(-q_C N/2), where q_C=C(C-1)/(m(m-1)).
At density 6m≤25C and C≥2, N≥800 log m gives failure at most m^(-10).

This file produces the first positive front after observed full activation.
The separate sparse-seed-to-macroscopic activation and early-mark estimates
are not asserted here.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal BigOperators MeasureTheory ProbabilityTheory

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockFirstPositive

open TimeTheorem PairLog PairLogAuxiliary PhaseThreeScalar
  PhaseThreeClockVirtual PhaseThreeClockGatedLaw PhaseThreeClockGatedLevelOne
  PhaseThreeClockEmbeddingBridge PhaseThreeClockThinning PhaseThreeClockPrefixTails

variable {L m : ℕ}

def HomogeneousStart (init : Cfg L 256) (ω : Ω L 256) (u : ℕ) : Prop :=
  (∀ i, (virtualLabels init ω u i).phase.val = 3) ∧
    ∀ i, nonMainCarrierSmallBiasZeroAgent (virtualLabels init ω u i)

theorem homogeneous_clockEnvironment (init : Cfg L 256) (ω : Ω L 256)
    (u : ℕ) (hu : HomogeneousStart init ω u) (t : ℕ) (hut : u ≤ t) :
    ClockEnvironment (virtualLabels init ω t) := by
  refine ⟨?_, virtualLabels_carrier_of_time init ω u hu.2 t hut⟩
  intro i
  have h := virtualLabels_phase_three_of_time init ω u hu.1 t hut i
  constructor <;> omega

theorem roles_fixed_from_homogeneous (init : Cfg L 256) (ω : Ω L 256)
    (u : ℕ) (hu : HomogeneousStart init ω u) :
    ∀ t, u ≤ t → ∀ i, (virtualLabels init ω t i).role =
      (virtualLabels init ω u i).role := by
  intro t hut
  induction t, hut using Nat.le_induction with
  | base => exact fun _ => rfl
  | succ t hut ih =>
      intro i
      exact (virtualLabels_roles_step_of_phase_range init ω t
        (homogeneous_clockEnvironment init ω u hu t hut).phase_range
        (fun k => ((homogeneous_clockEnvironment init ω u hu (t + 1)
          (by omega)).phase_range k).2) i).trans (ih i)

theorem clockSet_fixed_from_homogeneous (init : Cfg L 256) (ω : Ω L 256)
    (u : ℕ) (hu : HomogeneousStart init ω u) (t : ℕ) (hut : u ≤ t) :
    clockSet (virtualLabels init ω t) = clockSet (virtualLabels init ω u) := by
  classical
  ext i
  simp only [clockSet, Finset.mem_filter, Finset.mem_univ, true_and,
    roles_fixed_from_homogeneous init ω u hu t hut]

theorem frontCount_step_mono_from_homogeneous (init : Cfg L 256)
    (ω : Ω L 256) (u : ℕ) (hu : HomogeneousStart init ω u)
    (t : ℕ) (hut : u ≤ t) (ℓ : ℕ) (hℓ : 1 ≤ ℓ)
    (hcap : ℓ ≤ 256 * (L + 1)) :
    frontCount (virtualLabels init ω t) ℓ ≤
      frontCount (virtualLabels init ω (t + 1)) ℓ := by
  have henv := homogeneous_clockEnvironment init ω u hu t hut
  have hnext := homogeneous_clockEnvironment init ω u hu (t + 1) (by omega)
  cases hd : drawLabels init ω (t + 1) with
  | none =>
      exact (frontCount_virtualLabels_succ_of_none init ω t hd ℓ).ge
  | some ij =>
      rcases ij with ⟨i, j⟩
      rw [frontCount_virtualLabels_succ_of_phase_range init ω t i j hd henv.phase_range
        (fun k hk => (henv.clock_regime k hk).small)
        (fun k => (hnext.phase_range k).2) ℓ hℓ hcap]
      exact Nat.le_add_right _ _

theorem frontCount_mono_from_homogeneous (init : Cfg L 256)
    (ω : Ω L 256) (u : ℕ) (hu : HomogeneousStart init ω u)
    (s t : ℕ) (hus : u ≤ s) (hst : s ≤ t)
    (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (hcap : ℓ ≤ 256 * (L + 1)) :
    frontCount (virtualLabels init ω s) ℓ ≤
      frontCount (virtualLabels init ω t) ℓ := by
  induction t, hst using Nat.le_induction with
  | base => exact le_rfl
  | succ t hst ih =>
      exact ih.trans (frontCount_step_mono_from_homogeneous init ω u hu t
        (hus.trans hst) ℓ hℓ hcap)

theorem effMinute_eq_zero_of_front_one_eq_zero
    (f : Fin m → AgentState L 256) (hz : frontCount f 1 = 0)
    (i : Fin m) (hc : (f i).role = .clock) :
    effMinute (f i) = 0 := by
  have hn : ¬ 1 ≤ effMinute (f i) := by
    intro hp
    have hi : i ∈ aboveSet f 1 := by
      simp only [aboveSet, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hc, hp⟩
    have hpos : 0 < frontCount f 1 := Finset.card_pos.mpr ⟨i, hi⟩
    omega
  omega

theorem gatedTick_one_of_clock_pair_zero_front
    (f : Fin m → AgentState L 256)
    (hphase : ∀ k, (f k).phase.val = 3) (hz : frontCount f 1 = 0)
    (i j : Fin m) (hi : (f i).role = .clock) (hj : (f j).role = .clock) :
    GatedTick 1 f i j := by
  have him := effMinute_eq_zero_of_front_one_eq_zero f hz i hi
  have hjm := effMinute_eq_zero_of_front_one_eq_zero f hz j hj
  refine ⟨Or.inr (Or.inr ⟨?_, ?_⟩), Or.inl ?_⟩
  · simp [exactSet, hi, him]
  · simp [exactSet, hj, hjm]
  · exact (hphase i).ge

theorem maskTickCount_zero_of_front_zero (init : Cfg L 256)
    (ω : Ω L 256) (C : Finset (Fin init.card)) (u N : ℕ)
    (hu : HomogeneousStart init ω u)
    (hmask : clockSet (virtualLabels init ω u) = C)
    (hzero : frontCount (virtualLabels init ω (u + N)) 1 = 0) :
    maskTickCount init C u N ω = 0 := by
  classical
  unfold maskTickCount bernoulliCount
  apply Finset.sum_eq_zero
  intro t ht
  have htN : t < N := Finset.mem_range.mp ht
  have henv := homogeneous_clockEnvironment init ω u hu (u + t) (by omega)
  have hnext := homogeneous_clockEnvironment init ω u hu (u + t + 1) (by omega)
  have hz : frontCount (virtualLabels init ω (u + t)) 1 = 0 := by
    have h := frontCount_mono_from_homogeneous init ω u hu (u + t) (u + N)
      (by omega) (by omega) 1 le_rfl (by omega)
    omega
  by_cases hcontact : maskContact init C (u + t + 1) ω
  · exfalso
    obtain ⟨i, j, hd, hi, hj⟩ := hcontact
    have hmaskt : clockSet (virtualLabels init ω (u + t)) = C :=
      (clockSet_fixed_from_homogeneous init ω u hu (u + t) (by omega)).trans hmask
    have hic : (virtualLabels init ω (u + t) i).role = .clock := by
      have hi' : i ∈ clockSet (virtualLabels init ω (u + t)) := by
        rwa [hmaskt]
      simpa only [clockSet, Finset.mem_filter, Finset.mem_univ, true_and] using hi'
    have hjc : (virtualLabels init ω (u + t) j).role = .clock := by
      have hj' : j ∈ clockSet (virtualLabels init ω (u + t)) := by
        rwa [hmaskt]
      simpa only [clockSet, Finset.mem_filter, Finset.mem_univ, true_and] using hj'
    have hg := gatedTick_one_of_clock_pair_zero_front
      (virtualLabels init ω (u + t))
      (virtualLabels_phase_three_of_time init ω u hu.1 (u + t) (by omega)) hz i j hic hjc
    have hstep := frontCount_virtualLabels_succ_of_phase_range init ω (u + t) i j hd
      henv.phase_range (fun k hk => (henv.clock_regime k hk).small)
      (fun k => (hnext.phase_range k).2) 1 le_rfl (by omega)
    rw [if_pos hg, hz] at hstep
    have hle := frontCount_mono_from_homogeneous init ω u hu (u + t + 1) (u + N)
      (by omega) (by omega) 1 le_rfl (by omega)
    omega
  · simp only [maskTickIndicator, if_neg hcontact]

theorem zero_front_measurable (init : Cfg L 256) (t : ℕ) :
    MeasurableSet[pairLogFiltration L 256 t]
      {ω | frontCount (virtualLabels init ω t) 1 = 0} :=
  (show MeasurableSet {f : Fin init.card → AgentState L 256 | frontCount f 1 = 0} from
    (Set.to_countable _).measurableSet).preimage (measurable_virtualLabels init t)

/-- The first-positive-front failure bound at an observed homogeneous prefix. -/
theorem first_positive_prefix_real_tail (init : Cfg L 256)
    (hc : 2 ≤ init.card) (C : Finset (Fin init.card)) (u N : ℕ)
    (E : Set (Ω L 256)) (hE : MeasurableSet[pairLogFiltration L 256 u] E)
    (hstart : ∀ ω ∈ E, HomogeneousStart init ω u)
    (hmask : ∀ ω ∈ E, clockSet (virtualLabels init ω u) = C) :
    (law init).real (E ∩ {ω | frontCount (virtualLabels init ω (u + N)) 1 = 0}) ≤
      Real.exp (-clockMaskRate init.card C.card * (N : ℝ) / 2) * (law init).real E := by
  have hsub : E ∩ {ω | frontCount (virtualLabels init ω (u + N)) 1 = 0} ⊆
      E ∩ {ω | (-Real.log (2 : ℝ)) * 0 ≤
        (-Real.log (2 : ℝ)) * maskTickCount init C u N ω} := by
    rintro ω ⟨hω, hz⟩
    refine ⟨hω, ?_⟩
    simp only [Set.mem_setOf_eq, maskTickCount_zero_of_front_zero init ω C u N
      (hstart ω hω) (hmask ω hω) hz, mul_zero, le_refl]
  have ht := prefix_maskTick_exponential_tail init hc C u N E hE
    (-Real.log (2 : ℝ)) 0
  have hexp : Real.exp (-Real.log (2 : ℝ)) = (1 : ℝ) / 2 := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have harg :
      (Real.exp (-Real.log (2 : ℝ)) - 1) * clockMaskRate init.card C.card * (N : ℝ) -
          (-Real.log (2 : ℝ)) * 0 =
        -clockMaskRate init.card C.card * (N : ℝ) / 2 := by
    rw [hexp]
    ring
  exact (measureReal_mono hsub).trans (by simpa only [harg] using ht)

theorem first_positive_prefix_tail (init : Cfg L 256)
    (hc : 2 ≤ init.card) (C : Finset (Fin init.card)) (u N : ℕ)
    (E : Set (Ω L 256)) (hE : MeasurableSet[pairLogFiltration L 256 u] E)
    (hstart : ∀ ω ∈ E, HomogeneousStart init ω u)
    (hmask : ∀ ω ∈ E, clockSet (virtualLabels init ω u) = C) :
    law init (E ∩ {ω | frontCount (virtualLabels init ω (u + N)) 1 = 0}) ≤
      ENNReal.ofReal (Real.exp (-clockMaskRate init.card C.card * (N : ℝ) / 2)) *
        law init E :=
  measure_le_of_real_weighted_bound (law init) _ E _ (Real.exp_nonneg _)
    (first_positive_prefix_real_tail init hc C u N E hE hstart hmask)

theorem clockMaskRate_ge_one_fortieth (m C : ℕ) (hm : 2 ≤ m) (hC : 2 ≤ C)
    (hdensity : 6 * m ≤ 25 * C) :
    (1 / 40 : ℝ) ≤ clockMaskRate m C := by
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hCR : (2 : ℝ) ≤ (C : ℝ) := by exact_mod_cast hC
  have hdR : 6 * (m : ℝ) ≤ 25 * (C : ℝ) := by exact_mod_cast hdensity
  have hs := mul_self_le_mul_self (by positivity : 0 ≤ 6 * (m : ℝ)) hdR
  have hCp := mul_nonneg (by positivity : 0 ≤ (C : ℝ)) (by linarith : 0 ≤ (C : ℝ) - 2)
  have hden : 0 < (m : ℝ) * ((m : ℝ) - 1) := by
    exact mul_pos (by linarith) (by linarith)
  rw [clockMaskRate_eq_real m C (by omega)]
  apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 40) hden).2
  nlinarith

/-- A concrete logarithmic raw-time specialization. -/
theorem first_positive_log_prefix_tail (init : Cfg L 256)
    (hc : 2 ≤ init.card) (C : Finset (Fin init.card))
    (hC : 2 ≤ C.card) (hdensity : 6 * init.card ≤ 25 * C.card) (u N : ℕ)
    (hN : 800 * Real.log (init.card : ℝ) ≤ (N : ℝ))
    (E : Set (Ω L 256)) (hE : MeasurableSet[pairLogFiltration L 256 u] E)
    (hstart : ∀ ω ∈ E, HomogeneousStart init ω u)
    (hmask : ∀ ω ∈ E, clockSet (virtualLabels init ω u) = C) :
    law init (E ∩ {ω | frontCount (virtualLabels init ω (u + N)) 1 = 0}) ≤
      ENNReal.ofReal (1 / (init.card : ℝ) ^ 10) * law init E := by
  have hrate := clockMaskRate_ge_one_fortieth init.card C.card hc hC hdensity
  have hprod := mul_le_mul_of_nonneg_right hrate (Nat.cast_nonneg N)
  have harg :
      -clockMaskRate init.card C.card * (N : ℝ) / 2 ≤
        -(10 : ℝ) * Real.log (init.card : ℝ) := by
    linarith
  have hmpos : (0 : ℝ) < init.card := by exact_mod_cast (show 0 < init.card by omega)
  have hexact :
      Real.exp (-(10 : ℝ) * Real.log (init.card : ℝ)) =
        1 / (init.card : ℝ) ^ 10 := by
    rw [show -(10 : ℝ) * Real.log (init.card : ℝ) =
      -((10 : ℕ) * Real.log (init.card : ℝ)) by ring,
      Real.exp_neg, Real.exp_nat_mul, Real.exp_log hmpos]
    simp only [one_div]
  have hbound : ENNReal.ofReal
      (Real.exp (-clockMaskRate init.card C.card * (N : ℝ) / 2)) ≤
      ENNReal.ofReal (1 / (init.card : ℝ) ^ 10) :=
    ENNReal.ofReal_le_ofReal ((Real.exp_le_exp.mpr harg).trans_eq hexact)
  exact (first_positive_prefix_tail init hc C u N E hE hstart hmask).trans
    (mul_le_mul_right' hbound _)


/-- A fixed logarithmic first-positive horizon, in raw interactions. -/
def firstPositiveHorizon (m : ℕ) : ℕ :=
  Nat.ceil (800 * Real.log (m : ℝ))

theorem first_positive_horizon_prefix_tail (init : Cfg L 256)
    (hc : 2 ≤ init.card) (C : Finset (Fin init.card))
    (hC : 2 ≤ C.card) (hdensity : 6 * init.card ≤ 25 * C.card) (u : ℕ)
    (E : Set (Ω L 256)) (hE : MeasurableSet[pairLogFiltration L 256 u] E)
    (hstart : ∀ ω ∈ E, HomogeneousStart init ω u)
    (hmask : ∀ ω ∈ E, clockSet (virtualLabels init ω u) = C) :
    law init (E ∩ {ω | frontCount
        (virtualLabels init ω (u + firstPositiveHorizon init.card)) 1 = 0}) ≤
      ENNReal.ofReal (1 / (init.card : ℝ) ^ 10) * law init E :=
  first_positive_log_prefix_tail init hc C hC hdensity u _ (Nat.le_ceil _)
    E hE hstart hmask

open Classical in
/-- The first positive front after the observed start, measured in elapsed
raw interactions. This definition makes no future-success assumptions. -/
def firstPositiveTime (init : Cfg L 256) (u : ℕ) (ω : Ω L 256) : WithTop ℕ :=
  if h : ∃ k, 0 < frontCount (virtualLabels init ω (u + k)) 1
  then ((Nat.find h : ℕ) : WithTop ℕ) else ⊤

theorem firstPositiveTime_le_iff (init : Cfg L 256) (u N : ℕ)
    (ω : Ω L 256) :
    firstPositiveTime init u ω ≤ (N : WithTop ℕ) ↔
      ∃ k ≤ N, 0 < frontCount (virtualLabels init ω (u + k)) 1 := by
  classical
  unfold firstPositiveTime
  split_ifs with h
  · constructor
    · intro hle
      have hk : Nat.find h ≤ N := by exact_mod_cast hle
      exact ⟨Nat.find h, hk, Nat.find_spec h⟩
    · rintro ⟨k, hk, hpos⟩
      have hle : Nat.find h ≤ N := (Nat.find_min' h hpos).trans hk
      exact_mod_cast hle
  · constructor
    · intro hle
      exact absurd hle (by simp)
    · rintro ⟨k, -, hpos⟩
      exact absurd ⟨k, hpos⟩ h

theorem positive_front_measurable (init : Cfg L 256) (t : ℕ) :
    MeasurableSet[pairLogFiltration L 256 t]
      {ω | 0 < frontCount (virtualLabels init ω t) 1} :=
  (show MeasurableSet {f : Fin init.card → AgentState L 256 | 0 < frontCount f 1} from
    (Set.to_countable _).measurableSet).preimage (measurable_virtualLabels init t)

theorem firstPositiveTime_isStoppingTime (init : Cfg L 256) (u : ℕ) :
    IsStoppingTime (shiftedFiltration (pairLogFiltration L 256) u)
      (firstPositiveTime init u) := by
  intro N
  have hm : MeasurableSet[shiftedFiltration (pairLogFiltration L 256) u N]
      (⋃ k, {ω | k ≤ N ∧ 0 < frontCount (virtualLabels init ω (u + k)) 1}) := by
    refine MeasurableSet.iUnion fun k => ?_
    by_cases hk : k ≤ N
    · have hp : MeasurableSet[shiftedFiltration (pairLogFiltration L 256) u N]
          {ω | 0 < frontCount (virtualLabels init ω (u + k)) 1} :=
        ((shiftedFiltration (pairLogFiltration L 256) u).mono hk) _
          (positive_front_measurable init (u + k))
      simpa only [hk, true_and] using hp
    · simp only [hk, false_and, Set.setOf_false, MeasurableSet.empty]
  convert hm using 1
  ext ω
  simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
  exact firstPositiveTime_le_iff init u N ω

theorem front_zero_of_lt_firstPositiveTime (init : Cfg L 256)
    (u N : ℕ) (ω : Ω L 256)
    (hN : (N : WithTop ℕ) < firstPositiveTime init u ω) :
    frontCount (virtualLabels init ω (u + N)) 1 = 0 := by
  by_contra hn
  have hp : 0 < frontCount (virtualLabels init ω (u + N)) 1 := by omega
  have hle := (firstPositiveTime_le_iff init u N ω).2 ⟨N, le_rfl, hp⟩
  exact (not_lt_of_ge hle) hN

/-- With the homogeneous state observed at u, the first-passage failure
is exactly the zero-front event at its deadline. -/
theorem firstPositiveTime_gt_iff_front_zero (init : Cfg L 256)
    (u N : ℕ) (ω : Ω L 256) (hu : HomogeneousStart init ω u) :
    (N : WithTop ℕ) < firstPositiveTime init u ω ↔
      frontCount (virtualLabels init ω (u + N)) 1 = 0 := by
  constructor
  · exact front_zero_of_lt_firstPositiveTime init u N ω
  · intro hz
    apply lt_of_not_ge
    intro hle
    obtain ⟨k, hk, hp⟩ := (firstPositiveTime_le_iff init u N ω).1 hle
    have hm := frontCount_mono_from_homogeneous init ω u hu (u + k) (u + N)
      (by omega) (by omega) 1 le_rfl (by omega)
    omega

theorem first_positive_failure_measurable (init : Cfg L 256)
    (u N : ℕ) (E : Set (Ω L 256))
    (hE : MeasurableSet[pairLogFiltration L 256 u] E) :
    MeasurableSet[pairLogFiltration L 256 (u + N)]
      (E ∩ {ω | (N : WithTop ℕ) < firstPositiveTime init u ω}) := by
  exact (((pairLogFiltration L 256).mono (by omega : u ≤ u + N)) _ hE).inter
    ((firstPositiveTime_isStoppingTime init u).measurableSet_gt N)

theorem first_positive_passage_prefix_real_tail (init : Cfg L 256)
    (hc : 2 ≤ init.card) (C : Finset (Fin init.card)) (u N : ℕ)
    (E : Set (Ω L 256)) (hE : MeasurableSet[pairLogFiltration L 256 u] E)
    (hstart : ∀ ω ∈ E, HomogeneousStart init ω u)
    (hmask : ∀ ω ∈ E, clockSet (virtualLabels init ω u) = C) :
    (law init).real (E ∩ {ω | (N : WithTop ℕ) < firstPositiveTime init u ω}) ≤
      Real.exp (-clockMaskRate init.card C.card * (N : ℝ) / 2) * (law init).real E := by
  have hsub : E ∩ {ω | (N : WithTop ℕ) < firstPositiveTime init u ω} ⊆
      E ∩ {ω | frontCount (virtualLabels init ω (u + N)) 1 = 0} := by
    rintro ω ⟨hω, hN⟩
    exact ⟨hω, front_zero_of_lt_firstPositiveTime init u N ω hN⟩
  exact (measureReal_mono hsub).trans
    (first_positive_prefix_real_tail init hc C u N E hE hstart hmask)

theorem first_positive_passage_prefix_tail (init : Cfg L 256)
    (hc : 2 ≤ init.card) (C : Finset (Fin init.card)) (u N : ℕ)
    (E : Set (Ω L 256)) (hE : MeasurableSet[pairLogFiltration L 256 u] E)
    (hstart : ∀ ω ∈ E, HomogeneousStart init ω u)
    (hmask : ∀ ω ∈ E, clockSet (virtualLabels init ω u) = C) :
    law init (E ∩ {ω | (N : WithTop ℕ) < firstPositiveTime init u ω}) ≤
      ENNReal.ofReal (Real.exp (-clockMaskRate init.card C.card * (N : ℝ) / 2)) *
        law init E :=
  measure_le_of_real_weighted_bound (law init) _ E _ (Real.exp_nonneg _)
    (first_positive_passage_prefix_real_tail init hc C u N E hE hstart hmask)

theorem first_positive_passage_horizon_prefix_tail (init : Cfg L 256)
    (hc : 2 ≤ init.card) (C : Finset (Fin init.card))
    (hC : 2 ≤ C.card) (hdensity : 6 * init.card ≤ 25 * C.card) (u : ℕ)
    (E : Set (Ω L 256)) (hE : MeasurableSet[pairLogFiltration L 256 u] E)
    (hstart : ∀ ω ∈ E, HomogeneousStart init ω u)
    (hmask : ∀ ω ∈ E, clockSet (virtualLabels init ω u) = C) :
    law init (E ∩ {ω | (firstPositiveHorizon init.card : WithTop ℕ) <
        firstPositiveTime init u ω}) ≤
      ENNReal.ofReal (1 / (init.card : ℝ) ^ 10) * law init E := by
  have hsub :
      E ∩ {ω | (firstPositiveHorizon init.card : WithTop ℕ) <
        firstPositiveTime init u ω} ⊆
      E ∩ {ω | frontCount
        (virtualLabels init ω (u + firstPositiveHorizon init.card)) 1 = 0} := by
    rintro ω ⟨hω, hN⟩
    exact ⟨hω, front_zero_of_lt_firstPositiveTime init u _ ω hN⟩
  exact (measure_mono hsub).trans
    (first_positive_horizon_prefix_tail init hc C hC hdensity u E hE hstart hmask)

/-- A positive front is reached in finite time almost surely on the observed
homogeneous prefix, as soon as the fixed Clock mask has at least two labels. -/
theorem first_positive_infinite_prefix_null (init : Cfg L 256)
    (hc : 2 ≤ init.card) (C : Finset (Fin init.card)) (hC : 2 ≤ C.card) (u : ℕ)
    (E : Set (Ω L 256)) (hE : MeasurableSet[pairLogFiltration L 256 u] E)
    (hstart : ∀ ω ∈ E, HomogeneousStart init ω u)
    (hmask : ∀ ω ∈ E, clockSet (virtualLabels init ω u) = C) :
    law init (E ∩ {ω | firstPositiveTime init u ω = ⊤}) = 0 := by
  let A : Set (Ω L 256) := E ∩ {ω | firstPositiveTime init u ω = ⊤}
  let a : ℝ := (law init).real A
  have hmR : (2 : ℝ) ≤ (init.card : ℝ) := by exact_mod_cast hc
  have hCR : (2 : ℝ) ≤ (C.card : ℝ) := by exact_mod_cast hC
  have hq : 0 < clockMaskRate init.card C.card := by
    rw [clockMaskRate_eq_real init.card C.card (by omega)]
    exact div_pos (mul_pos (by linarith) (by linarith))
      (mul_pos (by linarith) (by linarith))
  have hEprob : (law init).real E ≤ 1 := by
    calc
      (law init).real E ≤ (law init).real Set.univ :=
        measureReal_mono (Set.subset_univ E)
      _ = 1 := by simp
  have hbound (N : ℕ) :
      a ≤ Real.exp (-clockMaskRate init.card C.card * (N : ℝ) / 2) := by
    have hsub : A ⊆ E ∩ {ω | (N : WithTop ℕ) < firstPositiveTime init u ω} := by
      rintro ω ⟨hω, ht⟩
      refine ⟨hω, ?_⟩
      simp only [Set.mem_setOf_eq]
      rw [show firstPositiveTime init u ω = ⊤ from ht]
      simp
    have hmul := mul_le_mul_of_nonneg_left hEprob
      (Real.exp_nonneg (-clockMaskRate init.card C.card * (N : ℝ) / 2))
    rw [mul_one] at hmul
    exact (measureReal_mono hsub).trans
      ((first_positive_passage_prefix_real_tail init hc C u N E hE hstart hmask).trans hmul)
  have ha : a = 0 := by
    apply le_antisymm ?_ (by dsimp only [a]; positivity)
    by_contra hnot
    have hpos : 0 < a := lt_of_not_ge hnot
    obtain ⟨N, hN⟩ := exists_nat_gt (-2 * Real.log a / clockMaskRate init.card C.card)
    have hprod : -2 * Real.log a < (N : ℝ) * clockMaskRate init.card C.card :=
      (div_lt_iff₀ hq).1 hN
    have harg : -clockMaskRate init.card C.card * (N : ℝ) / 2 < Real.log a := by
      nlinarith
    have hexp : Real.exp (-clockMaskRate init.card C.card * (N : ℝ) / 2) < a := by
      simpa only [Real.exp_log hpos] using Real.exp_lt_exp.mpr harg
    exact (not_lt_of_ge (hbound N)) hexp
  calc
    law init (E ∩ {ω | firstPositiveTime init u ω = ⊤}) = ENNReal.ofReal a :=
      (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
    _ = 0 := by rw [ha, ENNReal.ofReal_zero]

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockFirstPositive

end
