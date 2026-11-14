-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockMarkedWindow.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockMarkedClockRates

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal BigOperators MeasureTheory ProbabilityTheory

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockMarkedWindow

open TimeTheorem PairLog PhaseThreeScalar PhaseThreeClockVirtual PhaseThreeClockGatedLaw
  PhaseThreeClockActivationLaw PhaseThreeClockMacroscopicActivation
  PhaseThreeClockSmallActivation PhaseThreeClockSeedTails PhaseThreeClockPrefixTails
  PhaseThreeClockEarlyMarks PhaseThreeClockThinning PhaseThreeClockMarkedClockRates

variable {L K : ℕ}

open Classical in
def levelPositiveTime (init : Cfg L K) (s ℓ : ℕ) (ω : Ω L K) : WithTop ℕ :=
  if h : ∃ v, s ≤ v ∧ 0 < frontCount (virtualLabels init ω v) ℓ
  then ((Nat.find h : ℕ) : WithTop ℕ) else ⊤

theorem levelPositiveTime_le_iff (init : Cfg L K) (s ℓ v : ℕ) (ω : Ω L K) :
    levelPositiveTime init s ℓ ω ≤ (v : WithTop ℕ) ↔
      ∃ w ≤ v, s ≤ w ∧ 0 < frontCount (virtualLabels init ω w) ℓ := by
  classical
  unfold levelPositiveTime
  split_ifs with h
  · constructor
    · intro hle
      have hw : Nat.find h ≤ v := by exact_mod_cast hle
      exact ⟨Nat.find h, hw, Nat.find_spec h⟩
    · rintro ⟨w, hw, hs, hp⟩
      have hle : Nat.find h ≤ v := (Nat.find_min' h ⟨hs, hp⟩).trans hw
      exact_mod_cast hle
  · constructor
    · intro hle
      exact absurd hle (by simp)
    · rintro ⟨w, -, hs, hp⟩
      exact absurd ⟨w, hs, hp⟩ h

theorem levelPositiveTime_finite_state (init : Cfg L K) (s ℓ v : ℕ) (ω : Ω L K)
    (hv : levelPositiveTime init s ℓ ω = (v : WithTop ℕ)) :
    s ≤ v ∧ 0 < frontCount (virtualLabels init ω v) ℓ := by
  classical
  unfold levelPositiveTime at hv
  split_ifs at hv with h
  · have heq : Nat.find h = v := WithTop.coe_injective hv
    simpa only [heq] using Nat.find_spec h
  · exact absurd hv WithTop.top_ne_coe

theorem levelPositiveTime_isStoppingTime (init : Cfg L K) (s ℓ : ℕ) :
    IsStoppingTime (pairLogFiltration L K) (levelPositiveTime init s ℓ) := by
  intro N
  have hm : MeasurableSet[pairLogFiltration L K N]
      (⋃ v, {ω | v ≤ N ∧ s ≤ v ∧ 0 < frontCount (virtualLabels init ω v) ℓ}) := by
    refine MeasurableSet.iUnion fun v => ?_
    by_cases hv : v ≤ N
    · by_cases hs : s ≤ v
      · have hfront : MeasurableSet[pairLogFiltration L K v]
            {ω | 0 < frontCount (virtualLabels init ω v) ℓ} :=
          (show MeasurableSet {f : Fin init.card → AgentState L K | 0 < frontCount f ℓ} from
            (Set.to_countable _).measurableSet).preimage (measurable_virtualLabels init v)
        simpa only [hv, hs, true_and] using
          (((pairLogFiltration L K).mono hv) _ hfront)
      · simp only [hs, and_false, false_and, Set.setOf_false, MeasurableSet.empty]
    · simp only [hv, false_and, Set.setOf_false, MeasurableSet.empty]
  convert hm using 1
  ext ω
  simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
  exact levelPositiveTime_le_iff init s ℓ N ω

theorem front_zero_before_levelPositiveTime (init : Cfg L K)
    (s ℓ v : ℕ) (ω : Ω L K) (hsv : s ≤ v)
    (hbefore : (v : WithTop ℕ) < levelPositiveTime init s ℓ ω) :
    frontCount (virtualLabels init ω v) ℓ = 0 := by
  by_contra hz
  have hp : 0 < frontCount (virtualLabels init ω v) ℓ := by omega
  have hle := (levelPositiveTime_le_iff init s ℓ v ω).2 ⟨v, le_rfl, hsv, hp⟩
  exact (not_lt_of_ge hle) hbefore

def earlyEnd (init : Cfg L K) (s u N : ℕ) (ω : Ω L K) : WithTop ℕ :=
  min (macroscopicTime init s ω) ((u + N : ℕ) : WithTop ℕ)

def secondStart (init : Cfg L K) (s ℓ u N : ℕ) (ω : Ω L K) : WithTop ℕ :=
  max (earlyEnd init s u N ω) (levelPositiveTime init s ℓ ω)

def rawFlag (init : Cfg L K) (s u N t : ℕ) (ω : Ω L K) : Prop :=
  ((u + t : ℕ) : WithTop ℕ) < earlyEnd init s u N ω

def lateFlag (init : Cfg L K) (s ℓ u N t : ℕ) (ω : Ω L K) : Prop :=
  secondStart init s ℓ u N ω ≤ ((u + t : ℕ) : WithTop ℕ)

theorem earlyEnd_le_deadline (init : Cfg L K) (s u N : ℕ) (ω : Ω L K) :
    earlyEnd init s u N ω ≤ ((u + N : ℕ) : WithTop ℕ) :=
  min_le_right _ _

theorem earlyEnd_isStoppingTime (init : Cfg L K) (s u N : ℕ) :
    IsStoppingTime (pairLogFiltration L K) (earlyEnd init s u N) := by
  intro v
  change MeasurableSet[pairLogFiltration L K v] {ω | earlyEnd init s u N ω ≤ (v : WithTop ℕ)}
  by_cases hv : u + N ≤ v
  · have hc : ((u + N : ℕ) : WithTop ℕ) ≤ (v : WithTop ℕ) := by exact_mod_cast hv
    have he : {ω | earlyEnd init s u N ω ≤ (v : WithTop ℕ)} = Set.univ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      exact (earlyEnd_le_deadline init s u N ω).trans hc
    rw [he]
    exact MeasurableSet.univ
  · have hc : ¬ ((u + N : ℕ) : WithTop ℕ) ≤ (v : WithTop ℕ) := by exact_mod_cast hv
    have h := macroscopicTime_isStoppingTime init s v
    change MeasurableSet[pairLogFiltration L K v]
      {ω | macroscopicTime init s ω ≤ (v : WithTop ℕ)} at h
    simpa only [earlyEnd, min_le_iff, hc, or_false] using h

theorem secondStart_isStoppingTime (init : Cfg L K) (s ℓ u N : ℕ) :
    IsStoppingTime (pairLogFiltration L K) (secondStart init s ℓ u N) := by
  intro v
  convert (earlyEnd_isStoppingTime init s u N v).inter
    (levelPositiveTime_isStoppingTime init s ℓ v) using 1
  ext ω
  simp only [Set.mem_setOf_eq, Set.mem_inter_iff, secondStart, max_le_iff]

theorem rawFlag_measurable (init : Cfg L K) (s u N t : ℕ) :
    MeasurableSet[pairLogFiltration L K (u + t)] {ω | rawFlag init s u N t ω} :=
  (earlyEnd_isStoppingTime init s u N).measurableSet_gt (u + t)

theorem lateFlag_measurable (init : Cfg L K) (s ℓ u N t : ℕ) :
    MeasurableSet[pairLogFiltration L K (u + t)] {ω | lateFlag init s ℓ u N t ω} :=
  secondStart_isStoppingTime init s ℓ u N (u + t)

theorem raw_late_disjoint (init : Cfg L K) (s ℓ u N t : ℕ) (ω : Ω L K) :
    rawFlag init s u N t ω → ¬ lateFlag init s ℓ u N t ω := by
  intro hr hl
  have hH : earlyEnd init s u N ω ≤ secondStart init s ℓ u N ω := le_max_left _ _
  exact (not_lt_of_ge (hH.trans hl)) hr

theorem rawFlag_false_after_budget (init : Cfg L K) (s u N t : ℕ)
    (ω : Ω L K) (hNt : N ≤ t) :
    ¬ rawFlag init s u N t ω := by
  intro hr
  have hc : ((u + N : ℕ) : WithTop ℕ) ≤ ((u + t : ℕ) : WithTop ℕ) := by
    exact_mod_cast (show u + N ≤ u + t by omega)
  exact (not_lt_of_ge ((earlyEnd_le_deadline init s u N ω).trans hc)) hr

theorem secondStart_ge_observed_start (init : Cfg L K) (s ℓ u N : ℕ) (ω : Ω L K)
    (hα : (u : WithTop ℕ) ≤ macroscopicTime init s ω) :
    (u : WithTop ℕ) ≤ secondStart init s ℓ u N ω := by
  have hH : (u : WithTop ℕ) ≤ earlyEnd init s u N ω :=
    le_min hα (by exact_mod_cast (show u ≤ u + N by omega))
  exact hH.trans (le_max_left _ _)

theorem secondStart_ge_small_passage (init : Cfg L K)
    (s C ℓ u N : ℕ) (ω : Ω L K)
    (hthreshold : PhaseThreeModel.Numeric.smallActivation C ≤ macroscopicThreshold init.card)
    (hu : smallActivationTime init s C ω = (u : WithTop ℕ)) :
    (u : WithTop ℕ) ≤ secondStart init s ℓ u N ω := by
  apply secondStart_ge_observed_start
  simpa only [hu] using smallActivationTime_le_macroscopic init s C ω hthreshold

open Classical in
def rawSlotCount (init : Cfg L K) (s u N k : ℕ) (ω : Ω L K) : ℕ :=
  ((Finset.range k).filter (fun t => rawFlag init s u N t ω)).card

theorem rawSlotCount_le_budget (init : Cfg L K) (s u N k : ℕ) (ω : Ω L K) :
    rawSlotCount init s u N k ω ≤ N := by
  classical
  have hsub : (Finset.range k).filter (fun t => rawFlag init s u N t ω) ⊆ Finset.range N := by
    intro t ht
    have hr := (Finset.mem_filter.mp ht).2
    apply Finset.mem_range.mpr
    by_contra hnot
    exact rawFlag_false_after_budget init s u N t ω (by omega) hr
  simpa only [rawSlotCount, Finset.card_range] using Finset.card_le_card hsub

open Classical in
theorem rawSlotCount_cast_eq_sum (init : Cfg L K) (s u N k : ℕ) (ω : Ω L K) :
    (rawSlotCount init s u N k ω : ℝ) =
      ∑ t ∈ Finset.range k, if rawFlag init s u N t ω then (1 : ℝ) else 0 := by
  classical
  unfold rawSlotCount
  rw [Finset.card_filter]
  simp only [Nat.cast_sum, apply_ite, Nat.cast_one, Nat.cast_zero]

open Classical in
def laterTickIndicator (init : Cfg L K) (C : Finset (Fin init.card))
    (s ℓ u N t : ℕ) (ω : Ω L K) : ℝ :=
  if lateFlag init s ℓ u N t ω then maskTickIndicator init C (u + t) ω else 0

def laterClockCount (init : Cfg L K) (C : Finset (Fin init.card))
    (s ℓ u N k : ℕ) (ω : Ω L K) : ℝ :=
  bernoulliCount (laterTickIndicator init C s ℓ u N) k ω

theorem laterTickIndicator_stronglyMeasurable (init : Cfg L K)
    (C : Finset (Fin init.card)) (s ℓ u N t : ℕ) :
    StronglyMeasurable[pairLogFiltration L K (u + t + 1)]
      (laterTickIndicator init C s ℓ u N t) := by
  classical
  have hset : MeasurableSet[pairLogFiltration L K (u + t + 1)]
      {ω | lateFlag init s ℓ u N t ω} :=
    ((pairLogFiltration L K).mono (Nat.le_succ (u + t))) _
      (lateFlag_measurable init s ℓ u N t)
  simpa only [laterTickIndicator, Set.indicator_apply] using
    (maskTickIndicator_stronglyMeasurable init C (u + t)).indicator hset

theorem laterClockCount_stronglyMeasurable (init : Cfg L K)
    (C : Finset (Fin init.card)) (s ℓ u N k : ℕ) :
    StronglyMeasurable[pairLogFiltration L K (u + k)]
      (laterClockCount init C s ℓ u N k) := by
  have hI : ∀ t, StronglyMeasurable[shiftedFiltration (pairLogFiltration L K) u (t + 1)]
      (laterTickIndicator init C s ℓ u N t) := by
    intro t
    simpa only [shiftedFiltration_apply, Nat.add_assoc] using
      laterTickIndicator_stronglyMeasurable init C s ℓ u N t
  exact bernoulliCount_stronglyMeasurable hI k

theorem laterClockCount_succ (init : Cfg L K) (C : Finset (Fin init.card))
    (s ℓ u N k : ℕ) (ω : Ω L K) :
    laterClockCount init C s ℓ u N (k + 1) ω =
      laterClockCount init C s ℓ u N k ω + laterTickIndicator init C s ℓ u N k ω := by
  simp only [laterClockCount, bernoulliCount, Finset.sum_range_succ]

open Classical in
theorem maskContacts_succ_endpoint (init : Cfg L K) (C : Finset (Fin init.card))
    (b v : ℕ) (ω : Ω L K) :
    maskContacts init C b (v + 1) ω = maskContacts init C b v ω +
      if b ≤ v ∧ maskContact init C (v + 1) ω then 1 else 0 := by
  classical
  by_cases hb : b ≤ v
  · have hi : Finset.Ioc b (v + 1) = insert (v + 1) (Finset.Ioc b v) := by
      ext k
      simp only [Finset.mem_Ioc, Finset.mem_insert]
      omega
    have hnot : v + 1 ∉ (Finset.Ioc b v).filter (fun k => maskContact init C k ω) := by
      simp only [Finset.mem_filter, Finset.mem_Ioc]
      omega
    by_cases ht : maskContact init C (v + 1) ω <;>
      simp [maskContacts, hi, Finset.filter_insert, hb, ht, hnot, add_comm]
  · have hi : Finset.Ioc b v = ∅ := by
      ext k
      simp only [Finset.mem_Ioc, Finset.notMem_empty, iff_false]
      omega
    have hj : Finset.Ioc b (v + 1) = ∅ := by
      ext k
      simp only [Finset.mem_Ioc, Finset.notMem_empty, iff_false]
      omega
    simp only [maskContacts, hi, hj, Finset.filter_empty, Finset.card_empty,
      hb, false_and, if_false, add_zero]

theorem laterClockCount_eq_maskContacts (init : Cfg L K)
    (C : Finset (Fin init.card)) (s ℓ u N b : ℕ) (ω : Ω L K)
    (hB : secondStart init s ℓ u N ω = (b : WithTop ℕ)) (hub : u ≤ b) :
    ∀ k, laterClockCount init C s ℓ u N k ω =
      (maskContacts init C b (u + k) ω : ℝ) := by
  classical
  intro k
  induction k with
  | zero =>
      have hi : Finset.Ioc b u = ∅ := by
        ext j
        simp only [Finset.mem_Ioc, Finset.notMem_empty, iff_false]
        omega
      simp only [laterClockCount, bernoulliCount, Finset.sum_range_zero,
        Nat.add_zero, maskContacts, hi, Finset.filter_empty, Finset.card_empty, Nat.cast_zero]
  | succ k ih =>
      rw [laterClockCount_succ, ih]
      have hcount := maskContacts_succ_endpoint init C b (u + k) ω
      have hcountR : (maskContacts init C b (u + k + 1) ω : ℝ) =
          (maskContacts init C b (u + k) ω : ℝ) +
            if b ≤ u + k ∧ maskContact init C (u + k + 1) ω then (1 : ℝ) else 0 := by
        exact_mod_cast hcount
      rw [show u + (k + 1) = u + k + 1 by omega, hcountR]
      congr 1
      have hlate : lateFlag init s ℓ u N k ω ↔ b ≤ u + k := by
        change secondStart init s ℓ u N ω ≤ ((u + k : ℕ) : WithTop ℕ) ↔ _
        rw [hB]
        norm_cast
      by_cases hb : b ≤ u + k <;> by_cases ht : maskContact init C (u + k + 1) ω <;>
        simp only [laterTickIndicator, hlate, hb, ht, maskTickIndicator,
          true_and, false_and, and_false, if_true, if_false]

theorem laterClockCount_eq_maskTickCount (init : Cfg L K)
    (C : Finset (Fin init.card)) (s ℓ u N b k : ℕ) (ω : Ω L K)
    (hB : secondStart init s ℓ u N ω = (b : WithTop ℕ)) (hub : u ≤ b)
    (hbk : b ≤ u + k) :
    laterClockCount init C s ℓ u N k ω =
      maskTickCount init C b (u + k - b) ω := by
  rw [laterClockCount_eq_maskContacts init C s ℓ u N b ω hB hub k,
    maskTickCount_eq_contacts]
  have he : b + (u + k - b) = u + k := by omega
  rw [he]

def laterBudgetEvent (init : Cfg L K) (C : Finset (Fin init.card))
    (s ℓ u N D k : ℕ) : Set (Ω L K) :=
  {ω | lateFlag init s ℓ u N k ω ∧
    laterClockCount init C s ℓ u N k ω ≤ (D : ℝ)}

theorem laterBudgetEvent_measurable (init : Cfg L K)
    (C : Finset (Fin init.card)) (s ℓ u N D k : ℕ) :
    MeasurableSet[pairLogFiltration L K (u + k)] (laterBudgetEvent init C s ℓ u N D k) :=
  (lateFlag_measurable init s ℓ u N k).inter
    ((show MeasurableSet {x : ℝ | x ≤ (D : ℝ)} from measurableSet_Iic).preimage
      (laterClockCount_stronglyMeasurable init C s ℓ u N k).measurable)

theorem front_zero_on_gap (init : Cfg L K) (s ℓ u N t : ℕ) (ω : Ω L K)
    (hsu : s ≤ u) (hraw : ¬ rawFlag init s u N t ω)
    (hlate : ¬ lateFlag init s ℓ u N t ω) :
    frontCount (virtualLabels init ω (u + t)) ℓ = 0 := by
  have hH : earlyEnd init s u N ω ≤ ((u + t : ℕ) : WithTop ℕ) :=
    le_of_not_gt hraw
  have hfirst : ((u + t : ℕ) : WithTop ℕ) < levelPositiveTime init s ℓ ω := by
    apply lt_of_not_ge
    intro hf
    exact hlate (max_le hH hf)
  exact front_zero_before_levelPositiveTime init s ℓ (u + t) ω (by omega) hfirst

variable {n : ℕ}

theorem gap_mark_step (init : InputCfg n) (ω : InputLog n)
    (C : Finset (Fin init.card)) (s ℓ cutoff u N t : ℕ)
    (hseed : ω ∈ seedPrefix init s) (hsu : s ≤ u) (hℓ : 1 ≤ ℓ)
    (hmask : C = clockSet (labelsAt init ω s))
    (hcap : ∀ i, (virtualLabels init ω (u + t) i).phase.val ≤ 3)
    (hraw : ¬ rawFlag init s u N t ω) (hlate : ¬ lateFlag init s ℓ u N t ω) :
    markedAt init C ℓ cutoff s ω (u + t) = ∅ ∧
      immigrationIndicator init C ℓ cutoff (u + t) ω = 0 ∧
      propagationIndicator init C ℓ cutoff s (u + t) ω = 0 ∧
      markedAt init C ℓ cutoff s ω (u + t + 1) = ∅ :=
  zero_mark_gap_step init ω C ℓ cutoff s (u + t) hseed (by omega) hℓ hmask hcap
    (front_zero_on_gap init s ℓ u N t ω hsu hraw hlate)

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockMarkedWindow

end
