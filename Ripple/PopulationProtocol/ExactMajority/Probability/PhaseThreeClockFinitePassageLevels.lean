-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockFinitePassageLevels.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockNextFrontBirth
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockObservedPassage

/-!
# Finite genuine target passages at every virtual level

The preceding level is allowed to reach bulk before the next-level birth
argument starts. Once the next front is positive, the observed
positive-front estimate gives its finite bulk passage. A countable intersection
over all deterministic observed starting times makes these two implications
available on one full-measure set; pathwise induction then reaches every
level through the cap.

This finite-passage induction is independent of the shape barrier. It does
not provide coarse/fine passage widths or hour-occupancy windows.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal BigOperators MeasureTheory ProbabilityTheory

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockFinitePassageLevels

open TimeTheorem PairLog PhaseThreeClockVirtual PhaseThreeClockGatedLaw
  PhaseThreeClockEmbeddingBridge PhaseThreeClockPrefixTails
  PhaseThreeClockFirstPositive PhaseThreeClockNextFrontBirth
  PhaseThreeClockObservedPassage

variable {L m : ℕ}

theorem frontCount_zero_eq_clockCount (f : Fin m → AgentState L 256) :
    frontCount f 0 = clockCount f := by
  simp [frontCount, clockCount, aboveSet, clockSet]

theorem bulkThreshold_le_clockCount (C : ℕ) :
    StageEventSpec.bulkThreshold C ≤ C := by
  unfold StageEventSpec.bulkThreshold
  apply Nat.ceil_le.mpr
  have hC : (0 : ℝ) ≤ C := Nat.cast_nonneg C
  linarith

theorem two_le_bulkThreshold (C : ℕ) (hC : 11 ≤ C) :
    2 ≤ StageEventSpec.bulkThreshold C := by
  have hCR : (11 : ℝ) ≤ C := by exact_mod_cast hC
  change (1 + 1 : ℕ) ≤ Nat.ceil ((C : ℝ) / 10)
  exact Nat.add_one_le_ceil_iff.mpr (by linarith)

/-- On one full-measure set, birth succeeds from every observed two-label
front at every admissible level and every deterministic starting time. -/
theorem next_front_birth_everywhere_ae (init : Cfg L 256) (hc : 2 ≤ init.card) :
    ∀ᵐ ω ∂law init, ∀ u ℓ,
      ℓ + 1 ≤ 256 * (L + 1) →
      HomogeneousStart init ω u →
      2 ≤ frontCount (virtualLabels init ω u) ℓ →
      ∃ N, 0 < frontCount (virtualLabels init ω (u + N)) (ℓ + 1) := by
  apply ae_all_iff.mpr
  intro u
  apply ae_all_iff.mpr
  intro ℓ
  by_cases hcap : ℓ + 1 ≤ 256 * (L + 1)
  · have hgood : ∀ᵐ ω ∂law init,
        HomogeneousStart init ω u →
        2 ≤ frontCount (virtualLabels init ω u) ℓ →
        ∃ N, 0 < frontCount (virtualLabels init ω (u + N)) (ℓ + 1) := by
      apply ae_iff.mpr
      simpa only [_root_.not_imp] using next_front_never_positive_null init hc u ℓ hcap
    filter_upwards [hgood] with ω hω
    exact fun _ => hω
  · exact ae_of_all _ (fun _ h => False.elim (hcap h))

/-- The same countable observation principle for positive-front-to-bulk
passages. The all-time environment is derived from the observed homogeneous
state; it is not imposed by conditioning the law. -/
theorem positive_front_bulk_everywhere_ae (init : Cfg L 256) (hc : 2 ≤ init.card) :
    ∀ᵐ ω ∂law init, ∀ u ℓ C,
      1 ≤ ℓ → ℓ ≤ 256 * (L + 1) → 6 * init.card ≤ 25 * C →
      HomogeneousStart init ω u →
      1 ≤ frontCount (virtualLabels init ω u) ℓ →
      clockCount (virtualLabels init ω u) = C →
      ∃ N, StageEventSpec.bulkThreshold C ≤
        frontCount (virtualLabels init ω (u + N)) ℓ := by
  apply ae_all_iff.mpr
  intro u
  apply ae_all_iff.mpr
  intro ℓ
  apply ae_all_iff.mpr
  intro C
  by_cases hv : 1 ≤ ℓ ∧ ℓ ≤ 256 * (L + 1) ∧ 6 * init.card ≤ 25 * C
  · let E : Set (Ω L 256) := {ω |
      HomogeneousStart init ω u ∧
      1 ≤ frontCount (virtualLabels init ω u) ℓ ∧
      clockCount (virtualLabels init ω u) = C}
    have hnull := observed_bulk_never_hit_null init hc C ℓ u
      hv.2.2 hv.1 hv.2.1 E (fun _ hω => ⟨hω.2.1, hω.2.2⟩)
    have hgood : ∀ᵐ ω ∂law init,
        HomogeneousStart init ω u →
        1 ≤ frontCount (virtualLabels init ω u) ℓ →
        clockCount (virtualLabels init ω u) = C →
        ∃ N, StageEventSpec.bulkThreshold C ≤
          frontCount (virtualLabels init ω (u + N)) ℓ := by
      apply ae_iff.mpr
      apply le_antisymm ?_ zero_le
      calc
        law init {ω | ¬ (HomogeneousStart init ω u →
            1 ≤ frontCount (virtualLabels init ω u) ℓ →
            clockCount (virtualLabels init ω u) = C →
            ∃ N, StageEventSpec.bulkThreshold C ≤
              frontCount (virtualLabels init ω (u + N)) ℓ)} ≤
            law init (E ∩ {ω |
              (∀ t, ClockEnvironment (virtualLabels init ω (u + t))) ∧
              ¬ ∃ N, StageEventSpec.bulkThreshold C ≤
                frontCount (virtualLabels init ω (u + N)) ℓ}) := by
          apply measure_mono
          intro ω hbad
          have hbad' : HomogeneousStart init ω u ∧
              1 ≤ frontCount (virtualLabels init ω u) ℓ ∧
              clockCount (virtualLabels init ω u) = C ∧
              ¬ ∃ N, StageEventSpec.bulkThreshold C ≤
                frontCount (virtualLabels init ω (u + N)) ℓ := by
            simpa only [Set.mem_setOf_eq, _root_.not_imp] using hbad
          exact ⟨⟨hbad'.1, hbad'.2.1, hbad'.2.2.1⟩,
            (fun t => homogeneous_clockEnvironment init ω u hbad'.1 (u + t)
              (by omega)), hbad'.2.2.2⟩
        _ = 0 := hnull
    filter_upwards [hgood] with ω hω
    exact fun _ _ _ => hω
  · exact ae_of_all _ (fun _ hℓ hcap hdensity =>
      False.elim (hv ⟨hℓ, hcap, hdensity⟩))

/-- Every level through the virtual cap reaches bulk in finite raw time.
The initial time and Clock count may be chosen after the common full-measure
set has been fixed. -/
theorem finite_bulk_levels_ae (init : Cfg L 256) (hc : 2 ≤ init.card) :
    ∀ᵐ ω ∂law init, ∀ u C,
      HomogeneousStart init ω u →
      clockCount (virtualLabels init ω u) = C →
      11 ≤ C → 6 * init.card ≤ 25 * C →
      ∀ ℓ, ℓ ≤ 256 * (L + 1) →
        ∃ N, StageEventSpec.bulkThreshold C ≤
          frontCount (virtualLabels init ω (u + N)) ℓ := by
  filter_upwards [next_front_birth_everywhere_ae init hc,
    positive_front_bulk_everywhere_ae init hc] with ω hbirth hbulk
  intro u C hu hcount hC hdensity ℓ
  induction ℓ with
  | zero =>
      intro hcap
      refine ⟨0, ?_⟩
      simpa only [Nat.add_zero, frontCount_zero_eq_clockCount, hcount] using
        bulkThreshold_le_clockCount C
  | succ ℓ ih =>
      intro hcap
      obtain ⟨N, hN⟩ := ih (by omega)
      have hstart := homogeneousStart_of_time init ω u hu (u + N) (by omega)
      have htwo : 2 ≤ frontCount (virtualLabels init ω (u + N)) ℓ :=
        (two_le_bulkThreshold C hC).trans hN
      obtain ⟨R, hR⟩ := hbirth (u + N) ℓ hcap hstart htwo
      have hhom := homogeneousStart_of_time init ω u hu (u + N + R) (by omega)
      have hcount' : clockCount (virtualLabels init ω (u + N + R)) = C := by
        calc
          clockCount (virtualLabels init ω (u + N + R)) =
              clockCount (virtualLabels init ω u) :=
            congrArg Finset.card
              (clockSet_fixed_from_homogeneous init ω u hu (u + N + R) (by omega))
          _ = C := hcount
      obtain ⟨T, hT⟩ := hbulk (u + N + R) (ℓ + 1) C (by omega) hcap hdensity
        hhom (by omega) hcount'
      refine ⟨N + R + T, ?_⟩
      simpa only [Nat.add_assoc] using hT

open Classical in
/-- The genuine first bulk passage after u, in elapsed raw interactions. -/
def bulkPassageTime (init : Cfg L 256) (u ℓ C : ℕ) (ω : Ω L 256) : WithTop ℕ :=
  if h : ∃ N, StageEventSpec.bulkThreshold C ≤
    frontCount (virtualLabels init ω (u + N)) ℓ
  then ((Nat.find h : ℕ) : WithTop ℕ) else ⊤

theorem bulkPassageTime_le_iff (init : Cfg L 256) (u ℓ C N : ℕ) (ω : Ω L 256) :
    bulkPassageTime init u ℓ C ω ≤ (N : WithTop ℕ) ↔
      ∃ k ≤ N, StageEventSpec.bulkThreshold C ≤
        frontCount (virtualLabels init ω (u + k)) ℓ := by
  classical
  unfold bulkPassageTime
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

theorem bulkPassageTime_eq_top_iff (init : Cfg L 256) (u ℓ C : ℕ) (ω : Ω L 256) :
    bulkPassageTime init u ℓ C ω = ⊤ ↔
      ¬ ∃ N, StageEventSpec.bulkThreshold C ≤
        frontCount (virtualLabels init ω (u + N)) ℓ := by
  classical
  by_cases h : ∃ N, StageEventSpec.bulkThreshold C ≤
      frontCount (virtualLabels init ω (u + N)) ℓ <;>
    simp [bulkPassageTime, h]

theorem bulkPassageTime_isStoppingTime (init : Cfg L 256) (u ℓ C : ℕ) :
    IsStoppingTime (shiftedFiltration (pairLogFiltration L 256) u)
      (bulkPassageTime init u ℓ C) := by
  intro N
  have hm : MeasurableSet[shiftedFiltration (pairLogFiltration L 256) u N]
      (⋃ k, {ω | k ≤ N ∧ StageEventSpec.bulkThreshold C ≤
        frontCount (virtualLabels init ω (u + k)) ℓ}) := by
    refine MeasurableSet.iUnion fun k => ?_
    by_cases hk : k ≤ N
    · have hp : MeasurableSet[pairLogFiltration L 256 (u + k)]
          {ω | StageEventSpec.bulkThreshold C ≤
            frontCount (virtualLabels init ω (u + k)) ℓ} :=
        (show MeasurableSet {f : Fin init.card → AgentState L 256 |
            StageEventSpec.bulkThreshold C ≤ frontCount f ℓ} from
          (Set.to_countable _).measurableSet).preimage (measurable_virtualLabels init (u + k))
      have hp' : MeasurableSet[shiftedFiltration (pairLogFiltration L 256) u N]
          {ω | StageEventSpec.bulkThreshold C ≤
            frontCount (virtualLabels init ω (u + k)) ℓ} :=
        ((shiftedFiltration (pairLogFiltration L 256) u).mono hk) _ hp
      simpa only [hk, true_and] using hp'
    · simp only [hk, false_and, Set.setOf_false, MeasurableSet.empty]
  convert hm using 1
  ext ω
  simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
  exact bulkPassageTime_le_iff init u ℓ C N ω

theorem bulkPassage_failure_measurable (init : Cfg L 256) (u ℓ C N : ℕ)
    (E : Set (Ω L 256)) (hE : MeasurableSet[pairLogFiltration L 256 u] E) :
    MeasurableSet[pairLogFiltration L 256 (u + N)]
      (E ∩ {ω | (N : WithTop ℕ) < bulkPassageTime init u ℓ C ω}) :=
  (((pairLogFiltration L 256).mono (by omega : u ≤ u + N)) _ hE).inter
    ((bulkPassageTime_isStoppingTime init u ℓ C).measurableSet_gt N)

theorem below_bulk_of_lt_bulkPassageTime (init : Cfg L 256) (u ℓ C N : ℕ)
    (ω : Ω L 256) (hN : (N : WithTop ℕ) < bulkPassageTime init u ℓ C ω) :
    frontCount (virtualLabels init ω (u + N)) ℓ < StageEventSpec.bulkThreshold C := by
  apply lt_of_not_ge
  intro hhit
  have hle := (bulkPassageTime_le_iff init u ℓ C N ω).2 ⟨N, le_rfl, hhit⟩
  exact (not_lt_of_ge hle) hN

/-- The calibrated P3a bound for the genuine first target passage on an
observed homogeneous positive-front prefix. -/
theorem bulkPassage_prefix_tail (init : Cfg L 256) (hm : 20 ≤ init.card)
    (u ℓ C : ℕ) (hC : C ≤ init.card) (hdensity : 6 * init.card ≤ 25 * C)
    (hℓ : 1 ≤ ℓ) (hcap : ℓ ≤ 256 * (L + 1))
    (E : Set (Ω L 256)) (hE : MeasurableSet[pairLogFiltration L 256 u] E)
    (hhom : ∀ ω ∈ E, HomogeneousStart init ω u)
    (hstart : ∀ ω ∈ E, 1 ≤ frontCount (virtualLabels init ω u) ℓ ∧
      clockCount (virtualLabels init ω u) = C) :
    law init (E ∩ {ω | (PhaseThreeModel.Numeric.firstHitHorizon init.card : WithTop ℕ) <
      bulkPassageTime init u ℓ C ω}) ≤
      ENNReal.ofReal (1 / (init.card : ℝ) ^ 9) * law init E := by
  apply (measure_mono ?_).trans
    (observed_bulk_passage_prefix_tail init hm C ℓ u hC hdensity hℓ hcap E hE hstart)
  rintro ω ⟨he, htime⟩
  exact ⟨he, (fun t ht => homogeneous_clockEnvironment init ω u (hhom ω he)
    (u + t) (by omega)), below_bulk_of_lt_bulkPassageTime init u ℓ C _ ω htime⟩

/-- All genuine bulk-passage times through the cap are finite almost surely
on the observed homogeneous prefix. This null statement needs no
measurability assumption on E; quantitative tails above do require it. -/
theorem finite_bulk_passages_prefix_null (init : Cfg L 256) (hc : 2 ≤ init.card)
    (u C : ℕ) (hC : 11 ≤ C) (hdensity : 6 * init.card ≤ 25 * C)
    (E : Set (Ω L 256))
    (hstart : ∀ ω ∈ E, HomogeneousStart init ω u ∧
      clockCount (virtualLabels init ω u) = C) :
    law init (E ∩ {ω | ∃ ℓ, ℓ ≤ 256 * (L + 1) ∧
      bulkPassageTime init u ℓ C ω = ⊤}) = 0 := by
  have havoid : ∀ᵐ ω ∂law init, ω ∉ E ∩ {ω | ∃ ℓ, ℓ ≤ 256 * (L + 1) ∧
      bulkPassageTime init u ℓ C ω = ⊤} := by
    filter_upwards [finite_bulk_levels_ae init hc] with ω hω
    rintro ⟨he, ℓ, hcap, htop⟩
    exact (bulkPassageTime_eq_top_iff init u ℓ C ω).1 htop
      (hω u C (hstart ω he).1 (hstart ω he).2 hC hdensity ℓ hcap)
  simpa only [not_not] using ae_iff.mp havoid

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockFinitePassageLevels

end
