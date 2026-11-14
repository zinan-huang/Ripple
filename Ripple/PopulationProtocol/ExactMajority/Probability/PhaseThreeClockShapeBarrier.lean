-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockShapeBarrier.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockShapeFreeze

noncomputable section
open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal BigOperators MeasureTheory ProbabilityTheory

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockShapeBarrier

open TimeTheorem PairLog PairLogAuxiliary PhaseThreeScalar
  PhaseThreeClockVirtual PhaseThreeClockGatedLaw PhaseThreeClockGatedLevelOne
  PhaseThreeClockProbabilityFloors PhaseThreeClockPrefixTails
  PhaseThreeClockStoppedPassage PhaseThreeClockNormalRise
  PhaseThreeClockNormalRiseStoppedLaw PhaseThreeClockNormalBarrierAlgebra
  PhaseThreeClockNormalBarrierTails PhaseThreeClockShapeFreeze

variable {n : ℕ}

theorem gatedIndicator_adapted (init : InputCfg n) (ℓ t : ℕ) :
    StronglyMeasurable[pairLogFiltration _ _ (t + 1)] (gatedIndicator init ℓ t) := by
  have h := stronglyMeasurable_aux_pair_indicator init virtualRule (GatedTick ℓ) t
  convert h using 1
  funext ω
  simp only [gatedIndicator]
  split_ifs <;> rfl

theorem gatedIndicator_law (init : InputCfg n) (hc : 2 ≤ init.card) (ℓ t : ℕ) :
    (law init)[gatedIndicator init ℓ t | pairLogFiltration _ _ t] =ᵐ[law init]
      fun ω => ((goodPairs (GatedTick ℓ) (virtualLabels init ω t)).card : ℝ) /
        ((init.card : ℝ) * ((init.card : ℝ) - 1)) := by
  simpa only [gatedIndicator, virtualLabels] using gatedTick_conditional_law init hc ℓ t

theorem frozenFront_conditional_lower
    (init : InputCfg n) (hc : 2 ≤ init.card) (C : Finset (Fin init.card))
    (ℓ cutoff s u : ℕ) (hsu : s ≤ u) (hℓ : 1 ≤ ℓ)
    (hcap : ℓ ≤ 256 * (PhaseThreeModel.Numeric.hourIndex n + 1)) (t : ℕ) :
    ∀ᵐ ω ∂law init, shapeSafeAt init C s (u + t) ω →
      2 * frozenFront init C ℓ cutoff s u t ω *
          ((C.card : ℝ) - frozenFront init C ℓ cutoff s u t ω) /
          ((init.card : ℝ) * ((init.card : ℝ) - 1)) ≤
        (law init)[incrementIndicator (frozenFront init C ℓ cutoff s u) t |
          shiftedFiltration (pairLogFiltration _ _) u t] ω := by
  let ℱ := shiftedFiltration (pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256) u
  let A : Set (InputLog n) := {ω | shapeSafeAt init C s (u + t) ω}
  have hA : MeasurableSet[ℱ t] A :=
    shapeSafeAt_measurable init C s (u + t) (by omega)
  have hIi : Integrable (gatedIndicator init ℓ (u + t)) (law init) :=
    bernoulli_integrable (gatedIndicator_adapted init ℓ)
      (fun v => ae_of_all _ (gatedIndicator_zero_one init ℓ v)) (u + t)
  have hXi : Integrable
      (incrementIndicator (frozenFront init C ℓ cutoff s u) t) (law init) :=
    bernoulli_integrable
      (incrementIndicator_stronglyMeasurable _
        (frozenFront_adapted init C ℓ cutoff s u hsu))
      (fun v => ae_of_all _ (incrementIndicator_zero_one _ v)) t
  have hmono := condExp_mono (m := ℱ t)
    (hIi.indicator ((ℱ.le t) _ hA)) hXi
    (ae_of_all _ (gatedIndicator_le_frozenFront_increment
      init C ℓ cutoff s u hsu hℓ hcap t))
  have hN : (2 : ℝ) ≤ (init.card : ℝ) := by exact_mod_cast hc
  have hD : 0 ≤ (init.card : ℝ) * ((init.card : ℝ) - 1) :=
    mul_nonneg (by linarith) (by linarith)
  filter_upwards [hmono, condExp_indicator hIi hA,
    gatedIndicator_law init hc ℓ (u + t)] with ω hm hi hp
  intro hsafe
  have hmem : ω ∈ A := hsafe
  rw [hi, Set.indicator_of_mem hmem] at hm
  have hm' :
      ((goodPairs (GatedTick ℓ) (virtualLabels init ω (u + t))).card : ℝ) /
          ((init.card : ℝ) * ((init.card : ℝ) - 1)) ≤
        (law init)[incrementIndicator (frozenFront init C ℓ cutoff s u) t | ℱ t] ω := by
    simpa only [ℱ, shiftedFiltration_apply, hp] using hm
  have hg := shapeSafeAt_guard init C ℓ cutoff s (u + t) (by omega) hℓ ω hsafe
  have hclock : clockCount (virtualLabels init ω (u + t)) = C.card := by
    change (clockSet (virtualLabels init ω (u + t))).card = C.card
    rw [← hg.2.1]
  have hXC := frontCount_le_clockCount (virtualLabels init ω (u + t)) ℓ
  have hnum := epidemic_le_gated_pairs (virtualLabels init ω (u + t)) ℓ hℓ
  have hnumR :
      2 * (frontCount (virtualLabels init ω (u + t)) ℓ : ℝ) *
        ((clockCount (virtualLabels init ω (u + t)) : ℝ) -
          (frontCount (virtualLabels init ω (u + t)) ℓ : ℝ)) ≤
        ((goodPairs (GatedTick ℓ) (virtualLabels init ω (u + t))).card : ℝ) := by
    have hcast :
        ((2 * frontCount (virtualLabels init ω (u + t)) ℓ *
          (clockCount (virtualLabels init ω (u + t)) -
            frontCount (virtualLabels init ω (u + t)) ℓ) : ℕ) : ℝ) ≤
          ((goodPairs (GatedTick ℓ) (virtualLabels init ω (u + t))).card : ℝ) := by
      exact_mod_cast hnum
    simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub hXC] using hcast
  have hx : frozenFront init C ℓ cutoff s u t ω =
      (frontCount (virtualLabels init ω (u + t)) ℓ : ℝ) := by
    simp only [frozenFront, frozenShapeCounts_eq_raw init C ℓ cutoff s u t ω hsafe,
      rawShapeCounts]
  rw [hx]
  exact (div_le_div_of_nonneg_right (by simpa only [hclock] using hnumR) hD).trans hm'

theorem frozenNormal_conditional_upper
    (init : InputCfg n) (hc : 2 ≤ init.card) (C : Finset (Fin init.card))
    (ℓ cutoff s u : ℕ) (hsu : s ≤ u) (hℓ : 1 ≤ ℓ)
    (hcap : ℓ + 1 ≤ 256 * (PhaseThreeModel.Numeric.hourIndex n + 1)) (t : ℕ) :
    ∀ᵐ ω ∂law init, shapeSafeAt init C s (u + t) ω →
      (law init)[incrementIndicator (frozenNormal init C ℓ cutoff s u) t |
        shiftedFiltration (pairLogFiltration _ _) u t] ω ≤
      ((frozenFront init C ℓ cutoff s u t ω) ^ 2 +
        2 * (C.card : ℝ) * frozenNormal init C ℓ cutoff s u t ω) /
          ((init.card : ℝ) * ((init.card : ℝ) - 1)) := by
  let ℱ := shiftedFiltration (pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256) u
  have hYi : Integrable
      (incrementIndicator (frozenNormal init C ℓ cutoff s u) t) (law init) :=
    bernoulli_integrable
      (incrementIndicator_stronglyMeasurable _
        (frozenNormal_adapted init C ℓ cutoff s u hsu))
      (fun v => ae_of_all _ (incrementIndicator_zero_one _ v)) t
  have hNi : Integrable
      (nextSafeNormalIndicator init C ℓ cutoff s (u + t)) (law init) :=
    bernoulli_integrable
      (nextSafeNormalIndicator_stronglyMeasurable init C ℓ cutoff s)
      (fun v => ae_of_all _ (nextSafeNormalIndicator_zero_one init C ℓ cutoff s v))
      (u + t)
  have hmono := condExp_mono (m := ℱ t) hYi hNi
    (ae_of_all _ (frozenNormal_increment_le_nextSafe init C ℓ cutoff s u hsu hℓ t))
  filter_upwards [hmono, nextSafeNormalIndicator_conditional_upper_from_seed
    init hc C ℓ cutoff s (u + t) (by omega) hℓ hcap] with ω hm hu
  intro hsafe
  have hupper := hu hsafe.1.1 hsafe.1.2.symm hsafe.2
  have hx : frozenFront init C ℓ cutoff s u t ω =
      (frontCount (virtualLabels init ω (u + t)) ℓ : ℝ) := by
    simp only [frozenFront, frozenShapeCounts_eq_raw init C ℓ cutoff s u t ω hsafe,
      rawShapeCounts]
  have hy : frozenNormal init C ℓ cutoff s u t ω =
      (normalCount (virtualLabels init ω (u + t))
        (PhaseThreeClockEarlyMarks.markedAt init C ℓ cutoff s ω (u + t)) ℓ : ℝ) := by
    simp only [frozenNormal, frozenShapeCounts_eq_raw init C ℓ cutoff s u t ω hsafe,
      rawShapeCounts]
  rw [hx, hy]
  exact hm.trans hupper

def shapeRegion (init : InputCfg n) (C : Finset (Fin init.card))
    (ℓ cutoff s u t : ℕ) (ω : InputLog n) : Prop :=
  shapeSafeAt init C s (u + t) ω ∧
    frozenFront init C ℓ cutoff s u t ω / (C.card : ℝ) ≤ 101 / 1000 ∧
    normalPotential (C.card : ℝ)
      (frozenFront init C ℓ cutoff s u t ω) (frozenNormal init C ℓ cutoff s u t ω) ≤ 0

open Classical in
def shapeBarrierStop (init : InputCfg n) (C : Finset (Fin init.card))
    (ℓ cutoff s u : ℕ) (ω : InputLog n) : WithTop ℕ :=
  if h : ∃ t, ¬ shapeRegion init C ℓ cutoff s u t ω
  then ((Nat.find h : ℕ) : WithTop ℕ) else ⊤

theorem shapeBarrierStop_le_iff (init : InputCfg n) (C : Finset (Fin init.card))
    (ℓ cutoff s u N : ℕ) (ω : InputLog n) :
    shapeBarrierStop init C ℓ cutoff s u ω ≤ (N : WithTop ℕ) ↔
      ∃ t ≤ N, ¬ shapeRegion init C ℓ cutoff s u t ω := by
  classical
  unfold shapeBarrierStop
  split_ifs with h
  · constructor
    · intro hle
      have ht : Nat.find h ≤ N := by exact_mod_cast hle
      exact ⟨Nat.find h, ht, Nat.find_spec h⟩
    · rintro ⟨t, ht, hbad⟩
      have hle : Nat.find h ≤ N := (Nat.find_min' h hbad).trans ht
      exact_mod_cast hle
  · constructor
    · intro hle
      exact absurd hle (by simp)
    · rintro ⟨t, _, hbad⟩
      exact absurd ⟨t, hbad⟩ h

theorem shapeRegion_before_stop (init : InputCfg n) (C : Finset (Fin init.card))
    (ℓ cutoff s u t : ℕ) (ω : InputLog n)
    (ht : (t : WithTop ℕ) < shapeBarrierStop init C ℓ cutoff s u ω) :
    shapeRegion init C ℓ cutoff s u t ω := by
  by_contra hbad
  exact (not_lt_of_ge ((shapeBarrierStop_le_iff init C ℓ cutoff s u t ω).2
    ⟨t, le_rfl, hbad⟩)) ht

theorem shapeBarrierStop_finite_failure (init : InputCfg n)
    (C : Finset (Fin init.card)) (ℓ cutoff s u t : ℕ) (ω : InputLog n)
    (ht : shapeBarrierStop init C ℓ cutoff s u ω = (t : WithTop ℕ)) :
    ¬ shapeRegion init C ℓ cutoff s u t ω := by
  classical
  unfold shapeBarrierStop at ht
  split_ifs at ht with h
  · have he : Nat.find h = t := WithTop.coe_injective ht
    simpa only [he] using Nat.find_spec h
  · exact absurd ht WithTop.top_ne_coe

theorem shapeRegion_measurable (init : InputCfg n) (C : Finset (Fin init.card))
    (ℓ cutoff s u : ℕ) (hsu : s ≤ u) (t : ℕ) :
    MeasurableSet[shiftedFiltration (pairLogFiltration _ _) u t]
      {ω | shapeRegion init C ℓ cutoff s u t ω} := by
  have hx := frozenFront_adapted init C ℓ cutoff s u hsu t
  have hy := frozenNormal_adapted init C ℓ cutoff s u hsu t
  have hr : StronglyMeasurable[shiftedFiltration (pairLogFiltration _ _) u t]
      (fun ω => frozenFront init C ℓ cutoff s u t ω / (C.card : ℝ)) := by
    simpa only [div_eq_mul_inv] using hx.mul_const (C.card : ℝ)⁻¹
  have hf : StronglyMeasurable[shiftedFiltration (pairLogFiltration _ _) u t]
      (fun ω => normalPotential (C.card : ℝ)
        (frozenFront init C ℓ cutoff s u t ω)
        (frozenNormal init C ℓ cutoff s u t ω)) := by
    unfold normalPotential
    simpa only [div_eq_mul_inv] using
      hy.sub (((hx.pow 2).const_mul (9 / 10 : ℝ)).mul_const (C.card : ℝ)⁻¹)
  exact (shapeSafeAt_measurable init C s (u + t) (by omega)).inter
    ((measurableSet_le hr.measurable measurable_const).inter
      (measurableSet_le hf.measurable measurable_const))

theorem shapeBarrierStop_isStoppingTime (init : InputCfg n)
    (C : Finset (Fin init.card)) (ℓ cutoff s u : ℕ) (hsu : s ≤ u) :
    IsStoppingTime (shiftedFiltration (pairLogFiltration _ _) u)
      (shapeBarrierStop init C ℓ cutoff s u) := by
  intro N
  have hm : MeasurableSet[shiftedFiltration (pairLogFiltration _ _) u N]
      (⋃ t, {ω | t ≤ N ∧ ¬ shapeRegion init C ℓ cutoff s u t ω}) := by
    refine MeasurableSet.iUnion fun t => ?_
    by_cases ht : t ≤ N
    · have hbad := ((shiftedFiltration (pairLogFiltration _ _) u).mono ht) _
        (shapeRegion_measurable init C ℓ cutoff s u hsu t).compl
      simpa only [ht, true_and] using hbad
    · simp only [ht, false_and, Set.setOf_false, MeasurableSet.empty]
  convert hm using 1
  ext ω
  simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
  exact shapeBarrierStop_le_iff init C ℓ cutoff s u N ω

def actualNormalBarrierData (init : InputCfg n) (hc : 2 ≤ init.card)
    (C : Finset (Fin init.card)) (hC : 0 < C.card)
    (ℓ cutoff s u : ℕ) (hsu : s ≤ u) (hℓ : 1 ≤ ℓ)
    (hcap : ℓ + 1 ≤ 256 * (PhaseThreeModel.Numeric.hourIndex n + 1)) :
    NormalBarrierData (law init) (shiftedFiltration (pairLogFiltration _ _) u)
      (C.card : ℝ) ((init.card : ℝ) * ((init.card : ℝ) - 1)) where
  positive_clock := by exact_mod_cast hC
  positive_denominator := by
    have hm : (2 : ℝ) ≤ (init.card : ℝ) := by exact_mod_cast hc
    exact mul_pos (by linarith) (by linarith)
  X := frozenFront init C ℓ cutoff s u
  Y := frozenNormal init C ℓ cutoff s u
  stop := shapeBarrierStop init C ℓ cutoff s u
  adapted_front := frozenFront_adapted init C ℓ cutoff s u hsu
  adapted_normal := frozenNormal_adapted init C ℓ cutoff s u hsu
  stopping := shapeBarrierStop_isStoppingTime init C ℓ cutoff s u hsu
  front_nonneg := frozenFront_nonneg init C ℓ cutoff s u
  normal_upper := frozenNormal_bound init C ℓ cutoff s u hsu hℓ
  region := fun t ω ht => (shapeRegion_before_stop init C ℓ cutoff s u t ω ht).2
  front_increment := fun t ω _ =>
    frozenFront_delta_cases init C ℓ cutoff s u hsu hℓ (by omega) t ω
  normal_increment := fun t ω _ =>
    frozenNormal_delta_cases init C ℓ cutoff s u hsu hℓ hcap t ω
  front_rate := by
    intro t
    filter_upwards [frozenFront_conditional_lower init hc C ℓ cutoff s u hsu hℓ
      (by omega) t] with ω hω
    intro ht
    exact hω (shapeRegion_before_stop init C ℓ cutoff s u t ω ht).1
  normal_rate := by
    intro t
    filter_upwards [frozenNormal_conditional_upper init hc C ℓ cutoff s u hsu hℓ hcap t]
      with ω hω
    intro ht
    exact hω (shapeRegion_before_stop init C ℓ cutoff s u t ω ht).1

theorem frozen_initial_eq (init : InputCfg n) (C : Finset (Fin init.card))
    (ℓ cutoff s u : ℕ) (ω : InputLog n) (hsafe : shapeSafeAt init C s u ω) :
    frozenFront init C ℓ cutoff s u 0 ω =
      (frontCount (virtualLabels init ω u) ℓ : ℝ) ∧
    frozenNormal init C ℓ cutoff s u 0 ω =
      (normalCount (virtualLabels init ω u)
        (PhaseThreeClockEarlyMarks.markedAt init C ℓ cutoff s ω u) ℓ : ℝ) := by
  have h := frozenShapeCounts_eq_raw init C ℓ cutoff s u 0 ω
    (by simpa only [Nat.add_zero] using hsafe)
  simp only [frozenFront, frozenNormal, h, rawShapeCounts, Nat.add_zero, and_self]

theorem raw_crossing_mem_normalBarrierCrossing
    (init : InputCfg n) (hc : 2 ≤ init.card) (C : Finset (Fin init.card))
    (hC : 0 < C.card) (ℓ cutoff s u : ℕ) (hsu : s ≤ u) (hℓ : 1 ≤ ℓ)
    (hcap : ℓ + 1 ≤ 256 * (PhaseThreeModel.Numeric.hourIndex n + 1))
    (N : ℕ) (ω : InputLog n) (hsafe : shapeSafeAt init C s (u + N) ω)
    (hx : (frontCount (virtualLabels init ω (u + N)) ℓ : ℝ) /
      (C.card : ℝ) ≤ 101 / 1000)
    (hF : 0 ≤ normalPotential (C.card : ℝ)
      (frontCount (virtualLabels init ω (u + N)) ℓ : ℝ)
      (normalCount (virtualLabels init ω (u + N))
        (PhaseThreeClockEarlyMarks.markedAt init C ℓ cutoff s ω (u + N)) ℓ : ℝ)) :
    ω ∈ normalBarrierCrossing
      (actualNormalBarrierData init hc C hC ℓ cutoff s u hsu hℓ hcap) := by
  have hxN : frozenFront init C ℓ cutoff s u N ω =
      (frontCount (virtualLabels init ω (u + N)) ℓ : ℝ) := by
    simp only [frozenFront, frozenShapeCounts_eq_raw init C ℓ cutoff s u N ω hsafe,
      rawShapeCounts]
  have hyN : frozenNormal init C ℓ cutoff s u N ω =
      (normalCount (virtualLabels init ω (u + N))
        (PhaseThreeClockEarlyMarks.markedAt init C ℓ cutoff s ω (u + N)) ℓ : ℝ) := by
    simp only [frozenNormal, frozenShapeCounts_eq_raw init C ℓ cutoff s u N ω hsafe,
      rawShapeCounts]
  change ∃ t : ℕ, (t : WithTop ℕ) ≤ shapeBarrierStop init C ℓ cutoff s u ω ∧
    0 ≤ normalPotential (C.card : ℝ) (frozenFront init C ℓ cutoff s u t ω)
      (frozenNormal init C ℓ cutoff s u t ω)
  by_cases hN : (N : WithTop ℕ) ≤ shapeBarrierStop init C ℓ cutoff s u ω
  · exact ⟨N, hN, by simpa only [hxN, hyN] using hF⟩
  · have hlt : shapeBarrierStop init C ℓ cutoff s u ω < (N : WithTop ℕ) :=
      lt_of_not_ge hN
    have hfinite : shapeBarrierStop init C ℓ cutoff s u ω ≠ ⊤ := by
      intro he
      rw [he] at hlt
      exact not_lt_of_ge le_top hlt
    obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.mp hfinite
    have htN : t ≤ N := by
      rw [← ht] at hlt
      exact WithTop.coe_le_coe.mp hlt.le
    have hsafeT := shapeSafeAt_anti init C s (u + t) (u + N) (by omega) ω hsafe
    have hmono := frozenFront_mono init C ℓ cutoff s u hsu hℓ (by omega) ω htN
    have hCnonneg : (0 : ℝ) ≤ C.card := Nat.cast_nonneg _
    have hratio : frozenFront init C ℓ cutoff s u t ω / (C.card : ℝ) ≤
        101 / 1000 := by
      apply (div_le_div_of_nonneg_right hmono hCnonneg).trans
      simpa only [hxN] using hx
    have hbad := shapeBarrierStop_finite_failure init C ℓ cutoff s u t ω ht.symm
    refine ⟨t, ht.le, ?_⟩
    exact (lt_of_not_ge (fun hf => hbad ⟨hsafeT, hratio, hf⟩)).le

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockShapeBarrier

end
