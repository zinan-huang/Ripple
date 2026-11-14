-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockLowerPassageProcess.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockLowerPassageDiscount
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockBulkClockPassage
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockThinningCalibrated
import Mathlib.MeasureTheory.Function.Floor

/-!
P7 on the actual pair-log law.  Positive-level gated pair counts supply
the upper front rate.  A front freezes immediately before a failed
shapeSafeAt guard; its observed Clock-count discount is then stopped at
the finite contact horizon.  The final safe event is intersected only
after the unconditional exponential maximal estimate.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators MeasureTheory ProbabilityTheory

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockLowerPassageProcess

open TimeTheorem PairLog PairLogAuxiliary PhaseThreeScalar
  PhaseThreeClockVirtual PhaseThreeClockGatedLaw PhaseThreeClockGatedLevelOne
  PhaseThreeClockProbabilityFloors PhaseThreeClockPrefixTails
  PhaseThreeClockStoppedPassage PhaseThreeClockThinning
  PhaseThreeClockThinningCalibrated PhaseThreeClockShapeFreeze
  PhaseThreeClockShapeBarrier PhaseThreeClockNormalBarrierTails
  PhaseThreeClockBulkClockPassage PhaseThreeClockLowerPassageAlgebra
  PhaseThreeClockLowerPassageDiscount

variable {L K n m : ℕ}

theorem positive_gated_pairs_upper (f : Fin m → AgentState L K)
    (ell : ℕ) (hell : 1 ≤ ell) :
    ((goodPairs (GatedTick (ell + 1)) f).card : ℝ) ≤
      (frontCount f ell : ℝ) ^ 2 +
        2 * (clockCount f : ℝ) * (frontCount f (ell + 1) : ℝ) := by
  have hpred := frontCount_pred f (ell + 1) (by omega)
  simp only [Nat.add_sub_cancel] at hpred
  have hexact : exactCount f ell ≤ frontCount f ell := by omega
  have hn :
      (goodPairs (GatedTick (ell + 1)) f).card ≤
        2 * frontCount f (ell + 1) * clockCount f + frontCount f ell ^ 2 := by
    rw [goodPairs_gatedTick_eq_of_two_le f (ell + 1) (by omega),
      goodPairs_raisingTick_card, Nat.add_sub_cancel]
    apply add_le_add
    · exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    · calc
        _ ≤ exactCount f ell * exactCount f ell :=
          Nat.mul_le_mul_left _ (Nat.sub_le _ _)
        _ ≤ frontCount f ell * frontCount f ell := Nat.mul_le_mul hexact hexact
        _ = _ := (pow_two _).symm
  have hR :
      ((goodPairs (GatedTick (ell + 1)) f).card : ℝ) ≤
        2 * (frontCount f (ell + 1) : ℝ) * clockCount f +
          (frontCount f ell : ℝ) ^ 2 := by exact_mod_cast hn
  nlinarith only [hR]

theorem frozenFront_upper (init : InputCfg n) (C : Finset (Fin init.card))
    (ell s u : ℕ) (hsu : s ≤ u) (hell : 1 ≤ ell) (t : ℕ) (ω : InputLog n) :
    frozenFront init C ell 0 s u t ω ≤ (C.card : ℝ) := by
  classical
  have hraw (v : ℕ) (hsv : s ≤ v) (hs : shapeSafeAt init C s v ω) :
      frontCount (virtualLabels init ω v) ell ≤ C.card := by
    have hg := shapeSafeAt_guard init C ell 0 s v hsv hell ω hs
    have hcount : clockCount (virtualLabels init ω v) = C.card := by
      change (clockSet (virtualLabels init ω v)).card = C.card
      rw [← hg.2.1]
    exact (frontCount_le_clockCount _ ell).trans_eq hcount
  have hb : (frozenShapeCounts init C ell 0 s u t ω).1 ≤ C.card := by
    induction t with
    | zero =>
        by_cases hs : shapeSafeAt init C s u ω
        · simpa only [frozenShapeCounts, if_pos hs, rawShapeCounts] using hraw u hsu hs
        · simp only [frozenShapeCounts, if_neg hs, Nat.zero_le]
    | succ t ih =>
        by_cases hs : shapeSafeAt init C s (u + (t + 1)) ω
        · simpa only [frozenShapeCounts, if_pos hs, rawShapeCounts] using hraw _ (by omega) hs
        · simpa only [frozenShapeCounts, if_neg hs] using ih
  unfold frozenFront
  exact_mod_cast hb

theorem frozenFront_initial_le (init : InputCfg n) (C : Finset (Fin init.card))
    (ell s u : ℕ) (ω : InputLog n) :
    frozenFront init C ell 0 s u 0 ω ≤ (frontCount (virtualLabels init ω u) ell : ℝ) := by
  classical
  by_cases hs : shapeSafeAt init C s u ω
  · simp only [frozenFront, frozenShapeCounts, if_pos hs, rawShapeCounts, le_refl]
  · simp only [frozenFront, frozenShapeCounts, if_neg hs, Nat.cast_zero]
    positivity

theorem frozenFront_increment_le_current_gated
    (init : InputCfg n) (C : Finset (Fin init.card))
    (ell s u : ℕ) (hsu : s ≤ u) (hell : 1 ≤ ell) (htop : ell ≤ PhaseThreeModel.Numeric.clockCap n)
    (t : ℕ) (ω : InputLog n) :
    incrementIndicator (frozenFront init C ell 0 s u) t ω ≤
      ({ω | shapeSafeAt init C s (u + t) ω}.indicator
        (gatedIndicator init ell (u + t))) ω := by
  classical
  have hcap : ell ≤ 256 * (PhaseThreeModel.Numeric.hourIndex n + 1) := htop
  rw [incrementIndicator_eq_increment _ _ _ (frozenFront_delta_cases
    init C ell 0 s u hsu hell hcap t ω)]
  by_cases hs : shapeSafeAt init C s (u + (t + 1)) ω
  · have hc := shapeSafeAt_anti init C s (u + t) (u + (t + 1)) (by omega) ω hs
    rw [frozenFront_delta_of_safe init C ell 0 s u t hsu hell hcap ω hs,
      Set.indicator_of_mem (show ω ∈ {ω | shapeSafeAt init C s (u + t) ω} from hc)]
  · have he := frozenShapeCounts_skip init C ell 0 s u t ω hs
    simp only [frozenFront, he, sub_self]
    by_cases hc : shapeSafeAt init C s (u + t) ω
    · rw [Set.indicator_of_mem (show ω ∈ {ω | shapeSafeAt init C s (u + t) ω} from hc)]
      rcases gatedIndicator_zero_one init ell (u + t) ω with h | h <;>
        simp only [h] <;> norm_num
    · simp only [Set.indicator_of_notMem (show ω ∉ {ω | shapeSafeAt init C s (u + t) ω} from hc), le_refl]

theorem current_gated_le_mask (init : InputCfg n) (C : Finset (Fin init.card))
    (ell s v : ℕ) (hsv : s ≤ v) (hell : 1 ≤ ell) (ω : InputLog n) :
    ({ω | shapeSafeAt init C s v ω}.indicator (gatedIndicator init ell v)) ω ≤
      maskTickIndicator init C v ω := by
  classical
  have hJ : 0 ≤ maskTickIndicator init C v ω := by
    rcases maskTickIndicator_zero_one init C v ω with h | h <;> simp only [h] <;> norm_num
  by_cases hs : shapeSafeAt init C s v ω
  · rw [Set.indicator_of_mem (show ω ∈ {ω | shapeSafeAt init C s v ω} from hs)]
    unfold gatedIndicator
    split_ifs with hg
    · obtain ⟨i, j, hd, ht⟩ := hg
      have hr := gatedTick_clock_roles (virtualLabels init ω v) ell i j ht
      have hguard := shapeSafeAt_guard init C ell 0 s v hsv hell ω hs
      have hi : i ∈ C := by
        rw [hguard.2.1]
        simpa only [clockSet, Finset.mem_filter, Finset.mem_univ, true_and] using hr.1
      have hj : j ∈ C := by
        rw [hguard.2.1]
        simpa only [clockSet, Finset.mem_filter, Finset.mem_univ, true_and] using hr.2
      have hm : maskContact init C (v + 1) ω := ⟨i, j, hd, hi, hj⟩
      simp only [maskTickIndicator, if_pos hm, le_refl]
    · exact hJ
  · simpa only [Set.indicator_of_notMem (show ω ∉ {ω | shapeSafeAt init C s v ω} from hs)] using hJ

theorem frozenFront_increment_le_mask (init : InputCfg n) (C : Finset (Fin init.card))
    (ell s u : ℕ) (hsu : s ≤ u) (hell : 1 ≤ ell) (htop : ell ≤ PhaseThreeModel.Numeric.clockCap n)
    (t : ℕ) (ω : InputLog n) :
    incrementIndicator (frozenFront init C ell 0 s u) t ω ≤
      maskTickIndicator init C (u + t) ω :=
  (frozenFront_increment_le_current_gated init C ell s u hsu hell htop t ω).trans
    (current_gated_le_mask init C ell s (u + t) (by omega) hell ω)

def lowerTicks (init : InputCfg n) (C : Finset (Fin init.card)) (u t : ℕ)
    (ω : InputLog n) : ℕ := maskContacts init C u (u + t) ω

theorem lowerTicks_real (init : InputCfg n) (C : Finset (Fin init.card))
    (u t : ℕ) (ω : InputLog n) :
    (lowerTicks init C u t ω : ℝ) = maskTickCount init C u t ω :=
  (maskTickCount_eq_contacts init C u t ω).symm

theorem lowerTicks_measurable (init : InputCfg n) (C : Finset (Fin init.card))
    (u t : ℕ) :
    Measurable[shiftedFiltration (pairLogFiltration _ _) u t] (lowerTicks init C u t) := by
  have h := Nat.measurable_floor.comp
    (maskTickCount_stronglyMeasurable init C u t).measurable
  convert h using 1
  funext ω
  show lowerTicks init C u t ω = ⌊maskTickCount init C u t ω⌋₊
  rw [← lowerTicks_real init C u t ω]
  simp

theorem lowerTicks_zero (init : InputCfg n) (C : Finset (Fin init.card))
    (u : ℕ) (ω : InputLog n) : lowerTicks init C u 0 ω = 0 := by
  simp [lowerTicks, maskContacts]

theorem lowerTicks_step (init : InputCfg n) (C : Finset (Fin init.card))
    (u t : ℕ) (ω : InputLog n) :
    (lowerTicks init C u (t + 1) ω : ℝ) =
      (lowerTicks init C u t ω : ℝ) + maskTickIndicator init C (u + t) ω := by
  simpa only [lowerTicks_real] using maskTickCount_succ init C u t ω

theorem frozenFront_progress (init : InputCfg n) (C : Finset (Fin init.card))
    (ell s u : ℕ) (hsu : s ≤ u) (hell : 1 ≤ ell) (htop : ell ≤ PhaseThreeModel.Numeric.clockCap n)
    (t : ℕ) (ω : InputLog n) :
    frozenFront init C ell 0 s u t ω ≤ frozenFront init C ell 0 s u 0 ω +
      (lowerTicks init C u t ω : ℝ) := by
  induction t with
  | zero => simp only [lowerTicks_zero, Nat.cast_zero, add_zero, le_refl]
  | succ t ih =>
      have hi := frozenFront_increment_le_mask init C ell s u hsu hell htop t ω
      rw [incrementIndicator_eq_increment _ _ _ (frozenFront_delta_cases
        init C ell 0 s u hsu hell htop t ω)] at hi
      rw [lowerTicks_step]
      linarith only [ih, hi]

def lowerWindow (init : InputCfg n) (C : Finset (Fin init.card))
    (ell s u t : ℕ) (ω : InputLog n) : Prop :=
  lowerTicks init C u t ω < lowerHorizon C.card ∧
    frozenFront init C ell 0 s u t ω ≤
      (StageEventSpec.bulkThreshold C.card : ℝ) + (lowerTicks init C u t ω : ℝ)

open Classical in
def lowerStop (init : InputCfg n) (C : Finset (Fin init.card))
    (ell s u : ℕ) (ω : InputLog n) : WithTop ℕ :=
  if h : ∃ t, ¬ lowerWindow init C ell s u t ω
  then ((Nat.find h : ℕ) : WithTop ℕ) else ⊤

theorem lowerStop_le_iff (init : InputCfg n) (C : Finset (Fin init.card))
    (ell s u N : ℕ) (ω : InputLog n) :
    lowerStop init C ell s u ω ≤ (N : WithTop ℕ) ↔
      ∃ t ≤ N, ¬ lowerWindow init C ell s u t ω := by
  classical
  unfold lowerStop
  split_ifs with h
  · constructor
    · intro hle
      exact ⟨Nat.find h, by exact_mod_cast hle, Nat.find_spec h⟩
    · rintro ⟨t, ht, hbad⟩
      exact_mod_cast (Nat.find_min' h hbad).trans ht
  · constructor
    · intro hle
      exact absurd hle (by simp)
    · rintro ⟨t, _, hbad⟩
      exact absurd ⟨t, hbad⟩ h

theorem lowerWindow_of_lt_stop (init : InputCfg n) (C : Finset (Fin init.card))
    (ell s u t : ℕ) (ω : InputLog n)
    (ht : (t : WithTop ℕ) < lowerStop init C ell s u ω) :
    lowerWindow init C ell s u t ω := by
  by_contra hbad
  exact (not_lt_of_ge ((lowerStop_le_iff init C ell s u t ω).2 ⟨t, le_rfl, hbad⟩)) ht

theorem lowerWindow_measurable (init : InputCfg n) (C : Finset (Fin init.card))
    (ell s u : ℕ) (hsu : s ≤ u) (t : ℕ) :
    MeasurableSet[shiftedFiltration (pairLogFiltration _ _) u t]
      {ω | lowerWindow init C ell s u t ω} := by
  have hN := lowerTicks_measurable init C u t
  have hNR : Measurable[shiftedFiltration (pairLogFiltration _ _) u t]
      (fun ω => (lowerTicks init C u t ω : ℝ)) :=
    (measurable_of_countable (fun j : ℕ => (j : ℝ))).comp hN
  exact (measurableSet_lt hN measurable_const).inter
    (measurableSet_le (frozenFront_adapted init C ell 0 s u hsu t).measurable
      (measurable_const.add hNR))

theorem lowerStop_isStoppingTime (init : InputCfg n) (C : Finset (Fin init.card))
    (ell s u : ℕ) (hsu : s ≤ u) :
    IsStoppingTime (shiftedFiltration (pairLogFiltration _ _) u)
      (lowerStop init C ell s u) := by
  intro N
  have hm : MeasurableSet[shiftedFiltration (pairLogFiltration _ _) u N]
      (⋃ t : ℕ, {ω | t ≤ N ∧ ¬ lowerWindow init C ell s u t ω}) := by
    refine MeasurableSet.iUnion fun t => ?_
    by_cases ht : t ≤ N
    · have hbad := ((shiftedFiltration (pairLogFiltration _ _) u).mono ht) _
        (lowerWindow_measurable init C ell s u hsu t).compl
      simpa only [ht, true_and] using hbad
    · simp only [ht, false_and, Set.setOf_false, MeasurableSet.empty]
  convert hm using 1
  ext ω
  simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
  exact lowerStop_le_iff init C ell s u N ω

/-- The original scheduler, rather than an assumed embedded drift. -/
theorem lower_frozen_conditional_rate (init : InputCfg n) (hc : 2 ≤ init.card)
    (C : Finset (Fin init.card)) (hC : 1000000 ≤ C.card)
    (ell s u : ℕ) (hsu : s ≤ u) (hell : 1 ≤ ell)
    (htop : ell + 1 ≤ PhaseThreeModel.Numeric.clockCap n) (t : ℕ) :
    ∀ᵐ ω ∂law init, (t : WithTop ℕ) < lowerStop init C ell s u ω →
      (law init)[incrementIndicator (frozenFront init C (ell + 1) 0 s u) t |
        shiftedFiltration (pairLogFiltration _ _) u t] ω ≤
      (law init)[maskTickIndicator init C (u + t) |
        shiftedFiltration (pairLogFiltration _ _) u t] ω *
          lowerRate C.card (lowerTicks init C u t ω)
            (frozenFront init C (ell + 1) 0 s u t ω) := by
  let ℱ := shiftedFiltration (pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256) u
  let A : Set (InputLog n) := {ω | shapeSafeAt init C s (u + t) ω}
  let I := incrementIndicator (frozenFront init C (ell + 1) 0 s u) t
  have hA : MeasurableSet[ℱ t] A :=
    shapeSafeAt_measurable init C s (u + t) (by omega)
  have hIi : Integrable I (law init) := bernoulli_integrable
    (incrementIndicator_stronglyMeasurable _
      (frozenFront_adapted init C (ell + 1) 0 s u hsu))
    (fun k => ae_of_all _ (incrementIndicator_zero_one _ k)) t
  have hGi : Integrable (gatedIndicator init (ell + 1) (u + t)) (law init) :=
    bernoulli_integrable (gatedIndicator_adapted init (ell + 1))
      (fun v => ae_of_all _ (gatedIndicator_zero_one init (ell + 1) v)) (u + t)
  have hmono := condExp_mono (m := ℱ t) hIi
    (hGi.indicator ((ℱ.le t) _ hA))
    (ae_of_all _ (frozenFront_increment_le_current_gated
      init C (ell + 1) s u hsu (by omega) htop t))
  have hq := (mask_rate_bounds init hc C (by omega)).1.le
  have hmR : (2 : ℝ) ≤ init.card := by exact_mod_cast hc
  have hCR : (1000000 : ℝ) ≤ C.card := by exact_mod_cast hC
  have hden : 0 < (init.card : ℝ) * ((init.card : ℝ) - 1) :=
    mul_pos (by linarith) (by linarith)
  filter_upwards [hmono, condExp_indicator hGi hA,
    gatedIndicator_law init hc (ell + 1) (u + t),
    maskTickIndicator_conditional_law init hc C (u + t)] with ω hm hi hg hJ
  intro ht
  have hw := lowerWindow_of_lt_stop init C ell s u t ω ht
  change (law init)[I | ℱ t] ω ≤ _
  have hJ' :
      (law init)[maskTickIndicator init C (u + t) | ℱ t] ω =
        clockMaskRate init.card C.card := hJ
  rw [hJ']
  by_cases hs : shapeSafeAt init C s (u + t) ω
  · have hguard := shapeSafeAt_guard init C ell 0 s (u + t) (by omega) hell ω hs
    have hcount : clockCount (virtualLabels init ω (u + t)) = C.card := by
      change (clockSet (virtualLabels init ω (u + t))).card = C.card
      rw [← hguard.2.1]
    have hX : frozenFront init C ell 0 s u t ω =
        (frontCount (virtualLabels init ω (u + t)) ell : ℝ) := by
      simp only [frozenFront, frozenShapeCounts_eq_raw init C ell 0 s u t ω hs,
        rawShapeCounts]
    have hY : frozenFront init C (ell + 1) 0 s u t ω =
        (frontCount (virtualLabels init ω (u + t)) (ell + 1) : ℝ) := by
      simp only [frozenFront, frozenShapeCounts_eq_raw init C (ell + 1) 0 s u t ω hs,
        rawShapeCounts]
    have hp := positive_gated_pairs_upper (virtualLabels init ω (u + t)) ell hell
    rw [hcount, ← hX, ← hY] at hp
    have hsq := pow_le_pow_left₀ (frozenFront_nonneg init C ell 0 s u t ω) hw.2 2
    have hnum :
        ((goodPairs (GatedTick (ell + 1)) (virtualLabels init ω (u + t))).card : ℝ) ≤
          ((StageEventSpec.bulkThreshold C.card : ℝ) + lowerTicks init C u t ω) ^ 2 +
            2 * C.card * frozenFront init C (ell + 1) 0 s u t ω := by
      linarith only [hp, hsq]
    have hratio := div_le_div_of_nonneg_right hnum hden.le
    have he :
        (((StageEventSpec.bulkThreshold C.card : ℝ) + lowerTicks init C u t ω) ^ 2 +
          2 * C.card * frozenFront init C (ell + 1) 0 s u t ω) /
            ((init.card : ℝ) * ((init.card : ℝ) - 1)) =
          clockMaskRate init.card C.card *
            lowerRate C.card (lowerTicks init C u t ω)
              (frozenFront init C (ell + 1) 0 s u t ω) := by
      rw [clockMaskRate_eq_real _ _ (by omega)]
      unfold lowerRate lowerSource
      have hcpos : (C.card : ℝ) ≠ 0 := by linarith
      have hcm : (C.card : ℝ) - 1 ≠ 0 := by linarith
      have hmpos : (init.card : ℝ) ≠ 0 := by linarith
      have hmminus : (init.card : ℝ) - 1 ≠ 0 := by linarith
      field_simp [hcpos, hcm, hmpos, hmminus]
      <;> ring
    rw [he] at hratio
    have hmem : ω ∈ A := hs
    rw [hi, Set.indicator_of_mem hmem] at hm
    have hg' :
        (law init)[gatedIndicator init (ell + 1) (u + t) | ℱ t] ω =
          ((goodPairs (GatedTick (ell + 1)) (virtualLabels init ω (u + t))).card : ℝ) /
            ((init.card : ℝ) * ((init.card : ℝ) - 1)) := hg
    rw [hg'] at hm
    exact hm.trans hratio
  · have hmem : ω ∉ A := hs
    rw [hi, Set.indicator_of_notMem hmem] at hm
    exact hm.trans (mul_nonneg hq (lowerRate_bounds C.card _ hC hw.1.le _
      (frozenFront_nonneg init C (ell + 1) 0 s u t ω)
      (frozenFront_upper init C (ell + 1) s u hsu (by omega) t ω)).1)

def actualLowerData (init : InputCfg n) (hc : 2 ≤ init.card)
    (C : Finset (Fin init.card)) (hC : 1000000 ≤ C.card)
    (ell s u : ℕ) (hsu : s ≤ u) (hell : 1 ≤ ell)
    (htop : ell + 1 ≤ PhaseThreeModel.Numeric.clockCap n) :
    LowerPassageData (law init) (shiftedFiltration (pairLogFiltration _ _) u) C.card where
  large := hC
  Y := frozenFront init C (ell + 1) 0 s u
  N := lowerTicks init C u
  J := fun t => maskTickIndicator init C (u + t)
  stop := lowerStop init C ell s u
  adapted_front := frozenFront_adapted init C (ell + 1) 0 s u hsu
  adapted_count := lowerTicks_measurable init C u
  adapted_tick := fun t => by
    simpa only [shiftedFiltration_apply, Nat.add_assoc] using
      maskTickIndicator_stronglyMeasurable init C (u + t)
  stopping := lowerStop_isStoppingTime init C ell s u hsu
  front_nonneg := frozenFront_nonneg init C (ell + 1) 0 s u
  front_upper := frozenFront_upper init C (ell + 1) s u hsu (by omega)
  front_increment := frozenFront_delta_cases init C (ell + 1) 0 s u hsu (by omega) htop
  tick_zero_one := fun t => maskTickIndicator_zero_one init C (u + t)
  increment_le_tick := frozenFront_increment_le_mask init C (ell + 1) s u hsu (by omega) htop
  count_zero := lowerTicks_zero init C u
  count_step := lowerTicks_step init C u
  region := fun t ω ht => (lowerWindow_of_lt_stop init C ell s u t ω ht).1
  rate := lower_frozen_conditional_rate init hc C hC ell s u hsu hell htop

def LowerLaunch (init : InputCfg n) (C : Finset (Fin init.card))
    (ell u : ℕ) (ω : InputLog n) : Prop :=
  frontCount (virtualLabels init ω u) ell ≤ StageEventSpec.bulkThreshold C.card ∧
    (frontCount (virtualLabels init ω u) (ell + 1) : ℝ) ≤
      (StageEventSpec.bulkThreshold C.card : ℝ) ^ 2 / (C.card : ℝ)

def lowerClockFailure (init : InputCfg n) (C : Finset (Fin init.card))
    (ell s u : ℕ) : Set (InputLog n) :=
  {ω | ∃ t, shapeSafeAt init C s (u + t) ω ∧
    StageEventSpec.bulkThreshold C.card ≤ frontCount (virtualLabels init ω (u + t)) (ell + 1) ∧
      (lowerTicks init C u t ω : ℝ) < (2 / 5 : ℝ) * C.card}

theorem lower_clock_prefix_tail (init : InputCfg n) (hc : 2 ≤ init.card)
    (C : Finset (Fin init.card)) (hC : 1000000 ≤ C.card)
    (ell s u : ℕ) (hsu : s ≤ u) (hell : 1 ≤ ell)
    (htop : ell + 1 ≤ PhaseThreeModel.Numeric.clockCap n)
    (E : Set (InputLog n)) (hE : MeasurableSet[pairLogFiltration _ _ u] E)
    (hstart : ∀ ω ∈ E, LowerLaunch init C ell u ω) :
    law init (E ∩ lowerClockFailure init C ell s u) ≤
      ENNReal.ofReal (Real.exp (-(C.card : ℝ) / 1000000)) * law init E := by
  let d := actualLowerData init hc C hC ell s u hsu hell htop
  have hinitial : ∀ ω ∈ E,
      d.Y 0 ω ≤ (StageEventSpec.bulkThreshold C.card : ℝ) ^ 2 / (C.card : ℝ) :=
    fun ω he => (frozenFront_initial_le init C (ell + 1) s u ω).trans (hstart ω he).2
  apply (measure_mono ?_).trans
    (lower_crossing_prefix_tail d E
      (by simpa only [shiftedFiltration_apply, Nat.add_zero] using hE) hinitial)
  rintro ω ⟨he, t, hs, hhit, hbudget⟩
  have hNlt : lowerTicks init C u t ω < lowerHorizon C.card := by
    have h := hbudget.trans_le (lowerHorizon_bounds C.card hC).1
    exact_mod_cast h
  have hXzero : frozenFront init C ell 0 s u 0 ω ≤ (StageEventSpec.bulkThreshold C.card : ℝ) :=
    (frozenFront_initial_le init C ell s u ω).trans (by exact_mod_cast (hstart ω he).1)
  have hstop : (t : WithTop ℕ) < lowerStop init C ell s u ω := by
    apply lt_of_not_ge
    intro hbad
    obtain ⟨v, hvt, hfail⟩ := (lowerStop_le_iff init C ell s u t ω).mp hbad
    apply hfail
    have hvm : lowerTicks init C u v ω ≤ lowerTicks init C u t ω := by
      have h := maskTickCount_mono init C u v t hvt ω
      rw [← lowerTicks_real, ← lowerTicks_real] at h
      exact_mod_cast h
    refine ⟨hvm.trans_lt hNlt, ?_⟩
    have hp := frozenFront_progress init C ell s u hsu hell (by omega) v ω
    linarith only [hp, hXzero]
  refine ⟨he, t, hstop.le, hNlt.le, ?_⟩
  change (StageEventSpec.bulkThreshold C.card : ℝ) ≤
    frozenFront init C (ell + 1) 0 s u t ω
  simp only [frozenFront, frozenShapeCounts_eq_raw init C (ell + 1) 0 s u t ω hs,
    rawShapeCounts]
  exact_mod_cast hhit

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockLowerPassageProcess

end
