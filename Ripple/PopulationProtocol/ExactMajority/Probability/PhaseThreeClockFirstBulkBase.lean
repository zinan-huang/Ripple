-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockFirstBulkBase.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockBulkClockPassage
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockActivationRoleFloors
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockMacroscopicActivation
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockMarkCoverage

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal BigOperators

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockFirstBulkBase

open TimeTheorem PairLog PairLogAuxiliary PhaseThreeScalar
  PhaseThreeClockVirtual PhaseThreeClockGatedLaw PhaseThreeClockGatedLevelOne
  PhaseThreeClockProbabilityFloors PhaseThreeClockPrefixTails
  PhaseThreeClockStoppedPassage PhaseThreeClockShapeFreeze
  PhaseThreeClockShapeBarrier PhaseThreeClockBulkClockPassage
  PhaseThreeClockThinning PhaseThreeClockActivationLaw
  PhaseThreeClockActivationRoleFloors PhaseThreeClockCoreCounts
  PhaseThreeClockMacroscopicActivation PhaseThreeClockSeedTails
  PhaseThreeClockActivationSeed PhaseThreeClockSharpActivationSeed
  PhaseThreeClockRareDripCharging PhaseThreeClockMarkCoverage
open PhaseThreeModel.Numeric

variable {L K m n : ℕ}

theorem inactiveCount_le_dormant (f : Fin m → AgentState L K) :
    inactiveCount f ≤ m - PhaseThreeClockActivationLaw.activeCount f := by
  have hsub : inactiveSet f ⊆ dormantSet f := by
    intro i hi
    have hp := (Finset.mem_filter.mp hi).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
  have h := Finset.card_le_card hsub
  simpa only [inactiveCount, dormantSet_card] using h

theorem inactive_floor_of_macro (init : InputCfg n)
    (C : Finset (Fin init.card)) (s v : ℕ) (ω : InputLog n)
    (hsafe : shapeSafeAt init C s v ω)
    (hmacro : macroscopicThreshold init.card ≤
      PhaseThreeClockActivationLaw.activeCount (virtualLabels init ω v)) :
    4 * inactiveCount (virtualLabels init ω v) ≤ C.card := by
  have hI := inactiveCount_le_dormant (virtualLabels init ω v)
  have hA := inactive_one_percent init (virtualLabels init ω v)
    (by simpa only [macroscopicThreshold, activeCountL_eq_activeCount] using hmacro)
  rw [activeCountL_eq_activeCount] at hA
  have hden := clock_density_at_seedPrefix init ω s hsafe.1.1
  have hcount : clockCount (labelsAt init ω s) = C.card := by
    change (clockSet (labelsAt init ω s)).card = C.card
    rw [hsafe.1.2]
  rw [hcount] at hden
  omega

def firstBulkWindow (init : InputCfg n) (C : Finset (Fin init.card))
    (s u t : ℕ) (ω : InputLog n) : Prop :=
  shapeSafeAt init C s (u + t) ω ∧
    4 * inactiveCount (virtualLabels init ω (u + t)) ≤ C.card ∧
    frontCount (virtualLabels init ω (u + t)) 1 < StageEventSpec.bulkThreshold C.card

open Classical in
def firstBulkStop (init : InputCfg n) (C : Finset (Fin init.card))
    (s u : ℕ) (ω : InputLog n) : WithTop ℕ :=
  if h : ∃ t, ¬ firstBulkWindow init C s u t ω
  then ((Nat.find h : ℕ) : WithTop ℕ) else ⊤

theorem firstBulkStop_le_iff (init : InputCfg n) (C : Finset (Fin init.card))
    (s u N : ℕ) (ω : InputLog n) :
    firstBulkStop init C s u ω ≤ (N : WithTop ℕ) ↔
      ∃ t ≤ N, ¬ firstBulkWindow init C s u t ω := by
  classical
  unfold firstBulkStop
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

theorem firstBulkWindow_of_lt_stop (init : InputCfg n)
    (C : Finset (Fin init.card)) (s u N : ℕ) (ω : InputLog n)
    (hN : (N : WithTop ℕ) < firstBulkStop init C s u ω) :
    ∀ t ≤ N, firstBulkWindow init C s u t ω := by
  intro t ht
  by_contra hbad
  exact (not_lt_of_ge ((firstBulkStop_le_iff init C s u N ω).2 ⟨t, ht, hbad⟩)) hN

theorem firstBulkWindow_measurable (init : InputCfg n)
    (C : Finset (Fin init.card)) (s u : ℕ) (hsu : s ≤ u) (t : ℕ) :
    MeasurableSet[shiftedFiltration (pairLogFiltration _ _) u t]
      {ω | firstBulkWindow init C s u t ω} := by
  have hstate : MeasurableSet[pairLogFiltration _ _ (u + t)]
      {ω | 4 * inactiveCount (virtualLabels init ω (u + t)) ≤ C.card ∧
        frontCount (virtualLabels init ω (u + t)) 1 <
          StageEventSpec.bulkThreshold C.card} :=
    (show MeasurableSet {f : Fin init.card →
      AgentState (hourIndex n) 256 |
        4 * inactiveCount f ≤ C.card ∧
        frontCount f 1 < StageEventSpec.bulkThreshold C.card} from
      (Set.to_countable _).measurableSet).preimage (measurable_virtualLabels init (u + t))
  exact (shapeSafeAt_measurable init C s (u + t) (by omega)).inter hstate

theorem firstBulkStop_isStoppingTime (init : InputCfg n)
    (C : Finset (Fin init.card)) (s u : ℕ) (hsu : s ≤ u) :
    IsStoppingTime (shiftedFiltration (pairLogFiltration _ _) u)
      (firstBulkStop init C s u) := by
  intro N
  have hm : MeasurableSet[shiftedFiltration (pairLogFiltration _ _) u N]
      (⋃ t : ℕ, {ω | t ≤ N ∧ ¬ firstBulkWindow init C s u t ω}) := by
    refine MeasurableSet.iUnion fun t => ?_
    by_cases ht : t ≤ N
    · have hbad := ((shiftedFiltration (pairLogFiltration _ _) u).mono ht) _
        (firstBulkWindow_measurable init C s u hsu t).compl
      simpa only [ht, true_and] using hbad
    · simp only [ht, false_and, Set.setOf_false, MeasurableSet.empty]
  convert hm using 1
  ext ω
  simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
  exact firstBulkStop_le_iff init C s u N ω

theorem first_bulk_raw_floor (init : InputCfg n) (hc : 2 ≤ init.card)
    (C : Finset (Fin init.card)) (hC : 100 ≤ C.card)
    (f : Fin init.card → AgentState (hourIndex n) 256)
    (hcount : clockCount f = C.card)
    (hI : 4 * inactiveCount f ≤ C.card)
    (hbelow : frontCount f 1 < StageEventSpec.bulkThreshold C.card) :
    clockMaskRate init.card C.card / 2 ≤
      ((goodPairs (GatedTick 1) f).card : ℝ) /
        ((init.card : ℝ) * ((init.card : ℝ) - 1)) := by
  have hCR : (100 : ℝ) ≤ C.card := by exact_mod_cast hC
  have hb : (StageEventSpec.bulkThreshold C.card : ℝ) ≤ (C.card : ℝ) / 10 + 1 :=
    (Nat.ceil_lt_add_one (by positivity : 0 ≤ (C.card : ℝ) / 10)).le
  have hbelowR : (frontCount f 1 : ℝ) ≤ StageEventSpec.bulkThreshold C.card := by
    exact_mod_cast hbelow.le
  have hX : 4 * frontCount f 1 ≤ clockCount f := by
    rw [hcount]
    have hr : 4 * (frontCount f 1 : ℝ) ≤ C.card := by linarith
    exact_mod_cast hr
  have hpair := half_clock_pairs_le_gated_one f
    (by rw [hcount]; omega) hX (by simpa only [hcount] using hI)
  rw [hcount] at hpair
  have hcR : (2 : ℝ) ≤ init.card := by exact_mod_cast hc
  have hden : 0 ≤ (init.card : ℝ) * ((init.card : ℝ) - 1) :=
    mul_nonneg (by linarith) (by linarith)
  have hhalf : (C.card : ℝ) * ((C.card : ℝ) - 1) / 2 ≤
      ((goodPairs (GatedTick 1) f).card : ℝ) := by linarith
  have h := div_le_div_of_nonneg_right hhalf hden
  rw [clockMaskRate_eq_real _ _ (by omega)]
  convert h using 1 <;> ring

theorem first_bulk_survival_count (init : InputCfg n)
    (C : Finset (Fin init.card)) (s u N : ℕ) (hsu : s ≤ u)
    (ω : InputLog n) (hN : (N : WithTop ℕ) < firstBulkStop init C s u ω) :
    bernoulliCount (fun t => gatedIndicator init 1 (u + t)) N ω <
      (StageEventSpec.bulkThreshold C.card : ℝ) := by
  have hw := firstBulkWindow_of_lt_stop init C s u N ω hN
  have htel : ∀ r, r ≤ N →
      (frontCount (virtualLabels init ω (u + r)) 1 : ℝ) =
        (frontCount (virtualLabels init ω u) 1 : ℝ) +
          bernoulliCount (fun t => gatedIndicator init 1 (u + t)) r ω := by
    intro r
    induction r with
    | zero =>
        intro hr
        simp [bernoulliCount]
    | succ r ih =>
        intro hr
        have hp := ih (by omega)
        have hs := front_step_safe init C 1 0 s (u + r) (by omega) le_rfl
          (by omega) ω (by simpa only [Nat.add_assoc] using (hw (r + 1) hr).1)
        simpa only [Nat.add_assoc, bernoulliCount, Finset.sum_range_succ, add_assoc] using
          hs.trans (congrArg (fun z : ℝ => z + gatedIndicator init 1 (u + r) ω) hp)
  have hbelow : (frontCount (virtualLabels init ω (u + N)) 1 : ℝ) <
      (StageEventSpec.bulkThreshold C.card : ℝ) := by exact_mod_cast (hw N le_rfl).2.2
  have hz : 0 ≤ (frontCount (virtualLabels init ω u) 1 : ℝ) := by positivity
  linarith [htel N le_rfl]

def firstBulkRawHorizon (init : InputCfg n) (C : Finset (Fin init.card)) : ℕ :=
  Nat.ceil ((C.card : ℝ) / (2 * clockMaskRate init.card C.card))

theorem firstBulkRawHorizon_bounds (init : InputCfg n) (hc : 2 ≤ init.card)
    (C : Finset (Fin init.card)) (hC : 100 ≤ C.card) :
    (C.card : ℝ) / 2 ≤ clockMaskRate init.card C.card * (firstBulkRawHorizon init C : ℝ) ∧
    clockMaskRate init.card C.card * (firstBulkRawHorizon init C : ℝ) ≤
      (3 / 4 : ℝ) * C.card := by
  have hq := mask_rate_bounds init hc C (by omega)
  have hCR : (100 : ℝ) ≤ C.card := by exact_mod_cast hC
  have hl := Nat.le_ceil ((C.card : ℝ) / (2 * clockMaskRate init.card C.card))
  have hu := Nat.ceil_lt_add_one
    (show 0 ≤ (C.card : ℝ) / (2 * clockMaskRate init.card C.card) from
      div_nonneg (Nat.cast_nonneg _) (mul_nonneg (by norm_num) hq.1.le))
  have he : clockMaskRate init.card C.card *
      ((C.card : ℝ) / (2 * clockMaskRate init.card C.card)) = (C.card : ℝ) / 2 := by
    field_simp [hq.1.ne']
    <;> ring
  have hlow := mul_le_mul_of_nonneg_left hl hq.1.le
  have hupper := mul_le_mul_of_nonneg_left hu.le hq.1.le
  dsimp only [firstBulkRawHorizon]
  rw [he] at hlow
  rw [mul_add, he, mul_one] at hupper
  exact ⟨hlow, by linarith⟩

theorem first_bulk_raw_prefix_tail (init : InputCfg n) (hc : 2 ≤ init.card)
    (C : Finset (Fin init.card)) (hC : 100 ≤ C.card)
    (s u : ℕ) (hsu : s ≤ u)
    (E : Set (InputLog n)) (hE : MeasurableSet[pairLogFiltration _ _ u] E) :
    law init (E ∩ {ω |
      (firstBulkRawHorizon init C : WithTop ℕ) < firstBulkStop init C s u ω}) ≤
      ENNReal.ofReal (Real.exp (-(C.card : ℝ) / 25)) * law init E := by
  let ℱ := shiftedFiltration (pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256) u
  let I : ℕ → InputLog n → ℝ := fun t => gatedIndicator init 1 (u + t)
  let p : ℝ := clockMaskRate init.card C.card / 2
  have hq := mask_rate_bounds init hc C (by omega)
  have hI : ∀ t, StronglyMeasurable[ℱ (t + 1)] (I t) := by
    intro t
    simpa only [ℱ, I, shiftedFiltration_apply, Nat.add_assoc] using
      gatedIndicator_adapted init 1 (u + t)
  have hz : ∀ t, ∀ᵐ ω ∂law init, I t ω = 0 ∨ I t ω = 1 :=
    fun t => ae_of_all _ (gatedIndicator_zero_one init 1 (u + t))
  have hp : p ≤ 1 := by dsimp only [p]; linarith [hq.2]
  have hcond : ∀ t : ℕ, ∀ᵐ ω ∂law init,
      (t : WithTop ℕ) < firstBulkStop init C s u ω →
        p ≤ (law init)[I t | ℱ t] ω := by
    intro t
    filter_upwards [gatedIndicator_law init hc 1 (u + t)] with ω hlaw
    intro ht
    have hw := firstBulkWindow_of_lt_stop init C s u t ω ht t le_rfl
    have hg := shapeSafeAt_guard init C 1 0 s (u + t) (by omega) le_rfl ω hw.1
    have hcount : clockCount (virtualLabels init ω (u + t)) = C.card := by
      change (clockSet (virtualLabels init ω (u + t))).card = C.card
      rw [← hg.2.1]
    change p ≤ (law init)[gatedIndicator init 1 (u + t) |
      pairLogFiltration _ _ (u + t)] ω
    rw [hlaw]
    exact first_bulk_raw_floor init hc C hC _ hcount hw.2.1 hw.2.2
  have ht := prefix_success_hitting_tail hI hz
    (firstBulkStop_isStoppingTime init C s u hsu) hp hcond E
    (by simpa only [ℱ, shiftedFiltration_apply, Nat.add_zero] using hE)
    (firstBulkRawHorizon init C) (StageEventSpec.bulkThreshold C.card : ℝ)
    (fun ω _ hsur => first_bulk_survival_count init C s u _ hsu ω hsur)
  have hCR : (100 : ℝ) ≤ C.card := by exact_mod_cast hC
  have hb : (StageEventSpec.bulkThreshold C.card : ℝ) ≤ (C.card : ℝ) / 10 + 1 :=
    (Nat.ceil_lt_add_one (by positivity : 0 ≤ (C.card : ℝ) / 10)).le
  have hl : Real.log 2 ≤ (3 / 4 : ℝ) := log_two_bounds.2.trans (by norm_num)
  have hprod := mul_le_mul_of_nonneg_right hl
    (show (0 : ℝ) ≤ StageEventSpec.bulkThreshold C.card by positivity)
  have hN := (firstBulkRawHorizon_bounds init hc C hC).1
  have hexp : (StageEventSpec.bulkThreshold C.card : ℝ) * Real.log 2 -
      p * (firstBulkRawHorizon init C : ℝ) / 2 ≤ -(C.card : ℝ) / 25 := by
    dsimp only [p]
    nlinarith only [hprod, hb, hN, hCR]
  exact measure_le_of_real_weighted_bound (law init) _ E _ (Real.exp_nonneg _)
    (ht.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hexp)
      ENNReal.toReal_nonneg))

theorem first_bulk_endpoint_survival (init : InputCfg n)
    (C : Finset (Fin init.card)) (s u N : ℕ) (hsu : s ≤ u)
    (ω : InputLog n) (hsafe : shapeSafeAt init C s (u + N) ω)
    (hmacro : macroscopicThreshold init.card ≤ PhaseThreeClockActivationLaw.activeCount (virtualLabels init ω u))
    (hbelow : frontCount (virtualLabels init ω (u + N)) 1 <
      StageEventSpec.bulkThreshold C.card) :
    (N : WithTop ℕ) < firstBulkStop init C s u ω := by
  apply lt_of_not_ge
  intro hs
  obtain ⟨t, ht, hbad⟩ := (firstBulkStop_le_iff init C s u N ω).mp hs
  have hsafet := shapeSafeAt_anti init C s (u + t) (u + N) (by omega) ω hsafe
  apply hbad
  refine ⟨hsafet, ?_, ?_⟩
  · exact inactive_floor_of_macro init C s (u + t) ω hsafet
      (hmacro.trans (activeCount_virtualLabels_mono init ω (by omega)))
  · exact (frontCount_mono_safe init C s (u + t) (u + N) 1
      (by omega) (by omega) le_rfl (by omega) ω hsafe).trans_lt hbelow

def firstBulkClockFailure (init : InputCfg n) (C : Finset (Fin init.card))
    (s u : ℕ) : Set (InputLog n) :=
  ⋃ N : ℕ, {ω | shapeSafeAt init C s (u + N) ω ∧
    frontCount (virtualLabels init ω (u + N)) 1 < StageEventSpec.bulkThreshold C.card ∧
    (C.card : ℝ) ≤ maskTickCount init C u N ω}

theorem first_bulk_clock_prefix_tail (init : InputCfg n) (hc : 2 ≤ init.card)
    (C : Finset (Fin init.card)) (hC : 100 ≤ C.card)
    (s u : ℕ) (hsu : s ≤ u)
    (E : Set (InputLog n)) (hE : MeasurableSet[pairLogFiltration _ _ u] E)
    (hmacro : ∀ ω ∈ E,
      macroscopicThreshold init.card ≤ PhaseThreeClockActivationLaw.activeCount (virtualLabels init ω u)) :
    law init (E ∩ firstBulkClockFailure init C s u) ≤
      (2 * ENNReal.ofReal (Real.exp (-(C.card : ℝ) / 100))) * law init E := by
  let H := firstBulkRawHorizon init C
  let A : Set (InputLog n) := E ∩ {ω | (H : WithTop ℕ) < firstBulkStop init C s u ω}
  let B : Set (InputLog n) := E ∩ {ω | (C.card : ℝ) ≤ maskTickCount init C u H ω}
  have hcover : E ∩ firstBulkClockFailure init C s u ⊆ A ∪ B := by
    rintro ω ⟨he, hb⟩
    obtain ⟨N, hsafe, hbelow, htick⟩ := Set.mem_iUnion.mp hb
    by_cases hHN : H ≤ N
    · left
      exact ⟨he, (show (H : WithTop ℕ) ≤ (N : WithTop ℕ) by exact_mod_cast hHN).trans_lt
        (first_bulk_endpoint_survival init C s u N hsu ω hsafe (hmacro ω he) hbelow)⟩
    · exact Or.inr ⟨he, htick.trans (maskTickCount_mono init C u N H (by omega) ω)⟩
  have ha := first_bulk_raw_prefix_tail init hc C hC s u hsu E hE
  have hb := prefix_maskTick_upper_tail init hc C u H E hE (C.card : ℝ)
    (by positivity) (by
      have hm := (firstBulkRawHorizon_bounds init hc C hC).2
      dsimp only [H]
      linarith)
  have hbE : law init B ≤
      ENNReal.ofReal (Real.exp (-(C.card : ℝ) / 36)) * law init E :=
    measure_le_of_real_weighted_bound (law init) B E _ (Real.exp_nonneg _) hb
  have ha' : law init A ≤
      ENNReal.ofReal (Real.exp (-(C.card : ℝ) / 100)) * law init E :=
    ha.trans (mul_le_mul_right' (ENNReal.ofReal_le_ofReal
      (Real.exp_le_exp.mpr (by
        have : (0 : ℝ) ≤ C.card := Nat.cast_nonneg _
        linarith))) _)
  have hb' : law init B ≤
      ENNReal.ofReal (Real.exp (-(C.card : ℝ) / 100)) * law init E :=
    hbE.trans (mul_le_mul_right' (ENNReal.ofReal_le_ofReal
      (Real.exp_le_exp.mpr (by
        have : (0 : ℝ) ≤ C.card := Nat.cast_nonneg _
        linarith))) _)
  calc
    law init (E ∩ firstBulkClockFailure init C s u) ≤ law init (A ∪ B) := measure_mono hcover
    _ ≤ law init A + law init B := measure_union_le _ _
    _ ≤ _ := add_le_add ha' hb'
    _ = _ := by ring

theorem first_bulk_first_hit_contacts_le (init : InputCfg n)
    (C : Finset (Fin init.card)) (s u tau : ℕ) (ω : InputLog n)
    (hsafe : shapeSafeAt init C s tau ω)
    (hfirst : StageEventSpec.firstAfter
      (fun v => StageEventSpec.bulkThreshold C.card ≤
        frontCount (virtualLabels init ω v) 1) s tau)
    (hsu : s ≤ u) (hgood : ω ∉ firstBulkClockFailure init C s u) :
    maskContacts init C u tau ω ≤ C.card := by
  by_cases hut : u ≤ tau
  · apply contacts_le_budget_of_predecessors init C u tau C.card hut ω
    intro N hN
    apply lt_of_not_ge
    intro htick
    apply hgood
    exact Set.mem_iUnion.mpr ⟨N,
      shapeSafeAt_anti init C s (u + N) tau hN.le ω hsafe,
      lt_of_not_ge (hfirst.2.2 (u + N) (by omega) hN), htick⟩
  · classical
    have hz : maskContacts init C u tau ω = 0 := by
      apply Finset.card_eq_zero.mpr
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro t ht
      have htu := Finset.mem_Ioc.mp (Finset.mem_filter.mp ht).1
      omega
    rw [hz]
    exact Nat.zero_le _

theorem first_bulk_error_calibration {C : ℕ}
    (hC : 0 < (C : ℝ)) (hx : 536870912 ≤ Real.log (C : ℝ)) :
    2 * ENNReal.ofReal (Real.exp (-(C : ℝ) / 100)) ≤
      ENNReal.ofReal (1 / (C : ℝ) ^ 100) := by
  have hsize := Real.add_one_le_exp (Real.log (C : ℝ))
  rw [Real.exp_log hC] at hsize
  have htwo : (2 : ℝ) ≤ C := by linarith
  have hcal := (elementary_power_calibration hC hx).2.2.2.2.1
  rw [Real.exp_log hC] at hcal
  have hexp : -(C : ℝ) / 100 ≤ -101 * Real.log (C : ℝ) := by
    have : 0 ≤ Real.log (C : ℝ) := by linarith
    linarith
  have hreal : 2 * Real.exp (-(C : ℝ) / 100) ≤ (C : ℝ) ^ (-100 : ℝ) := by
    calc
      _ ≤ (C : ℝ) * Real.exp (-101 * Real.log (C : ℝ)) :=
        mul_le_mul htwo (Real.exp_le_exp.mpr hexp) (Real.exp_nonneg _)
          (Nat.cast_nonneg C)
      _ = Real.exp (Real.log (C : ℝ) + (-101 * Real.log (C : ℝ))) := by
        rw [Real.exp_add, Real.exp_log hC]
      _ = _ := by
        rw [Real.rpow_def_of_pos hC]
        congr 1
        ring
  have heq : (C : ℝ) ^ (-100 : ℝ) = 1 / (C : ℝ) ^ 100 :=
    PhaseThreeClockEarlyMarkCalibration.negative_hundred_rpow_eq C
  rw [heq] at hreal
  calc
    _ = ENNReal.ofReal (2 * Real.exp (-(C : ℝ) / 100)) := by
      rw [ENNReal.ofReal_mul (by norm_num)]
      norm_num
    _ ≤ _ := ENNReal.ofReal_le_ofReal hreal

def activationBulkFailure (init : InputCfg n) (C : Finset (Fin init.card))
    (s : ℕ) : Set (InputLog n) :=
  ⋃ u : ℕ, {ω | macroscopicTime init s ω = (u : WithTop ℕ)} ∩
    firstBulkClockFailure init C s u

theorem activation_bulk_prefix_tail (init : InputCfg n)
    (hn : populationThreshold ≤ n) (C : Finset (Fin init.card)) (s : ℕ)
    (E : Set (InputLog n)) (hE : MeasurableSet[pairLogFiltration _ _ s] E)
    (hseed : ∀ ω ∈ E, ω ∈ seedPrefix init s ∧ C = clockSet (labelsAt init ω s)) :
    law init (E ∩ activationBulkFailure init C s) ≤
      ENNReal.ofReal (1 / (C.card : ℝ) ^ 100) * law init E := by
  by_cases he : E = ∅
  · simp only [he, Set.empty_inter, measure_empty, mul_zero, le_refl]
  · obtain ⟨η, hη⟩ := Set.nonempty_iff_ne_empty.mpr he
    have hcount : clockCount (labelsAt init η s) = C.card := by
      change (clockSet (labelsAt init η s)).card = C.card
      rw [← (hseed η hη).2]
    obtain ⟨hm, hlo, hCm⟩ :=
      seed_clock_calibration_inputs init hn η s C.card (hseed η hη).1 hcount
    obtain ⟨hC, hx, -⟩ := logarithmic_inputs hm hlo hCm
    have hsize := Real.add_one_le_exp (Real.log (C.card : ℝ))
    rw [Real.exp_log hC] at hsize
    have hCbig : 100 ≤ C.card := by
      have : (100 : ℝ) ≤ C.card := by linarith
      exact_mod_cast this
    have hc : 2 ≤ init.card := by omega
    let A : ℕ → Set (InputLog n) := fun u =>
      E ∩ {ω | macroscopicTime init s ω = (u : WithTop ℕ)}
    have hA (u : ℕ) : MeasurableSet[pairLogFiltration _ _ u] (A u) := by
      by_cases hsu : s ≤ u
      · exact (((pairLogFiltration _ _).mono hsu) _ hE).inter
          (macroscopicTime_pastTime init s u)
      · have hz : A u = ∅ := by
          apply Set.eq_empty_iff_forall_notMem.mpr
          intro ω hω
          exact hsu (macroscopicTime_finite_state init s u ω hω.2).1
        rw [hz]
        exact MeasurableSpace.measurableSet_empty _
    have hdisj : Pairwise (fun u v => Disjoint (A u) (A v)) := by
      intro u v huv
      apply Set.disjoint_left.mpr
      intro ω hu hv
      exact huv (WithTop.coe_injective (hu.2.symm.trans hv.2))
    have hmass : (∑' u, law init (A u)) ≤ law init E := by
      rw [← measure_iUnion hdisj (fun u => (pairLogFiltration _ _).le u _ (hA u))]
      apply measure_mono
      intro ω hω
      obtain ⟨u, hu⟩ := Set.mem_iUnion.mp hω
      exact hu.1
    have hlocal (u : ℕ) :
        law init (A u ∩ firstBulkClockFailure init C s u) ≤
          ENNReal.ofReal (1 / (C.card : ℝ) ^ 100) * law init (A u) := by
      by_cases hsu : s ≤ u
      · exact (first_bulk_clock_prefix_tail init hc C hCbig s u hsu (A u) (hA u)
          (fun ω hω => (macroscopicTime_finite_state init s u ω hω.2).2)).trans
            (mul_le_mul_right' (first_bulk_error_calibration hC hx) _)
      · have hz : A u = ∅ := by
          apply Set.eq_empty_iff_forall_notMem.mpr
          intro ω hω
          exact hsu (macroscopicTime_finite_state init s u ω hω.2).1
        simp only [hz, Set.empty_inter, measure_empty, mul_zero, le_refl]
    have hcover : E ∩ activationBulkFailure init C s ⊆
        ⋃ u : ℕ, A u ∩ firstBulkClockFailure init C s u := by
      rintro ω ⟨heω, hb⟩
      obtain ⟨u, hu, hf⟩ := Set.mem_iUnion.mp hb
      exact Set.mem_iUnion.mpr ⟨u, ⟨heω, hu⟩, hf⟩
    calc
      law init (E ∩ activationBulkFailure init C s) ≤
          law init (⋃ u : ℕ, A u ∩ firstBulkClockFailure init C s u) :=
        measure_mono hcover
      _ ≤ ∑' u : ℕ, law init (A u ∩ firstBulkClockFailure init C s u) :=
        measure_iUnion_le _
      _ ≤ ∑' u : ℕ, ENNReal.ofReal (1 / (C.card : ℝ) ^ 100) * law init (A u) :=
        ENNReal.tsum_le_tsum hlocal
      _ = ENNReal.ofReal (1 / (C.card : ℝ) ^ 100) * ∑' u : ℕ, law init (A u) := by
        rw [ENNReal.tsum_mul_left]
      _ ≤ _ := mul_le_mul_left' hmass _

theorem activation_bulk_contacts_le (init : InputCfg n)
    (C : Finset (Fin init.card)) (s alpha tau : ℕ) (ω : InputLog n)
    (ha : macroscopicTime init s ω = (alpha : WithTop ℕ))
    (hsafe : shapeSafeAt init C s tau ω)
    (hfirst : StageEventSpec.firstAfter
      (fun v => StageEventSpec.bulkThreshold C.card ≤
        frontCount (virtualLabels init ω v) 1) s tau)
    (hgood : ω ∉ activationBulkFailure init C s) :
    maskContacts init C alpha tau ω ≤ C.card := by
  apply first_bulk_first_hit_contacts_le init C s alpha tau ω hsafe hfirst
    (macroscopicTime_finite_state init s alpha ω ha).1
  intro hb
  exact hgood (Set.mem_iUnion.mpr ⟨alpha, ha, hb⟩)

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockFirstBulkBase

end
