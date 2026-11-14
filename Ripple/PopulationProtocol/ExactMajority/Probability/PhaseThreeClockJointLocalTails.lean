-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockJointLocalTails.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockJointCore
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockFirstBulkBase
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockBulkShapeBudget
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockFirstAfterFibres

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockJointLocalTails

open TimeTheorem PairLog StageEventSpec PhaseThreeModel.Numeric
  PhaseThreeClockVirtual PhaseThreeClockGatedLaw PhaseThreeClockSeedTails
  PhaseThreeClockActivationSeed PhaseThreeClockSharpActivationSeed
  PhaseThreeClockEarlyMarkSeedTail PhaseThreeClockMarkedShape
  PhaseThreeClockShapeSeedFibre PhaseThreeClockShapeFreeze
  PhaseThreeClockFirstBulkBase PhaseThreeClockBulkClockPassage
  PhaseThreeClockFirstAfterFibres PhaseThreeClockRareChainFibres
  PhaseThreeClockBulkFamily PhaseThreeClockObservedStarts
  PhaseThreeClockBulkShapeBudget PhaseThreeClockThinning

variable {n : ℕ}

theorem mask_error_population_prefix (init : InputCfg n)
    (hn : populationThreshold ≤ n) (s : ℕ)
    (E : Set (InputLog n)) (hE : MeasurableSet[pairLogFiltration _ _ s] E)
    (hseed : E ⊆ seedPrefix init s)
    (B : Finset (Fin init.card) → Set (InputLog n))
    (hlocal : ∀ C,
      law init ((E ∩ {ω | C = clockSet (labelsAt init ω s)}) ∩ B C) ≤
        ENNReal.ofReal (1 / (C.card : ℝ) ^ 100) *
          law init (E ∩ {ω | C = clockSet (labelsAt init ω s)})) :
    law init (E ∩ {ω | ω ∈ B (clockSet (labelsAt init ω s))}) ≤
      ENNReal.ofReal (1 / (n : ℝ) ^ 99) * law init E := by
  apply seed_mask_prefix_union init s E hE B
  intro C
  let A := E ∩ {ω | C = clockSet (labelsAt init ω s)}
  by_cases ha : A = ∅
  · change law init (A ∩ B C) ≤ _ * law init A
    simp only [ha, Set.empty_inter, measure_empty, mul_zero, le_refl]
  · obtain ⟨ω, hω⟩ := Set.nonempty_iff_ne_empty.mpr ha
    exact (hlocal C).trans (mul_le_mul_right' (ENNReal.ofReal_le_ofReal
      (seed_clock_error_population init hn ω s C (hseed hω.1) hω.2)) _)

theorem sharp_activation_population_prefix_tail (init : InputCfg n)
    (hn : populationThreshold ≤ n) (s : ℕ)
    (E : Set (InputLog n)) (hE : MeasurableSet[pairLogFiltration _ _ s] E)
    (hseed : E ⊆ seedPrefix init s) :
    law init (E ∩ seedCountActivationFailure init s) ≤
      ENNReal.ofReal (1 / (n : ℝ) ^ 99) * law init E := by
  apply mask_error_population_prefix init hn s E hE hseed
    (fun C => sharpActivationFailure init s C.card)
  intro C
  apply seed_sharp_activation_prefix_tail init hn s C.card
    (E ∩ {ω | C = clockSet (labelsAt init ω s)})
    (hE.inter (seed_clockMask_measurable init s C))
  intro ω hω
  refine ⟨hseed hω.1, ?_⟩
  change (clockSet (labelsAt init ω s)).card = C.card
  rw [← hω.2]

def seedActivationBulkFailure (init : InputCfg n) (s : ℕ) : Set (InputLog n) :=
  {ω | ω ∈ activationBulkFailure init (clockSet (labelsAt init ω s)) s}

theorem activation_bulk_population_prefix_tail (init : InputCfg n)
    (hn : populationThreshold ≤ n) (s : ℕ)
    (E : Set (InputLog n)) (hE : MeasurableSet[pairLogFiltration _ _ s] E)
    (hseed : E ⊆ seedPrefix init s) :
    law init (E ∩ seedActivationBulkFailure init s) ≤
      ENNReal.ofReal (1 / (n : ℝ) ^ 99) * law init E := by
  apply mask_error_population_prefix init hn s E hE hseed
    (fun C => activationBulkFailure init C s)
  intro C
  exact activation_bulk_prefix_tail init hn C s
    (E ∩ {ω | C = clockSet (labelsAt init ω s)})
    (hE.inter (seed_clockMask_measurable init s C))
    (fun ω hω => ⟨hseed hω.1, hω.2⟩)

theorem coarse_error_calibration {C : ℕ}
    (hC : 0 < (C : ℝ)) (hx : 4194304 ≤ Real.log (C : ℝ)) :
    2 * ENNReal.ofReal (Real.exp (-(C : ℝ) / 1000)) ≤
      ENNReal.ofReal (1 / (C : ℝ) ^ 100) := by
  have hsize := Real.add_one_le_exp (Real.log (C : ℝ))
  rw [Real.exp_log hC] at hsize
  have htwo : (2 : ℝ) ≤ C := by linarith
  have hcal := (elementary_power_calibration hC hx).2.2.2.2.1
  rw [Real.exp_log hC] at hcal
  have hexp : -(C : ℝ) / 1000 ≤ -101 * Real.log (C : ℝ) := by
    have : 0 ≤ Real.log (C : ℝ) := by linarith
    linarith
  have hreal : 2 * Real.exp (-(C : ℝ) / 1000) ≤ (C : ℝ) ^ (-100 : ℝ) := by
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
  rw [PhaseThreeClockEarlyMarkCalibration.negative_hundred_rpow_eq] at hreal
  calc
    _ = ENNReal.ofReal (2 * Real.exp (-(C : ℝ) / 1000)) := by
      rw [ENNReal.ofReal_mul (by norm_num)]
      norm_num
    _ ≤ _ := ENNReal.ofReal_le_ofReal hreal

def coarseBulkFailure (init : InputCfg n) (C : Finset (Fin init.card))
    (ell s : ℕ) : Set (InputLog n) :=
  {ω | ∃ u, firstAfter (fun v => bulkThreshold C.card ≤
      PhaseThreeClockGatedLaw.frontCount (virtualLabels init ω v) ell) s u ∧
    ω ∈ bulkClockFailure init C (ell + 1) s u}

theorem coarse_bulk_prefix_tail (init : InputCfg n)
    (hn : populationThreshold ≤ n) (C : Finset (Fin init.card))
    (ell s : ℕ) (hell : 1 ≤ ell) (htop : ell < clockCap n)
    (E : Set (InputLog n)) (hE : MeasurableSet[pairLogFiltration _ _ s] E)
    (hseed : ∀ ω ∈ E, ω ∈ seedPrefix init s ∧ C = clockSet (labelsAt init ω s)) :
    law init (E ∩ coarseBulkFailure init C ell s) ≤
      ENNReal.ofReal (1 / (C.card : ℝ) ^ 100) * law init E := by
  by_cases he : E = ∅
  · simp only [he, Set.empty_inter, measure_empty, mul_zero, le_refl]
  · obtain ⟨η, hη⟩ := Set.nonempty_iff_ne_empty.mpr he
    have hcount : PhaseThreeClockGatedLaw.clockCount (labelsAt init η s) = C.card := by
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
    let P : ℕ → InputLog n → Prop := fun v ω =>
      bulkThreshold C.card ≤ PhaseThreeClockGatedLaw.frontCount (virtualLabels init ω v) ell
    have hP (v : ℕ) (_hv : s ≤ v) :
        MeasurableSet[pairLogFiltration _ _ v] {ω | P v ω} :=
      (show MeasurableSet {f : Fin init.card → AgentState (hourIndex n) 256 |
        bulkThreshold C.card ≤ PhaseThreeClockGatedLaw.frontCount f ell} from
          (Set.to_countable _).measurableSet).preimage (measurable_virtualLabels init v)
    apply firstAfter_prefix_union (law init) (pairLogFiltration _ _) P s E hE hP
      (fun u => bulkClockFailure init C (ell + 1) s u)
      (ENNReal.ofReal (1 / (C.card : ℝ) ^ 100))
    intro u
    let A := E ∩ {ω | firstAfter (fun v => P v ω) s u}
    by_cases hsu : s ≤ u
    · apply (bulk_next_bulk_clock_prefix_tail init (by omega) C hCbig
        (ell + 1) s u hsu (by omega)
        (by simpa only [clockCap, clockHours] using (show ell + 1 ≤ clockCap n by omega))
        A (firstAfter_prefix_measurable (pairLogFiltration _ _) P s u E hE hP)
        (by intro ω hω; simpa only [Nat.add_sub_cancel] using hω.2.2.1)).trans
      exact mul_le_mul_right' (coarse_error_calibration hC hx) _
    · have ha : A = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        rintro ω ⟨-, hf⟩
        exact hsu hf.1
      change law init (A ∩ _) ≤ _ * law init A
      simp only [ha, Set.empty_inter, measure_empty, mul_zero, le_refl]

def seedCoarseBulkFailure (init : InputCfg n) (ell s : ℕ) : Set (InputLog n) :=
  {ω | ω ∈ coarseBulkFailure init (clockSet (labelsAt init ω s)) ell s}

theorem coarse_bulk_population_prefix_tail (init : InputCfg n)
    (hn : populationThreshold ≤ n) (ell s : ℕ)
    (hell : 1 ≤ ell) (htop : ell < clockCap n)
    (E : Set (InputLog n)) (hE : MeasurableSet[pairLogFiltration _ _ s] E)
    (hseed : E ⊆ seedPrefix init s) :
    law init (E ∩ seedCoarseBulkFailure init ell s) ≤
      ENNReal.ofReal (1 / (n : ℝ) ^ 99) * law init E := by
  apply mask_error_population_prefix init hn s E hE hseed
    (fun C => coarseBulkFailure init C ell s)
  intro C
  exact coarse_bulk_prefix_tail init hn C ell s hell htop
    (E ∩ {ω | C = clockSet (labelsAt init ω s)})
    (hE.inter (seed_clockMask_measurable init s C))
    (fun ω hω => ⟨hseed hω.1, hω.2⟩)

theorem coarse_bulk_contacts_of_good (init : InputCfg n)
    (C : Finset (Fin init.card)) (ell s u v : ℕ) (ω : InputLog n)
    (hsafe : shapeSafeAt init C s v ω)
    (hu : firstAfter (fun t => bulkThreshold C.card ≤
      PhaseThreeClockGatedLaw.frontCount (virtualLabels init ω t) ell) s u)
    (hv : firstAfter (fun t => bulkThreshold C.card ≤
      PhaseThreeClockGatedLaw.frontCount (virtualLabels init ω t) (ell + 1)) s v)
    (hgood : ω ∉ coarseBulkFailure init C ell s) :
    maskContacts init C u v ω ≤ 100 * C.card := by
  have huv : u ≤ v := PhaseThreeClockRareDripCharging.firstAfter_le_of_hit hu hv.1
    (hv.2.1.trans (PhaseThreeClockRareDripCharging.frontCount_antitone_level
      _ ell (ell + 1) (Nat.le_succ ell)))
  have h := bulk_first_hit_contacts_le init C (ell + 1) s u v huv ω hsafe
    (by intro t hut htv; exact lt_of_not_ge (hv.2.2 t (hu.1.trans hut) htv))
    (by intro hb; exact hgood ⟨u, hu, hb⟩)
  have heq := maskContacts_seed_eq_stageEvent init ω s u v
  rw [hsafe.1.2] at heq
  rw [heq]
  exact h

def markedFamilyFailure (init : InputCfg n) (s : ℕ) : Set (InputLog n) :=
  ⋃ ell ∈ Finset.Icc 1 (clockCap n - 1), seedMarkedShapeFailure init ell s

def coarseFamilyFailure (init : InputCfg n) (s : ℕ) : Set (InputLog n) :=
  ⋃ ell ∈ Finset.Icc 1 (clockCap n - 1), seedCoarseBulkFailure init ell s

theorem spare_family_coefficient (q n : ℕ) (hn : 1 ≤ n) (hq : q ≤ n) :
    (q : ℝ≥0∞) * ENNReal.ofReal (1 / (n : ℝ) ^ 99) ≤
      ENNReal.ofReal (1 / (n : ℝ) ^ 98) := by
  have hnp : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  calc
    _ ≤ (n : ℝ≥0∞) * ENNReal.ofReal (1 / (n : ℝ) ^ 99) :=
      mul_le_mul_right' (by exact_mod_cast hq) _
    _ = ENNReal.ofReal ((n : ℝ) * (1 / (n : ℝ) ^ 99)) := by
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    _ = _ := by
      congr 1
      rw [show (99 : ℕ) = 98 + 1 from rfl, pow_succ]
      field_simp [hnp.ne']

theorem marked_family_prefix_tail (init : InputCfg n)
    (hn : populationThreshold ≤ n) (s : ℕ)
    (E : Set (InputLog n)) (hE : MeasurableSet[pairLogFiltration _ _ s] E)
    (hseed : E ⊆ seedPrefix init s) :
    law init (E ∩ markedFamilyFailure init s) ≤
      (2 * ENNReal.ofReal (1 / (n : ℝ) ^ 98)) * law init E := by
  have hlarge := (strong_bulk_family_calibration hn).1
  have hI : (Finset.Icc 1 (clockCap n - 1)).card ≤ n := by
    rw [Nat.card_Icc, Nat.add_sub_cancel]
    exact (Nat.sub_le _ _).trans (numeric_clockCap_le_population n hn)
  have ht := finite_union_prefix_bound (law init) E
    (fun ell => seedMarkedShapeFailure init ell s) (Finset.Icc 1 (clockCap n - 1))
    ((2 * ENNReal.ofReal (1 / (n : ℝ) ^ 99)) * law init E)
    (by
      intro ell hell
      obtain ⟨hpos, htop⟩ := Finset.mem_Icc.mp hell
      exact seed_marked_shape_population_prefix_tail init hn ell s hpos
        (by simpa only [clockCap, clockHours] using (show ell + 1 ≤ clockCap n by omega))
        E hE hseed)
  change law init (E ∩ markedFamilyFailure init s) ≤ _ at ht
  calc
    _ ≤ (Finset.Icc 1 (clockCap n - 1)).card *
        ((2 * ENNReal.ofReal (1 / (n : ℝ) ^ 99)) * law init E) := ht
    _ = (2 * ((Finset.Icc 1 (clockCap n - 1)).card *
        ENNReal.ofReal (1 / (n : ℝ) ^ 99))) * law init E := by ring
    _ ≤ _ := mul_le_mul_right' (mul_le_mul_left'
      (spare_family_coefficient _ n (by omega) hI) 2) _

theorem coarse_family_prefix_tail (init : InputCfg n)
    (hn : populationThreshold ≤ n) (s : ℕ)
    (E : Set (InputLog n)) (hE : MeasurableSet[pairLogFiltration _ _ s] E)
    (hseed : E ⊆ seedPrefix init s) :
    law init (E ∩ coarseFamilyFailure init s) ≤
      ENNReal.ofReal (1 / (n : ℝ) ^ 98) * law init E := by
  have hlarge := (strong_bulk_family_calibration hn).1
  have hI : (Finset.Icc 1 (clockCap n - 1)).card ≤ n := by
    rw [Nat.card_Icc, Nat.add_sub_cancel]
    exact (Nat.sub_le _ _).trans (numeric_clockCap_le_population n hn)
  have ht := finite_union_prefix_bound (law init) E
    (fun ell => seedCoarseBulkFailure init ell s) (Finset.Icc 1 (clockCap n - 1))
    (ENNReal.ofReal (1 / (n : ℝ) ^ 99) * law init E)
    (by
      intro ell hell
      obtain ⟨hpos, htop⟩ := Finset.mem_Icc.mp hell
      exact coarse_bulk_population_prefix_tail init hn ell s hpos (by omega) E hE hseed)
  change law init (E ∩ coarseFamilyFailure init s) ≤ _ at ht
  rw [← mul_assoc] at ht
  exact ht.trans (mul_le_mul_right' (spare_family_coefficient _ n (by omega) hI) _)

def rawFamilyFailure (init : InputCfg n) (s : ℕ) : Set (InputLog n) :=
  bulkFamilyFailure init (Finset.Icc 1 (clockCap n)) (fun ell => firstDenseTime init s ell)

def jointLocalFailure (init : InputCfg n) (s : ℕ) : Set (InputLog n) :=
  rawFamilyFailure init s ∪ (seedCountActivationFailure init s ∪
    (markedFamilyFailure init s ∪ (seedActivationBulkFailure init s ∪
      (coarseFamilyFailure init s ∪ seedRareChainFailure init s))))

def jointError (n : ℕ) : ℝ := 1 / (n : ℝ) ^ 10 + 4 / (n : ℝ) ^ 98

theorem prefix_union_bound {Ω : Type*} {m : MeasurableSpace Ω}
    (μ : Measure Ω) (E A B : Set Ω) (a b : ℝ≥0∞)
    (ha : μ (E ∩ A) ≤ a * μ E) (hb : μ (E ∩ B) ≤ b * μ E) :
    μ (E ∩ (A ∪ B)) ≤ (a + b) * μ E := by
  rw [Set.inter_union_distrib_left]
  exact (measure_union_le _ _).trans
    ((add_le_add ha hb).trans_eq (add_mul a b (μ E)).symm)

theorem joint_local_prefix_tail (init : InputCfg n)
    (hn : populationThreshold ≤ n) (hcard : init.card = n) (s : ℕ)
    (E : Set (InputLog n)) (hE : MeasurableSet[pairLogFiltration _ _ s] E)
    (hseed : E ⊆ seedPrefix init s) :
    law init (E ∩ jointLocalFailure init s) ≤
      ENNReal.ofReal (jointError n) * law init E := by
  have hr := firstDense_bulk_family_shape_tail init hcard hn s E hE
  have ha := sharp_activation_population_prefix_tail init hn s E hE hseed
  have hm := marked_family_prefix_tail init hn s E hE hseed
  have hb := activation_bulk_population_prefix_tail init hn s E hE hseed
  have hc := coarse_family_prefix_tail init hn s E hE hseed
  have hx := seed_rare_chain_population_prefix_tail init hn s E hE hseed
  have ht := prefix_union_bound (law init) E _ _ _ _ hr
    (prefix_union_bound (law init) E _ _ _ _ ha
    (prefix_union_bound (law init) E _ _ _ _ hm
    (prefix_union_bound (law init) E _ _ _ _ hb
    (prefix_union_bound (law init) E _ _ _ _ hc hx))))
  change law init (E ∩ jointLocalFailure init s) ≤ _ at ht
  apply ht.trans
  apply mul_le_mul_right'
  have hnlarge := (strong_bulk_family_calibration hn).1
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast (show 2 ≤ n by omega)
  have hnp : (0 : ℝ) < n := by linarith
  have hspare : 2 * (1 / (n : ℝ) ^ 99) ≤ 1 / (n : ℝ) ^ 98 := by
    rw [show (99 : ℕ) = 98 + 1 from rfl, pow_succ]
    apply (mul_le_mul_iff_right₀ (show 0 < (n : ℝ) ^ 98 * (n : ℝ) by positivity)).mp
    field_simp [hnp.ne']
    nlinarith only [hnR]
  have hnonneg : (0 : ℝ) ≤ 1 / (n : ℝ) ^ 98 := by positivity
  have heq :
      ENNReal.ofReal (1 / (2 * (n : ℝ) ^ 10)) +
        (ENNReal.ofReal (1 / (n : ℝ) ^ 99) +
        ((2 * ENNReal.ofReal (1 / (n : ℝ) ^ 98)) +
        (ENNReal.ofReal (1 / (n : ℝ) ^ 99) +
        (ENNReal.ofReal (1 / (n : ℝ) ^ 98) +
          ENNReal.ofReal (1 / (2 * (n : ℝ) ^ 10)))))) =
      ENNReal.ofReal (1 / (n : ℝ) ^ 10 +
        3 * (1 / (n : ℝ) ^ 98) + 2 * (1 / (n : ℝ) ^ 99)) := by
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) by norm_num,
      ← ENNReal.ofReal_mul (by norm_num)]
    rw [← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    field_simp [hnp.ne']
    <;> ring
  rw [heq]
  apply ENNReal.ofReal_le_ofReal
  unfold jointError
  have e4 : 4 / (n : ℝ) ^ 98 = 4 * (1 / (n : ℝ) ^ 98) := by ring
  linarith only [hspare, hnonneg, e4]

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockJointLocalTails

end
