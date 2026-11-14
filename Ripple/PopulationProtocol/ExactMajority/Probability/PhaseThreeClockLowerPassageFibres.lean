-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockLowerPassageFibres.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockLowerPassageProcess
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockFirstAfterFibres
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockShapeSeedFibre

/-!
The P7 launch inequalities are observed at the genuine bulk stopping
time.  They are intersected into that prefix fibre, not into a future
shape event.  Disjoint bulk-time, seed-mask, and seed-time fibres retain
their masses; only the finite positive-level family has a union cost.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockLowerPassageFibres

open TimeTheorem PairLog StageEventSpec
  PhaseThreeClockVirtual PhaseThreeClockGatedLaw
  PhaseThreeClockSeedTails PhaseThreeClockActivationSeed
  PhaseThreeClockSharpActivationSeed PhaseThreeClockShapeSeedFibre
  PhaseThreeClockFirstAfterFibres PhaseThreeClockThinning PhaseThreeClockShapeFreeze
  PhaseThreeClockEarlyMarkCalibration PhaseThreeClockLowerPassageAlgebra
  PhaseThreeClockLowerPassageProcess
open PhaseThreeModel.Numeric

variable {n : ℕ}

theorem lowerLaunch_measurable (init : InputCfg n)
    (C : Finset (Fin init.card)) (ell u : ℕ) :
    MeasurableSet[pairLogFiltration _ _ u] {ω | LowerLaunch init C ell u ω} :=
  (show MeasurableSet {f : Fin init.card → AgentState (hourIndex n) 256 |
    frontCount f ell ≤ StageEventSpec.bulkThreshold C.card ∧
      (frontCount f (ell + 1) : ℝ) ≤
        (StageEventSpec.bulkThreshold C.card : ℝ) ^ 2 / (C.card : ℝ)} from
    (Set.to_countable _).measurableSet).preimage (measurable_virtualLabels init u)

theorem lower_error_calibration {C : ℕ}
    (hC : 0 < (C : ℝ)) (hx : 4194304 ≤ Real.log (C : ℝ)) :
    Real.exp (-(C : ℝ) / 1000000) ≤ 1 / (C : ℝ) ^ 100 := by
  have hlin := (elementary_power_calibration hC hx).2.2.2.2.1
  rw [Real.exp_log hC] at hlin
  have hxzero : 0 ≤ Real.log (C : ℝ) := by linarith
  calc
    _ ≤ Real.exp (Real.log (C : ℝ) * (-100)) :=
      Real.exp_le_exp.mpr (by linarith only [hlin, hxzero])
    _ = (C : ℝ) ^ (-100 : ℝ) := (Real.rpow_def_of_pos hC _).symm
    _ = _ := negative_hundred_rpow_eq C

def lowerPassageFailure (init : InputCfg n) (C : Finset (Fin init.card))
    (ell s : ℕ) : Set (InputLog n) :=
  {ω | ∃ u, firstAfter
      (fun v => StageEventSpec.bulkThreshold C.card ≤
        frontCount (virtualLabels init ω v) ell) s u ∧
    LowerLaunch init C ell u ω ∧ ω ∈ lowerClockFailure init C ell s u}

theorem lower_passage_prefix_tail (init : InputCfg n)
    (hm : populationThreshold ≤ init.card)
    (C : Finset (Fin init.card))
    (hlower : (6 / 25 : ℝ) * (init.card : ℝ) ≤ (C.card : ℝ))
    (ell s : ℕ) (hell : 1 ≤ ell) (htop : ell < clockCap n)
    (E : Set (InputLog n)) (hE : MeasurableSet[pairLogFiltration _ _ s] E) :
    law init (E ∩ lowerPassageFailure init C ell s) ≤
      ENNReal.ofReal (1 / (C.card : ℝ) ^ 100) * law init E := by
  have hCm : C.card ≤ init.card :=
    (Finset.card_le_univ C).trans_eq (Fintype.card_fin init.card)
  obtain ⟨hC, hx, -⟩ := logarithmic_inputs hm hlower hCm
  have hsize := Real.add_one_le_exp (Real.log (C.card : ℝ))
  rw [Real.exp_log hC] at hsize
  have hCbig : 1000000 ≤ C.card := by
    have : (1000000 : ℝ) ≤ C.card := by linarith
    exact_mod_cast this
  have hc : 2 ≤ init.card := by omega
  let P : ℕ → InputLog n → Prop := fun v ω =>
    StageEventSpec.bulkThreshold C.card ≤ frontCount (virtualLabels init ω v) ell
  let D : ℕ → Set (InputLog n) := fun u =>
    {ω | LowerLaunch init C ell u ω} ∩ lowerClockFailure init C ell s u
  have hP (v : ℕ) (_hv : s ≤ v) :
      MeasurableSet[pairLogFiltration _ _ v] {ω | P v ω} :=
    (show MeasurableSet {f : Fin init.card → AgentState (hourIndex n) 256 |
      StageEventSpec.bulkThreshold C.card ≤ frontCount f ell} from
      (Set.to_countable _).measurableSet).preimage (measurable_virtualLabels init v)
  apply firstAfter_prefix_union (law init) (pairLogFiltration _ _)
    P s E hE hP D (ENNReal.ofReal (1 / (C.card : ℝ) ^ 100))
  intro u
  let F := E ∩ {ω | firstAfter (fun v => P v ω) s u}
  let A := F ∩ {ω | LowerLaunch init C ell u ω}
  by_cases hsu : s ≤ u
  · have hF : MeasurableSet[pairLogFiltration _ _ u] F :=
      firstAfter_prefix_measurable (pairLogFiltration _ _) P s u E hE hP
    have ht := lower_clock_prefix_tail init hc C hCbig ell s u hsu hell (by omega)
      A (hF.inter (lowerLaunch_measurable init C ell u)) (fun _ h => h.2)
    have hcal := ENNReal.ofReal_le_ofReal (lower_error_calibration hC hx)
    calc
      law init (F ∩ D u) = law init (A ∩ lowerClockFailure init C ell s u) := by
        congr 1
        ext ω
        simp only [D, A, Set.mem_inter_iff, Set.mem_setOf_eq, and_assoc]
      _ ≤ ENNReal.ofReal (Real.exp (-(C.card : ℝ) / 1000000)) * law init A := ht
      _ ≤ ENNReal.ofReal (1 / (C.card : ℝ) ^ 100) * law init A :=
        mul_le_mul_right' hcal _
      _ ≤ ENNReal.ofReal (1 / (C.card : ℝ) ^ 100) * law init F :=
        mul_le_mul_left' (measure_mono Set.inter_subset_left) _
  · have he : F = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro ω ⟨-, hω⟩
      exact hsu hω.1
    change law init (F ∩ D u) ≤ _ * law init F
    rw [he, Set.empty_inter, measure_empty, mul_zero]

def seedLowerFailure (init : InputCfg n) (s ell : ℕ) : Set (InputLog n) :=
  {ω | ω ∈ lowerPassageFailure init (clockSet (labelsAt init ω s)) ell s}

theorem seed_lower_prefix_tail (init : InputCfg n)
    (hn : populationThreshold ≤ n) (s ell : ℕ)
    (hell : 1 ≤ ell) (htop : ell < clockCap n)
    (E : Set (InputLog n)) (hE : MeasurableSet[pairLogFiltration _ _ s] E)
    (hseed : E ⊆ seedPrefix init s) :
    law init (E ∩ seedLowerFailure init s ell) ≤
      ENNReal.ofReal (1 / (n : ℝ) ^ 99) * law init E := by
  apply seed_mask_prefix_union init s E hE
    (fun C => lowerPassageFailure init C ell s) (ENNReal.ofReal (1 / (n : ℝ) ^ 99))
  intro C
  let A := E ∩ {ω | C = clockSet (labelsAt init ω s)}
  by_cases he : A = ∅
  · simp only [show E ∩ {ω | C = clockSet (labelsAt init ω s)} = ∅ from he,
      Set.empty_inter, measure_empty, mul_zero, le_refl]
  · obtain ⟨η, hη⟩ := Set.nonempty_iff_ne_empty.mpr he
    have hc : PhaseThreeClockGatedLaw.clockCount (labelsAt init η s) = C.card := by
      change (clockSet (labelsAt init η s)).card = C.card
      rw [← hη.2]
    obtain ⟨hm, hlo, -⟩ :=
      seed_clock_calibration_inputs init hn η s C.card (hseed hη.1) hc
    exact (lower_passage_prefix_tail init hm C hlo ell s hell htop A
      (hE.inter (PhaseThreeClockEarlyMarkSeedTail.seed_clockMask_measurable init s C))).trans
      (mul_le_mul_right' (ENNReal.ofReal_le_ofReal
        (seed_clock_error_population init hn η s C (hseed hη.1) hη.2)) _)

def allLowerFailure (init : InputCfg n) (s : ℕ) : Set (InputLog n) :=
  ⋃ ell : Fin (clockCap n - 1), seedLowerFailure init s (ell.val + 1)

theorem all_lower_prefix_tail (init : InputCfg n) (hn : populationThreshold ≤ n)
    (s : ℕ) (E : Set (InputLog n))
    (hE : MeasurableSet[pairLogFiltration _ _ s] E) (hseed : E ⊆ seedPrefix init s) :
    law init (E ∩ allLowerFailure init s) ≤
      ENNReal.ofReal (1 / (n : ℝ) ^ 98) * law init E := by
  have hlo : (6 / 25 : ℝ) * (n : ℝ) ≤ (n : ℝ) := by
    have h : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  obtain ⟨hnp, -, -, -, -, -, -, -, -, -, -, hQn, -, -⟩ :=
    numeric_calibration_core hn hlo le_rfl
  have hc : ((clockCap n - 1 : ℕ) : ℝ≥0∞) *
      ENNReal.ofReal (1 / (n : ℝ) ^ 99) ≤ ENNReal.ofReal (1 / (n : ℝ) ^ 98) := by
    calc
      _ ≤ (n : ℝ≥0∞) * ENNReal.ofReal (1 / (n : ℝ) ^ 99) :=
        mul_le_mul_right' (by exact_mod_cast (show clockCap n - 1 ≤ n by omega)) _
      _ = ENNReal.ofReal ((n : ℝ) * (1 / (n : ℝ) ^ 99)) := by
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg n), ENNReal.ofReal_natCast]
      _ = _ := by
        congr 1
        rw [show (99 : ℕ) = 98 + 1 from rfl, pow_succ]
        field_simp [ne_of_gt hnp]
  have hs : E ∩ allLowerFailure init s ⊆
      ⋃ ell : Fin (clockCap n - 1), E ∩ seedLowerFailure init s (ell.val + 1) := by
    rintro ω ⟨he, hb⟩
    obtain ⟨ell, hel⟩ := Set.mem_iUnion.mp hb
    exact Set.mem_iUnion.mpr ⟨ell, he, hel⟩
  calc
    _ ≤ law init (⋃ ell : Fin (clockCap n - 1), E ∩ seedLowerFailure init s (ell.val + 1)) :=
      measure_mono hs
    _ ≤ ∑' ell : Fin (clockCap n - 1), law init (E ∩ seedLowerFailure init s (ell.val + 1)) :=
      measure_iUnion_le _
    _ ≤ ∑' _ell : Fin (clockCap n - 1), ENNReal.ofReal (1 / (n : ℝ) ^ 99) * law init E :=
      ENNReal.tsum_le_tsum
        (fun ell => seed_lower_prefix_tail init hn s (ell.val + 1) (by omega)
          (by omega) E hE hseed)
    _ = (((clockCap n - 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 / (n : ℝ) ^ 99)) * law init E := by
      simp [tsum_fintype, nsmul_eq_mul, mul_assoc]
    _ ≤ _ := mul_le_mul_right' hc _

theorem lower_clock_good_at_bulk (init : InputCfg n)
    (C : Finset (Fin init.card)) (ell s u : ℕ) (ω : InputLog n)
    (hell : 1 ≤ ell) (htop : ell < clockCap n)
    (hmask : C = clockSet (labelsAt init ω s))
    (hbulk : firstAfter (fun v => StageEventSpec.bulkThreshold C.card ≤
      frontCount (virtualLabels init ω v) ell) s u)
    (hlaunch : LowerLaunch init C ell u ω)
    (hgood : ω ∉ allLowerFailure init s) :
    ω ∉ lowerClockFailure init C ell s u := by
  intro hb
  apply hgood
  let i : Fin (clockCap n - 1) := ⟨ell - 1, by omega⟩
  refine Set.mem_iUnion.mpr ⟨i, ?_⟩
  have hi : i.val + 1 = ell := by dsimp only [i]; omega
  change ω ∈ lowerPassageFailure init (clockSet (labelsAt init ω s)) (i.val + 1) s
  rw [hi, ← hmask]
  exact ⟨u, hbulk, hlaunch, hb⟩

theorem lower_contacts_of_family_good (init : InputCfg n)
    (C : Finset (Fin init.card)) (ell s u tau : ℕ) (ω : InputLog n)
    (hell : 1 ≤ ell) (htop : ell < clockCap n) (hutau : u ≤ tau)
    (hmask : C = clockSet (labelsAt init ω s))
    (hbulk : firstAfter (fun v => StageEventSpec.bulkThreshold C.card ≤
      frontCount (virtualLabels init ω v) ell) s u)
    (hlaunch : LowerLaunch init C ell u ω)
    (hhit : StageEventSpec.bulkThreshold C.card ≤
      frontCount (virtualLabels init ω tau) (ell + 1))
    (hsafe : shapeSafeAt init C s tau ω)
    (hgood : ω ∉ allLowerFailure init s) :
    (2 / 5 : ℝ) * C.card ≤ (maskContacts init C u tau ω : ℝ) := by
  apply le_of_not_gt
  intro hshort
  apply lower_clock_good_at_bulk init C ell s u ω hell htop hmask hbulk hlaunch hgood
  refine ⟨tau - u, ?_, ?_, ?_⟩
  · simpa only [Nat.add_sub_of_le hutau] using hsafe
  · simpa only [Nat.add_sub_of_le hutau] using hhit
  · simpa only [lowerTicks, Nat.add_sub_of_le hutau] using hshort

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockLowerPassageFibres

end
