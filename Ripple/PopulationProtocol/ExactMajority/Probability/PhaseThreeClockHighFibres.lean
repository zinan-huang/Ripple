-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockHighFibres.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockHighPassage
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockFirstAfterFibres
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockShapeSeedFibre

/-!
The P8 start is the genuine first bulk hit.  Its countably many observed
time fibres and the seed's physical Clock masks are disjoint.  Summing
them preserves the prefix mass; only the finite level union costs Q.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockHighFibres

open TimeTheorem PairLog StageEventSpec
  PhaseThreeClockVirtual PhaseThreeClockGatedLaw
  PhaseThreeClockSeedTails PhaseThreeClockActivationSeed
  PhaseThreeClockSharpActivationSeed PhaseThreeClockShapeSeedFibre
  PhaseThreeClockFirstAfterFibres PhaseThreeClockHighPassage
  PhaseThreeClockFirstBulkBase PhaseThreeClockThinning PhaseThreeClockShapeFreeze
open PhaseThreeModel.Numeric

variable {n : ℕ}

def highPassageFailure (init : InputCfg n) (C : Finset (Fin init.card))
    (ell s : ℕ) : Set (InputLog n) :=
  {ω | ∃ u, firstAfter
      (fun v => StageEventSpec.bulkThreshold C.card ≤
        frontCount (virtualLabels init ω v) ell) s u ∧
    ω ∈ highClockFailure init C ell s u}

theorem high_passage_prefix_tail (init : InputCfg n)
    (hm : populationThreshold ≤ init.card)
    (C : Finset (Fin init.card))
    (hlower : (6 / 25 : ℝ) * (init.card : ℝ) ≤ (C.card : ℝ))
    (ell s : ℕ) (hell : 1 ≤ ell) (htop : ell ≤ clockCap n)
    (E : Set (InputLog n)) (hE : MeasurableSet[pairLogFiltration _ _ s] E) :
    law init (E ∩ highPassageFailure init C ell s) ≤
      ENNReal.ofReal (1 / (C.card : ℝ) ^ 100) * law init E := by
  have hCm : C.card ≤ init.card :=
    (Finset.card_le_univ C).trans_eq (Fintype.card_fin init.card)
  obtain ⟨hC, hx, -⟩ := logarithmic_inputs hm hlower hCm
  have hsize := Real.add_one_le_exp (Real.log (C.card : ℝ))
  rw [Real.exp_log hC] at hsize
  have hCbig : 100 ≤ C.card := by
    have : (100 : ℝ) ≤ C.card := by linarith
    exact_mod_cast this
  have hc : 2 ≤ init.card := by omega
  let P : ℕ → InputLog n → Prop := fun v ω =>
    StageEventSpec.bulkThreshold C.card ≤ frontCount (virtualLabels init ω v) ell
  have hP (v : ℕ) (_hv : s ≤ v) :
      MeasurableSet[pairLogFiltration _ _ v] {ω | P v ω} :=
    (show MeasurableSet {f : Fin init.card → AgentState (hourIndex n) 256 |
      StageEventSpec.bulkThreshold C.card ≤ frontCount f ell} from
      (Set.to_countable _).measurableSet).preimage (measurable_virtualLabels init v)
  apply firstAfter_prefix_union (law init) (pairLogFiltration _ _)
    P s E hE hP (highClockFailure init C ell s)
      (ENNReal.ofReal (1 / (C.card : ℝ) ^ 100))
  intro u
  let F := E ∩ {ω | firstAfter (fun v => P v ω) s u}
  by_cases hsu : s ≤ u
  · exact (high_clock_prefix_tail init hc C hCbig ell s u hell htop hsu F
      (firstAfter_prefix_measurable (pairLogFiltration _ _) P s u E hE hP)
      (fun ω hω => hω.2.2.1)).trans
        (mul_le_mul_right' (first_bulk_error_calibration hC hx) _)
  · have he : F = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro ω ⟨-, hω⟩
      exact hsu hω.1
    change law init (F ∩ highClockFailure init C ell s u) ≤ _ * law init F
    rw [he, Set.empty_inter, measure_empty, mul_zero]

def seedHighFailure (init : InputCfg n) (s ell : ℕ) : Set (InputLog n) :=
  {ω | ω ∈ highPassageFailure init (clockSet (labelsAt init ω s)) ell s}

theorem seed_high_prefix_tail (init : InputCfg n)
    (hn : populationThreshold ≤ n) (s ell : ℕ)
    (hell : 1 ≤ ell) (htop : ell ≤ clockCap n)
    (E : Set (InputLog n)) (hE : MeasurableSet[pairLogFiltration _ _ s] E)
    (hseed : E ⊆ seedPrefix init s) :
    law init (E ∩ seedHighFailure init s ell) ≤
      ENNReal.ofReal (1 / (n : ℝ) ^ 99) * law init E := by
  apply seed_mask_prefix_union init s E hE
    (fun C => highPassageFailure init C ell s) (ENNReal.ofReal (1 / (n : ℝ) ^ 99))
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
    exact (high_passage_prefix_tail init hm C hlo ell s hell htop A
      (hE.inter (PhaseThreeClockEarlyMarkSeedTail.seed_clockMask_measurable init s C))).trans
      (mul_le_mul_right' (ENNReal.ofReal_le_ofReal
        (seed_clock_error_population init hn η s C (hseed hη.1) hη.2)) _)

def allHighFailure (init : InputCfg n) (s : ℕ) : Set (InputLog n) :=
  ⋃ ell : Fin (clockCap n), seedHighFailure init s (ell.val + 1)

theorem all_high_prefix_tail (init : InputCfg n) (hn : populationThreshold ≤ n)
    (s : ℕ) (E : Set (InputLog n))
    (hE : MeasurableSet[pairLogFiltration _ _ s] E) (hseed : E ⊆ seedPrefix init s) :
    law init (E ∩ allHighFailure init s) ≤
      ENNReal.ofReal (1 / (n : ℝ) ^ 98) * law init E := by
  have hlo : (6 / 25 : ℝ) * (n : ℝ) ≤ (n : ℝ) := by
    have h : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  obtain ⟨hnp, -, -, -, -, -, -, -, -, -, -, hQn, -, -⟩ :=
    numeric_calibration_core hn hlo le_rfl
  have hc : (clockCap n : ℝ≥0∞) * ENNReal.ofReal (1 / (n : ℝ) ^ 99) ≤
      ENNReal.ofReal (1 / (n : ℝ) ^ 98) := by
    calc
      _ ≤ (n : ℝ≥0∞) * ENNReal.ofReal (1 / (n : ℝ) ^ 99) :=
        mul_le_mul_right' (by exact_mod_cast hQn) _
      _ = ENNReal.ofReal ((n : ℝ) * (1 / (n : ℝ) ^ 99)) := by
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg n), ENNReal.ofReal_natCast]
      _ = _ := by
        congr 1
        rw [show (99 : ℕ) = 98 + 1 from rfl, pow_succ]
        field_simp [ne_of_gt hnp]
  have hs : E ∩ allHighFailure init s ⊆
      ⋃ ell : Fin (clockCap n), E ∩ seedHighFailure init s (ell.val + 1) := by
    rintro ω ⟨he, hb⟩
    obtain ⟨ell, hel⟩ := Set.mem_iUnion.mp hb
    exact Set.mem_iUnion.mpr ⟨ell, he, hel⟩
  calc
    _ ≤ law init (⋃ ell : Fin (clockCap n), E ∩ seedHighFailure init s (ell.val + 1)) :=
      measure_mono hs
    _ ≤ ∑' ell : Fin (clockCap n), law init (E ∩ seedHighFailure init s (ell.val + 1)) :=
      measure_iUnion_le _
    _ ≤ ∑' _ell : Fin (clockCap n), ENNReal.ofReal (1 / (n : ℝ) ^ 99) * law init E :=
      ENNReal.tsum_le_tsum
        (fun ell => seed_high_prefix_tail init hn s (ell.val + 1) (by omega)
          (by omega) E hE hseed)
    _ = ((clockCap n : ℝ≥0∞) * ENNReal.ofReal (1 / (n : ℝ) ^ 99)) * law init E := by
      simp [tsum_fintype, nsmul_eq_mul, mul_assoc]
    _ ≤ _ := mul_le_mul_right' hc _

theorem high_clock_good_at_bulk (init : InputCfg n)
    (C : Finset (Fin init.card)) (ell s u : ℕ) (ω : InputLog n)
    (hell : 1 ≤ ell) (htop : ell ≤ clockCap n)
    (hmask : C = clockSet (labelsAt init ω s))
    (hbulk : firstAfter (fun v => StageEventSpec.bulkThreshold C.card ≤
      frontCount (virtualLabels init ω v) ell) s u)
    (hgood : ω ∉ allHighFailure init s) :
    ω ∉ highClockFailure init C ell s u := by
  intro hb
  apply hgood
  let i : Fin (clockCap n) := ⟨ell - 1, by omega⟩
  refine Set.mem_iUnion.mpr ⟨i, ?_⟩
  have hi : i.val + 1 = ell := by dsimp only [i]; omega
  change ω ∈ highPassageFailure init (clockSet (labelsAt init ω s)) (i.val + 1) s
  rw [hi, ← hmask]
  exact ⟨u, hbulk, hb⟩

/-- Any genuine high first hit, not merely a chosen canonical witness. -/
theorem high_contacts_of_family_good (init : InputCfg n)
    (C : Finset (Fin init.card)) (ell s u tau : ℕ) (ω : InputLog n)
    (hell : 1 ≤ ell) (htop : ell ≤ clockCap n)
    (hmask : C = clockSet (labelsAt init ω s))
    (hbulk : firstAfter (fun v => StageEventSpec.bulkThreshold C.card ≤
      frontCount (virtualLabels init ω v) ell) s u)
    (hhigh : firstAfter (fun v => StageEventSpec.highThreshold C.card ≤
      frontCount (virtualLabels init ω v) ell) s tau)
    (hsafe : shapeSafeAt init C s tau ω)
    (hgood : ω ∉ allHighFailure init s) :
    maskContacts init C u tau ω ≤ 8 * C.card :=
  high_first_hit_contacts_le init C ell s u tau ω hsafe hhigh hbulk.1
    (high_clock_good_at_bulk init C ell s u ω hell htop hmask hbulk hgood)

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockHighFibres

end
