-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockFineThinning.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockHourThinningRows

noncomputable section
open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal BigOperators

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockFineThinning

open TimeTheorem PairLog StageEventSpec PhaseThreeModel.Numeric
  PhaseThreeClockProducer PhaseThreeClockVirtual PhaseThreeClockCore PhaseThreeClockCoreCounts
  PhaseThreeClockRows PhaseThreeClockSeedTails PhaseThreeClockActivationSeed
  PhaseThreeClockGatedLaw PhaseThreeClockMarkedWindow PhaseThreeClockMacroscopicActivation
  PhaseThreeClockShapeSeedFibre PhaseThreeClockSharpActivationSeed
  PhaseThreeClockThinningCalibrated PhaseThreeClockRawLocalRow
  PhaseThreeClockHourThinningRows PhaseThreeClockShapeFreeze

variable {n : ℕ}

def fineStart (init : InputCfg n) (s ell : ℕ) (ω : InputLog n) : WithTop ℕ :=
  max (levelPositiveTime init s ell ω) (macroscopicTime init s ω)

theorem fineStart_stopping (init : InputCfg n) (s ell : ℕ) :
    IsStoppingTime (pairLogFiltration _ _) (fineStart init s ell) := by
  intro u
  simpa only [fineStart, max_le_iff, Set.setOf_and] using
    (levelPositiveTime_isStoppingTime init s ell u).inter
      (macroscopicTime_isStoppingTime init s u)

theorem fineStart_seed_le (init : InputCfg n) (s ell : ℕ) (ω : InputLog n) :
    (s : WithTop ℕ) ≤ fineStart init s ell ω :=
  (seed_le_macroscopicTime init s ω).trans (le_max_right _ _)

open Classical in
theorem least_firstAfter_eq {P : ℕ → Prop} {s t : ℕ}
    (h : firstAfter P s t) :
    (if hx : ∃ v, s ≤ v ∧ P v then ((Nat.find hx : ℕ) : WithTop ℕ) else ⊤) =
      (t : WithTop ℕ) := by
  classical
  rw [dif_pos ⟨t, h.1, h.2.1⟩]
  have hx : ∃ v, s ≤ v ∧ P v := ⟨t, h.1, h.2.1⟩
  have hf : firstAfter P s (Nat.find hx) := by
    refine ⟨(Nat.find_spec hx).1, (Nat.find_spec hx).2, ?_⟩
    intro v hsv hvt hp
    exact (not_lt_of_ge (Nat.find_min' hx ⟨hsv, hp⟩)) hvt
  exact_mod_cast firstAfter_unique hf h

theorem fineStart_eq_firstAfter (init : InputCfg n) (ω : InputLog n)
    (s ell f a : ℕ)
    (hf : firstAfter (fun v => 0 < frontCount (virtualLabels init ω v) ell) s f)
    (ha : firstAfter (fun v => macroscopicThreshold init.card ≤
      PhaseThreeClockActivationLaw.activeCount (virtualLabels init ω v)) s a) :
    fineStart init s ell ω = (max f a : ℕ) := by
  have hp : levelPositiveTime init s ell ω = (f : WithTop ℕ) :=
    by unfold levelPositiveTime; convert least_firstAfter_eq hf
  have hq : macroscopicTime init s ω = (a : WithTop ℕ) :=
    by unfold macroscopicTime; convert least_firstAfter_eq ha
  simp only [fineStart, hp, hq]
  norm_cast

def fineThinningFailure (init : InputCfg n) (C : Finset (Fin init.card))
    (s ell : ℕ) : Set (InputLog n) :=
  ⋃ u : ℕ, {ω | fineStart init s ell ω = (u : WithTop ℕ)} ∩
    {ω | (StageEventSpec.clockContacts init ω s u
      (u + 2000 * init.card * PhaseThreeModel.Numeric.frontWidth C.card) : ℝ) < (fineTicks C.card : ℝ)}

theorem fine_thinning_prefix_tail (init : InputCfg n)
    (hm : populationThreshold ≤ init.card) (C : Finset (Fin init.card))
    (hlo : (6 / 25 : ℝ) * (init.card : ℝ) ≤ (C.card : ℝ))
    (s ell : ℕ) (E : Set (InputLog n))
    (hE : MeasurableSet[pairLogFiltration _ _ s] E)
    (hmask : ∀ ω ∈ E, clockSet (labelsAt init ω s) = C) :
    law init (E ∩ fineThinningFailure init C s ell) ≤
      ENNReal.ofReal (1 / (C.card : ℝ) ^ 100) * law init E := by
  let A : ℕ → Set (InputLog n) := fun u =>
    E ∩ {ω | fineStart init s ell ω = (u : WithTop ℕ)}
  have hA (u : ℕ) : MeasurableSet[pairLogFiltration _ _ u] (A u) := by
    by_cases hsu : s ≤ u
    · exact (((pairLogFiltration _ _).mono hsu) _ hE).inter
        ((fineStart_stopping init s ell).measurableSet_eq_of_countable u)
    · have he : A u = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        rintro ω ⟨-, hu⟩
        have hs := fineStart_seed_le init s ell ω
        rw [hu] at hs
        exact hsu (by exact_mod_cast hs)
      rw [he]
      exact MeasurableSpace.measurableSet_empty _
  have hd : Pairwise (fun u v => Disjoint (A u) (A v)) := by
    intro u v huv
    apply Set.disjoint_left.mpr
    intro ω hu hv
    exact huv (WithTop.coe_injective (hu.2.symm.trans hv.2))
  have hmass : (∑' u, law init (A u)) ≤ law init E := by
    rw [← measure_iUnion hd (fun u => (pairLogFiltration _ _).le u _ (hA u))]
    exact measure_mono (by
      intro ω hω
      obtain ⟨u, hu⟩ := Set.mem_iUnion.mp hω
      exact hu.1)
  let B : ℕ → Set (InputLog n) := fun u => {ω |
    (StageEventSpec.clockContacts init ω s u
      (u + 2000 * init.card * PhaseThreeModel.Numeric.frontWidth C.card) : ℝ) < (fineTicks C.card : ℝ)}
  have ht (u : ℕ) : law init (A u ∩ B u) ≤
      ENNReal.ofReal (1 / (C.card : ℝ) ^ 100) * law init (A u) := by
    simpa only [PhaseThreeClockEarlyMarkCalibration.negative_hundred_rpow_eq] using
      fine_contact_prefix_calibrated init hm C hlo s u (A u) (hA u)
        (fun ω hω => hmask ω hω.1)
  have hs : E ∩ fineThinningFailure init C s ell ⊆ ⋃ u, A u ∩ B u := by
    rintro ω ⟨he, hb⟩
    obtain ⟨u, hu, hc⟩ := Set.mem_iUnion.mp hb
    exact Set.mem_iUnion.mpr ⟨u, ⟨he, hu⟩, hc⟩
  calc
    _ ≤ law init (⋃ u, A u ∩ B u) := measure_mono hs
    _ ≤ ∑' u, law init (A u ∩ B u) := measure_iUnion_le _
    _ ≤ ∑' u, ENNReal.ofReal (1 / (C.card : ℝ) ^ 100) * law init (A u) :=
      ENNReal.tsum_le_tsum ht
    _ = ENNReal.ofReal (1 / (C.card : ℝ) ^ 100) * ∑' u, law init (A u) := by
      rw [ENNReal.tsum_mul_left]
    _ ≤ _ := mul_le_mul_left' hmass _

def seedFineFailure (init : InputCfg n) (s ell : ℕ) : Set (InputLog n) :=
  {ω | ω ∈ fineThinningFailure init (clockSet (labelsAt init ω s)) s ell}

theorem seed_fine_prefix_tail (init : InputCfg n)
    (hn : populationThreshold ≤ n) (s ell : ℕ)
    (E : Set (InputLog n)) (hE : MeasurableSet[pairLogFiltration _ _ s] E)
    (hseed : E ⊆ seedPrefix init s) :
    law init (E ∩ seedFineFailure init s ell) ≤
      ENNReal.ofReal (1 / (n : ℝ) ^ 99) * law init E := by
  apply seed_mask_prefix_union init s E hE
    (fun C => fineThinningFailure init C s ell) (ENNReal.ofReal (1 / (n : ℝ) ^ 99))
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
    exact (fine_thinning_prefix_tail init hm C hlo s ell A
      (hE.inter (PhaseThreeClockEarlyMarkSeedTail.seed_clockMask_measurable init s C))
      (fun ω hω => hω.2.symm)).trans
      (mul_le_mul_right' (ENNReal.ofReal_le_ofReal
        (seed_clock_error_population init hn η s C (hseed hη.1) hη.2)) _)

def allFineFailure (init : InputCfg n) (s : ℕ) : Set (InputLog n) :=
  ⋃ ell : Fin (clockCap n), seedFineFailure init s (ell.val + 1)

theorem all_fine_prefix_tail (init : InputCfg n) (hn : populationThreshold ≤ n)
    (s : ℕ) (E : Set (InputLog n))
    (hE : MeasurableSet[pairLogFiltration _ _ s] E) (hseed : E ⊆ seedPrefix init s) :
    law init (E ∩ allFineFailure init s) ≤
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
  have hs : E ∩ allFineFailure init s ⊆
      ⋃ ell : Fin (clockCap n), E ∩ seedFineFailure init s (ell.val + 1) := by
    rintro ω ⟨he, hb⟩
    obtain ⟨ell, hel⟩ := Set.mem_iUnion.mp hb
    exact Set.mem_iUnion.mpr ⟨ell, he, hel⟩
  calc
    _ ≤ law init (⋃ ell : Fin (clockCap n), E ∩ seedFineFailure init s (ell.val + 1)) :=
      measure_mono hs
    _ ≤ ∑' ell : Fin (clockCap n), law init (E ∩ seedFineFailure init s (ell.val + 1)) :=
      measure_iUnion_le _
    _ ≤ ∑' _ell : Fin (clockCap n), ENNReal.ofReal (1 / (n : ℝ) ^ 99) * law init E :=
      ENNReal.tsum_le_tsum (fun ell => seed_fine_prefix_tail init hn s (ell.val + 1) E hE hseed)
    _ = ((clockCap n : ℝ≥0∞) * ENNReal.ofReal (1 / (n : ℝ) ^ 99)) * law init E := by
      simp [tsum_fintype, nsmul_eq_mul, mul_assoc]
    _ ≤ _ := mul_le_mul_right' hc _

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockFineThinning

end
