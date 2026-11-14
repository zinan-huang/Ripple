-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockBulkShapeBudget.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockObservedStarts

/-!
A stronger P3a estimate on the unchanged first-hit horizon and failure
event.  The exact epidemic rate makes the existing reciprocal potential
contract by 1-3/(8m), for m >= 64.  The resulting per-level error is
m^(-41/4); the compiled logarithmic cap bound makes the whole H* family
cost at most 1/(2m^10).  No future environment event enters a prefix.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators MeasureTheory ProbabilityTheory

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockBulkShapeBudget

open TimeTheorem PairLog PairLogAuxiliary PhaseThreeModel.Numeric
  PhaseThreeClockVirtual PhaseThreeClockGatedLaw PhaseThreeClockGatedLevelOne
  PhaseThreeClockProbabilityFloors PhaseThreeClockPrefixTails
  PhaseThreeClockStoppedPassage PhaseThreeClockReciprocalAlgebra
  PhaseThreeClockReciprocalPassage PhaseThreeClockPotentialTail
  PhaseThreeClockObservedPassage PhaseThreeClockObservedPassageSplice
  PhaseThreeClockBulkFamily PhaseThreeClockObservedStarts

variable {L : ℕ}

/-- Keeping the exact epidemic rate avoids the loss from rounding its
state-dependent value down before applying the reciprocal decrement. -/
theorem frontLoss_epidemic_rate (X : ℕ) (hX : 1 ≤ X) (m C : ℝ)
    (hm : 64 ≤ m) (hdensity : 6 * m ≤ 25 * C)
    (hsparse : 10 * (X : ℝ) ≤ C) :
    (3 / (8 * m)) * frontWeight X ≤
      frontLoss X * (2 * (X : ℝ) * (C - (X : ℝ)) / (m * (m - 1))) := by
  have hmp : 0 < m := by linarith
  have hmonepos : 0 < m - 1 := by linarith
  have hXR : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hnum :
      3 * (m - 1) * (5 * (X : ℝ) + 1) ≤
        80 * (X : ℝ) * (C - (X : ℝ)) := by
    by_cases hxone : X = 1
    · subst X
      norm_num
      linarith only [hdensity, hm]
    · have hxtwo : (2 : ℝ) ≤ X := by
        exact_mod_cast (show 2 ≤ X by omega)
      have hroom : 27 * m ≤ 125 * (C - (X : ℝ)) := by
        linarith only [hdensity, hsparse]
      have hprod := mul_le_mul_of_nonneg_left hroom
        (show (0 : ℝ) ≤ X by positivity)
      have hgap : 0 ≤ (57 * (X : ℝ) - 75) * m :=
        mul_nonneg (by linarith only [hxtwo]) hmp.le
      nlinarith only [hprod, hgap, hXR]
  have hratio :
      3 / (8 * m) ≤
        10 * (X : ℝ) * (C - (X : ℝ)) /
          (m * (m - 1) * (5 * (X : ℝ) + 1)) := by
    apply (div_le_div_iff₀ (by positivity : 0 < 8 * m)
      (by positivity : 0 < m * (m - 1) * (5 * (X : ℝ) + 1))).2
    have hscaled := mul_le_mul_of_nonneg_left hnum hmp.le
    nlinarith only [hscaled]
  have hleft : 5 * (X : ℝ) - 4 ≠ 0 := by linarith
  have hright : 5 * (X : ℝ) + 1 ≠ 0 := by positivity
  have hmone : m - 1 ≠ 0 := by linarith
  have hid :
      frontLoss X * (2 * (X : ℝ) * (C - (X : ℝ)) / (m * (m - 1))) =
        (10 * (X : ℝ) * (C - (X : ℝ)) /
          (m * (m - 1) * (5 * (X : ℝ) + 1))) * frontWeight X := by
    rw [frontLoss_formula X hX, frontWeight_eq_of_one_le X hX]
    field_simp [hleft, hright, hmp.ne', hmone]
    <;> ring
  rw [hid]
  exact mul_le_mul_of_nonneg_right hratio (frontWeight_pos X).le

theorem gated_reciprocal_rate (f : Fin m → AgentState L 256)
    (hm : 64 ≤ m) (ell : ℕ) (hell : 1 ≤ ell)
    (hpositive : 1 ≤ frontCount f ell)
    (hdensity : 6 * m ≤ 25 * clockCount f)
    (hsparse : 10 * frontCount f ell ≤ clockCount f) :
    (3 / (8 * (m : ℝ))) * frontWeight (frontCount f ell) ≤
      frontLoss (frontCount f ell) *
        (((goodPairs (GatedTick ell) f).card : ℝ) /
          ((m : ℝ) * ((m : ℝ) - 1))) := by
  have hmR : (64 : ℝ) ≤ m := by exact_mod_cast hm
  have hXC := frontCount_le_clockCount f ell
  have hcount :
      2 * (frontCount f ell : ℝ) *
          ((clockCount f : ℝ) - (frontCount f ell : ℝ)) ≤
        ((goodPairs (GatedTick ell) f).card : ℝ) := by
    have hcast :
        ((2 * frontCount f ell * (clockCount f - frontCount f ell) : ℕ) : ℝ) ≤
          ((goodPairs (GatedTick ell) f).card : ℝ) := by
      exact_mod_cast epidemic_le_gated_pairs f ell hell
    simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub hXC] using hcast
  apply (frontLoss_epidemic_rate (frontCount f ell) hpositive (m : ℝ)
    (clockCount f : ℝ) hmR (by exact_mod_cast hdensity)
      (by exact_mod_cast hsparse)).trans
  apply mul_le_mul_of_nonneg_left _ (frontLoss_bounds _).1
  exact div_le_div_of_nonneg_right hcount
    (mul_nonneg (Nat.cast_nonneg m) (by linarith))

/-- The stronger drift is supplied by the actual gated pair law. -/
theorem passageWeight_shape_drift (init : Cfg L 256) (hm : 64 ≤ init.card)
    (ell b s : ℕ) (hell : 1 ≤ ell) (hcap : ell ≤ 256 * (L + 1)) :
    ∀ t, (law init)[passageWeight init ell b s (t + 1) |
        shiftedFiltration (pairLogFiltration L 256) s t] ≤ᵐ[law init]
      fun ω => (1 - 3 / (8 * (init.card : ℝ))) *
        passageWeight init ell b s t ω := by
  have hZ := passageWeight_stronglyMeasurable init ell b s
  have hZbound : ∀ t, ∀ᵐ ω ∂law init,
      0 ≤ passageWeight init ell b s t ω ∧
        passageWeight init ell b s t ω ≤ 1 :=
    fun t => ae_of_all _ (passageWeight_bounds init ell b s t)
  have hD := passageLoss_stronglyMeasurable init ell b s
  have hDbound : ∀ t, ∀ᵐ ω ∂law init,
      0 ≤ passageLoss init ell b s t ω ∧ passageLoss init ell b s t ω ≤ 1 :=
    fun t => ae_of_all _ (passageLoss_bounds init ell b s t)
  have hI : ∀ t,
      StronglyMeasurable[shiftedFiltration (pairLogFiltration L 256) s (t + 1)]
        (gatedIndicator init ell (s + t)) := by
    intro t
    simpa only [gatedIndicator, shiftedFiltration_apply, Nat.add_assoc] using
      stronglyMeasurable_aux_pair_indicator init virtualRule (GatedTick ell) (s + t)
  have hz : ∀ t, ∀ᵐ ω ∂law init,
      gatedIndicator init ell (s + t) ω = 0 ∨
        gatedIndicator init ell (s + t) ω = 1 :=
    fun t => ae_of_all _ (gatedIndicator_zero_one init ell (s + t))
  have hstep : ∀ t, passageWeight init ell b s (t + 1) ≤ᵐ[law init]
      fun ω => passageWeight init ell b s t ω -
        passageLoss init ell b s t ω * gatedIndicator init ell (s + t) ω :=
    fun t => ae_of_all _ (passageWeight_step init ell b s t hell hcap)
  have hrate : ∀ t, ∀ᵐ ω ∂law init,
      (3 / (8 * (init.card : ℝ))) * passageWeight init ell b s t ω ≤
        passageLoss init ell b s t ω *
          ((law init)[gatedIndicator init ell (s + t) |
            shiftedFiltration (pairLogFiltration L 256) s t]) ω := by
    intro t
    filter_upwards [gatedTick_conditional_law init (by omega) ell (s + t)] with ω hf
    classical
    by_cases ht : (t : WithTop ℕ) < passageStop init ell b s ω
    · have hw := passageWindow_of_lt_stop init ell b s t ω ht t le_rfl
      have htm : ω ∈ {ω | (t : WithTop ℕ) < passageStop init ell b s ω} := ht
      rw [passageWeight, Set.indicator_of_mem htm,
        passageLoss, Set.indicator_of_mem htm]
      have hcond :
          ((law init)[gatedIndicator init ell (s + t) |
            shiftedFiltration (pairLogFiltration L 256) s t]) ω =
          ((goodPairs (GatedTick ell) (virtualLabels init ω (s + t))).card : ℝ) /
            ((init.card : ℝ) * ((init.card : ℝ) - 1)) := by
        simpa only [gatedIndicator, shiftedFiltration_apply] using hf
      rw [hcond]
      exact gated_reciprocal_rate _ hm ell hell
        hw.2.2.2.1 hw.2.2.1 hw.2.2.2.2.2
    · simp [passageWeight, passageLoss, ht]
  exact affine_conditional_drift hZ hZbound hD hDbound hI hz hstep hrate

def strongBulkError (m : ℕ) : ℝ := (m : ℝ) ^ (-(41 / 4 : ℝ))

theorem shape_contraction_nonneg (m : ℕ) (hm : 1 ≤ m) :
    (0 : ℝ) ≤ 1 - 3 / (8 * (m : ℝ)) := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hfrac : (3 : ℝ) / (8 * (m : ℝ)) ≤ 1 := by
    apply (div_le_iff₀ (by positivity)).2
    linarith
  linarith

theorem strong_potential_calibration (m N : ℕ) (hm : 1 ≤ m)
    (R : ℝ) (hR : 0 ≤ R) (hRm : R ≤ (m : ℝ))
    (hN : 30 * (m : ℝ) * Real.log (m : ℝ) ≤ (N : ℝ)) :
    R * (1 - 3 / (8 * (m : ℝ))) ^ N ≤ strongBulkError m := by
  have hmp : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hbase : 1 - 3 / (8 * (m : ℝ)) ≤
      Real.exp (-(3 / (8 * (m : ℝ)))) := by
    simpa only [sub_eq_add_neg, add_comm] using
      Real.add_one_le_exp (-(3 / (8 * (m : ℝ))))
  have hpower :
      (1 - 3 / (8 * (m : ℝ))) ^ N ≤
        Real.exp (-(3 * (N : ℝ) / (8 * (m : ℝ)))) := by
    apply (pow_le_pow_left₀ (shape_contraction_nonneg m hm) hbase N).trans_eq
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hratio : (45 / 4 : ℝ) * Real.log (m : ℝ) ≤
      3 * (N : ℝ) / (8 * (m : ℝ)) := by
    apply (le_div_iff₀ (by positivity)).2
    nlinarith only [hN]
  calc
    _ ≤ R * Real.exp (-(3 * (N : ℝ) / (8 * (m : ℝ)))) :=
      mul_le_mul_of_nonneg_left hpower hR
    _ ≤ (m : ℝ) * Real.exp (-(3 * (N : ℝ) / (8 * (m : ℝ)))) :=
      mul_le_mul_of_nonneg_right hRm (Real.exp_nonneg _)
    _ ≤ (m : ℝ) * Real.exp (-((45 / 4 : ℝ) * Real.log (m : ℝ))) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg hratio)) hmp.le
    _ = Real.exp (Real.log (m : ℝ) * (-(41 / 4 : ℝ))) := by
      calc
        _ = Real.exp (Real.log (m : ℝ)) *
            Real.exp (-((45 / 4 : ℝ) * Real.log (m : ℝ))) := by rw [Real.exp_log hmp]
        _ = _ := by rw [← Real.exp_add]; congr 1; ring
    _ = strongBulkError m := (Real.rpow_def_of_pos hmp _).symm

theorem strong_bulk_passage_prefix_tail (init : Cfg L 256)
    (hm : 64 ≤ init.card) (C ell s : ℕ) (hC : C ≤ init.card)
    (hell : 1 ≤ ell) (hcap : ell ≤ 256 * (L + 1))
    (E : Set (Ω L 256)) (hE : MeasurableSet[pairLogFiltration L 256 s] E) :
    law init (E ∩ {ω | (firstHitHorizon init.card : WithTop ℕ) <
      passageStop init ell (StageEventSpec.bulkThreshold C) s ω}) ≤
        ENNReal.ofReal (strongBulkError init.card) * law init E := by
  have hbound : ∀ t, ∀ᵐ ω ∂law init,
      0 ≤ passageWeight init ell (StageEventSpec.bulkThreshold C) s t ω ∧
        passageWeight init ell (StageEventSpec.bulkThreshold C) s t ω ≤ 1 :=
    fun t => ae_of_all _ (passageWeight_bounds init ell (StageEventSpec.bulkThreshold C) s t)
  have hEs : MeasurableSet[shiftedFiltration (pairLogFiltration L 256) s 0] E := by
    simpa only [shiftedFiltration_apply, Nat.add_zero] using hE
  have ht := prefix_potential_tail_ennreal
    (passageWeight_stronglyMeasurable init ell (StageEventSpec.bulkThreshold C) s)
    hbound (shape_contraction_nonneg init.card (by omega))
    (passageWeight_shape_drift init hm ell (StageEventSpec.bulkThreshold C) s hell hcap)
    E hEs (firstHitHorizon init.card)
    {ω | (firstHitHorizon init.card : WithTop ℕ) <
      passageStop init ell (StageEventSpec.bulkThreshold C) s ω}
    (5 * (StageEventSpec.bulkThreshold C : ℝ)) (by positivity)
    (by
      intro ω hω
      have hw := passageWindow_of_lt_stop init ell (StageEventSpec.bulkThreshold C)
        s (firstHitHorizon init.card) ω hω (firstHitHorizon init.card) le_rfl
      simpa only [passageWeight, Set.indicator_of_mem hω] using
        frontWeight_boundary
          (frontCount (virtualLabels init ω (s + firstHitHorizon init.card)) ell)
          (StageEventSpec.bulkThreshold C) hw.2.2.2.2.1)
  exact ht.trans (mul_le_mul_right' (ENNReal.ofReal_le_ofReal
    (strong_potential_calibration init.card (firstHitHorizon init.card) (by omega)
      (5 * (StageEventSpec.bulkThreshold C : ℝ)) (by positivity)
      (by exact_mod_cast five_bulk_le_population init.card C (by omega) hC)
      (Nat.le_ceil _))) _)

theorem strong_observed_bulk_prefix_tail (init : Cfg L 256)
    (hm : 64 ≤ init.card) (C ℓ s : ℕ)
    (hC : C ≤ init.card) (hdensity : 6 * init.card ≤ 25 * C)
    (hℓ : 1 ≤ ℓ) (hcap : ℓ ≤ 256 * (L + 1))
    (E : Set (Ω L 256)) (hE : MeasurableSet[pairLogFiltration L 256 s] E)
    (hstart : ∀ ω ∈ E,
      1 ≤ frontCount (virtualLabels init ω s) ℓ ∧
        clockCount (virtualLabels init ω s) = C) :
    law init
        (E ∩ observedPassageFailure init ℓ C s
          (PhaseThreeModel.Numeric.firstHitHorizon init.card)) ≤
      ENNReal.ofReal (strongBulkError init.card) * law init E := by
  apply (measure_mono ?_).trans
    (strong_bulk_passage_prefix_tail init hm C ℓ s hC hℓ hcap E hE)
  rintro ω ⟨he, hspan, hbelow⟩
  exact ⟨he, below_bulk_implies_survival init ω ℓ C s _
    hℓ hcap hspan hdensity (hstart ω he).2 (hstart ω he).1 hbelow⟩

theorem strong_random_count_prefix_tail (init : Cfg L 256)
    (hm : 64 ≤ init.card) (ℓ s : ℕ)
    (hℓ : 1 ≤ ℓ) (hcap : ℓ ≤ 256 * (L + 1))
    (E : Set (Ω L 256)) (hE : MeasurableSet[pairLogFiltration L 256 s] E)
    (hstart : ∀ ω ∈ E, DensePositiveStart init ℓ ω s) :
    law init (E ∩ randomCountPassageFailure init ℓ s
      (PhaseThreeModel.Numeric.firstHitHorizon init.card)) ≤
      ENNReal.ofReal (strongBulkError init.card) * law init E := by
  classical
  let A : ℕ → Set (Ω L 256) :=
    fun C => E ∩ {ω | clockCount (virtualLabels init ω s) = C}
  let B := randomCountPassageFailure init ℓ s
    (PhaseThreeModel.Numeric.firstHitHorizon init.card)
  have hAm (C : ℕ) : MeasurableSet[pairLogFiltration L 256 s] (A C) :=
    hE.inter (clockCount_fibre_measurable init s C)
  have hdisj : Pairwise (fun C D => Disjoint (A C) (A D)) := by
    intro C D hCD
    apply Set.disjoint_left.mpr
    rintro ω ⟨-, hC⟩ ⟨-, hD⟩
    exact hCD (hC.symm.trans hD)
  have hunion : (⋃ C, A C) = E := by
    ext ω
    constructor
    · intro hω
      obtain ⟨C, hC⟩ := Set.mem_iUnion.mp hω
      exact hC.1
    · intro hω
      exact Set.mem_iUnion.mpr ⟨clockCount (virtualLabels init ω s), hω, rfl⟩
  have hcover : E ∩ B ⊆ ⋃ C, A C ∩ B := by
    rintro ω ⟨hω, hb⟩
    exact Set.mem_iUnion.mpr
      ⟨clockCount (virtualLabels init ω s), ⟨hω, rfl⟩, hb⟩
  have hlocal (C : ℕ) :
      law init (A C ∩ B) ≤ ENNReal.ofReal (strongBulkError init.card) *
        law init (A C) := by
    by_cases hne : (A C).Nonempty
    · obtain ⟨ω, hω⟩ := hne
      have hCeq : clockCount (virtualLabels init ω s) = C := hω.2
      have hC : C ≤ init.card := by
        rw [← hCeq]; exact clockCount_le_population init ω s
      have hdensity : 6 * init.card ≤ 25 * C := by
        rw [← hCeq]; exact (hstart ω hω.1).2
      apply (measure_mono ?_).trans
        (strong_observed_bulk_prefix_tail init hm C ℓ s hC hdensity hℓ hcap
          (A C) (hAm C) (fun ω hω => ⟨(hstart ω hω.1).1, hω.2⟩))
      rintro ω ⟨ha, hspan, hbelow⟩
      have haeq : clockCount (virtualLabels init ω s) = C := ha.2
      exact ⟨ha, hspan, by rw [← haeq]; exact hbelow⟩
    · have hempty : A C = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
      simp only [hempty, Set.empty_inter, measure_empty, mul_zero, le_refl]
  calc
    law init (E ∩ B) ≤ law init (⋃ C, A C ∩ B) := measure_mono hcover
    _ ≤ ∑' C, law init (A C ∩ B) := measure_iUnion_le _
    _ ≤ ∑' C, ENNReal.ofReal (strongBulkError init.card) * law init (A C) :=
      ENNReal.tsum_le_tsum hlocal
    _ = ENNReal.ofReal (strongBulkError init.card) * ∑' C, law init (A C) := by
      rw [ENNReal.tsum_mul_left]
    _ = ENNReal.ofReal (strongBulkError init.card) * law init E := by
      rw [← measure_iUnion hdisj
        (fun C => ((pairLogFiltration L 256).le s) _ (hAm C)), hunion]

theorem strong_observed_time_tail (init : Cfg L 256)
    (hm : 64 ≤ init.card) (ℓ : ℕ)
    (hℓ : 1 ≤ ℓ) (hcap : ℓ ≤ 256 * (L + 1))
    (T : Ω L 256 → WithTop ℕ) (E : Set (Ω L 256))
    (hprefix : ∀ s : ℕ, MeasurableSet[pairLogFiltration L 256 s]
      (E ∩ {ω | T ω = (s : WithTop ℕ)}))
    (hstart : ∀ s : ℕ, ∀ ω ∈ E, T ω = (s : WithTop ℕ) →
      DensePositiveStart init ℓ ω s) :
    law init (E ∩ observedBulkFailure init ℓ T) ≤
      ENNReal.ofReal (strongBulkError init.card) * law init E := by
  let A : ℕ → Set (Ω L 256) :=
    fun s => E ∩ {ω | T ω = (s : WithTop ℕ)}
  let B : ℕ → Set (Ω L 256) :=
    fun s => randomCountPassageFailure init ℓ s
      (PhaseThreeModel.Numeric.firstHitHorizon init.card)
  have hdisj : Pairwise (fun s u => Disjoint (A s) (A u)) := by
    intro s u hsu
    apply Set.disjoint_left.mpr
    rintro ω ⟨-, hs⟩ ⟨-, hu⟩
    exact hsu (WithTop.coe_injective (hs.symm.trans hu))
  have hcover : E ∩ observedBulkFailure init ℓ T ⊆ ⋃ s, A s ∩ B s := by
    rintro ω ⟨hω, s, hs, hb⟩
    exact Set.mem_iUnion.mpr ⟨s, ⟨hω, hs⟩, hb⟩
  have hmass : (∑' s, law init (A s)) ≤ law init E := by
    rw [← measure_iUnion hdisj
      (fun s => ((pairLogFiltration L 256).le s) _ (hprefix s))]
    apply measure_mono
    intro ω hω
    obtain ⟨s, hs⟩ := Set.mem_iUnion.mp hω
    exact hs.1
  have hlocal (s : ℕ) :
      law init (A s ∩ B s) ≤ ENNReal.ofReal (strongBulkError init.card) *
        law init (A s) :=
    strong_random_count_prefix_tail init hm ℓ s hℓ hcap (A s) (hprefix s)
      (fun ω hω => hstart s ω hω.1 hω.2)
  calc
    law init (E ∩ observedBulkFailure init ℓ T) ≤
        law init (⋃ s, A s ∩ B s) := measure_mono hcover
    _ ≤ ∑' s, law init (A s ∩ B s) := measure_iUnion_le _
    _ ≤ ∑' s, ENNReal.ofReal (strongBulkError init.card) * law init (A s) :=
      ENNReal.tsum_le_tsum hlocal
    _ = ENNReal.ofReal (strongBulkError init.card) * ∑' s, law init (A s) := by
      rw [ENNReal.tsum_mul_left]
    _ ≤ ENNReal.ofReal (strongBulkError init.card) * law init E :=
      mul_le_mul_left' hmass _

theorem strong_bulk_family_calibration {m : ℕ}
    (hm : populationThreshold ≤ m) :
    64 ≤ m ∧
      (clockCap m : ℝ≥0∞) * ENNReal.ofReal (strongBulkError m) ≤
        ENNReal.ofReal (1 / (2 * (m : ℝ) ^ 10)) := by
  have hdensity : (6 / 25 : ℝ) * (m : ℝ) ≤ (m : ℝ) := by
    nlinarith [(show (0 : ℝ) ≤ m by positivity)]
  obtain ⟨hmp, hx, -, -, -, -, -, -, -, hcap, -⟩ :=
    numeric_calibration_core hm hdensity le_rfl
  have hmR : (64 : ℝ) ≤ m := by
    have hlogle := Real.log_le_sub_one_of_pos hmp
    linarith
  have hmone : (1 : ℝ) ≤ m := by linarith
  have hpower := (new_power_calibration hmp hx).2.2.2
  have hcapquarter : 2 * (clockCap m : ℝ) ≤ (m : ℝ) ^ (1 / 4 : ℝ) := by
    calc
      _ ≤ 20000 * Real.log (m : ℝ) := by linarith only [hcap, hx]
      _ ≤ (m : ℝ) ^ (1 / 100 : ℝ) := hpower
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hmone (by norm_num)
  have hproduct :
      (m : ℝ) ^ (1 / 4 : ℝ) * strongBulkError m = 1 / (m : ℝ) ^ 10 := by
    unfold strongBulkError
    calc
      _ = (m : ℝ) ^ (-10 : ℝ) := by
        rw [← Real.rpow_add hmp]
        congr 1
        ring
      _ = _ := by
        rw [Real.rpow_neg hmp.le]
        first | rw [Real.rpow_ofNat, one_div] | simp [one_div]
  refine ⟨by exact_mod_cast hmR, ?_⟩
  calc
    _ = ENNReal.ofReal ((clockCap m : ℝ) * strongBulkError m) := by
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (((m : ℝ) ^ (1 / 4 : ℝ) / 2) * strongBulkError m) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
        (by linarith only [hcapquarter]) (Real.rpow_nonneg hmp.le _))
    _ = _ := by
      congr 1
      calc
        _ = ((m : ℝ) ^ (1 / 4 : ℝ) * strongBulkError m) / 2 := by ring
        _ = (1 / (m : ℝ) ^ 10) / 2 := by rw [hproduct]
        _ = _ := by ring

/-- The complete strengthened H* family, with its observed prefix mass.
This is the same failure event and horizon as the existing P3a family. -/
theorem firstDense_bulk_family_shape_tail {n : ℕ} (init : InputCfg n)
    (hcard : init.card = n) (hn : populationThreshold ≤ n)
    (s : ℕ) (E : Set (InputLog n))
    (hE : MeasurableSet[pairLogFiltration _ _ s] E) :
    law init (E ∩ bulkFamilyFailure init (Finset.Icc 1 (clockCap n))
      (fun ell => firstDenseTime init s ell)) ≤
        ENNReal.ofReal (1 / (2 * (n : ℝ) ^ 10)) * law init E := by
  obtain ⟨hnlarge, hcal⟩ := strong_bulk_family_calibration hn
  have hm : 64 ≤ init.card := by omega
  have hlocal (ell : ℕ) (hell : ell ∈ Finset.Icc 1 (clockCap n)) :
      law init (E ∩ observedBulkFailure init ell (firstDenseTime init s ell)) ≤
        ENNReal.ofReal (strongBulkError init.card) * law init E := by
    obtain ⟨hpos, htop⟩ := Finset.mem_Icc.mp hell
    apply strong_observed_time_tail init hm ell hpos
      (by simpa only [clockCap, clockHours] using htop)
      (firstDenseTime init s ell) E
    · intro u
      exact firstDenseTime_prefix_fibre_measurable init s ell u E hE
    · intro u ω _ hu
      exact (firstDenseTime_finite_state init s ell u ω hu).2
  have ht := finite_union_prefix_bound (law init) E
    (fun ell => observedBulkFailure init ell (firstDenseTime init s ell))
    (Finset.Icc 1 (clockCap n))
    (ENNReal.ofReal (strongBulkError init.card) * law init E) hlocal
  change law init (E ∩ bulkFamilyFailure init (Finset.Icc 1 (clockCap n))
      (fun ell => firstDenseTime init s ell)) ≤ _ at ht
  rw [Nat.card_Icc, Nat.add_sub_cancel, hcard, ← mul_assoc] at ht
  exact ht.trans (mul_le_mul_right' hcal _)

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockBulkShapeBudget

end
