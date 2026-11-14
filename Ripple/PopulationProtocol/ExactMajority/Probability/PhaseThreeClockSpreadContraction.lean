-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockSpreadContraction.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockHalfPassage
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockPotentialTail

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockSpreadContraction

open TimeTheorem PairLog PairLogAuxiliary PhaseThreeScalar
open PhaseThreeClockVirtual PhaseThreeClockGatedLaw PhaseThreeClockGatedLevelOne
open PhaseThreeClockProbabilityFloors PhaseThreeClockFirstPositive
open PhaseThreeClockNextFrontBirth PhaseThreeClockHalfPassage
open PhaseThreeClockStoppedPassage PhaseThreeClockPrefixTails PhaseThreeClockPotentialTail

variable {L : ℕ}

def spreadStart (init : Cfg L 256) (C ell s : ℕ) : Set (Ω L 256) :=
  {ω | HomogeneousStart init ω s ∧ clockCount (virtualLabels init ω s) = C ∧
    halfCount C ≤ frontCount (virtualLabels init ω s) ell}

open Classical in
def spreadPotential (init : Cfg L 256) (C ell s t : ℕ) : Ω L 256 → ℝ :=
  (spreadStart init C ell s).indicator (fun ω =>
    ((C : ℝ) - (frontCount (virtualLabels init ω (s + t)) ell : ℝ)) / C)

open Classical in
def spreadLoss (init : Cfg L 256) (C ell s t : ℕ) : Ω L 256 → ℝ :=
  (spreadStart init C ell s).indicator (fun _ => (1 : ℝ) / C)

theorem spreadStart_measurable (init : Cfg L 256) (C ell s : ℕ) :
    MeasurableSet[pairLogFiltration L 256 s] (spreadStart init C ell s) := by
  exact (measurable_virtualLabels init s)
    (Set.to_countable {f : Fin init.card → AgentState L 256 |
      ((∀ i, (f i).phase.val = 3) ∧
      (∀ i, nonMainCarrierSmallBiasZeroAgent (f i))) ∧
      clockCount f = C ∧ halfCount C ≤ frontCount f ell}).measurableSet

theorem spreadPotential_measurable (init : Cfg L 256) (C ell s t : ℕ) :
    StronglyMeasurable[shiftedFiltration (pairLogFiltration L 256) s t]
      (spreadPotential init C ell s t) := by
  have hs := (measurable_aux_potential init virtualRule
    (fun f => ((C : ℝ) - (frontCount f ell : ℝ)) / C) (s + t)).stronglyMeasurable
  exact hs.indicator (((pairLogFiltration L 256).mono (by omega : s ≤ s + t)) _
    (spreadStart_measurable init C ell s))

theorem spreadLoss_measurable (init : Cfg L 256) (C ell s t : ℕ) :
    StronglyMeasurable[shiftedFiltration (pairLogFiltration L 256) s t]
      (spreadLoss init C ell s t) :=
  stronglyMeasurable_const.indicator
    (((pairLogFiltration L 256).mono (by omega : s ≤ s + t)) _
      (spreadStart_measurable init C ell s))

theorem spread_current (init : Cfg L 256) (C ell s t : ℕ)
    (ω : Ω L 256) (hω : ω ∈ spreadStart init C ell s) :
    HomogeneousStart init ω (s + t) ∧
      clockCount (virtualLabels init ω (s + t)) = C ∧
      halfCount C ≤ frontCount (virtualLabels init ω (s + t)) ell := by
  refine ⟨homogeneousStart_of_time init ω s hω.1 (s + t) (by omega), ?_, ?_⟩
  · exact (congrArg Finset.card
      (clockSet_fixed_from_homogeneous init ω s hω.1 (s + t) (by omega))).trans hω.2.1
  · exact hω.2.2.trans (Finset.card_le_card
      (aboveSet_mono_from_homogeneous init ω s hω.1 s (s + t) le_rfl (by omega) ell))

theorem spreadPotential_bounds (init : Cfg L 256) (C ell s t : ℕ)
    (hC : 1 ≤ C) (ω : Ω L 256) :
    0 ≤ spreadPotential init C ell s t ω ∧ spreadPotential init C ell s t ω ≤ 1 := by
  classical
  by_cases hω : ω ∈ spreadStart init C ell s
  · have hc := (spread_current init C ell s t ω hω).2.1
    have hyN : frontCount (virtualLabels init ω (s + t)) ell ≤ C := by
      simpa only [hc] using frontCount_le_clockCount (virtualLabels init ω (s + t)) ell
    have hy : (frontCount (virtualLabels init ω (s + t)) ell : ℝ) ≤ (C : ℝ) := by
      exact_mod_cast hyN
    have hCR : (1 : ℝ) ≤ C := by exact_mod_cast hC
    simp only [spreadPotential, Set.indicator_of_mem hω]
    constructor
    · exact div_nonneg (sub_nonneg.mpr hy) (by positivity)
    · apply (div_le_one (by linarith : (0 : ℝ) < C)).2
      have hz : (0 : ℝ) ≤ frontCount (virtualLabels init ω (s + t)) ell := by positivity
      linarith
  · simp [spreadPotential, hω]

theorem spreadLoss_bounds (init : Cfg L 256) (C ell s t : ℕ)
    (hC : 1 ≤ C) (ω : Ω L 256) :
    0 ≤ spreadLoss init C ell s t ω ∧ spreadLoss init C ell s t ω ≤ 1 := by
  classical
  by_cases hω : ω ∈ spreadStart init C ell s
  · have hCR : (1 : ℝ) ≤ C := by exact_mod_cast hC
    simp only [spreadLoss, Set.indicator_of_mem hω]
    exact ⟨by positivity, (div_le_one (by linarith : (0 : ℝ) < C)).2 hCR⟩
  · simp [spreadLoss, hω]

theorem spreadPotential_step (init : Cfg L 256) (C ell s t : ℕ)
    (hell : 1 ≤ ell) (hcap : ell ≤ 256 * (L + 1)) (ω : Ω L 256) :
    spreadPotential init C ell s (t + 1) ω =
      spreadPotential init C ell s t ω -
        spreadLoss init C ell s t ω * gatedIndicator init ell (s + t) ω := by
  classical
  by_cases hω : ω ∈ spreadStart init C ell s
  · have hs := front_step_of_homogeneous init ω (s + t) ell hell hcap
      (spread_current init C ell s t ω hω).1
    simp only [spreadPotential, spreadLoss, Set.indicator_of_mem hω, Nat.add_assoc]
    simp only [Nat.add_assoc] at hs
    rw [hs]
    ring
  · simp [spreadPotential, spreadLoss, hω]

theorem remaining_epidemic_floor (m C X : ℝ)
    (hm : 2 ≤ m) (hdensity : 6 * m ≤ 25 * C)
    (hhalf : C ≤ 2 * X) (hX : X ≤ C) :
    (C - X) / (5 * m) ≤ 2 * X * (C - X) / (m * (m - 1)) := by
  have hroom : m - 1 ≤ 10 * X := by linarith
  have hp := mul_le_mul_of_nonneg_left hroom
    (mul_nonneg (sub_nonneg.mpr hX) (show 0 ≤ m by linarith))
  apply (div_le_div_iff₀ (by positivity : 0 < 5 * m)
    (mul_pos (by linarith : 0 < m) (by linarith : 0 < m - 1))).2
  nlinarith only [hp]

theorem spread_conditional_drift (init : Cfg L 256)
    (hm : 2 ≤ init.card) (C ell s : ℕ) (hC : 1 ≤ C)
    (hdensity : 6 * init.card ≤ 25 * C)
    (hell : 1 ≤ ell) (hcap : ell ≤ 256 * (L + 1)) :
    ∀ t, (law init)[spreadPotential init C ell s (t + 1) |
        shiftedFiltration (pairLogFiltration L 256) s t] ≤ᵐ[law init]
      fun ω => (1 - 1 / (5 * (init.card : ℝ))) * spreadPotential init C ell s t ω := by
  classical
  let ℱ := shiftedFiltration (pairLogFiltration L 256) s
  let I : ℕ → Ω L 256 → ℝ := fun t => gatedIndicator init ell (s + t)
  have hI : ∀ t, StronglyMeasurable[ℱ (t + 1)] (I t) := by
    intro t
    simpa only [ℱ, I, shiftedFiltration_apply, Nat.add_assoc, gatedIndicator] using
      stronglyMeasurable_aux_pair_indicator init virtualRule (GatedTick ell) (s + t)
  apply affine_conditional_drift
    (spreadPotential_measurable init C ell s)
    (fun t => ae_of_all _ (spreadPotential_bounds init C ell s t hC))
    (spreadLoss_measurable init C ell s)
    (fun t => ae_of_all _ (spreadLoss_bounds init C ell s t hC)) hI
    (fun t => ae_of_all _ (gatedIndicator_zero_one init ell (s + t)))
    (fun t => ae_of_all _ fun ω => (spreadPotential_step init C ell s t hell hcap ω).le)
  intro t
  have he : (law init)[I t | ℱ t] =ᵐ[law init]
      fun ω => ((goodPairs (GatedTick ell) (virtualLabels init ω (s + t))).card : ℝ) /
        ((init.card : ℝ) * ((init.card : ℝ) - 1)) := by
    change (law init)[fun ω => gatedIndicator init ell (s + t) ω |
      pairLogFiltration L 256 (s + t)] =ᵐ[law init] _
    simpa only [gatedIndicator] using gatedTick_conditional_law init hm ell (s + t)
  filter_upwards [he] with ω heω
  by_cases hω : ω ∈ spreadStart init C ell s
  · have hc := spread_current init C ell s t ω hω
    let X := frontCount (virtualLabels init ω (s + t)) ell
    have hmR : (2 : ℝ) ≤ init.card := by exact_mod_cast hm
    have hdR : 6 * (init.card : ℝ) ≤ 25 * (C : ℝ) := by exact_mod_cast hdensity
    have hXC : X ≤ C := by
      simpa only [hc.2.1] using frontCount_le_clockCount (virtualLabels init ω (s + t)) ell
    have hhalf : (C : ℝ) ≤ 2 * (X : ℝ) := by
      exact_mod_cast (halfCount_bounds C).1.trans (Nat.mul_le_mul_left 2 hc.2.2)
    have hfloor := remaining_epidemic_floor (init.card : ℝ) (C : ℝ) (X : ℝ)
      hmR hdR hhalf (by exact_mod_cast hXC)
    have hpairs := epidemic_le_gated_pairs (virtualLabels init ω (s + t)) ell hell
    rw [hc.2.1] at hpairs
    have hpairsR : 2 * (X : ℝ) * ((C : ℝ) - X) ≤
        ((goodPairs (GatedTick ell) (virtualLabels init ω (s + t))).card : ℝ) := by
      have hpcast : ((2 * X * (C - X) : ℕ) : ℝ) ≤
          ((goodPairs (GatedTick ell) (virtualLabels init ω (s + t))).card : ℝ) := by
        exact_mod_cast hpairs
      simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub hXC] using hpcast
    have hrate := hfloor.trans (div_le_div_of_nonneg_right hpairsR
      (show 0 ≤ (init.card : ℝ) * ((init.card : ℝ) - 1) from
        mul_nonneg (Nat.cast_nonneg _) (by linarith [hmR])))
    have hm := mul_le_mul_of_nonneg_left hrate (show 0 ≤ (1 : ℝ) / C by positivity)
    rw [heω]
    simp only [spreadPotential, spreadLoss, Set.indicator_of_mem hω]
    change (1 / (5 * (init.card : ℝ))) * (((C : ℝ) - X) / C) ≤ _
    convert hm using 1 <;> ring
  · simp only [spreadPotential, spreadLoss, Set.indicator_of_notMem hω, mul_zero, zero_mul, le_refl]

theorem spread_contraction_nonneg (m : ℕ) (hm : 1 ≤ m) :
    (0 : ℝ) ≤ 1 - 1 / (5 * (m : ℝ)) := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hfrac : (1 : ℝ) / (5 * (m : ℝ)) ≤ 1 := by
    apply (div_le_one (by positivity : 0 < 5 * (m : ℝ))).2
    linarith
  linarith

theorem spread_contraction_pow (m N : ℕ) (hm : 1 ≤ m) :
    (1 - 1 / (5 * (m : ℝ))) ^ N ≤ Real.exp (-(N : ℝ) / (5 * (m : ℝ))) := by
  have hb : 1 - 1 / (5 * (m : ℝ)) ≤ Real.exp (-(1 / (5 * (m : ℝ)))) := by
    simpa only [sub_eq_add_neg, add_comm] using Real.add_one_le_exp (-(1 / (5 * (m : ℝ))))
  calc
    _ ≤ (Real.exp (-(1 / (5 * (m : ℝ))))) ^ N :=
      pow_le_pow_left₀ (spread_contraction_nonneg m hm) hb N
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring

theorem spread_coefficient_calibration (m C N : ℕ) (hm : 1 ≤ m) (hCm : C ≤ m)
    (hN : 60 * (m : ℝ) * Real.log (m : ℝ) ≤ (N : ℝ)) :
    (C : ℝ) * (1 - 1 / (5 * (m : ℝ))) ^ N ≤ 1 / (m : ℝ) ^ 11 := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmp : (0 : ℝ) < m := by positivity
  have hfrac : 12 * Real.log (m : ℝ) ≤ (N : ℝ) / (5 * (m : ℝ)) := by
    apply (le_div_iff₀ (by positivity : 0 < 5 * (m : ℝ))).2
    nlinarith only [hN]
  have he : Real.exp (12 * Real.log (m : ℝ)) = (m : ℝ) ^ 12 := by
    change Real.exp ((12 : ℕ) * Real.log (m : ℝ)) = _
    rw [Real.exp_nat_mul, Real.exp_log hmp]
  have hl : (m : ℝ) * Real.exp (-(12 * Real.log (m : ℝ))) = 1 / (m : ℝ) ^ 11 := by
    rw [Real.exp_neg, he]
    field_simp [ne_of_gt hmp] <;> ring
  calc
    _ ≤ (C : ℝ) * Real.exp (-(N : ℝ) / (5 * (m : ℝ))) :=
      mul_le_mul_of_nonneg_left (spread_contraction_pow m N hm) (by positivity)
    _ ≤ (m : ℝ) * Real.exp (-(N : ℝ) / (5 * (m : ℝ))) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hCm) (Real.exp_nonneg _)
    _ ≤ (m : ℝ) * Real.exp (-(12 * Real.log (m : ℝ))) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by rw [neg_div]; linarith)) hmp.le
    _ = _ := hl

theorem spread_prefix_tail (init : Cfg L 256) (hm : 2 ≤ init.card)
    (C ell s N : ℕ) (hC : 1 ≤ C) (hCm : C ≤ init.card)
    (hdensity : 6 * init.card ≤ 25 * C)
    (hell : 1 ≤ ell) (hcap : ell ≤ 256 * (L + 1))
    (hN : 60 * (init.card : ℝ) * Real.log (init.card : ℝ) ≤ (N : ℝ))
    (E : Set (Ω L 256)) (hE : MeasurableSet[pairLogFiltration L 256 s] E)
    (hstart : E ⊆ spreadStart init C ell s) :
    law init (E ∩ {ω | frontCount (virtualLabels init ω (s + N)) ell < C}) ≤
      ENNReal.ofReal (1 / (init.card : ℝ) ^ 11) * law init E := by
  let B := E ∩ {ω | frontCount (virtualLabels init ω (s + N)) ell < C}
  have hCR : (0 : ℝ) < C := by exact_mod_cast (show 0 < C by omega)
  have hdom : ∀ ω ∈ B, 1 ≤ (C : ℝ) * spreadPotential init C ell s N ω := by
    rintro ω ⟨he, hb⟩
    have hb' : frontCount (virtualLabels init ω (s + N)) ell < C := hb
    have hgap : 1 ≤ (C : ℝ) - frontCount (virtualLabels init ω (s + N)) ell := by
      have h : frontCount (virtualLabels init ω (s + N)) ell + 1 ≤ C := by omega
      have hR : (frontCount (virtualLabels init ω (s + N)) ell : ℝ) + 1 ≤ C := by
        exact_mod_cast h
      linarith
    simp only [spreadPotential, Set.indicator_of_mem (hstart he)]
    have hid : (C : ℝ) * (((C : ℝ) -
        frontCount (virtualLabels init ω (s + N)) ell) / C) =
        (C : ℝ) - frontCount (virtualLabels init ω (s + N)) ell := by field_simp [ne_of_gt hCR]
    rw [hid]
    exact hgap
  have ht := prefix_potential_tail_ennreal
    (spreadPotential_measurable init C ell s)
    (fun t => ae_of_all _ (spreadPotential_bounds init C ell s t hC))
    (spread_contraction_nonneg init.card (by omega))
    (spread_conditional_drift init hm C ell s hC hdensity hell hcap)
    E (by simpa only [shiftedFiltration_apply, Nat.add_zero] using hE)
    N B (C : ℝ) (by positivity) hdom
  have hcal := ENNReal.ofReal_le_ofReal
    (spread_coefficient_calibration init.card C N (by omega) hCm hN)
  have ht' : law init B ≤ ENNReal.ofReal
      ((C : ℝ) * (1 - 1 / (5 * (init.card : ℝ))) ^ N) * law init E := by
    simpa only [B, ← Set.inter_assoc, Set.inter_self] using ht
  exact ht'.trans (mul_le_mul_right' hcal _)

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockSpreadContraction

end
