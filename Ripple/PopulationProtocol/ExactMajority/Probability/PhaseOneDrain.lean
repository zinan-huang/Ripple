/-
N11b support: Phase-1 drain.

This file supplies the entry/endpoint specification,
deterministic partner and cancellation lemmas, residual-clock kernel
bounds, scalar calibrations, and the recorded-past integration interface.

It does not establish the three protocol averaging tails or the
joint pair-log conditional producer. The missing theorem type is recorded
in a comment at the end.
-/

import Ripple.PopulationProtocol.ExactMajority.Probability.ThresholdEpidemic
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase1FarPhiSharp
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase1ClockDepthStopped
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase1GapFloorEntryClosure

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped BigOperators ENNReal NNReal MeasureTheory ProbabilityTheory

namespace Ripple.PopulationProtocol.ExactMajority.PhaseOneDrain

open TimeTheorem

variable {L K : ℕ}

/-! ## The observed entry and the required endpoint -/

def PhaseOneMass (c : Cfg L K) : ℕ :=
  (c.map (fun a => (AveragingRate.biasZ a).natAbs)).sum

/-- The observed §2 profile and the small-gap condition of §3.
The counter reserve is a lower bound on the actual residual counter. -/
def PhaseOneDrainEntry (n : ℕ) (g : ℤ) (c : Cfg L K) : Prop :=
  PhaseOnlyWindows.Phase1Win (L := L) (K := K) n c ∧
  (∀ a ∈ c,
    a.role = .main ∨ a.role = .clock ∨ a.role = .reserve) ∧
  99 * n ≤ 200 * RoleSplitConcentration.mainCount c ∧
  200 * RoleSplitConcentration.mainCount c ≤ 101 * n ∧
  97 * n ≤ 400 * RoleSplitConcentration.clockCount c ∧
  97 * n ≤ 400 * RoleSplitConcentration.reserveCount c ∧
  (∀ a ∈ c, a.role = .clock →
    30 * (L + 1) ≤ a.counter.val) ∧
  Phase1FarPhi.NonMainNeutral c ∧
  AveragingRate.centredBiasSum c = g ∧
  40 * g.natAbs ≤ RoleSplitConcentration.mainCount c

/-- At safe biases, PhaseOneMass is precisely the number of biased Mains. -/
def PhaseOneDrained (c : Cfg L K) : Prop :=
  (∀ a ∈ c, a.phase.val = 1) ∧
  (∀ a ∈ c, a.smallBias.val ∈ ({2, 3, 4} : Finset ℕ)) ∧
  100 * PhaseOneMass c ≤ 3 * RoleSplitConcentration.mainCount c

theorem safeSmall_iff_integerBias (a : AgentState L K) :
    a.smallBias.val ∈ ({2, 3, 4} : Finset ℕ) ↔
      a.smallBiasInt ∈ ({-1, 0, 1} : Finset ℤ) := by
  simp only [Finset.mem_insert, Finset.mem_singleton,
    AgentState.smallBiasInt]
  omega

theorem PhaseOneDrained.integer_biases
    {c : Cfg L K} (h : PhaseOneDrained c) :
    ∀ a ∈ c, a.smallBiasInt ∈ ({-1, 0, 1} : Finset ℤ) := by
  intro a ha
  exact (safeSmall_iff_integerBias a).mp (h.2.1 a ha)

theorem PhaseOneDrainEntry.gap_floor_entry
    {n : ℕ} {g : ℤ} {c : Cfg L K}
    (h : PhaseOneDrainEntry n g c) :
    Phase1PartnerFloor.Phase1GapFloorEntry (L := L) (K := K)
      n g.natAbs (RoleSplitConcentration.mainCount c) c := by
  rcases h with ⟨hwin, _, _, _, _, _, _, _, hsum, _⟩
  refine ⟨hwin, ?_, le_rfl⟩
  simpa only [hsum, Int.natCast_natAbs] using (le_refl (|g| : ℤ))

theorem PhaseOneDrainEntry.clock_depth_good
    {n : ℕ} {g : ℤ} {c : Cfg L K}
    (h : PhaseOneDrainEntry n g c) :
    Phase1ClockDepthStopped.Good (L := L) (K := K)
      n g.natAbs (RoleSplitConcentration.mainCount c) c := by
  have hgap := h.gap_floor_entry
  rcases h with ⟨_, _, _, _, _, _, hcounter, _, _, _⟩
  refine ⟨hgap, ?_⟩
  intro a ha hclock
  have hreserve := hcounter a ha hclock
  omega

theorem PhaseOneDrainEntry.role_split_good
    {n : ℕ} {g : ℤ} {c : Cfg L K}
    (h : PhaseOneDrainEntry n g c) :
    RoleSplitConcentration.RoleSplitGood
      (L := L) (K := K) (1 / 25 : ℝ) n c := by
  rcases h with
    ⟨_, hfinal, hmainLower, hmainUpper, hclockLower, hreserveLower,
      _, _, _, _⟩
  have hnoMcr : RoleSplitConcentration.roleMCRCount c = 0 := by
    unfold RoleSplitConcentration.roleMCRCount
    rw [Multiset.countP_eq_zero]
    intro a ha
    rcases hfinal a ha with hm | hc | hr
    · simp [hm]
    · simp [hc]
    · simp [hr]
  have hmainLowerReal :
      (99 : ℝ) * (n : ℝ) ≤
        200 * (RoleSplitConcentration.mainCount c : ℝ) := by
    exact_mod_cast hmainLower
  have hmainUpperReal :
      200 * (RoleSplitConcentration.mainCount c : ℝ) ≤
        101 * (n : ℝ) := by exact_mod_cast hmainUpper
  have hclockLowerReal :
      (97 : ℝ) * (n : ℝ) ≤
        400 * (RoleSplitConcentration.clockCount c : ℝ) := by
    exact_mod_cast hclockLower
  have hreserveLowerReal :
      (97 : ℝ) * (n : ℝ) ≤
        400 * (RoleSplitConcentration.reserveCount c : ℝ) := by
    exact_mod_cast hreserveLower
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  refine ⟨hnoMcr, ?_, ?_, ?_, ?_⟩ <;> nlinarith

theorem PhaseOneDrained.to_phase1Drained
    {n : ℕ} {c : Cfg L K} (hcard : c.card = n)
    (h : PhaseOneDrained c) :
    Phase1GapFloorEntryClosure.Phase1Drained (L := L) (K := K) n c := by
  refine ⟨⟨hcard, h.1⟩, ?_⟩
  apply (Phase1FarPhi.farPhiN_eq_zero_iff_mainBiasSafe c).mpr
  intro a ha _
  exact h.2.1 a ha

theorem PhaseOneMass_eq_biasedMainCount_of_safe
    (c : Cfg L K)
    (hsafe : ∀ a ∈ c,
      a.smallBias.val ∈ ({2, 3, 4} : Finset ℕ)) :
    PhaseOneMass c =
      c.countP (fun a => a.role = .main ∧ a.smallBias.val ≠ 3) := by
  induction c using Multiset.induction_on with
  | empty => simp [PhaseOneMass]
  | cons a c ih =>
    have ha := hsafe a (Multiset.mem_cons_self a c)
    have ht := ih (fun b hb => hsafe b (Multiset.mem_cons_of_mem hb))
    have hhead : (AveragingRate.biasZ a).natAbs =
        if a.role = .main ∧ a.smallBias.val ≠ 3 then 1 else 0 := by
      by_cases hm : a.role = .main
      · simp only [Finset.mem_insert, Finset.mem_singleton] at ha
        rcases ha with ha | ha | ha <;>
          simp [AveragingRate.biasZ, hm, ha]
      · simp [AveragingRate.biasZ, hm]
    have hmass : PhaseOneMass (a ::ₘ c) =
        (AveragingRate.biasZ a).natAbs + PhaseOneMass c := by
      simp only [PhaseOneMass, Multiset.map_cons, Multiset.sum_cons]
    rw [hmass, ht, Multiset.countP_cons, hhead]
    split_ifs <;> omega

theorem PhaseOneDrained.biased_main_count_le
    {c : Cfg L K} (h : PhaseOneDrained c) :
    100 * c.countP (fun a => a.role = .main ∧ a.smallBias.val ≠ 3) ≤
      3 * RoleSplitConcentration.mainCount c := by
  rw [← PhaseOneMass_eq_biasedMainCount_of_safe c h.2.1]
  exact h.2.2

/-- The literal three-stage raw-interaction deadline in PHASE02 (26). -/
noncomputable def weakHorizon (n : ℕ) : ℕ :=
  816000 * n +
    Nat.ceil ((27 / 2 : ℝ) * (n : ℝ) * Real.log (n : ℝ))

/-- Extract the logarithmic bound without reducing the population threshold. -/
theorem population_calibration {n : ℕ}
    (hn : TimeTheorem.timePopulationThreshold ≤ n) :
    0 < (n : ℝ) ∧ 2000000 ≤ Real.log (n : ℝ) := by
  have hbase : PhaseThreeModel.Numeric.populationThreshold ≤ n :=
    (TimeTheorem.time_population_bounds hn).1
  have hdensity : (6 / 25 : ℝ) * n ≤ (n : ℝ) := by
    nlinarith only [show (0 : ℝ) ≤ n from Nat.cast_nonneg n]
  obtain ⟨hnpos, hlog, _⟩ :=
    PhaseThreeModel.Numeric.logarithmic_inputs
      (n := n) (C := n) hbase hdensity le_rfl
  exact ⟨hnpos,
    (by norm_num : (2000000 : ℝ) ≤ 536870912).trans hlog⟩

theorem log_two_le_three_quarters :
    Real.log 2 ≤ (3 / 4 : ℝ) := by
  exact PhaseThreeModel.Numeric.log_two_bounds.2.trans (by norm_num)

/-- PHASE02 (26), including its exact ceiling. -/
theorem weakHorizon_le_log {n : ℕ}
    (hnpos : 0 < (n : ℝ))
    (hlog : 2000000 ≤ Real.log (n : ℝ)) :
    (weakHorizon n : ℝ) ≤ 14 * (n : ℝ) * Real.log (n : ℝ) := by
  have hnone : (1 : ℝ) ≤ n := by
    have he := Real.add_one_le_exp (Real.log (n : ℝ))
    rw [Real.exp_log hnpos] at he
    linarith only [he, hlog]
  have hlognonneg : 0 ≤ Real.log (n : ℝ) := by
    linarith only [hlog]
  have hceil :
      (Nat.ceil ((27 / 2 : ℝ) * (n : ℝ) *
        Real.log (n : ℝ)) : ℝ) ≤
        (27 / 2 : ℝ) * (n : ℝ) * Real.log (n : ℝ) + 1 :=
    (Nat.ceil_lt_add_one (by positivity)).le
  have hprod := mul_le_mul_of_nonneg_left hlog hnpos.le
  simp only [weakHorizon, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  nlinarith only [hceil, hprod, hnone]

/-- The finite certificate below (27); only small fixed exponents reduce. -/
theorem clock_integer_certificate :
    (3 : ℕ) ^ 60 - (2 : ℕ) ^ 95 =
        2777077018084034717522458033 ∧
      (2 : ℕ) ^ 95 < (3 : ℕ) ^ 60 := by
  decide +kernel

theorem clock_log_certificate :
    (35 / 2 : ℝ) * Real.log 2 <
      30 * Real.log (3 / 2 : ℝ) := by
  have hpow : (2 : ℝ) ^ 95 < (3 : ℝ) ^ 60 := by
    exact_mod_cast clock_integer_certificate.2
  have hl :=
    Real.log_lt_log (by positivity : (0 : ℝ) < (2 : ℝ) ^ 95) hpow
  rw [Real.log_pow, Real.log_pow] at hl
  rw [Real.log_div (by norm_num : (3 : ℝ) ≠ 0)
    (by norm_num : (2 : ℝ) ≠ 0)]
  norm_num only [Nat.cast_ofNat] at hl
  nlinarith only [hl]

theorem clock_hour_log_lower (n : ℕ) :
    Real.log (n : ℝ) ≤
      (PhaseThreeModel.Numeric.clockHours n : ℝ) * Real.log 2 := by
  have htwo : 0 < Real.log (2 : ℝ) := by
    linarith only [PhaseThreeModel.Numeric.log_two_bounds.1]
  have hindex :
      Real.log (n : ℝ) ≤
        (PhaseThreeModel.Numeric.hourIndex n : ℝ) * Real.log 2 := by
    apply (div_le_iff₀ htwo).mp
    rw [PhaseThreeModel.Numeric.hourIndex_eq_real_ceiling]
    exact Nat.le_ceil _
  simp only [PhaseThreeModel.Numeric.clockHours,
    Nat.cast_add, Nat.cast_one]
  nlinarith only [hindex, htwo.le]

/-- The real MGF calculation for the residual 30H budget in (27). -/
theorem clock_tail_real (n T : ℕ)
    (hnpos : 0 < (n : ℝ))
    (hT : (T : ℝ) ≤ 14 * (n : ℝ) * Real.log (n : ℝ)) :
    (1 + 1 / (n : ℝ)) ^ T * (n : ℝ) /
        Real.exp
          (Real.log (3 / 2 : ℝ) *
            ((30 * PhaseThreeModel.Numeric.clockHours n : ℕ) : ℝ)) ≤
      Real.rpow (n : ℝ) (-(5 / 2 : ℝ)) := by
  have hmgf :
      (1 + 1 / (n : ℝ)) ^ T ≤ Real.exp ((T : ℝ) / (n : ℝ)) := by
    calc
      (1 + 1 / (n : ℝ)) ^ T ≤
          (Real.exp (1 / (n : ℝ))) ^ T :=
        pow_le_pow_left₀ (by positivity)
          (by simpa only [add_comm] using
            Real.add_one_le_exp (1 / (n : ℝ))) T
      _ = Real.exp ((T : ℝ) / (n : ℝ)) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
  have hmean :
      (T : ℝ) / (n : ℝ) ≤ 14 * Real.log (n : ℝ) := by
    apply (div_le_iff₀ hnpos).2
    nlinarith only [hT]
  have hhour := clock_hour_log_lower n
  have hscaled :=
    mul_le_mul_of_nonneg_left clock_log_certificate.le
      (Nat.cast_nonneg (PhaseThreeModel.Numeric.clockHours n) : (0 : ℝ) ≤ _)
  have hcounter :
      (35 / 2 : ℝ) * Real.log (n : ℝ) ≤
        Real.log (3 / 2 : ℝ) *
          ((30 * PhaseThreeModel.Numeric.clockHours n : ℕ) : ℝ) := by
    simp only [Nat.cast_mul, Nat.cast_ofNat]
    nlinarith only [hhour, hscaled]
  calc
    (1 + 1 / (n : ℝ)) ^ T * (n : ℝ) /
        Real.exp
          (Real.log (3 / 2 : ℝ) *
            ((30 * PhaseThreeModel.Numeric.clockHours n : ℕ) : ℝ)) ≤
        Real.exp ((T : ℝ) / (n : ℝ)) * (n : ℝ) /
          Real.exp
            (Real.log (3 / 2 : ℝ) *
              ((30 * PhaseThreeModel.Numeric.clockHours n : ℕ) : ℝ)) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hmgf hnpos.le)
        (Real.exp_nonneg _)
    _ = Real.exp
        ((T : ℝ) / (n : ℝ) + Real.log (n : ℝ) -
          Real.log (3 / 2 : ℝ) *
            ((30 * PhaseThreeModel.Numeric.clockHours n : ℕ) : ℝ)) := by
      rw [Real.exp_sub, Real.exp_add, Real.exp_log hnpos]
    _ ≤ Real.rpow (n : ℝ) (-(5 / 2 : ℝ)) := by
      change _ ≤ (n : ℝ) ^ (-(5 / 2 : ℝ))
      rw [Real.rpow_def_of_pos hnpos]
      apply Real.exp_le_exp.mpr
      nlinarith only [hmean, hcounter]

theorem counterDepthRate_log_three_halves (n : ℕ)
    (hnpos : 0 < (n : ℝ)) :
    ClockCounterDepthCover.counterDepthRate n (Real.log (3 / 2 : ℝ)) =
      ENNReal.ofReal (1 + 1 / (n : ℝ)) := by
  have hof :
      ENNReal.ofReal (1 + 1 / (n : ℝ)) =
        1 + 1 / (n : ℝ≥0∞) := by
    rw [ENNReal.ofReal_add (by norm_num) (by positivity),
      ENNReal.ofReal_one, ENNReal.ofReal_div_of_pos hnpos,
      ENNReal.ofReal_one, ENNReal.ofReal_natCast]
  rw [hof]
  unfold ClockCounterDepthCover.counterDepthRate
  rw [Real.exp_log (by norm_num : (0 : ℝ) < 3 / 2)]
  norm_num
  rw [show ENNReal.ofReal (1 / 2) = 2⁻¹ by
        rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num)]
        norm_num,
    ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_div]

/-- Scalar calibration of the existing aggregate-depth tail. -/
theorem residual_counterDepthTail_le {n : ℕ}
    (hn : TimeTheorem.timePopulationThreshold ≤ n) :
    ClockCounterDepthCover.counterDepthTail
        n (weakHorizon n) (30 * PhaseThreeModel.Numeric.clockHours n)
        (Real.log (3 / 2 : ℝ)) ≤
      ENNReal.ofReal (Real.rpow (n : ℝ) (-(5 / 2 : ℝ))) := by
  obtain ⟨hnpos, hlog⟩ := population_calibration hn
  clear hn
  have hbase : (0 : ℝ) ≤ 1 + 1 / (n : ℝ) := by positivity
  have ht :
      ClockCounterDepthCover.counterDepthTail
          n (weakHorizon n) (30 * PhaseThreeModel.Numeric.clockHours n)
          (Real.log (3 / 2 : ℝ)) =
        ENNReal.ofReal
          ((1 + 1 / (n : ℝ)) ^ weakHorizon n * (n : ℝ) /
            Real.exp
              (Real.log (3 / 2 : ℝ) *
                ((30 * PhaseThreeModel.Numeric.clockHours n : ℕ) : ℝ))) := by
    unfold ClockCounterDepthCover.counterDepthTail
      ClockCounterDepthCover.counterDepthThreshold
    rw [counterDepthRate_log_three_halves n hnpos,
      ← ENNReal.ofReal_pow hbase,
      ← ENNReal.ofReal_natCast n,
      ← ENNReal.ofReal_mul (pow_nonneg hbase (weakHorizon n)),
      ← ENNReal.ofReal_div_of_pos (Real.exp_pos _)]
  rw [ht]
  exact ENNReal.ofReal_le_ofReal
    (clock_tail_real n (weakHorizon n) hnpos
      (weakHorizon_le_log hnpos hlog))

/-- Scalar part of (23), with the literal far-drain ceiling. -/
theorem far_decay_calibration {n : ℕ}
    (hnpos : 0 < (n : ℝ)) :
    ((n : ℝ) / 100) *
        Real.exp
          (-((229 : ℝ) / (1000 * (n : ℝ))) *
            (Nat.ceil ((27 / 2 : ℝ) * (n : ℝ) *
              Real.log (n : ℝ)) : ℝ)) ≤
      (1 / 100 : ℝ) *
        Real.rpow (n : ℝ) (-(4183 / 2000 : ℝ)) := by
  have hceil :
      (27 / 2 : ℝ) * (n : ℝ) * Real.log (n : ℝ) ≤
        (Nat.ceil ((27 / 2 : ℝ) * (n : ℝ) *
          Real.log (n : ℝ)) : ℝ) := Nat.le_ceil _
  have hrate : 0 ≤ (229 : ℝ) / (1000 * (n : ℝ)) := by positivity
  have hprod := mul_le_mul_of_nonneg_left hceil hrate
  have heq :
      ((229 : ℝ) / (1000 * (n : ℝ))) *
          ((27 / 2 : ℝ) * (n : ℝ) * Real.log (n : ℝ)) =
        (6183 / 2000 : ℝ) * Real.log (n : ℝ) := by
    field_simp [ne_of_gt hnpos]
    <;> ring
  rw [heq] at hprod
  calc
    ((n : ℝ) / 100) *
        Real.exp
          (-((229 : ℝ) / (1000 * (n : ℝ))) *
            (Nat.ceil ((27 / 2 : ℝ) * (n : ℝ) *
              Real.log (n : ℝ)) : ℝ)) ≤
        ((n : ℝ) / 100) *
          Real.exp (-(6183 / 2000 : ℝ) * Real.log (n : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.exp_le_exp.mpr
      nlinarith only [hprod]
    _ = (1 / 100 : ℝ) *
        (Real.exp (Real.log (n : ℝ)) *
          Real.exp (-(6183 / 2000 : ℝ) * Real.log (n : ℝ))) := by
      rw [Real.exp_log hnpos]
      ring
    _ = (1 / 100 : ℝ) *
        Real.exp
          (Real.log (n : ℝ) -
            (6183 / 2000 : ℝ) * Real.log (n : ℝ)) := by
      rw [← Real.exp_add]
      congr 2
      ring
    _ = (1 / 100 : ℝ) *
        Real.rpow (n : ℝ) (-(4183 / 2000 : ℝ)) := by
      change _ = (1 / 100 : ℝ) * (n : ℝ) ^ (-(4183 / 2000 : ℝ))
      rw [Real.rpow_def_of_pos hnpos]
      congr 2
      ring

/-- PHASE02 (28), proved without evaluating at a gigantic population. -/
theorem drain_error_budget {x : ℝ}
    (hx : 0 < x) (hlog : 2000000 ≤ Real.log x) :
    Real.exp (-x / 2) + Real.exp (-x / 4) +
        (1 / 100 : ℝ) * Real.rpow x (-(4183 / 2000 : ℝ)) +
        Real.rpow x (-(5 / 2 : ℝ)) ≤
      1 / x ^ 2 := by
  have hxlarge : 6912 ≤ x := by
    have he := Real.add_one_le_exp (Real.log x)
    rw [Real.exp_log hx] at he
    linarith only [he, hlog]
  have hlognonneg : 0 ≤ Real.log x := by
    linarith only [hlog]
  have hsquare :
      Real.exp ((2 : ℝ) * Real.log x) = x ^ 2 := by
    simpa only [Real.exp_log hx] using (Real.exp_nat_mul (Real.log x) 2)
  have hinvsquare :
      Real.exp (-((2 : ℝ) * Real.log x)) = 1 / x ^ 2 := by
    rw [Real.exp_neg, hsquare, one_div]
  have hden : 4 * x ^ 2 ≤ Real.exp (x / 4) := by
    have hbase : x / 12 ≤ Real.exp (x / 12) := by
      linarith only [Real.add_one_le_exp (x / 12)]
    have hpow :=
      pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ x / 12) hbase 3
    have hpoly : 4 * x ^ 2 ≤ (x / 12) ^ 3 := by
      have h := mul_nonneg (sub_nonneg.mpr hxlarge) (sq_nonneg x)
      nlinarith only [h]
    calc
      4 * x ^ 2 ≤ (x / 12) ^ 3 := hpoly
      _ ≤ Real.exp (x / 12) ^ 3 := hpow
      _ = Real.exp (x / 4) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
  have hquarter :
      Real.exp (-x / 4) ≤ (1 / 4 : ℝ) * (1 / x ^ 2) := by
    calc
      Real.exp (-x / 4) = 1 / Real.exp (x / 4) := by
        rw [show -x / 4 = -(x / 4) by ring, Real.exp_neg, one_div]
      _ ≤ 1 / (4 * x ^ 2) := by
        apply (div_le_div_iff₀ (Real.exp_pos _) (by positivity)).2
        simpa only [one_mul] using hden
      _ = (1 / 4 : ℝ) * (1 / x ^ 2) := by ring
  have hhalf :
      Real.exp (-x / 2) ≤ (1 / 4 : ℝ) * (1 / x ^ 2) := by
    apply (Real.exp_le_exp.mpr
      (show -x / 2 ≤ -x / 4 by linarith only [hx])).trans hquarter
  have hfar :
      Real.rpow x (-(4183 / 2000 : ℝ)) ≤ 1 / x ^ 2 := by
    change x ^ (-(4183 / 2000 : ℝ)) ≤ 1 / x ^ 2
    rw [Real.rpow_def_of_pos hx, ← hinvsquare]
    apply Real.exp_le_exp.mpr
    nlinarith only [hlognonneg]
  have hfour : 4 ≤ Real.exp (Real.log x / 2) := by
    have he := Real.add_one_le_exp (Real.log x / 2)
    linarith only [he, hlog]
  have hclockDen :
      4 * x ^ 2 ≤ Real.exp ((5 / 2 : ℝ) * Real.log x) := by
    calc
      4 * x ^ 2 ≤ Real.exp (Real.log x / 2) * x ^ 2 :=
        mul_le_mul_of_nonneg_right hfour (sq_nonneg x)
      _ = Real.exp (Real.log x / 2) *
          Real.exp ((2 : ℝ) * Real.log x) := by rw [hsquare]
      _ = Real.exp ((5 / 2 : ℝ) * Real.log x) := by
        rw [← Real.exp_add]
        congr 1
        ring
  have hclock :
      Real.rpow x (-(5 / 2 : ℝ)) ≤
        (1 / 4 : ℝ) * (1 / x ^ 2) := by
    calc
      Real.rpow x (-(5 / 2 : ℝ)) =
          1 / Real.exp ((5 / 2 : ℝ) * Real.log x) := by
        change x ^ (-(5 / 2 : ℝ)) = _
        rw [Real.rpow_def_of_pos hx,
          show Real.log x * (-(5 / 2 : ℝ)) =
            -((5 / 2 : ℝ) * Real.log x) by ring,
          Real.exp_neg, one_div]
      _ ≤ 1 / (4 * x ^ 2) := by
        apply (div_le_div_iff₀ (Real.exp_pos _) (by positivity)).2
        simpa only [one_mul] using hclockDen
      _ = (1 / 4 : ℝ) * (1 / x ^ 2) := by ring
  have hfarScaled := mul_le_mul_of_nonneg_left hfar
    (by norm_num : (0 : ℝ) ≤ 1 / 100)
  calc
    Real.exp (-x / 2) + Real.exp (-x / 4) +
        (1 / 100 : ℝ) * Real.rpow x (-(4183 / 2000 : ℝ)) +
        Real.rpow x (-(5 / 2 : ℝ)) ≤
        (1 / 4 : ℝ) * (1 / x ^ 2) +
          (1 / 4 : ℝ) * (1 / x ^ 2) +
          (1 / 100 : ℝ) * (1 / x ^ 2) +
          (1 / 4 : ℝ) * (1 / x ^ 2) :=
      add_le_add
        (add_le_add (add_le_add hhalf hquarter) hfarScaled) hclock
    _ = (19 / 25 : ℝ) * (1 / x ^ 2) := by ring
    _ ≤ 1 / x ^ 2 := by
      nlinarith only [show (0 : ℝ) ≤ 1 / x ^ 2 by positivity]

theorem drain_error_budget_of_population {n : ℕ}
    (hn : TimeTheorem.timePopulationThreshold ≤ n) :
    Real.exp (-(n : ℝ) / 2) + Real.exp (-(n : ℝ) / 4) +
        (1 / 100 : ℝ) *
          Real.rpow (n : ℝ) (-(4183 / 2000 : ℝ)) +
        Real.rpow (n : ℝ) (-(5 / 2 : ℝ)) ≤
      1 / (n : ℝ) ^ 2 := by
  obtain ⟨hnpos, hlog⟩ := population_calibration hn
  exact drain_error_budget hnpos hlog

/-! ## Refined partner census and the sharp local drift -/

theorem refined_low_atom (v : Fin 7) :
    (1 : ℤ) ≤
      2 * (if v.val ≤ 3 then (1 : ℤ) else 0) +
        ((v.val : ℤ) - 3) + (Phase1FarPhi.farPhi v : ℤ) := by
  revert v
  decide +kernel

theorem refined_high_atom (v : Fin 7) :
    (1 : ℤ) ≤
      2 * (if 3 ≤ v.val then (1 : ℤ) else 0) -
        ((v.val : ℤ) - 3) + (Phase1FarPhi.farPhi v : ℤ) := by
  revert v
  decide +kernel

theorem refined_low_count_core (s : Multiset (AgentState L K)) :
    (Multiset.countP
        (fun a : AgentState L K => a.role = Role.main) s : ℤ) ≤
      2 * (Multiset.countP
        (fun a : AgentState L K =>
          a.role = Role.main ∧ a.smallBias.val ≤ 3) s : ℤ) +
      (s.map (fun a => AveragingRate.biasZ a)).sum +
      ((s.map (fun a => Phase1FarPhi.farPhiMainN a)).sum : ℤ) := by
  classical
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.countP_cons, Multiset.countP_cons,
      Multiset.map_cons, Multiset.sum_cons,
      Multiset.map_cons, Multiset.sum_cons]
    by_cases hm : a.role = Role.main
    · have hb : AveragingRate.biasZ a = (a.smallBias.val : ℤ) - 3 := by
        simp [AveragingRate.biasZ, hm]
      have hp : Phase1FarPhi.farPhiMainN a =
          Phase1FarPhi.farPhi a.smallBias := by
        simp [Phase1FarPhi.farPhiMainN, hm]
      rw [if_pos hm, hb, hp]
      have hv := refined_low_atom a.smallBias
      by_cases hl : a.smallBias.val ≤ 3
      · rw [if_pos ⟨hm, hl⟩]
        rw [if_pos hl] at hv
        simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, Nat.cast_ofNat]
        omega
      · rw [if_neg (fun h => hl h.2)]
        rw [if_neg hl] at hv
        simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, Nat.cast_ofNat]
        omega
    · have hb : AveragingRate.biasZ a = 0 := by
        simp [AveragingRate.biasZ, hm]
      have hp : Phase1FarPhi.farPhiMainN a = 0 := by
        simp [Phase1FarPhi.farPhiMainN, hm]
      rw [if_neg hm, if_neg (fun h => hm h.1), hb, hp]
      simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, Nat.cast_ofNat]
      omega

theorem refined_high_count_core (s : Multiset (AgentState L K)) :
    (Multiset.countP
        (fun a : AgentState L K => a.role = Role.main) s : ℤ) ≤
      2 * (Multiset.countP
        (fun a : AgentState L K =>
          a.role = Role.main ∧ 3 ≤ a.smallBias.val) s : ℤ) -
      (s.map (fun a => AveragingRate.biasZ a)).sum +
      ((s.map (fun a => Phase1FarPhi.farPhiMainN a)).sum : ℤ) := by
  classical
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.countP_cons, Multiset.countP_cons,
      Multiset.map_cons, Multiset.sum_cons,
      Multiset.map_cons, Multiset.sum_cons]
    by_cases hm : a.role = Role.main
    · have hb : AveragingRate.biasZ a = (a.smallBias.val : ℤ) - 3 := by
        simp [AveragingRate.biasZ, hm]
      have hp : Phase1FarPhi.farPhiMainN a =
          Phase1FarPhi.farPhi a.smallBias := by
        simp [Phase1FarPhi.farPhiMainN, hm]
      rw [if_pos hm, hb, hp]
      have hv := refined_high_atom a.smallBias
      by_cases hh : 3 ≤ a.smallBias.val
      · rw [if_pos ⟨hm, hh⟩]
        rw [if_pos hh] at hv
        simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, Nat.cast_ofNat]
        omega
      · rw [if_neg (fun h => hh h.2)]
        rw [if_neg hh] at hv
        simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, Nat.cast_ofNat]
        omega
    · have hb : AveragingRate.biasZ a = 0 := by
        simp [AveragingRate.biasZ, hm]
      have hp : Phase1FarPhi.farPhiMainN a = 0 := by
        simp [Phase1FarPhi.farPhiMainN, hm]
      rw [if_neg hm, if_neg (fun h => hm h.1), hb, hp]
      simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, Nat.cast_ofNat]
      omega

theorem refined_low_partner_count
    (c : Config (AgentState L K)) (d : ℕ)
    (hgap : |AveragingRate.centredBiasSum c| ≤ (d : ℤ)) :
    RoleSplitConcentration.mainCount c ≤
      2 * (AveragingRate.lowSet L K).sum c.count +
        d + Phase1FarPhi.farPhiN c := by
  have hcore := refined_low_count_core c
  have hmcNat :
      Multiset.countP
          (fun a : AgentState L K => a.role = Role.main) c =
        RoleSplitConcentration.mainCount c := by
    unfold RoleSplitConcentration.mainCount
    exact Multiset.countP_congr rfl (fun _ _ => rfl)
  have hmc := congrArg (Nat.cast : ℕ → ℤ) hmcNat
  have hpool :
      (AveragingRate.lowSet L K).sum c.count =
        Multiset.countP
          (fun a : AgentState L K =>
            a.role = Role.main ∧ a.smallBias.val ≤ 3) c := by
    convert Phase1PartnerFloor.lowSet_sum_count_eq
      (L := L) (K := K) c using 1 <;>
      apply Multiset.countP_congr rfl <;> intro a _ <;> rfl
  have hs :
      (c.map (fun a => AveragingRate.biasZ a)).sum =
        AveragingRate.centredBiasSum c := rfl
  have hp :
      (c.map (fun a => Phase1FarPhi.farPhiMainN a)).sum =
        Phase1FarPhi.farPhiN c := rfl
  rw [hmc, hs, hp, ← hpool] at hcore
  have hupper := (abs_le.mp hgap).2
  omega

theorem refined_high_partner_count
    (c : Config (AgentState L K)) (d : ℕ)
    (hgap : |AveragingRate.centredBiasSum c| ≤ (d : ℤ)) :
    RoleSplitConcentration.mainCount c ≤
      2 * (AveragingRate.highSet L K).sum c.count +
        d + Phase1FarPhi.farPhiN c := by
  have hcore := refined_high_count_core c
  have hmcNat :
      Multiset.countP
          (fun a : AgentState L K => a.role = Role.main) c =
        RoleSplitConcentration.mainCount c := by
    unfold RoleSplitConcentration.mainCount
    exact Multiset.countP_congr rfl (fun _ _ => rfl)
  have hmc := congrArg (Nat.cast : ℕ → ℤ) hmcNat
  have hpool :
      (AveragingRate.highSet L K).sum c.count =
        Multiset.countP
          (fun a : AgentState L K =>
            a.role = Role.main ∧ 3 ≤ a.smallBias.val) c := by
    convert Phase1FarPhiDrift.highSet_sum_count_eq
      (L := L) (K := K) c using 1 <;>
      apply Multiset.countP_congr rfl <;> intro a _ <;> rfl
  have hs :
      (c.map (fun a => AveragingRate.biasZ a)).sum =
        AveragingRate.centredBiasSum c := rfl
  have hp :
      (c.map (fun a => Phase1FarPhi.farPhiMainN a)).sum =
        Phase1FarPhi.farPhiN c := rfl
  rw [hmc, hs, hp, ← hpool] at hcore
  have hlower := (abs_le.mp hgap).1
  omega

/-- PHASE02 (22), as an exact rounded partner-count floor. -/
theorem refined_partner_floor_calibrated
    (n d : ℕ) (c : Config (AgentState L K))
    (hmain : 12 * n ≤ 25 * RoleSplitConcentration.mainCount c)
    (hsmall : 40 * d ≤ RoleSplitConcentration.mainCount c)
    (hgap : |AveragingRate.centredBiasSum c| ≤ (d : ℤ))
    (hphi : 100 * Phase1FarPhi.farPhiN c ≤ n) :
    (229 * n + 999) / 1000 ≤
        (AveragingRate.lowSet L K).sum c.count ∧
      (229 * n + 999) / 1000 ≤
        (AveragingRate.highSet L K).sum c.count := by
  have hlo := refined_low_partner_count c d hgap
  have hhi := refined_high_partner_count c d hgap
  constructor <;> omega

noncomputable def partnerRate (n p : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal ((p : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)))

/-- Generalize the existing overlap-aware ledger to any partner floor. -/
theorem sharp_weighted_drop_of_partner_floor
    {n p : ℕ} (hn : 2 ≤ n)
    (c : Config (AgentState L K))
    (hwin : PhaseOnlyWindows.Phase1Win (L := L) (K := K) n c)
    (hlo : p ≤ (AveragingRate.lowSet L K).sum c.count)
    (hhi : p ≤ (AveragingRate.highSet L K).sum c.count) :
    partnerRate n p * (Phase1FarPhi.farPhiN c : ℝ≥0∞) ≤
      WeightedDriftDropSum.weightedDropSum
        (NonuniformMajority L K) Phase1FarPhi.farPhiN c := by
  classical
  let f : ℕ := (AveragingRate.farHighSet L K).sum c.count +
    (AveragingRate.farLowSet L K).sum c.count
  let m : ℕ :=
    (AveragingRate.farHighSet L K).sum c.count *
      (AveragingRate.lowSet L K).sum c.count +
    (AveragingRate.farLowSet L K).sum c.count *
      (AveragingRate.highSet L K).sum c.count
  have hphi : Phase1FarPhi.farPhiN c ≤ 2 * f := by
    simpa [f] using
      Phase1FarPhiMultiplicative.farPhiN_le_two_mul_farCount c
  have hcount : p * f ≤ m := by
    dsimp only [f, m]
    rw [Nat.mul_add]
    apply Nat.add_le_add
    · rw [Nat.mul_comm]
      exact Nat.mul_le_mul le_rfl hlo
    · rw [Nat.mul_comm]
      exact Nat.mul_le_mul le_rfl hhi
  have hrate :
      partnerRate n p =
        (p : ℝ≥0∞) / ((n * (n - 1) : ℕ) : ℝ≥0∞) := by
    exact Phase1FarPhiMultiplicative.ofReal_scheduler_rate_eq n p hn
  have hrect :
      (∑ q ∈ Phase1FarPhiMultiplicative.farDropRect L K,
          c.interactionProb q.1 q.2) +
        ∑ q ∈ Phase1FarPhiSharp.farDropRectRev L K,
          c.interactionProb q.1 q.2 =
      (m : ℝ≥0∞) / ((n * (n - 1) : ℕ) : ℝ≥0∞) +
        (m : ℝ≥0∞) / ((n * (n - 1) : ℕ) : ℝ≥0∞) := by
    rw [Phase1FarPhiMultiplicative.sum_interactionProb_farDropRect
        n c hwin.1,
      Phase1FarPhiSharp.sum_interactionProb_farDropRectRev n c hwin.1]
  calc
    partnerRate n p * (Phase1FarPhi.farPhiN c : ℝ≥0∞) =
        ((p : ℝ≥0∞) / ((n * (n - 1) : ℕ) : ℝ≥0∞)) *
          (Phase1FarPhi.farPhiN c : ℝ≥0∞) := by rw [hrate]
    _ ≤ ((p : ℝ≥0∞) / ((n * (n - 1) : ℕ) : ℝ≥0∞)) *
          ((2 * f : ℕ) : ℝ≥0∞) := by gcongr
    _ = ((2 * (p * f) : ℕ) : ℝ≥0∞) /
          ((n * (n - 1) : ℕ) : ℝ≥0∞) := by
      push_cast
      simp only [div_eq_mul_inv]
      ac_rfl
    _ ≤ ((2 * m : ℕ) : ℝ≥0∞) /
          ((n * (n - 1) : ℕ) : ℝ≥0∞) := by gcongr
    _ = (m : ℝ≥0∞) / ((n * (n - 1) : ℕ) : ℝ≥0∞) +
          (m : ℝ≥0∞) / ((n * (n - 1) : ℕ) : ℝ≥0∞) := by
      push_cast
      simp only [div_eq_mul_inv]
      rw [two_mul, add_mul]
    _ = (∑ q ∈ Phase1FarPhiMultiplicative.farDropRect L K,
          c.interactionProb q.1 q.2) +
        ∑ q ∈ Phase1FarPhiSharp.farDropRectRev L K,
          c.interactionProb q.1 q.2 := hrect.symm
    _ ≤ WeightedDriftDropSum.weightedDropSum
          (NonuniformMajority L K) Phase1FarPhi.farPhiN c :=
      Phase1FarPhiSharp.sharpRectMass_le_weightedDropSum n c hwin

theorem sharp_farPhi_drift_of_partner_floor
    {n p : ℕ} (hn : 2 ≤ n)
    (c : Config (AgentState L K))
    (hwin : PhaseOnlyWindows.Phase1Win (L := L) (K := K) n c)
    (hlo : p ≤ (AveragingRate.lowSet L K).sum c.count)
    (hhi : p ≤ (AveragingRate.highSet L K).sum c.count) :
    ∫⁻ c', (Phase1FarPhi.farPhiN c' : ℝ≥0∞)
        ∂((NonuniformMajority L K).transitionKernel c) ≤
      (1 - partnerRate n p) * (Phase1FarPhi.farPhiN c : ℝ≥0∞) := by
  refine WeightedDriftDropSum.weighted_dyadic_mass_drift_of_dropSum
    (NonuniformMajority L K) Phase1FarPhi.farPhiN c ?_
    (partnerRate n p) (by simp [partnerRate]) ?_ ?_
  · rw [hwin.1]
    exact hn
  · intro pair
    exact Phase1FarPhi.farPhiN_stepOrSelf_le_of_phase1Win
      n c hwin pair.1 pair.2
  · exact sharp_weighted_drop_of_partner_floor hn c hwin hlo hhi

theorem refined_farPhi_drift
    {n : ℕ} (hn : 2 ≤ n) (d : ℕ)
    (c : Config (AgentState L K))
    (hwin : PhaseOnlyWindows.Phase1Win (L := L) (K := K) n c)
    (hmain : 12 * n ≤ 25 * RoleSplitConcentration.mainCount c)
    (hsmall : 40 * d ≤ RoleSplitConcentration.mainCount c)
    (hgap : |AveragingRate.centredBiasSum c| ≤ (d : ℤ))
    (hphi : 100 * Phase1FarPhi.farPhiN c ≤ n) :
    ∫⁻ c', (Phase1FarPhi.farPhiN c' : ℝ≥0∞)
        ∂((NonuniformMajority L K).transitionKernel c) ≤
      (1 - partnerRate n ((229 * n + 999) / 1000)) *
        (Phase1FarPhi.farPhiN c : ℝ≥0∞) := by
  obtain ⟨hlo, hhi⟩ :=
    refined_partner_floor_calibrated n d c hmain hsmall hgap hphi
  exact sharp_farPhi_drift_of_partner_floor hn c hwin hlo hhi

theorem refined_partnerRate_lower {n : ℕ} (hn : 2 ≤ n) :
    ENNReal.ofReal ((229 : ℝ) / (1000 * (n : ℝ))) ≤
      partnerRate n ((229 * n + 999) / 1000) := by
  let p := (229 * n + 999) / 1000
  have hp : 229 * n ≤ 1000 * p := by dsimp [p]; omega
  have hpR : 229 * (n : ℝ) ≤ 1000 * (p : ℝ) := by exact_mod_cast hp
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : 0 < (n : ℝ) := by linarith only [hnR]
  have hmul := mul_le_mul_of_nonneg_right hpR hnpos.le
  unfold partnerRate
  apply ENNReal.ofReal_le_ofReal
  apply (div_le_div_iff₀
    (by positivity : (0 : ℝ) < 1000 * (n : ℝ))
    (by nlinarith : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1))).2
  dsimp [p] at hmul
  nlinarith only [hmul, hnR]

/-- The minority-count arithmetic before (24). -/
theorem minority_count_floor
    (n m a b : ℕ)
    (hmain : 12 * n ≤ 25 * m)
    (hmajor : b ≤ a)
    (hgap : 40 * (a - b) ≤ m)
    (hwork : 3 * m < 100 * (a + b)) :
    3 * n < 2500 * b := by
  omega

theorem cancellation_probability_floor
    (n a b : ℕ) (hn : 2 ≤ n)
    (hmajor : b ≤ a) (hminor : 3 * n < 2500 * b) :
    (1 / 400000 : ℝ) <
      2 * (a : ℝ) * b / ((n : ℝ) * ((n : ℝ) - 1)) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hab : (b : ℝ) ≤ a := by exact_mod_cast hmajor
  have hb : 3 * (n : ℝ) < 2500 * b := by exact_mod_cast hminor
  have hden : 0 < (n : ℝ) * ((n : ℝ) - 1) := by nlinarith
  have hprod :
      0 < (2500 * (b : ℝ) - 3 * n) *
        (2500 * (b : ℝ) + 3 * n) := by
    apply mul_pos <;> nlinarith
  have habprod : (b : ℝ) * b ≤ (a : ℝ) * b :=
    mul_le_mul_of_nonneg_right hab (by positivity)
  rw [lt_div_iff₀ hden]
  nlinarith [sq_nonneg (n : ℝ)]

theorem avgFin7_safe_unit_mass_le (x y : Fin 7)
    (hx : x.val ∈ ({2, 3, 4} : Finset ℕ))
    (hy : y.val ∈ ({2, 3, 4} : Finset ℕ)) :
    (if (avgFin7 x y).1.val = 3 then 0 else 1) +
        (if (avgFin7 x y).2.val = 3 then 0 else 1) ≤
      (if x.val = 3 then 0 else 1) +
        (if y.val = 3 then 0 else 1) := by
  revert hx hy
  revert x y
  decide +kernel

theorem avgFin7_opposite_unit_cancels :
    avgFin7 ⟨2, by decide⟩ ⟨4, by decide⟩ =
        (⟨3, by decide⟩, ⟨3, by decide⟩) ∧
      avgFin7 ⟨4, by decide⟩ ⟨2, by decide⟩ =
        (⟨3, by decide⟩, ⟨3, by decide⟩) := by
  decide +kernel

/-- The preliminary strict-decrease floor from the existing coarse
rectangle theorem. This is a one-step kernel estimate, not yet (21). -/
theorem preliminary_drop_probability
    {n d : ℕ} (hn : 2 ≤ n)
    (c : Config (AgentState L K))
    (hwin : PhaseOnlyWindows.Phase1Win (L := L) (K := K) n c)
    (hmain : 12 * n ≤ 25 * RoleSplitConcentration.mainCount c)
    (hsmall : 40 * d ≤ RoleSplitConcentration.mainCount c)
    (hgap : |AveragingRate.centredBiasSum c| ≤ (d : ℤ))
    (hphi : n < 100 * Phase1FarPhi.farPhiN c) :
    ENNReal.ofReal (1 / 4000 : ℝ) ≤
      (NonuniformMajority L K).transitionKernel c
        {c' | Phase1FarPhi.farPhiN c' + 1 ≤ Phase1FarPhi.farPhiN c} := by
  let p : ℕ := (RoleSplitConcentration.mainCount c - d + 3) / 4
  have hp : 117 * n ≤ 1000 * p := by
    dsimp [p]
    omega
  have hpR : 117 * (n : ℝ) ≤ 1000 * (p : ℝ) := by exact_mod_cast hp
  have hphiR : (n : ℝ) ≤ 100 * (Phase1FarPhi.farPhiN c : ℝ) := by
    exact_mod_cast hphi.le
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hden : 0 < 2 * ((n : ℝ) * ((n : ℝ) - 1)) := by nlinarith
  have hproduct := mul_le_mul hpR hphiR
    (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    (by positivity : (0 : ℝ) ≤ 1000 * (p : ℝ))
  have hrate : (0 : ℝ) ≤
      (p : ℝ) / (2 * ((n : ℝ) * ((n : ℝ) - 1))) :=
    div_nonneg (Nat.cast_nonneg p) hden.le
  have hreal :
      (1 / 4000 : ℝ) ≤
        ((p : ℝ) / (2 * ((n : ℝ) * ((n : ℝ) - 1)))) *
          (Phase1FarPhi.farPhiN c : ℝ) := by
    calc
      (1 / 4000 : ℝ) ≤
          ((p : ℝ) * (Phase1FarPhi.farPhiN c : ℝ)) /
            (2 * ((n : ℝ) * ((n : ℝ) - 1))) := by
        apply (le_div_iff₀ hden).2
        nlinarith [sq_nonneg (n : ℝ)]
      _ = _ := by ring
  have hentry :
      Phase1PartnerFloor.Phase1GapFloorEntry
        n d (RoleSplitConcentration.mainCount c) c :=
    ⟨hwin, hgap, le_rfl⟩
  calc
    ENNReal.ofReal (1 / 4000 : ℝ) ≤
        ENNReal.ofReal
          (((p : ℝ) / (2 * ((n : ℝ) * ((n : ℝ) - 1)))) *
            (Phase1FarPhi.farPhiN c : ℝ)) :=
      ENNReal.ofReal_le_ofReal hreal
    _ = Phase1FarPhiMultiplicative.farBeta
          n d (RoleSplitConcentration.mainCount c) *
        (Phase1FarPhi.farPhiN c : ℝ≥0∞) := by
      rw [ENNReal.ofReal_mul hrate, ENNReal.ofReal_natCast]
      rfl
    _ ≤ _ :=
      Phase1FarPhiMultiplicative.farPhiN_drop_prob_multiplicative hn c hentry

/-! ## Calibrated auxiliary success-count bounds

These are the Bernoulli-comparison conclusions used by (21) and (25).
The protocol-specific adapted indicators and their conditional floors are
not constructed in these two lemmas.
-/

theorem preliminary_success_tail
    {α : Type*} {m : MeasurableSpace α}
    {μ : Measure α} [IsProbabilityMeasure μ] {ℱ : Filtration ℕ m}
    (n : ℕ) (I : ℕ → α → ℝ) (τ : α → WithTop ℕ)
    (hI : ∀ t, StronglyMeasurable[ℱ (t + 1)] (I t))
    (hzeroOne : ∀ t, ∀ᵐ ω ∂μ, I t ω = 0 ∨ I t ω = 1)
    (hτ : IsStoppingTime ℱ τ)
    (hcond : ∀ t : ℕ, ∀ᵐ ω ∂μ, (t : WithTop ℕ) < τ ω →
      (1 / 4000 : ℝ) ≤ (μ[I t | ℱ t]) ω)
    (hfail : ∀ ω, ((16000 * n : ℕ) : WithTop ℕ) < τ ω →
      PhaseThreeScalar.bernoulliCount I (16000 * n) ω < 2 * (n : ℝ)) :
    μ.real {ω | ((16000 * n : ℕ) : WithTop ℕ) < τ ω} ≤
      Real.exp (-(n : ℝ) / 2) := by
  have h := PhaseThreeScalar.adapted_success_hitting_tail
    hI hzeroOne hτ (by norm_num : (1 / 4000 : ℝ) ≤ 1)
    hcond (16000 * n) (2 * (n : ℝ)) hfail
  refine h.trans (Real.exp_le_exp.mpr ?_)
  have hlog := mul_le_mul_of_nonneg_left log_two_le_three_quarters
    (by positivity : 0 ≤ 2 * (n : ℝ))
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  nlinarith only [hlog]

theorem mass_success_tail
    {α : Type*} {m : MeasurableSpace α}
    {μ : Measure α} [IsProbabilityMeasure μ] {ℱ : Filtration ℕ m}
    (n : ℕ) (I : ℕ → α → ℝ) (τ : α → WithTop ℕ)
    (hI : ∀ t, StronglyMeasurable[ℱ (t + 1)] (I t))
    (hzeroOne : ∀ t, ∀ᵐ ω ∂μ, I t ω = 0 ∨ I t ω = 1)
    (hτ : IsStoppingTime ℱ τ)
    (hcond : ∀ t : ℕ, ∀ᵐ ω ∂μ, (t : WithTop ℕ) < τ ω →
      (1 / 400000 : ℝ) ≤ (μ[I t | ℱ t]) ω)
    (hfail : ∀ ω, ((800000 * n : ℕ) : WithTop ℕ) < τ ω →
      PhaseThreeScalar.bernoulliCount I (800000 * n) ω < (n : ℝ)) :
    μ.real {ω | ((800000 * n : ℕ) : WithTop ℕ) < τ ω} ≤
      Real.exp (-(n : ℝ) / 4) := by
  have h := PhaseThreeScalar.adapted_success_hitting_tail
    hI hzeroOne hτ (by norm_num : (1 / 400000 : ℝ) ≤ 1)
    hcond (800000 * n) (n : ℝ) hfail
  refine h.trans (Real.exp_le_exp.mpr ?_)
  have hlog := mul_le_mul_of_nonneg_left log_two_le_three_quarters
    (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  nlinarith only [hlog]

/-! ## Residual counters: the initial-mass bound needs only a lower bound -/

/-- A lower bound on each residual counter is enough for the depth MGF. -/
theorem counterDepthMass_start_le_card_of_residual
    {L K : ℕ} (N R : ℕ) (θ : ℝ)
    (c : Config (AgentState L K))
    (hphase : ∀ a ∈ c, a.phase.val = N)
    (hresidual : ∀ a ∈ c, a.role = Role.clock → R ≤ a.counter.val) :
    ClockCounterDepthCover.counterDepthMass
        (L := L) (K := K) N R θ c ≤ (c.card : ℝ≥0∞) := by
  classical
  unfold ClockCounterDepthCover.counterDepthMass
  calc
    (∑ a : AgentState L K,
        (c.count a : ℝ≥0∞) *
          ClockCounterDepthCover.counterDepthWeight N R θ a)
        ≤ ∑ a : AgentState L K, (c.count a : ℝ≥0∞) := by
      refine Finset.sum_le_sum ?_
      intro a _
      by_cases hz : c.count a = 0
      · simp [hz]
      · have ha : a ∈ c :=
          Multiset.one_le_count_iff_mem.mp (Nat.one_le_iff_ne_zero.mpr hz)
        have hp := hphase a ha
        by_cases hc : a.role = Role.clock
        · have hr : R - a.counter.val = 0 :=
            Nat.sub_eq_zero_of_le (hresidual a ha hc)
          simp [ClockCounterDepthCover.counterDepthWeight, hp, hc, hr]
        · simp [ClockCounterDepthCover.counterDepthWeight, hp, hc]
    _ = (c.card : ℝ≥0∞) := by
      have hcount : (∑ a : AgentState L K, c.count a) = c.card :=
        Multiset.sum_count_eq_card
          (s := (Finset.univ : Finset (AgentState L K)))
          (m := c) (fun a _ => Finset.mem_univ a)
      exact_mod_cast hcount

/-- First-exit depth bound with genuine residual counters.
No counter is reset, and no common-counter equality is assumed. -/
theorem stopped_clock_exit_from_residual
    {L K : ℕ} (n d M T R : ℕ) (hn : 2 ≤ n)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (c : Config (AgentState L K))
    (hgood : Phase1ClockDepthStopped.Good n d M c)
    (hresidual : ∀ a ∈ c, a.role = Role.clock → R ≤ a.counter.val) :
    (Phase1ClockDepthStopped.stopK (L := L) (K := K) n d M ^ T) c
        {x | ¬ Phase1ClockDepthStopped.Good n d M x} ≤
      ClockCounterDepthCover.counterDepthTail n T R θ := by
  have hstart :
      ClockCounterDepthCover.counterDepthMass
          (L := L) (K := K) 1 R θ c ≤ (n : ℝ≥0∞) := by
    have h := counterDepthMass_start_le_card_of_residual
      1 R θ c hgood.1.1.2 hresidual
    simpa only [hgood.1.1.1] using h
  have htail := geometric_drift_tail
    (Phase1ClockDepthStopped.stopK (L := L) (K := K) n d M)
    (Phase1ClockDepthStopped.stoppedDepthMass
      (L := L) (K := K) n d M R θ)
    (Phase1ClockDepthStopped.stoppedDepthMass_measurable n d M R θ)
    (ClockCounterDepthCover.counterDepthRate n θ)
    (Phase1ClockDepthStopped.stoppedDepthMass_drift n d M R hn θ hθ)
    T c (ClockCounterDepthCover.counterDepthThreshold R θ)
    (ClockCounterDepthCover.counterDepthThreshold_ne_zero R θ)
    (ClockCounterDepthCover.counterDepthThreshold_ne_top R θ)
  calc
    (Phase1ClockDepthStopped.stopK (L := L) (K := K) n d M ^ T) c
        {x | ¬ Phase1ClockDepthStopped.Good n d M x} ≤
      (Phase1ClockDepthStopped.stopK (L := L) (K := K) n d M ^ T) c
        {x | ClockCounterDepthCover.counterDepthThreshold R θ ≤
          Phase1ClockDepthStopped.stoppedDepthMass n d M R θ x} := by
      apply measure_mono
      intro x hx
      have hx' : ¬ Phase1ClockDepthStopped.Good n d M x := hx
      simp [Phase1ClockDepthStopped.stoppedDepthMass, hx']
    _ ≤ ClockCounterDepthCover.counterDepthRate n θ ^ T *
        Phase1ClockDepthStopped.stoppedDepthMass n d M R θ c /
          ClockCounterDepthCover.counterDepthThreshold R θ := htail
    _ ≤ ClockCounterDepthCover.counterDepthRate n θ ^ T * (n : ℝ≥0∞) /
          ClockCounterDepthCover.counterDepthThreshold R θ := by
      gcongr
      simpa [Phase1ClockDepthStopped.stoppedDepthMass, hgood] using hstart
    _ = ClockCounterDepthCover.counterDepthTail n T R θ := rfl

/-- A real endpoint outside the Phase-1 positive-clock gate has the same
residual-counter upper bound, by the existing stopped-chain domination. -/
theorem real_clock_gate_failure_from_residual
    {L K : ℕ} (n d M T R : ℕ) (hn : 2 ≤ n)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (c : Config (AgentState L K))
    (hgood : Phase1ClockDepthStopped.Good n d M c)
    (hresidual : ∀ a ∈ c, a.role = Role.clock → R ≤ a.counter.val) :
    ((NonuniformMajority L K).transitionKernel ^ T) c
        {x | ¬ Phase1ClockDepthStopped.Good n d M x} ≤
      ClockCounterDepthCover.counterDepthTail n T R θ := by
  exact
    (Phase1ClockDepthStopped.real_bad_le_stopped_bad n d M T c).trans
      (stopped_clock_exit_from_residual
        n d M T R hn θ hθ c hgood hresidual)

/-- The calibrated residual-clock first-exit bound on the existing stopped
kernel. This does not yet identify a pair-log prefix hitting event. -/
theorem phase_one_stopped_clock_estimate
    {n : ℕ} (hn : timePopulationThreshold ≤ n)
    (g : ℤ) (c : InputCfg n) (hentry : PhaseOneDrainEntry n g c) :
    (Phase1ClockDepthStopped.stopK
        (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
        n g.natAbs (RoleSplitConcentration.mainCount c) ^ weakHorizon n) c
        {x | ¬ Phase1ClockDepthStopped.Good
          n g.natAbs (RoleSplitConcentration.mainCount c) x} ≤
      ENNReal.ofReal (Real.rpow (n : ℝ) (-(5 / 2 : ℝ))) := by
  have hnsmall : 2 ≤ n :=
    (by norm_num : (2 : ℕ) ≤ 40).trans (time_population_bounds hn).2
  have hgood := hentry.clock_depth_good
  have hreserve : ∀ a ∈ c, a.role = Role.clock →
      30 * PhaseThreeModel.Numeric.clockHours n ≤ a.counter.val := by
    rcases hentry with ⟨_, _, _, _, _, _, hcounter, _, _, _⟩
    simpa only [PhaseThreeModel.Numeric.clockHours] using hcounter
  exact
    (stopped_clock_exit_from_residual
      n g.natAbs (RoleSplitConcentration.mainCount c) (weakHorizon n)
      (30 * PhaseThreeModel.Numeric.clockHours n) hnsmall
      (Real.log (3 / 2 : ℝ))
      (Real.log_nonneg (by norm_num)) c hgood hreserve).trans
        (residual_counterDepthTail_le hn)

/-- Actual-kernel endpoint failure, with the residual counter hypothesis
and numerical value required by (27). No future survival is conditioned on. -/
theorem phase_one_clock_gate_failure_estimate
    {n : ℕ} (hn : timePopulationThreshold ≤ n)
    (g : ℤ) (c : InputCfg n) (hentry : PhaseOneDrainEntry n g c) :
    ((NonuniformMajority (PhaseThreeModel.Numeric.hourIndex n) 256).transitionKernel
        ^ weakHorizon n) c
        {x | ¬ Phase1ClockDepthStopped.Good
          n g.natAbs (RoleSplitConcentration.mainCount c) x} ≤
      ENNReal.ofReal (Real.rpow (n : ℝ) (-(5 / 2 : ℝ))) := by
  exact
    (Phase1ClockDepthStopped.real_bad_le_stopped_bad
      n g.natAbs (RoleSplitConcentration.mainCount c) (weakHorizon n) c).trans
        (phase_one_stopped_clock_estimate hn g c hentry)

/-! ## The joint event at a genuinely past-measurable time -/

/-- Finite fibres belong to the recorded past at their own times.
In discrete time, this is equivalent to the stopping-time condition. -/
def PairLogPastTime (σ : Ω L K → WithTop ℕ) : Prop :=
  ∀ s : ℕ,
    MeasurableSet[PairLog.pairLogFiltration L K s]
      {ω | σ ω = (s : WithTop ℕ)}

/-- The existential finite witness encodes finite sigma. The hit window
is inclusive, starts at sigma, and uses the exact three-stage duration. -/
def phaseOneDrainFailure
    (init : Cfg L K) (n : ℕ) (g : ℤ)
    (σ : Ω L K → WithTop ℕ) : Set (Ω L K) :=
  {ω | ∃ s : ℕ,
    σ ω = (s : WithTop ℕ) ∧
    PhaseOneDrainEntry n g (trace init ω s) ∧
    ∀ k ≤ weakHorizon n, ¬ PhaseOneDrained (trace init ω (s + k))}

theorem phaseOneDrainEntry_past
    (init : Cfg L K) (n : ℕ) (g : ℤ) (s : ℕ) :
    MeasurableSet[PairLog.pairLogFiltration L K s]
      {ω | PhaseOneDrainEntry n g (trace init ω s)} :=
  (show MeasurableSet {c : Cfg L K | PhaseOneDrainEntry n g c} from
    (Set.to_countable _).measurableSet).preimage
      (PairLog.measurable_trace_at init s)

theorem phaseOneDrained_measurable (init : Cfg L K) (t : ℕ) :
    MeasurableSet {ω | PhaseOneDrained (trace init ω t)} :=
  (show MeasurableSet {c : Cfg L K | PhaseOneDrained c} from
    (Set.to_countable _).measurableSet).preimage
      ((measurable_pi_apply t).comp (measurable_trace init))

theorem phaseOneDrainFailure_measurable
    (init : Cfg L K) (n : ℕ) (g : ℤ)
    (σ : Ω L K → WithTop ℕ) (hσ : PairLogPastTime σ) :
    MeasurableSet (phaseOneDrainFailure init n g σ) := by
  have htime (s : ℕ) :
      MeasurableSet {ω | σ ω = (s : WithTop ℕ)} :=
    (PairLog.pairLogFiltration L K).le s _ (hσ s)
  have hentry (s : ℕ) :
      MeasurableSet {ω | PhaseOneDrainEntry n g (trace init ω s)} :=
    (PairLog.pairLogFiltration L K).le s _
      (phaseOneDrainEntry_past init n g s)
  have hbad (s : ℕ) :
      MeasurableSet
        {ω | ∀ k ≤ weakHorizon n,
          ¬ PhaseOneDrained (trace init ω (s + k))} := by
    have heq :
        {ω : Ω L K | ∀ k ≤ weakHorizon n,
          ¬ PhaseOneDrained (trace init ω (s + k))} =
        ⋂ k : ℕ, {ω : Ω L K | k ≤ weakHorizon n →
          ¬ PhaseOneDrained (trace init ω (s + k))} := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
    rw [heq]
    apply MeasurableSet.iInter
    intro k
    by_cases hk : k ≤ weakHorizon n
    · simpa only [hk, true_implies] using
        (phaseOneDrained_measurable init (s + k)).compl
    · simp only [hk, false_implies, Set.setOf_true]
      exact MeasurableSet.univ
  have heq :
      phaseOneDrainFailure init n g σ =
      ⋃ s : ℕ,
        {ω | σ ω = (s : WithTop ℕ)} ∩
          ({ω | PhaseOneDrainEntry n g (trace init ω s)} ∩
            {ω | ∀ k ≤ weakHorizon n,
              ¬ PhaseOneDrained (trace init ω (s + k))}) := by
    ext ω
    simp only [phaseOneDrainFailure, Set.mem_setOf_eq,
      Set.mem_iUnion, Set.mem_inter_iff]
  rw [heq]
  exact MeasurableSet.iUnion
    (fun s => (htime s).inter ((hentry s).inter (hbad s)))

theorem phaseOneDrainFailure_finite
    (init : Cfg L K) (n : ℕ) (g : ℤ)
    (σ : Ω L K → WithTop ℕ) {ω : Ω L K}
    (hω : ω ∈ phaseOneDrainFailure init n g σ) :
    σ ω ≠ ⊤ := by
  obtain ⟨s, hs, _, _⟩ := hω
  rw [hs]
  exact WithTop.coe_ne_top

theorem phaseOneDrainFailure_subset_endpoint
    (init : Cfg L K) (n : ℕ) (g : ℤ)
    (σ : Ω L K → WithTop ℕ) :
    phaseOneDrainFailure init n g σ ⊆
      {ω | ∃ s : ℕ,
        σ ω = (s : WithTop ℕ) ∧
        PhaseOneDrainEntry n g (trace init ω s) ∧
        ¬ PhaseOneDrained (trace init ω (s + weakHorizon n))} := by
  intro ω hω
  obtain ⟨s, hs, hentry, hbad⟩ := hω
  exact ⟨s, hs, hentry, hbad (weakHorizon n) le_rfl⟩

/-- Integrate a continuation estimate against a complete recorded-past event.
This preserves scheduler information, including invisible interactions. -/
theorem pairLog_prefix_event_bound
    (init : Cfg L K) (s : ℕ)
    (A : Set (Finset.Iic s → Draw L K)) (hA : MeasurableSet A)
    (B : Set (Ω L K)) (hB : MeasurableSet B) (ε : ℝ≥0∞)
    (hbound : ∀ p ∈ A,
      Kernel.traj (X := fun _ => Draw L K)
        (fun t => pairKernel init t) s p B ≤ ε) :
    law init
      ((frestrictLe (π := fun _ => Draw L K) s) ⁻¹' A ∩ B) ≤
      ε * law init
        ((frestrictLe (π := fun _ => Draw L K) s) ⁻¹' A) := by
  classical
  let κ := fun t => pairKernel init t
  let Γ := Kernel.traj (X := fun _ => Draw L K) κ s
  let ν : Measure (Finset.Iic s → Draw L K) :=
    Kernel.partialTraj (X := fun _ => Draw L K) κ 0 s (fun _ => none)
  let E : Set (Ω L K) :=
    (frestrictLe (π := fun _ => Draw L K) s) ⁻¹' A
  have hE : MeasurableSet E :=
    hA.preimage (measurable_frestrictLe (X := fun _ => Draw L K) s)
  have hlaw :
      law init = Kernel.traj (X := fun _ => Draw L K) κ 0 (fun _ => none) :=
    (Kernel.traj_apply _ _).symm
  have hsplit (D : Set (Ω L K)) (hD : MeasurableSet D) :
      law init D = ∫⁻ p, Γ p D ∂ν := by
    rw [hlaw]
    change Kernel.traj (X := fun _ => Draw L K) κ 0 (fun _ => none) D =
      ∫⁻ p, Kernel.traj (X := fun _ => Draw L K) κ s p D
        ∂Kernel.partialTraj (X := fun _ => Draw L K) κ 0 s (fun _ => none)
    rw [← Kernel.traj_comp_partialTraj
      (X := fun _ => Draw L K) (Nat.zero_le s),
      Kernel.comp_apply' _ _ _ hD]
  have hlocal (p : Finset.Iic s → Draw L K) :
      Γ p (E ∩ B) ≤ ε * Γ p E := by
    have hfreeze :
        ∀ᵐ ω ∂Γ p, frestrictLe (π := fun _ => Draw L K) s ω = p := by
      rw [ae_iff]
      change Kernel.traj (X := fun _ => Draw L K) κ s p
        ((frestrictLe (π := fun _ => Draw L K) s) ⁻¹' ({p}ᶜ)) = 0
      rw [← Measure.map_apply
        (measurable_frestrictLe (X := fun _ => Draw L K) s)
        (measurableSet_singleton p).compl,
        Kernel.traj_map_frestrictLe_apply,
        Kernel.partialTraj_self, Kernel.id_apply]
      simp
    by_cases hp : p ∈ A
    · have hwhole : Γ p E = 1 := by
        calc
          Γ p E = Γ p Set.univ := by
            apply measure_congr
            filter_upwards [hfreeze] with ω hω
            show (ω ∈ E) = (ω ∈ Set.univ)
            simp only [E, Set.mem_preimage, hω, hp, Set.mem_univ]
          _ = 1 := measure_univ
      have hinter : Γ p (E ∩ B) = Γ p B := by
        apply measure_congr
        filter_upwards [hfreeze] with ω hω
        show (ω ∈ E ∩ B) = (ω ∈ B)
        simp only [Set.mem_inter_iff, E, Set.mem_preimage, hω, hp, true_and]
      rw [hwhole, mul_one, hinter]
      exact hbound p hp
    · have hzero : Γ p E = 0 := by
        calc
          Γ p E = Γ p ∅ := by
            apply measure_congr
            filter_upwards [hfreeze] with ω hω
            show (ω ∈ E) = (ω ∈ (∅ : Set _))
            simp only [E, Set.mem_preimage, hω, hp,
              Set.mem_empty_iff_false]
          _ = 0 := measure_empty
      rw [hzero, mul_zero]
      exact (measure_mono Set.inter_subset_left).trans_eq hzero
  change law init (E ∩ B) ≤ ε * law init E
  calc
    law init (E ∩ B) = ∫⁻ p, Γ p (E ∩ B) ∂ν :=
      hsplit (E ∩ B) (hE.inter hB)
    _ ≤ ∫⁻ p, ε * Γ p E ∂ν := lintegral_mono hlocal
    _ = ε * ∫⁻ p, Γ p E ∂ν :=
      lintegral_const_mul ε (Kernel.measurable_coe Γ hE)
    _ = ε * law init E := by rw [← hsplit E hE]

/-
The joint conditional producer requested here is proved, with this exact type, as
`PhaseOneDrainProducer.phaseOneDrain_conditional_producer`
(Probability/PhaseOneDrainProducer.lean): the three stage tails restated from a
past-measurable start (TraceDrain, PhaseOneDrainStages), the residual clock exit, and
the splice over the values of the stopping time.
-/

end Ripple.PopulationProtocol.ExactMajority.PhaseOneDrain
