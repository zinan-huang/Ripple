-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockReciprocalAlgebra.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockProbabilityFloors
import Ripple.PopulationProtocol.ExactMajority.Probability.StageEventSpec

/-!
# A reciprocal-potential proof of the P3a constants

The actual sparse-front rate is at least 2X/(5m), slightly stronger than
the X/(3m) floor recorded in P3a. For X >= 1, the potential 1/(5X-4)
therefore contracts by 1-1/(3m). This alternative to the coupon comparison
retains the same 30m log m horizon and m^-9 failure allowance.

The total definition frontWeight uses the natural predecessor, so its
value at zero is also positive and at most one. Stopping will exclude
zero fronts when the drift estimate is applied.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators MeasureTheory ProbabilityTheory

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockReciprocalAlgebra

open TimeTheorem PairLog PairLogAuxiliary PhaseThreeClockVirtual
  PhaseThreeClockGatedLaw PhaseThreeClockGatedLevelOne PhaseThreeClockProbabilityFloors

variable {L K m : ℕ}

/-- A sharper consequence of the same density and sparse-front hypotheses. -/
theorem raw_epidemic_rate_sharp (m C X : ℝ)
    (hm : 2 ≤ m) (hX : 0 ≤ X) (hdensity : 6 * m ≤ 25 * C)
    (hsparse : 10 * X ≤ C) :
    2 * X / (5 * m) ≤ 2 * X * (C - X) / (m * (m - 1)) := by
  have hmpos : 0 < m := by linarith
  have hroom : m - 1 ≤ 5 * (C - X) := by nlinarith
  have hprod := mul_le_mul_of_nonneg_left hroom
    (mul_nonneg hX hmpos.le)
  apply (div_le_div_iff₀ (by positivity : 0 < 5 * m)
    (mul_pos hmpos (by linarith : 0 < m - 1))).2
  nlinarith

theorem gated_raw_rate_sharp (f : Fin m → AgentState L K)
    (hm : 2 ≤ m) (ℓ : ℕ) (hℓ : 1 ≤ ℓ)
    (hdensity : 6 * m ≤ 25 * clockCount f)
    (hsparse : 10 * frontCount f ℓ ≤ clockCount f) :
    2 * (frontCount f ℓ : ℝ) / (5 * (m : ℝ)) ≤
      ((goodPairs (GatedTick ℓ) f).card : ℝ) /
        ((m : ℝ) * ((m : ℝ) - 1)) := by
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hden : 0 ≤ (m : ℝ) * ((m : ℝ) - 1) := by
    apply mul_nonneg (by positivity)
    linarith
  have hXC := frontCount_le_clockCount f ℓ
  have hcount :
      2 * (frontCount f ℓ : ℝ) *
          ((clockCount f : ℝ) - (frontCount f ℓ : ℝ)) ≤
        ((goodPairs (GatedTick ℓ) f).card : ℝ) := by
    have hcast :
        ((2 * frontCount f ℓ * (clockCount f - frontCount f ℓ) : ℕ) : ℝ) ≤
          ((goodPairs (GatedTick ℓ) f).card : ℝ) := by
      exact_mod_cast epidemic_le_gated_pairs f ℓ hℓ
    simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub hXC] using hcast
  exact (raw_epidemic_rate_sharp (m : ℝ) (clockCount f : ℝ)
    (frontCount f ℓ : ℝ) hmR (by positivity)
    (by exact_mod_cast hdensity) (by exact_mod_cast hsparse)).trans
      (div_le_div_of_nonneg_right hcount hden)

open Classical in
theorem gated_conditional_sharp_floor (init : Cfg L K) (hc : 2 ≤ init.card)
    (ℓ t : ℕ) (hℓ : 1 ≤ ℓ) :
    ∀ᵐ ω ∂law init,
      6 * init.card ≤ 25 * clockCount (auxLabels init virtualRule ω t) →
      10 * frontCount (auxLabels init virtualRule ω t) ℓ ≤
          clockCount (auxLabels init virtualRule ω t) →
      2 * (frontCount (auxLabels init virtualRule ω t) ℓ : ℝ) /
          (5 * (init.card : ℝ)) ≤
        ((law init)[fun ω =>
          if ∃ i j, drawLabels init ω (t + 1) = some (i, j) ∧
              GatedTick ℓ (auxLabels init virtualRule ω t) i j
          then (1 : ℝ) else 0 | pairLogFiltration L K t]) ω := by
  filter_upwards [gatedTick_conditional_law init hc ℓ t] with ω hω
  intro hdensity hsparse
  rw [hω]
  exact gated_raw_rate_sharp _ hc ℓ hℓ hdensity hsparse

def frontWeight (X : ℕ) : ℝ := 1 / (5 * ((X - 1 : ℕ) : ℝ) + 1)

def frontLoss (X : ℕ) : ℝ := frontWeight X - frontWeight (X + 1)

theorem frontWeight_pos (X : ℕ) : 0 < frontWeight X := by
  unfold frontWeight
  positivity

theorem frontWeight_le_one (X : ℕ) : frontWeight X ≤ 1 := by
  unfold frontWeight
  apply (div_le_iff₀ (by positivity : 0 < 5 * ((X - 1 : ℕ) : ℝ) + 1)).2
  have hX : (0 : ℝ) ≤ ((X - 1 : ℕ) : ℝ) := by positivity
  nlinarith

theorem frontWeight_antitone : Antitone frontWeight := by
  intro X Y hXY
  apply one_div_le_one_div_of_le (by positivity :
    0 < 5 * ((X - 1 : ℕ) : ℝ) + 1)
  have hpred : ((X - 1 : ℕ) : ℝ) ≤ ((Y - 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.sub_le_sub_right hXY 1
  linarith

theorem frontLoss_bounds (X : ℕ) : 0 ≤ frontLoss X ∧ frontLoss X ≤ 1 := by
  have hmono := frontWeight_antitone (Nat.le_succ X)
  have hpos := (frontWeight_pos (X + 1)).le
  have hup := frontWeight_le_one X
  unfold frontLoss
  constructor <;> linarith

theorem frontWeight_eq_of_one_le (X : ℕ) (hX : 1 ≤ X) :
    frontWeight X = 1 / (5 * (X : ℝ) - 4) := by
  unfold frontWeight
  rw [Nat.cast_sub hX, Nat.cast_one]
  congr 1
  ring

theorem frontWeight_succ (X : ℕ) :
    frontWeight (X + 1) = 1 / (5 * (X : ℝ) + 1) := by
  simp [frontWeight]

theorem frontLoss_formula (X : ℕ) (hX : 1 ≤ X) :
    frontLoss X =
      5 / ((5 * (X : ℝ) - 4) * (5 * (X : ℝ) + 1)) := by
  have hXR : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hleft : 5 * (X : ℝ) - 4 ≠ 0 := by linarith
  have hright : 5 * (X : ℝ) + 1 ≠ 0 := by positivity
  rw [frontLoss, frontWeight_eq_of_one_le X hX, frontWeight_succ]
  field_simp [hleft, hright]
  <;> ring

/-- The exact algebra behind contraction by 1-1/(3m). -/
theorem frontLoss_rate_dominates (X : ℕ) (hX : 1 ≤ X)
    (m : ℝ) (hm : 0 < m) :
    (1 / (3 * m)) * frontWeight X ≤
      frontLoss X * (2 * (X : ℝ) / (5 * m)) := by
  have hXR : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hratio :
      1 / (3 * m) ≤ 2 * (X : ℝ) / (m * (5 * (X : ℝ) + 1)) := by
    apply (div_le_div_iff₀ (by positivity : 0 < 3 * m)
      (by positivity : 0 < m * (5 * (X : ℝ) + 1))).2
    have hprod := mul_nonneg hm.le (sub_nonneg.mpr hXR)
    nlinarith
  have hleft : 5 * (X : ℝ) - 4 ≠ 0 := by linarith
  have hright : 5 * (X : ℝ) + 1 ≠ 0 := by positivity
  have hid :
      frontLoss X * (2 * (X : ℝ) / (5 * m)) =
        (2 * (X : ℝ) / (m * (5 * (X : ℝ) + 1))) * frontWeight X := by
    rw [frontLoss_formula X hX, frontWeight_eq_of_one_le X hX]
    field_simp [hleft, hright, ne_of_gt hm]
    <;> ring
  rw [hid]
  exact mul_le_mul_of_nonneg_right hratio (frontWeight_pos X).le

theorem frontWeight_boundary (X b : ℕ) (hX : X < b) :
    1 ≤ (5 * (b : ℝ)) * frontWeight X := by
  have hden : 5 * ((X - 1 : ℕ) : ℝ) + 1 ≤ 5 * (b : ℝ) := by
    have hnat : 5 * (X - 1) + 1 ≤ 5 * b := by omega
    exact_mod_cast hnat
  rw [frontWeight, mul_one_div]
  apply (le_div_iff₀ (by positivity : 0 < 5 * ((X - 1 : ℕ) : ℝ) + 1)).2
  simpa only [one_mul] using hden

theorem below_bulk_is_sparse (X C : ℕ)
    (hX : X < StageEventSpec.bulkThreshold C) : 10 * X ≤ C := by
  have hreal : (X : ℝ) < (C : ℝ) / 10 :=
    Nat.lt_ceil.mp hX
  have hbound : 10 * (X : ℝ) ≤ (C : ℝ) := by linarith
  exact_mod_cast hbound

theorem five_bulk_le_population (m C : ℕ) (hm : 20 ≤ m) (hC : C ≤ m) :
    5 * StageEventSpec.bulkThreshold C ≤ m := by
  have hceil := Nat.ceil_lt_add_one (by positivity : 0 ≤ (C : ℝ) / 10)
  have hmR : (20 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hCR : (C : ℝ) ≤ (m : ℝ) := by exact_mod_cast hC
  have hbound : 5 * (StageEventSpec.bulkThreshold C : ℝ) ≤ (m : ℝ) := by
    change 5 * (Nat.ceil ((C : ℝ) / 10) : ℝ) ≤ (m : ℝ)
    linarith
  exact_mod_cast hbound

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockReciprocalAlgebra

end
