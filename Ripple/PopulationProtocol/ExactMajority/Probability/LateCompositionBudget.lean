import Ripple.PopulationProtocol.ExactMajority.Probability.LateLemmaThirteenSmallGap
import Ripple.PopulationProtocol.ExactMajority.Probability.TimeTheorem
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase3Model

/-!
# Late composition budget (Lemma 15 of the late-tail analysis)

Numerical check that the late failure charges in the library (through
`lemmaThirteenFailureCharge`), together with the charges still to come from
Lemma 14, fit inside the Lemma 15 budget `100 n^(-2)` for every
`n >= timePopulationThreshold`.

Every term is bounded by a coefficient times `1 / n^2`, using only
* `TimeTheorem.time_hour_calibration`: `hourIndex n + 1 <= (11/6) log n`,
* `Calibration.population_log_lower`: in particular `500000 <= log n`,
* `TimeTheorem.time_exp_three_lt`: `exp 3 < 21`.

Coefficient ledger (all in units of `1 / n^2`):
`lemmaThirteenFailureCharge` 83, Lemma 14 spreads and cleanup 3, the upper-timer
exits of Phases 5 and 8 used by the late time chain 2, total 88 < 100.

The Lemma 14 charges and the reserve are stated here as plain scalars with no
finite-witness union factor.  A union factor `2 (n+1) (hourIndex n + 1)` on
any charge of exact order `n^(-3)` would multiply it by about `2 log n`, which
exceeds the whole budget; the Phase-9 spreads and the output cleanup must
therefore be proved by a state-independent tail applied at the first Phase-9
time (fibre weights), not by a witness union.
-/

noncomputable section

open scoped ENNReal

namespace Ripple.PopulationProtocol.ExactMajority.LateCompositionBudget

open TimeTheorem
open LateSamplingStrongReceiptProducer
open LatePhaseSixDrainSelectedLevel
open LatePhaseSixDrainPaperNumerics
open LateLemmaElevenAssembly
open LateLemmaTwelveSingleBand LateLemmaTwelveBands LateLemmaTwelveSmallGap
open LateLemmaThirteenRoute LateLemmaThirteenSmallGap

/-! ## Charges still to come -/

/-- Lemma 14: threshold-9 spread and majority-bit spread (`e^3 n^(-3)` each),
and output cleanup (`n^(-3)`), with no union factor. -/
def lemmaFourteenCharge (n : ℕ) : ℝ≥0∞ :=
  (ENNReal.ofReal (Real.exp 3 / (n : ℝ) ^ 3) +
      ENNReal.ofReal (Real.exp 3 / (n : ℝ) ^ 3)) +
    ENNReal.ofReal (1 / (n : ℝ) ^ 3)

/-- Reserve for the timed-phase upper exits of Phases 5 and 8, which the late
time chain uses; the upper exits of Phases 6 and 7 are already inside
`lemmaThirteenFailureCharge`, and Phase 9 has no timed upper exit. -/
def lateUpperExitReserve (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (1 / (n : ℝ) ^ 5) + ENNReal.ofReal (1 / (n : ℝ) ^ 5)

/-- The whole late charge of the Lemma 15 table on the small-gap branch. -/
def lateTotalCharge (n : ℕ) : ℝ≥0∞ :=
  (lemmaThirteenFailureCharge n + lemmaFourteenCharge n) +
    lateUpperExitReserve n

/-! ## Real-variable estimates -/

section Real

variable {x : ℝ}

private theorem exp_dominates {b K : ℝ} (hx : 500000 ≤ x)
    (hb : 1 / 50 ≤ b) (hK : K ≤ 100) :
    K * x * Real.exp (-(b * x)) ≤ 1 := by
  have hx0 : 0 ≤ x := by linarith
  have hbx : 0 ≤ b * x := by positivity
  have hq := Real.quadratic_le_exp_of_nonneg hbx
  have hbx2 : x / 50 ≤ b * x := by nlinarith
  have hsq : x * x / 5000 ≤ (b * x) ^ 2 / 2 := by nlinarith
  have hbig : K * x ≤ Real.exp (b * x) := by
    have : K * x ≤ x * x / 5000 := by nlinarith
    linarith
  rw [Real.exp_neg, ← div_eq_mul_inv]
  rw [div_le_one (Real.exp_pos _)]
  exact hbig

private theorem exp_neg_two_mul {x : ℝ} :
    Real.exp (-(2 * x)) = 1 / Real.exp x ^ 2 := by
  rw [one_div, ← Real.exp_nat_mul, ← Real.exp_neg]
  congr 1

private theorem exp_neg_nat_mul {x : ℝ} (k : ℕ) :
    Real.exp (-((k : ℝ) * x)) = 1 / Real.exp x ^ k := by
  rw [one_div, ← Real.exp_nat_mul, ← Real.exp_neg]

private theorem rpow_exp_neg {x : ℝ} (a : ℝ) :
    Real.rpow (Real.exp x) (-a) = Real.exp (-(a * x)) := by
  rw [Real.rpow_eq_pow, Real.rpow_def_of_pos (Real.exp_pos x), Real.log_exp]
  congr 1
  ring

/-- A power `n^(-a)` with `a >= 2.02` times a hour-index factor is below the
unit `n^(-2)`. -/
private theorem hour_mul_le {H a : ℝ} (hx : 500000 ≤ x)
    (hH : H ≤ 11 / 6 * x) (ha : 2 + 1 / 50 ≤ a) :
    H * Real.exp (-(a * x)) ≤ Real.exp (-(2 * x)) := by
  have hkey := exp_dominates (x := x) (b := a - 2) (K := 11 / 6) hx
    (by linarith) (by norm_num)
  have hsplit : Real.exp (-(a * x)) =
      Real.exp (-(2 * x)) * Real.exp (-((a - 2) * x)) := by
    rw [← Real.exp_add]; congr 1; ring
  have hpos : 0 < Real.exp (-((a - 2) * x)) := Real.exp_pos _
  rw [hsplit]
  have h1 : H * Real.exp (-((a - 2) * x)) ≤ 1 := by
    calc H * Real.exp (-((a - 2) * x))
        ≤ (11 / 6 * x) * Real.exp (-((a - 2) * x)) :=
          mul_le_mul_of_nonneg_right hH hpos.le
      _ = 11 / 6 * x * Real.exp (-((a - 2) * x)) := by ring
      _ ≤ 1 := hkey
  have hE := Real.exp_pos (-(2 * x))
  calc H * (Real.exp (-(2 * x)) * Real.exp (-((a - 2) * x)))
      = Real.exp (-(2 * x)) * (H * Real.exp (-((a - 2) * x))) := by ring
    _ ≤ Real.exp (-(2 * x)) * 1 := mul_le_mul_of_nonneg_left h1 hE.le
    _ = Real.exp (-(2 * x)) := by ring

/-- The finite-union factor `2 (N+1) H`, with a coefficient `c <= 3`, against
`N^(-a)` for `a >= 3.02`, is below `N^(-2)`. -/
private theorem union_mul_le {H a c : ℝ} (hx : 500000 ≤ x)
    (hH0 : 0 ≤ H) (hH : H ≤ 11 / 6 * x) (hc0 : 0 ≤ c) (hc : c ≤ 3)
    (ha : 3 + 1 / 50 ≤ a) :
    (2 * (Real.exp x + 1) * H) * (c * Real.exp (-(a * x))) ≤
      Real.exp (-(2 * x)) := by
  have hN1 : 1 ≤ Real.exp x := by
    rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by linarith)
  have hkey := exp_dominates (x := x) (b := a - 3) (K := 22) hx
    (by linarith) (by norm_num)
  have hsplit : Real.exp x * Real.exp (-(a * x)) =
      Real.exp (-(2 * x)) * Real.exp (-((a - 3) * x)) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hxpos : 0 ≤ x := by linarith
  have hE := Real.exp_pos (-(2 * x))
  have hEa := Real.exp_pos (-(a * x))
  have hEb := Real.exp_pos (-((a - 3) * x))
  have hNpos := Real.exp_pos x
  -- (2(N+1)H) c <= 12 N H <= 22 x N
  have hfac : (2 * (Real.exp x + 1) * H) * c ≤ 22 * x * Real.exp x := by
    have h1 : 2 * (Real.exp x + 1) ≤ 4 * Real.exp x := by linarith
    have h2 : (2 * (Real.exp x + 1) * H) ≤ (4 * Real.exp x) * H :=
      mul_le_mul_of_nonneg_right h1 hH0
    have h3 : (2 * (Real.exp x + 1) * H) * c ≤ ((4 * Real.exp x) * H) * 3 :=
      mul_le_mul h2 hc hc0 (by positivity)
    have h4 : ((4 * Real.exp x) * H) * 3 ≤ ((4 * Real.exp x) * (11 / 6 * x)) * 3 := by
      have := mul_le_mul_of_nonneg_left hH (show 0 ≤ 4 * Real.exp x by positivity)
      linarith
    nlinarith
  calc (2 * (Real.exp x + 1) * H) * (c * Real.exp (-(a * x)))
      = ((2 * (Real.exp x + 1) * H) * c) * Real.exp (-(a * x)) := by ring
    _ ≤ (22 * x * Real.exp x) * Real.exp (-(a * x)) :=
        mul_le_mul_of_nonneg_right hfac hEa.le
    _ = (22 * x) * (Real.exp x * Real.exp (-(a * x))) := by ring
    _ = (22 * x) * (Real.exp (-(2 * x)) * Real.exp (-((a - 3) * x))) := by
        rw [hsplit]
    _ = Real.exp (-(2 * x)) * (22 * x * Real.exp (-((a - 3) * x))) := by ring
    _ ≤ Real.exp (-(2 * x)) * 1 := mul_le_mul_of_nonneg_left hkey hE.le
    _ = Real.exp (-(2 * x)) := by ring

end Real

/-! ## Calibration -/

private theorem calib {n : ℕ} (hn : timePopulationThreshold ≤ n) :
    ∃ x : ℝ, (n : ℝ) = Real.exp x ∧ 500000 ≤ x ∧ 40 ≤ (n : ℝ) ∧
      ((PhaseThreeModel.Numeric.hourIndex n : ℕ) : ℝ) + 1 ≤ 11 / 6 * x := by
  obtain ⟨h40, hpos, -, -, hH, -⟩ := time_hour_calibration hn
  have hL := Calibration.population_log_lower hn
  refine ⟨Real.log (n : ℝ), (Real.exp_log hpos).symm, (by linarith only [hL]), ?_, ?_⟩
  · exact_mod_cast h40
  · simpa [PhaseThreeModel.Numeric.clockHours] using hH

private theorem ofReal_nat_mul (m : ℕ) (y : ℝ) :
    ((m : ℕ) : ℝ≥0∞) * ENNReal.ofReal y = ENNReal.ofReal ((m : ℝ) * y) := by
  rw [ENNReal.ofReal_mul (Nat.cast_nonneg m), ENNReal.ofReal_natCast]

/-! ## Unit bounds -/

private theorem unit_eq {n : ℕ} {x : ℝ} (hnx : (n : ℝ) = Real.exp x) :
    1 / (n : ℝ) ^ 2 = Real.exp (-(2 * x)) := by
  rw [hnx]; exact exp_neg_two_mul.symm

/-- `n^(-a) <= 1/n^2` for `a >= 2`. -/
private theorem rpow_le_unit {n : ℕ} {x : ℝ} (hnx : (n : ℝ) = Real.exp x)
    (hx : 0 ≤ x) {a : ℝ} (ha : 2 ≤ a) :
    Real.rpow (n : ℝ) (-a) ≤ 1 / (n : ℝ) ^ 2 := by
  rw [unit_eq hnx, hnx, rpow_exp_neg]
  exact Real.exp_le_exp.mpr (by nlinarith)

/-- `c / n^k <= c / n^2` for `2 <= k`, `1 <= n`. -/
private theorem pow_le_unit {n : ℕ} {x : ℝ} (hnx : (n : ℝ) = Real.exp x)
    (hx : 0 ≤ x) {k : ℕ} (hk : 2 ≤ k) :
    1 / (n : ℝ) ^ k ≤ 1 / (n : ℝ) ^ 2 := by
  rw [unit_eq hnx, hnx, ← exp_neg_nat_mul]
  exact Real.exp_le_exp.mpr (by
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk
    nlinarith)

/-- `e^3 / n^3 <= 1 / n^2` once `n >= 40`. -/
private theorem exp_three_cube_le {n : ℕ} (h40 : 40 ≤ (n : ℝ)) :
    Real.exp 3 / (n : ℝ) ^ 3 ≤ 1 / (n : ℝ) ^ 2 := by
  have hn0 : 0 < (n : ℝ) := by linarith
  have he := time_exp_three_lt
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [pow_pos hn0 2, mul_pos hn0 (pow_pos hn0 2)]

/-- `e^3 / n^2 <= 21 / n^2`. -/
private theorem exp_three_sq_le {n : ℕ} (h40 : 40 ≤ (n : ℝ)) :
    Real.exp 3 / (n : ℝ) ^ 2 ≤ 21 / (n : ℝ) ^ 2 := by
  have hn0 : 0 < (n : ℝ) := by linarith
  exact div_le_div_of_nonneg_right time_exp_three_lt.le (by positivity)

/-! ## Term bounds -/

section Terms

variable {n : ℕ}

private theorem sum_ofReal_le {p q a b : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    (h1 : p ≤ a) (h2 : q ≤ b) :
    ENNReal.ofReal p + ENNReal.ofReal q ≤ ENNReal.ofReal (a + b) := by
  have ha : 0 ≤ a := hp.trans h1
  rw [ENNReal.ofReal_add ha (hq.trans h2)]
  exact add_le_add (ENNReal.ofReal_le_ofReal h1) (ENNReal.ofReal_le_ofReal h2)

private theorem add_ofReal {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ENNReal.ofReal a + ENNReal.ofReal b = ENNReal.ofReal (a + b) :=
  (ENNReal.ofReal_add ha hb).symm

/-- Scalar bound: `ofReal y <= ofReal (c / n^2)` from `y <= c * (1/n^2)`. -/
private theorem ofReal_le_c {y c : ℝ} {n : ℕ}
    (h : y ≤ c * (1 / (n : ℝ) ^ 2)) :
    ENNReal.ofReal y ≤ ENNReal.ofReal (c / (n : ℝ) ^ 2) := by
  apply ENNReal.ofReal_le_ofReal
  calc y ≤ c * (1 / (n : ℝ) ^ 2) := h
    _ = c / (n : ℝ) ^ 2 := by ring

/-- `ofReal (c / n^2)` adds. -/
private theorem unit_add (c d : ℝ) (hc : 0 ≤ c) (hd : 0 ≤ d) (n : ℕ) :
    ENNReal.ofReal (c / (n : ℝ) ^ 2) + ENNReal.ofReal (d / (n : ℝ) ^ 2) =
      ENNReal.ofReal ((c + d) / (n : ℝ) ^ 2) := by
  rw [← ENNReal.ofReal_add (by positivity) (by positivity), ← add_div]

private theorem sumU {A B : ℝ≥0∞} {a b c D : ℝ} (hD : 0 ≤ D) (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hA : A ≤ ENNReal.ofReal (a / D))
    (hB : B ≤ ENNReal.ofReal (b / D)) (hc : a + b = c) :
    A + B ≤ ENNReal.ofReal (c / D) := by
  calc A + B ≤ ENNReal.ofReal (a / D) + ENNReal.ofReal (b / D) := add_le_add hA hB
    _ = ENNReal.ofReal ((a + b) / D) := by
        rw [← ENNReal.ofReal_add (div_nonneg ha hD) (div_nonneg hb hD), add_div]
    _ = ENNReal.ofReal (c / D) := by rw [hc]

private theorem rpow_term (hn : timePopulationThreshold ≤ n) {a : ℝ} (ha : 2 ≤ a) :
    ENNReal.ofReal (Real.rpow (n : ℝ) (-a)) ≤ ENNReal.ofReal (1 / (n : ℝ) ^ 2) := by
  obtain ⟨x, hnx, hx, -, -⟩ := calib hn
  clear hn
  exact ENNReal.ofReal_le_ofReal (rpow_le_unit hnx (by linarith) ha)

private theorem pow_term (hn : timePopulationThreshold ≤ n) {k : ℕ} (hk : 2 ≤ k) :
    ENNReal.ofReal (1 / (n : ℝ) ^ k) ≤ ENNReal.ofReal (1 / (n : ℝ) ^ 2) := by
  obtain ⟨x, hnx, hx, -, -⟩ := calib hn
  clear hn
  exact ENNReal.ofReal_le_ofReal (pow_le_unit hnx (by linarith) hk)

private theorem exp_cube_term (hn : timePopulationThreshold ≤ n) :
    ENNReal.ofReal (Real.exp 3 / (n : ℝ) ^ 3) ≤ ENNReal.ofReal (1 / (n : ℝ) ^ 2) := by
  obtain ⟨x, hnx, hx, h40, -⟩ := calib hn
  clear hn
  exact ENNReal.ofReal_le_ofReal (exp_three_cube_le h40)

private theorem exp_sq_term (hn : timePopulationThreshold ≤ n) :
    ENNReal.ofReal (Real.exp 3 / (n : ℝ) ^ 2) ≤ ENNReal.ofReal (21 / (n : ℝ) ^ 2) := by
  obtain ⟨x, hnx, hx, h40, -⟩ := calib hn
  clear hn
  exact ENNReal.ofReal_le_ofReal (exp_three_sq_le h40)

private theorem exp_rpow_term (hn : timePopulationThreshold ≤ n) :
    ENNReal.ofReal (Real.exp 3 * Real.rpow (n : ℝ) (1 - (3 : ℝ))) ≤
      ENNReal.ofReal (21 / (n : ℝ) ^ 2) := by
  obtain ⟨x, hnx, hx, h40, -⟩ := calib hn
  clear hn
  apply ofReal_le_c
  have h1 : (1 - (3 : ℝ)) = -2 := by norm_num
  rw [h1]
  have h2 := rpow_le_unit hnx (by linarith) (a := 2) le_rfl
  have h3 := time_exp_three_lt
  have h4 : 0 ≤ Real.rpow (n : ℝ) (-2) := Real.rpow_nonneg (by linarith) _
  nlinarith

/-- The hour-index factor against `n^(-190)`. -/
private theorem selectedRowTwo_le (hn : timePopulationThreshold ≤ n) :
    selectedLevelRowTwoCharge n ≤ ENNReal.ofReal (1 / (n : ℝ) ^ 2) := by
  obtain ⟨x, hnx, hx, -, hH⟩ := calib hn
  clear hn
  unfold selectedLevelRowTwoCharge
  rw [ofReal_nat_mul]
  apply ENNReal.ofReal_le_ofReal
  rw [unit_eq hnx, hnx, rpow_exp_neg]
  push_cast
  exact hour_mul_le hx hH (by norm_num)

private theorem selectedDrain_le (hn : timePopulationThreshold ≤ n) :
    selectedLevelPhaseSixDrainCharge n ≤ ENNReal.ofReal (1 / (n : ℝ) ^ 2) := by
  obtain ⟨x, hnx, hx, -, hH⟩ := calib hn
  clear hn
  unfold selectedLevelPhaseSixDrainCharge phaseSixDrainBudget
  rw [ofReal_nat_mul]
  apply ENNReal.ofReal_le_ofReal
  rw [unit_eq hnx, hnx, rpow_exp_neg]
  push_cast
  exact hour_mul_le hx hH (by norm_num)

private theorem sevenWitness_le (hn : timePopulationThreshold ≤ n) :
    phaseSevenWitnessCharge n ≤ ENNReal.ofReal (1 / (n : ℝ) ^ 2) := by
  obtain ⟨x, hnx, hx, -, hH⟩ := calib hn
  clear hn
  unfold phaseSevenWitnessCharge phaseSevenBandsBudget phaseSevenSingleBandBudget
  have h3 : (3 : ℝ≥0∞) = ENNReal.ofReal 3 := by simp
  rw [h3, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3), ofReal_nat_mul]
  apply ENNReal.ofReal_le_ofReal
  rw [unit_eq hnx]
  push_cast
  rw [hnx, rpow_exp_neg]
  exact union_mul_le hx (by positivity) hH (by norm_num) (by norm_num) (by norm_num)

private theorem eightWitness_le (hn : timePopulationThreshold ≤ n) :
    phaseEightDrainWitnessCharge n ≤ ENNReal.ofReal (1 / (n : ℝ) ^ 2) := by
  obtain ⟨x, hnx, hx, -, hH⟩ := calib hn
  clear hn
  unfold phaseEightDrainWitnessCharge phaseEightDrainBudget
  rw [ofReal_nat_mul]
  apply ENNReal.ofReal_le_ofReal
  rw [unit_eq hnx]
  push_cast
  rw [hnx, rpow_exp_neg]
  have := union_mul_le (x := x) (H := (PhaseThreeModel.Numeric.hourIndex n : ℝ) + 1)
    (a := 9931 / 3125) (c := 1) hx (by positivity) hH (by norm_num) (by norm_num)
    (by norm_num)
  linarith

/-! ## Composite bounds -/

private theorem nSixteen_le (hn : timePopulationThreshold ≤ n) :
    nSixteenReceiptCharge n ≤ ENNReal.ofReal (5 / (n : ℝ) ^ 2) := by
  obtain ⟨x, hnx, hx, h40, -⟩ := calib hn
  clear hn
  have hx0 : 0 ≤ x := by linarith
  unfold nSixteenReceiptCharge
  apply ofReal_le_c
  have h4 := pow_le_unit hnx hx0 (k := 4) (by norm_num)
  have h207 := rpow_le_unit hnx hx0 (a := 207 / 100) (by norm_num)
  have h2 : 2 / (n : ℝ) ^ 2 = 2 * (1 / (n : ℝ) ^ 2) := by ring
  have h4' : 2 / (n : ℝ) ^ 4 = 2 * (1 / (n : ℝ) ^ 4) := by ring
  rw [h2, h4']
  have : Real.rpow (n : ℝ) (-(207 / 100 : ℝ)) ≤ 1 / (n : ℝ) ^ 2 := h207
  linarith

private theorem strongReceipt_le (hn : timePopulationThreshold ≤ n) :
    strongReceiptCharge n ≤ ENNReal.ofReal (4 / (n : ℝ) ^ 2) := by
  have hD : (0 : ℝ) ≤ (n : ℝ) ^ 2 := by positivity
  have hpair : ENNReal.ofReal (Real.exp 3 / (n : ℝ) ^ 3) +
      ENNReal.ofReal (Real.exp 3 / (n : ℝ) ^ 3) ≤ ENNReal.ofReal (2 / (n : ℝ) ^ 2) :=
    sumU (a := 1) (b := 1) hD (by norm_num) (by norm_num) (exp_cube_term hn)
      (exp_cube_term hn) (by norm_num)
  have hmid : ENNReal.ofReal (Real.rpow (n : ℝ) (-(103 / 50 : ℝ))) +
      (ENNReal.ofReal (Real.exp 3 / (n : ℝ) ^ 3) +
        ENNReal.ofReal (Real.exp 3 / (n : ℝ) ^ 3)) ≤
      ENNReal.ofReal (3 / (n : ℝ) ^ 2) :=
    sumU (a := 1) (b := 2) hD (by norm_num) (by norm_num) (rpow_term hn (by norm_num))
      hpair (by norm_num)
  unfold strongReceiptCharge
  exact sumU (a := 3) (b := 1) hD (by norm_num) (by norm_num) hmid
    (rpow_term hn (by norm_num)) (by norm_num)

private theorem strongSnapshot_le (hn : timePopulationThreshold ≤ n) :
    strongSnapshotCharge n ≤ ENNReal.ofReal (5 / (n : ℝ) ^ 2) := by
  have hD : (0 : ℝ) ≤ (n : ℝ) ^ 2 := by positivity
  unfold strongSnapshotCharge
  exact sumU (a := 4) (b := 1) hD (by norm_num) (by norm_num) (strongReceipt_le hn)
    (selectedRowTwo_le hn) (by norm_num)

private theorem smallRowTwo_le (hn : timePopulationThreshold ≤ n) :
    smallRowTwoSnapshotCharge n ≤ ENNReal.ofReal (10 / (n : ℝ) ^ 2) := by
  have hD : (0 : ℝ) ≤ (n : ℝ) ^ 2 := by positivity
  unfold smallRowTwoSnapshotCharge
  exact sumU (a := 5) (b := 5) hD (by norm_num) (by norm_num) (nSixteen_le hn)
    (strongSnapshot_le hn) (by norm_num)

private theorem selectedProduced_le (hn : timePopulationThreshold ≤ n) :
    selectedProducedLevelPhaseSixCharge n ≤ ENNReal.ofReal (23 / (n : ℝ) ^ 2) := by
  have hD : (0 : ℝ) ≤ (n : ℝ) ^ 2 := by positivity
  have hin : ENNReal.ofReal (Real.rpow (n : ℝ) (-(103 / 50 : ℝ))) +
      selectedLevelPhaseSixDrainCharge n ≤ ENNReal.ofReal (2 / (n : ℝ) ^ 2) :=
    sumU (a := 1) (b := 1) hD (by norm_num) (by norm_num) (rpow_term hn (by norm_num))
      (selectedDrain_le hn) (by norm_num)
  unfold selectedProducedLevelPhaseSixCharge
  exact sumU (a := 21) (b := 2) hD (by norm_num) (by norm_num) (exp_sq_term hn) hin
    (by norm_num)

private theorem smallGapSix_le (hn : timePopulationThreshold ≤ n) :
    smallGapPhaseSixDrainCharge n ≤ ENNReal.ofReal (35 / (n : ℝ) ^ 2) := by
  have hD : (0 : ℝ) ≤ (n : ℝ) ^ 2 := by positivity
  have h1 : ENNReal.ofReal (1 / (n : ℝ) ^ 5) + selectedProducedLevelPhaseSixCharge n ≤
      ENNReal.ofReal (24 / (n : ℝ) ^ 2) :=
    sumU (a := 1) (b := 23) hD (by norm_num) (by norm_num)
      (pow_term hn (k := 5) (by norm_num)) (selectedProduced_le hn) (by norm_num)
  have h2 : ENNReal.ofReal (1 / (n : ℝ) ^ 2) +
      (ENNReal.ofReal (1 / (n : ℝ) ^ 5) + selectedProducedLevelPhaseSixCharge n) ≤
      ENNReal.ofReal (25 / (n : ℝ) ^ 2) :=
    sumU (a := 1) (b := 24) hD (by norm_num) (by norm_num)
      (pow_term hn (k := 2) le_rfl) h1 (by norm_num)
  unfold smallGapPhaseSixDrainCharge
  exact sumU (a := 10) (b := 25) hD (by norm_num) (by norm_num) (smallRowTwo_le hn) h2
    (by norm_num)

private theorem lemmaEleven_le (hn : timePopulationThreshold ≤ n) :
    lemmaElevenFailureCharge n ≤ ENNReal.ofReal (59 / (n : ℝ) ^ 2) := by
  have hD : (0 : ℝ) ≤ (n : ℝ) ^ 2 := by positivity
  have h1 : ENNReal.ofReal (Real.exp 3 * Real.rpow (n : ℝ) (1 - (3 : ℝ))) +
      ENNReal.ofReal (Real.rpow (n : ℝ) (-(103 / 50 : ℝ))) ≤
      ENNReal.ofReal (22 / (n : ℝ) ^ 2) :=
    sumU (a := 21) (b := 1) hD (by norm_num) (by norm_num) (exp_rpow_term hn)
      (rpow_term hn (by norm_num)) (by norm_num)
  have h2 : (ENNReal.ofReal (Real.exp 3 * Real.rpow (n : ℝ) (1 - (3 : ℝ))) +
      ENNReal.ofReal (Real.rpow (n : ℝ) (-(103 / 50 : ℝ)))) +
        ENNReal.ofReal (1 / (n : ℝ) ^ 5) ≤ ENNReal.ofReal (23 / (n : ℝ) ^ 2) :=
    sumU (a := 22) (b := 1) hD (by norm_num) (by norm_num) h1
      (pow_term hn (k := 5) (by norm_num)) (by norm_num)
  have h3 : ENNReal.ofReal (1 / (n : ℝ) ^ 5) +
      ((ENNReal.ofReal (Real.exp 3 * Real.rpow (n : ℝ) (1 - (3 : ℝ))) +
        ENNReal.ofReal (Real.rpow (n : ℝ) (-(103 / 50 : ℝ)))) +
          ENNReal.ofReal (1 / (n : ℝ) ^ 5)) ≤ ENNReal.ofReal (24 / (n : ℝ) ^ 2) :=
    sumU (a := 1) (b := 23) hD (by norm_num) (by norm_num)
      (pow_term hn (k := 5) (by norm_num)) h2 (by norm_num)
  unfold lemmaElevenFailureCharge
  exact sumU (a := 35) (b := 24) hD (by norm_num) (by norm_num) (smallGapSix_le hn) h3
    (by norm_num)

private theorem lemmaTwelve_le (hn : timePopulationThreshold ≤ n) :
    lemmaTwelveFailureCharge n ≤ ENNReal.ofReal (60 / (n : ℝ) ^ 2) := by
  have hD : (0 : ℝ) ≤ (n : ℝ) ^ 2 := by positivity
  unfold lemmaTwelveFailureCharge
  exact sumU (a := 59) (b := 1) hD (by norm_num) (by norm_num) (lemmaEleven_le hn)
    (sevenWitness_le hn) (by norm_num)

private theorem eightHomogeneous_le (hn : timePopulationThreshold ≤ n) :
    phaseEightHomogeneousCharge n ≤ ENNReal.ofReal (22 / (n : ℝ) ^ 2) := by
  have hD : (0 : ℝ) ≤ (n : ℝ) ^ 2 := by positivity
  unfold phaseEightHomogeneousCharge
  exact sumU (a := 21) (b := 1) hD (by norm_num) (by norm_num) (exp_rpow_term hn)
    (rpow_term hn (by norm_num)) (by norm_num)

private theorem lemmaThirteenRoute_le (hn : timePopulationThreshold ≤ n) :
    lemmaThirteenRouteFailureCharge n ≤ ENNReal.ofReal (82 / (n : ℝ) ^ 2) := by
  have hD : (0 : ℝ) ≤ (n : ℝ) ^ 2 := by positivity
  unfold lemmaThirteenRouteFailureCharge
  exact sumU (a := 60) (b := 22) hD (by norm_num) (by norm_num) (lemmaTwelve_le hn)
    (eightHomogeneous_le hn) (by norm_num)

/-- The `main` charge through Lemma 13: coefficient 83 in units of `n^(-2)`. -/
theorem lemmaThirteenFailureCharge_le (hn : timePopulationThreshold ≤ n) :
    lemmaThirteenFailureCharge n ≤ ENNReal.ofReal (83 / (n : ℝ) ^ 2) := by
  have hD : (0 : ℝ) ≤ (n : ℝ) ^ 2 := by positivity
  unfold lemmaThirteenFailureCharge
  exact sumU (a := 82) (b := 1) hD (by norm_num) (by norm_num) (lemmaThirteenRoute_le hn)
    (eightWitness_le hn) (by norm_num)

/-- Lemma 14 charges: coefficient 3. -/
theorem lemmaFourteenCharge_le (hn : timePopulationThreshold ≤ n) :
    lemmaFourteenCharge n ≤ ENNReal.ofReal (3 / (n : ℝ) ^ 2) := by
  have hD : (0 : ℝ) ≤ (n : ℝ) ^ 2 := by positivity
  unfold lemmaFourteenCharge
  have h2 : ENNReal.ofReal (Real.exp 3 / (n : ℝ) ^ 3) +
      ENNReal.ofReal (Real.exp 3 / (n : ℝ) ^ 3) ≤ ENNReal.ofReal (2 / (n : ℝ) ^ 2) :=
    sumU (a := 1) (b := 1) hD (by norm_num) (by norm_num) (exp_cube_term hn)
      (exp_cube_term hn) (by norm_num)
  exact sumU (a := 2) (b := 1) hD (by norm_num) (by norm_num) h2
    (pow_term hn (k := 3) (by norm_num)) (by norm_num)

/-- Reserved upper exits: coefficient 2. -/
theorem lateUpperExitReserve_le (hn : timePopulationThreshold ≤ n) :
    lateUpperExitReserve n ≤ ENNReal.ofReal (2 / (n : ℝ) ^ 2) := by
  have hD : (0 : ℝ) ≤ (n : ℝ) ^ 2 := by positivity
  unfold lateUpperExitReserve
  exact sumU (a := 1) (b := 1) hD (by norm_num) (by norm_num)
    (pow_term hn (k := 5) (by norm_num)) (pow_term hn (k := 5) (by norm_num)) (by norm_num)

/-- The composition budget: the total late charge is at most `88 / n^2`. -/
theorem lateTotalCharge_le (hn : timePopulationThreshold ≤ n) :
    lateTotalCharge n ≤ ENNReal.ofReal (88 / (n : ℝ) ^ 2) := by
  have hD : (0 : ℝ) ≤ (n : ℝ) ^ 2 := by positivity
  unfold lateTotalCharge
  have h1 : lemmaThirteenFailureCharge n + lemmaFourteenCharge n ≤
      ENNReal.ofReal (86 / (n : ℝ) ^ 2) :=
    sumU (a := 83) (b := 3) hD (by norm_num) (by norm_num)
      (lemmaThirteenFailureCharge_le hn) (lemmaFourteenCharge_le hn) (by norm_num)
  exact sumU (a := 86) (b := 2) hD (by norm_num) (by norm_num) h1
    (lateUpperExitReserve_le hn) (by norm_num)

/-- Lemma 15: the total late charge is strictly below `100 n^(-2)`. -/
theorem lateTotalCharge_lt (hn : timePopulationThreshold ≤ n) :
    lateTotalCharge n < ENNReal.ofReal (100 / (n : ℝ) ^ 2) := by
  obtain ⟨x, hnx, hx, -, -⟩ := calib hn
  have hpos : 0 < (n : ℝ) ^ 2 := by rw [hnx]; positivity
  refine (lateTotalCharge_le hn).trans_lt ?_
  rw [ENNReal.ofReal_lt_ofReal_iff (by positivity)]
  exact div_lt_div_of_pos_right (by norm_num) hpos

end Terms

end Ripple.PopulationProtocol.ExactMajority.LateCompositionBudget
