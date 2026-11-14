import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockMainTerminal

/-!
# Scalar calibration for the terminal Main exponent

For every population `n` above `PhaseThreeModel.Numeric.populationThreshold`
there is a Bernstein parameter `lam` satisfying the three scalar fields of
`HourTerminalCertificate`: `0 ≤ lam`, `lam * mainJumpBound n < 3`, and the
exponent bound `≤ 1 / n ^ 30`.  The parameter is the Bernstein optimiser
`u / (N c² + c u / 3)` with `N = mainTerminalHorizon n`, `c = mainJumpBound n`,
`u = mainBarrierRise n`.
-/

noncomputable section

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockMainTerminal

open TimeTheorem PhaseThreeModel.Numeric Ripple.Probability

/-- The abstract Bernstein step: with the optimal parameter the exponent is
`-(u² / (2 (N c² + c u / 3)))`. -/
theorem bernstein_exponent_core {N c u L : ℝ} (hN : 0 < N) (hc : 0 < c)
    (hu : 0 < u)
    (hE : 30 * L ≤ u ^ 2 / (2 * (N * c ^ 2 + c * u / 3))) :
    u / (N * c ^ 2 + c * u / 3) * c < 3 ∧
      Real.exp (N * (bernstein_psi (u / (N * c ^ 2 + c * u / 3)) c * c ^ 2) -
        u / (N * c ^ 2 + c * u / 3) * u) ≤ Real.exp (-(30 * L)) := by
  have hv : 0 < N * c ^ 2 := by positivity
  have hvcup : 0 < N * c ^ 2 + c * u / 3 := by positivity
  refine ⟨?_, ?_⟩
  · rw [div_mul_eq_mul_div, div_lt_iff₀ hvcup]
    nlinarith
  · apply Real.exp_le_exp.mpr
    have hopt := bernstein_optimal hu hv hc.le
    simp only at hopt
    have e : N * (bernstein_psi (u / (N * c ^ 2 + c * u / 3)) c * c ^ 2) =
        bernstein_psi (u / (N * c ^ 2 + c * u / 3)) c * (N * c ^ 2) := by ring
    rw [e, hopt, neg_div]
    exact neg_le_neg hE

/-- A hundredth root of `x`, with the barrier power rewritten through it. -/
theorem exists_hundredth_root {x : ℝ} (hx : 0 < x) :
    ∃ t : ℝ, 0 < t ∧ t ^ 100 = x ∧ x ^ (-2 / 25 : ℝ) = (t ^ 8)⁻¹ := by
  refine ⟨x ^ ((1 : ℝ) / 100), Real.rpow_pos_of_pos hx _, ?_, ?_⟩
  · rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]
    norm_num
  · rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le, ← Real.rpow_neg hx.le]
    norm_num

/-- The horizon is at most `23000 n log n`. -/
theorem main_horizon_le {n : ℕ} (hn : 0 < (n : ℝ)) (hy : 6 ≤ Real.log (n : ℝ)) :
    (mainTerminalHorizon n : ℝ) ≤ 23000 * n * Real.log (n : ℝ) := by
  have hH := (hour_bounds hn hy).2.1
  have hL0 : 0 ≤ Real.log (n : ℝ) := by linarith
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.cast_pos.mp hn
  have hnL : 6 ≤ (n : ℝ) * Real.log (n : ℝ) := by nlinarith
  have h1 : (logWindow n 20000 : ℝ) ≤ 20000 * n * Real.log (n : ℝ) + 1 := by
    unfold logWindow
    push_cast
    exact (Nat.ceil_lt_add_one (by positivity)).le
  have h2 : (logWindow n 30 : ℝ) ≤ 30 * n * Real.log (n : ℝ) + 1 := by
    unfold logWindow
    push_cast
    exact (Nat.ceil_lt_add_one (by positivity)).le
  have h3 : (1150 : ℝ) * n * (clockHours n : ℝ) ≤
      1150 * n * ((11 / 6 : ℝ) * Real.log (n : ℝ)) :=
    mul_le_mul_of_nonneg_left hH (by positivity)
  unfold mainTerminalHorizon earlyHorizon
  push_cast
  nlinarith

/-- The horizon is positive. -/
theorem main_horizon_pos {n : ℕ} (hn : 0 < (n : ℝ)) (hy : 6 ≤ Real.log (n : ℝ)) :
    0 < (mainTerminalHorizon n : ℝ) := by
  have hL0 : 0 < Real.log (n : ℝ) := by linarith
  have h1 : 20000 * (n : ℝ) * Real.log (n : ℝ) ≤ (logWindow n 20000 : ℝ) := by
    unfold logWindow
    push_cast
    exact Nat.le_ceil _
  have h2 : (logWindow n 20000 : ℝ) ≤ (mainTerminalHorizon n : ℝ) := by
    unfold mainTerminalHorizon
    exact_mod_cast (by omega :
      logWindow n 20000 ≤ earlyHorizon n + logWindow n 20000 + logWindow n 30)
  have h3 : 0 < 20000 * (n : ℝ) * Real.log (n : ℝ) := by positivity
  linarith

/-- Exponent-parametric wrapper, so the large power is never reduced. -/
private def thresholdAt (e : ℕ) : ℕ := 5 * 2 ^ e

private theorem threshold_eq_at :
    PhaseThreeModel.Numeric.populationThreshold = thresholdAt (2 ^ 30) := by
  rfl

private theorem power_le_at {e : ℕ} (he : 1000 ≤ e) : 1000 ^ 100 ≤ thresholdAt e :=
  calc 1000 ^ 100 ≤ (2 ^ 10) ^ 100 := Nat.pow_le_pow_left (by norm_num) 100
    _ = 2 ^ 1000 := by rw [← pow_mul]
    _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
    _ ≤ thresholdAt e := Nat.le_mul_of_pos_left _ (by norm_num)

/-- The threshold gives `1000 ^ 100 ≤ n`, without evaluating the large power. -/
theorem power_le_of_threshold {n : ℕ}
    (hn : PhaseThreeModel.Numeric.populationThreshold ≤ n) :
    (1000 : ℝ) ^ 100 ≤ n := by
  rw [threshold_eq_at] at hn
  exact_mod_cast (power_le_at (by norm_num)).trans hn

/-- The scalar calibration of the terminal Main exponent. -/
theorem main_exponent_calibration {n : ℕ}
    (hn : PhaseThreeModel.Numeric.populationThreshold ≤ n) :
    ∃ lam : ℝ, 0 ≤ lam ∧ lam * mainJumpBound n < 3 ∧
      ENNReal.ofReal (Real.exp ((mainTerminalHorizon n : ℝ) *
          (bernstein_psi lam (mainJumpBound n) * mainJumpBound n ^ 2) -
            lam * mainBarrierRise n)) ≤
        ENNReal.ofReal (1 / (n : ℝ) ^ 30) := by
  have h2000 := power_le_of_threshold hn
  clear hn
  have hnpos : 0 < (n : ℝ) := lt_of_lt_of_le (by positivity) h2000
  obtain ⟨t, ht0, ht100, hrpow⟩ := exists_hundredth_root hnpos
  have ht1000 : (1000 : ℝ) ≤ t := by
    by_contra hlt
    rw [not_le] at hlt
    have h := pow_lt_pow_left₀ hlt ht0.le (by norm_num : (100 : ℕ) ≠ 0)
    rw [ht100] at h
    linarith
  clear h2000
  -- logarithm bounds
  have hLeq : Real.log (n : ℝ) = 100 * Real.log t := by
    rw [← ht100, Real.log_pow]
    norm_num
  have hlogt_hi : Real.log t ≤ t := by
    linarith [Real.log_le_sub_one_of_pos ht0]
  have hlogt_lo : 9 * (0.69 : ℝ) ≤ Real.log t := by
    have h := Real.log_le_log (by norm_num) (show (2 : ℝ) ^ 9 ≤ t by linarith)
    rw [Real.log_pow] at h
    push_cast at h
    linarith [Real.log_two_gt_d9]
  have hL6 : 6 ≤ Real.log (n : ℝ) := by rw [hLeq]; linarith
  have hLt : Real.log (n : ℝ) ≤ 100 * t := by rw [hLeq]; linarith
  -- the three quantities
  have hNle := main_horizon_le hnpos hL6
  have hNpos := main_horizon_pos hnpos hL6
  set N : ℝ := (mainTerminalHorizon n : ℝ) with hNdef
  set L : ℝ := Real.log (n : ℝ) with hLdef
  have hc : 0 < mainJumpBound n := by
    unfold mainJumpBound; positivity
  have hcn : mainJumpBound n * n = 10 := by
    unfold mainJumpBound; field_simp
  have hu_eq : mainBarrierRise n = 9 / 100000 * (t ^ 8)⁻¹ := by
    unfold mainBarrierRise
    rw [Real.rpow_eq_pow, hrpow]
  have ht8 : 1 ≤ t ^ 8 := one_le_pow₀ (by
    linarith)
  have ht8pos : 0 < t ^ 8 := by positivity
  have hu : 0 < mainBarrierRise n := by rw [hu_eq]; positivity
  have hut : mainBarrierRise n * t ^ 8 = 9 / 100000 := by
    rw [hu_eq]; field_simp
  have hu1 : mainBarrierRise n ≤ 1 := by nlinarith
  set c : ℝ := mainJumpBound n with hcdef
  set u : ℝ := mainBarrierRise n with hudef
  -- the key inequality
  have hKn : (N * c ^ 2 + c * u / 3) * n ≤ 2400000 * L := by
    have h1 : N * c ≤ 230000 * L := by
      have : N * c ≤ 23000 * n * L * c := mul_le_mul_of_nonneg_right hNle hc.le
      nlinarith
    have h2 : (N * c ^ 2 + c * u / 3) * n = N * c * 10 + 10 * u / 3 := by
      have : (N * c ^ 2 + c * u / 3) * n = N * c * (c * n) + c * n * u / 3 := by ring
      rw [this, hcn]
    rw [h2]
    nlinarith
  have hcrux : 30 * L ≤ u ^ 2 / (2 * (N * c ^ 2 + c * u / 3)) := by
    have hK : 0 < N * c ^ 2 + c * u / 3 := by positivity
    rw [le_div_iff₀ (by positivity)]
    have hnu : (n : ℝ) * u ^ 2 = t ^ 84 * (u * t ^ 8) ^ 2 := by
      rw [← ht100]; ring
    have ht82' : (180000000000000000000 : ℝ) ≤ t ^ 82 := by
      have h7 : (1000 : ℝ) ^ 7 ≤ t ^ 7 := pow_le_pow_left₀ (by norm_num) ht1000 7
      have h8 : t ^ 7 ≤ t ^ 82 :=
        pow_le_pow_right₀ (by linarith) (by norm_num)
      have h9 : (1000 : ℝ) ^ 7 = 1000000000000000000000 := by norm_num
      linarith
    have hL2 : L ^ 2 ≤ 10000 * t ^ 2 := by
      have hL0 : 0 ≤ L := by linarith
      nlinarith
    have hfin : 1440000000000 * t ^ 2 ≤ t ^ 84 * (9 / 100000 : ℝ) ^ 2 := by
      have : t ^ 84 = t ^ 2 * t ^ 82 := by ring
      rw [this]
      have ht2 : 0 < t ^ 2 := by positivity
      nlinarith
    refine le_of_mul_le_mul_left ?_ hnpos
    have hmain : (n : ℝ) * (30 * L * (2 * (N * c ^ 2 + c * u / 3))) =
        60 * L * ((N * c ^ 2 + c * u / 3) * n) := by ring
    rw [hmain, hnu, hut]
    have hL0 : 0 ≤ L := by linarith
    calc 60 * L * ((N * c ^ 2 + c * u / 3) * n)
        ≤ 60 * L * (2400000 * L) :=
          mul_le_mul_of_nonneg_left hKn (by positivity)
      _ = 144000000 * L ^ 2 := by ring
      _ ≤ 144000000 * (10000 * t ^ 2) := by nlinarith
      _ = 1440000000000 * t ^ 2 := by ring
      _ ≤ _ := hfin
  obtain ⟨hlam3, hexp⟩ := bernstein_exponent_core hNpos hc hu hcrux
  refine ⟨u / (N * c ^ 2 + c * u / 3), ?_, hlam3, ?_⟩
  · positivity
  · apply ENNReal.ofReal_le_ofReal
    refine hexp.trans (le_of_eq ?_)
    have h30 : (30 : ℝ) * L = Real.log ((n : ℝ) ^ 30) := by
      rw [Real.log_pow, hLdef]; norm_num
    rw [h30, Real.exp_neg, Real.exp_log (by positivity), one_div]

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockMainTerminal

end
