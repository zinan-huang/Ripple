-- Ripple/PopulationProtocol/ExactMajority/Probability/AveragingNumerics.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.ScalarTails
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingCancellationAlgebra

/-!
# Scalar calibration for the stopped averaging estimates

All large-population comparisons use public logarithmic bounds. In fact the
public averaging bound log n >= 600 suffices for the fixed-exponential
comparison below; no enormous population power is reduced.
-/

noncomputable section

namespace Ripple.PopulationProtocol.ExactMajority.AveragingNumerics

open TimeTheorem

/-- `Real.rpow` form of `Real.rpow_def_of_pos`, since the definitions below use
`Real.rpow` literally and `rw` does not see through it. -/
theorem rpow_def' {x : ℝ} (hx : 0 < x) (y : ℝ) :
    Real.rpow x y = Real.exp (Real.log x * y) :=
  Real.rpow_def_of_pos hx y

def potentialTrials (n M : ℕ) : ℕ :=
  Nat.ceil ((60 : ℝ) * (n : ℝ) ^ 2 / (M : ℝ))

def potentialTarget (M : ℕ) : ℝ := (M : ℝ) / 1000

def potentialDrift (n M : ℕ) : ℝ :=
  (17 / 100 : ℝ) * (M : ℝ) / (n : ℝ) ^ 2

def atomBound (n : ℕ) : ℝ := Real.rpow (n : ℝ) (47 / 100)

def logJumpBound (n : ℕ) : ℝ :=
  20000 * Real.rpow (n : ℝ) (-53 / 100)

def oldCutoff (n : ℕ) : ℕ := Nat.floor (Real.log (n : ℝ) / 3)

theorem population_log_lower {n : ℕ} (hn : timePopulationThreshold ≤ n) :
    0 < (n : ℝ) ∧ 600 ≤ Real.log (n : ℝ) := by
  have hpos := (time_hour_calibration hn).2.1
  have hlog := Calibration.population_log_lower hn
  exact ⟨hpos, by linarith only [hlog]⟩

theorem exp_cubic_lower {x : ℝ} (hx : 0 ≤ x) :
    x ^ 3 / 6 ≤ Real.exp x := by
  have h := Real.sum_le_exp_of_nonneg hx 4
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  nlinarith only [h, hx, sq_nonneg x]

theorem exp_quadratic_lower {x : ℝ} (hx : 0 ≤ x) :
    x ^ 2 / 2 ≤ Real.exp x := by
  have h := Real.sum_le_exp_of_nonneg hx 3
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  nlinarith only [h, hx]

theorem exp_neg_log_nat {x : ℝ} (hx : 0 < x) (k : ℕ) :
    Real.exp (-((k : ℝ) * Real.log x)) = 1 / x ^ k := by
  rw [Real.exp_neg, Real.exp_nat_mul, Real.exp_log hx, one_div]

/-- A fixed Taylor certificate at 36, extended by the linear exponential bound. -/
theorem cubic_growth_dominates_log {x : ℝ} (hx : 600 ≤ x) :
    20 * x ≤ Real.exp ((3 / 50 : ℝ) * x) / 100000000000 := by
  have hone : (8 / 3 : ℝ) ≤ Real.exp 1 := by
    have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1) 4
    norm_num [Finset.sum_range_succ, Nat.factorial] at h
    linarith
  have hpow : (8 / 3 : ℝ) ^ 36 ≤ (Real.exp 1) ^ 36 := by
    gcongr <;> linarith only [hone]
  have hfixed : (1200000000000000 : ℝ) ≤ Real.exp 36 := by
    rw [show (36 : ℝ) = (36 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
    exact (by norm_num : (1200000000000000 : ℝ) ≤ (8 / 3 : ℝ) ^ 36).trans hpow
  have hrem : 0 ≤ (3 / 50 : ℝ) * (x - 600) := by linarith
  have hlinear := Real.add_one_le_exp ((3 / 50 : ℝ) * (x - 600))
  have hmul := mul_le_mul hfixed hlinear (by linarith) (Real.exp_nonneg 36)
  have heq : Real.exp 36 * Real.exp ((3 / 50 : ℝ) * (x - 600)) =
      Real.exp ((3 / 50 : ℝ) * x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [heq] at hmul
  nlinarith only [hmul, hx]

theorem logarithmic_tail_le_inverse_power {n : ℕ}
    (hn : timePopulationThreshold ≤ n) :
    Real.exp (-Real.rpow (n : ℝ) (3 / 50) / 100000000000) ≤
      1 / (n : ℝ) ^ 20 := by
  obtain ⟨hpos, hlog⟩ := population_log_lower hn
  have hcompare := cubic_growth_dominates_log hlog
  have hrpow : Real.rpow (n : ℝ) (3 / 50) =
      Real.exp ((3 / 50 : ℝ) * Real.log (n : ℝ)) := by
    rw [rpow_def' hpos]
    congr 1
    ring
  rw [hrpow]
  calc
    Real.exp (-Real.exp ((3 / 50 : ℝ) * Real.log (n : ℝ)) / 100000000000) ≤
        Real.exp (-(20 * Real.log (n : ℝ))) :=
      Real.exp_le_exp.mpr (by linarith only [hcompare])
    _ = 1 / (n : ℝ) ^ 20 := exp_neg_log_nat hpos 20

theorem mass_log_comparison {n M : ℕ}
    (hn : timePopulationThreshold ≤ n) (hmain : 12 * n ≤ 25 * M) :
    20 * Real.log (n : ℝ) ≤ (M : ℝ) / 1000 := by
  obtain ⟨hpos, hlog⟩ := population_log_lower hn
  have hx : 0 ≤ Real.log (n : ℝ) := by linarith
  have hcube := exp_cubic_lower hx
  rw [Real.exp_log hpos] at hcube
  have hsq : (250000 : ℝ) ≤ Real.log (n : ℝ) ^ 2 := by
    nlinarith only [hlog, sq_nonneg (Real.log (n : ℝ) - 600)]
  have hprod := mul_le_mul_of_nonneg_right hsq hx
  have hm : (12 : ℝ) * n ≤ 25 * (M : ℝ) := by exact_mod_cast hmain
  nlinarith only [hcube, hprod, hm]

theorem mass_tail_le_inverse_power {n M : ℕ}
    (hn : timePopulationThreshold ≤ n) (hmain : 12 * n ≤ 25 * M) :
    Real.exp (-(M : ℝ) / 1000) ≤ 1 / (n : ℝ) ^ 20 := by
  have hpos := (population_log_lower hn).1
  calc
    Real.exp (-(M : ℝ) / 1000) ≤ Real.exp (-(20 * Real.log (n : ℝ))) :=
      Real.exp_le_exp.mpr (by linarith only [mass_log_comparison hn hmain])
    _ = 1 / (n : ℝ) ^ 20 := exp_neg_log_nat hpos 20

theorem faster_mass_tail_le_inverse_power {n M : ℕ}
    (hn : timePopulationThreshold ≤ n) (hmain : 12 * n ≤ 25 * M)
    {d : ℝ} (hd : 0 < d) (hdsmall : d ≤ 1000) :
    Real.exp (-(M : ℝ) / d) ≤ 1 / (n : ℝ) ^ 20 := by
  have hquot : (M : ℝ) / 1000 ≤ (M : ℝ) / d :=
    div_le_div_of_nonneg_left (Nat.cast_nonneg M) hd hdsmall
  exact (Real.exp_le_exp.mpr (by simp only [neg_div]; linarith only [hquot])).trans
    (mass_tail_le_inverse_power hn hmain)

theorem potentialTrials_le {n M : ℕ} (hn : 1 ≤ n)
    (hmain : 12 * n ≤ 25 * M) :
    (potentialTrials n M : ℝ) ≤ 126 * (n : ℝ) := by
  have hM : 0 < M := by omega
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hmainr : (12 : ℝ) * n ≤ 25 * (M : ℝ) := by exact_mod_cast hmain
  have hbase : (60 : ℝ) * (n : ℝ) ^ 2 / M ≤ 125 * (n : ℝ) := by
    apply (div_le_iff₀ hMr).2
    have hmul := mul_le_mul_of_nonneg_left hmainr (Nat.cast_nonneg n)
    nlinarith only [hmul]
  have hceil :
      (potentialTrials n M : ℝ) < (60 : ℝ) * (n : ℝ) ^ 2 / M + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  linarith only [hceil, hbase, hnr]

theorem potential_compensation_lower {n M : ℕ}
    (hn : 0 < n) (hM : 0 < M) :
    (51 / 5 : ℝ) ≤ potentialDrift n M * potentialTrials n M := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hceil : (60 : ℝ) * (n : ℝ) ^ 2 / M ≤
      (potentialTrials n M : ℝ) := Nat.le_ceil _
  have hscale := mul_le_mul_of_nonneg_left hceil
    (show 0 ≤ potentialDrift n M by unfold potentialDrift; positivity)
  have hcancel : potentialDrift n M * ((60 : ℝ) * (n : ℝ) ^ 2 / M) =
      51 / 5 := by
    unfold potentialDrift
    field_simp [ne_of_gt hnr, ne_of_gt hMr]
    <;> ring
  rwa [hcancel] at hscale

theorem log_initial_ratio_lt : Real.log (412 : ℝ) < 7 := by
  apply (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 412)).2
  have h := Real.sum_le_exp_of_nonneg (x := (7 : ℝ)) (by norm_num) 7
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  linarith only [h]

theorem compensated_work_exceeds_three {n M : ℕ}
    (hn : 0 < n) (hM : 0 < M) :
    3 < potentialDrift n M * potentialTrials n M - Real.log 412 := by
  linarith only [potential_compensation_lower hn hM, log_initial_ratio_lt]

theorem logJumpBound_pos {n : ℕ} (hn : 0 < n) :
    0 < logJumpBound n := by
  unfold logJumpBound
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  exact mul_pos (by norm_num) (Real.rpow_pos_of_pos hnr _)

/-- The literal bounded-increment denominator from the maximal inequality. -/
theorem freedman_exponent_calibration {n N : ℕ}
    (hn : timePopulationThreshold ≤ n)
    (hN : (N : ℝ) ≤ 126 * (n : ℝ)) :
    Real.exp (-9 / (2 * ((N : ℝ) * logJumpBound n ^ 2 + 2 * logJumpBound n))) ≤
      Real.exp (-Real.rpow (n : ℝ) (3 / 50) / 100000000000) := by
  obtain ⟨hnpos, hlog⟩ := population_log_lower hn
  let x := Real.log (n : ℝ)
  let e := Real.exp (-(53 / 100 : ℝ) * x)
  let f := Real.exp (-(3 / 50 : ℝ) * x)
  let z := Real.exp ((3 / 50 : ℝ) * x)
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hepos : 0 < e := Real.exp_pos _
  have hfpos : 0 < f := Real.exp_pos _
  have hzpos : 0 < z := Real.exp_pos _
  have hb : logJumpBound n = 20000 * e := by
    unfold logJumpBound
    rw [rpow_def' hnpos]
    dsimp [e, x]
    congr 2
    ring
  have hne : (n : ℝ) * e ^ 2 = f := by
    calc
      (n : ℝ) * e ^ 2 =
          Real.exp x * (Real.exp (-(53 / 100 : ℝ) * x) *
            Real.exp (-(53 / 100 : ℝ) * x)) := by
              rw [show Real.exp x = (n : ℝ) from Real.exp_log hnpos]
              simp only [e, pow_two]
      _ = Real.exp (x + (-(53 / 100 : ℝ) * x + -(53 / 100 : ℝ) * x)) := by
        rw [← Real.exp_add, ← Real.exp_add]
      _ = f := by
        dsimp [f]
        congr 1
        ring
  have hef : e ≤ f := Real.exp_le_exp.mpr (by show -(53 / 100 : ℝ) * x ≤ -(3 / 50 : ℝ) * x; nlinarith only [hx])
  have hfz : f * z = 1 := by
    dsimp [f, z]
    rw [← Real.exp_add]
    convert Real.exp_zero using 1 <;> congr 1 <;> ring
  have hrpow : Real.rpow (n : ℝ) (3 / 50) = z := by
    rw [rpow_def' hnpos]
    dsimp [z, x]
    congr 1
    ring
  let den := 2 * ((N : ℝ) * logJumpBound n ^ 2 + 2 * logJumpBound n)
  have hden : 0 < den := by dsimp [den]; rw [hb]; positivity
  have hdenbound : den ≤ 900000000000 * f := by
    calc
      den ≤ 2 * (126 * (n : ℝ) * logJumpBound n ^ 2 + 2 * logJumpBound n) := by
        dsimp [den]
        gcongr <;> linarith only [hone]
      _ = 100800000000 * f + 80000 * e := by
        rw [hb]
        nlinarith only [hne]
      _ ≤ 900000000000 * f := by
        nlinarith only [hef, hfpos]
  have hquot : z / 100000000000 ≤ 9 / den := by
    apply (le_div_iff₀ hden).2
    have hmul := mul_le_mul_of_nonneg_left hdenbound
      (show 0 ≤ z / 100000000000 by positivity)
    have hid : z / 100000000000 * (900000000000 * f) = 9 := by
      nlinarith only [hfz]
    nlinarith only [hmul, hid]
  change Real.exp (-9 / den) ≤ _
  rw [hrpow]
  exact Real.exp_le_exp.mpr (by simp only [neg_div]; linarith only [hquot])

theorem freedman_tail_le_inverse_power {n N : ℕ}
    (hn : timePopulationThreshold ≤ n)
    (hN : (N : ℝ) ≤ 126 * (n : ℝ)) :
    Real.exp (-9 / (2 * ((N : ℝ) * logJumpBound n ^ 2 + 2 * logJumpBound n))) ≤
      1 / (n : ℝ) ^ 20 :=
  (freedman_exponent_calibration hn hN).trans
    (logarithmic_tail_le_inverse_power hn)

/-- The fixed potential contracts over q-6 sequential early work blocks. -/
theorem old_blocks_exponent {n : ℕ}
    (hn : timePopulationThreshold ≤ n) :
    (1 / 1000 : ℝ) * n * Real.exp (-77 * ((oldCutoff n : ℝ) - 6)) ≤
      1 / (n : ℝ) ^ 20 := by
  obtain ⟨hnpos, hlog⟩ := population_log_lower hn
  have hfloor : Real.log (n : ℝ) / 3 - 1 < (oldCutoff n : ℝ) := by
    have h := Nat.lt_floor_add_one (Real.log (n : ℝ) / 3)
    dsimp [oldCutoff]
    linarith only [h]
  have hlog0 : 0 ≤ Real.log (n : ℝ) := by linarith
  have hexp : Real.log (n : ℝ) - 77 * ((oldCutoff n : ℝ) - 6) ≤
      -(20 * Real.log (n : ℝ)) := by
    linarith only [hfloor, hlog]
  calc
    (1 / 1000 : ℝ) * n * Real.exp (-77 * ((oldCutoff n : ℝ) - 6)) ≤
        (n : ℝ) * Real.exp (-77 * ((oldCutoff n : ℝ) - 6)) := by
      have hnonneg : 0 ≤ (n : ℝ) * Real.exp (-77 * ((oldCutoff n : ℝ) - 6)) :=
        mul_nonneg hnpos.le (Real.exp_nonneg _)
      nlinarith only [hnonneg]
    _ = Real.exp (Real.log (n : ℝ) - 77 * ((oldCutoff n : ℝ) - 6)) := by
      rw [Real.exp_sub, Real.exp_log hnpos, div_eq_mul_inv, ← Real.exp_neg, neg_mul]
    _ ≤ Real.exp (-(20 * Real.log (n : ℝ))) := Real.exp_le_exp.mpr hexp
    _ = 1 / (n : ℝ) ^ 20 := exp_neg_log_nat hnpos 20

theorem atomBound_nonneg {n : ℕ} (hn : 0 < (n : ℝ)) :
    0 ≤ atomBound n := (Real.rpow_pos_of_pos hn _).le

theorem atom_decay_identity {n : ℕ} (hn : 0 < (n : ℝ)) :
    atomBound n = (n : ℝ) * Real.rpow (n : ℝ) (-53 / 100) := by
  have h := Real.exp_add (Real.log (n : ℝ))
    (Real.log (n : ℝ) * (-53 / 100))
  have hexp : Real.log (n : ℝ) +
      Real.log (n : ℝ) * (-53 / 100) =
      Real.log (n : ℝ) * (47 / 100) := by ring
  rw [hexp, Real.exp_log hn] at h
  simpa only [atomBound, rpow_def' hn] using h

theorem atom_reciprocal_identity {n : ℕ} (hn : 0 < (n : ℝ)) :
    atomBound n * Real.rpow (n : ℝ) (53 / 100) = (n : ℝ) := by
  unfold atomBound
  rw [rpow_def' hn, rpow_def' hn, ← Real.exp_add]
  convert Real.exp_log hn using 1 <;> congr 1 <;> ring

theorem atomBound_ge_one {n : ℕ} (hn : timePopulationThreshold ≤ n) :
    1 ≤ atomBound n := by
  obtain ⟨hpos, hlog⟩ := population_log_lower hn
  have hexp : Real.exp 0 ≤
      Real.exp (Real.log (n : ℝ) * (47 / 100)) :=
    Real.exp_le_exp.mpr (by nlinarith only [hlog])
  simpa only [Real.exp_zero, atomBound, rpow_def' hpos] using hexp

theorem reciprocal_atom_large {n : ℕ} (hn : timePopulationThreshold ≤ n) :
    5000 ≤ Real.rpow (n : ℝ) (53 / 100) := by
  obtain ⟨hpos, hlog⟩ := population_log_lower hn
  rw [rpow_def' hpos]
  have hx : 0 ≤ Real.log (n : ℝ) * (53 / 100) := by linarith
  have h := exp_quadratic_lower hx
  have hs : (318 : ℝ) ≤ Real.log (n : ℝ) * (53 / 100) := by linarith
  nlinarith only [h, hs, sq_nonneg (Real.log (n : ℝ) * (53 / 100) - 318)]

theorem atomBound_le_half_target {n M : ℕ}
    (hn : timePopulationThreshold ≤ n) (hmain : 12 * n ≤ 25 * M) :
    atomBound n ≤ potentialTarget M / 2 := by
  have hnpos := (population_log_lower hn).1
  have hid := atom_reciprocal_identity hnpos
  have hmul := mul_le_mul_of_nonneg_left (reciprocal_atom_large hn)
    (atomBound_nonneg hnpos)
  rw [hid] at hmul
  have hm : (12 : ℝ) * n ≤ 25 * (M : ℝ) := by exact_mod_cast hmain
  unfold potentialTarget
  nlinarith only [hmul, hm]

theorem compensated_jump_bound {n M : ℕ}
    (hn : timePopulationThreshold ≤ n) (hmain : 12 * n ≤ 25 * M)
    (hMn : M ≤ n) :
    2 * atomBound n / potentialTarget M + potentialDrift n M ≤ logJumpBound n := by
  have hnpos := (population_log_lower hn).1
  have hnNat : 0 < n := by exact_mod_cast hnpos
  have hM : 0 < M := by omega
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hm : (12 : ℝ) * n ≤ 25 * (M : ℝ) := by exact_mod_cast hmain
  have hmn : (M : ℝ) ≤ n := by exact_mod_cast hMn
  let e := Real.rpow (n : ℝ) (-53 / 100)
  have hepos : 0 < e := Real.rpow_pos_of_pos hnpos _
  have hid : atomBound n = (n : ℝ) * e := atom_decay_identity hnpos
  have htarget : 0 < potentialTarget M := by unfold potentialTarget; positivity
  have hratio : 2 * atomBound n / potentialTarget M ≤ 5000 * e := by
    apply (div_le_iff₀ htarget).2
    have hbase : 2 * (n : ℝ) ≤ 5 * (M : ℝ) := by linarith only [hm]
    have hmul := mul_le_mul_of_nonneg_right hbase hepos.le
    rw [hid]
    unfold potentialTarget
    nlinarith only [hmul]
  have hdrift : potentialDrift n M ≤ e := by
    unfold potentialDrift
    apply (div_le_iff₀ (pow_pos hnpos 2)).2
    have ha := mul_le_mul_of_nonneg_left (atomBound_ge_one hn) hnpos.le
    have hrate : (17 / 100 : ℝ) * (M : ℝ) ≤ (n : ℝ) := by
      nlinarith only [hmn, (Nat.cast_nonneg M : (0 : ℝ) ≤ M)]
    calc
      (17 / 100 : ℝ) * (M : ℝ) ≤ (n : ℝ) := hrate
      _ ≤ (n : ℝ) * atomBound n := by simpa only [mul_one] using ha
      _ = e * (n : ℝ) ^ 2 := by rw [hid]; ring
  unfold logJumpBound
  change 2 * atomBound n / potentialTarget M + potentialDrift n M ≤ 20000 * e
  linarith only [hratio, hdrift, hepos]

theorem oldCutoff_lower {n : ℕ} (hn : timePopulationThreshold ≤ n) :
    6 ≤ oldCutoff n := by
  have hlog := (population_log_lower hn).2
  have hfloor := Nat.lt_floor_add_one (Real.log (n : ℝ) / 3)
  have hr : (6 : ℝ) ≤ (oldCutoff n : ℝ) := by
    dsimp [oldCutoff]
    linarith only [hfloor, hlog]
  exact_mod_cast hr

theorem old_atom_bound {n : ℕ} (hn : timePopulationThreshold ≤ n) :
    (4 : ℝ) ^ oldCutoff n ≤ atomBound n := by
  obtain ⟨hpos, hlog⟩ := population_log_lower hn
  have hlogzero : 0 ≤ Real.log (n : ℝ) := by linarith only [hlog]
  have hfloor : (oldCutoff n : ℝ) ≤ Real.log (n : ℝ) / 3 :=
    Nat.floor_le (by positivity)
  have hfour : Real.log (4 : ℝ) ≤ 25 / 18 := by
    have heq : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, Real.log_pow]
      norm_num
    rw [heq]
    linarith only [PhaseThreeModel.Numeric.log_two_bounds.2]
  have hfirst := mul_le_mul_of_nonneg_left hfour (Nat.cast_nonneg (oldCutoff n))
  have hsecond := mul_le_mul_of_nonneg_left hfloor
    (show (0 : ℝ) ≤ 25 / 18 by norm_num)
  have hexp : (oldCutoff n : ℝ) * Real.log 4 ≤
      Real.log (n : ℝ) * (47 / 100) := by
    nlinarith only [hfirst, hsecond, hlogzero]
  calc
    (4 : ℝ) ^ oldCutoff n =
        Real.exp ((oldCutoff n : ℝ) * Real.log 4) := by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 4)]
    _ ≤ Real.exp (Real.log (n : ℝ) * (47 / 100)) :=
      Real.exp_le_exp.mpr hexp
    _ = atomBound n := by
      rw [atomBound, rpow_def' hpos]

theorem old_blocks_natural_exponent {n : ℕ}
    (hn : timePopulationThreshold ≤ n) :
    (1 / 1000 : ℝ) * n * Real.exp (-77 * ((oldCutoff n - 6 : ℕ) : ℝ)) ≤
      1 / (n : ℝ) ^ 20 := by
  simpa only [Nat.cast_sub (oldCutoff_lower hn), Nat.cast_ofNat] using
    old_blocks_exponent hn

theorem hour_test_union_scalar {n : ℕ}
    (hn : timePopulationThreshold ≤ n) :
    10 * (PhaseThreeModel.Numeric.clockHours n : ℝ) / (n : ℝ) ^ 20 ≤
      1 / (n : ℝ) ^ 4 := by
  obtain ⟨hnforty, hnpos, -, -, -, hH⟩ := time_hour_calibration hn
  have hnr : (40 : ℝ) ≤ n := by exact_mod_cast hnforty
  have hHr : (PhaseThreeModel.Numeric.clockHours n : ℝ) ≤ n := by
    exact_mod_cast hH
  have hnunit : (1 : ℝ) ≤ n := by linarith only [hnr]
  have hp : (n : ℝ) ≤ (n : ℝ) ^ 15 := by
    simpa only [pow_one] using
      pow_le_pow_right₀ hnunit (show (1 : ℕ) ≤ 15 by decide)
  have hmul : 10 * (PhaseThreeModel.Numeric.clockHours n : ℝ) ≤
      (n : ℝ) ^ 16 := by
    have hstep := mul_le_mul_of_nonneg_left hp hnpos.le
    rw [show (n : ℝ) * (n : ℝ) ^ 15 = (n : ℝ) ^ 16 by ring] at hstep
    have hsq : 10 * (n : ℝ) ≤ (n : ℝ) ^ 2 := by
      nlinarith only [hnr]
    nlinarith only [hHr, hstep, hsq]
  calc
    10 * (PhaseThreeModel.Numeric.clockHours n : ℝ) / (n : ℝ) ^ 20 ≤
        (n : ℝ) ^ 16 / (n : ℝ) ^ 20 :=
      div_le_div_of_nonneg_right hmul (pow_pos hnpos 20).le
    _ = 1 / (n : ℝ) ^ 4 := by
      field_simp [ne_of_gt hnpos]
      <;> ring

/-- The three-bit exponential test uses log 8, kept as an exact logarithm. -/
theorem log_eight_lower : (2 : ℝ) ≤ Real.log 8 := by
  have heq : Real.log (8 : ℝ) = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = (2 : ℝ) ^ 3 by norm_num, Real.log_pow]
    norm_num
  rw [heq]
  linarith only [PhaseThreeModel.Numeric.log_two_bounds.1]

theorem warmup_death_coefficient {x : ℝ} (hx : 899 / 100 ≤ x) :
    7 * Real.exp (-x) - (1 / 500 : ℝ) * Real.log 8 ≤ -(1 / 500 : ℝ) := by
  have hpower : (12 : ℝ) * Real.log 2 ≤ x := by
    linarith only [hx, PhaseThreeModel.Numeric.log_two_bounds.2]
  have hexp : Real.exp (-x) ≤ 1 / (2 : ℝ) ^ 12 := by
    calc
      Real.exp (-x) ≤ Real.exp (-(12 * Real.log 2)) :=
        Real.exp_le_exp.mpr (neg_le_neg hpower)
      _ = 1 / (2 : ℝ) ^ 12 := exp_neg_log_nat (by norm_num) 12
  norm_num only [show (2 : ℝ) ^ 12 = 4096 by norm_num] at hexp
  linarith only [hexp, log_eight_lower]

theorem terminal_death_coefficient {x : ℝ} (hx : 57 / 5 ≤ x) :
    7 * Real.exp (-x) - (1 / 1000 : ℝ) * Real.log 8 ≤ -(1 / 600 : ℝ) := by
  have hpower : (16 : ℝ) * Real.log 2 ≤ x := by
    linarith only [hx, PhaseThreeModel.Numeric.log_two_bounds.2]
  have hexp : Real.exp (-x) ≤ 1 / (2 : ℝ) ^ 16 := by
    calc
      Real.exp (-x) ≤ Real.exp (-(16 * Real.log 2)) :=
        Real.exp_le_exp.mpr (neg_le_neg hpower)
      _ = 1 / (2 : ℝ) ^ 16 := exp_neg_log_nat (by norm_num) 16
  norm_num only [show (2 : ℝ) ^ 16 = 65536 by norm_num] at hexp
  linarith only [hexp, log_eight_lower]

theorem warmup_death_exponent {x M : ℝ} (hx : 899 / 100 ≤ x) (hM : 0 ≤ M) :
    Real.exp ((7 * Real.exp (-x) - (1 / 500 : ℝ) * Real.log 8) * M) ≤
      Real.exp (-M / 500) := by
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_right (warmup_death_coefficient hx) hM
  linarith only [h]

theorem terminal_death_exponent {x M : ℝ} (hx : 57 / 5 ≤ x) (hM : 0 ≤ M) :
    Real.exp ((7 * Real.exp (-x) - (1 / 1000 : ℝ) * Real.log 8) * M) ≤
      Real.exp (-M / 600) := by
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_right (terminal_death_coefficient hx) hM
  linarith only [h]

theorem warmup_death_tail_le_inverse_power {n M : ℕ} {x : ℝ}
    (hn : timePopulationThreshold ≤ n) (hmain : 12 * n ≤ 25 * M)
    (hx : 899 / 100 ≤ x) :
    Real.exp ((7 * Real.exp (-x) - (1 / 500 : ℝ) * Real.log 8) * (M : ℝ)) ≤
      1 / (n : ℝ) ^ 20 :=
  (warmup_death_exponent hx (Nat.cast_nonneg M)).trans
    (faster_mass_tail_le_inverse_power hn hmain (by norm_num) (by norm_num))

theorem terminal_death_tail_le_inverse_power {n M : ℕ} {x : ℝ}
    (hn : timePopulationThreshold ≤ n) (hmain : 12 * n ≤ 25 * M)
    (hx : 57 / 5 ≤ x) :
    Real.exp ((7 * Real.exp (-x) - (1 / 1000 : ℝ) * Real.log 8) * (M : ℝ)) ≤
      1 / (n : ℝ) ^ 20 :=
  (terminal_death_exponent hx (Nat.cast_nonneg M)).trans
    (faster_mass_tail_le_inverse_power hn hmain (by norm_num) (by norm_num))

end Ripple.PopulationProtocol.ExactMajority.AveragingNumerics

end
