/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.RelaxedBandAdaptiveSchedule
import Tri.RatioExp

/-!
# Quantitative error bounds for relaxed dyadic rungs

This file separates the productive-event quota from the raw clock.  The
productive quota is `64RP`, while the raw horizon is `4096CRn`.  The
independent factor `C` absorbs the fixed inverse firing rate.
-/

namespace Tri

open scoped ENNReal

/-- A Bernoulli half-clock is exponentially small whenever its real-valued
drift budget pays for both the requested exponent and the denominator. -/
theorem bernoulliHalf_clock_error_le
    (p : ℝ≥0∞) (T M E : ℕ)
    (hpTop : p ≠ ⊤) (hpOne : p ≤ 1)
    (hbudget :
      (E : ℝ) + (M : ℝ) ≤ p.toReal * (T : ℝ) / 2) :
    ((1 - p) + p * ((1 : ℝ≥0∞) / 2)) ^ T /
        ((1 : ℝ≥0∞) / 2) ^ M ≤
      ENNReal.ofReal (Real.exp (-(E : ℝ))) := by
  let p' : ℝ≥0∞ := 1 - p
  let half : ℝ≥0∞ := (1 : ℝ≥0∞) / 2
  let x : ℝ≥0∞ := p * half
  let δ : ℝ := p.toReal / 2
  let δe : ℝ≥0∞ := ENNReal.ofReal δ
  have hp0 : 0 ≤ p.toReal := ENNReal.toReal_nonneg
  have hδ0 : 0 ≤ δ := by
    dsimp only [δ]
    positivity
  have hpRealOne : p.toReal ≤ 1 := by
    have := ENNReal.toReal_mono ENNReal.one_ne_top hpOne
    simpa using this
  have hδ1 : δ ≤ 1 := by
    dsimp only [δ]
    linarith
  have hppsum : p + p' = 1 := by
    dsimp only [p']
    rw [add_comm]
    exact tsub_add_cancel_of_le hpOne
  have hhalfCancel : (2 : ℝ≥0∞) * half = 1 := by
    dsimp only [half]
    rw [one_div, ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]
  have hhalfAdd : half + half = 1 := by
    calc
      half + half = 2 * half := by ring
      _ = 1 := hhalfCancel
  have hxx : x + x = p := by
    dsimp only [x]
    calc
      p * half + p * half = p * (half + half) := by ring
      _ = p := by rw [hhalfAdd, mul_one]
  have hxδ : x = δe := by
    apply (ENNReal.toReal_eq_toReal_iff'
      (by dsimp only [x, half]; finiteness)
      ENNReal.ofReal_ne_top).mp
    dsimp only [x, half, δe, δ]
    rw [ENNReal.toReal_mul, ENNReal.toReal_div,
      ENNReal.toReal_ofReal hδ0]
    norm_num
    ring
  have hphiSum : (p' + x) + δe ≤ 1 := by
    rw [← hxδ]
    calc
      (p' + x) + x = p' + (x + x) := by ring
      _ = p' + p := by rw [hxx]
      _ = 1 := by rw [add_comm, hppsum]
      _ ≤ 1 := le_rfl
  have hphiSub : p' + x ≤ 1 - δe :=
    ENNReal.le_sub_of_add_le_right ENNReal.ofReal_ne_top hphiSum
  have hsub : 1 - δe = ENNReal.ofReal (1 - δ) := by
    dsimp only [δe]
    rw [ENNReal.ofReal_sub 1 hδ0, ENNReal.ofReal_one]
  have hphi : p' + x ≤ ENNReal.ofReal (1 - δ) := by
    rwa [← hsub]
  have hnum :
      (p' + x) ^ T ≤
        ENNReal.ofReal (Real.exp (-(δ * (T : ℝ)))) :=
    enn_pow_le_ofReal_exp (p' + x) δ T hδ0 hδ1 hphi
  have hdiv :
      (p' + x) ^ T / half ^ M ≤
        ENNReal.ofReal (Real.exp (-(δ * (T : ℝ)))) /
          half ^ M :=
    ENNReal.div_le_div_right hnum _
  have hhalf :
      half = ENNReal.ofReal (1 / 2 : ℝ) := by
    dsimp only [half]
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have hquot :
      ENNReal.ofReal (Real.exp (-(δ * (T : ℝ)))) /
          half ^ M =
        ENNReal.ofReal
          (Real.exp
            (-(δ * (T : ℝ)) + (M : ℝ) * Real.log 2)) := by
    rw [hhalf, ← ENNReal.ofReal_pow
      (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    rw [← ENNReal.ofReal_div_of_pos
      (by positivity : (0 : ℝ) < (1 / 2 : ℝ) ^ M)]
    congr 2
    have hhalfReal :
        (1 / 2 : ℝ) ^ M =
          Real.exp (-(M : ℝ) * Real.log 2) := by
      rw [← Real.exp_log
        (by positivity : (0 : ℝ) < (1 / 2 : ℝ) ^ M),
        Real.log_pow]
      have hlogHalf : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
        rw [one_div, Real.log_inv]
      rw [hlogHalf]
      congr 1
      ring
    rw [hhalfReal, ← Real.exp_sub]
    congr 1
    ring
  have hlog2 : Real.log 2 ≤ 1 := by
    have h :=
      Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hM0 : (0 : ℝ) ≤ M := by positivity
  have hscaled :
      (M : ℝ) * Real.log 2 ≤ (M : ℝ) :=
    by simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hlog2 hM0
  have hδT : δ * (T : ℝ) = p.toReal * (T : ℝ) / 2 := by
    dsimp only [δ]
    ring
  have hexponent :
      -(δ * (T : ℝ)) + (M : ℝ) * Real.log 2 ≤
        -(E : ℝ) := by
    rw [hδT]
    linarith
  change (p' + x) ^ T / half ^ M ≤ _
  exact hdiv.trans (hquot.le.trans
    (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hexponent)))

/-- Throughout a legal dyadic rung, the exact productive floor is at least
`fire * P/(4n)`.  The constant is deliberately loose. -/
theorem relaxedDyadicProductiveP_ge
    (r : RelaxedRate) (n P L : ℕ)
    (hP : 1 ≤ P) (hL : 1 ≤ L)
    (hroom : 2 * (P + L) ≤ n) :
    (r.fire : ℝ≥0∞) *
        ((P : ℝ≥0∞) / ((4 * n : ℕ) : ℝ≥0∞)) ≤
      relaxedDyadicProductiveP r n P L := by
  let x := relaxedDyadicLower n P L + 1
  let y := relaxedDyadicYLo P
  let A := 3 * (x * y)
  let B := n * (n - 1)
  let D := 4 * n
  have hn : 1 ≤ n := by omega
  have hx : n ≤ 2 * x := by
    dsimp only [x, relaxedDyadicLower]
    omega
  have hy : P ≤ 2 * y := by
    dsimp only [y, relaxedDyadicYLo]
    omega
  have hxy : n * P ≤ 4 * (x * y) := by
    calc
      n * P ≤ (2 * x) * (2 * y) := Nat.mul_le_mul hx hy
      _ = 4 * (x * y) := by ring
  have hB : B ≤ n * n := by
    dsimp only [B]
    exact Nat.mul_le_mul_left n (Nat.sub_le n 1)
  have hcross : B * P ≤ D * A := by
    calc
      B * P ≤ (n * n) * P := Nat.mul_le_mul_right P hB
      _ = n * (n * P) := by ring
      _ ≤ n * (4 * (x * y)) := Nat.mul_le_mul_left n hxy
      _ = (4 * n) * (x * y) := by ring
      _ ≤ (4 * n) * (3 * (x * y)) :=
        Nat.mul_le_mul_left (4 * n) (by omega)
      _ = D * A := by rfl
  have hBpos : 0 < B := by
    dsimp only [B]
    exact Nat.mul_pos (by omega) (by omega)
  have hDpos : 0 < D := by
    dsimp only [D]
    exact Nat.mul_pos (by omega) (by omega)
  have hfrac :
      (P : ℝ≥0∞) / (D : ℝ≥0∞) ≤
        (A : ℝ≥0∞) / (B : ℝ≥0∞) := by
    rw [← ENNReal.toReal_le_toReal
      (ENNReal.div_ne_top (ENNReal.natCast_ne_top _)
        (by exact_mod_cast hDpos.ne'))
      (ENNReal.div_ne_top (ENNReal.natCast_ne_top _)
        (by exact_mod_cast hBpos.ne'))]
    rw [ENNReal.toReal_div, ENNReal.toReal_div]
    norm_num only [ENNReal.toReal_natCast]
    change (P : ℝ) / (D : ℝ) ≤ (A : ℝ) / (B : ℝ)
    rw [div_le_div_iff₀ (by exact_mod_cast hDpos)
      (by exact_mod_cast hBpos)]
    exact_mod_cast (by simpa [mul_comm] using hcross)
  unfold relaxedDyadicProductiveP relaxedBandProductiveFloor
  dsimp only [x, y, A, B, D] at hfrac ⊢
  exact mul_le_mul_left' hfrac (r.fire : ℝ≥0∞)

/-- With `H = C R`, a clock factor satisfying `fire * C ≥ 1` makes the
insufficient-productive-events term exponentially small in `RP`. -/
theorem relaxedDyadic_clock_error_le
    (r : RelaxedRate) (n P L R C : ℕ)
    (hP : 1 ≤ P) (hL : 1 ≤ L)
    (hR : 1 ≤ R) (hC : 1 ≤ C)
    (hroom : 2 * (P + L) ≤ n)
    (hclock : (1 : ℝ) ≤ (r.fire : ℝ) * (C : ℝ)) :
    let p := relaxedDyadicProductiveP r n P L
    ((1 - p) + p * ((1 : ℝ≥0∞) / 2)) ^
          relaxedDyadicHorizon (C * R) n /
        ((1 : ℝ≥0∞) / 2) ^ relaxedDyadicM R P ≤
      ENNReal.ofReal (Real.exp (-((R * P : ℕ) : ℝ))) := by
  let p := relaxedDyadicProductiveP r n P L
  let T := relaxedDyadicHorizon (C * R) n
  let M := relaxedDyadicM R P
  let E := R * P
  have hn : 1 ≤ n := by omega
  have hpOne : p ≤ 1 := by
    dsimp only [p]
    exact relaxedDyadicProductiveP_le_one r n P L hP hL hroom
  have hpTop : p ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top hpOne
  have hfloor :=
    relaxedDyadicProductiveP_ge r n P L hP hL hroom
  have hfloorReal :
      (r.fire : ℝ) * (P : ℝ) / (4 * (n : ℝ)) ≤
        p.toReal := by
    have hreal := ENNReal.toReal_mono hpTop hfloor
    dsimp only [p] at hreal ⊢
    rw [ENNReal.toReal_mul, ENNReal.toReal_div] at hreal
    norm_num only [ENNReal.toReal_natCast, Nat.cast_mul,
      Nat.cast_ofNat] at hreal
    simpa [div_eq_mul_inv, mul_assoc] using hreal
  have hT :
      (T : ℝ) =
        4096 * ((C : ℝ) * (R : ℝ)) * (n : ℝ) := by
    dsimp only [T, relaxedDyadicHorizon]
    push_cast
    ring
  have hM :
      (M : ℝ) = 64 * (R : ℝ) * (P : ℝ) := by
    dsimp only [M, relaxedDyadicM]
    push_cast
    ring
  have hE :
      (E : ℝ) = (R : ℝ) * (P : ℝ) := by
    dsimp only [E]
    push_cast
    ring
  have hRP0 : (0 : ℝ) ≤ (R : ℝ) * (P : ℝ) := by positivity
  have hclockScaled :
      512 * ((R : ℝ) * (P : ℝ)) ≤
        512 * ((r.fire : ℝ) * (C : ℝ)) *
          ((R : ℝ) * (P : ℝ)) := by
    have hc :
        512 * (1 : ℝ) ≤
          512 * ((r.fire : ℝ) * (C : ℝ)) :=
      mul_le_mul_of_nonneg_left hclock (by norm_num)
    nlinarith
  have hlowerT :
      ((r.fire : ℝ) * (P : ℝ) / (4 * (n : ℝ))) *
          (T : ℝ) / 2 =
        512 * ((r.fire : ℝ) * (C : ℝ)) *
          ((R : ℝ) * (P : ℝ)) := by
    rw [hT]
    field_simp
    ring
  have hbudget :
      (E : ℝ) + (M : ℝ) ≤ p.toReal * (T : ℝ) / 2 := by
    calc
      (E : ℝ) + (M : ℝ) =
          65 * ((R : ℝ) * (P : ℝ)) := by
            rw [hE, hM]
            ring
      _ ≤ 512 * ((R : ℝ) * (P : ℝ)) := by
        nlinarith
      _ ≤ 512 * ((r.fire : ℝ) * (C : ℝ)) *
          ((R : ℝ) * (P : ℝ)) := hclockScaled
      _ = ((r.fire : ℝ) * (P : ℝ) / (4 * (n : ℝ))) *
          (T : ℝ) / 2 := hlowerT.symm
      _ ≤ p.toReal * (T : ℝ) / 2 := by
        gcongr
  change
    ((1 - p) + p * ((1 : ℝ≥0∞) / 2)) ^ T /
        ((1 : ℝ≥0∞) / 2) ^ M ≤
      ENNReal.ofReal (Real.exp (-(E : ℝ)))
  exact bernoulliHalf_clock_error_le p T M E hpTop hpOne hbudget

/-- A finite geometric level/reward ratio is bounded by an exponential once
its logarithmic reward budget dominates both level loss and the target
exponent. -/
theorem geometricDirection_error_le
    (w eta : NNReal) (s u M : ℕ) (E : ℝ)
    (hw : 0 < w) (heta : 0 < eta) (hsu : s ≤ u)
    (hbudget :
      ((u : ℝ) - (s : ℝ)) * (-Real.log (w : ℝ)) + E ≤
        (M : ℝ) * Real.log (eta : ℝ)) :
    (w : ℝ≥0∞) ^ s /
        ((w : ℝ≥0∞) ^ u * (eta : ℝ≥0∞) ^ M) ≤
      ENNReal.ofReal (Real.exp (-E)) := by
  have hwR : (0 : ℝ) < (w : ℝ) := by exact_mod_cast hw
  have hetaR : (0 : ℝ) < (eta : ℝ) := by exact_mod_cast heta
  have hleftTop :
      (w : ℝ≥0∞) ^ s /
          ((w : ℝ≥0∞) ^ u * (eta : ℝ≥0∞) ^ M) ≠ ⊤ := by
    finiteness
  rw [← ENNReal.toReal_le_toReal hleftTop ENNReal.ofReal_ne_top]
  rw [ENNReal.toReal_div, ENNReal.toReal_mul,
    ENNReal.toReal_pow, ENNReal.toReal_pow, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal (Real.exp_pos (-E)).le]
  change
    (w : ℝ) ^ s / ((w : ℝ) ^ u * (eta : ℝ) ^ M) ≤
      Real.exp (-E)
  rw [← Real.exp_log
    (div_pos (pow_pos hwR s)
      (mul_pos (pow_pos hwR u) (pow_pos hetaR M)))]
  apply Real.exp_le_exp.mpr
  rw [Real.log_div (pow_ne_zero s hwR.ne')
      (mul_ne_zero (pow_ne_zero u hwR.ne')
        (pow_ne_zero M hetaR.ne')),
    Real.log_mul (pow_ne_zero u hwR.ne')
      (pow_ne_zero M hetaR.ne'),
    Real.log_pow, Real.log_pow, Real.log_pow]
  have hcast : (u - s : ℕ) = u - s := rfl
  have hus : ((u - s : ℕ) : ℝ) = (u : ℝ) - (s : ℝ) := by
    rw [Nat.cast_sub hsu]
  linarith

/-- The exact dyadic direction term is exponentially small after half of the
productive reward pays for the possible geometric level blow-up. -/
theorem relaxedDyadic_direction_error_le
    (n P R : ℕ) (B : NNReal)
    (hP : 1 ≤ P) (hroom : 2 * P ≤ n)
    (hB : 1 < B)
    (habsorb :
      -Real.log (relaxedDirW B : ℝ) ≤
        32 * (R : ℝ) * Real.log (relaxedDirEta B : ℝ)) :
    (relaxedDirW B : ℝ≥0∞) ^ relaxedDyadicStart n P /
        ((relaxedDirW B : ℝ≥0∞) ^
            (relaxedDyadicTarget n P - 1) *
          (relaxedDirEta B : ℝ≥0∞) ^ relaxedDyadicM R P) ≤
      ENNReal.ofReal
        (Real.exp
          (-(32 * (R : ℝ) * (P : ℝ) *
            Real.log (relaxedDirEta B : ℝ)))) := by
  let w := relaxedDirW B
  let eta := relaxedDirEta B
  let s := relaxedDyadicStart n P
  let u := relaxedDyadicTarget n P - 1
  let M := relaxedDyadicM R P
  let E : ℝ :=
    32 * (R : ℝ) * (P : ℝ) * Real.log (eta : ℝ)
  have hw : 0 < w := by
    dsimp only [w, relaxedDirW]
    positivity
  have heta : 0 < eta := by
    exact zero_lt_one.trans (relaxedDir_eta_gt_one hB)
  have hsu : s ≤ u := by
    dsimp only [s, u, relaxedDyadicStart, relaxedDyadicTarget]
    omega
  have hgap : u - s ≤ P := by
    dsimp only [s, u, relaxedDyadicStart, relaxedDyadicTarget]
    omega
  have hneglog : 0 ≤ -Real.log (w : ℝ) := by
    have hwR : (0 : ℝ) < (w : ℝ) := by exact_mod_cast hw
    have hwOne : (w : ℝ) ≤ 1 := by
      exact_mod_cast le_of_lt (relaxedDir_w_lt_one hB)
    exact neg_nonneg.mpr (Real.log_nonpos hwR.le hwOne)
  have hgapReal :
      ((u : ℝ) - (s : ℝ)) * (-Real.log (w : ℝ)) ≤
        (P : ℝ) * (-Real.log (w : ℝ)) := by
    have hcast : ((u - s : ℕ) : ℝ) ≤ (P : ℝ) := by
      exact_mod_cast hgap
    rw [Nat.cast_sub hsu] at hcast
    exact mul_le_mul_of_nonneg_right hcast hneglog
  have habsorb' :
      -Real.log (w : ℝ) ≤
        32 * (R : ℝ) * Real.log (eta : ℝ) := by
    simpa only [w, eta] using habsorb
  have hlevel :
      ((u : ℝ) - (s : ℝ)) * (-Real.log (w : ℝ)) ≤ E := by
    calc
      ((u : ℝ) - (s : ℝ)) * (-Real.log (w : ℝ)) ≤
          (P : ℝ) * (-Real.log (w : ℝ)) := hgapReal
      _ ≤ (P : ℝ) *
          (32 * (R : ℝ) * Real.log (eta : ℝ)) :=
        mul_le_mul_of_nonneg_left habsorb' (by positivity)
      _ = E := by
        dsimp only [E]
        ring
  have hM :
      (M : ℝ) = 64 * (R : ℝ) * (P : ℝ) := by
    dsimp only [M, relaxedDyadicM]
    push_cast
    ring
  have hbudget :
      ((u : ℝ) - (s : ℝ)) * (-Real.log (w : ℝ)) + E ≤
        (M : ℝ) * Real.log (eta : ℝ) := by
    rw [hM]
    dsimp only [E]
    nlinarith
  simpa only [w, eta, s, u, M, E] using
    geometricDirection_error_le w eta s u M E
      hw heta hsu hbudget

/-- The Feller ruin term is exactly an exponential in the buffer length. -/
theorem relaxedRuin_error_eq_exp
    (beta : NNReal) (L : ℕ) (hbeta : 0 < beta) :
    (beta : ℝ≥0∞)⁻¹ ^ L =
      ENNReal.ofReal
        (Real.exp (-((L : ℝ) * Real.log (beta : ℝ)))) := by
  rw [← ENNReal.toReal_eq_toReal_iff'
    (by finiteness : (beta : ℝ≥0∞)⁻¹ ^ L ≠ ⊤)
    ENNReal.ofReal_ne_top]
  rw [ENNReal.toReal_pow, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (Real.exp_pos _).le]
  change ((beta : ℝ)⁻¹) ^ L =
    Real.exp (-((L : ℝ) * Real.log (beta : ℝ)))
  have hbetaR : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbeta
  rw [← Real.exp_log (pow_pos (inv_pos.mpr hbetaR) L),
    Real.log_pow, Real.log_inv]
  congr 1
  ring

/-- All three exact error terms of a dyadic rung have explicit exponential
envelopes.  The direction and clock scales are independent. -/
theorem relaxedDyadicBandError_le_exp
    (r : RelaxedRate) (n P L R C : ℕ) (beta : NNReal)
    (hP : 1 ≤ P) (hL : 1 ≤ L)
    (hR : 1 ≤ R) (hC : 1 ≤ C)
    (hroom : 2 * (P + L) ≤ n)
    (hbeta : 1 < beta)
    (hclock : (1 : ℝ) ≤ (r.fire : ℝ) * (C : ℝ))
    (habsorb :
      -Real.log (relaxedDirW beta : ℝ) ≤
        32 * (R : ℝ) *
          Real.log (relaxedDirEta beta : ℝ)) :
    relaxedDyadicBandError r n P L R (C * R) beta 0 ≤
      ENNReal.ofReal
          (Real.exp (-((L : ℝ) * Real.log (beta : ℝ)))) +
        ENNReal.ofReal
          (Real.exp
            (-(32 * (R : ℝ) * (P : ℝ) *
              Real.log (relaxedDirEta beta : ℝ)))) +
        ENNReal.ofReal
          (Real.exp (-((R * P : ℕ) : ℝ))) := by
  unfold relaxedDyadicBandError
  simp only [add_zero]
  exact add_le_add
    (add_le_add
      (le_of_eq
        (relaxedRuin_error_eq_exp beta L
          (zero_lt_one.trans hbeta)))
      (relaxedDyadic_direction_error_le
        n P R beta hP (by omega) hbeta habsorb))
    (relaxedDyadic_clock_error_le
      r n P L R C hP hL hR hC hroom hclock)

end Tri

#print axioms Tri.bernoulliHalf_clock_error_le
#print axioms Tri.relaxedDyadicProductiveP_ge
#print axioms Tri.relaxedDyadic_clock_error_le
#print axioms Tri.geometricDirection_error_le
#print axioms Tri.relaxedDyadic_direction_error_le
#print axioms Tri.relaxedRuin_error_eq_exp
#print axioms Tri.relaxedDyadicBandError_le_exp
