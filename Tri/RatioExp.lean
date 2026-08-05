/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Harmonic ratio powers are Gaussian

The single analytic tool the phase-1 (and phase-2) Feller / return envelopes
need: a minority/majority ratio raised to a power is bounded by an exponential
of the drift.  Concretely, for `0 < b ≤ a`,

```
(b / a) ^ k ≤ exp (-k · (a - b) / a).
```

This is `Real.log_le_sub_one_of_pos` (`log x ≤ x - 1`) applied to `x = b/a`,
lifted through `Real.exp_log` and monotonicity, then transported to `ℝ≥0∞`.
-/

namespace Tri

open scoped ENNReal

/-- **Real harmonic-ratio bound.**  For `0 < b ≤ a`, the `k`-th power of the
ratio `b/a` is dominated by `exp(-k (a-b)/a)`. -/
theorem ratio_pow_le_exp_real (a b : ℝ) (k : ℕ) (hb : 0 < b) (hba : b ≤ a) :
    (b / a) ^ k ≤ Real.exp (-(k : ℝ) * (a - b) / a) := by
  have ha : 0 < a := lt_of_lt_of_le hb hba
  have hratio : 0 < b / a := div_pos hb ha
  -- `(b/a)^k = exp (k · log (b/a))`.
  have hpow : (b / a) ^ k = Real.exp ((k : ℝ) * Real.log (b / a)) := by
    rw [← Real.exp_log (show (0:ℝ) < (b / a) ^ k from pow_pos hratio k), Real.log_pow]
  rw [hpow]
  apply Real.exp_le_exp.mpr
  -- `log (b/a) ≤ b/a - 1 = -(a-b)/a`.
  have hlog : Real.log (b / a) ≤ b / a - 1 := Real.log_le_sub_one_of_pos hratio
  have hkey : b / a - 1 = -(a - b) / a := by field_simp; ring
  rw [hkey] at hlog
  have hkpos : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  calc (k : ℝ) * Real.log (b / a) ≤ (k : ℝ) * (-(a - b) / a) :=
        mul_le_mul_of_nonneg_left hlog hkpos
    _ = -(k : ℝ) * (a - b) / a := by ring

/-- **`ℝ≥0∞` harmonic-ratio bound.**  The natural-number ratio `b/a` in `ℝ≥0∞`,
raised to `k`, is bounded by the `ofReal` exponential of the drift. -/
theorem ratio_pow_le_exp (a b k : ℕ) (hb : 0 < b) (hba : b ≤ a) :
    ((b : ℝ≥0∞) / (a : ℝ≥0∞)) ^ k ≤
      ENNReal.ofReal (Real.exp (-(k : ℝ) * ((a : ℝ) - (b : ℝ)) / (a : ℝ))) := by
  have ha : 0 < a := lt_of_lt_of_le hb hba
  have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hbaR : (b : ℝ) ≤ (a : ℝ) := by exact_mod_cast hba
  -- Rewrite the `ℝ≥0∞` ratio as `ofReal (b/a)`.
  have hdiv : ((b : ℝ≥0∞) / (a : ℝ≥0∞)) = ENNReal.ofReal ((b : ℝ) / (a : ℝ)) := by
    rw [ENNReal.ofReal_div_of_pos haR, ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
  rw [hdiv, ← ENNReal.ofReal_pow (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  exact ratio_pow_le_exp_real (a : ℝ) (b : ℝ) k hbR hbaR

/-- **Envelope interface.**  Given any drift budget `E` dominated by the log-ratio
`k·(a-b)/a`, the ratio power fits `ofReal (exp (-E))`.  The caller supplies `hE`
(the boundary arithmetic `E ≤ k(a-b)/a`); this delivers the Gaussian shape the
phase-1 rung envelope `phase1RungEnvelopeR_eq_gap` demands (with `E = Δ²/48n`). -/
theorem ratio_pow_le_ofReal_exp (a b k : ℕ) (E : ℝ) (hb : 0 < b) (hba : b ≤ a)
    (hE : E ≤ (k : ℝ) * ((a : ℝ) - (b : ℝ)) / (a : ℝ)) :
    ((b : ℝ≥0∞) / (a : ℝ≥0∞)) ^ k ≤ ENNReal.ofReal (Real.exp (-E)) := by
  refine le_trans (ratio_pow_le_exp a b k hb hba) (ENNReal.ofReal_le_ofReal ?_)
  apply Real.exp_le_exp.mpr
  have : -(k : ℝ) * ((a : ℝ) - (b : ℝ)) / (a : ℝ) = -((k : ℝ) * ((a : ℝ) - (b : ℝ)) / (a : ℝ)) := by
    ring
  rw [this]
  linarith

/-- **Geometric decay is exponential.**  For a contraction gap `δ ∈ [0,1]`, the
`T`-th power of `1 - δ` is bounded by `exp(-δ T)`.  This is the deadline half of
the phase-1 progress estimate: `φ^T ≤ (1-δ)^T ≤ exp(-δT)`. -/
theorem one_sub_pow_le_exp (δ : ℝ) (T : ℕ) (h0 : 0 ≤ δ) (h1 : δ ≤ 1) :
    (1 - δ) ^ T ≤ Real.exp (-(δ * (T : ℝ))) := by
  have hbase : (1 : ℝ) - δ ≤ Real.exp (-δ) := by
    have := Real.add_one_le_exp (-δ)
    linarith
  calc (1 - δ) ^ T ≤ (Real.exp (-δ)) ^ T :=
        pow_le_pow_left₀ (by linarith) hbase T
    _ = Real.exp (-(δ * (T : ℝ))) := by
        rw [← Real.exp_nat_mul]; ring_nf

/-- **`ℝ≥0∞` geometric-decay bound.**  A `ℝ≥0∞` contraction factor `φ ≤ 1 - δ`
(with `δ ∈ [0,1]` real) has `φ ^ T ≤ ofReal (exp (-δ T))`. -/
theorem enn_pow_le_ofReal_exp (φ : ℝ≥0∞) (δ : ℝ) (T : ℕ)
    (h0 : 0 ≤ δ) (h1 : δ ≤ 1) (hφ : φ ≤ ENNReal.ofReal (1 - δ)) :
    φ ^ T ≤ ENNReal.ofReal (Real.exp (-(δ * (T : ℝ)))) := by
  calc φ ^ T ≤ (ENNReal.ofReal (1 - δ)) ^ T := pow_le_pow_left' hφ T
    _ = ENNReal.ofReal ((1 - δ) ^ T) := (ENNReal.ofReal_pow (by linarith) T).symm
    _ ≤ ENNReal.ofReal (Real.exp (-(δ * (T : ℝ)))) :=
        ENNReal.ofReal_le_ofReal (one_sub_pow_le_exp δ T h0 h1)

/-- **The three-mass contraction-gap identity.**  For any down/stay/up masses
summing to one and any potential `w`, the deficit of the weighted three-mass
expression below `w` factors as `(1-w)·(pUp·w - pDown)`.  This is the exact
algebraic core of the quantitative phase-1 contraction rate: the gap is the
product of the potential slack `1-w` and the directional drift `pUp·w - pDown`. -/
theorem three_mass_gap_identity (pDown pStay pUp w : ℝ)
    (hsum : pDown + pStay + pUp = 1) :
    w - (pDown + pStay * w + pUp * w ^ 2) = (1 - w) * (pUp * w - pDown) := by
  have hstay : pStay = 1 - pDown - pUp := by linarith
  rw [hstay]; ring

/-- **Potential blow-up as an exponential.**  For a base `p/q ∈ (0,1]` and
`s ≤ u`, the ratio `base^s / base^u` (which is `≥ 1`) equals `(q/p)^(u-s)` and is
bounded by `ofReal (exp ((u-s)·log (q/p)))`.  This is the potential-gain factor
`base^start / base^upper` in the phase-1 deadline (`phase1RungBase = (lower+bLo)/(2·lower)`). -/
theorem base_pow_ratio_le_ofReal_exp (p q s u : ℕ) (hp : 0 < p) (hpq : p ≤ q)
    (hsu : s ≤ u) :
    ((p : ℝ≥0∞) / (q : ℝ≥0∞)) ^ s / ((p : ℝ≥0∞) / (q : ℝ≥0∞)) ^ u
      ≤ ENNReal.ofReal (Real.exp (((u : ℝ) - (s : ℝ)) * Real.log ((q : ℝ) / (p : ℝ)))) := by
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hqR : (0 : ℝ) < (q : ℝ) := lt_of_lt_of_le hpR (by exact_mod_cast hpq)
  set r : ℝ := (p : ℝ) / (q : ℝ) with hr
  have hr0 : 0 < r := div_pos hpR hqR
  -- Move the whole ratio into `ofReal`.
  have hbase : ((p : ℝ≥0∞) / (q : ℝ≥0∞)) = ENNReal.ofReal r := by
    rw [hr, ENNReal.ofReal_div_of_pos hqR, ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
  rw [hbase, ← ENNReal.ofReal_pow hr0.le, ← ENNReal.ofReal_pow hr0.le,
    ← ENNReal.ofReal_div_of_pos (pow_pos hr0 u)]
  apply ENNReal.ofReal_le_ofReal
  -- In `ℝ`: `r^s / r^u = (q/p)^(u-s) = exp((u-s)·log(q/p))`.
  have hsplit : r ^ u = r ^ s * r ^ (u - s) := by rw [← pow_add]; congr 1; omega
  have hrs : (0 : ℝ) < r ^ s := pow_pos hr0 s
  have hru : (0 : ℝ) < r ^ (u - s) := pow_pos hr0 _
  have hrec : r ^ s / r ^ u = (r ^ (u - s))⁻¹ := by
    rw [hsplit]; field_simp
  rw [hrec]
  have hinvr : r⁻¹ = (q : ℝ) / (p : ℝ) := by rw [hr, inv_div]
  have hpow : (r ^ (u - s))⁻¹ = ((q : ℝ) / (p : ℝ)) ^ (u - s) := by
    rw [← inv_pow, hinvr]
  rw [hpow, ← Real.exp_log (show (0:ℝ) < ((q:ℝ)/(p:ℝ)) ^ (u - s) from
    pow_pos (div_pos hqR hpR) _), Real.log_pow]
  apply Real.exp_le_exp.mpr
  rw [Nat.cast_sub hsu]

end Tri

#print axioms Tri.ratio_pow_le_exp_real
#print axioms Tri.ratio_pow_le_exp
#print axioms Tri.ratio_pow_le_ofReal_exp
#print axioms Tri.one_sub_pow_le_exp
#print axioms Tri.enn_pow_le_ofReal_exp
#print axioms Tri.base_pow_ratio_le_ofReal_exp
