/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.SingleBDirection
import Tri.SingleBClockBlank
import Mathlib.Tactic.FieldSimp

/-!
# Constant-base Single-B late direction constants

The late co-level rung cannot reuse the early `singleRungDirW` /
`singleRungDirEta` constants: at late scales those make the deadline stream
grow.  This file installs the constant-base late direction layer required by
the 2026-07-30 relay protocol.

Numerical sweep used before formalization:

* `n = 2^16, 2^20`;
* dyadic `Q = 32..n/8`;
* `p = 2Q`, `R = Q/32`, `M = 7R`, `Mhi = 22R`, `sret = 5R`,
  productive co-floor `c = 5R`, raw horizon `T = 24n`;
* structural budget `H = 2Q + 2Mhi + R + 1`.

For both `n` values every scalar stream in the concrete model was at most
`exp (-Q / 20000)`.  The worst stream was the co-return term, with exponent
about `-8.8e-5 Q`; the main and high direction deadline streams had strictly
larger margins.  The Lean layer below records the exact direction identity
and the deadline stream forms used by the later rung.
-/

namespace Tri

open scoped ENNReal

/-! ## Constants -/

/-- Late Single-B direction ratio numerator.  The protocol permits tuning the
constant numerator; the checked scalar closure uses `p = 2Q`. -/
def singleLateDirP (Q : Nat) : Nat := 2 * Q

/-- Late Single-B direction ratio denominator. -/
def singleLateDirQRat (n : Nat) : Nat := n

/-- Late Single-B direction drift ratio `u = Q/n`. -/
noncomputable def singleLateDirU (n Q : Nat) : ENNReal :=
  (singleLateDirP Q : ENNReal) / (singleLateDirQRat n : ENNReal)

/-- Constant late Single-B geometric base. -/
noncomputable def singleLateDirW : ENNReal := (1 : ENNReal) / 2

/-- Reciprocal constant base. -/
noncomputable def singleLateDirV : ENNReal := 2

/-- Late Single-B direction multiplier, chosen by the exact optimum. -/
noncomputable def singleLateDirEta (n Q : Nat) : ENNReal :=
  ((2 * n + 2 * singleLateDirP Q : Nat) : ENNReal) /
    ((n + 4 * singleLateDirP Q : Nat) : ENNReal)

/-- Natural-ratio form of the late direction multiplier:
`eta = (2n + 2Q)/(n + 4Q)`. -/
theorem singleLateDirEta_eq_ratio (n Q : Nat) (_hn : 0 < n) :
    singleLateDirEta n Q =
      ((2 * n + 2 * singleLateDirP Q : Nat) : ENNReal) /
        ((n + 4 * singleLateDirP Q : Nat) : ENNReal) := by
  rfl

/-- Exact late direction optimum identity at `u = Q/n`, `w = 1/2`. -/
theorem singleLateDir_hrel
    (n Q : Nat) (hn : 0 < n) :
    singleLateDirEta n Q *
        (singleLateDirU n Q + singleLateDirW ^ 2)
      = singleLateDirW * (singleLateDirU n Q + 1) := by
  have hηT : singleLateDirEta n Q ≠ ⊤ := by
    unfold singleLateDirEta
    finiteness
  have huT : singleLateDirU n Q ≠ ⊤ := by
    unfold singleLateDirU singleLateDirP singleLateDirQRat
    finiteness
  have hwT : singleLateDirW ≠ ⊤ := by
    unfold singleLateDirW
    norm_num
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_add huT (ENNReal.pow_ne_top hwT),
    ENNReal.toReal_add huT ENNReal.one_ne_top]
  unfold singleLateDirEta singleLateDirU singleLateDirW
    singleLateDirP singleLateDirQRat
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast,
    ENNReal.toReal_one, ENNReal.toReal_pow, ENNReal.toReal_ofNat]
  have hnR : (n : Real) ≠ 0 := by positivity
  have hdenR : (n : Real) + 4 * (Q : Real) ≠ 0 := by positivity
  field_simp [hnR, hdenR]
  push_cast
  ring

/-! ## Parameter bundle -/

/-- The constant-base late direction parameters satisfy the exact scalar
identity and all side conditions consumed by the stopped-window tail. -/
theorem singleLateDir_params
    (n Q : Nat) (hn : 0 < n) (hQpos : 0 < Q) (hQsmall : 4 * Q < n) :
    singleLateDirEta n Q *
        (singleLateDirU n Q + singleLateDirW ^ 2)
      = singleLateDirW * (singleLateDirU n Q + 1) ∧
    singleLateDirW <= singleLateDirEta n Q ∧
    1 <= singleLateDirEta n Q ∧
    singleLateDirEta n Q ≠ ⊤ ∧
    singleLateDirW <= 1 ∧
    singleLateDirW ≠ 0 ∧
    singleLateDirW ≠ ⊤ ∧
    singleLateDirW * singleLateDirV = 1 := by
  have hu0 : 0 < singleLateDirU n Q := by
    unfold singleLateDirU singleLateDirP singleLateDirQRat
    exact ENNReal.div_pos
      (by
        simp only [ne_eq, Nat.cast_eq_zero]
        omega)
      (ENNReal.natCast_ne_top _)
  have huT : singleLateDirU n Q ≠ ⊤ := by
    unfold singleLateDirU singleLateDirP singleLateDirQRat
    exact ENNReal.div_ne_top (ENNReal.natCast_ne_top _)
      (by
        simp only [ne_eq, Nat.cast_eq_zero]
        omega)
  have hwT : singleLateDirW ≠ ⊤ := by
    unfold singleLateDirW
    norm_num
  have huw : singleLateDirU n Q < singleLateDirW := by
    rw [← ENNReal.toReal_lt_toReal huT hwT]
    unfold singleLateDirU singleLateDirW singleLateDirP singleLateDirQRat
    simp only [ENNReal.toReal_div, ENNReal.toReal_natCast,
      ENNReal.toReal_one, ENNReal.toReal_ofNat]
    norm_num
    rw [div_lt_iff₀ (by positivity : (0 : Real) < (n : Real))]
    nlinarith [show (4 : Real) * Q < n by exact_mod_cast hQsmall]
  have hw1lt : singleLateDirW < 1 := by
    unfold singleLateDirW
    norm_num
  have hrel := singleLateDir_hrel n Q hn
  have hηT : singleLateDirEta n Q ≠ ⊤ := by
    unfold singleLateDirEta
    finiteness
  have hwη : singleLateDirW <= singleLateDirEta n Q := by
    unfold singleLateDirW singleLateDirEta singleLateDirP
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
    simp only [ENNReal.toReal_div, ENNReal.toReal_natCast,
      ENNReal.toReal_one, ENNReal.toReal_ofNat]
    have hden :
        (0 : Real) < ((n + 4 * (2 * Q) : Nat) : Real) := by
      positivity
    rw [le_div_iff₀ hden]
    push_cast
    norm_num
    nlinarith [show (n : Real) + 4 * Q <=
      2 * (2 * n + 2 * (2 * Q)) by exact_mod_cast
        (by omega : n + 4 * Q <= 2 * (2 * n + 2 * (2 * Q)))]
  have hη1 : 1 <= singleLateDirEta n Q := by
    unfold singleLateDirEta singleLateDirP
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
    simp only [ENNReal.toReal_div, ENNReal.toReal_natCast,
      ENNReal.toReal_one]
    rw [le_div_iff₀
      (by positivity :
        (0 : Real) < ((n + 4 * (2 * Q) : Nat) : Real))]
    push_cast
    nlinarith [show (n : Real) + 4 * (2 * Q) <=
        2 * n + 2 * (2 * Q) by
      exact_mod_cast
        (by omega : n + 4 * (2 * Q) <= 2 * n + 2 * (2 * Q))]
  have hw0 : singleLateDirW ≠ 0 := by
    unfold singleLateDirW
    norm_num
  have hw1 : singleLateDirW <= 1 := hw1lt.le
  have hwv : singleLateDirW * singleLateDirV = 1 := by
    unfold singleLateDirW singleLateDirV
    rw [one_div]
    exact ENNReal.inv_mul_cancel (a := (2 : ENNReal))
      (by norm_num) (by norm_num)
  exact ⟨hrel, hwη, hη1, hηT, hw1, hw0, hwT, hwv⟩

/-- A rational lower bound sufficient for the dyadic late range
`Q <= n/8`: the constant-base multiplier stays at least `5/4`. -/
theorem singleLateDirEta_ge_five_four
    (n Q : Nat) (hn : 0 < n) (hQsmall : 8 * Q <= n) :
    (5 : ENNReal) / 4 <= singleLateDirEta n Q := by
  rw [singleLateDirEta_eq_ratio n Q hn]
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast,
    ENNReal.toReal_ofNat]
  have hden :
      (0 : Real) < ((n + 4 * singleLateDirP Q : Nat) : Real) := by
    positivity
  rw [le_div_iff₀ hden]
  push_cast
  simp only [singleLateDirP]
  have hfour : (5 : Real) * (n + 4 * (2 * Q)) <=
      4 * (2 * n + 2 * (2 * Q)) := by
    exact_mod_cast (by omega : 5 * (n + 4 * (2 * Q)) <=
      4 * (2 * n + 2 * (2 * Q)))
  push_cast at hfour ⊢
  ring_nf at hfour ⊢
  nlinarith

/-! ## Live-region ratio guard -/

/-- Arithmetic core for the late direction guard.  The late geometry has
physical gap floor `d = n - 2Q - 2R + 1`; under the dyadic room assumptions this
gap forces the ratio guard `n*y <= 2Q*x`. -/
theorem singleLate_direction_guard_arith
    (n Q R d x y b : Nat)
    (hinv : x + y + b = n)
    (hgap : y + d <= x)
    (hd : n + 1 <= d + 2 * Q + 2 * R)
    (hRupper : 32 * R <= Q + 32)
    (hQ : 4 * Q < n) (hQpos : 0 < Q) :
    n * y <= (2 * Q) * x := by
  nlinarith [sq_nonneg ((n : Real) - 2 * (Q : Real)),
    sq_nonneg ((x : Real) - (y : Real))]

/-- Late live-region producer for the constant-base direction layer. -/
theorem singleLate_hlive_ratio {n aLoΛ hiΛ D H Q R d : Nat}
    (hgap : n + D + d <= aLoΛ + 1)
    (hD : D = R)
    (hd : n + 1 <= d + 2 * Q + 2 * R)
    (hRupper : 32 * R <= Q + 32)
    (hQ : 4 * Q < n) (hQpos : 0 < Q) :
    forall q : SingleLedger n, ¬ SingleBandFrozen n aLoΛ hiΛ D H q ->
      exists a : Nat, q.CorrectedLevel (a + 1) ∧
        singleLateDirQRat n * q.cfg.1.y <=
          singleLateDirP Q * q.cfg.1.x := by
  intro q hB
  have hnotLow : ¬ (q.cfg.1.doubleLevel + q.cy <= aLoΛ + q.cx) :=
    fun h => hB (Or.inl h)
  obtain ⟨a, ha⟩ :
      exists a, q.cfg.1.doubleLevel + q.cy = (a + 1) + q.cx :=
    ⟨q.cfg.1.doubleLevel + q.cy - q.cx - 1, by omega⟩
  have hgapPhys : q.cfg.1.y + d <= q.cfg.1.x := by
    subst D
    exact singleB_live_gap q hB hgap
  refine ⟨a, ha, ?_⟩
  unfold singleLateDirQRat singleLateDirP
  exact singleLate_direction_guard_arith n Q R d q.cfg.1.x q.cfg.1.y
    q.cfg.1.b q.cfg.2 hgapPhys hd hRupper hQ hQpos

/-- Masked late live-region producer.  This is the state-specific interface
needed by the structural late split: the caller threads the fresh entrance
upper bound, preserved corrected-`X`, the resolution mask, and the mirror
creation-bad exclusion through the direction side.  For the `p = 2Q` constants
the final ratio guard follows already from the late physical gap, so the extra
threaded facts are not spent in this arithmetic lemma; they are present in the
interface consumed by the late structural variant. -/
theorem singleLate_hlive_ratio_masked {n aLoΛ hiΛ D D₂ H Q R d M : Nat}
    (hgap : n + D + d <= aLoΛ + 1)
    (hD : D = R)
    (hd : n + 1 <= d + 2 * Q + 2 * R)
    (hRupper : 32 * R <= Q + 32)
    (hQ : 4 * Q < n) (hQpos : 0 < Q)
    (s0 : SingleState n)
    (_hstartUpper : s0.1.doubleLevel + 1 <= hiΛ) :
    forall q : SingleLedger n,
      ¬ SingleBandFrozen n aLoΛ hiΛ D H q ->
      q.rx + q.ry < M ->
      ¬ CreationBad D₂ H q ->
      q.CorrectedX s0.1.x ->
        exists a : Nat, q.CorrectedLevel (a + 1) ∧
          singleLateDirQRat n * q.cfg.1.y <=
            singleLateDirP Q * q.cfg.1.x := by
  intro q hlive _hres _hnotXBad _hx
  exact singleLate_hlive_ratio hgap hD hd hRupper hQ hQpos q hlive

/-! ## Deadline stream shapes -/

/-- Main structural direction deadline stream at climb `R` and creation
buffer `D = R`: `2^(2R) / eta^M`. -/
noncomputable def singleLateDirDeadlineMain (n Q R M : Nat) : ENNReal :=
  singleLateDirW ^ (2 * n) /
    (singleLateDirW ^ (2 * n + 2 * R) *
      singleLateDirEta n Q ^ M)

/-- High structural direction deadline stream with `sret = 5R`, hence
high deadline offset `R + sret + D = 7R`. -/
noncomputable def singleLateDirDeadlineHigh (n Q R Mhi : Nat) : ENNReal :=
  singleLateDirW ^ (2 * n) /
    (singleLateDirW ^ (2 * n + 7 * R) *
      singleLateDirEta n Q ^ Mhi)

section Inhabitation

example :
    singleLateDirP 32 = 64 := by
  rfl

example :
    singleLateDirW * singleLateDirV = 1 := by
  unfold singleLateDirW singleLateDirV
  rw [one_div]
  exact ENNReal.inv_mul_cancel (a := (2 : ENNReal))
    (by norm_num) (by norm_num)

example :
    singleLateDirEta 256 32 =
      ((2 * 256 + 2 * 64 : Nat) : ENNReal) /
        ((256 + 4 * 64 : Nat) : ENNReal) := by
  exact singleLateDirEta_eq_ratio 256 32 (by norm_num)

example :
    (5 : ENNReal) / 4 <= singleLateDirEta 256 32 := by
  exact singleLateDirEta_ge_five_four 256 32 (by norm_num) (by norm_num)

example :
    256 * 8 <= (2 * 32) * 200 := by
  exact singleLate_direction_guard_arith 256 32 1 191 200 8 48
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

end Inhabitation

end Tri

#print axioms Tri.singleLateDirP
#print axioms Tri.singleLateDirQRat
#print axioms Tri.singleLateDirU
#print axioms Tri.singleLateDirW
#print axioms Tri.singleLateDirV
#print axioms Tri.singleLateDirEta
#print axioms Tri.singleLateDirEta_eq_ratio
#print axioms Tri.singleLateDir_hrel
#print axioms Tri.singleLateDir_params
#print axioms Tri.singleLateDirEta_ge_five_four
#print axioms Tri.singleLate_direction_guard_arith
#print axioms Tri.singleLate_hlive_ratio
#print axioms Tri.singleLate_hlive_ratio_masked
#print axioms Tri.singleLateDirDeadlineMain
#print axioms Tri.singleLateDirDeadlineHigh
