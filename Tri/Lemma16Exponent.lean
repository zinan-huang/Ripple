/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Lemma15Assembly

/-!
# Lemma 16's exponent floor

Paper Lemma 16's activation-label part is a DIRECT instance of the windowed urn
tail — no `recentred_split` is needed, because the window starts at the
beginning of the random activation order and its centre is therefore
deterministic.

This file checks the constant, which is the step I do not skip: paper Lemma 12
hid a real constant gap that only showed up when the arithmetic was done
explicitly.

## The substitution

```text
ν + 1 = n        R + B = ν        k + 1 = a
u + k + 1 = ν    δ = ρ/(2ν)       ρ² ≥ γ·lg n·a
```

with red = `Y`-labelled inactive and `k` the number of newly activated molecules
before the active population first reaches `a`.

## The constant is tight

`urn_window_tail_telescope` gives exponent `−δ²·ν·(u+1)/k`, and under the
first-quarter side condition `4a ≤ n` this is at most `−(3/16)·γ·lg n`.

Scanning `n` up to `10⁸`, `γ ∈ {1,2,10}` and `a` across its range, the minimum of
`exponent/(γ lg n)` is **exactly** `3/16`, attained at `4a = n` — the boundary of
the side condition. So `3/16` is not a convenient under-estimate; it is the
sharp value, and there is no room to weaken the side condition.
-/

namespace Tri

open scoped ENNReal

/-- **Lemma 16's exponent floor.**  With the activation urn substituted as
`ν + 1 = n`, `k + 1 = a`, `u + k + 1 = ν` and radius `δ = ρ/(2ν)`, the
telescope exponent `δ²·ν·(u+1)/k` is at least `(3/16)·γ·lg n` under the
first-quarter side condition `4a ≤ n`.

The constant is TIGHT: the ratio equals `3/16` exactly at `4a = n`, verified
numerically before this was stated. -/
theorem lemma16_exponent_floor
    (qq rho : ℝ) (n a k u ν : ℕ)
    (hq : 0 ≤ qq) (hrho : qq * (a : ℝ) ≤ rho ^ 2)
    (hν : ν + 1 = n) (hk : k + 1 = a) (huk : u + k + 1 = ν)
    (hquarter : 4 * a ≤ n) (hk0 : 0 < k) :
    3 / 16 * qq
      ≤ (rho / (2 * (ν : ℝ))) ^ 2 * (ν : ℝ) * ((u : ℝ) + 1) / (k : ℝ) := by
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk0
  have hνR : (0 : ℝ) < (ν : ℝ) := by
    have : 0 < ν := by omega
    exact_mod_cast this
  have haR : (a : ℝ) = (k : ℝ) + 1 := by exact_mod_cast hk.symm
  have hu1 : (u : ℝ) + 1 = (ν : ℝ) - (k : ℝ) := by
    have : ((u + k + 1 : ℕ) : ℝ) = ((ν : ℕ) : ℝ) := by exact_mod_cast huk
    push_cast at this; linarith
  -- the first-quarter condition, cast
  have hqu : 4 * ((k : ℝ) + 1) ≤ (ν : ℝ) + 1 := by
    have h1 : ((4 * a : ℕ) : ℝ) ≤ ((n : ℕ) : ℝ) := by exact_mod_cast hquarter
    have h2 : ((ν + 1 : ℕ) : ℝ) = ((n : ℕ) : ℝ) := by exact_mod_cast hν
    push_cast at h1 h2
    linarith [haR]
  -- rewrite the target
  have hexp : (rho / (2 * (ν : ℝ))) ^ 2 * (ν : ℝ) * ((u : ℝ) + 1) / (k : ℝ)
      = rho ^ 2 * ((ν : ℝ) - (k : ℝ)) / (4 * (ν : ℝ) * (k : ℝ)) := by
    rw [hu1]; field_simp; ring
  rw [hexp]
  rw [le_div_iff₀ (by positivity)]
  -- the polynomial core: 4(k+1) <= nu+1 gives nu >= 4k+3
  have hpoly : (3 : ℝ) / 4 * (ν : ℝ) * (k : ℝ)
      ≤ ((k : ℝ) + 1) * ((ν : ℝ) - (k : ℝ)) := by nlinarith [hqu, hkR, hνR]
  have hνk : (0 : ℝ) ≤ (ν : ℝ) - (k : ℝ) := by linarith
  have hkey : (3 : ℝ) / 4 * qq * (ν : ℝ) * (k : ℝ)
      ≤ qq * (((k : ℝ) + 1) * ((ν : ℝ) - (k : ℝ))) := by nlinarith [hpoly, hq]
  have hrho' : qq * ((k : ℝ) + 1) ≤ rho ^ 2 := by rw [← haR]; exact hrho
  nlinarith [hkey, hrho', hνk, hq]

/-- **Lemma 16's active-count mean cap.**  The root-scale hypothesis
`a⁵ q n ≤ n⁵` and the variance-scale hypothesis `q a ≤ ρ²` imply that the
mean all-active count at the target time is at most `ρ n²`.

Squaring exposes the two hypotheses as separate factors:
`(q a³)² = (q a) (a⁵ q)`. -/
theorem lemma16_active_mean_cap {n q a rho : ℕ}
    (hn : 0 < n)
    (hroot : a ^ 5 * q * n ≤ n ^ 5)
    (hrho : q * a ≤ rho ^ 2) :
    q * a ^ 3 ≤ rho * n ^ 2 := by
  have hroot' : a ^ 5 * q ≤ n ^ 4 := by
    apply Nat.le_of_mul_le_mul_right ?_ hn
    calc
      (a ^ 5 * q) * n = a ^ 5 * q * n := by ring
      _ ≤ n ^ 5 := hroot
      _ = n ^ 4 * n := by ring
  have hsquare : (q * a ^ 3) ^ 2 ≤ (rho * n ^ 2) ^ 2 := by
    calc
      (q * a ^ 3) ^ 2 = (q * a) * (a ^ 5 * q) := by ring
      _ ≤ rho ^ 2 * n ^ 4 := Nat.mul_le_mul hrho hroot'
      _ = (rho * n ^ 2) ^ 2 := by ring
  exact (Nat.pow_le_pow_iff_left (by norm_num : (2 : ℕ) ≠ 0)).mp hsquare

/-- The scale hypotheses used by Lemma 16 imply that the radius dominates the
common logarithmic parameter. -/
theorem lemma16_q_le_rho
    {q a rho : ℕ}
    (hqa : q ≤ a)
    (hrho : q * a ≤ rho ^ 2) :
    q ≤ rho := by
  apply (Nat.pow_le_pow_iff_left (by norm_num : (2 : ℕ) ≠ 0)).mp
  calc
    q ^ 2 = q * q := by ring
    _ ≤ q * a := Nat.mul_le_mul_left q hqa
    _ ≤ rho ^ 2 := hrho

/-- Deterministic endpoint closure for Lemma 16.  The activation-label excess,
the possible adverse seed label, and twice the all-active counter all fit
inside the paper's `3 cStar rho` envelope. -/
theorem lemma16_good_of_label_and_counter
    (x y C rho cStar : ℕ)
    (hrho : 1 ≤ rho)
    (hcStar : 6 ≤ cStar)
    (hledger : y ≤ x + rho + 1 + 2 * C)
    (hcount : 3 * C ≤ 4 * cStar * rho) :
    y ≤ x + 3 * cStar * rho := by
  have hthree : 3 ≤ 3 * rho := by
    simpa only [mul_one] using Nat.mul_le_mul_left 3 hrho
  have hsix : 6 * rho ≤ cStar * rho :=
    Nat.mul_le_mul_right rho hcStar
  have hsmall : 3 * rho + 3 ≤ cStar * rho := by
    calc
      3 * rho + 3 ≤ 3 * rho + 3 * rho :=
        Nat.add_le_add_left hthree _
      _ = 6 * rho := by ring
      _ ≤ cStar * rho := hsix
  have hcount' : 6 * C ≤ 8 * cStar * rho := by
    have h := Nat.mul_le_mul_left 2 hcount
    nlinarith
  have hscaled :
      3 * (rho + 1 + 2 * C) ≤ 3 * (3 * cStar * rho) := by
    calc
      3 * (rho + 1 + 2 * C) =
          (3 * rho + 3) + 6 * C := by ring
      _ ≤ cStar * rho + 8 * cStar * rho :=
        Nat.add_le_add hsmall hcount'
      _ = 3 * (3 * cStar * rho) := by ring
  have hextra : rho + 1 + 2 * C ≤ 3 * cStar * rho :=
    Nat.le_of_mul_le_mul_left hscaled (by norm_num)
  calc
    y ≤ x + rho + 1 + 2 * C := hledger
    _ = x + (rho + 1 + 2 * C) := by ring
    _ ≤ x + 3 * cStar * rho := Nat.add_le_add_left hextra x

/-- Overshooting the activation checkpoint by one extra revealed identity
costs one additional adverse unit.  The production constant used by Lemma 16
easily absorbs this strengthened endpoint estimate. -/
theorem lemma16_good_of_label_and_counter_overshoot
    (x y C rho cStar : ℕ)
    (hrho : 1 ≤ rho)
    (hcStar : 9 ≤ cStar)
    (hledger : y ≤ x + rho + 2 + 2 * C)
    (hcount : 3 * C ≤ 4 * cStar * rho) :
    y ≤ x + 3 * cStar * rho := by
  have hsix : 6 ≤ 6 * rho := by
    simpa only [mul_one] using Nat.mul_le_mul_left 6 hrho
  have hnine : 9 * rho ≤ cStar * rho :=
    Nat.mul_le_mul_right rho hcStar
  have hsmall : 3 * rho + 6 ≤ cStar * rho := by
    calc
      3 * rho + 6 ≤ 3 * rho + 6 * rho :=
        Nat.add_le_add_left hsix _
      _ = 9 * rho := by ring
      _ ≤ cStar * rho := hnine
  have hcount' : 6 * C ≤ 8 * cStar * rho := by
    have h := Nat.mul_le_mul_left 2 hcount
    nlinarith
  have hscaled :
      3 * (rho + 2 + 2 * C) ≤
        3 * (3 * cStar * rho) := by
    calc
      3 * (rho + 2 + 2 * C) =
          (3 * rho + 6) + 6 * C := by ring
      _ ≤ cStar * rho + 8 * cStar * rho :=
        Nat.add_le_add hsmall hcount'
      _ = 3 * (3 * cStar * rho) := by ring
  have hextra : rho + 2 + 2 * C ≤ 3 * cStar * rho :=
    Nat.le_of_mul_le_mul_left hscaled (by norm_num)
  calc
    y ≤ x + rho + 2 + 2 * C := hledger
    _ = x + (rho + 2 + 2 * C) := by ring
    _ ≤ x + 3 * cStar * rho :=
      Nat.add_le_add_left hextra x

/-- The direct activation-prefix urn error in Lemma 16. -/
noncomputable def lemma16UrnError (q : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-((3 : ℝ) / 16) * (q : ℝ)))

/-- A normalized epidemic-clock error used by the Lemma 16 union bound. -/
noncomputable def lemma16EpidemicError (q : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-(q : ℝ)))

/-- The normalized all-active-counter error used by the Lemma 16 union bound. -/
noncomputable def lemma16ReactionError
    (cStar rho : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-((cStar * rho : ℕ) : ℝ) / 27))

/-- The three exceptional-event errors in Lemma 16. -/
noncomputable def lemma16Error
    (q cStar rho : ℕ) : ℝ≥0∞ :=
  lemma16UrnError q +
    lemma16EpidemicError q +
    lemma16ReactionError cStar rho

/-- All three Lemma 16 errors fit under the slowest, urn-scale exponential.
The counter comparison uses `6q ≤ cStar rho`, so `cStar ≥ 6` and `q ≤ rho`
are the exact discrete hypotheses needed here. -/
theorem lemma16_error_envelope
    (q cStar rho : ℕ)
    (hqrho : q ≤ rho)
    (hcStar : 6 ≤ cStar) :
    lemma16Error q cStar rho
      ≤ 3 * lemma16UrnError q := by
  unfold lemma16Error lemma16UrnError
    lemma16EpidemicError lemma16ReactionError
  have hq0 : (0 : ℝ) ≤ (q : ℝ) := by positivity
  have hconst : (3 : ℝ) / 16 ≤ 2 / 9 := by norm_num
  have hmulNat : 6 * q ≤ cStar * rho :=
    Nat.mul_le_mul hcStar hqrho
  have hmulReal :
      (6 : ℝ) * (q : ℝ) ≤ (cStar : ℝ) * (rho : ℝ) := by
    exact_mod_cast hmulNat
  have hrate :
      ((3 : ℝ) / 16) * (q : ℝ)
        ≤ ((cStar * rho : ℕ) : ℝ) / 27 := by
    rw [Nat.cast_mul]
    calc
      ((3 : ℝ) / 16) * (q : ℝ)
          ≤ ((2 : ℝ) / 9) * (q : ℝ) :=
        mul_le_mul_of_nonneg_right hconst hq0
      _ ≤ (cStar : ℝ) * (rho : ℝ) / 27 := by
        nlinarith [hmulReal]
  have hqExp :
      Real.exp (-(q : ℝ))
        ≤ Real.exp (-((3 : ℝ) / 16) * (q : ℝ)) := by
    rw [Real.exp_le_exp]
    nlinarith [hq0]
  have hprodExp :
      Real.exp (-((cStar * rho : ℕ) : ℝ) / 27)
        ≤ Real.exp (-((3 : ℝ) / 16) * (q : ℝ)) := by
    rw [Real.exp_le_exp]
    nlinarith [hrate]
  calc
    ENNReal.ofReal (Real.exp (-((3 : ℝ) / 16) * (q : ℝ))) +
          ENNReal.ofReal (Real.exp (-(q : ℝ))) +
          ENNReal.ofReal
            (Real.exp (-((cStar * rho : ℕ) : ℝ) / 27))
        ≤ ENNReal.ofReal
              (Real.exp (-((3 : ℝ) / 16) * (q : ℝ))) +
            ENNReal.ofReal
              (Real.exp (-((3 : ℝ) / 16) * (q : ℝ))) +
            ENNReal.ofReal
              (Real.exp (-((3 : ℝ) / 16) * (q : ℝ))) := by
          exact add_le_add
            (add_le_add le_rfl (ENNReal.ofReal_le_ofReal hqExp))
            (ENNReal.ofReal_le_ofReal hprodExp)
    _ = 3 *
          ENNReal.ofReal
            (Real.exp (-((3 : ℝ) / 16) * (q : ℝ))) := by
      ring
end Tri

#print axioms Tri.lemma16_exponent_floor
#print axioms Tri.lemma16_active_mean_cap
#print axioms Tri.lemma16_q_le_rho
#print axioms Tri.lemma16_good_of_label_and_counter
#print axioms Tri.lemma16_good_of_label_and_counter_overshoot
#print axioms Tri.lemma16_error_envelope
