/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.ByzantineRelaxedBridge

/-!
# Paper Lemma 10: the second Byzantine effective-rate bound

Write `a = y + z` and `g = γ lg n`.  The paper assumes `a = n / k`,
`k ≥ 4`, and takes `n` sufficiently large.  We avoid truncated subtraction
and division by using witnesses

```
k * a = n
a + g + den = n.
```

The explicit large-population condition `68g < 3n` is sufficient for the
strict scalar comparison in the printed proof.
-/

namespace Tri.Byzantine

open scoped ENNReal

variable {n B : ℕ}

/-- Elementary exponential domination used to make the paper's phrase
"for sufficiently large `n`" explicit. -/
theorem square_le_two_pow_of_four_le
    (q : ℕ) (hq : 4 ≤ q) :
    q ^ 2 ≤ 2 ^ q := by
  induction q, hq using Nat.le_induction with
  | base =>
      norm_num
  | succ q hq ih =>
      have hstep : (q + 1) ^ 2 ≤ 2 * q ^ 2 := by
        nlinarith
      calc
        (q + 1) ^ 2 ≤ 2 * q ^ 2 := hstep
        _ ≤ 2 * 2 ^ q := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (q + 1) := by
          rw [pow_succ]
          ring

/-- A concrete population threshold for the scalar large-`n` premise in
paper Lemma 10.  The constant is deliberately simple rather than optimized. -/
theorem lemma10_largePopulation
    {n γ : ℕ}
    (hn : 2 ^ max 4 (68 * γ) ≤ n) :
    68 * (γ * Nat.log 2 n) < 3 * n := by
  have hnpos : 0 < n := by
    have hp : 0 < 2 ^ max 4 (68 * γ) := by positivity
    exact hp.trans_le hn
  have hlog :
      max 4 (68 * γ) ≤ Nat.log 2 n :=
    Nat.le_log_of_pow_le (by norm_num) hn
  have hfour : 4 ≤ Nat.log 2 n :=
    (le_max_left 4 (68 * γ)).trans hlog
  have hgamma : 68 * γ ≤ Nat.log 2 n :=
    (le_max_right 4 (68 * γ)).trans hlog
  have hsquare :
      (Nat.log 2 n) ^ 2 ≤ 2 ^ Nat.log 2 n :=
    square_le_two_pow_of_four_le _ hfour
  have hproduct :
      68 * (γ * Nat.log 2 n) ≤ (Nat.log 2 n) ^ 2 := by
    calc
      68 * (γ * Nat.log 2 n) =
          (68 * γ) * Nat.log 2 n := by ring
      _ ≤ (Nat.log 2 n) * Nat.log 2 n :=
        Nat.mul_le_mul_right _ hgamma
      _ = (Nat.log 2 n) ^ 2 := by ring
  have hpow :
      2 ^ Nat.log 2 n ≤ n :=
    Nat.pow_log_le_self 2 hnpos.ne'
  have hle :
      68 * (γ * Nat.log 2 n) ≤ n :=
    hproduct.trans (hsquare.trans hpow)
  omega

/-- Paper Lemma 10 in division-free count form.  The conclusion is

`6(a+g) / (5 den) < y/a`

after cross multiplication, where `a = y+z`. -/
theorem lemma10_effectiveRate_cross
    {s : State n B} {k g den : ℕ}
    (hx : State.x s + 2 * State.z s < n)
    (hk : 4 ≤ k)
    (hshare : k * (State.y s + State.z s) = n)
    (hden : State.y s + State.z s + g + den = n)
    (hlarge : 68 * g < 3 * n) :
    6 * (State.y s + State.z s + g) *
        (State.y s + State.z s) <
      5 * den * State.y s := by
  have htotal := State.total s
  have hyz : State.z s < State.y s := by
    omega
  have hy : 0 < State.y s := by
    omega
  have ha4 : 4 * (State.y s + State.z s) ≤ n := by
    calc
      4 * (State.y s + State.z s) ≤
          k * (State.y s + State.z s) :=
        Nat.mul_le_mul_right _ hk
      _ = n := hshare
  have hscalar :
      12 * (State.y s + State.z s + g) < 5 * den := by
    omega
  have hcoef :
      0 < 6 * (State.y s + State.z s + g) := by
    omega
  have hpair :
      State.y s + State.z s < 2 * State.y s := by
    omega
  calc
    6 * (State.y s + State.z s + g) *
          (State.y s + State.z s) <
        6 * (State.y s + State.z s + g) *
          (2 * State.y s) :=
      (Nat.mul_lt_mul_left hcoef).2 hpair
    _ = (12 * (State.y s + State.z s + g)) *
          State.y s := by ring
    _ < (5 * den) * State.y s :=
      (Nat.mul_lt_mul_right hy).2 hscalar
    _ = 5 * den * State.y s := by ring

/-- Count-level cross form with the paper denominator written as
`x - γ lg n`.  This is the direct arithmetic input to the paper-facing
effective-rate declaration below. -/
theorem lemma10_effectiveFireRate_count_cross
    {s : State n B} {k L : ℕ}
    (hx : State.x s + 2 * State.z s < n)
    (hk : 4 ≤ k)
    (hshare : k * (State.y s + State.z s) = n)
    (hlarge : 68 * L < 3 * n) :
    6 * (State.y s + State.z s + L) *
          (State.y s + State.z s) +
        5 * L * State.y s <
      5 * State.x s * State.y s := by
  have htotal := State.total s
  have hyz : State.z s < State.y s := by
    omega
  have hy : 0 < State.y s := by
    omega
  have ha4 : 4 * (State.y s + State.z s) ≤ n := by
    calc
      4 * (State.y s + State.z s) ≤
          k * (State.y s + State.z s) :=
        Nat.mul_le_mul_right _ hk
      _ = n := hshare
  have hscalar :
      12 * (State.y s + State.z s + L) + 5 * L <
        5 * State.x s := by
    omega
  have hcoef :
      0 < 6 * (State.y s + State.z s + L) := by
    omega
  have hpair :
      State.y s + State.z s < 2 * State.y s := by
    omega
  have hfirst :
      6 * (State.y s + State.z s + L) *
          (State.y s + State.z s) <
        12 * (State.y s + State.z s + L) *
          State.y s := by
    calc
      6 * (State.y s + State.z s + L) *
          (State.y s + State.z s) <
          6 * (State.y s + State.z s + L) *
            (2 * State.y s) :=
        (Nat.mul_lt_mul_left hcoef).2 hpair
      _ = 12 * (State.y s + State.z s + L) *
          State.y s := by ring
  calc
    6 * (State.y s + State.z s + L) *
          (State.y s + State.z s) +
        5 * L * State.y s <
      12 * (State.y s + State.z s + L) *
          State.y s +
        5 * L * State.y s :=
      Nat.add_lt_add_right hfirst _
    _ = (12 * (State.y s + State.z s + L) + 5 * L) *
        State.y s := by ring
    _ < (5 * State.x s) * State.y s :=
      (Nat.mul_lt_mul_right hy).2 hscalar
    _ = 5 * State.x s * State.y s := by ring

/-- Paper Lemma 10 as a strict, subtraction-free, division-free effective-rate
inequality.  It is equivalent to

`fire > (6/5) * (n/k + L) / (n(k-1)/k - L)`

under `k*(y+z)=n`, with `L = γ lg n`. -/
theorem lemma10_effectiveFireRate_cross
    {s : State n B} {γ k : ℕ}
    (r : RelaxedRate)
    (hrate : IsPaperEffectiveRate r s)
    (hk : 4 ≤ k)
    (hpopulation : k * (State.y s + State.z s) = n)
    (hpost : State.x s + 2 * State.z s < n)
    (hsize : 68 * (γ * Nat.log 2 n) < 3 * n) :
    (6 : ℝ≥0∞) *
          ((State.y s + State.z s + γ * Nat.log 2 n : ℕ) :
            ℝ≥0∞) +
        (5 : ℝ≥0∞) *
          ((γ * Nat.log 2 n : ℕ) : ℝ≥0∞) *
          (r.fire : ℝ≥0∞) <
      (5 : ℝ≥0∞) * (State.x s : ℝ≥0∞) *
        (r.fire : ℝ≥0∞) := by
  have hcount :=
    lemma10_effectiveFireRate_count_cross
      (s := s) hpost hk hpopulation hsize
  have htotal := State.total s
  have hq_pos : 0 < State.y s + State.z s := by
    omega
  have hq_ne :
      ((State.y s + State.z s : ℕ) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast hq_pos.ne'
  have hq_top :
      ((State.y s + State.z s : ℕ) : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.natCast_ne_top _
  apply
    (ENNReal.mul_lt_mul_iff_right hq_ne hq_top).mp
  calc
    ((State.y s + State.z s : ℕ) : ℝ≥0∞) *
        ((6 : ℝ≥0∞) *
            ((State.y s + State.z s + γ * Nat.log 2 n : ℕ) :
              ℝ≥0∞) +
          (5 : ℝ≥0∞) *
            ((γ * Nat.log 2 n : ℕ) : ℝ≥0∞) *
            (r.fire : ℝ≥0∞)) =
        ((6 * (State.y s + State.z s + γ * Nat.log 2 n) *
              (State.y s + State.z s) +
            5 * (γ * Nat.log 2 n) * State.y s : ℕ) :
          ℝ≥0∞) := by
            calc
              ((State.y s + State.z s : ℕ) : ℝ≥0∞) *
                  ((6 : ℝ≥0∞) *
                      ((State.y s + State.z s +
                        γ * Nat.log 2 n : ℕ) : ℝ≥0∞) +
                    (5 : ℝ≥0∞) *
                      ((γ * Nat.log 2 n : ℕ) : ℝ≥0∞) *
                      (r.fire : ℝ≥0∞)) =
                  (6 : ℝ≥0∞) *
                      ((State.y s + State.z s +
                        γ * Nat.log 2 n : ℕ) : ℝ≥0∞) *
                      ((State.y s : ℝ≥0∞) +
                        (State.z s : ℝ≥0∞)) +
                    (5 : ℝ≥0∞) *
                      ((γ * Nat.log 2 n : ℕ) : ℝ≥0∞) *
                      ((r.fire : ℝ≥0∞) *
                        ((State.y s : ℝ≥0∞) +
                          (State.z s : ℝ≥0∞))) := by
                            push_cast
                            ring
              _ = (6 : ℝ≥0∞) *
                      ((State.y s + State.z s +
                        γ * Nat.log 2 n : ℕ) : ℝ≥0∞) *
                      ((State.y s : ℝ≥0∞) +
                        (State.z s : ℝ≥0∞)) +
                    (5 : ℝ≥0∞) *
                      ((γ * Nat.log 2 n : ℕ) : ℝ≥0∞) *
                      (State.y s : ℝ≥0∞) := by
                            rw [hrate.fire_cross]
              _ = ((6 * (State.y s + State.z s +
                        γ * Nat.log 2 n) *
                      (State.y s + State.z s) +
                    5 * (γ * Nat.log 2 n) * State.y s : ℕ) :
                  ℝ≥0∞) := by
                            push_cast
                            ring
    _ < ((5 * State.x s * State.y s : ℕ) : ℝ≥0∞) := by
          exact_mod_cast hcount
    _ = ((State.y s + State.z s : ℕ) : ℝ≥0∞) *
        ((5 : ℝ≥0∞) * (State.x s : ℝ≥0∞) *
          (r.fire : ℝ≥0∞)) := by
            calc
              ((5 * State.x s * State.y s : ℕ) : ℝ≥0∞) =
                  (5 : ℝ≥0∞) * (State.x s : ℝ≥0∞) *
                    (State.y s : ℝ≥0∞) := by
                      push_cast
                      ring
              _ = (5 : ℝ≥0∞) * (State.x s : ℝ≥0∞) *
                    ((r.fire : ℝ≥0∞) *
                      ((State.y s : ℝ≥0∞) +
                        (State.z s : ℝ≥0∞))) := by
                      rw [hrate.fire_cross]
              _ = ((State.y s + State.z s : ℕ) : ℝ≥0∞) *
                    ((5 : ℝ≥0∞) * (State.x s : ℝ≥0∞) *
                      (r.fire : ℝ≥0∞)) := by
                      push_cast
                      ring

/-- Exact effective-rate form of paper Lemma 10.  The left side is algebraically
the printed

`(6/5) * (n/k + γ lg n) / (n(k-1)/k - γ lg n)`,

with `n/k = y+z`, `g = γ lg n`, and
`den = n - (y+z) - g`. -/
theorem lemma10_effectiveRate_lower
    {s : State n B} {k g den : ℕ}
    (r : RelaxedRate)
    (hrate : IsPaperEffectiveRate r s)
    (hx : State.x s + 2 * State.z s < n)
    (hk : 4 ≤ k)
    (hshare : k * (State.y s + State.z s) = n)
    (hden : State.y s + State.z s + g + den = n)
    (hlarge : 68 * g < 3 * n) :
    ((6 * (State.y s + State.z s + g) : ℕ) : ℝ≥0∞) /
        ((5 * den : ℕ) : ℝ≥0∞) <
      (r.fire : ℝ≥0∞) := by
  have hcross :=
    lemma10_effectiveRate_cross
      (s := s) hx hk hshare hden hlarge
  have htotal := State.total s
  have hyz_pos : 0 < State.y s + State.z s := by
    omega
  have hden_pos : 0 < den := by
    have hrhs :
        0 < (5 * den) * State.y s :=
      lt_of_le_of_lt (Nat.zero_le _) hcross
    have hfive : 0 < 5 * den :=
      Nat.pos_of_mul_pos_right hrhs
    exact Nat.pos_of_mul_pos_left hfive
  have ha_ne :
      ((State.y s + State.z s : ℕ) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast hyz_pos.ne'
  have ha_top :
      ((State.y s + State.z s : ℕ) : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.natCast_ne_top _
  have hscaled :
      ((6 * (State.y s + State.z s + g) : ℕ) : ℝ≥0∞) <
        ((5 * den : ℕ) : ℝ≥0∞) * (r.fire : ℝ≥0∞) := by
    apply
      (ENNReal.mul_lt_mul_iff_right ha_ne ha_top).mp
    calc
      ((State.y s + State.z s : ℕ) : ℝ≥0∞) *
          ((6 * (State.y s + State.z s + g) : ℕ) : ℝ≥0∞) =
          ((6 * (State.y s + State.z s + g) *
            (State.y s + State.z s) : ℕ) : ℝ≥0∞) := by
            push_cast
            ring
      _ < ((5 * den * State.y s : ℕ) : ℝ≥0∞) := by
            exact_mod_cast hcross
      _ = ((5 * den : ℕ) : ℝ≥0∞) *
          (State.y s : ℝ≥0∞) := by
            push_cast
            ring
      _ = ((5 * den : ℕ) : ℝ≥0∞) *
          ((r.fire : ℝ≥0∞) *
            ((State.y s : ℝ≥0∞) + (State.z s : ℝ≥0∞))) := by
            rw [hrate.fire_cross]
      _ = ((State.y s + State.z s : ℕ) : ℝ≥0∞) *
          (((5 * den : ℕ) : ℝ≥0∞) * (r.fire : ℝ≥0∞)) := by
            push_cast
            ring
  apply
    (ENNReal.div_lt_iff
      (Or.inl (by
        exact_mod_cast (Nat.mul_pos (by decide) hden_pos).ne'))
      (Or.inl (ENNReal.natCast_ne_top (5 * den)))).2
  simpa only [mul_comm] using hscaled

/-- Paper Lemma 10 with `g = γ lg n` and a concrete witness for
"sufficiently large `n`". -/
theorem lemma10_effectiveRate_lower_of_largePopulation
    {s : State n B} {k den γ : ℕ}
    (r : RelaxedRate)
    (hrate : IsPaperEffectiveRate r s)
    (hx : State.x s + 2 * State.z s < n)
    (hk : 4 ≤ k)
    (hshare : k * (State.y s + State.z s) = n)
    (hden :
      State.y s + State.z s + γ * Nat.log 2 n + den = n)
    (hn : 2 ^ max 4 (68 * γ) ≤ n) :
    ((6 * (State.y s + State.z s + γ * Nat.log 2 n) : ℕ) :
        ℝ≥0∞) /
        ((5 * den : ℕ) : ℝ≥0∞) <
      (r.fire : ℝ≥0∞) :=
  lemma10_effectiveRate_lower
    r hrate hx hk hshare hden (lemma10_largePopulation hn)

/-- Fully paper-facing Lemma 10 with an explicit threshold witnessing
"for sufficiently large `n`". -/
theorem lemma10_effectiveFireRate_cross_of_largePopulation
    {s : State n B} {γ k : ℕ}
    (r : RelaxedRate)
    (hrate : IsPaperEffectiveRate r s)
    (hk : 4 ≤ k)
    (hpopulation : k * (State.y s + State.z s) = n)
    (hpost : State.x s + 2 * State.z s < n)
    (hn : 2 ^ max 4 (68 * γ) ≤ n) :
    (6 : ℝ≥0∞) *
          ((State.y s + State.z s + γ * Nat.log 2 n : ℕ) :
            ℝ≥0∞) +
        (5 : ℝ≥0∞) *
          ((γ * Nat.log 2 n : ℕ) : ℝ≥0∞) *
          (r.fire : ℝ≥0∞) <
      (5 : ℝ≥0∞) * (State.x s : ℝ≥0∞) *
        (r.fire : ℝ≥0∞) :=
  lemma10_effectiveFireRate_cross
    r hrate hk hpopulation hpost (lemma10_largePopulation hn)

end Tri.Byzantine
