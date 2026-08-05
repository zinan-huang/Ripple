/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.RelaxedBand
import Tri.Ladder

/-!
# Concrete scalar rung for unequal reaction rates

This file instantiates `relaxedBand_phase_fail` on a dyadic minority scale `P`.
The stage starts at `y = P`, succeeds at `y ≤ P/2`, and declares ruin after an
upward minority excursion of `L`. The concrete productive-event threshold and
raw horizon are

```
M = 64 * R * P,
T = 4096 * H * n.
```
-/

namespace Tri

open scoped ENNReal

def relaxedDyadicLower (n P L : ℕ) : ℕ :=
  n - (P + L)

def relaxedDyadicStart (n P : ℕ) : ℕ :=
  n - P

def relaxedDyadicTarget (n P : ℕ) : ℕ :=
  n - P / 2

def relaxedDyadicBHi (P L : ℕ) : ℕ :=
  P + L - 2

def relaxedDyadicYLo (P : ℕ) : ℕ :=
  P / 2 + 1

def relaxedDyadicM (R P : ℕ) : ℕ :=
  64 * R * P

def relaxedDyadicHorizon (H n : ℕ) : ℕ :=
  4096 * H * n

noncomputable def relaxedDyadicProductiveP
    (r : RelaxedRate) (n P L : ℕ) : ℝ≥0∞ :=
  relaxedBandProductiveFloor r n
    (relaxedDyadicLower n P L + 1) (relaxedDyadicYLo P)

noncomputable def relaxedDyadicBandError
    (r : RelaxedRate) (n P L R H : ℕ)
    (beta tau : NNReal) : ℝ≥0∞ :=
  let start := relaxedDyadicStart n P
  let target := relaxedDyadicTarget n P
  let M := relaxedDyadicM R P
  let T := relaxedDyadicHorizon H n
  let p := relaxedDyadicProductiveP r n P L
  (beta : ℝ≥0∞)⁻¹ ^ L +
    (relaxedDirW (beta + tau) : ℝ≥0∞) ^ start /
      ((relaxedDirW (beta + tau) : ℝ≥0∞) ^ (target - 1) *
        (relaxedDirEta (beta + tau) : ℝ≥0∞) ^ M) +
    ((1 - p) + p * ((1 : ℝ≥0∞) / 2)) ^ T /
      ((1 : ℝ≥0∞) / 2) ^ M

/-- The exact rectangular productive floor is a probability. -/
theorem relaxedDyadicProductiveP_le_one
    (r : RelaxedRate) (n P L : ℕ)
    (hP : 1 ≤ P) (hL : 1 ≤ L)
    (hroom : 2 * (P + L) ≤ n) :
    relaxedDyadicProductiveP r n P L ≤ 1 := by
  let lower := relaxedDyadicLower n P L
  let target := relaxedDyadicTarget n P
  let bHi := relaxedDyadicBHi P L
  let yLo := relaxedDyadicYLo P
  have h3 : 3 ≤ n := by omega
  have hband : lower + bHi + 2 = n := by
    dsimp only [lower, bHi, relaxedDyadicLower, relaxedDyadicBHi]
    omega
  have hyLo : target + yLo = n + 1 := by
    dsimp only [target, yLo, relaxedDyadicTarget, relaxedDyadicYLo]
    omega
  have hlive : lower + 1 < target := by
    dsimp only [lower, target, relaxedDyadicLower, relaxedDyadicTarget]
    omega
  have hfloor :=
    relaxedBandProductiveFloor_le r n lower target yLo lower bHi
      h3 hband hyLo le_rfl hlive
  have hsum :=
    relaxedTriStep_masses_sum r lower (bHi + 1) (by omega)
  calc
    relaxedDyadicProductiveP r n P L =
        relaxedBandProductiveFloor r n (lower + 1) yLo := by
          rfl
    _ ≤ relaxedTriStep r (lower + 1) (bHi + 1) (by omega) lower +
          relaxedTriStep r (lower + 1) (bHi + 1) (by omega) (lower + 2) :=
      hfloor
    _ ≤ relaxedTriStep r (lower + 1) (bHi + 1) (by omega) lower +
          relaxedTriStep r (lower + 1) (bHi + 1) (by omega) (lower + 1) +
          relaxedTriStep r (lower + 1) (bHi + 1) (by omega) (lower + 2) := by
      gcongr
      exact le_add_right le_rfl
    _ = 1 := hsum

/-- Concrete stopped-band rung from minority scale `P` to `⌊P/2⌋`.

All stochastic parameters of `relaxedBand_phase_fail` are instantiated:
`wp = 1/2`, the exact rectangular productive floor and its complement,
`M = 64RP`, and `T = 4096Hn`. -/
theorem relaxedDyadicBand_reaches
    (r : RelaxedRate)
    (n P L R H : ℕ)
    (beta slack tau : NNReal)
    (hP : 1 ≤ P) (hL : 1 ≤ L) (hR : 1 ≤ R)
    (hroom : 2 * (P + L) ≤ n)
    (hbeta1 : 1 ≤ beta)
    (hslack : r.fire + slack ≤ beta)
    (htau :
      tau * (relaxedDyadicBHi P L : NNReal) ≤ slack)
    (hmargin :
      (1 : NNReal) + 1 / (R : NNReal) ≤ beta + tau)
    (hcorner :
      beta * (relaxedDyadicBHi P L + 1 : NNReal) ≤
        r.fire * (relaxedDyadicLower n P L + 1 : NNReal)) :
    Reaches
      (relaxedBandStop r n
        (relaxedDyadicLower n P L) (relaxedDyadicTarget n P))
      (relaxedDyadicHorizon H n)
      (fun q => q = (relaxedDyadicStart n P, 0))
      (fun q => relaxedDyadicTarget n P ≤ q.1)
      (relaxedDyadicBandError r n P L R H beta tau) := by
  let lower := relaxedDyadicLower n P L
  let start := relaxedDyadicStart n P
  let target := relaxedDyadicTarget n P
  let bHi := relaxedDyadicBHi P L
  let yLo := relaxedDyadicYLo P
  let M := relaxedDyadicM R P
  let T := relaxedDyadicHorizon H n
  let p := relaxedDyadicProductiveP r n P L
  have h3 : 3 ≤ n := by omega
  have htarget : target ≤ n := by
    dsimp only [target, relaxedDyadicTarget]
    omega
  have hband : lower + bHi + 2 = n := by
    dsimp only [lower, bHi, relaxedDyadicLower, relaxedDyadicBHi]
    omega
  have hyLo : target + yLo = n + 1 := by
    dsimp only [target, yLo, relaxedDyadicTarget, relaxedDyadicYLo]
    omega
  have hstart : start = lower + L := by
    dsimp only [start, lower, relaxedDyadicStart, relaxedDyadicLower]
    omega
  have hstartLive : lower < start ∧ start < target := by
    dsimp only [lower, start, target, relaxedDyadicLower,
      relaxedDyadicStart, relaxedDyadicTarget]
    omega
  have hB : 1 < beta + tau := by
    have hRpos : (0 : NNReal) < (R : NNReal) := by
      exact_mod_cast (show 0 < R by omega)
    have hrecip : (0 : NNReal) < 1 / (R : NNReal) := by
      positivity
    exact lt_of_lt_of_le (lt_add_of_pos_right 1 hrecip) hmargin
  have hpLe : p ≤ 1 := by
    dsimp only [p]
    exact relaxedDyadicProductiveP_le_one r n P L hP hL hroom
  have hpSum : p + (1 - p) = 1 := by
    rw [add_comm]
    exact tsub_add_cancel_of_le hpLe
  intro q hq
  subst q
  have hphase :=
    relaxedBand_phase_fail
      r n lower target bHi L M T yLo beta slack tau
      ((1 : ℝ≥0∞) / 2) p (1 - p)
      h3 htarget hband hyLo hbeta1 hslack htau hB hcorner
      (by norm_num) (by norm_num) hpSum le_rfl
      (start, 0) hstart hstartLive rfl
  change
    (∑' z, if target ≤ z.1 then 0 else
      iter (relaxedBandStop r n lower target) T (start, 0) z) ≤ _
  calc
    (∑' z, if target ≤ z.1 then 0 else
        iter (relaxedBandStop r n lower target) T (start, 0) z) =
      ∑' z, if z.1 + 1 ≤ target then
        iter (relaxedBandStop r n lower target) T (start, 0) z else 0 := by
          apply tsum_congr
          intro z
          by_cases hz : target ≤ z.1
          · have hn : ¬ z.1 + 1 ≤ target := by omega
            simp [hz, hn]
          · have hy : z.1 + 1 ≤ target := by omega
            simp [hz, hy]
    _ ≤ (beta : ℝ≥0∞)⁻¹ ^ L +
        (relaxedDirW (beta + tau) : ℝ≥0∞) ^ start /
          ((relaxedDirW (beta + tau) : ℝ≥0∞) ^ (target - 1) *
            (relaxedDirEta (beta + tau) : ℝ≥0∞) ^ M) +
        ((1 - p) + p * ((1 : ℝ≥0∞) / 2)) ^ T /
          ((1 : ℝ≥0∞) / 2) ^ M := by
            simpa only [mul_one] using hphase
    _ = relaxedDyadicBandError r n P L R H beta tau := by
      simp only [relaxedDyadicBandError, start, target, M, T, p]

end Tri

#print axioms Tri.relaxedDyadicProductiveP_le_one
#print axioms Tri.relaxedDyadicBand_reaches
