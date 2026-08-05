/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.SingleBClockProjection
import Tri.HeavyBClockConstants

/-!
# Scalar constants for the Single-B joint clock

The conservative fixed horizon uses

`K = n+2M`, `Hocc = 64K`, `T = 128K`.

The per-rung horizon is `Θ(n)` with NO `γ` dependence — this is load-bearing
for the lazy creation budget `H = T+1` of the repaired band.  The half-horizon
carries the factor `64` (not Heavy-B's `32`) because the Single-B blank branch
runs at the doubled scale `2n`; the blank envelope is then the Heavy-B one at
scale `2n`, giving `exp(−g²/(2n))`.
-/

namespace Tri

open scoped ENNReal

/-- Fuel budget used by the fixed Single-B clock envelope. -/
def singleClockBudget (n M : ℕ) : ℕ := n + 2 * M

/-- Number of ticks assigned to either occupation branch.  The factor is `64`
so that the doubled-scale blank exposure `32·(2n)` is covered. -/
def singleClockHalfHorizon (n M : ℕ) : ℕ :=
  64 * singleClockBudget n M

/-- Full raw-interaction horizon of one early Single-B rung. -/
def singleClockHorizon (n M : ℕ) : ℕ :=
  128 * singleClockBudget n M

theorem two_singleClockHalfHorizon (n M : ℕ) :
    2 * singleClockHalfHorizon n M = singleClockHorizon n M := by
  simp only [singleClockHalfHorizon, singleClockHorizon, singleClockBudget]
  ring

/-- **The γ-free `Θ(n)` horizon witness**: the per-rung horizon is an explicit
linear function of the population and the resolution quota alone — no gap,
drift, or `γ` parameter enters. -/
theorem singleClockHorizon_linear (n M : ℕ) :
    singleClockHorizon n M = 128 * n + 256 * M := by
  simp only [singleClockHorizon, singleClockBudget]
  ring

/-- The concrete normal-occupation error is bounded by `(3/4)^K`; the enlarged
`64K` half-horizon only helps. -/
theorem singleNormalClockError_le (K : ℕ) :
    1 / (((32 : ℝ≥0∞) / 31) ^ (64 * K) * (1 / 2) ^ K) ≤
      ((3 : ℝ≥0∞) / 4) ^ K := by
  have hbase : (1 : ℝ≥0∞) ≤ (32 : ℝ≥0∞) / 31 := by
    rw [← ENNReal.toReal_le_toReal ENNReal.one_ne_top
      (ENNReal.div_ne_top (by norm_num) (by norm_num))]
    norm_num
  have hmono :
      ((32 : ℝ≥0∞) / 31) ^ (32 * K) ≤ ((32 : ℝ≥0∞) / 31) ^ (64 * K) :=
    pow_le_pow_right' hbase (by omega)
  calc
    1 / (((32 : ℝ≥0∞) / 31) ^ (64 * K) * (1 / 2) ^ K)
        ≤ 1 / (((32 : ℝ≥0∞) / 31) ^ (32 * K) * (1 / 2) ^ K) :=
      ENNReal.div_le_div_left (mul_le_mul' hmono le_rfl) 1
    _ ≤ ((3 : ℝ≥0∞) / 4) ^ K := heavyNormalClockError_le K

/-- Gaussian-scale bound for the Single-B blank-clock error: the Heavy-B
envelope at the doubled scale `2n`. -/
theorem singleBlankClockError_le_exp_neg
    (n g start hi Hocc : ℕ)
    (hn : 0 < n) (hg : g ≤ 2 * n)
    (hstart : start ≤ hi) (hwidth : hi ≤ start + g)
    (hH : 64 * n ≤ Hocc) :
    singleBlankW n g ^ start /
        (singleBlankW n g ^ hi * singleBlankEta n g ^ Hocc) ≤
      ENNReal.ofReal
        (Real.exp (-((g : ℝ) ^ 2 / (2 * (n : ℝ))))) := by
  have h := heavyBlankClockError_le_exp_neg (2 * n) g start hi Hocc
    (by omega) hg hstart hwidth (by omega)
  have hcast : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by
    push_cast
    ring
  rw [hcast] at h
  simpa [singleBlankW, singleBlankEta] using h

/-- A uniform envelope for the two occupation-clock errors of one Single-B
rung. -/
noncomputable def singleJointClockEnvelope (n g M : ℕ) : ℝ≥0∞ :=
  ((3 : ℝ≥0∞) / 4) ^ singleClockBudget n M +
    ENNReal.ofReal (Real.exp (-((g : ℝ) ^ 2 / (2 * (n : ℝ)))))

/-- At the concrete half-horizon, the two occupation-clock errors are bounded
by a geometric normal term plus a Gaussian-scale blank term. -/
theorem singleJointClockError_le
    (n g start hi M : ℕ)
    (hn : 0 < n) (hg : g ≤ 2 * n)
    (hstart : start ≤ hi) (hwidth : hi ≤ start + g) :
    1 / (((32 : ℝ≥0∞) / 31) ^ singleClockHalfHorizon n M *
          (1 / 2) ^ singleClockBudget n M) +
        singleBlankW n g ^ start /
          (singleBlankW n g ^ hi *
            singleBlankEta n g ^ singleClockHalfHorizon n M) ≤
      singleJointClockEnvelope n g M := by
  unfold singleJointClockEnvelope
  apply add_le_add
  · simpa [singleClockHalfHorizon] using
      singleNormalClockError_le (singleClockBudget n M)
  · apply singleBlankClockError_le_exp_neg
      n g start hi (singleClockHalfHorizon n M) hn hg hstart hwidth
    simp only [singleClockHalfHorizon, singleClockBudget]
    omega

section Inhabitation

example :
    1 / (((32 : ℝ≥0∞) / 31) ^ singleClockHalfHorizon 160 1 *
          (1 / 2) ^ singleClockBudget 160 1) +
        singleBlankW 160 2 ^ 167 /
          (singleBlankW 160 2 ^ 168 *
            singleBlankEta 160 2 ^ singleClockHalfHorizon 160 1) ≤
      singleJointClockEnvelope 160 2 1 := by
  apply singleJointClockError_le
  · norm_num
  · norm_num
  · norm_num
  · norm_num

end Inhabitation

end Tri

#print axioms Tri.two_singleClockHalfHorizon
#print axioms Tri.singleClockHorizon_linear
#print axioms Tri.singleNormalClockError_le
#print axioms Tri.singleBlankClockError_le_exp_neg
#print axioms Tri.singleJointClockError_le
