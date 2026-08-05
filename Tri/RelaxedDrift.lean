/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Drift
import Tri.RelaxedOdds

/-!
# Geometric safety drift for unequal reaction rates

The exact rate-weighted inequality `β · down ≤ up` yields conservation of the
geometric potential `β⁻ˡᵉᵛᵉˡ`.  This is the one-step input needed by the
existing finite-horizon Feller engine.
-/

namespace Tri

open scoped ENNReal

/-- The relaxed step is supported on the three neighboring `X` counts. -/
theorem relaxedTriStep_eq_zero
    (r : RelaxedRate) (a y : ℕ) (h : 3 ≤ (a + 1) + y) {z : ℕ}
    (h0 : z ≠ a) (h1 : z ≠ a + 1) (h2 : z ≠ a + 2) :
    relaxedTriStep r (a + 1) y h z = 0 := by
  unfold relaxedTriStep
  rw [PMF.map_apply, tsum_fintype]
  rw [show (Finset.univ : Finset RelaxedTripleKind) =
    {RelaxedTripleKind.xxx, RelaxedTripleKind.xxyFire,
      RelaxedTripleKind.xxyIdle, RelaxedTripleKind.xyyFire,
      RelaxedTripleKind.yyy} from rfl]
  simp [RelaxedTripleKind.nextX, h0, h1, h2]

/-- Expectation under one relaxed step reduces to its three reachable atoms. -/
theorem expect_relaxedTriStep
    (r : RelaxedRate) (a y : ℕ) (h : 3 ≤ (a + 1) + y)
    (V : ℕ → ℝ≥0∞) :
    expect (relaxedTriStep r (a + 1) y h) V =
      relaxedTriStep r (a + 1) y h a * V a +
      relaxedTriStep r (a + 1) y h (a + 1) * V (a + 1) +
      relaxedTriStep r (a + 1) y h (a + 2) * V (a + 2) := by
  unfold expect
  rw [tsum_eq_sum (s := ({a, a + 1, a + 2} : Finset ℕ)) ?_]
  · rw [Finset.sum_insert (by simp), Finset.sum_insert (by simp),
      Finset.sum_singleton]
    ring
  · intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hz
    rw [relaxedTriStep_eq_zero r a y h hz.1 hz.2.1 hz.2.2, zero_mul]

/-- The down, stay, and up masses of one relaxed step sum to one. -/
theorem relaxedTriStep_masses_sum
    (r : RelaxedRate) (a y : ℕ) (h : 3 ≤ (a + 1) + y) :
    relaxedTriStep r (a + 1) y h a +
      relaxedTriStep r (a + 1) y h (a + 1) +
      relaxedTriStep r (a + 1) y h (a + 2) = 1 := by
  have hsum := expect_relaxedTriStep r a y h (fun _ => 1)
  simpa [expect, PMF.tsum_coe] using hsum.symm

/-- A three-atom drift inequality conserves the geometric potential. -/
theorem relaxedTriStep_geometric_conserve
    (r : RelaxedRate) (a y : ℕ) (h : 3 ≤ (a + 1) + y)
    {u : ℝ≥0∞} (hu1 : u ≤ 1)
    (hdrift :
      relaxedTriStep r (a + 1) y h a ≤
        relaxedTriStep r (a + 1) y h (a + 2) * u) :
    expect (relaxedTriStep r (a + 1) y h) (fun k => u ^ k) ≤
      u ^ (a + 1) := by
  rw [expect_relaxedTriStep]
  have hkey :=
    three_term_drift_ennreal (relaxedTriStep_masses_sum r a y h) hu1 hdrift
  calc
    relaxedTriStep r (a + 1) y h a * u ^ a +
          relaxedTriStep r (a + 1) y h (a + 1) * u ^ (a + 1) +
          relaxedTriStep r (a + 1) y h (a + 2) * u ^ (a + 2)
        = u ^ a *
            (relaxedTriStep r (a + 1) y h a +
              relaxedTriStep r (a + 1) y h (a + 1) * u +
              relaxedTriStep r (a + 1) y h (a + 2) * u ^ 2) := by ring
    _ ≤ u ^ a * u := mul_le_mul_right hkey _
    _ = u ^ (a + 1) := by ring

/-- The rate-weighted bias inequality conserves the potential with base
`β⁻¹`. -/
theorem relaxedTriStep_conserve_of_bias
    (r : RelaxedRate) (β : NNReal) (a b : ℕ)
    (h : 3 ≤ (a + 1) + (b + 1))
    (hβ1 : 1 ≤ β) (hfireβ : r.fire ≤ β)
    (hbias :
      β * (b + 1 : NNReal) ≤ r.fire * (a + 1 : NNReal)) :
    expect (relaxedTriStep r (a + 1) (b + 1) h)
        (fun k => (β : ℝ≥0∞)⁻¹ ^ k) ≤
      (β : ℝ≥0∞)⁻¹ ^ (a + 1) := by
  apply relaxedTriStep_geometric_conserve
  · exact ENNReal.inv_le_one.mpr (by exact_mod_cast hβ1)
  · have hm := relaxedTriStep_mass_bias r h hfireβ hbias
    have hβ0 : (β : ℝ≥0∞) ≠ 0 := by
      simp only [ne_eq, ENNReal.coe_eq_zero]
      exact ne_of_gt (lt_of_lt_of_le zero_lt_one hβ1)
    have hβtop : (β : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
    rw [← div_eq_mul_inv,
      ENNReal.le_div_iff_mul_le (Or.inl hβ0) (Or.inl hβtop)]
    simpa only [mul_comm] using hm

/-- A corner bias inequality controls every state in the corresponding
rectangular region. -/
theorem relaxed_bias_on_region
    (r : RelaxedRate) (β : NNReal) {a b aLo bHi : ℕ}
    (hLo : aLo ≤ a) (hHi : b ≤ bHi)
    (hcorner :
      β * (bHi + 1 : NNReal) ≤ r.fire * (aLo + 1 : NNReal)) :
    β * (b + 1 : NNReal) ≤ r.fire * (a + 1 : NNReal) := by
  calc
    β * (b + 1 : NNReal) ≤ β * (bHi + 1 : NNReal) := by
      gcongr
    _ ≤ r.fire * (aLo + 1 : NNReal) := hcorner
    _ ≤ r.fire * (a + 1 : NNReal) := by
      gcongr

/-- Uniform geometric conservation throughout a rectangular majority region. -/
theorem relaxedTriStep_conserve_on_region
    (r : RelaxedRate) (β : NNReal) (a b aLo bHi : ℕ)
    (h : 3 ≤ (a + 1) + (b + 1))
    (hLo : aLo ≤ a) (hHi : b ≤ bHi)
    (hβ1 : 1 ≤ β) (hfireβ : r.fire ≤ β)
    (hcorner :
      β * (bHi + 1 : NNReal) ≤ r.fire * (aLo + 1 : NNReal)) :
    expect (relaxedTriStep r (a + 1) (b + 1) h)
        (fun k => (β : ℝ≥0∞)⁻¹ ^ k) ≤
      (β : ℝ≥0∞)⁻¹ ^ (a + 1) :=
  relaxedTriStep_conserve_of_bias r β a b h hβ1 hfireβ
    (relaxed_bias_on_region r β hLo hHi hcorner)

end Tri

#print axioms Tri.relaxedTriStep_eq_zero
#print axioms Tri.relaxedTriStep_geometric_conserve
#print axioms Tri.relaxedTriStep_conserve_of_bias
#print axioms Tri.relaxedTriStep_conserve_on_region
