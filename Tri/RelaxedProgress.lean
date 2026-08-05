/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.RelaxedProductivity
import Tri.RelaxedDirectionParams
import Tri.DoubleBDirection

/-!
# Strict productive-event progress for unequal rates

This file couples the signed `X` level to the productive-event counter.  The
joint potential `w^x * eta^c` is a supermartingale when the live region has a
uniform productive up/down odds bound.
-/

namespace Tri

open scoped ENNReal

/-- A state-specific lower bound on `x*y` gives a stage-sensitive relaxed
productive-mass floor. -/
theorem relaxed_productive_mass_ge
    (r : RelaxedRate) (a b n K : ℕ)
    (h3 : 3 ≤ n) (hpop : a + b + 2 = n)
    (hK : K ≤ (a + 1) * (b + 1)) :
    (r.fire : ℝ≥0∞) *
        (((3 * K : ℕ) : ℝ≥0∞) /
          ((n * (a + b + 1) : ℕ) : ℝ≥0∞)) ≤
      relaxedTriStep r (a + 1) (b + 1) (by omega) a +
        relaxedTriStep r (a + 1) (b + 1) (by omega) (a + 2) := by
  calc
    (r.fire : ℝ≥0∞) *
          (((3 * K : ℕ) : ℝ≥0∞) /
            ((n * (a + b + 1) : ℕ) : ℝ≥0∞))
        ≤ (r.fire : ℝ≥0∞) *
            (triStep (a + 1) (b + 1) (by omega) a +
              triStep (a + 1) (b + 1) (by omega) (a + 2)) :=
      (by
        simpa [mul_comm] using
          mul_le_mul_right
            (productive_mass_ge a b n K h3 hpop hK)
            (r.fire : ℝ≥0∞))
    _ ≤ relaxedTriStep r (a + 1) (b + 1) (by omega) a +
          relaxedTriStep r (a + 1) (b + 1) (by omega) (a + 2) :=
      relaxed_productive_mass_ge_fire_mul r a b (by omega)

/-- Exact one-step expansion of the counted relaxed chain against a joint
level/counter test function. -/
theorem relaxedCount_expect_level_count
    (r : RelaxedRate) (n a b c : ℕ)
    (hpop : a + b + 2 = n) (h3 : 3 ≤ n)
    (G : ℕ → ℕ → ℝ≥0∞) :
    expect (relaxedCount r n (a + 1, c))
        (fun z => G z.1 z.2) =
      relaxedTriStep r (a + 1) (b + 1) (by omega) a *
          G a (c + 1) +
        relaxedTriStep r (a + 1) (b + 1) (by omega) (a + 1) *
          G (a + 1) c +
        relaxedTriStep r (a + 1) (b + 1) (by omega) (a + 2) *
          G (a + 2) (c + 1) := by
  unfold relaxedCount
  rw [expect_map, relaxedTriChain_apply r hpop h3,
    expect_relaxedTriStep]
  simp

/-- Event-indexed direction potential for the relaxed chain. -/
noncomputable def relaxedTheta
    (w eta : ℝ≥0∞) (q : ℕ × ℕ) : ℝ≥0∞ :=
  w ^ q.1 * eta ^ q.2

/-- A uniform productive bias makes the joint level/count potential a
one-step supermartingale. -/
theorem relaxedCount_theta_super
    (r : RelaxedRate) (beta : NNReal)
    (n a b c : ℕ)
    (hpop : a + b + 2 = n) (h3 : 3 ≤ n)
    (w eta : ℝ≥0∞)
    (hbeta1 : 1 ≤ beta) (hfirebeta : r.fire ≤ beta)
    (hbias :
      beta * (b + 1 : NNReal) ≤ r.fire * (a + 1 : NNReal))
    (hrel :
      eta * ((beta : ℝ≥0∞)⁻¹ + w ^ 2) =
        w * ((beta : ℝ≥0∞)⁻¹ + 1))
    (hweta : w ≤ eta) (hwt : w ≠ ⊤) (hetat : eta ≠ ⊤) :
    expect (relaxedCount r n (a + 1, c)) (relaxedTheta w eta) ≤
      relaxedTheta w eta (a + 1, c) := by
  let dn : ℝ≥0∞ :=
    relaxedTriStep r (a + 1) (b + 1) (by omega) a
  let neu : ℝ≥0∞ :=
    relaxedTriStep r (a + 1) (b + 1) (by omega) (a + 1)
  let up : ℝ≥0∞ :=
    relaxedTriStep r (a + 1) (b + 1) (by omega) (a + 2)
  have hsum : dn + neu + up = 1 := by
    dsimp only [dn, neu, up]
    exact relaxedTriStep_masses_sum r a (b + 1) (by omega)
  have hmass : (beta : ℝ≥0∞) * dn ≤ up := by
    dsimp only [dn, up]
    exact relaxedTriStep_mass_bias r (by omega) hfirebeta hbias
  have hbeta0 : (beta : ℝ≥0∞) ≠ 0 := by
    simp only [ne_eq, ENNReal.coe_eq_zero]
    exact ne_of_gt (lt_of_lt_of_le zero_lt_one hbeta1)
  have hbetatop : (beta : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  have hdle : dn ≤ up * (beta : ℝ≥0∞)⁻¹ := by
    rw [← div_eq_mul_inv]
    apply (ENNReal.le_div_iff_mul_le
      (Or.inl hbeta0) (Or.inl hbetatop)).2
    simpa only [mul_comm] using hmass
  have hdt : dn ≠ ⊤ := by
    dsimp only [dn]
    exact PMF.apply_ne_top _ _
  have hnt : neu ≠ ⊤ := by
    dsimp only [neu]
    exact PMF.apply_ne_top _ _
  have hut : up ≠ ⊤ := by
    dsimp only [up]
    exact PMF.apply_ne_top _ _
  have hutop : (beta : ℝ≥0∞)⁻¹ ≠ ⊤ :=
    ENNReal.inv_ne_top.mpr hbeta0
  have hscalar :
      neu * w + eta * (dn + up * w ^ 2) ≤ w :=
    doubleDir_scalar dn neu up (beta : ℝ≥0∞)⁻¹ w eta
      hsum hdle hrel hweta hdt hnt hut hwt hetat hutop
  unfold relaxedTheta
  rw [relaxedCount_expect_level_count r n a b c hpop h3
    (fun L C => w ^ L * eta ^ C)]
  change
    dn * (w ^ a * eta ^ (c + 1)) +
        neu * (w ^ (a + 1) * eta ^ c) +
        up * (w ^ (a + 2) * eta ^ (c + 1)) ≤
      w ^ (a + 1) * eta ^ c
  calc
    dn * (w ^ a * eta ^ (c + 1)) +
          neu * (w ^ (a + 1) * eta ^ c) +
          up * (w ^ (a + 2) * eta ^ (c + 1))
        = (w ^ a * eta ^ c) *
            (neu * w + eta * (dn + up * w ^ 2)) := by
      rw [pow_succ eta c, pow_succ w a,
        show a + 2 = (a + 1) + 1 by omega,
        pow_succ w (a + 1)]
      ring
    _ ≤ (w ^ a * eta ^ c) * w :=
      (by
        simpa [mul_comm] using
          mul_le_mul_left hscalar (w ^ a * eta ^ c))
    _ = w ^ (a + 1) * eta ^ c := by
      rw [pow_succ w a]
      ring

end Tri

#print axioms Tri.relaxed_productive_mass_ge
#print axioms Tri.relaxedCount_expect_level_count
#print axioms Tri.relaxedCount_theta_super
