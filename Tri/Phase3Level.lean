/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Phase3Productive

/-!
# The phase-3 Feller level

`feller_ruin_u` consumes a hit set of the shape `level z ≤ m`.  The phase-3
escape event is `2 y > 3 d` *together with* the non-physical states `n < x`
(which must be stopped, since the productive chain self-loops there and no
potential can contract).  Taking

```text
phase3Level n z = if n < z then 0 else z
```

puts the non-physical states at the bottom of the band, so the whole escape
event becomes `phase3Level n z ≤ phase3EscapeBound n γ` — with no reachability
argument needed anywhere.
-/

namespace Tri

open scoped ENNReal

/-- The Feller level for phase 3: the `X`-count, with the (unreachable)
non-physical states pushed to the bottom of the band.  This is what makes the
whole `Phase3Stop` escape set — including its `n < x` disjunct — have the
`level z ≤ m` shape that `feller_ruin_u` consumes, with no reachability
argument needed. -/
def phase3Level (n z : ℕ) : ℕ := if n < z then 0 else z

/-- The `level ≤ m` event is exactly the phase-3 escape event. -/
theorem phase3Level_le_iff (n γ z : ℕ) (h3 : 3 ≤ n)
    (hsize : 6 * phase3Scale n γ ≤ n) :
    phase3Level n z ≤ phase3EscapeBound n γ ↔
      (2 * z + 3 * phase3Scale n γ < 2 * n ∨ n < z) := by
  unfold phase3Level
  by_cases hz : n < z
  · simp only [if_pos hz]
    constructor
    · intro _; exact Or.inr hz
    · intro _; exact Nat.zero_le _
  · simp only [if_neg hz]
    rw [phase3_escape_iff n γ z h3 hsize]
    constructor
    · exact Or.inl
    · rintro (h | h)
      · exact h
      · omega

/-- **The phase-3 Feller supermartingale**, on the level that absorbs the
non-physical states. -/
theorem phase3_feller_hfroz_level
    (n γ : ℕ) (h3 : 3 ≤ n) (hsize : 6 * phase3Scale n γ ≤ n) (x : ℕ) :
    expect
        (freeze (fun z => phase3Level n z ≤ phase3EscapeBound n γ)
          (productiveTriChain n) x)
        (fun z => ((1 : ℝ≥0∞) / 3) ^ phase3Level n z)
      ≤ ((1 : ℝ≥0∞) / 3) ^ phase3Level n x := by
  classical
  by_cases hesc : phase3Level n x ≤ phase3EscapeBound n γ
  · simp [freeze, hesc]
  · rw [show freeze (fun z => phase3Level n z ≤ phase3EscapeBound n γ)
          (productiveTriChain n) x = productiveTriChain n x by
      simp [freeze, hesc]]
    have hxn : ¬ n < x := by
      intro h
      exact hesc (by simp [phase3Level, h])
    have hguard : ¬ (2 * x + 3 * phase3Scale n γ < 2 * n) := by
      intro h
      exact hesc ((phase3Level_le_iff n γ x h3 hsize).2 (Or.inl h))
    have hlvlx : phase3Level n x = x := by simp [phase3Level, hxn]
    by_cases hxeqn : x = n
    · subst hxeqn
      rw [show productiveTriChain x x = PMF.pure x by
        unfold productiveTriChain
        rw [dif_neg (by omega)]]
      simp
    · have hstop : ¬ Phase3Stop n γ x := by
        unfold Phase3Stop
        push Not
        exact ⟨hxeqn, by omega, by omega⟩
      obtain ⟨a, b, hx, hpop, hprod, hguard'⟩ :=
        phase3_live_interior h3 hsize hstop
      subst hx
      rw [productiveTriChain_apply hpop hprod, expect_productiveTriInterior]
      have hla : phase3Level n a = a := by
        simp [phase3Level, show ¬ n < a by omega]
      have hla2 : phase3Level n (a + 2) = a + 2 := by
        simp [phase3Level, show ¬ n < a + 2 by omega]
      rw [hla, hla2, hlvlx]
      have hq : (3 : ℝ≥0∞) / 4 ≤ (a : ℝ≥0∞) / ((a : ℝ≥0∞) + (b : ℝ≥0∞)) :=
        productive_down_mass_ge_three_quarters hprod hguard'
      have hsum : (a : ℝ≥0∞) / ((a : ℝ≥0∞) + (b : ℝ≥0∞))
          + (b : ℝ≥0∞) / ((a : ℝ≥0∞) + (b : ℝ≥0∞)) = 1 := by
        have := productiveTriInterior_masses a b hprod
        rw [add_comm] at this
        simpa using this
      have hscalar := phase3_feller_scalar_step hsum hq
      have hsq : ((1 : ℝ≥0∞) / 3) ^ 2 = 1 / 9 := by
        rw [← ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness),
          ENNReal.toReal_pow, ENNReal.toReal_div, ENNReal.toReal_div]
        norm_num
      rw [show ((1 : ℝ≥0∞) / 3) ^ (a + 2) = ((1 : ℝ≥0∞) / 3) ^ a * (1 / 9) by
          rw [pow_add, hsq],
        show ((1 : ℝ≥0∞) / 3) ^ (a + 1) = ((1 : ℝ≥0∞) / 3) ^ a * (1 / 3) by
          rw [pow_succ]]
      calc
        (b : ℝ≥0∞) / ((a : ℝ≥0∞) + (b : ℝ≥0∞)) * ((1 : ℝ≥0∞) / 3) ^ a
            + (a : ℝ≥0∞) / ((a : ℝ≥0∞) + (b : ℝ≥0∞))
                * (((1 : ℝ≥0∞) / 3) ^ a * (1 / 9))
            = ((b : ℝ≥0∞) / ((a : ℝ≥0∞) + (b : ℝ≥0∞))
                + (a : ℝ≥0∞) / ((a : ℝ≥0∞) + (b : ℝ≥0∞)) * (1 / 9))
              * ((1 : ℝ≥0∞) / 3) ^ a := by ring
        _ ≤ (1 / 3) * ((1 : ℝ≥0∞) / 3) ^ a := mul_le_mul_left hscalar _
        _ = ((1 : ℝ≥0∞) / 3) ^ a * (1 / 3) := by ring

end Tri

#print axioms Tri.phase3Level_le_iff
#print axioms Tri.phase3_feller_hfroz_level
