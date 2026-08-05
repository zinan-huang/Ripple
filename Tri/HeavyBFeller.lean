/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.HeavyBResolution
import Tri.Freeze

/-!
# Heavy-B safety: the Feller ruin bound

Assembling the one-step conservation `heavyState_conserve_on_region` through
`freeze_conserve` and `feller_ruin_u` gives the Heavy-B ruin estimate: from
heavy level `aLo + k` the probability that the level ever returns to `aLo`
is at most `(bHi/aLo)^k`.  This is the paper's Lemma-1 safety bound at
effective population `n`.

## Differences from Double-B

The scale is `n` instead of `2n`: `heavyLevel + (y+b) = n` where
`doubleLevel + doubleCoLevel = 2n`. The structure is otherwise identical.
-/

namespace Tri

open scoped ENNReal

/-- **Heavy-B ruin bound.**  Over any horizon, starting from heavy level
`aLo + k`, the level drops back to `aLo` with probability at most
`(bHi/aLo)^k`. -/
theorem heavyB_ruin {n : ℕ} (aLo bHi k : ℕ) (hn : 3 ≤ n)
    (hpop : aLo + bHi + 2 = n)
    (haLo : 0 < aLo) (hbHi : 0 < bHi) (hmaj : bHi ≤ aLo) (s₀ : HeavyState n)
    (hstart : BiCfg.heavyLevel s₀.1 = aLo + k) :
    ⨆ T : ℕ, hitProb (fun z : HeavyState n => BiCfg.heavyLevel z.1 ≤ aLo)
        (heavyStateStep n) T s₀
      ≤ ((bHi : ℝ≥0∞) / (aLo : ℝ≥0∞)) ^ k := by
  have haLone : (aLo : ℝ≥0∞) ≠ 0 := by simp only [ne_eq, Nat.cast_eq_zero]; omega
  have haLotop : (aLo : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hbHine : (bHi : ℝ≥0∞) ≠ 0 := by simp only [ne_eq, Nat.cast_eq_zero]; omega
  have hu1 : (bHi : ℝ≥0∞) / (aLo : ℝ≥0∞) ≤ 1 := by
    calc (bHi : ℝ≥0∞) / (aLo : ℝ≥0∞) ≤ (aLo : ℝ≥0∞) / (aLo : ℝ≥0∞) :=
        ENNReal.div_le_div_right (by exact_mod_cast hmaj) _
      _ = 1 := ENNReal.div_self haLone haLotop
  have hu0 : (bHi : ℝ≥0∞) / (aLo : ℝ≥0∞) ≠ 0 :=
    ENNReal.div_ne_zero.mpr ⟨hbHine, haLotop⟩
  refine feller_ruin_u (K := heavyStateStep n)
    (fun z => BiCfg.heavyLevel z.1) aLo k
    ((bHi : ℝ≥0∞) / (aLo : ℝ≥0∞)) hu1 hu0
    (fun z => ((bHi : ℝ≥0∞) / (aLo : ℝ≥0∞)) ^ BiCfg.heavyLevel z.1)
    (fun _ => rfl) (freeze_conserve ?_) s₀ hstart
  intro z hz
  simp only [not_le] at hz
  have hzco : z.1.y + z.1.b ≤ bHi + 1 := by
    have := BiCfg.heavyLevel_add_coLevel z.2; omega
  exact heavyState_conserve_on_region aLo bHi hn haLo hmaj z hz hzco

end Tri

#print axioms Tri.heavyB_ruin
