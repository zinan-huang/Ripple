/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.DoubleBResolution
import Tri.Freeze

/-!
# Double-B safety: the Feller ruin bound (Theorem 2)

Assembling the one-step conservation `doubleState_conserve_on_region` through
`freeze_conserve` and `feller_ruin_u` gives the Double-B safety estimate: from
effective level `aLo + k` the probability that the level *ever* returns to `aLo`
is at most `(bHi/aLo)^k`.  This is the paper's Lemma-1 safety bound at effective
population `2n`.
-/

namespace Tri

open scoped ENNReal

/-- **Double-B ruin bound.**  Over any horizon, starting from effective level
`aLo + k`, the level drops back to `aLo` with probability at most `(bHi/aLo)^k`. -/
theorem doubleB_ruin (n aLo bHi k : ℕ) (hn : 2 ≤ n) (hpop2n : aLo + bHi + 2 = 2 * n)
    (haLo : 0 < aLo) (hbHi : 0 < bHi) (hmaj : bHi ≤ aLo) (s₀ : DoubleState n)
    (hstart : s₀.1.doubleLevel = aLo + k) :
    ⨆ T : ℕ, hitProb (fun z : DoubleState n => z.1.doubleLevel ≤ aLo) (doubleStateStep n hn) T s₀
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
  refine feller_ruin_u (K := doubleStateStep n hn) (fun z => z.1.doubleLevel) aLo k
    ((bHi : ℝ≥0∞) / (aLo : ℝ≥0∞)) hu1 hu0 (fun z => ((bHi:ℝ≥0∞)/(aLo:ℝ≥0∞)) ^ z.1.doubleLevel)
    (fun _ => rfl) (freeze_conserve ?_) s₀ hstart
  intro z hz
  simp only [not_le] at hz
  have hzco : z.1.doubleCoLevel ≤ bHi + 1 := by
    have := doubleLevel_add_doubleCoLevel z; omega
  exact doubleState_conserve_on_region n aLo bHi hn haLo hmaj z hz hzco

end Tri
