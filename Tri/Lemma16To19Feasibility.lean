/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Mathlib

/-!
# Feasibility checks for the Lemma 16--19 parameter route

These lemmas prevent an invalid direct handoff from the decisive Lemma 18
stage to the late Lemma 19 regime.  The paper's decisive stage ends around
`2n / cStar²`, whereas the existing late-stage theorem starts only once at
least a quarter of the population is active.
-/

namespace Tri

/-- The decisive reaction-count conditions are incompatible with pretending
that its endpoint already has at least a quarter of the population active. -/
theorem criticalStage_directLate_infeasible
    (n a cStar r : ℕ)
    (hn : 0 < n)
    (hcStar : 1 ≤ cStar)
    (hquarterLate : n ≤ 8 * a)
    (hmeanActive : (2 * a) ^ 3 ≤ r * n ^ 2)
    (hreactionScale :
      1200 * cStar * r ≤ 7 * a) :
    False := by
  have ha : 0 < a := by omega
  have hnSq :
      n ^ 2 ≤ (8 * a) ^ 2 :=
    Nat.pow_le_pow_left hquarterLate 2
  have hmeanScaled :=
    Nat.mul_le_mul_left
      (1200 * cStar) hmeanActive
  have hreactionScaled :=
    Nat.mul_le_mul_right
      (n ^ 2) hreactionScale
  have hmeanScaled' :
      1200 * cStar * (2 * a) ^ 3 ≤
        (1200 * cStar * r) * n ^ 2 := by
    simpa only [Nat.mul_assoc] using hmeanScaled
  have hcombined :
      1200 * cStar * (2 * a) ^ 3 ≤
        7 * a * n ^ 2 :=
    hmeanScaled'.trans hreactionScaled
  have hpopulationScaled :
      7 * a * n ^ 2 ≤
        7 * a * (8 * a) ^ 2 :=
    Nat.mul_le_mul_left (7 * a) hnSq
  have hbound :=
    hcombined.trans hpopulationScaled
  ring_nf at hbound
  have hcubic :
      a ^ 3 ≤ cStar * a ^ 3 := by
    simpa using
      Nat.mul_le_mul_right (a ^ 3) hcStar
  have haCubic : 0 < a ^ 3 := by
    positivity
  omega

end Tri

#print axioms Tri.criticalStage_directLate_infeasible
