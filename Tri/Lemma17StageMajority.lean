/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Lemma17JointLabelTail

/-!
# One Lemma 17 stage from a remaining-label majority

This module discharges the two explicit inputs of the generic stage assembly:
the epidemic deadline comes from the physical marginal, and the immutable-label
term comes from the maximal-prefix urn tail.
-/

namespace Tri

open scoped ENNReal

noncomputable section

/-- One complete Lemma 17 stage when the remaining inactive population still
has at least as many immutable `X` labels as `Y` labels. -/
theorem lemma17CountedPath_stage_of_remaining_majority
    (n : ℕ) (h3 : 3 ≤ n)
    (q qpar rho aActive sampleSize k u nu R B A G D₀ M H cStar : ℕ)
    (haActive : 4 ≤ aActive)
    (hG : 2 * G ≤ aActive)
    (hA : A ≤ n)
    (s : InfectionRevealPhysicalState n)
    (hstartOne : 1 ≤ s.coarse.1.active)
    (hstartActive : aActive ≤ s.coarse.1.active)
    (hanchorActive : s.coarse.1.active + k = A)
    (hstartGap :
      s.coarse.1.ay ≤ s.coarse.1.ax + D₀)
    (hbudget : D₀ + (rho + 1) + 2 * M ≤ G)
    (hH : 0 < H)
    (hdrift : 4 * G * H ≤ aActive * M)
    (hlog : Nat.log 2 n ≤ q)
    (hquarterTarget : 4 * A ≤ n)
    (hcStar : 640 ≤ cStar)
    (hqa : qpar * sampleSize ≤ rho ^ 2)
    (hnu : nu + 1 = n)
    (hk : k + 1 = sampleSize)
    (huk : u + k + 1 = nu)
    (hRB : R + B = nu)
    (hquarterSample : 4 * sampleSize ≤ n)
    (hmajor : R ≤ B)
    (hx0 : s.inactive.xIds.card = B)
    (hy0 : s.inactive.yIds.card = R)
    (hk0 : 0 < k)
    (w : ℝ≥0∞) (hw1 : 1 ≤ w) (hwt : w ≠ ⊤) :
    terminalFailureMass
        (iter (lemma17CountedPathStep n h3 k A G)
          (cStar * q * n)
          (lemma17CountedPathInitial s))
        (Lemma17StageGood A G)
      ≤
    lemma16EpidemicError q + lemma16UrnError qpar +
      (infectionAllActiveCubeCompl n A +
          infectionAllActiveCube n A * w) ^ (cStar * q * n) /
        w ^ (H + 1) +
      ENNReal.ofReal
        (Real.exp
          (-((M : ℝ) ^ 2 / (8 * (H : ℝ))))) := by
  apply
    lemma17CountedPath_stage
      n h3 aActive k A G D₀ (rho + 1) M H
      (cStar * q * n)
      haActive hG hA s hstartActive hanchorActive
      hstartGap hbudget hH hdrift
      w hw1 hwt
      (lemma16EpidemicError q)
      (lemma16UrnError qpar)
  · exact
      lemma17CountedPath_epidemic_deadline
        n q A k G cStar h3 hlog hquarterTarget
        hcStar s hstartOne hanchorActive
  · exact
      lemma17CountedPath_label_tail
        n h3 qpar rho sampleSize k u nu R B
        A G (cStar * q * n) s hanchorActive
        hqa hnu hk huk hRB hquarterSample hmajor
        hx0 hy0 hk0

end

end Tri

#print axioms Tri.lemma17CountedPath_stage_of_remaining_majority
