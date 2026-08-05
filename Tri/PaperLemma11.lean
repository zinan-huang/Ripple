/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.MultiProductiveLinear
import Tri.MultiGapEdge

/-!
# Paper Lemma 11: no backsliding

This file exposes the existing unbounded productive-time half-gap theorem under
the two event names used in the paper.  Both wrappers keep the event shape
already proved by `productivePairGapEver_half_failure_exp`:
`productivePairGapEverFailure h3 X (D / 2) c0`.  That event is global over all
competitors, so its existing `m` prefactor is retained verbatim.
-/

namespace Tri.Multi

open scoped ENNReal

variable {m n : ℕ}

/-- Paper Lemma 11, two-party wording.  Specializing the already-global
half-gap event to a direct pairwise backslide gives the same
`m exp(-D^2/(18n))` bound. -/
theorem lemma11_twoPartyBacksliding
    (h3 : 3 ≤ n) (X : Species m)
    (D : ℕ) (hD4 : 4 ≤ D) (hDn : D ≤ n)
    (c0 : Config m n)
    (hinit : HasPairwiseGap c0 X D) :
    productivePairGapEverFailure h3 X (D / 2) c0 ≤
      (m : ℝ≥0∞) *
        ENNReal.ofReal
          (Real.exp (-((D : ℝ) ^ 2 / (18 * (n : ℝ))))) := by
  exact productivePairGapEver_half_failure_exp h3 X D hD4 hDn c0 hinit

/-- Paper Lemma 11, third-party wording.  The existing global half-gap event
already unions over third-party routes, so this wrapper is the same event with
the paper's third-party name. -/
theorem lemma11_thirdPartyBacksliding
    (h3 : 3 ≤ n) (X : Species m)
    (D : ℕ) (hD4 : 4 ≤ D) (hDn : D ≤ n)
    (c0 : Config m n)
    (hinit : HasPairwiseGap c0 X D) :
    productivePairGapEverFailure h3 X (D / 2) c0 ≤
      (m : ℝ≥0∞) *
        ENNReal.ofReal
          (Real.exp (-((D : ℝ) ^ 2 / (18 * (n : ℝ))))) := by
  exact productivePairGapEver_half_failure_exp h3 X D hD4 hDn c0 hinit

example :
    productivePairGapEverFailure (m := 1) (n := 4) (by norm_num)
        (0 : Species 1) (4 / 2)
        (⟨fun _ => ⟨4, by norm_num⟩, by simp⟩ : Config 1 4) ≤
      (1 : ℝ≥0∞) *
        ENNReal.ofReal (Real.exp (-((4 : ℝ) ^ 2 / (18 * (4 : ℝ))))) := by
  simpa using
    lemma11_twoPartyBacksliding (m := 1) (n := 4) (by norm_num)
      (0 : Species 1) 4 (by norm_num) (by norm_num)
      (⟨fun _ => ⟨4, by norm_num⟩, by simp⟩ : Config 1 4)
      (hasPairwiseGap_of_one_species _ _ _)

example :
    productivePairGapEverFailure (m := 1) (n := 4) (by norm_num)
        (0 : Species 1) (4 / 2)
        (⟨fun _ => ⟨4, by norm_num⟩, by simp⟩ : Config 1 4) ≤
      (1 : ℝ≥0∞) *
        ENNReal.ofReal (Real.exp (-((4 : ℝ) ^ 2 / (18 * (4 : ℝ))))) := by
  simpa using
    lemma11_thirdPartyBacksliding (m := 1) (n := 4) (by norm_num)
      (0 : Species 1) 4 (by norm_num) (by norm_num)
      (⟨fun _ => ⟨4, by norm_num⟩, by simp⟩ : Config 1 4)
      (hasPairwiseGap_of_one_species _ _ _)

end Tri.Multi

#print axioms Tri.Multi.lemma11_twoPartyBacksliding
#print axioms Tri.Multi.lemma11_thirdPartyBacksliding
