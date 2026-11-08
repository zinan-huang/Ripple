/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Lemma16To19PostParameters
import Tri.Lemma17PrefixFacts

/-!
# Explicit post-critical certificate

The terminal radius is reused by the whole fixed post-critical ladder, while
four copies of it form the incoming late reserve.  Its global square bound
also pays the smaller terminal post-scale square.
-/

namespace Tri

noncomputable section

/-- The fixed prefix and one global terminal square construct the complete
seventeen-stage post-critical certificate. -/
theorem lemma16To19PostFacts_explicit
    (n γ cStar a rho R : ℕ)
    (hn : 0 < n)
    (hcStar : 2 ≤ cStar)
    (ha : 0 < a)
    (hlarge :
      theorem6CStarSq *
          (theorem6CStarSq + 6) ≤ n)
    (P : Lemma17PrefixFacts
      n (theorem6Q n γ) cStar a rho hn (by omega) ha)
    (hSq : theorem6Q n γ * n ≤ R ^ 2) :
    Lemma16To19PostFacts
      n (theorem6Q n γ) cStar (4 * R) R := by
  let m := lemma17StageCount n a ha
  have hqPred :
      theorem6Q n γ ≤
        lemma17ScaleWithLanding a m
          (theorem6CriticalScale n) m := by
    exact P.herrorQa m (by
      simp only [m]
      omega)
  have hqBase :
      theorem6Q n γ ≤
        2 * theorem6CriticalScale n :=
    lemma16To19Post_qBase
      n (theorem6Q n γ)
      (lemma17ScaleWithLanding a m
        (theorem6CriticalScale n) m)
      hqPred P.hbelow
  obtain ⟨e, W⟩ :=
    lemma19WindowFacts_of_large n hn hlarge
  have hrootFinal :
      theorem6Q n γ *
          (theorem6PostScale
            (theorem6CriticalScale n)
            theorem6PostStages + 2) ≤
        R ^ 2 := by
    calc
      theorem6Q n γ *
            (theorem6PostScale
              (theorem6CriticalScale n)
              theorem6PostStages + 2)
          ≤ theorem6Q n γ * n :=
        Nat.mul_le_mul_left (theorem6Q n γ)
          (by
            have hroom := W.hstageRoomFinal
            omega)
      _ ≤ R ^ 2 := hSq
  exact
    lemma16To19PostFacts_of_large
      n (theorem6Q n γ) cStar (4 * R) R
      hn hlarge hcStar hqBase hrootFinal

end

end Tri

#print axioms Tri.lemma16To19PostFacts_explicit
