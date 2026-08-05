/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Theorem6InitialRadius
import Tri.Lemma17FixedPrefixFacts

/-!
# Theorem 6 fixed-prefix parameters

The explicit initial scale and radius are assembled with the fixed Lemma 17
families.  Only radius bias room and integral reaction feasibility remain.
-/

namespace Tri

noncomputable section

/-- Assemble the concrete Theorem 6 initial scale and radius with the complete
fixed Lemma 17 prefix certificate. -/
theorem theorem6FixedPrefixFacts
    (n γ cStar : ℕ)
    (hN : 0 < theorem6Q n γ * n)
    (hcStar : 0 < cStar)
    (S : Theorem6InitialScaleFacts n γ)
    (hqLarge : 8192 ≤ theorem6Q n γ)
    (hbias :
      38 * cStar *
          theorem6InitialRadius
            (theorem6Q n γ)
            (theorem6InitialScale n γ) ≤
        theorem6InitialScale n γ)
    (hfit :
      ∀ j ≤ lemma17FixedStageCount n
          (theorem6InitialScale n γ) S.hpositive,
        76 * cStar *
            lemma17FixedReactionLower n
              (theorem6Q n γ) cStar
              (lemma17FixedScale
                (theorem6InitialScale n γ) j) ≤
          lemma17FixedScale
            (theorem6InitialScale n γ) j) :
    Lemma17FixedPrefixFacts
      n (theorem6Q n γ) cStar
      (theorem6InitialScale n γ)
      (theorem6InitialRadius
        (theorem6Q n γ)
        (theorem6InitialScale n γ))
      (Nat.pos_of_mul_pos_left hN)
      hcStar S.hpositive :=
  lemma17FixedPrefixFacts
    n (theorem6Q n γ) cStar
    (theorem6InitialScale n γ)
    (theorem6InitialRadius
      (theorem6Q n γ)
      (theorem6InitialScale n γ))
    (Nat.pos_of_mul_pos_left hN)
    hcStar S.hfour S.hbelow S.hq
    (by
      unfold theorem6InitialRadius
      have hsqrt :
          22 ≤ Nat.sqrt
            (theorem6Q n γ *
              (theorem6InitialScale n γ + 1)) := by
        apply (Nat.le_sqrt').2
        calc
          22 ^ 2 ≤ 8192 := by norm_num
          _ ≤ theorem6Q n γ := hqLarge
          _ ≤ theorem6Q n γ *
                (theorem6InitialScale n γ + 1) := by
            have hfactor :
                1 ≤ theorem6InitialScale n γ + 1 := by
              omega
            simpa using
              Nat.mul_le_mul_left
                (theorem6Q n γ) hfactor
      omega)
    hbias
    (theorem6InitialRadius_sq
      (theorem6Q n γ)
      (theorem6InitialScale n γ))
    hfit

end

end Tri

#print axioms Tri.theorem6FixedPrefixFacts
