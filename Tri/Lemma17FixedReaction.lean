/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Lemma17FixedRadius
import Tri.Lemma16To19ErrorConditions
import Mathlib.Algebra.Order.Floor.Div

/-!
# Fixed reaction parameters for the dyadic Lemma 17 prefix

At each scale we choose the least positive natural satisfying both lower
bounds used by the semantic mean estimate and the final error envelope.
Only the physical upper-scale feasibility inequality remains external.
-/

namespace Tri

noncomputable section

/-- Integral lower endpoint forced by the semantic mean estimate. -/
def lemma17FixedReactionMeanLower
    (n a : ℕ) : ℕ :=
  (2 * a) ^ 3 ⌈/⌉ n ^ 2

/-- Integral lower endpoint forced by the active-error estimate. -/
def lemma17FixedReactionActiveLower
    (q cStar : ℕ) : ℕ :=
  15 * q ⌈/⌉ (4 * cStar)

/-- Joint positive lower endpoint for a fixed source scale. -/
def lemma17FixedReactionLower
    (n q cStar a : ℕ) : ℕ :=
  max 1
    (max
      (lemma17FixedReactionMeanLower n a)
      (lemma17FixedReactionActiveLower q cStar))

/-- The joint lower endpoint satisfies every lower constraint used in the
least-reaction definition. -/
theorem lemma17FixedReactionLower_spec
    (n q cStar a : ℕ)
    (hn : 0 < n)
    (hcStar : 0 < cStar) :
    0 < lemma17FixedReactionLower n q cStar a ∧
    (2 * a) ^ 3 ≤
      lemma17FixedReactionLower n q cStar a * n ^ 2 ∧
    15 * q ≤
      4 * cStar *
        lemma17FixedReactionLower n q cStar a := by
  have hnSq : 0 < n ^ 2 :=
    Nat.pow_pos hn
  have hcFour : 0 < 4 * cStar := by
    positivity
  have hmeanLower :
      lemma17FixedReactionMeanLower n a ≤
        lemma17FixedReactionLower n q cStar a := by
    unfold lemma17FixedReactionLower
    exact
      (Nat.le_max_left _ _).trans
        (Nat.le_max_right _ _)
  have hactiveLower :
      lemma17FixedReactionActiveLower q cStar ≤
        lemma17FixedReactionLower n q cStar a := by
    unfold lemma17FixedReactionLower
    exact
      (Nat.le_max_right _ _).trans
        (Nat.le_max_right _ _)
  refine ⟨by
    unfold lemma17FixedReactionLower
    omega, ?_, ?_⟩
  · have h :=
      (ceilDiv_le_iff_le_mul hnSq).1
        hmeanLower
    simpa [lemma17FixedReactionMeanLower,
      mul_comm] using h
  · have h :=
      (ceilDiv_le_iff_le_mul hcFour).1
        hactiveLower
    simpa [lemma17FixedReactionActiveLower] using h

/-- A reaction parameter satisfying both lower bounds always exists when the
population and the reaction multiplier are positive. -/
theorem lemma17FixedReaction_exists
    (n q cStar a : ℕ)
    (hn : 0 < n)
    (hcStar : 0 < cStar) :
    ∃ r,
      0 < r ∧
      (2 * a) ^ 3 ≤ r * n ^ 2 ∧
      15 * q ≤ 4 * cStar * r := by
  let r := (2 * a) ^ 3 + 15 * q + 1
  have hnSq : 1 ≤ n ^ 2 := by
    exact Nat.one_le_pow 2 n hn
  have hc : 1 ≤ 4 * cStar := by omega
  refine ⟨r, by dsimp [r]; omega, ?_, ?_⟩
  · calc
      (2 * a) ^ 3 ≤ r := by
        dsimp [r]
        omega
      _ ≤ r * n ^ 2 := by
        simpa using Nat.mul_le_mul_left r hnSq
  · calc
      15 * q ≤ r := by
        dsimp [r]
        omega
      _ ≤ 4 * cStar * r := by
        simpa [mul_comm] using
          Nat.mul_le_mul_right r hc

/-- Least positive reaction parameter satisfying the two lower bounds. -/
noncomputable def lemma17FixedReaction
    (n q cStar a : ℕ)
    (hn : 0 < n)
    (hcStar : 0 < cStar) : ℕ :=
  Nat.find
    (lemma17FixedReaction_exists
      n q cStar a hn hcStar)

theorem lemma17FixedReaction_spec
    (n q cStar a : ℕ)
    (hn : 0 < n)
    (hcStar : 0 < cStar) :
    0 < lemma17FixedReaction n q cStar a hn hcStar ∧
    (2 * a) ^ 3 ≤
      lemma17FixedReaction n q cStar a hn hcStar *
        n ^ 2 ∧
    15 * q ≤
      4 * cStar *
        lemma17FixedReaction n q cStar a hn hcStar :=
  Nat.find_spec
    (lemma17FixedReaction_exists
      n q cStar a hn hcStar)

/-- The least reaction choice lies below its explicit joint lower endpoint. -/
theorem lemma17FixedReaction_le_lower
    (n q cStar a : ℕ)
    (hn : 0 < n)
    (hcStar : 0 < cStar) :
      lemma17FixedReaction n q cStar a hn hcStar ≤
        lemma17FixedReactionLower n q cStar a := by
  apply Nat.find_min'
    (lemma17FixedReaction_exists
      n q cStar a hn hcStar)
  exact
    lemma17FixedReactionLower_spec
      n q cStar a hn hcStar

/-- Exact interval feasibility for the least reaction choice: it is enough
that its explicit joint lower endpoint fits below the physical scale cap. -/
theorem lemma17FixedReaction_upper
    (n q cStar a : ℕ)
    (hn : 0 < n)
    (hcStar : 0 < cStar)
    (hfit :
      76 * cStar *
          lemma17FixedReactionLower n q cStar a ≤
        a) :
    76 * cStar *
        lemma17FixedReaction n q cStar a hn hcStar ≤
      a := by
  exact
    (Nat.mul_le_mul_left (76 * cStar)
      (lemma17FixedReaction_le_lower
        n q cStar a hn hcStar)).trans
      hfit

/-- Reaction parameters along the fixed dyadic scale. -/
noncomputable def lemma17FixedReactionFamily
    (n q cStar a : ℕ)
    (hn : 0 < n)
    (hcStar : 0 < cStar)
    (j : ℕ) : ℕ :=
  lemma17FixedReaction n q cStar
    (lemma17FixedScale a j) hn hcStar

/-- All semantic and error-envelope reaction facts through the custom source
slot. -/
structure Lemma17FixedReactionFacts
    (n q cStar a rho m : ℕ)
    (hn : 0 < n)
    (hcStar : 0 < cStar) : Prop where
  hpositive :
    ∀ j ≤ m,
      0 <
        lemma17FixedReactionFamily
          n q cStar a hn hcStar j
  hqscale :
    ∀ j ≤ m, q ≤ lemma17FixedScale a j
  hupper :
    ∀ j ≤ m,
      76 * cStar *
          lemma17FixedReactionFamily
            n q cStar a hn hcStar j ≤
        lemma17FixedScale a j
  hmean :
    ∀ j ≤ m,
      (2 * lemma17FixedScale a j) ^ 3 ≤
        lemma17FixedReactionFamily
            n q cStar a hn hcStar j *
          n ^ 2
  hactive :
    ∀ j ≤ m,
      15 * q ≤
        4 * cStar *
          lemma17FixedReactionFamily
            n q cStar a hn hcStar j
  hdirection :
    ∀ j ≤ m,
      3 * q *
          lemma17FixedReactionFamily
            n q cStar a hn hcStar j ≤
        4 * cStar * (lemma17FixedRho rho j) ^ 2

/-- The fixed lower-bound choice and the radius certificate reduce the whole
reaction family to its physical upper-scale feasibility condition. -/
theorem lemma17FixedReactionFacts
    (n q cStar a rho m : ℕ)
    (hn : 0 < n)
    (hcStar : 0 < cStar)
    (hq0 : q ≤ a)
    (hrho : 1 ≤ rho)
    (hroot :
      q * (a + 1) ≤ rho ^ 2)
    (hupper :
      ∀ j ≤ m,
        76 * cStar *
            lemma17FixedReactionFamily
              n q cStar a hn hcStar j ≤
          lemma17FixedScale a j) :
    Lemma17FixedReactionFacts
      n q cStar a rho m hn hcStar := by
  refine
    { hpositive := ?_
      hqscale := ?_
      hupper := hupper
      hmean := ?_
      hactive := ?_
      hdirection := ?_ }
  · intro j hj
    exact
      (lemma17FixedReaction_spec
        n q cStar (lemma17FixedScale a j)
        hn hcStar).1
  · intro j hj
    exact hq0.trans
      (by
        simpa [lemma17FixedScale_zero] using
          lemma17FixedScale_mono a 0 j
            (Nat.zero_le j))
  · intro j hj
    exact
      (lemma17FixedReaction_spec
        n q cStar (lemma17FixedScale a j)
        hn hcStar).2.1
  · intro j hj
    exact
      (lemma17FixedReaction_spec
        n q cStar (lemma17FixedScale a j)
        hn hcStar).2.2
  · intro j hj
    exact lemma17_error_direction_of_stage
      q (lemma17FixedScale a j) cStar
      (lemma17FixedRho rho j)
      (lemma17FixedReactionFamily
        n q cStar a hn hcStar j)
      (by omega)
      (hupper j hj)
      (lemma17FixedRho_sq q a rho j hrho hroot)

/-- The explicit pointwise interval-fit condition supplies the sole physical
upper bound left by `lemma17FixedReactionFacts`. -/
theorem lemma17FixedReactionFacts_of_fit
    (n q cStar a rho m : ℕ)
    (hn : 0 < n)
    (hcStar : 0 < cStar)
    (hq0 : q ≤ a)
    (hrho : 1 ≤ rho)
    (hroot :
      q * (a + 1) ≤ rho ^ 2)
    (hfit :
      ∀ j ≤ m,
        76 * cStar *
            lemma17FixedReactionLower n q cStar
              (lemma17FixedScale a j) ≤
          lemma17FixedScale a j) :
    Lemma17FixedReactionFacts
      n q cStar a rho m hn hcStar :=
  lemma17FixedReactionFacts
    n q cStar a rho m hn hcStar hq0 hrho hroot
    (fun j hj =>
      lemma17FixedReaction_upper
        n q cStar (lemma17FixedScale a j)
        hn hcStar (hfit j hj))

end

end Tri

#print axioms Tri.lemma17FixedReaction_exists
#print axioms Tri.lemma17FixedReaction_spec
#print axioms Tri.lemma17FixedReactionLower_spec
#print axioms Tri.lemma17FixedReaction_le_lower
#print axioms Tri.lemma17FixedReaction_upper
#print axioms Tri.lemma17FixedReactionFacts
#print axioms Tri.lemma17FixedReactionFacts_of_fit
