/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Lemma17FixedLanding
import Tri.Theorem6Parameters

/-!
# The last dyadic scale below the fixed landing

The ordinary Lemma 17 prefix stops at the least dyadic index whose next
doubling covers the fixed critical scale.  Minimality supplies the strict
lower bracket without natural-number subtraction in any statement.
-/

namespace Tri

noncomputable section

/-- The dyadic Lemma 17 scale starting at `a`. -/
def lemma17FixedScale (a j : ℕ) : ℕ :=
  2 ^ j * a

@[simp] theorem lemma17FixedScale_zero
    (a : ℕ) :
    lemma17FixedScale a 0 = a := by
  simp [lemma17FixedScale]

@[simp] theorem lemma17FixedScale_succ
    (a j : ℕ) :
    lemma17FixedScale a (j + 1) =
      2 * lemma17FixedScale a j := by
  simp [lemma17FixedScale, pow_succ]
  ring

/-- Some dyadic successor covers every positive target. -/
theorem lemma17FixedStageCount_exists
    (n a : ℕ)
    (ha : 0 < a) :
    ∃ m,
      n ≤ theorem6FixedCStarSq *
        (2 * lemma17FixedScale a m) := by
  refine ⟨n, ?_⟩
  have hnPow : n ≤ 2 ^ n :=
    n.lt_two_pow_self.le
  have hfactor :
      1 ≤ 2 * theorem6FixedCStarSq * a := by
    have hc : 0 < theorem6FixedCStarSq := by
      norm_num [theorem6FixedCStarSq,
        theorem6FixedCStar]
    have hpos :
        0 < 2 * theorem6FixedCStarSq * a :=
      Nat.mul_pos (Nat.mul_pos (by omega) hc) ha
    omega
  have hscaled :
      2 ^ n ≤
        2 ^ n * (2 * theorem6FixedCStarSq * a) := by
    simpa using Nat.mul_le_mul_left (2 ^ n) hfactor
  calc
    n ≤ 2 ^ n := hnPow
    _ ≤ 2 ^ n * (2 * theorem6FixedCStarSq * a) :=
      hscaled
    _ =
        theorem6FixedCStarSq *
          (2 * lemma17FixedScale a n) := by
      unfold lemma17FixedScale
      ring

/-- Least dyadic index whose successor covers the fixed critical scale. -/
noncomputable def lemma17FixedStageCount
    (n a : ℕ) (ha : 0 < a) : ℕ :=
  Nat.find (lemma17FixedStageCount_exists n a ha)

/-- The successor of the selected dyadic scale covers `n`. -/
theorem lemma17FixedStageCount_above
    (n a : ℕ) (ha : 0 < a) :
    n ≤ theorem6FixedCStarSq *
      (2 * lemma17FixedScale a
        (lemma17FixedStageCount n a ha)) :=
  Nat.find_spec (lemma17FixedStageCount_exists n a ha)

/-- If the initial scale is still below the target, the selected dyadic scale
is also strictly below it. -/
theorem lemma17FixedStageCount_below
    (n a : ℕ) (ha : 0 < a)
    (hbase : theorem6FixedCStarSq * a < n) :
    theorem6FixedCStarSq *
        lemma17FixedScale a
          (lemma17FixedStageCount n a ha) < n := by
  let m := lemma17FixedStageCount n a ha
  by_cases hm : m = 0
  · simpa [m, hm] using hbase
  · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hm
    have hklt :
        k < lemma17FixedStageCount n a ha := by
      change k < m
      omega
    have hminimal :
        ¬ n ≤ theorem6FixedCStarSq *
          (2 * lemma17FixedScale a k) :=
      Nat.find_min
        (lemma17FixedStageCount_exists n a ha) hklt
    change theorem6FixedCStarSq *
        lemma17FixedScale a m < n
    rw [hk, lemma17FixedScale_succ]
    omega

/-- Complete fixed dyadic bracket for the ordinary Lemma 17 prefix. -/
structure Lemma17FixedScaleFacts
    (n a : ℕ) (ha : 0 < a) : Prop where
  hscale0 :
    lemma17FixedScale a 0 = a
  hdouble :
    ∀ j < lemma17FixedStageCount n a ha,
      lemma17FixedScale a (j + 1) =
        2 * lemma17FixedScale a j
  hbelow :
    theorem6FixedCStarSq *
        lemma17FixedScale a
          (lemma17FixedStageCount n a ha) < n
  habove :
    n ≤ theorem6FixedCStarSq *
      (2 * lemma17FixedScale a
        (lemma17FixedStageCount n a ha))

/-- The fixed dyadic scale facts follow from positivity and a strict initial
lower bracket. -/
theorem lemma17FixedScaleFacts
    (n a : ℕ) (ha : 0 < a)
    (hbase : theorem6FixedCStarSq * a < n) :
    Lemma17FixedScaleFacts n a ha :=
  { hscale0 := lemma17FixedScale_zero a
    hdouble := fun j _ => lemma17FixedScale_succ a j
    hbelow :=
      lemma17FixedStageCount_below n a ha hbase
    habove :=
      lemma17FixedStageCount_above n a ha }

/-- Dyadic scales are monotone in their index. -/
theorem lemma17FixedScale_mono
    (a i j : ℕ) (hij : i ≤ j) :
    lemma17FixedScale a i ≤
      lemma17FixedScale a j := by
  unfold lemma17FixedScale
  exact Nat.mul_le_mul_right a
    (Nat.pow_le_pow_right (by norm_num) hij)

/-- Every selected scale through the final predecessor inherits all elementary
population-room inequalities from the fixed-square lower bracket. -/
theorem lemma17FixedScale_room
    (n a : ℕ) (ha : 0 < a)
    (hbase : theorem6FixedCStarSq * a < n)
    (ha4 : 4 ≤ a)
    (j : ℕ)
    (hj : j ≤ lemma17FixedStageCount n a ha) :
    4 ≤ lemma17FixedScale a j ∧
    4 * lemma17FixedScale a j ≤ n ∧
    2 * lemma17FixedScale a j ≤ n ∧
    5 * (lemma17FixedScale a j + 1) ≤ n + 1 := by
  have hmono :
      lemma17FixedScale a j ≤
        lemma17FixedScale a
          (lemma17FixedStageCount n a ha) :=
    lemma17FixedScale_mono a j
      (lemma17FixedStageCount n a ha) hj
  have hbelow :
      theorem6FixedCStarSq *
          lemma17FixedScale a j < n := by
    exact
      (Nat.mul_le_mul_left theorem6FixedCStarSq
        hmono).trans_lt
        (lemma17FixedStageCount_below
          n a ha hbase)
  have haj :
      a ≤ lemma17FixedScale a j := by
    simpa [lemma17FixedScale_zero] using
      lemma17FixedScale_mono a 0 j (Nat.zero_le j)
  rw [theorem6FixedCStar_sq] at hbelow
  omega

/-- Scale-only hypotheses of the ordinary Lemma 17 prefix and its final
custom source slot. -/
structure Lemma17FixedScaleRoomFacts
    (n a : ℕ) (ha : 0 < a) : Prop where
  hscale0 :
    lemma17FixedScale a 0 = a
  hdouble :
    ∀ j < lemma17FixedStageCount n a ha,
      lemma17FixedScale a (j + 1) =
        2 * lemma17FixedScale a j
  hmonotone :
    ∀ j ≤ lemma17FixedStageCount n a ha,
      lemma17FixedScale a j ≤
        lemma17FixedScale a
          (lemma17FixedStageCount n a ha)
  hscaleLower :
    ∀ j ≤ lemma17FixedStageCount n a ha,
      4 ≤ lemma17FixedScale a j
  hquarter :
    ∀ j ≤ lemma17FixedStageCount n a ha,
      4 * lemma17FixedScale a j ≤ n
  htarget :
    ∀ j ≤ lemma17FixedStageCount n a ha,
      2 * lemma17FixedScale a j ≤ n
  hlabelRoom :
    ∀ j ≤ lemma17FixedStageCount n a ha,
      5 * (lemma17FixedScale a j + 1) ≤ n + 1
  hbelow :
    theorem6FixedCStarSq *
        lemma17FixedScale a
          (lemma17FixedStageCount n a ha) < n
  habove :
    n ≤ theorem6FixedCStarSq *
      (2 * lemma17FixedScale a
        (lemma17FixedStageCount n a ha))

/-- The fixed dyadic choice supplies all scale-room fields used before the
custom landing. -/
theorem lemma17FixedScaleRoomFacts
    (n a : ℕ) (ha : 0 < a)
    (hbase : theorem6FixedCStarSq * a < n)
    (ha4 : 4 ≤ a) :
    Lemma17FixedScaleRoomFacts n a ha := by
  have hroom :
      ∀ j, j ≤ lemma17FixedStageCount n a ha →
        4 ≤ lemma17FixedScale a j ∧
        4 * lemma17FixedScale a j ≤ n ∧
        2 * lemma17FixedScale a j ≤ n ∧
        5 * (lemma17FixedScale a j + 1) ≤ n + 1 :=
    fun j hj =>
      lemma17FixedScale_room n a ha hbase ha4 j hj
  exact
    { hscale0 := lemma17FixedScale_zero a
      hdouble := fun j _ => lemma17FixedScale_succ a j
      hmonotone :=
        fun j hj =>
          lemma17FixedScale_mono a j
            (lemma17FixedStageCount n a ha) hj
      hscaleLower := fun j hj => (hroom j hj).1
      hquarter := fun j hj => (hroom j hj).2.1
      htarget := fun j hj => (hroom j hj).2.2.1
      hlabelRoom := fun j hj => (hroom j hj).2.2.2
      hbelow :=
        lemma17FixedStageCount_below n a ha hbase
      habove :=
        lemma17FixedStageCount_above n a ha }

/-- The number of ordinary dyadic stages is at most the binary logarithm of
the population. -/
theorem lemma17FixedStageCount_le_log
    (n a : ℕ) (ha : 0 < a)
    (hbase : theorem6FixedCStarSq * a < n) :
    lemma17FixedStageCount n a ha ≤ Nat.log 2 n := by
  let m := lemma17FixedStageCount n a ha
  have hbelow :=
    lemma17FixedStageCount_below n a ha hbase
  have hscaleLt :
      lemma17FixedScale a m < n := by
    change theorem6FixedCStarSq *
        lemma17FixedScale a m < n at hbelow
    rw [theorem6FixedCStar_sq] at hbelow
    omega
  have hpow :
      2 ^ m ≤ lemma17FixedScale a m := by
    unfold lemma17FixedScale
    have ha1 : 1 ≤ a := by omega
    simpa using Nat.mul_le_mul_left (2 ^ m) ha1
  exact Nat.le_log_of_pow_le (by norm_num)
    (hpow.trans hscaleLt.le)

/-- The fixed large-population threshold alone pays the nineteen non-prefix
blocks in the raw-clock schedule. -/
theorem theorem6FixedPostStages_add_two_le_log
    (n : ℕ)
    (hlarge :
      theorem6FixedCStarSq *
          (theorem6FixedCStarSq + 6) ≤ n) :
    theorem6FixedPostStages + 2 ≤ Nat.log 2 n := by
  apply Nat.le_log_of_pow_le (by norm_num)
  calc
    2 ^ (theorem6FixedPostStages + 2)
        ≤ theorem6FixedCStarSq *
          (theorem6FixedCStarSq + 6) := by
      norm_num [theorem6FixedPostStages,
        theorem6FixedCStarSq, theorem6FixedCStar]
    _ ≤ n := hlarge

/-- A factor-two logarithmic budget pays the ordinary prefix, the fixed
landing, and all fixed post-critical stages. -/
theorem lemma17FixedStageCount_add_post_le_theorem6Q
    (n γ a : ℕ) (ha : 0 < a)
    (hbase : theorem6FixedCStarSq * a < n)
    (hγ : 2 ≤ γ)
    (hpostLog :
      theorem6FixedPostStages + 2 ≤ Nat.log 2 n) :
    lemma17FixedStageCount n a ha +
        theorem6FixedPostStages + 2 ≤
      theorem6Q n γ := by
  have hm :
      lemma17FixedStageCount n a ha ≤
        Nat.log 2 n :=
    lemma17FixedStageCount_le_log n a ha hbase
  unfold theorem6Q
  nlinarith

end

end Tri

#print axioms Tri.lemma17FixedStageCount_exists
#print axioms Tri.lemma17FixedStageCount_above
#print axioms Tri.lemma17FixedStageCount_below
#print axioms Tri.lemma17FixedScaleFacts
#print axioms Tri.lemma17FixedScale_mono
#print axioms Tri.lemma17FixedScale_room
#print axioms Tri.lemma17FixedScaleRoomFacts
#print axioms Tri.lemma17FixedStageCount_le_log
#print axioms Tri.theorem6FixedPostStages_add_two_le_log
#print axioms
  Tri.lemma17FixedStageCount_add_post_le_theorem6Q
