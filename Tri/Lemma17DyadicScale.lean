/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Lemma17CriticalLanding
import Tri.Theorem6Parameters
import Mathlib.Data.Int.Star

/-!
# The last dyadic scale below the fixed landing

The ordinary Lemma 17 prefix stops at the least dyadic index whose next
doubling covers the fixed critical scale.  Minimality supplies the strict
lower bracket without natural-number subtraction in any statement.
-/

namespace Tri

noncomputable section

/-- The dyadic Lemma 17 scale starting at `a`. -/
def lemma17Scale (a j : ℕ) : ℕ :=
  2 ^ j * a

@[simp] theorem lemma17Scale_zero
    (a : ℕ) :
    lemma17Scale a 0 = a := by
  simp [lemma17Scale]

@[simp] theorem lemma17Scale_succ
    (a j : ℕ) :
    lemma17Scale a (j + 1) =
      2 * lemma17Scale a j := by
  simp [lemma17Scale, pow_succ]
  ring

/-- Some dyadic successor covers every positive target. -/
theorem lemma17StageCount_exists
    (n a : ℕ)
    (ha : 0 < a) :
    ∃ m,
      n ≤ theorem6CStarSq *
        (2 * lemma17Scale a m) := by
  refine ⟨n, ?_⟩
  have hnPow : n ≤ 2 ^ n :=
    n.lt_two_pow_self.le
  have hfactor :
      1 ≤ 2 * theorem6CStarSq * a := by
    have hc : 0 < theorem6CStarSq := by
      norm_num [theorem6CStarSq,
        theorem6CStar]
    have hpos :
        0 < 2 * theorem6CStarSq * a :=
      Nat.mul_pos (Nat.mul_pos (by omega) hc) ha
    omega
  have hscaled :
      2 ^ n ≤
        2 ^ n * (2 * theorem6CStarSq * a) := by
    simpa using Nat.mul_le_mul_left (2 ^ n) hfactor
  calc
    n ≤ 2 ^ n := hnPow
    _ ≤ 2 ^ n * (2 * theorem6CStarSq * a) :=
      hscaled
    _ =
        theorem6CStarSq *
          (2 * lemma17Scale a n) := by
      unfold lemma17Scale
      ring

/-- Least dyadic index whose successor covers the fixed critical scale. -/
noncomputable def lemma17StageCount
    (n a : ℕ) (ha : 0 < a) : ℕ :=
  Nat.find (lemma17StageCount_exists n a ha)

/-- The successor of the selected dyadic scale covers `n`. -/
theorem lemma17StageCount_above
    (n a : ℕ) (ha : 0 < a) :
    n ≤ theorem6CStarSq *
      (2 * lemma17Scale a
        (lemma17StageCount n a ha)) :=
  Nat.find_spec (lemma17StageCount_exists n a ha)

/-- If the initial scale is still below the target, the selected dyadic scale
is also strictly below it. -/
theorem lemma17StageCount_below
    (n a : ℕ) (ha : 0 < a)
    (hbase : theorem6CStarSq * a < n) :
    theorem6CStarSq *
        lemma17Scale a
          (lemma17StageCount n a ha) < n := by
  let m := lemma17StageCount n a ha
  by_cases hm : m = 0
  · simpa [m, hm] using hbase
  · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hm
    have hklt :
        k < lemma17StageCount n a ha := by
      change k < m
      omega
    have hminimal :
        ¬ n ≤ theorem6CStarSq *
          (2 * lemma17Scale a k) :=
      Nat.find_min
        (lemma17StageCount_exists n a ha) hklt
    change theorem6CStarSq *
        lemma17Scale a m < n
    rw [hk, lemma17Scale_succ]
    omega

/-- Complete fixed dyadic bracket for the ordinary Lemma 17 prefix. -/
structure Lemma17ScaleFacts
    (n a : ℕ) (ha : 0 < a) : Prop where
  hscale0 :
    lemma17Scale a 0 = a
  hdouble :
    ∀ j < lemma17StageCount n a ha,
      lemma17Scale a (j + 1) =
        2 * lemma17Scale a j
  hbelow :
    theorem6CStarSq *
        lemma17Scale a
          (lemma17StageCount n a ha) < n
  habove :
    n ≤ theorem6CStarSq *
      (2 * lemma17Scale a
        (lemma17StageCount n a ha))

/-- The fixed dyadic scale facts follow from positivity and a strict initial
lower bracket. -/
theorem lemma17ScaleFacts
    (n a : ℕ) (ha : 0 < a)
    (hbase : theorem6CStarSq * a < n) :
    Lemma17ScaleFacts n a ha :=
  { hscale0 := lemma17Scale_zero a
    hdouble := fun j _ => lemma17Scale_succ a j
    hbelow :=
      lemma17StageCount_below n a ha hbase
    habove :=
      lemma17StageCount_above n a ha }

/-- Dyadic scales are monotone in their index. -/
theorem lemma17Scale_mono
    (a i j : ℕ) (hij : i ≤ j) :
    lemma17Scale a i ≤
      lemma17Scale a j := by
  unfold lemma17Scale
  exact Nat.mul_le_mul_right a
    (Nat.pow_le_pow_right (by norm_num) hij)

/-- Every selected scale through the final predecessor inherits all elementary
population-room inequalities from the fixed-square lower bracket. -/
theorem lemma17Scale_room
    (n a : ℕ) (ha : 0 < a)
    (hbase : theorem6CStarSq * a < n)
    (ha4 : 4 ≤ a)
    (j : ℕ)
    (hj : j ≤ lemma17StageCount n a ha) :
    4 ≤ lemma17Scale a j ∧
    4 * lemma17Scale a j ≤ n ∧
    2 * lemma17Scale a j ≤ n ∧
    5 * (lemma17Scale a j + 1) ≤ n + 1 := by
  have hmono :
      lemma17Scale a j ≤
        lemma17Scale a
          (lemma17StageCount n a ha) :=
    lemma17Scale_mono a j
      (lemma17StageCount n a ha) hj
  have hbelow :
      theorem6CStarSq *
          lemma17Scale a j < n := by
    exact
      (Nat.mul_le_mul_left theorem6CStarSq
        hmono).trans_lt
        (lemma17StageCount_below
          n a ha hbase)
  have haj :
      a ≤ lemma17Scale a j := by
    simpa [lemma17Scale_zero] using
      lemma17Scale_mono a 0 j (Nat.zero_le j)
  rw [theorem6CStar_sq] at hbelow
  omega

/-- Scale-only hypotheses of the ordinary Lemma 17 prefix and its final
custom source slot. -/
structure Lemma17ScaleRoomFacts
    (n a : ℕ) (ha : 0 < a) : Prop where
  hscale0 :
    lemma17Scale a 0 = a
  hdouble :
    ∀ j < lemma17StageCount n a ha,
      lemma17Scale a (j + 1) =
        2 * lemma17Scale a j
  hmonotone :
    ∀ j ≤ lemma17StageCount n a ha,
      lemma17Scale a j ≤
        lemma17Scale a
          (lemma17StageCount n a ha)
  hscaleLower :
    ∀ j ≤ lemma17StageCount n a ha,
      4 ≤ lemma17Scale a j
  hquarter :
    ∀ j ≤ lemma17StageCount n a ha,
      4 * lemma17Scale a j ≤ n
  htarget :
    ∀ j ≤ lemma17StageCount n a ha,
      2 * lemma17Scale a j ≤ n
  hlabelRoom :
    ∀ j ≤ lemma17StageCount n a ha,
      5 * (lemma17Scale a j + 1) ≤ n + 1
  hbelow :
    theorem6CStarSq *
        lemma17Scale a
          (lemma17StageCount n a ha) < n
  habove :
    n ≤ theorem6CStarSq *
      (2 * lemma17Scale a
        (lemma17StageCount n a ha))

/-- The fixed dyadic choice supplies all scale-room fields used before the
custom landing. -/
theorem lemma17ScaleRoomFacts
    (n a : ℕ) (ha : 0 < a)
    (hbase : theorem6CStarSq * a < n)
    (ha4 : 4 ≤ a) :
    Lemma17ScaleRoomFacts n a ha := by
  have hroom :
      ∀ j, j ≤ lemma17StageCount n a ha →
        4 ≤ lemma17Scale a j ∧
        4 * lemma17Scale a j ≤ n ∧
        2 * lemma17Scale a j ≤ n ∧
        5 * (lemma17Scale a j + 1) ≤ n + 1 :=
    fun j hj =>
      lemma17Scale_room n a ha hbase ha4 j hj
  exact
    { hscale0 := lemma17Scale_zero a
      hdouble := fun j _ => lemma17Scale_succ a j
      hmonotone :=
        fun j hj =>
          lemma17Scale_mono a j
            (lemma17StageCount n a ha) hj
      hscaleLower := fun j hj => (hroom j hj).1
      hquarter := fun j hj => (hroom j hj).2.1
      htarget := fun j hj => (hroom j hj).2.2.1
      hlabelRoom := fun j hj => (hroom j hj).2.2.2
      hbelow :=
        lemma17StageCount_below n a ha hbase
      habove :=
        lemma17StageCount_above n a ha }

/-- The number of ordinary dyadic stages is at most the binary logarithm of
the population. -/
theorem lemma17StageCount_le_log
    (n a : ℕ) (ha : 0 < a)
    (hbase : theorem6CStarSq * a < n) :
    lemma17StageCount n a ha ≤ Nat.log 2 n := by
  let m := lemma17StageCount n a ha
  have hbelow :=
    lemma17StageCount_below n a ha hbase
  have hscaleLt :
      lemma17Scale a m < n := by
    change theorem6CStarSq *
        lemma17Scale a m < n at hbelow
    rw [theorem6CStar_sq] at hbelow
    omega
  have hpow :
      2 ^ m ≤ lemma17Scale a m := by
    unfold lemma17Scale
    have ha1 : 1 ≤ a := by omega
    simpa using Nat.mul_le_mul_left (2 ^ m) ha1
  exact Nat.le_log_of_pow_le (by norm_num)
    (hpow.trans hscaleLt.le)

/-- The fixed large-population threshold alone pays the nineteen non-prefix
blocks in the raw-clock schedule. -/
theorem theorem6PostStages_add_two_le_log
    (n : ℕ)
    (hlarge :
      theorem6CStarSq *
          (theorem6CStarSq + 6) ≤ n) :
    theorem6PostStages + 2 ≤ Nat.log 2 n := by
  apply Nat.le_log_of_pow_le (by norm_num)
  calc
    2 ^ (theorem6PostStages + 2)
        ≤ theorem6CStarSq *
          (theorem6CStarSq + 6) := by
      norm_num [theorem6PostStages,
        theorem6CStarSq, theorem6CStar]
    _ ≤ n := hlarge

/-- A factor-two logarithmic budget pays the ordinary prefix, the fixed
landing, and all fixed post-critical stages. -/
theorem lemma17StageCount_add_post_le_theorem6Q
    (n γ a : ℕ) (ha : 0 < a)
    (hbase : theorem6CStarSq * a < n)
    (hγ : 2 ≤ γ)
    (hpostLog :
      theorem6PostStages + 2 ≤ Nat.log 2 n) :
    lemma17StageCount n a ha +
        theorem6PostStages + 2 ≤
      theorem6Q n γ := by
  have hm :
      lemma17StageCount n a ha ≤
        Nat.log 2 n :=
    lemma17StageCount_le_log n a ha hbase
  unfold theorem6Q
  nlinarith

end

end Tri

#print axioms Tri.lemma17StageCount_exists
#print axioms Tri.lemma17StageCount_above
#print axioms Tri.lemma17StageCount_below
#print axioms Tri.lemma17ScaleFacts
#print axioms Tri.lemma17Scale_mono
#print axioms Tri.lemma17Scale_room
#print axioms Tri.lemma17ScaleRoomFacts
#print axioms Tri.lemma17StageCount_le_log
#print axioms Tri.theorem6PostStages_add_two_le_log
#print axioms
  Tri.lemma17StageCount_add_post_le_theorem6Q
