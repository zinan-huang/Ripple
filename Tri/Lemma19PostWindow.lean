/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Lemma16To19GapLadder
import Tri.Lemma16To19ErrorConditions

/-!
# A fixed dyadic post-decisive window

Choosing `cStar = 1024` aligns its square with the final quarter threshold:
seventeen post-decisive doublings beginning at `2a` end at `2^18 a`, whose
fourfold is exactly `1024^2 a`.  A least-multiple ceiling supplies the small
additive error needed by the canonical post-window.
-/

namespace Tri

noncomputable section

def theorem6CStar : ℕ := 1024

def theorem6CStarSq : ℕ :=
  theorem6CStar ^ 2

def theorem6PostStages : ℕ := 17

def theorem6PostScale (a j : ℕ) : ℕ :=
  2 ^ (j + 1) * a

@[simp] theorem theorem6CStar_sq :
    theorem6CStarSq = 1048576 := by
  norm_num [theorem6CStarSq, theorem6CStar]

@[simp] theorem theorem6PostScale_zero
    (a : ℕ) :
    theorem6PostScale a 0 = 2 * a := by
  simp [theorem6PostScale]

@[simp] theorem theorem6PostScale_succ
    (a j : ℕ) :
    theorem6PostScale a (j + 1) =
      2 * theorem6PostScale a j := by
  simp [theorem6PostScale, pow_succ]
  ring

theorem theorem6PostScale_final
    (a : ℕ) :
    theorem6PostScale a theorem6PostStages =
      262144 * a := by
  norm_num [theorem6PostScale,
    theorem6PostStages]

theorem theorem6PostScale_four_final
    (a : ℕ) :
    4 * theorem6PostScale
        a theorem6PostStages =
      theorem6CStarSq * a := by
  rw [theorem6PostScale_final]
  norm_num [theorem6CStarSq,
    theorem6CStar]
  ring

/-- A fixed-square multiple covers every natural population. -/
theorem theorem6CriticalScale_exists
    (n : ℕ) :
    ∃ a, n ≤ theorem6CStarSq * a := by
  refine ⟨n, ?_⟩
  rw [theorem6CStar_sq]
  nlinarith

/-- Least fixed-square multiple covering `n`. -/
noncomputable def theorem6CriticalScale
    (n : ℕ) : ℕ :=
  Nat.find (theorem6CriticalScale_exists n)

theorem theorem6CriticalScale_spec
    (n : ℕ) :
    n ≤ theorem6CStarSq *
      theorem6CriticalScale n :=
  Nat.find_spec (theorem6CriticalScale_exists n)

theorem theorem6CriticalScale_pos
    (n : ℕ) (hn : 0 < n) :
    0 < theorem6CriticalScale n := by
  by_contra hnot
  have ha0 :
      theorem6CriticalScale n = 0 := by
    exact Nat.eq_zero_of_not_pos hnot
  have hspec := theorem6CriticalScale_spec n
  rw [ha0] at hspec
  simp at hspec
  omega

/-- The least covering multiple has an additive excess strictly below one
fixed square and a predecessor witness for the critical scale. -/
theorem theorem6CriticalScale_additive_ceiling
    (n : ℕ) (hn : 0 < n) :
    ∃ aPred e,
      aPred + 1 = theorem6CriticalScale n ∧
      n + e =
        theorem6CStarSq *
          theorem6CriticalScale n ∧
      e < theorem6CStarSq := by
  let a := theorem6CriticalScale n
  have ha : 0 < a :=
    theorem6CriticalScale_pos n hn
  obtain ⟨aPred, haPred⟩ :=
    Nat.exists_eq_add_of_le ha
  have haPred' : aPred + 1 = a := by
    omega
  have hpredLt :
      aPred < theorem6CriticalScale n := by
    simpa [a] using (show aPred < a by omega)
  have hminimal :
      ¬ n ≤ theorem6CStarSq * aPred := by
    exact Nat.find_min
      (theorem6CriticalScale_exists n)
      hpredLt
  have hpred :
      theorem6CStarSq * aPred < n := by
    omega
  obtain ⟨e, he⟩ :=
    Nat.exists_eq_add_of_le
      (theorem6CriticalScale_spec n)
  have he' :
      n + e = theorem6CStarSq * a := by
    simpa [a] using he.symm
  refine ⟨aPred, e, ?_, ?_, ?_⟩
  · simpa [a] using haPred'
  · simpa [a] using he'
  · have hmul :
        theorem6CStarSq * a =
          theorem6CStarSq * aPred +
            theorem6CStarSq := by
      rw [show a = aPred + 1 by omega]
      ring
    omega

/-- A population lower bound propagates to the least critical scale. -/
theorem theorem6CriticalScale_lower
    (n T : ℕ)
    (hT : theorem6CStarSq * T ≤ n) :
    T ≤ theorem6CriticalScale n := by
  have hcover :=
    theorem6CriticalScale_spec n
  rw [theorem6CStar_sq] at hT hcover
  omega

/-- All scale-only assumptions required by the corrected theorem. -/
structure Lemma19WindowFacts
    (n a e : ℕ) : Prop where
  hscale0 :
    theorem6PostScale a 0 = 2 * a
  hdouble :
    ∀ j < theorem6PostStages,
      theorem6PostScale a (j + 1) =
        2 * theorem6PostScale a j
  ha :
    ∀ j < theorem6PostStages,
      4 ≤ theorem6PostScale a j
  hquarter :
    ∀ j < theorem6PostStages,
      4 * theorem6PostScale a j ≤ n
  htarget :
    ∀ j < theorem6PostStages,
      2 * theorem6PostScale a j ≤ n
  hlabelRoom :
    ∀ j < theorem6PostStages,
      5 * (theorem6PostScale a j + 1) ≤
        n + 1
  hfinal :
    4 ≤ theorem6PostScale
      a theorem6PostStages
  hstageRoomFinal :
    theorem6PostScale
        a theorem6PostStages + 4 ≤ n
  hquarterFinal :
    n ≤
      4 * theorem6PostScale
        a theorem6PostStages
  hmonotone :
    ∀ j ≤ theorem6PostStages,
      theorem6PostScale a j ≤
        theorem6PostScale
          a theorem6PostStages
  hPostWindow :
    4 * theorem6PostScale
          a theorem6PostStages + 7 ≤
      n + 3 * a

/-- The additive ceiling gives every current dyadic room premise. -/
theorem lemma19WindowFacts
    (n a e : ℕ)
    (hceil :
      n + e = theorem6CStarSq * a)
    (hexcess : e < theorem6CStarSq)
    (haLarge : theorem6CStarSq + 6 ≤ a) :
    Lemma19WindowFacts n a e := by
  have ha4 : 4 ≤ a := by
    rw [theorem6CStar_sq] at haLarge
    omega
  have heBound : e + 7 ≤ 3 * a := by
    rw [theorem6CStar_sq] at hexcess haLarge
    omega
  have hceilN : n + e = 1048576 * a := by
    simpa using hceil
  have hexcessN : e < 1048576 := by
    simpa using hexcess
  have haLargeN : 1048582 ≤ a := by
    simpa using haLarge
  have hnQuarterBase : 524288 * a ≤ n := by
    omega
  have hnLabelBase :
      655360 * a + 5 ≤ n + 1 := by
    omega
  have hnFinalRoom :
      262144 * a + 4 ≤ n := by
    omega
  refine
    { hscale0 := theorem6PostScale_zero a
      hdouble := ?_
      ha := ?_
      hquarter := ?_
      htarget := ?_
      hlabelRoom := ?_
      hfinal := ?_
      hstageRoomFinal := ?_
      hquarterFinal := ?_
      hmonotone := ?_
      hPostWindow := ?_ }
  · intro j hj
    exact theorem6PostScale_succ a j
  · intro j hj
    unfold theorem6PostScale
    have hp : 1 ≤ 2 ^ (j + 1) :=
      one_le_pow₀ (by norm_num)
    have haPow :
        a ≤ 2 ^ (j + 1) * a := by
      simpa using Nat.mul_le_mul_right a hp
    exact ha4.trans haPow
  · intro j hj
    have hp :
        2 ^ (j + 1) ≤ 2 ^ 17 :=
      Nat.pow_le_pow_right (by norm_num)
        (by
          simpa [theorem6PostStages] using hj)
    have hmul :=
      Nat.mul_le_mul_right a hp
    unfold theorem6PostScale
    norm_num at hmul
    calc
      4 * (2 ^ (j + 1) * a)
          ≤ 4 * (131072 * a) :=
        Nat.mul_le_mul_left 4 hmul
      _ = 524288 * a := by ring
      _ ≤ n := hnQuarterBase
  · intro j hj
    have hq :
        4 * theorem6PostScale a j ≤ n := by
      have hp :
          2 ^ (j + 1) ≤ 2 ^ 17 :=
        Nat.pow_le_pow_right (by norm_num)
          (by
            simpa [theorem6PostStages] using hj)
      have hmul :=
        Nat.mul_le_mul_right a hp
      unfold theorem6PostScale
      norm_num at hmul
      calc
        4 * (2 ^ (j + 1) * a)
            ≤ 4 * (131072 * a) :=
          Nat.mul_le_mul_left 4 hmul
        _ = 524288 * a := by ring
        _ ≤ n := hnQuarterBase
    omega
  · intro j hj
    have hp :
        2 ^ (j + 1) ≤ 2 ^ 17 :=
      Nat.pow_le_pow_right (by norm_num)
        (by
          simpa [theorem6PostStages] using hj)
    have hmul :=
      Nat.mul_le_mul_right a hp
    unfold theorem6PostScale
    norm_num at hmul
    calc
      5 * (2 ^ (j + 1) * a + 1)
          ≤ 5 * (131072 * a + 1) :=
        Nat.mul_le_mul_left 5
          (Nat.add_le_add_right hmul 1)
      _ = 655360 * a + 5 := by ring
      _ ≤ n + 1 := hnLabelBase
  · rw [theorem6PostScale_final]
    omega
  · rw [theorem6PostScale_final]
    exact hnFinalRoom
  · rw [theorem6PostScale_four_final]
    omega
  · intro j hj
    unfold theorem6PostScale
    have hp :
        2 ^ (j + 1) ≤ 2 ^ 18 :=
      Nat.pow_le_pow_right (by norm_num)
        (by
          have hj' : j + 1 ≤
              theorem6PostStages + 1 :=
            Nat.add_le_add_right hj 1
          simpa [theorem6PostStages] using hj')
    norm_num at hp
    exact Nat.mul_le_mul_right a hp
  · rw [theorem6PostScale_four_final]
    omega

/-- For all sufficiently large populations, the least critical scale supplies
the complete fixed window. -/
theorem lemma19WindowFacts_of_large
    (n : ℕ)
    (hn : 0 < n)
    (hlarge :
      theorem6CStarSq *
          (theorem6CStarSq + 6) ≤ n) :
    ∃ e,
      Lemma19WindowFacts n
        (theorem6CriticalScale n) e := by
  obtain ⟨aPred, e, haPred, hceil, hexcess⟩ :=
    theorem6CriticalScale_additive_ceiling n hn
  have haLarge :
      theorem6CStarSq + 6 ≤
        theorem6CriticalScale n :=
    theorem6CriticalScale_lower
      n (theorem6CStarSq + 6) hlarge
  exact
    ⟨e, lemma19WindowFacts
      n (theorem6CriticalScale n) e
      hceil hexcess haLarge⟩

end

end Tri

#print axioms Tri.theorem6CriticalScale_spec
#print axioms Tri.theorem6CriticalScale_additive_ceiling
#print axioms Tri.theorem6CriticalScale_lower
#print axioms Tri.lemma19WindowFacts
#print axioms Tri.lemma19WindowFacts_of_large
