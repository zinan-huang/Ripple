/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Lemma16To19Corrected
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

def theorem6FixedCStar : ℕ := 1024

def theorem6FixedCStarSq : ℕ :=
  theorem6FixedCStar ^ 2

def theorem6FixedPostStages : ℕ := 17

def theorem6FixedPostScale (a j : ℕ) : ℕ :=
  2 ^ (j + 1) * a

@[simp] theorem theorem6FixedCStar_sq :
    theorem6FixedCStarSq = 1048576 := by
  norm_num [theorem6FixedCStarSq, theorem6FixedCStar]

@[simp] theorem theorem6FixedPostScale_zero
    (a : ℕ) :
    theorem6FixedPostScale a 0 = 2 * a := by
  simp [theorem6FixedPostScale]

@[simp] theorem theorem6FixedPostScale_succ
    (a j : ℕ) :
    theorem6FixedPostScale a (j + 1) =
      2 * theorem6FixedPostScale a j := by
  simp [theorem6FixedPostScale, pow_succ]
  ring

theorem theorem6FixedPostScale_final
    (a : ℕ) :
    theorem6FixedPostScale a theorem6FixedPostStages =
      262144 * a := by
  norm_num [theorem6FixedPostScale,
    theorem6FixedPostStages]

theorem theorem6FixedPostScale_four_final
    (a : ℕ) :
    4 * theorem6FixedPostScale
        a theorem6FixedPostStages =
      theorem6FixedCStarSq * a := by
  rw [theorem6FixedPostScale_final]
  norm_num [theorem6FixedCStarSq,
    theorem6FixedCStar]
  ring

/-- A fixed-square multiple covers every natural population. -/
theorem theorem6FixedCriticalScale_exists
    (n : ℕ) :
    ∃ a, n ≤ theorem6FixedCStarSq * a := by
  refine ⟨n, ?_⟩
  rw [theorem6FixedCStar_sq]
  nlinarith

/-- Least fixed-square multiple covering `n`. -/
noncomputable def theorem6FixedCriticalScale
    (n : ℕ) : ℕ :=
  Nat.find (theorem6FixedCriticalScale_exists n)

theorem theorem6FixedCriticalScale_spec
    (n : ℕ) :
    n ≤ theorem6FixedCStarSq *
      theorem6FixedCriticalScale n :=
  Nat.find_spec (theorem6FixedCriticalScale_exists n)

theorem theorem6FixedCriticalScale_pos
    (n : ℕ) (hn : 0 < n) :
    0 < theorem6FixedCriticalScale n := by
  by_contra hnot
  have ha0 :
      theorem6FixedCriticalScale n = 0 := by
    exact Nat.eq_zero_of_not_pos hnot
  have hspec := theorem6FixedCriticalScale_spec n
  rw [ha0] at hspec
  simp at hspec
  omega

/-- The least covering multiple has an additive excess strictly below one
fixed square and a predecessor witness for the critical scale. -/
theorem theorem6FixedCriticalScale_additive_ceiling
    (n : ℕ) (hn : 0 < n) :
    ∃ aPred e,
      aPred + 1 = theorem6FixedCriticalScale n ∧
      n + e =
        theorem6FixedCStarSq *
          theorem6FixedCriticalScale n ∧
      e < theorem6FixedCStarSq := by
  let a := theorem6FixedCriticalScale n
  have ha : 0 < a :=
    theorem6FixedCriticalScale_pos n hn
  obtain ⟨aPred, haPred⟩ :=
    Nat.exists_eq_add_of_le ha
  have haPred' : aPred + 1 = a := by
    omega
  have hpredLt :
      aPred < theorem6FixedCriticalScale n := by
    simpa [a] using (show aPred < a by omega)
  have hminimal :
      ¬ n ≤ theorem6FixedCStarSq * aPred := by
    exact Nat.find_min
      (theorem6FixedCriticalScale_exists n)
      hpredLt
  have hpred :
      theorem6FixedCStarSq * aPred < n := by
    omega
  obtain ⟨e, he⟩ :=
    Nat.exists_eq_add_of_le
      (theorem6FixedCriticalScale_spec n)
  have he' :
      n + e = theorem6FixedCStarSq * a := by
    simpa [a] using he.symm
  refine ⟨aPred, e, ?_, ?_, ?_⟩
  · simpa [a] using haPred'
  · simpa [a] using he'
  · have hmul :
        theorem6FixedCStarSq * a =
          theorem6FixedCStarSq * aPred +
            theorem6FixedCStarSq := by
      rw [show a = aPred + 1 by omega]
      ring
    omega

/-- A population lower bound propagates to the least critical scale. -/
theorem theorem6FixedCriticalScale_lower
    (n T : ℕ)
    (hT : theorem6FixedCStarSq * T ≤ n) :
    T ≤ theorem6FixedCriticalScale n := by
  have hcover :=
    theorem6FixedCriticalScale_spec n
  rw [theorem6FixedCStar_sq] at hT hcover
  omega

/-- All scale-only assumptions required by the corrected theorem. -/
structure Lemma19FixedWindowFacts
    (n a e : ℕ) : Prop where
  hscale0 :
    theorem6FixedPostScale a 0 = 2 * a
  hdouble :
    ∀ j < theorem6FixedPostStages,
      theorem6FixedPostScale a (j + 1) =
        2 * theorem6FixedPostScale a j
  ha :
    ∀ j < theorem6FixedPostStages,
      4 ≤ theorem6FixedPostScale a j
  hquarter :
    ∀ j < theorem6FixedPostStages,
      4 * theorem6FixedPostScale a j ≤ n
  htarget :
    ∀ j < theorem6FixedPostStages,
      2 * theorem6FixedPostScale a j ≤ n
  hlabelRoom :
    ∀ j < theorem6FixedPostStages,
      5 * (theorem6FixedPostScale a j + 1) ≤
        n + 1
  hfinal :
    4 ≤ theorem6FixedPostScale
      a theorem6FixedPostStages
  hstageRoomFinal :
    theorem6FixedPostScale
        a theorem6FixedPostStages + 4 ≤ n
  hquarterFinal :
    n ≤
      4 * theorem6FixedPostScale
        a theorem6FixedPostStages
  hmonotone :
    ∀ j ≤ theorem6FixedPostStages,
      theorem6FixedPostScale a j ≤
        theorem6FixedPostScale
          a theorem6FixedPostStages
  hPostWindow :
    4 * theorem6FixedPostScale
          a theorem6FixedPostStages + 7 ≤
      n + 3 * a

/-- The additive ceiling gives every current dyadic room premise. -/
theorem lemma19FixedWindowFacts
    (n a e : ℕ)
    (hceil :
      n + e = theorem6FixedCStarSq * a)
    (hexcess : e < theorem6FixedCStarSq)
    (haLarge : theorem6FixedCStarSq + 6 ≤ a) :
    Lemma19FixedWindowFacts n a e := by
  have ha4 : 4 ≤ a := by
    rw [theorem6FixedCStar_sq] at haLarge
    omega
  have heBound : e + 7 ≤ 3 * a := by
    rw [theorem6FixedCStar_sq] at hexcess haLarge
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
    { hscale0 := theorem6FixedPostScale_zero a
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
    exact theorem6FixedPostScale_succ a j
  · intro j hj
    unfold theorem6FixedPostScale
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
          simpa [theorem6FixedPostStages] using hj)
    have hmul :=
      Nat.mul_le_mul_right a hp
    unfold theorem6FixedPostScale
    norm_num at hmul
    calc
      4 * (2 ^ (j + 1) * a)
          ≤ 4 * (131072 * a) :=
        Nat.mul_le_mul_left 4 hmul
      _ = 524288 * a := by ring
      _ ≤ n := hnQuarterBase
  · intro j hj
    have hq :
        4 * theorem6FixedPostScale a j ≤ n := by
      have hp :
          2 ^ (j + 1) ≤ 2 ^ 17 :=
        Nat.pow_le_pow_right (by norm_num)
          (by
            simpa [theorem6FixedPostStages] using hj)
      have hmul :=
        Nat.mul_le_mul_right a hp
      unfold theorem6FixedPostScale
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
          simpa [theorem6FixedPostStages] using hj)
    have hmul :=
      Nat.mul_le_mul_right a hp
    unfold theorem6FixedPostScale
    norm_num at hmul
    calc
      5 * (2 ^ (j + 1) * a + 1)
          ≤ 5 * (131072 * a + 1) :=
        Nat.mul_le_mul_left 5
          (Nat.add_le_add_right hmul 1)
      _ = 655360 * a + 5 := by ring
      _ ≤ n + 1 := hnLabelBase
  · rw [theorem6FixedPostScale_final]
    omega
  · rw [theorem6FixedPostScale_final]
    exact hnFinalRoom
  · rw [theorem6FixedPostScale_four_final]
    omega
  · intro j hj
    unfold theorem6FixedPostScale
    have hp :
        2 ^ (j + 1) ≤ 2 ^ 18 :=
      Nat.pow_le_pow_right (by norm_num)
        (by
          have hj' : j + 1 ≤
              theorem6FixedPostStages + 1 :=
            Nat.add_le_add_right hj 1
          simpa [theorem6FixedPostStages] using hj')
    norm_num at hp
    exact Nat.mul_le_mul_right a hp
  · rw [theorem6FixedPostScale_four_final]
    omega

/-- For all sufficiently large populations, the least critical scale supplies
the complete fixed window. -/
theorem lemma19FixedWindowFacts_of_large
    (n : ℕ)
    (hn : 0 < n)
    (hlarge :
      theorem6FixedCStarSq *
          (theorem6FixedCStarSq + 6) ≤ n) :
    ∃ e,
      Lemma19FixedWindowFacts n
        (theorem6FixedCriticalScale n) e := by
  obtain ⟨aPred, e, haPred, hceil, hexcess⟩ :=
    theorem6FixedCriticalScale_additive_ceiling n hn
  have haLarge :
      theorem6FixedCStarSq + 6 ≤
        theorem6FixedCriticalScale n :=
    theorem6FixedCriticalScale_lower
      n (theorem6FixedCStarSq + 6) hlarge
  exact
    ⟨e, lemma19FixedWindowFacts
      n (theorem6FixedCriticalScale n) e
      hceil hexcess haLarge⟩

end

end Tri

#print axioms Tri.theorem6FixedCriticalScale_spec
#print axioms Tri.theorem6FixedCriticalScale_additive_ceiling
#print axioms Tri.theorem6FixedCriticalScale_lower
#print axioms Tri.lemma19FixedWindowFacts
#print axioms Tri.lemma19FixedWindowFacts_of_large
