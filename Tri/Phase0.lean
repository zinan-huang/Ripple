/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Phase0Interface

/-!
# Phase 0: escape from symmetry

This file proves the phase-0 input for `Theorem 1(a)`.  The proof uses a
single symmetric Lyapunov function on the original interaction chain.  For
population size `n` and signed gap `g`, set

`V(n,g) = (n^2-g^2)/(2n+g^2)`.

It vanishes at consensus, is at least one while the gap is below the required
square-root scale, and contracts by `2n/(2n+1)` in every non-consensus state.
Thus it controls returns to the central region as well as the first escape;
no stopped-chain transfer is needed.
-/

namespace Tri

open scoped ENNReal

set_option exponentiation.threshold 500

/-- The real symmetric phase-0 potential as a function of population size and
signed population gap. -/
noncomputable def phase0PotentialReal (N G : ℝ) : ℝ :=
  (N ^ 2 - G ^ 2) / (2 * N + G ^ 2)

/-- The phase-0 potential on the state space of `triChain`.  `ofReal` makes it
zero automatically above the physical population range. -/
noncomputable def phase0Potential (n x : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (phase0PotentialReal (n : ℝ) (2 * (x : ℝ) - (n : ℝ)))

/-- The contraction factor of the symmetric potential. -/
noncomputable def phase0Factor (n : ℕ) : ℝ≥0∞ :=
  (2 * n : ℝ≥0∞) / (2 * n + 1 : ℝ≥0∞)

/-- Evaluation of the potential at a physical population pair. -/
theorem phase0Potential_pair_toReal (x y : ℕ) (hpos : 0 < x + y) :
    (phase0Potential (x + y) x).toReal =
      phase0PotentialReal ((x : ℝ) + (y : ℝ)) ((x : ℝ) - (y : ℝ)) := by
  rw [phase0Potential, ENNReal.toReal_ofReal]
  · unfold phase0PotentialReal
    push_cast
    congr 2 <;> ring
  · unfold phase0PotentialReal
    push_cast
    have hN : (0 : ℝ) < (x : ℝ) + (y : ℝ) := by exact_mod_cast hpos
    have hnum : (0 : ℝ) ≤ ((x : ℝ) + (y : ℝ)) ^ 2 -
        (2 * (x : ℝ) - ((x : ℝ) + (y : ℝ))) ^ 2 := by
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ (x : ℝ) by positivity)
        (show (0 : ℝ) ≤ (y : ℝ) by positivity)]
    exact div_nonneg hnum (by positivity)

/-- Evaluation at a physical pair whose sum is a separately named population. -/
theorem phase0Potential_toReal_of_add {n x y : ℕ} (hpop : x + y = n)
    (hpos : 0 < n) :
    (phase0Potential n x).toReal =
      phase0PotentialReal (n : ℝ) ((x : ℝ) - (y : ℝ)) := by
  have h := phase0Potential_pair_toReal x y (by omega)
  have hpopR : (x : ℝ) + (y : ℝ) = (n : ℝ) := by exact_mod_cast hpop
  rw [hpop] at h
  rw [hpopR] at h
  exact h

/-- The phase-0 potential is finite at every state. -/
theorem phase0Potential_ne_top (n x : ℕ) : phase0Potential n x ≠ ⊤ := by
  exact ENNReal.ofReal_ne_top

/-- The phase-0 contraction factor is finite. -/
theorem phase0Factor_ne_top (n : ℕ) : phase0Factor n ≠ ⊤ := by
  unfold phase0Factor
  exact ENNReal.div_ne_top
    (ENNReal.mul_ne_top (by norm_num) (ENNReal.natCast_ne_top n)) (by simp)

/-- Real evaluation of the phase-0 contraction factor. -/
theorem phase0Factor_toReal (n : ℕ) :
    (phase0Factor n).toReal = (2 * (n : ℝ)) / (2 * (n : ℝ) + 1) := by
  have hmul : (2 * (n : ℝ≥0∞)) ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) (ENNReal.natCast_ne_top n)
  unfold phase0Factor
  rw [ENNReal.toReal_div, ENNReal.toReal_mul,
    ENNReal.toReal_add hmul (by norm_num), ENNReal.toReal_mul]
  norm_num

/-- The potential vanishes at either consensus and on the inert extension
above the physical population range. -/
theorem phase0Potential_eq_zero_of_boundary {n x : ℕ} (hx : x = 0 ∨ n ≤ x) :
    phase0Potential n x = 0 := by
  unfold phase0Potential
  rw [ENNReal.ofReal_eq_zero]
  unfold phase0PotentialReal
  have hden : (0 : ℝ) ≤ 2 * (n : ℝ) + (2 * (x : ℝ) - (n : ℝ)) ^ 2 := by
    positivity
  apply div_nonpos_of_nonpos_of_nonneg _ hden
  rcases hx with rfl | hx
  · norm_num
  · have hxR : (n : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
    nlinarith [sq_nonneg ((x : ℝ) - (n : ℝ))]

/-- Scalar core of the one-step phase-0 contraction.  The two directional
masses are written in signed-gap coordinates; the stay mass is recovered from
normalization. -/
private theorem phase0_contraction_real
    (N G pDown pStay pUp : ℝ) (hN : 3 ≤ N)
    (hG : G ^ 2 ≤ N ^ 2)
    (hsum : pDown + pStay + pUp = 1)
    (hdown : pDown =
      3 * (N ^ 2 - G ^ 2) * (N - G - 2) /
        (8 * N * (N - 1) * (N - 2)))
    (hup : pUp =
      3 * (N ^ 2 - G ^ 2) * (N + G - 2) /
        (8 * N * (N - 1) * (N - 2))) :
    pDown * phase0PotentialReal N (G - 2) +
        pStay * phase0PotentialReal N G +
        pUp * phase0PotentialReal N (G + 2) ≤
      (2 * N / (2 * N + 1)) * phase0PotentialReal N G := by
  have hN0 : 0 < N := by linarith
  have hN1 : 0 < N - 1 := by linarith
  have hN2 : 0 < N - 2 := by linarith
  have hd0 : 0 < 2 * N + (G - 2) ^ 2 := by positivity
  have hd1 : 0 < 2 * N + G ^ 2 := by positivity
  have hd2 : 0 < 2 * N + (G + 2) ^ 2 := by positivity
  have hf : 0 < 2 * N + 1 := by positivity
  have hstay : pStay = 1 - pDown - pUp := by linarith
  rw [hstay, hdown, hup]
  unfold phase0PotentialReal
  field_simp
  have hsq : 0 ≤ (G ^ 2 - N) ^ 2 := sq_nonneg _
  have htail : 0 ≤ 3 * N ^ 4 + 26 * N ^ 3 - 12 * N ^ 2 - 104 * N - 80 := by
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ N - 3 by linarith)
      (show (0 : ℝ) ≤ 3 * N ^ 3 + 35 * N ^ 2 + 93 * N + 175 by positivity)]
  have hpoly : 0 ≤
      5 * G ^ 4 * N ^ 2 + 18 * G ^ 4 * N + 4 * G ^ 4 -
        10 * G ^ 2 * N ^ 3 + 41 * G ^ 2 * N ^ 2 + 52 * G ^ 2 * N +
        52 * G ^ 2 + 8 * N ^ 4 + 26 * N ^ 3 - 12 * N ^ 2 -
        104 * N - 80 := by
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ 5 * N ^ 2 by positivity) hsq,
      mul_nonneg (show (0 : ℝ) ≤ 18 * N + 4 by positivity) (sq_nonneg (G ^ 2)),
      mul_nonneg (show (0 : ℝ) ≤ 41 * N ^ 2 + 52 * N + 52 by positivity)
        (sq_nonneg G), htail]
  have hprod := mul_nonneg (sub_nonneg.mpr hG) hpoly
  nlinarith [hprod]

/-- The scalar contraction is exactly the one-step contraction of the CRN at
an interior population state. -/
private theorem phase0_step_interior (n a b : ℕ) (h3 : 3 ≤ n)
    (hpop : a + b + 2 = n) :
    expect (triStep (a + 1) (b + 1) (by omega)) (phase0Potential n) ≤
      phase0Factor n * phase0Potential n (a + 1) := by
  let p0 : ℝ≥0∞ := triStep (a + 1) (b + 1) (by omega) a
  let p1 : ℝ≥0∞ := triStep (a + 1) (b + 1) (by omega) (a + 1)
  let p2 : ℝ≥0∞ := triStep (a + 1) (b + 1) (by omega) (a + 2)
  have fp0 : p0 ≠ ⊤ := PMF.apply_ne_top _ _
  have fp1 : p1 ≠ ⊤ := PMF.apply_ne_top _ _
  have fp2 : p2 ≠ ⊤ := PMF.apply_ne_top _ _
  have fv0 : phase0Potential n a ≠ ⊤ := phase0Potential_ne_top n a
  have fv1 : phase0Potential n (a + 1) ≠ ⊤ := phase0Potential_ne_top n (a + 1)
  have fv2 : phase0Potential n (a + 2) ≠ ⊤ := phase0Potential_ne_top n (a + 2)
  have ft0 : p0 * phase0Potential n a ≠ ⊤ := ENNReal.mul_ne_top fp0 fv0
  have ft1 : p1 * phase0Potential n (a + 1) ≠ ⊤ := ENNReal.mul_ne_top fp1 fv1
  have ft2 : p2 * phase0Potential n (a + 2) ≠ ⊤ := ENNReal.mul_ne_top fp2 fv2
  have fleft : p0 * phase0Potential n a + p1 * phase0Potential n (a + 1) +
      p2 * phase0Potential n (a + 2) ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨ft0, ft1⟩, ft2⟩
  have fright : phase0Factor n * phase0Potential n (a + 1) ≠ ⊤ :=
    ENNReal.mul_ne_top (phase0Factor_ne_top n) fv1
  have hsum : p0.toReal + p1.toReal + p2.toReal = 1 := by
    have hm := triStep_masses_sum a (b + 1) (by omega)
    change p0 + p1 + p2 = 1 at hm
    have hr := congrArg ENNReal.toReal hm
    rw [ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨fp0, fp1⟩) fp2,
      ENNReal.toReal_add fp0 fp1, ENNReal.toReal_one] at hr
    exact hr
  have htotal : (a + 1) + (b + 1) = n := by omega
  have hp0raw : p0.toReal =
      (a + 1 : ℝ) * (Nat.choose (b + 1) 2 : ℝ) / (Nat.choose n 3 : ℝ) := by
    dsimp [p0]
    rw [triStep_down, ENNReal.toReal_div, ENNReal.toReal_mul]
    simp only [ENNReal.toReal_natCast]
    rw [htotal]
    push_cast
    rfl
  have hp2raw : p2.toReal =
      (Nat.choose (a + 1) 2 : ℝ) * (b + 1 : ℝ) / (Nat.choose n 3 : ℝ) := by
    dsimp [p2]
    rw [triStep_up, ENNReal.toReal_div, ENNReal.toReal_mul]
    simp only [ENNReal.toReal_natCast]
    rw [htotal]
    push_cast
    rfl
  have hca : (Nat.choose (a + 1) 2 : ℝ) = (a + 1 : ℝ) * (a : ℝ) / 2 := by
    have ha := two_mul_choose_two_succ a
    have haR : (2 : ℝ) * (Nat.choose (a + 1) 2 : ℝ) =
        (a + 1 : ℝ) * (a : ℝ) := by exact_mod_cast ha
    linarith
  have hcb : (Nat.choose (b + 1) 2 : ℝ) = (b + 1 : ℝ) * (b : ℝ) / 2 := by
    have hb := two_mul_choose_two_succ b
    have hbR : (2 : ℝ) * (Nat.choose (b + 1) 2 : ℝ) =
        (b + 1 : ℝ) * (b : ℝ) := by exact_mod_cast hb
    linarith
  have h6c : (6 : ℝ) * (Nat.choose n 3 : ℝ) =
      (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) := by
    have hn := six_mul_choose_three_add_two (a + b)
    rw [hpop] at hn
    have hnR : (6 : ℝ) * (Nat.choose n 3 : ℝ) =
        (n : ℝ) * ((a : ℝ) + (b : ℝ) + 1) * ((a : ℝ) + (b : ℝ)) := by
      exact_mod_cast hn
    rw [hnR]
    have hpopR : (a : ℝ) + (b : ℝ) + 2 = (n : ℝ) := by exact_mod_cast hpop
    have habR : (a : ℝ) + (b : ℝ) = (n : ℝ) - 2 := by linarith
    rw [habR]
    ring
  have hcpos : (0 : ℝ) < (Nat.choose n 3 : ℝ) := by
    exact_mod_cast Nat.choose_pos h3
  have hnR : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h3
  have hG : ((a : ℝ) - (b : ℝ)) ^ 2 ≤ (n : ℝ) ^ 2 := by
    have ha0 : (0 : ℝ) ≤ (a : ℝ) := by positivity
    have hb0 : (0 : ℝ) ≤ (b : ℝ) := by positivity
    have hpopR : (a : ℝ) + (b : ℝ) + 2 = (n : ℝ) := by exact_mod_cast hpop
    nlinarith [mul_nonneg ha0 hb0]
  have hgapSquare : (n : ℝ) ^ 2 - ((a : ℝ) - (b : ℝ)) ^ 2 =
      4 * ((a : ℝ) + 1) * ((b : ℝ) + 1) := by
    have hpopR : (a : ℝ) + (b : ℝ) + 2 = (n : ℝ) := by exact_mod_cast hpop
    nlinarith
  have hgapDown : (n : ℝ) - ((a : ℝ) - (b : ℝ)) - 2 = 2 * (b : ℝ) := by
    have hpopR : (a : ℝ) + (b : ℝ) + 2 = (n : ℝ) := by exact_mod_cast hpop
    linarith
  have hgapUp : (n : ℝ) + ((a : ℝ) - (b : ℝ)) - 2 = 2 * (a : ℝ) := by
    have hpopR : (a : ℝ) + (b : ℝ) + 2 = (n : ℝ) := by exact_mod_cast hpop
    linarith
  have hp0 : p0.toReal =
      3 * ((n : ℝ) ^ 2 - ((a : ℝ) - (b : ℝ)) ^ 2) *
          ((n : ℝ) - ((a : ℝ) - (b : ℝ)) - 2) /
        (8 * (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2)) := by
    rw [hp0raw, hcb, hgapSquare, hgapDown]
    have hcn : (Nat.choose n 3 : ℝ) = (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) / 6 := by
      linarith [h6c]
    have hn0 : (n : ℝ) ≠ 0 := (by linarith : (0 : ℝ) < (n : ℝ)).ne'
    have hn1 : (n : ℝ) - 1 ≠ 0 := (by linarith : (0 : ℝ) < (n : ℝ) - 1).ne'
    have hn2 : (n : ℝ) - 2 ≠ 0 := (by linarith : (0 : ℝ) < (n : ℝ) - 2).ne'
    rw [hcn]
    field_simp
    ring
  have hp2 : p2.toReal =
      3 * ((n : ℝ) ^ 2 - ((a : ℝ) - (b : ℝ)) ^ 2) *
          ((n : ℝ) + ((a : ℝ) - (b : ℝ)) - 2) /
        (8 * (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2)) := by
    rw [hp2raw, hca, hgapSquare, hgapUp]
    have hcn : (Nat.choose n 3 : ℝ) = (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) / 6 := by
      linarith [h6c]
    have hn0 : (n : ℝ) ≠ 0 := (by linarith : (0 : ℝ) < (n : ℝ)).ne'
    have hn1 : (n : ℝ) - 1 ≠ 0 := (by linarith : (0 : ℝ) < (n : ℝ) - 1).ne'
    have hn2 : (n : ℝ) - 2 ≠ 0 := (by linarith : (0 : ℝ) < (n : ℝ) - 2).ne'
    rw [hcn]
    field_simp
    ring
  have hv0 : (phase0Potential n a).toReal =
      phase0PotentialReal (n : ℝ) ((a : ℝ) - (b : ℝ) - 2) := by
    have h := phase0Potential_toReal_of_add (n := n) (x := a) (y := b + 2)
      (by omega) (by omega)
    convert h using 1 <;> push_cast <;> ring
  have hv1 : (phase0Potential n (a + 1)).toReal =
      phase0PotentialReal (n : ℝ) ((a : ℝ) - (b : ℝ)) := by
    have h := phase0Potential_toReal_of_add (n := n) (x := a + 1) (y := b + 1)
      (by omega) (by omega)
    convert h using 1 <;> push_cast <;> ring
  have hv2 : (phase0Potential n (a + 2)).toReal =
      phase0PotentialReal (n : ℝ) ((a : ℝ) - (b : ℝ) + 2) := by
    have h := phase0Potential_toReal_of_add (n := n) (x := a + 2) (y := b)
      (by omega) (by omega)
    convert h using 1 <;> push_cast <;> ring
  rw [expect_triStep]
  change p0 * phase0Potential n a + p1 * phase0Potential n (a + 1) +
      p2 * phase0Potential n (a + 2) ≤ phase0Factor n * phase0Potential n (a + 1)
  rw [← ENNReal.toReal_le_toReal fleft fright]
  rw [ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨ft0, ft1⟩) ft2,
    ENNReal.toReal_add ft0 ft1, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_mul, ENNReal.toReal_mul, phase0Factor_toReal, hv0, hv1, hv2]
  exact phase0_contraction_real (n : ℝ) ((a : ℝ) - (b : ℝ))
    p0.toReal p1.toReal p2.toReal hnR hG hsum hp0 hp2

/-- **One-step contraction at every state.**  Interior states contract by
`phase0Factor` (via `phase0_step_interior`); at the absorbing boundary the
potential already vanishes. -/
theorem phase0_step (n : ℕ) (h3 : 3 ≤ n) (x : ℕ) :
    expect (triChain n x) (phase0Potential n) ≤
      phase0Factor n * phase0Potential n x := by
  rcases Nat.eq_zero_or_pos x with rfl | hxpos
  · have hz : phase0Potential n 0 = 0 :=
      phase0Potential_eq_zero_of_boundary (Or.inl rfl)
    have hc : triChain n 0 = PMF.pure 0 := by
      unfold triChain
      rw [dif_pos ⟨h3, Nat.zero_le n⟩]
      exact triStep_consensus_Y n (by omega)
    rw [hc, expect_pure, hz]
    simp
  · rcases Nat.lt_or_ge x n with hxn | hxn
    · obtain ⟨a, rfl⟩ : ∃ a, x = a + 1 := ⟨x - 1, by omega⟩
      obtain ⟨b, hb⟩ : ∃ b, a + b + 2 = n := ⟨n - (a + 2), by omega⟩
      rw [triChain_apply hb h3]
      exact phase0_step_interior n a b h3 hb
    · have hz : phase0Potential n x = 0 :=
        phase0Potential_eq_zero_of_boundary (Or.inr hxn)
      have hc : triChain n x = PMF.pure x := by
        rcases Nat.eq_or_lt_of_le hxn with heq | hlt
        · rw [← heq]; exact triChain_consensus h3
        · unfold triChain; rw [dif_neg (by omega)]
      rw [hc, expect_pure, hz]
      simp

/-- **Geometric decay of the phase-0 potential.**  Iterating the one-step
contraction, the expected potential after `T` steps is at most
`phase0Factor n ^ T` times its initial value. -/
theorem phase0_expect_iter (n : ℕ) (h3 : 3 ≤ n) (T x₀ : ℕ) :
    expect (iter (triChain n) T x₀) (phase0Potential n) ≤
      phase0Factor n ^ T * phase0Potential n x₀ :=
  expect_iter_le (triChain n) (phase0Potential n) (phase0Factor n)
    (phase0_step n h3) T x₀

/-- A physical state that is **not** a phase-0 seed has its signed gap-squared
strictly below the threshold `S = γ n lg n`.  The witness is the exact gap in
whichever direction the majority lies. -/
theorem phase0_gap_lt (n γ x : ℕ) (hx : x ≤ n) (hns : ¬ Phase0Seed n γ x) :
    (2 * (x : ℝ) - (n : ℝ)) ^ 2 < ((γ * n * Nat.log 2 n : ℕ) : ℝ) := by
  have hnotor : ¬ (HasXInitialGap n γ x ∨ HasYInitialGap n γ x) :=
    fun h => hns ⟨hx, h⟩
  have hnx : ¬ HasXInitialGap n γ x := fun h => hnotor (Or.inl h)
  have hny : ¬ HasYInitialGap n γ x := fun h => hnotor (Or.inr h)
  rcases Nat.lt_or_ge (2 * x) n with hlt | hle
  · obtain ⟨k, hk⟩ : ∃ k, n = 2 * x + k := ⟨n - 2 * x, by omega⟩
    have hgap : ¬ (γ * n * Nat.log 2 n ≤ k ^ 2) := fun hge => hny ⟨k, by omega, hge⟩
    have hnat : k ^ 2 < γ * n * Nat.log 2 n := Nat.lt_of_not_le hgap
    have hkR : 2 * (x : ℝ) - (n : ℝ) = -(k : ℝ) := by
      have : (n : ℝ) = 2 * (x : ℝ) + (k : ℝ) := by exact_mod_cast hk
      linarith
    rw [hkR, neg_sq]
    exact_mod_cast hnat
  · obtain ⟨k, hk⟩ : ∃ k, 2 * x = n + k := ⟨2 * x - n, by omega⟩
    have hgap : ¬ (γ * n * Nat.log 2 n ≤ k ^ 2) := fun hge => hnx ⟨k, by omega, hge⟩
    have hnat : k ^ 2 < γ * n * Nat.log 2 n := Nat.lt_of_not_le hgap
    have hkR : 2 * (x : ℝ) - (n : ℝ) = (k : ℝ) := by
      have : (2 * x : ℝ) = (n : ℝ) + (k : ℝ) := by exact_mod_cast hk
      linarith
    rw [hkR]
    exact_mod_cast hnat

/-- **Threshold bound.**  At a non-seed physical state the potential is at least
`θ = (n²−S)/(2n+S)`, because the potential is antitone in the gap-squared and the
gap-squared is below `S`.  This is the set over which Markov's inequality acts. -/
theorem phase0_threshold (n γ x : ℕ) (h3 : 3 ≤ n) (hx : x ≤ n)
    (hns : ¬ Phase0Seed n γ x) :
    ENNReal.ofReal
        (((n : ℝ) ^ 2 - ((γ * n * Nat.log 2 n : ℕ) : ℝ)) /
          (2 * (n : ℝ) + ((γ * n * Nat.log 2 n : ℕ) : ℝ))) ≤ phase0Potential n x := by
  have hglt := phase0_gap_lt n γ x hx hns
  have hnR : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h3
  have hSpos : (0 : ℝ) ≤ ((γ * n * Nat.log 2 n : ℕ) : ℝ) := by positivity
  unfold phase0Potential phase0PotentialReal
  apply ENNReal.ofReal_le_ofReal
  have hd1 : (0 : ℝ) < 2 * (n : ℝ) + ((γ * n * Nat.log 2 n : ℕ) : ℝ) := by linarith
  have hd2 : (0 : ℝ) < 2 * (n : ℝ) + (2 * (x : ℝ) - (n : ℝ)) ^ 2 := by
    nlinarith [sq_nonneg (2 * (x : ℝ) - (n : ℝ)), hnR]
  rw [div_le_div_iff₀ hd1 hd2]
  nlinarith [hglt, sq_nonneg (2 * (x : ℝ) - (n : ℝ)), hnR]

/-- **Markov tail bound for phase 0.**  The mass off the seed set after `T`
steps is at most the geometrically decayed initial potential divided by the
threshold `θ`.  Combines the pointwise threshold estimate, the support invariant
(states above `n` carry no mass), Markov's inequality and the geometric decay. -/
theorem phase0_reaches_bound (n γ T s : ℕ) (h3 : 3 ≤ n) (hs : s ≤ n)
    (hSlt : ((γ * n * Nat.log 2 n : ℕ) : ℝ) < (n : ℝ) ^ 2) :
    ∑' z, (if Phase0Seed n γ z then 0 else iter (triChain n) T s z) ≤
      phase0Factor n ^ T * phase0Potential n s /
        ENNReal.ofReal
          (((n : ℝ) ^ 2 - ((γ * n * Nat.log 2 n : ℕ) : ℝ)) /
            (2 * (n : ℝ) + ((γ * n * Nat.log 2 n : ℕ) : ℝ))) := by
  set θ : ℝ≥0∞ := ENNReal.ofReal
      (((n : ℝ) ^ 2 - ((γ * n * Nat.log 2 n : ℕ) : ℝ)) /
        (2 * (n : ℝ) + ((γ * n * Nat.log 2 n : ℕ) : ℝ))) with hθdef
  have hnR : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h3
  have hSpos : (0 : ℝ) ≤ ((γ * n * Nat.log 2 n : ℕ) : ℝ) := by positivity
  have hθrealpos : 0 < ((n : ℝ) ^ 2 - ((γ * n * Nat.log 2 n : ℕ) : ℝ)) /
      (2 * (n : ℝ) + ((γ * n * Nat.log 2 n : ℕ) : ℝ)) :=
    div_pos (by linarith) (by linarith)
  have hθne : θ ≠ 0 := by rw [hθdef]; exact (ENNReal.ofReal_pos.mpr hθrealpos).ne'
  have hθtop : θ ≠ ⊤ := by rw [hθdef]; exact ENNReal.ofReal_ne_top
  calc ∑' z, (if Phase0Seed n γ z then 0 else iter (triChain n) T s z)
      ≤ ∑' z, (if θ ≤ phase0Potential n z then iter (triChain n) T s z else 0) := by
        apply ENNReal.tsum_le_tsum
        intro z
        by_cases hseed : Phase0Seed n γ z
        · simp [hseed]
        · rw [if_neg hseed]
          by_cases hzn : z ≤ n
          · rw [if_pos (by rw [hθdef]; exact phase0_threshold n γ z h3 hzn hseed)]
          · rw [iter_triChain_eq_zero_above n T s z h3 hs (by omega)]
            simp
    _ ≤ expect (iter (triChain n) T s) (phase0Potential n) / θ :=
        markov_div (iter (triChain n) T s) (phase0Potential n) θ hθne hθtop
    _ ≤ phase0Factor n ^ T * phase0Potential n s / θ :=
        ENNReal.div_le_div_right (phase0_expect_iter n h3 T s) θ

/-- **The rpow closure.**  With horizon `210 γ n lg n` the geometrically decayed,
Markov-divided initial potential meets the target power law `n⁻¹^(γ/100)`.  The
contraction factor gives `exp(-Ω(γ lg n))`; the coarse bounds `V(s) ≤ n/2` and
`θ ≥ 5/2` absorb the remaining polynomial factors. -/
theorem phase0_final_bound (n γ s : ℕ) (hn : 2 ^ 420 ≤ n) (hγ : 1 ≤ γ)
    (hsize : 6 * γ * Nat.log 2 n ≤ n) (hs : s ≤ n) :
    phase0Factor n ^ (210 * γ * n * Nat.log 2 n) * phase0Potential n s /
        ENNReal.ofReal
          (((n : ℝ) ^ 2 - ((γ * n * Nat.log 2 n : ℕ) : ℝ)) /
            (2 * (n : ℝ) + ((γ * n * Nat.log 2 n : ℕ) : ℝ))) ≤ phase0Error n γ := by
  have h3 : (3 : ℕ) ≤ n :=
    le_trans (by norm_num) (le_trans (Nat.pow_le_pow_right (by norm_num) (by norm_num : 2 ≤ 420)) hn)
  have hnpos : 0 < n := by omega
  have hnR12 : (12 : ℝ) ≤ (n : ℝ) := by
    have h2 : (12 : ℕ) ≤ 2 ^ 420 :=
      le_trans (by norm_num : (12 : ℕ) ≤ 2 ^ 4) (Nat.pow_le_pow_right (by norm_num) (by norm_num))
    exact_mod_cast (le_trans h2 hn)
  have hA : phase0Potential n s ≤ ENNReal.ofReal ((n : ℝ) / 2) := by
    unfold phase0Potential phase0PotentialReal
    apply ENNReal.ofReal_le_ofReal
    have hd : (0 : ℝ) < 2 * (n : ℝ) + (2 * (s : ℝ) - (n : ℝ)) ^ 2 := by
      nlinarith [sq_nonneg (2 * (s : ℝ) - (n : ℝ)), hnR12]
    rw [div_le_iff₀ hd]; nlinarith [sq_nonneg (2 * (s : ℝ) - (n : ℝ)), hnR12]
  have hB : ENNReal.ofReal (5 / 2 : ℝ) ≤ ENNReal.ofReal
      (((n : ℝ) ^ 2 - ((γ * n * Nat.log 2 n : ℕ) : ℝ)) /
        (2 * (n : ℝ) + ((γ * n * Nat.log 2 n : ℕ) : ℝ))) := by
    apply ENNReal.ofReal_le_ofReal
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
    have h6 : (6 : ℝ) * (γ : ℝ) * (Nat.log 2 n : ℝ) ≤ (n : ℝ) := by exact_mod_cast hsize
    have hScast : ((γ * n * Nat.log 2 n : ℕ) : ℝ) = (γ : ℝ) * (n : ℝ) * (Nat.log 2 n : ℝ) := by
      push_cast; ring
    have hSle : ((γ * n * Nat.log 2 n : ℕ) : ℝ) ≤ (n : ℝ) ^ 2 / 6 := by
      rw [hScast]; nlinarith [mul_le_mul_of_nonneg_right h6 hn0, hn0]
    have hSpos : (0 : ℝ) ≤ ((γ * n * Nat.log 2 n : ℕ) : ℝ) := by positivity
    have hd : (0 : ℝ) < 2 * (n : ℝ) + ((γ * n * Nat.log 2 n : ℕ) : ℝ) := by nlinarith
    rw [le_div_iff₀ hd]; nlinarith [hSle, hSpos, hnR12]
  set θ : ℝ≥0∞ := ENNReal.ofReal
      (((n : ℝ) ^ 2 - ((γ * n * Nat.log 2 n : ℕ) : ℝ)) /
        (2 * (n : ℝ) + ((γ * n * Nat.log 2 n : ℕ) : ℝ))) with hθdef
  set A : ℝ≥0∞ := phase0Factor n ^ (210 * γ * n * Nat.log 2 n) with hAdef
  have hinv : θ⁻¹ ≤ (ENNReal.ofReal (5 / 2 : ℝ))⁻¹ := ENNReal.inv_le_inv.mpr hB
  have hC : A * phase0Potential n s / θ ≤ A * ENNReal.ofReal ((n : ℝ) / 5) := by
    have hstep : A * phase0Potential n s / θ
        ≤ A * ENNReal.ofReal ((n : ℝ) / 2) * (ENNReal.ofReal (5 / 2 : ℝ))⁻¹ := by
      rw [ENNReal.div_eq_inv_mul]
      calc θ⁻¹ * (A * phase0Potential n s)
            ≤ (ENNReal.ofReal (5 / 2 : ℝ))⁻¹ * (A * ENNReal.ofReal ((n : ℝ) / 2)) :=
              mul_le_mul' hinv (mul_le_mul' le_rfl hA)
        _ = A * ENNReal.ofReal ((n : ℝ) / 2) * (ENNReal.ofReal (5 / 2 : ℝ))⁻¹ := by ring
    refine le_trans hstep ?_
    have hcollapse : ENNReal.ofReal ((n : ℝ) / 2) * (ENNReal.ofReal (5 / 2 : ℝ))⁻¹
        = ENNReal.ofReal ((n : ℝ) / 5) := by
      rw [← ENNReal.ofReal_inv_of_pos (by norm_num), ← ENNReal.ofReal_mul (by positivity)]
      congr 1; ring
    rw [mul_assoc, hcollapse]
  have hD : A ≤ ENNReal.ofReal (Real.exp (-((1 + (γ : ℝ) / 100) * Real.log n - Real.log 5))) := by
    have hpf : phase0Factor n = ((2 * n : ℕ) : ℝ≥0∞) / ((2 * n + 1 : ℕ) : ℝ≥0∞) := by
      unfold phase0Factor; push_cast; rfl
    rw [hAdef, hpf]
    refine ratio_pow_le_ofReal_exp (2 * n + 1) (2 * n) (210 * γ * n * Nat.log 2 n)
      ((1 + (γ : ℝ) / 100) * Real.log n - Real.log 5) (by omega) (by omega) ?_
    have hnR1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnpos
    have hL : 420 ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by norm_num) hn
    have hLR : (1 : ℝ) ≤ (Nat.log 2 n : ℝ) := by exact_mod_cast (le_trans (by norm_num) hL)
    have hγR : (1 : ℝ) ≤ (γ : ℝ) := by exact_mod_cast hγ
    have hlog2u : Real.log 2 ≤ 1 := le_of_lt (lt_trans Real.log_two_lt_d9 (by norm_num))
    have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have hlogn : Real.log n ≤ ((Nat.log 2 n : ℝ) + 1) * Real.log 2 := by
      have hup : n < 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
      have hlt : Real.log n < Real.log (2 ^ (Nat.log 2 n + 1)) :=
        Real.log_lt_log (by exact_mod_cast hnpos) (by exact_mod_cast hup)
      rw [Real.log_pow] at hlt; push_cast at hlt; linarith
    have hlognpos : (0 : ℝ) ≤ Real.log n := Real.log_nonneg hnR1
    have hlog5 : (0 : ℝ) ≤ Real.log 5 := le_of_lt (Real.log_pos (by norm_num))
    have hlogn2 : Real.log n ≤ 2 * (Nat.log 2 n : ℝ) := by nlinarith [hlogn, hlog2u, hLR, hlog2pos]
    have h_g : (1 : ℝ) + (γ : ℝ) / 100 ≤ 2 * (γ : ℝ) := by nlinarith [hγR]
    have hab : ((2 * n + 1 : ℕ) : ℝ) - ((2 * n : ℕ) : ℝ) = 1 := by push_cast; ring
    have hden : (0 : ℝ) < ((2 * n + 1 : ℕ) : ℝ) := by positivity
    have h2n1 : ((2 * n + 1 : ℕ) : ℝ) ≤ 3 * (n : ℝ) := by push_cast; linarith
    have hTcast : ((210 * γ * n * Nat.log 2 n : ℕ) : ℝ)
        = 210 * (γ : ℝ) * (n : ℝ) * (Nat.log 2 n : ℝ) := by push_cast; ring
    rw [hab, mul_one, le_div_iff₀ hden, hTcast]
    have hstep1 : (1 + (γ : ℝ) / 100) * Real.log n ≤ (2 * (γ : ℝ)) * (2 * (Nat.log 2 n : ℝ)) :=
      mul_le_mul h_g hlogn2 hlognpos (by positivity)
    have hstep2 : (1 + (γ : ℝ) / 100) * Real.log n * ((2 * n + 1 : ℕ) : ℝ)
        ≤ (2 * (γ : ℝ)) * (2 * (Nat.log 2 n : ℝ)) * (3 * (n : ℝ)) :=
      mul_le_mul hstep1 h2n1 (by positivity) (by positivity)
    have hlog5den : (0 : ℝ) ≤ Real.log 5 * ((2 * n + 1 : ℕ) : ℝ) := mul_nonneg hlog5 hden.le
    nlinarith [hstep2, hlog5den,
      (by positivity : (0 : ℝ) ≤ (γ : ℝ) * (n : ℝ) * (Nat.log 2 n : ℝ))]
  have hF : ENNReal.ofReal (Real.exp (-((1 + (γ : ℝ) / 100) * Real.log n - Real.log 5))) *
      ENNReal.ofReal ((n : ℝ) / 5) ≤ phase0Error n γ := by
    have hnposR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
    have hrpow : phase0Error n γ = ENNReal.ofReal ((n : ℝ) ^ (-((1 / 100 : ℝ) * (γ : ℝ)))) := by
      unfold phase0Error
      rw [ENNReal.inv_rpow, ← ENNReal.ofReal_natCast n, ENNReal.ofReal_rpow_of_pos hnposR,
        ← ENNReal.ofReal_inv_of_pos (by positivity), Real.rpow_neg (by positivity)]
    rw [hrpow, ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    rw [Real.rpow_def_of_pos hnposR]
    rw [show (n : ℝ) / 5 = Real.exp (Real.log n - Real.log 5) by
      rw [← Real.log_div (by exact_mod_cast hnpos.ne') (by norm_num), Real.exp_log (by positivity)]]
    rw [← Real.exp_add]
    apply le_of_eq; congr 1; ring
  calc A * phase0Potential n s / θ
      ≤ A * ENNReal.ofReal ((n : ℝ) / 5) := hC
    _ ≤ ENNReal.ofReal (Real.exp (-((1 + (γ : ℝ) / 100) * Real.log n - Real.log 5))) *
          ENNReal.ofReal ((n : ℝ) / 5) := mul_le_mul_right' hD _
    _ ≤ phase0Error n γ := hF

/-- **The phase-0 interface is inhabited.**  With `C₀ = 210`, from every physical
start the tri-molecular CRN reaches a square-root gap in either direction within
`210 γ n lg n` interactions, off-target mass at most `n⁻¹^(γ/100)`. -/
theorem exists_phase0Hyp : ∃ C₀, Phase0Hyp C₀ :=
  ⟨210, {
    hC₀ := by norm_num
    reaches := by
      intro n γ hn hγ hsize s hs
      have h3 : (3 : ℕ) ≤ n :=
        le_trans (by norm_num)
          (le_trans (Nat.pow_le_pow_right (by norm_num) (by norm_num : 2 ≤ 420)) hn)
      have hnpos : 0 < n := by omega
      have hSlt : ((γ * n * Nat.log 2 n : ℕ) : ℝ) < (n : ℝ) ^ 2 := by
        have h6 : (6 : ℝ) * (γ : ℝ) * (Nat.log 2 n : ℝ) ≤ (n : ℝ) := by exact_mod_cast hsize
        have hScast : ((γ * n * Nat.log 2 n : ℕ) : ℝ) = (γ : ℝ) * (n : ℝ) * (Nat.log 2 n : ℝ) := by
          push_cast; ring
        have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
        have hnposR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
        rw [hScast]; nlinarith [mul_le_mul_of_nonneg_right h6 hn0, hnposR, mul_pos hnposR hnposR]
      exact le_trans (phase0_reaches_bound n γ (210 * γ * n * Nat.log 2 n) s h3 hs hSlt)
        (phase0_final_bound n γ s hn hγ hsize hs) }⟩

end Tri
