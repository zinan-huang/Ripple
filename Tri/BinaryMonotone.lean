/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Chain

/-!
# Stochastic monotonicity of the binary Tri chain

At fixed total population, increasing the current `X` count cannot decrease
the expectation of an increasing terminal observable.  The only nontrivial
adjacent-state condition is that the lower state's up mass plus the upper
state's down mass is at most one.
-/

namespace Tri

open scoped ENNReal

/-- The two crossing reaction fibers of adjacent binary states fit inside the
common physical triple sample space. -/
theorem adjacent_cross_count_le (a b : ℕ) :
    Nat.choose (a + 1) 2 * (b + 2) +
        (a + 2) * Nat.choose (b + 1) 2 ≤
      Nat.choose ((a + 1) + (b + 2)) 3 := by
  have hchoose2 :
      Nat.choose (a + 1) 2 ≤ Nat.choose (a + 2) 2 :=
    Nat.choose_le_choose 2 (by omega)
  have hmul :
      Nat.choose (a + 1) 2 * (b + 1) ≤
        Nat.choose (a + 2) 2 * (b + 1) :=
    Nat.mul_le_mul_right (b + 1) hchoose2
  have hchoose3 :
      Nat.choose (a + 1) 2 ≤ Nat.choose (a + 2) 3 := by
    have hpascal :
        Nat.choose (a + 2) 3 =
          Nat.choose (a + 1) 2 + Nat.choose (a + 1) 3 :=
      Nat.choose_succ_succ (a + 1) 2
    omega
  have hexpand :
      Nat.choose (a + 1) 2 * (b + 2) =
        Nat.choose (a + 1) 2 * (b + 1) +
          Nat.choose (a + 1) 2 := by ring
  have hsplit := choose_three_split (a + 2) (b + 1)
  rw [show (a + 2) + (b + 1) = (a + 1) + (b + 2) by omega] at hsplit
  rw [hexpand]
  omega

/-- The crossing masses of two adjacent interior states sum to at most one. -/
theorem triStep_adjacent_cross_le_one
    (a b : ℕ) (h3 : 3 ≤ (a + 1) + (b + 2)) :
    triStep (a + 1) (b + 2) h3 (a + 2) +
        triStep (a + 2) (b + 1) (by omega) (a + 1) ≤ 1 := by
  rw [triStep_up, triStep_down]
  have htotal :
      (a + 2) + (b + 1) = (a + 1) + (b + 2) := by omega
  rw [htotal, ENNReal.div_add_div_same]
  calc
    _ ≤
        (Nat.choose ((a + 1) + (b + 2)) 3 : ℝ≥0∞) /
          (Nat.choose ((a + 1) + (b + 2)) 3 : ℝ≥0∞) := by
      apply ENNReal.div_le_div_right
      exact_mod_cast adjacent_cross_count_le a b
    _ = 1 := by
      apply ENNReal.div_self
      · exact_mod_cast (choose_three_pos h3).ne'
      · exact ENNReal.natCast_ne_top _

/-- A three-atom law supported one step below another three-atom law is
ordered on increasing observables once their crossing masses fit inside one. -/
theorem adjacent_three_atom_expect_le
    {p0 p1 p2 q0 q1 q2 : ℝ≥0∞}
    (hp : p0 + p1 + p2 = 1)
    (hq : q0 + q1 + q2 = 1)
    (hcross : p2 + q0 ≤ 1)
    (F : ℕ → ℝ≥0∞) (hF : Monotone F) (a : ℕ) :
    p0 * F a + p1 * F (a + 1) + p2 * F (a + 2) ≤
      q0 * F (a + 1) + q1 * F (a + 2) + q2 * F (a + 3) := by
  have hp0 : p0 ≤ 1 := by
    rw [← hp]
    exact le_add_right (le_add_right le_rfl)
  have hp1 : p1 ≤ 1 := by
    rw [← hp]
    calc
      p1 ≤ p0 + p1 := le_add_left le_rfl
      _ ≤ p0 + p1 + p2 := le_add_right le_rfl
  have hp2 : p2 ≤ 1 := by
    rw [← hp]
    exact le_add_left le_rfl
  have hq0 : q0 ≤ 1 := by
    rw [← hq]
    exact le_add_right (le_add_right le_rfl)
  have hp2top : p2 ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top hp2
  have hq0top : q0 ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top hq0
  have hq0le : q0 ≤ p0 + p1 := by
    apply (ENNReal.add_le_add_iff_right hp2top).mp
    calc
      q0 + p2 = p2 + q0 := add_comm _ _
      _ ≤ 1 := hcross
      _ = (p0 + p1) + p2 := hp.symm
  let d : ℝ≥0∞ := (p0 + p1) - q0
  have hp01 : q0 + d = p0 + p1 := by
    exact add_tsub_cancel_of_le hq0le
  have hdq : d + p2 = q1 + q2 := by
    apply (ENNReal.add_right_inj hq0top).mp
    calc
      q0 + (d + p2) = (q0 + d) + p2 := by ring
      _ = (p0 + p1) + p2 := by rw [hp01]
      _ = 1 := hp
      _ = q0 + (q1 + q2) := by rw [← hq]; ring
  calc
    p0 * F a + p1 * F (a + 1) + p2 * F (a + 2) ≤
        p0 * F (a + 1) + p1 * F (a + 1) + p2 * F (a + 2) := by
      gcongr
      exact hF (by omega)
    _ = (p0 + p1) * F (a + 1) + p2 * F (a + 2) := by ring
    _ = (q0 + d) * F (a + 1) + p2 * F (a + 2) := by rw [hp01]
    _ = q0 * F (a + 1) + d * F (a + 1) + p2 * F (a + 2) := by ring
    _ ≤ q0 * F (a + 1) + d * F (a + 2) + p2 * F (a + 2) := by
      gcongr
      exact hF (by omega)
    _ = q0 * F (a + 1) + (d + p2) * F (a + 2) := by ring
    _ = q0 * F (a + 1) + (q1 + q2) * F (a + 2) := by rw [hdq]
    _ = q0 * F (a + 1) + q1 * F (a + 2) + q2 * F (a + 2) := by ring
    _ ≤ q0 * F (a + 1) + q1 * F (a + 2) + q2 * F (a + 3) := by
      gcongr
      exact hF (by omega)

/-- Adjacent interior binary states are stochastically ordered. -/
theorem expect_triStep_adjacent_le
    (a b : ℕ) (h3 : 3 ≤ (a + 1) + (b + 2))
    (F : ℕ → ℝ≥0∞) (hF : Monotone F) :
    expect (triStep (a + 1) (b + 2) h3) F ≤
      expect (triStep (a + 2) (b + 1) (by omega)) F := by
  rw [expect_triStep, expect_triStep]
  exact adjacent_three_atom_expect_le
    (triStep_masses_sum a (b + 2) h3)
    (triStep_masses_sum (a + 1) (b + 1) (by omega))
    (triStep_adjacent_cross_le_one a b h3) F hF a

/-- The expectation of a constant under a probability mass function. -/
@[simp] theorem expect_const (p : PMF ℕ) (r : ℝ≥0∞) :
    expect p (fun _ => r) = r := by
  unfold expect
  rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- Every increasing observable is bounded below by its value at zero. -/
theorem expect_ge_at_zero
    (p : PMF ℕ) (F : ℕ → ℝ≥0∞) (hF : Monotone F) :
    F 0 ≤ expect p F := by
  calc
    F 0 = expect p (fun _ => F 0) := (expect_const p (F 0)).symm
    _ ≤ expect p F := by
      unfold expect
      exact ENNReal.tsum_le_tsum fun z => by
        gcongr
        exact hF (Nat.zero_le z)

/-- From `(a+1,1)`, every possible next `X` count is at most consensus. -/
theorem expect_triStep_one_minor_le_consensus
    (a : ℕ) (h3 : 3 ≤ (a + 1) + 1)
    (F : ℕ → ℝ≥0∞) (hF : Monotone F) :
    expect (triStep (a + 1) 1 h3) F ≤ F (a + 2) := by
  rw [expect_triStep]
  calc
    triStep (a + 1) 1 h3 a * F a +
          triStep (a + 1) 1 h3 (a + 1) * F (a + 1) +
          triStep (a + 1) 1 h3 (a + 2) * F (a + 2) ≤
        triStep (a + 1) 1 h3 a * F (a + 2) +
          triStep (a + 1) 1 h3 (a + 1) * F (a + 2) +
          triStep (a + 1) 1 h3 (a + 2) * F (a + 2) := by
      gcongr
      · exact hF (by omega)
      · exact hF (by omega)
    _ = F (a + 2) := by
      rw [← add_mul, ← add_mul, triStep_masses_sum, one_mul]

/-- The fixed-population binary kernel preserves stochastic order between
adjacent starting counts, including both consensus boundaries. -/
theorem triChain_expect_le_succ
    (n x : ℕ) (F : ℕ → ℝ≥0∞) (hF : Monotone F) :
    expect (triChain n x) F ≤ expect (triChain n (x + 1)) F := by
  by_cases h3 : 3 ≤ n
  · by_cases hxlt : x < n
    · by_cases hx0 : x = 0
      · subst x
        rw [show triChain n 0 = triStep 0 n (by omega) by
          unfold triChain
          rw [dif_pos ⟨h3, Nat.zero_le n⟩]
          congr 1]
        rw [triStep_consensus_Y]
        simp only [expect_pure]
        exact expect_ge_at_zero (triChain n 1) F hF
      · by_cases hlast : x + 1 = n
        · obtain ⟨a, rfl⟩ : ∃ a, x = a + 1 := by
            exact ⟨x - 1, by omega⟩
          have hn : (a + 1) + 1 = n := by omega
          rw [triChain_apply (a := a) (b := 0) hn h3]
          have hcons :
              triChain n ((a + 1) + 1) = PMF.pure ((a + 1) + 1) := by
            rw [hn]
            exact triChain_consensus h3
          rw [hcons, expect_pure]
          simpa [show (a + 1) + 1 = a + 2 by omega] using
            expect_triStep_one_minor_le_consensus a (by omega) F hF
        · obtain ⟨a, rfl⟩ : ∃ a, x = a + 1 := by
            exact ⟨x - 1, by omega⟩
          obtain ⟨b, hb⟩ :
              ∃ b, n = (a + 1) + (b + 2) := by
            exact ⟨n - ((a + 1) + 2), by omega⟩
          rw [triChain_apply
              (a := a) (b := b + 1) (by omega) h3,
            triChain_apply
              (a := a + 1) (b := b) (by omega) h3]
          exact expect_triStep_adjacent_le a b (by omega) F hF
    · have hnx : n ≤ x := by omega
      by_cases hxn : x = n
      · subst x
        rw [triChain_consensus h3]
        have hout : triChain n (n + 1) = PMF.pure (n + 1) := by
          unfold triChain
          rw [dif_neg]
          omega
        rw [hout, expect_pure, expect_pure]
        exact hF (by omega)
      · have hxout : n < x := by omega
        have hout0 : triChain n x = PMF.pure x := by
          unfold triChain
          rw [dif_neg]
          omega
        have hout1 : triChain n (x + 1) = PMF.pure (x + 1) := by
          unfold triChain
          rw [dif_neg]
          omega
        rw [hout0, hout1, expect_pure, expect_pure]
        exact hF (by omega)
  · have hout0 : triChain n x = PMF.pure x := by
      unfold triChain
      rw [dif_neg]
      exact fun h => h3 h.1
    have hout1 : triChain n (x + 1) = PMF.pure (x + 1) := by
      unfold triChain
      rw [dif_neg]
      exact fun h => h3 h.1
    rw [hout0, hout1, expect_pure, expect_pure]
    exact hF (by omega)

/-- Expectations after one binary step are monotone in the starting count. -/
theorem triChain_expect_monotone
    (n : ℕ) (F : ℕ → ℝ≥0∞) (hF : Monotone F) :
    Monotone fun x => expect (triChain n x) F :=
  monotone_nat_of_le_succ fun x => triChain_expect_le_succ n x F hF

/-- Every finite-horizon binary semigroup preserves increasing observables. -/
theorem triChain_iter_expect_monotone
    (n T : ℕ) (F : ℕ → ℝ≥0∞) (hF : Monotone F) :
    Monotone fun x => expect (iter (triChain n) T x) F := by
  induction T with
  | zero =>
      simpa [iter] using hF
  | succ t ih =>
      intro x y hxy
      change
        expect (iter (triChain n) (t + 1) x) F ≤
          expect (iter (triChain n) (t + 1) y) F
      rw [iter_succ, iter_succ, expect_bind, expect_bind]
      exact (triChain_expect_monotone n
        (fun z => expect (iter (triChain n) t z) F) ih) hxy

end Tri

#print axioms Tri.adjacent_cross_count_le
#print axioms Tri.triStep_adjacent_cross_le_one
#print axioms Tri.expect_triStep_adjacent_le
#print axioms Tri.triChain_expect_monotone
#print axioms Tri.triChain_iter_expect_monotone
