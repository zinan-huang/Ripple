/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.BinaryMonotone
import Tri.PaperLemma6

/-!
# Monotonicity of the relaxed productive chain

This module proves stochastic monotonicity in the current `X` count for the
relaxed chain conditioned on productive reactions.  Positivity of the firing
rate excludes the degenerate one-minority state where the productive clock
does not ring.
-/

namespace Tri

open scoped ENNReal NNReal

/-- The adjacent raw productive weights satisfy the cross-product inequality
needed to compare their conditional up probabilities. -/
theorem relaxedProductive_count_adjacent_cross (a b : ℕ) :
    (Nat.choose (a + 1) 2 * (b + 2)) *
        ((a + 2) * Nat.choose (b + 1) 2) ≤
      (Nat.choose (a + 2) 2 * (b + 1)) *
        ((a + 1) * Nat.choose (b + 2) 2) := by
  have ha := two_mul_choose_two_succ a
  have ha1 := two_mul_choose_two_succ (a + 1)
  have hb := two_mul_choose_two_succ b
  have hb1 := two_mul_choose_two_succ (b + 1)
  have hab : a * b ≤ (a + 1) * (b + 1) := by
    nlinarith
  have hfour :
      4 *
          ((Nat.choose (a + 1) 2 * (b + 2)) *
            ((a + 2) * Nat.choose (b + 1) 2)) ≤
        4 *
          ((Nat.choose (a + 2) 2 * (b + 1)) *
            ((a + 1) * Nat.choose (b + 2) 2)) := by
    calc
      4 *
            ((Nat.choose (a + 1) 2 * (b + 2)) *
              ((a + 2) * Nat.choose (b + 1) 2)) =
          (2 * Nat.choose (a + 1) 2) *
            (2 * Nat.choose (b + 1) 2) *
            (b + 2) * (a + 2) := by ring
      _ = ((a + 1) * (a + 2) * (b + 1) * (b + 2)) *
            (a * b) := by rw [ha, hb]; ring
      _ ≤ ((a + 1) * (a + 2) * (b + 1) * (b + 2)) *
            ((a + 1) * (b + 1)) :=
        Nat.mul_le_mul_left _ hab
      _ = (2 * Nat.choose (a + 2) 2) *
            (2 * Nat.choose (b + 2) 2) *
            (b + 1) * (a + 1) := by rw [ha1, hb1]; ring
      _ = 4 *
          ((Nat.choose (a + 2) 2 * (b + 1)) *
            ((a + 1) * Nat.choose (b + 2) 2)) := by ring
  exact Nat.le_of_mul_le_mul_left hfour (by norm_num)

theorem relaxedProductiveTriStep_adjacent_cross_mul_le
    (r : RelaxedRate) (a b : ℕ)
    (h : 3 ≤ (a + 1) + (b + 2)) :
    relaxedTriStep r (a + 1) (b + 2) h (a + 2) *
        relaxedTriStep r (a + 2) (b + 1) (by omega) (a + 1) ≤
      relaxedTriStep r (a + 2) (b + 1) (by omega) (a + 3) *
        relaxedTriStep r (a + 1) (b + 2) h a := by
  rw [relaxedTriStep_up, relaxedTriStep_down,
    relaxedTriStep_up, relaxedTriStep_down]
  rw [show a + 1 + (b + 2) = a + b + 3 by omega,
    show a + 2 + (b + 1) = a + b + 3 by omega]
  simp only [div_eq_mul_inv]
  have hc :
      (↑(Nat.choose (a + 1) 2 * (b + 2)) : ℝ≥0∞) *
          ↑((a + 2) * Nat.choose (b + 1) 2) ≤
        (↑(Nat.choose (a + 2) 2 * (b + 1)) : ℝ≥0∞) *
          ↑((a + 1) * Nat.choose (b + 2) 2) := by
    exact_mod_cast relaxedProductive_count_adjacent_cross a b
  calc
    _ = (↑r.fire *
          (↑(Nat.choose (a + b + 3) 3) : ℝ≥0∞)⁻¹ *
          (↑(Nat.choose (a + b + 3) 3) : ℝ≥0∞)⁻¹) *
        ((↑(Nat.choose (a + 1) 2 * (b + 2)) : ℝ≥0∞) *
          ↑((a + 2) * Nat.choose (b + 1) 2)) := by
      push_cast
      ring
    _ ≤ (↑r.fire *
          (↑(Nat.choose (a + b + 3) 3) : ℝ≥0∞)⁻¹ *
          (↑(Nat.choose (a + b + 3) 3) : ℝ≥0∞)⁻¹) *
        ((↑(Nat.choose (a + 2) 2 * (b + 1)) : ℝ≥0∞) *
          ↑((a + 1) * Nat.choose (b + 2) 2)) :=
      by
        simpa [mul_comm] using
          mul_le_mul_right hc
            (↑r.fire *
              (↑(Nat.choose (a + b + 3) 3) : ℝ≥0∞)⁻¹ *
              (↑(Nat.choose (a + b + 3) 3) : ℝ≥0∞)⁻¹)
    _ = _ := by
      push_cast
      ring

/-- The conditional up probability is ordered between adjacent interior
states with the same population. -/
theorem relaxedProductiveTriInterior_adjacent_up_le
    (r : RelaxedRate) (a b : ℕ)
    (h : 3 ≤ (a + 1) + (b + 2))
    (hprod₀ :
      relaxedTriStep r (a + 1) (b + 2) h a +
          relaxedTriStep r (a + 1) (b + 2) h (a + 2) ≠ 0)
    (hprod₁ :
      relaxedTriStep r (a + 2) (b + 1) (by omega) (a + 1) +
          relaxedTriStep r (a + 2) (b + 1) (by omega) (a + 3) ≠ 0) :
    relaxedTriStep r (a + 1) (b + 2) h (a + 2) /
          (relaxedTriStep r (a + 1) (b + 2) h a +
            relaxedTriStep r (a + 1) (b + 2) h (a + 2)) ≤
      relaxedTriStep r (a + 2) (b + 1) (by omega) (a + 3) /
          (relaxedTriStep r (a + 2) (b + 1) (by omega) (a + 1) +
            relaxedTriStep r (a + 2) (b + 1) (by omega) (a + 3)) := by
  let d₀ := relaxedTriStep r (a + 1) (b + 2) h a
  let u₀ := relaxedTriStep r (a + 1) (b + 2) h (a + 2)
  let d₁ := relaxedTriStep r (a + 2) (b + 1) (by omega) (a + 1)
  let u₁ := relaxedTriStep r (a + 2) (b + 1) (by omega) (a + 3)
  have htop₀ : d₀ + u₀ ≠ ⊤ :=
    ENNReal.add_ne_top.mpr
      ⟨PMF.apply_ne_top _ _, PMF.apply_ne_top _ _⟩
  have htop₁ : d₁ + u₁ ≠ ⊤ :=
    ENNReal.add_ne_top.mpr
      ⟨PMF.apply_ne_top _ _, PMF.apply_ne_top _ _⟩
  change u₀ / (d₀ + u₀) ≤ u₁ / (d₁ + u₁)
  rw [ENNReal.le_div_iff_mul_le (Or.inl (by simpa [d₁, u₁] using hprod₁))
      (Or.inl htop₁)]
  rw [show u₀ / (d₀ + u₀) * (d₁ + u₁) =
      (u₀ * (d₁ + u₁)) / (d₀ + u₀) by
    simp only [div_eq_mul_inv]
    ring]
  rw [ENNReal.div_le_iff_le_mul (Or.inl (by simpa [d₀, u₀] using hprod₀))
      (Or.inl htop₀)]
  have hcross : u₀ * d₁ ≤ u₁ * d₀ := by
    exact relaxedProductiveTriStep_adjacent_cross_mul_le r a b h
  calc
    u₀ * (d₁ + u₁) = u₀ * d₁ + u₀ * u₁ := by ring
    _ ≤ u₁ * d₀ + u₀ * u₁ := by gcongr
    _ = u₁ * (d₀ + u₀) := by ring

private theorem two_point_test
    {d₀ u₀ d₁ u₁ vlo vhi : ℝ≥0∞}
    (hsum₀ : d₀ + u₀ = 1)
    (hsum₁ : d₁ + u₁ = 1)
    (hup : u₀ ≤ u₁)
    (hval : vlo ≤ vhi) :
    d₀ * vlo + u₀ * vhi ≤
      d₁ * vlo + u₁ * vhi := by
  let e : ℝ≥0∞ := u₁ - u₀
  have huadd : u₀ + e = u₁ :=
    add_tsub_cancel_of_le hup
  have hu₀one : u₀ ≤ 1 := by
    rw [← hsum₀]
    exact le_add_left le_rfl
  have hu₀top : u₀ ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top hu₀one
  have hbalance : (d₁ + e) + u₀ = d₀ + u₀ := by
    calc
      (d₁ + e) + u₀ = d₁ + (u₀ + e) := by ring
      _ = d₁ + u₁ := by rw [huadd]
      _ = 1 := hsum₁
      _ = d₀ + u₀ := hsum₀.symm
  have hd : d₁ + e = d₀ := by
    have hbalance' : u₀ + (d₁ + e) = u₀ + d₀ := by
      rw [add_comm u₀ (d₁ + e), add_comm u₀ d₀]
      exact hbalance
    exact (ENNReal.add_right_inj hu₀top).mp hbalance'
  calc
    d₀ * vlo + u₀ * vhi =
        (d₁ + e) * vlo + u₀ * vhi := by rw [hd]
    _ = d₁ * vlo + e * vlo + u₀ * vhi := by ring
    _ ≤ d₁ * vlo + e * vhi + u₀ * vhi := by
      gcongr
    _ = d₁ * vlo + (e + u₀) * vhi := by ring
    _ = d₁ * vlo + u₁ * vhi := by
      rw [add_comm e u₀, huadd]

/-- Adjacent productive interior states are ordered on increasing
observables. -/
theorem expect_relaxedProductiveTriInterior_adjacent_le
    (r : RelaxedRate) (a b : ℕ)
    (h : 3 ≤ (a + 1) + (b + 2))
    (hprod₀ :
      relaxedTriStep r (a + 1) (b + 2) h a +
          relaxedTriStep r (a + 1) (b + 2) h (a + 2) ≠ 0)
    (hprod₁ :
      relaxedTriStep r (a + 2) (b + 1) (by omega) (a + 1) +
          relaxedTriStep r (a + 2) (b + 1) (by omega) (a + 3) ≠ 0)
    (F : ℕ → ℝ≥0∞) (hF : Monotone F) :
    expect
        (relaxedProductiveTriInterior r a (b + 1) h hprod₀) F ≤
      expect
        (relaxedProductiveTriInterior r (a + 1) b (by omega) hprod₁) F := by
  let d₀ := relaxedTriStep r (a + 1) (b + 2) h a
  let u₀ := relaxedTriStep r (a + 1) (b + 2) h (a + 2)
  let d₁ := relaxedTriStep r (a + 2) (b + 1) (by omega) (a + 1)
  let u₁ := relaxedTriStep r (a + 2) (b + 1) (by omega) (a + 3)
  have hmass₀ : d₀ / (d₀ + u₀) + u₀ / (d₀ + u₀) = 1 := by
    rw [add_comm]
    simpa only [d₀, u₀] using
      relaxedProductiveTriInterior_masses r a (b + 1) h hprod₀
  have hmass₁ : d₁ / (d₁ + u₁) + u₁ / (d₁ + u₁) = 1 := by
    rw [add_comm]
    simpa only [d₁, u₁] using
      relaxedProductiveTriInterior_masses r (a + 1) b (by omega) hprod₁
  rw [expect_relaxedProductiveTriInterior,
    expect_relaxedProductiveTriInterior]
  calc
    d₀ / (d₀ + u₀) * F a + u₀ / (d₀ + u₀) * F (a + 2) ≤
        d₀ / (d₀ + u₀) * F (a + 1) +
          u₀ / (d₀ + u₀) * F (a + 3) := by
      gcongr
      · exact hF (by omega)
      · exact hF (by omega)
    _ ≤ d₁ / (d₁ + u₁) * F (a + 1) +
        u₁ / (d₁ + u₁) * F (a + 3) :=
      two_point_test hmass₀ hmass₁
        (relaxedProductiveTriInterior_adjacent_up_le
          r a b h hprod₀ hprod₁) (hF (by omega))
    _ = _ := by
      simp only [d₁, u₁]

/-- With one minority molecule left and a productive event available, the
next productive state is all-`X` consensus. -/
theorem expect_relaxedProductiveTriInterior_one_minor_le_consensus
    (r : RelaxedRate) (a : ℕ)
    (h : 3 ≤ (a + 1) + 1)
    (hprod :
      relaxedTriStep r (a + 1) 1 h a +
          relaxedTriStep r (a + 1) 1 h (a + 2) ≠ 0)
    (F : ℕ → ℝ≥0∞) :
    expect (relaxedProductiveTriInterior r a 0 h hprod) F ≤
      F (a + 2) := by
  rw [expect_relaxedProductiveTriInterior]
  have hdown : relaxedTriStep r (a + 1) 1 h a = 0 := by
    rw [relaxedTriStep_down]
    norm_num
  have hup :
      relaxedTriStep r (a + 1) 1 h (a + 2) ≠ 0 := by
    simpa only [hdown, zero_add] using hprod
  rw [hdown]
  simp only [zero_add, ENNReal.zero_div, zero_mul]
  rw [ENNReal.div_self hup (PMF.apply_ne_top _ _), one_mul]

/-- The relaxed productive kernel preserves stochastic order between
adjacent starting counts. -/
theorem relaxedProductiveTriChain_expect_le_succ
    (r : RelaxedRate) (n x : ℕ) (hfire : 0 < r.fire)
    (F : ℕ → ℝ≥0∞) (hF : Monotone F) :
    expect (relaxedProductiveTriChain r n x) F ≤
      expect (relaxedProductiveTriChain r n (x + 1)) F := by
  by_cases h3 : 3 ≤ n
  · by_cases hxlt : x < n
    · by_cases hx0 : x = 0
      · subst x
        have h0 : relaxedProductiveTriChain r n 0 = PMF.pure 0 := by
          unfold relaxedProductiveTriChain
          rw [dif_neg]
          omega
        rw [h0, expect_pure]
        exact expect_ge_at_zero (relaxedProductiveTriChain r n 1) F hF
      · by_cases hlast : x + 1 = n
        · obtain ⟨a, rfl⟩ : ∃ a, x = a + 1 := ⟨x - 1, by omega⟩
          have hn : a + 0 + 2 = n := by omega
          have hprod :=
            lemma6_live_productive_nonzero r
              (n := n) (a := a) (b := 0) h3 hn hfire
          rw [relaxedProductiveTriChain_apply r
            (n := n) (a := a) (b := 0) hn h3 hprod]
          have hcons :
              relaxedProductiveTriChain r n ((a + 1) + 1) =
                PMF.pure ((a + 1) + 1) := by
            unfold relaxedProductiveTriChain
            rw [dif_neg]
            omega
          rw [hcons, expect_pure]
          simpa [show (a + 1) + 1 = a + 2 by omega] using
            expect_relaxedProductiveTriInterior_one_minor_le_consensus
              r a (by omega) hprod F
        · obtain ⟨a, rfl⟩ : ∃ a, x = a + 1 := ⟨x - 1, by omega⟩
          obtain ⟨b, hb⟩ : ∃ b, n = (a + 1) + (b + 2) :=
            ⟨n - ((a + 1) + 2), by omega⟩
          have hpop₀ : a + (b + 1) + 2 = n := by omega
          have hpop₁ : (a + 1) + b + 2 = n := by omega
          have hprod₀ :=
            lemma6_live_productive_nonzero r
              (n := n) (a := a) (b := b + 1) h3 hpop₀ hfire
          have hprod₁ :=
            lemma6_live_productive_nonzero r
              (n := n) (a := a + 1) (b := b) h3 hpop₁ hfire
          rw [relaxedProductiveTriChain_apply r
              (n := n) (a := a) (b := b + 1) hpop₀ h3 hprod₀,
            relaxedProductiveTriChain_apply r
              (n := n) (a := a + 1) (b := b) hpop₁ h3 hprod₁]
          exact expect_relaxedProductiveTriInterior_adjacent_le
            r a b (by omega)
            hprod₀ hprod₁ F hF
    · have hnx : n ≤ x := by omega
      by_cases hxn : x = n
      · subst x
        have h0 : relaxedProductiveTriChain r n n = PMF.pure n := by
          unfold relaxedProductiveTriChain
          rw [dif_neg]
          omega
        have h1 :
            relaxedProductiveTriChain r n (n + 1) = PMF.pure (n + 1) := by
          unfold relaxedProductiveTriChain
          rw [dif_neg]
          omega
        rw [h0, h1, expect_pure, expect_pure]
        exact hF (by omega)
      · have h0 : relaxedProductiveTriChain r n x = PMF.pure x := by
          unfold relaxedProductiveTriChain
          rw [dif_neg]
          omega
        have h1 :
            relaxedProductiveTriChain r n (x + 1) = PMF.pure (x + 1) := by
          unfold relaxedProductiveTriChain
          rw [dif_neg]
          omega
        rw [h0, h1, expect_pure, expect_pure]
        exact hF (by omega)
  · have h0 : relaxedProductiveTriChain r n x = PMF.pure x := by
      unfold relaxedProductiveTriChain
      rw [dif_neg]
      exact fun hp => h3 hp.1
    have h1 : relaxedProductiveTriChain r n (x + 1) = PMF.pure (x + 1) := by
      unfold relaxedProductiveTriChain
      rw [dif_neg]
      exact fun hp => h3 hp.1
    rw [h0, h1, expect_pure, expect_pure]
    exact hF (by omega)

/-- Expectations after one productive step are monotone in the starting
count whenever the firing rate is positive. -/
theorem relaxedProductiveTriChain_expect_monotone
    (r : RelaxedRate) (n : ℕ) (hfire : 0 < r.fire)
    (F : ℕ → ℝ≥0∞) (hF : Monotone F) :
    Monotone fun x => expect (relaxedProductiveTriChain r n x) F :=
  monotone_nat_of_le_succ fun x =>
    relaxedProductiveTriChain_expect_le_succ r n x hfire F hF

end Tri

#print axioms Tri.relaxedProductive_count_adjacent_cross
#print axioms Tri.relaxedProductiveTriInterior_adjacent_up_le
#print axioms Tri.relaxedProductiveTriChain_expect_monotone
