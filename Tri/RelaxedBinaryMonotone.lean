/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.BinaryMonotone
import Tri.RelaxedChain
import Tri.RelaxedDrift

/-!
# Monotonicity of the relaxed binary chain

This module proves monotonicity both in the firing-rate parameter and in the
current `X` count.  These two orders provide the comparison interface used by
the buffered Byzantine Phase-II construction.
-/

namespace Tri

open scoped ENNReal

theorem expect_relaxedTriStep_mono_fire
    (r₀ r₁ : RelaxedRate) (a y : ℕ)
    (h : 3 ≤ (a + 1) + y)
    (hfire : r₀.fire ≤ r₁.fire)
    (F : ℕ → ℝ≥0∞) (hF : Monotone F) :
    expect (relaxedTriStep r₀ (a + 1) y h) F ≤
      expect (relaxedTriStep r₁ (a + 1) y h) F := by
  let d : ℝ≥0∞ := relaxedTriStep r₀ (a + 1) y h a
  let s₀ : ℝ≥0∞ := relaxedTriStep r₀ (a + 1) y h (a + 1)
  let u₀ : ℝ≥0∞ := relaxedTriStep r₀ (a + 1) y h (a + 2)
  let s₁ : ℝ≥0∞ := relaxedTriStep r₁ (a + 1) y h (a + 1)
  let u₁ : ℝ≥0∞ := relaxedTriStep r₁ (a + 1) y h (a + 2)
  have hd :
      d = relaxedTriStep r₁ (a + 1) y h a := by
    dsimp only [d]
    rw [relaxedTriStep_down, relaxedTriStep_down]
  have hu : u₀ ≤ u₁ := by
    dsimp only [u₀, u₁]
    rw [relaxedTriStep_up, relaxedTriStep_up]
    apply ENNReal.div_le_div_right
    simpa [mul_comm] using
      mul_le_mul_left (by exact_mod_cast hfire) _
  have hmass₀ : d + s₀ + u₀ = 1 := by
    simpa only [d, s₀, u₀] using
      relaxedTriStep_masses_sum r₀ a y h
  have hmass₁ : d + s₁ + u₁ = 1 := by
    rw [hd]
    simpa only [s₁, u₁] using
      relaxedTriStep_masses_sum r₁ a y h
  let e := u₁ - u₀
  have hue : u₀ + e = u₁ :=
    add_tsub_cancel_of_le hu
  have hu₀top : u₀ ≠ ⊤ := PMF.apply_ne_top _ _
  have hdtop : d ≠ ⊤ := PMF.apply_ne_top _ _
  have hbalance : s₁ + e = s₀ := by
    apply (ENNReal.add_left_inj hdtop).mp
    apply (ENNReal.add_right_inj hu₀top).mp
    calc
      u₀ + ((s₁ + e) + d) = d + s₁ + (u₀ + e) := by ring
      _ = d + s₁ + u₁ := by rw [hue]
      _ = 1 := hmass₁
      _ = u₀ + (s₀ + d) := by rw [← hmass₀]; ring
  rw [expect_relaxedTriStep, expect_relaxedTriStep]
  rw [← hd]
  calc
    d * F a + s₀ * F (a + 1) + u₀ * F (a + 2) =
        d * F a + (s₁ + e) * F (a + 1) + u₀ * F (a + 2) := by
      rw [hbalance]
    _ = d * F a + s₁ * F (a + 1) +
          e * F (a + 1) + u₀ * F (a + 2) := by ring
    _ ≤ d * F a + s₁ * F (a + 1) +
          e * F (a + 2) + u₀ * F (a + 2) := by
      gcongr
      exact hF (by omega)
    _ = d * F a + s₁ * F (a + 1) + u₁ * F (a + 2) := by
      rw [← hue]
      ring

/-- At a fixed population and count, increasing the firing rate
stochastically increases the raw relaxed transition law. -/
theorem expect_relaxedTriChain_mono_fire
    (r₀ r₁ : RelaxedRate) (n x : ℕ)
    (hfire : r₀.fire ≤ r₁.fire)
    (F : ℕ → ℝ≥0∞) (hF : Monotone F) :
    expect (relaxedTriChain r₀ n x) F ≤
      expect (relaxedTriChain r₁ n x) F := by
  by_cases hphys : 3 ≤ n ∧ x ≤ n
  · rw [relaxedTriChain, dif_pos hphys,
      relaxedTriChain, dif_pos hphys]
    by_cases hx : x = 0
    · subst x
      rw [relaxedTriStep_consensus_Y,
        relaxedTriStep_consensus_Y]
    · obtain ⟨a, rfl⟩ : ∃ a, x = a + 1 :=
        ⟨x - 1, by omega⟩
      exact expect_relaxedTriStep_mono_fire
        r₀ r₁ a (n - (a + 1)) (by omega) hfire F hF
  · rw [relaxedTriChain, dif_neg hphys,
      relaxedTriChain, dif_neg hphys]

theorem relaxedTriStep_adjacent_cross_le_one
    (r : RelaxedRate) (a b : ℕ)
    (h3 : 3 ≤ (a + 1) + (b + 2)) :
    relaxedTriStep r (a + 1) (b + 2) h3 (a + 2) +
        relaxedTriStep r (a + 2) (b + 1) (by omega) (a + 1) ≤ 1 := by
  have hfire : (r.fire : ℝ≥0∞) ≤ 1 := by
    exact_mod_cast (by
      rw [← r.add_eq_one]
      exact le_add_right le_rfl)
  calc
    relaxedTriStep r (a + 1) (b + 2) h3 (a + 2) +
          relaxedTriStep r (a + 2) (b + 1) (by omega) (a + 1) ≤
        triStep (a + 1) (b + 2) h3 (a + 2) +
          triStep (a + 2) (b + 1) (by omega) (a + 1) := by
      gcongr
      · rw [relaxedTriStep_up, triStep_up]
        apply ENNReal.div_le_div_right
        simpa using
          (mul_le_mul_left
            hfire
            ((Nat.choose (a + 1) 2 * (b + 2) : ℕ) : ℝ≥0∞))
      · rw [relaxedTriStep_down, triStep_down]
    _ ≤ 1 := triStep_adjacent_cross_le_one a b h3

theorem expect_relaxedTriStep_adjacent_le
    (r : RelaxedRate) (a b : ℕ)
    (h3 : 3 ≤ (a + 1) + (b + 2))
    (F : ℕ → ℝ≥0∞) (hF : Monotone F) :
    expect (relaxedTriStep r (a + 1) (b + 2) h3) F ≤
      expect (relaxedTriStep r (a + 2) (b + 1) (by omega)) F := by
  rw [expect_relaxedTriStep, expect_relaxedTriStep]
  exact adjacent_three_atom_expect_le
    (relaxedTriStep_masses_sum r a (b + 2) h3)
    (relaxedTriStep_masses_sum r (a + 1) (b + 1) (by omega))
    (relaxedTriStep_adjacent_cross_le_one r a b h3)
    F hF a

theorem expect_relaxedTriStep_one_minor_le_consensus
    (r : RelaxedRate) (a : ℕ)
    (h3 : 3 ≤ (a + 1) + 1)
    (F : ℕ → ℝ≥0∞) (hF : Monotone F) :
    expect (relaxedTriStep r (a + 1) 1 h3) F ≤ F (a + 2) := by
  rw [expect_relaxedTriStep]
  calc
    relaxedTriStep r (a + 1) 1 h3 a * F a +
          relaxedTriStep r (a + 1) 1 h3 (a + 1) * F (a + 1) +
          relaxedTriStep r (a + 1) 1 h3 (a + 2) * F (a + 2) ≤
        relaxedTriStep r (a + 1) 1 h3 a * F (a + 2) +
          relaxedTriStep r (a + 1) 1 h3 (a + 1) * F (a + 2) +
          relaxedTriStep r (a + 1) 1 h3 (a + 2) * F (a + 2) := by
      gcongr
      · exact hF (by omega)
      · exact hF (by omega)
    _ = F (a + 2) := by
      rw [← add_mul, ← add_mul, relaxedTriStep_masses_sum, one_mul]

theorem relaxedTriChain_expect_le_succ
    (r : RelaxedRate) (n x : ℕ)
    (F : ℕ → ℝ≥0∞) (hF : Monotone F) :
    expect (relaxedTriChain r n x) F ≤
      expect (relaxedTriChain r n (x + 1)) F := by
  by_cases h3 : 3 ≤ n
  · by_cases hxlt : x < n
    · by_cases hx0 : x = 0
      · subst x
        rw [relaxedTriChain_consensus_Y r h3, expect_pure]
        exact expect_ge_at_zero (relaxedTriChain r n 1) F hF
      · by_cases hlast : x + 1 = n
        · obtain ⟨a, rfl⟩ : ∃ a, x = a + 1 :=
            ⟨x - 1, by omega⟩
          have hn : (a + 1) + 1 = n := by omega
          rw [relaxedTriChain_apply r
            (a := a) (b := 0) (by omega) h3]
          have hcons :
              relaxedTriChain r n ((a + 1) + 1) =
                PMF.pure ((a + 1) + 1) := by
            rw [hn]
            exact relaxedTriChain_consensus_X r h3
          rw [hcons, expect_pure]
          simpa [show (a + 1) + 1 = a + 2 by omega] using
            expect_relaxedTriStep_one_minor_le_consensus
              r a (by omega) F hF
        · obtain ⟨a, rfl⟩ : ∃ a, x = a + 1 :=
            ⟨x - 1, by omega⟩
          obtain ⟨b, hb⟩ :
              ∃ b, n = (a + 1) + (b + 2) :=
            ⟨n - ((a + 1) + 2), by omega⟩
          rw [relaxedTriChain_apply r
              (a := a) (b := b + 1) (by omega) h3,
            relaxedTriChain_apply r
              (a := a + 1) (b := b) (by omega) h3]
          exact
            expect_relaxedTriStep_adjacent_le
              r a b (by omega) F hF
    · have hnx : n ≤ x := by omega
      by_cases hxn : x = n
      · subst x
        rw [relaxedTriChain_consensus_X r h3]
        have hout :
            relaxedTriChain r n (n + 1) = PMF.pure (n + 1) := by
          unfold relaxedTriChain
          rw [dif_neg]
          omega
        rw [hout, expect_pure, expect_pure]
        exact hF (by omega)
      · have hxout : n < x := by omega
        have hout0 : relaxedTriChain r n x = PMF.pure x := by
          unfold relaxedTriChain
          rw [dif_neg]
          omega
        have hout1 :
            relaxedTriChain r n (x + 1) = PMF.pure (x + 1) := by
          unfold relaxedTriChain
          rw [dif_neg]
          omega
        rw [hout0, hout1, expect_pure, expect_pure]
        exact hF (by omega)
  · have hout0 : relaxedTriChain r n x = PMF.pure x := by
      unfold relaxedTriChain
      rw [dif_neg]
      exact fun h => h3 h.1
    have hout1 :
        relaxedTriChain r n (x + 1) = PMF.pure (x + 1) := by
      unfold relaxedTriChain
      rw [dif_neg]
      exact fun h => h3 h.1
    rw [hout0, hout1, expect_pure, expect_pure]
    exact hF (by omega)

theorem relaxedTriChain_expect_monotone
    (r : RelaxedRate) (n : ℕ)
    (F : ℕ → ℝ≥0∞) (hF : Monotone F) :
    Monotone fun x => expect (relaxedTriChain r n x) F :=
  monotone_nat_of_le_succ
    (fun x => relaxedTriChain_expect_le_succ r n x F hF)

end Tri

#print axioms Tri.expect_relaxedTriStep_mono_fire
#print axioms Tri.expect_relaxedTriChain_mono_fire
#print axioms Tri.relaxedTriStep_adjacent_cross_le_one
#print axioms Tri.relaxedTriChain_expect_monotone
