/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.BinaryMonotone
import Tri.HitProbMono
import Tri.PaperCorollary3

/-!
# Monotonicity repair for Paper Corollary 3

The printed Corollary 3 proof applies the productive-clock estimate at the
boundary minority size `γ lg n`.  Starts with a smaller minority count are
handled by stochastic monotonicity of the productive binary chain: increasing
the initial `X` count can only increase the chance of hitting an upper target.
-/

namespace Tri

open scoped ENNReal

/-! ## One-step stochastic monotonicity for the productive chain -/

/-- Adjacent productive interior states are ordered on increasing observables. -/
theorem expect_productiveTriInterior_adjacent_le
    (a b : ℕ) (F : ℕ → ℝ≥0∞) (hF : Monotone F) :
    expect (productiveTriInterior a (b + 1) (by omega)) F ≤
      expect (productiveTriInterior (a + 1) b (by omega)) F := by
  rw [expect_productiveTriInterior, expect_productiveTriInterior]
  let D : ℝ≥0∞ := ((a + b + 1 : ℕ) : ℝ≥0∞)
  have hDlo :
      (a : ℝ≥0∞) + ((b + 1 : ℕ) : ℝ≥0∞) = D := by
    dsimp [D]
    push_cast
    ring
  have hDhi :
      ((a + 1 : ℕ) : ℝ≥0∞) + (b : ℝ≥0∞) = D := by
    dsimp [D]
    push_cast
    ring
  rw [hDlo, hDhi]
  have hb_succ :
      ((b + 1 : ℕ) : ℝ≥0∞) / D =
        (b : ℝ≥0∞) / D + (1 : ℝ≥0∞) / D := by
    calc
      ((b + 1 : ℕ) : ℝ≥0∞) / D =
          ((b : ℝ≥0∞) + 1) / D := by
            push_cast
            ring
      _ = (b : ℝ≥0∞) / D + (1 : ℝ≥0∞) / D := by
            rw [ENNReal.add_div]
  have ha_succ :
      ((a + 1 : ℕ) : ℝ≥0∞) / D =
        (a : ℝ≥0∞) / D + (1 : ℝ≥0∞) / D := by
    calc
      ((a + 1 : ℕ) : ℝ≥0∞) / D =
          ((a : ℝ≥0∞) + 1) / D := by
            push_cast
            ring
      _ = (a : ℝ≥0∞) / D + (1 : ℝ≥0∞) / D := by
            rw [ENNReal.add_div]
  calc
    ((b + 1 : ℕ) : ℝ≥0∞) / D * F a +
        (a : ℝ≥0∞) / D * F (a + 2) ≤
      ((b + 1 : ℕ) : ℝ≥0∞) / D * F (a + 1) +
        (a : ℝ≥0∞) / D * F (a + 2) := by
        gcongr
        exact hF (by omega)
    _ = ((b : ℝ≥0∞) / D + (1 : ℝ≥0∞) / D) * F (a + 1) +
        (a : ℝ≥0∞) / D * F (a + 2) := by
        rw [hb_succ]
    _ = (b : ℝ≥0∞) / D * F (a + 1) +
        ((1 : ℝ≥0∞) / D * F (a + 1) +
          (a : ℝ≥0∞) / D * F (a + 2)) := by ring
    _ ≤ (b : ℝ≥0∞) / D * F (a + 1) +
        ((1 : ℝ≥0∞) / D * F (a + 3) +
          (a : ℝ≥0∞) / D * F (a + 3)) := by
        gcongr
        · exact hF (by omega)
        · exact hF (by omega)
    _ = (b : ℝ≥0∞) / D * F (a + 1) +
        (((a : ℝ≥0∞) / D + (1 : ℝ≥0∞) / D) * F (a + 3)) := by ring
    _ = (b : ℝ≥0∞) / D * F (a + 1) +
        ((a + 1 : ℕ) : ℝ≥0∞) / D * F (a + 3) := by
        rw [← ha_succ]

/-- With one minority molecule left, the next productive step is bounded by
all-`X` consensus for increasing observables. -/
theorem expect_productiveTriInterior_one_minor_le_consensus
    (a : ℕ) (hprod : 0 < a)
    (F : ℕ → ℝ≥0∞) (hF : Monotone F) :
    expect (productiveTriInterior a 0 hprod) F ≤ F (a + 2) := by
  rw [expect_productiveTriInterior]
  simp only [Nat.cast_zero, add_zero]
  calc
    (0 : ℝ≥0∞) / (a : ℝ≥0∞) * F a +
        (a : ℝ≥0∞) / (a : ℝ≥0∞) * F (a + 2) ≤
      (0 : ℝ≥0∞) / (a : ℝ≥0∞) * F (a + 2) +
        (a : ℝ≥0∞) / (a : ℝ≥0∞) * F (a + 2) := by
        gcongr
        exact hF (by omega)
    _ = F (a + 2) := by
        have ha0 : (a : ℝ≥0∞) ≠ 0 := by exact_mod_cast hprod.ne'
        rw [ENNReal.zero_div, zero_mul, zero_add,
          ENNReal.div_self ha0 (ENNReal.natCast_ne_top a), one_mul]

/-- The productive binary kernel preserves stochastic order between adjacent
starting counts, including consensus and nonphysical boundary cases. -/
theorem productiveTriChain_expect_le_succ
    (n x : ℕ) (F : ℕ → ℝ≥0∞) (hF : Monotone F) :
    expect (productiveTriChain n x) F ≤
      expect (productiveTriChain n (x + 1)) F := by
  by_cases h3 : 3 ≤ n
  · by_cases hxlt : x < n
    · by_cases hx0 : x = 0
      · subst x
        have h0 : productiveTriChain n 0 = PMF.pure 0 := by
          unfold productiveTriChain
          rw [dif_neg]
          omega
        rw [h0, expect_pure]
        exact expect_ge_at_zero (productiveTriChain n 1) F hF
      · by_cases hlast : x + 1 = n
        · obtain ⟨a, rfl⟩ : ∃ a, x = a + 1 := ⟨x - 1, by omega⟩
          have hn : (a + 1) + 1 = n := by omega
          rw [productiveTriChain_apply (a := a) (b := 0) hn (by omega)]
          have hcons :
              productiveTriChain n ((a + 1) + 1) =
                PMF.pure ((a + 1) + 1) := by
            rw [hn]
            unfold productiveTriChain
            rw [dif_neg]
            omega
          rw [hcons, expect_pure]
          simpa [show (a + 1) + 1 = a + 2 by omega] using
            expect_productiveTriInterior_one_minor_le_consensus
              a (by omega) F hF
        · obtain ⟨a, rfl⟩ : ∃ a, x = a + 1 := ⟨x - 1, by omega⟩
          obtain ⟨b, hb⟩ : ∃ b, n = (a + 1) + (b + 2) :=
            ⟨n - ((a + 1) + 2), by omega⟩
          rw [productiveTriChain_apply
              (a := a) (b := b + 1) (by omega) (by omega),
            productiveTriChain_apply
              (a := a + 1) (b := b) (by omega) (by omega)]
          exact expect_productiveTriInterior_adjacent_le a b F hF
    · have hnx : n ≤ x := by omega
      by_cases hxn : x = n
      · subst x
        have h0 : productiveTriChain n n = PMF.pure n := by
          unfold productiveTriChain
          rw [dif_neg]
          omega
        have h1 : productiveTriChain n (n + 1) = PMF.pure (n + 1) := by
          unfold productiveTriChain
          rw [dif_neg]
          omega
        rw [h0, h1, expect_pure, expect_pure]
        exact hF (by omega)
      · have h0 : productiveTriChain n x = PMF.pure x := by
          unfold productiveTriChain
          rw [dif_neg]
          omega
        have h1 : productiveTriChain n (x + 1) = PMF.pure (x + 1) := by
          unfold productiveTriChain
          rw [dif_neg]
          omega
        rw [h0, h1, expect_pure, expect_pure]
        exact hF (by omega)
  · have h0 : productiveTriChain n x = PMF.pure x := by
      unfold productiveTriChain
      rw [dif_neg]
      exact fun h => h3 h.1
    have h1 : productiveTriChain n (x + 1) = PMF.pure (x + 1) := by
      unfold productiveTriChain
      rw [dif_neg]
      exact fun h => h3 h.1
    rw [h0, h1, expect_pure, expect_pure]
    exact hF (by omega)

/-- Expectations after one productive step are monotone in the starting count. -/
theorem productiveTriChain_expect_monotone
    (n : ℕ) (F : ℕ → ℝ≥0∞) (hF : Monotone F) :
    Monotone fun x => expect (productiveTriChain n x) F :=
  monotone_nat_of_le_succ fun x =>
    productiveTriChain_expect_le_succ n x F hF

/-- Every finite productive-clock horizon preserves increasing observables. -/
theorem productiveTriChain_iter_expect_monotone
    (n T : ℕ) (F : ℕ → ℝ≥0∞) (hF : Monotone F) :
    Monotone fun x => expect (iter (productiveTriChain n) T x) F := by
  induction T with
  | zero =>
      simpa [iter] using hF
  | succ t ih =>
      intro x y hxy
      change
        expect (iter (productiveTriChain n) (t + 1) x) F ≤
          expect (iter (productiveTriChain n) (t + 1) y) F
      rw [iter_succ, iter_succ, expect_bind, expect_bind]
      exact (productiveTriChain_expect_monotone n
        (fun z => expect (iter (productiveTriChain n) t z) F) ih) hxy

/-! ## Bellman monotonicity for hitting upper sets -/

/-- For any upward-closed target, the productive-chain hitting probability is
monotone in the initial `X` count. -/
theorem productive_hitProb_mono_start_of_upper
    (n T : ℕ) (A : ℕ → Prop) [DecidablePred A]
    (hA : ∀ ⦃x y : ℕ⦄, x ≤ y → A x → A y) :
    Monotone fun x => hitProb A (productiveTriChain n) T x := by
  induction T with
  | zero =>
      intro x y hxy
      unfold hitProb
      simp [iter, expect_pure, ind]
      by_cases hx : A x
      · have hy : A y := hA hxy hx
        simp [hx, hy]
      · by_cases hy : A y
        · simp [hx, hy]
        · simp [hx, hy]
  | succ t ih =>
      intro x y hxy
      change hitProb A (productiveTriChain n) (t + 1) x ≤
        hitProb A (productiveTriChain n) (t + 1) y
      by_cases hy : A y
      · rw [hitProb_eq_one_of_mem A (productiveTriChain n) (t + 1) y hy]
        exact hitProb_le_one A (productiveTriChain n) (t + 1) x
      · have hx : ¬ A x := fun hxA => hy (hA hxy hxA)
        rw [hitProb_succ_of_not A (productiveTriChain n) t x hx,
          hitProb_succ_of_not A (productiveTriChain n) t y hy]
        exact (productiveTriChain_expect_monotone n
          (fun z => hitProb A (productiveTriChain n) t z) ih) hxy

/-- The upward closure of all-`X` consensus.  On the physical support
`x ≤ n`, this is equivalent to `Phase3Done n`. -/
def Phase3DoneUpper (n x : ℕ) : Prop :=
  n ≤ x

instance phase3DoneUpperDecidable (n : ℕ) :
    DecidablePred (Phase3DoneUpper n) := by
  intro x
  unfold Phase3DoneUpper
  infer_instance

/-- The genuinely upward-closed consensus target. -/
theorem productive_hitProb_phase3DoneUpper_mono_start
    (n T : ℕ) :
    Monotone fun x =>
      hitProb (Phase3DoneUpper n) (productiveTriChain n) T x :=
  productive_hitProb_mono_start_of_upper n T (Phase3DoneUpper n) (by
    intro x y hxy hx
    unfold Phase3DoneUpper at hx ⊢
    omega)

/-- On physical starts, hitting `n ≤ x` is the same as hitting `x = n`. -/
theorem hitProb_phase3DoneUpper_eq_done_of_le
    (n T x : ℕ) (hx : x ≤ n) :
    hitProb (Phase3DoneUpper n) (productiveTriChain n) T x =
      hitProb (Phase3Done n) (productiveTriChain n) T x := by
  induction T generalizing x with
  | zero =>
      unfold hitProb
      rw [show iter (freeze (Phase3DoneUpper n) (productiveTriChain n)) 0 x =
          PMF.pure x from rfl,
        show iter (freeze (Phase3Done n) (productiveTriChain n)) 0 x =
          PMF.pure x from rfl,
        expect_pure, expect_pure]
      unfold ind Phase3DoneUpper Phase3Done
      by_cases hxn : x = n
      · simp [hxn]
      · have hnot : ¬ n ≤ x := by omega
        simp [hxn, hnot]
  | succ t ih =>
      by_cases hupper : Phase3DoneUpper n x
      · have hdone : Phase3Done n x := by
          unfold Phase3DoneUpper Phase3Done at *
          omega
        rw [hitProb_eq_one_of_mem (Phase3DoneUpper n) (productiveTriChain n)
            (t + 1) x hupper,
          hitProb_eq_one_of_mem (Phase3Done n) (productiveTriChain n)
            (t + 1) x hdone]
      · have hdone : ¬ Phase3Done n x := by
          unfold Phase3DoneUpper Phase3Done at *
          omega
        rw [hitProb_succ_of_not (Phase3DoneUpper n) (productiveTriChain n)
            t x hupper,
          hitProb_succ_of_not (Phase3Done n) (productiveTriChain n)
            t x hdone]
        refine tsum_congr fun z => ?_
        by_cases hzle : z ≤ n
        · rw [ih z hzle]
        · have hz0 : productiveTriChain n x z = 0 := by
            by_contra hzneq
            exact hzle (productiveTriChain_support_le n x hx z hzneq)
          simp [hz0]

/-- The all-`X` target is monotone across physical starting states. -/
theorem productive_hitProb_phase3Done_mono_start_of_le
    (n T : ℕ) {x y : ℕ} (hxy : x ≤ y) (hy : y ≤ n) :
    hitProb (Phase3Done n) (productiveTriChain n) T x ≤
      hitProb (Phase3Done n) (productiveTriChain n) T y := by
  have hx : x ≤ n := by omega
  rw [← hitProb_phase3DoneUpper_eq_done_of_le n T x hx,
    ← hitProb_phase3DoneUpper_eq_done_of_le n T y hy]
  exact productive_hitProb_phase3DoneUpper_mono_start n T hxy

/-- The omitted Corollary 3 boundary step: a proof at the boundary
`y = γ lg n` transfers to any phase-3 entry state with smaller minority. -/
theorem corollary3_boundary_success_le_entry_success
    (n γ T xb x₀ : ℕ)
    (hboundary : xb + phase3Scale n γ = n)
    (hentry : Phase3EntryProductive n γ x₀) :
    hitProb (Phase3Done n) (productiveTriChain n) T xb ≤
      hitProb (Phase3Done n) (productiveTriChain n) T x₀ := by
  exact productive_hitProb_phase3Done_mono_start_of_le n T
    (by
      unfold Phase3EntryProductive at hentry
      omega)
    hentry.1

example :
    hitProb (Phase3Done 16) (productiveTriChain 16) 6 12 ≤
      hitProb (Phase3Done 16) (productiveTriChain 16) 6 13 := by
  exact productive_hitProb_phase3Done_mono_start_of_le 16 6
    (by omega) (by omega)

end Tri

#print axioms Tri.expect_productiveTriInterior_adjacent_le
#print axioms Tri.productiveTriChain_expect_monotone
#print axioms Tri.productiveTriChain_iter_expect_monotone
#print axioms Tri.productive_hitProb_mono_start_of_upper
#print axioms Tri.productive_hitProb_phase3Done_mono_start_of_le
#print axioms Tri.corollary3_boundary_success_le_entry_success
