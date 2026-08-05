/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.PaperLemma7
import Tri.RelaxedProductivity
import Tri.LazyHitting

/-!
# The raw/productive time change for the relaxed Tri chain

The physical relaxed chain is a state-dependent mixture of an inert self-loop
and one step of `relaxedProductiveTriChain`.  A decreasing counter records how
many productive reactions remain.  This gives the finite-horizon bridge from
Paper Lemma 7's productive clock to the raw interaction clock.
-/

namespace Tri

open scoped ENNReal

/-- Total mass of the two state-changing atoms at a physical interior state. -/
noncomputable def relaxedProductiveMassAt
    (r : RelaxedRate) (n x : ℕ) : ℝ≥0∞ :=
  if hphys : 3 ≤ n ∧ 0 < x ∧ x < n then
    let a := x - 1
    let b := n - x - 1
    relaxedTriStep r (a + 1) (b + 1) (by omega) a +
      relaxedTriStep r (a + 1) (b + 1) (by omega) (a + 2)
  else
    0

/-- Inert mass of the physical relaxed chain. -/
noncomputable def relaxedNonproductiveMassAt
    (r : RelaxedRate) (n x : ℕ) : ℝ≥0∞ :=
  if hphys : 3 ≤ n ∧ 0 < x ∧ x < n then
    let a := x - 1
    let b := n - x - 1
    relaxedTriStep r (a + 1) (b + 1) (by omega) (a + 1)
  else
    1

/-- Productive and inert masses partition one physical interaction. -/
theorem relaxedProductiveMassAt_add_nonproductiveMassAt
    (r : RelaxedRate) (n x : ℕ) :
    relaxedProductiveMassAt r n x +
        relaxedNonproductiveMassAt r n x = 1 := by
  unfold relaxedProductiveMassAt relaxedNonproductiveMassAt
  by_cases hphys : 3 ≤ n ∧ 0 < x ∧ x < n
  · rw [dif_pos hphys, dif_pos hphys]
    dsimp only
    simp only [show x - 1 + 1 = x by omega,
      show n - x - 1 + 1 = n - x by omega,
      show x - 1 + 2 = x + 1 by omega]
    have hsum :=
      relaxedTriStep_masses_sum r (x - 1) (n - x) (by omega)
    calc
      _ =
          relaxedTriStep r x (n - x) (by omega) (x - 1) +
            relaxedTriStep r x (n - x) (by omega) x +
            relaxedTriStep r x (n - x) (by omega) (x + 1) := by ring
      _ = 1 := by
        simpa only [show x - 1 + 1 = x by omega,
          show x - 1 + 2 = x + 1 by omega] using hsum
  · rw [dif_neg hphys, dif_neg hphys, zero_add]

/-- The physical sampler equipped with a remaining-productive-events counter.
At zero the chain is frozen; otherwise a state change decrements the counter. -/
noncomputable def relaxedProductiveCountdown
    (r : RelaxedRate) (n : ℕ) :
    ℕ × ℕ → PMF (ℕ × ℕ)
  | q@(_, 0) => PMF.pure q
  | (x, k + 1) =>
      (relaxedTriChain r n x).map fun z =>
        if z = x then (x, k + 1) else (z, k)

@[simp] theorem relaxedProductiveCountdown_zero
    (r : RelaxedRate) (n x : ℕ) :
    relaxedProductiveCountdown r n (x, 0) = PMF.pure (x, 0) :=
  rfl

/-- Forgetting a positive countdown gives exactly one physical interaction. -/
theorem relaxedProductiveCountdown_succ_map_fst
    (r : RelaxedRate) (n x k : ℕ) :
    (relaxedProductiveCountdown r n (x, k + 1)).map Prod.fst =
      relaxedTriChain r n x := by
  unfold relaxedProductiveCountdown
  rw [PMF.map_comp]
  have hf :
      (Prod.fst ∘ fun z => if z = x then (x, k + 1) else (z, k)) =
        id := by
    funext z
    by_cases hz : z = x <;> simp [hz]
  rw [hf, PMF.map_id]

/-- Algebraic cancellation behind the physical/productive mixture. -/
private theorem relaxed_three_mass_mixture
    {down stay up gd gs gu : ℝ≥0∞}
    (hprod : down + up ≠ 0)
    (hprodTop : down + up ≠ ⊤) :
    down * gd + stay * gs + up * gu =
      stay * gs +
        (down + up) *
          (down / (down + up) * gd + up / (down + up) * gu) := by
  have hdown :
      (down + up) * (down / (down + up)) = down :=
    ENNReal.mul_div_cancel hprod hprodTop
  have hup :
      (down + up) * (up / (down + up)) = up :=
    ENNReal.mul_div_cancel hprod hprodTop
  calc
    down * gd + stay * gs + up * gu =
        stay * gs +
          ((down + up) * (down / (down + up))) * gd +
          ((down + up) * (up / (down + up))) * gu := by
            rw [hdown, hup]
            ring
    _ = _ := by ring

/-- Exact one-step inert/productive mixture formula for the countdown. -/
theorem expect_relaxedProductiveCountdown_succ
    (r : RelaxedRate) (n x k : ℕ)
    (G : ℕ × ℕ → ℝ≥0∞) :
    expect (relaxedProductiveCountdown r n (x, k + 1)) G =
      relaxedNonproductiveMassAt r n x * G (x, k + 1) +
        relaxedProductiveMassAt r n x *
          expect (relaxedProductiveTriChain r n x)
            (fun z => G (z, k)) := by
  unfold relaxedProductiveCountdown
  rw [expect_map]
  unfold relaxedProductiveMassAt relaxedNonproductiveMassAt
  by_cases hphys : 3 ≤ n ∧ 0 < x ∧ x < n
  · rw [dif_pos hphys, dif_pos hphys]
    dsimp only
    have hraw :
        relaxedTriChain r n x =
          relaxedTriStep r x (n - x) (by omega) := by
      unfold relaxedTriChain
      rw [dif_pos ⟨hphys.1, by omega⟩]
    rw [hraw]
    have hexpect :
        expect (relaxedTriStep r x (n - x) (by omega))
            (fun z => G (if z = x then (x, k + 1) else (z, k))) =
          relaxedTriStep r x (n - x) (by omega) (x - 1) *
              G (if x - 1 = x then (x, k + 1) else (x - 1, k)) +
            relaxedTriStep r x (n - x) (by omega) x *
              G (if x = x then (x, k + 1) else (x, k)) +
            relaxedTriStep r x (n - x) (by omega) (x + 1) *
              G (if x + 1 = x then (x, k + 1) else (x + 1, k)) := by
      simpa only [show x - 1 + 1 = x by omega,
        show x - 1 + 2 = x + 1 by omega] using
        expect_relaxedTriStep r (x - 1) (n - x) (by omega)
          (fun z => G (if z = x then (x, k + 1) else (z, k)))
    rw [hexpect]
    simp only [show x - 1 + 1 = x by omega,
      if_neg (by omega : x - 1 ≠ x),
      if_neg (by omega : x + 1 ≠ x)]
    simp only [show n - x - 1 + 1 = n - x by omega,
      show x - 1 + 2 = x + 1 by omega]
    let P :=
      relaxedTriStep r x (n - x) (by omega) (x - 1) +
        relaxedTriStep r x (n - x) (by omega) (x + 1)
    by_cases hP : P = 0
    · have hdown :
          relaxedTriStep r x (n - x) (by omega) (x - 1) = 0 :=
        (add_eq_zero.mp hP).1
      have hup :
          relaxedTriStep r x (n - x) (by omega) (x + 1) = 0 :=
        (add_eq_zero.mp hP).2
      unfold relaxedProductiveTriChain
      rw [dif_pos hphys]
      dsimp only
      simp only [show x - 1 + 1 = x by omega,
        show n - x - 1 + 1 = n - x by omega,
        show x - 1 + 2 = x + 1 by omega]
      rw [dif_neg (fun hne => hne hP)]
      simp [hdown, hup]
    · have hPtop : P ≠ ⊤ := by
        exact ENNReal.add_ne_top.mpr
          ⟨PMF.apply_ne_top _ _, PMF.apply_ne_top _ _⟩
      unfold relaxedProductiveTriChain
      rw [dif_pos hphys]
      dsimp only
      simp only [show x - 1 + 1 = x by omega,
        show n - x - 1 + 1 = n - x by omega,
        show x - 1 + 2 = x + 1 by omega]
      rw [dif_pos hP, expect_relaxedProductiveTriInterior]
      simp only [if_true, show x - 1 + 1 = x by omega,
        show n - x - 1 + 1 = n - x by omega,
        show x - 1 + 2 = x + 1 by omega]
      simpa only [P] using
        (relaxed_three_mass_mixture
          (down :=
            relaxedTriStep r x (n - x) (by omega) (x - 1))
          (stay :=
            relaxedTriStep r x (n - x) (by omega) x)
          (up :=
            relaxedTriStep r x (n - x) (by omega) (x + 1))
          (gd := G (x - 1, k))
          (gs := G (x, k + 1))
          (gu := G (x + 1, k))
          hP hPtop)
  · rw [dif_neg hphys, dif_neg hphys]
    have hraw : relaxedTriChain r n x = PMF.pure x := by
      unfold relaxedTriChain
      by_cases hn : 3 ≤ n ∧ x ≤ n
      · obtain ⟨hn3, hxn⟩ := hn
        have hxend : x = 0 ∨ x = n := by omega
        rcases hxend with rfl | rfl
        · exact relaxedTriChain_consensus_Y r hn3
        · exact relaxedTriChain_consensus_X r hn3
      · exact dif_neg hn
    have hprod : relaxedProductiveTriChain r n x = PMF.pure x := by
      unfold relaxedProductiveTriChain
      exact dif_neg hphys
    rw [hraw, hprod, expect_pure]
    simp

/-- Freeze the productive countdown when a physical boundary is reached. -/
noncomputable def relaxedProductiveCountdownStop
    (B : ℕ → Prop) [DecidablePred B]
    (r : RelaxedRate) (n : ℕ) :
    ℕ × ℕ → PMF (ℕ × ℕ) :=
  freeze (fun q => B q.1) (relaxedProductiveCountdown r n)

/-- The stopped countdown projects either to one physical interaction or to a
self-loop. -/
theorem relaxedProductiveCountdownStop_isLazyProjection
    (B : ℕ → Prop) [DecidablePred B]
    (r : RelaxedRate) (n : ℕ) :
    IsLazyProjection (relaxedTriChain r n)
      (relaxedProductiveCountdownStop B r n) Prod.fst := by
  intro q
  rcases q with ⟨x, k⟩
  by_cases hB : B x
  · right
    rw [relaxedProductiveCountdownStop, freeze_of_mem (x, k) hB]
    exact PMF.pure_map Prod.fst (x, k)
  · rw [relaxedProductiveCountdownStop, freeze_of_not_mem (x, k) hB]
    cases k with
    | zero =>
        right
        rw [relaxedProductiveCountdown_zero]
        exact PMF.pure_map Prod.fst (x, 0)
    | succ k =>
        left
        exact relaxedProductiveCountdown_succ_map_fst r n x k

/-- The raw relaxed chain hits a target at least as readily as the
boundary-stopped countdown with the same raw horizon. -/
theorem relaxedTriChain_targetFailure_le_productiveCountdownStop
    (A B : ℕ → Prop) [DecidablePred A] [DecidablePred B]
    (r : RelaxedRate) (n T M x₀ : ℕ) :
    terminalFailureMass
        (iter (freeze A (relaxedTriChain r n)) T x₀) A ≤
      terminalFailureMass
        (iter (relaxedProductiveCountdownStop B r n) T (x₀, M))
        (fun q => A q.1) := by
  exact targetFreeze_failure_le_lazy_projection
    A (relaxedTriChain r n) (relaxedProductiveCountdownStop B r n)
    Prod.fst (relaxedProductiveCountdownStop_isLazyProjection B r n)
    T (x₀, M)

@[simp] theorem relaxedProductiveCountdownStop_zero
    (B : ℕ → Prop) [DecidablePred B]
    (r : RelaxedRate) (n x : ℕ) :
    relaxedProductiveCountdownStop B r n (x, 0) = PMF.pure (x, 0) := by
  by_cases hB : B x
  · exact freeze_of_mem (x, 0) hB
  · rw [relaxedProductiveCountdownStop, freeze_of_not_mem (x, 0) hB,
      relaxedProductiveCountdown_zero]

/-- A boundary state is absorbing for every stopped-countdown iterate. -/
theorem iter_relaxedProductiveCountdownStop_of_boundary
    (B : ℕ → Prop) [DecidablePred B]
    (r : RelaxedRate) (n x k : ℕ) (hB : B x) :
    ∀ T,
      iter (relaxedProductiveCountdownStop B r n) T (x, k) =
        PMF.pure (x, k) := by
  intro T
  exact iter_targetFreeze_of_mem
    (fun q : ℕ × ℕ => B q.1)
    (relaxedProductiveCountdown r n) (x, k) hB T

/-- Resolved raw-countdown paths have no more terminal cost than the same
number of boundary-stopped productive steps. -/
theorem relaxedProductiveCountdownStop_resolved_le
    (B : ℕ → Prop) [DecidablePred B]
    (r : RelaxedRate) (n : ℕ) (F : ℕ → ℝ≥0∞) :
    ∀ T k x,
      expect
          (iter (relaxedProductiveCountdownStop B r n) T (x, k))
          (fun q => if q.2 = 0 ∨ B q.1 then F q.1 else 0) ≤
        expect
          (iter (freeze B (relaxedProductiveTriChain r n)) k x) F := by
  intro T
  induction T with
  | zero =>
      intro k x
      cases k with
      | zero => simp [iter]
      | succ k =>
          by_cases hB : B x
          · rw [iter_targetFreeze_of_mem
                B (relaxedProductiveTriChain r n) x hB (k + 1)]
            simp [iter, hB]
          · simp [iter, hB]
  | succ T ih =>
      intro k x
      cases k with
      | zero =>
          rw [iter_succ, relaxedProductiveCountdownStop_zero,
            PMF.pure_bind]
          simpa [iter] using ih 0 x
      | succ k =>
          by_cases hB : B x
          · rw [iter_relaxedProductiveCountdownStop_of_boundary
                B r n x (k + 1) hB,
              iter_targetFreeze_of_mem
                B (relaxedProductiveTriChain r n) x hB (k + 1)]
            simp [hB]
          · rw [iter_succ, expect_bind]
            change
              expect (relaxedProductiveCountdownStop B r n (x, k + 1))
                  (fun a =>
                    expect
                      (iter (relaxedProductiveCountdownStop B r n) T a)
                      (fun q =>
                        if q.2 = 0 ∨ B q.1 then F q.1 else 0)) ≤
                expect
                  (iter
                    (freeze B (relaxedProductiveTriChain r n))
                    (k + 1) x)
                  F
            rw [relaxedProductiveCountdownStop,
              freeze_of_not_mem (x, k + 1) hB,
              expect_relaxedProductiveCountdown_succ]
            let V : ℕ → ℝ≥0∞ := fun y =>
              expect
                (iter (freeze B (relaxedProductiveTriChain r n)) k y) F
            have hsmall :
                expect (relaxedProductiveTriChain r n x)
                    (fun y =>
                      expect
                        (iter (relaxedProductiveCountdownStop B r n)
                          T (y, k))
                        (fun q =>
                          if q.2 = 0 ∨ B q.1 then F q.1 else 0)) ≤
                  expect (relaxedProductiveTriChain r n x) V := by
              unfold expect
              exact ENNReal.tsum_le_tsum fun y =>
                mul_le_mul_right (ih k y) _
            have htarget :
                expect
                    (iter
                      (freeze B (relaxedProductiveTriChain r n))
                      (k + 1) x)
                    F =
                  expect (relaxedProductiveTriChain r n x) V := by
              rw [iter_succ, freeze_of_not_mem x hB, expect_bind]
              rfl
            calc
              relaxedNonproductiveMassAt r n x *
                    expect
                      (iter (relaxedProductiveCountdownStop B r n)
                        T (x, k + 1))
                      (fun q =>
                        if q.2 = 0 ∨ B q.1 then F q.1 else 0) +
                  relaxedProductiveMassAt r n x *
                    expect (relaxedProductiveTriChain r n x)
                      (fun y =>
                        expect
                          (iter (relaxedProductiveCountdownStop B r n)
                            T (y, k))
                          (fun q =>
                            if q.2 = 0 ∨ B q.1 then F q.1 else 0)) ≤
                relaxedNonproductiveMassAt r n x *
                      expect
                        (iter
                          (freeze B (relaxedProductiveTriChain r n))
                          (k + 1) x)
                        F +
                  relaxedProductiveMassAt r n x *
                    expect (relaxedProductiveTriChain r n x) V := by
                exact add_le_add
                  (mul_le_mul_left' (ih (k + 1) x) _)
                  (mul_le_mul_left' hsmall _)
              _ =
                relaxedNonproductiveMassAt r n x *
                      expect
                        (iter
                          (freeze B (relaxedProductiveTriChain r n))
                          (k + 1) x)
                        F +
                  relaxedProductiveMassAt r n x *
                      expect
                        (iter
                          (freeze B (relaxedProductiveTriChain r n))
                          (k + 1) x)
                        F := by
                rw [htarget]
              _ =
                expect
                  (iter
                    (freeze B (relaxedProductiveTriChain r n))
                    (k + 1) x)
                  F := by
                rw [← add_mul, add_comm,
                  relaxedProductiveMassAt_add_nonproductiveMassAt,
                  one_mul]

/-- Killed exponential potential for a still-live relaxed countdown. -/
noncomputable def relaxedProductiveCountdownLivePotential
    (B : ℕ → Prop) [DecidablePred B] :
    ℕ × ℕ → ℝ≥0∞ :=
  fun q =>
    if B q.1 ∨ q.2 = 0 then 0 else (2 : ℝ≥0∞) ^ q.2

/-- A uniform productive-mass floor contracts the live countdown potential. -/
theorem relaxedProductiveCountdownStop_livePotential_super
    (B : ℕ → Prop) [DecidablePred B]
    (r : RelaxedRate) (n : ℕ)
    (p p' : ℝ≥0∞)
    (hp : p + p' = 1)
    (hpFloor :
      ∀ x, ¬ B x → p ≤ relaxedProductiveMassAt r n x) :
    ∀ q,
      expect (relaxedProductiveCountdownStop B r n q)
          (relaxedProductiveCountdownLivePotential B) ≤
        (p' + p * ((1 : ℝ≥0∞) / 2)) *
          relaxedProductiveCountdownLivePotential B q := by
  intro q
  rcases q with ⟨x, k⟩
  by_cases hB : B x
  · rw [relaxedProductiveCountdownStop, freeze_of_mem (x, k) hB,
      expect_pure]
    simp [relaxedProductiveCountdownLivePotential, hB]
  · cases k with
    | zero =>
        rw [relaxedProductiveCountdownStop_zero, expect_pure]
        simp [relaxedProductiveCountdownLivePotential, hB]
    | succ k =>
        rw [relaxedProductiveCountdownStop,
          freeze_of_not_mem (x, k + 1) hB,
          expect_relaxedProductiveCountdown_succ]
        have hproductive :
            expect (relaxedProductiveTriChain r n x)
                (fun y =>
                  relaxedProductiveCountdownLivePotential B (y, k)) ≤
              (2 : ℝ≥0∞) ^ k := by
          unfold expect
          calc
            (∑' y,
              relaxedProductiveTriChain r n x y *
                relaxedProductiveCountdownLivePotential B (y, k)) ≤
                ∑' y,
                  relaxedProductiveTriChain r n x y *
                    (2 : ℝ≥0∞) ^ k := by
              exact ENNReal.tsum_le_tsum fun y =>
                mul_le_mul_right
                  (by
                    unfold relaxedProductiveCountdownLivePotential
                    split_ifs <;> simp) _
            _ =
                (∑' y, relaxedProductiveTriChain r n x y) *
                  (2 : ℝ≥0∞) ^ k := by
              rw [ENNReal.tsum_mul_right]
            _ = (2 : ℝ≥0∞) ^ k := by
              rw [PMF.tsum_coe, one_mul]
        have hqsum :
            relaxedProductiveMassAt r n x +
                relaxedNonproductiveMassAt r n x = 1 :=
          relaxedProductiveMassAt_add_nonproductiveMassAt r n x
        have hfactor :=
          step_factor_antitone_ennreal hp hqsum
            (by norm_num : ((1 : ℝ≥0∞) / 2) ≤ 1)
            (hpFloor x hB)
        have hpow :
            (2 : ℝ≥0∞) ^ k =
              ((1 : ℝ≥0∞) / 2) * (2 : ℝ≥0∞) ^ (k + 1) := by
          have hhalfTwo :
              ((1 : ℝ≥0∞) / 2) * 2 = 1 := by
            calc
              ((1 : ℝ≥0∞) / 2) * 2 =
                  2 * ((1 : ℝ≥0∞) / 2) := by ring
              _ = 1 := by
                rw [one_div,
                  ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]
          symm
          calc
            ((1 : ℝ≥0∞) / 2) * (2 : ℝ≥0∞) ^ (k + 1) =
                ((1 : ℝ≥0∞) / 2) *
                  ((2 : ℝ≥0∞) ^ k * 2) := by rw [pow_succ]
            _ = (2 : ℝ≥0∞) ^ k *
                  (((1 : ℝ≥0∞) / 2) * 2) := by ring
            _ = (2 : ℝ≥0∞) ^ k := by rw [hhalfTwo, mul_one]
        simp only [relaxedProductiveCountdownLivePotential,
          hB, false_or, Nat.add_eq_zero_iff, one_ne_zero, and_false,
          if_false]
        calc
          relaxedNonproductiveMassAt r n x * (2 : ℝ≥0∞) ^ (k + 1) +
                relaxedProductiveMassAt r n x *
                  expect (relaxedProductiveTriChain r n x)
                    (fun y =>
                      relaxedProductiveCountdownLivePotential B (y, k)) ≤
              relaxedNonproductiveMassAt r n x *
                    (2 : ℝ≥0∞) ^ (k + 1) +
                relaxedProductiveMassAt r n x *
                    (2 : ℝ≥0∞) ^ k := by
            exact add_le_add le_rfl
              (mul_le_mul_left' hproductive _)
          _ =
              (relaxedNonproductiveMassAt r n x +
                  relaxedProductiveMassAt r n x *
                    ((1 : ℝ≥0∞) / 2)) *
                (2 : ℝ≥0∞) ^ (k + 1) := by
            rw [hpow]
            ring
          _ ≤
              (p' + p * ((1 : ℝ≥0∞) / 2)) *
                (2 : ℝ≥0∞) ^ (k + 1) :=
            mul_le_mul_left hfactor _

/-- Raw deadline tail for an arbitrary boundary and productive-mass floor. -/
theorem relaxedProductiveCountdownStop_live_tail
    (B : ℕ → Prop) [DecidablePred B]
    (r : RelaxedRate) (n : ℕ)
    (p p' : ℝ≥0∞)
    (hp : p + p' = 1)
    (hpFloor :
      ∀ x, ¬ B x → p ≤ relaxedProductiveMassAt r n x)
    (T M x₀ : ℕ) :
    (∑' q, if ¬ B q.1 ∧ q.2 ≠ 0 then
        iter (relaxedProductiveCountdownStop B r n)
          T (x₀, M) q else 0) ≤
      (p' + p * ((1 : ℝ≥0∞) / 2)) ^ T *
        (2 : ℝ≥0∞) ^ M := by
  let V : ℕ × ℕ → ℝ≥0∞ :=
    relaxedProductiveCountdownLivePotential B
  have hpoint : ∀ q,
      (if ¬ B q.1 ∧ q.2 ≠ 0 then
          iter (relaxedProductiveCountdownStop B r n)
            T (x₀, M) q else 0) ≤
        iter (relaxedProductiveCountdownStop B r n)
            T (x₀, M) q * V q := by
    intro q
    by_cases hq : ¬ B q.1 ∧ q.2 ≠ 0
    · have hpow : (1 : ℝ≥0∞) ≤ (2 : ℝ≥0∞) ^ q.2 :=
        one_le_pow₀ (by norm_num)
      rw [if_pos hq]
      change
        iter (relaxedProductiveCountdownStop B r n)
            T (x₀, M) q ≤
          iter (relaxedProductiveCountdownStop B r n)
              T (x₀, M) q *
            relaxedProductiveCountdownLivePotential B q
      rw [relaxedProductiveCountdownLivePotential,
        if_neg (by simp [hq.1, hq.2])]
      simpa only [mul_one] using
        mul_le_mul_right hpow
          (iter (relaxedProductiveCountdownStop B r n)
            T (x₀, M) q)
    · simp [hq]
  calc
    (∑' q, if ¬ B q.1 ∧ q.2 ≠ 0 then
        iter (relaxedProductiveCountdownStop B r n)
          T (x₀, M) q else 0) ≤
      expect
        (iter (relaxedProductiveCountdownStop B r n) T (x₀, M))
        V := by
          unfold expect
          exact ENNReal.tsum_le_tsum hpoint
    _ ≤
      (p' + p * ((1 : ℝ≥0∞) / 2)) ^ T * V (x₀, M) :=
        expect_iter_le
          (relaxedProductiveCountdownStop B r n) V
          (p' + p * ((1 : ℝ≥0∞) / 2))
          (by
            simpa only [V] using
              relaxedProductiveCountdownStop_livePotential_super
                B r n p p' hp hpFloor)
          T (x₀, M)
    _ ≤
      (p' + p * ((1 : ℝ≥0∞) / 2)) ^ T *
        (2 : ℝ≥0∞) ^ M := by
          apply mul_le_mul_left'
          unfold V relaxedProductiveCountdownLivePotential
          split_ifs <;> simp

/-- Exact raw/productive failure decomposition for a stopped countdown. -/
theorem relaxedProductiveCountdownStop_failure_le
    (A B : ℕ → Prop) [DecidablePred A] [DecidablePred B]
    (r : RelaxedRate) (n T M x₀ : ℕ) :
    terminalFailureMass
        (iter (relaxedProductiveCountdownStop B r n) T (x₀, M))
        (fun q => A q.1) ≤
      terminalFailureMass
          (iter (freeze B (relaxedProductiveTriChain r n)) M x₀) A +
        ∑' q, if ¬ B q.1 ∧ q.2 ≠ 0 then
          iter (relaxedProductiveCountdownStop B r n)
            T (x₀, M) q else 0 := by
  let μ :=
    iter (relaxedProductiveCountdownStop B r n) T (x₀, M)
  let F : ℕ → ℝ≥0∞ :=
    fun x => if A x then 0 else 1
  let R : ℕ × ℕ → Prop :=
    fun q => q.2 = 0 ∨ B q.1
  have hpoint : ∀ q,
      μ q * (if A q.1 then 0 else 1) ≤
        μ q * (if R q then F q.1 else 0) +
          (if ¬ B q.1 ∧ q.2 ≠ 0 then μ q else 0) := by
    intro q
    by_cases hA : A q.1
    · simp [hA]
    · by_cases hR : R q
      · simp [hA, hR, R, F]
      · have hLive : ¬ B q.1 ∧ q.2 ≠ 0 :=
          ⟨fun hB => hR (Or.inr hB),
            fun hzero => hR (Or.inl hzero)⟩
        simp [hA, hR, hLive, F]
  have hresolved :=
    relaxedProductiveCountdownStop_resolved_le B r n F T M x₀
  rw [terminalFailureMass_eq_expect,
    terminalFailureMass_eq_expect]
  calc
    expect μ (fun q => (if A q.1 then 0 else 1 : ℝ≥0∞)) ≤
        expect μ (fun q => if R q then F q.1 else 0) +
          ∑' q, if ¬ B q.1 ∧ q.2 ≠ 0 then μ q else 0 := by
      unfold expect
      rw [← ENNReal.tsum_add]
      exact ENNReal.tsum_le_tsum hpoint
    _ ≤
        expect
            (iter (freeze B (relaxedProductiveTriChain r n)) M x₀)
            F +
          ∑' q, if ¬ B q.1 ∧ q.2 ≠ 0 then μ q else 0 :=
      add_le_add
        (by simpa only [μ, R] using hresolved) le_rfl
    _ =
        expect
            (iter (freeze B (relaxedProductiveTriChain r n)) M x₀)
            (fun x => (if A x then 0 else 1 : ℝ≥0∞)) +
          ∑' q, if ¬ B q.1 ∧ q.2 ≠ 0 then μ q else 0 := rfl

/-- Failure after a raw deadline is bounded by productive-chain failure plus
the explicit Bernoulli clock expression. -/
theorem relaxedProductiveCountdownStop_failure_le_clock
    (A B : ℕ → Prop) [DecidablePred A] [DecidablePred B]
    (r : RelaxedRate) (n : ℕ)
    (p p' : ℝ≥0∞)
    (hp : p + p' = 1)
    (hpFloor :
      ∀ x, ¬ B x → p ≤ relaxedProductiveMassAt r n x)
    (T M x₀ : ℕ) :
    terminalFailureMass
        (iter (relaxedProductiveCountdownStop B r n) T (x₀, M))
        (fun q => A q.1) ≤
      terminalFailureMass
          (iter (freeze B (relaxedProductiveTriChain r n)) M x₀) A +
        (p' + p * ((1 : ℝ≥0∞) / 2)) ^ T *
          (2 : ℝ≥0∞) ^ M := by
  exact
    (relaxedProductiveCountdownStop_failure_le
      A B r n T M x₀).trans
      (add_le_add le_rfl
        (relaxedProductiveCountdownStop_live_tail
          B r n p p' hp hpFloor T M x₀))

/-- The global interior productive floor in `relaxedProductiveMassAt` form. -/
theorem relaxedProductiveFloor_le_massAt
    (r : RelaxedRate) (n x : ℕ)
    (h3 : 3 ≤ n) (hx0 : 0 < x) (hxn : x < n) :
    (r.fire : ℝ≥0∞) * ((3 : ℝ≥0∞) / (n : ℝ≥0∞)) ≤
      relaxedProductiveMassAt r n x := by
  unfold relaxedProductiveMassAt
  rw [dif_pos ⟨h3, hx0, hxn⟩]
  dsimp only
  exact relaxed_productive_mass_ge_interior
    r (x - 1) (n - x - 1) n h3 (by omega)

/-- On the live portion of Paper Lemma 7's band, the raw productive clock has
the global interior floor `r.fire · 3/n`. -/
theorem lemma7Stop_productiveFloor
    (r : RelaxedRate) (n P d : ℕ)
    (h3 : 3 ≤ n) (hroom : P + d < n) :
    ∀ x, ¬ Lemma7Stop n P d x →
      (r.fire : ℝ≥0∞) * ((3 : ℝ≥0∞) / (n : ℝ≥0∞)) ≤
        relaxedProductiveMassAt r n x := by
  intro x hstop
  obtain ⟨a, b, hx, hpop, _⟩ :=
    lemma7_live_interior hroom hstop
  rw [hx]
  exact relaxedProductiveFloor_le_massAt r n (a + 1)
    h3 (by omega) (by omega)

/-- Target failure in the chain frozen at `Target ∪ Escape` splits into its
escape mass and its still-live mass. -/
theorem lemma7_stop_target_failure_split
    (r : RelaxedRate) (n P d T x₀ : ℕ) :
    terminalFailureMass
        (iter
          (freeze (Lemma7Stop n P d)
            (relaxedProductiveTriChain r n))
          T x₀)
        (Lemma7Target n) ≤
      hitProb (Lemma7Escape n P d)
          (freeze (Lemma7Target n)
            (relaxedProductiveTriChain r n))
          T x₀ +
        terminalFailureMass
          (iter
            (freeze (Lemma7Stop n P d)
              (relaxedProductiveTriChain r n))
            T x₀)
          (Lemma7Stop n P d) := by
  classical
  let K := relaxedProductiveTriChain r n
  let μ := iter (freeze (Lemma7Stop n P d) K) T x₀
  have hfreeze :
      freeze (Lemma7Escape n P d)
          (freeze (Lemma7Target n) K) =
        freeze (Lemma7Stop n P d) K := by
    rw [freeze_escape_freeze_done]
    exact lemma7_freeze_congr K
      (fun x => Lemma7Target n x ∨ Lemma7Escape n P d x)
      (Lemma7Stop n P d) (fun _ => Iff.rfl)
  rw [terminalFailureMass_eq_expect,
    terminalFailureMass_eq_expect]
  unfold hitProb
  rw [hfreeze]
  change
    expect μ
        (fun x =>
          (if Lemma7Target n x then 0 else 1 : ℝ≥0∞)) ≤
      expect μ (ind (Lemma7Escape n P d)) +
        expect μ
          (fun x =>
            (if Lemma7Stop n P d x then 0 else 1 : ℝ≥0∞))
  unfold expect
  rw [← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun x => ?_
  unfold ind Lemma7Stop
  by_cases ht : Lemma7Target n x
  · simp [ht]
  · by_cases he : Lemma7Escape n P d x
    · simp [ht, he]
    · simp [ht, he]

/-- Productive-clock Lemma 7 in the exact stopped-boundary form required by
the raw countdown. -/
theorem lemma7_stopped
    (r : RelaxedRate) (β : NNReal) (n P d x₀ T b : ℕ)
    (h3 : 3 ≤ n) (hroom : P + d < n)
    (hβgt : (1 : NNReal) < β) (_hβ2 : β ≤ 2)
    (hx₀n : x₀ ≤ n)
    (hstart : phase3Level n x₀ = lemma7EscapeBound n P d + b)
    (hguard :
      ∀ a b : ℕ, a + b + 2 = n → ¬ Lemma7Stop n P d (a + 1) →
        β * (b + 1 : NNReal) ≤ r.fire * (a + 1 : NNReal))
    (hprodLive :
      ∀ a b : ℕ, (hpop : a + b + 2 = n) →
        ¬ Lemma7Stop n P d (a + 1) →
        relaxedTriStep r (a + 1) (b + 1) (by omega) a +
            relaxedTriStep r (a + 1) (b + 1) (by omega) (a + 2) ≠ 0) :
    terminalFailureMass
        (iter
          (freeze (Lemma7Stop n P d)
            (relaxedProductiveTriChain r n))
          T x₀)
        (Lemma7Target n) ≤
      ((β : ℝ≥0∞)⁻¹) ^ b +
        lemma7DeadlinePhi β ^ T *
          (if Lemma7Stop n P d x₀ then 0
            else lemma7DeadlineW β ^ x₀) /
            lemma7DeadlineW β ^ n := by
  have hsplit :=
    lemma7_stop_target_failure_split r n P d T x₀
  exact hsplit.trans
    (add_le_add
      (lemma7_escape_branch r β n P d x₀ T b
        h3 hroom (le_of_lt hβgt) hstart hguard hprodLive)
      (lemma7_deadline_branch r β n P d x₀ T
        h3 hroom (le_of_lt hβgt) hx₀n hguard hprodLive))

/-- Full raw-clock bridge for Paper Lemma 7.  The first two terms are the
productive-chain error; the last term is the explicit raw-clock error. -/
theorem lemma7_raw
    (r : RelaxedRate) (β : NNReal)
    (n P d x₀ M T b : ℕ)
    (h3 : 3 ≤ n) (hroom : P + d < n)
    (hβgt : (1 : NNReal) < β) (hβ2 : β ≤ 2)
    (hx₀n : x₀ ≤ n)
    (hstartLive : ¬ Lemma7Stop n P d x₀)
    (hstart : phase3Level n x₀ = lemma7EscapeBound n P d + b)
    (hguard :
      ∀ a b : ℕ, a + b + 2 = n → ¬ Lemma7Stop n P d (a + 1) →
        β * (b + 1 : NNReal) ≤ r.fire * (a + 1 : NNReal))
    (hprodLive :
      ∀ a b : ℕ, (hpop : a + b + 2 = n) →
        ¬ Lemma7Stop n P d (a + 1) →
        relaxedTriStep r (a + 1) (b + 1) (by omega) a +
            relaxedTriStep r (a + 1) (b + 1) (by omega) (a + 2) ≠ 0) :
    terminalFailureMass
        (iter
          (freeze (Lemma7Target n) (relaxedTriChain r n))
          T x₀)
        (Lemma7Target n) ≤
      ((β : ℝ≥0∞)⁻¹) ^ b +
        lemma7DeadlinePhi β ^ M *
          lemma7DeadlineW β ^ x₀ /
            lemma7DeadlineW β ^ n +
        ((1 -
            (r.fire : ℝ≥0∞) *
              ((3 : ℝ≥0∞) / (n : ℝ≥0∞))) +
          (r.fire : ℝ≥0∞) *
              ((3 : ℝ≥0∞) / (n : ℝ≥0∞)) *
            ((1 : ℝ≥0∞) / 2)) ^ T *
          (2 : ℝ≥0∞) ^ M := by
  let p : ℝ≥0∞ :=
    (r.fire : ℝ≥0∞) * ((3 : ℝ≥0∞) / (n : ℝ≥0∞))
  let p' : ℝ≥0∞ := 1 - p
  have hpFloor :
      ∀ x, ¬ Lemma7Stop n P d x →
        p ≤ relaxedProductiveMassAt r n x :=
    lemma7Stop_productiveFloor r n P d h3 hroom
  have hpLe : p ≤ 1 := by
    calc
      p ≤ relaxedProductiveMassAt r n x₀ :=
        hpFloor x₀ hstartLive
      _ ≤
          relaxedProductiveMassAt r n x₀ +
            relaxedNonproductiveMassAt r n x₀ :=
        le_add_right le_rfl
      _ = 1 :=
        relaxedProductiveMassAt_add_nonproductiveMassAt r n x₀
  have hp : p + p' = 1 := by
    dsimp only [p']
    rw [add_comm]
    exact tsub_add_cancel_of_le hpLe
  have hphysical :=
    relaxedTriChain_targetFailure_le_productiveCountdownStop
      (Lemma7Target n) (Lemma7Stop n P d) r n T M x₀
  have hclock :=
    relaxedProductiveCountdownStop_failure_le_clock
      (Lemma7Target n) (Lemma7Stop n P d)
      r n p p' hp hpFloor T M x₀
  have hproductive :=
    lemma7_stopped r β n P d x₀ M b h3 hroom hβgt hβ2
      hx₀n hstart hguard hprodLive
  calc
    terminalFailureMass
        (iter
          (freeze (Lemma7Target n) (relaxedTriChain r n))
          T x₀)
        (Lemma7Target n) ≤
      terminalFailureMass
        (iter
          (relaxedProductiveCountdownStop
            (Lemma7Stop n P d) r n)
          T (x₀, M))
        (fun q => Lemma7Target n q.1) :=
      hphysical
    _ ≤
      terminalFailureMass
          (iter
            (freeze (Lemma7Stop n P d)
              (relaxedProductiveTriChain r n))
            M x₀)
          (Lemma7Target n) +
        (p' + p * ((1 : ℝ≥0∞) / 2)) ^ T *
          (2 : ℝ≥0∞) ^ M :=
      hclock
    _ ≤
      (((β : ℝ≥0∞)⁻¹) ^ b +
        lemma7DeadlinePhi β ^ M *
          (if Lemma7Stop n P d x₀ then 0
            else lemma7DeadlineW β ^ x₀) /
            lemma7DeadlineW β ^ n) +
        (p' + p * ((1 : ℝ≥0∞) / 2)) ^ T *
          (2 : ℝ≥0∞) ^ M :=
      add_le_add hproductive le_rfl
    _ = _ := by
      rw [if_neg hstartLive]

end Tri

#print axioms Tri.relaxedProductiveMassAt_add_nonproductiveMassAt
#print axioms Tri.relaxedProductiveCountdown_succ_map_fst
#print axioms Tri.expect_relaxedProductiveCountdown_succ
#print axioms Tri.relaxedProductiveCountdownStop_isLazyProjection
#print axioms Tri.relaxedTriChain_targetFailure_le_productiveCountdownStop
#print axioms Tri.relaxedProductiveCountdownStop_resolved_le
#print axioms Tri.relaxedProductiveCountdownStop_livePotential_super
#print axioms Tri.relaxedProductiveCountdownStop_live_tail
#print axioms Tri.relaxedProductiveCountdownStop_failure_le
#print axioms Tri.relaxedProductiveCountdownStop_failure_le_clock
#print axioms Tri.relaxedProductiveFloor_le_massAt
#print axioms Tri.lemma7Stop_productiveFloor
#print axioms Tri.lemma7_stop_target_failure_split
#print axioms Tri.lemma7_stopped
#print axioms Tri.lemma7_raw
