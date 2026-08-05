/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.MultiProductivePair
import Tri.LazyHitting

/-!
# A counted time change for productive reactions

The physical chain is a state-dependent mixture of an inert self-loop and
one step of the conditioned productive chain.  This file records that
decomposition with a decreasing productive-event counter and proves the
finite-horizon comparison needed to pass from productive-event time to raw
interaction time.
-/

namespace Tri.Multi

open scoped BigOperators ENNReal

variable {m n : ℕ}

/-- The physical sampler equipped with a remaining-productive-events counter.
At zero the chain is frozen; otherwise a productive sample decrements the
counter and an inert sample leaves the state and counter unchanged. -/
noncomputable def productiveCountdown
    (h3 : 3 ≤ n) :
    Config m n × ℕ → PMF (Config m n × ℕ)
  | q@(_, 0) => PMF.pure q
  | (c, r + 1) =>
      (triplePMF c h3).map fun t =>
        if IsProductiveSample t then
          (sampleNext c t, r)
        else
          (c, r + 1)

@[simp] theorem productiveCountdown_zero
    (h3 : 3 ≤ n) (c : Config m n) :
    productiveCountdown h3 (c, 0) = PMF.pure (c, 0) :=
  rfl

/-- Forgetting the countdown after a positive-counter step gives exactly one
physical interaction. -/
theorem productiveCountdown_succ_map_fst
    (h3 : 3 ≤ n) (c : Config m n) (r : ℕ) :
    (productiveCountdown h3 (c, r + 1)).map Prod.fst =
      multiStep c h3 := by
  classical
  unfold productiveCountdown multiStep
  rw [PMF.map_comp]
  apply congrArg (fun f => (triplePMF c h3).map f)
  funext t
  by_cases ht : IsProductiveSample t
  · simp [ht]
  · have hclass : classify t = none := by
      simpa [IsProductiveSample] using ht
    have hnext : sampleNext c t = c := by
      unfold sampleNext
      rw [hclass]
    simp [ht, hnext]

/-- Exact one-step mixture formula for the productive countdown. -/
theorem expect_productiveCountdown_succ
    (c : Config m n) (h3 : 3 ≤ n) (r : ℕ)
    (G : Config m n × ℕ → ℝ≥0∞) :
    expect (productiveCountdown h3 (c, r + 1)) G =
      nonproductiveMass c h3 * G (c, r + 1) +
        productiveMass c h3 *
          expect (productiveStep h3 c) (fun d => G (d, r)) := by
  classical
  by_cases hprod : productiveMass c h3 = 0
  · have hzero :
        ∀ t : TripleSample c,
          IsProductiveSample t → triplePMF c h3 t = 0 := by
      intro t ht
      have hsum :
          (∑' u : TripleSample c,
            if IsProductiveSample u then triplePMF c h3 u else 0) = 0 := by
        simpa only [productiveMass] using hprod
      have hterm := ENNReal.tsum_eq_zero.mp hsum t
      simpa [ht] using hterm
    unfold productiveCountdown
    rw [expect_map]
    unfold expect nonproductiveMass
    simp only [tsum_fintype]
    rw [hprod, zero_mul, add_zero]
    calc
      ∑ t : TripleSample c,
          triplePMF c h3 t *
            G (if IsProductiveSample t then
              (sampleNext c t, r) else (c, r + 1)) =
        ∑ t : TripleSample c,
          (if IsProductiveSample t then 0 else triplePMF c h3 t) *
            G (c, r + 1) := by
              apply Finset.sum_congr rfl
              intro t _ht
              by_cases ht : IsProductiveSample t
              · simp [ht, hzero t ht]
              · simp [ht]
      _ =
        (∑ t : TripleSample c,
          if IsProductiveSample t then 0 else triplePMF c h3 t) *
            G (c, r + 1) := by
              rw [Finset.sum_mul]
  · have hPtop : productiveMass c h3 ≠ ∞ :=
      ne_top_of_le_ne_top ENNReal.one_ne_top
        (productiveMass_le_one c h3)
    rw [productiveStep_of_mass_ne_zero h3 c hprod, expect_map,
      expect_productiveSamplePMF]
    unfold productiveCountdown
    rw [expect_map]
    unfold expect nonproductiveMass
    simp only [tsum_fintype]
    rw [ENNReal.mul_div_cancel hprod hPtop]
    calc
      ∑ t : TripleSample c,
          triplePMF c h3 t *
            G (if IsProductiveSample t then
              (sampleNext c t, r) else (c, r + 1)) =
        ∑ t : TripleSample c,
          ((if IsProductiveSample t then 0 else triplePMF c h3 t) *
              G (c, r + 1) +
            if IsProductiveSample t then
              triplePMF c h3 t * G (sampleNext c t, r) else 0) := by
                apply Finset.sum_congr rfl
                intro t _ht
                by_cases ht : IsProductiveSample t <;> simp [ht]
      _ =
        (∑ t : TripleSample c,
          if IsProductiveSample t then 0 else triplePMF c h3 t) *
              G (c, r + 1) +
          ∑ t : TripleSample c,
            if IsProductiveSample t then
              triplePMF c h3 t * G (sampleNext c t, r) else 0 := by
                rw [Finset.sum_add_distrib, Finset.sum_mul]

/-- A run that completes `r` productive reactions has no more mass under a
productive-chain superharmonic terminal cost than `r` direct productive
steps.  Paths that have not completed the countdown contribute zero. -/
theorem productiveCountdown_completion_le
    (h3 : 3 ≤ n) (F : Config m n → ℝ≥0∞) :
    ∀ T r (c : Config m n),
      expect (iter (productiveCountdown h3) T (c, r))
          (fun q => if q.2 = 0 then F q.1 else 0) ≤
        expect (iter (productiveStep h3) r c) F := by
  intro T
  induction T with
  | zero =>
      intro r c
      cases r <;> simp [iter]
  | succ T ih =>
      intro r c
      cases r with
      | zero =>
          rw [iter_succ, productiveCountdown_zero, PMF.pure_bind]
          simpa [iter] using ih 0 c
      | succ r =>
          rw [iter_succ, expect_bind]
          change
            expect (productiveCountdown h3 (c, r + 1))
                (fun a =>
                  expect (iter (productiveCountdown h3) T a)
                    (fun q => if q.2 = 0 then F q.1 else 0)) ≤
              expect (iter (productiveStep h3) (r + 1) c) F
          rw [expect_productiveCountdown_succ]
          let V : Config m n → ℝ≥0∞ := fun d =>
            expect (iter (productiveStep h3) r d) F
          have hsmall :
              expect (productiveStep h3 c)
                  (fun d =>
                    expect (iter (productiveCountdown h3) T (d, r))
                      (fun q => if q.2 = 0 then F q.1 else 0)) ≤
                expect (productiveStep h3 c) V := by
            unfold expect
            exact ENNReal.tsum_le_tsum fun d =>
              mul_le_mul_right (ih r d) _
          have htarget :
              expect (iter (productiveStep h3) (r + 1) c) F =
                expect (productiveStep h3 c) V := by
            rw [iter_succ, expect_bind]
            rfl
          calc
            nonproductiveMass c h3 *
                  expect
                    (iter (productiveCountdown h3) T (c, r + 1))
                    (fun q => if q.2 = 0 then F q.1 else 0) +
                productiveMass c h3 *
                  expect (productiveStep h3 c)
                    (fun d =>
                      expect
                        (iter (productiveCountdown h3) T (d, r))
                        (fun q => if q.2 = 0 then F q.1 else 0)) ≤
              nonproductiveMass c h3 *
                    expect (iter (productiveStep h3) (r + 1) c) F +
                productiveMass c h3 *
                    expect (productiveStep h3 c) V := by
                      exact add_le_add
                        (mul_le_mul_left' (ih (r + 1) c) _)
                        (mul_le_mul_left' hsmall _)
            _ =
              nonproductiveMass c h3 *
                    expect (iter (productiveStep h3) (r + 1) c) F +
                productiveMass c h3 *
                    expect (iter (productiveStep h3) (r + 1) c) F := by
                      rw [htarget]
            _ = expect (iter (productiveStep h3) (r + 1) c) F := by
              rw [← add_mul, add_comm,
                productiveMass_add_nonproductiveMass, one_mul]

/-- Freeze the productive countdown when a configuration boundary is reached. -/
noncomputable def productiveCountdownStop
    (B : Config m n → Prop) [DecidablePred B]
    (h3 : 3 ≤ n) :
    Config m n × ℕ → PMF (Config m n × ℕ) :=
  freeze (fun q => B q.1) (productiveCountdown h3)

/-- The stopped countdown projects either to one physical interaction or to a
self-loop. -/
theorem productiveCountdownStop_isLazyProjection
    (B : Config m n → Prop) [DecidablePred B]
    (h3 : 3 ≤ n) :
    IsLazyProjection (fun c => multiStep c h3)
      (productiveCountdownStop B h3) Prod.fst := by
  classical
  intro q
  rcases q with ⟨c, r⟩
  by_cases hB : B c
  · right
    rw [productiveCountdownStop, freeze_of_mem (c, r) hB]
    exact PMF.pure_map Prod.fst (c, r)
  · rw [productiveCountdownStop, freeze_of_not_mem (c, r) hB]
    cases r with
    | zero =>
        right
        rw [productiveCountdown_zero]
        exact PMF.pure_map Prod.fst (c, 0)
    | succ r =>
        left
        exact productiveCountdown_succ_map_fst h3 c r

/-- The physical raw chain hits any configuration target at least as readily
as the boundary-stopped countdown with the same raw horizon. -/
theorem multiStep_targetFailure_le_productiveCountdownStop
    (A B : Config m n → Prop)
    [DecidablePred A] [DecidablePred B]
    (h3 : 3 ≤ n) (T M : ℕ) (c0 : Config m n) :
    terminalFailureMass
        (iter (freeze A (fun c => multiStep c h3)) T c0) A ≤
      terminalFailureMass
        (iter (productiveCountdownStop B h3) T (c0, M))
        (fun q => A q.1) := by
  exact targetFreeze_failure_le_lazy_projection
    A (fun c => multiStep c h3) (productiveCountdownStop B h3)
    Prod.fst (productiveCountdownStop_isLazyProjection B h3) T (c0, M)

@[simp] theorem productiveCountdownStop_zero
    (B : Config m n → Prop) [DecidablePred B]
    (h3 : 3 ≤ n) (c : Config m n) :
    productiveCountdownStop B h3 (c, 0) = PMF.pure (c, 0) := by
  by_cases hB : B c
  · exact freeze_of_mem (c, 0) hB
  · rw [productiveCountdownStop, freeze_of_not_mem (c, 0) hB,
      productiveCountdown_zero]

/-- At a boundary state, every stopped-countdown iterate is a self-loop. -/
theorem iter_productiveCountdownStop_of_boundary
    (B : Config m n → Prop) [DecidablePred B]
    (h3 : 3 ≤ n) (c : Config m n) (r : ℕ)
    (hB : B c) :
    ∀ T,
      iter (productiveCountdownStop B h3) T (c, r) =
        PMF.pure (c, r) := by
  intro T
  exact iter_targetFreeze_of_mem
    (fun q : Config m n × ℕ => B q.1)
    (productiveCountdown h3) (c, r) hB T

/-- A stopped raw countdown that either reaches its configuration boundary or
completes `r` productive reactions has no more terminal cost than `r` steps of
the productive chain stopped on the same boundary. -/
theorem productiveCountdownStop_resolved_le
    (B : Config m n → Prop) [DecidablePred B]
    (h3 : 3 ≤ n) (F : Config m n → ℝ≥0∞) :
    ∀ T r (c : Config m n),
      expect (iter (productiveCountdownStop B h3) T (c, r))
          (fun q => if q.2 = 0 ∨ B q.1 then F q.1 else 0) ≤
        expect (iter (freeze B (productiveStep h3)) r c) F := by
  intro T
  induction T with
  | zero =>
      intro r c
      cases r with
      | zero => simp [iter]
      | succ r =>
          by_cases hB : B c
          · rw [iter_targetFreeze_of_mem B (productiveStep h3) c hB (r + 1)]
            simp [iter, hB]
          · simp [iter, hB]
  | succ T ih =>
      intro r c
      cases r with
      | zero =>
          rw [iter_succ, productiveCountdownStop_zero, PMF.pure_bind]
          simpa [iter] using ih 0 c
      | succ r =>
          by_cases hB : B c
          · rw [iter_productiveCountdownStop_of_boundary B h3 c (r + 1) hB,
              iter_targetFreeze_of_mem B (productiveStep h3) c hB (r + 1)]
            simp [hB]
          · rw [iter_succ, expect_bind]
            change
              expect (productiveCountdownStop B h3 (c, r + 1))
                  (fun a =>
                    expect (iter (productiveCountdownStop B h3) T a)
                      (fun q =>
                        if q.2 = 0 ∨ B q.1 then F q.1 else 0)) ≤
                expect
                  (iter (freeze B (productiveStep h3)) (r + 1) c) F
            rw [productiveCountdownStop, freeze_of_not_mem (c, r + 1) hB,
              expect_productiveCountdown_succ]
            let V : Config m n → ℝ≥0∞ := fun d =>
              expect (iter (freeze B (productiveStep h3)) r d) F
            have hsmall :
                expect (productiveStep h3 c)
                    (fun d =>
                      expect
                        (iter (productiveCountdownStop B h3) T (d, r))
                        (fun q =>
                          if q.2 = 0 ∨ B q.1 then F q.1 else 0)) ≤
                  expect (productiveStep h3 c) V := by
              unfold expect
              exact ENNReal.tsum_le_tsum fun d =>
                mul_le_mul_right (ih r d) _
            have htarget :
                expect
                    (iter (freeze B (productiveStep h3)) (r + 1) c) F =
                  expect (productiveStep h3 c) V := by
              rw [iter_succ, freeze_of_not_mem c hB, expect_bind]
              rfl
            calc
              nonproductiveMass c h3 *
                    expect
                      (iter (productiveCountdownStop B h3) T (c, r + 1))
                      (fun q =>
                        if q.2 = 0 ∨ B q.1 then F q.1 else 0) +
                  productiveMass c h3 *
                    expect (productiveStep h3 c)
                      (fun d =>
                        expect
                          (iter (productiveCountdownStop B h3) T (d, r))
                          (fun q =>
                            if q.2 = 0 ∨ B q.1 then F q.1 else 0)) ≤
                nonproductiveMass c h3 *
                      expect
                        (iter (freeze B (productiveStep h3)) (r + 1) c) F +
                  productiveMass c h3 *
                      expect (productiveStep h3 c) V := by
                        exact add_le_add
                          (mul_le_mul_left' (ih (r + 1) c) _)
                          (mul_le_mul_left' hsmall _)
              _ =
                nonproductiveMass c h3 *
                      expect
                        (iter (freeze B (productiveStep h3)) (r + 1) c) F +
                  productiveMass c h3 *
                      expect
                        (iter (freeze B (productiveStep h3)) (r + 1) c) F := by
                        rw [htarget]
              _ =
                expect
                  (iter (freeze B (productiveStep h3)) (r + 1) c) F := by
                rw [← add_mul, add_comm,
                  productiveMass_add_nonproductiveMass, one_mul]

/-- Killed exponential potential for a still-live productive countdown. -/
noncomputable def productiveCountdownLivePotential
    (B : Config m n → Prop) [DecidablePred B] :
    Config m n × ℕ → ℝ≥0∞ :=
  fun q =>
    if B q.1 ∨ q.2 = 0 then 0 else (2 : ℝ≥0∞) ^ q.2

/-- A uniform productive-mass floor contracts the live countdown potential.
The factor is the same Bernoulli factor as for the increasing productive
counter at the test value `w = 1/2`. -/
theorem productiveCountdownStop_livePotential_super
    (B : Config m n → Prop) [DecidablePred B]
    (h3 : 3 ≤ n) (p p' : ℝ≥0∞)
    (hp : p + p' = 1)
    (hpFloor : ∀ c, ¬ B c → p ≤ productiveMass c h3) :
    ∀ q,
      expect (productiveCountdownStop B h3 q)
          (productiveCountdownLivePotential B) ≤
        (p' + p * ((1 : ℝ≥0∞) / 2)) *
          productiveCountdownLivePotential B q := by
  intro q
  rcases q with ⟨c, r⟩
  by_cases hB : B c
  · rw [productiveCountdownStop, freeze_of_mem (c, r) hB, expect_pure]
    simp [productiveCountdownLivePotential, hB]
  · cases r with
    | zero =>
        rw [productiveCountdownStop_zero, expect_pure]
        simp [productiveCountdownLivePotential, hB]
    | succ r =>
        rw [productiveCountdownStop, freeze_of_not_mem (c, r + 1) hB,
          expect_productiveCountdown_succ]
        have hproductive :
            expect (productiveStep h3 c)
                (fun d =>
                  productiveCountdownLivePotential B (d, r)) ≤
              (2 : ℝ≥0∞) ^ r := by
          unfold expect
          calc
            (∑' d,
              productiveStep h3 c d *
                productiveCountdownLivePotential B (d, r)) ≤
                ∑' d,
                  productiveStep h3 c d * (2 : ℝ≥0∞) ^ r := by
                    exact ENNReal.tsum_le_tsum fun d =>
                      mul_le_mul_right
                        (by
                          unfold productiveCountdownLivePotential
                          split_ifs <;> simp) _
            _ = (∑' d, productiveStep h3 c d) *
                (2 : ℝ≥0∞) ^ r := by
                  rw [ENNReal.tsum_mul_right]
            _ = (2 : ℝ≥0∞) ^ r := by
                  rw [PMF.tsum_coe, one_mul]
        have hqsum :
            productiveMass c h3 + nonproductiveMass c h3 = 1 :=
          productiveMass_add_nonproductiveMass c h3
        have hfactor :=
          step_factor_antitone_ennreal hp hqsum
            (by norm_num : ((1 : ℝ≥0∞) / 2) ≤ 1)
            (hpFloor c hB)
        have hpow :
            (2 : ℝ≥0∞) ^ r =
              ((1 : ℝ≥0∞) / 2) * (2 : ℝ≥0∞) ^ (r + 1) := by
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
            ((1 : ℝ≥0∞) / 2) * (2 : ℝ≥0∞) ^ (r + 1) =
                ((1 : ℝ≥0∞) / 2) *
                  ((2 : ℝ≥0∞) ^ r * 2) := by rw [pow_succ]
            _ = (2 : ℝ≥0∞) ^ r *
                  (((1 : ℝ≥0∞) / 2) * 2) := by ring
            _ = (2 : ℝ≥0∞) ^ r := by rw [hhalfTwo, mul_one]
        simp only [productiveCountdownLivePotential, hB, false_or,
          Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false]
        calc
          nonproductiveMass c h3 * (2 : ℝ≥0∞) ^ (r + 1) +
                productiveMass c h3 *
                  expect (productiveStep h3 c)
                    (fun d =>
                      productiveCountdownLivePotential B (d, r)) ≤
              nonproductiveMass c h3 * (2 : ℝ≥0∞) ^ (r + 1) +
                productiveMass c h3 * (2 : ℝ≥0∞) ^ r := by
                  exact add_le_add le_rfl
                    (mul_le_mul_left' hproductive _)
          _ =
              (nonproductiveMass c h3 +
                  productiveMass c h3 * ((1 : ℝ≥0∞) / 2)) *
                (2 : ℝ≥0∞) ^ (r + 1) := by
                  rw [hpow]
                  ring
          _ ≤
              (p' + p * ((1 : ℝ≥0∞) / 2)) *
                (2 : ℝ≥0∞) ^ (r + 1) :=
            mul_le_mul_left hfactor _

/-- Raw deadline tail for a productive countdown under an arbitrary
configuration boundary and productive-mass floor. -/
theorem productiveCountdownStop_live_tail
    (B : Config m n → Prop) [DecidablePred B]
    (h3 : 3 ≤ n) (p p' : ℝ≥0∞)
    (hp : p + p' = 1)
    (hpFloor : ∀ c, ¬ B c → p ≤ productiveMass c h3)
    (T M : ℕ) (c0 : Config m n) :
    (∑' q, if ¬ B q.1 ∧ q.2 ≠ 0 then
        iter (productiveCountdownStop B h3) T (c0, M) q else 0) ≤
      (p' + p * ((1 : ℝ≥0∞) / 2)) ^ T *
        (2 : ℝ≥0∞) ^ M := by
  let V : Config m n × ℕ → ℝ≥0∞ :=
    productiveCountdownLivePotential B
  have hpoint : ∀ q,
      (if ¬ B q.1 ∧ q.2 ≠ 0 then
          iter (productiveCountdownStop B h3) T (c0, M) q else 0) ≤
        iter (productiveCountdownStop B h3) T (c0, M) q * V q := by
    intro q
    by_cases hq : ¬ B q.1 ∧ q.2 ≠ 0
    · have hr : 1 ≤ q.2 := Nat.one_le_iff_ne_zero.mpr hq.2
      have hpow : (1 : ℝ≥0∞) ≤ (2 : ℝ≥0∞) ^ q.2 := by
        exact one_le_pow₀ (by norm_num)
      rw [if_pos hq]
      change
        iter (productiveCountdownStop B h3) T (c0, M) q ≤
          iter (productiveCountdownStop B h3) T (c0, M) q *
            productiveCountdownLivePotential B q
      rw [productiveCountdownLivePotential,
        if_neg (by simp [hq.1, hq.2])]
      simpa only [mul_one] using
        mul_le_mul_right hpow
          (iter (productiveCountdownStop B h3) T (c0, M) q)
    · simp [hq]
  calc
    (∑' q, if ¬ B q.1 ∧ q.2 ≠ 0 then
        iter (productiveCountdownStop B h3) T (c0, M) q else 0) ≤
      expect (iter (productiveCountdownStop B h3) T (c0, M)) V := by
        unfold expect
        exact ENNReal.tsum_le_tsum hpoint
    _ ≤
      (p' + p * ((1 : ℝ≥0∞) / 2)) ^ T * V (c0, M) :=
        expect_iter_le
          (productiveCountdownStop B h3) V
          (p' + p * ((1 : ℝ≥0∞) / 2))
          (by
            simpa only [V] using
              productiveCountdownStop_livePotential_super
                B h3 p p' hp hpFloor)
          T (c0, M)
    _ ≤
      (p' + p * ((1 : ℝ≥0∞) / 2)) ^ T *
        (2 : ℝ≥0∞) ^ M := by
          apply mul_le_mul_left'
          unfold V productiveCountdownLivePotential
          split_ifs <;> simp

/-- Exact raw/productive failure decomposition for a stopped countdown.
Unresolved live paths are charged to the raw clock; every resolved path is
charged to the same boundary-stopped productive chain. -/
theorem productiveCountdownStop_failure_le
    (A B : Config m n → Prop)
    [DecidablePred A] [DecidablePred B]
    (h3 : 3 ≤ n) (T M : ℕ) (c0 : Config m n) :
    terminalFailureMass
        (iter (productiveCountdownStop B h3) T (c0, M))
        (fun q => A q.1) ≤
      terminalFailureMass
          (iter (freeze B (productiveStep h3)) M c0) A +
        ∑' q, if ¬ B q.1 ∧ q.2 ≠ 0 then
          iter (productiveCountdownStop B h3) T (c0, M) q else 0 := by
  let p :=
    iter (productiveCountdownStop B h3) T (c0, M)
  let F : Config m n → ℝ≥0∞ :=
    fun c => if A c then 0 else 1
  let R : Config m n × ℕ → Prop :=
    fun q => q.2 = 0 ∨ B q.1
  have hpoint : ∀ q,
      p q * (if A q.1 then 0 else 1) ≤
        p q * (if R q then F q.1 else 0) +
          (if ¬ B q.1 ∧ q.2 ≠ 0 then p q else 0) := by
    intro q
    by_cases hA : A q.1
    · simp [hA]
    · by_cases hR : R q
      · simp [hA, hR, R, F]
      · have hLive : ¬ B q.1 ∧ q.2 ≠ 0 := by
          exact
            ⟨(fun hB => hR (Or.inr hB)),
              (fun hzero => hR (Or.inl hzero))⟩
        simp [hA, hR, hLive, F]
  have hresolved :=
    productiveCountdownStop_resolved_le B h3 F T M c0
  rw [terminalFailureMass_eq_expect,
    terminalFailureMass_eq_expect]
  calc
    expect p (fun q => (if A q.1 then 0 else 1 : ℝ≥0∞)) ≤
        expect p (fun q => if R q then F q.1 else 0) +
          ∑' q, if ¬ B q.1 ∧ q.2 ≠ 0 then p q else 0 := by
            unfold expect
            rw [← ENNReal.tsum_add]
            exact ENNReal.tsum_le_tsum hpoint
    _ ≤
        expect (iter (freeze B (productiveStep h3)) M c0) F +
          ∑' q, if ¬ B q.1 ∧ q.2 ≠ 0 then p q else 0 :=
      add_le_add
        (by simpa only [p, R] using hresolved) le_rfl
    _ =
        expect (iter (freeze B (productiveStep h3)) M c0)
            (fun c => (if A c then 0 else 1 : ℝ≥0∞)) +
          ∑' q, if ¬ B q.1 ∧ q.2 ≠ 0 then p q else 0 := rfl

/-- Failure after a raw deadline is bounded by productive-chain failure plus
the explicit Bernoulli clock expression. -/
theorem productiveCountdownStop_failure_le_clock
    (A B : Config m n → Prop)
    [DecidablePred A] [DecidablePred B]
    (h3 : 3 ≤ n) (p p' : ℝ≥0∞)
    (hp : p + p' = 1)
    (hpFloor : ∀ c, ¬ B c → p ≤ productiveMass c h3)
    (T M : ℕ) (c0 : Config m n) :
    terminalFailureMass
        (iter (productiveCountdownStop B h3) T (c0, M))
        (fun q => A q.1) ≤
      terminalFailureMass
          (iter (freeze B (productiveStep h3)) M c0) A +
        (p' + p * ((1 : ℝ≥0∞) / 2)) ^ T *
          (2 : ℝ≥0∞) ^ M := by
  exact (productiveCountdownStop_failure_le A B h3 T M c0).trans
    (add_le_add le_rfl
      (productiveCountdownStop_live_tail
        B h3 p p' hp hpFloor T M c0))

end Tri.Multi

#print axioms Tri.Multi.expect_productiveCountdown_succ
#print axioms Tri.Multi.productiveCountdown_succ_map_fst
#print axioms Tri.Multi.productiveCountdownStop_isLazyProjection
#print axioms Tri.Multi.multiStep_targetFailure_le_productiveCountdownStop
#print axioms Tri.Multi.productiveCountdown_completion_le
#print axioms Tri.Multi.productiveCountdownStop_resolved_le
#print axioms Tri.Multi.productiveCountdownStop_live_tail
#print axioms Tri.Multi.productiveCountdownStop_failure_le_clock
