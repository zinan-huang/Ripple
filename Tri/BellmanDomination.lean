/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.HitProbMono

/-!
# Bellman domination for target-before-failure probabilities

The comparison used by the Byzantine ladder is not a comparison of expected
drifts.  It is a first-order stochastic-domination statement against every
increasing test function, iterated through the stopped Bellman recurrence.  The
reference chain stops on the lower failure set and the upper target set; the
controlled chain may depend on arbitrary external history.
-/

namespace Tri

open scoped ENNReal

variable {L H : Type*}

/-- If a nonnegative observable is bounded by one pointwise, then so is its
expectation under any PMF. -/
theorem expect_le_one_of_forall_le_one
    (p : PMF L) (F : L → ℝ≥0∞) (hF : ∀ x, F x ≤ 1) :
    expect p F ≤ 1 := by
  calc
    expect p F ≤ ∑' x, p x * (1 : ℝ≥0∞) := by
      unfold expect
      exact ENNReal.tsum_le_tsum fun x => by
        gcongr
        exact hF x
    _ = ∑' x, p x := by simp
    _ = 1 := PMF.tsum_coe p

/-- Reference stopped Bellman value: probability of reaching `G` before `B`
within the remaining horizon for a homogeneous reference kernel. -/
noncomputable def stoppedReferenceHit
    (B G : L → Prop) [DecidablePred B] [DecidablePred G]
    (Kref : L → PMF L) : ℕ → L → ℝ≥0∞
  | 0, i => ind G i
  | T + 1, i =>
      if G i then 1
      else if B i then 0
      else expect (Kref i) (stoppedReferenceHit B G Kref T)

/-- Controlled stopped Bellman value.  The one-step law returns both the next
external history/context and the next ordered level. -/
noncomputable def stoppedControlledHit
    (B G : L → Prop) [DecidablePred B] [DecidablePred G]
    (Kctl : H → L → PMF (H × L)) : ℕ → H → L → ℝ≥0∞
  | 0, _, i => ind G i
  | T + 1, h, i =>
      if G i then 1
      else if B i then 0
      else expect (Kctl h i)
        (fun q => stoppedControlledHit B G Kctl T q.1 q.2)

theorem stoppedReferenceHit_le_one
    (B G : L → Prop) [DecidablePred B] [DecidablePred G]
    (Kref : L → PMF L) :
    ∀ T i, stoppedReferenceHit B G Kref T i ≤ 1 := by
  intro T
  induction T with
  | zero =>
      intro i
      unfold stoppedReferenceHit ind
      by_cases hi : G i <;> simp [hi]
  | succ T ih =>
      intro i
      by_cases hG : G i
      · simp [stoppedReferenceHit, hG]
      · by_cases hB : B i
        · simp [stoppedReferenceHit, hG, hB]
        · simp [stoppedReferenceHit, hG, hB]
          exact expect_le_one_of_forall_le_one
            (Kref i) (stoppedReferenceHit B G Kref T) (ih)

/-- The reference stopped Bellman values are increasing when `B` is lower,
`G` is upper, and the reference kernel preserves stochastic order. -/
theorem stoppedReferenceHit_mono
    [Preorder L]
    (B G : L → Prop) [DecidablePred B] [DecidablePred G]
    (Kref : L → PMF L)
    (hB_lower : ∀ ⦃i j : L⦄, i ≤ j → B j → B i)
    (hG_upper : ∀ ⦃i j : L⦄, i ≤ j → G i → G j)
    (hmono : ∀ f : L → ℝ≥0∞, Monotone f →
      Monotone fun i => expect (Kref i) f) :
    ∀ T, Monotone (stoppedReferenceHit B G Kref T) := by
  intro T
  induction T with
  | zero =>
      intro i j hij
      unfold stoppedReferenceHit ind
      by_cases hi : G i
      · have hj : G j := hG_upper hij hi
        simp [hi, hj]
      · by_cases hj : G j <;> simp [hi, hj]
  | succ T ih =>
      intro i j hij
      by_cases hGi : G i
      · have hGj : G j := hG_upper hij hGi
        simp [stoppedReferenceHit, hGi, hGj]
      · by_cases hGj : G j
        · by_cases hBi : B i
          · simp [stoppedReferenceHit, hGi, hGj, hBi]
          · simp [stoppedReferenceHit, hGi, hGj, hBi]
            exact expect_le_one_of_forall_le_one
              (Kref i) (stoppedReferenceHit B G Kref T)
              (stoppedReferenceHit_le_one B G Kref T)
        · by_cases hBj : B j
          · have hBi : B i := hB_lower hij hBj
            simp [stoppedReferenceHit, hGi, hGj, hBi, hBj]
          · by_cases hBi : B i
            · simp [stoppedReferenceHit, hGi, hGj, hBi, hBj]
            · simp [stoppedReferenceHit, hGi, hGj, hBi, hBj]
              exact hmono (stoppedReferenceHit B G Kref T) ih hij

/-- A history-dependent controlled kernel dominates the reference stopped
hitting probability whenever every controlled one-step projection
first-order stochastically dominates the reference kernel. -/
theorem hitProb_ge_reference_of_kernel_stochDom
    [Preorder L]
    (B G : L → Prop) [DecidablePred B] [DecidablePred G]
    (Kref : L → PMF L)
    (Kctl : H → L → PMF (H × L))
    (hB_lower : ∀ ⦃i j : L⦄, i ≤ j → B j → B i)
    (hG_upper : ∀ ⦃i j : L⦄, i ≤ j → G i → G j)
    (hmono : ∀ f : L → ℝ≥0∞, Monotone f →
      Monotone fun i => expect (Kref i) f)
    (hdom : ∀ h i (f : L → ℝ≥0∞), Monotone f →
      expect (Kref i) f ≤ expect (Kctl h i) (fun q => f q.2)) :
    ∀ T h i,
      stoppedReferenceHit B G Kref T i ≤
        stoppedControlledHit B G Kctl T h i := by
  intro T
  induction T with
  | zero =>
      intro h i
      simp [stoppedReferenceHit, stoppedControlledHit]
  | succ T ih =>
      intro h i
      by_cases hG : G i
      · simp [stoppedReferenceHit, stoppedControlledHit, hG]
      · by_cases hB : B i
        · simp [stoppedReferenceHit, stoppedControlledHit, hG, hB]
        · simp [stoppedReferenceHit, stoppedControlledHit, hG, hB]
          calc
            expect (Kref i) (stoppedReferenceHit B G Kref T) ≤
                expect (Kctl h i)
                  (fun q => stoppedReferenceHit B G Kref T q.2) :=
              hdom h i (stoppedReferenceHit B G Kref T)
                (stoppedReferenceHit_mono B G Kref
                  hB_lower hG_upper hmono T)
            _ ≤ expect (Kctl h i)
                  (fun q => stoppedControlledHit B G Kctl T q.1 q.2) := by
              unfold expect
              exact ENNReal.tsum_le_tsum fun q => by
                gcongr
                exact ih q.1 q.2

namespace BellmanDominationExample

def bad (i : Fin 4) : Prop :=
  (i : ℕ) = 0

def good (i : Fin 4) : Prop :=
  3 ≤ (i : ℕ)

instance badDecidable : DecidablePred bad := by
  intro i
  unfold bad
  infer_instance

instance goodDecidable : DecidablePred good := by
  intro i
  unfold good
  infer_instance

def top : Fin 4 :=
  ⟨3, by decide⟩

noncomputable def refKernel (i : Fin 4) : PMF (Fin 4) :=
  PMF.pure i

noncomputable def ctlKernel (_ : Unit) (_ : Fin 4) : PMF (Unit × Fin 4) :=
  PMF.pure ((), top)

theorem bad_lower ⦃i j : Fin 4⦄ (hij : i ≤ j) (hj : bad j) :
    bad i := by
  unfold bad at *
  change (i : ℕ) ≤ (j : ℕ) at hij
  omega

theorem good_upper ⦃i j : Fin 4⦄ (hij : i ≤ j) (hi : good i) :
    good j := by
  unfold good at *
  change (i : ℕ) ≤ (j : ℕ) at hij
  omega

theorem refKernel_mono :
    ∀ f : Fin 4 → ℝ≥0∞, Monotone f →
      Monotone fun i => expect (refKernel i) f := by
  intro f hf i j hij
  simpa [refKernel] using hf hij

theorem ref_le_ctl :
    ∀ h i (f : Fin 4 → ℝ≥0∞), Monotone f →
      expect (refKernel i) f ≤ expect (ctlKernel h i) (fun q => f q.2) := by
  intro h i f hf
  have hitop : i ≤ top := by
    change (i : ℕ) ≤ 3
    exact Nat.le_of_lt_succ i.isLt
  simpa [refKernel, ctlKernel] using hf hitop

/-- Concrete non-vacuity check for the Bellman-domination hypotheses.  The
reference kernel stays put, while the controlled kernel jumps to the top state,
so domination is strict away from `top` for increasing tests that separate the
current state from `top`. -/
example :
    stoppedReferenceHit bad good refKernel 1 ⟨1, by decide⟩ ≤
      stoppedControlledHit bad good ctlKernel 1 () ⟨1, by decide⟩ := by
  exact
    hitProb_ge_reference_of_kernel_stochDom
      bad good refKernel ctlKernel
      (@bad_lower) (@good_upper) refKernel_mono ref_le_ctl
      1 () ⟨1, by decide⟩

end BellmanDominationExample

end Tri

#print axioms Tri.expect_le_one_of_forall_le_one
#print axioms Tri.stoppedReferenceHit_mono
#print axioms Tri.hitProb_ge_reference_of_kernel_stochDom
