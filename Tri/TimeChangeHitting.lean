/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.EscapeSplit

/-!
# Hitting probabilities under bounded time changes

The eventual hitting probability of a kernel is its least nonnegative
superharmonic majorant of the target indicator.  In particular, replacing one
step by any finite mixture of zero, one, or two original steps cannot increase
that eventual hitting probability.

The only continuity fact needed below is elementary monotone convergence for
expectations of `ℝ≥0∞`-valued functions.  It is proved directly from finite
sums and `ENNReal.tsum_eq_iSup_sum`.
-/

namespace Tri

open scoped ENNReal BigOperators

noncomputable section

variable {α : Type*}

/-- Changing the continuation kernel only at states of zero incoming mass
does not change a bind. -/
theorem PMF.bind_change_on_zero_mass
    {β : Type*} (p : PMF α) (f g : α → PMF β)
    (h : ∀ a, p a ≠ 0 → f a = g a) :
    p.bind f = p.bind g := by
  ext z
  rw [PMF.bind_apply, PMF.bind_apply]
  apply tsum_congr
  intro a
  by_cases ha : p a = 0
  · simp [ha]
  · rw [h a ha]

/-- A step projection available only on a support invariant still propagates
to every horizon started inside that invariant. -/
theorem iter_map_of_step_map_on_support_invariant
    {β : Type*}
    (K₁ : α → PMF α) (K₂ : β → PMF β)
    (φ : α → β) (P : α → Prop)
    (hclosed : ∀ s, P s → ∀ z, K₁ s z ≠ 0 → P z)
    (hstep : ∀ s, P s → (K₁ s).map φ = K₂ (φ s)) :
    ∀ T s, P s →
      (iter K₁ T s).map φ = iter K₂ T (φ s) := by
  intro T
  induction T with
  | zero =>
      intro s hs
      simp [iter, PMF.pure_map]
  | succ T ih =>
      intro s hs
      rw [iter_succ, iter_succ, PMF.map_bind]
      calc
        (K₁ s).bind (fun z => (iter K₁ T z).map φ) =
            (K₁ s).bind (fun z => iter K₂ T (φ z)) := by
              apply PMF.bind_change_on_zero_mass
              intro z hz
              exact ih z (hclosed s hs z hz)
        _ = ((K₁ s).map φ).bind (iter K₂ T) :=
              (PMF.bind_map _ _ _).symm
        _ = (K₂ (φ s)).bind (iter K₂ T) := by
              rw [hstep s hs]

/-- Finite sums commute with a directed monotone supremum in `ℝ≥0∞`. -/
theorem ennreal_finset_sum_iSup_of_monotone
    (s : Finset α) (f : α → ℕ → ℝ≥0∞)
    (hf : ∀ a, Monotone (f a)) :
    (∑ a ∈ s, ⨆ T, f a T) = ⨆ T, ∑ a ∈ s, f a T := by
  classical
  induction s using Finset.cons_induction with
  | empty =>
      simp
  | @cons a s ha ih =>
      simp_rw [Finset.sum_cons, ih]
      exact ENNReal.iSup_add_iSup_of_monotone
        (hf a)
        (fun i j hij =>
          Finset.sum_le_sum fun b hb => hf b hij)

/-- Expectation commutes with a pointwise monotone supremum. -/
theorem expect_iSup_of_monotone
    (p : PMF α) (f : ℕ → α → ℝ≥0∞)
    (hf : ∀ a, Monotone (fun T => f T a)) :
    expect p (fun a => ⨆ T, f T a) =
      ⨆ T, expect p (f T) := by
  classical
  unfold expect
  simp_rw [ENNReal.mul_iSup]
  rw [ENNReal.tsum_eq_iSup_sum]
  calc
    (⨆ s : Finset α, ∑ a ∈ s, ⨆ T, p a * f T a)
        = ⨆ s : Finset α, ⨆ T, ∑ a ∈ s, p a * f T a := by
          congr 1
          funext s
          exact ennreal_finset_sum_iSup_of_monotone s
            (fun a T => p a * f T a)
            (fun a _ _ h => mul_le_mul_right (hf a h) (p a))
    _ = ⨆ T, ⨆ s : Finset α, ∑ a ∈ s, p a * f T a :=
      iSup_comm
    _ = ⨆ T, ∑' a, p a * f T a := by
      simp_rw [ENNReal.tsum_eq_iSup_sum]

/-- Geometric expectation control when the one-step estimate is only needed
on a support invariant. -/
theorem expect_iter_le_of_support_invariant
    (K : α → PMF α) (P : α → Prop)
    (V : α → ℝ≥0∞) (c : ℝ≥0∞)
    (hclosed : ∀ s, P s → ∀ z, K s z ≠ 0 → P z)
    (hstep : ∀ s, P s → expect (K s) V ≤ c * V s) :
    ∀ T s, P s →
      expect (iter K T s) V ≤ c ^ T * V s := by
  intro T
  induction T with
  | zero =>
      intro s hs
      simp
  | succ T ih =>
      intro s hs
      rw [iter_succ, expect_bind]
      calc
        (∑' z, K s z * expect (iter K T z) V)
            ≤ ∑' z, K s z * (c ^ T * V z) := by
              refine ENNReal.tsum_le_tsum fun z => ?_
              by_cases hz : K s z = 0
              · simp [hz]
              · exact mul_le_mul_right
                  (ih z (hclosed s hs z hz)) _
        _ = c ^ T * ∑' z, K s z * V z := by
              rw [← ENNReal.tsum_mul_left]
              congr 1
              ext z
              ring
        _ ≤ c ^ T * (c * V s) :=
              mul_le_mul_right (hstep s hs) _
        _ = c ^ (T + 1) * V s := by ring

/-- Ville's maximal bound when superharmonicity is available only on a
support invariant containing the initial state. -/
theorem ville_frozen_of_support_invariant
    (K : α → PMF α)
    (B P : α → Prop) [DecidablePred B]
    (V : α → ℝ≥0∞) (θ : ℝ≥0∞)
    (hθ : θ ≠ 0) (htop : θ ≠ ⊤)
    (hcontain : ∀ z, P z → B z → θ ≤ V z)
    (hclosed : ∀ s, P s → ∀ z, K s z ≠ 0 → P z)
    (hsuper : ∀ s, P s → expect (K s) V ≤ V s)
    (q : α) (hq : P q) :
    ⨆ T : ℕ, hitProb B K T q ≤ V q / θ := by
  have hfrozenClosed :
      ∀ s, P s → ∀ z, freeze B K s z ≠ 0 → P z := by
    intro s hs z hz
    by_cases hB : B s
    · rw [freeze_of_mem s hB] at hz
      have hzs : z = s := by
        by_contra hne
        simp [PMF.pure_apply, hne] at hz
      simpa [hzs] using hs
    · rw [freeze_of_not_mem s hB] at hz
      exact hclosed s hs z hz
  have hfrozenSuper :
      ∀ s, P s → expect (freeze B K s) V ≤ V s := by
    intro s hs
    by_cases hB : B s
    · rw [freeze_of_mem s hB, expect_pure]
    · rw [freeze_of_not_mem s hB]
      exact hsuper s hs
  have hfrozenIterClosed :
      ∀ T s z, P s →
        iter (freeze B K) T s z ≠ 0 → P z := by
    intro T
    induction T with
    | zero =>
        intro s z hs hz
        simp only [iter, PMF.pure_apply] at hz
        by_cases hzs : z = s
        · simpa [hzs] using hs
        · simp [hzs] at hz
    | succ T ih =>
        intro s z hs hz
        rw [iter_succ, PMF.bind_apply] at hz
        by_contra hzP
        apply hz
        rw [ENNReal.tsum_eq_zero]
        intro a
        by_cases hsa : freeze B K s a = 0
        · simp [hsa]
        · have haP := hfrozenClosed s hs a hsa
          have hazero : iter (freeze B K) T a z = 0 := by
            by_contra haz
            exact hzP (ih a z haP haz)
          simp [hazero]
  refine iSup_le fun T => ?_
  have hrewrite :
      hitProb B K T q =
        ∑' z, if B z then iter (freeze B K) T q z else 0 := by
    unfold hitProb expect ind
    congr 1
    ext z
    by_cases hz : B z <;> simp [hz]
  rw [hrewrite]
  calc
    (∑' z, if B z then iter (freeze B K) T q z else 0)
        ≤ ∑' z,
            if θ ≤ V z then
              iter (freeze B K) T q z
            else 0 := by
              refine ENNReal.tsum_le_tsum fun z => ?_
              by_cases hz : B z
              · by_cases hzP : P z
                · rw [if_pos hz,
                    if_pos (hcontain z hzP hz)]
                · have hmass :
                      iter (freeze B K) T q z = 0 := by
                    by_contra hne
                    exact hzP
                      (hfrozenIterClosed T q z hq hne)
                  rw [if_pos hz, hmass]
                  simp
              · rw [if_neg hz]
                simp
    _ ≤ expect (iter (freeze B K) T q) V / θ :=
          markov_div
            (iter (freeze B K) T q) V θ hθ htop
    _ ≤ V q / θ := by
          refine ENNReal.div_le_div_right ?_ θ
          have hiter :=
            expect_iter_le_of_support_invariant
              (freeze B K) P V 1
              hfrozenClosed
              (fun s hs => by
                simpa using hfrozenSuper s hs)
              T q hq
          simpa using hiter

/-- Probability of hitting `B` at some finite horizon. -/
noncomputable def everHit
    (B : α → Prop) [DecidablePred B]
    (K : α → PMF α) (s : α) : ℝ≥0∞ :=
  ⨆ T : ℕ, hitProb B K T s

/-- Eventual hitting probability is at most one. -/
theorem everHit_le_one
    (B : α → Prop) [DecidablePred B]
    (K : α → PMF α) (s : α) :
    everHit B K s ≤ 1 := by
  refine iSup_le fun T => ?_
  unfold hitProb expect ind
  calc
    (∑' z, iter (freeze B K) T s z *
        (if B z then 1 else 0))
        ≤ ∑' z, iter (freeze B K) T s z := by
          refine ENNReal.tsum_le_tsum fun z => ?_
          by_cases hz : B z <;> simp [hz]
    _ = 1 := PMF.tsum_coe _

/-- The eventual hitting potential is one on the target. -/
theorem everHit_eq_one_of_mem
    (B : α → Prop) [DecidablePred B]
    (K : α → PMF α) (s : α) (hs : B s) :
    everHit B K s = 1 := by
  apply le_antisymm (everHit_le_one B K s)
  exact (show (1 : ℝ≥0∞) ≤ everHit B K s from
    (hitProb_eq_one_of_mem B K 0 s hs).ge.trans
      (le_iSup (fun T => hitProb B K T s) 0))

/-- Off the target, one original step preserves the eventual hitting
probability. -/
theorem expect_everHit_eq_of_not_mem
    (B : α → Prop) [DecidablePred B]
    (K : α → PMF α) (s : α) (hs : ¬ B s) :
    expect (K s) (everHit B K) = everHit B K s := by
  unfold everHit
  rw [expect_iSup_of_monotone
    (p := K s) (f := fun T x => hitProb B K T x)
    (fun x => hitProb_mono (B := B) (K := K) x)]
  apply le_antisymm
  · refine iSup_le fun T => ?_
    change (∑' x, K s x * hitProb B K T x) ≤ _
    rw [← hitProb_succ_of_not B K T s hs]
    exact le_iSup (fun U => hitProb B K U s) (T + 1)
  · refine iSup_le fun T => ?_
    cases T with
    | zero =>
        simp [hitProb, iter, ind, hs]
    | succ T =>
        rw [hitProb_succ_of_not B K T s hs]
        exact le_iSup (fun U =>
          ∑' x, K s x * hitProb B K U x) T

/-- One original step cannot increase the eventual hitting potential. -/
theorem expect_everHit_le
    (B : α → Prop) [DecidablePred B]
    (K : α → PMF α) (s : α) :
    expect (K s) (everHit B K) ≤ everHit B K s := by
  by_cases hs : B s
  · rw [everHit_eq_one_of_mem B K s hs]
    unfold expect
    calc
      (∑' z, K s z * everHit B K z)
          ≤ ∑' z, K s z * 1 :=
            ENNReal.tsum_le_tsum fun z =>
              mul_le_mul_right (everHit_le_one B K z) (K s z)
      _ = 1 := by
        simp [PMF.tsum_coe]
  · exact (expect_everHit_eq_of_not_mem B K s hs).le

/-- Any fixed number of original steps cannot increase eventual hitting. -/
theorem expect_iter_everHit_le
    (B : α → Prop) [DecidablePred B]
    (K : α → PMF α) (T : ℕ) (s : α) :
    expect (iter K T s) (everHit B K) ≤ everHit B K s := by
  simpa using
    expect_iter_le K (everHit B K) 1
      (fun q => by simpa using expect_everHit_le B K q) T s

end

end Tri

#print axioms Tri.PMF.bind_change_on_zero_mass
#print axioms Tri.iter_map_of_step_map_on_support_invariant
#print axioms Tri.expect_iSup_of_monotone
#print axioms Tri.expect_iter_le_of_support_invariant
#print axioms Tri.ville_frozen_of_support_invariant
#print axioms Tri.expect_everHit_le
#print axioms Tri.expect_iter_everHit_le
