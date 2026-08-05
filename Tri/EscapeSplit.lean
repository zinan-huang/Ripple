/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.LazyHitting
import Tri.BandRung

/-!
# The escape/live mass split

A two-branch failure analysis needs to say: the mass that has not reached the
target by time `T` is contained in the mass that escaped a safety band, plus
the mass that survived inside the band without finishing.  Making that precise
is pure `PMF` bookkeeping — no probability estimate is involved — and the key
is the pointwise identity

```text
freeze Escape (freeze Done K) = freeze (fun s => Done s ∨ Escape s) K
```

which is what makes the two right-hand terms comparable: they are computed
along the *same* trajectories.  Paths that touch `Escape` and later reach
`Done` are double-counted by the escape term, so the result is an inequality
rather than an identity.

No disjointness of `Done` and `Escape`, and no skip-free property of `K`, is
needed.
-/

namespace Tri

open scoped ENNReal

variable {α : Type*}

/-- Freezing on `Escape` after freezing on `Done` is freezing on the union. -/
theorem freeze_escape_freeze_done
    (K : α → PMF α) (Done Escape : α → Prop)
    [DecidablePred Done] [DecidablePred Escape] :
    freeze Escape (freeze Done K) =
      freeze (fun s => Done s ∨ Escape s) K := by
  funext s
  by_cases hE : Escape s
  · simp [freeze, hE]
  · by_cases hD : Done s
    · simp [freeze, hE, hD]
    · simp [freeze, hE, hD]

/-- A chain started inside the hit set hits it with probability one. -/
theorem hitProb_eq_one_of_mem
    (B : α → Prop) [DecidablePred B] (K : α → PMF α)
    (T : ℕ) (s : α) (hs : B s) :
    hitProb B K T s = 1 := by
  unfold hitProb
  rw [iter_freeze_of_mem s hs T, expect_pure]
  simp [ind, hs]

/-- Off the hit set, the hitting probability satisfies the one-step recurrence. -/
theorem hitProb_succ_of_not
    (B : α → Prop) [DecidablePred B] (K : α → PMF α)
    (T : ℕ) (s : α) (hs : ¬ B s) :
    hitProb B K (T + 1) s = ∑' x, K s x * hitProb B K T x := by
  unfold hitProb
  show expect ((freeze B K s).bind (iter (freeze B K) T)) (ind B) = _
  rw [show freeze B K s = K s by simp [freeze, hs], expect_bind]

/-- Failure mass of a point mass. -/
theorem terminalFailureMass_pure
    (s : α) (A : α → Prop) [DecidablePred A] :
    terminalFailureMass (PMF.pure s) A = if A s then 0 else 1 := by
  rw [terminalFailureMass_eq_expect, expect_pure]

/-- **The escape/live mass split.**  Failing to be in `Done` at time `T` under
the `Done`-frozen chain is contained in: hitting `Escape` by time `T`, or
surviving the chain frozen at `Done ∨ Escape` through time `T`.

No disjointness and no skip-free hypothesis is needed.  The point is the
pointwise identity `freeze Escape (freeze Done K) = freeze (Done ∨ Escape) K`,
so the two right-hand terms really are computed along the same trajectories.
Paths that hit `Escape` and later reach `Done` are double-counted by the first
term, which is exactly why this is an inequality and not an identity. -/
theorem terminalFailureMass_le_escape_add_live
    (K : α → PMF α) (Done Escape : α → Prop)
    [DecidablePred Done] [DecidablePred Escape]
    (T : ℕ) (s₀ : α) :
    terminalFailureMass (iter (freeze Done K) T s₀) Done
      ≤ hitProb Escape (freeze Done K) T s₀
        + terminalFailureMass
            (iter (freeze (fun s => Done s ∨ Escape s) K) T s₀)
            (fun s => Done s ∨ Escape s) := by
  classical
  induction T generalizing s₀ with
  | zero =>
      simp only [iter_zero, terminalFailureMass_pure]
      by_cases hD : Done s₀
      · simp [hD]
      · by_cases hE : Escape s₀
        · rw [hitProb_eq_one_of_mem Escape (freeze Done K) 0 s₀ hE]
          simp [hD]
        · simp [hD, hE]
  | succ T ih =>
      by_cases hD : Done s₀
      · rw [iter_freeze_of_mem s₀ hD (T + 1), terminalFailureMass_pure, if_pos hD]
        simp
      · by_cases hE : Escape s₀
        · rw [hitProb_eq_one_of_mem Escape (freeze Done K) (T + 1) s₀ hE]
          exact (terminalFailureMass_le_one _ _).trans le_self_add
        · have hKDone : freeze Done K s₀ = K s₀ := by simp [freeze, hD]
          have hKBoth :
              freeze (fun s => Done s ∨ Escape s) K s₀ = K s₀ := by
            simp [freeze, hD, hE]
          show terminalFailureMass
              ((freeze Done K s₀).bind (iter (freeze Done K) T)) Done ≤
            hitProb Escape (freeze Done K) (T + 1) s₀ +
              terminalFailureMass
                ((freeze (fun s => Done s ∨ Escape s) K s₀).bind
                  (iter (freeze (fun s => Done s ∨ Escape s) K) T))
                (fun s => Done s ∨ Escape s)
          rw [hKDone, hKBoth, terminalFailureMass_bind, terminalFailureMass_bind,
            hitProb_succ_of_not Escape (freeze Done K) T s₀ hE]
          simp only [hKDone]
          unfold expect
          rw [← ENNReal.tsum_add]
          refine ENNReal.tsum_le_tsum fun x => ?_
          simp only []
          rw [← mul_add]
          exact mul_le_mul_right (ih x) (K s₀ x)

end Tri

#print axioms Tri.terminalFailureMass_pure
#print axioms Tri.terminalFailureMass_le_escape_add_live
#print axioms Tri.freeze_escape_freeze_done
#print axioms Tri.hitProb_eq_one_of_mem
#print axioms Tri.hitProb_succ_of_not
