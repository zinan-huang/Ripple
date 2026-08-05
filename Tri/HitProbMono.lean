/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Lemma15Glue
import Tri.EscapeSplit
import Tri.Phase3Productive

/-!
# `hitProb` is monotone in its target set

The step Lemma 15's assembly turns on, and the one I was least sure of.

Discharging `recentred_split`'s `hgood` needs a DOMINATION argument: the
global-centred bad event is contained in a conditional-centred `UrnWindowBad`
(that is what `urn_recentre_identity` and `urn_split_two_thirds` establish), and
the windowed tail bounds the latter. Concluding a bound on the former requires

```text
B ⊆ C  →  hitProb B K T x ≤ hitProb C K T x
```

## Why the obvious proof does not work

`hitProb` runs the FROZEN chain, so one might try to compare `freeze B K` with
`freeze C K` as kernels. They are not comparable: at a state in `C \ B` the
`C`-frozen chain holds still while the `B`-frozen chain executes `K`, and those
two distributions are not pointwise ordered in either direction.

## Why the induction does work

Through the first-hit Bellman recurrence. Once `C x` is false, `B x` is false
too, and both recurrences then evaluate against the SAME underlying kernel
`K x`. The kernels differing *after* a hit is harmless, because after a hit the
larger target is already at probability one.

So the monotonicity is real but has to be proved on the recurrence, not on the
implementation.
-/

namespace Tri
open scoped ENNReal
variable {α : Type*}

/-- **`hitProb` is monotone in its target set.**

NOT provable by comparing the frozen kernels: at a state in `C \ B` the
`C`-frozen chain holds still while the `B`-frozen chain steps, and those two
distributions are not pointwise ordered in either direction.

The induction works instead through the first-hit Bellman recurrence: once
`C x` is false, `B x` is false too, and both recurrences then use the SAME
underlying kernel `K x`.  So the kernels differing after a hit is harmless. -/
theorem hitProb_mono_target {K : α → PMF α} {B C : α → Prop}
    [DecidablePred B] [DecidablePred C] (hBC : ∀ x, B x → C x) :
    ∀ (T : ℕ) (x : α), hitProb B K T x ≤ hitProb C K T x := by
  intro T
  induction T with
  | zero =>
      intro x
      by_cases hB : B x
      · rw [hitProb_eq_one_of_mem B K 0 x hB,
          hitProb_eq_one_of_mem C K 0 x (hBC x hB)]
      · have hzero : hitProb B K 0 x = 0 := by
          unfold hitProb
          rw [show iter (freeze B K) 0 x = PMF.pure x from rfl, expect_pure]
          simp [ind, hB]
        rw [hzero]
        exact zero_le'
  | succ T ih =>
      intro x
      by_cases hC : C x
      · rw [hitProb_eq_one_of_mem C K (T + 1) x hC]
        exact hitProb_le_one B K (T + 1) x
      · have hB : ¬ B x := fun hx => hC (hBC x hx)
        rw [hitProb_succ_of_not B K T x hB, hitProb_succ_of_not C K T x hC]
        exact ENNReal.tsum_le_tsum (fun y => by gcongr; exact ih y)

/-- Enlarging the frozen hitting target can only decrease terminal failure. -/
theorem targetFreeze_failure_mono_target
    {K : α → PMF α} {B C : α → Prop}
    [DecidablePred B] [DecidablePred C]
    (hBC : ∀ x, B x → C x) :
    ∀ (T : ℕ) (x : α),
      terminalFailureMass (iter (freeze C K) T x) C ≤
        terminalFailureMass (iter (freeze B K) T x) B := by
  intro T
  induction T with
  | zero =>
      intro x
      simp only [iter_zero]
      rw [terminalFailureMass_pure, terminalFailureMass_pure]
      by_cases hC : C x
      · simp [hC]
      · have hB : ¬ B x := fun hx => hC (hBC x hx)
        simp [hB, hC]
  | succ T ih =>
      intro x
      by_cases hC : C x
      · rw [iter_freeze_of_mem x hC (T + 1),
          terminalFailureMass_pure, if_pos hC]
        exact bot_le
      · have hB : ¬ B x := fun hx => hC (hBC x hx)
        rw [iter_succ, iter_succ, freeze_of_not_mem x hC,
          freeze_of_not_mem x hB, terminalFailureMass_bind,
          terminalFailureMass_bind]
        unfold expect
        exact ENNReal.tsum_le_tsum fun y =>
          mul_le_mul_right (ih y) _

/-- Freezing on any additional set cannot increase the probability of hitting
a fixed event. -/
theorem hitProb_freeze_le
    (Bad Stop : α → Prop)
    [DecidablePred Bad] [DecidablePred Stop]
    (K : α → PMF α) :
    ∀ (T : ℕ) (x : α),
      hitProb Bad (freeze Stop K) T x ≤ hitProb Bad K T x := by
  intro T
  induction T with
  | zero =>
      intro x
      unfold hitProb
      simp [iter, expect_pure]
  | succ T ih =>
      intro x
      by_cases hBad : Bad x
      · rw [hitProb_eq_one_of_mem Bad (freeze Stop K) (T + 1) x hBad,
          hitProb_eq_one_of_mem Bad K (T + 1) x hBad]
      · by_cases hStop : Stop x
        · have hstep :
              freeze Bad (freeze Stop K) x = PMF.pure x := by
            rw [freeze_of_not_mem x hBad, freeze_of_mem x hStop]
          have hiter :
              ∀ U, iter (freeze Bad (freeze Stop K)) U x =
                PMF.pure x := by
            intro U
            induction U with
            | zero => rfl
            | succ U ihU =>
                rw [iter_succ, hstep, PMF.pure_bind, ihU]
          have hzero :
              hitProb Bad (freeze Stop K) (T + 1) x = 0 := by
            unfold hitProb
            rw [hiter]
            simp [ind, hBad]
          rw [hzero]
          exact bot_le
        · rw [hitProb_succ_of_not Bad (freeze Stop K) T x hBad,
            hitProb_succ_of_not Bad K T x hBad,
            freeze_of_not_mem x hStop]
          exact ENNReal.tsum_le_tsum fun y =>
            mul_le_mul_right (ih y) _
end Tri

#print axioms Tri.hitProb_mono_target
#print axioms Tri.targetFreeze_failure_mono_target
#print axioms Tri.hitProb_freeze_le
