/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Lemma15Numeric
import Tri.Lemma15Split

/-!
# Lemma 15's prefix estimate: the clock is free at a fixed time

`recentred_split` needs a prefix hypothesis of the shape

```text
∑' q, (if Good q then 0 else iter K a q₀ q)  ≤  εpre
```

and Lemma 15's first application of Lemma 14 supplies it. That application is
FIXED-TIME — it controls only the endpoint after exactly `a` reveals — which is
what makes it cheaper than the windowed one.

## Why the clock conjunct is free here

`UrnWindowBad` carries a clock conjunct `u + 1 ≤ total` because the maximal
bound ranges over states at every depth, and a state deeper than the window's
end has a smaller variance budget (see `Tri/Lemma15Window.lean`).

At a FIXED time there is no such freedom: the urn loses exactly one ball per
reveal, so after `a` reveals the total is exactly `a` less. With the window
parametrised by `a + (u + 1) = ν` — the same subtraction-free parametrisation
used throughout — the total on the support is exactly `u + 1`, so the clock
conjunct holds with equality and costs nothing.

That is the whole content of this file: `urnStopped_iter_total` makes the
clock automatic, and the prefix tail then follows from the fixed-time Markov
bound already proved for Lemma 14.
-/

namespace Tri
open scoped ENNReal


/-- After exactly `a` reveals the remaining total is exactly `a` less, provided
the window has not run the urn down to its frozen floor. -/
theorem urnStopped_iter_total : ∀ (a : ℕ) (q z : ℕ × ℕ), a + 1 ≤ q.1 + q.2 →
    iter urnStopped a q z ≠ 0 → z.1 + z.2 + a = q.1 + q.2 := by
  intro a
  induction a with
  | zero =>
      intro q z _ hz
      simp only [iter, PMF.pure_apply] at hz
      by_cases h : z = q
      · rw [h]; omega
      · simp [h] at hz
  | succ a ih =>
      intro q z hlen hz
      rw [iter_succ, PMF.bind_apply, Ne, ENNReal.tsum_eq_zero] at hz
      push Not at hz
      obtain ⟨w, hw⟩ := hz
      rw [mul_ne_zero_iff] at hw
      have hq2 : ¬ (q.1 + q.2 ≤ 1) := by omega
      have hchain : urnChain q w ≠ 0 := by
        have := hw.1
        unfold urnStopped freeze at this
        rwa [if_neg hq2] at this
      have hstep := urnChain_support_total q (by omega) w hchain
      have hlen' : a + 1 ≤ w.1 + w.2 := by omega
      have := ih w z hlen' hw.2
      omega

/-- At a fixed time the deviation alone implies the full bad predicate: the
clock conjunct is supplied by the support. -/
theorem urn_fixed_time_bad (c₀ δ lam : ℝ) (R B a u : ℕ)
    (hν : a + (u + 1) = R + B) (z : ℕ × ℕ)
    (hz : iter urnStopped a (R, B) z ≠ 0)
    (hdev : |lam| * δ ≤ lam * urnM c₀ z) :
    UrnWindowBad c₀ δ lam u z := by
  refine ⟨?_, hdev⟩
  have h := urnStopped_iter_total a (R, B) z (by omega) hz
  simp only at h
  omega

/-- **Lemma 15's prefix estimate.**  After exactly `a` reveals, the mass of
endpoints whose centred red fraction has deviated by `δ` is at most
`G(start)/θ`.

This is the `hpre` that `recentred_split` consumes, with
`Good q := ¬(deviation at q)`. -/
theorem urn_prefix_tail (c₀ δ lam : ℝ) (R B a u : ℕ)
    (hν : a + (u + 1) = R + B) :
    ∑' z, (if |lam| * δ ≤ lam * urnM c₀ z then
        iter urnStopped a (R, B) z else 0)
      ≤ urnG c₀ lam (R, B) / urnTheta δ lam u := by
  refine le_trans (ENNReal.tsum_le_tsum ?_)
    (urnG_markov c₀ lam a (R, B) (urnTheta δ lam u)
      (urnTheta_ne_zero δ lam u) (urnTheta_ne_top δ lam u))
  intro z
  by_cases hz : iter urnStopped a (R, B) z = 0
  · simp [hz]
  · by_cases hdev : |lam| * δ ≤ lam * urnM c₀ z
    · have hbad := urn_fixed_time_bad c₀ δ lam R B a u hν z hz hdev
      have hcon := urn_window_contain c₀ δ lam u z hbad
      simp [hdev, hcon]
    · simp [hdev]

/-- The prefix estimate in the exact shape `recentred_split` wants, with the
good set stated positively. -/
theorem urn_prefix_tail_good (c₀ δ lam : ℝ) (R B a u : ℕ)
    (hν : a + (u + 1) = R + B) :
    ∑' z, (if ¬ (|lam| * δ ≤ lam * urnM c₀ z) then 0
        else iter urnStopped a (R, B) z)
      ≤ urnG c₀ lam (R, B) / urnTheta δ lam u := by
  refine le_trans (le_of_eq ?_) (urn_prefix_tail c₀ δ lam R B a u hν)
  refine tsum_congr fun z => ?_
  by_cases hdev : |lam| * δ ≤ lam * urnM c₀ z <;> simp [hdev]

end Tri

#print axioms Tri.urnStopped_iter_total
#print axioms Tri.urn_fixed_time_bad
#print axioms Tri.urn_prefix_tail
#print axioms Tri.urn_prefix_tail_good
