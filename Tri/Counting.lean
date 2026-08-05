/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Chain
import Tri.Progress

/-!
# Counting productive reactions

The progress engine (`Tri.count_tail_bernoulli`) bounds the probability that a
*counter* fails to grow. The Tri chain has no counter — its state is just the
`X`-count — so this file augments it with one.

`triCount` carries the pair `(x, c)` where `c` counts productive reactions. It
is built by mapping the existing `triChain`, so nothing about the dynamics is
re-derived; `Tri.expect_map` transports any potential through the augmentation.

The key computation is `triCount_decomp`: at an interior state the augmented
chain has exactly the two-atom form the progress engine expects — the counter
stays put with the probability of an unproductive triple, and increments
otherwise. That is what connects the paper's *productive-reaction* clock to the
*interaction* clock without ever constructing the embedded jump chain, which is
the design's `Tri.lazy_conserved` principle realized concretely.

## Main results

* `triCount` — the CRN augmented with a productive-reaction counter.
* `expect_triCount` — potentials transport through the augmentation.
* `triCount_decomp` — the two-atom decomposition at an interior state.

Reference: A. Condon, M. Hajiaghayi, D. Kirkpatrick, J. Mañuch,
*Approximate Majority Analyses using Tri-molecular Chemical Reaction Networks*,
Lemma 5.
-/

namespace Tri

open scoped ENNReal

/-- The CRN augmented with a counter of productive reactions: the counter
increments exactly when the `X`-count changes. -/
noncomputable def triCount (n : ℕ) : ℕ × ℕ → PMF (ℕ × ℕ) := fun s =>
  (triChain n s.1).map (fun x' => (x', if x' = s.1 then s.2 else s.2 + 1))

/-- A potential in the counter transports through the augmentation. -/
theorem expect_triCount (n : ℕ) (x c : ℕ) (w : ℝ≥0∞) :
    expect (triCount n (x, c)) (fun z => w ^ z.2)
      = expect (triChain n x) (fun x' => w ^ (if x' = x then c else c + 1)) := by
  unfold triCount
  rw [expect_map]

/-- **The two-atom decomposition.**

At an interior state the augmented chain leaves the counter alone with the
probability of an unproductive (homogeneous) triple, and increments it with the
probability of a productive one. This is exactly the shape
`Tri.count_step_of_masses` consumes, so the progress engine applies to the CRN
with no further probabilistic work.

Note what is *not* needed: the embedded jump chain over productive steps is
never constructed, and no conditioning on "the next productive reaction" occurs.
The productive and interaction clocks are related by this single algebraic
identity. -/
theorem triCount_decomp (n a b c : ℕ) (hb : a + b + 2 = n) (h3 : 3 ≤ n) (w : ℝ≥0∞) :
    expect (triCount n (a + 1, c)) (fun z => w ^ z.2)
      = triStep (a + 1) (b + 1) (by omega) (a + 1) * w ^ c
        + (triStep (a + 1) (b + 1) (by omega) a
            + triStep (a + 1) (b + 1) (by omega) (a + 2)) * w ^ (c + 1) := by
  rw [expect_triCount, triChain_apply hb h3, expect_triStep]
  have e1 : (if a = a + 1 then c else c + 1) = c + 1 := if_neg (by omega)
  have e2 : (if a + 1 = a + 1 then c else c + 1) = c := if_pos rfl
  have e3 : (if a + 2 = a + 1 then c else c + 1) = c + 1 := if_neg (by omega)
  rw [e1, e2, e3]
  ring

/-- The stay-mass and the productive mass sum to one, as `count_step_of_masses`
requires. -/
theorem triCount_masses (a b : ℕ) (h : 3 ≤ (a + 1) + (b + 1)) :
    triStep (a + 1) (b + 1) h (a + 1)
        + (triStep (a + 1) (b + 1) h a + triStep (a + 1) (b + 1) h (a + 2)) = 1 := by
  have := triStep_masses_sum a (b + 1) h
  rw [← this]; ring

end Tri
