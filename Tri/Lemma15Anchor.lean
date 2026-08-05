/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Lemma15Split

/-!
# What `recentred_split`'s left-hand side actually means

A hostile audit of `Tri/Lemma15Split.lean` returned this verdict on
`recentred_split`:

> The inequality itself is sound, and its left side has an exact probabilistic
> interpretation, but that interpretation is narrower than several natural
> English readings. In particular, it is not automatically the probability of
> hitting one fixed bad set.

Both halves are right, and the second is the dangerous one: the quantity

```text
∑' q, iter K a q₀ q * hitProb (Bad q) K b q
```

is NOT `hitProb B K (a+b) q₀` for any `B : α → Prop`, because `Bad q` varies
with `q`. Reading it as though it were would be a silent overclaim in exactly
the place Lemma 15's whole design lives.

This file removes the ambiguity by making the correct reading a THEOREM rather
than a docstring: the left-hand side is an ordinary `hitProb`, on an augmented
carrier `α × α` whose first coordinate is a frozen ANCHOR.

```text
carrier   α × α          -- (anchor, current)
kernel    anchorKernel K -- the anchor never moves; the current state runs K
bad set   fun p => Bad p.1 p.2   -- ONE fixed subset of the augmented carrier
```

With that, `recentred_split`'s conclusion is a bound on the hit probability of
a single fixed set — of the augmented chain, not of the original one. That is
the precise sense in which the recentring is legitimate, and it is now checked
by the compiler.

## What this does NOT say

The audit's other point stands and is not repaired here, because it is a
design choice rather than a defect: the prefix hypothesis controls only
`Pr[¬Good at the split endpoint]`, a FIXED-TIME event at time `a`. It says
nothing about `Good` failing earlier and recovering. That is exactly right for
Lemma 15, whose first Lemma 14 application is fixed-time by design and
controls only the endpoint — the maximal bound is needed for the window, not
for the prefix.
-/

namespace Tri

open scoped ENNReal

variable {α : Type*}

/-- The augmented kernel: the first coordinate is an anchor that never moves,
the second runs `K`. -/
noncomputable def anchorKernel (K : α → PMF α) : α × α → PMF (α × α) :=
  fun p => (K p.2).map fun z => (p.1, z)

/-- Iterating the augmented kernel is iterating `K` and tagging the anchor. -/
theorem iter_anchorKernel (K : α → PMF α) (T : ℕ) (a s : α) :
    iter (anchorKernel K) T (a, s) = (iter K T s).map fun z => (a, z) := by
  induction T generalizing s with
  | zero => simp [iter, PMF.pure_map]
  | succ T ih =>
      show ((K s).map fun z => (a, z)).bind (iter (anchorKernel K) T)
          = ((K s).bind (iter K T)).map fun z => (a, z)
      rw [PMF.bind_map, PMF.map_bind]
      exact congrArg _ (funext fun z => ih z)

/-- Freezing the augmented chain on an anchor-dependent set is the same as
freezing `K` on that set at the anchor's own value — **on the fibre over the
anchor**, which is the only place the chain ever visits. -/
theorem anchorKernel_freeze (K : α → PMF α) (Bad : α → α → Prop)
    [∀ q, DecidablePred (Bad q)] (a s : α) :
    freeze (fun p => Bad p.1 p.2) (anchorKernel K) (a, s)
      = (freeze (Bad a) K s).map fun z => (a, z) := by
  unfold freeze anchorKernel
  by_cases h : Bad a s
  · rw [if_pos h, if_pos h]
    rw [PMF.pure_map]
  · rw [if_neg h, if_neg h]

/-- The frozen augmented iterate, likewise. -/
theorem iter_freeze_anchorKernel (K : α → PMF α) (Bad : α → α → Prop)
    [∀ q, DecidablePred (Bad q)] (T : ℕ) (a s : α) :
    iter (freeze (fun p => Bad p.1 p.2) (anchorKernel K)) T (a, s)
      = (iter (freeze (Bad a) K) T s).map fun z => (a, z) := by
  induction T generalizing s with
  | zero => simp [iter, PMF.pure_map]
  | succ T ih =>
      rw [iter_succ, iter_succ, anchorKernel_freeze, PMF.bind_map, PMF.map_bind]
      exact congrArg _ (funext fun z => ih z)

/-- **The recentred hit probability IS an ordinary hit probability.**

On the augmented carrier the bad set is a single fixed subset — the anchor
dependence has been absorbed into the state.  This is the theorem that
licenses reading `hitProb (Bad q) K b q` as a genuine hitting probability of
the recentred event rather than as a formal expression. -/
theorem hitProb_anchorKernel (K : α → PMF α) (Bad : α → α → Prop)
    [∀ q, DecidablePred (Bad q)] (T : ℕ) (a s : α) :
    hitProb (fun p => Bad p.1 p.2) (anchorKernel K) T (a, s)
      = hitProb (Bad a) K T s := by
  unfold hitProb
  rw [iter_freeze_anchorKernel, expect_map]
  unfold expect ind
  congr 1

/-- **`recentred_split`, restated on the augmented carrier.**

Every `hitProb` here is the hitting probability of ONE fixed subset of
`α × α`, so the statement admits no recentring-flavoured overreading: it says
that the anchored chain, started with its anchor equal to its state, enters
the fixed bad set `{(q, z) | Bad q z}` with probability at most `εpre + ε`,
averaged over the prefix endpoint.

This is `recentred_split` with the same hypotheses and the same bound — only
the reading has changed, and now it is the compiler's reading. -/
theorem recentred_split_anchored
    (K : α → PMF α) (a b : ℕ) (q₀ : α)
    (Good : α → Prop) [DecidablePred Good]
    (Bad : α → α → Prop) [∀ q, DecidablePred (Bad q)]
    (εpre ε : ℝ≥0∞)
    (hpre : (∑' q, if Good q then 0 else iter K a q₀ q) ≤ εpre)
    (hgood : ∀ q, Good q →
      hitProb (fun p => Bad p.1 p.2) (anchorKernel K) b (q, q) ≤ ε) :
    ∑' q, iter K a q₀ q
        * hitProb (fun p => Bad p.1 p.2) (anchorKernel K) b (q, q)
      ≤ εpre + ε := by
  simp only [hitProb_anchorKernel]
  exact recentred_split K a b q₀ Good Bad εpre ε hpre
    (fun q hq => by simpa [hitProb_anchorKernel] using hgood q hq)

/-- The negative half of the audit's point, recorded as a definition rather
than left implicit: the prefix hypothesis of `recentred_split` is exactly
`Pr[¬ Good]` at the SPLIT TIME, not at any earlier time.

Naming it makes the fixed-time character visible at every call site.  Lemma
15's first Lemma 14 application is fixed-time by design — it controls only the
endpoint — so this is the right hypothesis there; a caller needing control
throughout the prefix must supply a maximal bound instead, and will see from
this name that `recentred_split` does not give one. -/
noncomputable def PrefixEndpointFailure (K : α → PMF α) (a : ℕ) (q₀ : α)
    (Good : α → Prop) [DecidablePred Good] : ℝ≥0∞ :=
  ∑' q, if Good q then 0 else iter K a q₀ q

theorem recentred_split_of_endpoint_failure
    (K : α → PMF α) (a b : ℕ) (q₀ : α)
    (Good : α → Prop) [DecidablePred Good]
    (Bad : α → α → Prop) [∀ q, DecidablePred (Bad q)]
    (εpre ε : ℝ≥0∞)
    (hpre : PrefixEndpointFailure K a q₀ Good ≤ εpre)
    (hgood : ∀ q, Good q → hitProb (Bad q) K b q ≤ ε) :
    ∑' q, iter K a q₀ q * hitProb (Bad q) K b q ≤ εpre + ε :=
  recentred_split K a b q₀ Good Bad εpre ε hpre hgood

end Tri

#print axioms Tri.iter_anchorKernel
#print axioms Tri.anchorKernel_freeze
#print axioms Tri.iter_freeze_anchorKernel
#print axioms Tri.hitProb_anchorKernel
#print axioms Tri.recentred_split_anchored
#print axioms Tri.recentred_split_of_endpoint_failure
