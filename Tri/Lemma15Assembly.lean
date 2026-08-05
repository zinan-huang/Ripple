/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Lemma15Domination

/-!
# Lemma 15, assembled

Every ingredient was proved separately; this chains them.

```text
prefix tail (fixed time)      clock free by exact depletion
window tail (maximal)         via ville_frozen
recentring identity           global centre  <->  conditional centre
2/3 + 1/3 split               prefix drift capped at Δ/3
domination                    GlobalBad ⊆ UrnWindowBad at the conditional centre
hitProb_mono_target           transfers the window bound to the global event
recentred_split               charges bad endpoints wholesale, good ones pointwise
```

## Why the bound is uniform over good endpoints

`PrefixGood` carries the endpoint's DEPTH (`q.1 + q.2 = ν₂`) as well as its
drift. That looks like extra baggage and is not: at the recentred start
`urnG_centered_start` collapses the potential's linear term, leaving
`exp(λ²/8 · urnA(ν₂−1))`, which depends on the endpoint only through `ν₂`. So
the window bound is the SAME at every good endpoint, which is exactly what
`recentred_split`'s single `ε` requires.

Without the depth conjunct the bound would be endpoint-dependent and the engine
would not apply — the extra conjunct is what makes the assembly typecheck, not
decoration.

Endpoints off the support fail the depth conjunct, so they land in the `¬Good`
branch; they carry zero mass there, so charging them wholesale costs nothing.
-/

namespace Tri
open scoped ENNReal


/-- The prefix-good predicate: the endpoint sits at the window's opening depth
AND its own red fraction has not drifted adversely past `Δ/(3s)`. -/
def PrefixGood (c Δ : ℝ) (s ν₂ : ℕ) (q : ℕ × ℕ) : Prop :=
  q.1 + q.2 = ν₂ ∧
    (q.1 : ℝ) / ((q.1 : ℝ) + (q.2 : ℝ)) ≤ c + Δ / (3 * (s : ℝ))

noncomputable instance (c Δ : ℝ) (s ν₂ : ℕ) :
    DecidablePred (PrefixGood c Δ s ν₂) := fun _ => Classical.dec _

/-- **`hgood`.**  At every good prefix endpoint the global-centred window event
is bounded, uniformly in the endpoint.

Three steps: domination puts the global event inside a conditional-centred
`UrnWindowBad`; `hitProb_mono_target` transfers the bound; and at the recentred
start `urnG_centered_start` collapses the potential's linear term, which is what
makes the bound the SAME for every good endpoint rather than endpoint-dependent. -/
theorem urn_hgood (c Δ lam : ℝ) (s u ν₂ b : ℕ)
    (hs : 0 < s) (hΔ : 0 ≤ Δ) (hlam : 0 < lam)
    (hclock : u + s + 1 = ν₂)
    (q : ℕ × ℕ) (hq : PrefixGood c Δ s ν₂ q) :
    hitProb (GlobalBad c Δ s q) urnStopped b q
      ≤ ENNReal.ofReal (Real.exp (lam ^ 2 / 8 * urnA (ν₂ - 1)))
        / urnTheta (2 * Δ / (3 * (ν₂ : ℝ))) lam u := by
  obtain ⟨htot, hdrift⟩ := hq
  have hqpos : 0 < q.1 + q.2 := by omega
  have hcast : (q.1 : ℝ) + (q.2 : ℝ) = (ν₂ : ℝ) := by
    have : ((q.1 + q.2 : ℕ) : ℝ) = ((ν₂ : ℕ) : ℝ) := by exact_mod_cast htot
    push_cast at this; linarith
  have hdom : ∀ z, GlobalBad c Δ s q z →
      UrnWindowBad ((q.1 : ℝ) / ((q.1 : ℝ) + (q.2 : ℝ)))
        (2 * Δ / (3 * (ν₂ : ℝ))) lam u z := by
    rw [← hcast]
    exact
      fun z hz => urn_global_dominates c Δ s u q z lam hs hΔ hlam hqpos
        (by omega) hdrift hz
  refine le_trans (hitProb_mono_target hdom b q) ?_
  refine le_trans (le_iSup (fun T => hitProb _ urnStopped T q) b) ?_
  refine le_trans (urn_window_ville _ _ lam u q) ?_
  have hcs : urnG ((q.1 : ℝ) / ((q.1 : ℝ) + (q.2 : ℝ))) lam q
      = ENNReal.ofReal (Real.exp (lam ^ 2 / 8 * urnA (q.1 + q.2 - 1))) := by
    have := urnG_centered_start lam q.1 q.2
    simpa using this
  rw [hcs, htot]

/-- **Lemma 15, assembled.**  `recentred_split` with the prefix-good predicate
and the global-centred bad relation, fed the fixed-time prefix tail and the
`hgood` above.

Every ingredient is proved: the prefix tail is free of its clock by exact
depletion, the window tail is maximal via Ville, and the two are reconciled by
the recentring identity and the `2/3 + 1/3` split through the domination. -/
theorem lemma15_recentred (c Δ lam : ℝ) (s u ν₂ a b R B : ℕ)
    (εpre ε : ℝ≥0∞)
    (hs : 0 < s) (hΔ : 0 ≤ Δ) (hlam : 0 < lam)
    (hclock : u + s + 1 = ν₂)
    (hpre : (∑' q, if PrefixGood c Δ s ν₂ q then 0
        else iter urnStopped a (R, B) q) ≤ εpre)
    (hε : ENNReal.ofReal (Real.exp (lam ^ 2 / 8 * urnA (ν₂ - 1)))
        / urnTheta (2 * Δ / (3 * (ν₂ : ℝ))) lam u ≤ ε) :
    ∑' q, iter urnStopped a (R, B) q
        * hitProb (GlobalBad c Δ s q) urnStopped b q
      ≤ εpre + ε :=
  recentred_split urnStopped a b (R, B) (PrefixGood c Δ s ν₂)
    (GlobalBad c Δ s) εpre ε hpre
    (fun q hq => le_trans (urn_hgood c Δ lam s u ν₂ b hs hΔ hlam hclock q hq) hε)

end Tri

#print axioms Tri.urn_hgood
#print axioms Tri.lemma15_recentred
