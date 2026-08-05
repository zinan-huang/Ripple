/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Compose
import Tri.Freeze

/-!
# Emulation transfer: moving a `Reaches` statement across a lumping map

The paper's abstract states its own architecture:

> We obtain simple analyses of three bimolecular protocols, including that of
> Angluin et al., by showing how they **emulate** the tri-molecular protocol.

So Heavy-B, Double-B and Single-B are three distinct bimolecular CRNs, each
transported from the tri-molecular analysis — not three regimes of one state
space. (I had it the other way round; the abstract settles it.)

This file supplies the transport. The hypothesis is the exact Markov
homomorphism, or **intertwining**,

```text
∀ s, (K₁ s).map φ = K₂ (φ s)
```

which says: take one step downstairs and lump, or lump and take one step
upstairs — same law. Nothing weaker will do for an exact transfer, and nothing
stronger is needed.

## The one identity that makes this cheap

Transferring a failure mass looks like it needs a fibrewise `tsum` argument,
because `PMF.map_apply` unfolds a pushforward into a sum over the preimage.
It does not. The failure mass is an `expect`:

```text
∑' z, (if Q z then 0 else μ z)  =  expect μ (fun z => if Q z then 0 else 1)
```

and `expect_map` (already in `Tri/Decay.lean`) pushes an `expect` through a
`map` for free. The fibre sum never appears.

## Scope

Everything here is exact — no leak term. A partial intertwining (holding only
on a reachable subregion, or up to a set of small mass) would transfer with an
additive leak; that is not built, because the CRN emulations are expected to
be exact on the reachable set and an unused approximate version would be
scaffolding.
-/

namespace Tri

open scoped ENNReal

variable {α β : Type*}

/-- `φ` lumps `K₁` onto `K₂`: stepping then lumping equals lumping then
stepping.  This is an exact Markov homomorphism. -/
def Intertwines (φ : α → β) (K₁ : α → PMF α) (K₂ : β → PMF β) : Prop :=
  ∀ s, (K₁ s).map φ = K₂ (φ s)

/-- The intertwining propagates to every horizon. -/
theorem iter_map_of_intertwines {φ : α → β} {K₁ : α → PMF α} {K₂ : β → PMF β}
    (h : Intertwines φ K₁ K₂) (T : ℕ) (s : α) :
    (iter K₁ T s).map φ = iter K₂ T (φ s) := by
  induction T generalizing s with
  | zero => simp [iter, PMF.pure_map]
  | succ T ih =>
      rw [iter_succ, iter_succ, PMF.map_bind]
      calc (K₁ s).bind (fun z => (iter K₁ T z).map φ)
          = (K₁ s).bind (fun z => iter K₂ T (φ z)) :=
            congrArg _ (funext fun z => ih z)
        _ = ((K₁ s).map φ).bind (iter K₂ T) := (PMF.bind_map _ _ _).symm
        _ = (K₂ (φ s)).bind (iter K₂ T) := by rw [h s]

/-- The failure mass is an expectation.  This is the whole reason the transfer
below costs three lines instead of a fibrewise `tsum` argument. -/
theorem failureMass_eq_expect (μ : PMF α) (Q : α → Prop) [DecidablePred Q] :
    (∑' z, if Q z then 0 else μ z)
      = expect μ (fun z => if Q z then 0 else 1) := by
  unfold expect
  refine tsum_congr fun z => ?_
  by_cases hz : Q z <;> simp [hz]

/-- **Pushforward of a failure mass.**  Measuring a lumped target downstairs
is measuring its preimage upstairs. -/
theorem failureMass_map (μ : PMF α) (φ : α → β) (Q : β → Prop)
    [DecidablePred Q] :
    (∑' w, if Q w then 0 else (μ.map φ) w)
      = ∑' z, if Q (φ z) then 0 else μ z := by
  rw [failureMass_eq_expect, failureMass_eq_expect, expect_map]

/-- **Emulation transfer for `Reaches`.**

If `φ` lumps `K₁` onto `K₂`, then every `Reaches` statement for `K₂` pulls
back along `φ` with the SAME horizon and the SAME failure bound.  There is no
loss: the intertwining is exact, so the two failure masses are equal, not
merely comparable. -/
theorem Reaches.transfer {φ : α → β} {K₁ : α → PMF α} {K₂ : β → PMF β}
    (h : Intertwines φ K₁ K₂) {T : ℕ} {P Q : β → Prop} [DecidablePred Q]
    {ε : ℝ≥0∞} (h₂ : Reaches K₂ T P Q ε) :
    Reaches K₁ T (fun s => P (φ s)) (fun z => Q (φ z)) ε := by
  intro s hs
  have hmap : (∑' z, if Q (φ z) then 0 else iter K₁ T s z)
      = ∑' w, if Q w then 0 else (iter K₂ T (φ s)) w := by
    rw [← iter_map_of_intertwines h T s, failureMass_map]
  rw [hmap]
  exact h₂ (φ s) hs

/-! ### Compatibility with `freeze`

The maximal statements all run on frozen kernels, so the transfer is only
useful if freezing commutes with lumping.  It does, PROVIDED the frozen set
downstairs is the preimage of the frozen set upstairs — which is exactly the
shape a transferred target has. -/

/-- Freezing on a pulled-back target preserves the intertwining. -/
theorem Intertwines.onFreeze {φ : α → β} {K₁ : α → PMF α} {K₂ : β → PMF β}
    (h : Intertwines φ K₁ K₂) (B : β → Prop) [DecidablePred B] :
    Intertwines φ (freeze (fun z => B (φ z)) K₁) (freeze B K₂) := by
  intro s
  unfold freeze
  by_cases hs : B (φ s)
  · rw [if_pos hs, if_pos hs, PMF.pure_map]
  · rw [if_neg hs, if_neg hs]
    exact h s

/-- **Emulation transfer for `hitProb`.**  Equality, not an inequality: the
probability of ever entering a lumped set is the probability of ever entering
its preimage. -/
theorem hitProb_transfer {φ : α → β} {K₁ : α → PMF α} {K₂ : β → PMF β}
    (h : Intertwines φ K₁ K₂) (B : β → Prop) [DecidablePred B]
    (T : ℕ) (s : α) :
    hitProb (fun z => B (φ z)) K₁ T s = hitProb B K₂ T (φ s) := by
  unfold hitProb
  rw [← iter_map_of_intertwines (h.onFreeze B) T s, expect_map]
  rfl

/-- The maximal form transfers too, since the supremum is taken of equal
families. -/
theorem iSup_hitProb_transfer {φ : α → β} {K₁ : α → PMF α} {K₂ : β → PMF β}
    (h : Intertwines φ K₁ K₂) (B : β → Prop) [DecidablePred B] (s : α) :
    (⨆ T : ℕ, hitProb (fun z => B (φ z)) K₁ T s)
      = ⨆ T : ℕ, hitProb B K₂ T (φ s) := by
  exact iSup_congr fun T => hitProb_transfer h B T s

/-- Transferring an expectation bound, for potential-style conclusions. -/
theorem expect_iter_transfer {φ : α → β} {K₁ : α → PMF α} {K₂ : β → PMF β}
    (h : Intertwines φ K₁ K₂) (V : β → ℝ≥0∞) (T : ℕ) (s : α) :
    expect (iter K₁ T s) (fun z => V (φ z)) = expect (iter K₂ T (φ s)) V := by
  rw [← iter_map_of_intertwines h T s, expect_map]

end Tri

#print axioms Tri.iter_map_of_intertwines
#print axioms Tri.failureMass_map
#print axioms Tri.Reaches.transfer
#print axioms Tri.Intertwines.onFreeze
#print axioms Tri.hitProb_transfer
#print axioms Tri.iSup_hitProb_transfer
#print axioms Tri.expect_iter_transfer
