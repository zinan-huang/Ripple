/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.HitProbMono

/-!
# Lemma 15's domination step

This is where the deterministic glue is spent.

`recentred_split`'s `hgood` must bound the GLOBAL-centred window event.  The
windowed tail bounds a CONDITIONAL-centred `UrnWindowBad`.  `hitProb_mono_target`
converts the second into the first — provided the first is contained in the
second, which is what this file proves.

## The containment

`GlobalBad c Δ s q z` says: between the anchor `q` and the state `z` there were
`k ≤ s` reveals of which `w` were red, and `Δ + k·c ≤ w` — the subtraction-free
form of "the red count exceeded its global-fraction prediction by `Δ`".

Given a prefix endpoint whose own fraction has not drifted past `Δ/(3s)`, the
`2/3 + 1/3` split turns that into `2Δ/3 ≤ w − k·cq`, and the recentring identity
turns THAT into `2Δ/3 ≤ t · urnM cq z`.  Dividing by `t ≤ ν₂` gives the window's
radius `2Δ/(3ν₂)`.

## The simplification worth noting

Applying `urn_recentre_identity` at the centre `cq` itself makes its anchor term
`urnM cq q = cq − cq` vanish, so the identity collapses to

```text
w − k·cq  =  t · urnM cq z
```

with no residue.  That is why the split's conclusion transfers to the window
observable in one step rather than needing a second reconciliation.

## The clock

`u + s + 1 = ν₂` and `k ≤ s` with `k + t = ν₂` give `u + 1 ≤ t` by `omega`, so
`UrnWindowBad`'s clock conjunct comes for free from the window-length bound —
no separate reachability argument.
-/

namespace Tri
open scoped ENNReal


/-- The global-centred window event, anchored at the prefix endpoint `q`. -/
def GlobalBad (c Δ : ℝ) (s : ℕ) (q z : ℕ × ℕ) : Prop :=
  ∃ w k : ℕ, z.1 + w = q.1 ∧ k + (z.1 + z.2) = q.1 + q.2 ∧ k ≤ s
    ∧ Δ + (k : ℝ) * c ≤ (w : ℝ)

noncomputable instance (c Δ : ℝ) (s : ℕ) (q : ℕ × ℕ) :
    DecidablePred (GlobalBad c Δ s q) := fun _ => Classical.dec _

/-- **The domination.**  A global-centred excess at a good prefix endpoint forces
a conditional-centred excess of `2Δ/(3ν₂)` at the same state, with the clock
conjunct supplied by the window's length bound. -/
theorem urn_global_dominates
    (c Δ : ℝ) (s u : ℕ) (q z : ℕ × ℕ) (lam : ℝ)
    (hs : 0 < s) (hΔ : 0 ≤ Δ) (hlam : 0 < lam)
    (hq : 0 < q.1 + q.2)
    (hclock : u + s + 1 = q.1 + q.2)
    (hgood : (q.1 : ℝ) / ((q.1 : ℝ) + (q.2 : ℝ)) ≤ c + Δ / (3 * (s : ℝ)))
    (hbad : GlobalBad c Δ s q z) :
    UrnWindowBad ((q.1 : ℝ) / ((q.1 : ℝ) + (q.2 : ℝ)))
      (2 * Δ / (3 * ((q.1 : ℝ) + (q.2 : ℝ)))) lam u z := by
  obtain ⟨w, k, hw, hkt, hks, hexc⟩ := hbad
  set cq : ℝ := (q.1 : ℝ) / ((q.1 : ℝ) + (q.2 : ℝ)) with hcqdef
  have hν2 : (0 : ℝ) < (q.1 : ℝ) + (q.2 : ℝ) := by
    have : (0 : ℝ) < ((q.1 + q.2 : ℕ) : ℝ) := by exact_mod_cast hq
    push_cast at this; linarith
  have htpos : 0 < z.1 + z.2 := by omega
  have htR : (0 : ℝ) < (z.1 : ℝ) + (z.2 : ℝ) := by
    have : (0 : ℝ) < ((z.1 + z.2 : ℕ) : ℝ) := by exact_mod_cast htpos
    push_cast at this; linarith
  -- the identity at centre `cq`, where the anchor term vanishes
  have hid := urn_recentre_identity cq z.1 w k (z.1 + z.2) q.1 q.2 z.2
    hw (by omega) rfl (by linarith) (by
      have : ((z.1 + z.2 : ℕ) : ℝ) = (z.1 : ℝ) + (z.2 : ℝ) := by push_cast; ring
      rw [this]; linarith)
  have hanchor : urnM cq (q.1, q.2) = 0 := by
    unfold urnM; simp only; rw [hcqdef]; ring
  rw [hanchor, mul_zero, sub_zero] at hid
  -- the 2/3 split
  have hsplit := urn_split_two_thirds Δ c cq (w : ℝ) k s hs
    (by exact_mod_cast hks) hΔ (by linarith) (by linarith [hgood])
  refine ⟨by omega, ?_⟩
  rw [abs_of_pos hlam]
  have hMt : 2 * Δ / 3 ≤ ((z.1 + z.2 : ℕ) : ℝ) * urnM cq z := by
    rw [← hid]; linarith [hsplit]
  have hcast : ((z.1 + z.2 : ℕ) : ℝ) = (z.1 : ℝ) + (z.2 : ℝ) := by push_cast; ring
  rw [hcast] at hMt
  have hle : (z.1 : ℝ) + (z.2 : ℝ) ≤ (q.1 : ℝ) + (q.2 : ℝ) := by
    have : ((z.1 + z.2 : ℕ) : ℝ) ≤ ((q.1 + q.2 : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_of_add_left_le (le_of_eq hkt)
    push_cast at this; linarith
  have hMlb : 2 * Δ / (3 * ((q.1 : ℝ) + (q.2 : ℝ))) ≤ urnM cq z := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [hMt, hle, htR]
  nlinarith [hMlb, hlam]
end Tri

#print axioms Tri.urn_global_dominates
