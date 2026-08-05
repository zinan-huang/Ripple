/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.SingleBCreationTail
import Tri.Freeze

/-!
# The mirror Single-B creation tail

`Tri.SingleBCreationTail` controls the `CX`-heavy side of the fair creation
walk.  The `Y`-heavy side is the same exponential supermartingale with the
sign of `λ` flipped: `creationG (-λ)` has exponent

```text
λ·(CY-CX) - (λ²/2)·(CX+CY).
```

The equal `xyToX`/`xyToY` weights are therefore reused through the existing
one-step proof.
-/

namespace Tri

open scoped ENNReal

variable {n : ℕ}

/-- The mirror bad set: the `Y`-oriented creation count is ahead by `D` while
the total number of creations is still within budget `H`. -/
def CreationBadY (D H : ℕ) (q : SingleLedger n) : Prop :=
  q.cx + q.cy ≤ H ∧ D + q.cx ≤ q.cy

instance (D H : ℕ) : DecidablePred (CreationBadY D H (n := n)) := fun _ =>
  inferInstanceAs (Decidable (_ ∧ _))

/-- Any freeze of the Single-B ledger kernel preserves the creation exponential
supermartingale.  Frozen states take a pure step, and outside the frozen set this
is exactly `creationG_step`. -/
theorem creationG_freeze_step (hn : 2 ≤ n) (lam : ℝ)
    (B : SingleLedger n → Prop) [DecidablePred B] (q : SingleLedger n) :
    expect (freeze B (singleLedgerStep n hn) q) (creationG lam)
      ≤ creationG lam q :=
  freeze_conserve (B := B) (K := singleLedgerStep n hn)
    (V := creationG lam) (fun s _ => creationG_step n hn lam s) q

/-- Containment for the `Y`-heavy bad set, using the sign-flipped creation
potential. -/
theorem creationY_contain (lam : ℝ) (hlam : 0 ≤ lam) (D H : ℕ)
    (q : SingleLedger n) (hq : CreationBadY D H q) :
    creationTheta lam D H ≤ creationG (-lam) q := by
  obtain ⟨hbudget, hdev⟩ := hq
  unfold creationTheta creationG creationExp creationImbalance creationCount
  refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
  have hD : (D : ℝ) ≤ (q.cy : ℝ) - (q.cx : ℝ) := by
    have : ((D + q.cx : ℕ) : ℝ) ≤ ((q.cy : ℕ) : ℝ) := by exact_mod_cast hdev
    push_cast at this
    linarith
  have hH : ((q.cx + q.cy : ℕ) : ℝ) ≤ (H : ℝ) := by exact_mod_cast hbudget
  have hlin : lam * (D : ℝ) ≤ lam * ((q.cy : ℝ) - (q.cx : ℝ)) :=
    mul_le_mul_of_nonneg_left hD hlam
  have hcomp : lam ^ 2 / 2 * ((q.cx + q.cy : ℕ) : ℝ) ≤
      lam ^ 2 / 2 * (H : ℝ) :=
    mul_le_mul_of_nonneg_left hH (by positivity)
  nlinarith

/-- A fresh ledger starts the mirror potential at one. -/
theorem creationYG_fresh (lam : ℝ) (s : SingleState n) :
    creationG (-lam) (⟨s, 0, 0, 0, 0⟩ : SingleLedger n) = 1 :=
  creationG_fresh (-lam) s

/-- Maximal inequality for the `Y`-heavy creation imbalance. -/
theorem creationY_tail_maximal (hn : 2 ≤ n) (lam : ℝ) (hlam : 0 ≤ lam)
    (D H : ℕ) (s : SingleState n) :
    (⨆ T : ℕ, hitProb (CreationBadY D H) (singleLedgerStep n hn) T
        (⟨s, 0, 0, 0, 0⟩ : SingleLedger n))
      ≤ 1 / creationTheta lam D H := by
  have h := ville_frozen (singleLedgerStep n hn) (CreationBadY D H)
    (creationG (-lam)) (creationTheta lam D H)
    (creationTheta_ne_zero lam D H) (creationTheta_ne_top lam D H)
    (creationY_contain lam hlam D H)
    (fun q => creationG_step n hn (-lam) q)
    (⟨s, 0, 0, 0, 0⟩ : SingleLedger n)
  rwa [creationYG_fresh] at h

/-- The optimised Single-B mirror creation tail. -/
theorem singleCreationY_tail (hn : 2 ≤ n) (D H : ℕ) (hH : 0 < H)
    (s : SingleState n) :
    (⨆ T : ℕ, hitProb (CreationBadY D H) (singleLedgerStep n hn) T
        (⟨s, 0, 0, 0, 0⟩ : SingleLedger n))
      ≤ ENNReal.ofReal (Real.exp (-((D : ℝ) ^ 2 / (2 * (H : ℝ))))) := by
  have hlam : (0 : ℝ) ≤ (D : ℝ) / (H : ℝ) := by positivity
  have h := creationY_tail_maximal hn ((D : ℝ) / (H : ℝ)) hlam D H s
  rw [one_div_creationTheta, creation_exponent_optimised D H hH] at h
  exact h

end Tri

#print axioms Tri.creationG_freeze_step
#print axioms Tri.creationY_contain
#print axioms Tri.creationYG_fresh
#print axioms Tri.creationY_tail_maximal
#print axioms Tri.singleCreationY_tail
