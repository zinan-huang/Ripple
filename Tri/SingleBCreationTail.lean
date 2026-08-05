/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.SingleBBudget

/-!
# The creation-imbalance tail, wired up

The three preceding files supply the pieces: the supermartingale step
(`SingleBCreationStep`), the general maximal inequality `ville_frozen`
(`Lemma14Leaf`), and the creation budget (`SingleBBudget`). This file names the
threshold and states the tail, which is the wiring the budget commit flagged as
unwritten.

## The bad set carries the budget, exactly as the urn's carries the clock

```text
CreationBad D H q  :=  (q.cx + q.cy ≤ H)  ∧  (D + q.cy ≤ q.cx)
```

Both conjuncts are load-bearing and for the same structural reason as in
`Tri/Lemma15Window.lean`: the potential's compensator is `−(λ²/2)(CX+CY)`,
which SHRINKS the potential as creations accumulate. A ledger with the same
imbalance but a larger creation count sits BELOW the threshold, so without the
budget conjunct the pointwise containment fails and the `tsum` bound with it.

Note the deviation conjunct is `D + CY ≤ CX`, not `CX − CY ≥ D`. Same content,
no ℕ-subtraction.

## The optimum, and why it is the expected constant

At `λ = D/H` the exponent `λD − (λ²/2)H` equals `D²/(2H)`, so the tail is

```text
exp (−D² / (2H))
```

which is exactly Azuma–Hoeffding for a fair `±1` walk of length `H`. Recovering
the textbook constant rather than something worse is the check that the
compensator `λ²/2` was the right one.
-/

namespace Tri

open scoped ENNReal

variable {n : ℕ}

/-- The bad set: the creation imbalance has reached `D` while the creation
count is still within budget `H`.  Both conjuncts are needed — see the module
docstring. -/
def CreationBad (D H : ℕ) (q : SingleLedger n) : Prop :=
  q.cx + q.cy ≤ H ∧ D + q.cy ≤ q.cx

instance (D H : ℕ) : DecidablePred (CreationBad D H (n := n)) := fun _ =>
  inferInstanceAs (Decidable (_ ∧ _))

/-- The threshold the bad set is guaranteed to have reached. -/
noncomputable def creationTheta (lam : ℝ) (D H : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (lam * (D : ℝ) - lam ^ 2 / 2 * (H : ℝ)))

theorem creationTheta_ne_zero (lam : ℝ) (D H : ℕ) :
    creationTheta lam D H ≠ 0 := by
  unfold creationTheta
  simp [ENNReal.ofReal_eq_zero, not_le, Real.exp_pos]

theorem creationTheta_ne_top (lam : ℝ) (D H : ℕ) :
    creationTheta lam D H ≠ ⊤ := ENNReal.ofReal_ne_top

/-- **Containment.**  Every in-budget ledger whose imbalance has reached `D`
has potential at least `θ`.

Two monotonicities, one per conjunct: the deviation conjunct pays for the
linear term (this is where `0 ≤ λ` is used), the budget conjunct pays for the
compensator. -/
theorem creation_contain (lam : ℝ) (hlam : 0 ≤ lam) (D H : ℕ)
    (q : SingleLedger n) (hq : CreationBad D H q) :
    creationTheta lam D H ≤ creationG lam q := by
  obtain ⟨hbudget, hdev⟩ := hq
  unfold creationTheta creationG creationExp creationImbalance creationCount
  refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
  have hD : (D : ℝ) ≤ (q.cx : ℝ) - (q.cy : ℝ) := by
    have : ((D + q.cy : ℕ) : ℝ) ≤ ((q.cx : ℕ) : ℝ) := by exact_mod_cast hdev
    push_cast at this
    linarith
  have hH : ((q.cx + q.cy : ℕ) : ℝ) ≤ (H : ℝ) := by exact_mod_cast hbudget
  have hlin : lam * (D : ℝ) ≤ lam * ((q.cx : ℝ) - (q.cy : ℝ)) :=
    mul_le_mul_of_nonneg_left hD hlam
  have hcomp : lam ^ 2 / 2 * ((q.cx + q.cy : ℕ) : ℝ) ≤ lam ^ 2 / 2 * (H : ℝ) :=
    mul_le_mul_of_nonneg_left hH (by positivity)
  linarith

/-- A fresh ledger sits at potential exactly `1`: no creations yet, so both the
imbalance and the compensator vanish. -/
theorem creationG_fresh (lam : ℝ) (s : SingleState n) :
    creationG lam (⟨s, 0, 0, 0, 0⟩ : SingleLedger n) = 1 := by
  unfold creationG creationExp creationImbalance creationCount
  norm_num

/-- **The maximal creation tail.**  Over EVERY prefix of the run, the mass of
trajectories whose creation imbalance has reached `D` while still within budget
`H` is at most `1/θ`.

`ville_frozen` supplies the maximal strengthening for free — the bound is the
same as the fixed-time one. -/
theorem creation_tail_maximal (hn : 2 ≤ n) (lam : ℝ) (hlam : 0 ≤ lam)
    (D H : ℕ) (s : SingleState n) :
    (⨆ T : ℕ, hitProb (CreationBad D H) (singleLedgerStep n hn) T
        (⟨s, 0, 0, 0, 0⟩ : SingleLedger n))
      ≤ 1 / creationTheta lam D H := by
  have h := ville_frozen (singleLedgerStep n hn) (CreationBad D H)
    (creationG lam) (creationTheta lam D H)
    (creationTheta_ne_zero lam D H) (creationTheta_ne_top lam D H)
    (creation_contain lam hlam D H)
    (fun q => creationG_step n hn lam q)
    (⟨s, 0, 0, 0, 0⟩ : SingleLedger n)
  rwa [creationG_fresh] at h

/-- The quotient in closed exponential form. -/
theorem one_div_creationTheta (lam : ℝ) (D H : ℕ) :
    1 / creationTheta lam D H
      = ENNReal.ofReal (Real.exp (-(lam * (D : ℝ) - lam ^ 2 / 2 * (H : ℝ)))) := by
  unfold creationTheta
  rw [← ENNReal.ofReal_one,
    ← ENNReal.ofReal_div_of_pos (Real.exp_pos _)]
  congr 1
  rw [Real.exp_neg, one_div]

/-- **The optimised tail.**  At `λ = D/H` the exponent is `D²/(2H)`, giving

```text
exp (−D² / (2H))
```

which is Azuma–Hoeffding for a fair `±1` walk of length `H`.  Recovering the
textbook constant is the check that the compensator `λ²/2` was right. -/
theorem creation_exponent_optimised (D H : ℕ) (hH : 0 < H) :
    -(((D : ℝ) / (H : ℝ)) * (D : ℝ)
        - ((D : ℝ) / (H : ℝ)) ^ 2 / 2 * (H : ℝ))
      = -((D : ℝ) ^ 2 / (2 * (H : ℝ))) := by
  have hH' : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH
  field_simp
  ring

/-- **The Single-B creation tail, optimised.**  This is the statement the
physical-gap recovery consumes. -/
theorem creation_tail (hn : 2 ≤ n) (D H : ℕ) (hH : 0 < H)
    (s : SingleState n) :
    (⨆ T : ℕ, hitProb (CreationBad D H) (singleLedgerStep n hn) T
        (⟨s, 0, 0, 0, 0⟩ : SingleLedger n))
      ≤ ENNReal.ofReal (Real.exp (-((D : ℝ) ^ 2 / (2 * (H : ℝ))))) := by
  have hH' : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH
  have hlam : (0 : ℝ) ≤ (D : ℝ) / (H : ℝ) := by positivity
  have h := creation_tail_maximal hn ((D : ℝ) / (H : ℝ)) hlam D H s
  rw [one_div_creationTheta, creation_exponent_optimised D H hH] at h
  exact h

end Tri

#print axioms Tri.creation_contain
#print axioms Tri.creationG_fresh
#print axioms Tri.creation_tail_maximal
#print axioms Tri.one_div_creationTheta
#print axioms Tri.creation_exponent_optimised
#print axioms Tri.creation_tail
