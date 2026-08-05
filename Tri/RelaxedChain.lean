/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.RelaxedStep

/-!
# The unequal-rate Tri chain

This packages the normalized unequal-rate interaction step as a fixed-population
chain on the `X` count.  Outside the physical range the chain is inert, exactly
as for `Tri.triChain`.
-/

namespace Tri

/-- The unequal-rate Tri CRN as a chain on the `X` count. -/
noncomputable def relaxedTriChain
    (r : RelaxedRate) (n : ℕ) : ℕ → PMF ℕ := fun x =>
  if h : 3 ≤ n ∧ x ≤ n then
    relaxedTriStep r x (n - x) (by omega)
  else
    PMF.pure x

/-- Subtraction-free rewriting of the relaxed chain on an interior state. -/
theorem relaxedTriChain_apply
    (r : RelaxedRate) {n a b : ℕ}
    (hpop : a + b + 2 = n) (h3 : 3 ≤ n) :
    relaxedTriChain r n (a + 1) =
      relaxedTriStep r (a + 1) (b + 1) (by omega) := by
  unfold relaxedTriChain
  rw [dif_pos ⟨h3, by omega⟩]
  congr 1
  omega

/-- All-`X` consensus is absorbing in the fixed-population relaxed chain. -/
theorem relaxedTriChain_consensus_X
    (r : RelaxedRate) {n : ℕ} (h3 : 3 ≤ n) :
    relaxedTriChain r n n = PMF.pure n := by
  unfold relaxedTriChain
  rw [dif_pos ⟨h3, le_rfl⟩]
  simp only [Nat.sub_self]
  exact relaxedTriStep_consensus_X r n (by omega)

/-- All-`Y` consensus is absorbing in the fixed-population relaxed chain. -/
theorem relaxedTriChain_consensus_Y
    (r : RelaxedRate) {n : ℕ} (h3 : 3 ≤ n) :
    relaxedTriChain r n 0 = PMF.pure 0 := by
  unfold relaxedTriChain
  rw [dif_pos ⟨h3, Nat.zero_le n⟩]
  simp only [Nat.sub_zero]
  exact relaxedTriStep_consensus_Y r n (by omega)

end Tri

#print axioms Tri.relaxedTriChain_apply
#print axioms Tri.relaxedTriChain_consensus_X
#print axioms Tri.relaxedTriChain_consensus_Y
