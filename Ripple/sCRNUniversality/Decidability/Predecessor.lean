/-
  Predecessor computation for backward coverability.

  pred(b, rxn) = b - rxn.r + rxn.l (when b ≥ rxn.r)
  Meaning: firing rxn from pred(b) produces a state ≥ b.
-/
import Ripple.sCRNUniversality.Core.Petri

namespace Ripple.sCRNUniversality.Decidability

variable {S : Type*} [Fintype S] [DecidableEq S]

open Ripple.sCRNUniversality

def canProduce (rho : Reaction S) (b : State S) : Prop :=
  ∀ s, rho.r s ≤ b s

instance (rho : Reaction S) (b : State S) : Decidable (canProduce rho b) :=
  Fintype.decidableForallFintype

def predecessorOf (rho : Reaction S) (b : State S) : State S :=
  fun s => b s - rho.r s + rho.l s

theorem predecessorOf_enabled (rho : Reaction S) (b : State S)
    (h : ∀ s, rho.r s ≤ b s) :
    rho.enabled (predecessorOf rho b) := by
  intro s; show rho.l s ≤ b s - rho.r s + rho.l s; omega

theorem predecessorOf_fire_ge (rho : Reaction S) (b : State S)
    (h : ∀ s, rho.r s ≤ b s) :
    ∀ s, b s ≤ rho.fire (predecessorOf rho b) s := by
  intro s
  show b s ≤ (b s - rho.r s + rho.l s) - rho.l s + rho.r s
  have := h s; omega

theorem predecessorOf_firesTo_covers (rho : Reaction S) (b : State S)
    (h : ∀ s, rho.r s ≤ b s) :
    rho.FiresTo (predecessorOf rho b) (rho.fire (predecessorOf rho b)) ∧
    ∀ s, b s ≤ rho.fire (predecessorOf rho b) s :=
  ⟨⟨predecessorOf_enabled rho b h, rfl⟩, predecessorOf_fire_ge rho b h⟩

def allPredecessorsFinset (N : Network S) (b : State S) : Finset (State S) :=
  Finset.univ.biUnion fun i : N.I =>
    if canProduce (N.rxn i) b then {predecessorOf (N.rxn i) b} else ∅

def basisPredecessors (N : Network S) (B : Finset (State S)) : Finset (State S) :=
  B.biUnion fun b => allPredecessorsFinset N b

end Ripple.sCRNUniversality.Decidability
