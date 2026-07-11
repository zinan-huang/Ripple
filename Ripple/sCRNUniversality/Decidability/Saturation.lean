/-
  Backward coverability saturation: closure check and step function.
-/
import Ripple.sCRNUniversality.Core.Petri

namespace Ripple.sCRNUniversality.Decidability

variable {S : Type*} [Fintype S] [DecidableEq S]

open Ripple.sCRNUniversality

def stateLe (a b : State S) : Prop := ∀ s, a s ≤ b s

instance (a b : State S) : Decidable (stateLe a b) :=
  Fintype.decidableForallFintype

def basisCovers (B : Finset (State S)) (m : State S) : Prop :=
  ∃ b ∈ B, stateLe b m

instance (B : Finset (State S)) (m : State S) : Decidable (basisCovers B m) :=
  show Decidable (∃ b ∈ B, stateLe b m) from inferInstance

def predecessorOfPetri (P : PetriNet S) (i : P.I) (b : State S) : State S :=
  fun s => b s - P.post i s + P.pre i s

def canProducePetri (P : PetriNet S) (i : P.I) (b : State S) : Prop :=
  ∀ s, P.post i s ≤ b s

instance (P : PetriNet S) (i : P.I) (b : State S) :
    Decidable (canProducePetri P i b) :=
  Fintype.decidableForallFintype

def isClosed (P : PetriNet S) (B : Finset (State S)) : Prop :=
  ∀ b ∈ B, ∀ i : P.I,
    canProducePetri P i b →
    basisCovers B (predecessorOfPetri P i b)

instance (P : PetriNet S) (B : Finset (State S)) : Decidable (isClosed P B) :=
  show Decidable (∀ b ∈ B, ∀ i : P.I, canProducePetri P i b → basisCovers B (predecessorOfPetri P i b)) from
    inferInstance

end Ripple.sCRNUniversality.Decidability
