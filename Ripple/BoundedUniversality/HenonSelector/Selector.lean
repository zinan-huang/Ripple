/-
Ripple.BoundedUniversality.HenonSelector.Selector
------------------------------
Selector definitions: algebraic selector, computable arithmetic
selector, universal itinerary family.
-/

import Ripple.BoundedUniversality.HenonSelector.Itinerary
import Ripple.BoundedUniversality.Core.Computability

namespace Ripple.BoundedUniversality.HenonSelector

open Ripple.BoundedUniversality.Core

abbrev MarkovCylinderCode := List Bool

def HitsCylinder (s : BinSeq) (C : MarkovCylinderCode) : Prop :=
  ∃ t : ℕ, ∀ i : Fin C.length, (Nat.iterate shift t s) (i : ℤ) = C.get i

structure UniversalItineraryFamily where
  s : ℕ → BinSeq
  halts : ℕ → Prop
  haltCylinder : MarkovCylinderCode := [true, true, true]
  encodes_halt :
    ∀ n : ℕ, halts n ↔ HitsCylinder (s n) haltCylinder
  halts_not_computable :
    NoComputableBoolDecider halts

structure AlgebraicSelector
    (hc : HenonCoding) (fam : UniversalItineraryFamily) where
  φ : ℕ → Point2
  alg : ∀ n : ℕ, IsAlgPoint (φ n)
  realizes : ∀ n : ℕ, φ n = hc.omega (fam.s n)

def InOmega (hc : HenonCoding) (z : Point2) : Prop :=
  ∃ s : BinSeq, hc.omega s = z

def NonperiodicRequired (fam : UniversalItineraryFamily) : Prop :=
  ∃ n : ℕ, ¬ IsPeriodicSeq (fam.s n)

def AlgebraicHorseshoeRigidity (hc : HenonCoding) : Prop :=
  ∀ z : Point2,
    InOmega hc z →
    IsAlgPoint z →
    IsHenonPeriodic z

end Ripple.BoundedUniversality.HenonSelector
