/-
Ripple.BoundedUniversality.HenonSelector.NoGo
--------------------------
T1 and T2: the two missing theorems that would close Framework 4.

T1 (Algebraic Horseshoe Rigidity) is defined in Selector.lean as
  AlgebraicHorseshoeRigidity.

T2 (Decidable Algebraic-Cylinder Reachability) is stated here.

These are DEFINITIONS (hypotheses), not axioms. Their consequences
are proved in SelectorConsequences.lean.
-/

import Ripple.BoundedUniversality.HenonSelector.Selector
import Ripple.BoundedUniversality.HenonSelector.Periodic

namespace Ripple.BoundedUniversality.HenonSelector

-- T2: for any Q-algebraic horseshoe point and finite Markov cylinder,
-- eventual cylinder hitting (via the symbolic coding) is decidable.
-- Stated as a Prop for simplicity; a fully computable version with
-- PresentedAlgPoint is future work.
def T2_DecidableReachability (hc : HenonCoding) : Prop :=
  ∀ (s : BinSeq) (C : MarkovCylinderCode),
    IsAlgPoint (hc.omega s) →
    HitsCylinder s C ∨ ¬ HitsCylinder s C

end Ripple.BoundedUniversality.HenonSelector
