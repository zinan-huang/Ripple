import Ripple.sCRNUniversality.Core.Footprint
import Ripple.sCRNUniversality.Computation.CRNRefinement

namespace Ripple.sCRNUniversality

universe u v w x

namespace NetworkRefinement

variable {S : Type u} {T : Type v}
variable {Nhi : Network.{u, w} S} {Nlo : Network.{v, x} T}

def EncPreservesAgreesOutside
    (R : NetworkRefinement Nhi Nlo)
    (PhiHi : S -> Prop) (PhiLo : T -> Prop) : Prop :=
  forall {a b : State S},
    State.AgreesOutside PhiHi a b ->
      State.AgreesOutside PhiLo (R.enc a) (R.enc b)

theorem agreesOutside_transfer
    (R : NetworkRefinement Nhi Nlo)
    {a b : State S}
    {PhiHi : S -> Prop} {PhiLo : T -> Prop}
    (hFrameHi : State.AgreesOutside PhiHi a b)
    (hEnc : R.EncPreservesAgreesOutside PhiHi PhiLo) :
    State.AgreesOutside PhiLo (R.enc a) (R.enc b) :=
  hEnc hFrameHi

theorem agreesOutside_transfer_of_reaches
    (R : NetworkRefinement Nhi Nlo)
    {a b : State S}
    (_hReach : Nhi.Reaches a b)
    {PhiHi : S -> Prop} {PhiLo : T -> Prop}
    (hFrameHi : State.AgreesOutside PhiHi a b)
    (hEnc : R.EncPreservesAgreesOutside PhiHi PhiLo) :
    State.AgreesOutside PhiLo (R.enc a) (R.enc b) :=
  R.agreesOutside_transfer hFrameHi hEnc

/--
Safer spelling of `agreesOutside_transfer`: this theorem is purely an encoding
frame-transfer statement. It does not use reachability.
-/
theorem enc_agreesOutside_transfer
    (R : NetworkRefinement Nhi Nlo)
    {a b : State S}
    {PhiHi : S -> Prop} {PhiLo : T -> Prop}
    (hFrameHi : State.AgreesOutside PhiHi a b)
    (hEnc : R.EncPreservesAgreesOutside PhiHi PhiLo) :
    State.AgreesOutside PhiLo (R.enc a) (R.enc b) :=
  R.agreesOutside_transfer hFrameHi hEnc

end NetworkRefinement

namespace BoundedNetworkRefinement

variable {S : Type u} {T : Type v}
variable {Nhi : Network.{u, w} S} {Nlo : Network.{v, x} T}

def EncPreservesAgreesOutside
    (R : BoundedNetworkRefinement Nhi Nlo)
    (PhiHi : S -> Prop) (PhiLo : T -> Prop) : Prop :=
  R.toNetworkRefinement.EncPreservesAgreesOutside PhiHi PhiLo

theorem agreesOutside_transfer
    (R : BoundedNetworkRefinement Nhi Nlo)
    {a b : State S}
    {PhiHi : S -> Prop} {PhiLo : T -> Prop}
    (hFrameHi : State.AgreesOutside PhiHi a b)
    (hEnc : R.EncPreservesAgreesOutside PhiHi PhiLo) :
    State.AgreesOutside PhiLo (R.enc a) (R.enc b) :=
  R.toNetworkRefinement.agreesOutside_transfer hFrameHi hEnc

/--
Safer spelling of `agreesOutside_transfer`: this theorem is purely an encoding
frame-transfer statement. It does not use bounded execution, reachability, or
the firing-count bound.
-/
theorem enc_agreesOutside_transfer
    (R : BoundedNetworkRefinement Nhi Nlo)
    {a b : State S}
    {PhiHi : S -> Prop} {PhiLo : T -> Prop}
    (hFrameHi : State.AgreesOutside PhiHi a b)
    (hEnc : R.EncPreservesAgreesOutside PhiHi PhiLo) :
    State.AgreesOutside PhiLo (R.enc a) (R.enc b) :=
  R.agreesOutside_transfer hFrameHi hEnc

end BoundedNetworkRefinement

end Ripple.sCRNUniversality
