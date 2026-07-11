import Ripple.sCRNUniversality.Core.Finite

namespace Ripple.sCRNUniversality

namespace Network

variable {S : Type u}

inductive OneRxnIdx where
  | step
deriving DecidableEq, Repr

instance : Fintype OneRxnIdx where
  elems := {OneRxnIdx.step}
  complete := by
    intro i
    cases i
    simp

def oneRxnNetwork (rho : Reaction S) : Network S where
  I := OneRxnIdx
  rxn
    | OneRxnIdx.step => rho

@[simp]
theorem oneRxnNetwork_rxn_step (rho : Reaction S) :
    (oneRxnNetwork rho).rxn OneRxnIdx.step = rho := by
  rfl

theorem oneRxn_exec {rho : Reaction S} {z z' : State S}
    (h : rho.FiresTo z z') :
    (oneRxnNetwork rho).Exec z z' [OneRxnIdx.step] := by
  simpa [oneRxnNetwork] using
    (ExecOf.cons h (ExecOf.nil z') :
      ExecOf (oneRxnNetwork rho).StepAt z z' [OneRxnIdx.step])

theorem oneRxnNetwork_exec_iff {rho : Reaction S} {z z' : State S} :
    (oneRxnNetwork rho).Exec z z' [OneRxnIdx.step] <->
      rho.FiresTo z z' := by
  constructor
  · intro hExec
    simpa [oneRxnNetwork, Network.StepAt] using
      (ExecOf.singleton_iff.mp hExec)
  · exact oneRxn_exec

theorem oneRxnNetwork_reaches_of_firesTo
    {rho : Reaction S} {z z' : State S}
    (h : rho.FiresTo z z') :
    (oneRxnNetwork rho).Reaches z z' :=
  Network.reaches_of_exec (oneRxn_exec h)

theorem oneRxnNetwork_coverable_of_firesTo_of_covers
    {rho : Reaction S} {z z' target : State S}
    (h : rho.FiresTo z z')
    (hCovers : Covers z' target) :
    (oneRxnNetwork rho).CoverableFrom z target :=
  Network.coverable_of_reaches_of_covers
    (oneRxnNetwork_reaches_of_firesTo h)
    hCovers

theorem oneRxnNetwork_coverable_of_firesTo_of_le
    {rho : Reaction S} {z z' target : State S}
    (h : rho.FiresTo z z')
    (hTarget : forall s, target s <= z' s) :
    (oneRxnNetwork rho).CoverableFrom z target :=
  oneRxnNetwork_coverable_of_firesTo_of_covers h hTarget

theorem oneRxnNetwork_speciesCoverableFrom_of_firesTo_coord
    [DecidableEq S] {rho : Reaction S} {z z' : State S}
    {species : S} {amount : Nat}
    (h : rho.FiresTo z z')
    (hamount : amount <= z' species) :
    (oneRxnNetwork rho).SpeciesCoverableFrom z species amount :=
  Network.speciesCoverableFrom_of_reaches_coord
    (oneRxnNetwork_reaches_of_firesTo h)
    hamount

theorem oneRxnNetwork_speciesCoverableFrom_one_of_firesTo_pos
    [DecidableEq S] {rho : Reaction S} {z z' : State S}
    {species : S}
    (h : rho.FiresTo z z')
    (hpos : 0 < z' species) :
    (oneRxnNetwork rho).SpeciesCoverableFrom z species :=
  Network.speciesCoverableFrom_one_of_reaches_pos
    (oneRxnNetwork_reaches_of_firesTo h)
    hpos

theorem oneRxnNetwork_allUnitRate_iff (rho : Reaction S) :
    (oneRxnNetwork rho).allUnitRate <-> rho.unitRate := by
  constructor
  · intro h
    simpa using h OneRxnIdx.step
  · intro h i
    cases i
    simpa using h

theorem oneRxnNetwork_hasPositiveRates_iff (rho : Reaction S) :
    (oneRxnNetwork rho).hasPositiveRates <-> rho.hasPositiveRate := by
  constructor
  · intro h
    simpa using h OneRxnIdx.step
  · intro h i
    cases i
    simpa using h

theorem oneRxnNetwork_equalRates (rho : Reaction S) :
    (oneRxnNetwork rho).equalRates := by
  intro i j
  cases i
  cases j
  rfl

theorem oneRxnNetwork_allBimolecularInput_iff [Fintype S]
    (rho : Reaction S) :
    (oneRxnNetwork rho).allBimolecularInput <->
      rho.isBimolecularInput := by
  constructor
  · intro h
    simpa using h OneRxnIdx.step
  · intro h i
    cases i
    simpa using h

theorem oneRxnNetwork_allAtMostBimolecularInput_iff [Fintype S]
    (rho : Reaction S) :
    (oneRxnNetwork rho).allAtMostBimolecularInput <->
      rho.isAtMostBimolecularInput := by
  constructor
  · intro h
    simpa using h OneRxnIdx.step
  · intro h i
    cases i
    simpa using h

theorem oneRxnNetwork_allAtMostBimolecularOutput_iff [Fintype S]
    (rho : Reaction S) :
    (oneRxnNetwork rho).allAtMostBimolecularOutput <->
      rho.isAtMostBimolecularOutput := by
  constructor
  · intro h
    simpa using h OneRxnIdx.step
  · intro h i
    cases i
    simpa using h

theorem oneRxnNetwork_allAtMostBimolecularFull_iff [Fintype S]
    (rho : Reaction S) :
    (oneRxnNetwork rho).allAtMostBimolecularFull <->
      rho.isAtMostBimolecularFull := by
  constructor
  · intro h
    simpa using h OneRxnIdx.step
  · intro h i
    cases i
    simpa using h

end Network

end Ripple.sCRNUniversality
