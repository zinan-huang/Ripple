import Ripple.sCRNUniversality.Computation.CTM.GadgetArithmetic
import Ripple.sCRNUniversality.Core.Schedule

namespace Ripple.sCRNUniversality

namespace CTM

namespace FourPhaseEncoding

universe u

variable {Q : Type u} [DecidableEq Q]

namespace FourPhaseSpecies

omit [DecidableEq Q] in
@[simp]
theorem ctrlOf_ne_tape (st : MicroState Q) :
    FourPhaseSpecies.ctrlOf st ≠ FourPhaseSpecies.tape := by
  cases st
  simp [FourPhaseSpecies.ctrlOf]

omit [DecidableEq Q] in
@[simp]
theorem ctrlOf_ne_tapeBar (st : MicroState Q) :
    FourPhaseSpecies.ctrlOf st ≠ FourPhaseSpecies.tapeBar := by
  cases st
  simp [FourPhaseSpecies.ctrlOf]

omit [DecidableEq Q] in
@[simp]
theorem tape_ne_tapeBar :
    (FourPhaseSpecies.tape : FourPhaseSpecies Q) ≠
      FourPhaseSpecies.tapeBar := by
  simp

end FourPhaseSpecies

omit [DecidableEq Q] in
theorem state_ext
    {z z' : State (Species Q)}
    (hctrl :
      forall q phase readSymbol pendingWrite pendingState,
        z (FourPhaseSpecies.ctrl q phase readSymbol pendingWrite pendingState) =
          z' (FourPhaseSpecies.ctrl q phase readSymbol pendingWrite pendingState))
    (htape :
      z FourPhaseSpecies.tape = z' FourPhaseSpecies.tape)
    (htapeBar :
      z FourPhaseSpecies.tapeBar = z' FourPhaseSpecies.tapeBar) :
    z = z' := by
  funext species
  cases species with
  | ctrl q phase readSymbol pendingWrite pendingState =>
      exact hctrl q phase readSymbol pendingWrite pendingState
  | tape =>
      exact htape
  | tapeBar =>
      exact htapeBar

@[simp]
theorem enc_ctrl_apply
    {s : Nat}
    (c : MicroCfg Q s)
    (q : Q) (phase : Phase4)
    (readSymbol pendingWrite : Option Bool)
    (pendingState : Option Q) :
    enc c
      (FourPhaseSpecies.ctrl q phase readSymbol pendingWrite pendingState) =
      if FourPhaseSpecies.ctrl q phase readSymbol pendingWrite pendingState =
          FourPhaseSpecies.ctrlOf c.state
      then 1 else 0 := by
  by_cases h :
      FourPhaseSpecies.ctrl q phase readSymbol pendingWrite pendingState =
        FourPhaseSpecies.ctrlOf c.state
  · rw [if_pos h, h]
    exact enc_ctrlOf c
  · rw [if_neg h]
    cases c with
    | mk st m =>
        cases st with
        | mk q0 phase0 read0 write0 state0 =>
        have hctrlne :
            FourPhaseSpecies.ctrl q phase readSymbol pendingWrite pendingState ≠
              FourPhaseSpecies.ctrl q0 phase0 read0 write0 state0 := by
          simpa [FourPhaseSpecies.ctrlOf] using h
        simp [enc, control, tape, tapeBar, State.add,
          FourPhaseSpecies.ctrlOf, State.single, hctrlne]

omit [DecidableEq Q] in
@[simp]
theorem ctrlOf_ne_readProbe
    (st : MicroState Q) (r : Bool) :
    FourPhaseSpecies.ctrlOf st ≠ readProbe (Q := Q) r := by
  cases r <;> simp [readProbe]

@[simp]
theorem enc_readProbe
    {s : Nat}
    (c : MicroCfg Q s) (r : Bool) :
    enc c (readProbe r) =
      if r then c.tape else maxTape s - c.tape := by
  cases r <;> simp [readProbe]

/--
Aggregate input complex for a full ideal encoded four-phase configuration.

This is a specification-level complex over aggregate species; it is not an
elementary or bimolecular implementation.
-/
def fullAggregateInput {s : Nat} (c : MicroCfg Q s) :
    Complex (Species Q) :=
  enc c

/-- Aggregate output complex for a full ideal encoded four-phase configuration. -/
def fullAggregateOutput {s : Nat} (c : MicroCfg Q s) :
    Complex (Species Q) :=
  enc c

/--
Single aggregate reaction realizing the full encoded-state rewrite `c` to `c'`.

This deterministic bridge is intentionally aggregate-level and is not claimed
to be bimolecular or stochastic.
-/
def fullAggregateReaction {s : Nat} (c c' : MicroCfg Q s) :
    Reaction (Species Q) where
  l := fullAggregateInput c
  r := fullAggregateOutput c'
  k := 1

@[simp]
theorem fullAggregateInput_apply {s : Nat}
    (c : MicroCfg Q s) (species : Species Q) :
    fullAggregateInput c species = enc c species := by
  rfl

@[simp]
theorem fullAggregateOutput_apply {s : Nat}
    (c : MicroCfg Q s) (species : Species Q) :
    fullAggregateOutput c species = enc c species := by
  rfl

@[simp]
theorem fullAggregateReaction_l {s : Nat}
    (c c' : MicroCfg Q s) :
    (fullAggregateReaction c c').l = fullAggregateInput c := by
  rfl

@[simp]
theorem fullAggregateReaction_r {s : Nat}
    (c c' : MicroCfg Q s) :
    (fullAggregateReaction c c').r = fullAggregateOutput c' := by
  rfl

@[simp]
theorem fullAggregateReaction_k {s : Nat}
    (c c' : MicroCfg Q s) :
    (fullAggregateReaction c c').k = 1 := by
  rfl

theorem fullAggregateReaction_enabled {s : Nat}
    (c c' : MicroCfg Q s) :
    (fullAggregateReaction c c').enabled (enc c) := by
  intro species
  rfl

theorem fullAggregateReaction_fire {s : Nat}
    (c c' : MicroCfg Q s) :
    (fullAggregateReaction c c').fire (enc c) = enc c' := by
  funext species
  simp [Reaction.fire, fullAggregateReaction, fullAggregateInput,
    fullAggregateOutput]

theorem fullAggregateReaction_firesTo {s : Nat}
    (c c' : MicroCfg Q s) :
    (fullAggregateReaction c c').FiresTo (enc c) (enc c') := by
  exact ⟨fullAggregateReaction_enabled c c',
    (fullAggregateReaction_fire c c').symm⟩

theorem fullAggregateReaction_firesTo_iff {s : Nat}
    (c c' : MicroCfg Q s) (z' : State (Species Q)) :
    (fullAggregateReaction c c').FiresTo (enc c) z' ↔
      z' = enc c' := by
  constructor
  · intro h
    exact Reaction.FiresTo.unique h (fullAggregateReaction_firesTo c c')
  · intro hz
    rw [hz]
    exact fullAggregateReaction_firesTo c c'

def fullAggregateNetwork {s : Nat} (c c' : MicroCfg Q s) :
    Network (Species Q) :=
  Network.oneRxnNetwork (fullAggregateReaction c c')

@[simp]
theorem fullAggregateNetwork_rxn_step {s : Nat}
    (c c' : MicroCfg Q s) :
    (fullAggregateNetwork c c').rxn Network.OneRxnIdx.step =
      fullAggregateReaction c c' := by
  rfl

theorem fullAggregateNetwork_allUnitRate {s : Nat}
    (c c' : MicroCfg Q s) :
    (fullAggregateNetwork c c').allUnitRate :=
  (Network.oneRxnNetwork_allUnitRate_iff
    (fullAggregateReaction c c')).2 rfl

theorem fullAggregateNetwork_hasPositiveRates {s : Nat}
    (c c' : MicroCfg Q s) :
    (fullAggregateNetwork c c').hasPositiveRates :=
  Network.hasPositiveRates_of_allUnitRate
    (fullAggregateNetwork_allUnitRate c c')

theorem fullAggregateNetwork_equalRates {s : Nat}
    (c c' : MicroCfg Q s) :
    (fullAggregateNetwork c c').equalRates :=
  Network.oneRxnNetwork_equalRates (fullAggregateReaction c c')

theorem fullAggregateNetwork_exec {s : Nat}
    (c c' : MicroCfg Q s) :
    (fullAggregateNetwork c c').Exec
      (enc c) (enc c') [Network.OneRxnIdx.step] :=
  Network.oneRxn_exec (fullAggregateReaction_firesTo c c')

theorem fullAggregateNetwork_exec_iff {s : Nat}
    (c c' : MicroCfg Q s) (z' : State (Species Q)) :
    (fullAggregateNetwork c c').Exec
      (enc c) z' [Network.OneRxnIdx.step] <->
        z' = enc c' := by
  constructor
  · intro hExec
    have hFire :
        (fullAggregateReaction c c').FiresTo (enc c) z' := by
      exact
        (Network.oneRxnNetwork_exec_iff
          (rho := fullAggregateReaction c c')
          (z := enc c) (z' := z')).1
          (by simpa [fullAggregateNetwork] using hExec)
    exact (fullAggregateReaction_firesTo_iff c c' z').1 hFire
  · intro hz
    rw [hz]
    exact fullAggregateNetwork_exec c c'

theorem fullAggregateNetwork_reaches {s : Nat}
    (c c' : MicroCfg Q s) :
    (fullAggregateNetwork c c').Reaches (enc c) (enc c') :=
  Network.reaches_of_exec (fullAggregateNetwork_exec c c')

def fullAggregateNetwork_intendedSchedule {s : Nat}
    (c c' : MicroCfg Q s) :
    (fullAggregateNetwork c c').IntendedSchedule (enc c) (enc c') :=
  Network.oneRxnNetwork_intendedSchedule
    (fullAggregateReaction_firesTo c c')

@[simp]
theorem fullAggregateNetwork_intendedSchedule_schedule {s : Nat}
    (c c' : MicroCfg Q s) :
    (fullAggregateNetwork_intendedSchedule c c').schedule =
      [Network.OneRxnIdx.step] := by
  rfl

@[simp]
theorem fullAggregateNetwork_intendedSchedule_firingCount {s : Nat}
    (c c' : MicroCfg Q s) :
    (fullAggregateNetwork_intendedSchedule c c').firingCount = 1 := by
  rfl

def fullAggregateNetwork_boundedIntendedSchedule {s : Nat}
    (c c' : MicroCfg Q s) :
    (fullAggregateNetwork c c').BoundedIntendedSchedule 1
      (enc c) (enc c') :=
  Network.oneRxnNetwork_boundedIntendedSchedule
    (fullAggregateReaction_firesTo c c')

@[simp]
theorem fullAggregateNetwork_boundedIntendedSchedule_schedule {s : Nat}
    (c c' : MicroCfg Q s) :
    (fullAggregateNetwork_boundedIntendedSchedule c c').schedule =
      [Network.OneRxnIdx.step] := by
  rfl

@[simp]
theorem fullAggregateNetwork_boundedIntendedSchedule_firingCount {s : Nat}
    (c c' : MicroCfg Q s) :
    (fullAggregateNetwork_boundedIntendedSchedule c c').firingCount = 1 := by
  rfl

@[simp]
theorem fullAggregateNetwork_boundedIntendedSchedule_toIntendedSchedule
    {s : Nat} (c c' : MicroCfg Q s) :
    (fullAggregateNetwork_boundedIntendedSchedule c c').toIntendedSchedule =
      fullAggregateNetwork_intendedSchedule c c' := by
  rfl

theorem fullAggregateNetwork_intended_reaches {s : Nat}
    (c c' : MicroCfg Q s) :
    (fullAggregateNetwork c c').Reaches (enc c) (enc c') :=
  (fullAggregateNetwork_intendedSchedule c c').reaches

theorem fullAggregateNetwork_boundedIntendedSchedule_reaches {s : Nat}
    (c c' : MicroCfg Q s) :
    (fullAggregateNetwork c c').Reaches (enc c) (enc c') :=
  (fullAggregateNetwork_boundedIntendedSchedule c c').reaches

theorem fullAggregateNetwork_coverable_of_covers {s : Nat}
    (c c' : MicroCfg Q s) {target : State (Species Q)}
    (hCovers : Covers (enc c') target) :
    (fullAggregateNetwork c c').CoverableFrom (enc c) target :=
  Network.coverable_of_reaches_of_covers
    (fullAggregateNetwork_reaches c c')
    hCovers

theorem fullAggregateNetwork_coverable_of_le {s : Nat}
    (c c' : MicroCfg Q s) {target : State (Species Q)}
    (hTarget : forall species, target species <= enc c' species) :
    (fullAggregateNetwork c c').CoverableFrom (enc c) target :=
  fullAggregateNetwork_coverable_of_covers c c' hTarget

theorem fullAggregateNetwork_coverableFrom_of_covers {s : Nat}
    (c c' : MicroCfg Q s) {target : State (Species Q)}
    (hCovers : Covers (enc c') target) :
    (fullAggregateNetwork c c').CoverableFrom (enc c) target :=
  fullAggregateNetwork_coverable_of_covers c c' hCovers

theorem fullAggregateNetwork_coverableFrom_of_le {s : Nat}
    (c c' : MicroCfg Q s) {target : State (Species Q)}
    (hTarget : forall species, target species <= enc c' species) :
    (fullAggregateNetwork c c').CoverableFrom (enc c) target :=
  fullAggregateNetwork_coverable_of_le c c' hTarget

theorem fullAggregateNetwork_speciesCoverableFrom_coord {s : Nat}
    (c c' : MicroCfg Q s)
    {species : Species Q} {amount : Nat}
    (hamount : amount <= enc c' species) :
    (fullAggregateNetwork c c').SpeciesCoverableFrom
      (enc c) species amount :=
  Network.speciesCoverableFrom_of_reaches_coord
    (fullAggregateNetwork_reaches c c')
    hamount

theorem fullAggregateNetwork_speciesCoverableFrom_one_of_pos {s : Nat}
    (c c' : MicroCfg Q s)
    {species : Species Q}
    (hpos : 0 < enc c' species) :
    (fullAggregateNetwork c c').SpeciesCoverableFrom (enc c) species :=
  Network.speciesCoverableFrom_one_of_reaches_pos
    (fullAggregateNetwork_reaches c c')
    hpos

theorem enc_covers_ctrl_add_tape {s : Nat}
    (c : MicroCfg Q s) {k : Nat}
    (hk : k <= c.tape) :
    Covers (enc c)
      (State.add
        (State.single (FourPhaseSpecies.ctrlOf c.state) 1)
        (State.single FourPhaseSpecies.tape k)) := by
  intro species
  cases species with
  | ctrl q phase readSymbol pendingWrite pendingState =>
      simp [enc, control, tape, tapeBar, State.add,
        FourPhaseSpecies.ctrlOf]
  | tape =>
      simpa [enc, control, tape, tapeBar, State.add,
        FourPhaseSpecies.ctrlOf] using hk
  | tapeBar =>
      simp [enc, control, tape, tapeBar, State.add,
        FourPhaseSpecies.ctrlOf]

theorem enc_covers_ctrl_add_tapeBar {s : Nat}
    (c : MicroCfg Q s) {k : Nat}
    (hk : k <= maxTape s - c.tape) :
    Covers (enc c)
      (State.add
        (State.single (FourPhaseSpecies.ctrlOf c.state) 1)
        (State.single FourPhaseSpecies.tapeBar k)) := by
  intro species
  cases species with
  | ctrl q phase readSymbol pendingWrite pendingState =>
      simp [enc, control, tape, tapeBar, State.add,
        FourPhaseSpecies.ctrlOf]
  | tape =>
      simp [enc, control, tape, tapeBar, State.add,
        FourPhaseSpecies.ctrlOf]
  | tapeBar =>
      simpa [enc, control, tape, tapeBar, State.add,
        FourPhaseSpecies.ctrlOf] using hk

theorem enc_covers_ctrl_add_readProbe {s : Nat}
    (c : MicroCfg Q s) {r : Bool} {k : Nat}
    (hk : k <= enc c (readProbe r)) :
    Covers (enc c)
      (State.add
        (State.single (FourPhaseSpecies.ctrlOf c.state) 1)
        (State.single (readProbe r) k)) := by
  intro species
  cases species with
  | ctrl q phase readSymbol pendingWrite pendingState =>
      cases r <;>
        simp [enc, control, tape, tapeBar, State.add,
          FourPhaseSpecies.ctrlOf, readProbe]
  | tape =>
      cases r
      · simp [enc, control, tape, tapeBar, State.add,
          FourPhaseSpecies.ctrlOf, readProbe]
      · have htape :
            FourPhaseSpecies.tape ≠ FourPhaseSpecies.ctrlOf c.state :=
          (FourPhaseSpecies.ctrlOf_ne_tape c.state).symm
        simpa [enc, control, tape, tapeBar, State.add,
          FourPhaseSpecies.ctrlOf, readProbe, State.single, htape] using hk
  | tapeBar =>
      cases r
      · have htapeBar :
            FourPhaseSpecies.tapeBar ≠ FourPhaseSpecies.ctrlOf c.state :=
          (FourPhaseSpecies.ctrlOf_ne_tapeBar c.state).symm
        simpa [enc, control, tape, tapeBar, State.add,
          FourPhaseSpecies.ctrlOf, readProbe, State.single, htapeBar] using hk
      · simp [enc, control, tape, tapeBar, State.add,
          FourPhaseSpecies.ctrlOf, readProbe]

theorem enc_covers_ctrl_add_tape_add_tapeBar {s : Nat}
    (c : MicroCfg Q s) {kt kb : Nat}
    (ht : kt <= c.tape)
    (hb : kb <= maxTape s - c.tape) :
    Covers (enc c)
      (State.add
        (State.add
          (State.single (FourPhaseSpecies.ctrlOf c.state) 1)
          (State.single FourPhaseSpecies.tape kt))
        (State.single FourPhaseSpecies.tapeBar kb)) := by
  intro species
  cases species with
  | ctrl q phase readSymbol pendingWrite pendingState =>
      simp [enc, control, tape, tapeBar, State.add,
        FourPhaseSpecies.ctrlOf]
  | tape =>
      simpa [enc, control, tape, tapeBar, State.add,
        FourPhaseSpecies.ctrlOf] using ht
  | tapeBar =>
      simpa [enc, control, tape, tapeBar, State.add,
        FourPhaseSpecies.ctrlOf] using hb

def aggregateInput
    (st : MicroState Q)
    (tapeIn tapeBarIn : Nat) :
    Complex (Species Q) :=
  State.add
    (State.add
      (State.single (FourPhaseSpecies.ctrlOf st) 1)
      (State.single FourPhaseSpecies.tape tapeIn))
    (State.single FourPhaseSpecies.tapeBar tapeBarIn)

def aggregateOutput
    (st' : MicroState Q)
    (tapeOut tapeBarOut : Nat) :
    Complex (Species Q) :=
  State.add
    (State.add
      (State.single (FourPhaseSpecies.ctrlOf st') 1)
      (State.single FourPhaseSpecies.tape tapeOut))
    (State.single FourPhaseSpecies.tapeBar tapeBarOut)

@[simp]
theorem aggregateInput_ctrlOf
    (st : MicroState Q) (tapeIn tapeBarIn : Nat) :
    aggregateInput st tapeIn tapeBarIn (FourPhaseSpecies.ctrlOf st) = 1 := by
  simp [aggregateInput, State.add]

@[simp]
theorem aggregateInput_tape
    (st : MicroState Q) (tapeIn tapeBarIn : Nat) :
    aggregateInput st tapeIn tapeBarIn FourPhaseSpecies.tape = tapeIn := by
  have hctrl :
      FourPhaseSpecies.tape ≠ FourPhaseSpecies.ctrlOf st :=
    (FourPhaseSpecies.ctrlOf_ne_tape st).symm
  simp [aggregateInput, State.add, State.single, hctrl]

@[simp]
theorem aggregateInput_tapeBar
    (st : MicroState Q) (tapeIn tapeBarIn : Nat) :
    aggregateInput st tapeIn tapeBarIn FourPhaseSpecies.tapeBar = tapeBarIn := by
  have hctrl :
      FourPhaseSpecies.tapeBar ≠ FourPhaseSpecies.ctrlOf st :=
    (FourPhaseSpecies.ctrlOf_ne_tapeBar st).symm
  simp [aggregateInput, State.add, State.single, hctrl]

@[simp]
theorem aggregateInput_size [Fintype Q]
    (st : MicroState Q) (tapeIn tapeBarIn : Nat) :
    Complex.size (aggregateInput st tapeIn tapeBarIn) =
      1 + tapeIn + tapeBarIn := by
  simp [aggregateInput, Nat.add_assoc]

@[simp]
theorem aggregateOutput_ctrlOf
    (st' : MicroState Q) (tapeOut tapeBarOut : Nat) :
    aggregateOutput st' tapeOut tapeBarOut (FourPhaseSpecies.ctrlOf st') = 1 := by
  simp [aggregateOutput, State.add]

@[simp]
theorem aggregateOutput_tape
    (st' : MicroState Q) (tapeOut tapeBarOut : Nat) :
    aggregateOutput st' tapeOut tapeBarOut FourPhaseSpecies.tape = tapeOut := by
  have hctrl :
      FourPhaseSpecies.tape ≠ FourPhaseSpecies.ctrlOf st' :=
    (FourPhaseSpecies.ctrlOf_ne_tape st').symm
  simp [aggregateOutput, State.add, State.single, hctrl]

@[simp]
theorem aggregateOutput_tapeBar
    (st' : MicroState Q) (tapeOut tapeBarOut : Nat) :
    aggregateOutput st' tapeOut tapeBarOut FourPhaseSpecies.tapeBar =
      tapeBarOut := by
  have hctrl :
      FourPhaseSpecies.tapeBar ≠ FourPhaseSpecies.ctrlOf st' :=
    (FourPhaseSpecies.ctrlOf_ne_tapeBar st').symm
  simp [aggregateOutput, State.add, State.single, hctrl]

@[simp]
theorem aggregateOutput_size [Fintype Q]
    (st' : MicroState Q) (tapeOut tapeBarOut : Nat) :
    Complex.size (aggregateOutput st' tapeOut tapeBarOut) =
      1 + tapeOut + tapeBarOut := by
  simp [aggregateOutput, Nat.add_assoc]

theorem fullAggregateInput_eq_aggregateInput {s : Nat}
    (c : MicroCfg Q s) :
    fullAggregateInput c =
      aggregateInput c.state c.tape (maxTape s - c.tape) := by
  rfl

theorem fullAggregateOutput_eq_aggregateOutput {s : Nat}
    (c : MicroCfg Q s) :
    fullAggregateOutput c =
      aggregateOutput c.state c.tape (maxTape s - c.tape) := by
  rfl

theorem enc_covers_aggregateInput {s : Nat}
    (c : MicroCfg Q s) {tapeIn tapeBarIn : Nat}
    (hTape : tapeIn <= c.tape)
    (hTapeBar : tapeBarIn <= maxTape s - c.tape) :
    Covers (enc c)
      (aggregateInput c.state tapeIn tapeBarIn) := by
  simpa [aggregateInput] using
    enc_covers_ctrl_add_tape_add_tapeBar c hTape hTapeBar

theorem enc_covers_aggregateInput_readProbe {s : Nat}
    (c : MicroCfg Q s) (r : Bool) {k : Nat}
    (hk : k <= enc c (readProbe r)) :
    Covers (enc c)
      (aggregateInput c.state
        (if r then k else 0)
        (if r then 0 else k)) := by
  cases r
  · simpa [enc_readProbe] using
      enc_covers_aggregateInput c (Nat.zero_le _)
        (by simpa [enc_readProbe] using hk)
  · simpa [enc_readProbe] using
      enc_covers_aggregateInput c
        (by simpa [enc_readProbe] using hk)
        (Nat.zero_le _)

theorem enc_covers_aggregateOutput {s : Nat}
    (c : MicroCfg Q s) {tapeOut tapeBarOut : Nat}
    (hTape : tapeOut <= c.tape)
    (hTapeBar : tapeBarOut <= maxTape s - c.tape) :
    Covers (enc c)
      (aggregateOutput c.state tapeOut tapeBarOut) := by
  simpa [aggregateOutput] using
    enc_covers_ctrl_add_tape_add_tapeBar c hTape hTapeBar

def aggregateReaction
    (st st' : MicroState Q)
    (tapeIn tapeBarIn tapeOut tapeBarOut : Nat) :
    Reaction (Species Q) where
  l := aggregateInput st tapeIn tapeBarIn
  r := aggregateOutput st' tapeOut tapeBarOut
  k := 1

theorem fullAggregateReaction_eq_aggregateReaction {s : Nat}
    (c c' : MicroCfg Q s) :
    fullAggregateReaction c c' =
      aggregateReaction c.state c'.state
        c.tape (maxTape s - c.tape)
        c'.tape (maxTape s - c'.tape) := by
  rfl

@[simp]
theorem aggregateReaction_l
    (st st' : MicroState Q)
    (tapeIn tapeBarIn tapeOut tapeBarOut : Nat) :
    (aggregateReaction st st' tapeIn tapeBarIn tapeOut tapeBarOut).l =
      aggregateInput st tapeIn tapeBarIn := by
  rfl

@[simp]
theorem aggregateReaction_r
    (st st' : MicroState Q)
    (tapeIn tapeBarIn tapeOut tapeBarOut : Nat) :
    (aggregateReaction st st' tapeIn tapeBarIn tapeOut tapeBarOut).r =
      aggregateOutput st' tapeOut tapeBarOut := by
  rfl

@[simp]
theorem aggregateReaction_k
    (st st' : MicroState Q)
    (tapeIn tapeBarIn tapeOut tapeBarOut : Nat) :
    (aggregateReaction st st' tapeIn tapeBarIn tapeOut tapeBarOut).k = 1 := by
  rfl

@[simp]
theorem aggregateReaction_inputArity [Fintype Q]
    (st st' : MicroState Q)
    (tapeIn tapeBarIn tapeOut tapeBarOut : Nat) :
    (aggregateReaction st st' tapeIn tapeBarIn tapeOut tapeBarOut).inputArity =
      1 + tapeIn + tapeBarIn := by
  simp [Reaction.inputArity, aggregateReaction]

@[simp]
theorem aggregateReaction_outputArity [Fintype Q]
    (st st' : MicroState Q)
    (tapeIn tapeBarIn tapeOut tapeBarOut : Nat) :
    (aggregateReaction st st' tapeIn tapeBarIn tapeOut tapeBarOut).outputArity =
      1 + tapeOut + tapeBarOut := by
  simp [Reaction.outputArity, aggregateReaction]

theorem aggregateReaction_not_atMostBimolecularInput_of_two_lt
    [Fintype Q]
    (st st' : MicroState Q)
    (tapeIn tapeBarIn tapeOut tapeBarOut : Nat)
    (hLarge : 2 < 1 + tapeIn + tapeBarIn) :
    Not
      (Reaction.isAtMostBimolecularInput
        (aggregateReaction st st' tapeIn tapeBarIn tapeOut tapeBarOut)) := by
  intro h
  unfold Reaction.isAtMostBimolecularInput at h
  rw [aggregateReaction_inputArity] at h
  exact not_lt_of_ge h hLarge

theorem aggregateReaction_isAtMostBimolecularInput_of_sum_le_one
    [Fintype Q]
    (st st' : MicroState Q)
    (tapeIn tapeBarIn tapeOut tapeBarOut : Nat)
    (h : tapeIn + tapeBarIn <= 1) :
    (aggregateReaction st st'
      tapeIn tapeBarIn tapeOut tapeBarOut).isAtMostBimolecularInput := by
  unfold Reaction.isAtMostBimolecularInput
  rw [aggregateReaction_inputArity]
  omega

theorem aggregateReaction_isAtMostBimolecularOutput_of_sum_le_one
    [Fintype Q]
    (st st' : MicroState Q)
    (tapeIn tapeBarIn tapeOut tapeBarOut : Nat)
    (h : tapeOut + tapeBarOut <= 1) :
    (aggregateReaction st st'
      tapeIn tapeBarIn tapeOut tapeBarOut).isAtMostBimolecularOutput := by
  unfold Reaction.isAtMostBimolecularOutput
  rw [aggregateReaction_outputArity]
  omega

theorem aggregateReaction_isAtMostBimolecularFull_of_sums_le_one
    [Fintype Q]
    (st st' : MicroState Q)
    (tapeIn tapeBarIn tapeOut tapeBarOut : Nat)
    (hin : tapeIn + tapeBarIn <= 1)
    (hout : tapeOut + tapeBarOut <= 1) :
    (aggregateReaction st st'
      tapeIn tapeBarIn tapeOut tapeBarOut).isAtMostBimolecularFull :=
  ⟨
    aggregateReaction_isAtMostBimolecularInput_of_sum_le_one
      st st' tapeIn tapeBarIn tapeOut tapeBarOut hin,
    aggregateReaction_isAtMostBimolecularOutput_of_sum_le_one
      st st' tapeIn tapeBarIn tapeOut tapeBarOut hout
  ⟩

theorem aggregateReaction_enabled
    {s : Nat}
    (st st' : MicroState Q)
    (m tapeIn tapeBarIn tapeOut tapeBarOut : Nat)
    (hTape : tapeIn <= m)
    (hTapeBar : tapeBarIn <= maxTape s - m) :
    (aggregateReaction st st' tapeIn tapeBarIn tapeOut tapeBarOut).enabled
      (enc ({ state := st, tape := m } : MicroCfg Q s)) := by
  intro species
  cases species with
  | ctrl q phase readSymbol pendingWrite pendingState =>
      simp [aggregateReaction, aggregateInput, enc, control, tape, tapeBar,
        State.add, FourPhaseSpecies.ctrlOf]
  | tape =>
      simpa [aggregateReaction, aggregateInput, enc, control, tape, tapeBar,
        State.add, FourPhaseSpecies.ctrlOf] using hTape
  | tapeBar =>
      simpa [aggregateReaction, aggregateInput, enc, control, tape, tapeBar,
        State.add, FourPhaseSpecies.ctrlOf] using hTapeBar

theorem aggregateReaction_enabled_iff
    {s : Nat}
    (st st' : MicroState Q)
    (m tapeIn tapeBarIn tapeOut tapeBarOut : Nat) :
    (aggregateReaction st st' tapeIn tapeBarIn tapeOut tapeBarOut).enabled
      (enc ({ state := st, tape := m } : MicroCfg Q s)) ↔
      tapeIn <= m /\ tapeBarIn <= maxTape s - m := by
  constructor
  · intro hEnabled
    constructor
    · simpa [aggregateReaction, aggregateInput, enc, control, tape, tapeBar,
        State.add, FourPhaseSpecies.ctrlOf]
        using hEnabled FourPhaseSpecies.tape
    · simpa [aggregateReaction, aggregateInput, enc, control, tape, tapeBar,
        State.add, FourPhaseSpecies.ctrlOf]
        using hEnabled FourPhaseSpecies.tapeBar
  · rintro ⟨hTape, hTapeBar⟩
    exact aggregateReaction_enabled
      (s := s) st st' m tapeIn tapeBarIn tapeOut tapeBarOut hTape hTapeBar

theorem aggregateReaction_not_enabled_iff
    {s : Nat}
    (st st' : MicroState Q)
    (m tapeIn tapeBarIn tapeOut tapeBarOut : Nat) :
    Not
      ((aggregateReaction st st' tapeIn tapeBarIn tapeOut tapeBarOut).enabled
        (enc ({ state := st, tape := m } : MicroCfg Q s))) <->
      m < tapeIn \/ maxTape s - m < tapeBarIn := by
  rw [aggregateReaction_enabled_iff
    (s := s) st st' m tapeIn tapeBarIn tapeOut tapeBarOut]
  constructor
  · intro hnot
    by_cases hTape : tapeIn <= m
    · right
      exact lt_of_not_ge (by
        intro hTapeBar
        exact hnot ⟨hTape, hTapeBar⟩)
    · left
      exact lt_of_not_ge hTape
  · rintro (hTape | hTapeBar) hEnabled
    · exact (not_le_of_gt hTape) hEnabled.1
    · exact (not_le_of_gt hTapeBar) hEnabled.2

theorem aggregateReaction_fire
    {s : Nat}
    (st st' : MicroState Q)
    (m m' tapeIn tapeBarIn tapeOut tapeBarOut : Nat)
    (hTapeEq : m - tapeIn + tapeOut = m')
    (hTapeBarEq :
      (maxTape s - m) - tapeBarIn + tapeBarOut = maxTape s - m') :
    (aggregateReaction st st' tapeIn tapeBarIn tapeOut tapeBarOut).fire
      (enc ({ state := st, tape := m } : MicroCfg Q s)) =
      enc ({ state := st', tape := m' } : MicroCfg Q s) := by
  funext species
  cases species with
  | ctrl q phase readSymbol pendingWrite pendingState =>
      simp [Reaction.fire, aggregateReaction, aggregateInput, aggregateOutput,
        enc, control, tape, tapeBar, State.add, FourPhaseSpecies.ctrlOf]
  | tape =>
      simpa [Reaction.fire, aggregateReaction, aggregateInput, aggregateOutput,
        enc, control, tape, tapeBar, State.add, FourPhaseSpecies.ctrlOf]
        using hTapeEq
  | tapeBar =>
      simpa [Reaction.fire, aggregateReaction, aggregateInput, aggregateOutput,
        enc, control, tape, tapeBar, State.add, FourPhaseSpecies.ctrlOf]
        using hTapeBarEq

theorem aggregateReaction_firesTo
    {s : Nat}
    (st st' : MicroState Q)
    (m m' tapeIn tapeBarIn tapeOut tapeBarOut : Nat)
    (hTape : tapeIn <= m)
    (hTapeBar : tapeBarIn <= maxTape s - m)
    (hTapeEq : m - tapeIn + tapeOut = m')
    (hTapeBarEq :
      (maxTape s - m) - tapeBarIn + tapeBarOut = maxTape s - m') :
    (aggregateReaction st st' tapeIn tapeBarIn tapeOut tapeBarOut).FiresTo
      (enc ({ state := st, tape := m } : MicroCfg Q s))
      (enc ({ state := st', tape := m' } : MicroCfg Q s)) := by
  refine ⟨
    (aggregateReaction_enabled_iff
      (s := s) st st' m
      tapeIn tapeBarIn tapeOut tapeBarOut).2 ⟨hTape, hTapeBar⟩,
    (aggregateReaction_fire
      (s := s) st st' m m'
      tapeIn tapeBarIn tapeOut tapeBarOut
      hTapeEq hTapeBarEq).symm⟩

theorem aggregateReaction_firesTo_iff
    {s : Nat}
    (st st' : MicroState Q)
    (m m' tapeIn tapeBarIn tapeOut tapeBarOut : Nat)
    (hTape : tapeIn <= m)
    (hTapeBar : tapeBarIn <= maxTape s - m)
    (hTapeEq : m - tapeIn + tapeOut = m')
    (hTapeBarEq :
      (maxTape s - m) - tapeBarIn + tapeBarOut = maxTape s - m')
    (z' : State (Species Q)) :
    (aggregateReaction st st' tapeIn tapeBarIn tapeOut tapeBarOut).FiresTo
      (enc ({ state := st, tape := m } : MicroCfg Q s)) z' <->
      z' = enc ({ state := st', tape := m' } : MicroCfg Q s) := by
  constructor
  · intro h
    exact Reaction.FiresTo.unique h
      (aggregateReaction_firesTo
        (s := s) st st' m m'
        tapeIn tapeBarIn tapeOut tapeBarOut
        hTape hTapeBar hTapeEq hTapeBarEq)
  · intro hz
    rw [hz]
    exact aggregateReaction_firesTo
      (s := s) st st' m m'
      tapeIn tapeBarIn tapeOut tapeBarOut
      hTape hTapeBar hTapeEq hTapeBarEq

def preserveTapeReaction
    (st st' : MicroState Q) (k : Nat) :
    Reaction (Species Q) :=
  aggregateReaction st st' k 0 k 0

theorem preserveTapeReaction_isAtMostBimolecularFull_of_le_one
    [Fintype Q]
    (st st' : MicroState Q) {k : Nat} (hk : k <= 1) :
    (preserveTapeReaction st st' k).isAtMostBimolecularFull := by
  exact aggregateReaction_isAtMostBimolecularFull_of_sums_le_one
    st st' k 0 k 0 (by omega) (by omega)

def preserveTapeBarReaction
    (st st' : MicroState Q) (k : Nat) :
    Reaction (Species Q) :=
  aggregateReaction st st' 0 k 0 k

theorem preserveTapeBarReaction_isAtMostBimolecularFull_of_le_one
    [Fintype Q]
    (st st' : MicroState Q) {k : Nat} (hk : k <= 1) :
    (preserveTapeBarReaction st st' k).isAtMostBimolecularFull := by
  exact aggregateReaction_isAtMostBimolecularFull_of_sums_le_one
    st st' 0 k 0 k (by omega) (by omega)

theorem preserve_tape_eq
    {m k : Nat} (hk : k <= m) :
    m - k + k = m :=
  Nat.sub_add_cancel hk

theorem preserve_tapeBar_eq
    {s m k : Nat} (hk : k <= maxTape s - m) :
    maxTape s - m - k + k = maxTape s - m :=
  Nat.sub_add_cancel hk

theorem tape_to_tapeBar_bar_eq
    {s m k : Nat}
    (hm : m <= maxTape s)
    (hk : k <= m) :
    maxTape s - m + k = maxTape s - (m - k) := by
  omega

theorem tapeBar_to_tape_bar_eq
    {s m k : Nat} :
    maxTape s - m - k = maxTape s - (m + k) := by
  omega

theorem preserveTapeReaction_firesTo
    {s : Nat}
    (st st' : MicroState Q) (m k : Nat)
    (hk : k <= m) :
    (preserveTapeReaction st st' k).FiresTo
      (enc ({ state := st, tape := m } : MicroCfg Q s))
      (enc ({ state := st', tape := m } : MicroCfg Q s)) := by
  exact aggregateReaction_firesTo
    (s := s) st st' m m k 0 k 0
    hk (Nat.zero_le _) (preserve_tape_eq hk) (by simp)

theorem preserveTapeReaction_firesTo_iff
    {s : Nat}
    (st st' : MicroState Q) (m k : Nat)
    (hk : k <= m)
    (z' : State (Species Q)) :
    (preserveTapeReaction st st' k).FiresTo
      (enc ({ state := st, tape := m } : MicroCfg Q s)) z' <->
      z' = enc ({ state := st', tape := m } : MicroCfg Q s) := by
  constructor
  · intro h
    exact Reaction.FiresTo.unique h
      (preserveTapeReaction_firesTo (s := s) st st' m k hk)
  · intro hz
    rw [hz]
    exact preserveTapeReaction_firesTo (s := s) st st' m k hk

theorem preserveTapeBarReaction_firesTo
    {s : Nat}
    (st st' : MicroState Q) (m k : Nat)
    (hk : k <= maxTape s - m) :
    (preserveTapeBarReaction st st' k).FiresTo
      (enc ({ state := st, tape := m } : MicroCfg Q s))
      (enc ({ state := st', tape := m } : MicroCfg Q s)) := by
  exact aggregateReaction_firesTo
    (s := s) st st' m m 0 k 0 k
    (Nat.zero_le _) hk (by simp) (preserve_tapeBar_eq hk)

theorem preserveTapeBarReaction_firesTo_iff
    {s : Nat}
    (st st' : MicroState Q) (m k : Nat)
    (hk : k <= maxTape s - m)
    (z' : State (Species Q)) :
    (preserveTapeBarReaction st st' k).FiresTo
      (enc ({ state := st, tape := m } : MicroCfg Q s)) z' <->
      z' = enc ({ state := st', tape := m } : MicroCfg Q s) := by
  constructor
  · intro h
    exact Reaction.FiresTo.unique h
      (preserveTapeBarReaction_firesTo (s := s) st st' m k hk)
  · intro hz
    rw [hz]
    exact preserveTapeBarReaction_firesTo (s := s) st st' m k hk

def transferTapeToTapeBarReaction
    (st st' : MicroState Q) (k : Nat) :
    Reaction (Species Q) :=
  aggregateReaction st st' k 0 0 k

theorem transferTapeToTapeBarReaction_isAtMostBimolecularFull_of_le_one
    [Fintype Q]
    (st st' : MicroState Q) {k : Nat} (hk : k <= 1) :
    (transferTapeToTapeBarReaction st st' k).isAtMostBimolecularFull := by
  exact aggregateReaction_isAtMostBimolecularFull_of_sums_le_one
    st st' k 0 0 k (by omega) (by omega)

@[simp]
theorem transferTapeToTapeBarReaction_one_inputArity
    [Fintype Q]
    (st st' : MicroState Q) :
    (transferTapeToTapeBarReaction st st' 1).inputArity = 2 := by
  simp [transferTapeToTapeBarReaction]

@[simp]
theorem transferTapeToTapeBarReaction_one_outputArity
    [Fintype Q]
    (st st' : MicroState Q) :
    (transferTapeToTapeBarReaction st st' 1).outputArity = 2 := by
  simp [transferTapeToTapeBarReaction]

theorem transferTapeToTapeBarReaction_one_isAtMostBimolecularFull
    [Fintype Q]
    (st st' : MicroState Q) :
    (transferTapeToTapeBarReaction st st' 1).isAtMostBimolecularFull :=
  transferTapeToTapeBarReaction_isAtMostBimolecularFull_of_le_one
    st st' le_rfl

theorem transferTapeToTapeBarReaction_firesTo
    {s : Nat}
    (st st' : MicroState Q) (m k : Nat)
    (hm : m <= maxTape s)
    (hk : k <= m) :
    (transferTapeToTapeBarReaction st st' k).FiresTo
      (enc ({ state := st, tape := m } : MicroCfg Q s))
      (enc ({ state := st', tape := m - k } : MicroCfg Q s)) := by
  exact aggregateReaction_firesTo
    (s := s) st st' m (m - k) k 0 0 k
    hk (Nat.zero_le _) (by simp) (tape_to_tapeBar_bar_eq hm hk)

theorem transferTapeToTapeBarReaction_firesTo_iff
    {s : Nat}
    (st st' : MicroState Q) (m k : Nat)
    (hm : m <= maxTape s)
    (hk : k <= m)
    (z' : State (Species Q)) :
    (transferTapeToTapeBarReaction st st' k).FiresTo
      (enc ({ state := st, tape := m } : MicroCfg Q s)) z' <->
      z' = enc ({ state := st', tape := m - k } : MicroCfg Q s) := by
  constructor
  · intro h
    exact Reaction.FiresTo.unique h
      (transferTapeToTapeBarReaction_firesTo
        (s := s) st st' m k hm hk)
  · intro hz
    rw [hz]
    exact transferTapeToTapeBarReaction_firesTo
      (s := s) st st' m k hm hk

theorem transferTapeToTapeBarReaction_firesTo_eraseMSBWith
    {s : Nat}
    (st st' : MicroState Q) (m : Nat) (r : Bool)
    (hm : m <= maxTape s)
    (hk : Encoding.bitDigit r * 3 ^ s <= m) :
    (transferTapeToTapeBarReaction st st'
      (Encoding.bitDigit r * 3 ^ s)).FiresTo
      (enc ({ state := st, tape := m } : MicroCfg Q s))
      (enc ({ state := st',
              tape := Encoding.eraseMSBWith s r m } : MicroCfg Q s)) := by
  simpa [Encoding.eraseMSBWith] using
    transferTapeToTapeBarReaction_firesTo
      (s := s) st st' m (Encoding.bitDigit r * 3 ^ s) hm hk

theorem transferTapeToTapeBarReaction_firesTo_eraseMSBWith_iff
    {s : Nat}
    (st st' : MicroState Q) (m : Nat) (r : Bool)
    (hm : m <= maxTape s)
    (hk : Encoding.bitDigit r * 3 ^ s <= m)
    (z' : State (Species Q)) :
    (transferTapeToTapeBarReaction st st'
      (Encoding.bitDigit r * 3 ^ s)).FiresTo
      (enc ({ state := st, tape := m } : MicroCfg Q s)) z' <->
      z' = enc ({ state := st',
                  tape := Encoding.eraseMSBWith s r m } : MicroCfg Q s) := by
  constructor
  · intro h
    exact Reaction.FiresTo.unique h
      (transferTapeToTapeBarReaction_firesTo_eraseMSBWith
        (s := s) st st' m r hm hk)
  · intro hz
    rw [hz]
    exact transferTapeToTapeBarReaction_firesTo_eraseMSBWith
      (s := s) st st' m r hm hk

def transferTapeBarToTapeReaction
    (st st' : MicroState Q) (k : Nat) :
    Reaction (Species Q) :=
  aggregateReaction st st' 0 k k 0

theorem transferTapeBarToTapeReaction_isAtMostBimolecularFull_of_le_one
    [Fintype Q]
    (st st' : MicroState Q) {k : Nat} (hk : k <= 1) :
    (transferTapeBarToTapeReaction st st' k).isAtMostBimolecularFull := by
  exact aggregateReaction_isAtMostBimolecularFull_of_sums_le_one
    st st' 0 k k 0 (by omega) (by omega)

@[simp]
theorem transferTapeBarToTapeReaction_one_inputArity
    [Fintype Q]
    (st st' : MicroState Q) :
    (transferTapeBarToTapeReaction st st' 1).inputArity = 2 := by
  simp [transferTapeBarToTapeReaction]

@[simp]
theorem transferTapeBarToTapeReaction_one_outputArity
    [Fintype Q]
    (st st' : MicroState Q) :
    (transferTapeBarToTapeReaction st st' 1).outputArity = 2 := by
  simp [transferTapeBarToTapeReaction]

theorem transferTapeBarToTapeReaction_one_isAtMostBimolecularFull
    [Fintype Q]
    (st st' : MicroState Q) :
    (transferTapeBarToTapeReaction st st' 1).isAtMostBimolecularFull :=
  transferTapeBarToTapeReaction_isAtMostBimolecularFull_of_le_one
    st st' le_rfl

theorem transferTapeBarToTapeReaction_firesTo
    {s : Nat}
    (st st' : MicroState Q) (m k : Nat)
    (hk : k <= maxTape s - m) :
    (transferTapeBarToTapeReaction st st' k).FiresTo
      (enc ({ state := st, tape := m } : MicroCfg Q s))
      (enc ({ state := st', tape := m + k } : MicroCfg Q s)) := by
  exact aggregateReaction_firesTo
    (s := s) st st' m (m + k) 0 k k 0
    (Nat.zero_le _) hk (by simp) (by
      simpa using tapeBar_to_tape_bar_eq (s := s) (m := m) (k := k))

theorem transferTapeBarToTapeReaction_firesTo_iff
    {s : Nat}
    (st st' : MicroState Q) (m k : Nat)
    (hk : k <= maxTape s - m)
    (z' : State (Species Q)) :
    (transferTapeBarToTapeReaction st st' k).FiresTo
      (enc ({ state := st, tape := m } : MicroCfg Q s)) z' <->
      z' = enc ({ state := st', tape := m + k } : MicroCfg Q s) := by
  constructor
  · intro h
    exact Reaction.FiresTo.unique h
      (transferTapeBarToTapeReaction_firesTo
        (s := s) st st' m k hk)
  · intro hz
    rw [hz]
    exact transferTapeBarToTapeReaction_firesTo
      (s := s) st st' m k hk

theorem transferTapeBarToTapeReaction_firesTo_writeLSB
    {s : Nat}
    (st st' : MicroState Q) (m : Nat) (b : Bool)
    (hk : Encoding.bitDigit b <= maxTape s - m) :
    (transferTapeBarToTapeReaction st st' (Encoding.bitDigit b)).FiresTo
      (enc ({ state := st, tape := m } : MicroCfg Q s))
      (enc ({ state := st',
              tape := Encoding.writeLSB m b } : MicroCfg Q s)) := by
  simpa [Encoding.writeLSB] using
    transferTapeBarToTapeReaction_firesTo
      (s := s) st st' m (Encoding.bitDigit b) hk

theorem transferTapeBarToTapeReaction_firesTo_writeLSB_iff
    {s : Nat}
    (st st' : MicroState Q) (m : Nat) (b : Bool)
    (hk : Encoding.bitDigit b <= maxTape s - m)
    (z' : State (Species Q)) :
    (transferTapeBarToTapeReaction st st' (Encoding.bitDigit b)).FiresTo
      (enc ({ state := st, tape := m } : MicroCfg Q s)) z' <->
      z' = enc ({ state := st',
                  tape := Encoding.writeLSB m b } : MicroCfg Q s) := by
  constructor
  · intro h
    exact Reaction.FiresTo.unique h
      (transferTapeBarToTapeReaction_firesTo_writeLSB
        (s := s) st st' m b hk)
  · intro hz
    rw [hz]
    exact transferTapeBarToTapeReaction_firesTo_writeLSB
      (s := s) st st' m b hk

theorem transferTapeBarToTapeReaction_firesTo_succ
    {s : Nat}
    (st st' : MicroState Q) (m : Nat)
    (hk : 1 <= maxTape s - m) :
    (transferTapeBarToTapeReaction st st' 1).FiresTo
      (enc ({ state := st, tape := m } : MicroCfg Q s))
      (enc ({ state := st', tape := m + 1 } : MicroCfg Q s)) :=
  transferTapeBarToTapeReaction_firesTo (s := s) st st' m 1 hk

theorem transferTapeBarToTapeReaction_firesTo_succ_iff
    {s : Nat}
    (st st' : MicroState Q) (m : Nat)
    (hk : 1 <= maxTape s - m)
    (z' : State (Species Q)) :
    (transferTapeBarToTapeReaction st st' 1).FiresTo
      (enc ({ state := st, tape := m } : MicroCfg Q s)) z' <->
      z' = enc ({ state := st', tape := m + 1 } : MicroCfg Q s) :=
  transferTapeBarToTapeReaction_firesTo_iff
    (s := s) st st' m 1 hk z'

def controlSwapReaction
    (st st' : MicroState Q) :
    Reaction (Species Q) :=
  aggregateReaction st st' 0 0 0 0

theorem controlSwapReaction_isAtMostBimolecularFull
    [Fintype Q]
    (st st' : MicroState Q) :
    (controlSwapReaction st st').isAtMostBimolecularFull := by
  exact aggregateReaction_isAtMostBimolecularFull_of_sums_le_one
    st st' 0 0 0 0 (by omega) (by omega)

theorem controlSwapReaction_firesTo
    {s : Nat}
    (st st' : MicroState Q) (m : Nat) :
    (controlSwapReaction st st').FiresTo
      (enc ({ state := st, tape := m } : MicroCfg Q s))
      (enc ({ state := st', tape := m } : MicroCfg Q s)) := by
  exact aggregateReaction_firesTo
    (s := s) st st' m m 0 0 0 0
    (Nat.zero_le _) (Nat.zero_le _) (by simp) (by simp)

theorem controlSwapReaction_firesTo_iff
    {s : Nat}
    (st st' : MicroState Q) (m : Nat)
    (z' : State (Species Q)) :
    (controlSwapReaction st st').FiresTo
      (enc ({ state := st, tape := m } : MicroCfg Q s)) z' <->
      z' = enc ({ state := st', tape := m } : MicroCfg Q s) := by
  constructor
  · intro h
    exact Reaction.FiresTo.unique h
      (controlSwapReaction_firesTo (s := s) st st' m)
  · intro hz
    rw [hz]
    exact controlSwapReaction_firesTo (s := s) st st' m

def preserveTapeUnitNetwork
    (st st' : MicroState Q) :
    Network (Species Q) :=
  Network.oneRxnNetwork (preserveTapeReaction st st' 1)

def preserveTapeBarUnitNetwork
    (st st' : MicroState Q) :
    Network (Species Q) :=
  Network.oneRxnNetwork (preserveTapeBarReaction st st' 1)

def transferTapeToTapeBarUnitNetwork
    (st st' : MicroState Q) :
    Network (Species Q) :=
  Network.oneRxnNetwork (transferTapeToTapeBarReaction st st' 1)

def transferTapeBarToTapeUnitNetwork
    (st st' : MicroState Q) :
    Network (Species Q) :=
  Network.oneRxnNetwork (transferTapeBarToTapeReaction st st' 1)

def controlSwapNetwork
    (st st' : MicroState Q) :
    Network (Species Q) :=
  Network.oneRxnNetwork (controlSwapReaction st st')

def tapeTransferUnitNetwork
    (st : MicroState Q) :
    Network (Species Q) :=
  (transferTapeToTapeBarUnitNetwork st st).parallel
    (transferTapeBarToTapeUnitNetwork st st)

def tapeTransferWithControlNetwork
    (st st' : MicroState Q) :
    Network (Species Q) :=
  (tapeTransferUnitNetwork st).parallel
    (controlSwapNetwork st st')

def tapeTransferWithControlToTapeBarSchedule
    (st st' : MicroState Q) (k : Nat) :
    List (tapeTransferWithControlNetwork st st').I :=
  ((List.replicate k Network.OneRxnIdx.step).map Sum.inl).map Sum.inl ++
    [Network.OneRxnIdx.step].map Sum.inr

def tapeTransferWithControlToTapeSchedule
    (st st' : MicroState Q) (k : Nat) :
    List (tapeTransferWithControlNetwork st st').I :=
  ((List.replicate k Network.OneRxnIdx.step).map Sum.inr).map Sum.inl ++
    [Network.OneRxnIdx.step].map Sum.inr

@[simp]
theorem tapeTransferWithControlToTapeBarSchedule_length
    (st st' : MicroState Q) (k : Nat) :
    (tapeTransferWithControlToTapeBarSchedule st st' k).length =
      k + 1 := by
  let A : List (tapeTransferWithControlNetwork st st').I :=
    ((List.replicate k Network.OneRxnIdx.step).map Sum.inl).map
      Sum.inl
  let B : List (tapeTransferWithControlNetwork st st').I :=
    [Network.OneRxnIdx.step].map Sum.inr
  change (A ++ B).length = k + 1
  rw [List.length_append]
  have hA : A.length = k := by
    dsimp [A]
    calc
      (List.map Sum.inl
          (List.map Sum.inl
            (List.replicate k Network.OneRxnIdx.step))).length =
          (List.map Sum.inl
            (List.replicate k Network.OneRxnIdx.step)).length :=
        List.length_map Sum.inl
      _ =
          (List.replicate k Network.OneRxnIdx.step).length :=
        List.length_map Sum.inl
      _ = k := List.length_replicate
  have hB : B.length = 1 := by
    dsimp [B]
    exact List.length_singleton
  rw [hA, hB]

@[simp]
theorem tapeTransferWithControlToTapeSchedule_length
    (st st' : MicroState Q) (k : Nat) :
    (tapeTransferWithControlToTapeSchedule st st' k).length =
      k + 1 := by
  let A : List (tapeTransferWithControlNetwork st st').I :=
    ((List.replicate k Network.OneRxnIdx.step).map Sum.inr).map
      Sum.inl
  let B : List (tapeTransferWithControlNetwork st st').I :=
    [Network.OneRxnIdx.step].map Sum.inr
  change (A ++ B).length = k + 1
  rw [List.length_append]
  have hA : A.length = k := by
    dsimp [A]
    calc
      (List.map Sum.inl
          (List.map Sum.inr
            (List.replicate k Network.OneRxnIdx.step))).length =
          (List.map Sum.inr
            (List.replicate k Network.OneRxnIdx.step)).length :=
        List.length_map Sum.inl
      _ =
          (List.replicate k Network.OneRxnIdx.step).length :=
        List.length_map Sum.inr
      _ = k := List.length_replicate
  have hB : B.length = 1 := by
    dsimp [B]
    exact List.length_singleton
  rw [hA, hB]

theorem preserveTapeUnitNetwork_allAtMostBimolecularFull
    [Fintype Q]
    (st st' : MicroState Q) :
    (preserveTapeUnitNetwork st st').allAtMostBimolecularFull :=
  (Network.oneRxnNetwork_allAtMostBimolecularFull_iff
    (preserveTapeReaction st st' 1)).2
    (preserveTapeReaction_isAtMostBimolecularFull_of_le_one
      st st' le_rfl)

theorem preserveTapeBarUnitNetwork_allAtMostBimolecularFull
    [Fintype Q]
    (st st' : MicroState Q) :
    (preserveTapeBarUnitNetwork st st').allAtMostBimolecularFull :=
  (Network.oneRxnNetwork_allAtMostBimolecularFull_iff
    (preserveTapeBarReaction st st' 1)).2
    (preserveTapeBarReaction_isAtMostBimolecularFull_of_le_one
      st st' le_rfl)

theorem transferTapeToTapeBarUnitNetwork_allAtMostBimolecularFull
    [Fintype Q]
    (st st' : MicroState Q) :
    (transferTapeToTapeBarUnitNetwork st st').allAtMostBimolecularFull :=
  (Network.oneRxnNetwork_allAtMostBimolecularFull_iff
    (transferTapeToTapeBarReaction st st' 1)).2
    (transferTapeToTapeBarReaction_one_isAtMostBimolecularFull
      st st')

theorem transferTapeBarToTapeUnitNetwork_allAtMostBimolecularFull
    [Fintype Q]
    (st st' : MicroState Q) :
    (transferTapeBarToTapeUnitNetwork st st').allAtMostBimolecularFull :=
  (Network.oneRxnNetwork_allAtMostBimolecularFull_iff
    (transferTapeBarToTapeReaction st st' 1)).2
    (transferTapeBarToTapeReaction_one_isAtMostBimolecularFull
      st st')

theorem controlSwapNetwork_allAtMostBimolecularFull
    [Fintype Q]
    (st st' : MicroState Q) :
    (controlSwapNetwork st st').allAtMostBimolecularFull :=
  (Network.oneRxnNetwork_allAtMostBimolecularFull_iff
    (controlSwapReaction st st')).2
    (controlSwapReaction_isAtMostBimolecularFull st st')

theorem tapeTransferUnitNetwork_allAtMostBimolecularFull
    [Fintype Q]
    (st : MicroState Q) :
    (tapeTransferUnitNetwork st).allAtMostBimolecularFull :=
  (Network.parallel_allAtMostBimolecularFull_iff
    (transferTapeToTapeBarUnitNetwork st st)
    (transferTapeBarToTapeUnitNetwork st st)).2
    ⟨
      transferTapeToTapeBarUnitNetwork_allAtMostBimolecularFull st st,
      transferTapeBarToTapeUnitNetwork_allAtMostBimolecularFull st st
    ⟩

theorem tapeTransferWithControlNetwork_allAtMostBimolecularFull
    [Fintype Q]
    (st st' : MicroState Q) :
    (tapeTransferWithControlNetwork st st').allAtMostBimolecularFull :=
  (Network.parallel_allAtMostBimolecularFull_iff
    (tapeTransferUnitNetwork st)
    (controlSwapNetwork st st')).2
    ⟨
      tapeTransferUnitNetwork_allAtMostBimolecularFull st,
      controlSwapNetwork_allAtMostBimolecularFull st st'
    ⟩

theorem preserveTapeUnitNetwork_allAtMostBimolecularInput
    [Fintype Q]
    (st st' : MicroState Q) :
    (preserveTapeUnitNetwork st st').allAtMostBimolecularInput :=
  Network.allAtMostBimolecularInput_of_full
    (preserveTapeUnitNetwork_allAtMostBimolecularFull st st')

theorem preserveTapeUnitNetwork_allAtMostBimolecularOutput
    [Fintype Q]
    (st st' : MicroState Q) :
    (preserveTapeUnitNetwork st st').allAtMostBimolecularOutput :=
  Network.allAtMostBimolecularOutput_of_full
    (preserveTapeUnitNetwork_allAtMostBimolecularFull st st')

theorem preserveTapeBarUnitNetwork_allAtMostBimolecularInput
    [Fintype Q]
    (st st' : MicroState Q) :
    (preserveTapeBarUnitNetwork st st').allAtMostBimolecularInput :=
  Network.allAtMostBimolecularInput_of_full
    (preserveTapeBarUnitNetwork_allAtMostBimolecularFull st st')

theorem preserveTapeBarUnitNetwork_allAtMostBimolecularOutput
    [Fintype Q]
    (st st' : MicroState Q) :
    (preserveTapeBarUnitNetwork st st').allAtMostBimolecularOutput :=
  Network.allAtMostBimolecularOutput_of_full
    (preserveTapeBarUnitNetwork_allAtMostBimolecularFull st st')

theorem transferTapeToTapeBarUnitNetwork_allAtMostBimolecularInput
    [Fintype Q]
    (st st' : MicroState Q) :
    (transferTapeToTapeBarUnitNetwork st st').allAtMostBimolecularInput :=
  Network.allAtMostBimolecularInput_of_full
    (transferTapeToTapeBarUnitNetwork_allAtMostBimolecularFull st st')

theorem transferTapeToTapeBarUnitNetwork_allAtMostBimolecularOutput
    [Fintype Q]
    (st st' : MicroState Q) :
    (transferTapeToTapeBarUnitNetwork st st').allAtMostBimolecularOutput :=
  Network.allAtMostBimolecularOutput_of_full
    (transferTapeToTapeBarUnitNetwork_allAtMostBimolecularFull st st')

theorem transferTapeBarToTapeUnitNetwork_allAtMostBimolecularInput
    [Fintype Q]
    (st st' : MicroState Q) :
    (transferTapeBarToTapeUnitNetwork st st').allAtMostBimolecularInput :=
  Network.allAtMostBimolecularInput_of_full
    (transferTapeBarToTapeUnitNetwork_allAtMostBimolecularFull st st')

theorem transferTapeBarToTapeUnitNetwork_allAtMostBimolecularOutput
    [Fintype Q]
    (st st' : MicroState Q) :
    (transferTapeBarToTapeUnitNetwork st st').allAtMostBimolecularOutput :=
  Network.allAtMostBimolecularOutput_of_full
    (transferTapeBarToTapeUnitNetwork_allAtMostBimolecularFull st st')

theorem controlSwapNetwork_allAtMostBimolecularInput
    [Fintype Q]
    (st st' : MicroState Q) :
    (controlSwapNetwork st st').allAtMostBimolecularInput :=
  Network.allAtMostBimolecularInput_of_full
    (controlSwapNetwork_allAtMostBimolecularFull st st')

theorem controlSwapNetwork_allAtMostBimolecularOutput
    [Fintype Q]
    (st st' : MicroState Q) :
    (controlSwapNetwork st st').allAtMostBimolecularOutput :=
  Network.allAtMostBimolecularOutput_of_full
    (controlSwapNetwork_allAtMostBimolecularFull st st')

theorem tapeTransferUnitNetwork_allAtMostBimolecularInput
    [Fintype Q]
    (st : MicroState Q) :
    (tapeTransferUnitNetwork st).allAtMostBimolecularInput :=
  Network.allAtMostBimolecularInput_of_full
    (tapeTransferUnitNetwork_allAtMostBimolecularFull st)

theorem tapeTransferUnitNetwork_allAtMostBimolecularOutput
    [Fintype Q]
    (st : MicroState Q) :
    (tapeTransferUnitNetwork st).allAtMostBimolecularOutput :=
  Network.allAtMostBimolecularOutput_of_full
    (tapeTransferUnitNetwork_allAtMostBimolecularFull st)

theorem tapeTransferWithControlNetwork_allAtMostBimolecularInput
    [Fintype Q]
    (st st' : MicroState Q) :
    (tapeTransferWithControlNetwork st st').allAtMostBimolecularInput :=
  Network.allAtMostBimolecularInput_of_full
    (tapeTransferWithControlNetwork_allAtMostBimolecularFull st st')

theorem tapeTransferWithControlNetwork_allAtMostBimolecularOutput
    [Fintype Q]
    (st st' : MicroState Q) :
    (tapeTransferWithControlNetwork st st').allAtMostBimolecularOutput :=
  Network.allAtMostBimolecularOutput_of_full
    (tapeTransferWithControlNetwork_allAtMostBimolecularFull st st')

theorem preserveTapeUnitNetwork_allUnitRate
    (st st' : MicroState Q) :
    (preserveTapeUnitNetwork st st').allUnitRate :=
  (Network.oneRxnNetwork_allUnitRate_iff
    (preserveTapeReaction st st' 1)).2 rfl

theorem preserveTapeBarUnitNetwork_allUnitRate
    (st st' : MicroState Q) :
    (preserveTapeBarUnitNetwork st st').allUnitRate :=
  (Network.oneRxnNetwork_allUnitRate_iff
    (preserveTapeBarReaction st st' 1)).2 rfl

theorem transferTapeToTapeBarUnitNetwork_allUnitRate
    (st st' : MicroState Q) :
    (transferTapeToTapeBarUnitNetwork st st').allUnitRate :=
  (Network.oneRxnNetwork_allUnitRate_iff
    (transferTapeToTapeBarReaction st st' 1)).2 rfl

theorem transferTapeBarToTapeUnitNetwork_allUnitRate
    (st st' : MicroState Q) :
    (transferTapeBarToTapeUnitNetwork st st').allUnitRate :=
  (Network.oneRxnNetwork_allUnitRate_iff
    (transferTapeBarToTapeReaction st st' 1)).2 rfl

theorem controlSwapNetwork_allUnitRate
    (st st' : MicroState Q) :
    (controlSwapNetwork st st').allUnitRate :=
  (Network.oneRxnNetwork_allUnitRate_iff
    (controlSwapReaction st st')).2 rfl

theorem tapeTransferUnitNetwork_allUnitRate
    (st : MicroState Q) :
    (tapeTransferUnitNetwork st).allUnitRate :=
  (Network.parallel_allUnitRate_iff
    (transferTapeToTapeBarUnitNetwork st st)
    (transferTapeBarToTapeUnitNetwork st st)).2
    ⟨
      transferTapeToTapeBarUnitNetwork_allUnitRate st st,
      transferTapeBarToTapeUnitNetwork_allUnitRate st st
    ⟩

theorem tapeTransferWithControlNetwork_allUnitRate
    (st st' : MicroState Q) :
    (tapeTransferWithControlNetwork st st').allUnitRate :=
  (Network.parallel_allUnitRate_iff
    (tapeTransferUnitNetwork st)
    (controlSwapNetwork st st')).2
    ⟨
      tapeTransferUnitNetwork_allUnitRate st,
      controlSwapNetwork_allUnitRate st st'
    ⟩

theorem preserveTapeUnitNetwork_hasPositiveRates
    (st st' : MicroState Q) :
    (preserveTapeUnitNetwork st st').hasPositiveRates :=
  Network.hasPositiveRates_of_allUnitRate
    (preserveTapeUnitNetwork_allUnitRate st st')

theorem preserveTapeUnitNetwork_equalRates
    (st st' : MicroState Q) :
    (preserveTapeUnitNetwork st st').equalRates :=
  Network.equalRates_of_allUnitRate
    (preserveTapeUnitNetwork_allUnitRate st st')

theorem preserveTapeBarUnitNetwork_hasPositiveRates
    (st st' : MicroState Q) :
    (preserveTapeBarUnitNetwork st st').hasPositiveRates :=
  Network.hasPositiveRates_of_allUnitRate
    (preserveTapeBarUnitNetwork_allUnitRate st st')

theorem preserveTapeBarUnitNetwork_equalRates
    (st st' : MicroState Q) :
    (preserveTapeBarUnitNetwork st st').equalRates :=
  Network.equalRates_of_allUnitRate
    (preserveTapeBarUnitNetwork_allUnitRate st st')

theorem transferTapeToTapeBarUnitNetwork_hasPositiveRates
    (st st' : MicroState Q) :
    (transferTapeToTapeBarUnitNetwork st st').hasPositiveRates :=
  Network.hasPositiveRates_of_allUnitRate
    (transferTapeToTapeBarUnitNetwork_allUnitRate st st')

theorem transferTapeToTapeBarUnitNetwork_equalRates
    (st st' : MicroState Q) :
    (transferTapeToTapeBarUnitNetwork st st').equalRates :=
  Network.equalRates_of_allUnitRate
    (transferTapeToTapeBarUnitNetwork_allUnitRate st st')

theorem transferTapeBarToTapeUnitNetwork_hasPositiveRates
    (st st' : MicroState Q) :
    (transferTapeBarToTapeUnitNetwork st st').hasPositiveRates :=
  Network.hasPositiveRates_of_allUnitRate
    (transferTapeBarToTapeUnitNetwork_allUnitRate st st')

theorem transferTapeBarToTapeUnitNetwork_equalRates
    (st st' : MicroState Q) :
    (transferTapeBarToTapeUnitNetwork st st').equalRates :=
  Network.equalRates_of_allUnitRate
    (transferTapeBarToTapeUnitNetwork_allUnitRate st st')

theorem controlSwapNetwork_hasPositiveRates
    (st st' : MicroState Q) :
    (controlSwapNetwork st st').hasPositiveRates :=
  Network.hasPositiveRates_of_allUnitRate
    (controlSwapNetwork_allUnitRate st st')

theorem controlSwapNetwork_equalRates
    (st st' : MicroState Q) :
    (controlSwapNetwork st st').equalRates :=
  Network.equalRates_of_allUnitRate
    (controlSwapNetwork_allUnitRate st st')

theorem tapeTransferUnitNetwork_hasPositiveRates
    (st : MicroState Q) :
    (tapeTransferUnitNetwork st).hasPositiveRates :=
  Network.hasPositiveRates_of_allUnitRate
    (tapeTransferUnitNetwork_allUnitRate st)

theorem tapeTransferUnitNetwork_equalRates
    (st : MicroState Q) :
    (tapeTransferUnitNetwork st).equalRates :=
  Network.equalRates_of_allUnitRate
    (tapeTransferUnitNetwork_allUnitRate st)

theorem tapeTransferWithControlNetwork_hasPositiveRates
    (st st' : MicroState Q) :
    (tapeTransferWithControlNetwork st st').hasPositiveRates :=
  Network.hasPositiveRates_of_allUnitRate
    (tapeTransferWithControlNetwork_allUnitRate st st')

theorem tapeTransferWithControlNetwork_equalRates
    (st st' : MicroState Q) :
    (tapeTransferWithControlNetwork st st').equalRates :=
  Network.equalRates_of_allUnitRate
    (tapeTransferWithControlNetwork_allUnitRate st st')

theorem preserveTapeUnitNetwork_exec
    {s : Nat}
    (st st' : MicroState Q) (m : Nat)
    (hm : 1 <= m) :
    (preserveTapeUnitNetwork st st').Exec
      (enc ({ state := st, tape := m } : MicroCfg Q s))
      (enc ({ state := st', tape := m } : MicroCfg Q s))
      [Network.OneRxnIdx.step] :=
  Network.oneRxn_exec
    (preserveTapeReaction_firesTo (s := s) st st' m 1 hm)

theorem preserveTapeBarUnitNetwork_exec
    {s : Nat}
    (st st' : MicroState Q) (m : Nat)
    (hm : 1 <= maxTape s - m) :
    (preserveTapeBarUnitNetwork st st').Exec
      (enc ({ state := st, tape := m } : MicroCfg Q s))
      (enc ({ state := st', tape := m } : MicroCfg Q s))
      [Network.OneRxnIdx.step] :=
  Network.oneRxn_exec
    (preserveTapeBarReaction_firesTo (s := s) st st' m 1 hm)

theorem transferTapeToTapeBarUnitNetwork_exec
    {s : Nat}
    (st st' : MicroState Q) (m : Nat)
    (hm : m <= maxTape s)
    (hpos : 1 <= m) :
    (transferTapeToTapeBarUnitNetwork st st').Exec
      (enc ({ state := st, tape := m } : MicroCfg Q s))
      (enc ({ state := st', tape := m - 1 } : MicroCfg Q s))
      [Network.OneRxnIdx.step] :=
  Network.oneRxn_exec
    (transferTapeToTapeBarReaction_firesTo
      (s := s) st st' m 1 hm hpos)

theorem transferTapeBarToTapeUnitNetwork_exec
    {s : Nat}
    (st st' : MicroState Q) (m : Nat)
    (hm : 1 <= maxTape s - m) :
    (transferTapeBarToTapeUnitNetwork st st').Exec
      (enc ({ state := st, tape := m } : MicroCfg Q s))
      (enc ({ state := st', tape := m + 1 } : MicroCfg Q s))
      [Network.OneRxnIdx.step] :=
  Network.oneRxn_exec
    (transferTapeBarToTapeReaction_firesTo_succ
      (s := s) st st' m hm)

theorem controlSwapNetwork_exec
    {s : Nat}
    (st st' : MicroState Q) (m : Nat) :
    (controlSwapNetwork st st').Exec
      (enc ({ state := st, tape := m } : MicroCfg Q s))
      (enc ({ state := st', tape := m } : MicroCfg Q s))
      [Network.OneRxnIdx.step] :=
  Network.oneRxn_exec
    (controlSwapReaction_firesTo (s := s) st st' m)

def preserveTapeUnitNetwork_intendedSchedule
    {s : Nat}
    (st st' : MicroState Q) (m : Nat)
    (hm : 1 <= m) :
    (preserveTapeUnitNetwork st st').IntendedSchedule
      (enc ({ state := st, tape := m } : MicroCfg Q s))
      (enc ({ state := st', tape := m } : MicroCfg Q s)) :=
  Network.oneRxnNetwork_intendedSchedule
    (preserveTapeReaction_firesTo (s := s) st st' m 1 hm)

@[simp]
theorem preserveTapeUnitNetwork_intendedSchedule_schedule
    {s : Nat}
    (st st' : MicroState Q) (m : Nat)
    (hm : 1 <= m) :
    (preserveTapeUnitNetwork_intendedSchedule
      (s := s) st st' m hm).schedule =
        [Network.OneRxnIdx.step] := by
  rfl

@[simp]
theorem preserveTapeUnitNetwork_intendedSchedule_firingCount
    {s : Nat}
    (st st' : MicroState Q) (m : Nat)
    (hm : 1 <= m) :
    (preserveTapeUnitNetwork_intendedSchedule
      (s := s) st st' m hm).firingCount = 1 := by
  rfl

def preserveTapeUnitNetwork_boundedIntendedSchedule
    {s : Nat}
    (st st' : MicroState Q) (m : Nat)
    (hm : 1 <= m) :
    (preserveTapeUnitNetwork st st').BoundedIntendedSchedule
      1
      (enc ({ state := st, tape := m } : MicroCfg Q s))
      (enc ({ state := st', tape := m } : MicroCfg Q s)) :=
  Network.oneRxnNetwork_boundedIntendedSchedule
    (preserveTapeReaction_firesTo (s := s) st st' m 1 hm)

@[simp]
theorem preserveTapeUnitNetwork_boundedIntendedSchedule_schedule
    {s : Nat}
    (st st' : MicroState Q) (m : Nat)
    (hm : 1 <= m) :
    (preserveTapeUnitNetwork_boundedIntendedSchedule
      (s := s) st st' m hm).schedule =
        [Network.OneRxnIdx.step] := by
  rfl

@[simp]
theorem preserveTapeUnitNetwork_boundedIntendedSchedule_firingCount
    {s : Nat}
    (st st' : MicroState Q) (m : Nat)
    (hm : 1 <= m) :
    (preserveTapeUnitNetwork_boundedIntendedSchedule
      (s := s) st st' m hm).firingCount = 1 := by
  rfl

@[simp]
theorem preserveTapeUnitNetwork_boundedIntendedSchedule_toIntendedSchedule
    {s : Nat}
    (st st' : MicroState Q) (m : Nat)
    (hm : 1 <= m) :
    (preserveTapeUnitNetwork_boundedIntendedSchedule
      (s := s) st st' m hm).toIntendedSchedule =
        preserveTapeUnitNetwork_intendedSchedule (s := s) st st' m hm := by
  rfl

def preserveTapeBarUnitNetwork_intendedSchedule
    {s : Nat}
    (st st' : MicroState Q) (m : Nat)
    (hm : 1 <= maxTape s - m) :
    (preserveTapeBarUnitNetwork st st').IntendedSchedule
      (enc ({ state := st, tape := m } : MicroCfg Q s))
      (enc ({ state := st', tape := m } : MicroCfg Q s)) :=
  Network.oneRxnNetwork_intendedSchedule
    (preserveTapeBarReaction_firesTo (s := s) st st' m 1 hm)

@[simp]
theorem preserveTapeBarUnitNetwork_intendedSchedule_schedule
    {s : Nat}
    (st st' : MicroState Q) (m : Nat)
    (hm : 1 <= maxTape s - m) :
    (preserveTapeBarUnitNetwork_intendedSchedule
      (s := s) st st' m hm).schedule =
        [Network.OneRxnIdx.step] := by
  rfl

@[simp]
theorem preserveTapeBarUnitNetwork_intendedSchedule_firingCount
    {s : Nat}
    (st st' : MicroState Q) (m : Nat)
    (hm : 1 <= maxTape s - m) :
    (preserveTapeBarUnitNetwork_intendedSchedule
      (s := s) st st' m hm).firingCount = 1 := by
  rfl

def preserveTapeBarUnitNetwork_boundedIntendedSchedule
    {s : Nat}
    (st st' : MicroState Q) (m : Nat)
    (hm : 1 <= maxTape s - m) :
    (preserveTapeBarUnitNetwork st st').BoundedIntendedSchedule
      1
      (enc ({ state := st, tape := m } : MicroCfg Q s))
      (enc ({ state := st', tape := m } : MicroCfg Q s)) :=
  Network.oneRxnNetwork_boundedIntendedSchedule
    (preserveTapeBarReaction_firesTo (s := s) st st' m 1 hm)

@[simp]
theorem preserveTapeBarUnitNetwork_boundedIntendedSchedule_schedule
    {s : Nat}
    (st st' : MicroState Q) (m : Nat)
    (hm : 1 <= maxTape s - m) :
    (preserveTapeBarUnitNetwork_boundedIntendedSchedule
      (s := s) st st' m hm).schedule =
        [Network.OneRxnIdx.step] := by
  rfl

@[simp]
theorem preserveTapeBarUnitNetwork_boundedIntendedSchedule_firingCount
    {s : Nat}
    (st st' : MicroState Q) (m : Nat)
    (hm : 1 <= maxTape s - m) :
    (preserveTapeBarUnitNetwork_boundedIntendedSchedule
      (s := s) st st' m hm).firingCount = 1 := by
  rfl

@[simp]
theorem preserveTapeBarUnitNetwork_boundedIntendedSchedule_toIntendedSchedule
    {s : Nat}
    (st st' : MicroState Q) (m : Nat)
    (hm : 1 <= maxTape s - m) :
    (preserveTapeBarUnitNetwork_boundedIntendedSchedule
      (s := s) st st' m hm).toIntendedSchedule =
        preserveTapeBarUnitNetwork_intendedSchedule (s := s) st st' m hm := by
  rfl

def transferTapeToTapeBarUnitNetwork_intendedSchedule
    {s : Nat}
    (st st' : MicroState Q) (m : Nat)
    (hm : m <= maxTape s)
    (hpos : 1 <= m) :
    (transferTapeToTapeBarUnitNetwork st st').IntendedSchedule
      (enc ({ state := st, tape := m } : MicroCfg Q s))
      (enc ({ state := st', tape := m - 1 } : MicroCfg Q s)) :=
  Network.oneRxnNetwork_intendedSchedule
    (transferTapeToTapeBarReaction_firesTo
      (s := s) st st' m 1 hm hpos)

@[simp]
theorem transferTapeToTapeBarUnitNetwork_intendedSchedule_schedule
    {s : Nat}
    (st st' : MicroState Q) (m : Nat)
    (hm : m <= maxTape s)
    (hpos : 1 <= m) :
    (transferTapeToTapeBarUnitNetwork_intendedSchedule
      (s := s) st st' m hm hpos).schedule =
        [Network.OneRxnIdx.step] := by
  rfl

@[simp]
theorem transferTapeToTapeBarUnitNetwork_intendedSchedule_firingCount
    {s : Nat}
    (st st' : MicroState Q) (m : Nat)
    (hm : m <= maxTape s)
    (hpos : 1 <= m) :
    (transferTapeToTapeBarUnitNetwork_intendedSchedule
      (s := s) st st' m hm hpos).firingCount = 1 := by
  rfl

def transferTapeToTapeBarUnitNetwork_boundedIntendedSchedule
    {s : Nat}
    (st st' : MicroState Q) (m : Nat)
    (hm : m <= maxTape s)
    (hpos : 1 <= m) :
    (transferTapeToTapeBarUnitNetwork st st').BoundedIntendedSchedule
      1
      (enc ({ state := st, tape := m } : MicroCfg Q s))
      (enc ({ state := st', tape := m - 1 } : MicroCfg Q s)) :=
  Network.oneRxnNetwork_boundedIntendedSchedule
    (transferTapeToTapeBarReaction_firesTo
      (s := s) st st' m 1 hm hpos)

@[simp]
theorem transferTapeToTapeBarUnitNetwork_boundedIntendedSchedule_schedule
    {s : Nat}
    (st st' : MicroState Q) (m : Nat)
    (hm : m <= maxTape s)
    (hpos : 1 <= m) :
    (transferTapeToTapeBarUnitNetwork_boundedIntendedSchedule
      (s := s) st st' m hm hpos).schedule =
        [Network.OneRxnIdx.step] := by
  rfl

@[simp]
theorem transferTapeToTapeBarUnitNetwork_boundedIntendedSchedule_firingCount
    {s : Nat}
    (st st' : MicroState Q) (m : Nat)
    (hm : m <= maxTape s)
    (hpos : 1 <= m) :
    (transferTapeToTapeBarUnitNetwork_boundedIntendedSchedule
      (s := s) st st' m hm hpos).firingCount = 1 := by
  rfl

@[simp]
theorem transferTapeToTapeBarUnitNetwork_boundedIntendedSchedule_toIntendedSchedule
    {s : Nat}
    (st st' : MicroState Q) (m : Nat)
    (hm : m <= maxTape s)
    (hpos : 1 <= m) :
    (transferTapeToTapeBarUnitNetwork_boundedIntendedSchedule
      (s := s) st st' m hm hpos).toIntendedSchedule =
        transferTapeToTapeBarUnitNetwork_intendedSchedule
          (s := s) st st' m hm hpos := by
  rfl

def transferTapeBarToTapeUnitNetwork_intendedSchedule
    {s : Nat}
    (st st' : MicroState Q) (m : Nat)
    (hm : 1 <= maxTape s - m) :
    (transferTapeBarToTapeUnitNetwork st st').IntendedSchedule
      (enc ({ state := st, tape := m } : MicroCfg Q s))
      (enc ({ state := st', tape := m + 1 } : MicroCfg Q s)) :=
  Network.oneRxnNetwork_intendedSchedule
    (transferTapeBarToTapeReaction_firesTo_succ
      (s := s) st st' m hm)

@[simp]
theorem transferTapeBarToTapeUnitNetwork_intendedSchedule_schedule
    {s : Nat}
    (st st' : MicroState Q) (m : Nat)
    (hm : 1 <= maxTape s - m) :
    (transferTapeBarToTapeUnitNetwork_intendedSchedule
      (s := s) st st' m hm).schedule =
        [Network.OneRxnIdx.step] := by
  rfl

@[simp]
theorem transferTapeBarToTapeUnitNetwork_intendedSchedule_firingCount
    {s : Nat}
    (st st' : MicroState Q) (m : Nat)
    (hm : 1 <= maxTape s - m) :
    (transferTapeBarToTapeUnitNetwork_intendedSchedule
      (s := s) st st' m hm).firingCount = 1 := by
  rfl

def transferTapeBarToTapeUnitNetwork_boundedIntendedSchedule
    {s : Nat}
    (st st' : MicroState Q) (m : Nat)
    (hm : 1 <= maxTape s - m) :
    (transferTapeBarToTapeUnitNetwork st st').BoundedIntendedSchedule
      1
      (enc ({ state := st, tape := m } : MicroCfg Q s))
      (enc ({ state := st', tape := m + 1 } : MicroCfg Q s)) :=
  Network.oneRxnNetwork_boundedIntendedSchedule
    (transferTapeBarToTapeReaction_firesTo_succ
      (s := s) st st' m hm)

@[simp]
theorem transferTapeBarToTapeUnitNetwork_boundedIntendedSchedule_schedule
    {s : Nat}
    (st st' : MicroState Q) (m : Nat)
    (hm : 1 <= maxTape s - m) :
    (transferTapeBarToTapeUnitNetwork_boundedIntendedSchedule
      (s := s) st st' m hm).schedule =
        [Network.OneRxnIdx.step] := by
  rfl

@[simp]
theorem transferTapeBarToTapeUnitNetwork_boundedIntendedSchedule_firingCount
    {s : Nat}
    (st st' : MicroState Q) (m : Nat)
    (hm : 1 <= maxTape s - m) :
    (transferTapeBarToTapeUnitNetwork_boundedIntendedSchedule
      (s := s) st st' m hm).firingCount = 1 := by
  rfl

@[simp]
theorem transferTapeBarToTapeUnitNetwork_boundedIntendedSchedule_toIntendedSchedule
    {s : Nat}
    (st st' : MicroState Q) (m : Nat)
    (hm : 1 <= maxTape s - m) :
    (transferTapeBarToTapeUnitNetwork_boundedIntendedSchedule
      (s := s) st st' m hm).toIntendedSchedule =
        transferTapeBarToTapeUnitNetwork_intendedSchedule (s := s) st st' m hm := by
  rfl

def controlSwapNetwork_intendedSchedule
    {s : Nat}
    (st st' : MicroState Q) (m : Nat) :
    (controlSwapNetwork st st').IntendedSchedule
      (enc ({ state := st, tape := m } : MicroCfg Q s))
      (enc ({ state := st', tape := m } : MicroCfg Q s)) :=
  Network.oneRxnNetwork_intendedSchedule
    (controlSwapReaction_firesTo (s := s) st st' m)

@[simp]
theorem controlSwapNetwork_intendedSchedule_schedule
    {s : Nat}
    (st st' : MicroState Q) (m : Nat) :
    (controlSwapNetwork_intendedSchedule (s := s) st st' m).schedule =
      [Network.OneRxnIdx.step] := by
  rfl

@[simp]
theorem controlSwapNetwork_intendedSchedule_firingCount
    {s : Nat}
    (st st' : MicroState Q) (m : Nat) :
    (controlSwapNetwork_intendedSchedule (s := s) st st' m).firingCount =
      1 := by
  rfl

def controlSwapNetwork_boundedIntendedSchedule
    {s : Nat}
    (st st' : MicroState Q) (m : Nat) :
    (controlSwapNetwork st st').BoundedIntendedSchedule
      1
      (enc ({ state := st, tape := m } : MicroCfg Q s))
      (enc ({ state := st', tape := m } : MicroCfg Q s)) :=
  Network.oneRxnNetwork_boundedIntendedSchedule
    (controlSwapReaction_firesTo (s := s) st st' m)

@[simp]
theorem controlSwapNetwork_boundedIntendedSchedule_schedule
    {s : Nat}
    (st st' : MicroState Q) (m : Nat) :
    (controlSwapNetwork_boundedIntendedSchedule (s := s) st st' m).schedule =
      [Network.OneRxnIdx.step] := by
  rfl

@[simp]
theorem controlSwapNetwork_boundedIntendedSchedule_firingCount
    {s : Nat}
    (st st' : MicroState Q) (m : Nat) :
    (controlSwapNetwork_boundedIntendedSchedule (s := s) st st' m).firingCount =
      1 := by
  rfl

@[simp]
theorem controlSwapNetwork_boundedIntendedSchedule_toIntendedSchedule
    {s : Nat}
    (st st' : MicroState Q) (m : Nat) :
    (controlSwapNetwork_boundedIntendedSchedule
      (s := s) st st' m).toIntendedSchedule =
        controlSwapNetwork_intendedSchedule (s := s) st st' m := by
  rfl

theorem transferTapeToTapeBarUnitNetwork_exec_replicate
    {s : Nat}
    (st : MicroState Q) (m k : Nat)
    (hm : m <= maxTape s)
    (hk : k <= m) :
    (transferTapeToTapeBarUnitNetwork st st).Exec
      (enc ({ state := st, tape := m } : MicroCfg Q s))
      (enc ({ state := st, tape := m - k } : MicroCfg Q s))
      (List.replicate k Network.OneRxnIdx.step) := by
  induction k generalizing m with
  | zero =>
      simp
  | succ k ih =>
      have hpos : 1 <= m := by omega
      have hm' : m - 1 <= maxTape s := by omega
      have hk' : k <= m - 1 := by omega
      have htarget : m - 1 - k = m - Nat.succ k := by omega
      have hfirst :
          (transferTapeToTapeBarUnitNetwork st st).Exec
            (enc ({ state := st, tape := m } : MicroCfg Q s))
            (enc ({ state := st, tape := m - 1 } : MicroCfg Q s))
            [Network.OneRxnIdx.step] :=
        transferTapeToTapeBarUnitNetwork_exec
          (s := s) st st m hm hpos
      have htail :
          (transferTapeToTapeBarUnitNetwork st st).Exec
            (enc ({ state := st, tape := m - 1 } : MicroCfg Q s))
            (enc ({ state := st, tape := m - Nat.succ k } :
              MicroCfg Q s))
            (List.replicate k Network.OneRxnIdx.step) := by
        simpa [htarget] using ih (m - 1) hm' hk'
      simpa [List.replicate_succ] using
        (ExecOf.append hfirst htail)

def transferTapeToTapeBarUnitNetwork_boundedIntendedSchedule_replicate
    {s : Nat}
    (st : MicroState Q) (m k : Nat)
    (hm : m <= maxTape s)
    (hk : k <= m) :
    (transferTapeToTapeBarUnitNetwork st st).BoundedIntendedSchedule k
      (enc ({ state := st, tape := m } : MicroCfg Q s))
      (enc ({ state := st, tape := m - k } : MicroCfg Q s)) where
  schedule := List.replicate k Network.OneRxnIdx.step
  exec :=
    transferTapeToTapeBarUnitNetwork_exec_replicate
      (s := s) st m k hm hk
  length_bound := by simp

@[simp]
theorem transferTapeToTapeBarUnitNetwork_boundedIntendedSchedule_replicate_schedule
    {s : Nat}
    (st : MicroState Q) (m k : Nat)
    (hm : m <= maxTape s)
    (hk : k <= m) :
    (transferTapeToTapeBarUnitNetwork_boundedIntendedSchedule_replicate
      (s := s) st m k hm hk).schedule =
        List.replicate k Network.OneRxnIdx.step := by
  rfl

@[simp]
theorem transferTapeToTapeBarUnitNetwork_boundedIntendedSchedule_replicate_firingCount
    {s : Nat}
    (st : MicroState Q) (m k : Nat)
    (hm : m <= maxTape s)
    (hk : k <= m) :
    (transferTapeToTapeBarUnitNetwork_boundedIntendedSchedule_replicate
      (s := s) st m k hm hk).firingCount = k := by
  change (List.replicate k Network.OneRxnIdx.step).length = k
  exact List.length_replicate

theorem transferTapeBarToTapeUnitNetwork_exec_replicate
    {s : Nat}
    (st : MicroState Q) (m k : Nat)
    (hk : k <= maxTape s - m) :
    (transferTapeBarToTapeUnitNetwork st st).Exec
      (enc ({ state := st, tape := m } : MicroCfg Q s))
      (enc ({ state := st, tape := m + k } : MicroCfg Q s))
      (List.replicate k Network.OneRxnIdx.step) := by
  induction k generalizing m with
  | zero =>
      simp
  | succ k ih =>
      have hpos : 1 <= maxTape s - m := by omega
      have hk' : k <= maxTape s - (m + 1) := by omega
      have htarget : m + 1 + k = m + Nat.succ k := by omega
      have hfirst :
          (transferTapeBarToTapeUnitNetwork st st).Exec
            (enc ({ state := st, tape := m } : MicroCfg Q s))
            (enc ({ state := st, tape := m + 1 } : MicroCfg Q s))
            [Network.OneRxnIdx.step] :=
        transferTapeBarToTapeUnitNetwork_exec
          (s := s) st st m hpos
      have htail :
          (transferTapeBarToTapeUnitNetwork st st).Exec
            (enc ({ state := st, tape := m + 1 } : MicroCfg Q s))
            (enc ({ state := st, tape := m + Nat.succ k } :
              MicroCfg Q s))
            (List.replicate k Network.OneRxnIdx.step) := by
        simpa [htarget] using ih (m + 1) hk'
      simpa [List.replicate_succ] using
        (ExecOf.append hfirst htail)

def transferTapeBarToTapeUnitNetwork_boundedIntendedSchedule_replicate
    {s : Nat}
    (st : MicroState Q) (m k : Nat)
    (hk : k <= maxTape s - m) :
    (transferTapeBarToTapeUnitNetwork st st).BoundedIntendedSchedule k
      (enc ({ state := st, tape := m } : MicroCfg Q s))
      (enc ({ state := st, tape := m + k } : MicroCfg Q s)) where
  schedule := List.replicate k Network.OneRxnIdx.step
  exec :=
    transferTapeBarToTapeUnitNetwork_exec_replicate
      (s := s) st m k hk
  length_bound := by simp

@[simp]
theorem transferTapeBarToTapeUnitNetwork_boundedIntendedSchedule_replicate_schedule
    {s : Nat}
    (st : MicroState Q) (m k : Nat)
    (hk : k <= maxTape s - m) :
    (transferTapeBarToTapeUnitNetwork_boundedIntendedSchedule_replicate
      (s := s) st m k hk).schedule =
        List.replicate k Network.OneRxnIdx.step := by
  rfl

@[simp]
theorem transferTapeBarToTapeUnitNetwork_boundedIntendedSchedule_replicate_firingCount
    {s : Nat}
    (st : MicroState Q) (m k : Nat)
    (hk : k <= maxTape s - m) :
    (transferTapeBarToTapeUnitNetwork_boundedIntendedSchedule_replicate
      (s := s) st m k hk).firingCount = k := by
  change (List.replicate k Network.OneRxnIdx.step).length = k
  exact List.length_replicate

theorem tapeTransferUnitNetwork_exec_toTapeBar_replicate
    {s : Nat}
    (st : MicroState Q) (m k : Nat)
    (hm : m <= maxTape s)
    (hk : k <= m) :
    (tapeTransferUnitNetwork st).Exec
      (enc ({ state := st, tape := m } : MicroCfg Q s))
      (enc ({ state := st, tape := m - k } : MicroCfg Q s))
      ((List.replicate k Network.OneRxnIdx.step).map Sum.inl) := by
  exact Network.parallel_exec_inl
    (transferTapeToTapeBarUnitNetwork st st)
    (transferTapeBarToTapeUnitNetwork st st)
    (transferTapeToTapeBarUnitNetwork_exec_replicate
      (s := s) st m k hm hk)

def tapeTransferUnitNetwork_boundedIntendedSchedule_toTapeBar_replicate
    {s : Nat}
    (st : MicroState Q) (m k : Nat)
    (hm : m <= maxTape s)
    (hk : k <= m) :
    (tapeTransferUnitNetwork st).BoundedIntendedSchedule k
      (enc ({ state := st, tape := m } : MicroCfg Q s))
      (enc ({ state := st, tape := m - k } : MicroCfg Q s)) where
  schedule := (List.replicate k Network.OneRxnIdx.step).map Sum.inl
  exec :=
    tapeTransferUnitNetwork_exec_toTapeBar_replicate
      (s := s) st m k hm hk
  length_bound := by
    rw [List.length_map]
    exact le_of_eq List.length_replicate

@[simp]
theorem tapeTransferUnitNetwork_boundedIntendedSchedule_toTapeBar_replicate_schedule
    {s : Nat}
    (st : MicroState Q) (m k : Nat)
    (hm : m <= maxTape s)
    (hk : k <= m) :
    (tapeTransferUnitNetwork_boundedIntendedSchedule_toTapeBar_replicate
      (s := s) st m k hm hk).schedule =
        (List.replicate k Network.OneRxnIdx.step).map Sum.inl := by
  rfl

@[simp]
theorem tapeTransferUnitNetwork_boundedIntendedSchedule_toTapeBar_replicate_firingCount
    {s : Nat}
    (st : MicroState Q) (m k : Nat)
    (hm : m <= maxTape s)
    (hk : k <= m) :
    (tapeTransferUnitNetwork_boundedIntendedSchedule_toTapeBar_replicate
      (s := s) st m k hm hk).firingCount = k := by
  unfold Network.BoundedIntendedSchedule.firingCount
  rw [
    tapeTransferUnitNetwork_boundedIntendedSchedule_toTapeBar_replicate_schedule
  ]
  rw [List.map_replicate]
  exact List.length_replicate

theorem tapeTransferUnitNetwork_exec_toTape_replicate
    {s : Nat}
    (st : MicroState Q) (m k : Nat)
    (hk : k <= maxTape s - m) :
    (tapeTransferUnitNetwork st).Exec
      (enc ({ state := st, tape := m } : MicroCfg Q s))
      (enc ({ state := st, tape := m + k } : MicroCfg Q s))
      ((List.replicate k Network.OneRxnIdx.step).map Sum.inr) := by
  exact Network.parallel_exec_inr
    (transferTapeToTapeBarUnitNetwork st st)
    (transferTapeBarToTapeUnitNetwork st st)
    (transferTapeBarToTapeUnitNetwork_exec_replicate
      (s := s) st m k hk)

def tapeTransferUnitNetwork_boundedIntendedSchedule_toTape_replicate
    {s : Nat}
    (st : MicroState Q) (m k : Nat)
    (hk : k <= maxTape s - m) :
    (tapeTransferUnitNetwork st).BoundedIntendedSchedule k
      (enc ({ state := st, tape := m } : MicroCfg Q s))
      (enc ({ state := st, tape := m + k } : MicroCfg Q s)) where
  schedule := (List.replicate k Network.OneRxnIdx.step).map Sum.inr
  exec :=
    tapeTransferUnitNetwork_exec_toTape_replicate
      (s := s) st m k hk
  length_bound := by
    rw [List.length_map]
    exact le_of_eq List.length_replicate

@[simp]
theorem tapeTransferUnitNetwork_boundedIntendedSchedule_toTape_replicate_schedule
    {s : Nat}
    (st : MicroState Q) (m k : Nat)
    (hk : k <= maxTape s - m) :
    (tapeTransferUnitNetwork_boundedIntendedSchedule_toTape_replicate
      (s := s) st m k hk).schedule =
        (List.replicate k Network.OneRxnIdx.step).map Sum.inr := by
  rfl

@[simp]
theorem tapeTransferUnitNetwork_boundedIntendedSchedule_toTape_replicate_firingCount
    {s : Nat}
    (st : MicroState Q) (m k : Nat)
    (hk : k <= maxTape s - m) :
    (tapeTransferUnitNetwork_boundedIntendedSchedule_toTape_replicate
      (s := s) st m k hk).firingCount = k := by
  unfold Network.BoundedIntendedSchedule.firingCount
  rw [
    tapeTransferUnitNetwork_boundedIntendedSchedule_toTape_replicate_schedule
  ]
  rw [List.map_replicate]
  exact List.length_replicate

theorem tapeTransferWithControlNetwork_exec_toTapeBar
    {s : Nat}
    (st st' : MicroState Q) (m k : Nat)
    (hm : m <= maxTape s)
    (hk : k <= m) :
    (tapeTransferWithControlNetwork st st').Exec
      (enc ({ state := st, tape := m } : MicroCfg Q s))
      (enc ({ state := st', tape := m - k } : MicroCfg Q s))
      (tapeTransferWithControlToTapeBarSchedule st st' k) := by
  change
    ((tapeTransferUnitNetwork st).parallel
      (controlSwapNetwork st st')).Exec
      (enc ({ state := st, tape := m } : MicroCfg Q s))
      (enc ({ state := st', tape := m - k } : MicroCfg Q s))
      (((List.replicate k Network.OneRxnIdx.step).map Sum.inl).map
        Sum.inl ++ [Network.OneRxnIdx.step].map Sum.inr)
  exact
    Network.parallel_exec_inl_append_inr
      (tapeTransferUnitNetwork st)
      (controlSwapNetwork st st')
      (tapeTransferUnitNetwork_exec_toTapeBar_replicate
        (s := s) st m k hm hk)
      (controlSwapNetwork_exec (s := s) st st' (m - k))

def tapeTransferWithControlNetwork_boundedIntendedSchedule_toTapeBar
    {s : Nat}
    (st st' : MicroState Q) (m k : Nat)
    (hm : m <= maxTape s)
    (hk : k <= m) :
    (tapeTransferWithControlNetwork st st').BoundedIntendedSchedule
      (k + 1)
      (enc ({ state := st, tape := m } : MicroCfg Q s))
      (enc ({ state := st', tape := m - k } : MicroCfg Q s)) where
  schedule := tapeTransferWithControlToTapeBarSchedule st st' k
  exec :=
    tapeTransferWithControlNetwork_exec_toTapeBar
      (s := s) st st' m k hm hk
  length_bound := by simp

@[simp]
theorem tapeTransferWithControlNetwork_boundedIntendedSchedule_toTapeBar_schedule
    {s : Nat}
    (st st' : MicroState Q) (m k : Nat)
    (hm : m <= maxTape s)
    (hk : k <= m) :
    (tapeTransferWithControlNetwork_boundedIntendedSchedule_toTapeBar
      (s := s) st st' m k hm hk).schedule =
        tapeTransferWithControlToTapeBarSchedule st st' k := by
  rfl

@[simp]
theorem tapeTransferWithControlNetwork_boundedIntendedSchedule_toTapeBar_firingCount
    {s : Nat}
    (st st' : MicroState Q) (m k : Nat)
    (hm : m <= maxTape s)
    (hk : k <= m) :
    (tapeTransferWithControlNetwork_boundedIntendedSchedule_toTapeBar
      (s := s) st st' m k hm hk).firingCount = k + 1 := by
  unfold Network.BoundedIntendedSchedule.firingCount
  rw [
    tapeTransferWithControlNetwork_boundedIntendedSchedule_toTapeBar_schedule
  ]
  exact tapeTransferWithControlToTapeBarSchedule_length st st' k

theorem tapeTransferWithControlNetwork_exec_toTape
    {s : Nat}
    (st st' : MicroState Q) (m k : Nat)
    (hk : k <= maxTape s - m) :
    (tapeTransferWithControlNetwork st st').Exec
      (enc ({ state := st, tape := m } : MicroCfg Q s))
      (enc ({ state := st', tape := m + k } : MicroCfg Q s))
      (tapeTransferWithControlToTapeSchedule st st' k) := by
  change
    ((tapeTransferUnitNetwork st).parallel
      (controlSwapNetwork st st')).Exec
      (enc ({ state := st, tape := m } : MicroCfg Q s))
      (enc ({ state := st', tape := m + k } : MicroCfg Q s))
      (((List.replicate k Network.OneRxnIdx.step).map Sum.inr).map
        Sum.inl ++ [Network.OneRxnIdx.step].map Sum.inr)
  exact
    Network.parallel_exec_inl_append_inr
      (tapeTransferUnitNetwork st)
      (controlSwapNetwork st st')
      (tapeTransferUnitNetwork_exec_toTape_replicate
        (s := s) st m k hk)
      (controlSwapNetwork_exec (s := s) st st' (m + k))

def tapeTransferWithControlNetwork_boundedIntendedSchedule_toTape
    {s : Nat}
    (st st' : MicroState Q) (m k : Nat)
    (hk : k <= maxTape s - m) :
    (tapeTransferWithControlNetwork st st').BoundedIntendedSchedule
      (k + 1)
      (enc ({ state := st, tape := m } : MicroCfg Q s))
      (enc ({ state := st', tape := m + k } : MicroCfg Q s)) where
  schedule := tapeTransferWithControlToTapeSchedule st st' k
  exec :=
    tapeTransferWithControlNetwork_exec_toTape
      (s := s) st st' m k hk
  length_bound := by simp

@[simp]
theorem tapeTransferWithControlNetwork_boundedIntendedSchedule_toTape_schedule
    {s : Nat}
    (st st' : MicroState Q) (m k : Nat)
    (hk : k <= maxTape s - m) :
    (tapeTransferWithControlNetwork_boundedIntendedSchedule_toTape
      (s := s) st st' m k hk).schedule =
        tapeTransferWithControlToTapeSchedule st st' k := by
  rfl

@[simp]
theorem tapeTransferWithControlNetwork_boundedIntendedSchedule_toTape_firingCount
    {s : Nat}
    (st st' : MicroState Q) (m k : Nat)
    (hk : k <= maxTape s - m) :
    (tapeTransferWithControlNetwork_boundedIntendedSchedule_toTape
      (s := s) st st' m k hk).firingCount = k + 1 := by
  unfold Network.BoundedIntendedSchedule.firingCount
  rw [
    tapeTransferWithControlNetwork_boundedIntendedSchedule_toTape_schedule
  ]
  exact tapeTransferWithControlToTapeSchedule_length st st' k

theorem tapeTransferWithControlNetwork_exec_eraseMSBWith
    {s : Nat}
    (st st' : MicroState Q) (m : Nat) (r : Bool)
    (hm : m <= maxTape s)
    (hk : Encoding.bitDigit r * 3 ^ s <= m) :
    (tapeTransferWithControlNetwork st st').Exec
      (enc ({ state := st, tape := m } : MicroCfg Q s))
      (enc ({ state := st',
              tape := Encoding.eraseMSBWith s r m } : MicroCfg Q s))
      (tapeTransferWithControlToTapeBarSchedule
        st st' (Encoding.bitDigit r * 3 ^ s)) := by
  simpa [Encoding.eraseMSBWith] using
    tapeTransferWithControlNetwork_exec_toTapeBar
      (s := s) st st' m (Encoding.bitDigit r * 3 ^ s) hm hk

def tapeTransferWithControlNetwork_boundedIntendedSchedule_eraseMSBWith
    {s : Nat}
    (st st' : MicroState Q) (m : Nat) (r : Bool)
    (hm : m <= maxTape s)
    (hk : Encoding.bitDigit r * 3 ^ s <= m) :
    (tapeTransferWithControlNetwork st st').BoundedIntendedSchedule
      (Encoding.bitDigit r * 3 ^ s + 1)
      (enc ({ state := st, tape := m } : MicroCfg Q s))
      (enc ({ state := st',
              tape := Encoding.eraseMSBWith s r m } : MicroCfg Q s)) where
  schedule :=
    tapeTransferWithControlToTapeBarSchedule
      st st' (Encoding.bitDigit r * 3 ^ s)
  exec :=
    tapeTransferWithControlNetwork_exec_eraseMSBWith
      (s := s) st st' m r hm hk
  length_bound := by simp

@[simp]
theorem tapeTransferWithControlNetwork_boundedIntendedSchedule_eraseMSBWith_schedule
    {s : Nat}
    (st st' : MicroState Q) (m : Nat) (r : Bool)
    (hm : m <= maxTape s)
    (hk : Encoding.bitDigit r * 3 ^ s <= m) :
    (tapeTransferWithControlNetwork_boundedIntendedSchedule_eraseMSBWith
      (s := s) st st' m r hm hk).schedule =
        tapeTransferWithControlToTapeBarSchedule
          st st' (Encoding.bitDigit r * 3 ^ s) := by
  rfl

@[simp]
theorem tapeTransferWithControlNetwork_boundedIntendedSchedule_eraseMSBWith_firingCount
    {s : Nat}
    (st st' : MicroState Q) (m : Nat) (r : Bool)
    (hm : m <= maxTape s)
    (hk : Encoding.bitDigit r * 3 ^ s <= m) :
    (tapeTransferWithControlNetwork_boundedIntendedSchedule_eraseMSBWith
      (s := s) st st' m r hm hk).firingCount =
        Encoding.bitDigit r * 3 ^ s + 1 := by
  unfold Network.BoundedIntendedSchedule.firingCount
  rw [
    tapeTransferWithControlNetwork_boundedIntendedSchedule_eraseMSBWith_schedule
  ]
  exact tapeTransferWithControlToTapeBarSchedule_length
    st st' (Encoding.bitDigit r * 3 ^ s)

theorem tapeTransferWithControlNetwork_exec_writeLSB
    {s : Nat}
    (st st' : MicroState Q) (m : Nat) (b : Bool)
    (hk : Encoding.bitDigit b <= maxTape s - m) :
    (tapeTransferWithControlNetwork st st').Exec
      (enc ({ state := st, tape := m } : MicroCfg Q s))
      (enc ({ state := st',
              tape := Encoding.writeLSB m b } : MicroCfg Q s))
      (tapeTransferWithControlToTapeSchedule
        st st' (Encoding.bitDigit b)) := by
  simpa [Encoding.writeLSB] using
    tapeTransferWithControlNetwork_exec_toTape
      (s := s) st st' m (Encoding.bitDigit b) hk

def tapeTransferWithControlNetwork_boundedIntendedSchedule_writeLSB
    {s : Nat}
    (st st' : MicroState Q) (m : Nat) (b : Bool)
    (hk : Encoding.bitDigit b <= maxTape s - m) :
    (tapeTransferWithControlNetwork st st').BoundedIntendedSchedule
      (Encoding.bitDigit b + 1)
      (enc ({ state := st, tape := m } : MicroCfg Q s))
      (enc ({ state := st',
              tape := Encoding.writeLSB m b } : MicroCfg Q s)) where
  schedule :=
    tapeTransferWithControlToTapeSchedule st st' (Encoding.bitDigit b)
  exec :=
    tapeTransferWithControlNetwork_exec_writeLSB
      (s := s) st st' m b hk
  length_bound := by simp

@[simp]
theorem tapeTransferWithControlNetwork_boundedIntendedSchedule_writeLSB_schedule
    {s : Nat}
    (st st' : MicroState Q) (m : Nat) (b : Bool)
    (hk : Encoding.bitDigit b <= maxTape s - m) :
    (tapeTransferWithControlNetwork_boundedIntendedSchedule_writeLSB
      (s := s) st st' m b hk).schedule =
        tapeTransferWithControlToTapeSchedule st st' (Encoding.bitDigit b) := by
  rfl

@[simp]
theorem tapeTransferWithControlNetwork_boundedIntendedSchedule_writeLSB_firingCount
    {s : Nat}
    (st st' : MicroState Q) (m : Nat) (b : Bool)
    (hk : Encoding.bitDigit b <= maxTape s - m) :
    (tapeTransferWithControlNetwork_boundedIntendedSchedule_writeLSB
      (s := s) st st' m b hk).firingCount =
        Encoding.bitDigit b + 1 := by
  unfold Network.BoundedIntendedSchedule.firingCount
  rw [
    tapeTransferWithControlNetwork_boundedIntendedSchedule_writeLSB_schedule
  ]
  exact tapeTransferWithControlToTapeSchedule_length
    st st' (Encoding.bitDigit b)

theorem tapeTransferWithControlNetwork_exec_shiftTail
    {s : Nat}
    (st st' : MicroState Q) (m : Nat)
    (hTape : Encoding.IsBase3BoolTape s m) :
    (tapeTransferWithControlNetwork st st').Exec
      (enc ({ state := st, tape := m } : MicroCfg Q s))
      (enc ({ state := st',
              tape := Encoding.shiftTail m } : MicroCfg Q s))
      (tapeTransferWithControlToTapeSchedule st st' (2 * m)) := by
  have hk : 2 * m <= maxTape s - m :=
    two_mul_le_tapeBar_of_lt_pow hTape.lt_pow
  have hshift : m + 2 * m = Encoding.shiftTail m := by
    unfold Encoding.shiftTail
    omega
  simpa [hshift] using
    tapeTransferWithControlNetwork_exec_toTape
      (s := s) st st' m (2 * m) hk

def tapeTransferWithControlNetwork_boundedIntendedSchedule_shiftTail
    {s : Nat}
    (st st' : MicroState Q) (m : Nat)
    (hTape : Encoding.IsBase3BoolTape s m) :
    (tapeTransferWithControlNetwork st st').BoundedIntendedSchedule
      (2 * m + 1)
      (enc ({ state := st, tape := m } : MicroCfg Q s))
      (enc ({ state := st',
              tape := Encoding.shiftTail m } : MicroCfg Q s)) where
  schedule := tapeTransferWithControlToTapeSchedule st st' (2 * m)
  exec :=
    tapeTransferWithControlNetwork_exec_shiftTail
      (s := s) st st' m hTape
  length_bound := by simp

@[simp]
theorem tapeTransferWithControlNetwork_boundedIntendedSchedule_shiftTail_schedule
    {s : Nat}
    (st st' : MicroState Q) (m : Nat)
    (hTape : Encoding.IsBase3BoolTape s m) :
    (tapeTransferWithControlNetwork_boundedIntendedSchedule_shiftTail
      (s := s) st st' m hTape).schedule =
        tapeTransferWithControlToTapeSchedule st st' (2 * m) := by
  rfl

@[simp]
theorem tapeTransferWithControlNetwork_boundedIntendedSchedule_shiftTail_firingCount
    {s : Nat}
    (st st' : MicroState Q) (m : Nat)
    (hTape : Encoding.IsBase3BoolTape s m) :
    (tapeTransferWithControlNetwork_boundedIntendedSchedule_shiftTail
      (s := s) st st' m hTape).firingCount = 2 * m + 1 := by
  unfold Network.BoundedIntendedSchedule.firingCount
  rw [
    tapeTransferWithControlNetwork_boundedIntendedSchedule_shiftTail_schedule
  ]
  exact tapeTransferWithControlToTapeSchedule_length st st' (2 * m)

def aggregateNetwork
    (st st' : MicroState Q)
    (tapeIn tapeBarIn tapeOut tapeBarOut : Nat) :
    Network (Species Q) :=
  Network.oneRxnNetwork
    (aggregateReaction st st' tapeIn tapeBarIn tapeOut tapeBarOut)

theorem fullAggregateNetwork_eq_aggregateNetwork {s : Nat}
    (c c' : MicroCfg Q s) :
    fullAggregateNetwork c c' =
      aggregateNetwork c.state c'.state
        c.tape (maxTape s - c.tape)
        c'.tape (maxTape s - c'.tape) := by
  rfl

@[simp]
theorem aggregateNetwork_rxn_step
    (st st' : MicroState Q)
    (tapeIn tapeBarIn tapeOut tapeBarOut : Nat) :
    (aggregateNetwork st st' tapeIn tapeBarIn tapeOut tapeBarOut).rxn
        Network.OneRxnIdx.step =
      aggregateReaction st st' tapeIn tapeBarIn tapeOut tapeBarOut := by
  rfl

theorem aggregateNetwork_allUnitRate
    (st st' : MicroState Q)
    (tapeIn tapeBarIn tapeOut tapeBarOut : Nat) :
    (aggregateNetwork st st'
      tapeIn tapeBarIn tapeOut tapeBarOut).allUnitRate :=
  (Network.oneRxnNetwork_allUnitRate_iff
    (aggregateReaction st st'
      tapeIn tapeBarIn tapeOut tapeBarOut)).2 rfl

theorem aggregateNetwork_hasPositiveRates
    (st st' : MicroState Q)
    (tapeIn tapeBarIn tapeOut tapeBarOut : Nat) :
    (aggregateNetwork st st'
      tapeIn tapeBarIn tapeOut tapeBarOut).hasPositiveRates :=
  Network.hasPositiveRates_of_allUnitRate
    (aggregateNetwork_allUnitRate st st'
      tapeIn tapeBarIn tapeOut tapeBarOut)

theorem aggregateNetwork_equalRates
    (st st' : MicroState Q)
    (tapeIn tapeBarIn tapeOut tapeBarOut : Nat) :
    (aggregateNetwork st st'
      tapeIn tapeBarIn tapeOut tapeBarOut).equalRates :=
  Network.oneRxnNetwork_equalRates
    (aggregateReaction st st'
      tapeIn tapeBarIn tapeOut tapeBarOut)

theorem aggregateNetwork_allAtMostBimolecularInput_iff
    [Fintype Q]
    (st st' : MicroState Q)
    (tapeIn tapeBarIn tapeOut tapeBarOut : Nat) :
    (aggregateNetwork st st'
      tapeIn tapeBarIn tapeOut tapeBarOut).allAtMostBimolecularInput <->
      1 + tapeIn + tapeBarIn <= 2 := by
  simpa [aggregateNetwork, Reaction.isAtMostBimolecularInput] using
    (Network.oneRxnNetwork_allAtMostBimolecularInput_iff
      (aggregateReaction st st'
        tapeIn tapeBarIn tapeOut tapeBarOut))

theorem aggregateNetwork_allAtMostBimolecularOutput_iff
    [Fintype Q]
    (st st' : MicroState Q)
    (tapeIn tapeBarIn tapeOut tapeBarOut : Nat) :
    (aggregateNetwork st st'
      tapeIn tapeBarIn tapeOut tapeBarOut).allAtMostBimolecularOutput <->
      1 + tapeOut + tapeBarOut <= 2 := by
  simpa [aggregateNetwork, Reaction.isAtMostBimolecularOutput] using
    (Network.oneRxnNetwork_allAtMostBimolecularOutput_iff
      (aggregateReaction st st'
        tapeIn tapeBarIn tapeOut tapeBarOut))

theorem aggregateNetwork_allAtMostBimolecularFull_iff
    [Fintype Q]
    (st st' : MicroState Q)
    (tapeIn tapeBarIn tapeOut tapeBarOut : Nat) :
    (aggregateNetwork st st'
      tapeIn tapeBarIn tapeOut tapeBarOut).allAtMostBimolecularFull <->
      1 + tapeIn + tapeBarIn <= 2 /\
        1 + tapeOut + tapeBarOut <= 2 := by
  constructor
  · intro h
    exact ⟨
      (aggregateNetwork_allAtMostBimolecularInput_iff
        st st' tapeIn tapeBarIn tapeOut tapeBarOut).1
        (Network.allAtMostBimolecularInput_of_full h),
      (aggregateNetwork_allAtMostBimolecularOutput_iff
        st st' tapeIn tapeBarIn tapeOut tapeBarOut).1
        (Network.allAtMostBimolecularOutput_of_full h)
    ⟩
  · rintro ⟨hin, hout⟩
    exact (Network.allAtMostBimolecularFull_iff
      (aggregateNetwork st st'
        tapeIn tapeBarIn tapeOut tapeBarOut)).2
      ⟨
        (aggregateNetwork_allAtMostBimolecularInput_iff
          st st' tapeIn tapeBarIn tapeOut tapeBarOut).2 hin,
        (aggregateNetwork_allAtMostBimolecularOutput_iff
          st st' tapeIn tapeBarIn tapeOut tapeBarOut).2 hout
      ⟩

theorem aggregateNetwork_not_allAtMostBimolecularInput_of_two_lt
    [Fintype Q]
    (st st' : MicroState Q)
    (tapeIn tapeBarIn tapeOut tapeBarOut : Nat)
    (hLarge : 2 < 1 + tapeIn + tapeBarIn) :
    Not
      ((aggregateNetwork st st'
        tapeIn tapeBarIn tapeOut tapeBarOut).allAtMostBimolecularInput) := by
  intro h
  have hle :
      1 + tapeIn + tapeBarIn <= 2 :=
    (aggregateNetwork_allAtMostBimolecularInput_iff
      st st' tapeIn tapeBarIn tapeOut tapeBarOut).1 h
  exact not_lt_of_ge hle hLarge

theorem aggregateNetwork_exec
    {s : Nat}
    (st st' : MicroState Q)
    (m m' tapeIn tapeBarIn tapeOut tapeBarOut : Nat)
    (hTape : tapeIn <= m)
    (hTapeBar : tapeBarIn <= maxTape s - m)
    (hTapeEq : m - tapeIn + tapeOut = m')
    (hTapeBarEq :
      (maxTape s - m) - tapeBarIn + tapeBarOut = maxTape s - m') :
    (aggregateNetwork st st' tapeIn tapeBarIn tapeOut tapeBarOut).Exec
      (enc ({ state := st, tape := m } : MicroCfg Q s))
      (enc ({ state := st', tape := m' } : MicroCfg Q s))
      [Network.OneRxnIdx.step] :=
  Network.oneRxn_exec
    (aggregateReaction_firesTo
      (s := s) st st' m m'
      tapeIn tapeBarIn tapeOut tapeBarOut
      hTape hTapeBar hTapeEq hTapeBarEq)

theorem aggregateNetwork_exec_iff
    {s : Nat}
    (st st' : MicroState Q)
    (m m' tapeIn tapeBarIn tapeOut tapeBarOut : Nat)
    (hTape : tapeIn <= m)
    (hTapeBar : tapeBarIn <= maxTape s - m)
    (hTapeEq : m - tapeIn + tapeOut = m')
    (hTapeBarEq :
      (maxTape s - m) - tapeBarIn + tapeBarOut = maxTape s - m')
    (z' : State (Species Q)) :
    (aggregateNetwork st st' tapeIn tapeBarIn tapeOut tapeBarOut).Exec
      (enc ({ state := st, tape := m } : MicroCfg Q s))
      z'
      [Network.OneRxnIdx.step] <->
        z' = enc ({ state := st', tape := m' } : MicroCfg Q s) := by
  constructor
  · intro hExec
    have hFire :
        (aggregateReaction st st'
          tapeIn tapeBarIn tapeOut tapeBarOut).FiresTo
          (enc ({ state := st, tape := m } : MicroCfg Q s))
          z' := by
      exact
        (Network.oneRxnNetwork_exec_iff
          (rho :=
            aggregateReaction st st'
              tapeIn tapeBarIn tapeOut tapeBarOut)
          (z := enc ({ state := st, tape := m } : MicroCfg Q s))
          (z' := z')).1
          (by simpa [aggregateNetwork] using hExec)
    exact
      (aggregateReaction_firesTo_iff
        (s := s) st st' m m'
        tapeIn tapeBarIn tapeOut tapeBarOut
        hTape hTapeBar hTapeEq hTapeBarEq z').1 hFire
  · intro hz
    rw [hz]
    exact aggregateNetwork_exec
      (s := s) st st' m m'
      tapeIn tapeBarIn tapeOut tapeBarOut
      hTape hTapeBar hTapeEq hTapeBarEq

theorem aggregateNetwork_reaches
    {s : Nat}
    (st st' : MicroState Q)
    (m m' tapeIn tapeBarIn tapeOut tapeBarOut : Nat)
    (hTape : tapeIn <= m)
    (hTapeBar : tapeBarIn <= maxTape s - m)
    (hTapeEq : m - tapeIn + tapeOut = m')
    (hTapeBarEq :
      (maxTape s - m) - tapeBarIn + tapeBarOut = maxTape s - m') :
    (aggregateNetwork st st' tapeIn tapeBarIn tapeOut tapeBarOut).Reaches
      (enc ({ state := st, tape := m } : MicroCfg Q s))
      (enc ({ state := st', tape := m' } : MicroCfg Q s)) :=
  Network.reaches_of_exec
    (aggregateNetwork_exec
      (s := s) st st' m m'
      tapeIn tapeBarIn tapeOut tapeBarOut
      hTape hTapeBar hTapeEq hTapeBarEq)

theorem aggregateNetwork_coverable_of_covers
    {s : Nat}
    (st st' : MicroState Q)
    (m m' tapeIn tapeBarIn tapeOut tapeBarOut : Nat)
    (hTape : tapeIn <= m)
    (hTapeBar : tapeBarIn <= maxTape s - m)
    (hTapeEq : m - tapeIn + tapeOut = m')
    (hTapeBarEq :
      (maxTape s - m) - tapeBarIn + tapeBarOut = maxTape s - m')
    {target : State (Species Q)}
    (hCovers :
      Covers
        (enc ({ state := st', tape := m' } : MicroCfg Q s))
        target) :
    (aggregateNetwork st st' tapeIn tapeBarIn tapeOut tapeBarOut).CoverableFrom
      (enc ({ state := st, tape := m } : MicroCfg Q s))
      target :=
  Network.coverable_of_reaches_of_covers
    (aggregateNetwork_reaches
      (s := s) st st' m m'
      tapeIn tapeBarIn tapeOut tapeBarOut
      hTape hTapeBar hTapeEq hTapeBarEq)
    hCovers

theorem aggregateNetwork_coverable_of_le
    {s : Nat}
    (st st' : MicroState Q)
    (m m' tapeIn tapeBarIn tapeOut tapeBarOut : Nat)
    (hTape : tapeIn <= m)
    (hTapeBar : tapeBarIn <= maxTape s - m)
    (hTapeEq : m - tapeIn + tapeOut = m')
    (hTapeBarEq :
      (maxTape s - m) - tapeBarIn + tapeBarOut = maxTape s - m')
    {target : State (Species Q)}
    (hTarget :
      forall species,
        target species <=
          enc ({ state := st', tape := m' } : MicroCfg Q s) species) :
    (aggregateNetwork st st' tapeIn tapeBarIn tapeOut tapeBarOut).CoverableFrom
      (enc ({ state := st, tape := m } : MicroCfg Q s))
      target :=
  aggregateNetwork_coverable_of_covers
    (s := s) st st' m m'
    tapeIn tapeBarIn tapeOut tapeBarOut
    hTape hTapeBar hTapeEq hTapeBarEq hTarget

theorem aggregateNetwork_speciesCoverableFrom_coord
    {s : Nat}
    (st st' : MicroState Q)
    (m m' tapeIn tapeBarIn tapeOut tapeBarOut : Nat)
    (hTape : tapeIn <= m)
    (hTapeBar : tapeBarIn <= maxTape s - m)
    (hTapeEq : m - tapeIn + tapeOut = m')
    (hTapeBarEq :
      (maxTape s - m) - tapeBarIn + tapeBarOut = maxTape s - m')
    {species : Species Q} {amount : Nat}
    (hamount :
      amount <=
        enc ({ state := st', tape := m' } : MicroCfg Q s) species) :
    (aggregateNetwork st st' tapeIn tapeBarIn tapeOut tapeBarOut).SpeciesCoverableFrom
        (enc ({ state := st, tape := m } : MicroCfg Q s))
        species amount :=
  Network.speciesCoverableFrom_of_reaches_coord
    (aggregateNetwork_reaches
      (s := s) st st' m m'
      tapeIn tapeBarIn tapeOut tapeBarOut
      hTape hTapeBar hTapeEq hTapeBarEq)
    hamount

theorem aggregateNetwork_speciesCoverableFrom_one_of_pos
    {s : Nat}
    (st st' : MicroState Q)
    (m m' tapeIn tapeBarIn tapeOut tapeBarOut : Nat)
    (hTape : tapeIn <= m)
    (hTapeBar : tapeBarIn <= maxTape s - m)
    (hTapeEq : m - tapeIn + tapeOut = m')
    (hTapeBarEq :
      (maxTape s - m) - tapeBarIn + tapeBarOut = maxTape s - m')
    {species : Species Q}
    (hpos :
      0 <
        enc ({ state := st', tape := m' } : MicroCfg Q s) species) :
    (aggregateNetwork st st' tapeIn tapeBarIn tapeOut tapeBarOut).SpeciesCoverableFrom
        (enc ({ state := st, tape := m } : MicroCfg Q s))
        species :=
  Network.speciesCoverableFrom_one_of_reaches_pos
    (aggregateNetwork_reaches
      (s := s) st st' m m'
      tapeIn tapeBarIn tapeOut tapeBarOut
      hTape hTapeBar hTapeEq hTapeBarEq)
    hpos

def aggregateNetwork_intendedSchedule
    {s : Nat}
    (st st' : MicroState Q)
    (m m' tapeIn tapeBarIn tapeOut tapeBarOut : Nat)
    (hTape : tapeIn <= m)
    (hTapeBar : tapeBarIn <= maxTape s - m)
    (hTapeEq : m - tapeIn + tapeOut = m')
    (hTapeBarEq :
      (maxTape s - m) - tapeBarIn + tapeBarOut = maxTape s - m') :
    Network.IntendedSchedule
      (aggregateNetwork st st' tapeIn tapeBarIn tapeOut tapeBarOut)
        (enc ({ state := st, tape := m } : MicroCfg Q s))
        (enc ({ state := st', tape := m' } : MicroCfg Q s)) :=
  Network.oneRxnNetwork_intendedSchedule
    (aggregateReaction_firesTo
      (s := s) st st' m m'
      tapeIn tapeBarIn tapeOut tapeBarOut
      hTape hTapeBar hTapeEq hTapeBarEq)

@[simp]
theorem aggregateNetwork_intendedSchedule_schedule
    {s : Nat}
    (st st' : MicroState Q)
    (m m' tapeIn tapeBarIn tapeOut tapeBarOut : Nat)
    (hTape : tapeIn <= m)
    (hTapeBar : tapeBarIn <= maxTape s - m)
    (hTapeEq : m - tapeIn + tapeOut = m')
    (hTapeBarEq :
      (maxTape s - m) - tapeBarIn + tapeBarOut = maxTape s - m') :
    (aggregateNetwork_intendedSchedule
      (s := s) st st' m m'
      tapeIn tapeBarIn tapeOut tapeBarOut
      hTape hTapeBar hTapeEq hTapeBarEq).schedule =
        [Network.OneRxnIdx.step] := by
  rfl

@[simp]
theorem aggregateNetwork_intendedSchedule_firingCount
    {s : Nat}
    (st st' : MicroState Q)
    (m m' tapeIn tapeBarIn tapeOut tapeBarOut : Nat)
    (hTape : tapeIn <= m)
    (hTapeBar : tapeBarIn <= maxTape s - m)
    (hTapeEq : m - tapeIn + tapeOut = m')
    (hTapeBarEq :
      (maxTape s - m) - tapeBarIn + tapeBarOut = maxTape s - m') :
    (aggregateNetwork_intendedSchedule
      (s := s) st st' m m'
      tapeIn tapeBarIn tapeOut tapeBarOut
      hTape hTapeBar hTapeEq hTapeBarEq).firingCount = 1 := by
  rfl

def aggregateNetwork_boundedIntendedSchedule
    {s : Nat}
    (st st' : MicroState Q)
    (m m' tapeIn tapeBarIn tapeOut tapeBarOut : Nat)
    (hTape : tapeIn <= m)
    (hTapeBar : tapeBarIn <= maxTape s - m)
    (hTapeEq : m - tapeIn + tapeOut = m')
    (hTapeBarEq :
      (maxTape s - m) - tapeBarIn + tapeBarOut = maxTape s - m') :
    Network.BoundedIntendedSchedule
      (aggregateNetwork st st' tapeIn tapeBarIn tapeOut tapeBarOut) 1
        (enc ({ state := st, tape := m } : MicroCfg Q s))
        (enc ({ state := st', tape := m' } : MicroCfg Q s)) :=
  Network.oneRxnNetwork_boundedIntendedSchedule
    (aggregateReaction_firesTo
      (s := s) st st' m m'
      tapeIn tapeBarIn tapeOut tapeBarOut
      hTape hTapeBar hTapeEq hTapeBarEq)

@[simp]
theorem aggregateNetwork_boundedIntendedSchedule_schedule
    {s : Nat}
    (st st' : MicroState Q)
    (m m' tapeIn tapeBarIn tapeOut tapeBarOut : Nat)
    (hTape : tapeIn <= m)
    (hTapeBar : tapeBarIn <= maxTape s - m)
    (hTapeEq : m - tapeIn + tapeOut = m')
    (hTapeBarEq :
      (maxTape s - m) - tapeBarIn + tapeBarOut = maxTape s - m') :
    (aggregateNetwork_boundedIntendedSchedule
      (s := s) st st' m m'
      tapeIn tapeBarIn tapeOut tapeBarOut
      hTape hTapeBar hTapeEq hTapeBarEq).schedule =
        [Network.OneRxnIdx.step] := by
  rfl

@[simp]
theorem aggregateNetwork_boundedIntendedSchedule_firingCount
    {s : Nat}
    (st st' : MicroState Q)
    (m m' tapeIn tapeBarIn tapeOut tapeBarOut : Nat)
    (hTape : tapeIn <= m)
    (hTapeBar : tapeBarIn <= maxTape s - m)
    (hTapeEq : m - tapeIn + tapeOut = m')
    (hTapeBarEq :
      (maxTape s - m) - tapeBarIn + tapeBarOut = maxTape s - m') :
    (aggregateNetwork_boundedIntendedSchedule
      (s := s) st st' m m'
      tapeIn tapeBarIn tapeOut tapeBarOut
      hTape hTapeBar hTapeEq hTapeBarEq).firingCount = 1 := by
  rfl

@[simp]
theorem aggregateNetwork_boundedIntendedSchedule_toIntendedSchedule
    {s : Nat}
    (st st' : MicroState Q)
    (m m' tapeIn tapeBarIn tapeOut tapeBarOut : Nat)
    (hTape : tapeIn <= m)
    (hTapeBar : tapeBarIn <= maxTape s - m)
    (hTapeEq : m - tapeIn + tapeOut = m')
    (hTapeBarEq :
      (maxTape s - m) - tapeBarIn + tapeBarOut = maxTape s - m') :
    (aggregateNetwork_boundedIntendedSchedule
      (s := s) st st' m m'
      tapeIn tapeBarIn tapeOut tapeBarOut
      hTape hTapeBar hTapeEq hTapeBarEq).toIntendedSchedule =
        aggregateNetwork_intendedSchedule
          (s := s) st st' m m'
          tapeIn tapeBarIn tapeOut tapeBarOut
          hTape hTapeBar hTapeEq hTapeBarEq := by
  rfl

theorem aggregateNetwork_intended_reaches
    {s : Nat}
    (st st' : MicroState Q)
    (m m' tapeIn tapeBarIn tapeOut tapeBarOut : Nat)
    (hTape : tapeIn <= m)
    (hTapeBar : tapeBarIn <= maxTape s - m)
    (hTapeEq : m - tapeIn + tapeOut = m')
    (hTapeBarEq :
      (maxTape s - m) - tapeBarIn + tapeBarOut = maxTape s - m') :
    (aggregateNetwork st st' tapeIn tapeBarIn tapeOut tapeBarOut).Reaches
      (enc ({ state := st, tape := m } : MicroCfg Q s))
      (enc ({ state := st', tape := m' } : MicroCfg Q s)) :=
  (aggregateNetwork_intendedSchedule
    (s := s) st st' m m'
    tapeIn tapeBarIn tapeOut tapeBarOut
    hTape hTapeBar hTapeEq hTapeBarEq).reaches

theorem aggregateNetwork_boundedIntendedSchedule_reaches
    {s : Nat}
    (st st' : MicroState Q)
    (m m' tapeIn tapeBarIn tapeOut tapeBarOut : Nat)
    (hTape : tapeIn <= m)
    (hTapeBar : tapeBarIn <= maxTape s - m)
    (hTapeEq : m - tapeIn + tapeOut = m')
    (hTapeBarEq :
      (maxTape s - m) - tapeBarIn + tapeBarOut = maxTape s - m') :
    (aggregateNetwork st st' tapeIn tapeBarIn tapeOut tapeBarOut).Reaches
      (enc ({ state := st, tape := m } : MicroCfg Q s))
      (enc ({ state := st', tape := m' } : MicroCfg Q s)) :=
  (aggregateNetwork_boundedIntendedSchedule
    (s := s) st st' m m'
    tapeIn tapeBarIn tapeOut tapeBarOut
    hTape hTapeBar hTapeEq hTapeBarEq).reaches

end FourPhaseEncoding

end CTM

end Ripple.sCRNUniversality
