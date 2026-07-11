import Ripple.sCRNUniversality.Computation.CTM.FourPhaseTapeInvariant

namespace Ripple.sCRNUniversality

namespace CTM

namespace FourPhaseEncoding

universe u

variable {Q : Type u} [DecidableEq Q] {s : Nat}

def Encoded (c : MicroCfg Q s) (z : State (Species Q)) : Prop :=
  z = enc c

@[simp]
theorem encoded_enc (c : MicroCfg Q s) :
    Encoded c (enc c) := by
  rfl

theorem eq_of_encoded {c : MicroCfg Q s} {z : State (Species Q)}
    (hz : Encoded c z) :
    z = enc c :=
  hz

def EncodedWith (P : MicroCfg Q s -> Prop)
    (z : State (Species Q)) : Prop :=
  exists c : MicroCfg Q s, P c /\ Encoded c z

def EncodedCanonical (z : State (Species Q)) : Prop :=
  EncodedWith (fun c : MicroCfg Q s => MicroState.Canonical c.state) z

def EncodedTapeWF (z : State (Species Q)) : Prop :=
  EncodedWith (fun c : MicroCfg Q s => c.TapeWF) z

def EncodedGadgetWF (z : State (Species Q)) : Prop :=
  EncodedWith (fun c : MicroCfg Q s => GadgetMicroCfgWF c) z

theorem encodedWith_mono {P R : MicroCfg Q s -> Prop}
    (hPR : forall c, P c -> R c)
    {z : State (Species Q)}
    (hz : EncodedWith P z) :
    EncodedWith R z := by
  rcases hz with ⟨c, hc, henc⟩
  exact ⟨c, hPR c hc, henc⟩

theorem encodedGadgetWF_encodedCanonical {z : State (Species Q)}
    (hz : EncodedGadgetWF (Q := Q) (s := s) z) :
    EncodedCanonical (Q := Q) (s := s) z := by
  rcases hz with ⟨c, hc, henc⟩
  exact ⟨c, hc.1, henc⟩

theorem encodedGadgetWF_encodedTapeWF {z : State (Species Q)}
    (hz : EncodedGadgetWF (Q := Q) (s := s) z) :
    EncodedTapeWF (Q := Q) (s := s) z := by
  rcases hz with ⟨c, hc, henc⟩
  exact ⟨c, hc.2, henc⟩

@[simp]
theorem enc_ctrl_eq_zero_of_ne_ctrlOf
    (c : MicroCfg Q s)
    {q : Q} {phase : Phase4}
    {readSymbol pendingWrite : Option Bool}
    {pendingState : Option Q}
    (hne :
      FourPhaseSpecies.ctrl q phase readSymbol pendingWrite pendingState ≠
        FourPhaseSpecies.ctrlOf c.state) :
    enc c
      (FourPhaseSpecies.ctrl q phase readSymbol pendingWrite pendingState) =
      0 := by
  cases c with
  | mk st m =>
      cases st with
      | mk q0 phase0 read0 write0 state0 =>
          have hne' :
              FourPhaseSpecies.ctrl q phase readSymbol pendingWrite pendingState ≠
                FourPhaseSpecies.ctrl q0 phase0 read0 write0 state0 := by
            simpa [FourPhaseSpecies.ctrlOf] using hne
          simp [enc, control, tape, tapeBar, State.add,
            FourPhaseSpecies.ctrlOf, State.single, hne']

theorem enc_ctrl_pos_iff_ctrlOf
    (c : MicroCfg Q s)
    {q : Q} {phase : Phase4}
    {readSymbol pendingWrite : Option Bool}
    {pendingState : Option Q} :
    0 <
      enc c
        (FourPhaseSpecies.ctrl q phase readSymbol pendingWrite pendingState) ↔
      FourPhaseSpecies.ctrl q phase readSymbol pendingWrite pendingState =
        FourPhaseSpecies.ctrlOf c.state := by
  constructor
  · intro hpos
    by_contra hne
    have hz :
        enc c
          (FourPhaseSpecies.ctrl q phase readSymbol pendingWrite pendingState) =
        0 :=
      enc_ctrl_eq_zero_of_ne_ctrlOf c hne
    rw [hz] at hpos
    exact False.elim ((Nat.lt_irrefl 0) hpos)
  · intro hEq
    rw [hEq]
    simp

theorem enc_ctrl_eq_zero_of_ne_phase
    (c : MicroCfg Q s)
    {q : Q} {phase : Phase4}
    {readSymbol pendingWrite : Option Bool}
    {pendingState : Option Q}
    (hphase : phase ≠ c.state.phase) :
    enc c
      (FourPhaseSpecies.ctrl q phase readSymbol pendingWrite pendingState) =
      0 := by
  cases c with
  | mk st m =>
      cases st with
      | mk q0 phase0 read0 write0 state0 =>
          apply enc_ctrl_eq_zero_of_ne_ctrlOf
          intro hctrl
          injection hctrl with _ hphaseEq _ _ _
          exact hphase hphaseEq

theorem enc_ctrlOf_eq_zero_of_ne_phase
    (c : MicroCfg Q s) (st : MicroState Q)
    (hphase : st.phase ≠ c.state.phase) :
    enc c (FourPhaseSpecies.ctrlOf st) = 0 := by
  cases st with
  | mk q phase readSymbol pendingWrite pendingState =>
      exact enc_ctrl_eq_zero_of_ne_phase c hphase

def ControlTokenAt (st : MicroState Q) (z : State (Species Q)) : Prop :=
  z (FourPhaseSpecies.ctrlOf st) = 1

def OtherControlTokensZero
    (st : MicroState Q) (z : State (Species Q)) : Prop :=
  forall q phase readSymbol pendingWrite pendingState,
    FourPhaseSpecies.ctrl q phase readSymbol pendingWrite pendingState ≠
      FourPhaseSpecies.ctrlOf st ->
    z (FourPhaseSpecies.ctrl q phase readSymbol pendingWrite pendingState) = 0

def UniqueControlTokenAt
    (st : MicroState Q) (z : State (Species Q)) : Prop :=
  ControlTokenAt st z /\ OtherControlTokensZero st z

def ControlPhaseAt (phase : Phase4) (z : State (Species Q)) : Prop :=
  exists st : MicroState Q, st.phase = phase /\ ControlTokenAt st z

theorem encoded_controlTokenAt
    {c : MicroCfg Q s} {z : State (Species Q)}
    (hz : Encoded c z) :
    ControlTokenAt c.state z := by
  cases hz
  simp [ControlTokenAt]

theorem encoded_otherControlTokensZero
    {c : MicroCfg Q s} {z : State (Species Q)}
    (hz : Encoded c z) :
    OtherControlTokensZero c.state z := by
  cases hz
  intro q phase readSymbol pendingWrite pendingState hne
  exact enc_ctrl_eq_zero_of_ne_ctrlOf c hne

theorem encoded_uniqueControlTokenAt
    {c : MicroCfg Q s} {z : State (Species Q)}
    (hz : Encoded c z) :
    UniqueControlTokenAt c.state z :=
  ⟨encoded_controlTokenAt hz, encoded_otherControlTokensZero hz⟩

theorem encoded_controlPhaseAt
    {c : MicroCfg Q s} {z : State (Species Q)}
    (hz : Encoded c z) :
    ControlPhaseAt c.state.phase z :=
  ⟨c.state, rfl, encoded_controlTokenAt hz⟩

def TapeValueAt (n : Nat) (z : State (Species Q)) : Prop :=
  z FourPhaseSpecies.tape = n

def TapeBarValueAt (s n : Nat) (z : State (Species Q)) : Prop :=
  z FourPhaseSpecies.tapeBar = maxTape s - n

def TapePairAt (s n : Nat) (z : State (Species Q)) : Prop :=
  TapeValueAt n z /\ TapeBarValueAt (Q := Q) s n z

def TapeComplement (s : Nat) (z : State (Species Q)) : Prop :=
  z FourPhaseSpecies.tape + z FourPhaseSpecies.tapeBar = maxTape s

def TapeBound (s : Nat) (z : State (Species Q)) : Prop :=
  z FourPhaseSpecies.tape <= maxTape s /\
    z FourPhaseSpecies.tapeBar <= maxTape s

omit [DecidableEq Q] in
theorem tape_le_maxTape_of_tapeWF {c : MicroCfg Q s}
    (hc : c.TapeWF) :
    c.tape <= maxTape s := by
  cases c with
  | mk st m =>
      cases st with
      | mk q phase readSymbol pendingWrite pendingState =>
          cases phase
          · exact le_maxTape_of_IsBase3BoolTape hc
          · exact le_maxTape_of_IsBase3BoolTape hc.1
          · change m <= maxTape s
            have hlt : m < 3 ^ s := hc.lt_pow
            have hltSucc : m < 3 ^ (s + 1) := by
              rw [pow_succ]
              have hpos : 0 < 3 ^ s := Nat.pow_pos (by norm_num)
              nlinarith
            unfold maxTape
            omega
          · rcases hc with ⟨tail, hTail, rfl⟩
            exact shiftTail_le_maxTape_of_lt_pow hTail.lt_pow

omit [DecidableEq Q] in
theorem tape_le_maxTape_of_gadgetWF {c : MicroCfg Q s}
    (hc : GadgetMicroCfgWF c) :
    c.tape <= maxTape s :=
  tape_le_maxTape_of_tapeWF hc.2

theorem encoded_tapePairAt
    {c : MicroCfg Q s} {z : State (Species Q)}
    (hz : Encoded c z) :
    TapePairAt (Q := Q) s c.tape z := by
  cases hz
  simp [TapePairAt, TapeValueAt, TapeBarValueAt]

theorem encoded_tapeComplement_of_le
    {c : MicroCfg Q s} {z : State (Species Q)}
    (hz : Encoded c z)
    (hle : c.tape <= maxTape s) :
    TapeComplement (Q := Q) s z := by
  cases hz
  unfold TapeComplement
  rw [enc_tape, enc_tapeBar]
  exact Nat.add_sub_of_le hle

theorem encoded_tapeComplement_of_gadgetWF
    {c : MicroCfg Q s} {z : State (Species Q)}
    (hc : GadgetMicroCfgWF c)
    (hz : Encoded c z) :
    TapeComplement (Q := Q) s z :=
  encoded_tapeComplement_of_le hz (tape_le_maxTape_of_gadgetWF hc)

theorem encoded_tapeBound_of_le
    {c : MicroCfg Q s} {z : State (Species Q)}
    (hz : Encoded c z)
    (hle : c.tape <= maxTape s) :
    TapeBound (Q := Q) s z := by
  cases hz
  constructor
  · simpa [TapeBound] using hle
  · simp

theorem encoded_tapeBound_of_gadgetWF
    {c : MicroCfg Q s} {z : State (Species Q)}
    (hc : GadgetMicroCfgWF c)
    (hz : Encoded c z) :
    TapeBound (Q := Q) s z :=
  encoded_tapeBound_of_le hz (tape_le_maxTape_of_gadgetWF hc)

theorem encodedGadgetWF_boundary_invariants
    {z : State (Species Q)}
    (hz : EncodedGadgetWF (Q := Q) (s := s) z) :
    exists c : MicroCfg Q s,
      GadgetMicroCfgWF c /\
        UniqueControlTokenAt c.state z /\
        TapePairAt (Q := Q) s c.tape z /\
        TapeComplement (Q := Q) s z /\
        TapeBound (Q := Q) s z := by
  rcases hz with ⟨c, hc, henc⟩
  exact
    ⟨c, hc,
      encoded_uniqueControlTokenAt henc,
      encoded_tapePairAt henc,
      encoded_tapeComplement_of_gadgetWF hc henc,
      encoded_tapeBound_of_gadgetWF hc henc⟩

end FourPhaseEncoding

end CTM

end Ripple.sCRNUniversality
