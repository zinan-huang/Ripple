import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod
import Ripple.sCRNUniversality.Computation.Simulation
import Ripple.sCRNUniversality.Computation.CTM.FourPhase
import Ripple.sCRNUniversality.Computation.Encoding.Base3Tape

namespace Ripple.sCRNUniversality

namespace CTM

structure MicroState (Q : Type u) where
  q : Q
  phase : Phase4
  readSymbol : Option Bool := none
  pendingWrite : Option Bool := none
  pendingState : Option Q := none
deriving DecidableEq, Repr

namespace MicroState

def equivTuple {Q : Type u} :
    MicroState Q ≃ Q × Phase4 × Option Bool × Option Bool × Option Q where
  toFun st :=
    (st.q, st.phase, st.readSymbol, st.pendingWrite, st.pendingState)
  invFun
    | (q, phase, readSymbol, pendingWrite, pendingState) =>
        { q := q, phase := phase, readSymbol := readSymbol,
          pendingWrite := pendingWrite, pendingState := pendingState }
  left_inv := by
    intro st
    cases st
    rfl
  right_inv := by
    rintro ⟨q, phase, readSymbol, pendingWrite, pendingState⟩
    rfl

instance instFintype {Q : Type u} [Fintype Q] :
    Fintype (MicroState Q) :=
  Fintype.ofEquiv
    (Q × Phase4 × Option Bool × Option Bool × Option Q)
    (equivTuple (Q := Q)).symm

def readPhase {Q : Type u} (q : Q) : MicroState Q :=
  { q := q, phase := Phase4.read }

def afterRead {Q : Type u} (st : MicroState Q) (r w : Bool) (q' : Q) :
    MicroState Q :=
  { q := st.q, phase := Phase4.erase, readSymbol := some r,
    pendingWrite := some w, pendingState := some q' }

def afterErase {Q : Type u} (st : MicroState Q) : MicroState Q :=
  { st with phase := Phase4.shift }

def afterShift {Q : Type u} (st : MicroState Q) : MicroState Q :=
  { st with phase := Phase4.write }

def afterWrite {Q : Type u} (q' : Q) : MicroState Q :=
  { q := q', phase := Phase4.read }

@[simp]
theorem afterRead_phase {Q : Type u} (st : MicroState Q) (r w : Bool) (q' : Q) :
    (afterRead st r w q').phase = Phase4.erase := by
  rfl

@[simp]
theorem afterErase_phase {Q : Type u} (st : MicroState Q) :
    (afterErase st).phase = Phase4.shift := by
  rfl

@[simp]
theorem afterShift_phase {Q : Type u} (st : MicroState Q) :
    (afterShift st).phase = Phase4.write := by
  rfl

@[simp]
theorem afterWrite_phase {Q : Type u} (q' : Q) :
    (afterWrite q').phase = Phase4.read := by
  rfl

def Canonical {Q : Type u} (st : MicroState Q) : Prop :=
  match st.phase with
  | Phase4.read =>
      st.readSymbol = none ∧
        st.pendingWrite = none ∧
        st.pendingState = none
  | Phase4.erase =>
      exists r w q',
        st.readSymbol = some r ∧
          st.pendingWrite = some w ∧
          st.pendingState = some q'
  | Phase4.shift =>
      exists r w q',
        st.readSymbol = some r ∧
          st.pendingWrite = some w ∧
          st.pendingState = some q'
  | Phase4.write =>
      exists r w q',
        st.readSymbol = some r ∧
          st.pendingWrite = some w ∧
          st.pendingState = some q'

@[simp]
theorem readPhase_canonical {Q : Type u} (q : Q) :
    Canonical (readPhase q) := by
  simp [Canonical, readPhase]

@[simp]
theorem afterRead_canonical {Q : Type u} (st : MicroState Q)
    (r w : Bool) (q' : Q) :
    Canonical (afterRead st r w q') := by
  simp [Canonical, afterRead]

@[simp]
theorem afterWrite_canonical {Q : Type u} (q' : Q) :
    Canonical (afterWrite q') := by
  simp [Canonical, afterWrite]

theorem afterErase_canonical_of_erase {Q : Type u} {st : MicroState Q}
    (hst : Canonical st) (hphase : st.phase = Phase4.erase) :
    Canonical (afterErase st) := by
  have hpayload :
      exists r w q',
        st.readSymbol = some r ∧
          st.pendingWrite = some w ∧
          st.pendingState = some q' := by
    simpa [Canonical, hphase] using hst
  simpa [Canonical, afterErase] using hpayload

theorem afterShift_canonical_of_shift {Q : Type u} {st : MicroState Q}
    (hst : Canonical st) (hphase : st.phase = Phase4.shift) :
    Canonical (afterShift st) := by
  have hpayload :
      exists r w q',
        st.readSymbol = some r ∧
          st.pendingWrite = some w ∧
          st.pendingState = some q' := by
    simpa [Canonical, hphase] using hst
  simpa [Canonical, afterShift] using hpayload

end MicroState

structure MicroCfg (Q : Type u) (s : Nat) where
  state : MicroState Q
  tape : Nat
deriving Repr

namespace MicroCfg

def ofCTM {Q : Type u} {s : Nat} (c : Cfg Q Bool s) : MicroCfg Q s :=
  { state := MicroState.readPhase c.state, tape := Encoding.base3Val c.tape }

@[simp]
theorem ofCTM_state_canonical {Q : Type u} {s : Nat} (c : Cfg Q Bool s) :
    MicroState.Canonical (ofCTM c).state := by
  cases c
  simp [ofCTM]

end MicroCfg

def phaseStep? {Q : Type u} {s : Nat} (M : Binary Q) :
    MicroCfg Q s -> Option (MicroCfg Q s)
  | c =>
      match c.state.phase with
      | Phase4.read =>
          let r := Encoding.readMSB? s c.tape
          match M.delta c.state.q r with
          | none => none
          | some (w, q') =>
              some { state := MicroState.afterRead c.state r w q', tape := c.tape }
      | Phase4.erase =>
          match c.state.readSymbol with
          | none => none
          | some r =>
              some
                { state := MicroState.afterErase c.state,
                  tape := Encoding.eraseMSBWith s r c.tape }
      | Phase4.shift =>
          some
            { state := MicroState.afterShift c.state,
              tape := Encoding.shiftTail c.tape }
      | Phase4.write =>
          match c.state.pendingWrite, c.state.pendingState with
          | some w, some q' =>
              some
                { state := MicroState.afterWrite q',
                  tape := Encoding.writeLSB c.tape w }
          | _, _ => none

def fourPhaseSystem {Q : Type u} {s : Nat} (M : Binary Q) : DetSystem where
  Cfg := MicroCfg Q s
  step? := phaseStep? M

theorem phaseStep?_preserves_canonical {Q : Type u} {s : Nat}
    (M : Binary Q) {x y : MicroCfg Q s}
    (hx : MicroState.Canonical x.state)
    (hxy : phaseStep? (s := s) M x = some y) :
    MicroState.Canonical y.state := by
  cases x with
  | mk st tape =>
      cases st with
      | mk q phase readSymbol pendingWrite pendingState =>
          cases phase
          · cases hδ : M.delta q (Encoding.readMSB? s tape) with
            | none =>
                simp only [phaseStep?, hδ] at hxy
                cases hxy
            | some out =>
                rcases out with ⟨w, q'⟩
                have hEq :
                    some
                      ({ state :=
                          MicroState.afterRead
                            ({ q := q, phase := Phase4.read,
                               readSymbol := readSymbol,
                               pendingWrite := pendingWrite,
                               pendingState := pendingState } : MicroState Q)
                            (Encoding.readMSB? s tape) w q',
                         tape := tape } : MicroCfg Q s) = some y := by
                  simpa [phaseStep?, hδ] using hxy
                cases hEq
                exact
                  MicroState.afterRead_canonical
                    ({ q := q, phase := Phase4.read,
                       readSymbol := readSymbol,
                       pendingWrite := pendingWrite,
                       pendingState := pendingState } : MicroState Q)
                    (Encoding.readMSB? s tape) w q'
          · have hpayload :
                exists r w q',
                  readSymbol = some r ∧
                    pendingWrite = some w ∧
                    pendingState = some q' := by
              simpa [MicroState.Canonical] using hx
            rcases hpayload with ⟨r, _w, _q', hr, _hw, _hq⟩
            cases hr
            have hEq :
                some
                  ({ state :=
                      MicroState.afterErase
                        ({ q := q, phase := Phase4.erase,
                           readSymbol := some r,
                           pendingWrite := pendingWrite,
                           pendingState := pendingState } : MicroState Q),
                     tape := Encoding.eraseMSBWith s r tape } : MicroCfg Q s) =
                  some y := by
              simpa [phaseStep?] using hxy
            cases hEq
            exact
              MicroState.afterErase_canonical_of_erase
                (st :=
                  ({ q := q, phase := Phase4.erase,
                     readSymbol := some r,
                     pendingWrite := pendingWrite,
                     pendingState := pendingState } : MicroState Q))
                hx rfl
          · have hpayload :
                exists r w q',
                  readSymbol = some r ∧
                    pendingWrite = some w ∧
                    pendingState = some q' := by
              simpa [MicroState.Canonical] using hx
            rcases hpayload with ⟨_r, _w, _q', _hr, _hw, _hq⟩
            have hEq :
                some
                  ({ state :=
                      MicroState.afterShift
                        ({ q := q, phase := Phase4.shift,
                           readSymbol := readSymbol,
                           pendingWrite := pendingWrite,
                           pendingState := pendingState } : MicroState Q),
                     tape := Encoding.shiftTail tape } : MicroCfg Q s) =
                  some y := by
              simpa [phaseStep?] using hxy
            cases hEq
            exact
              MicroState.afterShift_canonical_of_shift
                (st :=
                  ({ q := q, phase := Phase4.shift,
                     readSymbol := readSymbol,
                     pendingWrite := pendingWrite,
                     pendingState := pendingState } : MicroState Q))
                hx rfl
          · have hpayload :
                exists r w q',
                  readSymbol = some r ∧
                    pendingWrite = some w ∧
                    pendingState = some q' := by
              simpa [MicroState.Canonical] using hx
            rcases hpayload with ⟨_r, w, q', _hr, hw, hq⟩
            cases hw
            cases hq
            have hEq :
                some
                  ({ state := MicroState.afterWrite q',
                     tape := Encoding.writeLSB tape w } : MicroCfg Q s) =
                  some y := by
              simpa [phaseStep?] using hxy
            cases hEq
            exact MicroState.afterWrite_canonical q'

theorem fourPhaseSystem_step_preserves_canonical {Q : Type u} {s : Nat}
    (M : Binary Q) {x y : MicroCfg Q s}
    (hx : MicroState.Canonical x.state)
    (hxy : (fourPhaseSystem (s := s) M).step? x = some y) :
    MicroState.Canonical y.state := by
  exact phaseStep?_preserves_canonical (s := s) M hx
    (by simpa [fourPhaseSystem] using hxy)

theorem fourPhaseSystem_steps_preserves_canonical {Q : Type u} {s : Nat}
    (M : Binary Q) {n : Nat} {x y : MicroCfg Q s}
    (hx : MicroState.Canonical x.state)
    (hxy : (fourPhaseSystem (s := s) M).steps? n x = some y) :
    MicroState.Canonical y.state := by
  induction n generalizing x y with
  | zero =>
      have hEq : (some x : Option (MicroCfg Q s)) = some y := by
        exact hxy
      cases hEq
      exact hx
  | succ n ih =>
      cases hstep : (fourPhaseSystem (s := s) M).step? x with
      | none =>
          simp only [DetSystem.steps?, DetSystem.iter, hstep] at hxy
          cases hxy
      | some x₁ =>
          have hx₁ : MicroState.Canonical x₁.state :=
            fourPhaseSystem_step_preserves_canonical (s := s) M hx hstep
          have htail :
              (fourPhaseSystem (s := s) M).steps? n x₁ = some y := by
            simpa [DetSystem.steps?, DetSystem.iter, hstep] using hxy
          exact ih hx₁ htail

@[simp]
theorem phaseStep?_read_some {Q : Type u} {s : Nat} (M : Binary Q)
    {q q' : Q} {tape : Nat} {readSymbol pendingWrite : Option Bool}
    {pendingState : Option Q} {w : Bool}
    (h : M.delta q (Encoding.readMSB? s tape) = some (w, q')) :
    phaseStep? (s := s) M
      { state :=
          { q := q, phase := Phase4.read, readSymbol := readSymbol,
            pendingWrite := pendingWrite, pendingState := pendingState },
        tape := tape } =
      some
        { state :=
            { q := q, phase := Phase4.erase,
              readSymbol := some (Encoding.readMSB? s tape),
              pendingWrite := some w, pendingState := some q' },
          tape := tape } := by
  simp [phaseStep?, h, MicroState.afterRead]

theorem phaseStep?_eq_afterRead_of_read {Q : Type u} {s : Nat}
    (M : Binary Q)
    {c c' : MicroCfg Q s} {w : Bool} {q' : Q}
    (hphase : c.state.phase = Phase4.read)
    (hdelta :
      M.delta c.state.q (Encoding.readMSB? s c.tape) = some (w, q'))
    (hstep : phaseStep? (s := s) M c = some c') :
    c' =
      { state :=
          MicroState.afterRead c.state (Encoding.readMSB? s c.tape) w q',
        tape := c.tape } := by
  cases c with
  | mk st tape =>
      cases st with
      | mk q phase readSymbol pendingWrite pendingState =>
          cases phase <;> try cases hphase
          have hEq :
              some
                ({ state :=
                    MicroState.afterRead
                      ({ q := q, phase := Phase4.read,
                         readSymbol := readSymbol,
                         pendingWrite := pendingWrite,
                         pendingState := pendingState } : MicroState Q)
                      (Encoding.readMSB? s tape) w q',
                   tape := tape } : MicroCfg Q s) =
                some c' := by
            simpa [phaseStep?, hdelta] using hstep
          cases hEq
          rfl

@[simp]
theorem phaseStep?_read_none {Q : Type u} {s : Nat} (M : Binary Q)
    {q : Q} {tape : Nat} {readSymbol pendingWrite : Option Bool}
    {pendingState : Option Q}
    (h : M.delta q (Encoding.readMSB? s tape) = none) :
    phaseStep? (s := s) M
      { state :=
          { q := q, phase := Phase4.read, readSymbol := readSymbol,
            pendingWrite := pendingWrite, pendingState := pendingState },
        tape := tape } = none := by
  simp [phaseStep?, h]

@[simp]
theorem phaseStep?_erase {Q : Type u} {s : Nat} (M : Binary Q)
    {q : Q} {tape : Nat} {r : Bool} {pendingWrite : Option Bool}
    {pendingState : Option Q} :
    phaseStep? (s := s) M
      { state :=
          { q := q, phase := Phase4.erase, readSymbol := some r,
            pendingWrite := pendingWrite, pendingState := pendingState },
        tape := tape } =
      some
        { state :=
            { q := q, phase := Phase4.shift, readSymbol := some r,
              pendingWrite := pendingWrite, pendingState := pendingState },
          tape := Encoding.eraseMSBWith s r tape } := by
  simp [phaseStep?, MicroState.afterErase]

theorem phaseStep?_eq_eraseMSBWith_of_erase {Q : Type u} {s : Nat}
    (M : Binary Q)
    {c c' : MicroCfg Q s} {r : Bool}
    (hphase : c.state.phase = Phase4.erase)
    (hr : c.state.readSymbol = some r)
    (hstep : phaseStep? (s := s) M c = some c') :
    c' =
      { state := MicroState.afterErase c.state,
        tape := Encoding.eraseMSBWith s r c.tape } := by
  cases c with
  | mk st tape =>
      cases st with
      | mk q phase readSymbol pendingWrite pendingState =>
          cases phase <;> try cases hphase
          cases readSymbol with
          | none =>
              simp at hr
          | some r0 =>
              cases hr
              have hEq :
                  some
                    ({ state :=
                        MicroState.afterErase
                          ({ q := q, phase := Phase4.erase,
                             readSymbol := some r,
                             pendingWrite := pendingWrite,
                             pendingState := pendingState } : MicroState Q),
                       tape := Encoding.eraseMSBWith s r tape } :
                      MicroCfg Q s) =
                    some c' := by
                simpa [phaseStep?] using hstep
              cases hEq
              rfl

@[simp]
theorem phaseStep?_erase_none {Q : Type u} {s : Nat} (M : Binary Q)
    {q : Q} {tape : Nat} {pendingWrite : Option Bool}
    {pendingState : Option Q} :
    phaseStep? (s := s) M
      { state :=
          { q := q, phase := Phase4.erase, readSymbol := none,
            pendingWrite := pendingWrite, pendingState := pendingState },
        tape := tape } = none := by
  simp [phaseStep?]

@[simp]
theorem phaseStep?_shift {Q : Type u} {s : Nat} (M : Binary Q)
    {q : Q} {tape : Nat} {readSymbol pendingWrite : Option Bool}
    {pendingState : Option Q} :
    phaseStep? (s := s) M
      { state :=
          { q := q, phase := Phase4.shift, readSymbol := readSymbol,
            pendingWrite := pendingWrite, pendingState := pendingState },
        tape := tape } =
      some
        { state :=
            { q := q, phase := Phase4.write, readSymbol := readSymbol,
              pendingWrite := pendingWrite, pendingState := pendingState },
          tape := Encoding.shiftTail tape } := by
  simp [phaseStep?, MicroState.afterShift]

theorem phaseStep?_eq_shiftTail_of_shift {Q : Type u} {s : Nat}
    (M : Binary Q)
    {c c' : MicroCfg Q s}
    (hphase : c.state.phase = Phase4.shift)
    (hstep : phaseStep? (s := s) M c = some c') :
    c' =
      { state := MicroState.afterShift c.state,
        tape := Encoding.shiftTail c.tape } := by
  cases c with
  | mk st tape =>
      cases st with
      | mk q phase readSymbol pendingWrite pendingState =>
          cases phase <;> try cases hphase
          have hEq :
              some
                ({ state :=
                    MicroState.afterShift
                      ({ q := q, phase := Phase4.shift,
                         readSymbol := readSymbol,
                         pendingWrite := pendingWrite,
                         pendingState := pendingState } : MicroState Q),
                   tape := Encoding.shiftTail tape } : MicroCfg Q s) =
                some c' := by
            simpa [phaseStep?] using hstep
          cases hEq
          rfl

@[simp]
theorem phaseStep?_write {Q : Type u} {s : Nat} (M : Binary Q)
    {q q' : Q} {tape : Nat} {readSymbol : Option Bool} {w : Bool} :
    phaseStep? (s := s) M
      { state :=
          { q := q, phase := Phase4.write, readSymbol := readSymbol,
            pendingWrite := some w, pendingState := some q' },
        tape := tape } =
      some
        { state :=
            { q := q', phase := Phase4.read, readSymbol := none,
              pendingWrite := none, pendingState := none },
          tape := Encoding.writeLSB tape w } := by
  simp [phaseStep?, MicroState.afterWrite]

theorem phaseStep?_eq_writeLSB_of_write {Q : Type u} {s : Nat}
    (M : Binary Q)
    {c c' : MicroCfg Q s} {b : Bool} {q' : Q}
    (hphase : c.state.phase = Phase4.write)
    (hwrite : c.state.pendingWrite = some b)
    (hstate : c.state.pendingState = some q')
    (hstep : phaseStep? (s := s) M c = some c') :
    c' =
      { state := MicroState.afterWrite q',
        tape := Encoding.writeLSB c.tape b } := by
  cases c with
  | mk st tape =>
      cases st with
      | mk q phase readSymbol pendingWrite pendingState =>
          cases phase <;> try cases hphase
          cases pendingWrite with
          | none =>
              simp at hwrite
          | some b0 =>
              cases hwrite
              cases pendingState with
              | none =>
                  simp at hstate
              | some q0 =>
                  cases hstate
                  have hEq :
                      some
                        ({ state := MicroState.afterWrite q',
                           tape := Encoding.writeLSB tape b } :
                          MicroCfg Q s) =
                        some c' := by
                    simpa [phaseStep?] using hstep
                  cases hEq
                  rfl

@[simp]
theorem phaseStep?_write_no_symbol {Q : Type u} {s : Nat} (M : Binary Q)
    {q : Q} {tape : Nat} {readSymbol : Option Bool}
    {pendingState : Option Q} :
    phaseStep? (s := s) M
      { state :=
          { q := q, phase := Phase4.write, readSymbol := readSymbol,
            pendingWrite := none, pendingState := pendingState },
        tape := tape } = none := by
  cases pendingState <;> simp [phaseStep?]

@[simp]
theorem phaseStep?_write_no_state {Q : Type u} {s : Nat} (M : Binary Q)
    {q : Q} {tape : Nat} {readSymbol : Option Bool}
    {pendingWrite : Option Bool} :
    phaseStep? (s := s) M
      { state :=
          { q := q, phase := Phase4.write, readSymbol := readSymbol,
            pendingWrite := pendingWrite, pendingState := none },
        tape := tape } = none := by
  cases pendingWrite <;> simp [phaseStep?]

theorem phaseStep?_read_base3_some {Q : Type u} {s : Nat} (M : Binary Q)
    {q q' : Q} {tape : List.Vector Bool (s + 1)}
    {readSymbol pendingWrite : Option Bool} {pendingState : Option Q}
    {w : Bool} (h : M.delta q tape.head = some (w, q')) :
    phaseStep? (s := s) M
      { state :=
          { q := q, phase := Phase4.read, readSymbol := readSymbol,
            pendingWrite := pendingWrite, pendingState := pendingState },
        tape := Encoding.base3Val tape } =
      some
        { state :=
            { q := q, phase := Phase4.erase, readSymbol := some tape.head,
              pendingWrite := some w, pendingState := some q' },
          tape := Encoding.base3Val tape } := by
  simp [phaseStep?, Encoding.readMSB?_base3Val tape, h, MicroState.afterRead]

theorem phaseStep?_read_base3_none {Q : Type u} {s : Nat} (M : Binary Q)
    {q : Q} {tape : List.Vector Bool (s + 1)}
    {readSymbol pendingWrite : Option Bool} {pendingState : Option Q}
    (h : M.delta q tape.head = none) :
    phaseStep? (s := s) M
      { state :=
          { q := q, phase := Phase4.read, readSymbol := readSymbol,
            pendingWrite := pendingWrite, pendingState := pendingState },
        tape := Encoding.base3Val tape } = none := by
  simp [phaseStep?, Encoding.readMSB?_base3Val tape, h]

theorem fourPhase_count_correct {Q : Type u} {s : Nat} (M : Binary Q)
    {q q' : Q} {tape : Nat} {w : Bool}
    (h : M.delta q (Encoding.readMSB? s tape) = some (w, q')) :
    (fourPhaseSystem (s := s) M).steps? 4
        { state := MicroState.readPhase q, tape := tape } =
      some
        { state := MicroState.readPhase (q'),
          tape := Encoding.rotateWriteVal s tape w } := by
  simp [fourPhaseSystem, DetSystem.steps?, DetSystem.iter, phaseStep?, h,
    MicroState.readPhase, MicroState.afterRead, MicroState.afterErase,
    MicroState.afterShift, MicroState.afterWrite, Encoding.rotateWriteVal,
    Encoding.eraseMSB]

theorem fourPhase_count_halt {Q : Type u} {s : Nat} (M : Binary Q)
    {q : Q} {tape : Nat}
    (h : M.delta q (Encoding.readMSB? s tape) = none) :
    (fourPhaseSystem (s := s) M).steps? 1
        { state := MicroState.readPhase q, tape := tape } = none := by
  simp [fourPhaseSystem, DetSystem.steps?, DetSystem.iter, phaseStep?, h,
    MicroState.readPhase]

theorem fourPhase_base3_correct {Q : Type u} {s : Nat} (M : Binary Q)
    {q q' : Q} {tape : List.Vector Bool (s + 1)} {w : Bool}
    (h : M.delta q tape.head = some (w, q')) :
    (fourPhaseSystem (s := s) M).steps? 4
        { state := MicroState.readPhase q, tape := Encoding.base3Val tape } =
      some
        { state := MicroState.readPhase (q'),
          tape := Encoding.base3Val (Machine.rotateWrite tape w) } := by
  have hRead :
      M.delta q (Encoding.readMSB? s (Encoding.base3Val tape)) = some (w, q') := by
    simpa [Encoding.readMSB?_base3Val tape] using h
  simpa [Encoding.rotateWriteVal_base3Val tape w] using
    (fourPhase_count_correct (s := s) M
      (q := q) (q' := q') (tape := Encoding.base3Val tape) (w := w) hRead)

theorem phaseStep?_boundary_none_iff {Q : Type u} {s : Nat}
    (M : Binary Q) (c : Cfg Q Bool s) :
    phaseStep? (s := s) M (MicroCfg.ofCTM c) = none <->
      M.step? c = none := by
  cases c with
  | mk q tape =>
      cases hDelta : M.delta q tape.head with
      | none =>
          simp [MicroCfg.ofCTM, Machine.step?, phaseStep?,
            Encoding.readMSB?_base3Val tape, MicroState.readPhase, hDelta]
      | some p =>
          rcases p with ⟨w, q'⟩
          simp [MicroCfg.ofCTM, Machine.step?, phaseStep?,
            Encoding.readMSB?_base3Val tape, MicroState.readPhase, hDelta]

theorem fourPhase_boundary_step {Q : Type u} {s : Nat}
    (M : Binary Q) {c c' : Cfg Q Bool s}
    (h : M.step? c = some c') :
    (fourPhaseSystem (s := s) M).steps? 4 (MicroCfg.ofCTM c) =
      some (MicroCfg.ofCTM c') := by
  cases c with
  | mk q tape =>
      cases hDelta : M.delta q tape.head with
      | none =>
          have hStep :
              M.step? ({ state := q, tape := tape } : Cfg Q Bool s) = none := by
            simp [Machine.step?, hDelta]
          rw [hStep] at h
          cases h
      | some p =>
          rcases p with ⟨w, q'⟩
          have hSome :
              some { state := q', tape := Machine.rotateWrite tape w } = some c' := by
            simpa [Machine.step?, hDelta] using h
          cases hSome
          simpa [MicroCfg.ofCTM] using
            (fourPhase_base3_correct (s := s) M
              (q := q) (q' := q') (tape := tape) (w := w) hDelta)

def fourPhaseKStepSim {Q : Type u} {s : Nat}
    (M : Binary Q) : KStepSim (M.detSystem (s := s)) (fourPhaseSystem (s := s) M) 4 where
  enc := MicroCfg.ofCTM
  step_ok := by
    intro c c' h
    exact fourPhase_boundary_step M h
  halt_ok := by
    intro c h
    exact (phaseStep?_boundary_none_iff M c).mpr h

theorem fourPhaseKStepSim_steps {Q : Type u} {s n : Nat}
    (M : Binary Q) {cfg cfg' : Cfg Q Bool s}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg') :
    (fourPhaseSystem (s := s) M).steps? (4 * n) (MicroCfg.ofCTM cfg) =
      some (MicroCfg.ofCTM cfg') := by
  simpa using
    (KStepSim.steps? (sim := fourPhaseKStepSim (s := s) M) h)

theorem fourPhaseKStepSim_steps_canonical {Q : Type u} {s n : Nat}
    (M : Binary Q) {cfg : Cfg Q Bool s} {y : MicroCfg Q s}
    (h :
      (fourPhaseSystem (s := s) M).steps? (4 * n) (MicroCfg.ofCTM cfg) =
        some y) :
    MicroState.Canonical y.state := by
  exact fourPhaseSystem_steps_preserves_canonical (s := s) M
    (n := 4 * n) (x := MicroCfg.ofCTM cfg) (y := y)
    (MicroCfg.ofCTM_state_canonical cfg) h

end CTM

end Ripple.sCRNUniversality
