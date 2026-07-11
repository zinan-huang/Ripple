import Mathlib.Tactic
import Ripple.sCRNUniversality.Computation.CTM.FourPhaseCRNBridge
import Ripple.sCRNUniversality.Core.Finite
import Ripple.sCRNUniversality.Core.Footprint

namespace Ripple.sCRNUniversality

namespace CTM

universe u v

section PhaseParallel

variable {S : Type v} [Fintype S]

abbrev phaseParallel4
    (Nread Nerase Nshift Nwrite : Network.{v, w} S) :
    Network.{v, w} S :=
  (Nread.parallel Nerase).parallel (Nshift.parallel Nwrite)

omit [Fintype S] in
theorem phaseParallel4_exec_read
    {Nread Nerase Nshift Nwrite : Network.{v, w} S}
    {z z' : State S} {is : List Nread.I}
    (h : Nread.Exec z z' is) :
    (phaseParallel4 Nread Nerase Nshift Nwrite).Exec z z'
      (is.map (fun i => Sum.inl (Sum.inl i))) := by
  simpa [phaseParallel4, List.map_map] using
    Network.parallel_exec_inl
      (Nread.parallel Nerase) (Nshift.parallel Nwrite)
      (Network.parallel_exec_inl Nread Nerase h)

omit [Fintype S] in
theorem phaseParallel4_exec_erase
    {Nread Nerase Nshift Nwrite : Network.{v, w} S}
    {z z' : State S} {is : List Nerase.I}
    (h : Nerase.Exec z z' is) :
    (phaseParallel4 Nread Nerase Nshift Nwrite).Exec z z'
      (is.map (fun i => Sum.inl (Sum.inr i))) := by
  simpa [phaseParallel4, List.map_map] using
    Network.parallel_exec_inl
      (Nread.parallel Nerase) (Nshift.parallel Nwrite)
      (Network.parallel_exec_inr Nread Nerase h)

omit [Fintype S] in
theorem phaseParallel4_exec_shift
    {Nread Nerase Nshift Nwrite : Network.{v, w} S}
    {z z' : State S} {is : List Nshift.I}
    (h : Nshift.Exec z z' is) :
    (phaseParallel4 Nread Nerase Nshift Nwrite).Exec z z'
      (is.map (fun i => Sum.inr (Sum.inl i))) := by
  simpa [phaseParallel4, List.map_map] using
    Network.parallel_exec_inr
      (Nread.parallel Nerase) (Nshift.parallel Nwrite)
      (Network.parallel_exec_inl Nshift Nwrite h)

omit [Fintype S] in
theorem phaseParallel4_exec_write
    {Nread Nerase Nshift Nwrite : Network.{v, w} S}
    {z z' : State S} {is : List Nwrite.I}
    (h : Nwrite.Exec z z' is) :
    (phaseParallel4 Nread Nerase Nshift Nwrite).Exec z z'
      (is.map (fun i => Sum.inr (Sum.inr i))) := by
  simpa [phaseParallel4, List.map_map] using
    Network.parallel_exec_inr
      (Nread.parallel Nerase) (Nshift.parallel Nwrite)
      (Network.parallel_exec_inr Nshift Nwrite h)

omit [Fintype S] in
theorem phaseParallel4_scheduleFootprintWithin_read
    {Nread Nerase Nshift Nwrite : Network.{v, w} S}
    {is : List Nread.I} {P : S -> Prop}
    (h : Nread.ScheduleFootprintWithin is P) :
    (phaseParallel4 Nread Nerase Nshift Nwrite).ScheduleFootprintWithin
      (is.map (fun i => Sum.inl (Sum.inl i))) P := by
  simpa [phaseParallel4, List.map_map] using
    Network.parallel_scheduleFootprintWithin_inl
      (N := Nread.parallel Nerase) (M := Nshift.parallel Nwrite)
      (Network.parallel_scheduleFootprintWithin_inl
        (N := Nread) (M := Nerase) h)

omit [Fintype S] in
theorem phaseParallel4_scheduleFootprintWithin_erase
    {Nread Nerase Nshift Nwrite : Network.{v, w} S}
    {is : List Nerase.I} {P : S -> Prop}
    (h : Nerase.ScheduleFootprintWithin is P) :
    (phaseParallel4 Nread Nerase Nshift Nwrite).ScheduleFootprintWithin
      (is.map (fun i => Sum.inl (Sum.inr i))) P := by
  simpa [phaseParallel4, List.map_map] using
    Network.parallel_scheduleFootprintWithin_inl
      (N := Nread.parallel Nerase) (M := Nshift.parallel Nwrite)
      (Network.parallel_scheduleFootprintWithin_inr
        (N := Nread) (M := Nerase) h)

omit [Fintype S] in
theorem phaseParallel4_scheduleFootprintWithin_shift
    {Nread Nerase Nshift Nwrite : Network.{v, w} S}
    {is : List Nshift.I} {P : S -> Prop}
    (h : Nshift.ScheduleFootprintWithin is P) :
    (phaseParallel4 Nread Nerase Nshift Nwrite).ScheduleFootprintWithin
      (is.map (fun i => Sum.inr (Sum.inl i))) P := by
  simpa [phaseParallel4, List.map_map] using
    Network.parallel_scheduleFootprintWithin_inr
      (N := Nread.parallel Nerase) (M := Nshift.parallel Nwrite)
      (Network.parallel_scheduleFootprintWithin_inl
        (N := Nshift) (M := Nwrite) h)

omit [Fintype S] in
theorem phaseParallel4_scheduleFootprintWithin_write
    {Nread Nerase Nshift Nwrite : Network.{v, w} S}
    {is : List Nwrite.I} {P : S -> Prop}
    (h : Nwrite.ScheduleFootprintWithin is P) :
    (phaseParallel4 Nread Nerase Nshift Nwrite).ScheduleFootprintWithin
      (is.map (fun i => Sum.inr (Sum.inr i))) P := by
  simpa [phaseParallel4, List.map_map] using
    Network.parallel_scheduleFootprintWithin_inr
      (N := Nread.parallel Nerase) (M := Nshift.parallel Nwrite)
      (Network.parallel_scheduleFootprintWithin_inr
        (N := Nshift) (M := Nwrite) h)

omit [Fintype S] in
theorem phaseParallel4_hasPositiveRates
    {Nread Nerase Nshift Nwrite : Network.{v, w} S}
    (hread : Nread.hasPositiveRates)
    (herase : Nerase.hasPositiveRates)
    (hshift : Nshift.hasPositiveRates)
    (hwrite : Nwrite.hasPositiveRates) :
    (phaseParallel4 Nread Nerase Nshift Nwrite).hasPositiveRates := by
  exact
    (Network.parallel_hasPositiveRates_iff
      (Nread.parallel Nerase) (Nshift.parallel Nwrite)).2
      ⟨
        (Network.parallel_hasPositiveRates_iff Nread Nerase).2
          ⟨hread, herase⟩,
        (Network.parallel_hasPositiveRates_iff Nshift Nwrite).2
          ⟨hshift, hwrite⟩
      ⟩

omit [Fintype S] in
theorem phaseParallel4_allUnitRate
    {Nread Nerase Nshift Nwrite : Network.{v, w} S}
    (hread : Nread.allUnitRate)
    (herase : Nerase.allUnitRate)
    (hshift : Nshift.allUnitRate)
    (hwrite : Nwrite.allUnitRate) :
    (phaseParallel4 Nread Nerase Nshift Nwrite).allUnitRate := by
  exact
    (Network.parallel_allUnitRate_iff
      (Nread.parallel Nerase) (Nshift.parallel Nwrite)).2
      ⟨
        (Network.parallel_allUnitRate_iff Nread Nerase).2
          ⟨hread, herase⟩,
        (Network.parallel_allUnitRate_iff Nshift Nwrite).2
          ⟨hshift, hwrite⟩
      ⟩

theorem phaseParallel4_allBimolecularInput
    {Nread Nerase Nshift Nwrite : Network.{v, w} S}
    (hread : Nread.allBimolecularInput)
    (herase : Nerase.allBimolecularInput)
    (hshift : Nshift.allBimolecularInput)
    (hwrite : Nwrite.allBimolecularInput) :
    (phaseParallel4 Nread Nerase Nshift Nwrite).allBimolecularInput := by
  exact
    (Network.parallel_allBimolecularInput_iff
      (Nread.parallel Nerase) (Nshift.parallel Nwrite)).2
      ⟨
        (Network.parallel_allBimolecularInput_iff Nread Nerase).2
          ⟨hread, herase⟩,
        (Network.parallel_allBimolecularInput_iff Nshift Nwrite).2
          ⟨hshift, hwrite⟩
      ⟩

theorem phaseParallel4_allAtMostBimolecularInput
    {Nread Nerase Nshift Nwrite : Network.{v, w} S}
    (hread : Nread.allAtMostBimolecularInput)
    (herase : Nerase.allAtMostBimolecularInput)
    (hshift : Nshift.allAtMostBimolecularInput)
    (hwrite : Nwrite.allAtMostBimolecularInput) :
    (phaseParallel4 Nread Nerase Nshift Nwrite).allAtMostBimolecularInput := by
  exact
    (Network.parallel_allAtMostBimolecularInput_iff
      (Nread.parallel Nerase) (Nshift.parallel Nwrite)).2
      ⟨
        (Network.parallel_allAtMostBimolecularInput_iff Nread Nerase).2
          ⟨hread, herase⟩,
        (Network.parallel_allAtMostBimolecularInput_iff Nshift Nwrite).2
          ⟨hshift, hwrite⟩
      ⟩

theorem phaseParallel4_allAtMostBimolecularOutput
    {Nread Nerase Nshift Nwrite : Network.{v, w} S}
    (hread : Nread.allAtMostBimolecularOutput)
    (herase : Nerase.allAtMostBimolecularOutput)
    (hshift : Nshift.allAtMostBimolecularOutput)
    (hwrite : Nwrite.allAtMostBimolecularOutput) :
    (phaseParallel4 Nread Nerase Nshift Nwrite).allAtMostBimolecularOutput := by
  exact
    (Network.parallel_allAtMostBimolecularOutput_iff
      (Nread.parallel Nerase) (Nshift.parallel Nwrite)).2
      ⟨
        (Network.parallel_allAtMostBimolecularOutput_iff Nread Nerase).2
          ⟨hread, herase⟩,
        (Network.parallel_allAtMostBimolecularOutput_iff Nshift Nwrite).2
          ⟨hshift, hwrite⟩
      ⟩

theorem phaseParallel4_allAtMostBimolecularFull
    {Nread Nerase Nshift Nwrite : Network.{v, w} S}
    (hread : Nread.allAtMostBimolecularFull)
    (herase : Nerase.allAtMostBimolecularFull)
    (hshift : Nshift.allAtMostBimolecularFull)
    (hwrite : Nwrite.allAtMostBimolecularFull) :
    (phaseParallel4 Nread Nerase Nshift Nwrite).allAtMostBimolecularFull := by
  exact
    (Network.parallel_allAtMostBimolecularFull_iff
      (Nread.parallel Nerase) (Nshift.parallel Nwrite)).2
      ⟨
        (Network.parallel_allAtMostBimolecularFull_iff Nread Nerase).2
          ⟨hread, herase⟩,
        (Network.parallel_allAtMostBimolecularFull_iff Nshift Nwrite).2
          ⟨hshift, hwrite⟩
      ⟩

end PhaseParallel

inductive FourPhaseSpecies (Q : Type u) where
  | ctrl :
      Q ->
      Phase4 ->
      Option Bool ->
      Option Bool ->
      Option Q ->
      FourPhaseSpecies Q
  | tape : FourPhaseSpecies Q
  | tapeBar : FourPhaseSpecies Q
deriving DecidableEq, Repr, Fintype

namespace FourPhaseSpecies

def ctrlOf {Q : Type u} (st : MicroState Q) : FourPhaseSpecies Q :=
  FourPhaseSpecies.ctrl
    st.q st.phase st.readSymbol st.pendingWrite st.pendingState

@[simp]
theorem ctrlOf_readPhase {Q : Type u} (q : Q) :
    ctrlOf (MicroState.readPhase q) =
      FourPhaseSpecies.ctrl q Phase4.read none none none := by
  rfl

@[simp]
theorem ctrlOf_afterRead {Q : Type u}
    (st : MicroState Q) (r w : Bool) (q' : Q) :
    ctrlOf (MicroState.afterRead st r w q') =
      FourPhaseSpecies.ctrl st.q Phase4.erase (some r) (some w) (some q') := by
  rfl

@[simp]
theorem ctrlOf_afterErase {Q : Type u} (st : MicroState Q) :
    ctrlOf (MicroState.afterErase st) =
      FourPhaseSpecies.ctrl
        st.q Phase4.shift st.readSymbol st.pendingWrite st.pendingState := by
  rfl

@[simp]
theorem ctrlOf_afterShift {Q : Type u} (st : MicroState Q) :
    ctrlOf (MicroState.afterShift st) =
      FourPhaseSpecies.ctrl
        st.q Phase4.write st.readSymbol st.pendingWrite st.pendingState := by
  rfl

@[simp]
theorem ctrlOf_afterWrite {Q : Type u} (q' : Q) :
    ctrlOf (MicroState.afterWrite q') =
      FourPhaseSpecies.ctrl q' Phase4.read none none none := by
  rfl

end FourPhaseSpecies

namespace FourPhaseEncoding

variable {Q : Type u} [DecidableEq Q]

abbrev Species (Q : Type u) :=
  FourPhaseSpecies Q

def maxTape (s : Nat) : Nat :=
  3 ^ (s + 1) - 1

def control (st : MicroState Q) : State (Species Q) :=
  State.single (FourPhaseSpecies.ctrlOf st) 1

def tape (n : Nat) : State (Species Q) :=
  State.single FourPhaseSpecies.tape n

def tapeBar {s : Nat} (n : Nat) : State (Species Q) :=
  State.single FourPhaseSpecies.tapeBar (maxTape s - n)

def readProbe (r : Bool) : Species Q :=
  if r then FourPhaseSpecies.tape else FourPhaseSpecies.tapeBar

def readProbeNeed (s : Nat) : Bool -> Nat
  | false => 3 ^ s
  | true => 2 * 3 ^ s

def enc {s : Nat} (c : MicroCfg Q s) : State (Species Q) :=
  State.add (State.add (control c.state) (tape c.tape))
    (tapeBar (s := s) c.tape)

@[simp]
theorem enc_ctrlOf {s : Nat} (c : MicroCfg Q s) :
    enc c (FourPhaseSpecies.ctrlOf c.state) = 1 := by
  cases c with
  | mk st m =>
      cases st
      simp [enc, control, tape, tapeBar, State.add, FourPhaseSpecies.ctrlOf]

@[simp]
theorem enc_tape {s : Nat} (c : MicroCfg Q s) :
    enc c FourPhaseSpecies.tape = c.tape := by
  simp [enc, control, tape, tapeBar, State.add, FourPhaseSpecies.ctrlOf]

@[simp]
theorem enc_tapeBar {s : Nat} (c : MicroCfg Q s) :
    enc c FourPhaseSpecies.tapeBar = maxTape s - c.tape := by
  simp [enc, control, tape, tapeBar, State.add, FourPhaseSpecies.ctrlOf]

theorem enc_covers_control {s : Nat} (c : MicroCfg Q s) :
    Covers (enc c) (State.single (FourPhaseSpecies.ctrlOf c.state) 1) := by
  exact Covers.single_iff.mpr (by simp)

theorem enc_covers_tape {s : Nat} (c : MicroCfg Q s) :
    Covers (enc c) (State.single FourPhaseSpecies.tape c.tape) := by
  exact Covers.single_iff.mpr (by simp)

theorem enc_covers_tapeBar {s : Nat} (c : MicroCfg Q s) :
    Covers (enc c)
      (State.single FourPhaseSpecies.tapeBar (maxTape s - c.tape)) := by
  exact Covers.single_iff.mpr (by simp)

theorem readProbeNeed_le_enc_readProbe_of_readMSB {s : Nat}
    (c : MicroCfg Q s) (r : Bool)
    (hr : r = Encoding.readMSB? s c.tape) :
    readProbeNeed s r <= enc c (readProbe r) := by
  cases r
  · have hfalse : Encoding.readMSB? s c.tape = false := by
      simpa using hr.symm
    have hlt : c.tape < 2 * 3 ^ s :=
      Encoding.readMSB?_eq_false.mp hfalse
    have hsucc : c.tape + 1 <= 2 * 3 ^ s :=
      Nat.succ_le_of_lt hlt
    have hmax : maxTape s = 3 * 3 ^ s - 1 := by
      unfold maxTape
      rw [pow_succ]
      ring_nf
    have hgoal : 3 ^ s <= maxTape s - c.tape := by
      apply Nat.le_sub_of_add_le
      rw [hmax]
      omega
    simpa [readProbe, readProbeNeed] using hgoal
  · have htrue : Encoding.readMSB? s c.tape = true := by
      simpa using hr.symm
    have hle : 2 * 3 ^ s <= c.tape :=
      Encoding.readMSB?_eq_true.mp htrue
    simpa [readProbe, readProbeNeed] using hle

@[simp]
theorem enc_ofCTM_tape {s : Nat} (c : Cfg Q Bool s) :
    enc (MicroCfg.ofCTM c) FourPhaseSpecies.tape =
      Encoding.base3Val c.tape := by
  simp [MicroCfg.ofCTM]

end FourPhaseEncoding

structure CanonicalFourPhaseModule
    {Q : Type u} [Fintype Q] [DecidableEq Q] {s : Nat}
    (M : Binary Q) where
  N : Network.{u, v} (FourPhaseSpecies Q)
  step_exec :
    forall {c c' : MicroCfg Q s},
      CanonicalMicroCfg c ->
      phaseStep? (s := s) M c = some c' ->
        exists is : List N.I,
          N.Exec (FourPhaseEncoding.enc c) (FourPhaseEncoding.enc c') is

namespace CanonicalFourPhaseModule

variable {Q : Type u} [Fintype Q] [DecidableEq Q] {s : Nat}
variable {M : Binary Q}

def toInvariantStepwiseRealization
    (G : CanonicalFourPhaseModule (s := s) M) :
    InvariantStepwiseRealization
      (fourPhaseSystem (s := s) M) G.N
      (CanonicalMicroCfg (Q := Q) (s := s)) where
  enc := FourPhaseEncoding.enc
  step_exec := by
    intro c c' hc hstep
    exact G.step_exec hc hstep
  step_preserves := by
    intro c c' hc hstep
    exact phaseStep?_preserves_canonical (s := s) M hc hstep

@[simp]
theorem toInvariantStepwiseRealization_enc
    (G : CanonicalFourPhaseModule (s := s) M) (c : MicroCfg Q s) :
    G.toInvariantStepwiseRealization.enc c = FourPhaseEncoding.enc c := by
  rfl

theorem exec_of_ctm_steps
    (G : CanonicalFourPhaseModule (s := s) M)
    {n : Nat} {cfg cfg' : Cfg Q Bool s}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg') :
    exists is : List G.N.I,
      G.N.Exec
        (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg))
        (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg')) is :=
  crn_exec_of_steps_canonical (s := s) M
    G.toInvariantStepwiseRealization h

theorem reaches_of_ctm_steps
    (G : CanonicalFourPhaseModule (s := s) M)
    {n : Nat} {cfg cfg' : Cfg Q Bool s}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg') :
    G.N.Reaches
      (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg))
      (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg')) :=
  crn_reaches_of_steps_canonical (s := s) M
    G.toInvariantStepwiseRealization h

end CanonicalFourPhaseModule

structure BoundedCanonicalFourPhaseModule
    {Q : Type u} [Fintype Q] [DecidableEq Q] {s : Nat}
    (M : Binary Q) where
  N : Network.{u, v} (FourPhaseSpecies Q)
  step_len_bound : Nat
  step_exec_bounded :
    forall {c c' : MicroCfg Q s},
      CanonicalMicroCfg c ->
      phaseStep? (s := s) M c = some c' ->
        exists is : List N.I,
          N.Exec (FourPhaseEncoding.enc c) (FourPhaseEncoding.enc c') is /\
            is.length <= step_len_bound

namespace BoundedCanonicalFourPhaseModule

variable {Q : Type u} [Fintype Q] [DecidableEq Q] {s : Nat}
variable {M : Binary Q}

def toCanonicalFourPhaseModule
    (G : BoundedCanonicalFourPhaseModule (s := s) M) :
    CanonicalFourPhaseModule (s := s) M where
  N := G.N
  step_exec := by
    intro c c' hc hstep
    rcases G.step_exec_bounded hc hstep with ⟨is, hExec, _hLen⟩
    exact ⟨is, hExec⟩

def toInvariantStepwiseRealization
    (G : BoundedCanonicalFourPhaseModule (s := s) M) :
    InvariantStepwiseRealization
      (fourPhaseSystem (s := s) M) G.N
      (CanonicalMicroCfg (Q := Q) (s := s)) :=
  G.toCanonicalFourPhaseModule.toInvariantStepwiseRealization

theorem exec_of_ctm_steps
    (G : BoundedCanonicalFourPhaseModule (s := s) M)
    {n : Nat} {cfg cfg' : Cfg Q Bool s}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg') :
    exists is : List G.N.I,
      G.N.Exec
        (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg))
        (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg')) is :=
  G.toCanonicalFourPhaseModule.exec_of_ctm_steps h

end BoundedCanonicalFourPhaseModule

structure FourPhaseStochasticReady
    {Q : Type u} [Fintype Q] [DecidableEq Q] {s : Nat}
    (M : Binary Q) where
  det : BoundedCanonicalFourPhaseModule.{u, v} (s := s) M
  allBimolecularInput : det.N.allBimolecularInput
  allUnitRate : det.N.allUnitRate
  equalRates : det.N.equalRates
  hasPositiveRates : det.N.hasPositiveRates

namespace FourPhaseStochasticReady

variable {Q : Type u} [Fintype Q] [DecidableEq Q] {s : Nat}
variable {M : Binary Q}

def toBoundedCanonicalFourPhaseModule
    (G : FourPhaseStochasticReady (s := s) M) :
    BoundedCanonicalFourPhaseModule (s := s) M :=
  G.det

def toInvariantStepwiseRealization
    (G : FourPhaseStochasticReady (s := s) M) :
    InvariantStepwiseRealization
      (fourPhaseSystem (s := s) M) G.det.N
      (CanonicalMicroCfg (Q := Q) (s := s)) :=
  G.det.toInvariantStepwiseRealization

end FourPhaseStochasticReady

end CTM

end Ripple.sCRNUniversality
