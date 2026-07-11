import Ripple.sCRNUniversality.Computation.CTM.FourPhaseMacroSafety

namespace Ripple.sCRNUniversality

namespace CTM

universe u

namespace FourPhaseSpecies

variable {Q : Type u}

theorem ctrlOf_injective :
    Function.Injective (ctrlOf (Q := Q)) := by
  intro st₁ st₂ h
  cases st₁ with
  | mk q₁ p₁ r₁ w₁ s₁ =>
    cases st₂ with
    | mk q₂ p₂ r₂ w₂ s₂ =>
      simp [ctrlOf] at h
      rcases h with ⟨hq, hp, hr, hw, hs⟩
      subst hq; subst hp; subst hr; subst hw; subst hs
      rfl

end FourPhaseSpecies

namespace FourPhaseEncoding

variable {Q : Type u} [DecidableEq Q] {s : Nat}

theorem enc_ctrlOf_eq_of_pos (c : MicroCfg Q s) (st : MicroState Q)
    (hpos : 0 < enc c (FourPhaseSpecies.ctrlOf st)) :
    st = c.state := by
  by_contra hne
  have hne' : FourPhaseSpecies.ctrlOf st ≠ FourPhaseSpecies.ctrlOf c.state := by
    intro heq
    exact hne (FourPhaseSpecies.ctrlOf_injective heq)
  have hzero : enc c (FourPhaseSpecies.ctrlOf st) = 0 := by
    cases st with
    | mk q phase readSymbol pendingWrite pendingState =>
      exact enc_ctrl_eq_zero_of_ne_ctrlOf c hne'
  rw [hzero] at hpos
  exact Nat.lt_irrefl 0 hpos

theorem guardedBy_enabledAt_enc_state_eq (c : MicroCfg Q s)
    (rho : Reaction (FourPhaseSpecies Q)) (st : MicroState Q)
    (hGuard : rho.GuardedBy (FourPhaseSpecies.ctrlOf st))
    (hEnabled : rho.enabled (enc c)) :
    st = c.state := by
  apply enc_ctrlOf_eq_of_pos c st
  exact Nat.lt_of_lt_of_le Nat.zero_lt_one
    (le_trans hGuard (hEnabled _))

end FourPhaseEncoding

namespace FourPhaseQuasiDeterminism

variable {Q : Type u} [Fintype Q] [DecidableEq Q] {s : Nat}

private theorem read_enabledAt_state_eq
    (M : Binary Q) (c : MicroCfg Q s)
    (i : ReadNetwork.ReadIdx M)
    (hEnabled :
      (ReadNetwork.network (s := s) M).EnabledAt
        (FourPhaseEncoding.enc c) i) :
    c.state = MicroState.readPhase (ReadNetwork.ReadIdx.q i) :=
  (FourPhaseEncoding.guardedBy_enabledAt_enc_state_eq c _ _
    (ReadGadget.reaction_guardedBy (s := s) _ _ _ _) hEnabled).symm

private theorem read_enabledAt_determines_r
    (M : Binary Q) (c : MicroCfg Q s)
    (_hphase : c.state.phase = Phase4.read)
    (i : ReadNetwork.ReadIdx M)
    (hEnabled :
      (ReadNetwork.network (s := s) M).EnabledAt
        (FourPhaseEncoding.enc c) i) :
    ReadNetwork.ReadIdx.r i = Encoding.readMSB? s c.tape := by
  by_contra hne
  have hStateEq := read_enabledAt_state_eq M c i hEnabled
  have hEncRewrite :
      FourPhaseEncoding.enc c = FourPhaseEncoding.enc
        (ReadGadget.sourceCfg (s := s) (ReadNetwork.ReadIdx.q i) c.tape) := by
    simp only [FourPhaseEncoding.enc, FourPhaseEncoding.control,
      FourPhaseEncoding.tape, FourPhaseEncoding.tapeBar,
      ReadGadget.sourceCfg, hStateEq]
  rw [hEncRewrite, show Network.EnabledAt _ _ _ = _ from rfl] at hEnabled
  cases hr : ReadNetwork.ReadIdx.r i with
  | false =>
    have hMSBtrue : Encoding.readMSB? s c.tape = true := by
      cases hm : Encoding.readMSB? s c.tape with
      | false => rw [hr] at hne; exact absurd (hm ▸ rfl) hne
      | true => rfl
    have hTapeLe : 2 * 3 ^ s ≤ c.tape := Encoding.readMSB?_eq_true.mp hMSBtrue
    have h3pos : 0 < 3 ^ s := Nat.pos_of_ne_zero (by positivity)
    have hBarLt : FourPhaseEncoding.enc
        (ReadGadget.sourceCfg (s := s) (ReadNetwork.ReadIdx.q i) c.tape)
        FourPhaseSpecies.tapeBar < 3 ^ s := by
      rw [FourPhaseEncoding.enc_tapeBar]
      simp only [ReadGadget.sourceCfg]
      unfold FourPhaseEncoding.maxTape; omega
    have hReq : (ReadGadget.reaction (s := s) (ReadNetwork.ReadIdx.q i)
        false (ReadNetwork.ReadIdx.w i) (ReadNetwork.ReadIdx.qNext i)).Requires
        FourPhaseSpecies.tapeBar (3 ^ s) := by
      show 3 ^ s ≤ _
      simp [ReadGadget.reaction, ReadGadget.input, FourPhaseEncoding.readProbe,
        FourPhaseEncoding.readProbeNeed, State.add, State.single]
    have hRxnEq : (ReadNetwork.network (s := s) M).rxn i =
        ReadGadget.reaction (s := s) (ReadNetwork.ReadIdx.q i) false
          (ReadNetwork.ReadIdx.w i) (ReadNetwork.ReadIdx.qNext i) := by
      simp [ReadNetwork.network, hr]
    rw [Network.EnabledAt, hRxnEq] at hEnabled
    exact Reaction.not_enabled_of_requires_of_lt hReq hBarLt hEnabled
  | true =>
    have hMSBfalse : Encoding.readMSB? s c.tape = false := by
      cases hm : Encoding.readMSB? s c.tape with
      | true => rw [hr] at hne; exact absurd (hm ▸ rfl) hne
      | false => rfl
    have hTapeLt : c.tape < 2 * 3 ^ s := Encoding.readMSB?_eq_false.mp hMSBfalse
    have hTapeLt' : FourPhaseEncoding.enc
        (ReadGadget.sourceCfg (s := s) (ReadNetwork.ReadIdx.q i) c.tape)
        FourPhaseSpecies.tape < 2 * 3 ^ s := by
      rw [FourPhaseEncoding.enc_tape]
      simp only [ReadGadget.sourceCfg]; exact hTapeLt
    have hReq : (ReadGadget.reaction (s := s) (ReadNetwork.ReadIdx.q i)
        true (ReadNetwork.ReadIdx.w i) (ReadNetwork.ReadIdx.qNext i)).Requires
        FourPhaseSpecies.tape (2 * 3 ^ s) := by
      show 2 * 3 ^ s ≤ _
      simp [ReadGadget.reaction, ReadGadget.input, FourPhaseEncoding.readProbe,
        FourPhaseEncoding.readProbeNeed, State.add, State.single]
    have hRxnEq : (ReadNetwork.network (s := s) M).rxn i =
        ReadGadget.reaction (s := s) (ReadNetwork.ReadIdx.q i) true
          (ReadNetwork.ReadIdx.w i) (ReadNetwork.ReadIdx.qNext i) := by
      simp [ReadNetwork.network, hr]
    rw [Network.EnabledAt, hRxnEq] at hEnabled
    exact Reaction.not_enabled_of_requires_of_lt hReq hTapeLt' hEnabled

private theorem read_atMost_one_enabledAt_enc
    (M : Binary Q) (c : MicroCfg Q s)
    (hphase : c.state.phase = Phase4.read)
    (i j : ReadNetwork.ReadIdx M)
    (hi :
      (ReadNetwork.network (s := s) M).EnabledAt
        (FourPhaseEncoding.enc c) i)
    (hj :
      (ReadNetwork.network (s := s) M).EnabledAt
        (FourPhaseEncoding.enc c) j) :
    i = j := by
  have hsi := read_enabledAt_state_eq M c i hi
  have hsj := read_enabledAt_state_eq M c j hj
  have hri := read_enabledAt_determines_r M c hphase i hi
  have hrj := read_enabledAt_determines_r M c hphase j hj
  have hqEq : (ReadNetwork.ReadIdx.q i) = (ReadNetwork.ReadIdx.q j) := by
    have : MicroState.readPhase (ReadNetwork.ReadIdx.q i) =
        MicroState.readPhase (ReadNetwork.ReadIdx.q j) := hsi.symm.trans hsj
    simp [MicroState.readPhase] at this
    exact this
  have hrEq : (ReadNetwork.ReadIdx.r i) = (ReadNetwork.ReadIdx.r j) :=
    hri.trans hrj.symm
  have hDelta_i := ReadNetwork.ReadIdx.delta i
  have hDelta_j := ReadNetwork.ReadIdx.delta j
  rw [hqEq, hrEq] at hDelta_i
  rw [hDelta_i] at hDelta_j
  injection hDelta_j with hDelta_j
  cases i with
  | mk val₁ prop₁ =>
    cases j with
    | mk val₂ prop₂ =>
      congr 1
      cases val₁ with | mk q₁ r₁ w₁ qn₁ =>
      cases val₂ with | mk q₂ r₂ w₂ qn₂ =>
      simp only [ReadNetwork.ReadIdx.q] at hqEq
      simp only [ReadNetwork.ReadIdx.r] at hrEq
      obtain ⟨hw, hqn⟩ := Prod.mk.inj hDelta_j
      subst hqEq; subst hrEq; subst hw; subst hqn
      rfl

omit [Fintype Q] in
private theorem guardedBy_ctrl_unique
    (c : MicroCfg Q s) {I : Type*}
    (guard : I → MicroState Q) (rxn : I → Reaction (FourPhaseSpecies Q))
    (hGuarded : ∀ i, (rxn i).GuardedBy (FourPhaseSpecies.ctrlOf (guard i)))
    (hInj : ∀ i j, guard i = guard j → i = j)
    (i j : I)
    (hi : (rxn i).enabled (FourPhaseEncoding.enc c))
    (hj : (rxn j).enabled (FourPhaseEncoding.enc c)) :
    i = j := by
  have hsi := FourPhaseEncoding.guardedBy_enabledAt_enc_state_eq c _ _ (hGuarded i) hi
  have hsj := FourPhaseEncoding.guardedBy_enabledAt_enc_state_eq c _ _ (hGuarded j) hj
  exact hInj i j (hsi.trans hsj.symm)

private theorem erase_atMost_one_enabledAt_enc
    (c : MicroCfg Q s)
    (i j : EraseNetwork.Idx Q)
    (hi : (EraseNetwork.network Q s).EnabledAt (FourPhaseEncoding.enc c) i)
    (hj : (EraseNetwork.network Q s).EnabledAt (FourPhaseEncoding.enc c) j) :
    i = j := by
  apply guardedBy_ctrl_unique c
    (fun idx => EraseGadget.sourceState idx.q idx.r idx.w idx.qNext)
    (fun idx => EraseGadget.reaction (s := s) idx.q idx.r idx.w idx.qNext)
    (fun idx => EraseGadget.reaction_guardedBy (s := s) idx.q idx.r idx.w idx.qNext)
  · intro a b hab
    simp [EraseGadget.sourceState, MicroState.afterRead, MicroState.readPhase] at hab
    cases a; cases b; simp_all
  · exact hi
  · exact hj

private theorem shift_enabledAt_same_params
    (c : MicroCfg Q s)
    (i j : ShiftGadget.Idx Q s)
    (hi : (ShiftGadget.network Q s).EnabledAt (FourPhaseEncoding.enc c) i)
    (hj : (ShiftGadget.network Q s).EnabledAt (FourPhaseEncoding.enc c) j) :
    i.q = j.q ∧ i.r = j.r ∧ i.w = j.w ∧ i.qNext = j.qNext := by
  have hsi := FourPhaseEncoding.guardedBy_enabledAt_enc_state_eq c _ _
    (ShiftGadget.reaction_guardedBy (s := s) i) hi
  have hsj := FourPhaseEncoding.guardedBy_enabledAt_enc_state_eq c _ _
    (ShiftGadget.reaction_guardedBy (s := s) j) hj
  have heq : ShiftGadget.sourceState i.q i.r i.w i.qNext =
      ShiftGadget.sourceState j.q j.r j.w j.qNext :=
    hsi.trans hsj.symm
  simp [ShiftGadget.sourceState, MicroState.afterErase, MicroState.afterRead,
    MicroState.readPhase] at heq
  exact heq

private theorem write_atMost_one_enabledAt_enc
    (c : MicroCfg Q s)
    (i j : WriteNetwork.Idx Q)
    (hi : (WriteNetwork.network Q).EnabledAt (FourPhaseEncoding.enc c) i)
    (hj : (WriteNetwork.network Q).EnabledAt (FourPhaseEncoding.enc c) j) :
    i = j := by
  apply guardedBy_ctrl_unique c
    (fun idx => WriteGadget.sourceState idx.q idx.r idx.w idx.qNext)
    (fun idx => WriteGadget.reaction idx.q idx.r idx.w idx.qNext)
    (fun idx => WriteGadget.reaction_guardedBy idx.q idx.r idx.w idx.qNext)
  · intro a b hab
    simp [WriteGadget.sourceState, MicroState.afterShift, MicroState.afterErase,
      MicroState.afterRead, MicroState.readPhase] at hab
    cases a; cases b; simp_all
  · exact hi
  · exact hj

theorem atMost_one_enabledAt_enc_of_ne_shift
    (M : Binary Q) (c : MicroCfg Q s)
    (hphase : c.state.phase ≠ Phase4.shift)
    (i j : (FourPhaseMacroModule.network (s := s) M).I)
    (hi : (FourPhaseMacroModule.network (s := s) M).EnabledAt (FourPhaseEncoding.enc c) i)
    (hj : (FourPhaseMacroModule.network (s := s) M).EnabledAt (FourPhaseEncoding.enc c) j) :
    i = j := by
  cases hphase' : c.state.phase with
  | read =>
    rcases FourPhaseMacroSafety.enabledAt_isReadIndex_of_phase_read (s := s) M hphase' hi with ⟨ir, hir⟩
    rcases FourPhaseMacroSafety.enabledAt_isReadIndex_of_phase_read (s := s) M hphase' hj with ⟨jr, hjr⟩
    subst hir; subst hjr; congr 1; congr 1
    exact read_atMost_one_enabledAt_enc M c hphase' ir jr
      (by simpa [FourPhaseMacroModule.network] using hi)
      (by simpa [FourPhaseMacroModule.network] using hj)
  | erase =>
    rcases FourPhaseMacroSafety.enabledAt_isEraseIndex_of_phase_erase (s := s) M hphase' hi with ⟨ie, hie⟩
    rcases FourPhaseMacroSafety.enabledAt_isEraseIndex_of_phase_erase (s := s) M hphase' hj with ⟨je, hje⟩
    subst hie; subst hje; congr 1; congr 1
    exact erase_atMost_one_enabledAt_enc c ie je
      (by simpa [FourPhaseMacroModule.network] using hi)
      (by simpa [FourPhaseMacroModule.network] using hj)
  | shift => exact absurd hphase' hphase
  | write =>
    rcases FourPhaseMacroSafety.enabledAt_isWriteIndex_of_phase_write (s := s) M hphase' hi with ⟨iw, hiw⟩
    rcases FourPhaseMacroSafety.enabledAt_isWriteIndex_of_phase_write (s := s) M hphase' hj with ⟨jw, hjw⟩
    subst hiw; subst hjw; congr 1; congr 1
    exact write_atMost_one_enabledAt_enc c iw jw
      (by simpa [FourPhaseMacroModule.network] using hi)
      (by simpa [FourPhaseMacroModule.network] using hj)

theorem shift_enabledAt_enc_same_control
    (M : Binary Q) (c : MicroCfg Q s)
    (hphase : c.state.phase = Phase4.shift)
    (i j : (FourPhaseMacroModule.network (s := s) M).I)
    (hi : (FourPhaseMacroModule.network (s := s) M).EnabledAt (FourPhaseEncoding.enc c) i)
    (hj : (FourPhaseMacroModule.network (s := s) M).EnabledAt (FourPhaseEncoding.enc c) j) :
    exists (is_ js : ShiftGadget.Idx Q s),
      i = Sum.inr (Sum.inl is_) ∧
      j = Sum.inr (Sum.inl js) ∧
      is_.q = js.q ∧ is_.r = js.r ∧ is_.w = js.w ∧ is_.qNext = js.qNext := by
  rcases FourPhaseMacroSafety.enabledAt_isShiftIndex_of_phase_shift (s := s) M hphase hi with ⟨is_, his⟩
  rcases FourPhaseMacroSafety.enabledAt_isShiftIndex_of_phase_shift (s := s) M hphase hj with ⟨js, hjs⟩
  subst his; subst hjs
  exact ⟨is_, js, rfl, rfl,
    shift_enabledAt_same_params c is_ js
      (by simpa [FourPhaseMacroModule.network] using hi)
      (by simpa [FourPhaseMacroModule.network] using hj)⟩

end FourPhaseQuasiDeterminism

namespace FourPhaseAutonomous

variable {Q : Type u} [Fintype Q] [DecidableEq Q] {s : Nat}

def AutonomousStepDeterministic (N : Network S) (z : State S) : Prop :=
  forall i j z₁ z₂, N.StepAt i z z₁ → N.StepAt j z z₂ → z₁ = z₂

theorem deterministic_at_enc_of_ne_shift
    (M : Binary Q) (c : MicroCfg Q s)
    (hphase : c.state.phase ≠ Phase4.shift) :
    AutonomousStepDeterministic
      (FourPhaseMacroModule.network (s := s) M)
      (FourPhaseEncoding.enc c) := by
  intro i j z₁ z₂ hi hj
  have hiEq := FourPhaseQuasiDeterminism.atMost_one_enabledAt_enc_of_ne_shift
    M c hphase i j hi.enabled hj.enabled
  subst hiEq
  exact hi.unique hj

private theorem shift_reactions_same_ctrl_input
    (i j : ShiftGadget.Idx Q s)
    (hq : i.q = j.q) (hr : i.r = j.r) (hw : i.w = j.w) (hqn : i.qNext = j.qNext)
    (sp : FourPhaseSpecies Q) (hctrl : exists q p r w s,
      sp = FourPhaseSpecies.ctrl q p r w s) :
    (ShiftGadget.reaction i).l sp = (ShiftGadget.reaction j).l sp ∧
    (ShiftGadget.reaction i).r sp = (ShiftGadget.reaction j).r sp := by
  rcases hctrl with ⟨q', p', r', w', s', hsp⟩
  subst hsp
  simp only [ShiftGadget.reaction, ShiftGadget.input, ShiftGadget.output,
    State.add, State.single, FourPhaseSpecies.ctrlOf,
    ShiftGadget.sourceState, ShiftGadget.targetState,
    MicroState.afterErase, MicroState.afterRead, MicroState.readPhase,
    MicroState.afterShift]
  constructor <;> simp [hq, hr, hw, hqn]

theorem shift_step_preserves_ctrl
    (M : Binary Q) (c : MicroCfg Q s)
    (hphase : c.state.phase = Phase4.shift)
    (i j : (FourPhaseMacroModule.network (s := s) M).I)
    (z₁ z₂ : State (FourPhaseSpecies Q))
    (hi : (FourPhaseMacroModule.network (s := s) M).StepAt i
      (FourPhaseEncoding.enc c) z₁)
    (hj : (FourPhaseMacroModule.network (s := s) M).StepAt j
      (FourPhaseEncoding.enc c) z₂)
    (q' : Q) (p : Phase4) (r' : Option Bool) (w' : Option Bool) (s' : Option Q) :
    z₁ (FourPhaseSpecies.ctrl q' p r' w' s') =
      z₂ (FourPhaseSpecies.ctrl q' p r' w' s') := by
  rcases FourPhaseQuasiDeterminism.shift_enabledAt_enc_same_control
    M c hphase i j hi.enabled hj.enabled with
    ⟨is_, js, his, hjs, hq, hr, hw, hqn⟩
  subst his; subst hjs
  let sp := FourPhaseSpecies.ctrl q' p r' w' s'
  have ⟨hLEq, hREq⟩ := shift_reactions_same_ctrl_input is_ js hq hr hw hqn
    sp ⟨q', p, r', w', s', rfl⟩
  let rxn_i := (FourPhaseMacroModule.network (s := s) M).rxn (Sum.inr (Sum.inl is_))
  let rxn_j := (FourPhaseMacroModule.network (s := s) M).rxn (Sum.inr (Sum.inl js))
  have hz₁ : z₁ sp = FourPhaseEncoding.enc c sp - rxn_i.l sp + rxn_i.r sp := by
    have heq := hi.eq_fire
    subst heq; rfl
  have hz₂ : z₂ sp = FourPhaseEncoding.enc c sp - rxn_j.l sp + rxn_j.r sp := by
    have heq := hj.eq_fire
    subst heq; rfl
  have hLEq' : rxn_i.l sp = rxn_j.l sp := hLEq
  have hREq' : rxn_i.r sp = rxn_j.r sp := hREq
  rw [hz₁, hz₂, hLEq', hREq']

theorem autonomous_step_unique_of_ne_shift
    (M : Binary Q) (c : MicroCfg Q s)
    (hphase : c.state.phase ≠ Phase4.shift)
    (z₁ z₂ : State (FourPhaseSpecies Q))
    (h₁ : (FourPhaseMacroModule.network (s := s) M).Step
      (FourPhaseEncoding.enc c) z₁)
    (h₂ : (FourPhaseMacroModule.network (s := s) M).Step
      (FourPhaseEncoding.enc c) z₂) :
    z₁ = z₂ := by
  rcases h₁ with ⟨i, hi⟩
  rcases h₂ with ⟨j, hj⟩
  exact deterministic_at_enc_of_ne_shift M c hphase i j z₁ z₂ hi hj

theorem shift_step_ctrl_unique
    (M : Binary Q) (c : MicroCfg Q s)
    (hphase : c.state.phase = Phase4.shift)
    (z₁ z₂ : State (FourPhaseSpecies Q))
    (h₁ : (FourPhaseMacroModule.network (s := s) M).Step
      (FourPhaseEncoding.enc c) z₁)
    (h₂ : (FourPhaseMacroModule.network (s := s) M).Step
      (FourPhaseEncoding.enc c) z₂)
    (q' : Q) (p : Phase4) (r' : Option Bool) (w' : Option Bool) (s' : Option Q) :
    z₁ (FourPhaseSpecies.ctrl q' p r' w' s') =
      z₂ (FourPhaseSpecies.ctrl q' p r' w' s') := by
  rcases h₁ with ⟨i, hi⟩
  rcases h₂ with ⟨j, hj⟩
  exact shift_step_preserves_ctrl M c hphase i j z₁ z₂ hi hj q' p r' w' s'

end FourPhaseAutonomous

end CTM

end Ripple.sCRNUniversality
