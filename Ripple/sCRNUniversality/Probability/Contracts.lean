import Ripple.sCRNUniversality.Probability.Basic

namespace Ripple.sCRNUniversality

namespace Probability

structure SuccessContract {Omega : Type u} (P : ProbSpec Omega) where
  success : Omega -> Prop
  error : ENNReal
  prob_error_le : P.Pr (ErrorEvent success) <= error

namespace SuccessContract

def errorEvent {Omega : Type u} {P : ProbSpec Omega}
    (C : SuccessContract P) : Event Omega :=
  ErrorEvent C.success

theorem errorEvent_mono {Omega : Type u} {P : ProbSpec Omega}
    (C : SuccessContract P) {success' : Omega -> Prop}
    (h : forall omega, C.success omega -> success' omega) :
    ErrorEvent success' ⊆ C.errorEvent := by
  intro omega hbad hsuccess
  exact hbad (h omega hsuccess)

theorem errorEvent_and_subset_union {Omega : Type u} {P : ProbSpec Omega}
    (C D : SuccessContract P) :
    ErrorEvent (fun omega => C.success omega /\ D.success omega) ⊆
      finUnion (Finset.univ : Finset Bool)
        (fun b => if b then C.errorEvent else D.errorEvent) := by
  intro omega hbad
  by_cases hC : C.success omega
  · refine ⟨false, by simp, ?_⟩
    exact fun hD => hbad ⟨hC, hD⟩
  · refine ⟨true, by simp, ?_⟩
    exact hC

def consequence {Omega : Type u} {P : ProbSpec Omega}
    (hP : ProbAxioms P) (C : SuccessContract P)
    (success' : Omega -> Prop)
    (h : forall omega, C.success omega -> success' omega) :
    SuccessContract P where
  success := success'
  error := C.error
  prob_error_le := by
    exact le_trans
      (hP.monotone (C.errorEvent_mono h))
      (by simpa [errorEvent] using C.prob_error_le)

noncomputable def «and» {Omega : Type u} {P : ProbSpec Omega}
    (hP : ProbAxioms.{u, 0} P) (C D : SuccessContract P) :
    SuccessContract P where
  success := fun omega => C.success omega /\ D.success omega
  error := C.error + D.error
  prob_error_le := by
    let E : Bool -> Event Omega :=
      fun b => if b then C.errorEvent else D.errorEvent
    have hsum :
        (Finset.univ : Finset Bool).sum (fun b => P.Pr (E b)) <=
          C.error + D.error := by
      simpa [E, errorEvent, add_comm, add_left_comm, add_assoc] using
        (add_le_add D.prob_error_le C.prob_error_le)
    exact le_trans
      (hP.monotone (C.errorEvent_and_subset_union D))
      (le_trans
        (hP.finUnion_le_sum (I := Bool) (Finset.univ : Finset Bool) E)
        hsum)

end SuccessContract

structure EventBound {Omega : Type u} (P : ProbSpec Omega) where
  event : Event Omega
  bound : ENNReal
  prob_le : P.Pr event <= bound

namespace SuccessContract

def ofEventBound {Omega : Type u} {P : ProbSpec Omega}
    (hP : ProbAxioms P) (success : Omega -> Prop)
    (B : EventBound P) (hsubset : ErrorEvent success ⊆ B.event) :
    SuccessContract P where
  success := success
  error := B.bound
  prob_error_le := le_trans (hP.monotone hsubset) B.prob_le

def ofEventBoundWitness {Omega : Type u} {P : ProbSpec Omega}
    (hP : ProbAxioms P)
    (witness success : Omega -> Prop)
    (B : EventBound P)
    (hsubset : ErrorEvent witness ⊆ B.event)
    (hwitness : forall omega, witness omega -> success omega) :
    SuccessContract P :=
  consequence hP (ofEventBound hP witness B hsubset)
    success hwitness

def weaken_bound {Omega : Type u} {P : ProbSpec Omega}
    (C : SuccessContract P) {error' : ENNReal}
    (herror : C.error <= error') : SuccessContract P where
  success := C.success
  error := error'
  prob_error_le := le_trans C.prob_error_le herror

def weaken_error {Omega : Type u} {P : ProbSpec Omega}
    (C : SuccessContract P) {error' : ENNReal}
    (herror : C.error <= error') : SuccessContract P :=
  C.weaken_bound herror

def of_subset {Omega : Type u} {P : ProbSpec Omega}
    (hP : ProbAxioms P) (C : SuccessContract P)
    (success' : Omega -> Prop)
    (hsubset : ErrorEvent success' ⊆ C.errorEvent) :
    SuccessContract P where
  success := success'
  error := C.error
  prob_error_le := by
    exact le_trans (hP.monotone hsubset)
      (by simpa [errorEvent] using C.prob_error_le)

theorem prob_le_of_subset {Omega : Type u} {P : ProbSpec Omega}
    (hP : ProbAxioms P) (C : SuccessContract P)
    {E : Event Omega}
    (hsubset : E ⊆ C.errorEvent) :
    P.Pr E <= C.error := by
  exact le_trans (hP.monotone hsubset)
    (by simpa [errorEvent] using C.prob_error_le)

end SuccessContract

def SuccessContract.toEventBound {Omega : Type u} {P : ProbSpec Omega}
    (C : SuccessContract P) : EventBound P where
  event := C.errorEvent
  bound := C.error
  prob_le := by
    simpa [SuccessContract.errorEvent] using C.prob_error_le

structure CompletionContract {Omega : Type u} (P : ProbSpec Omega) where
  done : Omega -> Prop
  bound : ENNReal
  prob_le : P.Pr (ErrorEvent done) <= bound

structure CorrectnessContract {Omega : Type u} (P : ProbSpec Omega) where
  done : Omega -> Prop
  correct : Omega -> Prop
  bound : ENNReal
  prob_le : P.Pr {omega | done omega /\ Not (correct omega)} <= bound

structure ModuleContract {Omega : Type u} (P : ProbSpec Omega) where
  done : Omega -> Prop
  correct : Omega -> Prop
  liveBound : ENNReal
  corrBound : ENNReal
  prob_not_done_le : P.Pr {omega | Not (done omega)} <= liveBound
  prob_done_not_correct_le : P.Pr {omega | done omega /\ Not (correct omega)} <= corrBound

structure DeadlineContract {Omega : Type u} (P : ProbSpec Omega) where
  finishTime : Omega -> Nat
  deadline : Nat
  bound : ENNReal
  prob_le : P.Pr {omega | deadline < finishTime omega} <= bound

namespace SuccessContract

def toCompletionContract {Omega : Type u} {P : ProbSpec Omega}
    (C : SuccessContract P) : CompletionContract P where
  done := C.success
  bound := C.error
  prob_le := C.prob_error_le

def toCompletionContract_of_implication
    {Omega : Type u} {P : ProbSpec Omega}
    (C : SuccessContract P)
    (hP : ProbAxioms P)
    (done : Omega -> Prop)
    (hdone : forall omega, C.success omega -> done omega) :
    CompletionContract P where
  done := done
  bound := C.error
  prob_le := by
    exact le_trans
      (hP.monotone (by
        intro omega hnotDone hsuccess
        exact hnotDone (hdone omega hsuccess)))
      C.prob_error_le

end SuccessContract

namespace CompletionContract

def notDone {Omega : Type u} {P : ProbSpec Omega}
    (C : CompletionContract P) : Event Omega :=
  ErrorEvent C.done

def toEventBound {Omega : Type u} {P : ProbSpec Omega}
    (C : CompletionContract P) : EventBound P where
  event := C.notDone
  bound := C.bound
  prob_le := C.prob_le

def toSuccessContract {Omega : Type u} {P : ProbSpec Omega}
    (C : CompletionContract P) : SuccessContract P where
  success := C.done
  error := C.bound
  prob_error_le := C.prob_le

def ofEventBound {Omega : Type u} {P : ProbSpec Omega}
    (hP : ProbAxioms P) (done : Omega -> Prop)
    (B : EventBound P) (hsubset : ErrorEvent done ⊆ B.event) :
    CompletionContract P where
  done := done
  bound := B.bound
  prob_le := le_trans (hP.monotone hsubset) B.prob_le

def ofEventBoundWitness {Omega : Type u} {P : ProbSpec Omega}
    (hP : ProbAxioms P)
    (witness done : Omega -> Prop)
    (B : EventBound P)
    (hsubset : ErrorEvent witness ⊆ B.event)
    (hwitness : forall omega, witness omega -> done omega) :
    CompletionContract P :=
  ofEventBound hP done B (by
    intro omega hnotDone
    apply hsubset
    intro hw
    exact hnotDone (hwitness omega hw))

def weaken_bound {Omega : Type u} {P : ProbSpec Omega}
    (C : CompletionContract P) {bound' : ENNReal}
    (hbound : C.bound <= bound') : CompletionContract P where
  done := C.done
  bound := bound'
  prob_le := le_trans C.prob_le hbound

def of_subset {Omega : Type u} {P : ProbSpec Omega}
    (hP : ProbAxioms P) (C : CompletionContract P)
    (done' : Omega -> Prop)
    (hsubset : ErrorEvent done' ⊆ C.notDone) :
    CompletionContract P where
  done := done'
  bound := C.bound
  prob_le := by
    exact le_trans (hP.monotone hsubset)
      (by simpa [notDone] using C.prob_le)

def consequence {Omega : Type u} {P : ProbSpec Omega}
    (hP : ProbAxioms P) (C : CompletionContract P)
    (done' : Omega -> Prop)
    (hdone : forall omega, C.done omega -> done' omega) :
    CompletionContract P :=
  of_subset hP C done' (by
    intro omega hbad
    change Not (C.done omega)
    intro hdone_old
    exact hbad (hdone omega hdone_old))

theorem prob_le_of_subset {Omega : Type u} {P : ProbSpec Omega}
    (hP : ProbAxioms P) (C : CompletionContract P)
    {E : Event Omega}
    (hsubset : E ⊆ C.notDone) :
    P.Pr E <= C.bound := by
  exact le_trans (hP.monotone hsubset)
    (by simpa [notDone] using C.prob_le)

end CompletionContract

namespace CorrectnessContract

def doneWrong {Omega : Type u} {P : ProbSpec Omega}
    (C : CorrectnessContract P) : Event Omega :=
  {omega | C.done omega /\ Not (C.correct omega)}

def toEventBound {Omega : Type u} {P : ProbSpec Omega}
    (C : CorrectnessContract P) : EventBound P where
  event := C.doneWrong
  bound := C.bound
  prob_le := by
    simpa [doneWrong] using C.prob_le

def toSuccessContract {Omega : Type u} {P : ProbSpec Omega}
    (C : CorrectnessContract P) : SuccessContract P where
  success := fun omega => C.done omega -> C.correct omega
  error := C.bound
  prob_error_le := by
    have hEq :
        ErrorEvent (fun omega => C.done omega -> C.correct omega) =
          {omega | C.done omega /\ Not (C.correct omega)} := by
      ext omega
      constructor
      · intro hbad
        by_cases hdone : C.done omega
        · exact ⟨hdone, fun hcorrect => hbad (fun _ => hcorrect)⟩
        · exact False.elim (hbad (fun hdone' => False.elim (hdone hdone')))
      · intro hbad hsuccess
        exact hbad.2 (hsuccess hbad.1)
    simpa [hEq] using C.prob_le

def ofEventBound {Omega : Type u} {P : ProbSpec Omega}
    (hP : ProbAxioms P) (done correct : Omega -> Prop)
    (B : EventBound P)
    (hsubset : {omega | done omega /\ Not (correct omega)} ⊆ B.event) :
    CorrectnessContract P where
  done := done
  correct := correct
  bound := B.bound
  prob_le := le_trans (hP.monotone hsubset) B.prob_le

def ofEventBoundWitness {Omega : Type u} {P : ProbSpec Omega}
    (hP : ProbAxioms P)
    (witness done correct : Omega -> Prop)
    (B : EventBound P)
    (hsubset : ErrorEvent witness ⊆ B.event)
    (hwitness :
      forall omega, witness omega -> done omega -> correct omega) :
    CorrectnessContract P :=
  ofEventBound hP done correct B (by
    intro omega hwrong
    apply hsubset
    intro hw
    exact hwrong.2 (hwitness omega hw hwrong.1))

def weaken_bound {Omega : Type u} {P : ProbSpec Omega}
    (C : CorrectnessContract P) {bound' : ENNReal}
    (hbound : C.bound <= bound') : CorrectnessContract P where
  done := C.done
  correct := C.correct
  bound := bound'
  prob_le := le_trans C.prob_le hbound

def of_subset {Omega : Type u} {P : ProbSpec Omega}
    (hP : ProbAxioms P) (C : CorrectnessContract P)
    (done' correct' : Omega -> Prop)
    (hsubset : {omega | done' omega /\ Not (correct' omega)} ⊆ C.doneWrong) :
    CorrectnessContract P where
  done := done'
  correct := correct'
  bound := C.bound
  prob_le := by
    exact le_trans (hP.monotone hsubset)
      (by simpa [doneWrong] using C.prob_le)

def consequence {Omega : Type u} {P : ProbSpec Omega}
    (hP : ProbAxioms P) (C : CorrectnessContract P)
    (done' correct' : Omega -> Prop)
    (hdone : forall omega, done' omega -> C.done omega)
    (hcorrect : forall omega, done' omega -> C.correct omega -> correct' omega) :
    CorrectnessContract P :=
  of_subset hP C done' correct' (by
    intro omega hbad
    exact ⟨hdone omega hbad.1, by
      intro hc
      exact hbad.2 (hcorrect omega hbad.1 hc)⟩)

def restrict_done {Omega : Type u} {P : ProbSpec Omega}
    (hP : ProbAxioms P) (C : CorrectnessContract P)
    (done' : Omega -> Prop)
    (hdone : forall omega, done' omega -> C.done omega) :
    CorrectnessContract P :=
  consequence hP C done' C.correct hdone (by
    intro _omega _hdone hc
    exact hc)

def weaken_correct {Omega : Type u} {P : ProbSpec Omega}
    (hP : ProbAxioms P) (C : CorrectnessContract P)
    (correct' : Omega -> Prop)
    (hcorrect : forall omega, C.done omega -> C.correct omega -> correct' omega) :
    CorrectnessContract P :=
  consequence hP C C.done correct'
    (by intro _omega hdone; exact hdone)
    hcorrect

theorem prob_le_of_subset {Omega : Type u} {P : ProbSpec Omega}
    (hP : ProbAxioms P) (C : CorrectnessContract P)
    {E : Event Omega}
    (hsubset : E ⊆ C.doneWrong) :
    P.Pr E <= C.bound := by
  exact le_trans (hP.monotone hsubset)
    (by simpa [doneWrong] using C.prob_le)

end CorrectnessContract

namespace SuccessContract

def toCorrectnessContract_of_implication
    {Omega : Type u} {P : ProbSpec Omega}
    (C : SuccessContract P)
    (hP : ProbAxioms P)
    (done correct : Omega -> Prop)
    (hcorrect :
      forall omega, C.success omega -> done omega -> correct omega) :
    CorrectnessContract P where
  done := done
  correct := correct
  bound := C.error
  prob_le := by
    exact le_trans
      (hP.monotone (by
        intro omega hwrong hsuccess
        exact hwrong.2
          (hcorrect omega hsuccess hwrong.1)))
      C.prob_error_le

def toDeadlineContract_of_implication
    {Omega : Type u} {P : ProbSpec Omega}
    (C : SuccessContract P)
    (hP : ProbAxioms P)
    (finishTime : Omega -> Nat) (deadline : Nat)
    (honTime :
      forall omega, C.success omega -> finishTime omega <= deadline) :
    DeadlineContract P where
  finishTime := finishTime
  deadline := deadline
  bound := C.error
  prob_le := by
    exact le_trans
      (hP.monotone (by
        intro omega hlate hsuccess
        exact not_lt_of_ge (honTime omega hsuccess) hlate))
      C.prob_error_le

end SuccessContract

namespace CompletionContract

def toCorrectnessContract_of_implication
    {Omega : Type u} {P : ProbSpec Omega}
    (C : CompletionContract P)
    (hP : ProbAxioms P)
    (done correct : Omega -> Prop)
    (hcorrect :
      forall omega, C.done omega -> done omega -> correct omega) :
    CorrectnessContract P :=
  C.toSuccessContract.toCorrectnessContract_of_implication
    hP done correct hcorrect

def toDeadlineContract_of_implication
    {Omega : Type u} {P : ProbSpec Omega}
    (C : CompletionContract P)
    (hP : ProbAxioms P)
    (finishTime : Omega -> Nat) (deadline : Nat)
    (honTime :
      forall omega, C.done omega -> finishTime omega <= deadline) :
    DeadlineContract P :=
  C.toSuccessContract.toDeadlineContract_of_implication
    hP finishTime deadline honTime

end CompletionContract

namespace DeadlineContract

def late {Omega : Type u} {P : ProbSpec Omega}
    (C : DeadlineContract P) : Event Omega :=
  {omega | C.deadline < C.finishTime omega}

def toEventBound {Omega : Type u} {P : ProbSpec Omega}
    (C : DeadlineContract P) : EventBound P where
  event := C.late
  bound := C.bound
  prob_le := by
    simpa [late] using C.prob_le

def ofEventBound {Omega : Type u} {P : ProbSpec Omega}
    (hP : ProbAxioms P) (finishTime : Omega -> Nat) (deadline : Nat)
    (B : EventBound P)
    (hsubset : {omega | deadline < finishTime omega} ⊆ B.event) :
    DeadlineContract P where
  finishTime := finishTime
  deadline := deadline
  bound := B.bound
  prob_le := le_trans (hP.monotone hsubset) B.prob_le

def ofEventBoundWitness {Omega : Type u} {P : ProbSpec Omega}
    (hP : ProbAxioms P)
    (witness : Omega -> Prop)
    (finishTime : Omega -> Nat) (deadline : Nat)
    (B : EventBound P)
    (hsubset : ErrorEvent witness ⊆ B.event)
    (hwitness : forall omega, witness omega -> finishTime omega <= deadline) :
    DeadlineContract P :=
  ofEventBound hP finishTime deadline B (by
    intro omega hlate
    apply hsubset
    intro hw
    exact not_lt_of_ge (hwitness omega hw) hlate)

def weaken_bound {Omega : Type u} {P : ProbSpec Omega}
    (C : DeadlineContract P) {bound' : ENNReal}
    (hbound : C.bound <= bound') : DeadlineContract P where
  finishTime := C.finishTime
  deadline := C.deadline
  bound := bound'
  prob_le := le_trans C.prob_le hbound

def of_subset {Omega : Type u} {P : ProbSpec Omega}
    (hP : ProbAxioms P) (C : DeadlineContract P)
    (finishTime' : Omega -> Nat) (deadline' : Nat)
    (hsubset : {omega | deadline' < finishTime' omega} ⊆ C.late) :
    DeadlineContract P where
  finishTime := finishTime'
  deadline := deadline'
  bound := C.bound
  prob_le := by
    exact le_trans (hP.monotone hsubset)
      (by simpa [late] using C.prob_le)

def consequence {Omega : Type u} {P : ProbSpec Omega}
    (hP : ProbAxioms P) (C : DeadlineContract P)
    (finishTime' : Omega -> Nat) (deadline' : Nat)
    (honTime :
      forall omega,
        C.finishTime omega <= C.deadline ->
          finishTime' omega <= deadline') :
    DeadlineContract P :=
  of_subset hP C finishTime' deadline' (by
    intro omega hlate
    by_contra hnotLateOld
    have hOldOnTime : C.finishTime omega <= C.deadline :=
      Nat.not_lt.mp hnotLateOld
    exact not_lt_of_ge (honTime omega hOldOnTime) hlate)

def monotone {Omega : Type u} {P : ProbSpec Omega}
    (hP : ProbAxioms P) (C : DeadlineContract P)
    (finishTime' : Omega -> Nat) (deadline' : Nat)
    (hdeadline : C.deadline <= deadline')
    (htime : forall omega, finishTime' omega <= C.finishTime omega) :
    DeadlineContract P :=
  of_subset hP C finishTime' deadline' (by
    intro omega hlate
    exact lt_of_le_of_lt hdeadline (lt_of_lt_of_le hlate (htime omega)))

def relax_deadline {Omega : Type u} {P : ProbSpec Omega}
    (hP : ProbAxioms P) (C : DeadlineContract P)
    {deadline' : Nat}
    (hdeadline : C.deadline <= deadline') :
    DeadlineContract P :=
  monotone hP C C.finishTime deadline' hdeadline (by
    intro _omega
    exact le_rfl)

def decrease_finishTime {Omega : Type u} {P : ProbSpec Omega}
    (hP : ProbAxioms P) (C : DeadlineContract P)
    (finishTime' : Omega -> Nat)
    (htime : forall omega, finishTime' omega <= C.finishTime omega) :
    DeadlineContract P :=
  monotone hP C finishTime' C.deadline le_rfl htime

theorem prob_le_of_subset {Omega : Type u} {P : ProbSpec Omega}
    (hP : ProbAxioms P) (C : DeadlineContract P)
    {E : Event Omega}
    (hsubset : E ⊆ C.late) :
    P.Pr E <= C.bound := by
  exact le_trans (hP.monotone hsubset)
    (by simpa [late] using C.prob_le)

def toCompletionContract {Omega : Type u} {P : ProbSpec Omega}
    (C : DeadlineContract P) : CompletionContract P where
  done := fun omega => C.finishTime omega <= C.deadline
  bound := C.bound
  prob_le := by
    simpa [ErrorEvent, not_le] using C.prob_le

def toSuccessContract {Omega : Type u} {P : ProbSpec Omega}
    (C : DeadlineContract P) : SuccessContract P where
  success := fun omega => C.finishTime omega <= C.deadline
  error := C.bound
  prob_error_le := by
    simpa [ErrorEvent, not_le, late] using C.prob_le

def toCorrectnessContract_of_implication
    {Omega : Type u} {P : ProbSpec Omega}
    (C : DeadlineContract P)
    (hP : ProbAxioms P)
    (done correct : Omega -> Prop)
    (hcorrect :
      forall omega,
        C.finishTime omega <= C.deadline -> done omega -> correct omega) :
    CorrectnessContract P :=
  C.toSuccessContract.toCorrectnessContract_of_implication
    hP done correct hcorrect

end DeadlineContract

namespace EventBound

def weaken_bound {Omega : Type u} {P : ProbSpec Omega}
    (B : EventBound P) {bound' : ENNReal}
    (hbound : B.bound <= bound') : EventBound P where
  event := B.event
  bound := bound'
  prob_le := le_trans B.prob_le hbound

def of_subset {Omega : Type u} {P : ProbSpec Omega}
    (hP : ProbAxioms P) (B : EventBound P) {E : Event Omega}
    (hE : E ⊆ B.event) : EventBound P where
  event := E
  bound := B.bound
  prob_le := le_trans (hP.monotone hE) B.prob_le

noncomputable def finUnion {Omega : Type u} {I : Type v} {P : ProbSpec Omega}
    (hP : ProbAxioms.{u, v} P)
    (s : Finset I) (B : I -> EventBound P) : EventBound P where
  event := Ripple.sCRNUniversality.Probability.finUnion s (fun i => (B i).event)
  bound := s.sum (fun i => (B i).bound)
  prob_le := by
    exact le_trans
      (hP.finUnion_le_sum (I := I) s (fun i => (B i).event))
      (Finset.sum_le_sum (fun i _hi => (B i).prob_le))

def binaryUnion {Omega : Type u} {P : ProbSpec Omega}
    (hP : ProbAxioms P) (B D : EventBound P) : EventBound P where
  event := B.event ∪ D.event
  bound := B.bound + D.bound
  prob_le := by
    exact le_trans
      (hP.union_le_add B.event D.event)
      (add_le_add B.prob_le D.prob_le)

theorem binaryUnion_prob_le {Omega : Type u} {P : ProbSpec Omega}
    (hP : ProbAxioms P) (B D : EventBound P) :
    P.Pr (B.event ∪ D.event) <= B.bound + D.bound :=
  (binaryUnion hP B D).prob_le

def binaryUnion_of_subsets {Omega : Type u} {P : ProbSpec Omega}
    (hP : ProbAxioms P) {E F : Event Omega}
    (B D : EventBound P)
    (hE : E ⊆ B.event) (hF : F ⊆ D.event) :
    EventBound P :=
  of_subset hP (binaryUnion hP B D) (E := E ∪ F) (by
    intro omega h
    rcases h with hEomega | hFomega
    · exact Or.inl (hE hEomega)
    · exact Or.inr (hF hFomega))

noncomputable def finUnion_of_subsets {Omega : Type u} {I : Type v}
    {P : ProbSpec Omega}
    (hP : ProbAxioms.{u, v} P) (s : Finset I) (E : I -> Event Omega)
    (B : I -> EventBound P)
    (hE : forall i, i ∈ s -> E i ⊆ (B i).event) : EventBound P where
  event := Ripple.sCRNUniversality.Probability.finUnion s E
  bound := s.sum (fun i => (B i).bound)
  prob_le := by
    exact le_trans
      (hP.finUnion_le_sum (I := I) s E)
      (Finset.sum_le_sum (fun i hi =>
        le_trans (hP.monotone (hE i hi)) (B i).prob_le))

def countUnion {Omega : Type u} {P : ProbSpec Omega}
    (B : Nat -> EventBound P) : Event Omega :=
  {omega | exists n, (B n).event omega}

theorem mono {Omega : Type u} {P : ProbSpec Omega}
    (hP : ProbAxioms P) (B : EventBound P) {E : Event Omega}
    (hE : E ⊆ B.event) :
    P.Pr E <= B.bound := by
  exact le_trans (hP.monotone hE) B.prob_le

theorem countUnion_le_of_prefixBounds {Omega : Type u} {P : ProbSpec Omega}
    (hP : ProbAxioms P)
    (B : Nat -> EventBound P) (epsilon : ENNReal)
    (hprefix : forall N, (Finset.range N).sum (fun n => (B n).bound) <= epsilon) :
    P.Pr (countUnion B) <= epsilon := by
  exact hP.countUnion_le_of_prefixBounds
    (fun n => (B n).event)
    (fun n => (B n).bound)
    epsilon
    (fun n => (B n).prob_le)
    hprefix

noncomputable def countUnion_of_prefixBounds {Omega : Type u} {P : ProbSpec Omega}
    (hP : ProbAxioms P)
    (B : Nat -> EventBound P) (epsilon : ENNReal)
    (hprefix : forall N, (Finset.range N).sum (fun n => (B n).bound) <= epsilon) :
    EventBound P where
  event := countUnion B
  bound := epsilon
  prob_le := countUnion_le_of_prefixBounds hP B epsilon hprefix

end EventBound

namespace ModuleContract

def failure {Omega : Type u} {P : ProbSpec Omega}
    (C : ModuleContract P) : Event Omega :=
  {omega | Not (C.done omega /\ C.correct omega)}

def liveBad {Omega : Type u} {P : ProbSpec Omega}
    (C : ModuleContract P) : Event Omega :=
  {omega | Not (C.done omega)}

def corrBad {Omega : Type u} {P : ProbSpec Omega}
    (C : ModuleContract P) : Event Omega :=
  {omega | C.done omega /\ Not (C.correct omega)}

def notDone {Omega : Type u} {P : ProbSpec Omega}
    (C : ModuleContract P) : Event Omega :=
  C.liveBad

def doneWrong {Omega : Type u} {P : ProbSpec Omega}
    (C : ModuleContract P) : Event Omega :=
  C.corrBad

theorem failure_subset_liveBad_union_corrBad {Omega : Type u} {P : ProbSpec Omega}
    (C : ModuleContract P) :
    C.failure ⊆ C.liveBad ∪ C.corrBad := by
  intro omega hFailure
  by_cases hDone : C.done omega
  · exact Or.inr ⟨hDone, fun hCorrect => hFailure ⟨hDone, hCorrect⟩⟩
  · exact Or.inl hDone

theorem liveBad_subset_failure {Omega : Type u} {P : ProbSpec Omega}
    (C : ModuleContract P) :
    C.liveBad ⊆ C.failure := by
  intro omega hLive hSuccess
  exact hLive hSuccess.1

theorem corrBad_subset_failure {Omega : Type u} {P : ProbSpec Omega}
    (C : ModuleContract P) :
    C.corrBad ⊆ C.failure := by
  intro omega hCorr hSuccess
  exact hCorr.2 hSuccess.2

theorem failure_subset_of_component_subsets {Omega : Type u} {P : ProbSpec Omega}
    (C : ModuleContract P) {E_live E_corr : Event Omega}
    (hlive : C.liveBad ⊆ E_live)
    (hcorr : C.corrBad ⊆ E_corr) :
    C.failure ⊆ E_live ∪ E_corr := by
  intro omega hFailure
  cases C.failure_subset_liveBad_union_corrBad hFailure with
  | inl hLive => exact Or.inl (hlive hLive)
  | inr hCorr => exact Or.inr (hcorr hCorr)

theorem failure_le {Omega : Type u} {P : ProbSpec Omega}
    (hP : ProbAxioms.{u, v} P) (C : ModuleContract P) :
    P.Pr C.failure <= C.liveBound + C.corrBound := by
  exact le_trans
    (hP.monotone C.failure_subset_liveBad_union_corrBad)
    (le_trans
      (hP.union_le_add C.liveBad C.corrBad)
      (add_le_add C.prob_not_done_le C.prob_done_not_correct_le))

def failureEventBound {Omega : Type u} {P : ProbSpec Omega}
    (hP : ProbAxioms.{u, v} P) (C : ModuleContract P) : EventBound P where
  event := C.failure
  bound := C.liveBound + C.corrBound
  prob_le := C.failure_le hP

def failureEventBound_of_componentBounds {Omega : Type u} {P : ProbSpec Omega}
    (hP : ProbAxioms P) (C : ModuleContract P)
    (B_live B_corr : EventBound P)
    (hlive : C.liveBad ⊆ B_live.event)
    (hcorr : C.corrBad ⊆ B_corr.event) : EventBound P :=
  EventBound.of_subset hP
    (EventBound.binaryUnion hP B_live B_corr)
    (C.failure_subset_of_component_subsets hlive hcorr)

def toSuccessContract {Omega : Type u} {P : ProbSpec Omega}
    (hP : ProbAxioms.{u, v} P) (C : ModuleContract P) :
    SuccessContract P where
  success := fun omega => C.done omega /\ C.correct omega
  error := C.liveBound + C.corrBound
  prob_error_le := by
    simpa [failure, ErrorEvent] using C.failure_le hP

def toSuccessContract_of_budget {Omega : Type u} {P : ProbSpec Omega}
    (hP : ProbAxioms.{u, v} P) (C : ModuleContract P)
    (epsilon : ENNReal)
    (hbudget : C.liveBound + C.corrBound <= epsilon) :
    SuccessContract P :=
  (C.toSuccessContract hP).weaken_bound hbudget

def consequenceSuccess {Omega : Type u} {P : ProbSpec Omega}
    (hP : ProbAxioms.{u, v} P)
    (C : ModuleContract P)
    (success : Omega -> Prop)
    (h : forall omega, C.done omega -> C.correct omega -> success omega) :
    SuccessContract P :=
  SuccessContract.consequence hP
    (C.toSuccessContract hP)
    success
    (by
      intro omega hdoneCorrect
      exact h omega hdoneCorrect.1 hdoneCorrect.2)

def ofCompletionAndCorrectness {Omega : Type u} {P : ProbSpec Omega}
    (hP : ProbAxioms P) (L : CompletionContract P)
    (K : CorrectnessContract P)
    (hdone : forall omega, L.done omega -> K.done omega) :
    ModuleContract P where
  done := L.done
  correct := K.correct
  liveBound := L.bound
  corrBound := K.bound
  prob_not_done_le := L.prob_le
  prob_done_not_correct_le := by
    exact le_trans
      (hP.monotone (by
        intro omega h
        exact ⟨hdone omega h.1, h.2⟩))
      K.prob_le

def ofCompletionAndSuccess {Omega : Type u} {P : ProbSpec Omega}
    (hP : ProbAxioms P) (L : CompletionContract P)
    (S : SuccessContract P) : ModuleContract P where
  done := L.done
  correct := S.success
  liveBound := L.bound
  corrBound := S.error
  prob_not_done_le := L.prob_le
  prob_done_not_correct_le := by
    exact le_trans
      (hP.monotone (by
        intro omega h
        exact h.2))
      S.prob_error_le

def ofDeadlineAndCorrectness {Omega : Type u} {P : ProbSpec Omega}
    (hP : ProbAxioms P) (D : DeadlineContract P)
    (K : CorrectnessContract P)
    (hdone :
      forall omega, D.finishTime omega <= D.deadline -> K.done omega) :
    ModuleContract P :=
  ofCompletionAndCorrectness hP D.toCompletionContract K hdone

def ofDeadlineAndSuccess {Omega : Type u} {P : ProbSpec Omega}
    (hP : ProbAxioms P) (D : DeadlineContract P)
    (S : SuccessContract P) : ModuleContract P :=
  ofCompletionAndSuccess hP D.toCompletionContract S

def ofEventBounds {Omega : Type u} {P : ProbSpec Omega}
    (hP : ProbAxioms P) (done correct : Omega -> Prop)
    (liveBound corrBound : ENNReal)
    (B_live B_corr : EventBound P)
    (hlive_bound : B_live.bound <= liveBound)
    (hcorr_bound : B_corr.bound <= corrBound)
    (hlive_sub : {omega | Not (done omega)} ⊆ B_live.event)
    (hcorr_sub : {omega | done omega /\ Not (correct omega)} ⊆ B_corr.event) :
    ModuleContract P where
  done := done
  correct := correct
  liveBound := liveBound
  corrBound := corrBound
  prob_not_done_le :=
    le_trans (le_trans (hP.monotone hlive_sub) B_live.prob_le) hlive_bound
  prob_done_not_correct_le :=
    le_trans (le_trans (hP.monotone hcorr_sub) B_corr.prob_le) hcorr_bound

def ofEventBounds_selfBounds {Omega : Type u} {P : ProbSpec Omega}
    (hP : ProbAxioms P) (done correct : Omega -> Prop)
    (B_live B_corr : EventBound P)
    (hlive_sub : {omega | Not (done omega)} ⊆ B_live.event)
    (hcorr_sub : {omega | done omega /\ Not (correct omega)} ⊆
      B_corr.event) :
    ModuleContract P :=
  ofEventBounds
    hP
    done
    correct
    B_live.bound
    B_corr.bound
    B_live
    B_corr
    le_rfl
    le_rfl
    hlive_sub
    hcorr_sub

def weaken_bounds {Omega : Type u} {P : ProbSpec Omega}
    (C : ModuleContract P) {liveBound' corrBound' : ENNReal}
    (hlive : C.liveBound <= liveBound')
    (hcorr : C.corrBound <= corrBound') : ModuleContract P where
  done := C.done
  correct := C.correct
  liveBound := liveBound'
  corrBound := corrBound'
  prob_not_done_le := le_trans C.prob_not_done_le hlive
  prob_done_not_correct_le := le_trans C.prob_done_not_correct_le hcorr

def liveEventBound {Omega : Type u} {P : ProbSpec Omega}
    (C : ModuleContract P) : EventBound P where
  event := C.liveBad
  bound := C.liveBound
  prob_le := by
    simpa [liveBad] using C.prob_not_done_le

def corrEventBound {Omega : Type u} {P : ProbSpec Omega}
    (C : ModuleContract P) : EventBound P where
  event := C.corrBad
  bound := C.corrBound
  prob_le := by
    simpa [corrBad] using C.prob_done_not_correct_le

def toCompletionContract {Omega : Type u} {P : ProbSpec Omega}
    (C : ModuleContract P) : CompletionContract P where
  done := C.done
  bound := C.liveBound
  prob_le := by
    simpa [ErrorEvent] using C.prob_not_done_le

def toCorrectnessContract {Omega : Type u} {P : ProbSpec Omega}
    (C : ModuleContract P) : CorrectnessContract P where
  done := C.done
  correct := C.correct
  bound := C.corrBound
  prob_le := C.prob_done_not_correct_le

def of_subset {Omega : Type u} {P : ProbSpec Omega}
    (hP : ProbAxioms P) (C : ModuleContract P)
    (done correct : Omega -> Prop)
    (hlive : {omega | Not (done omega)} ⊆ C.liveBad)
    (hcorr : {omega | done omega /\ Not (correct omega)} ⊆ C.corrBad) :
    ModuleContract P where
  done := done
  correct := correct
  liveBound := C.liveBound
  corrBound := C.corrBound
  prob_not_done_le := by
    exact le_trans (hP.monotone hlive)
      (by simpa [liveBad] using C.prob_not_done_le)
  prob_done_not_correct_le := by
    exact le_trans (hP.monotone hcorr)
      (by simpa [corrBad] using C.prob_done_not_correct_le)

def consequence {Omega : Type u} {P : ProbSpec Omega}
    (hP : ProbAxioms P) (C : ModuleContract P)
    (done correct : Omega -> Prop)
    (hdone_to : forall omega, C.done omega -> done omega)
    (hdone_from : forall omega, done omega -> C.done omega)
    (hcorrect : forall omega, done omega -> C.correct omega -> correct omega) :
    ModuleContract P :=
  of_subset hP C done correct
    (by
      intro omega hbad
      change Not (C.done omega)
      intro hdone_old
      exact hbad (hdone_to omega hdone_old))
    (by
      intro omega hbad
      exact ⟨hdone_from omega hbad.1, by
        intro hc
        exact hbad.2 (hcorrect omega hbad.1 hc)⟩)

def weaken_correct {Omega : Type u} {P : ProbSpec Omega}
    (hP : ProbAxioms P) (C : ModuleContract P)
    (correct' : Omega -> Prop)
    (hcorrect : forall omega, C.done omega -> C.correct omega -> correct' omega) :
    ModuleContract P :=
  consequence hP C C.done correct'
    (by intro _omega hdone; exact hdone)
    (by intro _omega hdone; exact hdone)
    hcorrect

def ofDeadlineAndOnTimeCorrect {Omega : Type u} {P : ProbSpec Omega}
    (D : DeadlineContract P) (correct : Omega -> Prop)
    (corrBound : ENNReal)
    (hcorr :
      P.Pr {omega | D.finishTime omega <= D.deadline /\ Not (correct omega)}
        <= corrBound) :
    ModuleContract P where
  done := fun omega => D.finishTime omega <= D.deadline
  correct := correct
  liveBound := D.bound
  corrBound := corrBound
  prob_not_done_le := by
    simpa [ErrorEvent, not_le] using D.prob_le
  prob_done_not_correct_le := hcorr

def ofDeadlineAndOnTimeCorrectEventBound
    {Omega : Type u} {P : ProbSpec Omega}
    (hP : ProbAxioms P)
    (D : DeadlineContract P) (correct : Omega -> Prop)
    (corrBound : ENNReal)
    (B_corr : EventBound P)
    (hcorr_bound : B_corr.bound <= corrBound)
    (hcorr_sub :
      {omega | D.finishTime omega <= D.deadline /\ Not (correct omega)}
        ⊆ B_corr.event) :
    ModuleContract P :=
  ofDeadlineAndOnTimeCorrect D correct corrBound
    (le_trans (le_trans (hP.monotone hcorr_sub) B_corr.prob_le)
      hcorr_bound)

noncomputable def finFailureEventBound {Omega : Type u} {I : Type v}
    {P : ProbSpec Omega}
    (hP : ProbAxioms.{u, v} P) (s : Finset I)
    (C : I -> ModuleContract P) : EventBound P :=
  EventBound.finUnion hP s (fun i => (C i).failureEventBound hP)

theorem fin_failure_le {Omega : Type u} {I : Type v} {P : ProbSpec Omega}
    (hP : ProbAxioms.{u, v} P) (s : Finset I)
    (C : I -> ModuleContract P) :
    P.Pr (finUnion s (fun i => (C i).failure)) <=
      s.sum (fun i => (C i).liveBound + (C i).corrBound) :=
  (finFailureEventBound hP s C).prob_le

theorem count_failure_le_of_prefixBounds {Omega : Type u} {P : ProbSpec Omega}
    (hP : ProbAxioms.{u, 0} P)
    (C : Nat -> ModuleContract P) (epsilon : ENNReal)
    (hprefix :
      forall N,
        (Finset.range N).sum
          (fun n => (C n).liveBound + (C n).corrBound) <= epsilon) :
    P.Pr (countUnion (fun n => (C n).failure)) <= epsilon := by
  exact hP.countUnion_le_of_prefixBounds
    (fun n => (C n).failure)
    (fun n => (C n).liveBound + (C n).corrBound)
    epsilon
    (fun n => (C n).failure_le hP)
    hprefix

noncomputable def countFailureEventBound_of_prefixBounds {Omega : Type u}
    {P : ProbSpec Omega}
    (hP : ProbAxioms.{u, 0} P)
    (C : Nat -> ModuleContract P) (epsilon : ENNReal)
    (hprefix :
      forall N,
        (Finset.range N).sum
          (fun n => (C n).liveBound + (C n).corrBound) <= epsilon) :
    EventBound P where
  event := countUnion (fun n => (C n).failure)
  bound := epsilon
  prob_le := count_failure_le_of_prefixBounds hP C epsilon hprefix

end ModuleContract

def allFinSuccess {Omega : Type u} {I : Type v} {P : ProbSpec Omega}
    (s : Finset I) (C : I -> SuccessContract P) : Omega -> Prop :=
  fun omega => Not ((finUnion s (fun i => ErrorEvent (C i).success)) omega)

def allNatSuccess {Omega : Type u} {P : ProbSpec Omega}
    (C : Nat -> SuccessContract P) : Omega -> Prop :=
  fun omega => Not ((countUnion (fun n => ErrorEvent (C n).success)) omega)

theorem allFinSuccess_iff {Omega : Type u} {I : Type v} {P : ProbSpec Omega}
    (s : Finset I) (C : I -> SuccessContract P) (omega : Omega) :
    allFinSuccess s C omega <->
      forall i, i ∈ s -> (C i).success omega := by
  constructor
  · intro hall i hi
    by_contra hbad
    exact hall ⟨i, hi, by simpa [ErrorEvent] using hbad⟩
  · intro hall hbad
    rcases hbad with ⟨i, hi, hfail⟩
    have hnot : Not ((C i).success omega) := by
      simpa [ErrorEvent] using hfail
    exact hnot (hall i hi)

theorem allNatSuccess_iff {Omega : Type u} {P : ProbSpec Omega}
    (C : Nat -> SuccessContract P) (omega : Omega) :
    allNatSuccess C omega <-> forall n, (C n).success omega := by
  constructor
  · intro hall n
    by_contra hbad
    exact hall ⟨n, by simpa [ErrorEvent] using hbad⟩
  · intro hall hbad
    rcases hbad with ⟨n, hfail⟩
    have hnot : Not ((C n).success omega) := by
      simpa [ErrorEvent] using hfail
    exact hnot (hall n)

theorem allFinSuccess_error_le {Omega : Type u} {I : Type v}
    (P : ProbSpec Omega) (hP : ProbAxioms.{u, v} P)
    (s : Finset I) (C : I -> SuccessContract P) :
    P.Pr (ErrorEvent (allFinSuccess s C)) <=
      s.sum (fun i => (C i).error) := by
  classical
  have hsubset :
      ErrorEvent (allFinSuccess s C) ⊆
        finUnion s (fun i => ErrorEvent (C i).success) := by
    intro omega h
    simpa [ErrorEvent, allFinSuccess] using h
  exact le_trans
    (hP.monotone hsubset)
    (le_trans
      (hP.finUnion_le_sum (I := I) s
        (fun i => ErrorEvent (C i).success))
      (Finset.sum_le_sum (fun i _hi => (C i).prob_error_le)))

namespace SuccessContract

noncomputable def finAll {Omega : Type u} {I : Type v} {P : ProbSpec Omega}
    (hP : ProbAxioms.{u, v} P) (s : Finset I)
    (C : I -> SuccessContract P) : SuccessContract P where
  success := allFinSuccess s C
  error := s.sum (fun i => (C i).error)
  prob_error_le := allFinSuccess_error_le P hP s C

theorem finAll_success_iff {Omega : Type u} {I : Type v} {P : ProbSpec Omega}
    (hP : ProbAxioms.{u, v} P) (s : Finset I)
    (C : I -> SuccessContract P) (omega : Omega) :
    (finAll hP s C).success omega <->
      forall i, i ∈ s -> (C i).success omega := by
  simpa [finAll] using allFinSuccess_iff s C omega

end SuccessContract

theorem allNatSuccess_error_le_of_prefixBounds {Omega : Type u}
    (P : ProbSpec Omega) (hP : ProbAxioms P)
    (C : Nat -> SuccessContract P)
    (epsilon : ENNReal)
    (hprefix : forall N, (Finset.range N).sum (fun n => (C n).error) <= epsilon) :
    P.Pr (ErrorEvent (allNatSuccess C)) <= epsilon := by
  classical
  have hsubset :
      ErrorEvent (allNatSuccess C) ⊆
        countUnion (fun n => ErrorEvent (C n).success) := by
    intro omega h
    simpa [ErrorEvent, allNatSuccess] using h
  exact le_trans
    (hP.monotone hsubset)
    (hP.countUnion_le_of_prefixBounds
      (fun n => ErrorEvent (C n).success)
      (fun n => (C n).error)
      epsilon
      (fun n => (C n).prob_error_le)
      hprefix)

namespace SuccessContract

noncomputable def countAll {Omega : Type u} {P : ProbSpec Omega}
    (hP : ProbAxioms P) (C : Nat -> SuccessContract P)
    (epsilon : ENNReal)
    (hprefix : forall N, (Finset.range N).sum (fun n => (C n).error) <= epsilon) :
    SuccessContract P where
  success := allNatSuccess C
  error := epsilon
  prob_error_le := allNatSuccess_error_le_of_prefixBounds P hP C epsilon hprefix

theorem countAll_success_iff {Omega : Type u} {P : ProbSpec Omega}
    (hP : ProbAxioms P) (C : Nat -> SuccessContract P)
    (epsilon : ENNReal)
    (hprefix : forall N, (Finset.range N).sum (fun n => (C n).error) <= epsilon)
    (omega : Omega) :
    (countAll hP C epsilon hprefix).success omega <->
      forall n, (C n).success omega := by
  simpa [countAll] using allNatSuccess_iff C omega

end SuccessContract

namespace ModuleContract

noncomputable def finAllSuccessContract {Omega : Type u} {I : Type v}
    {P : ProbSpec Omega}
    (hP : ProbAxioms.{u, v} P) (s : Finset I)
    (C : I -> ModuleContract P) : SuccessContract P :=
  SuccessContract.finAll hP s (fun i => (C i).toSuccessContract hP)

theorem finAllSuccessContract_success_iff {Omega : Type u} {I : Type v}
    {P : ProbSpec Omega}
    (hP : ProbAxioms.{u, v} P) (s : Finset I)
    (C : I -> ModuleContract P) (omega : Omega) :
    (finAllSuccessContract hP s C).success omega <->
      forall i, i ∈ s -> (C i).done omega /\ (C i).correct omega := by
  simpa [finAllSuccessContract, toSuccessContract] using
    (SuccessContract.finAll_success_iff
      (hP := hP) (s := s)
      (C := fun i => (C i).toSuccessContract hP)
      (omega := omega))

noncomputable def countAllSuccessContract {Omega : Type u}
    {P : ProbSpec Omega}
    (hP : ProbAxioms.{u, 0} P)
    (C : Nat -> ModuleContract P) (epsilon : ENNReal)
    (hprefix :
      forall N,
        (Finset.range N).sum
          (fun n => (C n).liveBound + (C n).corrBound) <= epsilon) :
    SuccessContract P :=
  SuccessContract.countAll hP
    (fun n => (C n).toSuccessContract hP)
    epsilon
    (by
      intro N
      simpa [toSuccessContract] using hprefix N)

theorem countAllSuccessContract_success_iff {Omega : Type u}
    {P : ProbSpec Omega}
    (hP : ProbAxioms.{u, 0} P)
    (C : Nat -> ModuleContract P) (epsilon : ENNReal)
    (hprefix :
      forall N,
        (Finset.range N).sum
          (fun n => (C n).liveBound + (C n).corrBound) <= epsilon)
    (omega : Omega) :
    (countAllSuccessContract hP C epsilon hprefix).success omega <->
      forall n, (C n).done omega /\ (C n).correct omega := by
  simpa [countAllSuccessContract, toSuccessContract] using
    (SuccessContract.countAll_success_iff
      (hP := hP)
      (C := fun n => (C n).toSuccessContract hP)
      (epsilon := epsilon)
      (hprefix := by
        intro N
        simpa [toSuccessContract] using hprefix N)
      (omega := omega))

end ModuleContract

structure ProbabilisticSimulationContract where
  errorBound : ENNReal
  expectedTimeBound : Nat

end Probability

end Ripple.sCRNUniversality
