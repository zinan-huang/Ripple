import Ripple.sCRNUniversality.Probability.Contracts

namespace Ripple.sCRNUniversality

namespace Probability

universe u v w

namespace PathEvent

/--
Lift a predicate on abstract paths to an event over the probability sample
space.

`observe` is intentionally abstract.  It can later be instantiated by a CTMC
sample-path observation map, a finite trace projection, a scheduler log, or
any other observation function. This file assumes no path-generation semantics.
-/
def lift {Omega : Type u} {Path : Type v}
    (observe : Omega -> Path) (A : Path -> Prop) : Event Omega :=
  {omega | A (observe omega)}

theorem lift_subset {Omega : Type u} {Path : Type v}
    {observe : Omega -> Path} {A B : Path -> Prop}
    (h : forall path, A path -> B path) :
    lift observe A ⊆ lift observe B := by
  intro omega hA
  exact h (observe omega) hA

/-- Avoid every bad path event in a finite index set. -/
def avoidsFin {Omega : Type u} {Path : Type v} {I : Type w}
    (observe : Omega -> Path) (s : Finset I)
    (bad : I -> Path -> Prop) : Omega -> Prop :=
  fun omega => forall i, i ∈ s -> Not (bad i (observe omega))

/-- Avoid every bad path event in a countable family indexed by `Nat`. -/
def avoidsAll {Omega : Type u} {Path : Type v}
    (observe : Omega -> Path)
    (bad : Nat -> Path -> Prop) : Omega -> Prop :=
  fun omega => forall n, Not (bad n (observe omega))

theorem error_avoidsFin_subset_finUnion
    {Omega : Type u} {Path : Type v} {I : Type w}
    (observe : Omega -> Path) (s : Finset I)
    (bad : I -> Path -> Prop) :
    ErrorEvent (avoidsFin observe s bad) ⊆
      finUnion s (fun i => lift observe (bad i)) := by
  classical
  intro omega hbad
  by_contra hnone
  apply hbad
  intro i hi hbi
  exact hnone ⟨i, hi, hbi⟩

theorem error_avoidsAll_subset_countUnion
    {Omega : Type u} {Path : Type v}
    (observe : Omega -> Path)
    (bad : Nat -> Path -> Prop) :
    ErrorEvent (avoidsAll observe bad) ⊆
      countUnion (fun n => lift observe (bad n)) := by
  classical
  intro omega hbad
  by_contra hnone
  apply hbad
  intro n hbn
  exact hnone ⟨n, hbn⟩

/--
Finite union bound for lifted path events, allowing each lifted event to be
included in a larger already-bounded event.
-/
noncomputable def finUnionBound_of_subsets
    {Omega : Type u} {Path : Type v} {I : Type w}
    {P : ProbSpec Omega}
    (hP : ProbAxioms.{u, w} P)
    (observe : Omega -> Path) (s : Finset I)
    (bad : I -> Path -> Prop)
    (B : I -> EventBound P)
    (hB : forall i, i ∈ s -> lift observe (bad i) ⊆ (B i).event) :
    EventBound P :=
  EventBound.finUnion_of_subsets hP s
    (fun i => lift observe (bad i))
    B
    hB

/--
Countable union bound for lifted path events under prefix-sum accounting.

This is only an event-union theorem. It does not assert that any path is
sampled from a CTMC or that a schedule occurs with any particular probability.
-/
noncomputable def countUnionBound_of_subsets
    {Omega : Type u} {Path : Type v} {P : ProbSpec Omega}
    (hP : ProbAxioms P)
    (observe : Omega -> Path)
    (bad : Nat -> Path -> Prop)
    (B : Nat -> EventBound P)
    (hB : forall n, lift observe (bad n) ⊆ (B n).event)
    (epsilon : ENNReal)
    (hprefix :
      forall N, (Finset.range N).sum (fun n => (B n).bound) <= epsilon) :
    EventBound P where
  event := countUnion (fun n => lift observe (bad n))
  bound := epsilon
  prob_le := by
    let B' : Nat -> EventBound P :=
      fun n => EventBound.of_subset hP (B n) (hB n)
    have hprefix' :
        forall N, (Finset.range N).sum (fun n => (B' n).bound) <=
          epsilon := by
      intro N
      simpa [B'] using hprefix N
    have hle :
        P.Pr (EventBound.countUnion B') <= epsilon :=
      EventBound.countUnion_le_of_prefixBounds hP B' epsilon hprefix'
    simpa [EventBound.countUnion, B', EventBound.of_subset, countUnion]
      using hle

/-- Success contract saying that all finitely indexed bad path events are avoided. -/
noncomputable def finAvoidsSuccess
    {Omega : Type u} {Path : Type v} {I : Type w}
    {P : ProbSpec Omega}
    (hP : ProbAxioms.{u, w} P)
    (observe : Omega -> Path) (s : Finset I)
    (bad : I -> Path -> Prop)
    (B : I -> EventBound P)
    (hB : forall i, i ∈ s -> lift observe (bad i) ⊆ (B i).event) :
    SuccessContract P :=
  SuccessContract.ofEventBound hP
    (avoidsFin observe s bad)
    (finUnionBound_of_subsets hP observe s bad B hB)
    (error_avoidsFin_subset_finUnion observe s bad)

theorem finAvoidsSuccess_iff
    {Omega : Type u} {Path : Type v} {I : Type w}
    {P : ProbSpec Omega}
    (hP : ProbAxioms.{u, w} P)
    (observe : Omega -> Path) (s : Finset I)
    (bad : I -> Path -> Prop)
    (B : I -> EventBound P)
    (hB : forall i, i ∈ s -> lift observe (bad i) ⊆ (B i).event)
    (omega : Omega) :
    (finAvoidsSuccess hP observe s bad B hB).success omega <->
      forall i, i ∈ s -> Not (bad i (observe omega)) := by
  rfl

/--
Success contract saying that every countably indexed bad path event is avoided,
under prefix-sum accounting.
-/
noncomputable def countAvoidsSuccess
    {Omega : Type u} {Path : Type v} {P : ProbSpec Omega}
    (hP : ProbAxioms P)
    (observe : Omega -> Path)
    (bad : Nat -> Path -> Prop)
    (B : Nat -> EventBound P)
    (hB : forall n, lift observe (bad n) ⊆ (B n).event)
    (epsilon : ENNReal)
    (hprefix :
      forall N, (Finset.range N).sum (fun n => (B n).bound) <= epsilon) :
    SuccessContract P :=
  SuccessContract.ofEventBound hP
    (avoidsAll observe bad)
    (countUnionBound_of_subsets hP observe bad B hB epsilon hprefix)
    (error_avoidsAll_subset_countUnion observe bad)

theorem countAvoidsSuccess_iff
    {Omega : Type u} {Path : Type v} {P : ProbSpec Omega}
    (hP : ProbAxioms P)
    (observe : Omega -> Path)
    (bad : Nat -> Path -> Prop)
    (B : Nat -> EventBound P)
    (hB : forall n, lift observe (bad n) ⊆ (B n).event)
    (epsilon : ENNReal)
    (hprefix :
      forall N, (Finset.range N).sum (fun n => (B n).bound) <= epsilon)
    (omega : Omega) :
    (countAvoidsSuccess hP observe bad B hB epsilon hprefix).success omega <->
      forall n, Not (bad n (observe omega)) := by
  rfl

/--
“Hit by deadline” as a pure path predicate. This does not say how the path is
generated or how likely a hit is.
-/
def hitBy {Omega : Type u} {Path : Type v}
    (observe : Omega -> Path)
    (hitAt : Nat -> Path -> Prop)
    (deadline : Nat) : Omega -> Prop :=
  fun omega => exists n, n <= deadline /\ hitAt n (observe omega)

def missBy {Omega : Type u} {Path : Type v}
    (observe : Omega -> Path)
    (hitAt : Nat -> Path -> Prop)
    (deadline : Nat) : Event Omega :=
  ErrorEvent (hitBy observe hitAt deadline)

end PathEvent

namespace SuccessContract

/--
Build a success contract for a path predicate from a bound on any event that
contains its failure event.
-/
def ofPathEventBound {Omega : Type u} {Path : Type v} {P : ProbSpec Omega}
    (hP : ProbAxioms P)
    (observe : Omega -> Path)
    (successPath : Path -> Prop)
    (B : EventBound P)
    (hsubset :
      ErrorEvent (fun omega => successPath (observe omega)) ⊆ B.event) :
    SuccessContract P :=
  SuccessContract.ofEventBound hP
    (fun omega => successPath (observe omega))
    B
    hsubset

/--
Build a success contract from a witness path predicate that implies the desired
path predicate.
-/
def ofPathWitnessEventBound {Omega : Type u} {Path : Type v} {P : ProbSpec Omega}
    (hP : ProbAxioms P)
    (observe : Omega -> Path)
    (witnessPath successPath : Path -> Prop)
    (B : EventBound P)
    (hsubset :
      ErrorEvent (fun omega => witnessPath (observe omega)) ⊆ B.event)
    (hwitness : forall path, witnessPath path -> successPath path) :
    SuccessContract P :=
  SuccessContract.ofEventBoundWitness hP
    (fun omega => witnessPath (observe omega))
    (fun omega => successPath (observe omega))
    B
    hsubset
    (fun omega h => hwitness (observe omega) h)

/--
Success contract for hitting a pure path predicate by a finite discrete
deadline.

The event bound is supplied externally as a bound on `PathEvent.missBy`. This
does not estimate that miss probability from any path-generation semantics.
-/
def ofHitByEventBound {Omega : Type u} {Path : Type v} {P : ProbSpec Omega}
    (hP : ProbAxioms P)
    (observe : Omega -> Path)
    (hitAt : Nat -> Path -> Prop)
    (deadline : Nat)
    (B : EventBound P)
    (hsubset : PathEvent.missBy observe hitAt deadline ⊆ B.event) :
    SuccessContract P :=
  SuccessContract.ofEventBound hP
    (PathEvent.hitBy observe hitAt deadline)
    B
    hsubset

end SuccessContract

namespace CompletionContract

def ofPathEventBound {Omega : Type u} {Path : Type v} {P : ProbSpec Omega}
    (hP : ProbAxioms P)
    (observe : Omega -> Path)
    (donePath : Path -> Prop)
    (B : EventBound P)
    (hsubset :
      ErrorEvent (fun omega => donePath (observe omega)) ⊆ B.event) :
    CompletionContract P :=
  CompletionContract.ofEventBound hP
    (fun omega => donePath (observe omega))
    B
    hsubset

def ofPathWitnessEventBound
    {Omega : Type u} {Path : Type v} {P : ProbSpec Omega}
    (hP : ProbAxioms P)
    (observe : Omega -> Path)
    (witnessPath donePath : Path -> Prop)
    (B : EventBound P)
    (hsubset :
      ErrorEvent (fun omega => witnessPath (observe omega)) ⊆ B.event)
    (hwitness : forall path, witnessPath path -> donePath path) :
    CompletionContract P :=
  CompletionContract.ofEventBoundWitness hP
    (fun omega => witnessPath (observe omega))
    (fun omega => donePath (observe omega))
    B
    hsubset
    (fun omega h => hwitness (observe omega) h)

/--
Completion by a finite discrete observation deadline.

The event bound is supplied externally. This file does not estimate its
probability from rates or clocks.
-/
def ofHitByEventBound {Omega : Type u} {Path : Type v} {P : ProbSpec Omega}
    (hP : ProbAxioms P)
    (observe : Omega -> Path)
    (hitAt : Nat -> Path -> Prop)
    (deadline : Nat)
    (B : EventBound P)
    (hsubset : PathEvent.missBy observe hitAt deadline ⊆ B.event) :
    CompletionContract P :=
  CompletionContract.ofEventBound hP
    (PathEvent.hitBy observe hitAt deadline)
    B
    hsubset

/--
Completion by a later deadline from an externally supplied bound on missing an
earlier deadline.
-/
def ofHitByEventBound_of_le_deadline
    {Omega : Type u} {Path : Type v} {P : ProbSpec Omega}
    (hP : ProbAxioms P)
    (observe : Omega -> Path)
    (hitAt : Nat -> Path -> Prop)
    {deadline0 deadline1 : Nat}
    (hdeadline : deadline0 <= deadline1)
    (B : EventBound P)
    (hsubset : PathEvent.missBy observe hitAt deadline0 ⊆ B.event) :
    CompletionContract P :=
  CompletionContract.ofHitByEventBound hP observe hitAt deadline1 B (by
    intro omega hmiss1
    apply hsubset
    intro hhit0
    apply hmiss1
    rcases hhit0 with ⟨n, hn, hhit⟩
    exact ⟨n, le_trans hn hdeadline, hhit⟩)

end CompletionContract

namespace CorrectnessContract

def ofPathEventBound {Omega : Type u} {Path : Type v} {P : ProbSpec Omega}
    (hP : ProbAxioms P)
    (observe : Omega -> Path)
    (donePath correctPath : Path -> Prop)
    (B : EventBound P)
    (hsubset :
      {omega | donePath (observe omega) /\ Not (correctPath (observe omega))}
        ⊆ B.event) :
    CorrectnessContract P :=
  CorrectnessContract.ofEventBound hP
    (fun omega => donePath (observe omega))
    (fun omega => correctPath (observe omega))
    B
    hsubset

def ofPathWitnessEventBound
    {Omega : Type u} {Path : Type v} {P : ProbSpec Omega}
    (hP : ProbAxioms P)
    (observe : Omega -> Path)
    (witnessPath donePath correctPath : Path -> Prop)
    (B : EventBound P)
    (hsubset :
      ErrorEvent (fun omega => witnessPath (observe omega)) ⊆ B.event)
    (hwitness :
      forall path, witnessPath path -> donePath path -> correctPath path) :
    CorrectnessContract P :=
  CorrectnessContract.ofEventBoundWitness hP
    (fun omega => witnessPath (observe omega))
    (fun omega => donePath (observe omega))
    (fun omega => correctPath (observe omega))
    B
    hsubset
    (fun omega hw hd => hwitness (observe omega) hw hd)

end CorrectnessContract

namespace DeadlineContract

/--
Deadline contract from a path-level finish-time function.

`finishTimePath` is just data extracted from a path. This does not assert
anything about CTMC hitting times.
-/
def ofPathEventBound {Omega : Type u} {Path : Type v} {P : ProbSpec Omega}
    (hP : ProbAxioms P)
    (observe : Omega -> Path)
    (finishTimePath : Path -> Nat)
    (deadline : Nat)
    (B : EventBound P)
    (hsubset :
      {omega | deadline < finishTimePath (observe omega)} ⊆ B.event) :
    DeadlineContract P :=
  DeadlineContract.ofEventBound hP
    (fun omega => finishTimePath (observe omega))
    deadline
    B
    hsubset

def ofPathWitnessEventBound
    {Omega : Type u} {Path : Type v} {P : ProbSpec Omega}
    (hP : ProbAxioms P)
    (observe : Omega -> Path)
    (witnessPath : Path -> Prop)
    (finishTimePath : Path -> Nat)
    (deadline : Nat)
    (B : EventBound P)
    (hsubset :
      ErrorEvent (fun omega => witnessPath (observe omega)) ⊆ B.event)
    (hwitness :
      forall path, witnessPath path -> finishTimePath path <= deadline) :
    DeadlineContract P :=
  DeadlineContract.ofEventBoundWitness hP
    (fun omega => witnessPath (observe omega))
    (fun omega => finishTimePath (observe omega))
    deadline
    B
    hsubset
    (fun omega h => hwitness (observe omega) h)

end DeadlineContract

namespace ModuleContract

/--
Module contract from path-level done/correct predicates and externally supplied
event bounds for liveness and correctness failures.
-/
def ofPathEventBounds {Omega : Type u} {Path : Type v} {P : ProbSpec Omega}
    (hP : ProbAxioms P)
    (observe : Omega -> Path)
    (donePath correctPath : Path -> Prop)
    (liveBound corrBound : ENNReal)
    (B_live B_corr : EventBound P)
    (hlive_bound : B_live.bound <= liveBound)
    (hcorr_bound : B_corr.bound <= corrBound)
    (hlive_sub :
      {omega | Not (donePath (observe omega))} ⊆ B_live.event)
    (hcorr_sub :
      {omega | donePath (observe omega) /\
        Not (correctPath (observe omega))} ⊆ B_corr.event) :
    ModuleContract P :=
  ModuleContract.ofEventBounds hP
    (fun omega => donePath (observe omega))
    (fun omega => correctPath (observe omega))
    liveBound
    corrBound
    B_live
    B_corr
    hlive_bound
    hcorr_bound
    hlive_sub
    hcorr_sub

/--
Module contract from path-level liveness and correctness witnesses.

The event bounds are supplied externally for failure of the witnesses.  This
adapter only transports those bounds through deterministic path implications.
-/
def ofPathWitnessEventBounds
    {Omega : Type u} {Path : Type v} {P : ProbSpec Omega}
    (hP : ProbAxioms P)
    (observe : Omega -> Path)
    (liveWitness donePath corrWitness correctPath : Path -> Prop)
    (liveBound corrBound : ENNReal)
    (B_live B_corr : EventBound P)
    (hlive_bound : B_live.bound <= liveBound)
    (hcorr_bound : B_corr.bound <= corrBound)
    (hlive_sub :
      ErrorEvent (fun omega => liveWitness (observe omega)) ⊆
        B_live.event)
    (hcorr_sub :
      ErrorEvent (fun omega => corrWitness (observe omega)) ⊆
        B_corr.event)
    (hlive : forall path, liveWitness path -> donePath path)
    (hcorr :
      forall path, corrWitness path -> donePath path -> correctPath path) :
    ModuleContract P :=
  ModuleContract.ofEventBounds hP
    (fun omega => donePath (observe omega))
    (fun omega => correctPath (observe omega))
    liveBound
    corrBound
    B_live
    B_corr
    hlive_bound
    hcorr_bound
    (by
      intro omega hnotDone
      apply hlive_sub
      intro hwitness
      exact hnotDone (hlive (observe omega) hwitness))
    (by
      intro omega hwrong
      apply hcorr_sub
      intro hwitness
      exact hwrong.2
        (hcorr (observe omega) hwitness hwrong.1))

/--
Module contract from a path-level deadline completion contract plus an
externally supplied bound on on-time-but-wrong paths.
-/
def ofPathDeadlineAndOnTimeCorrect
    {Omega : Type u} {Path : Type v} {P : ProbSpec Omega}
    (D : DeadlineContract P)
    (observe : Omega -> Path)
    (correctPath : Path -> Prop)
    (corrBound : ENNReal)
    (hcorr :
      P.Pr {omega | D.finishTime omega <= D.deadline /\
        Not (correctPath (observe omega))} <= corrBound) :
    ModuleContract P :=
  ModuleContract.ofDeadlineAndOnTimeCorrect D
    (fun omega => correctPath (observe omega))
    corrBound
    hcorr

/--
Module contract from a path-level deadline completion contract plus an
externally supplied event bound on on-time-but-wrong paths.
-/
def ofPathDeadlineAndOnTimeCorrectEventBound
    {Omega : Type u} {Path : Type v} {P : ProbSpec Omega}
    (hP : ProbAxioms P)
    (D : DeadlineContract P)
    (observe : Omega -> Path)
    (correctPath : Path -> Prop)
    (corrBound : ENNReal)
    (B_corr : EventBound P)
    (hcorr_bound : B_corr.bound <= corrBound)
    (hcorr_sub :
      {omega | D.finishTime omega <= D.deadline /\
        Not (correctPath (observe omega))} ⊆ B_corr.event) :
    ModuleContract P :=
  ModuleContract.ofPathDeadlineAndOnTimeCorrect
    D
    observe
    correctPath
    corrBound
    (le_trans
      (hP.monotone hcorr_sub)
      (le_trans B_corr.prob_le hcorr_bound))

end ModuleContract

end Probability

end Ripple.sCRNUniversality
