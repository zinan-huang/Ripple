import Ripple.sCRNUniversality.Computation.BimolecularRefinement
import Ripple.sCRNUniversality.Computation.CTM.FourPhaseConcreteModule
import Ripple.sCRNUniversality.Computation.CTM.FourPhaseEncodingTransferConcrete
import Ripple.sCRNUniversality.Computation.CTM.FourPhaseMacroModule
import Ripple.sCRNUniversality.Computation.CTM.FourPhaseNetworkFootprint

/-!
# Four-phase at-most-bimolecular forward refinement

This file is a deterministic adapter from the aggregate four-phase macro layer
to a concrete at-most-bimolecular network.

The key hypothesis is `GoodStepAt`/`GoodExec` from
`BimolecularNetworkRefinement`: only aggregate executions proved good/intended
are transported to concrete executions. The file does not prove that arbitrary
aggregate executions are refined unless `GoodStepAt` is instantiated as
ordinary `StepAt`.

The concrete network fields `allAtMostBimolecularInput` and `hasPositiveRates`
are static network-shape/rate predicates. They are not CTMC semantics, race
probability bounds, stochastic completion, expected-time, or high-probability
correctness claims.
-/

namespace Ripple.sCRNUniversality

namespace CTM

universe u v w x

structure BimolecularFourPhaseRefinement
    {Q : Type u} [Fintype Q] [DecidableEq Q] {s : Nat}
    {T : Type v} [Fintype T]
    (M : Binary Q) where
  agg : WellFormedFourPhaseModule.{u, w} (s := s) M
  N : Network.{v, x} T
  R : BimolecularNetworkRefinement agg.N N
  good_step_exec :
    forall {c c' : MicroCfg Q s},
      GadgetMicroCfgWF c ->
      phaseStep? (s := s) M c = some c' ->
        exists is : List agg.N.I,
          R.GoodExec
            (FourPhaseEncoding.enc c)
            (FourPhaseEncoding.enc c') is

/--
Safer alias for `BimolecularFourPhaseRefinement`.

This is a deterministic, forward-only refinement from intended aggregate
four-phase executions to concrete executions in an at-most-bimolecular network.
It is not a stochastic correctness theorem.
-/
abbrev AtMostBimolecularForwardFourPhaseRefinement
    {Q : Type u} [Fintype Q] [DecidableEq Q] {s : Nat}
    {T : Type v} [Fintype T]
    (M : Binary Q) :=
  BimolecularFourPhaseRefinement (s := s) (T := T) M

namespace BimolecularFourPhaseRefinement

variable {Q : Type u} [Fintype Q] [DecidableEq Q] {s : Nat}
variable {T : Type v} [Fintype T]
variable {M : Binary Q}

def encMicro
    (G : BimolecularFourPhaseRefinement (s := s) (T := T) M)
    (c : MicroCfg Q s) : State T :=
  G.R.enc (FourPhaseEncoding.enc c)

def encCTM
    (G : BimolecularFourPhaseRefinement (s := s) (T := T) M)
    (cfg : Cfg Q Bool s) : State T :=
  G.encMicro (MicroCfg.ofCTM cfg)

@[simp]
theorem encMicro_apply
    (G : BimolecularFourPhaseRefinement (s := s) (T := T) M)
    (c : MicroCfg Q s) :
    G.encMicro c = G.R.enc (FourPhaseEncoding.enc c) := by
  rfl

@[simp]
theorem encCTM_apply
    (G : BimolecularFourPhaseRefinement (s := s) (T := T) M)
    (cfg : Cfg Q Bool s) :
    G.encCTM cfg = G.encMicro (MicroCfg.ofCTM cfg) := by
  rfl

@[simp]
theorem encCTM_eq
    (G : BimolecularFourPhaseRefinement (s := s) (T := T) M)
    (cfg : Cfg Q Bool s) :
    G.encCTM cfg =
      G.R.enc (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg)) := by
  rfl

theorem concrete_allAtMostBimolecularInput
    (G : BimolecularFourPhaseRefinement (s := s) (T := T) M) :
    G.N.allAtMostBimolecularInput :=
  G.R.concrete_allAtMostBimolecularInput

theorem concrete_hasPositiveRates
    (G : BimolecularFourPhaseRefinement (s := s) (T := T) M) :
    G.N.hasPositiveRates :=
  G.R.concrete_hasPositiveRates

/-- Static at-most-bimolecular input-arity fact for the concrete network. -/
theorem concrete_static_allAtMostBimolecularInput
    (G : BimolecularFourPhaseRefinement (s := s) (T := T) M) :
    G.N.allAtMostBimolecularInput :=
  G.concrete_allAtMostBimolecularInput

/-- Static positive-rate fact for the concrete network; not a stochastic timing claim. -/
theorem concrete_static_hasPositiveRates
    (G : BimolecularFourPhaseRefinement (s := s) (T := T) M) :
    G.N.hasPositiveRates :=
  G.concrete_hasPositiveRates

theorem goodExec_of_phaseStep
    (G : BimolecularFourPhaseRefinement (s := s) (T := T) M)
    {c c' : MicroCfg Q s}
    (hc : GadgetMicroCfgWF c)
    (hstep : phaseStep? (s := s) M c = some c') :
    exists is : List G.agg.N.I,
      G.R.GoodExec
        (FourPhaseEncoding.enc c)
        (FourPhaseEncoding.enc c') is :=
  G.good_step_exec hc hstep

theorem aggregate_exec_of_phaseStep
    (G : BimolecularFourPhaseRefinement (s := s) (T := T) M)
    {c c' : MicroCfg Q s}
    (hc : GadgetMicroCfgWF c)
    (hstep : phaseStep? (s := s) M c = some c') :
    exists is : List G.agg.N.I,
      G.agg.N.Exec
        (FourPhaseEncoding.enc c)
        (FourPhaseEncoding.enc c') is := by
  rcases G.goodExec_of_phaseStep hc hstep with ⟨is, hGood⟩
  exact ⟨is, G.R.aggregate_exec_of_goodExec hGood⟩

theorem exec_of_phaseStep
    (G : BimolecularFourPhaseRefinement (s := s) (T := T) M)
    {c c' : MicroCfg Q s}
    (hc : GadgetMicroCfgWF c)
    (hstep : phaseStep? (s := s) M c = some c') :
    exists js : List G.N.I,
      G.N.Exec (G.encMicro c) (G.encMicro c') js := by
  rcases G.goodExec_of_phaseStep hc hstep with ⟨is, hGood⟩
  simpa [encMicro] using G.R.exec hGood

/--
Forward transport of an aggregate good execution to a concrete execution.

This is a wrapper around `G.R.exec`. It applies only to `GoodExec`, not to
arbitrary aggregate executions.
-/
theorem forward_exec_of_goodExec
    (G : BimolecularFourPhaseRefinement (s := s) (T := T) M)
    {z z' : State (FourPhaseSpecies Q)} {is : List G.agg.N.I}
    (hGood : G.R.GoodExec z z' is) :
    exists js : List G.N.I,
      G.N.Exec (G.R.enc z) (G.R.enc z') js :=
  G.R.exec hGood

/-- Forward transport of aggregate good reachability to concrete reachability. -/
theorem forward_reaches_of_goodReaches
    (G : BimolecularFourPhaseRefinement (s := s) (T := T) M)
    {z z' : State (FourPhaseSpecies Q)}
    (hGood : G.R.GoodReaches z z') :
    G.N.Reaches (G.R.enc z) (G.R.enc z') :=
  G.R.reaches hGood

theorem goodReaches_of_goodExec
    (G : BimolecularFourPhaseRefinement (s := s) (T := T) M)
    {z z' : State (FourPhaseSpecies Q)} {is : List G.agg.N.I}
    (hGood : G.R.GoodExec z z' is) :
    G.R.GoodReaches z z' :=
  ⟨is, hGood⟩

def aggregateIntendedSchedule_of_goodExec
    (G : BimolecularFourPhaseRefinement (s := s) (T := T) M)
    {z z' : State (FourPhaseSpecies Q)} {is : List G.agg.N.I}
    (hGood : G.R.GoodExec z z' is) :
    G.agg.N.IntendedSchedule z z' where
  schedule := is
  exec := G.R.aggregate_exec_of_goodExec hGood

@[simp]
theorem aggregateIntendedSchedule_of_goodExec_schedule
    (G : BimolecularFourPhaseRefinement (s := s) (T := T) M)
    {z z' : State (FourPhaseSpecies Q)} {is : List G.agg.N.I}
    (hGood : G.R.GoodExec z z' is) :
    (G.aggregateIntendedSchedule_of_goodExec hGood).schedule = is := by
  rfl

theorem aggregateIntendedSchedule_goodExec
    (G : BimolecularFourPhaseRefinement (s := s) (T := T) M)
    {z z' : State (FourPhaseSpecies Q)} {is : List G.agg.N.I}
    (hGood : G.R.GoodExec z z' is) :
    G.R.GoodExec z z'
      (G.aggregateIntendedSchedule_of_goodExec hGood).schedule := by
  simpa using hGood

/--
Intended aggregate good execution for one successful four-phase micro-step.

This wrapper keeps the intended/good schedule nature visible.
-/
theorem intended_goodExec_of_phaseStep
    (G : BimolecularFourPhaseRefinement (s := s) (T := T) M)
    {c c' : MicroCfg Q s}
    (hc : GadgetMicroCfgWF c)
    (hstep : phaseStep? (s := s) M c = some c') :
    exists is : List G.agg.N.I,
      G.R.GoodExec
        (FourPhaseEncoding.enc c)
        (FourPhaseEncoding.enc c') is :=
  G.goodExec_of_phaseStep hc hstep

/-- Concrete forward execution for one successful four-phase micro-step. -/
theorem forward_exec_of_phaseStep
    (G : BimolecularFourPhaseRefinement (s := s) (T := T) M)
    {c c' : MicroCfg Q s}
    (hc : GadgetMicroCfgWF c)
    (hstep : phaseStep? (s := s) M c = some c') :
    exists js : List G.N.I,
      G.N.Exec (G.encMicro c) (G.encMicro c') js :=
  G.exec_of_phaseStep hc hstep

noncomputable def concreteIntendedSchedule_of_phaseStep
    (G : BimolecularFourPhaseRefinement (s := s) (T := T) M)
    {c c' : MicroCfg Q s}
    (hc : GadgetMicroCfgWF c)
    (hstep : phaseStep? (s := s) M c = some c') :
    G.N.IntendedSchedule (G.encMicro c) (G.encMicro c') where
  schedule := Classical.choose (G.exec_of_phaseStep hc hstep)
  exec := Classical.choose_spec (G.exec_of_phaseStep hc hstep)

theorem exec_of_concreteIntendedSchedule_of_phaseStep
    (G : BimolecularFourPhaseRefinement (s := s) (T := T) M)
    {c c' : MicroCfg Q s}
    (hc : GadgetMicroCfgWF c)
    (hstep : phaseStep? (s := s) M c = some c') :
    G.N.Exec (G.encMicro c) (G.encMicro c')
      (G.concreteIntendedSchedule_of_phaseStep hc hstep).schedule :=
  (G.concreteIntendedSchedule_of_phaseStep hc hstep).exec

theorem goodReaches_of_phaseStep
    (G : BimolecularFourPhaseRefinement (s := s) (T := T) M)
    {c c' : MicroCfg Q s}
    (hc : GadgetMicroCfgWF c)
    (hstep : phaseStep? (s := s) M c = some c') :
    G.R.GoodReaches
      (FourPhaseEncoding.enc c)
      (FourPhaseEncoding.enc c') := by
  rcases G.goodExec_of_phaseStep hc hstep with ⟨is, hGood⟩
  exact ⟨is, hGood⟩

theorem goodCoverableFrom_of_phaseStep_covers
    (G : BimolecularFourPhaseRefinement (s := s) (T := T) M)
    {c c' : MicroCfg Q s}
    {target : State (FourPhaseSpecies Q)}
    (hc : GadgetMicroCfgWF c)
    (hstep : phaseStep? (s := s) M c = some c')
    (hCovers : Covers (FourPhaseEncoding.enc c') target) :
    G.R.GoodCoverableFrom (FourPhaseEncoding.enc c) target :=
  G.R.goodCoverableFrom_of_goodReaches_covers
    (G.goodReaches_of_phaseStep hc hstep)
    hCovers

theorem goodCoverableFrom_of_phaseStep_of_le
    (G : BimolecularFourPhaseRefinement (s := s) (T := T) M)
    {c c' : MicroCfg Q s}
    {target : State (FourPhaseSpecies Q)}
    (hc : GadgetMicroCfgWF c)
    (hstep : phaseStep? (s := s) M c = some c')
    (hTarget :
      forall species,
        target species <= FourPhaseEncoding.enc c' species) :
    G.R.GoodCoverableFrom (FourPhaseEncoding.enc c) target :=
  G.goodCoverableFrom_of_phaseStep_covers hc hstep hTarget

theorem aggregateIntendedSchedule_of_phaseStep
    (G : BimolecularFourPhaseRefinement (s := s) (T := T) M)
    {c c' : MicroCfg Q s}
    (hc : GadgetMicroCfgWF c)
    (hstep : phaseStep? (s := s) M c = some c') :
    exists I :
      G.agg.N.IntendedSchedule
        (FourPhaseEncoding.enc c)
        (FourPhaseEncoding.enc c'),
      G.R.GoodExec
        (FourPhaseEncoding.enc c)
        (FourPhaseEncoding.enc c')
        I.schedule := by
  rcases G.goodExec_of_phaseStep hc hstep with ⟨is, hGood⟩
  refine ⟨G.aggregateIntendedSchedule_of_goodExec hGood, ?_⟩
  simpa using hGood

/-- Concrete forward reachability for one successful four-phase micro-step. -/
theorem forward_reaches_of_phaseStep
    (G : BimolecularFourPhaseRefinement (s := s) (T := T) M)
    {c c' : MicroCfg Q s}
    (hc : GadgetMicroCfgWF c)
    (hstep : phaseStep? (s := s) M c = some c') :
    G.N.Reaches (G.encMicro c) (G.encMicro c') := by
  simpa [encMicro] using
    G.forward_reaches_of_goodReaches
      (G.goodReaches_of_phaseStep hc hstep)

theorem concreteIntendedSchedule_reaches_of_phaseStep
    (G : BimolecularFourPhaseRefinement (s := s) (T := T) M)
    {c c' : MicroCfg Q s}
    (hc : GadgetMicroCfgWF c)
    (hstep : phaseStep? (s := s) M c = some c') :
    G.N.Reaches (G.encMicro c) (G.encMicro c') :=
  (G.concreteIntendedSchedule_of_phaseStep hc hstep).reaches

theorem state_after_phaseStep_of_concreteIntendedWinsRaceAt
    (G : BimolecularFourPhaseRefinement (s := s) (T := T) M)
    {c c' : MicroCfg Q s}
    {path : G.N.Path}
    {Bad : G.N.BadIndexSet}
    {t : Nat}
    (hc : GadgetMicroCfgWF c)
    (hstep : phaseStep? (s := s) M c = some c')
    (hwin :
      path.IntendedWinsRaceAt Bad t
        (G.concreteIntendedSchedule_of_phaseStep hc hstep)) :
    path.state
        (t + (G.concreteIntendedSchedule_of_phaseStep hc hstep).firingCount) =
      G.encMicro c' := by
  simpa [Network.IntendedSchedule.firingCount] using
    path.state_after_intendedWinsRaceAt Bad
      (G.concreteIntendedSchedule_of_phaseStep hc hstep)
      hwin

theorem coverableFrom_of_phaseStep_covers
    (G : BimolecularFourPhaseRefinement (s := s) (T := T) M)
    {c c' : MicroCfg Q s} {target : State T}
    (hc : GadgetMicroCfgWF c)
    (hstep : phaseStep? (s := s) M c = some c')
    (hCovers : Covers (G.encMicro c') target) :
    G.N.CoverableFrom (G.encMicro c) target :=
  Network.coverable_of_reaches_of_covers
    (G.forward_reaches_of_phaseStep hc hstep)
    hCovers

theorem coverableFrom_of_phaseStep_of_le
    (G : BimolecularFourPhaseRefinement (s := s) (T := T) M)
    {c c' : MicroCfg Q s} {target : State T}
    (hc : GadgetMicroCfgWF c)
    (hstep : phaseStep? (s := s) M c = some c')
    (hTarget : forall species, target species <= G.encMicro c' species) :
    G.N.CoverableFrom (G.encMicro c) target :=
  G.coverableFrom_of_phaseStep_covers hc hstep hTarget

theorem coverable_of_phaseStep_covers
    (G : BimolecularFourPhaseRefinement (s := s) (T := T) M)
    {c c' : MicroCfg Q s} {target : State T}
    (hc : GadgetMicroCfgWF c)
    (hstep : phaseStep? (s := s) M c = some c')
    (hCovers : Covers (G.encMicro c') target) :
    G.N.CoverableFrom (G.encMicro c) target :=
  G.coverableFrom_of_phaseStep_covers hc hstep hCovers

theorem coverable_of_phaseStep_of_le
    (G : BimolecularFourPhaseRefinement (s := s) (T := T) M)
    {c c' : MicroCfg Q s} {target : State T}
    (hc : GadgetMicroCfgWF c)
    (hstep : phaseStep? (s := s) M c = some c')
    (hTarget : forall species, target species <= G.encMicro c' species) :
    G.N.CoverableFrom (G.encMicro c) target :=
  G.coverableFrom_of_phaseStep_of_le hc hstep hTarget

theorem speciesCoverableFrom_of_phaseStep_coord
    [DecidableEq T]
    (G : BimolecularFourPhaseRefinement (s := s) (T := T) M)
    {c c' : MicroCfg Q s}
    {species : T} {amount : Nat}
    (hc : GadgetMicroCfgWF c)
    (hstep : phaseStep? (s := s) M c = some c')
    (hamount : amount <= G.encMicro c' species) :
    G.N.SpeciesCoverableFrom (G.encMicro c) species amount :=
  Network.speciesCoverableFrom_of_reaches_coord
    (G.forward_reaches_of_phaseStep hc hstep)
    hamount

theorem speciesCoverableFrom_one_of_phaseStep_pos
    [DecidableEq T]
    (G : BimolecularFourPhaseRefinement (s := s) (T := T) M)
    {c c' : MicroCfg Q s}
    {species : T}
    (hc : GadgetMicroCfgWF c)
    (hstep : phaseStep? (s := s) M c = some c')
    (hpos : 0 < G.encMicro c' species) :
    G.N.SpeciesCoverableFrom (G.encMicro c) species :=
  Network.speciesCoverableFrom_one_of_reaches_pos
    (G.forward_reaches_of_phaseStep hc hstep)
    hpos

def toInvariantStepwiseRealization
    (G : BimolecularFourPhaseRefinement (s := s) (T := T) M) :
    InvariantStepwiseRealization
      (fourPhaseSystem (s := s) M) G.N
      (GadgetMicroCfgWF (Q := Q) (s := s)) where
  enc := G.encMicro
  step_exec := by
    intro c c' hc hstep
    exact G.exec_of_phaseStep hc hstep
  step_preserves := by
    intro c c' hc hstep
    exact G.agg.toInvariantStepwiseRealization.step_preserves hc hstep

@[simp]
theorem toInvariantStepwiseRealization_enc
    (G : BimolecularFourPhaseRefinement (s := s) (T := T) M)
    (c : MicroCfg Q s) :
    G.toInvariantStepwiseRealization.enc c = G.encMicro c := by
  rfl

theorem goodExec_of_fourPhase_steps
    (G : BimolecularFourPhaseRefinement (s := s) (T := T) M)
    {n : Nat} {c c' : MicroCfg Q s}
    (hc : GadgetMicroCfgWF c)
    (h : (fourPhaseSystem (s := s) M).steps? n c = some c') :
    exists is : List G.agg.N.I,
      G.R.GoodExec
        (FourPhaseEncoding.enc c)
        (FourPhaseEncoding.enc c') is := by
  induction n generalizing c c' with
  | zero =>
      have hSome : (some c : Option (MicroCfg Q s)) = some c' := by
        exact h
      cases hSome
      exact ⟨[], ExecOf.nil (FourPhaseEncoding.enc c)⟩
  | succ n ih =>
      cases hstep : (fourPhaseSystem (s := s) M).step? c with
      | none =>
          simp [DetSystem.steps?, DetSystem.iter, hstep] at h
      | some c₁ =>
          have hphase : phaseStep? (s := s) M c = some c₁ := by
            simpa [fourPhaseSystem] using hstep
          have hc₁ : GadgetMicroCfgWF c₁ :=
            phaseStep?_preserves_gadgetWF (s := s) M hc hphase
          have htail :
              (fourPhaseSystem (s := s) M).steps? n c₁ = some c' := by
            simpa [DetSystem.steps?, DetSystem.iter, hstep] using h
          rcases G.goodExec_of_phaseStep hc hphase with
            ⟨is, hGoodStep⟩
          rcases ih hc₁ htail with ⟨js, hGoodTail⟩
          exact ⟨is ++ js, ExecOf.append hGoodStep hGoodTail⟩

theorem goodReaches_of_fourPhase_steps
    (G : BimolecularFourPhaseRefinement (s := s) (T := T) M)
    {n : Nat} {c c' : MicroCfg Q s}
    (hc : GadgetMicroCfgWF c)
    (h : (fourPhaseSystem (s := s) M).steps? n c = some c') :
    G.R.GoodReaches
      (FourPhaseEncoding.enc c)
      (FourPhaseEncoding.enc c') := by
  rcases G.goodExec_of_fourPhase_steps hc h with ⟨is, hGood⟩
  exact ⟨is, hGood⟩

theorem goodCoverableFrom_of_fourPhase_steps_covers
    (G : BimolecularFourPhaseRefinement (s := s) (T := T) M)
    {n : Nat} {c c' : MicroCfg Q s}
    {target : State (FourPhaseSpecies Q)}
    (hc : GadgetMicroCfgWF c)
    (h : (fourPhaseSystem (s := s) M).steps? n c = some c')
    (hCovers : Covers (FourPhaseEncoding.enc c') target) :
    G.R.GoodCoverableFrom (FourPhaseEncoding.enc c) target :=
  G.R.goodCoverableFrom_of_goodReaches_covers
    (G.goodReaches_of_fourPhase_steps hc h)
    hCovers

theorem goodCoverableFrom_of_fourPhase_steps_of_le
    (G : BimolecularFourPhaseRefinement (s := s) (T := T) M)
    {n : Nat} {c c' : MicroCfg Q s}
    {target : State (FourPhaseSpecies Q)}
    (hc : GadgetMicroCfgWF c)
    (h : (fourPhaseSystem (s := s) M).steps? n c = some c')
    (hTarget :
      forall species,
        target species <= FourPhaseEncoding.enc c' species) :
    G.R.GoodCoverableFrom (FourPhaseEncoding.enc c) target :=
  G.goodCoverableFrom_of_fourPhase_steps_covers hc h hTarget

theorem aggregateIntendedSchedule_of_fourPhase_steps
    (G : BimolecularFourPhaseRefinement (s := s) (T := T) M)
    {n : Nat} {c c' : MicroCfg Q s}
    (hc : GadgetMicroCfgWF c)
    (h : (fourPhaseSystem (s := s) M).steps? n c = some c') :
    exists I :
      G.agg.N.IntendedSchedule
        (FourPhaseEncoding.enc c)
        (FourPhaseEncoding.enc c'),
      G.R.GoodExec
        (FourPhaseEncoding.enc c)
        (FourPhaseEncoding.enc c')
        I.schedule := by
  rcases G.goodExec_of_fourPhase_steps hc h with ⟨is, hGood⟩
  refine ⟨G.aggregateIntendedSchedule_of_goodExec hGood, ?_⟩
  simpa using hGood

theorem exec_of_fourPhase_steps
    (G : BimolecularFourPhaseRefinement (s := s) (T := T) M)
    {n : Nat} {c c' : MicroCfg Q s}
    (hc : GadgetMicroCfgWF c)
    (h : (fourPhaseSystem (s := s) M).steps? n c = some c') :
    exists is : List G.N.I,
      G.N.Exec (G.encMicro c) (G.encMicro c') is :=
  G.toInvariantStepwiseRealization.exec_of_steps hc h

/-- Concrete forward execution for a deterministic four-phase run. -/
theorem intended_forward_exec_of_fourPhase_steps
    (G : BimolecularFourPhaseRefinement (s := s) (T := T) M)
    {n : Nat} {c c' : MicroCfg Q s}
    (hc : GadgetMicroCfgWF c)
    (h : (fourPhaseSystem (s := s) M).steps? n c = some c') :
    exists is : List G.N.I,
      G.N.Exec (G.encMicro c) (G.encMicro c') is :=
  G.exec_of_fourPhase_steps hc h

noncomputable def concreteIntendedSchedule_of_fourPhase_steps
    (G : BimolecularFourPhaseRefinement (s := s) (T := T) M)
    {n : Nat} {c c' : MicroCfg Q s}
    (hc : GadgetMicroCfgWF c)
    (h : (fourPhaseSystem (s := s) M).steps? n c = some c') :
    G.N.IntendedSchedule (G.encMicro c) (G.encMicro c') where
  schedule := Classical.choose (G.exec_of_fourPhase_steps hc h)
  exec := Classical.choose_spec (G.exec_of_fourPhase_steps hc h)

theorem exec_of_concreteIntendedSchedule_of_fourPhase_steps
    (G : BimolecularFourPhaseRefinement (s := s) (T := T) M)
    {n : Nat} {c c' : MicroCfg Q s}
    (hc : GadgetMicroCfgWF c)
    (h : (fourPhaseSystem (s := s) M).steps? n c = some c') :
    G.N.Exec (G.encMicro c) (G.encMicro c')
      (G.concreteIntendedSchedule_of_fourPhase_steps hc h).schedule :=
  (G.concreteIntendedSchedule_of_fourPhase_steps hc h).exec

theorem reaches_of_fourPhase_steps
    (G : BimolecularFourPhaseRefinement (s := s) (T := T) M)
    {n : Nat} {c c' : MicroCfg Q s}
    (hc : GadgetMicroCfgWF c)
    (h : (fourPhaseSystem (s := s) M).steps? n c = some c') :
    G.N.Reaches (G.encMicro c) (G.encMicro c') :=
  G.toInvariantStepwiseRealization.reaches_of_steps hc h

/-- Concrete forward reachability for a deterministic four-phase run. -/
theorem intended_forward_reaches_of_fourPhase_steps
    (G : BimolecularFourPhaseRefinement (s := s) (T := T) M)
    {n : Nat} {c c' : MicroCfg Q s}
    (hc : GadgetMicroCfgWF c)
    (h : (fourPhaseSystem (s := s) M).steps? n c = some c') :
    G.N.Reaches (G.encMicro c) (G.encMicro c') :=
  G.reaches_of_fourPhase_steps hc h

theorem concreteIntendedSchedule_reaches_of_fourPhase_steps
    (G : BimolecularFourPhaseRefinement (s := s) (T := T) M)
    {n : Nat} {c c' : MicroCfg Q s}
    (hc : GadgetMicroCfgWF c)
    (h : (fourPhaseSystem (s := s) M).steps? n c = some c') :
    G.N.Reaches (G.encMicro c) (G.encMicro c') :=
  (G.concreteIntendedSchedule_of_fourPhase_steps hc h).reaches

theorem coverableFrom_of_fourPhase_steps_covers
    (G : BimolecularFourPhaseRefinement (s := s) (T := T) M)
    {n : Nat} {c c' : MicroCfg Q s}
    {target : State T}
    (hc : GadgetMicroCfgWF c)
    (h : (fourPhaseSystem (s := s) M).steps? n c = some c')
    (hCovers : Covers (G.encMicro c') target) :
    G.N.CoverableFrom (G.encMicro c) target :=
  Network.coverable_of_reaches_of_covers
    (G.reaches_of_fourPhase_steps hc h)
    hCovers

theorem coverableFrom_of_fourPhase_steps_of_le
    (G : BimolecularFourPhaseRefinement (s := s) (T := T) M)
    {n : Nat} {c c' : MicroCfg Q s}
    {target : State T}
    (hc : GadgetMicroCfgWF c)
    (h : (fourPhaseSystem (s := s) M).steps? n c = some c')
    (hTarget : forall species, target species <= G.encMicro c' species) :
    G.N.CoverableFrom (G.encMicro c) target :=
  G.coverableFrom_of_fourPhase_steps_covers hc h hTarget

theorem coverable_of_fourPhase_steps_covers
    (G : BimolecularFourPhaseRefinement (s := s) (T := T) M)
    {n : Nat} {c c' : MicroCfg Q s}
    {target : State T}
    (hc : GadgetMicroCfgWF c)
    (h : (fourPhaseSystem (s := s) M).steps? n c = some c')
    (hCovers : Covers (G.encMicro c') target) :
    G.N.CoverableFrom (G.encMicro c) target :=
  G.coverableFrom_of_fourPhase_steps_covers hc h hCovers

theorem coverable_of_fourPhase_steps_of_le
    (G : BimolecularFourPhaseRefinement (s := s) (T := T) M)
    {n : Nat} {c c' : MicroCfg Q s}
    {target : State T}
    (hc : GadgetMicroCfgWF c)
    (h : (fourPhaseSystem (s := s) M).steps? n c = some c')
    (hTarget : forall species, target species <= G.encMicro c' species) :
    G.N.CoverableFrom (G.encMicro c) target :=
  G.coverableFrom_of_fourPhase_steps_of_le hc h hTarget

/-- Safer spelling of the existing four-phase concrete coverability theorem. -/
theorem forward_coverableFrom_of_fourPhase_steps_covers
    (G : BimolecularFourPhaseRefinement (s := s) (T := T) M)
    {n : Nat} {c c' : MicroCfg Q s}
    {target : State T}
    (hc : GadgetMicroCfgWF c)
    (h : (fourPhaseSystem (s := s) M).steps? n c = some c')
    (hCovers : Covers (G.encMicro c') target) :
    G.N.CoverableFrom (G.encMicro c) target :=
  G.coverableFrom_of_fourPhase_steps_covers hc h hCovers

theorem forward_coverableFrom_of_fourPhase_steps_of_le
    (G : BimolecularFourPhaseRefinement (s := s) (T := T) M)
    {n : Nat} {c c' : MicroCfg Q s}
    {target : State T}
    (hc : GadgetMicroCfgWF c)
    (h : (fourPhaseSystem (s := s) M).steps? n c = some c')
    (hTarget : forall species, target species <= G.encMicro c' species) :
    G.N.CoverableFrom (G.encMicro c) target :=
  G.coverableFrom_of_fourPhase_steps_of_le hc h hTarget

theorem speciesCoverableFrom_of_fourPhase_steps_coord
    [DecidableEq T]
    (G : BimolecularFourPhaseRefinement (s := s) (T := T) M)
    {n : Nat} {c c' : MicroCfg Q s}
    {species : T} {amount : Nat}
    (hc : GadgetMicroCfgWF c)
    (h : (fourPhaseSystem (s := s) M).steps? n c = some c')
    (hamount : amount <= G.encMicro c' species) :
    G.N.SpeciesCoverableFrom (G.encMicro c) species amount :=
  Network.speciesCoverableFrom_of_reaches_coord
    (G.reaches_of_fourPhase_steps hc h)
    hamount

theorem speciesCoverableFrom_one_of_fourPhase_steps_pos
    [DecidableEq T]
    (G : BimolecularFourPhaseRefinement (s := s) (T := T) M)
    {n : Nat} {c c' : MicroCfg Q s}
    {species : T}
    (hc : GadgetMicroCfgWF c)
    (h : (fourPhaseSystem (s := s) M).steps? n c = some c')
    (hpos : 0 < G.encMicro c' species) :
    G.N.SpeciesCoverableFrom (G.encMicro c) species :=
  Network.speciesCoverableFrom_one_of_reaches_pos
    (G.reaches_of_fourPhase_steps hc h)
    hpos

/-- Safer spelling of the four-phase concrete species-coverability theorem. -/
theorem forward_speciesCoverableFrom_of_fourPhase_steps_coord
    [DecidableEq T]
    (G : BimolecularFourPhaseRefinement (s := s) (T := T) M)
    {n : Nat} {c c' : MicroCfg Q s}
    {species : T} {amount : Nat}
    (hc : GadgetMicroCfgWF c)
    (h : (fourPhaseSystem (s := s) M).steps? n c = some c')
    (hamount : amount <= G.encMicro c' species) :
    G.N.SpeciesCoverableFrom (G.encMicro c) species amount :=
  G.speciesCoverableFrom_of_fourPhase_steps_coord hc h hamount

theorem forward_speciesCoverableFrom_one_of_fourPhase_steps_pos
    [DecidableEq T]
    (G : BimolecularFourPhaseRefinement (s := s) (T := T) M)
    {n : Nat} {c c' : MicroCfg Q s}
    {species : T}
    (hc : GadgetMicroCfgWF c)
    (h : (fourPhaseSystem (s := s) M).steps? n c = some c')
    (hpos : 0 < G.encMicro c' species) :
    G.N.SpeciesCoverableFrom (G.encMicro c) species :=
  G.speciesCoverableFrom_one_of_fourPhase_steps_pos hc h hpos

theorem exec_of_ctm_steps
    (G : BimolecularFourPhaseRefinement (s := s) (T := T) M)
    {n : Nat} {cfg cfg' : Cfg Q Bool s}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg') :
    exists is : List G.N.I,
      G.N.Exec (G.encCTM cfg) (G.encCTM cfg') is := by
  simpa [encCTM, encMicro] using
    InvariantStepwiseRealization.exec_of_kStepSim_steps
      (sim := fourPhaseKStepSim (s := s) M)
      G.toInvariantStepwiseRealization
      (MicroCfg.ofCTM_gadgetWF cfg)
      h

/-- Concrete forward execution for a deterministic CTM run. -/
theorem intended_forward_exec_of_ctm_steps
    (G : BimolecularFourPhaseRefinement (s := s) (T := T) M)
    {n : Nat} {cfg cfg' : Cfg Q Bool s}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg') :
    exists is : List G.N.I,
      G.N.Exec (G.encCTM cfg) (G.encCTM cfg') is :=
  G.exec_of_ctm_steps h

theorem goodExec_of_ctm_steps
    (G : BimolecularFourPhaseRefinement (s := s) (T := T) M)
    {n : Nat} {cfg cfg' : Cfg Q Bool s}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg') :
    exists is : List G.agg.N.I,
      G.R.GoodExec
        (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg))
        (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg')) is :=
  G.goodExec_of_fourPhase_steps
    (MicroCfg.ofCTM_gadgetWF cfg)
    (fourPhaseKStepSim_steps (s := s) M h)

theorem goodReaches_of_ctm_steps
    (G : BimolecularFourPhaseRefinement (s := s) (T := T) M)
    {n : Nat} {cfg cfg' : Cfg Q Bool s}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg') :
    G.R.GoodReaches
      (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg))
      (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg')) := by
  rcases G.goodExec_of_ctm_steps h with ⟨is, hGood⟩
  exact ⟨is, hGood⟩

theorem goodCoverableFrom_of_ctm_steps_covers
    (G : BimolecularFourPhaseRefinement (s := s) (T := T) M)
    {n : Nat} {cfg cfg' : Cfg Q Bool s}
    {target : State (FourPhaseSpecies Q)}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg')
    (hCovers :
      Covers (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg')) target) :
    G.R.GoodCoverableFrom
      (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg))
      target :=
  G.R.goodCoverableFrom_of_goodReaches_covers
    (G.goodReaches_of_ctm_steps h)
    hCovers

theorem goodCoverableFrom_of_ctm_steps_of_le
    (G : BimolecularFourPhaseRefinement (s := s) (T := T) M)
    {n : Nat} {cfg cfg' : Cfg Q Bool s}
    {target : State (FourPhaseSpecies Q)}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg')
    (hTarget :
      forall species,
        target species <=
          FourPhaseEncoding.enc (MicroCfg.ofCTM cfg') species) :
    G.R.GoodCoverableFrom
      (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg))
      target :=
  G.goodCoverableFrom_of_ctm_steps_covers h hTarget

theorem aggregateIntendedSchedule_of_ctm_steps
    (G : BimolecularFourPhaseRefinement (s := s) (T := T) M)
    {n : Nat} {cfg cfg' : Cfg Q Bool s}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg') :
    exists I :
      G.agg.N.IntendedSchedule
        (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg))
        (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg')),
      G.R.GoodExec
        (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg))
        (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg'))
        I.schedule := by
  rcases G.goodExec_of_ctm_steps h with ⟨is, hGood⟩
  refine ⟨G.aggregateIntendedSchedule_of_goodExec hGood, ?_⟩
  simpa using hGood

noncomputable def concreteIntendedSchedule_of_ctm_steps
    (G : BimolecularFourPhaseRefinement (s := s) (T := T) M)
    {n : Nat} {cfg cfg' : Cfg Q Bool s}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg') :
    G.N.IntendedSchedule (G.encCTM cfg) (G.encCTM cfg') where
  schedule := Classical.choose (G.exec_of_ctm_steps h)
  exec := Classical.choose_spec (G.exec_of_ctm_steps h)

theorem exec_of_concreteIntendedSchedule_of_ctm_steps
    (G : BimolecularFourPhaseRefinement (s := s) (T := T) M)
    {n : Nat} {cfg cfg' : Cfg Q Bool s}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg') :
    G.N.Exec (G.encCTM cfg) (G.encCTM cfg')
      (G.concreteIntendedSchedule_of_ctm_steps h).schedule :=
  (G.concreteIntendedSchedule_of_ctm_steps h).exec

noncomputable def intendedSchedule_of_ctm_steps
    (G : BimolecularFourPhaseRefinement (s := s) (T := T) M)
    {n : Nat} {cfg cfg' : Cfg Q Bool s}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg') :
    G.N.IntendedSchedule (G.encCTM cfg) (G.encCTM cfg') :=
  G.concreteIntendedSchedule_of_ctm_steps h

theorem exec_of_intendedSchedule_of_ctm_steps
    (G : BimolecularFourPhaseRefinement (s := s) (T := T) M)
    {n : Nat} {cfg cfg' : Cfg Q Bool s}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg') :
    G.N.Exec (G.encCTM cfg) (G.encCTM cfg')
      (G.intendedSchedule_of_ctm_steps h).schedule :=
  (G.intendedSchedule_of_ctm_steps h).exec

theorem exec_of_ctm_step
    (G : BimolecularFourPhaseRefinement (s := s) (T := T) M)
    {cfg cfg' : Cfg Q Bool s}
    (h : M.step? cfg = some cfg') :
    exists is : List G.N.I,
      G.N.Exec (G.encCTM cfg) (G.encCTM cfg') is :=
  G.exec_of_ctm_steps
    (DetSystem.steps?_one_of_step? (M.detSystem (s := s)) h)

/-- Concrete forward execution for one deterministic CTM step. -/
theorem intended_forward_exec_of_ctm_step
    (G : BimolecularFourPhaseRefinement (s := s) (T := T) M)
    {cfg cfg' : Cfg Q Bool s}
    (h : M.step? cfg = some cfg') :
    exists is : List G.N.I,
      G.N.Exec (G.encCTM cfg) (G.encCTM cfg') is :=
  G.exec_of_ctm_step h

theorem goodExec_of_ctm_step
    (G : BimolecularFourPhaseRefinement (s := s) (T := T) M)
    {cfg cfg' : Cfg Q Bool s}
    (h : M.step? cfg = some cfg') :
    exists is : List G.agg.N.I,
      G.R.GoodExec
        (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg))
        (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg')) is :=
  G.goodExec_of_ctm_steps
    (DetSystem.steps?_one_of_step? (M.detSystem (s := s)) h)

theorem goodReaches_of_ctm_step
    (G : BimolecularFourPhaseRefinement (s := s) (T := T) M)
    {cfg cfg' : Cfg Q Bool s}
    (h : M.step? cfg = some cfg') :
    G.R.GoodReaches
      (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg))
      (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg')) := by
  rcases G.goodExec_of_ctm_step h with ⟨is, hGood⟩
  exact ⟨is, hGood⟩

theorem goodCoverableFrom_of_ctm_step_covers
    (G : BimolecularFourPhaseRefinement (s := s) (T := T) M)
    {cfg cfg' : Cfg Q Bool s}
    {target : State (FourPhaseSpecies Q)}
    (h : M.step? cfg = some cfg')
    (hCovers :
      Covers (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg')) target) :
    G.R.GoodCoverableFrom
      (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg))
      target :=
  G.R.goodCoverableFrom_of_goodReaches_covers
    (G.goodReaches_of_ctm_step h)
    hCovers

theorem goodCoverableFrom_of_ctm_step_of_le
    (G : BimolecularFourPhaseRefinement (s := s) (T := T) M)
    {cfg cfg' : Cfg Q Bool s}
    {target : State (FourPhaseSpecies Q)}
    (h : M.step? cfg = some cfg')
    (hTarget :
      forall species,
        target species <=
          FourPhaseEncoding.enc (MicroCfg.ofCTM cfg') species) :
    G.R.GoodCoverableFrom
      (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg))
      target :=
  G.goodCoverableFrom_of_ctm_step_covers h hTarget

theorem aggregateIntendedSchedule_of_ctm_step
    (G : BimolecularFourPhaseRefinement (s := s) (T := T) M)
    {cfg cfg' : Cfg Q Bool s}
    (h : M.step? cfg = some cfg') :
    exists I :
      G.agg.N.IntendedSchedule
        (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg))
        (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg')),
      G.R.GoodExec
        (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg))
        (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg'))
        I.schedule :=
  G.aggregateIntendedSchedule_of_ctm_steps
    (DetSystem.steps?_one_of_step? (M.detSystem (s := s)) h)

noncomputable def concreteIntendedSchedule_of_ctm_step
    (G : BimolecularFourPhaseRefinement (s := s) (T := T) M)
    {cfg cfg' : Cfg Q Bool s}
    (h : M.step? cfg = some cfg') :
    G.N.IntendedSchedule (G.encCTM cfg) (G.encCTM cfg') where
  schedule := Classical.choose (G.exec_of_ctm_step h)
  exec := Classical.choose_spec (G.exec_of_ctm_step h)

theorem exec_of_concreteIntendedSchedule_of_ctm_step
    (G : BimolecularFourPhaseRefinement (s := s) (T := T) M)
    {cfg cfg' : Cfg Q Bool s}
    (h : M.step? cfg = some cfg') :
    G.N.Exec (G.encCTM cfg) (G.encCTM cfg')
      (G.concreteIntendedSchedule_of_ctm_step h).schedule :=
  (G.concreteIntendedSchedule_of_ctm_step h).exec

noncomputable def intendedSchedule_of_ctm_step
    (G : BimolecularFourPhaseRefinement (s := s) (T := T) M)
    {cfg cfg' : Cfg Q Bool s}
    (h : M.step? cfg = some cfg') :
    G.N.IntendedSchedule (G.encCTM cfg) (G.encCTM cfg') :=
  G.concreteIntendedSchedule_of_ctm_step h

theorem exec_of_intendedSchedule_of_ctm_step
    (G : BimolecularFourPhaseRefinement (s := s) (T := T) M)
    {cfg cfg' : Cfg Q Bool s}
    (h : M.step? cfg = some cfg') :
    G.N.Exec (G.encCTM cfg) (G.encCTM cfg')
      (G.intendedSchedule_of_ctm_step h).schedule :=
  (G.intendedSchedule_of_ctm_step h).exec

theorem concreteIntendedSchedule_reaches_of_ctm_step
    (G : BimolecularFourPhaseRefinement (s := s) (T := T) M)
    {cfg cfg' : Cfg Q Bool s}
    (h : M.step? cfg = some cfg') :
    G.N.Reaches (G.encCTM cfg) (G.encCTM cfg') :=
  (G.concreteIntendedSchedule_of_ctm_step h).reaches

theorem state_after_ctm_step_of_concreteIntendedWinsRaceAt
    (G : BimolecularFourPhaseRefinement (s := s) (T := T) M)
    {cfg cfg' : Cfg Q Bool s}
    {path : G.N.Path}
    {Bad : G.N.BadIndexSet}
    {t : Nat}
    (h : M.step? cfg = some cfg')
    (hwin :
      path.IntendedWinsRaceAt Bad t
        (G.concreteIntendedSchedule_of_ctm_step h)) :
    path.state
        (t + (G.concreteIntendedSchedule_of_ctm_step h).firingCount) =
      G.encCTM cfg' := by
  simpa [Network.IntendedSchedule.firingCount] using
    path.state_after_intendedWinsRaceAt Bad
      (G.concreteIntendedSchedule_of_ctm_step h)
      hwin

theorem state_after_ctm_step_of_intendedWinsRaceAt
    (G : BimolecularFourPhaseRefinement (s := s) (T := T) M)
    {cfg cfg' : Cfg Q Bool s}
    {path : G.N.Path}
    {Bad : G.N.BadIndexSet}
    {t : Nat}
    (h : M.step? cfg = some cfg')
    (hwin :
      path.IntendedWinsRaceAt Bad t
        (G.intendedSchedule_of_ctm_step h)) :
    path.state
        (t + (G.intendedSchedule_of_ctm_step h).firingCount) =
      G.encCTM cfg' := by
  simpa [intendedSchedule_of_ctm_step] using
    G.state_after_ctm_step_of_concreteIntendedWinsRaceAt h hwin

theorem reaches_of_ctm_step
    (G : BimolecularFourPhaseRefinement (s := s) (T := T) M)
    {cfg cfg' : Cfg Q Bool s}
    (h : M.step? cfg = some cfg') :
    G.N.Reaches (G.encCTM cfg) (G.encCTM cfg') :=
  (G.intendedSchedule_of_ctm_step h).reaches

/-- Concrete forward reachability for one deterministic CTM step. -/
theorem intended_forward_reaches_of_ctm_step
    (G : BimolecularFourPhaseRefinement (s := s) (T := T) M)
    {cfg cfg' : Cfg Q Bool s}
    (h : M.step? cfg = some cfg') :
    G.N.Reaches (G.encCTM cfg) (G.encCTM cfg') :=
  G.reaches_of_ctm_step h

theorem coverableFrom_of_ctm_step_covers
    (G : BimolecularFourPhaseRefinement (s := s) (T := T) M)
    {cfg cfg' : Cfg Q Bool s}
    {target : State T}
    (h : M.step? cfg = some cfg')
    (hCovers : Covers (G.encCTM cfg') target) :
    G.N.CoverableFrom (G.encCTM cfg) target :=
  Network.coverable_of_reaches_of_covers
    (G.reaches_of_ctm_step h)
    hCovers

theorem coverableFrom_of_ctm_step_of_le
    (G : BimolecularFourPhaseRefinement (s := s) (T := T) M)
    {cfg cfg' : Cfg Q Bool s}
    {target : State T}
    (h : M.step? cfg = some cfg')
    (hTarget : forall species, target species <= G.encCTM cfg' species) :
    G.N.CoverableFrom (G.encCTM cfg) target :=
  G.coverableFrom_of_ctm_step_covers h hTarget

theorem coverable_of_ctm_step_covers
    (G : BimolecularFourPhaseRefinement (s := s) (T := T) M)
    {cfg cfg' : Cfg Q Bool s}
    {target : State T}
    (h : M.step? cfg = some cfg')
    (hCovers : Covers (G.encCTM cfg') target) :
    G.N.CoverableFrom (G.encCTM cfg) target :=
  G.coverableFrom_of_ctm_step_covers h hCovers

theorem coverable_of_ctm_step_of_le
    (G : BimolecularFourPhaseRefinement (s := s) (T := T) M)
    {cfg cfg' : Cfg Q Bool s}
    {target : State T}
    (h : M.step? cfg = some cfg')
    (hTarget : forall species, target species <= G.encCTM cfg' species) :
    G.N.CoverableFrom (G.encCTM cfg) target :=
  G.coverableFrom_of_ctm_step_of_le h hTarget

/-- Safer spelling of the one-step concrete coverability theorem. -/
theorem forward_coverableFrom_of_ctm_step_covers
    (G : BimolecularFourPhaseRefinement (s := s) (T := T) M)
    {cfg cfg' : Cfg Q Bool s}
    {target : State T}
    (h : M.step? cfg = some cfg')
    (hCovers : Covers (G.encCTM cfg') target) :
    G.N.CoverableFrom (G.encCTM cfg) target :=
  G.coverableFrom_of_ctm_step_covers h hCovers

theorem forward_coverableFrom_of_ctm_step_of_le
    (G : BimolecularFourPhaseRefinement (s := s) (T := T) M)
    {cfg cfg' : Cfg Q Bool s}
    {target : State T}
    (h : M.step? cfg = some cfg')
    (hTarget : forall species, target species <= G.encCTM cfg' species) :
    G.N.CoverableFrom (G.encCTM cfg) target :=
  G.coverableFrom_of_ctm_step_of_le h hTarget

theorem speciesCoverableFrom_of_ctm_step_coord
    [DecidableEq T]
    (G : BimolecularFourPhaseRefinement (s := s) (T := T) M)
    {cfg cfg' : Cfg Q Bool s}
    {species : T} {amount : Nat}
    (h : M.step? cfg = some cfg')
    (hamount : amount <= G.encCTM cfg' species) :
    G.N.SpeciesCoverableFrom (G.encCTM cfg) species amount :=
  Network.speciesCoverableFrom_of_reaches_coord
    (G.reaches_of_ctm_step h)
    hamount

theorem speciesCoverableFrom_one_of_ctm_step_pos
    [DecidableEq T]
    (G : BimolecularFourPhaseRefinement (s := s) (T := T) M)
    {cfg cfg' : Cfg Q Bool s}
    {species : T}
    (h : M.step? cfg = some cfg')
    (hpos : 0 < G.encCTM cfg' species) :
    G.N.SpeciesCoverableFrom (G.encCTM cfg) species :=
  Network.speciesCoverableFrom_one_of_reaches_pos
    (G.reaches_of_ctm_step h)
    hpos

/-- Safer spelling of the one-step concrete species-coverability theorem. -/
theorem forward_speciesCoverableFrom_of_ctm_step_coord
    [DecidableEq T]
    (G : BimolecularFourPhaseRefinement (s := s) (T := T) M)
    {cfg cfg' : Cfg Q Bool s}
    {species : T} {amount : Nat}
    (h : M.step? cfg = some cfg')
    (hamount : amount <= G.encCTM cfg' species) :
    G.N.SpeciesCoverableFrom (G.encCTM cfg) species amount :=
  G.speciesCoverableFrom_of_ctm_step_coord h hamount

theorem forward_speciesCoverableFrom_one_of_ctm_step_pos
    [DecidableEq T]
    (G : BimolecularFourPhaseRefinement (s := s) (T := T) M)
    {cfg cfg' : Cfg Q Bool s}
    {species : T}
    (h : M.step? cfg = some cfg')
    (hpos : 0 < G.encCTM cfg' species) :
    G.N.SpeciesCoverableFrom (G.encCTM cfg) species :=
  G.speciesCoverableFrom_one_of_ctm_step_pos h hpos

theorem concreteIntendedSchedule_reaches_of_ctm_steps
    (G : BimolecularFourPhaseRefinement (s := s) (T := T) M)
    {n : Nat} {cfg cfg' : Cfg Q Bool s}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg') :
    G.N.Reaches (G.encCTM cfg) (G.encCTM cfg') :=
  (G.concreteIntendedSchedule_of_ctm_steps h).reaches

theorem state_after_ctm_steps_of_concreteIntendedWinsRaceAt
    (G : BimolecularFourPhaseRefinement (s := s) (T := T) M)
    {n : Nat} {cfg cfg' : Cfg Q Bool s}
    {path : G.N.Path}
    {Bad : G.N.BadIndexSet}
    {t : Nat}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg')
    (hwin :
      path.IntendedWinsRaceAt Bad t
        (G.concreteIntendedSchedule_of_ctm_steps h)) :
    path.state
        (t + (G.concreteIntendedSchedule_of_ctm_steps h).firingCount) =
      G.encCTM cfg' := by
  simpa [Network.IntendedSchedule.firingCount] using
    path.state_after_intendedWinsRaceAt Bad
      (G.concreteIntendedSchedule_of_ctm_steps h)
      hwin

theorem state_after_ctm_steps_of_intendedWinsRaceAt
    (G : BimolecularFourPhaseRefinement (s := s) (T := T) M)
    {n : Nat} {cfg cfg' : Cfg Q Bool s}
    {path : G.N.Path}
    {Bad : G.N.BadIndexSet}
    {t : Nat}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg')
    (hwin :
      path.IntendedWinsRaceAt Bad t
        (G.intendedSchedule_of_ctm_steps h)) :
    path.state
        (t + (G.intendedSchedule_of_ctm_steps h).firingCount) =
      G.encCTM cfg' := by
  simpa [intendedSchedule_of_ctm_steps] using
    G.state_after_ctm_steps_of_concreteIntendedWinsRaceAt h hwin

theorem reaches_of_ctm_steps
    (G : BimolecularFourPhaseRefinement (s := s) (T := T) M)
    {n : Nat} {cfg cfg' : Cfg Q Bool s}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg') :
    G.N.Reaches (G.encCTM cfg) (G.encCTM cfg') := by
  simpa [encCTM, encMicro] using
    InvariantStepwiseRealization.reaches_of_kStepSim_steps
      (sim := fourPhaseKStepSim (s := s) M)
      G.toInvariantStepwiseRealization
      (MicroCfg.ofCTM_gadgetWF cfg)
      h

/-- Concrete forward reachability for a deterministic CTM run. -/
theorem intended_forward_reaches_of_ctm_steps
    (G : BimolecularFourPhaseRefinement (s := s) (T := T) M)
    {n : Nat} {cfg cfg' : Cfg Q Bool s}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg') :
    G.N.Reaches (G.encCTM cfg) (G.encCTM cfg') :=
  G.reaches_of_ctm_steps h

theorem coverableFrom_of_ctm_steps_covers
    (G : BimolecularFourPhaseRefinement (s := s) (T := T) M)
    {n : Nat} {cfg cfg' : Cfg Q Bool s}
    {target : State T}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg')
    (hCovers : Covers (G.encCTM cfg') target) :
    G.N.CoverableFrom (G.encCTM cfg) target :=
  Network.coverable_of_reaches_of_covers
    (G.reaches_of_ctm_steps h)
    hCovers

theorem coverableFrom_of_ctm_steps_of_le
    (G : BimolecularFourPhaseRefinement (s := s) (T := T) M)
    {n : Nat} {cfg cfg' : Cfg Q Bool s}
    {target : State T}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg')
    (hTarget : forall species, target species <= G.encCTM cfg' species) :
    G.N.CoverableFrom (G.encCTM cfg) target :=
  G.coverableFrom_of_ctm_steps_covers h hTarget

theorem coverable_of_ctm_steps_covers
    (G : BimolecularFourPhaseRefinement (s := s) (T := T) M)
    {n : Nat} {cfg cfg' : Cfg Q Bool s}
    {target : State T}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg')
    (hCovers : Covers (G.encCTM cfg') target) :
    G.N.CoverableFrom (G.encCTM cfg) target :=
  G.coverableFrom_of_ctm_steps_covers h hCovers

theorem coverable_of_ctm_steps_of_le
    (G : BimolecularFourPhaseRefinement (s := s) (T := T) M)
    {n : Nat} {cfg cfg' : Cfg Q Bool s}
    {target : State T}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg')
    (hTarget : forall species, target species <= G.encCTM cfg' species) :
    G.N.CoverableFrom (G.encCTM cfg) target :=
  G.coverableFrom_of_ctm_steps_of_le h hTarget

/-- Safer spelling of the existing concrete coverability theorem. -/
theorem forward_coverableFrom_of_ctm_steps_covers
    (G : BimolecularFourPhaseRefinement (s := s) (T := T) M)
    {n : Nat} {cfg cfg' : Cfg Q Bool s}
    {target : State T}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg')
    (hCovers : Covers (G.encCTM cfg') target) :
    G.N.CoverableFrom (G.encCTM cfg) target :=
  G.coverableFrom_of_ctm_steps_covers h hCovers

theorem forward_coverableFrom_of_ctm_steps_of_le
    (G : BimolecularFourPhaseRefinement (s := s) (T := T) M)
    {n : Nat} {cfg cfg' : Cfg Q Bool s}
    {target : State T}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg')
    (hTarget : forall species, target species <= G.encCTM cfg' species) :
    G.N.CoverableFrom (G.encCTM cfg) target :=
  G.coverableFrom_of_ctm_steps_of_le h hTarget

theorem speciesCoverableFrom_of_ctm_steps_coord
    [DecidableEq T]
    (G : BimolecularFourPhaseRefinement (s := s) (T := T) M)
    {n : Nat} {cfg cfg' : Cfg Q Bool s}
    {species : T} {amount : Nat}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg')
    (hamount : amount <= G.encCTM cfg' species) :
    G.N.SpeciesCoverableFrom (G.encCTM cfg) species amount :=
  Network.speciesCoverableFrom_of_reaches_coord
    (G.reaches_of_ctm_steps h)
    hamount

theorem speciesCoverableFrom_one_of_ctm_steps_pos
    [DecidableEq T]
    (G : BimolecularFourPhaseRefinement (s := s) (T := T) M)
    {n : Nat} {cfg cfg' : Cfg Q Bool s}
    {species : T}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg')
    (hpos : 0 < G.encCTM cfg' species) :
    G.N.SpeciesCoverableFrom (G.encCTM cfg) species :=
  Network.speciesCoverableFrom_one_of_reaches_pos
    (G.reaches_of_ctm_steps h)
    hpos

/-- Safer spelling of the existing concrete species-coverability theorem. -/
theorem forward_speciesCoverableFrom_of_ctm_steps_coord
    [DecidableEq T]
    (G : BimolecularFourPhaseRefinement (s := s) (T := T) M)
    {n : Nat} {cfg cfg' : Cfg Q Bool s}
    {species : T} {amount : Nat}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg')
    (hamount : amount <= G.encCTM cfg' species) :
    G.N.SpeciesCoverableFrom (G.encCTM cfg) species amount :=
  G.speciesCoverableFrom_of_ctm_steps_coord h hamount

theorem forward_speciesCoverableFrom_one_of_ctm_steps_pos
    [DecidableEq T]
    (G : BimolecularFourPhaseRefinement (s := s) (T := T) M)
    {n : Nat} {cfg cfg' : Cfg Q Bool s}
    {species : T}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg')
    (hpos : 0 < G.encCTM cfg' species) :
    G.N.SpeciesCoverableFrom (G.encCTM cfg) species :=
  G.speciesCoverableFrom_one_of_ctm_steps_pos h hpos

def networkRefinementOfConcreteFourPhaseModule
    {Q : Type u} [Fintype Q] [DecidableEq Q] {s : Nat}
    (M : Binary Q)
    (G : ConcreteFourPhaseModule.{u, v, x} (s := s) M)
    (encAgg : State (FourPhaseSpecies Q) -> State G.CSp)
    (henc :
      forall c : MicroCfg Q s,
        encAgg (FourPhaseEncoding.enc c) = G.encMicro c) :
    BimolecularNetworkRefinement
      (FourPhaseMacroModule.network (s := s) M) G.N where
  enc := encAgg
  GoodStepAt := fun i z z' =>
    exists c c' : MicroCfg Q s,
      GadgetMicroCfgWF c /\
        phaseStep? (s := s) M c = some c' /\
        z = FourPhaseEncoding.enc c /\
        z' = FourPhaseEncoding.enc c' /\
        (FourPhaseMacroModule.network (s := s) M).StepAt i z z'
  goodStepAt_stepAt := by
    intro _i _z _z' hGood
    rcases hGood with ⟨_c, _c', _hc, _hstep, _hz, _hz', hStep⟩
    exact hStep
  concrete_allAtMostBimolecularInput := G.allAtMostBimolecularInput
  concrete_hasPositiveRates := G.hasPositiveRates
  stepAt_exec := by
    intro _i z z' hGood
    rcases hGood with ⟨c, c', hc, hstep, hz, hz', _hStep⟩
    subst z
    subst z'
    rcases G.step_exec_bounded hc hstep with ⟨js, hExec, _hLen⟩
    refine ⟨js, ?_⟩
    rw [henc c, henc c']
    simpa [ConcreteFourPhaseModule.encMicro] using hExec

@[simp]
theorem networkRefinementOfConcreteFourPhaseModule_enc
    {Q : Type u} [Fintype Q] [DecidableEq Q] {s : Nat}
    (M : Binary Q)
    (G : ConcreteFourPhaseModule.{u, v, x} (s := s) M)
    (encAgg : State (FourPhaseSpecies Q) -> State G.CSp)
    (henc :
      forall c : MicroCfg Q s,
        encAgg (FourPhaseEncoding.enc c) = G.encMicro c)
    (c : MicroCfg Q s) :
    (networkRefinementOfConcreteFourPhaseModule
      (s := s) M G encAgg henc).enc (FourPhaseEncoding.enc c) =
        G.encMicro c := by
  exact henc c

theorem networkRefinementOfConcreteFourPhaseModule_goodStepAt_of_phaseStep
    {Q : Type u} [Fintype Q] [DecidableEq Q] {s : Nat}
    (M : Binary Q)
    (G : ConcreteFourPhaseModule.{u, v, x} (s := s) M)
    (encAgg : State (FourPhaseSpecies Q) -> State G.CSp)
    (henc :
      forall c : MicroCfg Q s,
        encAgg (FourPhaseEncoding.enc c) = G.encMicro c)
    {c c' : MicroCfg Q s}
    (hc : GadgetMicroCfgWF c)
    (hstep : phaseStep? (s := s) M c = some c') :
    exists i : (FourPhaseMacroModule.network (s := s) M).I,
      (networkRefinementOfConcreteFourPhaseModule
        (s := s) M G encAgg henc).GoodStepAt i
        (FourPhaseEncoding.enc c)
        (FourPhaseEncoding.enc c') := by
  rcases
    FourPhaseMacroModule.exists_phaseIndex_singleton_exec_of_phaseStep?
      (s := s) M hc hstep with
    ⟨i, _hPhase, hExec⟩
  have hStep :
      (FourPhaseMacroModule.network (s := s) M).StepAt i
        (FourPhaseEncoding.enc c)
        (FourPhaseEncoding.enc c') :=
    ExecOf.singleton_iff.mp hExec
  refine ⟨i, ?_⟩
  exact ⟨c, c', hc, hstep, rfl, rfl, hStep⟩

theorem networkRefinementOfConcreteFourPhaseModule_goodExec_of_phaseStep
    {Q : Type u} [Fintype Q] [DecidableEq Q] {s : Nat}
    (M : Binary Q)
    (G : ConcreteFourPhaseModule.{u, v, x} (s := s) M)
    (encAgg : State (FourPhaseSpecies Q) -> State G.CSp)
    (henc :
      forall c : MicroCfg Q s,
        encAgg (FourPhaseEncoding.enc c) = G.encMicro c)
    {c c' : MicroCfg Q s}
    (hc : GadgetMicroCfgWF c)
    (hstep : phaseStep? (s := s) M c = some c') :
    exists is : List (FourPhaseMacroModule.network (s := s) M).I,
      (networkRefinementOfConcreteFourPhaseModule
        (s := s) M G encAgg henc).GoodExec
        (FourPhaseEncoding.enc c)
        (FourPhaseEncoding.enc c') is := by
  rcases
    networkRefinementOfConcreteFourPhaseModule_goodStepAt_of_phaseStep
      (s := s) M G encAgg henc hc hstep with
    ⟨i, hGood⟩
  exact ⟨[i], ExecOf.cons hGood
    (ExecOf.nil (FourPhaseEncoding.enc c'))⟩

def ofFourPhaseMacroModule
    {Q : Type u} [Fintype Q] [DecidableEq Q] {s : Nat}
    {T : Type v} [Fintype T]
    (M : Binary Q)
    (N : Network.{v, x} T)
    (R :
      BimolecularNetworkRefinement
        (FourPhaseMacroModule.network (s := s) M) N)
    (hGood :
      forall {c c' : MicroCfg Q s},
        GadgetMicroCfgWF c ->
        phaseStep? (s := s) M c = some c' ->
          exists is : List (FourPhaseMacroModule.network (s := s) M).I,
            R.GoodExec
              (FourPhaseEncoding.enc c)
              (FourPhaseEncoding.enc c') is) :
    BimolecularFourPhaseRefinement (s := s) (T := T) M where
  agg := FourPhaseMacroModule.module (s := s) M
  N := N
  R := by
    simpa [FourPhaseMacroModule.module] using R
  good_step_exec := by
    intro c c' hc hstep
    simpa [FourPhaseMacroModule.module] using
      hGood (c := c) (c' := c') hc hstep

@[simp]
theorem ofFourPhaseMacroModule_encMicro
    {Q : Type u} [Fintype Q] [DecidableEq Q] {s : Nat}
    {T : Type v} [Fintype T]
    (M : Binary Q)
    (N : Network.{v, x} T)
    (R :
      BimolecularNetworkRefinement
        (FourPhaseMacroModule.network (s := s) M) N)
    (hGood :
      forall {c c' : MicroCfg Q s},
        GadgetMicroCfgWF c ->
        phaseStep? (s := s) M c = some c' ->
          exists is : List (FourPhaseMacroModule.network (s := s) M).I,
            R.GoodExec
              (FourPhaseEncoding.enc c)
              (FourPhaseEncoding.enc c') is)
    (c : MicroCfg Q s) :
    (ofFourPhaseMacroModule (s := s) M N R hGood).encMicro c =
      R.enc (FourPhaseEncoding.enc c) := by
  simp [ofFourPhaseMacroModule, encMicro, FourPhaseMacroModule.module]

@[simp]
theorem ofFourPhaseMacroModule_encCTM
    {Q : Type u} [Fintype Q] [DecidableEq Q] {s : Nat}
    {T : Type v} [Fintype T]
    (M : Binary Q)
    (N : Network.{v, x} T)
    (R :
      BimolecularNetworkRefinement
        (FourPhaseMacroModule.network (s := s) M) N)
    (hGood :
      forall {c c' : MicroCfg Q s},
        GadgetMicroCfgWF c ->
        phaseStep? (s := s) M c = some c' ->
          exists is : List (FourPhaseMacroModule.network (s := s) M).I,
            R.GoodExec
              (FourPhaseEncoding.enc c)
              (FourPhaseEncoding.enc c') is)
    (cfg : Cfg Q Bool s) :
    (ofFourPhaseMacroModule (s := s) M N R hGood).encCTM cfg =
      R.enc (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg)) := by
  simpa [encCTM] using
    ofFourPhaseMacroModule_encMicro
      (s := s) M N R hGood (MicroCfg.ofCTM cfg)

def ofConcreteFourPhaseModule
    {Q : Type u} [Fintype Q] [DecidableEq Q] {s : Nat}
    (M : Binary Q)
    (G : ConcreteFourPhaseModule.{u, v, x} (s := s) M)
    (encAgg : State (FourPhaseSpecies Q) -> State G.CSp)
    (henc :
      forall c : MicroCfg Q s,
        encAgg (FourPhaseEncoding.enc c) = G.encMicro c) :
    BimolecularFourPhaseRefinement (s := s) (T := G.CSp) M :=
  ofFourPhaseMacroModule (s := s) M G.N
    (networkRefinementOfConcreteFourPhaseModule
      (s := s) M G encAgg henc)
    (by
      intro c c' hc hstep
      rcases
        FourPhaseMacroModule.exists_phaseIndex_singleton_exec_of_phaseStep?
          (s := s) M hc hstep with
        ⟨i, _hPhase, hExec⟩
      have hStep :
          (FourPhaseMacroModule.network (s := s) M).StepAt i
            (FourPhaseEncoding.enc c)
            (FourPhaseEncoding.enc c') :=
        ExecOf.singleton_iff.mp hExec
      refine ⟨[i], ?_⟩
      exact ExecOf.cons
        ⟨c, c', hc, hstep, rfl, rfl, hStep⟩
        (ExecOf.nil (FourPhaseEncoding.enc c')))

def atMostBimolecularForwardOfConcreteFourPhaseModule
    {Q : Type u} [Fintype Q] [DecidableEq Q] {s : Nat}
    (M : Binary Q)
    (G : ConcreteFourPhaseModule.{u, v, x} (s := s) M)
    (encAgg : State (FourPhaseSpecies Q) -> State G.CSp)
    (henc :
      forall c : MicroCfg Q s,
        encAgg (FourPhaseEncoding.enc c) = G.encMicro c) :
    BimolecularFourPhaseRefinement (s := s) (T := G.CSp) M :=
  ofConcreteFourPhaseModule (s := s) M G encAgg henc

@[simp]
theorem ofConcreteFourPhaseModule_encMicro
    {Q : Type u} [Fintype Q] [DecidableEq Q] {s : Nat}
    (M : Binary Q)
    (G : ConcreteFourPhaseModule.{u, v, x} (s := s) M)
    (encAgg : State (FourPhaseSpecies Q) -> State G.CSp)
    (henc :
      forall c : MicroCfg Q s,
        encAgg (FourPhaseEncoding.enc c) = G.encMicro c)
    (c : MicroCfg Q s) :
    (ofConcreteFourPhaseModule (s := s) M G encAgg henc).encMicro c =
      G.encMicro c := by
  simpa [
    ofConcreteFourPhaseModule,
    ofFourPhaseMacroModule,
    networkRefinementOfConcreteFourPhaseModule,
    encMicro,
    FourPhaseMacroModule.module
  ] using henc c

@[simp]
theorem ofConcreteFourPhaseModule_encCTM
    {Q : Type u} [Fintype Q] [DecidableEq Q] {s : Nat}
    (M : Binary Q)
    (G : ConcreteFourPhaseModule.{u, v, x} (s := s) M)
    (encAgg : State (FourPhaseSpecies Q) -> State G.CSp)
    (henc :
      forall c : MicroCfg Q s,
        encAgg (FourPhaseEncoding.enc c) = G.encMicro c)
    (cfg : Cfg Q Bool s) :
    (ofConcreteFourPhaseModule (s := s) M G encAgg henc).encCTM cfg =
      G.encCTM cfg := by
  simpa [encCTM, ConcreteFourPhaseModule.encCTM] using
    ofConcreteFourPhaseModule_encMicro
      (s := s) M G encAgg henc (MicroCfg.ofCTM cfg)

def networkRefinementOfConcreteFourPhaseExpansionFamily
    {Q : Type u} [Fintype Q] [DecidableEq Q] {s : Nat}
    (M : Binary Q)
    (F :
      FourPhaseConcrete.ConcreteFourPhaseExpansionFamily.{u, v, x}
        (s := s) M)
    (encAgg : State (FourPhaseSpecies Q) -> State F.CSp)
    (henc :
      forall c : MicroCfg Q s,
        encAgg (FourPhaseEncoding.enc c) = F.enc c) :
    BimolecularNetworkRefinement
      (FourPhaseMacroModule.network (s := s) M) F.network :=
  networkRefinementOfConcreteFourPhaseModule
    (s := s) M F.toConcreteFourPhaseModule encAgg
    (by
      intro c
      simpa [
        FourPhaseConcrete.ConcreteFourPhaseExpansionFamily.toConcreteFourPhaseModule,
        ConcreteFourPhaseModule.encMicro
      ] using henc c)

@[simp]
theorem networkRefinementOfConcreteFourPhaseExpansionFamily_enc
    {Q : Type u} [Fintype Q] [DecidableEq Q] {s : Nat}
    (M : Binary Q)
    (F :
      FourPhaseConcrete.ConcreteFourPhaseExpansionFamily.{u, v, x}
        (s := s) M)
    (encAgg : State (FourPhaseSpecies Q) -> State F.CSp)
    (henc :
      forall c : MicroCfg Q s,
        encAgg (FourPhaseEncoding.enc c) = F.enc c)
    (c : MicroCfg Q s) :
    (networkRefinementOfConcreteFourPhaseExpansionFamily
      (s := s) M F encAgg henc).enc (FourPhaseEncoding.enc c) =
        F.enc c := by
  exact henc c

theorem networkRefinementOfConcreteFourPhaseExpansionFamily_goodStepAt_of_phaseStep
    {Q : Type u} [Fintype Q] [DecidableEq Q] {s : Nat}
    (M : Binary Q)
    (F :
      FourPhaseConcrete.ConcreteFourPhaseExpansionFamily.{u, v, x}
        (s := s) M)
    (encAgg : State (FourPhaseSpecies Q) -> State F.CSp)
    (henc :
      forall c : MicroCfg Q s,
        encAgg (FourPhaseEncoding.enc c) = F.enc c)
    {c c' : MicroCfg Q s}
    (hc : GadgetMicroCfgWF c)
    (hstep : phaseStep? (s := s) M c = some c') :
    exists i : (FourPhaseMacroModule.network (s := s) M).I,
      (networkRefinementOfConcreteFourPhaseExpansionFamily
        (s := s) M F encAgg henc).GoodStepAt i
        (FourPhaseEncoding.enc c)
        (FourPhaseEncoding.enc c') := by
  simpa [networkRefinementOfConcreteFourPhaseExpansionFamily] using
    networkRefinementOfConcreteFourPhaseModule_goodStepAt_of_phaseStep
      (s := s) M F.toConcreteFourPhaseModule encAgg
      (by
        intro c
        simpa [
          FourPhaseConcrete.ConcreteFourPhaseExpansionFamily.toConcreteFourPhaseModule,
          ConcreteFourPhaseModule.encMicro
        ] using henc c)
      hc hstep

theorem networkRefinementOfConcreteFourPhaseExpansionFamily_goodExec_of_phaseStep
    {Q : Type u} [Fintype Q] [DecidableEq Q] {s : Nat}
    (M : Binary Q)
    (F :
      FourPhaseConcrete.ConcreteFourPhaseExpansionFamily.{u, v, x}
        (s := s) M)
    (encAgg : State (FourPhaseSpecies Q) -> State F.CSp)
    (henc :
      forall c : MicroCfg Q s,
        encAgg (FourPhaseEncoding.enc c) = F.enc c)
    {c c' : MicroCfg Q s}
    (hc : GadgetMicroCfgWF c)
    (hstep : phaseStep? (s := s) M c = some c') :
    exists is : List (FourPhaseMacroModule.network (s := s) M).I,
      (networkRefinementOfConcreteFourPhaseExpansionFamily
        (s := s) M F encAgg henc).GoodExec
        (FourPhaseEncoding.enc c)
        (FourPhaseEncoding.enc c') is := by
  simpa [networkRefinementOfConcreteFourPhaseExpansionFamily] using
    networkRefinementOfConcreteFourPhaseModule_goodExec_of_phaseStep
      (s := s) M F.toConcreteFourPhaseModule encAgg
      (by
        intro c
        simpa [
          FourPhaseConcrete.ConcreteFourPhaseExpansionFamily.toConcreteFourPhaseModule,
          ConcreteFourPhaseModule.encMicro
        ] using henc c)
      hc hstep

def ofConcreteFourPhaseExpansionFamily
    {Q : Type u} [Fintype Q] [DecidableEq Q] {s : Nat}
    (M : Binary Q)
    (F :
      FourPhaseConcrete.ConcreteFourPhaseExpansionFamily.{u, v, x}
        (s := s) M)
    (encAgg : State (FourPhaseSpecies Q) -> State F.CSp)
    (henc :
      forall c : MicroCfg Q s,
        encAgg (FourPhaseEncoding.enc c) = F.enc c) :
    BimolecularFourPhaseRefinement (s := s) (T := F.CSp) M :=
  ofConcreteFourPhaseModule
    (s := s) M F.toConcreteFourPhaseModule encAgg
    (by
      intro c
      simpa [
        FourPhaseConcrete.ConcreteFourPhaseExpansionFamily.toConcreteFourPhaseModule,
        ConcreteFourPhaseModule.encMicro
      ] using henc c)

def atMostBimolecularForwardOfConcreteFourPhaseExpansionFamily
    {Q : Type u} [Fintype Q] [DecidableEq Q] {s : Nat}
    (M : Binary Q)
    (F :
      FourPhaseConcrete.ConcreteFourPhaseExpansionFamily.{u, v, x}
        (s := s) M)
    (encAgg : State (FourPhaseSpecies Q) -> State F.CSp)
    (henc :
      forall c : MicroCfg Q s,
        encAgg (FourPhaseEncoding.enc c) = F.enc c) :
    BimolecularFourPhaseRefinement (s := s) (T := F.CSp) M :=
  ofConcreteFourPhaseExpansionFamily (s := s) M F encAgg henc

@[simp]
theorem ofConcreteFourPhaseExpansionFamily_encMicro
    {Q : Type u} [Fintype Q] [DecidableEq Q] {s : Nat}
    (M : Binary Q)
    (F :
      FourPhaseConcrete.ConcreteFourPhaseExpansionFamily.{u, v, x}
        (s := s) M)
    (encAgg : State (FourPhaseSpecies Q) -> State F.CSp)
    (henc :
      forall c : MicroCfg Q s,
        encAgg (FourPhaseEncoding.enc c) = F.enc c)
    (c : MicroCfg Q s) :
    (ofConcreteFourPhaseExpansionFamily
      (s := s) M F encAgg henc).encMicro c = F.enc c := by
  simpa [
    ofConcreteFourPhaseExpansionFamily,
    FourPhaseConcrete.ConcreteFourPhaseExpansionFamily.toConcreteFourPhaseModule,
    ConcreteFourPhaseModule.encMicro
  ] using henc c

@[simp]
theorem ofConcreteFourPhaseExpansionFamily_encCTM
    {Q : Type u} [Fintype Q] [DecidableEq Q] {s : Nat}
    (M : Binary Q)
    (F :
      FourPhaseConcrete.ConcreteFourPhaseExpansionFamily.{u, v, x}
        (s := s) M)
    (encAgg : State (FourPhaseSpecies Q) -> State F.CSp)
    (henc :
      forall c : MicroCfg Q s,
        encAgg (FourPhaseEncoding.enc c) = F.enc c)
    (cfg : Cfg Q Bool s) :
    (ofConcreteFourPhaseExpansionFamily
      (s := s) M F encAgg henc).encCTM cfg =
        F.enc (MicroCfg.ofCTM cfg) := by
  simpa [encCTM] using
    ofConcreteFourPhaseExpansionFamily_encMicro
      (s := s) M F encAgg henc (MicroCfg.ofCTM cfg)

def networkRefinementOfFootprintedConcreteFourPhaseModule
    {Q : Type u} [Fintype Q] [DecidableEq Q] {s : Nat}
    (M : Binary Q)
    (G :
      FourPhaseConcrete.FootprintedConcreteFourPhaseModule.{u, v, x}
        (s := s) M)
    (encAgg : State (FourPhaseSpecies Q) -> State G.CSp)
    (henc :
      forall c : MicroCfg Q s,
        encAgg (FourPhaseEncoding.enc c) = G.enc c) :
    BimolecularNetworkRefinement
      (FourPhaseMacroModule.network (s := s) M) G.N :=
  networkRefinementOfConcreteFourPhaseModule
    (s := s) M G.toConcreteFourPhaseModule encAgg
    (by
      intro c
      simpa [
        FourPhaseConcrete.FootprintedConcreteFourPhaseModule.toConcreteFourPhaseModule,
        ConcreteFourPhaseModule.encMicro
      ] using henc c)

@[simp]
theorem networkRefinementOfFootprintedConcreteFourPhaseModule_enc
    {Q : Type u} [Fintype Q] [DecidableEq Q] {s : Nat}
    (M : Binary Q)
    (G :
      FourPhaseConcrete.FootprintedConcreteFourPhaseModule.{u, v, x}
        (s := s) M)
    (encAgg : State (FourPhaseSpecies Q) -> State G.CSp)
    (henc :
      forall c : MicroCfg Q s,
        encAgg (FourPhaseEncoding.enc c) = G.enc c)
    (c : MicroCfg Q s) :
    (networkRefinementOfFootprintedConcreteFourPhaseModule
      (s := s) M G encAgg henc).enc (FourPhaseEncoding.enc c) =
        G.enc c := by
  exact henc c

theorem networkRefinementOfFootprintedConcreteFourPhaseModule_goodStepAt_of_phaseStep
    {Q : Type u} [Fintype Q] [DecidableEq Q] {s : Nat}
    (M : Binary Q)
    (G :
      FourPhaseConcrete.FootprintedConcreteFourPhaseModule.{u, v, x}
        (s := s) M)
    (encAgg : State (FourPhaseSpecies Q) -> State G.CSp)
    (henc :
      forall c : MicroCfg Q s,
        encAgg (FourPhaseEncoding.enc c) = G.enc c)
    {c c' : MicroCfg Q s}
    (hc : GadgetMicroCfgWF c)
    (hstep : phaseStep? (s := s) M c = some c') :
    exists i : (FourPhaseMacroModule.network (s := s) M).I,
      (networkRefinementOfFootprintedConcreteFourPhaseModule
        (s := s) M G encAgg henc).GoodStepAt i
        (FourPhaseEncoding.enc c)
        (FourPhaseEncoding.enc c') := by
  rcases
    FourPhaseMacroModule.exists_phaseIndex_singleton_exec_of_phaseStep?
      (s := s) M hc hstep with
    ⟨i, _hPhase, hExec⟩
  have hStep :
      (FourPhaseMacroModule.network (s := s) M).StepAt i
        (FourPhaseEncoding.enc c)
        (FourPhaseEncoding.enc c') :=
    ExecOf.singleton_iff.mp hExec
  refine ⟨i, ?_⟩
  exact ⟨c, c', hc, hstep, rfl, rfl, hStep⟩

theorem networkRefinementOfFootprintedConcreteFourPhaseModule_goodExec_of_phaseStep
    {Q : Type u} [Fintype Q] [DecidableEq Q] {s : Nat}
    (M : Binary Q)
    (G :
      FourPhaseConcrete.FootprintedConcreteFourPhaseModule.{u, v, x}
        (s := s) M)
    (encAgg : State (FourPhaseSpecies Q) -> State G.CSp)
    (henc :
      forall c : MicroCfg Q s,
        encAgg (FourPhaseEncoding.enc c) = G.enc c)
    {c c' : MicroCfg Q s}
    (hc : GadgetMicroCfgWF c)
    (hstep : phaseStep? (s := s) M c = some c') :
    exists is : List (FourPhaseMacroModule.network (s := s) M).I,
      (networkRefinementOfFootprintedConcreteFourPhaseModule
        (s := s) M G encAgg henc).GoodExec
        (FourPhaseEncoding.enc c)
        (FourPhaseEncoding.enc c') is := by
  rcases
    networkRefinementOfFootprintedConcreteFourPhaseModule_goodStepAt_of_phaseStep
      (s := s) M G encAgg henc hc hstep with
    ⟨i, hGood⟩
  exact ⟨[i], ExecOf.cons hGood
    (ExecOf.nil (FourPhaseEncoding.enc c'))⟩

def ofFootprintedConcreteFourPhaseModule
    {Q : Type u} [Fintype Q] [DecidableEq Q] {s : Nat}
    (M : Binary Q)
    (G :
      FourPhaseConcrete.FootprintedConcreteFourPhaseModule.{u, v, x}
        (s := s) M)
    (encAgg : State (FourPhaseSpecies Q) -> State G.CSp)
    (henc :
      forall c : MicroCfg Q s,
        encAgg (FourPhaseEncoding.enc c) = G.enc c) :
    BimolecularFourPhaseRefinement (s := s) (T := G.CSp) M :=
  ofConcreteFourPhaseModule
    (s := s) M G.toConcreteFourPhaseModule encAgg
    (by
      intro c
      simpa [
        FourPhaseConcrete.FootprintedConcreteFourPhaseModule.toConcreteFourPhaseModule,
        ConcreteFourPhaseModule.encMicro
      ] using henc c)

/--
Safer spelling of `ofFootprintedConcreteFourPhaseModule`.

This constructor exposes only the deterministic, forward-only,
at-most-bimolecular-input refinement interface. It reuses the residual fields
of the foot-printed concrete module: scheduled executions for intended good
steps, static input-arity/rate predicates, and boundary encodings. It does not
assert a CTMC construction, race probabilities, autonomous scheduler safety,
arbitrary concrete trajectory safety, or a physical bimolecular implementation
theorem.
-/
def atMostBimolecularForwardOfFootprintedConcreteFourPhaseModule
    {Q : Type u} [Fintype Q] [DecidableEq Q] {s : Nat}
    (M : Binary Q)
    (G :
      FourPhaseConcrete.FootprintedConcreteFourPhaseModule.{u, v, x}
        (s := s) M)
    (encAgg : State (FourPhaseSpecies Q) -> State G.CSp)
    (henc :
      forall c : MicroCfg Q s,
        encAgg (FourPhaseEncoding.enc c) = G.enc c) :
    BimolecularFourPhaseRefinement (s := s) (T := G.CSp) M :=
  ofFootprintedConcreteFourPhaseModule
    (s := s) M G encAgg henc

@[simp]
theorem ofFootprintedConcreteFourPhaseModule_encMicro
    {Q : Type u} [Fintype Q] [DecidableEq Q] {s : Nat}
    (M : Binary Q)
    (G :
      FourPhaseConcrete.FootprintedConcreteFourPhaseModule.{u, v, x}
        (s := s) M)
    (encAgg : State (FourPhaseSpecies Q) -> State G.CSp)
    (henc :
      forall c : MicroCfg Q s,
        encAgg (FourPhaseEncoding.enc c) = G.enc c)
    (c : MicroCfg Q s) :
    (ofFootprintedConcreteFourPhaseModule
      (s := s) M G encAgg henc).encMicro c = G.enc c := by
  simpa [
    ofFootprintedConcreteFourPhaseModule,
    FourPhaseConcrete.FootprintedConcreteFourPhaseModule.toConcreteFourPhaseModule,
    ConcreteFourPhaseModule.encMicro
  ] using henc c

@[simp]
theorem ofFootprintedConcreteFourPhaseModule_encCTM
    {Q : Type u} [Fintype Q] [DecidableEq Q] {s : Nat}
    (M : Binary Q)
    (G :
      FourPhaseConcrete.FootprintedConcreteFourPhaseModule.{u, v, x}
        (s := s) M)
    (encAgg : State (FourPhaseSpecies Q) -> State G.CSp)
    (henc :
      forall c : MicroCfg Q s,
        encAgg (FourPhaseEncoding.enc c) = G.enc c)
    (cfg : Cfg Q Bool s) :
    (ofFootprintedConcreteFourPhaseModule
      (s := s) M G encAgg henc).encCTM cfg =
        G.enc (MicroCfg.ofCTM cfg) := by
  simpa [encCTM] using
    ofFootprintedConcreteFourPhaseModule_encMicro
      (s := s) M G encAgg henc (MicroCfg.ofCTM cfg)

def ofFootprintedConcreteFourPhaseExpansionFamily
    {Q : Type u} [Fintype Q] [DecidableEq Q] {s : Nat}
    (M : Binary Q)
    (F :
      FourPhaseConcrete.FootprintedConcreteFourPhaseExpansionFamily.{u, v, x}
        (s := s) M)
    (encAgg : State (FourPhaseSpecies Q) -> State F.CSp)
    (henc :
      forall c : MicroCfg Q s,
        encAgg (FourPhaseEncoding.enc c) = F.enc c) :
    BimolecularFourPhaseRefinement (s := s) (T := F.CSp) M :=
  ofFootprintedConcreteFourPhaseModule
    (s := s) M F.toFootprintedConcreteFourPhaseModule encAgg
    (by
      intro c
      exact henc c)

def atMostBimolecularForwardOfFootprintedConcreteFourPhaseExpansionFamily
    {Q : Type u} [Fintype Q] [DecidableEq Q] {s : Nat}
    (M : Binary Q)
    (F :
      FourPhaseConcrete.FootprintedConcreteFourPhaseExpansionFamily.{u, v, x}
        (s := s) M)
    (encAgg : State (FourPhaseSpecies Q) -> State F.CSp)
    (henc :
      forall c : MicroCfg Q s,
        encAgg (FourPhaseEncoding.enc c) = F.enc c) :
    BimolecularFourPhaseRefinement (s := s) (T := F.CSp) M :=
  ofFootprintedConcreteFourPhaseExpansionFamily (s := s) M F encAgg henc

def networkRefinementOfFootprintedConcreteFourPhaseExpansionFamily
    {Q : Type u} [Fintype Q] [DecidableEq Q] {s : Nat}
    (M : Binary Q)
    (F :
      FourPhaseConcrete.FootprintedConcreteFourPhaseExpansionFamily.{u, v, x}
        (s := s) M)
    (encAgg : State (FourPhaseSpecies Q) -> State F.CSp)
    (henc :
      forall c : MicroCfg Q s,
        encAgg (FourPhaseEncoding.enc c) = F.enc c) :
    BimolecularNetworkRefinement
      (FourPhaseMacroModule.network (s := s) M) F.network :=
  networkRefinementOfFootprintedConcreteFourPhaseModule
    (s := s) M F.toFootprintedConcreteFourPhaseModule encAgg
    (by
      intro c
      exact henc c)

@[simp]
theorem networkRefinementOfFootprintedConcreteFourPhaseExpansionFamily_enc
    {Q : Type u} [Fintype Q] [DecidableEq Q] {s : Nat}
    (M : Binary Q)
    (F :
      FourPhaseConcrete.FootprintedConcreteFourPhaseExpansionFamily.{u, v, x}
        (s := s) M)
    (encAgg : State (FourPhaseSpecies Q) -> State F.CSp)
    (henc :
      forall c : MicroCfg Q s,
        encAgg (FourPhaseEncoding.enc c) = F.enc c)
    (c : MicroCfg Q s) :
    (networkRefinementOfFootprintedConcreteFourPhaseExpansionFamily
      (s := s) M F encAgg henc).enc (FourPhaseEncoding.enc c) =
        F.enc c := by
  exact henc c

theorem networkRefinementOfFootprintedConcreteFourPhaseExpansionFamily_goodExec_of_phaseStep
    {Q : Type u} [Fintype Q] [DecidableEq Q] {s : Nat}
    (M : Binary Q)
    (F :
      FourPhaseConcrete.FootprintedConcreteFourPhaseExpansionFamily.{u, v, x}
        (s := s) M)
    (encAgg : State (FourPhaseSpecies Q) -> State F.CSp)
    (henc :
      forall c : MicroCfg Q s,
        encAgg (FourPhaseEncoding.enc c) = F.enc c)
    {c c' : MicroCfg Q s}
    (hc : GadgetMicroCfgWF c)
    (hstep : phaseStep? (s := s) M c = some c') :
    exists is : List (FourPhaseMacroModule.network (s := s) M).I,
      (networkRefinementOfFootprintedConcreteFourPhaseExpansionFamily
        (s := s) M F encAgg henc).GoodExec
        (FourPhaseEncoding.enc c)
        (FourPhaseEncoding.enc c') is := by
  simpa [networkRefinementOfFootprintedConcreteFourPhaseExpansionFamily] using
    networkRefinementOfFootprintedConcreteFourPhaseModule_goodExec_of_phaseStep
      (s := s) M F.toFootprintedConcreteFourPhaseModule encAgg
      (by
        intro c
        exact henc c)
      hc hstep

@[simp]
theorem ofFootprintedConcreteFourPhaseExpansionFamily_encMicro
    {Q : Type u} [Fintype Q] [DecidableEq Q] {s : Nat}
    (M : Binary Q)
    (F :
      FourPhaseConcrete.FootprintedConcreteFourPhaseExpansionFamily.{u, v, x}
        (s := s) M)
    (encAgg : State (FourPhaseSpecies Q) -> State F.CSp)
    (henc :
      forall c : MicroCfg Q s,
        encAgg (FourPhaseEncoding.enc c) = F.enc c)
    (c : MicroCfg Q s) :
    (ofFootprintedConcreteFourPhaseExpansionFamily
      (s := s) M F encAgg henc).encMicro c = F.enc c := by
  simpa [ofFootprintedConcreteFourPhaseExpansionFamily] using henc c

@[simp]
theorem ofFootprintedConcreteFourPhaseExpansionFamily_encCTM
    {Q : Type u} [Fintype Q] [DecidableEq Q] {s : Nat}
    (M : Binary Q)
    (F :
      FourPhaseConcrete.FootprintedConcreteFourPhaseExpansionFamily.{u, v, x}
        (s := s) M)
    (encAgg : State (FourPhaseSpecies Q) -> State F.CSp)
    (henc :
      forall c : MicroCfg Q s,
        encAgg (FourPhaseEncoding.enc c) = F.enc c)
    (cfg : Cfg Q Bool s) :
    (ofFootprintedConcreteFourPhaseExpansionFamily
      (s := s) M F encAgg henc).encCTM cfg =
        F.enc (MicroCfg.ofCTM cfg) := by
  simpa [encCTM] using
    ofFootprintedConcreteFourPhaseExpansionFamily_encMicro
      (s := s) M F encAgg henc (MicroCfg.ofCTM cfg)

def statePairTransferNetworkRefinement
    {Q : Type u} [Fintype Q] [DecidableEq Q] {s : Nat}
    (M : Binary Q) :
    BimolecularNetworkRefinement
      (FourPhaseMacroModule.network (s := s) M)
      (FourPhaseEncoding.statePairTransferFootprintedConcreteFourPhaseExpansionFamily
        (s := s) M).network :=
  networkRefinementOfFootprintedConcreteFourPhaseExpansionFamily
    (s := s) M
    (FourPhaseEncoding.statePairTransferFootprintedConcreteFourPhaseExpansionFamily
      (s := s) M)
    id
    (by
      intro c
      rfl)

abbrev statePairTransferNetwork
    {Q : Type u} [Fintype Q] [DecidableEq Q] {s : Nat}
    (M : Binary Q) : Network (FourPhaseEncoding.Species Q) :=
  (FourPhaseEncoding.statePairTransferFootprintedConcreteFourPhaseExpansionFamily
    (s := s) M).network

def statePairTransferBimolecularFourPhaseRefinement
    {Q : Type u} [Fintype Q] [DecidableEq Q] {s : Nat}
    (M : Binary Q) :
    BimolecularFourPhaseRefinement
      (s := s) (T := FourPhaseEncoding.Species Q) M :=
  ofFootprintedConcreteFourPhaseExpansionFamily
    (s := s) M
    (FourPhaseEncoding.statePairTransferFootprintedConcreteFourPhaseExpansionFamily
      (s := s) M)
    id
    (by
      intro c
      rfl)

def statePairTransferAtMostBimolecularForwardRefinement
    {Q : Type u} [Fintype Q] [DecidableEq Q] {s : Nat}
    (M : Binary Q) :
    AtMostBimolecularForwardFourPhaseRefinement
      (s := s) (T := FourPhaseEncoding.Species Q) M :=
  statePairTransferBimolecularFourPhaseRefinement (s := s) M

@[simp]
theorem statePairTransferBimolecularFourPhaseRefinement_encMicro
    {Q : Type u} [Fintype Q] [DecidableEq Q] {s : Nat}
    (M : Binary Q) (c : MicroCfg Q s) :
    (statePairTransferBimolecularFourPhaseRefinement
      (s := s) M).encMicro c =
        FourPhaseEncoding.enc c := by
  rfl

@[simp]
theorem statePairTransferBimolecularFourPhaseRefinement_encCTM
    {Q : Type u} [Fintype Q] [DecidableEq Q] {s : Nat}
    (M : Binary Q) (cfg : Cfg Q Bool s) :
    (statePairTransferBimolecularFourPhaseRefinement
      (s := s) M).encCTM cfg =
        FourPhaseEncoding.enc (MicroCfg.ofCTM cfg) := by
  rfl

theorem statePairTransferBimolecularFourPhaseRefinement_goodExec_of_phaseStep
    {Q : Type u} [Fintype Q] [DecidableEq Q] {s : Nat}
    (M : Binary Q)
    {c c' : MicroCfg Q s}
    (hc : GadgetMicroCfgWF c)
    (hstep : phaseStep? (s := s) M c = some c') :
    exists is : List (FourPhaseMacroModule.network (s := s) M).I,
      (statePairTransferBimolecularFourPhaseRefinement
        (s := s) M).R.GoodExec
        (FourPhaseEncoding.enc c)
        (FourPhaseEncoding.enc c') is :=
  (statePairTransferBimolecularFourPhaseRefinement
    (s := s) M).goodExec_of_phaseStep hc hstep

theorem statePairTransferNetwork_allAtMostBimolecularInput
    {Q : Type u} [Fintype Q] [DecidableEq Q] {s : Nat}
    (M : Binary Q) :
    (statePairTransferNetwork (s := s) M).allAtMostBimolecularInput :=
  (statePairTransferBimolecularFourPhaseRefinement
    (s := s) M).concrete_allAtMostBimolecularInput

theorem statePairTransferNetwork_hasPositiveRates
    {Q : Type u} [Fintype Q] [DecidableEq Q] {s : Nat}
    (M : Binary Q) :
    (statePairTransferNetwork (s := s) M).hasPositiveRates :=
  (statePairTransferBimolecularFourPhaseRefinement
    (s := s) M).concrete_hasPositiveRates

theorem statePairTransferNetwork_allAtMostBimolecularFull
    {Q : Type u} [Fintype Q] [DecidableEq Q] {s : Nat}
    (M : Binary Q) :
    (statePairTransferNetwork (s := s) M).allAtMostBimolecularFull := by
  change
    ((FourPhaseEncoding.statePairTransferFootprintedConcreteFourPhaseExpansionFamily
      (s := s) M).network).allAtMostBimolecularFull
  dsimp [
    FourPhaseConcrete.FootprintedConcreteFourPhaseExpansionFamily.network,
    FourPhaseEncoding.statePairTransferFootprintedConcreteFourPhaseExpansionFamily
  ]
  exact phaseParallel4_allAtMostBimolecularFull
    (FourPhaseEncoding.controlSwapStatePairNetwork_allAtMostBimolecularFull
      (Q := Q))
    (FourPhaseEncoding.tapeTransferWithControlStatePairNetwork_allAtMostBimolecularFull
      (Q := Q))
    (FourPhaseEncoding.tapeTransferWithControlStatePairNetwork_allAtMostBimolecularFull
      (Q := Q))
    (FourPhaseEncoding.tapeTransferWithControlStatePairNetwork_allAtMostBimolecularFull
      (Q := Q))

theorem statePairTransferNetwork_allAtMostBimolecularOutput
    {Q : Type u} [Fintype Q] [DecidableEq Q] {s : Nat}
    (M : Binary Q) :
    (statePairTransferNetwork (s := s) M).allAtMostBimolecularOutput :=
  Network.allAtMostBimolecularOutput_of_full
    (statePairTransferNetwork_allAtMostBimolecularFull (s := s) M)

theorem statePairTransferNetwork_allUnitRate
    {Q : Type u} [Fintype Q] [DecidableEq Q] {s : Nat}
    (M : Binary Q) :
    (statePairTransferNetwork (s := s) M).allUnitRate := by
  change
    ((FourPhaseEncoding.statePairTransferFootprintedConcreteFourPhaseExpansionFamily
      (s := s) M).network).allUnitRate
  dsimp [
    FourPhaseConcrete.FootprintedConcreteFourPhaseExpansionFamily.network,
    FourPhaseEncoding.statePairTransferFootprintedConcreteFourPhaseExpansionFamily
  ]
  exact phaseParallel4_allUnitRate
    (FourPhaseEncoding.controlSwapStatePairNetwork_allUnitRate
      (Q := Q))
    (FourPhaseEncoding.tapeTransferWithControlStatePairNetwork_allUnitRate
      (Q := Q))
    (FourPhaseEncoding.tapeTransferWithControlStatePairNetwork_allUnitRate
      (Q := Q))
    (FourPhaseEncoding.tapeTransferWithControlStatePairNetwork_allUnitRate
      (Q := Q))

theorem statePairTransferNetwork_equalRates
    {Q : Type u} [Fintype Q] [DecidableEq Q] {s : Nat}
    (M : Binary Q) :
    (statePairTransferNetwork (s := s) M).equalRates :=
  Network.equalRates_of_allUnitRate
    (statePairTransferNetwork_allUnitRate (s := s) M)

theorem statePairTransfer_exec_of_ctm_steps
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s n : Nat} (M : Binary Q)
    {cfg cfg' : Cfg Q Bool s}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg') :
    exists is : List (statePairTransferNetwork (s := s) M).I,
      (statePairTransferNetwork (s := s) M).Exec
        (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg))
        (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg')) is := by
  simpa using
    (statePairTransferBimolecularFourPhaseRefinement
      (s := s) M).exec_of_ctm_steps h

noncomputable def statePairTransfer_intendedSchedule_of_ctm_steps
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s n : Nat} (M : Binary Q)
    {cfg cfg' : Cfg Q Bool s}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg') :
    (statePairTransferNetwork (s := s) M).IntendedSchedule
      (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg))
      (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg')) := by
  simpa using
    (statePairTransferBimolecularFourPhaseRefinement
      (s := s) M).intendedSchedule_of_ctm_steps h

theorem statePairTransfer_reaches_of_ctm_steps
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s n : Nat} (M : Binary Q)
    {cfg cfg' : Cfg Q Bool s}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg') :
    (statePairTransferNetwork (s := s) M).Reaches
      (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg))
      (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg')) := by
  simpa using
    (statePairTransferBimolecularFourPhaseRefinement
      (s := s) M).reaches_of_ctm_steps h

theorem statePairTransfer_state_after_ctm_steps_of_intendedWinsRaceAt
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s n : Nat} (M : Binary Q)
    {cfg cfg' : Cfg Q Bool s}
    {path : (statePairTransferNetwork (s := s) M).Path}
    {Bad : (statePairTransferNetwork (s := s) M).BadIndexSet}
    {t : Nat}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg')
    (hwin :
      path.IntendedWinsRaceAt Bad t
        (statePairTransfer_intendedSchedule_of_ctm_steps
          (s := s) M h)) :
    path.state
        (t +
          (statePairTransfer_intendedSchedule_of_ctm_steps
            (s := s) M h).firingCount) =
      FourPhaseEncoding.enc (MicroCfg.ofCTM cfg') := by
  simpa [statePairTransfer_intendedSchedule_of_ctm_steps] using
    (statePairTransferBimolecularFourPhaseRefinement
      (s := s) M).state_after_ctm_steps_of_intendedWinsRaceAt h hwin

theorem statePairTransfer_coverableFrom_of_ctm_steps_covers
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s n : Nat} (M : Binary Q)
    {cfg cfg' : Cfg Q Bool s}
    {target : State (FourPhaseEncoding.Species Q)}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg')
    (hCovers :
      Covers
        (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg'))
        target) :
    (statePairTransferNetwork (s := s) M).CoverableFrom
      (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg))
      target := by
  simpa using
    (statePairTransferBimolecularFourPhaseRefinement
      (s := s) M).coverableFrom_of_ctm_steps_covers h hCovers

theorem statePairTransfer_coverableFrom_of_ctm_steps_of_le
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s n : Nat} (M : Binary Q)
    {cfg cfg' : Cfg Q Bool s}
    {target : State (FourPhaseEncoding.Species Q)}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg')
    (hTarget :
      forall species,
        target species <=
          FourPhaseEncoding.enc (MicroCfg.ofCTM cfg') species) :
    (statePairTransferNetwork (s := s) M).CoverableFrom
      (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg))
      target :=
  statePairTransfer_coverableFrom_of_ctm_steps_covers
    (s := s) M h hTarget

theorem statePairTransfer_speciesCoverableFrom_of_ctm_steps_coord
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s n : Nat} (M : Binary Q)
    {cfg cfg' : Cfg Q Bool s}
    {species : FourPhaseEncoding.Species Q} {amount : Nat}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg')
    (hamount :
      amount <=
        FourPhaseEncoding.enc (MicroCfg.ofCTM cfg') species) :
    (statePairTransferNetwork (s := s) M).SpeciesCoverableFrom
      (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg))
      species amount := by
  simpa using
    (statePairTransferBimolecularFourPhaseRefinement
      (s := s) M).speciesCoverableFrom_of_ctm_steps_coord
        h hamount

theorem statePairTransfer_speciesCoverableFrom_one_of_ctm_steps_pos
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s n : Nat} (M : Binary Q)
    {cfg cfg' : Cfg Q Bool s}
    {species : FourPhaseEncoding.Species Q}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg')
    (hpos :
      0 < FourPhaseEncoding.enc (MicroCfg.ofCTM cfg') species) :
    (statePairTransferNetwork (s := s) M).SpeciesCoverableFrom
      (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg))
      species := by
  simpa using
    (statePairTransferBimolecularFourPhaseRefinement
      (s := s) M).speciesCoverableFrom_one_of_ctm_steps_pos
        h hpos

theorem statePairTransfer_tape_speciesCoverableFrom_of_ctm_steps
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s n : Nat} (M : Binary Q)
    {cfg cfg' : Cfg Q Bool s}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg') :
    (statePairTransferNetwork (s := s) M).SpeciesCoverableFrom
      (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg))
      FourPhaseSpecies.tape
      (Encoding.base3Val cfg'.tape) :=
  statePairTransfer_speciesCoverableFrom_of_ctm_steps_coord
    (s := s) M h (by simp [MicroCfg.ofCTM])

theorem statePairTransfer_tapeBar_speciesCoverableFrom_of_ctm_steps
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s n : Nat} (M : Binary Q)
    {cfg cfg' : Cfg Q Bool s}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg') :
    (statePairTransferNetwork (s := s) M).SpeciesCoverableFrom
      (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg))
      FourPhaseSpecies.tapeBar
      (FourPhaseEncoding.maxTape s - Encoding.base3Val cfg'.tape) :=
  statePairTransfer_speciesCoverableFrom_of_ctm_steps_coord
    (s := s) M h (by simp [MicroCfg.ofCTM])

theorem statePairTransfer_exec_of_ctm_steps_bounded
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s n : Nat} (M : Binary Q)
    {cfg cfg' : Cfg Q Bool s}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg') :
    exists is : List (statePairTransferNetwork (s := s) M).I,
      (statePairTransferNetwork (s := s) M).Exec
        (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg))
        (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg')) is /\
        is.length <=
          ((FourPhaseEncoding.statePairTransferConcreteFourPhaseModule
              (s := s) M).step_len_bound * 4) * n := by
  simpa [
    statePairTransferNetwork,
    FourPhaseEncoding.statePairTransferConcreteFourPhaseModule
  ] using
    (FourPhaseEncoding.statePairTransferConcreteFourPhaseModule
      (s := s) M).exec_of_ctm_steps_bounded h

noncomputable def statePairTransfer_boundedIntendedSchedule_of_ctm_steps
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s n : Nat} (M : Binary Q)
    {cfg cfg' : Cfg Q Bool s}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg') :
    (statePairTransferNetwork (s := s) M).BoundedIntendedSchedule
      (((FourPhaseEncoding.statePairTransferConcreteFourPhaseModule
          (s := s) M).step_len_bound * 4) * n)
      (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg))
      (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg')) := by
  simpa [
    statePairTransferNetwork,
    FourPhaseEncoding.statePairTransferConcreteFourPhaseModule
  ] using
    (FourPhaseEncoding.statePairTransferConcreteFourPhaseModule
      (s := s) M).boundedIntendedSchedule_of_ctm_steps h

theorem statePairTransfer_boundedIntendedSchedule_firingCount_le_of_ctm_steps
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s n : Nat} (M : Binary Q)
    {cfg cfg' : Cfg Q Bool s}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg') :
    (statePairTransfer_boundedIntendedSchedule_of_ctm_steps
      (s := s) M h).firingCount <=
        ((FourPhaseEncoding.statePairTransferConcreteFourPhaseModule
            (s := s) M).step_len_bound * 4) * n :=
  Network.BoundedIntendedSchedule.firingCount_le_bound
    (statePairTransfer_boundedIntendedSchedule_of_ctm_steps
      (s := s) M h)

theorem statePairTransfer_boundedIntendedSchedule_reaches_of_ctm_steps
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s n : Nat} (M : Binary Q)
    {cfg cfg' : Cfg Q Bool s}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg') :
    (statePairTransferNetwork (s := s) M).Reaches
      (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg))
      (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg')) :=
  (statePairTransfer_boundedIntendedSchedule_of_ctm_steps
    (s := s) M h).reaches

end BimolecularFourPhaseRefinement

end CTM

end Ripple.sCRNUniversality
