import Ripple.sCRNUniversality.Computation.CTM.FourPhaseWellFormedModule
import Ripple.sCRNUniversality.Computation.CTM.FourPhaseFootprint
import Ripple.sCRNUniversality.Core.Finite

/-!
# Concrete four-phase module interface

This file records a deterministic boundary-to-boundary interface for a future
concrete four-phase network. It is an interface for scheduled executions, not a
stochastic process construction and not a proof that the current macro network
is physically or bimolecularly implemented.
-/

namespace Ripple.sCRNUniversality

namespace CTM

universe u v w x

abbrev ConcreteSpecies (Q : Type u) (Aux : Type v) :=
  Sum (FourPhaseSpecies Q) Aux

namespace ConcreteSpecies

def ideal {Q : Type u} {Aux : Type v} :
    FourPhaseSpecies Q -> ConcreteSpecies Q Aux :=
  Sum.inl

def aux {Q : Type u} {Aux : Type v} :
    Aux -> ConcreteSpecies Q Aux :=
  Sum.inr

theorem ideal_injective {Q : Type u} {Aux : Type v} :
    Function.Injective
      (ideal : FourPhaseSpecies Q -> ConcreteSpecies Q Aux) := by
  intro x y h
  cases h
  rfl

def projectIdeal {Q : Type u} {Aux : Type v}
    (z : State (ConcreteSpecies Q Aux)) :
    State (FourPhaseSpecies Q) :=
  fun species => z (ideal species)

def auxZero {Q : Type u} {Aux : Type v}
    (z : State (ConcreteSpecies Q Aux)) : Prop :=
  forall a : Aux, z (aux a) = 0

end ConcreteSpecies

namespace FourPhaseConcrete

def ConcreteLocalFootprint
    {Q : Type u} {s : Nat} {CSp : Type v}
    (ideal : FourPhaseSpecies Q -> CSp)
    (auxFootprint : MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop)
    (c c' : MicroCfg Q s) :
    CSp -> Prop :=
  fun sp =>
    (exists species : FourPhaseSpecies Q,
      FourPhaseSpecies.IsLocalMacroFootprint
        (FourPhaseSpecies.ctrlOf c.state)
        (FourPhaseSpecies.ctrlOf c'.state)
        species /\
      sp = ideal species) \/
    auxFootprint c c' sp

theorem concreteLocalFootprint_mono
    {Q : Type u} {s : Nat} {CSp : Type v}
    {ideal : FourPhaseSpecies Q -> CSp}
    {auxFootprint : MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop}
    {c c' : MicroCfg Q s}
    {P : CSp -> Prop}
    (hIdeal :
      forall species : FourPhaseSpecies Q,
        FourPhaseSpecies.IsLocalMacroFootprint
          (FourPhaseSpecies.ctrlOf c.state)
          (FourPhaseSpecies.ctrlOf c'.state)
          species ->
        P (ideal species))
    (hAux :
      forall sp, auxFootprint c c' sp -> P sp) :
    forall sp,
      ConcreteLocalFootprint ideal auxFootprint c c' sp -> P sp := by
  intro sp hFoot
  rcases hFoot with hVisible | hAuxFoot
  · rcases hVisible with ⟨species, hLocal, hEq⟩
    simpa [hEq] using hIdeal species hLocal
  · exact hAux sp hAuxFoot

theorem concreteLocalFootprint_mono_of_members
    {Q : Type u} {s : Nat} {CSp : Type v}
    {ideal : FourPhaseSpecies Q -> CSp}
    {auxFootprint : MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop}
    {c c' : MicroCfg Q s}
    {P : CSp -> Prop}
    (hold : P (ideal (FourPhaseSpecies.ctrlOf c.state)))
    (hnew : P (ideal (FourPhaseSpecies.ctrlOf c'.state)))
    (htape : P (ideal FourPhaseSpecies.tape))
    (htapeBar : P (ideal FourPhaseSpecies.tapeBar))
    (hAux :
      forall sp, auxFootprint c c' sp -> P sp) :
    forall sp,
      ConcreteLocalFootprint ideal auxFootprint c c' sp -> P sp :=
  concreteLocalFootprint_mono
    (ideal := ideal)
    (auxFootprint := auxFootprint)
    (c := c)
    (c' := c')
    (P := P)
    (by
      intro species hLocal
      exact FourPhaseSpecies.localMacroFootprint_mono
        (oldCtrl := FourPhaseSpecies.ctrlOf c.state)
        (newCtrl := FourPhaseSpecies.ctrlOf c'.state)
        (P := fun species => P (ideal species))
        hold hnew htape htapeBar hLocal)
    hAux

structure ConcreteGoodStepSchedule
    {Q : Type u} {s : Nat}
    {CSp : Type v} [Fintype CSp]
    (N : Network.{v, w} CSp)
    (enc : MicroCfg Q s -> State CSp)
    (Foot : MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop)
    (L : Nat)
    (c c' : MicroCfg Q s) where
  schedule : List N.I
  exec : N.Exec (enc c) (enc c') schedule
  length_le : schedule.length <= L
  footprint : N.ScheduleFootprintWithin schedule (Foot c c')

namespace ConcreteGoodStepSchedule

def toIntendedSchedule
    {Q : Type u} {s : Nat}
    {CSp : Type v} [Fintype CSp]
    {N : Network.{v, w} CSp}
    {enc : MicroCfg Q s -> State CSp}
    {Foot : MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop}
    {L : Nat} {c c' : MicroCfg Q s}
    (Sched : ConcreteGoodStepSchedule N enc Foot L c c') :
    N.IntendedSchedule (enc c) (enc c') where
  schedule := Sched.schedule
  exec := Sched.exec

def toBoundedIntendedSchedule
    {Q : Type u} {s : Nat}
    {CSp : Type v} [Fintype CSp]
    {N : Network.{v, w} CSp}
    {enc : MicroCfg Q s -> State CSp}
    {Foot : MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop}
    {L : Nat} {c c' : MicroCfg Q s}
    (Sched : ConcreteGoodStepSchedule N enc Foot L c c') :
    N.BoundedIntendedSchedule L (enc c) (enc c') where
  schedule := Sched.schedule
  exec := Sched.exec
  length_bound := Sched.length_le

@[simp]
theorem toIntendedSchedule_schedule
    {Q : Type u} {s : Nat}
    {CSp : Type v} [Fintype CSp]
    {N : Network.{v, w} CSp}
    {enc : MicroCfg Q s -> State CSp}
    {Foot : MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop}
    {L : Nat} {c c' : MicroCfg Q s}
    (Sched : ConcreteGoodStepSchedule N enc Foot L c c') :
    Sched.toIntendedSchedule.schedule = Sched.schedule := by
  rfl

@[simp]
theorem toBoundedIntendedSchedule_schedule
    {Q : Type u} {s : Nat}
    {CSp : Type v} [Fintype CSp]
    {N : Network.{v, w} CSp}
    {enc : MicroCfg Q s -> State CSp}
    {Foot : MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop}
    {L : Nat} {c c' : MicroCfg Q s}
    (Sched : ConcreteGoodStepSchedule N enc Foot L c c') :
    Sched.toBoundedIntendedSchedule.schedule = Sched.schedule := by
  rfl

theorem toIntendedSchedule_scheduleFootprintWithin
    {Q : Type u} {s : Nat}
    {CSp : Type v} [Fintype CSp]
    {N : Network.{v, w} CSp}
    {enc : MicroCfg Q s -> State CSp}
    {Foot : MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop}
    {L : Nat} {c c' : MicroCfg Q s}
    (Sched : ConcreteGoodStepSchedule N enc Foot L c c') :
    N.ScheduleFootprintWithin
      Sched.toIntendedSchedule.schedule
      (Foot c c') := by
  simpa using Sched.footprint

theorem toBoundedIntendedSchedule_scheduleFootprintWithin
    {Q : Type u} {s : Nat}
    {CSp : Type v} [Fintype CSp]
    {N : Network.{v, w} CSp}
    {enc : MicroCfg Q s -> State CSp}
    {Foot : MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop}
    {L : Nat} {c c' : MicroCfg Q s}
    (Sched : ConcreteGoodStepSchedule N enc Foot L c c') :
    N.ScheduleFootprintWithin
      Sched.toBoundedIntendedSchedule.schedule
      (Foot c c') := by
  simpa using Sched.footprint

def liftSigma
    {Q : Type u} {s : Nat}
    {CSp : Type v} [Fintype CSp]
    {A : Type x} [Fintype A]
    (Nfam : A -> Network.{v, w} CSp)
    {enc : MicroCfg Q s -> State CSp}
    {Foot : MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop}
    {L : Nat} {c c' : MicroCfg Q s}
    (a : A)
    (Sched : ConcreteGoodStepSchedule (Nfam a) enc Foot L c c') :
    ConcreteGoodStepSchedule (Network.sigma Nfam) enc Foot L c c' where
  schedule := Sched.schedule.map (fun i => Sigma.mk a i)
  exec := Network.sigma_exec Nfam a Sched.exec
  length_le := by
    simpa [List.length_map] using Sched.length_le
  footprint :=
    Network.sigma_scheduleFootprintWithin Nfam a Sched.footprint

@[simp]
theorem liftSigma_schedule
    {Q : Type u} {s : Nat}
    {CSp : Type v} [Fintype CSp]
    {A : Type x} [Fintype A]
    (Nfam : A -> Network.{v, w} CSp)
    {enc : MicroCfg Q s -> State CSp}
    {Foot : MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop}
    {L : Nat} {c c' : MicroCfg Q s}
    (a : A)
    (Sched : ConcreteGoodStepSchedule (Nfam a) enc Foot L c c') :
    (liftSigma Nfam a Sched).schedule =
      Sched.schedule.map (fun i => Sigma.mk a i) := by
  rfl

@[simp]
theorem liftSigma_toIntendedSchedule
    {Q : Type u} {s : Nat}
    {CSp : Type v} [Fintype CSp]
    {A : Type x} [Fintype A]
    (Nfam : A -> Network.{v, w} CSp)
    {enc : MicroCfg Q s -> State CSp}
    {Foot : MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop}
    {L : Nat} {c c' : MicroCfg Q s}
    (a : A)
    (Sched : ConcreteGoodStepSchedule (Nfam a) enc Foot L c c') :
    (liftSigma Nfam a Sched).toIntendedSchedule =
      Sched.toIntendedSchedule.sigma := by
  rfl

@[simp]
theorem liftSigma_toBoundedIntendedSchedule
    {Q : Type u} {s : Nat}
    {CSp : Type v} [Fintype CSp]
    {A : Type x} [Fintype A]
    (Nfam : A -> Network.{v, w} CSp)
    {enc : MicroCfg Q s -> State CSp}
    {Foot : MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop}
    {L : Nat} {c c' : MicroCfg Q s}
    (a : A)
    (Sched : ConcreteGoodStepSchedule (Nfam a) enc Foot L c c') :
    (liftSigma Nfam a Sched).toBoundedIntendedSchedule =
      Sched.toBoundedIntendedSchedule.sigma := by
  rfl

@[simp]
theorem liftSigma_toIntendedSchedule_firingCount
    {Q : Type u} {s : Nat}
    {CSp : Type v} [Fintype CSp]
    {A : Type x} [Fintype A]
    (Nfam : A -> Network.{v, w} CSp)
    {enc : MicroCfg Q s -> State CSp}
    {Foot : MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop}
    {L : Nat} {c c' : MicroCfg Q s}
    (a : A)
    (Sched : ConcreteGoodStepSchedule (Nfam a) enc Foot L c c') :
    (liftSigma Nfam a Sched).toIntendedSchedule.firingCount =
      Sched.toIntendedSchedule.firingCount := by
  exact List.length_map
    (f := fun i => (Sigma.mk a i : Sigma (fun a => (Nfam a).I)))
    (as := Sched.schedule)

@[simp]
theorem liftSigma_toBoundedIntendedSchedule_firingCount
    {Q : Type u} {s : Nat}
    {CSp : Type v} [Fintype CSp]
    {A : Type x} [Fintype A]
    (Nfam : A -> Network.{v, w} CSp)
    {enc : MicroCfg Q s -> State CSp}
    {Foot : MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop}
    {L : Nat} {c c' : MicroCfg Q s}
    (a : A)
    (Sched : ConcreteGoodStepSchedule (Nfam a) enc Foot L c c') :
    (liftSigma Nfam a Sched).toBoundedIntendedSchedule.firingCount =
      Sched.toBoundedIntendedSchedule.firingCount := by
  exact List.length_map
    (f := fun i => (Sigma.mk a i : Sigma (fun a => (Nfam a).I)))
    (as := Sched.schedule)

@[simp]
theorem toBoundedIntendedSchedule_toIntendedSchedule
    {Q : Type u} {s : Nat}
    {CSp : Type v} [Fintype CSp]
    {N : Network.{v, w} CSp}
    {enc : MicroCfg Q s -> State CSp}
    {Foot : MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop}
    {L : Nat} {c c' : MicroCfg Q s}
    (Sched : ConcreteGoodStepSchedule N enc Foot L c c') :
    Sched.toBoundedIntendedSchedule.toIntendedSchedule =
      Sched.toIntendedSchedule := by
  rfl

@[simp]
theorem toBoundedIntendedSchedule_firingCount
    {Q : Type u} {s : Nat}
    {CSp : Type v} [Fintype CSp]
    {N : Network.{v, w} CSp}
    {enc : MicroCfg Q s -> State CSp}
    {Foot : MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop}
    {L : Nat} {c c' : MicroCfg Q s}
    (Sched : ConcreteGoodStepSchedule N enc Foot L c c') :
    Sched.toBoundedIntendedSchedule.firingCount =
      Sched.schedule.length := by
  rfl

theorem boundedFiringCount_le
    {Q : Type u} {s : Nat}
    {CSp : Type v} [Fintype CSp]
    {N : Network.{v, w} CSp}
    {enc : MicroCfg Q s -> State CSp}
    {Foot : MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop}
    {L : Nat} {c c' : MicroCfg Q s}
    (Sched : ConcreteGoodStepSchedule N enc Foot L c c') :
    Sched.toBoundedIntendedSchedule.firingCount <= L :=
  Sched.toBoundedIntendedSchedule.firingCount_le_bound

theorem toIntendedSchedule_firingCount_le
    {Q : Type u} {s : Nat}
    {CSp : Type v} [Fintype CSp]
    {N : Network.{v, w} CSp}
    {enc : MicroCfg Q s -> State CSp}
    {Foot : MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop}
    {L : Nat} {c c' : MicroCfg Q s}
    (Sched : ConcreteGoodStepSchedule N enc Foot L c c') :
    Sched.toIntendedSchedule.firingCount <= L := by
  simpa [ConcreteGoodStepSchedule.toIntendedSchedule] using
    Sched.length_le

theorem reaches
    {Q : Type u} {s : Nat}
    {CSp : Type v} [Fintype CSp]
    {N : Network.{v, w} CSp}
    {enc : MicroCfg Q s -> State CSp}
    {Foot : MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop}
    {L : Nat} {c c' : MicroCfg Q s}
    (Sched : ConcreteGoodStepSchedule N enc Foot L c c') :
    N.Reaches (enc c) (enc c') :=
  Sched.toIntendedSchedule.reaches

theorem executableSchedule
    {Q : Type u} {s : Nat}
    {CSp : Type v} [Fintype CSp]
    {N : Network.{v, w} CSp}
    {enc : MicroCfg Q s -> State CSp}
    {Foot : MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop}
    {L : Nat} {c c' : MicroCfg Q s}
    (Sched : ConcreteGoodStepSchedule N enc Foot L c c') :
    N.ExecutableSchedule (enc c) Sched.schedule :=
  Sched.toIntendedSchedule.executableSchedule

theorem boundedExecutableSchedule
    {Q : Type u} {s : Nat}
    {CSp : Type v} [Fintype CSp]
    {N : Network.{v, w} CSp}
    {enc : MicroCfg Q s -> State CSp}
    {Foot : MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop}
    {L : Nat} {c c' : MicroCfg Q s}
    (Sched : ConcreteGoodStepSchedule N enc Foot L c c') :
    N.ExecutableSchedule
      (enc c) Sched.toBoundedIntendedSchedule.schedule :=
  Sched.toBoundedIntendedSchedule.executableSchedule

theorem coverableFrom_of_covers
    {Q : Type u} {s : Nat}
    {CSp : Type v} [Fintype CSp]
    {N : Network.{v, w} CSp}
    {enc : MicroCfg Q s -> State CSp}
    {Foot : MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop}
    {L : Nat} {c c' : MicroCfg Q s}
    (Sched : ConcreteGoodStepSchedule N enc Foot L c c')
    {target : State CSp}
    (hCovers : Covers (enc c') target) :
    N.CoverableFrom (enc c) target :=
  Sched.toIntendedSchedule.coverableFrom_of_covers hCovers

theorem coverableFrom_of_le
    {Q : Type u} {s : Nat}
    {CSp : Type v} [Fintype CSp]
    {N : Network.{v, w} CSp}
    {enc : MicroCfg Q s -> State CSp}
    {Foot : MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop}
    {L : Nat} {c c' : MicroCfg Q s}
    (Sched : ConcreteGoodStepSchedule N enc Foot L c c')
    {target : State CSp}
    (hTarget : forall sp, target sp <= enc c' sp) :
    N.CoverableFrom (enc c) target :=
  Sched.coverableFrom_of_covers hTarget

theorem speciesCoverableFrom_of_coord
    {Q : Type u} {s : Nat}
    {CSp : Type v} [Fintype CSp] [DecidableEq CSp]
    {N : Network.{v, w} CSp}
    {enc : MicroCfg Q s -> State CSp}
    {Foot : MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop}
    {L : Nat} {c c' : MicroCfg Q s}
    (Sched : ConcreteGoodStepSchedule N enc Foot L c c')
    {species : CSp} {amount : Nat}
    (hamount : amount <= enc c' species) :
    N.SpeciesCoverableFrom (enc c) species amount :=
  Sched.toIntendedSchedule.speciesCoverableFrom_of_coord hamount

theorem speciesCoverableFrom_one_of_pos
    {Q : Type u} {s : Nat}
    {CSp : Type v} [Fintype CSp] [DecidableEq CSp]
    {N : Network.{v, w} CSp}
    {enc : MicroCfg Q s -> State CSp}
    {Foot : MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop}
    {L : Nat} {c c' : MicroCfg Q s}
    (Sched : ConcreteGoodStepSchedule N enc Foot L c c')
    {species : CSp}
    (hpos : 0 < enc c' species) :
    N.SpeciesCoverableFrom (enc c) species :=
  Sched.toIntendedSchedule.speciesCoverableFrom_one_of_pos hpos

def parallel_inl
    {Q : Type u} {s : Nat}
    {CSp : Type v} [Fintype CSp]
    {N M : Network.{v, w} CSp}
    {enc : MicroCfg Q s -> State CSp}
    {Foot : MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop}
    {L : Nat} {c c' : MicroCfg Q s}
    (Sched : ConcreteGoodStepSchedule N enc Foot L c c') :
    ConcreteGoodStepSchedule (N.parallel M) enc Foot L c c' where
  schedule := Sched.schedule.map Sum.inl
  exec := Network.parallel_exec_inl N M Sched.exec
  length_le := by
    simpa using Sched.length_le
  footprint :=
    Network.parallel_scheduleFootprintWithin_inl Sched.footprint

def parallel_inr
    {Q : Type u} {s : Nat}
    {CSp : Type v} [Fintype CSp]
    {N M : Network.{v, w} CSp}
    {enc : MicroCfg Q s -> State CSp}
    {Foot : MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop}
    {L : Nat} {c c' : MicroCfg Q s}
    (Sched : ConcreteGoodStepSchedule M enc Foot L c c') :
    ConcreteGoodStepSchedule (N.parallel M) enc Foot L c c' where
  schedule := Sched.schedule.map Sum.inr
  exec := Network.parallel_exec_inr N M Sched.exec
  length_le := by
    simpa using Sched.length_le
  footprint :=
    Network.parallel_scheduleFootprintWithin_inr Sched.footprint

@[simp]
theorem parallel_inl_schedule
    {Q : Type u} {s : Nat}
    {CSp : Type v} [Fintype CSp]
    {N M : Network.{v, w} CSp}
    {enc : MicroCfg Q s -> State CSp}
    {Foot : MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop}
    {L : Nat} {c c' : MicroCfg Q s}
    (Sched : ConcreteGoodStepSchedule N enc Foot L c c') :
    (Sched.parallel_inl (M := M)).schedule =
      Sched.schedule.map Sum.inl := by
  rfl

@[simp]
theorem parallel_inr_schedule
    {Q : Type u} {s : Nat}
    {CSp : Type v} [Fintype CSp]
    {N M : Network.{v, w} CSp}
    {enc : MicroCfg Q s -> State CSp}
    {Foot : MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop}
    {L : Nat} {c c' : MicroCfg Q s}
    (Sched : ConcreteGoodStepSchedule M enc Foot L c c') :
    (Sched.parallel_inr (N := N)).schedule =
      Sched.schedule.map Sum.inr := by
  rfl

@[simp]
theorem parallel_inl_firingCount
    {Q : Type u} {s : Nat}
    {CSp : Type v} [Fintype CSp]
    {N M : Network.{v, w} CSp}
    {enc : MicroCfg Q s -> State CSp}
    {Foot : MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop}
    {L : Nat} {c c' : MicroCfg Q s}
    (Sched : ConcreteGoodStepSchedule N enc Foot L c c') :
    (Sched.parallel_inl (M := M)).toBoundedIntendedSchedule.firingCount =
      Sched.toBoundedIntendedSchedule.firingCount := by
  exact List.length_map (f := Sum.inl) (as := Sched.schedule)

@[simp]
theorem parallel_inr_firingCount
    {Q : Type u} {s : Nat}
    {CSp : Type v} [Fintype CSp]
    {N M : Network.{v, w} CSp}
    {enc : MicroCfg Q s -> State CSp}
    {Foot : MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop}
    {L : Nat} {c c' : MicroCfg Q s}
    (Sched : ConcreteGoodStepSchedule M enc Foot L c c') :
    (Sched.parallel_inr (N := N)).toBoundedIntendedSchedule.firingCount =
      Sched.toBoundedIntendedSchedule.firingCount := by
  exact List.length_map (f := Sum.inr) (as := Sched.schedule)

def phaseParallel4_read
    {Q : Type u} {s : Nat}
    {CSp : Type v} [Fintype CSp]
    {Nread Nerase Nshift Nwrite : Network.{v, w} CSp}
    {enc : MicroCfg Q s -> State CSp}
    {Foot : MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop}
    {L : Nat} {c c' : MicroCfg Q s}
    (Sched : ConcreteGoodStepSchedule Nread enc Foot L c c') :
    ConcreteGoodStepSchedule
      (phaseParallel4 Nread Nerase Nshift Nwrite) enc Foot L c c' where
  schedule := Sched.schedule.map (fun i => Sum.inl (Sum.inl i))
  exec := phaseParallel4_exec_read Sched.exec
  length_le := by
    simpa using Sched.length_le
  footprint :=
    phaseParallel4_scheduleFootprintWithin_read Sched.footprint

def phaseParallel4_erase
    {Q : Type u} {s : Nat}
    {CSp : Type v} [Fintype CSp]
    {Nread Nerase Nshift Nwrite : Network.{v, w} CSp}
    {enc : MicroCfg Q s -> State CSp}
    {Foot : MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop}
    {L : Nat} {c c' : MicroCfg Q s}
    (Sched : ConcreteGoodStepSchedule Nerase enc Foot L c c') :
    ConcreteGoodStepSchedule
      (phaseParallel4 Nread Nerase Nshift Nwrite) enc Foot L c c' where
  schedule := Sched.schedule.map (fun i => Sum.inl (Sum.inr i))
  exec := phaseParallel4_exec_erase Sched.exec
  length_le := by
    simpa using Sched.length_le
  footprint :=
    phaseParallel4_scheduleFootprintWithin_erase Sched.footprint

def phaseParallel4_shift
    {Q : Type u} {s : Nat}
    {CSp : Type v} [Fintype CSp]
    {Nread Nerase Nshift Nwrite : Network.{v, w} CSp}
    {enc : MicroCfg Q s -> State CSp}
    {Foot : MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop}
    {L : Nat} {c c' : MicroCfg Q s}
    (Sched : ConcreteGoodStepSchedule Nshift enc Foot L c c') :
    ConcreteGoodStepSchedule
      (phaseParallel4 Nread Nerase Nshift Nwrite) enc Foot L c c' where
  schedule := Sched.schedule.map (fun i => Sum.inr (Sum.inl i))
  exec := phaseParallel4_exec_shift Sched.exec
  length_le := by
    simpa using Sched.length_le
  footprint :=
    phaseParallel4_scheduleFootprintWithin_shift Sched.footprint

def phaseParallel4_write
    {Q : Type u} {s : Nat}
    {CSp : Type v} [Fintype CSp]
    {Nread Nerase Nshift Nwrite : Network.{v, w} CSp}
    {enc : MicroCfg Q s -> State CSp}
    {Foot : MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop}
    {L : Nat} {c c' : MicroCfg Q s}
    (Sched : ConcreteGoodStepSchedule Nwrite enc Foot L c c') :
    ConcreteGoodStepSchedule
      (phaseParallel4 Nread Nerase Nshift Nwrite) enc Foot L c c' where
  schedule := Sched.schedule.map (fun i => Sum.inr (Sum.inr i))
  exec := phaseParallel4_exec_write Sched.exec
  length_le := by
    simpa using Sched.length_le
  footprint :=
    phaseParallel4_scheduleFootprintWithin_write Sched.footprint

@[simp]
theorem phaseParallel4_read_schedule
    {Q : Type u} {s : Nat}
    {CSp : Type v} [Fintype CSp]
    {Nread Nerase Nshift Nwrite : Network.{v, w} CSp}
    {enc : MicroCfg Q s -> State CSp}
    {Foot : MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop}
    {L : Nat} {c c' : MicroCfg Q s}
    (Sched : ConcreteGoodStepSchedule Nread enc Foot L c c') :
    (Sched.phaseParallel4_read
      (Nerase := Nerase) (Nshift := Nshift) (Nwrite := Nwrite)).schedule =
        Sched.schedule.map (fun i => Sum.inl (Sum.inl i)) := by
  rfl

@[simp]
theorem phaseParallel4_erase_schedule
    {Q : Type u} {s : Nat}
    {CSp : Type v} [Fintype CSp]
    {Nread Nerase Nshift Nwrite : Network.{v, w} CSp}
    {enc : MicroCfg Q s -> State CSp}
    {Foot : MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop}
    {L : Nat} {c c' : MicroCfg Q s}
    (Sched : ConcreteGoodStepSchedule Nerase enc Foot L c c') :
    (Sched.phaseParallel4_erase
      (Nread := Nread) (Nshift := Nshift) (Nwrite := Nwrite)).schedule =
        Sched.schedule.map (fun i => Sum.inl (Sum.inr i)) := by
  rfl

@[simp]
theorem phaseParallel4_shift_schedule
    {Q : Type u} {s : Nat}
    {CSp : Type v} [Fintype CSp]
    {Nread Nerase Nshift Nwrite : Network.{v, w} CSp}
    {enc : MicroCfg Q s -> State CSp}
    {Foot : MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop}
    {L : Nat} {c c' : MicroCfg Q s}
    (Sched : ConcreteGoodStepSchedule Nshift enc Foot L c c') :
    (Sched.phaseParallel4_shift
      (Nread := Nread) (Nerase := Nerase) (Nwrite := Nwrite)).schedule =
        Sched.schedule.map (fun i => Sum.inr (Sum.inl i)) := by
  rfl

@[simp]
theorem phaseParallel4_write_schedule
    {Q : Type u} {s : Nat}
    {CSp : Type v} [Fintype CSp]
    {Nread Nerase Nshift Nwrite : Network.{v, w} CSp}
    {enc : MicroCfg Q s -> State CSp}
    {Foot : MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop}
    {L : Nat} {c c' : MicroCfg Q s}
    (Sched : ConcreteGoodStepSchedule Nwrite enc Foot L c c') :
    (Sched.phaseParallel4_write
      (Nread := Nread) (Nerase := Nerase) (Nshift := Nshift)).schedule =
        Sched.schedule.map (fun i => Sum.inr (Sum.inr i)) := by
  rfl

@[simp]
theorem phaseParallel4_read_firingCount
    {Q : Type u} {s : Nat}
    {CSp : Type v} [Fintype CSp]
    {Nread Nerase Nshift Nwrite : Network.{v, w} CSp}
    {enc : MicroCfg Q s -> State CSp}
    {Foot : MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop}
    {L : Nat} {c c' : MicroCfg Q s}
    (Sched : ConcreteGoodStepSchedule Nread enc Foot L c c') :
    Network.BoundedIntendedSchedule.firingCount
        (ConcreteGoodStepSchedule.toBoundedIntendedSchedule
          (Sched.phaseParallel4_read
            (Nerase := Nerase) (Nshift := Nshift) (Nwrite := Nwrite))) =
      Sched.toBoundedIntendedSchedule.firingCount := by
  exact List.length_map
    (f := fun i => Sum.inl (Sum.inl i)) (as := Sched.schedule)

@[simp]
theorem phaseParallel4_erase_firingCount
    {Q : Type u} {s : Nat}
    {CSp : Type v} [Fintype CSp]
    {Nread Nerase Nshift Nwrite : Network.{v, w} CSp}
    {enc : MicroCfg Q s -> State CSp}
    {Foot : MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop}
    {L : Nat} {c c' : MicroCfg Q s}
    (Sched : ConcreteGoodStepSchedule Nerase enc Foot L c c') :
    Network.BoundedIntendedSchedule.firingCount
        (ConcreteGoodStepSchedule.toBoundedIntendedSchedule
          (Sched.phaseParallel4_erase
            (Nread := Nread) (Nshift := Nshift) (Nwrite := Nwrite))) =
      Sched.toBoundedIntendedSchedule.firingCount := by
  exact List.length_map
    (f := fun i => Sum.inl (Sum.inr i)) (as := Sched.schedule)

@[simp]
theorem phaseParallel4_shift_firingCount
    {Q : Type u} {s : Nat}
    {CSp : Type v} [Fintype CSp]
    {Nread Nerase Nshift Nwrite : Network.{v, w} CSp}
    {enc : MicroCfg Q s -> State CSp}
    {Foot : MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop}
    {L : Nat} {c c' : MicroCfg Q s}
    (Sched : ConcreteGoodStepSchedule Nshift enc Foot L c c') :
    Network.BoundedIntendedSchedule.firingCount
        (ConcreteGoodStepSchedule.toBoundedIntendedSchedule
          (Sched.phaseParallel4_shift
            (Nread := Nread) (Nerase := Nerase) (Nwrite := Nwrite))) =
      Sched.toBoundedIntendedSchedule.firingCount := by
  exact List.length_map
    (f := fun i => Sum.inr (Sum.inl i)) (as := Sched.schedule)

@[simp]
theorem phaseParallel4_write_firingCount
    {Q : Type u} {s : Nat}
    {CSp : Type v} [Fintype CSp]
    {Nread Nerase Nshift Nwrite : Network.{v, w} CSp}
    {enc : MicroCfg Q s -> State CSp}
    {Foot : MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop}
    {L : Nat} {c c' : MicroCfg Q s}
    (Sched : ConcreteGoodStepSchedule Nwrite enc Foot L c c') :
    Network.BoundedIntendedSchedule.firingCount
        (ConcreteGoodStepSchedule.toBoundedIntendedSchedule
          (Sched.phaseParallel4_write
            (Nread := Nread) (Nerase := Nerase) (Nshift := Nshift))) =
      Sched.toBoundedIntendedSchedule.firingCount := by
  exact List.length_map
    (f := fun i => Sum.inr (Sum.inr i)) (as := Sched.schedule)

def monoLength
    {Q : Type u} {s : Nat}
    {CSp : Type v} [Fintype CSp]
    {N : Network.{v, w} CSp}
    {enc : MicroCfg Q s -> State CSp}
    {Foot : MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop}
    {L L' : Nat} {c c' : MicroCfg Q s}
    (Sched : ConcreteGoodStepSchedule N enc Foot L c c')
    (hL : L <= L') :
    ConcreteGoodStepSchedule N enc Foot L' c c' where
  schedule := Sched.schedule
  exec := Sched.exec
  length_le := le_trans Sched.length_le hL
  footprint := Sched.footprint

@[simp]
theorem monoLength_schedule
    {Q : Type u} {s : Nat}
    {CSp : Type v} [Fintype CSp]
    {N : Network.{v, w} CSp}
    {enc : MicroCfg Q s -> State CSp}
    {Foot : MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop}
    {L L' : Nat} {c c' : MicroCfg Q s}
    (Sched : ConcreteGoodStepSchedule N enc Foot L c c')
    (hL : L <= L') :
    (Sched.monoLength hL).schedule = Sched.schedule := by
  rfl

@[simp]
theorem monoLength_toIntendedSchedule
    {Q : Type u} {s : Nat}
    {CSp : Type v} [Fintype CSp]
    {N : Network.{v, w} CSp}
    {enc : MicroCfg Q s -> State CSp}
    {Foot : MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop}
    {L L' : Nat} {c c' : MicroCfg Q s}
    (Sched : ConcreteGoodStepSchedule N enc Foot L c c')
    (hL : L <= L') :
    (Sched.monoLength hL).toIntendedSchedule =
      Sched.toIntendedSchedule := by
  rfl

@[simp]
theorem monoLength_toBoundedIntendedSchedule
    {Q : Type u} {s : Nat}
    {CSp : Type v} [Fintype CSp]
    {N : Network.{v, w} CSp}
    {enc : MicroCfg Q s -> State CSp}
    {Foot : MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop}
    {L L' : Nat} {c c' : MicroCfg Q s}
    (Sched : ConcreteGoodStepSchedule N enc Foot L c c')
    (hL : L <= L') :
    (Sched.monoLength hL).toBoundedIntendedSchedule =
      Sched.toBoundedIntendedSchedule.weakenBound hL := by
  rfl

def weakenBound
    {Q : Type u} {s : Nat}
    {CSp : Type v} [Fintype CSp]
    {N : Network.{v, w} CSp}
    {enc : MicroCfg Q s -> State CSp}
    {Foot : MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop}
    {L L' : Nat} {c c' : MicroCfg Q s}
    (Sched : ConcreteGoodStepSchedule N enc Foot L c c')
    (hL : L <= L') :
    ConcreteGoodStepSchedule N enc Foot L' c c' :=
  Sched.monoLength hL

@[simp]
theorem weakenBound_schedule
    {Q : Type u} {s : Nat}
    {CSp : Type v} [Fintype CSp]
    {N : Network.{v, w} CSp}
    {enc : MicroCfg Q s -> State CSp}
    {Foot : MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop}
    {L L' : Nat} {c c' : MicroCfg Q s}
    (Sched : ConcreteGoodStepSchedule N enc Foot L c c')
    (hL : L <= L') :
    (Sched.weakenBound hL).schedule = Sched.schedule := by
  rfl

@[simp]
theorem weakenBound_toIntendedSchedule
    {Q : Type u} {s : Nat}
    {CSp : Type v} [Fintype CSp]
    {N : Network.{v, w} CSp}
    {enc : MicroCfg Q s -> State CSp}
    {Foot : MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop}
    {L L' : Nat} {c c' : MicroCfg Q s}
    (Sched : ConcreteGoodStepSchedule N enc Foot L c c')
    (hL : L <= L') :
    (Sched.weakenBound hL).toIntendedSchedule =
      Sched.toIntendedSchedule := by
  rfl

@[simp]
theorem weakenBound_toBoundedIntendedSchedule
    {Q : Type u} {s : Nat}
    {CSp : Type v} [Fintype CSp]
    {N : Network.{v, w} CSp}
    {enc : MicroCfg Q s -> State CSp}
    {Foot : MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop}
    {L L' : Nat} {c c' : MicroCfg Q s}
    (Sched : ConcreteGoodStepSchedule N enc Foot L c c')
    (hL : L <= L') :
    (Sched.weakenBound hL).toBoundedIntendedSchedule =
      Sched.toBoundedIntendedSchedule.weakenBound hL := by
  rfl

def monoFootprint
    {Q : Type u} {s : Nat}
    {CSp : Type v} [Fintype CSp]
    {N : Network.{v, w} CSp}
    {enc : MicroCfg Q s -> State CSp}
    {Foot Foot' : MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop}
    {L : Nat} {c c' : MicroCfg Q s}
    (Sched : ConcreteGoodStepSchedule N enc Foot L c c')
    (hFoot : forall sp, Foot c c' sp -> Foot' c c' sp) :
    ConcreteGoodStepSchedule N enc Foot' L c c' where
  schedule := Sched.schedule
  exec := Sched.exec
  length_le := Sched.length_le
  footprint :=
    Network.scheduleFootprintWithin_mono
      Sched.footprint hFoot

@[simp]
theorem monoFootprint_schedule
    {Q : Type u} {s : Nat}
    {CSp : Type v} [Fintype CSp]
    {N : Network.{v, w} CSp}
    {enc : MicroCfg Q s -> State CSp}
    {Foot Foot' : MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop}
    {L : Nat} {c c' : MicroCfg Q s}
    (Sched : ConcreteGoodStepSchedule N enc Foot L c c')
    (hFoot : forall sp, Foot c c' sp -> Foot' c c' sp) :
    (Sched.monoFootprint hFoot).schedule = Sched.schedule := by
  rfl

@[simp]
theorem monoFootprint_toIntendedSchedule
    {Q : Type u} {s : Nat}
    {CSp : Type v} [Fintype CSp]
    {N : Network.{v, w} CSp}
    {enc : MicroCfg Q s -> State CSp}
    {Foot Foot' : MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop}
    {L : Nat} {c c' : MicroCfg Q s}
    (Sched : ConcreteGoodStepSchedule N enc Foot L c c')
    (hFoot : forall sp, Foot c c' sp -> Foot' c c' sp) :
    (Sched.monoFootprint hFoot).toIntendedSchedule =
      Sched.toIntendedSchedule := by
  rfl

@[simp]
theorem monoFootprint_toBoundedIntendedSchedule
    {Q : Type u} {s : Nat}
    {CSp : Type v} [Fintype CSp]
    {N : Network.{v, w} CSp}
    {enc : MicroCfg Q s -> State CSp}
    {Foot Foot' : MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop}
    {L : Nat} {c c' : MicroCfg Q s}
    (Sched : ConcreteGoodStepSchedule N enc Foot L c c')
    (hFoot : forall sp, Foot c c' sp -> Foot' c c' sp) :
    (Sched.monoFootprint hFoot).toBoundedIntendedSchedule =
      Sched.toBoundedIntendedSchedule := by
  rfl

def mono
    {Q : Type u} {s : Nat}
    {CSp : Type v} [Fintype CSp]
    {N : Network.{v, w} CSp}
    {enc : MicroCfg Q s -> State CSp}
    {Foot Foot' : MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop}
    {L L' : Nat} {c c' : MicroCfg Q s}
    (Sched : ConcreteGoodStepSchedule N enc Foot L c c')
    (hL : L <= L')
    (hFoot : forall sp, Foot c c' sp -> Foot' c c' sp) :
    ConcreteGoodStepSchedule N enc Foot' L' c c' :=
  (Sched.monoLength hL).monoFootprint hFoot

@[simp]
theorem mono_schedule
    {Q : Type u} {s : Nat}
    {CSp : Type v} [Fintype CSp]
    {N : Network.{v, w} CSp}
    {enc : MicroCfg Q s -> State CSp}
    {Foot Foot' : MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop}
    {L L' : Nat} {c c' : MicroCfg Q s}
    (Sched : ConcreteGoodStepSchedule N enc Foot L c c')
    (hL : L <= L')
    (hFoot : forall sp, Foot c c' sp -> Foot' c c' sp) :
    (Sched.mono hL hFoot).schedule = Sched.schedule := by
  rfl

@[simp]
theorem mono_toIntendedSchedule
    {Q : Type u} {s : Nat}
    {CSp : Type v} [Fintype CSp]
    {N : Network.{v, w} CSp}
    {enc : MicroCfg Q s -> State CSp}
    {Foot Foot' : MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop}
    {L L' : Nat} {c c' : MicroCfg Q s}
    (Sched : ConcreteGoodStepSchedule N enc Foot L c c')
    (hL : L <= L')
    (hFoot : forall sp, Foot c c' sp -> Foot' c c' sp) :
    (Sched.mono hL hFoot).toIntendedSchedule =
      Sched.toIntendedSchedule := by
  rfl

@[simp]
theorem mono_toBoundedIntendedSchedule
    {Q : Type u} {s : Nat}
    {CSp : Type v} [Fintype CSp]
    {N : Network.{v, w} CSp}
    {enc : MicroCfg Q s -> State CSp}
    {Foot Foot' : MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop}
    {L L' : Nat} {c c' : MicroCfg Q s}
    (Sched : ConcreteGoodStepSchedule N enc Foot L c c')
    (hL : L <= L')
    (hFoot : forall sp, Foot c c' sp -> Foot' c c' sp) :
    (Sched.mono hL hFoot).toBoundedIntendedSchedule =
      Sched.toBoundedIntendedSchedule.weakenBound hL := by
  rfl

def weakenFootprint
    {Q : Type u} {s : Nat}
    {CSp : Type v} [Fintype CSp]
    {N : Network.{v, w} CSp}
    {enc : MicroCfg Q s -> State CSp}
    {Foot Foot' : MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop}
    {L : Nat} {c c' : MicroCfg Q s}
    (Sched : ConcreteGoodStepSchedule N enc Foot L c c')
    (hFoot : forall sp, Foot c c' sp -> Foot' c c' sp) :
    ConcreteGoodStepSchedule N enc Foot' L c c' :=
  Sched.monoFootprint hFoot

@[simp]
theorem weakenFootprint_schedule
    {Q : Type u} {s : Nat}
    {CSp : Type v} [Fintype CSp]
    {N : Network.{v, w} CSp}
    {enc : MicroCfg Q s -> State CSp}
    {Foot Foot' : MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop}
    {L : Nat} {c c' : MicroCfg Q s}
    (Sched : ConcreteGoodStepSchedule N enc Foot L c c')
    (hFoot : forall sp, Foot c c' sp -> Foot' c c' sp) :
    (Sched.weakenFootprint hFoot).schedule = Sched.schedule := by
  rfl

@[simp]
theorem weakenFootprint_toIntendedSchedule
    {Q : Type u} {s : Nat}
    {CSp : Type v} [Fintype CSp]
    {N : Network.{v, w} CSp}
    {enc : MicroCfg Q s -> State CSp}
    {Foot Foot' : MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop}
    {L : Nat} {c c' : MicroCfg Q s}
    (Sched : ConcreteGoodStepSchedule N enc Foot L c c')
    (hFoot : forall sp, Foot c c' sp -> Foot' c c' sp) :
    (Sched.weakenFootprint hFoot).toIntendedSchedule =
      Sched.toIntendedSchedule := by
  rfl

@[simp]
theorem weakenFootprint_toBoundedIntendedSchedule
    {Q : Type u} {s : Nat}
    {CSp : Type v} [Fintype CSp]
    {N : Network.{v, w} CSp}
    {enc : MicroCfg Q s -> State CSp}
    {Foot Foot' : MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop}
    {L : Nat} {c c' : MicroCfg Q s}
    (Sched : ConcreteGoodStepSchedule N enc Foot L c c')
    (hFoot : forall sp, Foot c c' sp -> Foot' c c' sp) :
    (Sched.weakenFootprint hFoot).toBoundedIntendedSchedule =
      Sched.toBoundedIntendedSchedule := by
  rfl

def monoConcreteLocalFootprint
    {Q : Type u} {s : Nat}
    {CSp : Type v} [Fintype CSp]
    {N : Network.{v, w} CSp}
    {enc : MicroCfg Q s -> State CSp}
    {ideal : FourPhaseSpecies Q -> CSp}
    {auxFootprint : MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop}
    {L : Nat} {c c' : MicroCfg Q s}
    (Sched :
      ConcreteGoodStepSchedule N enc
        (ConcreteLocalFootprint ideal auxFootprint) L c c')
    (P : CSp -> Prop)
    (hIdeal :
      forall species : FourPhaseSpecies Q,
        FourPhaseSpecies.IsLocalMacroFootprint
          (FourPhaseSpecies.ctrlOf c.state)
          (FourPhaseSpecies.ctrlOf c'.state)
          species ->
        P (ideal species))
    (hAux :
      forall sp, auxFootprint c c' sp -> P sp) :
    ConcreteGoodStepSchedule N enc (fun _ _ sp => P sp) L c c' :=
  Sched.monoFootprint
    (concreteLocalFootprint_mono hIdeal hAux)

def monoConcreteLocalFootprint_of_members
    {Q : Type u} {s : Nat}
    {CSp : Type v} [Fintype CSp]
    {N : Network.{v, w} CSp}
    {enc : MicroCfg Q s -> State CSp}
    {ideal : FourPhaseSpecies Q -> CSp}
    {auxFootprint : MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop}
    {L : Nat} {c c' : MicroCfg Q s}
    (Sched :
      ConcreteGoodStepSchedule N enc
        (ConcreteLocalFootprint ideal auxFootprint) L c c')
    (P : CSp -> Prop)
    (hold : P (ideal (FourPhaseSpecies.ctrlOf c.state)))
    (hnew : P (ideal (FourPhaseSpecies.ctrlOf c'.state)))
    (htape : P (ideal FourPhaseSpecies.tape))
    (htapeBar : P (ideal FourPhaseSpecies.tapeBar))
    (hAux :
      forall sp, auxFootprint c c' sp -> P sp) :
    ConcreteGoodStepSchedule N enc (fun _ _ sp => P sp) L c c' :=
  Sched.monoConcreteLocalFootprint P
    (by
      intro species hLocal
      exact FourPhaseSpecies.localMacroFootprint_mono
        (oldCtrl := FourPhaseSpecies.ctrlOf c.state)
        (newCtrl := FourPhaseSpecies.ctrlOf c'.state)
        (P := fun species => P (ideal species))
        hold hnew htape htapeBar hLocal)
    hAux

def appendWithFootprint
    {Q : Type u} {s : Nat}
    {CSp : Type v} [Fintype CSp]
    {N : Network.{v, w} CSp}
    {enc : MicroCfg Q s -> State CSp}
    {Foot01 Foot12 Foot02 :
      MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop}
    {L01 L12 : Nat} {c0 c1 c2 : MicroCfg Q s}
    (Sched01 :
      ConcreteGoodStepSchedule N enc Foot01 L01 c0 c1)
    (Sched12 :
      ConcreteGoodStepSchedule N enc Foot12 L12 c1 c2)
    (hFoot01 :
      forall sp, Foot01 c0 c1 sp -> Foot02 c0 c2 sp)
    (hFoot12 :
      forall sp, Foot12 c1 c2 sp -> Foot02 c0 c2 sp) :
    ConcreteGoodStepSchedule N enc Foot02 (L01 + L12) c0 c2 where
  schedule := Sched01.schedule ++ Sched12.schedule
  exec := ExecOf.append Sched01.exec Sched12.exec
  length_le := by
    simpa [List.length_append] using
      Nat.add_le_add Sched01.length_le Sched12.length_le
  footprint :=
    Network.scheduleFootprintWithin_append
      (Network.scheduleFootprintWithin_mono
        Sched01.footprint hFoot01)
      (Network.scheduleFootprintWithin_mono
        Sched12.footprint hFoot12)

@[simp]
theorem appendWithFootprint_schedule
    {Q : Type u} {s : Nat}
    {CSp : Type v} [Fintype CSp]
    {N : Network.{v, w} CSp}
    {enc : MicroCfg Q s -> State CSp}
    {Foot01 Foot12 Foot02 :
      MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop}
    {L01 L12 : Nat} {c0 c1 c2 : MicroCfg Q s}
    (Sched01 :
      ConcreteGoodStepSchedule N enc Foot01 L01 c0 c1)
    (Sched12 :
      ConcreteGoodStepSchedule N enc Foot12 L12 c1 c2)
    (hFoot01 :
      forall sp, Foot01 c0 c1 sp -> Foot02 c0 c2 sp)
    (hFoot12 :
      forall sp, Foot12 c1 c2 sp -> Foot02 c0 c2 sp) :
    (appendWithFootprint
      Sched01 Sched12 hFoot01 hFoot12).schedule =
      Sched01.schedule ++ Sched12.schedule := by
  rfl

@[simp]
theorem appendWithFootprint_toIntendedSchedule
    {Q : Type u} {s : Nat}
    {CSp : Type v} [Fintype CSp]
    {N : Network.{v, w} CSp}
    {enc : MicroCfg Q s -> State CSp}
    {Foot01 Foot12 Foot02 :
      MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop}
    {L01 L12 : Nat} {c0 c1 c2 : MicroCfg Q s}
    (Sched01 :
      ConcreteGoodStepSchedule N enc Foot01 L01 c0 c1)
    (Sched12 :
      ConcreteGoodStepSchedule N enc Foot12 L12 c1 c2)
    (hFoot01 :
      forall sp, Foot01 c0 c1 sp -> Foot02 c0 c2 sp)
    (hFoot12 :
      forall sp, Foot12 c1 c2 sp -> Foot02 c0 c2 sp) :
    (appendWithFootprint
      Sched01 Sched12 hFoot01 hFoot12).toIntendedSchedule =
      Sched01.toIntendedSchedule.append Sched12.toIntendedSchedule := by
  rfl

@[simp]
theorem appendWithFootprint_toBoundedIntendedSchedule
    {Q : Type u} {s : Nat}
    {CSp : Type v} [Fintype CSp]
    {N : Network.{v, w} CSp}
    {enc : MicroCfg Q s -> State CSp}
    {Foot01 Foot12 Foot02 :
      MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop}
    {L01 L12 : Nat} {c0 c1 c2 : MicroCfg Q s}
    (Sched01 :
      ConcreteGoodStepSchedule N enc Foot01 L01 c0 c1)
    (Sched12 :
      ConcreteGoodStepSchedule N enc Foot12 L12 c1 c2)
    (hFoot01 :
      forall sp, Foot01 c0 c1 sp -> Foot02 c0 c2 sp)
    (hFoot12 :
      forall sp, Foot12 c1 c2 sp -> Foot02 c0 c2 sp) :
    (appendWithFootprint
      Sched01 Sched12 hFoot01 hFoot12).toBoundedIntendedSchedule =
      Sched01.toBoundedIntendedSchedule.append
        Sched12.toBoundedIntendedSchedule := by
  rfl

@[simp]
theorem appendWithFootprint_toIntendedSchedule_firingCount
    {Q : Type u} {s : Nat}
    {CSp : Type v} [Fintype CSp]
    {N : Network.{v, w} CSp}
    {enc : MicroCfg Q s -> State CSp}
    {Foot01 Foot12 Foot02 :
      MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop}
    {L01 L12 : Nat} {c0 c1 c2 : MicroCfg Q s}
    (Sched01 :
      ConcreteGoodStepSchedule N enc Foot01 L01 c0 c1)
    (Sched12 :
      ConcreteGoodStepSchedule N enc Foot12 L12 c1 c2)
    (hFoot01 :
      forall sp, Foot01 c0 c1 sp -> Foot02 c0 c2 sp)
    (hFoot12 :
      forall sp, Foot12 c1 c2 sp -> Foot02 c0 c2 sp) :
    (appendWithFootprint
      Sched01 Sched12 hFoot01 hFoot12).toIntendedSchedule.firingCount =
      Sched01.toIntendedSchedule.firingCount +
        Sched12.toIntendedSchedule.firingCount := by
  simp

@[simp]
theorem appendWithFootprint_toBoundedIntendedSchedule_firingCount
    {Q : Type u} {s : Nat}
    {CSp : Type v} [Fintype CSp]
    {N : Network.{v, w} CSp}
    {enc : MicroCfg Q s -> State CSp}
    {Foot01 Foot12 Foot02 :
      MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop}
    {L01 L12 : Nat} {c0 c1 c2 : MicroCfg Q s}
    (Sched01 :
      ConcreteGoodStepSchedule N enc Foot01 L01 c0 c1)
    (Sched12 :
      ConcreteGoodStepSchedule N enc Foot12 L12 c1 c2)
    (hFoot01 :
      forall sp, Foot01 c0 c1 sp -> Foot02 c0 c2 sp)
    (hFoot12 :
      forall sp, Foot12 c1 c2 sp -> Foot02 c0 c2 sp) :
    (appendWithFootprint
      Sched01 Sched12 hFoot01 hFoot12).toBoundedIntendedSchedule.firingCount =
      Sched01.toBoundedIntendedSchedule.firingCount +
        Sched12.toBoundedIntendedSchedule.firingCount := by
  simp

def appendUnion
    {Q : Type u} {s : Nat}
    {CSp : Type v} [Fintype CSp]
    {N : Network.{v, w} CSp}
    {enc : MicroCfg Q s -> State CSp}
    {Foot01 Foot12 :
      MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop}
    {L01 L12 : Nat} {c0 c1 c2 : MicroCfg Q s}
    (Sched01 :
      ConcreteGoodStepSchedule N enc Foot01 L01 c0 c1)
    (Sched12 :
      ConcreteGoodStepSchedule N enc Foot12 L12 c1 c2) :
    ConcreteGoodStepSchedule N enc
      (fun _ _ sp => Foot01 c0 c1 sp \/ Foot12 c1 c2 sp)
      (L01 + L12) c0 c2 :=
  appendWithFootprint
    Sched01 Sched12
    (fun _ h => Or.inl h)
    (fun _ h => Or.inr h)

@[simp]
theorem appendUnion_schedule
    {Q : Type u} {s : Nat}
    {CSp : Type v} [Fintype CSp]
    {N : Network.{v, w} CSp}
    {enc : MicroCfg Q s -> State CSp}
    {Foot01 Foot12 :
      MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop}
    {L01 L12 : Nat} {c0 c1 c2 : MicroCfg Q s}
    (Sched01 :
      ConcreteGoodStepSchedule N enc Foot01 L01 c0 c1)
    (Sched12 :
      ConcreteGoodStepSchedule N enc Foot12 L12 c1 c2) :
    (appendUnion Sched01 Sched12).schedule =
      Sched01.schedule ++ Sched12.schedule := by
  rfl

@[simp]
theorem appendUnion_toIntendedSchedule
    {Q : Type u} {s : Nat}
    {CSp : Type v} [Fintype CSp]
    {N : Network.{v, w} CSp}
    {enc : MicroCfg Q s -> State CSp}
    {Foot01 Foot12 :
      MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop}
    {L01 L12 : Nat} {c0 c1 c2 : MicroCfg Q s}
    (Sched01 :
      ConcreteGoodStepSchedule N enc Foot01 L01 c0 c1)
    (Sched12 :
      ConcreteGoodStepSchedule N enc Foot12 L12 c1 c2) :
    (appendUnion Sched01 Sched12).toIntendedSchedule =
      Sched01.toIntendedSchedule.append Sched12.toIntendedSchedule := by
  rfl

@[simp]
theorem appendUnion_toBoundedIntendedSchedule
    {Q : Type u} {s : Nat}
    {CSp : Type v} [Fintype CSp]
    {N : Network.{v, w} CSp}
    {enc : MicroCfg Q s -> State CSp}
    {Foot01 Foot12 :
      MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop}
    {L01 L12 : Nat} {c0 c1 c2 : MicroCfg Q s}
    (Sched01 :
      ConcreteGoodStepSchedule N enc Foot01 L01 c0 c1)
    (Sched12 :
      ConcreteGoodStepSchedule N enc Foot12 L12 c1 c2) :
    (appendUnion Sched01 Sched12).toBoundedIntendedSchedule =
      Sched01.toBoundedIntendedSchedule.append
        Sched12.toBoundedIntendedSchedule := by
  rfl

@[simp]
theorem appendUnion_toIntendedSchedule_firingCount
    {Q : Type u} {s : Nat}
    {CSp : Type v} [Fintype CSp]
    {N : Network.{v, w} CSp}
    {enc : MicroCfg Q s -> State CSp}
    {Foot01 Foot12 :
      MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop}
    {L01 L12 : Nat} {c0 c1 c2 : MicroCfg Q s}
    (Sched01 :
      ConcreteGoodStepSchedule N enc Foot01 L01 c0 c1)
    (Sched12 :
      ConcreteGoodStepSchedule N enc Foot12 L12 c1 c2) :
    (appendUnion Sched01 Sched12).toIntendedSchedule.firingCount =
      Sched01.toIntendedSchedule.firingCount +
        Sched12.toIntendedSchedule.firingCount := by
  simp

@[simp]
theorem appendUnion_toBoundedIntendedSchedule_firingCount
    {Q : Type u} {s : Nat}
    {CSp : Type v} [Fintype CSp]
    {N : Network.{v, w} CSp}
    {enc : MicroCfg Q s -> State CSp}
    {Foot01 Foot12 :
      MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop}
    {L01 L12 : Nat} {c0 c1 c2 : MicroCfg Q s}
    (Sched01 :
      ConcreteGoodStepSchedule N enc Foot01 L01 c0 c1)
    (Sched12 :
      ConcreteGoodStepSchedule N enc Foot12 L12 c1 c2) :
    (appendUnion Sched01 Sched12).toBoundedIntendedSchedule.firingCount =
      Sched01.toBoundedIntendedSchedule.firingCount +
        Sched12.toBoundedIntendedSchedule.firingCount := by
  simp

def append
    {Q : Type u} {s : Nat}
    {CSp : Type v} [Fintype CSp]
    {N : Network.{v, w} CSp}
    {enc : MicroCfg Q s -> State CSp}
    {Foot : MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop}
    {L01 L12 : Nat} {c0 c1 c2 : MicroCfg Q s}
    (Sched01 : ConcreteGoodStepSchedule N enc Foot L01 c0 c1)
    (Sched12 : ConcreteGoodStepSchedule N enc Foot L12 c1 c2)
    (hFoot01 : forall sp, Foot c0 c1 sp -> Foot c0 c2 sp)
    (hFoot12 : forall sp, Foot c1 c2 sp -> Foot c0 c2 sp) :
    ConcreteGoodStepSchedule N enc Foot (L01 + L12) c0 c2 :=
  appendWithFootprint Sched01 Sched12 hFoot01 hFoot12

@[simp]
theorem append_schedule
    {Q : Type u} {s : Nat}
    {CSp : Type v} [Fintype CSp]
    {N : Network.{v, w} CSp}
    {enc : MicroCfg Q s -> State CSp}
    {Foot : MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop}
    {L01 L12 : Nat} {c0 c1 c2 : MicroCfg Q s}
    (Sched01 : ConcreteGoodStepSchedule N enc Foot L01 c0 c1)
    (Sched12 : ConcreteGoodStepSchedule N enc Foot L12 c1 c2)
    (hFoot01 : forall sp, Foot c0 c1 sp -> Foot c0 c2 sp)
    (hFoot12 : forall sp, Foot c1 c2 sp -> Foot c0 c2 sp) :
    (Sched01.append Sched12 hFoot01 hFoot12).schedule =
      Sched01.schedule ++ Sched12.schedule := by
  rfl

@[simp]
theorem append_toIntendedSchedule
    {Q : Type u} {s : Nat}
    {CSp : Type v} [Fintype CSp]
    {N : Network.{v, w} CSp}
    {enc : MicroCfg Q s -> State CSp}
    {Foot : MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop}
    {L01 L12 : Nat} {c0 c1 c2 : MicroCfg Q s}
    (Sched01 : ConcreteGoodStepSchedule N enc Foot L01 c0 c1)
    (Sched12 : ConcreteGoodStepSchedule N enc Foot L12 c1 c2)
    (hFoot01 : forall sp, Foot c0 c1 sp -> Foot c0 c2 sp)
    (hFoot12 : forall sp, Foot c1 c2 sp -> Foot c0 c2 sp) :
    (Sched01.append Sched12 hFoot01 hFoot12).toIntendedSchedule =
      Sched01.toIntendedSchedule.append Sched12.toIntendedSchedule := by
  rfl

@[simp]
theorem append_toBoundedIntendedSchedule
    {Q : Type u} {s : Nat}
    {CSp : Type v} [Fintype CSp]
    {N : Network.{v, w} CSp}
    {enc : MicroCfg Q s -> State CSp}
    {Foot : MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop}
    {L01 L12 : Nat} {c0 c1 c2 : MicroCfg Q s}
    (Sched01 : ConcreteGoodStepSchedule N enc Foot L01 c0 c1)
    (Sched12 : ConcreteGoodStepSchedule N enc Foot L12 c1 c2)
    (hFoot01 : forall sp, Foot c0 c1 sp -> Foot c0 c2 sp)
    (hFoot12 : forall sp, Foot c1 c2 sp -> Foot c0 c2 sp) :
    (Sched01.append Sched12 hFoot01 hFoot12).toBoundedIntendedSchedule =
      Sched01.toBoundedIntendedSchedule.append
        Sched12.toBoundedIntendedSchedule := by
  rfl

@[simp]
theorem append_toIntendedSchedule_firingCount
    {Q : Type u} {s : Nat}
    {CSp : Type v} [Fintype CSp]
    {N : Network.{v, w} CSp}
    {enc : MicroCfg Q s -> State CSp}
    {Foot : MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop}
    {L01 L12 : Nat} {c0 c1 c2 : MicroCfg Q s}
    (Sched01 : ConcreteGoodStepSchedule N enc Foot L01 c0 c1)
    (Sched12 : ConcreteGoodStepSchedule N enc Foot L12 c1 c2)
    (hFoot01 : forall sp, Foot c0 c1 sp -> Foot c0 c2 sp)
    (hFoot12 : forall sp, Foot c1 c2 sp -> Foot c0 c2 sp) :
    (Sched01.append Sched12 hFoot01 hFoot12).toIntendedSchedule.firingCount =
      Sched01.toIntendedSchedule.firingCount +
        Sched12.toIntendedSchedule.firingCount := by
  simp

@[simp]
theorem append_toBoundedIntendedSchedule_firingCount
    {Q : Type u} {s : Nat}
    {CSp : Type v} [Fintype CSp]
    {N : Network.{v, w} CSp}
    {enc : MicroCfg Q s -> State CSp}
    {Foot : MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop}
    {L01 L12 : Nat} {c0 c1 c2 : MicroCfg Q s}
    (Sched01 : ConcreteGoodStepSchedule N enc Foot L01 c0 c1)
    (Sched12 : ConcreteGoodStepSchedule N enc Foot L12 c1 c2)
    (hFoot01 : forall sp, Foot c0 c1 sp -> Foot c0 c2 sp)
    (hFoot12 : forall sp, Foot c1 c2 sp -> Foot c0 c2 sp) :
    (Sched01.append Sched12 hFoot01 hFoot12).toBoundedIntendedSchedule.firingCount =
      Sched01.toBoundedIntendedSchedule.firingCount +
        Sched12.toBoundedIntendedSchedule.firingCount := by
  simp

theorem state_after_firesListAt
    {Q : Type u} {s : Nat}
    {CSp : Type v} [Fintype CSp]
    {N : Network.{v, w} CSp}
    {enc : MicroCfg Q s -> State CSp}
    {Foot : MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop}
    {L : Nat} {c c' : MicroCfg Q s}
    (Sched : ConcreteGoodStepSchedule N enc Foot L c c')
    {path : N.Path} {t : Nat}
    (hstate : path.state t = enc c)
    (hfires : path.FiresListAt t Sched.schedule) :
    path.state (t + Sched.schedule.length) = enc c' := by
  simpa [ConcreteGoodStepSchedule.toIntendedSchedule] using
    path.state_after_intended_of_firesListAt
      Sched.toIntendedSchedule hstate
      (by simpa using hfires)

theorem intendedWinsRaceAt_of_firesListAt_forall_not_bad
    {Q : Type u} {s : Nat}
    {CSp : Type v} [Fintype CSp]
    {N : Network.{v, w} CSp}
    {enc : MicroCfg Q s -> State CSp}
    {Foot : MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop}
    {L : Nat} {c c' : MicroCfg Q s}
    (Sched : ConcreteGoodStepSchedule N enc Foot L c c')
    {path : N.Path} {Bad : N.BadIndexSet} {t : Nat}
    (hstate : path.state t = enc c)
    (hfires : path.FiresListAt t Sched.schedule)
    (hnotBad : forall i, i ∈ Sched.schedule -> Not (Bad i)) :
    path.IntendedWinsRaceAt Bad t Sched.toIntendedSchedule := by
  exact
    Network.Path.intendedWinsRaceAt_of_firesIntendedContiguouslyAt_forall_not_bad
      (Bad := Bad)
      (I := Sched.toIntendedSchedule)
      (by
        exact ⟨hstate, by
          simpa [ConcreteGoodStepSchedule.toIntendedSchedule] using
            hfires⟩)
      (by
        intro i hi
        exact hnotBad i (by
          simpa [ConcreteGoodStepSchedule.toIntendedSchedule] using hi))

theorem boundedIntendedWinsRaceAt_of_firesListAt_forall_not_bad
    {Q : Type u} {s : Nat}
    {CSp : Type v} [Fintype CSp]
    {N : Network.{v, w} CSp}
    {enc : MicroCfg Q s -> State CSp}
    {Foot : MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop}
    {L : Nat} {c c' : MicroCfg Q s}
    (Sched : ConcreteGoodStepSchedule N enc Foot L c c')
    {path : N.Path} {Bad : N.BadIndexSet} {t : Nat}
    (hstate : path.state t = enc c)
    (hfires : path.FiresListAt t Sched.schedule)
    (hnotBad : forall i, i ∈ Sched.schedule -> Not (Bad i)) :
    path.IntendedWinsRaceAt Bad t
      Sched.toBoundedIntendedSchedule.toIntendedSchedule := by
  simpa [ConcreteGoodStepSchedule.toBoundedIntendedSchedule_toIntendedSchedule]
    using
      Sched.intendedWinsRaceAt_of_firesListAt_forall_not_bad
        hstate hfires hnotBad

theorem eqOn_after_firesListAt_of_disjoint
    {Q : Type u} {s : Nat}
    {CSp : Type v} [Fintype CSp]
    {N : Network.{v, w} CSp}
    {enc : MicroCfg Q s -> State CSp}
    {Foot : MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop}
    {L : Nat} {c c' : MicroCfg Q s}
    (Sched : ConcreteGoodStepSchedule N enc Foot L c c')
    {path : N.Path} {t : Nat}
    {Protected : CSp -> Prop}
    (hstate : path.state t = enc c)
    (hfires : path.FiresListAt t Sched.schedule)
    (hDisjoint :
      forall sp, Foot c c' sp -> Protected sp -> False) :
    State.EqOn Protected
      (path.state (t + Sched.schedule.length))
      (path.state t) := by
  intro sp hProtected
  have hEnd :
      path.state (t + Sched.schedule.length) = enc c' :=
    Sched.state_after_firesListAt hstate hfires
  have hFrame : State.EqOn Protected (enc c') (enc c) :=
    Network.Exec.eqOn_of_scheduleTouchesOnly_disjoint
      Sched.exec Sched.footprint hDisjoint
  rw [hEnd, hstate]
  exact hFrame sp hProtected

theorem zeroOn_after_firesListAt_of_disjoint
    {Q : Type u} {s : Nat}
    {CSp : Type v} [Fintype CSp]
    {N : Network.{v, w} CSp}
    {enc : MicroCfg Q s -> State CSp}
    {Foot : MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop}
    {L : Nat} {c c' : MicroCfg Q s}
    (Sched : ConcreteGoodStepSchedule N enc Foot L c c')
    {path : N.Path} {t : Nat}
    {Protected : CSp -> Prop}
    (hstate : path.state t = enc c)
    (hfires : path.FiresListAt t Sched.schedule)
    (hDisjoint :
      forall sp, Foot c c' sp -> Protected sp -> False)
    (hZero : State.ZeroOn Protected (path.state t)) :
    State.ZeroOn Protected
      (path.state (t + Sched.schedule.length)) :=
  State.zeroOn_of_eqOn
    (Sched.eqOn_after_firesListAt_of_disjoint
      hstate hfires hDisjoint)
    hZero

theorem state_after_firesIntendedContiguouslyAt
    {Q : Type u} {s : Nat}
    {CSp : Type v} [Fintype CSp]
    {N : Network.{v, w} CSp}
    {enc : MicroCfg Q s -> State CSp}
    {Foot : MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop}
    {L : Nat} {c c' : MicroCfg Q s}
    (Sched : ConcreteGoodStepSchedule N enc Foot L c c')
    {path : N.Path} {t : Nat}
    (hfire :
      path.FiresIntendedContiguouslyAt t Sched.toIntendedSchedule) :
    path.state (t + Sched.schedule.length) = enc c' := by
  simpa [ConcreteGoodStepSchedule.toIntendedSchedule] using
    path.state_after_intended_of_firesListAt
      Sched.toIntendedSchedule hfire.1 hfire.2

theorem state_after_intendedWinsRaceAt
    {Q : Type u} {s : Nat}
    {CSp : Type v} [Fintype CSp]
    {N : Network.{v, w} CSp}
    {enc : MicroCfg Q s -> State CSp}
    {Foot : MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop}
    {L : Nat} {c c' : MicroCfg Q s}
    (Sched : ConcreteGoodStepSchedule N enc Foot L c c')
    {path : N.Path} {Bad : N.BadIndexSet} {t : Nat}
    (hwin :
      path.IntendedWinsRaceAt Bad t Sched.toIntendedSchedule) :
    path.state (t + Sched.schedule.length) = enc c' := by
  simpa [ConcreteGoodStepSchedule.toIntendedSchedule] using
    path.state_after_intendedWinsRaceAt Bad Sched.toIntendedSchedule hwin

theorem applyHoareExec
    {Q : Type u} {s : Nat}
    {CSp : Type v} [Fintype CSp]
    {N : Network.{v, w} CSp}
    {enc : MicroCfg Q s -> State CSp}
    {Foot : MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop}
    {L : Nat} {c c' : MicroCfg Q s}
    {Pre : State CSp -> Prop}
    {Post : State CSp -> State CSp -> Prop}
    (Sched : ConcreteGoodStepSchedule N enc Foot L c c')
    (hHoare : N.HoareExec Sched.schedule Pre Post)
    (hPre : Pre (enc c)) :
    Post (enc c) (enc c') :=
  hHoare Sched.exec hPre

theorem boundedApplyHoareExec
    {Q : Type u} {s : Nat}
    {CSp : Type v} [Fintype CSp]
    {N : Network.{v, w} CSp}
    {enc : MicroCfg Q s -> State CSp}
    {Foot : MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop}
    {L : Nat} {c c' : MicroCfg Q s}
    {Pre : State CSp -> Prop}
    {Post : State CSp -> State CSp -> Prop}
    (Sched : ConcreteGoodStepSchedule N enc Foot L c c')
    (hHoare :
      N.HoareExec Sched.toBoundedIntendedSchedule.schedule Pre Post)
    (hPre : Pre (enc c)) :
    Post (enc c) (enc c') :=
  hHoare Sched.toBoundedIntendedSchedule.exec hPre

theorem preserves_of_schedulePreserves
    {Q : Type u} {s : Nat}
    {CSp : Type v} [Fintype CSp]
    {N : Network.{v, w} CSp}
    {enc : MicroCfg Q s -> State CSp}
    {Foot : MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop}
    {L : Nat} {c c' : MicroCfg Q s}
    (Sched : ConcreteGoodStepSchedule N enc Foot L c c')
    {P : State CSp -> Prop}
    (hPres : N.SchedulePreserves Sched.schedule P)
    (hP : P (enc c)) :
    P (enc c') :=
  Sched.toIntendedSchedule.preserves_of_schedulePreserves hPres hP

theorem boundedPreserves_of_schedulePreserves
    {Q : Type u} {s : Nat}
    {CSp : Type v} [Fintype CSp]
    {N : Network.{v, w} CSp}
    {enc : MicroCfg Q s -> State CSp}
    {Foot : MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop}
    {L : Nat} {c c' : MicroCfg Q s}
    (Sched : ConcreteGoodStepSchedule N enc Foot L c c')
    {P : State CSp -> Prop}
    (hPres :
      N.SchedulePreserves Sched.toBoundedIntendedSchedule.schedule P)
    (hP : P (enc c)) :
    P (enc c') :=
  Sched.toBoundedIntendedSchedule.preserves_of_schedulePreserves hPres hP

theorem hoareExec_exact
    {Q : Type u} {s : Nat}
    {CSp : Type v} [Fintype CSp]
    {N : Network.{v, w} CSp}
    {enc : MicroCfg Q s -> State CSp}
    {Foot : MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop}
    {L : Nat} {c c' : MicroCfg Q s}
    (Sched : ConcreteGoodStepSchedule N enc Foot L c c') :
    N.HoareExec Sched.schedule
      (fun z => z = enc c)
      (fun _ z' => z' = enc c') :=
  Sched.toIntendedSchedule.hoareExec_exact

theorem boundedHoareExec_exact
    {Q : Type u} {s : Nat}
    {CSp : Type v} [Fintype CSp]
    {N : Network.{v, w} CSp}
    {enc : MicroCfg Q s -> State CSp}
    {Foot : MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop}
    {L : Nat} {c c' : MicroCfg Q s}
    (Sched : ConcreteGoodStepSchedule N enc Foot L c c') :
    N.HoareExec Sched.toBoundedIntendedSchedule.schedule
      (fun z => z = enc c)
      (fun _ z' => z' = enc c') :=
  Sched.toBoundedIntendedSchedule.hoareExec_exact

theorem execFootprintWithin
    {Q : Type u} {s : Nat}
    {CSp : Type v} [Fintype CSp]
    {N : Network.{v, w} CSp}
    {enc : MicroCfg Q s -> State CSp}
    {Foot : MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop}
    {L : Nat} {c c' : MicroCfg Q s}
    (Sched : ConcreteGoodStepSchedule N enc Foot L c c') :
    N.ExecFootprintWithin (Foot c c') (enc c) (enc c') :=
  Network.ExecFootprintWithin.of_exec_scheduleFootprintWithin
    Sched.exec Sched.footprint

theorem scheduleUntouches_of_disjoint
    {Q : Type u} {s : Nat}
    {CSp : Type v} [Fintype CSp]
    {N : Network.{v, w} CSp}
    {enc : MicroCfg Q s -> State CSp}
    {Foot : MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop}
    {L : Nat} {c c' : MicroCfg Q s}
    (Sched : ConcreteGoodStepSchedule N enc Foot L c c')
    {Protected : CSp -> Prop}
    (hDisjoint :
      forall sp, Foot c c' sp -> Protected sp -> False) :
    N.ScheduleUntouches Sched.schedule Protected :=
  Network.scheduleUntouches_of_scheduleTouchesOnly_disjoint
    Sched.footprint hDisjoint

theorem scheduleClears_of_disjoint
    {Q : Type u} {s : Nat}
    {CSp : Type v} [Fintype CSp]
    {N : Network.{v, w} CSp}
    {enc : MicroCfg Q s -> State CSp}
    {Foot : MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop}
    {L : Nat} {c c' : MicroCfg Q s}
    (Sched : ConcreteGoodStepSchedule N enc Foot L c c')
    {Protected : CSp -> Prop}
    (hDisjoint :
      forall sp, Foot c c' sp -> Protected sp -> False) :
    N.ScheduleClears Sched.schedule Protected :=
  Network.scheduleClears_of_scheduleTouchesOnly_disjoint
    Sched.footprint hDisjoint

theorem hoareExec_frame_eqOn_of_disjoint
    {Q : Type u} {s : Nat}
    {CSp : Type v} [Fintype CSp]
    {N : Network.{v, w} CSp}
    {enc : MicroCfg Q s -> State CSp}
    {Foot : MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop}
    {L : Nat} {c c' : MicroCfg Q s}
    (Sched : ConcreteGoodStepSchedule N enc Foot L c c')
    {Pre : State CSp -> Prop}
    {Post : State CSp -> State CSp -> Prop}
    {Protected : CSp -> Prop}
    (hSpec : N.HoareExec Sched.schedule Pre Post)
    (hDisjoint :
      forall sp, Foot c c' sp -> Protected sp -> False) :
    N.HoareExec Sched.schedule Pre
      (fun z z' => Post z z' /\ State.EqOn Protected z' z) :=
  hSpec.frame_eqOn_of_scheduleUntouches
    (Sched.scheduleUntouches_of_disjoint hDisjoint)

theorem hoareExec_frame_zeroOn_of_disjoint
    {Q : Type u} {s : Nat}
    {CSp : Type v} [Fintype CSp]
    {N : Network.{v, w} CSp}
    {enc : MicroCfg Q s -> State CSp}
    {Foot : MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop}
    {L : Nat} {c c' : MicroCfg Q s}
    (Sched : ConcreteGoodStepSchedule N enc Foot L c c')
    {Pre : State CSp -> Prop}
    {Post : State CSp -> State CSp -> Prop}
    {Protected : CSp -> Prop}
    (hSpec : N.HoareExec Sched.schedule Pre Post)
    (hDisjoint :
      forall sp, Foot c c' sp -> Protected sp -> False) :
    N.HoareExec Sched.schedule
      (fun z => Pre z /\ State.ZeroOn Protected z)
      (fun z z' => Post z z' /\ State.ZeroOn Protected z') :=
  hSpec.frame_zeroOn_of_scheduleUntouches
    (Sched.scheduleUntouches_of_disjoint hDisjoint)

theorem hoareExec_with_clears_of_disjoint
    {Q : Type u} {s : Nat}
    {CSp : Type v} [Fintype CSp]
    {N : Network.{v, w} CSp}
    {enc : MicroCfg Q s -> State CSp}
    {Foot : MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop}
    {L : Nat} {c c' : MicroCfg Q s}
    (Sched : ConcreteGoodStepSchedule N enc Foot L c c')
    {Pre : State CSp -> Prop}
    {Post : State CSp -> State CSp -> Prop}
    {Garbage : CSp -> Prop}
    (hSpec : N.HoareExec Sched.schedule Pre Post)
    (hDisjoint :
      forall sp, Foot c c' sp -> Garbage sp -> False) :
    N.HoareExec Sched.schedule
      (fun z => Pre z /\ State.ZeroOn Garbage z)
      (fun z z' => Post z z' /\ State.ZeroOn Garbage z') :=
  hSpec.with_clears
    (Sched.scheduleClears_of_disjoint hDisjoint)

theorem hoareExec_exact_frame_eqOn_of_disjoint
    {Q : Type u} {s : Nat}
    {CSp : Type v} [Fintype CSp]
    {N : Network.{v, w} CSp}
    {enc : MicroCfg Q s -> State CSp}
    {Foot : MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop}
    {L : Nat} {c c' : MicroCfg Q s}
    (Sched : ConcreteGoodStepSchedule N enc Foot L c c')
    {Protected : CSp -> Prop}
    (hDisjoint :
      forall sp, Foot c c' sp -> Protected sp -> False) :
    N.HoareExec Sched.schedule
      (fun z => z = enc c)
      (fun z z' => z' = enc c' /\ State.EqOn Protected z' z) :=
  Sched.hoareExec_frame_eqOn_of_disjoint
    Sched.hoareExec_exact hDisjoint

theorem hoareExec_exact_frame_zeroOn_of_disjoint
    {Q : Type u} {s : Nat}
    {CSp : Type v} [Fintype CSp]
    {N : Network.{v, w} CSp}
    {enc : MicroCfg Q s -> State CSp}
    {Foot : MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop}
    {L : Nat} {c c' : MicroCfg Q s}
    (Sched : ConcreteGoodStepSchedule N enc Foot L c c')
    {Protected : CSp -> Prop}
    (hDisjoint :
      forall sp, Foot c c' sp -> Protected sp -> False) :
    N.HoareExec Sched.schedule
      (fun z => z = enc c /\ State.ZeroOn Protected z)
      (fun _ z' => z' = enc c' /\ State.ZeroOn Protected z') :=
  Sched.hoareExec_frame_zeroOn_of_disjoint
    Sched.hoareExec_exact hDisjoint

theorem hoareExec_exact_with_clears_of_disjoint
    {Q : Type u} {s : Nat}
    {CSp : Type v} [Fintype CSp]
    {N : Network.{v, w} CSp}
    {enc : MicroCfg Q s -> State CSp}
    {Foot : MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop}
    {L : Nat} {c c' : MicroCfg Q s}
    (Sched : ConcreteGoodStepSchedule N enc Foot L c c')
    {Garbage : CSp -> Prop}
    (hDisjoint :
      forall sp, Foot c c' sp -> Garbage sp -> False) :
    N.HoareExec Sched.schedule
      (fun z => z = enc c /\ State.ZeroOn Garbage z)
      (fun _ z' => z' = enc c' /\ State.ZeroOn Garbage z') :=
  Sched.hoareExec_with_clears_of_disjoint
    Sched.hoareExec_exact hDisjoint

theorem boundedHoareExec_exact_frame_eqOn_of_disjoint
    {Q : Type u} {s : Nat}
    {CSp : Type v} [Fintype CSp]
    {N : Network.{v, w} CSp}
    {enc : MicroCfg Q s -> State CSp}
    {Foot : MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop}
    {L : Nat} {c c' : MicroCfg Q s}
    (Sched : ConcreteGoodStepSchedule N enc Foot L c c')
    {Protected : CSp -> Prop}
    (hDisjoint :
      forall sp, Foot c c' sp -> Protected sp -> False) :
    N.HoareExec Sched.toBoundedIntendedSchedule.schedule
      (fun z => z = enc c)
      (fun z z' => z' = enc c' /\ State.EqOn Protected z' z) :=
  Sched.hoareExec_frame_eqOn_of_disjoint
    Sched.boundedHoareExec_exact hDisjoint

theorem boundedHoareExec_exact_frame_zeroOn_of_disjoint
    {Q : Type u} {s : Nat}
    {CSp : Type v} [Fintype CSp]
    {N : Network.{v, w} CSp}
    {enc : MicroCfg Q s -> State CSp}
    {Foot : MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop}
    {L : Nat} {c c' : MicroCfg Q s}
    (Sched : ConcreteGoodStepSchedule N enc Foot L c c')
    {Protected : CSp -> Prop}
    (hDisjoint :
      forall sp, Foot c c' sp -> Protected sp -> False) :
    N.HoareExec Sched.toBoundedIntendedSchedule.schedule
      (fun z => z = enc c /\ State.ZeroOn Protected z)
      (fun _ z' => z' = enc c' /\ State.ZeroOn Protected z') :=
  Sched.hoareExec_frame_zeroOn_of_disjoint
    Sched.boundedHoareExec_exact hDisjoint

theorem boundedHoareExec_exact_with_clears_of_disjoint
    {Q : Type u} {s : Nat}
    {CSp : Type v} [Fintype CSp]
    {N : Network.{v, w} CSp}
    {enc : MicroCfg Q s -> State CSp}
    {Foot : MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop}
    {L : Nat} {c c' : MicroCfg Q s}
    (Sched : ConcreteGoodStepSchedule N enc Foot L c c')
    {Garbage : CSp -> Prop}
    (hDisjoint :
      forall sp, Foot c c' sp -> Garbage sp -> False) :
    N.HoareExec Sched.toBoundedIntendedSchedule.schedule
      (fun z => z = enc c /\ State.ZeroOn Garbage z)
      (fun _ z' => z' = enc c' /\ State.ZeroOn Garbage z') :=
  Sched.hoareExec_with_clears_of_disjoint
    Sched.boundedHoareExec_exact hDisjoint

theorem eqOn_of_disjoint
    {Q : Type u} {s : Nat}
    {CSp : Type v} [Fintype CSp]
    {N : Network.{v, w} CSp}
    {enc : MicroCfg Q s -> State CSp}
    {Foot : MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop}
    {L : Nat} {c c' : MicroCfg Q s}
    (Sched : ConcreteGoodStepSchedule N enc Foot L c c')
    {Protected : CSp -> Prop}
    (hDisjoint :
      forall sp, Foot c c' sp -> Protected sp -> False) :
    State.EqOn Protected (enc c') (enc c) :=
  Network.Exec.eqOn_of_scheduleUntouches
    Sched.exec
    (Sched.scheduleUntouches_of_disjoint hDisjoint)

theorem agreesOutside
    {Q : Type u} {s : Nat}
    {CSp : Type v} [Fintype CSp]
    {N : Network.{v, w} CSp}
    {enc : MicroCfg Q s -> State CSp}
    {Foot : MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop}
    {L : Nat} {c c' : MicroCfg Q s}
    (Sched : ConcreteGoodStepSchedule N enc Foot L c c') :
    State.AgreesOutside (Foot c c') (enc c) (enc c') :=
  Network.ExecFootprintWithin.agreesOutside
    Sched.execFootprintWithin

theorem coord_eq_of_not_footprint
    {Q : Type u} {s : Nat}
    {CSp : Type v} [Fintype CSp]
    {N : Network.{v, w} CSp}
    {enc : MicroCfg Q s -> State CSp}
    {Foot : MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop}
    {L : Nat} {c c' : MicroCfg Q s}
    (Sched : ConcreteGoodStepSchedule N enc Foot L c c')
    {sp : CSp}
    (hnot : Not (Foot c c' sp)) :
    enc c' sp = enc c sp :=
  Sched.agreesOutside.coord hnot

theorem ideal_coord_eq_of_not_local
    {Q : Type u} {s : Nat}
    {CSp : Type v} [Fintype CSp]
    {N : Network.{v, w} CSp}
    {enc : MicroCfg Q s -> State CSp}
    {ideal : FourPhaseSpecies Q -> CSp}
    {auxFootprint : MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop}
    {L : Nat} {c c' : MicroCfg Q s}
    (Sched :
      ConcreteGoodStepSchedule N enc
        (ConcreteLocalFootprint ideal auxFootprint) L c c')
    (hideal : Function.Injective ideal)
    (haux :
      forall species : FourPhaseSpecies Q,
        Not (auxFootprint c c' (ideal species)))
    {species : FourPhaseSpecies Q}
    (hnot :
      Not
        (FourPhaseSpecies.IsLocalMacroFootprint
          (FourPhaseSpecies.ctrlOf c.state)
          (FourPhaseSpecies.ctrlOf c'.state)
          species)) :
    enc c' (ideal species) = enc c (ideal species) :=
  Sched.coord_eq_of_not_footprint (by
    intro hFoot
    change
      ((exists species' : FourPhaseSpecies Q,
        FourPhaseSpecies.IsLocalMacroFootprint
          (FourPhaseSpecies.ctrlOf c.state)
          (FourPhaseSpecies.ctrlOf c'.state)
          species' /\
        ideal species = ideal species') \/
        auxFootprint c c' (ideal species)) at hFoot
    rcases hFoot with hVisible | hAux
    · rcases hVisible with ⟨species', hLocal, hEq⟩
      have hSpecies : species = species' :=
        hideal hEq
      cases hSpecies
      exact hnot hLocal
    · exact haux species hAux)

theorem ideal_coord_eq_of_not_members
    {Q : Type u} {s : Nat}
    {CSp : Type v} [Fintype CSp]
    {N : Network.{v, w} CSp}
    {enc : MicroCfg Q s -> State CSp}
    {ideal : FourPhaseSpecies Q -> CSp}
    {auxFootprint : MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop}
    {L : Nat} {c c' : MicroCfg Q s}
    (Sched :
      ConcreteGoodStepSchedule N enc
        (ConcreteLocalFootprint ideal auxFootprint) L c c')
    (hideal : Function.Injective ideal)
    (haux :
      forall species : FourPhaseSpecies Q,
        Not (auxFootprint c c' (ideal species)))
    {species : FourPhaseSpecies Q}
    (hold : species ≠ FourPhaseSpecies.ctrlOf c.state)
    (hnew : species ≠ FourPhaseSpecies.ctrlOf c'.state)
    (htape : Not (FourPhaseSpecies.IsTapePair species)) :
    enc c' (ideal species) = enc c (ideal species) :=
  Sched.ideal_coord_eq_of_not_local hideal haux
    (FourPhaseSpecies.not_localMacroFootprint_of_not_members
      (oldCtrl := FourPhaseSpecies.ctrlOf c.state)
      (newCtrl := FourPhaseSpecies.ctrlOf c'.state)
      hold hnew htape)

end ConcreteGoodStepSchedule

end FourPhaseConcrete

namespace FourPhaseConcrete

structure ConcretePhaseExpansion
    {Q : Type u} [Fintype Q] [DecidableEq Q] {s : Nat}
    {CSp : Type v} [Fintype CSp] [DecidableEq CSp]
    (M : Binary Q)
    (phase : Phase4)
    (enc : MicroCfg Q s -> State CSp) where
  N : Network.{v, w} CSp
  step_len_bound : Nat
  allAtMostBimolecularInput : N.allAtMostBimolecularInput
  hasPositiveRates : N.hasPositiveRates
  exec_of_good_phase_step :
    forall {c c' : MicroCfg Q s},
      GadgetMicroCfgWF c ->
      c.state.phase = phase ->
      phaseStep? (s := s) M c = some c' ->
        exists is : List N.I,
          N.Exec (enc c) (enc c') is /\
            is.length <= step_len_bound

namespace ConcretePhaseExpansion

variable {Q : Type u} [Fintype Q] [DecidableEq Q] {s : Nat}
variable {CSp : Type v} [Fintype CSp] [DecidableEq CSp]
variable {M : Binary Q} {phase : Phase4}
variable {enc : MicroCfg Q s -> State CSp}

noncomputable def intendedSchedule_of_good_phase_step
    (E :
      ConcretePhaseExpansion.{u, v, w}
        (s := s) (CSp := CSp) M phase enc)
    {c c' : MicroCfg Q s}
    (hc : GadgetMicroCfgWF c)
    (hphase : c.state.phase = phase)
    (hstep : phaseStep? (s := s) M c = some c') :
    E.N.IntendedSchedule (enc c) (enc c') where
  schedule := Classical.choose
    (E.exec_of_good_phase_step hc hphase hstep)
  exec := (Classical.choose_spec
    (E.exec_of_good_phase_step hc hphase hstep)).1

theorem exec_of_intendedSchedule_of_good_phase_step
    (E :
      ConcretePhaseExpansion.{u, v, w}
        (s := s) (CSp := CSp) M phase enc)
    {c c' : MicroCfg Q s}
    (hc : GadgetMicroCfgWF c)
    (hphase : c.state.phase = phase)
    (hstep : phaseStep? (s := s) M c = some c') :
    E.N.Exec (enc c) (enc c')
      (E.intendedSchedule_of_good_phase_step hc hphase hstep).schedule :=
  (E.intendedSchedule_of_good_phase_step hc hphase hstep).exec

noncomputable def boundedIntendedSchedule_of_good_phase_step
    (E :
      ConcretePhaseExpansion.{u, v, w}
        (s := s) (CSp := CSp) M phase enc)
    {c c' : MicroCfg Q s}
    (hc : GadgetMicroCfgWF c)
    (hphase : c.state.phase = phase)
    (hstep : phaseStep? (s := s) M c = some c') :
    E.N.BoundedIntendedSchedule E.step_len_bound (enc c) (enc c') where
  schedule := Classical.choose
    (E.exec_of_good_phase_step hc hphase hstep)
  exec := (Classical.choose_spec
    (E.exec_of_good_phase_step hc hphase hstep)).1
  length_bound := (Classical.choose_spec
    (E.exec_of_good_phase_step hc hphase hstep)).2

theorem exec_of_boundedIntendedSchedule_of_good_phase_step
    (E :
      ConcretePhaseExpansion.{u, v, w}
        (s := s) (CSp := CSp) M phase enc)
    {c c' : MicroCfg Q s}
    (hc : GadgetMicroCfgWF c)
    (hphase : c.state.phase = phase)
    (hstep : phaseStep? (s := s) M c = some c') :
    E.N.Exec (enc c) (enc c')
      (E.boundedIntendedSchedule_of_good_phase_step
        hc hphase hstep).schedule :=
  (E.boundedIntendedSchedule_of_good_phase_step hc hphase hstep).exec

theorem boundedIntendedSchedule_firingCount_le_of_good_phase_step
    (E :
      ConcretePhaseExpansion.{u, v, w}
        (s := s) (CSp := CSp) M phase enc)
    {c c' : MicroCfg Q s}
    (hc : GadgetMicroCfgWF c)
    (hphase : c.state.phase = phase)
    (hstep : phaseStep? (s := s) M c = some c') :
    (E.boundedIntendedSchedule_of_good_phase_step
      hc hphase hstep).firingCount <= E.step_len_bound :=
  Network.BoundedIntendedSchedule.firingCount_le_bound
    (E.boundedIntendedSchedule_of_good_phase_step hc hphase hstep)

theorem intended_reaches_of_good_phase_step
    (E :
      ConcretePhaseExpansion.{u, v, w}
        (s := s) (CSp := CSp) M phase enc)
    {c c' : MicroCfg Q s}
    (hc : GadgetMicroCfgWF c)
    (hphase : c.state.phase = phase)
    (hstep : phaseStep? (s := s) M c = some c') :
    E.N.Reaches (enc c) (enc c') :=
  (E.intendedSchedule_of_good_phase_step hc hphase hstep).reaches

theorem boundedIntendedSchedule_reaches_of_good_phase_step
    (E :
      ConcretePhaseExpansion.{u, v, w}
        (s := s) (CSp := CSp) M phase enc)
    {c c' : MicroCfg Q s}
    (hc : GadgetMicroCfgWF c)
    (hphase : c.state.phase = phase)
    (hstep : phaseStep? (s := s) M c = some c') :
    E.N.Reaches (enc c) (enc c') :=
  (E.boundedIntendedSchedule_of_good_phase_step hc hphase hstep).reaches

theorem reaches_of_good_phase_step
    (E :
      ConcretePhaseExpansion.{u, v, w}
        (s := s) (CSp := CSp) M phase enc)
    {c c' : MicroCfg Q s}
    (hc : GadgetMicroCfgWF c)
    (hphase : c.state.phase = phase)
    (hstep : phaseStep? (s := s) M c = some c') :
    E.N.Reaches (enc c) (enc c') :=
  E.intended_reaches_of_good_phase_step hc hphase hstep

end ConcretePhaseExpansion

structure ConcreteFourPhaseExpansionFamily
    {Q : Type u} [Fintype Q] [DecidableEq Q] {s : Nat}
    (M : Binary Q) where
  CSp : Type v
  instFintype : Fintype CSp
  instDecidableEq : DecidableEq CSp
  enc : MicroCfg Q s -> State CSp
  ideal : FourPhaseSpecies Q -> CSp
  ideal_injective : Function.Injective ideal
  enc_ideal :
    forall (c : MicroCfg Q s) (species : FourPhaseSpecies Q),
      enc c (ideal species) = FourPhaseEncoding.enc c species
  read :
    ConcretePhaseExpansion.{u, v, w}
      (s := s) (CSp := CSp) M Phase4.read enc
  erase :
    ConcretePhaseExpansion.{u, v, w}
      (s := s) (CSp := CSp) M Phase4.erase enc
  shift :
    ConcretePhaseExpansion.{u, v, w}
      (s := s) (CSp := CSp) M Phase4.shift enc
  write :
    ConcretePhaseExpansion.{u, v, w}
      (s := s) (CSp := CSp) M Phase4.write enc

namespace ConcreteFourPhaseExpansionFamily

attribute [instance] instFintype instDecidableEq

variable {Q : Type u} [Fintype Q] [DecidableEq Q] {s : Nat}
variable {M : Binary Q}

def step_len_bound
    (F : ConcreteFourPhaseExpansionFamily.{u, v, w} (s := s) M) :
    Nat :=
  F.read.step_len_bound + F.erase.step_len_bound +
    F.shift.step_len_bound + F.write.step_len_bound

def network
    (F : ConcreteFourPhaseExpansionFamily.{u, v, w} (s := s) M) :
    Network.{v, w} F.CSp :=
  phaseParallel4 F.read.N F.erase.N F.shift.N F.write.N

theorem network_allAtMostBimolecularInput
    (F : ConcreteFourPhaseExpansionFamily.{u, v, w} (s := s) M) :
    F.network.allAtMostBimolecularInput := by
  dsimp [network]
  exact phaseParallel4_allAtMostBimolecularInput
    F.read.allAtMostBimolecularInput
    F.erase.allAtMostBimolecularInput
    F.shift.allAtMostBimolecularInput
    F.write.allAtMostBimolecularInput

theorem network_hasPositiveRates
    (F : ConcreteFourPhaseExpansionFamily.{u, v, w} (s := s) M) :
    F.network.hasPositiveRates := by
  dsimp [network]
  exact phaseParallel4_hasPositiveRates
    F.read.hasPositiveRates
    F.erase.hasPositiveRates
    F.shift.hasPositiveRates
    F.write.hasPositiveRates

end ConcreteFourPhaseExpansionFamily

end FourPhaseConcrete

/--
Deterministic interface for a concrete four-phase network.

The residual proof obligation is `step_exec_bounded`: every well-formed ideal
four-phase step has a concrete scheduled execution between concrete boundary
encodings. Static arity/rate fields are syntactic network predicates; this
record does not state autonomous scheduler safety or stochastic correctness.
-/
structure ConcreteFourPhaseModule
    {Q : Type u} [Fintype Q] [DecidableEq Q] {s : Nat}
    (M : Binary Q) where
  CSp : Type v
  instFintype : Fintype CSp
  instDecidableEq : DecidableEq CSp
  N : Network.{v, w} CSp
  enc : MicroCfg Q s -> State CSp
  ideal : FourPhaseSpecies Q -> CSp
  ideal_injective : Function.Injective ideal
  enc_ideal :
    forall (c : MicroCfg Q s) (species : FourPhaseSpecies Q),
      enc c (ideal species) = FourPhaseEncoding.enc c species
  step_len_bound : Nat
  allAtMostBimolecularInput : N.allAtMostBimolecularInput
  hasPositiveRates : N.hasPositiveRates
  step_exec_bounded :
    forall {c c' : MicroCfg Q s},
      GadgetMicroCfgWF c ->
      phaseStep? (s := s) M c = some c' ->
        exists is : List N.I,
          N.Exec (enc c) (enc c') is /\
            is.length <= step_len_bound

namespace ConcreteFourPhaseModule

attribute [instance] instFintype instDecidableEq

variable {Q : Type u} [Fintype Q] [DecidableEq Q] {s : Nat}
variable {M : Binary Q}

def encMicro
    (G : ConcreteFourPhaseModule.{u, v, w} (s := s) M)
    (c : MicroCfg Q s) : State G.CSp :=
  G.enc c

def encCTM
    (G : ConcreteFourPhaseModule.{u, v, w} (s := s) M)
    (cfg : Cfg Q Bool s) : State G.CSp :=
  G.encMicro (MicroCfg.ofCTM cfg)

@[simp]
theorem encMicro_ideal
    (G : ConcreteFourPhaseModule.{u, v, w} (s := s) M)
    (c : MicroCfg Q s) (species : FourPhaseSpecies Q) :
    G.encMicro c (G.ideal species) =
      FourPhaseEncoding.enc c species :=
  G.enc_ideal c species

@[simp]
theorem encCTM_ideal
    (G : ConcreteFourPhaseModule.{u, v, w} (s := s) M)
    (cfg : Cfg Q Bool s) (species : FourPhaseSpecies Q) :
    G.encCTM cfg (G.ideal species) =
      FourPhaseEncoding.enc (MicroCfg.ofCTM cfg) species :=
  G.enc_ideal (MicroCfg.ofCTM cfg) species

theorem concrete_allAtMostBimolecularInput
    (G : ConcreteFourPhaseModule.{u, v, w} (s := s) M) :
    G.N.allAtMostBimolecularInput :=
  G.allAtMostBimolecularInput

theorem concrete_hasPositiveRates
    (G : ConcreteFourPhaseModule.{u, v, w} (s := s) M) :
    G.N.hasPositiveRates :=
  G.hasPositiveRates

def toInvariantStepwiseRealization
    (G : ConcreteFourPhaseModule.{u, v, w} (s := s) M) :
    InvariantStepwiseRealization
      (fourPhaseSystem (s := s) M) G.N
      (GadgetMicroCfgWF (Q := Q) (s := s)) where
  enc := G.enc
  step_exec := by
    intro c c' hc hstep
    rcases G.step_exec_bounded hc hstep with ⟨is, hExec, _hLen⟩
    exact ⟨is, hExec⟩
  step_preserves := by
    intro c c' hc hstep
    exact phaseStep?_preserves_gadgetWF (s := s) M hc hstep

theorem exec_of_ctm_steps
    (G : ConcreteFourPhaseModule.{u, v, w} (s := s) M)
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

theorem exec_of_fourPhase_steps_bounded
    (G : ConcreteFourPhaseModule.{u, v, w} (s := s) M)
    {n : Nat} {c c' : MicroCfg Q s}
    (hc : GadgetMicroCfgWF c)
    (h : (fourPhaseSystem (s := s) M).steps? n c = some c') :
    exists is : List G.N.I,
      G.N.Exec (G.encMicro c) (G.encMicro c') is /\
        is.length <= G.step_len_bound * n := by
  induction n generalizing c c' with
  | zero =>
      have hSome : (some c : Option (MicroCfg Q s)) = some c' := by
        exact h
      cases hSome
      exact ⟨[], ExecOf.nil (G.encMicro c), by simp⟩
  | succ n ih =>
      cases hstep : (fourPhaseSystem (s := s) M).step? c with
      | none =>
          simp [DetSystem.steps?, DetSystem.iter, hstep] at h
      | some c₁ =>
          have hc₁ : GadgetMicroCfgWF c₁ :=
            phaseStep?_preserves_gadgetWF (s := s) M hc
              (by simpa [fourPhaseSystem] using hstep)
          have htail :
              (fourPhaseSystem (s := s) M).steps? n c₁ = some c' := by
            simpa [DetSystem.steps?, DetSystem.iter, hstep] using h
          have hphase :
              phaseStep? (s := s) M c = some c₁ := by
            simpa [fourPhaseSystem] using hstep
          rcases G.step_exec_bounded hc hphase with
            ⟨is, hExecStep, hLenStep⟩
          rcases ih hc₁ htail with ⟨js, hExecTail, hLenTail⟩
          refine ⟨is ++ js, ExecOf.append hExecStep hExecTail, ?_⟩
          have hLen :
              (is ++ js).length <=
                G.step_len_bound + G.step_len_bound * n := by
            simpa [List.length_append] using
              Nat.add_le_add hLenStep hLenTail
          simpa [Nat.mul_succ, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
            using hLen

noncomputable def intendedSchedule_of_fourPhase_steps
    (G : ConcreteFourPhaseModule.{u, v, w} (s := s) M)
    {n : Nat} {c c' : MicroCfg Q s}
    (hc : GadgetMicroCfgWF c)
    (h : (fourPhaseSystem (s := s) M).steps? n c = some c') :
    G.N.IntendedSchedule (G.encMicro c) (G.encMicro c') where
  schedule := Classical.choose (G.exec_of_fourPhase_steps_bounded hc h)
  exec := (Classical.choose_spec (G.exec_of_fourPhase_steps_bounded hc h)).1

theorem exec_of_intendedSchedule_of_fourPhase_steps
    (G : ConcreteFourPhaseModule.{u, v, w} (s := s) M)
    {n : Nat} {c c' : MicroCfg Q s}
    (hc : GadgetMicroCfgWF c)
    (h : (fourPhaseSystem (s := s) M).steps? n c = some c') :
    G.N.Exec (G.encMicro c) (G.encMicro c')
      (G.intendedSchedule_of_fourPhase_steps hc h).schedule :=
  (G.intendedSchedule_of_fourPhase_steps hc h).exec

noncomputable def boundedIntendedSchedule_of_fourPhase_steps
    (G : ConcreteFourPhaseModule.{u, v, w} (s := s) M)
    {n : Nat} {c c' : MicroCfg Q s}
    (hc : GadgetMicroCfgWF c)
    (h : (fourPhaseSystem (s := s) M).steps? n c = some c') :
    G.N.BoundedIntendedSchedule
      (G.step_len_bound * n) (G.encMicro c) (G.encMicro c') where
  schedule := Classical.choose (G.exec_of_fourPhase_steps_bounded hc h)
  exec := (Classical.choose_spec (G.exec_of_fourPhase_steps_bounded hc h)).1
  length_bound :=
    (Classical.choose_spec (G.exec_of_fourPhase_steps_bounded hc h)).2

theorem exec_of_boundedIntendedSchedule_of_fourPhase_steps
    (G : ConcreteFourPhaseModule.{u, v, w} (s := s) M)
    {n : Nat} {c c' : MicroCfg Q s}
    (hc : GadgetMicroCfgWF c)
    (h : (fourPhaseSystem (s := s) M).steps? n c = some c') :
    G.N.Exec (G.encMicro c) (G.encMicro c')
      (G.boundedIntendedSchedule_of_fourPhase_steps hc h).schedule :=
  (G.boundedIntendedSchedule_of_fourPhase_steps hc h).exec

theorem boundedIntendedSchedule_firingCount_le_of_fourPhase_steps
    (G : ConcreteFourPhaseModule.{u, v, w} (s := s) M)
    {n : Nat} {c c' : MicroCfg Q s}
    (hc : GadgetMicroCfgWF c)
    (h : (fourPhaseSystem (s := s) M).steps? n c = some c') :
    (G.boundedIntendedSchedule_of_fourPhase_steps hc h).firingCount <=
      G.step_len_bound * n :=
  Network.BoundedIntendedSchedule.firingCount_le_bound
    (G.boundedIntendedSchedule_of_fourPhase_steps hc h)

theorem state_after_fourPhase_steps_of_intendedWinsRaceAt
    (G : ConcreteFourPhaseModule.{u, v, w} (s := s) M)
    {n : Nat} {c c' : MicroCfg Q s}
    {path : G.N.Path} {Bad : G.N.BadIndexSet} {t : Nat}
    (hc : GadgetMicroCfgWF c)
    (h : (fourPhaseSystem (s := s) M).steps? n c = some c')
    (hwin :
      path.IntendedWinsRaceAt Bad t
        (G.intendedSchedule_of_fourPhase_steps hc h)) :
    path.state
        (t + (G.intendedSchedule_of_fourPhase_steps hc h).firingCount) =
      G.encMicro c' := by
  simpa [Network.IntendedSchedule.firingCount] using
    path.state_after_intendedWinsRaceAt Bad
      (G.intendedSchedule_of_fourPhase_steps hc h)
      hwin

theorem state_after_bounded_fourPhase_steps_of_intendedWinsRaceAt
    (G : ConcreteFourPhaseModule.{u, v, w} (s := s) M)
    {n : Nat} {c c' : MicroCfg Q s}
    {path : G.N.Path} {Bad : G.N.BadIndexSet} {t : Nat}
    (hc : GadgetMicroCfgWF c)
    (h : (fourPhaseSystem (s := s) M).steps? n c = some c')
    (hwin :
      path.IntendedWinsRaceAt Bad t
        (G.boundedIntendedSchedule_of_fourPhase_steps hc h).toIntendedSchedule) :
    path.state
        (t + (G.boundedIntendedSchedule_of_fourPhase_steps hc h).firingCount) =
      G.encMicro c' :=
  path.state_after_boundedIntendedWinsRaceAt Bad
    (G.boundedIntendedSchedule_of_fourPhase_steps hc h)
    hwin

theorem intended_reaches_of_fourPhase_steps
    (G : ConcreteFourPhaseModule.{u, v, w} (s := s) M)
    {n : Nat} {c c' : MicroCfg Q s}
    (hc : GadgetMicroCfgWF c)
    (h : (fourPhaseSystem (s := s) M).steps? n c = some c') :
    G.N.Reaches (G.encMicro c) (G.encMicro c') :=
  (G.intendedSchedule_of_fourPhase_steps hc h).reaches

theorem boundedIntendedSchedule_reaches_of_fourPhase_steps
    (G : ConcreteFourPhaseModule.{u, v, w} (s := s) M)
    {n : Nat} {c c' : MicroCfg Q s}
    (hc : GadgetMicroCfgWF c)
    (h : (fourPhaseSystem (s := s) M).steps? n c = some c') :
    G.N.Reaches (G.encMicro c) (G.encMicro c') :=
  (G.boundedIntendedSchedule_of_fourPhase_steps hc h).reaches

theorem reaches_of_fourPhase_steps
    (G : ConcreteFourPhaseModule.{u, v, w} (s := s) M)
    {n : Nat} {c c' : MicroCfg Q s}
    (hc : GadgetMicroCfgWF c)
    (h : (fourPhaseSystem (s := s) M).steps? n c = some c') :
    G.N.Reaches (G.encMicro c) (G.encMicro c') :=
  (G.intendedSchedule_of_fourPhase_steps hc h).reaches

theorem coverable_of_fourPhase_steps_covers
    (G : ConcreteFourPhaseModule.{u, v, w} (s := s) M)
    {n : Nat} {c c' : MicroCfg Q s}
    {target : State G.CSp}
    (hc : GadgetMicroCfgWF c)
    (h : (fourPhaseSystem (s := s) M).steps? n c = some c')
    (hCovers : Covers (G.encMicro c') target) :
    G.N.CoverableFrom (G.encMicro c) target :=
  Network.coverable_of_reaches_of_covers
    (G.reaches_of_fourPhase_steps hc h)
    hCovers

theorem coverable_of_fourPhase_steps_of_le
    (G : ConcreteFourPhaseModule.{u, v, w} (s := s) M)
    {n : Nat} {c c' : MicroCfg Q s}
    {target : State G.CSp}
    (hc : GadgetMicroCfgWF c)
    (h : (fourPhaseSystem (s := s) M).steps? n c = some c')
    (hTarget : forall species, target species <= G.encMicro c' species) :
    G.N.CoverableFrom (G.encMicro c) target :=
  G.coverable_of_fourPhase_steps_covers hc h hTarget

theorem coverableFrom_of_fourPhase_steps_covers
    (G : ConcreteFourPhaseModule.{u, v, w} (s := s) M)
    {n : Nat} {c c' : MicroCfg Q s}
    {target : State G.CSp}
    (hc : GadgetMicroCfgWF c)
    (h : (fourPhaseSystem (s := s) M).steps? n c = some c')
    (hCovers : Covers (G.encMicro c') target) :
    G.N.CoverableFrom (G.encMicro c) target :=
  G.coverable_of_fourPhase_steps_covers hc h hCovers

theorem coverableFrom_of_fourPhase_steps_of_le
    (G : ConcreteFourPhaseModule.{u, v, w} (s := s) M)
    {n : Nat} {c c' : MicroCfg Q s}
    {target : State G.CSp}
    (hc : GadgetMicroCfgWF c)
    (h : (fourPhaseSystem (s := s) M).steps? n c = some c')
    (hTarget : forall species, target species <= G.encMicro c' species) :
    G.N.CoverableFrom (G.encMicro c) target :=
  G.coverable_of_fourPhase_steps_of_le hc h hTarget

theorem ideal_coverable_of_fourPhase_steps_covers
    (G : ConcreteFourPhaseModule.{u, v, w} (s := s) M)
    {n : Nat} {c c' : MicroCfg Q s}
    {target : State (FourPhaseSpecies Q)}
    (hc : GadgetMicroCfgWF c)
    (h : (fourPhaseSystem (s := s) M).steps? n c = some c')
    (hCovers : Covers (FourPhaseEncoding.enc c') target) :
    G.N.CoverableFrom
      (G.encMicro c)
      (State.embed G.ideal target) := by
  refine G.coverable_of_fourPhase_steps_covers hc h ?_
  intro species
  by_cases hImage : exists idealSpecies, G.ideal idealSpecies = species
  · rcases hImage with ⟨idealSpecies, rfl⟩
    simpa [State.embed_apply_of_injective
      (e := G.ideal) G.ideal_injective target idealSpecies] using
      hCovers idealSpecies
  · have hzero :
        State.embed G.ideal target species = 0 :=
      State.embed_eq_zero_of_not_exists
        (e := G.ideal) (z := target) (t := species) hImage
    simp [hzero]

theorem ideal_coverable_of_fourPhase_steps_of_le
    (G : ConcreteFourPhaseModule.{u, v, w} (s := s) M)
    {n : Nat} {c c' : MicroCfg Q s}
    {target : State (FourPhaseSpecies Q)}
    (hc : GadgetMicroCfgWF c)
    (h : (fourPhaseSystem (s := s) M).steps? n c = some c')
    (hTarget :
      forall species, target species <= FourPhaseEncoding.enc c' species) :
    G.N.CoverableFrom
      (G.encMicro c)
      (State.embed G.ideal target) :=
  G.ideal_coverable_of_fourPhase_steps_covers hc h hTarget

theorem ideal_coverableFrom_of_fourPhase_steps_covers
    (G : ConcreteFourPhaseModule.{u, v, w} (s := s) M)
    {n : Nat} {c c' : MicroCfg Q s}
    {target : State (FourPhaseSpecies Q)}
    (hc : GadgetMicroCfgWF c)
    (h : (fourPhaseSystem (s := s) M).steps? n c = some c')
    (hCovers : Covers (FourPhaseEncoding.enc c') target) :
    G.N.CoverableFrom
      (G.encMicro c)
      (State.embed G.ideal target) :=
  G.ideal_coverable_of_fourPhase_steps_covers hc h hCovers

theorem ideal_coverableFrom_of_fourPhase_steps_of_le
    (G : ConcreteFourPhaseModule.{u, v, w} (s := s) M)
    {n : Nat} {c c' : MicroCfg Q s}
    {target : State (FourPhaseSpecies Q)}
    (hc : GadgetMicroCfgWF c)
    (h : (fourPhaseSystem (s := s) M).steps? n c = some c')
    (hTarget :
      forall species, target species <= FourPhaseEncoding.enc c' species) :
    G.N.CoverableFrom
      (G.encMicro c)
      (State.embed G.ideal target) :=
  G.ideal_coverable_of_fourPhase_steps_of_le hc h hTarget

theorem speciesCoverableFrom_of_fourPhase_steps_coord
    (G : ConcreteFourPhaseModule.{u, v, w} (s := s) M)
    {n : Nat} {c c' : MicroCfg Q s}
    {species : G.CSp} {amount : Nat}
    (hc : GadgetMicroCfgWF c)
    (h : (fourPhaseSystem (s := s) M).steps? n c = some c')
    (hamount : amount <= G.encMicro c' species) :
    G.N.SpeciesCoverableFrom (G.encMicro c) species amount :=
  Network.speciesCoverableFrom_of_reaches_coord
    (G.reaches_of_fourPhase_steps hc h)
    hamount

theorem speciesCoverableFrom_one_of_fourPhase_steps_pos
    (G : ConcreteFourPhaseModule.{u, v, w} (s := s) M)
    {n : Nat} {c c' : MicroCfg Q s}
    {species : G.CSp}
    (hc : GadgetMicroCfgWF c)
    (h : (fourPhaseSystem (s := s) M).steps? n c = some c')
    (hpos : 0 < G.encMicro c' species) :
    G.N.SpeciesCoverableFrom (G.encMicro c) species :=
  Network.speciesCoverableFrom_one_of_reaches_pos
    (G.reaches_of_fourPhase_steps hc h)
    hpos

theorem ideal_speciesCoverableFrom_of_fourPhase_steps
    (G : ConcreteFourPhaseModule.{u, v, w} (s := s) M)
    {n : Nat} {c c' : MicroCfg Q s}
    {species : FourPhaseSpecies Q} {amount : Nat}
    (hc : GadgetMicroCfgWF c)
    (h : (fourPhaseSystem (s := s) M).steps? n c = some c')
    (hamount : amount <= FourPhaseEncoding.enc c' species) :
    G.N.SpeciesCoverableFrom
      (G.encMicro c) (G.ideal species) amount := by
  have hamount' :
      amount <= G.encMicro c' (G.ideal species) := by
    simpa [encMicro] using
      (by
        rw [G.enc_ideal c' species]
        exact hamount)
  exact G.speciesCoverableFrom_of_fourPhase_steps_coord hc h hamount'

theorem ideal_speciesCoverableFrom_one_of_fourPhase_steps_pos
    (G : ConcreteFourPhaseModule.{u, v, w} (s := s) M)
    {n : Nat} {c c' : MicroCfg Q s}
    {species : FourPhaseSpecies Q}
    (hc : GadgetMicroCfgWF c)
    (h : (fourPhaseSystem (s := s) M).steps? n c = some c')
    (hpos : 0 < FourPhaseEncoding.enc c' species) :
    G.N.SpeciesCoverableFrom
      (G.encMicro c) (G.ideal species) := by
  have hpos' : 0 < G.encMicro c' (G.ideal species) := by
    simpa [encMicro] using
      (by
        rw [G.enc_ideal c' species]
        exact hpos)
  exact G.speciesCoverableFrom_one_of_fourPhase_steps_pos hc h hpos'

def toBoundedStepwiseRealization
    (G : ConcreteFourPhaseModule.{u, v, w} (s := s) M) :
    BoundedStepwiseRealization (M.detSystem (s := s)) G.N where
  enc := G.encCTM
  step_len_bound := G.step_len_bound * 4
  step_exec_bounded := by
    intro cfg cfg' hstep
    have hMicro :
        (fourPhaseSystem (s := s) M).steps? 4
          (MicroCfg.ofCTM cfg) = some (MicroCfg.ofCTM cfg') :=
      (fourPhaseKStepSim (s := s) M).step_ok hstep
    simpa [encCTM, encMicro] using
      G.exec_of_fourPhase_steps_bounded
        (MicroCfg.ofCTM_gadgetWF cfg)
        hMicro

theorem exec_of_ctm_steps_bounded
    (G : ConcreteFourPhaseModule.{u, v, w} (s := s) M)
    {n : Nat} {cfg cfg' : Cfg Q Bool s}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg') :
    exists is : List G.N.I,
      G.N.Exec (G.encCTM cfg) (G.encCTM cfg') is /\
        is.length <= (G.step_len_bound * 4) * n := by
  simpa [toBoundedStepwiseRealization] using
    G.toBoundedStepwiseRealization.exec_of_steps_bounded h

noncomputable def intendedSchedule_of_ctm_steps
    (G : ConcreteFourPhaseModule.{u, v, w} (s := s) M)
    {n : Nat} {cfg cfg' : Cfg Q Bool s}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg') :
    G.N.IntendedSchedule (G.encCTM cfg) (G.encCTM cfg') where
  schedule := Classical.choose (G.exec_of_ctm_steps h)
  exec := Classical.choose_spec (G.exec_of_ctm_steps h)

theorem exec_of_intendedSchedule_of_ctm_steps
    (G : ConcreteFourPhaseModule.{u, v, w} (s := s) M)
    {n : Nat} {cfg cfg' : Cfg Q Bool s}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg') :
    G.N.Exec (G.encCTM cfg) (G.encCTM cfg')
      (G.intendedSchedule_of_ctm_steps h).schedule :=
  (G.intendedSchedule_of_ctm_steps h).exec

noncomputable def boundedIntendedSchedule_of_ctm_steps
    (G : ConcreteFourPhaseModule.{u, v, w} (s := s) M)
    {n : Nat} {cfg cfg' : Cfg Q Bool s}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg') :
    G.N.BoundedIntendedSchedule
      ((G.step_len_bound * 4) * n)
      (G.encCTM cfg)
      (G.encCTM cfg') where
  schedule := Classical.choose (G.exec_of_ctm_steps_bounded h)
  exec := (Classical.choose_spec (G.exec_of_ctm_steps_bounded h)).1
  length_bound := (Classical.choose_spec (G.exec_of_ctm_steps_bounded h)).2

theorem exec_of_boundedIntendedSchedule_of_ctm_steps
    (G : ConcreteFourPhaseModule.{u, v, w} (s := s) M)
    {n : Nat} {cfg cfg' : Cfg Q Bool s}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg') :
    G.N.Exec (G.encCTM cfg) (G.encCTM cfg')
      (G.boundedIntendedSchedule_of_ctm_steps h).schedule :=
  (G.boundedIntendedSchedule_of_ctm_steps h).exec

noncomputable def intendedSchedule_of_ctm_step
    (G : ConcreteFourPhaseModule.{u, v, w} (s := s) M)
    {cfg cfg' : Cfg Q Bool s}
    (h : M.step? cfg = some cfg') :
    G.N.IntendedSchedule (G.encCTM cfg) (G.encCTM cfg') :=
  G.intendedSchedule_of_ctm_steps
    (DetSystem.steps?_one_of_step? (M.detSystem (s := s)) h)

theorem exec_of_intendedSchedule_of_ctm_step
    (G : ConcreteFourPhaseModule.{u, v, w} (s := s) M)
    {cfg cfg' : Cfg Q Bool s}
    (h : M.step? cfg = some cfg') :
    G.N.Exec (G.encCTM cfg) (G.encCTM cfg')
      (G.intendedSchedule_of_ctm_step h).schedule :=
  (G.intendedSchedule_of_ctm_step h).exec

noncomputable def boundedIntendedSchedule_of_ctm_step
    (G : ConcreteFourPhaseModule.{u, v, w} (s := s) M)
    {cfg cfg' : Cfg Q Bool s}
    (h : M.step? cfg = some cfg') :
    G.N.BoundedIntendedSchedule
      (G.step_len_bound * 4)
      (G.encCTM cfg)
      (G.encCTM cfg') where
  schedule := Classical.choose
    (G.toBoundedStepwiseRealization.step_exec_bounded h)
  exec := (Classical.choose_spec
    (G.toBoundedStepwiseRealization.step_exec_bounded h)).1
  length_bound := (Classical.choose_spec
    (G.toBoundedStepwiseRealization.step_exec_bounded h)).2

theorem exec_of_boundedIntendedSchedule_of_ctm_step
    (G : ConcreteFourPhaseModule.{u, v, w} (s := s) M)
    {cfg cfg' : Cfg Q Bool s}
    (h : M.step? cfg = some cfg') :
    G.N.Exec (G.encCTM cfg) (G.encCTM cfg')
      (G.boundedIntendedSchedule_of_ctm_step h).schedule :=
  (G.boundedIntendedSchedule_of_ctm_step h).exec

theorem boundedIntendedSchedule_firingCount_le_of_ctm_step
    (G : ConcreteFourPhaseModule.{u, v, w} (s := s) M)
    {cfg cfg' : Cfg Q Bool s}
    (h : M.step? cfg = some cfg') :
    (G.boundedIntendedSchedule_of_ctm_step h).firingCount <=
      G.step_len_bound * 4 :=
  Network.BoundedIntendedSchedule.firingCount_le_bound
    (G.boundedIntendedSchedule_of_ctm_step h)

theorem state_after_ctm_step_of_firesListAt
    (G : ConcreteFourPhaseModule.{u, v, w} (s := s) M)
    {cfg cfg' : Cfg Q Bool s}
    {path : G.N.Path} {t : Nat}
    (h : M.step? cfg = some cfg')
    (hstate : path.state t = G.encCTM cfg)
    (hfires :
      path.FiresListAt t (G.intendedSchedule_of_ctm_step h).schedule) :
    path.state
        (t + (G.intendedSchedule_of_ctm_step h).firingCount) =
      G.encCTM cfg' := by
  simpa [Network.IntendedSchedule.firingCount] using
    path.state_after_intended_of_firesListAt
      (G.intendedSchedule_of_ctm_step h)
      hstate
      hfires

theorem state_after_ctm_step_of_intendedWinsRaceAt
    (G : ConcreteFourPhaseModule.{u, v, w} (s := s) M)
    {cfg cfg' : Cfg Q Bool s}
    {path : G.N.Path} {Bad : G.N.BadIndexSet} {t : Nat}
    (h : M.step? cfg = some cfg')
    (hwin :
      path.IntendedWinsRaceAt Bad t
        (G.intendedSchedule_of_ctm_step h)) :
    path.state
        (t + (G.intendedSchedule_of_ctm_step h).firingCount) =
      G.encCTM cfg' := by
  simpa [Network.IntendedSchedule.firingCount] using
    path.state_after_intendedWinsRaceAt Bad
      (G.intendedSchedule_of_ctm_step h)
      hwin

theorem state_after_bounded_ctm_step_of_intendedWinsRaceAt
    (G : ConcreteFourPhaseModule.{u, v, w} (s := s) M)
    {cfg cfg' : Cfg Q Bool s}
    {path : G.N.Path} {Bad : G.N.BadIndexSet} {t : Nat}
    (h : M.step? cfg = some cfg')
    (hwin :
      path.IntendedWinsRaceAt Bad t
        (G.boundedIntendedSchedule_of_ctm_step h).toIntendedSchedule) :
    path.state
        (t + (G.boundedIntendedSchedule_of_ctm_step h).firingCount) =
      G.encCTM cfg' :=
  path.state_after_boundedIntendedWinsRaceAt Bad
    (G.boundedIntendedSchedule_of_ctm_step h)
    hwin

theorem state_after_bounded_ctm_step_of_firesListAt
    (G : ConcreteFourPhaseModule.{u, v, w} (s := s) M)
    {cfg cfg' : Cfg Q Bool s}
    {path : G.N.Path} {t : Nat}
    (h : M.step? cfg = some cfg')
    (hstate : path.state t = G.encCTM cfg)
    (hfires :
      path.FiresListAt t
        (G.boundedIntendedSchedule_of_ctm_step h).schedule) :
    path.state
        (t + (G.boundedIntendedSchedule_of_ctm_step h).firingCount) =
      G.encCTM cfg' :=
  path.state_after_boundedIntended_of_firesListAt
    (G.boundedIntendedSchedule_of_ctm_step h)
    hstate
    hfires

theorem intended_reaches_of_ctm_step
    (G : ConcreteFourPhaseModule.{u, v, w} (s := s) M)
    {cfg cfg' : Cfg Q Bool s}
    (h : M.step? cfg = some cfg') :
    G.N.Reaches (G.encCTM cfg) (G.encCTM cfg') :=
  (G.intendedSchedule_of_ctm_step h).reaches

theorem boundedIntendedSchedule_reaches_of_ctm_step
    (G : ConcreteFourPhaseModule.{u, v, w} (s := s) M)
    {cfg cfg' : Cfg Q Bool s}
    (h : M.step? cfg = some cfg') :
    G.N.Reaches (G.encCTM cfg) (G.encCTM cfg') :=
  (G.boundedIntendedSchedule_of_ctm_step h).reaches

theorem reaches_of_ctm_step
    (G : ConcreteFourPhaseModule.{u, v, w} (s := s) M)
    {cfg cfg' : Cfg Q Bool s}
    (h : M.step? cfg = some cfg') :
    G.N.Reaches (G.encCTM cfg) (G.encCTM cfg') :=
  G.intended_reaches_of_ctm_step h

theorem coverable_of_ctm_step_covers
    (G : ConcreteFourPhaseModule.{u, v, w} (s := s) M)
    {cfg cfg' : Cfg Q Bool s}
    {target : State G.CSp}
    (h : M.step? cfg = some cfg')
    (hCovers : Covers (G.encCTM cfg') target) :
    G.N.CoverableFrom (G.encCTM cfg) target :=
  Network.coverable_of_reaches_of_covers
    (G.intended_reaches_of_ctm_step h)
    hCovers

theorem coverable_of_ctm_step_of_le
    (G : ConcreteFourPhaseModule.{u, v, w} (s := s) M)
    {cfg cfg' : Cfg Q Bool s}
    {target : State G.CSp}
    (h : M.step? cfg = some cfg')
    (hTarget : forall species, target species <= G.encCTM cfg' species) :
    G.N.CoverableFrom (G.encCTM cfg) target :=
  G.coverable_of_ctm_step_covers h hTarget

theorem coverableFrom_of_ctm_step_covers
    (G : ConcreteFourPhaseModule.{u, v, w} (s := s) M)
    {cfg cfg' : Cfg Q Bool s}
    {target : State G.CSp}
    (h : M.step? cfg = some cfg')
    (hCovers : Covers (G.encCTM cfg') target) :
    G.N.CoverableFrom (G.encCTM cfg) target :=
  G.coverable_of_ctm_step_covers h hCovers

theorem coverableFrom_of_ctm_step_of_le
    (G : ConcreteFourPhaseModule.{u, v, w} (s := s) M)
    {cfg cfg' : Cfg Q Bool s}
    {target : State G.CSp}
    (h : M.step? cfg = some cfg')
    (hTarget : forall species, target species <= G.encCTM cfg' species) :
    G.N.CoverableFrom (G.encCTM cfg) target :=
  G.coverable_of_ctm_step_of_le h hTarget

theorem speciesCoverableFrom_of_ctm_step_coord
    (G : ConcreteFourPhaseModule.{u, v, w} (s := s) M)
    {cfg cfg' : Cfg Q Bool s}
    {species : G.CSp} {amount : Nat}
    (h : M.step? cfg = some cfg')
    (hamount : amount <= G.encCTM cfg' species) :
    G.N.SpeciesCoverableFrom (G.encCTM cfg) species amount :=
  Network.speciesCoverableFrom_of_reaches_coord
    (G.intended_reaches_of_ctm_step h)
    hamount

theorem speciesCoverableFrom_one_of_ctm_step_pos
    (G : ConcreteFourPhaseModule.{u, v, w} (s := s) M)
    {cfg cfg' : Cfg Q Bool s}
    {species : G.CSp}
    (h : M.step? cfg = some cfg')
    (hpos : 0 < G.encCTM cfg' species) :
    G.N.SpeciesCoverableFrom (G.encCTM cfg) species :=
  Network.speciesCoverableFrom_one_of_reaches_pos
    (G.intended_reaches_of_ctm_step h)
    hpos

theorem ideal_coverable_of_ctm_step_covers
    (G : ConcreteFourPhaseModule.{u, v, w} (s := s) M)
    {cfg cfg' : Cfg Q Bool s}
    {target : State (FourPhaseSpecies Q)}
    (h : M.step? cfg = some cfg')
    (hCovers :
      Covers
        (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg'))
        target) :
    G.N.CoverableFrom
      (G.encCTM cfg)
      (State.embed G.ideal target) := by
  refine G.coverable_of_ctm_step_covers h ?_
  intro species
  by_cases hImage : exists idealSpecies, G.ideal idealSpecies = species
  · rcases hImage with ⟨idealSpecies, rfl⟩
    simpa [State.embed_apply_of_injective
      (e := G.ideal) G.ideal_injective target idealSpecies] using
      hCovers idealSpecies
  · have hzero :
        State.embed G.ideal target species = 0 :=
      State.embed_eq_zero_of_not_exists
        (e := G.ideal) (z := target) (t := species) hImage
    simp [hzero]

theorem ideal_coverable_of_ctm_step_of_le
    (G : ConcreteFourPhaseModule.{u, v, w} (s := s) M)
    {cfg cfg' : Cfg Q Bool s}
    {target : State (FourPhaseSpecies Q)}
    (h : M.step? cfg = some cfg')
    (hTarget :
      forall species,
        target species <=
          FourPhaseEncoding.enc (MicroCfg.ofCTM cfg') species) :
    G.N.CoverableFrom
      (G.encCTM cfg)
      (State.embed G.ideal target) :=
  G.ideal_coverable_of_ctm_step_covers h hTarget

theorem ideal_coverableFrom_of_ctm_step_covers
    (G : ConcreteFourPhaseModule.{u, v, w} (s := s) M)
    {cfg cfg' : Cfg Q Bool s}
    {target : State (FourPhaseSpecies Q)}
    (h : M.step? cfg = some cfg')
    (hCovers :
      Covers
        (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg'))
        target) :
    G.N.CoverableFrom
      (G.encCTM cfg)
      (State.embed G.ideal target) :=
  G.ideal_coverable_of_ctm_step_covers h hCovers

theorem ideal_coverableFrom_of_ctm_step_of_le
    (G : ConcreteFourPhaseModule.{u, v, w} (s := s) M)
    {cfg cfg' : Cfg Q Bool s}
    {target : State (FourPhaseSpecies Q)}
    (h : M.step? cfg = some cfg')
    (hTarget :
      forall species,
        target species <=
          FourPhaseEncoding.enc (MicroCfg.ofCTM cfg') species) :
    G.N.CoverableFrom
      (G.encCTM cfg)
      (State.embed G.ideal target) :=
  G.ideal_coverable_of_ctm_step_of_le h hTarget

theorem ideal_speciesCoverableFrom_of_ctm_step
    (G : ConcreteFourPhaseModule.{u, v, w} (s := s) M)
    {cfg cfg' : Cfg Q Bool s}
    {species : FourPhaseSpecies Q} {amount : Nat}
    (h : M.step? cfg = some cfg')
    (hamount :
      amount <= FourPhaseEncoding.enc (MicroCfg.ofCTM cfg') species) :
    G.N.SpeciesCoverableFrom
      (G.encCTM cfg) (G.ideal species) amount := by
  have hamount' :
      amount <= G.encCTM cfg' (G.ideal species) := by
    simpa [encCTM, encMicro] using
      (by
        rw [G.enc_ideal (MicroCfg.ofCTM cfg') species]
        exact hamount)
  exact G.speciesCoverableFrom_of_ctm_step_coord h hamount'

theorem ideal_speciesCoverableFrom_one_of_ctm_step_pos
    (G : ConcreteFourPhaseModule.{u, v, w} (s := s) M)
    {cfg cfg' : Cfg Q Bool s}
    {species : FourPhaseSpecies Q}
    (h : M.step? cfg = some cfg')
    (hpos :
      0 < FourPhaseEncoding.enc (MicroCfg.ofCTM cfg') species) :
    G.N.SpeciesCoverableFrom (G.encCTM cfg) (G.ideal species) := by
  have hpos' : 0 < G.encCTM cfg' (G.ideal species) := by
    simpa [encCTM, encMicro] using
      (by
        rw [G.enc_ideal (MicroCfg.ofCTM cfg') species]
        exact hpos)
  exact G.speciesCoverableFrom_one_of_ctm_step_pos h hpos'

theorem ideal_tape_speciesCoverableFrom_of_ctm_step
    (G : ConcreteFourPhaseModule.{u, v, w} (s := s) M)
    {cfg cfg' : Cfg Q Bool s}
    (h : M.step? cfg = some cfg') :
    G.N.SpeciesCoverableFrom
      (G.encCTM cfg)
      (G.ideal FourPhaseSpecies.tape)
      (Encoding.base3Val cfg'.tape) :=
  G.ideal_speciesCoverableFrom_of_ctm_step h
    (by simp [MicroCfg.ofCTM])

theorem ideal_tapeBar_speciesCoverableFrom_of_ctm_step
    (G : ConcreteFourPhaseModule.{u, v, w} (s := s) M)
    {cfg cfg' : Cfg Q Bool s}
    (h : M.step? cfg = some cfg') :
    G.N.SpeciesCoverableFrom
      (G.encCTM cfg)
      (G.ideal FourPhaseSpecies.tapeBar)
      (FourPhaseEncoding.maxTape s - Encoding.base3Val cfg'.tape) :=
  G.ideal_speciesCoverableFrom_of_ctm_step h
    (by simp [MicroCfg.ofCTM])

theorem boundedIntendedSchedule_firingCount_le_of_ctm_steps
    (G : ConcreteFourPhaseModule.{u, v, w} (s := s) M)
    {n : Nat} {cfg cfg' : Cfg Q Bool s}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg') :
    (G.boundedIntendedSchedule_of_ctm_steps h).firingCount <=
      (G.step_len_bound * 4) * n :=
  Network.BoundedIntendedSchedule.firingCount_le_bound
    (G.boundedIntendedSchedule_of_ctm_steps h)

theorem boundedFiringCount_le_of_ctm_steps
    (G : ConcreteFourPhaseModule.{u, v, w} (s := s) M)
    {n : Nat} {cfg cfg' : Cfg Q Bool s}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg') :
    (G.boundedIntendedSchedule_of_ctm_steps h).firingCount <=
      (G.step_len_bound * 4) * n :=
  G.boundedIntendedSchedule_firingCount_le_of_ctm_steps h

theorem state_after_ctm_steps_of_firesListAt
    (G : ConcreteFourPhaseModule.{u, v, w} (s := s) M)
    {n : Nat} {cfg cfg' : Cfg Q Bool s}
    {path : G.N.Path} {t : Nat}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg')
    (hstate : path.state t = G.encCTM cfg)
    (hfires :
      path.FiresListAt t (G.intendedSchedule_of_ctm_steps h).schedule) :
    path.state
        (t + (G.intendedSchedule_of_ctm_steps h).firingCount) =
      G.encCTM cfg' := by
  simpa [Network.IntendedSchedule.firingCount] using
    path.state_after_intended_of_firesListAt
      (G.intendedSchedule_of_ctm_steps h)
      hstate
      hfires

theorem state_after_ctm_steps_of_intendedWinsRaceAt
    (G : ConcreteFourPhaseModule.{u, v, w} (s := s) M)
    {n : Nat} {cfg cfg' : Cfg Q Bool s}
    {path : G.N.Path} {Bad : G.N.BadIndexSet} {t : Nat}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg')
    (hwin :
      path.IntendedWinsRaceAt Bad t
        (G.intendedSchedule_of_ctm_steps h)) :
    path.state
        (t + (G.intendedSchedule_of_ctm_steps h).firingCount) =
      G.encCTM cfg' := by
  simpa [Network.IntendedSchedule.firingCount] using
    path.state_after_intendedWinsRaceAt Bad
      (G.intendedSchedule_of_ctm_steps h)
      hwin

theorem state_after_bounded_ctm_steps_of_intendedWinsRaceAt
    (G : ConcreteFourPhaseModule.{u, v, w} (s := s) M)
    {n : Nat} {cfg cfg' : Cfg Q Bool s}
    {path : G.N.Path} {Bad : G.N.BadIndexSet} {t : Nat}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg')
    (hwin :
      path.IntendedWinsRaceAt Bad t
        (G.boundedIntendedSchedule_of_ctm_steps h).toIntendedSchedule) :
    path.state
        (t + (G.boundedIntendedSchedule_of_ctm_steps h).firingCount) =
      G.encCTM cfg' :=
  path.state_after_boundedIntendedWinsRaceAt Bad
    (G.boundedIntendedSchedule_of_ctm_steps h)
    hwin

theorem state_after_bounded_ctm_steps_of_firesListAt
    (G : ConcreteFourPhaseModule.{u, v, w} (s := s) M)
    {n : Nat} {cfg cfg' : Cfg Q Bool s}
    {path : G.N.Path} {t : Nat}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg')
    (hstate : path.state t = G.encCTM cfg)
    (hfires :
      path.FiresListAt t
        (G.boundedIntendedSchedule_of_ctm_steps h).schedule) :
    path.state
        (t + (G.boundedIntendedSchedule_of_ctm_steps h).firingCount) =
      G.encCTM cfg' :=
  path.state_after_boundedIntended_of_firesListAt
    (G.boundedIntendedSchedule_of_ctm_steps h)
    hstate
    hfires

theorem intended_reaches_of_ctm_steps
    (G : ConcreteFourPhaseModule.{u, v, w} (s := s) M)
    {n : Nat} {cfg cfg' : Cfg Q Bool s}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg') :
    G.N.Reaches (G.encCTM cfg) (G.encCTM cfg') :=
  (G.intendedSchedule_of_ctm_steps h).reaches

theorem boundedIntendedSchedule_reaches_of_ctm_steps
    (G : ConcreteFourPhaseModule.{u, v, w} (s := s) M)
    {n : Nat} {cfg cfg' : Cfg Q Bool s}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg') :
    G.N.Reaches (G.encCTM cfg) (G.encCTM cfg') :=
  (G.boundedIntendedSchedule_of_ctm_steps h).reaches

theorem reaches_of_ctm_steps
    (G : ConcreteFourPhaseModule.{u, v, w} (s := s) M)
    {n : Nat} {cfg cfg' : Cfg Q Bool s}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg') :
    G.N.Reaches (G.encCTM cfg) (G.encCTM cfg') := by
  simpa [encCTM, encMicro] using
    InvariantStepwiseRealization.reaches_of_kStepSim_steps
      (sim := fourPhaseKStepSim (s := s) M)
      G.toInvariantStepwiseRealization
      (MicroCfg.ofCTM_gadgetWF cfg)
      h

theorem coverable_of_ctm_steps_covers
    (G : ConcreteFourPhaseModule.{u, v, w} (s := s) M)
    {n : Nat} {cfg cfg' : Cfg Q Bool s}
    {target : State G.CSp}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg')
    (hCovers : Covers (G.encCTM cfg') target) :
    G.N.CoverableFrom (G.encCTM cfg) target :=
  Network.coverable_of_reaches_of_covers
    (G.reaches_of_ctm_steps h)
    hCovers

theorem coverable_of_ctm_steps_of_le
    (G : ConcreteFourPhaseModule.{u, v, w} (s := s) M)
    {n : Nat} {cfg cfg' : Cfg Q Bool s}
    {target : State G.CSp}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg')
    (hTarget : forall species, target species <= G.encCTM cfg' species) :
    G.N.CoverableFrom (G.encCTM cfg) target :=
  G.coverable_of_ctm_steps_covers h hTarget

theorem coverableFrom_of_ctm_steps_covers
    (G : ConcreteFourPhaseModule.{u, v, w} (s := s) M)
    {n : Nat} {cfg cfg' : Cfg Q Bool s}
    {target : State G.CSp}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg')
    (hCovers : Covers (G.encCTM cfg') target) :
    G.N.CoverableFrom (G.encCTM cfg) target :=
  G.coverable_of_ctm_steps_covers h hCovers

theorem coverableFrom_of_ctm_steps_of_le
    (G : ConcreteFourPhaseModule.{u, v, w} (s := s) M)
    {n : Nat} {cfg cfg' : Cfg Q Bool s}
    {target : State G.CSp}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg')
    (hTarget : forall species, target species <= G.encCTM cfg' species) :
    G.N.CoverableFrom (G.encCTM cfg) target :=
  G.coverable_of_ctm_steps_of_le h hTarget

theorem ideal_coverable_of_ctm_steps_covers
    (G : ConcreteFourPhaseModule.{u, v, w} (s := s) M)
    {n : Nat} {cfg cfg' : Cfg Q Bool s}
    {target : State (FourPhaseSpecies Q)}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg')
    (hCovers :
      Covers
        (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg'))
        target) :
    G.N.CoverableFrom
      (G.encCTM cfg)
      (State.embed G.ideal target) := by
  refine G.coverable_of_ctm_steps_covers h ?_
  intro species
  by_cases hImage : exists idealSpecies, G.ideal idealSpecies = species
  · rcases hImage with ⟨idealSpecies, rfl⟩
    simpa [State.embed_apply_of_injective
      (e := G.ideal) G.ideal_injective target idealSpecies] using
      hCovers idealSpecies
  · have hzero :
        State.embed G.ideal target species = 0 :=
      State.embed_eq_zero_of_not_exists
        (e := G.ideal) (z := target) (t := species) hImage
    simp [hzero]

theorem ideal_coverable_of_ctm_steps_of_le
    (G : ConcreteFourPhaseModule.{u, v, w} (s := s) M)
    {n : Nat} {cfg cfg' : Cfg Q Bool s}
    {target : State (FourPhaseSpecies Q)}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg')
    (hTarget :
      forall species,
        target species <=
          FourPhaseEncoding.enc (MicroCfg.ofCTM cfg') species) :
    G.N.CoverableFrom
      (G.encCTM cfg)
      (State.embed G.ideal target) :=
  G.ideal_coverable_of_ctm_steps_covers h hTarget

theorem ideal_coverableFrom_of_ctm_steps_covers
    (G : ConcreteFourPhaseModule.{u, v, w} (s := s) M)
    {n : Nat} {cfg cfg' : Cfg Q Bool s}
    {target : State (FourPhaseSpecies Q)}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg')
    (hCovers :
      Covers
        (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg'))
        target) :
    G.N.CoverableFrom
      (G.encCTM cfg)
      (State.embed G.ideal target) :=
  G.ideal_coverable_of_ctm_steps_covers h hCovers

theorem ideal_coverableFrom_of_ctm_steps_of_le
    (G : ConcreteFourPhaseModule.{u, v, w} (s := s) M)
    {n : Nat} {cfg cfg' : Cfg Q Bool s}
    {target : State (FourPhaseSpecies Q)}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg')
    (hTarget :
      forall species,
        target species <=
          FourPhaseEncoding.enc (MicroCfg.ofCTM cfg') species) :
    G.N.CoverableFrom
      (G.encCTM cfg)
      (State.embed G.ideal target) :=
  G.ideal_coverable_of_ctm_steps_of_le h hTarget

theorem speciesCoverableFrom_of_ctm_steps_coord
    (G : ConcreteFourPhaseModule.{u, v, w} (s := s) M)
    {n : Nat} {cfg cfg' : Cfg Q Bool s}
    {species : G.CSp} {amount : Nat}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg')
    (hamount : amount <= G.encCTM cfg' species) :
    G.N.SpeciesCoverableFrom (G.encCTM cfg) species amount :=
  Network.speciesCoverableFrom_of_reaches_coord
    (G.reaches_of_ctm_steps h)
    hamount

theorem speciesCoverableFrom_one_of_ctm_steps_pos
    (G : ConcreteFourPhaseModule.{u, v, w} (s := s) M)
    {n : Nat} {cfg cfg' : Cfg Q Bool s}
    {species : G.CSp}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg')
    (hpos : 0 < G.encCTM cfg' species) :
    G.N.SpeciesCoverableFrom (G.encCTM cfg) species :=
  Network.speciesCoverableFrom_one_of_reaches_pos
    (G.reaches_of_ctm_steps h)
    hpos

theorem ideal_speciesCoverableFrom_of_ctm_steps
    (G : ConcreteFourPhaseModule.{u, v, w} (s := s) M)
    {n : Nat} {cfg cfg' : Cfg Q Bool s}
    {species : FourPhaseSpecies Q} {amount : Nat}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg')
    (hamount :
      amount <= FourPhaseEncoding.enc (MicroCfg.ofCTM cfg') species) :
    G.N.SpeciesCoverableFrom
      (G.encCTM cfg) (G.ideal species) amount := by
  have hamount' :
      amount <= G.encCTM cfg' (G.ideal species) := by
    simpa [encCTM, encMicro] using
      (by
        rw [G.enc_ideal (MicroCfg.ofCTM cfg') species]
        exact hamount)
  exact G.speciesCoverableFrom_of_ctm_steps_coord h hamount'

theorem ideal_speciesCoverableFrom_one_of_ctm_steps_pos
    (G : ConcreteFourPhaseModule.{u, v, w} (s := s) M)
    {n : Nat} {cfg cfg' : Cfg Q Bool s}
    {species : FourPhaseSpecies Q}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg')
    (hpos :
      0 < FourPhaseEncoding.enc (MicroCfg.ofCTM cfg') species) :
    G.N.SpeciesCoverableFrom (G.encCTM cfg) (G.ideal species) := by
  have hpos' : 0 < G.encCTM cfg' (G.ideal species) := by
    simpa [encCTM, encMicro] using
      (by
        rw [G.enc_ideal (MicroCfg.ofCTM cfg') species]
        exact hpos)
  exact G.speciesCoverableFrom_one_of_ctm_steps_pos h hpos'

theorem ideal_tape_speciesCoverableFrom_of_ctm_steps
    (G : ConcreteFourPhaseModule.{u, v, w} (s := s) M)
    {n : Nat} {cfg cfg' : Cfg Q Bool s}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg') :
    G.N.SpeciesCoverableFrom
      (G.encCTM cfg)
      (G.ideal FourPhaseSpecies.tape)
      (Encoding.base3Val cfg'.tape) :=
  G.ideal_speciesCoverableFrom_of_ctm_steps h
    (by simp [MicroCfg.ofCTM])

theorem ideal_tapeBar_speciesCoverableFrom_of_ctm_steps
    (G : ConcreteFourPhaseModule.{u, v, w} (s := s) M)
    {n : Nat} {cfg cfg' : Cfg Q Bool s}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg') :
    G.N.SpeciesCoverableFrom
      (G.encCTM cfg)
      (G.ideal FourPhaseSpecies.tapeBar)
      (FourPhaseEncoding.maxTape s - Encoding.base3Val cfg'.tape) :=
  G.ideal_speciesCoverableFrom_of_ctm_steps h
    (by simp [MicroCfg.ofCTM])

end ConcreteFourPhaseModule

namespace FourPhaseConcrete

namespace ConcreteFourPhaseExpansionFamily

variable {Q : Type u} [Fintype Q] [DecidableEq Q] {s : Nat}
variable {M : Binary Q}

def toConcreteFourPhaseModule
    (F : ConcreteFourPhaseExpansionFamily.{u, v, w} (s := s) M) :
    ConcreteFourPhaseModule.{u, v, w} (s := s) M where
  CSp := F.CSp
  instFintype := F.instFintype
  instDecidableEq := F.instDecidableEq
  N := F.network
  enc := F.enc
  ideal := F.ideal
  ideal_injective := F.ideal_injective
  enc_ideal := F.enc_ideal
  step_len_bound := F.step_len_bound
  allAtMostBimolecularInput := F.network_allAtMostBimolecularInput
  hasPositiveRates := F.network_hasPositiveRates
  step_exec_bounded := by
    intro c c' hc hstep
    cases hphase : c.state.phase with
    | read =>
        rcases F.read.exec_of_good_phase_step hc hphase hstep with
          ⟨is, hExec, hLen⟩
        refine ⟨is.map (fun i => Sum.inl (Sum.inl i)),
          phaseParallel4_exec_read hExec, ?_⟩
        simp [List.length_map, step_len_bound]
        omega
    | erase =>
        rcases F.erase.exec_of_good_phase_step hc hphase hstep with
          ⟨is, hExec, hLen⟩
        refine ⟨is.map (fun i => Sum.inl (Sum.inr i)),
          phaseParallel4_exec_erase hExec, ?_⟩
        simp [List.length_map, step_len_bound]
        omega
    | shift =>
        rcases F.shift.exec_of_good_phase_step hc hphase hstep with
          ⟨is, hExec, hLen⟩
        refine ⟨is.map (fun i => Sum.inr (Sum.inl i)),
          phaseParallel4_exec_shift hExec, ?_⟩
        simp [List.length_map, step_len_bound]
        omega
    | write =>
        rcases F.write.exec_of_good_phase_step hc hphase hstep with
          ⟨is, hExec, hLen⟩
        refine ⟨is.map (fun i => Sum.inr (Sum.inr i)),
          phaseParallel4_exec_write hExec, ?_⟩
        simp [List.length_map, step_len_bound]
        omega

end ConcreteFourPhaseExpansionFamily

structure FootprintedConcretePhaseExpansion
    {Q : Type u} [Fintype Q] [DecidableEq Q] {s : Nat}
    {CSp : Type v} [Fintype CSp] [DecidableEq CSp]
    (M : Binary Q)
    (phase : Phase4)
    (enc : MicroCfg Q s -> State CSp)
    (ideal : FourPhaseSpecies Q -> CSp) where
  N : Network.{v, w} CSp
  step_len_bound : Nat
  allAtMostBimolecularInput : N.allAtMostBimolecularInput
  hasPositiveRates : N.hasPositiveRates
  auxFootprint : MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop
  auxFootprint_disjoint_ideal :
    forall {c c' : MicroCfg Q s} (species : FourPhaseSpecies Q),
      Not (auxFootprint c c' (ideal species))
  step_schedule :
    forall {c c' : MicroCfg Q s},
      GadgetMicroCfgWF c ->
      c.state.phase = phase ->
      phaseStep? (s := s) M c = some c' ->
        ConcreteGoodStepSchedule
          N enc
          (ConcreteLocalFootprint ideal auxFootprint)
          step_len_bound c c'

structure FootprintedConcreteFourPhaseExpansionFamily
    {Q : Type u} [Fintype Q] [DecidableEq Q] {s : Nat}
    (M : Binary Q) where
  CSp : Type v
  instFintype : Fintype CSp
  instDecidableEq : DecidableEq CSp
  enc : MicroCfg Q s -> State CSp
  ideal : FourPhaseSpecies Q -> CSp
  ideal_injective : Function.Injective ideal
  enc_ideal :
    forall (c : MicroCfg Q s) (species : FourPhaseSpecies Q),
      enc c (ideal species) = FourPhaseEncoding.enc c species
  read :
    FootprintedConcretePhaseExpansion.{u, v, w}
      (s := s) (CSp := CSp) M Phase4.read enc ideal
  erase :
    FootprintedConcretePhaseExpansion.{u, v, w}
      (s := s) (CSp := CSp) M Phase4.erase enc ideal
  shift :
    FootprintedConcretePhaseExpansion.{u, v, w}
      (s := s) (CSp := CSp) M Phase4.shift enc ideal
  write :
    FootprintedConcretePhaseExpansion.{u, v, w}
      (s := s) (CSp := CSp) M Phase4.write enc ideal

namespace FootprintedConcretePhaseExpansion

variable {Q : Type u} [Fintype Q] [DecidableEq Q] {s : Nat}
variable {CSp : Type v} [Fintype CSp] [DecidableEq CSp]
variable {M : Binary Q} {phase : Phase4}
variable {enc : MicroCfg Q s -> State CSp}
variable {ideal : FourPhaseSpecies Q -> CSp}

def toConcretePhaseExpansion
    (G :
      FootprintedConcretePhaseExpansion.{u, v, w}
        (s := s) (CSp := CSp) M phase enc ideal) :
    ConcretePhaseExpansion.{u, v, w}
      (s := s) (CSp := CSp) M phase enc where
  N := G.N
  step_len_bound := G.step_len_bound
  allAtMostBimolecularInput := G.allAtMostBimolecularInput
  hasPositiveRates := G.hasPositiveRates
  exec_of_good_phase_step := by
    intro c c' hc hphase hstep
    let Sched := G.step_schedule hc hphase hstep
    exact ⟨Sched.schedule, Sched.exec, Sched.length_le⟩

def intendedSchedule_of_good_phase_step
    (G :
      FootprintedConcretePhaseExpansion.{u, v, w}
        (s := s) (CSp := CSp) M phase enc ideal)
    {c c' : MicroCfg Q s}
    (hc : GadgetMicroCfgWF c)
    (hphase : c.state.phase = phase)
    (hstep : phaseStep? (s := s) M c = some c') :
    G.N.IntendedSchedule (enc c) (enc c') :=
  (G.step_schedule hc hphase hstep).toIntendedSchedule

theorem exec_of_intendedSchedule_of_good_phase_step
    (G :
      FootprintedConcretePhaseExpansion.{u, v, w}
        (s := s) (CSp := CSp) M phase enc ideal)
    {c c' : MicroCfg Q s}
    (hc : GadgetMicroCfgWF c)
    (hphase : c.state.phase = phase)
    (hstep : phaseStep? (s := s) M c = some c') :
    G.N.Exec (enc c) (enc c')
      (G.intendedSchedule_of_good_phase_step hc hphase hstep).schedule :=
  (G.intendedSchedule_of_good_phase_step hc hphase hstep).exec

def boundedIntendedSchedule_of_good_phase_step
    (G :
      FootprintedConcretePhaseExpansion.{u, v, w}
        (s := s) (CSp := CSp) M phase enc ideal)
    {c c' : MicroCfg Q s}
    (hc : GadgetMicroCfgWF c)
    (hphase : c.state.phase = phase)
    (hstep : phaseStep? (s := s) M c = some c') :
    G.N.BoundedIntendedSchedule G.step_len_bound (enc c) (enc c') :=
  (G.step_schedule hc hphase hstep).toBoundedIntendedSchedule

theorem exec_of_boundedIntendedSchedule_of_good_phase_step
    (G :
      FootprintedConcretePhaseExpansion.{u, v, w}
        (s := s) (CSp := CSp) M phase enc ideal)
    {c c' : MicroCfg Q s}
    (hc : GadgetMicroCfgWF c)
    (hphase : c.state.phase = phase)
    (hstep : phaseStep? (s := s) M c = some c') :
    G.N.Exec (enc c) (enc c')
      (G.boundedIntendedSchedule_of_good_phase_step
        hc hphase hstep).schedule :=
  (G.boundedIntendedSchedule_of_good_phase_step hc hphase hstep).exec

theorem scheduleFootprintWithin_of_good_phase_step
    (G :
      FootprintedConcretePhaseExpansion.{u, v, w}
        (s := s) (CSp := CSp) M phase enc ideal)
    {c c' : MicroCfg Q s}
    (hc : GadgetMicroCfgWF c)
    (hphase : c.state.phase = phase)
    (hstep : phaseStep? (s := s) M c = some c') :
    G.N.ScheduleFootprintWithin
      (G.intendedSchedule_of_good_phase_step hc hphase hstep).schedule
      (ConcreteLocalFootprint ideal G.auxFootprint c c') := by
  simpa [intendedSchedule_of_good_phase_step] using
    (G.step_schedule hc hphase hstep).footprint

theorem boundedIntendedSchedule_firingCount_le_of_good_phase_step
    (G :
      FootprintedConcretePhaseExpansion.{u, v, w}
        (s := s) (CSp := CSp) M phase enc ideal)
    {c c' : MicroCfg Q s}
    (hc : GadgetMicroCfgWF c)
    (hphase : c.state.phase = phase)
    (hstep : phaseStep? (s := s) M c = some c') :
    (G.boundedIntendedSchedule_of_good_phase_step
      hc hphase hstep).firingCount <= G.step_len_bound :=
  Network.BoundedIntendedSchedule.firingCount_le_bound
    (G.boundedIntendedSchedule_of_good_phase_step hc hphase hstep)

theorem intended_reaches_of_good_phase_step
    (G :
      FootprintedConcretePhaseExpansion.{u, v, w}
        (s := s) (CSp := CSp) M phase enc ideal)
    {c c' : MicroCfg Q s}
    (hc : GadgetMicroCfgWF c)
    (hphase : c.state.phase = phase)
    (hstep : phaseStep? (s := s) M c = some c') :
    G.N.Reaches (enc c) (enc c') :=
  (G.intendedSchedule_of_good_phase_step hc hphase hstep).reaches

theorem boundedIntendedSchedule_reaches_of_good_phase_step
    (G :
      FootprintedConcretePhaseExpansion.{u, v, w}
        (s := s) (CSp := CSp) M phase enc ideal)
    {c c' : MicroCfg Q s}
    (hc : GadgetMicroCfgWF c)
    (hphase : c.state.phase = phase)
    (hstep : phaseStep? (s := s) M c = some c') :
    G.N.Reaches (enc c) (enc c') :=
  (G.boundedIntendedSchedule_of_good_phase_step hc hphase hstep).reaches

theorem reaches_of_good_phase_step
    (G :
      FootprintedConcretePhaseExpansion.{u, v, w}
        (s := s) (CSp := CSp) M phase enc ideal)
    {c c' : MicroCfg Q s}
    (hc : GadgetMicroCfgWF c)
    (hphase : c.state.phase = phase)
    (hstep : phaseStep? (s := s) M c = some c') :
    G.N.Reaches (enc c) (enc c') :=
  G.intended_reaches_of_good_phase_step hc hphase hstep

end FootprintedConcretePhaseExpansion

namespace FootprintedConcreteFourPhaseExpansionFamily

attribute [instance] instFintype instDecidableEq

variable {Q : Type u} [Fintype Q] [DecidableEq Q] {s : Nat}
variable {M : Binary Q}

def step_len_bound
    (F : FootprintedConcreteFourPhaseExpansionFamily.{u, v, w} (s := s) M) :
    Nat :=
  F.read.step_len_bound + F.erase.step_len_bound +
    F.shift.step_len_bound + F.write.step_len_bound

def network
    (F : FootprintedConcreteFourPhaseExpansionFamily.{u, v, w} (s := s) M) :
    Network.{v, w} F.CSp :=
  phaseParallel4 F.read.N F.erase.N F.shift.N F.write.N

theorem network_allAtMostBimolecularInput
    (F : FootprintedConcreteFourPhaseExpansionFamily.{u, v, w} (s := s) M) :
    F.network.allAtMostBimolecularInput := by
  dsimp [network]
  exact phaseParallel4_allAtMostBimolecularInput
    F.read.allAtMostBimolecularInput
    F.erase.allAtMostBimolecularInput
    F.shift.allAtMostBimolecularInput
    F.write.allAtMostBimolecularInput

theorem network_hasPositiveRates
    (F : FootprintedConcreteFourPhaseExpansionFamily.{u, v, w} (s := s) M) :
    F.network.hasPositiveRates := by
  dsimp [network]
  exact phaseParallel4_hasPositiveRates
    F.read.hasPositiveRates
    F.erase.hasPositiveRates
    F.shift.hasPositiveRates
    F.write.hasPositiveRates

def auxFootprint
    (F : FootprintedConcreteFourPhaseExpansionFamily.{u, v, w} (s := s) M)
    (c c' : MicroCfg Q s) : F.CSp -> Prop :=
  match c.state.phase with
  | Phase4.read => F.read.auxFootprint c c'
  | Phase4.erase => F.erase.auxFootprint c c'
  | Phase4.shift => F.shift.auxFootprint c c'
  | Phase4.write => F.write.auxFootprint c c'

def toConcreteFourPhaseExpansionFamily
    (F : FootprintedConcreteFourPhaseExpansionFamily.{u, v, w} (s := s) M) :
    ConcreteFourPhaseExpansionFamily.{u, v, w} (s := s) M where
  CSp := F.CSp
  instFintype := F.instFintype
  instDecidableEq := F.instDecidableEq
  enc := F.enc
  ideal := F.ideal
  ideal_injective := F.ideal_injective
  enc_ideal := F.enc_ideal
  read := F.read.toConcretePhaseExpansion
  erase := F.erase.toConcretePhaseExpansion
  shift := F.shift.toConcretePhaseExpansion
  write := F.write.toConcretePhaseExpansion

end FootprintedConcreteFourPhaseExpansionFamily

/--
Footprinted deterministic interface for a concrete four-phase network.

The footprint is attached only to the chosen scheduled execution for a good
ideal step. This does not assert that arbitrary concrete trajectories stay in
the footprint.
-/
structure FootprintedConcreteFourPhaseModule
    {Q : Type u} [Fintype Q] [DecidableEq Q] {s : Nat}
    (M : Binary Q) where
  CSp : Type v
  instFintype : Fintype CSp
  instDecidableEq : DecidableEq CSp
  N : Network.{v, w} CSp
  enc : MicroCfg Q s -> State CSp
  ideal : FourPhaseSpecies Q -> CSp
  ideal_injective : Function.Injective ideal
  enc_ideal :
    forall (c : MicroCfg Q s) (species : FourPhaseSpecies Q),
      enc c (ideal species) = FourPhaseEncoding.enc c species
  step_len_bound : Nat
  allAtMostBimolecularInput : N.allAtMostBimolecularInput
  hasPositiveRates : N.hasPositiveRates
  auxFootprint : MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop
  auxFootprint_disjoint_ideal :
    forall {c c' : MicroCfg Q s} (species : FourPhaseSpecies Q),
      Not (auxFootprint c c' (ideal species))
  step_schedule :
    forall {c c' : MicroCfg Q s},
      GadgetMicroCfgWF c ->
      phaseStep? (s := s) M c = some c' ->
        ConcreteGoodStepSchedule
          N enc
          (ConcreteLocalFootprint ideal auxFootprint)
          step_len_bound c c'

namespace FootprintedConcreteFourPhaseModule

attribute [instance] instFintype instDecidableEq

variable {Q : Type u} [Fintype Q] [DecidableEq Q] {s : Nat}
variable {M : Binary Q}

def toConcreteFourPhaseModule
    (G : FootprintedConcreteFourPhaseModule.{u, v, w} (s := s) M) :
    ConcreteFourPhaseModule.{u, v, w} (s := s) M where
  CSp := G.CSp
  instFintype := G.instFintype
  instDecidableEq := G.instDecidableEq
  N := G.N
  enc := G.enc
  ideal := G.ideal
  ideal_injective := G.ideal_injective
  enc_ideal := G.enc_ideal
  step_len_bound := G.step_len_bound
  allAtMostBimolecularInput := G.allAtMostBimolecularInput
  hasPositiveRates := G.hasPositiveRates
  step_exec_bounded := by
    intro c c' hc hstep
    let Sched := G.step_schedule hc hstep
    exact ⟨Sched.schedule, Sched.exec, Sched.length_le⟩

theorem execFootprintWithin_of_step_schedule
    (G : FootprintedConcreteFourPhaseModule.{u, v, w} (s := s) M)
    {c c' : MicroCfg Q s}
    (hc : GadgetMicroCfgWF c)
    (hstep : phaseStep? (s := s) M c = some c') :
    G.N.ExecFootprintWithin
      (ConcreteLocalFootprint G.ideal G.auxFootprint c c')
      (G.enc c) (G.enc c') := by
  let Sched := G.step_schedule hc hstep
  exact Network.ExecFootprintWithin.of_exec_scheduleFootprintWithin
    Sched.exec Sched.footprint

theorem agreesOutside_of_step_schedule
    (G : FootprintedConcreteFourPhaseModule.{u, v, w} (s := s) M)
    {c c' : MicroCfg Q s}
    (hc : GadgetMicroCfgWF c)
    (hstep : phaseStep? (s := s) M c = some c') :
    State.AgreesOutside
      (ConcreteLocalFootprint G.ideal G.auxFootprint c c')
      (G.enc c) (G.enc c') :=
  Network.ExecFootprintWithin.agreesOutside
    (G.execFootprintWithin_of_step_schedule hc hstep)

def intendedSchedule_of_step_schedule
    (G : FootprintedConcreteFourPhaseModule.{u, v, w} (s := s) M)
    {c c' : MicroCfg Q s}
    (hc : GadgetMicroCfgWF c)
    (hstep : phaseStep? (s := s) M c = some c') :
    G.N.IntendedSchedule (G.enc c) (G.enc c') :=
  (G.step_schedule hc hstep).toIntendedSchedule

@[simp]
theorem intendedSchedule_of_step_schedule_schedule
    (G : FootprintedConcreteFourPhaseModule.{u, v, w} (s := s) M)
    {c c' : MicroCfg Q s}
    (hc : GadgetMicroCfgWF c)
    (hstep : phaseStep? (s := s) M c = some c') :
    (G.intendedSchedule_of_step_schedule hc hstep).schedule =
      (G.step_schedule hc hstep).schedule := by
  rfl

theorem scheduleFootprintWithin_of_step_schedule
    (G : FootprintedConcreteFourPhaseModule.{u, v, w} (s := s) M)
    {c c' : MicroCfg Q s}
    (hc : GadgetMicroCfgWF c)
    (hstep : phaseStep? (s := s) M c = some c') :
    G.N.ScheduleFootprintWithin
      (G.intendedSchedule_of_step_schedule hc hstep).schedule
      (ConcreteLocalFootprint G.ideal G.auxFootprint c c') := by
  simpa [intendedSchedule_of_step_schedule] using
    (G.step_schedule hc hstep).footprint

theorem exec_of_intendedSchedule_of_step_schedule
    (G : FootprintedConcreteFourPhaseModule.{u, v, w} (s := s) M)
    {c c' : MicroCfg Q s}
    (hc : GadgetMicroCfgWF c)
    (hstep : phaseStep? (s := s) M c = some c') :
    G.N.Exec (G.enc c) (G.enc c')
      (G.intendedSchedule_of_step_schedule hc hstep).schedule :=
  (G.intendedSchedule_of_step_schedule hc hstep).exec

def boundedIntendedSchedule_of_step_schedule
    (G : FootprintedConcreteFourPhaseModule.{u, v, w} (s := s) M)
    {c c' : MicroCfg Q s}
    (hc : GadgetMicroCfgWF c)
    (hstep : phaseStep? (s := s) M c = some c') :
    G.N.BoundedIntendedSchedule
      G.step_len_bound (G.enc c) (G.enc c') :=
  (G.step_schedule hc hstep).toBoundedIntendedSchedule

@[simp]
theorem boundedIntendedSchedule_of_step_schedule_schedule
    (G : FootprintedConcreteFourPhaseModule.{u, v, w} (s := s) M)
    {c c' : MicroCfg Q s}
    (hc : GadgetMicroCfgWF c)
    (hstep : phaseStep? (s := s) M c = some c') :
    (G.boundedIntendedSchedule_of_step_schedule hc hstep).schedule =
      (G.step_schedule hc hstep).schedule := by
  rfl

theorem exec_of_boundedIntendedSchedule_of_step_schedule
    (G : FootprintedConcreteFourPhaseModule.{u, v, w} (s := s) M)
    {c c' : MicroCfg Q s}
    (hc : GadgetMicroCfgWF c)
    (hstep : phaseStep? (s := s) M c = some c') :
    G.N.Exec (G.enc c) (G.enc c')
      (G.boundedIntendedSchedule_of_step_schedule hc hstep).schedule :=
  (G.boundedIntendedSchedule_of_step_schedule hc hstep).exec

theorem boundedIntendedSchedule_firingCount_le_of_step_schedule
    (G : FootprintedConcreteFourPhaseModule.{u, v, w} (s := s) M)
    {c c' : MicroCfg Q s}
    (hc : GadgetMicroCfgWF c)
    (hstep : phaseStep? (s := s) M c = some c') :
    (G.boundedIntendedSchedule_of_step_schedule hc hstep).firingCount <=
      G.step_len_bound :=
  Network.BoundedIntendedSchedule.firingCount_le_bound
    (G.boundedIntendedSchedule_of_step_schedule hc hstep)

theorem reaches_of_step_schedule
    (G : FootprintedConcreteFourPhaseModule.{u, v, w} (s := s) M)
    {c c' : MicroCfg Q s}
    (hc : GadgetMicroCfgWF c)
    (hstep : phaseStep? (s := s) M c = some c') :
    G.N.Reaches (G.enc c) (G.enc c') :=
  (G.step_schedule hc hstep).reaches

theorem coverable_of_step_schedule_covers
    (G : FootprintedConcreteFourPhaseModule.{u, v, w} (s := s) M)
    {c c' : MicroCfg Q s}
    {target : State G.CSp}
    (hc : GadgetMicroCfgWF c)
    (hstep : phaseStep? (s := s) M c = some c')
    (hCovers : Covers (G.enc c') target) :
    G.N.CoverableFrom (G.enc c) target :=
  Network.coverable_of_reaches_of_covers
    (G.reaches_of_step_schedule hc hstep)
    hCovers

theorem coverable_of_step_schedule_of_le
    (G : FootprintedConcreteFourPhaseModule.{u, v, w} (s := s) M)
    {c c' : MicroCfg Q s}
    {target : State G.CSp}
    (hc : GadgetMicroCfgWF c)
    (hstep : phaseStep? (s := s) M c = some c')
    (hTarget : forall species, target species <= G.enc c' species) :
    G.N.CoverableFrom (G.enc c) target :=
  G.coverable_of_step_schedule_covers hc hstep hTarget

theorem coverableFrom_of_step_schedule_covers
    (G : FootprintedConcreteFourPhaseModule.{u, v, w} (s := s) M)
    {c c' : MicroCfg Q s}
    {target : State G.CSp}
    (hc : GadgetMicroCfgWF c)
    (hstep : phaseStep? (s := s) M c = some c')
    (hCovers : Covers (G.enc c') target) :
    G.N.CoverableFrom (G.enc c) target :=
  G.coverable_of_step_schedule_covers hc hstep hCovers

theorem coverableFrom_of_step_schedule_of_le
    (G : FootprintedConcreteFourPhaseModule.{u, v, w} (s := s) M)
    {c c' : MicroCfg Q s}
    {target : State G.CSp}
    (hc : GadgetMicroCfgWF c)
    (hstep : phaseStep? (s := s) M c = some c')
    (hTarget : forall species, target species <= G.enc c' species) :
    G.N.CoverableFrom (G.enc c) target :=
  G.coverable_of_step_schedule_of_le hc hstep hTarget

theorem speciesCoverableFrom_of_step_schedule_coord
    (G : FootprintedConcreteFourPhaseModule.{u, v, w} (s := s) M)
    {c c' : MicroCfg Q s}
    {species : G.CSp} {amount : Nat}
    (hc : GadgetMicroCfgWF c)
    (hstep : phaseStep? (s := s) M c = some c')
    (hamount : amount <= G.enc c' species) :
    G.N.SpeciesCoverableFrom (G.enc c) species amount :=
  Network.speciesCoverableFrom_of_reaches_coord
    (G.reaches_of_step_schedule hc hstep)
    hamount

theorem speciesCoverableFrom_one_of_step_schedule_pos
    (G : FootprintedConcreteFourPhaseModule.{u, v, w} (s := s) M)
    {c c' : MicroCfg Q s}
    {species : G.CSp}
    (hc : GadgetMicroCfgWF c)
    (hstep : phaseStep? (s := s) M c = some c')
    (hpos : 0 < G.enc c' species) :
    G.N.SpeciesCoverableFrom (G.enc c) species :=
  Network.speciesCoverableFrom_one_of_reaches_pos
    (G.reaches_of_step_schedule hc hstep)
    hpos

theorem ideal_coverable_of_step_schedule_covers
    (G : FootprintedConcreteFourPhaseModule.{u, v, w} (s := s) M)
    {c c' : MicroCfg Q s}
    {target : State (FourPhaseSpecies Q)}
    (hc : GadgetMicroCfgWF c)
    (hstep : phaseStep? (s := s) M c = some c')
    (hCovers : Covers (FourPhaseEncoding.enc c') target) :
    G.N.CoverableFrom
      (G.enc c)
      (State.embed G.ideal target) := by
  refine G.coverable_of_step_schedule_covers hc hstep ?_
  intro species
  by_cases hImage : exists idealSpecies, G.ideal idealSpecies = species
  · rcases hImage with ⟨idealSpecies, rfl⟩
    simpa [
      State.embed_apply_of_injective
        (e := G.ideal) G.ideal_injective target idealSpecies,
      G.enc_ideal c' idealSpecies
    ] using hCovers idealSpecies
  · have hzero :
        State.embed G.ideal target species = 0 :=
      State.embed_eq_zero_of_not_exists
        (e := G.ideal) (z := target) (t := species) hImage
    simp [hzero]

theorem ideal_coverable_of_step_schedule_of_le
    (G : FootprintedConcreteFourPhaseModule.{u, v, w} (s := s) M)
    {c c' : MicroCfg Q s}
    {target : State (FourPhaseSpecies Q)}
    (hc : GadgetMicroCfgWF c)
    (hstep : phaseStep? (s := s) M c = some c')
    (hTarget :
      forall species, target species <= FourPhaseEncoding.enc c' species) :
    G.N.CoverableFrom
      (G.enc c)
      (State.embed G.ideal target) :=
  G.ideal_coverable_of_step_schedule_covers hc hstep hTarget

theorem ideal_coverableFrom_of_step_schedule_covers
    (G : FootprintedConcreteFourPhaseModule.{u, v, w} (s := s) M)
    {c c' : MicroCfg Q s}
    {target : State (FourPhaseSpecies Q)}
    (hc : GadgetMicroCfgWF c)
    (hstep : phaseStep? (s := s) M c = some c')
    (hCovers : Covers (FourPhaseEncoding.enc c') target) :
    G.N.CoverableFrom
      (G.enc c)
      (State.embed G.ideal target) :=
  G.ideal_coverable_of_step_schedule_covers hc hstep hCovers

theorem ideal_coverableFrom_of_step_schedule_of_le
    (G : FootprintedConcreteFourPhaseModule.{u, v, w} (s := s) M)
    {c c' : MicroCfg Q s}
    {target : State (FourPhaseSpecies Q)}
    (hc : GadgetMicroCfgWF c)
    (hstep : phaseStep? (s := s) M c = some c')
    (hTarget :
      forall species, target species <= FourPhaseEncoding.enc c' species) :
    G.N.CoverableFrom
      (G.enc c)
      (State.embed G.ideal target) :=
  G.ideal_coverable_of_step_schedule_of_le hc hstep hTarget

theorem ideal_speciesCoverableFrom_of_step_schedule
    (G : FootprintedConcreteFourPhaseModule.{u, v, w} (s := s) M)
    {c c' : MicroCfg Q s}
    {species : FourPhaseSpecies Q} {amount : Nat}
    (hc : GadgetMicroCfgWF c)
    (hstep : phaseStep? (s := s) M c = some c')
    (hamount : amount <= FourPhaseEncoding.enc c' species) :
    G.N.SpeciesCoverableFrom
      (G.enc c) (G.ideal species) amount := by
  have hamount' :
      amount <= G.enc c' (G.ideal species) := by
    rw [G.enc_ideal c' species]
    exact hamount
  exact G.speciesCoverableFrom_of_step_schedule_coord hc hstep hamount'

theorem ideal_speciesCoverableFrom_one_of_step_schedule_pos
    (G : FootprintedConcreteFourPhaseModule.{u, v, w} (s := s) M)
    {c c' : MicroCfg Q s}
    {species : FourPhaseSpecies Q}
    (hc : GadgetMicroCfgWF c)
    (hstep : phaseStep? (s := s) M c = some c')
    (hpos : 0 < FourPhaseEncoding.enc c' species) :
    G.N.SpeciesCoverableFrom
      (G.enc c) (G.ideal species) := by
  have hpos' : 0 < G.enc c' (G.ideal species) := by
    rw [G.enc_ideal c' species]
    exact hpos
  exact G.speciesCoverableFrom_one_of_step_schedule_pos hc hstep hpos'

theorem ideal_tape_speciesCoverableFrom_of_step_schedule
    (G : FootprintedConcreteFourPhaseModule.{u, v, w} (s := s) M)
    {c c' : MicroCfg Q s}
    (hc : GadgetMicroCfgWF c)
    (hstep : phaseStep? (s := s) M c = some c') :
    G.N.SpeciesCoverableFrom
      (G.enc c)
      (G.ideal FourPhaseSpecies.tape)
      c'.tape :=
  G.ideal_speciesCoverableFrom_of_step_schedule hc hstep (by simp)

theorem ideal_tapeBar_speciesCoverableFrom_of_step_schedule
    (G : FootprintedConcreteFourPhaseModule.{u, v, w} (s := s) M)
    {c c' : MicroCfg Q s}
    (hc : GadgetMicroCfgWF c)
    (hstep : phaseStep? (s := s) M c = some c') :
    G.N.SpeciesCoverableFrom
      (G.enc c)
      (G.ideal FourPhaseSpecies.tapeBar)
      (FourPhaseEncoding.maxTape s - c'.tape) :=
  G.ideal_speciesCoverableFrom_of_step_schedule hc hstep (by simp)

theorem state_after_step_schedule_of_firesListAt
    (G : FootprintedConcreteFourPhaseModule.{u, v, w} (s := s) M)
    {c c' : MicroCfg Q s}
    (hc : GadgetMicroCfgWF c)
    (hstep : phaseStep? (s := s) M c = some c')
    {path : G.N.Path} {t : Nat}
    (hstate : path.state t = G.enc c)
    (hfires :
      path.FiresListAt t (G.step_schedule hc hstep).schedule) :
    path.state (t + (G.step_schedule hc hstep).schedule.length) =
      G.enc c' :=
  (G.step_schedule hc hstep).state_after_firesListAt hstate hfires

theorem state_after_step_schedule_of_firesIntendedContiguouslyAt
    (G : FootprintedConcreteFourPhaseModule.{u, v, w} (s := s) M)
    {c c' : MicroCfg Q s}
    (hc : GadgetMicroCfgWF c)
    (hstep : phaseStep? (s := s) M c = some c')
    {path : G.N.Path} {t : Nat}
    (hfire :
      path.FiresIntendedContiguouslyAt t
        (G.intendedSchedule_of_step_schedule hc hstep)) :
    path.state
        (t +
          (G.intendedSchedule_of_step_schedule hc hstep).firingCount) =
      G.enc c' := by
  simpa [
    intendedSchedule_of_step_schedule,
    Network.IntendedSchedule.firingCount
  ] using
    (G.step_schedule hc hstep).state_after_firesIntendedContiguouslyAt
      hfire

theorem state_after_bounded_step_schedule_of_firesListAt
    (G : FootprintedConcreteFourPhaseModule.{u, v, w} (s := s) M)
    {c c' : MicroCfg Q s}
    (hc : GadgetMicroCfgWF c)
    (hstep : phaseStep? (s := s) M c = some c')
    {path : G.N.Path} {t : Nat}
    (hstate : path.state t = G.enc c)
    (hfires :
      path.FiresListAt t
        (G.boundedIntendedSchedule_of_step_schedule hc hstep).schedule) :
    path.state
        (t +
          (G.boundedIntendedSchedule_of_step_schedule hc hstep).firingCount) =
      G.enc c' :=
  path.state_after_boundedIntended_of_firesListAt
    (G.boundedIntendedSchedule_of_step_schedule hc hstep)
    hstate
    hfires

theorem state_after_bounded_step_schedule_of_firesIntendedContiguouslyAt
    (G : FootprintedConcreteFourPhaseModule.{u, v, w} (s := s) M)
    {c c' : MicroCfg Q s}
    (hc : GadgetMicroCfgWF c)
    (hstep : phaseStep? (s := s) M c = some c')
    {path : G.N.Path} {t : Nat}
    (hfire :
      path.FiresIntendedContiguouslyAt t
        (G.boundedIntendedSchedule_of_step_schedule hc hstep).toIntendedSchedule) :
    path.state
        (t +
          (G.boundedIntendedSchedule_of_step_schedule hc hstep).firingCount) =
      G.enc c' :=
  path.state_after_boundedIntended_of_firesIntendedContiguouslyAt
    (G.boundedIntendedSchedule_of_step_schedule hc hstep)
    hfire

theorem state_after_step_schedule_of_intendedWinsRaceAt
    (G : FootprintedConcreteFourPhaseModule.{u, v, w} (s := s) M)
    {c c' : MicroCfg Q s}
    (hc : GadgetMicroCfgWF c)
    (hstep : phaseStep? (s := s) M c = some c')
    {path : G.N.Path} {Bad : G.N.BadIndexSet} {t : Nat}
    (hwin :
      path.IntendedWinsRaceAt Bad t
        (G.intendedSchedule_of_step_schedule hc hstep)) :
    path.state
        (t +
          (G.intendedSchedule_of_step_schedule hc hstep).firingCount) =
      G.enc c' := by
  simpa [
    intendedSchedule_of_step_schedule,
    Network.IntendedSchedule.firingCount
  ] using
    (G.step_schedule hc hstep).state_after_intendedWinsRaceAt hwin

theorem state_after_bounded_step_schedule_of_intendedWinsRaceAt
    (G : FootprintedConcreteFourPhaseModule.{u, v, w} (s := s) M)
    {c c' : MicroCfg Q s}
    (hc : GadgetMicroCfgWF c)
    (hstep : phaseStep? (s := s) M c = some c')
    {path : G.N.Path} {Bad : G.N.BadIndexSet} {t : Nat}
    (hwin :
      path.IntendedWinsRaceAt Bad t
        (G.boundedIntendedSchedule_of_step_schedule hc hstep).toIntendedSchedule) :
    path.state
        (t +
          (G.boundedIntendedSchedule_of_step_schedule hc hstep).firingCount) =
      G.enc c' :=
  path.state_after_boundedIntendedWinsRaceAt Bad
    (G.boundedIntendedSchedule_of_step_schedule hc hstep)
    hwin

theorem eqOn_of_step_schedule_disjoint
    (G : FootprintedConcreteFourPhaseModule.{u, v, w} (s := s) M)
    {c c' : MicroCfg Q s}
    (hc : GadgetMicroCfgWF c)
    (hstep : phaseStep? (s := s) M c = some c')
    {Protected : G.CSp -> Prop}
    (hDisjoint :
      forall sp,
        ConcreteLocalFootprint G.ideal G.auxFootprint c c' sp ->
          Protected sp -> False) :
    State.EqOn Protected (G.enc c') (G.enc c) :=
  (G.step_schedule hc hstep).eqOn_of_disjoint hDisjoint

theorem concrete_coord_eq_of_step_schedule_not_footprint
    (G : FootprintedConcreteFourPhaseModule.{u, v, w} (s := s) M)
    {c c' : MicroCfg Q s}
    (hc : GadgetMicroCfgWF c)
    (hstep : phaseStep? (s := s) M c = some c')
    {species : G.CSp}
    (hnot :
      Not (ConcreteLocalFootprint G.ideal G.auxFootprint c c' species)) :
    G.enc c' species = G.enc c species :=
  (G.agreesOutside_of_step_schedule hc hstep) species hnot

theorem not_concreteLocalFootprint_ideal_of_not_local
    (G : FootprintedConcreteFourPhaseModule.{u, v, w} (s := s) M)
    {c c' : MicroCfg Q s}
    {species : FourPhaseSpecies Q}
    (hnot :
      Not
        (FourPhaseSpecies.IsLocalMacroFootprint
          (FourPhaseSpecies.ctrlOf c.state)
          (FourPhaseSpecies.ctrlOf c'.state)
          species)) :
    Not
      (ConcreteLocalFootprint G.ideal G.auxFootprint c c'
        (G.ideal species)) := by
  intro hFoot
  rcases hFoot with hVisible | hAux
  · rcases hVisible with ⟨species', hLocal, hEq⟩
    have hSpecies : species = species' :=
      G.ideal_injective hEq
    cases hSpecies
    exact hnot hLocal
  · exact G.auxFootprint_disjoint_ideal species hAux

theorem concreteLocalFootprint_ideal_iff
    (G : FootprintedConcreteFourPhaseModule.{u, v, w} (s := s) M)
    {c c' : MicroCfg Q s}
    {species : FourPhaseSpecies Q} :
    ConcreteLocalFootprint G.ideal G.auxFootprint c c'
        (G.ideal species) <->
      FourPhaseSpecies.IsLocalMacroFootprint
        (FourPhaseSpecies.ctrlOf c.state)
        (FourPhaseSpecies.ctrlOf c'.state)
        species := by
  constructor
  · intro hFoot
    rcases hFoot with hVisible | hAux
    · rcases hVisible with ⟨species', hLocal, hEq⟩
      have hSpecies : species = species' :=
        G.ideal_injective hEq
      cases hSpecies
      exact hLocal
    · exact False.elim (G.auxFootprint_disjoint_ideal species hAux)
  · intro hLocal
    exact Or.inl ⟨species, hLocal, rfl⟩

theorem not_concreteLocalFootprint_ideal_of_not_members
    (G : FootprintedConcreteFourPhaseModule.{u, v, w} (s := s) M)
    {c c' : MicroCfg Q s}
    {species : FourPhaseSpecies Q}
    (hold : species ≠ FourPhaseSpecies.ctrlOf c.state)
    (hnew : species ≠ FourPhaseSpecies.ctrlOf c'.state)
    (htape : Not (FourPhaseSpecies.IsTapePair species)) :
    Not
      (ConcreteLocalFootprint G.ideal G.auxFootprint c c'
        (G.ideal species)) :=
  G.not_concreteLocalFootprint_ideal_of_not_local
    (FourPhaseSpecies.not_localMacroFootprint_of_not_members
      hold hnew htape)

theorem ideal_coord_eq_of_step_schedule_not_members
    (G : FootprintedConcreteFourPhaseModule.{u, v, w} (s := s) M)
    {c c' : MicroCfg Q s}
    (hc : GadgetMicroCfgWF c)
    (hstep : phaseStep? (s := s) M c = some c')
    {species : FourPhaseSpecies Q}
    (hold : species ≠ FourPhaseSpecies.ctrlOf c.state)
    (hnew : species ≠ FourPhaseSpecies.ctrlOf c'.state)
    (htape : Not (FourPhaseSpecies.IsTapePair species)) :
    G.enc c' (G.ideal species) = G.enc c (G.ideal species) :=
  G.concrete_coord_eq_of_step_schedule_not_footprint hc hstep
    (G.not_concreteLocalFootprint_ideal_of_not_members hold hnew htape)

theorem ideal_coord_eq_of_step_schedule_not_local
    (G : FootprintedConcreteFourPhaseModule.{u, v, w} (s := s) M)
    {c c' : MicroCfg Q s}
    (hc : GadgetMicroCfgWF c)
    (hstep : phaseStep? (s := s) M c = some c')
    {species : FourPhaseSpecies Q}
    (hnot :
      Not
        (FourPhaseSpecies.IsLocalMacroFootprint
          (FourPhaseSpecies.ctrlOf c.state)
          (FourPhaseSpecies.ctrlOf c'.state)
          species)) :
    G.enc c' (G.ideal species) = G.enc c (G.ideal species) := by
  exact
    (G.agreesOutside_of_step_schedule hc hstep) (G.ideal species)
      (G.not_concreteLocalFootprint_ideal_of_not_local hnot)

theorem fourPhaseEncoding_coord_eq_of_step_schedule_not_local
    (G : FootprintedConcreteFourPhaseModule.{u, v, w} (s := s) M)
    {c c' : MicroCfg Q s}
    (hc : GadgetMicroCfgWF c)
    (hstep : phaseStep? (s := s) M c = some c')
    {species : FourPhaseSpecies Q}
    (hnot :
      Not
        (FourPhaseSpecies.IsLocalMacroFootprint
          (FourPhaseSpecies.ctrlOf c.state)
          (FourPhaseSpecies.ctrlOf c'.state)
          species)) :
    FourPhaseEncoding.enc c' species =
      FourPhaseEncoding.enc c species := by
  have hEq :
      G.enc c' (G.ideal species) =
        G.enc c (G.ideal species) :=
    G.ideal_coord_eq_of_step_schedule_not_local hc hstep hnot
  rw [G.enc_ideal c' species, G.enc_ideal c species] at hEq
  exact hEq

theorem fourPhaseEncoding_coord_eq_of_step_schedule_not_members
    (G : FootprintedConcreteFourPhaseModule.{u, v, w} (s := s) M)
    {c c' : MicroCfg Q s}
    (hc : GadgetMicroCfgWF c)
    (hstep : phaseStep? (s := s) M c = some c')
    {species : FourPhaseSpecies Q}
    (hold : species ≠ FourPhaseSpecies.ctrlOf c.state)
    (hnew : species ≠ FourPhaseSpecies.ctrlOf c'.state)
    (htape : Not (FourPhaseSpecies.IsTapePair species)) :
    FourPhaseEncoding.enc c' species =
      FourPhaseEncoding.enc c species :=
  G.fourPhaseEncoding_coord_eq_of_step_schedule_not_local hc hstep
    (FourPhaseSpecies.not_localMacroFootprint_of_not_members
      (oldCtrl := FourPhaseSpecies.ctrlOf c.state)
      (newCtrl := FourPhaseSpecies.ctrlOf c'.state)
      hold hnew htape)

end FootprintedConcreteFourPhaseModule

namespace FootprintedConcreteFourPhaseExpansionFamily

variable {Q : Type u} [Fintype Q] [DecidableEq Q] {s : Nat}
variable {M : Binary Q}

def toFootprintedConcreteFourPhaseModule
    (F : FootprintedConcreteFourPhaseExpansionFamily.{u, v, w} (s := s) M) :
    FootprintedConcreteFourPhaseModule.{u, v, w} (s := s) M where
  CSp := F.CSp
  instFintype := F.instFintype
  instDecidableEq := F.instDecidableEq
  N := F.network
  enc := F.enc
  ideal := F.ideal
  ideal_injective := F.ideal_injective
  enc_ideal := F.enc_ideal
  step_len_bound := F.step_len_bound
  allAtMostBimolecularInput := F.network_allAtMostBimolecularInput
  hasPositiveRates := F.network_hasPositiveRates
  auxFootprint := F.auxFootprint
  auxFootprint_disjoint_ideal := by
    intro c c' species
    cases hphase : c.state.phase with
    | read =>
        simpa [auxFootprint, hphase] using
          (F.read.auxFootprint_disjoint_ideal
            (c := c) (c' := c') species)
    | erase =>
        simpa [auxFootprint, hphase] using
          (F.erase.auxFootprint_disjoint_ideal
            (c := c) (c' := c') species)
    | shift =>
        simpa [auxFootprint, hphase] using
          (F.shift.auxFootprint_disjoint_ideal
            (c := c) (c' := c') species)
    | write =>
        simpa [auxFootprint, hphase] using
          (F.write.auxFootprint_disjoint_ideal
            (c := c) (c' := c') species)
  step_schedule := by
    intro c c' hc hstep
    cases hphase : c.state.phase with
    | read =>
        let Sched := F.read.step_schedule hc hphase hstep
        have hL : F.read.step_len_bound <= F.step_len_bound := by
          dsimp [step_len_bound]
          omega
        have hFoot :
            forall sp,
              ConcreteLocalFootprint F.ideal F.read.auxFootprint c c' sp ->
                ConcreteLocalFootprint F.ideal F.auxFootprint c c' sp := by
          intro sp hFoot
          rcases hFoot with hVisible | hAux
          · exact Or.inl hVisible
          · exact Or.inr (by
              simpa [auxFootprint, hphase] using hAux)
        simpa [network] using
          (Sched.mono hL hFoot).phaseParallel4_read
            (Nerase := F.erase.N)
            (Nshift := F.shift.N)
            (Nwrite := F.write.N)
    | erase =>
        let Sched := F.erase.step_schedule hc hphase hstep
        have hL : F.erase.step_len_bound <= F.step_len_bound := by
          dsimp [step_len_bound]
          omega
        have hFoot :
            forall sp,
              ConcreteLocalFootprint F.ideal F.erase.auxFootprint c c' sp ->
                ConcreteLocalFootprint F.ideal F.auxFootprint c c' sp := by
          intro sp hFoot
          rcases hFoot with hVisible | hAux
          · exact Or.inl hVisible
          · exact Or.inr (by
              simpa [auxFootprint, hphase] using hAux)
        simpa [network] using
          (Sched.mono hL hFoot).phaseParallel4_erase
            (Nread := F.read.N)
            (Nshift := F.shift.N)
            (Nwrite := F.write.N)
    | shift =>
        let Sched := F.shift.step_schedule hc hphase hstep
        have hL : F.shift.step_len_bound <= F.step_len_bound := by
          dsimp [step_len_bound]
          omega
        have hFoot :
            forall sp,
              ConcreteLocalFootprint F.ideal F.shift.auxFootprint c c' sp ->
                ConcreteLocalFootprint F.ideal F.auxFootprint c c' sp := by
          intro sp hFoot
          rcases hFoot with hVisible | hAux
          · exact Or.inl hVisible
          · exact Or.inr (by
              simpa [auxFootprint, hphase] using hAux)
        simpa [network] using
          (Sched.mono hL hFoot).phaseParallel4_shift
            (Nread := F.read.N)
            (Nerase := F.erase.N)
            (Nwrite := F.write.N)
    | write =>
        let Sched := F.write.step_schedule hc hphase hstep
        have hL : F.write.step_len_bound <= F.step_len_bound := by
          dsimp [step_len_bound]
          omega
        have hFoot :
            forall sp,
              ConcreteLocalFootprint F.ideal F.write.auxFootprint c c' sp ->
                ConcreteLocalFootprint F.ideal F.auxFootprint c c' sp := by
          intro sp hFoot
          rcases hFoot with hVisible | hAux
          · exact Or.inl hVisible
          · exact Or.inr (by
              simpa [auxFootprint, hphase] using hAux)
        simpa [network] using
          (Sched.mono hL hFoot).phaseParallel4_write
            (Nread := F.read.N)
            (Nerase := F.erase.N)
            (Nshift := F.shift.N)

end FootprintedConcreteFourPhaseExpansionFamily

namespace FootprintedConcreteFourPhaseExpansionFamily

variable {Q : Type u} [Fintype Q] [DecidableEq Q] {s : Nat}
variable {M : Binary Q}

def toConcreteFourPhaseModule
    (F : FootprintedConcreteFourPhaseExpansionFamily.{u, v, w} (s := s) M) :
    ConcreteFourPhaseModule.{u, v, w} (s := s) M :=
  F.toFootprintedConcreteFourPhaseModule.toConcreteFourPhaseModule

end FootprintedConcreteFourPhaseExpansionFamily

end FourPhaseConcrete

end CTM

end Ripple.sCRNUniversality
