import Ripple.sCRNUniversality.Computation.CTM.FourPhaseMacroModule

namespace Ripple.sCRNUniversality

namespace CTM

namespace FourPhaseMacroModule

universe u w

def coverabilitySuccess
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {Omega : Type w}
    (cfg0 : Omega -> Cfg Q Bool s)
    (target : Omega -> State (FourPhaseSpecies Q)) :
    Omega -> Prop :=
  fun omega =>
    (network (s := s) M).CoverableFrom
      (FourPhaseEncoding.enc (MicroCfg.ofCTM (cfg0 omega)))
      (target omega)

def speciesCoverabilitySuccess
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {Omega : Type w}
    (cfg0 : Omega -> Cfg Q Bool s)
    (species : FourPhaseSpecies Q)
    (amount : Nat) :
    Omega -> Prop :=
  fun omega =>
    (network (s := s) M).SpeciesCoverableFrom
      (FourPhaseEncoding.enc (MicroCfg.ofCTM (cfg0 omega)))
      species amount

def execSuccess
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {Omega : Type w}
    (cfg0 cfg1 : Omega -> Cfg Q Bool s) :
    Omega -> Prop :=
  fun omega =>
    exists is : List (network (s := s) M).I,
      (network (s := s) M).Exec
        (FourPhaseEncoding.enc (MicroCfg.ofCTM (cfg0 omega)))
        (FourPhaseEncoding.enc (MicroCfg.ofCTM (cfg1 omega))) is

/--
Alias for `execSuccess` emphasizing that the event is produced by the intended
deterministic CTM-to-macro bridge, not by stochastic semantics.
-/
abbrev intendedExecSuccess
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {Omega : Type w}
    (cfg0 cfg1 : Omega -> Cfg Q Bool s) :
    Omega -> Prop :=
  execSuccess (s := s) M cfg0 cfg1

def boundedExecToSuccess
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {Omega : Type w}
    (cfg0 cfg1 : Omega -> Cfg Q Bool s)
    (maxSteps : Nat) :
    Omega -> Prop :=
  fun omega =>
    exists is : List (network (s := s) M).I,
      (network (s := s) M).Exec
        (FourPhaseEncoding.enc (MicroCfg.ofCTM (cfg0 omega)))
        (FourPhaseEncoding.enc (MicroCfg.ofCTM (cfg1 omega))) is /\
      is.length <= 4 * maxSteps

/--
Targetless bounded execution. This is extensionally trivial by taking the empty
schedule to the initial configuration itself; use `boundedExecToSuccess` when a
fixed CTM endpoint matters.
-/
def boundedExecSuccess
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {Omega : Type w}
    (cfg0 : Omega -> Cfg Q Bool s)
    (maxSteps : Nat) :
    Omega -> Prop :=
  fun omega =>
    exists cfg' : Cfg Q Bool s,
    exists is : List (network (s := s) M).I,
      (network (s := s) M).Exec
        (FourPhaseEncoding.enc (MicroCfg.ofCTM (cfg0 omega)))
        (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg')) is /\
      is.length <= 4 * maxSteps

/--
Alias for the targetless `boundedExecSuccess`, emphasizing that the bound is on
the number of macro reaction firings in the produced deterministic schedule.
-/
abbrev boundedFiringCountExecSuccess
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {Omega : Type w}
    (cfg0 : Omega -> Cfg Q Bool s)
    (maxSteps : Nat) :
    Omega -> Prop :=
  boundedExecSuccess (s := s) M cfg0 maxSteps

def boundedCoverabilitySuccess
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {Omega : Type w}
    (cfg0 : Omega -> Cfg Q Bool s)
    (target : Omega -> State (FourPhaseSpecies Q))
    (maxSteps : Nat) :
    Omega -> Prop :=
  fun omega =>
    exists cfg' : Cfg Q Bool s,
    exists is : List (network (s := s) M).I,
      (network (s := s) M).Exec
        (FourPhaseEncoding.enc (MicroCfg.ofCTM (cfg0 omega)))
        (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg')) is /\
      is.length <= 4 * maxSteps /\
      Covers (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg'))
        (target omega)

/--
Alias for bounded coverability with a deterministic macro firing-count witness.
-/
abbrev boundedFiringCountCoverabilitySuccess
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {Omega : Type w}
    (cfg0 : Omega -> Cfg Q Bool s)
    (target : Omega -> State (FourPhaseSpecies Q))
    (maxSteps : Nat) :
    Omega -> Prop :=
  boundedCoverabilitySuccess (s := s) M cfg0 target maxSteps

def boundedSpeciesCoverabilitySuccess
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {Omega : Type w}
    (cfg0 : Omega -> Cfg Q Bool s)
    (species : FourPhaseSpecies Q)
    (amount maxSteps : Nat) :
    Omega -> Prop :=
  fun omega =>
    exists cfg' : Cfg Q Bool s,
    exists is : List (network (s := s) M).I,
      (network (s := s) M).Exec
        (FourPhaseEncoding.enc (MicroCfg.ofCTM (cfg0 omega)))
        (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg')) is /\
      is.length <= 4 * maxSteps /\
      amount <= FourPhaseEncoding.enc (MicroCfg.ofCTM cfg') species

/--
Alias for bounded species-coverability with a deterministic macro firing-count
witness.
-/
abbrev boundedFiringCountSpeciesCoverabilitySuccess
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {Omega : Type w}
    (cfg0 : Omega -> Cfg Q Bool s)
    (species : FourPhaseSpecies Q)
    (amount maxSteps : Nat) :
    Omega -> Prop :=
  boundedSpeciesCoverabilitySuccess
    (s := s) M cfg0 species amount maxSteps

/--
Targetless execution. This is extensionally trivial by taking the empty
schedule to the initial configuration itself.
-/
def someExecSuccess
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {Omega : Type w}
    (cfg0 : Omega -> Cfg Q Bool s) :
    Omega -> Prop :=
  fun omega =>
    exists cfg' : Cfg Q Bool s,
    exists is : List (network (s := s) M).I,
      (network (s := s) M).Exec
        (FourPhaseEncoding.enc (MicroCfg.ofCTM (cfg0 omega)))
        (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg')) is

theorem boundedExecSuccess_imp_someExecSuccess
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {Omega : Type w}
    (cfg0 : Omega -> Cfg Q Bool s)
    (maxSteps : Nat)
    (omega : Omega)
    (h : boundedExecSuccess (s := s) M cfg0 maxSteps omega) :
    someExecSuccess (s := s) M cfg0 omega := by
  rcases h with ⟨cfg', is, hExec, _hLen⟩
  exact ⟨cfg', is, hExec⟩

theorem boundedCoverabilitySuccess_imp_coverabilitySuccess
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {Omega : Type w}
    (cfg0 : Omega -> Cfg Q Bool s)
    (target : Omega -> State (FourPhaseSpecies Q))
    (maxSteps : Nat)
    (omega : Omega)
    (h :
      boundedCoverabilitySuccess
        (s := s) M cfg0 target maxSteps omega) :
    coverabilitySuccess (s := s) M cfg0 target omega := by
  rcases h with ⟨cfg', is, hExec, _hLen, hCovers⟩
  exact ⟨FourPhaseEncoding.enc (MicroCfg.ofCTM cfg'),
    ⟨is, hExec⟩, hCovers⟩

theorem boundedSpeciesCoverabilitySuccess_imp_speciesCoverabilitySuccess
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {Omega : Type w}
    (cfg0 : Omega -> Cfg Q Bool s)
    (species : FourPhaseSpecies Q)
    (amount maxSteps : Nat)
    (omega : Omega)
    (h :
      boundedSpeciesCoverabilitySuccess
        (s := s) M cfg0 species amount maxSteps omega) :
    speciesCoverabilitySuccess (s := s) M cfg0 species amount omega := by
  rcases h with ⟨cfg', is, hExec, _hLen, hAmount⟩
  exact Network.speciesCoverableFrom_of_reaches_coord
    (N := network (s := s) M)
    ⟨is, hExec⟩
    hAmount

theorem execSuccess_imp_coverabilitySuccess
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {Omega : Type w}
    (cfg0 cfg1 : Omega -> Cfg Q Bool s)
    (target : Omega -> State (FourPhaseSpecies Q))
    (omega : Omega)
    (hExec : execSuccess (s := s) M cfg0 cfg1 omega)
    (hCovers :
      Covers
        (FourPhaseEncoding.enc (MicroCfg.ofCTM (cfg1 omega)))
        (target omega)) :
    coverabilitySuccess (s := s) M cfg0 target omega := by
  rcases hExec with ⟨is, hIs⟩
  exact Network.coverable_of_reaches_of_covers
    ⟨is, hIs⟩
    hCovers

theorem execSuccess_imp_speciesCoverabilitySuccess
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {Omega : Type w}
    (cfg0 cfg1 : Omega -> Cfg Q Bool s)
    (species : FourPhaseSpecies Q)
    (amount : Nat)
    (omega : Omega)
    (hExec : execSuccess (s := s) M cfg0 cfg1 omega)
    (hAmount :
      amount <=
        FourPhaseEncoding.enc (MicroCfg.ofCTM (cfg1 omega)) species) :
    speciesCoverabilitySuccess (s := s) M cfg0 species amount omega := by
  rcases hExec with ⟨is, hIs⟩
  exact Network.speciesCoverableFrom_of_reaches_coord
    (N := network (s := s) M)
    ⟨is, hIs⟩
    hAmount

theorem execSuccess_imp_tapeSpeciesCoverabilitySuccess
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {Omega : Type w}
    (cfg0 cfg1 : Omega -> Cfg Q Bool s)
    (amount : Nat)
    (omega : Omega)
    (hExec : execSuccess (s := s) M cfg0 cfg1 omega)
    (hAmount : amount <= Encoding.base3Val (cfg1 omega).tape) :
    speciesCoverabilitySuccess
      (s := s) M cfg0 FourPhaseSpecies.tape amount omega :=
  execSuccess_imp_speciesCoverabilitySuccess
    (s := s) M cfg0 cfg1 FourPhaseSpecies.tape amount omega
    hExec
    (by
      simpa [MicroCfg.ofCTM] using hAmount)

def ctmExecWitness
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {Omega : Type w}
    (cfg0 cfg1 : Omega -> Cfg Q Bool s) :
    Omega -> Prop :=
  fun omega =>
    exists n,
      (M.detSystem (s := s)).steps? n (cfg0 omega) =
        some (cfg1 omega)

abbrev ctmExecWitnessSuccess
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {Omega : Type w}
    (cfg0 cfg1 : Omega -> Cfg Q Bool s) :
    Omega -> Prop :=
  ctmExecWitness (s := s) M cfg0 cfg1

def ctmBoundedExecToWitness
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {Omega : Type w}
    (cfg0 cfg1 : Omega -> Cfg Q Bool s)
    (maxSteps : Nat) :
    Omega -> Prop :=
  fun omega =>
    exists n, n <= maxSteps /\
      (M.detSystem (s := s)).steps? n (cfg0 omega) =
        some (cfg1 omega)

abbrev ctmBoundedExecToWitnessSuccess
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {Omega : Type w}
    (cfg0 cfg1 : Omega -> Cfg Q Bool s)
    (maxSteps : Nat) :
    Omega -> Prop :=
  ctmBoundedExecToWitness (s := s) M cfg0 cfg1 maxSteps

def ctmCoverabilityWitness
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {Omega : Type w}
    (cfg0 : Omega -> Cfg Q Bool s)
    (target : Omega -> State (FourPhaseSpecies Q)) :
    Omega -> Prop :=
  fun omega =>
    exists n,
    exists cfg' : Cfg Q Bool s,
      (M.detSystem (s := s)).steps? n (cfg0 omega) = some cfg' /\
      Covers (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg'))
        (target omega)

abbrev ctmCoverabilityWitnessSuccess
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {Omega : Type w}
    (cfg0 : Omega -> Cfg Q Bool s)
    (target : Omega -> State (FourPhaseSpecies Q)) :
    Omega -> Prop :=
  ctmCoverabilityWitness (s := s) M cfg0 target

def ctmBoundedCoverabilityWitness
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {Omega : Type w}
    (cfg0 : Omega -> Cfg Q Bool s)
    (target : Omega -> State (FourPhaseSpecies Q))
    (maxSteps : Nat) :
    Omega -> Prop :=
  fun omega =>
    exists n, n <= maxSteps /\
    exists cfg' : Cfg Q Bool s,
      (M.detSystem (s := s)).steps? n (cfg0 omega) = some cfg' /\
      Covers (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg'))
        (target omega)

abbrev ctmBoundedCoverabilityWitnessSuccess
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {Omega : Type w}
    (cfg0 : Omega -> Cfg Q Bool s)
    (target : Omega -> State (FourPhaseSpecies Q))
    (maxSteps : Nat) :
    Omega -> Prop :=
  ctmBoundedCoverabilityWitness (s := s) M cfg0 target maxSteps

def ctmSpeciesCoverabilityWitness
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {Omega : Type w}
    (cfg0 : Omega -> Cfg Q Bool s)
    (species : FourPhaseSpecies Q)
    (amount : Nat) :
    Omega -> Prop :=
  fun omega =>
    exists n,
    exists cfg' : Cfg Q Bool s,
      (M.detSystem (s := s)).steps? n (cfg0 omega) = some cfg' /\
      amount <= FourPhaseEncoding.enc (MicroCfg.ofCTM cfg') species

abbrev ctmSpeciesCoverabilityWitnessSuccess
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {Omega : Type w}
    (cfg0 : Omega -> Cfg Q Bool s)
    (species : FourPhaseSpecies Q)
    (amount : Nat) :
    Omega -> Prop :=
  ctmSpeciesCoverabilityWitness (s := s) M cfg0 species amount

def ctmTapeSpeciesCoverabilityWitness
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {Omega : Type w}
    (cfg0 : Omega -> Cfg Q Bool s)
    (amount : Nat) :
    Omega -> Prop :=
  fun omega =>
    exists n,
    exists cfg' : Cfg Q Bool s,
      (M.detSystem (s := s)).steps? n (cfg0 omega) = some cfg' /\
      amount <= Encoding.base3Val cfg'.tape

def ctmBoundedSpeciesCoverabilityWitness
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {Omega : Type w}
    (cfg0 : Omega -> Cfg Q Bool s)
    (species : FourPhaseSpecies Q)
    (amount maxSteps : Nat) :
    Omega -> Prop :=
  fun omega =>
    exists n, n <= maxSteps /\
    exists cfg' : Cfg Q Bool s,
      (M.detSystem (s := s)).steps? n (cfg0 omega) = some cfg' /\
      amount <= FourPhaseEncoding.enc (MicroCfg.ofCTM cfg') species

abbrev ctmBoundedSpeciesCoverabilityWitnessSuccess
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {Omega : Type w}
    (cfg0 : Omega -> Cfg Q Bool s)
    (species : FourPhaseSpecies Q)
    (amount maxSteps : Nat) :
    Omega -> Prop :=
  ctmBoundedSpeciesCoverabilityWitness
    (s := s) M cfg0 species amount maxSteps

def ctmBoundedTapeSpeciesCoverabilityWitness
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {Omega : Type w}
    (cfg0 : Omega -> Cfg Q Bool s)
    (amount maxSteps : Nat) :
    Omega -> Prop :=
  fun omega =>
    exists n, n <= maxSteps /\
    exists cfg' : Cfg Q Bool s,
      (M.detSystem (s := s)).steps? n (cfg0 omega) = some cfg' /\
      amount <= Encoding.base3Val cfg'.tape

theorem execSuccess_of_ctmExecWitness
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {Omega : Type w}
    (cfg0 cfg1 : Omega -> Cfg Q Bool s)
    (omega : Omega)
    (h : ctmExecWitness (s := s) M cfg0 cfg1 omega) :
    execSuccess (s := s) M cfg0 cfg1 omega := by
  rcases h with ⟨n, hsteps⟩
  exact exec_of_ctm_steps (s := s) M hsteps

theorem boundedExecToSuccess_of_ctmBoundedExecToWitness
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {Omega : Type w}
    (cfg0 cfg1 : Omega -> Cfg Q Bool s)
    (maxSteps : Nat)
    (omega : Omega)
    (h :
      ctmBoundedExecToWitness
        (s := s) M cfg0 cfg1 maxSteps omega) :
    boundedExecToSuccess (s := s) M cfg0 cfg1 maxSteps omega := by
  rcases h with ⟨n, hn, hsteps⟩
  rcases exec_of_ctm_steps_bounded (s := s) M hsteps with
    ⟨is, hExec, hLen⟩
  exact ⟨is, hExec, le_trans hLen (Nat.mul_le_mul_left 4 hn)⟩

theorem execSuccess_of_ctmBoundedExecToWitness
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {Omega : Type w}
    (cfg0 cfg1 : Omega -> Cfg Q Bool s)
    (maxSteps : Nat)
    (omega : Omega)
    (h :
      ctmBoundedExecToWitness
        (s := s) M cfg0 cfg1 maxSteps omega) :
    execSuccess (s := s) M cfg0 cfg1 omega := by
  rcases h with ⟨n, _hn, hsteps⟩
  exact exec_of_ctm_steps (s := s) M hsteps

theorem boundedExecToSuccess_imp_execSuccess
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {Omega : Type w}
    (cfg0 cfg1 : Omega -> Cfg Q Bool s)
    (maxSteps : Nat)
    (omega : Omega)
    (h :
      boundedExecToSuccess
        (s := s) M cfg0 cfg1 maxSteps omega) :
    execSuccess (s := s) M cfg0 cfg1 omega := by
  rcases h with ⟨is, hExec, _hLen⟩
  exact ⟨is, hExec⟩

theorem boundedExecSuccess_trivial
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {Omega : Type w}
    (cfg0 : Omega -> Cfg Q Bool s)
    (maxSteps : Nat)
    (omega : Omega) :
    boundedExecSuccess (s := s) M cfg0 maxSteps omega :=
  ⟨cfg0 omega, [], ExecOf.nil _, by simp⟩

theorem coverabilitySuccess_of_ctmCoverabilityWitness
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {Omega : Type w}
    (cfg0 : Omega -> Cfg Q Bool s)
    (target : Omega -> State (FourPhaseSpecies Q))
    (omega : Omega)
    (h :
      ctmCoverabilityWitness
        (s := s) M cfg0 target omega) :
    coverabilitySuccess (s := s) M cfg0 target omega := by
  rcases h with ⟨n, cfg', hsteps, hCovers⟩
  exact coverable_of_ctm_steps_covers (s := s) M hsteps hCovers

theorem boundedCoverabilitySuccess_of_ctmBoundedCoverabilityWitness
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {Omega : Type w}
    (cfg0 : Omega -> Cfg Q Bool s)
    (target : Omega -> State (FourPhaseSpecies Q))
    (maxSteps : Nat)
    (omega : Omega)
    (h :
      ctmBoundedCoverabilityWitness
        (s := s) M cfg0 target maxSteps omega) :
    boundedCoverabilitySuccess (s := s) M cfg0 target maxSteps omega := by
  rcases h with ⟨n, hn, cfg', hsteps, hCovers⟩
  rcases exec_of_ctm_steps_bounded (s := s) M hsteps with
    ⟨is, hExec, hLen⟩
  exact ⟨cfg', is, hExec,
    le_trans hLen (Nat.mul_le_mul_left 4 hn), hCovers⟩

theorem speciesCoverabilitySuccess_of_ctmSpeciesCoverabilityWitness
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {Omega : Type w}
    (cfg0 : Omega -> Cfg Q Bool s)
    (species : FourPhaseSpecies Q)
    (amount : Nat)
    (omega : Omega)
    (h :
      ctmSpeciesCoverabilityWitness
        (s := s) M cfg0 species amount omega) :
    speciesCoverabilitySuccess (s := s) M cfg0 species amount omega := by
  rcases h with ⟨n, cfg', hsteps, hAmount⟩
  exact speciesCoverableFrom_of_ctm_steps_coord
    (s := s) M hsteps hAmount

theorem speciesCoverabilitySuccess_of_ctmTapeSpeciesCoverabilityWitness
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {Omega : Type w}
    (cfg0 : Omega -> Cfg Q Bool s)
    (amount : Nat)
    (omega : Omega)
    (h :
      ctmTapeSpeciesCoverabilityWitness
        (s := s) M cfg0 amount omega) :
    speciesCoverabilitySuccess
      (s := s) M cfg0 FourPhaseSpecies.tape amount omega := by
  rcases h with ⟨n, cfg', hsteps, hAmount⟩
  exact speciesCoverableFrom_of_ctm_steps_coord
    (s := s) M hsteps (by
      simpa [MicroCfg.ofCTM] using hAmount)

theorem boundedSpeciesCoverabilitySuccess_of_ctmBoundedSpeciesCoverabilityWitness
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {Omega : Type w}
    (cfg0 : Omega -> Cfg Q Bool s)
    (species : FourPhaseSpecies Q)
    (amount maxSteps : Nat)
    (omega : Omega)
    (h :
      ctmBoundedSpeciesCoverabilityWitness
        (s := s) M cfg0 species amount maxSteps omega) :
    boundedSpeciesCoverabilitySuccess
      (s := s) M cfg0 species amount maxSteps omega := by
  rcases h with ⟨n, hn, cfg', hsteps, hAmount⟩
  rcases exec_of_ctm_steps_bounded (s := s) M hsteps with
    ⟨is, hExec, hLen⟩
  exact ⟨cfg', is, hExec,
    le_trans hLen (Nat.mul_le_mul_left 4 hn), hAmount⟩

theorem boundedSpeciesCoverabilitySuccess_of_ctmBoundedTapeSpeciesCoverabilityWitness
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {Omega : Type w}
    (cfg0 : Omega -> Cfg Q Bool s)
    (amount maxSteps : Nat)
    (omega : Omega)
    (h :
      ctmBoundedTapeSpeciesCoverabilityWitness
        (s := s) M cfg0 amount maxSteps omega) :
    boundedSpeciesCoverabilitySuccess
      (s := s) M cfg0 FourPhaseSpecies.tape amount maxSteps omega := by
  rcases h with ⟨n, hn, cfg', hsteps, hAmount⟩
  rcases exec_of_ctm_steps_bounded (s := s) M hsteps with
    ⟨is, hExec, hLen⟩
  exact ⟨cfg', is, hExec,
    le_trans hLen (Nat.mul_le_mul_left 4 hn),
    by simpa [MicroCfg.ofCTM] using hAmount⟩

theorem ctmExecWitness_imp_execSuccess
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {Omega : Type w}
    (cfg0 cfg1 : Omega -> Cfg Q Bool s) :
    forall omega,
      ctmExecWitness (s := s) M cfg0 cfg1 omega ->
        execSuccess (s := s) M cfg0 cfg1 omega := by
  intro omega h
  exact execSuccess_of_ctmExecWitness (s := s) M cfg0 cfg1 omega h

theorem ctmBoundedExecToWitness_imp_boundedExecToSuccess
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {Omega : Type w}
    (cfg0 cfg1 : Omega -> Cfg Q Bool s)
    (maxSteps : Nat) :
    forall omega,
      ctmBoundedExecToWitness
        (s := s) M cfg0 cfg1 maxSteps omega ->
        boundedExecToSuccess
          (s := s) M cfg0 cfg1 maxSteps omega := by
  intro omega h
  exact boundedExecToSuccess_of_ctmBoundedExecToWitness
    (s := s) M cfg0 cfg1 maxSteps omega h

theorem ctmBoundedExecToWitness_imp_execSuccess
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {Omega : Type w}
    (cfg0 cfg1 : Omega -> Cfg Q Bool s)
    (maxSteps : Nat) :
    forall omega,
      ctmBoundedExecToWitness
        (s := s) M cfg0 cfg1 maxSteps omega ->
        execSuccess (s := s) M cfg0 cfg1 omega := by
  intro omega h
  exact execSuccess_of_ctmBoundedExecToWitness
    (s := s) M cfg0 cfg1 maxSteps omega h

theorem ctmCoverabilityWitness_imp_coverabilitySuccess
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {Omega : Type w}
    (cfg0 : Omega -> Cfg Q Bool s)
    (target : Omega -> State (FourPhaseSpecies Q)) :
    forall omega,
      ctmCoverabilityWitness (s := s) M cfg0 target omega ->
        coverabilitySuccess (s := s) M cfg0 target omega := by
  intro omega h
  exact coverabilitySuccess_of_ctmCoverabilityWitness
    (s := s) M cfg0 target omega h

theorem ctmBoundedCoverabilityWitness_imp_boundedCoverabilitySuccess
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {Omega : Type w}
    (cfg0 : Omega -> Cfg Q Bool s)
    (target : Omega -> State (FourPhaseSpecies Q))
    (maxSteps : Nat) :
    forall omega,
      ctmBoundedCoverabilityWitness
        (s := s) M cfg0 target maxSteps omega ->
        boundedCoverabilitySuccess
          (s := s) M cfg0 target maxSteps omega := by
  intro omega h
  exact boundedCoverabilitySuccess_of_ctmBoundedCoverabilityWitness
    (s := s) M cfg0 target maxSteps omega h

theorem ctmBoundedCoverabilityWitness_imp_coverabilitySuccess
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {Omega : Type w}
    (cfg0 : Omega -> Cfg Q Bool s)
    (target : Omega -> State (FourPhaseSpecies Q))
    (maxSteps : Nat) :
    forall omega,
      ctmBoundedCoverabilityWitness
        (s := s) M cfg0 target maxSteps omega ->
        coverabilitySuccess (s := s) M cfg0 target omega := by
  intro omega h
  exact boundedCoverabilitySuccess_imp_coverabilitySuccess
    (s := s) M cfg0 target maxSteps omega
    (boundedCoverabilitySuccess_of_ctmBoundedCoverabilityWitness
      (s := s) M cfg0 target maxSteps omega h)

theorem ctmSpeciesCoverabilityWitness_imp_speciesCoverabilitySuccess
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {Omega : Type w}
    (cfg0 : Omega -> Cfg Q Bool s)
    (species : FourPhaseSpecies Q)
    (amount : Nat) :
    forall omega,
      ctmSpeciesCoverabilityWitness
        (s := s) M cfg0 species amount omega ->
        speciesCoverabilitySuccess
          (s := s) M cfg0 species amount omega := by
  intro omega h
  exact speciesCoverabilitySuccess_of_ctmSpeciesCoverabilityWitness
    (s := s) M cfg0 species amount omega h

theorem ctmTapeSpeciesCoverabilityWitness_imp_speciesCoverabilitySuccess
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {Omega : Type w}
    (cfg0 : Omega -> Cfg Q Bool s)
    (amount : Nat) :
    forall omega,
      ctmTapeSpeciesCoverabilityWitness
        (s := s) M cfg0 amount omega ->
        speciesCoverabilitySuccess
          (s := s) M cfg0 FourPhaseSpecies.tape amount omega := by
  intro omega h
  exact speciesCoverabilitySuccess_of_ctmTapeSpeciesCoverabilityWitness
    (s := s) M cfg0 amount omega h

theorem ctmBoundedSpeciesCoverabilityWitness_imp_boundedSpeciesCoverabilitySuccess
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {Omega : Type w}
    (cfg0 : Omega -> Cfg Q Bool s)
    (species : FourPhaseSpecies Q)
    (amount maxSteps : Nat) :
    forall omega,
      ctmBoundedSpeciesCoverabilityWitness
        (s := s) M cfg0 species amount maxSteps omega ->
        boundedSpeciesCoverabilitySuccess
          (s := s) M cfg0 species amount maxSteps omega := by
  intro omega h
  exact boundedSpeciesCoverabilitySuccess_of_ctmBoundedSpeciesCoverabilityWitness
    (s := s) M cfg0 species amount maxSteps omega h

theorem ctmBoundedTapeSpeciesCoverabilityWitness_imp_boundedSpeciesCoverabilitySuccess
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {Omega : Type w}
    (cfg0 : Omega -> Cfg Q Bool s)
    (amount maxSteps : Nat) :
    forall omega,
      ctmBoundedTapeSpeciesCoverabilityWitness
        (s := s) M cfg0 amount maxSteps omega ->
        boundedSpeciesCoverabilitySuccess
          (s := s) M cfg0 FourPhaseSpecies.tape amount maxSteps omega := by
  intro omega h
  exact boundedSpeciesCoverabilitySuccess_of_ctmBoundedTapeSpeciesCoverabilityWitness
    (s := s) M cfg0 amount maxSteps omega h

theorem ctmBoundedTapeSpeciesCoverabilityWitness_imp_speciesCoverabilitySuccess
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {Omega : Type w}
    (cfg0 : Omega -> Cfg Q Bool s)
    (amount maxSteps : Nat) :
    forall omega,
      ctmBoundedTapeSpeciesCoverabilityWitness
        (s := s) M cfg0 amount maxSteps omega ->
        speciesCoverabilitySuccess
          (s := s) M cfg0 FourPhaseSpecies.tape amount omega := by
  intro omega h
  exact boundedSpeciesCoverabilitySuccess_imp_speciesCoverabilitySuccess
    (s := s) M cfg0 FourPhaseSpecies.tape amount maxSteps omega
    (boundedSpeciesCoverabilitySuccess_of_ctmBoundedTapeSpeciesCoverabilityWitness
      (s := s) M cfg0 amount maxSteps omega h)

theorem ctmBoundedSpeciesCoverabilityWitness_imp_speciesCoverabilitySuccess
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {Omega : Type w}
    (cfg0 : Omega -> Cfg Q Bool s)
    (species : FourPhaseSpecies Q)
    (amount maxSteps : Nat) :
    forall omega,
      ctmBoundedSpeciesCoverabilityWitness
        (s := s) M cfg0 species amount maxSteps omega ->
        speciesCoverabilitySuccess
          (s := s) M cfg0 species amount omega := by
  intro omega h
  exact boundedSpeciesCoverabilitySuccess_imp_speciesCoverabilitySuccess
    (s := s) M cfg0 species amount maxSteps omega
    (boundedSpeciesCoverabilitySuccess_of_ctmBoundedSpeciesCoverabilityWitness
      (s := s) M cfg0 species amount maxSteps omega h)

end FourPhaseMacroModule

end CTM

end Ripple.sCRNUniversality
