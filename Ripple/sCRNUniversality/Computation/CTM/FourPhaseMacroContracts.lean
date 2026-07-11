import Ripple.sCRNUniversality.Computation.CTM.FourPhaseMacroPredicates
import Ripple.sCRNUniversality.Probability.Contracts

namespace Ripple.sCRNUniversality

namespace CTM

namespace FourPhaseMacroModule

universe u w

def execSuccessContract_of_boundedExecToSuccessContract
    {Omega : Type w} {P : Probability.ProbSpec Omega}
    (hP : Probability.ProbAxioms P)
    (C : Probability.SuccessContract P)
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    (cfg0 cfg1 : Omega -> Cfg Q Bool s)
    (maxSteps : Nat)
    (hC :
      forall omega, C.success omega ->
        boundedExecToSuccess (s := s) M cfg0 cfg1 maxSteps omega) :
    Probability.SuccessContract P :=
  Probability.SuccessContract.consequence hP C
    (execSuccess (s := s) M cfg0 cfg1)
    (by
      intro omega hsuccess
      exact boundedExecToSuccess_imp_execSuccess
        (s := s) M cfg0 cfg1 maxSteps omega
        (hC omega hsuccess))

def boundedCoverabilitySuccessContract_of_boundedExecToSuccessContract
    {Omega : Type w} {P : Probability.ProbSpec Omega}
    (hP : Probability.ProbAxioms P)
    (C : Probability.SuccessContract P)
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    (cfg0 cfg1 : Omega -> Cfg Q Bool s)
    (target : Omega -> State (FourPhaseSpecies Q))
    (maxSteps : Nat)
    (hExec :
      forall omega, C.success omega ->
        boundedExecToSuccess (s := s) M cfg0 cfg1 maxSteps omega)
    (hCovers :
      forall omega, C.success omega ->
        Covers
          (FourPhaseEncoding.enc (MicroCfg.ofCTM (cfg1 omega)))
          (target omega)) :
    Probability.SuccessContract P :=
  Probability.SuccessContract.consequence hP C
    (boundedCoverabilitySuccess (s := s) M cfg0 target maxSteps)
    (by
      intro omega hsuccess
      rcases hExec omega hsuccess with ⟨is, hExecMacro, hLen⟩
      exact ⟨cfg1 omega, is, hExecMacro, hLen,
        hCovers omega hsuccess⟩)

/--
Consequence adapter from a bounded deterministic macro execution contract to a
bounded species-coverability contract.

The probability bound is inherited entirely from the input `SuccessContract`.
The additional hypotheses only say that, on already-successful samples, the
chosen deterministic endpoint schedule exists and the endpoint has enough of
`species`. This is not a CTMC semantics theorem, race-probability estimate,
fairness statement, or autonomous coverability claim.
-/
def boundedSpeciesCoverabilitySuccessContract_of_boundedExecToSuccessContract
    {Omega : Type w} {P : Probability.ProbSpec Omega}
    (hP : Probability.ProbAxioms P)
    (C : Probability.SuccessContract P)
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    (cfg0 cfg1 : Omega -> Cfg Q Bool s)
    (species : FourPhaseSpecies Q)
    (amount maxSteps : Nat)
    (hExec :
      forall omega, C.success omega ->
        boundedExecToSuccess (s := s) M cfg0 cfg1 maxSteps omega)
    (hAmount :
      forall omega, C.success omega ->
        amount <=
          FourPhaseEncoding.enc (MicroCfg.ofCTM (cfg1 omega)) species) :
    Probability.SuccessContract P :=
  Probability.SuccessContract.consequence hP C
    (boundedSpeciesCoverabilitySuccess
      (s := s) M cfg0 species amount maxSteps)
    (by
      intro omega hsuccess
      rcases hExec omega hsuccess with ⟨is, hExecMacro, hLen⟩
      exact ⟨cfg1 omega, is, hExecMacro, hLen,
        hAmount omega hsuccess⟩)

def boundedTapeSpeciesCoverabilitySuccessContract_of_boundedExecToSuccessContract
    {Omega : Type w} {P : Probability.ProbSpec Omega}
    (hP : Probability.ProbAxioms P)
    (C : Probability.SuccessContract P)
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    (cfg0 cfg1 : Omega -> Cfg Q Bool s)
    (amount maxSteps : Nat)
    (hExec :
      forall omega, C.success omega ->
        boundedExecToSuccess (s := s) M cfg0 cfg1 maxSteps omega)
    (hAmount :
      forall omega, C.success omega ->
        amount <= Encoding.base3Val (cfg1 omega).tape) :
    Probability.SuccessContract P :=
  boundedSpeciesCoverabilitySuccessContract_of_boundedExecToSuccessContract
    (s := s) hP C M cfg0 cfg1 FourPhaseSpecies.tape amount maxSteps
    hExec
    (by
      intro omega hsuccess
      simpa [MicroCfg.ofCTM] using hAmount omega hsuccess)

def coverabilitySuccessContract_of_boundedCoverabilitySuccessContract
    {Omega : Type w} {P : Probability.ProbSpec Omega}
    (hP : Probability.ProbAxioms P)
    (C : Probability.SuccessContract P)
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    (cfg0 : Omega -> Cfg Q Bool s)
    (target : Omega -> State (FourPhaseSpecies Q))
    (maxSteps : Nat)
    (hC :
      forall omega, C.success omega ->
        boundedCoverabilitySuccess
          (s := s) M cfg0 target maxSteps omega) :
    Probability.SuccessContract P :=
  Probability.SuccessContract.consequence hP C
    (coverabilitySuccess (s := s) M cfg0 target)
    (by
      intro omega hsuccess
      exact boundedCoverabilitySuccess_imp_coverabilitySuccess
        (s := s) M cfg0 target maxSteps omega
        (hC omega hsuccess))

def speciesCoverabilitySuccessContract_of_boundedSpeciesCoverabilitySuccessContract
    {Omega : Type w} {P : Probability.ProbSpec Omega}
    (hP : Probability.ProbAxioms P)
    (C : Probability.SuccessContract P)
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    (cfg0 : Omega -> Cfg Q Bool s)
    (species : FourPhaseSpecies Q)
    (amount maxSteps : Nat)
    (hC :
      forall omega, C.success omega ->
        boundedSpeciesCoverabilitySuccess
          (s := s) M cfg0 species amount maxSteps omega) :
    Probability.SuccessContract P :=
  Probability.SuccessContract.consequence hP C
    (speciesCoverabilitySuccess (s := s) M cfg0 species amount)
    (by
      intro omega hsuccess
      exact boundedSpeciesCoverabilitySuccess_imp_speciesCoverabilitySuccess
        (s := s) M cfg0 species amount maxSteps omega
        (hC omega hsuccess))

def someExecSuccessContract_of_boundedExecSuccessContract
    {Omega : Type w} {P : Probability.ProbSpec Omega}
    (hP : Probability.ProbAxioms P)
    (C : Probability.SuccessContract P)
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    (cfg0 : Omega -> Cfg Q Bool s)
    (maxSteps : Nat)
    (hC :
      forall omega, C.success omega ->
        boundedExecSuccess (s := s) M cfg0 maxSteps omega) :
    Probability.SuccessContract P :=
  Probability.SuccessContract.consequence hP C
    (someExecSuccess (s := s) M cfg0)
    (by
      intro omega hsuccess
      exact boundedExecSuccess_imp_someExecSuccess
        (s := s) M cfg0 maxSteps omega
        (hC omega hsuccess))

def coverabilitySuccessContract_of_execSuccessContract
    {Omega : Type w} {P : Probability.ProbSpec Omega}
    (hP : Probability.ProbAxioms P)
    (C : Probability.SuccessContract P)
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    (cfg0 cfg1 : Omega -> Cfg Q Bool s)
    (target : Omega -> State (FourPhaseSpecies Q))
    (hExec :
      forall omega, C.success omega ->
        execSuccess (s := s) M cfg0 cfg1 omega)
    (hCovers :
      forall omega, C.success omega ->
        Covers
          (FourPhaseEncoding.enc (MicroCfg.ofCTM (cfg1 omega)))
          (target omega)) :
    Probability.SuccessContract P :=
  Probability.SuccessContract.consequence hP C
    (coverabilitySuccess (s := s) M cfg0 target)
    (by
      intro omega hsuccess
      exact execSuccess_imp_coverabilitySuccess
        (s := s) M cfg0 cfg1 target omega
        (hExec omega hsuccess)
        (hCovers omega hsuccess))

def speciesCoverabilitySuccessContract_of_execSuccessContract
    {Omega : Type w} {P : Probability.ProbSpec Omega}
    (hP : Probability.ProbAxioms P)
    (C : Probability.SuccessContract P)
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    (cfg0 cfg1 : Omega -> Cfg Q Bool s)
    (species : FourPhaseSpecies Q)
    (amount : Nat)
    (hExec :
      forall omega, C.success omega ->
        execSuccess (s := s) M cfg0 cfg1 omega)
    (hAmount :
      forall omega, C.success omega ->
        amount <=
          FourPhaseEncoding.enc (MicroCfg.ofCTM (cfg1 omega)) species) :
    Probability.SuccessContract P :=
  Probability.SuccessContract.consequence hP C
    (speciesCoverabilitySuccess (s := s) M cfg0 species amount)
    (by
      intro omega hsuccess
      exact execSuccess_imp_speciesCoverabilitySuccess
        (s := s) M cfg0 cfg1 species amount omega
        (hExec omega hsuccess)
        (hAmount omega hsuccess))

def tapeSpeciesCoverabilitySuccessContract_of_execSuccessContract
    {Omega : Type w} {P : Probability.ProbSpec Omega}
    (hP : Probability.ProbAxioms P)
    (C : Probability.SuccessContract P)
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    (cfg0 cfg1 : Omega -> Cfg Q Bool s)
    (amount : Nat)
    (hExec :
      forall omega, C.success omega ->
        execSuccess (s := s) M cfg0 cfg1 omega)
    (hAmount :
      forall omega, C.success omega ->
        amount <= Encoding.base3Val (cfg1 omega).tape) :
    Probability.SuccessContract P :=
  speciesCoverabilitySuccessContract_of_execSuccessContract
    (s := s) hP C M cfg0 cfg1 FourPhaseSpecies.tape amount
    hExec
    (by
      intro omega hsuccess
      simpa [MicroCfg.ofCTM] using hAmount omega hsuccess)

def execSuccessContract_of_ctmSuccess
    {Omega : Type w} {P : Probability.ProbSpec Omega}
    (hP : Probability.ProbAxioms P)
    (C : Probability.SuccessContract P)
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    (cfg0 cfg1 : Omega -> Cfg Q Bool s)
    (h :
      forall omega, C.success omega ->
        ctmExecWitness (s := s) M cfg0 cfg1 omega) :
    Probability.SuccessContract P :=
  Probability.SuccessContract.consequence hP C
    (execSuccess (s := s) M cfg0 cfg1)
    (by
      intro omega hsuccess
      exact ctmExecWitness_imp_execSuccess
        (s := s) M cfg0 cfg1 omega (h omega hsuccess))

/--
Safer spelling of `execSuccessContract_of_ctmSuccess`.

The result is an intended deterministic macro execution event.
-/
def intendedExecSuccessContract_of_ctmSuccess
    {Omega : Type w} {P : Probability.ProbSpec Omega}
    (hP : Probability.ProbAxioms P)
    (C : Probability.SuccessContract P)
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    (cfg0 cfg1 : Omega -> Cfg Q Bool s)
    (h :
      forall omega, C.success omega ->
        ctmExecWitness (s := s) M cfg0 cfg1 omega) :
    Probability.SuccessContract P :=
  execSuccessContract_of_ctmSuccess (s := s) hP C M cfg0 cfg1 h

/--
Consequence adapter from a CTM-side bounded endpoint witness to deterministic
macro bounded-execution success.
-/
def boundedExecToSuccessContract_of_ctmBoundedExecToWitness
    {Omega : Type w} {P : Probability.ProbSpec Omega}
    (hP : Probability.ProbAxioms P)
    (C : Probability.SuccessContract P)
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    (cfg0 cfg1 : Omega -> Cfg Q Bool s)
    (maxSteps : Nat)
    (h :
      forall omega, C.success omega ->
        ctmBoundedExecToWitness
          (s := s) M cfg0 cfg1 maxSteps omega) :
    Probability.SuccessContract P :=
  Probability.SuccessContract.consequence hP C
    (boundedExecToSuccess (s := s) M cfg0 cfg1 maxSteps)
    (by
      intro omega hsuccess
      exact boundedExecToSuccess_of_ctmBoundedExecToWitness
        (s := s) M cfg0 cfg1 maxSteps omega
        (h omega hsuccess))

def execSuccessContract_of_ctmBoundedExecToWitness
    {Omega : Type w} {P : Probability.ProbSpec Omega}
    (hP : Probability.ProbAxioms P)
    (C : Probability.SuccessContract P)
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    (cfg0 cfg1 : Omega -> Cfg Q Bool s)
    (maxSteps : Nat)
    (h :
      forall omega, C.success omega ->
        ctmBoundedExecToWitness
          (s := s) M cfg0 cfg1 maxSteps omega) :
    Probability.SuccessContract P :=
  Probability.SuccessContract.consequence hP C
    (execSuccess (s := s) M cfg0 cfg1)
    (by
      intro omega hsuccess
      exact ctmBoundedExecToWitness_imp_execSuccess
        (s := s) M cfg0 cfg1 maxSteps omega
        (h omega hsuccess))

def boundedCoverabilitySuccessContract_of_ctmBoundedCoverabilityWitness
    {Omega : Type w} {P : Probability.ProbSpec Omega}
    (hP : Probability.ProbAxioms P)
    (C : Probability.SuccessContract P)
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    (cfg0 : Omega -> Cfg Q Bool s)
    (target : Omega -> State (FourPhaseSpecies Q))
    (maxSteps : Nat)
    (h :
      forall omega, C.success omega ->
        ctmBoundedCoverabilityWitness
          (s := s) M cfg0 target maxSteps omega) :
    Probability.SuccessContract P :=
  Probability.SuccessContract.consequence hP C
    (boundedCoverabilitySuccess (s := s) M cfg0 target maxSteps)
    (by
      intro omega hsuccess
      exact boundedCoverabilitySuccess_of_ctmBoundedCoverabilityWitness
        (s := s) M cfg0 target maxSteps omega
        (h omega hsuccess))

def boundedSpeciesCoverabilitySuccessContract_of_ctmBoundedSpeciesWitness
    {Omega : Type w} {P : Probability.ProbSpec Omega}
    (hP : Probability.ProbAxioms P)
    (C : Probability.SuccessContract P)
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    (cfg0 : Omega -> Cfg Q Bool s)
    (species : FourPhaseSpecies Q)
    (amount maxSteps : Nat)
    (h :
      forall omega, C.success omega ->
        ctmBoundedSpeciesCoverabilityWitness
          (s := s) M cfg0 species amount maxSteps omega) :
    Probability.SuccessContract P :=
  Probability.SuccessContract.consequence hP C
    (boundedSpeciesCoverabilitySuccess
      (s := s) M cfg0 species amount maxSteps)
    (by
      intro omega hsuccess
      exact boundedSpeciesCoverabilitySuccess_of_ctmBoundedSpeciesCoverabilityWitness
        (s := s) M cfg0 species amount maxSteps omega
        (h omega hsuccess))

def boundedTapeSpeciesCoverabilitySuccessContract_of_ctmBoundedTapeWitness
    {Omega : Type w} {P : Probability.ProbSpec Omega}
    (hP : Probability.ProbAxioms P)
    (C : Probability.SuccessContract P)
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    (cfg0 : Omega -> Cfg Q Bool s)
    (amount maxSteps : Nat)
    (h :
      forall omega, C.success omega ->
        ctmBoundedTapeSpeciesCoverabilityWitness
          (s := s) M cfg0 amount maxSteps omega) :
    Probability.SuccessContract P :=
  Probability.SuccessContract.consequence hP C
    (boundedSpeciesCoverabilitySuccess
      (s := s) M cfg0 FourPhaseSpecies.tape amount maxSteps)
    (by
      intro omega hsuccess
      exact boundedSpeciesCoverabilitySuccess_of_ctmBoundedTapeSpeciesCoverabilityWitness
        (s := s) M cfg0 amount maxSteps omega
        (h omega hsuccess))

def coverabilitySuccessContract_of_ctmBoundedCoverabilityWitness
    {Omega : Type w} {P : Probability.ProbSpec Omega}
    (hP : Probability.ProbAxioms P)
    (C : Probability.SuccessContract P)
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    (cfg0 : Omega -> Cfg Q Bool s)
    (target : Omega -> State (FourPhaseSpecies Q))
    (maxSteps : Nat)
    (h :
      forall omega, C.success omega ->
        ctmBoundedCoverabilityWitness
          (s := s) M cfg0 target maxSteps omega) :
    Probability.SuccessContract P :=
  Probability.SuccessContract.consequence hP C
    (coverabilitySuccess (s := s) M cfg0 target)
    (by
      intro omega hsuccess
      exact ctmBoundedCoverabilityWitness_imp_coverabilitySuccess
        (s := s) M cfg0 target maxSteps omega
        (h omega hsuccess))

def speciesCoverabilitySuccessContract_of_ctmBoundedSpeciesWitness
    {Omega : Type w} {P : Probability.ProbSpec Omega}
    (hP : Probability.ProbAxioms P)
    (C : Probability.SuccessContract P)
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    (cfg0 : Omega -> Cfg Q Bool s)
    (species : FourPhaseSpecies Q)
    (amount maxSteps : Nat)
    (h :
      forall omega, C.success omega ->
        ctmBoundedSpeciesCoverabilityWitness
          (s := s) M cfg0 species amount maxSteps omega) :
    Probability.SuccessContract P :=
  Probability.SuccessContract.consequence hP C
    (speciesCoverabilitySuccess (s := s) M cfg0 species amount)
    (by
      intro omega hsuccess
      exact ctmBoundedSpeciesCoverabilityWitness_imp_speciesCoverabilitySuccess
        (s := s) M cfg0 species amount maxSteps omega
        (h omega hsuccess))

def tapeSpeciesCoverabilitySuccessContract_of_ctmBoundedTapeWitness
    {Omega : Type w} {P : Probability.ProbSpec Omega}
    (hP : Probability.ProbAxioms P)
    (C : Probability.SuccessContract P)
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    (cfg0 : Omega -> Cfg Q Bool s)
    (amount maxSteps : Nat)
    (h :
      forall omega, C.success omega ->
        ctmBoundedTapeSpeciesCoverabilityWitness
          (s := s) M cfg0 amount maxSteps omega) :
    Probability.SuccessContract P :=
  Probability.SuccessContract.consequence hP C
    (speciesCoverabilitySuccess (s := s) M cfg0 FourPhaseSpecies.tape amount)
    (by
      intro omega hsuccess
      exact ctmBoundedTapeSpeciesCoverabilityWitness_imp_speciesCoverabilitySuccess
        (s := s) M cfg0 amount maxSteps omega
        (h omega hsuccess))

/--
Deadline consequence for a fixed CTM endpoint.

The deadline is an external CTM-side contract. The CRN conclusion is only a
deterministic macro firing-count bound for the intended scheduled execution.
-/
def boundedExecToSuccessContract_of_deadline
    {Omega : Type w} {P : Probability.ProbSpec Omega}
    (hP : Probability.ProbAxioms P)
    (D : Probability.DeadlineContract P)
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    (cfg0 cfg1 : Omega -> Cfg Q Bool s)
    (hsteps :
      forall omega,
        D.finishTime omega <= D.deadline ->
          (M.detSystem (s := s)).steps?
            (D.finishTime omega) (cfg0 omega) = some (cfg1 omega)) :
    Probability.SuccessContract P :=
  Probability.SuccessContract.consequence hP
    D.toSuccessContract
    (boundedExecToSuccess (s := s) M cfg0 cfg1 D.deadline)
    (by
      intro omega hOnTime
      exact boundedExecToSuccess_of_ctmBoundedExecToWitness
        (s := s) M cfg0 cfg1 D.deadline omega
        ⟨D.finishTime omega, hOnTime, hsteps omega hOnTime⟩)

/--
Safer spelling of `boundedExecToSuccessContract_of_deadline`.

The source deadline is CTM-side; the CRN conclusion is a deterministic macro
firing-count bound to a fixed endpoint.
-/
def boundedFiringCountExecToSuccessContract_of_ctmDeadline
    {Omega : Type w} {P : Probability.ProbSpec Omega}
    (hP : Probability.ProbAxioms P)
    (D : Probability.DeadlineContract P)
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    (cfg0 cfg1 : Omega -> Cfg Q Bool s)
    (hsteps :
      forall omega,
        D.finishTime omega <= D.deadline ->
          (M.detSystem (s := s)).steps?
            (D.finishTime omega) (cfg0 omega) = some (cfg1 omega)) :
    Probability.SuccessContract P :=
  boundedExecToSuccessContract_of_deadline
    (s := s) hP D M cfg0 cfg1 hsteps

def boundedCoverabilitySuccessContract_of_deadline
    {Omega : Type w} {P : Probability.ProbSpec Omega}
    (hP : Probability.ProbAxioms P)
    (D : Probability.DeadlineContract P)
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    (cfg0 : Omega -> Cfg Q Bool s)
    (target : Omega -> State (FourPhaseSpecies Q))
    (hsteps :
      forall omega,
        D.finishTime omega <= D.deadline ->
          exists cfg' : Cfg Q Bool s,
            (M.detSystem (s := s)).steps?
              (D.finishTime omega) (cfg0 omega) = some cfg' /\
            Covers (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg'))
              (target omega)) :
    Probability.SuccessContract P :=
  Probability.SuccessContract.consequence hP
    D.toSuccessContract
    (boundedCoverabilitySuccess (s := s) M cfg0 target D.deadline)
    (by
      intro omega hOnTime
      rcases hsteps omega hOnTime with ⟨cfg', hrun, hCovers⟩
      exact boundedCoverabilitySuccess_of_ctmBoundedCoverabilityWitness
        (s := s) M cfg0 target D.deadline omega
        ⟨D.finishTime omega, hOnTime, cfg', hrun, hCovers⟩)

/-- Safer spelling of `boundedCoverabilitySuccessContract_of_deadline`. -/
def boundedFiringCountCoverabilitySuccessContract_of_ctmDeadline
    {Omega : Type w} {P : Probability.ProbSpec Omega}
    (hP : Probability.ProbAxioms P)
    (D : Probability.DeadlineContract P)
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    (cfg0 : Omega -> Cfg Q Bool s)
    (target : Omega -> State (FourPhaseSpecies Q))
    (hsteps :
      forall omega,
        D.finishTime omega <= D.deadline ->
          exists cfg' : Cfg Q Bool s,
            (M.detSystem (s := s)).steps?
              (D.finishTime omega) (cfg0 omega) = some cfg' /\
            Covers (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg'))
              (target omega)) :
    Probability.SuccessContract P :=
  boundedCoverabilitySuccessContract_of_deadline
    (s := s) hP D M cfg0 target hsteps

def coverabilitySuccessContract_of_deadline
    {Omega : Type w} {P : Probability.ProbSpec Omega}
    (hP : Probability.ProbAxioms P)
    (D : Probability.DeadlineContract P)
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    (cfg0 : Omega -> Cfg Q Bool s)
    (target : Omega -> State (FourPhaseSpecies Q))
    (hsteps :
      forall omega,
        D.finishTime omega <= D.deadline ->
          exists cfg' : Cfg Q Bool s,
            (M.detSystem (s := s)).steps?
              (D.finishTime omega) (cfg0 omega) = some cfg' /\
            Covers (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg'))
              (target omega)) :
    Probability.SuccessContract P :=
  coverabilitySuccessContract_of_boundedCoverabilitySuccessContract
    (s := s) hP
    (boundedCoverabilitySuccessContract_of_deadline
      (s := s) hP D M cfg0 target hsteps)
    M cfg0 target D.deadline
    (by
      intro omega hsuccess
      exact hsuccess)

def boundedSpeciesCoverabilitySuccessContract_of_deadline
    {Omega : Type w} {P : Probability.ProbSpec Omega}
    (hP : Probability.ProbAxioms P)
    (D : Probability.DeadlineContract P)
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    (cfg0 : Omega -> Cfg Q Bool s)
    (species : FourPhaseSpecies Q)
    (amount : Nat)
    (hsteps :
      forall omega,
        D.finishTime omega <= D.deadline ->
          exists cfg' : Cfg Q Bool s,
            (M.detSystem (s := s)).steps?
              (D.finishTime omega) (cfg0 omega) = some cfg' /\
            amount <=
              FourPhaseEncoding.enc (MicroCfg.ofCTM cfg') species) :
    Probability.SuccessContract P :=
  Probability.SuccessContract.consequence hP
    D.toSuccessContract
    (boundedSpeciesCoverabilitySuccess
      (s := s) M cfg0 species amount D.deadline)
    (by
      intro omega hOnTime
      rcases hsteps omega hOnTime with ⟨cfg', hrun, hAmount⟩
      exact boundedSpeciesCoverabilitySuccess_of_ctmBoundedSpeciesCoverabilityWitness
        (s := s) M cfg0 species amount D.deadline omega
        ⟨D.finishTime omega, hOnTime, cfg', hrun, hAmount⟩)

def speciesCoverabilitySuccessContract_of_deadline
    {Omega : Type w} {P : Probability.ProbSpec Omega}
    (hP : Probability.ProbAxioms P)
    (D : Probability.DeadlineContract P)
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    (cfg0 : Omega -> Cfg Q Bool s)
    (species : FourPhaseSpecies Q)
    (amount : Nat)
    (hsteps :
      forall omega,
        D.finishTime omega <= D.deadline ->
          exists cfg' : Cfg Q Bool s,
            (M.detSystem (s := s)).steps?
              (D.finishTime omega) (cfg0 omega) = some cfg' /\
            amount <=
              FourPhaseEncoding.enc (MicroCfg.ofCTM cfg') species) :
    Probability.SuccessContract P :=
  speciesCoverabilitySuccessContract_of_boundedSpeciesCoverabilitySuccessContract
    (s := s) hP
    (boundedSpeciesCoverabilitySuccessContract_of_deadline
      (s := s) hP D M cfg0 species amount hsteps)
    M cfg0 species amount D.deadline
    (by
      intro omega hsuccess
      exact hsuccess)

def boundedTapeSpeciesCoverabilitySuccessContract_of_deadline
    {Omega : Type w} {P : Probability.ProbSpec Omega}
    (hP : Probability.ProbAxioms P)
    (D : Probability.DeadlineContract P)
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    (cfg0 : Omega -> Cfg Q Bool s)
    (amount : Nat)
    (hsteps :
      forall omega,
        D.finishTime omega <= D.deadline ->
          exists cfg' : Cfg Q Bool s,
            (M.detSystem (s := s)).steps?
              (D.finishTime omega) (cfg0 omega) = some cfg' /\
            amount <= Encoding.base3Val cfg'.tape) :
    Probability.SuccessContract P :=
  Probability.SuccessContract.consequence hP
    D.toSuccessContract
    (boundedSpeciesCoverabilitySuccess
      (s := s) M cfg0 FourPhaseSpecies.tape amount D.deadline)
    (by
      intro omega hOnTime
      rcases hsteps omega hOnTime with ⟨cfg', hrun, hAmount⟩
      exact boundedSpeciesCoverabilitySuccess_of_ctmBoundedTapeSpeciesCoverabilityWitness
        (s := s) M cfg0 amount D.deadline omega
        ⟨D.finishTime omega, hOnTime, cfg', hrun, hAmount⟩)

def tapeSpeciesCoverabilitySuccessContract_of_deadline
    {Omega : Type w} {P : Probability.ProbSpec Omega}
    (hP : Probability.ProbAxioms P)
    (D : Probability.DeadlineContract P)
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    (cfg0 : Omega -> Cfg Q Bool s)
    (amount : Nat)
    (hsteps :
      forall omega,
        D.finishTime omega <= D.deadline ->
          exists cfg' : Cfg Q Bool s,
            (M.detSystem (s := s)).steps?
              (D.finishTime omega) (cfg0 omega) = some cfg' /\
            amount <= Encoding.base3Val cfg'.tape) :
    Probability.SuccessContract P :=
  speciesCoverabilitySuccessContract_of_boundedSpeciesCoverabilitySuccessContract
    (s := s) hP
    (boundedTapeSpeciesCoverabilitySuccessContract_of_deadline
      (s := s) hP D M cfg0 amount hsteps)
    M cfg0 FourPhaseSpecies.tape amount D.deadline
    (by
      intro omega hsuccess
      exact hsuccess)

def coverabilitySuccessContract_of_ctmSuccess
    {Omega : Type w} {P : Probability.ProbSpec Omega}
    (hP : Probability.ProbAxioms P)
    (C : Probability.SuccessContract P)
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    (cfg0 : Omega -> Cfg Q Bool s)
    (target : Omega -> State (FourPhaseSpecies Q))
    (h :
      forall omega, C.success omega ->
        ctmCoverabilityWitness (s := s) M cfg0 target omega) :
    Probability.SuccessContract P :=
  Probability.SuccessContract.consequence hP C
    (coverabilitySuccess (s := s) M cfg0 target)
    (by
      intro omega hsuccess
      exact ctmCoverabilityWitness_imp_coverabilitySuccess
        (s := s) M cfg0 target omega (h omega hsuccess))

def speciesCoverabilitySuccessContract_of_ctmSuccess
    {Omega : Type w} {P : Probability.ProbSpec Omega}
    (hP : Probability.ProbAxioms P)
    (C : Probability.SuccessContract P)
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    (cfg0 : Omega -> Cfg Q Bool s)
    (species : FourPhaseSpecies Q)
    (amount : Nat)
    (h :
      forall omega, C.success omega ->
        ctmSpeciesCoverabilityWitness
          (s := s) M cfg0 species amount omega) :
    Probability.SuccessContract P :=
  Probability.SuccessContract.consequence hP C
    (speciesCoverabilitySuccess (s := s) M cfg0 species amount)
    (by
      intro omega hsuccess
      exact ctmSpeciesCoverabilityWitness_imp_speciesCoverabilitySuccess
        (s := s) M cfg0 species amount omega (h omega hsuccess))

def tapeSpeciesCoverabilitySuccessContract_of_ctmSuccess
    {Omega : Type w} {P : Probability.ProbSpec Omega}
    (hP : Probability.ProbAxioms P)
    (C : Probability.SuccessContract P)
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    (cfg0 : Omega -> Cfg Q Bool s)
    (amount : Nat)
    (h :
      forall omega, C.success omega ->
        ctmTapeSpeciesCoverabilityWitness
          (s := s) M cfg0 amount omega) :
    Probability.SuccessContract P :=
  Probability.SuccessContract.consequence hP C
    (speciesCoverabilitySuccess (s := s) M cfg0 FourPhaseSpecies.tape amount)
    (by
      intro omega hsuccess
      exact ctmTapeSpeciesCoverabilityWitness_imp_speciesCoverabilitySuccess
        (s := s) M cfg0 amount omega (h omega hsuccess))

end FourPhaseMacroModule

end CTM

end Ripple.sCRNUniversality
