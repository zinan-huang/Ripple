import Ripple.sCRNUniversality.Core.Petri
import Ripple.sCRNUniversality.Decidability.Coverability
import Ripple.sCRNUniversality.CTM.FourPhaseBimolecularRefinement
import Ripple.sCRNUniversality.Stochastic.RaceBoundOfPropensityDominance
import Ripple.sCRNUniversality.Stochastic.MassAction.RaceLaw
import Ripple.sCRNUniversality.Stochastic.MassAction.UniformRaceBound
import Ripple.sCRNUniversality.Stochastic.StatePairTransferPropensity

namespace Ripple.sCRNUniversality

namespace PaperTheorems

universe u v

/-!
Paper-facing statements for Soloveichik, Cook, Winfree and Bruck, "Computation
with finite stochastic chemical reaction networks" (Natural Computing 7 (2008)
615-633; Caltech technical report etr085v2, `ref/SCWB-2007-finite-stochastic-CRN-etr085v2.pdf`).

What is formalized:

* §2 of the paper, CRN and Petri-net semantics agree:
  `crn_reaches_iff_petri_reaches`, `crn_coverability_iff_petri_coverability`.
* Theorem 4.2 (coverability is decidable): the computable instances
  `Decidability.petriCoverabilityDecidable` and
  `Decidability.networkCoverabilityDecidable`, built from the backward algorithm
  and its termination (`Decidability.exists_fuel_saturates`, Dickson's lemma) and
  the characterization `Decidability.coverable_iff_mem_up_fixpoint`.

What is not formalized: Theorem 3.1 (register machines with error at most δ),
Theorems 3.2 and 4.1 (Turing machines with error at most δ, bounded and
unbounded).  See `OPEN_PROBLEMS.md` §6.2.  The four-phase CTM development
in `CTM/` proves that a correct execution exists in a network that does not
depend on the machine; it is not a simulation statement.
-/

variable {S : Type u}

theorem crn_reaches_iff_petri_reaches
    (N : Network S) (z z' : State S) :
    N.Reaches z z' <-> (N.toPetri).Reaches z z' := by
  exact (Network.toPetri_reaches_iff N z z').symm

theorem crn_coverability_iff_petri_coverability
    (N : Network S) (z0 target : State S) :
    N.CoverableFrom z0 target <-> (N.toPetri).CoverableFrom z0 target := by
  exact (Network.toPetri_coverable_iff N z0 target).symm

/-- SCWB Theorem 4.2, CRN form: coverability in a finite CRN is decidable,
by a computable procedure. -/
example {S : Type u} [Fintype S] [DecidableEq S] (N : Network.{u, v} S)
    (z0 target : State S) : Decidable (N.CoverableFrom z0 target) :=
  Decidability.networkCoverabilityDecidable N z0 target

end PaperTheorems

end Ripple.sCRNUniversality
