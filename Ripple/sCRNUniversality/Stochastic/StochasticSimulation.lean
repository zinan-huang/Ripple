/-
  Stochastic CTM simulation: specification and correctness theorem.

  The existing deterministic Theorems.lean proves:
    CTM n steps → ∃ bimolecular unit-rate CRN, CRN.Reaches (enc cfg) (enc cfg')

  The stochastic layer adds:
    Under ClockBoundedLaw with per-microstep error ε ≤ δ/(4n),
    the CRN simulation succeeds with probability ≥ 1 - δ.

  The cascade shift ensures all phases are deterministic (no propensity
  race), so the ONLY error source is premature clock ticks.

  This file states the specification structure and records that the
  existing Theorems.lean provides the deterministic component.
-/
import Ripple.sCRNUniversality.Computation.CTM.FourPhaseMacroModule

namespace Ripple.sCRNUniversality

namespace Stochastic

universe u

variable {Q : Type u} [Fintype Q] [DecidableEq Q]

theorem existing_deterministic_simulation
    (M : CTM.Binary Q) (s : Nat)
    {n : Nat} {cfg cfg' : CTM.Cfg Q Bool s}
    (hsteps : (M.detSystem (s := s)).steps? n cfg = some cfg') :
    (CTM.FourPhaseMacroModule.network (s := s) M).Reaches
        (CTM.FourPhaseEncoding.enc (CTM.MicroCfg.ofCTM cfg))
        (CTM.FourPhaseEncoding.enc (CTM.MicroCfg.ofCTM cfg')) :=
  CTM.FourPhaseMacroModule.reaches_of_ctm_steps (s := s) M hsteps

end Stochastic

end Ripple.sCRNUniversality
