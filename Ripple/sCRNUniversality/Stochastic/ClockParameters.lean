/-
  Clock module instantiation for the cascade four-phase CRN.

  The ClockBoundedLaw requires a per-microstep error bound:
  at each firing, P(wrong reaction) ≤ ε.

  For the cascade four-phase construction:
  - Read/erase/write phases: deterministic (unique enabled reaction)
    → "wrong reaction" = clock tick reaction
    → P(wrong) = propensity(clock_tick) / total_propensity
  - Cascade shift sub-phases: deterministic (unique enabled reaction)
    → same analysis as above

  The clock tick's propensity is λ = k · #C_1 / v (at most k/v when #C_1 ≤ 1).
  The memory reaction's propensity is at least k · 1 / v (at least one molecule).

  So P(clock tick wins) ≤ λ / (λ + ρ_memory).

  By the SCWB paper's clock analysis (Lemma A.2-A.4):
  - The effective clock tick rate λ ≤ O(k / (v · #A^(l-1)))
  - Setting #A = Θ((4n/δ)^{1/(l-1)}) gives P(wrong) ≤ δ/(4n) per microstep

  This module states the connection between ClockCRN parameters and
  the ClockBoundedLaw's per-microstep error bound.
-/
import Ripple.sCRNUniversality.Stochastic.JumpPathLaw

namespace Ripple.sCRNUniversality

namespace Stochastic

universe u v w

structure ClockParameters where
  chainLength : Nat
  hChainPos : 0 < chainLength
  accuracyCount : Nat
  hAccPos : 0 < accuracyCount
  rateConstant : NNRat
  volume : Nat
  hVolPos : 0 < volume

noncomputable def ClockParameters.effectiveTickRate (p : ClockParameters) : NNRat :=
  p.rateConstant / (p.accuracyCount ^ (p.chainLength - 1))

end Stochastic

end Ripple.sCRNUniversality
