import Ripple.Kurtz.StrongApprox.BrownianCodeLaw
import Ripple.Kurtz.StrongApprox.DyadicPreBrownian

/-!
# The reference all-time KMT Brownian path is pre-Brownian

The reference path `referenceBrownian` of the KMT transfer is the all-time KMT Brownian path
restricted to nonnegative times. Its dyadic increment laws on every horizon `2 ^ N` and its zero
initial value give all finite-dimensional Brownian laws, so it is pre-Brownian. This discharges
the premise `hRefBrownian` of the code-law identification and of the transferred KMT bound.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace Ripple.Kurtz.StrongApprox.KMTTransfer

open AllTimeKMT

/-- The reference all-time KMT Brownian path has the finite-dimensional laws of a Brownian
motion at all nonnegative real times. -/
theorem referenceBrownian_isPreBrownian :
    IsPreBrownian referenceBrownian allTimeKMTMeasure :=
  allDyadicBrownian_isPreBrownian
    (W := fun t ω => allTimeKMTBrownian t ω)
    AllTimeKMTBrownianLaw.allTimeKMTBrownian_dyadicBrownianOn
    (Filter.Eventually.of_forall AllTimeKMTLaws.allTimeKMTBrownian_zero_time)

/-- Every pre-Brownian process has the KMT Brownian code law. -/
theorem kmtBrownianCodeLaw_eq
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {β : ℝ≥0 → Ω → ℝ} [IsPreBrownian β P] :
    P.map (brownianCodeOf β) = kmtBrownianCodeLaw :=
  kmtBrownianCodeLaw_eq_of_isPreBrownian referenceBrownian_isPreBrownian

/-- The transferred KMT bound for an arbitrary pre-Brownian process with measurable,
almost surely continuous paths. -/
theorem kmtTransfer_bound_ae_of_preBrownian
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {β : ℝ≥0 → Ω → ℝ} [IsPreBrownian β P] (hβ : ∀ t, Measurable (β t))
    (hcont : ∀ᵐ ω ∂P, Continuous fun t => β t ω) :
    ∀ᵐ z ∂kmtTransferMeasure P (brownianCodeOf β) (measurable_brownianCodeOf hβ),
      ∀ t : ℝ≥0,
        |(cellPath (t : ℝ) z.2 : ℝ) - (t : ℝ) - β t z.1| ≤
          (kmtCodeXi (brownianCodeOf β z.1) z.2).toReal * Real.log (max 2 (t : ℝ)) :=
  kmtTransfer_bound_ae_of_isPreBrownian referenceBrownian_isPreBrownian hβ hcont

end Ripple.Kurtz.StrongApprox.KMTTransfer
