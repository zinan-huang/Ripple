-- Ripple/PopulationProtocol/ExactMajority/Probability/LateSamplingShallowCorollary.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.LateSamplingClassReceiptArithmetic
import Ripple.PopulationProtocol.ExactMajority.Probability.LateSamplingShallowTransport

/-!
# The two-class floor with the shallow-transport premise discharged

`LateSamplingShallowTransport.scaledShallowPositive_seed_mono` is exactly the
`hshallowTransport` premise of `LateSamplingClassReceiptArithmetic.two_class_at`
and `shallow_two_class_at`.
-/

noncomputable section

namespace Ripple.PopulationProtocol.ExactMajority.LateSamplingShallowCorollary

open TimeTheorem StageEventSpec
open LateStrengthening
open LateSamplingSeedReceipt

variable {n : ℕ}

/-- `two_class_at` for an actual observed pre-Phase-6 prefix: the shallow
transport input is now supplied by the prefix itself. -/
theorem two_class_at_of_prefix
    {init : InputCfg n} {ω : InputLog n}
    {a s t v M ell : ℕ} {σ : Sign}
    (hpath : LateF6OriginalLaw.Prefix init ω a s t)
    (hseed : LateSamplingSeedReceipt.LateSamplingSeedReceipt init M ell σ
      (trace init ω s))
    (hsv : s ≤ v) (hvt : v ≤ t)
    (hcount : timeMainCount (trace init ω v) = M)
    (hlevelWeight :
      (bandCount σ ell 0 (trace init ω v) : ℚ) ≤
        scaledShallowPositive σ ell (trace init ω v))
    (hmass :
      592 * M ≤
        3000 * bandCount σ ell 0 (trace init ω v) +
        1000 * bandCount σ (ell + 1) 0 (trace init ω v))
    (hpartition :
      bandCount σ ell 1 (trace init ω v) =
        bandCount σ ell 0 (trace init ω v) +
        bandCount σ (ell + 1) 0 (trace init ω v)) :
    5698 * M ≤ 10000 * bandCount σ ell 1 (trace init ω v) ∨
      939 * M ≤ 1000 * bandCount σ ell 1 (trace init ω v) :=
  LateSamplingClassReceiptArithmetic.two_class_at hpath hseed hsv hvt hcount
    (LateSamplingShallowTransport.scaledShallowPositive_seed_mono hpath hsv hvt)
    hlevelWeight hmass hpartition

end Ripple.PopulationProtocol.ExactMajority.LateSamplingShallowCorollary

end
