/-
  Ripple.Core.CRNPipeline — GPAC-to-CRN Pipeline

  Formalizes the pipeline from [BAC] §7:
    Bounded GPAC → Dual-rail encoding → Readout subtraction → CRN

  Key results:
  - Dual-rail encoding is exact (from [RTCRN2], [Fages 2017])
  - Readout subtraction acts as a low-pass filter
  - Time complexity is preserved through the full pipeline

  The low-pass filter analysis ([BAC] §7.2):
    δ̇ + α·δ = α·ε(t)
  where ε is the input error and δ is the readout error.

  Two regimes:
  - Input-limited: ε decays slower than e^{-αt} → δ(t) ~ ε(t)
  - Module-limited: ε decays faster than e^{-αt} → δ(t) ~ Ce^{-αt}
-/

import Ripple.Core.Compilation
import Ripple.DualRail.UnitIntervalCertification
import Ripple.LPP.Stages
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Ripple

/-- A CRN (Chemical Reaction Network) is a bounded PIVP where all
  variables represent non-negative species concentrations and the
  dynamics follow mass-action kinetics. -/
structure CRN (d : ℕ) extends PIVP d where
  /-- All species concentrations are non-negative. -/
  nonneg : ∀ i : Fin d, 0 ≤ init i

/-- **CRN readout closure** ([BAC] §7).

A zero-initial-value certified computation of `α ∈ [0, 1]` gives a certified computation of the
same `α` together with a `PolyCRNDecomposition` of its field, i.e. a concrete mass-action CRN
witness. This is the [BAC] §7 readout content: the dual-rail + subtraction readout (DNA25
annihilation + Lemma 8) is CRN-implementable. The induced modulus is the explicit chain of
Stage A + Stage B composed with the input modulus (see
`Ripple.DualRail.btc_to_cbtc_pcd_of_unit_interval`); the sharpened modulus bound of [BAC]
Thm 7.3 (asymptotic low-pass filter regimes) is not stated here. -/
theorem crn_readout_preserves_complexity {d : ℕ} {α : ℝ}
    (btc : CertifiedBoundedTimeComputable d α)
    (h_zero : ∀ j : Fin d, btc.pivp.init j = 0)
    (hα_lo : 0 ≤ α) (hα_hi : α ≤ 1) :
    ∃ (d' : ℕ) (cbtc' : CertifiedBoundedTimeComputable d' α),
      Nonempty (PolyCRNDecomposition d' cbtc'.pivp) := by
  haveI : NeZero d := ⟨by have := btc.pivp.output.isLt; omega⟩
  have h_zero' : ∀ j, btc.toSemantic.pivp.init j = 0 := by
    intro j
    change ((btc.pivp.init j : ℚ) : ℝ) = 0
    rw [h_zero j, Rat.cast_zero]
  exact Ripple.DualRail.btc_to_cbtc_pcd_of_unit_interval btc.toSemantic
    btc.pivp.field (fun _ _ => rfl) h_zero' hα_lo hα_hi

/-- **Exponentiation closure** ([BAC] Thm 6.1), conditional reduction.

Conditional on `h_exp` (closure of `IsCRNComputable` under the real exponential) and `h_log`
(closure under the real logarithm on positive reals), which are the content of [BAC] Thm 6.1
and are not proved in this repository: then `α^β = exp(log α · β)` is CRN-computable.
Multiplication closure is discharged by `crn_computable_mul` (the certified product
tracker). -/
theorem closure_exponentiation_via_exp_log {α β : ℝ} (hα : 0 < α)
    (ha : IsCRNComputable α) (hb : IsCRNComputable β)
    (h_exp : ∀ γ : ℝ, IsCRNComputable γ → IsCRNComputable (Real.exp γ))
    (h_log : ∀ γ : ℝ, 0 < γ → IsCRNComputable γ → IsCRNComputable (Real.log γ)) :
    IsCRNComputable (Real.rpow α β) := by
  change IsCRNComputable (α ^ β)
  rw [Real.rpow_def_of_pos hα β]
  exact h_exp _ (crn_computable_mul (h_log α hα ha) hb)

end Ripple
