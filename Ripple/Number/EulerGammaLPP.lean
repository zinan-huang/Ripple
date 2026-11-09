/-
  Ripple.Number.EulerGammaLPP — Euler's constant γ is LPP-computable ([LPP] Corollary 19).

  `euler_gamma_is_realtime` (Huang's thesis, Theorem 3.3.4) gives a bounded ℚ-PIVP computing γ;
  `IsCRNComputable.isLPPComputable` (the GPAC ⇒ LPP direction of the [LPP] Main Theorem, via the
  zero-initial-value CRN of `Ripple.crn_of_certified`) applies since `1/2 < γ < 2/3`.
-/

import Ripple.Number.EulerGamma
import Ripple.Core.CRNReadout

namespace Ripple.Number

/-- [LPP] Corollary 19: Euler's constant `γ` is computable by a deterministic large-population
protocol. -/
theorem euler_gamma_is_lpp_computable : IsLPPComputable Real.eulerMascheroniConstant :=
  euler_gamma_is_realtime.isCRNComputable.isLPPComputable
    ((by norm_num : (0 : ℝ) ≤ 1 / 2).trans Real.one_half_lt_eulerMascheroniConstant.le)
    (Real.eulerMascheroniConstant_lt_two_thirds.le.trans (by norm_num))

end Ripple.Number
