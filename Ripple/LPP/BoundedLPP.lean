/-
  Ripple.LPP.BoundedLPP — bounded CRNs on [0, 1] compile to large-population protocols
  ([LPP] Main Theorem, GPAC ⇒ LPP direction, for the CRN form of [LPP] §3).

  The input is a certified computation (`CertifiedBoundedTimeComputable`: bounded ℚ-PIVP with a
  modulus) whose field has a `PolyCRNDecomposition`. The compiler itself is
  `isPLPPComputable_of_certified` / `isLPPComputable_of_certified` (`Ripple.LPP.Compiler`:
  Stage 1 v-variables with ℚ coefficients, Stage 2 balancing dilation, Stage 3 formally
  conservative symmetric lift, Stage 4 PLPP table, readout, and Theorem 17 for the deterministic
  form). The former sharp-bound and real-coefficient variants of this module concluded the
  field-unrestricted predicate and were removed in the 2026-11 S1 refactor.
-/

import Ripple.LPP.Compiler
import Ripple.Core.Compilation

namespace Ripple

/-- **[LPP] Main Theorem (GPAC ⇒ PLPP), CRN form.** -/
theorem bounded_crn_is_plpp_computable {α : ℝ} {d : ℕ}
    (hα01 : 0 ≤ α ∧ α ≤ 1)
    (cbtc : CertifiedBoundedTimeComputable d α)
    (pcd : PolyCRNDecomposition d cbtc.pivp) :
    IsPLPPComputable α :=
  isPLPPComputable_of_certified hα01 cbtc pcd

/-- **[LPP] Main Theorem (GPAC ⇒ LPP), CRN form.** Every `α ∈ [0, 1]` computed by a bounded
ℚ-PIVP with a CRN decomposition is computed by a deterministic LPP. -/
theorem bounded_crn_is_lpp_computable {α : ℝ} {d : ℕ}
    (hα01 : 0 ≤ α ∧ α ≤ 1)
    (cbtc : CertifiedBoundedTimeComputable d α)
    (pcd : PolyCRNDecomposition d cbtc.pivp) :
    IsLPPComputable α :=
  isLPPComputable_of_certified hα01 cbtc pcd

end Ripple
