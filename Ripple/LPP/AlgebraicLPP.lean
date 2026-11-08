/-
  Ripple.LPP.AlgebraicLPP — [LPP] Corollary 18: every algebraic number in [0, 1] is computable
  by a (deterministic) large-population protocol.

  The certified CRN for an algebraic `α ≥ 0` (`algebraic_is_certified_crn`: a bounded ℚ-PIVP with
  a `PolyCRNDecomposition`) is compiled by the faithful compiler `isLPPComputable_of_certified`
  ([LPP] Main Theorem, GPAC ⇒ LPP, with Theorem 17). The boundary values `0` and `1` are also
  given directly by idle protocols (`isLPPComputable_rat`).
-/

import Ripple.LPP.Compiler
import Ripple.LPP.AlgebraicConstruction

namespace Ripple

/-- `0` is computed by a deterministic LPP (the idle protocol). -/
theorem zero_lpp : IsLPPComputable (0 : ℝ) := by
  have h := isLPPComputable_rat 0 le_rfl zero_le_one
  rwa [Rat.cast_zero] at h

/-- `1` is computed by a deterministic LPP (the idle protocol). -/
theorem one_lpp : IsLPPComputable (1 : ℝ) := by
  have h := isLPPComputable_rat 1 zero_le_one le_rfl
  rwa [Rat.cast_one] at h

/-- The boundary values `0` and `1` are LPP-computable. -/
theorem algebraic_lpp_computable_boundary_cases {α : ℝ} (hα_bdry : α = 0 ∨ α = 1) :
    IsLPPComputable α := by
  rcases hα_bdry with rfl | rfl
  · exact zero_lpp
  · exact one_lpp

/-- **[LPP] Corollary 18, PLPP form.** Every algebraic `α ∈ [0, 1]` is PLPP-computable. -/
theorem algebraic_plpp_computable {α : ℝ}
    (hα01 : 0 ≤ α ∧ α ≤ 1)
    (halg : ∃ p : Polynomial ℤ, p ≠ 0 ∧ (Polynomial.aeval α p : ℝ) = 0) :
    IsPLPPComputable α := by
  obtain ⟨d, cbtc, pcd, -⟩ := algebraic_is_certified_crn hα01.1 halg
  exact isPLPPComputable_of_certified hα01 cbtc pcd

/-- **[LPP] Corollary 18.** Every algebraic `α ∈ [0, 1]` is computable by a deterministic LPP. -/
theorem algebraic_lpp_computable {α : ℝ}
    (hα01 : 0 ≤ α ∧ α ≤ 1)
    (halg : ∃ p : Polynomial ℤ, p ≠ 0 ∧ (Polynomial.aeval α p : ℝ) = 0) :
    IsLPPComputable α :=
  (algebraic_plpp_computable hα01 halg).isLPPComputable

end Ripple
