import Ripple.LPP.Stages
import Ripple.LPP.AlgebraicLPP

/-!
# The boundary values 0 and 1 are LPUP-computable

`algebraic_lpp_computable_boundary_cases` concludes only LPP-computability for `α = 0` or
`α = 1`; both values already lie in the narrower unimolecular class.
-/

namespace Ripple

/-- The two endpoint values already have unimolecular computations. -/
theorem lpup_computable_boundary_cases {α : ℝ}
    (hα_bdry : α = 0 ∨ α = 1) : IsLPUPComputable α := by
  rcases hα_bdry with rfl | rfl
  · simpa only [Rat.cast_zero] using
      (isLPUPComputable_rat (0 : ℚ) le_rfl zero_le_one)
  · simpa only [Rat.cast_one] using
      (isLPUPComputable_rat (1 : ℚ) zero_le_one le_rfl)

end Ripple
