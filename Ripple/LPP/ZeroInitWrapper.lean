/-
  Ripple.LPP.ZeroInitWrapper — Zero-init wrapper for CertifiedBoundedTimeComputable.

  Purpose. `stage2_to_lpp_from_bounds` (in `Ripple.LPP.Stage2Convergence`, via
  `stage2_ode_axiomless_from_room`) requires the input BTC to satisfy
  `btc.pivp.init btc.pivp.output = 0` (the DNA 25 "zero-init" normalization).
  The algebraic pipeline (`algebraic_is_certified_crn`) does not guarantee
  this in general: the direct minimum-polynomial encoding typically places a
  nonzero rational seed at the output.

  Construction. Given any `CertifiedBoundedTimeComputable d β` with a
  `PolyCRNDecomposition` (and `0 ≤ β`, as supplied by
  `algebraic_is_certified_crn`), add a single relaxation-tracker species `y`
  obeying the linear scalar ODE
      y'(t) = x_out(t) - y(t),   y(0) = 0
  i.e. the `q = 0` specialization of the RTCRN1 Lemma 4.3 construction in
  `Ripple.LPP.AddRationalPos`. The tracker converges to `β + 0 = β`, is
  bounded, and — crucially — its initial value is `0`, satisfying the
  zero-init hypothesis.

  All the building blocks (`relaxationPIVP`, `relaxationPIVP_polyCRN`,
  `extendedSolution`, `extendedTraj_isBounded`, `relaxation_tracker_convergence`)
  from `AddRationalPos` are already `0 ≤ q`-friendly or fully sign-independent;
  only the outer wrapper `relaxation_tracker_solution` / `certified_add_rational_pos_proved`
  carried a vestigial `0 < q` requirement (used solely to route to
  `relaxationPIVP_polyCRN`'s `0 ≤ q`). We build a direct `q = 0` variant
  here without modifying the existing theorems.

  No new axioms: the resulting theorem depends on exactly
  `[propext, Classical.choice, Quot.sound]`.
-/

import Ripple.LPP.AddRationalPos

namespace Ripple
namespace Algebraic

open MvPolynomial

/-- **Zero-init wrapper** at the q = 0 specialization of the relaxation tracker.

Given any `CertifiedBoundedTimeComputable d β` with a `PolyCRNDecomposition`,
produce a new `CertifiedBoundedTimeComputable (d+1) β` whose underlying
`PolyPIVP` has `init output = 0` (the DNA 25 normalization demanded by
`stage2_to_lpp_from_bounds`).

The tracker is the `q = 0` relaxation species `y' = x_out − y`, with
`y(0) = 0` by construction. The shift is `β + 0 = β`, so the target number
is unchanged. All existing helpers are reused. -/
theorem certified_zero_init_wrapper {β : ℝ} {d : ℕ}
    (cbtc : CertifiedBoundedTimeComputable d β)
    (pcd : PolyCRNDecomposition d cbtc.pivp) :
    ∃ (d' : ℕ) (cbtc' : CertifiedBoundedTimeComputable d' β)
      (_ : PolyCRNDecomposition d' cbtc'.pivp),
      cbtc'.pivp.init cbtc'.pivp.output = 0 := by
  -- Fix q := 0. The existing convergence/boundedness/decomposition helpers
  -- are q-polymorphic (or `0 ≤ q`-friendly); only the outer glue theorem
  -- carried a vestigial strict-positivity requirement.
  set q : ℚ := 0 with hq_def
  -- Convergence of the tracker at q = 0: target is β + 0 = β.
  obtain ⟨mod', hconv⟩ := relaxation_tracker_convergence q cbtc
  -- Rewrite the convergence target from β + (q : ℝ) to β.
  have hq_real : ((q : ℝ)) = 0 := by simp [hq_def]
  have hβq : β + ((q : ℝ)) = β := by rw [hq_real]; ring
  -- Assemble the extended CBTC.
  refine ⟨d + 1,
    { pivp := relaxationPIVP cbtc.pivp q
      sol := extendedSolution cbtc q
      modulus := mod'
      bounded := extendedTraj_isBounded cbtc q
      convergence := by
        intro r t ht
        show |(extendedSolution cbtc q).trajectory t
                (relaxationPIVP cbtc.pivp q).output - β| < _
        rw [relaxationPIVP_output]
        have h := hconv r t ht
        rw [hβq] at h
        exact h },
    relaxationPIVP_polyCRN q (le_refl 0) pcd, ?_⟩
  -- init (output = Fin.last d) = q = 0.
  change (relaxationPIVP cbtc.pivp q).init (relaxationPIVP cbtc.pivp q).output = 0
  rw [relaxationPIVP_output, relaxationPIVP_init_last]

end Algebraic

/-- Top-level alias in the `Ripple` namespace. -/
theorem certified_zero_init_wrapper {β : ℝ} {d : ℕ}
    (cbtc : CertifiedBoundedTimeComputable d β)
    (pcd : PolyCRNDecomposition d cbtc.pivp) :
    ∃ (d' : ℕ) (cbtc' : CertifiedBoundedTimeComputable d' β)
      (_ : PolyCRNDecomposition d' cbtc'.pivp),
      cbtc'.pivp.init cbtc'.pivp.output = 0 :=
  Algebraic.certified_zero_init_wrapper cbtc pcd

end Ripple
