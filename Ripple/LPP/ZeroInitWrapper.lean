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

/-- **Sharp variant of `certified_zero_init_wrapper`.** Additionally propagates
a pointwise sharp upper bound: if the upstream trajectory is bounded above by
some `U ≥ 0` with `β ≤ U` (used at the call site as `U := α`, i.e. the
algebraic target), then the zero-init-wrapped trajectory is also bounded by `U`.

Sharp bound proof. The wrapped output is the `q = 0` tracker
`y(t) = ∫₀^t e^{-(t-s)} · x_out(s) ds`. If `x_out(s) ≤ U` on `[0, t]` and
`U ≥ 0`, then via `trackerTraj_upper_of_outTraj_upper`
`y(t) ≤ U · (1 − e^{-t}) ≤ U`. -/
theorem certified_zero_init_wrapper_sharp {β U : ℝ} {d : ℕ}
    (cbtc : CertifiedBoundedTimeComputable d β)
    (pcd : PolyCRNDecomposition d cbtc.pivp)
    (hU_nn : 0 ≤ U)
    (h_sharp_up : ∀ σ, 0 ≤ σ → cbtc.sol.trajectory σ cbtc.pivp.output ≤ U) :
    ∃ (d' : ℕ) (cbtc' : CertifiedBoundedTimeComputable d' β)
      (_ : PolyCRNDecomposition d' cbtc'.pivp),
      cbtc'.pivp.init cbtc'.pivp.output = 0 ∧
      ∀ σ, 0 ≤ σ → cbtc'.sol.trajectory σ cbtc'.pivp.output ≤ U := by
  set q : ℚ := 0 with hq_def
  obtain ⟨mod', hconv⟩ := relaxation_tracker_convergence q cbtc
  have hq_real : ((q : ℝ)) = 0 := by simp [hq_def]
  have hβq : β + ((q : ℝ)) = β := by rw [hq_real]; ring
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
    relaxationPIVP_polyCRN q (le_refl 0) pcd, ?_, ?_⟩
  · -- init output = q = 0.
    change (relaxationPIVP cbtc.pivp q).init (relaxationPIVP cbtc.pivp q).output = 0
    rw [relaxationPIVP_output, relaxationPIVP_init_last]
  · -- Sharp bound: trajectory at output ≤ U.
    intro σ hσ
    show (extendedSolution cbtc q).trajectory σ (relaxationPIVP cbtc.pivp q).output ≤ U
    rw [relaxationPIVP_output]
    have h_traj_eq : (extendedSolution cbtc q).trajectory σ (Fin.last d)
        = trackerTraj cbtc q σ := extendedTraj_last cbtc q σ
    rw [h_traj_eq]
    -- Apply trackerTraj_upper_of_outTraj_upper with the upstream bound U.
    have h_outTraj_le : ∀ s, 0 ≤ s → s ≤ σ → outTraj cbtc s ≤ U := by
      intro s hs_nn _
      rw [outTraj_of_nonneg cbtc hs_nn]
      exact h_sharp_up s hs_nn
    have h := trackerTraj_upper_of_outTraj_upper cbtc (le_refl 0) hU_nn hσ h_outTraj_le
    -- h : trackerTraj cbtc q σ ≤ U + (q : ℝ) = U + 0 = U.
    have : (q : ℝ) = 0 := hq_real
    linarith

end Algebraic

/-- Top-level alias in the `Ripple` namespace. -/
theorem certified_zero_init_wrapper {β : ℝ} {d : ℕ}
    (cbtc : CertifiedBoundedTimeComputable d β)
    (pcd : PolyCRNDecomposition d cbtc.pivp) :
    ∃ (d' : ℕ) (cbtc' : CertifiedBoundedTimeComputable d' β)
      (_ : PolyCRNDecomposition d' cbtc'.pivp),
      cbtc'.pivp.init cbtc'.pivp.output = 0 :=
  Algebraic.certified_zero_init_wrapper cbtc pcd

/-- Top-level alias for the sharp variant. -/
theorem certified_zero_init_wrapper_sharp {β U : ℝ} {d : ℕ}
    (cbtc : CertifiedBoundedTimeComputable d β)
    (pcd : PolyCRNDecomposition d cbtc.pivp)
    (hU_nn : 0 ≤ U)
    (h_sharp_up : ∀ σ, 0 ≤ σ → cbtc.sol.trajectory σ cbtc.pivp.output ≤ U) :
    ∃ (d' : ℕ) (cbtc' : CertifiedBoundedTimeComputable d' β)
      (_ : PolyCRNDecomposition d' cbtc'.pivp),
      cbtc'.pivp.init cbtc'.pivp.output = 0 ∧
      ∀ σ, 0 ≤ σ → cbtc'.sol.trajectory σ cbtc'.pivp.output ≤ U :=
  Algebraic.certified_zero_init_wrapper_sharp cbtc pcd hU_nn h_sharp_up

end Ripple
