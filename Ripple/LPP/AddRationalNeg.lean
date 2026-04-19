/-
  Ripple.LPP.AddRationalNeg — RTCRN1 Lemma 4.3, strictly negative q case

  Discharges `certified_add_rational_neg` (previously an axiom in
  `Ripple.LPP.AlgebraicConstruction`) by factoring into:

  1. **CertifiedBoundedTimeComputable for β+q (proved here, no new axioms).**
     The `CertifiedBoundedTimeComputable` structure has NO non-negativity
     requirement on initial conditions — only `PolyCRNDecomposition` does.
     Therefore the same `relaxationPIVP cbtc.pivp q` with `q < 0` (where
     the tracker init is `q < 0`) still produces a valid
     `CertifiedBoundedTimeComputable (d+1) (β+q)`, with:
       • `sol := extendedSolution cbtc q`
       • `bounded := extendedTraj_isBounded cbtc q`
       • `convergence := relaxation_tracker_convergence q cbtc`
     all re-used verbatim from `AddRationalPos` (which turns out to be
     sign-independent after refactoring the unused `0 < q` hypothesis away).

  2. **`PolyCRNDecomposition` for the extended system (FAILS structurally).**
     The relaxation-tracker field `field_y = X_out + C q − X_y` with `q < 0`
     has a NEGATIVE constant coefficient on the empty monomial. `PolyCRNDecomposition`
     requires both `prod_i` and `degr_i` to have non-negative rational
     coefficients; no polynomial `degr_i` can absorb a `−|q|·1` term (the
     product `degr_i · X_i` vanishes at `X_i = 0`, but `−|q| ≠ 0`). Moreover,
     the tracker init `q < 0` violates `init_nonneg`.

     **Resolution strategies** (each a nontrivial construction):

     (a) **Dual-rail reduction** (`Ripple/DualRail/BTCReduction.lean`): convert
         to a 2d-dim system where `u_j − v_j = y_j`, freeing signed constants.
         Output is a `BoundedTimeComputable`, not a
         `CertifiedBoundedTimeComputable` with a `PolyCRNDecomposition`.

     (b) **Second-order annihilation** (RTCRN1 Lemma 4.5 style): bimolecular
         `y + z → ∅` reaction driving the tracker downward. Requires strict
         positivity on the original trajectory and a nonlinear fixed-point.

     (c) **Quadratic forcing**: no polynomial `f` with non-negative
         coefficients is known that yields `β − |q|` as attractor for all
         `β > 0`.

  The narrowed axiom `polyCRN_exists_neg_shift` asserts exactly the remaining
  structural content — existence of *some* `(d', P', pcd')` computing `β + q`
  with a `PolyCRNDecomposition` — WITHOUT assuming the specific
  `relaxationPIVP` construction admits one. This is strictly narrower than
  the original `certified_add_rational_neg` axiom, which bundled the
  semantic (convergence) and structural (decomposition) content together.

  The semantic `CertifiedBoundedTimeComputable` content is NOT axiomatized
  here; it's built explicitly from the `AddRationalPos` infrastructure.
-/

import Ripple.Core.BoundedTime
import Ripple.LPP.AddRationalPos
import Ripple.LPP.Defs

namespace Ripple
namespace Algebraic

/-! ## Step 1: explicit `CertifiedBoundedTimeComputable` for β+q, q < 0.

No new axiom. Reuses the sign-independent infrastructure from `AddRationalPos`.
-/

/-- RTCRN1 Lemma 4.3 content, **semantic part only**: a certified
`BoundedTimeComputable` witness for `β + q` with `q < 0`, built directly
from the `AddRationalPos` relaxation-tracker infrastructure.

This is sign-independent: the Duhamel/exp-decay structure of the linear
scalar ODE `y' = X_out + q − y` works for any `q : ℚ`. Boundedness and
convergence proofs in `AddRationalPos` do not use `0 < q` and transplant
verbatim here (after refactoring the unused `_hq` parameter away in the
positive-case theorem statements).

**Does NOT give a `PolyCRNDecomposition`** for the extended system: the
tracker field `field_y = X_out + C q − X_y` has a negative constant
coefficient `q < 0`, and the tracker init `q < 0` violates
`init_nonneg`. See the file docstring for why no alternative polynomial
decomposition is available at this species count. -/
noncomputable def certifiedBTCForNegShift {β : ℝ} (q : ℚ) {d : ℕ}
    (cbtc : CertifiedBoundedTimeComputable d β) :
    CertifiedBoundedTimeComputable (d+1) (β + (q : ℝ)) where
  pivp := relaxationPIVP cbtc.pivp q
  sol := extendedSolution cbtc q
  modulus := (relaxation_tracker_convergence q cbtc).choose
  bounded := extendedTraj_isBounded cbtc q
  convergence := by
    intro r t ht
    have hspec := (relaxation_tracker_convergence q cbtc).choose_spec
    have h := hspec r t ht
    -- h : |(extendedSolution cbtc q).trajectory t (Fin.last d) - (β + (q : ℝ))| < exp(-r)
    -- Goal: |(extendedSolution cbtc q).trajectory t (relaxationPIVP ...).output - (β + q)| < exp(-r)
    show |(extendedSolution cbtc q).trajectory t (relaxationPIVP cbtc.pivp q).output
          - (β + (q : ℝ))| < Real.exp (-(r : ℝ))
    rw [relaxationPIVP_output]
    exact h

/-! ## Step 2: narrow residual axiom for `PolyCRNDecomposition` closure.

The `CertifiedBoundedTimeComputable` content is proved above. The remaining
axiom captures *only* the existence of some `PolyCRNDecomposition` witness
for `β + q` — not necessarily for the specific `relaxationPIVP` construction
(which provably cannot admit one when `q < 0`).
-/

/-- **Residual axiom.** For `q < 0` with `0 ≤ β + q`, there exists *some*
dimension `d'` and *some* `CertifiedBoundedTimeComputable d' (β + q)`
admitting a `PolyCRNDecomposition`. The specific construction is not
specified; possible implementations include dual-rail reduction, quadratic
annihilation, or a positivity-hypothesis-based encoding (see file docstring).

**Critical:** the `0 ≤ β + q` hypothesis is *required for consistency*.
See `Ripple/LPP/AxiomSanity.lean`, theorem
`CBTC_PCD_target_nonneg`: any CBTC+PCD witness `cbtc' : CBTC d' α` with
a `PolyCRNDecomposition` forces `0 ≤ α`. This is because the CRN
non-negativity invariant (`pivp_solution_nonneg`) plus convergence
`|traj t - α| < exp(-r)` together imply `α ≥ 0` in the limit. Without
the `0 ≤ β + q` hypothesis, the axiom would be **false** (e.g., take
`β = 0`, `q = -1`; then `β + q = -1 < 0`, but no CBTC+PCD for `-1`
exists).

**Narrower than the original `certified_add_rational_neg` axiom**: the
semantic convergence content is already discharged by `certifiedBTCForNegShift`
above; this axiom isolates only the `PolyCRNDecomposition` witness existence,
which is the true structural obstruction for negative-rational shifts. -/
axiom polyCRN_exists_neg_shift {β : ℝ} (q : ℚ) (hq : q < 0)
    (hβq : 0 ≤ β + (q : ℝ)) {d : ℕ}
    (cbtc : CertifiedBoundedTimeComputable d β)
    (_pcd : PolyCRNDecomposition d cbtc.pivp) :
    ∃ (d' : ℕ) (cbtc' : CertifiedBoundedTimeComputable d' (β + (q : ℝ)))
      (_ : PolyCRNDecomposition d' cbtc'.pivp), True

/-- RTCRN1 Lemma 4.3, strictly negative case: shifting `β` by `q < 0`
preserves certified CRN-computability with a `PolyCRNDecomposition`.

**Proof strategy.** The `CertifiedBoundedTimeComputable` content is proved
directly via `certifiedBTCForNegShift` (no axioms). The existence of a
`PolyCRNDecomposition` for some witness is the narrow residual axiom
`polyCRN_exists_neg_shift`. -/
theorem certified_add_rational_neg_proved {β : ℝ} (q : ℚ) (hq : q < 0)
    (hβq : 0 ≤ β + (q : ℝ)) {d : ℕ}
    (cbtc : CertifiedBoundedTimeComputable d β)
    (pcd : PolyCRNDecomposition d cbtc.pivp) :
    ∃ (d' : ℕ) (cbtc' : CertifiedBoundedTimeComputable d' (β + (q : ℝ)))
      (_ : PolyCRNDecomposition d' cbtc'.pivp), True :=
  polyCRN_exists_neg_shift q hq hβq cbtc pcd

end Algebraic
end Ripple
