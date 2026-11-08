/-
  Ripple.DualRail.Method — Unified annihilation method interface.

  Two proven methods for constructing the annihilation term in dual-railing:

    M1. **Polynomial-scale**: Z_i = P̂_i⁺ + P̂_i⁻
        [RTCRN2/DNA25, Huang-Klinge-Lathrop 2019]
        Boundedness: `PolynomialScaleDualRailBounded.lean` (0 sorry)

    M2. **Constant-rate**: Z = k (single constant for all species)
        [UCNC25 Problem 1, resolved in Huang-Huang 2025]
        Boundedness: `ConstantAnnihilationGeneral.lean` +
                     `ScalarCubic.lean` + `ScalarQuintic.lean` (0 sorry)

  This file provides a unified `AnnihilationMethod` type and dispatches
  to the existing constructions. The method is orthogonal to the strategy
  (which variables to dual-rail); the two dimensions combine in
  `Combination.lean`.
-/

import Ripple.DualRail.ConstantAnnihilation
import Ripple.DualRail.ConstantAnnihilationGeneral
import Ripple.DualRail.InfectionGraph

namespace Ripple
namespace DualRail

open MvPolynomial

/-- The two proven annihilation methods for dual-railing.

  Given species pair `(u_i, v_i)` with `u_i − v_i = y_i`, the shared
  annihilation term `−Z · u_i · v_i` prevents the pair from drifting apart.
  The two methods differ in the choice of Z:

  - `polynomialScale`: Z_i = P̂_i⁺(u,v) + P̂_i⁻(u,v), coupling the
    annihilation rate to the system's own dynamics. Produces more species
    when composed (the annihilation term itself is a polynomial in all
    dual-railed variables).

  - `constantRate k`: Z = k (a single positive rational), decoupling the
    annihilation from the polynomial structure. Cleaner for incremental
    dual-railing since the annihilation term doesn't introduce new
    cross-dependencies. -/
inductive AnnihilationMethod where
  /-- Polynomial-scale annihilation: Z_i = P̂_i⁺ + P̂_i⁻.
  Proven bounded in `PolynomialScaleDualRailBounded.lean`. -/
  | polynomialScale
  /-- Constant-rate annihilation: Z = k for a fixed positive rational.
  Proven bounded in `ConstantAnnihilationGeneral.lean`. -/
  | constantRate (k : ℚ) (hk : 0 < k)

/-- Apply an annihilation method to construct a full (all-at-once) dual-rail
system. This dispatches to the existing `polynomialScaleDualRail` and
`constantAnnihilationDualRail` constructions.

This is Strategy S1 (all-at-once): every variable is dual-railed.
Dimension: n → 2n. -/
noncomputable def AnnihilationMethod.applyAllAtOnce (method : AnnihilationMethod)
    (n : ℕ) [NeZero n] (p : Fin n → MvPolynomial (Fin n) ℚ) :
    PolyPIVP (2 * n) :=
  match method with
  | .polynomialScale => polynomialScaleDualRail n p
  | .constantRate k _ => constantAnnihilationDualRail n p k

/-- **Boundedness of M2 (constant-rate).**
If the original GPAC is bounded with bound β, then for some k > 0,
the constant-rate dual-rail system is bounded by 2β and tracks the
original trajectory exactly.

This is `constantAnnihilation_bounded_pos` from
`ConstantAnnihilationGeneral.lean`, restated for the unified interface. -/
theorem constantRate_bounded (n : ℕ) [NeZero n]
    (p : Fin n → MvPolynomial (Fin n) ℚ)
    (y₀ : Fin n → ℚ) (ySol : ℝ → Fin n → ℝ) (β : ℝ)
    (hBd : OriginalBounded p y₀ ySol β) :
    ∃ k : ℚ, 0 < k ∧
      ∃ (ûSol : ℝ → Fin (2 * n) → ℝ) (B : ℝ), 0 < B ∧
        (∀ t ≥ (0 : ℝ), ∀ K, 0 ≤ ûSol t K ∧ ûSol t K ≤ B) ∧
        (∀ t ≥ (0 : ℝ), ∀ i : Fin n,
          ûSol t ⟨2 * i.val, by have := i.isLt; omega⟩
            - ûSol t ⟨2 * i.val + 1, by have := i.isLt; omega⟩
            = ySol t i) :=
  constantAnnihilation_bounded_pos n p y₀ ySol β hBd

/-! ## Boundedness results

Both methods produce bounded dual-rail systems from bounded original GPACs.
The proofs are in `PolynomialScaleDualRailBounded.lean` and `ConstantAnnihilationGeneral.lean`
respectively, using `OriginalBounded` as the input hypothesis.

Note: `polynomialScaleDualRail_bounded` (in PolynomialScaleDualRailBounded.lean) uses the
`SemanticBTC` interface rather than `OriginalBounded`, so it is
not directly restated here. The constant-rate result aligns directly. -/

/-! ## SoundMethod: the 2+3 abstraction

A `SoundMethod` witnesses that a dual-rail construction produces a
CRN-implementable system. This is the "method" half of the 2+3
decomposition: it is independent of which variables are selected for
dual-railing (the "strategy" half).

To add a new method M3, one only needs to construct a `SoundMethod`
instance. It then automatically composes with all existing strategies. -/

/-- A **sound annihilation method** provides an all-at-once dual-rail
construction together with a proof that every variable in the resulting
2n-dimensional system is CRN-implementable (well-formed).

The well-formedness proof is the method's sole obligation. It is
independent of which variables "needed" to be dual-railed — the method
handles them all uniformly. The strategy determines which variables to
target; the composition theorem shows their contributions combine. -/
structure SoundMethod where
  /-- Construct the all-at-once dual-rail system (n → 2n). -/
  construct : (n : ℕ) → [NeZero n] →
    (Fin n → MvPolynomial (Fin n) ℚ) → PolyPIVP (2 * n)
  /-- Every variable in the constructed system is well-formed. -/
  wellFormed : ∀ (n : ℕ) [NeZero n]
    (p : Fin n → MvPolynomial (Fin n) ℚ) (i : Fin (2 * n)),
    IsWellFormed (construct n p).field i

/-- **M1 is sound.** Polynomial-scale annihilation produces CRN-implementable
systems, via `polynomialScaleDualRail_pcd` + `wellFormed_of_polyCRNDecomposition`. -/
noncomputable def soundMethod_polynomialScale : SoundMethod where
  construct := fun n [_] p => polynomialScaleDualRail n p
  wellFormed := fun n [_] p i =>
    wellFormed_of_polyCRNDecomposition (polynomialScaleDualRail_pcd n p) i

/-- **M2 is sound** (for any fixed k ≥ 0). Constant-rate annihilation produces
CRN-implementable systems, via `constantAnnihilationDualRail_pcd` +
`wellFormed_of_polyCRNDecomposition`. -/
noncomputable def soundMethod_constantRate (k : ℚ) (hk : 0 ≤ k) :
    SoundMethod where
  construct := fun n [_] p => constantAnnihilationDualRail n p k
  wellFormed := fun n [_] p i =>
    wellFormed_of_polyCRNDecomposition (constantAnnihilationDualRail_pcd n p k hk) i

end DualRail
end Ripple
