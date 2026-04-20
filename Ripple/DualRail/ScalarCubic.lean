/-
  Ripple.DualRail.ScalarCubic — UCNC25 Problem 1, scalar cubic case

  Concrete first case for UCNC25 Problem 1: the scalar GPAC
    y' = 1 - y^3        y(0) ∈ [0, 1]
  which is bounded (attracts to y = 1). Uniform dual-rail with constant-k
  annihilation:
    u' = 1 + 3 u^2 v + v^3 − k · u · v
    v' = u^3 + 3 u v^2 − k · u · v
  with u(0) = v(0) = 0.

  **Theorem (target, this file).** There exists `k* > 0` such that for all
  `k > k*`, the dual-rail solution `(u, v)` is bounded for all t ≥ 0.

  The (informal) proof in `notes/constant-annihilation-UCNC25.tex`:
  - Let `σ := u + v`. Using the dual-rail identity `u - v = y`, we get
      uv = (σ² - y²) / 4.
  - The drift simplifies to
      σ' = (p̂⁺ + p̂⁻) − 2k · uv
         = (1 + σ³) − (k/2) (σ² − y²)          -- using u² + v² + 3uv = …
         = Q_k(σ; y) / (quantity stuff)
    where the right-hand side is a cubic in σ with discriminant sign
    controlling boundedness.
  - For `k > k_SN(y) := 3 · ∛4 · (sup |y|)^{2/3}` the cubic Q_k has two
    positive roots; the smaller root σ_⁻(y) is an asymptotically stable
    fixed point of the σ-ODE at fixed y, and the interval [0, σ_⁻(y)] is
    forward-invariant. Since u, v ≥ 0 and u + v = σ ≤ σ_⁻(y) ≤ σ_⁻(1), the
    pair (u, v) stays bounded.

  This file formalizes the statement. The proof is scaffolded in three
  tiers with `sorry` placeholders; see Section 5 of the research note for
  the full structure.

  References:
  - `notes/constant-annihilation-UCNC25.tex` (research note).
  - `experiments/dual-rail-problem1/` (empirical corroboration).
  - UCNC25: `../../ref/selective-dual-railing-UCNC2025.pdf`.
-/

import Ripple.Core.PIVP
import Ripple.DualRail.ConstantAnnihilation
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Ripple
namespace DualRail
namespace ScalarCubic

open MvPolynomial

/-! ## The scalar polynomial p(y) = 1 − y³ -/

/-- The 1-dimensional polynomial vector field `p(y) = 1 − y³`, encoded as
a `Fin 1 → MvPolynomial (Fin 1) ℚ`. -/
noncomputable def cubicField : Fin 1 → MvPolynomial (Fin 1) ℚ :=
  fun _ => 1 - (X 0) ^ 3

/-- The scalar PIVP `y' = 1 − y³`, `y(0) = 0`. -/
noncomputable def cubicPIVP : PolyPIVP 1 where
  field := cubicField
  init := fun _ => 0
  output := 0

/-! ## The uniform constant-annihilation dual-railed system

Instantiates `constantAnnihilationDualRail` at `n = 1` and `p = cubicField`.
Produces a `PolyPIVP 2` with variables `(u, v) = (X 0, X 1)`. -/

/-- The dual-railed PolyPIVP at a fixed annihilation rate `k`. -/
noncomputable def dualRailedCubic (k : ℚ) : PolyPIVP 2 :=
  constantAnnihilationDualRail 1 cubicField k

/-! ## Positive / negative decomposition for p(y) = 1 − y³

After the substitution `y ↦ u − v`:
  p̂(u, v) = 1 − (u − v)³ = 1 − u³ + 3 u² v − 3 u v² + v³

So:
  p̂⁺ = 1 + 3 u² v + v³      (all non-negative coefficients)
  p̂⁻ = u³ + 3 u v²           (with sign-flipped to non-negative)

The cubic u³ dominates naive degree bounds; the boundedness proof relies
on the specific `σ = u + v` reduction, not a degree-driven Gronwall. -/

/-- The positive part `p̂⁺(u, v) = 1 + 3 u² v + v³` as a real polynomial
evaluation. Stated as a specification (proof is a concrete
polynomial-coefficient computation — not needed for the main theorem
statement, but useful for debugging the σ-reduction). -/
theorem dualRailPosPart_cubic_eval (w : Fin 2 → ℝ) :
    (dualRailPosPart 1 cubicField 0).eval₂ (Rat.castHom ℝ) w
      = 1 + 3 * (w 0) ^ 2 * (w 1) + (w 1) ^ 3 := by
  sorry

/-- The negative part `p̂⁻(u, v) = u³ + 3 u v²` (with non-negative
coefficients after the sign flip). -/
theorem dualRailNegPart_cubic_eval (w : Fin 2 → ℝ) :
    (dualRailNegPart 1 cubicField 0).eval₂ (Rat.castHom ℝ) w
      = (w 0) ^ 3 + 3 * (w 0) * (w 1) ^ 2 := by
  sorry

/-! ## Drift-difference identity (pos-part minus neg-part)

The cleanest algebraic consequence: the drift of `u` minus the drift of
`v` equals the original GPAC RHS, which for `p(y) = 1 − y³` is
`1 − (u − v)³`. This does **not** require computing `p̂⁺` and `p̂⁻`
individually — the annihilation terms cancel, and the difference
`p̂⁺ − p̂⁻` is handled by the general
`dualRailPos_sub_dualRailNeg_eval`. -/

/-- **Drift-difference identity for the scalar cubic.** At any state
`w : Fin 2 → ℝ`, the u-row drift minus the v-row drift equals
`1 − (w 0 − w 1)³`. Proof sketch:
- Unfold to `p̂⁺(w) − k_ℝ · w(0) · w(1)` (u) and `p̂⁻(w) − k_ℝ · w(0) · w(1)` (v).
- Subtraction cancels the annihilation; leaves `p̂⁺ − p̂⁻`.
- Apply `dualRailPos_sub_dualRailNeg_eval` to reduce to `p(w 0 − w 1)
  = 1 − (w 0 − w 1)³`.

The purely mechanical `if`/Fin-index unfolding is left as `sorry` — the
algebraic content is carried by `dualRailPos_sub_dualRailNeg_eval`
upstream and does not repeat here. -/
theorem dualRailedCubic_drift_diff (k : ℚ) (w : Fin 2 → ℝ) :
    (dualRailedCubic k).evalField w 0 - (dualRailedCubic k).evalField w 1
      = 1 - (w 0 - w 1) ^ 3 := by
  -- Helper: reformulate the two rows as `p̂± − k · u · v`.
  have hrow0 :
      (dualRailedCubic k).evalField w 0
        = (dualRailPosPart 1 cubicField 0).eval₂ (Rat.castHom ℝ) w
          - (k : ℝ) * w 0 * w 1 := by
    unfold dualRailedCubic PolyPIVP.evalField constantAnnihilationDualRail
    simp [MvPolynomial.eval₂_sub, MvPolynomial.eval₂_mul,
      MvPolynomial.eval₂_C, MvPolynomial.eval₂_X]
  have hrow1 :
      (dualRailedCubic k).evalField w 1
        = (dualRailNegPart 1 cubicField 0).eval₂ (Rat.castHom ℝ) w
          - (k : ℝ) * w 0 * w 1 := by
    unfold dualRailedCubic PolyPIVP.evalField constantAnnihilationDualRail
    simp [MvPolynomial.eval₂_sub, MvPolynomial.eval₂_mul,
      MvPolynomial.eval₂_C, MvPolynomial.eval₂_X]
  rw [hrow0, hrow1]
  ring_nf
  -- After ring_nf the goal reduces to `p̂⁺(w) − p̂⁻(w) = 1 − (w 0 − w 1)³`.
  have hdiff :
      (dualRailPosPart 1 cubicField 0).eval₂ (Rat.castHom ℝ) w
        - (dualRailNegPart 1 cubicField 0).eval₂ (Rat.castHom ℝ) w
      = (cubicField 0).eval₂ (Rat.castHom ℝ)
          (fun j : Fin 1 =>
            w ⟨2 * j.val, by omega⟩ - w ⟨2 * j.val + 1, by omega⟩) :=
    dualRailPos_sub_dualRailNeg_eval 1 cubicField 0 w
  have heval : (cubicField 0).eval₂ (Rat.castHom ℝ)
      (fun j : Fin 1 =>
        w ⟨2 * j.val, by omega⟩ - w ⟨2 * j.val + 1, by omega⟩)
      = 1 - (w 0 - w 1) ^ 3 := by
    unfold cubicField
    simp [MvPolynomial.eval₂_sub, MvPolynomial.eval₂_one,
      MvPolynomial.eval₂_pow, MvPolynomial.eval₂_X]
  rw [heval] at hdiff
  linarith [hdiff]

/-! ## Sigma-reduction identity

Setting `σ := u + v` and `y := u − v`, one has
  uv = (σ² − y²) / 4
  p̂⁺ + p̂⁻ = 1 + σ³             (after algebraic simplification).

The σ-dynamics are:
  σ' = u' + v' = (p̂⁺ − k u v) + (p̂⁻ − k u v)
               = (1 + σ³) − 2 k · uv
               = (1 + σ³) − (k/2)(σ² − y²).

This reduces the boundedness question to a scalar ODE in σ driven by the
known-bounded y. -/

/-- **Algebraic key identity** for the cubic dual-rail.

  `(1 + 3 u² v + v³) + (u³ + 3 u v²) = 1 + (u + v)³`.

Proven by direct expansion. -/
theorem cubic_posPart_plus_negPart (u v : ℝ) :
    (1 + 3 * u ^ 2 * v + v ^ 3) + (u ^ 3 + 3 * u * v ^ 2) = 1 + (u + v) ^ 3 := by
  ring

/-- **Auxiliary algebraic identity.**

  `2 u v = ((u + v)² − (u − v)²) / 2`, equivalently `4uv = σ² − y²`. -/
theorem two_uv_sigma_y (u v : ℝ) :
    2 * (u * v) = ((u + v) ^ 2 - (u - v) ^ 2) / 2 := by
  ring

/-! ## Main theorem (statement only, proof scaffolded)

Target: for every initial condition `y(0) ∈ [0, 1]`, there exists
`k* > 0` such that for all `k > k*` the dual-rail system is bounded.

The specific initial condition `y(0) = 0` (inherited from `cubicPIVP.init`)
is covered as the easy case: the whole (y, u, v) trajectory stays in the
invariant region `{0 ≤ y ≤ 1, 0 ≤ σ ≤ σ_⁻(1)}` by forward-invariance. -/

/-- **Saddle-node threshold.** For the cubic `p(y) = 1 − y³` with `|y| ≤ β`,
the σ-cubic `Q_k(σ; y) = σ³ − (k/2)σ² + (k β²/2) + 1` has two non-negative
real roots iff `k ≥ k_SN(β) := 3 · ∛4 · β^{2/3}` (when β > 0) or
`k > k_SN(0) := 0` trivially. We use `k* := 3 · ∛4 + 1` as a safe upper
bound for the unit interval case. -/
noncomputable def scalarCubicThreshold : ℝ := 3 * (4 : ℝ) ^ ((1 : ℝ) / 3) + 1

lemma scalarCubicThreshold_pos : 0 < scalarCubicThreshold := by
  unfold scalarCubicThreshold
  have h1 : (0 : ℝ) < 3 * (4 : ℝ) ^ ((1 : ℝ) / 3) := by
    apply mul_pos
    · norm_num
    · exact Real.rpow_pos_of_pos (by norm_num) _
  linarith

/-- **Main theorem (UCNC25 Problem 1, scalar cubic case).**

  For every rational `k > scalarCubicThreshold`, the uniform constant-
  annihilation dual-rail of the scalar cubic GPAC `y' = 1 − y³` with zero
  initial condition admits a bounded solution on `[0, ∞)`.

  The bound `B` depends on `k` but not on `t`.

  **Proof structure** (see `notes/constant-annihilation-UCNC25.tex`,
  Section 3):
  1. Local existence via Picard–Lindelöf (polynomial RHS is locally
     Lipschitz).
  2. Non-negativity: `u(0) = v(0) = 0`, `u' ≥ −k u v` and `v' ≥ −k u v`
     at the boundary `u = 0` (resp. `v = 0`), so `u, v ≥ 0` for all t ≥ 0.
  3. Dual-rail identity: `u − v = y` is invariant, so `|u − v| ≤ 1`.
  4. Sigma-reduction: `σ = u + v` satisfies `σ' = 1 + σ³ − (k/2)(σ² − y²)`.
  5. Invariant region: for `k > k_SN(1)`, the polynomial
     `Q_k(σ; y) = σ³ − (k/2) σ² + (k/2) y² + 1`
     has two positive roots `σ_⁻(y) < σ_⁺(y)`, and `[0, σ_⁻(y)]` is
     forward-invariant in the σ-direction at fixed y.
  6. Global existence: `0 ≤ σ ≤ σ_⁻(1)` and `|u − v| ≤ 1` bound each of
     `u, v` individually by `(σ_⁻(1) + 1) / 2`, preventing blowup. -/
theorem scalar_cubic_bounded :
    ∀ (k : ℚ), scalarCubicThreshold < (k : ℝ) →
      ∃ (sol : ℝ → Fin 2 → ℝ) (B : ℝ), 0 < B ∧
        (∀ t ≥ (0 : ℝ), ∀ i, 0 ≤ sol t i ∧ sol t i ≤ B) ∧
        (∀ t ≥ (0 : ℝ),
          HasDerivAt (fun s => sol s) ((dualRailedCubic k).evalField (sol t)) t) ∧
        sol 0 = fun _ => 0 := by
  sorry

/-- **Corollary.** Instantiated at a specific concrete `k`, e.g. `k = 10`
(well above the threshold `3 · ∛4 + 1 ≈ 5.76`), the scalar-cubic dual-rail
admits a bounded solution. Useful as a sanity-check instance once
`scalar_cubic_bounded` is proven. -/
theorem scalar_cubic_bounded_at_ten :
    ∃ (sol : ℝ → Fin 2 → ℝ) (B : ℝ), 0 < B ∧
      (∀ t ≥ (0 : ℝ), ∀ i, 0 ≤ sol t i ∧ sol t i ≤ B) ∧
      (∀ t ≥ (0 : ℝ),
        HasDerivAt (fun s => sol s)
          ((dualRailedCubic (10 : ℚ)).evalField (sol t)) t) ∧
      sol 0 = fun _ => 0 := by
  have hk : scalarCubicThreshold < ((10 : ℚ) : ℝ) := by
    unfold scalarCubicThreshold
    -- k* = 3 · 4^(1/3) + 1 ≈ 5.762..., so 10 > k*.
    -- 4^(1/3) < 4^(1/2) = 2, so 3 · 4^(1/3) < 6, hence k* < 7 < 10.
    have h1 : (4 : ℝ) ^ ((1 : ℝ) / 3) < (4 : ℝ) ^ ((1 : ℝ) / 2) := by
      apply Real.rpow_lt_rpow_of_exponent_lt
      · norm_num
      · norm_num
    have h2 : (4 : ℝ) ^ ((1 : ℝ) / 2) = 2 := by
      rw [show ((1 : ℝ) / 2) = ((1 : ℕ) : ℝ) / 2 by norm_num]
      rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) by norm_num]
      rw [← Real.rpow_natCast (2 : ℝ) 2]
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    have h3 : 3 * (4 : ℝ) ^ ((1 : ℝ) / 3) < 6 := by
      have := mul_lt_mul_of_pos_left h1 (by norm_num : (0 : ℝ) < 3)
      rw [h2] at this
      linarith
    have h10 : ((10 : ℚ) : ℝ) = 10 := by norm_num
    rw [h10]
    linarith
  exact scalar_cubic_bounded 10 hk

end ScalarCubic
end DualRail
end Ripple
