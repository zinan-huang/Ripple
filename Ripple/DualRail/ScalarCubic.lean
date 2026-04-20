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
import Ripple.Core.ODEGlobal
import Ripple.DualRail.ConstantAnnihilation
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.ODE.Gronwall

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

/-! ### Explicit decomposition of `dualRailHom 1 cubicField 0`

Expanding `1 − (u − v)³ = (1 + 3u²v + v³) − (u³ + 3uv²)` gives a
non-negative-coefficient decomposition with disjoint monomial supports.
We record the two explicit polynomials, prove the decomposition, and
apply `posPart_negPart_of_nonneg_disjoint_decomp` to identify the
`posPart`/`negPart`. -/

/-- The positive part as an explicit polynomial: `1 + 3·X₀²·X₁ + X₁³`. -/
noncomputable def cubicPosExplicit : MvPolynomial (Fin 2) ℚ :=
  C 1 + C 3 * X 0 ^ 2 * X 1 + X 1 ^ 3

/-- The negative part as an explicit polynomial: `X₀³ + 3·X₀·X₁²`. -/
noncomputable def cubicNegExplicit : MvPolynomial (Fin 2) ℚ :=
  X 0 ^ 3 + C 3 * X 0 * X 1 ^ 2

/-- Algebraic identity: `dualRailHom 1 (cubicField 0) = pos − neg`. -/
theorem dualRailHom_cubic_eq_pos_sub_neg :
    dualRailHom 1 (cubicField 0) = cubicPosExplicit - cubicNegExplicit := by
  unfold dualRailHom cubicField cubicPosExplicit cubicNegExplicit
  have e0 : (⟨2 * (0 : Fin 1).val, by omega⟩ : Fin 2) = 0 := by
    apply Fin.ext; simp
  have e1 : (⟨2 * (0 : Fin 1).val + 1, by omega⟩ : Fin 2) = 1 := by
    apply Fin.ext; simp
  simp only [map_sub, map_one, map_pow, MvPolynomial.aeval_X, e0, e1]
  show _ = 1 + C 3 * (X 0 : MvPolynomial (Fin 2) ℚ) ^ 2 * X 1 + X 1 ^ 3
    - (X 0 ^ 3 + C 3 * X 0 * X 1 ^ 2)
  simp only [map_ofNat]
  ring

/-- The five monomial multi-indices appearing in `cubicPosExplicit` and
`cubicNegExplicit`. We use `Finsupp.single` pairs. -/
private lemma cubic_coeff_X0_sq_X1 (s : Fin 2 →₀ ℕ) :
    ((X 0 ^ 2 * X 1 : MvPolynomial (Fin 2) ℚ)).coeff s
      = if s = Finsupp.single 0 2 + Finsupp.single 1 1 then 1 else 0 := by
  have hX1 : (X 1 : MvPolynomial (Fin 2) ℚ)
      = MvPolynomial.monomial (Finsupp.single (1 : Fin 2) 1) 1 := by
    rw [← pow_one (X 1 : MvPolynomial (Fin 2) ℚ), MvPolynomial.X_pow_eq_monomial]
  rw [MvPolynomial.X_pow_eq_monomial, hX1,
      MvPolynomial.monomial_mul, MvPolynomial.coeff_monomial]
  split_ifs with h1 h2 h2
  · ring
  · exact (h2 h1.symm).elim
  · exact (h1 h2.symm).elim
  · rfl

/-- Coefficient formula for `cubicPosExplicit`. -/
private lemma cubicPosExplicit_coeff (s : Fin 2 →₀ ℕ) :
    cubicPosExplicit.coeff s
      = (if s = 0 then 1 else 0)
        + (if s = Finsupp.single 0 2 + Finsupp.single 1 1 then 3 else 0)
        + (if s = Finsupp.single 1 3 then 1 else 0) := by
  have heq : cubicPosExplicit = C 1 + C 3 * (X 0 ^ 2 * X 1) + X 1 ^ 3 := by
    unfold cubicPosExplicit; ring
  rw [heq, MvPolynomial.coeff_add, MvPolynomial.coeff_add,
      MvPolynomial.coeff_C_mul]
  -- C 1 coeff
  have h1 : ((C 1 : MvPolynomial (Fin 2) ℚ)).coeff s
      = if s = 0 then 1 else 0 := by
    rw [MvPolynomial.coeff_C]
    split_ifs with h1 h2 h2
    · rfl
    · exact (h2 h1.symm).elim
    · exact (h1 h2.symm).elim
    · rfl
  rw [h1, cubic_coeff_X0_sq_X1]
  -- X 1 ^ 3 coeff
  have h3 : ((X 1 ^ 3 : MvPolynomial (Fin 2) ℚ)).coeff s
      = if s = Finsupp.single 1 3 then 1 else 0 := by
    rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.coeff_monomial]
    split_ifs with h1 h2 h2
    · rfl
    · exact (h2 h1.symm).elim
    · exact (h1 h2.symm).elim
    · rfl
  rw [h3]
  split_ifs <;> ring

private lemma cubic_coeff_X0_X1_sq (s : Fin 2 →₀ ℕ) :
    ((X 0 * X 1 ^ 2 : MvPolynomial (Fin 2) ℚ)).coeff s
      = if s = Finsupp.single 0 1 + Finsupp.single 1 2 then 1 else 0 := by
  have hX0 : (X 0 : MvPolynomial (Fin 2) ℚ)
      = MvPolynomial.monomial (Finsupp.single (0 : Fin 2) 1) 1 := by
    rw [← pow_one (X 0 : MvPolynomial (Fin 2) ℚ), MvPolynomial.X_pow_eq_monomial]
  rw [hX0, MvPolynomial.X_pow_eq_monomial,
      MvPolynomial.monomial_mul, MvPolynomial.coeff_monomial]
  split_ifs with h1 h2 h2
  · ring
  · exact (h2 h1.symm).elim
  · exact (h1 h2.symm).elim
  · rfl

/-- Coefficient formula for `cubicNegExplicit`. -/
private lemma cubicNegExplicit_coeff (s : Fin 2 →₀ ℕ) :
    cubicNegExplicit.coeff s
      = (if s = Finsupp.single 0 3 then 1 else 0)
        + (if s = Finsupp.single 0 1 + Finsupp.single 1 2 then 3 else 0) := by
  have heq : cubicNegExplicit = X 0 ^ 3 + C 3 * (X 0 * X 1 ^ 2) := by
    unfold cubicNegExplicit; ring
  rw [heq, MvPolynomial.coeff_add, MvPolynomial.coeff_C_mul]
  -- X 0 ^ 3 coeff
  have h1 : ((X 0 ^ 3 : MvPolynomial (Fin 2) ℚ)).coeff s
      = if s = Finsupp.single 0 3 then 1 else 0 := by
    rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.coeff_monomial]
    split_ifs with h1 h2 h2
    · rfl
    · exact (h2 h1.symm).elim
    · exact (h1 h2.symm).elim
    · rfl
  rw [h1, cubic_coeff_X0_X1_sq]
  split_ifs <;> ring

/-- All coefficients of `cubicPosExplicit` are non-negative. -/
private lemma cubicPosExplicit_coeff_nonneg (s : Fin 2 →₀ ℕ) :
    0 ≤ cubicPosExplicit.coeff s := by
  rw [cubicPosExplicit_coeff]
  split_ifs <;> norm_num

/-- All coefficients of `cubicNegExplicit` are non-negative. -/
private lemma cubicNegExplicit_coeff_nonneg (s : Fin 2 →₀ ℕ) :
    0 ≤ cubicNegExplicit.coeff s := by
  rw [cubicNegExplicit_coeff]
  split_ifs <;> norm_num

/-- The five monomial multi-indices are pairwise distinct. We establish
disjointness of supports by case-analysis on `s`'s components at 0 and 1. -/
private lemma cubic_supports_disjoint (s : Fin 2 →₀ ℕ) :
    cubicPosExplicit.coeff s = 0 ∨ cubicNegExplicit.coeff s = 0 := by
  rw [cubicPosExplicit_coeff, cubicNegExplicit_coeff]
  -- For each s, check which of the 5 indices it equals. The (val 0, val 1) pairs are:
  --   (0,0), (2,1), (0,3), (3,0), (1,2). All distinct.
  -- Rather than enumerate, we show that if any pos-ite triggers, all neg-ites are false.
  by_cases hp1 : s = 0
  · right
    have hn1 : s ≠ Finsupp.single 0 3 := by
      intro h; rw [hp1] at h
      have := congrArg (fun f : Fin 2 →₀ ℕ => f 0) h
      simp [Finsupp.single_apply] at this
    have hn2 : s ≠ Finsupp.single 0 1 + Finsupp.single 1 2 := by
      intro h; rw [hp1] at h
      have := congrArg (fun f : Fin 2 →₀ ℕ => f 0) h
      simp [Finsupp.single_apply] at this
    rw [if_neg hn1, if_neg hn2]; ring
  by_cases hp2 : s = Finsupp.single 0 2 + Finsupp.single 1 1
  · right
    have hn1 : s ≠ Finsupp.single 0 3 := by
      intro h; rw [hp2] at h
      have := congrArg (fun f : Fin 2 →₀ ℕ => f 1) h
      simp [Finsupp.single_apply] at this
    have hn2 : s ≠ Finsupp.single 0 1 + Finsupp.single 1 2 := by
      intro h; rw [hp2] at h
      have := congrArg (fun f : Fin 2 →₀ ℕ => f 0) h
      simp [Finsupp.single_apply] at this
    rw [if_neg hn1, if_neg hn2]; ring
  by_cases hp3 : s = Finsupp.single 1 3
  · right
    have hn1 : s ≠ Finsupp.single 0 3 := by
      intro h; rw [hp3] at h
      have := congrArg (fun f : Fin 2 →₀ ℕ => f 0) h
      simp [Finsupp.single_apply] at this
    have hn2 : s ≠ Finsupp.single 0 1 + Finsupp.single 1 2 := by
      intro h; rw [hp3] at h
      have := congrArg (fun f : Fin 2 →₀ ℕ => f 0) h
      simp [Finsupp.single_apply] at this
    rw [if_neg hn1, if_neg hn2]; ring
  -- Otherwise all three pos-ites are false, so pos coefficient is 0.
  left
  rw [if_neg hp1, if_neg hp2, if_neg hp3]; ring

/-- Identification: `dualRailPosPart = cubicPosExplicit`. -/
theorem dualRailPosPart_cubic_eq :
    dualRailPosPart 1 cubicField 0 = cubicPosExplicit := by
  unfold dualRailPosPart
  exact (posPart_negPart_of_nonneg_disjoint_decomp
    dualRailHom_cubic_eq_pos_sub_neg
    cubicPosExplicit_coeff_nonneg
    cubicNegExplicit_coeff_nonneg
    cubic_supports_disjoint).1

/-- Identification: `dualRailNegPart = cubicNegExplicit`. -/
theorem dualRailNegPart_cubic_eq :
    dualRailNegPart 1 cubicField 0 = cubicNegExplicit := by
  unfold dualRailNegPart
  exact (posPart_negPart_of_nonneg_disjoint_decomp
    dualRailHom_cubic_eq_pos_sub_neg
    cubicPosExplicit_coeff_nonneg
    cubicNegExplicit_coeff_nonneg
    cubic_supports_disjoint).2

/-- The positive part `p̂⁺(u, v) = 1 + 3 u² v + v³` as a real polynomial
evaluation. Stated as a specification (proof is a concrete
polynomial-coefficient computation — not needed for the main theorem
statement, but useful for debugging the σ-reduction). -/
theorem dualRailPosPart_cubic_eval (w : Fin 2 → ℝ) :
    (dualRailPosPart 1 cubicField 0).eval₂ (Rat.castHom ℝ) w
      = 1 + 3 * (w 0) ^ 2 * (w 1) + (w 1) ^ 3 := by
  rw [dualRailPosPart_cubic_eq]
  unfold cubicPosExplicit
  simp only [MvPolynomial.eval₂_add, MvPolynomial.eval₂_mul,
    MvPolynomial.eval₂_X, MvPolynomial.eval₂_pow,
    MvPolynomial.eval₂_one, MvPolynomial.eval₂_ofNat,
    map_one, map_ofNat]

/-- The negative part `p̂⁻(u, v) = u³ + 3 u v²` (with non-negative
coefficients after the sign flip). -/
theorem dualRailNegPart_cubic_eval (w : Fin 2 → ℝ) :
    (dualRailNegPart 1 cubicField 0).eval₂ (Rat.castHom ℝ) w
      = (w 0) ^ 3 + 3 * (w 0) * (w 1) ^ 2 := by
  rw [dualRailNegPart_cubic_eq]
  unfold cubicNegExplicit
  simp only [MvPolynomial.eval₂_add, MvPolynomial.eval₂_mul,
    MvPolynomial.eval₂_X, MvPolynomial.eval₂_pow,
    MvPolynomial.eval₂_one, MvPolynomial.eval₂_ofNat,
    map_one, map_ofNat]

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

/-- **Drift-sum identity for the scalar cubic.** At any state
`w : Fin 2 → ℝ`, the u-row drift plus the v-row drift equals
`1 + (w 0 + w 1)³ − 2·k·w 0·w 1`.

Proof: same row-wise unfold as `dualRailedCubic_drift_diff`, then use
`cubic_posPart_plus_negPart` together with the two individual eval
specs `dualRailPosPart_cubic_eval` / `dualRailNegPart_cubic_eval`. -/
theorem dualRailedCubic_drift_sum (k : ℚ) (w : Fin 2 → ℝ) :
    (dualRailedCubic k).evalField w 0 + (dualRailedCubic k).evalField w 1
      = 1 + (w 0 + w 1) ^ 3 - 2 * (k : ℝ) * w 0 * w 1 := by
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
  rw [hrow0, hrow1, dualRailPosPart_cubic_eval, dualRailNegPart_cubic_eval]
  ring

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

/-- **Saddle-node threshold.** For the cubic `p(y) = 1 − y³` with `|y| ≤ 1`,
the σ-cubic `Q_k(σ; y) = σ³ − (k/2)σ² + (k y²/2) + 1` attains its local
minimum on `[0, k/3]` at `σ = k/3`, with value
`Q_k(k/3; y) = −k³/54 + 1 + (k/2) y²`. For `|y| ≤ 1` this is bounded above
by `−k³/54 + 1 + k/2`, which is strictly negative iff `k³ > 27 k + 54`, i.e.
`(k − 6)(k + 3)² > 0`, i.e. `k > 6`. So the true saddle-node threshold for
the unit-`|y|` case is exactly `k* = 6`. (An earlier approximation
`3 · ∛4 + 1 ≈ 5.76` was based on the β=|y|-agnostic form and is strictly
below `6`; the σ = k/3 barrier argument needs the sharper bound.) -/
noncomputable def scalarCubicThreshold : ℝ := 6

lemma scalarCubicThreshold_pos : 0 < scalarCubicThreshold := by
  unfold scalarCubicThreshold
  norm_num

/-! ## Proof sub-lemmas (Tier 1)

The main theorem decomposes into six analytic pieces. Each is stated
here with `sorry` so `scalar_cubic_bounded` can consume them directly
and so individual work fronts are visible. -/

/-- Lipschitz estimate for `(·)^3` on balls: `|x³ − y³| ≤ 3 R² |x − y|` when
`|x|, |y| ≤ R`. Derived from the factoring
`x³ − y³ = (x − y)(x² + x y + y²)`. Placed here so both the CRN
field-Lipschitz bound and the scalar barrier helpers below can use it. -/
private lemma cube_lipschitz_on_ball (R : ℝ) (hR : 0 ≤ R)
    (x y : ℝ) (hx : |x| ≤ R) (hy : |y| ≤ R) :
    |x ^ 3 - y ^ 3| ≤ 3 * R ^ 2 * |x - y| := by
  have hfactor : x ^ 3 - y ^ 3 = (x - y) * (x ^ 2 + x * y + y ^ 2) := by ring
  rw [hfactor, abs_mul]
  have h_bound : |x ^ 2 + x * y + y ^ 2| ≤ 3 * R ^ 2 := by
    rcases abs_le.mp hx with ⟨hxl, hxr⟩
    rcases abs_le.mp hy with ⟨hyl, hyr⟩
    rw [abs_le]
    refine ⟨?_, ?_⟩
    · nlinarith [sq_nonneg (x + y), sq_nonneg (x - y), sq_nonneg x, sq_nonneg y,
        sq_nonneg (x + R), sq_nonneg (y + R), sq_nonneg (x - R), sq_nonneg (y - R)]
    · nlinarith [sq_nonneg (x + y), sq_nonneg (x - y), sq_nonneg x, sq_nonneg y,
        sq_nonneg (x + R), sq_nonneg (y + R), sq_nonneg (x - R), sq_nonneg (y - R)]
  calc |x - y| * |x ^ 2 + x * y + y ^ 2|
      ≤ |x - y| * (3 * R ^ 2) :=
        mul_le_mul_of_nonneg_left h_bound (abs_nonneg _)
    _ = 3 * R ^ 2 * |x - y| := by ring

/-- Explicit component drift for row 0 of the dual-railed cubic. -/
private theorem dualRailedCubic_drift0 (k : ℚ) (w : Fin 2 → ℝ) :
    (dualRailedCubic k).evalField w 0
      = 1 + 3 * (w 0) ^ 2 * (w 1) + (w 1) ^ 3 - (k : ℝ) * (w 0) * (w 1) := by
  have hrow0 :
      (dualRailedCubic k).evalField w 0
        = (dualRailPosPart 1 cubicField 0).eval₂ (Rat.castHom ℝ) w
          - (k : ℝ) * w 0 * w 1 := by
    unfold dualRailedCubic PolyPIVP.evalField constantAnnihilationDualRail
    simp [MvPolynomial.eval₂_sub, MvPolynomial.eval₂_mul,
      MvPolynomial.eval₂_C, MvPolynomial.eval₂_X]
  rw [hrow0, dualRailPosPart_cubic_eval]

/-- Explicit component drift for row 1 of the dual-railed cubic. -/
private theorem dualRailedCubic_drift1 (k : ℚ) (w : Fin 2 → ℝ) :
    (dualRailedCubic k).evalField w 1
      = (w 0) ^ 3 + 3 * (w 0) * (w 1) ^ 2 - (k : ℝ) * (w 0) * (w 1) := by
  have hrow1 :
      (dualRailedCubic k).evalField w 1
        = (dualRailNegPart 1 cubicField 0).eval₂ (Rat.castHom ℝ) w
          - (k : ℝ) * w 0 * w 1 := by
    unfold dualRailedCubic PolyPIVP.evalField constantAnnihilationDualRail
    simp [MvPolynomial.eval₂_sub, MvPolynomial.eval₂_mul,
      MvPolynomial.eval₂_C, MvPolynomial.eval₂_X]
  rw [hrow1, dualRailNegPart_cubic_eval]

/-- Semantic CRN-implementability of the dual-railed cubic field.
Splits `k = k⁺ − k⁻` with both parts non-negative; the `−k·u·v`
annihilation term goes to the degradation when `k ≥ 0` and is absorbed
into the (non-negative) production when `k < 0`. -/
private noncomputable def dualRailedCubic_crn (k : ℚ) :
    IsCRNImplementable 2 (dualRailedCubic k).evalField where
  prod := fun i w => match i with
    | ⟨0, _⟩ => 1 + 3 * (w 0) ^ 2 * (w 1) + (w 1) ^ 3
        + max (-(k : ℝ)) 0 * (w 0) * (w 1)
    | ⟨1, _⟩ => (w 0) ^ 3 + 3 * (w 0) * (w 1) ^ 2
        + max (-(k : ℝ)) 0 * (w 0) * (w 1)
  degr := fun i w => match i with
    | ⟨0, _⟩ => max (k : ℝ) 0 * (w 1)
    | ⟨1, _⟩ => max (k : ℝ) 0 * (w 0)
  prod_pos := by
    intro i w hw
    fin_cases i
    · -- prod 0: 1 + 3u²v + v³ + max(-k,0)·u·v ≥ 0
      have h0 := hw 0
      have h1 := hw 1
      have hkm : 0 ≤ max (-(k : ℝ)) 0 := le_max_right _ _
      have hterm : 0 ≤ max (-(k : ℝ)) 0 * (w 0) * (w 1) := by
        have : 0 ≤ max (-(k : ℝ)) 0 * (w 0) := mul_nonneg hkm h0
        exact mul_nonneg this h1
      have h3u2v : 0 ≤ 3 * (w 0) ^ 2 * (w 1) := by
        have : 0 ≤ 3 * (w 0) ^ 2 :=
          mul_nonneg (by norm_num) (sq_nonneg _)
        exact mul_nonneg this h1
      have hv3 : 0 ≤ (w 1) ^ 3 := by positivity
      linarith
    · -- prod 1: u³ + 3uv² + max(-k,0)·u·v ≥ 0
      have h0 := hw 0
      have h1 := hw 1
      have hkm : 0 ≤ max (-(k : ℝ)) 0 := le_max_right _ _
      have hterm : 0 ≤ max (-(k : ℝ)) 0 * (w 0) * (w 1) := by
        have : 0 ≤ max (-(k : ℝ)) 0 * (w 0) := mul_nonneg hkm h0
        exact mul_nonneg this h1
      have h3uv2 : 0 ≤ 3 * (w 0) * (w 1) ^ 2 := by
        have : 0 ≤ 3 * (w 0) := mul_nonneg (by norm_num) h0
        exact mul_nonneg this (sq_nonneg _)
      have hu3 : 0 ≤ (w 0) ^ 3 := by positivity
      linarith
  degr_pos := by
    intro i w hw
    fin_cases i
    · exact mul_nonneg (le_max_right _ _) (hw 1)
    · exact mul_nonneg (le_max_right _ _) (hw 0)
  field_eq := by
    intro w i
    have hsplit : max (k : ℝ) 0 - max (-(k : ℝ)) 0 = (k : ℝ) := by
      rcases le_or_gt 0 (k : ℝ) with hk | hk
      · rw [max_eq_left hk, max_eq_right (by linarith : -(k : ℝ) ≤ 0)]; ring
      · rw [max_eq_right hk.le, max_eq_left (by linarith : 0 ≤ -(k : ℝ))]; ring
    fin_cases i
    · -- Row 0.
      have h0 := dualRailedCubic_drift0 k w
      show (dualRailedCubic k).evalField w 0 = _
      rw [h0]
      show 1 + 3 * w 0 ^ 2 * w 1 + w 1 ^ 3 - (k : ℝ) * w 0 * w 1
        = (1 + 3 * w 0 ^ 2 * w 1 + w 1 ^ 3 + max (-(k : ℝ)) 0 * w 0 * w 1)
          - max (k : ℝ) 0 * w 1 * w 0
      linear_combination (w 0 * w 1) * hsplit
    · -- Row 1.
      have h1 := dualRailedCubic_drift1 k w
      show (dualRailedCubic k).evalField w 1 = _
      rw [h1]
      show w 0 ^ 3 + 3 * w 0 * w 1 ^ 2 - (k : ℝ) * w 0 * w 1
        = (w 0 ^ 3 + 3 * w 0 * w 1 ^ 2 + max (-(k : ℝ)) 0 * w 0 * w 1)
          - max (k : ℝ) 0 * w 0 * w 1
      linear_combination (w 0 * w 1) * hsplit

/-- Local Lipschitz estimate for the dual-railed cubic field on norm balls. -/
private lemma dualRailedCubic_lipschitz (k : ℚ) :
    ∀ R : ℝ, 0 < R → ∃ L : ℝ, ∀ x y : Fin 2 → ℝ,
      ‖x‖ ≤ R → ‖y‖ ≤ R →
      ‖(dualRailedCubic k).evalField x - (dualRailedCubic k).evalField y‖
        ≤ L * ‖x - y‖ := by
  intro R hR
  -- Each coordinate is a polynomial of total degree ≤ 3 in (u, v).
  -- Lipschitz constant L := 8·(3R² + |k|·R + R) suffices as a loose bound.
  refine ⟨16 * (R^2 + |(k : ℝ)| * R + 1), ?_⟩
  intro x y hx hy
  -- Component bounds.
  have hx0 : |x 0| ≤ R := by
    have := norm_le_pi_norm x 0; rw [Real.norm_eq_abs] at this; linarith
  have hx1 : |x 1| ≤ R := by
    have := norm_le_pi_norm x 1; rw [Real.norm_eq_abs] at this; linarith
  have hy0 : |y 0| ≤ R := by
    have := norm_le_pi_norm y 0; rw [Real.norm_eq_abs] at this; linarith
  have hy1 : |y 1| ≤ R := by
    have := norm_le_pi_norm y 1; rw [Real.norm_eq_abs] at this; linarith
  have hdiff0 : |x 0 - y 0| ≤ ‖x - y‖ := by
    have := norm_le_pi_norm (x - y) 0
    rw [Real.norm_eq_abs] at this
    simpa [Pi.sub_apply] using this
  have hdiff1 : |x 1 - y 1| ≤ ‖x - y‖ := by
    have := norm_le_pi_norm (x - y) 1
    rw [Real.norm_eq_abs] at this
    simpa [Pi.sub_apply] using this
  have hxy_nn : 0 ≤ ‖x - y‖ := norm_nonneg _
  have hR_nn : 0 ≤ R := hR.le
  have hL_nn : 0 ≤ 16 * (R^2 + |(k : ℝ)| * R + 1) := by
    have : 0 ≤ R^2 + |(k : ℝ)| * R + 1 := by
      have h1 : 0 ≤ R^2 := sq_nonneg _
      have h2 : 0 ≤ |(k : ℝ)| * R := mul_nonneg (abs_nonneg _) hR_nn
      linarith
    linarith
  -- Bound each coordinate diff.
  have coord_bound : ∀ i : Fin 2,
      |(dualRailedCubic k).evalField x i - (dualRailedCubic k).evalField y i|
        ≤ 16 * (R^2 + |(k : ℝ)| * R + 1) * ‖x - y‖ := by
    intro i
    fin_cases i
    · have hx_d0 := dualRailedCubic_drift0 k x
      have hy_d0 := dualRailedCubic_drift0 k y
      change |(dualRailedCubic k).evalField x 0 - (dualRailedCubic k).evalField y 0|
        ≤ 16 * (R^2 + |(k : ℝ)| * R + 1) * ‖x - y‖
      rw [hx_d0, hy_d0]
      -- Difference = Δ₁ + Δ₂ + Δ₃ with:
      -- Δ₁ = 3·(x₀²·x₁ − y₀²·y₁), Δ₂ = (x₁³ − y₁³), Δ₃ = −k·(x₀·x₁ − y₀·y₁)
      have h_expand :
          (1 + 3 * (x 0) ^ 2 * (x 1) + (x 1) ^ 3 - (k : ℝ) * (x 0) * (x 1))
          - (1 + 3 * (y 0) ^ 2 * (y 1) + (y 1) ^ 3 - (k : ℝ) * (y 0) * (y 1))
          = 3 * ((x 0)^2 * (x 1) - (y 0)^2 * (y 1))
            + ((x 1)^3 - (y 1)^3)
            + (-(k : ℝ)) * ((x 0) * (x 1) - (y 0) * (y 1)) := by ring
      rw [h_expand]
      -- Bound each piece.
      have h_cube : |(x 1)^3 - (y 1)^3| ≤ 3 * R^2 * |x 1 - y 1| :=
        cube_lipschitz_on_ball R hR_nn (x 1) (y 1) hx1 hy1
      -- |x₀²·x₁ − y₀²·y₁| ≤ |x₀² − y₀²|·|x₁| + |y₀²|·|x₁ − y₁|
      -- ≤ 2R·|x₀−y₀|·R + R²·|x₁−y₁| = 2R²·|x₀−y₀| + R²·|x₁−y₁|
      have h_sq_diff : |(x 0)^2 - (y 0)^2| ≤ 2 * R * |x 0 - y 0| := by
        have h_fact : (x 0)^2 - (y 0)^2 = (x 0 - y 0) * (x 0 + y 0) := by ring
        rw [h_fact, abs_mul]
        have habsum : |x 0 + y 0| ≤ 2 * R := by
          have := abs_add_le (x 0) (y 0); linarith
        calc |x 0 - y 0| * |x 0 + y 0|
            ≤ |x 0 - y 0| * (2 * R) :=
              mul_le_mul_of_nonneg_left habsum (abs_nonneg _)
          _ = 2 * R * |x 0 - y 0| := by ring
      have h_prod1 : |(x 0)^2 * (x 1) - (y 0)^2 * (y 1)|
          ≤ 2 * R^2 * |x 0 - y 0| + R^2 * |x 1 - y 1| := by
        have h_eq : (x 0)^2 * (x 1) - (y 0)^2 * (y 1)
            = ((x 0)^2 - (y 0)^2) * (x 1) + (y 0)^2 * ((x 1) - (y 1)) := by ring
        rw [h_eq]
        have h1 := abs_add_le (((x 0)^2 - (y 0)^2) * (x 1))
                            ((y 0)^2 * ((x 1) - (y 1)))
        have h2 : |((x 0)^2 - (y 0)^2) * (x 1)|
            ≤ 2 * R * |x 0 - y 0| * R := by
          rw [abs_mul]
          have := mul_le_mul h_sq_diff hx1 (abs_nonneg _)
                  (by positivity : (0 : ℝ) ≤ 2 * R * |x 0 - y 0|)
          linarith
        have h3 : |(y 0)^2 * ((x 1) - (y 1))| ≤ R^2 * |x 1 - y 1| := by
          rw [abs_mul, abs_pow]
          have hy0sq : |y 0|^2 ≤ R^2 := by
            exact sq_le_sq' (by linarith [abs_nonneg (y 0)]) hy0
          exact mul_le_mul_of_nonneg_right hy0sq (abs_nonneg _)
        calc |((x 0)^2 - (y 0)^2) * (x 1) + (y 0)^2 * ((x 1) - (y 1))|
            ≤ |((x 0)^2 - (y 0)^2) * (x 1)| + |(y 0)^2 * ((x 1) - (y 1))| := h1
          _ ≤ 2 * R * |x 0 - y 0| * R + R^2 * |x 1 - y 1| := by linarith
          _ = 2 * R^2 * |x 0 - y 0| + R^2 * |x 1 - y 1| := by ring
      -- |x₀·x₁ − y₀·y₁| ≤ R·|x₀−y₀| + R·|x₁−y₁|
      have h_prod2 : |(x 0) * (x 1) - (y 0) * (y 1)|
          ≤ R * |x 0 - y 0| + R * |x 1 - y 1| := by
        have h_eq : (x 0) * (x 1) - (y 0) * (y 1)
            = (x 0 - y 0) * (x 1) + (y 0) * ((x 1) - (y 1)) := by ring
        rw [h_eq]
        have h1 := abs_add_le ((x 0 - y 0) * (x 1)) ((y 0) * ((x 1) - (y 1)))
        have h2 : |(x 0 - y 0) * (x 1)| ≤ |x 0 - y 0| * R := by
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left hx1 (abs_nonneg _)
        have h3 : |(y 0) * ((x 1) - (y 1))| ≤ R * |x 1 - y 1| := by
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_right hy0 (abs_nonneg _)
        calc |(x 0 - y 0) * (x 1) + (y 0) * ((x 1) - (y 1))|
            ≤ |(x 0 - y 0) * (x 1)| + |(y 0) * ((x 1) - (y 1))| := h1
          _ ≤ |x 0 - y 0| * R + R * |x 1 - y 1| := by linarith
          _ = R * |x 0 - y 0| + R * |x 1 - y 1| := by ring
      -- Combine.
      calc |3 * ((x 0)^2 * (x 1) - (y 0)^2 * (y 1))
              + ((x 1)^3 - (y 1)^3)
              + (-(k : ℝ)) * ((x 0) * (x 1) - (y 0) * (y 1))|
          ≤ |3 * ((x 0)^2 * (x 1) - (y 0)^2 * (y 1))|
              + |((x 1)^3 - (y 1)^3)|
              + |(-(k : ℝ)) * ((x 0) * (x 1) - (y 0) * (y 1))| := by
            have h1 := abs_add_le (3 * ((x 0)^2 * (x 1) - (y 0)^2 * (y 1))
                                  + ((x 1)^3 - (y 1)^3))
                                ((-(k : ℝ)) * ((x 0) * (x 1) - (y 0) * (y 1)))
            have h2 := abs_add_le (3 * ((x 0)^2 * (x 1) - (y 0)^2 * (y 1)))
                                ((x 1)^3 - (y 1)^3)
            linarith
        _ ≤ 3 * (2 * R^2 * |x 0 - y 0| + R^2 * |x 1 - y 1|)
              + 3 * R^2 * |x 1 - y 1|
              + |(k : ℝ)| * (R * |x 0 - y 0| + R * |x 1 - y 1|) := by
            have hc1 : |3 * ((x 0)^2 * (x 1) - (y 0)^2 * (y 1))|
                = 3 * |(x 0)^2 * (x 1) - (y 0)^2 * (y 1)| := by
              rw [abs_mul]; norm_num
            have hc2 : |(-(k : ℝ)) * ((x 0) * (x 1) - (y 0) * (y 1))|
                = |(k : ℝ)| * |(x 0) * (x 1) - (y 0) * (y 1)| := by
              rw [abs_mul, abs_neg]
            rw [hc1, hc2]
            have h_abs_k_nn : 0 ≤ |(k : ℝ)| := abs_nonneg _
            have p1 := mul_le_mul_of_nonneg_left h_prod1 (by norm_num : (0 : ℝ) ≤ 3)
            have p2 := mul_le_mul_of_nonneg_left h_prod2 h_abs_k_nn
            linarith
        _ ≤ 16 * (R^2 + |(k : ℝ)| * R + 1) * ‖x - y‖ := by
            have hL_nn' : 0 ≤ 16 * (R^2 + |(k : ℝ)| * R + 1) := hL_nn
            have h_abs_k_nn : 0 ≤ |(k : ℝ)| := abs_nonneg _
            nlinarith [hdiff0, hdiff1, sq_nonneg R, hR_nn,
                       mul_nonneg h_abs_k_nn hR_nn, abs_nonneg (x 0 - y 0),
                       abs_nonneg (x 1 - y 1)]
    · have hx_d1 := dualRailedCubic_drift1 k x
      have hy_d1 := dualRailedCubic_drift1 k y
      change |(dualRailedCubic k).evalField x 1 - (dualRailedCubic k).evalField y 1|
        ≤ 16 * (R^2 + |(k : ℝ)| * R + 1) * ‖x - y‖
      rw [hx_d1, hy_d1]
      have h_expand :
          ((x 0)^3 + 3 * (x 0) * (x 1)^2 - (k : ℝ) * (x 0) * (x 1))
          - ((y 0)^3 + 3 * (y 0) * (y 1)^2 - (k : ℝ) * (y 0) * (y 1))
          = ((x 0)^3 - (y 0)^3)
            + 3 * ((x 0) * (x 1)^2 - (y 0) * (y 1)^2)
            + (-(k : ℝ)) * ((x 0) * (x 1) - (y 0) * (y 1)) := by ring
      rw [h_expand]
      have h_cube : |(x 0)^3 - (y 0)^3| ≤ 3 * R^2 * |x 0 - y 0| :=
        cube_lipschitz_on_ball R hR_nn (x 0) (y 0) hx0 hy0
      have h_sq_diff : |(x 1)^2 - (y 1)^2| ≤ 2 * R * |x 1 - y 1| := by
        have h_fact : (x 1)^2 - (y 1)^2 = (x 1 - y 1) * (x 1 + y 1) := by ring
        rw [h_fact, abs_mul]
        have habsum : |x 1 + y 1| ≤ 2 * R := by
          have := abs_add_le (x 1) (y 1); linarith
        calc |x 1 - y 1| * |x 1 + y 1|
            ≤ |x 1 - y 1| * (2 * R) :=
              mul_le_mul_of_nonneg_left habsum (abs_nonneg _)
          _ = 2 * R * |x 1 - y 1| := by ring
      have h_prod1 : |(x 0) * (x 1)^2 - (y 0) * (y 1)^2|
          ≤ R^2 * |x 0 - y 0| + 2 * R^2 * |x 1 - y 1| := by
        have h_eq : (x 0) * (x 1)^2 - (y 0) * (y 1)^2
            = ((x 0) - (y 0)) * (x 1)^2 + (y 0) * ((x 1)^2 - (y 1)^2) := by ring
        rw [h_eq]
        have h1 := abs_add_le (((x 0) - (y 0)) * (x 1)^2)
                            ((y 0) * ((x 1)^2 - (y 1)^2))
        have h2 : |((x 0) - (y 0)) * (x 1)^2| ≤ |x 0 - y 0| * R^2 := by
          rw [abs_mul, abs_pow]
          have hx1sq : |x 1|^2 ≤ R^2 :=
            sq_le_sq' (by linarith [abs_nonneg (x 1)]) hx1
          exact mul_le_mul_of_nonneg_left hx1sq (abs_nonneg _)
        have h3 : |(y 0) * ((x 1)^2 - (y 1)^2)| ≤ R * (2 * R * |x 1 - y 1|) := by
          rw [abs_mul]
          have := mul_le_mul hy0 h_sq_diff (abs_nonneg _) hR_nn
          linarith
        calc |((x 0) - (y 0)) * (x 1)^2 + (y 0) * ((x 1)^2 - (y 1)^2)|
            ≤ |((x 0) - (y 0)) * (x 1)^2| + |(y 0) * ((x 1)^2 - (y 1)^2)| := h1
          _ ≤ |x 0 - y 0| * R^2 + R * (2 * R * |x 1 - y 1|) := by linarith
          _ = R^2 * |x 0 - y 0| + 2 * R^2 * |x 1 - y 1| := by ring
      have h_prod2 : |(x 0) * (x 1) - (y 0) * (y 1)|
          ≤ R * |x 0 - y 0| + R * |x 1 - y 1| := by
        have h_eq : (x 0) * (x 1) - (y 0) * (y 1)
            = (x 0 - y 0) * (x 1) + (y 0) * ((x 1) - (y 1)) := by ring
        rw [h_eq]
        have h1 := abs_add_le ((x 0 - y 0) * (x 1)) ((y 0) * ((x 1) - (y 1)))
        have h2 : |(x 0 - y 0) * (x 1)| ≤ |x 0 - y 0| * R := by
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left hx1 (abs_nonneg _)
        have h3 : |(y 0) * ((x 1) - (y 1))| ≤ R * |x 1 - y 1| := by
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_right hy0 (abs_nonneg _)
        calc |(x 0 - y 0) * (x 1) + (y 0) * ((x 1) - (y 1))|
            ≤ |(x 0 - y 0) * (x 1)| + |(y 0) * ((x 1) - (y 1))| := h1
          _ ≤ |x 0 - y 0| * R + R * |x 1 - y 1| := by linarith
          _ = R * |x 0 - y 0| + R * |x 1 - y 1| := by ring
      calc |((x 0)^3 - (y 0)^3)
              + 3 * ((x 0) * (x 1)^2 - (y 0) * (y 1)^2)
              + (-(k : ℝ)) * ((x 0) * (x 1) - (y 0) * (y 1))|
          ≤ |((x 0)^3 - (y 0)^3)|
              + |3 * ((x 0) * (x 1)^2 - (y 0) * (y 1)^2)|
              + |(-(k : ℝ)) * ((x 0) * (x 1) - (y 0) * (y 1))| := by
            have h1 := abs_add_le (((x 0)^3 - (y 0)^3)
                                  + 3 * ((x 0) * (x 1)^2 - (y 0) * (y 1)^2))
                                ((-(k : ℝ)) * ((x 0) * (x 1) - (y 0) * (y 1)))
            have h2 := abs_add_le ((x 0)^3 - (y 0)^3)
                                (3 * ((x 0) * (x 1)^2 - (y 0) * (y 1)^2))
            linarith
        _ ≤ 3 * R^2 * |x 0 - y 0|
              + 3 * (R^2 * |x 0 - y 0| + 2 * R^2 * |x 1 - y 1|)
              + |(k : ℝ)| * (R * |x 0 - y 0| + R * |x 1 - y 1|) := by
            have hc1 : |3 * ((x 0) * (x 1)^2 - (y 0) * (y 1)^2)|
                = 3 * |(x 0) * (x 1)^2 - (y 0) * (y 1)^2| := by
              rw [abs_mul]; norm_num
            have hc2 : |(-(k : ℝ)) * ((x 0) * (x 1) - (y 0) * (y 1))|
                = |(k : ℝ)| * |(x 0) * (x 1) - (y 0) * (y 1)| := by
              rw [abs_mul, abs_neg]
            rw [hc1, hc2]
            have h_abs_k_nn : 0 ≤ |(k : ℝ)| := abs_nonneg _
            have p1 := mul_le_mul_of_nonneg_left h_prod1 (by norm_num : (0 : ℝ) ≤ 3)
            have p2 := mul_le_mul_of_nonneg_left h_prod2 h_abs_k_nn
            linarith
        _ ≤ 16 * (R^2 + |(k : ℝ)| * R + 1) * ‖x - y‖ := by
            have hL_nn' : 0 ≤ 16 * (R^2 + |(k : ℝ)| * R + 1) := hL_nn
            have h_abs_k_nn : 0 ≤ |(k : ℝ)| := abs_nonneg _
            nlinarith [hdiff0, hdiff1, sq_nonneg R, hR_nn,
                       mul_nonneg h_abs_k_nn hR_nn, abs_nonneg (x 0 - y 0),
                       abs_nonneg (x 1 - y 1)]
  -- Combine via sup-norm.
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro i
  rw [Real.norm_eq_abs, Pi.sub_apply]
  exact coord_bound i

/-- **Sub-lemma 1: non-negativity of the dual-rail solution.** If a
solution `sol` to `dualRailedCubic k` starts at the origin, both
components stay non-negative on `[0, ∞)`.

Proof: the dual-railed field is CRN-implementable (production polynomials
with non-negative values on ℝ≥0 and a single linear degradation term per
species). Combined with local Lipschitz (polynomial of degree 3) and
zero initial condition, `crn_local_nonneg` (Ripple.Core.ODEGlobal) gives
coordinate-wise non-negativity on any forward time interval. Pick
`T := t + 1` to cover the target point. -/
theorem scalar_cubic_nonneg (k : ℚ) (sol : ℝ → Fin 2 → ℝ)
    (h_init : sol 0 = fun _ => 0)
    (h_deriv : ∀ t ≥ (0 : ℝ),
      HasDerivAt (fun s => sol s) ((dualRailedCubic k).evalField (sol t)) t) :
    ∀ t ≥ (0 : ℝ), ∀ i, 0 ≤ sol t i := by
  intro t ht i
  have hT : (0 : ℝ) < t + 1 := by linarith
  have h_init_nn : ∀ j, 0 ≤ sol 0 j := fun j => by rw [h_init]
  have h_ode : ∀ s ∈ Set.Ico (0 : ℝ) (t + 1),
      HasDerivAt sol ((dualRailedCubic k).evalField (sol s)) s := by
    intro s hs
    exact h_deriv s hs.1
  have h_crn := dualRailedCubic_crn k
  have h_lip := dualRailedCubic_lipschitz k
  have := crn_local_nonneg h_crn h_lip (t + 1) hT sol h_init_nn h_ode
    t ⟨ht, by linarith⟩ i
  exact this

/-- **Sub-lemma 2: dual-rail identity preservation.** The difference
`u − v` of a dual-rail solution satisfies the original scalar cubic
GPAC `y' = 1 − y³`. This is the derivative version of
`dualRailedCubic_drift_diff`. -/
theorem scalar_cubic_dual_rail_identity (k : ℚ) (sol : ℝ → Fin 2 → ℝ)
    (h_deriv : ∀ t ≥ (0 : ℝ),
      HasDerivAt (fun s => sol s) ((dualRailedCubic k).evalField (sol t)) t) :
    ∀ t ≥ (0 : ℝ),
      HasDerivAt (fun s => sol s 0 - sol s 1)
        (1 - (sol t 0 - sol t 1) ^ 3) t := by
  intro t ht
  have h := h_deriv t ht
  have hpi := (hasDerivAt_pi (φ := fun s => sol s)
    (φ' := (dualRailedCubic k).evalField (sol t))).1 h
  have hu := hpi 0
  have hv := hpi 1
  have hdiff := hu.sub hv
  have heq := dualRailedCubic_drift_diff k (sol t)
  rw [heq] at hdiff
  exact hdiff

/-! ### Helpers for `scalar_cubic_original_bounded`

Lower/upper barrier arguments adapted to this specific ODE. Kept private to
this file. (The general cube Lipschitz estimate is hoisted above
`scalar_cubic_nonneg` so its CRN-implementability proof can reuse it.) -/

/-- Lower barrier for the scalar cubic ODE `y' = 1 − y³` with `y(0) = 0`.
If `y t < 0` at some `t > 0`, take the sup `s` of times in `[0, t]` with
`y ≥ 0`; on `(s, t]`, `y < 0`, so `y' = 1 − y³ > 1 > 0`; MVT gives
`y t > y s = 0`, contradiction. -/
private lemma scalar_cubic_lower_barrier
    {y : ℝ → ℝ}
    (hy0 : y 0 = 0)
    (hy_deriv : ∀ t, 0 ≤ t → HasDerivAt y (1 - (y t) ^ 3) t) :
    ∀ t, 0 ≤ t → 0 ≤ y t := by
  intro t ht_nn
  by_contra h_neg
  push_neg at h_neg
  -- y is continuous on [0, t].
  have hy_cont : ContinuousOn y (Set.Icc 0 t) := by
    intro u hu
    exact (hy_deriv u hu.1).continuousAt.continuousWithinAt
  -- S := {u ∈ [0, t] | 0 ≤ y u}.
  let S : Set ℝ := {u | u ∈ Set.Icc (0 : ℝ) t ∧ 0 ≤ y u}
  have h0_mem : (0 : ℝ) ∈ S := ⟨⟨le_refl _, ht_nn⟩, by rw [hy0]⟩
  have hS_bdd : BddAbove S := ⟨t, fun u hu => hu.1.2⟩
  have hS_nonempty : S.Nonempty := ⟨0, h0_mem⟩
  set s := sSup S with hs_def
  have hs_le_t : s ≤ t := csSup_le hS_nonempty (fun u hu => hu.1.2)
  have hs_nn : 0 ≤ s := le_csSup hS_bdd h0_mem
  have hs_in_Icc : s ∈ Set.Icc (0 : ℝ) t := ⟨hs_nn, hs_le_t⟩
  -- y s ≥ 0 by continuity at s from the left (sequence in S converging to s).
  have hys_nn : 0 ≤ y s := by
    have hy_cont_s : ContinuousWithinAt y (Set.Icc 0 t) s :=
      hy_cont s hs_in_Icc
    rcases eq_or_lt_of_le hs_nn with hs_zero | hs_pos
    · rw [← hs_zero, hy0]
    · have h_seq : ∀ ε > 0, ∃ u ∈ S, s - ε < u ∧ u ≤ s := by
        intro ε hε
        obtain ⟨u, hu_mem, hu_lt⟩ :=
          exists_lt_of_lt_csSup hS_nonempty (show s - ε < s by linarith)
        exact ⟨u, hu_mem, hu_lt, le_csSup hS_bdd hu_mem⟩
      have : ∀ ε > 0, ∃ u ∈ Set.Icc (0:ℝ) t, |u - s| < ε ∧ 0 ≤ y u := by
        intro ε hε
        obtain ⟨u, ⟨hu1, hu2⟩, hu_lt, hu_le⟩ := h_seq ε hε
        refine ⟨u, hu1, ?_, hu2⟩
        rw [abs_sub_lt_iff]; exact ⟨by linarith, by linarith⟩
      by_contra h_ys_neg
      push_neg at h_ys_neg
      rw [Metric.continuousWithinAt_iff] at hy_cont_s
      obtain ⟨δ, hδ, hδ_prop⟩ := hy_cont_s (-y s / 2) (by linarith)
      obtain ⟨u, hu_in, hu_dist, hyu_nn⟩ := this δ hδ
      have := hδ_prop hu_in (by rw [Real.dist_eq]; exact hu_dist)
      rw [Real.dist_eq] at this
      have := abs_sub_lt_iff.mp this
      linarith
  -- s < t, else y t ≥ 0 contradicts h_neg.
  have hs_lt_t : s < t := by
    rcases lt_or_eq_of_le hs_le_t with h | h
    · exact h
    · exfalso; rw [← h] at h_neg; linarith
  -- On (s, t], y < 0.
  have hy_neg_on : ∀ u, s < u → u ≤ t → y u < 0 := by
    intro u hsu hut
    by_contra hu_nn
    push_neg at hu_nn
    have hu_in_S : u ∈ S :=
      ⟨⟨le_trans hs_nn (le_of_lt hsu), hut⟩, hu_nn⟩
    have : u ≤ s := le_csSup hS_bdd hu_in_S
    linarith
  -- By continuity and `hy_neg_on`, `y s = 0`: indeed `y s ≥ 0` and
  -- taking limit from the right (where y < 0) forces y s ≤ 0.
  have hys_zero : y s = 0 := by
    refine le_antisymm ?_ hys_nn
    by_contra h_pos
    push_neg at h_pos
    have hy_cont_s : ContinuousWithinAt y (Set.Icc 0 t) s :=
      hy_cont s hs_in_Icc
    rw [Metric.continuousWithinAt_iff] at hy_cont_s
    obtain ⟨δ, hδ, hδ_prop⟩ := hy_cont_s (y s) h_pos
    set u := min (s + δ / 2) t with hu_def
    have hu_lt_t : u ≤ t := min_le_right _ _
    have hsu : s < u := lt_min (by linarith) hs_lt_t
    have hu_mem : u ∈ Set.Icc (0 : ℝ) t :=
      ⟨le_trans hs_nn (le_of_lt hsu), hu_lt_t⟩
    have h_dist : dist u s < δ := by
      have h1 : u ≤ s + δ / 2 := min_le_left _ _
      rw [Real.dist_eq, abs_of_pos (by linarith : (0:ℝ) < u - s)]
      linarith
    have h_apply := hδ_prop hu_mem h_dist
    have hyu_close : |y u - y s| < y s := by rwa [Real.dist_eq] at h_apply
    have hyu_neg : y u < 0 := hy_neg_on u hsu hu_lt_t
    have : y u > 0 := by
      have := abs_sub_lt_iff.mp hyu_close; linarith
    linarith
  -- MVT on [s, t]: ∃ ξ ∈ (s, t) with (y t - y s)/(t - s) = 1 − y ξ ^ 3.
  have hy_cont_st : ContinuousOn y (Set.Icc s t) :=
    hy_cont.mono (fun u hu => ⟨le_trans hs_nn hu.1, hu.2⟩)
  have hy_diff_st : ∀ u ∈ Set.Ioo s t, HasDerivAt y (1 - (y u) ^ 3) u := by
    intro u ⟨hu1, hu2⟩
    have hu_nn : 0 ≤ u := le_trans hs_nn (le_of_lt hu1)
    exact hy_deriv u hu_nn
  obtain ⟨ξ, hξ_mem, hξ_eq⟩ :=
    exists_hasDerivAt_eq_slope y (fun u => 1 - (y u) ^ 3)
      hs_lt_t hy_cont_st (fun u hu => hy_diff_st u hu)
  -- On (s, t), y < 0, so y ξ < 0, hence (y ξ)^3 < 0, so 1 − (y ξ)^3 > 1 > 0.
  have hy_ξ_neg : y ξ < 0 := hy_neg_on ξ hξ_mem.1 (le_of_lt hξ_mem.2)
  have h_cube_neg : (y ξ) ^ 3 < 0 := by
    have := mul_pos (mul_pos (neg_pos.mpr hy_ξ_neg) (neg_pos.mpr hy_ξ_neg))
      (neg_pos.mpr hy_ξ_neg)
    have h_eq : (-(y ξ)) * (-(y ξ)) * (-(y ξ)) = -(y ξ) ^ 3 := by ring
    rw [h_eq] at this; linarith
  have hξ_pos : 0 < 1 - (y ξ) ^ 3 := by linarith
  have htsub : 0 < t - s := by linarith
  rw [hys_zero, sub_zero] at hξ_eq
  have h1 : 0 < y t / (t - s) := hξ_eq ▸ hξ_pos
  have : 0 < y t := by
    have := mul_pos h1 htsub
    rw [div_mul_cancel₀ _ (ne_of_gt htsub)] at this
    exact this
  linarith

/-- Upper barrier for the scalar cubic ODE `y' = 1 − y³` with `y(0) = 0`.
At the first time `s` where `y(s) = 1`, both `y` and the constant `1`
solve the ODE on `[s, t]` with the same value at `s`; ODE uniqueness
forces `y ≡ 1`, contradicting `y(t) > 1`. -/
private lemma scalar_cubic_upper_barrier
    {y : ℝ → ℝ}
    (hy0 : y 0 = 0)
    (hy_deriv : ∀ t, 0 ≤ t → HasDerivAt y (1 - (y t) ^ 3) t) :
    ∀ t, 0 ≤ t → y t ≤ 1 := by
  intro t ht_nn
  by_contra h_gt
  push_neg at h_gt
  -- y continuous on [0, t].
  have hy_cont : ContinuousOn y (Set.Icc 0 t) := by
    intro u hu
    exact (hy_deriv u hu.1).continuousAt.continuousWithinAt
  -- S := {u ∈ [0, t] | y u ≤ 1}, contains 0.
  let S : Set ℝ := {u | u ∈ Set.Icc (0 : ℝ) t ∧ y u ≤ 1}
  have h0_mem : (0 : ℝ) ∈ S :=
    ⟨⟨le_refl _, ht_nn⟩, by rw [hy0]; norm_num⟩
  have hS_bdd : BddAbove S := ⟨t, fun u hu => hu.1.2⟩
  have hS_nonempty : S.Nonempty := ⟨0, h0_mem⟩
  set s := sSup S with hs_def
  have hs_le_t : s ≤ t := csSup_le hS_nonempty (fun u hu => hu.1.2)
  have hs_nn : 0 ≤ s := le_csSup hS_bdd h0_mem
  have hs_in_Icc : s ∈ Set.Icc (0 : ℝ) t := ⟨hs_nn, hs_le_t⟩
  -- y s ≤ 1 by continuity from the left.
  have hys_le : y s ≤ 1 := by
    rcases eq_or_lt_of_le hs_nn with hs_zero | hs_pos
    · rw [← hs_zero, hy0]; norm_num
    · by_contra h_ys_gt
      push_neg at h_ys_gt
      have hy_cont_s : ContinuousWithinAt y (Set.Icc 0 t) s := hy_cont s hs_in_Icc
      rw [Metric.continuousWithinAt_iff] at hy_cont_s
      obtain ⟨δ, hδ, hδ_prop⟩ := hy_cont_s ((y s - 1) / 2) (by linarith)
      obtain ⟨u, hu_mem, hu_lt⟩ :=
        exists_lt_of_lt_csSup hS_nonempty (show s - δ < s by linarith)
      have hu_le : u ≤ s := le_csSup hS_bdd hu_mem
      have hu_dist : |u - s| < δ := by
        rw [abs_sub_lt_iff]; exact ⟨by linarith, by linarith⟩
      have := hδ_prop hu_mem.1 (by rw [Real.dist_eq]; exact hu_dist)
      rw [Real.dist_eq] at this
      have := abs_sub_lt_iff.mp this
      linarith [hu_mem.2]
  -- s < t.
  have hs_lt_t : s < t := by
    rcases lt_or_eq_of_le hs_le_t with h | h
    · exact h
    · exfalso; rw [← h] at h_gt; linarith
  -- y s = 1.
  have hys_eq : y s = 1 := by
    refine le_antisymm hys_le ?_
    by_contra h_ys_lt
    push_neg at h_ys_lt
    have hy_cont_s : ContinuousWithinAt y (Set.Icc 0 t) s := hy_cont s hs_in_Icc
    rw [Metric.continuousWithinAt_iff] at hy_cont_s
    obtain ⟨δ, hδ, hδ_prop⟩ := hy_cont_s ((1 - y s) / 2) (by linarith)
    set u := min (s + δ / 2) t with hu_def
    have hsu : s < u := lt_min (by linarith) hs_lt_t
    have hu_le_t : u ≤ t := min_le_right _ _
    have hu_mem_Icc : u ∈ Set.Icc (0 : ℝ) t :=
      ⟨le_trans hs_nn (le_of_lt hsu), hu_le_t⟩
    have hu_dist : dist u s < δ := by
      have h1 : u ≤ s + δ / 2 := min_le_left _ _
      rw [Real.dist_eq, abs_of_pos (by linarith : (0:ℝ) < u - s)]
      linarith
    have h_apply := hδ_prop hu_mem_Icc hu_dist
    rw [Real.dist_eq] at h_apply
    have := abs_sub_lt_iff.mp h_apply
    have hu_in_S : u ∈ S := ⟨hu_mem_Icc, by linarith⟩
    have : u ≤ s := le_csSup hS_bdd hu_in_S
    linarith
  -- On (s, t], y > 1.
  have hy_gt_on : ∀ u, s < u → u ≤ t → 1 < y u := by
    intro u hsu hut
    by_contra h_u_le
    push_neg at h_u_le
    have hu_in_S : u ∈ S :=
      ⟨⟨le_trans hs_nn (le_of_lt hsu), hut⟩, h_u_le⟩
    have : u ≤ s := le_csSup hS_bdd hu_in_S
    linarith
  -- ODE uniqueness on [s, t] between y and constant 1.
  have hy_cont_st : ContinuousOn y (Set.Icc s t) :=
    hy_cont.mono (fun u hu => ⟨le_trans hs_nn hu.1, hu.2⟩)
  -- Bound |y| on [s, t] via EVT.
  have h_st_ne : (Set.Icc s t).Nonempty :=
    ⟨s, ⟨le_refl _, hs_lt_t.le⟩⟩
  obtain ⟨u_y, _, hu_y_max⟩ :=
    isCompact_Icc.exists_isMaxOn h_st_ne hy_cont_st.abs
  set R : ℝ := |y u_y| + 2 with hR_def
  have hR_pos : 0 < R := by
    have h1 : 0 ≤ |y u_y| := abs_nonneg _
    linarith
  have hR_nn : 0 ≤ R := hR_pos.le
  have hy_bdd : ∀ u ∈ Set.Icc s t, |y u| ≤ R := by
    intro u hu
    have h1 : |y u| ≤ |y u_y| := hu_y_max hu
    linarith
  -- Vector field v(_, z) := 1 - z^3.
  let v : ℝ → ℝ → ℝ := fun _ z => 1 - z ^ 3
  set K_val : ℝ := 3 * R ^ 2 with hK_val_def
  have hK_nn : 0 ≤ K_val := by positivity
  let K : NNReal := Real.toNNReal K_val
  have hK_coe : (K : ℝ) = K_val := Real.coe_toNNReal K_val hK_nn
  -- Lipschitz on [-R, R] with constant K.
  have hv_lip : ∀ u ∈ Set.Ico s t, LipschitzOnWith K (v u) (Set.Icc (-R) R) := by
    intro u _
    rw [lipschitzOnWith_iff_dist_le_mul]
    intro z hz z' hz'
    rw [Real.dist_eq, Real.dist_eq, hK_coe]
    have hz_abs : |z| ≤ R := abs_le.mpr hz
    have hz'_abs : |z'| ≤ R := abs_le.mpr hz'
    have h_exp : v u z - v u z' = -(z ^ 3 - z' ^ 3) := by simp only [v]; ring
    rw [h_exp, abs_neg]
    have := cube_lipschitz_on_ball R hR_nn z z' hz_abs hz'_abs
    linarith [this]
  -- Constant function c ≡ 1.
  let c : ℝ → ℝ := fun _ => (1 : ℝ)
  have hc_cont : ContinuousOn c (Set.Icc s t) := continuousOn_const
  have hc_deriv : ∀ u ∈ Set.Ico s t,
      HasDerivWithinAt c (v u (c u)) (Set.Ici u) u := by
    intro u _
    have h_v : v u (c u) = 0 := by simp [v, c]
    rw [h_v]
    exact (hasDerivAt_const u (1 : ℝ)).hasDerivWithinAt
  have hy_within : ∀ u ∈ Set.Ico s t,
      HasDerivWithinAt y (v u (y u)) (Set.Ici u) u := by
    intro u ⟨hu1, _⟩
    have hu_nn : 0 ≤ u := le_trans hs_nn hu1
    exact (hy_deriv u hu_nn).hasDerivWithinAt
  have hy_in_s : ∀ u ∈ Set.Ico s t, y u ∈ Set.Icc (-R) R := fun u hu =>
    abs_le.mp (hy_bdd u ⟨hu.1, le_of_lt hu.2⟩)
  have hc_in_s : ∀ u ∈ Set.Ico s t, c u ∈ Set.Icc (-R) R := by
    intro u _
    show (1 : ℝ) ∈ Set.Icc (-R) R
    refine ⟨?_, ?_⟩ <;> · have h1 := abs_nonneg (y u_y); linarith
  have h_eq_at : y s = c s := hys_eq
  have hst_eqOn : Set.EqOn y c (Set.Icc s t) :=
    ODE_solution_unique_of_mem_Icc_right hv_lip hy_cont_st hy_within hy_in_s
      hc_cont hc_deriv hc_in_s h_eq_at
  have : y t = 1 := hst_eqOn ⟨hs_lt_t.le, le_refl _⟩
  linarith

/-- **Sub-lemma 3: original GPAC is bounded in [0, 1].** For
`y(0) = 0`, the solution of `y' = 1 − y³` stays in `[0, 1]` forever.
Standard monotonic-attractor argument: `y = 0 ⇒ y' = 1 > 0` (lower
barrier trivially holds with init = 0); `y = 1 ⇒ y' = 0` (upper barrier
sharp). -/
theorem scalar_cubic_original_bounded :
    ∃ ySol : ℝ → ℝ, ySol 0 = 0 ∧
      (∀ t ≥ (0 : ℝ), HasDerivAt ySol (1 - (ySol t) ^ 3) t) ∧
      (∀ t ≥ (0 : ℝ), 0 ≤ ySol t ∧ ySol t ≤ 1) := by
  classical
  -- Set up the Fin-1 encoding.
  let F : (Fin 1 → ℝ) → Fin 1 → ℝ := fun z _ => 1 - (z 0) ^ 3
  let y₀ : Fin 1 → ℝ := fun _ => 0
  -- Lipschitz of F on balls: follows from cube_lipschitz_on_ball pointwise.
  have h_lip : ∀ R : ℝ, 0 < R → ∃ L : ℝ, ∀ x y : Fin 1 → ℝ,
      ‖x‖ ≤ R → ‖y‖ ≤ R → ‖F x - F y‖ ≤ L * ‖x - y‖ := by
    intro R hR
    refine ⟨3 * R ^ 2, ?_⟩
    intro x y hx hy
    -- ‖F x - F y‖ = |(1 - x 0 ^ 3) - (1 - y 0 ^ 3)| = |y 0 ^ 3 - x 0 ^ 3|
    have hx0 : |x 0| ≤ R := by
      have := norm_le_pi_norm x 0
      rw [Real.norm_eq_abs] at this
      linarith [this.trans hx]
    have hy0 : |y 0| ≤ R := by
      have := norm_le_pi_norm y 0
      rw [Real.norm_eq_abs] at this
      linarith [this.trans hy]
    have h_coord : ‖F x - F y‖ ≤ 3 * R ^ 2 * |x 0 - y 0| := by
      rw [show F x - F y = fun _ => -(x 0 ^ 3 - y 0 ^ 3) by
            funext i; simp only [F, Pi.sub_apply]; ring]
      rw [pi_norm_le_iff_of_nonneg (by positivity)]
      intro i
      rw [Real.norm_eq_abs, abs_neg]
      exact cube_lipschitz_on_ball R hR.le (x 0) (y 0) hx0 hy0
    have h_diff_coord : |x 0 - y 0| ≤ ‖x - y‖ := by
      have := norm_le_pi_norm (x - y) 0
      rw [Real.norm_eq_abs] at this
      simpa [Pi.sub_apply] using this
    calc ‖F x - F y‖
        ≤ 3 * R ^ 2 * |x 0 - y 0| := h_coord
      _ ≤ 3 * R ^ 2 * ‖x - y‖ :=
          mul_le_mul_of_nonneg_left h_diff_coord (by positivity)
  -- Invariance: any Fin-1 solution on [0, T) with y(0) = 0 satisfies ‖y t‖ ≤ 1.
  have h_invariant : ∀ (T : ℝ), 0 < T → ∀ (w : ℝ → Fin 1 → ℝ),
      w 0 = y₀ →
      (∀ t ∈ Set.Ico (0 : ℝ) T, HasDerivAt w (F (w t)) t) →
      ∀ t ∈ Set.Ico (0 : ℝ) T, ‖w t‖ ≤ 1 := by
    intro T _hT w hw0 hw_deriv t htm
    -- Project to scalar: z τ := w τ 0.
    set z : ℝ → ℝ := fun τ => w τ 0 with hz_def
    -- z satisfies the scalar ODE on [0, T).
    have hz_deriv : ∀ τ ∈ Set.Ico (0 : ℝ) T,
        HasDerivAt z (1 - (z τ) ^ 3) τ := by
      intro τ hτ
      have h := hw_deriv τ hτ
      have hpi := (hasDerivAt_pi (φ := w) (φ' := F (w τ))).1 h
      have := hpi 0
      show HasDerivAt z (F (w τ) 0) τ
      exact this
    have hz0 : z 0 = 0 := by
      show w 0 0 = 0
      rw [hw0]
    -- Extend: we need hy_deriv on all of [0, ∞), but we only have it on [0, T).
    -- Apply the barrier arguments restricted to [0, T).
    -- Lower barrier: 0 ≤ z t on [0, T).
    -- We re-run the lower barrier argument, but scoped to [0, T).
    have hz_lb_Ico : ∀ τ, 0 ≤ τ → τ < T → 0 ≤ z τ := by
      -- Duplicate of scalar_cubic_lower_barrier, but with T cutoff on derivative.
      intro τ hτ_nn hτ_lt
      -- Reuse the same sup-argument on [0, τ].
      by_contra h_neg
      push_neg at h_neg
      have hz_cont_local : ContinuousOn z (Set.Icc 0 τ) := by
        intro u hu
        have hu_lt : u < T := lt_of_le_of_lt hu.2 hτ_lt
        exact (hz_deriv u ⟨hu.1, hu_lt⟩).continuousAt.continuousWithinAt
      let S : Set ℝ := {u | u ∈ Set.Icc (0 : ℝ) τ ∧ 0 ≤ z u}
      have h0_mem : (0 : ℝ) ∈ S := ⟨⟨le_refl _, hτ_nn⟩, by rw [hz0]⟩
      have hS_bdd : BddAbove S := ⟨τ, fun u hu => hu.1.2⟩
      have hS_nonempty : S.Nonempty := ⟨0, h0_mem⟩
      set s := sSup S with hs_def
      have hs_le_τ : s ≤ τ := csSup_le hS_nonempty (fun u hu => hu.1.2)
      have hs_nn : 0 ≤ s := le_csSup hS_bdd h0_mem
      have hs_in_Icc : s ∈ Set.Icc (0 : ℝ) τ := ⟨hs_nn, hs_le_τ⟩
      have hzs_nn : 0 ≤ z s := by
        have hz_cont_s : ContinuousWithinAt z (Set.Icc 0 τ) s :=
          hz_cont_local s hs_in_Icc
        rcases eq_or_lt_of_le hs_nn with hs_zero | hs_pos
        · rw [← hs_zero, hz0]
        · have h_seq : ∀ ε > 0, ∃ u ∈ S, s - ε < u ∧ u ≤ s := by
            intro ε hε
            obtain ⟨u, hu_mem, hu_lt⟩ :=
              exists_lt_of_lt_csSup hS_nonempty (show s - ε < s by linarith)
            exact ⟨u, hu_mem, hu_lt, le_csSup hS_bdd hu_mem⟩
          have hmix : ∀ ε > 0, ∃ u ∈ Set.Icc (0:ℝ) τ, |u - s| < ε ∧ 0 ≤ z u := by
            intro ε hε
            obtain ⟨u, ⟨hu1, hu2⟩, hu_lt, hu_le⟩ := h_seq ε hε
            refine ⟨u, hu1, ?_, hu2⟩
            rw [abs_sub_lt_iff]; exact ⟨by linarith, by linarith⟩
          by_contra h_zs_neg
          push_neg at h_zs_neg
          rw [Metric.continuousWithinAt_iff] at hz_cont_s
          obtain ⟨δ, hδ, hδ_prop⟩ := hz_cont_s (-z s / 2) (by linarith)
          obtain ⟨u, hu_in, hu_dist, hzu_nn⟩ := hmix δ hδ
          have := hδ_prop hu_in (by rw [Real.dist_eq]; exact hu_dist)
          rw [Real.dist_eq] at this
          have := abs_sub_lt_iff.mp this
          linarith
      have hs_lt_τ : s < τ := by
        rcases lt_or_eq_of_le hs_le_τ with h | h
        · exact h
        · exfalso; rw [← h] at h_neg; linarith
      have hz_neg_on : ∀ u, s < u → u ≤ τ → z u < 0 := by
        intro u hsu huτ
        by_contra hu_nn
        push_neg at hu_nn
        have hu_in_S : u ∈ S :=
          ⟨⟨le_trans hs_nn (le_of_lt hsu), huτ⟩, hu_nn⟩
        have : u ≤ s := le_csSup hS_bdd hu_in_S
        linarith
      have hzs_zero : z s = 0 := by
        refine le_antisymm ?_ hzs_nn
        by_contra h_pos
        push_neg at h_pos
        have hz_cont_s : ContinuousWithinAt z (Set.Icc 0 τ) s :=
          hz_cont_local s hs_in_Icc
        rw [Metric.continuousWithinAt_iff] at hz_cont_s
        obtain ⟨δ, hδ, hδ_prop⟩ := hz_cont_s (z s) h_pos
        set u := min (s + δ / 2) τ with hu_def
        have hu_le_τ : u ≤ τ := min_le_right _ _
        have hsu : s < u := lt_min (by linarith) hs_lt_τ
        have hu_mem : u ∈ Set.Icc (0 : ℝ) τ :=
          ⟨le_trans hs_nn (le_of_lt hsu), hu_le_τ⟩
        have h_dist : dist u s < δ := by
          have h1 : u ≤ s + δ / 2 := min_le_left _ _
          rw [Real.dist_eq, abs_of_pos (by linarith : (0:ℝ) < u - s)]
          linarith
        have h_apply := hδ_prop hu_mem h_dist
        have hzu_close : |z u - z s| < z s := by rwa [Real.dist_eq] at h_apply
        have hzu_neg : z u < 0 := hz_neg_on u hsu hu_le_τ
        have : z u > 0 := by
          have := abs_sub_lt_iff.mp hzu_close; linarith
        linarith
      have hz_cont_sτ : ContinuousOn z (Set.Icc s τ) :=
        hz_cont_local.mono (fun u hu => ⟨le_trans hs_nn hu.1, hu.2⟩)
      have hz_diff_sτ : ∀ u ∈ Set.Ioo s τ, HasDerivAt z (1 - (z u) ^ 3) u := by
        intro u ⟨hu1, hu2⟩
        have hu_nn : 0 ≤ u := le_trans hs_nn (le_of_lt hu1)
        have hu_lt_T : u < T := lt_trans hu2 hτ_lt
        exact hz_deriv u ⟨hu_nn, hu_lt_T⟩
      obtain ⟨ξ, hξ_mem, hξ_eq⟩ :=
        exists_hasDerivAt_eq_slope z (fun u => 1 - (z u) ^ 3)
          hs_lt_τ hz_cont_sτ (fun u hu => hz_diff_sτ u hu)
      have hz_ξ_neg : z ξ < 0 := hz_neg_on ξ hξ_mem.1 (le_of_lt hξ_mem.2)
      have h_cube_neg : (z ξ) ^ 3 < 0 := by
        have := mul_pos (mul_pos (neg_pos.mpr hz_ξ_neg) (neg_pos.mpr hz_ξ_neg))
          (neg_pos.mpr hz_ξ_neg)
        have h_eq : (-(z ξ)) * (-(z ξ)) * (-(z ξ)) = -(z ξ) ^ 3 := by ring
        rw [h_eq] at this; linarith
      have hξ_pos : 0 < 1 - (z ξ) ^ 3 := by linarith
      have hτsub : 0 < τ - s := by linarith
      rw [hzs_zero, sub_zero] at hξ_eq
      have h1 : 0 < z τ / (τ - s) := hξ_eq ▸ hξ_pos
      have : 0 < z τ := by
        have := mul_pos h1 hτsub
        rw [div_mul_cancel₀ _ (ne_of_gt hτsub)] at this; exact this
      linarith
    -- Upper barrier analogous.
    have hz_ub_Ico : ∀ τ, 0 ≤ τ → τ < T → z τ ≤ 1 := by
      intro τ hτ_nn hτ_lt
      by_contra h_gt
      push_neg at h_gt
      have hz_cont_local : ContinuousOn z (Set.Icc 0 τ) := by
        intro u hu
        have hu_lt : u < T := lt_of_le_of_lt hu.2 hτ_lt
        exact (hz_deriv u ⟨hu.1, hu_lt⟩).continuousAt.continuousWithinAt
      let S : Set ℝ := {u | u ∈ Set.Icc (0 : ℝ) τ ∧ z u ≤ 1}
      have h0_mem : (0 : ℝ) ∈ S :=
        ⟨⟨le_refl _, hτ_nn⟩, by rw [hz0]; norm_num⟩
      have hS_bdd : BddAbove S := ⟨τ, fun u hu => hu.1.2⟩
      have hS_nonempty : S.Nonempty := ⟨0, h0_mem⟩
      set s := sSup S with hs_def
      have hs_le_τ : s ≤ τ := csSup_le hS_nonempty (fun u hu => hu.1.2)
      have hs_nn : 0 ≤ s := le_csSup hS_bdd h0_mem
      have hs_in_Icc : s ∈ Set.Icc (0 : ℝ) τ := ⟨hs_nn, hs_le_τ⟩
      have hzs_le : z s ≤ 1 := by
        rcases eq_or_lt_of_le hs_nn with hs_zero | hs_pos
        · rw [← hs_zero, hz0]; norm_num
        · by_contra h_zs_gt
          push_neg at h_zs_gt
          have hz_cont_s : ContinuousWithinAt z (Set.Icc 0 τ) s :=
            hz_cont_local s hs_in_Icc
          rw [Metric.continuousWithinAt_iff] at hz_cont_s
          obtain ⟨δ, hδ, hδ_prop⟩ := hz_cont_s ((z s - 1) / 2) (by linarith)
          obtain ⟨u, hu_mem, hu_lt⟩ :=
            exists_lt_of_lt_csSup hS_nonempty (show s - δ < s by linarith)
          have hu_le : u ≤ s := le_csSup hS_bdd hu_mem
          have hu_dist : |u - s| < δ := by
            rw [abs_sub_lt_iff]; exact ⟨by linarith, by linarith⟩
          have := hδ_prop hu_mem.1 (by rw [Real.dist_eq]; exact hu_dist)
          rw [Real.dist_eq] at this
          have := abs_sub_lt_iff.mp this
          linarith [hu_mem.2]
      have hs_lt_τ : s < τ := by
        rcases lt_or_eq_of_le hs_le_τ with h | h
        · exact h
        · exfalso; rw [← h] at h_gt; linarith
      have hzs_eq : z s = 1 := by
        refine le_antisymm hzs_le ?_
        by_contra h_zs_lt
        push_neg at h_zs_lt
        have hz_cont_s : ContinuousWithinAt z (Set.Icc 0 τ) s :=
          hz_cont_local s hs_in_Icc
        rw [Metric.continuousWithinAt_iff] at hz_cont_s
        obtain ⟨δ, hδ, hδ_prop⟩ := hz_cont_s ((1 - z s) / 2) (by linarith)
        set u := min (s + δ / 2) τ with hu_def
        have hsu : s < u := lt_min (by linarith) hs_lt_τ
        have hu_le_τ : u ≤ τ := min_le_right _ _
        have hu_mem_Icc : u ∈ Set.Icc (0 : ℝ) τ :=
          ⟨le_trans hs_nn (le_of_lt hsu), hu_le_τ⟩
        have hu_dist : dist u s < δ := by
          have h1 : u ≤ s + δ / 2 := min_le_left _ _
          rw [Real.dist_eq, abs_of_pos (by linarith : (0:ℝ) < u - s)]
          linarith
        have h_apply := hδ_prop hu_mem_Icc hu_dist
        rw [Real.dist_eq] at h_apply
        have := abs_sub_lt_iff.mp h_apply
        have hu_in_S : u ∈ S := ⟨hu_mem_Icc, by linarith⟩
        have : u ≤ s := le_csSup hS_bdd hu_in_S
        linarith
      have hz_gt_on : ∀ u, s < u → u ≤ τ → 1 < z u := by
        intro u hsu huτ
        by_contra h_u_le
        push_neg at h_u_le
        have hu_in_S : u ∈ S :=
          ⟨⟨le_trans hs_nn (le_of_lt hsu), huτ⟩, h_u_le⟩
        have : u ≤ s := le_csSup hS_bdd hu_in_S
        linarith
      have hz_cont_sτ : ContinuousOn z (Set.Icc s τ) :=
        hz_cont_local.mono (fun u hu => ⟨le_trans hs_nn hu.1, hu.2⟩)
      have h_sτ_ne : (Set.Icc s τ).Nonempty :=
        ⟨s, ⟨le_refl _, hs_lt_τ.le⟩⟩
      obtain ⟨u_y, _, hu_y_max⟩ :=
        isCompact_Icc.exists_isMaxOn h_sτ_ne hz_cont_sτ.abs
      set R : ℝ := |z u_y| + 2 with hR_def
      have hR_pos : 0 < R := by
        have h1 : 0 ≤ |z u_y| := abs_nonneg _; linarith
      have hR_nn : 0 ≤ R := hR_pos.le
      have hz_bdd : ∀ u ∈ Set.Icc s τ, |z u| ≤ R := by
        intro u hu
        have h1 : |z u| ≤ |z u_y| := hu_y_max hu
        linarith
      let v : ℝ → ℝ → ℝ := fun _ w => 1 - w ^ 3
      set K_val : ℝ := 3 * R ^ 2 with hK_val_def
      have hK_nn : 0 ≤ K_val := by positivity
      let K : NNReal := Real.toNNReal K_val
      have hK_coe : (K : ℝ) = K_val := Real.coe_toNNReal K_val hK_nn
      have hv_lip : ∀ u ∈ Set.Ico s τ, LipschitzOnWith K (v u) (Set.Icc (-R) R) := by
        intro u _
        rw [lipschitzOnWith_iff_dist_le_mul]
        intro w hw w' hw'
        rw [Real.dist_eq, Real.dist_eq, hK_coe]
        have hw_abs : |w| ≤ R := abs_le.mpr hw
        have hw'_abs : |w'| ≤ R := abs_le.mpr hw'
        have h_exp : v u w - v u w' = -(w ^ 3 - w' ^ 3) := by simp only [v]; ring
        rw [h_exp, abs_neg]
        have := cube_lipschitz_on_ball R hR_nn w w' hw_abs hw'_abs
        linarith [this]
      let c : ℝ → ℝ := fun _ => (1 : ℝ)
      have hc_cont : ContinuousOn c (Set.Icc s τ) := continuousOn_const
      have hc_deriv : ∀ u ∈ Set.Ico s τ,
          HasDerivWithinAt c (v u (c u)) (Set.Ici u) u := by
        intro u _
        have h_v : v u (c u) = 0 := by simp [v, c]
        rw [h_v]
        exact (hasDerivAt_const u (1 : ℝ)).hasDerivWithinAt
      have hz_within : ∀ u ∈ Set.Ico s τ,
          HasDerivWithinAt z (v u (z u)) (Set.Ici u) u := by
        intro u ⟨hu1, hu2⟩
        have hu_nn : 0 ≤ u := le_trans hs_nn hu1
        have hu_lt_T : u < T := lt_trans hu2 hτ_lt
        exact (hz_deriv u ⟨hu_nn, hu_lt_T⟩).hasDerivWithinAt
      have hz_in_s : ∀ u ∈ Set.Ico s τ, z u ∈ Set.Icc (-R) R := fun u hu =>
        abs_le.mp (hz_bdd u ⟨hu.1, le_of_lt hu.2⟩)
      have hc_in_s : ∀ u ∈ Set.Ico s τ, c u ∈ Set.Icc (-R) R := by
        intro u _
        show (1 : ℝ) ∈ Set.Icc (-R) R
        refine ⟨?_, ?_⟩ <;> · have h1 := abs_nonneg (z u_y); linarith
      have h_eq_at : z s = c s := hzs_eq
      have hsτ_eqOn : Set.EqOn z c (Set.Icc s τ) :=
        ODE_solution_unique_of_mem_Icc_right hv_lip hz_cont_sτ hz_within hz_in_s
          hc_cont hc_deriv hc_in_s h_eq_at
      have : z τ = 1 := hsτ_eqOn ⟨hs_lt_τ.le, le_refl _⟩
      linarith
    -- Combine: |z t| ≤ 1, so ‖w t‖ ≤ 1.
    have hlb : 0 ≤ z t := hz_lb_Ico t htm.1 htm.2
    have hub : z t ≤ 1 := hz_ub_Ico t htm.1 htm.2
    -- ‖w t‖ = |w t 0| (Fin 1 norm).
    rw [pi_norm_le_iff_of_nonneg zero_le_one]
    intro i
    have hi0 : i = 0 := Subsingleton.elim i 0
    subst hi0
    rw [Real.norm_eq_abs]
    show |z t| ≤ 1
    rw [abs_le]
    exact ⟨by linarith, hub⟩
  -- Apply the global ODE existence theorem.
  obtain ⟨w, hw0, hw_deriv, _hw_cont⟩ :=
    locally_lipschitz_bounded_global_ode_proved_continuous F y₀ h_lip 1
      (by norm_num) h_invariant
  -- Project back to a real-valued function.
  refine ⟨fun τ => w τ 0, ?_, ?_, ?_⟩
  · show w 0 0 = 0
    rw [hw0]
  · intro t ht
    have h := hw_deriv t ht
    have hpi := (hasDerivAt_pi (φ := w) (φ' := F (w t))).1 h
    have := hpi 0
    show HasDerivAt (fun τ => w τ 0) (F (w t) 0) t
    exact this
  · intro t ht
    -- Build scalar ODE on ℝ, and re-apply barriers on that to get the
    -- pointwise bounds.  Since hw_deriv only requires 0 ≤ t, we set up a
    -- scalar-ODE version on all of [0, ∞).
    set z : ℝ → ℝ := fun τ => w τ 0 with hz_def
    have hz_deriv_all : ∀ τ, 0 ≤ τ → HasDerivAt z (1 - (z τ) ^ 3) τ := by
      intro τ hτ
      have h := hw_deriv τ hτ
      have hpi := (hasDerivAt_pi (φ := w) (φ' := F (w τ))).1 h
      have := hpi 0
      show HasDerivAt z (F (w τ) 0) τ
      exact this
    have hz0 : z 0 = 0 := by show w 0 0 = 0; rw [hw0]
    have hlb := scalar_cubic_lower_barrier hz0 hz_deriv_all t ht
    have hub := scalar_cubic_upper_barrier hz0 hz_deriv_all t ht
    exact ⟨hlb, hub⟩

/-- **Sub-lemma 4: σ-drift identity.** For any dual-rail solution, the
sum `σ := u + v` satisfies
  `σ' = 1 + σ³ − (k/2)(σ² − y²)`
where `y := u − v`. Using `2uv = (σ² − y²)/2` (i.e. `4uv = σ² − y²`). -/
theorem scalar_cubic_sigma_drift (k : ℚ) (sol : ℝ → Fin 2 → ℝ)
    (h_deriv : ∀ t ≥ (0 : ℝ),
      HasDerivAt (fun s => sol s) ((dualRailedCubic k).evalField (sol t)) t) :
    ∀ t ≥ (0 : ℝ),
      HasDerivAt (fun s => sol s 0 + sol s 1)
        (1 + (sol t 0 + sol t 1) ^ 3
          - (k : ℝ) / 2 * ((sol t 0 + sol t 1) ^ 2 - (sol t 0 - sol t 1) ^ 2)) t := by
  intro t ht
  have h := h_deriv t ht
  have hpi := (hasDerivAt_pi (φ := fun s => sol s)
    (φ' := (dualRailedCubic k).evalField (sol t))).1 h
  have hu := hpi 0
  have hv := hpi 1
  have hadd := hu.add hv
  -- The RHS of hadd is (evalField (sol t)) 0 + (evalField (sol t)) 1.
  -- Rewrite via drift_sum and then align (σ² − y²)/2 = 2·u·v algebraically.
  rw [dualRailedCubic_drift_sum k (sol t)] at hadd
  -- Goal: HasDerivAt (fun s => sol s 0 + sol s 1)
  --        (1 + (sol t 0 + sol t 1)^3 - (k/2) ((σ)^2 − y^2)) t
  -- hadd : same, with drift value `1 + (sol t 0 + sol t 1)^3 − 2·k·(sol t 0)·(sol t 1)`.
  -- These are equal by `(σ² − y²)/2 = 2uv` (i.e. (σ²−y²) = 4uv, k/2 · 4uv = 2kuv).
  have halg :
      1 + (sol t 0 + sol t 1) ^ 3 - 2 * (k : ℝ) * (sol t 0) * (sol t 1)
        = 1 + (sol t 0 + sol t 1) ^ 3
          - (k : ℝ) / 2 * ((sol t 0 + sol t 1) ^ 2 - (sol t 0 - sol t 1) ^ 2) := by
    ring
  rw [halg] at hadd
  exact hadd

/-- **Sub-lemma 5: σ forward-invariance.** For `k > scalarCubicThreshold`
and `|y| ≤ 1`, there is a constant `Σ` (depending on `k`) such that any
σ trajectory starting at `σ(0) = 0` satisfies `σ(t) ≤ Σ` forever.

The key constant is `σ_⁻(1)`, the smaller root of
`Q_k(σ; 1) = σ³ − (k/2)σ² + k/2 + 1 = 0`,
which exists as a real number for `k > scalarCubicThreshold` by
saddle-node bifurcation. For concreteness take `Σ := k`, a loose
overestimate (`σ_⁻(1) ≤ k/2` for large k, so `Σ = k` is safe). -/
theorem scalar_cubic_sigma_bound (k : ℚ) (hk : scalarCubicThreshold < (k : ℝ))
    (σ y : ℝ → ℝ) (hσ0 : σ 0 = 0) (hy_bound : ∀ t ≥ (0 : ℝ), |y t| ≤ 1)
    (h_deriv : ∀ t ≥ (0 : ℝ),
      HasDerivAt σ (1 + (σ t) ^ 3 - (k : ℝ) / 2 * ((σ t) ^ 2 - (y t) ^ 2)) t) :
    ∀ t ≥ (0 : ℝ), 0 ≤ σ t ∧ σ t ≤ (k : ℝ) := by
  -- Basic facts about k: k > 6 > 0.
  have hk6 : (6 : ℝ) < (k : ℝ) := by
    have := hk
    unfold scalarCubicThreshold at this
    exact this
  have hk_pos : (0 : ℝ) < (k : ℝ) := by linarith
  -- σ is continuous on [0, ∞).
  have hσ_cont : ∀ t, 0 ≤ t → ContinuousAt σ t := fun t ht =>
    (h_deriv t ht).continuousAt
  -- **Lower barrier: 0 ≤ σ t.**
  -- Drift at σ = 0 is 1 + (k/2) y², which is ≥ 1 > 0; hence σ cannot dip below 0.
  have h_lower : ∀ t, 0 ≤ t → 0 ≤ σ t := by
    intro t ht_nn
    by_contra h_neg
    push_neg at h_neg
    -- σ continuous on [0, t].
    have hσ_cont_Icc : ContinuousOn σ (Set.Icc 0 t) := fun u hu =>
      (hσ_cont u hu.1).continuousWithinAt
    -- S := {u ∈ [0, t] | 0 ≤ σ u}.
    let S : Set ℝ := {u | u ∈ Set.Icc (0 : ℝ) t ∧ 0 ≤ σ u}
    have h0_mem : (0 : ℝ) ∈ S := ⟨⟨le_refl _, ht_nn⟩, by rw [hσ0]⟩
    have hS_bdd : BddAbove S := ⟨t, fun u hu => hu.1.2⟩
    have hS_nonempty : S.Nonempty := ⟨0, h0_mem⟩
    set s := sSup S with hs_def
    have hs_le_t : s ≤ t := csSup_le hS_nonempty (fun u hu => hu.1.2)
    have hs_nn : 0 ≤ s := le_csSup hS_bdd h0_mem
    have hs_in_Icc : s ∈ Set.Icc (0 : ℝ) t := ⟨hs_nn, hs_le_t⟩
    -- σ s ≥ 0 by continuity on the left.
    have hσs_nn : 0 ≤ σ s := by
      rcases eq_or_lt_of_le hs_nn with hs_zero | hs_pos
      · rw [← hs_zero, hσ0]
      · have hσ_cont_s : ContinuousWithinAt σ (Set.Icc 0 t) s :=
          hσ_cont_Icc s hs_in_Icc
        have h_seq : ∀ ε > 0, ∃ u ∈ S, s - ε < u ∧ u ≤ s := by
          intro ε hε
          obtain ⟨u, hu_mem, hu_lt⟩ :=
            exists_lt_of_lt_csSup hS_nonempty (show s - ε < s by linarith)
          exact ⟨u, hu_mem, hu_lt, le_csSup hS_bdd hu_mem⟩
        have h_approach :
            ∀ ε > 0, ∃ u ∈ Set.Icc (0:ℝ) t, |u - s| < ε ∧ 0 ≤ σ u := by
          intro ε hε
          obtain ⟨u, ⟨hu1, hu2⟩, hu_lt, hu_le⟩ := h_seq ε hε
          refine ⟨u, hu1, ?_, hu2⟩
          rw [abs_sub_lt_iff]; exact ⟨by linarith, by linarith⟩
        by_contra h_σs_neg
        push_neg at h_σs_neg
        rw [Metric.continuousWithinAt_iff] at hσ_cont_s
        obtain ⟨δ, hδ, hδ_prop⟩ := hσ_cont_s (-σ s / 2) (by linarith)
        obtain ⟨u, hu_in, hu_dist, hσu_nn⟩ := h_approach δ hδ
        have := hδ_prop hu_in (by rw [Real.dist_eq]; exact hu_dist)
        rw [Real.dist_eq] at this
        have := abs_sub_lt_iff.mp this
        linarith
    -- s < t (else σ t ≥ 0 contradicts h_neg).
    have hs_lt_t : s < t := by
      rcases lt_or_eq_of_le hs_le_t with h | h
      · exact h
      · exfalso; rw [← h] at h_neg; linarith
    -- On (s, t], σ < 0.
    have hσ_neg_on : ∀ u, s < u → u ≤ t → σ u < 0 := by
      intro u hsu hut
      by_contra hu_nn
      push_neg at hu_nn
      have hu_in_S : u ∈ S :=
        ⟨⟨le_trans hs_nn (le_of_lt hsu), hut⟩, hu_nn⟩
      have : u ≤ s := le_csSup hS_bdd hu_in_S
      linarith
    -- σ s = 0 (σ s ≥ 0 and limit from the right forces ≤ 0, since σ u < 0 near s⁺).
    have hσs_zero : σ s = 0 := by
      refine le_antisymm ?_ hσs_nn
      by_contra h_pos
      push_neg at h_pos
      -- σ continuous at s ⇒ σ u close to σ s > 0 in a neighborhood,
      -- contradicting σ u < 0 on (s, t].
      have hσ_cont_s : ContinuousWithinAt σ (Set.Icc 0 t) s :=
        hσ_cont_Icc s hs_in_Icc
      rw [Metric.continuousWithinAt_iff] at hσ_cont_s
      obtain ⟨δ, hδ, hδ_prop⟩ := hσ_cont_s (σ s) h_pos
      set u := min (s + δ / 2) t with hu_def
      have hu_lt_t : u ≤ t := min_le_right _ _
      have hsu : s < u := lt_min (by linarith) hs_lt_t
      have hu_mem : u ∈ Set.Icc (0 : ℝ) t :=
        ⟨le_trans hs_nn (le_of_lt hsu), hu_lt_t⟩
      have h_dist : dist u s < δ := by
        have h1 : u ≤ s + δ / 2 := min_le_left _ _
        rw [Real.dist_eq, abs_of_pos (by linarith : (0:ℝ) < u - s)]
        linarith
      have h_apply := hδ_prop hu_mem h_dist
      have : |σ u - σ s| < σ s := by rwa [Real.dist_eq] at h_apply
      have hσu_neg : σ u < 0 := hσ_neg_on u hsu hu_lt_t
      have := abs_sub_lt_iff.mp this
      linarith
    -- Now use the derivative at s: drift(s) = 1 + (k/2) y(s)² ≥ 1 > 0.
    have h_deriv_s :
        HasDerivAt σ (1 + (σ s) ^ 3 - (k : ℝ) / 2 * ((σ s) ^ 2 - (y s) ^ 2)) s :=
      h_deriv s hs_nn
    have h_drift_val :
        (1 + (σ s) ^ 3 - (k : ℝ) / 2 * ((σ s) ^ 2 - (y s) ^ 2))
          = 1 + (k : ℝ) / 2 * (y s) ^ 2 := by
      rw [hσs_zero]; ring
    rw [h_drift_val] at h_deriv_s
    set d : ℝ := 1 + (k : ℝ) / 2 * (y s) ^ 2 with hd_def
    have hd_pos : 0 < d := by
      have hy_sq_nn : 0 ≤ (y s) ^ 2 := sq_nonneg _
      have : 0 ≤ (k : ℝ) / 2 * (y s) ^ 2 :=
        mul_nonneg (by linarith) hy_sq_nn
      linarith
    -- Extract the little-o bound at ε = d/2.
    have h_lo : (fun h => σ (s + h) - σ s - h • d) =o[nhds 0] fun h => h :=
      (hasDerivAt_iff_isLittleO_nhds_zero.mp h_deriv_s)
    have h_bnd_ev : ∀ᶠ h in nhds (0 : ℝ), ‖σ (s + h) - σ s - h • d‖ ≤ (d / 2) * ‖h‖ :=
      h_lo.def (by linarith : 0 < d / 2)
    -- Convert to an explicit δ > 0.
    rw [Metric.eventually_nhds_iff] at h_bnd_ev
    obtain ⟨δ, hδ, hδ_prop⟩ := h_bnd_ev
    -- Pick h = min(δ/2, (t - s)/2) > 0.
    set h := min (δ / 2) ((t - s) / 2) with hh_def
    have hh_pos : 0 < h := lt_min (by linarith) (by linarith)
    have hh_lt_ts : h ≤ (t - s) / 2 := min_le_right _ _
    have hh_lt_δ : h < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hh_dist : dist h 0 < δ := by
      rw [Real.dist_0_eq_abs, abs_of_pos hh_pos]
      exact hh_lt_δ
    have h_ineq := hδ_prop hh_dist
    -- σ(s + h) ≥ (d/2) * h > 0.
    have hσ_h_pos : 0 < σ (s + h) := by
      rw [hσs_zero] at h_ineq
      have h_simp : σ (s + h) - 0 - h • d = σ (s + h) - h * d := by
        simp [smul_eq_mul]
      rw [h_simp] at h_ineq
      have h_abs_h : ‖h‖ = h := by rw [Real.norm_eq_abs, abs_of_pos hh_pos]
      rw [h_abs_h] at h_ineq
      -- From ‖σ(s+h) - h·d‖ ≤ (d/2)·h, get σ(s+h) ≥ h·d - (d/2)·h = (d/2)·h > 0.
      have h_norm_eq : ‖σ (s + h) - h * d‖ = |σ (s + h) - h * d| := Real.norm_eq_abs _
      rw [h_norm_eq] at h_ineq
      have h_abs_lb : -(d / 2 * h) ≤ σ (s + h) - h * d :=
        neg_le_of_abs_le h_ineq
      have h_half_d_h : 0 < (d / 2) * h :=
        mul_pos (by linarith : (0:ℝ) < d / 2) hh_pos
      nlinarith
    -- But σ(s + h) < 0 since s + h ∈ (s, t].
    have hs_h_lt_t : s + h ≤ t := by linarith
    have hs_lt_sh : s < s + h := by linarith
    have : σ (s + h) < 0 := hσ_neg_on (s + h) hs_lt_sh hs_h_lt_t
    linarith
  -- **Upper barrier: σ t ≤ k/3 ≤ k.**
  -- Drift at σ = k/3, |y| ≤ 1 is ≤ -k³/54 + 1 + k/2, which is < 0 iff k > 6.
  have h_upper_kth : ∀ t, 0 ≤ t → σ t ≤ (k : ℝ) / 3 := by
    intro t ht_nn
    by_contra h_gt
    push_neg at h_gt
    -- σ continuous on [0, t].
    have hσ_cont_Icc : ContinuousOn σ (Set.Icc 0 t) := fun u hu =>
      (hσ_cont u hu.1).continuousWithinAt
    -- S := {u ∈ [0, t] | σ u ≤ k/3}.
    let S : Set ℝ := {u | u ∈ Set.Icc (0 : ℝ) t ∧ σ u ≤ (k : ℝ) / 3}
    have h0_mem : (0 : ℝ) ∈ S :=
      ⟨⟨le_refl _, ht_nn⟩, by rw [hσ0]; linarith⟩
    have hS_bdd : BddAbove S := ⟨t, fun u hu => hu.1.2⟩
    have hS_nonempty : S.Nonempty := ⟨0, h0_mem⟩
    set s := sSup S with hs_def
    have hs_le_t : s ≤ t := csSup_le hS_nonempty (fun u hu => hu.1.2)
    have hs_nn : 0 ≤ s := le_csSup hS_bdd h0_mem
    have hs_in_Icc : s ∈ Set.Icc (0 : ℝ) t := ⟨hs_nn, hs_le_t⟩
    -- σ s ≤ k/3 by continuity from the left.
    have hσs_le : σ s ≤ (k : ℝ) / 3 := by
      rcases eq_or_lt_of_le hs_nn with hs_zero | hs_pos
      · rw [← hs_zero, hσ0]; linarith
      · by_contra h_σs_gt
        push_neg at h_σs_gt
        have hσ_cont_s : ContinuousWithinAt σ (Set.Icc 0 t) s :=
          hσ_cont_Icc s hs_in_Icc
        rw [Metric.continuousWithinAt_iff] at hσ_cont_s
        obtain ⟨δ, hδ, hδ_prop⟩ := hσ_cont_s ((σ s - (k : ℝ) / 3) / 2) (by linarith)
        obtain ⟨u, hu_mem, hu_lt⟩ :=
          exists_lt_of_lt_csSup hS_nonempty (show s - δ < s by linarith)
        have hu_le : u ≤ s := le_csSup hS_bdd hu_mem
        have hu_dist : |u - s| < δ := by
          rw [abs_sub_lt_iff]; exact ⟨by linarith, by linarith⟩
        have := hδ_prop hu_mem.1 (by rw [Real.dist_eq]; exact hu_dist)
        rw [Real.dist_eq] at this
        have := abs_sub_lt_iff.mp this
        linarith [hu_mem.2]
    -- s < t.
    have hs_lt_t : s < t := by
      rcases lt_or_eq_of_le hs_le_t with h | h
      · exact h
      · exfalso; rw [← h] at h_gt; linarith
    -- σ s = k/3 (else σ s < k/3, which contradicts s being sup by continuity).
    have hσs_eq : σ s = (k : ℝ) / 3 := by
      refine le_antisymm hσs_le ?_
      by_contra h_σs_lt
      push_neg at h_σs_lt
      have hσ_cont_s : ContinuousWithinAt σ (Set.Icc 0 t) s :=
        hσ_cont_Icc s hs_in_Icc
      rw [Metric.continuousWithinAt_iff] at hσ_cont_s
      obtain ⟨δ, hδ, hδ_prop⟩ := hσ_cont_s (((k : ℝ) / 3 - σ s) / 2) (by linarith)
      set u := min (s + δ / 2) t with hu_def
      have hsu : s < u := lt_min (by linarith) hs_lt_t
      have hu_le_t : u ≤ t := min_le_right _ _
      have hu_mem_Icc : u ∈ Set.Icc (0 : ℝ) t :=
        ⟨le_trans hs_nn (le_of_lt hsu), hu_le_t⟩
      have hu_dist : dist u s < δ := by
        have h1 : u ≤ s + δ / 2 := min_le_left _ _
        rw [Real.dist_eq, abs_of_pos (by linarith : (0:ℝ) < u - s)]
        linarith
      have h_apply := hδ_prop hu_mem_Icc hu_dist
      rw [Real.dist_eq] at h_apply
      have := abs_sub_lt_iff.mp h_apply
      have hu_in_S : u ∈ S := ⟨hu_mem_Icc, by linarith⟩
      have : u ≤ s := le_csSup hS_bdd hu_in_S
      linarith
    -- On (s, t], σ > k/3.
    have hσ_gt_on : ∀ u, s < u → u ≤ t → (k : ℝ) / 3 < σ u := by
      intro u hsu hut
      by_contra h_u_le
      push_neg at h_u_le
      have hu_in_S : u ∈ S :=
        ⟨⟨le_trans hs_nn (le_of_lt hsu), hut⟩, h_u_le⟩
      have : u ≤ s := le_csSup hS_bdd hu_in_S
      linarith
    -- Now use drift at s with σ s = k/3:
    -- drift(s) = -k³/54 + 1 + (k/2)(y s)²
    -- ≤ -k³/54 + 1 + k/2 (since (y s)² ≤ 1, k > 0)
    -- < 0 (since k > 6).
    have h_deriv_s :
        HasDerivAt σ (1 + (σ s) ^ 3 - (k : ℝ) / 2 * ((σ s) ^ 2 - (y s) ^ 2)) s :=
      h_deriv s hs_nn
    have hy_s_bd : |y s| ≤ 1 := hy_bound s hs_nn
    have hy_s_sq_le : (y s) ^ 2 ≤ 1 := by
      have h_sq : (y s) ^ 2 = |y s| ^ 2 := (sq_abs _).symm
      rw [h_sq]
      have := hy_s_bd
      have h_abs_nn : 0 ≤ |y s| := abs_nonneg _
      nlinarith
    have h_drift_val :
        1 + (σ s) ^ 3 - (k : ℝ) / 2 * ((σ s) ^ 2 - (y s) ^ 2)
          = -((k : ℝ) ^ 3) / 54 + 1 + (k : ℝ) / 2 * (y s) ^ 2 := by
      rw [hσs_eq]; ring
    rw [h_drift_val] at h_deriv_s
    set d : ℝ := -((k : ℝ) ^ 3) / 54 + 1 + (k : ℝ) / 2 * (y s) ^ 2 with hd_def
    -- d < 0: -k³/54 + 1 + (k/2)(y s)² ≤ -k³/54 + 1 + k/2.
    -- We need (-k³/54 + 1 + k/2) < 0, i.e. k³ > 54 + 27k, i.e. (k-6)(k+3)² > 0 for k > 6.
    have hd_neg : d < 0 := by
      have h_ub : d ≤ -((k : ℝ) ^ 3) / 54 + 1 + (k : ℝ) / 2 := by
        have : (k : ℝ) / 2 * (y s) ^ 2 ≤ (k : ℝ) / 2 * 1 := by
          have hk2_nn : 0 ≤ (k : ℝ) / 2 := by linarith
          exact mul_le_mul_of_nonneg_left hy_s_sq_le hk2_nn
        simp at this
        linarith
      -- Show -k³/54 + 1 + k/2 < 0 for k > 6.
      -- Equivalently: k³ > 27k + 54. Factor: k³ - 27k - 54 = (k - 6)(k + 3)².
      have h_factor : (k : ℝ)^3 - 27 * (k : ℝ) - 54 = ((k : ℝ) - 6) * ((k : ℝ) + 3)^2 := by
        ring
      have hk_minus_6_pos : 0 < (k : ℝ) - 6 := by linarith
      have hk_plus_3_sq_nn : 0 ≤ ((k : ℝ) + 3)^2 := sq_nonneg _
      have hk_plus_3_pos : 0 < (k : ℝ) + 3 := by linarith
      have hk_plus_3_sq_pos : 0 < ((k : ℝ) + 3)^2 := by positivity
      have h_rhs_pos : 0 < ((k : ℝ) - 6) * ((k : ℝ) + 3)^2 :=
        mul_pos hk_minus_6_pos hk_plus_3_sq_pos
      have : 0 < (k : ℝ)^3 - 27 * (k : ℝ) - 54 := by rw [h_factor]; exact h_rhs_pos
      have h_upper_strict : -((k : ℝ) ^ 3) / 54 + 1 + (k : ℝ) / 2 < 0 := by linarith
      linarith
    -- Apply derivative definition to get σ decreasing at s.
    have h_lo : (fun h => σ (s + h) - σ s - h • d) =o[nhds 0] fun h => h :=
      (hasDerivAt_iff_isLittleO_nhds_zero.mp h_deriv_s)
    have h_bnd_ev : ∀ᶠ h in nhds (0 : ℝ), ‖σ (s + h) - σ s - h • d‖ ≤ (-d / 2) * ‖h‖ :=
      h_lo.def (by linarith : 0 < -d / 2)
    rw [Metric.eventually_nhds_iff] at h_bnd_ev
    obtain ⟨δ, hδ, hδ_prop⟩ := h_bnd_ev
    set hh := min (δ / 2) ((t - s) / 2) with hh_def
    have hh_pos : 0 < hh := lt_min (by linarith) (by linarith)
    have hh_lt_ts : hh ≤ (t - s) / 2 := min_le_right _ _
    have hh_lt_δ : hh < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hh_dist : dist hh 0 < δ := by
      rw [Real.dist_0_eq_abs, abs_of_pos hh_pos]; exact hh_lt_δ
    have h_ineq := hδ_prop hh_dist
    -- σ(s + hh) - σ s - hh * d has abs ≤ (-d/2) * hh.
    -- So σ(s + hh) ≤ σ s + hh * d + (-d/2)*hh = σ s + (d/2) * hh < σ s = k/3.
    have hσ_sh_lt : σ (s + hh) < σ s := by
      have h_norm_eq : ‖σ (s + hh) - σ s - hh • d‖ = |σ (s + hh) - σ s - hh * d| := by
        rw [Real.norm_eq_abs]; simp [smul_eq_mul]
      rw [h_norm_eq] at h_ineq
      have h_abs_h : ‖hh‖ = hh := by rw [Real.norm_eq_abs, abs_of_pos hh_pos]
      rw [h_abs_h] at h_ineq
      have h_upper : σ (s + hh) - σ s - hh * d ≤ -d / 2 * hh :=
        le_of_abs_le h_ineq
      have h_hh_d_neg : hh * d < 0 := mul_neg_of_pos_of_neg hh_pos hd_neg
      -- σ(s+hh) ≤ σ s + hh*d + (-d/2)*hh = σ s + (d/2) * hh
      nlinarith
    rw [hσs_eq] at hσ_sh_lt
    have hs_h_lt_t : s + hh ≤ t := by linarith
    have hs_lt_sh : s < s + hh := by linarith
    have : (k : ℝ) / 3 < σ (s + hh) := hσ_gt_on (s + hh) hs_lt_sh hs_h_lt_t
    linarith
  -- Combine lower + upper → the stated bound.
  intro t ht
  refine ⟨h_lower t ht, ?_⟩
  have h_kth := h_upper_kth t ht
  -- σ t ≤ k/3 ≤ k since k > 0.
  have : (k : ℝ) / 3 ≤ (k : ℝ) := by linarith
  linarith

/-- **Sub-lemma 6: Picard existence from invariance.** Combining
Sub-lemmas 1-5 yields global existence and boundedness for the dual-
rail solution. Uses `locally_lipschitz_bounded_global_ode_proved_continuous`
from `Ripple/Core/ODEGlobal.lean`. -/
theorem scalar_cubic_picard (k : ℚ) (hk : scalarCubicThreshold < (k : ℝ)) :
    ∃ (sol : ℝ → Fin 2 → ℝ),
      sol 0 = (fun _ => 0) ∧
      (∀ t ≥ (0 : ℝ),
        HasDerivAt (fun s => sol s) ((dualRailedCubic k).evalField (sol t)) t) ∧
      (∀ t ≥ (0 : ℝ), ∀ i, 0 ≤ sol t i ∧ sol t i ≤ (k : ℝ)) := by
  sorry

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
  intro k hk
  obtain ⟨sol, h_init, h_deriv, h_bound⟩ := scalar_cubic_picard k hk
  refine ⟨sol, (k : ℝ), ?_, h_bound, h_deriv, h_init⟩
  -- `(k : ℝ) > 0` follows from `k > scalarCubicThreshold > 0`.
  exact lt_trans scalarCubicThreshold_pos hk

/-- **Corollary.** Instantiated at a specific concrete `k`, e.g. `k = 10`
(well above the threshold `6`), the scalar-cubic dual-rail
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
    have h10 : ((10 : ℚ) : ℝ) = 10 := by norm_num
    rw [h10]; norm_num
  exact scalar_cubic_bounded 10 hk

end ScalarCubic
end DualRail
end Ripple
