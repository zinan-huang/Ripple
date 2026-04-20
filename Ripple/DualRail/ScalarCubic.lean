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
import Mathlib.Analysis.Calculus.Deriv.Prod

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

/-! ## Proof sub-lemmas (Tier 1)

The main theorem decomposes into six analytic pieces. Each is stated
here with `sorry` so `scalar_cubic_bounded` can consume them directly
and so individual work fronts are visible. -/

/-- **Sub-lemma 1: non-negativity of the dual-rail solution.** If a
solution `sol` to `dualRailedCubic k` starts at the origin, both
components stay non-negative on `[0, ∞)`. -/
theorem scalar_cubic_nonneg (k : ℚ) (sol : ℝ → Fin 2 → ℝ)
    (h_init : sol 0 = fun _ => 0)
    (h_deriv : ∀ t ≥ (0 : ℝ),
      HasDerivAt (fun s => sol s) ((dualRailedCubic k).evalField (sol t)) t) :
    ∀ t ≥ (0 : ℝ), ∀ i, 0 ≤ sol t i := by
  sorry

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

/-- **Sub-lemma 3: original GPAC is bounded in [0, 1].** For
`y(0) = 0`, the solution of `y' = 1 − y³` stays in `[0, 1]` forever.
Standard monotonic-attractor argument: `y = 0 ⇒ y' = 1 > 0` (lower
barrier trivially holds with init = 0); `y = 1 ⇒ y' = 0` (upper barrier
sharp). -/
theorem scalar_cubic_original_bounded :
    ∃ ySol : ℝ → ℝ, ySol 0 = 0 ∧
      (∀ t ≥ (0 : ℝ), HasDerivAt ySol (1 - (ySol t) ^ 3) t) ∧
      (∀ t ≥ (0 : ℝ), 0 ≤ ySol t ∧ ySol t ≤ 1) := by
  sorry

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
  sorry

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
