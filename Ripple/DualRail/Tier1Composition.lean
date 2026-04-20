/-
  Ripple.DualRail.Tier1Composition — Tier 1 composition theorem.

  Composes the DNA25 polynomial-scale dual-rail construction with the DNA25
  Lemma 8 two-stage subtraction gadget, turning a plain `BoundedTimeComputable`
  (with polynomial field and zero initial conditions) for `α ∈ [0, 1]` into a
  `CertifiedBoundedTimeComputable + PolyCRNDecomposition` witness for the same
  `α`.

  Endpoint cases `α = 0` and `α = 1` are handled via constant-trajectory
  witnesses; the interior `0 < α < 1` case routes through
  `polynomialScaleDualRail_bounded_converges` (dual-rail) composed with
  `subtraction_lemma8_analytic` at `β = 0` (Lemma 8), producing a CBTC+PCD for
  `α − 0 = α`.
-/

import Ripple.DualRail.DNA25Bounded
import Ripple.DualRail.ConstantAnnihilation
import Ripple.DualRail.SubtractionGadget
import Ripple.LPP.AlgebraicConstruction

set_option linter.style.show false

namespace Ripple
namespace DualRail

open MvPolynomial

/-! ## Endpoint construction: trivial `α = 1` CBTC + PCD

A 1-species PIVP with `init = 1` and `field = 0` has constant-one trajectory,
which converges to 1.  Its PCD is the trivial `prod = 0, degr = 0` (so
`field = 0 = 0 − 0 · X`), with `init_nonneg` holding since `1 ≥ 0`. -/

/-- The 1-species constant-one PolyPIVP: `x' = 0`, `x(0) = 1`. -/
noncomputable def trivialOnePolyPIVP : PolyPIVP 1 where
  field := fun _ => 0
  init := fun _ => 1
  output := 0

/-- The constant-one solution to `trivialOnePolyPIVP`. -/
noncomputable def trivialOneSolution :
    PIVP.Solution trivialOnePolyPIVP.toPIVP where
  trajectory := fun _ _ => 1
  init_cond := by
    funext i
    show (1 : ℝ) = ((trivialOnePolyPIVP.init i : ℚ) : ℝ)
    simp [trivialOnePolyPIVP]
  is_solution := by
    intro t _
    have hfield : trivialOnePolyPIVP.toPIVP.field (fun _ : Fin 1 => (1 : ℝ)) =
        (fun _ : Fin 1 => (0 : ℝ)) := by
      funext i
      change (trivialOnePolyPIVP.field i).eval₂ (Rat.castHom ℝ)
          (fun _ : Fin 1 => (1 : ℝ)) = 0
      simp [trivialOnePolyPIVP]
    rw [hfield]
    exact hasDerivAt_const t (fun _ : Fin 1 => (1 : ℝ))

/-- `CertifiedBoundedTimeComputable 1 1` via the constant-one trivial PIVP. -/
noncomputable def trivialOneCBTC : CertifiedBoundedTimeComputable 1 (1 : ℝ) where
  pivp := trivialOnePolyPIVP
  sol := trivialOneSolution
  modulus := fun _ => 0
  bounded := ⟨2, by norm_num, fun t _ => by
    show ‖(fun _ : Fin 1 => (1 : ℝ))‖ ≤ 2
    simp [Pi.norm_def]⟩
  trajectory_continuous := by
    show Continuous (fun _ : ℝ => (fun _ : Fin 1 => (1 : ℝ)))
    exact continuous_const
  convergence := by
    intro r t _
    show |(1 : ℝ) - 1| < Real.exp (-(r : ℝ))
    simp [Real.exp_pos]

/-- `PolyCRNDecomposition` for the trivial one PIVP:
all production/degradation polys are zero; `init_nonneg` holds since `init = 1 ≥ 0`. -/
noncomputable def trivialOnePCD :
    PolyCRNDecomposition 1 trivialOneCBTC.pivp where
  prod := fun _ => 0
  degr := fun _ => 0
  prod_nonneg := fun _ _ => by simp
  degr_nonneg := fun _ _ => by simp
  init_nonneg := fun _ => by
    show (0 : ℚ) ≤ trivialOneCBTC.pivp.init _
    simp [trivialOneCBTC, trivialOnePolyPIVP]
  field_eq := fun i => by
    show trivialOneCBTC.pivp.field i = (0 : MvPolynomial (Fin 1) ℚ)
      - (0 : MvPolynomial (Fin 1) ℚ) * MvPolynomial.X i
    simp [trivialOneCBTC, trivialOnePolyPIVP]

/-! ## Interior composition: 0 < α < 1

For `α` strictly interior, compose the polynomial-scale dual-rail of `btc`
(producing a bounded, continuous, non-negative `2·d`-dimensional PIVP whose
`(u_out, v_out)` difference converges to `α`) with the Lemma 8 subtraction
gadget at `β = 0`.  The two input PIVPs `Px, Py` fed to the subtraction
gadget are both copies of `polynomialScaleDualRail d p`, with distinct
output indices (`u_out = 2·btc.output` and `v_out = 2·btc.output+1`).  Using
the *same* solution `solDR` for both `solX` and `solY` — legal since `Px`
and `Py` share `field` and `init` — the Lemma 8 Stage A driver
`x(t) − y(t) = u_out(t) − v_out(t)` converges to `α − 0 = α`. -/

/-- Rebuild a PCD of `polynomialScaleDualRail d p` on top of a record-updated
copy that differs only in `output`.  Since `PolyCRNDecomposition` depends on
`P.field`, `P.init` (but not `P.output`), the fields of the original PCD
remain valid. -/
noncomputable def polynomialScaleDualRail_pcd_output
    {d : ℕ} [NeZero d] (p : Fin d → MvPolynomial (Fin d) ℚ)
    (out : Fin (2 * d)) :
    PolyCRNDecomposition (2 * d)
      { polynomialScaleDualRail d p with output := out } :=
  let base := polynomialScaleDualRail_pcd d p
  { prod := base.prod
    degr := base.degr
    prod_nonneg := base.prod_nonneg
    degr_nonneg := base.degr_nonneg
    init_nonneg := base.init_nonneg
    field_eq := base.field_eq }

/-- **Tier 1 composition (DNA25 annihilation + Lemma 8), α ∈ [0, 1] case split.**

From a polynomial BTC for `α ∈ [0, 1]` with zero initial conditions and
polynomial field hypothesis, build a CertifiedBoundedTimeComputable +
PolyCRNDecomposition for the same `α`.

The proof:
* `α = 0`: use `trivialZeroCBTC` + `trivialZeroPCD`.
* `α = 1`: use `trivialOneCBTC` + `trivialOnePCD`.
* `0 < α < 1`: apply `polynomialScaleDualRail_bounded_converges btc p h_field
  h_zero`, package the result as the joint-difference convergence needed by
  `subtraction_lemma8_analytic` at `β = 0`, and assemble a CBTC+PCD for
  `α − 0 = α` using the `subtractionPIVP / subtractionPCD` of two copies of
  the dual-rail PIVP with distinct output indices `(2·btc.output, 2·btc.output+1)`. -/
theorem btc_to_cbtc_pcd_of_unit_interval {d : ℕ} [NeZero d] {α : ℝ}
    (btc : BoundedTimeComputable d α)
    (p : Fin d → MvPolynomial (Fin d) ℚ)
    (h_field : ∀ y : Fin d → ℝ, ∀ i : Fin d,
        btc.pivp.field y i = (p i).eval₂ (Rat.castHom ℝ) y)
    (h_zero : ∀ j, btc.pivp.init j = 0)
    (hα_lo : 0 ≤ α) (hα_hi : α ≤ 1) :
    ∃ (d' : ℕ) (cbtc' : CertifiedBoundedTimeComputable d' α)
      (_ : PolyCRNDecomposition d' cbtc'.pivp), True := by
  -- Split on the three cases α = 0, α = 1, 0 < α < 1.
  rcases eq_or_lt_of_le hα_lo with hα0 | hα_pos
  · -- α = 0: trivial.
    have hα_eq : α = 0 := hα0.symm
    subst hα_eq
    exact ⟨1, Ripple.Algebraic.trivialZeroCBTC, Ripple.Algebraic.trivialZeroPCD,
      trivial⟩
  · rcases eq_or_lt_of_le hα_hi with hα1 | hα_lt_one
    · -- α = 1: trivial.
      subst hα1
      exact ⟨1, trivialOneCBTC, trivialOnePCD, trivial⟩
    · -- 0 < α < 1: the main composition path.
      -- 1. Invoke the dual-rail converger.
      obtain ⟨solDR, B, hB_pos, h_nonneg, h_bnd, _h_id, h_cont, h_conv⟩ :=
        polynomialScaleDualRail_bounded_converges btc p h_field h_zero
      -- 2. Define the two PolyPIVP copies with distinct output indices.
      let uOut : Fin (2 * d) := ⟨2 * btc.pivp.output.val, by
        have := btc.pivp.output.isLt; omega⟩
      let vOut : Fin (2 * d) := ⟨2 * btc.pivp.output.val + 1, by
        have := btc.pivp.output.isLt; omega⟩
      let Px : PolyPIVP (2 * d) :=
        { polynomialScaleDualRail d p with output := uOut }
      let Py : PolyPIVP (2 * d) :=
        { polynomialScaleDualRail d p with output := vOut }
      -- 3. The solDR is a solution of both Px.toPIVP and Py.toPIVP since
      --    toPIVP.field/init only depend on .field/.init.  Rebuild the
      --    `PIVP.Solution` structures so the types align.
      let solX : PIVP.Solution Px.toPIVP :=
        { trajectory := solDR.trajectory
          init_cond := solDR.init_cond
          is_solution := solDR.is_solution }
      let solY : PIVP.Solution Py.toPIVP :=
        { trajectory := solDR.trajectory
          init_cond := solDR.init_cond
          is_solution := solDR.is_solution }
      -- 4. Boundedness (pi-norm) of solDR on [0,∞).
      have hXbd : Px.toPIVP.IsBounded solX.trajectory := by
        refine ⟨B, hB_pos, ?_⟩
        intro t ht
        rw [pi_norm_le_iff_of_nonneg hB_pos.le]
        intro k
        rw [Real.norm_eq_abs]
        have h1 := h_nonneg t ht k
        have h2 := h_bnd t ht k
        rw [abs_of_nonneg h1]
        exact h2
      have hYbd : Py.toPIVP.IsBounded solY.trajectory := hXbd
      -- 5. Continuity of solDR.
      have hXcont : Continuous solX.trajectory := h_cont
      have hYcont : Continuous solY.trajectory := h_cont
      -- 6. Build the diffMod and its convergence.
      let diffMod : TimeModulus := btc.modulus
      have h_diff_conv : ∀ r : ℕ, ∀ t : ℝ, 0 ≤ t → t > diffMod r →
          |solX.trajectory t Px.output - solY.trajectory t Py.output - (α - 0)|
          < Real.exp (-(r : ℝ)) := by
        intro r t ht_nn ht_gt
        -- `solX.trajectory = solY.trajectory = solDR.trajectory`.
        -- Px.output = uOut = ⟨2·btc.output, _⟩, Py.output = vOut.
        show |solDR.trajectory t Px.output - solDR.trajectory t Py.output
              - (α - 0)| < Real.exp (-(r : ℝ))
        have hrw :
            solDR.trajectory t Px.output - solDR.trajectory t Py.output - (α - 0)
              = solDR.trajectory t ⟨2 * btc.pivp.output.val, by
                  have := btc.pivp.output.isLt; omega⟩
                - solDR.trajectory t ⟨2 * btc.pivp.output.val + 1, by
                    have := btc.pivp.output.isLt; omega⟩
                - α := by
          show solDR.trajectory t uOut - solDR.trajectory t vOut - (α - 0) = _
          ring
        rw [hrw]
        exact h_conv r t ht_nn ht_gt
      -- 7. Apply subtraction_lemma8_analytic with β = 0.
      have hβ_lo : (0 : ℝ) ≤ 0 := le_refl _
      have hβ_hi : (0 : ℝ) < 1 := by norm_num
      have hαβ : (0 : ℝ) < α := hα_pos
      obtain ⟨sol', mod', hbd', hconv', hcont'⟩ :=
        subtraction_lemma8_analytic Px Py solX solY
          hXbd hYbd hXcont hYcont
          diffMod h_diff_conv
          hα_pos hα_lt_one hβ_lo hβ_hi hαβ
      -- 8. Build the PCDs for Px, Py and combine via subtractionPCD.
      let pcdX : PolyCRNDecomposition (2 * d) Px :=
        polynomialScaleDualRail_pcd_output p uOut
      let pcdY : PolyCRNDecomposition (2 * d) Py :=
        polynomialScaleDualRail_pcd_output p vOut
      let pcd' : PolyCRNDecomposition ((2*d + 2*d) + 1 + 1)
          (subtractionPIVP Px Py) :=
        subtractionPCD pcdX pcdY
      -- 9. Assemble the CBTC.  Convergence: `hconv'` yields
      --    `|sol'.traj t (idxZ) - (α - 0)| < exp(-r)` past `mod' r`.
      --    Need `|sol'.traj t output - α| < exp(-r)`.  By
      --    `subtractionPIVP_output`, `output = idxZ`, and `α - 0 = α`.
      refine ⟨(2*d + 2*d) + 1 + 1,
        { pivp := subtractionPIVP Px Py
          sol := sol'
          modulus := mod'
          bounded := hbd'
          trajectory_continuous := hcont'
          convergence := by
            intro r t ht
            show |sol'.trajectory t (subtractionPIVP Px Py).output - α|
              < Real.exp (-(r : ℝ))
            rw [subtractionPIVP_output]
            have hαrw : α = α - 0 := by ring
            rw [hαrw]
            exact hconv' r t ht },
        pcd', trivial⟩

end DualRail
end Ripple
