/-
  CRN-safe representative of the 23→33 QBee quadratization.

  QBee is only required to agree on its monomial manifold.  The raw
  emitted auxiliary equations contain unguarded negative monomials; the
  equal-on-manifold rewrites below factor every negative monomial through
  its own auxiliary variable, restoring CRN implementability.
-/

import Ripple.LPP.QBeeGammaDualRail23Generated
import Ripple.LPP.QBeeCertificate
import Ripple.LPP.Stages

set_option linter.style.longLine false
set_option linter.unusedSimpArgs false

namespace Ripple.LPP.QBee.Generated.GammaDualRail23

open Ripple

/-! ## The selective dual-rail front end -/

/-- Read the first nine variables as rails. The positive `v,r,p` coordinates
use the journal's affine `u-v+1` chart; the five guarded coordinates are kept
single-railed in the order `gam,e,e₁,eₙ,ginv`. -/
noncomputable def dualRailDecode (x : Fin 23 → ℝ) : Fin 14 → ℝ :=
  ![x 0 - x 1, x 2 - x 3, x 4 - x 5, x 6 - x 7,
    x 8 - x 9 + 1, x 10 - x 11 + 1, x 12 - x 13 + 1,
    x 14 - x 15, x 19, x 16 - x 17, x 20, x 21, x 22, x 18]

/-- Linear part of `dualRailDecode`, used on tangent vectors. -/
noncomputable def dualRailTangent (v : Fin 23 → ℝ) : Fin 14 → ℝ :=
  ![v 0 - v 1, v 2 - v 3, v 4 - v 5, v 6 - v 7,
    v 8 - v 9, v 10 - v 11, v 12 - v 13, v 14 - v 15,
    v 19, v 16 - v 17, v 20, v 21, v 22, v 18]

/-- The actual selective field has the required dual-rail difference
semantics. The common `-68*u*v` annihilation terms cancel pairwise. -/
theorem dualRailTangent_origField (x : Fin 23 → ℝ) :
    dualRailTangent (origField x) = QBee.gammaField (dualRailDecode x) := by
  funext i
  fin_cases i <;> simp [dualRailDecode, dualRailTangent, origField, QBee.gammaField,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] <;> ring

noncomputable def origProd (i : Fin 23) (x : Fin 23 → ℝ) : ℝ :=
  ![x 4,
    x 5,
    x 8 * x 12 * x 14 + x 8 * x 14 + x 8 * x 13 * x 15 +
      x 12 * x 14 + x 12 * x 9 * x 15 + x 14 * x 9 * x 13 +
      x 14 + x 9 * x 15 + x 13 * x 15,
    x 8 * x 12 * x 15 + x 8 * x 14 * x 13 + x 8 * x 15 +
      x 12 * x 14 * x 9 + x 12 * x 15 + x 14 * x 9 +
      x 14 * x 13 + x 9 * x 13 * x 15 + x 15,
    x 6 + x 8 + x 5 + 1,
    x 4 + x 7 + x 9,
    x 8 * x 10 + x 8 + x 10 + x 7 + x 9 * x 11 + 1,
    x 6 + x 8 * x 11 + x 10 * x 9 + x 9 + x 11,
    x 9,
    x 8 + 1,
    2 * x 11,
    x 10 ^ 2 + 2 * x 10 + x 11 ^ 2 + 1,
    x 8 * x 12 + x 8 + x 12 + x 9 * x 13 + 1,
    x 8 * x 13 + x 12 * x 9 + x 9 + x 13,
    x 8 + x 15 + 1,
    x 14 + x 9,
    x 16 * x 19 + x 17 + 1,
    x 16 + x 17 * x 19 + x 19,
    1,
    1,
    x 16 * x 20 + 1,
    1,
    x 0 * x 21 * x 22 + x 3 * x 21 * x 22 + 1] i

noncomputable def origDegr (i : Fin 23) (x : Fin 23 → ℝ) : ℝ :=
  ![68 * x 1, 68 * x 0, 68 * x 3, 68 * x 2, 68 * x 5,
    68 * x 4, 68 * x 7, 68 * x 6, 68 * x 9, 68 * x 8,
    66 * x 11, 68 * x 10, 68 * x 13, 68 * x 12, 68 * x 15,
    68 * x 14, 68 * x 17, 68 * x 16, x 22, 1, x 17 + 1,
    x 20, x 2 * x 21 + x 1 * x 21 + 1] i

/-- CRN implementability is established before QBee, in the senior-author
order. The first nine coordinates are the dual rails; the remaining five
negative terms retain their original variable as a guard. -/
noncomputable def origField_crn : IsCRNImplementable 23 origField where
  prod := origProd
  degr := origDegr
  prod_pos := by
    intro i x hx
    have hx0 := hx 0; have hx1 := hx 1; have hx2 := hx 2
    have hx3 := hx 3; have hx4 := hx 4; have hx5 := hx 5
    have hx6 := hx 6; have hx7 := hx 7; have hx8 := hx 8
    have hx9 := hx 9; have hx10 := hx 10; have hx11 := hx 11
    have hx12 := hx 12; have hx13 := hx 13; have hx14 := hx 14
    have hx15 := hx 15; have hx16 := hx 16; have hx17 := hx 17
    have hx18 := hx 18; have hx19 := hx 19; have hx20 := hx 20
    have hx21 := hx 21; have hx22 := hx 22
    fin_cases i <;> simp [origProd, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons] <;> positivity
  degr_pos := by
    intro i x hx
    have hx0 := hx 0; have hx1 := hx 1; have hx2 := hx 2
    have hx3 := hx 3; have hx4 := hx 4; have hx5 := hx 5
    have hx6 := hx 6; have hx7 := hx 7; have hx8 := hx 8
    have hx9 := hx 9; have hx10 := hx 10; have hx11 := hx 11
    have hx12 := hx 12; have hx13 := hx 13; have hx14 := hx 14
    have hx15 := hx 15; have hx16 := hx 16; have hx17 := hx 17
    have hx18 := hx 18; have hx19 := hx 19; have hx20 := hx 20
    have hx21 := hx 21; have hx22 := hx 22
    fin_cases i <;> simp [origDegr, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons] <;> positivity
  field_eq := by
    intro x i
    fin_cases i <;> simp [origField, origProd, origDegr,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] <;> ring

/-- Pointwise derivative form of selective dual-rail projection. -/
theorem origField_solution_projects_at {x : ℝ → Fin 23 → ℝ} {t : ℝ}
    (hx : HasDerivAt x (origField (x t)) t) :
    HasDerivAt (fun s ↦ dualRailDecode (x s))
      (QBee.gammaField (dualRailDecode (x t))) t := by
  rw [← dualRailTangent_origField]
  have hcomp : ∀ i : Fin 23,
      HasDerivAt (fun s ↦ x s i) (origField (x t) i) t :=
    hasDerivAt_pi.mp hx
  refine hasDerivAt_pi.mpr (fun i ↦ ?_)
  fin_cases i
  · simpa [dualRailDecode, dualRailTangent] using (hcomp 0).sub (hcomp 1)
  · simpa [dualRailDecode, dualRailTangent] using (hcomp 2).sub (hcomp 3)
  · simpa [dualRailDecode, dualRailTangent] using (hcomp 4).sub (hcomp 5)
  · simpa [dualRailDecode, dualRailTangent] using (hcomp 6).sub (hcomp 7)
  · simpa [dualRailDecode, dualRailTangent] using
      ((hcomp 8).sub (hcomp 9)).add_const 1
  · simpa [dualRailDecode, dualRailTangent] using
      ((hcomp 10).sub (hcomp 11)).add_const 1
  · simpa [dualRailDecode, dualRailTangent] using
      ((hcomp 12).sub (hcomp 13)).add_const 1
  · simpa [dualRailDecode, dualRailTangent] using (hcomp 14).sub (hcomp 15)
  · simpa [dualRailDecode, dualRailTangent] using hcomp 19
  · simpa [dualRailDecode, dualRailTangent] using (hcomp 16).sub (hcomp 17)
  · simpa [dualRailDecode, dualRailTangent] using hcomp 20
  · simpa [dualRailDecode, dualRailTangent] using hcomp 21
  · simpa [dualRailDecode, dualRailTangent] using hcomp 22
  · simpa [dualRailDecode, dualRailTangent] using hcomp 18

/-- Every solution of the selective CRN projects to a solution of the
original 14-coordinate gamma field. -/
theorem origField_solution_projects {x : ℝ → Fin 23 → ℝ}
    (hx : ∀ t : ℝ, 0 ≤ t → HasDerivAt x (origField (x t)) t) :
    ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (fun s ↦ dualRailDecode (x s))
        (QBee.gammaField (dualRailDecode (x t))) t := by
  intro t ht
  exact origField_solution_projects_at (hx t ht)

noncomputable def crnQuadField (y : Fin 33 → ℝ) : Fin 33 → ℝ :=
  ![(((-68) * y 0 * y 1) + y 4), (((-68) * y 0 * y 1) + y 5), (((-68) * y 2 * y 3) + (y 8 * y 14) + (y 8 * y 23) + (y 8 * y 26) + y 14 + (y 9 * y 15) + (y 9 * y 24) + (y 9 * y 25) + y 23 + y 26), (((-68) * y 2 * y 3) + (y 8 * y 15) + (y 8 * y 24) + (y 8 * y 25) + (y 14 * y 9) + (y 9 * y 23) + (y 9 * y 26) + y 15 + y 24 + y 25), (((-68) * y 4 * y 5) + y 6 + y 8 + y 5 + 1), (((-68) * y 4 * y 5) + y 4 + y 7 + y 9), (((-68) * y 6 * y 7) + (y 8 * y 10) + y 8 + y 10 + y 7 + (y 9 * y 11) + 1), (((-68) * y 6 * y 7) + y 6 + (y 8 * y 11) + (y 10 * y 9) + y 9 + y 11), (((-68) * y 8 * y 9) + y 9), (((-68) * y 8 * y 9) + y 8 + 1), (((-66) * y 10 * y 11) + (2 * y 11)), ((y 10 ^ 2) + ((-68) * y 10 * y 11) + (2 * y 10) + (y 11 ^ 2) + 1), ((y 8 * y 12) + y 8 + ((-68) * y 12 * y 13) + y 12 + (y 9 * y 13) + 1), ((y 8 * y 13) + (y 12 * y 9) + ((-68) * y 12 * y 13) + y 9 + y 13), (y 8 + ((-68) * y 14 * y 15) + y 15 + 1), (((-68) * y 14 * y 15) + y 14 + y 9), (((-68) * y 16 * y 17) + (y 16 * y 19) + y 17 + 1), (((-68) * y 16 * y 17) + y 16 + (y 17 * y 19) + y 19), (-(y 18 * y 22) + 1), (1 + -(y 19)), ((y 16 * y 20) + -(y 17 * y 20) + -(y 20) + 1), (-(y 20 * y 21) + 1), ((y 27 * y 22) + -(y 30 * y 22) + -(y 31 * y 22) + (y 32 * y 22) + -(y 22) + 1), ((y 8 * y 23) + ((-68) * y 12 * y 23) + ((-68) * y 14 * y 23) + (y 9 * y 13) + (y 9 * y 15) + (y 9 * y 25) + y 23 + y 24), ((y 8 * y 13) + (y 8 * y 24) + ((-68) * y 12 * y 24) + (y 14 * y 9) + (y 9 * y 26) + y 13 + ((-68) * y 15 * y 24) + y 23 + y 24), ((y 8 * y 15) + (y 8 * y 25) + (y 12 * y 9) + ((-68) * y 14 * y 25) + (y 9 * y 23) + ((-68) * y 13 * y 25) + y 15 + y 25 + y 26), ((y 8 * y 12) + (y 8 * y 14) + (y 8 * y 26) + y 12 + y 14 + (y 9 * y 24) + ((-68) * y 13 * y 26) + ((-68) * y 15 * y 26) + y 25 + y 26), (((-68) * y 2 * y 27) + (y 14 * y 28) + y 3 + (y 15 * y 29) + (y 15 * y 21) + (y 23 * y 28) + (y 24 * y 29) + (y 24 * y 21) + (y 25 * y 29) + (y 25 * y 21) + (y 26 * y 28) + -(y 27 * y 20)), (((-68) * y 8 * y 28) + y 9 + -(y 28 * y 20) + y 29 + y 21), (y 8 + ((-68) * y 9 * y 29) + y 28 + -(y 29 * y 20)), (y 2 + (y 14 * y 29) + (y 14 * y 21) + ((-68) * y 3 * y 30) + (y 15 * y 28) + (y 23 * y 29) + (y 23 * y 21) + (y 24 * y 28) + (y 25 * y 28) + (y 26 * y 29) + (y 26 * y 21) + -(y 30 * y 20)), (((-68) * y 0 * y 31) + y 1 + (y 5 * y 21) + -(y 31 * y 20)), (y 0 + (y 4 * y 21) + ((-68) * y 1 * y 32) + -(y 32 * y 20))]

noncomputable def crnProd (i : Fin 33) (y : Fin 33 → ℝ) : ℝ :=
  (![y 4, y 5, ((y 8 * y 14) + (y 8 * y 23) + (y 8 * y 26) + y 14 + (y 9 * y 15) + (y 9 * y 24) + (y 9 * y 25) + y 23 + y 26), ((y 8 * y 15) + (y 8 * y 24) + (y 8 * y 25) + (y 14 * y 9) + (y 9 * y 23) + (y 9 * y 26) + y 15 + y 24 + y 25), (y 6 + y 8 + y 5 + 1), (y 4 + y 7 + y 9), ((y 8 * y 10) + y 8 + y 10 + y 7 + (y 9 * y 11) + 1), (y 6 + (y 8 * y 11) + (y 10 * y 9) + y 9 + y 11), y 9, (y 8 + 1), (2 * y 11), ((y 10 ^ 2) + (2 * y 10) + (y 11 ^ 2) + 1), ((y 8 * y 12) + y 8 + y 12 + (y 9 * y 13) + 1), ((y 8 * y 13) + (y 12 * y 9) + y 9 + y 13), (y 8 + y 15 + 1), (y 14 + y 9), ((y 16 * y 19) + y 17 + 1), (y 16 + (y 17 * y 19) + y 19), 1, 1, ((y 16 * y 20) + 1), 1, ((y 27 * y 22) + (y 32 * y 22) + 1), ((y 8 * y 23) + (y 9 * y 13) + (y 9 * y 15) + (y 9 * y 25) + y 23 + y 24), ((y 8 * y 13) + (y 8 * y 24) + (y 14 * y 9) + (y 9 * y 26) + y 13 + y 23 + y 24), ((y 8 * y 15) + (y 8 * y 25) + (y 12 * y 9) + (y 9 * y 23) + y 15 + y 25 + y 26), ((y 8 * y 12) + (y 8 * y 14) + (y 8 * y 26) + y 12 + y 14 + (y 9 * y 24) + y 25 + y 26), ((y 14 * y 28) + y 3 + (y 15 * y 29) + (y 15 * y 21) + (y 23 * y 28) + (y 24 * y 29) + (y 24 * y 21) + (y 25 * y 29) + (y 25 * y 21) + (y 26 * y 28)), (y 9 + y 29 + y 21), (y 8 + y 28), (y 2 + (y 14 * y 29) + (y 14 * y 21) + (y 15 * y 28) + (y 23 * y 29) + (y 23 * y 21) + (y 24 * y 28) + (y 25 * y 28) + (y 26 * y 29) + (y 26 * y 21)), (y 1 + (y 5 * y 21)), (y 0 + (y 4 * y 21))]) i

noncomputable def crnDegr (i : Fin 33) (y : Fin 33 → ℝ) : ℝ :=
  (![(68 * y 1), (68 * y 0), (68 * y 3), (68 * y 2), (68 * y 5), (68 * y 4), (68 * y 7), (68 * y 6), (68 * y 9), (68 * y 8), (66 * y 11), (68 * y 10), (68 * y 13), (68 * y 12), (68 * y 15), (68 * y 14), (68 * y 17), (68 * y 16), y 22, 1, (y 17 + 1), y 20, (y 30 + y 31 + 1), ((68 * y 12) + (68 * y 14)), ((68 * y 12) + (68 * y 15)), ((68 * y 14) + (68 * y 13)), ((68 * y 13) + (68 * y 15)), ((68 * y 2) + y 20), ((68 * y 8) + y 20), ((68 * y 9) + y 20), ((68 * y 3) + y 20), ((68 * y 0) + y 20), ((68 * y 1) + y 20)]) i

set_option maxHeartbeats 1600000 in
-- Generated 33-coordinate manifold normalization.
theorem crnQuadField_eq_quadField_on_embed (x : Fin 23 → ℝ) :
    crnQuadField (embed x) = quadField (embed x) := by
  funext i
  fin_cases i <;> simp [crnQuadField, quadField, embed,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] <;> ring

set_option maxHeartbeats 1600000 in
-- Generated positivity and field decomposition for 33 coordinates.
noncomputable def crnQuadField_crn : IsCRNImplementable 33 crnQuadField where
  prod := crnProd
  degr := crnDegr
  prod_pos := by
    intro i y hy
    have hy0 : 0 ≤ y 0 := hy 0
    have hy1 : 0 ≤ y 1 := hy 1
    have hy2 : 0 ≤ y 2 := hy 2
    have hy3 : 0 ≤ y 3 := hy 3
    have hy4 : 0 ≤ y 4 := hy 4
    have hy5 : 0 ≤ y 5 := hy 5
    have hy6 : 0 ≤ y 6 := hy 6
    have hy7 : 0 ≤ y 7 := hy 7
    have hy8 : 0 ≤ y 8 := hy 8
    have hy9 : 0 ≤ y 9 := hy 9
    have hy10 : 0 ≤ y 10 := hy 10
    have hy11 : 0 ≤ y 11 := hy 11
    have hy12 : 0 ≤ y 12 := hy 12
    have hy13 : 0 ≤ y 13 := hy 13
    have hy14 : 0 ≤ y 14 := hy 14
    have hy15 : 0 ≤ y 15 := hy 15
    have hy16 : 0 ≤ y 16 := hy 16
    have hy17 : 0 ≤ y 17 := hy 17
    have hy18 : 0 ≤ y 18 := hy 18
    have hy19 : 0 ≤ y 19 := hy 19
    have hy20 : 0 ≤ y 20 := hy 20
    have hy21 : 0 ≤ y 21 := hy 21
    have hy22 : 0 ≤ y 22 := hy 22
    have hy23 : 0 ≤ y 23 := hy 23
    have hy24 : 0 ≤ y 24 := hy 24
    have hy25 : 0 ≤ y 25 := hy 25
    have hy26 : 0 ≤ y 26 := hy 26
    have hy27 : 0 ≤ y 27 := hy 27
    have hy28 : 0 ≤ y 28 := hy 28
    have hy29 : 0 ≤ y 29 := hy 29
    have hy30 : 0 ≤ y 30 := hy 30
    have hy31 : 0 ≤ y 31 := hy 31
    have hy32 : 0 ≤ y 32 := hy 32
    fin_cases i <;> simp [crnProd, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons] <;> positivity
  degr_pos := by
    intro i y hy
    have hy0 : 0 ≤ y 0 := hy 0
    have hy1 : 0 ≤ y 1 := hy 1
    have hy2 : 0 ≤ y 2 := hy 2
    have hy3 : 0 ≤ y 3 := hy 3
    have hy4 : 0 ≤ y 4 := hy 4
    have hy5 : 0 ≤ y 5 := hy 5
    have hy6 : 0 ≤ y 6 := hy 6
    have hy7 : 0 ≤ y 7 := hy 7
    have hy8 : 0 ≤ y 8 := hy 8
    have hy9 : 0 ≤ y 9 := hy 9
    have hy10 : 0 ≤ y 10 := hy 10
    have hy11 : 0 ≤ y 11 := hy 11
    have hy12 : 0 ≤ y 12 := hy 12
    have hy13 : 0 ≤ y 13 := hy 13
    have hy14 : 0 ≤ y 14 := hy 14
    have hy15 : 0 ≤ y 15 := hy 15
    have hy16 : 0 ≤ y 16 := hy 16
    have hy17 : 0 ≤ y 17 := hy 17
    have hy18 : 0 ≤ y 18 := hy 18
    have hy19 : 0 ≤ y 19 := hy 19
    have hy20 : 0 ≤ y 20 := hy 20
    have hy21 : 0 ≤ y 21 := hy 21
    have hy22 : 0 ≤ y 22 := hy 22
    have hy23 : 0 ≤ y 23 := hy 23
    have hy24 : 0 ≤ y 24 := hy 24
    have hy25 : 0 ≤ y 25 := hy 25
    have hy26 : 0 ≤ y 26 := hy 26
    have hy27 : 0 ≤ y 27 := hy 27
    have hy28 : 0 ≤ y 28 := hy 28
    have hy29 : 0 ≤ y 29 := hy 29
    have hy30 : 0 ≤ y 30 := hy 30
    have hy31 : 0 ≤ y 31 := hy 31
    have hy32 : 0 ≤ y 32 := hy 32
    fin_cases i <;> simp [crnDegr, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons] <;> positivity
  field_eq := by
    intro y i
    fin_cases i <;> simp [crnQuadField, crnProd, crnDegr,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] <;> ring

set_option maxHeartbeats 3200000 in
/-- The CRN-safe representative retains the QBee solution lift. The seven
guarded rewrites only change the field away from the monomial manifold. -/
theorem crnQBee_solution_lift {x : ℝ → Fin 23 → ℝ}
    (hx : ∀ t : ℝ, 0 ≤ t → HasDerivAt x (origField (x t)) t) :
    ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (fun s => embed (x s)) (crnQuadField (embed (x t))) t := by
  intro t ht
  have hx_t := hx t ht
  have hcomp : ∀ i : Fin 23,
      HasDerivAt (fun s => x s i) (origField (x t) i) t :=
    fun i => hasDerivAt_pi.mp hx_t i
  let F := origField (x t)
  have h23 := (hcomp 13).mul (hcomp 15)
  have h24 := (hcomp 14).mul (hcomp 13)
  have h25 := (hcomp 12).mul (hcomp 15)
  have h26 := (hcomp 12).mul (hcomp 14)
  have h27 := (hcomp 3).mul (hcomp 21)
  have h28 := (hcomp 9).mul (hcomp 21)
  have h29 := (hcomp 8).mul (hcomp 21)
  have h30 := (hcomp 2).mul (hcomp 21)
  have h31 := (hcomp 1).mul (hcomp 21)
  have h32 := (hcomp 0).mul (hcomp 21)
  let deriv : Fin 33 → ℝ :=
    ![F 0, F 1, F 2, F 3, F 4, F 5, F 6, F 7, F 8, F 9, F 10,
      F 11, F 12, F 13, F 14, F 15, F 16, F 17, F 18, F 19, F 20,
      F 21, F 22,
      F 13 * x t 15 + x t 13 * F 15,
      F 14 * x t 13 + x t 14 * F 13,
      F 12 * x t 15 + x t 12 * F 15,
      F 12 * x t 14 + x t 12 * F 14,
      F 3 * x t 21 + x t 3 * F 21,
      F 9 * x t 21 + x t 9 * F 21,
      F 8 * x t 21 + x t 8 * F 21,
      F 2 * x t 21 + x t 2 * F 21,
      F 1 * x t 21 + x t 1 * F 21,
      F 0 * x t 21 + x t 0 * F 21]
  have hderiv : HasDerivAt (fun s => embed (x s)) deriv t := by
    rw [show (fun s => embed (x s)) = (fun s =>
      ![x s 0, x s 1, x s 2, x s 3, x s 4, x s 5, x s 6, x s 7,
        x s 8, x s 9, x s 10, x s 11, x s 12, x s 13, x s 14, x s 15,
        x s 16, x s 17, x s 18, x s 19, x s 20, x s 21, x s 22,
        x s 13 * x s 15, x s 14 * x s 13, x s 12 * x s 15,
        x s 12 * x s 14, x s 3 * x s 21, x s 9 * x s 21,
        x s 8 * x s 21, x s 2 * x s 21, x s 1 * x s 21,
        x s 0 * x s 21]) from by ext s i; fin_cases i <;> simp [embed]]
    exact hasDerivAt_pi.mpr (fun i => by
      fin_cases i <;> simp [deriv, F, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons] <;>
      first
        | exact hcomp _
        | exact h23
        | exact h24
        | exact h25
        | exact h26
        | exact h27
        | exact h28
        | exact h29
        | exact h30
        | exact h31
        | exact h32)
  convert hderiv using 1
  ext i
  fin_cases i <;> simp [deriv, F, crnQuadField, origField, embed,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] <;> ring

#print axioms crnQuadField_eq_quadField_on_embed
#print axioms dualRailTangent_origField
#print axioms origField_crn
#print axioms origField_solution_projects_at
#print axioms origField_solution_projects
#print axioms crnQuadField_crn
#print axioms crnQBee_solution_lift

end Ripple.LPP.QBee.Generated.GammaDualRail23
