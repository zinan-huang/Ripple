/-
  Auto-generated QBee certificate for `gamma14`.
  Original variables: 14; new QBee variables: 4; total: 18.

  New variables:
    14: w{0} = p*v
    15: w{1} = e_n*g
    16: w{2} = e_n*f
    17: w{3} = e_n*p*v
-/

import Ripple.LPP.QBeeGeneric

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.style.longLine false

namespace Ripple.LPP.QBee.Generated
namespace Gamma14

noncomputable def origField (x : Fin 14 → ℝ) : Fin 14 → ℝ :=
  ![x 2, (x 6 * x 7 * x 4), (x 3 + x 4 + -(x 2)), ((x 5 * x 4) + -(x 3)), -(x 4), -((x 5 ^ 2)), (x 6 * x 4), (-(x 7) + x 4), (1 + -(x 8)), ((x 9 * x 8) + -(x 9) + -(x 8) + 1), ((x 9 * x 10) + -(x 10) + 1), (-(x 10 * x 11) + 1), ((x 11 * x 0 * x 12) + -(x 11 * x 1 * x 12) + -(x 12) + 1), (-(x 13 * x 12) + 1)]

noncomputable def quadField (y : Fin 18 → ℝ) : Fin 18 → ℝ :=
  ![y 2, (y 7 * y 14), (y 3 + y 4 + -(y 2)), ((y 5 * y 4) + -(y 3)), -(y 4), -((y 5 ^ 2)), y 14, (-(y 7) + y 4), (1 + -(y 8)), ((y 9 * y 8) + -(y 9) + -(y 8) + 1), ((y 9 * y 10) + -(y 10) + 1), (-(y 10 * y 11) + 1), (-(y 12 * y 15) + (y 12 * y 16) + -(y 12) + 1), (-(y 13 * y 12) + 1), ((y 4 * y 14) + -(y 14)), (-(y 10 * y 15) + y 1 + (y 7 * y 17)), (-(y 10 * y 16) + (y 11 * y 2) + y 0), (-(y 10 * y 17) + (y 4 * y 17) + y 14 + -(y 17))]

noncomputable def embed (x : Fin 14 → ℝ) : Fin 18 → ℝ :=
  ![x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, (x 6 * x 4), (x 11 * x 1), (x 11 * x 0), (x 11 * x 6 * x 4)]

noncomputable def chainRule (x : Fin 14 → ℝ) : Fin 4 → ℝ :=
  ![((x 6 * (x 4 ^ 2)) + -(x 6 * x 4)), (-(x 10 * x 11 * x 1) + (x 11 * x 6 * x 7 * x 4) + x 1), (-(x 10 * x 11 * x 0) + (x 11 * x 2) + x 0), (-(x 10 * x 11 * x 6 * x 4) + (x 11 * x 6 * (x 4 ^ 2)) + -(x 11 * x 6 * x 4) + (x 6 * x 4))]

theorem embed_orig (x : Fin 14 → ℝ) (i : Fin 14) :
    embed x (Fin.castAdd 4 i) = x i := by
  fin_cases i <;> simp [origField, quadField, embed, chainRule, Fin.castAdd, Fin.natAdd, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

theorem orig_correct (x : Fin 14 → ℝ) (i : Fin 14) :
    quadField (embed x) (Fin.castAdd 4 i) = origField x i := by
  fin_cases i <;> simp [origField, quadField, embed, chainRule, Fin.castAdd, Fin.natAdd, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] <;> ring

theorem chain_correct (x : Fin 14 → ℝ) (j : Fin 4) :
    quadField (embed x) (Fin.natAdd 14 j) = chainRule x j := by
  fin_cases j <;> simp [origField, quadField, embed, chainRule, Fin.castAdd, Fin.natAdd, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] <;> ring

noncomputable def certificate : QBeeCertificate 14 4 where
  origField := origField
  quadField := quadField
  embed := embed
  chainRule := chainRule
  embed_orig := embed_orig
  orig_correct := orig_correct
  chain_correct := chain_correct

end Gamma14
end Ripple.LPP.QBee.Generated
