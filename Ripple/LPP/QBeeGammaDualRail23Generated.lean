/-
  Auto-generated QBee certificate for `gammaDualRail23`.
  Original variables: 23; new QBee variables: 10; total: 33.

  New variables:
    23: w{0} = v_x_8*v_x_9
    24: w{1} = u_x_9*v_x_8
    25: w{2} = u_x_8*v_x_9
    26: w{3} = u_x_8*u_x_9
    27: w{4} = v_x_3*x_13
    28: w{5} = v_x_6*x_13
    29: w{6} = u_x_6*x_13
    30: w{7} = u_x_3*x_13
    31: w{8} = v_x_2*x_13
    32: w{9} = u_x_2*x_13
-/

import Ripple.LPP.QBeeGeneric

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.style.longLine false

namespace Ripple.LPP.QBee.Generated
namespace GammaDualRail23

noncomputable def origField (x : Fin 23 → ℝ) : Fin 23 → ℝ :=
  ![(((-68) * x 0 * x 1) + x 4), (((-68) * x 0 * x 1) + x 5), (((-68) * x 2 * x 3) + (x 8 * x 12 * x 14) + (x 8 * x 14) + (x 8 * x 13 * x 15) + (x 12 * x 14) + (x 12 * x 9 * x 15) + (x 14 * x 9 * x 13) + x 14 + (x 9 * x 15) + (x 13 * x 15)), (((-68) * x 2 * x 3) + (x 8 * x 12 * x 15) + (x 8 * x 14 * x 13) + (x 8 * x 15) + (x 12 * x 14 * x 9) + (x 12 * x 15) + (x 14 * x 9) + (x 14 * x 13) + (x 9 * x 13 * x 15) + x 15), (((-68) * x 4 * x 5) + x 6 + x 8 + x 5 + 1), (((-68) * x 4 * x 5) + x 4 + x 7 + x 9), (((-68) * x 6 * x 7) + (x 8 * x 10) + x 8 + x 10 + x 7 + (x 9 * x 11) + 1), (((-68) * x 6 * x 7) + x 6 + (x 8 * x 11) + (x 10 * x 9) + x 9 + x 11), (((-68) * x 8 * x 9) + x 9), (((-68) * x 8 * x 9) + x 8 + 1), (((-66) * x 10 * x 11) + (2 * x 11)), ((x 10 ^ 2) + ((-68) * x 10 * x 11) + (2 * x 10) + (x 11 ^ 2) + 1), ((x 8 * x 12) + x 8 + ((-68) * x 12 * x 13) + x 12 + (x 9 * x 13) + 1), ((x 8 * x 13) + (x 12 * x 9) + ((-68) * x 12 * x 13) + x 9 + x 13), (x 8 + ((-68) * x 14 * x 15) + x 15 + 1), (((-68) * x 14 * x 15) + x 14 + x 9), (((-68) * x 16 * x 17) + (x 16 * x 19) + x 17 + 1), (((-68) * x 16 * x 17) + x 16 + (x 17 * x 19) + x 19), (-(x 18 * x 22) + 1), (1 + -(x 19)), ((x 16 * x 20) + -(x 17 * x 20) + -(x 20) + 1), (-(x 20 * x 21) + 1), ((x 0 * x 21 * x 22) + -(x 2 * x 21 * x 22) + -(x 1 * x 21 * x 22) + (x 3 * x 21 * x 22) + -(x 22) + 1)]

noncomputable def quadField (y : Fin 33 → ℝ) : Fin 33 → ℝ :=
  ![(((-68) * y 0 * y 1) + y 4), (((-68) * y 0 * y 1) + y 5), (((-68) * y 2 * y 3) + (y 8 * y 14) + (y 8 * y 23) + (y 8 * y 26) + y 14 + (y 9 * y 15) + (y 9 * y 24) + (y 9 * y 25) + y 23 + y 26), (((-68) * y 2 * y 3) + (y 8 * y 15) + (y 8 * y 24) + (y 8 * y 25) + (y 14 * y 9) + (y 9 * y 23) + (y 9 * y 26) + y 15 + y 24 + y 25), (((-68) * y 4 * y 5) + y 6 + y 8 + y 5 + 1), (((-68) * y 4 * y 5) + y 4 + y 7 + y 9), (((-68) * y 6 * y 7) + (y 8 * y 10) + y 8 + y 10 + y 7 + (y 9 * y 11) + 1), (((-68) * y 6 * y 7) + y 6 + (y 8 * y 11) + (y 10 * y 9) + y 9 + y 11), (((-68) * y 8 * y 9) + y 9), (((-68) * y 8 * y 9) + y 8 + 1), (((-66) * y 10 * y 11) + (2 * y 11)), ((y 10 ^ 2) + ((-68) * y 10 * y 11) + (2 * y 10) + (y 11 ^ 2) + 1), ((y 8 * y 12) + y 8 + ((-68) * y 12 * y 13) + y 12 + (y 9 * y 13) + 1), ((y 8 * y 13) + (y 12 * y 9) + ((-68) * y 12 * y 13) + y 9 + y 13), (y 8 + ((-68) * y 14 * y 15) + y 15 + 1), (((-68) * y 14 * y 15) + y 14 + y 9), (((-68) * y 16 * y 17) + (y 16 * y 19) + y 17 + 1), (((-68) * y 16 * y 17) + y 16 + (y 17 * y 19) + y 19), (-(y 18 * y 22) + 1), (1 + -(y 19)), ((y 16 * y 20) + -(y 17 * y 20) + -(y 20) + 1), (-(y 20 * y 21) + 1), ((y 27 * y 22) + -(y 30 * y 22) + -(y 31 * y 22) + (y 32 * y 22) + -(y 22) + 1), ((y 8 * y 23) + (y 9 * y 13) + (y 9 * y 15) + (y 9 * y 25) + ((-68) * y 13 * y 25) + ((-68) * y 15 * y 24) + y 23 + y 24), ((y 8 * y 13) + (y 8 * y 24) + (y 14 * y 9) + (y 9 * y 26) + ((-68) * y 13 * y 26) + y 13 + ((-68) * y 15 * y 24) + y 23 + y 24), ((y 8 * y 15) + (y 8 * y 25) + (y 12 * y 9) + (y 9 * y 23) + ((-68) * y 13 * y 25) + ((-68) * y 15 * y 26) + y 15 + y 25 + y 26), ((y 8 * y 12) + (y 8 * y 14) + (y 8 * y 26) + y 12 + y 14 + (y 9 * y 24) + ((-68) * y 13 * y 26) + ((-68) * y 15 * y 26) + y 25 + y 26), ((y 14 * y 28) + ((-68) * y 3 * y 30) + y 3 + (y 15 * y 29) + (y 15 * y 21) + (y 23 * y 28) + (y 24 * y 29) + (y 24 * y 21) + (y 25 * y 29) + (y 25 * y 21) + (y 26 * y 28) + -(y 27 * y 20)), (((-68) * y 9 * y 29) + y 9 + -(y 28 * y 20) + y 29 + y 21), (y 8 + ((-68) * y 9 * y 29) + y 28 + -(y 29 * y 20)), (y 2 + (y 14 * y 29) + (y 14 * y 21) + ((-68) * y 3 * y 30) + (y 15 * y 28) + (y 23 * y 29) + (y 23 * y 21) + (y 24 * y 28) + (y 25 * y 28) + (y 26 * y 29) + (y 26 * y 21) + -(y 30 * y 20)), (((-68) * y 1 * y 32) + y 1 + (y 5 * y 21) + -(y 31 * y 20)), (y 0 + (y 4 * y 21) + ((-68) * y 1 * y 32) + -(y 32 * y 20))]

noncomputable def embed (x : Fin 23 → ℝ) : Fin 33 → ℝ :=
  ![x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, (x 13 * x 15), (x 14 * x 13), (x 12 * x 15), (x 12 * x 14), (x 3 * x 21), (x 9 * x 21), (x 8 * x 21), (x 2 * x 21), (x 1 * x 21), (x 0 * x 21)]

noncomputable def chainRule (x : Fin 23 → ℝ) : Fin 10 → ℝ :=
  ![((x 8 * x 13 * x 15) + (x 12 * x 9 * x 15) + ((-68) * x 12 * x 13 * x 15) + ((-68) * x 14 * x 13 * x 15) + (x 14 * x 13) + (x 9 * x 13) + (x 9 * x 15) + (x 13 * x 15)), ((x 8 * x 14 * x 13) + (x 8 * x 13) + (x 12 * x 14 * x 9) + ((-68) * x 12 * x 14 * x 13) + (x 14 * x 9) + ((-68) * x 14 * x 13 * x 15) + (x 14 * x 13) + (x 13 * x 15) + x 13), ((x 8 * x 12 * x 15) + (x 8 * x 15) + ((-68) * x 12 * x 14 * x 15) + (x 12 * x 14) + (x 12 * x 9) + ((-68) * x 12 * x 13 * x 15) + (x 12 * x 15) + (x 9 * x 13 * x 15) + x 15), ((x 8 * x 12 * x 14) + (x 8 * x 12) + (x 8 * x 14) + ((-68) * x 12 * x 14 * x 13) + ((-68) * x 12 * x 14 * x 15) + (x 12 * x 14) + (x 12 * x 15) + x 12 + (x 14 * x 9 * x 13) + x 14), (((-68) * x 2 * x 3 * x 21) + (x 8 * x 12 * x 15 * x 21) + (x 8 * x 14 * x 13 * x 21) + (x 8 * x 15 * x 21) + (x 12 * x 14 * x 9 * x 21) + (x 12 * x 15 * x 21) + (x 14 * x 9 * x 21) + (x 14 * x 13 * x 21) + -(x 3 * x 20 * x 21) + x 3 + (x 9 * x 13 * x 15 * x 21) + (x 15 * x 21)), (((-68) * x 8 * x 9 * x 21) + (x 8 * x 21) + -(x 9 * x 20 * x 21) + x 9 + x 21), (((-68) * x 8 * x 9 * x 21) + -(x 8 * x 20 * x 21) + x 8 + (x 9 * x 21)), (((-68) * x 2 * x 3 * x 21) + -(x 2 * x 20 * x 21) + x 2 + (x 8 * x 12 * x 14 * x 21) + (x 8 * x 14 * x 21) + (x 8 * x 13 * x 15 * x 21) + (x 12 * x 14 * x 21) + (x 12 * x 9 * x 15 * x 21) + (x 14 * x 9 * x 13 * x 21) + (x 14 * x 21) + (x 9 * x 15 * x 21) + (x 13 * x 15 * x 21)), (((-68) * x 0 * x 1 * x 21) + -(x 1 * x 20 * x 21) + x 1 + (x 5 * x 21)), (((-68) * x 0 * x 1 * x 21) + -(x 0 * x 20 * x 21) + x 0 + (x 4 * x 21))]

theorem embed_orig (x : Fin 23 → ℝ) (i : Fin 23) :
    embed x (Fin.castAdd 10 i) = x i := by
  fin_cases i <;> simp [origField, quadField, embed, chainRule, Fin.castAdd, Fin.natAdd, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

theorem orig_correct (x : Fin 23 → ℝ) (i : Fin 23) :
    quadField (embed x) (Fin.castAdd 10 i) = origField x i := by
  fin_cases i <;> simp [origField, quadField, embed, chainRule, Fin.castAdd, Fin.natAdd, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] <;> ring

theorem chain_correct (x : Fin 23 → ℝ) (j : Fin 10) :
    quadField (embed x) (Fin.natAdd 23 j) = chainRule x j := by
  fin_cases j <;> simp [origField, quadField, embed, chainRule, Fin.castAdd, Fin.natAdd, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] <;> ring

noncomputable def certificate : QBeeCertificate 23 10 where
  origField := origField
  quadField := quadField
  embed := embed
  chainRule := chainRule
  embed_orig := embed_orig
  orig_correct := orig_correct
  chain_correct := chain_correct

end GammaDualRail23
end Ripple.LPP.QBee.Generated
