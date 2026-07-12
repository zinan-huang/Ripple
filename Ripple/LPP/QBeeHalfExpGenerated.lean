/-
  Auto-generated QBee certificate for `halfExp`.
  Original variables: 3; new QBee variables: 0; total: 3.
-/

import Ripple.LPP.QBeeGeneric

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.style.longLine false

namespace Ripple.LPP.QBee.Generated
namespace HalfExp

noncomputable def origField (x : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![((-2) * x 1 * x 0), -(x 1), ((2 * x 1 * x 0) + x 1)]

noncomputable def quadField (y : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![((-2) * y 1 * y 0), -(y 1), ((2 * y 1 * y 0) + y 1)]

noncomputable def embed (x : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![x 0, x 1, x 2]

noncomputable def chainRule (_x : Fin 3 → ℝ) : Fin 0 → ℝ :=
  fun j => nomatch j

theorem embed_orig (x : Fin 3 → ℝ) (i : Fin 3) :
    embed x (Fin.castAdd 0 i) = x i := by
  fin_cases i <;> simp [origField, quadField, embed, chainRule, Fin.castAdd, Fin.natAdd, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

theorem orig_correct (x : Fin 3 → ℝ) (i : Fin 3) :
    quadField (embed x) (Fin.castAdd 0 i) = origField x i := by
  fin_cases i <;> simp [origField, quadField, embed, chainRule, Fin.castAdd, Fin.natAdd, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] <;> ring

theorem chain_correct (x : Fin 3 → ℝ) (j : Fin 0) :
    quadField (embed x) (Fin.natAdd 3 j) = chainRule x j := by
  exact Fin.elim0 j

noncomputable def certificate : QBeeCertificate 3 0 where
  origField := origField
  quadField := quadField
  embed := embed
  chainRule := chainRule
  embed_orig := embed_orig
  orig_correct := orig_correct
  chain_correct := chain_correct

end HalfExp
end Ripple.LPP.QBee.Generated
