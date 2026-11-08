import Ripple.Number.Modular.ModularPoly41Terms

/-!
# Kernel check of the symmetry of `Φ₄₁`

`Φ₄₁(X, Y) = Φ₄₁(Y, X)`, checked on the term data: in one pass over the terms, bucket `x`
collects the terms with `xPow = x` (the rows); in a second pass, bucket `y` collects the terms with
`yPow = y` (the columns). The data are symmetric exactly when every row equals the corresponding
column with the two exponents swapped. The soundness lemmas (the buckets flatten to a permutation
of the terms, hence `phi41SparseTerms` is a permutation of its swap) are in `Phi41Fricke`.

The module imports only the term data, so that the kernel evaluation does not load Mathlib.
-/

namespace Ripple.Number.Modular

deriving instance DecidableEq for SparseBivarTerm

/-- Swap the two exponents of a term (equal by `rfl` to `swapSparseBivarTerm`). -/
def swapTerm (t : SparseBivarTerm) : SparseBivarTerm := ⟨t.coeff, t.yPow, t.xPow⟩

/-- Prepend `t` to bucket `n` (no change when `n` is out of range). -/
def pushAt (t : SparseBivarTerm) : Nat → List (List SparseBivarTerm) → List (List SparseBivarTerm)
  | _, [] => []
  | 0, b :: bs => (t :: b) :: bs
  | n + 1, b :: bs => b :: pushAt t n bs

/-- One pass over the terms: bucket `i` collects, in reverse order, the terms with `key t = i`. -/
def bucketBy (key : SparseBivarTerm → Nat) (n : Nat) (terms : List SparseBivarTerm) :
    List (List SparseBivarTerm) :=
  terms.foldl (fun acc t => pushAt t (key t) acc) (List.replicate n [])

/-- The rows of `Φ₄₁` are its columns with the exponents swapped. -/
theorem phi41SparseTerms_rows_eq_swapped_cols :
    bucketBy SparseBivarTerm.xPow 43 phi41SparseTerms =
      (bucketBy SparseBivarTerm.yPow 43 phi41SparseTerms).map (List.map swapTerm) := by
  decide +kernel

end Ripple.Number.Modular
