/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Lemma17Reaction

/-!
# Fixed Lemma 17 scale with a custom landing slot

The ordinary prefix is dyadic through `m`.  The error envelope also inspects
the otherwise unused slot `m + 1`; that slot must record the custom decisive
target rather than another dyadic doubling.
-/

namespace Tri

noncomputable section

/-- Dyadic prefix through `m`, followed by the custom landing target. -/
def lemma17ScaleWithLanding
    (a m target j : ℕ) : ℕ :=
  if j ≤ m then lemma17Scale a j else target

@[simp] theorem lemma17ScaleWithLanding_of_le
    (a m target j : ℕ) (hj : j ≤ m) :
    lemma17ScaleWithLanding a m target j =
      lemma17Scale a j := by
  simp [lemma17ScaleWithLanding, hj]

@[simp] theorem lemma17ScaleWithLanding_zero
    (a m target : ℕ) :
    lemma17ScaleWithLanding a m target 0 = a := by
  simp [lemma17ScaleWithLanding]

theorem lemma17ScaleWithLanding_succ
    (a m target j : ℕ) (hj : j < m) :
    lemma17ScaleWithLanding a m target (j + 1) =
      2 * lemma17ScaleWithLanding a m target j := by
  rw [lemma17ScaleWithLanding_of_le _ _ _ _
      (by omega),
    lemma17ScaleWithLanding_of_le _ _ _ _
      (by omega),
    lemma17Scale_succ]

@[simp] theorem lemma17ScaleWithLanding_target
    (a m target : ℕ) :
    lemma17ScaleWithLanding a m target (m + 1) =
      target := by
  simp [lemma17ScaleWithLanding]

/-- Every ordinary source slot, including the custom source at `m`, agrees
with the dyadic scale used by the fixed prefix certificates. -/
theorem lemma17ScaleWithLanding_prefix
    (a m target : ℕ) :
    ∀ j ≤ m,
      lemma17ScaleWithLanding a m target j =
        lemma17Scale a j :=
  fun j hj =>
    lemma17ScaleWithLanding_of_le
      a m target j hj

end

end Tri

#print axioms Tri.lemma17ScaleWithLanding_of_le
#print axioms Tri.lemma17ScaleWithLanding_succ
#print axioms Tri.lemma17ScaleWithLanding_target
#print axioms Tri.lemma17ScaleWithLanding_prefix
