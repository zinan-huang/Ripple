/-
Ripple.BoundedUniversality.HenonSelector.Markov
----------------------------
Q-semialgebraic Markov partition for the Hénon horseshoe at (a,b)=(9,1).

Per Arai-Ishii bounding box:
  R = (1 + |b| + √((1+|b|)² + 4|a|)) / 2.
For (a,b)=(9,1): R = (2 + √40) / 2 = 1 + √10.

Predicate ρ(t) := (t ≥ 0 ∧ t² - 2t - 9 ≤ 0) ∨ (t ≤ 0 ∧ t² + 2t - 9 ≤ 0)
captures |t| ≤ 1 + √10 using only Q-polynomial inequalities.
-/

import Ripple.BoundedUniversality.HenonSelector.Henon
import Ripple.BoundedUniversality.HenonSelector.QSemialg

namespace Ripple.BoundedUniversality.HenonSelector

/-- Q-semialgebraic predicate equivalent to |t| ≤ 1 + √10.
Uses only rational polynomial inequalities. -/
def ρ (t : ℝ) : Prop :=
  (0 ≤ t ∧ t ^ 2 - 2 * t - 9 ≤ 0) ∨ (t ≤ 0 ∧ t ^ 2 + 2 * t - 9 ≤ 0)

/-- The Hénon bounding box D = {(x,y) : ρ(x) ∧ ρ(y)}. -/
def D (p : Point2) : Prop := ρ p.1 ∧ ρ p.2

/-- D with forward image: D ∩ f⁻¹(D). -/
def Dpre (p : Point2) : Prop :=
  D p ∧ D (henon91 p)

/-- The "0-symbol" Markov strip: Dpre ∩ {x < 0}. -/
def D₀ (p : Point2) : Prop :=
  Dpre p ∧ p.1 < 0

/-- The "1-symbol" Markov strip: Dpre ∩ {x > 0}. -/
def D₁ (p : Point2) : Prop :=
  Dpre p ∧ 0 < p.1

/-- Symbol selector: D₀ for false, D₁ for true. -/
def strip (b : Bool) (p : Point2) : Prop :=
  if b then D₁ p else D₀ p

/-- ρ(t) ↔ |t| ≤ 1 + √10. The key equivalence between the
Q-polynomial predicate and the analytic bound. -/
theorem ρ_iff_abs_le (t : ℝ) :
    ρ t ↔ |t| ≤ 1 + Real.sqrt 10 := by
  have hsqrt_pos : 0 < Real.sqrt 10 := Real.sqrt_pos_of_pos (by norm_num)
  have hsqrt_sq : Real.sqrt 10 ^ 2 = 10 := Real.sq_sqrt (by norm_num : (10 : ℝ) ≥ 0)
  constructor
  · intro h
    rcases h with ⟨ht_nn, ht_ineq⟩ | ⟨ht_np, ht_ineq⟩
    · rw [abs_of_nonneg ht_nn]
      nlinarith [sq_nonneg (t - (1 + Real.sqrt 10))]
    · rw [abs_of_nonpos ht_np]
      nlinarith [sq_nonneg (t + (1 + Real.sqrt 10))]
  · intro h
    by_cases ht : 0 ≤ t
    · left
      refine ⟨ht, ?_⟩
      rw [abs_of_nonneg ht] at h
      nlinarith [sq_nonneg (t - (1 + Real.sqrt 10))]
    · right
      push_neg at ht
      refine ⟨ht.le, ?_⟩
      rw [abs_of_neg ht] at h
      nlinarith [sq_nonneg (t + (1 + Real.sqrt 10))]

/-- Helper: construct the MvPolynomial for variable i in dimension 2. -/
private noncomputable def xPoly (i : Fin 2) : MvPolynomial (Fin 2) ℚ :=
  MvPolynomial.X i

/-- The Q-semialgebraic formula encoding ρ for variable at index `i`.
ρ(t) = (t ≥ 0 ∧ t²-2t-9 ≤ 0) ∨ (t ≤ 0 ∧ t²+2t-9 ≤ 0)
Written as: ((-t ≤ 0) ∧ (t²-2t-9 ≤ 0)) ∨ ((t ≤ 0) ∧ (t²+2t-9 ≤ 0)) -/
private noncomputable def ρFormula (i : Fin 2) : QSemialgFormula 2 :=
  let t := xPoly i
  let t_ge_0 := QSemialgFormula.atom (.le (-t))       -- -t ≤ 0 means t ≥ 0
  let t_le_0 := QSemialgFormula.atom (.le t)           -- t ≤ 0
  let q1 := QSemialgFormula.atom (.le (t ^ 2 - 2 * t - 9))  -- t²-2t-9 ≤ 0
  let q2 := QSemialgFormula.atom (.le (t ^ 2 + 2 * t - 9))  -- t²+2t-9 ≤ 0
  .disj (.conj t_ge_0 q1) (.conj t_le_0 q2)

/-- The Q-semialgebraic formula for D = {(x,y) : ρ(x) ∧ ρ(y)}. -/
private noncomputable def dFormula : QSemialgFormula 2 :=
  .conj (ρFormula 0) (ρFormula 1)

private theorem qeval_X (i : Fin 2) (x : Point 2) :
    qeval (xPoly i) x = x i := by
  simp [xPoly, qeval, MvPolynomial.eval₂_X]

private theorem qeval_neg_X (i : Fin 2) (x : Point 2) :
    qeval (-(xPoly i)) x = -(x i) := by
  simp [qeval, xPoly, map_neg, MvPolynomial.eval₂_X]

private theorem qeval_X_sq_sub_2X_sub_9 (i : Fin 2) (x : Point 2) :
    qeval (xPoly i ^ 2 - 2 * xPoly i - (9 : MvPolynomial (Fin 2) ℚ)) x =
    (x i) ^ 2 - 2 * (x i) - 9 := by
  simp [qeval, xPoly, map_sub, map_pow, map_mul, MvPolynomial.eval₂_X,
    MvPolynomial.eval₂_C, map_ofNat]

private theorem qeval_X_sq_add_2X_sub_9 (i : Fin 2) (x : Point 2) :
    qeval (xPoly i ^ 2 + 2 * xPoly i - (9 : MvPolynomial (Fin 2) ℚ)) x =
    (x i) ^ 2 + 2 * (x i) - 9 := by
  simp [qeval, xPoly, map_sub, map_add, map_pow, map_mul, MvPolynomial.eval₂_X,
    MvPolynomial.eval₂_C, map_ofNat]

private theorem ρFormula_realize_iff (i : Fin 2) (x : Point 2) :
    (ρFormula i).Realize x ↔ ρ (x i) := by
  unfold ρFormula
  simp only [QSemialgFormula.Realize, ρ,
    qeval_neg_X, qeval_X, qeval_X_sq_sub_2X_sub_9, qeval_X_sq_add_2X_sub_9]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · left; exact ⟨by linarith, h2⟩
    · right; exact ⟨h1, h2⟩
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · left; exact ⟨by linarith, h2⟩
    · right; exact ⟨h1, h2⟩

theorem D_isQSemialgebraicPair :
    IsQSemialgebraicPair { p : Point2 | D p } := by
  refine ⟨dFormula, ?_⟩
  ext ⟨x₁, x₂⟩
  simp only [Set.mem_setOf_eq, D, dFormula, QSemialgFormula.Realize,
    point2ToPoint, Prod.fst, Prod.snd]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · have : point2ToPoint (x₁, x₂) = fun i => if i = 0 then x₁ else x₂ := rfl
      rw [this] at *
      exact (ρFormula_realize_iff 0 _).mpr h1
    · have : point2ToPoint (x₁, x₂) = fun i => if i = 0 then x₁ else x₂ := rfl
      rw [this] at *
      exact (ρFormula_realize_iff 1 _).mpr h2
  · rintro ⟨h1, h2⟩
    have hpt : point2ToPoint (x₁, x₂) = fun i => if i = 0 then x₁ else x₂ := rfl
    rw [hpt] at h1 h2
    exact ⟨(ρFormula_realize_iff 0 _).mp h1, (ρFormula_realize_iff 1 _).mp h2⟩

end Ripple.BoundedUniversality.HenonSelector
