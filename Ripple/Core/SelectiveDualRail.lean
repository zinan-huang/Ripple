import Ripple.Core.CRNReadout
import Ripple.Core.MaximalPIVP
import Ripple.Core.ODEBox

/-!
# Selective dual rail for BAC journal A1

Auxiliary coordinates are dual railed with polynomial-scale annihilation.
A multiplicative scalar output is retained as one species. The source and
the CRN are compared at the same time, including nonzero rational initial
data. Only the auxiliary rail sums have the universal square-root bound.
-/

noncomputable section

namespace Ripple.SelectiveDualRail

open MvPolynomial MeasureTheory

variable {d : ℕ}

def pos (j : Fin d) : Fin (2 * d + 1) :=
  Fin.castSucc (dualRailU j)

def neg (j : Fin d) : Fin (2 * d + 1) :=
  Fin.castSucc (dualRailV j)

def out : Fin (2 * d + 1) := Fin.last (2 * d)

def decode (x : Fin (2 * d + 1) → ℝ) : Fin d → ℝ :=
  fun j => x (pos j) - x (neg j)

def hat (p : MvPolynomial (Fin d) ℚ) :
    MvPolynomial (Fin (2 * d + 1)) ℚ :=
  MvPolynomial.bind₁ (fun j => X (pos j) - X (neg j)) p

def plus (p : MvPolynomial (Fin d) ℚ) :
    MvPolynomial (Fin (2 * d + 1)) ℚ :=
  DualRail.posPart (hat p)

def minus (p : MvPolynomial (Fin d) ℚ) :
    MvPolynomial (Fin (2 * d + 1)) ℚ :=
  DualRail.negPart (hat p)

theorem eval_hat (p : MvPolynomial (Fin d) ℚ)
    (x : Fin (2 * d + 1) → ℝ) :
    (hat p).eval₂ (Rat.castHom ℝ) x =
      p.eval₂ (Rat.castHom ℝ) (decode x) := by
  unfold hat
  rw [← MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂Hom_bind₁]
  have hs :
      (fun j => (MvPolynomial.eval₂Hom (Rat.castHom ℝ) x)
        (X (pos j) - X (neg j))) = decode x := by
    funext j
    simp only [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_sub,
      MvPolynomial.eval₂_X, decode]
  rw [hs, MvPolynomial.coe_eval₂Hom]

theorem split_eval (p : MvPolynomial (Fin d) ℚ)
    (x : Fin (2 * d + 1) → ℝ) :
    (plus p).eval₂ (Rat.castHom ℝ) x -
        (minus p).eval₂ (Rat.castHom ℝ) x =
      p.eval₂ (Rat.castHom ℝ) (decode x) := by
  unfold plus minus
  rw [DualRail.posPart_eval_sub_negPart_eval]
  exact eval_hat p x

theorem plus_nonneg (p : MvPolynomial (Fin d) ℚ)
    (x : Fin (2 * d + 1) → ℝ) (hx : ∀ k, 0 ≤ x k) :
    0 ≤ (plus p).eval₂ (Rat.castHom ℝ) x :=
  DualRail.posPart_eval_nonneg (hat p) x hx

theorem minus_nonneg (p : MvPolynomial (Fin d) ℚ)
    (x : Fin (2 * d + 1) → ℝ) (hx : ∀ k, 0 ≤ x k) :
    0 ≤ (minus p).eval₂ (Rat.castHom ℝ) x :=
  DualRail.negPart_eval_nonneg (hat p) x hx

theorem coordinate_cases (k : Fin (2 * d + 1)) :
    (∃ j, k = pos j) ∨ (∃ j, k = neg j) ∨ k = out := by
  refine Fin.lastCases ?_ (fun l => ?_) k
  · exact Or.inr (Or.inr rfl)
  · by_cases he : l.val % 2 = 0
    · left
      refine ⟨dualRailJ l, ?_⟩
      apply Fin.ext
      change l.val = 2 * (l.val / 2)
      omega
    · right
      left
      refine ⟨dualRailJ l, ?_⟩
      apply Fin.ext
      change l.val = 2 * (l.val / 2) + 1
      omega

def railInitial (a₀ : Fin d → ℚ) (k : Fin (2 * d)) : ℚ :=
  if k.val % 2 = 0 then max (a₀ (dualRailJ k)) 0
  else max (-a₀ (dualRailJ k)) 0

def production
    (G : Fin d → MvPolynomial (Fin d) ℚ)
    (h : MvPolynomial (Fin d) ℚ) :
    Fin (2 * d + 1) → MvPolynomial (Fin (2 * d + 1)) ℚ :=
  Fin.snoc
    (fun k => if k.val % 2 = 0 then plus (G (dualRailJ k))
      else minus (G (dualRailJ k)))
    (X out * plus h)

def degradation
    (G : Fin d → MvPolynomial (Fin d) ℚ)
    (h : MvPolynomial (Fin d) ℚ) :
    Fin (2 * d + 1) → MvPolynomial (Fin (2 * d + 1)) ℚ :=
  Fin.snoc
    (fun k => if k.val % 2 = 0 then
        X (neg (dualRailJ k)) *
          (plus (G (dualRailJ k)) + minus (G (dualRailJ k)))
      else
        X (pos (dualRailJ k)) *
          (plus (G (dualRailJ k)) + minus (G (dualRailJ k))))
    (minus h)

/-- Rational polynomial syntax for the exact selective CRN. -/
def compile
    (G : Fin d → MvPolynomial (Fin d) ℚ)
    (h : MvPolynomial (Fin d) ℚ)
    (a₀ : Fin d → ℚ) (z₀ : ℚ) : PolyPIVP (2 * d + 1) where
  field := fun k => production G h k - degradation G h k * X k
  init := Fin.snoc (railInitial a₀) z₀
  output := out

@[simp] theorem production_pos
    (G : Fin d → MvPolynomial (Fin d) ℚ)
    (h : MvPolynomial (Fin d) ℚ) (j : Fin d) :
    production G h (pos j) = plus (G j) := by
  have hk : (dualRailU j).val % 2 = 0 := by
    change (2 * j.val) % 2 = 0
    omega
  simp only [production, pos, Fin.snoc_castSucc, hk, if_true,
    dualRailJ_of_u]

@[simp] theorem production_neg
    (G : Fin d → MvPolynomial (Fin d) ℚ)
    (h : MvPolynomial (Fin d) ℚ) (j : Fin d) :
    production G h (neg j) = minus (G j) := by
  have hk : ¬ (dualRailV j).val % 2 = 0 := by
    change ¬ (2 * j.val + 1) % 2 = 0
    omega
  simp only [production, neg, Fin.snoc_castSucc, hk, if_false,
    dualRailJ_of_v]

@[simp] theorem production_out
    (G : Fin d → MvPolynomial (Fin d) ℚ)
    (h : MvPolynomial (Fin d) ℚ) :
    production G h out = X out * plus h := by
  simp only [production, out, Fin.snoc_last]

@[simp] theorem degradation_pos
    (G : Fin d → MvPolynomial (Fin d) ℚ)
    (h : MvPolynomial (Fin d) ℚ) (j : Fin d) :
    degradation G h (pos j) =
      X (neg j) * (plus (G j) + minus (G j)) := by
  have hk : (dualRailU j).val % 2 = 0 := by
    change (2 * j.val) % 2 = 0
    omega
  simp only [degradation, pos, Fin.snoc_castSucc, hk, if_true,
    dualRailJ_of_u]

@[simp] theorem degradation_neg
    (G : Fin d → MvPolynomial (Fin d) ℚ)
    (h : MvPolynomial (Fin d) ℚ) (j : Fin d) :
    degradation G h (neg j) =
      X (pos j) * (plus (G j) + minus (G j)) := by
  have hk : ¬ (dualRailV j).val % 2 = 0 := by
    change ¬ (2 * j.val + 1) % 2 = 0
    omega
  simp only [degradation, neg, Fin.snoc_castSucc, hk, if_false,
    dualRailJ_of_v]

@[simp] theorem degradation_out
    (G : Fin d → MvPolynomial (Fin d) ℚ)
    (h : MvPolynomial (Fin d) ℚ) :
    degradation G h out = minus h := by
  simp only [degradation, out, Fin.snoc_last]

@[simp] theorem initial_pos
    (G : Fin d → MvPolynomial (Fin d) ℚ)
    (h : MvPolynomial (Fin d) ℚ)
    (a₀ : Fin d → ℚ) (z₀ : ℚ) (j : Fin d) :
    (compile G h a₀ z₀).init (pos j) = max (a₀ j) 0 := by
  have hk : (dualRailU j).val % 2 = 0 := by
    change (2 * j.val) % 2 = 0
    omega
  simp only [compile, pos, Fin.snoc_castSucc, railInitial, hk,
    if_true, dualRailJ_of_u]

@[simp] theorem initial_neg
    (G : Fin d → MvPolynomial (Fin d) ℚ)
    (h : MvPolynomial (Fin d) ℚ)
    (a₀ : Fin d → ℚ) (z₀ : ℚ) (j : Fin d) :
    (compile G h a₀ z₀).init (neg j) = max (-a₀ j) 0 := by
  have hk : ¬ (dualRailV j).val % 2 = 0 := by
    change ¬ (2 * j.val + 1) % 2 = 0
    omega
  simp only [compile, neg, Fin.snoc_castSucc, railInitial, hk,
    if_false, dualRailJ_of_v]

@[simp] theorem initial_out
    (G : Fin d → MvPolynomial (Fin d) ℚ)
    (h : MvPolynomial (Fin d) ℚ)
    (a₀ : Fin d → ℚ) (z₀ : ℚ) :
    (compile G h a₀ z₀).init out = z₀ := by
  simp only [compile, out, Fin.snoc_last]

theorem initial_decode
    (G : Fin d → MvPolynomial (Fin d) ℚ)
    (h : MvPolynomial (Fin d) ℚ)
    (a₀ : Fin d → ℚ) (z₀ : ℚ) :
    decode (fun k => ((compile G h a₀ z₀).init k : ℝ)) =
      fun j => (a₀ j : ℝ) := by
  funext j
  simp only [decode, initial_pos, initial_neg]
  have hs : max (a₀ j) 0 - max (-a₀ j) 0 = a₀ j := by
    by_cases hj : 0 ≤ a₀ j
    · rw [max_eq_left hj, max_eq_right (neg_nonpos.mpr hj)]
      ring
    · have hj' : a₀ j ≤ 0 := (lt_of_not_ge hj).le
      rw [max_eq_right hj', max_eq_left (neg_nonneg.mpr hj')]
      ring
  exact_mod_cast hs

theorem initial_pair_sum
    (G : Fin d → MvPolynomial (Fin d) ℚ)
    (h : MvPolynomial (Fin d) ℚ)
    (a₀ : Fin d → ℚ) (z₀ : ℚ) (j : Fin d) :
    ((compile G h a₀ z₀).init (pos j) : ℝ) +
        ((compile G h a₀ z₀).init (neg j) : ℝ) = |(a₀ j : ℝ)| := by
  rw [initial_pos, initial_neg]
  have hs : max (a₀ j) 0 + max (-a₀ j) 0 = |a₀ j| := by
    by_cases hj : 0 ≤ a₀ j
    · rw [max_eq_left hj, max_eq_right (neg_nonpos.mpr hj),
        abs_of_nonneg hj]
      ring
    · have hj' : a₀ j ≤ 0 := (lt_of_not_ge hj).le
      rw [max_eq_right hj', max_eq_left (neg_nonneg.mpr hj'),
        abs_of_nonpos hj']
      ring
  exact_mod_cast hs

/-- A concrete mass-action decomposition with nonnegative rational data. -/
def decomposition
    (G : Fin d → MvPolynomial (Fin d) ℚ)
    (h : MvPolynomial (Fin d) ℚ)
    (a₀ : Fin d → ℚ) (z₀ : ℚ) (hz₀ : 0 ≤ z₀) :
    PolyCRNDecomposition (2 * d + 1) (compile G h a₀ z₀) where
  prod := production G h
  degr := degradation G h
  prod_nonneg := by
    intro k m
    refine Fin.lastCases ?_ (fun l => ?_) k
    · simp only [production, Fin.snoc_last]
      exact CRNReadout.coeff_nonneg_mul
        (CRNReadout.coeff_nonneg_X out)
        (DualRail.posPart_coeff_nonneg (hat h)) m
    · simp only [production, Fin.snoc_castSucc]
      split_ifs
      · exact DualRail.posPart_coeff_nonneg _ _
      · exact DualRail.negPart_coeff_nonneg _ _
  degr_nonneg := by
    intro k m
    refine Fin.lastCases ?_ (fun l => ?_) k
    · simp only [degradation, Fin.snoc_last]
      exact DualRail.negPart_coeff_nonneg _ _
    · simp only [degradation, Fin.snoc_castSucc]
      have hs :
          ∀ m, 0 ≤
            (plus (G (dualRailJ l)) + minus (G (dualRailJ l))).coeff m :=
        CRNReadout.coeff_nonneg_add
          (DualRail.posPart_coeff_nonneg _) (DualRail.negPart_coeff_nonneg _)
      split_ifs
      · exact CRNReadout.coeff_nonneg_mul
          (CRNReadout.coeff_nonneg_X _) hs m
      · exact CRNReadout.coeff_nonneg_mul
          (CRNReadout.coeff_nonneg_X _) hs m
  init_nonneg := by
    intro k
    refine Fin.lastCases ?_ (fun l => ?_) k
    · simpa only [compile, Fin.snoc_last] using hz₀
    · simp only [compile, Fin.snoc_castSucc]
      unfold railInitial
      split_ifs <;> exact le_max_right _ _
  field_eq := fun _ => rfl

theorem field_pos
    (G : Fin d → MvPolynomial (Fin d) ℚ)
    (h : MvPolynomial (Fin d) ℚ)
    (a₀ : Fin d → ℚ) (z₀ : ℚ)
    (x : Fin (2 * d + 1) → ℝ) (j : Fin d) :
    (compile G h a₀ z₀).evalField x (pos j) =
      (plus (G j)).eval₂ (Rat.castHom ℝ) x -
        x (pos j) * x (neg j) *
          ((plus (G j)).eval₂ (Rat.castHom ℝ) x +
            (minus (G j)).eval₂ (Rat.castHom ℝ) x) := by
  change (production G h (pos j) - degradation G h (pos j) * X (pos j)).eval₂
      (Rat.castHom ℝ) x = _
  rw [production_pos, degradation_pos]
  simp only [eval₂_sub, eval₂_mul, eval₂_add, eval₂_X]
  ring

theorem field_neg
    (G : Fin d → MvPolynomial (Fin d) ℚ)
    (h : MvPolynomial (Fin d) ℚ)
    (a₀ : Fin d → ℚ) (z₀ : ℚ)
    (x : Fin (2 * d + 1) → ℝ) (j : Fin d) :
    (compile G h a₀ z₀).evalField x (neg j) =
      (minus (G j)).eval₂ (Rat.castHom ℝ) x -
        x (pos j) * x (neg j) *
          ((plus (G j)).eval₂ (Rat.castHom ℝ) x +
            (minus (G j)).eval₂ (Rat.castHom ℝ) x) := by
  change (production G h (neg j) - degradation G h (neg j) * X (neg j)).eval₂
      (Rat.castHom ℝ) x = _
  rw [production_neg, degradation_neg]
  simp only [eval₂_sub, eval₂_mul, eval₂_add, eval₂_X]
  ring

theorem field_out_split
    (G : Fin d → MvPolynomial (Fin d) ℚ)
    (h : MvPolynomial (Fin d) ℚ)
    (a₀ : Fin d → ℚ) (z₀ : ℚ)
    (x : Fin (2 * d + 1) → ℝ) :
    (compile G h a₀ z₀).evalField x out =
      x out * (plus h).eval₂ (Rat.castHom ℝ) x -
        x out * (minus h).eval₂ (Rat.castHom ℝ) x := by
  change (production G h out - degradation G h out * X out).eval₂
      (Rat.castHom ℝ) x = _
  rw [production_out, degradation_out]
  simp only [eval₂_sub, eval₂_mul, eval₂_X]
  ring

theorem field_out
    (G : Fin d → MvPolynomial (Fin d) ℚ)
    (h : MvPolynomial (Fin d) ℚ)
    (a₀ : Fin d → ℚ) (z₀ : ℚ)
    (x : Fin (2 * d + 1) → ℝ) :
    (compile G h a₀ z₀).evalField x out =
      x out * h.eval₂ (Rat.castHom ℝ) (decode x) := by
  rw [field_out_split, ← mul_sub, split_eval h x]

theorem field_difference
    (G : Fin d → MvPolynomial (Fin d) ℚ)
    (h : MvPolynomial (Fin d) ℚ)
    (a₀ : Fin d → ℚ) (z₀ : ℚ)
    (x : Fin (2 * d + 1) → ℝ) (j : Fin d) :
    (compile G h a₀ z₀).evalField x (pos j) -
        (compile G h a₀ z₀).evalField x (neg j) =
      (G j).eval₂ (Rat.castHom ℝ) (decode x) := by
  rw [field_pos, field_neg, ← split_eval (G j) x]
  ring

theorem field_sum
    (G : Fin d → MvPolynomial (Fin d) ℚ)
    (h : MvPolynomial (Fin d) ℚ)
    (a₀ : Fin d → ℚ) (z₀ : ℚ)
    (x : Fin (2 * d + 1) → ℝ) (j : Fin d) :
    (compile G h a₀ z₀).evalField x (pos j) +
        (compile G h a₀ z₀).evalField x (neg j) =
      ((plus (G j)).eval₂ (Rat.castHom ℝ) x +
        (minus (G j)).eval₂ (Rat.castHom ℝ) x) *
          (1 - 2 * x (pos j) * x (neg j)) := by
  rw [field_pos, field_neg]
  ring

/-! ## The pair-sum barrier -/

theorem rail_sum_bound {T M : ℝ} (u v q : ℝ → ℝ)
    (hinit : u 0 + v 0 ≤ M)
    (hderiv : ∀ s ∈ Set.Ico (0 : ℝ) T,
      HasDerivAt (fun r => u r + v r) (q s * (1 - 2 * u s * v s)) s)
    (hq : ∀ s ∈ Set.Ico (0 : ℝ) T, 0 ≤ q s)
    (hdiff : ∀ s ∈ Set.Ico (0 : ℝ) T, |u s - v s| ≤ M)
    {t : ℝ} (ht : t ∈ Set.Ico (0 : ℝ) T) :
    u t + v t ≤ Real.sqrt (2 + M ^ 2) := by
  have hroot : 0 ≤ Real.sqrt (2 + M ^ 2) := Real.sqrt_nonneg _
  have hroot_sq : (Real.sqrt (2 + M ^ 2)) ^ 2 = 2 + M ^ 2 :=
    Real.sq_sqrt (by positivity)
  have hstart : u 0 + v 0 ≤ Real.sqrt (2 + M ^ 2) :=
    hinit.trans (Real.le_sqrt_of_sq_le (by linarith))
  have hc : ContinuousOn (fun r => u r + v r) (Set.Icc (0 : ℝ) t) := by
    intro s hs
    exact (hderiv s ⟨hs.1, hs.2.trans_lt ht.2⟩).continuousAt.continuousWithinAt
  have hd : ∀ s ∈ Set.Ico (0 : ℝ) t,
      HasDerivWithinAt (fun r => u r + v r)
        (q s * (1 - 2 * u s * v s)) (Set.Ici s) s := by
    intro s hs
    exact (hderiv s ⟨hs.1, hs.2.trans ht.2⟩).hasDerivWithinAt
  have hb : ∀ s ∈ Set.Ico (0 : ℝ) t,
      Real.sqrt (2 + M ^ 2) ≤ u s + v s →
      q s * (1 - 2 * u s * v s) ≤ 0 := by
    intro s hs hlarge
    have hsT : s ∈ Set.Ico (0 : ℝ) T := ⟨hs.1, hs.2.trans ht.2⟩
    have hsum_sq : (Real.sqrt (2 + M ^ 2)) ^ 2 ≤ (u s + v s) ^ 2 :=
      pow_le_pow_left₀ hroot hlarge 2
    have hdiff_sq : (u s - v s) ^ 2 ≤ M ^ 2 := by
      simpa only [sq_abs] using
        (pow_le_pow_left₀ (abs_nonneg (u s - v s)) (hdiff s hsT) 2)
    have hfactor : 1 - 2 * u s * v s ≤ 0 := by
      nlinarith [hroot_sq, hsum_sq, hdiff_sq]
    exact mul_nonpos_of_nonneg_of_nonpos (hq s hsT) hfactor
  exact scalar_upper_barrier_exterior_on_Icc ht.1
    (fun r => u r + v r) (fun r => q r * (1 - 2 * u r * v r))
    hstart hc hd hb t ⟨ht.1, le_rfl⟩

theorem rail_bounds_of_sum_bound {u v M : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hs : u + v ≤ Real.sqrt (2 + M ^ 2)) :
    (0 ≤ u ∧ u ≤ Real.sqrt (2 + M ^ 2)) ∧
      (0 ≤ v ∧ v ≤ Real.sqrt (2 + M ^ 2)) := by
  constructor
  · exact ⟨hu, by linarith⟩
  · exact ⟨hv, by linarith⟩

/-! ## The source triangular PIVP and same-time uniqueness -/

def source
    (G : Fin d → MvPolynomial (Fin d) ℚ)
    (h : MvPolynomial (Fin d) ℚ)
    (a₀ : Fin d → ℚ) (z₀ : ℚ) : PolyPIVP (d + 1) where
  field := Fin.snoc
    (fun j => MvPolynomial.rename Fin.castSucc (G j))
    (MvPolynomial.X (Fin.last d) * MvPolynomial.rename Fin.castSucc h)
  init := Fin.snoc a₀ z₀
  output := Fin.last d

theorem source_field_snoc
    (G : Fin d → MvPolynomial (Fin d) ℚ)
    (h : MvPolynomial (Fin d) ℚ)
    (a₀ : Fin d → ℚ) (z₀ : ℚ)
    (a : Fin d → ℝ) (z : ℝ) :
    (source G h a₀ z₀).evalField (Fin.snoc a z) =
      Fin.snoc (fun j => (G j).eval₂ (Rat.castHom ℝ) a)
        (z * h.eval₂ (Rat.castHom ℝ) a) := by
  funext k
  refine Fin.lastCases ?_ (fun j => ?_) k
  · simp [source, PolyPIVP.evalField, MvPolynomial.eval₂_rename,
      Function.comp_def]
  · simp [source, PolyPIVP.evalField, MvPolynomial.eval₂_rename,
      Function.comp_def]

theorem source_initial_cast
    (G : Fin d → MvPolynomial (Fin d) ℚ)
    (h : MvPolynomial (Fin d) ℚ)
    (a₀ : Fin d → ℚ) (z₀ : ℚ) :
    (fun k => ((source G h a₀ z₀).init k : ℝ)) =
      Fin.snoc (fun j => (a₀ j : ℝ)) (z₀ : ℝ) := by
  funext k
  refine Fin.lastCases ?_ (fun j => ?_) k <;> simp [source]

private theorem snoc_hasDerivAt
    {a : ℝ → Fin d → ℝ} {z : ℝ → ℝ}
    {a' : Fin d → ℝ} {z' t : ℝ}
    (ha : HasDerivAt a a' t) (hz : HasDerivAt z z' t) :
    HasDerivAt (fun s => Fin.snoc (α := fun _ => ℝ) (a s) (z s))
      (Fin.snoc (α := fun _ => ℝ) a' z') t := by
  apply hasDerivAt_pi.mpr
  intro k
  refine Fin.lastCases ?_ (fun j => ?_) k
  · simpa only [Fin.snoc_last] using hz
  · simpa only [Fin.snoc_castSucc] using (hasDerivAt_pi.mp ha j)

def sourceSolution
    (G : Fin d → MvPolynomial (Fin d) ℚ)
    (h : MvPolynomial (Fin d) ℚ)
    (a₀ : Fin d → ℚ) (z₀ : ℚ)
    (a : ℝ → Fin d → ℝ) (z : ℝ → ℝ)
    (ha₀ : a 0 = fun j => (a₀ j : ℝ))
    (hzinit : z 0 = (z₀ : ℝ))
    (ha : ∀ t, 0 ≤ t →
      HasDerivAt a (fun j => (G j).eval₂ (Rat.castHom ℝ) (a t)) t)
    (hz : ∀ t, 0 ≤ t →
      HasDerivAt z (z t * h.eval₂ (Rat.castHom ℝ) (a t)) t) :
    PIVP.Solution (source G h a₀ z₀).toPIVP where
  trajectory := fun t => Fin.snoc (a t) (z t)
  init_cond := by
    change Fin.snoc (a 0) (z 0) =
      fun k => ((source G h a₀ z₀).init k : ℝ)
    rw [ha₀, hzinit, source_initial_cast]
  is_solution := by
    intro t ht
    change HasDerivAt (fun s => Fin.snoc (a s) (z s))
      ((source G h a₀ z₀).evalField (Fin.snoc (a t) (z t))) t
    rw [source_field_snoc]
    exact snoc_hasDerivAt (ha t ht) (hz t ht)

/-- Decoding a local selective solution gives a source solution on the
identical forward interval. No time reparametrization occurs. -/
def decodedForward
    (G : Fin d → MvPolynomial (Fin d) ℚ)
    (h : MvPolynomial (Fin d) ℚ)
    (a₀ : Fin d → ℚ) (z₀ : ℚ)
    (u : MaximalPIVP.ForwardSolution (compile G h a₀ z₀)) :
    MaximalPIVP.ForwardSolution (source G h a₀ z₀) where
  lifetime := u.lifetime
  positive := u.positive
  trajectory := fun t => Fin.snoc (decode (u.trajectory t)) (u.trajectory t out)
  initial := by
    rw [u.initial, initial_decode, source_initial_cast]
    simp only [initial_out]
  ode := by
    intro t ht
    have hc := hasDerivAt_pi.mp (u.ode t ht)
    have ha : HasDerivAt (fun s => decode (u.trajectory s))
        (fun j => (G j).eval₂ (Rat.castHom ℝ) (decode (u.trajectory t))) t := by
      apply hasDerivAt_pi.mpr
      intro j
      have hj := (hc (pos j)).sub (hc (neg j))
      rw [field_difference] at hj
      exact hj
    have hz : HasDerivAt (fun s => u.trajectory s out)
        (u.trajectory t out * h.eval₂ (Rat.castHom ℝ)
          (decode (u.trajectory t))) t := by
      simpa only [field_out] using hc out
    rw [source_field_snoc]
    exact snoc_hasDerivAt ha hz

/-- The exact coordinatewise sup-norm bound, separating rails from output. -/
theorem norm_le (x : Fin (2 * d + 1) → ℝ) {R B : ℝ}
    (hR : 0 ≤ R) (hB : 0 ≤ B)
    (hnn : ∀ k, 0 ≤ x k)
    (hsum : ∀ j, x (pos j) + x (neg j) ≤ R)
    (hout : |x out| ≤ B) :
    ‖x‖ ≤ max R B := by
  apply (pi_norm_le_iff_of_nonneg (hR.trans (le_max_left _ _))).mpr
  intro k
  rw [Real.norm_eq_abs, abs_of_nonneg (hnn k)]
  rcases coordinate_cases k with ⟨j, rfl⟩ | ⟨j, rfl⟩ | rfl
  · exact (show x (pos j) ≤ R by linarith [hsum j, hnn (neg j)]).trans
      (le_max_left _ _)
  · exact (show x (neg j) ≤ R by linarith [hsum j, hnn (pos j)]).trans
      (le_max_left _ _)
  · exact ((le_abs_self _).trans hout).trans (le_max_right _ _)

private theorem local_spec
    (G : Fin d → MvPolynomial (Fin d) ℚ)
    (h : MvPolynomial (Fin d) ℚ)
    (a₀ : Fin d → ℚ) (z₀ : ℚ) (hz₀ : 0 ≤ z₀)
    (s : PIVP.Solution (source G h a₀ z₀).toPIVP)
    (M : ℝ)
    (hbound : ∀ t, 0 ≤ t → ∀ j,
      |s.trajectory t (Fin.castSucc j)| ≤ M)
    (T : ℝ) (hT : 0 < T)
    (y : ℝ → Fin (2 * d + 1) → ℝ)
    (hyinit : y 0 = fun k => ((compile G h a₀ z₀).init k : ℝ))
    (hy : ∀ t ∈ Set.Ico (0 : ℝ) T,
      HasDerivAt y ((compile G h a₀ z₀).evalField (y t)) t) :
    ∀ t ∈ Set.Ico (0 : ℝ) T,
      (∀ k, 0 ≤ y t k) ∧
      decode (y t) = (fun j => s.trajectory t (Fin.castSucc j)) ∧
      y t out = s.trajectory t (Fin.last d) ∧
      (∀ j, y t (pos j) + y t (neg j) ≤ Real.sqrt (2 + M ^ 2)) := by
  let pcd := decomposition G h a₀ z₀ hz₀
  have hnn : ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ k, 0 ≤ y t k := by
    apply crn_local_nonneg pcd.toIsCRNImplementable
      (polyPIVP_field_locally_lipschitz (compile G h a₀ z₀)) T hT y
    · intro k
      rw [hyinit]
      show (0 : ℝ) ≤ ((compile G h a₀ z₀).init k : ℝ)
      exact_mod_cast pcd.init_nonneg k
    · exact hy
  let u := MaximalPIVP.ForwardSolution.ofIco
    (compile G h a₀ z₀) T hT y hyinit hy
  have heq : ∀ t ∈ Set.Ico (0 : ℝ) T,
      Fin.snoc (decode (y t)) (y t out) = s.trajectory t := by
    intro t ht
    have hu : t ∈ MaximalPIVP.forwardInterval u.lifetime := by
      change 0 ≤ t ∧ ENNReal.ofReal t < ENNReal.ofReal T
      exact ⟨ht.1, (ENNReal.ofReal_lt_ofReal_iff hT).mpr ht.2⟩
    exact (decodedForward G h a₀ z₀ u).agree
      (MaximalPIVP.ForwardSolution.ofGlobal s) hu
      ⟨ht.1, (ENNReal.ofReal_lt_top : ENNReal.ofReal t < ⊤)⟩
  have hdec : ∀ t ∈ Set.Ico (0 : ℝ) T,
      decode (y t) = (fun j => s.trajectory t (Fin.castSucc j)) := by
    intro t ht
    funext j
    simpa only [Fin.snoc_castSucc] using congrFun (heq t ht) (Fin.castSucc j)
  have hout : ∀ t ∈ Set.Ico (0 : ℝ) T,
      y t out = s.trajectory t (Fin.last d) := by
    intro t ht
    simpa only [Fin.snoc_last] using congrFun (heq t ht) (Fin.last d)
  intro t ht
  refine ⟨hnn t ht, hdec t ht, hout t ht, ?_⟩
  intro j
  apply rail_sum_bound
    (fun r => y r (pos j)) (fun r => y r (neg j))
    (fun r => (plus (G j)).eval₂ (Rat.castHom ℝ) (y r) +
      (minus (G j)).eval₂ (Rat.castHom ℝ) (y r)) ?_ ?_ ?_ ?_ ht
  · show y 0 (pos j) + y 0 (neg j) ≤ M
    rw [hyinit]
    show ((compile G h a₀ z₀).init (pos j) : ℝ) +
        ((compile G h a₀ z₀).init (neg j) : ℝ) ≤ M
    rw [initial_pair_sum]
    have hzero : s.trajectory 0 (Fin.castSucc j) = (a₀ j : ℝ) := by
      rw [s.init_cond]
      simp [source, PolyPIVP.toPIVP]
    rw [← hzero]
    exact hbound 0 le_rfl j
  · intro r hr
    have hc := hasDerivAt_pi.mp (hy r hr)
    exact ((hc (pos j)).add (hc (neg j))).congr_deriv
      (field_sum G h a₀ z₀ (y r) j)
  · intro r hr
    exact add_nonneg (plus_nonneg (G j) (y r) (hnn r hr))
      (minus_nonneg (G j) (y r) (hnn r hr))
  · intro r hr
    change |decode (y r) j| ≤ M
    rw [hdec r hr]
    exact hbound r hr.1 j

/-- Global existence needs a bound only on the auxiliary coordinates.
The direct output may be unbounded as time tends to infinity. -/
theorem exists_lift
    (G : Fin d → MvPolynomial (Fin d) ℚ)
    (h : MvPolynomial (Fin d) ℚ)
    (a₀ : Fin d → ℚ) (z₀ : ℚ) (hz₀ : 0 ≤ z₀)
    (s : PIVP.Solution (source G h a₀ z₀).toPIVP)
    (M : ℝ)
    (hbound : ∀ t, 0 ≤ t → ∀ j,
      |s.trajectory t (Fin.castSucc j)| ≤ M) :
    ∃ sol : PIVP.Solution (compile G h a₀ z₀).toPIVP,
      Continuous sol.trajectory ∧
      (∀ t, 0 ≤ t → ∀ k, 0 ≤ sol.trajectory t k) ∧
      (∀ t, 0 ≤ t → decode (sol.trajectory t) =
        (fun j => s.trajectory t (Fin.castSucc j))) ∧
      (∀ t, 0 ≤ t → sol.trajectory t out = s.trajectory t (Fin.last d)) ∧
      (∀ t, 0 ≤ t → ∀ j, sol.trajectory t (pos j) + sol.trajectory t (neg j) ≤
        Real.sqrt (2 + M ^ 2)) := by
  obtain ⟨u⟩ := MaximalPIVP.exists_maximal (compile G h a₀ z₀)
  have htop : u.lifetime = ⊤ := by
    by_contra hfin
    let T := u.lifetime.toReal
    have hT : 0 < T := u.finite_time_pos hfin
    have hspec := local_spec G h a₀ z₀ hz₀ s M hbound T hT
      u.trajectory u.initial (u.ode_finite hfin)
    have hc : ContinuousOn (fun t => s.trajectory t (Fin.last d))
        (Set.Icc (0 : ℝ) T) := by
      intro t ht
      exact (hasDerivAt_pi.mp (s.is_solution t ht.1) (Fin.last d)).continuousAt.continuousWithinAt
    obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
    apply u.not_bddAbove_of_finite hfin
    refine ⟨max (Real.sqrt (2 + M ^ 2)) (max B 0), ?_⟩
    rintro _ ⟨t, ht, rfl⟩
    obtain ⟨hnn, _, hout, hsum⟩ := hspec t ht
    apply norm_le (u.trajectory t) (Real.sqrt_nonneg _) (le_max_right B 0)
      hnn hsum
    rw [hout, ← Real.norm_eq_abs]
    exact (hB t ⟨ht.1, ht.2.le⟩).trans (le_max_left B 0)
  obtain ⟨sol, hc, _⟩ :=
    (u.toForwardSolution.toGlobal htop).exists_continuous
  have hs : ∀ t, 0 ≤ t →
      (∀ k, 0 ≤ sol.trajectory t k) ∧
      decode (sol.trajectory t) = (fun j => s.trajectory t (Fin.castSucc j)) ∧
      sol.trajectory t out = s.trajectory t (Fin.last d) ∧
      (∀ j, sol.trajectory t (pos j) + sol.trajectory t (neg j) ≤
        Real.sqrt (2 + M ^ 2)) := by
    intro t ht
    exact local_spec G h a₀ z₀ hz₀ s M hbound (t + 1) (by linarith)
      sol.trajectory sol.init_cond
      (fun r hr => sol.is_solution r hr.1) t ⟨ht, by linarith⟩
  exact ⟨sol, hc, fun t ht => (hs t ht).1,
    fun t ht => (hs t ht).2.1,
    fun t ht => (hs t ht).2.2.1,
    fun t ht => (hs t ht).2.2.2⟩

/-- A1's general selective implementation, on the same physical time axis.
The bound is on each auxiliary pair sum; no bound on z is assumed. -/
theorem exists_solution
    (G : Fin d → MvPolynomial (Fin d) ℚ)
    (h : MvPolynomial (Fin d) ℚ)
    (a₀ : Fin d → ℚ) (z₀ : ℚ) (hz₀ : 0 ≤ z₀)
    (a : ℝ → Fin d → ℝ) (z : ℝ → ℝ)
    (ha₀ : a 0 = fun j => (a₀ j : ℝ))
    (hzinit : z 0 = (z₀ : ℝ))
    (ha : ∀ t, 0 ≤ t →
      HasDerivAt a (fun j => (G j).eval₂ (Rat.castHom ℝ) (a t)) t)
    (hz : ∀ t, 0 ≤ t →
      HasDerivAt z (z t * h.eval₂ (Rat.castHom ℝ) (a t)) t)
    (M : ℝ) (_hM : 0 ≤ M)
    (hbound : ∀ t, 0 ≤ t → ∀ j, |a t j| ≤ M) :
    ∃ sol : PIVP.Solution (compile G h a₀ z₀).toPIVP,
      Continuous sol.trajectory ∧
      (∀ t, 0 ≤ t → ∀ k, 0 ≤ sol.trajectory t k) ∧
      (∀ t, 0 ≤ t → decode (sol.trajectory t) = a t) ∧
      (∀ t, 0 ≤ t → sol.trajectory t out = z t) ∧
      (∀ t, 0 ≤ t → ∀ j, sol.trajectory t (pos j) + sol.trajectory t (neg j) ≤
        Real.sqrt (2 + M ^ 2)) := by
  let s := sourceSolution G h a₀ z₀ a z ha₀ hzinit ha hz
  have hsbound : ∀ t, 0 ≤ t → ∀ j,
      |s.trajectory t (Fin.castSucc j)| ≤ M := by
    intro t ht j
    simpa only [s, sourceSolution, Fin.snoc_castSucc] using hbound t ht j
  obtain ⟨sol, hc, hn, haeq, hzeq, hb⟩ :=
    exists_lift G h a₀ z₀ hz₀ s M hsbound
  refine ⟨sol, hc, hn, ?_, ?_, hb⟩
  · intro t ht
    simpa only [s, sourceSolution, Fin.snoc_castSucc] using haeq t ht
  · intro t ht
    simpa only [s, sourceSolution, Fin.snoc_last] using hzeq t ht

/-! ## Existence from the auxiliary trajectory alone -/

/-- The scalar source solution. Clamping the coefficient at negative time
only selects a continuous representative outside the forward domain. -/
def scalarOutput (h : MvPolynomial (Fin d) ℚ)
    (a : ℝ → Fin d → ℝ) (z₀ : ℚ) (t : ℝ) : ℝ :=
  (z₀ : ℝ) * Real.exp
    (∫ s in (0 : ℝ)..t, h.eval₂ (Rat.castHom ℝ) (a (max s 0)))

@[simp] theorem scalarOutput_initial
    (h : MvPolynomial (Fin d) ℚ) (a : ℝ → Fin d → ℝ) (z₀ : ℚ) :
    scalarOutput h a z₀ 0 = (z₀ : ℝ) := by
  simp [scalarOutput]

theorem scalarOutput_derivative
    (h : MvPolynomial (Fin d) ℚ)
    (a : ℝ → Fin d → ℝ) (z₀ : ℚ)
    (ha : ContinuousOn a (Set.Ici (0 : ℝ)))
    (t : ℝ) (ht : 0 ≤ t) :
    HasDerivAt (scalarOutput h a z₀)
      (scalarOutput h a z₀ t * h.eval₂ (Rat.castHom ℝ) (a t)) t := by
  let g : ℝ → ℝ := fun s => h.eval₂ (Rat.castHom ℝ) (a (max s 0))
  have hac : Continuous (fun s : ℝ => a (max s 0)) :=
    ha.comp_continuous (continuous_id.max continuous_const)
      (fun s => le_max_right s 0)
  have hgc : Continuous g := (mvPolynomial_eval₂_contDiff h).continuous.comp hac
  have hd := (hgc.integral_hasStrictDerivAt 0 t).hasDerivAt
  have he := (hd.exp).const_mul (z₀ : ℝ)
  apply he.congr_deriv
  simp only [scalarOutput, g, max_eq_left ht]
  ring

/-- Bounded global auxiliary dynamics alone suffice: the scalar equation
has an explicit global solution, which the selective CRN realizes. -/
theorem exists_solution_of_auxiliary
    (G : Fin d → MvPolynomial (Fin d) ℚ)
    (h : MvPolynomial (Fin d) ℚ)
    (a₀ : Fin d → ℚ) (z₀ : ℚ) (hz₀ : 0 ≤ z₀)
    (a : ℝ → Fin d → ℝ)
    (ha₀ : a 0 = fun j => (a₀ j : ℝ))
    (ha : ∀ t, 0 ≤ t →
      HasDerivAt a (fun j => (G j).eval₂ (Rat.castHom ℝ) (a t)) t)
    (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ t, 0 ≤ t → ∀ j, |a t j| ≤ M) :
    ∃ sol : PIVP.Solution (compile G h a₀ z₀).toPIVP,
      Continuous sol.trajectory ∧
      (∀ t, 0 ≤ t → ∀ k, 0 ≤ sol.trajectory t k) ∧
      (∀ t, 0 ≤ t → decode (sol.trajectory t) = a t) ∧
      (∀ t, 0 ≤ t → sol.trajectory t out = scalarOutput h a z₀ t) ∧
      (∀ t, 0 ≤ t → ∀ j, sol.trajectory t (pos j) + sol.trajectory t (neg j) ≤
        Real.sqrt (2 + M ^ 2)) := by
  have hac : ContinuousOn a (Set.Ici (0 : ℝ)) :=
    fun t ht => (ha t ht).continuousAt.continuousWithinAt
  exact exists_solution G h a₀ z₀ hz₀ a (scalarOutput h a z₀)
    ha₀ (scalarOutput_initial h a z₀) ha
    (scalarOutput_derivative h a z₀ hac) M hM hbound

/-- Any forward-time modulus transfers verbatim along the exact output
identity. The selective construction adds no readout or clock overhead. -/
theorem transfer_modulus
    {Z z : ℝ → ℝ} {α : ℝ} {μ : TimeModulus}
    (heq : ∀ t, 0 ≤ t → Z t = z t)
    (hμ : ∀ r t, 0 ≤ t → μ r < t →
      |z t - α| < Real.exp (-(r : ℝ))) :
    ∀ r t, 0 ≤ t → μ r < t →
      |Z t - α| < Real.exp (-(r : ℝ)) := by
  intro r t ht hrt
  rw [heq t ht]
  exact hμ r t ht hrt

/-- Polynomial uniqueness identifies every global selective solution on
the forward domain. -/
theorem solution_unique
    (G : Fin d → MvPolynomial (Fin d) ℚ)
    (h : MvPolynomial (Fin d) ℚ)
    (a₀ : Fin d → ℚ) (z₀ : ℚ)
    (u v : PIVP.Solution (compile G h a₀ z₀).toPIVP) :
    Set.EqOn u.trajectory v.trajectory (Set.Ici (0 : ℝ)) :=
  MaximalPIVP.global_solution_unique (compile G h a₀ z₀) u v

/-! ## Boundedness when the retained output is bounded -/

theorem bounded_of_output_bound
    (G : Fin d → MvPolynomial (Fin d) ℚ)
    (h : MvPolynomial (Fin d) ℚ)
    (a₀ : Fin d → ℚ) (z₀ : ℚ)
    (sol : PIVP.Solution (compile G h a₀ z₀).toPIVP)
    (M B : ℝ) (hB : 0 ≤ B)
    (hnn : ∀ t, 0 ≤ t → ∀ k, 0 ≤ sol.trajectory t k)
    (hsum : ∀ t, 0 ≤ t → ∀ j,
      sol.trajectory t (pos j) + sol.trajectory t (neg j) ≤
        Real.sqrt (2 + M ^ 2))
    (hout : ∀ t, 0 ≤ t → |sol.trajectory t out| ≤ B) :
    (compile G h a₀ z₀).toPIVP.IsBounded sol.trajectory := by
  have hR : 0 < Real.sqrt (2 + M ^ 2) :=
    Real.sqrt_pos.mpr (by positivity)
  exact ⟨max (Real.sqrt (2 + M ^ 2)) B,
    hR.trans_le (le_max_left _ _),
    fun t ht => norm_le (sol.trajectory t) hR.le hB
      (hnn t ht) (hsum t ht) (hout t ht)⟩

/-! ## Explicit initialization and overgeneralization counterexamples -/

theorem not_zero_init_of_output_ne_zero
    (G : Fin d → MvPolynomial (Fin d) ℚ)
    (h : MvPolynomial (Fin d) ℚ)
    (a₀ : Fin d → ℚ) (z₀ : ℚ) (hz₀ : z₀ ≠ 0) :
    ¬ (compile G h a₀ z₀).IsZeroInit := by
  intro hz
  apply hz₀
  simpa only [initial_out] using hz (out (d := d))

/-- G = h = 0, a(0) = 0, z(0) = 1 is already not all-zero initialized. -/
theorem constant_one_initial_not_zero :
    ¬ (compile (d := 1) (fun _ => 0) 0 (fun _ => 0) 1).IsZeroInit :=
  not_zero_init_of_output_ne_zero (d := 1) (fun _ => 0) 0 (fun _ => 0) 1 one_ne_zero

/-- The unrestricted general statement is false when z(0) is negative. -/
theorem negative_output_initial_obstruction :
    ¬ ∃ Z : ℝ → ℝ, (∀ t, 0 ≤ t → 0 ≤ Z t) ∧ Z 0 = -1 := by
  rintro ⟨Z, hZ, hz⟩
  have hh := hZ 0 le_rfl
  rw [hz] at hh
  norm_num at hh

theorem negative_initial_not_nonnegative :
    ¬ (∀ k, 0 ≤
      (compile (d := 1) (fun _ => 0) 0 (fun _ => 0) (-1)).init k) := by
  intro hn
  have hh : (0 : ℚ) ≤ -1 := by
    simpa only [initial_out] using hn (out (d := 1))
  norm_num at hh

/-- With a = 0 and z = 2 constant, the output exceeds the auxiliary bound. -/
theorem direct_output_can_exceed_rail_bound :
    Real.sqrt (2 + (0 : ℝ) ^ 2) < (2 : ℝ) := by
  have hs : (Real.sqrt (2 + (0 : ℝ) ^ 2)) ^ 2 = 2 := by
    simpa using
      (Real.sq_sqrt (show (0 : ℝ) ≤ 2 + (0 : ℝ) ^ 2 by norm_num))
  have hn := Real.sqrt_nonneg (2 + (0 : ℝ) ^ 2)
  nlinarith

theorem constant_two_initial_above_rail_bound :
    Real.sqrt (2 + (0 : ℝ) ^ 2) <
      ((compile (d := 1) (fun _ => 0) 0 (fun _ => 0) 2).init out : ℝ) := by
  simpa using direct_output_can_exceed_rail_bound

/-- For G = 0, h = 1, a = 0 and z(0) = 1, the scalar output is exp(t). -/
theorem scalarOutput_constant_one_coefficient (t : ℝ) :
    scalarOutput (d := 1) (MvPolynomial.C 1) (fun _ _ => 0) 1 t =
      Real.exp t := by
  simp [scalarOutput]

theorem exponential_output_not_bounded :
    ¬ ∃ B : ℝ, ∀ t : ℝ, 0 ≤ t → Real.exp t ≤ B := by
  rintro ⟨B, hB⟩
  have hh := hB (max B 0 + 1) (by positivity)
  have he := Real.add_one_le_exp (max B 0 + 1)
  linarith [le_max_left B 0]

/-! ## The actual power construction, with only its output retained -/

inductive PowerAuxSlot
  | filterValue | logValue | inverseValue
  deriving DecidableEq, Fintype

abbrev PowerAuxIndex (d₁ d₂ : ℕ) :=
  Fin d₁ ⊕ (Fin d₂ ⊕ PowerAuxSlot)

abbrev powerAuxDim (d₁ d₂ : ℕ) :=
  Fintype.card (PowerAuxIndex d₁ d₂)

def powerAuxEmbed {d₁ d₂ : ℕ} :
    PowerAuxIndex d₁ d₂ → PowIndex d₁ d₂
  | Sum.inl i => Sum.inl i
  | Sum.inr (Sum.inl j) => Sum.inr (Sum.inl j)
  | Sum.inr (Sum.inr PowerAuxSlot.filterValue) => Sum.inr (Sum.inr PowSlot.x1)
  | Sum.inr (Sum.inr PowerAuxSlot.logValue) => Sum.inr (Sum.inr PowSlot.u)
  | Sum.inr (Sum.inr PowerAuxSlot.inverseValue) => Sum.inr (Sum.inr PowSlot.v)

def powerAuxFilter {d₁ d₂ : ℕ}
    (Px : PolyPIVP d₁) : MvPolynomial (PowerAuxIndex d₁ d₂) ℚ :=
  X (Sum.inl Px.output) ^ 2 - 1 -
    X (Sum.inr (Sum.inr PowerAuxSlot.filterValue))

def powerAuxField {d₁ d₂ : ℕ}
    (Px : PolyPIVP d₁) (Py : PolyPIVP d₂) :
    PowerAuxIndex d₁ d₂ → MvPolynomial (PowerAuxIndex d₁ d₂) ℚ
  | Sum.inl i => rename Sum.inl (Px.field i)
  | Sum.inr (Sum.inl j) =>
      rename (fun k => Sum.inr (Sum.inl k)) (Py.field j)
  | Sum.inr (Sum.inr PowerAuxSlot.filterValue) => powerAuxFilter Px
  | Sum.inr (Sum.inr PowerAuxSlot.logValue) =>
      (1 - X (Sum.inr (Sum.inr PowerAuxSlot.inverseValue))) *
        powerAuxFilter Px
  | Sum.inr (Sum.inr PowerAuxSlot.inverseValue) =>
      (1 - X (Sum.inr (Sum.inr PowerAuxSlot.inverseValue))) ^ 2 *
        powerAuxFilter Px

def powerAuxMultiplier {d₁ d₂ : ℕ}
    (Px : PolyPIVP d₁) (Py : PolyPIVP d₂) :
    MvPolynomial (PowerAuxIndex d₁ d₂) ℚ :=
  C (1 / 2 : ℚ) *
    (rename (fun k => Sum.inr (Sum.inl k)) (Py.field Py.output) *
        X (Sum.inr (Sum.inr PowerAuxSlot.logValue)) +
      X (Sum.inr (Sum.inl Py.output)) *
        (1 - X (Sum.inr (Sum.inr PowerAuxSlot.inverseValue))) *
          powerAuxFilter Px)

def powerG {d₁ d₂ : ℕ}
    (Px : PolyPIVP d₁) (Py : PolyPIVP d₂) :
    Fin (powerAuxDim d₁ d₂) →
      MvPolynomial (Fin (powerAuxDim d₁ d₂)) ℚ :=
  fun j => rename (Fintype.equivFin (PowerAuxIndex d₁ d₂))
    (powerAuxField Px Py
      ((Fintype.equivFin (PowerAuxIndex d₁ d₂)).symm j))

def powerH {d₁ d₂ : ℕ}
    (Px : PolyPIVP d₁) (Py : PolyPIVP d₂) :
    MvPolynomial (Fin (powerAuxDim d₁ d₂)) ℚ :=
  rename (Fintype.equivFin (PowerAuxIndex d₁ d₂)) (powerAuxMultiplier Px Py)

def powerInitial {d₁ d₂ : ℕ}
    (Px : PolyPIVP d₁) (Py : PolyPIVP d₂) :
    Fin (powerAuxDim d₁ d₂) → ℚ :=
  fun j => powInit Px Py
    (powerAuxEmbed ((Fintype.equivFin (PowerAuxIndex d₁ d₂)).symm j))

def powerAuxCoordinate {d₁ d₂ : ℕ}
    (j : Fin (powerAuxDim d₁ d₂)) :
    Fin (Fintype.card (PowIndex d₁ d₂)) :=
  Fintype.equivFin (PowIndex d₁ d₂)
    (powerAuxEmbed ((Fintype.equivFin (PowerAuxIndex d₁ d₂)).symm j))

def powerAuxCurve {d₁ d₂ : ℕ}
    {Px : PolyPIVP d₁} {Py : PolyPIVP d₂}
    (s : PIVP.Solution (Px.powerSqCompile Py).toPIVP) :
    ℝ → Fin (powerAuxDim d₁ d₂) → ℝ :=
  fun t j => s.trajectory t (powerAuxCoordinate j)

theorem powerAuxDim_eq (d₁ d₂ : ℕ) :
    powerAuxDim d₁ d₂ = d₁ + (d₂ + 3) := by
  simp only [powerAuxDim, PowerAuxIndex, Fintype.card_sum, Fintype.card_fin]
  rfl

theorem power_dimension (d₁ d₂ : ℕ) :
    2 * powerAuxDim d₁ d₂ + 1 = 2 * (d₁ + d₂ + 3) + 1 := by
  rw [powerAuxDim_eq]
  omega

theorem powerAux_eval {d₁ d₂ : ℕ}
    (Px : PolyPIVP d₁) (Py : PolyPIVP d₂)
    (b : PowIndex d₁ d₂ → ℝ) (k : PowerAuxIndex d₁ d₂) :
    (powerAuxField Px Py k).eval₂ (Rat.castHom ℝ)
      (fun j => b (powerAuxEmbed j)) =
    (powField Px Py (powerAuxEmbed k)).eval₂ (Rat.castHom ℝ) b := by
  rcases k with i | j | k
  · rw [powerAuxField, powerAuxEmbed, powField, eval₂_rename, eval₂_rename]
    rfl
  · rw [powerAuxField, powerAuxEmbed, powField, eval₂_rename, eval₂_rename]
    rfl
  · cases k <;>
      simp [powerAuxField, powerAuxEmbed, powerAuxFilter, powField,
        powX1RHS, eval₂_mul, eval₂_sub, eval₂_pow, eval₂_X, eval₂_one]

theorem powerOutput_eval {d₁ d₂ : ℕ}
    (Px : PolyPIVP d₁) (Py : PolyPIVP d₂)
    (b : PowIndex d₁ d₂ → ℝ) :
    (powField Px Py (Sum.inr (Sum.inr PowSlot.z))).eval₂
        (Rat.castHom ℝ) b =
      b (Sum.inr (Sum.inr PowSlot.z)) *
        (powerAuxMultiplier Px Py).eval₂ (Rat.castHom ℝ)
          (fun j => b (powerAuxEmbed j)) := by
  simp only [powField, powerAuxMultiplier, powerAuxFilter, powX1RHS,
    eval₂_mul, eval₂_add, eval₂_sub, eval₂_pow, eval₂_X, eval₂_one,
    eval₂_C, eval₂_rename, Function.comp_def, powerAuxEmbed]
  ring

theorem powerCompiled_eval {d₁ d₂ : ℕ}
    (Px : PolyPIVP d₁) (Py : PolyPIVP d₂)
    (b : Fin (Fintype.card (PowIndex d₁ d₂)) → ℝ)
    (k : PowIndex d₁ d₂) :
    (Px.powerSqCompile Py).evalField b
        (Fintype.equivFin (PowIndex d₁ d₂) k) =
      (powField Px Py k).eval₂ (Rat.castHom ℝ)
        (fun j => b (Fintype.equivFin (PowIndex d₁ d₂) j)) := by
  simp [PolyPIVP.powerSqCompile, PolyPIVP.ofIndexed,
    PolyPIVP.evalField, eval₂_rename, Function.comp_def]

theorem powerAuxCurve_initial {d₁ d₂ : ℕ}
    (Px : PolyPIVP d₁) (Py : PolyPIVP d₂)
    (s : PIVP.Solution (Px.powerSqCompile Py).toPIVP) :
    powerAuxCurve s 0 = fun j => (powerInitial Px Py j : ℝ) := by
  funext j
  have hj := congrFun s.init_cond (powerAuxCoordinate j)
  simpa [powerAuxCurve, powerAuxCoordinate, powerInitial,
    PolyPIVP.powerSqCompile, PolyPIVP.ofIndexed, PolyPIVP.toPIVP] using hj

theorem powerOutput_initial {d₁ d₂ : ℕ}
    (Px : PolyPIVP d₁) (Py : PolyPIVP d₂)
    (s : PIVP.Solution (Px.powerSqCompile Py).toPIVP) :
    s.trajectory 0 (Px.powerSqCompile Py).output = 1 := by
  have hz := congrFun s.init_cond (Px.powerSqCompile Py).output
  simpa [PolyPIVP.powerSqCompile, PolyPIVP.ofIndexed,
    PolyPIVP.toPIVP, powInit] using hz

theorem powerAuxCurve_derivative {d₁ d₂ : ℕ}
    (Px : PolyPIVP d₁) (Py : PolyPIVP d₂)
    (s : PIVP.Solution (Px.powerSqCompile Py).toPIVP)
    {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (powerAuxCurve s)
      (fun j => (powerG Px Py j).eval₂ (Rat.castHom ℝ)
        (powerAuxCurve s t)) t := by
  refine hasDerivAt_pi.mpr fun j => ?_
  have hj := hasDerivAt_pi.mp (s.is_solution t ht) (powerAuxCoordinate j)
  change HasDerivAt (fun u => powerAuxCurve s u j)
    ((Px.powerSqCompile Py).evalField (s.trajectory t)
      (powerAuxCoordinate j)) t at hj
  refine hj.congr_deriv ?_
  have hvars :
      powerAuxCurve s t ∘ Fintype.equivFin (PowerAuxIndex d₁ d₂) =
        fun k => s.trajectory t
          (Fintype.equivFin (PowIndex d₁ d₂) (powerAuxEmbed k)) := by
    funext k
    simp only [Function.comp_apply, powerAuxCurve,
      powerAuxCoordinate, Equiv.symm_apply_apply]
  rw [powerG, eval₂_rename, hvars]
  change (Px.powerSqCompile Py).evalField (s.trajectory t)
      (Fintype.equivFin (PowIndex d₁ d₂)
        (powerAuxEmbed
          ((Fintype.equivFin (PowerAuxIndex d₁ d₂)).symm j))) =
    (powerAuxField Px Py
      ((Fintype.equivFin (PowerAuxIndex d₁ d₂)).symm j)).eval₂
        (Rat.castHom ℝ)
        (fun k => s.trajectory t
          (Fintype.equivFin (PowIndex d₁ d₂) (powerAuxEmbed k)))
  rw [powerCompiled_eval]
  exact (powerAux_eval Px Py
    (fun k => s.trajectory t (Fintype.equivFin (PowIndex d₁ d₂) k))
    ((Fintype.equivFin (PowerAuxIndex d₁ d₂)).symm j)).symm

theorem powerOutput_derivative {d₁ d₂ : ℕ}
    (Px : PolyPIVP d₁) (Py : PolyPIVP d₂)
    (s : PIVP.Solution (Px.powerSqCompile Py).toPIVP)
    {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (fun u => s.trajectory u (Px.powerSqCompile Py).output)
      (s.trajectory t (Px.powerSqCompile Py).output *
        (powerH Px Py).eval₂ (Rat.castHom ℝ) (powerAuxCurve s t)) t := by
  have hz := hasDerivAt_pi.mp (s.is_solution t ht) (Px.powerSqCompile Py).output
  refine hz.congr_deriv ?_
  change (Px.powerSqCompile Py).evalField (s.trajectory t)
      (Fintype.equivFin (PowIndex d₁ d₂) (Sum.inr (Sum.inr PowSlot.z))) =
    s.trajectory t
      (Fintype.equivFin (PowIndex d₁ d₂) (Sum.inr (Sum.inr PowSlot.z))) *
      (powerH Px Py).eval₂ (Rat.castHom ℝ) (powerAuxCurve s t)
  have hvars :
      powerAuxCurve s t ∘ Fintype.equivFin (PowerAuxIndex d₁ d₂) =
        fun k => s.trajectory t
          (Fintype.equivFin (PowIndex d₁ d₂) (powerAuxEmbed k)) := by
    funext k
    simp only [Function.comp_apply, powerAuxCurve,
      powerAuxCoordinate, Equiv.symm_apply_apply]
  rw [powerCompiled_eval, powerOutput_eval, powerH, eval₂_rename, hvars]

def powerCompile {d₁ d₂ : ℕ}
    (Px : PolyPIVP d₁) (Py : PolyPIVP d₂) :
    PolyPIVP (2 * powerAuxDim d₁ d₂ + 1) :=
  compile (powerG Px Py) (powerH Px Py) (powerInitial Px Py) 1

def powerCompile_decomposition {d₁ d₂ : ℕ}
    (Px : PolyPIVP d₁) (Py : PolyPIVP d₂) :
    PolyCRNDecomposition (2 * powerAuxDim d₁ d₂ + 1) (powerCompile Px Py) :=
  decomposition (powerG Px Py) (powerH Px Py)
    (powerInitial Px Py) 1 (by norm_num)

/-- A1's selective implementation of the actual power system. -/
theorem power_solution {d₁ d₂ : ℕ}
    (Px : PolyPIVP d₁) (Py : PolyPIVP d₂)
    (s : PIVP.Solution (Px.powerSqCompile Py).toPIVP)
    (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ t, 0 ≤ t → ‖s.trajectory t‖ ≤ M) :
    ∃ sol : PIVP.Solution (powerCompile Px Py).toPIVP,
      Continuous sol.trajectory ∧
      (∀ t, 0 ≤ t → ∀ k, 0 ≤ sol.trajectory t k) ∧
      (∀ t, 0 ≤ t → decode (sol.trajectory t) = powerAuxCurve s t) ∧
      (∀ t, 0 ≤ t → sol.trajectory t out =
        s.trajectory t (Px.powerSqCompile Py).output) ∧
      (∀ t, 0 ≤ t → ∀ j, sol.trajectory t (pos j) +
        sol.trajectory t (neg j) ≤ Real.sqrt (2 + M ^ 2)) := by
  exact exists_solution (powerG Px Py) (powerH Px Py)
    (powerInitial Px Py) 1 (by norm_num)
    (powerAuxCurve s) (fun t => s.trajectory t (Px.powerSqCompile Py).output)
    (powerAuxCurve_initial Px Py s)
    (by simpa using powerOutput_initial Px Py s)
    (fun t ht => powerAuxCurve_derivative Px Py s ht)
    (fun t ht => powerOutput_derivative Px Py s ht)
    M hM (fun t ht j =>
      (show |powerAuxCurve s t j| ≤ ‖s.trajectory t‖ by
        simpa only [powerAuxCurve, Real.norm_eq_abs] using
          norm_le_pi_norm (s.trajectory t) (powerAuxCoordinate j)).trans (hb t ht))

/-- The existing power-complexity bound, transferred without changing time.
The inner max with zero is already present in rpow_certified. -/
theorem rpow_selective {d₁ d₂ : ℕ} {α β : ℝ} (hα : 0 < α)
    (bα : CertifiedBoundedTimeComputable d₁ α)
    (bβ : CertifiedBoundedTimeComputable d₂ β) :
    ∃ (C : ℕ)
      (sol : PIVP.Solution (powerCompile bα.pivp bβ.pivp).toPIVP),
      Nonempty (PolyCRNDecomposition (2 * powerAuxDim d₁ d₂ + 1)
        (powerCompile bα.pivp bβ.pivp)) ∧
      Continuous sol.trajectory ∧
      (powerCompile bα.pivp bβ.pivp).toPIVP.IsBounded sol.trajectory ∧
      (∀ t, 0 ≤ t → ∀ k, 0 ≤ sol.trajectory t k) ∧
      (∀ r : ℕ, ∀ t : ℝ,
        t > max (max (bα.modulus (r + C)) 0 + r + C)
          (bβ.modulus (r + C)) →
        |sol.trajectory t out - α ^ β| < Real.exp (-(r : ℝ))) := by
  obtain ⟨C, b, hpin, hmod⟩ := rpow_certified hα bα bβ
  rcases b with ⟨P, s, μ, hb, hc, hconv⟩
  dsimp only at hpin hmod
  subst P
  obtain ⟨M, hM, hMb⟩ := hb
  obtain ⟨sol, hcont, hnonneg, _, hout, hsum⟩ :=
    power_solution bα.pivp bβ.pivp s M hM.le hMb
  have hbounded :
      (powerCompile bα.pivp bβ.pivp).toPIVP.IsBounded sol.trajectory := by
    refine ⟨max (Real.sqrt (2 + M ^ 2)) M,
      lt_of_lt_of_le hM (le_max_right _ _), ?_⟩
    intro t ht
    apply norm_le (sol.trajectory t) (Real.sqrt_nonneg _) hM.le
      (hnonneg t ht) (hsum t ht)
    rw [hout t ht]
    exact (show |s.trajectory t (bα.pivp.powerSqCompile bβ.pivp).output| ≤
        ‖s.trajectory t‖ by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm (s.trajectory t)
        (bα.pivp.powerSqCompile bβ.pivp).output).trans (hMb t ht)
  refine ⟨C, sol, ⟨powerCompile_decomposition bα.pivp bβ.pivp⟩,
    hcont, hbounded, hnonneg, ?_⟩
  intro r t ht
  have hbase : (0 : ℝ) ≤ max (bα.modulus (r + C)) 0 + r + C := by
    positivity
  have htforward : 0 ≤ t :=
    hbase.trans ((le_max_left _ _).trans ht.le)
  rw [hout t htforward]
  exact hconv r t ((hmod r).trans_lt ht)

theorem power_modulus_eq_of_nonneg (μa μb : TimeModulus)
    (hμa : ∀ r, 0 ≤ μa r) (C r : ℕ) :
    max (max (μa (r + C)) 0 + r + C) (μb (r + C)) =
      max (μa (r + C) + r + C) (μb (r + C)) := by
  rw [max_eq_left (hμa (r + C))]

/-- The journal's displayed modulus, for nonnegative upstream moduli. -/
theorem rpow_selective_nonnegative_moduli {d₁ d₂ : ℕ} {α β : ℝ}
    (hα : 0 < α)
    (bα : CertifiedBoundedTimeComputable d₁ α)
    (bβ : CertifiedBoundedTimeComputable d₂ β)
    (hμa : ∀ r, 0 ≤ bα.modulus r) :
    ∃ (C : ℕ)
      (sol : PIVP.Solution (powerCompile bα.pivp bβ.pivp).toPIVP),
      Nonempty (PolyCRNDecomposition (2 * powerAuxDim d₁ d₂ + 1)
        (powerCompile bα.pivp bβ.pivp)) ∧
      Continuous sol.trajectory ∧
      (powerCompile bα.pivp bβ.pivp).toPIVP.IsBounded sol.trajectory ∧
      (∀ t, 0 ≤ t → ∀ k, 0 ≤ sol.trajectory t k) ∧
      (∀ r : ℕ, ∀ t : ℝ,
        t > max (bα.modulus (r + C) + r + C) (bβ.modulus (r + C)) →
        |sol.trajectory t out - α ^ β| < Real.exp (-(r : ℝ))) := by
  obtain ⟨C, sol, hpcd, hcont, hbounded, hnonneg, hconv⟩ :=
    rpow_selective hα bα bβ
  refine ⟨C, sol, hpcd, hcont, hbounded, hnonneg, ?_⟩
  intro r t ht
  apply hconv r t
  simpa only [max_eq_left (hμa (r + C))] using ht

theorem powerCompile_not_all_zero {d₁ d₂ : ℕ}
    (Px : PolyPIVP d₁) (Py : PolyPIVP d₂) :
    ¬ (∀ k, (powerCompile Px Py).init k = 0) := by
  intro hz
  have hh := hz out
  change (compile (powerG Px Py) (powerH Px Py)
    (powerInitial Px Py) 1).init out = 0 at hh
  rw [initial_out] at hh
  norm_num at hh

end Ripple.SelectiveDualRail
