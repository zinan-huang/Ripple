/-
Ripple.BoundedUniversality.HenonSelector.Cylinder
------------------------------
Symbolic and geometric Markov cylinders, and the bridge theorem
connecting symbolic cylinder hitting to geometric Hénon cylinder hitting.

F6: Finite Hénon Markov cylinders are Q-semialgebraic.
-/

import Ripple.BoundedUniversality.HenonSelector.Selector
import Ripple.BoundedUniversality.HenonSelector.Markov

namespace Ripple.BoundedUniversality.HenonSelector

/-- Symbolic cylinder: the set of bi-infinite sequences whose initial
segment matches the finite word w. -/
def SymbolicCylinder (w : MarkovCylinderCode) : Set BinSeq :=
  { s | ∀ i : Fin w.length, s (i : ℤ) = w.get i }

/-- Geometric Markov cylinder: the set of points whose first |w|
iterates under henon91 lie in the corresponding Markov strips. -/
def GeometricCylinder (w : MarkovCylinderCode) : Set Point2 :=
  { p | ∀ i : Fin w.length, strip (w.get i) (Nat.iterate henon91 (i : ℕ) p) }

/-- The coding map sends symbolic cylinders to geometric cylinders. -/
private theorem strip_iff_symbol (hc : HenonCoding) (b : Bool) (s : BinSeq) :
    strip b (hc.omega s) ↔ s 0 = b := by
  cases b
  · -- b = false
    simp only [strip, ite_false, D₀, and_iff_right (hc.omega_in_dpre s)]
    exact (hc.symbol_zero s).symm
  · -- b = true
    simp only [strip, ite_true, D₁, and_iff_right (hc.omega_in_dpre s)]
    exact (hc.symbol_one s).symm

theorem omega_mem_geometric_iff
    (hc : HenonCoding) (s : BinSeq) (w : MarkovCylinderCode) :
    hc.omega s ∈ GeometricCylinder w ↔ s ∈ SymbolicCylinder w := by
  simp only [GeometricCylinder, SymbolicCylinder, Set.mem_setOf_eq]
  constructor
  · intro h i
    have hiter := h i
    rw [conjugacy_iter hc (i : ℕ) s] at hiter
    rw [strip_iff_symbol hc] at hiter
    rw [shift_iter_apply s (i : ℕ) 0] at hiter
    simpa using hiter
  · intro h i
    rw [conjugacy_iter hc (i : ℕ) s]
    rw [strip_iff_symbol hc]
    rw [shift_iter_apply s (i : ℕ) 0]
    simpa using h i

/-- Symbolic cylinder hitting via shift iterates corresponds to
geometric cylinder hitting via henon91 iterates. -/
theorem omega_hits_cylinder_iff
    (hc : HenonCoding) (s : BinSeq) (w : MarkovCylinderCode) :
    HitsCylinder s w ↔
      ∃ t : ℕ, Nat.iterate henon91 t (hc.omega s) ∈ GeometricCylinder w := by
  unfold HitsCylinder
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨t, ?_⟩
    rw [conjugacy_iter hc t s]
    exact (omega_mem_geometric_iff hc (Nat.iterate shift t s) w).mpr ht
  · rintro ⟨t, ht⟩
    refine ⟨t, ?_⟩
    rw [conjugacy_iter hc t s] at ht
    exact (omega_mem_geometric_iff hc (Nat.iterate shift t s) w).mp ht

-- henon91 polynomial components (needed before dpre/strip proofs)
noncomputable def henon91_poly_fst' : MvPolynomial (Fin 2) ℚ :=
  MvPolynomial.X ⟨0, by omega⟩ ^ 2 - 9 - MvPolynomial.X ⟨1, by omega⟩
noncomputable def henon91_poly_snd' : MvPolynomial (Fin 2) ℚ :=
  MvPolynomial.X ⟨0, by omega⟩
theorem henon91_is_qpoly' :
    ∃ p q : MvPolynomial (Fin 2) ℚ,
      ∀ x : ℝ × ℝ, henon91 x = (qeval p (point2ToPoint x),
                                   qeval q (point2ToPoint x)) := by
  refine ⟨henon91_poly_fst', henon91_poly_snd', fun ⟨x₁, x₂⟩ => ?_⟩
  simp only [henon91, henon, henon91_poly_fst', henon91_poly_snd', qeval, point2ToPoint,
    MvPolynomial.eval₂_sub, MvPolynomial.eval₂_pow, MvPolynomial.eval₂_X,
    MvPolynomial.eval₂_C, map_ofNat, Prod.fst, Prod.snd]
  ext <;> simp [ite_true, ite_false] <;> ring

private theorem dpre_isQSemialgebraicPair :
    IsQSemialgebraicPair { p : Point2 | Dpre p } := by
  -- Dpre p = D p ∧ D (henon91 p)
  -- D is Q-semialgebraic, henon91 is Q-polynomial, preimage preserves Q-semialg
  have hD := D_isQSemialgebraicPair
  have hD_pre := hD.preimage_poly henon91 henon91_is_qpoly'
  -- {p | Dpre p} = {p | D p} ∩ {p | D (henon91 p)} = {p | D p} ∩ henon91⁻¹'{p | D p}
  have : { p : Point2 | Dpre p } = { p | D p } ∩ (henon91 ⁻¹' { p | D p }) := by
    ext p; simp [Dpre]
  rw [this]
  exact hD.inter hD_pre

private theorem strip_isQSemialgebraicPair (b : Bool) :
    IsQSemialgebraicPair { p : Point2 | strip b p } := by
  cases b
  · -- b = false: D₀ p = Dpre p ∧ p.1 < 0
    have : { p : Point2 | strip false p } = { p | Dpre p } ∩ { p : Point2 | p.1 < 0 } := by
      ext p; simp [strip, D₀]
    rw [this]
    apply IsQSemialgebraicPair.inter dpre_isQSemialgebraicPair
    -- {p | p.1 < 0} is Q-semialgebraic: complement of {p | -p.1 ≤ 0} (i.e. p.1 ≥ 0)
    have : { p : Point2 | p.1 < 0 } =
        { p : Point2 | ¬ (0 ≤ p.1) } := by ext p; simp [not_le]
    rw [this]
    have hge : IsQSemialgebraicPair { p : Point2 | 0 ≤ p.1 } := by
      refine ⟨.atom (.le (-(MvPolynomial.X ⟨0, by omega⟩))), ?_⟩
      ext ⟨x₁, x₂⟩
      simp [QSemialgFormula.Realize, qeval, point2ToPoint, MvPolynomial.eval₂_neg,
        MvPolynomial.eval₂_X, ite_true]
    have : { p : Point2 | ¬ (0 ≤ p.1) } = { p : Point2 | 0 ≤ p.1 }ᶜ := by
      ext p; simp
    rw [this]
    exact hge.compl
  · -- b = true: D₁ p = Dpre p ∧ 0 < p.1
    have : { p : Point2 | strip true p } = { p | Dpre p } ∩ { p : Point2 | 0 < p.1 } := by
      ext p; simp [strip, D₁]
    rw [this]
    apply IsQSemialgebraicPair.inter dpre_isQSemialgebraicPair
    -- {p | 0 < p.1} = complement of {p | p.1 ≤ 0}
    have : { p : Point2 | 0 < p.1 } =
        { p : Point2 | ¬ (p.1 ≤ 0) } := by ext p; simp [not_le]
    rw [this]
    have hle : IsQSemialgebraicPair { p : Point2 | p.1 ≤ 0 } := by
      refine ⟨.atom (.le (MvPolynomial.X ⟨0, by omega⟩)), ?_⟩
      ext ⟨x₁, x₂⟩
      simp [QSemialgFormula.Realize, qeval, point2ToPoint, MvPolynomial.eval₂_X, ite_true]
    have : { p : Point2 | ¬ (p.1 ≤ 0) } = { p : Point2 | p.1 ≤ 0 }ᶜ := by
      ext p; simp
    rw [this]
    exact hle.compl

/-- henon91 is a Q-polynomial map (components are polynomials with rational coefficients). -/
noncomputable def henon91_poly_fst : MvPolynomial (Fin 2) ℚ :=
  MvPolynomial.X ⟨0, by omega⟩ ^ 2 - 9 - MvPolynomial.X ⟨1, by omega⟩

noncomputable def henon91_poly_snd : MvPolynomial (Fin 2) ℚ :=
  MvPolynomial.X ⟨0, by omega⟩

theorem henon91_is_qpoly :
    ∃ p q : MvPolynomial (Fin 2) ℚ,
      ∀ x : ℝ × ℝ, henon91 x = (qeval p (point2ToPoint x),
                                   qeval q (point2ToPoint x)) := by
  refine ⟨henon91_poly_fst, henon91_poly_snd, fun ⟨x₁, x₂⟩ => ?_⟩
  simp only [henon91, henon, henon91_poly_fst, henon91_poly_snd, qeval, point2ToPoint,
    MvPolynomial.eval₂_sub, MvPolynomial.eval₂_pow, MvPolynomial.eval₂_X,
    MvPolynomial.eval₂_C, map_ofNat, Prod.fst, Prod.snd]
  ext <;> simp [ite_true, ite_false] <;> ring

/-- henon91^[k] is a Q-polynomial map (composition of Q-polynomial maps). -/
private theorem henon91_iter_is_qpoly (k : ℕ) :
    ∃ p q : MvPolynomial (Fin 2) ℚ,
      ∀ x : ℝ × ℝ, Nat.iterate henon91 k x =
        (qeval p (point2ToPoint x), qeval q (point2ToPoint x)) := by
  induction k with
  | zero =>
    refine ⟨MvPolynomial.X ⟨0, by omega⟩, MvPolynomial.X ⟨1, by omega⟩, fun ⟨x₁, x₂⟩ => ?_⟩
    simp [qeval, point2ToPoint, MvPolynomial.eval₂_X, ite_true, ite_false]
  | succ k ih =>
    obtain ⟨pk, qk, hk⟩ := ih
    let σ : Fin 2 → MvPolynomial (Fin 2) ℚ := fun i =>
      if i = 0 then pk else qk
    refine ⟨MvPolynomial.aeval σ henon91_poly_fst,
            MvPolynomial.aeval σ henon91_poly_snd, fun x => ?_⟩
    have hcomp : ∀ (r : MvPolynomial (Fin 2) ℚ),
        qeval (MvPolynomial.aeval σ r) (point2ToPoint x) =
        qeval r (fun i => qeval (σ i) (point2ToPoint x)) := by
      intro r
      simp only [qeval]
      have haeval : MvPolynomial.aeval σ r = MvPolynomial.bind₁ σ r := by
        rw [MvPolynomial.aeval_eq_bind₁]
      rw [haeval]
      have := MvPolynomial.eval₂Hom_bind₁ (algebraMap ℚ ℝ) (point2ToPoint x) σ r
      simp only [MvPolynomial.coe_eval₂Hom] at this
      exact this
    -- The proof is: henon91^[k+1] x = henon91 (henon91^[k] x) = henon91 (qeval pk pt, qeval qk pt)
    -- = ((qeval pk pt)^2 - 9 - qeval qk pt, qeval pk pt)
    -- = (qeval (aeval σ fst) pt, qeval (aeval σ snd) pt)
    -- We build this as a chain of equalities using exact/trans.
    exact (Function.iterate_succ_apply' henon91 k x).symm ▸
      (hk x).symm ▸ by
        simp only [henon91, henon, Prod.fst, Prod.snd]
        ext
        · simp only [Prod.fst]; rw [hcomp]
          simp [henon91_poly_fst, qeval, σ, MvPolynomial.eval₂_sub, MvPolynomial.eval₂_pow,
            MvPolynomial.eval₂_X, MvPolynomial.eval₂_C, map_ofNat, ite_true, ite_false]
        · simp only [Prod.snd]; rw [hcomp]
          simp [henon91_poly_snd, qeval, σ, MvPolynomial.eval₂_X, ite_true]

/-- Each individual strip preimage {p | strip b (henon91^[k] p)} is Q-semialgebraic. -/
private theorem strip_preimage_iter_isQSemialgebraicPair (b : Bool) (k : ℕ) :
    IsQSemialgebraicPair { p : Point2 | strip b (Nat.iterate henon91 k p) } := by
  exact (strip_isQSemialgebraicPair b).preimage_poly
    (Nat.iterate henon91 k) (henon91_iter_is_qpoly k)

theorem geometricCylinder_isQSemialgebraicPair (w : MarkovCylinderCode) :
    IsQSemialgebraicPair (GeometricCylinder w) := by
  -- Prove by induction on the length of w
  induction w with
  | nil =>
    -- Empty word: GeometricCylinder [] = Set.univ
    have : GeometricCylinder [] = Set.univ := by
      ext p; simp [GeometricCylinder]
    rw [this]
    exact ⟨.neg (.conj (.atom (.le 0)) (.neg (.atom (.le 0)))),
           by ext p; simp [QSemialgFormula.Realize, qeval, MvPolynomial.eval₂_C]⟩
  | cons b w ih =>
    -- GeometricCylinder (b::w) = {p | strip b p} ∩ henon91⁻¹'(GeometricCylinder w)
    have hsplit : GeometricCylinder (b :: w) =
        { p | strip b p } ∩ (henon91 ⁻¹' GeometricCylinder w) := by
      ext p
      simp only [GeometricCylinder, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage]
      constructor
      · intro h
        refine ⟨by simpa using h ⟨0, by simp⟩, fun i => ?_⟩
        have := h ⟨i.val + 1, by simp⟩
        simp only [List.get_cons_succ] at this
        simpa [Function.iterate_succ_apply] using this
      · rintro ⟨h0, hw⟩ ⟨i, hi⟩
        match i with
        | 0 => simpa using h0
        | i + 1 =>
          have := hw ⟨i, by simp at hi; omega⟩
          simp only [List.get_cons_succ]
          simpa [Function.iterate_succ_apply] using this
    rw [hsplit]
    exact (strip_preimage_iter_isQSemialgebraicPair b 0).inter
      (ih.preimage_poly henon91 henon91_is_qpoly')

end Ripple.BoundedUniversality.HenonSelector
