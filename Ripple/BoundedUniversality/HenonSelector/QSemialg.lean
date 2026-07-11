/-
Ripple.BoundedUniversality.HenonSelector.QSemialg
------------------------------
Syntactic Q-semialgebraic formula framework. Defines quantifier-free
formulas built from Q-polynomial inequalities/equations, with closure
under Boolean operations and polynomial preimage.

Claim C (Tarski-Seidenberg: Q-semialgebraic singleton ⇒ Q-algebraic
coordinates) is axiomatized.
-/

import Mathlib

namespace Ripple.BoundedUniversality.HenonSelector

abbrev Point (n : ℕ) := Fin n → ℝ

inductive QPolyRel (n : ℕ) where
  | le : MvPolynomial (Fin n) ℚ → QPolyRel n
  | eq : MvPolynomial (Fin n) ℚ → QPolyRel n

inductive QSemialgFormula (n : ℕ) where
  | atom : QPolyRel n → QSemialgFormula n
  | neg  : QSemialgFormula n → QSemialgFormula n
  | conj : QSemialgFormula n → QSemialgFormula n → QSemialgFormula n
  | disj : QSemialgFormula n → QSemialgFormula n → QSemialgFormula n

noncomputable def qeval {n : ℕ}
    (p : MvPolynomial (Fin n) ℚ) (x : Point n) : ℝ :=
  MvPolynomial.eval₂ (algebraMap ℚ ℝ) x p

def QSemialgFormula.Realize {n : ℕ} :
    QSemialgFormula n → Point n → Prop
  | .atom (.le p), x => qeval p x ≤ 0
  | .atom (.eq p), x => qeval p x = 0
  | .neg ψ, x        => ¬ ψ.Realize x
  | .conj ψ χ, x     => ψ.Realize x ∧ χ.Realize x
  | .disj ψ χ, x     => ψ.Realize x ∨ χ.Realize x

def IsQSemialgebraic {n : ℕ} (S : Set (Point n)) : Prop :=
  ∃ φ : QSemialgFormula n, S = { x | φ.Realize x }

theorem IsQSemialgebraic.compl {n : ℕ} {S : Set (Point n)}
    (hS : IsQSemialgebraic S) : IsQSemialgebraic Sᶜ := by
  obtain ⟨φ, hφ⟩ := hS
  exact ⟨.neg φ, by ext x; simp [hφ, Set.mem_compl_iff, QSemialgFormula.Realize]⟩

theorem IsQSemialgebraic.inter {n : ℕ} {S T : Set (Point n)}
    (hS : IsQSemialgebraic S) (hT : IsQSemialgebraic T) :
    IsQSemialgebraic (S ∩ T) := by
  obtain ⟨φ, hφ⟩ := hS
  obtain ⟨ψ, hψ⟩ := hT
  exact ⟨.conj φ ψ, by ext x; simp [hφ, hψ, QSemialgFormula.Realize]⟩

theorem IsQSemialgebraic.union {n : ℕ} {S T : Set (Point n)}
    (hS : IsQSemialgebraic S) (hT : IsQSemialgebraic T) :
    IsQSemialgebraic (S ∪ T) := by
  obtain ⟨φ, hφ⟩ := hS
  obtain ⟨ψ, hψ⟩ := hT
  exact ⟨.disj φ ψ, by ext x; simp [hφ, hψ, QSemialgFormula.Realize]⟩

def point2ToPoint (p : ℝ × ℝ) : Point 2 :=
  fun i => if i = 0 then p.1 else p.2

def IsQSemialgebraicPair (S : Set (ℝ × ℝ)) : Prop :=
  ∃ φ : QSemialgFormula 2, S = { p | φ.Realize (point2ToPoint p) }

theorem IsQSemialgebraicPair.compl {S : Set (ℝ × ℝ)}
    (hS : IsQSemialgebraicPair S) : IsQSemialgebraicPair Sᶜ := by
  obtain ⟨φ, hφ⟩ := hS
  exact ⟨.neg φ, by ext x; simp [hφ, QSemialgFormula.Realize]⟩

theorem IsQSemialgebraicPair.inter {S T : Set (ℝ × ℝ)}
    (hS : IsQSemialgebraicPair S) (hT : IsQSemialgebraicPair T) :
    IsQSemialgebraicPair (S ∩ T) := by
  obtain ⟨φ, hφ⟩ := hS
  obtain ⟨ψ, hψ⟩ := hT
  exact ⟨.conj φ ψ, by ext x; simp [hφ, hψ, QSemialgFormula.Realize]⟩

/-- Substitute polynomial components into a formula. -/
noncomputable def QSemialgFormula.subst {n : ℕ}
    (σ : Fin n → MvPolynomial (Fin n) ℚ) :
    QSemialgFormula n → QSemialgFormula n
  | .atom (.le p) => .atom (.le (MvPolynomial.aeval σ p))
  | .atom (.eq p) => .atom (.eq (MvPolynomial.aeval σ p))
  | .neg ψ        => .neg (ψ.subst σ)
  | .conj ψ χ     => .conj (ψ.subst σ) (χ.subst σ)
  | .disj ψ χ     => .disj (ψ.subst σ) (χ.subst σ)

private theorem qeval_aeval_eq {n : ℕ}
    (σ : Fin n → MvPolynomial (Fin n) ℚ)
    (p : MvPolynomial (Fin n) ℚ) (x : Point n) :
    qeval (MvPolynomial.aeval σ p) x =
    qeval p (fun i => qeval (σ i) x) := by
  simp only [qeval]
  rw [MvPolynomial.aeval_eq_bind₁]
  have := MvPolynomial.eval₂Hom_bind₁ (algebraMap ℚ ℝ) x σ p
  simp only [MvPolynomial.coe_eval₂Hom] at this
  exact this

theorem QSemialgFormula.realize_subst {n : ℕ}
    (σ : Fin n → MvPolynomial (Fin n) ℚ) (φ : QSemialgFormula n) (x : Point n) :
    (φ.subst σ).Realize x ↔ φ.Realize (fun i => qeval (σ i) x) := by
  induction φ with
  | atom r =>
    cases r with
    | le p => simp only [subst, Realize, qeval_aeval_eq]
    | eq p => simp only [subst, Realize, qeval_aeval_eq]
  | neg ψ ih =>
    simp only [subst, Realize]
    exact Iff.not ih
  | conj ψ χ ihψ ihχ =>
    simp only [subst, Realize]
    exact Iff.and ihψ ihχ
  | disj ψ χ ihψ ihχ =>
    simp only [subst, Realize]
    exact Iff.or ihψ ihχ

theorem IsQSemialgebraicPair.preimage_poly
    {S : Set (ℝ × ℝ)}
    (hS : IsQSemialgebraicPair S)
    (f : ℝ × ℝ → ℝ × ℝ)
    (hf : ∃ p q : MvPolynomial (Fin 2) ℚ,
      ∀ x : ℝ × ℝ, f x = (qeval p (point2ToPoint x),
                             qeval q (point2ToPoint x))) :
    IsQSemialgebraicPair (f ⁻¹' S) := by
  obtain ⟨φ, hφ⟩ := hS
  obtain ⟨p_f, q_f, hfx⟩ := hf
  let σ : Fin 2 → MvPolynomial (Fin 2) ℚ := fun i => if i = 0 then p_f else q_f
  refine ⟨φ.subst σ, ?_⟩
  ext x
  simp only [Set.mem_preimage, Set.mem_setOf_eq, hφ]
  constructor
  · intro h
    rw [QSemialgFormula.realize_subst]
    convert h using 1
    ext i; simp only [σ, point2ToPoint, hfx x]; split <;> simp_all
  · intro h
    rw [QSemialgFormula.realize_subst] at h
    convert h using 1
    ext i; simp only [σ, point2ToPoint, hfx x]; split <;> simp_all

-- Claim C (Tarski-Seidenberg: Q-semialgebraic singleton ⇒ algebraic
-- coordinates) is mathematically true but not used in the current
-- theorem chain. It would be needed if the formalization extended to
-- proving specific Hénon horseshoe points are algebraic from their
-- semialgebraic characterization. Removed from the axiom ledger since
-- #print axioms should only show assumptions that are actually used.

end Ripple.BoundedUniversality.HenonSelector
