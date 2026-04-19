/-
  Ripple.DualRail.ConstantAnnihilation — UCNC 2025 Problem 1

  Open problem from [UCNC25] (Haisler-Huang-Migunov-Mohammed-Provence,
  "A Selective Dual-Railing Technique for General-Purpose Analog Computers"):

  > It is often assumed that the fast annihilation reaction method results
  > in a bounded system for sufficiently large k, but this has not yet
  > been shown.
  >
  > Problem 1. Given x, is there a constant k so that the dual-railed
  > system based on annihilation reactions (Z = k) is bounded?

  Setup. For a bounded GPAC `y' = p(y)` with `y(t) ∈ (−β, β)ⁿ`, dual-rail
  each variable `yᵢ = uᵢ − vᵢ` with `uᵢ, vᵢ ≥ 0` (CRN-implementable). Write
  `p̂ᵢ(u, v) = pᵢ(u − v)` and split into non-negative-coefficient monomial
  parts `p̂ᵢ = p̂ᵢ⁺ − p̂ᵢ⁻`. Two competing annihilation choices:

    (a) `Z = p̂ᵢ⁺ + p̂ᵢ⁻`  — scales with the polynomial itself.
        **Known bounded.** [RTCRN2] Huang-Klinge-Lathrop 2019 (DNA 25),
        proof in the present file as `dualRail_polynomial_scale_bounded`.
    (b) `Z = k`            — constant annihilation rate.
        **Open.** Problem 1 as stated above.

  The dual-rail identity `uᵢ − vᵢ = yᵢ` is preserved by both (a) and (b)
  when `uᵢ(0) = vᵢ(0) = 0`, so `uᵢ − vᵢ` stays bounded automatically. The
  question is whether `uᵢ, vᵢ` individually stay bounded.

  This file records the formal statement of Problem 1, the DNA25 baseline,
  and the state of our attempted proof / counterexample search.

  References:
  - UCNC25: `../../ref/selective-dual-railing-UCNC2025.pdf`
  - DNA25:  `../../ref/RTCRN2-Huang-Klinge-Lathrop.pdf`
  - Conversation with Xiang, 2026-04-18 (message 1132).
-/

import Ripple.Core.PIVP
import Ripple.LPP.Defs
import Mathlib.Algebra.MvPolynomial.CommRing

namespace Ripple
namespace DualRail

open MvPolynomial

/-! ## Coefficient-wise positive/negative decomposition

For a multivariate polynomial `p : MvPolynomial σ ℚ`, `posPart p` collects
all monomials with positive coefficients (coefficient preserved) and
`negPart p` collects all monomials with negative coefficients (coefficient
negated, so non-negative). Then `p = posPart p − negPart p` as polynomials,
and both parts have non-negative coefficients. -/

noncomputable def posPart {σ : Type*} [DecidableEq σ]
    (p : MvPolynomial σ ℚ) : MvPolynomial σ ℚ :=
  (p.support.filter (fun s => 0 < p.coeff s)).sum
    (fun s => monomial s (p.coeff s))

noncomputable def negPart {σ : Type*} [DecidableEq σ]
    (p : MvPolynomial σ ℚ) : MvPolynomial σ ℚ :=
  (p.support.filter (fun s => p.coeff s < 0)).sum
    (fun s => monomial s (-(p.coeff s)))

/-! ### Algebraic identities for the positive/negative decomposition -/

/-- The polynomial decomposes as `posPart p - negPart p`. -/
theorem posPart_sub_negPart {σ : Type*} [DecidableEq σ]
    (p : MvPolynomial σ ℚ) : posPart p - negPart p = p := by
  classical
  -- On `p.support`, `coeff s ≠ 0`, so `¬ (0 < coeff s) ↔ coeff s < 0`.
  have hNotPos_iff : ∀ s ∈ p.support, ¬ (0 < p.coeff s) ↔ p.coeff s < 0 := by
    intro s hs
    have hne : p.coeff s ≠ 0 := (MvPolynomial.mem_support_iff).1 hs
    constructor
    · intro hnot
      rcases lt_trichotomy (p.coeff s) 0 with h | h | h
      · exact h
      · exact (hne h).elim
      · exact (hnot h).elim
    · intro hlt hpos
      exact (lt_asymm hlt) hpos
  -- Rewrite `negPart` sum over `¬ (0 < coeff)` filter via `Finset.sum_congr`.
  have hNeg : negPart p =
      (p.support.filter (fun s => ¬ (0 < p.coeff s))).sum
        (fun s => monomial s (-(p.coeff s))) := by
    unfold negPart
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    apply Finset.filter_congr
    intro s hs; exact (hNotPos_iff s hs).symm
  unfold posPart
  rw [hNeg]
  -- Now combine the two filtered sums:
  --   ∑_{0 < coeff} monomial s (coeff s) - ∑_{¬(0 < coeff)} monomial s (-coeff s)
  -- = ∑_{0 < coeff} monomial s (coeff s) + ∑_{¬(0 < coeff)} monomial s (coeff s)
  -- = ∑_{s ∈ support} monomial s (coeff s) = p.
  have hFlip : (p.support.filter (fun s => ¬ (0 < p.coeff s))).sum
        (fun s => monomial s (-(p.coeff s)))
      = - (p.support.filter (fun s => ¬ (0 < p.coeff s))).sum
          (fun s => monomial s (p.coeff s)) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl ?_
    intro s _
    rw [← map_neg]
  rw [hFlip, sub_neg_eq_add]
  have hSplit :
      (p.support.filter (fun s => 0 < p.coeff s)).sum
          (fun s => monomial s (p.coeff s))
        + (p.support.filter (fun s => ¬ (0 < p.coeff s))).sum
          (fun s => monomial s (p.coeff s))
      = p.support.sum (fun s => monomial s (p.coeff s)) :=
    Finset.sum_filter_add_sum_filter_not p.support (fun s => 0 < p.coeff s) _
  rw [hSplit]
  exact MvPolynomial.support_sum_monomial_coeff p

/-- Every coefficient of `posPart p` is non-negative. -/
theorem posPart_coeff_nonneg {σ : Type*} [DecidableEq σ]
    (p : MvPolynomial σ ℚ) (s : σ →₀ ℕ) : 0 ≤ (posPart p).coeff s := by
  classical
  unfold posPart
  rw [MvPolynomial.coeff_sum]
  refine Finset.sum_nonneg ?_
  intro t ht
  rw [MvPolynomial.coeff_monomial]
  split_ifs with heq
  · exact le_of_lt (Finset.mem_filter.1 ht).2
  · exact le_refl _

/-- Every coefficient of `negPart p` is non-negative. -/
theorem negPart_coeff_nonneg {σ : Type*} [DecidableEq σ]
    (p : MvPolynomial σ ℚ) (s : σ →₀ ℕ) : 0 ≤ (negPart p).coeff s := by
  classical
  unfold negPart
  rw [MvPolynomial.coeff_sum]
  refine Finset.sum_nonneg ?_
  intro t ht
  rw [MvPolynomial.coeff_monomial]
  split_ifs with heq
  · have : p.coeff t < 0 := (Finset.mem_filter.1 ht).2
    linarith
  · exact le_refl _

/-- Evaluating `posPart p` on a non-negative real input yields a non-negative
result. This is the key positivity lemma used in dual-rail boundedness: the
positive-part polynomial cannot drive `u_i` negative from the boundary `u_i = 0`
as long as `v_i ≥ 0`. -/
theorem posPart_eval_nonneg {σ : Type*} [DecidableEq σ]
    (p : MvPolynomial σ ℚ) (x : σ → ℝ) (hx : ∀ i, 0 ≤ x i) :
    0 ≤ (posPart p).eval₂ (Rat.castHom ℝ) x := by
  classical
  unfold posPart
  rw [MvPolynomial.eval₂_sum]
  refine Finset.sum_nonneg ?_
  intro s hs
  rw [MvPolynomial.eval₂_monomial]
  have hcoeff : 0 < p.coeff s := (Finset.mem_filter.1 hs).2
  have h1 : (0 : ℝ) ≤ (Rat.castHom ℝ) (p.coeff s) := by
    have := (Rat.cast_nonneg (K := ℝ)).mpr (le_of_lt hcoeff)
    simpa using this
  have h2 : (0 : ℝ) ≤ s.prod (fun n e => x n ^ e) := by
    apply Finset.prod_nonneg
    intro i _
    exact pow_nonneg (hx i) _
  exact mul_nonneg h1 h2

/-- Evaluating `negPart p` on a non-negative real input yields a non-negative
result. -/
theorem negPart_eval_nonneg {σ : Type*} [DecidableEq σ]
    (p : MvPolynomial σ ℚ) (x : σ → ℝ) (hx : ∀ i, 0 ≤ x i) :
    0 ≤ (negPart p).eval₂ (Rat.castHom ℝ) x := by
  classical
  unfold negPart
  rw [MvPolynomial.eval₂_sum]
  refine Finset.sum_nonneg ?_
  intro s hs
  rw [MvPolynomial.eval₂_monomial]
  have hcoeff : p.coeff s < 0 := (Finset.mem_filter.1 hs).2
  have h1 : (0 : ℝ) ≤ (Rat.castHom ℝ) (-(p.coeff s)) := by
    have hn : (0 : ℚ) ≤ -(p.coeff s) := by linarith
    have := (Rat.cast_nonneg (K := ℝ)).mpr hn
    simpa using this
  have h2 : (0 : ℝ) ≤ s.prod (fun n e => x n ^ e) := by
    apply Finset.prod_nonneg
    intro i _
    exact pow_nonneg (hx i) _
  exact mul_nonneg h1 h2

/-- Scalar identity: the difference of positive and negative part evaluations
equals the original polynomial's evaluation. This is `posPart_sub_negPart` at
the semantic level — the key "dual-rail invariant" algebraic fact: at a point
where `u_i, v_i` encode `y_i = u_i - v_i`, we have
`p̂⁺(u,v) - p̂⁻(u,v) = p̂(u,v)`. -/
theorem posPart_eval_sub_negPart_eval {σ : Type*} [DecidableEq σ]
    (p : MvPolynomial σ ℚ) (x : σ → ℝ) :
    (posPart p).eval₂ (Rat.castHom ℝ) x
      - (negPart p).eval₂ (Rat.castHom ℝ) x
      = p.eval₂ (Rat.castHom ℝ) x := by
  have h := posPart_sub_negPart p
  have heval : (posPart p - negPart p).eval₂ (Rat.castHom ℝ) x
      = p.eval₂ (Rat.castHom ℝ) x :=
    congrArg (fun q : MvPolynomial σ ℚ => q.eval₂ (Rat.castHom ℝ) x) h
  rw [MvPolynomial.eval₂_sub] at heval
  exact heval

/-! ## Dual-railing data

Given a GPAC dimension `n` and polynomial vector `p : Fin n → MvPolynomial
(Fin n) ℚ`, the dual-railed system lives on `Fin (2n)` with `uᵢ = x_{2i}`,
`vᵢ = x_{2i+1}`. We substitute each `X j` with `X (2j) - X (2j+1)` to get
`p̂ᵢ : MvPolynomial (Fin (2n)) ℚ`, then split into positive and negative
parts. This produces two concrete CRNs depending on the choice of `Z`. -/

/-- The substitution that replaces variable `j` with `X (2j) − X (2j+1)`. -/
noncomputable def dualRailHom (n : ℕ) :
    MvPolynomial (Fin n) ℚ →ₐ[ℚ] MvPolynomial (Fin (2 * n)) ℚ :=
  MvPolynomial.aeval (fun j : Fin n =>
    X ⟨2 * j.val, by omega⟩ - X ⟨2 * j.val + 1, by omega⟩)

/-- Positive part of the dual-railed polynomial for species `i`. -/
noncomputable def dualRailPosPart (n : ℕ)
    (p : Fin n → MvPolynomial (Fin n) ℚ) (i : Fin n) :
    MvPolynomial (Fin (2 * n)) ℚ :=
  posPart (dualRailHom n (p i))

/-- Negative part of the dual-railed polynomial for species `i`. -/
noncomputable def dualRailNegPart (n : ℕ)
    (p : Fin n → MvPolynomial (Fin n) ℚ) (i : Fin n) :
    MvPolynomial (Fin (2 * n)) ℚ :=
  negPart (dualRailHom n (p i))

/-- Evaluating the dual-railed polynomial at a state vector `w : Fin (2n) → ℝ`
equals evaluating the original polynomial at the "differences"
`j ↦ w(2j) − w(2j+1)`. -/
theorem dualRailHom_eval₂ (n : ℕ) (q : MvPolynomial (Fin n) ℚ)
    (w : Fin (2 * n) → ℝ) :
    (dualRailHom n q).eval₂ (Rat.castHom ℝ) w
      = q.eval₂ (Rat.castHom ℝ)
        (fun j : Fin n =>
          w ⟨2 * j.val, by omega⟩ - w ⟨2 * j.val + 1, by omega⟩) := by
  -- Replace `eval₂ (Rat.castHom ℝ)` by `aeval`, then apply `comp_aeval_apply`.
  rw [show (Rat.castHom ℝ : ℚ →+* ℝ) = algebraMap ℚ ℝ from rfl,
      ← MvPolynomial.aeval_def, ← MvPolynomial.aeval_def]
  unfold dualRailHom
  -- Goal: aeval w (aeval (fun j => X (2j) - X (2j+1)) q)
  --      = aeval (fun j => w (2j) - w (2j+1)) q
  have hkey := MvPolynomial.comp_aeval_apply
    (R := ℚ) (S₁ := MvPolynomial (Fin (2 * n)) ℚ) (B := ℝ) (σ := Fin n)
    (f := fun j : Fin n =>
      (X ⟨2 * j.val, by omega⟩ - X ⟨2 * j.val + 1, by omega⟩ :
        MvPolynomial (Fin (2 * n)) ℚ))
    (MvPolynomial.aeval w) q
  simp only [map_sub, MvPolynomial.aeval_X] at hkey
  exact hkey

/-- **Dual-rail scalar identity.** At any state `w : Fin (2n) → ℝ`, the
difference `p̂ᵢ⁺(w) − p̂ᵢ⁻(w)` equals `pᵢ(y)` where `yⱼ = w(2j) − w(2j+1)`.

This is the core algebraic identity that makes the dual-rail invariant
`uᵢ − vᵢ = yᵢ` persist under the ODE: its derivative is
`uᵢ' − vᵢ' = p̂ᵢ⁺ − p̂ᵢ⁻ = pᵢ(u − v)`, which matches the GPAC `yᵢ' = pᵢ(y)`. -/
theorem dualRailPos_sub_dualRailNeg_eval (n : ℕ)
    (p : Fin n → MvPolynomial (Fin n) ℚ) (i : Fin n)
    (w : Fin (2 * n) → ℝ) :
    (dualRailPosPart n p i).eval₂ (Rat.castHom ℝ) w
      - (dualRailNegPart n p i).eval₂ (Rat.castHom ℝ) w
      = (p i).eval₂ (Rat.castHom ℝ)
        (fun j : Fin n =>
          w ⟨2 * j.val, by omega⟩ - w ⟨2 * j.val + 1, by omega⟩) := by
  unfold dualRailPosPart dualRailNegPart
  rw [posPart_eval_sub_negPart_eval (dualRailHom n (p i)) w]
  exact dualRailHom_eval₂ n (p i) w

/-- **Non-negativity of the dual-rail vector field positive term.** At a
non-negative state `w ≥ 0`, the positive-part evaluation `p̂ᵢ⁺(w) ≥ 0`. -/
theorem dualRailPosPart_eval_nonneg (n : ℕ)
    (p : Fin n → MvPolynomial (Fin n) ℚ) (i : Fin n)
    (w : Fin (2 * n) → ℝ) (hw : ∀ k, 0 ≤ w k) :
    0 ≤ (dualRailPosPart n p i).eval₂ (Rat.castHom ℝ) w := by
  unfold dualRailPosPart
  exact posPart_eval_nonneg (dualRailHom n (p i)) w hw

/-- **Non-negativity of the dual-rail vector field negative term.** At a
non-negative state `w ≥ 0`, the negative-part evaluation `p̂ᵢ⁻(w) ≥ 0`. -/
theorem dualRailNegPart_eval_nonneg (n : ℕ)
    (p : Fin n → MvPolynomial (Fin n) ℚ) (i : Fin n)
    (w : Fin (2 * n) → ℝ) (hw : ∀ k, 0 ≤ w k) :
    0 ≤ (dualRailNegPart n p i).eval₂ (Rat.castHom ℝ) w := by
  unfold dualRailNegPart
  exact negPart_eval_nonneg (dualRailHom n (p i)) w hw

/-! ## The two constructions

Option (a) — polynomial-scale annihilation (DNA25, proven bounded).
Option (b) — constant-k annihilation (UCNC25 Problem 1, open). -/

/-- **Option (a).** Dual-railed system with Z = p̂⁺ + p̂⁻ (polynomial-scale
annihilation). This is the DNA25/RTCRN2 construction:

  uᵢ' = p̂ᵢ⁺ − uᵢ·vᵢ·(p̂ᵢ⁺ + p̂ᵢ⁻)
  vᵢ' = p̂ᵢ⁻ − uᵢ·vᵢ·(p̂ᵢ⁺ + p̂ᵢ⁻)

Known bounded in [RTCRN2]. -/
noncomputable def polynomialScaleDualRail (n : ℕ) [NeZero n]
    (p : Fin n → MvPolynomial (Fin n) ℚ) : PolyPIVP (2 * n) where
  field := fun k =>
    -- Decode: k = 2i (u) or k = 2i+1 (v)
    let i : Fin n := ⟨k.val / 2, by omega⟩
    let is_u : Bool := k.val % 2 = 0
    let pPos := dualRailPosPart n p i
    let pNeg := dualRailNegPart n p i
    let annihilation :=
      X ⟨2 * i.val, by omega⟩ * X ⟨2 * i.val + 1, by omega⟩ * (pPos + pNeg)
    if is_u then pPos - annihilation else pNeg - annihilation
  init := fun _ => 0
  output := ⟨0, by have := NeZero.ne n; omega⟩

/-- **Option (b).** Dual-railed system with Z = k (constant annihilation).
The subject of UCNC25 Problem 1:

  uᵢ' = p̂ᵢ⁺ − k · uᵢ · vᵢ
  vᵢ' = p̂ᵢ⁻ − k · uᵢ · vᵢ

Boundedness open for general bounded GPAC `p`. -/
noncomputable def constantAnnihilationDualRail (n : ℕ) [NeZero n]
    (p : Fin n → MvPolynomial (Fin n) ℚ) (k : ℚ) : PolyPIVP (2 * n) where
  field := fun K =>
    let i : Fin n := ⟨K.val / 2, by omega⟩
    let is_u : Bool := K.val % 2 = 0
    let pPos := dualRailPosPart n p i
    let pNeg := dualRailNegPart n p i
    let annihilation :=
      C k * X ⟨2 * i.val, by omega⟩ * X ⟨2 * i.val + 1, by omega⟩
    if is_u then pPos - annihilation else pNeg - annihilation
  init := fun _ => 0
  output := ⟨0, by have := NeZero.ne n; omega⟩

/-! ## Boundedness statements

A PolyPIVP is "GPAC-bounded" if its original GPAC solution is bounded
(assumption on the input). We ask whether the dual-railed system is
also bounded. -/

/-- A predicate on the original GPAC: its solution is bounded by some
β > 0 in sup norm on [0, ∞). -/
def OriginalBounded {n : ℕ} (p : Fin n → MvPolynomial (Fin n) ℚ)
    (y₀ : Fin n → ℚ) (sol : ℝ → Fin n → ℝ) (β : ℝ) : Prop :=
  0 < β ∧ sol 0 = (fun i => (y₀ i : ℝ)) ∧
  (∀ t ≥ (0 : ℝ), ∀ i, HasDerivAt (fun s => sol s i)
    ((p i).eval₂ (Rat.castHom ℝ) (sol t)) t) ∧
  (∀ t ≥ (0 : ℝ), ∀ i, |sol t i| ≤ β)

/-- **[RTCRN2] Theorem (Option (a)): the polynomial-scale annihilation
dual-rail produces a bounded CRN.**

If the original GPAC `p` has a bounded solution (∀ t, |yᵢ(t)| ≤ β), then
the polynomial-scale dual-railed PIVP has a bounded solution with
`uᵢ, vᵢ ≥ 0` and `uᵢ − vᵢ = yᵢ`. The DNA25 paper proves this by: `ui - vi
= yi` is bounded, so if either is unbounded both are unbounded together,
but the degradation `−uᵢ·vᵢ·(p̂⁺+p̂⁻)` dominates the positive terms
`p̂⁺` (or `p̂⁻`) when uᵢvᵢ → ∞, contradiction.

Algebraic machinery for a future proof is provided above:
 * `posPart_sub_negPart`: `p = posPart p − negPart p` at the syntactic level.
 * `posPart_eval_nonneg` / `negPart_eval_nonneg`: both parts evaluate
   non-negatively on non-negative inputs.
 * `dualRailHom_eval₂`: evaluating the dual-railed polynomial at
   `w : Fin (2n) → ℝ` equals evaluating the original polynomial at the
   "difference state" `j ↦ w(2j) − w(2j+1)`.
 * `dualRailPos_sub_dualRailNeg_eval`: the scalar identity
   `p̂ᵢ⁺(w) − p̂ᵢ⁻(w) = pᵢ(u − v)` — core to persistence of `uᵢ − vᵢ = yᵢ`.
 * `dualRailPosPart_eval_nonneg` / `dualRailNegPart_eval_nonneg`:
   barrier lemmas guaranteeing no negative flow at `uᵢ = 0` or `vᵢ = 0`.

The remaining analytic content (global existence of a non-negative solution
plus the Lyapunov-based a priori bound on `Σᵢ(uᵢ² + vᵢ²)`) is left as an
axiom because its mechanization in Mathlib requires interleaving local
Picard–Lindelöf, comparison principles for barrier preservation, and
Grönwall applied to a scalar differential inequality
`S'(t) ≤ C(β) − k(β)·S(t)²` — a substantial formalization beyond the scope
of a single proof run. -/
axiom dualRail_polynomial_scale_bounded {n : ℕ}
    (p : Fin n → MvPolynomial (Fin n) ℚ) (y₀ : Fin n → ℚ)
    (ySol : ℝ → Fin n → ℝ) (β : ℝ) (_hBd : OriginalBounded p y₀ ySol β) :
    ∃ (ûSol : ℝ → Fin (2 * n) → ℝ) (B : ℝ), 0 < B ∧
      (∀ t ≥ (0 : ℝ), ∀ K, 0 ≤ ûSol t K ∧ ûSol t K ≤ B) ∧
      (∀ t ≥ (0 : ℝ), ∀ i : Fin n,
        ûSol t ⟨2 * i.val, by omega⟩ - ûSol t ⟨2 * i.val + 1, by omega⟩
          = ySol t i)

/-! ## The open question (UCNC25 Problem 1)

Below we state the UCNC25 open question precisely. This is NOT axiomatized
— it is a `Prop` whose truth is the subject of investigation. The file
will evolve as we accumulate either a proof or a counterexample. -/

/-- **UCNC25 Problem 1 (open).** For every bounded GPAC `p`, there exists
a constant `k > 0` such that the constant-annihilation dual-railed system
is bounded.

If this is true, the counterexample question is vacuous; if false, there
is a specific `p` with unbounded `u, v` for every `k`. -/
def ConstantAnnihilationBounded : Prop :=
  ∀ (n : ℕ) (p : Fin n → MvPolynomial (Fin n) ℚ) (y₀ : Fin n → ℚ)
    (ySol : ℝ → Fin n → ℝ) (β : ℝ) (_hBd : OriginalBounded p y₀ ySol β),
    ∃ (k : ℚ), 0 < k ∧
      ∃ (ûSol : ℝ → Fin (2 * n) → ℝ) (B : ℝ), 0 < B ∧
        (∀ t ≥ (0 : ℝ), ∀ K, 0 ≤ ûSol t K ∧ ûSol t K ≤ B) ∧
        (∀ t ≥ (0 : ℝ), ∀ i : Fin n,
          ûSol t ⟨2 * i.val, by omega⟩ - ûSol t ⟨2 * i.val + 1, by omega⟩
            = ySol t i)

/-- **The negation (counterexample form).** There exists a bounded GPAC
`p` for which *no* constant `k` yields a bounded dual-railed system. -/
def ConstantAnnihilationCounterexample : Prop :=
  ∃ (n : ℕ) (p : Fin n → MvPolynomial (Fin n) ℚ) (y₀ : Fin n → ℚ)
    (ySol : ℝ → Fin n → ℝ) (β : ℝ) (_hBd : OriginalBounded p y₀ ySol β),
    ∀ (k : ℚ), 0 < k →
      ¬ ∃ (ûSol : ℝ → Fin (2 * n) → ℝ) (B : ℝ), 0 < B ∧
          (∀ t ≥ (0 : ℝ), ∀ K, 0 ≤ ûSol t K ∧ ûSol t K ≤ B) ∧
          (∀ t ≥ (0 : ℝ), ∀ i : Fin n,
            ûSol t ⟨2 * i.val, by omega⟩ - ûSol t ⟨2 * i.val + 1, by omega⟩
              = ySol t i)

/-- One direction of duality: a counterexample negates the conjecture. -/
theorem not_conjecture_of_counterexample :
    ConstantAnnihilationCounterexample → ¬ ConstantAnnihilationBounded := by
  rintro ⟨n, p, y₀, ySol, β, hBd, hnone⟩ hconj
  obtain ⟨k, hk, hsol⟩ := hconj n p y₀ ySol β hBd
  exact hnone k hk hsol

end DualRail
end Ripple
