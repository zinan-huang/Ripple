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

/-! ### Coefficient specification for posPart / negPart

We give the coefficient `(posPart p).coeff t` directly in terms of
`p.coeff t`. This avoids unfolding the Finset.sum over the filtered
support at each use site. -/

/-- Coefficient specification: `(posPart p).coeff t = p.coeff t` if
`p.coeff t > 0`, else `0`. -/
theorem posPart_coeff_spec {σ : Type*} [DecidableEq σ]
    (p : MvPolynomial σ ℚ) (t : σ →₀ ℕ) :
    (posPart p).coeff t = if 0 < p.coeff t then p.coeff t else 0 := by
  classical
  unfold posPart
  rw [MvPolynomial.coeff_sum]
  by_cases h : 0 < p.coeff t
  · rw [if_pos h]
    have ht_mem : t ∈ p.support.filter (fun s => 0 < p.coeff s) :=
      Finset.mem_filter.mpr
        ⟨MvPolynomial.mem_support_iff.mpr (ne_of_gt h), h⟩
    rw [Finset.sum_eq_single t]
    · rw [MvPolynomial.coeff_monomial, if_pos rfl]
    · intro s _ hne
      rw [MvPolynomial.coeff_monomial, if_neg hne]
    · intro hnot; exact absurd ht_mem hnot
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro s hs
    rw [MvPolynomial.coeff_monomial]
    split_ifs with heq
    · exfalso
      have hsp : 0 < p.coeff s := (Finset.mem_filter.mp hs).2
      rw [heq] at hsp
      exact h hsp
    · rfl

/-- Coefficient specification: `(negPart p).coeff t = -p.coeff t` if
`p.coeff t < 0`, else `0`. -/
theorem negPart_coeff_spec {σ : Type*} [DecidableEq σ]
    (p : MvPolynomial σ ℚ) (t : σ →₀ ℕ) :
    (negPart p).coeff t = if p.coeff t < 0 then -p.coeff t else 0 := by
  classical
  unfold negPart
  rw [MvPolynomial.coeff_sum]
  by_cases h : p.coeff t < 0
  · rw [if_pos h]
    have ht_mem : t ∈ p.support.filter (fun s => p.coeff s < 0) :=
      Finset.mem_filter.mpr
        ⟨MvPolynomial.mem_support_iff.mpr (ne_of_lt h), h⟩
    rw [Finset.sum_eq_single t]
    · rw [MvPolynomial.coeff_monomial, if_pos rfl]
    · intro s _ hne
      rw [MvPolynomial.coeff_monomial, if_neg hne]
    · intro hnot; exact absurd ht_mem hnot
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro s hs
    rw [MvPolynomial.coeff_monomial]
    split_ifs with heq
    · exfalso
      have hsp : p.coeff s < 0 := (Finset.mem_filter.mp hs).2
      rw [heq] at hsp
      exact h hsp
    · rfl

/-- **Decomposition lemma.** If `p = P − N` where both `P, N` have only
non-negative coefficients and their supports are disjoint, then
`posPart p = P` and `negPart p = N`. -/
theorem posPart_negPart_of_nonneg_disjoint_decomp {σ : Type*} [DecidableEq σ]
    {p P N : MvPolynomial σ ℚ}
    (hp : p = P - N)
    (hP_nn : ∀ s, 0 ≤ P.coeff s)
    (hN_nn : ∀ s, 0 ≤ N.coeff s)
    (hdisj : ∀ s, P.coeff s = 0 ∨ N.coeff s = 0) :
    posPart p = P ∧ negPart p = N := by
  classical
  have hcoeff : ∀ s, p.coeff s = P.coeff s - N.coeff s := fun s => by
    rw [hp, MvPolynomial.coeff_sub]
  refine ⟨MvPolynomial.ext _ _ (fun t => ?_), MvPolynomial.ext _ _ (fun t => ?_)⟩
  · -- posPart p = P via coefficient comparison.
    rw [posPart_coeff_spec]
    have hPt : 0 ≤ P.coeff t := hP_nn t
    have hNt : 0 ≤ N.coeff t := hN_nn t
    rcases lt_or_eq_of_le hPt with hPpos | hPzero
    · -- P.coeff t > 0, so N.coeff t = 0 (disj), p.coeff t = P.coeff t > 0.
      have hN0 : N.coeff t = 0 := by
        rcases hdisj t with hPz | hNz
        · exfalso; rw [hPz] at hPpos; exact lt_irrefl 0 hPpos
        · exact hNz
      have hpt : p.coeff t = P.coeff t := by rw [hcoeff, hN0, sub_zero]
      have hptpos : 0 < p.coeff t := hpt ▸ hPpos
      rw [if_pos hptpos, hpt]
    · -- P.coeff t = 0.
      have hpt : p.coeff t = -N.coeff t := by rw [hcoeff, ← hPzero, zero_sub]
      rcases lt_or_eq_of_le hNt with hNpos | hNzero
      · -- N.coeff t > 0, p.coeff t = -N.coeff t < 0, not in filter.
        have hnpt : p.coeff t < 0 := by rw [hpt]; linarith
        have hnot : ¬ 0 < p.coeff t := not_lt.mpr (le_of_lt hnpt)
        rw [if_neg hnot, ← hPzero]
      · -- N.coeff t = 0, p.coeff t = 0.
        have hpzero : p.coeff t = 0 := by rw [hpt, ← hNzero, neg_zero]
        have hnot : ¬ 0 < p.coeff t := by rw [hpzero]; exact lt_irrefl 0
        rw [if_neg hnot, ← hPzero]
  · -- negPart p = N via coefficient comparison.
    rw [negPart_coeff_spec]
    have hPt : 0 ≤ P.coeff t := hP_nn t
    have hNt : 0 ≤ N.coeff t := hN_nn t
    rcases lt_or_eq_of_le hNt with hNpos | hNzero
    · -- N.coeff t > 0, so P.coeff t = 0 (disj), p.coeff t = -N.coeff t < 0.
      have hP0 : P.coeff t = 0 := by
        rcases hdisj t with hPz | hNz
        · exact hPz
        · exfalso; rw [hNz] at hNpos; exact lt_irrefl 0 hNpos
      have hpt : p.coeff t = -N.coeff t := by rw [hcoeff, hP0, zero_sub]
      have hptneg : p.coeff t < 0 := by rw [hpt]; linarith
      rw [if_pos hptneg, hpt, neg_neg]
    · -- N.coeff t = 0.
      have hpt : p.coeff t = P.coeff t := by rw [hcoeff, ← hNzero, sub_zero]
      rcases lt_or_eq_of_le hPt with hPpos | hPzero
      · -- P.coeff t > 0, p.coeff t > 0, not in negPart filter.
        have hptpos : 0 < p.coeff t := hpt ▸ hPpos
        have hnot : ¬ p.coeff t < 0 := not_lt.mpr (le_of_lt hptpos)
        rw [if_neg hnot, ← hNzero]
      · -- both zero.
        have hpzero : p.coeff t = 0 := by rw [hpt, ← hPzero]
        have hnot : ¬ p.coeff t < 0 := by rw [hpzero]; exact lt_irrefl 0
        rw [if_neg hnot, ← hNzero]

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

/-! ## Dual-railing variants (scope clarification)

Three distinct notions of "dual-railing" appear in the literature. They
coincide on scalar problems but differ in the multi-variable setting:

  **Uniform**   — every species is dual-railed simultaneously. The whole
                  system moves from `Fin n` to `Fin (2n)` in one shot.
                  Positive/negative split is computed once per `pᵢ` with
                  `yⱼ = uⱼ − vⱼ` substituted for *all* `j`.

  **Single**    — one species at a time: pick index `i`, replace `yᵢ` by
                  `uᵢ − vᵢ`, leave other `yⱼ` as-is. Iterating this
                  one-variable-at-a-time recovers Uniform up to ordering,
                  but intermediate systems have mixed rails.

  **Selected**  — only a designated subset `S ⊆ Fin n` is dual-railed
                  (e.g. the transitive closure of some initial "anchor"
                  species under the dependency graph of `p`). The UCNC25
                  paper studies this variant.

The current file formalizes the **Uniform** variant as
`constantAnnihilationDualRail`. The two constructions below (Option (a)
and Option (b)) are both Uniform. Single-variable and Selected variants
are deferred until the Uniform case is resolved.

Note on polynomial degree: when we split `p̂ᵢ = p̂ᵢ⁺ − p̂ᵢ⁻`, the positive
and negative parts can each have degree up to `deg(pᵢ)` in the `u, v`
variables — substitution `yⱼ ↦ uⱼ − vⱼ` preserves total degree but
inflates monomial count. The annihilation term `k · uᵢ · vᵢ` is degree 2,
so the drift `pᵢ⁺ − k · uᵢ · vᵢ` has degree `max(deg pᵢ, 2)` regardless of
polynomial size. The open question is whether this bounded drift suffices
to keep `uᵢ, vᵢ` individually bounded.

## The two constructions

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

/-! ### Algebraic infrastructure for the DNA25 dual-rail boundedness

The strong DNA25 theorem — existence of a `PIVP.Solution` of the
polynomial-scale dual-rail system with non-negativity, boundedness, and
the dual-rail identity — lives at the semantic `BoundedTimeComputable`
level as `Ripple.dualRail_semantic_solution` (in `BTCReduction.lean`),
since it is consumed by `BoundedTimeComputable.toDualRail`.

The algebraic lemmas established in this file —
`posPart_sub_negPart`, `posPart_eval_nonneg`, `negPart_eval_nonneg`,
`dualRailHom_eval₂`, `dualRailPos_sub_dualRailNeg_eval`,
`dualRailPosPart_eval_nonneg`, `dualRailNegPart_eval_nonneg` — are the
purely syntactic / evaluation reductions needed by any eventual proof of
the semantic solution axiom. They are used in the downstream construction
and remain available for future proof work on the analytic core
(Picard–Lindelöf + Lyapunov global existence). -/

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
