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
`p̂⁺` (or `p̂⁻`) when uᵢvᵢ → ∞, contradiction. -/
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
