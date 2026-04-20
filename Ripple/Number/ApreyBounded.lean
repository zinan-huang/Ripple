/-
  Ripple.Number.ApreyBounded — ζ(3) via an 8-variable bounded PIVP
  (first-floor real-time scaffold)

  This file formalizes the bounded polynomial ODE system Xiang Huang
  recorded at https://infsup.com/math/apery-adaptation-zeta3/ for
  computing Apéry's constant

      ζ(3) = ∑_{k ≥ 0} 1 / (k+1)^3

  in the *real-time* (first-floor) class of Ripple's bounded complexity
  hierarchy.  The goal of this scaffold is not to close the proof —
  several pieces (invariant region, Frobenius analysis at the
  conifold singularity z₁ = 17 − 12√2, exponential adaptation) are
  genuine open sub-lemmas — but to record the polynomial system
  faithfully as a `PolyPIVP 8` and to state each open sub-lemma with
  a named signature so future work has explicit targets.

  The companion file `Apery.lean` remains in place; it documents the
  older, vacuous `IsCRNComputable` witness via `realtime_const`.
  This file introduces honest `sorry`s instead.

  State layout `Fin 8` (index / symbol / semantic role):

        0  z       Frobenius uniformiser (scalar ODE dz = p(z) dτ)
        1  α       ratio α = B/A at the z-scale
        2  σ_A     "auxiliary" accumulator for A
        3  β       ratio β = B'/A
        4  ρ       ratio ρ(t) → ζ(3) as t → ∞
        5  σ_B     accumulator for B
        6  w       inhomogeneous driver
        7  ζ       adaptation output, ζ̇ = ε (ρ − ζ)

  Polynomial RHS (τ-time, all components polynomial in the state):

      p(z)        = z² − 34 z³ + z⁴               = z² (1 − 34 z + z²)
      q(z)        = 3 z − 153 z² + 6 z³           = z (3 − 153 z + 6 z²)
      r(z)        = 1 − 112 z + 7 z²
      s(z)        = −5 + z
      Q(z,α,σ_A)  = q(z) + r(z) α + s(z) σ_A

      dz/dτ      = p(z)
      dα/dτ      = p(z) + q(z) α + r(z) α² + s(z) σ_A α
      dσ_A/dτ    = α p(z) + σ_A Q(z,α,σ_A)
      dβ/dτ      = ρ p(z) + β Q(z,α,σ_A)
      dρ/dτ      = r(z) (ρ α − β) + s(z) (ρ σ_A − σ_B) + 6 w
      dσ_B/dτ    = β p(z) + σ_B Q(z,α,σ_A)
      dw/dτ      = w Q(z,α,σ_A)
      dζ/dτ      = ε (ρ − ζ)                      (ε ∈ ℚ, e.g. 1/100)

  References:
  - Xiang Huang, "Apéry adaptation for ζ(3)" (infsup.com, 2026-04)
  - Apéry (1979), the original irrationality proof
  - Beukers, "Irrationality proofs using modular forms" (for the
    Frobenius / conifold analysis at z₁ = 17 − 12√2)
-/

import Ripple.Core.BoundedTime
import Ripple.Core.ODEGlobal
import Ripple.Core.ZeroInitPositivity
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace Ripple.Number

open Ripple
open MvPolynomial

/-! ## Named indices

  We give local notations for the eight state indices.  Using `Fin 8`
  literals everywhere would be legal but nearly unreadable.
-/

/-- Frobenius uniformiser index. -/
private def iZ : Fin 8 := 0
/-- Ratio α = B/A (at z-scale). -/
private def iA : Fin 8 := 1
/-- Auxiliary accumulator σ_A. -/
private def iSA : Fin 8 := 2
/-- Ratio β = B'/A. -/
private def iB : Fin 8 := 3
/-- Ratio ρ(t) → ζ(3). -/
private def iR : Fin 8 := 4
/-- Auxiliary accumulator σ_B. -/
private def iSB : Fin 8 := 5
/-- Inhomogeneous driver w. -/
private def iW : Fin 8 := 6
/-- Adaptation output ζ(t). -/
private def iZeta : Fin 8 := 7

/-! ## Adaptation rate

  ε is a fixed rational; 1/100 is a convenient working value.
-/

/-- Adaptation rate ε in the ζ̇ = ε(ρ − ζ) law.  Kept as a literal rational. -/
def aperyEps : ℚ := 1 / 100

/-! ## Polynomial helpers

  All polynomials live in `MvPolynomial (Fin 8) ℚ`; only the variable
  `z = X iZ` actually appears in p, q, r, s (they are polynomials in a
  single variable, lifted to the 8-variable ring for composition inside
  the field below).
-/

/-- p(z) = z² − 34 z³ + z⁴ = z² (1 − 34 z + z²). -/
noncomputable def aperyP : MvPolynomial (Fin 8) ℚ :=
  let z : MvPolynomial (Fin 8) ℚ := X iZ
  z ^ 2 - C 34 * z ^ 3 + z ^ 4

/-- q(z) = 3 z − 153 z² + 6 z³ = z (3 − 153 z + 6 z²). -/
noncomputable def aperyQ : MvPolynomial (Fin 8) ℚ :=
  let z : MvPolynomial (Fin 8) ℚ := X iZ
  C 3 * z - C 153 * z ^ 2 + C 6 * z ^ 3

/-- r(z) = 1 − 112 z + 7 z². -/
noncomputable def aperyR : MvPolynomial (Fin 8) ℚ :=
  let z : MvPolynomial (Fin 8) ℚ := X iZ
  C 1 - C 112 * z + C 7 * z ^ 2

/-- s(z) = −5 + z. -/
noncomputable def aperyS : MvPolynomial (Fin 8) ℚ :=
  let z : MvPolynomial (Fin 8) ℚ := X iZ
  (- C 5) + z

/-- Q(z, α, σ_A) = q(z) + r(z) α + s(z) σ_A.  A polynomial in three of
the eight variables. -/
noncomputable def aperyBigQ : MvPolynomial (Fin 8) ℚ :=
  aperyQ + aperyR * X iA + aperyS * X iSA

/-! ## Elaboration checks

  Keep these around to catch regressions early.  Each `#check` below
  fires during `lake build` only if the surrounding module elaborates.
-/

#check (aperyP   : MvPolynomial (Fin 8) ℚ)
#check (aperyQ   : MvPolynomial (Fin 8) ℚ)
#check (aperyR   : MvPolynomial (Fin 8) ℚ)
#check (aperyS   : MvPolynomial (Fin 8) ℚ)
#check (aperyBigQ : MvPolynomial (Fin 8) ℚ)

/-! ## The 8-variable polynomial vector field -/

/-- The polynomial vector field for the Apéry ζ(3) adaptation system.
The eight components implement the τ-time ODE recorded in the header. -/
noncomputable def apery8VarField : Fin 8 → MvPolynomial (Fin 8) ℚ := fun i =>
  let α  : MvPolynomial (Fin 8) ℚ := X iA
  let sA : MvPolynomial (Fin 8) ℚ := X iSA
  let β  : MvPolynomial (Fin 8) ℚ := X iB
  let ρ  : MvPolynomial (Fin 8) ℚ := X iR
  let sB : MvPolynomial (Fin 8) ℚ := X iSB
  let w  : MvPolynomial (Fin 8) ℚ := X iW
  let ζ  : MvPolynomial (Fin 8) ℚ := X iZeta
  match i with
  -- dz/dτ = p(z)
  | ⟨0, _⟩ => aperyP
  -- dα/dτ = p(z) + q(z) α + r(z) α² + s(z) σ_A α
  | ⟨1, _⟩ => aperyP + aperyQ * α + aperyR * α ^ 2 + aperyS * sA * α
  -- dσ_A/dτ = α p(z) + σ_A Q
  | ⟨2, _⟩ => α * aperyP + sA * aperyBigQ
  -- dβ/dτ = ρ p(z) + β Q
  | ⟨3, _⟩ => ρ * aperyP + β * aperyBigQ
  -- dρ/dτ = r(z)(ρ α − β) + s(z)(ρ σ_A − σ_B) + 6 w
  | ⟨4, _⟩ => aperyR * (ρ * α - β) + aperyS * (ρ * sA - sB) + C 6 * w
  -- dσ_B/dτ = β p(z) + σ_B Q
  | ⟨5, _⟩ => β * aperyP + sB * aperyBigQ
  -- dw/dτ = w Q
  | ⟨6, _⟩ => w * aperyBigQ
  -- dζ/dτ = ε (ρ − ζ)
  | ⟨7, _⟩ => C aperyEps * (ρ - ζ)

/-! ## The parameterised PolyPIVP

  The initial condition is supplied as an abstract rational vector
  `init : Fin 8 → ℚ`.  The intended values are the Taylor-truncation
  initial values at `z₀ = 1/1000`: `init iZ = 1/1000`, `init iZeta = 0`,
  and the six middle entries are specific rationals obtained from
  truncating the Apéry generating function.  We deliberately do NOT
  hard-code the middle six entries: the scaffold's correctness does
  not depend on their specific values, only on the downstream lemma
  `apery_exists_bounded_trajectory` constraining them to lie in the
  basin of the bounded invariant region.
-/

/-- The 8-variable Apéry PIVP parameterised by an abstract rational
initial vector.  Output index is `iZeta` (the adaptation output). -/
noncomputable def apery8VarPolyPIVP (init : Fin 8 → ℚ) : PolyPIVP 8 where
  field  := apery8VarField
  init   := init
  output := iZeta

/-! ## Open sub-lemmas

  The proof of `apery_real_time_from_adaptation` below reduces to four
  self-contained analytic statements.  Each is recorded here with a
  `sorry` body so that future work has an explicit target signature.
-/

/-- **(a)** Existence of a bounded global trajectory of the Apéry 8-var
PIVP, given a **hypothesised** forward-invariant region.

**Shape.** This lemma is the pure "global existence from local Lipschitz
+ an a priori bound" wrapper. We take the forward-invariant region
`‖y t‖ ≤ M` as a hypothesis (`h_invariant`): the caller is responsible
for verifying it for the specific initial condition of interest. For
the Taylor-truncation init at `z₀ = 1/1000`, verifying `h_invariant` is
the analytic content of sub-lemma (b) (Frobenius analysis at the
conifold singularity `z₁ = 17 − 12√2`) — it is deliberately *not*
proved here: (a) is agnostic to which initial conditions admit the
invariant.

**Why the hypothesis is necessary.** Without a forward-invariant region,
the 8-variable polynomial ODE may blow up in finite time for arbitrary
initial data (e.g. `dz/dτ = z² − 34z³ + z⁴` has `z ↗ ∞` finite-time
from large enough `z(0)`), so the required `PIVP.Solution` — which
demands `HasDerivAt` on all of `[0, ∞)` — does not exist in general.

**Proof pipeline.**
  (A) Local Lipschitz of the 8-variable polynomial vector field on every
      closed ball, via `polyPIVP_field_locally_lipschitz` (which itself
      comes from `ContDiffOn.lipschitzOnWith` on the compact ball).
  (B) The hypothesised `h_invariant` supplies the a priori bound.
  (C) `locally_lipschitz_bounded_global_ode_proved_continuous` combines
      (A)+(B) into a globally-defined trajectory with `HasDerivAt` on
      `[0, ∞)` and `Continuous` overall.
  (D) Package as a `PIVP.Solution` and re-extract the `IsBounded` bound
      by instantiating `h_invariant` on `Ico 0 (t+1)`.
-/
theorem apery_exists_bounded_trajectory
    (init : Fin 8 → ℚ)
    (M : ℝ) (hM : 0 < M)
    (h_invariant : ∀ (T : ℝ), 0 < T → ∀ (y : ℝ → Fin 8 → ℝ),
      y 0 = (fun i => ((init i : ℚ) : ℝ)) →
      (∀ t ∈ Set.Ico (0 : ℝ) T,
        HasDerivAt y ((apery8VarPolyPIVP init).toPIVP.field (y t)) t) →
      ∀ t ∈ Set.Ico (0 : ℝ) T, ‖y t‖ ≤ M) :
    ∃ sol : PIVP.Solution (apery8VarPolyPIVP init).toPIVP,
      (apery8VarPolyPIVP init).toPIVP.IsBounded sol.trajectory := by
  -- Abbreviations.
  set F : (Fin 8 → ℝ) → Fin 8 → ℝ :=
    (apery8VarPolyPIVP init).toPIVP.field with hF_def
  set y₀ : Fin 8 → ℝ := (apery8VarPolyPIVP init).toPIVP.init with hy₀_def
  -- `y₀` is just `init` coerced to ℝ componentwise.
  have hy₀_eq : y₀ = fun i => ((init i : ℚ) : ℝ) := by
    funext i
    show (apery8VarPolyPIVP init).toPIVP.init i = ((init i : ℚ) : ℝ)
    simp [PolyPIVP.toPIVP_init, apery8VarPolyPIVP]
  -- (A) Local Lipschitz of F on every closed ball.
  have h_lip : ∀ R : ℝ, 0 < R → ∃ L : ℝ, ∀ x y : Fin 8 → ℝ,
      ‖x‖ ≤ R → ‖y‖ ≤ R → ‖F x - F y‖ ≤ L * ‖x - y‖ :=
    polyPIVP_field_locally_lipschitz (apery8VarPolyPIVP init)
  -- (B) Convert h_invariant to the exact shape the global-existence theorem
  --     wants (i.e. stated in terms of `F` and `y₀`).
  have h_invariant' : ∀ (T : ℝ), 0 < T → ∀ (y : ℝ → Fin 8 → ℝ),
      y 0 = y₀ →
      (∀ t ∈ Set.Ico (0 : ℝ) T, HasDerivAt y (F (y t)) t) →
      ∀ t ∈ Set.Ico (0 : ℝ) T, ‖y t‖ ≤ M := by
    intro T hT y hy0 h_deriv
    apply h_invariant T hT y
    · rw [hy0, hy₀_eq]
    · exact h_deriv
  -- (C) Invoke the global-existence theorem.
  obtain ⟨y, hy0, hy_deriv, _hy_cont⟩ :=
    locally_lipschitz_bounded_global_ode_proved_continuous F y₀
      h_lip M hM h_invariant'
  -- (D) Package as PIVP.Solution and extract IsBounded.
  refine
    ⟨ { trajectory := y,
        init_cond := hy0,
        is_solution := hy_deriv },
      M, hM, ?_ ⟩
  intro t ht
  -- Apply h_invariant on [0, t+1] to get ‖y t‖ ≤ M.
  have hT_pos : (0 : ℝ) < t + 1 := by linarith
  have hy_deriv' : ∀ s ∈ Set.Ico (0 : ℝ) (t + 1),
      HasDerivAt y (F (y s)) s := fun s hs => hy_deriv s hs.1
  have ht_in : t ∈ Set.Ico (0 : ℝ) (t + 1) := ⟨ht, by linarith⟩
  exact h_invariant' (t + 1) hT_pos y hy0 hy_deriv' t ht_in

/-- **Apéry conifold Frobenius witness** — the single deep analytic
gap in the ζ(3) chain.

**Claim.** Along any bounded trajectory of the Apéry 8-var PIVP
whose initial z-coordinate lies in the conifold basin
`(0, z₁)` with `z₁ := 17 − 12√2` (the conifold singularity of the
Apéry generating-function ODE), there exist `K, κ > 0` such that
the ρ-coordinate satisfies
    `|ρ(τ) − ζ(3)| ≤ K · exp(−κ τ)`.

**What the proof requires** — none of this is currently in Mathlib:

  (F1) The Apéry sequences `aₙ, bₙ` defined combinatorially
       (`aₙ = Σ C(n,k)² C(n+k,k)²`; companion `b₀ = 0, b₁ = 6`)
       satisfy the three-term recurrence
         `(n+1)³ aₙ₊₁ = (2n+1)(17n²+17n+5) aₙ − n³ aₙ₋₁`.
  (F2) The generating functions `A(z) = Σ aₙ zⁿ`, `B(z) = Σ bₙ zⁿ`
       satisfy respectively the homogeneous and inhomogeneous
       Apéry ODE of order 3:
         `p A''' + q A'' + r A' + s A = 0`,
         `p B''' + q B'' + r B' + s B = 6`.
  (F3) At the conifold `z₁ = 17 − 12√2` the indicial equation
       `ρ(2ρ − 1)(ρ − 1) = 0` gives local Frobenius exponents
       `{0, 1/2, 1}`.
  (F4) **Apéry's identity** `β₁/α₁ = ζ(3)`: the `√(z₁ − z)`
       Frobenius coefficient of `E(z) := B(z) − ζ(3) · A(z)`
       vanishes.  (This is the analytical content of Apéry's
       irrationality proof.)
  (F5) Consequently `E(z)` is analytic at `z₁`, hence `E''(z)` is
       bounded there, while `A''(z) ~ C (z₁ − z)^(−3/2)` blows
       up, giving `|B''/A'' − ζ(3)| = O((z₁ − z)^(3/2))`.
  (F6) The scalar ODE `dz/dτ = p(z) = z²(1 − 34z + z²)` starting
       from `z₀ ∈ (0, z₁)` yields `z(τ) → z₁` with
       `|z₁ − z(τ)| ≤ C · exp(−λ τ)`, `λ = 24√2 · z₁²`
       (linearization at the simple zero of `p` at `z₁`).

Combining (F5) and (F6):
    `|ρ(τ) − ζ(3)| ≤ C'·|z₁ − z(τ)|^(3/2) ≤ C'·C^(3/2)·exp(−(3λ/2)·τ)`.

**Status.** (F6) is pure scalar ODE — Mathlib-closeable with
effort (linearization + Grönwall at the isolated zero of `p`).
(F1)–(F5) are Apéry's theorem and regular-singular-point
Frobenius theory, neither of which Mathlib currently has;
formalizing them is on the order of a standalone project. The
whole analytical core is therefore concentrated in this single
witness. -/
theorem apery_conifold_frobenius_witness
    (init : Fin 8 → ℚ)
    (sol : PIVP.Solution (apery8VarPolyPIVP init).toPIVP)
    (_hbdd : (apery8VarPolyPIVP init).toPIVP.IsBounded sol.trajectory)
    (_h_z_init : (0 : ℝ) < ((init iZ : ℚ) : ℝ) ∧
                 ((init iZ : ℚ) : ℝ) < 17 - 12 * Real.sqrt 2) :
    ∃ K κ : ℝ, 0 < K ∧ 0 < κ ∧
      ∀ t : ℝ, 0 ≤ t →
        |sol.trajectory t iR - (∑' k : ℕ, 1 / ((k + 1 : ℝ) ^ 3))|
          ≤ K * Real.exp (-(κ * t)) := by
  sorry

/-- **(b)** Exponential convergence of the ratio `ρ(t)` to `ζ(3)`
along any bounded trajectory whose initial z-coordinate lies in
the conifold basin `(0, z₁)`, `z₁ := 17 − 12√2`.

**Reduction.** This is a direct repackaging of
`apery_conifold_frobenius_witness`: once the Frobenius estimate
is granted as a black box, the statement is immediate. All the
analytical work lives in the witness — see its docstring for the
six-step roadmap (F1)–(F6) of what remains to be formalized. -/
theorem apery_ratio_converges_exponentially
    (init : Fin 8 → ℚ)
    (sol : PIVP.Solution (apery8VarPolyPIVP init).toPIVP)
    (hbdd : (apery8VarPolyPIVP init).toPIVP.IsBounded sol.trajectory)
    (h_z_init : (0 : ℝ) < ((init iZ : ℚ) : ℝ) ∧
                ((init iZ : ℚ) : ℝ) < 17 - 12 * Real.sqrt 2) :
    ∃ K κ : ℝ, 0 < K ∧ 0 < κ ∧
      ∀ t : ℝ, 0 ≤ t →
        |sol.trajectory t iR - (∑' k : ℕ, 1 / ((k + 1 : ℝ) ^ 3))|
          ≤ K * Real.exp (-(κ * t)) :=
  apery_conifold_frobenius_witness init sol hbdd h_z_init

/-! ### Helpers for (c)

  The sub-lemma (c) is a scalar linear-ODE estimate: from
  `ζ̇(t) = ε (ρ(t) − ζ(t))` and `|ρ(t) − ζ(3)| ≤ K e^(−κt)` we derive
  `|ζ(t) − ζ(3)| ≤ K' e^(−κ' t)` for suitable `K', κ' > 0`.  The
  proof uses the integrating-factor / fencing lemma
  `image_norm_le_of_norm_deriv_right_le_deriv_boundary` applied to
  `w(t) := e^(εt) · (ζ(t) − ζ(3))`.
-/

/-- The ζ-component of the Apéry PIVP satisfies
`HasDerivAt (ζ·) (ε(ρ − ζ)) t`.  This is just the projection of the
full `is_solution` onto the output index, combined with the explicit
polynomial field expression. -/
private lemma apery_zeta_hasDerivAt
    (init : Fin 8 → ℚ)
    (sol : PIVP.Solution (apery8VarPolyPIVP init).toPIVP)
    (t : ℝ) (ht : 0 ≤ t) :
    HasDerivAt (fun s => sol.trajectory s iZeta)
      ((aperyEps : ℝ) *
        (sol.trajectory t iR - sol.trajectory t iZeta)) t := by
  have h := (hasDerivAt_pi.mp (sol.is_solution t ht)) iZeta
  -- Simplify the field at iZeta to the closed polynomial expression.
  have hfield : (apery8VarPolyPIVP init).toPIVP.field (sol.trajectory t) iZeta =
      (aperyEps : ℝ) *
        (sol.trajectory t iR - sol.trajectory t iZeta) := by
    -- Unfold through the toPIVP / evalField / apery8VarField layer.
    show (apery8VarPolyPIVP init).evalField (sol.trajectory t) iZeta = _
    unfold PolyPIVP.evalField apery8VarPolyPIVP
    simp [apery8VarField, iZeta, iR, MvPolynomial.eval₂_C,
      MvPolynomial.eval₂_X, MvPolynomial.eval₂_sub, MvPolynomial.eval₂_mul]
  rw [hfield] at h
  exact h

/-- The abbreviated scalar error `u(t) := ζ(t) − ζ(3)` satisfies
`u̇ = ε(ρ − ζ(3)) − ε u`. -/
private lemma apery_u_hasDerivAt
    (init : Fin 8 → ℚ)
    (sol : PIVP.Solution (apery8VarPolyPIVP init).toPIVP)
    (t : ℝ) (ht : 0 ≤ t) :
    HasDerivAt (fun s => sol.trajectory s iZeta -
          (∑' k : ℕ, 1 / ((k + 1 : ℝ) ^ 3)))
      ((aperyEps : ℝ) *
        (sol.trajectory t iR -
          (∑' k : ℕ, 1 / ((k + 1 : ℝ) ^ 3))) -
        (aperyEps : ℝ) *
          (sol.trajectory t iZeta -
            (∑' k : ℕ, 1 / ((k + 1 : ℝ) ^ 3)))) t := by
  set ζ3 : ℝ := ∑' k : ℕ, 1 / ((k + 1 : ℝ) ^ 3)
  have h0 := apery_zeta_hasDerivAt init sol t ht
  have h1 := h0.sub_const ζ3
  -- Rewrite the rate to the desired algebraic form.
  convert h1 using 1
  ring

/-- `w(t) := e^(εt) · u(t)` has derivative `e^(εt) · ε · (ρ − ζ(3))`. -/
private lemma apery_w_hasDerivAt
    (init : Fin 8 → ℚ)
    (sol : PIVP.Solution (apery8VarPolyPIVP init).toPIVP)
    (t : ℝ) (ht : 0 ≤ t) :
    HasDerivAt
      (fun s => Real.exp ((aperyEps : ℝ) * s) *
        (sol.trajectory s iZeta -
          (∑' k : ℕ, 1 / ((k + 1 : ℝ) ^ 3))))
      (Real.exp ((aperyEps : ℝ) * t) * (aperyEps : ℝ) *
        (sol.trajectory t iR -
          (∑' k : ℕ, 1 / ((k + 1 : ℝ) ^ 3)))) t := by
  set ε : ℝ := (aperyEps : ℝ)
  set ζ3 : ℝ := ∑' k : ℕ, 1 / ((k + 1 : ℝ) ^ 3)
  have hLin : HasDerivAt (fun s : ℝ => ε * s) ε t := by
    simpa using (hasDerivAt_id t).const_mul ε
  have hExp : HasDerivAt (fun s => Real.exp (ε * s))
      (Real.exp (ε * t) * ε) t := by
    have h := (Real.hasDerivAt_exp (ε * t)).comp t hLin
    -- h : HasDerivAt (fun s => Real.exp (ε * s)) (Real.exp (ε * t) * ε) t
    convert h using 1
  have hU := apery_u_hasDerivAt init sol t ht
  have hProd := hExp.mul hU
  convert hProd using 1
  -- Rate: e^(εt) · ε · (ρ − ζ3)
  --   vs e^(εt)*ε · u + e^(εt)·(ε(ρ−ζ3) − ε·u) = e^(εt)·ε·(ρ−ζ3).
  ring

/-- Helper: `t · e^(-α t) ≤ 1/α` for `t ≥ 0`, `α > 0`. -/
private lemma t_mul_exp_neg_le (α : ℝ) (hα : 0 < α) (t : ℝ) (ht : 0 ≤ t) :
    t * Real.exp (-(α * t)) ≤ 1 / α := by
  -- Equivalent to `α · t ≤ e^(α t)`, standard.
  have hαt_nn : 0 ≤ α * t := mul_nonneg hα.le ht
  have h_add_one : α * t + 1 ≤ Real.exp (α * t) := by
    have := Real.add_one_le_exp (α * t)
    linarith
  have h1 : α * t ≤ Real.exp (α * t) := by linarith
  -- Multiply by e^(-α t) > 0:
  have hExpPos : 0 < Real.exp (α * t) := Real.exp_pos _
  have hNeg_exp : Real.exp (-(α * t)) = (Real.exp (α * t))⁻¹ := by
    rw [← Real.exp_neg]
  calc t * Real.exp (-(α * t))
      = t * (Real.exp (α * t))⁻¹ := by rw [hNeg_exp]
    _ = (α * t) * (α * Real.exp (α * t))⁻¹ := by
        field_simp
    _ ≤ Real.exp (α * t) * (α * Real.exp (α * t))⁻¹ := by
        apply mul_le_mul_of_nonneg_right h1
        positivity
    _ = 1 / α := by
        have hne : Real.exp (α * t) ≠ 0 := ne_of_gt hExpPos
        have hαne : α ≠ 0 := ne_of_gt hα
        field_simp

/-- **(c)** The linear adaptation law ζ̇ = ε(ρ − ζ) drives ζ to ρ
exponentially.  Combined with (b), ζ(t) → ζ(3).  Proof is a scalar
linear-ODE fencing estimate: apply
`image_norm_le_of_norm_deriv_right_le_deriv_boundary` to
`w(t) = e^(εt)·(ζ(t)−ζ(3))`, then translate back through `e^(−εt)`. -/
theorem apery_adaptation_tracks_ratio
    (init : Fin 8 → ℚ)
    (sol : PIVP.Solution (apery8VarPolyPIVP init).toPIVP)
    (_hbdd : (apery8VarPolyPIVP init).toPIVP.IsBounded sol.trajectory)
    (K κ : ℝ) (_hK : 0 < K) (_hκ : 0 < κ)
    (_hρ : ∀ t : ℝ, 0 ≤ t →
        |sol.trajectory t iR - (∑' k : ℕ, 1 / ((k + 1 : ℝ) ^ 3))|
          ≤ K * Real.exp (-(κ * t))) :
    ∃ K' κ' : ℝ, 0 < K' ∧ 0 < κ' ∧
      ∀ t : ℝ, 0 ≤ t →
        |sol.trajectory t iZeta - (∑' k : ℕ, 1 / ((k + 1 : ℝ) ^ 3))|
          ≤ K' * Real.exp (-(κ' * t)) := by
  set ε : ℝ := (aperyEps : ℝ) with hε_def
  set ζ3 : ℝ := ∑' k : ℕ, 1 / ((k + 1 : ℝ) ^ 3) with hζ3_def
  -- ε > 0 since aperyEps = 1/100 > 0.
  have hε_pos : 0 < ε := by
    rw [hε_def]
    show (0 : ℝ) < ((aperyEps : ℚ) : ℝ)
    have : (0 : ℚ) < aperyEps := by unfold aperyEps; norm_num
    exact_mod_cast this
  -- Initial error |u(0)| = |ζ(0) − ζ(3)|.
  set u0 : ℝ := |sol.trajectory 0 iZeta - ζ3| with hu0_def
  have hu0_nn : 0 ≤ u0 := abs_nonneg _
  -- Case split on κ vs ε.
  by_cases hcase : ε ≤ κ
  · -- Case A: ε ≤ κ.  Pick κ' = ε/2, K' = u0 + 2 K ε / ε + 1 = u0 + 2 K + 1.
    -- Boundary for w(t) = e^(εt) u(t): B(t) = u0 + ε K · t,
    -- valid because B'(t) = ε K ≥ ε K · e^((ε − κ)t) (since ε ≤ κ).
    refine ⟨u0 + 2 * K + 1, ε / 2, by positivity, by positivity, ?_⟩
    intro t ht
    -- Apply the fencing lemma on [0, t].
    set a : ℝ := 0
    set b : ℝ := t
    -- f := w = e^(εs) * u(s).
    let fW : ℝ → ℝ := fun s =>
      Real.exp (ε * s) * (sol.trajectory s iZeta - ζ3)
    -- f' := ẇ = e^(εs) · ε · (ρ(s) − ζ3).
    let fW' : ℝ → ℝ := fun s =>
      Real.exp (ε * s) * ε * (sol.trajectory s iR - ζ3)
    -- Boundary B(s) := u0 + ε K · s, B'(s) = ε K.
    let BB : ℝ → ℝ := fun s => u0 + ε * K * s
    let BB' : ℝ → ℝ := fun _ => ε * K
    have hfW_deriv : ∀ s ∈ Set.Ico (a : ℝ) b,
        HasDerivWithinAt fW (fW' s) (Set.Ici s) s := by
      intro s hs
      have hs_nn : 0 ≤ s := hs.1
      exact (apery_w_hasDerivAt init sol s hs_nn).hasDerivWithinAt
    have hfW_cont : ContinuousOn fW (Set.Icc a b) := by
      intro s hs
      by_cases hs0 : s = b ∧ s = a
      · -- degenerate, falls back below
        exact ((apery_w_hasDerivAt init sol s hs.1).continuousAt).continuousWithinAt
      · exact ((apery_w_hasDerivAt init sol s hs.1).continuousAt).continuousWithinAt
    have hBB_deriv : ∀ s, HasDerivAt BB (BB' s) s := by
      intro s
      show HasDerivAt (fun x => u0 + ε * K * x) (ε * K) s
      have h1 : HasDerivAt (fun x : ℝ => ε * K * x) (ε * K) s := by
        simpa using (hasDerivAt_id s).const_mul (ε * K)
      have h2 : HasDerivAt (fun x : ℝ => u0 + ε * K * x) (0 + ε * K) s :=
        (hasDerivAt_const s u0).add h1
      simpa using h2
    have hInit : ‖fW a‖ ≤ BB a := by
      show |fW 0| ≤ u0 + ε * K * 0
      simp only [fW, Real.norm_eq_abs]
      rw [mul_zero, Real.exp_zero, one_mul]
      show |sol.trajectory 0 iZeta - ζ3| ≤ u0 + ε * K * 0
      rw [mul_zero, add_zero, hu0_def]
    have hBound : ∀ s ∈ Set.Ico a b, ‖fW' s‖ ≤ BB' s := by
      intro s hs
      have hs_nn : 0 ≤ s := hs.1
      show |Real.exp (ε * s) * ε * (sol.trajectory s iR - ζ3)| ≤ ε * K
      have hρBound : |sol.trajectory s iR - ζ3| ≤ K * Real.exp (-(κ * s)) :=
        _hρ s hs_nn
      have hExpPos : 0 < Real.exp (ε * s) := Real.exp_pos _
      have h1 : |Real.exp (ε * s) * ε * (sol.trajectory s iR - ζ3)|
          = Real.exp (ε * s) * ε * |sol.trajectory s iR - ζ3| := by
        rw [abs_mul, abs_of_pos (by positivity : 0 < Real.exp (ε * s) * ε)]
      rw [h1]
      have h2 : Real.exp (ε * s) * ε * |sol.trajectory s iR - ζ3|
          ≤ Real.exp (ε * s) * ε * (K * Real.exp (-(κ * s))) := by
        apply mul_le_mul_of_nonneg_left hρBound
        positivity
      -- Now bound Real.exp (ε s) * ε * K * exp(-κ s) ≤ ε * K
      -- via exp((ε-κ)s) ≤ 1 when ε ≤ κ and s ≥ 0.
      have hExpCombine : Real.exp (ε * s) * Real.exp (-(κ * s))
          = Real.exp ((ε - κ) * s) := by
        rw [← Real.exp_add]
        congr 1; ring
      have h3 : Real.exp (ε * s) * ε * (K * Real.exp (-(κ * s)))
          = ε * K * Real.exp ((ε - κ) * s) := by
        rw [show Real.exp (ε * s) * ε * (K * Real.exp (-(κ * s)))
            = ε * K * (Real.exp (ε * s) * Real.exp (-(κ * s))) from by ring,
          hExpCombine]
      rw [h3] at h2
      have h4 : Real.exp ((ε - κ) * s) ≤ 1 := by
        apply Real.exp_le_one_iff.mpr
        have : (ε - κ) ≤ 0 := by linarith
        exact mul_nonpos_of_nonpos_of_nonneg this hs_nn
      calc Real.exp (ε * s) * ε * |sol.trajectory s iR - ζ3|
          ≤ ε * K * Real.exp ((ε - κ) * s) := h2
        _ ≤ ε * K * 1 := by
            apply mul_le_mul_of_nonneg_left h4
            positivity
        _ = ε * K := mul_one _
    have hab : (a : ℝ) ≤ b := ht
    have hw_bound : ∀ ⦃s⦄, s ∈ Set.Icc a b → ‖fW s‖ ≤ BB s :=
      image_norm_le_of_norm_deriv_right_le_deriv_boundary hfW_cont hfW_deriv
        hInit hBB_deriv hBound
    have h_at_t : ‖fW t‖ ≤ BB t := hw_bound (Set.right_mem_Icc.mpr hab)
    -- Translate back: |u(t)| ≤ e^(-εt) · (u0 + ε K t).
    have hw_eq : fW t = Real.exp (ε * t) *
        (sol.trajectory t iZeta - ζ3) := rfl
    have hAbsW : |fW t| = Real.exp (ε * t) *
        |sol.trajectory t iZeta - ζ3| := by
      rw [hw_eq, abs_mul, abs_of_pos (Real.exp_pos _)]
    have hExpPos_t : 0 < Real.exp (ε * t) := Real.exp_pos _
    have h_at_t' :
        Real.exp (ε * t) * |sol.trajectory t iZeta - ζ3|
          ≤ u0 + ε * K * t := by
      have := h_at_t
      rw [Real.norm_eq_abs, hAbsW] at this
      show Real.exp (ε * t) * |sol.trajectory t iZeta - ζ3|
          ≤ u0 + ε * K * t
      exact this
    have habs_bound :
        |sol.trajectory t iZeta - ζ3|
          ≤ (u0 + ε * K * t) * Real.exp (-(ε * t)) := by
      -- from h_at_t' : e^(εt) * |u(t)| ≤ u0 + εKt, divide both sides by e^(εt).
      have h_div : |sol.trajectory t iZeta - ζ3|
          ≤ (u0 + ε * K * t) / Real.exp (ε * t) := by
        rw [le_div_iff₀ hExpPos_t, mul_comm]
        exact h_at_t'
      have h_eq : (u0 + ε * K * t) / Real.exp (ε * t)
          = (u0 + ε * K * t) * Real.exp (-(ε * t)) := by
        rw [Real.exp_neg, div_eq_mul_inv]
      linarith [h_div, h_eq]
    -- Now bound (u0 + ε K t) * exp(-εt) by (u0 + 2K + 1) * exp(-εt/2).
    -- |u(t)| ≤ u0 · exp(-εt) + εKt · exp(-εt)
    --       ≤ u0 · exp(-εt/2) + 2K · exp(-εt/2)
    -- using t·exp(-εt/2) ≤ 2/ε.
    have hexp_split : Real.exp (-(ε * t))
        = Real.exp (-(ε/2 * t)) * Real.exp (-(ε/2 * t)) := by
      rw [← Real.exp_add]; congr 1; ring
    have hε2_pos : 0 < ε / 2 := by linarith
    have hExp_half_pos : 0 < Real.exp (-(ε / 2 * t)) := Real.exp_pos _
    have hExp_half_le_one : Real.exp (-(ε / 2 * t)) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      have : 0 ≤ ε / 2 * t := by positivity
      linarith
    have h_texp : t * Real.exp (-(ε / 2 * t)) ≤ 2 / ε := by
      have h := t_mul_exp_neg_le (ε/2) hε2_pos t ht
      have : 1 / (ε / 2) = 2 / ε := by field_simp
      rw [this] at h
      exact h
    have hfinal :
        (u0 + ε * K * t) * Real.exp (-(ε * t))
          ≤ (u0 + 2 * K + 1) * Real.exp (-(ε / 2 * t)) := by
      rw [hexp_split]
      have h_distr : (u0 + ε * K * t) *
          (Real.exp (-(ε / 2 * t)) * Real.exp (-(ε / 2 * t)))
          = u0 * Real.exp (-(ε / 2 * t)) * Real.exp (-(ε / 2 * t))
            + ε * K * (t * Real.exp (-(ε / 2 * t))) *
              Real.exp (-(ε / 2 * t)) := by ring
      rw [h_distr]
      have hA : u0 * Real.exp (-(ε / 2 * t)) * Real.exp (-(ε / 2 * t))
          ≤ u0 * Real.exp (-(ε / 2 * t)) := by
        have : u0 * Real.exp (-(ε / 2 * t)) * Real.exp (-(ε / 2 * t))
            ≤ u0 * Real.exp (-(ε / 2 * t)) * 1 := by
          apply mul_le_mul_of_nonneg_left hExp_half_le_one
          exact mul_nonneg hu0_nn hExp_half_pos.le
        linarith
      have hB : ε * K * (t * Real.exp (-(ε / 2 * t))) *
          Real.exp (-(ε / 2 * t)) ≤ 2 * K * Real.exp (-(ε / 2 * t)) := by
        have hεK_nn : 0 ≤ ε * K := mul_nonneg hε_pos.le _hK.le
        have h1 : ε * K * (t * Real.exp (-(ε / 2 * t)))
            ≤ ε * K * (2 / ε) := by
          exact mul_le_mul_of_nonneg_left h_texp hεK_nn
        have h2 : ε * K * (2 / ε) = 2 * K := by
          have hne : ε ≠ 0 := ne_of_gt hε_pos
          field_simp
        rw [h2] at h1
        have h3 : ε * K * (t * Real.exp (-(ε / 2 * t))) *
            Real.exp (-(ε / 2 * t))
            ≤ 2 * K * Real.exp (-(ε / 2 * t)) := by
          have hne : 0 ≤ Real.exp (-(ε / 2 * t)) := Real.exp_pos _ |>.le
          exact mul_le_mul_of_nonneg_right h1 hne
        exact h3
      have hC : (u0 + 2 * K + 1) * Real.exp (-(ε / 2 * t))
          = u0 * Real.exp (-(ε / 2 * t)) +
            2 * K * Real.exp (-(ε / 2 * t)) +
            Real.exp (-(ε / 2 * t)) := by ring
      have hSlack : 0 ≤ Real.exp (-(ε / 2 * t)) := hExp_half_pos.le
      linarith
    -- Conclude.
    have : |sol.trajectory t iZeta - ζ3|
        ≤ (u0 + 2 * K + 1) * Real.exp (-(ε / 2 * t)) :=
      le_trans habs_bound hfinal
    -- Now rewrite the target bound with κ' = ε/2.
    show |sol.trajectory t iZeta - ζ3|
        ≤ (u0 + 2 * K + 1) * Real.exp (-(ε / 2 * t))
    exact this
  · -- Case B: κ < ε.
    push_neg at hcase
    -- Take κ' = κ/2, K' = u0 + ε K / (ε − κ) + 1.
    have hdiff_pos : 0 < ε - κ := by linarith
    refine ⟨u0 + ε * K / (ε - κ) + 1, κ / 2,
      by positivity, by positivity, ?_⟩
    intro t ht
    set a : ℝ := 0
    set b : ℝ := t
    let fW : ℝ → ℝ := fun s =>
      Real.exp (ε * s) * (sol.trajectory s iZeta - ζ3)
    let fW' : ℝ → ℝ := fun s =>
      Real.exp (ε * s) * ε * (sol.trajectory s iR - ζ3)
    -- Boundary: B(s) := u0 + ε K / (ε−κ) · (e^((ε−κ)s) − 1),
    -- B'(s) = ε K · e^((ε−κ)s).
    let BB : ℝ → ℝ := fun s =>
      u0 + ε * K / (ε - κ) * (Real.exp ((ε - κ) * s) - 1)
    let BB' : ℝ → ℝ := fun s =>
      ε * K * Real.exp ((ε - κ) * s)
    have hfW_deriv : ∀ s ∈ Set.Ico (a : ℝ) b,
        HasDerivWithinAt fW (fW' s) (Set.Ici s) s := by
      intro s hs
      exact (apery_w_hasDerivAt init sol s hs.1).hasDerivWithinAt
    have hfW_cont : ContinuousOn fW (Set.Icc a b) := fun s hs =>
      ((apery_w_hasDerivAt init sol s hs.1).continuousAt).continuousWithinAt
    have hBB_deriv : ∀ s, HasDerivAt BB (BB' s) s := by
      intro s
      show HasDerivAt
        (fun x => u0 + ε * K / (ε - κ) * (Real.exp ((ε - κ) * x) - 1))
        (ε * K * Real.exp ((ε - κ) * s)) s
      have hLin : HasDerivAt (fun x : ℝ => (ε - κ) * x) (ε - κ) s := by
        simpa using (hasDerivAt_id s).const_mul (ε - κ)
      have hExp : HasDerivAt (fun x => Real.exp ((ε - κ) * x))
          (Real.exp ((ε - κ) * s) * (ε - κ)) s := by
        have := (Real.hasDerivAt_exp ((ε - κ) * s)).comp s hLin
        convert this using 1
      have h1 : HasDerivAt (fun x => Real.exp ((ε - κ) * x) - 1)
          (Real.exp ((ε - κ) * s) * (ε - κ)) s := hExp.sub_const 1
      have h2 : HasDerivAt
          (fun x => ε * K / (ε - κ) * (Real.exp ((ε - κ) * x) - 1))
          (ε * K / (ε - κ) * (Real.exp ((ε - κ) * s) * (ε - κ))) s :=
        h1.const_mul (ε * K / (ε - κ))
      have hrewrite :
          ε * K / (ε - κ) * (Real.exp ((ε - κ) * s) * (ε - κ))
            = ε * K * Real.exp ((ε - κ) * s) := by
        have hne : ε - κ ≠ 0 := ne_of_gt hdiff_pos
        field_simp
      rw [hrewrite] at h2
      have h3 : HasDerivAt
          (fun x => u0 + ε * K / (ε - κ) * (Real.exp ((ε - κ) * x) - 1))
          (0 + ε * K * Real.exp ((ε - κ) * s)) s :=
        (hasDerivAt_const s u0).add h2
      simpa using h3
    have hInit : ‖fW a‖ ≤ BB a := by
      show |fW 0| ≤ u0 + ε * K / (ε - κ) * (Real.exp ((ε - κ) * 0) - 1)
      show |Real.exp (ε * 0) * (sol.trajectory 0 iZeta - ζ3)|
          ≤ u0 + ε * K / (ε - κ) * (Real.exp ((ε - κ) * 0) - 1)
      rw [mul_zero, Real.exp_zero, one_mul, mul_zero, Real.exp_zero,
        sub_self, mul_zero, add_zero, hu0_def]
    have hBound : ∀ s ∈ Set.Ico a b, ‖fW' s‖ ≤ BB' s := by
      intro s hs
      have hs_nn : 0 ≤ s := hs.1
      show |Real.exp (ε * s) * ε * (sol.trajectory s iR - ζ3)|
          ≤ ε * K * Real.exp ((ε - κ) * s)
      have hρBound : |sol.trajectory s iR - ζ3| ≤ K * Real.exp (-(κ * s)) :=
        _hρ s hs_nn
      have h1 : |Real.exp (ε * s) * ε * (sol.trajectory s iR - ζ3)|
          = Real.exp (ε * s) * ε * |sol.trajectory s iR - ζ3| := by
        rw [abs_mul, abs_of_pos (by positivity : 0 < Real.exp (ε * s) * ε)]
      rw [h1]
      have h2 : Real.exp (ε * s) * ε * |sol.trajectory s iR - ζ3|
          ≤ Real.exp (ε * s) * ε * (K * Real.exp (-(κ * s))) := by
        apply mul_le_mul_of_nonneg_left hρBound
        positivity
      have hExpCombine : Real.exp (ε * s) * Real.exp (-(κ * s))
          = Real.exp ((ε - κ) * s) := by
        rw [← Real.exp_add]; congr 1; ring
      have h3 : Real.exp (ε * s) * ε * (K * Real.exp (-(κ * s)))
          = ε * K * Real.exp ((ε - κ) * s) := by
        rw [show Real.exp (ε * s) * ε * (K * Real.exp (-(κ * s)))
            = ε * K * (Real.exp (ε * s) * Real.exp (-(κ * s))) from by ring,
          hExpCombine]
      linarith [h2.trans_eq h3]
    have hab : (a : ℝ) ≤ b := ht
    have hw_bound : ∀ ⦃s⦄, s ∈ Set.Icc a b → ‖fW s‖ ≤ BB s :=
      image_norm_le_of_norm_deriv_right_le_deriv_boundary hfW_cont hfW_deriv
        hInit hBB_deriv hBound
    have h_at_t : ‖fW t‖ ≤ BB t := hw_bound (Set.right_mem_Icc.mpr hab)
    have hw_eq : fW t = Real.exp (ε * t) *
        (sol.trajectory t iZeta - ζ3) := rfl
    have hAbsW : |fW t| = Real.exp (ε * t) *
        |sol.trajectory t iZeta - ζ3| := by
      rw [hw_eq, abs_mul, abs_of_pos (Real.exp_pos _)]
    have hExpPos_t : 0 < Real.exp (ε * t) := Real.exp_pos _
    have h_at_t' :
        Real.exp (ε * t) * |sol.trajectory t iZeta - ζ3|
          ≤ u0 + ε * K / (ε - κ) * (Real.exp ((ε - κ) * t) - 1) := by
      have := h_at_t
      rw [Real.norm_eq_abs, hAbsW] at this
      exact this
    have habs_bound :
        |sol.trajectory t iZeta - ζ3|
          ≤ (u0 + ε * K / (ε - κ) * (Real.exp ((ε - κ) * t) - 1))
            * Real.exp (-(ε * t)) := by
      have h_div : |sol.trajectory t iZeta - ζ3|
          ≤ (u0 + ε * K / (ε - κ) * (Real.exp ((ε - κ) * t) - 1))
              / Real.exp (ε * t) := by
        rw [le_div_iff₀ hExpPos_t, mul_comm]
        exact h_at_t'
      have h_eq : (u0 + ε * K / (ε - κ) * (Real.exp ((ε - κ) * t) - 1))
            / Real.exp (ε * t)
          = (u0 + ε * K / (ε - κ) * (Real.exp ((ε - κ) * t) - 1))
            * Real.exp (-(ε * t)) := by
        rw [Real.exp_neg, div_eq_mul_inv]
      linarith [h_div, h_eq]
    -- Simplify: (u0 + ε K/(ε−κ)·(e^((ε−κ)t) − 1)) · e^(−εt)
    --   = u0 · e^(−εt) + ε K/(ε−κ)·(e^(−κt) − e^(−εt))
    --   ≤ u0 · e^(−κt/2) + ε K/(ε−κ)·e^(−κt/2)
    have hE_identity : Real.exp ((ε - κ) * t) * Real.exp (-(ε * t))
        = Real.exp (-(κ * t)) := by
      rw [← Real.exp_add]; congr 1; ring
    have habs_bound2 :
        |sol.trajectory t iZeta - ζ3|
          ≤ u0 * Real.exp (-(ε * t))
            + ε * K / (ε - κ) *
              (Real.exp (-(κ * t)) - Real.exp (-(ε * t))) := by
      have hrewrite :
          (u0 + ε * K / (ε - κ) * (Real.exp ((ε - κ) * t) - 1))
              * Real.exp (-(ε * t))
            = u0 * Real.exp (-(ε * t))
              + ε * K / (ε - κ) *
                (Real.exp (-(κ * t)) - Real.exp (-(ε * t))) := by
        have h := hE_identity
        have : (u0 + ε * K / (ε - κ) * (Real.exp ((ε - κ) * t) - 1))
                * Real.exp (-(ε * t))
              = u0 * Real.exp (-(ε * t))
                + ε * K / (ε - κ) *
                  (Real.exp ((ε - κ) * t) * Real.exp (-(ε * t))
                    - Real.exp (-(ε * t))) := by ring
        rw [this, h]
      linarith [habs_bound, hrewrite]
    -- Further: both e^(−εt), e^(−κt) ≤ e^(−κt/2). Also e^(−κt) − e^(−εt) ≤ e^(−κt).
    have hε_ge_κ : κ ≤ ε := hcase.le
    have hκ_pos : (0 : ℝ) < κ := _hκ
    have hExp_neg_ε_le : Real.exp (-(ε * t)) ≤ Real.exp (-(κ / 2 * t)) := by
      apply Real.exp_le_exp.mpr
      have : κ / 2 * t ≤ ε * t := by
        apply mul_le_mul_of_nonneg_right _ ht
        linarith
      linarith
    have hExp_neg_κ_le : Real.exp (-(κ * t)) ≤ Real.exp (-(κ / 2 * t)) := by
      apply Real.exp_le_exp.mpr
      have : κ / 2 * t ≤ κ * t := by
        apply mul_le_mul_of_nonneg_right _ ht
        linarith
      linarith
    have hExp_neg_ε_pos : 0 < Real.exp (-(ε * t)) := Real.exp_pos _
    have hExp_neg_κ_pos : 0 < Real.exp (-(κ * t)) := Real.exp_pos _
    have hDiff_nonneg : 0 ≤ Real.exp (-(κ * t)) - Real.exp (-(ε * t)) := by
      have : Real.exp (-(ε * t)) ≤ Real.exp (-(κ * t)) := by
        apply Real.exp_le_exp.mpr
        have : κ * t ≤ ε * t := by
          apply mul_le_mul_of_nonneg_right hε_ge_κ ht
        linarith
      linarith
    have hDiff_le : Real.exp (-(κ * t)) - Real.exp (-(ε * t))
        ≤ Real.exp (-(κ / 2 * t)) := by
      calc Real.exp (-(κ * t)) - Real.exp (-(ε * t))
          ≤ Real.exp (-(κ * t)) := by linarith
        _ ≤ Real.exp (-(κ / 2 * t)) := hExp_neg_κ_le
    have hcoef_nn : 0 ≤ ε * K / (ε - κ) :=
      div_nonneg (mul_nonneg hε_pos.le _hK.le) hdiff_pos.le
    have habs_bound3 :
        |sol.trajectory t iZeta - ζ3|
          ≤ u0 * Real.exp (-(κ / 2 * t))
            + ε * K / (ε - κ) * Real.exp (-(κ / 2 * t)) := by
      have hA : u0 * Real.exp (-(ε * t))
          ≤ u0 * Real.exp (-(κ / 2 * t)) :=
        mul_le_mul_of_nonneg_left hExp_neg_ε_le hu0_nn
      have hB : ε * K / (ε - κ) *
          (Real.exp (-(κ * t)) - Real.exp (-(ε * t)))
          ≤ ε * K / (ε - κ) * Real.exp (-(κ / 2 * t)) :=
        mul_le_mul_of_nonneg_left hDiff_le hcoef_nn
      linarith
    -- Finally: u0 · e + εK/(ε−κ) · e ≤ (u0 + εK/(ε−κ) + 1) · e.
    have hfinal :
        u0 * Real.exp (-(κ / 2 * t))
          + ε * K / (ε - κ) * Real.exp (-(κ / 2 * t))
          ≤ (u0 + ε * K / (ε - κ) + 1) * Real.exp (-(κ / 2 * t)) := by
      have hExp_pos : 0 < Real.exp (-(κ / 2 * t)) := Real.exp_pos _
      have : (u0 + ε * K / (ε - κ) + 1) * Real.exp (-(κ / 2 * t))
          = u0 * Real.exp (-(κ / 2 * t))
            + ε * K / (ε - κ) * Real.exp (-(κ / 2 * t))
            + Real.exp (-(κ / 2 * t)) := by ring
      linarith
    show |sol.trajectory t iZeta - ζ3|
        ≤ (u0 + ε * K / (ε - κ) + 1) * Real.exp (-(κ / 2 * t))
    linarith [habs_bound3, hfinal]

/-- **(d)** Combined modulus is linear in `r`.  From (a)–(c) there
exist `K', κ' > 0` with `|ζ(t) − ζ(3)| ≤ K' exp(−κ' t)`; solving
`K' exp(−κ' t) < exp(−r)` for `t` gives a time modulus `μ(r)` linear
in `r`, which is the real-time (first-floor) bound.

**Construction.** Let `L = log K'` and `|L| = abs L`. Take
`μ(r) := (|L| + r + 2) / κ'` and `C := (|L| + 2) / κ'`.

*Positivity.* `0 < (|L| + 2)/κ'` since `|L| ≥ 0`, `2 > 0`, `κ' > 0`.

*Linear bound.* For `r ∈ ℕ`, `μ(r) = (|L| + r + 2)/κ'`;
`C · (r+1) = (|L|+2)(r+1)/κ' = (|L|(r+1) + 2r + 2)/κ'`; since
`r+1 ≥ 1` and `|L| ≥ 0` we have `|L|(r+1) ≥ |L|` and `2r + 2 ≥ r + 2`
so `C · (r+1) ≥ (|L| + r + 2)/κ' = μ(r)`.

*Convergence.* For `t > μ(r)`, first `t > 0` since
`μ(r) ≥ 2/κ' > 0`, so `_hζ` applies. Then `κ' t > |L| + r + 2 ≥ L + r`
so `exp(κ' t) > exp(L + r) = K' exp(r)`, whence
`K' exp(−κ' t) < exp(−r)`; combined with the `_hζ` bound this gives
strict `< exp(−r)`. -/
theorem apery_combined_linear_modulus
    (init : Fin 8 → ℚ)
    (sol : PIVP.Solution (apery8VarPolyPIVP init).toPIVP)
    (_hbdd : (apery8VarPolyPIVP init).toPIVP.IsBounded sol.trajectory)
    (K' κ' : ℝ) (hK' : 0 < K') (hκ' : 0 < κ')
    (hζ : ∀ t : ℝ, 0 ≤ t →
        |sol.trajectory t iZeta - (∑' k : ℕ, 1 / ((k + 1 : ℝ) ^ 3))|
          ≤ K' * Real.exp (-(κ' * t))) :
    ∃ (modulus : TimeModulus) (C : ℝ), 0 < C ∧
      (∀ r : ℕ, modulus r ≤ C * (↑r + 1)) ∧
      (∀ r : ℕ, ∀ t : ℝ, t > modulus r →
        |sol.trajectory t iZeta - (∑' k : ℕ, 1 / ((k + 1 : ℝ) ^ 3))|
          < Real.exp (-(r : ℝ))) := by
  set L : ℝ := Real.log K' with hL_def
  have habsL_nn : (0 : ℝ) ≤ |L| := abs_nonneg L
  have hL_le : L ≤ |L| := le_abs_self L
  -- μ(r) = (|L| + r + 2) / κ', C = (|L| + 2)/κ'
  refine ⟨fun r => (|L| + (r : ℝ) + 2) / κ', (|L| + 2) / κ', ?_, ?_, ?_⟩
  · -- 0 < (|L| + 2) / κ'
    exact div_pos (by linarith) hκ'
  · -- ∀ r, μ(r) ≤ C * (r+1)
    intro r
    have hr_nn : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
    rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hκ']
    -- goal: |L| + r + 2 ≤ (|L|+2) * (r+1)
    have hexpand : (|L| + 2) * ((r : ℝ) + 1) = |L| * (r + 1) + 2 * (r + 1) := by ring
    rw [hexpand]
    have h1 : |L| ≤ |L| * ((r : ℝ) + 1) := by
      have hr1 : (1 : ℝ) ≤ (r : ℝ) + 1 := by linarith
      calc |L| = |L| * 1 := (mul_one _).symm
        _ ≤ |L| * ((r : ℝ) + 1) := mul_le_mul_of_nonneg_left hr1 habsL_nn
    have h2 : (r : ℝ) + 2 ≤ 2 * ((r : ℝ) + 1) := by linarith
    linarith
  · intro r t ht
    -- μ(r) > 0
    have hmod_pos : (0 : ℝ) < (|L| + (r : ℝ) + 2) / κ' := by
      apply div_pos _ hκ'
      have hr_nn : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
      linarith
    -- t > 0
    have ht_pos : 0 < t := lt_trans hmod_pos ht
    have ht_nn : 0 ≤ t := le_of_lt ht_pos
    -- apply hζ
    have hbound := hζ t ht_nn
    -- κ' * t > |L| + r + 2
    have hkappa_t : |L| + (r : ℝ) + 2 < κ' * t := by
      have h := (div_lt_iff₀ hκ').mp ht
      linarith
    -- hence κ' * t > L + r
    have hLr : L + (r : ℝ) < κ' * t := by linarith
    -- K' * exp(-κ' t) < exp(-r)
    have hK'_exp : K' = Real.exp L := (Real.exp_log hK').symm
    have step : K' * Real.exp (-(κ' * t)) < Real.exp (-(r : ℝ)) := by
      rw [hK'_exp, ← Real.exp_add]
      apply Real.exp_lt_exp.mpr
      linarith
    exact lt_of_le_of_lt hbound step

/-! ## Main theorem

  Assembles (a)–(d) into the real-time computability statement,
  **conditional** on two hypotheses that encode what the analytical
  content needs from an admissible initial vector:

  * `h_invariant` — a forward-invariant sup-norm ball of radius `M`
    around `init`; consumed by (a);
  * `h_z_init` — the initial z-coordinate lies in the conifold basin
    `(0, z₁)` with `z₁ = 17 − 12√2`; consumed by (b) via the Frobenius
    witness.

  Producing these two hypotheses for a concrete Taylor-truncation
  `init` at `z₀ = 1/1000` is pure Frobenius/Apéry analysis and is
  what `apery_conifold_frobenius_witness` is really about; once that
  witness is closed, choosing any such `init` and discharging the
  invariance hypothesis (by a dynamical-systems argument on the ball
  around the conifold attractor) gives the unconditional statement
  `IsRealTimeComputable ζ(3)` as an immediate corollary.

  **No axioms added by this file.** The remaining sorries, as of this
  commit, are concentrated in `apery_conifold_frobenius_witness` (the
  single analytic gap).
-/

/--
**Main statement (conditional).**  ζ(3) is real-time (first-floor)
CRN-computable via the 8-variable Apéry adaptation PIVP, given:

  * a rational initial vector `init` whose first coordinate `init iZ`
    is in the open conifold basin `(0, 17 − 12√2)`;
  * a forward-invariant sup-norm ball of radius `M` around `init`
    for the Apéry 8-var vector field.

**Proof structure.**  Assembles (a)–(d):

  (a) `apery_exists_bounded_trajectory` — bounded global trajectory
      from `h_invariant`;
  (b) `apery_ratio_converges_exponentially` — ρ → ζ(3) at rate
      `K·e^(−κt)`, by `apery_conifold_frobenius_witness`;
  (c) `apery_adaptation_tracks_ratio` — ζ tracks ρ with rate
      `K'·e^(−κ't)` (scalar linear ODE fencing);
  (d) `apery_combined_linear_modulus` — invert to a linear-in-`r`
      modulus, i.e. real-time.

The bridge from (d)'s existential `modulus` to the
`IsRealTimeComputable` record is now algebraic: package as a
`BoundedTimeComputable 8`, read off `convergence` from (d)'s output
and `modulus r ≤ C(r+1)` from (d)'s linear-bound clause.
-/
theorem apery_real_time_from_adaptation
    (init : Fin 8 → ℚ)
    (M : ℝ) (hM : 0 < M)
    (h_invariant : ∀ (T : ℝ), 0 < T → ∀ (y : ℝ → Fin 8 → ℝ),
      y 0 = (fun i => ((init i : ℚ) : ℝ)) →
      (∀ t ∈ Set.Ico (0 : ℝ) T,
        HasDerivAt y ((apery8VarPolyPIVP init).toPIVP.field (y t)) t) →
      ∀ t ∈ Set.Ico (0 : ℝ) T, ‖y t‖ ≤ M)
    (h_z_init : (0 : ℝ) < ((init iZ : ℚ) : ℝ) ∧
                ((init iZ : ℚ) : ℝ) < 17 - 12 * Real.sqrt 2) :
    IsRealTimeComputable (∑' k : ℕ, 1 / ((k + 1 : ℝ) ^ 3)) := by
  -- (a) bounded global trajectory.
  obtain ⟨sol, hbdd⟩ :=
    apery_exists_bounded_trajectory init M hM h_invariant
  -- (b) ρ(t) → ζ(3) exponentially.
  obtain ⟨K, κ, hK, hκ, hρ⟩ :=
    apery_ratio_converges_exponentially init sol hbdd h_z_init
  -- (c) ζ(t) tracks ρ(t) exponentially ⇒ ζ(t) → ζ(3) exponentially.
  obtain ⟨K', κ', hK', hκ', hζ⟩ :=
    apery_adaptation_tracks_ratio init sol hbdd K κ hK hκ hρ
  -- (d) Linear-in-r modulus from exponential convergence.
  obtain ⟨modulus, C, hC, hlin, hconv⟩ :=
    apery_combined_linear_modulus init sol hbdd K' κ' hK' hκ' hζ
  -- Package as `IsRealTimeComputable`.
  refine ⟨8,
    { pivp := (apery8VarPolyPIVP init).toPIVP,
      sol := sol,
      modulus := modulus,
      bounded := hbdd,
      convergence := ?_ },
    C, hC, hlin⟩
  intro r t ht
  have hconv' := hconv r t ht
  -- Output index is `iZeta` by definition of `apery8VarPolyPIVP`.
  show |sol.trajectory t (apery8VarPolyPIVP init).toPIVP.output -
        (∑' k : ℕ, 1 / ((k + 1 : ℝ) ^ 3))| < Real.exp (-(r : ℝ))
  have houtput : (apery8VarPolyPIVP init).toPIVP.output = iZeta := rfl
  rw [houtput]
  exact hconv'

end Ripple.Number
