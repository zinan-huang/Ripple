/-
Ripple.BoundedUniversality.GPAC.SurrogateCompileGlobalODE
--------------------------
Bridge from surrogateCompileOneVar to Ripple's global ODE existence.

The compiled PIVP from surrogateCompileOneVar has:
- Polynomial vector field → locally Lipschitz
- Surrogate variables ∈ [0,1] → bounded invariant set

Ripple.locally_lipschitz_bounded_global_ode_proved then gives a global
solution with HasDerivAt. This is the key analytical bridge.
-/

import Ripple.BoundedUniversality.GPAC.SurrogateCompile
import Ripple.BoundedUniversality.GPAC.StrongSemantics
import Ripple.BoundedUniversality.GPAC.TimeChange
import Ripple.Core.ODEGlobal
import Ripple.LPP.Stages

namespace Ripple.BoundedUniversality.GPAC

private theorem mvPolynomial_eval₂_contDiff
    {K : Type*} [Field K] [Algebra K ℝ]
    {d : ℕ} (p : MvPolynomial (Fin d) K) :
    ContDiff ℝ ⊤ (fun x : Fin d → ℝ => p.eval₂ (algebraMap K ℝ) x) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    simp only [MvPolynomial.eval₂_C]
    exact contDiff_const
  | add p q hp hq =>
    simp only [MvPolynomial.eval₂_add]
    exact hp.add hq
  | mul_X p i hp =>
    have h_eval : ∀ x : Fin d → ℝ,
        (p * MvPolynomial.X i).eval₂ (algebraMap K ℝ) x
          = p.eval₂ (algebraMap K ℝ) x * x i := by
      intro x
      rw [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X]
    simp only [h_eval]
    exact hp.mul (contDiff_apply ℝ ℝ i)

/-- Polynomial vector fields are locally Lipschitz. This is a
consequence of polynomial functions being smooth (C∞), hence
locally Lipschitz on bounded sets.

For the formalization, this uses the fact that MvPolynomial evaluation
is continuous and differentiable, hence Lipschitz on compact sets. -/
theorem polyVF_locally_lipschitz
    {K : Type*} [Field K] [Algebra K ℝ]
    (P : PIVP K) :
    ∀ R : ℝ, 0 < R → ∃ L : ℝ, ∀ x y : Fin P.n → ℝ,
      ‖x‖ ≤ R → ‖y‖ ≤ R → ‖P.evalVF x - P.evalVF y‖ ≤ L * ‖x - y‖ := by
  have h_cd_comp :
      ∀ i : Fin P.n,
        ContDiff ℝ ⊤ (fun x : Fin P.n → ℝ => P.evalVF x i) := by
    intro i
    have h_eq :
        (fun x : Fin P.n → ℝ => P.evalVF x i)
          = fun x => (P.vf i).eval₂ (algebraMap K ℝ) x := by
      funext x
      rfl
    rw [h_eq]
    exact mvPolynomial_eval₂_contDiff (P.vf i)
  have h_cd : ContDiff ℝ ⊤ (fun x : Fin P.n → ℝ =>
      (fun i => P.evalVF x i : Fin P.n → ℝ)) :=
    contDiff_pi' h_cd_comp
  exact Ripple.contDiff_locally_lipschitz h_cd

/-- The compiled PIVP has a global ODE solution, obtained by
applying Ripple's global existence theorem to the polynomial
vector field with surrogate-bounded invariant set.

This bridges Ripple.BoundedUniversality's types to Ripple's proven ODE existence.

The premise `h_inv` assumes the a-priori bound of every local solution, which is what a
compilation theorem has to prove; the theorem has no consumer. For the joint compiled system of
[BAC] Construction 3.1 the solution and its bound are proved directly
(`Ripple.PolyPIVP.jointSurrogateCompile_solution`, `Ripple.jointSurrogateCompile_isBounded`). -/
theorem compiled_pivp_has_strong_semantics
    {K : Type*} [Field K] [Algebra K ℝ]
    (P' : PIVP K) (w : ℕ)
    (h_lip : ∀ R : ℝ, 0 < R → ∃ L : ℝ, ∀ x y : Fin P'.n → ℝ,
      ‖x‖ ≤ R → ‖y‖ ≤ R → ‖P'.evalVF x - P'.evalVF y‖ ≤ L * ‖x - y‖)
    (M : ℝ) (hM : 0 < M)
    (h_inv : ∀ (T : ℝ), 0 < T → ∀ (y : ℝ → Fin P'.n → ℝ),
      y 0 = P'.realInit w →
      (∀ t ∈ Set.Ico (0 : ℝ) T, HasDerivAt y (P'.evalVF (y t)) t) →
      ∀ t ∈ Set.Ico (0 : ℝ) T, ‖y t‖ ≤ M) :
    ∃ traj : ℝ → Fin P'.n → ℝ,
      traj 0 = P'.realInit w ∧
      (∀ t : ℝ, 0 ≤ t → HasDerivAt traj (P'.evalVF (traj t)) t) ∧
      (∀ t : ℝ, 0 ≤ t → ‖traj t‖ ≤ M) := by
  obtain ⟨y, hy0, hode⟩ :=
    Ripple.locally_lipschitz_bounded_global_ode_proved
      P'.evalVF (P'.realInit w) h_lip M hM h_inv
  refine ⟨y, hy0, hode, fun t ht => ?_⟩
  -- The bound follows from h_inv applied to [0, t+1) which contains t
  have := h_inv (t + 1) (by linarith) y hy0
    (fun s hs => hode s (by exact hs.1))
  exact this t ⟨ht, by linarith⟩

-- No forward-invariance argument is needed for the joint construction of [BAC] Construction
-- 3.1: the compiled solution is built as `τ ↦ (y_o(s τ), (W_a(y(s τ)))_a)` and the bound
-- `|W_a| ≤ 1` is algebraic (`Ripple.jointSurrogate_abs_le_one`). See
-- `Ripple/Core/SurrogateCompilation.lean` and `docs/refactor/BC.md`.

end Ripple.BoundedUniversality.GPAC
