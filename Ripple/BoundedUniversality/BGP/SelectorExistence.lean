import Ripple.BoundedUniversality.BGP.SelectorFinalAssembly
import Ripple.Core.ODEGlobal
import Ripple.Core.ODEFiniteTime
import Mathlib

/-!
Ripple.BoundedUniversality.BGP.SelectorExistence
----------------------------
Analytic solution-existence layer for the clock-driven selector field.

This file is intentionally additive.  It builds the Picard/existence wrapper for
the already-defined autonomous selector polynomial field
`selectorAssembledField`, then packages the resulting trajectory as a
`SelectorDynSol`.

The one genuinely missing analytic ingredient is carried explicitly as a named
hypothesis: the global a-priori boundedness predicate required by
`Ripple.locally_lipschitz_bounded_global_ode_proved_continuous`.  This cannot be
discharged by the CONTRACT bounded-ball argument as-is, because the selector
state contains the unbounded clock coordinates `μ' = cμ` and `α' = cα·α`.
-/

noncomputable section

namespace Ripple.BoundedUniversality.BGP

open scoped BigOperators
open MvPolynomial Set

private theorem locallyLipschitz_pi_lip_on_closedBall {n : ℕ}
    (f : (Fin n → ℝ) → Fin n → ℝ)
    (hcoord : ∀ k : Fin n, LocallyLipschitz fun x : Fin n → ℝ => f x k) :
    ∀ R : ℝ, 0 < R → ∃ L : ℝ, ∀ x y : Fin n → ℝ,
      ‖x‖ ≤ R → ‖y‖ ≤ R → ‖f x - f y‖ ≤ L * ‖x - y‖ := by
  intro R hR
  let s : Set (Fin n → ℝ) := Metric.closedBall 0 R
  have hs : IsCompact s := isCompact_closedBall _ _
  have hloc : ∀ k : Fin n, LocallyLipschitzOn s (fun x : Fin n → ℝ => f x k) :=
    fun k => (hcoord k).locallyLipschitzOn
  have hK : ∀ k : Fin n, ∃ K : NNReal,
      LipschitzOnWith K (fun x : Fin n → ℝ => f x k) s :=
    fun k => LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hs (hloc k)
  choose K hKlip using hK
  refine ⟨(∑ k : Fin n, (K k : ℝ)), ?_⟩
  intro x y hx hy
  have hxmem : x ∈ s := by simpa [s, Metric.mem_closedBall, dist_zero_right] using hx
  have hymem : y ∈ s := by simpa [s, Metric.mem_closedBall, dist_zero_right] using hy
  rw [← dist_eq_norm]
  have hnonneg : 0 ≤ (∑ k : Fin n, (K k : ℝ)) * ‖x - y‖ := by
    exact mul_nonneg (Finset.sum_nonneg fun k _ => (K k).2) (norm_nonneg _)
  apply (dist_pi_le_iff hnonneg).2
  intro k
  have hk := (hKlip k).dist_le_mul x hxmem y hymem
  rw [dist_eq_norm] at hk
  calc
    dist (f x k) (f y k) ≤ (K k : ℝ) * ‖x - y‖ := by
      simpa [dist_eq_norm] using hk
    _ ≤ (∑ j : Fin n, (K j : ℝ)) * ‖x - y‖ := by
      have hle : (K k : ℝ) ≤ ∑ j : Fin n, (K j : ℝ) :=
        Finset.single_le_sum (fun j _ => (K j).2) (Finset.mem_univ k)
      exact mul_le_mul_of_nonneg_right hle (norm_nonneg _)

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

private noncomputable def clamp (C x : ℝ) : ℝ := max (-C) (min C x)

private theorem abs_clamp_le {C x : ℝ} (hC : 0 ≤ C) : |clamp C x| ≤ C := by
  rw [abs_le]
  constructor
  · unfold clamp
    exact le_max_left _ _
  · unfold clamp
    exact max_le (by linarith) (min_le_left C x)

/-- Clipped selector mixture target, used only in the `z` Reach coordinates. -/
def selectorClippedMixCoord
    {d B : ℕ} {V : Type} [Fintype V]
    (branch : V → BranchData d B) (C : ℝ)
    (y : Fin (selectorDim d V) → ℝ) (i : Fin d) : ℝ :=
  clamp C
    (selectorF branch
      (fun j => y (selU V j))
      (fun v => y (selLamCoord v)) i)

theorem selectorClippedMixCoord_abs_le
    {d B : ℕ} {V : Type} [Fintype V]
    (branch : V → BranchData d B) {C : ℝ} (hC : 0 ≤ C)
    (y : Fin (selectorDim d V) → ℝ) (i : Fin d) :
    |selectorClippedMixCoord branch C y i| ≤ C := by
  exact abs_clamp_le hC

/-- Euclidean selector polynomial field as a vector field on `Fin (selectorDim d V)`. -/
def selectorAssembledVectorField
    (d B : ℕ) (V : Type) [Fintype V]
    (branch : V → BranchData d B)
    (chiResetP chiGateP kappaP gainP : MvPolynomial (Fin (selectorDim d V)) ℚ)
    (PpolyP : V → MvPolynomial (Fin (selectorDim d V)) ℚ)
    (HP : MvPolynomial (Fin d) ℚ)
    (Aq Kq cμq cαq : ℚ) (L R : ℕ) :
    (Fin (selectorDim d V) → ℝ) → Fin (selectorDim d V) → ℝ :=
  fun y i =>
    MvPolynomial.eval₂ (algebraMap ℚ ℝ) y
      (selectorAssembledField d B V branch chiResetP chiGateP kappaP gainP PpolyP HP
        Aq Kq cμq cαq L R i)

/--
Clipped selector vector field.  It agrees with `selectorAssembledVectorField`
except on the `z` coordinates, where the dynamic selector mixture is clamped
componentwise before the Reach term.
-/
def selectorClippedAssembledVectorField
    (d B : ℕ) (V : Type) [Fintype V]
    (branch : V → BranchData d B) (Cclip : ℝ)
    (chiResetP chiGateP kappaP gainP : MvPolynomial (Fin (selectorDim d V)) ℚ)
    (PpolyP : V → MvPolynomial (Fin (selectorDim d V)) ℚ)
    (HP : MvPolynomial (Fin d) ℚ)
    (Aq Kq cμq cαq : ℚ) (L R : ℕ) :
    (Fin (selectorDim d V) → ℝ) → Fin (selectorDim d V) → ℝ :=
  fun y k =>
    if h : ∃ i : Fin d, k = selZ V i then
      let i : Fin d := Classical.choose h
      (Aq : ℝ) * y (selOfContract V (contractAlpha d)) *
        y (selOfContract V (contractGateZ d)) *
          (selectorClippedMixCoord branch Cclip y i - y (selZ V i))
    else
      selectorAssembledVectorField d B V branch
        chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R y k

theorem selectorClippedAssembledVectorField_lip_of_coord
    (d B : ℕ) (V : Type) [Fintype V]
    (branch : V → BranchData d B) (Cclip : ℝ)
    (chiResetP chiGateP kappaP gainP : MvPolynomial (Fin (selectorDim d V)) ℚ)
    (PpolyP : V → MvPolynomial (Fin (selectorDim d V)) ℚ)
    (HP : MvPolynomial (Fin d) ℚ)
    (Aq Kq cμq cαq : ℚ) (L R : ℕ)
    (hcoord : ∀ k : Fin (selectorDim d V),
      LocallyLipschitz fun y : Fin (selectorDim d V) → ℝ =>
        selectorClippedAssembledVectorField d B V branch Cclip
          chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R y k) :
    ∀ Rb : ℝ, 0 < Rb → ∃ Lb : ℝ,
      ∀ x y : Fin (selectorDim d V) → ℝ,
        ‖x‖ ≤ Rb → ‖y‖ ≤ Rb →
          ‖selectorClippedAssembledVectorField d B V branch Cclip
              chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R x
            - selectorClippedAssembledVectorField d B V branch Cclip
              chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R y‖
            ≤ Lb * ‖x - y‖ :=
  locallyLipschitz_pi_lip_on_closedBall
    (selectorClippedAssembledVectorField d B V branch Cclip
      chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R)
    hcoord

theorem selectorAssembledVectorField_coord_locallyLipschitz
    (d B : ℕ) (V : Type) [Fintype V]
    (branch : V → BranchData d B)
    (chiResetP chiGateP kappaP gainP : MvPolynomial (Fin (selectorDim d V)) ℚ)
    (PpolyP : V → MvPolynomial (Fin (selectorDim d V)) ℚ)
    (HP : MvPolynomial (Fin d) ℚ)
    (Aq Kq cμq cαq : ℚ) (L R : ℕ) :
    ∀ k : Fin (selectorDim d V),
      LocallyLipschitz fun y : Fin (selectorDim d V) → ℝ =>
        selectorAssembledVectorField d B V branch
          chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R y k := by
  intro k
  unfold selectorAssembledVectorField
  exact ((mvPolynomial_eval₂_contDiff
    (K := ℚ)
    (selectorAssembledField d B V branch chiResetP chiGateP kappaP gainP PpolyP HP
      Aq Kq cμq cαq L R k)).of_le (by simp)).locallyLipschitz

private lemma selectorAssembledField_z_eq
    {d B : ℕ} {V : Type} [Fintype V]
    (branch : V → BranchData d B)
    (chiReset chiGate kappa gainPoly : MvPolynomial (Fin (selectorDim d V)) ℚ)
    (Ppoly : V → MvPolynomial (Fin (selectorDim d V)) ℚ)
    (HP : MvPolynomial (Fin d) ℚ) (A K cμ cα : ℚ) (L R : ℕ) (i : Fin d) :
    selectorAssembledField d B V branch chiReset chiGate kappa gainPoly Ppoly HP A K cμ cα L R
        (selZ V i) =
      C A * X (selOfContract V (contractAlpha d)) *
        X (selOfContract V (contractGateZ d)) *
        (selectorMixField branch i - X (selZ V i)) := by
  simp [selectorAssembledField, selZ, selOfContract, contractZ, contractTailZ]

private lemma selectorAssembledField_u_eq
    {d B : ℕ} {V : Type} [Fintype V]
    (branch : V → BranchData d B)
    (chiReset chiGate kappa gainPoly : MvPolynomial (Fin (selectorDim d V)) ℚ)
    (Ppoly : V → MvPolynomial (Fin (selectorDim d V)) ℚ)
    (HP : MvPolynomial (Fin d) ℚ) (A K cμ cα : ℚ) (L R : ℕ) (i : Fin d) :
    selectorAssembledField d B V branch chiReset chiGate kappa gainPoly Ppoly HP A K cμ cα L R
        (selU V i) =
      C A * X (selOfContract V (contractAlpha d)) *
        X (selOfContract V (contractGateU d)) *
        (X (selZ V i) - X (selU V i)) := by
  simp [selectorAssembledField, selU, selZ, selOfContract, contractU, contractTailU]

private lemma selectorAssembledField_lam_eq
    {d B : ℕ} {V : Type} [Fintype V]
    (branch : V → BranchData d B)
    (chiReset chiGate kappa gainPoly : MvPolynomial (Fin (selectorDim d V)) ℚ)
    (Ppoly : V → MvPolynomial (Fin (selectorDim d V)) ℚ)
    (HP : MvPolynomial (Fin d) ℚ) (A K cμ cα : ℚ) (L R : ℕ) (v : V) :
    selectorAssembledField d B V branch chiReset chiGate kappa gainPoly Ppoly HP A K cμ cα L R
        (selLamCoord v) =
      selectorResetGateFieldPoly chiReset chiGate kappa gainPoly (Ppoly v) (selLamCoord v) := by
  simp only [selectorAssembledField, selLamCoord, Fin.append_right, Fin.append_left,
    Equiv.symm_apply_apply]

private lemma selectorAssembledField_G_eq
    {d B : ℕ} {V : Type} [Fintype V]
    (branch : V → BranchData d B)
    (chiReset chiGate kappa gainPoly : MvPolynomial (Fin (selectorDim d V)) ℚ)
    (Ppoly : V → MvPolynomial (Fin (selectorDim d V)) ℚ)
    (HP : MvPolynomial (Fin d) ℚ) (A K cμ cα : ℚ) (L R : ℕ) :
    selectorAssembledField d B V branch chiReset chiGate kappa gainPoly Ppoly HP A K cμ cα L R
        (selGCoord d V) =
      selectorGainFieldPoly chiGate gainPoly := by
  simp [selectorAssembledField, selGCoord, Fin.append_right]
  rfl

private lemma selectorAssembledField_mu_eq
    {d B : ℕ} {V : Type} [Fintype V]
    (branch : V → BranchData d B)
    (chiReset chiGate kappa gainPoly : MvPolynomial (Fin (selectorDim d V)) ℚ)
    (Ppoly : V → MvPolynomial (Fin (selectorDim d V)) ℚ)
    (HP : MvPolynomial (Fin d) ℚ) (A K cμ cα : ℚ) (L R : ℕ) :
    selectorAssembledField d B V branch chiReset chiGate kappa gainPoly Ppoly HP A K cμ cα L R
        (selOfContract V (contractMu d)) = C cμ := by
  simp [selectorAssembledField, selOfContract, contractMu, contractS]

private lemma selectorAssembledField_alpha_eq
    {d B : ℕ} {V : Type} [Fintype V]
    (branch : V → BranchData d B)
    (chiReset chiGate kappa gainPoly : MvPolynomial (Fin (selectorDim d V)) ℚ)
    (Ppoly : V → MvPolynomial (Fin (selectorDim d V)) ℚ)
    (HP : MvPolynomial (Fin d) ℚ) (A K cμ cα : ℚ) (L R : ℕ) :
    selectorAssembledField d B V branch chiReset chiGate kappa gainPoly Ppoly HP A K cμ cα L R
        (selOfContract V (contractAlpha d)) =
      C cα * X (selOfContract V (contractAlpha d)) := by
  simp [selectorAssembledField, selOfContract, contractAlpha, contractS]

theorem selectorAssembledVectorField_lip
    (d B : ℕ) (V : Type) [Fintype V]
    (branch : V → BranchData d B)
    (chiResetP chiGateP kappaP gainP : MvPolynomial (Fin (selectorDim d V)) ℚ)
    (PpolyP : V → MvPolynomial (Fin (selectorDim d V)) ℚ)
    (HP : MvPolynomial (Fin d) ℚ)
    (Aq Kq cμq cαq : ℚ) (L R : ℕ) :
    ∀ Rb : ℝ, 0 < Rb → ∃ Lb : ℝ,
      ∀ x y : Fin (selectorDim d V) → ℝ,
        ‖x‖ ≤ Rb → ‖y‖ ≤ Rb →
          ‖selectorAssembledVectorField d B V branch
              chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R x
            - selectorAssembledVectorField d B V branch
              chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R y‖
            ≤ Lb * ‖x - y‖ :=
  locallyLipschitz_pi_lip_on_closedBall
    (selectorAssembledVectorField d B V branch
      chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R)
    (selectorAssembledVectorField_coord_locallyLipschitz d B V branch
      chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R)

/--
Named a-priori boundedness assumption needed by the current Picard engine.

For selector fields this is the exact remaining analytic gap: unlike the boxed
CONTRACT iterator, the Euclidean selector field contains unbounded clock
coordinates (`μ`, `α`, and generally `G`), so the existing bounded-global ODE
engine cannot be applied without either a compactifying coordinate change or a
new global-existence theorem with finite-time bounds.
-/
def SelectorAssembledBoundedHyp
    {d B : ℕ} {V : Type} [Fintype V]
    (branch : V → BranchData d B)
    (chiResetP chiGateP kappaP gainP : MvPolynomial (Fin (selectorDim d V)) ℚ)
    (PpolyP : V → MvPolynomial (Fin (selectorDim d V)) ℚ)
    (HP : MvPolynomial (Fin d) ℚ)
    (Aq Kq cμq cαq : ℚ) (L R : ℕ)
    (y₀ : Fin (selectorDim d V) → ℝ) (M : ℝ) : Prop :=
  ∀ (T : ℝ), 0 < T → ∀ (y : ℝ → Fin (selectorDim d V) → ℝ),
    y 0 = y₀ →
    (∀ t ∈ Set.Ico (0 : ℝ) T,
      HasDerivAt y
        (selectorAssembledVectorField d B V branch
          chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R (y t)) t) →
    ∀ t ∈ Set.Ico (0 : ℝ) T, ‖y t‖ ≤ M

theorem selector_assembled_global_solution
    {d B : ℕ} {V : Type} [Fintype V]
    (branch : V → BranchData d B)
    (chiResetP chiGateP kappaP gainP : MvPolynomial (Fin (selectorDim d V)) ℚ)
    (PpolyP : V → MvPolynomial (Fin (selectorDim d V)) ℚ)
    (HP : MvPolynomial (Fin d) ℚ)
    (Aq Kq cμq cαq : ℚ) (L R : ℕ)
    (y₀ : Fin (selectorDim d V) → ℝ)
    (M : ℝ) (hM : 0 < M)
    (hbounded : SelectorAssembledBoundedHyp branch chiResetP chiGateP kappaP gainP
      PpolyP HP Aq Kq cμq cαq L R y₀ M) :
    ∃ y : ℝ → Fin (selectorDim d V) → ℝ,
      y 0 = y₀ ∧
      (∀ t : ℝ, 0 ≤ t →
        HasDerivAt y
          (selectorAssembledVectorField d B V branch
            chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R (y t)) t) ∧
      Continuous y := by
  exact Ripple.locally_lipschitz_bounded_global_ode_proved_continuous
    (selectorAssembledVectorField d B V branch
      chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R)
    y₀
    (selectorAssembledVectorField_lip d B V branch
      chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R)
    M hM hbounded

/--
**Sound global solution via the finite-time-bounds engine.**

The selector Euclidean state contains the unbounded clock coordinates `μ' = cμ` and `α' = cα·α`,
so the *uniform*-ball hypothesis `SelectorAssembledBoundedHyp` is UNSATISFIABLE (no single `M` bounds
`α(t) = exp(cα·t) → ∞`) — making `selector_assembled_global_solution` vacuous.  This replacement uses
`Ripple.locally_lipschitz_finitetime_global_ode_continuous`, whose a-priori bound `FiniteHorizonBound`
is *prefix-uniform* (the bound may depend on the horizon `T`).  That hypothesis IS satisfiable for the
selector field: the fiber coordinates `(z, u, λ)` are bounded by a uniform box (branch-contraction +
logistic invariance) and the clock coordinates `α, μ, G, gates` are bounded on every finite
`[0, T]`.
-/
theorem selector_assembled_global_solution_finitetime
    {d B : ℕ} {V : Type} [Fintype V]
    (branch : V → BranchData d B)
    (chiResetP chiGateP kappaP gainP : MvPolynomial (Fin (selectorDim d V)) ℚ)
    (PpolyP : V → MvPolynomial (Fin (selectorDim d V)) ℚ)
    (HP : MvPolynomial (Fin d) ℚ)
    (Aq Kq cμq cαq : ℚ) (L R : ℕ)
    (y₀ : Fin (selectorDim d V) → ℝ)
    (hfin : Ripple.FiniteHorizonBound
      (selectorAssembledVectorField d B V branch
        chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R) y₀) :
    ∃ y : ℝ → Fin (selectorDim d V) → ℝ,
      y 0 = y₀ ∧
      (∀ t : ℝ, 0 ≤ t →
        HasDerivAt y
          (selectorAssembledVectorField d B V branch
            chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R (y t)) t) ∧
      Continuous y :=
  Ripple.locally_lipschitz_finitetime_global_ode_continuous
    (selectorAssembledVectorField d B V branch
      chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R)
    y₀
    (selectorAssembledVectorField_lip d B V branch
      chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R)
    hfin

/--
Field solution packaged as an explicit-time `SelectorDynSol`.

This is the same bridge as `selectorDynSol_of_selectorAssembledField_solution`,
but the phase/readout functions are supplied as explicit target functions
through realization hypotheses.  This is the form needed by the M_U selector
path, where the intended functions are
`((1+cos t)/2)^M`, `((1+sin t)/2)^M`, `κ₀`, and
`g₀ * exp(cα*t)`.
-/
noncomputable def selectorDynSol_of_selectorAssembledField_solution_explicit
    {d B : ℕ} {V : Type} [Fintype V]
    (p : DynGateParams) (sched : PhaseSchedule)
    (branch : V → BranchData d B)
    (chiResetP chiGateP kappaP gainP : MvPolynomial (Fin (selectorDim d V)) ℚ)
    (PpolyP : V → MvPolynomial (Fin (selectorDim d V)) ℚ)
    (HP : MvPolynomial (Fin d) ℚ)
    {Aq Kq cμq cαq : ℚ} {L R : ℕ}
    (hA : p.A = (Aq : ℝ)) (hcμ : p.cμ = (cμq : ℝ)) (hcα : p.cα = (cαq : ℝ))
    (hL : p.L = L)
    (hdomain_nonneg : ∀ t : ℝ, t ∈ sched.domain → 0 ≤ t)
    (y : ℝ → Fin (selectorDim d V) → ℝ)
    (hyode : ∀ t : ℝ, 0 ≤ t →
      HasDerivAt y
        (selectorAssembledVectorField d B V branch
          chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R (y t)) t)
    (hycont : Continuous y)
    (hgateZ : ∀ t : ℝ, 0 ≤ t →
      y t (selOfContract V (contractGateZ d)) =
        bGateZ L (y t (selOfContract V (contractMu d))) t)
    (hgateU : ∀ t : ℝ, 0 ≤ t →
      y t (selOfContract V (contractGateU d)) =
        bGateU L (y t (selOfContract V (contractMu d))) t)
    (chiResetF chiGateF kappaF gainF : ℝ → ℝ)
    (readoutP : V → (Fin d → ℝ) → ℝ)
    (hα0 : y 0 (selOfContract V (contractAlpha d)) = 1)
    (h_chiReset : ∀ t : ℝ, 0 ≤ t →
      MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t) chiResetP = chiResetF t)
    (h_chiGate : ∀ t : ℝ, 0 ≤ t →
      MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t) chiGateP = chiGateF t)
    (h_kappa : ∀ t : ℝ, 0 ≤ t →
      MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t) kappaP = kappaF t)
    (h_gain : ∀ t : ℝ, 0 ≤ t →
      MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t) gainP = gainF t)
    (h_P : ∀ (v : V) (t : ℝ), 0 ≤ t →
      MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t) (PpolyP v) =
        readoutP v (fun i => y t (selU V i)))
    (hμ0 : y 0 (selOfContract V (contractMu d)) = 0) :
    SelectorDynSol d B V p sched branch chiResetF chiGateF kappaF gainF readoutP := by
  classical
  refine
    { z := fun t i => y t (selZ V i)
      u := fun t i => y t (selU V i)
      lam := fun v t => y t (selLamCoord v)
      G := fun t => y t (selGCoord d V)
      μ := fun t => y t (selOfContract V (contractMu d))
      α := fun t => y t (selOfContract V (contractAlpha d))
      init_z := fun i => y 0 (selZ V i)
      init_u := fun i => y 0 (selU V i)
      z_at_zero := rfl
      u_at_zero := rfl
      α_at_zero := hα0
      μ_at_zero := hμ0
      cont_z := fun i => (continuous_apply (selZ V i)).comp hycont
      cont_u := fun i => (continuous_apply (selU V i)).comp hycont
      cont_lam := fun v => (continuous_apply (selLamCoord v)).comp hycont
      cont_G := (continuous_apply (selGCoord d V)).comp hycont
      z_hasDeriv := ?_
      u_hasDeriv := ?_
      lam_hasDeriv := ?_
      G_hasDeriv := ?_
      μ_hasDeriv := ?_
      α_hasDeriv := ?_ }
  · intro t ht i
    have ht0 : 0 ≤ t := hdomain_nonneg t ht
    have hcoord := (hasDerivAt_pi.mp (hyode t ht0)) (selZ V i)
    have heq :
        selectorAssembledVectorField d B V branch
            chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R
            (y t) (selZ V i) =
          p.A * y t (selOfContract V (contractAlpha d)) *
            bGateZ p.L (y t (selOfContract V (contractMu d))) t *
            (selectorMixTarget branch (fun t i => y t (selU V i))
                (fun v t => y t (selLamCoord v)) t i - y t (selZ V i)) := by
      unfold selectorAssembledVectorField
      rw [selectorAssembledField_z_eq]
      simp [selectorMixField, selectorMixTarget, selectorF, hgateZ t ht0, hA, hL]
    exact heq ▸ hcoord
  · intro t ht i
    have ht0 : 0 ≤ t := hdomain_nonneg t ht
    have hcoord := (hasDerivAt_pi.mp (hyode t ht0)) (selU V i)
    have heq :
        selectorAssembledVectorField d B V branch
            chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R
            (y t) (selU V i) =
          p.A * y t (selOfContract V (contractAlpha d)) *
            bGateU p.L (y t (selOfContract V (contractMu d))) t *
            (y t (selZ V i) - y t (selU V i)) := by
      unfold selectorAssembledVectorField
      rw [selectorAssembledField_u_eq]
      simp [hgateU t ht0, hA, hL]
    exact heq ▸ hcoord
  · intro v t ht
    have ht0 : 0 ≤ t := hdomain_nonneg t ht
    have hcoord := (hasDerivAt_pi.mp (hyode t ht0)) (selLamCoord v)
    have heq :
        selectorAssembledVectorField d B V branch
            chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R
            (y t) (selLamCoord v) =
          chiResetF t * kappaF t * (1 / 2 - y t (selLamCoord v))
            + chiGateF t *
              (gainF t * readoutP v (fun i => y t (selU V i)) *
                (y t (selLamCoord v) * (1 - y t (selLamCoord v)))) := by
      unfold selectorAssembledVectorField
      rw [selectorAssembledField_lam_eq, eval₂_selectorResetGateFieldPoly,
        h_chiReset t ht0, h_chiGate t ht0, h_kappa t ht0, h_gain t ht0, h_P v t ht0]
    exact heq ▸ hcoord
  · intro t ht
    have ht0 : 0 ≤ t := hdomain_nonneg t ht
    have hcoord := (hasDerivAt_pi.mp (hyode t ht0)) (selGCoord d V)
    have heq :
        selectorAssembledVectorField d B V branch
            chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R
            (y t) (selGCoord d V) =
          chiGateF t * gainF t := by
      unfold selectorAssembledVectorField
      rw [selectorAssembledField_G_eq, eval₂_selectorGainFieldPoly,
        h_chiGate t ht0, h_gain t ht0]
    exact heq ▸ hcoord
  · intro t ht
    have ht0 : 0 ≤ t := hdomain_nonneg t ht
    have hcoord := (hasDerivAt_pi.mp (hyode t ht0)) (selOfContract V (contractMu d))
    have heq :
        selectorAssembledVectorField d B V branch
            chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R
            (y t) (selOfContract V (contractMu d)) = p.cμ := by
      unfold selectorAssembledVectorField
      rw [selectorAssembledField_mu_eq]
      simp [hcμ]
    exact heq ▸ hcoord
  · intro t ht
    have ht0 : 0 ≤ t := hdomain_nonneg t ht
    have hcoord := (hasDerivAt_pi.mp (hyode t ht0)) (selOfContract V (contractAlpha d))
    have heq :
        selectorAssembledVectorField d B V branch
            chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R
            (y t) (selOfContract V (contractAlpha d)) =
          p.cα * y t (selOfContract V (contractAlpha d)) := by
      unfold selectorAssembledVectorField
      rw [selectorAssembledField_alpha_eq]
      simp [hcα]
    exact heq ▸ hcoord

/-- Main selector solution existence wrapper from the assembled autonomous field. -/
theorem selector_sol_exists
    {d B : ℕ} {V : Type} [Fintype V]
    (p : DynGateParams) (sched : PhaseSchedule)
    (branch : V → BranchData d B)
    (chiResetP chiGateP kappaP gainP : MvPolynomial (Fin (selectorDim d V)) ℚ)
    (PpolyP : V → MvPolynomial (Fin (selectorDim d V)) ℚ)
    (HP : MvPolynomial (Fin d) ℚ)
    {Aq Kq cμq cαq : ℚ} {L R : ℕ}
    (hA : p.A = (Aq : ℝ)) (hcμ : p.cμ = (cμq : ℝ)) (hcα : p.cα = (cαq : ℝ))
    (hL : p.L = L)
    (hdomain_nonneg : ∀ t : ℝ, t ∈ sched.domain → 0 ≤ t)
    (chiResetF chiGateF kappaF gainF : ℝ → ℝ)
    (readoutP : V → (Fin d → ℝ) → ℝ)
    (x₀ : ℕ → Fin d → ℚ) (w : ℕ) (warmGainInit : ℚ)
    (hfin :
      Ripple.FiniteHorizonBound
        (selectorAssembledVectorField d B V branch
          chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R)
        (fun i => ((selectorEuclInitQ d V x₀ w warmGainInit i : ℚ) : ℝ)))
    (hgateZ :
      ∀ y : ℝ → Fin (selectorDim d V) → ℝ,
        y 0 = (fun i => ((selectorEuclInitQ d V x₀ w warmGainInit i : ℚ) : ℝ)) →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y
            (selectorAssembledVectorField d B V branch
              chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R (y t)) t) →
        ∀ t : ℝ, 0 ≤ t →
          y t (selOfContract V (contractGateZ d)) =
            bGateZ L (y t (selOfContract V (contractMu d))) t)
    (hgateU :
      ∀ y : ℝ → Fin (selectorDim d V) → ℝ,
        y 0 = (fun i => ((selectorEuclInitQ d V x₀ w warmGainInit i : ℚ) : ℝ)) →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y
            (selectorAssembledVectorField d B V branch
              chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R (y t)) t) →
        ∀ t : ℝ, 0 ≤ t →
          y t (selOfContract V (contractGateU d)) =
            bGateU L (y t (selOfContract V (contractMu d))) t)
    (h_chiReset :
      ∀ y : ℝ → Fin (selectorDim d V) → ℝ,
        y 0 = (fun i => ((selectorEuclInitQ d V x₀ w warmGainInit i : ℚ) : ℝ)) →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y
            (selectorAssembledVectorField d B V branch
              chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R (y t)) t) →
        ∀ t : ℝ, 0 ≤ t →
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t) chiResetP = chiResetF t)
    (h_chiGate :
      ∀ y : ℝ → Fin (selectorDim d V) → ℝ,
        y 0 = (fun i => ((selectorEuclInitQ d V x₀ w warmGainInit i : ℚ) : ℝ)) →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y
            (selectorAssembledVectorField d B V branch
              chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R (y t)) t) →
        ∀ t : ℝ, 0 ≤ t →
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t) chiGateP = chiGateF t)
    (h_kappa :
      ∀ y : ℝ → Fin (selectorDim d V) → ℝ,
        y 0 = (fun i => ((selectorEuclInitQ d V x₀ w warmGainInit i : ℚ) : ℝ)) →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y
            (selectorAssembledVectorField d B V branch
              chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R (y t)) t) →
        ∀ t : ℝ, 0 ≤ t →
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t) kappaP = kappaF t)
    (h_gain :
      ∀ y : ℝ → Fin (selectorDim d V) → ℝ,
        y 0 = (fun i => ((selectorEuclInitQ d V x₀ w warmGainInit i : ℚ) : ℝ)) →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y
            (selectorAssembledVectorField d B V branch
              chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R (y t)) t) →
        ∀ t : ℝ, 0 ≤ t →
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t) gainP = gainF t)
    (h_P :
      ∀ y : ℝ → Fin (selectorDim d V) → ℝ,
        y 0 = (fun i => ((selectorEuclInitQ d V x₀ w warmGainInit i : ℚ) : ℝ)) →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y
            (selectorAssembledVectorField d B V branch
              chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R (y t)) t) →
        ∀ (v : V) (t : ℝ), 0 ≤ t →
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t) (PpolyP v) =
            readoutP v (fun i => y t (selU V i))) :
    ∃ sol : SelectorDynSol d B V p sched branch
        chiResetF chiGateF kappaF gainF readoutP,
      sol.z 0 = sol.init_z ∧ sol.u 0 = sol.init_u ∧
        (∀ i, sol.u 0 i = ((selectorEuclInitQ d V x₀ w warmGainInit (selU V i) : ℚ) : ℝ)) ∧
        sol.ZUFiniteCoordBound := by
  obtain ⟨y, hy0, hyode, hycont⟩ :=
    selector_assembled_global_solution_finitetime branch chiResetP chiGateP kappaP gainP PpolyP HP
      Aq Kq cμq cαq L R
      (fun i => ((selectorEuclInitQ d V x₀ w warmGainInit i : ℚ) : ℝ))
      hfin
  have hα0 : y 0 (selOfContract V (contractAlpha d)) = 1 := by
    rw [hy0]
    simp [selectorEuclInitQ, selOfContract, contractAlpha]
  have hμ0 : y 0 (selOfContract V (contractMu d)) = 0 := by
    rw [hy0]
    simp [selectorEuclInitQ, selOfContract, contractMu]
  let sol := selectorDynSol_of_selectorAssembledField_solution_explicit
    p sched branch chiResetP chiGateP kappaP gainP PpolyP HP hA hcμ hcα hL
    hdomain_nonneg y hyode hycont
    (hgateZ y hy0 hyode) (hgateU y hy0 hyode)
    chiResetF chiGateF kappaF gainF readoutP hα0
    (h_chiReset y hy0 hyode) (h_chiGate y hy0 hyode)
    (h_kappa y hy0 hyode) (h_gain y hy0 hyode) (h_P y hy0 hyode) hμ0
  refine ⟨sol, sol.z_at_zero, sol.u_at_zero, ?_, ?_⟩
  · intro i
    show y 0 (selU V i) = _
    exact congrFun hy0 (selU V i)
  · intro T hT
    obtain ⟨M, hMpos, hPrefix⟩ := hfin T hT
    refine ⟨M, hMpos, ?_⟩
    intro t ht i
    have hyM : ‖y t‖ ≤ M :=
      hPrefix T hT le_rfl y hy0 (fun s hs => hyode s hs.1) t ht
    constructor
    · have hzcoord : |y t (selZ V i)| ≤ ‖y t‖ := by
        simpa [Real.norm_eq_abs] using norm_le_pi_norm (y t) (selZ V i)
      simpa [sol] using hzcoord.trans hyM
    · have hucoord : |y t (selU V i)| ≤ ‖y t‖ := by
        simpa [Real.norm_eq_abs] using norm_le_pi_norm (y t) (selU V i)
      simpa [sol] using hucoord.trans hyM

end Ripple.BoundedUniversality.BGP
