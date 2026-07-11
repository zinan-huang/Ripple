import Ripple.BoundedUniversality.BGP.ContractTracking
import Ripple.BoundedUniversality.BGP.Existence
import Ripple.Core.ODEFiniteTime
import Ripple.BoundedUniversality.BGP.ContractMain
import Ripple.BoundedUniversality.BGP.ContractField

/-!
Ripple.BoundedUniversality.BGP.ContractSupply
-------------------------
Supplier-facing wrapper for the contract iterator.

The current contract field record keeps `S.F` as an arbitrary function
family, and `IsRationalFamily` is presently only a placeholder predicate.
Consequently the analytic Picard/clipping construction cannot be derived in
this file without an additional regularity/global-existence input.  The
proved interface below isolates the exact `hsupply` shape consumed by
`main_assembled_dyn_contract`: once the dynamic-gate layer supplies a
trajectory together with the four per-cycle box bounds, this file packages it
as `ContractPerCycleBox`.
-/

noncomputable section

namespace Ripple.BoundedUniversality.BGP

open Ripple.BoundedUniversality.Core
open scoped BigOperators

private theorem contract_locallyLipschitz_pi_lip_on_closedBall {n : ℕ}
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

private theorem contract_mvPolynomial_eval₂_contDiff
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

private theorem contract_polynomialVectorField_lip {n : ℕ}
    (P : Fin n → MvPolynomial (Fin n) ℚ) :
    ∀ R : ℝ, 0 < R → ∃ L : ℝ, ∀ x y : Fin n → ℝ,
      ‖x‖ ≤ R → ‖y‖ ≤ R →
      ‖(fun i => MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (P i)) -
          (fun i => MvPolynomial.eval₂ (algebraMap ℚ ℝ) y (P i))‖ ≤
        L * ‖x - y‖ :=
  contract_locallyLipschitz_pi_lip_on_closedBall
    (fun x i => MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (P i))
    (fun i =>
      ((contract_mvPolynomial_eval₂_contDiff (K := ℚ) (P i)).of_le
        (by norm_num : (1 : WithTop ℕ∞) ≤ ⊤)).locallyLipschitz)

/-- E1. Global forward existence for the concrete contract assembled
polynomial field, via Ripple's invariant-based global Picard theorem.

This is the same honest route as `Existence.lean`: polynomial fields provide
the local Lipschitz estimates, while global existence is obtained only after
an explicit a-priori invariant bound is supplied for the field actually being
integrated. -/
theorem contractAssembledField_global_solution_exists
    {d : ℕ}
    (FP : Fin d → MvPolynomial (Fin (contractDim d)) ℚ)
    (HP : MvPolynomial (Fin d) ℚ)
    (Aq Kq cμq cαq : ℚ) (L R : ℕ)
    (y₀ : Fin (contractDim d) → ℝ)
    (Mbound : ℝ) (hMbound : 0 < Mbound)
    (h_invariant :
      ∀ (T : ℝ), 0 < T → ∀ (y : ℝ → Fin (contractDim d) → ℝ),
        y 0 = y₀ →
        (∀ t ∈ Set.Ico (0 : ℝ) T,
          HasDerivAt y
            (fun i => MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t)
              (contractAssembledField d FP HP Aq Kq cμq cαq L R i)) t) →
        ∀ t ∈ Set.Ico (0 : ℝ) T, ‖y t‖ ≤ Mbound) :
    ∃ y : ℝ → Fin (contractDim d) → ℝ,
      y 0 = y₀ ∧
      (∀ t : ℝ, 0 ≤ t →
        HasDerivAt y
          (fun i => MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t)
            (contractAssembledField d FP HP Aq Kq cμq cαq L R i)) t) ∧
      Continuous y := by
  exact Ripple.locally_lipschitz_bounded_global_ode_proved_continuous
    (fun x i => MvPolynomial.eval₂ (algebraMap ℚ ℝ) x
      (contractAssembledField d FP HP Aq Kq cμq cαq L R i))
    y₀
    (contract_polynomialVectorField_lip
      (contractAssembledField d FP HP Aq Kq cμq cαq L R))
    Mbound hMbound h_invariant

private theorem contract_polynomial_eval_continuous {n : ℕ}
    (P : MvPolynomial (Fin n) ℚ) (y : ℝ → Fin n → ℝ) (hy : Continuous y) :
    Continuous fun t : ℝ => MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t) P :=
  (contract_mvPolynomial_eval₂_contDiff (K := ℚ) P).continuous.comp hy

/-- E2. Extract the contract iterator structure from a global solution of the
contract assembled polynomial field.

The two bridge hypotheses are the unavoidable interface facts: the polynomial
target coordinates evaluate to the abstract contract target `S.F`, and the
polynomial gate coordinates agree with the analytic exponential gate
definitions used by `DynContractIteratorSol`. -/
noncomputable def dynContractIteratorSol_of_contractAssembledField_solution
    {d nS : ℕ} {Conf : Type} [Primcodable Conf] {M : DiscreteMachine Conf}
    {E : StackMachineEncoding d nS M}
    {S : RobustStepContract M E}
    {p : DynGateParams} {sched : PhaseSchedule}
    (FP : Fin d → MvPolynomial (Fin (contractDim d)) ℚ)
    (HP : MvPolynomial (Fin d) ℚ)
    {Aq Kq cμq cαq : ℚ} {L R : ℕ}
    (hA : p.A = (Aq : ℝ))
    (hcμ : p.cμ = (cμq : ℝ)) (hcα : p.cα = (cαq : ℝ))
    (hL : p.L = L)
    (hdomain_nonneg : ∀ t : ℝ, t ∈ sched.domain → 0 ≤ t)
    (y : ℝ → Fin (contractDim d) → ℝ)
    (hyode : ∀ t : ℝ, 0 ≤ t →
      HasDerivAt y
        (fun i => MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t)
          (contractAssembledField d FP HP Aq Kq cμq cαq L R i)) t)
    (hycont : Continuous y)
    (hgateZ : ∀ t : ℝ, 0 ≤ t →
      y t (contractGateZ d) = bGateZ L (y t (contractMu d)) t)
    (hgateU : ∀ t : ℝ, 0 ≤ t →
      y t (contractGateU d) = bGateU L (y t (contractMu d)) t)
    (field_eval_identity :
      ∀ t : ℝ, 0 ≤ t → ∀ i : Fin d,
        MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t) (FP i) =
          S.F (y t (contractMu d)) (fun k => y t (contractU k)) i) :
    DynContractIteratorSol (Fin d) p sched S.F := by
  classical
  let z : ℝ → Fin d → ℝ := fun t i => y t (contractZ i)
  let u : ℝ → Fin d → ℝ := fun t i => y t (contractU i)
  let w : ℝ → Fin d → ℝ :=
    fun t i => MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t) (FP i)
  let μ : ℝ → ℝ := fun t => y t (contractMu d)
  let α : ℝ → ℝ := fun t => y t (contractAlpha d)
  refine
    { z := z
      u := u
      w := w
      μ := μ
      α := α
      init_z := z 0
      init_u := u 0
      init_μ := μ 0
      init_α := α 0
      z_at_zero := rfl
      u_at_zero := rfl
      μ_at_zero := rfl
      α_at_zero := rfl
      cont_z := ?_
      cont_u := ?_
      cont_w := ?_
      z_hasDeriv := ?_
      u_hasDeriv := ?_
      μ_hasDeriv := ?_
      α_hasDeriv := ?_
      target_eq := ?_
      F_is_rational := trivial }
  · intro i
    exact (continuous_apply (contractZ i)).comp hycont
  · intro i
    exact (continuous_apply (contractU i)).comp hycont
  · intro i
    exact contract_polynomial_eval_continuous (FP i) y hycont
  · intro t ht i
    have ht0 : 0 ≤ t := hdomain_nonneg t ht
    have hcoord := (hasDerivAt_pi.mp (hyode t ht0)) (contractZ i)
    convert hcoord using 1
    simp [z, w, α, μ, contractAssembledField, contractZ, contractTailZ,
      hA, hL, hgateZ t ht0]
  · intro t ht i
    have ht0 : 0 ≤ t := hdomain_nonneg t ht
    have hcoord := (hasDerivAt_pi.mp (hyode t ht0)) (contractU i)
    convert hcoord using 1
    simp [z, u, α, μ, contractAssembledField, contractU, contractTailU,
      hA, hL, hgateU t ht0]
  · intro t ht
    have ht0 : 0 ≤ t := hdomain_nonneg t ht
    have hcoord := (hasDerivAt_pi.mp (hyode t ht0)) (contractMu d)
    convert hcoord using 1
    simp [contractAssembledField, contractMu, hcμ]
  · intro t ht
    have ht0 : 0 ≤ t := hdomain_nonneg t ht
    have hcoord := (hasDerivAt_pi.mp (hyode t ht0)) (contractAlpha d)
    convert hcoord using 1
    simp [α, contractAssembledField, contractAlpha, hcα]
  · intro t ht
    ext i
    have ht0 : 0 ≤ t := hdomain_nonneg t ht
    exact field_eval_identity t ht0 i

/--
Extract a contract iterator solution from a polynomial-field trajectory without
packaging the target field through a `RobustStepContract`.

This is the raw-field version of
`dynContractIteratorSol_of_contractAssembledField_solution`: the target field
`F` is supplied directly.  It is the extraction layer needed by the N-atom
headline that avoids the old all-`μ` branch-spread premise used only to build a
`RobustStepContract`.
-/
noncomputable def dynContractIteratorSol_of_contractAssembledField_solution_raw
    {d : ℕ}
    {F : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    {p : DynGateParams} {sched : PhaseSchedule}
    (FP : Fin d → MvPolynomial (Fin (contractDim d)) ℚ)
    (HP : MvPolynomial (Fin d) ℚ)
    {Aq Kq cμq cαq : ℚ} {L R : ℕ}
    (hA : p.A = (Aq : ℝ))
    (hcμ : p.cμ = (cμq : ℝ)) (hcα : p.cα = (cαq : ℝ))
    (hL : p.L = L)
    (hdomain_nonneg : ∀ t : ℝ, t ∈ sched.domain → 0 ≤ t)
    (y : ℝ → Fin (contractDim d) → ℝ)
    (hyode : ∀ t : ℝ, 0 ≤ t →
      HasDerivAt y
        (fun i => MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t)
          (contractAssembledField d FP HP Aq Kq cμq cαq L R i)) t)
    (hycont : Continuous y)
    (hgateZ : ∀ t : ℝ, 0 ≤ t →
      y t (contractGateZ d) = bGateZ L (y t (contractMu d)) t)
    (hgateU : ∀ t : ℝ, 0 ≤ t →
      y t (contractGateU d) = bGateU L (y t (contractMu d)) t)
    (field_eval_identity :
      ∀ t : ℝ, 0 ≤ t → ∀ i : Fin d,
        MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t) (FP i) =
          F (y t (contractMu d)) (fun k => y t (contractU k)) i) :
    DynContractIteratorSol (Fin d) p sched F := by
  classical
  let z : ℝ → Fin d → ℝ := fun t i => y t (contractZ i)
  let u : ℝ → Fin d → ℝ := fun t i => y t (contractU i)
  let w : ℝ → Fin d → ℝ :=
    fun t i => MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t) (FP i)
  let μ : ℝ → ℝ := fun t => y t (contractMu d)
  let α : ℝ → ℝ := fun t => y t (contractAlpha d)
  refine
    { z := z
      u := u
      w := w
      μ := μ
      α := α
      init_z := z 0
      init_u := u 0
      init_μ := μ 0
      init_α := α 0
      z_at_zero := rfl
      u_at_zero := rfl
      μ_at_zero := rfl
      α_at_zero := rfl
      cont_z := ?_
      cont_u := ?_
      cont_w := ?_
      z_hasDeriv := ?_
      u_hasDeriv := ?_
      μ_hasDeriv := ?_
      α_hasDeriv := ?_
      target_eq := ?_
      F_is_rational := trivial }
  · intro i
    exact (continuous_apply (contractZ i)).comp hycont
  · intro i
    exact (continuous_apply (contractU i)).comp hycont
  · intro i
    exact contract_polynomial_eval_continuous (FP i) y hycont
  · intro t ht i
    have ht0 : 0 ≤ t := hdomain_nonneg t ht
    have hcoord := (hasDerivAt_pi.mp (hyode t ht0)) (contractZ i)
    convert hcoord using 1
    simp [z, w, α, μ, contractAssembledField, contractZ, contractTailZ,
      hA, hL, hgateZ t ht0]
  · intro t ht i
    have ht0 : 0 ≤ t := hdomain_nonneg t ht
    have hcoord := (hasDerivAt_pi.mp (hyode t ht0)) (contractU i)
    convert hcoord using 1
    simp [z, u, α, μ, contractAssembledField, contractU, contractTailU,
      hA, hL, hgateU t ht0]
  · intro t ht
    have ht0 : 0 ≤ t := hdomain_nonneg t ht
    have hcoord := (hasDerivAt_pi.mp (hyode t ht0)) (contractMu d)
    convert hcoord using 1
    simp [contractAssembledField, contractMu, hcμ]
  · intro t ht
    have ht0 : 0 ≤ t := hdomain_nonneg t ht
    have hcoord := (hasDerivAt_pi.mp (hyode t ht0)) (contractAlpha d)
    convert hcoord using 1
    simp [α, contractAssembledField, contractAlpha, hcα]
  · intro t ht
    ext i
    have ht0 : 0 ≤ t := hdomain_nonneg t ht
    exact field_eval_identity t ht0 i

/-- The four pointwise bounds that define `ContractPerCycleBox`, exposed as a
plain hypothesis so analytic suppliers can target this shape directly. -/
def ContractPerCycleBoxBounds
    {d nS : ℕ} {Conf : Type} [Primcodable Conf] {M : DiscreteMachine Conf}
    (E : StackMachineEncoding d nS M)
    {p : DynGateParams} {sched : PhaseSchedule}
    {F : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    (sol : DynContractIteratorSol (Fin d) p sched F)
    (w : ℕ) (D : ℝ) : Prop :=
  ∀ j t, t ∈ sched.zActiveWindow j →
    (∀ i, |contractOrbit E w (j + 1) i - contractOrbit E w j i| ≤ D) ∧
    (∀ i, |sol.z t i - contractOrbit E w j i| ≤ D) ∧
    (∀ i, |sol.u t i - contractOrbit E w j i| ≤ D) ∧
    (∀ i, |sol.w t i - contractOrbit E w j i| ≤ D)

/-- Package explicit per-window bounds into the contract box certificate. -/
theorem contract_per_cycle_box_of_bounds
    {d nS : ℕ} {Conf : Type} [Primcodable Conf] {M : DiscreteMachine Conf}
    {E : StackMachineEncoding d nS M}
    {p : DynGateParams} {sched : PhaseSchedule}
    {F : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    {sol : DynContractIteratorSol (Fin d) p sched F}
    {w : ℕ} {D : ℝ}
    (hbox : ContractPerCycleBoxBounds E sol w D) :
    ContractPerCycleBox E sol w D :=
  { box := hbox }

/-- E3. Supplier wrapper from polynomial-field data.

This composes E1 and E2 with the existing `contract_supply` target shape.  The
remaining hypotheses are exactly the non-existence bridges that are not encoded
in `RobustStepContract.F`: gate-coordinate identification, target-polynomial
evaluation, and the per-cycle box proof for the extracted contract iterator. -/
theorem contract_supply_of_polynomial_field
    {d nS : ℕ} {Conf : Type} [Primcodable Conf] {M : DiscreteMachine Conf}
    (E : StackMachineEncoding d nS M)
    (S : RobustStepContract M E)
    (p : DynGateParams) (sched : PhaseSchedule)
    (FP : Fin d → MvPolynomial (Fin (contractDim d)) ℚ)
    (HP : MvPolynomial (Fin d) ℚ)
    {Aq Kq cμq cαq : ℚ} {L R : ℕ}
    (hA : p.A = (Aq : ℝ))
    (hcμ : p.cμ = (cμq : ℝ)) (hcα : p.cα = (cαq : ℝ))
    (hL : p.L = L)
    (hdomain_nonneg : ∀ t : ℝ, t ∈ sched.domain → 0 ≤ t)
    (y₀ : ℕ → Fin (contractDim d) → ℝ)
    (Mbound : ℝ) (hMbound : 0 < Mbound)
    (D : ℝ)
    (h_invariant :
      ∀ w : ℕ, ∀ (T : ℝ), 0 < T →
        ∀ (y : ℝ → Fin (contractDim d) → ℝ),
          y 0 = y₀ w →
          (∀ t ∈ Set.Ico (0 : ℝ) T,
            HasDerivAt y
              (fun i => MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t)
                (contractAssembledField d FP HP Aq Kq cμq cαq L R i)) t) →
          ∀ t ∈ Set.Ico (0 : ℝ) T, ‖y t‖ ≤ Mbound)
    (hgateZ :
      ∀ (_w : ℕ) (y : ℝ → Fin (contractDim d) → ℝ), ∀ t : ℝ, 0 ≤ t →
        y t (contractGateZ d) = bGateZ L (y t (contractMu d)) t)
    (hgateU :
      ∀ (_w : ℕ) (y : ℝ → Fin (contractDim d) → ℝ), ∀ t : ℝ, 0 ≤ t →
        y t (contractGateU d) = bGateU L (y t (contractMu d)) t)
    (field_eval_identity :
      ∀ (_w : ℕ) (y : ℝ → Fin (contractDim d) → ℝ), ∀ t : ℝ, 0 ≤ t →
        ∀ i : Fin d,
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t) (FP i) =
            S.F (y t (contractMu d)) (fun k => y t (contractU k)) i)
    (hbox :
      ∀ (w : ℕ) (y : ℝ → Fin (contractDim d) → ℝ)
        (hyode : ∀ t : ℝ, 0 ≤ t →
          HasDerivAt y
            (fun i => MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t)
              (contractAssembledField d FP HP Aq Kq cμq cαq L R i)) t)
        (hycont : Continuous y),
        ContractPerCycleBoxBounds E
          (dynContractIteratorSol_of_contractAssembledField_solution
            (E := E) (S := S) (p := p) (sched := sched)
            FP HP hA hcμ hcα hL hdomain_nonneg y hyode hycont
            (hgateZ w y) (hgateU w y) (field_eval_identity w y))
          w D) :
    ∀ w : ℕ,
      ∃ sol : DynContractIteratorSol (Fin d) p sched S.F,
        ContractPerCycleBox E sol w D := by
  intro w
  obtain ⟨y, _hy0, hyode, hycont⟩ :=
    contractAssembledField_global_solution_exists
      FP HP Aq Kq cμq cαq L R (y₀ w) Mbound hMbound (h_invariant w)
  let sol : DynContractIteratorSol (Fin d) p sched S.F :=
    dynContractIteratorSol_of_contractAssembledField_solution
      (E := E) (S := S) (p := p) (sched := sched)
      FP HP hA hcμ hcα hL hdomain_nonneg y hyode hycont
      (hgateZ w y) (hgateU w y) (field_eval_identity w y)
  exact ⟨sol, contract_per_cycle_box_of_bounds (hbox w y hyode hycont)⟩

/--
Supplier theorem in the exact shape required by `main_assembled_dyn_contract`.

This is intentionally parametric in the analytic trajectory provider.  The
provider is the missing clipped dynamic Picard/barrier layer: it must construct
the `DynContractIteratorSol` and prove the four bounds on every active window.
-/
theorem contract_supply
    {d nS : ℕ} {Conf : Type} [Primcodable Conf] {M : DiscreteMachine Conf}
    (E : StackMachineEncoding d nS M)
    (S : RobustStepContract M E)
    (p : DynGateParams) (sched : PhaseSchedule)
    (D : ℝ)
    (hbounded :
      ∀ w : ℕ,
        ∃ sol : DynContractIteratorSol (Fin d) p sched S.F,
          ContractPerCycleBoxBounds E sol w D) :
    ∀ w : ℕ,
      ∃ sol : DynContractIteratorSol (Fin d) p sched S.F,
        ContractPerCycleBox E sol w D := by
  intro w
  obtain ⟨sol, hbox⟩ := hbounded w
  exact ⟨sol, contract_per_cycle_box_of_bounds hbox⟩

/-- E1-finite.  Global forward existence for the concrete contract assembled
polynomial field via the FINITE-HORIZON engine: a per-horizon
`Ripple.FiniteHorizonBound` (rather than a single all-time `Mbound`) suffices,
because the field is locally Lipschitz and Ripple's finite-time global
continuation glues compatible integer horizons.  This is the honest route for a
field with `α ~ exp(cα t)` growth, which is NOT all-time bounded but IS bounded
on every compact horizon. -/
theorem contractAssembledField_global_solution_exists_finitetime
    {d : ℕ}
    (FP : Fin d → MvPolynomial (Fin (contractDim d)) ℚ)
    (HP : MvPolynomial (Fin d) ℚ)
    (Aq Kq cμq cαq : ℚ) (L R : ℕ)
    (y₀ : Fin (contractDim d) → ℝ)
    (hfin :
      Ripple.FiniteHorizonBound
        (fun x i => MvPolynomial.eval₂ (algebraMap ℚ ℝ) x
          (contractAssembledField d FP HP Aq Kq cμq cαq L R i))
        y₀) :
    ∃ y : ℝ → Fin (contractDim d) → ℝ,
      y 0 = y₀ ∧
      (∀ t : ℝ, 0 ≤ t →
        HasDerivAt y
          (fun i => MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t)
            (contractAssembledField d FP HP Aq Kq cμq cαq L R i)) t) ∧
      Continuous y :=
  Ripple.locally_lipschitz_finitetime_global_ode_continuous
    (fun x i => MvPolynomial.eval₂ (algebraMap ℚ ℝ) x
      (contractAssembledField d FP HP Aq Kq cμq cαq L R i))
    y₀
    (contract_polynomialVectorField_lip
      (contractAssembledField d FP HP Aq Kq cμq cαq L R))
    hfin

/-- E3-finite.  Finite-horizon contract supply: the exact mirror of
`contract_supply_of_polynomial_field` with the all-time `Mbound + h_invariant`
replaced by a per-input `Ripple.FiniteHorizonBound` `hfin`.  Everything else (the
iterator extraction and the per-cycle box) is identical. -/
theorem contract_supply_of_polynomial_field_finitetime
    {d nS : ℕ} {Conf : Type} [Primcodable Conf] {M : DiscreteMachine Conf}
    (E : StackMachineEncoding d nS M)
    (S : RobustStepContract M E)
    (p : DynGateParams) (sched : PhaseSchedule)
    (FP : Fin d → MvPolynomial (Fin (contractDim d)) ℚ)
    (HP : MvPolynomial (Fin d) ℚ)
    {Aq Kq cμq cαq : ℚ} {L R : ℕ}
    (hA : p.A = (Aq : ℝ))
    (hcμ : p.cμ = (cμq : ℝ)) (hcα : p.cα = (cαq : ℝ))
    (hL : p.L = L)
    (hdomain_nonneg : ∀ t : ℝ, t ∈ sched.domain → 0 ≤ t)
    (y₀ : ℕ → Fin (contractDim d) → ℝ)
    (D : ℝ)
    (hfin :
      ∀ w : ℕ,
        Ripple.FiniteHorizonBound
          (fun x i => MvPolynomial.eval₂ (algebraMap ℚ ℝ) x
            (contractAssembledField d FP HP Aq Kq cμq cαq L R i))
          (y₀ w))
    (hgateZ :
      ∀ (_w : ℕ) (y : ℝ → Fin (contractDim d) → ℝ), ∀ t : ℝ, 0 ≤ t →
        y t (contractGateZ d) = bGateZ L (y t (contractMu d)) t)
    (hgateU :
      ∀ (_w : ℕ) (y : ℝ → Fin (contractDim d) → ℝ), ∀ t : ℝ, 0 ≤ t →
        y t (contractGateU d) = bGateU L (y t (contractMu d)) t)
    (field_eval_identity :
      ∀ (_w : ℕ) (y : ℝ → Fin (contractDim d) → ℝ), ∀ t : ℝ, 0 ≤ t →
        ∀ i : Fin d,
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t) (FP i) =
            S.F (y t (contractMu d)) (fun k => y t (contractU k)) i)
    (hbox :
      ∀ (w : ℕ) (y : ℝ → Fin (contractDim d) → ℝ)
        (hyode : ∀ t : ℝ, 0 ≤ t →
          HasDerivAt y
            (fun i => MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t)
              (contractAssembledField d FP HP Aq Kq cμq cαq L R i)) t)
        (hycont : Continuous y),
        ContractPerCycleBoxBounds E
          (dynContractIteratorSol_of_contractAssembledField_solution
            (E := E) (S := S) (p := p) (sched := sched)
            FP HP hA hcμ hcα hL hdomain_nonneg y hyode hycont
            (hgateZ w y) (hgateU w y) (field_eval_identity w y))
          w D) :
    ∀ w : ℕ,
      ∃ sol : DynContractIteratorSol (Fin d) p sched S.F,
        ContractPerCycleBox E sol w D := by
  intro w
  obtain ⟨y, _hy0, hyode, hycont⟩ :=
    contractAssembledField_global_solution_exists_finitetime
      FP HP Aq Kq cμq cαq L R (y₀ w) (hfin w)
  let sol : DynContractIteratorSol (Fin d) p sched S.F :=
    dynContractIteratorSol_of_contractAssembledField_solution
      (E := E) (S := S) (p := p) (sched := sched)
      FP HP hA hcμ hcα hL hdomain_nonneg y hyode hycont
      (hgateZ w y) (hgateU w y) (field_eval_identity w y)
  exact ⟨sol, contract_per_cycle_box_of_bounds (hbox w y hyode hycont)⟩

/--
Finite-horizon raw-field supply.

Unlike `contract_raw_supply_of_polynomial_field_finitetime`, this theorem does
not require a `RobustStepContract`; the target field `F` is the raw function
appearing in the extracted `DynContractIteratorSol`.
-/
theorem contract_supply_of_polynomial_field_finitetime_raw
    {d : ℕ}
    {F : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    (p : DynGateParams) (sched : PhaseSchedule)
    (FP : Fin d → MvPolynomial (Fin (contractDim d)) ℚ)
    (HP : MvPolynomial (Fin d) ℚ)
    {Aq Kq cμq cαq : ℚ} {L R : ℕ}
    (hA : p.A = (Aq : ℝ))
    (hcμ : p.cμ = (cμq : ℝ)) (hcα : p.cα = (cαq : ℝ))
    (hL : p.L = L)
    (hdomain_nonneg : ∀ t : ℝ, t ∈ sched.domain → 0 ≤ t)
    (y₀ : ℕ → Fin (contractDim d) → ℝ)
    (hfin :
      ∀ w : ℕ,
        Ripple.FiniteHorizonBound
          (fun x i => MvPolynomial.eval₂ (algebraMap ℚ ℝ) x
            (contractAssembledField d FP HP Aq Kq cμq cαq L R i))
          (y₀ w))
    (hgateZ :
      ∀ (_w : ℕ) (y : ℝ → Fin (contractDim d) → ℝ), ∀ t : ℝ, 0 ≤ t →
        y t (contractGateZ d) = bGateZ L (y t (contractMu d)) t)
    (hgateU :
      ∀ (_w : ℕ) (y : ℝ → Fin (contractDim d) → ℝ), ∀ t : ℝ, 0 ≤ t →
        y t (contractGateU d) = bGateU L (y t (contractMu d)) t)
    (field_eval_identity :
      ∀ (_w : ℕ) (y : ℝ → Fin (contractDim d) → ℝ), ∀ t : ℝ, 0 ≤ t →
        ∀ i : Fin d,
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t) (FP i) =
            F (y t (contractMu d)) (fun k => y t (contractU k)) i) :
    ∀ _w : ℕ, ∃ _sol : DynContractIteratorSol (Fin d) p sched F, True := by
  intro w
  obtain ⟨y, _hy0, hyode, hycont⟩ :=
    contractAssembledField_global_solution_exists_finitetime
      FP HP Aq Kq cμq cαq L R (y₀ w) (hfin w)
  exact
    ⟨dynContractIteratorSol_of_contractAssembledField_solution_raw
      (F := F) (p := p) (sched := sched)
      FP HP hA hcμ hcα hL hdomain_nonneg y hyode hycont
      (hgateZ w y) (hgateU w y) (field_eval_identity w y), trivial⟩

/--
Finite-horizon raw-field supply retaining the primitive contract initial data.

This closes the init part of the raw N-atom headline from the rational Euclidean
initial vector `contractEuclInitQ x₀ w`.
-/
theorem contract_init_supply_of_polynomial_field_finitetime_raw
    {d : ℕ}
    {F : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    (p : DynGateParams) (sched : PhaseSchedule)
    (FP : Fin d → MvPolynomial (Fin (contractDim d)) ℚ)
    (HP : MvPolynomial (Fin d) ℚ)
    {Aq Kq cμq cαq : ℚ} {L R : ℕ}
    (hA : p.A = (Aq : ℝ))
    (hcμ : p.cμ = (cμq : ℝ)) (hcα : p.cα = (cαq : ℝ))
    (hL : p.L = L)
    (hdomain_nonneg : ∀ t : ℝ, t ∈ sched.domain → 0 ≤ t)
    (x₀ : ℕ → Fin d → ℚ)
    (hfin :
      ∀ w : ℕ,
        Ripple.FiniteHorizonBound
          (fun x i => MvPolynomial.eval₂ (algebraMap ℚ ℝ) x
            (contractAssembledField d FP HP Aq Kq cμq cαq L R i))
          (fun i => ((contractEuclInitQ x₀ w i : ℚ) : ℝ)))
    (hgateZ :
      ∀ (_w : ℕ) (y : ℝ → Fin (contractDim d) → ℝ), ∀ t : ℝ, 0 ≤ t →
        y t (contractGateZ d) = bGateZ L (y t (contractMu d)) t)
    (hgateU :
      ∀ (_w : ℕ) (y : ℝ → Fin (contractDim d) → ℝ), ∀ t : ℝ, 0 ≤ t →
        y t (contractGateU d) = bGateU L (y t (contractMu d)) t)
    (field_eval_identity :
      ∀ (_w : ℕ) (y : ℝ → Fin (contractDim d) → ℝ), ∀ t : ℝ, 0 ≤ t →
        ∀ i : Fin d,
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t) (FP i) =
            F (y t (contractMu d)) (fun k => y t (contractU k)) i) :
    ∀ w : ℕ, ∃ sol : DynContractIteratorSol (Fin d) p sched F,
      sol.init_μ = 0 ∧
      sol.init_α = 1 ∧
      (∀ i : Fin d, sol.init_z i = ((x₀ w i : ℚ) : ℝ)) ∧
      (∀ i : Fin d, sol.init_u i = ((x₀ w i : ℚ) : ℝ)) := by
  intro w
  obtain ⟨y, hy0, hyode, hycont⟩ :=
    contractAssembledField_global_solution_exists_finitetime
      FP HP Aq Kq cμq cαq L R
      (fun i => ((contractEuclInitQ x₀ w i : ℚ) : ℝ))
      (hfin w)
  let sol : DynContractIteratorSol (Fin d) p sched F :=
    dynContractIteratorSol_of_contractAssembledField_solution_raw
      (F := F) (p := p) (sched := sched)
      FP HP hA hcμ hcα hL hdomain_nonneg y hyode hycont
      (hgateZ w y) (hgateU w y) (field_eval_identity w y)
  refine ⟨sol, ?_, ?_, ?_, ?_⟩
  · change y 0 (contractMu d) = 0
    rw [hy0]
    simp [contractEuclInitQ, contractMu]
  · change y 0 (contractAlpha d) = 1
    rw [hy0]
    simp [contractEuclInitQ, contractAlpha]
  · intro i
    change y 0 (contractZ i) = ((x₀ w i : ℚ) : ℝ)
    rw [hy0]
    simp [contractEuclInitQ, contractZ, contractTailZ]
  · intro i
    change y 0 (contractU i) = ((x₀ w i : ℚ) : ℝ)
    rw [hy0]
    simp [contractEuclInitQ, contractU, contractTailU]

end Ripple.BoundedUniversality.BGP
