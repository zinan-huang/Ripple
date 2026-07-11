/-
Ripple.BoundedUniversality.BGP.WarmHoldMU
---------------------
The **budget-absorbed** warm-start certificate for the warmed headline (Option A).

§3.3 correction (pbook1 R-WARMHOLD; supersedes the exact path in `WarmPhaseMU`):
the dynamic gates `bGateZ/U = exp(...)` are strictly positive — NEVER exactly
zero — so the warm prefix cannot freeze `z/u` EXACTLY at `enc (init w)`.
Therefore `ContractWarmPrefixExact` (exact equality) is unsatisfiable for the real
gates, and a zero initial budget `W 0 = 0` (which forces exact zero boundary
error) cannot be used.  The faithful certificate is APPROXIMATE
(`ContractWarmPrefixLeak`: `z/u` within a `leak` of `enc (init w)`), and the
initial weighted budget must PAY the weighted warm leak: `k^depth · leak ≤ W 0`.

The `leak` is supplied by the off-phase prefix drift (`z_prefix_drift_le` /
`u_prefix_drift_le`, mirrors of `InactiveLeakage`), which is `B^(-N)`-small under
the warm-up, so the nonzero `W 0` is absorbed into the reserve cap.
-/

import Ripple.BoundedUniversality.BGP.InactiveLeakageZ
import Ripple.BoundedUniversality.BGP.WarmIndexMU
import Ripple.BoundedUniversality.BGP.ClockWarmBounds
import Ripple.BoundedUniversality.BGP.BGPParams38

namespace Ripple.BoundedUniversality.BGP

open Real
open Ripple.BoundedUniversality.Core

noncomputable section

/-- The dynamic gates are never exactly zero — off-phase means small, not zero. -/
theorem bGateZ_not_exactly_off (L : ℕ) (m t : ℝ) : bGateZ L m t ≠ 0 :=
  ne_of_gt (bGateZ_pos L m t)

theorem bGateU_not_exactly_off (L : ℕ) (m t : ℝ) : bGateU L m t ≠ 0 :=
  ne_of_gt (bGateU_pos L m t)

/-! ## Prefix drift lemmas (off-phase warm-prefix, mirrors of `InactiveLeakage`) -/

/-- z-channel warm-prefix drift from the ODE and a prefix-wide small-gate bound. -/
theorem z_prefix_drift_le
    {d : ℕ} {p : DynGateParams} {sched : PhaseSchedule}
    (sol : DynMovingTargetIteratorSol (Fin d) p sched)
    (i : Fin d) {T K Dwz : ℝ}
    (hT : 0 ≤ T)
    (hdom : Set.Icc (0 : ℝ) T ⊆ sched.domain)
    (hwz : ∀ τ ∈ Set.Icc (0 : ℝ) T, |sol.w τ i - sol.z τ i| ≤ Dwz)
    (hDwz : 0 ≤ Dwz)
    (hgate : ∀ τ ∈ Set.Icc (0 : ℝ) T,
      |p.A * sol.α τ * bGateZ p.L (sol.μ τ) τ| ≤ K)
    (hK : 0 ≤ K) :
    |sol.z T i - sol.z 0 i| ≤ K * Dwz * T := by
  set v : ℝ → ℝ := fun τ =>
    p.A * sol.α τ * bGateZ p.L (sol.μ τ) τ * (sol.w τ i - sol.z τ i) with hv
  set f : ℝ → ℝ := fun τ => sol.z τ i with hf
  have hderiv : ∀ x ∈ Set.Icc (0 : ℝ) T,
      HasDerivWithinAt f (v x) (Set.Icc (0 : ℝ) T) x := by
    intro x hx
    have hx_dom : x ∈ sched.domain := hdom hx
    have hx_at : HasDerivAt (fun τ => sol.z τ i) (v x) x := by
      simpa [hv] using sol.z_hasDeriv x hx_dom i
    exact hx_at.hasDerivWithinAt
  have hbound : ∀ x ∈ Set.Ico (0 : ℝ) T, ‖v x‖ ≤ K * Dwz := by
    intro x hx
    have hxIcc : x ∈ Set.Icc (0 : ℝ) T := Set.Ico_subset_Icc_self hx
    have hg := hgate x hxIcc
    have hz := hwz x hxIcc
    have he : v x =
        p.A * sol.α x * bGateZ p.L (sol.μ x) x * (sol.w x i - sol.z x i) := by
      simp only [hv]
    rw [he, Real.norm_eq_abs, abs_mul]
    exact mul_le_mul hg hz (abs_nonneg _) hK
  have hmvt := norm_image_sub_le_of_norm_deriv_le_segment'
    (f := f) (f' := v) (C := K * Dwz) hderiv hbound T (Set.right_mem_Icc.mpr hT)
  have hfta : f T - f 0 = sol.z T i - sol.z 0 i := by simp only [hf]
  have key : |sol.z T i - sol.z 0 i| ≤ K * Dwz * (T - 0) := by
    rw [← hfta, ← Real.norm_eq_abs]; exact hmvt
  simpa using key

/-- u-channel warm-prefix drift from the ODE and a prefix-wide small-gate bound. -/
theorem u_prefix_drift_le
    {d : ℕ} {p : DynGateParams} {sched : PhaseSchedule}
    (sol : DynMovingTargetIteratorSol (Fin d) p sched)
    (i : Fin d) {T K Dzu : ℝ}
    (hT : 0 ≤ T)
    (hdom : Set.Icc (0 : ℝ) T ⊆ sched.domain)
    (hzu : ∀ τ ∈ Set.Icc (0 : ℝ) T, |sol.z τ i - sol.u τ i| ≤ Dzu)
    (hDzu : 0 ≤ Dzu)
    (hgate : ∀ τ ∈ Set.Icc (0 : ℝ) T,
      |p.A * sol.α τ * bGateU p.L (sol.μ τ) τ| ≤ K)
    (hK : 0 ≤ K) :
    |sol.u T i - sol.u 0 i| ≤ K * Dzu * T := by
  set v : ℝ → ℝ := fun τ =>
    p.A * sol.α τ * bGateU p.L (sol.μ τ) τ * (sol.z τ i - sol.u τ i) with hv
  set f : ℝ → ℝ := fun τ => sol.u τ i with hf
  have hderiv : ∀ x ∈ Set.Icc (0 : ℝ) T,
      HasDerivWithinAt f (v x) (Set.Icc (0 : ℝ) T) x := by
    intro x hx
    have hx_dom : x ∈ sched.domain := hdom hx
    have hx_at : HasDerivAt (fun τ => sol.u τ i) (v x) x := by
      simpa [hv] using sol.u_hasDeriv x hx_dom i
    exact hx_at.hasDerivWithinAt
  have hbound : ∀ x ∈ Set.Ico (0 : ℝ) T, ‖v x‖ ≤ K * Dzu := by
    intro x hx
    have hxIcc : x ∈ Set.Icc (0 : ℝ) T := Set.Ico_subset_Icc_self hx
    have hg := hgate x hxIcc
    have hz := hzu x hxIcc
    have he : v x =
        p.A * sol.α x * bGateU p.L (sol.μ x) x * (sol.z x i - sol.u x i) := by
      simp only [hv]
    rw [he, Real.norm_eq_abs, abs_mul]
    exact mul_le_mul hg hz (abs_nonneg _) hK
  have hmvt := norm_image_sub_le_of_norm_deriv_le_segment'
    (f := f) (f' := v) (C := K * Dzu) hderiv hbound T (Set.right_mem_Icc.mpr hT)
  have hfta : f T - f 0 = sol.u T i - sol.u 0 i := by simp only [hf]
  have key : |sol.u T i - sol.u 0 i| ≤ K * Dzu * (T - 0) := by
    rw [← hfta, ← Real.norm_eq_abs]; exact hmvt
  simpa using key

/-! ## Budget-absorbed warm-start certificate -/

/-- Approximate warm-start certificate: at logical cycle `0` (read at
`cycleStart 0`), `z/u` are within `leak` of `enc (init w)`.  Replaces the
unsatisfiable exact `ContractWarmPrefixExact`. -/
structure ContractWarmPrefixLeak
    {Conf : Type} [Primcodable Conf] {M : DiscreteMachine Conf}
    {d nS : ℕ} (E : StackMachineEncoding d nS M)
    {p : DynGateParams} {sched : PhaseSchedule}
    {F : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    (sol : DynContractIteratorSol (Fin d) p sched F)
    (w : ℕ) (leak : Fin d → ℝ) : Prop where
  z_at_warmStart :
    ∀ i : Fin d, |sol.z (sched.cycleStart 0) i - E.enc (M.init w) i| ≤ leak i
  u_at_warmStart :
    ∀ i : Fin d, |sol.u (sched.cycleStart 0) i - E.enc (M.init w) i| ≤ leak i

/-- Build the leak certificate from prefix drift + exact rational init at time `0`. -/
theorem contractWarmPrefixLeak_of_prefix_drifts
    {Conf : Type} [Primcodable Conf] {M : DiscreteMachine Conf}
    {d nS : ℕ} {E : StackMachineEncoding d nS M}
    {p : DynGateParams} {sched : PhaseSchedule}
    {F : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    (sol : DynContractIteratorSol (Fin d) p sched F)
    (w : ℕ) (leak : Fin d → ℝ) {T : ℝ}
    (hcycle0 : sched.cycleStart 0 = T)
    (hz0 : sol.z 0 = E.enc (M.init w))
    (hu0 : sol.u 0 = E.enc (M.init w))
    (hzdrift : ∀ i : Fin d, |sol.z T i - sol.z 0 i| ≤ leak i)
    (hudrift : ∀ i : Fin d, |sol.u T i - sol.u 0 i| ≤ leak i) :
    ContractWarmPrefixLeak E sol w leak := by
  refine ⟨?_, ?_⟩
  · intro i; rw [hcycle0]; simpa [congrFun hz0 i] using hzdrift i
  · intro i; rw [hcycle0]; simpa [congrFun hu0 i] using hudrift i

/-- Boundary error at logical cycle `0` is bounded by the warm-start leak. -/
theorem contractBoundaryError_zero_le_of_warmPrefixLeak
    {Conf : Type} [Primcodable Conf] {M : DiscreteMachine Conf}
    {d nS : ℕ} {E : StackMachineEncoding d nS M}
    {p : DynGateParams} {sched : PhaseSchedule}
    {F : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    (sol : DynContractIteratorSol (Fin d) p sched F)
    (w : ℕ) (leak : Fin d → ℝ)
    (hwarm : ContractWarmPrefixLeak E sol w leak) (i : Fin d) :
    contractBoundaryError (E := E) sol (fun j => M.step^[j] (M.init w)) 0 i
      ≤ leak i := by
  unfold contractBoundaryError
  exact max_le (by simpa using hwarm.z_at_warmStart i)
    (by simpa using hwarm.u_at_warmStart i)

/-- **Budget-absorbed initial weighted bound** — the replacement for the
zero-budget exact base case: `W 0` pays the weighted warm leak. -/
theorem contract_hinit_weighted_of_warmPrefixLeak
    {Conf : Type} [Primcodable Conf] {M : DiscreteMachine Conf}
    {d nS : ℕ} {E : StackMachineEncoding d nS M}
    {p : DynGateParams} {sched : PhaseSchedule}
    {F : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    (sol : DynContractIteratorSol (Fin d) p sched F)
    (w : ℕ)
    (depth : ℕ → Fin d → ℤ) (Wb : ℕ → Fin d → ℝ) (leak : Fin d → ℝ)
    (hwarm : ContractWarmPrefixLeak E sol w leak)
    (hweight_nonneg : ∀ i : Fin d, 0 ≤ (E.k : ℝ) ^ depth 0 i)
    (hW0 : ∀ i : Fin d, (E.k : ℝ) ^ depth 0 i * leak i ≤ Wb 0 i) :
    ContractWeightedBound (E := E) sol
      (fun j => M.step^[j] (M.init w)) depth Wb 0 := by
  intro i
  have hbe := contractBoundaryError_zero_le_of_warmPrefixLeak
    (E := E) sol w leak hwarm i
  exact (mul_le_mul_of_nonneg_left hbe (hweight_nonneg i)).trans (hW0 i)

/-- §3.3 demonstration: a zero initial budget `W 0 i = 0` forces the actual
cycle-0 boundary error to be exactly zero — so it CANNOT absorb a nonzero leak. -/
theorem zero_initial_budget_forces_zero_boundaryError
    {Conf : Type} [Primcodable Conf] {M : DiscreteMachine Conf}
    {d nS : ℕ} {E : StackMachineEncoding d nS M}
    {p : DynGateParams} {sched : PhaseSchedule}
    {F : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    (sol : DynContractIteratorSol (Fin d) p sched F)
    (c : ℕ → Conf) (depth : ℕ → Fin d → ℤ) (Wb : ℕ → Fin d → ℝ) (i : Fin d)
    (hweighted : ContractWeightedBound (E := E) sol c depth Wb 0)
    (hW0 : Wb 0 i = 0)
    (hweight_pos : 0 < (E.k : ℝ) ^ depth 0 i) :
    contractBoundaryError (E := E) sol c 0 i = 0 := by
  have h := hweighted i
  rw [hW0] at h
  have hbe0 := contractBoundaryError_nonneg (E := E) sol c 0 i
  have hprod_eq : (E.k : ℝ) ^ depth 0 i * contractBoundaryError (E := E) sol c 0 i = 0 :=
    le_antisymm h (mul_nonneg hweight_pos.le hbe0)
  exact (mul_eq_zero.mp hprod_eq).resolve_left (ne_of_gt hweight_pos)

/-- For `(A=1,L=1,cμ=1,cα=1/4)` the κ exponent is CONSTANT in `n` — the obstruction:
no growth, so the warm `hP` cannot hold for unbounded `N`, linear `j`. -/
lemma bgp_dynKappaExponent_const (n : ℕ) :
    dynKappaExponent (1 : ℝ) 1 (1 : ℝ) ((1 : ℝ) / 4) n
      = Real.exp (-(Real.pi / 2)) * (2 * Real.pi / 3) := by
  unfold dynKappaExponent
  rw [one_mul, ← Real.exp_add]
  exact congrArg (fun x => Real.exp x * (2 * Real.pi / 3)) (by push_cast; ring)

/-- Named κ lower-bound obligation (the carried `hP` for `dynKappa_warm_bound`).
At `cα = 3/8` the inner exponent has positive growth in the physical index. -/
def KappaWarmHP (A B qκ cμ cα : ℝ) (L N m : ℕ) : Prop :=
  ∀ j : ℕ,
    (N : ℝ) * Real.log B + (j : ℝ) * Real.log (1 / qκ)
      ≤ dynKappaExponent A L cμ cα (m + j)

/-- Plug the named κ supplier into the landed `dynKappa_warm_bound`. -/
theorem dynKappa_warm_bound_of_KappaWarmHP
    {A B qκ cμ cα : ℝ} {L N m : ℕ}
    (hB0 : 0 < B) (hqκ : 0 < qκ) (hP : KappaWarmHP A B qκ cμ cα L N m) :
    ∀ j : ℕ, dynKappa A L cμ cα (m + j) ≤ B ^ (-(N : ℤ)) * qκ ^ j := by
  intro j
  exact dynKappa_warm_bound (A := A) (B := B) (qκ := qκ)
    (L := L) (c₀ := cμ) (c₁ := cα) (N := N) (m := m) (j := j) hB0 hqκ (hP j)

/-- The concrete `3/8` κ warm-bound shape. -/
theorem dynKappa_warm_bound_3_8
    {B qκ : ℝ} {N m : ℕ}
    (hB0 : 0 < B) (hqκ : 0 < qκ)
    (hP : KappaWarmHP (1 : ℝ) B qκ (1 : ℝ) ((3 : ℝ) / 8) 1 N m) :
    ∀ j : ℕ, dynKappa (1 : ℝ) 1 (1 : ℝ) ((3 : ℝ) / 8) (m + j) ≤ B ^ (-(N : ℤ)) * qκ ^ j :=
  dynKappa_warm_bound_of_KappaWarmHP hB0 hqκ hP

end

end Ripple.BoundedUniversality.BGP
