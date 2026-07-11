import Ripple.BoundedUniversality.BGP.SelectorReplicatorExistence
import Ripple.BoundedUniversality.BGP.SelectorZRead

/-!
Ripple.BoundedUniversality.BGP.SelectorReplicatorUTube
----------------------------------
Replicator-sibling port of the all-cycle `u`-tube chain.

This file is additive.  The logistic `SelectorDynSol` declarations stay in their
original files; the declarations below copy the same value-level `z`/`u` budget
chain for `SelectorReplicatorDynSol`.
-/

noncomputable section

namespace Ripple.BoundedUniversality.BGP

open scoped BigOperators
open Set

/-- Replicator sibling of `muBoundaryError`. -/
def muBoundaryError_repl
    {V : Type} [Fintype V] {branch : V → BranchData MachineInstance.d_U MachineInstance.B_U}
    {Pv : V → (Fin MachineInstance.d_U → ℝ) → ℝ} {p : DynGateParams}
    {chiResetF chiGateF kappaF gainF : ℝ → ℝ}
    (sol : SelectorReplicatorDynSol MachineInstance.d_U MachineInstance.B_U V p
      selectorSchedule branch chiResetF chiGateF kappaF gainF Pv)
    (enc : ℕ → Fin MachineInstance.d_U → ℝ) (j : ℕ) (i : Fin MachineInstance.d_U) : ℝ :=
  |sol.u (2 * Real.pi * (j : ℝ) + Real.pi / 6) i - enc j i|

/-- Nonnegativity of the replicator boundary error. -/
theorem muBoundaryError_nonneg_repl
    {V : Type} [Fintype V] {branch : V → BranchData MachineInstance.d_U MachineInstance.B_U}
    {Pv : V → (Fin MachineInstance.d_U → ℝ) → ℝ} {p : DynGateParams}
    {chiResetF chiGateF kappaF gainF : ℝ → ℝ}
    (sol : SelectorReplicatorDynSol MachineInstance.d_U MachineInstance.B_U V p
      selectorSchedule branch chiResetF chiGateF kappaF gainF Pv)
    (enc : ℕ → Fin MachineInstance.d_U → ℝ) (j : ℕ) (i : Fin MachineInstance.d_U) :
    0 ≤ muBoundaryError_repl sol enc j i := abs_nonneg _

/-- Replicator sibling of `MUWeighted`. -/
def MUWeighted_repl
    {V : Type} [Fintype V] {branch : V → BranchData MachineInstance.d_U MachineInstance.B_U}
    {Pv : V → (Fin MachineInstance.d_U → ℝ) → ℝ} {p : DynGateParams}
    {chiResetF chiGateF kappaF gainF : ℝ → ℝ}
    (sol : SelectorReplicatorDynSol MachineInstance.d_U MachineInstance.B_U V p
      selectorSchedule branch chiResetF chiGateF kappaF gainF Pv)
    (enc : ℕ → Fin MachineInstance.d_U → ℝ) (k : ℝ) (dep : ℕ → Fin MachineInstance.d_U → ℤ)
    (Wbound : ℕ → Fin MachineInstance.d_U → ℝ) (j : ℕ) : Prop :=
  ∀ i : Fin MachineInstance.d_U,
    k ^ dep j i * muBoundaryError_repl sol enc j i ≤ Wbound j i

/-- Replicator sibling of `MURecur`. -/
def MURecur_repl
    {V : Type} [Fintype V] {branch : V → BranchData MachineInstance.d_U MachineInstance.B_U}
    {Pv : V → (Fin MachineInstance.d_U → ℝ) → ℝ} {p : DynGateParams}
    {chiResetF chiGateF kappaF gainF : ℝ → ℝ}
    (sol : SelectorReplicatorDynSol MachineInstance.d_U MachineInstance.B_U V p
      selectorSchedule branch chiResetF chiGateF kappaF gainF Pv)
    (enc : ℕ → Fin MachineInstance.d_U → ℝ) (k : ℝ) (delta : ℕ → Fin MachineInstance.d_U → ℤ)
    (η : ℕ → Fin MachineInstance.d_U → ℝ) (j : ℕ) : Prop :=
  ∀ i : Fin MachineInstance.d_U,
    muBoundaryError_repl sol enc (j + 1) i ≤
      k ^ delta j i * muBoundaryError_repl sol enc j i + η j i

/-- Replicator sibling of `mu_weighted_step`. -/
theorem mu_weighted_step_repl
    {V : Type} [Fintype V] {branch : V → BranchData MachineInstance.d_U MachineInstance.B_U}
    {Pv : V → (Fin MachineInstance.d_U → ℝ) → ℝ} {p : DynGateParams}
    {chiResetF chiGateF kappaF gainF : ℝ → ℝ}
    (sol : SelectorReplicatorDynSol MachineInstance.d_U MachineInstance.B_U V p
      selectorSchedule branch chiResetF chiGateF kappaF gainF Pv)
    (enc : ℕ → Fin MachineInstance.d_U → ℝ) {k : ℝ} (hk : 1 < k)
    (dep delta : ℕ → Fin MachineInstance.d_U → ℤ) (η Wbound : ℕ → Fin MachineInstance.d_U → ℝ)
    (hdepth : ∀ j i, dep (j + 1) i = dep j i - delta j i)
    (hWstep : ∀ j i, Wbound j i + k ^ dep (j + 1) i * η j i ≤ Wbound (j + 1) i)
    (j : ℕ) (hw : MUWeighted_repl sol enc k dep Wbound j)
    (hr : MURecur_repl sol enc k delta η j) :
    MUWeighted_repl sol enc k dep Wbound (j + 1) := by
  intro i
  -- the per-coordinate one-step weighted inequality, mirroring `DepthBudget.weighted_step`.
  have hk0 : (0 : ℝ) ≤ k := (zero_lt_one.trans hk).le
  have hk_ne : k ≠ 0 := (zero_lt_one.trans hk).ne'
  have hpow_nonneg : 0 ≤ k ^ dep (j + 1) i := zpow_nonneg hk0 _
  have hstep :
      k ^ dep (j + 1) i * muBoundaryError_repl sol enc (j + 1) i ≤
        k ^ dep j i * muBoundaryError_repl sol enc j i + k ^ dep (j + 1) i * η j i := by
    calc k ^ dep (j + 1) i * muBoundaryError_repl sol enc (j + 1) i
        ≤ k ^ dep (j + 1) i *
            (k ^ delta j i * muBoundaryError_repl sol enc j i + η j i) :=
          mul_le_mul_of_nonneg_left (hr i) hpow_nonneg
      _ = k ^ (dep (j + 1) i + delta j i) * muBoundaryError_repl sol enc j i
            + k ^ dep (j + 1) i * η j i := by
          rw [mul_add, ← mul_assoc, ← zpow_add₀ hk_ne]
      _ = k ^ dep j i * muBoundaryError_repl sol enc j i + k ^ dep (j + 1) i * η j i := by
          have hd : dep (j + 1) i + delta j i = dep j i := by rw [hdepth j i]; abel
          rw [hd]
  calc k ^ dep (j + 1) i * muBoundaryError_repl sol enc (j + 1) i
      ≤ k ^ dep j i * muBoundaryError_repl sol enc j i + k ^ dep (j + 1) i * η j i := hstep
    _ ≤ Wbound j i + k ^ dep (j + 1) i * η j i := by linarith [hw i]
    _ ≤ Wbound (j + 1) i := hWstep j i

/-- Replicator sibling of the pure weighted-bound-to-radius algebra. -/
theorem weighted_boundary_to_radius_repl
    {d B : ℕ} {V : Type} [Fintype V] {p : DynGateParams} {sched : PhaseSchedule}
    {branch : V → BranchData d B} {chiReset chiGate kappa gain : ℝ → ℝ}
    {readoutP : V → (Fin d → ℝ) → ℝ}
    (sol : SelectorReplicatorDynSol d B V p sched branch chiReset chiGate kappa gain readoutP)
    (enc : Fin d → ℝ) {k : ℝ} (hk1 : 1 < k) (dep : Fin d → ℤ) (Wbound : Fin d → ℝ)
    {a t εhold ρ : ℝ}
    (hhold : ∀ i, |sol.u t i - sol.u a i| ≤ εhold)
    (hradius : ∀ i, Wbound i / k ^ dep i + εhold ≤ ρ)
    (hw : ∀ i, k ^ dep i * |sol.u a i - enc i| ≤ Wbound i) :
    ∀ i, |sol.u t i - enc i| ≤ ρ := by
  intro i
  have hkpos : 0 < k ^ dep i := zpow_pos (by linarith : (0 : ℝ) < k) _
  -- divide the weighted bound by the positive `k^(dep i)` (the pitfall)
  have hbd : |sol.u a i - enc i| ≤ Wbound i / k ^ dep i := by
    rw [le_div_iff₀ hkpos]
    calc |sol.u a i - enc i| * k ^ dep i = k ^ dep i * |sol.u a i - enc i| := by ring
      _ ≤ Wbound i := hw i
  have htri : |sol.u t i - enc i| ≤ |sol.u a i - enc i| + |sol.u t i - sol.u a i| := by
    have heq : sol.u t i - enc i = (sol.u a i - enc i) + (sol.u t i - sol.u a i) := by ring
    rw [heq]; exact abs_add_le _ _
  calc |sol.u t i - enc i| ≤ |sol.u a i - enc i| + |sol.u t i - sol.u a i| := htri
    _ ≤ Wbound i / k ^ dep i + εhold := add_le_add hbd (hhold i)
    _ ≤ ρ := hradius i

/-- Replicator sibling of `selector_MU_hwin_of_weighted`. -/
theorem selector_MU_hwin_of_weighted_repl
    {B : ℕ} {V : Type} [Fintype V] {p : DynGateParams}
    {branch : V → BranchData MachineInstance.d_U B}
    {chiReset chiGate kappa gain : ℝ → ℝ}
    {readoutP : V → (Fin MachineInstance.d_U → ℝ) → ℝ}
    (sol : SelectorReplicatorDynSol MachineInstance.d_U B V p selectorSchedule branch
      chiReset chiGate kappa gain readoutP)
    (cfg : ℕ → MachineInstance.UConf) {k : ℝ} (hk1 : 1 < k)
    (dep : ℕ → Fin MachineInstance.d_U → ℤ) (Wbound : ℕ → Fin MachineInstance.d_U → ℝ)
    {εhold : ℝ} (j : ℕ)
    (hhold : ∀ i, ∀ t ∈ Icc (2 * Real.pi * (j : ℝ) + Real.pi / 6)
        (2 * Real.pi * (j : ℝ) + Real.pi / 2),
        |sol.u t i - sol.u (2 * Real.pi * (j : ℝ) + Real.pi / 6) i| ≤ εhold)
    (hradius : ∀ i, Wbound j i / k ^ dep j i + εhold ≤ MachineInstance.r_LE_U)
    (hw : ∀ i, k ^ dep j i *
        |sol.u (2 * Real.pi * (j : ℝ) + Real.pi / 6) i
          - MachineInstance.stackMachineEncodingU.enc (cfg j) i| ≤ Wbound j i) :
    ∀ t ∈ Ico (2 * Real.pi * (j : ℝ) + Real.pi / 6) (2 * Real.pi * (j : ℝ) + Real.pi / 2),
      MachineInstance.UTube MachineInstance.r_LE_U (cfg j) (sol.u t) := by
  intro t ht
  have htIcc : t ∈ Icc (2 * Real.pi * (j : ℝ) + Real.pi / 6)
      (2 * Real.pi * (j : ℝ) + Real.pi / 2) := ⟨ht.1, le_of_lt ht.2⟩
  -- `UTube r_LE_U (cfg j) (u t) = ∀ i, |u t i − confEncU (cfg j) i| ≤ r_LE_U`, and
  -- `stackMachineEncodingU.enc (cfg j) i = confEncU (cfg j) i` is `rfl`, so the abstract core
  -- conclusion lands the tube definitionally.
  exact weighted_boundary_to_radius_repl sol
    (MachineInstance.stackMachineEncodingU.enc (cfg j)) hk1 (dep j) (Wbound j)
    (fun i => hhold i t htIcc) hradius hw

/-- Replicator sibling of `MUWeighted_all_of_init_step`. -/
theorem MUWeighted_all_of_init_step_repl
    {V : Type} [Fintype V]
    {branch : V → BranchData MachineInstance.d_U MachineInstance.B_U}
    {Pv : V → (Fin MachineInstance.d_U → ℝ) → ℝ} {p : DynGateParams}
    {chiResetF chiGateF kappaF gainF : ℝ → ℝ}
    (sol : SelectorReplicatorDynSol MachineInstance.d_U MachineInstance.B_U V p
      selectorSchedule branch chiResetF chiGateF kappaF gainF Pv)
    (enc : ℕ → Fin MachineInstance.d_U → ℝ) {k : ℝ} (hk : 1 < k)
    (dep delta : ℕ → Fin MachineInstance.d_U → ℤ)
    (η Wbound : ℕ → Fin MachineInstance.d_U → ℝ)
    (hdepth : ∀ j i, dep (j + 1) i = dep j i - delta j i)
    (hWstep : ∀ j i, Wbound j i + k ^ dep (j + 1) i * η j i ≤ Wbound (j + 1) i)
    (hinit : MUWeighted_repl sol enc k dep Wbound 0)
    (hrecur : ∀ j, MUWeighted_repl sol enc k dep Wbound j → MURecur_repl sol enc k delta η j) :
    ∀ j, MUWeighted_repl sol enc k dep Wbound j := by
  intro j
  induction j with
  | zero => exact hinit
  | succ n ih =>
      exact mu_weighted_step_repl sol enc hk dep delta η Wbound hdepth hWstep n ih (hrecur n ih)

/-- Replicator sibling of `selector_MU_utube_all`. -/
theorem selector_MU_utube_all_repl
    {V : Type} [Fintype V]
    {branch : V → BranchData MachineInstance.d_U MachineInstance.B_U}
    {Pv : V → (Fin MachineInstance.d_U → ℝ) → ℝ} {p : DynGateParams}
    {chiResetF chiGateF kappaF gainF : ℝ → ℝ}
    (sol : SelectorReplicatorDynSol MachineInstance.d_U MachineInstance.B_U V p
      selectorSchedule branch chiResetF chiGateF kappaF gainF Pv)
    (cfg : ℕ → MachineInstance.UConf) {k : ℝ} (hk1 : 1 < k)
    (dep : ℕ → Fin MachineInstance.d_U → ℤ) (Wbound : ℕ → Fin MachineInstance.d_U → ℝ) {εhold : ℝ}
    (hMU : ∀ j, MUWeighted_repl sol
      (fun j => MachineInstance.stackMachineEncodingU.enc (cfg j)) k dep Wbound j)
    (hhold : ∀ (j : ℕ), ∀ i, ∀ t ∈ Icc (2 * Real.pi * (j : ℝ) + Real.pi / 6)
        (2 * Real.pi * (j : ℝ) + Real.pi / 2),
        |sol.u t i - sol.u (2 * Real.pi * (j : ℝ) + Real.pi / 6) i| ≤ εhold)
    (hradius : ∀ j, ∀ i, Wbound j i / k ^ dep j i + εhold ≤ MachineInstance.r_LE_U) :
    ∀ (j : ℕ), ∀ t ∈ Ico (2 * Real.pi * (j : ℝ) + Real.pi / 6) (2 * Real.pi * (j : ℝ) + Real.pi / 2),
      MachineInstance.UTube MachineInstance.r_LE_U (cfg j) (sol.u t) := by
  intro j
  exact selector_MU_hwin_of_weighted_repl sol cfg hk1 dep Wbound j (hhold j) (hradius j) (hMU j)

#print axioms muBoundaryError_repl
#print axioms muBoundaryError_nonneg_repl
#print axioms MUWeighted_repl
#print axioms MURecur_repl
#print axioms mu_weighted_step_repl
#print axioms weighted_boundary_to_radius_repl
#print axioms selector_MU_hwin_of_weighted_repl
#print axioms MUWeighted_all_of_init_step_repl
#print axioms selector_MU_utube_all_repl

end Ripple.BoundedUniversality.BGP
