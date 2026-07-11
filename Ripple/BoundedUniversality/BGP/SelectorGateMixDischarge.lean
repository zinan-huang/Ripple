import Ripple.BoundedUniversality.BGP.SelectorStackOpDischarge
import Ripple.BoundedUniversality.BGP.SelectorZWriteDischarge

/-!
Ripple.BoundedUniversality.BGP.SelectorGateMixDischarge
------------------------------------

Gate-mixture discharge for the stack-coordinate premise of
`selector_stack_faithful_tube`.

The finite-dimensional algebra is proved here.  The remaining selector-dynamics
input is carried as a named one-hot hypothesis on the live weights at the hold
time; it is the public logistic/sharpness obligation.
-/

noncomputable section

namespace Ripple.BoundedUniversality.BGP

open Filter
open scoped BigOperators Topology

/-! ## Diagonal branch evaluation -/

theorem evalBranch_eq_of_coord_eq {d B : ℕ} (D : BranchData d B)
    {Z W : Fin d → ℝ} {i : Fin d} (hcoord : Z i = W i) :
    BranchData.evalBranch D Z i = BranchData.evalBranch D W i := by
  simp [BranchData.evalBranch, hcoord]

theorem evalBranch_sub_eq_zero_of_coord_eq {d B : ℕ} (D : BranchData d B)
    {Z W : Fin d → ℝ} {i : Fin d} (hcoord : Z i = W i) :
    BranchData.evalBranch D Z i - BranchData.evalBranch D W i = 0 := by
  rw [evalBranch_eq_of_coord_eq D hcoord]
  ring

theorem evalBranch_abs_sub_eq_zero_of_coord_eq {d B : ℕ} (D : BranchData d B)
    {Z W : Fin d → ℝ} {i : Fin d} (hcoord : Z i = W i) :
    |BranchData.evalBranch D Z i - BranchData.evalBranch D W i| = 0 := by
  rw [evalBranch_sub_eq_zero_of_coord_eq D hcoord, abs_zero]

/-! ## Pure convex-mixture algebra -/

theorem selectorF_sub_selected_eq_sum_diffs
    {V : Type} [Fintype V] {d B : ℕ}
    (branch : V → BranchData d B) (Z : Fin d → ℝ) (Λ : V → ℝ)
    (vstar : V) (i : Fin d)
    (hsum : (∑ v : V, Λ v) = 1) :
    selectorF branch Z Λ i - BranchData.evalBranch (branch vstar) Z i =
      ∑ v : V, Λ v *
        (BranchData.evalBranch (branch v) Z i -
          BranchData.evalBranch (branch vstar) Z i) := by
  calc
    selectorF branch Z Λ i - BranchData.evalBranch (branch vstar) Z i
        = (∑ v : V, Λ v * BranchData.evalBranch (branch v) Z i) -
            (∑ v : V, Λ v) * BranchData.evalBranch (branch vstar) Z i := by
          simp [selectorF, hsum]
    _ = ∑ v : V, Λ v *
          (BranchData.evalBranch (branch v) Z i -
            BranchData.evalBranch (branch vstar) Z i) := by
          rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl ?_
          intro v _hv
          ring

theorem selectorF_onehot_bound
    {V : Type} [Fintype V] [DecidableEq V] {d B : ℕ}
    (branch : V → BranchData d B) (Z : Fin d → ℝ) (Λ : V → ℝ)
    (vstar : V) (i : Fin d) {R epsLam : ℝ}
    (hR : 0 ≤ R) (hepsLam : 0 ≤ epsLam)
    (hsum : (∑ v : V, Λ v) = 1)
    (hlam_nonneg : ∀ v, 0 ≤ Λ v)
    (hwrong : ∀ v, v ≠ vstar → Λ v ≤ epsLam)
    (hspread : ∀ v, v ≠ vstar →
      |BranchData.evalBranch (branch v) Z i -
        BranchData.evalBranch (branch vstar) Z i| ≤ R) :
    |selectorF branch Z Λ i - BranchData.evalBranch (branch vstar) Z i| ≤
      (Fintype.card V : ℝ) * R * epsLam := by
  have hdecomp := selectorF_sub_selected_eq_sum_diffs branch Z Λ vstar i hsum
  have hterm :
      ∀ v : V,
        |Λ v *
          (BranchData.evalBranch (branch v) Z i -
            BranchData.evalBranch (branch vstar) Z i)| ≤ epsLam * R := by
    intro v
    by_cases hv : v = vstar
    · subst hv
      simp [mul_nonneg hepsLam hR]
    · calc
        |Λ v *
          (BranchData.evalBranch (branch v) Z i -
            BranchData.evalBranch (branch vstar) Z i)|
            = |Λ v| *
              |BranchData.evalBranch (branch v) Z i -
                BranchData.evalBranch (branch vstar) Z i| := by
                rw [abs_mul]
        _ = Λ v *
              |BranchData.evalBranch (branch v) Z i -
                BranchData.evalBranch (branch vstar) Z i| := by
                rw [abs_of_nonneg (hlam_nonneg v)]
        _ ≤ epsLam * R :=
              mul_le_mul (hwrong v hv) (hspread v hv) (abs_nonneg _) hepsLam
  calc
    |selectorF branch Z Λ i - BranchData.evalBranch (branch vstar) Z i|
        = |∑ v : V, Λ v *
          (BranchData.evalBranch (branch v) Z i -
            BranchData.evalBranch (branch vstar) Z i)| := by
            rw [hdecomp]
    _ ≤ ∑ v : V, |Λ v *
          (BranchData.evalBranch (branch v) Z i -
            BranchData.evalBranch (branch vstar) Z i)| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _v : V, epsLam * R :=
          Finset.sum_le_sum (fun v _hv => hterm v)
    _ = (Fintype.card V : ℝ) * (epsLam * R) := by
          simp [Finset.sum_const, nsmul_eq_mul]
    _ = (Fintype.card V : ℝ) * R * epsLam := by
          ring

theorem selectorF_onehot_analog_bound
    {V : Type} [Fintype V] [DecidableEq V] {d B : ℕ}
    (branch : V → BranchData d B) (Z W : Fin d → ℝ) (Λ : V → ℝ)
    (vstar : V) (i : Fin d) {R epsLam : ℝ}
    (hR : 0 ≤ R) (hepsLam : 0 ≤ epsLam)
    (hsum : (∑ v : V, Λ v) = 1)
    (hlam_nonneg : ∀ v, 0 ≤ Λ v)
    (hwrong : ∀ v, v ≠ vstar → Λ v ≤ epsLam)
    (hspread : ∀ v, v ≠ vstar →
      |BranchData.evalBranch (branch v) Z i -
        BranchData.evalBranch (branch vstar) Z i| ≤ R)
    (hcoord : Z i = W i) :
    |selectorF branch Z Λ i - BranchData.evalBranch (branch vstar) W i| ≤
      (Fintype.card V : ℝ) * R * epsLam := by
  have hdiag :
      BranchData.evalBranch (branch vstar) Z i =
        BranchData.evalBranch (branch vstar) W i :=
    evalBranch_eq_of_coord_eq (branch vstar) hcoord
  rw [← hdiag]
  exact selectorF_onehot_bound branch Z Λ vstar i hR hepsLam
    hsum hlam_nonneg hwrong hspread

theorem selectorMixTarget_onehot_analog_bound
    {V : Type} [Fintype V] [DecidableEq V] {d B : ℕ}
    (branch : V → BranchData d B) (u : ℝ → Fin d → ℝ) (lam : V → ℝ → ℝ)
    (t : ℝ) (W : Fin d → ℝ) (vstar : V) (i : Fin d) {R epsLam : ℝ}
    (hR : 0 ≤ R) (hepsLam : 0 ≤ epsLam)
    (hsum : (∑ v : V, lam v t) = 1)
    (hlam_nonneg : ∀ v, 0 ≤ lam v t)
    (hwrong : ∀ v, v ≠ vstar → lam v t ≤ epsLam)
    (hspread : ∀ v, v ≠ vstar →
      |BranchData.evalBranch (branch v) (u t) i -
        BranchData.evalBranch (branch vstar) (u t) i| ≤ R)
    (hcoord : u t i = W i) :
    |selectorMixTarget branch u lam t i - BranchData.evalBranch (branch vstar) W i| ≤
      (Fintype.card V : ℝ) * R * epsLam := by
  simpa [selectorMixTarget] using
    selectorF_onehot_analog_bound branch (u t) W (fun v => lam v t) vstar i
      hR hepsLam hsum hlam_nonneg hwrong hspread hcoord

/-! ## Stack-coordinate M_U wrapper -/

def selectorGateMixHold (j : ℕ) : ℝ :=
  selectorZHold j

def selectorGateMixEps {V : Type} [Fintype V] (R : ℝ) (epsLam : ℕ → ℝ) : ℕ → ℝ :=
  fun j => (Fintype.card V : ℝ) * R * epsLam j

def selectorStackGateMixTargetU
    {p : DynGateParams} {chiReset chiGate kappa gain : ℝ → ℝ}
    {readoutP : MachineInstance.UniversalLocalView →
      (Fin MachineInstance.d_U → ℝ) → ℝ}
    (sol : SelectorDynSol MachineInstance.d_U MachineInstance.B_U
      MachineInstance.UniversalLocalView p selectorSchedule MachineInstance.branchU
      chiReset chiGate kappa gain readoutP)
    (s : Fin 4) : ℕ → ℝ :=
  fun j =>
    selectorMixTarget MachineInstance.branchU sol.u sol.lam
      (selectorGateMixHold j) (selectorStackCoordU s)

structure SelectorStackGateOneHotAtU
    {p : DynGateParams} {chiReset chiGate kappa gain : ℝ → ℝ}
    {readoutP : MachineInstance.UniversalLocalView →
      (Fin MachineInstance.d_U → ℝ) → ℝ}
    (sol : SelectorDynSol MachineInstance.d_U MachineInstance.B_U
      MachineInstance.UniversalLocalView p selectorSchedule MachineInstance.branchU
      chiReset chiGate kappa gain readoutP)
    (w : ℕ) (s : Fin 4) (x epsLam : ℕ → ℝ) (rho : ℝ) : Prop where
  lam_nonneg :
    ∀ j, expWeight (MachineInstance.B_U : ℝ) (selectorStackDepthU w s)
        (selectorStackErrorU w s x) j ≤ rho →
      ∀ v, 0 ≤ sol.lam v (selectorGateMixHold j)
  lam_sum :
    ∀ j, expWeight (MachineInstance.B_U : ℝ) (selectorStackDepthU w s)
        (selectorStackErrorU w s x) j ≤ rho →
      (∑ v : MachineInstance.UniversalLocalView, sol.lam v (selectorGateMixHold j)) = 1
  wrong_le :
    ∀ j, expWeight (MachineInstance.B_U : ℝ) (selectorStackDepthU w s)
        (selectorStackErrorU w s x) j ≤ rho →
      ∀ v, v ≠ MachineInstance.localViewU (selectorCfgU w j) →
        sol.lam v (selectorGateMixHold j) ≤ epsLam j

def SelectorStackBranchSpreadU
    {p : DynGateParams} {chiReset chiGate kappa gain : ℝ → ℝ}
    {readoutP : MachineInstance.UniversalLocalView →
      (Fin MachineInstance.d_U → ℝ) → ℝ}
    (sol : SelectorDynSol MachineInstance.d_U MachineInstance.B_U
      MachineInstance.UniversalLocalView p selectorSchedule MachineInstance.branchU
      chiReset chiGate kappa gain readoutP)
    (w : ℕ) (s : Fin 4) (R : ℝ) : Prop :=
  ∀ j, ∀ v, v ≠ MachineInstance.localViewU (selectorCfgU w j) →
    |BranchData.evalBranch (MachineInstance.branchU v)
        (sol.u (selectorGateMixHold j)) (selectorStackCoordU s) -
      BranchData.evalBranch
        (MachineInstance.branchU (MachineInstance.localViewU (selectorCfgU w j)))
        (sol.u (selectorGateMixHold j)) (selectorStackCoordU s)| ≤ R

theorem selectorStack_trueBranch_eq_opTargetU
    {p : DynGateParams} {chiReset chiGate kappa gain : ℝ → ℝ}
    {readoutP : MachineInstance.UniversalLocalView →
      (Fin MachineInstance.d_U → ℝ) → ℝ}
    (sol : SelectorDynSol MachineInstance.d_U MachineInstance.B_U
      MachineInstance.UniversalLocalView p selectorSchedule MachineInstance.branchU
      chiReset chiGate kappa gain readoutP)
    (w : ℕ) (s : Fin 4) (x : ℕ → ℝ) (j : ℕ)
    (hx_hold :
      sol.u (selectorGateMixHold j) (selectorStackCoordU s) = x j) :
    BranchData.evalBranch
        (MachineInstance.branchU (MachineInstance.localViewU (selectorCfgU w j)))
        (sol.u (selectorGateMixHold j)) (selectorStackCoordU s) =
      selectorStackOpTargetU w s x j := by
  unfold selectorStackOpTargetU
  exact evalBranch_eq_of_coord_eq
    (MachineInstance.branchU (MachineInstance.localViewU (selectorCfgU w j))) (by
      simp [selectorStackAnalogStateU, hx_hold])

theorem selectorStack_trueBranch_second_term_zero_U
    {p : DynGateParams} {chiReset chiGate kappa gain : ℝ → ℝ}
    {readoutP : MachineInstance.UniversalLocalView →
      (Fin MachineInstance.d_U → ℝ) → ℝ}
    (sol : SelectorDynSol MachineInstance.d_U MachineInstance.B_U
      MachineInstance.UniversalLocalView p selectorSchedule MachineInstance.branchU
      chiReset chiGate kappa gain readoutP)
    (w : ℕ) (s : Fin 4) (x : ℕ → ℝ) (j : ℕ)
    (hx_hold :
      sol.u (selectorGateMixHold j) (selectorStackCoordU s) = x j) :
    |BranchData.evalBranch
        (MachineInstance.branchU (MachineInstance.localViewU (selectorCfgU w j)))
        (sol.u (selectorGateMixHold j)) (selectorStackCoordU s) -
      selectorStackOpTargetU w s x j| = 0 := by
  rw [selectorStack_trueBranch_eq_opTargetU sol w s x j hx_hold, sub_self, abs_zero]

theorem selectorStack_gate_mix_discharge_U
    {p : DynGateParams} {chiReset chiGate kappa gain : ℝ → ℝ}
    {readoutP : MachineInstance.UniversalLocalView →
      (Fin MachineInstance.d_U → ℝ) → ℝ}
    (sol : SelectorDynSol MachineInstance.d_U MachineInstance.B_U
      MachineInstance.UniversalLocalView p selectorSchedule MachineInstance.branchU
      chiReset chiGate kappa gain readoutP)
    (w : ℕ) (s : Fin 4) (x epsLam : ℕ → ℝ) {R rho : ℝ}
    (hR : 0 ≤ R) (hepsLam : ∀ j, 0 ≤ epsLam j)
    (hx_hold :
      ∀ j, sol.u (selectorGateMixHold j) (selectorStackCoordU s) = x j)
    (honehot : SelectorStackGateOneHotAtU sol w s x epsLam rho)
    (hspread : SelectorStackBranchSpreadU sol w s R) :
    ∀ j,
      expWeight (MachineInstance.B_U : ℝ) (selectorStackDepthU w s)
          (selectorStackErrorU w s x) j ≤ rho →
        |selectorStackGateMixTargetU sol s j - selectorStackOpTargetU w s x j| ≤
          selectorGateMixEps (V := MachineInstance.UniversalLocalView) R epsLam j := by
  intro j hE
  let vstar : MachineInstance.UniversalLocalView :=
    MachineInstance.localViewU (selectorCfgU w j)
  let W : Fin MachineInstance.d_U → ℝ := selectorStackAnalogStateU w s x j
  have hcoord :
      sol.u (selectorGateMixHold j) (selectorStackCoordU s) =
        W (selectorStackCoordU s) := by
    simp [W, hx_hold j]
  have hcore :=
    selectorMixTarget_onehot_analog_bound MachineInstance.branchU sol.u sol.lam
      (selectorGateMixHold j) W vstar (selectorStackCoordU s)
      hR (hepsLam j) (honehot.lam_sum j hE) (honehot.lam_nonneg j hE)
      (honehot.wrong_le j hE) (hspread j) hcoord
  simpa [selectorStackGateMixTargetU, selectorStackOpTargetU, selectorGateMixEps,
    selectorGateMixHold, vstar, W] using hcore

theorem selectorGateMixEps_tendsto_zero
    {V : Type} [Fintype V] (R : ℝ) {epsLam : ℕ → ℝ}
    (hepsLam : Tendsto epsLam atTop (𝓝 0)) :
    Tendsto (selectorGateMixEps (V := V) R epsLam) atTop (𝓝 0) := by
  have h :
      Tendsto (fun j : ℕ => ((Fintype.card V : ℝ) * R) * epsLam j)
        atTop (𝓝 0) := by
    have h0 :
        Tendsto (fun j : ℕ => ((Fintype.card V : ℝ) * R) * epsLam j)
          atTop (𝓝 (((Fintype.card V : ℝ) * R) * 0)) :=
      tendsto_const_nhds.mul hepsLam
    simpa using h0
  simpa [selectorGateMixEps] using h

theorem selectorStack_gate_mix_eps_tendsto_zero_U
    (R : ℝ) {epsLam : ℕ → ℝ}
    (hepsLam : Tendsto epsLam atTop (𝓝 0)) :
    Tendsto (selectorGateMixEps
      (V := MachineInstance.UniversalLocalView) R epsLam) atTop (𝓝 0) :=
  selectorGateMixEps_tendsto_zero (V := MachineInstance.UniversalLocalView) R hepsLam

#print axioms selectorStack_gate_mix_discharge_U

end Ripple.BoundedUniversality.BGP
