import Ripple.BoundedUniversality.BGP.SelectorSelfConsistent
import Ripple.BoundedUniversality.BGP.SelectorGateSharpAssembly
import Ripple.BoundedUniversality.BGP.SelectorGateMixDischarge
import Ripple.BoundedUniversality.BGP.SelectorOneHotDischarge
import Ripple.BoundedUniversality.BGP.SelectorStackOpDischarge
import Ripple.BoundedUniversality.BGP.SelectorStackDepthSemantics

/-!
Ripple.BoundedUniversality.BGP.SelectorFaithfulCapstone
-----------------------------------

Self-consistent all-cycle exposure tube for the faithful selector stack readout.

The point of this capstone is that the gate-mix estimate is not carried as an
unconditional premise.  At cycle `j`, the simultaneous tube hypothesis gives
the five local-view coordinates: control plus the four stack coordinates.  Those
current facts give gate sharpness; sharpness feeds the named logistic/readout
contract for the wrong-view lambda weights; the one-hot mixture algebra gives
the gate-mix error; and the stack operation plus write reach gives the exposure
recurrence for the next cycle.
-/

noncomputable section

namespace Ripple.BoundedUniversality.BGP

open Finset
open Set
open scoped BigOperators
open Turing.PartrecToTM2

/-- The discrete stack signal read from a cycle-start vector. -/
def selectorStackValueU (u : ℕ → Fin MachineInstance.d_U → ℝ) (s : Fin 4) : ℕ → ℝ :=
  fun j => u j (selectorStackCoordU s)

/-- Control-coordinate error at cycle starts. -/
def selectorControlErrorU (w : ℕ) (u : ℕ → Fin MachineInstance.d_U → ℝ) : ℕ → ℝ :=
  fun j =>
    |u j MachineInstance.ctrlCoordU -
      (MachineInstance.confEncU (selectorCfgU w j) MachineInstance.ctrlCoordU : ℝ)|

/-- Exposure-weighted stack error for one concrete stack coordinate. -/
def selectorStackExpU (w : ℕ) (u : ℕ → Fin MachineInstance.d_U → ℝ)
    (s : Fin 4) : ℕ → ℝ :=
  fun j =>
    expWeight (MachineInstance.B_U : ℝ) (selectorStackDepthU w s)
      (selectorStackErrorU w s (selectorStackValueU u s)) j

/-- The wrong-view lambda budget used by the gate-mix discharge. -/
def selectorGateWrongEpsU
    {p : DynGateParams} {chiReset chiGate kappa gain : ℝ → ℝ}
    {readoutP : MachineInstance.UniversalLocalView →
      (Fin MachineInstance.d_U → ℝ) → ℝ}
    (sol : SelectorDynSol MachineInstance.d_U MachineInstance.B_U
      MachineInstance.UniversalLocalView p selectorSchedule MachineInstance.branchU
      chiReset chiGate kappa gain readoutP)
    (gateStart : ℕ → ℝ) (Qa0 rhoB Lmax Kint alpha : ℝ) : ℕ → ℝ :=
  selectorOneHotWrongEps Qa0 rhoB Lmax Kint alpha
    (fun j => sol.G (selectorGateMixHold j) - sol.G (gateStart j))

/-- Stack forcing term after the gate-mix and write defects are discharged. -/
def selectorStackOmegaU (w : ℕ) (epsLam : ℕ → ℝ)
    (epsWrite : Fin 4 → ℕ → ℝ) (R : ℝ) (s : Fin 4) : ℕ → ℝ :=
  fun j =>
    (MachineInstance.B_U : ℝ) ^ (selectorStackDepthU w s (j + 1) + 2) *
      (selectorGateMixEps (V := MachineInstance.UniversalLocalView) R epsLam j +
        epsWrite s j)

/-- The five coordinates participating in the self-consistent local-view tube. -/
inductive SelectorFaithfulCoordU where
  | ctrl : SelectorFaithfulCoordU
  | stack : Fin 4 → SelectorFaithfulCoordU

/-- Current all-five tube fact at one cycle. -/
structure SelectorFaithfulAllTubesAtU
    (w : ℕ) (u : ℕ → Fin MachineInstance.d_U → ℝ) (rho : ℝ) (j : ℕ) : Prop where
  ctrl : selectorControlErrorU w u j ≤ rho
  stack : ∀ s : Fin 4, selectorStackExpU w u s j ≤ rho

def selectorFaithfulCoordExpU
    (w : ℕ) (u : ℕ → Fin MachineInstance.d_U → ℝ) :
    SelectorFaithfulCoordU → ℕ → ℝ
  | .ctrl, j => selectorControlErrorU w u j
  | .stack s, j => selectorStackExpU w u s j

def selectorFaithfulCoordOmegaU
    (w : ℕ) (epsLam : ℕ → ℝ) (epsWrite : Fin 4 → ℕ → ℝ)
    (R : ℝ) (OmegaCtrl : ℕ → ℝ) :
    SelectorFaithfulCoordU → ℕ → ℝ
  | .ctrl, j => OmegaCtrl j
  | .stack s, j => selectorStackOmegaU w epsLam epsWrite R s j

/-- Simultaneous version of `expTube_uniform_conditional`. -/
theorem expTube_uniform_conditional_all
    {ι : Type*} {E Ω : ι → ℕ → ℝ} {rho : ℝ}
    (hstep : ∀ j, (∀ i, E i j ≤ rho) → ∀ i, E i (j + 1) ≤ E i j + Ω i j)
    (hres : ∀ i j, E i 0 + ∑ ell ∈ range j, Ω i ell ≤ rho) :
    ∀ j i, E i j ≤ rho := by
  have htel : ∀ j, ∀ i, E i j ≤ E i 0 + ∑ ell ∈ range j, Ω i ell := by
    intro j
    induction j with
    | zero =>
        intro i
        simp
    | succ j ih =>
        intro i
        have htube_j : ∀ i, E i j ≤ rho := fun i => le_trans (ih i) (hres i j)
        have hnext := hstep j htube_j i
        rw [sum_range_succ]
        calc
          E i (j + 1) ≤ E i j + Ω i j := hnext
          _ ≤ (E i 0 + ∑ ell ∈ range j, Ω i ell) + Ω i j := by
            linarith [ih i]
          _ = E i 0 + (∑ ell ∈ range j, Ω i ell + Ω i j) := by ring
  intro j i
  exact le_trans (htel j i) (hres i j)

/-- A current stack exposure bound gives the local stack-coordinate read bound. -/
theorem stackError_le_of_current_expTube
    (w : ℕ) (u : ℕ → Fin MachineInstance.d_U → ℝ) (s : Fin 4) {rho : ℝ} (j : ℕ)
    (hE : selectorStackExpU w u s j ≤ rho)
    (hrho :
      rho ≤ MachineInstance.r_LE_U * (MachineInstance.B_U : ℝ) ^ (2 : Int)) :
    |selectorStackValueU u s j -
        (MachineInstance.confEncU (selectorCfgU w j) (selectorStackCoordU s) : ℝ)| ≤
      MachineInstance.r_LE_U := by
  have hB : 1 ≤ (MachineInstance.B_U : ℝ) := by
    norm_num [MachineInstance.B_U]
  have he : 0 ≤ selectorStackErrorU w s (selectorStackValueU u s) j := abs_nonneg _
  have hread :
      (MachineInstance.B_U : ℝ) ^ (2 : Int) *
          selectorStackErrorU w s (selectorStackValueU u s) j ≤ rho :=
    localview_read_of_expTube (MachineInstance.B_U : ℝ) hB
      (selectorStackDepthU w s)
      (selectorStackErrorU w s (selectorStackValueU u s)) j
      (selectorStackDepthU_nonneg w s j) he hE
  exact stackError_le_of_faithful_read w s (selectorStackValueU u s) j hread hrho

/--
Pointwise gate sharpness from the current five-coordinate tube.

The existing all-tube wrapper `selector_gate_sharp_of_stackTubes_and_control`
has a global `∀ n` signature.  This pointwise form is what the self-consistent
induction needs at cycle `j`.
-/
theorem selector_gate_sharp_of_current_all_tubes
    (eta : ℚ) (heta : 0 < eta) {w j : ℕ}
    {u : ℕ → Fin MachineInstance.d_U → ℝ} {rho : ℝ}
    (hrho_stack :
      rho ≤ MachineInstance.r_LE_U * (MachineInstance.B_U : ℝ) ^ (2 : Int))
    (hrho_ctrl : rho ≤ MachineInstance.r_LE_U)
    (htube : SelectorFaithfulAllTubesAtU w u rho j) :
    GateAtomSharpnessN MachineInstance.universalViewSpecN
      (gateSelectorAtomsCoordN (MachineInstance.universalGateAtoms eta heta))
      (u j) (MachineInstance.localViewU (selectorCfgU w j)) := by
  have hctrl :
      |u j MachineInstance.ctrlCoordU -
          (MachineInstance.confEncU (selectorCfgU w j) MachineInstance.ctrlCoordU : ℝ)| ≤
        MachineInstance.r_LE_U :=
    le_trans htube.ctrl hrho_ctrl
  refine selector_gate_sharp_of_coord_tubes eta heta hctrl ?_ ?_ ?_ ?_
  · simpa [selectorStackValueU, selectorStackCoordU, MachineInstance.stackCoordFinU,
      MachineInstance.stackIndexU, MachineInstance.stackKindOfIndexU,
      MachineInstance.stackCoordU] using
      stackError_le_of_current_expTube w u (MachineInstance.stackIndexU K'.main)
        j (htube.stack (MachineInstance.stackIndexU K'.main)) hrho_stack
  · simpa [selectorStackValueU, selectorStackCoordU, MachineInstance.stackCoordFinU,
      MachineInstance.stackIndexU, MachineInstance.stackKindOfIndexU,
      MachineInstance.stackCoordU] using
      stackError_le_of_current_expTube w u (MachineInstance.stackIndexU K'.rev)
        j (htube.stack (MachineInstance.stackIndexU K'.rev)) hrho_stack
  · simpa [selectorStackValueU, selectorStackCoordU, MachineInstance.stackCoordFinU,
      MachineInstance.stackIndexU, MachineInstance.stackKindOfIndexU,
      MachineInstance.stackCoordU] using
      stackError_le_of_current_expTube w u (MachineInstance.stackIndexU K'.aux)
        j (htube.stack (MachineInstance.stackIndexU K'.aux)) hrho_stack
  · simpa [selectorStackValueU, selectorStackCoordU, MachineInstance.stackCoordFinU,
      MachineInstance.stackIndexU, MachineInstance.stackKindOfIndexU,
      MachineInstance.stackCoordU] using
      stackError_le_of_current_expTube w u (MachineInstance.stackIndexU K'.stack)
        j (htube.stack (MachineInstance.stackIndexU K'.stack)) hrho_stack

/--
Single-window `SelectorDynSol` wrong-view estimate whose readout negativity is
provided from the sharp gate at this same cycle.
-/
theorem selectorDyn_oneHot_wrong_weight_bound_at_of_sharp
    {d B : ℕ} {V : Type} [Fintype V] [DecidableEq V]
    {p : DynGateParams} {sched : PhaseSchedule} {branch : V → BranchData d B}
    {chiReset chiGate kappa gain : ℝ → ℝ}
    {readoutP : V → (Fin d → ℝ) → ℝ}
    (sol : SelectorDynSol d B V p sched branch chiReset chiGate kappa gain readoutP)
    (vstar v : V) (hv : v ≠ vstar)
    {a b : ℕ → ℝ} {alpha Lmax rhoB Kint Qa0 : ℝ} (j : ℕ)
    (hab : a j ≤ b j) (hLmax1 : Lmax < 1)
    (hdom : ∀ t ∈ Ico (a j) (b j), t ∈ sched.domain)
    (hr0 : ∀ t ∈ Ico (a j) (b j), 0 ≤ chiGate t * gain t)
    (readout_neg_of_sharp :
      ∀ v, v ≠ vstar → ∀ t ∈ Ico (a j) (b j), sol.Pval v t ≤ -alpha)
    (hunit : ∀ t ∈ Icc (a j) (b j), 0 < sol.lam v t ∧ sol.lam v t < 1)
    (reset_odds : sol.lam v (a j) / (1 - sol.lam v (a j)) ≤ Qa0)
    (hLub : ∀ t ∈ Icc (a j) (b j), sol.lam v t ≤ Lmax)
    (hrho_ge : ∀ t ∈ Ico (a j) (b j),
      -rhoB ≤ chiReset t * kappa t * (1 / 2 - sol.lam v t))
    (hrho_le : ∀ t ∈ Ico (a j) (b j),
      chiReset t * kappa t * (1 / 2 - sol.lam v t) ≤ rhoB)
    (hrhoB : 0 ≤ rhoB)
    (hint :
      (∫ t in a j..b j, Real.exp (alpha * (sol.G t - sol.G (a j)))) ≤ Kint)
    (hKint : 0 ≤ Kint) :
    sol.lam v (b j) ≤ selectorOneHotWrongEps Qa0 rhoB Lmax Kint alpha
      (fun j => sol.G (b j) - sol.G (a j)) j := by
  simpa [selectorOneHotWrongEps] using
    selector_oneHot_wrong_weight_bound_window (vstar := vstar) (v := v) hv
      (r := fun t => chiGate t * gain t) (G := sol.G)
      (lam := fun v t => sol.lam v t) (P := sol.Pval)
      (ρ := fun v t => chiReset t * kappa t * (1 / 2 - sol.lam v t))
      hab hLmax1 sol.cont_G
      (by
        intro t ht
        have h := (sol.lam_hasDeriv v t (hdom t ht)).hasDerivWithinAt (s := Ici t)
        convert h using 1
        simp only [SelectorDynSol.Pval]
        ring)
      (by
        intro t ht
        have h := (sol.G_hasDeriv t (hdom t ht)).hasDerivWithinAt (s := Ici t)
        simpa using h)
      ((sol.cont_lam v).continuousOn) hr0 readout_neg_of_sharp hunit reset_odds
      hLub hrho_ge hrho_le hrhoB hint hKint

/-- Pointwise gate-mix discharge from the one-hot lambda facts at the hold time. -/
theorem selectorStack_gate_mix_discharge_at_U
    {p : DynGateParams} {chiReset chiGate kappa gain : ℝ → ℝ}
    {readoutP : MachineInstance.UniversalLocalView →
      (Fin MachineInstance.d_U → ℝ) → ℝ}
    (sol : SelectorDynSol MachineInstance.d_U MachineInstance.B_U
      MachineInstance.UniversalLocalView p selectorSchedule MachineInstance.branchU
      chiReset chiGate kappa gain readoutP)
    (w : ℕ) (s : Fin 4) (x epsLam : ℕ → ℝ) {R : ℝ} (j : ℕ)
    (hR : 0 ≤ R) (hepsLam : 0 ≤ epsLam j)
    (hx_hold :
      sol.u (selectorGateMixHold j) (selectorStackCoordU s) = x j)
    (hlam_nonneg :
      ∀ v, 0 ≤ sol.lam v (selectorGateMixHold j))
    (hlam_sum :
      (∑ v : MachineInstance.UniversalLocalView, sol.lam v (selectorGateMixHold j)) = 1)
    (hwrong :
      ∀ v, v ≠ MachineInstance.localViewU (selectorCfgU w j) →
        sol.lam v (selectorGateMixHold j) ≤ epsLam j)
    (hspread :
      ∀ v, v ≠ MachineInstance.localViewU (selectorCfgU w j) →
        |BranchData.evalBranch (MachineInstance.branchU v)
            (sol.u (selectorGateMixHold j)) (selectorStackCoordU s) -
          BranchData.evalBranch
            (MachineInstance.branchU (MachineInstance.localViewU (selectorCfgU w j)))
            (sol.u (selectorGateMixHold j)) (selectorStackCoordU s)| ≤ R) :
    |selectorStackGateMixTargetU sol s j - selectorStackOpTargetU w s x j| ≤
      selectorGateMixEps (V := MachineInstance.UniversalLocalView) R epsLam j := by
  let vstar : MachineInstance.UniversalLocalView :=
    MachineInstance.localViewU (selectorCfgU w j)
  let W : Fin MachineInstance.d_U → ℝ := selectorStackAnalogStateU w s x j
  have hcoord :
      sol.u (selectorGateMixHold j) (selectorStackCoordU s) =
        W (selectorStackCoordU s) := by
    simp [W, hx_hold]
  have hcore :=
    selectorMixTarget_onehot_analog_bound MachineInstance.branchU sol.u sol.lam
      (selectorGateMixHold j) W vstar (selectorStackCoordU s)
      hR hepsLam hlam_sum hlam_nonneg hwrong hspread hcoord
  simpa [selectorStackGateMixTargetU, selectorStackOpTargetU, selectorGateMixEps,
    selectorGateMixHold, vstar, W] using hcore

/-- One stack-coordinate exposure recurrence after gate-mix and write reach are known. -/
theorem selectorStack_expstep_from_gate_mix_at_U
    {p : DynGateParams} {chiReset chiGate kappa gain : ℝ → ℝ}
    {readoutP : MachineInstance.UniversalLocalView →
      (Fin MachineInstance.d_U → ℝ) → ℝ}
    (sol : SelectorDynSol MachineInstance.d_U MachineInstance.B_U
      MachineInstance.UniversalLocalView p selectorSchedule MachineInstance.branchU
      chiReset chiGate kappa gain readoutP)
    (w : ℕ) (u : ℕ → Fin MachineInstance.d_U → ℝ) (s : Fin 4)
    (epsMix epsWrite : ℕ → ℝ) (j : ℕ)
    (hop :
      SelectorStackOpClassification w s (selectorStackValueU u s)
        (selectorStackOpTargetU w s (selectorStackValueU u s)) j)
    (hmix :
      |selectorStackGateMixTargetU sol s j -
        selectorStackOpTargetU w s (selectorStackValueU u s) j| ≤ epsMix j)
    (hwrite :
      |selectorStackValueU u s (j + 1) - selectorStackGateMixTargetU sol s j| ≤
        epsWrite j) :
    selectorStackExpU w u s (j + 1) ≤
      selectorStackExpU w u s j +
        (MachineInstance.B_U : ℝ) ^ (selectorStackDepthU w s (j + 1) + 2) *
          (epsMix j + epsWrite j) := by
  let H : ℕ → Int := selectorStackDepthU w s
  let e : ℕ → ℝ := selectorStackErrorU w s (selectorStackValueU u s)
  let xi : ℕ → ℝ := fun j => epsMix j + epsWrite j
  have hBpos : 0 < (MachineInstance.B_U : ℝ) := by
    norm_num [MachineInstance.B_U]
  have hrec :
      e (j + 1) ≤
        (MachineInstance.B_U : ℝ) ^ (H j - H (j + 1)) * e j + xi j := by
    have hmixCode :
        |selectorStackGateMixTargetU sol s j - selectorStackCodeU w s (j + 1)| ≤
          epsMix j +
            (MachineInstance.B_U : ℝ) ^ (H j - H (j + 1)) * e j := by
      calc
        |selectorStackGateMixTargetU sol s j - selectorStackCodeU w s (j + 1)|
            ≤ |selectorStackGateMixTargetU sol s j -
                  selectorStackOpTargetU w s (selectorStackValueU u s) j| +
                |selectorStackOpTargetU w s (selectorStackValueU u s) j -
                  selectorStackCodeU w s (j + 1)| := by
              exact abs_sub_le (selectorStackGateMixTargetU sol s j)
                (selectorStackOpTargetU w s (selectorStackValueU u s) j)
                (selectorStackCodeU w s (j + 1))
        _ ≤ epsMix j +
              (MachineInstance.B_U : ℝ) ^ (H j - H (j + 1)) * e j := by
              exact add_le_add hmix hop.op_error
    calc
      e (j + 1)
          = |selectorStackValueU u s (j + 1) - selectorStackCodeU w s (j + 1)| := by
            rfl
      _ ≤ |selectorStackValueU u s (j + 1) - selectorStackGateMixTargetU sol s j| +
            |selectorStackGateMixTargetU sol s j - selectorStackCodeU w s (j + 1)| := by
            exact abs_sub_le (selectorStackValueU u s (j + 1))
              (selectorStackGateMixTargetU sol s j)
              (selectorStackCodeU w s (j + 1))
      _ ≤ epsWrite j +
            (epsMix j +
              (MachineInstance.B_U : ℝ) ^ (H j - H (j + 1)) * e j) := by
            exact add_le_add hwrite hmixCode
      _ =
            (MachineInstance.B_U : ℝ) ^ (H j - H (j + 1)) * e j + xi j := by
            simp [xi]
            ring
  simpa [selectorStackExpU, selectorStackOmegaU, H, e, xi] using
    expWeight_nonexpansive (MachineInstance.B_U : ℝ) hBpos H e xi j hrec

/--
Faithful all-cycle exposure tube, self-consistent.

The theorem carries contract-status hypotheses (control recurrence, write reach,
reset odds / lambda box facts, readout negativity from sharpness, branch spread,
and stack operation classification via `hdepth`).  It does not carry an
unconditional gate-mix premise.  The gate-mix estimate is produced inside the
cycle step from the current simultaneous tube.
-/
theorem selector_faithful_tube_selfconsistent
    {p : DynGateParams} {chiReset chiGate kappa gain : ℝ → ℝ}
    {readoutP : MachineInstance.UniversalLocalView →
      (Fin MachineInstance.d_U → ℝ) → ℝ}
    (sol : SelectorDynSol MachineInstance.d_U MachineInstance.B_U
      MachineInstance.UniversalLocalView p selectorSchedule MachineInstance.branchU
      chiReset chiGate kappa gain readoutP)
    (eta : ℚ) (heta : 0 < eta) (w : ℕ)
    (u : ℕ → Fin MachineInstance.d_U → ℝ)
    (gateStart : ℕ → ℝ)
    (epsLam OmegaCtrl : ℕ → ℝ) (epsWrite : Fin 4 → ℕ → ℝ)
    {R rho alpha Lmax rhoB Kint Qa0 Cctrl rctrl : ℝ}
    (Cstack rstack : Fin 4 → ℝ)
    (hepsLam :
      epsLam = selectorGateWrongEpsU sol gateStart Qa0 rhoB Lmax Kint alpha)
    (hrho_stack :
      rho ≤ MachineInstance.r_LE_U * (MachineInstance.B_U : ℝ) ^ (2 : Int))
    (hrho_ctrl : rho ≤ MachineInstance.r_LE_U)
    (hcontrol_step :
      ∀ j, SelectorFaithfulAllTubesAtU w u rho j →
        selectorControlErrorU w u (j + 1) ≤
          selectorControlErrorU w u j + OmegaCtrl j)
    (hcontrol_geometric :
      ∀ ell, OmegaCtrl ell ≤ Cctrl * rctrl ^ ell)
    (hCctrl : 0 ≤ Cctrl) (hrctrl0 : 0 ≤ rctrl) (hrctrl1 : rctrl < 1)
    (hcontrol_capacity :
      selectorControlErrorU w u 0 + Cctrl / (1 - rctrl) ≤ rho)
    (hdepth : SelectorStackDepthStepSemanticsU)
    (hx_hold :
      ∀ s j, sol.u (selectorGateMixHold j) (selectorStackCoordU s) =
        selectorStackValueU u s j)
    (hwrite_reach :
      ∀ s j,
        |selectorStackValueU u s (j + 1) - selectorStackGateMixTargetU sol s j| ≤
          epsWrite s j)
    (hR : 0 ≤ R)
    (hbranch_spread :
      ∀ s, SelectorStackBranchSpreadU sol w s R)
    (hstack_geometric :
      ∀ s ell, selectorStackOmegaU w epsLam epsWrite R s ell ≤
        Cstack s * rstack s ^ ell)
    (hCstack : ∀ s, 0 ≤ Cstack s)
    (hrstack0 : ∀ s, 0 ≤ rstack s)
    (hrstack1 : ∀ s, rstack s < 1)
    (hstack_capacity :
      ∀ s, selectorStackExpU w u s 0 + Cstack s / (1 - rstack s) ≤ rho)
    (hab :
      ∀ j, gateStart j ≤ selectorGateMixHold j)
    (hLmax1 : Lmax < 1)
    (hQa0 : 0 ≤ Qa0)
    (hdom :
      ∀ j, ∀ t ∈ Ico (gateStart j) (selectorGateMixHold j),
        t ∈ selectorSchedule.domain)
    (hr0 :
      ∀ j, ∀ t ∈ Ico (gateStart j) (selectorGateMixHold j),
        0 ≤ chiGate t * gain t)
    (hreadout_neg_of_sharp :
      ∀ j,
        GateAtomSharpnessN MachineInstance.universalViewSpecN
          (gateSelectorAtomsCoordN (MachineInstance.universalGateAtoms eta heta))
          (u j) (MachineInstance.localViewU (selectorCfgU w j)) →
        ∀ v, v ≠ MachineInstance.localViewU (selectorCfgU w j) →
          ∀ t ∈ Ico (gateStart j) (selectorGateMixHold j), sol.Pval v t ≤ -alpha)
    (hlam_nonneg_hold :
      ∀ j, ∀ v : MachineInstance.UniversalLocalView,
        0 ≤ sol.lam v (selectorGateMixHold j))
    (hlam_sum_hold :
      ∀ j,
        (∑ v : MachineInstance.UniversalLocalView, sol.lam v (selectorGateMixHold j)) = 1)
    (hunit :
      ∀ j, ∀ v : MachineInstance.UniversalLocalView,
        ∀ t ∈ Icc (gateStart j) (selectorGateMixHold j),
          0 < sol.lam v t ∧ sol.lam v t < 1)
    (hreset_odds :
      ∀ j, ∀ v : MachineInstance.UniversalLocalView,
        sol.lam v (gateStart j) / (1 - sol.lam v (gateStart j)) ≤ Qa0)
    (hLub :
      ∀ j, ∀ v : MachineInstance.UniversalLocalView,
        ∀ t ∈ Icc (gateStart j) (selectorGateMixHold j), sol.lam v t ≤ Lmax)
    (hrho_ge :
      ∀ j, ∀ v : MachineInstance.UniversalLocalView,
        ∀ t ∈ Ico (gateStart j) (selectorGateMixHold j),
          -rhoB ≤ chiReset t * kappa t * (1 / 2 - sol.lam v t))
    (hrho_le :
      ∀ j, ∀ v : MachineInstance.UniversalLocalView,
        ∀ t ∈ Ico (gateStart j) (selectorGateMixHold j),
          chiReset t * kappa t * (1 / 2 - sol.lam v t) ≤ rhoB)
    (hrhoB : 0 ≤ rhoB)
    (hint :
      ∀ j,
        (∫ t in gateStart j..selectorGateMixHold j,
          Real.exp (alpha * (sol.G t - sol.G (gateStart j)))) ≤ Kint)
    (hKint : 0 ≤ Kint) :
    ∀ j, SelectorFaithfulAllTubesAtU w u rho j := by
  subst epsLam
  let epsLam' : ℕ → ℝ :=
    selectorGateWrongEpsU sol gateStart Qa0 rhoB Lmax Kint alpha
  let E : SelectorFaithfulCoordU → ℕ → ℝ := selectorFaithfulCoordExpU w u
  let Omega : SelectorFaithfulCoordU → ℕ → ℝ :=
    selectorFaithfulCoordOmegaU w epsLam' epsWrite R OmegaCtrl
  have hepsLam_nonneg : ∀ j, 0 ≤ epsLam' j := by
    intro j
    exact selectorOneHotWrongEps_nonneg hQa0 hrhoB hKint j
  have hstep :
      ∀ j, (∀ i, E i j ≤ rho) → ∀ i, E i (j + 1) ≤ E i j + Omega i j := by
    intro j hall i
    have htube : SelectorFaithfulAllTubesAtU w u rho j := by
      refine ⟨?_, ?_⟩
      · simpa [E, selectorFaithfulCoordExpU] using hall SelectorFaithfulCoordU.ctrl
      · intro s
        simpa [E, selectorFaithfulCoordExpU] using hall (SelectorFaithfulCoordU.stack s)
    have hsharp :=
      selector_gate_sharp_of_current_all_tubes eta heta hrho_stack hrho_ctrl htube
    cases i with
    | ctrl =>
        simpa [E, Omega, selectorFaithfulCoordExpU, selectorFaithfulCoordOmegaU] using
          hcontrol_step j htube
    | stack s =>
        have hwrong :
            ∀ v, v ≠ MachineInstance.localViewU (selectorCfgU w j) →
              sol.lam v (selectorGateMixHold j) ≤ epsLam' j := by
          intro v hv
          exact
            selectorDyn_oneHot_wrong_weight_bound_at_of_sharp
              (sol := sol)
              (vstar := MachineInstance.localViewU (selectorCfgU w j)) (v := v) hv
              (a := gateStart) (b := selectorGateMixHold)
              (alpha := alpha) (Lmax := Lmax) (rhoB := rhoB)
              (Kint := Kint) (Qa0 := Qa0) j
              (hab j) hLmax1 (hdom j) (hr0 j)
              (hreadout_neg_of_sharp j hsharp)
              (hunit j v) (hreset_odds j v) (hLub j v)
              (hrho_ge j v) (hrho_le j v) hrhoB (hint j) hKint
        have hmix :
            |selectorStackGateMixTargetU sol s j -
              selectorStackOpTargetU w s (selectorStackValueU u s) j| ≤
              selectorGateMixEps (V := MachineInstance.UniversalLocalView) R epsLam' j :=
          selectorStack_gate_mix_discharge_at_U sol w s (selectorStackValueU u s)
            epsLam' j hR (hepsLam_nonneg j) (hx_hold s j)
            (hlam_nonneg_hold j) (hlam_sum_hold j) hwrong (hbranch_spread s j)
        have hop :=
          selectorStackOpClassificationU hdepth w s (selectorStackValueU u s) j
        have hnext :=
          selectorStack_expstep_from_gate_mix_at_U sol w u s
            (selectorGateMixEps (V := MachineInstance.UniversalLocalView) R epsLam')
            (epsWrite s) j hop hmix (hwrite_reach s j)
        simpa [E, Omega, selectorFaithfulCoordExpU, selectorFaithfulCoordOmegaU,
          selectorStackOmegaU, epsLam'] using hnext
  have hres : ∀ i j, E i 0 + ∑ ell ∈ range j, Omega i ell ≤ rho := by
    intro i j
    cases i with
    | ctrl =>
        have h :=
          expTube_reserve_geometric
            (E := fun n => selectorControlErrorU w u n)
            (Ω := OmegaCtrl)
            (C := Cctrl) (r := rctrl)
            hcontrol_geometric hCctrl hrctrl0 hrctrl1 j
        exact le_trans
          (by
            simpa [E, Omega, selectorFaithfulCoordExpU, selectorFaithfulCoordOmegaU]
              using h)
          hcontrol_capacity
    | stack s =>
        have h :=
          expTube_reserve_geometric
            (E := fun n => selectorStackExpU w u s n)
            (Ω := fun n => selectorStackOmegaU w epsLam' epsWrite R s n)
            (C := Cstack s) (r := rstack s)
            (hstack_geometric s) (hCstack s) (hrstack0 s) (hrstack1 s) j
        exact le_trans
          (by
            simpa [E, Omega, selectorFaithfulCoordExpU, selectorFaithfulCoordOmegaU,
              selectorStackOmegaU, epsLam'] using h)
          (hstack_capacity s)
  have hall : ∀ j i, E i j ≤ rho :=
    expTube_uniform_conditional_all hstep hres
  intro j
  exact {
    ctrl := by
      simpa [E, selectorFaithfulCoordExpU] using hall j .ctrl
    stack := by
      intro s
      simpa [E, selectorFaithfulCoordExpU] using hall j (.stack s)
  }

/-- Concrete version of `selector_faithful_tube_selfconsistent` for `M_U`.

The old theorem is kept as the reusable interface, but the `M_U` capstone no
longer carries `SelectorStackDepthStepSemanticsU`: it is supplied by
`selectorStackDepthStepSemanticsU_proved`. -/
theorem selector_faithful_tube_selfconsistent_concrete
    {p : DynGateParams} {chiReset chiGate kappa gain : ℝ → ℝ}
    {readoutP : MachineInstance.UniversalLocalView →
      (Fin MachineInstance.d_U → ℝ) → ℝ}
    (sol : SelectorDynSol MachineInstance.d_U MachineInstance.B_U
      MachineInstance.UniversalLocalView p selectorSchedule MachineInstance.branchU
      chiReset chiGate kappa gain readoutP)
    (eta : ℚ) (heta : 0 < eta) (w : ℕ)
    (u : ℕ → Fin MachineInstance.d_U → ℝ)
    (gateStart : ℕ → ℝ)
    (epsLam OmegaCtrl : ℕ → ℝ) (epsWrite : Fin 4 → ℕ → ℝ)
    {R rho alpha Lmax rhoB Kint Qa0 Cctrl rctrl : ℝ}
    (Cstack rstack : Fin 4 → ℝ)
    (hepsLam :
      epsLam = selectorGateWrongEpsU sol gateStart Qa0 rhoB Lmax Kint alpha)
    (hrho_stack :
      rho ≤ MachineInstance.r_LE_U * (MachineInstance.B_U : ℝ) ^ (2 : Int))
    (hrho_ctrl : rho ≤ MachineInstance.r_LE_U)
    (hcontrol_step :
      ∀ j, SelectorFaithfulAllTubesAtU w u rho j →
        selectorControlErrorU w u (j + 1) ≤
          selectorControlErrorU w u j + OmegaCtrl j)
    (hcontrol_geometric :
      ∀ ell, OmegaCtrl ell ≤ Cctrl * rctrl ^ ell)
    (hCctrl : 0 ≤ Cctrl) (hrctrl0 : 0 ≤ rctrl) (hrctrl1 : rctrl < 1)
    (hcontrol_capacity :
      selectorControlErrorU w u 0 + Cctrl / (1 - rctrl) ≤ rho)
    (hx_hold :
      ∀ s j, sol.u (selectorGateMixHold j) (selectorStackCoordU s) =
        selectorStackValueU u s j)
    (hwrite_reach :
      ∀ s j,
        |selectorStackValueU u s (j + 1) - selectorStackGateMixTargetU sol s j| ≤
          epsWrite s j)
    (hR : 0 ≤ R)
    (hbranch_spread :
      ∀ s, SelectorStackBranchSpreadU sol w s R)
    (hstack_geometric :
      ∀ s ell, selectorStackOmegaU w epsLam epsWrite R s ell ≤
        Cstack s * rstack s ^ ell)
    (hCstack : ∀ s, 0 ≤ Cstack s)
    (hrstack0 : ∀ s, 0 ≤ rstack s)
    (hrstack1 : ∀ s, rstack s < 1)
    (hstack_capacity :
      ∀ s, selectorStackExpU w u s 0 + Cstack s / (1 - rstack s) ≤ rho)
    (hab :
      ∀ j, gateStart j ≤ selectorGateMixHold j)
    (hLmax1 : Lmax < 1)
    (hQa0 : 0 ≤ Qa0)
    (hdom :
      ∀ j, ∀ t ∈ Ico (gateStart j) (selectorGateMixHold j),
        t ∈ selectorSchedule.domain)
    (hr0 :
      ∀ j, ∀ t ∈ Ico (gateStart j) (selectorGateMixHold j),
        0 ≤ chiGate t * gain t)
    (hreadout_neg_of_sharp :
      ∀ j,
        GateAtomSharpnessN MachineInstance.universalViewSpecN
          (gateSelectorAtomsCoordN (MachineInstance.universalGateAtoms eta heta))
          (u j) (MachineInstance.localViewU (selectorCfgU w j)) →
        ∀ v, v ≠ MachineInstance.localViewU (selectorCfgU w j) →
          ∀ t ∈ Ico (gateStart j) (selectorGateMixHold j), sol.Pval v t ≤ -alpha)
    (hlam_nonneg_hold :
      ∀ j, ∀ v : MachineInstance.UniversalLocalView,
        0 ≤ sol.lam v (selectorGateMixHold j))
    (hlam_sum_hold :
      ∀ j,
        (∑ v : MachineInstance.UniversalLocalView, sol.lam v (selectorGateMixHold j)) = 1)
    (hunit :
      ∀ j, ∀ v : MachineInstance.UniversalLocalView,
        ∀ t ∈ Icc (gateStart j) (selectorGateMixHold j),
          0 < sol.lam v t ∧ sol.lam v t < 1)
    (hreset_odds :
      ∀ j, ∀ v : MachineInstance.UniversalLocalView,
        sol.lam v (gateStart j) / (1 - sol.lam v (gateStart j)) ≤ Qa0)
    (hLub :
      ∀ j, ∀ v : MachineInstance.UniversalLocalView,
        ∀ t ∈ Icc (gateStart j) (selectorGateMixHold j), sol.lam v t ≤ Lmax)
    (hrho_ge :
      ∀ j, ∀ v : MachineInstance.UniversalLocalView,
        ∀ t ∈ Ico (gateStart j) (selectorGateMixHold j),
          -rhoB ≤ chiReset t * kappa t * (1 / 2 - sol.lam v t))
    (hrho_le :
      ∀ j, ∀ v : MachineInstance.UniversalLocalView,
        ∀ t ∈ Ico (gateStart j) (selectorGateMixHold j),
          chiReset t * kappa t * (1 / 2 - sol.lam v t) ≤ rhoB)
    (hrhoB : 0 ≤ rhoB)
    (hint :
      ∀ j,
        (∫ t in gateStart j..selectorGateMixHold j,
          Real.exp (alpha * (sol.G t - sol.G (gateStart j)))) ≤ Kint)
    (hKint : 0 ≤ Kint) :
    ∀ j, SelectorFaithfulAllTubesAtU w u rho j :=
  selector_faithful_tube_selfconsistent sol eta heta w u gateStart
    epsLam OmegaCtrl epsWrite Cstack rstack hepsLam hrho_stack hrho_ctrl
    hcontrol_step hcontrol_geometric hCctrl hrctrl0 hrctrl1 hcontrol_capacity
    selectorStackDepthStepSemanticsU_proved hx_hold hwrite_reach hR
    hbranch_spread hstack_geometric hCstack hrstack0 hrstack1 hstack_capacity
    hab hLmax1 hQa0 hdom hr0 hreadout_neg_of_sharp hlam_nonneg_hold
    hlam_sum_hold hunit hreset_odds hLub hrho_ge hrho_le hrhoB hint hKint

#print axioms selector_faithful_tube_selfconsistent_concrete

end Ripple.BoundedUniversality.BGP
