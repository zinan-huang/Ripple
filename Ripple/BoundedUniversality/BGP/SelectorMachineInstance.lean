import Ripple.BoundedUniversality.BGP.MachineInstance
import Ripple.BoundedUniversality.BGP.SelectorField

/-!
Ripple.BoundedUniversality.BGP.SelectorMachineInstance
----------------------------------
M_U (universal machine) instantiation of the clock-driven selector path.  Mirrors
`FinalAssembly.lean`'s discharge of the fixed-precision contract path, but feeds the
generic selector machinery of `SelectorField.lean`.  This file discharges, for the
universal machine, the two inputs of `bgp_unconditional_selector` (the field package
and the per-input `hsupply`).  See `HANDOFF/fin3-MU-instantiation-blueprint.md`.

First brick: the margins-from-tube fact (the `hbranch_of_window` analog) — at any
point in the encoding tube, the universal gate atoms' Bernstein readout separates the
true local view from all others by the fixed margin `1/2 - errSel`.
-/

noncomputable section

namespace Ripple.BoundedUniversality.BGP

open scoped BigOperators

/-- **M_U margins from the encoding tube.**  At any point `Z` in the `r_LE_U`-tube of a
universal config `c`, the coarse Bernstein readout `LambdaN` of the universal gate atoms
separates the true local view `localViewU c` from every other view by the fixed margin
`1/2 - errSel`: `Pval vstar ≥ 1/2 - errSel` and `Pval v ≤ -(1/2 - errSel)` for `v ≠ vstar`,
where `Pval v = LambdaN(...) v - 1/2`.  Chains
`universalGateAtoms_sharpness → gate_view_selectorsN_SEL1_hypotheses → coarse_margin_of_sel1`.
This is the margins-from-tube fact the selector simultaneous-induction tracking consumes
(the `hbranch_of_window` analog), with `errSel = atoms.errSel → 0` as `eta → 0`. -/
theorem universal_selector_margins_of_tube
    (eta : ℚ) (heta : 0 < eta)
    {c : MachineInstance.UConf} {Z : Fin MachineInstance.d_U → ℝ}
    (htube : MachineInstance.UTube MachineInstance.r_LE_U c Z)
    (herr : (gateSelectorAtomsCoordN (MachineInstance.universalGateAtoms eta heta)).errSel
      < 1 / 2) :
    (1 / 2 - (gateSelectorAtomsCoordN (MachineInstance.universalGateAtoms eta heta)).errSel ≤
        LambdaN MachineInstance.universalViewSpecN
            (gateSelectorAtomsCoordN (MachineInstance.universalGateAtoms eta heta)) Z
            (MachineInstance.localViewU c) - 1 / 2) ∧
      (∀ v, v ≠ MachineInstance.localViewU c →
        LambdaN MachineInstance.universalViewSpecN
              (gateSelectorAtomsCoordN (MachineInstance.universalGateAtoms eta heta)) Z v
            - 1 / 2 ≤
          -(1 / 2 -
            (gateSelectorAtomsCoordN (MachineInstance.universalGateAtoms eta heta)).errSel)) := by
  have hsharp := MachineInstance.universalGateAtoms_sharpness eta heta htube
  have hinwork := MachineInstance.universalGateAtoms_inWorkingDomain eta heta htube
  have hsel1 := gate_view_selectorsN_SEL1_hypotheses MachineInstance.universalViewSpecN
    (gateSelectorAtomsCoordN (MachineInstance.universalGateAtoms eta heta)) Z
    (MachineInstance.localViewU c) hinwork hsharp
  have hmargin := coarse_margin_of_sel1 (MachineInstance.localViewU c)
    (LambdaN MachineInstance.universalViewSpecN
      (gateSelectorAtomsCoordN (MachineInstance.universalGateAtoms eta heta)) Z)
    herr hsel1.htrue (fun v hv => (hsel1.hoff v hv).2)
  exact ⟨hmargin.2.1, hmargin.2.2⟩

/-- The coarse-margin readout for the universal selector path: `Λ_N(v) - 1/2`. -/
def universalPval (eta : ℚ) (heta : 0 < eta) (v : MachineInstance.UniversalLocalView)
    (x : Fin MachineInstance.d_U → ℝ) : ℝ :=
  LambdaN MachineInstance.universalViewSpecN
    (gateSelectorAtomsCoordN (MachineInstance.universalGateAtoms eta heta)) x v - 1 / 2

/-- **M_U windowed margins.**  When the held config `u t` stays in the encoding tube of a
fixed config `c` throughout a window `[a,b)`, the universal coarse readout supplies the gate
margins `gate_mix_error` consumes: `Pval vstar ≥ αmar` and `Pval v ≤ -αmar` with
`αmar = 1/2 - errSel`, over the whole window.  (Lifts `universal_selector_margins_of_tube`
pointwise; `bgpSchedule.zActiveWindow = univ` so this covers the active window.) -/
theorem universal_selector_margins_on_window
    (eta : ℚ) (heta : 0 < eta) (c : MachineInstance.UConf)
    (u : ℝ → Fin MachineInstance.d_U → ℝ) {a b : ℝ}
    (herr : (gateSelectorAtomsCoordN (MachineInstance.universalGateAtoms eta heta)).errSel
      < 1 / 2)
    (htube : ∀ t ∈ Set.Ico a b, MachineInstance.UTube MachineInstance.r_LE_U c (u t)) :
    (∀ t ∈ Set.Ico a b,
        1 / 2 - (gateSelectorAtomsCoordN (MachineInstance.universalGateAtoms eta heta)).errSel
          ≤ universalPval eta heta (MachineInstance.localViewU c) (u t)) ∧
      (∀ v, v ≠ MachineInstance.localViewU c → ∀ t ∈ Set.Ico a b,
        universalPval eta heta v (u t) ≤
          -(1 / 2 -
            (gateSelectorAtomsCoordN (MachineInstance.universalGateAtoms eta heta)).errSel)) := by
  refine ⟨?_, ?_⟩
  · intro t ht
    exact (universal_selector_margins_of_tube eta heta (htube t ht) herr).1
  · intro v hv t ht
    exact (universal_selector_margins_of_tube eta heta (htube t ht) herr).2 v hv

/-- **Flag-read from the config tube.**  Since the encoding-tube radius `r_LE_U = 1/1000`
is below the flag-read tolerance `1/4`, whenever the live config `sol.z` stays in the
`r_LE_U`-tube of the orbit configs throughout the read windows, the halt-flag coordinate
is within `1/4` of its true encoded value — exactly the `hflag_read` hypothesis of
`bgp_unconditional_selector_assembled`.  This reduces the flag-read obligation to the
config tube closing (the simultaneous-induction core). -/
theorem selector_MU_flag_read_of_ztube
    {V : Type} [Fintype V] {p : DynGateParams} {sched : PhaseSchedule}
    {branch : V → BranchData MachineInstance.d_U MachineInstance.B_U}
    {chiResetF chiGateF kappaF gainF : ℝ → ℝ}
    {readoutP : V → (Fin MachineInstance.d_U → ℝ) → ℝ}
    (sol : SelectorDynSol MachineInstance.d_U MachineInstance.B_U V p sched
      branch chiResetF chiGateF kappaF gainF readoutP)
    (c : ℕ → MachineInstance.UConf)
    (hztube : ∀ j t, t ∈ sched.zActiveWindow j →
      MachineInstance.UTube MachineInstance.r_LE_U (c j) (sol.z t)) :
    ∀ j t, t ∈ sched.zActiveWindow j →
      |sol.z t MachineInstance.haltCoordU
        - MachineInstance.stackMachineEncodingU.enc (c j) MachineInstance.haltCoordU| ≤ 1 / 4 := by
  intro j t ht
  have h := hztube j t ht MachineInstance.haltCoordU
  have hrle : MachineInstance.r_LE_U ≤ (1 : ℝ) / 4 := by
    norm_num [MachineInstance.r_LE_U]
  calc |sol.z t MachineInstance.haltCoordU
          - MachineInstance.stackMachineEncodingU.enc (c j) MachineInstance.haltCoordU|
      = |sol.z t MachineInstance.haltCoordU
          - (MachineInstance.confEncU (c j) MachineInstance.haltCoordU : ℝ)| := by
        rfl
    _ ≤ MachineInstance.r_LE_U := h
    _ ≤ 1 / 4 := hrle

/-- **M_U config tube via the simultaneous induction (margins bootstrapping discharged).**
Instantiates `selector_simultaneous_induction` with the gate-window config tube as the
`Window` invariant and the universal coarse margins as `Branch`, concretely discharging the
`Window → Branch` step (the margins-from-tube bootstrapping link) via
`universal_selector_margins_on_window`.  The remaining per-step implications — the tube hold
(`Weighted → Window`), the per-cycle recurrence (`… → Recur`, via `cycle_step` + `gate_mix_error`
with these margins + gain growth), and the budget step (`Weighted ∧ Recur → Weighted′`) — are
taken as hypotheses (they are the solution's Reach/gain/budget facts, the analog of the
contract tracking premises).  Concludes the config `u` stays in the `r_LE_U` tube on every
gate window. -/
theorem selector_MU_config_tube
    {p : DynGateParams} {sched : PhaseSchedule}
    {chiResetF chiGateF kappaF gainF : ℝ → ℝ}
    {readoutP : MachineInstance.UniversalLocalView → (Fin MachineInstance.d_U → ℝ) → ℝ}
    (sol : SelectorDynSol MachineInstance.d_U MachineInstance.B_U
      MachineInstance.UniversalLocalView p sched MachineInstance.branchU
      chiResetF chiGateF kappaF gainF readoutP)
    (eta : ℚ) (heta : 0 < eta)
    (herr : (gateSelectorAtomsCoordN (MachineInstance.universalGateAtoms eta heta)).errSel
      < 1 / 2)
    (c : ℕ → MachineInstance.UConf) (aGate bGate : ℕ → ℝ)
    (Weighted Recur : ℕ → Prop)
    (hinit : Weighted 0)
    (hwin_of_weighted : ∀ j, Weighted j →
      ∀ t ∈ Set.Ico (aGate j) (bGate j),
        MachineInstance.UTube MachineInstance.r_LE_U (c j) (sol.u t))
    (hrecur_of_branch : ∀ j, Weighted j →
      (∀ t ∈ Set.Ico (aGate j) (bGate j),
        MachineInstance.UTube MachineInstance.r_LE_U (c j) (sol.u t)) →
      ((∀ t ∈ Set.Ico (aGate j) (bGate j),
          1 / 2 - (gateSelectorAtomsCoordN (MachineInstance.universalGateAtoms eta heta)).errSel
            ≤ universalPval eta heta (MachineInstance.localViewU (c j)) (sol.u t)) ∧
        (∀ v, v ≠ MachineInstance.localViewU (c j) → ∀ t ∈ Set.Ico (aGate j) (bGate j),
          universalPval eta heta v (sol.u t) ≤
            -(1 / 2 -
              (gateSelectorAtomsCoordN (MachineInstance.universalGateAtoms eta heta)).errSel))) →
      Recur j)
    (hweighted_step : ∀ j, Weighted j → Recur j → Weighted (j + 1)) :
    ∀ j, ∀ t ∈ Set.Ico (aGate j) (bGate j),
      MachineInstance.UTube MachineInstance.r_LE_U (c j) (sol.u t) := by
  intro j
  exact (selector_simultaneous_induction Weighted
    (fun j => ∀ t ∈ Set.Ico (aGate j) (bGate j),
      MachineInstance.UTube MachineInstance.r_LE_U (c j) (sol.u t))
    (fun j =>
      (∀ t ∈ Set.Ico (aGate j) (bGate j),
          1 / 2 - (gateSelectorAtomsCoordN (MachineInstance.universalGateAtoms eta heta)).errSel
            ≤ universalPval eta heta (MachineInstance.localViewU (c j)) (sol.u t)) ∧
        (∀ v, v ≠ MachineInstance.localViewU (c j) → ∀ t ∈ Set.Ico (aGate j) (bGate j),
          universalPval eta heta v (sol.u t) ≤
            -(1 / 2 -
              (gateSelectorAtomsCoordN (MachineInstance.universalGateAtoms eta heta)).errSel)))
    Recur hinit hwin_of_weighted
    (fun j hwin => universal_selector_margins_on_window eta heta (c j) sol.u herr hwin)
    hrecur_of_branch hweighted_step j).2.1

end Ripple.BoundedUniversality.BGP
