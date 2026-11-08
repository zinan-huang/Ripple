import Ripple.BoundedUniversality.BGP.SelectorTubeReach
import Ripple.BoundedUniversality.BGP.MachineInstance

/-!
Ripple.BoundedUniversality.BGP.SelectorWeightedUTube
-----------------------------
Wiring the abstract tube-Reach foundations (`SelectorTubeReach`) into the M_U-specific
`UTube` conclusion that `selector_MU_flag_read_of_tracking_concrete` carries as
`hwin_of_weighted`.

`selector_MU_hwin_of_weighted` discharges the `u`-tube-on-window fact directly from
`weighted_boundary_to_radius`: the M_U encoding `stackMachineEncodingU.enc (cfg j)` IS
`confEncU (cfg j)` (definitionally — `stackMachineEncodingU_enc_eq` is `rfl`), so the abstract
conclusion `∀ i, |u t i − enc i| ≤ r_LE_U` is exactly `UTube r_LE_U (cfg j) (u t)`.  The carried
facts shrink to the smaller, satisfiable ones: the hold drift `εhold` (`u`-Reach, from
`u_hold_window_bound`/`selector_uhold_decays`) and the radius-budget admissibility
`Wbound/k^dep + εhold ≤ r_LE_U`.
-/

noncomputable section

namespace Ripple.BoundedUniversality.BGP

open scoped BigOperators
open Set

variable {B : ℕ} {V : Type} [Fintype V] {p : DynGateParams}
  {branch : V → BranchData MachineInstance.d_U B}
  {chiReset chiGate kappa gain : ℝ → ℝ}
  {readoutP : V → (Fin MachineInstance.d_U → ℝ) → ℝ}

/-- **M_U `hwin_of_weighted` discharge (the `u`-tube on the gate window).**  From the weighted
boundary bound at the window start `2πj+π/6` (one cycle of `MUWeighted`), the hold drift over the
window, and the radius budget, the held config `sol.u t` stays in the `UTube` of the encoded
orbit value `cfg j` across the whole gate window `[2πj+π/6, 2πj+π/2)`.  This is exactly the carried
`hwin_of_weighted` of `selector_MU_flag_read_of_tracking_concrete`, discharged via
`weighted_boundary_to_radius` + the `rfl` encoding bridge
(`stackMachineEncodingU.enc (cfg j) = confEncU (cfg j)`). -/
theorem selector_MU_hwin_of_weighted
    (sol : SelectorDynSol MachineInstance.d_U B V p selectorSchedule branch
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
  exact weighted_boundary_to_radius sol
    (MachineInstance.stackMachineEncodingU.enc (cfg j)) hk1 (dep j) (Wbound j)
    (fun i => hhold i t htIcc) hradius hw

end Ripple.BoundedUniversality.BGP
