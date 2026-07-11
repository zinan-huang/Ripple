import Ripple.BoundedUniversality.BGP.SelectorReplicatorHeadline

/-!
Ripple.BoundedUniversality.BGP.SelectorReplicatorEventual
--------------------------------------
Eventual-radius variants of the replicator hold endpoint.

The headline hold endpoint only needs per-cycle start/hold/smallness hypotheses
past a finite prefix, because `eventual_region_of_tiled` already skips all
cycles below its threshold.  This file exposes that threshold explicitly and
then extracts it from `ρ → 0` and `δhold → 0`.
-/

noncomputable section

namespace Ripple.BoundedUniversality.BGP

open Filter Set MachineInstance
open scoped Topology

/-- Hold-form halting endpoint with start/hold/smallness required only after
the carried cycle threshold `N`. -/
theorem selector_correct_halt_endtoend_hold_repl_eventual
    {V : Type} [Fintype V]
    {branch : V → BranchData MachineInstance.d_U MachineInstance.B_U}
    {Pv : V → (Fin MachineInstance.d_U → ℝ) → ℝ} {pp : DynGateParams}
    {chiResetF chiGateF kappaF gainF : ℝ → ℝ}
    (sol : SelectorReplicatorDynSol MachineInstance.d_U MachineInstance.B_U V pp
      selectorSchedule branch
      chiResetF chiGateF kappaF gainF Pv)
    (w : ℕ) (hw : M_U.haltsOn w)
    (cfg : ℕ → MachineInstance.UConf) (hcfg : ∀ j, cfg j = M_U.step^[j] (M_U.init w))
    (ρ δhold : ℕ → ℝ) (N : ℕ)
    (hstart : ∀ (j : ℕ), N ≤ j →
      |sol.z (2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6) MachineInstance.haltCoordU
        - MachineInstance.stackMachineEncodingU.enc (cfg (j + 1))
            MachineInstance.haltCoordU| ≤ ρ j)
    (hhold : ∀ (j : ℕ), N ≤ j → ∀ t ∈ Icc (2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6)
        (2 * Real.pi * ((j : ℝ) + 1) + 5 * Real.pi / 6),
      |sol.z t MachineInstance.haltCoordU
        - sol.z (2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6)
            MachineInstance.haltCoordU| ≤ δhold j)
    (hsmall : ∀ j, N ≤ j → ρ j + δhold j ≤ 1 / 4)
    (hbox : ∀ t, 0 ≤ t → sol.z t MachineInstance.haltCoordU ≤ 1) :
    ∃ T : ℝ, ∀ t ≥ T,
      3 / 4 ≤ sol.z t MachineInstance.haltCoordU ∧
        sol.z t MachineInstance.haltCoordU ≤ 1 := by
  obtain ⟨Nh, hNh⟩ := flag_target_eventually_one_of_halts hw
  apply eventual_region_of_tiled (N := max N Nh)
  intro j hjN t ht
  have hNj : N ≤ j := le_trans (le_max_left N Nh) hjN
  have hNhj : Nh ≤ j := le_trans (le_max_right N Nh) hjN
  have hlatch := flag_within_quarter_on_interval_hold_repl sol MachineInstance.haltCoordU
    (hstart j hNj) (hhold j hNj) (hsmall j hNj) t ht
  have hone : MachineInstance.stackMachineEncodingU.enc (cfg (j + 1)) MachineInstance.haltCoordU
      = (1 : ℝ) := by
    rw [hcfg (j + 1)]
    exact hNh j hNhj
  have ht0 : 0 ≤ t := by
    have hleft : 0 ≤ 2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6 := by positivity
    exact le_trans hleft ht.1
  rw [hone] at hlatch
  exact mem_haltRegion_of_flag_one hlatch (hbox t ht0)

/-- Hold-form nonhalting endpoint with start/hold/smallness required only after
the carried cycle threshold `N`. -/
theorem selector_correct_nonhalt_endtoend_hold_repl_eventual
    {V : Type} [Fintype V]
    {branch : V → BranchData MachineInstance.d_U MachineInstance.B_U}
    {Pv : V → (Fin MachineInstance.d_U → ℝ) → ℝ} {pp : DynGateParams}
    {chiResetF chiGateF kappaF gainF : ℝ → ℝ}
    (sol : SelectorReplicatorDynSol MachineInstance.d_U MachineInstance.B_U V pp
      selectorSchedule branch
      chiResetF chiGateF kappaF gainF Pv)
    (w : ℕ) (hw : ¬ M_U.haltsOn w)
    (cfg : ℕ → MachineInstance.UConf) (hcfg : ∀ j, cfg j = M_U.step^[j] (M_U.init w))
    (ρ δhold : ℕ → ℝ) (N : ℕ)
    (hstart : ∀ (j : ℕ), N ≤ j →
      |sol.z (2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6) MachineInstance.haltCoordU
        - MachineInstance.stackMachineEncodingU.enc (cfg (j + 1))
            MachineInstance.haltCoordU| ≤ ρ j)
    (hhold : ∀ (j : ℕ), N ≤ j → ∀ t ∈ Icc (2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6)
        (2 * Real.pi * ((j : ℝ) + 1) + 5 * Real.pi / 6),
      |sol.z t MachineInstance.haltCoordU
        - sol.z (2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6)
            MachineInstance.haltCoordU| ≤ δhold j)
    (hsmall : ∀ j, N ≤ j → ρ j + δhold j ≤ 1 / 4)
    (hbox : ∀ t, 0 ≤ t → 0 ≤ sol.z t MachineInstance.haltCoordU) :
    ∃ T : ℝ, ∀ t ≥ T,
      0 ≤ sol.z t MachineInstance.haltCoordU ∧
        sol.z t MachineInstance.haltCoordU ≤ 1 / 4 := by
  apply eventual_region_of_tiled (N := N)
  intro j hjN t ht
  have hlatch := flag_within_quarter_on_interval_hold_repl sol MachineInstance.haltCoordU
    (hstart j hjN) (hhold j hjN) (hsmall j hjN) t ht
  have hzero : MachineInstance.stackMachineEncodingU.enc (cfg (j + 1)) MachineInstance.haltCoordU
      = (0 : ℝ) := by
    rw [hcfg (j + 1)]
    exact flag_target_zero_of_not_halts hw j
  have ht0 : 0 ≤ t := by
    have hleft : 0 ≤ 2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6 := by positivity
    exact le_trans hleft ht.1
  rw [hzero] at hlatch
  exact mem_nonhaltRegion_of_flag_zero hlatch (hbox t ht0)

/-- If both carried radii tend to zero, then their sum is eventually below
`1/4`.  The nonnegativity hypotheses are kept in the interface used by the
headline corollaries. -/
theorem eventual_hsmall_of_tendsto {ρ δhold : ℕ → ℝ}
    (hρ : Tendsto ρ atTop (𝓝 0))
    (hδhold : Tendsto δhold atTop (𝓝 0))
    (hρ_nonneg : ∀ j, 0 ≤ ρ j)
    (hδhold_nonneg : ∀ j, 0 ≤ δhold j) :
    ∃ N : ℕ, ∀ j, N ≤ j → ρ j + δhold j ≤ 1 / 4 := by
  have hsum : Tendsto (fun j => ρ j + δhold j) atTop (𝓝 (0 : ℝ)) := by
    simpa using hρ.add hδhold
  have habs : Tendsto (fun j => |ρ j + δhold j|) atTop (𝓝 (0 : ℝ)) := by
    simpa using hsum.norm
  have hev : ∀ᶠ j : ℕ in atTop, |ρ j + δhold j| < 1 / 4 :=
    habs.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
  refine ⟨N, fun j hj => ?_⟩
  have hnonneg : 0 ≤ ρ j + δhold j := add_nonneg (hρ_nonneg j) (hδhold_nonneg j)
  have hlt := hN j hj
  rw [abs_of_nonneg hnonneg] at hlt
  exact le_of_lt hlt

/-- Hold-form halting endpoint whose only smallness input is
`ρ → 0` and `δhold → 0`. -/
theorem selector_correct_halt_endtoend_hold_repl_of_tendsto
    {V : Type} [Fintype V]
    {branch : V → BranchData MachineInstance.d_U MachineInstance.B_U}
    {Pv : V → (Fin MachineInstance.d_U → ℝ) → ℝ} {pp : DynGateParams}
    {chiResetF chiGateF kappaF gainF : ℝ → ℝ}
    (sol : SelectorReplicatorDynSol MachineInstance.d_U MachineInstance.B_U V pp
      selectorSchedule branch
      chiResetF chiGateF kappaF gainF Pv)
    (w : ℕ) (hw : M_U.haltsOn w)
    (cfg : ℕ → MachineInstance.UConf) (hcfg : ∀ j, cfg j = M_U.step^[j] (M_U.init w))
    (ρ δhold : ℕ → ℝ)
    (hstart : ∀ (j : ℕ),
      |sol.z (2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6) MachineInstance.haltCoordU
        - MachineInstance.stackMachineEncodingU.enc (cfg (j + 1))
            MachineInstance.haltCoordU| ≤ ρ j)
    (hhold : ∀ (j : ℕ), ∀ t ∈ Icc (2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6)
        (2 * Real.pi * ((j : ℝ) + 1) + 5 * Real.pi / 6),
      |sol.z t MachineInstance.haltCoordU
        - sol.z (2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6)
            MachineInstance.haltCoordU| ≤ δhold j)
    (hbox : ∀ t, 0 ≤ t → sol.z t MachineInstance.haltCoordU ≤ 1)
    (hρ : Tendsto ρ atTop (𝓝 0))
    (hδhold : Tendsto δhold atTop (𝓝 0))
    (hρ_nonneg : ∀ j, 0 ≤ ρ j)
    (hδhold_nonneg : ∀ j, 0 ≤ δhold j) :
    ∃ T : ℝ, ∀ t ≥ T,
      3 / 4 ≤ sol.z t MachineInstance.haltCoordU ∧
        sol.z t MachineInstance.haltCoordU ≤ 1 := by
  obtain ⟨N, hsmall⟩ :=
    eventual_hsmall_of_tendsto hρ hδhold hρ_nonneg hδhold_nonneg
  exact selector_correct_halt_endtoend_hold_repl_eventual sol w hw cfg hcfg ρ δhold N
    (fun j _hj => hstart j)
    (fun j _hj => hhold j)
    hsmall hbox

/-- Hold-form nonhalting endpoint whose only smallness input is
`ρ → 0` and `δhold → 0`. -/
theorem selector_correct_nonhalt_endtoend_hold_repl_of_tendsto
    {V : Type} [Fintype V]
    {branch : V → BranchData MachineInstance.d_U MachineInstance.B_U}
    {Pv : V → (Fin MachineInstance.d_U → ℝ) → ℝ} {pp : DynGateParams}
    {chiResetF chiGateF kappaF gainF : ℝ → ℝ}
    (sol : SelectorReplicatorDynSol MachineInstance.d_U MachineInstance.B_U V pp
      selectorSchedule branch
      chiResetF chiGateF kappaF gainF Pv)
    (w : ℕ) (hw : ¬ M_U.haltsOn w)
    (cfg : ℕ → MachineInstance.UConf) (hcfg : ∀ j, cfg j = M_U.step^[j] (M_U.init w))
    (ρ δhold : ℕ → ℝ)
    (hstart : ∀ (j : ℕ),
      |sol.z (2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6) MachineInstance.haltCoordU
        - MachineInstance.stackMachineEncodingU.enc (cfg (j + 1))
            MachineInstance.haltCoordU| ≤ ρ j)
    (hhold : ∀ (j : ℕ), ∀ t ∈ Icc (2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6)
        (2 * Real.pi * ((j : ℝ) + 1) + 5 * Real.pi / 6),
      |sol.z t MachineInstance.haltCoordU
        - sol.z (2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6)
            MachineInstance.haltCoordU| ≤ δhold j)
    (hbox : ∀ t, 0 ≤ t → 0 ≤ sol.z t MachineInstance.haltCoordU)
    (hρ : Tendsto ρ atTop (𝓝 0))
    (hδhold : Tendsto δhold atTop (𝓝 0))
    (hρ_nonneg : ∀ j, 0 ≤ ρ j)
    (hδhold_nonneg : ∀ j, 0 ≤ δhold j) :
    ∃ T : ℝ, ∀ t ≥ T,
      0 ≤ sol.z t MachineInstance.haltCoordU ∧
        sol.z t MachineInstance.haltCoordU ≤ 1 / 4 := by
  obtain ⟨N, hsmall⟩ :=
    eventual_hsmall_of_tendsto hρ hδhold hρ_nonneg hδhold_nonneg
  exact selector_correct_nonhalt_endtoend_hold_repl_eventual sol w hw cfg hcfg ρ δhold N
    (fun j _hj => hstart j)
    (fun j _hj => hhold j)
    hsmall hbox

#print axioms selector_correct_halt_endtoend_hold_repl_eventual
#print axioms selector_correct_nonhalt_endtoend_hold_repl_eventual
#print axioms eventual_hsmall_of_tendsto
#print axioms selector_correct_halt_endtoend_hold_repl_of_tendsto
#print axioms selector_correct_nonhalt_endtoend_hold_repl_of_tendsto

end Ripple.BoundedUniversality.BGP
