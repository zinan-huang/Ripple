import Ripple.BoundedUniversality.BGP.SelectorFlagLatch
import Ripple.BoundedUniversality.BGP.SelectorEventualRegion

/-!
Ripple.BoundedUniversality.BGP.SelectorCorrectHaltEndToEnd
--------------------------------------
The end-to-end composition of the flag-coordinate route: from SATISFIABLE per-cycle premises (z starts
near the flag target, the mixture stays near it, the gate is nonneg, the per-cycle radius `ρ + δmix`
is `≤ 1/4`, the box, and the halting verdict) to the `EventualThresholdSimulation` region conclusion
`∃ T, ∀ t ≥ T, z[haltCoord] ∈ HaltRegion` — WITHOUT the §3.3-vacuous depth-budget.

Wires: `SelectorFlagLatch.flag_within_quarter_on_interval` (latch, gap E: flag within `1/4` on each
FULL cycle interval `[2πj+5π/6, 2π(j+1)+5π/6]`) + `SelectorFlagRegion.flag_target_eventually_one_of_halts`
(eventual constant flag verdict, from the control-only absorbing halt) + `SelectorEventualRegion`
(tiling to `∀ t ≥ T`) + the box region lemma.  Every premise is satisfiable; no divergent budget.
-/

noncomputable section

namespace Ripple.BoundedUniversality.BGP

open Set MachineInstance UniversalMachine

/-- **`correct_halt` end-to-end.**  For a halting input, the flag coordinate is eventually in
`HaltRegion` (`3/4 ≤ z[haltCoord] ≤ 1`), assembled from the latch (per full cycle interval) + the
eventually-`1` flag target + box.  All carried premises are satisfiable. -/
theorem selector_correct_halt_endtoend
    {V : Type} [Fintype V]
    {branch : V → BranchData MachineInstance.d_U MachineInstance.B_U}
    {Pv : V → (Fin MachineInstance.d_U → ℝ) → ℝ} {pp : DynGateParams}
    {chiResetF chiGateF kappaF gainF : ℝ → ℝ}
    (sol : SelectorDynSol MachineInstance.d_U MachineInstance.B_U V pp selectorSchedule branch
      chiResetF chiGateF kappaF gainF Pv)
    (w : ℕ) (hw : M_U.haltsOn w)
    (cfg : ℕ → MachineInstance.UConf) (hcfg : ∀ j, cfg j = M_U.step^[j] (M_U.init w))
    (ρ δmix : ℕ → ℝ)
    (hdom : ∀ (j : ℕ), ∀ t ∈ Icc (2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6)
        (2 * Real.pi * ((j : ℝ) + 1) + 5 * Real.pi / 6), t ∈ selectorSchedule.domain)
    (hg_cont : Continuous (fun t => pp.A * sol.α t * bGateZ pp.L (sol.μ t) t))
    (hg0 : ∀ (j : ℕ), ∀ t ∈ Icc (2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6)
        (2 * Real.pi * ((j : ℝ) + 1) + 5 * Real.pi / 6),
      0 ≤ pp.A * sol.α t * bGateZ pp.L (sol.μ t) t)
    (hmix : ∀ (j : ℕ), ∀ t ∈ Icc (2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6)
        (2 * Real.pi * ((j : ℝ) + 1) + 5 * Real.pi / 6),
      |selectorMixTarget branch sol.u sol.lam t MachineInstance.haltCoordU
        - MachineInstance.stackMachineEncodingU.enc (cfg (j + 1)) MachineInstance.haltCoordU| ≤ δmix j)
    (hstart : ∀ (j : ℕ), |sol.z (2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6) MachineInstance.haltCoordU
        - MachineInstance.stackMachineEncodingU.enc (cfg (j + 1)) MachineInstance.haltCoordU| ≤ ρ j)
    (hsmall : ∀ j, ρ j + δmix j ≤ 1 / 4)
    (hbox : ∀ t, sol.z t MachineInstance.haltCoordU ≤ 1) :
    ∃ T : ℝ, ∀ t ≥ T,
      3 / 4 ≤ sol.z t MachineInstance.haltCoordU ∧ sol.z t MachineInstance.haltCoordU ≤ 1 := by
  obtain ⟨N, hN⟩ := flag_target_eventually_one_of_halts hw
  apply eventual_region_of_tiled (N := N)
  intro j hjN t ht
  have hab : 2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6
      ≤ 2 * Real.pi * ((j : ℝ) + 1) + 5 * Real.pi / 6 := by
    have := Real.pi_pos; nlinarith
  have hlatch := flag_within_quarter_on_interval sol MachineInstance.haltCoordU
    hab (hdom j) hg_cont (hg0 j) (hmix j) (hstart j) (hsmall j) t ht
  have hone : MachineInstance.stackMachineEncodingU.enc (cfg (j + 1)) MachineInstance.haltCoordU
      = (1 : ℝ) := by rw [hcfg (j + 1)]; exact hN j hjN
  rw [hone] at hlatch
  exact mem_haltRegion_of_flag_one hlatch (hbox t)

/-- **`correct_nonhalt` end-to-end.**  For a non-halting input, the flag coordinate is eventually in
`NonhaltRegion` (`0 ≤ z[haltCoord] ≤ 1/4`), assembled from the latch (per full cycle interval) + the
constantly-`0` flag target + box.  All carried premises are satisfiable. -/
theorem selector_correct_nonhalt_endtoend
    {V : Type} [Fintype V]
    {branch : V → BranchData MachineInstance.d_U MachineInstance.B_U}
    {Pv : V → (Fin MachineInstance.d_U → ℝ) → ℝ} {pp : DynGateParams}
    {chiResetF chiGateF kappaF gainF : ℝ → ℝ}
    (sol : SelectorDynSol MachineInstance.d_U MachineInstance.B_U V pp selectorSchedule branch
      chiResetF chiGateF kappaF gainF Pv)
    (w : ℕ) (hw : ¬ M_U.haltsOn w)
    (cfg : ℕ → MachineInstance.UConf) (hcfg : ∀ j, cfg j = M_U.step^[j] (M_U.init w))
    (ρ δmix : ℕ → ℝ)
    (hdom : ∀ (j : ℕ), ∀ t ∈ Icc (2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6)
        (2 * Real.pi * ((j : ℝ) + 1) + 5 * Real.pi / 6), t ∈ selectorSchedule.domain)
    (hg_cont : Continuous (fun t => pp.A * sol.α t * bGateZ pp.L (sol.μ t) t))
    (hg0 : ∀ (j : ℕ), ∀ t ∈ Icc (2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6)
        (2 * Real.pi * ((j : ℝ) + 1) + 5 * Real.pi / 6),
      0 ≤ pp.A * sol.α t * bGateZ pp.L (sol.μ t) t)
    (hmix : ∀ (j : ℕ), ∀ t ∈ Icc (2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6)
        (2 * Real.pi * ((j : ℝ) + 1) + 5 * Real.pi / 6),
      |selectorMixTarget branch sol.u sol.lam t MachineInstance.haltCoordU
        - MachineInstance.stackMachineEncodingU.enc (cfg (j + 1)) MachineInstance.haltCoordU| ≤ δmix j)
    (hstart : ∀ (j : ℕ), |sol.z (2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6) MachineInstance.haltCoordU
        - MachineInstance.stackMachineEncodingU.enc (cfg (j + 1)) MachineInstance.haltCoordU| ≤ ρ j)
    (hsmall : ∀ j, ρ j + δmix j ≤ 1 / 4)
    (hbox : ∀ t, 0 ≤ sol.z t MachineInstance.haltCoordU) :
    ∃ T : ℝ, ∀ t ≥ T,
      0 ≤ sol.z t MachineInstance.haltCoordU ∧ sol.z t MachineInstance.haltCoordU ≤ 1 / 4 := by
  apply eventual_region_of_tiled (N := 0)
  intro j _hjN t ht
  have hab : 2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6
      ≤ 2 * Real.pi * ((j : ℝ) + 1) + 5 * Real.pi / 6 := by
    have := Real.pi_pos; nlinarith
  have hlatch := flag_within_quarter_on_interval sol MachineInstance.haltCoordU
    hab (hdom j) hg_cont (hg0 j) (hmix j) (hstart j) (hsmall j) t ht
  have hzero : MachineInstance.stackMachineEncodingU.enc (cfg (j + 1)) MachineInstance.haltCoordU
      = (0 : ℝ) := by rw [hcfg (j + 1)]; exact flag_target_zero_of_not_halts hw j
  rw [hzero] at hlatch
  exact mem_nonhaltRegion_of_flag_zero hlatch (hbox t)

end Ripple.BoundedUniversality.BGP
