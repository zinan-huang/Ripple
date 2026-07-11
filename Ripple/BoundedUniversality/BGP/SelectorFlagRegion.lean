import Ripple.BoundedUniversality.BGP.HaltAbsorbing
import Ripple.BoundedUniversality.BGP.SelectorZRead

/-!
Ripple.BoundedUniversality.BGP.SelectorFlagRegion
-----------------------------
Avenue (c) of DOCTRINE-allcycle: the FLAG-coordinate route to the eventual-threshold regions.

The readout regions constrain ONLY the halt-flag coordinate (`HaltRegion = {y | 3/4 ≤ y[h] ≤ 1}`,
`NonhaltRegion = {y | 0 ≤ y[h] ≤ 1/4}`).  The halt is control-only (`finHalted = fc.1.isNone`) and
absorbing, so the encoded flag target `enc(M_U.step^[j+1] w)[haltCoord]` is EVENTUALLY CONSTANT
(`= 1` after halting, `= 0` throughout a nonhalting run) — proven here from `HaltAbsorbing`.  Combined
with the landed per-cycle flag read (`selector_MU_flag_read_all_next`: `|z[haltCoord] − target| ≤ 1/4`
on read windows) and the carried box `0 ≤ z[haltCoord] ≤ 1` (`hflag_dom`), the flag coordinate lands
in the correct region on every read window past a finite burn-in — WITHOUT the vacuous full-config
depth-budget.  The remaining gap is the between-window latch (`∀ t ≥ T`, gap E).
-/

namespace Ripple.BoundedUniversality.BGP

open MachineInstance UniversalMachine

/-- **Eventual flag proximity to a constant verdict, on read windows.**  From the per-cycle flag read
and eventual constancy of the encoded flag target (`= b`), the flag coordinate is eventually within
`1/4` of `b` on every read window. -/
theorem flag_eventually_near_const_on_windows
    {V : Type} [Fintype V]
    {branch : V → BranchData MachineInstance.d_U MachineInstance.B_U}
    {Pv : V → (Fin MachineInstance.d_U → ℝ) → ℝ} {p : DynGateParams}
    {chiResetF chiGateF kappaF gainF : ℝ → ℝ}
    (sol : SelectorDynSol MachineInstance.d_U MachineInstance.B_U V p selectorSchedule branch
      chiResetF chiGateF kappaF gainF Pv)
    (cfg : ℕ → MachineInstance.UConf) (b : ℝ)
    (hflag : ∀ j, ∀ t ∈ selectorReadWindow j,
      |sol.z t MachineInstance.haltCoordU
        - MachineInstance.stackMachineEncodingU.enc (cfg (j + 1)) MachineInstance.haltCoordU| ≤ 1 / 4)
    (hconst : ∃ N, ∀ j ≥ N,
      (MachineInstance.stackMachineEncodingU.enc (cfg (j + 1)) MachineInstance.haltCoordU : ℝ) = b) :
    ∃ N, ∀ j ≥ N, ∀ t ∈ selectorReadWindow j,
      |sol.z t MachineInstance.haltCoordU - b| ≤ 1 / 4 := by
  obtain ⟨N, hN⟩ := hconst
  refine ⟨N, fun j hj t ht => ?_⟩
  rw [← hN j hj]
  exact hflag j t ht

/-- **Halt region from flag proximity to `1` + box.**  `|z − 1| ≤ 1/4` and `z ≤ 1` ⟹ `z ∈ [3/4, 1]`. -/
theorem mem_haltRegion_of_flag_one {z : ℝ} (hz : |z - 1| ≤ 1 / 4) (hbox : z ≤ 1) :
    3 / 4 ≤ z ∧ z ≤ 1 := by
  rw [abs_le] at hz; exact ⟨by linarith [hz.1], hbox⟩

/-- **Nonhalt region from flag proximity to `0` + box.**  `|z| ≤ 1/4` and `0 ≤ z` ⟹ `z ∈ [0, 1/4]`. -/
theorem mem_nonhaltRegion_of_flag_zero {z : ℝ} (hz : |z - 0| ≤ 1 / 4) (hbox : 0 ≤ z) :
    0 ≤ z ∧ z ≤ 1 / 4 := by
  rw [abs_le] at hz; exact ⟨hbox, by linarith [hz.2]⟩

/-- **Flag target is eventually `1` on a halting run.**  From `HaltAbsorbing.halted_eventually_of_halts`
the halt test is `true` past the witness, so the encoded flag coordinate reads `1`. -/
theorem flag_target_eventually_one_of_halts {w : ℕ} (hw : M_U.haltsOn w) :
    ∃ N, ∀ j ≥ N,
      (MachineInstance.stackMachineEncodingU.enc (M_U.step^[j + 1] (M_U.init w))
        MachineInstance.haltCoordU : ℝ) = 1 := by
  obtain ⟨n, hn⟩ := hw
  refine ⟨n, fun j hj => ?_⟩
  have hk : M_U.halted (M_U.step^[j + 1] (M_U.init w)) = true :=
    M_U.halted_eventually_of_halts hn (j + 1) (by omega)
  rw [stackMachineEncodingU_enc_eq, confEncU_halt]
  have hfin : finHalted (M_U.step^[j + 1] (M_U.init w)) = true := hk
  unfold haltFlagU
  rw [if_pos (by rw [hfin])]
  norm_num

/-- **Flag target is `0` throughout a nonhalting run.**  From `HaltAbsorbing.halted_false_of_not_halts`
the halt test is always `false`, so the encoded flag coordinate reads `0`. -/
theorem flag_target_zero_of_not_halts {w : ℕ} (hw : ¬ M_U.haltsOn w) :
    ∀ j, (MachineInstance.stackMachineEncodingU.enc (M_U.step^[j + 1] (M_U.init w))
        MachineInstance.haltCoordU : ℝ) = 0 := by
  intro j
  have hk : M_U.halted (M_U.step^[j + 1] (M_U.init w)) = false :=
    M_U.halted_false_of_not_halts hw (j + 1)
  rw [stackMachineEncodingU_enc_eq, confEncU_halt]
  have hfin : finHalted (M_U.step^[j + 1] (M_U.init w)) = false := hk
  unfold haltFlagU
  rw [if_neg (by rw [hfin]; decide)]
  norm_num

end Ripple.BoundedUniversality.BGP
