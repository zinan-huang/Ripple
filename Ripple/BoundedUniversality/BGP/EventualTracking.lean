import Ripple.BoundedUniversality.BGP.MUReplicatorSettledConstructionShifted

/-!
Ripple.BoundedUniversality.BGP.EventualTracking
----------------------------
Tail-only interfaces for the eventual-tracking route.

The current shifted late-start package asks for several estimates at every
cycle.  The final threshold readout only consumes those estimates after a
finite cycle threshold.  This file exposes that weaker interface explicitly, so
an eventual tracking producer can be wired to the headline without manufacturing
false small-cycle tubes.
-/

noncomputable section

namespace Ripple.BoundedUniversality.BGP

open Filter Set MachineInstance UniversalMachine
open scoped Topology

/-- Diagonal late-start facts needed only after cycle `N`.

The radius sequences are still global sequences because the final smallness
argument is expressed as convergence to zero, but the pointwise estimates are
only required on the tail. -/
structure EventualLateStartHaltFactsAt
    {p : DynGateParams} {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamilyP p eta heta Mcy κ₀ g₀)
    (w : ℕ) where
  cfg : ℕ → UConf
  hcfg : ∀ j, cfg j = M_U.step^[j] (M_U.init w)
  N : ℕ
  Bz_read : ℕ → ℝ
  hz_read_start : ∀ j, N ≤ j →
    |(sol w).z (selectorMUInterReadStart j) haltCoordU -
      stackMachineEncodingU.enc (cfg (j + 1)) haltCoordU| ≤ Bz_read j
  hBz_read_tendsto : Tendsto Bz_read atTop (𝓝 0)
  hBz_read_nonneg : ∀ j, 0 ≤ Bz_read j
  δnext : ℕ → ℝ
  hδnext : Tendsto δnext atTop (𝓝 0)
  hδnext_nonneg : ∀ j, 0 ≤ δnext j
  hoff : ∀ j, N ≤ j → selectorMUHaltEncConst cfg j → ∀ t ∈
      Icc (selectorMUInterReadStart j) (selectorMUNextWriteStart j),
    |(sol w).z t haltCoordU - (sol w).z (selectorMUInterReadStart j) haltCoordU| ≤
      selectorReplicatorHoldEnvelope j
  hnextWrite : ∀ j, N ≤ j → ∀ t ∈ Icc (selectorMUNextWriteStart j)
      (selectorMUNextRead j),
    |(sol w).z t haltCoordU - stackMachineEncodingU.enc (cfg (j + 2)) haltCoordU| ≤
      δnext j

namespace EventualLateStartHaltFactsAt

/-- All-cycle diagonal late-start facts are a special case of the tail-only
eventual interface, with threshold `0`. -/
def ofLateStart
    {p : DynGateParams} {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamilyP p eta heta Mcy κ₀ g₀} {w : ℕ}
    (late : MUReplicatorLateStartHaltFactsAt sol w) :
    EventualLateStartHaltFactsAt sol w where
  cfg := late.cfg
  hcfg := late.hcfg
  N := 0
  Bz_read := late.Bz_read
  hz_read_start := by
    intro j _hj
    exact late.hz_read_start j
  hBz_read_tendsto := late.hBz_read_tendsto
  hBz_read_nonneg := late.hBz_read_nonneg
  δnext := late.δnext
  hδnext := late.hδnext
  hδnext_nonneg := late.hδnext_nonneg
  hoff := by
    intro j _hj henc t ht
    exact late.hoff j henc t ht
  hnextWrite := by
    intro j _hj t ht
    exact late.hnextWrite j t ht

theorem selfHold_nonneg_P
    {p : DynGateParams}
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamilyP p eta heta Mcy κ₀ g₀} {w : ℕ}
    (late : EventualLateStartHaltFactsAt sol w) :
    ∀ j, 0 ≤ selectorMUSelfHoldDelta late.δnext late.Bz_read j := by
  intro j
  have henv : 0 ≤ selectorReplicatorHoldEnvelope j := by
    exact selectorReplicatorHoldEnvelope_nonneg j
  simp [selectorMUSelfHoldDelta]
  linarith [henv, late.hδnext_nonneg j, late.hBz_read_nonneg j]

theorem selfHold_nonneg
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀} {w : ℕ}
    (late : EventualLateStartHaltFactsAt sol w) :
    ∀ j, 0 ≤ selectorMUSelfHoldDelta late.δnext late.Bz_read j := by
  exact selfHold_nonneg_P late

/-- Tail-only late-start facts imply eventual halt-region convergence. -/
theorem correct_halt_z_P
    {p : DynGateParams}
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamilyP p eta heta Mcy κ₀ g₀} {w : ℕ}
    (late : EventualLateStartHaltFactsAt sol w)
    (hbox_hi : ∀ t, 0 ≤ t → (sol w).z t haltCoordU ≤ 1)
    (hw : M_U.haltsOn w) :
    ∃ T : ℝ, ∀ t ≥ T, 3 / 4 ≤ (sol w).z t haltCoordU ∧
      (sol w).z t haltCoordU ≤ 1 := by
  obtain ⟨Nh, hconst⟩ :=
    halt_flag_target_const_cfg_succ_succ_of_halts hw late.cfg late.hcfg
  let Ntail : ℕ := max late.N Nh
  have hN_late : late.N ≤ Ntail := by
    dsimp [Ntail]
    exact le_max_left _ _
  have hN_halt : Nh ≤ Ntail := by
    dsimp [Ntail]
    exact le_max_right _ _
  have hhold_tail :
      ∀ j, Ntail ≤ j → ∀ t ∈ Icc (selectorMUInterReadStart j)
          (selectorMUNextRead j),
        |(sol w).z t haltCoordU - (sol w).z (selectorMUInterReadStart j) haltCoordU| ≤
          selectorMUSelfHoldDelta late.δnext late.Bz_read j := by
    exact
      z_self_hold_on_inter_read_P
        (sol w) late.cfg late.δnext late.Bz_read Ntail
        (fun j _hj => late.hδnext_nonneg j)
        (fun j _hj => late.hBz_read_nonneg j)
        (fun j hj => hconst j (le_trans hN_halt hj))
        (fun j hj => late.hz_read_start j (le_trans hN_late hj))
        (fun j hj henc => late.hoff j (le_trans hN_late hj) henc)
        (fun j hj => late.hnextWrite j (le_trans hN_late hj))
  have hδhold :
      Tendsto (selectorMUSelfHoldDelta late.δnext late.Bz_read) atTop (𝓝 0) :=
    selectorMUSelfHoldDelta_tendsto_zero late.hδnext late.hBz_read_tendsto
  obtain ⟨Nsmall, hsmall⟩ :=
    eventual_hsmall_of_tendsto late.hBz_read_tendsto hδhold
      late.hBz_read_nonneg (selfHold_nonneg_P late)
  let Nfinal : ℕ := max Ntail Nsmall
  have hNfinal_tail : Ntail ≤ Nfinal := by
    dsimp [Nfinal]
    exact le_max_left _ _
  have hNfinal_small : Nsmall ≤ Nfinal := by
    dsimp [Nfinal]
    exact le_max_right _ _
  refine
    selector_correct_halt_endtoend_hold_repl_eventual
      (sol w) w hw late.cfg late.hcfg late.Bz_read
      (selectorMUSelfHoldDelta late.δnext late.Bz_read) Nfinal ?_ ?_ ?_ hbox_hi
  · intro j hj
    exact late.hz_read_start j (le_trans hN_late (le_trans hNfinal_tail hj))
  · intro j hj t ht
    exact hhold_tail j (le_trans hNfinal_tail hj) t (by
      simpa [selectorMUInterReadStart, selectorMUNextRead, selectorMUWriteReadTime] using ht)
  · intro j hj
    exact hsmall j (le_trans hNfinal_small hj)

theorem correct_halt_z
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀} {w : ℕ}
    (late : EventualLateStartHaltFactsAt sol w)
    (hbox_hi : ∀ t, 0 ≤ t → (sol w).z t haltCoordU ≤ 1)
    (hw : M_U.haltsOn w) :
    ∃ T : ℝ, ∀ t ≥ T, 3 / 4 ≤ (sol w).z t haltCoordU ∧
      (sol w).z t haltCoordU ≤ 1 := by
  exact correct_halt_z_P late hbox_hi hw

/-- Tail-only late-start facts imply eventual nonhalt-region convergence. -/
theorem correct_nonhalt_z_P
    {p : DynGateParams}
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamilyP p eta heta Mcy κ₀ g₀} {w : ℕ}
    (late : EventualLateStartHaltFactsAt sol w)
    (hbox_lo : ∀ t, 0 ≤ t → 0 ≤ (sol w).z t haltCoordU)
    (hw : ¬ M_U.haltsOn w) :
    ∃ T : ℝ, ∀ t ≥ T, 0 ≤ (sol w).z t haltCoordU ∧
      (sol w).z t haltCoordU ≤ 1 / 4 := by
  have hconst := halt_flag_target_const_cfg_succ_succ_of_nonhalts hw late.cfg late.hcfg
  have hhold_tail :
      ∀ j, late.N ≤ j → ∀ t ∈ Icc (selectorMUInterReadStart j)
          (selectorMUNextRead j),
        |(sol w).z t haltCoordU - (sol w).z (selectorMUInterReadStart j) haltCoordU| ≤
          selectorMUSelfHoldDelta late.δnext late.Bz_read j := by
    exact
      z_self_hold_on_inter_read_P
        (sol w) late.cfg late.δnext late.Bz_read late.N
        (fun j _hj => late.hδnext_nonneg j)
        (fun j _hj => late.hBz_read_nonneg j)
        (fun j _hj => hconst j)
        (fun j hj => late.hz_read_start j hj)
        (fun j hj henc => late.hoff j hj henc)
        (fun j hj => late.hnextWrite j hj)
  have hδhold :
      Tendsto (selectorMUSelfHoldDelta late.δnext late.Bz_read) atTop (𝓝 0) :=
    selectorMUSelfHoldDelta_tendsto_zero late.hδnext late.hBz_read_tendsto
  obtain ⟨Nsmall, hsmall⟩ :=
    eventual_hsmall_of_tendsto late.hBz_read_tendsto hδhold
      late.hBz_read_nonneg (selfHold_nonneg_P late)
  let Nfinal : ℕ := max late.N Nsmall
  have hNfinal_tail : late.N ≤ Nfinal := by
    dsimp [Nfinal]
    exact le_max_left _ _
  have hNfinal_small : Nsmall ≤ Nfinal := by
    dsimp [Nfinal]
    exact le_max_right _ _
  refine
    selector_correct_nonhalt_endtoend_hold_repl_eventual
      (sol w) w hw late.cfg late.hcfg late.Bz_read
      (selectorMUSelfHoldDelta late.δnext late.Bz_read) Nfinal ?_ ?_ ?_ hbox_lo
  · intro j hj
    exact late.hz_read_start j (le_trans hNfinal_tail hj)
  · intro j hj t ht
    exact hhold_tail j (le_trans hNfinal_tail hj) t (by
      simpa [selectorMUInterReadStart, selectorMUNextRead, selectorMUWriteReadTime] using ht)
  · intro j hj
    exact hsmall j (le_trans hNfinal_small hj)

theorem correct_nonhalt_z
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀} {w : ℕ}
    (late : EventualLateStartHaltFactsAt sol w)
    (hbox_lo : ∀ t, 0 ≤ t → 0 ≤ (sol w).z t haltCoordU)
    (hw : ¬ M_U.haltsOn w) :
    ∃ T : ℝ, ∀ t ≥ T, 0 ≤ (sol w).z t haltCoordU ∧
      (sol w).z t haltCoordU ≤ 1 / 4 := by
  exact correct_nonhalt_z_P late hbox_lo hw

section PGeneralizationSentinels

variable {p : DynGateParams}

example : @selfHold_nonneg_P p = @selfHold_nonneg_P p := by
  rfl

example : @correct_halt_z_P p = @correct_halt_z_P p := by
  rfl

example : @correct_nonhalt_z_P p = @correct_nonhalt_z_P p := by
  rfl

end PGeneralizationSentinels

end EventualLateStartHaltFactsAt

end Ripple.BoundedUniversality.BGP
