import Ripple.BoundedUniversality.BGP.HaltAbsorbing
import Ripple.BoundedUniversality.BGP.SelectorReplicatorEventual
import Ripple.BoundedUniversality.BGP.SelectorReplicatorRadiiDecay
import Ripple.BoundedUniversality.BGP.SelectorReplicatorSettledZ
import Ripple.BoundedUniversality.BGP.BGPParams38

/-!
Ripple.BoundedUniversality.BGP.SelectorReplicatorSelfHold
--------------------------------------
Self-hold wiring for the restructured halt headline.

The consumer is `selector_correct_halt_endtoend_hold_repl`, whose hold premise is
pure `z` self-drift:

  `|z(t)[halt] - z(readStart j)[halt]| ≤ δhold j`.

This file does not introduce a full inter-read moving-target stability
hypothesis.  The split is:

* the offphase part carries a direct self-drift envelope;
* the next settled write is compared to the same encoded halt target, using
  absorbing-halt constancy `enc(j+2)[halt] = enc(j+1)[halt]`.
-/

noncomputable section

namespace Ripple.BoundedUniversality.BGP

open Set MachineInstance
open Filter
open scoped Topology

/-- Inter-read left endpoint: `2πj + 5π/6`. -/
def selectorMUInterReadStart (j : ℕ) : ℝ :=
  selectorMUWriteReadTime j

/-- Start of the next settled write window: `2π(j+1) + π/2`. -/
def selectorMUNextWriteStart (j : ℕ) : ℝ :=
  selectorMUWriteHoldTime (j + 1)

/-- Inter-read right endpoint: `2π(j+1) + 5π/6`. -/
def selectorMUNextRead (j : ℕ) : ℝ :=
  selectorMUWriteReadTime (j + 1)

theorem selectorMUSuccCast_pos (j : ℕ) : 0 < (((j + 1 : ℕ) : ℝ)) := by
  exact Nat.cast_pos.mpr (Nat.succ_pos j)

theorem selectorMUInterReadStart_le_nextWriteStart (j : ℕ) :
    selectorMUInterReadStart j ≤ selectorMUNextWriteStart j := by
  unfold selectorMUInterReadStart selectorMUNextWriteStart
  unfold selectorMUWriteReadTime selectorMUWriteHoldTime
  push_cast
  nlinarith [Real.pi_pos]

theorem selectorMUNextWriteStart_le_nextRead (j : ℕ) :
    selectorMUNextWriteStart j ≤ selectorMUNextRead j := by
  unfold selectorMUNextWriteStart selectorMUNextRead
  exact selectorMUWriteHold_le_read (j + 1)

theorem selectorMUInterReadStart_le_nextRead (j : ℕ) :
    selectorMUInterReadStart j ≤ selectorMUNextRead j :=
  le_trans (selectorMUInterReadStart_le_nextWriteStart j)
    (selectorMUNextWriteStart_le_nextRead j)

/-- The halt-coordinate encoding is constant across the next write target. -/
def selectorMUHaltEncConst (cfg : ℕ → UConf) (j : ℕ) : Prop :=
  stackMachineEncodingU.enc (cfg (j + 2)) haltCoordU =
    stackMachineEncodingU.enc (cfg (j + 1)) haltCoordU

/-- Family version of `selectorMUHaltEncConst`. -/
def selectorMUHaltEncConstW (cfg : ℕ → ℕ → UConf) (w j : ℕ) : Prop :=
  selectorMUHaltEncConst (cfg w) j

/-- Absorbing halt makes the encoded halt target constant between consecutive
post-halt read indices. -/
theorem halt_flag_target_const_succ_succ_of_halts {w : ℕ} (hw : M_U.haltsOn w) :
    ∃ N : ℕ, ∀ j ≥ N,
      selectorMUHaltEncConst (fun j => M_U.step^[j] (M_U.init w)) j := by
  obtain ⟨n, hn⟩ := hw
  refine ⟨n, fun j hj => ?_⟩
  have h2 :
      M_U.step^[j + 2] (M_U.init w) = M_U.step^[n] (M_U.init w) :=
    M_U.config_const_of_halted_at hn (j + 2) (by omega)
  have h1 :
      M_U.step^[j + 1] (M_U.init w) = M_U.step^[n] (M_U.init w) :=
    M_U.config_const_of_halted_at hn (j + 1) (by omega)
  unfold selectorMUHaltEncConst
  simp only
  rw [h2, h1]

/-- Same constancy through a carried configuration trace `cfg`. -/
theorem halt_flag_target_const_cfg_succ_succ_of_halts
    {w : ℕ} (hw : M_U.haltsOn w)
    (cfg : ℕ → UConf) (hcfg : ∀ j, cfg j = M_U.step^[j] (M_U.init w)) :
    ∃ N : ℕ, ∀ j ≥ N,
      selectorMUHaltEncConst cfg j := by
  obtain ⟨N, hN⟩ := halt_flag_target_const_succ_succ_of_halts (w := w) hw
  refine ⟨N, fun j hj => ?_⟩
  unfold selectorMUHaltEncConst
  rw [hcfg (j + 2), hcfg (j + 1)]
  simpa [selectorMUHaltEncConst] using hN j hj

/-- The pure self-hold radius used by the inter-read split:
offphase leakage + next settled-write error + settled start radius. -/
def selectorMUSelfHoldDelta (δnextWrite δwSettled : ℕ → ℝ) (j : ℕ) : ℝ :=
  selectorReplicatorHoldEnvelope j + δnextWrite j + δwSettled j

theorem selectorMUSelfHoldDelta_tendsto_zero
    {δnextWrite δwSettled : ℕ → ℝ}
    (hnext : Tendsto δnextWrite atTop (𝓝 0))
    (hsettled : Tendsto δwSettled atTop (𝓝 0)) :
    Tendsto (selectorMUSelfHoldDelta δnextWrite δwSettled) atTop (𝓝 0) := by
  simpa [selectorMUSelfHoldDelta] using
    (selectorReplicatorHoldEnvelope_tendsto_zero.add hnext).add hsettled

/-- Inter-read pure `z` self-hold, post halt.

The assumptions are deliberately not a moving-target-over-the-tile premise.
`hnextWrite` is the settled next-write estimate against `enc(cfg (j+2))`,
and `hconst` rewrites that target to `enc(cfg (j+1))` once halt is absorbing.
-/
theorem z_self_hold_on_inter_read_P
    {p : DynGateParams}
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : SelectorReplicatorDynSol d_U B_U UniversalLocalView p
      selectorSchedule branchU
      (fun t => ((1 + Real.cos t) / 2) ^ Mcy)
      (fun t => ((1 + Real.sin t) / 2) ^ Mcy)
      (fun _ => (κ₀ : ℝ))
      (fun t => (g₀ : ℝ) * Real.exp (p.cα * t))
      (universalPval eta heta))
    (cfg : ℕ → UConf) (δnextWrite δwSettled : ℕ → ℝ) (N : ℕ)
    (hδnext_nonneg : ∀ j, N ≤ j → 0 ≤ δnextWrite j)
    (hδsettled_nonneg : ∀ j, N ≤ j → 0 ≤ δwSettled j)
    (hconst : ∀ j, N ≤ j → selectorMUHaltEncConst cfg j)
    (hstart : ∀ j, N ≤ j →
      |sol.z (selectorMUInterReadStart j) haltCoordU -
        stackMachineEncodingU.enc (cfg (j + 1)) haltCoordU| ≤ δwSettled j)
    (hoff : ∀ j, N ≤ j → selectorMUHaltEncConst cfg j → ∀ t ∈
        Icc (selectorMUInterReadStart j) (selectorMUNextWriteStart j),
      |sol.z t haltCoordU - sol.z (selectorMUInterReadStart j) haltCoordU| ≤
        selectorReplicatorHoldEnvelope j)
    (hnextWrite : ∀ j, N ≤ j → ∀ t ∈
        Icc (selectorMUNextWriteStart j) (selectorMUNextRead j),
      |sol.z t haltCoordU - stackMachineEncodingU.enc (cfg (j + 2)) haltCoordU| ≤
        δnextWrite j) :
    ∀ j, N ≤ j → ∀ t ∈ Icc (selectorMUInterReadStart j) (selectorMUNextRead j),
      |sol.z t haltCoordU - sol.z (selectorMUInterReadStart j) haltCoordU| ≤
        selectorMUSelfHoldDelta δnextWrite δwSettled j := by
  intro j hjN t ht
  rcases le_total t (selectorMUNextWriteStart j) with ht_left | ht_right
  · have ht_off : t ∈ Icc (selectorMUInterReadStart j) (selectorMUNextWriteStart j) :=
      ⟨ht.1, ht_left⟩
    have hbase := hoff j hjN (hconst j hjN) t ht_off
    have htail : 0 ≤ δnextWrite j + δwSettled j :=
      add_nonneg (hδnext_nonneg j hjN) (hδsettled_nonneg j hjN)
    calc
      |sol.z t haltCoordU - sol.z (selectorMUInterReadStart j) haltCoordU|
          ≤ selectorReplicatorHoldEnvelope j := hbase
      _ ≤ selectorMUSelfHoldDelta δnextWrite δwSettled j := by
        dsimp [selectorMUSelfHoldDelta]
        linarith
  · have ht_write : t ∈ Icc (selectorMUNextWriteStart j) (selectorMUNextRead j) :=
      ⟨ht_right, ht.2⟩
    have hwrite := hnextWrite j hjN t ht_write
    have hstart_j := hstart j hjN
    have htarget :
        |stackMachineEncodingU.enc (cfg (j + 2)) haltCoordU -
            sol.z (selectorMUInterReadStart j) haltCoordU| ≤ δwSettled j := by
      rw [hconst j hjN]
      simpa [abs_sub_comm] using hstart_j
    calc
      |sol.z t haltCoordU - sol.z (selectorMUInterReadStart j) haltCoordU|
          ≤ |sol.z t haltCoordU - stackMachineEncodingU.enc (cfg (j + 2)) haltCoordU|
            + |stackMachineEncodingU.enc (cfg (j + 2)) haltCoordU -
                sol.z (selectorMUInterReadStart j) haltCoordU| := abs_sub_le _ _ _
      _ ≤ δnextWrite j + δwSettled j := add_le_add hwrite htarget
      _ ≤ selectorMUSelfHoldDelta δnextWrite δwSettled j := by
        have hoff_nonneg : 0 ≤ selectorReplicatorHoldEnvelope j :=
          selectorReplicatorHoldEnvelope_nonneg j
        dsimp [selectorMUSelfHoldDelta]
        linarith

/-- The `bgpParams38` compatibility façade for pure inter-read self-hold. -/
theorem z_self_hold_on_inter_read
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : SelectorReplicatorDynSol d_U B_U UniversalLocalView bgpParams38 selectorSchedule
      branchU
      (fun t => ((1 + Real.cos t) / 2) ^ Mcy)
      (fun t => ((1 + Real.sin t) / 2) ^ Mcy)
      (fun _ => (κ₀ : ℝ))
      (fun t => (g₀ : ℝ) * Real.exp (bgpParams38.cα * t))
      (universalPval eta heta))
    (cfg : ℕ → UConf) (δnextWrite δwSettled : ℕ → ℝ) (N : ℕ)
    (hδnext_nonneg : ∀ j, N ≤ j → 0 ≤ δnextWrite j)
    (hδsettled_nonneg : ∀ j, N ≤ j → 0 ≤ δwSettled j)
    (hconst : ∀ j, N ≤ j → selectorMUHaltEncConst cfg j)
    (hstart : ∀ j, N ≤ j →
      |sol.z (selectorMUInterReadStart j) haltCoordU -
        stackMachineEncodingU.enc (cfg (j + 1)) haltCoordU| ≤ δwSettled j)
    (hoff : ∀ j, N ≤ j → selectorMUHaltEncConst cfg j → ∀ t ∈
        Icc (selectorMUInterReadStart j) (selectorMUNextWriteStart j),
      |sol.z t haltCoordU - sol.z (selectorMUInterReadStart j) haltCoordU| ≤
        selectorReplicatorHoldEnvelope j)
    (hnextWrite : ∀ j, N ≤ j → ∀ t ∈
        Icc (selectorMUNextWriteStart j) (selectorMUNextRead j),
      |sol.z t haltCoordU -
        stackMachineEncodingU.enc (cfg (j + 2)) haltCoordU| ≤
          δnextWrite j) :
    ∀ j, N ≤ j → ∀ t ∈
        Icc (selectorMUInterReadStart j) (selectorMUNextRead j),
      |sol.z t haltCoordU - sol.z (selectorMUInterReadStart j) haltCoordU| ≤
        selectorMUSelfHoldDelta δnextWrite δwSettled j := by
  exact
    z_self_hold_on_inter_read_P
      sol cfg δnextWrite δwSettled N
      hδnext_nonneg hδsettled_nonneg hconst hstart hoff hnextWrite

section PGeneralizationSentinel

variable {p : DynGateParams}

example : @z_self_hold_on_inter_read_P p =
    @z_self_hold_on_inter_read_P p := by
  rfl

end PGeneralizationSentinel

/-- Halting-run wrapper: the post-halt threshold is supplied by
`HaltAbsorbing`, and the finite-window producers are global in `j`. -/
theorem z_self_hold_on_inter_read_of_halts
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : SelectorReplicatorDynSol d_U B_U UniversalLocalView bgpParams38 selectorSchedule
      branchU
      (fun t => ((1 + Real.cos t) / 2) ^ Mcy)
      (fun t => ((1 + Real.sin t) / 2) ^ Mcy)
      (fun _ => (κ₀ : ℝ))
      (fun t => (g₀ : ℝ) * Real.exp (bgpParams38.cα * t))
      (universalPval eta heta))
    (w : ℕ) (hw : M_U.haltsOn w)
    (cfg : ℕ → UConf) (hcfg : ∀ j, cfg j = M_U.step^[j] (M_U.init w))
    (δnextWrite δwSettled : ℕ → ℝ)
    (hδnext_nonneg : ∀ j, 0 ≤ δnextWrite j)
    (hδsettled_nonneg : ∀ j, 0 ≤ δwSettled j)
    (hstart : ∀ j,
      |sol.z (selectorMUInterReadStart j) haltCoordU -
        stackMachineEncodingU.enc (cfg (j + 1)) haltCoordU| ≤ δwSettled j)
    (hoff : ∀ j, selectorMUHaltEncConst cfg j → ∀ t ∈
        Icc (selectorMUInterReadStart j) (selectorMUNextWriteStart j),
      |sol.z t haltCoordU - sol.z (selectorMUInterReadStart j) haltCoordU| ≤
        selectorReplicatorHoldEnvelope j)
    (hnextWrite : ∀ j, ∀ t ∈
        Icc (selectorMUNextWriteStart j) (selectorMUNextRead j),
      |sol.z t haltCoordU - stackMachineEncodingU.enc (cfg (j + 2)) haltCoordU| ≤
        δnextWrite j) :
    ∃ N : ℕ, ∀ j, N ≤ j → ∀ t ∈
        Icc (selectorMUInterReadStart j) (selectorMUNextRead j),
      |sol.z t haltCoordU - sol.z (selectorMUInterReadStart j) haltCoordU| ≤
        selectorMUSelfHoldDelta δnextWrite δwSettled j := by
  obtain ⟨N, hconst⟩ := halt_flag_target_const_cfg_succ_succ_of_halts hw cfg hcfg
  refine ⟨N, ?_⟩
  exact z_self_hold_on_inter_read sol cfg δnextWrite δwSettled N
    (fun j _hj => hδnext_nonneg j)
    (fun j _hj => hδsettled_nonneg j)
    hconst
    (fun j _hj => hstart j)
    (fun j _hj henc => hoff j henc)
    (fun j _hj => hnextWrite j)

#print axioms selectorMUInterReadStart
#print axioms selectorMUNextWriteStart
#print axioms selectorMUNextRead
#print axioms selectorMUSuccCast_pos
#print axioms selectorMUInterReadStart_le_nextWriteStart
#print axioms selectorMUNextWriteStart_le_nextRead
#print axioms selectorMUInterReadStart_le_nextRead
#print axioms selectorMUHaltEncConst
#print axioms selectorMUHaltEncConstW
#print axioms halt_flag_target_const_succ_succ_of_halts
#print axioms halt_flag_target_const_cfg_succ_succ_of_halts
#print axioms selectorMUSelfHoldDelta
#print axioms selectorMUSelfHoldDelta_tendsto_zero
#print axioms z_self_hold_on_inter_read
#print axioms z_self_hold_on_inter_read_of_halts

end Ripple.BoundedUniversality.BGP
