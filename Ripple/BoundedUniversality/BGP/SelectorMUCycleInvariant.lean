import Ripple.BoundedUniversality.BGP.SelectorReplicatorShiftedConc
import Ripple.BoundedUniversality.BGP.SelectorReplicatorRecovery
import Ripple.BoundedUniversality.BGP.MUReplicatorSettledConstructionShifted
import Ripple.BoundedUniversality.BGP.SelectorReplicatorAvgGap

/-!
# Per-cycle invariant for the shifted `M_U` selector route

This file is the Stage 2 framework from `CODEX_SPEC_CYCLE_INVARIANT.md`.
The hard phase estimates are left as explicit `sorry` sub-steps, with the
analytic obligation recorded next to each placeholder.
-/

noncomputable section

namespace Ripple.BoundedUniversality.BGP

open Set MachineInstance UniversalMachine Filter
open scoped BigOperators Topology

/-- Loser mass at the post-write read time of cycle `j`. -/
def selectorMULoserMassAtRead
    {p : DynGateParams}
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamilyP p eta heta Mcy κ₀ g₀) (w j : ℕ) : ℝ :=
  (Finset.univ.filter (fun v : UniversalLocalView =>
    v ≠ localViewU (solMUReplStaticCfg w j))).sum
      (fun v => (sol w).lam v (selectorMUWriteReadTime j))

/-- Halt-coordinate read error against the next encoded configuration. -/
def selectorMUHaltReadError
    {p : DynGateParams}
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamilyP p eta heta Mcy κ₀ g₀) (w j : ℕ) : ℝ :=
  |(sol w).z (selectorMUWriteReadTime j) haltCoordU -
    stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 1)) haltCoordU|

/-- `S_j`: the cycle invariant at `WriteRead(j) = 2πj + 5π/6`.

The `u` tube is carried over the whole write window ending at this read time.
The lambda and halt-coordinate clauses are read-time endpoint bounds. -/
structure SelectorMUCycleInvariant
    {p : DynGateParams}
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamilyP p eta heta Mcy κ₀ g₀) (w : ℕ)
    (ρU : ℝ) (eps δzH : ℕ → ℝ) (j : ℕ) : Prop where
  hu_win : ∀ t ∈ Set.Ico (selectorMUWriteStartTime j) (selectorMUWriteReadTime j),
    UTube ρU (solMUReplStaticCfg w j) ((sol w).u t)
  hlam_read : selectorMULoserMassAtRead sol w j ≤ eps j
  hz_halt : selectorMUHaltReadError sol w j ≤ δzH j

/-- Narrow field-integral producer for Step A.

This is the local version of the `hoff` cap surface from
`SelectorReplicatorSettledResidual`: it carries exactly the integral bound
consumed by `flag_drift_bound_on_interval_repl`, without importing that large
residual module into the cycle-invariant file. -/
structure SelectorMUCycleHoffFieldIntegralResidual
    {p : DynGateParams}
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamilyP p eta heta Mcy κ₀ g₀) where
  hfieldInt : ∀ w j, selectorMUHaltEncConst (solMUReplStaticCfg w) j →
    ∀ t ∈ Icc (selectorMUInterReadStart j) (selectorMUNextWriteStart j),
      (∫ τ in (selectorMUInterReadStart j)..t,
        |p.A * (sol w).α τ * bGateZ p.L ((sol w).μ τ) τ *
          (selectorMixTarget branchU (sol w).u (sol w).lam τ haltCoordU -
            (sol w).z τ haltCoordU)|) ≤ selectorReplicatorHoldEnvelope j

/-- Per-cycle field-integral producer for Step A.

This is the induction-friendly form: the analytic producer may use the already
established cycle invariant `S_j`.  The current upstream residual still carries
the halt-constant side condition, so the step form keeps that argument while
making the cycle invariant available. -/
structure SelectorMUCycleHoffFieldIntegralStep
    {p : DynGateParams}
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamilyP p eta heta Mcy κ₀ g₀)
    (w : ℕ) (ρU : ℝ) (eps δzH : ℕ → ℝ) where
  hfieldIntStep : ∀ j,
    SelectorMUCycleInvariant sol w ρU eps δzH j →
    selectorMUHaltEncConst (solMUReplStaticCfg w) j →
    ∀ t ∈ Icc (selectorMUInterReadStart j) (selectorMUNextWriteStart j),
      |(∫ τ in (selectorMUInterReadStart j)..t,
        p.A * (sol w).α τ * bGateZ p.L ((sol w).μ τ) τ *
          (selectorMixTarget branchU (sol w).u (sol w).lam τ haltCoordU -
            (sol w).z τ haltCoordU))| ≤
        selectorReplicatorHoldEnvelope j

namespace SelectorMUCycleHoffFieldIntegralResidual

/-- Compatibility adapter from the global residual to the induction-local step
form. -/
def toStep
    {p : DynGateParams}
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamilyP p eta heta Mcy κ₀ g₀}
    (res : SelectorMUCycleHoffFieldIntegralResidual sol)
    (w : ℕ) (ρU : ℝ) (eps δzH : ℕ → ℝ) :
    SelectorMUCycleHoffFieldIntegralStep sol w ρU eps δzH where
  hfieldIntStep := by
    intro j _Sj henc_const t ht
    exact
      (intervalIntegral.abs_integral_le_integral_abs ht.1).trans
        (res.hfieldInt w j henc_const t ht)

/-- Convert the Step-A field-integral cap into the pointwise self-drift bound. -/
theorem p_hoff
    {p : DynGateParams}
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamilyP p eta heta Mcy κ₀ g₀}
    (res : SelectorMUCycleHoffFieldIntegralResidual sol) :
    ∀ w j, selectorMUHaltEncConst (solMUReplStaticCfg w) j → ∀ t ∈
        Icc (selectorMUInterReadStart j) (selectorMUNextWriteStart j),
      |(sol w).z t haltCoordU -
        (sol w).z (selectorMUInterReadStart j) haltCoordU| ≤
        selectorReplicatorHoldEnvelope j := by
  intro w j henc_const t ht
  have hleft_nonneg : 0 ≤ selectorMUInterReadStart j := by
    unfold selectorMUInterReadStart selectorMUWriteReadTime
    positivity
  have hdom : ∀ s ∈ Icc (selectorMUInterReadStart j)
      (selectorMUNextWriteStart j), s ∈ selectorSchedule.domain := by
    intro s hs
    exact selectorSchedule_domain_of_nonneg_structural s (le_trans hleft_nonneg hs.1)
  exact
    flag_drift_bound_on_interval_repl (sol w) haltCoordU
      (selectorMUInterReadStart_le_nextWriteStart j) hdom
      (selector_replicator_gateZ_integrand_continuous (sol w))
      (res.hfieldInt w j henc_const) t ht

end SelectorMUCycleHoffFieldIntegralResidual

namespace SelectorMUCycleHoffFieldIntegralStep

/-- Convert the step-local field-integral cap into the pointwise self-drift
bound. -/
theorem p_hoff
    {p : DynGateParams}
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamilyP p eta heta Mcy κ₀ g₀}
    {w : ℕ} {ρU : ℝ} {eps δzH : ℕ → ℝ}
    (res : SelectorMUCycleHoffFieldIntegralStep sol w ρU eps δzH) :
    ∀ j, SelectorMUCycleInvariant sol w ρU eps δzH j →
      selectorMUHaltEncConst (solMUReplStaticCfg w) j →
      ∀ t ∈ Icc (selectorMUInterReadStart j) (selectorMUNextWriteStart j),
        |(sol w).z t haltCoordU -
          (sol w).z (selectorMUInterReadStart j) haltCoordU| ≤
          selectorReplicatorHoldEnvelope j := by
  intro j Sj henc_const t ht
  let a : ℝ := selectorMUInterReadStart j
  let b : ℝ := selectorMUNextWriteStart j
  let g : ℝ → ℝ := fun τ =>
    p.A * (sol w).α τ * bGateZ p.L ((sol w).μ τ) τ *
      (selectorMixTarget branchU (sol w).u (sol w).lam τ haltCoordU -
        (sol w).z τ haltCoordU)
  have ha_nonneg : 0 ≤ a := by
    dsimp [a]
    unfold selectorMUInterReadStart selectorMUWriteReadTime
    positivity
  have hdom : ∀ s ∈ Icc a b, s ∈ selectorSchedule.domain := by
    intro s hs
    exact selectorSchedule_domain_of_nonneg_structural s (le_trans ha_nonneg hs.1)
  have hgc : Continuous g := by
    dsimp [g]
    exact
      (selector_replicator_gateZ_integrand_continuous (sol w)).mul
        (((sol w).cont_mixTarget haltCoordU).sub ((sol w).cont_z haltCoordU))
  have hderiv : ∀ τ ∈ Icc a t,
      HasDerivAt (fun ξ => (sol w).z ξ haltCoordU) (g τ) τ := by
    intro τ hτ
    have hτab : τ ∈ Icc a b := ⟨hτ.1, le_trans hτ.2 ht.2⟩
    dsimp [g]
    exact (sol w).z_hasDeriv τ (hdom τ hτab) haltCoordU
  have hftc :
      (∫ τ in a..t, g τ) =
        (sol w).z t haltCoordU - (sol w).z a haltCoordU := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro τ hτ
      rw [Set.uIcc_of_le ht.1] at hτ
      exact hderiv τ hτ
    · exact hgc.intervalIntegrable a t
  rw [← hftc]
  simpa [a, g] using res.hfieldIntStep j Sj henc_const t ht

end SelectorMUCycleHoffFieldIntegralStep

section PGeneralizationSentinels

variable {p : DynGateParams}

example : @selectorMULoserMassAtRead p =
    @selectorMULoserMassAtRead p := by
  rfl

example : @selectorMUHaltReadError p =
    @selectorMUHaltReadError p := by
  rfl

example : @SelectorMUCycleInvariant p =
    @SelectorMUCycleInvariant p := by
  rfl

example : @SelectorMUCycleHoffFieldIntegralResidual p =
    @SelectorMUCycleHoffFieldIntegralResidual p := by
  rfl

example : @SelectorMUCycleHoffFieldIntegralStep p =
    @SelectorMUCycleHoffFieldIntegralStep p := by
  rfl

example : @SelectorMUCycleHoffFieldIntegralResidual.toStep p =
    @SelectorMUCycleHoffFieldIntegralResidual.toStep p := by
  rfl

example : @SelectorMUCycleHoffFieldIntegralResidual.p_hoff p =
    @SelectorMUCycleHoffFieldIntegralResidual.p_hoff p := by
  rfl

example : @SelectorMUCycleHoffFieldIntegralStep.p_hoff p =
    @SelectorMUCycleHoffFieldIntegralStep.p_hoff p := by
  rfl

end PGeneralizationSentinels

/-- Step A: freeze/hold after `WriteRead(j)`.

This is the off-phase `z` self-hold residual consumed by the late-start
headline. -/
theorem selectorMU_cycle_freeze_substep
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    {w : ℕ} {j : ℕ}
    (hoffIntegral : SelectorMUCycleHoffFieldIntegralResidual sol) :
    selectorMUHaltEncConst (solMUReplStaticCfg w) j →
      ∀ t ∈ Icc (selectorMUInterReadStart j) (selectorMUNextWriteStart j),
        |(sol w).z t haltCoordU -
          (sol w).z (selectorMUInterReadStart j) haltCoordU| ≤
            selectorReplicatorHoldEnvelope j := by
  intro hconst t ht
  simpa [selectorMUHaltEncConstW] using
    hoffIntegral.p_hoff w j hconst t ht

/-- Step A in induction-local form. -/
theorem selectorMU_cycle_freeze_substep_step
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    {w : ℕ} {ρU : ℝ} {eps δzH : ℕ → ℝ} {j : ℕ}
    (hoffStep : SelectorMUCycleHoffFieldIntegralStep sol w ρU eps δzH)
    (Sj : SelectorMUCycleInvariant sol w ρU eps δzH j) :
    selectorMUHaltEncConst (solMUReplStaticCfg w) j →
      ∀ t ∈ Icc (selectorMUInterReadStart j) (selectorMUNextWriteStart j),
        |(sol w).z t haltCoordU -
          (sol w).z (selectorMUInterReadStart j) haltCoordU| ≤
            selectorReplicatorHoldEnvelope j := by
  intro hconst t ht
  exact hoffStep.p_hoff j Sj hconst t ht

/-- Step B: copy the freshly written `z` target into `u`, then freeze `u`.

The result is the next cycle's write-window `UTube`. -/
theorem selectorMU_cycle_ucopy_substep
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    {w : ℕ} {ρU : ℝ} {j : ℕ}
    (hhaltCopyFreeze : ∀ t ∈ Set.Ico (selectorMUWriteStartTime (j + 1))
        (selectorMUWriteReadTime (j + 1)),
      |(sol w).u t haltCoordU -
        stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 1)) haltCoordU| ≤ ρU)
    (hstackCopyFreeze : ∀ i : Fin d_U, i ≠ haltCoordU →
      ∀ t ∈ Set.Ico (selectorMUWriteStartTime (j + 1))
          (selectorMUWriteReadTime (j + 1)),
        |(sol w).u t i -
          stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 1)) i| ≤ ρU) :
    ∀ t ∈ Set.Ico (selectorMUWriteStartTime (j + 1))
        (selectorMUWriteReadTime (j + 1)),
      UTube ρU (solMUReplStaticCfg w (j + 1)) ((sol w).u t) := by
  intro t ht i
  by_cases hi : i = haltCoordU
  · subst i
    simpa [UTube, stackMachineEncodingU_enc_eq] using hhaltCopyFreeze t ht
  · simpa [UTube, stackMachineEncodingU_enc_eq] using hstackCopyFreeze i hi t ht

private theorem selectorMU_cycle_lam_sum_forward
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (w : ℕ) :
    ∀ t : ℝ, 0 ≤ t →
      (∑ v : UniversalLocalView, (sol w).lam v t) = 1 := by
  classical
  haveI : Nonempty UniversalLocalView := ⟨defaultLocalViewU⟩
  have hode : ∀ v : UniversalLocalView, ∀ t : ℝ, 0 ≤ t →
      HasDerivAt ((sol w).lam v)
        ((((1 + Real.cos t) / 2) ^ Mcy * (κ₀ : ℝ)) *
            (1 / (Fintype.card UniversalLocalView : ℝ) - (sol w).lam v t)
          + (((1 + Real.sin t) / 2) ^ Mcy *
              ((g₀ : ℝ) * Real.exp (bgpParams38.cα * t))) *
            (sol w).lam v t *
              (universalPval eta heta v ((sol w).u t)
                - ∑ u : UniversalLocalView,
                    (sol w).lam u t * universalPval eta heta u ((sol w).u t))) t := by
    intro v t ht
    simpa [selectorSchedule] using
      (sol w).lam_hasDeriv v t (by simpa [selectorSchedule] using ht)
  exact
    replicator_sum_lam_eq_one
      (lam := fun v t => (sol w).lam v t)
      (P := fun v t => universalPval eta heta v ((sol w).u t))
      (cr := fun t => ((1 + Real.cos t) / 2) ^ Mcy * (κ₀ : ℝ))
      (cg := fun t =>
        ((1 + Real.sin t) / 2) ^ Mcy *
          ((g₀ : ℝ) * Real.exp (bgpParams38.cα * t)))
      boxInputs.hcr_cont boxInputs.hcg_cont
      (fun v => (sol w).cont_lam v)
      (boxInputs.hP_cont w) hode (boxInputs.hlam_sum0 w)

private theorem selectorMU_cycle_lam_nonneg_forward
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (w : ℕ) :
    ∀ v : UniversalLocalView, ∀ t : ℝ, 0 ≤ t → 0 ≤ (sol w).lam v t := by
  classical
  haveI : Nonempty UniversalLocalView := ⟨defaultLocalViewU⟩
  have hode : ∀ v : UniversalLocalView, ∀ t : ℝ, 0 ≤ t →
      HasDerivAt ((sol w).lam v)
        ((((1 + Real.cos t) / 2) ^ Mcy * (κ₀ : ℝ)) *
            (1 / (Fintype.card UniversalLocalView : ℝ) - (sol w).lam v t)
          + (((1 + Real.sin t) / 2) ^ Mcy *
              ((g₀ : ℝ) * Real.exp (bgpParams38.cα * t))) *
            (sol w).lam v t *
              (universalPval eta heta v ((sol w).u t)
                - ∑ u : UniversalLocalView,
                    (sol w).lam u t * universalPval eta heta u ((sol w).u t))) t := by
    intro v t ht
    simpa [selectorSchedule] using
      (sol w).lam_hasDeriv v t (by simpa [selectorSchedule] using ht)
  exact
    replicator_lam_nonneg
      (lam := fun v t => (sol w).lam v t)
      (P := fun v t => universalPval eta heta v ((sol w).u t))
      (cr := fun t => ((1 + Real.cos t) / 2) ^ Mcy * (κ₀ : ℝ))
      (cg := fun t =>
        ((1 + Real.sin t) / 2) ^ Mcy *
          ((g₀ : ℝ) * Real.exp (bgpParams38.cα * t)))
      boxInputs.hcr_cont boxInputs.hcg_cont
      (fun v => (sol w).cont_lam v)
      (boxInputs.hP_cont w) boxInputs.hcr_nonneg hode
      (boxInputs.hlam_init_nonneg w)

private theorem selectorMU_cycle_lam_ratio_card_bound_at
    {V : Type} [Fintype V] [Nonempty V]
    (lam : V → ℝ) (vstar : V)
    (hsum : (∑ v : V, lam v) = 1)
    (hlam_nonneg : ∀ v : V, 0 ≤ lam v)
    (hqL : 1 / (Fintype.card V : ℝ) ≤ lam vstar) :
    ∀ v : V, v ≠ vstar →
      lam v / lam vstar ≤ (Fintype.card V : ℝ) := by
  classical
  intro v _hv
  have hN_pos : 0 < (Fintype.card V : ℝ) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr inferInstance :
      0 < Fintype.card V)
  have hden_pos : 0 < lam vstar :=
    lt_of_lt_of_le (by positivity : 0 < (1 / (Fintype.card V : ℝ))) hqL
  have hnum_le_one : lam v ≤ 1 := by
    have hle_sum : lam v ≤ ∑ u : V, lam u :=
      Finset.single_le_sum (fun u _ => hlam_nonneg u) (Finset.mem_univ v)
    simpa [hsum] using hle_sum
  rw [div_le_iff₀ hden_pos]
  have hmul_floor :
      (1 : ℝ) ≤ (Fintype.card V : ℝ) * lam vstar := by
    have hmul := mul_le_mul_of_nonneg_left hqL hN_pos.le
    have hone :
        (Fintype.card V : ℝ) * (1 / (Fintype.card V : ℝ)) = 1 := by
      field_simp [ne_of_gt hN_pos]
    simpa [hone] using hmul
  exact le_trans hnum_le_one hmul_floor

/-- Step C: winner-lambda recovery at the shifted select-start anchor. -/
theorem selectorMU_cycle_recovery_substep
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    {w : ℕ} {eps δzH : ℕ → ℝ} {j : ℕ}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (herr : (gateSelectorAtomsCoordN (universalGateAtoms eta heta)).errSel < 1 / 2)
    (crMin crMax cgMin recoveryGap recoveryB : ℕ → ℝ)
    (recoveryK : ℕ → ℕ)
    (hN2 : 2 ≤ Fintype.card UniversalLocalView)
    (hcrMin_pos : ∀ k, 0 < crMin k)
    (hcrMin_le_crMax : ∀ k, crMin k ≤ crMax k)
    (hcgMin_nonneg : ∀ k, 0 ≤ cgMin k)
    (hrecoveryGap_nonneg : ∀ k, 0 ≤ recoveryGap k)
    (hrecoveryGap_le_gapVal : ∀ k, recoveryGap k ≤ selectorReplicatorGapVal eta heta)
    (hrecoveryB_eq : ∀ k, recoveryB k = cgMin k * recoveryGap k / 2 - crMax k)
    (hrecoveryB_pos : ∀ k, 0 < recoveryB k)
    (hrecoveryBDelta : ∀ k, (recoveryK k : ℝ) ≤
      recoveryB k * selectorMURecoveryDelta)
    (hpow : ∀ k, 1 + recoveryB k / crMin k ≤ (2 : ℝ) ^ recoveryK k)
    (hcr_bounds : ∀ k,
      ∀ u ∈ Icc (selectorMUWriteStartTime k) (selectorMUSelectStartTime k),
        crMin k ≤ ((1 + Real.cos u) / 2) ^ Mcy * (κ₀ : ℝ) ∧
          ((1 + Real.cos u) / 2) ^ Mcy * (κ₀ : ℝ) ≤ crMax k)
    (hcg_min : ∀ k,
      ∀ u ∈ Icc (selectorMUWriteStartTime k) (selectorMUSelectStartTime k),
        cgMin k ≤
          ((1 + Real.sin u) / 2) ^ Mcy *
            ((g₀ : ℝ) * Real.exp (bgpParams38.cα * u)))
    (Sj : SelectorMUCycleInvariant sol w r_LE_U eps δzH j)
    (hu_next : ∀ t ∈ Set.Ico (selectorMUWriteStartTime (j + 1))
        (selectorMUWriteReadTime (j + 1)),
      UTube r_LE_U (solMUReplStaticCfg w (j + 1)) ((sol w).u t)) :
    1 / (Fintype.card UniversalLocalView : ℝ) ≤
      (sol w).lam (localViewU (solMUReplStaticCfg w (j + 1)))
        (selectorMUSelectStartTime (j + 1)) := by
  classical
  haveI : Nonempty UniversalLocalView := ⟨defaultLocalViewU⟩
  have hsum_forward := selectorMU_cycle_lam_sum_forward (sol := sol) boxInputs w
  have hlam_forward := selectorMU_cycle_lam_nonneg_forward (sol := sol) boxInputs w
  have hgap0 : 0 < selectorReplicatorGapVal eta heta :=
    solMURepl_static_hgap0 eta heta herr
  have hgap_floor :
      ∀ v : UniversalLocalView, v ≠ localViewU (solMUReplStaticCfg w (j + 1)) →
        ∀ u ∈ Ico (selectorMUWriteStartTime (j + 1))
            (selectorMUSelectStartTime (j + 1)),
          universalPval eta heta v ((sol w).u u) -
            universalPval eta heta (localViewU (solMUReplStaticCfg w (j + 1)))
              ((sol w).u u) ≤ 0 := by
    intro v hv u hu
    have hu_full : u ∈ Ico (selectorMUWriteStartTime (j + 1))
        (selectorMUWriteReadTime (j + 1)) :=
      ⟨hu.1, lt_of_lt_of_le hu.2 (selectorMUSelectStart_le_read (j + 1))⟩
    have hmargins :=
      universal_selector_margins_of_tube eta heta (hu_next u hu_full) herr
    have hwinner :
        1 / 2 - (gateSelectorAtomsCoordN (universalGateAtoms eta heta)).errSel ≤
          universalPval eta heta (localViewU (solMUReplStaticCfg w (j + 1)))
            ((sol w).u u) := by
      simpa [universalPval] using hmargins.1
    have hloser :
        universalPval eta heta v ((sol w).u u) ≤
          -(1 / 2 - (gateSelectorAtomsCoordN (universalGateAtoms eta heta)).errSel) := by
      simpa [universalPval] using hmargins.2 v hv
    have hgap_le :
        universalPval eta heta v ((sol w).u u) -
            universalPval eta heta (localViewU (solMUReplStaticCfg w (j + 1)))
              ((sol w).u u) ≤ -selectorReplicatorGapVal eta heta := by
      dsimp [selectorReplicatorGapVal]
      linarith
    exact le_trans hgap_le (neg_nonpos.mpr hgap0.le)
  have havg_gap :
      ∀ u ∈ Ico (selectorMUWriteStartTime (j + 1))
          (selectorMUSelectStartTime (j + 1)),
        recoveryGap (j + 1) *
            (1 - (sol w).lam (localViewU (solMUReplStaticCfg w (j + 1))) u) ≤
          universalPval eta heta (localViewU (solMUReplStaticCfg w (j + 1)))
              ((sol w).u u) -
            ∑ v : UniversalLocalView,
              (sol w).lam v u * universalPval eta heta v ((sol w).u u) := by
    intro u hu
    have hu_full : u ∈ Ico (selectorMUWriteStartTime (j + 1))
        (selectorMUWriteReadTime (j + 1)) :=
      ⟨hu.1, lt_of_lt_of_le hu.2 (selectorMUSelectStart_le_read (j + 1))⟩
    exact
      selector_replicator_havg_gap_of_utube
        (eta := eta) (heta := heta)
        (lam := fun v : UniversalLocalView => (sol w).lam v u)
        (u := (sol w).u u)
        (c := solMUReplStaticCfg w (j + 1))
        (gap := recoveryGap (j + 1))
        herr
        (hu_next u hu_full)
        (hrecoveryGap_le_gapVal (j + 1))
        (hsum_forward u (le_trans (selectorMUWriteStartTime_nonneg (j + 1)) hu.1))
        (fun v => hlam_forward v u
          (le_trans (selectorMUWriteStartTime_nonneg (j + 1)) hu.1))
  exact
    replicator_winner_recovery_at_selectStart
      (sol := sol w)
      (vstar := localViewU (solMUReplStaticCfg w (j + 1)))
      (j := j + 1)
      (crMin := crMin (j + 1))
      (crMax := crMax (j + 1))
      (cgMin := cgMin (j + 1))
      (gap := recoveryGap (j + 1))
      (b := recoveryB (j + 1))
      hN2
      (hcrMin_pos (j + 1))
      (hcrMin_le_crMax (j + 1))
      (hcgMin_nonneg (j + 1))
      (hrecoveryGap_nonneg (j + 1))
      (hrecoveryB_eq (j + 1))
      (hrecoveryB_pos (j + 1))
      (hrecoveryBDelta (j + 1))
      (hpow (j + 1))
      (fun u hu => solMURepl_static_hdom_nonneg u
        (le_trans (selectorMUWriteStartTime_nonneg (j + 1)) hu.1))
      (hcr_bounds (j + 1))
      (hcg_min (j + 1))
      hgap_floor
      havg_gap
      (fun u hu => hsum_forward u
        (le_trans (selectorMUWriteStartTime_nonneg (j + 1)) hu.1))
      (fun v u hu => hlam_forward v u
        (le_trans (selectorMUWriteStartTime_nonneg (j + 1)) hu.1))

/-- Step D: shifted recovery plus settled write produces the next read facts. -/
theorem selectorMU_cycle_write_substep
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    {w : ℕ} {eps δzH : ℕ → ℝ} {j : ℕ}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (herr : (gateSelectorAtomsCoordN (universalGateAtoms eta heta)).errSel < 1 / 2)
    (hκ₀_nonneg : 0 ≤ (κ₀ : ℝ))
    (hg₀ : 0 < (g₀ : ℝ))
    (hscale : (κ₀ : ℝ) ≤ ((3 / 4 : ℝ) ^ Mcy) * (g₀ : ℝ))
    {Bz : ℕ → ℝ}
    (hz_start : ∀ k,
      |(sol w).z (selectorMUWriteHoldTime k) haltCoordU -
        stackMachineEncodingU.enc (solMUReplStaticCfg w (k + 1)) haltCoordU| ≤ Bz k)
    (heps_bound :
      epsLamShiftedFullAt sol w (selectorReplicatorGapVal eta heta)
          (Fintype.card UniversalLocalView : ℝ) (j + 1) ≤ eps (j + 1))
    (hδzH_bound :
      solMUReplSettledRho (fun k => selectorSettledWriteIntLower k) Bz
          (fun k => (Fintype.card UniversalLocalView : ℝ) *
            epsLamShiftedFullAt sol w (selectorReplicatorGapVal eta heta)
              (Fintype.card UniversalLocalView : ℝ) k)
          (j + 1) ≤ δzH (j + 1))
    (Sj : SelectorMUCycleInvariant sol w r_LE_U eps δzH j)
    (hu_next : ∀ t ∈ Set.Ico (selectorMUWriteStartTime (j + 1))
        (selectorMUWriteReadTime (j + 1)),
      UTube r_LE_U (solMUReplStaticCfg w (j + 1)) ((sol w).u t))
    (hrecovery :
      1 / (Fintype.card UniversalLocalView : ℝ) ≤
        (sol w).lam (localViewU (solMUReplStaticCfg w (j + 1)))
          (selectorMUSelectStartTime (j + 1))) :
    selectorMULoserMassAtRead sol w (j + 1) ≤ eps (j + 1) ∧
      selectorMUHaltReadError sol w (j + 1) ≤ δzH (j + 1) := by
  classical
  haveI : Nonempty UniversalLocalView := ⟨defaultLocalViewU⟩
  let gap : ℝ := selectorReplicatorGapVal eta heta
  let R0 : ℝ := Fintype.card UniversalLocalView
  let epsLam : ℕ → ℝ := epsLamShiftedFullAt sol w gap R0
  let Λ : ℕ → ℝ := fun k => selectorSettledWriteIntLower k
  have hgap0 : 0 < gap := by
    simpa [gap] using solMURepl_static_hgap0 eta heta herr
  have hR0_nonneg : 0 ≤ R0 := by
    dsimp [R0]
    positivity
  have hselect_nonneg : 0 ≤ selectorMUSelectStartTime (j + 1) :=
    le_trans (selectorMUWriteStartTime_nonneg (j + 1))
      (selectorMUWriteStart_le_selectStart (j + 1))
  have hsum_forward := selectorMU_cycle_lam_sum_forward (sol := sol) boxInputs w
  have hlam_forward := selectorMU_cycle_lam_nonneg_forward (sol := sol) boxInputs w
  have hqL_select :
      ∀ t ∈ Icc (selectorMUSelectStartTime (j + 1))
          (selectorMUWriteReadTime (j + 1)),
        1 / (Fintype.card UniversalLocalView : ℝ) ≤
          (sol w).lam (localViewU (solMUReplStaticCfg w (j + 1))) t := by
    have hgap_floor :
        ∀ v : UniversalLocalView, v ≠ localViewU (solMUReplStaticCfg w (j + 1)) →
          ∀ t ∈ Ico (selectorMUSelectStartTime (j + 1))
              (selectorMUWriteReadTime (j + 1)),
            universalPval eta heta v ((sol w).u t) -
              universalPval eta heta (localViewU (solMUReplStaticCfg w (j + 1)))
                ((sol w).u t) ≤ 0 := by
      intro v hv t ht
      have ht_full : t ∈ Ico (selectorMUWriteStartTime (j + 1))
          (selectorMUWriteReadTime (j + 1)) :=
        ⟨le_trans (selectorMUWriteStart_le_selectStart (j + 1)) ht.1, ht.2⟩
      have hmargins :=
        universal_selector_margins_of_tube eta heta (hu_next t ht_full) herr
      have hwinner :
          1 / 2 - (gateSelectorAtomsCoordN (universalGateAtoms eta heta)).errSel ≤
            universalPval eta heta (localViewU (solMUReplStaticCfg w (j + 1)))
              ((sol w).u t) := by
        simpa [universalPval] using hmargins.1
      have hloser :
          universalPval eta heta v ((sol w).u t) ≤
            -(1 / 2 - (gateSelectorAtomsCoordN (universalGateAtoms eta heta)).errSel) := by
        simpa [universalPval] using hmargins.2 v hv
      have hgap_le :
          universalPval eta heta v ((sol w).u t) -
              universalPval eta heta (localViewU (solMUReplStaticCfg w (j + 1)))
                ((sol w).u t) ≤ -selectorReplicatorGapVal eta heta := by
        dsimp [selectorReplicatorGapVal]
        linarith
      exact le_trans hgap_le (by simpa [gap] using neg_nonpos.mpr hgap0.le)
    exact
      replicator_winner_floor_on_interval_param
        (sol := sol w) (localViewU (solMUReplStaticCfg w (j + 1)))
        (a := selectorMUSelectStartTime (j + 1))
        (b := selectorMUWriteReadTime (j + 1))
        (selectorMUSelectStart_le_read (j + 1))
        (1 / (Fintype.card UniversalLocalView : ℝ)) (le_refl _)
        (fun t ht => solMURepl_static_hdom_nonneg t
          (le_trans hselect_nonneg ht.1))
        (fun t _ht => boxInputs.hcr_nonneg t)
        (fun t _ht =>
          mul_nonneg
            (pow_nonneg (by nlinarith [Real.neg_one_le_sin t]) _)
            (mul_nonneg hg₀.le (Real.exp_pos _).le))
        hgap_floor
        (fun t ht => hsum_forward t (le_trans hselect_nonneg ht.1))
        (fun v t ht => hlam_forward v t (le_trans hselect_nonneg ht.1))
        hrecovery
  have hRa_select :
      ∀ v : UniversalLocalView, v ≠ localViewU (solMUReplStaticCfg w (j + 1)) →
        (sol w).lam v (selectorMUSelectStartTime (j + 1)) /
            (sol w).lam (localViewU (solMUReplStaticCfg w (j + 1)))
              (selectorMUSelectStartTime (j + 1)) ≤ R0 := by
    have hsum := hsum_forward (selectorMUSelectStartTime (j + 1)) hselect_nonneg
    have hnonneg : ∀ v : UniversalLocalView,
        0 ≤ (sol w).lam v (selectorMUSelectStartTime (j + 1)) :=
      fun v => hlam_forward v (selectorMUSelectStartTime (j + 1)) hselect_nonneg
    simpa [R0] using
      selectorMU_cycle_lam_ratio_card_bound_at
        (lam := fun v : UniversalLocalView =>
          (sol w).lam v (selectorMUSelectStartTime (j + 1)))
        (vstar := localViewU (solMUReplStaticCfg w (j + 1)))
        hsum hnonneg hrecovery
  have hloser :
      ∀ t ∈ Icc (selectorMUWriteHoldTime (j + 1))
          (selectorMUWriteReadTime (j + 1)),
        (Finset.univ.filter (fun v : UniversalLocalView =>
          v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
            (fun v => (sol w).lam v t) ≤ epsLam (j + 1) := by
    have hgap_cond :
        ∀ v : UniversalLocalView, v ≠ localViewU (solMUReplStaticCfg w (j + 1)) →
          ∀ t ∈ Ico (selectorMUSelectStartTime (j + 1))
              (selectorMUWriteReadTime (j + 1)),
            universalPval eta heta v ((sol w).u t) -
              universalPval eta heta (localViewU (solMUReplStaticCfg w (j + 1)))
                ((sol w).u t) ≤ -gap := by
      intro v hv t ht
      have ht_full : t ∈ Ico (selectorMUWriteStartTime (j + 1))
          (selectorMUWriteReadTime (j + 1)) :=
        ⟨le_trans (selectorMUWriteStart_le_selectStart (j + 1)) ht.1, ht.2⟩
      have hmargins :=
        universal_selector_margins_of_tube eta heta (hu_next t ht_full) herr
      have hwinner :
          1 / 2 - (gateSelectorAtomsCoordN (universalGateAtoms eta heta)).errSel ≤
            universalPval eta heta (localViewU (solMUReplStaticCfg w (j + 1)))
              ((sol w).u t) := by
        simpa [universalPval] using hmargins.1
      have hloser :
          universalPval eta heta v ((sol w).u t) ≤
            -(1 / 2 - (gateSelectorAtomsCoordN (universalGateAtoms eta heta)).errSel) := by
        simpa [universalPval] using hmargins.2 v hv
      have hgap_le :
          universalPval eta heta v ((sol w).u t) -
              universalPval eta heta (localViewU (solMUReplStaticCfg w (j + 1)))
                ((sol w).u t) ≤ -selectorReplicatorGapVal eta heta := by
        dsimp [selectorReplicatorGapVal]
        linarith
      simpa [gap] using hgap_le
    exact
      hloser_of_shifted_concentration
        (sol := sol) (cfg := fun k => solMUReplStaticCfg w k)
        w (j + 1) (gap := gap) (R0 := R0)
        hgap0 hR0_nonneg hκ₀_nonneg hscale
        (fun t ht => solMURepl_static_hdom_nonneg t
          (le_trans hselect_nonneg ht.1))
        hqL_select
        (fun v t ht => hlam_forward v t (le_trans hselect_nonneg ht.1))
        (fun t ht => hsum_forward t (le_trans hselect_nonneg ht.1))
        hgap_cond
        hRa_select
  have hread_lam :
      selectorMULoserMassAtRead sol w (j + 1) ≤ eps (j + 1) := by
    have ht_read : selectorMUWriteReadTime (j + 1) ∈
        Icc (selectorMUWriteHoldTime (j + 1))
          (selectorMUWriteReadTime (j + 1)) :=
      right_mem_Icc.mpr (selectorMUWriteHold_le_read (j + 1))
    exact le_trans (by simpa [selectorMULoserMassAtRead, epsLam] using hloser _ ht_read)
      heps_bound
  have hepsLam_nonneg_j : 0 ≤ epsLam (j + 1) := by
    have ht_hold : selectorMUWriteHoldTime (j + 1) ∈
        Icc (selectorMUWriteHoldTime (j + 1))
          (selectorMUWriteReadTime (j + 1)) :=
      ⟨le_rfl, selectorMUWriteHold_le_read (j + 1)⟩
    have ht0 : 0 ≤ selectorMUWriteHoldTime (j + 1) :=
      le_trans (selectorMUWriteStartTime_nonneg (j + 1))
        (selectorMUWriteStart_le_hold (j + 1))
    have hloser_nonneg :
        0 ≤ (Finset.univ.filter (fun v : UniversalLocalView =>
          v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
            (fun v => (sol w).lam v (selectorMUWriteHoldTime (j + 1))) :=
      Finset.sum_nonneg (fun v _hv => hlam_forward v _ ht0)
    exact le_trans hloser_nonneg (hloser _ ht_hold)
  have hmix_settled :
      ∀ t ∈ Icc (selectorMUWriteHoldTime (j + 1))
          (selectorMUWriteReadTime (j + 1)),
        |selectorMixTarget branchU (sol w).u (sol w).lam t haltCoordU -
          stackMachineEncodingU.enc (solMUReplStaticCfg w ((j + 1) + 1))
            haltCoordU| ≤
            (Fintype.card UniversalLocalView : ℝ) * epsLam (j + 1) := by
    intro t ht
    have hwrong : ∀ v : UniversalLocalView,
        v ≠ localViewU (solMUReplStaticCfg w (j + 1)) →
          (sol w).lam v t ≤ epsLam (j + 1) := by
      intro v hv
      have ht0 : 0 ≤ t :=
        le_trans
          (le_trans (selectorMUWriteStartTime_nonneg (j + 1))
            (selectorMUWriteStart_le_hold (j + 1))) ht.1
      exact le_trans
        (Finset.single_le_sum (fun u _ => hlam_forward u t ht0) (by simp [hv]))
        (hloser t ht)
    have hraw := selectorMixTarget_halt_to_next_of_concentration
      (sol w).u (sol w).lam t (solMUReplStaticCfg w (j + 1))
      hepsLam_nonneg_j
      (hsum_forward t
        (le_trans
          (le_trans (selectorMUWriteStartTime_nonneg (j + 1))
            (selectorMUWriteStart_le_hold (j + 1))) ht.1))
      (fun v => hlam_forward v t
        (le_trans
          (le_trans (selectorMUWriteStartTime_nonneg (j + 1))
            (selectorMUWriteStart_le_hold (j + 1))) ht.1))
      hwrong
    simpa [solMUReplStaticCfg_step, epsLam] using hraw
  have hΛ_lower :
      Λ (j + 1) ≤ ∫ τ in selectorMUWriteHoldTime (j + 1)..selectorMUWriteReadTime (j + 1),
        bgpParams38.A * (sol w).α τ * bGateZ bgpParams38.L ((sol w).μ τ) τ := by
    have hdom_nonneg := solMURepl_static_hdom_nonneg
    have hgZ_cont := solMURepl_static_hgZ_cont sol w
    have hgZ0 := solMURepl_static_hgZ0 sol
    have hsub := selector_settled_writeIntegral_lower_lbd_repl (sol w) (j + 1)
      hdom_nonneg hgZ_cont
    have hcont_int : ∀ a b : ℝ,
        IntervalIntegrable
          (fun t : ℝ => bgpParams38.A * (sol w).α t *
            bGateZ bgpParams38.L ((sol w).μ t) t)
          MeasureTheory.volume a b :=
      fun a b => hgZ_cont.intervalIntegrable a b
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (hcont_int (selectorMUWriteHoldTime (j + 1))
        (selectorMUSettledWriteSubEnd (j + 1)))
      (hcont_int (selectorMUSettledWriteSubEnd (j + 1))
        (selectorMUWriteReadTime (j + 1)))
    have htail_nonneg :
        0 ≤ ∫ t in selectorMUSettledWriteSubEnd (j + 1)..selectorMUWriteReadTime (j + 1),
            bgpParams38.A * (sol w).α t *
              bGateZ bgpParams38.L ((sol w).μ t) t := by
      apply intervalIntegral.integral_nonneg (selectorMUSettledSubEnd_le_read (j + 1))
      intro t ht
      exact hgZ0 w (j + 1) t
        ⟨le_trans (selectorMUWriteHold_le_settledSubEnd (j + 1)) ht.1, ht.2⟩
    simpa [Λ] using (by linarith)
  have hz_read_raw :
      |(sol w).z (selectorMUWriteReadTime (j + 1)) haltCoordU -
        stackMachineEncodingU.enc (solMUReplStaticCfg w ((j + 1) + 1)) haltCoordU| ≤
          solMUReplSettledRho Λ Bz
            (fun k => (Fintype.card UniversalLocalView : ℝ) * epsLam k) (j + 1) := by
    have hz :=
      z_write_settled_endpoint
        (sol w) (fun k => solMUReplStaticCfg w k) Λ Bz
        (fun k => (Fintype.card UniversalLocalView : ℝ) * epsLam k)
        (j + 1) haltCoordU
        (fun t ht => solMURepl_static_hdom_write w (j + 1) t ht)
        (solMURepl_static_hgZ_cont sol w)
        (solMURepl_static_hgZ0 sol w (j + 1))
        hmix_settled
        (hz_start (j + 1))
        hΛ_lower
    simpa [solMUReplSettledRho, selectorZWriteContraction] using hz
  have hread_z :
      selectorMUHaltReadError sol w (j + 1) ≤ δzH (j + 1) := by
    exact le_trans (by simpa [selectorMUHaltReadError, epsLam, gap, R0, Λ]
      using hz_read_raw) hδzH_bound
  exact ⟨hread_lam, hread_z⟩

/-- One-cycle induction step: `S_j → S_{j+1}`. -/
theorem selectorMU_cycle_step
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    {w : ℕ} {eps δzH : ℕ → ℝ} {j : ℕ}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (hoffStep : SelectorMUCycleHoffFieldIntegralStep sol w r_LE_U eps δzH)
    (herr : (gateSelectorAtomsCoordN (universalGateAtoms eta heta)).errSel < 1 / 2)
    (hκ₀_nonneg : 0 ≤ (κ₀ : ℝ))
    (hg₀ : 0 < (g₀ : ℝ))
    (hscale : (κ₀ : ℝ) ≤ ((3 / 4 : ℝ) ^ Mcy) * (g₀ : ℝ))
    (crMin crMax cgMin recoveryGap recoveryB : ℕ → ℝ)
    (recoveryK : ℕ → ℕ)
    (hN2 : 2 ≤ Fintype.card UniversalLocalView)
    (hcrMin_pos : ∀ k, 0 < crMin k)
    (hcrMin_le_crMax : ∀ k, crMin k ≤ crMax k)
    (hcgMin_nonneg : ∀ k, 0 ≤ cgMin k)
    (hrecoveryGap_nonneg : ∀ k, 0 ≤ recoveryGap k)
    (hrecoveryGap_le_gapVal : ∀ k, recoveryGap k ≤ selectorReplicatorGapVal eta heta)
    (hrecoveryB_eq : ∀ k, recoveryB k = cgMin k * recoveryGap k / 2 - crMax k)
    (hrecoveryB_pos : ∀ k, 0 < recoveryB k)
    (hrecoveryBDelta : ∀ k, (recoveryK k : ℝ) ≤
      recoveryB k * selectorMURecoveryDelta)
    (hpow : ∀ k, 1 + recoveryB k / crMin k ≤ (2 : ℝ) ^ recoveryK k)
    (hcr_bounds : ∀ k,
      ∀ u ∈ Icc (selectorMUWriteStartTime k) (selectorMUSelectStartTime k),
        crMin k ≤ ((1 + Real.cos u) / 2) ^ Mcy * (κ₀ : ℝ) ∧
          ((1 + Real.cos u) / 2) ^ Mcy * (κ₀ : ℝ) ≤ crMax k)
    (hcg_min : ∀ k,
      ∀ u ∈ Icc (selectorMUWriteStartTime k) (selectorMUSelectStartTime k),
        cgMin k ≤
          ((1 + Real.sin u) / 2) ^ Mcy *
            ((g₀ : ℝ) * Real.exp (bgpParams38.cα * u)))
    {Bz : ℕ → ℝ}
    (hz_start : ∀ k,
      |(sol w).z (selectorMUWriteHoldTime k) haltCoordU -
        stackMachineEncodingU.enc (solMUReplStaticCfg w (k + 1)) haltCoordU| ≤ Bz k)
    (heps_bound : ∀ k,
      epsLamShiftedFullAt sol w (selectorReplicatorGapVal eta heta)
          (Fintype.card UniversalLocalView : ℝ) (k + 1) ≤ eps (k + 1))
    (hδzH_bound : ∀ k,
      solMUReplSettledRho (fun n => selectorSettledWriteIntLower n) Bz
          (fun n => (Fintype.card UniversalLocalView : ℝ) *
            epsLamShiftedFullAt sol w (selectorReplicatorGapVal eta heta)
              (Fintype.card UniversalLocalView : ℝ) n)
          (k + 1) ≤ δzH (k + 1)) :
    (∀ k,
      SelectorMUCycleInvariant sol w r_LE_U eps δzH k →
      (selectorMUHaltEncConst (solMUReplStaticCfg w) k →
        ∀ t ∈ Icc (selectorMUInterReadStart k) (selectorMUNextWriteStart k),
          |(sol w).z t haltCoordU -
            (sol w).z (selectorMUInterReadStart k) haltCoordU| ≤
              selectorReplicatorHoldEnvelope k) →
      ∀ t ∈ Set.Ico (selectorMUWriteStartTime (k + 1))
          (selectorMUWriteReadTime (k + 1)),
        |(sol w).u t haltCoordU -
          stackMachineEncodingU.enc (solMUReplStaticCfg w (k + 1)) haltCoordU| ≤
            r_LE_U) →
    (∀ k,
      SelectorMUCycleInvariant sol w r_LE_U eps δzH k →
      (selectorMUHaltEncConst (solMUReplStaticCfg w) k →
        ∀ t ∈ Icc (selectorMUInterReadStart k) (selectorMUNextWriteStart k),
          |(sol w).z t haltCoordU -
            (sol w).z (selectorMUInterReadStart k) haltCoordU| ≤
              selectorReplicatorHoldEnvelope k) →
      ∀ i : Fin d_U, i ≠ haltCoordU →
        ∀ t ∈ Set.Ico (selectorMUWriteStartTime (k + 1))
            (selectorMUWriteReadTime (k + 1)),
          |(sol w).u t i -
            stackMachineEncodingU.enc (solMUReplStaticCfg w (k + 1)) i| ≤
              r_LE_U) →
      SelectorMUCycleInvariant sol w r_LE_U eps δzH j →
      SelectorMUCycleInvariant sol w r_LE_U eps δzH (j + 1) := by
  intro hucopyHalt hucopyStack Sj
  have hfreeze := selectorMU_cycle_freeze_substep_step
    (hoffStep := hoffStep) (Sj := Sj)
  have hu_next := selectorMU_cycle_ucopy_substep
    (hucopyHalt j Sj hfreeze) (hucopyStack j Sj hfreeze)
  have hrecovery :=
    selectorMU_cycle_recovery_substep
      (boxInputs := boxInputs) herr
      crMin crMax cgMin recoveryGap recoveryB recoveryK
      hN2 hcrMin_pos hcrMin_le_crMax hcgMin_nonneg
      hrecoveryGap_nonneg hrecoveryGap_le_gapVal hrecoveryB_eq
      hrecoveryB_pos hrecoveryBDelta hpow hcr_bounds hcg_min
      (Sj := Sj) hu_next
  have hwrite :=
    selectorMU_cycle_write_substep
      (boxInputs := boxInputs) herr hκ₀_nonneg hg₀ hscale
      (hz_start := hz_start)
      (heps_bound := heps_bound j)
      (hδzH_bound := hδzH_bound j)
      (Sj := Sj) hu_next hrecovery
  exact
    { hu_win := hu_next
      hlam_read := hwrite.1
      hz_halt := hwrite.2 }

/-- Induction over all cycles from `S_0`, using a cycle-local `hoff` producer. -/
theorem selectorMU_cycle_all_step
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    {w : ℕ} {eps δzH : ℕ → ℝ}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (hoffStep : SelectorMUCycleHoffFieldIntegralStep sol w r_LE_U eps δzH)
    (herr : (gateSelectorAtomsCoordN (universalGateAtoms eta heta)).errSel < 1 / 2)
    (hκ₀_nonneg : 0 ≤ (κ₀ : ℝ))
    (hg₀ : 0 < (g₀ : ℝ))
    (hscale : (κ₀ : ℝ) ≤ ((3 / 4 : ℝ) ^ Mcy) * (g₀ : ℝ))
    (crMin crMax cgMin recoveryGap recoveryB : ℕ → ℝ)
    (recoveryK : ℕ → ℕ)
    (hN2 : 2 ≤ Fintype.card UniversalLocalView)
    (hcrMin_pos : ∀ k, 0 < crMin k)
    (hcrMin_le_crMax : ∀ k, crMin k ≤ crMax k)
    (hcgMin_nonneg : ∀ k, 0 ≤ cgMin k)
    (hrecoveryGap_nonneg : ∀ k, 0 ≤ recoveryGap k)
    (hrecoveryGap_le_gapVal : ∀ k, recoveryGap k ≤ selectorReplicatorGapVal eta heta)
    (hrecoveryB_eq : ∀ k, recoveryB k = cgMin k * recoveryGap k / 2 - crMax k)
    (hrecoveryB_pos : ∀ k, 0 < recoveryB k)
    (hrecoveryBDelta : ∀ k, (recoveryK k : ℝ) ≤
      recoveryB k * selectorMURecoveryDelta)
    (hpow : ∀ k, 1 + recoveryB k / crMin k ≤ (2 : ℝ) ^ recoveryK k)
    (hcr_bounds : ∀ k,
      ∀ u ∈ Icc (selectorMUWriteStartTime k) (selectorMUSelectStartTime k),
        crMin k ≤ ((1 + Real.cos u) / 2) ^ Mcy * (κ₀ : ℝ) ∧
          ((1 + Real.cos u) / 2) ^ Mcy * (κ₀ : ℝ) ≤ crMax k)
    (hcg_min : ∀ k,
      ∀ u ∈ Icc (selectorMUWriteStartTime k) (selectorMUSelectStartTime k),
        cgMin k ≤
          ((1 + Real.sin u) / 2) ^ Mcy *
            ((g₀ : ℝ) * Real.exp (bgpParams38.cα * u)))
    {Bz : ℕ → ℝ}
    (hz_start : ∀ k,
      |(sol w).z (selectorMUWriteHoldTime k) haltCoordU -
        stackMachineEncodingU.enc (solMUReplStaticCfg w (k + 1)) haltCoordU| ≤ Bz k)
    (heps_bound : ∀ k,
      epsLamShiftedFullAt sol w (selectorReplicatorGapVal eta heta)
          (Fintype.card UniversalLocalView : ℝ) (k + 1) ≤ eps (k + 1))
    (hδzH_bound : ∀ k,
      solMUReplSettledRho (fun n => selectorSettledWriteIntLower n) Bz
          (fun n => (Fintype.card UniversalLocalView : ℝ) *
            epsLamShiftedFullAt sol w (selectorReplicatorGapVal eta heta)
              (Fintype.card UniversalLocalView : ℝ) n)
          (k + 1) ≤ δzH (k + 1))
    (hucopyHalt : ∀ k,
      SelectorMUCycleInvariant sol w r_LE_U eps δzH k →
      (selectorMUHaltEncConst (solMUReplStaticCfg w) k →
        ∀ t ∈ Icc (selectorMUInterReadStart k) (selectorMUNextWriteStart k),
          |(sol w).z t haltCoordU -
            (sol w).z (selectorMUInterReadStart k) haltCoordU| ≤
              selectorReplicatorHoldEnvelope k) →
      ∀ t ∈ Set.Ico (selectorMUWriteStartTime (k + 1))
          (selectorMUWriteReadTime (k + 1)),
        |(sol w).u t haltCoordU -
          stackMachineEncodingU.enc (solMUReplStaticCfg w (k + 1)) haltCoordU| ≤
            r_LE_U)
    (hucopyStack : ∀ k,
      SelectorMUCycleInvariant sol w r_LE_U eps δzH k →
      (selectorMUHaltEncConst (solMUReplStaticCfg w) k →
        ∀ t ∈ Icc (selectorMUInterReadStart k) (selectorMUNextWriteStart k),
          |(sol w).z t haltCoordU -
            (sol w).z (selectorMUInterReadStart k) haltCoordU| ≤
              selectorReplicatorHoldEnvelope k) →
      ∀ i : Fin d_U, i ≠ haltCoordU →
        ∀ t ∈ Set.Ico (selectorMUWriteStartTime (k + 1))
            (selectorMUWriteReadTime (k + 1)),
          |(sol w).u t i -
            stackMachineEncodingU.enc (solMUReplStaticCfg w (k + 1)) i| ≤
              r_LE_U)
    (h0 : SelectorMUCycleInvariant sol w r_LE_U eps δzH 0) :
    ∀ j : ℕ, SelectorMUCycleInvariant sol w r_LE_U eps δzH j := by
  intro j
  induction j with
  | zero =>
      exact h0
  | succ j ih =>
      exact
        selectorMU_cycle_step
          (boxInputs := boxInputs) (hoffStep := hoffStep)
          herr hκ₀_nonneg hg₀ hscale
          crMin crMax cgMin recoveryGap recoveryB recoveryK
          hN2 hcrMin_pos hcrMin_le_crMax hcgMin_nonneg
          hrecoveryGap_nonneg hrecoveryGap_le_gapVal hrecoveryB_eq
          hrecoveryB_pos hrecoveryBDelta hpow hcr_bounds hcg_min
          hz_start heps_bound hδzH_bound hucopyHalt hucopyStack ih

/-- Backward-compatible all-cycle induction wrapper for the old global `hoff`
residual interface. -/
theorem selectorMU_cycle_all
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    {w : ℕ} {eps δzH : ℕ → ℝ}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (hoffIntegral : SelectorMUCycleHoffFieldIntegralResidual sol)
    (herr : (gateSelectorAtomsCoordN (universalGateAtoms eta heta)).errSel < 1 / 2)
    (hκ₀_nonneg : 0 ≤ (κ₀ : ℝ))
    (hg₀ : 0 < (g₀ : ℝ))
    (hscale : (κ₀ : ℝ) ≤ ((3 / 4 : ℝ) ^ Mcy) * (g₀ : ℝ))
    (crMin crMax cgMin recoveryGap recoveryB : ℕ → ℝ)
    (recoveryK : ℕ → ℕ)
    (hN2 : 2 ≤ Fintype.card UniversalLocalView)
    (hcrMin_pos : ∀ k, 0 < crMin k)
    (hcrMin_le_crMax : ∀ k, crMin k ≤ crMax k)
    (hcgMin_nonneg : ∀ k, 0 ≤ cgMin k)
    (hrecoveryGap_nonneg : ∀ k, 0 ≤ recoveryGap k)
    (hrecoveryGap_le_gapVal : ∀ k, recoveryGap k ≤ selectorReplicatorGapVal eta heta)
    (hrecoveryB_eq : ∀ k, recoveryB k = cgMin k * recoveryGap k / 2 - crMax k)
    (hrecoveryB_pos : ∀ k, 0 < recoveryB k)
    (hrecoveryBDelta : ∀ k, (recoveryK k : ℝ) ≤
      recoveryB k * selectorMURecoveryDelta)
    (hpow : ∀ k, 1 + recoveryB k / crMin k ≤ (2 : ℝ) ^ recoveryK k)
    (hcr_bounds : ∀ k,
      ∀ u ∈ Icc (selectorMUWriteStartTime k) (selectorMUSelectStartTime k),
        crMin k ≤ ((1 + Real.cos u) / 2) ^ Mcy * (κ₀ : ℝ) ∧
          ((1 + Real.cos u) / 2) ^ Mcy * (κ₀ : ℝ) ≤ crMax k)
    (hcg_min : ∀ k,
      ∀ u ∈ Icc (selectorMUWriteStartTime k) (selectorMUSelectStartTime k),
        cgMin k ≤
          ((1 + Real.sin u) / 2) ^ Mcy *
            ((g₀ : ℝ) * Real.exp (bgpParams38.cα * u)))
    {Bz : ℕ → ℝ}
    (hz_start : ∀ k,
      |(sol w).z (selectorMUWriteHoldTime k) haltCoordU -
        stackMachineEncodingU.enc (solMUReplStaticCfg w (k + 1)) haltCoordU| ≤ Bz k)
    (heps_bound : ∀ k,
      epsLamShiftedFullAt sol w (selectorReplicatorGapVal eta heta)
          (Fintype.card UniversalLocalView : ℝ) (k + 1) ≤ eps (k + 1))
    (hδzH_bound : ∀ k,
      solMUReplSettledRho (fun n => selectorSettledWriteIntLower n) Bz
          (fun n => (Fintype.card UniversalLocalView : ℝ) *
            epsLamShiftedFullAt sol w (selectorReplicatorGapVal eta heta)
              (Fintype.card UniversalLocalView : ℝ) n)
          (k + 1) ≤ δzH (k + 1))
    (hucopyHalt : ∀ k,
      SelectorMUCycleInvariant sol w r_LE_U eps δzH k →
      (selectorMUHaltEncConst (solMUReplStaticCfg w) k →
        ∀ t ∈ Icc (selectorMUInterReadStart k) (selectorMUNextWriteStart k),
          |(sol w).z t haltCoordU -
            (sol w).z (selectorMUInterReadStart k) haltCoordU| ≤
              selectorReplicatorHoldEnvelope k) →
      ∀ t ∈ Set.Ico (selectorMUWriteStartTime (k + 1))
          (selectorMUWriteReadTime (k + 1)),
        |(sol w).u t haltCoordU -
          stackMachineEncodingU.enc (solMUReplStaticCfg w (k + 1)) haltCoordU| ≤
            r_LE_U)
    (hucopyStack : ∀ k,
      SelectorMUCycleInvariant sol w r_LE_U eps δzH k →
      (selectorMUHaltEncConst (solMUReplStaticCfg w) k →
        ∀ t ∈ Icc (selectorMUInterReadStart k) (selectorMUNextWriteStart k),
          |(sol w).z t haltCoordU -
            (sol w).z (selectorMUInterReadStart k) haltCoordU| ≤
              selectorReplicatorHoldEnvelope k) →
      ∀ i : Fin d_U, i ≠ haltCoordU →
        ∀ t ∈ Set.Ico (selectorMUWriteStartTime (k + 1))
            (selectorMUWriteReadTime (k + 1)),
          |(sol w).u t i -
            stackMachineEncodingU.enc (solMUReplStaticCfg w (k + 1)) i| ≤
              r_LE_U)
    (h0 : SelectorMUCycleInvariant sol w r_LE_U eps δzH 0) :
    ∀ j : ℕ, SelectorMUCycleInvariant sol w r_LE_U eps δzH j := by
  exact
    selectorMU_cycle_all_step
      (boxInputs := boxInputs)
      (hoffStep := hoffIntegral.toStep w r_LE_U eps δzH)
      herr hκ₀_nonneg hg₀ hscale
      crMin crMax cgMin recoveryGap recoveryB recoveryK
      hN2 hcrMin_pos hcrMin_le_crMax hcgMin_nonneg
      hrecoveryGap_nonneg hrecoveryGap_le_gapVal hrecoveryB_eq
      hrecoveryB_pos hrecoveryBDelta hpow hcr_bounds hcg_min
      hz_start heps_bound hδzH_bound hucopyHalt hucopyStack h0

/-- The fixed-`w` residual block whose fields match the non-numeric residual
inputs of `bgp_headline_warmGain_shifted_recovery`. -/
structure SelectorMUCycleResidualsAt
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀) (w : ℕ)
    (Bz : ℕ → ℝ) (Bzmax : ℝ) (δnext holdPrefix : ℕ → ℝ) : Prop where
  hutube_win : ∀ j, ∀ t ∈ Set.Ico (selectorMUWriteStartTime j)
      (selectorMUWriteReadTime j),
    UTube r_LE_U (solMUReplStaticCfg w j) ((sol w).u t)
  hBz_nonneg : ∀ j, 0 ≤ Bz j
  hBz_bdd : ∀ᶠ j in atTop, Bz j ≤ Bzmax
  hδnext : Tendsto δnext atTop (𝓝 0)
  hδnext_nonneg : ∀ j, 0 ≤ δnext j
  hholdPrefix_nonneg : ∀ j, 0 ≤ holdPrefix j
  p_hz_start : ∀ j,
    |(sol w).z (selectorMUWriteHoldTime j) haltCoordU -
      stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 1)) haltCoordU| ≤ Bz j
  p_hoff : ∀ j, selectorMUHaltEncConst (solMUReplStaticCfg w) j → ∀ t ∈
      Icc (selectorMUInterReadStart j) (selectorMUNextWriteStart j),
    |(sol w).z t haltCoordU -
      (sol w).z (selectorMUInterReadStart j) haltCoordU| ≤
        selectorReplicatorHoldEnvelope j
  p_hnextWrite : ∀ j, ∀ t ∈ Icc (selectorMUNextWriteStart j)
      (selectorMUNextRead j),
    |(sol w).z t haltCoordU -
      stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 2)) haltCoordU| ≤ δnext j
  p_hfiniteHold : ∀ j, ∀ t ∈ Icc (selectorMUInterReadStart j)
      (selectorMUNextRead j),
    |(sol w).z t haltCoordU -
      (sol w).z (selectorMUInterReadStart j) haltCoordU| ≤ holdPrefix j

private theorem selectorMU_abs_sub_le_one_of_unit_interval_pair {x y : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) :
    |x - y| ≤ (1 : ℝ) := by
  rw [abs_sub_le_iff]
  constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

private theorem selectorMU_enc_haltCoordU_mem_unit (c : UConf) :
    stackMachineEncodingU.enc c haltCoordU ∈ Icc (0 : ℝ) 1 := by
  change (confEncU c haltCoordU : ℝ) ∈ Icc (0 : ℝ) 1
  rw [confEncU_halt]
  unfold haltFlagU
  split <;> simp

private theorem selectorMU_halt_z_mem_Icc
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol) :
    ∀ w t, 0 ≤ t → (sol w).z t haltCoordU ∈ Icc (0 : ℝ) 1 := by
  intro w t ht
  have hzbox :=
    selector_replicator_flag_box_on_nonneg_repl (sol w)
      boxInputs.hcr_cont boxInputs.hcg_cont (boxInputs.hP_cont w)
      boxInputs.hcr_nonneg (boxInputs.hlam_sum0 w)
      (boxInputs.hlam_init_nonneg w) (boxInputs.hz0 w)
  exact ⟨hzbox.2 t ht, hzbox.1 t ht⟩

/-- Projection of the write-hold start residual needed by the shifted
constructor. -/
theorem selectorMU_cycle_p_hz_start_of_all
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    {w : ℕ} {eps δzH : ℕ → ℝ} {Bz : ℕ → ℝ}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (hBz_one : ∀ j, (1 : ℝ) ≤ Bz j)
    (hall : ∀ j, SelectorMUCycleInvariant sol w r_LE_U eps δzH j) :
    ∀ j,
      |(sol w).z (selectorMUWriteHoldTime j) haltCoordU -
        stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 1)) haltCoordU| ≤ Bz j := by
  intro j
  have _Sj := hall j
  have ht0 : 0 ≤ selectorMUWriteHoldTime j := by
    unfold selectorMUWriteHoldTime
    positivity
  exact le_trans
    (selectorMU_abs_sub_le_one_of_unit_interval_pair
      (selectorMU_halt_z_mem_Icc boxInputs w (selectorMUWriteHoldTime j) ht0)
      (selectorMU_enc_haltCoordU_mem_unit (solMUReplStaticCfg w (j + 1))))
    (hBz_one j)

/-- Projection of the next-write residual needed by the shifted constructor. -/
theorem selectorMU_cycle_p_hnextWrite_of_all
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    {w : ℕ} {eps δzH : ℕ → ℝ} {δnext : ℕ → ℝ}
    (hnextWrite : ∀ j, ∀ t ∈ Icc (selectorMUNextWriteStart j)
      (selectorMUNextRead j),
        |(sol w).z t haltCoordU -
          stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 2)) haltCoordU| ≤
            δnext j)
    (hall : ∀ j, SelectorMUCycleInvariant sol w r_LE_U eps δzH j) :
    ∀ j, ∀ t ∈ Icc (selectorMUNextWriteStart j) (selectorMUNextRead j),
      |(sol w).z t haltCoordU -
        stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 2)) haltCoordU| ≤ δnext j := by
  intro j t ht
  have _Sj_next := hall (j + 1)
  exact hnextWrite j t ht

/-- Projection of the finite inter-read self-hold residual. -/
theorem selectorMU_cycle_p_hfiniteHold_of_all
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    {w : ℕ} {eps δzH : ℕ → ℝ} {holdPrefix : ℕ → ℝ}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (hholdPrefix_one : ∀ j, (1 : ℝ) ≤ holdPrefix j)
    (hall : ∀ j, SelectorMUCycleInvariant sol w r_LE_U eps δzH j) :
    ∀ j, ∀ t ∈ Icc (selectorMUInterReadStart j) (selectorMUNextRead j),
      |(sol w).z t haltCoordU -
        (sol w).z (selectorMUInterReadStart j) haltCoordU| ≤ holdPrefix j := by
  intro j t ht
  have _Sj := hall j
  have ha0 : 0 ≤ selectorMUInterReadStart j := by
    unfold selectorMUInterReadStart selectorMUWriteReadTime
    positivity
  have ht0 : 0 ≤ t := le_trans ha0 ht.1
  exact le_trans
    (selectorMU_abs_sub_le_one_of_unit_interval_pair
      (selectorMU_halt_z_mem_Icc boxInputs w t ht0)
      (selectorMU_halt_z_mem_Icc boxInputs w (selectorMUInterReadStart j) ha0))
    (hholdPrefix_one j)

/-- Build the fixed-`w` residual bundle from all-cycle invariants, a cycle-local
`hoff` producer, and scalar radius side conditions. -/
theorem selectorMU_cycle_residuals_at_of_all_step
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    {w : ℕ} {eps δzH : ℕ → ℝ}
    {Bz : ℕ → ℝ} {Bzmax : ℝ} {δnext holdPrefix : ℕ → ℝ}
    (hall : ∀ j, SelectorMUCycleInvariant sol w r_LE_U eps δzH j)
    (hoffStep : SelectorMUCycleHoffFieldIntegralStep sol w r_LE_U eps δzH)
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (hBz_nonneg : ∀ j, 0 ≤ Bz j)
    (hBz_one : ∀ j, (1 : ℝ) ≤ Bz j)
    (hBz_bdd : ∀ᶠ j in atTop, Bz j ≤ Bzmax)
    (hδnext : Tendsto δnext atTop (𝓝 0))
    (hδnext_nonneg : ∀ j, 0 ≤ δnext j)
    (hnextWrite : ∀ j, ∀ t ∈ Icc (selectorMUNextWriteStart j)
      (selectorMUNextRead j),
        |(sol w).z t haltCoordU -
          stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 2)) haltCoordU| ≤
            δnext j)
    (hholdPrefix_nonneg : ∀ j, 0 ≤ holdPrefix j)
    (hholdPrefix_one : ∀ j, (1 : ℝ) ≤ holdPrefix j) :
    SelectorMUCycleResidualsAt sol w Bz Bzmax δnext holdPrefix where
  hutube_win := fun j => (hall j).hu_win
  hBz_nonneg := hBz_nonneg
  hBz_bdd := hBz_bdd
  hδnext := hδnext
  hδnext_nonneg := hδnext_nonneg
  hholdPrefix_nonneg := hholdPrefix_nonneg
  p_hz_start := selectorMU_cycle_p_hz_start_of_all
    (boxInputs := boxInputs) (hBz_one := hBz_one) (hall := hall)
  p_hoff := fun j =>
    selectorMU_cycle_freeze_substep_step (hoffStep := hoffStep) (Sj := hall j)
  p_hnextWrite := selectorMU_cycle_p_hnextWrite_of_all
    (hnextWrite := hnextWrite) (hall := hall)
  p_hfiniteHold := selectorMU_cycle_p_hfiniteHold_of_all
    (boxInputs := boxInputs) (hholdPrefix_one := hholdPrefix_one) (hall := hall)

/-- Backward-compatible residual-bundle wrapper for the old global `hoff`
residual interface. -/
theorem selectorMU_cycle_residuals_at_of_all
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    {w : ℕ} {eps δzH : ℕ → ℝ}
    {Bz : ℕ → ℝ} {Bzmax : ℝ} {δnext holdPrefix : ℕ → ℝ}
    (hall : ∀ j, SelectorMUCycleInvariant sol w r_LE_U eps δzH j)
    (hoffIntegral : SelectorMUCycleHoffFieldIntegralResidual sol)
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (hBz_nonneg : ∀ j, 0 ≤ Bz j)
    (hBz_one : ∀ j, (1 : ℝ) ≤ Bz j)
    (hBz_bdd : ∀ᶠ j in atTop, Bz j ≤ Bzmax)
    (hδnext : Tendsto δnext atTop (𝓝 0))
    (hδnext_nonneg : ∀ j, 0 ≤ δnext j)
    (hnextWrite : ∀ j, ∀ t ∈ Icc (selectorMUNextWriteStart j)
      (selectorMUNextRead j),
        |(sol w).z t haltCoordU -
          stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 2)) haltCoordU| ≤
            δnext j)
    (hholdPrefix_nonneg : ∀ j, 0 ≤ holdPrefix j)
    (hholdPrefix_one : ∀ j, (1 : ℝ) ≤ holdPrefix j) :
    SelectorMUCycleResidualsAt sol w Bz Bzmax δnext holdPrefix := by
  exact
    selectorMU_cycle_residuals_at_of_all_step
      (hall := hall)
      (hoffStep := hoffIntegral.toStep w r_LE_U eps δzH)
      (boxInputs := boxInputs)
      hBz_nonneg hBz_one hBz_bdd hδnext hδnext_nonneg
      hnextWrite hholdPrefix_nonneg hholdPrefix_one

/-- Feed the cycle residual bundle into the shifted late-start constructor.

This is the fixed-`w` wiring layer used by
`bgp_headline_warmGain_shifted_recovery`: the headline's family-level residual
arguments are obtained by applying this theorem on each diagonal `wg`. -/
def selectorMU_cycle_late_start_of_residuals
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    {w : ℕ}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (herr : (gateSelectorAtomsCoordN (universalGateAtoms eta heta)).errSel < 1 / 2)
    (hκ₀_nonneg : 0 ≤ (κ₀ : ℝ))
    (hg₀ : 0 < (g₀ : ℝ))
    (hscale : (κ₀ : ℝ) ≤ ((3 / 4 : ℝ) ^ Mcy) * (g₀ : ℝ))
    (crMin crMax cgMin recoveryGap recoveryB : ℕ → ℝ)
    (recoveryK : ℕ → ℕ)
    (hN2 : 2 ≤ Fintype.card UniversalLocalView)
    (hcrMin_pos : ∀ j, 0 < crMin j)
    (hcrMin_le_crMax : ∀ j, crMin j ≤ crMax j)
    (hcgMin_nonneg : ∀ j, 0 ≤ cgMin j)
    (hrecoveryGap_nonneg : ∀ j, 0 ≤ recoveryGap j)
    (hrecoveryGap_le_gapVal : ∀ j, recoveryGap j ≤ selectorReplicatorGapVal eta heta)
    (hrecoveryB_eq : ∀ j, recoveryB j = cgMin j * recoveryGap j / 2 - crMax j)
    (hrecoveryB_pos : ∀ j, 0 < recoveryB j)
    (hrecoveryBDelta : ∀ j, (recoveryK j : ℝ) ≤ recoveryB j * selectorMURecoveryDelta)
    (hpow : ∀ j, 1 + recoveryB j / crMin j ≤ (2 : ℝ) ^ recoveryK j)
    (hcr_bounds : ∀ j,
      ∀ u ∈ Icc (selectorMUWriteStartTime j) (selectorMUSelectStartTime j),
        crMin j ≤ ((1 + Real.cos u) / 2) ^ Mcy * (κ₀ : ℝ) ∧
          ((1 + Real.cos u) / 2) ^ Mcy * (κ₀ : ℝ) ≤ crMax j)
    (hcg_min : ∀ j,
      ∀ u ∈ Icc (selectorMUWriteStartTime j) (selectorMUSelectStartTime j),
        cgMin j ≤
          ((1 + Real.sin u) / 2) ^ Mcy *
            ((g₀ : ℝ) * Real.exp (bgpParams38.cα * u)))
    {Bz : ℕ → ℝ} {Bzmax : ℝ} {δnext holdPrefix : ℕ → ℝ}
    (res : SelectorMUCycleResidualsAt sol w Bz Bzmax δnext holdPrefix) :
    MUReplicatorLateStartHaltFactsAt sol w :=
  muReplicatorLateStartHaltFactsAt_shifted
    sol w boxInputs herr hκ₀_nonneg hg₀ hscale
    crMin crMax cgMin recoveryGap recoveryB recoveryK hN2
    hcrMin_pos hcrMin_le_crMax hcgMin_nonneg hrecoveryGap_nonneg
    hrecoveryGap_le_gapVal hrecoveryB_eq hrecoveryB_pos hrecoveryBDelta hpow
    hcr_bounds hcg_min
    res.hutube_win Bz Bzmax δnext holdPrefix
    res.hBz_nonneg res.hBz_bdd res.hδnext res.hδnext_nonneg
    res.hholdPrefix_nonneg res.p_hz_start res.p_hoff
    res.p_hnextWrite res.p_hfiniteHold

/-- Direct all-cycle-to-late-start wiring using a cycle-local `hoff` producer. -/
def selectorMU_cycle_late_start_of_all_step
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    {w : ℕ} {eps δzH : ℕ → ℝ}
    (hall : ∀ j, SelectorMUCycleInvariant sol w r_LE_U eps δzH j)
    (hoffStep : SelectorMUCycleHoffFieldIntegralStep sol w r_LE_U eps δzH)
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (herr : (gateSelectorAtomsCoordN (universalGateAtoms eta heta)).errSel < 1 / 2)
    (hκ₀_nonneg : 0 ≤ (κ₀ : ℝ))
    (hg₀ : 0 < (g₀ : ℝ))
    (hscale : (κ₀ : ℝ) ≤ ((3 / 4 : ℝ) ^ Mcy) * (g₀ : ℝ))
    (crMin crMax cgMin recoveryGap recoveryB : ℕ → ℝ)
    (recoveryK : ℕ → ℕ)
    (hN2 : 2 ≤ Fintype.card UniversalLocalView)
    (hcrMin_pos : ∀ j, 0 < crMin j)
    (hcrMin_le_crMax : ∀ j, crMin j ≤ crMax j)
    (hcgMin_nonneg : ∀ j, 0 ≤ cgMin j)
    (hrecoveryGap_nonneg : ∀ j, 0 ≤ recoveryGap j)
    (hrecoveryGap_le_gapVal : ∀ j, recoveryGap j ≤ selectorReplicatorGapVal eta heta)
    (hrecoveryB_eq : ∀ j, recoveryB j = cgMin j * recoveryGap j / 2 - crMax j)
    (hrecoveryB_pos : ∀ j, 0 < recoveryB j)
    (hrecoveryBDelta : ∀ j, (recoveryK j : ℝ) ≤ recoveryB j * selectorMURecoveryDelta)
    (hpow : ∀ j, 1 + recoveryB j / crMin j ≤ (2 : ℝ) ^ recoveryK j)
    (hcr_bounds : ∀ j,
      ∀ u ∈ Icc (selectorMUWriteStartTime j) (selectorMUSelectStartTime j),
        crMin j ≤ ((1 + Real.cos u) / 2) ^ Mcy * (κ₀ : ℝ) ∧
          ((1 + Real.cos u) / 2) ^ Mcy * (κ₀ : ℝ) ≤ crMax j)
    (hcg_min : ∀ j,
      ∀ u ∈ Icc (selectorMUWriteStartTime j) (selectorMUSelectStartTime j),
        cgMin j ≤
          ((1 + Real.sin u) / 2) ^ Mcy *
            ((g₀ : ℝ) * Real.exp (bgpParams38.cα * u)))
    {Bz : ℕ → ℝ} {Bzmax : ℝ} {δnext holdPrefix : ℕ → ℝ}
    (hBz_nonneg : ∀ j, 0 ≤ Bz j)
    (hBz_one : ∀ j, (1 : ℝ) ≤ Bz j)
    (hBz_bdd : ∀ᶠ j in atTop, Bz j ≤ Bzmax)
    (hδnext : Tendsto δnext atTop (𝓝 0))
    (hδnext_nonneg : ∀ j, 0 ≤ δnext j)
    (hnextWrite : ∀ j, ∀ t ∈ Icc (selectorMUNextWriteStart j)
      (selectorMUNextRead j),
        |(sol w).z t haltCoordU -
          stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 2)) haltCoordU| ≤
            δnext j)
    (hholdPrefix_nonneg : ∀ j, 0 ≤ holdPrefix j)
    (hholdPrefix_one : ∀ j, (1 : ℝ) ≤ holdPrefix j) :
    MUReplicatorLateStartHaltFactsAt sol w := by
  exact
    selectorMU_cycle_late_start_of_residuals
      (boxInputs := boxInputs) herr hκ₀_nonneg hg₀ hscale
      crMin crMax cgMin recoveryGap recoveryB recoveryK
      hN2 hcrMin_pos hcrMin_le_crMax hcgMin_nonneg
      hrecoveryGap_nonneg hrecoveryGap_le_gapVal hrecoveryB_eq
      hrecoveryB_pos hrecoveryBDelta hpow hcr_bounds hcg_min
      (selectorMU_cycle_residuals_at_of_all_step
        (hall := hall) (hoffStep := hoffStep) (boxInputs := boxInputs)
        hBz_nonneg hBz_one hBz_bdd hδnext hδnext_nonneg
        hnextWrite hholdPrefix_nonneg hholdPrefix_one)

/-- Backward-compatible all-cycle-to-late-start wiring for the old global `hoff`
residual interface. -/
def selectorMU_cycle_late_start_of_all
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    {w : ℕ} {eps δzH : ℕ → ℝ}
    (hall : ∀ j, SelectorMUCycleInvariant sol w r_LE_U eps δzH j)
    (hoffIntegral : SelectorMUCycleHoffFieldIntegralResidual sol)
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (herr : (gateSelectorAtomsCoordN (universalGateAtoms eta heta)).errSel < 1 / 2)
    (hκ₀_nonneg : 0 ≤ (κ₀ : ℝ))
    (hg₀ : 0 < (g₀ : ℝ))
    (hscale : (κ₀ : ℝ) ≤ ((3 / 4 : ℝ) ^ Mcy) * (g₀ : ℝ))
    (crMin crMax cgMin recoveryGap recoveryB : ℕ → ℝ)
    (recoveryK : ℕ → ℕ)
    (hN2 : 2 ≤ Fintype.card UniversalLocalView)
    (hcrMin_pos : ∀ j, 0 < crMin j)
    (hcrMin_le_crMax : ∀ j, crMin j ≤ crMax j)
    (hcgMin_nonneg : ∀ j, 0 ≤ cgMin j)
    (hrecoveryGap_nonneg : ∀ j, 0 ≤ recoveryGap j)
    (hrecoveryGap_le_gapVal : ∀ j, recoveryGap j ≤ selectorReplicatorGapVal eta heta)
    (hrecoveryB_eq : ∀ j, recoveryB j = cgMin j * recoveryGap j / 2 - crMax j)
    (hrecoveryB_pos : ∀ j, 0 < recoveryB j)
    (hrecoveryBDelta : ∀ j, (recoveryK j : ℝ) ≤ recoveryB j * selectorMURecoveryDelta)
    (hpow : ∀ j, 1 + recoveryB j / crMin j ≤ (2 : ℝ) ^ recoveryK j)
    (hcr_bounds : ∀ j,
      ∀ u ∈ Icc (selectorMUWriteStartTime j) (selectorMUSelectStartTime j),
        crMin j ≤ ((1 + Real.cos u) / 2) ^ Mcy * (κ₀ : ℝ) ∧
          ((1 + Real.cos u) / 2) ^ Mcy * (κ₀ : ℝ) ≤ crMax j)
    (hcg_min : ∀ j,
      ∀ u ∈ Icc (selectorMUWriteStartTime j) (selectorMUSelectStartTime j),
        cgMin j ≤
          ((1 + Real.sin u) / 2) ^ Mcy *
            ((g₀ : ℝ) * Real.exp (bgpParams38.cα * u)))
    {Bz : ℕ → ℝ} {Bzmax : ℝ} {δnext holdPrefix : ℕ → ℝ}
    (hBz_nonneg : ∀ j, 0 ≤ Bz j)
    (hBz_one : ∀ j, (1 : ℝ) ≤ Bz j)
    (hBz_bdd : ∀ᶠ j in atTop, Bz j ≤ Bzmax)
    (hδnext : Tendsto δnext atTop (𝓝 0))
    (hδnext_nonneg : ∀ j, 0 ≤ δnext j)
    (hnextWrite : ∀ j, ∀ t ∈ Icc (selectorMUNextWriteStart j)
      (selectorMUNextRead j),
        |(sol w).z t haltCoordU -
          stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 2)) haltCoordU| ≤
            δnext j)
    (hholdPrefix_nonneg : ∀ j, 0 ≤ holdPrefix j)
    (hholdPrefix_one : ∀ j, (1 : ℝ) ≤ holdPrefix j) :
    MUReplicatorLateStartHaltFactsAt sol w :=
  selectorMU_cycle_late_start_of_all_step
    (hall := hall)
    (hoffStep := hoffIntegral.toStep w r_LE_U eps δzH)
    (boxInputs := boxInputs)
    herr hκ₀_nonneg hg₀ hscale
    crMin crMax cgMin recoveryGap recoveryB recoveryK
    hN2 hcrMin_pos hcrMin_le_crMax hcgMin_nonneg
    hrecoveryGap_nonneg hrecoveryGap_le_gapVal hrecoveryB_eq
    hrecoveryB_pos hrecoveryBDelta hpow hcr_bounds hcg_min
    hBz_nonneg hBz_one hBz_bdd hδnext hδnext_nonneg
    hnextWrite hholdPrefix_nonneg hholdPrefix_one

end Ripple.BoundedUniversality.BGP
