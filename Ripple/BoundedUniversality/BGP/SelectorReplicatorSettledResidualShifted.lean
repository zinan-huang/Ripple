import Ripple.BoundedUniversality.BGP.SelectorReplicatorConc
import Ripple.BoundedUniversality.BGP.SelectorReplicatorDuhamel
import Ripple.BoundedUniversality.BGP.SelectorReplicatorSettledResidual
import Ripple.BoundedUniversality.BGP.MUReplicatorSettledConstructionShifted
import Ripple.BoundedUniversality.BGP.FlagHmixConstant
import Ripple.BoundedUniversality.BGP.SelectorDuhamelWrite

/-!
# Shifted settled residual adapters

Adapters from the shifted concentration package to the settled next-write
residual interfaces.  These deliberately avoid the older
`MUReplicatorSettledHaltConcentrationRateResiduals` surface, whose
`hqL_full` field is too strong for the shifted route.
-/

noncomputable section

namespace Ripple.BoundedUniversality.BGP

open MachineInstance UniversalMachine Filter Set
open scoped BigOperators Topology

private def shiftedEpsLam
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (shifted : ∀ w, MUReplicatorShiftedConcentrationAt sol w) :
    ℕ → ℕ → ℝ :=
  fun w j => (shifted w).epsLam j

private theorem shifted_p_hloser
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (shifted : ∀ w, MUReplicatorShiftedConcentrationAt sol w) :
    ∀ w j, ∀ t ∈ Icc (selectorMUWriteHoldTime j)
        (selectorMUWriteReadTime j),
      (Finset.univ.filter (fun v : UniversalLocalView =>
        v ≠ localViewU (solMUReplStaticCfg w j))).sum (fun v => (sol w).lam v t) ≤
          shiftedEpsLam shifted w j := by
  intro w j t ht
  exact (shifted w).p_hloser j t ht

private theorem abs_sub_le_one_of_unit_interval_pair {x y : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) :
    |x - y| ≤ (1 : ℝ) := by
  rw [abs_sub_le_iff]
  constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

private theorem branchU_halt_defect_nonneg_of_left_one
    {c v : UniversalLocalView} {u : Fin d_U → ℝ}
    (hc : BranchData.evalBranch (branchU c) u haltCoordU = 1) :
    0 ≤ BranchData.evalBranch (branchU c) u haltCoordU -
      BranchData.evalBranch (branchU v) u haltCoordU := by
  have hv_le_one : BranchData.evalBranch (branchU v) u haltCoordU ≤ 1 :=
    (branchU_halt_target_mem_Icc v u).2
  rw [hc]
  linarith

private theorem branchU_halt_defect_nonneg_of_right_zero
    {c v : UniversalLocalView} {u : Fin d_U → ℝ}
    (hc : BranchData.evalBranch (branchU c) u haltCoordU = 0) :
    0 ≤ BranchData.evalBranch (branchU v) u haltCoordU -
      BranchData.evalBranch (branchU c) u haltCoordU := by
  have hv_nonneg : 0 ≤ BranchData.evalBranch (branchU v) u haltCoordU :=
    (branchU_halt_target_mem_Icc v u).1
  rw [hc]
  simpa using hv_nonneg

private theorem selectorMUSelectStart_nonneg_weighted (j : ℕ) :
    0 ≤ selectorMUSelectStartTime j :=
  le_trans (selectorMUWriteStartTime_nonneg j)
    (selectorMUWriteStart_le_selectStart j)

private theorem lam_ratio_card_bound_at_weighted
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

/-- Box-only bound: halt-coordinate mix targets differ by at most one. -/
theorem halt_mixTarget_abs_sub_le_one
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (w : ℕ) {t s : ℝ} (ht0 : 0 ≤ t) (hs0 : 0 ≤ s) :
    |selectorMixTarget branchU (sol w).u (sol w).lam t haltCoordU -
      selectorMixTarget branchU (sol w).u (sol w).lam s haltCoordU| ≤ (1 : ℝ) := by
  exact abs_sub_le_one_of_unit_interval_pair
    (boxInputs.halt_mixTarget_mem_Icc w t ht0)
    (boxInputs.halt_mixTarget_mem_Icc w s hs0)

/-- Pointwise two-safe halt-mix bridge.

On a halt-constant edge the previous and next local views have the same
halt-coordinate branch target, so the halt-mix endpoint error only pays selector
mass outside those two views. -/
theorem selectorMUHoff_mix_pointwise_le_old_or_new_loser
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (w j : ℕ) {t M : ℝ} (ht0 : 0 ≤ t)
    (hM_old : stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 1)) haltCoordU = M)
    (hM_new : stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 2)) haltCoordU = M) :
    |selectorMixTarget branchU (sol w).u (sol w).lam t haltCoordU - M| ≤
      (Finset.univ.filter (fun v : UniversalLocalView =>
        v ≠ localViewU (solMUReplStaticCfg w j) ∧
          v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
            (fun v => (sol w).lam v t) := by
  classical
  let oldView : UniversalLocalView := localViewU (solMUReplStaticCfg w j)
  let newView : UniversalLocalView := localViewU (solMUReplStaticCfg w (j + 1))
  let safe : UniversalLocalView → Prop := fun v => v = oldView ∨ v = newView
  let bad : ℝ :=
    (Finset.univ.filter (fun v : UniversalLocalView =>
      v ≠ oldView ∧ v ≠ newView)).sum (fun v => (sol w).lam v t)
  have hsum_forward := solMURepl_static_lam_sum_forward (sol := sol) boxInputs
  have hlam_forward := solMURepl_static_lam_nonneg_forward (sol := sol) boxInputs
  have hsafe_target : ∀ v, safe v →
      BranchData.evalBranch (branchU v) ((sol w).u t) haltCoordU = M := by
    intro v hv
    rcases hv with hv | hv
    · subst hv
      have hbranch :=
        branchU_haltCoord_exact_independent (solMUReplStaticCfg w j)
          ((sol w).u t)
      simpa [oldView, hM_old, solMUReplStaticCfg_step w j] using hbranch
    · subst hv
      have hbranch :=
        branchU_haltCoord_exact_independent (solMUReplStaticCfg w (j + 1))
          ((sol w).u t)
      simpa [newView, hM_new, solMUReplStaticCfg_step w (j + 1),
        Nat.add_assoc] using hbranch
  have hold_target :
      BranchData.evalBranch (branchU oldView) ((sol w).u t) haltCoordU = M := by
    exact hsafe_target oldView (Or.inl rfl)
  have hspread : ∀ v,
      |BranchData.evalBranch (branchU v) ((sol w).u t) haltCoordU - M| ≤ (1 : ℝ) := by
    intro v
    simpa [hold_target] using
      branchU_haltCoord_spread_le_one v oldView ((sol w).u t)
  have hraw := selectorMixTarget_halt_to_const_of_safe_loser_sum
    (u := (sol w).u) (Λ := (sol w).lam) (t := t) (M := M)
    (safe := safe)
    (hsum_forward w t ht0)
    (fun v => hlam_forward w v t ht0)
    hsafe_target hspread
  simpa [bad, safe, oldView, newView, not_or] using hraw

/-- Hoff-weighted halt-mix integral controlled by the corresponding loser-mass
integral on any forward interval.

This is the reusable bridge needed for the cross-boundary Hoff estimates: the
dynamic work is reduced to proving an integral bound for wrong-view mass. -/
theorem selectorMUHoff_mix_integral_le_card_loser_integral
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (w n : ℕ) {a b M : ℝ}
    (hab : a ≤ b) (ha0 : 0 ≤ a)
    (hM : stackMachineEncodingU.enc (solMUReplStaticCfg w (n + 1)) haltCoordU = M) :
    (∫ τ in a..b, selectorMUHoffGateCoeff sol w τ *
      |selectorMixTarget branchU (sol w).u (sol w).lam τ haltCoordU - M|)
      ≤
    (∫ τ in a..b, selectorMUHoffGateCoeff sol w τ *
      (Finset.univ.filter (fun v : UniversalLocalView =>
        v ≠ localViewU (solMUReplStaticCfg w n))).sum
          (fun v => (sol w).lam v τ)) := by
  classical
  let k : ℝ → ℝ := fun τ => selectorMUHoffGateCoeff sol w τ
  let loser : ℝ → ℝ := fun τ =>
    (Finset.univ.filter (fun v : UniversalLocalView =>
      v ≠ localViewU (solMUReplStaticCfg w n))).sum
        (fun v => (sol w).lam v τ)
  have hsum_forward := solMURepl_static_lam_sum_forward (sol := sol) boxInputs
  have hlam_forward := solMURepl_static_lam_nonneg_forward (sol := sol) boxInputs
  have hk_cont : Continuous k := by
    dsimp [k, selectorMUHoffGateCoeff]
    exact selector_replicator_gateZ_integrand_continuous (sol w)
  have hm_cont : Continuous fun τ =>
      selectorMixTarget branchU (sol w).u (sol w).lam τ haltCoordU - M := by
    exact ((sol w).cont_mixTarget haltCoordU).sub continuous_const
  have hloser_cont : Continuous loser := by
    dsimp [loser]
    simpa using
      (continuous_finsetSum
        (Finset.univ.filter (fun v : UniversalLocalView =>
          v ≠ localViewU (solMUReplStaticCfg w n)))
        (fun v _hv => (sol w).cont_lam v))
  have hleft_int : IntervalIntegrable
      (fun τ => k τ *
        |selectorMixTarget branchU (sol w).u (sol w).lam τ haltCoordU - M|)
      MeasureTheory.volume a b := by
    exact (hk_cont.mul hm_cont.abs).intervalIntegrable a b
  have hright_int : IntervalIntegrable
      (fun τ => k τ * loser τ) MeasureTheory.volume a b := by
    exact (hk_cont.mul hloser_cont).intervalIntegrable a b
  apply intervalIntegral.integral_mono_on hab hleft_int hright_int
  intro τ hτ
  have hτ0 : 0 ≤ τ := le_trans ha0 hτ.1
  have hk_nonneg : 0 ≤ k τ := by
    dsimp [k, selectorMUHoffGateCoeff]
    exact selector_replicator_gateZ_integrand_nonneg (sol w)
      selectorSchedule_domain_of_nonneg_structural (by norm_num [bgpParams38]) hτ0
  have hmix :
      |selectorMixTarget branchU (sol w).u (sol w).lam τ haltCoordU - M| ≤
        loser τ := by
    have hraw := selectorMixTarget_halt_to_next_of_loser_sum_sharp
      (u := (sol w).u) (Λ := (sol w).lam) (t := τ)
      (c := solMUReplStaticCfg w n) (epsLam := loser τ)
      (hsum_forward w τ hτ0)
      (fun v => hlam_forward w v τ hτ0)
      (show
        (Finset.univ.filter (fun v : UniversalLocalView =>
          v ≠ localViewU (solMUReplStaticCfg w n))).sum
            (fun v => (sol w).lam v τ) ≤ loser τ from by
          rfl)
    simpa [hM, solMUReplStaticCfg_step w n] using hraw
  exact mul_le_mul_of_nonneg_left hmix hk_nonneg

/-- Hoff-weighted halt-mix integral controlled by the mass outside the two
halt-safe views `cfg j` and `cfg (j+1)`.

On a halt-constant cycle, both the previous local view and the next local view
produce the same halt-coordinate branch target.  Thus the cross-boundary Hoff
mix error only pays selector mass outside these two views. -/
theorem selectorMUHoff_mix_integral_le_old_or_new_loser_integral
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (w j : ℕ) {a b M : ℝ}
    (hab : a ≤ b) (ha0 : 0 ≤ a)
    (hM_old : stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 1)) haltCoordU = M)
    (hM_new : stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 2)) haltCoordU = M) :
    (∫ τ in a..b, selectorMUHoffGateCoeff sol w τ *
      |selectorMixTarget branchU (sol w).u (sol w).lam τ haltCoordU - M|)
      ≤
    (∫ τ in a..b, selectorMUHoffGateCoeff sol w τ *
      (Finset.univ.filter (fun v : UniversalLocalView =>
        v ≠ localViewU (solMUReplStaticCfg w j) ∧
          v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
            (fun v => (sol w).lam v τ)) := by
  classical
  let k : ℝ → ℝ := fun τ => selectorMUHoffGateCoeff sol w τ
  let oldView : UniversalLocalView := localViewU (solMUReplStaticCfg w j)
  let newView : UniversalLocalView := localViewU (solMUReplStaticCfg w (j + 1))
  let bad : ℝ → ℝ := fun τ =>
    (Finset.univ.filter (fun v : UniversalLocalView =>
      v ≠ oldView ∧ v ≠ newView)).sum (fun v => (sol w).lam v τ)
  have hsum_forward := solMURepl_static_lam_sum_forward (sol := sol) boxInputs
  have hlam_forward := solMURepl_static_lam_nonneg_forward (sol := sol) boxInputs
  have hk_cont : Continuous k := by
    dsimp [k, selectorMUHoffGateCoeff]
    exact selector_replicator_gateZ_integrand_continuous (sol w)
  have hm_cont : Continuous fun τ =>
      selectorMixTarget branchU (sol w).u (sol w).lam τ haltCoordU - M := by
    exact ((sol w).cont_mixTarget haltCoordU).sub continuous_const
  have hbad_cont : Continuous bad := by
    dsimp [bad]
    simpa using
      (continuous_finsetSum
        (Finset.univ.filter (fun v : UniversalLocalView =>
          v ≠ oldView ∧ v ≠ newView))
        (fun v _hv => (sol w).cont_lam v))
  have hleft_int : IntervalIntegrable
      (fun τ => k τ *
        |selectorMixTarget branchU (sol w).u (sol w).lam τ haltCoordU - M|)
      MeasureTheory.volume a b := by
    exact (hk_cont.mul hm_cont.abs).intervalIntegrable a b
  have hright_int : IntervalIntegrable (fun τ => k τ * bad τ)
      MeasureTheory.volume a b := by
    exact (hk_cont.mul hbad_cont).intervalIntegrable a b
  apply intervalIntegral.integral_mono_on hab hleft_int hright_int
  intro τ hτ
  have hτ0 : 0 ≤ τ := le_trans ha0 hτ.1
  have hk_nonneg : 0 ≤ k τ := by
    dsimp [k, selectorMUHoffGateCoeff]
    exact selector_replicator_gateZ_integrand_nonneg (sol w)
      selectorSchedule_domain_of_nonneg_structural (by norm_num [bgpParams38]) hτ0
  let safe : UniversalLocalView → Prop := fun v => v = oldView ∨ v = newView
  have hsafe_target : ∀ v, safe v →
      BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU = M := by
    intro v hv
    rcases hv with hv | hv
    · subst hv
      have hbranch :=
        branchU_haltCoord_exact_independent (solMUReplStaticCfg w j)
          ((sol w).u τ)
      simpa [oldView, hM_old, solMUReplStaticCfg_step w j] using hbranch
    · subst hv
      have hbranch :=
        branchU_haltCoord_exact_independent (solMUReplStaticCfg w (j + 1))
          ((sol w).u τ)
      simpa [newView, hM_new, solMUReplStaticCfg_step w (j + 1),
        Nat.add_assoc] using hbranch
  have hold_target :
      BranchData.evalBranch (branchU oldView) ((sol w).u τ) haltCoordU = M := by
    exact hsafe_target oldView (Or.inl rfl)
  have hspread : ∀ v,
      |BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU - M| ≤ (1 : ℝ) := by
    intro v
    simpa [hold_target] using
      branchU_haltCoord_spread_le_one v oldView ((sol w).u τ)
  have hmix :
      |selectorMixTarget branchU (sol w).u (sol w).lam τ haltCoordU - M| ≤
        bad τ := by
    have hraw := selectorMixTarget_halt_to_const_of_safe_loser_sum
      (u := (sol w).u) (Λ := (sol w).lam) (t := τ) (M := M)
      (safe := safe)
      (hsum_forward w τ hτ0)
      (fun v => hlam_forward w v τ hτ0)
      hsafe_target hspread
    simpa [bad, safe, oldView, newView, not_or] using hraw
  exact mul_le_mul_of_nonneg_left hmix hk_nonneg

/-- The right cross-boundary prefix is ordered before the early z-write
subwindow of the next cycle. -/
theorem selectorMUZOffEnd_le_earlyWriteSubStart_succ (j : ℕ) :
    selectorMUZOffEnd j ≤ selectorMUEarlyWriteSubStart (j + 1) := by
  unfold selectorMUZOffEnd selectorMUEarlyWriteSubStart
  push_cast
  linarith [Real.pi_pos]

/-- The right cross-boundary prefix starts before the next write window. -/
theorem selectorMUZOffEnd_le_writeStart_succ (j : ℕ) :
    selectorMUZOffEnd j ≤ selectorMUWriteStartTime (j + 1) := by
  unfold selectorMUZOffEnd selectorMUWriteStartTime
  push_cast
  linarith [Real.pi_pos]

/-- The prewrite prefix lies in the nonnegative sine half-period. -/
theorem selectorMU_sin_nonneg_prewrite (j : ℕ) {t : ℝ}
    (ht : t ∈ Icc (selectorMUZOffEnd j) (selectorMUWriteStartTime (j + 1))) :
    0 ≤ Real.sin t := by
  apply sin_window_nonneg (j + 1)
  · unfold selectorMUZOffEnd at ht
    push_cast at ht ⊢
    exact ht.1
  · have hupper := ht.2
    unfold selectorMUWriteStartTime at hupper
    push_cast at hupper ⊢
    linarith [Real.pi_pos]

/-- Schedule-only reset/gate ratio on the prewrite Hoff prefix.

On `[ZOffEnd j, WriteStart (j+1)]` we only have `sin t ≥ 0`, hence the
static scale hypothesis uses `(1/2)^M` rather than the write-window
`(3/4)^M`. -/
theorem solMURepl_static_hratio_bound_prewrite
    {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (hκ₀_nonneg : 0 ≤ (κ₀ : ℝ))
    (hg₀_nonneg : 0 ≤ (g₀ : ℝ))
    (hscale : (κ₀ : ℝ) ≤ ((1 / 2 : ℝ) ^ Mcy) * (g₀ : ℝ)) :
    ∀ (_ : ℕ) j, ∀ t ∈
      Icc (selectorMUZOffEnd j) (selectorMUWriteStartTime (j + 1)),
        (((1 + Real.cos t) / 2) ^ Mcy * (κ₀ : ℝ)) ≤
          (Real.exp (-(bgpParams38.cα * selectorMUZOffEnd j))) *
            (((1 + Real.sin t) / 2) ^ Mcy *
              ((g₀ : ℝ) * Real.exp (bgpParams38.cα * t))) := by
  intro _w j t ht
  have hcos_nonneg : 0 ≤ (1 + Real.cos t) / 2 := by
    nlinarith [Real.neg_one_le_cos t]
  have hcos_le_one : (1 + Real.cos t) / 2 ≤ 1 := by
    nlinarith [Real.cos_le_one t]
  have hcos_pow_le : ((1 + Real.cos t) / 2) ^ Mcy ≤ 1 := by
    simpa using pow_le_one₀ hcos_nonneg hcos_le_one
  have hlhs :
      (((1 + Real.cos t) / 2) ^ Mcy * (κ₀ : ℝ)) ≤ (κ₀ : ℝ) := by
    simpa using mul_le_mul_of_nonneg_right hcos_pow_le hκ₀_nonneg
  have hsin_nonneg : 0 ≤ Real.sin t :=
    selectorMU_sin_nonneg_prewrite j ht
  have hsin_base : (1 / 2 : ℝ) ≤ (1 + Real.sin t) / 2 := by
    linarith
  have hsin_pow :
      ((1 / 2 : ℝ) ^ Mcy) ≤ ((1 + Real.sin t) / 2) ^ Mcy := by
    exact pow_le_pow_left₀ (by norm_num) hsin_base Mcy
  have hgate_scale :
      ((1 / 2 : ℝ) ^ Mcy) * (g₀ : ℝ) ≤
        ((1 + Real.sin t) / 2) ^ Mcy * (g₀ : ℝ) := by
    exact mul_le_mul_of_nonneg_right hsin_pow hg₀_nonneg
  have ht_ge_start : selectorMUZOffEnd j ≤ t := ht.1
  have hclock_nonneg :
      0 ≤ bgpParams38.cα * (t - selectorMUZOffEnd j) := by
    have hcα : 0 ≤ bgpParams38.cα := by norm_num [bgpParams38]
    exact mul_nonneg hcα (sub_nonneg.mpr ht_ge_start)
  have hexp_one :
      1 ≤ Real.exp (bgpParams38.cα * (t - selectorMUZOffEnd j)) := by
    simpa using Real.one_le_exp_iff.mpr hclock_nonneg
  have hgate_nonneg :
      0 ≤ ((1 + Real.sin t) / 2) ^ Mcy * (g₀ : ℝ) :=
    mul_nonneg (pow_nonneg (le_trans (by norm_num : (0 : ℝ) ≤ 1 / 2) hsin_base) Mcy)
      hg₀_nonneg
  have hclock_mul :
      ((1 + Real.sin t) / 2) ^ Mcy * (g₀ : ℝ) ≤
        ((1 + Real.sin t) / 2) ^ Mcy * (g₀ : ℝ) *
          Real.exp (bgpParams38.cα * (t - selectorMUZOffEnd j)) := by
    simpa [mul_assoc] using mul_le_mul_of_nonneg_left hexp_one hgate_nonneg
  calc
    (((1 + Real.cos t) / 2) ^ Mcy * (κ₀ : ℝ)) ≤ (κ₀ : ℝ) := hlhs
    _ ≤ ((1 / 2 : ℝ) ^ Mcy) * (g₀ : ℝ) := hscale
    _ ≤ ((1 + Real.sin t) / 2) ^ Mcy * (g₀ : ℝ) := hgate_scale
    _ ≤ ((1 + Real.sin t) / 2) ^ Mcy * (g₀ : ℝ) *
          Real.exp (bgpParams38.cα * (t - selectorMUZOffEnd j)) := hclock_mul
    _ =
        Real.exp (-(bgpParams38.cα * selectorMUZOffEnd j)) *
          (((1 + Real.sin t) / 2) ^ Mcy *
            ((g₀ : ℝ) * Real.exp (bgpParams38.cα * t))) := by
          rw [show bgpParams38.cα * (t - selectorMUZOffEnd j) =
              bgpParams38.cα * t + -(bgpParams38.cα * selectorMUZOffEnd j) by ring,
            Real.exp_add]
          ring

/-- The shifted select-start lies before the early z-write subwindow. -/
theorem selectorMUSelectStart_le_earlySubStart (j : ℕ) :
    selectorMUSelectStartTime j ≤ selectorMUEarlyWriteSubStart j := by
  unfold selectorMUSelectStartTime selectorMUWriteStartTime
    selectorMUEarlyWriteSubStart selectorMURecoveryDelta
  nlinarith [Real.pi_gt_three]

/-- Mass outside `{old,new}` is bounded by the old-view loser mass. -/
theorem selectorMU_old_new_loser_mass_le_old_loser
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (w j : ℕ) (t : ℝ)
    (hlam_nonneg : ∀ v : UniversalLocalView, 0 ≤ (sol w).lam v t) :
    (Finset.univ.filter (fun v : UniversalLocalView =>
      v ≠ localViewU (solMUReplStaticCfg w j) ∧
        v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
          (fun v => (sol w).lam v t)
      ≤
    (Finset.univ.filter (fun v : UniversalLocalView =>
      v ≠ localViewU (solMUReplStaticCfg w j))).sum
          (fun v => (sol w).lam v t) := by
  classical
  refine Finset.sum_le_sum_of_subset_of_nonneg ?hsubset ?hnonneg
  · intro v hv
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ v, (Finset.mem_filter.mp hv).2.1⟩
  · intro v _hvold _hvbad
    exact hlam_nonneg v

/-- Mass outside `{old,new}` is bounded by the new-view loser mass. -/
theorem selectorMU_old_new_loser_mass_le_new_loser
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (w j : ℕ) (t : ℝ)
    (hlam_nonneg : ∀ v : UniversalLocalView, 0 ≤ (sol w).lam v t) :
    (Finset.univ.filter (fun v : UniversalLocalView =>
      v ≠ localViewU (solMUReplStaticCfg w j) ∧
        v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
          (fun v => (sol w).lam v t)
      ≤
    (Finset.univ.filter (fun v : UniversalLocalView =>
      v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
          (fun v => (sol w).lam v t) := by
  classical
  refine Finset.sum_le_sum_of_subset_of_nonneg ?hsubset ?hnonneg
  · intro v hv
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ v, (Finset.mem_filter.mp hv).2.2⟩
  · intro v _hvnew _hvbad
    exact hlam_nonneg v

/-- Mass outside `{old,new}` is bounded by the total selector mass. -/
theorem selectorMU_old_new_loser_mass_le_one
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (w j : ℕ) (t : ℝ)
    (hsum : (∑ v : UniversalLocalView, (sol w).lam v t) = 1)
    (hlam_nonneg : ∀ v : UniversalLocalView, 0 ≤ (sol w).lam v t) :
    (Finset.univ.filter (fun v : UniversalLocalView =>
      v ≠ localViewU (solMUReplStaticCfg w j) ∧
        v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
          (fun v => (sol w).lam v t)
      ≤ 1 := by
  classical
  calc
    (Finset.univ.filter (fun v : UniversalLocalView =>
      v ≠ localViewU (solMUReplStaticCfg w j) ∧
        v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
          (fun v => (sol w).lam v t)
        ≤ ∑ v : UniversalLocalView, (sol w).lam v t := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?hsubset ?hnonneg
          · intro v _hv
            exact Finset.mem_univ v
          · intro v _hvuniv _hvbad
            exact hlam_nonneg v
    _ = 1 := hsum

/-- Concrete old/new bad-mass differential inequality.

This is the `MUReplicatorSolFamily` instantiation of the generic aggregate
bad-mass ODE comparison, with the safe set `{cfg j, cfg (j+1)}`.  The real
mathematical inputs are kept explicit: a lower bound on the safe mass and a
pairwise payoff gap from every bad view to every safe view. -/
theorem selectorMU_old_new_badMass_hasDeriv_le_pairwise_safe_floor
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (hg₀_nonneg : 0 ≤ (g₀ : ℝ))
    (w j : ℕ) {t gap Lsafe : ℝ}
    (ht0 : 0 ≤ t)
    (hgap_nonneg : 0 ≤ gap) :
    Lsafe ≤
      (insert (localViewU (solMUReplStaticCfg w j))
        ({localViewU (solMUReplStaticCfg w (j + 1))} :
          Finset UniversalLocalView)).sum (fun u => (sol w).lam u t) →
    (∀ v : UniversalLocalView,
      v ∉ insert (localViewU (solMUReplStaticCfg w j))
        ({localViewU (solMUReplStaticCfg w (j + 1))} :
          Finset UniversalLocalView) →
      ∀ u : UniversalLocalView,
        u ∈ insert (localViewU (solMUReplStaticCfg w j))
          ({localViewU (solMUReplStaticCfg w (j + 1))} :
            Finset UniversalLocalView) →
        universalPval eta heta v ((sol w).u t) -
          universalPval eta heta u ((sol w).u t) ≤ -gap) →
    ∃ dB : ℝ,
      HasDerivAt
        (fun s : ℝ =>
          (Finset.univ.filter (fun v : UniversalLocalView =>
            v ∉ insert (localViewU (solMUReplStaticCfg w j))
              ({localViewU (solMUReplStaticCfg w (j + 1))} :
                Finset UniversalLocalView))).sum (fun v => (sol w).lam v s))
        dB t ∧
        dB ≤
          -(gap * Lsafe) *
              (((1 + Real.sin t) / 2) ^ Mcy *
                ((g₀ : ℝ) * Real.exp (bgpParams38.cα * t))) *
              (Finset.univ.filter (fun v : UniversalLocalView =>
                v ∉ insert (localViewU (solMUReplStaticCfg w j))
                  ({localViewU (solMUReplStaticCfg w (j + 1))} :
                    Finset UniversalLocalView))).sum (fun v => (sol w).lam v t)
            + (((1 + Real.cos t) / 2) ^ Mcy * (κ₀ : ℝ)) *
                (((Finset.univ.filter (fun v : UniversalLocalView =>
                  v ∉ insert (localViewU (solMUReplStaticCfg w j))
                    ({localViewU (solMUReplStaticCfg w (j + 1))} :
                      Finset UniversalLocalView))).card : ℝ) /
                  (Fintype.card UniversalLocalView : ℝ)) := by
  classical
  let safe : Finset UniversalLocalView :=
    insert (localViewU (solMUReplStaticCfg w j))
      ({localViewU (solMUReplStaticCfg w (j + 1))} : Finset UniversalLocalView)
  intro hsafe_floor hpair
  haveI : Nonempty UniversalLocalView := ⟨defaultLocalViewU⟩
  have hode : ∀ v : UniversalLocalView,
      HasDerivAt (fun s : ℝ => (sol w).lam v s)
        ((((1 + Real.cos t) / 2) ^ Mcy * (κ₀ : ℝ)) *
            (1 / (Fintype.card UniversalLocalView : ℝ) - (sol w).lam v t)
          + (((1 + Real.sin t) / 2) ^ Mcy *
              ((g₀ : ℝ) * Real.exp (bgpParams38.cα * t))) *
            (sol w).lam v t *
              (universalPval eta heta v ((sol w).u t)
                - ∑ u : UniversalLocalView,
                    (sol w).lam u t * universalPval eta heta u ((sol w).u t))) t := by
    intro v
    simpa [selectorSchedule] using
      (sol w).lam_hasDeriv v t (by simpa [selectorSchedule] using ht0)
  have hsum_forward := solMURepl_static_lam_sum_forward (sol := sol) boxInputs
  have hlam_forward := solMURepl_static_lam_nonneg_forward (sol := sol) boxInputs
  have hsin_base_nonneg : 0 ≤ (1 + Real.sin t) / 2 := by
    nlinarith [Real.neg_one_le_sin t]
  have hcg_nonneg :
      0 ≤ ((1 + Real.sin t) / 2) ^ Mcy *
        ((g₀ : ℝ) * Real.exp (bgpParams38.cα * t)) := by
    exact mul_nonneg (pow_nonneg hsin_base_nonneg Mcy)
      (mul_nonneg hg₀_nonneg (Real.exp_pos _).le)
  have hmain :=
    replicator_badMass_hasDeriv_le_pairwise_safe_floor
      (V := UniversalLocalView)
      (lam := fun v : UniversalLocalView => fun s : ℝ => (sol w).lam v s)
      (P := fun v : UniversalLocalView => fun s : ℝ =>
        universalPval eta heta v ((sol w).u s))
      (cr := fun s : ℝ => ((1 + Real.cos s) / 2) ^ Mcy * (κ₀ : ℝ))
      (cg := fun s : ℝ =>
        ((1 + Real.sin s) / 2) ^ Mcy *
          ((g₀ : ℝ) * Real.exp (bgpParams38.cα * s)))
      (safe := safe) (t := t) (gap := gap) (Lsafe := Lsafe)
      hode
      (hsum_forward w t ht0)
      (fun v => hlam_forward w v t ht0)
      (boxInputs.hcr_nonneg t)
      hcg_nonneg hgap_nonneg hsafe_floor hpair
  simpa [safe] using hmain

/-- Within-derivative form of
`selectorMU_old_new_badMass_hasDeriv_le_pairwise_safe_floor`, with the bad set
in the `v ≠ old ∧ v ≠ new` shape used by the Hoff edge integrals. -/
theorem selectorMU_old_new_badMass_hasDerivWithin_le_pairwise_safe_floor_on_Ico
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (hg₀_nonneg : 0 ≤ (g₀ : ℝ))
    (w j : ℕ) {a b gap Lsafe : ℝ}
    (hI_nonneg : ∀ t ∈ Icc a b, 0 ≤ t)
    (hgap_nonneg : 0 ≤ gap)
    (hsafe_floor : ∀ t ∈ Icc a b,
      Lsafe ≤
        (insert (localViewU (solMUReplStaticCfg w j))
          ({localViewU (solMUReplStaticCfg w (j + 1))} :
            Finset UniversalLocalView)).sum (fun u => (sol w).lam u t))
    (hpair : ∀ t ∈ Icc a b,
      ∀ v : UniversalLocalView,
        v ∉ insert (localViewU (solMUReplStaticCfg w j))
          ({localViewU (solMUReplStaticCfg w (j + 1))} :
            Finset UniversalLocalView) →
      ∀ u : UniversalLocalView,
        u ∈ insert (localViewU (solMUReplStaticCfg w j))
          ({localViewU (solMUReplStaticCfg w (j + 1))} :
            Finset UniversalLocalView) →
        universalPval eta heta v ((sol w).u t) -
          universalPval eta heta u ((sol w).u t) ≤ -gap) :
    ∀ t ∈ Ico a b,
      ∃ dB : ℝ,
        HasDerivWithinAt
          (fun s : ℝ =>
            (Finset.univ.filter (fun v : UniversalLocalView =>
              v ≠ localViewU (solMUReplStaticCfg w j) ∧
                v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
              (fun v => (sol w).lam v s))
          dB (Ici t) t ∧
          dB ≤
            -(gap * Lsafe) *
                (((1 + Real.sin t) / 2) ^ Mcy *
                  ((g₀ : ℝ) * Real.exp (bgpParams38.cα * t))) *
                (Finset.univ.filter (fun v : UniversalLocalView =>
                  v ≠ localViewU (solMUReplStaticCfg w j) ∧
                    v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
                  (fun v => (sol w).lam v t)
              + (((1 + Real.cos t) / 2) ^ Mcy * (κ₀ : ℝ)) *
                  (((Finset.univ.filter (fun v : UniversalLocalView =>
                    v ≠ localViewU (solMUReplStaticCfg w j) ∧
                      v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).card : ℝ) /
                    (Fintype.card UniversalLocalView : ℝ)) := by
  classical
  intro t ht
  let safe : Finset UniversalLocalView :=
    insert (localViewU (solMUReplStaticCfg w j))
      ({localViewU (solMUReplStaticCfg w (j + 1))} : Finset UniversalLocalView)
  let badNotMem : Finset UniversalLocalView :=
    Finset.univ.filter (fun v : UniversalLocalView => v ∉ safe)
  let badNe : Finset UniversalLocalView :=
    Finset.univ.filter (fun v : UniversalLocalView =>
      v ≠ localViewU (solMUReplStaticCfg w j) ∧
        v ≠ localViewU (solMUReplStaticCfg w (j + 1)))
  have htIcc : t ∈ Icc a b := Ico_subset_Icc_self ht
  have hbad_eq : badNotMem = badNe := by
    ext v
    simp [badNotMem, badNe, safe]
  have hpoint :=
    selectorMU_old_new_badMass_hasDeriv_le_pairwise_safe_floor
      (sol := sol) boxInputs hg₀_nonneg w j (hI_nonneg t htIcc)
      hgap_nonneg
      (by simpa [safe] using hsafe_floor t htIcc)
      (by
        intro v hv u hu
        exact hpair t htIcc v (by simpa [safe] using hv) u
          (by simpa [safe] using hu))
  rcases hpoint with ⟨dB, hder, hle⟩
  refine ⟨dB, ?_, ?_⟩
  · simpa [badNotMem, badNe, safe, hbad_eq] using hder.hasDerivWithinAt
  · simpa [badNotMem, badNe, safe, hbad_eq] using hle

/-- Duhamel bound for the concrete old/new bad mass under a safe-mass floor and
pairwise safe dominance on a forward interval. -/
theorem selectorMU_old_new_badMass_duhamel_bound_on_Icc
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (hg₀_nonneg : 0 ≤ (g₀ : ℝ))
    (w j : ℕ) {a b gap Lsafe : ℝ}
    (hab : a ≤ b)
    (hI_nonneg : ∀ t ∈ Icc a b, 0 ≤ t)
    (hgap_nonneg : 0 ≤ gap)
    (hgapL_pos : 0 < gap * Lsafe)
    (hsafe_floor : ∀ t ∈ Icc a b,
      Lsafe ≤
        (insert (localViewU (solMUReplStaticCfg w j))
          ({localViewU (solMUReplStaticCfg w (j + 1))} :
            Finset UniversalLocalView)).sum (fun u => (sol w).lam u t))
    (hpair : ∀ t ∈ Icc a b,
      ∀ v : UniversalLocalView,
        v ∉ insert (localViewU (solMUReplStaticCfg w j))
          ({localViewU (solMUReplStaticCfg w (j + 1))} :
            Finset UniversalLocalView) →
      ∀ u : UniversalLocalView,
        u ∈ insert (localViewU (solMUReplStaticCfg w j))
          ({localViewU (solMUReplStaticCfg w (j + 1))} :
            Finset UniversalLocalView) →
        universalPval eta heta v ((sol w).u t) -
          universalPval eta heta u ((sol w).u t) ≤ -gap) :
    ∀ t ∈ Icc a b,
      (Finset.univ.filter (fun v : UniversalLocalView =>
        v ≠ localViewU (solMUReplStaticCfg w j) ∧
          v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
          (fun v => (sol w).lam v t)
        ≤
      (Finset.univ.filter (fun v : UniversalLocalView =>
        v ≠ localViewU (solMUReplStaticCfg w j) ∧
          v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
          (fun v => (sol w).lam v a) *
          Real.exp (-((gap * Lsafe) * ((sol w).G t - (sol w).G a))) +
        (∫ s in a..t,
          Real.exp ((gap * Lsafe) * ((sol w).G s - (sol w).G a)) *
            (((1 + Real.cos s) / 2) ^ Mcy * (κ₀ : ℝ)) *
            ((((Finset.univ.filter (fun v : UniversalLocalView =>
              v ≠ localViewU (solMUReplStaticCfg w j) ∧
                v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).card : ℝ) /
              (Fintype.card UniversalLocalView : ℝ)))) *
          Real.exp (-((gap * Lsafe) * ((sol w).G t - (sol w).G a))) := by
  classical
  let bad : Finset UniversalLocalView :=
    Finset.univ.filter (fun v : UniversalLocalView =>
      v ≠ localViewU (solMUReplStaticCfg w j) ∧
        v ≠ localViewU (solMUReplStaticCfg w (j + 1)))
  let B : ℝ → ℝ := fun t => bad.sum (fun v => (sol w).lam v t)
  let cr : ℝ → ℝ := fun t => ((1 + Real.cos t) / 2) ^ Mcy * (κ₀ : ℝ)
  let cg : ℝ → ℝ := fun t =>
    ((1 + Real.sin t) / 2) ^ Mcy *
      ((g₀ : ℝ) * Real.exp (bgpParams38.cα * t))
  let Creset : ℝ := (bad.card : ℝ) / (Fintype.card UniversalLocalView : ℝ)
  have hB_cont : ContinuousOn B (Icc a b) := by
    dsimp [B, bad]
    exact
      (continuous_finsetSum
        (Finset.univ.filter (fun v : UniversalLocalView =>
          v ≠ localViewU (solMUReplStaticCfg w j) ∧
            v ≠ localViewU (solMUReplStaticCfg w (j + 1))))
        (fun v _hv => (sol w).cont_lam v)).continuousOn
  have hGder : ∀ t ∈ Ico a b,
      HasDerivWithinAt (sol w).G (cg t) (Ici t) t := by
    intro t ht
    have ht0 : 0 ≤ t := hI_nonneg t (Ico_subset_Icc_self ht)
    exact ((sol w).G_hasDeriv t
      (selectorSchedule_domain_of_nonneg_structural t ht0)).hasDerivWithinAt
  have hBder_le : ∀ t ∈ Ico a b,
      ∃ dB : ℝ,
        HasDerivWithinAt B dB (Ici t) t ∧
          dB ≤ -(gap * Lsafe) * cg t * B t + cr t * Creset := by
    intro t ht
    rcases selectorMU_old_new_badMass_hasDerivWithin_le_pairwise_safe_floor_on_Ico
        (sol := sol) boxInputs hg₀_nonneg w j hI_nonneg hgap_nonneg
        hsafe_floor hpair t ht with ⟨dB, hder, hle⟩
    exact ⟨dB, by simpa [B, bad] using hder, by simpa [B, bad, cr, cg, Creset] using hle⟩
  have hbound := badMass_scalar_duhamel_bound
    (B := B) (cr := cr) (cg := cg) (G := (sol w).G)
    (a := a) (b := b) (gap := gap * Lsafe) (Creset := Creset)
    hab hgapL_pos hB_cont (sol w).cont_G (by fun_prop) hGder hBder_le
  intro t ht
  simpa [B, bad, cr, cg, Creset] using hbound t ht

/-- Initial/source scalar corollary of
`selectorMU_old_new_badMass_duhamel_bound_on_Icc`.  The remaining hypotheses are
exactly the scalar estimates needed later for Hoff edge budgets. -/
theorem selectorMU_old_new_badMass_duhamel_bound_of_initial_source_on_Icc
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (hg₀_nonneg : 0 ≤ (g₀ : ℝ))
    (w j : ℕ) {a b gap Lsafe B0 K : ℝ}
    (hab : a ≤ b)
    (hI_nonneg : ∀ t ∈ Icc a b, 0 ≤ t)
    (hgap_nonneg : 0 ≤ gap)
    (hgapL_pos : 0 < gap * Lsafe)
    (hsafe_floor : ∀ t ∈ Icc a b,
      Lsafe ≤
        (insert (localViewU (solMUReplStaticCfg w j))
          ({localViewU (solMUReplStaticCfg w (j + 1))} :
            Finset UniversalLocalView)).sum (fun u => (sol w).lam u t))
    (hpair : ∀ t ∈ Icc a b,
      ∀ v : UniversalLocalView,
        v ∉ insert (localViewU (solMUReplStaticCfg w j))
          ({localViewU (solMUReplStaticCfg w (j + 1))} :
            Finset UniversalLocalView) →
      ∀ u : UniversalLocalView,
        u ∈ insert (localViewU (solMUReplStaticCfg w j))
          ({localViewU (solMUReplStaticCfg w (j + 1))} :
            Finset UniversalLocalView) →
        universalPval eta heta v ((sol w).u t) -
          universalPval eta heta u ((sol w).u t) ≤ -gap)
    (hBa :
      (Finset.univ.filter (fun v : UniversalLocalView =>
        v ≠ localViewU (solMUReplStaticCfg w j) ∧
          v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
          (fun v => (sol w).lam v a) ≤ B0)
    (hsource : ∀ t ∈ Icc a b,
      (∫ s in a..t,
        Real.exp ((gap * Lsafe) * ((sol w).G s - (sol w).G a)) *
          (((1 + Real.cos s) / 2) ^ Mcy * (κ₀ : ℝ)) *
          ((((Finset.univ.filter (fun v : UniversalLocalView =>
            v ≠ localViewU (solMUReplStaticCfg w j) ∧
              v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).card : ℝ) /
            (Fintype.card UniversalLocalView : ℝ)))) ≤ K) :
    ∀ t ∈ Icc a b,
      (Finset.univ.filter (fun v : UniversalLocalView =>
        v ≠ localViewU (solMUReplStaticCfg w j) ∧
          v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
          (fun v => (sol w).lam v t)
        ≤
      (B0 + K) *
        Real.exp (-((gap * Lsafe) * ((sol w).G t - (sol w).G a))) := by
  classical
  intro t ht
  have hduh :=
    selectorMU_old_new_badMass_duhamel_bound_on_Icc
      (sol := sol) boxInputs hg₀_nonneg w j hab hI_nonneg hgap_nonneg
      hgapL_pos hsafe_floor hpair t ht
  have hdecay_nonneg :
      0 ≤ Real.exp (-((gap * Lsafe) * ((sol w).G t - (sol w).G a))) :=
    (Real.exp_pos _).le
  calc
    (Finset.univ.filter (fun v : UniversalLocalView =>
      v ≠ localViewU (solMUReplStaticCfg w j) ∧
        v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
        (fun v => (sol w).lam v t)
        ≤
      (Finset.univ.filter (fun v : UniversalLocalView =>
        v ≠ localViewU (solMUReplStaticCfg w j) ∧
          v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
          (fun v => (sol w).lam v a) *
          Real.exp (-((gap * Lsafe) * ((sol w).G t - (sol w).G a))) +
        (∫ s in a..t,
          Real.exp ((gap * Lsafe) * ((sol w).G s - (sol w).G a)) *
            (((1 + Real.cos s) / 2) ^ Mcy * (κ₀ : ℝ)) *
            ((((Finset.univ.filter (fun v : UniversalLocalView =>
              v ≠ localViewU (solMUReplStaticCfg w j) ∧
                v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).card : ℝ) /
              (Fintype.card UniversalLocalView : ℝ)))) *
          Real.exp (-((gap * Lsafe) * ((sol w).G t - (sol w).G a))) := hduh
    _ ≤
      B0 * Real.exp (-((gap * Lsafe) * ((sol w).G t - (sol w).G a))) +
        K * Real.exp (-((gap * Lsafe) * ((sol w).G t - (sol w).G a))) := by
          exact add_le_add
            (mul_le_mul_of_nonneg_right hBa hdecay_nonneg)
            (mul_le_mul_of_nonneg_right (hsource t ht) hdecay_nonneg)
    _ =
      (B0 + K) *
        Real.exp (-((gap * Lsafe) * ((sol w).G t - (sol w).G a))) := by
          ring

/-- Duhamel source term bound for the concrete old/new bad-mass equation.

Once the reset coefficient is pointwise bounded by `Csrc * cg` on `[a,t]`,
the weighted reset integral times the terminal decay is bounded by
`Csrc / gapEff`.  This discharges the integrating-factor algebra and leaves
only the concrete schedule ratio as an explicit scalar condition. -/
theorem selectorMU_old_new_source_decay_le_of_reset_ratio
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀) (w : ℕ)
    {a t gapEff Creset Csrc : ℝ}
    (hat : a ≤ t)
    (hgapEff : 0 < gapEff)
    (hCsrc : 0 ≤ Csrc)
    (hκ₀_nonneg : 0 ≤ (κ₀ : ℝ))
    (hCreset_nonneg : 0 ≤ Creset)
    (ha_nonneg : 0 ≤ a)
    (hreset_bound : ∀ s ∈ Icc a t,
      (((1 + Real.cos s) / 2) ^ Mcy * (κ₀ : ℝ)) * Creset ≤
        Csrc * (((1 + Real.sin s) / 2) ^ Mcy *
          ((g₀ : ℝ) * Real.exp (bgpParams38.cα * s)))) :
    (∫ s in a..t,
        Real.exp (gapEff * ((sol w).G s - (sol w).G a)) *
          ((((1 + Real.cos s) / 2) ^ Mcy * (κ₀ : ℝ)) * Creset)) *
      Real.exp (-(gapEff * ((sol w).G t - (sol w).G a))) ≤ Csrc / gapEff := by
  let cg : ℝ → ℝ := fun s =>
    ((1 + Real.sin s) / 2) ^ Mcy *
      ((g₀ : ℝ) * Real.exp (bgpParams38.cα * s))
  let reset : ℝ → ℝ := fun s =>
    (((1 + Real.cos s) / 2) ^ Mcy * (κ₀ : ℝ)) * Creset
  have hGder : ∀ s ∈ Icc a t, HasDerivAt (sol w).G (cg s) s := by
    intro s hs
    exact (sol w).G_hasDeriv s
      (selectorSchedule_domain_of_nonneg_structural s
        (le_trans ha_nonneg hs.1))
  have hreset_nonneg : ∀ s ∈ Icc a t, 0 ≤ reset s := by
    intro s _hs
    dsimp [reset]
    exact mul_nonneg
      (mul_nonneg (pow_nonneg (by nlinarith [Real.neg_one_le_cos s]) Mcy)
        hκ₀_nonneg)
      hCreset_nonneg
  have hbound :=
    forward_reset_integral_mul_decay_le
      (a := a) (b := t) (gap := gapEff) (C := Csrc)
      (G := (sol w).G) (cg := cg) (reset := reset)
      hat hgapEff hCsrc (sol w).cont_G hGder
      (by dsimp [cg]; fun_prop)
      (by dsimp [reset]; fun_prop)
      hreset_nonneg
      (by
        intro s hs
        simpa [cg, reset] using hreset_bound s hs)
  simpa [cg, reset] using hbound.2

/-- Hoff-weighted old/new bad mass is bounded by the pure gate integral on any
forward interval.  This discharges only the simplex part; scalar decay of the
gate integral is a separate estimate. -/
theorem selectorMUHoff_old_new_loser_integral_le_gate_integral
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (w j : ℕ) {a b : ℝ} (hab : a ≤ b) (ha0 : 0 ≤ a) :
    (∫ τ in a..b, selectorMUHoffGateCoeff sol w τ *
      (Finset.univ.filter (fun v : UniversalLocalView =>
        v ≠ localViewU (solMUReplStaticCfg w j) ∧
          v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
            (fun v => (sol w).lam v τ))
      ≤
    (∫ τ in a..b, selectorMUHoffGateCoeff sol w τ) := by
  classical
  let k : ℝ → ℝ := fun τ => selectorMUHoffGateCoeff sol w τ
  let bad : ℝ → ℝ := fun τ =>
    (Finset.univ.filter (fun v : UniversalLocalView =>
      v ≠ localViewU (solMUReplStaticCfg w j) ∧
        v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
          (fun v => (sol w).lam v τ)
  have hsum_forward := solMURepl_static_lam_sum_forward (sol := sol) boxInputs
  have hlam_forward := solMURepl_static_lam_nonneg_forward (sol := sol) boxInputs
  have hk_cont : Continuous k := by
    dsimp [k, selectorMUHoffGateCoeff]
    exact selector_replicator_gateZ_integrand_continuous (sol w)
  have hbad_cont : Continuous bad := by
    dsimp [bad]
    simpa using
      (continuous_finsetSum
        (Finset.univ.filter (fun v : UniversalLocalView =>
          v ≠ localViewU (solMUReplStaticCfg w j) ∧
            v ≠ localViewU (solMUReplStaticCfg w (j + 1))))
        (fun v _hv => (sol w).cont_lam v))
  have hleft_int : IntervalIntegrable (fun τ => k τ * bad τ)
      MeasureTheory.volume a b := (hk_cont.mul hbad_cont).intervalIntegrable a b
  have hright_int : IntervalIntegrable k MeasureTheory.volume a b :=
    hk_cont.intervalIntegrable a b
  have hpoint : ∀ τ ∈ Icc a b, k τ * bad τ ≤ k τ := by
    intro τ hτ
    have hτ0 : 0 ≤ τ := le_trans ha0 hτ.1
    have hk_nonneg : 0 ≤ k τ := by
      dsimp [k, selectorMUHoffGateCoeff]
      exact selector_replicator_gateZ_integrand_nonneg (sol w)
        selectorSchedule_domain_of_nonneg_structural (by norm_num [bgpParams38]) hτ0
    have hbad_le_one : bad τ ≤ 1 := by
      dsimp [bad]
      exact selectorMU_old_new_loser_mass_le_one (sol := sol) w j τ
        (hsum_forward w τ hτ0)
        (fun v => hlam_forward w v τ hτ0)
    calc
      k τ * bad τ ≤ k τ * 1 :=
        mul_le_mul_of_nonneg_left hbad_le_one hk_nonneg
      _ = k τ := by ring
  simpa [k, bad] using
    intervalIntegral.integral_mono_on hab hleft_int hright_int hpoint

/-- The z-off-to-next-write part of the right cross-boundary old/new bad mass
pays no selector dynamics: simplex alone bounds it by the pure Hoff gate. -/
theorem selectorMUHoff_right_cross_prewrite_old_new_loser_integral_le_gate_integral
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (w j : ℕ) :
    (∫ τ in (selectorMUZOffEnd j)..(selectorMUWriteStartTime (j + 1)),
      selectorMUHoffGateCoeff sol w τ *
        (Finset.univ.filter (fun v : UniversalLocalView =>
          v ≠ localViewU (solMUReplStaticCfg w j) ∧
            v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
              (fun v => (sol w).lam v τ))
      ≤
    (∫ τ in (selectorMUZOffEnd j)..(selectorMUWriteStartTime (j + 1)),
      selectorMUHoffGateCoeff sol w τ) := by
  refine selectorMUHoff_old_new_loser_integral_le_gate_integral
    (sol := sol) boxInputs w j (selectorMUZOffEnd_le_writeStart_succ j) ?_
  unfold selectorMUZOffEnd
  positivity

/-- Pure simplex bound for the recovery prefix before the select-start floor.
This does not by itself close the Hoff scalar budget; it only isolates the
remaining scalar/dynamic estimate on `[WriteStart, SelectStart]`. -/
theorem selectorMUHoff_right_cross_recovery_old_new_loser_integral_le_gate_integral
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (w j : ℕ) :
    (∫ τ in (selectorMUWriteStartTime (j + 1))..
        (selectorMUSelectStartTime (j + 1)),
      selectorMUHoffGateCoeff sol w τ *
        (Finset.univ.filter (fun v : UniversalLocalView =>
          v ≠ localViewU (solMUReplStaticCfg w j) ∧
            v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
              (fun v => (sol w).lam v τ))
      ≤
    (∫ τ in (selectorMUWriteStartTime (j + 1))..
        (selectorMUSelectStartTime (j + 1)),
      selectorMUHoffGateCoeff sol w τ) := by
  refine selectorMUHoff_old_new_loser_integral_le_gate_integral
    (sol := sol) boxInputs w j (selectorMUWriteStart_le_selectStart (j + 1)) ?_
  exact selectorMUWriteStartTime_nonneg (j + 1)

/-- Hoff-weighted old/new bad mass is bounded by the old-view loser mass on any
forward interval.  This is useful on intervals where old-view concentration is
already available; it deliberately does not assert any new-view concentration. -/
theorem selectorMUHoff_old_new_loser_integral_le_old_loser_integral
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (w j : ℕ) {a b : ℝ} (hab : a ≤ b) (ha0 : 0 ≤ a) :
    (∫ τ in a..b, selectorMUHoffGateCoeff sol w τ *
      (Finset.univ.filter (fun v : UniversalLocalView =>
        v ≠ localViewU (solMUReplStaticCfg w j) ∧
          v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
            (fun v => (sol w).lam v τ))
      ≤
    (∫ τ in a..b, selectorMUHoffGateCoeff sol w τ *
      (Finset.univ.filter (fun v : UniversalLocalView =>
        v ≠ localViewU (solMUReplStaticCfg w j))).sum
            (fun v => (sol w).lam v τ)) := by
  classical
  let k : ℝ → ℝ := fun τ => selectorMUHoffGateCoeff sol w τ
  let bad : ℝ → ℝ := fun τ =>
    (Finset.univ.filter (fun v : UniversalLocalView =>
      v ≠ localViewU (solMUReplStaticCfg w j) ∧
        v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
          (fun v => (sol w).lam v τ)
  let oldLoser : ℝ → ℝ := fun τ =>
    (Finset.univ.filter (fun v : UniversalLocalView =>
      v ≠ localViewU (solMUReplStaticCfg w j))).sum
          (fun v => (sol w).lam v τ)
  have hlam_forward := solMURepl_static_lam_nonneg_forward (sol := sol) boxInputs
  have hk_cont : Continuous k := by
    dsimp [k, selectorMUHoffGateCoeff]
    exact selector_replicator_gateZ_integrand_continuous (sol w)
  have hbad_cont : Continuous bad := by
    dsimp [bad]
    simpa using
      (continuous_finsetSum
        (Finset.univ.filter (fun v : UniversalLocalView =>
          v ≠ localViewU (solMUReplStaticCfg w j) ∧
            v ≠ localViewU (solMUReplStaticCfg w (j + 1))))
        (fun v _hv => (sol w).cont_lam v))
  have hold_cont : Continuous oldLoser := by
    dsimp [oldLoser]
    simpa using
      (continuous_finsetSum
        (Finset.univ.filter (fun v : UniversalLocalView =>
          v ≠ localViewU (solMUReplStaticCfg w j)))
        (fun v _hv => (sol w).cont_lam v))
  have hleft_int : IntervalIntegrable (fun τ => k τ * bad τ)
      MeasureTheory.volume a b := (hk_cont.mul hbad_cont).intervalIntegrable a b
  have hright_int : IntervalIntegrable (fun τ => k τ * oldLoser τ)
      MeasureTheory.volume a b := (hk_cont.mul hold_cont).intervalIntegrable a b
  have hpoint : ∀ τ ∈ Icc a b, k τ * bad τ ≤ k τ * oldLoser τ := by
    intro τ hτ
    have hτ0 : 0 ≤ τ := le_trans ha0 hτ.1
    have hk_nonneg : 0 ≤ k τ := by
      dsimp [k, selectorMUHoffGateCoeff]
      exact selector_replicator_gateZ_integrand_nonneg (sol w)
        selectorSchedule_domain_of_nonneg_structural (by norm_num [bgpParams38]) hτ0
    exact mul_le_mul_of_nonneg_left
      (selectorMU_old_new_loser_mass_le_old_loser (sol := sol) w j τ
        (fun v => hlam_forward w v τ hτ0))
      hk_nonneg
  simpa [k, bad, oldLoser] using
    intervalIntegral.integral_mono_on hab hleft_int hright_int hpoint

/-- Hoff-weighted old/new bad mass is bounded by the new-view loser mass on any
forward interval.  This is the safe post-new-floor bridge; it does not assert
that the new-view loser mass is small on the recovery prefix. -/
theorem selectorMUHoff_old_new_loser_integral_le_new_loser_integral
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (w j : ℕ) {a b : ℝ} (hab : a ≤ b) (ha0 : 0 ≤ a) :
    (∫ τ in a..b, selectorMUHoffGateCoeff sol w τ *
      (Finset.univ.filter (fun v : UniversalLocalView =>
        v ≠ localViewU (solMUReplStaticCfg w j) ∧
          v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
            (fun v => (sol w).lam v τ))
      ≤
    (∫ τ in a..b, selectorMUHoffGateCoeff sol w τ *
      (Finset.univ.filter (fun v : UniversalLocalView =>
        v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
            (fun v => (sol w).lam v τ)) := by
  classical
  let k : ℝ → ℝ := fun τ => selectorMUHoffGateCoeff sol w τ
  let bad : ℝ → ℝ := fun τ =>
    (Finset.univ.filter (fun v : UniversalLocalView =>
      v ≠ localViewU (solMUReplStaticCfg w j) ∧
        v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
          (fun v => (sol w).lam v τ)
  let newLoser : ℝ → ℝ := fun τ =>
    (Finset.univ.filter (fun v : UniversalLocalView =>
      v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
          (fun v => (sol w).lam v τ)
  have hlam_forward := solMURepl_static_lam_nonneg_forward (sol := sol) boxInputs
  have hk_cont : Continuous k := by
    dsimp [k, selectorMUHoffGateCoeff]
    exact selector_replicator_gateZ_integrand_continuous (sol w)
  have hbad_cont : Continuous bad := by
    dsimp [bad]
    simpa using
      (continuous_finsetSum
        (Finset.univ.filter (fun v : UniversalLocalView =>
          v ≠ localViewU (solMUReplStaticCfg w j) ∧
            v ≠ localViewU (solMUReplStaticCfg w (j + 1))))
        (fun v _hv => (sol w).cont_lam v))
  have hnew_cont : Continuous newLoser := by
    dsimp [newLoser]
    simpa using
      (continuous_finsetSum
        (Finset.univ.filter (fun v : UniversalLocalView =>
          v ≠ localViewU (solMUReplStaticCfg w (j + 1))))
        (fun v _hv => (sol w).cont_lam v))
  have hleft_int : IntervalIntegrable (fun τ => k τ * bad τ)
      MeasureTheory.volume a b := (hk_cont.mul hbad_cont).intervalIntegrable a b
  have hright_int : IntervalIntegrable (fun τ => k τ * newLoser τ)
      MeasureTheory.volume a b := (hk_cont.mul hnew_cont).intervalIntegrable a b
  have hpoint : ∀ τ ∈ Icc a b, k τ * bad τ ≤ k τ * newLoser τ := by
    intro τ hτ
    have hτ0 : 0 ≤ τ := le_trans ha0 hτ.1
    have hk_nonneg : 0 ≤ k τ := by
      dsimp [k, selectorMUHoffGateCoeff]
      exact selector_replicator_gateZ_integrand_nonneg (sol w)
        selectorSchedule_domain_of_nonneg_structural (by norm_num [bgpParams38]) hτ0
    exact mul_le_mul_of_nonneg_left
      (selectorMU_old_new_loser_mass_le_new_loser (sol := sol) w j τ
        (fun v => hlam_forward w v τ hτ0))
      hk_nonneg
  simpa [k, bad, newLoser] using
    intervalIntegral.integral_mono_on hab hleft_int hright_int hpoint

/-- Split the right cross-boundary old/new bad-mass integral at the recovered
new-view floor time.  The post-select part may be bounded by ordinary
new-view loser mass; the pre-select part remains the genuine recovery-prefix
obligation. -/
theorem selectorMUHoff_right_cross_old_new_loser_integral_le_preselect_add_new_loser
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (w j : ℕ) :
    (∫ τ in (selectorMUZOffEnd j)..(selectorMUEarlyWriteSubStart (j + 1)),
      selectorMUHoffGateCoeff sol w τ *
        (Finset.univ.filter (fun v : UniversalLocalView =>
          v ≠ localViewU (solMUReplStaticCfg w j) ∧
            v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
              (fun v => (sol w).lam v τ))
      ≤
    (∫ τ in (selectorMUZOffEnd j)..(selectorMUSelectStartTime (j + 1)),
      selectorMUHoffGateCoeff sol w τ *
        (Finset.univ.filter (fun v : UniversalLocalView =>
          v ≠ localViewU (solMUReplStaticCfg w j) ∧
            v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
              (fun v => (sol w).lam v τ)) +
    (∫ τ in (selectorMUSelectStartTime (j + 1))..
        (selectorMUEarlyWriteSubStart (j + 1)),
      selectorMUHoffGateCoeff sol w τ *
        (Finset.univ.filter (fun v : UniversalLocalView =>
          v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
              (fun v => (sol w).lam v τ)) := by
  classical
  let Z : ℝ := selectorMUZOffEnd j
  let S : ℝ := selectorMUSelectStartTime (j + 1)
  let E : ℝ := selectorMUEarlyWriteSubStart (j + 1)
  let bad : ℝ → ℝ := fun τ =>
    selectorMUHoffGateCoeff sol w τ *
      (Finset.univ.filter (fun v : UniversalLocalView =>
        v ≠ localViewU (solMUReplStaticCfg w j) ∧
          v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
            (fun v => (sol w).lam v τ)
  let newLoser : ℝ → ℝ := fun τ =>
    selectorMUHoffGateCoeff sol w τ *
      (Finset.univ.filter (fun v : UniversalLocalView =>
        v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
          (fun v => (sol w).lam v τ)
  have hZE : Z ≤ E := by
    simpa [Z, E] using selectorMUZOffEnd_le_earlyWriteSubStart_succ j
  have hZS : Z ≤ S := by
    exact le_trans (by
      simpa [Z] using selectorMUZOffEnd_le_writeStart_succ j)
      (by simpa [S] using selectorMUWriteStart_le_selectStart (j + 1))
  have hSE : S ≤ E := by
    simpa [S, E] using selectorMUSelectStart_le_earlySubStart (j + 1)
  have hbad_cont : Continuous bad := by
    dsimp [bad]
    exact (selector_replicator_gateZ_integrand_continuous (sol w)).mul
      (by
        simpa using
          (continuous_finsetSum
            (Finset.univ.filter (fun v : UniversalLocalView =>
              v ≠ localViewU (solMUReplStaticCfg w j) ∧
                v ≠ localViewU (solMUReplStaticCfg w (j + 1))))
            (fun v _hv => (sol w).cont_lam v)))
  have hI : ∀ x y : ℝ, IntervalIntegrable bad MeasureTheory.volume x y :=
    fun x y => hbad_cont.intervalIntegrable x y
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hI Z S) (hI S E)
  have hpost :=
    selectorMUHoff_old_new_loser_integral_le_new_loser_integral
      (sol := sol) boxInputs w j hSE
      (by
        simpa [S] using selectorMUSelectStart_nonneg_weighted (j + 1))
  have hpost' : (∫ τ in S..E, bad τ) ≤ (∫ τ in S..E, newLoser τ) := by
    simpa [S, E, bad, newLoser] using hpost
  calc
    (∫ τ in (selectorMUZOffEnd j)..(selectorMUEarlyWriteSubStart (j + 1)),
      selectorMUHoffGateCoeff sol w τ *
        (Finset.univ.filter (fun v : UniversalLocalView =>
          v ≠ localViewU (solMUReplStaticCfg w j) ∧
            v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
              (fun v => (sol w).lam v τ))
        = ∫ τ in Z..E, bad τ := by
          simp [Z, E, bad]
    _ = (∫ τ in Z..S, bad τ) + (∫ τ in S..E, bad τ) := hsplit.symm
    _ ≤ (∫ τ in Z..S, bad τ) + (∫ τ in S..E, newLoser τ) := by
          exact add_le_add le_rfl hpost'
    _ =
      (∫ τ in (selectorMUZOffEnd j)..(selectorMUSelectStartTime (j + 1)),
        selectorMUHoffGateCoeff sol w τ *
          (Finset.univ.filter (fun v : UniversalLocalView =>
            v ≠ localViewU (solMUReplStaticCfg w j) ∧
              v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
                (fun v => (sol w).lam v τ)) +
      (∫ τ in (selectorMUSelectStartTime (j + 1))..
          (selectorMUEarlyWriteSubStart (j + 1)),
        selectorMUHoffGateCoeff sol w τ *
          (Finset.univ.filter (fun v : UniversalLocalView =>
            v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
                (fun v => (sol w).lam v τ)) := by
          simp [Z, S, E, bad, newLoser]

/-- Finer split of the right cross-boundary old/new bad-mass integral.

The post-select part is still paid by the ordinary new-view loser mass.  The
remaining genuine scalar obligations are the z-off-to-write-start prefix and
the next recovery prefix before the select-start floor is available. -/
theorem selectorMUHoff_right_cross_old_new_loser_integral_le_prewrite_add_recovery_add_new_loser
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (w j : ℕ) :
    (∫ τ in (selectorMUZOffEnd j)..(selectorMUEarlyWriteSubStart (j + 1)),
      selectorMUHoffGateCoeff sol w τ *
        (Finset.univ.filter (fun v : UniversalLocalView =>
          v ≠ localViewU (solMUReplStaticCfg w j) ∧
            v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
              (fun v => (sol w).lam v τ))
      ≤
    (∫ τ in (selectorMUZOffEnd j)..(selectorMUWriteStartTime (j + 1)),
      selectorMUHoffGateCoeff sol w τ *
        (Finset.univ.filter (fun v : UniversalLocalView =>
          v ≠ localViewU (solMUReplStaticCfg w j) ∧
            v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
              (fun v => (sol w).lam v τ)) +
    (∫ τ in (selectorMUWriteStartTime (j + 1))..
        (selectorMUSelectStartTime (j + 1)),
      selectorMUHoffGateCoeff sol w τ *
        (Finset.univ.filter (fun v : UniversalLocalView =>
          v ≠ localViewU (solMUReplStaticCfg w j) ∧
            v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
              (fun v => (sol w).lam v τ)) +
    (∫ τ in (selectorMUSelectStartTime (j + 1))..
        (selectorMUEarlyWriteSubStart (j + 1)),
      selectorMUHoffGateCoeff sol w τ *
        (Finset.univ.filter (fun v : UniversalLocalView =>
          v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
              (fun v => (sol w).lam v τ)) := by
  classical
  let Z : ℝ := selectorMUZOffEnd j
  let W : ℝ := selectorMUWriteStartTime (j + 1)
  let S : ℝ := selectorMUSelectStartTime (j + 1)
  let E : ℝ := selectorMUEarlyWriteSubStart (j + 1)
  let bad : ℝ → ℝ := fun τ =>
    selectorMUHoffGateCoeff sol w τ *
      (Finset.univ.filter (fun v : UniversalLocalView =>
        v ≠ localViewU (solMUReplStaticCfg w j) ∧
          v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
            (fun v => (sol w).lam v τ)
  let newLoser : ℝ → ℝ := fun τ =>
    selectorMUHoffGateCoeff sol w τ *
      (Finset.univ.filter (fun v : UniversalLocalView =>
        v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
          (fun v => (sol w).lam v τ)
  have hZW : Z ≤ W := by
    simpa [Z, W] using selectorMUZOffEnd_le_writeStart_succ j
  have hWS : W ≤ S := by
    simpa [W, S] using selectorMUWriteStart_le_selectStart (j + 1)
  have hbad_cont : Continuous bad := by
    dsimp [bad]
    exact (selector_replicator_gateZ_integrand_continuous (sol w)).mul
      (by
        simpa using
          (continuous_finsetSum
            (Finset.univ.filter (fun v : UniversalLocalView =>
              v ≠ localViewU (solMUReplStaticCfg w j) ∧
                v ≠ localViewU (solMUReplStaticCfg w (j + 1))))
            (fun v _hv => (sol w).cont_lam v)))
  have hI : ∀ x y : ℝ, IntervalIntegrable bad MeasureTheory.volume x y :=
    fun x y => hbad_cont.intervalIntegrable x y
  have hpre_split :
      (∫ τ in Z..S, bad τ) = (∫ τ in Z..W, bad τ) + (∫ τ in W..S, bad τ) := by
    exact (intervalIntegral.integral_add_adjacent_intervals (hI Z W) (hI W S)).symm
  have hbase :=
    selectorMUHoff_right_cross_old_new_loser_integral_le_preselect_add_new_loser
      (sol := sol) boxInputs w j
  calc
    (∫ τ in (selectorMUZOffEnd j)..(selectorMUEarlyWriteSubStart (j + 1)),
      selectorMUHoffGateCoeff sol w τ *
        (Finset.univ.filter (fun v : UniversalLocalView =>
          v ≠ localViewU (solMUReplStaticCfg w j) ∧
            v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
              (fun v => (sol w).lam v τ))
        ≤
      (∫ τ in Z..S, bad τ) + (∫ τ in S..E, newLoser τ) := by
        simpa [Z, S, E, bad, newLoser] using hbase
    _ = ((∫ τ in Z..W, bad τ) + (∫ τ in W..S, bad τ)) +
        (∫ τ in S..E, newLoser τ) := by
          rw [hpre_split]
    _ =
      (∫ τ in (selectorMUZOffEnd j)..(selectorMUWriteStartTime (j + 1)),
        selectorMUHoffGateCoeff sol w τ *
          (Finset.univ.filter (fun v : UniversalLocalView =>
            v ≠ localViewU (solMUReplStaticCfg w j) ∧
              v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
                (fun v => (sol w).lam v τ)) +
      (∫ τ in (selectorMUWriteStartTime (j + 1))..
          (selectorMUSelectStartTime (j + 1)),
        selectorMUHoffGateCoeff sol w τ *
          (Finset.univ.filter (fun v : UniversalLocalView =>
            v ≠ localViewU (solMUReplStaticCfg w j) ∧
              v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
                (fun v => (sol w).lam v τ)) +
      (∫ τ in (selectorMUSelectStartTime (j + 1))..
          (selectorMUEarlyWriteSubStart (j + 1)),
        selectorMUHoffGateCoeff sol w τ *
          (Finset.univ.filter (fun v : UniversalLocalView =>
            v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
                (fun v => (sol w).lam v τ)) := by
          simp [Z, W, S, E, bad, newLoser]

/-- Right cross-boundary old/new bad mass reduced to pure gate integrals before
the recovered floor and ordinary new-view loser mass after the floor. -/
theorem selectorMUHoff_right_cross_old_new_loser_integral_le_prefix_gates_add_new_loser
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (w j : ℕ) :
    (∫ τ in (selectorMUZOffEnd j)..(selectorMUEarlyWriteSubStart (j + 1)),
      selectorMUHoffGateCoeff sol w τ *
        (Finset.univ.filter (fun v : UniversalLocalView =>
          v ≠ localViewU (solMUReplStaticCfg w j) ∧
            v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
              (fun v => (sol w).lam v τ))
      ≤
    (∫ τ in (selectorMUZOffEnd j)..(selectorMUWriteStartTime (j + 1)),
      selectorMUHoffGateCoeff sol w τ) +
    (∫ τ in (selectorMUWriteStartTime (j + 1))..
        (selectorMUSelectStartTime (j + 1)),
      selectorMUHoffGateCoeff sol w τ) +
    (∫ τ in (selectorMUSelectStartTime (j + 1))..
        (selectorMUEarlyWriteSubStart (j + 1)),
      selectorMUHoffGateCoeff sol w τ *
        (Finset.univ.filter (fun v : UniversalLocalView =>
          v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
              (fun v => (sol w).lam v τ)) := by
  have hsplit :=
    selectorMUHoff_right_cross_old_new_loser_integral_le_prewrite_add_recovery_add_new_loser
      (sol := sol) boxInputs w j
  have hpre :=
    selectorMUHoff_right_cross_prewrite_old_new_loser_integral_le_gate_integral
      (sol := sol) boxInputs w j
  have hrec :=
    selectorMUHoff_right_cross_recovery_old_new_loser_integral_le_gate_integral
      (sol := sol) boxInputs w j
  nlinarith [hsplit, hpre, hrec]

/-- The post-write-start part of the right cross-boundary old/new bad mass is
bounded by the recovery gate plus the new-view loser mass after the select
floor. -/
theorem selectorMUHoff_right_cross_writeStart_old_new_loser_integral_le_recovery_add_new_loser
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (w j : ℕ) :
    (∫ τ in (selectorMUWriteStartTime (j + 1))..
        (selectorMUEarlyWriteSubStart (j + 1)),
      selectorMUHoffGateCoeff sol w τ *
        (Finset.univ.filter (fun v : UniversalLocalView =>
          v ≠ localViewU (solMUReplStaticCfg w j) ∧
            v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
              (fun v => (sol w).lam v τ))
      ≤
    (∫ τ in (selectorMUWriteStartTime (j + 1))..
        (selectorMUSelectStartTime (j + 1)),
      selectorMUHoffGateCoeff sol w τ) +
    (∫ τ in (selectorMUSelectStartTime (j + 1))..
        (selectorMUEarlyWriteSubStart (j + 1)),
      selectorMUHoffGateCoeff sol w τ *
        (Finset.univ.filter (fun v : UniversalLocalView =>
          v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
            (fun v => (sol w).lam v τ)) := by
  classical
  let W : ℝ := selectorMUWriteStartTime (j + 1)
  let S : ℝ := selectorMUSelectStartTime (j + 1)
  let E : ℝ := selectorMUEarlyWriteSubStart (j + 1)
  let bad : ℝ → ℝ := fun τ =>
    selectorMUHoffGateCoeff sol w τ *
      (Finset.univ.filter (fun v : UniversalLocalView =>
        v ≠ localViewU (solMUReplStaticCfg w j) ∧
          v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
            (fun v => (sol w).lam v τ)
  let newLoser : ℝ → ℝ := fun τ =>
    selectorMUHoffGateCoeff sol w τ *
      (Finset.univ.filter (fun v : UniversalLocalView =>
        v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
          (fun v => (sol w).lam v τ)
  have hWS : W ≤ S := by
    simpa [W, S] using selectorMUWriteStart_le_selectStart (j + 1)
  have hSE : S ≤ E := by
    simpa [S, E] using selectorMUSelectStart_le_earlySubStart (j + 1)
  have hbad_cont : Continuous bad := by
    dsimp [bad]
    exact (selector_replicator_gateZ_integrand_continuous (sol w)).mul
      (by
        simpa using
          (continuous_finsetSum
            (Finset.univ.filter (fun v : UniversalLocalView =>
              v ≠ localViewU (solMUReplStaticCfg w j) ∧
                v ≠ localViewU (solMUReplStaticCfg w (j + 1))))
            (fun v _hv => (sol w).cont_lam v)))
  have hI : ∀ x y : ℝ, IntervalIntegrable bad MeasureTheory.volume x y :=
    fun x y => hbad_cont.intervalIntegrable x y
  have hsplit :
      (∫ τ in W..E, bad τ) = (∫ τ in W..S, bad τ) + (∫ τ in S..E, bad τ) :=
    (intervalIntegral.integral_add_adjacent_intervals (hI W S) (hI S E)).symm
  have hrec :=
    selectorMUHoff_right_cross_recovery_old_new_loser_integral_le_gate_integral
      (sol := sol) boxInputs w j
  have hpost :=
    selectorMUHoff_old_new_loser_integral_le_new_loser_integral
      (sol := sol) boxInputs w j hSE
      (by
        simpa [S] using selectorMUSelectStart_nonneg_weighted (j + 1))
  calc
    (∫ τ in (selectorMUWriteStartTime (j + 1))..
        (selectorMUEarlyWriteSubStart (j + 1)),
      selectorMUHoffGateCoeff sol w τ *
        (Finset.univ.filter (fun v : UniversalLocalView =>
          v ≠ localViewU (solMUReplStaticCfg w j) ∧
            v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
              (fun v => (sol w).lam v τ))
        = ∫ τ in W..E, bad τ := by
          simp [W, E, bad]
    _ = (∫ τ in W..S, bad τ) + (∫ τ in S..E, bad τ) := hsplit
    _ ≤
      (∫ τ in (selectorMUWriteStartTime (j + 1))..
          (selectorMUSelectStartTime (j + 1)),
        selectorMUHoffGateCoeff sol w τ) +
      (∫ τ in (selectorMUSelectStartTime (j + 1))..
          (selectorMUEarlyWriteSubStart (j + 1)),
        selectorMUHoffGateCoeff sol w τ *
          (Finset.univ.filter (fun v : UniversalLocalView =>
            v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
              (fun v => (sol w).lam v τ)) := by
        exact add_le_add
          (by simpa [W, S, bad] using hrec)
          (by simpa [S, E, bad, newLoser] using hpost)

/-- Concrete two-safe halt-mix bridge on the right cross-boundary Hoff prefix.

After a halt, the previous local view and the next local view have the same
halt-coordinate target.  Therefore this prefix only pays selector mass outside
those two views. -/
theorem selectorMUHoff_right_cross_mix_integral_le_old_or_new_loser_integral
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (w j : ℕ)
    (henc : selectorMUHaltEncConstW solMUReplStaticCfg w j) :
    (∫ τ in (selectorMUZOffEnd j)..(selectorMUEarlyWriteSubStart (j + 1)),
      selectorMUHoffGateCoeff sol w τ *
        |selectorMixTarget branchU (sol w).u (sol w).lam τ haltCoordU -
          stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 1)) haltCoordU|)
      ≤
    (∫ τ in (selectorMUZOffEnd j)..(selectorMUEarlyWriteSubStart (j + 1)),
      selectorMUHoffGateCoeff sol w τ *
        (Finset.univ.filter (fun v : UniversalLocalView =>
          v ≠ localViewU (solMUReplStaticCfg w j) ∧
            v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
              (fun v => (sol w).lam v τ)) := by
  refine
    selectorMUHoff_mix_integral_le_old_or_new_loser_integral
      (sol := sol) boxInputs w j
      (a := selectorMUZOffEnd j)
      (b := selectorMUEarlyWriteSubStart (j + 1))
      (M := stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 1)) haltCoordU)
      (selectorMUZOffEnd_le_earlyWriteSubStart_succ j)
      ?_ rfl ?_
  · unfold selectorMUZOffEnd
    positivity
  · simpa [selectorMUHaltEncConstW, selectorMUHaltEncConst] using henc

/-- Concrete two-safe halt-mix bridge on the prewrite Hoff prefix.

This keeps the genuinely hard prewrite quantity as selector bad mass rather
than replacing it by the pure gate integral. -/
theorem selectorMUHoff_right_prewrite_mix_integral_le_old_or_new_loser_integral
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (w j : ℕ)
    (henc : selectorMUHaltEncConstW solMUReplStaticCfg w j) :
    (∫ τ in (selectorMUZOffEnd j)..(selectorMUWriteStartTime (j + 1)),
      selectorMUHoffGateCoeff sol w τ *
        |selectorMixTarget branchU (sol w).u (sol w).lam τ haltCoordU -
          stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 1)) haltCoordU|)
      ≤
    (∫ τ in (selectorMUZOffEnd j)..(selectorMUWriteStartTime (j + 1)),
      selectorMUHoffGateCoeff sol w τ *
        (Finset.univ.filter (fun v : UniversalLocalView =>
          v ≠ localViewU (solMUReplStaticCfg w j) ∧
            v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
              (fun v => (sol w).lam v τ)) := by
  refine
    selectorMUHoff_mix_integral_le_old_or_new_loser_integral
      (sol := sol) boxInputs w j
      (a := selectorMUZOffEnd j)
      (b := selectorMUWriteStartTime (j + 1))
      (M := stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 1)) haltCoordU)
      (selectorMUZOffEnd_le_writeStart_succ j)
      ?_ rfl ?_
  · unfold selectorMUZOffEnd
    positivity
  · simpa [selectorMUHaltEncConstW, selectorMUHaltEncConst] using henc

/-- Concrete two-safe halt-mix bridge on the left Hoff edge. -/
theorem selectorMUHoff_left_mix_integral_le_old_or_new_loser_integral
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (w j : ℕ)
    (henc : selectorMUHaltEncConstW solMUReplStaticCfg w j) :
    (∫ τ in (selectorMUInterReadStart j)..(selectorMUZOffStart j),
      selectorMUHoffGateCoeff sol w τ *
        |selectorMixTarget branchU (sol w).u (sol w).lam τ haltCoordU -
          stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 1)) haltCoordU|)
      ≤
    (∫ τ in (selectorMUInterReadStart j)..(selectorMUZOffStart j),
      selectorMUHoffGateCoeff sol w τ *
        (Finset.univ.filter (fun v : UniversalLocalView =>
          v ≠ localViewU (solMUReplStaticCfg w j) ∧
            v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
              (fun v => (sol w).lam v τ)) := by
  refine
    selectorMUHoff_mix_integral_le_old_or_new_loser_integral
      (sol := sol) boxInputs w j
      (a := selectorMUInterReadStart j)
      (b := selectorMUZOffStart j)
      (M := stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 1)) haltCoordU)
      (selectorMUInterReadStart_le_zOffStart j)
      ?_ rfl ?_
  · unfold selectorMUInterReadStart selectorMUWriteReadTime
    positivity
  · simpa [selectorMUHaltEncConstW, selectorMUHaltEncConst] using henc

/-- Left actual Hoff cap reduced to the read-start endpoint error and the
two-safe bad-mass integral. -/
theorem selectorMUHoffCapLeftField_le_initial_add_old_new_loser_integral
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (w j : ℕ)
    (henc : selectorMUHaltEncConstW solMUReplStaticCfg w j) :
    selectorMUHoffCapLeftField sol w j ≤
      |(sol w).z (selectorMUInterReadStart j) haltCoordU -
        stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 1)) haltCoordU| +
        2 *
          (∫ τ in (selectorMUInterReadStart j)..(selectorMUZOffStart j),
            selectorMUHoffGateCoeff sol w τ *
              (Finset.univ.filter (fun v : UniversalLocalView =>
                v ≠ localViewU (solMUReplStaticCfg w j) ∧
                  v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
                    (fun v => (sol w).lam v τ)) := by
  let M : ℝ := stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 1)) haltCoordU
  have hcap := selectorMUHoffCapLeftField_le_initial_add_target
    (sol := sol) w j M
  have hmix := selectorMUHoff_left_mix_integral_le_old_or_new_loser_integral
    (sol := sol) boxInputs w j henc
  have hmixM :
      (∫ τ in (selectorMUInterReadStart j)..(selectorMUZOffStart j),
        selectorMUHoffGateCoeff sol w τ *
          |selectorMixTarget branchU (sol w).u (sol w).lam τ haltCoordU - M|)
      ≤
      (∫ τ in (selectorMUInterReadStart j)..(selectorMUZOffStart j),
        selectorMUHoffGateCoeff sol w τ *
          (Finset.univ.filter (fun v : UniversalLocalView =>
            v ≠ localViewU (solMUReplStaticCfg w j) ∧
              v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
                (fun v => (sol w).lam v τ)) := by
    simpa [M] using hmix
  calc
    selectorMUHoffCapLeftField sol w j
        ≤ |(sol w).z (selectorMUInterReadStart j) haltCoordU - M| +
            2 * (∫ τ in (selectorMUInterReadStart j)..(selectorMUZOffStart j),
              selectorMUHoffGateCoeff sol w τ *
                |selectorMixTarget branchU (sol w).u (sol w).lam τ haltCoordU - M|) :=
          hcap
    _ ≤ |(sol w).z (selectorMUInterReadStart j) haltCoordU - M| +
          2 *
            (∫ τ in (selectorMUInterReadStart j)..(selectorMUZOffStart j),
              selectorMUHoffGateCoeff sol w τ *
                (Finset.univ.filter (fun v : UniversalLocalView =>
                  v ≠ localViewU (solMUReplStaticCfg w j) ∧
                    v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
                      (fun v => (sol w).lam v τ)) := by
        exact add_le_add le_rfl
          (mul_le_mul_of_nonneg_left hmixM (by norm_num : (0 : ℝ) ≤ 2))

/-- Right cross-boundary actual Hoff field cap up to the early active-write
subwindow, reduced to the z-off endpoint error and two-safe bad mass. -/
theorem selectorMUHoff_right_cross_field_integral_le_initial_add_old_new_loser
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (w j : ℕ)
    (henc : selectorMUHaltEncConstW solMUReplStaticCfg w j) :
    (∫ τ in (selectorMUZOffEnd j)..(selectorMUEarlyWriteSubStart (j + 1)),
      selectorMUHoffIntegrand sol w τ) ≤
      |(sol w).z (selectorMUZOffEnd j) haltCoordU -
        stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 1)) haltCoordU| +
        2 *
          (∫ τ in (selectorMUZOffEnd j)..(selectorMUEarlyWriteSubStart (j + 1)),
            selectorMUHoffGateCoeff sol w τ *
              (Finset.univ.filter (fun v : UniversalLocalView =>
                v ≠ localViewU (solMUReplStaticCfg w j) ∧
                  v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
                    (fun v => (sol w).lam v τ)) := by
  let a : ℝ := selectorMUZOffEnd j
  let b : ℝ := selectorMUEarlyWriteSubStart (j + 1)
  let M : ℝ := stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 1)) haltCoordU
  let y : ℝ → ℝ := fun τ => (sol w).z τ haltCoordU
  let m : ℝ → ℝ := fun τ =>
    selectorMixTarget branchU (sol w).u (sol w).lam τ haltCoordU
  let k : ℝ → ℝ := fun τ => selectorMUHoffGateCoeff sol w τ
  have hab : a ≤ b := by
    simpa [a, b] using selectorMUZOffEnd_le_earlyWriteSubStart_succ j
  have hk_cont : Continuous k := by
    simpa [k, selectorMUHoffGateCoeff] using
      selector_replicator_gateZ_integrand_continuous (sol w)
  have hm_cont : Continuous m := by
    simpa [m] using (sol w).cont_mixTarget haltCoordU
  have hy_cont : Continuous y := by
    simpa [y] using (sol w).cont_z haltCoordU
  have ha0 : 0 ≤ a := by
    simp [a, selectorMUZOffEnd]
    positivity
  have hk_nonneg : ∀ τ ∈ Set.Icc a b, 0 ≤ k τ := by
    intro τ hτ
    have hτ0 : 0 ≤ τ := le_trans ha0 hτ.1
    simpa [k, selectorMUHoffGateCoeff] using
      selector_replicator_gateZ_integrand_nonneg (sol w)
        selectorSchedule_domain_of_nonneg_structural (by norm_num [bgpParams38]) hτ0
  have hy_ode : ∀ τ ∈ Set.Icc a b,
      HasDerivAt y (k τ * (m τ - y τ)) τ := by
    intro τ hτ
    have hτ0 : 0 ≤ τ := le_trans ha0 hτ.1
    simpa [y, m, k, selectorMUHoffGateCoeff] using
      (sol w).z_hasDeriv τ (selectorSchedule_domain_of_nonneg_structural τ hτ0)
        haltCoordU
  have herrorInt :
      (∫ τ in a..b, k τ * |y τ - M|) ≤
        |y a - M| + (∫ τ in a..b, k τ * |m τ - M|) := by
    have h := stack_write_error_integral_le_initial_add_target
      y m k M a b hab hk_cont hk_nonneg hy_cont hm_cont hy_ode
    simpa [a, b, y, m, k] using h
  have hscalar := stack_write_field_cap_bound_of_error_integral
    y m k M a b hab hk_cont hk_nonneg hy_cont hm_cont herrorInt
  have hcap_le :
      (∫ τ in a..b, selectorMUHoffIntegrand sol w τ) ≤
        ∫ τ in a..b, k τ * |m τ - y τ| := by
    have hleft_int : IntervalIntegrable
        (fun τ => selectorMUHoffIntegrand sol w τ) MeasureTheory.volume a b := by
      exact (selectorMUHoffIntegrand_continuous (sol := sol) w).intervalIntegrable a b
    have hright_int : IntervalIntegrable (fun τ => k τ * |m τ - y τ|)
        MeasureTheory.volume a b := by
      exact (hk_cont.mul ((hm_cont.sub hy_cont).abs)).intervalIntegrable a b
    apply intervalIntegral.integral_mono_on hab hleft_int hright_int
    intro τ hτ
    have hk0 : 0 ≤ k τ := hk_nonneg τ hτ
    calc
      selectorMUHoffIntegrand sol w τ
          = |k τ * (m τ - y τ)| := by
            simp [selectorMUHoffIntegrand, selectorMUHoffGateCoeff, k, m, y]
      _ = k τ * |m τ - y τ| := by
            rw [abs_mul, abs_of_nonneg hk0]
      _ ≤ k τ * |m τ - y τ| := le_rfl
  have hfield :
      (∫ τ in a..b, selectorMUHoffIntegrand sol w τ) ≤
        |y a - M| + 2 * (∫ τ in a..b, k τ * |m τ - M|) :=
    le_trans hcap_le hscalar
  have hmix :=
    selectorMUHoff_right_cross_mix_integral_le_old_or_new_loser_integral
      (sol := sol) boxInputs w j henc
  have hmixM :
      (∫ τ in a..b, k τ * |m τ - M|) ≤
      (∫ τ in (selectorMUZOffEnd j)..(selectorMUEarlyWriteSubStart (j + 1)),
        selectorMUHoffGateCoeff sol w τ *
          (Finset.univ.filter (fun v : UniversalLocalView =>
            v ≠ localViewU (solMUReplStaticCfg w j) ∧
              v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
                (fun v => (sol w).lam v τ)) := by
    simpa [a, b, M, m, k] using hmix
  calc
    (∫ τ in (selectorMUZOffEnd j)..(selectorMUEarlyWriteSubStart (j + 1)),
      selectorMUHoffIntegrand sol w τ)
        = ∫ τ in a..b, selectorMUHoffIntegrand sol w τ := by
          simp [a, b]
    _ ≤ |y a - M| + 2 * (∫ τ in a..b, k τ * |m τ - M|) := hfield
    _ ≤ |y a - M| + 2 *
          (∫ τ in (selectorMUZOffEnd j)..(selectorMUEarlyWriteSubStart (j + 1)),
            selectorMUHoffGateCoeff sol w τ *
              (Finset.univ.filter (fun v : UniversalLocalView =>
                v ≠ localViewU (solMUReplStaticCfg w j) ∧
                  v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
                    (fun v => (sol w).lam v τ)) := by
        exact add_le_add le_rfl
          (mul_le_mul_of_nonneg_left hmixM (by norm_num : (0 : ℝ) ≤ 2))
    _ = |(sol w).z (selectorMUZOffEnd j) haltCoordU - M| + 2 *
          (∫ τ in (selectorMUZOffEnd j)..(selectorMUEarlyWriteSubStart (j + 1)),
            selectorMUHoffGateCoeff sol w τ *
              (Finset.univ.filter (fun v : UniversalLocalView =>
                v ≠ localViewU (solMUReplStaticCfg w j) ∧
                  v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
                    (fun v => (sol w).lam v τ)) := by
        simp [a, M, y]

/-- Endpoint active-track error at the start of the active suffix.

This removes the naked `activeTrack` term by reusing the cross-boundary write
equation and the two-safe halt-mix bridge. -/
theorem selectorMUHoff_activeTrack_le_initial_add_rightCross_add_endpointBad
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (w j : ℕ)
    (henc : selectorMUHaltEncConstW solMUReplStaticCfg w j) :
    |selectorMixTarget branchU (sol w).u (sol w).lam
        (selectorMUEarlyWriteSubStart (j + 1)) haltCoordU -
      (sol w).z (selectorMUEarlyWriteSubStart (j + 1)) haltCoordU| ≤
      |(sol w).z (selectorMUZOffEnd j) haltCoordU -
        stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 1)) haltCoordU| +
      (∫ τ in (selectorMUZOffEnd j)..(selectorMUEarlyWriteSubStart (j + 1)),
        selectorMUHoffGateCoeff sol w τ *
          (Finset.univ.filter (fun v : UniversalLocalView =>
            v ≠ localViewU (solMUReplStaticCfg w j) ∧
              v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
                (fun v => (sol w).lam v τ)) +
      (Finset.univ.filter (fun v : UniversalLocalView =>
        v ≠ localViewU (solMUReplStaticCfg w j) ∧
          v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
            (fun v => (sol w).lam v
              (selectorMUEarlyWriteSubStart (j + 1))) := by
  classical
  let Z : ℝ := selectorMUZOffEnd j
  let E : ℝ := selectorMUEarlyWriteSubStart (j + 1)
  let M : ℝ :=
    stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 1)) haltCoordU
  let y : ℝ → ℝ := fun τ => (sol w).z τ haltCoordU
  let m : ℝ → ℝ := fun τ =>
    selectorMixTarget branchU (sol w).u (sol w).lam τ haltCoordU
  let k : ℝ → ℝ := fun τ => selectorMUHoffGateCoeff sol w τ
  let bad : ℝ → ℝ := fun τ =>
    (Finset.univ.filter (fun v : UniversalLocalView =>
      v ≠ localViewU (solMUReplStaticCfg w j) ∧
        v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
          (fun v => (sol w).lam v τ)
  have hZE : Z ≤ E := by
    simpa [Z, E] using selectorMUZOffEnd_le_earlyWriteSubStart_succ j
  have hZ0 : 0 ≤ Z := by
    simp [Z, selectorMUZOffEnd]
    positivity
  have hE0 : 0 ≤ E := by
    exact le_trans (selectorMUWriteStartTime_nonneg (j + 1))
      (by simpa [E] using selectorMUWriteStart_le_earlySubStart (j + 1))
  have hk_cont : Continuous k := by
    simpa [k, selectorMUHoffGateCoeff] using
      selector_replicator_gateZ_integrand_continuous (sol w)
  have hm_cont : Continuous m := by
    simpa [m] using (sol w).cont_mixTarget haltCoordU
  have hk_nonneg : ∀ τ ∈ Set.Icc Z E, 0 ≤ k τ := by
    intro τ hτ
    have hτ0 : 0 ≤ τ := le_trans hZ0 hτ.1
    simpa [k, selectorMUHoffGateCoeff] using
      selector_replicator_gateZ_integrand_nonneg (sol w)
        selectorSchedule_domain_of_nonneg_structural (by norm_num [bgpParams38]) hτ0
  have hy_ode : ∀ τ ∈ Set.Icc Z E,
      HasDerivAt y (k τ * (m τ - y τ)) τ := by
    intro τ hτ
    have hτ0 : 0 ≤ τ := le_trans hZ0 hτ.1
    simpa [y, m, k, selectorMUHoffGateCoeff] using
      (sol w).z_hasDeriv τ (selectorSchedule_domain_of_nonneg_structural τ hτ0)
        haltCoordU
  have hz_endpoint :
      |y E - M| ≤ |y Z - M| + ∫ τ in Z..E, k τ * |m τ - M| := by
    exact stack_write_endpoint_le_initial_add_target_integral
      y m k M Z E hZE hk_cont hk_nonneg hm_cont hy_ode
  have hmixInt :=
    selectorMUHoff_right_cross_mix_integral_le_old_or_new_loser_integral
      (sol := sol) boxInputs w j henc
  have hmixIntM :
      (∫ τ in Z..E, k τ * |m τ - M|) ≤
        ∫ τ in (selectorMUZOffEnd j)..(selectorMUEarlyWriteSubStart (j + 1)),
          selectorMUHoffGateCoeff sol w τ * bad τ := by
    simpa [Z, E, M, m, k, bad] using hmixInt
  have hzE :
      |y E - M| ≤ |y Z - M| +
        ∫ τ in (selectorMUZOffEnd j)..(selectorMUEarlyWriteSubStart (j + 1)),
          selectorMUHoffGateCoeff sol w τ * bad τ := by
    exact le_trans hz_endpoint (add_le_add_right hmixIntM _)
  have hM_new : stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 2)) haltCoordU = M := by
    simpa [selectorMUHaltEncConstW, selectorMUHaltEncConst, M] using henc
  have hmixE :
      |m E - M| ≤ bad E := by
    simpa [E, M, m, bad] using
      selectorMUHoff_mix_pointwise_le_old_or_new_loser
        (sol := sol) boxInputs w j (t := E) hE0 rfl hM_new
  have htri : |m E - y E| ≤ |m E - M| + |y E - M| := by
    calc
      |m E - y E| = |(m E - M) + (M - y E)| := by
        congr 1
        ring
      _ ≤ |m E - M| + |M - y E| := abs_add_le _ _
      _ = |m E - M| + |y E - M| := by
        rw [abs_sub_comm M (y E)]
  calc
    |selectorMixTarget branchU (sol w).u (sol w).lam
        (selectorMUEarlyWriteSubStart (j + 1)) haltCoordU -
      (sol w).z (selectorMUEarlyWriteSubStart (j + 1)) haltCoordU|
        = |m E - y E| := by
          simp [m, y, E]
    _ ≤ |m E - M| + |y E - M| := htri
    _ ≤ bad E +
        (|y Z - M| +
          ∫ τ in (selectorMUZOffEnd j)..(selectorMUEarlyWriteSubStart (j + 1)),
            selectorMUHoffGateCoeff sol w τ * bad τ) := by
          exact add_le_add hmixE hzE
    _ =
      |(sol w).z (selectorMUZOffEnd j) haltCoordU -
        stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 1)) haltCoordU| +
      (∫ τ in (selectorMUZOffEnd j)..(selectorMUEarlyWriteSubStart (j + 1)),
        selectorMUHoffGateCoeff sol w τ *
          (Finset.univ.filter (fun v : UniversalLocalView =>
            v ≠ localViewU (solMUReplStaticCfg w j) ∧
              v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
                (fun v => (sol w).lam v τ)) +
      (Finset.univ.filter (fun v : UniversalLocalView =>
        v ≠ localViewU (solMUReplStaticCfg w j) ∧
          v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
            (fun v => (sol w).lam v
              (selectorMUEarlyWriteSubStart (j + 1))) := by
        simp [Z, E, M, y, bad]
        ring

/-- Right actual Hoff cap reduced to the cross-boundary two-safe prefix and the
active suffix's centered target-variation term. -/
theorem selectorMUHoffCapRightField_le_initial_cross_add_centered_active_variation
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (w j : ℕ)
    (henc : selectorMUHaltEncConstW solMUReplStaticCfg w j) :
    selectorMUHoffCapRightField sol w j ≤
      (|(sol w).z (selectorMUZOffEnd j) haltCoordU -
          stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 1)) haltCoordU| +
        2 *
          (∫ τ in (selectorMUZOffEnd j)..(selectorMUEarlyWriteSubStart (j + 1)),
            selectorMUHoffGateCoeff sol w τ *
              (Finset.univ.filter (fun v : UniversalLocalView =>
                v ≠ localViewU (solMUReplStaticCfg w j) ∧
                  v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
                    (fun v => (sol w).lam v τ))) +
      (|selectorMixTarget branchU (sol w).u (sol w).lam
          (selectorMUEarlyWriteSubStart (j + 1)) haltCoordU -
        (sol w).z (selectorMUEarlyWriteSubStart (j + 1)) haltCoordU| +
        (∫ τ in (selectorMUEarlyWriteSubStart (j + 1))..
            (selectorMUWriteHoldTime (j + 1)),
          abs (∑ v : UniversalLocalView,
            ((((1 + Real.cos τ) / 2) ^ Mcy * (κ₀ : ℝ) *
                  (1 / (Fintype.card UniversalLocalView : ℝ) - (sol w).lam v τ) +
                ((1 + Real.sin τ) / 2) ^ Mcy *
                  ((g₀ : ℝ) * Real.exp (bgpParams38.cα * τ)) *
                  (sol w).lam v τ *
                    (universalPval eta heta v ((sol w).u τ) -
                      ∑ w' : UniversalLocalView,
                        (sol w).lam w' τ *
                          universalPval eta heta w' ((sol w).u τ))) *
              (BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU -
                BranchData.evalBranch
                  (branchU (localViewU (solMUReplStaticCfg w (j + 1))))
                  ((sol w).u τ) haltCoordU))))) := by
  let Z : ℝ := selectorMUZOffEnd j
  let E : ℝ := selectorMUEarlyWriteSubStart (j + 1)
  let H : ℝ := selectorMUWriteHoldTime (j + 1)
  let f : ℝ → ℝ := fun τ => selectorMUHoffIntegrand sol w τ
  have hf_cont : Continuous f := by
    simpa [f] using selectorMUHoffIntegrand_continuous (sol := sol) w
  have hI : ∀ x y : ℝ, IntervalIntegrable f MeasureTheory.volume x y :=
    fun x y => hf_cont.intervalIntegrable x y
  have hsplit_raw := intervalIntegral.integral_add_adjacent_intervals
    (hI Z E) (hI E H)
  have hsplit :
      selectorMUHoffCapRightField sol w j =
        (∫ τ in Z..E, f τ) + (∫ τ in E..H, f τ) := by
    unfold selectorMUHoffCapRightField
    simpa [Z, E, H, f, selectorMUNextWriteStart] using hsplit_raw.symm
  have hprefix :=
    selectorMUHoff_right_cross_field_integral_le_initial_add_old_new_loser
      (sol := sol) boxInputs w j henc
  have hsuffix :=
    selectorMUHoff_activeSuffix_integrand_le_initial_tracking_add_centered_mixTargetVariation
      (sol := sol) boxInputs w j (localViewU (solMUReplStaticCfg w (j + 1)))
  calc
    selectorMUHoffCapRightField sol w j
        = (∫ τ in Z..E, f τ) + (∫ τ in E..H, f τ) := hsplit
    _ ≤
        (|(sol w).z (selectorMUZOffEnd j) haltCoordU -
            stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 1)) haltCoordU| +
          2 *
            (∫ τ in (selectorMUZOffEnd j)..(selectorMUEarlyWriteSubStart (j + 1)),
              selectorMUHoffGateCoeff sol w τ *
                (Finset.univ.filter (fun v : UniversalLocalView =>
                  v ≠ localViewU (solMUReplStaticCfg w j) ∧
                    v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
                      (fun v => (sol w).lam v τ))) +
        (|selectorMixTarget branchU (sol w).u (sol w).lam
            (selectorMUEarlyWriteSubStart (j + 1)) haltCoordU -
          (sol w).z (selectorMUEarlyWriteSubStart (j + 1)) haltCoordU| +
          (∫ τ in (selectorMUEarlyWriteSubStart (j + 1))..
              (selectorMUWriteHoldTime (j + 1)),
            abs (∑ v : UniversalLocalView,
              ((((1 + Real.cos τ) / 2) ^ Mcy * (κ₀ : ℝ) *
                    (1 / (Fintype.card UniversalLocalView : ℝ) - (sol w).lam v τ) +
                  ((1 + Real.sin τ) / 2) ^ Mcy *
                    ((g₀ : ℝ) * Real.exp (bgpParams38.cα * τ)) *
                    (sol w).lam v τ *
                      (universalPval eta heta v ((sol w).u τ) -
                        ∑ w' : UniversalLocalView,
                          (sol w).lam w' τ *
                            universalPval eta heta w' ((sol w).u τ))) *
                (BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU -
                  BranchData.evalBranch
                    (branchU (localViewU (solMUReplStaticCfg w (j + 1))))
                    ((sol w).u τ) haltCoordU))))) := by
        exact add_le_add
          (by simpa [Z, E, f] using hprefix)
          (by simpa [E, H, f] using hsuffix)

/-- Combined edge-cap reduction using the centered active-suffix variation
surface instead of the false late shifted-loser tail. -/
theorem selectorMUHoffCapEdges_le_initial_add_centered_active_error_terms
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol) :
    ∀ w j, selectorMUHaltEncConstW solMUReplStaticCfg w j →
      let M : ℝ := stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 1)) haltCoordU
      let leftBad : ℝ :=
        ∫ τ in (selectorMUInterReadStart j)..(selectorMUZOffStart j),
          selectorMUHoffGateCoeff sol w τ *
            (Finset.univ.filter (fun v : UniversalLocalView =>
              v ≠ localViewU (solMUReplStaticCfg w j) ∧
                v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
                  (fun v => (sol w).lam v τ)
      let rightCross : ℝ :=
        ∫ τ in (selectorMUZOffEnd j)..(selectorMUEarlyWriteSubStart (j + 1)),
          selectorMUHoffGateCoeff sol w τ *
            (Finset.univ.filter (fun v : UniversalLocalView =>
              v ≠ localViewU (solMUReplStaticCfg w j) ∧
                v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
                  (fun v => (sol w).lam v τ)
      let activeTrack : ℝ :=
        |selectorMixTarget branchU (sol w).u (sol w).lam
            (selectorMUEarlyWriteSubStart (j + 1)) haltCoordU -
          (sol w).z (selectorMUEarlyWriteSubStart (j + 1)) haltCoordU|
      let activeVar : ℝ :=
        ∫ τ in (selectorMUEarlyWriteSubStart (j + 1))..
            (selectorMUWriteHoldTime (j + 1)),
          abs (∑ v : UniversalLocalView,
            (((1 + Real.cos τ) / 2) ^ Mcy * (κ₀ : ℝ) *
                (1 / (Fintype.card UniversalLocalView : ℝ) - (sol w).lam v τ) +
              ((1 + Real.sin τ) / 2) ^ Mcy *
                ((g₀ : ℝ) * Real.exp (bgpParams38.cα * τ)) *
                (sol w).lam v τ *
                  (universalPval eta heta v ((sol w).u τ) -
                    ∑ w' : UniversalLocalView,
                      (sol w).lam w' τ *
                        universalPval eta heta w' ((sol w).u τ))) *
              (BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU -
                BranchData.evalBranch
                  (branchU (localViewU (solMUReplStaticCfg w (j + 1))))
                  ((sol w).u τ) haltCoordU))
      selectorMUHoffCapLeftField sol w j + selectorMUHoffCapRightField sol w j ≤
        |(sol w).z (selectorMUInterReadStart j) haltCoordU - M| +
          |(sol w).z (selectorMUZOffEnd j) haltCoordU - M| +
          2 * (leftBad + rightCross) + activeTrack + activeVar := by
  intro w j henc
  let M : ℝ := stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 1)) haltCoordU
  let leftBad : ℝ :=
    ∫ τ in (selectorMUInterReadStart j)..(selectorMUZOffStart j),
      selectorMUHoffGateCoeff sol w τ *
        (Finset.univ.filter (fun v : UniversalLocalView =>
          v ≠ localViewU (solMUReplStaticCfg w j) ∧
            v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
              (fun v => (sol w).lam v τ)
  let rightCross : ℝ :=
    ∫ τ in (selectorMUZOffEnd j)..(selectorMUEarlyWriteSubStart (j + 1)),
      selectorMUHoffGateCoeff sol w τ *
        (Finset.univ.filter (fun v : UniversalLocalView =>
          v ≠ localViewU (solMUReplStaticCfg w j) ∧
            v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
              (fun v => (sol w).lam v τ)
  let activeTrack : ℝ :=
    |selectorMixTarget branchU (sol w).u (sol w).lam
        (selectorMUEarlyWriteSubStart (j + 1)) haltCoordU -
      (sol w).z (selectorMUEarlyWriteSubStart (j + 1)) haltCoordU|
  let activeVar : ℝ :=
    ∫ τ in (selectorMUEarlyWriteSubStart (j + 1))..
        (selectorMUWriteHoldTime (j + 1)),
      abs (∑ v : UniversalLocalView,
        (((1 + Real.cos τ) / 2) ^ Mcy * (κ₀ : ℝ) *
            (1 / (Fintype.card UniversalLocalView : ℝ) - (sol w).lam v τ) +
          ((1 + Real.sin τ) / 2) ^ Mcy *
            ((g₀ : ℝ) * Real.exp (bgpParams38.cα * τ)) *
            (sol w).lam v τ *
              (universalPval eta heta v ((sol w).u τ) -
                ∑ w' : UniversalLocalView,
                  (sol w).lam w' τ *
                    universalPval eta heta w' ((sol w).u τ))) *
          (BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU -
            BranchData.evalBranch
              (branchU (localViewU (solMUReplStaticCfg w (j + 1))))
              ((sol w).u τ) haltCoordU))
  have hleft := selectorMUHoffCapLeftField_le_initial_add_old_new_loser_integral
    (sol := sol) boxInputs w j henc
  have hright :=
    selectorMUHoffCapRightField_le_initial_cross_add_centered_active_variation
      (sol := sol) boxInputs w j henc
  dsimp only
  change
    selectorMUHoffCapLeftField sol w j + selectorMUHoffCapRightField sol w j ≤
      |(sol w).z (selectorMUInterReadStart j) haltCoordU - M| +
        |(sol w).z (selectorMUZOffEnd j) haltCoordU - M| +
        2 * (leftBad + rightCross) + activeTrack + activeVar
  have hleft' :
      selectorMUHoffCapLeftField sol w j ≤
        |(sol w).z (selectorMUInterReadStart j) haltCoordU - M| + 2 * leftBad := by
    simpa [M, leftBad] using hleft
  have hright' :
      selectorMUHoffCapRightField sol w j ≤
        (|(sol w).z (selectorMUZOffEnd j) haltCoordU - M| + 2 * rightCross) +
          (activeTrack + activeVar) := by
    simpa [M, rightCross, activeTrack, activeVar] using hright
  nlinarith [hleft', hright']

/-- Combined edge-cap reduction with the active-suffix term in the
cancellation-preserving gap/reset covariance coordinates. -/
theorem selectorMUHoffCapEdges_le_initial_add_gap_covariance_error_terms
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol) :
    ∀ w j, selectorMUHaltEncConstW solMUReplStaticCfg w j →
      let M : ℝ := stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 1)) haltCoordU
      let leftBad : ℝ :=
        ∫ τ in (selectorMUInterReadStart j)..(selectorMUZOffStart j),
          selectorMUHoffGateCoeff sol w τ *
            (Finset.univ.filter (fun v : UniversalLocalView =>
              v ≠ localViewU (solMUReplStaticCfg w j) ∧
                v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
                  (fun v => (sol w).lam v τ)
      let rightCross : ℝ :=
        ∫ τ in (selectorMUZOffEnd j)..(selectorMUEarlyWriteSubStart (j + 1)),
          selectorMUHoffGateCoeff sol w τ *
            (Finset.univ.filter (fun v : UniversalLocalView =>
              v ≠ localViewU (solMUReplStaticCfg w j) ∧
                v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
                  (fun v => (sol w).lam v τ)
      let activeTrack : ℝ :=
        |selectorMixTarget branchU (sol w).u (sol w).lam
            (selectorMUEarlyWriteSubStart (j + 1)) haltCoordU -
          (sol w).z (selectorMUEarlyWriteSubStart (j + 1)) haltCoordU|
      let activeVar : ℝ :=
        ∫ τ in (selectorMUEarlyWriteSubStart (j + 1))..
            (selectorMUWriteHoldTime (j + 1)),
          abs ((((1 + Real.sin τ) / 2) ^ Mcy *
              ((g₀ : ℝ) * Real.exp (bgpParams38.cα * τ))) *
              (∑ v : UniversalLocalView,
                (sol w).lam v τ *
                  (universalPval eta heta
                    (localViewU (solMUReplStaticCfg w (j + 1))) ((sol w).u τ) -
                    universalPval eta heta v ((sol w).u τ)) *
                  ((BranchData.evalBranch
                      (branchU (localViewU (solMUReplStaticCfg w (j + 1))))
                      ((sol w).u τ) haltCoordU -
                      BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU) -
                    ∑ w' : UniversalLocalView,
                      (sol w).lam w' τ *
                        (BranchData.evalBranch
                          (branchU (localViewU (solMUReplStaticCfg w (j + 1))))
                          ((sol w).u τ) haltCoordU -
                          BranchData.evalBranch (branchU w') ((sol w).u τ) haltCoordU))) -
            (((1 + Real.cos τ) / 2) ^ Mcy * (κ₀ : ℝ)) *
              (((Fintype.card UniversalLocalView : ℝ)⁻¹ *
                  ∑ v : UniversalLocalView,
                    (BranchData.evalBranch
                      (branchU (localViewU (solMUReplStaticCfg w (j + 1))))
                      ((sol w).u τ) haltCoordU -
                      BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU)) -
                ∑ v : UniversalLocalView,
                  (sol w).lam v τ *
                    (BranchData.evalBranch
                      (branchU (localViewU (solMUReplStaticCfg w (j + 1))))
                      ((sol w).u τ) haltCoordU -
                      BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU)))
      selectorMUHoffCapLeftField sol w j + selectorMUHoffCapRightField sol w j ≤
        |(sol w).z (selectorMUInterReadStart j) haltCoordU - M| +
          |(sol w).z (selectorMUZOffEnd j) haltCoordU - M| +
          2 * (leftBad + rightCross) + activeTrack + activeVar := by
  intro w j henc
  let c : UniversalLocalView := localViewU (solMUReplStaticCfg w (j + 1))
  let M : ℝ := stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 1)) haltCoordU
  let leftBad : ℝ :=
    ∫ τ in (selectorMUInterReadStart j)..(selectorMUZOffStart j),
      selectorMUHoffGateCoeff sol w τ *
        (Finset.univ.filter (fun v : UniversalLocalView =>
          v ≠ localViewU (solMUReplStaticCfg w j) ∧
            v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
              (fun v => (sol w).lam v τ)
  let rightCross : ℝ :=
    ∫ τ in (selectorMUZOffEnd j)..(selectorMUEarlyWriteSubStart (j + 1)),
      selectorMUHoffGateCoeff sol w τ *
        (Finset.univ.filter (fun v : UniversalLocalView =>
          v ≠ localViewU (solMUReplStaticCfg w j) ∧
            v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
              (fun v => (sol w).lam v τ)
  let activeTrack : ℝ :=
    |selectorMixTarget branchU (sol w).u (sol w).lam
        (selectorMUEarlyWriteSubStart (j + 1)) haltCoordU -
      (sol w).z (selectorMUEarlyWriteSubStart (j + 1)) haltCoordU|
  let activeVarCentered : ℝ :=
    ∫ τ in (selectorMUEarlyWriteSubStart (j + 1))..
        (selectorMUWriteHoldTime (j + 1)),
      abs (∑ v : UniversalLocalView,
        (((1 + Real.cos τ) / 2) ^ Mcy * (κ₀ : ℝ) *
            (1 / (Fintype.card UniversalLocalView : ℝ) - (sol w).lam v τ) +
          ((1 + Real.sin τ) / 2) ^ Mcy *
            ((g₀ : ℝ) * Real.exp (bgpParams38.cα * τ)) *
            (sol w).lam v τ *
              (universalPval eta heta v ((sol w).u τ) -
                ∑ w' : UniversalLocalView,
                  (sol w).lam w' τ *
                    universalPval eta heta w' ((sol w).u τ))) *
          (BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU -
            BranchData.evalBranch (branchU c) ((sol w).u τ) haltCoordU))
  let activeVar : ℝ :=
    ∫ τ in (selectorMUEarlyWriteSubStart (j + 1))..
        (selectorMUWriteHoldTime (j + 1)),
      abs ((((1 + Real.sin τ) / 2) ^ Mcy *
          ((g₀ : ℝ) * Real.exp (bgpParams38.cα * τ))) *
          (∑ v : UniversalLocalView,
            (sol w).lam v τ *
              (universalPval eta heta c ((sol w).u τ) -
                universalPval eta heta v ((sol w).u τ)) *
              ((BranchData.evalBranch (branchU c) ((sol w).u τ) haltCoordU -
                  BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU) -
                ∑ w' : UniversalLocalView,
                  (sol w).lam w' τ *
                    (BranchData.evalBranch (branchU c) ((sol w).u τ) haltCoordU -
                      BranchData.evalBranch (branchU w') ((sol w).u τ) haltCoordU))) -
        (((1 + Real.cos τ) / 2) ^ Mcy * (κ₀ : ℝ)) *
          (((Fintype.card UniversalLocalView : ℝ)⁻¹ *
              ∑ v : UniversalLocalView,
                (BranchData.evalBranch (branchU c) ((sol w).u τ) haltCoordU -
                  BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU)) -
            ∑ v : UniversalLocalView,
              (sol w).lam v τ *
                (BranchData.evalBranch (branchU c) ((sol w).u τ) haltCoordU -
                  BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU)))
  have hcenter :=
    selectorMUHoffCapEdges_le_initial_add_centered_active_error_terms
      (sol := sol) boxInputs w j henc
  have hvar : activeVarCentered = activeVar := by
    simpa [activeVarCentered, activeVar, c] using
      selectorMUHoff_activeSuffix_centeredVariation_eq_gap_covarianceVariation
        (sol := sol) boxInputs w j c
  dsimp only
  change
    selectorMUHoffCapLeftField sol w j + selectorMUHoffCapRightField sol w j ≤
      |(sol w).z (selectorMUInterReadStart j) haltCoordU - M| +
        |(sol w).z (selectorMUZOffEnd j) haltCoordU - M| +
        2 * (leftBad + rightCross) + activeTrack + activeVar
  have hcenter' :
      selectorMUHoffCapLeftField sol w j + selectorMUHoffCapRightField sol w j ≤
        |(sol w).z (selectorMUInterReadStart j) haltCoordU - M| +
          |(sol w).z (selectorMUZOffEnd j) haltCoordU - M| +
          2 * (leftBad + rightCross) + activeTrack + activeVarCentered := by
    simpa [M, leftBad, rightCross, activeTrack, activeVarCentered, c] using hcenter
  simpa [hvar] using hcenter'

/-- Combined edge-cap reduction with the active-track endpoint discharged.

The remaining right-edge terms are the two-safe cross integral, its early
endpoint bad mass, and the cancellation-preserving active covariance term. -/
theorem selectorMUHoffCapEdges_le_initial_add_gap_covariance_no_activeTrack
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol) :
    ∀ w j, selectorMUHaltEncConstW solMUReplStaticCfg w j →
      let M : ℝ := stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 1)) haltCoordU
      let leftBad : ℝ :=
        ∫ τ in (selectorMUInterReadStart j)..(selectorMUZOffStart j),
          selectorMUHoffGateCoeff sol w τ *
            (Finset.univ.filter (fun v : UniversalLocalView =>
              v ≠ localViewU (solMUReplStaticCfg w j) ∧
                v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
                  (fun v => (sol w).lam v τ)
      let rightCross : ℝ :=
        ∫ τ in (selectorMUZOffEnd j)..(selectorMUEarlyWriteSubStart (j + 1)),
          selectorMUHoffGateCoeff sol w τ *
            (Finset.univ.filter (fun v : UniversalLocalView =>
              v ≠ localViewU (solMUReplStaticCfg w j) ∧
                v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
                  (fun v => (sol w).lam v τ)
      let endpointBad : ℝ :=
        (Finset.univ.filter (fun v : UniversalLocalView =>
          v ≠ localViewU (solMUReplStaticCfg w j) ∧
            v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
              (fun v => (sol w).lam v
                (selectorMUEarlyWriteSubStart (j + 1)))
      let activeVar : ℝ :=
        ∫ τ in (selectorMUEarlyWriteSubStart (j + 1))..
            (selectorMUWriteHoldTime (j + 1)),
          abs ((((1 + Real.sin τ) / 2) ^ Mcy *
              ((g₀ : ℝ) * Real.exp (bgpParams38.cα * τ))) *
              (∑ v : UniversalLocalView,
                (sol w).lam v τ *
                  (universalPval eta heta
                    (localViewU (solMUReplStaticCfg w (j + 1))) ((sol w).u τ) -
                    universalPval eta heta v ((sol w).u τ)) *
                  ((BranchData.evalBranch
                      (branchU (localViewU (solMUReplStaticCfg w (j + 1))))
                      ((sol w).u τ) haltCoordU -
                      BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU) -
                    ∑ w' : UniversalLocalView,
                      (sol w).lam w' τ *
                        (BranchData.evalBranch
                          (branchU (localViewU (solMUReplStaticCfg w (j + 1))))
                          ((sol w).u τ) haltCoordU -
                          BranchData.evalBranch (branchU w') ((sol w).u τ) haltCoordU))) -
            (((1 + Real.cos τ) / 2) ^ Mcy * (κ₀ : ℝ)) *
              (((Fintype.card UniversalLocalView : ℝ)⁻¹ *
                  ∑ v : UniversalLocalView,
                    (BranchData.evalBranch
                      (branchU (localViewU (solMUReplStaticCfg w (j + 1))))
                      ((sol w).u τ) haltCoordU -
                      BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU)) -
                ∑ v : UniversalLocalView,
                  (sol w).lam v τ *
                    (BranchData.evalBranch
                      (branchU (localViewU (solMUReplStaticCfg w (j + 1))))
                      ((sol w).u τ) haltCoordU -
                      BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU)))
      selectorMUHoffCapLeftField sol w j + selectorMUHoffCapRightField sol w j ≤
        |(sol w).z (selectorMUInterReadStart j) haltCoordU - M| +
          2 * |(sol w).z (selectorMUZOffEnd j) haltCoordU - M| +
          2 * leftBad + 3 * rightCross + endpointBad + activeVar := by
  intro w j henc
  let c : UniversalLocalView := localViewU (solMUReplStaticCfg w (j + 1))
  let M : ℝ := stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 1)) haltCoordU
  let leftBad : ℝ :=
    ∫ τ in (selectorMUInterReadStart j)..(selectorMUZOffStart j),
      selectorMUHoffGateCoeff sol w τ *
        (Finset.univ.filter (fun v : UniversalLocalView =>
          v ≠ localViewU (solMUReplStaticCfg w j) ∧
            v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
              (fun v => (sol w).lam v τ)
  let rightCross : ℝ :=
    ∫ τ in (selectorMUZOffEnd j)..(selectorMUEarlyWriteSubStart (j + 1)),
      selectorMUHoffGateCoeff sol w τ *
        (Finset.univ.filter (fun v : UniversalLocalView =>
          v ≠ localViewU (solMUReplStaticCfg w j) ∧
            v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
              (fun v => (sol w).lam v τ)
  let endpointBad : ℝ :=
    (Finset.univ.filter (fun v : UniversalLocalView =>
      v ≠ localViewU (solMUReplStaticCfg w j) ∧
        v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
          (fun v => (sol w).lam v
            (selectorMUEarlyWriteSubStart (j + 1)))
  let activeTrack : ℝ :=
    |selectorMixTarget branchU (sol w).u (sol w).lam
        (selectorMUEarlyWriteSubStart (j + 1)) haltCoordU -
      (sol w).z (selectorMUEarlyWriteSubStart (j + 1)) haltCoordU|
  let activeVar : ℝ :=
    ∫ τ in (selectorMUEarlyWriteSubStart (j + 1))..
        (selectorMUWriteHoldTime (j + 1)),
      abs ((((1 + Real.sin τ) / 2) ^ Mcy *
          ((g₀ : ℝ) * Real.exp (bgpParams38.cα * τ))) *
          (∑ v : UniversalLocalView,
            (sol w).lam v τ *
              (universalPval eta heta c ((sol w).u τ) -
                universalPval eta heta v ((sol w).u τ)) *
              ((BranchData.evalBranch (branchU c) ((sol w).u τ) haltCoordU -
                  BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU) -
                ∑ w' : UniversalLocalView,
                  (sol w).lam w' τ *
                    (BranchData.evalBranch (branchU c) ((sol w).u τ) haltCoordU -
                      BranchData.evalBranch (branchU w') ((sol w).u τ) haltCoordU))) -
        (((1 + Real.cos τ) / 2) ^ Mcy * (κ₀ : ℝ)) *
          (((Fintype.card UniversalLocalView : ℝ)⁻¹ *
              ∑ v : UniversalLocalView,
                (BranchData.evalBranch (branchU c) ((sol w).u τ) haltCoordU -
                  BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU)) -
            ∑ v : UniversalLocalView,
              (sol w).lam v τ *
                (BranchData.evalBranch (branchU c) ((sol w).u τ) haltCoordU -
                  BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU)))
  have hbase :=
    selectorMUHoffCapEdges_le_initial_add_gap_covariance_error_terms
      (sol := sol) boxInputs w j henc
  have htrack :=
    selectorMUHoff_activeTrack_le_initial_add_rightCross_add_endpointBad
      (sol := sol) boxInputs w j henc
  dsimp only
  change
    selectorMUHoffCapLeftField sol w j + selectorMUHoffCapRightField sol w j ≤
      |(sol w).z (selectorMUInterReadStart j) haltCoordU - M| +
        2 * |(sol w).z (selectorMUZOffEnd j) haltCoordU - M| +
        2 * leftBad + 3 * rightCross + endpointBad + activeVar
  have hbase' :
      selectorMUHoffCapLeftField sol w j + selectorMUHoffCapRightField sol w j ≤
        |(sol w).z (selectorMUInterReadStart j) haltCoordU - M| +
          |(sol w).z (selectorMUZOffEnd j) haltCoordU - M| +
          2 * (leftBad + rightCross) + activeTrack + activeVar := by
    simpa [M, leftBad, rightCross, activeTrack, activeVar, c] using hbase
  have htrack' :
      activeTrack ≤
        |(sol w).z (selectorMUZOffEnd j) haltCoordU - M| +
          rightCross + endpointBad := by
    simpa [M, rightCross, endpointBad, activeTrack] using htrack
  nlinarith [hbase', htrack']

/-- Combined edge-cap reduction with the active covariance discharged into the
branch-residual/mean-product surface.

This is the honest active-write outlet: it keeps the reset and selector terms
coupled until after the finite-sum cancellation, then leaves only the concrete
branch tracking residual and mean-gap product on the active suffix. -/
theorem selectorMUHoffCapEdges_le_initial_add_branchResidual_active_terms
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (hg₀_nonneg : 0 ≤ (g₀ : ℝ)) :
    ∀ w j, selectorMUHaltEncConstW solMUReplStaticCfg w j →
      (∀ τ ∈ Set.Icc (selectorMUEarlyWriteSubStart (j + 1))
          (selectorMUWriteHoldTime (j + 1)), ∀ v : UniversalLocalView,
        0 ≤ BranchData.evalBranch
            (branchU (localViewU (solMUReplStaticCfg w (j + 1))))
            ((sol w).u τ) haltCoordU -
          BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU) →
      (∀ τ ∈ Set.Icc (selectorMUEarlyWriteSubStart (j + 1))
          (selectorMUWriteHoldTime (j + 1)), ∀ v : UniversalLocalView,
        0 ≤ universalPval eta heta
            (localViewU (solMUReplStaticCfg w (j + 1))) ((sol w).u τ) -
          universalPval eta heta v ((sol w).u τ)) →
      let M : ℝ := stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 1)) haltCoordU
      let leftBad : ℝ :=
        ∫ τ in (selectorMUInterReadStart j)..(selectorMUZOffStart j),
          selectorMUHoffGateCoeff sol w τ *
            (Finset.univ.filter (fun v : UniversalLocalView =>
              v ≠ localViewU (solMUReplStaticCfg w j) ∧
                v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
                  (fun v => (sol w).lam v τ)
      let rightCross : ℝ :=
        ∫ τ in (selectorMUZOffEnd j)..(selectorMUEarlyWriteSubStart (j + 1)),
          selectorMUHoffGateCoeff sol w τ *
            (Finset.univ.filter (fun v : UniversalLocalView =>
              v ≠ localViewU (solMUReplStaticCfg w j) ∧
                v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
                  (fun v => (sol w).lam v τ)
      let endpointBad : ℝ :=
        (Finset.univ.filter (fun v : UniversalLocalView =>
          v ≠ localViewU (solMUReplStaticCfg w j) ∧
            v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
              (fun v => (sol w).lam v
                (selectorMUEarlyWriteSubStart (j + 1)))
      let activeBranchResidual : ℝ :=
        ∫ τ in (selectorMUEarlyWriteSubStart (j + 1))..
            (selectorMUWriteHoldTime (j + 1)),
          (∑ v : UniversalLocalView,
            (BranchData.evalBranch
                (branchU (localViewU (solMUReplStaticCfg w (j + 1))))
                ((sol w).u τ) haltCoordU -
              BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU) *
              |(((1 + Real.cos τ) / 2) ^ Mcy * (κ₀ : ℝ)) *
                  (Fintype.card UniversalLocalView : ℝ)⁻¹ -
                ((((1 + Real.cos τ) / 2) ^ Mcy * (κ₀ : ℝ)) +
                  (((1 + Real.sin τ) / 2) ^ Mcy *
                    ((g₀ : ℝ) * Real.exp (bgpParams38.cα * τ))) *
                    (universalPval eta heta
                        (localViewU (solMUReplStaticCfg w (j + 1))) ((sol w).u τ) -
                      universalPval eta heta v ((sol w).u τ))) *
                  (sol w).lam v τ|) +
          (((1 + Real.sin τ) / 2) ^ Mcy *
            ((g₀ : ℝ) * Real.exp (bgpParams38.cα * τ))) *
            (∑ v : UniversalLocalView,
              (sol w).lam v τ *
                (universalPval eta heta
                    (localViewU (solMUReplStaticCfg w (j + 1))) ((sol w).u τ) -
                  universalPval eta heta v ((sol w).u τ))) *
            (∑ v : UniversalLocalView,
              (sol w).lam v τ *
                (BranchData.evalBranch
                    (branchU (localViewU (solMUReplStaticCfg w (j + 1))))
                    ((sol w).u τ) haltCoordU -
                  BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU))
      selectorMUHoffCapLeftField sol w j + selectorMUHoffCapRightField sol w j ≤
        |(sol w).z (selectorMUInterReadStart j) haltCoordU - M| +
          2 * |(sol w).z (selectorMUZOffEnd j) haltCoordU - M| +
          2 * leftBad + 3 * rightCross + endpointBad + activeBranchResidual := by
  intro w j henc hD_nonneg hdelta_nonneg
  let c : UniversalLocalView := localViewU (solMUReplStaticCfg w (j + 1))
  let M : ℝ := stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 1)) haltCoordU
  let leftBad : ℝ :=
    ∫ τ in (selectorMUInterReadStart j)..(selectorMUZOffStart j),
      selectorMUHoffGateCoeff sol w τ *
        (Finset.univ.filter (fun v : UniversalLocalView =>
          v ≠ localViewU (solMUReplStaticCfg w j) ∧
            v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
              (fun v => (sol w).lam v τ)
  let rightCross : ℝ :=
    ∫ τ in (selectorMUZOffEnd j)..(selectorMUEarlyWriteSubStart (j + 1)),
      selectorMUHoffGateCoeff sol w τ *
        (Finset.univ.filter (fun v : UniversalLocalView =>
          v ≠ localViewU (solMUReplStaticCfg w j) ∧
            v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
              (fun v => (sol w).lam v τ)
  let endpointBad : ℝ :=
    (Finset.univ.filter (fun v : UniversalLocalView =>
      v ≠ localViewU (solMUReplStaticCfg w j) ∧
        v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
          (fun v => (sol w).lam v
            (selectorMUEarlyWriteSubStart (j + 1)))
  let activeVar : ℝ :=
    ∫ τ in (selectorMUEarlyWriteSubStart (j + 1))..
        (selectorMUWriteHoldTime (j + 1)),
      abs ((((1 + Real.sin τ) / 2) ^ Mcy *
          ((g₀ : ℝ) * Real.exp (bgpParams38.cα * τ))) *
          (∑ v : UniversalLocalView,
            (sol w).lam v τ *
              (universalPval eta heta c ((sol w).u τ) -
                universalPval eta heta v ((sol w).u τ)) *
              ((BranchData.evalBranch (branchU c) ((sol w).u τ) haltCoordU -
                  BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU) -
                ∑ w' : UniversalLocalView,
                  (sol w).lam w' τ *
                    (BranchData.evalBranch (branchU c) ((sol w).u τ) haltCoordU -
                      BranchData.evalBranch (branchU w') ((sol w).u τ) haltCoordU))) -
        (((1 + Real.cos τ) / 2) ^ Mcy * (κ₀ : ℝ)) *
          (((Fintype.card UniversalLocalView : ℝ)⁻¹ *
              ∑ v : UniversalLocalView,
                (BranchData.evalBranch (branchU c) ((sol w).u τ) haltCoordU -
                  BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU)) -
            ∑ v : UniversalLocalView,
              (sol w).lam v τ *
                (BranchData.evalBranch (branchU c) ((sol w).u τ) haltCoordU -
                  BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU)))
  let activeBranchResidual : ℝ :=
    ∫ τ in (selectorMUEarlyWriteSubStart (j + 1))..
        (selectorMUWriteHoldTime (j + 1)),
      (∑ v : UniversalLocalView,
        (BranchData.evalBranch (branchU c) ((sol w).u τ) haltCoordU -
          BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU) *
          |(((1 + Real.cos τ) / 2) ^ Mcy * (κ₀ : ℝ)) *
              (Fintype.card UniversalLocalView : ℝ)⁻¹ -
            ((((1 + Real.cos τ) / 2) ^ Mcy * (κ₀ : ℝ)) +
              (((1 + Real.sin τ) / 2) ^ Mcy *
                ((g₀ : ℝ) * Real.exp (bgpParams38.cα * τ))) *
                (universalPval eta heta c ((sol w).u τ) -
                  universalPval eta heta v ((sol w).u τ))) *
              (sol w).lam v τ|) +
      (((1 + Real.sin τ) / 2) ^ Mcy *
        ((g₀ : ℝ) * Real.exp (bgpParams38.cα * τ))) *
        (∑ v : UniversalLocalView,
          (sol w).lam v τ *
            (universalPval eta heta c ((sol w).u τ) -
              universalPval eta heta v ((sol w).u τ))) *
        (∑ v : UniversalLocalView,
          (sol w).lam v τ *
            (BranchData.evalBranch (branchU c) ((sol w).u τ) haltCoordU -
              BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU))
  have hbase :=
    selectorMUHoffCapEdges_le_initial_add_gap_covariance_no_activeTrack
      (sol := sol) boxInputs w j henc
  have hactive :=
    selectorMUHoff_activeGapCovarianceVariation_le_branchResiduals_add_meanGapProduct_of_nonneg
      (sol := sol) boxInputs hg₀_nonneg w j c
      (by simpa [c] using hD_nonneg)
      (by simpa [c] using hdelta_nonneg)
  dsimp only
  change
    selectorMUHoffCapLeftField sol w j + selectorMUHoffCapRightField sol w j ≤
      |(sol w).z (selectorMUInterReadStart j) haltCoordU - M| +
        2 * |(sol w).z (selectorMUZOffEnd j) haltCoordU - M| +
        2 * leftBad + 3 * rightCross + endpointBad + activeBranchResidual
  have hbase' :
      selectorMUHoffCapLeftField sol w j + selectorMUHoffCapRightField sol w j ≤
        |(sol w).z (selectorMUInterReadStart j) haltCoordU - M| +
          2 * |(sol w).z (selectorMUZOffEnd j) haltCoordU - M| +
          2 * leftBad + 3 * rightCross + endpointBad + activeVar := by
    simpa [M, leftBad, rightCross, endpointBad, activeVar, c] using hbase
  have hactive' : activeVar ≤ activeBranchResidual := by
    simpa [activeVar, activeBranchResidual, c] using hactive
  nlinarith [hbase', hactive']

/-- Combined edge-cap reduction with flipped active branch residuals.

This is the `target = 0` analogue of
`selectorMUHoffCapEdges_le_initial_add_branchResidual_active_terms`: the cap
variation is unchanged, but the residual branch coordinate is `B_v - B_c`. -/
theorem selectorMUHoffCapEdges_le_initial_add_branchResidual_active_terms_flip
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (hg₀_nonneg : 0 ≤ (g₀ : ℝ)) :
    ∀ w j, selectorMUHaltEncConstW solMUReplStaticCfg w j →
      (∀ τ ∈ Set.Icc (selectorMUEarlyWriteSubStart (j + 1))
          (selectorMUWriteHoldTime (j + 1)), ∀ v : UniversalLocalView,
        0 ≤ BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU -
          BranchData.evalBranch
            (branchU (localViewU (solMUReplStaticCfg w (j + 1))))
            ((sol w).u τ) haltCoordU) →
      (∀ τ ∈ Set.Icc (selectorMUEarlyWriteSubStart (j + 1))
          (selectorMUWriteHoldTime (j + 1)), ∀ v : UniversalLocalView,
        0 ≤ universalPval eta heta
            (localViewU (solMUReplStaticCfg w (j + 1))) ((sol w).u τ) -
          universalPval eta heta v ((sol w).u τ)) →
      let M : ℝ := stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 1)) haltCoordU
      let leftBad : ℝ :=
        ∫ τ in (selectorMUInterReadStart j)..(selectorMUZOffStart j),
          selectorMUHoffGateCoeff sol w τ *
            (Finset.univ.filter (fun v : UniversalLocalView =>
              v ≠ localViewU (solMUReplStaticCfg w j) ∧
                v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
                  (fun v => (sol w).lam v τ)
      let rightCross : ℝ :=
        ∫ τ in (selectorMUZOffEnd j)..(selectorMUEarlyWriteSubStart (j + 1)),
          selectorMUHoffGateCoeff sol w τ *
            (Finset.univ.filter (fun v : UniversalLocalView =>
              v ≠ localViewU (solMUReplStaticCfg w j) ∧
                v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
                  (fun v => (sol w).lam v τ)
      let endpointBad : ℝ :=
        (Finset.univ.filter (fun v : UniversalLocalView =>
          v ≠ localViewU (solMUReplStaticCfg w j) ∧
            v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
              (fun v => (sol w).lam v
                (selectorMUEarlyWriteSubStart (j + 1)))
      let activeBranchResidual : ℝ :=
        ∫ τ in (selectorMUEarlyWriteSubStart (j + 1))..
            (selectorMUWriteHoldTime (j + 1)),
          (∑ v : UniversalLocalView,
            (BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU -
              BranchData.evalBranch
                (branchU (localViewU (solMUReplStaticCfg w (j + 1))))
                ((sol w).u τ) haltCoordU) *
              |(((1 + Real.cos τ) / 2) ^ Mcy * (κ₀ : ℝ)) *
                  (Fintype.card UniversalLocalView : ℝ)⁻¹ -
                ((((1 + Real.cos τ) / 2) ^ Mcy * (κ₀ : ℝ)) +
                  (((1 + Real.sin τ) / 2) ^ Mcy *
                    ((g₀ : ℝ) * Real.exp (bgpParams38.cα * τ))) *
                    (universalPval eta heta
                        (localViewU (solMUReplStaticCfg w (j + 1))) ((sol w).u τ) -
                      universalPval eta heta v ((sol w).u τ))) *
                  (sol w).lam v τ|) +
          (((1 + Real.sin τ) / 2) ^ Mcy *
            ((g₀ : ℝ) * Real.exp (bgpParams38.cα * τ))) *
            (∑ v : UniversalLocalView,
              (sol w).lam v τ *
                (universalPval eta heta
                    (localViewU (solMUReplStaticCfg w (j + 1))) ((sol w).u τ) -
                  universalPval eta heta v ((sol w).u τ))) *
            (∑ v : UniversalLocalView,
              (sol w).lam v τ *
                (BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU -
                  BranchData.evalBranch
                    (branchU (localViewU (solMUReplStaticCfg w (j + 1))))
                    ((sol w).u τ) haltCoordU))
      selectorMUHoffCapLeftField sol w j + selectorMUHoffCapRightField sol w j ≤
        |(sol w).z (selectorMUInterReadStart j) haltCoordU - M| +
          2 * |(sol w).z (selectorMUZOffEnd j) haltCoordU - M| +
          2 * leftBad + 3 * rightCross + endpointBad + activeBranchResidual := by
  intro w j henc hD_nonneg hdelta_nonneg
  let c : UniversalLocalView := localViewU (solMUReplStaticCfg w (j + 1))
  let M : ℝ := stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 1)) haltCoordU
  let leftBad : ℝ :=
    ∫ τ in (selectorMUInterReadStart j)..(selectorMUZOffStart j),
      selectorMUHoffGateCoeff sol w τ *
        (Finset.univ.filter (fun v : UniversalLocalView =>
          v ≠ localViewU (solMUReplStaticCfg w j) ∧
            v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
              (fun v => (sol w).lam v τ)
  let rightCross : ℝ :=
    ∫ τ in (selectorMUZOffEnd j)..(selectorMUEarlyWriteSubStart (j + 1)),
      selectorMUHoffGateCoeff sol w τ *
        (Finset.univ.filter (fun v : UniversalLocalView =>
          v ≠ localViewU (solMUReplStaticCfg w j) ∧
            v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
              (fun v => (sol w).lam v τ)
  let endpointBad : ℝ :=
    (Finset.univ.filter (fun v : UniversalLocalView =>
      v ≠ localViewU (solMUReplStaticCfg w j) ∧
        v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
          (fun v => (sol w).lam v
            (selectorMUEarlyWriteSubStart (j + 1)))
  let activeVar : ℝ :=
    ∫ τ in (selectorMUEarlyWriteSubStart (j + 1))..
        (selectorMUWriteHoldTime (j + 1)),
      abs ((((1 + Real.sin τ) / 2) ^ Mcy *
          ((g₀ : ℝ) * Real.exp (bgpParams38.cα * τ))) *
          (∑ v : UniversalLocalView,
            (sol w).lam v τ *
              (universalPval eta heta c ((sol w).u τ) -
                universalPval eta heta v ((sol w).u τ)) *
              ((BranchData.evalBranch (branchU c) ((sol w).u τ) haltCoordU -
                  BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU) -
                ∑ w' : UniversalLocalView,
                  (sol w).lam w' τ *
                    (BranchData.evalBranch (branchU c) ((sol w).u τ) haltCoordU -
                      BranchData.evalBranch (branchU w') ((sol w).u τ) haltCoordU))) -
        (((1 + Real.cos τ) / 2) ^ Mcy * (κ₀ : ℝ)) *
          (((Fintype.card UniversalLocalView : ℝ)⁻¹ *
              ∑ v : UniversalLocalView,
                (BranchData.evalBranch (branchU c) ((sol w).u τ) haltCoordU -
                  BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU)) -
            ∑ v : UniversalLocalView,
              (sol w).lam v τ *
                (BranchData.evalBranch (branchU c) ((sol w).u τ) haltCoordU -
                  BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU)))
  let activeBranchResidual : ℝ :=
    ∫ τ in (selectorMUEarlyWriteSubStart (j + 1))..
        (selectorMUWriteHoldTime (j + 1)),
      (∑ v : UniversalLocalView,
        (BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU -
          BranchData.evalBranch (branchU c) ((sol w).u τ) haltCoordU) *
          |(((1 + Real.cos τ) / 2) ^ Mcy * (κ₀ : ℝ)) *
              (Fintype.card UniversalLocalView : ℝ)⁻¹ -
            ((((1 + Real.cos τ) / 2) ^ Mcy * (κ₀ : ℝ)) +
              (((1 + Real.sin τ) / 2) ^ Mcy *
                ((g₀ : ℝ) * Real.exp (bgpParams38.cα * τ))) *
                (universalPval eta heta c ((sol w).u τ) -
                  universalPval eta heta v ((sol w).u τ))) *
              (sol w).lam v τ|) +
      (((1 + Real.sin τ) / 2) ^ Mcy *
        ((g₀ : ℝ) * Real.exp (bgpParams38.cα * τ))) *
        (∑ v : UniversalLocalView,
          (sol w).lam v τ *
            (universalPval eta heta c ((sol w).u τ) -
              universalPval eta heta v ((sol w).u τ))) *
        (∑ v : UniversalLocalView,
          (sol w).lam v τ *
            (BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU -
              BranchData.evalBranch (branchU c) ((sol w).u τ) haltCoordU))
  have hbase :=
    selectorMUHoffCapEdges_le_initial_add_gap_covariance_no_activeTrack
      (sol := sol) boxInputs w j henc
  have hactive :=
    selectorMUHoff_activeGapCovarianceVariation_le_branchResiduals_add_meanGapProduct_flip_original_of_nonneg
      (sol := sol) boxInputs hg₀_nonneg w j c
      (by simpa [c] using hD_nonneg)
      (by simpa [c] using hdelta_nonneg)
  dsimp only
  change
    selectorMUHoffCapLeftField sol w j + selectorMUHoffCapRightField sol w j ≤
      |(sol w).z (selectorMUInterReadStart j) haltCoordU - M| +
        2 * |(sol w).z (selectorMUZOffEnd j) haltCoordU - M| +
        2 * leftBad + 3 * rightCross + endpointBad + activeBranchResidual
  have hbase' :
      selectorMUHoffCapLeftField sol w j + selectorMUHoffCapRightField sol w j ≤
        |(sol w).z (selectorMUInterReadStart j) haltCoordU - M| +
          2 * |(sol w).z (selectorMUZOffEnd j) haltCoordU - M| +
          2 * leftBad + 3 * rightCross + endpointBad + activeVar := by
    simpa [M, leftBad, rightCross, endpointBad, activeVar, c] using hbase
  have hactive' : activeVar ≤ activeBranchResidual := by
    simpa [activeVar, activeBranchResidual, c] using hactive
  nlinarith [hbase', hactive']

/-- Active-suffix halt-branch defect nonnegativity from a pointwise active
halt target `1`.

This is deliberately conditional: the active next branch has halt target `1`
only on the halted side of the edge.  In nonhalting windows the analogous
unconditional statement is false. -/
theorem selectorMU_activeSuffix_hD_nonneg_of_active_halt_one
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (w j : ℕ)
    (hactive_one :
      ∀ τ ∈ Set.Icc (selectorMUEarlyWriteSubStart (j + 1))
          (selectorMUWriteHoldTime (j + 1)),
        BranchData.evalBranch
            (branchU (localViewU (solMUReplStaticCfg w (j + 1))))
            ((sol w).u τ) haltCoordU = 1) :
    ∀ τ ∈ Set.Icc (selectorMUEarlyWriteSubStart (j + 1))
        (selectorMUWriteHoldTime (j + 1)), ∀ v : UniversalLocalView,
      0 ≤ BranchData.evalBranch
          (branchU (localViewU (solMUReplStaticCfg w (j + 1))))
          ((sol w).u τ) haltCoordU -
        BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU := by
  intro τ hτ v
  exact branchU_halt_defect_nonneg_of_left_one
    (c := localViewU (solMUReplStaticCfg w (j + 1))) (v := v)
    (u := (sol w).u τ) (hactive_one τ hτ)

/-- Active-suffix halt-branch defect nonnegativity from the next encoded halt
target being `1`.  This is the concrete producer for the `hD_nonneg` side
condition in `selectorMUHoffCapEdges_le_initial_add_branchResidual_active_terms`
on halted edges. -/
theorem selectorMU_activeSuffix_hD_nonneg_of_next_halt_one
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (w j : ℕ)
    (hnext_one :
      stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 2)) haltCoordU = 1) :
    ∀ τ ∈ Set.Icc (selectorMUEarlyWriteSubStart (j + 1))
        (selectorMUWriteHoldTime (j + 1)), ∀ v : UniversalLocalView,
      0 ≤ BranchData.evalBranch
          (branchU (localViewU (solMUReplStaticCfg w (j + 1))))
          ((sol w).u τ) haltCoordU -
        BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU := by
  refine selectorMU_activeSuffix_hD_nonneg_of_active_halt_one
    (sol := sol) w j ?_
  intro τ _hτ
  have hbranch :=
    branchU_haltCoord_exact_independent (solMUReplStaticCfg w (j + 1))
      ((sol w).u τ)
  simpa [solMUReplStaticCfg_step w (j + 1), Nat.add_assoc, hnext_one] using hbranch

/-- Flipped active-suffix halt-branch defect nonnegativity from a pointwise
active halt target `0`. -/
theorem selectorMU_activeSuffix_hD_flip_nonneg_of_active_halt_zero
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (w j : ℕ)
    (hactive_zero :
      ∀ τ ∈ Set.Icc (selectorMUEarlyWriteSubStart (j + 1))
          (selectorMUWriteHoldTime (j + 1)),
        BranchData.evalBranch
            (branchU (localViewU (solMUReplStaticCfg w (j + 1))))
            ((sol w).u τ) haltCoordU = 0) :
    ∀ τ ∈ Set.Icc (selectorMUEarlyWriteSubStart (j + 1))
        (selectorMUWriteHoldTime (j + 1)), ∀ v : UniversalLocalView,
      0 ≤ BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU -
        BranchData.evalBranch
          (branchU (localViewU (solMUReplStaticCfg w (j + 1))))
          ((sol w).u τ) haltCoordU := by
  intro τ hτ v
  exact branchU_halt_defect_nonneg_of_right_zero
    (c := localViewU (solMUReplStaticCfg w (j + 1))) (v := v)
    (u := (sol w).u τ) (hactive_zero τ hτ)

/-- Flipped active-suffix halt-branch defect nonnegativity from the next
encoded halt target being `0`. -/
theorem selectorMU_activeSuffix_hD_flip_nonneg_of_next_halt_zero
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (w j : ℕ)
    (hnext_zero :
      stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 2)) haltCoordU = 0) :
    ∀ τ ∈ Set.Icc (selectorMUEarlyWriteSubStart (j + 1))
        (selectorMUWriteHoldTime (j + 1)), ∀ v : UniversalLocalView,
      0 ≤ BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU -
        BranchData.evalBranch
          (branchU (localViewU (solMUReplStaticCfg w (j + 1))))
          ((sol w).u τ) haltCoordU := by
  refine selectorMU_activeSuffix_hD_flip_nonneg_of_active_halt_zero
    (sol := sol) w j ?_
  intro τ _hτ
  have hbranch :=
    branchU_haltCoord_exact_independent (solMUReplStaticCfg w (j + 1))
      ((sol w).u τ)
  simpa [solMUReplStaticCfg_step w (j + 1), Nat.add_assoc, hnext_zero] using hbranch

/-- Selector payoff defect nonnegativity from the concrete universal `UTube`.

Inside the encoding tube of `c`, `localViewU c` is the coarse selector winner,
so its universal payoff is no smaller than any competing local view payoff. -/
theorem selectorMU_universalPval_defect_nonneg_of_utube
    {eta : ℚ} {heta : 0 < eta} {c : UConf} {u : Fin d_U → ℝ}
    (herr :
      (gateSelectorAtomsCoordN (universalGateAtoms eta heta)).errSel < 1 / 2)
    (hutube : UTube r_LE_U c u) :
    ∀ v : UniversalLocalView,
      0 ≤ universalPval eta heta (localViewU c) u -
        universalPval eta heta v u := by
  intro v
  by_cases hv : v = localViewU c
  · subst v
    simp
  · have hmargins :=
      universal_selector_margins_of_tube (eta := eta) (heta := heta)
        (c := c) (Z := u) hutube herr
    have hwinner :
        1 / 2 - (gateSelectorAtomsCoordN (universalGateAtoms eta heta)).errSel ≤
          universalPval eta heta (localViewU c) u := by
      simpa [universalPval] using hmargins.1
    have hloser :
        universalPval eta heta v u ≤
          -(1 / 2 - (gateSelectorAtomsCoordN (universalGateAtoms eta heta)).errSel) := by
      simpa [universalPval] using hmargins.2 v hv
    have hmargin_pos :
        0 < 1 / 2 - (gateSelectorAtomsCoordN (universalGateAtoms eta heta)).errSel := by
      linarith
    linarith

/-- Active-suffix selector payoff defect nonnegativity from a pointwise active
`UTube` hypothesis. -/
theorem selectorMU_activeSuffix_hdelta_nonneg_of_utube
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (herr :
      (gateSelectorAtomsCoordN (universalGateAtoms eta heta)).errSel < 1 / 2)
    (w j : ℕ)
    (hutube :
      ∀ τ ∈ Set.Icc (selectorMUEarlyWriteSubStart (j + 1))
          (selectorMUWriteHoldTime (j + 1)),
        UTube r_LE_U (solMUReplStaticCfg w (j + 1)) ((sol w).u τ)) :
    ∀ τ ∈ Set.Icc (selectorMUEarlyWriteSubStart (j + 1))
        (selectorMUWriteHoldTime (j + 1)), ∀ v : UniversalLocalView,
      0 ≤ universalPval eta heta
          (localViewU (solMUReplStaticCfg w (j + 1))) ((sol w).u τ) -
        universalPval eta heta v ((sol w).u τ) := by
  intro τ hτ v
  exact selectorMU_universalPval_defect_nonneg_of_utube
    (eta := eta) (heta := heta) (c := solMUReplStaticCfg w (j + 1))
    (u := (sol w).u τ) herr (hutube τ hτ) v

/-- Active-suffix selector payoff defect nonnegativity from the existing full
write-window `UTube` residual. -/
theorem selectorMU_activeSuffix_hdelta_nonneg_of_full_utube
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (fullUTube : SelectorMUWriteFullUTubeResidual sol)
    (herr :
      (gateSelectorAtomsCoordN (universalGateAtoms eta heta)).errSel < 1 / 2)
    (w j : ℕ) :
    ∀ τ ∈ Set.Icc (selectorMUEarlyWriteSubStart (j + 1))
        (selectorMUWriteHoldTime (j + 1)), ∀ v : UniversalLocalView,
      0 ≤ universalPval eta heta
          (localViewU (solMUReplStaticCfg w (j + 1))) ((sol w).u τ) -
        universalPval eta heta v ((sol w).u τ) := by
  refine selectorMU_activeSuffix_hdelta_nonneg_of_utube
    (sol := sol) herr w j ?_
  intro τ hτ
  have hstart :
      selectorMUWriteStartTime (j + 1) ≤ selectorMUEarlyWriteSubStart (j + 1) :=
    selectorMUWriteStart_le_earlySubStart (j + 1)
  have hread :
      selectorMUWriteHoldTime (j + 1) < selectorMUWriteReadTime (j + 1) := by
    unfold selectorMUWriteHoldTime selectorMUWriteReadTime
    linarith [Real.pi_pos]
  have ht :
      τ ∈ Ico (selectorMUWriteStartTime (j + 1))
          (selectorMUWriteReadTime (j + 1)) :=
    ⟨le_trans hstart hτ.1, lt_of_le_of_lt hτ.2 hread⟩
  exact fullUTube.hutube_win w (j + 1) τ ht

/-- Active-suffix selector payoff defect has the full concrete selector gap on
every non-active view. -/
theorem selectorMU_activeSuffix_hdelta_ge_gap_of_full_utube
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (fullUTube : SelectorMUWriteFullUTubeResidual sol)
    (herr :
      (gateSelectorAtomsCoordN (universalGateAtoms eta heta)).errSel < 1 / 2)
    (w j : ℕ) :
    ∀ τ ∈ Set.Icc (selectorMUEarlyWriteSubStart (j + 1))
        (selectorMUWriteHoldTime (j + 1)), ∀ v : UniversalLocalView,
      v ≠ localViewU (solMUReplStaticCfg w (j + 1)) →
      selectorReplicatorGapVal eta heta ≤
        universalPval eta heta
            (localViewU (solMUReplStaticCfg w (j + 1))) ((sol w).u τ) -
          universalPval eta heta v ((sol w).u τ) := by
  intro τ hτ v hv
  have hstart :
      selectorMUWriteStartTime (j + 1) ≤ selectorMUEarlyWriteSubStart (j + 1) :=
    selectorMUWriteStart_le_earlySubStart (j + 1)
  have hread :
      selectorMUWriteHoldTime (j + 1) < selectorMUWriteReadTime (j + 1) := by
    unfold selectorMUWriteHoldTime selectorMUWriteReadTime
    linarith [Real.pi_pos]
  have ht :
      τ ∈ Ico (selectorMUWriteStartTime (j + 1))
          (selectorMUWriteReadTime (j + 1)) :=
    ⟨le_trans hstart hτ.1, lt_of_le_of_lt hτ.2 hread⟩
  have hgap_full :=
    selector_replicator_hgap_of_utube
      (sol := fun _ : ℕ => sol w)
      (cfg := fun _ k => solMUReplStaticCfg w k)
      herr
      (fun _ k t ht => fullUTube.hutube_win w k t ht)
  have hraw :
      universalPval eta heta v ((sol w).u τ) -
        universalPval eta heta
          (localViewU (solMUReplStaticCfg w (j + 1))) ((sol w).u τ)
        ≤ -selectorReplicatorGapVal eta heta := by
    simpa using hgap_full 0 (j + 1) v hv τ ht
  linarith

/-- Candidate weighted active-write mix radius. -/
def selectorMUWeightedHoldMixDelta
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀)
    (shifted : ∀ w, MUReplicatorShiftedConcentrationAt sol w)
    (gap R0 : ℝ) : ℕ → ℕ → ℝ :=
  fun w j =>
    Real.exp (-(selectorEarlyWriteIntLower j)) +
      (Fintype.card UniversalLocalView : ℝ) *
        epsLamShiftedEarlyFullAt sol w gap R0 j +
      (Fintype.card UniversalLocalView : ℝ) * (shifted w).epsLam j

/-- The weighted active-write mix radius tends to zero. -/
theorem selectorMUWeightedHoldMixDelta_tendsto_zero
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀)
    (shifted : ∀ w, MUReplicatorShiftedConcentrationAt sol w)
    (w : ℕ) {gap R0 : ℝ}
    (hg₀ : 0 < (g₀ : ℝ))
    (hgap0 : 0 < gap)
    (hR0_nonneg : 0 ≤ R0)
    (hκ₀_nonneg : 0 ≤ (κ₀ : ℝ))
    (hscale : (κ₀ : ℝ) ≤ ((3 / 4 : ℝ) ^ Mcy) * (g₀ : ℝ)) :
    Tendsto (selectorMUWeightedHoldMixDelta sol shifted gap R0 w) atTop (𝓝 0) := by
  have hearlyExp :
      Tendsto (fun j : ℕ => Real.exp (-(selectorEarlyWriteIntLower j)))
        atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp
      (tendsto_neg_atBot_iff.mpr selectorEarlyWriteIntLower_tendsto_atTop)
  have hearly :=
    epsLamShiftedEarlyFull_tendsto_zero sol w hg₀ hgap0 hR0_nonneg
      hκ₀_nonneg hscale
  have hhold := (shifted w).hεLam
  unfold selectorMUWeightedHoldMixDelta
  simpa [add_assoc] using
    (hearlyExp.add
      (Filter.Tendsto.const_mul (Fintype.card UniversalLocalView : ℝ) hearly)).add
        (Filter.Tendsto.const_mul (Fintype.card UniversalLocalView : ℝ) hhold)

/-- Nonnegativity of the weighted active-write mix radius. -/
theorem selectorMUWeightedHoldMixDelta_nonneg
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (shifted : ∀ w, MUReplicatorShiftedConcentrationAt sol w)
    {gap R0 : ℝ}
    (hgap0 : 0 < gap)
    (hR0_nonneg : 0 ≤ R0)
    (hκ₀_nonneg : 0 ≤ (κ₀ : ℝ)) :
    ∀ w j, 0 ≤ selectorMUWeightedHoldMixDelta sol shifted gap R0 w j := by
  intro w j
  unfold selectorMUWeightedHoldMixDelta
  exact add_nonneg
    (add_nonneg (Real.exp_nonneg _)
      (mul_nonneg (Nat.cast_nonneg _)
        (epsLamShiftedEarlyFullAt_nonneg sol w hgap0 hR0_nonneg hκ₀_nonneg j)))
    (mul_nonneg (Nat.cast_nonneg _) ((shifted w).hεLam_nonneg j))

/-- True next-write frontier for the active z-write window.

The uniform frozen-mix condition on the whole `[WriteStart, WriteHold]` window is
only a strong sufficient hypothesis.  The z-write equation actually pays
target variation through the Duhamel kernel below, so this weighted residual is
the intended analytic surface for replacing the over-strong hold-stability
route. -/
structure MUReplicatorNextWriteStartWeightedHoldMixResidual
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀) where
  δw : ℕ → ℕ → ℝ
  hδw : ∀ w, Tendsto (δw w) atTop (𝓝 0)
  hδw_nonneg : ∀ w j, 0 ≤ δw w j
  hmix_weighted_z_write_hold : ∀ w j,
    (∫ τ in (selectorMUWriteStartTime j)..(selectorMUWriteHoldTime j),
      Real.exp (-(∫ σ in τ..(selectorMUWriteHoldTime j),
        bgpParams38.A * (sol w).α σ *
          bGateZ bgpParams38.L ((sol w).μ σ) σ)) *
      (bgpParams38.A * (sol w).α τ *
        bGateZ bgpParams38.L ((sol w).μ τ) τ) *
      |selectorMixTarget branchU (sol w).u (sol w).lam τ haltCoordU -
        selectorMixTarget branchU (sol w).u (sol w).lam
          (selectorMUWriteHoldTime j) haltCoordU|) ≤ δw w j

def selectorMUWeightedHoldMixResidual_of_shifted
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀)
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (shifted : ∀ w, MUReplicatorShiftedConcentrationAt sol w)
    (herr : (gateSelectorAtomsCoordN (universalGateAtoms eta heta)).errSel < 1 / 2)
    (hκ₀_nonneg : 0 ≤ (κ₀ : ℝ))
    (hg₀ : 0 < (g₀ : ℝ))
    (hscale : (κ₀ : ℝ) ≤ ((3 / 4 : ℝ) ^ Mcy) * (g₀ : ℝ))
    (hselect_start : ∀ w j,
      1 / (Fintype.card UniversalLocalView : ℝ) ≤
        (sol w).lam (localViewU (solMUReplStaticCfg w j))
          (selectorMUSelectStartTime j))
    (hutube_win : ∀ w j, ∀ t ∈ Set.Ico (selectorMUWriteStartTime j)
        (selectorMUWriteReadTime j),
      UTube r_LE_U (solMUReplStaticCfg w j) ((sol w).u t)) :
    MUReplicatorNextWriteStartWeightedHoldMixResidual sol where
  δw := selectorMUWeightedHoldMixDelta sol shifted
    (selectorReplicatorGapVal eta heta) (Fintype.card UniversalLocalView : ℝ)
  hδw := by
    intro w
    exact selectorMUWeightedHoldMixDelta_tendsto_zero sol shifted w hg₀
      (by simpa using solMURepl_static_hgap0 eta heta herr)
      (by positivity) hκ₀_nonneg hscale
  hδw_nonneg := by
    intro w j
    exact selectorMUWeightedHoldMixDelta_nonneg shifted
      (by simpa using solMURepl_static_hgap0 eta heta herr)
      (by positivity) hκ₀_nonneg w j
  hmix_weighted_z_write_hold := by
    classical
    haveI : Nonempty UniversalLocalView := ⟨defaultLocalViewU⟩
    intro w j
    let gap : ℝ := selectorReplicatorGapVal eta heta
    let R0 : ℝ := Fintype.card UniversalLocalView
    let W : ℝ := selectorMUWriteStartTime j
    let E : ℝ := selectorMUEarlyWriteSubStart j
    let H : ℝ := selectorMUWriteHoldTime j
    let k : ℝ → ℝ := fun t =>
      bgpParams38.A * (sol w).α t * bGateZ bgpParams38.L ((sol w).μ t) t
    let d : ℝ → ℝ := fun t =>
      selectorMixTarget branchU (sol w).u (sol w).lam t haltCoordU -
        selectorMixTarget branchU (sol w).u (sol w).lam H haltCoordU
    let C : ℝ :=
      (Fintype.card UniversalLocalView : ℝ) *
          epsLamShiftedEarlyFullAt sol w gap R0 j +
        (Fintype.card UniversalLocalView : ℝ) * (shifted w).epsLam j
    have hgap0 : 0 < gap := by
      simpa [gap] using solMURepl_static_hgap0 eta heta herr
    have hR0_nonneg : 0 ≤ R0 := by
      dsimp [R0]
      positivity
    have hsum_forward := solMURepl_static_lam_sum_forward (sol := sol) boxInputs
    have hlam_forward := solMURepl_static_lam_nonneg_forward (sol := sol) boxInputs
    have hqL_select :
        ∀ t ∈ Icc (selectorMUSelectStartTime j) (selectorMUWriteHoldTime j),
          1 / (Fintype.card UniversalLocalView : ℝ) ≤
            (sol w).lam (localViewU (solMUReplStaticCfg w j)) t := by
      have hgap_floor :
          ∀ v : UniversalLocalView, v ≠ localViewU (solMUReplStaticCfg w j) →
            ∀ t ∈ Ico (selectorMUSelectStartTime j) (selectorMUWriteHoldTime j),
              universalPval eta heta v ((sol w).u t) -
                universalPval eta heta (localViewU (solMUReplStaticCfg w j))
                  ((sol w).u t) ≤ 0 := by
        intro v hv t ht
        have hgap_full :=
          selector_replicator_hgap_of_utube
            (sol := fun _ : ℕ => sol w)
            (cfg := fun _ j => solMUReplStaticCfg w j)
            herr
            (fun _ j t ht => hutube_win w j t ht)
        have hnonpos : -gap ≤ 0 := neg_nonpos.mpr hgap0.le
        exact le_trans
          (by
            have ht_full : t ∈ Ico (selectorMUWriteStartTime j)
                (selectorMUWriteReadTime j) :=
              ⟨le_trans (selectorMUWriteStart_le_selectStart j) ht.1,
                lt_of_lt_of_le ht.2 (selectorMUWriteHold_le_read j)⟩
            simpa [gap] using hgap_full 0 j v hv t ht_full)
          hnonpos
      have hbar :=
        replicator_winner_floor_on_interval_param
          (sol := sol w) (localViewU (solMUReplStaticCfg w j))
          (a := selectorMUSelectStartTime j) (b := selectorMUWriteHoldTime j)
          (le_of_lt (selectorMUSelectStart_lt_hold j))
          (1 / (Fintype.card UniversalLocalView : ℝ)) (le_refl _)
          (fun t ht => solMURepl_static_hdom_nonneg t
            (le_trans (selectorMUSelectStart_nonneg_weighted j) ht.1))
          (fun t _ht => boxInputs.hcr_nonneg t)
          (fun t _ht =>
            mul_nonneg
              (pow_nonneg (by nlinarith [Real.neg_one_le_sin t]) _)
              (mul_nonneg hg₀.le (Real.exp_pos _).le))
          hgap_floor
          (fun t ht => hsum_forward w t
            (le_trans (selectorMUSelectStart_nonneg_weighted j) ht.1))
          (fun v t ht => hlam_forward w v t
            (le_trans (selectorMUSelectStart_nonneg_weighted j) ht.1))
          (hselect_start w j)
      exact hbar
    have hRa_select :
        ∀ v : UniversalLocalView, v ≠ localViewU (solMUReplStaticCfg w j) →
          (sol w).lam v (selectorMUSelectStartTime j) /
              (sol w).lam (localViewU (solMUReplStaticCfg w j))
                (selectorMUSelectStartTime j) ≤ R0 := by
      have hsum := hsum_forward w (selectorMUSelectStartTime j)
        (selectorMUSelectStart_nonneg_weighted j)
      have hnonneg : ∀ v : UniversalLocalView,
          0 ≤ (sol w).lam v (selectorMUSelectStartTime j) :=
        fun v => hlam_forward w v (selectorMUSelectStartTime j)
          (selectorMUSelectStart_nonneg_weighted j)
      simpa [R0] using
        lam_ratio_card_bound_at_weighted
          (lam := fun v : UniversalLocalView =>
            (sol w).lam v (selectorMUSelectStartTime j))
          (vstar := localViewU (solMUReplStaticCfg w j))
          hsum hnonneg (hselect_start w j)
    have hgap_cond :
        ∀ v : UniversalLocalView, v ≠ localViewU (solMUReplStaticCfg w j) →
          ∀ t ∈ Ico (selectorMUSelectStartTime j) (selectorMUWriteHoldTime j),
            universalPval eta heta v ((sol w).u t) -
              universalPval eta heta (localViewU (solMUReplStaticCfg w j))
                ((sol w).u t) ≤ -gap := by
      intro v hv t ht
      have hgap_full :=
        selector_replicator_hgap_of_utube
          (sol := fun _ : ℕ => sol w)
          (cfg := fun _ j => solMUReplStaticCfg w j)
          herr
          (fun _ j t ht => hutube_win w j t ht)
      have ht_full : t ∈ Ico (selectorMUWriteStartTime j)
          (selectorMUWriteReadTime j) :=
        ⟨le_trans (selectorMUWriteStart_le_selectStart j) ht.1,
          lt_of_lt_of_le ht.2 (selectorMUWriteHold_le_read j)⟩
      simpa [gap] using hgap_full 0 j v hv t ht_full
    have hloser_early :
        ∀ t ∈ Icc E H,
          (Finset.univ.filter (fun v : UniversalLocalView =>
            v ≠ localViewU (solMUReplStaticCfg w j))).sum
              (fun v => (sol w).lam v t) ≤
            epsLamShiftedEarlyFullAt sol w gap R0 j := by
      dsimp [E, H]
      exact hloser_of_shifted_concentration_from_early
        (sol := sol) (cfg := fun j => solMUReplStaticCfg w j)
        w j (gap := gap) (R0 := R0)
        hgap0 hR0_nonneg hκ₀_nonneg hscale
        (fun t ht => solMURepl_static_hdom_nonneg t
          (le_trans (selectorMUSelectStart_nonneg_weighted j) ht.1))
        hqL_select
        (fun v t ht => hlam_forward w v t
          (le_trans (selectorMUSelectStart_nonneg_weighted j) ht.1))
        (fun t ht => hsum_forward w t
          (le_trans (selectorMUSelectStart_nonneg_weighted j) ht.1))
        hgap_cond
        hRa_select
    have hC_nonneg : 0 ≤ C := by
      dsimp [C]
      exact add_nonneg
        (mul_nonneg (Nat.cast_nonneg _)
          (epsLamShiftedEarlyFullAt_nonneg sol w hgap0 hR0_nonneg hκ₀_nonneg j))
        (mul_nonneg (Nat.cast_nonneg _) ((shifted w).hεLam_nonneg j))
    have hk_cont : Continuous k := by
      dsimp [k]
      exact selector_replicator_gateZ_integrand_continuous (sol w)
    have hd_cont : Continuous d := by
      dsimp [d, H]
      exact ((sol w).cont_mixTarget haltCoordU).sub continuous_const
    have hk_nonneg : ∀ t ∈ Icc W H, 0 ≤ k t := by
      intro t ht
      dsimp [k]
      have ht0 : 0 ≤ t := le_trans (selectorMUWriteStartTime_nonneg j) ht.1
      exact selector_replicator_gateZ_integrand_nonneg (sol w)
        selectorSchedule_domain_of_nonneg_structural (by norm_num [bgpParams38]) ht0
    have hprefix : ∀ t ∈ Icc W E, |d t| ≤ (1 : ℝ) := by
      intro t ht
      dsimp [d, W, E, H]
      have ht0 : 0 ≤ t := le_trans (selectorMUWriteStartTime_nonneg j) ht.1
      have hH0 : 0 ≤ selectorMUWriteHoldTime j :=
        le_trans (selectorMUWriteStartTime_nonneg j) (selectorMUWriteStart_le_hold j)
      exact halt_mixTarget_abs_sub_le_one boxInputs w ht0 hH0
    have hsuffix : ∀ t ∈ Icc E H, |d t| ≤ C := by
      intro t ht
      dsimp [d, C, E, H]
      have ht0 : 0 ≤ t := by
        exact le_trans (selectorMUWriteStartTime_nonneg j)
          (le_trans (selectorMUWriteStart_le_earlySubStart j) ht.1)
      have hH0 : 0 ≤ selectorMUWriteHoldTime j :=
        le_trans (selectorMUWriteStartTime_nonneg j) (selectorMUWriteStart_le_hold j)
      have hsumT := hsum_forward w t ht0
      have hsumH := hsum_forward w (selectorMUWriteHoldTime j) hH0
      have hlamT := hlam_forward w
      have hlamH := hlam_forward w
      have hlate := selectorMixTarget_halt_pair_of_loser_sum
        (u := (sol w).u) (Λ := (sol w).lam)
        (t := t) (s := selectorMUWriteHoldTime j)
        (c := solMUReplStaticCfg w j)
        (epsT := epsLamShiftedEarlyFullAt sol w gap R0 j)
        (epsS := (shifted w).epsLam j)
        hsumT hsumH
        (fun v => hlamT v t ht0)
        (fun v => hlamH v (selectorMUWriteHoldTime j) hH0)
        (hloser_early t ht)
        ((shifted w).p_hloser j (selectorMUWriteHoldTime j)
          ⟨le_rfl, selectorMUWriteHold_le_read j⟩)
      simpa [add_assoc] using hlate
    have hkernel :=
      terminal_kernel_split_abs_bound k d W E H C
        (selectorMUWriteStart_le_earlySubStart j)
        (selectorMUEarlySubStart_le_writeHold j)
        hk_cont hd_cont hk_nonneg hprefix hsuffix hC_nonneg
    have htail_lower :
        selectorEarlyWriteIntLower j ≤ ∫ s in E..H, k s := by
      dsimp [E, H, k]
      exact selector_early_writeIntegral_lower_sub_lbd_repl (sol w) j
        selectorSchedule_domain_of_nonneg_structural
        (selector_replicator_gateZ_integrand_continuous (sol w))
    have hexp_mono :
        Real.exp (-(∫ s in E..H, k s)) ≤
          Real.exp (-(selectorEarlyWriteIntLower j)) := by
      exact Real.exp_le_exp.mpr (neg_le_neg htail_lower)
    calc
      (∫ τ in (selectorMUWriteStartTime j)..(selectorMUWriteHoldTime j),
        Real.exp (-(∫ σ in τ..(selectorMUWriteHoldTime j),
          bgpParams38.A * (sol w).α σ *
            bGateZ bgpParams38.L ((sol w).μ σ) σ)) *
        (bgpParams38.A * (sol w).α τ *
          bGateZ bgpParams38.L ((sol w).μ τ) τ) *
        |selectorMixTarget branchU (sol w).u (sol w).lam τ haltCoordU -
          selectorMixTarget branchU (sol w).u (sol w).lam
            (selectorMUWriteHoldTime j) haltCoordU|)
          = ∫ τ in W..H,
              Real.exp (-(∫ σ in τ..H, k σ)) * k τ * |d τ| := by
            simp [W, H, k, d]
      _ ≤ Real.exp (-(∫ s in E..H, k s)) + C := hkernel
      _ ≤ Real.exp (-(selectorEarlyWriteIntLower j)) + C :=
        by simpa [add_comm] using add_le_add_left hexp_mono C
      _ ≤ selectorMUWeightedHoldMixDelta sol shifted gap R0 w j := by
        simp [selectorMUWeightedHoldMixDelta, C, gap, R0, add_assoc]

/-- Late right-edge halt mix bound from the shifted concentration package.

This covers the portion
`[selectorMUEarlyWriteSubStart (j+1), selectorMUWriteHoldTime (j+1)]`
of the right `hoff` edge.  The target is rewritten from the next-cycle halt
target to the previous halt target using `selectorMUHaltEncConstW`, so the
statement is directly usable in the right-cap scalar estimate. -/
theorem selectorMUHoff_right_late_mix_integral_le_of_shifted
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀)
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (herr : (gateSelectorAtomsCoordN (universalGateAtoms eta heta)).errSel < 1 / 2)
    (hκ₀_nonneg : 0 ≤ (κ₀ : ℝ))
    (hg₀ : 0 < (g₀ : ℝ))
    (hscale : (κ₀ : ℝ) ≤ ((3 / 4 : ℝ) ^ Mcy) * (g₀ : ℝ))
    (hselect_start : ∀ w j,
      1 / (Fintype.card UniversalLocalView : ℝ) ≤
        (sol w).lam (localViewU (solMUReplStaticCfg w j))
          (selectorMUSelectStartTime j))
    (hutube_win : ∀ w j, ∀ t ∈ Set.Ico (selectorMUWriteStartTime j)
        (selectorMUWriteReadTime j),
      UTube r_LE_U (solMUReplStaticCfg w j) ((sol w).u t)) :
    ∀ w j, selectorMUHaltEncConstW solMUReplStaticCfg w j →
      (∫ τ in (selectorMUEarlyWriteSubStart (j + 1))..
          (selectorMUWriteHoldTime (j + 1)),
        selectorMUHoffGateCoeff sol w τ *
          |selectorMixTarget branchU (sol w).u (sol w).lam τ haltCoordU -
            stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 1)) haltCoordU|)
      ≤
      (∫ τ in (selectorMUEarlyWriteSubStart (j + 1))..
          (selectorMUWriteHoldTime (j + 1)),
        selectorMUHoffGateCoeff sol w τ *
          epsLamShiftedEarlyFullAt sol w
            (selectorReplicatorGapVal eta heta)
            (Fintype.card UniversalLocalView : ℝ) (j + 1)) := by
  classical
  haveI : Nonempty UniversalLocalView := ⟨defaultLocalViewU⟩
  intro w j henc
  let n : ℕ := j + 1
  let gap : ℝ := selectorReplicatorGapVal eta heta
  let R0 : ℝ := Fintype.card UniversalLocalView
  let E : ℝ := selectorMUEarlyWriteSubStart n
  let H : ℝ := selectorMUWriteHoldTime n
  let C : ℝ :=
    epsLamShiftedEarlyFullAt sol w gap R0 n
  let k : ℝ → ℝ := fun t => selectorMUHoffGateCoeff sol w t
  let m : ℝ → ℝ := fun t =>
    selectorMixTarget branchU (sol w).u (sol w).lam t haltCoordU
  let M : ℝ := stackMachineEncodingU.enc (solMUReplStaticCfg w n) haltCoordU
  have hgap0 : 0 < gap := by
    simpa [gap] using solMURepl_static_hgap0 eta heta herr
  have hR0_nonneg : 0 ≤ R0 := by
    dsimp [R0]
    positivity
  have hsum_forward := solMURepl_static_lam_sum_forward (sol := sol) boxInputs
  have hlam_forward := solMURepl_static_lam_nonneg_forward (sol := sol) boxInputs
  have hn_nonneg : 0 ≤ selectorMUSelectStartTime n :=
    selectorMUSelectStart_nonneg_weighted n
  have hqL_select :
      ∀ t ∈ Icc (selectorMUSelectStartTime n) (selectorMUWriteHoldTime n),
        1 / (Fintype.card UniversalLocalView : ℝ) ≤
          (sol w).lam (localViewU (solMUReplStaticCfg w n)) t := by
    have hgap_floor :
        ∀ v : UniversalLocalView, v ≠ localViewU (solMUReplStaticCfg w n) →
          ∀ t ∈ Ico (selectorMUSelectStartTime n) (selectorMUWriteHoldTime n),
            universalPval eta heta v ((sol w).u t) -
              universalPval eta heta (localViewU (solMUReplStaticCfg w n))
                ((sol w).u t) ≤ 0 := by
      intro v hv t ht
      have hgap_full :=
        selector_replicator_hgap_of_utube
          (sol := fun _ : ℕ => sol w)
          (cfg := fun _ j => solMUReplStaticCfg w j)
          herr
          (fun _ j t ht => hutube_win w j t ht)
      have hnonpos : -gap ≤ 0 := neg_nonpos.mpr hgap0.le
      exact le_trans
        (by
          have ht_full : t ∈ Ico (selectorMUWriteStartTime n)
              (selectorMUWriteReadTime n) :=
            ⟨le_trans (selectorMUWriteStart_le_selectStart n) ht.1,
              lt_of_lt_of_le ht.2 (selectorMUWriteHold_le_read n)⟩
          simpa [gap] using hgap_full 0 n v hv t ht_full)
        hnonpos
    exact
      replicator_winner_floor_on_interval_param
        (sol := sol w) (localViewU (solMUReplStaticCfg w n))
        (a := selectorMUSelectStartTime n) (b := selectorMUWriteHoldTime n)
        (le_of_lt (selectorMUSelectStart_lt_hold n))
        (1 / (Fintype.card UniversalLocalView : ℝ)) (le_refl _)
        (fun t ht => solMURepl_static_hdom_nonneg t
          (le_trans hn_nonneg ht.1))
        (fun t _ht => boxInputs.hcr_nonneg t)
        (fun t _ht =>
          mul_nonneg
            (pow_nonneg (by nlinarith [Real.neg_one_le_sin t]) _)
            (mul_nonneg hg₀.le (Real.exp_pos _).le))
        hgap_floor
        (fun t ht => hsum_forward w t (le_trans hn_nonneg ht.1))
        (fun v t ht => hlam_forward w v t (le_trans hn_nonneg ht.1))
        (hselect_start w n)
  have hRa_select :
      ∀ v : UniversalLocalView, v ≠ localViewU (solMUReplStaticCfg w n) →
        (sol w).lam v (selectorMUSelectStartTime n) /
            (sol w).lam (localViewU (solMUReplStaticCfg w n))
              (selectorMUSelectStartTime n) ≤ R0 := by
    have hsum := hsum_forward w (selectorMUSelectStartTime n) hn_nonneg
    have hnonneg : ∀ v : UniversalLocalView,
        0 ≤ (sol w).lam v (selectorMUSelectStartTime n) :=
      fun v => hlam_forward w v (selectorMUSelectStartTime n) hn_nonneg
    simpa [R0] using
      lam_ratio_card_bound_at_weighted
        (lam := fun v : UniversalLocalView =>
          (sol w).lam v (selectorMUSelectStartTime n))
        (vstar := localViewU (solMUReplStaticCfg w n))
        hsum hnonneg (hselect_start w n)
  have hgap_cond :
      ∀ v : UniversalLocalView, v ≠ localViewU (solMUReplStaticCfg w n) →
        ∀ t ∈ Ico (selectorMUSelectStartTime n) (selectorMUWriteHoldTime n),
          universalPval eta heta v ((sol w).u t) -
            universalPval eta heta (localViewU (solMUReplStaticCfg w n))
              ((sol w).u t) ≤ -gap := by
    intro v hv t ht
    have hgap_full :=
      selector_replicator_hgap_of_utube
        (sol := fun _ : ℕ => sol w)
        (cfg := fun _ j => solMUReplStaticCfg w j)
        herr
        (fun _ j t ht => hutube_win w j t ht)
    have ht_full : t ∈ Ico (selectorMUWriteStartTime n)
        (selectorMUWriteReadTime n) :=
      ⟨le_trans (selectorMUWriteStart_le_selectStart n) ht.1,
        lt_of_lt_of_le ht.2 (selectorMUWriteHold_le_read n)⟩
    simpa [gap] using hgap_full 0 n v hv t ht_full
  have hloser_early :
      ∀ t ∈ Icc E H,
        (Finset.univ.filter (fun v : UniversalLocalView =>
          v ≠ localViewU (solMUReplStaticCfg w n))).sum
            (fun v => (sol w).lam v t) ≤
          epsLamShiftedEarlyFullAt sol w gap R0 n := by
    dsimp [E, H]
    exact hloser_of_shifted_concentration_from_early
      (sol := sol) (cfg := fun j => solMUReplStaticCfg w j)
      w n (gap := gap) (R0 := R0)
      hgap0 hR0_nonneg hκ₀_nonneg hscale
      (fun t ht => solMURepl_static_hdom_nonneg t
        (le_trans hn_nonneg ht.1))
      hqL_select
      (fun v t ht => hlam_forward w v t (le_trans hn_nonneg ht.1))
      (fun t ht => hsum_forward w t (le_trans hn_nonneg ht.1))
      hgap_cond
      hRa_select
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    exact epsLamShiftedEarlyFullAt_nonneg sol w hgap0 hR0_nonneg hκ₀_nonneg n
  have hmix_bound : ∀ t ∈ Icc E H, |m t - M| ≤ C := by
    intro t ht
    have ht0 : 0 ≤ t := by
      exact le_trans (selectorMUWriteStartTime_nonneg n)
        (le_trans (selectorMUWriteStart_le_earlySubStart n) ht.1)
    have hraw := selectorMixTarget_halt_to_next_of_loser_sum_sharp
      (sol w).u (sol w).lam t (solMUReplStaticCfg w n)
      (hsum_forward w t ht0)
      (fun v => hlam_forward w v t ht0)
      (hloser_early t ht)
    have htarget :
        stackMachineEncodingU.enc (solMUReplStaticCfg w (n + 1)) haltCoordU =
          M := by
      simpa [selectorMUHaltEncConstW, selectorMUHaltEncConst, n, M,
        Nat.add_assoc] using henc
    dsimp [m, M, C]
    simpa [solMUReplStaticCfg_step, htarget, n, gap, R0] using hraw
  have hab : E ≤ H := by
    simpa [E, H] using selectorMUEarlySubStart_le_writeHold n
  have hk_cont : Continuous k := by
    simpa [k, selectorMUHoffGateCoeff] using
      selector_replicator_gateZ_integrand_continuous (sol w)
  have hm_cont : Continuous fun t : ℝ => |m t - M| := by
    dsimp [m, M]
    exact (((sol w).cont_mixTarget haltCoordU).sub continuous_const).abs
  have hright_cont : Continuous fun t : ℝ => k t * C := by
    exact hk_cont.mul continuous_const
  have hk_nonneg : ∀ t ∈ Icc E H, 0 ≤ k t := by
    intro t ht
    have ht0 : 0 ≤ t := by
      exact le_trans (selectorMUWriteStartTime_nonneg n)
        (le_trans (selectorMUWriteStart_le_earlySubStart n) ht.1)
    simpa [k, selectorMUHoffGateCoeff] using
      selector_replicator_gateZ_integrand_nonneg (sol w)
        selectorSchedule_domain_of_nonneg_structural (by norm_num [bgpParams38]) ht0
  have hmono :
      (∫ τ in E..H, k τ * |m τ - M|) ≤
        ∫ τ in E..H, k τ * C := by
    apply intervalIntegral.integral_mono_on hab
    · exact (hk_cont.mul hm_cont).intervalIntegrable E H
    · exact hright_cont.intervalIntegrable E H
    · intro τ hτ
      exact mul_le_mul_of_nonneg_left (hmix_bound τ hτ) (hk_nonneg τ hτ)
  simpa [E, H, k, m, M, C, gap, R0, n] using hmono

/-- Right-late active-window mix contribution in weighted loser-mass form.

Unlike the product form below, this keeps the time-dependent loser mass inside
the Hoff gate integral.  This is the form needed for a sharp scalar estimate on
the active write window, where a uniform `epsLamShiftedEarlyFullAt` multiplier
is too coarse. -/
theorem selectorMUHoff_right_late_mix_integral_le_card_loser_integral
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀)
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol) :
    ∀ w j, selectorMUHaltEncConstW solMUReplStaticCfg w j →
      (∫ τ in (selectorMUEarlyWriteSubStart (j + 1))..
          (selectorMUWriteHoldTime (j + 1)),
        selectorMUHoffGateCoeff sol w τ *
          |selectorMixTarget branchU (sol w).u (sol w).lam τ haltCoordU -
            stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 1)) haltCoordU|)
      ≤
      (∫ τ in (selectorMUEarlyWriteSubStart (j + 1))..
          (selectorMUWriteHoldTime (j + 1)),
        selectorMUHoffGateCoeff sol w τ *
          (Finset.univ.filter (fun v : UniversalLocalView =>
            v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
              (fun v => (sol w).lam v τ)) := by
  classical
  intro w j henc
  let n : ℕ := j + 1
  let M : ℝ := stackMachineEncodingU.enc (solMUReplStaticCfg w n) haltCoordU
  have hab : selectorMUEarlyWriteSubStart n ≤ selectorMUWriteHoldTime n :=
    selectorMUEarlySubStart_le_writeHold n
  have ha0 : 0 ≤ selectorMUEarlyWriteSubStart n :=
    le_trans (selectorMUWriteStartTime_nonneg n)
      (selectorMUWriteStart_le_earlySubStart n)
  have hM :
      stackMachineEncodingU.enc (solMUReplStaticCfg w (n + 1)) haltCoordU = M := by
    simpa [selectorMUHaltEncConstW, selectorMUHaltEncConst, n, M,
      Nat.add_assoc] using henc
  have hbase :=
    selectorMUHoff_mix_integral_le_card_loser_integral
      (sol := sol) boxInputs w n (a := selectorMUEarlyWriteSubStart n)
      (b := selectorMUWriteHoldTime n) (M := M) hab ha0 hM
  simpa [n, M] using hbase

/-- Product form of `selectorMUHoff_right_late_mix_integral_le_of_shifted`.

The late shifted radius is constant in `τ`, so the right-late term is bounded
by the late Hoff gate integral times the shifted early-full loser radius.  This
is the scalar form needed before comparing the term to a concrete exponential
edge budget. -/
theorem selectorMUHoff_right_late_mix_integral_le_shiftedEarly_gate_mul
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀)
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (herr : (gateSelectorAtomsCoordN (universalGateAtoms eta heta)).errSel < 1 / 2)
    (hκ₀_nonneg : 0 ≤ (κ₀ : ℝ))
    (hg₀ : 0 < (g₀ : ℝ))
    (hscale : (κ₀ : ℝ) ≤ ((3 / 4 : ℝ) ^ Mcy) * (g₀ : ℝ))
    (hselect_start : ∀ w j,
      1 / (Fintype.card UniversalLocalView : ℝ) ≤
        (sol w).lam (localViewU (solMUReplStaticCfg w j))
          (selectorMUSelectStartTime j))
    (hutube_win : ∀ w j, ∀ t ∈ Set.Ico (selectorMUWriteStartTime j)
        (selectorMUWriteReadTime j),
      UTube r_LE_U (solMUReplStaticCfg w j) ((sol w).u t)) :
    ∀ w j, selectorMUHaltEncConstW solMUReplStaticCfg w j →
      (∫ τ in (selectorMUEarlyWriteSubStart (j + 1))..
          (selectorMUWriteHoldTime (j + 1)),
        selectorMUHoffGateCoeff sol w τ *
          |selectorMixTarget branchU (sol w).u (sol w).lam τ haltCoordU -
            stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 1)) haltCoordU|)
      ≤
      (∫ τ in (selectorMUEarlyWriteSubStart (j + 1))..
          (selectorMUWriteHoldTime (j + 1)),
        selectorMUHoffGateCoeff sol w τ) *
        epsLamShiftedEarlyFullAt sol w
          (selectorReplicatorGapVal eta heta)
          (Fintype.card UniversalLocalView : ℝ) (j + 1) := by
  classical
  intro w j henc
  let C : ℝ :=
    epsLamShiftedEarlyFullAt sol w
      (selectorReplicatorGapVal eta heta)
      (Fintype.card UniversalLocalView : ℝ) (j + 1)
  have hlate :=
    selectorMUHoff_right_late_mix_integral_le_of_shifted
      sol boxInputs herr hκ₀_nonneg hg₀ hscale hselect_start hutube_win
      w j henc
  have hconst :
      (∫ τ in (selectorMUEarlyWriteSubStart (j + 1))..
          (selectorMUWriteHoldTime (j + 1)),
        selectorMUHoffGateCoeff sol w τ * C) =
      (∫ τ in (selectorMUEarlyWriteSubStart (j + 1))..
          (selectorMUWriteHoldTime (j + 1)),
        selectorMUHoffGateCoeff sol w τ) * C := by
    rw [intervalIntegral.integral_mul_const]
  simpa [C] using hlate.trans_eq hconst

/-- Algebraic scalar exit for the canonical settled envelope with
`Lmin = 1 / card`.

This theorem performs no ODE comparison.  It only expands
`epsLamSettled_card_inv` and combines the two scalar forward estimates for the
homogeneous and prefix-reset terms. -/
theorem epsLamSettled_card_inv_prefix_weighted_integral_le_of_forward_bounds
    {a b gap R0 C : ℝ} {G weight reset : ℝ → ℝ}
    (hR0 : 0 ≤ R0)
    (hdecay :
      (∫ t in a..b,
        weight t * Real.exp (-(gap * (G t - G a)))) ≤ C / gap)
    (hprefix :
      (∫ t in a..b,
        weight t *
          (∫ s in a..t, Real.exp (gap * (G s - G a)) * reset s) *
          Real.exp (-(gap * (G t - G a)))) ≤
        (C / gap) * ∫ s in a..b, reset s)
    (hdecay_int : IntervalIntegrable
      (fun t => weight t * Real.exp (-(gap * (G t - G a))))
      MeasureTheory.volume a b)
    (hprefix_int : IntervalIntegrable
      (fun t =>
        weight t *
          (∫ s in a..t, Real.exp (gap * (G s - G a)) * reset s) *
          Real.exp (-(gap * (G t - G a))))
      MeasureTheory.volume a b) :
    (∫ t in a..b,
      weight t *
        epsLamSettled
          (V := UniversalLocalView)
          ((1 : ℝ) / Fintype.card UniversalLocalView)
          gap R0
          (∫ s in a..t, Real.exp (gap * (G s - G a)) * reset s)
          G a t) ≤
      ((Fintype.card UniversalLocalView : ℝ) - 1) *
        (R0 * (C / gap) +
          (C / gap) * ∫ s in a..b, reset s) := by
  classical
  haveI : Nonempty UniversalLocalView := ⟨defaultLocalViewU⟩
  let N : ℝ := Fintype.card UniversalLocalView
  let K : ℝ → ℝ := fun t =>
    ∫ s in a..t, Real.exp (gap * (G s - G a)) * reset s
  let decay : ℝ → ℝ := fun t => Real.exp (-(gap * (G t - G a)))
  let f0 : ℝ → ℝ := fun t => weight t * decay t
  let f1 : ℝ → ℝ := fun t => weight t * K t * decay t
  have hcard_nonneg : 0 ≤ N - 1 := by
    have hcard_one : (1 : ℝ) ≤ Fintype.card UniversalLocalView := by
      exact_mod_cast (Nat.succ_le_of_lt
        (Fintype.card_pos_iff.mpr ⟨defaultLocalViewU⟩ :
          0 < Fintype.card UniversalLocalView))
    simpa [N] using sub_nonneg.mpr hcard_one
  have hf0_int : IntervalIntegrable f0 MeasureTheory.volume a b := by
    simpa [f0, decay] using hdecay_int
  have hf1_int : IntervalIntegrable f1 MeasureTheory.volume a b := by
    simpa [f1, K, decay] using hprefix_int
  have hR0f0_int : IntervalIntegrable (fun t => R0 * f0 t) MeasureTheory.volume a b :=
    hf0_int.const_mul R0
  have hsplit :
      (∫ t in a..b,
        weight t *
          epsLamSettled
            (V := UniversalLocalView)
            ((1 : ℝ) / Fintype.card UniversalLocalView)
            gap R0 (K t) G a t) =
        (N - 1) *
          (R0 * (∫ t in a..b, f0 t) + ∫ t in a..b, f1 t) := by
    calc
      (∫ t in a..b,
        weight t *
          epsLamSettled
            (V := UniversalLocalView)
            ((1 : ℝ) / Fintype.card UniversalLocalView)
            gap R0 (K t) G a t)
          =
        (∫ t in a..b,
          (N - 1) * (R0 * f0 t + f1 t)) := by
            refine intervalIntegral.integral_congr ?_
            intro t _ht
            dsimp
            rw [epsLamSettled_card_inv (V := UniversalLocalView) gap R0 (K t) G a t]
            dsimp [N, f0, f1, K, decay]
            ring
      _ =
        (N - 1) * ∫ t in a..b, R0 * f0 t + f1 t := by
          rw [intervalIntegral.integral_const_mul]
      _ =
        (N - 1) *
          ((∫ t in a..b, R0 * f0 t) + ∫ t in a..b, f1 t) := by
          rw [intervalIntegral.integral_add hR0f0_int hf1_int]
      _ =
        (N - 1) *
          (R0 * (∫ t in a..b, f0 t) + ∫ t in a..b, f1 t) := by
          rw [intervalIntegral.integral_const_mul]
  have hdecay' : (∫ t in a..b, f0 t) ≤ C / gap := by
    simpa [f0, decay] using hdecay
  have hprefix' :
      (∫ t in a..b, f1 t) ≤ (C / gap) * ∫ s in a..b, reset s := by
    simpa [f1, K, decay] using hprefix
  have hsum :
      R0 * (∫ t in a..b, f0 t) + ∫ t in a..b, f1 t ≤
        R0 * (C / gap) + (C / gap) * ∫ s in a..b, reset s :=
    add_le_add (mul_le_mul_of_nonneg_left hdecay' hR0) hprefix'
  calc
    (∫ t in a..b,
      weight t *
        epsLamSettled
          (V := UniversalLocalView)
          ((1 : ℝ) / Fintype.card UniversalLocalView)
          gap R0 (K t) G a t)
        = (N - 1) *
            (R0 * (∫ t in a..b, f0 t) + ∫ t in a..b, f1 t) := hsplit
    _ ≤
      (N - 1) *
        (R0 * (C / gap) +
          (C / gap) * ∫ s in a..b, reset s) :=
        mul_le_mul_of_nonneg_left hsum hcard_nonneg

/-- Post-select new-view loser mass bounded by the time-dependent shifted
Duhamel envelope.

This is the corrected active-prefix surface: on
`[SelectStart, EarlyWriteSubStart]` the endpoint radius
`epsLamShiftedEarlyFullAt` is not a pointwise bound, so the Duhamel decay must
remain inside the Hoff-gate integral. -/
theorem selectorMUHoff_postSelect_new_loser_integral_le_prefix_duhamel
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀)
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (herr : (gateSelectorAtomsCoordN (universalGateAtoms eta heta)).errSel < 1 / 2)
    (hκ₀_nonneg : 0 ≤ (κ₀ : ℝ))
    (hg₀ : 0 < (g₀ : ℝ))
    (_hscale : (κ₀ : ℝ) ≤ ((3 / 4 : ℝ) ^ Mcy) * (g₀ : ℝ))
    (hselect_start : ∀ w j,
      1 / (Fintype.card UniversalLocalView : ℝ) ≤
        (sol w).lam (localViewU (solMUReplStaticCfg w j))
          (selectorMUSelectStartTime j))
    (hutube_win : ∀ w j, ∀ t ∈ Set.Ico (selectorMUWriteStartTime j)
        (selectorMUWriteReadTime j),
      UTube r_LE_U (solMUReplStaticCfg w j) ((sol w).u t)) :
    ∀ w j,
      (∫ τ in (selectorMUSelectStartTime (j + 1))..
          (selectorMUEarlyWriteSubStart (j + 1)),
        selectorMUHoffGateCoeff sol w τ *
          (Finset.univ.filter (fun v : UniversalLocalView =>
            v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
              (fun v => (sol w).lam v τ))
      ≤
      (∫ τ in (selectorMUSelectStartTime (j + 1))..
          (selectorMUEarlyWriteSubStart (j + 1)),
        selectorMUHoffGateCoeff sol w τ *
          epsLamSettled (V := UniversalLocalView)
            (1 / (Fintype.card UniversalLocalView : ℝ))
            (selectorReplicatorGapVal eta heta)
            (Fintype.card UniversalLocalView : ℝ)
            (∫ s in (selectorMUSelectStartTime (j + 1))..τ,
              Real.exp ((selectorReplicatorGapVal eta heta) *
                ((sol w).G s -
                  (sol w).G (selectorMUSelectStartTime (j + 1)))) *
                (((1 + Real.cos s) / 2) ^ Mcy * (κ₀ : ℝ)))
            (sol w).G (selectorMUSelectStartTime (j + 1)) τ) := by
  classical
  haveI : Nonempty UniversalLocalView := ⟨defaultLocalViewU⟩
  intro w j
  let n : ℕ := j + 1
  let gap : ℝ := selectorReplicatorGapVal eta heta
  let R0 : ℝ := Fintype.card UniversalLocalView
  let S : ℝ := selectorMUSelectStartTime n
  let E : ℝ := selectorMUEarlyWriteSubStart n
  let k : ℝ → ℝ := fun τ => selectorMUHoffGateCoeff sol w τ
  let mass : ℝ → ℝ := fun τ =>
    (Finset.univ.filter (fun v : UniversalLocalView =>
      v ≠ localViewU (solMUReplStaticCfg w n))).sum
        (fun v => (sol w).lam v τ)
  let env : ℝ → ℝ := fun τ =>
    epsLamSettled (V := UniversalLocalView)
      (1 / (Fintype.card UniversalLocalView : ℝ)) gap R0
      (∫ s in S..τ,
        Real.exp (gap * ((sol w).G s - (sol w).G S)) *
          (((1 + Real.cos s) / 2) ^ Mcy * (κ₀ : ℝ)))
      (sol w).G S τ
  have hgap0 : 0 < gap := by
    simpa [gap] using solMURepl_static_hgap0 eta heta herr
  have hR0_nonneg : 0 ≤ R0 := by
    dsimp [R0]
    positivity
  have hsum_forward := solMURepl_static_lam_sum_forward (sol := sol) boxInputs
  have hlam_forward := solMURepl_static_lam_nonneg_forward (sol := sol) boxInputs
  have hn_nonneg : 0 ≤ S := by
    simpa [S] using selectorMUSelectStart_nonneg_weighted n
  have hSE : S ≤ E := by
    simpa [S, E] using selectorMUSelectStart_le_earlySubStart n
  have hqL_select :
      ∀ t ∈ Icc S E,
        1 / (Fintype.card UniversalLocalView : ℝ) ≤
          (sol w).lam (localViewU (solMUReplStaticCfg w n)) t := by
    have hgap_floor :
        ∀ v : UniversalLocalView, v ≠ localViewU (solMUReplStaticCfg w n) →
          ∀ t ∈ Ico S E,
            universalPval eta heta v ((sol w).u t) -
              universalPval eta heta (localViewU (solMUReplStaticCfg w n))
                ((sol w).u t) ≤ 0 := by
      intro v hv t ht
      have hgap_full :=
        selector_replicator_hgap_of_utube
          (sol := fun _ : ℕ => sol w)
          (cfg := fun _ j => solMUReplStaticCfg w j)
          herr
          (fun _ j t ht => hutube_win w j t ht)
      have ht_full : t ∈ Ico (selectorMUWriteStartTime n)
          (selectorMUWriteReadTime n) :=
        ⟨le_trans (selectorMUWriteStart_le_selectStart n) (by simpa [S] using ht.1),
          lt_of_lt_of_le (by simpa [E] using ht.2)
            (le_trans (selectorMUEarlySubStart_le_writeHold n)
              (selectorMUWriteHold_le_read n))⟩
      have hnonpos : -gap ≤ 0 := neg_nonpos.mpr hgap0.le
      exact le_trans
        (by simpa [gap] using hgap_full 0 n v hv t ht_full)
        hnonpos
    exact
      replicator_winner_floor_on_interval_param
        (sol := sol w) (localViewU (solMUReplStaticCfg w n))
        (a := S) (b := E) hSE
        (1 / (Fintype.card UniversalLocalView : ℝ)) (le_refl _)
        (fun t ht => solMURepl_static_hdom_nonneg t
          (le_trans hn_nonneg ht.1))
        (fun t _ht => boxInputs.hcr_nonneg t)
        (fun t _ht =>
          mul_nonneg
            (pow_nonneg (by nlinarith [Real.neg_one_le_sin t]) _)
            (mul_nonneg hg₀.le (Real.exp_pos _).le))
        hgap_floor
        (fun t ht => hsum_forward w t (le_trans hn_nonneg ht.1))
        (fun v t ht => hlam_forward w v t (le_trans hn_nonneg ht.1))
        (by simpa [S, n] using hselect_start w n)
  have hRa_select :
      ∀ v : UniversalLocalView, v ≠ localViewU (solMUReplStaticCfg w n) →
        (sol w).lam v S /
            (sol w).lam (localViewU (solMUReplStaticCfg w n)) S ≤ R0 := by
    have hsum := hsum_forward w S hn_nonneg
    have hnonneg : ∀ v : UniversalLocalView, 0 ≤ (sol w).lam v S :=
      fun v => hlam_forward w v S hn_nonneg
    simpa [R0, S] using
      lam_ratio_card_bound_at_weighted
        (lam := fun v : UniversalLocalView => (sol w).lam v S)
        (vstar := localViewU (solMUReplStaticCfg w n))
        hsum hnonneg (by simpa [S, n] using hselect_start w n)
  have hgap_cond :
      ∀ v : UniversalLocalView, v ≠ localViewU (solMUReplStaticCfg w n) →
        ∀ t ∈ Ico S E,
          universalPval eta heta v ((sol w).u t) -
            universalPval eta heta (localViewU (solMUReplStaticCfg w n))
              ((sol w).u t) ≤ -gap := by
    intro v hv t ht
    have hgap_full :=
      selector_replicator_hgap_of_utube
        (sol := fun _ : ℕ => sol w)
        (cfg := fun _ j => solMUReplStaticCfg w j)
        herr
        (fun _ j t ht => hutube_win w j t ht)
    have ht_full : t ∈ Ico (selectorMUWriteStartTime n)
        (selectorMUWriteReadTime n) :=
      ⟨le_trans (selectorMUWriteStart_le_selectStart n) (by simpa [S] using ht.1),
        lt_of_lt_of_le (by simpa [E] using ht.2)
          (le_trans (selectorMUEarlySubStart_le_writeHold n)
            (selectorMUWriteHold_le_read n))⟩
    simpa [gap] using hgap_full 0 n v hv t ht_full
  have hmass : ∀ τ ∈ Icc S E, mass τ ≤ env τ := by
    simpa [mass, env, S, E, gap, R0] using
      loser_mass_small_on_prefix_pointwise
        (sol := sol w) (vstar := localViewU (solMUReplStaticCfg w n))
        (a := S) (b := E)
        (Lmin := 1 / (Fintype.card UniversalLocalView : ℝ))
        (gap := gap) (R0 := R0)
        solMURepl_concLmin_floor
        (le_of_lt hgap0)
        hR0_nonneg
        (fun t ht => solMURepl_static_hdom_nonneg t
          (le_trans hn_nonneg ht.1))
        (by fun_prop)
        hqL_select
        (fun v t ht => hlam_forward w v t (le_trans hn_nonneg ht.1))
        (fun t ht => hsum_forward w t (le_trans hn_nonneg ht.1))
        (fun s _hs =>
          mul_nonneg
            (pow_nonneg (by nlinarith [Real.neg_one_le_cos s]) _)
            hκ₀_nonneg)
        (fun s _hs =>
          mul_nonneg
            (pow_nonneg (by nlinarith [Real.neg_one_le_sin s]) _)
            (mul_nonneg hg₀.le (Real.exp_pos _).le))
        hgap_cond
        hRa_select
  have hk_cont : Continuous k := by
    simpa [k, selectorMUHoffGateCoeff] using
      selector_replicator_gateZ_integrand_continuous (sol w)
  have hmass_cont : Continuous mass := by
    dsimp [mass]
    simpa using
      (continuous_finsetSum
        (Finset.univ.filter (fun v : UniversalLocalView =>
          v ≠ localViewU (solMUReplStaticCfg w n)))
        (fun v _hv => (sol w).cont_lam v))
  have henv_cont : Continuous env := by
    have hG_cont : Continuous fun τ : ℝ => (sol w).G τ := (sol w).cont_G
    have hreset_cont : Continuous fun s : ℝ =>
        Real.exp (gap * ((sol w).G s - (sol w).G S)) *
          (((1 + Real.cos s) / 2) ^ Mcy * (κ₀ : ℝ)) := by
      fun_prop
    have hK_cont : Continuous fun τ : ℝ =>
        ∫ s in S..τ,
          Real.exp (gap * ((sol w).G s - (sol w).G S)) *
            (((1 + Real.cos s) / 2) ^ Mcy * (κ₀ : ℝ)) := by
      exact continuous_iff_continuousAt.mpr fun τ =>
        (intervalIntegral.integral_hasDerivAt_right
          (hreset_cont.intervalIntegrable S τ)
          (hreset_cont.stronglyMeasurableAtFilter _ _) hreset_cont.continuousAt).continuousAt
    dsimp [env]
    unfold epsLamSettled selectorSettledRatioEps selectorSettledRatioCoeff
    exact continuous_const.mul
      (((continuous_const.add (hK_cont.div_const _)).mul
          (Real.continuous_exp.comp
            (continuous_const.mul (hG_cont.sub continuous_const)))))
  have hk_nonneg : ∀ τ ∈ Icc S E, 0 ≤ k τ := by
    intro τ hτ
    have hτ0 : 0 ≤ τ := le_trans hn_nonneg hτ.1
    simpa [k, selectorMUHoffGateCoeff] using
      selector_replicator_gateZ_integrand_nonneg (sol w)
        selectorSchedule_domain_of_nonneg_structural (by norm_num [bgpParams38]) hτ0
  have hmono :
      (∫ τ in S..E, k τ * mass τ) ≤ ∫ τ in S..E, k τ * env τ := by
    apply intervalIntegral.integral_mono_on hSE
    · exact (hk_cont.mul hmass_cont).intervalIntegrable S E
    · exact (hk_cont.mul henv_cont).intervalIntegrable S E
    · intro τ hτ
      exact mul_le_mul_of_nonneg_left (hmass τ hτ) (hk_nonneg τ hτ)
  simpa [n, S, E, k, mass, env, gap, R0] using hmono

/-- Active-late new-view loser mass bounded by the time-dependent shifted
Duhamel envelope.

This is the active suffix analogue of
`selectorMUHoff_postSelect_new_loser_integral_le_prefix_duhamel`.  The weighted
integral stays on `[EarlyWriteSubStart, WriteHold]`, but the Duhamel source
term is still accumulated from `SelectStart` to the current time. -/
theorem selectorMUHoff_activeLate_new_loser_integral_le_duhamel
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀)
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (herr : (gateSelectorAtomsCoordN (universalGateAtoms eta heta)).errSel < 1 / 2)
    (hκ₀_nonneg : 0 ≤ (κ₀ : ℝ))
    (hg₀ : 0 < (g₀ : ℝ))
    (hscale : (κ₀ : ℝ) ≤ ((3 / 4 : ℝ) ^ Mcy) * (g₀ : ℝ))
    (hselect_start : ∀ w j,
      1 / (Fintype.card UniversalLocalView : ℝ) ≤
        (sol w).lam (localViewU (solMUReplStaticCfg w j))
          (selectorMUSelectStartTime j))
    (hutube_win : ∀ w j, ∀ t ∈ Set.Ico (selectorMUWriteStartTime j)
        (selectorMUWriteReadTime j),
      UTube r_LE_U (solMUReplStaticCfg w j) ((sol w).u t)) :
    ∀ w j,
      (∫ τ in (selectorMUEarlyWriteSubStart (j + 1))..
          (selectorMUWriteHoldTime (j + 1)),
        selectorMUHoffGateCoeff sol w τ *
          (Finset.univ.filter (fun v : UniversalLocalView =>
            v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
              (fun v => (sol w).lam v τ))
      ≤
      (∫ τ in (selectorMUEarlyWriteSubStart (j + 1))..
          (selectorMUWriteHoldTime (j + 1)),
        selectorMUHoffGateCoeff sol w τ *
          epsLamSettled (V := UniversalLocalView)
            (1 / (Fintype.card UniversalLocalView : ℝ))
            (selectorReplicatorGapVal eta heta)
            (Fintype.card UniversalLocalView : ℝ)
            (∫ s in (selectorMUSelectStartTime (j + 1))..τ,
              Real.exp ((selectorReplicatorGapVal eta heta) *
                ((sol w).G s -
                  (sol w).G (selectorMUSelectStartTime (j + 1)))) *
                (((1 + Real.cos s) / 2) ^ Mcy * (κ₀ : ℝ)))
            (sol w).G (selectorMUSelectStartTime (j + 1)) τ) := by
  classical
  haveI : Nonempty UniversalLocalView := ⟨defaultLocalViewU⟩
  intro w j
  let n : ℕ := j + 1
  let gap : ℝ := selectorReplicatorGapVal eta heta
  let R0 : ℝ := Fintype.card UniversalLocalView
  let S : ℝ := selectorMUSelectStartTime n
  let E : ℝ := selectorMUEarlyWriteSubStart n
  let H : ℝ := selectorMUWriteHoldTime n
  let k : ℝ → ℝ := fun τ => selectorMUHoffGateCoeff sol w τ
  let mass : ℝ → ℝ := fun τ =>
    (Finset.univ.filter (fun v : UniversalLocalView =>
      v ≠ localViewU (solMUReplStaticCfg w n))).sum
        (fun v => (sol w).lam v τ)
  let env : ℝ → ℝ := fun τ =>
    epsLamSettled (V := UniversalLocalView)
      (1 / (Fintype.card UniversalLocalView : ℝ)) gap R0
      (∫ s in S..τ,
        Real.exp (gap * ((sol w).G s - (sol w).G S)) *
          (((1 + Real.cos s) / 2) ^ Mcy * (κ₀ : ℝ)))
      (sol w).G S τ
  have hgap0 : 0 < gap := by
    simpa [gap] using solMURepl_static_hgap0 eta heta herr
  have hR0_nonneg : 0 ≤ R0 := by
    dsimp [R0]
    positivity
  have hsum_forward := solMURepl_static_lam_sum_forward (sol := sol) boxInputs
  have hlam_forward := solMURepl_static_lam_nonneg_forward (sol := sol) boxInputs
  have hn_nonneg : 0 ≤ S := by
    simpa [S] using selectorMUSelectStart_nonneg_weighted n
  have hSE : S ≤ E := by
    simpa [S, E] using selectorMUSelectStart_le_earlySubStart n
  have hEH : E ≤ H := by
    simpa [E, H] using selectorMUEarlySubStart_le_writeHold n
  have hSH : S ≤ H := le_trans hSE hEH
  have hqL_select :
      ∀ t ∈ Icc S H,
        1 / (Fintype.card UniversalLocalView : ℝ) ≤
          (sol w).lam (localViewU (solMUReplStaticCfg w n)) t := by
    have hgap_floor :
        ∀ v : UniversalLocalView, v ≠ localViewU (solMUReplStaticCfg w n) →
          ∀ t ∈ Ico S H,
            universalPval eta heta v ((sol w).u t) -
              universalPval eta heta (localViewU (solMUReplStaticCfg w n))
                ((sol w).u t) ≤ 0 := by
      intro v hv t ht
      have hgap_full :=
        selector_replicator_hgap_of_utube
          (sol := fun _ : ℕ => sol w)
          (cfg := fun _ j => solMUReplStaticCfg w j)
          herr
          (fun _ j t ht => hutube_win w j t ht)
      have ht_full : t ∈ Ico (selectorMUWriteStartTime n)
          (selectorMUWriteReadTime n) :=
        ⟨le_trans (selectorMUWriteStart_le_selectStart n) (by simpa [S] using ht.1),
          lt_of_lt_of_le (by simpa [H] using ht.2)
            (selectorMUWriteHold_le_read n)⟩
      have hnonpos : -gap ≤ 0 := neg_nonpos.mpr hgap0.le
      exact le_trans
        (by simpa [gap] using hgap_full 0 n v hv t ht_full)
        hnonpos
    exact
      replicator_winner_floor_on_interval_param
        (sol := sol w) (localViewU (solMUReplStaticCfg w n))
        (a := S) (b := H) hSH
        (1 / (Fintype.card UniversalLocalView : ℝ)) (le_refl _)
        (fun t ht => solMURepl_static_hdom_nonneg t
          (le_trans hn_nonneg ht.1))
        (fun t _ht => boxInputs.hcr_nonneg t)
        (fun t _ht =>
          mul_nonneg
            (pow_nonneg (by nlinarith [Real.neg_one_le_sin t]) _)
            (mul_nonneg hg₀.le (Real.exp_pos _).le))
        hgap_floor
        (fun t ht => hsum_forward w t (le_trans hn_nonneg ht.1))
        (fun v t ht => hlam_forward w v t (le_trans hn_nonneg ht.1))
        (by simpa [S, n] using hselect_start w n)
  have hRa_select :
      ∀ v : UniversalLocalView, v ≠ localViewU (solMUReplStaticCfg w n) →
        (sol w).lam v S /
            (sol w).lam (localViewU (solMUReplStaticCfg w n)) S ≤ R0 := by
    have hsum := hsum_forward w S hn_nonneg
    have hnonneg : ∀ v : UniversalLocalView, 0 ≤ (sol w).lam v S :=
      fun v => hlam_forward w v S hn_nonneg
    simpa [R0, S] using
      lam_ratio_card_bound_at_weighted
        (lam := fun v : UniversalLocalView => (sol w).lam v S)
        (vstar := localViewU (solMUReplStaticCfg w n))
        hsum hnonneg (by simpa [S, n] using hselect_start w n)
  have hgap_cond :
      ∀ v : UniversalLocalView, v ≠ localViewU (solMUReplStaticCfg w n) →
        ∀ t ∈ Ico S H,
          universalPval eta heta v ((sol w).u t) -
            universalPval eta heta (localViewU (solMUReplStaticCfg w n))
              ((sol w).u t) ≤ -gap := by
    intro v hv t ht
    have hgap_full :=
      selector_replicator_hgap_of_utube
        (sol := fun _ : ℕ => sol w)
        (cfg := fun _ j => solMUReplStaticCfg w j)
        herr
        (fun _ j t ht => hutube_win w j t ht)
    have ht_full : t ∈ Ico (selectorMUWriteStartTime n)
        (selectorMUWriteReadTime n) :=
      ⟨le_trans (selectorMUWriteStart_le_selectStart n) (by simpa [S] using ht.1),
        lt_of_lt_of_le (by simpa [H] using ht.2)
          (selectorMUWriteHold_le_read n)⟩
    simpa [gap] using hgap_full 0 n v hv t ht_full
  have hmass : ∀ τ ∈ Icc E H, mass τ ≤ env τ := by
    simpa [mass, env, S, E, H, gap, R0, n] using
      hloser_of_shifted_concentration_from_early_duhamel
        (sol := sol) (cfg := fun j => solMUReplStaticCfg w j) w n
        hgap0 hR0_nonneg hκ₀_nonneg hscale
        (fun t ht => solMURepl_static_hdom_nonneg t
          (le_trans hn_nonneg ht.1))
        hqL_select
        (fun v t ht => hlam_forward w v t (le_trans hn_nonneg ht.1))
        (fun t ht => hsum_forward w t (le_trans hn_nonneg ht.1))
        hgap_cond
        hRa_select
  have hk_cont : Continuous k := by
    simpa [k, selectorMUHoffGateCoeff] using
      selector_replicator_gateZ_integrand_continuous (sol w)
  have hmass_cont : Continuous mass := by
    dsimp [mass]
    simpa using
      (continuous_finsetSum
        (Finset.univ.filter (fun v : UniversalLocalView =>
          v ≠ localViewU (solMUReplStaticCfg w n)))
        (fun v _hv => (sol w).cont_lam v))
  have henv_cont : Continuous env := by
    have hG_cont : Continuous fun τ : ℝ => (sol w).G τ := (sol w).cont_G
    have hreset_cont : Continuous fun s : ℝ =>
        Real.exp (gap * ((sol w).G s - (sol w).G S)) *
          (((1 + Real.cos s) / 2) ^ Mcy * (κ₀ : ℝ)) := by
      fun_prop
    have hK_cont : Continuous fun τ : ℝ =>
        ∫ s in S..τ,
          Real.exp (gap * ((sol w).G s - (sol w).G S)) *
            (((1 + Real.cos s) / 2) ^ Mcy * (κ₀ : ℝ)) := by
      exact continuous_iff_continuousAt.mpr fun τ =>
        (intervalIntegral.integral_hasDerivAt_right
          (hreset_cont.intervalIntegrable S τ)
          (hreset_cont.stronglyMeasurableAtFilter _ _) hreset_cont.continuousAt).continuousAt
    dsimp [env]
    unfold epsLamSettled selectorSettledRatioEps selectorSettledRatioCoeff
    exact continuous_const.mul
      (((continuous_const.add (hK_cont.div_const _)).mul
          (Real.continuous_exp.comp
            (continuous_const.mul (hG_cont.sub continuous_const)))))
  have hk_nonneg : ∀ τ ∈ Icc E H, 0 ≤ k τ := by
    intro τ hτ
    have hτ0 : 0 ≤ τ := le_trans (le_trans hn_nonneg hSE) hτ.1
    simpa [k, selectorMUHoffGateCoeff] using
      selector_replicator_gateZ_integrand_nonneg (sol w)
        selectorSchedule_domain_of_nonneg_structural (by norm_num [bgpParams38]) hτ0
  have hmono :
      (∫ τ in E..H, k τ * mass τ) ≤ ∫ τ in E..H, k τ * env τ := by
    apply intervalIntegral.integral_mono_on hEH
    · exact (hk_cont.mul hmass_cont).intervalIntegrable E H
    · exact (hk_cont.mul henv_cont).intervalIntegrable E H
    · intro τ hτ
      exact mul_le_mul_of_nonneg_left (hmass τ hτ) (hk_nonneg τ hτ)
  simpa [n, E, H, S, k, mass, env, gap, R0] using hmono

/-- Scalar active-late new-loser bound after the time-dependent Duhamel
envelope.

This is the source-aware late analogue of
`selectorMUHoff_postSelect_new_loser_integral_le_prefix_scalar`.  The right hand
side keeps the reset integral over the whole select-to-hold interval, rather
than taking a static supremum radius outside the active Hoff integral. -/
theorem selectorMUHoff_activeLate_new_loser_integral_le_prefix_scalar
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀)
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (herr : (gateSelectorAtomsCoordN (universalGateAtoms eta heta)).errSel < 1 / 2)
    (hκ₀_nonneg : 0 ≤ (κ₀ : ℝ))
    (hg₀ : 0 < (g₀ : ℝ))
    (hscale : (κ₀ : ℝ) ≤ ((3 / 4 : ℝ) ^ Mcy) * (g₀ : ℝ))
    (hselect_start : ∀ w j,
      1 / (Fintype.card UniversalLocalView : ℝ) ≤
        (sol w).lam (localViewU (solMUReplStaticCfg w j))
          (selectorMUSelectStartTime j))
    (hutube_win : ∀ w j, ∀ t ∈ Set.Ico (selectorMUWriteStartTime j)
        (selectorMUWriteReadTime j),
      UTube r_LE_U (solMUReplStaticCfg w j) ((sol w).u t))
    (C : ℕ → ℕ → ℝ)
    (hC_nonneg : ∀ w n, 0 ≤ C w n)
    (hweight_bound : ∀ w n, ∀ t ∈ Icc (selectorMUSelectStartTime n)
        (selectorMUWriteHoldTime n),
      selectorMUHoffGateCoeff sol w t ≤
        C w n *
          (((1 + Real.sin t) / 2) ^ Mcy *
            ((g₀ : ℝ) * Real.exp (bgpParams38.cα * t)))) :
    ∀ w j,
      (∫ τ in (selectorMUEarlyWriteSubStart (j + 1))..
          (selectorMUWriteHoldTime (j + 1)),
        selectorMUHoffGateCoeff sol w τ *
          (Finset.univ.filter (fun v : UniversalLocalView =>
            v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
              (fun v => (sol w).lam v τ))
      ≤
      ((Fintype.card UniversalLocalView : ℝ) - 1) *
        ((Fintype.card UniversalLocalView : ℝ) *
            ((C w (j + 1)) / selectorReplicatorGapVal eta heta) +
          ((C w (j + 1)) / selectorReplicatorGapVal eta heta) *
            ∫ s in (selectorMUSelectStartTime (j + 1))..
                (selectorMUWriteHoldTime (j + 1)),
              (((1 + Real.cos s) / 2) ^ Mcy * (κ₀ : ℝ))) := by
  classical
  haveI : Nonempty UniversalLocalView := ⟨defaultLocalViewU⟩
  intro w j
  let n : ℕ := j + 1
  let gap : ℝ := selectorReplicatorGapVal eta heta
  let S : ℝ := selectorMUSelectStartTime n
  let E : ℝ := selectorMUEarlyWriteSubStart n
  let H : ℝ := selectorMUWriteHoldTime n
  let R0 : ℝ := Fintype.card UniversalLocalView
  let weight : ℝ → ℝ := fun τ => selectorMUHoffGateCoeff sol w τ
  let cg : ℝ → ℝ := fun τ =>
    ((1 + Real.sin τ) / 2) ^ Mcy *
      ((g₀ : ℝ) * Real.exp (bgpParams38.cα * τ))
  let reset : ℝ → ℝ := fun τ =>
    ((1 + Real.cos τ) / 2) ^ Mcy * (κ₀ : ℝ)
  let env : ℝ → ℝ := fun τ =>
    epsLamSettled (V := UniversalLocalView)
      (1 / (Fintype.card UniversalLocalView : ℝ)) gap R0
      (∫ s in S..τ,
        Real.exp (gap * ((sol w).G s - (sol w).G S)) * reset s)
      (sol w).G S τ
  have hactive :=
    selectorMUHoff_activeLate_new_loser_integral_le_duhamel
      sol boxInputs herr hκ₀_nonneg hg₀ hscale hselect_start hutube_win w j
  have hgap_pos : 0 < gap := by
    simpa [gap] using solMURepl_static_hgap0 eta heta herr
  have hSE : S ≤ E := by
    simpa [S, E] using selectorMUSelectStart_le_earlySubStart n
  have hEH : E ≤ H := by
    simpa [E, H] using selectorMUEarlySubStart_le_writeHold n
  have hSH : S ≤ H := le_trans hSE hEH
  have hS_nonneg : 0 ≤ S := by
    simpa [S] using selectorMUSelectStart_nonneg_weighted n
  have hG_cont : Continuous fun τ : ℝ => (sol w).G τ := (sol w).cont_G
  have hGder : ∀ τ ∈ Icc S H, HasDerivAt (sol w).G (cg τ) τ := by
    intro τ hτ
    have hτ0 : 0 ≤ τ := le_trans hS_nonneg hτ.1
    simpa [cg] using
      (sol w).G_hasDeriv τ (solMURepl_static_hdom_nonneg τ hτ0)
  have hcg_cont : Continuous cg := by
    dsimp [cg]
    fun_prop
  have hreset_cont : Continuous reset := by
    dsimp [reset]
    fun_prop
  have hweight_cont : Continuous weight := by
    dsimp [weight, selectorMUHoffGateCoeff]
    exact selector_replicator_gateZ_integrand_continuous (sol w)
  have hcg_nonneg : ∀ τ ∈ Icc S H, 0 ≤ cg τ := by
    intro τ _hτ
    dsimp [cg]
    have hsin_nonneg : 0 ≤ (1 + Real.sin τ) / 2 := by
      nlinarith [Real.neg_one_le_sin τ]
    exact mul_nonneg (pow_nonneg hsin_nonneg Mcy)
      (mul_nonneg hg₀.le (Real.exp_pos _).le)
  have hreset_nonneg : ∀ τ ∈ Icc S H, 0 ≤ reset τ := by
    intro τ _hτ
    dsimp [reset]
    have hcos_nonneg : 0 ≤ (1 + Real.cos τ) / 2 := by
      nlinarith [Real.neg_one_le_cos τ]
    exact mul_nonneg (pow_nonneg hcos_nonneg Mcy) hκ₀_nonneg
  have hweight_nonneg : ∀ τ ∈ Icc S H, 0 ≤ weight τ := by
    intro τ hτ
    have hτ0 : 0 ≤ τ := le_trans hS_nonneg hτ.1
    dsimp [weight, selectorMUHoffGateCoeff]
    exact selector_replicator_gateZ_integrand_nonneg (sol w)
      selectorSchedule_domain_of_nonneg_structural (by norm_num [bgpParams38]) hτ0
  have hweight_bound' : ∀ τ ∈ Icc S H, weight τ ≤ C w n * cg τ := by
    intro τ hτ
    simpa [S, H, weight, cg, n] using hweight_bound w n τ hτ
  have hdecay_bound :=
    forward_weight_decay_integral_le
      (a := S) (b := H) (gap := gap) (C := C w n)
      (G := (sol w).G) (cg := cg) (weight := weight)
      hSH hgap_pos (hC_nonneg w n) hG_cont hGder hcg_cont
      hweight_cont hweight_nonneg hweight_bound'
  have hprefix_bound :=
    forward_weight_prefix_reset_decay_integral_le
      (a := S) (b := H) (gap := gap) (C := C w n)
      (G := (sol w).G) (cg := cg) (weight := weight) (reset := reset)
      hSH hgap_pos (hC_nonneg w n) hG_cont hGder hcg_cont
      hweight_cont hreset_cont hcg_nonneg hreset_nonneg hweight_nonneg
      hweight_bound'
  have hdecay_cont : Continuous fun τ : ℝ =>
      Real.exp (-(gap * ((sol w).G τ - (sol w).G S))) := by
    fun_prop
  have hdecay_int : IntervalIntegrable
      (fun τ => weight τ * Real.exp (-(gap * ((sol w).G τ - (sol w).G S))))
      MeasureTheory.volume S H :=
    (hweight_cont.mul hdecay_cont).intervalIntegrable S H
  have hresetExp_cont : Continuous fun σ : ℝ =>
      Real.exp (gap * ((sol w).G σ - (sol w).G S)) * reset σ := by
    fun_prop
  have hK_cont : Continuous fun τ : ℝ =>
      ∫ σ in S..τ,
        Real.exp (gap * ((sol w).G σ - (sol w).G S)) * reset σ := by
    exact continuous_iff_continuousAt.mpr fun τ =>
      (intervalIntegral.integral_hasDerivAt_right
        (hresetExp_cont.intervalIntegrable S τ)
        (hresetExp_cont.stronglyMeasurableAtFilter _ _)
        hresetExp_cont.continuousAt).continuousAt
  have hprefix_int : IntervalIntegrable
      (fun τ =>
        weight τ *
          (∫ σ in S..τ,
            Real.exp (gap * ((sol w).G σ - (sol w).G S)) * reset σ) *
          Real.exp (-(gap * ((sol w).G τ - (sol w).G S))))
      MeasureTheory.volume S H :=
    ((hweight_cont.mul hK_cont).mul hdecay_cont).intervalIntegrable S H
  have henv_cont : Continuous env := by
    dsimp [env]
    unfold epsLamSettled selectorSettledRatioEps selectorSettledRatioCoeff
    exact continuous_const.mul
      (((continuous_const.add (hK_cont.div_const _)).mul
          (Real.continuous_exp.comp
            (continuous_const.mul (hG_cont.sub continuous_const)))))
  have hcard_sub_nonneg :
      0 ≤ (Fintype.card UniversalLocalView : ℝ) - 1 := by
    have hcard_one : (1 : ℝ) ≤ Fintype.card UniversalLocalView := by
      exact_mod_cast (Nat.succ_le_of_lt
        (Fintype.card_pos_iff.mpr ⟨defaultLocalViewU⟩ :
          0 < Fintype.card UniversalLocalView))
    linarith
  have henv_nonneg : ∀ τ ∈ Icc S H, 0 ≤ env τ := by
    intro τ hτ
    have hK_nonneg :
        0 ≤ ∫ σ in S..τ,
          Real.exp (gap * ((sol w).G σ - (sol w).G S)) * reset σ := by
      apply intervalIntegral.integral_nonneg hτ.1
      intro σ hσ
      exact mul_nonneg (Real.exp_pos _).le
        (hreset_nonneg σ ⟨hσ.1, le_trans hσ.2 hτ.2⟩)
    dsimp [env]
    rw [epsLamSettled_card_inv]
    exact mul_nonneg hcard_sub_nonneg
      (mul_nonneg (add_nonneg (by dsimp [R0]; positivity) hK_nonneg)
        (Real.exp_pos _).le)
  have henv_weight_nonneg :
      0 ≤ᵐ[MeasureTheory.volume.restrict (Ioc S H)]
        fun τ => weight τ * env τ := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with τ hτ
    have hτIcc : τ ∈ Icc S H := ⟨le_of_lt hτ.1, hτ.2⟩
    exact mul_nonneg (hweight_nonneg τ hτIcc) (henv_nonneg τ hτIcc)
  have hsub :
      (∫ τ in E..H, weight τ * env τ) ≤ ∫ τ in S..H, weight τ * env τ := by
    apply intervalIntegral.integral_mono_interval
    · exact hSE
    · exact hEH
    · exact le_rfl
    · exact henv_weight_nonneg
    · exact (hweight_cont.mul henv_cont).intervalIntegrable S H
  have henv :=
    epsLamSettled_card_inv_prefix_weighted_integral_le_of_forward_bounds
      (a := S) (b := H) (gap := gap) (R0 := R0) (C := C w n)
      (G := (sol w).G) (weight := weight) (reset := reset)
      (by dsimp [R0]; positivity)
      hdecay_bound.2 hprefix_bound.2 hdecay_int hprefix_int
  exact le_trans (by simpa [n, E, H, S, gap, R0, weight, reset, env] using hactive)
    (le_trans hsub
      (by simpa [n, S, H, gap, R0, weight, reset, env] using henv))

/-- Scalar post-select new-loser bound after the prefix-Duhamel envelope.

The only schedule-specific input is the pointwise Hoff/gain ratio
`selectorMUHoffGateCoeff ≤ C w n * cg`.  The theorem keeps the reset integral
explicit, matching the scalar convolution estimate. -/
theorem selectorMUHoff_postSelect_new_loser_integral_le_prefix_scalar
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀)
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (herr : (gateSelectorAtomsCoordN (universalGateAtoms eta heta)).errSel < 1 / 2)
    (hκ₀_nonneg : 0 ≤ (κ₀ : ℝ))
    (hg₀ : 0 < (g₀ : ℝ))
    (hscale : (κ₀ : ℝ) ≤ ((3 / 4 : ℝ) ^ Mcy) * (g₀ : ℝ))
    (hselect_start : ∀ w j,
      1 / (Fintype.card UniversalLocalView : ℝ) ≤
        (sol w).lam (localViewU (solMUReplStaticCfg w j))
          (selectorMUSelectStartTime j))
    (hutube_win : ∀ w j, ∀ t ∈ Set.Ico (selectorMUWriteStartTime j)
        (selectorMUWriteReadTime j),
      UTube r_LE_U (solMUReplStaticCfg w j) ((sol w).u t))
    (C : ℕ → ℕ → ℝ)
    (hC_nonneg : ∀ w n, 0 ≤ C w n)
    (hweight_bound : ∀ w n, ∀ t ∈ Icc (selectorMUSelectStartTime n)
        (selectorMUEarlyWriteSubStart n),
      selectorMUHoffGateCoeff sol w t ≤
        C w n *
          (((1 + Real.sin t) / 2) ^ Mcy *
            ((g₀ : ℝ) * Real.exp (bgpParams38.cα * t)))) :
    ∀ w j,
      (∫ τ in (selectorMUSelectStartTime (j + 1))..
          (selectorMUEarlyWriteSubStart (j + 1)),
        selectorMUHoffGateCoeff sol w τ *
          (Finset.univ.filter (fun v : UniversalLocalView =>
            v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
              (fun v => (sol w).lam v τ))
      ≤
      ((Fintype.card UniversalLocalView : ℝ) - 1) *
        ((Fintype.card UniversalLocalView : ℝ) *
            ((C w (j + 1)) / selectorReplicatorGapVal eta heta) +
          ((C w (j + 1)) / selectorReplicatorGapVal eta heta) *
            ∫ s in (selectorMUSelectStartTime (j + 1))..
                (selectorMUEarlyWriteSubStart (j + 1)),
              (((1 + Real.cos s) / 2) ^ Mcy * (κ₀ : ℝ))) := by
  classical
  haveI : Nonempty UniversalLocalView := ⟨defaultLocalViewU⟩
  intro w j
  let n : ℕ := j + 1
  let gap : ℝ := selectorReplicatorGapVal eta heta
  let S : ℝ := selectorMUSelectStartTime n
  let E : ℝ := selectorMUEarlyWriteSubStart n
  let R0 : ℝ := Fintype.card UniversalLocalView
  let weight : ℝ → ℝ := fun τ => selectorMUHoffGateCoeff sol w τ
  let cg : ℝ → ℝ := fun τ =>
    ((1 + Real.sin τ) / 2) ^ Mcy *
      ((g₀ : ℝ) * Real.exp (bgpParams38.cα * τ))
  let reset : ℝ → ℝ := fun τ =>
    ((1 + Real.cos τ) / 2) ^ Mcy * (κ₀ : ℝ)
  have hpost :=
    selectorMUHoff_postSelect_new_loser_integral_le_prefix_duhamel
      sol boxInputs herr hκ₀_nonneg hg₀ hscale hselect_start hutube_win w j
  have hgap_pos : 0 < gap := by
    simpa [gap] using solMURepl_static_hgap0 eta heta herr
  have hSE : S ≤ E := by
    simpa [S, E] using selectorMUSelectStart_le_earlySubStart n
  have hS_nonneg : 0 ≤ S := by
    simpa [S] using selectorMUSelectStart_nonneg_weighted n
  have hG_cont : Continuous fun τ : ℝ => (sol w).G τ := (sol w).cont_G
  have hGder : ∀ τ ∈ Icc S E, HasDerivAt (sol w).G (cg τ) τ := by
    intro τ hτ
    have hτ0 : 0 ≤ τ := le_trans hS_nonneg hτ.1
    simpa [cg] using
      (sol w).G_hasDeriv τ (solMURepl_static_hdom_nonneg τ hτ0)
  have hcg_cont : Continuous cg := by
    dsimp [cg]
    fun_prop
  have hreset_cont : Continuous reset := by
    dsimp [reset]
    fun_prop
  have hweight_cont : Continuous weight := by
    dsimp [weight, selectorMUHoffGateCoeff]
    exact selector_replicator_gateZ_integrand_continuous (sol w)
  have hcg_nonneg : ∀ τ ∈ Icc S E, 0 ≤ cg τ := by
    intro τ _hτ
    dsimp [cg]
    have hsin_nonneg : 0 ≤ (1 + Real.sin τ) / 2 := by
      nlinarith [Real.neg_one_le_sin τ]
    exact mul_nonneg (pow_nonneg hsin_nonneg Mcy)
      (mul_nonneg hg₀.le (Real.exp_pos _).le)
  have hreset_nonneg : ∀ τ ∈ Icc S E, 0 ≤ reset τ := by
    intro τ _hτ
    dsimp [reset]
    have hcos_nonneg : 0 ≤ (1 + Real.cos τ) / 2 := by
      nlinarith [Real.neg_one_le_cos τ]
    exact mul_nonneg (pow_nonneg hcos_nonneg Mcy) hκ₀_nonneg
  have hweight_nonneg : ∀ τ ∈ Icc S E, 0 ≤ weight τ := by
    intro τ hτ
    have hτ0 : 0 ≤ τ := le_trans hS_nonneg hτ.1
    dsimp [weight, selectorMUHoffGateCoeff]
    exact selector_replicator_gateZ_integrand_nonneg (sol w)
      selectorSchedule_domain_of_nonneg_structural (by norm_num [bgpParams38]) hτ0
  have hweight_bound' : ∀ τ ∈ Icc S E, weight τ ≤ C w n * cg τ := by
    intro τ hτ
    simpa [S, E, weight, cg, n] using hweight_bound w n τ hτ
  have hdecay_bound :=
    forward_weight_decay_integral_le
      (a := S) (b := E) (gap := gap) (C := C w n)
      (G := (sol w).G) (cg := cg) (weight := weight)
      hSE hgap_pos (hC_nonneg w n) hG_cont hGder hcg_cont
      hweight_cont hweight_nonneg hweight_bound'
  have hprefix_bound :=
    forward_weight_prefix_reset_decay_integral_le
      (a := S) (b := E) (gap := gap) (C := C w n)
      (G := (sol w).G) (cg := cg) (weight := weight) (reset := reset)
      hSE hgap_pos (hC_nonneg w n) hG_cont hGder hcg_cont
      hweight_cont hreset_cont hcg_nonneg hreset_nonneg hweight_nonneg
      hweight_bound'
  have hdecay_cont : Continuous fun τ : ℝ =>
      Real.exp (-(gap * ((sol w).G τ - (sol w).G S))) := by
    fun_prop
  have hdecay_int : IntervalIntegrable
      (fun τ => weight τ * Real.exp (-(gap * ((sol w).G τ - (sol w).G S))))
      MeasureTheory.volume S E :=
    (hweight_cont.mul hdecay_cont).intervalIntegrable S E
  have hresetExp_cont : Continuous fun σ : ℝ =>
      Real.exp (gap * ((sol w).G σ - (sol w).G S)) * reset σ := by
    fun_prop
  have hK_cont : Continuous fun τ : ℝ =>
      ∫ σ in S..τ,
        Real.exp (gap * ((sol w).G σ - (sol w).G S)) * reset σ := by
    exact continuous_iff_continuousAt.mpr fun τ =>
      (intervalIntegral.integral_hasDerivAt_right
        (hresetExp_cont.intervalIntegrable S τ)
        (hresetExp_cont.stronglyMeasurableAtFilter _ _)
        hresetExp_cont.continuousAt).continuousAt
  have hprefix_int : IntervalIntegrable
      (fun τ =>
        weight τ *
          (∫ σ in S..τ,
            Real.exp (gap * ((sol w).G σ - (sol w).G S)) * reset σ) *
          Real.exp (-(gap * ((sol w).G τ - (sol w).G S))))
      MeasureTheory.volume S E :=
    ((hweight_cont.mul hK_cont).mul hdecay_cont).intervalIntegrable S E
  have henv :=
    epsLamSettled_card_inv_prefix_weighted_integral_le_of_forward_bounds
      (a := S) (b := E) (gap := gap) (R0 := R0) (C := C w n)
      (G := (sol w).G) (weight := weight) (reset := reset)
      (by dsimp [R0]; positivity)
      hdecay_bound.2 hprefix_bound.2 hdecay_int hprefix_int
  exact le_trans (by simpa [n, S, E, gap, R0, weight, reset] using hpost)
    (by simpa [n, S, E, gap, R0, weight, reset] using henv)

/-- Right-edge target-mix tail after the next write start.  The recovery prefix
is paid by the pure Hoff gate, the post-select prefix by new-view loser mass,
and the early-write suffix by shifted concentration. -/
theorem selectorMUHoff_right_mix_from_writeStart_le_recovery_add_new_loser_late_shifted
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀)
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (herr : (gateSelectorAtomsCoordN (universalGateAtoms eta heta)).errSel < 1 / 2)
    (hκ₀_nonneg : 0 ≤ (κ₀ : ℝ))
    (hg₀ : 0 < (g₀ : ℝ))
    (hscale : (κ₀ : ℝ) ≤ ((3 / 4 : ℝ) ^ Mcy) * (g₀ : ℝ))
    (hselect_start : ∀ w j,
      1 / (Fintype.card UniversalLocalView : ℝ) ≤
        (sol w).lam (localViewU (solMUReplStaticCfg w j))
          (selectorMUSelectStartTime j))
    (hutube_win : ∀ w j, ∀ t ∈ Set.Ico (selectorMUWriteStartTime j)
        (selectorMUWriteReadTime j),
      UTube r_LE_U (solMUReplStaticCfg w j) ((sol w).u t)) :
    ∀ w j, selectorMUHaltEncConstW solMUReplStaticCfg w j →
      (∫ τ in (selectorMUWriteStartTime (j + 1))..(selectorMUNextWriteStart j),
        selectorMUHoffGateCoeff sol w τ *
          |selectorMixTarget branchU (sol w).u (sol w).lam τ haltCoordU -
            stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 1)) haltCoordU|)
      ≤
      (∫ τ in (selectorMUWriteStartTime (j + 1))..
          (selectorMUSelectStartTime (j + 1)),
        selectorMUHoffGateCoeff sol w τ) +
      (∫ τ in (selectorMUSelectStartTime (j + 1))..
          (selectorMUEarlyWriteSubStart (j + 1)),
        selectorMUHoffGateCoeff sol w τ *
          (Finset.univ.filter (fun v : UniversalLocalView =>
            v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
              (fun v => (sol w).lam v τ)) +
      (∫ τ in (selectorMUEarlyWriteSubStart (j + 1))..
          (selectorMUWriteHoldTime (j + 1)),
        selectorMUHoffGateCoeff sol w τ *
          epsLamShiftedEarlyFullAt sol w
            (selectorReplicatorGapVal eta heta)
            (Fintype.card UniversalLocalView : ℝ) (j + 1)) := by
  classical
  intro w j henc
  let W : ℝ := selectorMUWriteStartTime (j + 1)
  let S : ℝ := selectorMUSelectStartTime (j + 1)
  let E : ℝ := selectorMUEarlyWriteSubStart (j + 1)
  let H : ℝ := selectorMUWriteHoldTime (j + 1)
  let M : ℝ := stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 1)) haltCoordU
  let f : ℝ → ℝ := fun τ =>
    selectorMUHoffGateCoeff sol w τ *
      |selectorMixTarget branchU (sol w).u (sol w).lam τ haltCoordU - M|
  have hf_cont : Continuous f := by
    dsimp [f, M]
    exact (selector_replicator_gateZ_integrand_continuous (sol w)).mul
      (((sol w).cont_mixTarget haltCoordU).sub continuous_const).abs
  have hI : ∀ x y : ℝ, IntervalIntegrable f MeasureTheory.volume x y :=
    fun x y => hf_cont.intervalIntegrable x y
  have hsplit :
      (∫ τ in W..H, f τ) = (∫ τ in W..E, f τ) + (∫ τ in E..H, f τ) :=
    (intervalIntegral.integral_add_adjacent_intervals (hI W E) (hI E H)).symm
  have hWE : W ≤ E := by
    simpa [W, E] using selectorMUWriteStart_le_earlySubStart (j + 1)
  have hmixWE :
      (∫ τ in W..E, f τ) ≤
      (∫ τ in (selectorMUWriteStartTime (j + 1))..
          (selectorMUEarlyWriteSubStart (j + 1)),
        selectorMUHoffGateCoeff sol w τ *
          (Finset.univ.filter (fun v : UniversalLocalView =>
            v ≠ localViewU (solMUReplStaticCfg w j) ∧
              v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
                (fun v => (sol w).lam v τ)) := by
    have hM_new :
        stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 2)) haltCoordU = M := by
      simpa [selectorMUHaltEncConstW, selectorMUHaltEncConst, M] using henc
    have hbase :=
      selectorMUHoff_mix_integral_le_old_or_new_loser_integral
        (sol := sol) boxInputs w j
        (a := W) (b := E) (M := M)
        hWE
        (by simpa [W] using selectorMUWriteStartTime_nonneg (j + 1))
        rfl hM_new
    simpa [W, E, M, f] using hbase
  have hbadTail :=
    selectorMUHoff_right_cross_writeStart_old_new_loser_integral_le_recovery_add_new_loser
      (sol := sol) boxInputs w j
  have hWE_tail :
      (∫ τ in W..E, f τ) ≤
      (∫ τ in (selectorMUWriteStartTime (j + 1))..
          (selectorMUSelectStartTime (j + 1)),
        selectorMUHoffGateCoeff sol w τ) +
      (∫ τ in (selectorMUSelectStartTime (j + 1))..
          (selectorMUEarlyWriteSubStart (j + 1)),
        selectorMUHoffGateCoeff sol w τ *
          (Finset.univ.filter (fun v : UniversalLocalView =>
            v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
              (fun v => (sol w).lam v τ)) :=
    le_trans hmixWE hbadTail
  have hlate :=
    selectorMUHoff_right_late_mix_integral_le_of_shifted
      sol boxInputs herr hκ₀_nonneg hg₀ hscale hselect_start hutube_win
      w j henc
  calc
    (∫ τ in (selectorMUWriteStartTime (j + 1))..(selectorMUNextWriteStart j),
        selectorMUHoffGateCoeff sol w τ *
          |selectorMixTarget branchU (sol w).u (sol w).lam τ haltCoordU -
            stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 1)) haltCoordU|)
        = ∫ τ in W..H, f τ := by
          simp [W, H, M, f, selectorMUNextWriteStart]
    _ = (∫ τ in W..E, f τ) + (∫ τ in E..H, f τ) := hsplit
    _ ≤
      ((∫ τ in (selectorMUWriteStartTime (j + 1))..
          (selectorMUSelectStartTime (j + 1)),
        selectorMUHoffGateCoeff sol w τ) +
      (∫ τ in (selectorMUSelectStartTime (j + 1))..
          (selectorMUEarlyWriteSubStart (j + 1)),
        selectorMUHoffGateCoeff sol w τ *
          (Finset.univ.filter (fun v : UniversalLocalView =>
            v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
              (fun v => (sol w).lam v τ))) +
      (∫ τ in (selectorMUEarlyWriteSubStart (j + 1))..
          (selectorMUWriteHoldTime (j + 1)),
        selectorMUHoffGateCoeff sol w τ *
          epsLamShiftedEarlyFullAt sol w
            (selectorReplicatorGapVal eta heta)
            (Fintype.card UniversalLocalView : ℝ) (j + 1)) := by
        exact add_le_add hWE_tail (by simpa [E, H, M, f] using hlate)
    _ =
      (∫ τ in (selectorMUWriteStartTime (j + 1))..
          (selectorMUSelectStartTime (j + 1)),
        selectorMUHoffGateCoeff sol w τ) +
      (∫ τ in (selectorMUSelectStartTime (j + 1))..
          (selectorMUEarlyWriteSubStart (j + 1)),
        selectorMUHoffGateCoeff sol w τ *
          (Finset.univ.filter (fun v : UniversalLocalView =>
            v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
              (fun v => (sol w).lam v τ)) +
      (∫ τ in (selectorMUEarlyWriteSubStart (j + 1))..
          (selectorMUWriteHoldTime (j + 1)),
        selectorMUHoffGateCoeff sol w τ *
          epsLamShiftedEarlyFullAt sol w
            (selectorReplicatorGapVal eta heta)
            (Fintype.card UniversalLocalView : ℝ) (j + 1)) := by
        ring

/-- Right-edge target-mix tail after the next write start, with the post-select
prefix replaced by its time-dependent Duhamel envelope.

This is the corrected form for the select-to-early subwindow: the endpoint
shifted radius is not used as a uniform multiplier before `EarlyWriteSubStart`. -/
theorem selectorMUHoff_right_mix_from_writeStart_le_recovery_add_postselect_duhamel_late_shifted
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀)
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (herr : (gateSelectorAtomsCoordN (universalGateAtoms eta heta)).errSel < 1 / 2)
    (hκ₀_nonneg : 0 ≤ (κ₀ : ℝ))
    (hg₀ : 0 < (g₀ : ℝ))
    (hscale : (κ₀ : ℝ) ≤ ((3 / 4 : ℝ) ^ Mcy) * (g₀ : ℝ))
    (hselect_start : ∀ w j,
      1 / (Fintype.card UniversalLocalView : ℝ) ≤
        (sol w).lam (localViewU (solMUReplStaticCfg w j))
          (selectorMUSelectStartTime j))
    (hutube_win : ∀ w j, ∀ t ∈ Set.Ico (selectorMUWriteStartTime j)
        (selectorMUWriteReadTime j),
      UTube r_LE_U (solMUReplStaticCfg w j) ((sol w).u t)) :
    ∀ w j, selectorMUHaltEncConstW solMUReplStaticCfg w j →
      (∫ τ in (selectorMUWriteStartTime (j + 1))..(selectorMUNextWriteStart j),
        selectorMUHoffGateCoeff sol w τ *
          |selectorMixTarget branchU (sol w).u (sol w).lam τ haltCoordU -
            stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 1)) haltCoordU|)
      ≤
      (∫ τ in (selectorMUWriteStartTime (j + 1))..
          (selectorMUSelectStartTime (j + 1)),
        selectorMUHoffGateCoeff sol w τ) +
      (∫ τ in (selectorMUSelectStartTime (j + 1))..
          (selectorMUEarlyWriteSubStart (j + 1)),
        selectorMUHoffGateCoeff sol w τ *
          epsLamSettled (V := UniversalLocalView)
            (1 / (Fintype.card UniversalLocalView : ℝ))
            (selectorReplicatorGapVal eta heta)
            (Fintype.card UniversalLocalView : ℝ)
            (∫ s in (selectorMUSelectStartTime (j + 1))..τ,
              Real.exp ((selectorReplicatorGapVal eta heta) *
                ((sol w).G s -
                  (sol w).G (selectorMUSelectStartTime (j + 1)))) *
                (((1 + Real.cos s) / 2) ^ Mcy * (κ₀ : ℝ)))
            (sol w).G (selectorMUSelectStartTime (j + 1)) τ) +
      (∫ τ in (selectorMUEarlyWriteSubStart (j + 1))..
          (selectorMUWriteHoldTime (j + 1)),
        selectorMUHoffGateCoeff sol w τ *
          epsLamShiftedEarlyFullAt sol w
            (selectorReplicatorGapVal eta heta)
            (Fintype.card UniversalLocalView : ℝ) (j + 1)) := by
  intro w j henc
  let recoveryGate : ℝ :=
    ∫ τ in (selectorMUWriteStartTime (j + 1))..
        (selectorMUSelectStartTime (j + 1)),
      selectorMUHoffGateCoeff sol w τ
  let postSelectNewLoser : ℝ :=
    ∫ τ in (selectorMUSelectStartTime (j + 1))..
        (selectorMUEarlyWriteSubStart (j + 1)),
      selectorMUHoffGateCoeff sol w τ *
        (Finset.univ.filter (fun v : UniversalLocalView =>
          v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
            (fun v => (sol w).lam v τ)
  let postSelectDuhamel : ℝ :=
    ∫ τ in (selectorMUSelectStartTime (j + 1))..
        (selectorMUEarlyWriteSubStart (j + 1)),
      selectorMUHoffGateCoeff sol w τ *
        epsLamSettled (V := UniversalLocalView)
          (1 / (Fintype.card UniversalLocalView : ℝ))
          (selectorReplicatorGapVal eta heta)
          (Fintype.card UniversalLocalView : ℝ)
          (∫ s in (selectorMUSelectStartTime (j + 1))..τ,
            Real.exp ((selectorReplicatorGapVal eta heta) *
              ((sol w).G s -
                (sol w).G (selectorMUSelectStartTime (j + 1)))) *
              (((1 + Real.cos s) / 2) ^ Mcy * (κ₀ : ℝ)))
          (sol w).G (selectorMUSelectStartTime (j + 1)) τ
  let rightLate : ℝ :=
    ∫ τ in (selectorMUEarlyWriteSubStart (j + 1))..
        (selectorMUWriteHoldTime (j + 1)),
      selectorMUHoffGateCoeff sol w τ *
        epsLamShiftedEarlyFullAt sol w
          (selectorReplicatorGapVal eta heta)
          (Fintype.card UniversalLocalView : ℝ) (j + 1)
  have hbase :=
    selectorMUHoff_right_mix_from_writeStart_le_recovery_add_new_loser_late_shifted
      sol boxInputs herr hκ₀_nonneg hg₀ hscale hselect_start hutube_win w j henc
  have hpost :=
    selectorMUHoff_postSelect_new_loser_integral_le_prefix_duhamel
      sol boxInputs herr hκ₀_nonneg hg₀ hscale hselect_start hutube_win w j
  have hbase' :
      (∫ τ in (selectorMUWriteStartTime (j + 1))..(selectorMUNextWriteStart j),
        selectorMUHoffGateCoeff sol w τ *
          |selectorMixTarget branchU (sol w).u (sol w).lam τ haltCoordU -
            stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 1)) haltCoordU|)
      ≤ recoveryGate + postSelectNewLoser + rightLate := by
    simpa [recoveryGate, postSelectNewLoser, rightLate] using hbase
  have hpost' : postSelectNewLoser ≤ postSelectDuhamel := by
    simpa [postSelectNewLoser, postSelectDuhamel] using hpost
  change
      (∫ τ in (selectorMUWriteStartTime (j + 1))..(selectorMUNextWriteStart j),
        selectorMUHoffGateCoeff sol w τ *
          |selectorMixTarget branchU (sol w).u (sol w).lam τ haltCoordU -
            stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 1)) haltCoordU|)
      ≤ recoveryGate + postSelectDuhamel + rightLate
  nlinarith [hbase', hpost']

/-- Right-edge target-mix tail after the next write start, keeping the active
early-write suffix as a weighted loser-mass integral.

This is the faithful form of the right-late estimate before any scalar
asymptotic claim: the reset-source contribution remains inside the time
integral instead of being hidden in a uniform shifted concentration radius. -/
theorem selectorMUHoff_right_mix_from_writeStart_le_recovery_add_new_loser_late_weighted
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀)
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol) :
    ∀ w j, selectorMUHaltEncConstW solMUReplStaticCfg w j →
      (∫ τ in (selectorMUWriteStartTime (j + 1))..(selectorMUNextWriteStart j),
        selectorMUHoffGateCoeff sol w τ *
          |selectorMixTarget branchU (sol w).u (sol w).lam τ haltCoordU -
            stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 1)) haltCoordU|)
      ≤
      (∫ τ in (selectorMUWriteStartTime (j + 1))..
          (selectorMUSelectStartTime (j + 1)),
        selectorMUHoffGateCoeff sol w τ) +
      (∫ τ in (selectorMUSelectStartTime (j + 1))..
          (selectorMUEarlyWriteSubStart (j + 1)),
        selectorMUHoffGateCoeff sol w τ *
          (Finset.univ.filter (fun v : UniversalLocalView =>
            v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
              (fun v => (sol w).lam v τ)) +
      (∫ τ in (selectorMUEarlyWriteSubStart (j + 1))..
          (selectorMUWriteHoldTime (j + 1)),
        selectorMUHoffGateCoeff sol w τ *
          (Finset.univ.filter (fun v : UniversalLocalView =>
            v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
              (fun v => (sol w).lam v τ)) := by
  classical
  intro w j henc
  let W : ℝ := selectorMUWriteStartTime (j + 1)
  let S : ℝ := selectorMUSelectStartTime (j + 1)
  let E : ℝ := selectorMUEarlyWriteSubStart (j + 1)
  let H : ℝ := selectorMUWriteHoldTime (j + 1)
  let M : ℝ := stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 1)) haltCoordU
  let f : ℝ → ℝ := fun τ =>
    selectorMUHoffGateCoeff sol w τ *
      |selectorMixTarget branchU (sol w).u (sol w).lam τ haltCoordU - M|
  have hf_cont : Continuous f := by
    dsimp [f, M]
    exact (selector_replicator_gateZ_integrand_continuous (sol w)).mul
      (((sol w).cont_mixTarget haltCoordU).sub continuous_const).abs
  have hI : ∀ x y : ℝ, IntervalIntegrable f MeasureTheory.volume x y :=
    fun x y => hf_cont.intervalIntegrable x y
  have hsplit :
      (∫ τ in W..H, f τ) = (∫ τ in W..E, f τ) + (∫ τ in E..H, f τ) :=
    (intervalIntegral.integral_add_adjacent_intervals (hI W E) (hI E H)).symm
  have hWE : W ≤ E := by
    simpa [W, E] using selectorMUWriteStart_le_earlySubStart (j + 1)
  have hmixWE :
      (∫ τ in W..E, f τ) ≤
      (∫ τ in (selectorMUWriteStartTime (j + 1))..
          (selectorMUEarlyWriteSubStart (j + 1)),
        selectorMUHoffGateCoeff sol w τ *
          (Finset.univ.filter (fun v : UniversalLocalView =>
            v ≠ localViewU (solMUReplStaticCfg w j) ∧
              v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
                (fun v => (sol w).lam v τ)) := by
    have hM_new :
        stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 2)) haltCoordU = M := by
      simpa [selectorMUHaltEncConstW, selectorMUHaltEncConst, M] using henc
    have hbase :=
      selectorMUHoff_mix_integral_le_old_or_new_loser_integral
        (sol := sol) boxInputs w j
        (a := W) (b := E) (M := M)
        hWE
        (by simpa [W] using selectorMUWriteStartTime_nonneg (j + 1))
        rfl hM_new
    simpa [W, E, M, f] using hbase
  have hbadTail :=
    selectorMUHoff_right_cross_writeStart_old_new_loser_integral_le_recovery_add_new_loser
      (sol := sol) boxInputs w j
  have hWE_tail :
      (∫ τ in W..E, f τ) ≤
      (∫ τ in (selectorMUWriteStartTime (j + 1))..
          (selectorMUSelectStartTime (j + 1)),
        selectorMUHoffGateCoeff sol w τ) +
      (∫ τ in (selectorMUSelectStartTime (j + 1))..
          (selectorMUEarlyWriteSubStart (j + 1)),
        selectorMUHoffGateCoeff sol w τ *
          (Finset.univ.filter (fun v : UniversalLocalView =>
            v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
              (fun v => (sol w).lam v τ)) :=
    le_trans hmixWE hbadTail
  have hlate :=
    selectorMUHoff_right_late_mix_integral_le_card_loser_integral
      (sol := sol) boxInputs w j henc
  calc
    (∫ τ in (selectorMUWriteStartTime (j + 1))..(selectorMUNextWriteStart j),
        selectorMUHoffGateCoeff sol w τ *
          |selectorMixTarget branchU (sol w).u (sol w).lam τ haltCoordU -
            stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 1)) haltCoordU|)
        = ∫ τ in W..H, f τ := by
          simp [W, H, M, f, selectorMUNextWriteStart]
    _ = (∫ τ in W..E, f τ) + (∫ τ in E..H, f τ) := hsplit
    _ ≤
      ((∫ τ in (selectorMUWriteStartTime (j + 1))..
          (selectorMUSelectStartTime (j + 1)),
        selectorMUHoffGateCoeff sol w τ) +
      (∫ τ in (selectorMUSelectStartTime (j + 1))..
          (selectorMUEarlyWriteSubStart (j + 1)),
        selectorMUHoffGateCoeff sol w τ *
          (Finset.univ.filter (fun v : UniversalLocalView =>
            v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
              (fun v => (sol w).lam v τ))) +
      (∫ τ in (selectorMUEarlyWriteSubStart (j + 1))..
          (selectorMUWriteHoldTime (j + 1)),
        selectorMUHoffGateCoeff sol w τ *
          (Finset.univ.filter (fun v : UniversalLocalView =>
            v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
              (fun v => (sol w).lam v τ)) := by
        exact add_le_add hWE_tail (by simpa [E, H, M, f] using hlate)
    _ =
      (∫ τ in (selectorMUWriteStartTime (j + 1))..
          (selectorMUSelectStartTime (j + 1)),
        selectorMUHoffGateCoeff sol w τ) +
      (∫ τ in (selectorMUSelectStartTime (j + 1))..
          (selectorMUEarlyWriteSubStart (j + 1)),
        selectorMUHoffGateCoeff sol w τ *
          (Finset.univ.filter (fun v : UniversalLocalView =>
            v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
              (fun v => (sol w).lam v τ)) +
      (∫ τ in (selectorMUEarlyWriteSubStart (j + 1))..
          (selectorMUWriteHoldTime (j + 1)),
        selectorMUHoffGateCoeff sol w τ *
          (Finset.univ.filter (fun v : UniversalLocalView =>
            v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
              (fun v => (sol w).lam v τ)) := by
        ring

/-- Full right-edge halt-mix integral reduced to the cross-boundary two-safe
bad-mass integral plus the late shifted concentration tail. -/
theorem selectorMUHoff_right_mix_integral_le_cross_old_new_add_late_shifted
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀)
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (herr : (gateSelectorAtomsCoordN (universalGateAtoms eta heta)).errSel < 1 / 2)
    (hκ₀_nonneg : 0 ≤ (κ₀ : ℝ))
    (hg₀ : 0 < (g₀ : ℝ))
    (hscale : (κ₀ : ℝ) ≤ ((3 / 4 : ℝ) ^ Mcy) * (g₀ : ℝ))
    (hselect_start : ∀ w j,
      1 / (Fintype.card UniversalLocalView : ℝ) ≤
        (sol w).lam (localViewU (solMUReplStaticCfg w j))
          (selectorMUSelectStartTime j))
    (hutube_win : ∀ w j, ∀ t ∈ Set.Ico (selectorMUWriteStartTime j)
        (selectorMUWriteReadTime j),
      UTube r_LE_U (solMUReplStaticCfg w j) ((sol w).u t)) :
    ∀ w j, selectorMUHaltEncConstW solMUReplStaticCfg w j →
      (∫ τ in (selectorMUZOffEnd j)..(selectorMUNextWriteStart j),
        selectorMUHoffGateCoeff sol w τ *
          |selectorMixTarget branchU (sol w).u (sol w).lam τ haltCoordU -
            stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 1)) haltCoordU|)
      ≤
      (∫ τ in (selectorMUZOffEnd j)..(selectorMUEarlyWriteSubStart (j + 1)),
        selectorMUHoffGateCoeff sol w τ *
          (Finset.univ.filter (fun v : UniversalLocalView =>
            v ≠ localViewU (solMUReplStaticCfg w j) ∧
              v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
                (fun v => (sol w).lam v τ)) +
      (∫ τ in (selectorMUEarlyWriteSubStart (j + 1))..
          (selectorMUWriteHoldTime (j + 1)),
        selectorMUHoffGateCoeff sol w τ *
          epsLamShiftedEarlyFullAt sol w
            (selectorReplicatorGapVal eta heta)
            (Fintype.card UniversalLocalView : ℝ) (j + 1)) := by
  intro w j henc
  let Z : ℝ := selectorMUZOffEnd j
  let E : ℝ := selectorMUEarlyWriteSubStart (j + 1)
  let H : ℝ := selectorMUWriteHoldTime (j + 1)
  let M : ℝ := stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 1)) haltCoordU
  let f : ℝ → ℝ := fun τ =>
    selectorMUHoffGateCoeff sol w τ *
      |selectorMixTarget branchU (sol w).u (sol w).lam τ haltCoordU - M|
  have hf_cont : Continuous f := by
    dsimp [f, M]
    exact (selector_replicator_gateZ_integrand_continuous (sol w)).mul
      (((sol w).cont_mixTarget haltCoordU).sub continuous_const).abs
  have hI : ∀ x y : ℝ, IntervalIntegrable f MeasureTheory.volume x y :=
    fun x y => hf_cont.intervalIntegrable x y
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hI Z E) (hI E H)
  have hcross :=
    selectorMUHoff_right_cross_mix_integral_le_old_or_new_loser_integral
      (sol := sol) boxInputs w j henc
  have hlate :=
    selectorMUHoff_right_late_mix_integral_le_of_shifted
      sol boxInputs herr hκ₀_nonneg hg₀ hscale hselect_start hutube_win
      w j henc
  calc
    (∫ τ in (selectorMUZOffEnd j)..(selectorMUNextWriteStart j),
        selectorMUHoffGateCoeff sol w τ *
          |selectorMixTarget branchU (sol w).u (sol w).lam τ haltCoordU -
            stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 1)) haltCoordU|)
        = (∫ τ in Z..H, f τ) := by
          simp [Z, H, M, f, selectorMUNextWriteStart]
    _ = (∫ τ in Z..E, f τ) + (∫ τ in E..H, f τ) := hsplit.symm
    _ ≤
      (∫ τ in (selectorMUZOffEnd j)..(selectorMUEarlyWriteSubStart (j + 1)),
        selectorMUHoffGateCoeff sol w τ *
          (Finset.univ.filter (fun v : UniversalLocalView =>
            v ≠ localViewU (solMUReplStaticCfg w j) ∧
              v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
                (fun v => (sol w).lam v τ)) +
      (∫ τ in (selectorMUEarlyWriteSubStart (j + 1))..
          (selectorMUWriteHoldTime (j + 1)),
        selectorMUHoffGateCoeff sol w τ *
          epsLamShiftedEarlyFullAt sol w
            (selectorReplicatorGapVal eta heta)
            (Fintype.card UniversalLocalView : ℝ) (j + 1)) := by
        exact add_le_add
          (by simpa [Z, E, M, f] using hcross)
          (by simpa [E, H, M, f] using hlate)

/-- Right actual Hoff cap reduced to the z-off endpoint error, the two-safe
cross-boundary bad-mass integral, and the late shifted concentration tail. -/
theorem selectorMUHoffCapRightField_le_initial_add_cross_old_new_late_shifted
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀)
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (herr : (gateSelectorAtomsCoordN (universalGateAtoms eta heta)).errSel < 1 / 2)
    (hκ₀_nonneg : 0 ≤ (κ₀ : ℝ))
    (hg₀ : 0 < (g₀ : ℝ))
    (hscale : (κ₀ : ℝ) ≤ ((3 / 4 : ℝ) ^ Mcy) * (g₀ : ℝ))
    (hselect_start : ∀ w j,
      1 / (Fintype.card UniversalLocalView : ℝ) ≤
        (sol w).lam (localViewU (solMUReplStaticCfg w j))
          (selectorMUSelectStartTime j))
    (hutube_win : ∀ w j, ∀ t ∈ Set.Ico (selectorMUWriteStartTime j)
        (selectorMUWriteReadTime j),
      UTube r_LE_U (solMUReplStaticCfg w j) ((sol w).u t)) :
    ∀ w j, selectorMUHaltEncConstW solMUReplStaticCfg w j →
      selectorMUHoffCapRightField sol w j ≤
        |(sol w).z (selectorMUZOffEnd j) haltCoordU -
          stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 1)) haltCoordU| +
        2 *
          ((∫ τ in (selectorMUZOffEnd j)..(selectorMUEarlyWriteSubStart (j + 1)),
            selectorMUHoffGateCoeff sol w τ *
              (Finset.univ.filter (fun v : UniversalLocalView =>
                v ≠ localViewU (solMUReplStaticCfg w j) ∧
                  v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
                    (fun v => (sol w).lam v τ)) +
          (∫ τ in (selectorMUEarlyWriteSubStart (j + 1))..
              (selectorMUWriteHoldTime (j + 1)),
            selectorMUHoffGateCoeff sol w τ *
              epsLamShiftedEarlyFullAt sol w
                (selectorReplicatorGapVal eta heta)
                (Fintype.card UniversalLocalView : ℝ) (j + 1))) := by
  intro w j henc
  let M : ℝ := stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 1)) haltCoordU
  have hcap := selectorMUHoffCapRightField_le_initial_add_target
    (sol := sol) w j M
  have hmix := selectorMUHoff_right_mix_integral_le_cross_old_new_add_late_shifted
    sol boxInputs herr hκ₀_nonneg hg₀ hscale hselect_start hutube_win w j henc
  have hmixM :
      (∫ τ in (selectorMUZOffEnd j)..(selectorMUNextWriteStart j),
        selectorMUHoffGateCoeff sol w τ *
          |selectorMixTarget branchU (sol w).u (sol w).lam τ haltCoordU - M|)
      ≤
      (∫ τ in (selectorMUZOffEnd j)..(selectorMUEarlyWriteSubStart (j + 1)),
        selectorMUHoffGateCoeff sol w τ *
          (Finset.univ.filter (fun v : UniversalLocalView =>
            v ≠ localViewU (solMUReplStaticCfg w j) ∧
              v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
                (fun v => (sol w).lam v τ)) +
      (∫ τ in (selectorMUEarlyWriteSubStart (j + 1))..
          (selectorMUWriteHoldTime (j + 1)),
        selectorMUHoffGateCoeff sol w τ *
          epsLamShiftedEarlyFullAt sol w
            (selectorReplicatorGapVal eta heta)
            (Fintype.card UniversalLocalView : ℝ) (j + 1)) := by
    simpa [M] using hmix
  calc
    selectorMUHoffCapRightField sol w j
        ≤ |(sol w).z (selectorMUZOffEnd j) haltCoordU - M| +
            2 * (∫ τ in (selectorMUZOffEnd j)..(selectorMUNextWriteStart j),
              selectorMUHoffGateCoeff sol w τ *
                |selectorMixTarget branchU (sol w).u (sol w).lam τ haltCoordU - M|) :=
          hcap
    _ ≤ |(sol w).z (selectorMUZOffEnd j) haltCoordU - M| +
          2 *
            ((∫ τ in (selectorMUZOffEnd j)..(selectorMUEarlyWriteSubStart (j + 1)),
              selectorMUHoffGateCoeff sol w τ *
                (Finset.univ.filter (fun v : UniversalLocalView =>
                  v ≠ localViewU (solMUReplStaticCfg w j) ∧
                    v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
                      (fun v => (sol w).lam v τ)) +
            (∫ τ in (selectorMUEarlyWriteSubStart (j + 1))..
                (selectorMUWriteHoldTime (j + 1)),
              selectorMUHoffGateCoeff sol w τ *
                epsLamShiftedEarlyFullAt sol w
                  (selectorReplicatorGapVal eta heta)
                  (Fintype.card UniversalLocalView : ℝ) (j + 1))) := by
        exact add_le_add le_rfl
          (mul_le_mul_of_nonneg_left hmixM (by norm_num : (0 : ℝ) ≤ 2))

/-- Combined actual Hoff edge-cap reduction from shifted concentration.

The remaining scalar work is exactly the two endpoint errors, the left
old/new-bad integral, the right cross-boundary old/new-bad integral, and the
late shifted-concentration tail. -/
theorem selectorMUHoffCapEdges_le_initial_add_shifted_error_terms
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀)
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (herr : (gateSelectorAtomsCoordN (universalGateAtoms eta heta)).errSel < 1 / 2)
    (hκ₀_nonneg : 0 ≤ (κ₀ : ℝ))
    (hg₀ : 0 < (g₀ : ℝ))
    (hscale : (κ₀ : ℝ) ≤ ((3 / 4 : ℝ) ^ Mcy) * (g₀ : ℝ))
    (hselect_start : ∀ w j,
      1 / (Fintype.card UniversalLocalView : ℝ) ≤
        (sol w).lam (localViewU (solMUReplStaticCfg w j))
          (selectorMUSelectStartTime j))
    (hutube_win : ∀ w j, ∀ t ∈ Set.Ico (selectorMUWriteStartTime j)
        (selectorMUWriteReadTime j),
      UTube r_LE_U (solMUReplStaticCfg w j) ((sol w).u t)) :
    ∀ w j, selectorMUHaltEncConstW solMUReplStaticCfg w j →
      let M : ℝ := stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 1)) haltCoordU
      let leftBad : ℝ :=
        ∫ τ in (selectorMUInterReadStart j)..(selectorMUZOffStart j),
          selectorMUHoffGateCoeff sol w τ *
            (Finset.univ.filter (fun v : UniversalLocalView =>
              v ≠ localViewU (solMUReplStaticCfg w j) ∧
                v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
                  (fun v => (sol w).lam v τ)
      let rightCross : ℝ :=
        ∫ τ in (selectorMUZOffEnd j)..(selectorMUEarlyWriteSubStart (j + 1)),
          selectorMUHoffGateCoeff sol w τ *
            (Finset.univ.filter (fun v : UniversalLocalView =>
              v ≠ localViewU (solMUReplStaticCfg w j) ∧
                v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
                  (fun v => (sol w).lam v τ)
      let rightLate : ℝ :=
        ∫ τ in (selectorMUEarlyWriteSubStart (j + 1))..
            (selectorMUWriteHoldTime (j + 1)),
          selectorMUHoffGateCoeff sol w τ *
            epsLamShiftedEarlyFullAt sol w
              (selectorReplicatorGapVal eta heta)
              (Fintype.card UniversalLocalView : ℝ) (j + 1)
      selectorMUHoffCapLeftField sol w j + selectorMUHoffCapRightField sol w j ≤
        |(sol w).z (selectorMUInterReadStart j) haltCoordU - M| +
          |(sol w).z (selectorMUZOffEnd j) haltCoordU - M| +
            2 * (leftBad + rightCross + rightLate) := by
  intro w j henc
  let M : ℝ := stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 1)) haltCoordU
  let leftBad : ℝ :=
    ∫ τ in (selectorMUInterReadStart j)..(selectorMUZOffStart j),
      selectorMUHoffGateCoeff sol w τ *
        (Finset.univ.filter (fun v : UniversalLocalView =>
          v ≠ localViewU (solMUReplStaticCfg w j) ∧
            v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
              (fun v => (sol w).lam v τ)
  let rightCross : ℝ :=
    ∫ τ in (selectorMUZOffEnd j)..(selectorMUEarlyWriteSubStart (j + 1)),
      selectorMUHoffGateCoeff sol w τ *
        (Finset.univ.filter (fun v : UniversalLocalView =>
          v ≠ localViewU (solMUReplStaticCfg w j) ∧
            v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
              (fun v => (sol w).lam v τ)
  let rightLate : ℝ :=
    ∫ τ in (selectorMUEarlyWriteSubStart (j + 1))..
        (selectorMUWriteHoldTime (j + 1)),
      selectorMUHoffGateCoeff sol w τ *
        epsLamShiftedEarlyFullAt sol w
          (selectorReplicatorGapVal eta heta)
          (Fintype.card UniversalLocalView : ℝ) (j + 1)
  have hleft := selectorMUHoffCapLeftField_le_initial_add_old_new_loser_integral
    (sol := sol) boxInputs w j henc
  have hright := selectorMUHoffCapRightField_le_initial_add_cross_old_new_late_shifted
    sol boxInputs herr hκ₀_nonneg hg₀ hscale hselect_start hutube_win w j henc
  dsimp only
  change
    selectorMUHoffCapLeftField sol w j + selectorMUHoffCapRightField sol w j ≤
      |(sol w).z (selectorMUInterReadStart j) haltCoordU - M| +
        |(sol w).z (selectorMUZOffEnd j) haltCoordU - M| +
          2 * (leftBad + rightCross + rightLate)
  have hleft' :
      selectorMUHoffCapLeftField sol w j ≤
        |(sol w).z (selectorMUInterReadStart j) haltCoordU - M| + 2 * leftBad := by
    simpa [M, leftBad] using hleft
  have hright' :
      selectorMUHoffCapRightField sol w j ≤
        |(sol w).z (selectorMUZOffEnd j) haltCoordU - M| +
          2 * (rightCross + rightLate) := by
    simpa [M, rightCross, rightLate] using hright
  nlinarith [hleft', hright']

/-- Refined actual Hoff edge-cap reduction after splitting the right
cross-boundary term at the next write start and select start.  The remaining
prefix gate integrals are explicit scalar/dynamic obligations rather than
hidden inside `rightCross`. -/
theorem selectorMUHoffCapEdges_le_initial_add_refined_shifted_error_terms
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀)
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (herr : (gateSelectorAtomsCoordN (universalGateAtoms eta heta)).errSel < 1 / 2)
    (hκ₀_nonneg : 0 ≤ (κ₀ : ℝ))
    (hg₀ : 0 < (g₀ : ℝ))
    (hscale : (κ₀ : ℝ) ≤ ((3 / 4 : ℝ) ^ Mcy) * (g₀ : ℝ))
    (hselect_start : ∀ w j,
      1 / (Fintype.card UniversalLocalView : ℝ) ≤
        (sol w).lam (localViewU (solMUReplStaticCfg w j))
          (selectorMUSelectStartTime j))
    (hutube_win : ∀ w j, ∀ t ∈ Set.Ico (selectorMUWriteStartTime j)
        (selectorMUWriteReadTime j),
      UTube r_LE_U (solMUReplStaticCfg w j) ((sol w).u t)) :
    ∀ w j, selectorMUHaltEncConstW solMUReplStaticCfg w j →
      let M : ℝ := stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 1)) haltCoordU
      let leftBad : ℝ :=
        ∫ τ in (selectorMUInterReadStart j)..(selectorMUZOffStart j),
          selectorMUHoffGateCoeff sol w τ *
            (Finset.univ.filter (fun v : UniversalLocalView =>
              v ≠ localViewU (solMUReplStaticCfg w j) ∧
                v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
                  (fun v => (sol w).lam v τ)
      let prewriteGate : ℝ :=
        ∫ τ in (selectorMUZOffEnd j)..(selectorMUWriteStartTime (j + 1)),
          selectorMUHoffGateCoeff sol w τ
      let recoveryGate : ℝ :=
        ∫ τ in (selectorMUWriteStartTime (j + 1))..
            (selectorMUSelectStartTime (j + 1)),
          selectorMUHoffGateCoeff sol w τ
      let postSelectNewLoser : ℝ :=
        ∫ τ in (selectorMUSelectStartTime (j + 1))..
            (selectorMUEarlyWriteSubStart (j + 1)),
          selectorMUHoffGateCoeff sol w τ *
            (Finset.univ.filter (fun v : UniversalLocalView =>
              v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
                (fun v => (sol w).lam v τ)
      let rightLate : ℝ :=
        ∫ τ in (selectorMUEarlyWriteSubStart (j + 1))..
            (selectorMUWriteHoldTime (j + 1)),
          selectorMUHoffGateCoeff sol w τ *
            epsLamShiftedEarlyFullAt sol w
              (selectorReplicatorGapVal eta heta)
              (Fintype.card UniversalLocalView : ℝ) (j + 1)
      selectorMUHoffCapLeftField sol w j + selectorMUHoffCapRightField sol w j ≤
        |(sol w).z (selectorMUInterReadStart j) haltCoordU - M| +
          |(sol w).z (selectorMUZOffEnd j) haltCoordU - M| +
            2 * (leftBad + (prewriteGate + recoveryGate + postSelectNewLoser) + rightLate) := by
  intro w j henc
  let M : ℝ := stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 1)) haltCoordU
  let leftBad : ℝ :=
    ∫ τ in (selectorMUInterReadStart j)..(selectorMUZOffStart j),
      selectorMUHoffGateCoeff sol w τ *
        (Finset.univ.filter (fun v : UniversalLocalView =>
          v ≠ localViewU (solMUReplStaticCfg w j) ∧
            v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
              (fun v => (sol w).lam v τ)
  let rightCross : ℝ :=
    ∫ τ in (selectorMUZOffEnd j)..(selectorMUEarlyWriteSubStart (j + 1)),
      selectorMUHoffGateCoeff sol w τ *
        (Finset.univ.filter (fun v : UniversalLocalView =>
          v ≠ localViewU (solMUReplStaticCfg w j) ∧
            v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
              (fun v => (sol w).lam v τ)
  let prewriteGate : ℝ :=
    ∫ τ in (selectorMUZOffEnd j)..(selectorMUWriteStartTime (j + 1)),
      selectorMUHoffGateCoeff sol w τ
  let recoveryGate : ℝ :=
    ∫ τ in (selectorMUWriteStartTime (j + 1))..
        (selectorMUSelectStartTime (j + 1)),
      selectorMUHoffGateCoeff sol w τ
  let postSelectNewLoser : ℝ :=
    ∫ τ in (selectorMUSelectStartTime (j + 1))..
        (selectorMUEarlyWriteSubStart (j + 1)),
      selectorMUHoffGateCoeff sol w τ *
        (Finset.univ.filter (fun v : UniversalLocalView =>
          v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
            (fun v => (sol w).lam v τ)
  let rightLate : ℝ :=
    ∫ τ in (selectorMUEarlyWriteSubStart (j + 1))..
        (selectorMUWriteHoldTime (j + 1)),
      selectorMUHoffGateCoeff sol w τ *
        epsLamShiftedEarlyFullAt sol w
          (selectorReplicatorGapVal eta heta)
          (Fintype.card UniversalLocalView : ℝ) (j + 1)
  have hbase := selectorMUHoffCapEdges_le_initial_add_shifted_error_terms
    sol boxInputs herr hκ₀_nonneg hg₀ hscale hselect_start hutube_win w j henc
  have hcross :=
    selectorMUHoff_right_cross_old_new_loser_integral_le_prefix_gates_add_new_loser
      (sol := sol) boxInputs w j
  dsimp only
  change
    selectorMUHoffCapLeftField sol w j + selectorMUHoffCapRightField sol w j ≤
      |(sol w).z (selectorMUInterReadStart j) haltCoordU - M| +
        |(sol w).z (selectorMUZOffEnd j) haltCoordU - M| +
          2 * (leftBad + (prewriteGate + recoveryGate + postSelectNewLoser) + rightLate)
  have hbase' :
      selectorMUHoffCapLeftField sol w j + selectorMUHoffCapRightField sol w j ≤
        |(sol w).z (selectorMUInterReadStart j) haltCoordU - M| +
          |(sol w).z (selectorMUZOffEnd j) haltCoordU - M| +
            2 * (leftBad + rightCross + rightLate) := by
    simpa [M, leftBad, rightCross, rightLate] using hbase
  have hcross' : rightCross ≤ prewriteGate + recoveryGate + postSelectNewLoser := by
    simpa [rightCross, prewriteGate, recoveryGate, postSelectNewLoser] using hcross
  nlinarith [hbase', hcross']

/-- Direct read-start residual from the shifted concentration package.

The old rate-concentration wrapper carries a full-window floor premise that
the shifted route no longer has.  This proof uses only the settled-window
loser mass supplied by `MUReplicatorShiftedConcentrationAt`, which is the part
needed by the read-start z-write endpoint estimate. -/
def mu_replicator_late_start_read_start_of_shifted
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (shifted : ∀ w, MUReplicatorShiftedConcentrationAt sol w) :
    MUReplicatorLateStartReadStartResidual sol where
  Bz_read := fun w j =>
    solMUReplSettledRho (fun j => selectorSettledWriteIntLower j)
      (fun _j => (1 : ℝ)) (shiftedEpsLam shifted w) j
  hz_read_start := by
    intro w j
    let δ : ℕ → ℝ := shiftedEpsLam shifted w
    have heps_nonneg : 0 ≤ shiftedEpsLam shifted w j := by
      have ht : selectorMUWriteHoldTime j ∈
          Icc (selectorMUWriteHoldTime j) (selectorMUWriteReadTime j) :=
        ⟨le_rfl, selectorMUWriteHold_le_read j⟩
      have hlam_nonneg :=
        solMURepl_static_hlam_nonneg boxInputs w j (selectorMUWriteHoldTime j) ht
      have hloser_nonneg :
          0 ≤ (Finset.univ.filter (fun v : UniversalLocalView =>
            v ≠ localViewU (solMUReplStaticCfg w j))).sum
              (fun v => (sol w).lam v (selectorMUWriteHoldTime j)) := by
        exact Finset.sum_nonneg (fun v _hv => hlam_nonneg v)
      exact le_trans hloser_nonneg
        (shifted_p_hloser shifted w j (selectorMUWriteHoldTime j) ht)
    have hmix : ∀ t ∈ Icc (selectorMUWriteHoldTime j)
        (selectorMUWriteReadTime j),
        |selectorMixTarget branchU (sol w).u (sol w).lam t haltCoordU -
          stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 1)) haltCoordU| ≤
            δ j := by
      intro t ht
      have hsum := solMURepl_static_hsum boxInputs w j t ht
      have hlam_nonneg := solMURepl_static_hlam_nonneg boxInputs w j t ht
      have hraw :=
        selectorMixTarget_halt_to_next_of_loser_sum_sharp
          (sol w).u (sol w).lam t (solMUReplStaticCfg w j)
          hsum hlam_nonneg (shifted_p_hloser shifted w j t ht)
      simpa [δ, shiftedEpsLam, solMUReplStaticCfg_step w j] using hraw
    have hendpoint :=
      z_write_settled_endpoint (sol w) (fun j => solMUReplStaticCfg w j)
        (fun j => selectorSettledWriteIntLower j) (fun _j => (1 : ℝ)) δ
        j haltCoordU
        (solMURepl_static_hdom_write w j) (solMURepl_static_hgZ_cont sol w)
        (solMURepl_static_hgZ0 sol w j) hmix
        (boxInputs.hz_writeHold_static_next_le_one w j)
        (selectorSettledWriteIntLower_le_gateZ_integral sol w j)
    simpa [δ, solMUReplSettledRho, selectorMUWriteReadTime] using hendpoint
  hBz_read_tendsto := by
    intro w
    have hctr :
        Tendsto
          (fun j : ℕ =>
            selectorZWriteContraction (fun j => selectorSettledWriteIntLower j)
              (fun _j => (1 : ℝ)) j) atTop (𝓝 0) := by
      simpa using
        solMURepl_expNegLambda_Bz0_tendsto_zero
          (Λ := fun _w j => selectorSettledWriteIntLower j)
          (Bz0 := fun _w _j => (1 : ℝ)) (w := 0) (Bz0max := (1 : ℝ))
          (by simpa using selectorSettledWriteIntLower_tendsto_atTop)
          (Filter.Eventually.of_forall (fun _j => by norm_num))
          (Filter.Eventually.of_forall (fun _j => le_rfl))
    have hδ :
        Tendsto (shiftedEpsLam shifted w) atTop (𝓝 0) := by
      simpa [shiftedEpsLam] using (shifted w).hεLam
    simpa [solMUReplSettledRho, selectorZWriteContraction] using hctr.add hδ
  hBz_read_nonneg := by
    intro w j
    have heps_nonneg : 0 ≤ shiftedEpsLam shifted w j := by
      have ht : selectorMUWriteHoldTime j ∈
          Icc (selectorMUWriteHoldTime j) (selectorMUWriteReadTime j) :=
        ⟨le_rfl, selectorMUWriteHold_le_read j⟩
      have hlam_nonneg :=
        solMURepl_static_hlam_nonneg boxInputs w j (selectorMUWriteHoldTime j) ht
      have hloser_nonneg :
          0 ≤ (Finset.univ.filter (fun v : UniversalLocalView =>
            v ≠ localViewU (solMUReplStaticCfg w j))).sum
              (fun v => (sol w).lam v (selectorMUWriteHoldTime j)) := by
        exact Finset.sum_nonneg (fun v _hv => hlam_nonneg v)
      exact le_trans hloser_nonneg
        (shifted_p_hloser shifted w j (selectorMUWriteHoldTime j) ht)
    dsimp [solMUReplSettledRho, shiftedEpsLam]
    exact add_nonneg (mul_nonneg (Real.exp_pos _).le (by norm_num))
      heps_nonneg

/-- The shifted read-start residual has the concrete settled-contraction shape:
one endpoint contraction term plus the halt-mix error induced by shifted
loser concentration. -/
theorem mu_replicator_late_start_read_start_of_shifted_Bz_read_eq
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (shifted : ∀ w, MUReplicatorShiftedConcentrationAt sol w)
    (w j : ℕ) :
    (mu_replicator_late_start_read_start_of_shifted
      (sol := sol) boxInputs shifted).Bz_read w j =
      Real.exp (-(selectorSettledWriteIntLower j)) + (shifted w).epsLam j := by
  simp [mu_replicator_late_start_read_start_of_shifted, solMUReplSettledRho,
    shiftedEpsLam]

/-- Pointwise upper bound for the shifted read-start residual from any
pointwise upper bound on the shifted loser radius. -/
theorem mu_replicator_late_start_read_start_of_shifted_Bz_read_le
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (shifted : ∀ w, MUReplicatorShiftedConcentrationAt sol w)
    {E : ℕ → ℝ} {w j : ℕ}
    (hE : (shifted w).epsLam j ≤ E j) :
    (mu_replicator_late_start_read_start_of_shifted
      (sol := sol) boxInputs shifted).Bz_read w j ≤
      Real.exp (-(selectorSettledWriteIntLower j)) + E j := by
  rw [mu_replicator_late_start_read_start_of_shifted_Bz_read_eq]
  linarith

namespace MUReplicatorNextWriteStartHoldStableMixResidual

/-- Convert the write-hold-frozen stability residual to write-reach endpoint
inputs, using shifted concentration directly for the halt-mix radius. -/
def toWriteReachShiftedResidual
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (res : MUReplicatorNextWriteStartHoldStableMixResidual sol)
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (shifted : ∀ w, MUReplicatorShiftedConcentrationAt sol w) :
    MUReplicatorNextWriteStartWriteReachResidual sol where
  a := fun _w j => selectorMUWriteStartTime j
  θ := fun _w j => selectorMUWriteHoldTime j
  Λ := fun _w j => selectorEarlyWriteIntLower j
  Bz0 := fun _w _j => (1 : ℝ)
  δw := res.δw
  εmix := selectorSettledHaltDeltaRate (shiftedEpsLam shifted)
  hwrite_le := by
    intro _w j
    exact selectorMUWriteStart_le_hold j
  hdom_write := selectorMU_hdom_writeHold
  hgZ_cont := by
    intro w
    exact selector_replicator_gateZ_integrand_continuous (sol w)
  hgZ0 := by
    intro w j t ht
    have ht0 : 0 ≤ t := le_trans (selectorMUWriteStartTime_nonneg j) ht.1
    exact selector_replicator_gateZ_integrand_nonneg (sol w)
      selectorSchedule_domain_of_nonneg_structural (by norm_num [bgpParams38]) ht0
  hmix_stable_z_write := res.hmix_stable_z_write_hold
  hz_start_mismatch_bound := by
    intro w j
    have hz := boxInputs.halt_z_mem_Icc w (selectorMUWriteStartTime j)
      (selectorMUWriteStartTime_nonneg j)
    have hhold0 : 0 ≤ selectorMUWriteHoldTime j :=
      le_trans (selectorMUWriteStartTime_nonneg j) (selectorMUWriteStart_le_hold j)
    have hm := boxInputs.halt_mixTarget_mem_Icc w (selectorMUWriteHoldTime j) hhold0
    exact abs_sub_le_one_of_unit_interval_pair hz hm
  hwriteInt_lbd_z := selectorMU_nextStart_hwriteInt_hold_lbd_z sol
  hmix_halt := by
    intro w j
    exact solMURepl_hmix_halt_on_settled_of_loser_rate boxInputs
      (shifted_p_hloser shifted) w j (selectorMUWriteHoldTime j)
      ⟨le_rfl, selectorMUWriteHold_le_read j⟩
  hwrite_tendsto := by
    intro w
    have hΛ :
        Tendsto ((fun _w j => selectorEarlyWriteIntLower j) w) atTop atTop := by
      simpa using selectorEarlyWriteIntLower_tendsto_atTop
    simpa [selectorZWriteContraction] using
      solMURepl_expNegLambda_Bz0_tendsto_zero
        (Λ := fun _w j => selectorEarlyWriteIntLower j)
        (Bz0 := fun _w _j => (1 : ℝ)) w (Bz0max := (1 : ℝ)) hΛ
        (Filter.Eventually.of_forall (fun _j => by norm_num))
        (Filter.Eventually.of_forall (fun _j => le_rfl))
  hδw := res.hδw
  hεmix := by
    intro w
    simpa [selectorSettledHaltDeltaRate, shiftedEpsLam] using
      Filter.Tendsto.const_mul (Fintype.card UniversalLocalView : ℝ)
        (shifted w).hεLam
  hBz0_nonneg := by
    intro _w _j
    norm_num
  hδw_nonneg := res.hδw_nonneg
  hεmix_nonneg := by
    intro w j
    exact mul_nonneg (Nat.cast_nonneg _) ((shifted w).hεLam_nonneg j)

/-- Directly produce the start-only residual from write-hold-frozen stability
and shifted concentration. -/
def toStartOnlyShiftedResidual
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (res : MUReplicatorNextWriteStartHoldStableMixResidual sol)
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (shifted : ∀ w, MUReplicatorShiftedConcentrationAt sol w) :
    MUReplicatorNextWriteStartOnlyResidual sol :=
  (res.toWriteReachShiftedResidual boxInputs shifted).toStartOnlyResidual

end MUReplicatorNextWriteStartHoldStableMixResidual

namespace MUReplicatorNextWriteStartWeightedHoldMixResidual

/-- Directly produce the start-only residual from the weighted write-hold
moving-target residual and shifted concentration. -/
def toStartOnlyShiftedResidual
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (res : MUReplicatorNextWriteStartWeightedHoldMixResidual sol)
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (shifted : ∀ w, MUReplicatorShiftedConcentrationAt sol w) :
    MUReplicatorNextWriteStartOnlyResidual sol where
  δstart := fun w j =>
    selectorReplicatorHStartRhoHalt
      (fun k => selectorEarlyWriteIntLower k)
      (fun _k => (1 : ℝ))
      (res.δw w)
      (selectorSettledHaltDeltaRate (shiftedEpsLam shifted) w)
      (j + 1)
  hδstart := by
    intro w
    have hΛ :
        Tendsto (fun j => selectorEarlyWriteIntLower j) atTop atTop := by
      simpa using selectorEarlyWriteIntLower_tendsto_atTop
    have hwrite :
        Tendsto
          (fun j =>
            Real.exp (-(selectorEarlyWriteIntLower j)) * (1 : ℝ))
          atTop (𝓝 0) := by
      simpa [selectorZWriteContraction] using
        solMURepl_expNegLambda_Bz0_tendsto_zero
          (Λ := fun _w j => selectorEarlyWriteIntLower j)
          (Bz0 := fun _w _j => (1 : ℝ)) w (Bz0max := (1 : ℝ)) hΛ
          (Filter.Eventually.of_forall (fun _j => by norm_num))
          (Filter.Eventually.of_forall (fun _j => le_rfl))
    have hεmix :
        Tendsto (selectorSettledHaltDeltaRate (shiftedEpsLam shifted) w)
          atTop (𝓝 0) := by
      simpa [selectorSettledHaltDeltaRate, shiftedEpsLam] using
        Filter.Tendsto.const_mul (Fintype.card UniversalLocalView : ℝ)
          (shifted w).hεLam
    have hbase :
        Tendsto
          (selectorReplicatorHStartRhoHalt
            (fun k => selectorEarlyWriteIntLower k)
            (fun _k => (1 : ℝ))
            (res.δw w)
            (selectorSettledHaltDeltaRate (shiftedEpsLam shifted) w))
          atTop (𝓝 0) :=
      selectorReplicatorHStartRhoHalt_tendsto_zero hwrite (res.hδw w) hεmix
    simpa using hbase.comp (Filter.tendsto_add_atTop_nat 1)
  hδstart_nonneg := by
    intro w j
    unfold selectorReplicatorHStartRhoHalt
    exact add_nonneg
      (add_nonneg
        (mul_nonneg (Real.exp_nonneg _) (by norm_num))
        (res.hδw_nonneg w (j + 1)))
      (mul_nonneg (Nat.cast_nonneg _) ((shifted w).hεLam_nonneg (j + 1)))
  p_hnextStart := by
    intro w j
    let cfg : ℕ → UConf := fun n => solMUReplStaticCfg w n
    have hcfg_step : ∀ n, cfg (n + 1) = M_U.step (cfg n) := by
      intro n
      dsimp [cfg]
      exact (solMUReplStaticCfg_step w n).symm
    have h :=
      selector_replicator_haltExact_endpoint_of_writeReach_weighted
        (sol := sol w) (cfg := cfg) (hcfg_step := hcfg_step)
        (a := fun k => selectorMUWriteStartTime k)
        (m := fun k => selectorMUWriteHoldTime k)
        (θ := fun k => selectorMUWriteHoldTime k)
        (Λ := fun k => selectorEarlyWriteIntLower k)
        (Bz0 := fun _k => (1 : ℝ))
        (δw := res.δw w)
        (εmix := selectorSettledHaltDeltaRate (shiftedEpsLam shifted) w)
        (ham := fun k => selectorMUWriteStart_le_hold k)
        (hdom_write := fun k => selectorMU_hdom_writeHold w k)
        (hgZ_cont := selector_replicator_gateZ_integrand_continuous (sol w))
        (hgZ0 := by
          intro k t ht
          have ht0 : 0 ≤ t := le_trans (selectorMUWriteStartTime_nonneg k) ht.1
          exact selector_replicator_gateZ_integrand_nonneg (sol w)
            selectorSchedule_domain_of_nonneg_structural (by norm_num [bgpParams38]) ht0)
        (hmix_weighted_z_write := res.hmix_weighted_z_write_hold w)
        (hz_start_mismatch_bound := by
          intro k
          have hz := boxInputs.halt_z_mem_Icc w (selectorMUWriteStartTime k)
            (selectorMUWriteStartTime_nonneg k)
          have hhold0 : 0 ≤ selectorMUWriteHoldTime k :=
            le_trans (selectorMUWriteStartTime_nonneg k) (selectorMUWriteStart_le_hold k)
          have hm := boxInputs.halt_mixTarget_mem_Icc w (selectorMUWriteHoldTime k) hhold0
          exact abs_sub_le_one_of_unit_interval_pair hz hm)
        (hwriteInt_lbd_z := selectorMU_nextStart_hwriteInt_hold_lbd_z sol w)
        (hmix_halt := by
          intro k
          exact solMURepl_hmix_halt_on_settled_of_loser_rate boxInputs
            (shifted_p_hloser shifted) w k (selectorMUWriteHoldTime k)
            ⟨le_rfl, selectorMUWriteHold_le_read k⟩)
        (j + 1)
    simpa [selectorMUNextWriteStart, cfg, Nat.add_assoc] using h

end MUReplicatorNextWriteStartWeightedHoldMixResidual

namespace MUReplicatorNextWriteStartOnlyResidual

/-- Fill the start+mix next-write residual from a start-only residual and the
shifted concentration package, without constructing the old full-window floor
rate residual. -/
def toStartMixShiftedResidual
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (res : MUReplicatorNextWriteStartOnlyResidual sol)
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (shifted : ∀ w, MUReplicatorShiftedConcentrationAt sol w) :
    MUReplicatorNextWriteStartMixResidual sol where
  δstart := res.δstart
  δmix := fun w j => selectorSettledHaltDeltaRate (shiftedEpsLam shifted) w (j + 1)
  hδstart := res.hδstart
  hδmix := by
    intro w
    have hshift := (shifted w).hεLam.comp (Filter.tendsto_add_atTop_nat 1)
    simpa [selectorSettledHaltDeltaRate, shiftedEpsLam] using
      Filter.Tendsto.const_mul (Fintype.card UniversalLocalView : ℝ) hshift
  hδstart_nonneg := res.hδstart_nonneg
  hδmix_nonneg := by
    intro w j
    exact mul_nonneg (Nat.cast_nonneg _) ((shifted w).hεLam_nonneg (j + 1))
  p_hnextStart := res.p_hnextStart
  p_hnextMix := by
    intro w j t ht
    simpa [shiftedEpsLam] using
      solMURepl_p_hnextMix_of_loser_rate boxInputs
        (shifted_p_hloser shifted) w j t ht

end MUReplicatorNextWriteStartOnlyResidual

end Ripple.BoundedUniversality.BGP
