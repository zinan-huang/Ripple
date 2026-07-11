import Ripple.BoundedUniversality.BGP.SelectorReplicatorShiftedConc
import Ripple.BoundedUniversality.BGP.SelectorReplicatorSelfHold
import Ripple.BoundedUniversality.BGP.SelectorReplicatorWarmHeadline
import Ripple.BoundedUniversality.BGP.SelectorReplicatorAvgGap
import Ripple.BoundedUniversality.BGP.BGPParams38

/-!
# Shifted settled construction and warm-gain assembly

This file packages the mid-window-anchor concentration route.  The old
`MUReplicatorSettledHaltFactsAt` interface is tied to the `WriteStart` anchor;
the shifted route instead produces the late-start read residual consumed by the
final halt/nonhalt endgame.
-/

noncomputable section

namespace Ripple.BoundedUniversality.BGP

open MachineInstance UniversalMachine Filter Set
open scoped BigOperators Topology

/-- Diagonal late-start halt facts at one fixed warm-gain input. -/
structure MUReplicatorLateStartHaltFactsAt
    {p : DynGateParams} {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamilyP p eta heta Mcy κ₀ g₀)
    (w : ℕ) where
  cfg : ℕ → UConf
  hcfg : ∀ j, cfg j = M_U.step^[j] (M_U.init w)
  Bz_read : ℕ → ℝ
  hz_read_start : ∀ j,
    |(sol w).z (selectorMUInterReadStart j) haltCoordU -
      stackMachineEncodingU.enc (cfg (j + 1)) haltCoordU| ≤ Bz_read j
  hBz_read_tendsto : Tendsto Bz_read atTop (𝓝 0)
  hBz_read_nonneg : ∀ j, 0 ≤ Bz_read j
  δnext : ℕ → ℝ
  holdPrefix : ℕ → ℝ
  hδnext : Tendsto δnext atTop (𝓝 0)
  hδnext_nonneg : ∀ j, 0 ≤ δnext j
  hholdPrefix_nonneg : ∀ j, 0 ≤ holdPrefix j
  hoff : ∀ j, selectorMUHaltEncConst cfg j → ∀ t ∈
      Icc (selectorMUInterReadStart j)
      (selectorMUNextWriteStart j),
    |(sol w).z t haltCoordU - (sol w).z (selectorMUInterReadStart j) haltCoordU| ≤
      selectorReplicatorHoldEnvelope j
  hnextWrite : ∀ j, ∀ t ∈ Icc (selectorMUNextWriteStart j)
      (selectorMUNextRead j),
    |(sol w).z t haltCoordU - stackMachineEncodingU.enc (cfg (j + 2)) haltCoordU| ≤
      δnext j
  hfiniteHold : ∀ j, ∀ t ∈ Icc (selectorMUInterReadStart j)
      (selectorMUNextRead j),
    |(sol w).z t haltCoordU - (sol w).z (selectorMUInterReadStart j) haltCoordU| ≤
      holdPrefix j

private theorem selectorMUSelectStart_nonneg (j : ℕ) :
    0 ≤ selectorMUSelectStartTime j := by
  exact le_trans (selectorMUWriteStartTime_nonneg j)
    (selectorMUWriteStart_le_selectStart j)

private theorem solMURepl_lam_sum_forward_P
    {p : DynGateParams}
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamilyP p eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputsP p eta heta Mcy κ₀ g₀ sol) :
    ∀ w, ∀ t : ℝ, 0 ≤ t →
      (∑ v : UniversalLocalView, (sol w).lam v t) = 1 := by
  classical
  intro w
  haveI : Nonempty UniversalLocalView := ⟨defaultLocalViewU⟩
  have hode : ∀ v : UniversalLocalView, ∀ t : ℝ, 0 ≤ t →
      HasDerivAt ((sol w).lam v)
        ((((1 + Real.cos t) / 2) ^ Mcy * (κ₀ : ℝ)) *
            (1 / (Fintype.card UniversalLocalView : ℝ) - (sol w).lam v t)
          + (((1 + Real.sin t) / 2) ^ Mcy *
              ((g₀ : ℝ) * Real.exp (p.cα * t))) *
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
          ((g₀ : ℝ) * Real.exp (p.cα * t)))
      boxInputs.hcr_cont boxInputs.hcg_cont
      (fun v => (sol w).cont_lam v)
      (boxInputs.hP_cont w) hode (boxInputs.hlam_sum0 w)

private theorem solMURepl_lam_nonneg_forward_P
    {p : DynGateParams}
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamilyP p eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputsP p eta heta Mcy κ₀ g₀ sol) :
    ∀ w, ∀ v : UniversalLocalView, ∀ t : ℝ, 0 ≤ t → 0 ≤ (sol w).lam v t := by
  classical
  intro w
  haveI : Nonempty UniversalLocalView := ⟨defaultLocalViewU⟩
  have hode : ∀ v : UniversalLocalView, ∀ t : ℝ, 0 ≤ t →
      HasDerivAt ((sol w).lam v)
        ((((1 + Real.cos t) / 2) ^ Mcy * (κ₀ : ℝ)) *
            (1 / (Fintype.card UniversalLocalView : ℝ) - (sol w).lam v t)
          + (((1 + Real.sin t) / 2) ^ Mcy *
              ((g₀ : ℝ) * Real.exp (p.cα * t))) *
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
          ((g₀ : ℝ) * Real.exp (p.cα * t)))
      boxInputs.hcr_cont boxInputs.hcg_cont
      (fun v => (sol w).cont_lam v)
      (boxInputs.hP_cont w) boxInputs.hcr_nonneg hode
      (boxInputs.hlam_init_nonneg w)

private theorem lam_ratio_card_bound_at
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

private theorem epsLamShiftedFullAt_nonneg
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀)
    (w : ℕ) {gap R0 : ℝ}
    (hgap0 : 0 < gap)
    (hR0_nonneg : 0 ≤ R0)
    (hκ₀_nonneg : 0 ≤ (κ₀ : ℝ)) :
    ∀ j, 0 ≤ epsLamShiftedFullAt sol w gap R0 j := by
  classical
  haveI : Nonempty UniversalLocalView := ⟨defaultLocalViewU⟩
  intro j
  unfold epsLamShiftedFullAt
  refine add_nonneg ?_ ?_
  · unfold epsLamShiftedAt epsLamSettled selectorSettledRatioEps selectorSettledRatioCoeff
    refine mul_nonneg ?_ ?_
    · have hcard_pos_nat :
          0 < Fintype.card UniversalLocalView := Fintype.card_pos_iff.mpr inferInstance
      have hcard_one : (1 : ℝ) ≤ Fintype.card UniversalLocalView := by
        exact_mod_cast hcard_pos_nat
      linarith
    · refine mul_nonneg ?_ (Real.exp_pos _).le
      refine add_nonneg hR0_nonneg ?_
      refine div_nonneg ?_ ?_
      · exact intervalIntegral.integral_nonneg_of_forall
          (le_of_lt (selectorMUSelectStart_lt_hold j))
          (fun s =>
            mul_nonneg (Real.exp_pos _).le
              (mul_nonneg (pow_nonneg (by nlinarith [Real.neg_one_le_cos s]) _)
                hκ₀_nonneg))
      · positivity
  · unfold epsLamShiftedTailAt
    refine mul_nonneg ?_ ?_
    · have hcard_pos_nat :
          0 < Fintype.card UniversalLocalView := Fintype.card_pos_iff.mpr inferInstance
      have hcard_one : (1 : ℝ) ≤ Fintype.card UniversalLocalView := by
        exact_mod_cast hcard_pos_nat
      linarith
    · exact div_nonneg (Real.exp_pos _).le hgap0.le

/-- Parameter-sensitive analytic inputs for the shifted late-start constructor
at one fixed diagonal input `w`. -/
structure MUReplicatorSettledAnalyticP
    {p : DynGateParams}
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamilyP p eta heta Mcy κ₀ g₀)
    (w : ℕ) where
  hcα_pos : 0 < p.cα
  epsLam : ℕ → ℝ
  hεLam_nonneg : ∀ j, 0 ≤ epsLam j
  hεLam_tendsto : Tendsto epsLam atTop (𝓝 0)
  hloser : ∀ j, ∀ t ∈
      Icc (selectorMUWriteHoldTime j) (selectorMUWriteReadTime j),
    (Finset.univ.filter (fun v : UniversalLocalView =>
      v ≠ localViewU (solMUReplStaticCfg w j))).sum
        (fun v => (sol w).lam v t) ≤ epsLam j
  Λ : ℕ → ℝ
  hΛ_lower : ∀ j,
    Λ j ≤ ∫ τ in selectorMUWriteHoldTime j..selectorMUWriteReadTime j,
      p.A * (sol w).α τ * bGateZ p.L ((sol w).μ τ) τ
  hΛ_tendsto : Tendsto Λ atTop atTop

/-- Parameter-generic shifted concentration package at one diagonal input. -/
structure MUReplicatorShiftedConcentrationAtP
    {p : DynGateParams}
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamilyP p eta heta Mcy κ₀ g₀)
    (w : ℕ) where
  epsLam : ℕ → ℝ
  hεLam : Tendsto epsLam atTop (𝓝 0)
  hεLam_nonneg : ∀ j, 0 ≤ epsLam j
  p_hloser : ∀ j, ∀ t ∈ Icc (selectorMUWriteHoldTime j)
      (selectorMUWriteReadTime j),
    (Finset.univ.filter (fun v : UniversalLocalView =>
      v ≠ localViewU (solMUReplStaticCfg w j))).sum
        (fun v => (sol w).lam v t) ≤ epsLam j

/-- Standalone shifted concentration package at one diagonal input.

This is the reusable output of the shifted select-start concentration argument:
an explicit per-cycle loser radius, its convergence to zero, nonnegativity, and
the settled-window loser-mass bound.  It deliberately does not carry the old
full-window `hqL` premise, which is false at `WriteStart`. -/
structure MUReplicatorShiftedConcentrationAt
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀)
    (w : ℕ) where
  epsLam : ℕ → ℝ
  hεLam : Tendsto epsLam atTop (𝓝 0)
  hεLam_nonneg : ∀ j, 0 ≤ epsLam j
  p_hloser : ∀ j, ∀ t ∈ Icc (selectorMUWriteHoldTime j)
      (selectorMUWriteReadTime j),
    (Finset.univ.filter (fun v : UniversalLocalView =>
      v ≠ localViewU (solMUReplStaticCfg w j))).sum (fun v => (sol w).lam v t) ≤
        epsLam j

/-- The legacy 38 analytic producer used by the exact compatibility façade. -/
private def muReplicatorShiftedConcentrationAt_of_selectStart_38_impl
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀)
    (w : ℕ)
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (herr : (gateSelectorAtomsCoordN (universalGateAtoms eta heta)).errSel < 1 / 2)
    (hκ₀_nonneg : 0 ≤ (κ₀ : ℝ))
    (hg₀ : 0 < (g₀ : ℝ))
    (hscale : (κ₀ : ℝ) ≤ ((3 / 4 : ℝ) ^ Mcy) * (g₀ : ℝ))
    (hselect_start : ∀ j,
      1 / (Fintype.card UniversalLocalView : ℝ) ≤
        (sol w).lam (localViewU (solMUReplStaticCfg w j))
          (selectorMUSelectStartTime j))
    (hutube_win : ∀ j, ∀ t ∈ Set.Ico (selectorMUWriteStartTime j)
        (selectorMUWriteReadTime j),
      UTube r_LE_U (solMUReplStaticCfg w j) ((sol w).u t)) :
    MUReplicatorShiftedConcentrationAt sol w := by
  classical
  haveI : Nonempty UniversalLocalView := ⟨defaultLocalViewU⟩
  let gap : ℝ := selectorReplicatorGapVal eta heta
  let R0 : ℝ := Fintype.card UniversalLocalView
  let epsLam : ℕ → ℝ := epsLamShiftedFullAt sol w gap R0
  have hgap0 : 0 < gap := by
    simpa [gap] using solMURepl_static_hgap0 eta heta herr
  have hR0_nonneg : 0 ≤ R0 := by
    dsimp [R0]
    positivity
  have hsum_forward := solMURepl_lam_sum_forward_P (sol := sol) boxInputs
  have hlam_forward := solMURepl_lam_nonneg_forward_P (sol := sol) boxInputs
  have hqL_select :
      ∀ j, ∀ t ∈ Icc (selectorMUSelectStartTime j)
          (selectorMUWriteReadTime j),
        1 / (Fintype.card UniversalLocalView : ℝ) ≤
          (sol w).lam (localViewU (solMUReplStaticCfg w j)) t := by
    intro j
    have hgap_floor :
        ∀ v : UniversalLocalView, v ≠ localViewU (solMUReplStaticCfg w j) →
          ∀ t ∈ Ico (selectorMUSelectStartTime j) (selectorMUWriteReadTime j),
            universalPval eta heta v ((sol w).u t) -
              universalPval eta heta (localViewU (solMUReplStaticCfg w j)) ((sol w).u t) ≤ 0 := by
      intro v hv t ht
      have hgap_full :=
        selector_replicator_hgap_of_utube
          (sol := fun _ : ℕ => sol w)
          (cfg := fun _ j => solMUReplStaticCfg w j)
          herr
          (fun _ j t ht => hutube_win j t ht)
      have hnonpos : -(gap) ≤ 0 := by
        exact neg_nonpos.mpr hgap0.le
      exact le_trans
        (by
          have ht_full : t ∈ Ico (selectorMUWriteStartTime j)
              (selectorMUWriteReadTime j) :=
            ⟨le_trans (selectorMUWriteStart_le_selectStart j) ht.1, ht.2⟩
          simpa [gap] using hgap_full 0 j v hv t ht_full)
        hnonpos
    have hbar :=
      replicator_winner_floor_on_interval_param
        (sol := sol w) (localViewU (solMUReplStaticCfg w j))
        (a := selectorMUSelectStartTime j) (b := selectorMUWriteReadTime j)
        (selectorMUSelectStart_le_read j)
        (1 / (Fintype.card UniversalLocalView : ℝ)) (le_refl _)
        (fun t ht => solMURepl_static_hdom_nonneg t
          (le_trans (selectorMUSelectStart_nonneg j) ht.1))
        (fun t _ht => boxInputs.hcr_nonneg t)
        (fun t _ht =>
          mul_nonneg
            (pow_nonneg (by nlinarith [Real.neg_one_le_sin t]) _)
            (mul_nonneg hg₀.le (Real.exp_pos _).le))
        hgap_floor
        (fun t ht => hsum_forward w t
          (le_trans (selectorMUSelectStart_nonneg j) ht.1))
        (fun v t ht => hlam_forward w v t
          (le_trans (selectorMUSelectStart_nonneg j) ht.1))
        (hselect_start j)
    exact hbar
  have hRa_select :
      ∀ j, ∀ v : UniversalLocalView, v ≠ localViewU (solMUReplStaticCfg w j) →
        (sol w).lam v (selectorMUSelectStartTime j) /
            (sol w).lam (localViewU (solMUReplStaticCfg w j))
              (selectorMUSelectStartTime j) ≤ R0 := by
    intro j
    have hsum := hsum_forward w (selectorMUSelectStartTime j)
      (selectorMUSelectStart_nonneg j)
    have hnonneg : ∀ v : UniversalLocalView,
        0 ≤ (sol w).lam v (selectorMUSelectStartTime j) :=
      fun v => hlam_forward w v (selectorMUSelectStartTime j)
        (selectorMUSelectStart_nonneg j)
    simpa [R0] using
      lam_ratio_card_bound_at
        (lam := fun v : UniversalLocalView => (sol w).lam v (selectorMUSelectStartTime j))
        (vstar := localViewU (solMUReplStaticCfg w j))
        hsum hnonneg (hselect_start j)
  have hloser :
      ∀ j, ∀ t ∈ Icc (selectorMUWriteHoldTime j)
          (selectorMUWriteReadTime j),
        (Finset.univ.filter (fun v : UniversalLocalView =>
          v ≠ localViewU (solMUReplStaticCfg w j))).sum (fun v => (sol w).lam v t) ≤
            epsLam j := by
    intro j
    have hgap_cond :
        ∀ v : UniversalLocalView, v ≠ localViewU (solMUReplStaticCfg w j) →
          ∀ t ∈ Ico (selectorMUSelectStartTime j) (selectorMUWriteReadTime j),
            universalPval eta heta v ((sol w).u t) -
              universalPval eta heta (localViewU (solMUReplStaticCfg w j))
                ((sol w).u t) ≤ -gap := by
      intro v hv t ht
      have hgap_full :=
        selector_replicator_hgap_of_utube
          (sol := fun _ : ℕ => sol w)
          (cfg := fun _ j => solMUReplStaticCfg w j)
          herr
          (fun _ j t ht => hutube_win j t ht)
      have ht_full : t ∈ Ico (selectorMUWriteStartTime j)
          (selectorMUWriteReadTime j) :=
        ⟨le_trans (selectorMUWriteStart_le_selectStart j) ht.1, ht.2⟩
      simpa [gap] using hgap_full 0 j v hv t ht_full
    have hloser_j := hloser_of_shifted_concentration
      (sol := sol) (cfg := fun j => solMUReplStaticCfg w j)
      w j (gap := gap) (R0 := R0)
      hgap0 hR0_nonneg hκ₀_nonneg hscale
      (fun t ht => solMURepl_static_hdom_nonneg t
        (le_trans (selectorMUSelectStart_nonneg j) ht.1))
      (hqL_select j)
      (fun v t ht => hlam_forward w v t
        (le_trans (selectorMUSelectStart_nonneg j) ht.1))
      (fun t ht => hsum_forward w t
        (le_trans (selectorMUSelectStart_nonneg j) ht.1))
      hgap_cond
      (hRa_select j)
    simpa [epsLam] using hloser_j
  have hepsLam_tendsto : Tendsto epsLam atTop (𝓝 0) := by
    simpa [epsLam, gap, R0] using
      epsLamShiftedFull_tendsto_zero sol w hg₀ hgap0 hR0_nonneg hκ₀_nonneg hscale
  have hepsLam_nonneg : ∀ j, 0 ≤ epsLam j := by
    intro j
    simpa [epsLam, gap, R0] using
      epsLamShiftedFullAt_nonneg sol w hgap0 hR0_nonneg hκ₀_nonneg j
  exact
  { epsLam := epsLam
    hεLam := hepsLam_tendsto
    hεLam_nonneg := hepsLam_nonneg
    p_hloser := hloser }

/-- Package an abstract shifted analytic input as a concentration result. -/
def muReplicatorShiftedConcentrationAt_of_selectStart_P
    {p : DynGateParams}
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamilyP p eta heta Mcy κ₀ g₀)
    (w : ℕ)
    (analytic : MUReplicatorSettledAnalyticP sol w) :
    MUReplicatorShiftedConcentrationAtP sol w where
  epsLam := analytic.epsLam
  hεLam := analytic.hεLam_tendsto
  hεLam_nonneg := analytic.hεLam_nonneg
  p_hloser := analytic.hloser

/-- The concrete 38 discharge of `MUReplicatorSettledAnalyticP` from the
existing shifted-concentration and settled-write lemmas. -/
def muReplicatorSettledAnalytic38_of_selectStart
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀)
    (w : ℕ)
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (herr :
      (gateSelectorAtomsCoordN (universalGateAtoms eta heta)).errSel < 1 / 2)
    (hκ₀_nonneg : 0 ≤ (κ₀ : ℝ))
    (hg₀ : 0 < (g₀ : ℝ))
    (hscale : (κ₀ : ℝ) ≤ ((3 / 4 : ℝ) ^ Mcy) * (g₀ : ℝ))
    (hselect_start : ∀ j,
      1 / (Fintype.card UniversalLocalView : ℝ) ≤
        (sol w).lam (localViewU (solMUReplStaticCfg w j))
          (selectorMUSelectStartTime j))
    (hutube_win : ∀ j, ∀ t ∈ Set.Ico (selectorMUWriteStartTime j)
        (selectorMUWriteReadTime j),
      UTube r_LE_U (solMUReplStaticCfg w j) ((sol w).u t)) :
    MUReplicatorSettledAnalyticP sol w := by
  let conc :=
    muReplicatorShiftedConcentrationAt_of_selectStart_38_impl
      sol w boxInputs herr hκ₀_nonneg hg₀ hscale hselect_start hutube_win
  exact
  { hcα_pos := by norm_num [bgpParams38]
    epsLam := conc.epsLam
    hεLam_nonneg := conc.hεLam_nonneg
    hεLam_tendsto := conc.hεLam
    hloser := conc.p_hloser
    Λ := selectorSettledWriteIntLower
    hΛ_lower := by
      intro j
      have hdom_nonneg := solMURepl_static_hdom_nonneg
      have hgZ_cont := solMURepl_static_hgZ_cont sol w
      have hgZ0 := solMURepl_static_hgZ0 sol
      have hsub :=
        selector_settled_writeIntegral_lower_lbd_repl
          (sol w) j hdom_nonneg hgZ_cont
      have hcont_int : ∀ a b : ℝ,
          IntervalIntegrable
            (fun t : ℝ => bgpParams38.A * (sol w).α t *
              bGateZ bgpParams38.L ((sol w).μ t) t)
            MeasureTheory.volume a b :=
        fun a b => hgZ_cont.intervalIntegrable a b
      have hadd := intervalIntegral.integral_add_adjacent_intervals
        (hcont_int (selectorMUWriteHoldTime j)
          (selectorMUSettledWriteSubEnd j))
        (hcont_int (selectorMUSettledWriteSubEnd j)
          (selectorMUWriteReadTime j))
      have htail_nonneg :
          0 ≤ ∫ t in selectorMUSettledWriteSubEnd j..
              selectorMUWriteReadTime j,
            bgpParams38.A * (sol w).α t *
              bGateZ bgpParams38.L ((sol w).μ t) t := by
        apply intervalIntegral.integral_nonneg
          (selectorMUSettledSubEnd_le_read j)
        intro t ht
        exact hgZ0 w j t
          ⟨le_trans (selectorMUWriteHold_le_settledSubEnd j) ht.1, ht.2⟩
      linarith
    hΛ_tendsto := selectorSettledWriteIntLower_tendsto_atTop }

/-- Produce the standalone shifted concentration package from the recovered
select-start floor and the full write-window `UTube`. -/
def muReplicatorShiftedConcentrationAt_of_selectStart
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀)
    (w : ℕ)
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (herr : (gateSelectorAtomsCoordN (universalGateAtoms eta heta)).errSel < 1 / 2)
    (hκ₀_nonneg : 0 ≤ (κ₀ : ℝ))
    (hg₀ : 0 < (g₀ : ℝ))
    (hscale : (κ₀ : ℝ) ≤ ((3 / 4 : ℝ) ^ Mcy) * (g₀ : ℝ))
    (hselect_start : ∀ j,
      1 / (Fintype.card UniversalLocalView : ℝ) ≤
        (sol w).lam (localViewU (solMUReplStaticCfg w j))
          (selectorMUSelectStartTime j))
    (hutube_win : ∀ j, ∀ t ∈ Set.Ico (selectorMUWriteStartTime j)
        (selectorMUWriteReadTime j),
      UTube r_LE_U (solMUReplStaticCfg w j) ((sol w).u t)) :
    MUReplicatorShiftedConcentrationAt sol w := by
  let analytic :=
    muReplicatorSettledAnalytic38_of_selectStart
      sol w boxInputs herr hκ₀_nonneg hg₀ hscale hselect_start hutube_win
  let shifted :=
    muReplicatorShiftedConcentrationAt_of_selectStart_P sol w analytic
  exact
  { epsLam := shifted.epsLam
    hεLam := shifted.hεLam
    hεLam_nonneg := shifted.hεLam_nonneg
    p_hloser := shifted.p_hloser }

/-- The shifted concentration constructor exposes the concrete Duhamel radius
`epsLamShiftedFullAt` as its loser-mass envelope. -/
theorem muReplicatorShiftedConcentrationAt_of_selectStart_epsLam
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀)
    (w : ℕ)
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (herr : (gateSelectorAtomsCoordN (universalGateAtoms eta heta)).errSel < 1 / 2)
    (hκ₀_nonneg : 0 ≤ (κ₀ : ℝ))
    (hg₀ : 0 < (g₀ : ℝ))
    (hscale : (κ₀ : ℝ) ≤ ((3 / 4 : ℝ) ^ Mcy) * (g₀ : ℝ))
    (hselect_start : ∀ j,
      1 / (Fintype.card UniversalLocalView : ℝ) ≤
        (sol w).lam (localViewU (solMUReplStaticCfg w j))
          (selectorMUSelectStartTime j))
    (hutube_win : ∀ j, ∀ t ∈ Set.Ico (selectorMUWriteStartTime j)
        (selectorMUWriteReadTime j),
      UTube r_LE_U (solMUReplStaticCfg w j) ((sol w).u t))
    (j : ℕ) :
    (muReplicatorShiftedConcentrationAt_of_selectStart sol w boxInputs
      herr hκ₀_nonneg hg₀ hscale hselect_start hutube_win).epsLam j =
      epsLamShiftedFullAt sol w (selectorReplicatorGapVal eta heta)
        (Fintype.card UniversalLocalView : ℝ) j := by
  rfl

/-- Shifted diagonal late-start constructor from the recovered select-start floor.

The caller supplies recovery at `selectorMUSelectStartTime`; this constructor
uses the barrier to propagate the winner floor, applies shifted concentration,
then feeds the abstract settled z-write theorem. -/
private def muReplicatorLateStartHaltFactsAt_shifted_of_selectStart_38_impl
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀)
    (w : ℕ)
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (herr : (gateSelectorAtomsCoordN (universalGateAtoms eta heta)).errSel < 1 / 2)
    (hκ₀_nonneg : 0 ≤ (κ₀ : ℝ))
    (hg₀ : 0 < (g₀ : ℝ))
    (hscale : (κ₀ : ℝ) ≤ ((3 / 4 : ℝ) ^ Mcy) * (g₀ : ℝ))
    (hselect_start : ∀ j,
      1 / (Fintype.card UniversalLocalView : ℝ) ≤
        (sol w).lam (localViewU (solMUReplStaticCfg w j))
          (selectorMUSelectStartTime j))
    (hutube_win : ∀ j, ∀ t ∈ Set.Ico (selectorMUWriteStartTime j)
        (selectorMUWriteReadTime j),
      UTube r_LE_U (solMUReplStaticCfg w j) ((sol w).u t))
    (Bz : ℕ → ℝ) (Bzmax : ℝ)
    (δnext : ℕ → ℝ) (holdPrefix : ℕ → ℝ)
    (hBz_nonneg : ∀ j, 0 ≤ Bz j)
    (hBz_bdd : ∀ᶠ j in atTop, Bz j ≤ Bzmax)
    (hδnext : Tendsto δnext atTop (𝓝 0))
    (hδnext_nonneg : ∀ j, 0 ≤ δnext j)
    (hholdPrefix_nonneg : ∀ j, 0 ≤ holdPrefix j)
    (p_hz_start : ∀ j,
      |(sol w).z (selectorMUWriteHoldTime j) haltCoordU -
        stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 1)) haltCoordU| ≤ Bz j)
    (p_hoff : ∀ j, selectorMUHaltEncConst (solMUReplStaticCfg w) j → ∀ t ∈
        Icc (selectorMUInterReadStart j)
        (selectorMUNextWriteStart j),
      |(sol w).z t haltCoordU - (sol w).z (selectorMUInterReadStart j) haltCoordU| ≤
        selectorReplicatorHoldEnvelope j)
    (p_hnextWrite : ∀ j, ∀ t ∈ Icc (selectorMUNextWriteStart j)
        (selectorMUNextRead j),
      |(sol w).z t haltCoordU -
        stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 2)) haltCoordU| ≤ δnext j)
    (p_hfiniteHold : ∀ j, ∀ t ∈ Icc (selectorMUInterReadStart j)
        (selectorMUNextRead j),
      |(sol w).z t haltCoordU -
        (sol w).z (selectorMUInterReadStart j) haltCoordU| ≤ holdPrefix j) :
    MUReplicatorLateStartHaltFactsAt sol w := by
  classical
  haveI : Nonempty UniversalLocalView := ⟨defaultLocalViewU⟩
  let gap : ℝ := selectorReplicatorGapVal eta heta
  let R0 : ℝ := Fintype.card UniversalLocalView
  let epsLam : ℕ → ℝ := epsLamShiftedFullAt sol w gap R0
  let Λ : ℕ → ℝ := fun j => selectorSettledWriteIntLower j
  let Bz_read : ℕ → ℝ :=
    solMUReplSettledRho Λ Bz
      (fun j => (Fintype.card UniversalLocalView : ℝ) * epsLam j)
  have hgap0 : 0 < gap := by
    simpa [gap] using solMURepl_static_hgap0 eta heta herr
  have hR0_nonneg : 0 ≤ R0 := by
    dsimp [R0]
    positivity
  have hsum_forward := solMURepl_lam_sum_forward_P (sol := sol) boxInputs
  have hlam_forward := solMURepl_lam_nonneg_forward_P (sol := sol) boxInputs
  have hqL_select :
      ∀ j, ∀ t ∈ Icc (selectorMUSelectStartTime j)
          (selectorMUWriteReadTime j),
        1 / (Fintype.card UniversalLocalView : ℝ) ≤
          (sol w).lam (localViewU (solMUReplStaticCfg w j)) t := by
    intro j
    have hgap_floor :
        ∀ v : UniversalLocalView, v ≠ localViewU (solMUReplStaticCfg w j) →
          ∀ t ∈ Ico (selectorMUSelectStartTime j) (selectorMUWriteReadTime j),
            universalPval eta heta v ((sol w).u t) -
              universalPval eta heta (localViewU (solMUReplStaticCfg w j)) ((sol w).u t) ≤ 0 := by
      intro v hv t ht
      have hgap_full :=
        selector_replicator_hgap_of_utube
          (sol := fun _ : ℕ => sol w)
          (cfg := fun _ j => solMUReplStaticCfg w j)
          herr
          (fun _ j t ht => hutube_win j t ht)
      have hnonpos : -(gap) ≤ 0 := by
        exact neg_nonpos.mpr hgap0.le
      exact le_trans
        (by
          have ht_full : t ∈ Ico (selectorMUWriteStartTime j)
              (selectorMUWriteReadTime j) :=
            ⟨le_trans (selectorMUWriteStart_le_selectStart j) ht.1, ht.2⟩
          simpa [gap] using hgap_full 0 j v hv t ht_full)
        hnonpos
    have hbar :=
      replicator_winner_floor_on_interval_param
        (sol := sol w) (localViewU (solMUReplStaticCfg w j))
        (a := selectorMUSelectStartTime j) (b := selectorMUWriteReadTime j)
        (selectorMUSelectStart_le_read j)
        (1 / (Fintype.card UniversalLocalView : ℝ)) (le_refl _)
        (fun t ht => solMURepl_static_hdom_nonneg t
          (le_trans (selectorMUSelectStart_nonneg j) ht.1))
        (fun t _ht => boxInputs.hcr_nonneg t)
        (fun t _ht =>
          mul_nonneg
            (pow_nonneg (by nlinarith [Real.neg_one_le_sin t]) _)
            (mul_nonneg hg₀.le (Real.exp_pos _).le))
        hgap_floor
        (fun t ht => hsum_forward w t
          (le_trans (selectorMUSelectStart_nonneg j) ht.1))
        (fun v t ht => hlam_forward w v t
          (le_trans (selectorMUSelectStart_nonneg j) ht.1))
        (hselect_start j)
    exact hbar
  have hRa_select :
      ∀ j, ∀ v : UniversalLocalView, v ≠ localViewU (solMUReplStaticCfg w j) →
        (sol w).lam v (selectorMUSelectStartTime j) /
            (sol w).lam (localViewU (solMUReplStaticCfg w j))
              (selectorMUSelectStartTime j) ≤ R0 := by
    intro j
    have hsum := hsum_forward w (selectorMUSelectStartTime j)
      (selectorMUSelectStart_nonneg j)
    have hnonneg : ∀ v : UniversalLocalView,
        0 ≤ (sol w).lam v (selectorMUSelectStartTime j) :=
      fun v => hlam_forward w v (selectorMUSelectStartTime j)
        (selectorMUSelectStart_nonneg j)
    simpa [R0] using
      lam_ratio_card_bound_at
        (lam := fun v : UniversalLocalView => (sol w).lam v (selectorMUSelectStartTime j))
        (vstar := localViewU (solMUReplStaticCfg w j))
        hsum hnonneg (hselect_start j)
  have hloser :
      ∀ j, ∀ t ∈ Icc (selectorMUWriteHoldTime j)
          (selectorMUWriteReadTime j),
        (Finset.univ.filter (fun v : UniversalLocalView =>
          v ≠ localViewU (solMUReplStaticCfg w j))).sum (fun v => (sol w).lam v t) ≤
            epsLam j := by
    intro j
    have hgap_cond :
        ∀ v : UniversalLocalView, v ≠ localViewU (solMUReplStaticCfg w j) →
          ∀ t ∈ Ico (selectorMUSelectStartTime j) (selectorMUWriteReadTime j),
            universalPval eta heta v ((sol w).u t) -
              universalPval eta heta (localViewU (solMUReplStaticCfg w j))
                ((sol w).u t) ≤ -gap := by
      intro v hv t ht
      have hgap_full :=
        selector_replicator_hgap_of_utube
          (sol := fun _ : ℕ => sol w)
          (cfg := fun _ j => solMUReplStaticCfg w j)
          herr
          (fun _ j t ht => hutube_win j t ht)
      have ht_full : t ∈ Ico (selectorMUWriteStartTime j)
          (selectorMUWriteReadTime j) :=
        ⟨le_trans (selectorMUWriteStart_le_selectStart j) ht.1, ht.2⟩
      simpa [gap] using hgap_full 0 j v hv t ht_full
    have hloser_j := hloser_of_shifted_concentration
      (sol := sol) (cfg := fun j => solMUReplStaticCfg w j)
      w j (gap := gap) (R0 := R0)
      hgap0 hR0_nonneg hκ₀_nonneg hscale
      (fun t ht => solMURepl_static_hdom_nonneg t
        (le_trans (selectorMUSelectStart_nonneg j) ht.1))
      (hqL_select j)
      (fun v t ht => hlam_forward w v t
        (le_trans (selectorMUSelectStart_nonneg j) ht.1))
      (fun t ht => hsum_forward w t
        (le_trans (selectorMUSelectStart_nonneg j) ht.1))
      hgap_cond
      (hRa_select j)
    simpa [epsLam] using hloser_j
  have hepsLam_tendsto : Tendsto epsLam atTop (𝓝 0) := by
    simpa [epsLam, gap, R0] using
      epsLamShiftedFull_tendsto_zero sol w hg₀ hgap0 hR0_nonneg hκ₀_nonneg hscale
  have hepsLam_nonneg : ∀ j, 0 ≤ epsLam j := by
    intro j
    simpa [epsLam, gap, R0] using
      epsLamShiftedFullAt_nonneg sol w hgap0 hR0_nonneg hκ₀_nonneg j
  have hstart_gen :
      (∀ (j : ℕ),
        |(sol w).z (selectorMUWriteReadTime j) haltCoordU -
          stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 1)) haltCoordU| ≤
            Bz_read j) ∧
      Tendsto Bz_read atTop (𝓝 0) ∧
      (∀ j, 0 ≤ Bz_read j) := by
    have hraw :=
      solMURepl_settled_hstart_gen
        (w := w)
        (hcfg_step := fun j => solMUReplStaticCfg_step w j)
        (epsLam := epsLam) (Λ := Λ) (Bz := Bz) (Bzmax := Bzmax)
        (hdom_write := fun j t ht => solMURepl_static_hdom_write w j t ht)
        (hgZ_cont := solMURepl_static_hgZ_cont sol w)
        (hgZ0 := fun j t ht => solMURepl_static_hgZ0 sol w j t ht)
        (hsum := fun j t ht => hsum_forward w t
          (le_trans
            (le_trans (selectorMUWriteStartTime_nonneg j) (selectorMUWriteStart_le_hold j))
            ht.1))
        (hlam_nonneg := fun j t ht v => hlam_forward w v t
          (le_trans
            (le_trans (selectorMUWriteStartTime_nonneg j) (selectorMUWriteStart_le_hold j))
            ht.1))
        (hloser := hloser)
        (hz_start := p_hz_start)
        (hΛ_lower := by
          intro j
          have hdom_nonneg := solMURepl_static_hdom_nonneg
          have hgZ_cont := solMURepl_static_hgZ_cont sol w
          have hgZ0 := solMURepl_static_hgZ0 sol
          have hsub := selector_settled_writeIntegral_lower_lbd_repl (sol w) j
            hdom_nonneg hgZ_cont
          have hcont_int : ∀ a b : ℝ,
              IntervalIntegrable
                (fun t : ℝ => bgpParams38.A * (sol w).α t *
                  bGateZ bgpParams38.L ((sol w).μ t) t)
                MeasureTheory.volume a b :=
            fun a b => hgZ_cont.intervalIntegrable a b
          have hadd := intervalIntegral.integral_add_adjacent_intervals
            (hcont_int (selectorMUWriteHoldTime j) (selectorMUSettledWriteSubEnd j))
            (hcont_int (selectorMUSettledWriteSubEnd j) (selectorMUWriteReadTime j))
          have htail_nonneg :
              0 ≤ ∫ t in selectorMUSettledWriteSubEnd j..selectorMUWriteReadTime j,
                  bgpParams38.A * (sol w).α t *
                    bGateZ bgpParams38.L ((sol w).μ t) t := by
            apply intervalIntegral.integral_nonneg (selectorMUSettledSubEnd_le_read j)
            intro t ht
            exact hgZ0 w j t
              ⟨le_trans (selectorMUWriteHold_le_settledSubEnd j) ht.1, ht.2⟩
          linarith)
        (hΛ := selectorSettledWriteIntLower_tendsto_atTop)
        (hBz_nonneg := hBz_nonneg)
        (hBz_bdd := hBz_bdd)
        (hepsLam_nonneg := hepsLam_nonneg)
        (hepsLam_tendsto := hepsLam_tendsto)
    simpa [Bz_read, Λ] using hraw
  exact
  { cfg := fun j => solMUReplStaticCfg w j
    hcfg := fun j => solMUReplStaticCfg_eq w j
    Bz_read := Bz_read
    hz_read_start := by
      intro j
      simpa [Bz_read, selectorMUInterReadStart, selectorMUWriteReadTime]
        using hstart_gen.1 j
    hBz_read_tendsto := hstart_gen.2.1
    hBz_read_nonneg := hstart_gen.2.2
    δnext := δnext
    holdPrefix := holdPrefix
    hδnext := hδnext
    hδnext_nonneg := hδnext_nonneg
    hholdPrefix_nonneg := hholdPrefix_nonneg
    hoff := p_hoff
    hnextWrite := p_hnextWrite
    hfiniteHold := p_hfiniteHold }

private theorem solMURepl_settled_hstart_gen_P
    {p : DynGateParams}
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamilyP p eta heta Mcy κ₀ g₀}
    (w : ℕ) (hA_nonneg : 0 ≤ p.A)
    (epsLam Λ Bz : ℕ → ℝ) (Bzmax : ℝ)
    (hsum : ∀ j, ∀ t ∈ Icc (selectorMUWriteHoldTime j)
        (selectorMUWriteReadTime j),
      (∑ v : UniversalLocalView, (sol w).lam v t) = 1)
    (hlam_nonneg : ∀ j, ∀ t ∈ Icc (selectorMUWriteHoldTime j)
        (selectorMUWriteReadTime j), ∀ v : UniversalLocalView,
      0 ≤ (sol w).lam v t)
    (hloser : ∀ j, ∀ t ∈ Icc (selectorMUWriteHoldTime j)
        (selectorMUWriteReadTime j),
      (Finset.univ.filter (fun v : UniversalLocalView =>
        v ≠ localViewU (solMUReplStaticCfg w j))).sum
          (fun v => (sol w).lam v t) ≤ epsLam j)
    (hz_start : ∀ j,
      |(sol w).z (selectorMUWriteHoldTime j) haltCoordU -
        stackMachineEncodingU.enc
          (solMUReplStaticCfg w (j + 1)) haltCoordU| ≤ Bz j)
    (hΛ_lower : ∀ j,
      Λ j ≤ ∫ τ in selectorMUWriteHoldTime j..selectorMUWriteReadTime j,
        p.A * (sol w).α τ * bGateZ p.L ((sol w).μ τ) τ)
    (hΛ : Tendsto Λ atTop atTop)
    (hBz_nonneg : ∀ j, 0 ≤ Bz j)
    (hBz_bdd : ∀ᶠ j in atTop, Bz j ≤ Bzmax)
    (hepsLam_nonneg : ∀ j, 0 ≤ epsLam j)
    (hepsLam_tendsto : Tendsto epsLam atTop (𝓝 0)) :
    let delta : ℕ → ℝ :=
      fun j => (Fintype.card UniversalLocalView : ℝ) * epsLam j
    (∀ j,
      |(sol w).z (selectorMUWriteReadTime j) haltCoordU -
        stackMachineEncodingU.enc
          (solMUReplStaticCfg w (j + 1)) haltCoordU| ≤
        selectorZWriteContraction Λ Bz j + delta j) ∧
    Tendsto (fun j => selectorZWriteContraction Λ Bz j + delta j)
      atTop (𝓝 0) ∧
    (∀ j, 0 ≤ selectorZWriteContraction Λ Bz j + delta j) := by
  intro delta
  have hδ_tendsto : Tendsto delta atTop (𝓝 0) := by
    simpa [delta] using
      hepsLam_tendsto.const_mul
        (Fintype.card UniversalLocalView : ℝ)
  have hctr : Tendsto (selectorZWriteContraction Λ Bz) atTop (𝓝 0) := by
    simpa using
      solMURepl_expNegLambda_Bz0_tendsto_zero
        (Λ := fun _ : ℕ => Λ) (Bz0 := fun _ : ℕ => Bz) (w := 0)
        hΛ (Eventually.of_forall hBz_nonneg) hBz_bdd
  have hgZ_cont : Continuous fun t : ℝ =>
      p.A * (sol w).α t * bGateZ p.L ((sol w).μ t) t :=
    selector_replicator_gateZ_integrand_continuous (sol w)
  refine ⟨?_, ?_, ?_⟩
  · intro j
    have hmix : ∀ t ∈ Icc (selectorMUWriteHoldTime j)
        (selectorMUWriteReadTime j),
        |selectorMixTarget branchU (sol w).u (sol w).lam t haltCoordU -
          stackMachineEncodingU.enc
            (solMUReplStaticCfg w (j + 1)) haltCoordU| ≤ delta j := by
      intro t ht
      have hwrong : ∀ v : UniversalLocalView,
          v ≠ localViewU (solMUReplStaticCfg w j) →
          (sol w).lam v t ≤ epsLam j :=
        fun v hv => le_trans
          (Finset.single_le_sum
            (fun u _ => hlam_nonneg j t ht u) (by simp [hv]))
          (hloser j t ht)
      have hraw :=
        selectorMixTarget_halt_to_next_of_concentration
          (sol w).u (sol w).lam t (solMUReplStaticCfg w j)
          (hepsLam_nonneg j) (hsum j t ht)
          (fun v => hlam_nonneg j t ht v) hwrong
      simpa [delta, solMUReplStaticCfg_step w j] using hraw
    have hgZ0 : ∀ t ∈ Icc (selectorMUWriteHoldTime j)
        (selectorMUWriteReadTime j),
        0 ≤ p.A * (sol w).α t * bGateZ p.L ((sol w).μ t) t := by
      intro t ht
      have ht0 : 0 ≤ t := le_trans
        (le_trans (selectorMUWriteStartTime_nonneg j)
          (selectorMUWriteStart_le_hold j)) ht.1
      exact
        selector_replicator_gateZ_integrand_nonneg
          (sol w) selectorSchedule_domain_of_nonneg_structural
          hA_nonneg ht0
    have hzero : ∀ t ∈ Icc (selectorMUWriteReadTime j)
        (selectorMUWriteReadTime j),
        |(sol w).z t haltCoordU -
          (sol w).z (selectorMUWriteReadTime j) haltCoordU| ≤ (0 : ℝ) := by
      intro t ht
      have ht_eq : t = selectorMUWriteReadTime j :=
        le_antisymm ht.2 ht.1
      simp [ht_eq]
    have hz_after :=
      z_after_write_bound_repl
        (sol w) haltCoordU
        (selectorMUWriteHold_le_read j)
        (fun t ht => solMURepl_static_hdom_write w j t ht)
        hgZ_cont hgZ0 hmix hzero
    have hz_raw :=
      hz_after (selectorMUWriteReadTime j) ⟨le_rfl, le_rfl⟩
    have hbound :=
      exp_neg_mul_abs_le_exp_neg_lbd_mul
        (hΛ_lower j) (hz_start j)
    dsimp [selectorZWriteContraction]
    linarith
  · simpa using hctr.add hδ_tendsto
  · intro j
    exact add_nonneg
      (mul_nonneg (Real.exp_pos _).le (hBz_nonneg j))
      (mul_nonneg (Nat.cast_nonneg _) (hepsLam_nonneg j))

/-- Parameter-generic shifted late-start constructor from an analytic package. -/
def muReplicatorLateStartHaltFactsAt_shifted_of_selectStart_P
    {p : DynGateParams}
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamilyP p eta heta Mcy κ₀ g₀)
    (w : ℕ)
    (analytic : MUReplicatorSettledAnalyticP sol w)
    (hA_nonneg : 0 ≤ p.A)
    (boxInputs : MUReplicatorBoxInputsP p eta heta Mcy κ₀ g₀ sol)
    (Bz : ℕ → ℝ) (Bzmax : ℝ)
    (δnext holdPrefix : ℕ → ℝ)
    (hBz_nonneg : ∀ j, 0 ≤ Bz j)
    (hBz_bdd : ∀ᶠ j in atTop, Bz j ≤ Bzmax)
    (hδnext : Tendsto δnext atTop (𝓝 0))
    (hδnext_nonneg : ∀ j, 0 ≤ δnext j)
    (hholdPrefix_nonneg : ∀ j, 0 ≤ holdPrefix j)
    (p_hz_start : ∀ j,
      |(sol w).z (selectorMUWriteHoldTime j) haltCoordU -
        stackMachineEncodingU.enc
          (solMUReplStaticCfg w (j + 1)) haltCoordU| ≤ Bz j)
    (p_hoff : ∀ j, selectorMUHaltEncConst (solMUReplStaticCfg w) j →
      ∀ t ∈ Icc (selectorMUInterReadStart j)
          (selectorMUNextWriteStart j),
        |(sol w).z t haltCoordU -
          (sol w).z (selectorMUInterReadStart j) haltCoordU| ≤
            selectorReplicatorHoldEnvelope j)
    (p_hnextWrite : ∀ j, ∀ t ∈ Icc (selectorMUNextWriteStart j)
        (selectorMUNextRead j),
      |(sol w).z t haltCoordU -
        stackMachineEncodingU.enc
          (solMUReplStaticCfg w (j + 2)) haltCoordU| ≤ δnext j)
    (p_hfiniteHold : ∀ j, ∀ t ∈ Icc (selectorMUInterReadStart j)
        (selectorMUNextRead j),
      |(sol w).z t haltCoordU -
        (sol w).z (selectorMUInterReadStart j) haltCoordU| ≤ holdPrefix j) :
    MUReplicatorLateStartHaltFactsAt sol w := by
  classical
  let Bz_read : ℕ → ℝ :=
    solMUReplSettledRho analytic.Λ Bz
      (fun j =>
        (Fintype.card UniversalLocalView : ℝ) * analytic.epsLam j)
  have hsum_forward :=
    solMURepl_lam_sum_forward_P (sol := sol) boxInputs
  have hlam_forward :=
    solMURepl_lam_nonneg_forward_P (sol := sol) boxInputs
  have hstart_gen :=
    solMURepl_settled_hstart_gen_P
      w hA_nonneg analytic.epsLam analytic.Λ Bz Bzmax
      (fun j t ht => hsum_forward w t
        (le_trans
          (le_trans (selectorMUWriteStartTime_nonneg j)
            (selectorMUWriteStart_le_hold j)) ht.1))
      (fun j t ht v => hlam_forward w v t
        (le_trans
          (le_trans (selectorMUWriteStartTime_nonneg j)
            (selectorMUWriteStart_le_hold j)) ht.1))
      analytic.hloser p_hz_start analytic.hΛ_lower
      analytic.hΛ_tendsto hBz_nonneg hBz_bdd
      analytic.hεLam_nonneg analytic.hεLam_tendsto
  exact
  { cfg := fun j => solMUReplStaticCfg w j
    hcfg := fun j => solMUReplStaticCfg_eq w j
    Bz_read := Bz_read
    hz_read_start := by
      intro j
      simpa [Bz_read, selectorMUInterReadStart,
        selectorMUWriteReadTime] using hstart_gen.1 j
    hBz_read_tendsto := hstart_gen.2.1
    hBz_read_nonneg := hstart_gen.2.2
    δnext := δnext
    holdPrefix := holdPrefix
    hδnext := hδnext
    hδnext_nonneg := hδnext_nonneg
    hholdPrefix_nonneg := hholdPrefix_nonneg
    hoff := p_hoff
    hnextWrite := p_hnextWrite
    hfiniteHold := p_hfiniteHold }

/-- Shifted diagonal late-start constructor from the recovered select-start floor.

The caller supplies recovery at `selectorMUSelectStartTime`; this constructor
uses the barrier to propagate the winner floor, applies shifted concentration,
then feeds the abstract settled z-write theorem. -/
def muReplicatorLateStartHaltFactsAt_shifted_of_selectStart
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀)
    (w : ℕ)
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (herr : (gateSelectorAtomsCoordN (universalGateAtoms eta heta)).errSel < 1 / 2)
    (hκ₀_nonneg : 0 ≤ (κ₀ : ℝ))
    (hg₀ : 0 < (g₀ : ℝ))
    (hscale : (κ₀ : ℝ) ≤ ((3 / 4 : ℝ) ^ Mcy) * (g₀ : ℝ))
    (hselect_start : ∀ j,
      1 / (Fintype.card UniversalLocalView : ℝ) ≤
        (sol w).lam (localViewU (solMUReplStaticCfg w j))
          (selectorMUSelectStartTime j))
    (hutube_win : ∀ j, ∀ t ∈ Set.Ico (selectorMUWriteStartTime j)
        (selectorMUWriteReadTime j),
      UTube r_LE_U (solMUReplStaticCfg w j) ((sol w).u t))
    (Bz : ℕ → ℝ) (Bzmax : ℝ)
    (δnext : ℕ → ℝ) (holdPrefix : ℕ → ℝ)
    (hBz_nonneg : ∀ j, 0 ≤ Bz j)
    (hBz_bdd : ∀ᶠ j in atTop, Bz j ≤ Bzmax)
    (hδnext : Tendsto δnext atTop (𝓝 0))
    (hδnext_nonneg : ∀ j, 0 ≤ δnext j)
    (hholdPrefix_nonneg : ∀ j, 0 ≤ holdPrefix j)
    (p_hz_start : ∀ j,
      |(sol w).z (selectorMUWriteHoldTime j) haltCoordU -
        stackMachineEncodingU.enc
          (solMUReplStaticCfg w (j + 1)) haltCoordU| ≤ Bz j)
    (p_hoff : ∀ j, selectorMUHaltEncConst (solMUReplStaticCfg w) j →
      ∀ t ∈ Icc (selectorMUInterReadStart j)
          (selectorMUNextWriteStart j),
        |(sol w).z t haltCoordU -
          (sol w).z (selectorMUInterReadStart j) haltCoordU| ≤
            selectorReplicatorHoldEnvelope j)
    (p_hnextWrite : ∀ j, ∀ t ∈ Icc (selectorMUNextWriteStart j)
        (selectorMUNextRead j),
      |(sol w).z t haltCoordU -
        stackMachineEncodingU.enc
          (solMUReplStaticCfg w (j + 2)) haltCoordU| ≤ δnext j)
    (p_hfiniteHold : ∀ j, ∀ t ∈ Icc (selectorMUInterReadStart j)
        (selectorMUNextRead j),
      |(sol w).z t haltCoordU -
        (sol w).z (selectorMUInterReadStart j) haltCoordU| ≤ holdPrefix j) :
    MUReplicatorLateStartHaltFactsAt sol w := by
  let analytic :=
    muReplicatorSettledAnalytic38_of_selectStart
      sol w boxInputs herr hκ₀_nonneg hg₀ hscale
      hselect_start hutube_win
  exact
    muReplicatorLateStartHaltFactsAt_shifted_of_selectStart_P
      sol w analytic (by norm_num [bgpParams38]) boxInputs
      Bz Bzmax δnext holdPrefix hBz_nonneg hBz_bdd
      hδnext hδnext_nonneg hholdPrefix_nonneg
      p_hz_start p_hoff p_hnextWrite p_hfiniteHold

/-- Shifted diagonal late-start constructor with recovery wired internally.

The recovery-rate hypotheses are the local numerical inputs required by
`replicator_winner_recovery_at_selectStart` on each write-to-select window.
All simplex/domain inputs and the weak readout gap are discharged from the
MU replicator solution, `boxInputs`, and the supplied write-window U-tube. -/
private def muReplicatorLateStartHaltFactsAt_shifted_38_impl
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀)
    (w : ℕ)
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
    (hutube_win : ∀ j, ∀ t ∈ Set.Ico (selectorMUWriteStartTime j)
        (selectorMUWriteReadTime j),
      UTube r_LE_U (solMUReplStaticCfg w j) ((sol w).u t))
    (Bz : ℕ → ℝ) (Bzmax : ℝ)
    (δnext : ℕ → ℝ) (holdPrefix : ℕ → ℝ)
    (hBz_nonneg : ∀ j, 0 ≤ Bz j)
    (hBz_bdd : ∀ᶠ j in atTop, Bz j ≤ Bzmax)
    (hδnext : Tendsto δnext atTop (𝓝 0))
    (hδnext_nonneg : ∀ j, 0 ≤ δnext j)
    (hholdPrefix_nonneg : ∀ j, 0 ≤ holdPrefix j)
    (p_hz_start : ∀ j,
      |(sol w).z (selectorMUWriteHoldTime j) haltCoordU -
        stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 1)) haltCoordU| ≤ Bz j)
    (p_hoff : ∀ j, selectorMUHaltEncConst (solMUReplStaticCfg w) j → ∀ t ∈
        Icc (selectorMUInterReadStart j)
        (selectorMUNextWriteStart j),
      |(sol w).z t haltCoordU - (sol w).z (selectorMUInterReadStart j) haltCoordU| ≤
        selectorReplicatorHoldEnvelope j)
    (p_hnextWrite : ∀ j, ∀ t ∈ Icc (selectorMUNextWriteStart j)
        (selectorMUNextRead j),
      |(sol w).z t haltCoordU -
        stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 2)) haltCoordU| ≤ δnext j)
    (p_hfiniteHold : ∀ j, ∀ t ∈ Icc (selectorMUInterReadStart j)
        (selectorMUNextRead j),
      |(sol w).z t haltCoordU -
        (sol w).z (selectorMUInterReadStart j) haltCoordU| ≤ holdPrefix j) :
    MUReplicatorLateStartHaltFactsAt sol w := by
  classical
  haveI : Nonempty UniversalLocalView := ⟨defaultLocalViewU⟩
  let gap : ℝ := selectorReplicatorGapVal eta heta
  have hgap0 : 0 < gap := by
    simpa [gap] using solMURepl_static_hgap0 eta heta herr
  have hsum_forward := solMURepl_lam_sum_forward_P (sol := sol) boxInputs
  have hlam_forward := solMURepl_lam_nonneg_forward_P (sol := sol) boxInputs
  have hselect_start :
      ∀ j,
        1 / (Fintype.card UniversalLocalView : ℝ) ≤
          (sol w).lam (localViewU (solMUReplStaticCfg w j))
            (selectorMUSelectStartTime j) := by
    intro j
    have hgap_floor :
        ∀ v : UniversalLocalView, v ≠ localViewU (solMUReplStaticCfg w j) →
          ∀ u ∈ Ico (selectorMUWriteStartTime j) (selectorMUSelectStartTime j),
            universalPval eta heta v ((sol w).u u) -
              universalPval eta heta (localViewU (solMUReplStaticCfg w j)) ((sol w).u u) ≤
                0 := by
      intro v hv u hu
      have hgap_full :=
        selector_replicator_hgap_of_utube
          (sol := fun _ : ℕ => sol w)
          (cfg := fun _ j => solMUReplStaticCfg w j)
          herr
          (fun _ j t ht => hutube_win j t ht)
      have hu_full : u ∈ Ico (selectorMUWriteStartTime j)
          (selectorMUWriteReadTime j) :=
        ⟨hu.1, lt_of_lt_of_le hu.2 (selectorMUSelectStart_le_read j)⟩
      have hnonpos : -(gap) ≤ 0 := neg_nonpos.mpr hgap0.le
      exact le_trans (by simpa [gap] using hgap_full 0 j v hv u hu_full) hnonpos
    have havg_gap :
        ∀ u ∈ Ico (selectorMUWriteStartTime j) (selectorMUSelectStartTime j),
          recoveryGap j *
              (1 - (sol w).lam (localViewU (solMUReplStaticCfg w j)) u) ≤
            universalPval eta heta (localViewU (solMUReplStaticCfg w j)) ((sol w).u u) -
              ∑ v : UniversalLocalView,
                (sol w).lam v u * universalPval eta heta v ((sol w).u u) := by
      intro u hu
      have hu_full : u ∈ Ico (selectorMUWriteStartTime j)
          (selectorMUWriteReadTime j) :=
        ⟨hu.1, lt_of_lt_of_le hu.2 (selectorMUSelectStart_le_read j)⟩
      exact
        selector_replicator_havg_gap_of_utube
          (eta := eta) (heta := heta)
          (lam := fun v : UniversalLocalView => (sol w).lam v u)
          (u := (sol w).u u)
          (c := solMUReplStaticCfg w j)
          (gap := recoveryGap j)
          herr
          (hutube_win j u hu_full)
          (hrecoveryGap_le_gapVal j)
          (hsum_forward w u (le_trans (selectorMUWriteStartTime_nonneg j) hu.1))
          (fun v => hlam_forward w v u
            (le_trans (selectorMUWriteStartTime_nonneg j) hu.1))
    exact
      replicator_winner_recovery_at_selectStart
        (sol := sol w)
        (vstar := localViewU (solMUReplStaticCfg w j))
        (j := j)
        (crMin := crMin j)
        (crMax := crMax j)
        (cgMin := cgMin j)
        (gap := recoveryGap j)
        (b := recoveryB j)
        hN2
        (hcrMin_pos j)
        (hcrMin_le_crMax j)
        (hcgMin_nonneg j)
        (hrecoveryGap_nonneg j)
        (hrecoveryB_eq j)
        (hrecoveryB_pos j)
        (hrecoveryBDelta j)
        (hpow j)
        (fun u hu => solMURepl_static_hdom_nonneg u
          (le_trans (selectorMUWriteStartTime_nonneg j) hu.1))
        (hcr_bounds j)
        (hcg_min j)
        hgap_floor
        havg_gap
        (fun u hu => hsum_forward w u
          (le_trans (selectorMUWriteStartTime_nonneg j) hu.1))
        (fun v u hu => hlam_forward w v u
          (le_trans (selectorMUWriteStartTime_nonneg j) hu.1))
  exact
    muReplicatorLateStartHaltFactsAt_shifted_of_selectStart
      sol w boxInputs herr hκ₀_nonneg hg₀ hscale hselect_start hutube_win
      Bz Bzmax δnext holdPrefix hBz_nonneg hBz_bdd hδnext hδnext_nonneg
      hholdPrefix_nonneg p_hz_start p_hoff p_hnextWrite p_hfiniteHold

private theorem muReplicator_selectStart_floor_P
    {p : DynGateParams}
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamilyP p eta heta Mcy κ₀ g₀)
    (w : ℕ)
    (boxInputs : MUReplicatorBoxInputsP p eta heta Mcy κ₀ g₀ sol)
    (herr :
      (gateSelectorAtomsCoordN (universalGateAtoms eta heta)).errSel < 1 / 2)
    (crMin crMax cgMin recoveryGap recoveryB : ℕ → ℝ)
    (recoveryK : ℕ → ℕ)
    (hN2 : 2 ≤ Fintype.card UniversalLocalView)
    (hcrMin_pos : ∀ j, 0 < crMin j)
    (hcrMin_le_crMax : ∀ j, crMin j ≤ crMax j)
    (hcgMin_nonneg : ∀ j, 0 ≤ cgMin j)
    (hrecoveryGap_nonneg : ∀ j, 0 ≤ recoveryGap j)
    (hrecoveryGap_le_gapVal :
      ∀ j, recoveryGap j ≤ selectorReplicatorGapVal eta heta)
    (hrecoveryB_eq :
      ∀ j, recoveryB j = cgMin j * recoveryGap j / 2 - crMax j)
    (hrecoveryB_pos : ∀ j, 0 < recoveryB j)
    (hrecoveryBDelta :
      ∀ j, (recoveryK j : ℝ) ≤
        recoveryB j * selectorMURecoveryDelta)
    (hpow : ∀ j,
      1 + recoveryB j / crMin j ≤ (2 : ℝ) ^ recoveryK j)
    (hcr_bounds : ∀ j,
      ∀ u ∈ Icc (selectorMUWriteStartTime j)
          (selectorMUSelectStartTime j),
        crMin j ≤ ((1 + Real.cos u) / 2) ^ Mcy * (κ₀ : ℝ) ∧
          ((1 + Real.cos u) / 2) ^ Mcy * (κ₀ : ℝ) ≤ crMax j)
    (hcg_min : ∀ j,
      ∀ u ∈ Icc (selectorMUWriteStartTime j)
          (selectorMUSelectStartTime j),
        cgMin j ≤ ((1 + Real.sin u) / 2) ^ Mcy *
          ((g₀ : ℝ) * Real.exp (p.cα * u)))
    (hutube_win : ∀ j, ∀ t ∈ Set.Ico (selectorMUWriteStartTime j)
        (selectorMUWriteReadTime j),
      UTube r_LE_U (solMUReplStaticCfg w j) ((sol w).u t)) :
    ∀ j,
      1 / (Fintype.card UniversalLocalView : ℝ) ≤
        (sol w).lam (localViewU (solMUReplStaticCfg w j))
          (selectorMUSelectStartTime j) := by
  classical
  haveI : Nonempty UniversalLocalView := ⟨defaultLocalViewU⟩
  let gap : ℝ := selectorReplicatorGapVal eta heta
  have hgap0 : 0 < gap := by
    simpa [gap] using solMURepl_static_hgap0 eta heta herr
  have hsum_forward :=
    solMURepl_lam_sum_forward_P (sol := sol) boxInputs
  have hlam_forward :=
    solMURepl_lam_nonneg_forward_P (sol := sol) boxInputs
  intro j
  have hgap_floor :
      ∀ v : UniversalLocalView,
        v ≠ localViewU (solMUReplStaticCfg w j) →
      ∀ u ∈ Ico (selectorMUWriteStartTime j)
          (selectorMUSelectStartTime j),
        universalPval eta heta v ((sol w).u u) -
          universalPval eta heta
            (localViewU (solMUReplStaticCfg w j)) ((sol w).u u) ≤ 0 := by
    intro v hv u hu
    have hu_full : u ∈ Ico (selectorMUWriteStartTime j)
        (selectorMUWriteReadTime j) :=
      ⟨hu.1, lt_of_lt_of_le hu.2 (selectorMUSelectStart_le_read j)⟩
    have hmargins :=
      universal_selector_margins_of_tube
        (eta := eta) (heta := heta)
        (c := solMUReplStaticCfg w j) (Z := (sol w).u u)
        (hutube_win j u hu_full) herr
    have hwinner :
        1 / 2 -
            (gateSelectorAtomsCoordN
              (universalGateAtoms eta heta)).errSel ≤
          universalPval eta heta
            (localViewU (solMUReplStaticCfg w j)) ((sol w).u u) := by
      simpa [universalPval] using hmargins.1
    have hloser :
        universalPval eta heta v ((sol w).u u) ≤
          -(1 / 2 -
            (gateSelectorAtomsCoordN
              (universalGateAtoms eta heta)).errSel) := by
      simpa [universalPval] using hmargins.2 v hv
    linarith
  have havg_gap :
      ∀ u ∈ Ico (selectorMUWriteStartTime j)
          (selectorMUSelectStartTime j),
        recoveryGap j *
            (1 - (sol w).lam
              (localViewU (solMUReplStaticCfg w j)) u) ≤
          universalPval eta heta
              (localViewU (solMUReplStaticCfg w j)) ((sol w).u u) -
            ∑ v : UniversalLocalView,
              (sol w).lam v u *
                universalPval eta heta v ((sol w).u u) := by
    intro u hu
    have hu_full : u ∈ Ico (selectorMUWriteStartTime j)
        (selectorMUWriteReadTime j) :=
      ⟨hu.1, lt_of_lt_of_le hu.2 (selectorMUSelectStart_le_read j)⟩
    exact
      selector_replicator_havg_gap_of_utube
        (eta := eta) (heta := heta)
        (lam := fun v : UniversalLocalView => (sol w).lam v u)
        (u := (sol w).u u) (c := solMUReplStaticCfg w j)
        (gap := recoveryGap j) herr (hutube_win j u hu_full)
        (hrecoveryGap_le_gapVal j)
        (hsum_forward w u
          (le_trans (selectorMUWriteStartTime_nonneg j) hu.1))
        (fun v => hlam_forward w v u
          (le_trans (selectorMUWriteStartTime_nonneg j) hu.1))
  exact
    replicator_winner_recovery_at_selectStart
      (sol := sol w)
      (vstar := localViewU (solMUReplStaticCfg w j))
      (j := j) (crMin := crMin j) (crMax := crMax j)
      (cgMin := cgMin j) (gap := recoveryGap j)
      (b := recoveryB j) hN2
      (hcrMin_pos j) (hcrMin_le_crMax j)
      (hcgMin_nonneg j) (hrecoveryGap_nonneg j)
      (hrecoveryB_eq j) (hrecoveryB_pos j)
      (hrecoveryBDelta j) (hpow j)
      (fun u hu => solMURepl_static_hdom_nonneg u
        (le_trans (selectorMUWriteStartTime_nonneg j) hu.1))
      (hcr_bounds j) (hcg_min j) hgap_floor havg_gap
      (fun u hu => hsum_forward w u
        (le_trans (selectorMUWriteStartTime_nonneg j) hu.1))
      (fun v u hu => hlam_forward w v u
        (le_trans (selectorMUWriteStartTime_nonneg j) hu.1))

/-- Parameter-generic shifted late-start constructor with recovery internal. -/
def muReplicatorLateStartHaltFactsAt_shifted_P
    {p : DynGateParams}
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamilyP p eta heta Mcy κ₀ g₀)
    (w : ℕ)
    (analytic : MUReplicatorSettledAnalyticP sol w)
    (hA_nonneg : 0 ≤ p.A)
    (boxInputs : MUReplicatorBoxInputsP p eta heta Mcy κ₀ g₀ sol)
    (herr :
      (gateSelectorAtomsCoordN (universalGateAtoms eta heta)).errSel < 1 / 2)
    (crMin crMax cgMin recoveryGap recoveryB : ℕ → ℝ)
    (recoveryK : ℕ → ℕ)
    (hN2 : 2 ≤ Fintype.card UniversalLocalView)
    (hcrMin_pos : ∀ j, 0 < crMin j)
    (hcrMin_le_crMax : ∀ j, crMin j ≤ crMax j)
    (hcgMin_nonneg : ∀ j, 0 ≤ cgMin j)
    (hrecoveryGap_nonneg : ∀ j, 0 ≤ recoveryGap j)
    (hrecoveryGap_le_gapVal :
      ∀ j, recoveryGap j ≤ selectorReplicatorGapVal eta heta)
    (hrecoveryB_eq :
      ∀ j, recoveryB j = cgMin j * recoveryGap j / 2 - crMax j)
    (hrecoveryB_pos : ∀ j, 0 < recoveryB j)
    (hrecoveryBDelta :
      ∀ j, (recoveryK j : ℝ) ≤
        recoveryB j * selectorMURecoveryDelta)
    (hpow : ∀ j,
      1 + recoveryB j / crMin j ≤ (2 : ℝ) ^ recoveryK j)
    (hcr_bounds : ∀ j,
      ∀ u ∈ Icc (selectorMUWriteStartTime j)
          (selectorMUSelectStartTime j),
        crMin j ≤ ((1 + Real.cos u) / 2) ^ Mcy * (κ₀ : ℝ) ∧
          ((1 + Real.cos u) / 2) ^ Mcy * (κ₀ : ℝ) ≤ crMax j)
    (hcg_min : ∀ j,
      ∀ u ∈ Icc (selectorMUWriteStartTime j)
          (selectorMUSelectStartTime j),
        cgMin j ≤ ((1 + Real.sin u) / 2) ^ Mcy *
          ((g₀ : ℝ) * Real.exp (p.cα * u)))
    (hutube_win : ∀ j, ∀ t ∈ Set.Ico (selectorMUWriteStartTime j)
        (selectorMUWriteReadTime j),
      UTube r_LE_U (solMUReplStaticCfg w j) ((sol w).u t))
    (Bz : ℕ → ℝ) (Bzmax : ℝ)
    (δnext holdPrefix : ℕ → ℝ)
    (hBz_nonneg : ∀ j, 0 ≤ Bz j)
    (hBz_bdd : ∀ᶠ j in atTop, Bz j ≤ Bzmax)
    (hδnext : Tendsto δnext atTop (𝓝 0))
    (hδnext_nonneg : ∀ j, 0 ≤ δnext j)
    (hholdPrefix_nonneg : ∀ j, 0 ≤ holdPrefix j)
    (p_hz_start : ∀ j,
      |(sol w).z (selectorMUWriteHoldTime j) haltCoordU -
        stackMachineEncodingU.enc
          (solMUReplStaticCfg w (j + 1)) haltCoordU| ≤ Bz j)
    (p_hoff : ∀ j, selectorMUHaltEncConst (solMUReplStaticCfg w) j →
      ∀ t ∈ Icc (selectorMUInterReadStart j)
          (selectorMUNextWriteStart j),
        |(sol w).z t haltCoordU -
          (sol w).z (selectorMUInterReadStart j) haltCoordU| ≤
            selectorReplicatorHoldEnvelope j)
    (p_hnextWrite : ∀ j, ∀ t ∈ Icc (selectorMUNextWriteStart j)
        (selectorMUNextRead j),
      |(sol w).z t haltCoordU -
        stackMachineEncodingU.enc
          (solMUReplStaticCfg w (j + 2)) haltCoordU| ≤ δnext j)
    (p_hfiniteHold : ∀ j, ∀ t ∈ Icc (selectorMUInterReadStart j)
        (selectorMUNextRead j),
      |(sol w).z t haltCoordU -
        (sol w).z (selectorMUInterReadStart j) haltCoordU| ≤ holdPrefix j) :
    MUReplicatorLateStartHaltFactsAt sol w := by
  have hselect_start :=
    muReplicator_selectStart_floor_P
      sol w boxInputs herr crMin crMax cgMin recoveryGap recoveryB
      recoveryK hN2 hcrMin_pos hcrMin_le_crMax hcgMin_nonneg
      hrecoveryGap_nonneg hrecoveryGap_le_gapVal hrecoveryB_eq
      hrecoveryB_pos hrecoveryBDelta hpow hcr_bounds hcg_min hutube_win
  exact
    muReplicatorLateStartHaltFactsAt_shifted_of_selectStart_P
      sol w analytic hA_nonneg boxInputs
      Bz Bzmax δnext holdPrefix hBz_nonneg hBz_bdd
      hδnext hδnext_nonneg hholdPrefix_nonneg
      p_hz_start p_hoff p_hnextWrite p_hfiniteHold

/-- Shifted diagonal late-start constructor with recovery wired internally.

The recovery-rate hypotheses are the local numerical inputs required by
`replicator_winner_recovery_at_selectStart` on each write-to-select window.
All simplex/domain inputs and the weak readout gap are discharged from the
MU replicator solution, `boxInputs`, and the supplied write-window U-tube. -/
def muReplicatorLateStartHaltFactsAt_shifted
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀)
    (w : ℕ)
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
    (hutube_win : ∀ j, ∀ t ∈ Set.Ico (selectorMUWriteStartTime j)
        (selectorMUWriteReadTime j),
      UTube r_LE_U (solMUReplStaticCfg w j) ((sol w).u t))
    (Bz : ℕ → ℝ) (Bzmax : ℝ)
    (δnext : ℕ → ℝ) (holdPrefix : ℕ → ℝ)
    (hBz_nonneg : ∀ j, 0 ≤ Bz j)
    (hBz_bdd : ∀ᶠ j in atTop, Bz j ≤ Bzmax)
    (hδnext : Tendsto δnext atTop (𝓝 0))
    (hδnext_nonneg : ∀ j, 0 ≤ δnext j)
    (hholdPrefix_nonneg : ∀ j, 0 ≤ holdPrefix j)
    (p_hz_start : ∀ j,
      |(sol w).z (selectorMUWriteHoldTime j) haltCoordU -
        stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 1)) haltCoordU| ≤ Bz j)
    (p_hoff : ∀ j, selectorMUHaltEncConst (solMUReplStaticCfg w) j → ∀ t ∈
        Icc (selectorMUInterReadStart j)
        (selectorMUNextWriteStart j),
      |(sol w).z t haltCoordU - (sol w).z (selectorMUInterReadStart j) haltCoordU| ≤
        selectorReplicatorHoldEnvelope j)
    (p_hnextWrite : ∀ j, ∀ t ∈ Icc (selectorMUNextWriteStart j)
        (selectorMUNextRead j),
      |(sol w).z t haltCoordU -
        stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 2)) haltCoordU| ≤ δnext j)
    (p_hfiniteHold : ∀ j, ∀ t ∈ Icc (selectorMUInterReadStart j)
        (selectorMUNextRead j),
      |(sol w).z t haltCoordU -
        (sol w).z (selectorMUInterReadStart j) haltCoordU| ≤ holdPrefix j) :
    MUReplicatorLateStartHaltFactsAt sol w := by
  have hselect_start :=
    muReplicator_selectStart_floor_P
      sol w boxInputs herr crMin crMax cgMin recoveryGap recoveryB
      recoveryK hN2 hcrMin_pos hcrMin_le_crMax hcgMin_nonneg
      hrecoveryGap_nonneg hrecoveryGap_le_gapVal hrecoveryB_eq
      hrecoveryB_pos hrecoveryBDelta hpow hcr_bounds hcg_min hutube_win
  let analytic :=
    muReplicatorSettledAnalytic38_of_selectStart
      sol w boxInputs herr hκ₀_nonneg hg₀ hscale
      hselect_start hutube_win
  exact
    muReplicatorLateStartHaltFactsAt_shifted_P
      sol w analytic (by norm_num [bgpParams38]) boxInputs herr
      crMin crMax cgMin recoveryGap recoveryB recoveryK
      hN2 hcrMin_pos hcrMin_le_crMax hcgMin_nonneg
      hrecoveryGap_nonneg hrecoveryGap_le_gapVal hrecoveryB_eq
      hrecoveryB_pos hrecoveryBDelta hpow hcr_bounds hcg_min
      hutube_win Bz Bzmax δnext holdPrefix
      hBz_nonneg hBz_bdd hδnext hδnext_nonneg hholdPrefix_nonneg
      p_hz_start p_hoff p_hnextWrite p_hfiniteHold

section PGeneralizationSentinels

variable {p : DynGateParams}

example : @solMURepl_lam_sum_forward_P p =
    @solMURepl_lam_sum_forward_P p := by
  rfl

example : @solMURepl_lam_nonneg_forward_P p =
    @solMURepl_lam_nonneg_forward_P p := by
  rfl

example : @MUReplicatorSettledAnalyticP p =
    @MUReplicatorSettledAnalyticP p := by
  rfl

example : @MUReplicatorShiftedConcentrationAtP p =
    @MUReplicatorShiftedConcentrationAtP p := by
  rfl

example : @muReplicatorShiftedConcentrationAt_of_selectStart_P p =
    @muReplicatorShiftedConcentrationAt_of_selectStart_P p := by
  rfl

example : @muReplicatorLateStartHaltFactsAt_shifted_of_selectStart_P p =
    @muReplicatorLateStartHaltFactsAt_shifted_of_selectStart_P p := by
  rfl

example : @muReplicator_selectStart_floor_P p =
    @muReplicator_selectStart_floor_P p := by
  rfl

example : @muReplicatorLateStartHaltFactsAt_shifted_P p =
    @muReplicatorLateStartHaltFactsAt_shifted_P p := by
  rfl

end PGeneralizationSentinels

set_option maxHeartbeats 1600000 in
-- Large endgame replay, matching `bgp_headline_warmGain_euclidean_at`.
/-- Warm-gain Euclidean headline from diagonal late-start facts. -/
theorem bgp_headline_warmGain_euclidean_at_late_start
    (eta : ℚ) (heta : 0 < eta)
    (M : ℕ) (κ₀ : ℚ) (warmGainQ : ℕ → ℚ)
    (HP : MvPolynomial (Fin d_U) ℚ) (Kq : ℚ) (R : ℕ)
    (hfin : ∀ wg w,
      Ripple.FiniteHorizonBound
        (selectorMUReplicatorField eta heta M κ₀ (warmGainQ wg) HP Kq R)
        (selectorMUReplicatorInit selectorInitX0 w (warmGainQ wg)))
    (hgateZ : ∀ wg w,
      ∀ y : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        y 0 = selectorMUReplicatorInit selectorInitX0 w (warmGainQ wg) →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y
            (selectorMUReplicatorField eta heta M κ₀ (warmGainQ wg) HP Kq R (y t)) t) →
        ∀ t : ℝ, 0 ≤ t →
          y t (selOfContract UniversalLocalView (contractGateZ d_U)) =
            bGateZ 1 (y t (selOfContract UniversalLocalView (contractMu d_U))) t)
    (hgateU : ∀ wg w,
      ∀ y : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        y 0 = selectorMUReplicatorInit selectorInitX0 w (warmGainQ wg) →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y
            (selectorMUReplicatorField eta heta M κ₀ (warmGainQ wg) HP Kq R (y t)) t) →
        ∀ t : ℝ, 0 ≤ t →
          y t (selOfContract UniversalLocalView (contractGateU d_U)) =
            bGateU 1 (y t (selOfContract UniversalLocalView (contractMu d_U))) t)
    (h_chiReset : ∀ wg w,
      ∀ y : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        y 0 = selectorMUReplicatorInit selectorInitX0 w (warmGainQ wg) →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y
            (selectorMUReplicatorField eta heta M κ₀ (warmGainQ wg) HP Kq R (y t)) t) →
        ∀ t : ℝ, 0 ≤ t →
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t)
            (selChiResetPoly d_U UniversalLocalView M) =
              ((1 + Real.cos t) / 2) ^ M)
    (h_chiGate : ∀ wg w,
      ∀ y : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        y 0 = selectorMUReplicatorInit selectorInitX0 w (warmGainQ wg) →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y
            (selectorMUReplicatorField eta heta M κ₀ (warmGainQ wg) HP Kq R (y t)) t) →
        ∀ t : ℝ, 0 ≤ t →
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t)
            (selChiGatePoly d_U UniversalLocalView M) =
              ((1 + Real.sin t) / 2) ^ M)
    (h_kappa : ∀ wg w,
      ∀ y : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        y 0 = selectorMUReplicatorInit selectorInitX0 w (warmGainQ wg) →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y
            (selectorMUReplicatorField eta heta M κ₀ (warmGainQ wg) HP Kq R (y t)) t) →
        ∀ t : ℝ, 0 ≤ t →
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t)
            (selKappaPoly d_U UniversalLocalView κ₀) = (κ₀ : ℝ))
    (h_gain : ∀ wg w,
      ∀ y : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        y 0 = selectorMUReplicatorInit selectorInitX0 w (warmGainQ wg) →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y
            (selectorMUReplicatorField eta heta M κ₀ (warmGainQ wg) HP Kq R (y t)) t) →
        ∀ t : ℝ, 0 ≤ t →
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t)
            (selGainPoly d_U UniversalLocalView) =
              ((warmGainQ wg : ℚ) : ℝ) * Real.exp (bgpParams38.cα * t))
    (h_P : ∀ wg w,
      ∀ y : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        y 0 = selectorMUReplicatorInit selectorInitX0 w (warmGainQ wg) →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y
            (selectorMUReplicatorField eta heta M κ₀ (warmGainQ wg) HP Kq R (y t)) t) →
        ∀ (v : UniversalLocalView) (t : ℝ), 0 ≤ t →
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t)
            ((muReadoutPoly eta heta) v) =
              universalPval eta heta v (fun i => y t (selU UniversalLocalView i)))
    (boxInputs : ∀ wg, MUReplicatorBoxInputs eta heta M κ₀ (warmGainQ wg)
      (solMUReplWarm eta heta M κ₀ warmGainQ HP Kq R hfin hgateZ hgateU
        h_chiReset h_chiGate h_kappa h_gain h_P wg))
    (late : ∀ wg, MUReplicatorLateStartHaltFactsAt
      (solMUReplWarm eta heta M κ₀ warmGainQ HP Kq R hfin hgateZ hgateU
        h_chiReset h_chiGate h_kappa h_gain h_P wg) wg) :
    ∀ w : ℕ,
      ∃ (sol : MUReplicatorSolW eta heta M κ₀ warmGainQ w)
        (_La : SelectorReplicatorHaltLatchSol sol (fun _ : (Fin d_U → ℝ) => (0 : ℝ)) 0 R),
        (undecidableMachine.toDiscreteMachine.haltsOn w →
          ∃ T : ℝ, ∀ t ≥ T, 3 / 4 ≤ sol.z t haltCoordU ∧ sol.z t haltCoordU ≤ 1) ∧
        (¬ undecidableMachine.toDiscreteMachine.haltsOn w →
          ∃ T : ℝ, ∀ t ≥ T, 0 ≤ sol.z t haltCoordU ∧ sol.z t haltCoordU ≤ 1 / 4) := by
  classical
  haveI : Nonempty UniversalLocalView := ⟨defaultLocalViewU⟩
  intro w
  let solFam : MUReplicatorSolFamily eta heta M κ₀ (warmGainQ w) :=
    solMUReplWarm eta heta M κ₀ warmGainQ HP Kq R hfin hgateZ hgateU
      h_chiReset h_chiGate h_kappa h_gain h_P w
  have hforward_boxes :
      (∀ t : ℝ, 0 ≤ t →
        selectorMixTarget branchU (solFam w).u (solFam w).lam t haltCoordU ∈ Icc (0 : ℝ) 1) ∧
      (∀ t : ℝ, 0 ≤ t → (solFam w).z t haltCoordU ≤ 1) ∧
      (∀ t : ℝ, 0 ≤ t → 0 ≤ (solFam w).z t haltCoordU) := by
    have boxW := boxInputs w
    have hode : ∀ v : UniversalLocalView, ∀ t : ℝ, 0 ≤ t →
        HasDerivAt ((solFam w).lam v)
          ((((1 + Real.cos t) / 2) ^ M * (κ₀ : ℝ)) *
              (1 / (Fintype.card UniversalLocalView : ℝ) - (solFam w).lam v t)
            + (((1 + Real.sin t) / 2) ^ M *
                (((warmGainQ w : ℚ) : ℝ) * Real.exp (bgpParams38.cα * t))) *
              (solFam w).lam v t *
                (universalPval eta heta v ((solFam w).u t)
                  - ∑ u : UniversalLocalView,
                      (solFam w).lam u t * universalPval eta heta u ((solFam w).u t))) t := by
      intro v t ht
      simpa [selectorSchedule] using
        (solFam w).lam_hasDeriv v t (by simpa [selectorSchedule] using ht)
    have hsum : ∀ t : ℝ, 0 ≤ t →
        (∑ v : UniversalLocalView, (solFam w).lam v t) = 1 :=
      replicator_sum_lam_eq_one
        (lam := fun v t => (solFam w).lam v t)
        (P := fun v t => universalPval eta heta v ((solFam w).u t))
        (cr := fun t => ((1 + Real.cos t) / 2) ^ M * (κ₀ : ℝ))
        (cg := fun t =>
          ((1 + Real.sin t) / 2) ^ M *
            (((warmGainQ w : ℚ) : ℝ) * Real.exp (bgpParams38.cα * t)))
        boxW.hcr_cont boxW.hcg_cont
        (fun v => (solFam w).cont_lam v)
        (boxW.hP_cont w) hode (boxW.hlam_sum0 w)
    have hlam_nonneg_forward :
        ∀ v : UniversalLocalView, ∀ t : ℝ, 0 ≤ t → 0 ≤ (solFam w).lam v t :=
      replicator_lam_nonneg
        (lam := fun v t => (solFam w).lam v t)
        (P := fun v t => universalPval eta heta v ((solFam w).u t))
        (cr := fun t => ((1 + Real.cos t) / 2) ^ M * (κ₀ : ℝ))
        (cg := fun t =>
          ((1 + Real.sin t) / 2) ^ M *
            (((warmGainQ w : ℚ) : ℝ) * Real.exp (bgpParams38.cα * t)))
        boxW.hcr_cont boxW.hcg_cont
        (fun v => (solFam w).cont_lam v)
        (boxW.hP_cont w) boxW.hcr_nonneg hode
        (boxW.hlam_init_nonneg w)
    have hmix : ∀ t : ℝ, 0 ≤ t →
        selectorMixTarget branchU (solFam w).u (solFam w).lam t haltCoordU ∈ Icc (0 : ℝ) 1 := by
      intro t ht
      exact selectorMixTarget_haltCoord_mem_Icc_of_lam_sum_eq_one
        (solFam w).u (solFam w).lam t
        (fun v => hlam_nonneg_forward v t ht)
        (hsum t ht)
    have hzbox :=
      selector_replicator_flag_box_on_nonneg_repl (solFam w)
        boxW.hcr_cont boxW.hcg_cont (boxW.hP_cont w)
        boxW.hcr_nonneg (boxW.hlam_sum0 w)
        (boxW.hlam_init_nonneg w) (boxW.hz0 w)
    exact ⟨hmix, hzbox.1, hzbox.2⟩
  have correct_halt_z :
      undecidableMachine.toDiscreteMachine.haltsOn w →
        ∃ T : ℝ, ∀ t ≥ T, 3 / 4 ≤ (solFam w).z t haltCoordU ∧
          (solFam w).z t haltCoordU ≤ 1 := by
    intro hw
    have hwU : M_U.haltsOn w := by
      simpa using hw
    have lateW := late w
    have hhold :=
      solMURepl_settled_hhold_of_halts (solFam w) w hwU lateW.cfg
        lateW.hcfg lateW.Bz_read lateW.δnext lateW.holdPrefix
        lateW.hBz_read_nonneg lateW.hδnext_nonneg lateW.hholdPrefix_nonneg
        lateW.hBz_read_tendsto lateW.hδnext
        lateW.hz_read_start lateW.hoff lateW.hnextWrite lateW.hfiniteHold
    obtain ⟨δhold, hhold_all, hδhold, hδhold_nonneg⟩ := hhold
    exact selector_correct_halt_endtoend_hold_repl_of_tendsto (solFam w) w hwU
      lateW.cfg lateW.hcfg lateW.Bz_read δhold
      lateW.hz_read_start hhold_all hforward_boxes.2.1
      lateW.hBz_read_tendsto hδhold lateW.hBz_read_nonneg hδhold_nonneg
  have correct_nonhalt_z :
      ¬ undecidableMachine.toDiscreteMachine.haltsOn w →
        ∃ T : ℝ, ∀ t ≥ T, 0 ≤ (solFam w).z t haltCoordU ∧
          (solFam w).z t haltCoordU ≤ 1 / 4 := by
    intro hw
    have hwU : ¬ M_U.haltsOn w := by
      simpa using hw
    have lateW := late w
    have hhold :=
      solMURepl_settled_hhold_of_nonhalts (solFam w) w hwU lateW.cfg
        lateW.hcfg lateW.Bz_read lateW.δnext
        lateW.hBz_read_nonneg lateW.hδnext_nonneg
        lateW.hBz_read_tendsto lateW.hδnext
        lateW.hz_read_start lateW.hoff lateW.hnextWrite
    exact selector_correct_nonhalt_endtoend_hold_repl_of_tendsto (solFam w) w hwU
      lateW.cfg lateW.hcfg lateW.Bz_read
      (selectorMUSelfHoldDelta lateW.δnext lateW.Bz_read)
      lateW.hz_read_start hhold.1 hforward_boxes.2.2
      lateW.hBz_read_tendsto hhold.2.1 lateW.hBz_read_nonneg hhold.2.2
  exact ⟨solFam w, selector_replicator_zero_latch_solution (solFam w) R,
    correct_halt_z, correct_nonhalt_z⟩

set_option maxHeartbeats 1800000 in
-- Threads the large Euclidean replay through the warm-gain compactification headline.
/-- Warm-gain PIVP headline from diagonal late-start facts. -/
theorem bgp_headline_warmGain_late_start
    (eta : ℚ) (heta : 0 < eta)
    (M : ℕ) (κ₀ : ℚ) (warmGainQ : ℕ → ℚ)
    (HP : MvPolynomial (Fin d_U) ℚ) (Kq : ℚ) (R : ℕ)
    (hfin : ∀ wg w,
      Ripple.FiniteHorizonBound
        (selectorMUReplicatorField eta heta M κ₀ (warmGainQ wg) HP Kq R)
        (selectorMUReplicatorInit selectorInitX0 w (warmGainQ wg)))
    (hgateZ : ∀ wg w,
      ∀ y : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        y 0 = selectorMUReplicatorInit selectorInitX0 w (warmGainQ wg) →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y
            (selectorMUReplicatorField eta heta M κ₀ (warmGainQ wg) HP Kq R (y t)) t) →
        ∀ t : ℝ, 0 ≤ t →
          y t (selOfContract UniversalLocalView (contractGateZ d_U)) =
            bGateZ 1 (y t (selOfContract UniversalLocalView (contractMu d_U))) t)
    (hgateU : ∀ wg w,
      ∀ y : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        y 0 = selectorMUReplicatorInit selectorInitX0 w (warmGainQ wg) →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y
            (selectorMUReplicatorField eta heta M κ₀ (warmGainQ wg) HP Kq R (y t)) t) →
        ∀ t : ℝ, 0 ≤ t →
          y t (selOfContract UniversalLocalView (contractGateU d_U)) =
            bGateU 1 (y t (selOfContract UniversalLocalView (contractMu d_U))) t)
    (h_chiReset : ∀ wg w,
      ∀ y : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        y 0 = selectorMUReplicatorInit selectorInitX0 w (warmGainQ wg) →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y
            (selectorMUReplicatorField eta heta M κ₀ (warmGainQ wg) HP Kq R (y t)) t) →
        ∀ t : ℝ, 0 ≤ t →
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t)
            (selChiResetPoly d_U UniversalLocalView M) =
              ((1 + Real.cos t) / 2) ^ M)
    (h_chiGate : ∀ wg w,
      ∀ y : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        y 0 = selectorMUReplicatorInit selectorInitX0 w (warmGainQ wg) →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y
            (selectorMUReplicatorField eta heta M κ₀ (warmGainQ wg) HP Kq R (y t)) t) →
        ∀ t : ℝ, 0 ≤ t →
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t)
            (selChiGatePoly d_U UniversalLocalView M) =
              ((1 + Real.sin t) / 2) ^ M)
    (h_kappa : ∀ wg w,
      ∀ y : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        y 0 = selectorMUReplicatorInit selectorInitX0 w (warmGainQ wg) →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y
            (selectorMUReplicatorField eta heta M κ₀ (warmGainQ wg) HP Kq R (y t)) t) →
        ∀ t : ℝ, 0 ≤ t →
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t)
            (selKappaPoly d_U UniversalLocalView κ₀) = (κ₀ : ℝ))
    (h_gain : ∀ wg w,
      ∀ y : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        y 0 = selectorMUReplicatorInit selectorInitX0 w (warmGainQ wg) →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y
            (selectorMUReplicatorField eta heta M κ₀ (warmGainQ wg) HP Kq R (y t)) t) →
        ∀ t : ℝ, 0 ≤ t →
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t)
            (selGainPoly d_U UniversalLocalView) =
              ((warmGainQ wg : ℚ) : ℝ) * Real.exp (bgpParams38.cα * t))
    (h_P : ∀ wg w,
      ∀ y : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        y 0 = selectorMUReplicatorInit selectorInitX0 w (warmGainQ wg) →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y
            (selectorMUReplicatorField eta heta M κ₀ (warmGainQ wg) HP Kq R (y t)) t) →
        ∀ (v : UniversalLocalView) (t : ℝ), 0 ≤ t →
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t)
            ((muReadoutPoly eta heta) v) =
              universalPval eta heta v (fun i => y t (selU UniversalLocalView i)))
    (init_presented :
      ∃ f : ℕ → Fin (selectorDim d_U UniversalLocalView + 1) → ℤ × ℕ,
        Computable f ∧
        ∀ w i, (f w i).2 ≠ 0 ∧
          selectorReplicatorSphereInitQ d_U UniversalLocalView selectorInitX0 w
            (warmGainQ w) i =
            (f w i).1 / ((f w i).2 : ℚ))
    (init_zero :
      ∀ (w : ℕ)
        (sol : MUReplicatorSolW eta heta M κ₀ warmGainQ w)
        (La : SelectorReplicatorHaltLatchSol sol (fun _ : (Fin d_U → ℝ) => (0 : ℝ)) 0 R),
          ((selectorReplicatorSphereInitQ d_U UniversalLocalView selectorInitX0 w
              (warmGainQ w) 0 : ℚ) : ℝ) =
            ((∑ i : Fin (selectorDim d_U UniversalLocalView),
                selectorReplicatorTupleTraj sol La ((warmGainQ w : ℚ) : ℝ) 0 i ^ 2) - 1) /
              ((∑ i : Fin (selectorDim d_U UniversalLocalView),
                selectorReplicatorTupleTraj sol La ((warmGainQ w : ℚ) : ℝ) 0 i ^ 2) + 1))
    (init_succ :
      ∀ (w : ℕ)
        (sol : MUReplicatorSolW eta heta M κ₀ warmGainQ w)
        (La : SelectorReplicatorHaltLatchSol sol (fun _ : (Fin d_U → ℝ) => (0 : ℝ)) 0 R)
        (i : Fin (selectorDim d_U UniversalLocalView)),
          ((selectorReplicatorSphereInitQ d_U UniversalLocalView selectorInitX0 w
              (warmGainQ w) i.succ : ℚ) : ℝ) =
            2 * selectorReplicatorTupleTraj sol La ((warmGainQ w : ℚ) : ℝ) 0 i /
              ((∑ k : Fin (selectorDim d_U UniversalLocalView),
                selectorReplicatorTupleTraj sol La ((warmGainQ w : ℚ) : ℝ) 0 k ^ 2) + 1))
    (boxInputs : ∀ wg, MUReplicatorBoxInputs eta heta M κ₀ (warmGainQ wg)
      (solMUReplWarm eta heta M κ₀ warmGainQ HP Kq R hfin hgateZ hgateU
        h_chiReset h_chiGate h_kappa h_gain h_P wg))
    (late : ∀ wg, MUReplicatorLateStartHaltFactsAt
      (solMUReplWarm eta heta M κ₀ warmGainQ HP Kq R hfin hgateZ hgateU
        h_chiReset h_chiGate h_kappa h_gain h_P wg) wg) :
    ∃ P : Ripple.BoundedUniversality.GPAC.PIVP ℚ,
      Nonempty (EventualThresholdSimulation P undecidableMachine) :=
  bgp_headline_warmGain eta heta M κ₀ warmGainQ R
    init_presented init_zero init_succ
    (bgp_headline_warmGain_euclidean_at_late_start eta heta M κ₀ warmGainQ
      HP Kq R hfin hgateZ hgateU h_chiReset h_chiGate h_kappa h_gain h_P
      boxInputs late)

/-- Warm-gain PIVP headline with recovery, shifted concentration, and late-start
facts assembled directly. -/
theorem bgp_headline_warmGain_shifted_recovery
    (eta : ℚ) (heta : 0 < eta)
    (M : ℕ) (κ₀ : ℚ) (warmGainQ : ℕ → ℚ)
    (HP : MvPolynomial (Fin d_U) ℚ) (Kq : ℚ) (R : ℕ)
    (hfin : ∀ wg w,
      Ripple.FiniteHorizonBound
        (selectorMUReplicatorField eta heta M κ₀ (warmGainQ wg) HP Kq R)
        (selectorMUReplicatorInit selectorInitX0 w (warmGainQ wg)))
    (hgateZ : ∀ wg w,
      ∀ y : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        y 0 = selectorMUReplicatorInit selectorInitX0 w (warmGainQ wg) →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y
            (selectorMUReplicatorField eta heta M κ₀ (warmGainQ wg) HP Kq R (y t)) t) →
        ∀ t : ℝ, 0 ≤ t →
          y t (selOfContract UniversalLocalView (contractGateZ d_U)) =
            bGateZ 1 (y t (selOfContract UniversalLocalView (contractMu d_U))) t)
    (hgateU : ∀ wg w,
      ∀ y : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        y 0 = selectorMUReplicatorInit selectorInitX0 w (warmGainQ wg) →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y
            (selectorMUReplicatorField eta heta M κ₀ (warmGainQ wg) HP Kq R (y t)) t) →
        ∀ t : ℝ, 0 ≤ t →
          y t (selOfContract UniversalLocalView (contractGateU d_U)) =
            bGateU 1 (y t (selOfContract UniversalLocalView (contractMu d_U))) t)
    (h_chiReset : ∀ wg w,
      ∀ y : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        y 0 = selectorMUReplicatorInit selectorInitX0 w (warmGainQ wg) →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y
            (selectorMUReplicatorField eta heta M κ₀ (warmGainQ wg) HP Kq R (y t)) t) →
        ∀ t : ℝ, 0 ≤ t →
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t)
            (selChiResetPoly d_U UniversalLocalView M) =
              ((1 + Real.cos t) / 2) ^ M)
    (h_chiGate : ∀ wg w,
      ∀ y : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        y 0 = selectorMUReplicatorInit selectorInitX0 w (warmGainQ wg) →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y
            (selectorMUReplicatorField eta heta M κ₀ (warmGainQ wg) HP Kq R (y t)) t) →
        ∀ t : ℝ, 0 ≤ t →
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t)
            (selChiGatePoly d_U UniversalLocalView M) =
              ((1 + Real.sin t) / 2) ^ M)
    (h_kappa : ∀ wg w,
      ∀ y : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        y 0 = selectorMUReplicatorInit selectorInitX0 w (warmGainQ wg) →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y
            (selectorMUReplicatorField eta heta M κ₀ (warmGainQ wg) HP Kq R (y t)) t) →
        ∀ t : ℝ, 0 ≤ t →
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t)
            (selKappaPoly d_U UniversalLocalView κ₀) = (κ₀ : ℝ))
    (h_gain : ∀ wg w,
      ∀ y : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        y 0 = selectorMUReplicatorInit selectorInitX0 w (warmGainQ wg) →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y
            (selectorMUReplicatorField eta heta M κ₀ (warmGainQ wg) HP Kq R (y t)) t) →
        ∀ t : ℝ, 0 ≤ t →
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t)
            (selGainPoly d_U UniversalLocalView) =
              ((warmGainQ wg : ℚ) : ℝ) * Real.exp (bgpParams38.cα * t))
    (h_P : ∀ wg w,
      ∀ y : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        y 0 = selectorMUReplicatorInit selectorInitX0 w (warmGainQ wg) →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y
            (selectorMUReplicatorField eta heta M κ₀ (warmGainQ wg) HP Kq R (y t)) t) →
        ∀ (v : UniversalLocalView) (t : ℝ), 0 ≤ t →
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t)
            ((muReadoutPoly eta heta) v) =
              universalPval eta heta v (fun i => y t (selU UniversalLocalView i)))
    (init_presented :
      ∃ f : ℕ → Fin (selectorDim d_U UniversalLocalView + 1) → ℤ × ℕ,
        Computable f ∧
        ∀ w i, (f w i).2 ≠ 0 ∧
          selectorReplicatorSphereInitQ d_U UniversalLocalView selectorInitX0 w
            (warmGainQ w) i =
            (f w i).1 / ((f w i).2 : ℚ))
    (init_zero :
      ∀ (w : ℕ)
        (sol : MUReplicatorSolW eta heta M κ₀ warmGainQ w)
        (La : SelectorReplicatorHaltLatchSol sol (fun _ : (Fin d_U → ℝ) => (0 : ℝ)) 0 R),
          ((selectorReplicatorSphereInitQ d_U UniversalLocalView selectorInitX0 w
              (warmGainQ w) 0 : ℚ) : ℝ) =
            ((∑ i : Fin (selectorDim d_U UniversalLocalView),
                selectorReplicatorTupleTraj sol La ((warmGainQ w : ℚ) : ℝ) 0 i ^ 2) - 1) /
              ((∑ i : Fin (selectorDim d_U UniversalLocalView),
                selectorReplicatorTupleTraj sol La ((warmGainQ w : ℚ) : ℝ) 0 i ^ 2) + 1))
    (init_succ :
      ∀ (w : ℕ)
        (sol : MUReplicatorSolW eta heta M κ₀ warmGainQ w)
        (La : SelectorReplicatorHaltLatchSol sol (fun _ : (Fin d_U → ℝ) => (0 : ℝ)) 0 R)
        (i : Fin (selectorDim d_U UniversalLocalView)),
          ((selectorReplicatorSphereInitQ d_U UniversalLocalView selectorInitX0 w
              (warmGainQ w) i.succ : ℚ) : ℝ) =
            2 * selectorReplicatorTupleTraj sol La ((warmGainQ w : ℚ) : ℝ) 0 i /
              ((∑ k : Fin (selectorDim d_U UniversalLocalView),
                selectorReplicatorTupleTraj sol La ((warmGainQ w : ℚ) : ℝ) 0 k ^ 2) + 1))
    (boxInputs : ∀ wg, MUReplicatorBoxInputs eta heta M κ₀ (warmGainQ wg)
      (solMUReplWarm eta heta M κ₀ warmGainQ HP Kq R hfin hgateZ hgateU
        h_chiReset h_chiGate h_kappa h_gain h_P wg))
    (herr : (gateSelectorAtomsCoordN (universalGateAtoms eta heta)).errSel < 1 / 2)
    (hκ₀_nonneg : 0 ≤ (κ₀ : ℝ))
    (hwarmGain_pos : ∀ wg, 0 < ((warmGainQ wg : ℚ) : ℝ))
    (hscale : ∀ wg, (κ₀ : ℝ) ≤ ((3 / 4 : ℝ) ^ M) * ((warmGainQ wg : ℚ) : ℝ))
    (crMin crMax cgMin recoveryGap recoveryB : ℕ → ℕ → ℝ)
    (recoveryK : ℕ → ℕ → ℕ)
    (hN2 : 2 ≤ Fintype.card UniversalLocalView)
    (hcrMin_pos : ∀ wg j, 0 < crMin wg j)
    (hcrMin_le_crMax : ∀ wg j, crMin wg j ≤ crMax wg j)
    (hcgMin_nonneg : ∀ wg j, 0 ≤ cgMin wg j)
    (hrecoveryGap_nonneg : ∀ wg j, 0 ≤ recoveryGap wg j)
    (hrecoveryGap_le_gapVal : ∀ wg j,
      recoveryGap wg j ≤ selectorReplicatorGapVal eta heta)
    (hrecoveryB_eq : ∀ wg j,
      recoveryB wg j = cgMin wg j * recoveryGap wg j / 2 - crMax wg j)
    (hrecoveryB_pos : ∀ wg j, 0 < recoveryB wg j)
    (hrecoveryBDelta : ∀ wg j, (recoveryK wg j : ℝ) ≤ recoveryB wg j * selectorMURecoveryDelta)
    (hpow : ∀ wg j, 1 + recoveryB wg j / crMin wg j ≤ (2 : ℝ) ^ recoveryK wg j)
    (hcr_bounds : ∀ wg j,
      ∀ u ∈ Icc (selectorMUWriteStartTime j) (selectorMUSelectStartTime j),
        crMin wg j ≤ ((1 + Real.cos u) / 2) ^ M * (κ₀ : ℝ) ∧
          ((1 + Real.cos u) / 2) ^ M * (κ₀ : ℝ) ≤ crMax wg j)
    (hcg_min : ∀ wg j,
      ∀ u ∈ Icc (selectorMUWriteStartTime j) (selectorMUSelectStartTime j),
        cgMin wg j ≤
          ((1 + Real.sin u) / 2) ^ M *
            (((warmGainQ wg : ℚ) : ℝ) * Real.exp (bgpParams38.cα * u)))
    (hutube_win : ∀ wg j, ∀ t ∈ Set.Ico (selectorMUWriteStartTime j)
        (selectorMUWriteReadTime j),
      UTube r_LE_U (solMUReplStaticCfg wg j)
        (((solMUReplWarm eta heta M κ₀ warmGainQ HP Kq R hfin hgateZ hgateU
          h_chiReset h_chiGate h_kappa h_gain h_P wg) wg).u t))
    (Bz : ℕ → ℕ → ℝ) (Bzmax : ℕ → ℝ)
    (δnext : ℕ → ℕ → ℝ) (holdPrefix : ℕ → ℕ → ℝ)
    (hBz_nonneg : ∀ wg j, 0 ≤ Bz wg j)
    (hBz_bdd : ∀ wg, ∀ᶠ j in atTop, Bz wg j ≤ Bzmax wg)
    (hδnext : ∀ wg, Tendsto (δnext wg) atTop (𝓝 0))
    (hδnext_nonneg : ∀ wg j, 0 ≤ δnext wg j)
    (hholdPrefix_nonneg : ∀ wg j, 0 ≤ holdPrefix wg j)
    (p_hz_start : ∀ wg j,
      |((solMUReplWarm eta heta M κ₀ warmGainQ HP Kq R hfin hgateZ hgateU
          h_chiReset h_chiGate h_kappa h_gain h_P wg) wg).z
          (selectorMUWriteHoldTime j) haltCoordU -
        stackMachineEncodingU.enc (solMUReplStaticCfg wg (j + 1)) haltCoordU| ≤ Bz wg j)
    (p_hoff : ∀ wg j, selectorMUHaltEncConst (solMUReplStaticCfg wg) j → ∀ t ∈
        Icc (selectorMUInterReadStart j)
        (selectorMUNextWriteStart j),
      |((solMUReplWarm eta heta M κ₀ warmGainQ HP Kq R hfin hgateZ hgateU
          h_chiReset h_chiGate h_kappa h_gain h_P wg) wg).z t haltCoordU -
        ((solMUReplWarm eta heta M κ₀ warmGainQ HP Kq R hfin hgateZ hgateU
          h_chiReset h_chiGate h_kappa h_gain h_P wg) wg).z
            (selectorMUInterReadStart j) haltCoordU| ≤ selectorReplicatorHoldEnvelope j)
    (p_hnextWrite : ∀ wg j, ∀ t ∈ Icc (selectorMUNextWriteStart j)
        (selectorMUNextRead j),
      |((solMUReplWarm eta heta M κ₀ warmGainQ HP Kq R hfin hgateZ hgateU
          h_chiReset h_chiGate h_kappa h_gain h_P wg) wg).z t haltCoordU -
        stackMachineEncodingU.enc (solMUReplStaticCfg wg (j + 2)) haltCoordU| ≤
          δnext wg j)
    (p_hfiniteHold : ∀ wg j, ∀ t ∈ Icc (selectorMUInterReadStart j)
        (selectorMUNextRead j),
      |((solMUReplWarm eta heta M κ₀ warmGainQ HP Kq R hfin hgateZ hgateU
          h_chiReset h_chiGate h_kappa h_gain h_P wg) wg).z t haltCoordU -
        ((solMUReplWarm eta heta M κ₀ warmGainQ HP Kq R hfin hgateZ hgateU
          h_chiReset h_chiGate h_kappa h_gain h_P wg) wg).z
            (selectorMUInterReadStart j) haltCoordU| ≤ holdPrefix wg j) :
    ∃ P : Ripple.BoundedUniversality.GPAC.PIVP ℚ,
      Nonempty (EventualThresholdSimulation P undecidableMachine) := by
  refine
    bgp_headline_warmGain_late_start eta heta M κ₀ warmGainQ HP Kq R
      hfin hgateZ hgateU h_chiReset h_chiGate h_kappa h_gain h_P
      init_presented init_zero init_succ boxInputs ?_
  intro wg
  exact
    muReplicatorLateStartHaltFactsAt_shifted
      (sol := solMUReplWarm eta heta M κ₀ warmGainQ HP Kq R hfin hgateZ hgateU
        h_chiReset h_chiGate h_kappa h_gain h_P wg)
      (w := wg)
      (boxInputs := boxInputs wg)
      herr hκ₀_nonneg (hwarmGain_pos wg) (hscale wg)
      (crMin wg) (crMax wg) (cgMin wg) (recoveryGap wg) (recoveryB wg) (recoveryK wg)
      hN2 (hcrMin_pos wg) (hcrMin_le_crMax wg) (hcgMin_nonneg wg)
      (hrecoveryGap_nonneg wg) (hrecoveryGap_le_gapVal wg)
      (hrecoveryB_eq wg) (hrecoveryB_pos wg)
      (hrecoveryBDelta wg) (hpow wg) (hcr_bounds wg) (hcg_min wg)
      (hutube_win wg) (Bz wg) (Bzmax wg)
      (δnext wg) (holdPrefix wg) (hBz_nonneg wg) (hBz_bdd wg)
      (hδnext wg) (hδnext_nonneg wg) (hholdPrefix_nonneg wg)
      (p_hz_start wg) (p_hoff wg) (p_hnextWrite wg) (p_hfiniteHold wg)

end Ripple.BoundedUniversality.BGP
