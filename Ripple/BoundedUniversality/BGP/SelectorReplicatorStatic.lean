import Ripple.BoundedUniversality.BGP.SelectorReplicatorSettledFinal
import Ripple.BoundedUniversality.BGP.BGPParams38

/-!
Ripple.BoundedUniversality.BGP.SelectorReplicatorStatic
------------------------------------
Static producers for the settled-window `M_U` replicator facts.

This file deliberately stops at the P3/P4 boundary.  It proves the pieces that
come from definitions, selector numeric sharpness, schedule algebra, and the
simplex/structural invariants.  The margin lower bound, reusable `Lmin` floor,
`u`-tube, and `ρu → 0` remain outside this file.
-/

noncomputable section

namespace Ripple.BoundedUniversality.BGP

open Set MachineInstance
open Filter
open scoped BigOperators Topology

/-- Canonical configuration stream used by the `M_U` replicator settled facts. -/
def solMUReplStaticCfg (w j : ℕ) : UConf :=
  M_U.step^[j] (M_U.init w)

theorem solMUReplStaticCfg_eq (w j : ℕ) :
    solMUReplStaticCfg w j = M_U.step^[j] (M_U.init w) := by
  rfl

theorem solMUReplStaticCfg_step (w j : ℕ) :
    M_U.step (solMUReplStaticCfg w j) = solMUReplStaticCfg w (j + 1) := by
  simp [solMUReplStaticCfg, Function.iterate_succ_apply']

/-- Static positivity of the concrete selector gap from the numeric selector
sharpness input `errSel < 1/2`. -/
theorem solMURepl_static_hgap0
    (eta : ℚ) (heta : 0 < eta)
    (herr : (gateSelectorAtomsCoordN (universalGateAtoms eta heta)).errSel < 1 / 2) :
    0 < selectorReplicatorGapVal eta heta :=
  selectorReplicatorGapVal_pos eta heta herr

/-- The settled file uses the fixed static `R0 = 1` skeleton.  P4 must prove
that the actual winner/loser ratios fit this skeleton when assembling
`SelectorReplicatorConcInputs`. -/
def solMUReplStaticR0 (_w _j : ℕ) : ℝ :=
  1

theorem solMURepl_static_hR0_nonneg :
    ∀ w : ℕ, ∀ᶠ j in atTop, 0 ≤ solMUReplStaticR0 w j := by
  intro w
  filter_upwards [] with j
  simp [solMUReplStaticR0]

theorem solMURepl_static_hR0_bound :
    ∀ w : ℕ, ∀ᶠ j in atTop, solMUReplStaticR0 w j ≤ 1 := by
  intro w
  filter_upwards [] with j
  simp [solMUReplStaticR0]

/-- Static choice of the prefix reset coefficient.  The equality is
definitionally true for this skeleton. -/
def solMUReplStaticKreset
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    {cfg : ℕ → ℕ → UConf}
    (inputs : SelectorReplicatorConcInputs sol cfg) (w j : ℕ) : ℝ :=
  solMUReplPreForwardResetIntegral inputs w j

theorem solMURepl_static_hKreset_eq
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    {cfg : ℕ → ℕ → UConf}
    (inputs : SelectorReplicatorConcInputs sol cfg) :
    ∀ w j, solMUReplStaticKreset inputs w j =
      solMUReplPreForwardResetIntegral inputs w j := by
  intro w j
  rfl

theorem solMURepl_static_hCratio_nonneg : 0 ≤ (1 : ℝ) := by
  norm_num

theorem solMURepl_static_hkappa_nonneg {κ₀ : ℚ}
    (hκ₀ : 0 ≤ (κ₀ : ℝ)) :
    0 ≤ (κ₀ : ℝ) :=
  hκ₀

theorem solMURepl_static_hg0 {g₀ : ℚ}
    (hg₀ : 0 < (g₀ : ℝ)) :
    0 < (g₀ : ℝ) :=
  hg₀

/-- Schedule-only reset/gate ratio on the prefix select window.

The one remaining input is numeric and static: the reset scale must fit under
the gate scale at the left edge of the select window. -/
theorem solMURepl_static_hratio_bound
    {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (hκ₀_nonneg : 0 ≤ (κ₀ : ℝ))
    (hg₀_nonneg : 0 ≤ (g₀ : ℝ))
    (hscale : (κ₀ : ℝ) ≤ ((3 / 4 : ℝ) ^ Mcy) * (g₀ : ℝ)) :
    ∀ (w : ℕ) j, ∀ t ∈
      Icc (selectorMUWriteStartTime j) (selectorMUWriteHoldTime j),
        (((1 + Real.cos t) / 2) ^ Mcy * (κ₀ : ℝ)) ≤
          ((1 : ℝ) * Real.exp (-(bgpParams38.cα * selectorMUWriteStartTime j))) *
            (((1 + Real.sin t) / 2) ^ Mcy *
              ((g₀ : ℝ) * Real.exp (bgpParams38.cα * t))) := by
  intro w j t ht
  have hcos_nonneg : 0 ≤ (1 + Real.cos t) / 2 := by
    nlinarith [Real.neg_one_le_cos t]
  have hcos_le_one : (1 + Real.cos t) / 2 ≤ 1 := by
    nlinarith [Real.cos_le_one t]
  have hcos_pow_le : ((1 + Real.cos t) / 2) ^ Mcy ≤ 1 := by
    simpa using pow_le_one₀ hcos_nonneg hcos_le_one
  have hlhs :
      (((1 + Real.cos t) / 2) ^ Mcy * (κ₀ : ℝ)) ≤ (κ₀ : ℝ) := by
    simpa using mul_le_mul_of_nonneg_right hcos_pow_le hκ₀_nonneg
  have hsin_half : (1 : ℝ) / 2 ≤ Real.sin t := by
    exact sin_ge_half_of_gate_window j (by
      simpa [selectorMUWriteStartTime, selectorMUWriteHoldTime] using ht)
  have hsin_base : (3 / 4 : ℝ) ≤ (1 + Real.sin t) / 2 := by
    linarith
  have hsin_pow :
      ((3 / 4 : ℝ) ^ Mcy) ≤ ((1 + Real.sin t) / 2) ^ Mcy := by
    exact pow_le_pow_left₀ (by norm_num) hsin_base Mcy
  have hgate_scale :
      ((3 / 4 : ℝ) ^ Mcy) * (g₀ : ℝ) ≤
        ((1 + Real.sin t) / 2) ^ Mcy * (g₀ : ℝ) := by
    exact mul_le_mul_of_nonneg_right hsin_pow hg₀_nonneg
  have ht_ge_start : selectorMUWriteStartTime j ≤ t := ht.1
  have hclock_nonneg :
      0 ≤ bgpParams38.cα * (t - selectorMUWriteStartTime j) := by
    have hcα : 0 ≤ bgpParams38.cα := by norm_num [bgpParams38]
    exact mul_nonneg hcα (sub_nonneg.mpr ht_ge_start)
  have hexp_one :
      1 ≤ Real.exp (bgpParams38.cα * (t - selectorMUWriteStartTime j)) := by
    simpa using Real.one_le_exp_iff.mpr hclock_nonneg
  have hgate_nonneg :
      0 ≤ ((1 + Real.sin t) / 2) ^ Mcy * (g₀ : ℝ) :=
    mul_nonneg (pow_nonneg (le_trans (by norm_num : (0 : ℝ) ≤ 3 / 4) hsin_base) Mcy)
      hg₀_nonneg
  have hclock_mul :
      ((1 + Real.sin t) / 2) ^ Mcy * (g₀ : ℝ) ≤
        ((1 + Real.sin t) / 2) ^ Mcy * (g₀ : ℝ) *
          Real.exp (bgpParams38.cα * (t - selectorMUWriteStartTime j)) := by
    simpa [mul_assoc] using mul_le_mul_of_nonneg_left hexp_one hgate_nonneg
  calc
    (((1 + Real.cos t) / 2) ^ Mcy * (κ₀ : ℝ)) ≤ (κ₀ : ℝ) := hlhs
    _ ≤ ((3 / 4 : ℝ) ^ Mcy) * (g₀ : ℝ) := hscale
    _ ≤ ((1 + Real.sin t) / 2) ^ Mcy * (g₀ : ℝ) := hgate_scale
    _ ≤ ((1 + Real.sin t) / 2) ^ Mcy * (g₀ : ℝ) *
          Real.exp (bgpParams38.cα * (t - selectorMUWriteStartTime j)) := hclock_mul
    _ =
        ((1 : ℝ) * Real.exp (-(bgpParams38.cα * selectorMUWriteStartTime j))) *
          (((1 + Real.sin t) / 2) ^ Mcy *
            ((g₀ : ℝ) * Real.exp (bgpParams38.cα * t))) := by
          rw [show bgpParams38.cα * (t - selectorMUWriteStartTime j) =
              bgpParams38.cα * t + -(bgpParams38.cα * selectorMUWriteStartTime j) by ring,
            Real.exp_add]
          ring

theorem solMURepl_static_hratio_bound_full
    {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (hκ₀_nonneg : 0 ≤ (κ₀ : ℝ))
    (hg₀_nonneg : 0 ≤ (g₀ : ℝ))
    (hscale : (κ₀ : ℝ) ≤ ((3 / 4 : ℝ) ^ Mcy) * (g₀ : ℝ)) :
    ∀ (w : ℕ) j, ∀ t ∈
      Icc (selectorMUWriteStartTime j) (selectorMUWriteReadTime j),
        (((1 + Real.cos t) / 2) ^ Mcy * (κ₀ : ℝ)) ≤
          ((1 : ℝ) * Real.exp (-(bgpParams38.cα * selectorMUWriteStartTime j))) *
            (((1 + Real.sin t) / 2) ^ Mcy *
              ((g₀ : ℝ) * Real.exp (bgpParams38.cα * t))) := by
  intro w j t ht
  have hcos_nonneg : 0 ≤ (1 + Real.cos t) / 2 := by
    nlinarith [Real.neg_one_le_cos t]
  have hcos_le_one : (1 + Real.cos t) / 2 ≤ 1 := by
    nlinarith [Real.cos_le_one t]
  have hcos_pow_le : ((1 + Real.cos t) / 2) ^ Mcy ≤ 1 := by
    simpa using pow_le_one₀ hcos_nonneg hcos_le_one
  have hlhs :
      (((1 + Real.cos t) / 2) ^ Mcy * (κ₀ : ℝ)) ≤ (κ₀ : ℝ) := by
    simpa using mul_le_mul_of_nonneg_right hcos_pow_le hκ₀_nonneg
  have hsin_half : (1 : ℝ) / 2 ≤ Real.sin t := by
    exact sin_ge_half_of_write_window j (by
      simpa [selectorMUWriteStartTime, selectorMUWriteReadTime] using ht)
  have hsin_base : (3 / 4 : ℝ) ≤ (1 + Real.sin t) / 2 := by
    linarith
  have hsin_pow :
      ((3 / 4 : ℝ) ^ Mcy) ≤ ((1 + Real.sin t) / 2) ^ Mcy := by
    exact pow_le_pow_left₀ (by norm_num) hsin_base Mcy
  have hgate_scale :
      ((3 / 4 : ℝ) ^ Mcy) * (g₀ : ℝ) ≤
        ((1 + Real.sin t) / 2) ^ Mcy * (g₀ : ℝ) := by
    exact mul_le_mul_of_nonneg_right hsin_pow hg₀_nonneg
  have ht_ge_start : selectorMUWriteStartTime j ≤ t := ht.1
  have hclock_nonneg :
      0 ≤ bgpParams38.cα * (t - selectorMUWriteStartTime j) := by
    have hcα : 0 ≤ bgpParams38.cα := by norm_num [bgpParams38]
    exact mul_nonneg hcα (sub_nonneg.mpr ht_ge_start)
  have hexp_one :
      1 ≤ Real.exp (bgpParams38.cα * (t - selectorMUWriteStartTime j)) := by
    simpa using Real.one_le_exp_iff.mpr hclock_nonneg
  have hgate_nonneg :
      0 ≤ ((1 + Real.sin t) / 2) ^ Mcy * (g₀ : ℝ) :=
    mul_nonneg (pow_nonneg (le_trans (by norm_num : (0 : ℝ) ≤ 3 / 4) hsin_base) Mcy)
      hg₀_nonneg
  have hclock_mul :
      ((1 + Real.sin t) / 2) ^ Mcy * (g₀ : ℝ) ≤
        ((1 + Real.sin t) / 2) ^ Mcy * (g₀ : ℝ) *
          Real.exp (bgpParams38.cα * (t - selectorMUWriteStartTime j)) := by
    simpa [mul_assoc] using mul_le_mul_of_nonneg_left hexp_one hgate_nonneg
  calc
    (((1 + Real.cos t) / 2) ^ Mcy * (κ₀ : ℝ)) ≤ (κ₀ : ℝ) := hlhs
    _ ≤ ((3 / 4 : ℝ) ^ Mcy) * (g₀ : ℝ) := hscale
    _ ≤ ((1 + Real.sin t) / 2) ^ Mcy * (g₀ : ℝ) := hgate_scale
    _ ≤ ((1 + Real.sin t) / 2) ^ Mcy * (g₀ : ℝ) *
          Real.exp (bgpParams38.cα * (t - selectorMUWriteStartTime j)) := hclock_mul
    _ =
        ((1 : ℝ) * Real.exp (-(bgpParams38.cα * selectorMUWriteStartTime j))) *
          (((1 + Real.sin t) / 2) ^ Mcy *
            ((g₀ : ℝ) * Real.exp (bgpParams38.cα * t))) := by
          rw [show bgpParams38.cα * (t - selectorMUWriteStartTime j) =
              bgpParams38.cα * t + -(bgpParams38.cα * selectorMUWriteStartTime j) by ring,
            Real.exp_add]
          ring

theorem solMURepl_static_hdom_nonneg :
    ∀ t : ℝ, 0 ≤ t → t ∈ selectorSchedule.domain :=
  selectorSchedule_domain_of_nonneg_structural

theorem solMURepl_static_hdom_write :
    ∀ (w : ℕ) j, ∀ t ∈ Icc (selectorMUWriteHoldTime j)
      (selectorMUWriteReadTime j), t ∈ selectorSchedule.domain := by
  intro w j t ht
  exact selectorMU_hdom_writeStart w j t
    ⟨le_trans (selectorMUWriteStart_le_hold j) ht.1, ht.2⟩

theorem solMURepl_static_hgZ_cont
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀) :
    ∀ w, Continuous fun t : ℝ =>
      bgpParams38.A * (sol w).α t * bGateZ bgpParams38.L ((sol w).μ t) t := by
  intro w
  exact selector_replicator_gateZ_integrand_continuous (sol w)

theorem solMURepl_static_hgZ0
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀) :
    ∀ w j, ∀ t ∈ Icc (selectorMUWriteHoldTime j)
      (selectorMUWriteReadTime j),
        0 ≤ bgpParams38.A * (sol w).α t * bGateZ bgpParams38.L ((sol w).μ t) t := by
  intro w j t ht
  have ht0 : 0 ≤ t :=
    le_trans (le_trans (selectorMUWriteStartTime_nonneg j)
      (selectorMUWriteStart_le_hold j)) ht.1
  exact selector_replicator_gateZ_integrand_nonneg (sol w)
    selectorSchedule_domain_of_nonneg_structural (by norm_num [bgpParams38]) ht0

/-- Replicator selector mass is conserved on the whole forward domain. -/
theorem solMURepl_static_lam_sum_forward
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol) :
    ∀ w, ∀ t : ℝ, 0 ≤ t →
      (∑ v : UniversalLocalView, (sol w).lam v t) = 1 := by
  classical
  intro w
  haveI : Nonempty UniversalLocalView := ⟨defaultLocalViewU⟩
  have hode : ∀ v : UniversalLocalView, ∀ s : ℝ, 0 ≤ s →
      HasDerivAt ((sol w).lam v)
        ((((1 + Real.cos s) / 2) ^ Mcy * (κ₀ : ℝ)) *
            (1 / (Fintype.card UniversalLocalView : ℝ) - (sol w).lam v s)
          + (((1 + Real.sin s) / 2) ^ Mcy *
              ((g₀ : ℝ) * Real.exp (bgpParams38.cα * s))) *
            (sol w).lam v s *
              (universalPval eta heta v ((sol w).u s)
                - ∑ u : UniversalLocalView,
                    (sol w).lam u s * universalPval eta heta u ((sol w).u s))) s := by
    intro v s hs
    simpa [selectorSchedule] using
      (sol w).lam_hasDeriv v s (by simpa [selectorSchedule] using hs)
  exact
    replicator_sum_lam_eq_one
      (lam := fun v s => (sol w).lam v s)
      (P := fun v s => universalPval eta heta v ((sol w).u s))
      (cr := fun s => ((1 + Real.cos s) / 2) ^ Mcy * (κ₀ : ℝ))
      (cg := fun s =>
        ((1 + Real.sin s) / 2) ^ Mcy *
          ((g₀ : ℝ) * Real.exp (bgpParams38.cα * s)))
      boxInputs.hcr_cont boxInputs.hcg_cont
      (fun v => (sol w).cont_lam v)
      (boxInputs.hP_cont w) hode (boxInputs.hlam_sum0 w)

/-- Replicator selector weights stay nonnegative on the whole forward domain. -/
theorem solMURepl_static_lam_nonneg_forward
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol) :
    ∀ w, ∀ v : UniversalLocalView, ∀ t : ℝ, 0 ≤ t → 0 ≤ (sol w).lam v t := by
  classical
  intro w
  haveI : Nonempty UniversalLocalView := ⟨defaultLocalViewU⟩
  have hode : ∀ v : UniversalLocalView, ∀ s : ℝ, 0 ≤ s →
      HasDerivAt ((sol w).lam v)
        ((((1 + Real.cos s) / 2) ^ Mcy * (κ₀ : ℝ)) *
            (1 / (Fintype.card UniversalLocalView : ℝ) - (sol w).lam v s)
          + (((1 + Real.sin s) / 2) ^ Mcy *
              ((g₀ : ℝ) * Real.exp (bgpParams38.cα * s))) *
            (sol w).lam v s *
              (universalPval eta heta v ((sol w).u s)
                - ∑ u : UniversalLocalView,
                    (sol w).lam u s * universalPval eta heta u ((sol w).u s))) s := by
    intro v s hs
    simpa [selectorSchedule] using
      (sol w).lam_hasDeriv v s (by simpa [selectorSchedule] using hs)
  exact
    replicator_lam_nonneg
      (lam := fun v s => (sol w).lam v s)
      (P := fun v s => universalPval eta heta v ((sol w).u s))
      (cr := fun s => ((1 + Real.cos s) / 2) ^ Mcy * (κ₀ : ℝ))
      (cg := fun s =>
        ((1 + Real.sin s) / 2) ^ Mcy *
          ((g₀ : ℝ) * Real.exp (bgpParams38.cα * s)))
      boxInputs.hcr_cont boxInputs.hcg_cont
      (fun v => (sol w).cont_lam v)
      (boxInputs.hP_cont w) boxInputs.hcr_nonneg hode
      (boxInputs.hlam_init_nonneg w)

/-- Replicator selector mass is conserved on the forward domain. -/
theorem solMURepl_static_hsum
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol) :
    ∀ w j, ∀ t ∈ Icc (selectorMUWriteHoldTime j)
      (selectorMUWriteReadTime j),
        (∑ v : UniversalLocalView, (sol w).lam v t) = 1 := by
  classical
  intro w j t ht
  haveI : Nonempty UniversalLocalView := ⟨defaultLocalViewU⟩
  have hode : ∀ v : UniversalLocalView, ∀ s : ℝ, 0 ≤ s →
      HasDerivAt ((sol w).lam v)
        ((((1 + Real.cos s) / 2) ^ Mcy * (κ₀ : ℝ)) *
            (1 / (Fintype.card UniversalLocalView : ℝ) - (sol w).lam v s)
          + (((1 + Real.sin s) / 2) ^ Mcy *
              ((g₀ : ℝ) * Real.exp (bgpParams38.cα * s))) *
            (sol w).lam v s *
              (universalPval eta heta v ((sol w).u s)
                - ∑ u : UniversalLocalView,
                    (sol w).lam u s * universalPval eta heta u ((sol w).u s))) s := by
    intro v s hs
    simpa [selectorSchedule] using
      (sol w).lam_hasDeriv v s (by simpa [selectorSchedule] using hs)
  have hsum_forward : ∀ s : ℝ, 0 ≤ s →
      (∑ v : UniversalLocalView, (sol w).lam v s) = 1 :=
    replicator_sum_lam_eq_one
      (lam := fun v s => (sol w).lam v s)
      (P := fun v s => universalPval eta heta v ((sol w).u s))
      (cr := fun s => ((1 + Real.cos s) / 2) ^ Mcy * (κ₀ : ℝ))
      (cg := fun s =>
        ((1 + Real.sin s) / 2) ^ Mcy *
          ((g₀ : ℝ) * Real.exp (bgpParams38.cα * s)))
      boxInputs.hcr_cont boxInputs.hcg_cont
      (fun v => (sol w).cont_lam v)
      (boxInputs.hP_cont w) hode (boxInputs.hlam_sum0 w)
  have ht0 : 0 ≤ t :=
    le_trans (le_trans (selectorMUWriteStartTime_nonneg j)
      (selectorMUWriteStart_le_hold j)) ht.1
  exact hsum_forward t ht0

/-- Replicator selector weights stay nonnegative on the forward domain. -/
theorem solMURepl_static_hlam_nonneg
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol) :
    ∀ w j, ∀ t ∈ Icc (selectorMUWriteHoldTime j)
      (selectorMUWriteReadTime j), ∀ v : UniversalLocalView,
        0 ≤ (sol w).lam v t := by
  classical
  intro w j t ht v
  haveI : Nonempty UniversalLocalView := ⟨defaultLocalViewU⟩
  have hode : ∀ v : UniversalLocalView, ∀ s : ℝ, 0 ≤ s →
      HasDerivAt ((sol w).lam v)
        ((((1 + Real.cos s) / 2) ^ Mcy * (κ₀ : ℝ)) *
            (1 / (Fintype.card UniversalLocalView : ℝ) - (sol w).lam v s)
          + (((1 + Real.sin s) / 2) ^ Mcy *
              ((g₀ : ℝ) * Real.exp (bgpParams38.cα * s))) *
            (sol w).lam v s *
              (universalPval eta heta v ((sol w).u s)
                - ∑ u : UniversalLocalView,
                    (sol w).lam u s * universalPval eta heta u ((sol w).u s))) s := by
    intro v s hs
    simpa [selectorSchedule] using
      (sol w).lam_hasDeriv v s (by simpa [selectorSchedule] using hs)
  have hlam_forward :
      ∀ v : UniversalLocalView, ∀ s : ℝ, 0 ≤ s → 0 ≤ (sol w).lam v s :=
    replicator_lam_nonneg
      (lam := fun v s => (sol w).lam v s)
      (P := fun v s => universalPval eta heta v ((sol w).u s))
      (cr := fun s => ((1 + Real.cos s) / 2) ^ Mcy * (κ₀ : ℝ))
      (cg := fun s =>
        ((1 + Real.sin s) / 2) ^ Mcy *
          ((g₀ : ℝ) * Real.exp (bgpParams38.cα * s)))
      boxInputs.hcr_cont boxInputs.hcg_cont
      (fun v => (sol w).cont_lam v)
      (boxInputs.hP_cont w) boxInputs.hcr_nonneg hode
      (boxInputs.hlam_init_nonneg w)
  have ht0 : 0 ≤ t :=
    le_trans (le_trans (selectorMUWriteStartTime_nonneg j)
      (selectorMUWriteStart_le_hold j)) ht.1
  exact hlam_forward v t ht0

theorem solMURepl_static_hmult0 : 0 ≤ selectorMUHStartMult :=
  selectorMUHStartMult_nonneg

theorem solMURepl_static_hmultbound :
    ∀ w j, ∀ i, stackMachineEncodingU.coordMultiplier (solMUReplStaticCfg w j) i
      ≤ selectorMUHStartMult := by
  intro w j i
  exact selectorMU_coordMultiplier_le_hstartMult (solMUReplStaticCfg w j) i

/-- Halt-coordinate branch spread is static: every branch halt target is
Boolean, so two such targets differ by at most `1`.  This is intentionally only
the halt coordinate; all stack-coordinate spread still depends on the `u`-tube
or another bounded-branch invariant. -/
theorem solMURepl_static_halt_Rspread
    (u : Fin d_U → ℝ) (v vstar : UniversalLocalView) :
    |BranchData.evalBranch (branchU v) u haltCoordU
      - BranchData.evalBranch (branchU vstar) u haltCoordU| ≤ (1 : ℝ) := by
  have hv := branchU_halt_target_mem_Icc v u
  have hs := branchU_halt_target_mem_Icc vstar u
  have hle :
      BranchData.evalBranch (branchU v) u haltCoordU
        - BranchData.evalBranch (branchU vstar) u haltCoordU ≤ 1 := by
    linarith [hv.2, hs.1]
  have hge :
      -1 ≤ BranchData.evalBranch (branchU v) u haltCoordU
        - BranchData.evalBranch (branchU vstar) u haltCoordU := by
    linarith [hv.1, hs.2]
  exact abs_le.mpr ⟨hge, hle⟩

theorem solMURepl_static_halt_Rspread_nonneg : 0 ≤ (1 : ℝ) := by
  norm_num

/-- Static facts that can be consumed by the eventual P5 assembly.  This is not
the full `MUReplicatorSettledFacts`: P4 must still provide the tube/floor
fields and all non-halt branch-spread data needed to construct the final
concentration input bundle. -/
structure MUReplicatorSettledStaticFacts
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀) where
  cfg : ℕ → ℕ → UConf
  hcfg : ∀ w j, cfg w j = M_U.step^[j] (M_U.init w)
  hcfg_step : ∀ w j, M_U.step (cfg w j) = cfg w (j + 1)
  hg₀ : 0 < (g₀ : ℝ)
  hgap0 : 0 < selectorReplicatorGapVal eta heta
  hR0_nonneg : ∀ w : ℕ, ∀ᶠ j in atTop, 0 ≤ solMUReplStaticR0 w j
  hR0_bound : ∀ w : ℕ, ∀ᶠ j in atTop, solMUReplStaticR0 w j ≤ 1
  hκ₀_nonneg : 0 ≤ (κ₀ : ℝ)
  hCratio_nonneg : 0 ≤ (1 : ℝ)
  hratio_bound : ∀ (w : ℕ) j, ∀ t ∈
    Icc (selectorMUWriteStartTime j) (selectorMUWriteHoldTime j),
      (((1 + Real.cos t) / 2) ^ Mcy * (κ₀ : ℝ)) ≤
        ((1 : ℝ) * Real.exp (-(bgpParams38.cα * selectorMUWriteStartTime j))) *
          (((1 + Real.sin t) / 2) ^ Mcy *
            ((g₀ : ℝ) * Real.exp (bgpParams38.cα * t)))
  hdom_nonneg : ∀ t : ℝ, 0 ≤ t → t ∈ selectorSchedule.domain
  hdom_write : ∀ (w : ℕ) j, ∀ t ∈ Icc (selectorMUWriteHoldTime j)
      (selectorMUWriteReadTime j), t ∈ selectorSchedule.domain
  hgZ_cont : ∀ w, Continuous fun t : ℝ =>
    bgpParams38.A * (sol w).α t * bGateZ bgpParams38.L ((sol w).μ t) t
  hgZ0 : ∀ w j, ∀ t ∈ Icc (selectorMUWriteHoldTime j)
      (selectorMUWriteReadTime j),
    0 ≤ bgpParams38.A * (sol w).α t * bGateZ bgpParams38.L ((sol w).μ t) t
  hmult0 : 0 ≤ selectorMUHStartMult
  hmultbound : ∀ w j, ∀ i, stackMachineEncodingU.coordMultiplier (cfg w j) i
    ≤ selectorMUHStartMult
  hsum : ∀ w j, ∀ t ∈ Icc (selectorMUWriteHoldTime j)
      (selectorMUWriteReadTime j),
    (∑ v : UniversalLocalView, (sol w).lam v t) = 1
  hlam_nonneg : ∀ w j, ∀ t ∈ Icc (selectorMUWriteHoldTime j)
      (selectorMUWriteReadTime j), ∀ v : UniversalLocalView, 0 ≤ (sol w).lam v t
  hhalt_Rspread_nonneg : 0 ≤ (1 : ℝ)
  hhalt_spread : ∀ w j, ∀ t ∈ Icc (selectorMUWriteHoldTime j)
      (selectorMUWriteReadTime j), ∀ v : UniversalLocalView,
    v ≠ localViewU (cfg w j) →
      |BranchData.evalBranch (branchU v) ((sol w).u t) haltCoordU
        - BranchData.evalBranch (branchU (localViewU (cfg w j)))
            ((sol w).u t) haltCoordU| ≤ (1 : ℝ)

/-- Producer for all settled facts in this file's static scope. -/
noncomputable def solMURepl_settled_static_facts
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀)
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (herr : (gateSelectorAtomsCoordN (universalGateAtoms eta heta)).errSel < 1 / 2)
    (hκ₀_nonneg : 0 ≤ (κ₀ : ℝ))
    (hg₀ : 0 < (g₀ : ℝ))
    (hscale : (κ₀ : ℝ) ≤ ((3 / 4 : ℝ) ^ Mcy) * (g₀ : ℝ)) :
    MUReplicatorSettledStaticFacts sol := by
  refine
    { cfg := solMUReplStaticCfg
      hcfg := solMUReplStaticCfg_eq
      hcfg_step := solMUReplStaticCfg_step
      hg₀ := solMURepl_static_hg0 hg₀
      hgap0 := solMURepl_static_hgap0 eta heta herr
      hR0_nonneg := solMURepl_static_hR0_nonneg
      hR0_bound := solMURepl_static_hR0_bound
      hκ₀_nonneg := solMURepl_static_hkappa_nonneg hκ₀_nonneg
      hCratio_nonneg := solMURepl_static_hCratio_nonneg
      hratio_bound := solMURepl_static_hratio_bound hκ₀_nonneg hg₀.le hscale
      hdom_nonneg := solMURepl_static_hdom_nonneg
      hdom_write := solMURepl_static_hdom_write
      hgZ_cont := solMURepl_static_hgZ_cont sol
      hgZ0 := solMURepl_static_hgZ0 sol
      hmult0 := solMURepl_static_hmult0
      hmultbound := solMURepl_static_hmultbound
      hsum := solMURepl_static_hsum boxInputs
      hlam_nonneg := solMURepl_static_hlam_nonneg boxInputs
      hhalt_Rspread_nonneg := solMURepl_static_halt_Rspread_nonneg
      hhalt_spread := ?_ }
  intro w j t ht v hv
  exact solMURepl_static_halt_Rspread ((sol w).u t) v (localViewU (solMUReplStaticCfg w j))

#print axioms solMUReplStaticCfg
#print axioms solMUReplStaticCfg_eq
#print axioms solMUReplStaticCfg_step
#print axioms solMURepl_static_hgap0
#print axioms solMUReplStaticR0
#print axioms solMURepl_static_hR0_nonneg
#print axioms solMURepl_static_hR0_bound
#print axioms solMUReplStaticKreset
#print axioms solMURepl_static_hKreset_eq
#print axioms solMURepl_static_hCratio_nonneg
#print axioms solMURepl_static_hkappa_nonneg
#print axioms solMURepl_static_hg0
#print axioms solMURepl_static_hratio_bound
#print axioms solMURepl_static_hdom_nonneg
#print axioms solMURepl_static_hdom_write
#print axioms solMURepl_static_hgZ_cont
#print axioms solMURepl_static_hgZ0
#print axioms solMURepl_static_hsum
#print axioms solMURepl_static_hlam_nonneg
#print axioms solMURepl_static_hmult0
#print axioms solMURepl_static_hmultbound
#print axioms solMURepl_static_halt_Rspread
#print axioms solMURepl_static_halt_Rspread_nonneg
#print axioms MUReplicatorSettledStaticFacts
#print axioms solMURepl_settled_static_facts

end Ripple.BoundedUniversality.BGP
