import Ripple.BoundedUniversality.BGP.SelectorReplicatorSettledResidual

/-!
# P-generic Hoff field-integral residuals

This file mirrors the `bgpParams38` Hoff field-integral surface from
`SelectorReplicatorSettledResidual` at an arbitrary `DynGateParams`.
-/

noncomputable section

namespace Ripple.BoundedUniversality.BGP

open MachineInstance UniversalMachine Filter Set
open scoped BigOperators Topology

private theorem abs_sub_le_one_of_unit_interval_pair {x y : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) :
    |x - y| ≤ (1 : ℝ) := by
  rw [abs_le]
  constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

private theorem selectorDynSol_flag_box_of_mixTarget_haltCoord_mem_Icc_replP
    {p : DynGateParams}
    {eta : ℚ} {heta : 0 < eta} {M : ℕ} {κ₀ g₀ : ℚ}
    (sol : SelectorReplicatorDynSol d_U B_U UniversalLocalView p selectorSchedule
      branchU
      (fun t => ((1 + Real.cos t) / 2) ^ M)
      (fun t => ((1 + Real.sin t) / 2) ^ M)
      (fun _ => (κ₀ : ℝ))
      (fun t => (g₀ : ℝ) * Real.exp (p.cα * t))
      (universalPval eta heta))
    (hA : 0 ≤ p.A)
    (hz0 : sol.z 0 haltCoordU ∈ Icc (0 : ℝ) 1)
    (hmix : ∀ t : ℝ, 0 ≤ t →
      selectorMixTarget branchU sol.u sol.lam t haltCoordU ∈ Icc (0 : ℝ) 1) :
    (∀ t : ℝ, 0 ≤ t → sol.z t haltCoordU ≤ 1) ∧
      (∀ t : ℝ, 0 ≤ t → 0 ≤ sol.z t haltCoordU) := by
  constructor
  · intro T hT
    have hupper := Ripple.scalar_upper_barrier_exterior_on_Icc
      (T := T) (b := (1 : ℝ)) hT
      (fun t : ℝ => sol.z t haltCoordU)
      (fun t : ℝ =>
        p.A * sol.α t * bGateZ p.L (sol.μ t) t *
          (selectorMixTarget branchU sol.u sol.lam t haltCoordU -
            sol.z t haltCoordU))
      hz0.2
      ((sol.cont_z haltCoordU).continuousOn)
      (fun t ht =>
        (sol.z_hasDeriv t
          (selectorSchedule_domain_of_nonneg_box t ht.1)
          haltCoordU).hasDerivWithinAt)
      (fun t ht _hwall => by
        have hcoef : 0 ≤ p.A * sol.α t * bGateZ p.L (sol.μ t) t := by
          have halpha : sol.α t = Real.exp (p.cα * t) :=
            sol.alpha_eq_exp selectorSchedule_domain_of_nonneg_box ht.1
          rw [halpha]
          exact mul_nonneg (mul_nonneg hA (Real.exp_pos _).le)
            (bGateZ_pos p.L (sol.μ t) t).le
        have hdiff :
            selectorMixTarget branchU sol.u sol.lam t haltCoordU -
              sol.z t haltCoordU ≤ 0 := by
          linarith [(hmix t ht.1).2]
        exact mul_nonpos_of_nonneg_of_nonpos hcoef hdiff)
    exact hupper T (right_mem_Icc.mpr hT)
  · intro T hT
    have hlower := Ripple.scalar_lower_barrier_exterior_on_Icc
      (T := T) (a := (0 : ℝ)) hT
      (fun t : ℝ => sol.z t haltCoordU)
      (fun t : ℝ =>
        p.A * sol.α t * bGateZ p.L (sol.μ t) t *
          (selectorMixTarget branchU sol.u sol.lam t haltCoordU -
            sol.z t haltCoordU))
      hz0.1
      ((sol.cont_z haltCoordU).continuousOn)
      (fun t ht =>
        (sol.z_hasDeriv t
          (selectorSchedule_domain_of_nonneg_box t ht.1)
          haltCoordU).hasDerivWithinAt)
      (fun t ht _hwall => by
        have hcoef : 0 ≤ p.A * sol.α t * bGateZ p.L (sol.μ t) t := by
          have halpha : sol.α t = Real.exp (p.cα * t) :=
            sol.alpha_eq_exp selectorSchedule_domain_of_nonneg_box ht.1
          rw [halpha]
          exact mul_nonneg (mul_nonneg hA (Real.exp_pos _).le)
            (bGateZ_pos p.L (sol.μ t) t).le
        have hdiff :
            0 ≤ selectorMixTarget branchU sol.u sol.lam t haltCoordU -
              sol.z t haltCoordU := by
          linarith [(hmix t ht.1).1]
        exact mul_nonneg hcoef hdiff)
    exact hlower T (right_mem_Icc.mpr hT)

/-- Forward halt-coordinate mix-target box from `MUReplicatorBoxInputsP`. -/
theorem MUReplicatorBoxInputsP.halt_mixTarget_mem_Icc
    {p : DynGateParams}
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamilyP p eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputsP p eta heta Mcy κ₀ g₀ sol) :
    ∀ w t, 0 ≤ t →
      selectorMixTarget branchU (sol w).u (sol w).lam t haltCoordU ∈ Icc (0 : ℝ) 1 := by
  classical
  intro w t ht
  haveI : Nonempty UniversalLocalView := ⟨defaultLocalViewU⟩
  have hode : ∀ v : UniversalLocalView, ∀ s : ℝ, 0 ≤ s →
      HasDerivAt ((sol w).lam v)
        ((((1 + Real.cos s) / 2) ^ Mcy * (κ₀ : ℝ)) *
            (1 / (Fintype.card UniversalLocalView : ℝ) - (sol w).lam v s)
          + (((1 + Real.sin s) / 2) ^ Mcy *
              ((g₀ : ℝ) * Real.exp (p.cα * s))) *
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
          ((g₀ : ℝ) * Real.exp (p.cα * s)))
      boxInputs.hcr_cont boxInputs.hcg_cont
      (fun v => (sol w).cont_lam v)
      (boxInputs.hP_cont w) hode (boxInputs.hlam_sum0 w)
  have hlam_nonneg_forward :
      ∀ v : UniversalLocalView, ∀ s : ℝ, 0 ≤ s → 0 ≤ (sol w).lam v s :=
    replicator_lam_nonneg
      (lam := fun v s => (sol w).lam v s)
      (P := fun v s => universalPval eta heta v ((sol w).u s))
      (cr := fun s => ((1 + Real.cos s) / 2) ^ Mcy * (κ₀ : ℝ))
      (cg := fun s =>
        ((1 + Real.sin s) / 2) ^ Mcy *
          ((g₀ : ℝ) * Real.exp (p.cα * s)))
      boxInputs.hcr_cont boxInputs.hcg_cont
      (fun v => (sol w).cont_lam v)
      (boxInputs.hP_cont w) boxInputs.hcr_nonneg hode
      (boxInputs.hlam_init_nonneg w)
  exact selectorMixTarget_haltCoord_mem_Icc_of_lam_sum_eq_one
    (sol w).u (sol w).lam t
    (fun v => hlam_nonneg_forward v t ht)
    (hsum_forward t ht)

/-- Forward halt-coordinate z-box from `MUReplicatorBoxInputsP`. -/
theorem MUReplicatorBoxInputsP.halt_z_mem_Icc
    {p : DynGateParams}
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamilyP p eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputsP p eta heta Mcy κ₀ g₀ sol)
    (hA : 0 ≤ p.A) :
    ∀ w t, 0 ≤ t → (sol w).z t haltCoordU ∈ Icc (0 : ℝ) 1 := by
  intro w t ht
  have hzbox :=
    selectorDynSol_flag_box_of_mixTarget_haltCoord_mem_Icc_replP
      (sol w) hA (boxInputs.hz0 w)
      (boxInputs.halt_mixTarget_mem_Icc w)
  exact ⟨hzbox.2 t ht, hzbox.1 t ht⟩

/-- Coarse unit bound for the P-generic z-start mismatch. -/
theorem MUReplicatorBoxInputsP.hz_writeHold_static_next_le_one
    {p : DynGateParams}
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamilyP p eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputsP p eta heta Mcy κ₀ g₀ sol)
    (hA : 0 ≤ p.A) :
    ∀ w j,
      |(sol w).z (selectorMUWriteHoldTime j) haltCoordU -
        stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 1)) haltCoordU| ≤
          (1 : ℝ) := by
  intro w j
  have ht0 : 0 ≤ selectorMUWriteHoldTime j := by
    unfold selectorMUWriteHoldTime
    positivity
  exact abs_sub_le_one_of_unit_interval_pair
    (boxInputs.halt_z_mem_Icc hA w (selectorMUWriteHoldTime j) ht0)
    (enc_haltCoordU_mem_unit (solMUReplStaticCfg w (j + 1)))

/-- Coarse unit bound for the P-generic finite-prefix self-hold patch. -/
theorem MUReplicatorBoxInputsP.hfiniteHold_one
    {p : DynGateParams}
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamilyP p eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputsP p eta heta Mcy κ₀ g₀ sol)
    (hA : 0 ≤ p.A) :
    ∀ w j, ∀ t ∈ Icc (selectorMUInterReadStart j) (selectorMUNextRead j),
      |(sol w).z t haltCoordU -
        (sol w).z (selectorMUInterReadStart j) haltCoordU| ≤ (1 : ℝ) := by
  intro w j t ht
  have ha0 : 0 ≤ selectorMUInterReadStart j := by
    unfold selectorMUInterReadStart selectorMUWriteReadTime
    positivity
  have ht0 : 0 ≤ t := le_trans ha0 ht.1
  exact abs_sub_le_one_of_unit_interval_pair
    (boxInputs.halt_z_mem_Icc hA w t ht0)
    (boxInputs.halt_z_mem_Icc hA w (selectorMUInterReadStart j) ha0)

/-- P-generic absolute halt-coordinate z-field integrand used by `hoff`. -/
def selectorMUHoffIntegrandP
    {p : DynGateParams}
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamilyP p eta heta Mcy κ₀ g₀) (w : ℕ) (τ : ℝ) : ℝ :=
  |p.A * (sol w).α τ * bGateZ p.L ((sol w).μ τ) τ *
    (selectorMixTarget branchU (sol w).u (sol w).lam τ haltCoordU -
      (sol w).z τ haltCoordU)|

/-- Continuity of the P-generic absolute halt-coordinate field integrand. -/
theorem selectorMUHoffIntegrandP_continuous
    {p : DynGateParams}
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamilyP p eta heta Mcy κ₀ g₀} (w : ℕ) :
    Continuous fun τ : ℝ => selectorMUHoffIntegrandP sol w τ := by
  unfold selectorMUHoffIntegrandP
  exact ((selector_replicator_gateZ_integrand_continuous (sol w)).mul
    (((sol w).cont_mixTarget haltCoordU).sub ((sol w).cont_z haltCoordU))).abs

/-- Nonnegativity of the P-generic absolute halt-coordinate field integrand. -/
theorem selectorMUHoffIntegrandP_nonneg
    {p : DynGateParams}
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamilyP p eta heta Mcy κ₀ g₀) (w : ℕ) (τ : ℝ) :
    0 ≤ selectorMUHoffIntegrandP sol w τ := by
  exact abs_nonneg _

/-- Compatibility sentinel for the 38-parameter Hoff integrand. -/
theorem selectorMUHoffIntegrandP_eq_38
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀) (w : ℕ) (τ : ℝ) :
    selectorMUHoffIntegrandP (p := bgpParams38) sol w τ =
      selectorMUHoffIntegrand sol w τ := rfl

/-- P-generic z-gate coefficient whose integral controls the left/right caps. -/
def selectorMUHoffGateCoeffP
    {p : DynGateParams}
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamilyP p eta heta Mcy κ₀ g₀) (w : ℕ) (τ : ℝ) : ℝ :=
  p.A * (sol w).α τ * bGateZ p.L ((sol w).μ τ) τ

/-- Continuity of the P-generic Hoff z-gate coefficient. -/
theorem selectorMUHoffGateCoeffP_continuous
    {p : DynGateParams}
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamilyP p eta heta Mcy κ₀ g₀} (w : ℕ) :
    Continuous fun τ : ℝ => selectorMUHoffGateCoeffP sol w τ := by
  simpa [selectorMUHoffGateCoeffP] using
    selector_replicator_gateZ_integrand_continuous (sol w)

/-- Left P-generic `hoff` cap from a z-gate coefficient integral cap. -/
theorem selectorMUHoff_hcapLeft_of_gateP
    {p : DynGateParams}
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamilyP p eta heta Mcy κ₀ g₀}
    (hA : 0 ≤ p.A)
    (boxInputs : MUReplicatorBoxInputsP p eta heta Mcy κ₀ g₀ sol)
    {capLeft : ℕ → ℕ → ℝ}
    (hgateLeft : ∀ w j, ∀ t ∈ Icc (selectorMUInterReadStart j)
      (selectorMUZOffStart j),
      (∫ τ in (selectorMUInterReadStart j)..t,
        selectorMUHoffGateCoeffP sol w τ) ≤ capLeft w j) :
    ∀ w j, ∀ t ∈ Icc (selectorMUInterReadStart j) (selectorMUZOffStart j),
      (∫ τ in (selectorMUInterReadStart j)..t,
        selectorMUHoffIntegrandP sol w τ) ≤ capLeft w j := by
  intro w j t ht
  have ha0 : 0 ≤ selectorMUInterReadStart j := by
    unfold selectorMUInterReadStart selectorMUWriteReadTime
    positivity
  have hmix_box : ∀ τ ∈ Icc (selectorMUInterReadStart j) (selectorMUZOffStart j),
      selectorMixTarget branchU (sol w).u (sol w).lam τ haltCoordU ∈ Icc (0 : ℝ) 1 := by
    intro τ hτ
    exact boxInputs.halt_mixTarget_mem_Icc w τ (le_trans ha0 hτ.1)
  have hz_box : ∀ τ ∈ Icc (selectorMUInterReadStart j) (selectorMUZOffStart j),
      (sol w).z τ haltCoordU ∈ Icc (0 : ℝ) 1 := by
    intro τ hτ
    exact boxInputs.halt_z_mem_Icc hA w τ (le_trans ha0 hτ.1)
  have hfield :=
    flag_fieldIntegral_bound_of_gate_integral_repl
      (sol w) haltCoordU
      (a := selectorMUInterReadStart j) (b := selectorMUZOffStart j)
      (δhold := capLeft w j)
      (selector_replicator_gateZ_integrand_continuous (sol w))
      (by
        intro τ hτ
        exact selector_replicator_gateZ_integrand_nonneg (sol w)
          selectorSchedule_domain_of_nonneg_structural hA
          (le_trans ha0 hτ.1))
      hmix_box hz_box
      (by
        intro τ hτ
        simpa [selectorMUHoffGateCoeffP] using hgateLeft w j τ hτ)
  simpa [selectorMUHoffIntegrandP, selectorMUHoffGateCoeffP] using hfield t ht

/-- Right P-generic `hoff` cap from a z-gate coefficient integral cap. -/
theorem selectorMUHoff_hcapRight_of_gateP
    {p : DynGateParams}
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamilyP p eta heta Mcy κ₀ g₀}
    (hA : 0 ≤ p.A)
    (boxInputs : MUReplicatorBoxInputsP p eta heta Mcy κ₀ g₀ sol)
    {capRight : ℕ → ℕ → ℝ}
    (hgateRight : ∀ w j, selectorMUHaltEncConstW solMUReplStaticCfg w j → ∀ t ∈
      Icc (selectorMUZOffEnd j)
      (selectorMUNextWriteStart j),
      (∫ τ in (selectorMUZOffEnd j)..t,
        selectorMUHoffGateCoeffP sol w τ) ≤ capRight w j) :
    ∀ w j, selectorMUHaltEncConstW solMUReplStaticCfg w j → ∀ t ∈
      Icc (selectorMUZOffEnd j) (selectorMUNextWriteStart j),
      (∫ τ in (selectorMUZOffEnd j)..t,
        selectorMUHoffIntegrandP sol w τ) ≤ capRight w j := by
  intro w j henc_const t ht
  have ha0 : 0 ≤ selectorMUZOffEnd j := by
    unfold selectorMUZOffEnd
    positivity
  have hmix_box : ∀ τ ∈ Icc (selectorMUZOffEnd j) (selectorMUNextWriteStart j),
      selectorMixTarget branchU (sol w).u (sol w).lam τ haltCoordU ∈ Icc (0 : ℝ) 1 := by
    intro τ hτ
    exact boxInputs.halt_mixTarget_mem_Icc w τ (le_trans ha0 hτ.1)
  have hz_box : ∀ τ ∈ Icc (selectorMUZOffEnd j) (selectorMUNextWriteStart j),
      (sol w).z τ haltCoordU ∈ Icc (0 : ℝ) 1 := by
    intro τ hτ
    exact boxInputs.halt_z_mem_Icc hA w τ (le_trans ha0 hτ.1)
  have hfield :=
    flag_fieldIntegral_bound_of_gate_integral_repl
      (sol w) haltCoordU
      (a := selectorMUZOffEnd j) (b := selectorMUNextWriteStart j)
      (δhold := capRight w j)
      (selector_replicator_gateZ_integrand_continuous (sol w))
      (by
        intro τ hτ
        exact selector_replicator_gateZ_integrand_nonneg (sol w)
          selectorSchedule_domain_of_nonneg_structural hA
          (le_trans ha0 hτ.1))
      hmix_box hz_box
      (by
        intro τ hτ
        simpa [selectorMUHoffGateCoeffP] using hgateRight w j henc_const τ hτ)
  simpa [selectorMUHoffIntegrandP, selectorMUHoffGateCoeffP] using hfield t ht

/-- P-generic z-off envelope on the middle inter-read interval. -/
def selectorMUHoffMiddleEnvelopeP (p : DynGateParams) (τ : ℝ) : ℝ :=
  p.A * Real.exp (-((p.cμ * (1 / 2 : ℝ) ^ p.L - p.cα) * τ))

/-- Scalar residual for the P-generic middle z-off envelope integral. -/
structure SelectorMUHoffMiddleEnvelopeResidualP (p : DynGateParams) where
  capMid : ℕ → ℕ → ℝ
  henvInt : ∀ w j, ∀ t ∈ Icc (selectorMUZOffStart j) (selectorMUZOffEnd j),
    (∫ τ in (selectorMUZOffStart j)..t, selectorMUHoffMiddleEnvelopeP p τ) ≤
      capMid w j

/-- P-generic integral-form producer for inter-read halt-coordinate self drift. -/
structure SelectorMUHoffFieldIntegralResidualP
    {p : DynGateParams}
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamilyP p eta heta Mcy κ₀ g₀) where
  hfieldInt : ∀ w j, selectorMUHaltEncConstW solMUReplStaticCfg w j → ∀ t ∈
      Icc (selectorMUInterReadStart j)
      (selectorMUNextWriteStart j),
    (∫ τ in (selectorMUInterReadStart j)..t,
      selectorMUHoffIntegrandP sol w τ) ≤ selectorReplicatorHoldEnvelope j

namespace SelectorMUHoffFieldIntegralResidualP

/-- Convert the P-generic field-integral producer into the current `p_hoff` shape. -/
theorem p_hoff
    {p : DynGateParams}
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamilyP p eta heta Mcy κ₀ g₀}
    (res : SelectorMUHoffFieldIntegralResidualP sol) :
    ∀ w j, selectorMUHaltEncConstW solMUReplStaticCfg w j → ∀ t ∈
        Icc (selectorMUInterReadStart j)
        (selectorMUNextWriteStart j),
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
      (by
        intro s hs
        simpa [selectorMUHoffIntegrandP] using res.hfieldInt w j henc_const s hs)
      t ht

end SelectorMUHoffFieldIntegralResidualP

/-- Phase-split form of the P-generic `hoff` field-integral residual. -/
structure SelectorMUHoffSplitFieldIntegralResidualP
    {p : DynGateParams}
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamilyP p eta heta Mcy κ₀ g₀) where
  capLeft : ℕ → ℕ → ℝ
  capMid : ℕ → ℕ → ℝ
  capRight : ℕ → ℕ → ℝ
  hcapLeft : ∀ w j, ∀ t ∈ Icc (selectorMUInterReadStart j) (selectorMUZOffStart j),
    (∫ τ in (selectorMUInterReadStart j)..t,
      selectorMUHoffIntegrandP sol w τ) ≤ capLeft w j
  hoffMid : ∀ w j, ∀ t ∈ Icc (selectorMUZOffStart j) (selectorMUZOffEnd j),
    (∫ τ in (selectorMUZOffStart j)..t,
      selectorMUHoffIntegrandP sol w τ) ≤ capMid w j
  hcapRight : ∀ w j, selectorMUHaltEncConstW solMUReplStaticCfg w j → ∀ t ∈
      Icc (selectorMUZOffEnd j) (selectorMUNextWriteStart j),
    (∫ τ in (selectorMUZOffEnd j)..t,
      selectorMUHoffIntegrandP sol w τ) ≤ capRight w j
  hsplitInt : ∀ w j, selectorMUHaltEncConstW solMUReplStaticCfg w j → ∀ t ∈
      Icc (selectorMUInterReadStart j)
      (selectorMUNextWriteStart j),
    (∫ τ in (selectorMUInterReadStart j)..t,
      selectorMUHoffIntegrandP sol w τ) ≤ capLeft w j + capMid w j + capRight w j
  hsum_le : ∀ w j, selectorMUHaltEncConstW solMUReplStaticCfg w j →
    capLeft w j + capMid w j + capRight w j ≤ selectorReplicatorHoldEnvelope j

namespace SelectorMUHoffSplitFieldIntegralResidualP

/-- Forget the P-generic phase-split residual to the full-integral residual. -/
def toFieldIntegralResidual
    {p : DynGateParams}
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamilyP p eta heta Mcy κ₀ g₀}
    (res : SelectorMUHoffSplitFieldIntegralResidualP sol) :
    SelectorMUHoffFieldIntegralResidualP sol where
  hfieldInt := by
    intro w j henc_const t ht
    exact le_trans
      (by simpa [selectorMUHoffIntegrandP] using res.hsplitInt w j henc_const t ht)
      (res.hsum_le w j henc_const)

end SelectorMUHoffSplitFieldIntegralResidualP

/-- P-generic middle z-offphase field-integral estimate. -/
theorem selectorMUHoff_middle_offphase_of_envelopeP
    {p : DynGateParams}
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamilyP p eta heta Mcy κ₀ g₀}
    (hA : 0 ≤ p.A) (hcμ : 0 ≤ p.cμ)
    (boxInputs : MUReplicatorBoxInputsP p eta heta Mcy κ₀ g₀ sol)
    (env : SelectorMUHoffMiddleEnvelopeResidualP p) :
    ∀ w j, ∀ t ∈ Icc (selectorMUZOffStart j) (selectorMUZOffEnd j),
      (∫ τ in (selectorMUZOffStart j)..t,
        selectorMUHoffIntegrandP sol w τ) ≤ env.capMid w j := by
  intro w j t ht
  have ha0 : 0 ≤ selectorMUZOffStart j := by
    unfold selectorMUZOffStart
    positivity
  have hdom : ∀ s : ℝ, 0 ≤ s → s ∈ selectorSchedule.domain :=
    selectorSchedule_domain_of_nonneg_structural
  have hα : ∀ τ ∈ Icc (selectorMUZOffStart j) (selectorMUZOffEnd j),
      (sol w).α τ = Real.exp (p.cα * τ) := by
    intro τ hτ
    exact (sol w).alpha_eq_exp hdom (le_trans ha0 hτ.1)
  have hμ : ∀ τ ∈ Icc (selectorMUZOffStart j) (selectorMUZOffEnd j),
      (sol w).μ τ = p.cμ * τ := by
    intro τ hτ
    rw [(sol w).mu_eq_linear hdom (le_trans ha0 hτ.1), (sol w).μ_at_zero]
    ring
  have hsin : ∀ τ ∈ Icc (selectorMUZOffStart j) (selectorMUZOffEnd j),
      Real.sin τ ≤ 0 := by
    intro τ hτ
    exact selectorMU_sin_nonpos_zOffMiddle j hτ.1 hτ.2
  have hmix_box : ∀ τ ∈ Icc (selectorMUZOffStart j) (selectorMUZOffEnd j),
      selectorMixTarget branchU (sol w).u (sol w).lam τ haltCoordU ∈ Icc (0 : ℝ) 1 := by
    intro τ hτ
    exact boxInputs.halt_mixTarget_mem_Icc w τ (le_trans ha0 hτ.1)
  have hz_box : ∀ τ ∈ Icc (selectorMUZOffStart j) (selectorMUZOffEnd j),
      (sol w).z τ haltCoordU ∈ Icc (0 : ℝ) 1 := by
    intro τ hτ
    exact boxInputs.halt_z_mem_Icc hA w τ (le_trans ha0 hτ.1)
  have hfield :=
    flag_fieldIntegral_bound_of_offphase_envelope_repl
      (sol w) haltCoordU
      (a := selectorMUZOffStart j) (b := selectorMUZOffEnd j)
      (A := p.A) (cμ := p.cμ) (cα := p.cα)
      (δhold := env.capMid w j)
      (selectorMUZOffStart_le_zOffEnd j) ha0
      hA hcμ
      (by rfl)
      (selector_replicator_gateZ_integrand_continuous (sol w))
      (by
        intro τ hτ
        exact selector_replicator_gateZ_integrand_nonneg (sol w)
          selectorSchedule_domain_of_nonneg_structural hA
          (le_trans ha0 hτ.1))
      hα hμ hsin hmix_box hz_box
      (by
        intro τ hτ
        simpa [selectorMUHoffMiddleEnvelopeP] using env.henvInt w j τ hτ)
  simpa [selectorMUHoffIntegrandP] using hfield t ht

/-- P-generic split integral bound from left, middle, and right caps. -/
theorem selectorMUHoff_hsplitInt_of_capsP
    {p : DynGateParams}
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamilyP p eta heta Mcy κ₀ g₀}
    (hA : 0 ≤ p.A) (hcμ : 0 ≤ p.cμ)
    (boxInputs : MUReplicatorBoxInputsP p eta heta Mcy κ₀ g₀ sol)
    {capLeft capRight : ℕ → ℕ → ℝ}
    (env : SelectorMUHoffMiddleEnvelopeResidualP p)
    (hcapLeft : ∀ w j, ∀ t ∈ Icc (selectorMUInterReadStart j) (selectorMUZOffStart j),
      (∫ τ in (selectorMUInterReadStart j)..t,
        selectorMUHoffIntegrandP sol w τ) ≤ capLeft w j)
    (hcapRight : ∀ w j, selectorMUHaltEncConstW solMUReplStaticCfg w j → ∀ t ∈
      Icc (selectorMUZOffEnd j) (selectorMUNextWriteStart j),
      (∫ τ in (selectorMUZOffEnd j)..t,
        selectorMUHoffIntegrandP sol w τ) ≤ capRight w j) :
    ∀ w j, selectorMUHaltEncConstW solMUReplStaticCfg w j → ∀ t ∈
      Icc (selectorMUInterReadStart j) (selectorMUNextWriteStart j),
      (∫ τ in (selectorMUInterReadStart j)..t,
        selectorMUHoffIntegrandP sol w τ) ≤
        capLeft w j + env.capMid w j + capRight w j := by
  intro w j henc_const t ht
  let f : ℝ → ℝ := fun τ => selectorMUHoffIntegrandP sol w τ
  have hf_cont : Continuous f := by
    simpa [f] using selectorMUHoffIntegrandP_continuous (sol := sol) w
  have hI : ∀ x y : ℝ, IntervalIntegrable f MeasureTheory.volume x y :=
    fun x y => hf_cont.intervalIntegrable x y
  have hmid := selectorMUHoff_middle_offphase_of_envelopeP
    (sol := sol) hA hcμ boxInputs env
  have hmid_nonneg : 0 ≤ env.capMid w j := by
    have h := env.henvInt w j (selectorMUZOffStart j)
      ⟨le_rfl, selectorMUZOffStart_le_zOffEnd j⟩
    simpa [selectorMUHoffMiddleEnvelopeP] using h
  have hright_nonneg : 0 ≤ capRight w j := by
    have h := hcapRight w j henc_const (selectorMUZOffEnd j)
      ⟨le_rfl, selectorMUZOffEnd_le_nextWriteStart j⟩
    simpa [f] using h
  change (∫ τ in (selectorMUInterReadStart j)..t, f τ) ≤
    capLeft w j + env.capMid w j + capRight w j
  by_cases ht_left : t ≤ selectorMUZOffStart j
  · have hleft := hcapLeft w j t ⟨ht.1, ht_left⟩
    have hleft' : (∫ τ in (selectorMUInterReadStart j)..t, f τ) ≤ capLeft w j := by
      simpa [f] using hleft
    linarith
  · have hb_t : selectorMUZOffStart j ≤ t := le_of_not_ge ht_left
    by_cases ht_mid : t ≤ selectorMUZOffEnd j
    · have hleft := hcapLeft w j (selectorMUZOffStart j)
        ⟨selectorMUInterReadStart_le_zOffStart j, le_rfl⟩
      have hleft' :
          (∫ τ in (selectorMUInterReadStart j)..(selectorMUZOffStart j), f τ) ≤
            capLeft w j := by
        simpa [f] using hleft
      have hmid_t := hmid w j t ⟨hb_t, ht_mid⟩
      have hmid_t' :
          (∫ τ in (selectorMUZOffStart j)..t, f τ) ≤ env.capMid w j := by
        simpa [f] using hmid_t
      have hadd := intervalIntegral.integral_add_adjacent_intervals
        (hI (selectorMUInterReadStart j) (selectorMUZOffStart j))
        (hI (selectorMUZOffStart j) t)
      calc
        (∫ τ in (selectorMUInterReadStart j)..t, f τ)
            = (∫ τ in (selectorMUInterReadStart j)..(selectorMUZOffStart j), f τ) +
              (∫ τ in (selectorMUZOffStart j)..t, f τ) := by
                exact hadd.symm
        _ ≤ capLeft w j + env.capMid w j := add_le_add hleft' hmid_t'
        _ ≤ capLeft w j + env.capMid w j + capRight w j := by linarith
    · have hc_t : selectorMUZOffEnd j ≤ t := le_of_not_ge ht_mid
      have hleft := hcapLeft w j (selectorMUZOffStart j)
        ⟨selectorMUInterReadStart_le_zOffStart j, le_rfl⟩
      have hleft' :
          (∫ τ in (selectorMUInterReadStart j)..(selectorMUZOffStart j), f τ) ≤
            capLeft w j := by
        simpa [f] using hleft
      have hmid_full := hmid w j (selectorMUZOffEnd j)
        ⟨selectorMUZOffStart_le_zOffEnd j, le_rfl⟩
      have hmid_full' :
          (∫ τ in (selectorMUZOffStart j)..(selectorMUZOffEnd j), f τ) ≤
            env.capMid w j := by
        simpa [f] using hmid_full
      have hright := hcapRight w j henc_const t ⟨hc_t, ht.2⟩
      have hright' :
          (∫ τ in (selectorMUZOffEnd j)..t, f τ) ≤ capRight w j := by
        simpa [f] using hright
      have hadd_ab_bc := intervalIntegral.integral_add_adjacent_intervals
        (hI (selectorMUInterReadStart j) (selectorMUZOffStart j))
        (hI (selectorMUZOffStart j) (selectorMUZOffEnd j))
      have hadd_ac_ct := intervalIntegral.integral_add_adjacent_intervals
        (hI (selectorMUInterReadStart j) (selectorMUZOffEnd j))
        (hI (selectorMUZOffEnd j) t)
      have hdecomp_ac :
          (∫ τ in (selectorMUInterReadStart j)..(selectorMUZOffEnd j), f τ) =
            (∫ τ in (selectorMUInterReadStart j)..(selectorMUZOffStart j), f τ) +
            (∫ τ in (selectorMUZOffStart j)..(selectorMUZOffEnd j), f τ) := by
        exact hadd_ab_bc.symm
      calc
        (∫ τ in (selectorMUInterReadStart j)..t, f τ)
            = (∫ τ in (selectorMUInterReadStart j)..(selectorMUZOffEnd j), f τ) +
              (∫ τ in (selectorMUZOffEnd j)..t, f τ) := by
                exact hadd_ac_ct.symm
        _ = ((∫ τ in (selectorMUInterReadStart j)..(selectorMUZOffStart j), f τ) +
              (∫ τ in (selectorMUZOffStart j)..(selectorMUZOffEnd j), f τ)) +
              (∫ τ in (selectorMUZOffEnd j)..t, f τ) := by
                rw [hdecomp_ac]
        _ ≤ (capLeft w j + env.capMid w j) + capRight w j :=
              add_le_add (add_le_add hleft' hmid_full') hright'
        _ = capLeft w j + env.capMid w j + capRight w j := by ring

/-- P-generic split residual with the middle field discharged by the envelope. -/
structure SelectorMUHoffSplitMiddleEnvelopeResidualP
    {p : DynGateParams}
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamilyP p eta heta Mcy κ₀ g₀) where
  capLeft : ℕ → ℕ → ℝ
  capRight : ℕ → ℕ → ℝ
  env : SelectorMUHoffMiddleEnvelopeResidualP p
  hcapLeft : ∀ w j, ∀ t ∈ Icc (selectorMUInterReadStart j) (selectorMUZOffStart j),
    (∫ τ in (selectorMUInterReadStart j)..t,
      selectorMUHoffIntegrandP sol w τ) ≤ capLeft w j
  hcapRight : ∀ w j, selectorMUHaltEncConstW solMUReplStaticCfg w j → ∀ t ∈
      Icc (selectorMUZOffEnd j) (selectorMUNextWriteStart j),
    (∫ τ in (selectorMUZOffEnd j)..t,
      selectorMUHoffIntegrandP sol w τ) ≤ capRight w j
  hsplitInt : ∀ w j, selectorMUHaltEncConstW solMUReplStaticCfg w j → ∀ t ∈
      Icc (selectorMUInterReadStart j)
      (selectorMUNextWriteStart j),
    (∫ τ in (selectorMUInterReadStart j)..t,
      selectorMUHoffIntegrandP sol w τ) ≤ capLeft w j + env.capMid w j + capRight w j
  hsum_le : ∀ w j, selectorMUHaltEncConstW solMUReplStaticCfg w j →
    capLeft w j + env.capMid w j + capRight w j ≤ selectorReplicatorHoldEnvelope j

namespace SelectorMUHoffSplitMiddleEnvelopeResidualP

/-- Fill the P-generic split field-integral residual from the middle envelope. -/
def toSplitFieldIntegralResidual
    {p : DynGateParams}
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamilyP p eta heta Mcy κ₀ g₀}
    (res : SelectorMUHoffSplitMiddleEnvelopeResidualP sol)
    (hA : 0 ≤ p.A) (hcμ : 0 ≤ p.cμ)
    (boxInputs : MUReplicatorBoxInputsP p eta heta Mcy κ₀ g₀ sol) :
    SelectorMUHoffSplitFieldIntegralResidualP sol where
  capLeft := res.capLeft
  capMid := res.env.capMid
  capRight := res.capRight
  hcapLeft := res.hcapLeft
  hoffMid := selectorMUHoff_middle_offphase_of_envelopeP hA hcμ boxInputs res.env
  hcapRight := res.hcapRight
  hsplitInt := res.hsplitInt
  hsum_le := res.hsum_le

/-- Directly forget to the P-generic full inter-read field-integral residual. -/
def toFieldIntegralResidual
    {p : DynGateParams}
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamilyP p eta heta Mcy κ₀ g₀}
    (res : SelectorMUHoffSplitMiddleEnvelopeResidualP sol)
    (hA : 0 ≤ p.A) (hcμ : 0 ≤ p.cμ)
    (boxInputs : MUReplicatorBoxInputsP p eta heta Mcy κ₀ g₀ sol) :
    SelectorMUHoffFieldIntegralResidualP sol :=
  (res.toSplitFieldIntegralResidual hA hcμ boxInputs).toFieldIntegralResidual

end SelectorMUHoffSplitMiddleEnvelopeResidualP

/-- P-generic no-split residual with middle offphase derived, not carried. -/
structure SelectorMUHoffSplitMiddleEnvelopeNoSplitResidualP
    {p : DynGateParams}
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamilyP p eta heta Mcy κ₀ g₀) where
  capLeft : ℕ → ℕ → ℝ
  capRight : ℕ → ℕ → ℝ
  env : SelectorMUHoffMiddleEnvelopeResidualP p
  hcapLeft : ∀ w j, ∀ t ∈ Icc (selectorMUInterReadStart j) (selectorMUZOffStart j),
    (∫ τ in (selectorMUInterReadStart j)..t,
      selectorMUHoffIntegrandP sol w τ) ≤ capLeft w j
  hcapRight : ∀ w j, selectorMUHaltEncConstW solMUReplStaticCfg w j → ∀ t ∈
      Icc (selectorMUZOffEnd j) (selectorMUNextWriteStart j),
    (∫ τ in (selectorMUZOffEnd j)..t,
      selectorMUHoffIntegrandP sol w τ) ≤ capRight w j
  hsum_le : ∀ w j, selectorMUHaltEncConstW solMUReplStaticCfg w j →
    capLeft w j + env.capMid w j + capRight w j ≤ selectorReplicatorHoldEnvelope j

namespace SelectorMUHoffSplitMiddleEnvelopeNoSplitResidualP

/-- Fill the P-generic split-middle residual by deriving the full split integral. -/
def toSplitMiddleEnvelopeResidual
    {p : DynGateParams}
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamilyP p eta heta Mcy κ₀ g₀}
    (res : SelectorMUHoffSplitMiddleEnvelopeNoSplitResidualP sol)
    (hA : 0 ≤ p.A) (hcμ : 0 ≤ p.cμ)
    (boxInputs : MUReplicatorBoxInputsP p eta heta Mcy κ₀ g₀ sol) :
    SelectorMUHoffSplitMiddleEnvelopeResidualP sol where
  capLeft := res.capLeft
  capRight := res.capRight
  env := res.env
  hcapLeft := res.hcapLeft
  hcapRight := res.hcapRight
  hsplitInt :=
    selectorMUHoff_hsplitInt_of_capsP hA hcμ boxInputs res.env res.hcapLeft
      res.hcapRight
  hsum_le := res.hsum_le

/-- Directly forget to the P-generic full inter-read field-integral residual. -/
def toFieldIntegralResidual
    {p : DynGateParams}
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamilyP p eta heta Mcy κ₀ g₀}
    (res : SelectorMUHoffSplitMiddleEnvelopeNoSplitResidualP sol)
    (hA : 0 ≤ p.A) (hcμ : 0 ≤ p.cμ)
    (boxInputs : MUReplicatorBoxInputsP p eta heta Mcy κ₀ g₀ sol) :
    SelectorMUHoffFieldIntegralResidualP sol :=
  (res.toSplitMiddleEnvelopeResidual hA hcμ boxInputs).toFieldIntegralResidual
    hA hcμ boxInputs

end SelectorMUHoffSplitMiddleEnvelopeNoSplitResidualP

/-- P-generic no-split `hoff` residual with left/right z-gate cap inputs. -/
structure SelectorMUHoffSplitMiddleEnvelopeGateCapNoSplitResidualP
    {p : DynGateParams}
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamilyP p eta heta Mcy κ₀ g₀) where
  capLeft : ℕ → ℕ → ℝ
  capRight : ℕ → ℕ → ℝ
  env : SelectorMUHoffMiddleEnvelopeResidualP p
  hcapLeftGate : ∀ w j, ∀ t ∈ Icc (selectorMUInterReadStart j)
      (selectorMUZOffStart j),
    (∫ τ in (selectorMUInterReadStart j)..t,
      selectorMUHoffGateCoeffP sol w τ) ≤ capLeft w j
  hcapRightGate : ∀ w j, selectorMUHaltEncConstW solMUReplStaticCfg w j → ∀ t ∈
      Icc (selectorMUZOffEnd j)
      (selectorMUNextWriteStart j),
    (∫ τ in (selectorMUZOffEnd j)..t,
      selectorMUHoffGateCoeffP sol w τ) ≤ capRight w j
  hsum_le : ∀ w j, selectorMUHaltEncConstW solMUReplStaticCfg w j →
    capLeft w j + env.capMid w j + capRight w j ≤ selectorReplicatorHoldEnvelope j

namespace SelectorMUHoffSplitMiddleEnvelopeGateCapNoSplitResidualP

/-- Convert P-generic gate-coefficient cap inputs to the no-split residual. -/
def toNoSplitResidual
    {p : DynGateParams}
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamilyP p eta heta Mcy κ₀ g₀}
    (res : SelectorMUHoffSplitMiddleEnvelopeGateCapNoSplitResidualP sol)
    (hA : 0 ≤ p.A)
    (boxInputs : MUReplicatorBoxInputsP p eta heta Mcy κ₀ g₀ sol) :
    SelectorMUHoffSplitMiddleEnvelopeNoSplitResidualP sol where
  capLeft := res.capLeft
  capRight := res.capRight
  env := res.env
  hcapLeft := selectorMUHoff_hcapLeft_of_gateP hA boxInputs res.hcapLeftGate
  hcapRight := selectorMUHoff_hcapRight_of_gateP hA boxInputs res.hcapRightGate
  hsum_le := res.hsum_le

end SelectorMUHoffSplitMiddleEnvelopeGateCapNoSplitResidualP

section ArbitraryPSentinels

variable {p : DynGateParams}
variable {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
variable {sol : MUReplicatorSolFamilyP p eta heta Mcy κ₀ g₀}
variable (hA : 0 ≤ p.A) (hcμ : 0 ≤ p.cμ)
variable (boxInputs : MUReplicatorBoxInputsP p eta heta Mcy κ₀ g₀ sol)

example (w : ℕ) :
    Continuous fun τ : ℝ => selectorMUHoffIntegrandP (p := p) sol w τ :=
  selectorMUHoffIntegrandP_continuous (sol := sol) w

example (w : ℕ) :
    Continuous fun τ : ℝ => selectorMUHoffGateCoeffP (p := p) sol w τ :=
  selectorMUHoffGateCoeffP_continuous (sol := sol) w

example (res : SelectorMUHoffFieldIntegralResidualP (p := p) sol) :
    ∀ w j, selectorMUHaltEncConstW solMUReplStaticCfg w j → ∀ t ∈
        Icc (selectorMUInterReadStart j) (selectorMUNextWriteStart j),
      |(sol w).z t haltCoordU -
        (sol w).z (selectorMUInterReadStart j) haltCoordU| ≤
        selectorReplicatorHoldEnvelope j :=
  SelectorMUHoffFieldIntegralResidualP.p_hoff res

example (res : SelectorMUHoffSplitFieldIntegralResidualP (p := p) sol) :
    SelectorMUHoffFieldIntegralResidualP (p := p) sol :=
  res.toFieldIntegralResidual

example (env : SelectorMUHoffMiddleEnvelopeResidualP p) :
    ∀ w j, ∀ t ∈ Icc (selectorMUZOffStart j) (selectorMUZOffEnd j),
      (∫ τ in (selectorMUZOffStart j)..t,
        selectorMUHoffIntegrandP (p := p) sol w τ) ≤ env.capMid w j :=
  selectorMUHoff_middle_offphase_of_envelopeP hA hcμ boxInputs env

example
    {capLeft capRight : ℕ → ℕ → ℝ}
    (env : SelectorMUHoffMiddleEnvelopeResidualP p)
    (hcapLeft : ∀ w j, ∀ t ∈ Icc (selectorMUInterReadStart j) (selectorMUZOffStart j),
      (∫ τ in (selectorMUInterReadStart j)..t,
        selectorMUHoffIntegrandP (p := p) sol w τ) ≤ capLeft w j)
    (hcapRight : ∀ w j, selectorMUHaltEncConstW solMUReplStaticCfg w j → ∀ t ∈
      Icc (selectorMUZOffEnd j) (selectorMUNextWriteStart j),
      (∫ τ in (selectorMUZOffEnd j)..t,
        selectorMUHoffIntegrandP (p := p) sol w τ) ≤ capRight w j) :
    ∀ w j, selectorMUHaltEncConstW solMUReplStaticCfg w j → ∀ t ∈
      Icc (selectorMUInterReadStart j) (selectorMUNextWriteStart j),
      (∫ τ in (selectorMUInterReadStart j)..t,
        selectorMUHoffIntegrandP (p := p) sol w τ) ≤
        capLeft w j + env.capMid w j + capRight w j :=
  selectorMUHoff_hsplitInt_of_capsP hA hcμ boxInputs env hcapLeft hcapRight

example (res : SelectorMUHoffSplitMiddleEnvelopeResidualP (p := p) sol) :
    SelectorMUHoffSplitFieldIntegralResidualP (p := p) sol :=
  res.toSplitFieldIntegralResidual hA hcμ boxInputs

example (res : SelectorMUHoffSplitMiddleEnvelopeResidualP (p := p) sol) :
    SelectorMUHoffFieldIntegralResidualP (p := p) sol :=
  res.toFieldIntegralResidual hA hcμ boxInputs

example (res : SelectorMUHoffSplitMiddleEnvelopeNoSplitResidualP (p := p) sol) :
    SelectorMUHoffSplitMiddleEnvelopeResidualP (p := p) sol :=
  res.toSplitMiddleEnvelopeResidual hA hcμ boxInputs

example (res : SelectorMUHoffSplitMiddleEnvelopeNoSplitResidualP (p := p) sol) :
    SelectorMUHoffFieldIntegralResidualP (p := p) sol :=
  res.toFieldIntegralResidual hA hcμ boxInputs

example (res : SelectorMUHoffSplitMiddleEnvelopeGateCapNoSplitResidualP (p := p) sol) :
    SelectorMUHoffSplitMiddleEnvelopeNoSplitResidualP (p := p) sol :=
  res.toNoSplitResidual hA boxInputs

end ArbitraryPSentinels

end Ripple.BoundedUniversality.BGP
