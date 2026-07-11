import Ripple.BoundedUniversality.BGP.SelectorReplicatorHStart
import Ripple.BoundedUniversality.BGP.SelectorStackGrowthActual
import Ripple.BoundedUniversality.BGP.SelectorDuhamelWrite
import Ripple.BoundedUniversality.BGP.BGPParams38

/-!
Ripple.BoundedUniversality.BGP.SelectorReplicatorHStartHaltExact
---------------------------------------------

Halt-coordinate-specific mix-to-next theorem that DROPS the `mult * ρu` term.

The escape from the B^N/N ∀w obstruction: at the halt coordinate,
`branchU_haltCoord_exact_independent` shows the branch evaluation is
a CONSTANT (0 or 1), independent of the analog input vector. Therefore
the mix-to-next error at haltCoord = pure λ-concentration error (εmix)
with NO `mult * ρu` contribution.

This means the halt-coordinate headline does NOT need:
- hutube_write (full u-tube at all coords)
- hρu → 0 (vanishing u-tube radius)
- The full exposure-weighted stack tracking

It needs ONLY:
- λ-concentration (gate sharpening → εmix → 0)
- z-contraction at haltCoord (ODE toward constant mix target)
- z box at haltCoord (∈ [0, 1], from hw_unit already proved)
-/

noncomputable section

namespace Ripple.BoundedUniversality.BGP

open MachineInstance UniversalMachine

/-- **Halt-coordinate mix-to-next: ZERO u-tube penalty.**

At the halt coordinate, `branchU_haltCoord_exact_independent` gives
`evalBranch(branchU(localViewU c), Z, haltCoordU) = enc(step c, haltCoordU)`
for ANY Z. So the triangle inequality through the winning branch gives:

  |mixTarget(th, haltCoord) - enc(step c, haltCoord)|
    ≤ |mixTarget - evalBranch(correct)| + |evalBranch(correct) - enc(step c)|
    = εmix + 0 = εmix

No `mult * ρu` term appears because the second triangle term is exactly zero. -/
theorem selector_MU_hMnext_haltExact
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : SelectorReplicatorDynSol d_U B_U UniversalLocalView bgpParams38 selectorSchedule
      branchU
      (fun t => ((1 + Real.cos t) / 2) ^ Mcy)
      (fun t => ((1 + Real.sin t) / 2) ^ Mcy)
      (fun _ => (κ₀ : ℝ))
      (fun t => (g₀ : ℝ) * Real.exp (bgpParams38.cα * t))
      (universalPval eta heta))
    (c : UConf) (th : ℝ) {εmix : ℝ}
    (hmix : |selectorMixTarget branchU sol.u sol.lam th haltCoordU
        - BranchData.evalBranch (branchU (localViewU c)) (sol.u th) haltCoordU| ≤ εmix) :
    |selectorMixTarget branchU sol.u sol.lam th haltCoordU
        - stackMachineEncodingU.enc (M_U.step c) haltCoordU| ≤ εmix := by
  have hexact := branchU_haltCoord_exact_independent c (sol.u th)
  calc |selectorMixTarget branchU sol.u sol.lam th haltCoordU
          - stackMachineEncodingU.enc (M_U.step c) haltCoordU|
      = |selectorMixTarget branchU sol.u sol.lam th haltCoordU
          - BranchData.evalBranch (branchU (localViewU c)) (sol.u th) haltCoordU| := by
        congr 1; rw [hexact]
    _ ≤ εmix := hmix

/-- Same for ctrl coordinate (multiplier also = 0). -/
theorem selector_MU_hMnext_ctrlExact
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : SelectorReplicatorDynSol d_U B_U UniversalLocalView bgpParams38 selectorSchedule
      branchU
      (fun t => ((1 + Real.cos t) / 2) ^ Mcy)
      (fun t => ((1 + Real.sin t) / 2) ^ Mcy)
      (fun _ => (κ₀ : ℝ))
      (fun t => (g₀ : ℝ) * Real.exp (bgpParams38.cα * t))
      (universalPval eta heta))
    (c : UConf) (th : ℝ) {εmix : ℝ}
    (hmix : |selectorMixTarget branchU sol.u sol.lam th ctrlCoordU
        - BranchData.evalBranch (branchU (localViewU c)) (sol.u th) ctrlCoordU| ≤ εmix) :
    |selectorMixTarget branchU sol.u sol.lam th ctrlCoordU
        - stackMachineEncodingU.enc (M_U.step c) ctrlCoordU| ≤ εmix := by
  have hexact := branchU_ctrlCoord_exact_independent c (sol.u th)
  calc |selectorMixTarget branchU sol.u sol.lam th ctrlCoordU
          - stackMachineEncodingU.enc (M_U.step c) ctrlCoordU|
      = |selectorMixTarget branchU sol.u sol.lam th ctrlCoordU
          - BranchData.evalBranch (branchU (localViewU c)) (sol.u th) ctrlCoordU| := by
        congr 1; rw [hexact]
    _ ≤ εmix := hmix

#print axioms selector_MU_hMnext_haltExact
#print axioms selector_MU_hMnext_ctrlExact

/-- Halt-coordinate start radius with no carried `u`-tube contribution. -/
def selectorReplicatorHStartRhoHalt
    (Λ Bz0 δw εmix : ℕ → ℝ) (j : ℕ) : ℝ :=
  Real.exp (-(Λ j)) * Bz0 j + δw j + εmix j

theorem selectorReplicatorHStartRhoHalt_tendsto_zero
    {Λ Bz0 δw εmix : ℕ → ℝ}
    (hwrite : Filter.Tendsto (fun j => Real.exp (-(Λ j)) * Bz0 j)
      Filter.atTop (nhds 0))
    (hδw : Filter.Tendsto δw Filter.atTop (nhds 0))
    (hεmix : Filter.Tendsto εmix Filter.atTop (nhds 0)) :
    Filter.Tendsto (selectorReplicatorHStartRhoHalt Λ Bz0 δw εmix)
      Filter.atTop (nhds 0) := by
  simpa [selectorReplicatorHStartRhoHalt] using (hwrite.add hδw).add hεmix

/-- Halt-coordinate hstart from write Reach and halt-exact mix-to-next.

Compared with `selector_replicator_hstart_of_writeReach`, this drops both the
carried `u`-tube and the `mult * ρu` term.  The only mix-to-next input is the
halt-coordinate mixture error at the frozen write sample.
-/
theorem selector_replicator_hstart_haltExact_of_writeReach
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : SelectorReplicatorDynSol d_U B_U UniversalLocalView bgpParams38 selectorSchedule
      branchU
      (fun t => ((1 + Real.cos t) / 2) ^ Mcy)
      (fun t => ((1 + Real.sin t) / 2) ^ Mcy)
      (fun _ => (κ₀ : ℝ))
      (fun t => (g₀ : ℝ) * Real.exp (bgpParams38.cα * t))
      (universalPval eta heta))
    (cfg : ℕ → UConf) (hcfg_step : ∀ j, cfg (j + 1) = M_U.step (cfg j))
    (a θ : ℕ → ℝ) (Λ Bz0 δw εmix : ℕ → ℝ)
    (hwrite_le : ∀ j, a j ≤ selectorMUWriteReadTime j)
    (hdom_write : ∀ j, ∀ t ∈ Set.Icc (a j) (selectorMUWriteReadTime j),
      t ∈ selectorSchedule.domain)
    (hgZ_cont : Continuous fun t : ℝ =>
      bgpParams38.A * sol.α t * bGateZ bgpParams38.L (sol.μ t) t)
    (hgZ0 : ∀ j, ∀ t ∈ Set.Icc (a j) (selectorMUWriteReadTime j),
      0 ≤ bgpParams38.A * sol.α t * bGateZ bgpParams38.L (sol.μ t) t)
    (hmix_stable_z_write : ∀ j, ∀ t ∈ Set.Icc (a j) (selectorMUWriteReadTime j),
      |selectorMixTarget branchU sol.u sol.lam t haltCoordU
        - selectorMixTarget branchU sol.u sol.lam (θ j) haltCoordU| ≤ δw j)
    (hz_start_mismatch_bound : ∀ j,
      |sol.z (a j) haltCoordU
        - selectorMixTarget branchU sol.u sol.lam (θ j) haltCoordU| ≤ Bz0 j)
    (hwriteInt_lbd_z : ∀ j,
      Λ j ≤ ∫ τ in (a j)..(selectorMUWriteReadTime j),
        bgpParams38.A * sol.α τ * bGateZ bgpParams38.L (sol.μ τ) τ)
    (hmix_halt : ∀ j,
      |selectorMixTarget branchU sol.u sol.lam (θ j) haltCoordU
        - BranchData.evalBranch (branchU (localViewU (cfg j))) (sol.u (θ j)) haltCoordU|
          ≤ εmix j) :
    ∀ j,
      |sol.z (selectorMUWriteReadTime j) haltCoordU
        - stackMachineEncodingU.enc (cfg (j + 1)) haltCoordU| ≤
          selectorReplicatorHStartRhoHalt Λ Bz0 δw εmix j := by
  intro j
  have hzh_zero : ∀ t ∈ Set.Icc (selectorMUWriteReadTime j) (selectorMUWriteReadTime j),
      |sol.z t haltCoordU - sol.z (selectorMUWriteReadTime j) haltCoordU| ≤ (0 : ℝ) := by
    intro t ht
    have ht_eq : t = selectorMUWriteReadTime j := le_antisymm ht.2 ht.1
    simp [ht_eq]
  have hz_after :=
    z_after_write_bound_repl
      (sol := sol) (s := haltCoordU)
      (a := a j) (m := selectorMUWriteReadTime j) (b := selectorMUWriteReadTime j)
      (M := selectorMixTarget branchU sol.u sol.lam (θ j) haltCoordU)
      (δw := δw j) (δzh := 0)
      (hwrite_le j) (hdom_write j) hgZ_cont (hgZ0 j)
      (hmix_stable_z_write j) hzh_zero
  have hzM_raw :
      |sol.z (selectorMUWriteReadTime j) haltCoordU
        - selectorMixTarget branchU sol.u sol.lam (θ j) haltCoordU| ≤
        0 + (Real.exp (-(∫ τ in (a j)..(selectorMUWriteReadTime j),
          bgpParams38.A * sol.α τ * bGateZ bgpParams38.L (sol.μ τ) τ)) *
            |sol.z (a j) haltCoordU
              - selectorMixTarget branchU sol.u sol.lam (θ j) haltCoordU| + δw j) :=
    hz_after (selectorMUWriteReadTime j) ⟨le_rfl, le_rfl⟩
  have hctr :
      Real.exp (-(∫ τ in (a j)..(selectorMUWriteReadTime j),
            bgpParams38.A * sol.α τ * bGateZ bgpParams38.L (sol.μ τ) τ)) *
          |sol.z (a j) haltCoordU
            - selectorMixTarget branchU sol.u sol.lam (θ j) haltCoordU|
        ≤ Real.exp (-(Λ j)) * Bz0 j :=
    exp_neg_mul_abs_le_exp_neg_lbd_mul (hwriteInt_lbd_z j)
      (hz_start_mismatch_bound j)
  have hzM :
      |sol.z (selectorMUWriteReadTime j) haltCoordU
        - selectorMixTarget branchU sol.u sol.lam (θ j) haltCoordU| ≤
          Real.exp (-(Λ j)) * Bz0 j + δw j := by
    linarith
  have hMnext_step :=
    selector_MU_hMnext_haltExact sol (cfg j) (θ j) (hmix_halt j)
  have hMnext :
      |selectorMixTarget branchU sol.u sol.lam (θ j) haltCoordU
        - stackMachineEncodingU.enc (cfg (j + 1)) haltCoordU|
          ≤ εmix j := by
    simpa [hcfg_step j] using hMnext_step
  calc
    |sol.z (selectorMUWriteReadTime j) haltCoordU
        - stackMachineEncodingU.enc (cfg (j + 1)) haltCoordU|
        ≤ |sol.z (selectorMUWriteReadTime j) haltCoordU
            - selectorMixTarget branchU sol.u sol.lam (θ j) haltCoordU|
          + |selectorMixTarget branchU sol.u sol.lam (θ j) haltCoordU
            - stackMachineEncodingU.enc (cfg (j + 1)) haltCoordU| := abs_sub_le _ _ _
    _ ≤ (Real.exp (-(Λ j)) * Bz0 j + δw j) + εmix j :=
      add_le_add hzM hMnext
    _ = selectorReplicatorHStartRhoHalt Λ Bz0 δw εmix j := by
      rw [selectorReplicatorHStartRhoHalt]

/-- Halt-coordinate write-reach endpoint with a variable terminal time.

This is the same contraction estimate as
`selector_replicator_hstart_haltExact_of_writeReach`, but the write endpoint is
an arbitrary `m j` instead of `selectorMUWriteReadTime j`.  It is used for the
next-cycle write-hold endpoint in the settled residual interface. -/
theorem selector_replicator_haltExact_endpoint_of_writeReach
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : SelectorReplicatorDynSol d_U B_U UniversalLocalView bgpParams38 selectorSchedule
      branchU
      (fun t => ((1 + Real.cos t) / 2) ^ Mcy)
      (fun t => ((1 + Real.sin t) / 2) ^ Mcy)
      (fun _ => (κ₀ : ℝ))
      (fun t => (g₀ : ℝ) * Real.exp (bgpParams38.cα * t))
      (universalPval eta heta))
    (cfg : ℕ → UConf) (hcfg_step : ∀ j, cfg (j + 1) = M_U.step (cfg j))
    (a θ m : ℕ → ℝ) (Λ Bz0 δw εmix : ℕ → ℝ)
    (ham : ∀ j, a j ≤ m j)
    (hdom_write : ∀ j, ∀ t ∈ Set.Icc (a j) (m j),
      t ∈ selectorSchedule.domain)
    (hgZ_cont : Continuous fun t : ℝ =>
      bgpParams38.A * sol.α t * bGateZ bgpParams38.L (sol.μ t) t)
    (hgZ0 : ∀ j, ∀ t ∈ Set.Icc (a j) (m j),
      0 ≤ bgpParams38.A * sol.α t * bGateZ bgpParams38.L (sol.μ t) t)
    (hmix_stable_z_write : ∀ j, ∀ t ∈ Set.Icc (a j) (m j),
      |selectorMixTarget branchU sol.u sol.lam t haltCoordU
        - selectorMixTarget branchU sol.u sol.lam (θ j) haltCoordU| ≤ δw j)
    (hz_start_mismatch_bound : ∀ j,
      |sol.z (a j) haltCoordU
        - selectorMixTarget branchU sol.u sol.lam (θ j) haltCoordU| ≤ Bz0 j)
    (hwriteInt_lbd_z : ∀ j,
      Λ j ≤ ∫ τ in (a j)..(m j),
        bgpParams38.A * sol.α τ * bGateZ bgpParams38.L (sol.μ τ) τ)
    (hmix_halt : ∀ j,
      |selectorMixTarget branchU sol.u sol.lam (θ j) haltCoordU
        - BranchData.evalBranch (branchU (localViewU (cfg j))) (sol.u (θ j)) haltCoordU|
          ≤ εmix j) :
    ∀ j,
      |sol.z (m j) haltCoordU
        - stackMachineEncodingU.enc (cfg (j + 1)) haltCoordU| ≤
          selectorReplicatorHStartRhoHalt Λ Bz0 δw εmix j := by
  intro j
  have hzh_zero : ∀ t ∈ Set.Icc (m j) (m j),
      |sol.z t haltCoordU - sol.z (m j) haltCoordU| ≤ (0 : ℝ) := by
    intro t ht
    have ht_eq : t = m j := le_antisymm ht.2 ht.1
    simp [ht_eq]
  have hz_after :=
    z_after_write_bound_repl
      (sol := sol) (s := haltCoordU)
      (a := a j) (m := m j) (b := m j)
      (M := selectorMixTarget branchU sol.u sol.lam (θ j) haltCoordU)
      (δw := δw j) (δzh := 0)
      (ham j) (hdom_write j) hgZ_cont (hgZ0 j)
      (hmix_stable_z_write j) hzh_zero
  have hzM_raw :
      |sol.z (m j) haltCoordU
        - selectorMixTarget branchU sol.u sol.lam (θ j) haltCoordU| ≤
        0 + (Real.exp (-(∫ τ in (a j)..(m j),
          bgpParams38.A * sol.α τ * bGateZ bgpParams38.L (sol.μ τ) τ)) *
            |sol.z (a j) haltCoordU
              - selectorMixTarget branchU sol.u sol.lam (θ j) haltCoordU| + δw j) :=
    hz_after (m j) ⟨le_rfl, le_rfl⟩
  have hctr :
      Real.exp (-(∫ τ in (a j)..(m j),
            bgpParams38.A * sol.α τ * bGateZ bgpParams38.L (sol.μ τ) τ)) *
          |sol.z (a j) haltCoordU
            - selectorMixTarget branchU sol.u sol.lam (θ j) haltCoordU|
        ≤ Real.exp (-(Λ j)) * Bz0 j :=
    exp_neg_mul_abs_le_exp_neg_lbd_mul (hwriteInt_lbd_z j)
      (hz_start_mismatch_bound j)
  have hzM :
      |sol.z (m j) haltCoordU
        - selectorMixTarget branchU sol.u sol.lam (θ j) haltCoordU| ≤
          Real.exp (-(Λ j)) * Bz0 j + δw j := by
    linarith
  have hMnext_step :=
    selector_MU_hMnext_haltExact sol (cfg j) (θ j) (hmix_halt j)
  have hMnext :
      |selectorMixTarget branchU sol.u sol.lam (θ j) haltCoordU
        - stackMachineEncodingU.enc (cfg (j + 1)) haltCoordU|
          ≤ εmix j := by
    simpa [hcfg_step j] using hMnext_step
  calc
    |sol.z (m j) haltCoordU
        - stackMachineEncodingU.enc (cfg (j + 1)) haltCoordU|
        ≤ |sol.z (m j) haltCoordU
            - selectorMixTarget branchU sol.u sol.lam (θ j) haltCoordU|
          + |selectorMixTarget branchU sol.u sol.lam (θ j) haltCoordU
            - stackMachineEncodingU.enc (cfg (j + 1)) haltCoordU| := abs_sub_le _ _ _
    _ ≤ (Real.exp (-(Λ j)) * Bz0 j + δw j) + εmix j :=
      add_le_add hzM hMnext
    _ = selectorReplicatorHStartRhoHalt Λ Bz0 δw εmix j := by
      rw [selectorReplicatorHStartRhoHalt]

/-- Halt-coordinate write-reach endpoint with a weighted moving-target error.

This is the same endpoint as
`selector_replicator_haltExact_endpoint_of_writeReach`, but it uses the sharp
Duhamel-weighted target variation instead of a uniform frozen-mix bound on the
whole write window.
-/
theorem selector_replicator_haltExact_endpoint_of_writeReach_weighted
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : SelectorReplicatorDynSol d_U B_U UniversalLocalView bgpParams38 selectorSchedule
      branchU
      (fun t => ((1 + Real.cos t) / 2) ^ Mcy)
      (fun t => ((1 + Real.sin t) / 2) ^ Mcy)
      (fun _ => (κ₀ : ℝ))
      (fun t => (g₀ : ℝ) * Real.exp (bgpParams38.cα * t))
      (universalPval eta heta))
    (cfg : ℕ → UConf) (hcfg_step : ∀ j, cfg (j + 1) = M_U.step (cfg j))
    (a θ m : ℕ → ℝ) (Λ Bz0 δw εmix : ℕ → ℝ)
    (ham : ∀ j, a j ≤ m j)
    (hdom_write : ∀ j, ∀ t ∈ Set.Icc (a j) (m j),
      t ∈ selectorSchedule.domain)
    (hgZ_cont : Continuous fun t : ℝ =>
      bgpParams38.A * sol.α t * bGateZ bgpParams38.L (sol.μ t) t)
    (hgZ0 : ∀ j, ∀ t ∈ Set.Icc (a j) (m j),
      0 ≤ bgpParams38.A * sol.α t * bGateZ bgpParams38.L (sol.μ t) t)
    (hmix_weighted_z_write : ∀ j,
      (∫ τ in (a j)..(m j),
        Real.exp (-(∫ σ in τ..(m j),
          bgpParams38.A * sol.α σ * bGateZ bgpParams38.L (sol.μ σ) σ)) *
        (bgpParams38.A * sol.α τ * bGateZ bgpParams38.L (sol.μ τ) τ) *
        |selectorMixTarget branchU sol.u sol.lam τ haltCoordU -
          selectorMixTarget branchU sol.u sol.lam (θ j) haltCoordU|) ≤ δw j)
    (hz_start_mismatch_bound : ∀ j,
      |sol.z (a j) haltCoordU
        - selectorMixTarget branchU sol.u sol.lam (θ j) haltCoordU| ≤ Bz0 j)
    (hwriteInt_lbd_z : ∀ j,
      Λ j ≤ ∫ τ in (a j)..(m j),
        bgpParams38.A * sol.α τ * bGateZ bgpParams38.L (sol.μ τ) τ)
    (hmix_halt : ∀ j,
      |selectorMixTarget branchU sol.u sol.lam (θ j) haltCoordU
        - BranchData.evalBranch (branchU (localViewU (cfg j))) (sol.u (θ j)) haltCoordU|
          ≤ εmix j) :
    ∀ j,
      |sol.z (m j) haltCoordU
        - stackMachineEncodingU.enc (cfg (j + 1)) haltCoordU| ≤
          selectorReplicatorHStartRhoHalt Λ Bz0 δw εmix j := by
  intro j
  let kfun : ℝ → ℝ := fun t =>
    bgpParams38.A * sol.α t * bGateZ bgpParams38.L (sol.μ t) t
  let mfun : ℝ → ℝ := fun t =>
    selectorMixTarget branchU sol.u sol.lam t haltCoordU
  let Mtarget : ℝ := selectorMixTarget branchU sol.u sol.lam (θ j) haltCoordU
  have hm_cont : Continuous mfun := by
    simpa [mfun] using sol.cont_mixTarget haltCoordU
  have hy_ode : ∀ t ∈ Set.Icc (a j) (m j),
      HasDerivAt (fun τ => sol.z τ haltCoordU)
        (kfun t * (mfun t - sol.z t haltCoordU)) t := by
    intro t ht
    simpa [kfun, mfun] using sol.z_hasDeriv t (hdom_write j t ht) haltCoordU
  have hscalar := stack_write_gronwall_weighted_bound
    (fun t => sol.z t haltCoordU) mfun kfun Mtarget (a j) (m j)
    (ham j) (by simpa [kfun] using hgZ_cont)
    (by intro t ht; simpa [kfun] using hgZ0 j t ht)
    hm_cont hy_ode
  have hscalar_expanded :
      |sol.z (m j) haltCoordU - Mtarget| ≤
        Real.exp (-(∫ τ in (a j)..(m j),
          bgpParams38.A * sol.α τ * bGateZ bgpParams38.L (sol.μ τ) τ)) *
          |sol.z (a j) haltCoordU - Mtarget| +
        (∫ τ in (a j)..(m j),
          Real.exp (-(∫ σ in τ..(m j),
            bgpParams38.A * sol.α σ * bGateZ bgpParams38.L (sol.μ σ) σ)) *
          (bgpParams38.A * sol.α τ * bGateZ bgpParams38.L (sol.μ τ) τ) *
          |selectorMixTarget branchU sol.u sol.lam τ haltCoordU - Mtarget|) := by
    simpa [kfun, mfun, Mtarget] using hscalar
  have hctr :
      Real.exp (-(∫ τ in (a j)..(m j),
            bgpParams38.A * sol.α τ * bGateZ bgpParams38.L (sol.μ τ) τ)) *
          |sol.z (a j) haltCoordU
            - selectorMixTarget branchU sol.u sol.lam (θ j) haltCoordU|
        ≤ Real.exp (-(Λ j)) * Bz0 j :=
    exp_neg_mul_abs_le_exp_neg_lbd_mul (hwriteInt_lbd_z j)
      (hz_start_mismatch_bound j)
  have hweighted :
      (∫ τ in (a j)..(m j),
        Real.exp (-(∫ σ in τ..(m j),
          bgpParams38.A * sol.α σ * bGateZ bgpParams38.L (sol.μ σ) σ)) *
        (bgpParams38.A * sol.α τ * bGateZ bgpParams38.L (sol.μ τ) τ) *
        |selectorMixTarget branchU sol.u sol.lam τ haltCoordU - Mtarget|) ≤ δw j := by
    simpa [Mtarget] using hmix_weighted_z_write j
  have hzM :
      |sol.z (m j) haltCoordU
        - selectorMixTarget branchU sol.u sol.lam (θ j) haltCoordU| ≤
          Real.exp (-(Λ j)) * Bz0 j + δw j := by
    simpa [Mtarget] using
      hscalar_expanded.trans (add_le_add hctr hweighted)
  have hMnext_step :=
    selector_MU_hMnext_haltExact sol (cfg j) (θ j) (hmix_halt j)
  have hMnext :
      |selectorMixTarget branchU sol.u sol.lam (θ j) haltCoordU
        - stackMachineEncodingU.enc (cfg (j + 1)) haltCoordU|
          ≤ εmix j := by
    simpa [hcfg_step j] using hMnext_step
  calc
    |sol.z (m j) haltCoordU
        - stackMachineEncodingU.enc (cfg (j + 1)) haltCoordU|
        ≤ |sol.z (m j) haltCoordU
            - selectorMixTarget branchU sol.u sol.lam (θ j) haltCoordU|
          + |selectorMixTarget branchU sol.u sol.lam (θ j) haltCoordU
            - stackMachineEncodingU.enc (cfg (j + 1)) haltCoordU| := abs_sub_le _ _ _
    _ ≤ (Real.exp (-(Λ j)) * Bz0 j + δw j) + εmix j :=
      add_le_add hzM hMnext
    _ = selectorReplicatorHStartRhoHalt Λ Bz0 δw εmix j := by
      rw [selectorReplicatorHStartRhoHalt]

/-- Weighted write-reach endpoint for an arbitrary coordinate.

This is the coordinate-generic analogue of
`selector_replicator_haltExact_endpoint_of_writeReach_weighted`.  Since general
coordinates do not have halt-coordinate exactness, the last mix-to-next step
uses `selector_MU_hMnext_repl` and the radius includes `mult * ρu`. -/
theorem selector_replicator_endpoint_coord_of_writeReach_weighted
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : SelectorReplicatorDynSol d_U B_U UniversalLocalView bgpParams38 selectorSchedule
      branchU
      (fun t => ((1 + Real.cos t) / 2) ^ Mcy)
      (fun t => ((1 + Real.sin t) / 2) ^ Mcy)
      (fun _ => (κ₀ : ℝ))
      (fun t => (g₀ : ℝ) * Real.exp (bgpParams38.cα * t))
      (universalPval eta heta))
    (cfg : ℕ → UConf) (hcfg_step : ∀ j, cfg (j + 1) = M_U.step (cfg j))
    (a θ m : ℕ → ℝ) (Λ Bz0 δw εmix ρu : ℕ → ℝ) {mult : ℝ}
    (i : Fin d_U)
    (ham : ∀ j, a j ≤ m j)
    (hdom_write : ∀ j, ∀ t ∈ Set.Icc (a j) (m j),
      t ∈ selectorSchedule.domain)
    (hgZ_cont : Continuous fun t : ℝ =>
      bgpParams38.A * sol.α t * bGateZ bgpParams38.L (sol.μ t) t)
    (hgZ0 : ∀ j, ∀ t ∈ Set.Icc (a j) (m j),
      0 ≤ bgpParams38.A * sol.α t * bGateZ bgpParams38.L (sol.μ t) t)
    (hmix_weighted_z_write : ∀ j,
      (∫ τ in (a j)..(m j),
        Real.exp (-(∫ σ in τ..(m j),
          bgpParams38.A * sol.α σ * bGateZ bgpParams38.L (sol.μ σ) σ)) *
        (bgpParams38.A * sol.α τ * bGateZ bgpParams38.L (sol.μ τ) τ) *
        |selectorMixTarget branchU sol.u sol.lam τ i -
          selectorMixTarget branchU sol.u sol.lam (θ j) i|) ≤ δw j)
    (hz_start_mismatch_bound : ∀ j,
      |sol.z (a j) i
        - selectorMixTarget branchU sol.u sol.lam (θ j) i| ≤ Bz0 j)
    (hwriteInt_lbd_z : ∀ j,
      Λ j ≤ ∫ τ in (a j)..(m j),
        bgpParams38.A * sol.α τ * bGateZ bgpParams38.L (sol.μ τ) τ)
    (hmult0 : 0 ≤ mult)
    (hmultbound : ∀ j, ∀ i, stackMachineEncodingU.coordMultiplier (cfg j) i ≤ mult)
    (hmix : ∀ j, ∀ i,
      |selectorMixTarget branchU sol.u sol.lam (θ j) i
        - BranchData.evalBranch (branchU (localViewU (cfg j))) (sol.u (θ j)) i|
          ≤ εmix j)
    (hutube : ∀ j, ∀ i,
      |sol.u (θ j) i - stackMachineEncodingU.enc (cfg j) i| ≤ ρu j) :
    ∀ j,
      |sol.z (m j) i
        - stackMachineEncodingU.enc (cfg (j + 1)) i| ≤
          selectorReplicatorHStartRho Λ Bz0 δw εmix ρu mult j := by
  intro j
  let kfun : ℝ → ℝ := fun t =>
    bgpParams38.A * sol.α t * bGateZ bgpParams38.L (sol.μ t) t
  let mfun : ℝ → ℝ := fun t =>
    selectorMixTarget branchU sol.u sol.lam t i
  let Mtarget : ℝ := selectorMixTarget branchU sol.u sol.lam (θ j) i
  have hm_cont : Continuous mfun := by
    simpa [mfun] using sol.cont_mixTarget i
  have hy_ode : ∀ t ∈ Set.Icc (a j) (m j),
      HasDerivAt (fun τ => sol.z τ i)
        (kfun t * (mfun t - sol.z t i)) t := by
    intro t ht
    simpa [kfun, mfun] using sol.z_hasDeriv t (hdom_write j t ht) i
  have hscalar := stack_write_gronwall_weighted_bound
    (fun t => sol.z t i) mfun kfun Mtarget (a j) (m j)
    (ham j) (by simpa [kfun] using hgZ_cont)
    (by intro t ht; simpa [kfun] using hgZ0 j t ht)
    hm_cont hy_ode
  have hscalar_expanded :
      |sol.z (m j) i - Mtarget| ≤
        Real.exp (-(∫ τ in (a j)..(m j),
          bgpParams38.A * sol.α τ * bGateZ bgpParams38.L (sol.μ τ) τ)) *
          |sol.z (a j) i - Mtarget| +
        (∫ τ in (a j)..(m j),
          Real.exp (-(∫ σ in τ..(m j),
            bgpParams38.A * sol.α σ * bGateZ bgpParams38.L (sol.μ σ) σ)) *
          (bgpParams38.A * sol.α τ * bGateZ bgpParams38.L (sol.μ τ) τ) *
          |selectorMixTarget branchU sol.u sol.lam τ i - Mtarget|) := by
    simpa [kfun, mfun, Mtarget] using hscalar
  have hctr :
      Real.exp (-(∫ τ in (a j)..(m j),
            bgpParams38.A * sol.α τ * bGateZ bgpParams38.L (sol.μ τ) τ)) *
          |sol.z (a j) i
            - selectorMixTarget branchU sol.u sol.lam (θ j) i|
        ≤ Real.exp (-(Λ j)) * Bz0 j :=
    exp_neg_mul_abs_le_exp_neg_lbd_mul (hwriteInt_lbd_z j)
      (hz_start_mismatch_bound j)
  have hweighted :
      (∫ τ in (a j)..(m j),
        Real.exp (-(∫ σ in τ..(m j),
          bgpParams38.A * sol.α σ * bGateZ bgpParams38.L (sol.μ σ) σ)) *
        (bgpParams38.A * sol.α τ * bGateZ bgpParams38.L (sol.μ τ) τ) *
        |selectorMixTarget branchU sol.u sol.lam τ i - Mtarget|) ≤ δw j := by
    simpa [Mtarget] using hmix_weighted_z_write j
  have hzM :
      |sol.z (m j) i
        - selectorMixTarget branchU sol.u sol.lam (θ j) i| ≤
          Real.exp (-(Λ j)) * Bz0 j + δw j := by
    simpa [Mtarget] using
      hscalar_expanded.trans (add_le_add hctr hweighted)
  have hMnext_step :=
    selector_MU_hMnext_repl sol (cfg j) (θ j)
      (ρu := ρu j) hmult0 (hmultbound j) (hmix j) (hutube j) i
  have hMnext :
      |selectorMixTarget branchU sol.u sol.lam (θ j) i
        - stackMachineEncodingU.enc (cfg (j + 1)) i|
          ≤ εmix j + mult * ρu j := by
    simpa [hcfg_step j] using hMnext_step
  calc
    |sol.z (m j) i
        - stackMachineEncodingU.enc (cfg (j + 1)) i|
        ≤ |sol.z (m j) i
            - selectorMixTarget branchU sol.u sol.lam (θ j) i|
          + |selectorMixTarget branchU sol.u sol.lam (θ j) i
            - stackMachineEncodingU.enc (cfg (j + 1)) i| := abs_sub_le _ _ _
    _ ≤ (Real.exp (-(Λ j)) * Bz0 j + δw j) + (εmix j + mult * ρu j) :=
      add_le_add hzM hMnext
    _ = selectorReplicatorHStartRho Λ Bz0 δw εmix ρu mult j := by
      rw [selectorReplicatorHStartRho]

/-- All-coordinate weighted write-reach endpoint. -/
theorem selector_replicator_endpoint_allCoord_of_writeReach_weighted
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : SelectorReplicatorDynSol d_U B_U UniversalLocalView bgpParams38 selectorSchedule
      branchU
      (fun t => ((1 + Real.cos t) / 2) ^ Mcy)
      (fun t => ((1 + Real.sin t) / 2) ^ Mcy)
      (fun _ => (κ₀ : ℝ))
      (fun t => (g₀ : ℝ) * Real.exp (bgpParams38.cα * t))
      (universalPval eta heta))
    (cfg : ℕ → UConf) (hcfg_step : ∀ j, cfg (j + 1) = M_U.step (cfg j))
    (a θ m : ℕ → ℝ) (Λ Bz0 δw εmix ρu : ℕ → ℝ) {mult : ℝ}
    (ham : ∀ j, a j ≤ m j)
    (hdom_write : ∀ j, ∀ t ∈ Set.Icc (a j) (m j),
      t ∈ selectorSchedule.domain)
    (hgZ_cont : Continuous fun t : ℝ =>
      bgpParams38.A * sol.α t * bGateZ bgpParams38.L (sol.μ t) t)
    (hgZ0 : ∀ j, ∀ t ∈ Set.Icc (a j) (m j),
      0 ≤ bgpParams38.A * sol.α t * bGateZ bgpParams38.L (sol.μ t) t)
    (hmix_weighted_z_write : ∀ j i,
      (∫ τ in (a j)..(m j),
        Real.exp (-(∫ σ in τ..(m j),
          bgpParams38.A * sol.α σ * bGateZ bgpParams38.L (sol.μ σ) σ)) *
        (bgpParams38.A * sol.α τ * bGateZ bgpParams38.L (sol.μ τ) τ) *
        |selectorMixTarget branchU sol.u sol.lam τ i -
          selectorMixTarget branchU sol.u sol.lam (θ j) i|) ≤ δw j)
    (hz_start_mismatch_bound : ∀ j i,
      |sol.z (a j) i
        - selectorMixTarget branchU sol.u sol.lam (θ j) i| ≤ Bz0 j)
    (hwriteInt_lbd_z : ∀ j,
      Λ j ≤ ∫ τ in (a j)..(m j),
        bgpParams38.A * sol.α τ * bGateZ bgpParams38.L (sol.μ τ) τ)
    (hmult0 : 0 ≤ mult)
    (hmultbound : ∀ j, ∀ i, stackMachineEncodingU.coordMultiplier (cfg j) i ≤ mult)
    (hmix : ∀ j, ∀ i,
      |selectorMixTarget branchU sol.u sol.lam (θ j) i
        - BranchData.evalBranch (branchU (localViewU (cfg j))) (sol.u (θ j)) i|
          ≤ εmix j)
    (hutube : ∀ j, ∀ i,
      |sol.u (θ j) i - stackMachineEncodingU.enc (cfg j) i| ≤ ρu j) :
    ∀ j i,
      |sol.z (m j) i
        - stackMachineEncodingU.enc (cfg (j + 1)) i| ≤
          selectorReplicatorHStartRho Λ Bz0 δw εmix ρu mult j := by
  intro j i
  exact selector_replicator_endpoint_coord_of_writeReach_weighted
    (sol := sol) (cfg := cfg) (hcfg_step := hcfg_step)
    (a := a) (θ := θ) (m := m)
    (Λ := Λ) (Bz0 := Bz0) (δw := δw) (εmix := εmix) (ρu := ρu)
    (mult := mult) i ham hdom_write hgZ_cont hgZ0
    (fun k => hmix_weighted_z_write k i)
    (fun k => hz_start_mismatch_bound k i)
    hwriteInt_lbd_z hmult0 hmultbound hmix hutube j

/-- F1 halt-exact wrapper for the constructed `solMURepl` family. -/
theorem solMURepl_hstart_haltExact
    (eta : ℚ) (heta : 0 < eta) (Mcy : ℕ) (κ₀ g₀ : ℚ)
    (HP : MvPolynomial (Fin d_U) ℚ) (Kq : ℚ) (R : ℕ)
    (hfin : ∀ w,
      Ripple.FiniteHorizonBound (selectorMUReplicatorField eta heta Mcy κ₀ g₀ HP Kq R)
        (selectorMUReplicatorInit selectorInitX0 w g₀))
    (hgateZ : ∀ w,
      ∀ y : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        y 0 = selectorMUReplicatorInit selectorInitX0 w g₀ →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y (selectorMUReplicatorField eta heta Mcy κ₀ g₀ HP Kq R (y t)) t) →
        ∀ t : ℝ, 0 ≤ t →
          y t (selOfContract UniversalLocalView (contractGateZ d_U)) =
            bGateZ 1 (y t (selOfContract UniversalLocalView (contractMu d_U))) t)
    (hgateU : ∀ w,
      ∀ y : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        y 0 = selectorMUReplicatorInit selectorInitX0 w g₀ →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y (selectorMUReplicatorField eta heta Mcy κ₀ g₀ HP Kq R (y t)) t) →
        ∀ t : ℝ, 0 ≤ t →
          y t (selOfContract UniversalLocalView (contractGateU d_U)) =
            bGateU 1 (y t (selOfContract UniversalLocalView (contractMu d_U))) t)
    (h_chiReset : ∀ w,
      ∀ y : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        y 0 = selectorMUReplicatorInit selectorInitX0 w g₀ →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y (selectorMUReplicatorField eta heta Mcy κ₀ g₀ HP Kq R (y t)) t) →
        ∀ t : ℝ, 0 ≤ t →
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t)
            (selChiResetPoly d_U UniversalLocalView Mcy) =
              ((1 + Real.cos t) / 2) ^ Mcy)
    (h_chiGate : ∀ w,
      ∀ y : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        y 0 = selectorMUReplicatorInit selectorInitX0 w g₀ →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y (selectorMUReplicatorField eta heta Mcy κ₀ g₀ HP Kq R (y t)) t) →
        ∀ t : ℝ, 0 ≤ t →
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t)
            (selChiGatePoly d_U UniversalLocalView Mcy) =
              ((1 + Real.sin t) / 2) ^ Mcy)
    (h_kappa : ∀ w,
      ∀ y : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        y 0 = selectorMUReplicatorInit selectorInitX0 w g₀ →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y (selectorMUReplicatorField eta heta Mcy κ₀ g₀ HP Kq R (y t)) t) →
        ∀ t : ℝ, 0 ≤ t →
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t)
            (selKappaPoly d_U UniversalLocalView κ₀) = (κ₀ : ℝ))
    (h_gain : ∀ w,
      ∀ y : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        y 0 = selectorMUReplicatorInit selectorInitX0 w g₀ →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y (selectorMUReplicatorField eta heta Mcy κ₀ g₀ HP Kq R (y t)) t) →
        ∀ t : ℝ, 0 ≤ t →
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t)
            (selGainPoly d_U UniversalLocalView) =
              (g₀ : ℝ) * Real.exp (bgpParams38.cα * t))
    (h_P : ∀ w,
      ∀ y : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        y 0 = selectorMUReplicatorInit selectorInitX0 w g₀ →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y (selectorMUReplicatorField eta heta Mcy κ₀ g₀ HP Kq R (y t)) t) →
        ∀ (v : UniversalLocalView) (t : ℝ), 0 ≤ t →
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t)
            ((muReadoutPoly eta heta) v) =
              universalPval eta heta v (fun i => y t (selU UniversalLocalView i)))
    (a θ : ℕ → ℕ → ℝ)
    (Λ Bz0 δw εmix : ℕ → ℕ → ℝ)
    (hwrite_le : ∀ w j, a w j ≤ selectorMUWriteReadTime j)
    (hdom_write : ∀ w j, ∀ t ∈ Set.Icc (a w j) (selectorMUWriteReadTime j),
      t ∈ selectorSchedule.domain)
    (hgZ_cont : ∀ w, Continuous fun t : ℝ =>
      bgpParams38.A *
        (solMURepl eta heta Mcy κ₀ g₀ HP Kq R selectorInitX0 hfin hgateZ hgateU
          h_chiReset h_chiGate h_kappa h_gain h_P w).α t *
          bGateZ bgpParams38.L
            ((solMURepl eta heta Mcy κ₀ g₀ HP Kq R selectorInitX0 hfin hgateZ hgateU
              h_chiReset h_chiGate h_kappa h_gain h_P w).μ t) t)
    (hgZ0 : ∀ w j, ∀ t ∈ Set.Icc (a w j) (selectorMUWriteReadTime j),
      0 ≤ bgpParams38.A *
        (solMURepl eta heta Mcy κ₀ g₀ HP Kq R selectorInitX0 hfin hgateZ hgateU
          h_chiReset h_chiGate h_kappa h_gain h_P w).α t *
          bGateZ bgpParams38.L
            ((solMURepl eta heta Mcy κ₀ g₀ HP Kq R selectorInitX0 hfin hgateZ hgateU
              h_chiReset h_chiGate h_kappa h_gain h_P w).μ t) t)
    (hmix_stable_z_write : ∀ w j,
      ∀ t ∈ Set.Icc (a w j) (selectorMUWriteReadTime j),
        |selectorMixTarget branchU
            (solMURepl eta heta Mcy κ₀ g₀ HP Kq R selectorInitX0 hfin hgateZ hgateU
              h_chiReset h_chiGate h_kappa h_gain h_P w).u
            (solMURepl eta heta Mcy κ₀ g₀ HP Kq R selectorInitX0 hfin hgateZ hgateU
              h_chiReset h_chiGate h_kappa h_gain h_P w).lam
            t haltCoordU
          - selectorMixTarget branchU
            (solMURepl eta heta Mcy κ₀ g₀ HP Kq R selectorInitX0 hfin hgateZ hgateU
              h_chiReset h_chiGate h_kappa h_gain h_P w).u
            (solMURepl eta heta Mcy κ₀ g₀ HP Kq R selectorInitX0 hfin hgateZ hgateU
              h_chiReset h_chiGate h_kappa h_gain h_P w).lam
            (θ w j) haltCoordU| ≤ δw w j)
    (hz_start_mismatch_bound : ∀ w j,
      |(solMURepl eta heta Mcy κ₀ g₀ HP Kq R selectorInitX0 hfin hgateZ hgateU
          h_chiReset h_chiGate h_kappa h_gain h_P w).z (a w j) haltCoordU
        - selectorMixTarget branchU
          (solMURepl eta heta Mcy κ₀ g₀ HP Kq R selectorInitX0 hfin hgateZ hgateU
            h_chiReset h_chiGate h_kappa h_gain h_P w).u
          (solMURepl eta heta Mcy κ₀ g₀ HP Kq R selectorInitX0 hfin hgateZ hgateU
            h_chiReset h_chiGate h_kappa h_gain h_P w).lam
          (θ w j) haltCoordU| ≤ Bz0 w j)
    (hwriteInt_lbd_z : ∀ w j,
      Λ w j ≤ ∫ τ in (a w j)..(selectorMUWriteReadTime j),
        bgpParams38.A *
          (solMURepl eta heta Mcy κ₀ g₀ HP Kq R selectorInitX0 hfin hgateZ hgateU
            h_chiReset h_chiGate h_kappa h_gain h_P w).α τ *
            bGateZ bgpParams38.L
              ((solMURepl eta heta Mcy κ₀ g₀ HP Kq R selectorInitX0 hfin hgateZ hgateU
                h_chiReset h_chiGate h_kappa h_gain h_P w).μ τ) τ)
    (hmix_halt : ∀ w j,
      |selectorMixTarget branchU
          (solMURepl eta heta Mcy κ₀ g₀ HP Kq R selectorInitX0 hfin hgateZ hgateU
            h_chiReset h_chiGate h_kappa h_gain h_P w).u
          (solMURepl eta heta Mcy κ₀ g₀ HP Kq R selectorInitX0 hfin hgateZ hgateU
            h_chiReset h_chiGate h_kappa h_gain h_P w).lam
          (θ w j) haltCoordU
        - BranchData.evalBranch
            (branchU (localViewU (M_U.step^[j] (M_U.init w))))
            ((solMURepl eta heta Mcy κ₀ g₀ HP Kq R selectorInitX0 hfin hgateZ hgateU
              h_chiReset h_chiGate h_kappa h_gain h_P w).u (θ w j))
            haltCoordU| ≤ εmix w j) :
    ∀ w j,
      |(solMURepl eta heta Mcy κ₀ g₀ HP Kq R selectorInitX0 hfin hgateZ hgateU
          h_chiReset h_chiGate h_kappa h_gain h_P w).z
            (selectorMUWriteReadTime j) haltCoordU
        - stackMachineEncodingU.enc (M_U.step^[j + 1] (M_U.init w)) haltCoordU| ≤
          selectorReplicatorHStartRhoHalt (Λ w) (Bz0 w) (δw w) (εmix w) j := by
  intro w j
  let solw :=
    solMURepl eta heta Mcy κ₀ g₀ HP Kq R selectorInitX0 hfin hgateZ hgateU
      h_chiReset h_chiGate h_kappa h_gain h_P w
  let cfg : ℕ → UConf := fun n => M_U.step^[n] (M_U.init w)
  have hcfg_step : ∀ n, cfg (n + 1) = M_U.step (cfg n) := by
    intro n
    simp [cfg, Function.iterate_succ_apply']
  have h := selector_replicator_hstart_haltExact_of_writeReach
    (sol := solw) (cfg := cfg) hcfg_step
    (a := a w) (θ := θ w) (Λ := Λ w) (Bz0 := Bz0 w)
    (δw := δw w) (εmix := εmix w)
    (hwrite_le w) (hdom_write w) (hgZ_cont w) (hgZ0 w)
    (hmix_stable_z_write w) (hz_start_mismatch_bound w)
    (hwriteInt_lbd_z w) (hmix_halt w) j
  simpa [solw, cfg] using h

#print axioms selectorReplicatorHStartRhoHalt_tendsto_zero
#print axioms selector_replicator_hstart_haltExact_of_writeReach
#print axioms selector_replicator_haltExact_endpoint_of_writeReach
#print axioms solMURepl_hstart_haltExact

end Ripple.BoundedUniversality.BGP
