import Ripple.BoundedUniversality.BGP.SelectorReplicatorExistence
import Ripple.BoundedUniversality.BGP.SelectorReplicatorConc
import Ripple.BoundedUniversality.BGP.SelectorReplicatorHeadline
import Ripple.BoundedUniversality.BGP.SelectorZWriteDischarge
import Ripple.BoundedUniversality.BGP.BGPParams38

/-!
Ripple.BoundedUniversality.BGP.SelectorReplicatorHStart
------------------------------------
F1 sibling port: discharge the per-cycle post-write `z` read for the
replicator selector solution, modulo the honest simultaneous-induction inputs.

This file deliberately avoids a shared-core refactor.  The only copied surface
is the part that is independent of the logistic `lam_hasDeriv`: branch-diagonal
mix-close and write-Reach composition for `SelectorReplicatorDynSol`.
-/

noncomputable section

open Filter
open scoped BigOperators Topology

namespace Ripple.BoundedUniversality.BGP

open Set MachineInstance

/-- The post-write read time used by the end-to-end headline:
`2πj + 5π/6`. -/
def selectorMUWriteReadTime (j : ℕ) : ℝ :=
  (2 : ℝ) * Real.pi * (j : ℝ) + (5 : ℝ) * Real.pi / 6

/-- Explicit F1 start radius:
`exp(-Λ j) * Bz0 j + δw j + (εmix j + mult * ρu j)`.

The first two terms are the z-write Reach error; the last parenthesis is the
write-time mix-close error from replicator concentration plus branch diagonal
and the carried config tube. -/
def selectorReplicatorHStartRho
    (Λ Bz0 δw εmix ρu : ℕ → ℝ) (mult : ℝ) (j : ℕ) : ℝ :=
  Real.exp (-(Λ j)) * Bz0 j + δw j + (εmix j + mult * ρu j)

theorem selectorReplicatorHStartRho_tendsto_zero
    {Λ Bz0 δw εmix ρu : ℕ → ℝ} {mult : ℝ}
    (hwrite : Tendsto (fun j => Real.exp (-(Λ j)) * Bz0 j) atTop (𝓝 0))
    (hδw : Tendsto δw atTop (𝓝 0))
    (hεmix : Tendsto εmix atTop (𝓝 0))
    (hρu : Tendsto ρu atTop (𝓝 0)) :
    Tendsto (selectorReplicatorHStartRho Λ Bz0 δw εmix ρu mult) atTop (𝓝 0) := by
  simpa [selectorReplicatorHStartRho] using
    (hwrite.add hδw).add (hεmix.add (Filter.Tendsto.const_mul mult hρu))

/-- Replicator sibling of `selector_MU_hMnext`, with a variable carried tube
radius `ρu` rather than the fixed `r_LE_U`.

The proof is purely algebraic and uses only `z/u/lam`; it is independent of the
selector-weight ODE shape. -/
theorem selector_MU_hMnext_repl
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : SelectorReplicatorDynSol d_U B_U UniversalLocalView bgpParams38 selectorSchedule
      branchU
      (fun t => ((1 + Real.cos t) / 2) ^ Mcy)
      (fun t => ((1 + Real.sin t) / 2) ^ Mcy)
      (fun _ => (κ₀ : ℝ))
      (fun t => (g₀ : ℝ) * Real.exp (bgpParams38.cα * t))
      (universalPval eta heta))
    (c : UConf) (th : ℝ) {εmix mult ρu : ℝ} (hmult0 : 0 ≤ mult)
    (hmultbound : ∀ i, stackMachineEncodingU.coordMultiplier c i ≤ mult)
    (hmix : ∀ i, |selectorMixTarget branchU sol.u sol.lam th i
        - BranchData.evalBranch (branchU (localViewU c)) (sol.u th) i| ≤ εmix)
    (hutube : ∀ i, |sol.u th i - stackMachineEncodingU.enc c i| ≤ ρu) :
    ∀ i, |selectorMixTarget branchU sol.u sol.lam th i
        - stackMachineEncodingU.enc (M_U.step c) i| ≤ εmix + mult * ρu := by
  intro i
  exact mixTarget_near_next hmult0 (hmix i)
    (selector_MU_hdiag c (sol.u th) hmultbound i) (hutube i)

/-- S3-style write-time mix-close for the replicator selector.

This is the direct call to `replicator_mix_error`, specialized to the selector
mixture coordinate at a fixed write/read time `b`.  The branch-diagonal step is
kept separate in `selector_MU_hMnext_repl`, so this theorem only proves that the
live mixture is close to the winning branch value. -/
theorem selector_replicator_mix_close_of_concentration
    {d B : ℕ} {V : Type} [Fintype V] [DecidableEq V] [Nonempty V]
    {p : DynGateParams} {sched : PhaseSchedule} {branch : V → BranchData d B}
    {chiReset chiGate kappa gain : ℝ → ℝ} {readoutP : V → (Fin d → ℝ) → ℝ}
    (sol : SelectorReplicatorDynSol d B V p sched branch
      chiReset chiGate kappa gain readoutP)
    (vstar : V) (i : Fin d) {a b Lmin gap R0 Kreset Rspread : ℝ}
    (hab : a ≤ b)
    (hLmin_pos : 0 < Lmin)
    (hdom : ∀ t ∈ Icc a b, t ∈ sched.domain)
    (hcr_cont : Continuous fun t : ℝ => chiReset t * kappa t)
    (hqL : ∀ t ∈ Icc a b, Lmin ≤ sol.lam vstar t)
    (hlam_nonneg_Icc : ∀ w : V, ∀ t ∈ Icc a b, 0 ≤ sol.lam w t)
    (hsum_b : (∑ w : V, sol.lam w b) = 1)
    (hcr_nonneg : ∀ t ∈ Ico a b, 0 ≤ chiReset t * kappa t)
    (hcg_nonneg : ∀ t ∈ Ico a b, 0 ≤ chiGate t * gain t)
    (hgap : ∀ v : V, v ≠ vstar → ∀ t ∈ Ico a b,
      readoutP v (sol.u t) - readoutP vstar (sol.u t) ≤ -gap)
    (hRa : ∀ v : V, v ≠ vstar → sol.lam v a / sol.lam vstar a ≤ R0)
    (hKreset : (∫ t in a..b,
      Real.exp (gap * (sol.G t - sol.G a)) * (chiReset t * kappa t)) ≤ Kreset)
    (hRspread_nonneg : 0 ≤ Rspread)
    (hspread : ∀ v : V, v ≠ vstar →
      |BranchData.evalBranch (branch v) (sol.u b) i
        - BranchData.evalBranch (branch vstar) (sol.u b) i| ≤ Rspread) :
    |selectorMixTarget branch sol.u sol.lam b i
        - BranchData.evalBranch (branch vstar) (sol.u b) i| ≤
      Rspread * ((Fintype.card V : ℝ) - 1) *
        ((R0 + Kreset / ((Fintype.card V : ℝ) * Lmin))
          * Real.exp (-gap * (sol.G b - sol.G a))) := by
  have hode : ∀ w : V, ∀ t ∈ Ico a b,
      HasDerivAt (sol.lam w)
        ((chiReset t * kappa t) * (1 / (Fintype.card V : ℝ) - sol.lam w t)
          + (chiGate t * gain t) * sol.lam w t *
              (readoutP w (sol.u t)
                - ∑ u : V, sol.lam u t * readoutP u (sol.u t))) t := by
    intro w t ht
    have htIcc : t ∈ Icc a b := Ico_subset_Icc_self ht
    simpa [mul_assoc] using sol.lam_hasDeriv w t (hdom t htIcc)
  have hGder : ∀ t ∈ Ico a b,
      HasDerivWithinAt sol.G (chiGate t * gain t) (Ici t) t := by
    intro t ht
    exact (sol.G_hasDeriv t (hdom t (Ico_subset_Icc_self ht))).hasDerivWithinAt
  have hmix := replicator_mix_error
    (lam := sol.lam)
    (P := fun v t => readoutP v (sol.u t))
    (cr := fun t => chiReset t * kappa t)
    (cg := fun t => chiGate t * gain t)
    (G := sol.G)
    (vstar := vstar)
    (A := fun v => BranchData.evalBranch (branch v) (sol.u b) i)
    hab hLmin_pos sol.cont_G hcr_cont
    (fun w => (sol.cont_lam w).continuousOn) hode hGder hqL
    hlam_nonneg_Icc hsum_b hcr_nonneg hcg_nonneg hgap hRa hKreset
    hRspread_nonneg hspread
  simpa only [selectorMixTarget, selectorF] using hmix

/-- Generic F1 write-time `hstart` for any replicator selector solution.

Inputs carried here are exactly the simultaneous-induction facts that the next
stage should close: finite z-start radius, write-window mix stability, z-write
integral lower bound, write-time replicator mix error, branch multiplier bound,
and the write-time config tube. -/
theorem selector_replicator_hstart_of_writeReach
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : SelectorReplicatorDynSol d_U B_U UniversalLocalView bgpParams38 selectorSchedule
      branchU
      (fun t => ((1 + Real.cos t) / 2) ^ Mcy)
      (fun t => ((1 + Real.sin t) / 2) ^ Mcy)
      (fun _ => (κ₀ : ℝ))
      (fun t => (g₀ : ℝ) * Real.exp (bgpParams38.cα * t))
      (universalPval eta heta))
    (cfg : ℕ → UConf) (hcfg_step : ∀ j, cfg (j + 1) = M_U.step (cfg j))
    (a θ : ℕ → ℝ) (Λ Bz0 δw εmix ρu : ℕ → ℝ) {mult : ℝ}
    (hwrite_le : ∀ j, a j ≤ selectorMUWriteReadTime j)
    (hdom_write : ∀ j, ∀ t ∈ Icc (a j) (selectorMUWriteReadTime j),
      t ∈ selectorSchedule.domain)
    (hgZ_cont : Continuous fun t : ℝ =>
      bgpParams38.A * sol.α t * bGateZ bgpParams38.L (sol.μ t) t)
    (hgZ0 : ∀ j, ∀ t ∈ Icc (a j) (selectorMUWriteReadTime j),
      0 ≤ bgpParams38.A * sol.α t * bGateZ bgpParams38.L (sol.μ t) t)
    (hmix_stable_z_write : ∀ j, ∀ t ∈ Icc (a j) (selectorMUWriteReadTime j),
      |selectorMixTarget branchU sol.u sol.lam t haltCoordU
        - selectorMixTarget branchU sol.u sol.lam (θ j) haltCoordU| ≤ δw j)
    (hz_start_mismatch_bound : ∀ j,
      |sol.z (a j) haltCoordU
        - selectorMixTarget branchU sol.u sol.lam (θ j) haltCoordU| ≤ Bz0 j)
    (hwriteInt_lbd_z : ∀ j,
      Λ j ≤ ∫ τ in (a j)..(selectorMUWriteReadTime j),
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
      |sol.z (selectorMUWriteReadTime j) haltCoordU
        - stackMachineEncodingU.enc (cfg (j + 1)) haltCoordU| ≤
          selectorReplicatorHStartRho Λ Bz0 δw εmix ρu mult j := by
  intro j
  have hzh_zero : ∀ t ∈ Icc (selectorMUWriteReadTime j) (selectorMUWriteReadTime j),
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
    selector_MU_hMnext_repl sol (cfg j) (θ j)
      (ρu := ρu j) hmult0 (hmultbound j) (hmix j) (hutube j) haltCoordU
  have hMnext :
      |selectorMixTarget branchU sol.u sol.lam (θ j) haltCoordU
        - stackMachineEncodingU.enc (cfg (j + 1)) haltCoordU|
          ≤ εmix j + mult * ρu j := by
    simpa [hcfg_step j] using hMnext_step
  calc
    |sol.z (selectorMUWriteReadTime j) haltCoordU
        - stackMachineEncodingU.enc (cfg (j + 1)) haltCoordU|
        ≤ |sol.z (selectorMUWriteReadTime j) haltCoordU
            - selectorMixTarget branchU sol.u sol.lam (θ j) haltCoordU|
          + |selectorMixTarget branchU sol.u sol.lam (θ j) haltCoordU
            - stackMachineEncodingU.enc (cfg (j + 1)) haltCoordU| := abs_sub_le _ _ _
    _ ≤ (Real.exp (-(Λ j)) * Bz0 j + δw j) + (εmix j + mult * ρu j) :=
      add_le_add hzM hMnext
    _ = selectorReplicatorHStartRho Λ Bz0 δw εmix ρu mult j := by
      rw [selectorReplicatorHStartRho]

/-- All-coordinate sibling of `selector_replicator_hstart_of_writeReach`.

The proof is the same write-Reach composition, with the coordinate kept as a
parameter instead of being specialized to `haltCoordU`. -/
theorem selector_replicator_hstart_allCoord_of_writeReach
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : SelectorReplicatorDynSol d_U B_U UniversalLocalView bgpParams38 selectorSchedule
      branchU
      (fun t => ((1 + Real.cos t) / 2) ^ Mcy)
      (fun t => ((1 + Real.sin t) / 2) ^ Mcy)
      (fun _ => (κ₀ : ℝ))
      (fun t => (g₀ : ℝ) * Real.exp (bgpParams38.cα * t))
      (universalPval eta heta))
    (cfg : ℕ → UConf) (hcfg_step : ∀ j, cfg (j + 1) = M_U.step (cfg j))
    (a θ : ℕ → ℝ) (Λ Bz0 δw εmix ρu : ℕ → ℝ) {mult : ℝ}
    (hwrite_le : ∀ j, a j ≤ selectorMUWriteReadTime j)
    (hdom_write : ∀ j, ∀ t ∈ Icc (a j) (selectorMUWriteReadTime j),
      t ∈ selectorSchedule.domain)
    (hgZ_cont : Continuous fun t : ℝ =>
      bgpParams38.A * sol.α t * bGateZ bgpParams38.L (sol.μ t) t)
    (hgZ0 : ∀ j, ∀ t ∈ Icc (a j) (selectorMUWriteReadTime j),
      0 ≤ bgpParams38.A * sol.α t * bGateZ bgpParams38.L (sol.μ t) t)
    (hmix_stable_z_write : ∀ j, ∀ i, ∀ t ∈ Icc (a j) (selectorMUWriteReadTime j),
      |selectorMixTarget branchU sol.u sol.lam t i
        - selectorMixTarget branchU sol.u sol.lam (θ j) i| ≤ δw j)
    (hz_start_mismatch_bound : ∀ j, ∀ i,
      |sol.z (a j) i
        - selectorMixTarget branchU sol.u sol.lam (θ j) i| ≤ Bz0 j)
    (hwriteInt_lbd_z : ∀ j,
      Λ j ≤ ∫ τ in (a j)..(selectorMUWriteReadTime j),
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
      |sol.z (selectorMUWriteReadTime j) i
        - stackMachineEncodingU.enc (cfg (j + 1)) i| ≤
          selectorReplicatorHStartRho Λ Bz0 δw εmix ρu mult j := by
  intro j i
  have hzh_zero : ∀ t ∈ Icc (selectorMUWriteReadTime j) (selectorMUWriteReadTime j),
      |sol.z t i - sol.z (selectorMUWriteReadTime j) i| ≤ (0 : ℝ) := by
    intro t ht
    have ht_eq : t = selectorMUWriteReadTime j := le_antisymm ht.2 ht.1
    simp [ht_eq]
  have hz_after :=
    z_after_write_bound_repl
      (sol := sol) (s := i)
      (a := a j) (m := selectorMUWriteReadTime j) (b := selectorMUWriteReadTime j)
      (M := selectorMixTarget branchU sol.u sol.lam (θ j) i)
      (δw := δw j) (δzh := 0)
      (hwrite_le j) (hdom_write j) hgZ_cont (hgZ0 j)
      (hmix_stable_z_write j i) hzh_zero
  have hzM_raw :
      |sol.z (selectorMUWriteReadTime j) i
        - selectorMixTarget branchU sol.u sol.lam (θ j) i| ≤
        0 + (Real.exp (-(∫ τ in (a j)..(selectorMUWriteReadTime j),
          bgpParams38.A * sol.α τ * bGateZ bgpParams38.L (sol.μ τ) τ)) *
            |sol.z (a j) i
              - selectorMixTarget branchU sol.u sol.lam (θ j) i| + δw j) :=
    hz_after (selectorMUWriteReadTime j) ⟨le_rfl, le_rfl⟩
  have hctr :
      Real.exp (-(∫ τ in (a j)..(selectorMUWriteReadTime j),
            bgpParams38.A * sol.α τ * bGateZ bgpParams38.L (sol.μ τ) τ)) *
          |sol.z (a j) i
            - selectorMixTarget branchU sol.u sol.lam (θ j) i|
        ≤ Real.exp (-(Λ j)) * Bz0 j :=
    exp_neg_mul_abs_le_exp_neg_lbd_mul (hwriteInt_lbd_z j)
      (hz_start_mismatch_bound j i)
  have hzM :
      |sol.z (selectorMUWriteReadTime j) i
        - selectorMixTarget branchU sol.u sol.lam (θ j) i| ≤
          Real.exp (-(Λ j)) * Bz0 j + δw j := by
    linarith
  have hMnext_step :=
    selector_MU_hMnext_repl sol (cfg j) (θ j)
      (ρu := ρu j) hmult0 (hmultbound j) (hmix j) (hutube j) i
  have hMnext :
      |selectorMixTarget branchU sol.u sol.lam (θ j) i
        - stackMachineEncodingU.enc (cfg (j + 1)) i|
          ≤ εmix j + mult * ρu j := by
    simpa [hcfg_step j] using hMnext_step
  calc
    |sol.z (selectorMUWriteReadTime j) i
        - stackMachineEncodingU.enc (cfg (j + 1)) i|
        ≤ |sol.z (selectorMUWriteReadTime j) i
            - selectorMixTarget branchU sol.u sol.lam (θ j) i|
          + |selectorMixTarget branchU sol.u sol.lam (θ j) i
            - stackMachineEncodingU.enc (cfg (j + 1)) i| := abs_sub_le _ _ _
    _ ≤ (Real.exp (-(Λ j)) * Bz0 j + δw j) + (εmix j + mult * ρu j) :=
      add_le_add hzM hMnext
    _ = selectorReplicatorHStartRho Λ Bz0 δw εmix ρu mult j := by
      rw [selectorReplicatorHStartRho]

/-- F1 wrapper for the constructed `solMURepl` family.  The solution remains
opaque (`solMURepl` is irreducible); all analytic inputs are passed through the
generic sibling-port theorem above. -/
theorem solMURepl_hstart
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
    (Λ Bz0 δw εmix ρu : ℕ → ℕ → ℝ) {mult : ℝ}
    (hwrite_le : ∀ w j, a w j ≤ selectorMUWriteReadTime j)
    (hdom_write : ∀ w j, ∀ t ∈ Icc (a w j) (selectorMUWriteReadTime j),
      t ∈ selectorSchedule.domain)
    (hgZ_cont : ∀ w, Continuous fun t : ℝ =>
      bgpParams38.A *
        (solMURepl eta heta Mcy κ₀ g₀ HP Kq R selectorInitX0 hfin hgateZ hgateU
          h_chiReset h_chiGate h_kappa h_gain h_P w).α t *
          bGateZ bgpParams38.L
            ((solMURepl eta heta Mcy κ₀ g₀ HP Kq R selectorInitX0 hfin hgateZ hgateU
              h_chiReset h_chiGate h_kappa h_gain h_P w).μ t) t)
    (hgZ0 : ∀ w j, ∀ t ∈ Icc (a w j) (selectorMUWriteReadTime j),
      0 ≤ bgpParams38.A *
        (solMURepl eta heta Mcy κ₀ g₀ HP Kq R selectorInitX0 hfin hgateZ hgateU
          h_chiReset h_chiGate h_kappa h_gain h_P w).α t *
          bGateZ bgpParams38.L
            ((solMURepl eta heta Mcy κ₀ g₀ HP Kq R selectorInitX0 hfin hgateZ hgateU
              h_chiReset h_chiGate h_kappa h_gain h_P w).μ t) t)
    (hmix_stable_z_write : ∀ w j, ∀ t ∈ Icc (a w j) (selectorMUWriteReadTime j),
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
    (hmult0 : 0 ≤ mult)
    (hmultbound : ∀ w j, ∀ i,
      stackMachineEncodingU.coordMultiplier (M_U.step^[j] (M_U.init w)) i ≤ mult)
    (hmix : ∀ w j, ∀ i,
      |selectorMixTarget branchU
          (solMURepl eta heta Mcy κ₀ g₀ HP Kq R selectorInitX0 hfin hgateZ hgateU
            h_chiReset h_chiGate h_kappa h_gain h_P w).u
          (solMURepl eta heta Mcy κ₀ g₀ HP Kq R selectorInitX0 hfin hgateZ hgateU
            h_chiReset h_chiGate h_kappa h_gain h_P w).lam
          (θ w j) i
        - BranchData.evalBranch
            (branchU (localViewU (M_U.step^[j] (M_U.init w))))
            ((solMURepl eta heta Mcy κ₀ g₀ HP Kq R selectorInitX0 hfin hgateZ hgateU
              h_chiReset h_chiGate h_kappa h_gain h_P w).u (θ w j)) i|
          ≤ εmix w j)
    (hutube : ∀ w j, ∀ i,
      |(solMURepl eta heta Mcy κ₀ g₀ HP Kq R selectorInitX0 hfin hgateZ hgateU
          h_chiReset h_chiGate h_kappa h_gain h_P w).u (θ w j) i
        - stackMachineEncodingU.enc (M_U.step^[j] (M_U.init w)) i| ≤ ρu w j) :
    ∀ w j,
      |(solMURepl eta heta Mcy κ₀ g₀ HP Kq R selectorInitX0 hfin hgateZ hgateU
          h_chiReset h_chiGate h_kappa h_gain h_P w).z
            (selectorMUWriteReadTime j) haltCoordU
        - stackMachineEncodingU.enc (M_U.step^[j + 1] (M_U.init w)) haltCoordU| ≤
          selectorReplicatorHStartRho (Λ w) (Bz0 w) (δw w) (εmix w) (ρu w) mult j := by
  intro w j
  let solw :=
    solMURepl eta heta Mcy κ₀ g₀ HP Kq R selectorInitX0 hfin hgateZ hgateU
      h_chiReset h_chiGate h_kappa h_gain h_P w
  let cfg : ℕ → UConf := fun n => M_U.step^[n] (M_U.init w)
  have hcfg_step : ∀ n, cfg (n + 1) = M_U.step (cfg n) := by
    intro n
    simp [cfg, Function.iterate_succ_apply']
  have h := selector_replicator_hstart_of_writeReach
    (sol := solw) (cfg := cfg) hcfg_step
    (a := a w) (θ := θ w) (Λ := Λ w) (Bz0 := Bz0 w) (δw := δw w)
    (εmix := εmix w) (ρu := ρu w) (mult := mult)
    (hwrite_le w) (hdom_write w) (hgZ_cont w) (hgZ0 w)
    (hmix_stable_z_write w) (hz_start_mismatch_bound w) (hwriteInt_lbd_z w)
    hmult0 (hmultbound w) (hmix w) (hutube w) j
  simpa [solw, cfg] using h

#print axioms selectorReplicatorHStartRho_tendsto_zero
#print axioms selector_MU_hMnext_repl
#print axioms selector_replicator_mix_close_of_concentration
#print axioms selector_replicator_hstart_of_writeReach
#print axioms solMURepl_hstart

end Ripple.BoundedUniversality.BGP
