/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Ripple.LPP.SynPPKurtz
import Ripple.CTMC.FrozenGeneratorSkeletonBound

/-!
# Kurtz's law of large numbers on a finite horizon

Kurtz, "Solutions of ordinary differential equations as limits of pure jump Markov
processes", J. Appl. Prob. 7 (1970), Theorem 3.1; Ethier–Kurtz, *Markov Processes*, Ch. 11,
Theorem 2.1: for a density-dependent family of CTMCs with locally Lipschitz drift `F`, if the
initial densities converge to `x₀` and the solution `x(t)` of `ẋ = F(x)`, `x(0) = x₀` stays in
the domain on `[0, T]`, then `sup_{t ≤ T} ‖X̄^N(t) − x(t)‖ → 0` in probability.

`kurtz_finite_horizon` proves this for the canonical density-dependent CTMC
`DensityDepCTMC.mk N hN Γ` of a finite rate specification `Γ` on the lattice cube, with
deterministic initial states within `1/N` of `x₀`.  Its hypotheses are model conditions of the
lattice chain (conservative jumps; jumps leaving the lattice have rate zero at simplex states),
the domain condition `‖x(t)‖ ≤ 1`, and
regularity of `x`.  The Doob L² maximal inequality, carried as `FrozenDoobL2` by
`kurtz_finite_horizon_generic`, is proved here from the model conditions
(`frozenDoobL2_of_boundaryCompatible`), and the quadratic-variation rate bound is
`RateSpec.exists_instantQVRate_bound_uniform`.
-/

namespace Ripple
namespace Kurtz

open MeasureTheory

variable {d : ℕ}

/-- On the simplex, boundary compatibility makes the drift vanish at every absorbing lattice
state (an absorbing state has zero exit rate, hence zero generator drift, and the generator drift
equals the rate-specification drift on the simplex). -/
theorem driftZeroAtAbsorbingOnSimplex_of_boundaryCompatible (M : CTMC.DensityDepCTMC d)
    (hBC : M.BoundaryCompatibleOnSimplex) : M.DriftZeroAtAbsorbingOnSimplex := by
  intro x hx hexit
  change M.rateSpec.drift (M.scaledState x) = 0
  rw [← M.generatorDrift_eq_rateSpec_drift_of_boundaryCompatibleOnSimplex hBC hx]
  funext i
  exact M.generatorDrift_eq_zero_of_exitRateAt_zero
    (by simpa [CTMC.DensityDepCTMC.exitRateAt] using hexit) i

/-- **Doob's L² maximal inequality for the frozen canonical martingale**, for every rate
specification whose lattice chains are conservative and boundary compatible on the simplex. -/
theorem frozenDoobL2_of_boundaryCompatible [NeZero d] (Γ : RateSpec d)
    (hcons : ∀ (N : ℕ) (hN : 0 < N), (CTMC.DensityDepCTMC.mk N hN Γ).ConservativeJumps)
    (hBC : ∀ (N : ℕ) (hN : 0 < N),
      (CTMC.DensityDepCTMC.mk N hN Γ).BoundaryCompatibleOnSimplex) :
    FrozenDoobL2 Γ (CTMC.DensityDepCTMC.frozenMartingalePartDoobL2Constant d) := by
  intro N hN x₀ hinit T hT
  let M : CTMC.DensityDepCTMC d := CTMC.DensityDepCTMC.mk N hN Γ
  have heq :=
    M.canonical_frozenMartingalePart_eq_frozenGeneratorMartingalePart_ae
      x₀ (hcons N hN) hinit (hBC N hN)
  have hgenerator := Ripple.CTMC.frozenGeneratorMP_skeleton_bound_ae M x₀ hinit hT
  have hbridge : ∀ᵐ records ∂M.canonicalRecordMeasure x₀,
      ∃ n, (⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
        ‖M.frozenMartingalePart M.canonicalPathMap s records‖ ^ 2) ≤
      (4 / 3 : ℝ) * M.frozenClockSkeletonSupSq T n records +
        4 * M.frozenTruncatedJumpSqSum T n records := by
    filter_upwards [heq, hgenerator] with records heq_records hgenerator_records
    obtain ⟨n, hn⟩ := hgenerator_records
    refine ⟨n, ?_⟩
    simpa only [heq_records] using hn
  exact M.frozenMartingalePart_DoobL2_of_skeleton_bound_ae
    x₀ hinit hT hbridge
    (fun n => M.frozenClockTruncatedQVIntegralSum_le_frozenQV_setIntegral
      x₀ hinit T hT n)

/-- **Kurtz's law of large numbers on `[0, T]`** (Kurtz 1970, Thm 3.1), for canonical
density-dependent CTMCs: for every `ε, η > 0` there is `N₀` such that for every `N ≥ N₀` and
every simplex initial state within `1/N` of `x₀`,
`P(sup_{0 ≤ t ≤ T} ‖X̄^N(t) − x(t)‖ > ε) ≤ η`. -/
theorem kurtz_finite_horizon [NeZero d]
    (Γ : RateSpec d) (mf : MeanFieldSolution d Γ)
    (hConservative : ∀ (N : ℕ) (hN : 0 < N),
      (CTMC.DensityDepCTMC.mk N hN Γ).ConservativeJumps)
    (hBoundary : ∀ (N : ℕ) (hN : 0 < N),
      (CTMC.DensityDepCTMC.mk N hN Γ).BoundaryCompatibleOnSimplex)
    (hSolBound : ∀ t : ℝ, 0 ≤ t → ‖mf.sol t‖ ≤ 1)
    (hSolMeas : Measurable mf.sol)
    (hSolDriftInt : ∀ i : Fin d, ∀ {t : ℝ}, 0 ≤ t →
      IntervalIntegrable
        (fun s : ℝ => (Γ.drift (mf.sol s)) i)
        MeasureTheory.volume (0 : ℝ) t)
    {T : ℝ} (hT : 0 < T) (ε : ℝ) (hε : 0 < ε) (η : ℝ) (hη : 0 < η) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (hN : 0 < N)
    (x₀ : Fin d → Fin (N + 1))
    (hinit : (CTMC.DensityDepCTMC.mk N hN Γ).InSimplex x₀)
    (_hinit_close :
      ‖(fun i => (↑(x₀ i) : ℝ) / ↑N) - mf.x₀‖ ≤ 1 / ↑N),
    (CTMC.DensityDepCTMC.mk N hN Γ).canonicalRecordMeasure x₀
      {ω | ⨆ (t : ℝ) (_ : 0 ≤ t ∧ t ≤ T),
        ‖((CTMC.DensityDepCTMC.mk N hN Γ).toFrozenDensityProcess x₀
            (driftZeroAtAbsorbingOnSimplex_of_boundaryCompatible _ (hBoundary N hN))
            (hConservative N hN) hinit).process t ω -
          mf.sol t‖ > ε} ≤ ENNReal.ofReal η :=
  kurtz_finite_horizon_generic Γ mf
    (fun N hN => driftZeroAtAbsorbingOnSimplex_of_boundaryCompatible _ (hBoundary N hN))
    hConservative hSolBound hSolMeas
    hSolDriftInt (CTMC.DensityDepCTMC.frozenMartingalePartDoobL2Constant_pos d)
    (frozenDoobL2_of_boundaryCompatible Γ hConservative hBoundary)
    (Γ.exists_instantQVRate_bound_uniform) hT ε hε η hη

end Kurtz
end Ripple
