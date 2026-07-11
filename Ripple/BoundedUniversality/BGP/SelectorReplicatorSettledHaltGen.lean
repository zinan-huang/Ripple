import Ripple.BoundedUniversality.BGP.SelectorReplicatorSettledZ
import Ripple.BoundedUniversality.BGP.FlagHmixConstant
import Ripple.BoundedUniversality.BGP.BGPParams38

/-!
# SelectorReplicatorSettledHaltGen

Generalized z-coordinate settled convergence from an ABSTRACT loser-mass
bound `epsLam : ℕ → ℝ`. Decouples from `SelectorReplicatorHaltConcInputs`
(which hardcodes `selectorMUWriteStartTime` in the epsLam formula).

This enables the mid-window anchor approach: the shifted concentration
on `[selectStart, WriteHold]` produces a valid epsLam that tends to zero
but doesn't match the standard formula anchored at WriteStart.
-/

noncomputable section

namespace Ripple.BoundedUniversality.BGP

open MachineInstance UniversalMachine Filter Set
open scoped BigOperators Topology

/-- Generalized z-coordinate settled convergence from abstract loser-mass bound.

The proof follows `solMURepl_settled_hstart_haltOnly` but takes
`epsLam : ℕ → ℝ` as a parameter.  The existing theorem uses
`solMUReplSettledHaltEpsLam inputs w` (which hardcodes `WriteStart`
in the gain integral); this version accepts any epsLam satisfying
`hloser` and `Tendsto epsLam 0`. -/
theorem solMURepl_settled_hstart_gen
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    {cfg : ℕ → UConf}
    (w : ℕ) (hcfg_step : ∀ j, M_U.step (cfg j) = cfg (j + 1))
    (epsLam : ℕ → ℝ)
    (Λ Bz : ℕ → ℝ) (Bzmax : ℝ)
    (hdom_write : ∀ j, ∀ t ∈ Icc (selectorMUWriteHoldTime j)
        (selectorMUWriteReadTime j), t ∈ selectorSchedule.domain)
    (hgZ_cont : Continuous fun t : ℝ =>
      bgpParams38.A * (sol w).α t * bGateZ bgpParams38.L ((sol w).μ t) t)
    (hgZ0 : ∀ j, ∀ t ∈ Icc (selectorMUWriteHoldTime j)
        (selectorMUWriteReadTime j),
      0 ≤ bgpParams38.A * (sol w).α t * bGateZ bgpParams38.L ((sol w).μ t) t)
    (hsum : ∀ j, ∀ t ∈ Icc (selectorMUWriteHoldTime j)
        (selectorMUWriteReadTime j),
      (∑ v : UniversalLocalView, (sol w).lam v t) = 1)
    (hlam_nonneg : ∀ j, ∀ t ∈ Icc (selectorMUWriteHoldTime j)
        (selectorMUWriteReadTime j), ∀ v : UniversalLocalView,
      0 ≤ (sol w).lam v t)
    (hloser : ∀ j, ∀ t ∈ Icc (selectorMUWriteHoldTime j)
        (selectorMUWriteReadTime j),
      (Finset.univ.filter (fun v : UniversalLocalView =>
        v ≠ localViewU (cfg j))).sum (fun v => (sol w).lam v t) ≤ epsLam j)
    (hz_start : ∀ j,
      |(sol w).z (selectorMUWriteHoldTime j) haltCoordU -
        stackMachineEncodingU.enc (cfg (j + 1)) haltCoordU| ≤ Bz j)
    (hΛ_lower : ∀ j,
      Λ j ≤ ∫ τ in selectorMUWriteHoldTime j..selectorMUWriteReadTime j,
        bgpParams38.A * (sol w).α τ * bGateZ bgpParams38.L ((sol w).μ τ) τ)
    (hΛ : Tendsto Λ atTop atTop)
    (hBz_nonneg : ∀ j, 0 ≤ Bz j)
    (hBz_bdd : ∀ᶠ j in atTop, Bz j ≤ Bzmax)
    (hepsLam_nonneg : ∀ j, 0 ≤ epsLam j)
    (hepsLam_tendsto : Tendsto epsLam atTop (𝓝 0)) :
    let delta : ℕ → ℝ := fun j => (Fintype.card UniversalLocalView : ℝ) * epsLam j
    (∀ (j : ℕ),
      |(sol w).z (selectorMUWriteReadTime j) haltCoordU -
        stackMachineEncodingU.enc (cfg (j + 1)) haltCoordU| ≤
          selectorZWriteContraction Λ Bz j + delta j) ∧
    Tendsto (fun j => selectorZWriteContraction Λ Bz j + delta j) atTop (𝓝 0) ∧
    (∀ j, 0 ≤ selectorZWriteContraction Λ Bz j + delta j) := by
  intro delta
  have hδ_tendsto : Tendsto delta atTop (𝓝 0) := by
    simpa [delta] using hepsLam_tendsto.const_mul (Fintype.card UniversalLocalView : ℝ)
  have hctr : Tendsto (selectorZWriteContraction Λ Bz) atTop (𝓝 0) := by
    simpa using solMURepl_expNegLambda_Bz0_tendsto_zero
      (Λ := fun _ : ℕ => Λ) (Bz0 := fun _ : ℕ => Bz) (w := 0)
      hΛ (Eventually.of_forall hBz_nonneg) hBz_bdd
  refine ⟨?_, ?_, ?_⟩
  · intro j
    have hmix : ∀ t ∈ Icc (selectorMUWriteHoldTime j)
        (selectorMUWriteReadTime j),
        |selectorMixTarget branchU (sol w).u (sol w).lam t haltCoordU -
          stackMachineEncodingU.enc (cfg (j + 1)) haltCoordU| ≤ delta j := by
      intro t ht
      have hwrong : ∀ v : UniversalLocalView, v ≠ localViewU (cfg j) →
          (sol w).lam v t ≤ epsLam j :=
        fun v hv => le_trans
          (Finset.single_le_sum (fun u _ => hlam_nonneg j t ht u) (by simp [hv]))
          (hloser j t ht)
      have hraw := selectorMixTarget_halt_to_next_of_concentration
        (sol w).u (sol w).lam t (cfg j) (hepsLam_nonneg j)
        (hsum j t ht) (fun v => hlam_nonneg j t ht v) hwrong
      simpa [delta, hcfg_step j] using hraw
    have := z_write_settled_endpoint (sol w) cfg Λ Bz
      (fun j => delta j) j haltCoordU
      (hdom_write j) hgZ_cont (hgZ0 j) hmix (hz_start j) (hΛ_lower j)
    simpa [selectorMUWriteReadTime] using this
  · simpa using hctr.add hδ_tendsto
  · intro j
    exact add_nonneg
      (mul_nonneg (Real.exp_pos _).le (hBz_nonneg j))
      (mul_nonneg (Nat.cast_nonneg _) (hepsLam_nonneg j))

end Ripple.BoundedUniversality.BGP
