-- Ripple/LPP/NAPLayerCopyPipeline.lean
/-
  A marked-set PP readout compiles to a marked-set NAP readout with the same value.
  The producer is pp_to_nap_ode_of_init_set. Its returned protocol, source
  solution, and clock are used directly; the new solution is their three-layer
  diagonal copy. Both possible slack marking coefficients are represented.
-/

import Ripple.LPP.NAPLayerCopyReadout
import Ripple.LPP.NAPLayerCopyDynamics

namespace Ripple
namespace NAPTransport
namespace LayerCopy

open Set Filter Topology Finset

/-- The explicit copied Veronese initial point. -/
noncomputable def copiedInitial (n : ℕ) (J : Finset (Fin n)) (lam : ℚ)
    (x0 : Fin n → ℝ) : MI (n + 1) 3 × Fin 3 → ℝ :=
  diagonal 3 (ver (n + 1) (slackMapSet n J lam x0))

/-- The actual copied trajectory of the returned original solution and clock. -/
noncomputable def copiedTrajectory (n : ℕ) (J : Finset (Fin n)) (lam : ℚ)
    (source : ℝ → Fin n → ℝ) (clock : ℝ → ℝ) :
    ℝ → MI (n + 1) 3 × Fin 3 → ℝ :=
  fun t => copiedInitial n J lam (source (clock t))

/-- Complete data and conclusions of marked-set compilation at a given initial point.
The original base protocol is retained, and the copied protocol is copyProtocol baseProtocol 3.
No output trajectory or unique-solution premise is assumed by the producer theorem. -/
structure MarkedCompilation (n : ℕ) (g : QuadPP n) (M J : Finset (Fin n))
    (slackMarked : Bool) (lam : ℚ) (hlam0 : 0 < lam) (x0 : Fin n → ℝ) where
  common_mark :
    ∀ j ∈ J, markedIndicator n M j = (if slackMarked then (1 : ℝ) else 0)
  baseProtocol : WProtocol (MI (n + 1) 3)
  base_nonneg : ∀ sh, 0 ≤ baseProtocol sh
  base_isNAP : baseProtocol.IsNAP
  base_realizes :
    Realizes (veroneseLift (n + 1) 3) baseProtocol
      (demand (n + 1) (liftR2Set n g J lam hlam0))
  copy_nonneg : ∀ sh, 0 ≤ copyProtocol baseProtocol 3 sh
  copy_isNAP : (copyProtocol baseProtocol 3).IsNAP
  source : ℝ → Fin n → ℝ
  source_initial : source 0 = x0
  source_ode : ∀ t, 0 ≤ t → HasDerivAt source (quadFun n g (source t)) t
  source_unique :
    ∀ source' : ℝ → Fin n → ℝ, source' 0 = x0 →
      (∀ t, 0 ≤ t → HasDerivAt source' (quadFun n g (source' t)) t) →
      ∀ t, 0 ≤ t → source' t = source t
  source_simplex : ∀ t, 0 ≤ t → (∀ j, 0 ≤ source t j) ∧ ∑ j, source t j = 1
  clock : ℝ → ℝ
  clock_inverse :
    ∀ σ, 0 ≤ σ →
      clock (∫ s in (0 : ℝ)..σ, ((1 - (lam : ℝ)) * ∑ j ∈ J, source s j)⁻¹ ^ 2) = σ
  clock_zero : clock 0 = 0
  clock_strictMono : StrictMono clock
  clock_tendsto : Tendsto clock atTop atTop
  clock_nonneg_deriv :
    ∀ t, 0 ≤ t → 0 ≤ clock t ∧
      HasDerivAt clock (((1 - (lam : ℝ)) * ∑ j ∈ J, source (clock t) j) ^ 2) t
  copy_initial :
    copiedTrajectory n J lam source clock 0 = copiedInitial n J lam x0
  copy_ode :
    ∀ t, 0 ≤ t →
      HasDerivWithinAt (copiedTrajectory n J lam source clock)
        (field (copyProtocol baseProtocol 3) (copiedTrajectory n J lam source clock t))
        (Ici 0) t
  copy_simplex :
    ∀ t, 0 ≤ t →
      (∀ p, 0 ≤ copiedTrajectory n J lam source clock t p) ∧
        ∑ p, copiedTrajectory n J lam source clock t p = 1
  copy_unique_Icc :
    ∀ (T : ℝ) (u : ℝ → MI (n + 1) 3 × Fin 3 → ℝ),
      (∀ t ∈ Icc (0 : ℝ) T,
        HasDerivWithinAt u (field (copyProtocol baseProtocol 3) (u t)) (Icc 0 T) t) →
      u 0 = copiedInitial n J lam x0 →
      EqOn u (copiedTrajectory n J lam source clock) (Icc 0 T)
  copy_unique :
    ∀ u : ℝ → MI (n + 1) 3 × Fin 3 → ℝ,
      (∀ t, 0 ≤ t →
        HasDerivWithinAt u (field (copyProtocol baseProtocol 3) (u t)) (Ici 0) t) →
      u 0 = copiedInitial n J lam x0 →
      ∀ t, 0 ≤ t → u t = copiedTrajectory n J lam source clock t
  readout :
    ∀ t, 0 ≤ t →
      (∑ p ∈ copyMarkedSet n M slackMarked, copiedTrajectory n J lam source clock t p) =
        ∑ j ∈ M, source (clock t) j
  readout_limit :
    ∀ ν : ℝ, Tendsto (fun s => ∑ j ∈ M, source s j) atTop (𝓝 ν) →
      Tendsto (fun t => ∑ p ∈ copyMarkedSet n M slackMarked,
        copiedTrajectory n J lam source clock t p) atTop (𝓝 ν)
  clock_rate :
    ∀ m : ℝ, 0 < m →
      Tendsto (fun s => ∑ j ∈ J, source s j) atTop (𝓝 m) →
      ∀ θ : ℝ, 0 < θ → θ < 1 →
      ∃ C, ∀ t, 0 ≤ t → θ * ((1 - (lam : ℝ)) * m) ^ 2 * t - C ≤ clock t
  readout_rate :
    ∀ ν A κ m : ℝ, 0 ≤ κ → 0 < m →
      Tendsto (fun s => ∑ j ∈ J, source s j) atTop (𝓝 m) →
      (∀ s, 0 ≤ s → |∑ j ∈ M, source s j - ν| ≤ A * Real.exp (-κ * s)) →
      ∀ θ : ℝ, 0 < θ → θ < 1 →
      ∃ C, ∀ t, 0 ≤ t →
        |∑ p ∈ copyMarkedSet n M slackMarked, copiedTrajectory n J lam source clock t p - ν|
          ≤ C * Real.exp (-(θ * κ * ((1 - (lam : ℝ)) * m) ^ 2) * t)

/-- The base protocol is chosen before the initial point. Thus the marked-set compiler is
uniform over all simplex initial points having positive mass on the chosen slack set. -/
theorem pp_to_nap_layer_copy_uniform (n : ℕ) (g : QuadPP n) (M J : Finset (Fin n))
    (b : Bool) (hc : ∀ j ∈ J, markedIndicator n M j = (if b then (1 : ℝ) else 0))
    (lam : ℚ) (hlam0 : 0 < lam) (hlam1 : lam < 1) :
    ∃ w : WProtocol (MI (n + 1) 3), (∀ sh, 0 ≤ w sh) ∧ w.IsNAP ∧
      Realizes (veroneseLift (n + 1) 3) w (demand (n + 1) (liftR2Set n g J lam hlam0)) ∧
      ∀ x0 : Fin n → ℝ, (∀ j, 0 ≤ x0 j) → ∑ j, x0 j = 1 → 0 < ∑ j ∈ J, x0 j →
        ∃ C : MarkedCompilation n g M J b lam hlam0 x0, C.baseProtocol = w := by
  obtain ⟨w, hw0, hwN, hwr, hproducer⟩ :=
    pp_to_nap_ode_of_init_set n g J lam hlam0 hlam1
  refine ⟨w, hw0, hwN, hwr, ?_⟩
  intro x0 hx0n hx0s hx0p
  obtain ⟨x, hxi, hx, hxu, hxs, τ, hinverse, hzero, hstrict, htop, hderiv,
      hlift, hliftunique, hlinear, hlinearlimit, hclock, hexponential⟩ :=
    hproducer x0 hx0n hx0s hx0p
  have hv :
      ∀ t, 0 ≤ t →
        HasDerivWithinAt (fun s => ver (n + 1) (slackMapSet n J lam (x (τ s))))
          (field w (ver (n + 1) (slackMapSet n J lam (x (τ t))))) (Ici 0) t := by
    intro t ht
    simpa only [field_eq_balanceFun] using hlift t ht
  have hcopyinitial :
      copiedTrajectory n J lam x τ 0 = copiedInitial n J lam x0 := by
    simp only [copiedTrajectory, hzero, hxi]
  have hcopyderiv :
      ∀ t, 0 ≤ t →
        HasDerivWithinAt (copiedTrajectory n J lam x τ)
          (field (copyProtocol w 3) (copiedTrajectory n J lam x τ t)) (Ici 0) t := by
    intro t ht
    simpa only [copiedTrajectory, copiedInitial] using
      diagonal_hasDerivWithinAt w 3 (by norm_num) (hv t ht)
  have hcopysimplex :
      ∀ t, 0 ≤ t →
        (∀ p, 0 ≤ copiedTrajectory n J lam x τ t p) ∧
          ∑ p, copiedTrajectory n J lam x τ t p = 1 := by
    intro t ht
    have hl0 : (0 : ℝ) ≤ lam := by exact_mod_cast hlam0.le
    have hl1 : (lam : ℝ) ≤ 1 := by exact_mod_cast hlam1.le
    have hp := ver_slackMapSet_simplex n J lam hl0 hl1 (x (τ t))
      (hxs (τ t) (hderiv t ht).1).1 (hxs (τ t) (hderiv t ht).1).2
    simpa only [copiedTrajectory, copiedInitial] using
      diagonal_simplex 3 (by norm_num) _ hp.1 hp.2
  have hcopyunique :
      ∀ (T : ℝ) (u : ℝ → MI (n + 1) 3 × Fin 3 → ℝ),
        (∀ t ∈ Icc (0 : ℝ) T,
          HasDerivWithinAt u (field (copyProtocol w 3) (u t)) (Icc 0 T) t) →
        u 0 = copiedInitial n J lam x0 →
        EqOn u (copiedTrajectory n J lam x τ) (Icc 0 T) := by
    intro T u hu hu0
    have hinit :
        u 0 = diagonal 3 (ver (n + 1) (slackMapSet n J lam (x (τ 0)))) := by
      simpa only [hzero, hxi, copiedInitial] using hu0
    simpa only [copiedTrajectory, copiedInitial] using
      copy_solution_unique_Icc w 3 (by norm_num) hv hu hinit
  have hcopyuniqueGlobal :
      ∀ u : ℝ → MI (n + 1) 3 × Fin 3 → ℝ,
        (∀ t, 0 ≤ t → HasDerivWithinAt u (field (copyProtocol w 3) (u t)) (Ici 0) t) →
        u 0 = copiedInitial n J lam x0 →
        ∀ t, 0 ≤ t → u t = copiedTrajectory n J lam x τ t := by
    intro u hu hu0
    have hinit :
        u 0 = diagonal 3 (ver (n + 1) (slackMapSet n J lam (x (τ 0)))) := by
      simpa only [hzero, hxi, copiedInitial] using hu0
    simpa only [copiedTrajectory, copiedInitial] using
      copy_solution_unique w 3 (by norm_num) hv hu hinit
  have hread :
      ∀ t, 0 ≤ t →
        (∑ p ∈ copyMarkedSet n M b, copiedTrajectory n J lam x τ t p) =
          ∑ j ∈ M, x (τ t) j := by
    intro t ht
    unfold copiedTrajectory copiedInitial
    rw [sum_copyMarkedSet_diagonal,
      hlinear (markedIndicator n M) (if b then 1 else 0) hc t ht, sum_markedIndicator]
  have hreadlimit :
      ∀ ν : ℝ, Tendsto (fun s => ∑ j ∈ M, x s j) atTop (𝓝 ν) →
        Tendsto (fun t => ∑ p ∈ copyMarkedSet n M b, copiedTrajectory n J lam x τ t p)
          atTop (𝓝 ν) := by
    intro ν hν
    have h : Tendsto (fun t => ∑ j ∈ M, x (τ t) j) atTop (𝓝 ν) := hν.comp htop
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact (hread t ht).symm
  have hreadrate :
      ∀ ν A κ m : ℝ, 0 ≤ κ → 0 < m →
        Tendsto (fun s => ∑ j ∈ J, x s j) atTop (𝓝 m) →
        (∀ s, 0 ≤ s → |∑ j ∈ M, x s j - ν| ≤ A * Real.exp (-κ * s)) →
        ∀ θ : ℝ, 0 < θ → θ < 1 →
        ∃ C, ∀ t, 0 ≤ t →
          |∑ p ∈ copyMarkedSet n M b, copiedTrajectory n J lam x τ t p - ν|
            ≤ C * Real.exp (-(θ * κ * ((1 - (lam : ℝ)) * m) ^ 2) * t) := by
    intro ν A κ m hκ hm hxm hA θ hθ0 hθ1
    obtain ⟨C, hC⟩ :=
      hexponential (markedIndicator n M) (if b then 1 else 0) ν A κ m hc hκ hm hxm
        (fun s hs => by simpa only [sum_markedIndicator] using hA s hs) θ hθ0 hθ1
    refine ⟨C, ?_⟩
    intro t ht
    simpa only [copiedTrajectory, copiedInitial, sum_copyMarkedSet_diagonal] using hC t ht
  let result : MarkedCompilation n g M J b lam hlam0 x0 :=
    { common_mark := hc
      baseProtocol := w
      base_nonneg := hw0
      base_isNAP := hwN
      base_realizes := hwr
      copy_nonneg := copyProtocol_nonneg w 3 hw0
      copy_isNAP := copyProtocol_isNAP w 3 hwN
      source := x
      source_initial := hxi
      source_ode := hx
      source_unique := hxu
      source_simplex := hxs
      clock := τ
      clock_inverse := hinverse
      clock_zero := hzero
      clock_strictMono := hstrict
      clock_tendsto := htop
      clock_nonneg_deriv := hderiv
      copy_initial := hcopyinitial
      copy_ode := hcopyderiv
      copy_simplex := hcopysimplex
      copy_unique_Icc := hcopyunique
      copy_unique := hcopyuniqueGlobal
      readout := hread
      readout_limit := hreadlimit
      clock_rate := hclock
      readout_rate := hreadrate }
  exact ⟨result, rfl⟩

/-- Pointwise form of the uniform producer with an explicit common zero/one coefficient. -/
theorem pp_to_nap_layer_copy_of_common_mark (n : ℕ) (g : QuadPP n)
    (M J : Finset (Fin n)) (b : Bool)
    (hc : ∀ j ∈ J, markedIndicator n M j = (if b then (1 : ℝ) else 0))
    (lam : ℚ) (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (x0 : Fin n → ℝ) (hx0n : ∀ j, 0 ≤ x0 j) (hx0s : ∑ j, x0 j = 1)
    (hx0p : 0 < ∑ j ∈ J, x0 j) :
    Nonempty (MarkedCompilation n g M J b lam hlam0 x0) := by
  obtain ⟨w, hw0, hwN, hwr, h⟩ :=
    pp_to_nap_layer_copy_uniform n g M J b hc lam hlam0 hlam1
  obtain ⟨result, _⟩ := h x0 hx0n hx0s hx0p
  exact ⟨result⟩

/-- **Marked-set PP to marked-set NAP.**
Either admissible choice of the shrunk set is supported; the slack is marked exactly
when its common original coefficient is one. The output value and pipeline exponent
are unchanged by the three-layer construction. -/
theorem pp_to_nap_layer_copy_of_init_set (n : ℕ) (g : QuadPP n)
    (M J : Finset (Fin n)) (hJ : J ⊆ M ∨ J ⊆ Mᶜ)
    (lam : ℚ) (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (x0 : Fin n → ℝ) (hx0n : ∀ j, 0 ≤ x0 j) (hx0s : ∑ j, x0 j = 1)
    (hx0p : 0 < ∑ j ∈ J, x0 j) :
    ∃ b : Bool, Nonempty (MarkedCompilation n g M J b lam hlam0 x0) := by
  obtain ⟨b, hb⟩ := exists_common_mark n M J hJ
  exact ⟨b, pp_to_nap_layer_copy_of_common_mark n g M J b hb lam hlam0 hlam1
    x0 hx0n hx0s hx0p⟩


/-- Every simplex initial point admits one of the two required slack orientations.
If the marked set has zero initial mass, its complement has all the initial mass. -/
theorem pp_to_nap_layer_copy_of_init (n : ℕ) (g : QuadPP n)
    (M : Finset (Fin n)) (lam : ℚ) (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (x0 : Fin n → ℝ) (hx0n : ∀ j, 0 ≤ x0 j) (hx0s : ∑ j, x0 j = 1) :
    ∃ J : Finset (Fin n), ∃ b : Bool,
      (J = M ∨ J = Mᶜ) ∧ (0 < ∑ j ∈ J, x0 j) ∧
        Nonempty (MarkedCompilation n g M J b lam hlam0 x0) := by
  classical
  by_cases hM : 0 < ∑ j ∈ M, x0 j
  · refine ⟨M, true, Or.inl rfl, hM, ?_⟩
    exact pp_to_nap_layer_copy_of_common_mark n g M M true
      (common_mark_of_marked_subset n M M (by intro j hj; exact hj))
      lam hlam0 hlam1 x0 hx0n hx0s hM
  · have hMc : 0 < ∑ j ∈ Mᶜ, x0 j := by
      rw [sum_compl_eq_one_sub_marked n M x0 hx0s]
      have hle : (∑ j ∈ M, x0 j) ≤ 0 := le_of_not_gt hM
      linarith
    refine ⟨Mᶜ, false, Or.inr rfl, hMc, ?_⟩
    exact pp_to_nap_layer_copy_of_common_mark n g M Mᶜ false
      (common_mark_of_unmarked_subset n M Mᶜ (by intro j hj; exact hj))
      lam hlam0 hlam1 x0 hx0n hx0s hMc


end LayerCopy
end NAPTransport
end Ripple
