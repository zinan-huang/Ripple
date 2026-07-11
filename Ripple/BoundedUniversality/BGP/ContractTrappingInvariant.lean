/-
Ripple.BoundedUniversality.BGP.ContractTrappingInvariant
------------------------------------

Scalar trapping invariants for relaxation ODEs and the contract z-coordinate.

The main scalar lemma is stated on a finite interval `[0,T]` and then wrapped
as an all-`t ≥ 0` theorem.  The proof uses the existing Duhamel/Gronwall bound
`stack_write_gronwall_sup_bound`: center `[lo, hi]` at `(lo + hi) / 2` and use
radius `(hi - lo) / 2`.
-/

import Ripple.BoundedUniversality.BGP.ContractDuhamelHold

namespace Ripple.BoundedUniversality.BGP

open Real intervalIntegral
open scoped BigOperators Topology

noncomputable section

private lemma abs_sub_mid_le_half_width {lo hi x : ℝ}
    (hx : x ∈ Set.Icc lo hi) :
    |x - (lo + hi) / 2| ≤ (hi - lo) / 2 := by
  rw [abs_le]
  constructor <;> linarith [hx.1, hx.2]

private lemma mem_Icc_of_abs_sub_mid_le_half_width {lo hi x : ℝ}
    (hx : |x - (lo + hi) / 2| ≤ (hi - lo) / 2) :
    x ∈ Set.Icc lo hi := by
  rw [abs_le] at hx
  constructor <;> linarith [hx.1, hx.2]

/-- Scalar trapping on a finite interval for a relaxation ODE.

If `y' = k(t) * (g(t) - y(t))`, `k ≥ 0`, the moving target `g` stays in
`[lo, hi]` on `[0,T]`, and `y(0) ∈ [lo, hi]`, then `y(T) ∈ [lo, hi]`.

The proof applies the existing Duhamel/Gronwall estimate to the centered error
`|y - (lo + hi)/2|` with radius `(hi - lo)/2`. -/
theorem scalar_relaxation_trapping_invariant
    (y g k : ℝ → ℝ) {lo hi T : ℝ}
    (hT : 0 ≤ T)
    (hk_cont : Continuous k)
    (hg_cont : Continuous g)
    (hy_ode : ∀ τ ∈ Set.Icc (0 : ℝ) T,
      HasDerivAt y (k τ * (g τ - y τ)) τ)
    (hk_nonneg : ∀ τ ∈ Set.Icc (0 : ℝ) T, 0 ≤ k τ)
    (hg_range : ∀ τ ∈ Set.Icc (0 : ℝ) T, g τ ∈ Set.Icc lo hi)
    (hy0 : y 0 ∈ Set.Icc lo hi) :
    y T ∈ Set.Icc lo hi := by
  let mid : ℝ := (lo + hi) / 2
  let δ : ℝ := (hi - lo) / 2
  have hg_mid : ∀ τ ∈ Set.Icc (0 : ℝ) T, |g τ - mid| ≤ δ := by
    intro τ hτ
    simpa [mid, δ] using abs_sub_mid_le_half_width (hg_range τ hτ)
  have hy0_mid : |y 0 - mid| ≤ δ := by
    simpa [mid, δ] using abs_sub_mid_le_half_width hy0
  have hraw :
      |y T - mid| ≤
        Real.exp (-(∫ τ in (0 : ℝ)..T, k τ)) * |y 0 - mid| +
          δ * (1 - Real.exp (-(∫ τ in (0 : ℝ)..T, k τ))) :=
    stack_write_gronwall_sup_bound y g k mid (0 : ℝ) T hT hk_cont
      hk_nonneg hg_cont hy_ode hg_mid
  have hexp_nonneg : 0 ≤ Real.exp (-(∫ τ in (0 : ℝ)..T, k τ)) :=
    (Real.exp_pos _).le
  have hyT_mid : |y T - mid| ≤ δ := by
    calc
      |y T - mid|
          ≤ Real.exp (-(∫ τ in (0 : ℝ)..T, k τ)) * |y 0 - mid| +
              δ * (1 - Real.exp (-(∫ τ in (0 : ℝ)..T, k τ))) := hraw
      _ ≤ Real.exp (-(∫ τ in (0 : ℝ)..T, k τ)) * δ +
              δ * (1 - Real.exp (-(∫ τ in (0 : ℝ)..T, k τ))) :=
            add_le_add (mul_le_mul_of_nonneg_left hy0_mid hexp_nonneg) le_rfl
      _ = δ := by ring
  exact mem_Icc_of_abs_sub_mid_le_half_width (lo := lo) (hi := hi)
    (x := y T) (by simpa [mid, δ] using hyT_mid)

/--
Scalar trapping with interval-local continuity hypotheses.

The proof clamps the target and rate to `[0,T]`, obtaining global continuous
extensions, and then reuses `scalar_relaxation_trapping_invariant`.
-/
theorem scalar_relaxation_trapping_invariant_continuousOn
    (y g k : ℝ → ℝ) {lo hi T : ℝ}
    (hT : 0 ≤ T)
    (hk_cont : ContinuousOn k (Set.Icc (0 : ℝ) T))
    (hg_cont : ContinuousOn g (Set.Icc (0 : ℝ) T))
    (hy_ode : ∀ τ ∈ Set.Icc (0 : ℝ) T,
      HasDerivAt y (k τ * (g τ - y τ)) τ)
    (hk_nonneg : ∀ τ ∈ Set.Icc (0 : ℝ) T, 0 ≤ k τ)
    (hg_range : ∀ τ ∈ Set.Icc (0 : ℝ) T, g τ ∈ Set.Icc lo hi)
    (hy0 : y 0 ∈ Set.Icc lo hi) :
    y T ∈ Set.Icc lo hi := by
  let clamp : ℝ → ℝ := fun τ => min (max τ (0 : ℝ)) T
  let gext : ℝ → ℝ := fun τ => g (clamp τ)
  let kext : ℝ → ℝ := fun τ => k (clamp τ)
  have hclamp_cont : Continuous clamp := by
    dsimp [clamp]
    exact (continuous_id.max continuous_const).min continuous_const
  have hclamp_mem : ∀ τ : ℝ, clamp τ ∈ Set.Icc (0 : ℝ) T := by
    intro τ
    dsimp [clamp]
    constructor
    · exact le_min (le_max_right τ 0) hT
    · exact min_le_right _ _
  have hclamp_eq : ∀ τ ∈ Set.Icc (0 : ℝ) T, clamp τ = τ := by
    intro τ hτ
    dsimp [clamp]
    rw [max_eq_left hτ.1, min_eq_left hτ.2]
  have hkext_cont : Continuous kext := by
    exact hk_cont.comp_continuous hclamp_cont hclamp_mem
  have hgext_cont : Continuous gext := by
    exact hg_cont.comp_continuous hclamp_cont hclamp_mem
  exact scalar_relaxation_trapping_invariant
    (y := y) (g := gext) (k := kext) (lo := lo) (hi := hi) (T := T)
    hT hkext_cont hgext_cont
    (by
      intro τ hτ
      have hc : clamp τ = τ := hclamp_eq τ hτ
      simpa [gext, kext, hc] using hy_ode τ hτ)
    (by
      intro τ hτ
      have hc : clamp τ = τ := hclamp_eq τ hτ
      simpa [kext, hc] using hk_nonneg τ hτ)
    (by
      intro τ hτ
      have hc : clamp τ = τ := hclamp_eq τ hτ
      simpa [gext, hc] using hg_range τ hτ)
    hy0

/-- All-forward-time form of `scalar_relaxation_trapping_invariant`. -/
theorem scalar_relaxation_trapping_invariant_Ici
    (y g k : ℝ → ℝ) {lo hi : ℝ}
    (hk_cont : Continuous k)
    (hg_cont : Continuous g)
    (hy_ode : ∀ τ, 0 ≤ τ → HasDerivAt y (k τ * (g τ - y τ)) τ)
    (hk_nonneg : ∀ τ, 0 ≤ τ → 0 ≤ k τ)
    (hg_range : ∀ τ, 0 ≤ τ → g τ ∈ Set.Icc lo hi)
    (hy0 : y 0 ∈ Set.Icc lo hi) :
    ∀ T : ℝ, 0 ≤ T → y T ∈ Set.Icc lo hi := by
  intro T hT
  exact scalar_relaxation_trapping_invariant
    (y := y) (g := g) (k := k) (lo := lo) (hi := hi) (T := T)
    hT hk_cont hg_cont
    (fun τ hτ => hy_ode τ hτ.1)
    (fun τ hτ => hk_nonneg τ hτ.1)
    (fun τ hτ => hg_range τ hτ.1)
    hy0

/-- Contract z-coordinate trapping on a finite interval.

For a `DynContractIteratorSol`, the z-ODE at coordinate `s` is
`z' = zRate sol * (sol.w - z)`, where `zRate sol t = A * α(t) * bGateZ ...`.
If the rate is nonnegative, `sol.w · s` stays in `[lo, hi]`, and the initial
z-coordinate is in `[lo, hi]`, then the z-coordinate stays in `[lo, hi]`. -/
theorem contract_z_coord_trapping_invariant
    {d : ℕ} {p : DynGateParams} {sched : PhaseSchedule}
    {F : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    (sol : DynContractIteratorSol (Fin d) p sched F)
    (s : Fin d) {lo hi T : ℝ}
    (hT : 0 ≤ T)
    (hseg_domain : Set.Icc (0 : ℝ) T ⊆ sched.domain)
    (hA : 0 ≤ p.A)
    (hα_cont : Continuous sol.α)
    (hμ_cont : Continuous sol.μ)
    (hα_nonneg : ∀ τ ∈ Set.Icc (0 : ℝ) T, 0 ≤ sol.α τ)
    (hw_range : ∀ τ ∈ Set.Icc (0 : ℝ) T, sol.w τ s ∈ Set.Icc lo hi)
    (hz0 : sol.z 0 s ∈ Set.Icc lo hi) :
    sol.z T s ∈ Set.Icc lo hi := by
  exact scalar_relaxation_trapping_invariant
    (y := fun τ => sol.z τ s)
    (g := fun τ => sol.w τ s)
    (k := zRate sol)
    (lo := lo) (hi := hi) (T := T)
    hT
    (zRate_continuous sol hα_cont hμ_cont)
    (sol.cont_w s)
    (by
      intro τ hτ
      have h := sol.z_hasDeriv τ (hseg_domain hτ) s
      simpa [zRate] using h)
    (by
      intro τ hτ
      unfold zRate
      exact mul_nonneg (mul_nonneg hA (hα_nonneg τ hτ))
        (bGateZ_pos p.L (sol.μ τ) τ).le)
    hw_range
    hz0

/-- Same as `contract_z_coord_trapping_invariant`, but the moving target is
rewritten through the contract field identity `sol.w = F sol.μ sol.u`. -/
theorem contract_z_coord_trapping_invariant_of_F
    {d : ℕ} {p : DynGateParams} {sched : PhaseSchedule}
    {F : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    (sol : DynContractIteratorSol (Fin d) p sched F)
    (s : Fin d) {lo hi T : ℝ}
    (hT : 0 ≤ T)
    (hseg_domain : Set.Icc (0 : ℝ) T ⊆ sched.domain)
    (hA : 0 ≤ p.A)
    (hα_cont : Continuous sol.α)
    (hμ_cont : Continuous sol.μ)
    (hα_nonneg : ∀ τ ∈ Set.Icc (0 : ℝ) T, 0 ≤ sol.α τ)
    (hF_range : ∀ τ ∈ Set.Icc (0 : ℝ) T,
      F (sol.μ τ) (sol.u τ) s ∈ Set.Icc lo hi)
    (hz0 : sol.z 0 s ∈ Set.Icc lo hi) :
    sol.z T s ∈ Set.Icc lo hi := by
  refine contract_z_coord_trapping_invariant
    (sol := sol) (s := s) (lo := lo) (hi := hi) (T := T)
    hT hseg_domain hA hα_cont hμ_cont hα_nonneg ?_ hz0
  intro τ hτ
  have hτdom : τ ∈ sched.domain := hseg_domain hτ
  have htarget : sol.w τ = F (sol.μ τ) (sol.u τ) := sol.target_eq τ hτdom
  simpa [htarget] using hF_range τ hτ

/-- z-coordinate trapping on every active read window.  With `lo = 0`, `hi = 1`,
and `s = flagCoord`, this is exactly the shape needed for the flag-domain input
of `contract_flag_only_headline` for one supplied solution. -/
theorem contract_z_coord_trapping_on_zActiveWindow
    {d : ℕ} {p : DynGateParams} {sched : PhaseSchedule}
    {F : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    (sol : DynContractIteratorSol (Fin d) p sched F)
    (s : Fin d) {lo hi : ℝ}
    (hread_nonneg : ∀ j t, t ∈ sched.zActiveWindow j → 0 ≤ t)
    (hread_domain_Icc : ∀ j t, t ∈ sched.zActiveWindow j →
      Set.Icc (0 : ℝ) t ⊆ sched.domain)
    (hA : 0 ≤ p.A)
    (hα_cont : Continuous sol.α)
    (hμ_cont : Continuous sol.μ)
    (hα_nonneg : ∀ τ, τ ∈ sched.domain → 0 ≤ sol.α τ)
    (hw_range : ∀ j t, t ∈ sched.zActiveWindow j →
      ∀ τ ∈ Set.Icc (0 : ℝ) t, sol.w τ s ∈ Set.Icc lo hi)
    (hz0 : sol.z 0 s ∈ Set.Icc lo hi) :
    ∀ j t, t ∈ sched.zActiveWindow j →
      sol.z t s ∈ Set.Icc lo hi := by
  intro j t ht
  exact contract_z_coord_trapping_invariant
    (sol := sol) (s := s) (lo := lo) (hi := hi) (T := t)
    (hread_nonneg j t ht)
    (hread_domain_Icc j t ht)
    hA hα_cont hμ_cont
    (fun τ hτ => hα_nonneg τ ((hread_domain_Icc j t ht) hτ))
    (hw_range j t ht)
    hz0

/-- Active-window trapping with the target expressed as `F (sol.μ t) (sol.u t)`. -/
theorem contract_z_coord_trapping_on_zActiveWindow_of_F
    {d : ℕ} {p : DynGateParams} {sched : PhaseSchedule}
    {F : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    (sol : DynContractIteratorSol (Fin d) p sched F)
    (s : Fin d) {lo hi : ℝ}
    (hread_nonneg : ∀ j t, t ∈ sched.zActiveWindow j → 0 ≤ t)
    (hread_domain_Icc : ∀ j t, t ∈ sched.zActiveWindow j →
      Set.Icc (0 : ℝ) t ⊆ sched.domain)
    (hA : 0 ≤ p.A)
    (hα_cont : Continuous sol.α)
    (hμ_cont : Continuous sol.μ)
    (hα_nonneg : ∀ τ, τ ∈ sched.domain → 0 ≤ sol.α τ)
    (hF_range : ∀ j t, t ∈ sched.zActiveWindow j →
      ∀ τ ∈ Set.Icc (0 : ℝ) t,
        F (sol.μ τ) (sol.u τ) s ∈ Set.Icc lo hi)
    (hz0 : sol.z 0 s ∈ Set.Icc lo hi) :
    ∀ j t, t ∈ sched.zActiveWindow j →
      sol.z t s ∈ Set.Icc lo hi := by
  exact contract_z_coord_trapping_on_zActiveWindow
    (sol := sol) (s := s) (lo := lo) (hi := hi)
    hread_nonneg hread_domain_Icc hA hα_cont hμ_cont hα_nonneg
    (fun j t ht τ hτ => by
      have hτdom : τ ∈ sched.domain := (hread_domain_Icc j t ht) hτ
      have htarget : sol.w τ = F (sol.μ τ) (sol.u τ) := sol.target_eq τ hτdom
      simpa [htarget] using hF_range j t ht τ hτ)
    hz0

end

end Ripple.BoundedUniversality.BGP
