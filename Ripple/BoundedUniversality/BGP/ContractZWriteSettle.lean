/-
Ripple.BoundedUniversality.BGP.ContractZWriteSettle
-------------------------------
The contract-sol analog of `SelectorReplicatorSettledZ.z_write_settled_endpoint`,
upgraded to an INTERVAL bound over the left read-half `[2πj+5π/6, 2πj+π]` — the
`hz_left` producer consumed by `ContractTrackingPhys.contract_z_read_next_full`.

Mechanism (identical to the selector settled-endpoint): over the z-active write
window starting at `a = 2πj+π/6`, the z-rail relaxes toward its moving write
target `w` (which the settled-mixture bound keeps within `δw` of the next config
`Menc`).  The Duhamel relaxation bound (`contract_z_duhamel_bound`) gives

  |z(t)−Menc| ≤ exp(−∫_a^t k)·|z(a)−Menc| + δw·(1−exp(−∫_a^t k)),

and the (large, O(1)) starting gap `Bz = |z(a)−Menc|` is killed by the integral
mass: for every `t` in the left read-half, `∫_a^t k ≥ ∫_a^{2πj+5π/6} k ≥ Λ`
(rate ≥ 0, mass monotone), so `exp(−∫_a^t k)·Bz ≤ exp(−Λ)·Bz` and the moving-
target term `≤ δw`.  Hence `|z(t)−Menc| ≤ exp(−Λ)·Bz + δw =: ρ` uniformly on the
left half.  The mass lower bound `Λ` is supplied externally (the selector side
discharges its analog via `z_write_settled_mass_tendsto_atTop`).

ABSOLUTE: no sorry/admit/native_decide/axiom.
-/

import Ripple.BoundedUniversality.BGP.ContractDuhamelHold

namespace Ripple.BoundedUniversality.BGP

open Ripple.BoundedUniversality.Core

noncomputable section

variable {d : ℕ} {p : DynGateParams} {sched : PhaseSchedule}
  {F : ℝ → (Fin d → ℝ) → Fin d → ℝ}

/-- **Contract-sol interval z-write-settle** (the `hz_left` producer).  Over the
left read-half `[2πj+5π/6, 2πj+π]` the z-rail is within `ρ` of the next-config
target `Menc`, where `ρ ≥ exp(−Λ)·Bz + δw`:
* `Bz` bounds the (possibly O(1)) starting gap `|z(2πj+π/6)−Menc|`;
* `δw` bounds the moving write target `|w(τ)−Menc|` over the write window;
* `Λ` lower-bounds the accumulated gate mass `∫_{2πj+π/6}^{2πj+5π/6} k`.

Feeds `ContractTrackingPhys.contract_z_read_next_full` with
`Menc i := E.enc (c (j+1)) i`, `ρ i := ρ j i`. -/
theorem contract_hz_left
    (sol : DynContractIteratorSol (Fin d) p sched F)
    (Menc : Fin d → ℝ) (j : ℕ)
    {Bz δw Λ : ℝ} {ρ : Fin d → ℝ}
    (hA : 0 ≤ p.A)
    (hk_cont : Continuous (zRate sol))
    (hαnn : ∀ τ ∈ Set.Icc (2 * Real.pi * (j : ℝ) + Real.pi / 6)
        (2 * Real.pi * (j : ℝ) + Real.pi), 0 ≤ sol.α τ)
    (hdom : Set.Icc (2 * Real.pi * (j : ℝ) + Real.pi / 6)
        (2 * Real.pi * (j : ℝ) + Real.pi) ⊆ sched.domain)
    (hz_start : ∀ i,
      |sol.z (2 * Real.pi * (j : ℝ) + Real.pi / 6) i - Menc i| ≤ Bz)
    (hwsup : ∀ i, ∀ τ ∈ Set.Icc (2 * Real.pi * (j : ℝ) + Real.pi / 6)
        (2 * Real.pi * (j : ℝ) + Real.pi), |sol.w τ i - Menc i| ≤ δw)
    (hΛ : Λ ≤ ∫ τ in (2 * Real.pi * (j : ℝ) + Real.pi / 6)..(2 * Real.pi * (j : ℝ)
        + 5 * Real.pi / 6), zRate sol τ)
    (hρ : ∀ i, Real.exp (-Λ) * Bz + δw ≤ ρ i) :
    ∀ t ∈ Set.Icc (2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6)
        (2 * Real.pi * (j : ℝ) + Real.pi), ∀ i,
      |sol.z t i - Menc i| ≤ ρ i := by
  intro t ht i
  set a : ℝ := 2 * Real.pi * (j : ℝ) + Real.pi / 6 with ha_def
  set m : ℝ := 2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6 with hm_def
  set e : ℝ := 2 * Real.pi * (j : ℝ) + Real.pi with he_def
  have ham : a ≤ m := by rw [ha_def, hm_def]; nlinarith [Real.pi_pos]
  have hmt : m ≤ t := ht.1
  have hte : t ≤ e := ht.2
  have hat : a ≤ t := le_trans ham hmt
  -- rate ≥ 0 on the whole write window [a,e]
  have hrate_nn : ∀ τ ∈ Set.Icc a e, 0 ≤ zRate sol τ := by
    intro τ hτ
    rw [zRate]
    exact mul_nonneg (mul_nonneg hA (hαnn τ hτ)) (bGateZ_pos p.L (sol.μ τ) τ).le
  -- Duhamel relaxation bound at b = t, target Menc i
  have hαnn_at : ∀ τ ∈ Set.Icc a t, 0 ≤ sol.α τ :=
    fun τ hτ => hαnn τ ⟨hτ.1, le_trans hτ.2 hte⟩
  have hdom_at : Set.Icc a t ⊆ sched.domain :=
    fun τ hτ => hdom ⟨hτ.1, le_trans hτ.2 hte⟩
  have hwsup_at : ∀ τ ∈ Set.Icc a t, |sol.w τ i - Menc i| ≤ δw :=
    fun τ hτ => hwsup i τ ⟨hτ.1, le_trans hτ.2 hte⟩
  have hduh := contract_z_duhamel_bound sol i (Menc i) a t hat hk_cont hA
    hαnn_at hdom_at hwsup_at
  -- integral mass: ∫_a^t ≥ ∫_a^m ≥ Λ, and ∫_a^t ≥ 0
  have hII : ∀ x y : ℝ,
      IntervalIntegrable (zRate sol) MeasureTheory.volume x y :=
    fun x y => hk_cont.intervalIntegrable x y
  have hadd : (∫ τ in a..m, zRate sol τ) + (∫ τ in m..t, zRate sol τ)
      = ∫ τ in a..t, zRate sol τ :=
    intervalIntegral.integral_add_adjacent_intervals (hII a m) (hII m t)
  have htail_nn : 0 ≤ ∫ τ in m..t, zRate sol τ := by
    apply intervalIntegral.integral_nonneg hmt
    intro τ hτ
    exact hrate_nn τ ⟨le_trans ham hτ.1, le_trans hτ.2 hte⟩
  have hmass : Λ ≤ ∫ τ in a..t, zRate sol τ := by
    have hmono : (∫ τ in a..m, zRate sol τ) ≤ ∫ τ in a..t, zRate sol τ := by
      rw [← hadd]; linarith
    linarith [hΛ]
  have hmass_nn : 0 ≤ ∫ τ in a..t, zRate sol τ := by
    apply intervalIntegral.integral_nonneg hat
    intro τ hτ
    exact hrate_nn τ ⟨hτ.1, le_trans hτ.2 hte⟩
  -- exponential comparisons
  have hexp_le : Real.exp (-(∫ τ in a..t, zRate sol τ)) ≤ Real.exp (-Λ) :=
    Real.exp_le_exp.mpr (by linarith [hmass])
  have hexp_le_one : Real.exp (-(∫ τ in a..t, zRate sol τ)) ≤ 1 := by
    rw [show (1 : ℝ) = Real.exp 0 from Real.exp_zero.symm]
    exact Real.exp_le_exp.mpr (by linarith [hmass_nn])
  have hexp_nn : 0 ≤ Real.exp (-(∫ τ in a..t, zRate sol τ)) := (Real.exp_pos _).le
  -- nonnegativity of the radii constants
  have hBz_nn : 0 ≤ Bz := le_trans (abs_nonneg _) (hz_start i)
  have hδw_nn : 0 ≤ δw := by
    have := hwsup i a ⟨le_refl a, le_trans hat hte⟩
    exact le_trans (abs_nonneg _) this
  -- bound each Duhamel term
  have hterm1 : Real.exp (-(∫ τ in a..t, zRate sol τ)) * |sol.z a i - Menc i|
      ≤ Real.exp (-Λ) * Bz :=
    mul_le_mul hexp_le (hz_start i) (abs_nonneg _) (Real.exp_pos _).le
  have hterm2 : δw * (1 - Real.exp (-(∫ τ in a..t, zRate sol τ))) ≤ δw := by
    nlinarith [hδw_nn, hexp_nn, hexp_le_one]
  calc |sol.z t i - Menc i|
      ≤ Real.exp (-(∫ τ in a..t, zRate sol τ)) * |sol.z a i - Menc i|
          + δw * (1 - Real.exp (-(∫ τ in a..t, zRate sol τ))) := hduh
    _ ≤ Real.exp (-Λ) * Bz + δw := by linarith [hterm1, hterm2]
    _ ≤ ρ i := hρ i

/-- **Contract-sol U-copy at the cycle boundary** (the `hu_write_next` producer).
The u-rail relaxes toward the moving target `z`; over the copy window
`[2πj+7π/6, 2π(j+1)+π/6]` (read-end → next strong-start) `z` has settled, staying
within `δz` of its read-end value `z(2πj+7π/6)`.  Taking the fixed target
`M := z(2πj+7π/6) i`, the Duhamel relaxation gives

  |u(2π(j+1)+π/6) − M| ≤ exp(−∫ uRate)·|u(2πj+7π/6) − M| + δz·(1−exp(−∫ uRate)),

and `|u(2πj+7π/6) − M| = |u(readEnd) − z(readEnd)| ≤ Bu` is shrunk by the gate
mass `Λu`.  Hence `ω ≥ exp(−Λu)·Bu + δz`.  Feeds
`ContractTrackingPhys.contract_hrec_step_phys`'s `hu_write_next`. -/
theorem contract_hu_write_next
    (sol : DynContractIteratorSol (Fin d) p sched F)
    (j : ℕ) {Bu δz Λu : ℝ} {ω : Fin d → ℝ}
    (hA : 0 ≤ p.A)
    (hk_cont : Continuous (uRate sol))
    (hαnn : ∀ τ ∈ Set.Icc (2 * Real.pi * (j : ℝ) + 7 * Real.pi / 6)
        (2 * Real.pi * ((j + 1 : ℕ) : ℝ) + Real.pi / 6), 0 ≤ sol.α τ)
    (hdom : Set.Icc (2 * Real.pi * (j : ℝ) + 7 * Real.pi / 6)
        (2 * Real.pi * ((j + 1 : ℕ) : ℝ) + Real.pi / 6) ⊆ sched.domain)
    (hu_start : ∀ i,
      |sol.u (2 * Real.pi * (j : ℝ) + 7 * Real.pi / 6) i
        - sol.z (2 * Real.pi * (j : ℝ) + 7 * Real.pi / 6) i| ≤ Bu)
    (hz_settle : ∀ i, ∀ τ ∈ Set.Icc (2 * Real.pi * (j : ℝ) + 7 * Real.pi / 6)
        (2 * Real.pi * ((j + 1 : ℕ) : ℝ) + Real.pi / 6),
      |sol.z τ i - sol.z (2 * Real.pi * (j : ℝ) + 7 * Real.pi / 6) i| ≤ δz)
    (hΛ : Λu ≤ ∫ τ in (2 * Real.pi * (j : ℝ) + 7 * Real.pi / 6)..(2 * Real.pi
        * ((j + 1 : ℕ) : ℝ) + Real.pi / 6), uRate sol τ)
    (hω : ∀ i, Real.exp (-Λu) * Bu + δz ≤ ω i) :
    ∀ i, |sol.u (2 * Real.pi * ((j + 1 : ℕ) : ℝ) + Real.pi / 6) i
        - sol.z (2 * Real.pi * (j : ℝ) + 7 * Real.pi / 6) i| ≤ ω i := by
  intro i
  set a : ℝ := 2 * Real.pi * (j : ℝ) + 7 * Real.pi / 6 with ha_def
  set b : ℝ := 2 * Real.pi * ((j + 1 : ℕ) : ℝ) + Real.pi / 6 with hb_def
  have hab : a ≤ b := by rw [ha_def, hb_def]; push_cast; nlinarith [Real.pi_pos]
  -- rate ≥ 0 on the copy window
  have hrate_nn : ∀ τ ∈ Set.Icc a b, 0 ≤ uRate sol τ := by
    intro τ hτ
    rw [uRate]
    exact mul_nonneg (mul_nonneg hA (hαnn τ hτ)) (bGateU_pos p.L (sol.μ τ) τ).le
  -- Duhamel at fixed target M = z(a) i
  have hzsup : ∀ τ ∈ Set.Icc a b, |sol.z τ i - sol.z a i| ≤ δz :=
    fun τ hτ => hz_settle i τ hτ
  have hduh := contract_u_duhamel_bound sol i (sol.z a i) a b hab hk_cont hA
    hαnn hdom hzsup
  -- mass nonneg + exponential comparisons
  have hmass_nn : 0 ≤ ∫ τ in a..b, uRate sol τ := by
    apply intervalIntegral.integral_nonneg hab
    intro τ hτ
    exact hrate_nn τ hτ
  have hexp_le : Real.exp (-(∫ τ in a..b, uRate sol τ)) ≤ Real.exp (-Λu) :=
    Real.exp_le_exp.mpr (by linarith [hΛ])
  have hexp_le_one : Real.exp (-(∫ τ in a..b, uRate sol τ)) ≤ 1 := by
    rw [show (1 : ℝ) = Real.exp 0 from Real.exp_zero.symm]
    exact Real.exp_le_exp.mpr (by linarith [hmass_nn])
  have hexp_nn : 0 ≤ Real.exp (-(∫ τ in a..b, uRate sol τ)) := (Real.exp_pos _).le
  have hBu_nn : 0 ≤ Bu := le_trans (abs_nonneg _) (hu_start i)
  have hδz_nn : 0 ≤ δz := by
    have := hz_settle i a ⟨le_refl a, hab⟩
    exact le_trans (abs_nonneg _) this
  have hterm1 : Real.exp (-(∫ τ in a..b, uRate sol τ)) * |sol.u a i - sol.z a i|
      ≤ Real.exp (-Λu) * Bu :=
    mul_le_mul hexp_le (hu_start i) (abs_nonneg _) (Real.exp_pos _).le
  have hterm2 : δz * (1 - Real.exp (-(∫ τ in a..b, uRate sol τ))) ≤ δz := by
    nlinarith [hδz_nn, hexp_nn, hexp_le_one]
  calc |sol.u b i - sol.z a i|
      ≤ Real.exp (-(∫ τ in a..b, uRate sol τ)) * |sol.u a i - sol.z a i|
          + δz * (1 - Real.exp (-(∫ τ in a..b, uRate sol τ))) := hduh
    _ ≤ Real.exp (-Λu) * Bu + δz := by linarith [hterm1, hterm2]
    _ ≤ ω i := hω i

#print axioms contract_hz_left
#print axioms contract_hu_write_next

end

end Ripple.BoundedUniversality.BGP
