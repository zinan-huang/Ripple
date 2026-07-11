/-
Ripple.BoundedUniversality.BGP.ContractFlagZReadFromContraction
-------------------------------------------
Produces the `hflag_z_read_from` hypothesis of `contract_flag_only_headline`
(the flag-coordinate z-read tube for j ≥ j₀) from the per-cycle z-write
contraction and Z-off hold.

The KEY simplification at the flag coordinate: because
`E.coordStackIndex flagCoord = none` (the `flag_reset` field of
`HaltFlagPackage`), we have `E.coordMultiplier c flagCoord = 0` for every
config `c`.  The robust-step diagonal bound therefore gives
  `|w flagCoord − enc(step c) flagCoord| ≤ 0 + epsF(μ) flagCoord = epsF(μ) flagCoord`,
independent of the u-tube.  This eliminates the u-tracking dependency from
the flag z-read, making it dischargeable before (and independently of) the
full weighted-bound induction.

Discharge path:
1. LEFT half `[2πj+5π/6, 2πj+π]`: Duhamel relaxation at `flagCoord` with
   `δw = δw_flag` (the flag-specific epsF-only bound on the moving target).
   The starting gap `Bz_flag` is killed by the write-phase gate mass `Λ_flag`.
2. RIGHT half `[2πj+π, 2πj+7π/6]`: Z-off hold via
   `contract_z_hold_via_integral` (sin ≤ 0), with `Dw = δw_flag` and the
   z-start bound from the left-half output.
3. GLUE: split the read window at `2πj+π`.

All lemmas operate at a single coordinate (`flagCoord`), not coordwise,
exploiting the flag-specific moving-target collapse.

No sorry/admit/native_decide/axiom.
-/

import Ripple.BoundedUniversality.BGP.ContractZWriteSettle
import Ripple.BoundedUniversality.BGP.ContractTrackingPhys

namespace Ripple.BoundedUniversality.BGP

open Ripple.BoundedUniversality.Core

noncomputable section

variable {d nS : ℕ} {Conf : Type} [Primcodable Conf] {M : DiscreteMachine Conf}
  {E : StackMachineEncoding d nS M}
  {p : DynGateParams} {sched : PhaseSchedule}

/-- **Flag-coordinate moving-target bound (epsF-only).**  For a reset coordinate
`flagCoord` with `E.coordStackIndex flagCoord = none`, the robust-step diagonal
`|F(μ,u) flagCoord − enc(step c) flagCoord| ≤ coordMultiplier c flagCoord * err + epsF`
collapses to `≤ epsF(μ) flagCoord` because `coordMultiplier c flagCoord = 0`.
This is the flag-specific tightening that eliminates the u-tube dependency. -/
theorem contract_w_flag_near_next
    (S : RobustStepContract M E)
    (sol : DynContractIteratorSol (Fin d) p sched S.F)
    (c : ℕ → Conf) (j : ℕ) {τ : ℝ} (hτdom : τ ∈ sched.domain)
    (hcstep : c (j + 1) = M.step (c j))
    (hmu : S.mu_min ≤ sol.μ τ)
    (htube : EncodingTube E (S.radius (sol.μ τ)) (c j) (sol.u τ))
    (flagCoord : Fin d) (hflag : E.coordStackIndex flagCoord = none) :
    |sol.w τ flagCoord - E.enc (c (j + 1)) flagCoord| ≤ S.epsF (sol.μ τ) flagCoord := by
  have hw : sol.w τ = S.F (sol.μ τ) (sol.u τ) := sol.target_eq τ hτdom
  rw [hcstep, hw]
  have hdiag := S.diagonal_bound hmu htube flagCoord
  have hmult : E.coordMultiplier (c j) flagCoord = 0 := by
    simp [StackMachineEncoding.coordMultiplier, hflag]
  rw [hmult, zero_mul, zero_add] at hdiag
  exact hdiag

/-- **Scalar left-half z-write-settle at the flag coordinate.**  On the left
read-half `[2πj+5π/6, 2πj+π]`, `z` at `flagCoord` is within
`exp(−Λ)·Bz + δw` of the next-config target, where:
* `Bz` bounds `|z(2πj+π/6) flagCoord − M|`;
* `δw` bounds `|w(τ) flagCoord − M|` uniformly;
* `Λ` lower-bounds `∫_{2πj+π/6}^{2πj+5π/6} zRate`.

This is the single-coordinate extraction from `contract_z_duhamel_bound`,
parallel to `contract_hz_left` but operating at a single coordinate. -/
theorem contract_hz_left_flag
    {F : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    (sol : DynContractIteratorSol (Fin d) p sched F)
    (flagCoord : Fin d)
    (M : ℝ) (j : ℕ)
    {Bz δw Λ ρ : ℝ}
    (hA : 0 ≤ p.A)
    (hk_cont : Continuous (zRate sol))
    (hαnn : ∀ τ ∈ Set.Icc (2 * Real.pi * (j : ℝ) + Real.pi / 6)
        (2 * Real.pi * (j : ℝ) + Real.pi), 0 ≤ sol.α τ)
    (hdom : Set.Icc (2 * Real.pi * (j : ℝ) + Real.pi / 6)
        (2 * Real.pi * (j : ℝ) + Real.pi) ⊆ sched.domain)
    (hz_start :
      |sol.z (2 * Real.pi * (j : ℝ) + Real.pi / 6) flagCoord - M| ≤ Bz)
    (hwsup : ∀ τ ∈ Set.Icc (2 * Real.pi * (j : ℝ) + Real.pi / 6)
        (2 * Real.pi * (j : ℝ) + Real.pi),
      |sol.w τ flagCoord - M| ≤ δw)
    (hΛ : Λ ≤ ∫ τ in (2 * Real.pi * (j : ℝ) + Real.pi / 6)..(2 * Real.pi * (j : ℝ)
        + 5 * Real.pi / 6), zRate sol τ)
    (hρ : Real.exp (-Λ) * Bz + δw ≤ ρ) :
    ∀ t ∈ Set.Icc (2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6)
        (2 * Real.pi * (j : ℝ) + Real.pi),
      |sol.z t flagCoord - M| ≤ ρ := by
  intro t ht
  set a : ℝ := 2 * Real.pi * (j : ℝ) + Real.pi / 6 with ha_def
  set m : ℝ := 2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6 with hm_def
  set e : ℝ := 2 * Real.pi * (j : ℝ) + Real.pi with he_def
  have ham : a ≤ m := by rw [ha_def, hm_def]; nlinarith [Real.pi_pos]
  have hmt : m ≤ t := ht.1
  have hte : t ≤ e := ht.2
  have hat : a ≤ t := le_trans ham hmt
  have hrate_nn : ∀ τ ∈ Set.Icc a e, 0 ≤ zRate sol τ := by
    intro τ hτ; rw [zRate]
    exact mul_nonneg (mul_nonneg hA (hαnn τ hτ)) (bGateZ_pos p.L (sol.μ τ) τ).le
  have hαnn_at : ∀ τ ∈ Set.Icc a t, 0 ≤ sol.α τ :=
    fun τ hτ => hαnn τ ⟨hτ.1, le_trans hτ.2 hte⟩
  have hdom_at : Set.Icc a t ⊆ sched.domain :=
    fun τ hτ => hdom ⟨hτ.1, le_trans hτ.2 hte⟩
  have hwsup_at : ∀ τ ∈ Set.Icc a t, |sol.w τ flagCoord - M| ≤ δw :=
    fun τ hτ => hwsup τ ⟨hτ.1, le_trans hτ.2 hte⟩
  have hduh := contract_z_duhamel_bound sol flagCoord M a t hat hk_cont hA
    hαnn_at hdom_at hwsup_at
  have hII : ∀ x y : ℝ,
      IntervalIntegrable (zRate sol) MeasureTheory.volume x y :=
    fun x y => hk_cont.intervalIntegrable x y
  have hadd : (∫ τ in a..m, zRate sol τ) + (∫ τ in m..t, zRate sol τ)
      = ∫ τ in a..t, zRate sol τ :=
    intervalIntegral.integral_add_adjacent_intervals (hII a m) (hII m t)
  have htail_nn : 0 ≤ ∫ τ in m..t, zRate sol τ := by
    apply intervalIntegral.integral_nonneg hmt
    intro τ hτ; exact hrate_nn τ ⟨le_trans ham hτ.1, le_trans hτ.2 hte⟩
  have hmass : Λ ≤ ∫ τ in a..t, zRate sol τ := by linarith [hadd, hΛ, htail_nn]
  have hmass_nn : 0 ≤ ∫ τ in a..t, zRate sol τ := by
    apply intervalIntegral.integral_nonneg hat
    intro τ hτ; exact hrate_nn τ ⟨hτ.1, le_trans hτ.2 hte⟩
  have hexp_le : Real.exp (-(∫ τ in a..t, zRate sol τ)) ≤ Real.exp (-Λ) :=
    Real.exp_le_exp.mpr (by linarith [hmass])
  have hexp_le_one : Real.exp (-(∫ τ in a..t, zRate sol τ)) ≤ 1 := by
    rw [show (1 : ℝ) = Real.exp 0 from Real.exp_zero.symm]
    exact Real.exp_le_exp.mpr (by linarith [hmass_nn])
  have hexp_nn : 0 ≤ Real.exp (-(∫ τ in a..t, zRate sol τ)) := (Real.exp_pos _).le
  have hBz_nn : 0 ≤ Bz := le_trans (abs_nonneg _) hz_start
  have hδw_nn : 0 ≤ δw := le_trans (abs_nonneg _) (hwsup a ⟨le_refl a, le_trans hat hte⟩)
  have hterm1 : Real.exp (-(∫ τ in a..t, zRate sol τ))
      * |sol.z a flagCoord - M| ≤ Real.exp (-Λ) * Bz :=
    mul_le_mul hexp_le hz_start (abs_nonneg _) (Real.exp_pos _).le
  have hterm2 : δw * (1 - Real.exp (-(∫ τ in a..t, zRate sol τ))) ≤ δw := by
    nlinarith [hδw_nn, hexp_nn, hexp_le_one]
  calc |sol.z t flagCoord - M|
      ≤ Real.exp (-(∫ τ in a..t, zRate sol τ)) * |sol.z a flagCoord - M|
          + δw * (1 - Real.exp (-(∫ τ in a..t, zRate sol τ))) := hduh
    _ ≤ Real.exp (-Λ) * Bz + δw := by linarith [hterm1, hterm2]
    _ ≤ ρ := hρ

/-- **Single-cycle flag-coordinate z-read from a direct moving-target bound.**

This is the same Duhamel-plus-hold estimate as
`contract_flag_z_read_cycle_from_contraction`, but its moving-target residual
is supplied directly as a bound on `sol.w`.  It is the interface to use when the
read analysis should not expose a `RobustStepContract` diagonal-bound witness.
-/
theorem contract_flag_z_read_cycle_from_target_bound
    {F : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    (sol : DynContractIteratorSol (Fin d) p sched F)
    (flagCoord : Fin d) (target : ℝ) (j : ℕ)
    (hA : 0 ≤ p.A) (hcμ : 0 ≤ p.cμ)
    (hαinit : 0 ≤ sol.init_α) (hμinit : 0 ≤ sol.init_μ)
    (hlam_pos : 0 < DynChiLeak.leakLambda p.cμ p.cα p.L)
    (hdom : ∀ s : ℝ, 0 ≤ s → s ∈ sched.domain)
    (hαcont : Continuous sol.α) (hμcont : Continuous sol.μ)
    {δw_flag : ℝ}
    (hw_flag : ∀ τ ∈ Set.Icc
        (2 * Real.pi * (j : ℝ) + Real.pi / 6)
        (2 * Real.pi * (j : ℝ) + 7 * Real.pi / 6),
      |sol.w τ flagCoord - target| ≤ δw_flag)
    {Bz_flag : ℝ}
    (hz_start_flag :
      |sol.z (2 * Real.pi * (j : ℝ) + Real.pi / 6) flagCoord
        - target| ≤ Bz_flag)
    {Λ_flag : ℝ}
    (hΛ_flag :
      Λ_flag ≤
        ∫ τ in (2 * Real.pi * (j : ℝ) + Real.pi / 6)..(2 * Real.pi * (j : ℝ)
            + 5 * Real.pi / 6), zRate sol τ)
    {ρ_flag : ℝ}
    (hρ_budget :
      Real.exp (-Λ_flag) * Bz_flag + δw_flag
        + δw_flag * (p.A * sol.init_α
            * Real.exp (-(sol.init_μ * (1 / 2 : ℝ) ^ p.L))
            * Real.exp (-(DynChiLeak.leakLambda p.cμ p.cα p.L
                * (2 * Real.pi * (j : ℝ) + Real.pi)))
            / DynChiLeak.leakLambda p.cμ p.cα p.L) ≤ ρ_flag) :
    ∀ t ∈ contractReadWindow j,
      |sol.z t flagCoord - target| ≤ ρ_flag := by
  intro t ht
  rw [contractReadWindow, Set.mem_Icc] at ht
  have hzk_cont := zRate_continuous sol hαcont hμcont
  have hws_nn : (0 : ℝ) ≤ 2 * Real.pi * (j : ℝ) + Real.pi / 6 := by positivity
  have hws_le_mid :
      2 * Real.pi * (j : ℝ) + Real.pi / 6 ≤
        2 * Real.pi * (j : ℝ) + Real.pi := by
    nlinarith
  have hws_le_rend :
      2 * Real.pi * (j : ℝ) + Real.pi / 6 ≤
        2 * Real.pi * (j : ℝ) + 7 * Real.pi / 6 := by
    nlinarith
  have hmid_le_rend :
      2 * Real.pi * (j : ℝ) + Real.pi ≤
        2 * Real.pi * (j : ℝ) + 7 * Real.pi / 6 := by
    nlinarith
  have hmid_nn : (0 : ℝ) ≤ 2 * Real.pi * (j : ℝ) + Real.pi := by
    nlinarith
  have hlstart_le_mid :
      2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6 ≤
        2 * Real.pi * (j : ℝ) + Real.pi := by
    nlinarith
  have hδw_flag : 0 ≤ δw_flag :=
    le_trans (abs_nonneg _)
      (hw_flag (2 * Real.pi * (j : ℝ) + Real.pi / 6)
        ⟨le_refl _, hws_le_rend⟩)
  have hαnn : ∀ τ ∈ Set.Icc
      (2 * Real.pi * (j : ℝ) + Real.pi / 6)
      (2 * Real.pi * (j : ℝ) + Real.pi), 0 ≤ sol.α τ := by
    intro τ hτ
    rw [contractSol_alpha_eq sol hdom (le_trans hws_nn hτ.1)]
    exact mul_nonneg hαinit (Real.exp_pos _).le
  have hdom_sub : Set.Icc
      (2 * Real.pi * (j : ℝ) + Real.pi / 6)
      (2 * Real.pi * (j : ℝ) + Real.pi) ⊆ sched.domain :=
    fun τ hτ => hdom τ (le_trans hws_nn hτ.1)
  set ρL := Real.exp (-Λ_flag) * Bz_flag + δw_flag
  have hz_left_bound : ∀ t' ∈ Set.Icc
      (2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6)
      (2 * Real.pi * (j : ℝ) + Real.pi),
      |sol.z t' flagCoord - target| ≤ ρL :=
    contract_hz_left_flag sol flagCoord target j hA
      hzk_cont hαnn hdom_sub hz_start_flag
      (fun τ hτ => hw_flag τ ⟨hτ.1, le_trans hτ.2 hmid_le_rend⟩)
      hΛ_flag (le_refl _)
  by_cases htm : t ≤ 2 * Real.pi * (j : ℝ) + Real.pi
  · have hleft := hz_left_bound t ⟨ht.1, htm⟩
    have hρL_le : ρL ≤ ρ_flag := by
      have hleak_nn : 0 ≤ δw_flag * (p.A * sol.init_α
          * Real.exp (-(sol.init_μ * (1 / 2 : ℝ) ^ p.L))
          * Real.exp (-(DynChiLeak.leakLambda p.cμ p.cα p.L
              * (2 * Real.pi * (j : ℝ) + Real.pi)))
          / DynChiLeak.leakLambda p.cμ p.cα p.L) := by
        apply mul_nonneg hδw_flag
        apply div_nonneg
        · exact mul_nonneg (mul_nonneg (mul_nonneg hA hαinit)
            (Real.exp_pos _).le) (Real.exp_pos _).le
        · exact hlam_pos.le
      linarith
    exact le_trans hleft hρL_le
  · simp only [not_le] at htm
    have hjunction := hz_left_bound (2 * Real.pi * (j : ℝ) + Real.pi)
      ⟨hlstart_le_mid, le_refl _⟩
    have hsin : ∀ τ ∈ Set.Icc (2 * Real.pi * (j : ℝ) + Real.pi) t,
        Real.sin τ ≤ 0 :=
      fun τ hτ => sin_nonpos_read_right j hτ.1 (le_trans hτ.2 ht.2)
    have hwsup_right : ∀ τ ∈ Set.Icc (2 * Real.pi * (j : ℝ) + Real.pi) t,
        |sol.w τ flagCoord - target| ≤ δw_flag :=
      fun τ hτ => hw_flag τ ⟨le_trans hws_le_mid hτ.1, le_trans hτ.2 ht.2⟩
    have hright := contract_z_hold_via_integral sol flagCoord target
      (2 * Real.pi * (j : ℝ) + Real.pi) t
      (le_of_lt htm) hmid_nn
      hA hcμ hαinit hμinit hlam_pos hdom hzk_cont hsin hδw_flag hjunction hwsup_right
    exact le_trans hright hρ_budget

#print axioms contract_flag_z_read_cycle_from_target_bound

/-- **Single-cycle flag-coordinate z-read from a late-start moving-target bound.**

The moving target is required only on the actual read window
`[2πj + 5π/6, 2πj + 7π/6]`, and the start radius is supplied at the read
opening.  This is the reducer shape matching HStart-style producers.
-/
theorem contract_flag_z_read_cycle_from_late_target_bound
    {F : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    (sol : DynContractIteratorSol (Fin d) p sched F)
    (flagCoord : Fin d) (target : ℝ) (j : ℕ)
    (hA : 0 ≤ p.A)
    (hdom : ∀ s : ℝ, 0 ≤ s → s ∈ sched.domain)
    (hαcont : Continuous sol.α) (hμcont : Continuous sol.μ)
    (hαinit : 0 ≤ sol.init_α)
    {δw_read Bz_read ρ_read : ℝ}
    (hz_read_start :
      |sol.z (2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6) flagCoord
        - target| ≤ Bz_read)
    (hw_read : ∀ τ ∈ contractReadWindow j,
      |sol.w τ flagCoord - target| ≤ δw_read)
    (hρ_budget : Bz_read + δw_read ≤ ρ_read) :
    ∀ t ∈ contractReadWindow j,
      |sol.z t flagCoord - target| ≤ ρ_read := by
  intro t ht
  rw [contractReadWindow, Set.mem_Icc] at ht
  set a : ℝ := 2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6 with ha_def
  set b : ℝ := 2 * Real.pi * (j : ℝ) + 7 * Real.pi / 6 with hb_def
  have ha0 : 0 ≤ a := by
    rw [ha_def]
    positivity
  have hat : a ≤ t := by
    simpa [ha_def] using ht.1
  have htb : t ≤ b := by
    simpa [hb_def] using ht.2
  have ha_mem : a ∈ contractReadWindow j := by
    rw [contractReadWindow, Set.mem_Icc]
    constructor
    · rw [ha_def]
    · rw [ha_def]
      nlinarith [Real.pi_pos]
  have hδw_nn : 0 ≤ δw_read :=
    le_trans (abs_nonneg _) (hw_read a ha_mem)
  have hBz_nn : 0 ≤ Bz_read :=
    le_trans (abs_nonneg _) hz_read_start
  have hαnn : ∀ τ ∈ Set.Icc a t, 0 ≤ sol.α τ := by
    intro τ hτ
    rw [contractSol_alpha_eq sol hdom (le_trans ha0 hτ.1)]
    exact mul_nonneg hαinit (Real.exp_pos _).le
  have hdom_sub : Set.Icc a t ⊆ sched.domain :=
    fun τ hτ => hdom τ (le_trans ha0 hτ.1)
  have hz0 : |sol.z a flagCoord - target| ≤ Bz_read + δw_read := by
    have hz0' : |sol.z a flagCoord - target| ≤ Bz_read := by
      simpa [ha_def] using hz_read_start
    linarith
  have hw : ∀ τ ∈ Set.Icc a t,
      |sol.w τ flagCoord - target| ≤ Bz_read + δw_read := by
    intro τ hτ
    have hτread : τ ∈ contractReadWindow j := by
      rw [contractReadWindow, Set.mem_Icc]
      constructor
      · simpa [ha_def] using hτ.1
      · simpa [hb_def] using le_trans hτ.2 htb
    have hτw := hw_read τ hτread
    linarith
  exact
    (contract_z_hold_le sol flagCoord target a t hat
      (zRate_continuous sol hαcont hμcont)
      hA hαnn hdom_sub hz0 hw).trans hρ_budget

#print axioms contract_flag_z_read_cycle_from_late_target_bound

/-- **Single-cycle flag-coordinate z-read tube from contraction.**

For a fixed cycle `j` and every `t ∈ contractReadWindow j`,
  `|sol.z t flagCoord − E.enc (c(j+1)) flagCoord| ≤ ρ_flag`
where `ρ_flag` absorbs both the left-half write-settle and right-half
Z-off-hold contributions.

The flag-specific moving-target collapse (`coordMultiplier = 0 ⇒ δw = epsF`)
makes `ρ_flag` independent of the u-tracking weighted bound.

The proof splits the read window `[2πj+5π/6, 2πj+7π/6]` at `2πj+π`:
* LEFT `[2πj+5π/6, 2πj+π]`: `contract_hz_left_flag` (Duhamel write-settle),
  giving `|z − enc(c(j+1))| ≤ exp(−Λ)·Bz + δw =: ρL` at the junction;
* RIGHT `[2πj+π, 2πj+7π/6]`: `contract_z_hold_via_integral` (Z-off hold),
  using the junction bound `ρL` as z-start and `δw_flag` as moving-target `Dw`,
  adding `δw · leak(2πj+π)`.
* Budget: `ρ_flag ≥ exp(−Λ)·Bz + δw + δw · leak(2πj+π)`. -/
theorem contract_flag_z_read_cycle_from_contraction
    (S : RobustStepContract M E)
    (sol : DynContractIteratorSol (Fin d) p sched S.F)
    (c : ℕ → Conf) (j : ℕ)
    (flagCoord : Fin d) (hflag : E.coordStackIndex flagCoord = none)
    (hcstep : c (j + 1) = M.step (c j))
    (hA : 0 ≤ p.A) (hcμ : 0 ≤ p.cμ)
    (hαinit : 0 ≤ sol.init_α) (hμinit : 0 ≤ sol.init_μ)
    (hlam_pos : 0 < DynChiLeak.leakLambda p.cμ p.cα p.L)
    (hdom : ∀ s : ℝ, 0 ≤ s → s ∈ sched.domain)
    (hαcont : Continuous sol.α) (hμcont : Continuous sol.μ)
    (hmuLB : ∀ τ ∈ Set.Icc
        (2 * Real.pi * (j : ℝ) + Real.pi / 6)
        (2 * Real.pi * (j : ℝ) + 7 * Real.pi / 6),
        S.mu_min ≤ sol.μ τ)
    (hutube : ∀ τ ∈ Set.Icc
        (2 * Real.pi * (j : ℝ) + Real.pi / 6)
        (2 * Real.pi * (j : ℝ) + 7 * Real.pi / 6),
      EncodingTube E (S.radius (sol.μ τ)) (c j) (sol.u τ))
    {δw_flag : ℝ} (hδw_flag : 0 ≤ δw_flag)
    (hepsF_flag : ∀ τ ∈ Set.Icc
        (2 * Real.pi * (j : ℝ) + Real.pi / 6)
        (2 * Real.pi * (j : ℝ) + 7 * Real.pi / 6),
      S.epsF (sol.μ τ) flagCoord ≤ δw_flag)
    {Bz_flag : ℝ}
    (hz_start_flag :
      |sol.z (2 * Real.pi * (j : ℝ) + Real.pi / 6) flagCoord
        - E.enc (c (j + 1)) flagCoord| ≤ Bz_flag)
    {Λ_flag : ℝ}
    (hΛ_flag :
      Λ_flag ≤
        ∫ τ in (2 * Real.pi * (j : ℝ) + Real.pi / 6)..(2 * Real.pi * (j : ℝ)
            + 5 * Real.pi / 6), zRate sol τ)
    {ρ_flag : ℝ}
    (hρ_budget :
      Real.exp (-Λ_flag) * Bz_flag + δw_flag
        + δw_flag * (p.A * sol.init_α
            * Real.exp (-(sol.init_μ * (1 / 2 : ℝ) ^ p.L))
            * Real.exp (-(DynChiLeak.leakLambda p.cμ p.cα p.L
                * (2 * Real.pi * (j : ℝ) + Real.pi)))
            / DynChiLeak.leakLambda p.cμ p.cα p.L) ≤ ρ_flag) :
    ∀ t ∈ contractReadWindow j,
      |sol.z t flagCoord - E.enc (c (j + 1)) flagCoord| ≤ ρ_flag := by
  intro t ht
  rw [contractReadWindow, Set.mem_Icc] at ht
  have hzk_cont := zRate_continuous sol hαcont hμcont
  have hws_nn : (0 : ℝ) ≤ 2 * Real.pi * (j : ℝ) + Real.pi / 6 := by positivity
  have hws_le_mid :
      2 * Real.pi * (j : ℝ) + Real.pi / 6 ≤
        2 * Real.pi * (j : ℝ) + Real.pi := by
    nlinarith
  have hmid_le_rend :
      2 * Real.pi * (j : ℝ) + Real.pi ≤
        2 * Real.pi * (j : ℝ) + 7 * Real.pi / 6 := by
    nlinarith
  have hmid_nn : (0 : ℝ) ≤ 2 * Real.pi * (j : ℝ) + Real.pi := by
    nlinarith
  have hlstart_le_mid :
      2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6 ≤
        2 * Real.pi * (j : ℝ) + Real.pi := by
    nlinarith
  have hαnn : ∀ τ ∈ Set.Icc
      (2 * Real.pi * (j : ℝ) + Real.pi / 6)
      (2 * Real.pi * (j : ℝ) + Real.pi), 0 ≤ sol.α τ := by
    intro τ hτ
    rw [contractSol_alpha_eq sol hdom (le_trans hws_nn hτ.1)]
    exact mul_nonneg hαinit (Real.exp_pos _).le
  have hdom_sub : Set.Icc
      (2 * Real.pi * (j : ℝ) + Real.pi / 6)
      (2 * Real.pi * (j : ℝ) + Real.pi) ⊆ sched.domain :=
    fun τ hτ => hdom τ (le_trans hws_nn hτ.1)
  have hw_flag : ∀ τ ∈ Set.Icc
      (2 * Real.pi * (j : ℝ) + Real.pi / 6)
      (2 * Real.pi * (j : ℝ) + 7 * Real.pi / 6),
      |sol.w τ flagCoord - E.enc (c (j + 1)) flagCoord| ≤ δw_flag := by
    intro τ hτ
    exact le_trans
      (contract_w_flag_near_next S sol c j
        (hdom τ (le_trans hws_nn hτ.1))
        hcstep (hmuLB τ hτ) (hutube τ hτ) flagCoord hflag)
      (hepsF_flag τ hτ)
  set ρL := Real.exp (-Λ_flag) * Bz_flag + δw_flag
  have hz_left_bound : ∀ t' ∈ Set.Icc
      (2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6)
      (2 * Real.pi * (j : ℝ) + Real.pi),
      |sol.z t' flagCoord - E.enc (c (j + 1)) flagCoord| ≤ ρL :=
    contract_hz_left_flag sol flagCoord (E.enc (c (j + 1)) flagCoord) j hA
      hzk_cont hαnn hdom_sub hz_start_flag
      (fun τ hτ => hw_flag τ ⟨hτ.1, le_trans hτ.2 hmid_le_rend⟩)
      hΛ_flag (le_refl _)
  by_cases htm : t ≤ 2 * Real.pi * (j : ℝ) + Real.pi
  · have hleft := hz_left_bound t ⟨ht.1, htm⟩
    have hρL_le : ρL ≤ ρ_flag := by
      have hleak_nn : 0 ≤ δw_flag * (p.A * sol.init_α
          * Real.exp (-(sol.init_μ * (1 / 2 : ℝ) ^ p.L))
          * Real.exp (-(DynChiLeak.leakLambda p.cμ p.cα p.L
              * (2 * Real.pi * (j : ℝ) + Real.pi)))
          / DynChiLeak.leakLambda p.cμ p.cα p.L) := by
        apply mul_nonneg hδw_flag
        apply div_nonneg
        · exact mul_nonneg (mul_nonneg (mul_nonneg hA hαinit)
            (Real.exp_pos _).le) (Real.exp_pos _).le
        · exact hlam_pos.le
      linarith
    exact le_trans hleft hρL_le
  · simp only [not_le] at htm
    have hjunction := hz_left_bound (2 * Real.pi * (j : ℝ) + Real.pi)
      ⟨hlstart_le_mid, le_refl _⟩
    have hsin : ∀ τ ∈ Set.Icc (2 * Real.pi * (j : ℝ) + Real.pi) t,
        Real.sin τ ≤ 0 :=
      fun τ hτ => sin_nonpos_read_right j hτ.1 (le_trans hτ.2 ht.2)
    have hwsup_right : ∀ τ ∈ Set.Icc (2 * Real.pi * (j : ℝ) + Real.pi) t,
        |sol.w τ flagCoord - E.enc (c (j + 1)) flagCoord| ≤ δw_flag :=
      fun τ hτ => hw_flag τ ⟨le_trans hws_le_mid hτ.1, le_trans hτ.2 ht.2⟩
    have hright := contract_z_hold_via_integral sol flagCoord
      (E.enc (c (j + 1)) flagCoord) (2 * Real.pi * (j : ℝ) + Real.pi) t
      (le_of_lt htm) hmid_nn
      hA hcμ hαinit hμinit hlam_pos hdom hzk_cont hsin hδw_flag hjunction hwsup_right
    exact le_trans hright hρ_budget

#print axioms contract_flag_z_read_cycle_from_contraction

/-- **Flag-coordinate z-read tube from contraction.**  Produces the
`hflag_z_read_from` hypothesis of `contract_flag_only_headline`: for every
`j ≥ j₀` and every `t ∈ contractReadWindow j`,
  `|sol.z t flagCoord − E.enc (c(j+1)) flagCoord| ≤ ρ_flag j`
where `ρ_flag` absorbs both the left-half write-settle and right-half
Z-off-hold contributions.

This all-cycle wrapper keeps the original scalar-budget interface.  Use
`contract_flag_z_read_cycle_from_contraction` when the residuals need to depend
on the cycle index. -/
theorem contract_flag_z_read_from_contraction
    (S : RobustStepContract M E)
    (sol : DynContractIteratorSol (Fin d) p sched S.F)
    (c : ℕ → Conf) (j₀ : ℕ)
    (flagCoord : Fin d) (hflag : E.coordStackIndex flagCoord = none)
    (hcstep : ∀ j, c (j + 1) = M.step (c j))
    -- sol regularity
    (hA : 0 ≤ p.A) (hcμ : 0 ≤ p.cμ)
    (hαinit : 0 ≤ sol.init_α) (hμinit : 0 ≤ sol.init_μ)
    (hlam_pos : 0 < DynChiLeak.leakLambda p.cμ p.cα p.L)
    (hdom : ∀ s : ℝ, 0 ≤ s → s ∈ sched.domain)
    (hαcont : Continuous sol.α) (hμcont : Continuous sol.μ)
    -- mu lower bound + u-tube (for the diagonal_bound → epsF collapse)
    (hmuLB : ∀ j, j₀ ≤ j → ∀ τ ∈ Set.Icc (2 * Real.pi * (j : ℝ) + Real.pi / 6)
        (2 * Real.pi * (j : ℝ) + 7 * Real.pi / 6), S.mu_min ≤ sol.μ τ)
    (hutube : ∀ j, j₀ ≤ j → ∀ τ ∈ Set.Icc (2 * Real.pi * (j : ℝ) + Real.pi / 6)
        (2 * Real.pi * (j : ℝ) + 7 * Real.pi / 6),
      EncodingTube E (S.radius (sol.μ τ)) (c j) (sol.u τ))
    -- flag-specific moving-target bound (the epsF-only collapse)
    {δw_flag : ℝ} (hδw_flag : 0 ≤ δw_flag)
    (hepsF_flag : ∀ j, j₀ ≤ j → ∀ τ ∈ Set.Icc (2 * Real.pi * (j : ℝ) + Real.pi / 6)
        (2 * Real.pi * (j : ℝ) + 7 * Real.pi / 6),
      S.epsF (sol.μ τ) flagCoord ≤ δw_flag)
    -- z-start gap at the flag coordinate
    {Bz_flag : ℝ}
    (hz_start_flag : ∀ j, j₀ ≤ j →
      |sol.z (2 * Real.pi * (j : ℝ) + Real.pi / 6) flagCoord
        - E.enc (c (j + 1)) flagCoord| ≤ Bz_flag)
    -- gate mass lower bound
    {Λ_flag : ℝ}
    (hΛ_flag : ∀ j, j₀ ≤ j →
      Λ_flag ≤ ∫ τ in (2 * Real.pi * (j : ℝ) + Real.pi / 6)..(2 * Real.pi * (j : ℝ)
          + 5 * Real.pi / 6), zRate sol τ)
    -- carried radius (absorbs BOTH halves:
    --   left gives exp(−Λ)*Bz + δw,
    --   right adds δw * offphase-leak(2πj+π))
    {ρ_flag : ℕ → ℝ}
    (hρ_budget : ∀ j, j₀ ≤ j →
      Real.exp (-Λ_flag) * Bz_flag + δw_flag
        + δw_flag * (p.A * sol.init_α
            * Real.exp (-(sol.init_μ * (1 / 2 : ℝ) ^ p.L))
            * Real.exp (-(DynChiLeak.leakLambda p.cμ p.cα p.L
                * (2 * Real.pi * (j : ℝ) + Real.pi)))
            / DynChiLeak.leakLambda p.cμ p.cα p.L) ≤ ρ_flag j) :
    ∀ j, j₀ ≤ j → ∀ t ∈ contractReadWindow j,
      |sol.z t flagCoord - E.enc (c (j + 1)) flagCoord| ≤ ρ_flag j := by
  intro j hj₀ t ht
  rw [contractReadWindow, Set.mem_Icc] at ht
  have hzk_cont := zRate_continuous sol hαcont hμcont
  -- Key time points
  have hπ := Real.pi_pos
  have hws_nn : (0 : ℝ) ≤ 2 * Real.pi * (j : ℝ) + Real.pi / 6 := by positivity
  have hws_le_mid : 2 * Real.pi * (j : ℝ) + Real.pi / 6 ≤ 2 * Real.pi * (j : ℝ) + Real.pi :=
    by nlinarith
  have hws_le_rend : 2 * Real.pi * (j : ℝ) + Real.pi / 6
      ≤ 2 * Real.pi * (j : ℝ) + 7 * Real.pi / 6 := by nlinarith
  have hmid_le_rend : 2 * Real.pi * (j : ℝ) + Real.pi
      ≤ 2 * Real.pi * (j : ℝ) + 7 * Real.pi / 6 := by nlinarith
  have hmid_nn : (0 : ℝ) ≤ 2 * Real.pi * (j : ℝ) + Real.pi := by nlinarith
  have hlstart_le_mid : 2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6
      ≤ 2 * Real.pi * (j : ℝ) + Real.pi := by nlinarith
  -- α ≥ 0 on the write window [wstart, midpt]
  have hαnn : ∀ τ ∈ Set.Icc (2 * Real.pi * (j : ℝ) + Real.pi / 6)
      (2 * Real.pi * (j : ℝ) + Real.pi), 0 ≤ sol.α τ := by
    intro τ hτ
    rw [contractSol_alpha_eq sol hdom (le_trans hws_nn hτ.1)]
    exact mul_nonneg hαinit (Real.exp_pos _).le
  -- domain inclusion
  have hdom_sub : Set.Icc (2 * Real.pi * (j : ℝ) + Real.pi / 6)
      (2 * Real.pi * (j : ℝ) + Real.pi) ⊆ sched.domain :=
    fun τ hτ => hdom τ (le_trans hws_nn hτ.1)
  -- w bound at flagCoord from the epsF collapse (over the full write+read window)
  have hw_flag : ∀ τ ∈ Set.Icc (2 * Real.pi * (j : ℝ) + Real.pi / 6)
      (2 * Real.pi * (j : ℝ) + 7 * Real.pi / 6),
      |sol.w τ flagCoord - E.enc (c (j + 1)) flagCoord| ≤ δw_flag := by
    intro τ hτ
    exact le_trans
      (contract_w_flag_near_next S sol c j
        (hdom τ (le_trans hws_nn hτ.1))
        (hcstep j) (hmuLB j hj₀ τ hτ) (hutube j hj₀ τ hτ) flagCoord hflag)
      (hepsF_flag j hj₀ τ hτ)
  -- Left-half bound
  set ρL := Real.exp (-Λ_flag) * Bz_flag + δw_flag
  have hz_left_bound : ∀ t' ∈ Set.Icc (2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6)
      (2 * Real.pi * (j : ℝ) + Real.pi),
      |sol.z t' flagCoord - E.enc (c (j + 1)) flagCoord| ≤ ρL :=
    contract_hz_left_flag sol flagCoord (E.enc (c (j + 1)) flagCoord) j hA
      hzk_cont hαnn hdom_sub (hz_start_flag j hj₀)
      (fun τ hτ => hw_flag τ ⟨hτ.1, le_trans hτ.2 hmid_le_rend⟩)
      (hΛ_flag j hj₀) (le_refl _)
  by_cases htm : t ≤ 2 * Real.pi * (j : ℝ) + Real.pi
  · -- LEFT half: t ∈ [2πj+5π/6, 2πj+π]
    have hleft := hz_left_bound t ⟨ht.1, htm⟩
    -- ρL ≤ ρ_flag j (the budget has ρL + nonneg ≤ ρ_flag)
    have hρL_le : ρL ≤ ρ_flag j := by
      have hbudget := hρ_budget j hj₀
      have hleak_nn : 0 ≤ δw_flag * (p.A * sol.init_α
          * Real.exp (-(sol.init_μ * (1 / 2 : ℝ) ^ p.L))
          * Real.exp (-(DynChiLeak.leakLambda p.cμ p.cα p.L
              * (2 * Real.pi * (j : ℝ) + Real.pi)))
          / DynChiLeak.leakLambda p.cμ p.cα p.L) := by
        apply mul_nonneg hδw_flag
        apply div_nonneg
        · exact mul_nonneg (mul_nonneg (mul_nonneg hA hαinit)
            (Real.exp_pos _).le) (Real.exp_pos _).le
        · exact hlam_pos.le
      linarith
    exact le_trans hleft hρL_le
  · -- RIGHT half: t ∈ (2πj+π, 2πj+7π/6]
    simp only [not_le] at htm
    -- z-start at the junction point
    have hjunction := hz_left_bound (2 * Real.pi * (j : ℝ) + Real.pi)
      ⟨hlstart_le_mid, le_refl _⟩
    -- sin ≤ 0 on [2πj+π, t]
    have hsin : ∀ τ ∈ Set.Icc (2 * Real.pi * (j : ℝ) + Real.pi) t, Real.sin τ ≤ 0 :=
      fun τ hτ => sin_nonpos_read_right j hτ.1 (le_trans hτ.2 ht.2)
    -- w bound on [2πj+π, t]
    have hwsup_right : ∀ τ ∈ Set.Icc (2 * Real.pi * (j : ℝ) + Real.pi) t,
        |sol.w τ flagCoord - E.enc (c (j + 1)) flagCoord| ≤ δw_flag :=
      fun τ hτ => hw_flag τ ⟨le_trans hws_le_mid hτ.1, le_trans hτ.2 ht.2⟩
    -- Z-off hold: contract_z_hold_via_integral with a = 2πj+π, b = t
    have hright := contract_z_hold_via_integral sol flagCoord
      (E.enc (c (j + 1)) flagCoord) (2 * Real.pi * (j : ℝ) + Real.pi) t
      (le_of_lt htm) hmid_nn
      hA hcμ hαinit hμinit hlam_pos hdom hzk_cont hsin hδw_flag hjunction hwsup_right
    -- hright : |z t flagCoord − enc(c(j+1)) flagCoord|
    --        ≤ ρL + δw_flag * (A * α₀ * exp₁ * exp(-λ * (2πj+π)) / λ)
    -- This is exactly the LHS of hρ_budget j hj₀
    exact le_trans hright (hρ_budget j hj₀)

#print axioms contract_w_flag_near_next
#print axioms contract_hz_left_flag
#print axioms contract_flag_z_read_from_contraction

end

end Ripple.BoundedUniversality.BGP
