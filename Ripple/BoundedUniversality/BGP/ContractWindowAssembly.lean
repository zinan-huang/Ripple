/-
Ripple.BoundedUniversality.BGP.ContractWindowAssembly
---------------------------------
The window-aligned assembly: combines the banked Duhamel relaxation holds
(`ContractDuhamelHold`) with the off-phase gate-integral leak bounds
(`ContractGateEnvelope.gate_integral_offphase_U/Z`) into the per-channel
hold-via-integral lemmas the box-free producers need.

The Duhamel bound's moving-target term `δsup·(1−exp(−∫k))` is bounded by
`δsup·∫k` (via `1−exp(−x) ≤ x`), and `∫k` by the off-phase gate-integral
(decaying like `dynChi`).  Net: `|u(b)−M| ≤ E0 + Dz·(C·exp(−λa)/λ)` — the start
error plus a decaying leak term, even though the moving target `z` may be far
(`Dz` large) while the gate is suppressed.
-/

import Ripple.BoundedUniversality.BGP.ContractDuhamelHold
import Ripple.BoundedUniversality.BGP.ContractGateEnvelope

namespace Ripple.BoundedUniversality.BGP

open Real
open Ripple.BoundedUniversality.Core

noncomputable section

variable {d : ℕ} {p : DynGateParams} {sched : PhaseSchedule}
  {F : ℝ → (Fin d → ℝ) → Fin d → ℝ}

/-! ## Gate-phase sin facts for the interface windows.

The strong-hold u-window `[2πj+π/6, 2πj+π/2]` (where `bGateU` is super-suppressed,
`sin ≥ 0`) and the Z-off read sub-window `[2πj+π, 2πj+7π/6]` (`sin ≤ 0`). -/

/-- `sin ≥ 0` on the strong-hold u-window `[2πj+π/6, 2πj+π/2]` (⊆ `[2πj, 2πj+π]`). -/
theorem sin_nonneg_strong_hold (j : ℕ) {t : ℝ}
    (h1 : 2 * Real.pi * (j : ℝ) + Real.pi / 6 ≤ t)
    (h2 : t ≤ 2 * Real.pi * (j : ℝ) + Real.pi / 2) :
    0 ≤ Real.sin t :=
  sin_window_nonneg j (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])

/-- `sin ≤ 0` on the Z-off read sub-window `[2πj+π, 2πj+7π/6]` (⊆ `[2πj+π, 2πj+2π]`). -/
theorem sin_nonpos_read_right (j : ℕ) {t : ℝ}
    (h1 : 2 * Real.pi * (j : ℝ) + Real.pi ≤ t)
    (h2 : t ≤ 2 * Real.pi * (j : ℝ) + 7 * Real.pi / 6) :
    Real.sin t ≤ 0 :=
  sin_window_nonpos j (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])

/-- `α ≥ 0` on `[0,∞)` from `init_α ≥ 0` (via the closed form). -/
private theorem alpha_nonneg_on (sol : DynContractIteratorSol (Fin d) p sched F)
    (hdom : ∀ s : ℝ, 0 ≤ s → s ∈ sched.domain) (hαinit : 0 ≤ sol.init_α)
    {τ : ℝ} (hτ : 0 ≤ τ) : 0 ≤ sol.α τ := by
  rw [contractSol_alpha_eq sol hdom hτ]
  exact mul_nonneg hαinit (Real.exp_pos _).le

/-- **Strong-hold U-tube via the gate integral.**  On a U-off window (`0 ≤ sin`),
`u` stays within `E0 + Dz·(C·exp(−λa)/λ)` of the fixed target `M`, where `E0`
bounds the start error and `Dz` bounds the (possibly far) moving target `z`.  The
leak term decays like `dynChi`. -/
theorem contract_u_hold_via_integral
    (sol : DynContractIteratorSol (Fin d) p sched F)
    (i : Fin d) (M a b : ℝ) (hab : a ≤ b) (ha : 0 ≤ a)
    (hA : 0 ≤ p.A) (hcμ : 0 ≤ p.cμ) (hαinit : 0 ≤ sol.init_α)
    (hμinit : 0 ≤ sol.init_μ)
    (hlam_pos : 0 < DynChiLeak.leakLambda p.cμ p.cα p.L)
    (hdom : ∀ s : ℝ, 0 ≤ s → s ∈ sched.domain)
    (hk_cont : Continuous (uRate sol))
    (hsin : ∀ τ ∈ Set.Icc a b, 0 ≤ Real.sin τ)
    {E0 Dz : ℝ} (hDz : 0 ≤ Dz)
    (hustart : |sol.u a i - M| ≤ E0)
    (hzsup : ∀ τ ∈ Set.Icc a b, |sol.z τ i - M| ≤ Dz) :
    |sol.u b i - M| ≤
      E0 + Dz * (p.A * sol.init_α * Real.exp (-(sol.init_μ * (1 / 2 : ℝ) ^ p.L))
        * Real.exp (-(DynChiLeak.leakLambda p.cμ p.cα p.L * a))
        / DynChiLeak.leakLambda p.cμ p.cα p.L) := by
  have hαnn : ∀ τ ∈ Set.Icc a b, 0 ≤ sol.α τ := fun τ hτ =>
    alpha_nonneg_on sol hdom hαinit (le_trans ha hτ.1)
  have hsubdom : Set.Icc a b ⊆ sched.domain := fun τ hτ =>
    hdom τ (le_trans ha hτ.1)
  -- Duhamel bound
  have hduh := contract_u_duhamel_bound sol i M a b hab hk_cont hA hαnn hsubdom hzsup
  set I := ∫ τ in a..b, uRate sol τ with hIdef
  -- ∫k ≥ 0
  have hI_nonneg : 0 ≤ I := by
    rw [hIdef]
    apply intervalIntegral.integral_nonneg hab
    intro τ hτ
    exact mul_nonneg (mul_nonneg hA (hαnn τ hτ)) (bGateU_pos p.L (sol.μ τ) τ).le
  -- gate-integral bound: I ≤ GB
  have hint : I ≤ p.A * sol.init_α * Real.exp (-(sol.init_μ * (1 / 2 : ℝ) ^ p.L))
        * Real.exp (-(DynChiLeak.leakLambda p.cμ p.cα p.L * a))
        / DynChiLeak.leakLambda p.cμ p.cα p.L := by
    rw [hIdef]
    exact gate_integral_offphase_U sol hdom hA hcμ hαinit hμinit hlam_pos ha hab hsin hk_cont
  -- 1 − exp(−I) ≤ I  and  exp(−I) ≤ 1
  have hexp_le_one : Real.exp (-I) ≤ 1 := by
    rw [Real.exp_le_one_iff]; linarith [hI_nonneg]
  have h1mexp : 1 - Real.exp (-I) ≤ I := by
    have hle := Real.add_one_le_exp (-I)
    linarith
  have hE0nn : 0 ≤ E0 := le_trans (abs_nonneg _) hustart
  set GB := p.A * sol.init_α * Real.exp (-(sol.init_μ * (1 / 2 : ℝ) ^ p.L))
      * Real.exp (-(DynChiLeak.leakLambda p.cμ p.cα p.L * a))
      / DynChiLeak.leakLambda p.cμ p.cα p.L with hGBdef
  calc
    |sol.u b i - M|
        ≤ Real.exp (-I) * |sol.u a i - M| + Dz * (1 - Real.exp (-I)) := hduh
    _ ≤ E0 + Dz * I := by
          have s1 : Real.exp (-I) * |sol.u a i - M| ≤ E0 := by
            calc Real.exp (-I) * |sol.u a i - M|
                ≤ 1 * |sol.u a i - M| :=
                  mul_le_mul_of_nonneg_right hexp_le_one (abs_nonneg _)
              _ = |sol.u a i - M| := one_mul _
              _ ≤ E0 := hustart
          have s2 : Dz * (1 - Real.exp (-I)) ≤ Dz * I :=
            mul_le_mul_of_nonneg_left h1mexp hDz
          linarith
    _ ≤ E0 + Dz * GB := by
          have s3 : Dz * I ≤ Dz * GB := mul_le_mul_of_nonneg_left hint hDz
          linarith

/-- **Z-channel mirror via the gate integral.**  On a Z-off window (`sin ≤ 0`),
`z` stays within `E0 + Dw·(C·exp(−λa)/λ)` of `M`, where `E0` bounds the start
error and `Dw` bounds the moving target `w = F(μ,u)`. -/
theorem contract_z_hold_via_integral
    (sol : DynContractIteratorSol (Fin d) p sched F)
    (i : Fin d) (M a b : ℝ) (hab : a ≤ b) (ha : 0 ≤ a)
    (hA : 0 ≤ p.A) (hcμ : 0 ≤ p.cμ) (hαinit : 0 ≤ sol.init_α)
    (hμinit : 0 ≤ sol.init_μ)
    (hlam_pos : 0 < DynChiLeak.leakLambda p.cμ p.cα p.L)
    (hdom : ∀ s : ℝ, 0 ≤ s → s ∈ sched.domain)
    (hk_cont : Continuous (zRate sol))
    (hsin : ∀ τ ∈ Set.Icc a b, Real.sin τ ≤ 0)
    {E0 Dw : ℝ} (hDw : 0 ≤ Dw)
    (hzstart : |sol.z a i - M| ≤ E0)
    (hwsup : ∀ τ ∈ Set.Icc a b, |sol.w τ i - M| ≤ Dw) :
    |sol.z b i - M| ≤
      E0 + Dw * (p.A * sol.init_α * Real.exp (-(sol.init_μ * (1 / 2 : ℝ) ^ p.L))
        * Real.exp (-(DynChiLeak.leakLambda p.cμ p.cα p.L * a))
        / DynChiLeak.leakLambda p.cμ p.cα p.L) := by
  have hαnn : ∀ τ ∈ Set.Icc a b, 0 ≤ sol.α τ := fun τ hτ =>
    alpha_nonneg_on sol hdom hαinit (le_trans ha hτ.1)
  have hsubdom : Set.Icc a b ⊆ sched.domain := fun τ hτ =>
    hdom τ (le_trans ha hτ.1)
  have hduh := contract_z_duhamel_bound sol i M a b hab hk_cont hA hαnn hsubdom hwsup
  set I := ∫ τ in a..b, zRate sol τ with hIdef
  have hI_nonneg : 0 ≤ I := by
    rw [hIdef]
    apply intervalIntegral.integral_nonneg hab
    intro τ hτ
    exact mul_nonneg (mul_nonneg hA (hαnn τ hτ)) (bGateZ_pos p.L (sol.μ τ) τ).le
  have hint : I ≤ p.A * sol.init_α * Real.exp (-(sol.init_μ * (1 / 2 : ℝ) ^ p.L))
        * Real.exp (-(DynChiLeak.leakLambda p.cμ p.cα p.L * a))
        / DynChiLeak.leakLambda p.cμ p.cα p.L := by
    rw [hIdef]
    exact gate_integral_offphase_Z sol hdom hA hcμ hαinit hμinit hlam_pos ha hab hsin hk_cont
  have hexp_le_one : Real.exp (-I) ≤ 1 := by
    rw [Real.exp_le_one_iff]; linarith [hI_nonneg]
  have h1mexp : 1 - Real.exp (-I) ≤ I := by
    have hle := Real.add_one_le_exp (-I)
    linarith
  have hE0nn : 0 ≤ E0 := le_trans (abs_nonneg _) hzstart
  set GB := p.A * sol.init_α * Real.exp (-(sol.init_μ * (1 / 2 : ℝ) ^ p.L))
      * Real.exp (-(DynChiLeak.leakLambda p.cμ p.cα p.L * a))
      / DynChiLeak.leakLambda p.cμ p.cα p.L with hGBdef
  calc
    |sol.z b i - M|
        ≤ Real.exp (-I) * |sol.z a i - M| + Dw * (1 - Real.exp (-I)) := hduh
    _ ≤ E0 + Dw * I := by
          have s1 : Real.exp (-I) * |sol.z a i - M| ≤ E0 := by
            calc Real.exp (-I) * |sol.z a i - M|
                ≤ 1 * |sol.z a i - M| :=
                  mul_le_mul_of_nonneg_right hexp_le_one (abs_nonneg _)
              _ = |sol.z a i - M| := one_mul _
              _ ≤ E0 := hzstart
          have s2 : Dw * (1 - Real.exp (-I)) ≤ Dw * I :=
            mul_le_mul_of_nonneg_left h1mexp hDw
          linarith
    _ ≤ E0 + Dw * GB := by
          have s3 : Dw * I ≤ Dw * GB := mul_le_mul_of_nonneg_left hint hDw
          linarith

/-- **The moving target `w = F(μ,u)` tracks the NEXT config.**  From the robust-step
diagonal (`sampled_zpow_bound`) + `sol.target_eq` (`w = S.F μ u`): if `u` is in the
radius-tube of `enc(c j)`, then `|w − enc(c(j+1))| ≤ k^δ·|u − enc(c j)| + epsF(μ)`.
This supplies the `Dw` (moving-target deviation from the NEXT config) for
`contract_z_hold_via_integral` with `M = enc(c(j+1))`. -/
theorem contract_w_near_next
    {nS : ℕ} {Conf : Type} [Primcodable Conf] {Mch : DiscreteMachine Conf}
    {E : StackMachineEncoding d nS Mch}
    (S : RobustStepContract Mch E)
    (sol : DynContractIteratorSol (Fin d) p sched S.F)
    (c : ℕ → Conf) (j : ℕ) {τ : ℝ} (hτdom : τ ∈ sched.domain)
    (hcstep : c (j + 1) = Mch.step (c j))
    (hmu : S.mu_min ≤ sol.μ τ)
    (htube : EncodingTube E (S.radius (sol.μ τ)) (c j) (sol.u τ))
    (i : Fin d) :
    |sol.w τ i - E.enc (c (j + 1)) i| ≤
      (E.k : ℝ) ^ E.coordDelta (c j) i * |sol.u τ i - E.enc (c j) i| + S.epsF (sol.μ τ) i := by
  have hw : sol.w τ = S.F (sol.μ τ) (sol.u τ) := sol.target_eq τ hτdom
  rw [hcstep, hw]
  exact S.sampled_zpow_bound hmu htube i

/-- **The next-config z-read tube (capstone).**  On a Z-off window `[a,b]`, `z`
stays within `E0 + Dw·(C·exp(−λa)/λ)` of the NEXT config `enc(c(j+1))`, where `E0`
bounds the z start error (vs the next config) and `Dw` bounds the robust-step
moving-target deviation `k^δ·|u−enc(c j)| + epsF(μ)` (supplied by
`contract_w_near_next` from the u-tube).  This is the producer-corrected z-read
(`enc(c(j+1))`, not the impossible `enc(c j)`), built from the banked Duhamel/gate
tools + `RobustStepContract`. -/
theorem contract_z_read_next_config
    {nS : ℕ} {Conf : Type} [Primcodable Conf] {Mch : DiscreteMachine Conf}
    {E : StackMachineEncoding d nS Mch}
    (S : RobustStepContract Mch E)
    (sol : DynContractIteratorSol (Fin d) p sched S.F)
    (c : ℕ → Conf) (j : ℕ) (i : Fin d) {a b : ℝ} (hab : a ≤ b) (ha : 0 ≤ a)
    (hA : 0 ≤ p.A) (hcμ : 0 ≤ p.cμ) (hαinit : 0 ≤ sol.init_α)
    (hμinit : 0 ≤ sol.init_μ)
    (hlam_pos : 0 < DynChiLeak.leakLambda p.cμ p.cα p.L)
    (hdom : ∀ s : ℝ, 0 ≤ s → s ∈ sched.domain)
    (hk_cont : Continuous (zRate sol))
    (hsin : ∀ τ ∈ Set.Icc a b, Real.sin τ ≤ 0)
    (hcstep : c (j + 1) = Mch.step (c j))
    {E0 Dw : ℝ} (hDw : 0 ≤ Dw)
    (hzstart : |sol.z a i - E.enc (c (j + 1)) i| ≤ E0)
    (hmuLB : ∀ τ ∈ Set.Icc a b, S.mu_min ≤ sol.μ τ)
    (hutube : ∀ τ ∈ Set.Icc a b, EncodingTube E (S.radius (sol.μ τ)) (c j) (sol.u τ))
    (hwbound : ∀ τ ∈ Set.Icc a b,
      (E.k : ℝ) ^ E.coordDelta (c j) i * |sol.u τ i - E.enc (c j) i| + S.epsF (sol.μ τ) i ≤ Dw) :
    |sol.z b i - E.enc (c (j + 1)) i| ≤
      E0 + Dw * (p.A * sol.init_α * Real.exp (-(sol.init_μ * (1 / 2 : ℝ) ^ p.L))
        * Real.exp (-(DynChiLeak.leakLambda p.cμ p.cα p.L * a))
        / DynChiLeak.leakLambda p.cμ p.cα p.L) := by
  refine contract_z_hold_via_integral sol i (E.enc (c (j + 1)) i) a b hab ha
    hA hcμ hαinit hμinit hlam_pos hdom hk_cont hsin hDw hzstart ?_
  intro τ hτ
  have hw := contract_w_near_next S sol c j (hdom τ (le_trans ha hτ.1)) hcstep
    (hmuLB τ hτ) (hutube τ hτ) i
  exact le_trans hw (hwbound τ hτ)

end

end Ripple.BoundedUniversality.BGP
