/-
Ripple.BoundedUniversality.BGP.ContractGateMassLower
--------------------------------
The contract-sol ON-phase gate-mass LOWER bound — the `hΛ` input the write-settle
producers (`ContractZWriteSettle.contract_hz_left` / `contract_hu_write_next`)
consume.  This is the dual of the banked off-phase envelope
`ContractGateEnvelope.gate_integral_offphase_Z` (an UPPER bound), ported from the
selector template `SelectorReplicatorSettledZ.write_Z_integral_lower_repl`,
generalized to nonzero `init_α`/`init_μ`.

Mechanism: on a `sin ≥ √2/2` sub-window the z-gate `rPulse` is bounded above by
`rmax := (1−√2/2)/2`, so the integrand
`zRate = A·α·exp(−μ·rPulse) ≥ A·init_α·exp(cα·a)·exp(−(init_μ+cμ·b)·rmax)`
is bounded below by a positive constant whose integral over a fixed-width window
grows like `exp((cα − cμ·rmax)·a)`.  At `bgpParams38` (`cα = 3/8`, `cμ = 1`,
`L = 1`) the growth rate `cα − cμ·rmax > cα − cμ·(1/4) > 0` (since
`rmax ≈ 0.146 < 1/4`, cf. `bgpParams38_kappa_growth_regime`), so the mass `→ ∞`.

ABSOLUTE: no sorry/admit/native_decide/axiom.
-/

import Ripple.BoundedUniversality.BGP.ContractWindowAssembly
import Ripple.BoundedUniversality.BGP.SelectorWriteReach

namespace Ripple.BoundedUniversality.BGP

open Ripple.BoundedUniversality.Core

noncomputable section

variable {d : ℕ} {p : DynGateParams} {sched : PhaseSchedule}
  {F : ℝ → (Fin d → ℝ) → Fin d → ℝ}

/-- Inline trivial: on the `sin ≥ √2/2` window, `rPulse 1 t ≤ (1−√2/2)/2`
(`rPulse 1 t = (1 − sin t)/2`). -/
private theorem rPulse_le_rmax {t : ℝ} (hs : Real.sqrt 2 / 2 ≤ Real.sin t) :
    rPulse 1 t ≤ (1 - Real.sqrt 2 / 2) / 2 := by
  unfold rPulse
  simp only [pow_one]
  linarith [Real.sin_le_one t]

/-- **Contract-sol gate-mass lower bound** on a `sin ≥ √2/2` sub-window.  Port of
`write_Z_integral_lower_repl` to `DynContractIteratorSol`, generalized to nonzero
`init_α`/`init_μ`.  Combined with nonneg-extension to the full write window, this
supplies the `Λ` input of `contract_hz_left`/`contract_hu_write_next`. -/
theorem contract_writeZ_integral_lower
    (sol : DynContractIteratorSol (Fin d) p sched F)
    {a b : ℝ} (hab : a ≤ b) (ha0 : 0 ≤ a)
    (hA : 0 ≤ p.A) (hcμ : 0 ≤ p.cμ) (hcα : 0 ≤ p.cα)
    (hαinit : 0 ≤ sol.init_α) (hμinit : 0 ≤ sol.init_μ)
    (hpL : p.L = 1)
    (hdom : ∀ s : ℝ, 0 ≤ s → s ∈ sched.domain)
    (hg_cont : Continuous (zRate sol))
    (hsin : ∀ t ∈ Set.Icc a b, Real.sqrt 2 / 2 ≤ Real.sin t) :
    p.A * sol.init_α * Real.exp (p.cα * a)
        * Real.exp (-((sol.init_μ + p.cμ * b) * ((1 - Real.sqrt 2 / 2) / 2)))
        * (b - a)
      ≤ ∫ t in a..b, zRate sol t := by
  set rmax : ℝ := (1 - Real.sqrt 2 / 2) / 2 with hrmax
  have hrmax0 : 0 ≤ rmax := by
    have h2 : Real.sqrt 2 ≤ 2 := by
      have := Real.sqrt_le_sqrt (by norm_num : (2 : ℝ) ≤ 4)
      simpa [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq] using this
    rw [hrmax]
    nlinarith [Real.sqrt_nonneg 2]
  -- pointwise lower bound: zRate ≥ positive constant
  have hconstlb : ∀ t ∈ Set.Icc a b,
      p.A * sol.init_α * Real.exp (p.cα * a)
          * Real.exp (-((sol.init_μ + p.cμ * b) * rmax))
        ≤ zRate sol t := by
    intro t ht
    have hat : a ≤ t := ht.1
    have htb : t ≤ b := ht.2
    have ht0 : 0 ≤ t := le_trans ha0 hat
    unfold zRate
    rw [contractSol_alpha_eq sol hdom ht0, contractSol_mu_eq sol hdom ht0, hpL]
    unfold bGateZ
    have hαle : Real.exp (p.cα * a) ≤ Real.exp (p.cα * t) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hat hcα)
    have hrp : rPulse 1 t ≤ rmax := rPulse_le_rmax (hsin t ht)
    have hrp0 : 0 ≤ rPulse 1 t := rPulse_nonneg 1 t
    have hμmono : (sol.init_μ + p.cμ * t) * rPulse 1 t
        ≤ (sol.init_μ + p.cμ * b) * rmax := by
      have h1 : sol.init_μ + p.cμ * t ≤ sol.init_μ + p.cμ * b := by
        have := mul_le_mul_of_nonneg_left htb hcμ; linarith
      have h2 : 0 ≤ sol.init_μ + p.cμ * t := by positivity
      nlinarith [h1, h2, hrp, hrp0, hrmax0]
    have hgate : Real.exp (-((sol.init_μ + p.cμ * b) * rmax))
        ≤ Real.exp (-((sol.init_μ + p.cμ * t) * rPulse 1 t)) :=
      Real.exp_le_exp.mpr (by linarith [hμmono])
    have hmul := mul_le_mul hαle hgate (Real.exp_pos _).le (Real.exp_pos _).le
    have hAα : 0 ≤ p.A * sol.init_α := mul_nonneg hA hαinit
    calc p.A * sol.init_α * Real.exp (p.cα * a)
            * Real.exp (-((sol.init_μ + p.cμ * b) * rmax))
        = (p.A * sol.init_α)
            * (Real.exp (p.cα * a) * Real.exp (-((sol.init_μ + p.cμ * b) * rmax))) := by
          ring
      _ ≤ (p.A * sol.init_α)
            * (Real.exp (p.cα * t)
              * Real.exp (-((sol.init_μ + p.cμ * t) * rPulse 1 t))) :=
          mul_le_mul_of_nonneg_left hmul hAα
      _ = p.A * (sol.init_α * Real.exp (p.cα * t))
            * Real.exp (-((sol.init_μ + p.cμ * t) * rPulse 1 t)) := by ring
  -- integrate the constant lower bound over [a,b]
  have hconst_int : (∫ _t in a..b, p.A * sol.init_α * Real.exp (p.cα * a)
        * Real.exp (-((sol.init_μ + p.cμ * b) * rmax)))
      = p.A * sol.init_α * Real.exp (p.cα * a)
        * Real.exp (-((sol.init_μ + p.cμ * b) * rmax)) * (b - a) := by
    rw [intervalIntegral.integral_const, smul_eq_mul]; ring
  calc p.A * sol.init_α * Real.exp (p.cα * a)
          * Real.exp (-((sol.init_μ + p.cμ * b) * rmax)) * (b - a)
      = ∫ _t in a..b, p.A * sol.init_α * Real.exp (p.cα * a)
          * Real.exp (-((sol.init_μ + p.cμ * b) * rmax)) := hconst_int.symm
    _ ≤ ∫ t in a..b, zRate sol t :=
        intervalIntegral.integral_mono_on hab _root_.intervalIntegrable_const
          (hg_cont.intervalIntegrable a b) hconstlb

/-- Explicit gate-mass lower bound value over the z-write window of cycle `j`
(the `Λ` input the write-settle producers consume), from the `[π/4,3π/4]`
sub-window of width `π/2`. -/
def contractWriteMassLB (sol : DynContractIteratorSol (Fin d) p sched F) (j : ℕ) : ℝ :=
  p.A * sol.init_α * Real.exp (p.cα * (2 * Real.pi * (j : ℝ) + Real.pi / 4))
    * Real.exp (-((sol.init_μ + p.cμ * (2 * Real.pi * (j : ℝ) + 3 * Real.pi / 4))
        * ((1 - Real.sqrt 2 / 2) / 2)))
    * (Real.pi / 2)

/-- **The explicit lower bound is `≤` the full z-write-window gate mass.**  Lower-
bounds the `sin ≥ √2/2` sub-window `[2πj+π/4, 2πj+3π/4]` via
`contract_writeZ_integral_lower`, then extends to the full write window
`[2πj+π/6, 2πj+5π/6]` by nonneg-integrand monotonicity. -/
theorem contractWriteMassLB_le_integral
    (sol : DynContractIteratorSol (Fin d) p sched F) (j : ℕ)
    (hA : 0 ≤ p.A) (hcμ : 0 ≤ p.cμ) (hcα : 0 ≤ p.cα)
    (hαinit : 0 ≤ sol.init_α) (hμinit : 0 ≤ sol.init_μ)
    (hpL : p.L = 1)
    (hdom : ∀ s : ℝ, 0 ≤ s → s ∈ sched.domain)
    (hg_cont : Continuous (zRate sol)) :
    contractWriteMassLB sol j
      ≤ ∫ t in (2 * Real.pi * (j : ℝ) + Real.pi / 6)..(2 * Real.pi * (j : ℝ)
          + 5 * Real.pi / 6), zRate sol t := by
  have hπ := Real.pi_pos
  have hjnn : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  have h_a4_b4 : 2 * Real.pi * (j : ℝ) + Real.pi / 4
      ≤ 2 * Real.pi * (j : ℝ) + 3 * Real.pi / 4 := by nlinarith
  have h_a4_0 : (0 : ℝ) ≤ 2 * Real.pi * (j : ℝ) + Real.pi / 4 := by positivity
  have h_a6_a4 : 2 * Real.pi * (j : ℝ) + Real.pi / 6
      ≤ 2 * Real.pi * (j : ℝ) + Real.pi / 4 := by nlinarith
  have h_b4_b6 : 2 * Real.pi * (j : ℝ) + 3 * Real.pi / 4
      ≤ 2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6 := by nlinarith
  have h_a6_0 : (0 : ℝ) ≤ 2 * Real.pi * (j : ℝ) + Real.pi / 6 := by positivity
  have hsin : ∀ t ∈ Set.Icc (2 * Real.pi * (j : ℝ) + Real.pi / 4)
      (2 * Real.pi * (j : ℝ) + 3 * Real.pi / 4), Real.sqrt 2 / 2 ≤ Real.sin t := by
    intro t ht
    exact sin_window_ge_sqrt2 j ht.1 ht.2
  have hlow := contract_writeZ_integral_lower sol h_a4_b4 h_a4_0 hA hcμ hcα hαinit
    hμinit hpL hdom hg_cont hsin
  -- contractWriteMassLB = hlow's LHS (width 3π/4 − π/4 = π/2)
  have hLB_le : contractWriteMassLB sol j
      ≤ ∫ t in (2 * Real.pi * (j : ℝ) + Real.pi / 4)..(2 * Real.pi * (j : ℝ)
          + 3 * Real.pi / 4), zRate sol t := by
    rw [contractWriteMassLB,
      show (Real.pi / 2) = (2 * Real.pi * (j : ℝ) + 3 * Real.pi / 4)
        - (2 * Real.pi * (j : ℝ) + Real.pi / 4) from by ring]
    exact hlow
  -- nonneg-integrand extension to the full write window
  have hz_nn : ∀ t, 0 ≤ t → 0 ≤ zRate sol t := by
    intro t ht
    unfold zRate
    rw [contractSol_alpha_eq sol hdom ht]
    exact mul_nonneg (mul_nonneg hA (mul_nonneg hαinit (Real.exp_pos _).le))
      (bGateZ_pos p.L (sol.μ t) t).le
  have hII : ∀ x y : ℝ, IntervalIntegrable (zRate sol) MeasureTheory.volume x y :=
    fun x y => hg_cont.intervalIntegrable x y
  have hadd1 : (∫ t in (2 * Real.pi * (j : ℝ) + Real.pi / 6)..(2 * Real.pi * (j : ℝ)
        + Real.pi / 4), zRate sol t)
      + (∫ t in (2 * Real.pi * (j : ℝ) + Real.pi / 4)..(2 * Real.pi * (j : ℝ)
        + 3 * Real.pi / 4), zRate sol t)
      = ∫ t in (2 * Real.pi * (j : ℝ) + Real.pi / 6)..(2 * Real.pi * (j : ℝ)
        + 3 * Real.pi / 4), zRate sol t :=
    intervalIntegral.integral_add_adjacent_intervals (hII _ _) (hII _ _)
  have hadd2 : (∫ t in (2 * Real.pi * (j : ℝ) + Real.pi / 6)..(2 * Real.pi * (j : ℝ)
        + 3 * Real.pi / 4), zRate sol t)
      + (∫ t in (2 * Real.pi * (j : ℝ) + 3 * Real.pi / 4)..(2 * Real.pi * (j : ℝ)
        + 5 * Real.pi / 6), zRate sol t)
      = ∫ t in (2 * Real.pi * (j : ℝ) + Real.pi / 6)..(2 * Real.pi * (j : ℝ)
        + 5 * Real.pi / 6), zRate sol t :=
    intervalIntegral.integral_add_adjacent_intervals (hII _ _) (hII _ _)
  have hnn1 : 0 ≤ ∫ t in (2 * Real.pi * (j : ℝ) + Real.pi / 6)..(2 * Real.pi * (j : ℝ)
      + Real.pi / 4), zRate sol t :=
    intervalIntegral.integral_nonneg h_a6_a4 (fun t ht => hz_nn t (le_trans h_a6_0 ht.1))
  have hnn3 : 0 ≤ ∫ t in (2 * Real.pi * (j : ℝ) + 3 * Real.pi / 4)..(2 * Real.pi * (j : ℝ)
      + 5 * Real.pi / 6), zRate sol t :=
    intervalIntegral.integral_nonneg h_b4_b6
      (fun t ht => hz_nn t (le_trans (le_trans h_a4_0 h_a4_b4) ht.1))
  have hext : (∫ t in (2 * Real.pi * (j : ℝ) + Real.pi / 4)..(2 * Real.pi * (j : ℝ)
        + 3 * Real.pi / 4), zRate sol t)
      ≤ ∫ t in (2 * Real.pi * (j : ℝ) + Real.pi / 6)..(2 * Real.pi * (j : ℝ)
        + 5 * Real.pi / 6), zRate sol t := by
    have hsplit : (∫ t in (2 * Real.pi * (j : ℝ) + Real.pi / 6)..(2 * Real.pi * (j : ℝ)
          + 5 * Real.pi / 6), zRate sol t)
        = (∫ t in (2 * Real.pi * (j : ℝ) + Real.pi / 6)..(2 * Real.pi * (j : ℝ)
            + Real.pi / 4), zRate sol t)
          + (∫ t in (2 * Real.pi * (j : ℝ) + Real.pi / 4)..(2 * Real.pi * (j : ℝ)
            + 3 * Real.pi / 4), zRate sol t)
          + (∫ t in (2 * Real.pi * (j : ℝ) + 3 * Real.pi / 4)..(2 * Real.pi * (j : ℝ)
            + 5 * Real.pi / 6), zRate sol t) := by
      rw [← hadd2, ← hadd1]
    rw [hsplit]; linarith
  exact le_trans hLB_le hext

/-- **The explicit gate-mass lower bound diverges** (`Λ_j → ∞`), given the growth
gap `cα − cμ·rmax > 0` (at `bgpParams38`: `rmax ≈ 0.146 < 1/4`, and
`cα − cμ·(1/4) > 0` by `bgpParams38_kappa_growth_regime`).  This is the
convergence input (`exp(−Λ_j)·B → 0`) the warmed headline consumes. -/
theorem contractWriteMassLB_tendsto
    (sol : DynContractIteratorSol (Fin d) p sched F)
    (hApos : 0 < p.A) (hαpos : 0 < sol.init_α)
    (hgrow : 0 < p.cα - p.cμ * ((1 - Real.sqrt 2 / 2) / 2)) :
    Filter.Tendsto (contractWriteMassLB sol) Filter.atTop Filter.atTop := by
  have hπ := Real.pi_pos
  set rmax : ℝ := (1 - Real.sqrt 2 / 2) / 2 with hrmax
  set C : ℝ := p.A * sol.init_α * (Real.pi / 2) with hC
  have hCpos : 0 < C := by rw [hC]; positivity
  set K : ℝ := p.cα * (Real.pi / 4)
      - (sol.init_μ + p.cμ * (3 * Real.pi / 4)) * rmax with hK
  set sl : ℝ := 2 * Real.pi * (p.cα - p.cμ * rmax) with hsl
  have hslpos : 0 < sl := by rw [hsl]; exact mul_pos (by positivity) hgrow
  have hEq : ∀ j : ℕ, contractWriteMassLB sol j = C * Real.exp (sl * (j : ℝ) + K) := by
    intro j
    rw [contractWriteMassLB, hC, hsl, hK]
    rw [show 2 * Real.pi * (p.cα - p.cμ * rmax) * (j : ℝ)
          + (p.cα * (Real.pi / 4) - (sol.init_μ + p.cμ * (3 * Real.pi / 4)) * rmax)
        = p.cα * (2 * Real.pi * (j : ℝ) + Real.pi / 4)
          + (-((sol.init_μ + p.cμ * (2 * Real.pi * (j : ℝ) + 3 * Real.pi / 4)) * rmax))
        from by ring]
    rw [Real.exp_add]
    ring
  rw [Filter.tendsto_congr hEq]
  apply Filter.Tendsto.const_mul_atTop hCpos
  apply Real.tendsto_exp_atTop.comp
  apply Filter.tendsto_atTop_add_const_right
  exact Filter.Tendsto.const_mul_atTop hslpos tendsto_natCast_atTop_atTop

/-! ## U-channel mirror: the copy-window gate-mass lower bound (`uRate`/`bGateU`).

`bGateU L m t = exp(−m · qPulse L t)`; on the `sin ≤ −√2/2` sub-window
`[2πj+5π/4, 2πj+7π/4]` (`⊆` the copy window `[2πj+7π/6, 2π(j+1)+π/6]`) the
U-gate `qPulse` is bounded above by `rmax`, giving the same growth mechanism. -/

/-- **Contract-sol U-gate-mass lower bound** on a `sin ≤ −√2/2` sub-window
(mirror of `contract_writeZ_integral_lower` with `qPulse`/`bGateU`). -/
theorem contract_writeU_integral_lower
    (sol : DynContractIteratorSol (Fin d) p sched F)
    {a b : ℝ} (hab : a ≤ b) (ha0 : 0 ≤ a)
    (hA : 0 ≤ p.A) (hcμ : 0 ≤ p.cμ) (hcα : 0 ≤ p.cα)
    (hαinit : 0 ≤ sol.init_α) (hμinit : 0 ≤ sol.init_μ)
    (hpL : p.L = 1)
    (hdom : ∀ s : ℝ, 0 ≤ s → s ∈ sched.domain)
    (hg_cont : Continuous (uRate sol))
    (hsin : ∀ t ∈ Set.Icc a b, Real.sin t ≤ -(Real.sqrt 2 / 2)) :
    p.A * sol.init_α * Real.exp (p.cα * a)
        * Real.exp (-((sol.init_μ + p.cμ * b) * ((1 - Real.sqrt 2 / 2) / 2)))
        * (b - a)
      ≤ ∫ t in a..b, uRate sol t := by
  set rmax : ℝ := (1 - Real.sqrt 2 / 2) / 2 with hrmax
  have hrmax0 : 0 ≤ rmax := by
    have h2 : Real.sqrt 2 ≤ 2 := by
      have := Real.sqrt_le_sqrt (by norm_num : (2 : ℝ) ≤ 4)
      simpa [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq] using this
    rw [hrmax]
    nlinarith [Real.sqrt_nonneg 2]
  have hconstlb : ∀ t ∈ Set.Icc a b,
      p.A * sol.init_α * Real.exp (p.cα * a)
          * Real.exp (-((sol.init_μ + p.cμ * b) * rmax))
        ≤ uRate sol t := by
    intro t ht
    have hat : a ≤ t := ht.1
    have htb : t ≤ b := ht.2
    have ht0 : 0 ≤ t := le_trans ha0 hat
    unfold uRate
    rw [contractSol_alpha_eq sol hdom ht0, contractSol_mu_eq sol hdom ht0, hpL]
    unfold bGateU
    have hαle : Real.exp (p.cα * a) ≤ Real.exp (p.cα * t) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hat hcα)
    have hqp : qPulse 1 t ≤ rmax := qPulse_le_sqrt2_window (hsin t ht)
    have hqp0 : 0 ≤ qPulse 1 t := qPulse_nonneg 1 t
    have hμmono : (sol.init_μ + p.cμ * t) * qPulse 1 t
        ≤ (sol.init_μ + p.cμ * b) * rmax := by
      have h1 : sol.init_μ + p.cμ * t ≤ sol.init_μ + p.cμ * b := by
        have := mul_le_mul_of_nonneg_left htb hcμ; linarith
      have h2 : 0 ≤ sol.init_μ + p.cμ * t := by positivity
      nlinarith [h1, h2, hqp, hqp0, hrmax0]
    have hgate : Real.exp (-((sol.init_μ + p.cμ * b) * rmax))
        ≤ Real.exp (-((sol.init_μ + p.cμ * t) * qPulse 1 t)) :=
      Real.exp_le_exp.mpr (by linarith [hμmono])
    have hmul := mul_le_mul hαle hgate (Real.exp_pos _).le (Real.exp_pos _).le
    have hAα : 0 ≤ p.A * sol.init_α := mul_nonneg hA hαinit
    calc p.A * sol.init_α * Real.exp (p.cα * a)
            * Real.exp (-((sol.init_μ + p.cμ * b) * rmax))
        = (p.A * sol.init_α)
            * (Real.exp (p.cα * a) * Real.exp (-((sol.init_μ + p.cμ * b) * rmax))) := by
          ring
      _ ≤ (p.A * sol.init_α)
            * (Real.exp (p.cα * t)
              * Real.exp (-((sol.init_μ + p.cμ * t) * qPulse 1 t))) :=
          mul_le_mul_of_nonneg_left hmul hAα
      _ = p.A * (sol.init_α * Real.exp (p.cα * t))
            * Real.exp (-((sol.init_μ + p.cμ * t) * qPulse 1 t)) := by ring
  have hconst_int : (∫ _t in a..b, p.A * sol.init_α * Real.exp (p.cα * a)
        * Real.exp (-((sol.init_μ + p.cμ * b) * rmax)))
      = p.A * sol.init_α * Real.exp (p.cα * a)
        * Real.exp (-((sol.init_μ + p.cμ * b) * rmax)) * (b - a) := by
    rw [intervalIntegral.integral_const, smul_eq_mul]; ring
  calc p.A * sol.init_α * Real.exp (p.cα * a)
          * Real.exp (-((sol.init_μ + p.cμ * b) * rmax)) * (b - a)
      = ∫ _t in a..b, p.A * sol.init_α * Real.exp (p.cα * a)
          * Real.exp (-((sol.init_μ + p.cμ * b) * rmax)) := hconst_int.symm
    _ ≤ ∫ t in a..b, uRate sol t :=
        intervalIntegral.integral_mono_on hab _root_.intervalIntegrable_const
          (hg_cont.intervalIntegrable a b) hconstlb

/-- Explicit U-gate-mass lower bound over the copy window of cycle `j`
(`[2πj+5π/4, 2πj+7π/4]` sub-window, width `π/2`). -/
def contractCopyMassLB (sol : DynContractIteratorSol (Fin d) p sched F) (j : ℕ) : ℝ :=
  p.A * sol.init_α * Real.exp (p.cα * (2 * Real.pi * (j : ℝ) + 5 * Real.pi / 4))
    * Real.exp (-((sol.init_μ + p.cμ * (2 * Real.pi * (j : ℝ) + 7 * Real.pi / 4))
        * ((1 - Real.sqrt 2 / 2) / 2)))
    * (Real.pi / 2)

/-- The explicit U lower bound is `≤` the full copy-window gate mass
`[2πj+7π/6, 2π(j+1)+π/6]`. -/
theorem contractCopyMassLB_le_integral
    (sol : DynContractIteratorSol (Fin d) p sched F) (j : ℕ)
    (hA : 0 ≤ p.A) (hcμ : 0 ≤ p.cμ) (hcα : 0 ≤ p.cα)
    (hαinit : 0 ≤ sol.init_α) (hμinit : 0 ≤ sol.init_μ)
    (hpL : p.L = 1)
    (hdom : ∀ s : ℝ, 0 ≤ s → s ∈ sched.domain)
    (hg_cont : Continuous (uRate sol)) :
    contractCopyMassLB sol j
      ≤ ∫ t in (2 * Real.pi * (j : ℝ) + 7 * Real.pi / 6)..(2 * Real.pi
          * ((j + 1 : ℕ) : ℝ) + Real.pi / 6), uRate sol t := by
  have hπ := Real.pi_pos
  have hjnn : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  have hcast : (2 * Real.pi * ((j + 1 : ℕ) : ℝ) + Real.pi / 6)
      = 2 * Real.pi * (j : ℝ) + 13 * Real.pi / 6 := by push_cast; ring
  rw [hcast]
  have h_a4_b4 : 2 * Real.pi * (j : ℝ) + 5 * Real.pi / 4
      ≤ 2 * Real.pi * (j : ℝ) + 7 * Real.pi / 4 := by nlinarith
  have h_a4_0 : (0 : ℝ) ≤ 2 * Real.pi * (j : ℝ) + 5 * Real.pi / 4 := by positivity
  have h_a6_a4 : 2 * Real.pi * (j : ℝ) + 7 * Real.pi / 6
      ≤ 2 * Real.pi * (j : ℝ) + 5 * Real.pi / 4 := by nlinarith
  have h_b4_b6 : 2 * Real.pi * (j : ℝ) + 7 * Real.pi / 4
      ≤ 2 * Real.pi * (j : ℝ) + 13 * Real.pi / 6 := by nlinarith
  have h_a6_0 : (0 : ℝ) ≤ 2 * Real.pi * (j : ℝ) + 7 * Real.pi / 6 := by positivity
  have hsin : ∀ t ∈ Set.Icc (2 * Real.pi * (j : ℝ) + 5 * Real.pi / 4)
      (2 * Real.pi * (j : ℝ) + 7 * Real.pi / 4), Real.sin t ≤ -(Real.sqrt 2 / 2) := by
    intro t ht
    exact sin_window_le_neg_sqrt2 j ht.1 ht.2
  have hlow := contract_writeU_integral_lower sol h_a4_b4 h_a4_0 hA hcμ hcα hαinit
    hμinit hpL hdom hg_cont hsin
  have hLB_le : contractCopyMassLB sol j
      ≤ ∫ t in (2 * Real.pi * (j : ℝ) + 5 * Real.pi / 4)..(2 * Real.pi * (j : ℝ)
          + 7 * Real.pi / 4), uRate sol t := by
    rw [contractCopyMassLB,
      show (Real.pi / 2) = (2 * Real.pi * (j : ℝ) + 7 * Real.pi / 4)
        - (2 * Real.pi * (j : ℝ) + 5 * Real.pi / 4) from by ring]
    exact hlow
  have hu_nn : ∀ t, 0 ≤ t → 0 ≤ uRate sol t := by
    intro t ht
    unfold uRate
    rw [contractSol_alpha_eq sol hdom ht]
    exact mul_nonneg (mul_nonneg hA (mul_nonneg hαinit (Real.exp_pos _).le))
      (bGateU_pos p.L (sol.μ t) t).le
  have hII : ∀ x y : ℝ, IntervalIntegrable (uRate sol) MeasureTheory.volume x y :=
    fun x y => hg_cont.intervalIntegrable x y
  have hadd1 : (∫ t in (2 * Real.pi * (j : ℝ) + 7 * Real.pi / 6)..(2 * Real.pi * (j : ℝ)
        + 5 * Real.pi / 4), uRate sol t)
      + (∫ t in (2 * Real.pi * (j : ℝ) + 5 * Real.pi / 4)..(2 * Real.pi * (j : ℝ)
        + 7 * Real.pi / 4), uRate sol t)
      = ∫ t in (2 * Real.pi * (j : ℝ) + 7 * Real.pi / 6)..(2 * Real.pi * (j : ℝ)
        + 7 * Real.pi / 4), uRate sol t :=
    intervalIntegral.integral_add_adjacent_intervals (hII _ _) (hII _ _)
  have hadd2 : (∫ t in (2 * Real.pi * (j : ℝ) + 7 * Real.pi / 6)..(2 * Real.pi * (j : ℝ)
        + 7 * Real.pi / 4), uRate sol t)
      + (∫ t in (2 * Real.pi * (j : ℝ) + 7 * Real.pi / 4)..(2 * Real.pi * (j : ℝ)
        + 13 * Real.pi / 6), uRate sol t)
      = ∫ t in (2 * Real.pi * (j : ℝ) + 7 * Real.pi / 6)..(2 * Real.pi * (j : ℝ)
        + 13 * Real.pi / 6), uRate sol t :=
    intervalIntegral.integral_add_adjacent_intervals (hII _ _) (hII _ _)
  have hnn1 : 0 ≤ ∫ t in (2 * Real.pi * (j : ℝ) + 7 * Real.pi / 6)..(2 * Real.pi * (j : ℝ)
      + 5 * Real.pi / 4), uRate sol t :=
    intervalIntegral.integral_nonneg h_a6_a4 (fun t ht => hu_nn t (le_trans h_a6_0 ht.1))
  have hnn3 : 0 ≤ ∫ t in (2 * Real.pi * (j : ℝ) + 7 * Real.pi / 4)..(2 * Real.pi * (j : ℝ)
      + 13 * Real.pi / 6), uRate sol t :=
    intervalIntegral.integral_nonneg h_b4_b6
      (fun t ht => hu_nn t (le_trans (le_trans h_a4_0 h_a4_b4) ht.1))
  have hext : (∫ t in (2 * Real.pi * (j : ℝ) + 5 * Real.pi / 4)..(2 * Real.pi * (j : ℝ)
        + 7 * Real.pi / 4), uRate sol t)
      ≤ ∫ t in (2 * Real.pi * (j : ℝ) + 7 * Real.pi / 6)..(2 * Real.pi * (j : ℝ)
        + 13 * Real.pi / 6), uRate sol t := by
    have hsplit : (∫ t in (2 * Real.pi * (j : ℝ) + 7 * Real.pi / 6)..(2 * Real.pi * (j : ℝ)
          + 13 * Real.pi / 6), uRate sol t)
        = (∫ t in (2 * Real.pi * (j : ℝ) + 7 * Real.pi / 6)..(2 * Real.pi * (j : ℝ)
            + 5 * Real.pi / 4), uRate sol t)
          + (∫ t in (2 * Real.pi * (j : ℝ) + 5 * Real.pi / 4)..(2 * Real.pi * (j : ℝ)
            + 7 * Real.pi / 4), uRate sol t)
          + (∫ t in (2 * Real.pi * (j : ℝ) + 7 * Real.pi / 4)..(2 * Real.pi * (j : ℝ)
            + 13 * Real.pi / 6), uRate sol t) := by
      rw [← hadd2, ← hadd1]
    rw [hsplit]; linarith
  exact le_trans hLB_le hext

/-- The U copy-window gate mass diverges (`Λu_j → ∞`), same growth gap. -/
theorem contractCopyMassLB_tendsto
    (sol : DynContractIteratorSol (Fin d) p sched F)
    (hApos : 0 < p.A) (hαpos : 0 < sol.init_α)
    (hgrow : 0 < p.cα - p.cμ * ((1 - Real.sqrt 2 / 2) / 2)) :
    Filter.Tendsto (contractCopyMassLB sol) Filter.atTop Filter.atTop := by
  have hπ := Real.pi_pos
  set rmax : ℝ := (1 - Real.sqrt 2 / 2) / 2 with hrmax
  set C : ℝ := p.A * sol.init_α * (Real.pi / 2) with hC
  have hCpos : 0 < C := by rw [hC]; positivity
  set K : ℝ := p.cα * (5 * Real.pi / 4)
      - (sol.init_μ + p.cμ * (7 * Real.pi / 4)) * rmax with hK
  set sl : ℝ := 2 * Real.pi * (p.cα - p.cμ * rmax) with hsl
  have hslpos : 0 < sl := by rw [hsl]; exact mul_pos (by positivity) hgrow
  have hEq : ∀ j : ℕ, contractCopyMassLB sol j = C * Real.exp (sl * (j : ℝ) + K) := by
    intro j
    rw [contractCopyMassLB, hC, hsl, hK]
    rw [show 2 * Real.pi * (p.cα - p.cμ * rmax) * (j : ℝ)
          + (p.cα * (5 * Real.pi / 4) - (sol.init_μ + p.cμ * (7 * Real.pi / 4)) * rmax)
        = p.cα * (2 * Real.pi * (j : ℝ) + 5 * Real.pi / 4)
          + (-((sol.init_μ + p.cμ * (2 * Real.pi * (j : ℝ) + 7 * Real.pi / 4)) * rmax))
        from by ring]
    rw [Real.exp_add]
    ring
  rw [Filter.tendsto_congr hEq]
  apply Filter.Tendsto.const_mul_atTop hCpos
  apply Real.tendsto_exp_atTop.comp
  apply Filter.tendsto_atTop_add_const_right
  exact Filter.Tendsto.const_mul_atTop hslpos tendsto_natCast_atTop_atTop

#print axioms contract_writeZ_integral_lower
#print axioms contractWriteMassLB_le_integral
#print axioms contractWriteMassLB_tendsto
#print axioms contract_writeU_integral_lower
#print axioms contractCopyMassLB_le_integral
#print axioms contractCopyMassLB_tendsto

end

end Ripple.BoundedUniversality.BGP
