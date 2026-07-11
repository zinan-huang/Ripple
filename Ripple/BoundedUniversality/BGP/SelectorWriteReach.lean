import Ripple.BoundedUniversality.BGP.SelectorField

/-!
Ripple.BoundedUniversality.BGP.SelectorWriteReach
-----------------------------
Discharge of config-Reach item **#2 (`hwrite`)** for the clock-driven selector `M_U`
solution: the per-coordinate write bound

  `|sol.u tEnd s − selectorMixTarget branch sol.u sol.lam tHold s| ≤ εwrite j`  with  `εwrite j → 0`.

The write of one cycle is the two-half Reach of `SelectorDynSol.write_reach`
(`SelectorDyn.lean`): on the z-active half `[a,m]` the register `z` reaches the
*frozen* mixture target `M := selectorMixTarget branch sol.u sol.lam tHold` (a constant
in `t`, since `tHold` is a fixed cycle time), and on the u-active half `[m,b]` the held
register `u` reaches `z`.  `write_reach` concludes

  `|u(b) − M| ≤ exp(−I_U)·|u(m) − M| + (δzh + exp(−I_Z)·|z(a) − M| + δw)`,

with the write integrals `I_Z = ∫_a^m A·α·bGateZ`, `I_U = ∫_m^b A·α·bGateU`.

The genuinely-new analytic content here is the **write-integral lower bound**: on a
tighter active sub-window `{sin ≥ √2/2}` (resp. `{sin ≤ −√2/2}`) the gate loss is
strictly beaten by the precision gain, so

  `I_Z, I_U ≥ (positive rate)·exp(cα·a_j)·width  ≥ c·j  → ∞`,

hence `exp(−I_Z), exp(−I_U) → 0` geometrically in the cycle index `j`.  This is the
write-channel analogue of `selector_gain_lower_exp`/`selector_gain_linear_growth`
(`SelectorField.lean`), but for the config Reach field `A·α·bGate` rather than the gate
gain `G`.

For the M_U parameters `A = 1, L = 1, cμ = 1, cα = 1/4` the balance `cμ·(1/4)^L = cα`
makes the loose window `{sin ≥ 1/2}` exactly flat (no growth); the tighter window
`{sin ≥ √2/2}` gives strict growth `cα − cμ·(1−√2/2)/2 > 0`.

The remaining write defects — the z-hold drift `δzh`, the mixture variation `δw`, and the
tube radii `|u(m) − M|`, `|z(a) − M|` — are CARRIED as explicit hypotheses, exactly
mirroring the contract-status (`RobustStepContract`) box/hold facts; they vanish through
the inductive tube.  The contraction factors `exp(−I_Z)`, `exp(−I_U)` are DISCHARGED.

No `sorry`/`admit`/`axiom`.
-/

noncomputable section

namespace Ripple.BoundedUniversality.BGP

open Real Set
open scoped BigOperators

/-! ## A tighter active sub-window: `sin ≥ √2/2` -/

/-- On `[2πj + π/4, 2πj + 3π/4]` the oscillator phase has `sin t ≥ √2/2`.  This is the
tightened analogue of `sin_window_ge` (which only gives `sin ≥ 1/2` on the wider
`[2πj+π/6, 2πj+5π/6]`); the strict gap `√2/2 > 1/2` is what makes the write integrand
grow (not merely stay flat) for the M_U parameters. -/
theorem sin_window_ge_sqrt2 (j : ℕ) {t : ℝ}
    (h1 : 2 * π * j + π / 4 ≤ t) (h2 : t ≤ 2 * π * j + 3 * π / 4) :
    Real.sqrt 2 / 2 ≤ Real.sin t := by
  have hπ := Real.pi_pos
  have hteq : t = (t - 2 * π * j) + (j : ℕ) * (2 * π) := by push_cast; ring
  have hsin : Real.sin t = Real.sin (t - 2 * π * j) := by
    conv_lhs => rw [hteq]
    rw [Real.sin_add_nat_mul_two_pi]
  rw [hsin]
  set x := t - 2 * π * (j : ℝ) with hx
  have hx1 : π / 4 ≤ x := by simp only [hx]; linarith
  have hx2 : x ≤ 3 * π / 4 := by simp only [hx]; linarith
  have hy : |π / 2 - x| ≤ π / 4 := abs_le.mpr ⟨by linarith, by linarith⟩
  calc Real.sqrt 2 / 2 = Real.cos (π / 4) := (Real.cos_pi_div_four).symm
    _ ≤ Real.cos |π / 2 - x| :=
        Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith) hy
    _ = Real.cos (π / 2 - x) := Real.cos_abs _
    _ = Real.sin x := Real.cos_pi_div_two_sub x

/-- Mirrored tighter window for the u-channel: on `[2πj + 5π/4, 2πj + 7π/4]`,
`sin t ≤ −√2/2`. -/
theorem sin_window_le_neg_sqrt2 (j : ℕ) {t : ℝ}
    (h1 : 2 * π * j + 5 * π / 4 ≤ t) (h2 : t ≤ 2 * π * j + 7 * π / 4) :
    Real.sin t ≤ -(Real.sqrt 2 / 2) := by
  have hπ := Real.pi_pos
  have hteq : t = (t - 2 * π * j) + (j : ℕ) * (2 * π) := by push_cast; ring
  have hsin : Real.sin t = Real.sin (t - 2 * π * j) := by
    conv_lhs => rw [hteq]
    rw [Real.sin_add_nat_mul_two_pi]
  rw [hsin]
  set x := t - 2 * π * (j : ℝ) with hx
  have hx1 : 5 * π / 4 ≤ x := by simp only [hx]; linarith
  have hx2 : x ≤ 7 * π / 4 := by simp only [hx]; linarith
  have hid := Real.sin_sub_pi x
  have hy : |π / 2 - (x - π)| ≤ π / 4 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hge : Real.sqrt 2 / 2 ≤ Real.sin (x - π) := by
    calc Real.sqrt 2 / 2 = Real.cos (π / 4) := (Real.cos_pi_div_four).symm
      _ ≤ Real.cos |π / 2 - (x - π)| :=
          Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith) hy
      _ = Real.cos (π / 2 - (x - π)) := Real.cos_abs _
      _ = Real.sin (x - π) := Real.cos_pi_div_two_sub _
  linarith [hid]

/-! ## The growth rate gap for the M_U parameters -/

/-- The strict growth gap `cα − cμ·rPulseMax > 0` on the tighter window.  For
`L = 1`, `cμ = 1`, `cα = 1/4`, the window-max of `rPulse` on `{sin ≥ √2/2}` is
`(1 − √2/2)/2`, and `1/4 − (1 − √2/2)/2 = (√2/2 − 1/2)/2 > 0`. -/
theorem rPulse_le_sqrt2_window {t : ℝ} (hs : Real.sqrt 2 / 2 ≤ Real.sin t) :
    rPulse 1 t ≤ (1 - Real.sqrt 2 / 2) / 2 := by
  unfold rPulse
  simp only [pow_one]
  have hsin1 : Real.sin t ≤ 1 := Real.sin_le_one t
  linarith

theorem qPulse_le_sqrt2_window {t : ℝ} (hs : Real.sin t ≤ -(Real.sqrt 2 / 2)) :
    qPulse 1 t ≤ (1 - Real.sqrt 2 / 2) / 2 := by
  unfold qPulse
  simp only [pow_one]
  have hsinm1 : -1 ≤ Real.sin t := Real.neg_one_le_sin t
  linarith

/-- The growth rate `cα − cμ·((1−√2/2)/2) = 1/4 − (1−√2/2)/2` is strictly positive. -/
theorem write_rate_pos : (0 : ℝ) < 1 / 4 - (1 - Real.sqrt 2 / 2) / 2 := by
  have h2 : (1 : ℝ) < Real.sqrt 2 := by
    have h := Real.sqrt_lt_sqrt (by norm_num : (0:ℝ) ≤ 1) (by norm_num : (1:ℝ) < 2)
    rwa [Real.sqrt_one] at h
  nlinarith

/-! ## Write-integral lower bounds (the contraction engine)

The config write integrals `I_Z = ∫ A·α·bGateZ`, `I_U = ∫ A·α·bGateU` are bounded
below on the tighter active sub-window by a quantity that grows like `exp(rate·a)·width`,
the write-channel analogue of `selector_gain_lower_exp`. -/

section Integral

variable {d B : ℕ} {V : Type} [Fintype V]
    {p : DynGateParams} {sched : PhaseSchedule} {branch : V → BranchData d B}
    {chiResetF chiGateF kappaF gainF : ℝ → ℝ} {Pv : V → (Fin d → ℝ) → ℝ}

/-- **z-write integral, window lower bound.**  On a window `[a,b]` where the closed forms
`α t = exp(cα·t)` and `μ t = cμ·t` hold and `sin t ≥ √2/2` (so `bGateZ ≥ exp(−μ·rPulseMax)`
with `rPulseMax = (1−√2/2)/2`), the write integrand `A·α·bGateZ` exceeds the constant
window-minimum, hence

  `A·exp(cα·a)·exp(−cμ·b·rPulseMax)·(b−a) ≤ ∫_a^b A·α·bGateZ`.

With `cα = 1/4 > cμ·rPulseMax`, the constant `exp(cα·a)·exp(−cμ·b·rPulseMax)` grows in `a`. -/
theorem write_Z_integral_lower
    (sol : SelectorDynSol d B V p sched branch chiResetF chiGateF kappaF gainF Pv)
    {a b cμ cα A : ℝ} (hab : a ≤ b) (ha0 : 0 ≤ a) (hA : 0 ≤ A) (hcμ : 0 ≤ cμ) (hcα : 0 ≤ cα)
    (hpA : p.A = A) (hpL : p.L = 1)
    (hg_cont : Continuous (fun t => p.A * sol.α t * bGateZ p.L (sol.μ t) t))
    (hα : ∀ t ∈ Icc a b, sol.α t = Real.exp (cα * t))
    (hμ : ∀ t ∈ Icc a b, sol.μ t = cμ * t)
    (hsin : ∀ t ∈ Icc a b, Real.sqrt 2 / 2 ≤ Real.sin t) :
    A * Real.exp (cα * a) * Real.exp (-(cμ * b * ((1 - Real.sqrt 2 / 2) / 2))) * (b - a)
      ≤ ∫ t in a..b, p.A * sol.α t * bGateZ p.L (sol.μ t) t := by
  set rmax : ℝ := (1 - Real.sqrt 2 / 2) / 2 with hrmax
  have hrmax0 : 0 ≤ rmax := by
    have h2 : Real.sqrt 2 ≤ 2 := by
      have := Real.sqrt_le_sqrt (by norm_num : (2:ℝ) ≤ 4)
      simpa [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq] using this
    rw [hrmax]; nlinarith [Real.sqrt_nonneg 2]
  set φ : ℝ → ℝ := fun t => p.A * sol.α t * bGateZ p.L (sol.μ t) t with hφdef
  have hφc : Continuous φ := hg_cont
  -- pointwise lower bound on [a,b]
  have hlb : ∀ t ∈ Icc a b,
      A * Real.exp (cα * a) * Real.exp (-(cμ * b * rmax)) ≤ φ t := by
    intro t ht
    have hat : a ≤ t := ht.1
    have htb : t ≤ b := ht.2
    have ht0 : 0 ≤ t := le_trans ha0 hat
    rw [hφdef]; simp only
    rw [hpA, hα t ht]
    -- A·exp(cα t)·bGateZ
    have hαle : Real.exp (cα * a) ≤ Real.exp (cα * t) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_left hat hcα
    have hgate : Real.exp (-(cμ * b * rmax)) ≤ bGateZ p.L (sol.μ t) t := by
      rw [hpL, hμ t ht]
      have hsint : Real.sqrt 2 / 2 ≤ Real.sin t := hsin t ht
      have hrp : rPulse 1 t ≤ rmax := rPulse_le_sqrt2_window hsint
      have hμt : cμ * t ≤ cμ * b := mul_le_mul_of_nonneg_left htb hcμ
      have hμt0 : 0 ≤ cμ * t := mul_nonneg hcμ ht0
      calc Real.exp (-(cμ * b * rmax))
          ≤ Real.exp (-(cμ * t * rPulse 1 t)) := by
            apply Real.exp_le_exp.mpr
            have hrp0 : 0 ≤ rPulse 1 t := rPulse_nonneg 1 t
            nlinarith [mul_nonneg hμt0 hrp0]
        _ = bGateZ 1 (cμ * t) t := by unfold bGateZ; ring_nf
    have hmul := mul_le_mul hαle hgate (Real.exp_pos _).le (Real.exp_pos _).le
    have hfin := mul_le_mul_of_nonneg_left hmul hA
    -- hfin : A*(exp(cα a)*exp(-(cμ b rmax))) ≤ A*(exp(cα t)*bGateZ p.L (sol.μ t) t)
    calc A * Real.exp (cα * a) * Real.exp (-(cμ * b * rmax))
        = A * (Real.exp (cα * a) * Real.exp (-(cμ * b * rmax))) := by ring
      _ ≤ A * (Real.exp (cα * t) * bGateZ p.L (sol.μ t) t) := hfin
      _ = A * Real.exp (cα * t) * bGateZ p.L (sol.μ t) t := by ring
  have hconst : (∫ _t in a..b, A * Real.exp (cα * a) * Real.exp (-(cμ * b * rmax)))
      = A * Real.exp (cα * a) * Real.exp (-(cμ * b * rmax)) * (b - a) := by
    rw [intervalIntegral.integral_const, smul_eq_mul]; ring
  calc A * Real.exp (cα * a) * Real.exp (-(cμ * b * rmax)) * (b - a)
      = ∫ _t in a..b, A * Real.exp (cα * a) * Real.exp (-(cμ * b * rmax)) := hconst.symm
    _ ≤ ∫ t in a..b, φ t :=
        intervalIntegral.integral_mono_on hab _root_.intervalIntegrable_const
          (hφc.intervalIntegrable a b) hlb

/-- **u-write integral, window lower bound** (mirror of `write_Z_integral_lower` on the
u-active sub-window `{sin ≤ −√2/2}`, where `bGateU ≥ exp(−μ·rPulseMax)`). -/
theorem write_U_integral_lower
    (sol : SelectorDynSol d B V p sched branch chiResetF chiGateF kappaF gainF Pv)
    {a b cμ cα A : ℝ} (hab : a ≤ b) (ha0 : 0 ≤ a) (hA : 0 ≤ A) (hcμ : 0 ≤ cμ) (hcα : 0 ≤ cα)
    (hpA : p.A = A) (hpL : p.L = 1)
    (hg_cont : Continuous (fun t => p.A * sol.α t * bGateU p.L (sol.μ t) t))
    (hα : ∀ t ∈ Icc a b, sol.α t = Real.exp (cα * t))
    (hμ : ∀ t ∈ Icc a b, sol.μ t = cμ * t)
    (hsin : ∀ t ∈ Icc a b, Real.sin t ≤ -(Real.sqrt 2 / 2)) :
    A * Real.exp (cα * a) * Real.exp (-(cμ * b * ((1 - Real.sqrt 2 / 2) / 2))) * (b - a)
      ≤ ∫ t in a..b, p.A * sol.α t * bGateU p.L (sol.μ t) t := by
  set rmax : ℝ := (1 - Real.sqrt 2 / 2) / 2 with hrmax
  set φ : ℝ → ℝ := fun t => p.A * sol.α t * bGateU p.L (sol.μ t) t with hφdef
  have hφc : Continuous φ := hg_cont
  have hlb : ∀ t ∈ Icc a b,
      A * Real.exp (cα * a) * Real.exp (-(cμ * b * rmax)) ≤ φ t := by
    intro t ht
    have hat : a ≤ t := ht.1
    have htb : t ≤ b := ht.2
    have ht0 : 0 ≤ t := le_trans ha0 hat
    rw [hφdef]; simp only
    rw [hpA, hα t ht]
    have hαle : Real.exp (cα * a) ≤ Real.exp (cα * t) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hat hcα)
    have hgate : Real.exp (-(cμ * b * rmax)) ≤ bGateU p.L (sol.μ t) t := by
      rw [hpL, hμ t ht]
      have hsint : Real.sin t ≤ -(Real.sqrt 2 / 2) := hsin t ht
      have hrp : qPulse 1 t ≤ rmax := qPulse_le_sqrt2_window hsint
      have hμt : cμ * t ≤ cμ * b := mul_le_mul_of_nonneg_left htb hcμ
      have hμt0 : 0 ≤ cμ * t := mul_nonneg hcμ ht0
      calc Real.exp (-(cμ * b * rmax))
          ≤ Real.exp (-(cμ * t * qPulse 1 t)) := by
            apply Real.exp_le_exp.mpr
            have hrp0 : 0 ≤ qPulse 1 t := qPulse_nonneg 1 t
            nlinarith [mul_nonneg hμt0 hrp0]
        _ = bGateU 1 (cμ * t) t := by unfold bGateU; ring_nf
    have hmul := mul_le_mul hαle hgate (Real.exp_pos _).le (Real.exp_pos _).le
    have hfin := mul_le_mul_of_nonneg_left hmul hA
    calc A * Real.exp (cα * a) * Real.exp (-(cμ * b * rmax))
        = A * (Real.exp (cα * a) * Real.exp (-(cμ * b * rmax))) := by ring
      _ ≤ A * (Real.exp (cα * t) * bGateU p.L (sol.μ t) t) := hfin
      _ = A * Real.exp (cα * t) * bGateU p.L (sol.μ t) t := by ring
  have hconst : (∫ _t in a..b, A * Real.exp (cα * a) * Real.exp (-(cμ * b * rmax)))
      = A * Real.exp (cα * a) * Real.exp (-(cμ * b * rmax)) * (b - a) := by
    rw [intervalIntegral.integral_const, smul_eq_mul]; ring
  calc A * Real.exp (cα * a) * Real.exp (-(cμ * b * rmax)) * (b - a)
      = ∫ _t in a..b, A * Real.exp (cα * a) * Real.exp (-(cμ * b * rmax)) := hconst.symm
    _ ≤ ∫ t in a..b, φ t :=
        intervalIntegral.integral_mono_on hab _root_.intervalIntegrable_const
          (hφc.intervalIntegrable a b) hlb

end Integral

/-! ## Decay of the write contraction factor

The window lower bound `I ≥ A·exp(cα·a_j)·exp(−cμ·b_j·rmax)·w` with `a_j = 2πj+π/4`,
`b_j = 2πj+3π/4`, `cα = 1/4`, `cμ = 1`, `rmax = (1−√2/2)/2`, `w = π/2` grows like
`exp(2π·rate·j)` with `rate = cα − cμ·rmax > 0`.  Since the lower bound `→ +∞`, the
contraction factor `exp(−I) ≤ exp(−(lower bound)) → 0`. -/

/-- The per-cycle window lower bound on the write integral, as an explicit function of `j`
for the M_U parameters.  `Lbd j = exp(cα·(2πj+π/4)) · exp(−cμ·(2πj+3π/4)·rmax) · (π/2)`. -/
noncomputable def writeIntegralLbd (cμ cα rmax : ℝ) (j : ℕ) : ℝ :=
  Real.exp (cα * (2 * π * (j : ℝ) + π / 4))
    * Real.exp (-(cμ * (2 * π * (j : ℝ) + 3 * π / 4) * rmax)) * (π / 2)

/-- **The write lower bound tends to `+∞`.**  Writing `Lbd j = (π/2)·exp(linear-in-j)`
with positive slope `2π·(cα − cμ·rmax) > 0`, the lower bound diverges. -/
theorem writeIntegralLbd_tendsto_atTop {cμ cα rmax : ℝ}
    (hrate : 0 < cα - cμ * rmax) :
    Filter.Tendsto (fun j : ℕ => writeIntegralLbd cμ cα rmax j) Filter.atTop Filter.atTop := by
  have hπ := Real.pi_pos
  -- Lbd j = (π/2) * exp( s·j + c0 ),  s = 2π(cα − cμ rmax) > 0
  set s : ℝ := 2 * π * (cα - cμ * rmax) with hs
  set c0 : ℝ := cα * (π / 4) - cμ * (3 * π / 4) * rmax with hc0
  have hrw : ∀ j : ℕ, writeIntegralLbd cμ cα rmax j
      = (π / 2) * Real.exp (s * (j : ℝ) + c0) := by
    intro j
    unfold writeIntegralLbd
    rw [← Real.exp_add]
    rw [hs, hc0]
    ring_nf
  have hs_pos : 0 < s := by rw [hs]; positivity
  -- exp(s·j + c0) → ∞, times positive const
  have hlin : Filter.Tendsto (fun j : ℕ => s * (j : ℝ) + c0) Filter.atTop Filter.atTop := by
    apply Filter.Tendsto.atTop_add _ tendsto_const_nhds
    exact Filter.Tendsto.const_mul_atTop hs_pos
      (tendsto_natCast_atTop_atTop)
  have hexp : Filter.Tendsto (fun j : ℕ => Real.exp (s * (j : ℝ) + c0))
      Filter.atTop Filter.atTop := Real.tendsto_exp_atTop.comp hlin
  have : Filter.Tendsto (fun j : ℕ => (π / 2) * Real.exp (s * (j : ℝ) + c0))
      Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop (by positivity) hexp
  simpa only [hrw] using this

/-- **The write contraction factor decays to `0`.**  `exp(−I_j) ≤ exp(−Lbd j) → 0`
since `Lbd j → +∞`. -/
theorem write_contraction_tendsto_zero {cμ cα rmax : ℝ}
    (hrate : 0 < cα - cμ * rmax) (I : ℕ → ℝ)
    (hI : ∀ j, writeIntegralLbd cμ cα rmax j ≤ I j) :
    Filter.Tendsto (fun j : ℕ => Real.exp (-(I j))) Filter.atTop (nhds 0) := by
  have hLbd := writeIntegralLbd_tendsto_atTop hrate
  -- exp(-Lbd j) → 0, and exp(-I j) ≤ exp(-Lbd j)
  have hexp_Lbd : Filter.Tendsto (fun j : ℕ => Real.exp (-(writeIntegralLbd cμ cα rmax j)))
      Filter.atTop (nhds 0) := by
    have hneg : Filter.Tendsto (fun j : ℕ => -(writeIntegralLbd cμ cα rmax j))
        Filter.atTop Filter.atBot := Filter.tendsto_neg_atBot_iff.mpr hLbd
    exact Real.tendsto_exp_atBot.comp hneg
  refine squeeze_zero (fun j => (Real.exp_pos _).le) (fun j => ?_) hexp_Lbd
  exact Real.exp_le_exp.mpr (by linarith [hI j])

/-! ## Assembled per-coordinate `hwrite` bound for the M_U solution

Combining `write_reach` with the two write-integral lower bounds, the per-cycle write
defect splits as

  `εwrite j = exp(−I_U)·R_u + δzh + exp(−I_Z)·R_z + δw`,

where `R_u = |u(m) − M|`, `R_z = |z(a) − M|` are the CARRIED tube radii (box bounds), and
`δzh`, `δw` are the CARRIED z-hold drift / mixture-variation defects.  The contraction
factors `exp(−I_U)`, `exp(−I_Z)` are DISCHARGED (they `→ 0` by
`write_contraction_tendsto_zero`); the remaining terms vanish through the inductive tube
exactly as the contract's `RobustStepContract` box/hold facts do. -/

variable {d B : ℕ} {V : Type} [Fintype V]
    {p : DynGateParams} {sched : PhaseSchedule} {branch : V → BranchData d B}
    {chiResetF chiGateF kappaF gainF : ℝ → ℝ} {Pv : V → (Fin d → ℝ) → ℝ}

/-- **(#2) Per-coordinate write bound with discharged contraction factor.**
Specializing `SelectorDynSol.write_reach` to the M_U cycle `j` with z-active half
`[a,m] ⊆ {sin ≥ √2/2}` and u-active half `[m,b] ⊆ {sin ≤ −√2/2}`, the held config at the
cycle end is within

  `εwrite j := exp(−Lbd_U j)·R_u + δzh + (exp(−Lbd_Z j)·R_z + δw)`

of the frozen mixture target `M`, where `Lbd_Z/U j` are the growing window lower bounds.
The radii `R_u`, `R_z`, the hold `δzh` and the variation `δw` are carried as hypotheses
(matching the contract status); the contraction `exp(−Lbd) → 0` is discharged. -/
theorem selector_hwrite_bound
    (sol : SelectorDynSol d B V p sched branch chiResetF chiGateF kappaF gainF Pv)
    (s : Fin d) {a m b M δw δzh cμ cα A Ru Rz : ℝ}
    (ham : a ≤ m) (hmb : m ≤ b) (ha0 : 0 ≤ a) (hmpos : 0 ≤ m)
    (hA : 0 ≤ A) (hcμ : 0 ≤ cμ) (hcα : 0 ≤ cα)
    (hpA : p.A = A) (hpL : p.L = 1)
    (hdom1 : ∀ t ∈ Icc a m, t ∈ sched.domain)
    (hdom2 : ∀ t ∈ Icc m b, t ∈ sched.domain)
    (hgZ_cont : Continuous (fun t => p.A * sol.α t * bGateZ p.L (sol.μ t) t))
    (hgZ0 : ∀ t ∈ Icc a m, 0 ≤ p.A * sol.α t * bGateZ p.L (sol.μ t) t)
    (hgU_cont : Continuous (fun t => p.A * sol.α t * bGateU p.L (sol.μ t) t))
    (hgU0 : ∀ t ∈ Icc m b, 0 ≤ p.A * sol.α t * bGateU p.L (sol.μ t) t)
    (hstab : ∀ t ∈ Icc a m, |selectorMixTarget branch sol.u sol.lam t s - M| ≤ δw)
    (hzh : ∀ t ∈ Icc m b, |sol.z t s - sol.z m s| ≤ δzh)
    -- closed forms on the two halves
    (hαZ : ∀ t ∈ Icc a m, sol.α t = Real.exp (cα * t))
    (hμZ : ∀ t ∈ Icc a m, sol.μ t = cμ * t)
    (hsinZ : ∀ t ∈ Icc a m, Real.sqrt 2 / 2 ≤ Real.sin t)
    (hαU : ∀ t ∈ Icc m b, sol.α t = Real.exp (cα * t))
    (hμU : ∀ t ∈ Icc m b, sol.μ t = cμ * t)
    (hsinU : ∀ t ∈ Icc m b, Real.sin t ≤ -(Real.sqrt 2 / 2))
    -- carried tube radii (box bounds)
    (hRu : |sol.u m s - M| ≤ Ru) (hRz : |sol.z a s - M| ≤ Rz)
    (hRu0 : 0 ≤ Ru) (hRz0 : 0 ≤ Rz) :
    |sol.u b s - M| ≤
      Real.exp (-(A * Real.exp (cα * m)
            * Real.exp (-(cμ * b * ((1 - Real.sqrt 2 / 2) / 2))) * (b - m))) * Ru
        + (δzh + (Real.exp (-(A * Real.exp (cα * a)
            * Real.exp (-(cμ * m * ((1 - Real.sqrt 2 / 2) / 2))) * (m - a))) * Rz + δw)) := by
  -- write_reach gives the exp(-∫) form
  have hwr := sol.write_reach s ham hmb hdom1 hdom2 hgZ_cont hgZ0 hgU_cont hgU0 hstab hzh
  -- lower-bound the two integrals
  have hIZ := write_Z_integral_lower sol ham ha0 hA hcμ hcα hpA hpL hgZ_cont hαZ hμZ hsinZ
  have hIU := write_U_integral_lower sol hmb hmpos hA hcμ hcα hpA hpL hgU_cont hαU hμU hsinU
  -- exp is antitone: exp(-∫_Z) ≤ exp(-Lbd_Z), and the lower bound is nonneg
  set LZ : ℝ := A * Real.exp (cα * a)
      * Real.exp (-(cμ * m * ((1 - Real.sqrt 2 / 2) / 2))) * (m - a) with hLZdef
  set LU : ℝ := A * Real.exp (cα * m)
      * Real.exp (-(cμ * b * ((1 - Real.sqrt 2 / 2) / 2))) * (b - m) with hLUdef
  have hexpZ : Real.exp (-(∫ t in a..m, p.A * sol.α t * bGateZ p.L (sol.μ t) t))
      ≤ Real.exp (-LZ) := Real.exp_le_exp.mpr (by rw [hLZdef]; linarith [hIZ])
  have hexpU : Real.exp (-(∫ t in m..b, p.A * sol.α t * bGateU p.L (sol.μ t) t))
      ≤ Real.exp (-LU) := Real.exp_le_exp.mpr (by rw [hLUdef]; linarith [hIU])
  -- chain: the write_reach bound's terms are dominated
  have hU_term : Real.exp (-(∫ t in m..b, p.A * sol.α t * bGateU p.L (sol.μ t) t))
        * |sol.u m s - M| ≤ Real.exp (-LU) * Ru := by
    apply mul_le_mul hexpU hRu (abs_nonneg _) (Real.exp_pos _).le
  have hZ_term : Real.exp (-(∫ t in a..m, p.A * sol.α t * bGateZ p.L (sol.μ t) t))
        * |sol.z a s - M| ≤ Real.exp (-LZ) * Rz := by
    apply mul_le_mul hexpZ hRz (abs_nonneg _) (Real.exp_pos _).le
  calc |sol.u b s - M|
      ≤ Real.exp (-(∫ t in m..b, p.A * sol.α t * bGateU p.L (sol.μ t) t))
            * |sol.u m s - M|
          + (δzh + (Real.exp (-(∫ t in a..m, p.A * sol.α t * bGateZ p.L (sol.μ t) t))
              * |sol.z a s - M| + δw)) := hwr
    _ ≤ Real.exp (-LU) * Ru + (δzh + (Real.exp (-LZ) * Rz + δw)) :=
          add_le_add hU_term
            (add_le_add (le_refl δzh) (add_le_add hZ_term (le_refl δw)))

end Ripple.BoundedUniversality.BGP
