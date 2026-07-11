import Ripple.BoundedUniversality.BGP.SelectorReplicatorSettled
import Ripple.BoundedUniversality.BGP.SelectorReplicatorRadiiDecay
import Ripple.BoundedUniversality.BGP.SelectorDuhamelWrite
import Ripple.BoundedUniversality.BGP.BGPParams38

/-!
Ripple.BoundedUniversality.BGP.SelectorReplicatorSettledZ
--------------------------------------

Analytic settled-window facts for the restructured replicator selector.

The settled write window is `[selectorMUWriteHoldTime j, selectorMUWriteReadTime j]`,
namely `[2πj + π/2, 2πj + 5π/6]`.  This file is additive: it reuses the
existing hold/moving-target machinery and adds only the u-channel qPulse
offphase envelope and the settled z-write lower-bound instantiation needed for
this shifted window.
-/

noncomputable section

namespace Ripple.BoundedUniversality.BGP

open Set MachineInstance
open Filter
open scoped BigOperators Topology Real

/-! ## Settled u-drift -/

/-- The concrete settled u-offphase rate:
`cμ * (3/4)^L - cα = 1000 * 3/4 - 300 = 450` for `bgpParams38`. -/
def selectorUSettledRate : ℝ :=
  bgpParams38.cμ * (3 / 4 : ℝ) ^ bgpParams38.L - bgpParams38.cα

/-- Explicit settled-window u-drift envelope from the qPulse offphase bound. -/
def δuSettled (Bzu : ℝ) (j : ℕ) : ℝ :=
  Bzu * ((Real.pi / 3) * Real.exp (-(selectorUSettledRate * selectorMUWriteHoldTime j)))

/-- Explicit prefix-window u-drift envelope from the qPulse offphase bound. -/
def δuWritePrefix (Bzu : ℝ) (j : ℕ) : ℝ :=
  Bzu * ((Real.pi / 3) * Real.exp (-(selectorUSettledRate * selectorMUWriteStartTime j)))

theorem selectorUSettledRate_pos : 0 < selectorUSettledRate := by
  norm_num [selectorUSettledRate, bgpParams38]

theorem δuSettled_tendsto_zero (Bzu : ℝ) :
    Tendsto (δuSettled Bzu) atTop (𝓝 0) := by
  have hlin :
      Tendsto (fun j : ℕ => selectorMUWriteHoldTime j) atTop atTop := by
    have hbase : Tendsto (fun j : ℕ => (2 * Real.pi) * (j : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.const_mul_atTop
        (by positivity : (0 : ℝ) < 2 * Real.pi)
    simpa [selectorMUWriteHoldTime, mul_assoc] using
      Filter.tendsto_atTop_add_const_right atTop (Real.pi / 2) hbase
  have hscaled :
      Tendsto (fun j : ℕ => selectorUSettledRate * selectorMUWriteHoldTime j)
        atTop atTop :=
    hlin.const_mul_atTop selectorUSettledRate_pos
  have hneg :
      Tendsto (fun j : ℕ => -(selectorUSettledRate * selectorMUWriteHoldTime j))
        atTop atBot :=
    Filter.tendsto_neg_atBot_iff.mpr hscaled
  have hexp :
      Tendsto
        (fun j : ℕ =>
          Real.exp (-(selectorUSettledRate * selectorMUWriteHoldTime j)))
        atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hneg
  have hmul :
      Tendsto
        (fun j : ℕ =>
          (Bzu * (Real.pi / 3)) *
            Real.exp (-(selectorUSettledRate * selectorMUWriteHoldTime j)))
        atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hexp
  refine hmul.congr' ?_
  filter_upwards [] with j
  dsimp [δuSettled]
  ring

theorem δuWritePrefix_tendsto_zero (Bzu : ℝ) :
    Tendsto (δuWritePrefix Bzu) atTop (𝓝 0) := by
  have hlin :
      Tendsto (fun j : ℕ => selectorMUWriteStartTime j) atTop atTop := by
    have hbase : Tendsto (fun j : ℕ => (2 * Real.pi) * (j : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.const_mul_atTop
        (by positivity : (0 : ℝ) < 2 * Real.pi)
    simpa [selectorMUWriteStartTime, mul_assoc] using
      Filter.tendsto_atTop_add_const_right atTop (Real.pi / 6) hbase
  have hscaled :
      Tendsto (fun j : ℕ => selectorUSettledRate * selectorMUWriteStartTime j)
        atTop atTop :=
    hlin.const_mul_atTop selectorUSettledRate_pos
  have hneg :
      Tendsto (fun j : ℕ => -(selectorUSettledRate * selectorMUWriteStartTime j))
        atTop atBot :=
    Filter.tendsto_neg_atBot_iff.mpr hscaled
  have hexp :
      Tendsto
        (fun j : ℕ =>
          Real.exp (-(selectorUSettledRate * selectorMUWriteStartTime j)))
        atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hneg
  have hmul :
      Tendsto
        (fun j : ℕ =>
          (Bzu * (Real.pi / 3)) *
            Real.exp (-(selectorUSettledRate * selectorMUWriteStartTime j)))
        atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hexp
  refine hmul.congr' ?_
  filter_upwards [] with j
  dsimp [δuWritePrefix]
  ring

theorem δuSettled_nonneg {Bzu : ℝ} {j : ℕ} (hBzu0 : 0 ≤ Bzu) :
    0 ≤ δuSettled Bzu j := by
  dsimp [δuSettled]
  exact mul_nonneg hBzu0
    (mul_nonneg (by positivity) (Real.exp_pos _).le)

theorem δuWritePrefix_nonneg {Bzu : ℝ} {j : ℕ} (hBzu0 : 0 ≤ Bzu) :
    0 ≤ δuWritePrefix Bzu j := by
  dsimp [δuWritePrefix]
  exact mul_nonneg hBzu0
    (mul_nonneg (by positivity) (Real.exp_pos _).le)

theorem selectorMUWriteStartTime_zero_le (j : ℕ) :
    selectorMUWriteStartTime 0 ≤ selectorMUWriteStartTime j := by
  unfold selectorMUWriteStartTime
  have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  nlinarith [Real.pi_pos, hj]

theorem δuWritePrefix_le_initial {Bzu : ℝ} (hBzu0 : 0 ≤ Bzu) (j : ℕ) :
    δuWritePrefix Bzu j ≤ δuWritePrefix Bzu 0 := by
  have hstart := selectorMUWriteStartTime_zero_le j
  have hscaled :
      selectorUSettledRate * selectorMUWriteStartTime 0 ≤
        selectorUSettledRate * selectorMUWriteStartTime j :=
    mul_le_mul_of_nonneg_left hstart selectorUSettledRate_pos.le
  have hexp :
      Real.exp (-(selectorUSettledRate * selectorMUWriteStartTime j)) ≤
        Real.exp (-(selectorUSettledRate * selectorMUWriteStartTime 0)) := by
    exact Real.exp_le_exp.mpr (by linarith)
  dsimp [δuWritePrefix]
  have hcoef : 0 ≤ Bzu * (Real.pi / 3) :=
    mul_nonneg hBzu0 (by positivity)
  nlinarith [mul_le_mul_of_nonneg_left hexp hcoef]

/-- The settled-tail reserve still vanishes when the per-cycle `z-u` envelope is
eventually bounded.  This is the exact growth condition needed by the F1 cap
surface; the crude finite-horizon envelope is not known to satisfy it. -/
theorem δuSettled_tendsto_zero_of_eventually_bounded
    (Bzu : ℕ → ℝ) {C : ℝ}
    (hBzu0 : ∀ᶠ j in atTop, 0 ≤ Bzu j)
    (hBzu_le : ∀ᶠ j in atTop, Bzu j ≤ C) :
    Tendsto (fun j => δuSettled (Bzu j) j) atTop (𝓝 0) := by
  have hdecay : Tendsto (δuSettled (1 : ℝ)) atTop (𝓝 0) :=
    δuSettled_tendsto_zero 1
  have hprod :
      Tendsto (fun j => Bzu j * δuSettled (1 : ℝ) j) atTop (𝓝 0) :=
    bdd_le_mul_tendsto_zero hBzu0 hBzu_le hdecay
  refine hprod.congr' ?_
  filter_upwards [] with j
  dsimp [δuSettled]
  ring

theorem δuSettled_tendsto_zero_of_uniform_bound
    (Bzu : ℕ → ℝ) {C : ℝ}
    (hBzu0 : ∀ j, 0 ≤ Bzu j)
    (hBzu_le : ∀ j, Bzu j ≤ C) :
    Tendsto (fun j => δuSettled (Bzu j) j) atTop (𝓝 0) :=
  δuSettled_tendsto_zero_of_eventually_bounded Bzu
    (Filter.Eventually.of_forall hBzu0)
    (Filter.Eventually.of_forall hBzu_le)

theorem δuWritePrefix_tendsto_zero_of_eventually_bounded
    (Bzu : ℕ → ℝ) {C : ℝ}
    (hBzu0 : ∀ᶠ j in atTop, 0 ≤ Bzu j)
    (hBzu_le : ∀ᶠ j in atTop, Bzu j ≤ C) :
    Tendsto (fun j => δuWritePrefix (Bzu j) j) atTop (𝓝 0) := by
  have hdecay : Tendsto (δuWritePrefix (1 : ℝ)) atTop (𝓝 0) :=
    δuWritePrefix_tendsto_zero 1
  have hprod :
      Tendsto (fun j => Bzu j * δuWritePrefix (1 : ℝ) j) atTop (𝓝 0) :=
    bdd_le_mul_tendsto_zero hBzu0 hBzu_le hdecay
  refine hprod.congr' ?_
  filter_upwards [] with j
  dsimp [δuWritePrefix]
  ring

theorem δuWritePrefix_tendsto_zero_of_uniform_bound
    (Bzu : ℕ → ℝ) {C : ℝ}
    (hBzu0 : ∀ j, 0 ≤ Bzu j)
    (hBzu_le : ∀ j, Bzu j ≤ C) :
    Tendsto (fun j => δuWritePrefix (Bzu j) j) atTop (𝓝 0) :=
  δuWritePrefix_tendsto_zero_of_eventually_bounded Bzu
    (Filter.Eventually.of_forall hBzu0)
    (Filter.Eventually.of_forall hBzu_le)

/-- Pointwise qPulse-offphase envelope for the u-gate integrand on a settled
window where `sin t ≥ 1/2`. -/
theorem gateU_integrand_le_settled_exp_repl
    {d B : ℕ} {V : Type} [Fintype V]
    {p : DynGateParams} {sched : PhaseSchedule} {branch : V → BranchData d B}
    {chiReset chiGate kappa gain : ℝ → ℝ} {readoutP : V → (Fin d → ℝ) → ℝ}
    (sol : SelectorReplicatorDynSol d B V p sched branch chiReset chiGate kappa gain readoutP)
    {A cμ cα t : ℝ} (ht0 : 0 ≤ t) (hA0 : 0 ≤ A) (hcμ0 : 0 ≤ cμ)
    (hpA : p.A = A)
    (hα : sol.α t = Real.exp (cα * t))
    (hμ : sol.μ t = cμ * t)
    (hsin : (1 : ℝ) / 2 ≤ Real.sin t) :
    p.A * sol.α t * bGateU p.L (sol.μ t) t
      ≤ A * Real.exp (-((cμ * (3 / 4 : ℝ) ^ p.L - cα) * t)) := by
  rw [hpA, hα]
  have hgate :
      bGateU p.L (sol.μ t) t ≤ Real.exp (-(cμ * t * (3 / 4 : ℝ) ^ p.L)) := by
    rw [hμ]
    unfold bGateU
    apply Real.exp_le_exp.mpr
    have hq : (3 / 4 : ℝ) ^ p.L ≤ qPulse p.L t := qPulse_ge_active hsin
    have hct0 : 0 ≤ cμ * t := mul_nonneg hcμ0 ht0
    have hmul :
        cμ * t * (3 / 4 : ℝ) ^ p.L ≤ cμ * t * qPulse p.L t :=
      mul_le_mul_of_nonneg_left hq hct0
    nlinarith
  have hmul :
      Real.exp (cα * t) * bGateU p.L (sol.μ t) t
        ≤ Real.exp (cα * t) *
            Real.exp (-(cμ * t * (3 / 4 : ℝ) ^ p.L)) :=
    mul_le_mul_of_nonneg_left hgate (Real.exp_pos _).le
  have hA_mul := mul_le_mul_of_nonneg_left hmul hA0
  calc
    A * Real.exp (cα * t) * bGateU p.L (sol.μ t) t
        = A * (Real.exp (cα * t) * bGateU p.L (sol.μ t) t) := by ring
    _ ≤ A * (Real.exp (cα * t) *
          Real.exp (-(cμ * t * (3 / 4 : ℝ) ^ p.L))) := hA_mul
    _ = A * Real.exp (-((cμ * (3 / 4 : ℝ) ^ p.L - cα) * t)) := by
      rw [← Real.exp_add]
      ring

/-- Integral qPulse-offphase envelope for the u-gate on settled subwindows. -/
theorem gateU_integral_le_settled_exp_repl
    {d B : ℕ} {V : Type} [Fintype V]
    {p : DynGateParams} {sched : PhaseSchedule} {branch : V → BranchData d B}
    {chiReset chiGate kappa gain : ℝ → ℝ} {readoutP : V → (Fin d → ℝ) → ℝ}
    (sol : SelectorReplicatorDynSol d B V p sched branch chiReset chiGate kappa gain readoutP)
    {a b A cμ cα : ℝ} (hab : a ≤ b) (ha0 : 0 ≤ a)
    (hA0 : 0 ≤ A) (hcμ0 : 0 ≤ cμ)
    (hpA : p.A = A)
    (hg_cont : Continuous (fun t => p.A * sol.α t * bGateU p.L (sol.μ t) t))
    (hα : ∀ t ∈ Icc a b, sol.α t = Real.exp (cα * t))
    (hμ : ∀ t ∈ Icc a b, sol.μ t = cμ * t)
    (hsin : ∀ t ∈ Icc a b, (1 : ℝ) / 2 ≤ Real.sin t) :
    (∫ t in a..b, p.A * sol.α t * bGateU p.L (sol.μ t) t)
      ≤ ∫ t in a..b, A * Real.exp (-((cμ * (3 / 4 : ℝ) ^ p.L - cα) * t)) := by
  have henv_cont :
      Continuous fun t : ℝ =>
        A * Real.exp (-((cμ * (3 / 4 : ℝ) ^ p.L - cα) * t)) := by
    fun_prop
  apply intervalIntegral.integral_mono_on hab
  · exact hg_cont.intervalIntegrable a b
  · exact henv_cont.intervalIntegrable a b
  · intro t ht
    exact gateU_integrand_le_settled_exp_repl sol
      (le_trans ha0 ht.1) hA0 hcμ0 hpA (hα t ht) (hμ t ht) (hsin t ht)

/-- Pointwise half-phase envelope for the replicator z-gate integrand.

On edge windows with `sin t ≤ 1/2`, `bGateZ ≤ exp(-(cμ·t·4^{-L}))`,
hence `A·exp(cα t)·bGateZ ≤ A·exp(-((cμ·4^{-L} - cα)t))`. -/
theorem gateZ_integrand_le_halfphase_exp_repl
    {d B : ℕ} {V : Type} [Fintype V]
    {p : DynGateParams} {sched : PhaseSchedule} {branch : V → BranchData d B}
    {chiReset chiGate kappa gain : ℝ → ℝ} {readoutP : V → (Fin d → ℝ) → ℝ}
    (sol : SelectorReplicatorDynSol d B V p sched branch chiReset chiGate kappa gain readoutP)
    {A cμ cα t : ℝ} (ht0 : 0 ≤ t) (hA0 : 0 ≤ A) (hcμ0 : 0 ≤ cμ)
    (hpA : p.A = A)
    (hα : sol.α t = Real.exp (cα * t))
    (hμ : sol.μ t = cμ * t)
    (hsin : Real.sin t ≤ (1 / 2 : ℝ)) :
    p.A * sol.α t * bGateZ p.L (sol.μ t) t
      ≤ A * Real.exp (-((cμ * (1 / 4 : ℝ) ^ p.L - cα) * t)) := by
  rw [hpA, hα]
  have hgate :
      bGateZ p.L (sol.μ t) t ≤ Real.exp (-(cμ * t * (1 / 4 : ℝ) ^ p.L)) := by
    rw [hμ]
    simpa [mul_assoc] using bGateZ_le_halfphase p.L (mul_nonneg hcμ0 ht0) hsin
  have hmul :
      Real.exp (cα * t) * bGateZ p.L (sol.μ t) t
        ≤ Real.exp (cα * t) *
            Real.exp (-(cμ * t * (1 / 4 : ℝ) ^ p.L)) :=
    mul_le_mul_of_nonneg_left hgate (Real.exp_pos _).le
  have hA_mul := mul_le_mul_of_nonneg_left hmul hA0
  calc
    A * Real.exp (cα * t) * bGateZ p.L (sol.μ t) t
        = A * (Real.exp (cα * t) * bGateZ p.L (sol.μ t) t) := by ring
    _ ≤ A * (Real.exp (cα * t) *
          Real.exp (-(cμ * t * (1 / 4 : ℝ) ^ p.L))) := hA_mul
    _ = A * Real.exp (-((cμ * (1 / 4 : ℝ) ^ p.L - cα) * t)) := by
      rw [← Real.exp_add]
      ring

/-- Concrete BGP38 z-rate on a half-phase edge:
`A·α(t)·bGateZ(μ(t),t) ≤ exp(50t)`. -/
theorem selector_replicator_gateZ_integrand_le_halfphase_exp
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : SelectorReplicatorDynSol d_U B_U UniversalLocalView bgpParams38 selectorSchedule
      branchU
      (fun t => ((1 + Real.cos t) / 2) ^ Mcy)
      (fun t => ((1 + Real.sin t) / 2) ^ Mcy)
      (fun _ => (κ₀ : ℝ))
      (fun t => (g₀ : ℝ) * Real.exp (bgpParams38.cα * t))
      (universalPval eta heta))
    {t : ℝ} (ht0 : 0 ≤ t) (hsin : Real.sin t ≤ (1 / 2 : ℝ)) :
    bgpParams38.A * sol.α t * bGateZ bgpParams38.L (sol.μ t) t ≤
      Real.exp ((50 : ℝ) * t) := by
  have hα : sol.α t = Real.exp (bgpParams38.cα * t) :=
    sol.alpha_eq_exp selectorSchedule_domain_of_nonneg_structural ht0
  have hμ : sol.μ t = bgpParams38.cμ * t := by
    rw [sol.mu_eq_linear selectorSchedule_domain_of_nonneg_structural ht0,
      sol.μ_at_zero, zero_add]
  have h :=
    gateZ_integrand_le_halfphase_exp_repl
      (sol := sol) (A := (1 : ℝ)) (cμ := bgpParams38.cμ)
      (cα := bgpParams38.cα)
      ht0 (by norm_num) (by norm_num [bgpParams38]) (by norm_num [bgpParams38])
      hα hμ hsin
  calc
    bgpParams38.A * sol.α t * bGateZ bgpParams38.L (sol.μ t) t
        ≤ (1 : ℝ) *
            Real.exp (-((bgpParams38.cμ * (1 / 4 : ℝ) ^ bgpParams38.L -
              bgpParams38.cα) * t)) := h
    _ = Real.exp ((50 : ℝ) * t) := by
      norm_num [bgpParams38]

/-- Concrete BGP38 z-rate on the z-off middle:
`A·α(t)·bGateZ(μ(t),t) ≤ exp(-200t)`. -/
theorem selector_replicator_gateZ_integrand_le_offphase_exp
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : SelectorReplicatorDynSol d_U B_U UniversalLocalView bgpParams38 selectorSchedule
      branchU
      (fun t => ((1 + Real.cos t) / 2) ^ Mcy)
      (fun t => ((1 + Real.sin t) / 2) ^ Mcy)
      (fun _ => (κ₀ : ℝ))
      (fun t => (g₀ : ℝ) * Real.exp (bgpParams38.cα * t))
      (universalPval eta heta))
    {t : ℝ} (ht0 : 0 ≤ t) (hsin : Real.sin t ≤ 0) :
    bgpParams38.A * sol.α t * bGateZ bgpParams38.L (sol.μ t) t ≤
      Real.exp (-((200 : ℝ) * t)) := by
  have hα : sol.α t = Real.exp (bgpParams38.cα * t) :=
    sol.alpha_eq_exp selectorSchedule_domain_of_nonneg_structural ht0
  have hμ : sol.μ t = bgpParams38.cμ * t := by
    rw [sol.mu_eq_linear selectorSchedule_domain_of_nonneg_structural ht0,
      sol.μ_at_zero, zero_add]
  have h :=
    gateZ_integrand_le_offphase_exp_repl
      (sol := sol) (A := (1 : ℝ)) (cμ := bgpParams38.cμ)
      (cα := bgpParams38.cα)
      ht0 (by norm_num) (by norm_num [bgpParams38]) (by norm_num [bgpParams38])
      hα hμ hsin
  calc
    bgpParams38.A * sol.α t * bGateZ bgpParams38.L (sol.μ t) t
        ≤ (1 : ℝ) *
            Real.exp (-((bgpParams38.cμ * (1 / 2 : ℝ) ^ bgpParams38.L -
              bgpParams38.cα) * t)) := h
    _ = Real.exp (-((200 : ℝ) * t)) := by
      norm_num [bgpParams38]

/-- Start of the u-active subwindow inside the inter-read interval. -/
def selectorMUUActiveStart (j : ℕ) : ℝ :=
  (2 : ℝ) * Real.pi * (j : ℝ) + (7 : ℝ) * Real.pi / 6

/-- End of the u-active subwindow inside the inter-read interval. -/
def selectorMUUActiveEnd (j : ℕ) : ℝ :=
  (2 : ℝ) * Real.pi * (j : ℝ) + (11 : ℝ) * Real.pi / 6

/-- Explicit lower bound for the u-active mass on `[7π/6,11π/6]`. -/
def selectorInterReadUActiveMassLower (j : ℕ) : ℝ :=
  Real.exp ((300 : ℝ) * selectorMUUActiveStart j) *
    Real.exp (-((1000 : ℝ) * selectorMUUActiveEnd j * (1 / 4 : ℝ))) *
      ((2 : ℝ) * Real.pi / 3)

theorem selectorInterReadUActiveMassLower_nonneg (j : ℕ) :
    0 ≤ selectorInterReadUActiveMassLower j := by
  dsimp [selectorInterReadUActiveMassLower]
  positivity

/-- Lower bound the actual u-gate mass on the u-active inter-read subwindow. -/
theorem selectorInterReadUActiveMassLower_le_integral
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : SelectorReplicatorDynSol d_U B_U UniversalLocalView bgpParams38 selectorSchedule
      branchU
      (fun t => ((1 + Real.cos t) / 2) ^ Mcy)
      (fun t => ((1 + Real.sin t) / 2) ^ Mcy)
      (fun _ => (κ₀ : ℝ))
      (fun t => (g₀ : ℝ) * Real.exp (bgpParams38.cα * t))
      (universalPval eta heta))
    (j : ℕ) :
    selectorInterReadUActiveMassLower j ≤
      ∫ s in (selectorMUUActiveStart j)..(selectorMUUActiveEnd j),
        bgpParams38.A * sol.α s * bGateU bgpParams38.L (sol.μ s) s := by
  let a : ℝ := selectorMUUActiveStart j
  let b : ℝ := selectorMUUActiveEnd j
  let c : ℝ := Real.exp ((300 : ℝ) * a) *
    Real.exp (-((1000 : ℝ) * b * (1 / 4 : ℝ)))
  have hab : a ≤ b := by
    dsimp [a, b, selectorMUUActiveStart, selectorMUUActiveEnd]
    linarith [Real.pi_pos]
  have ha0 : 0 ≤ a := by
    dsimp [a, selectorMUUActiveStart]
    positivity
  have hg_cont : Continuous fun s : ℝ =>
      bgpParams38.A * sol.α s * bGateU bgpParams38.L (sol.μ s) s := by
    have hq : Continuous fun s : ℝ => qPulse bgpParams38.L s := by
      simp only [qPulse]
      exact ((continuous_const.add Real.continuous_sin).div_const 2).pow
        bgpParams38.L
    have hgateU : Continuous fun s : ℝ =>
        bGateU bgpParams38.L (sol.μ s) s := by
      simp only [bGateU]
      exact Real.continuous_exp.comp (((sol.cont_μ).mul hq).neg)
    simpa [mul_assoc] using
      ((continuous_const.mul sol.cont_α).mul hgateU)
  have hpoint : ∀ s ∈ Icc a b, c ≤
      bgpParams38.A * sol.α s * bGateU bgpParams38.L (sol.μ s) s := by
    intro s hs
    have hs0 : 0 ≤ s := le_trans ha0 hs.1
    have hαs : sol.α s = Real.exp (bgpParams38.cα * s) :=
      sol.alpha_eq_exp selectorSchedule_domain_of_nonneg_structural hs0
    have hμs : sol.μ s = bgpParams38.cμ * s := by
      rw [sol.mu_eq_linear selectorSchedule_domain_of_nonneg_structural hs0,
        sol.μ_at_zero, zero_add]
    have hsin : Real.sin s ≤ -(1 / 2 : ℝ) := by
      apply sin_window_le_neg_half j
      · simpa [a, selectorMUUActiveStart] using hs.1
      · simpa [b, selectorMUUActiveEnd] using hs.2
    have hαle : Real.exp ((300 : ℝ) * a) ≤
        Real.exp ((300 : ℝ) * s) := by
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hs.1 (by norm_num))
    have hgate_active :
        Real.exp (-(sol.μ s * (1 / 4 : ℝ) ^ bgpParams38.L)) ≤
          bGateU bgpParams38.L (sol.μ s) s :=
      bGateU_ge_active bgpParams38.L
        (by rw [hμs]; exact mul_nonneg (by norm_num [bgpParams38]) hs0)
        hsin
    have hgate_floor : Real.exp (-((1000 : ℝ) * b * (1 / 4 : ℝ))) ≤
        bGateU bgpParams38.L (sol.μ s) s := by
      have hfloor :
          Real.exp (-((1000 : ℝ) * b * (1 / 4 : ℝ))) ≤
            Real.exp (-(sol.μ s * (1 / 4 : ℝ) ^ bgpParams38.L)) := by
        apply Real.exp_le_exp.mpr
        rw [hμs]
        norm_num [bgpParams38]
        nlinarith [hs.2]
      exact le_trans hfloor hgate_active
    have hmul := mul_le_mul hαle hgate_floor (Real.exp_pos _).le (Real.exp_pos _).le
    calc
      c ≤ Real.exp ((300 : ℝ) * s) *
          bGateU bgpParams38.L (sol.μ s) s := by
        simpa [c] using hmul
      _ = bgpParams38.A * sol.α s * bGateU bgpParams38.L (sol.μ s) s := by
        rw [hαs]
        norm_num [bgpParams38]
  have hmono :
      (∫ _s in a..b, c) ≤
        ∫ s in a..b,
          bgpParams38.A * sol.α s * bGateU bgpParams38.L (sol.μ s) s :=
    intervalIntegral.integral_mono_on hab _root_.intervalIntegrable_const
      (hg_cont.intervalIntegrable a b) hpoint
  have hconst :
      (∫ _s in a..b, c) = c * (b - a) := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
    ring
  have hmass :
      selectorInterReadUActiveMassLower j = c * (b - a) := by
    dsimp [selectorInterReadUActiveMassLower, selectorMUUActiveStart,
      selectorMUUActiveEnd, a, b, c]
    ring
  calc
    selectorInterReadUActiveMassLower j = c * (b - a) := hmass
    _ = ∫ _s in a..b, c := hconst.symm
    _ ≤ ∫ s in a..b,
          bgpParams38.A * sol.α s * bGateU bgpParams38.L (sol.μ s) s := hmono

/-- If `τ` is before the u-active subwindow, the future `u` kernel to the next
write start includes the whole u-active mass. -/
theorem selectorInterRead_kernel_le_uActiveMass
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : SelectorReplicatorDynSol d_U B_U UniversalLocalView bgpParams38 selectorSchedule
      branchU
      (fun t => ((1 + Real.cos t) / 2) ^ Mcy)
      (fun t => ((1 + Real.sin t) / 2) ^ Mcy)
      (fun _ => (κ₀ : ℝ))
      (fun t => (g₀ : ℝ) * Real.exp (bgpParams38.cα * t))
      (universalPval eta heta))
    (j : ℕ) {τ : ℝ}
    (hτ : τ ∈ Icc (selectorMUWriteReadTime j) (selectorMUUActiveStart j)) :
    Real.exp (-(∫ s in τ..(selectorMUWriteStartTime (j + 1)),
      bgpParams38.A * sol.α s * bGateU bgpParams38.L (sol.μ s) s)) ≤
    Real.exp (-(selectorInterReadUActiveMassLower j)) := by
  let U0 : ℝ := selectorMUUActiveStart j
  let U1 : ℝ := selectorMUUActiveEnd j
  let W : ℝ := selectorMUWriteStartTime (j + 1)
  let kU : ℝ → ℝ := fun s =>
    bgpParams38.A * sol.α s * bGateU bgpParams38.L (sol.μ s) s
  have hτU0 : τ ≤ U0 := by simpa [U0] using hτ.2
  have hU0U1 : U0 ≤ U1 := by
    dsimp [U0, U1, selectorMUUActiveStart, selectorMUUActiveEnd]
    linarith [Real.pi_pos]
  have hU1W : U1 ≤ W := by
    dsimp [U1, W, selectorMUUActiveEnd, selectorMUWriteStartTime]
    push_cast
    linarith [Real.pi_pos]
  have hread0 : 0 ≤ selectorMUWriteReadTime j := by
    unfold selectorMUWriteReadTime
    positivity
  have hτ0 : 0 ≤ τ := le_trans hread0 hτ.1
  have hk_cont : Continuous kU := by
    have hq : Continuous fun s : ℝ => qPulse bgpParams38.L s := by
      simp only [qPulse]
      exact ((continuous_const.add Real.continuous_sin).div_const 2).pow
        bgpParams38.L
    have hgateU : Continuous fun s : ℝ =>
        bGateU bgpParams38.L (sol.μ s) s := by
      simp only [bGateU]
      exact Real.continuous_exp.comp (((sol.cont_μ).mul hq).neg)
    simpa [kU, mul_assoc] using
      ((continuous_const.mul sol.cont_α).mul hgateU)
  have hk_nonneg : ∀ s : ℝ, 0 ≤ s → 0 ≤ kU s := by
    intro s hs0
    have hαs : sol.α s = Real.exp (bgpParams38.cα * s) :=
      sol.alpha_eq_exp selectorSchedule_domain_of_nonneg_structural hs0
    dsimp [kU]
    rw [hαs]
    exact mul_nonneg
      (mul_nonneg (by norm_num [bgpParams38]) (Real.exp_pos _).le)
      (bGateU_pos bgpParams38.L (sol.μ s) s).le
  have hI_left_nonneg : 0 ≤ ∫ s in τ..U0, kU s := by
    apply intervalIntegral.integral_nonneg hτU0
    intro s hs
    exact hk_nonneg s (le_trans hτ0 hs.1)
  have hI_right_nonneg : 0 ≤ ∫ s in U1..W, kU s := by
    apply intervalIntegral.integral_nonneg hU1W
    intro s hs
    have hU10 : 0 ≤ U1 := by
      dsimp [U1, selectorMUUActiveEnd]
      positivity
    exact hk_nonneg s (le_trans hU10 hs.1)
  have hmass_mid :
      selectorInterReadUActiveMassLower j ≤ ∫ s in U0..U1, kU s := by
    simpa [U0, U1, kU] using selectorInterReadUActiveMassLower_le_integral sol j
  have hI : selectorInterReadUActiveMassLower j ≤ ∫ s in τ..W, kU s := by
    have hII : ∀ x y : ℝ, IntervalIntegrable kU MeasureTheory.volume x y :=
      fun x y => hk_cont.intervalIntegrable x y
    have hadd1 :
        (∫ s in τ..U0, kU s) + (∫ s in U0..U1, kU s)
          = ∫ s in τ..U1, kU s :=
      intervalIntegral.integral_add_adjacent_intervals (hII τ U0) (hII U0 U1)
    have hadd2 :
        (∫ s in τ..U1, kU s) + (∫ s in U1..W, kU s)
          = ∫ s in τ..W, kU s :=
      intervalIntegral.integral_add_adjacent_intervals (hII τ U1) (hII U1 W)
    calc
      selectorInterReadUActiveMassLower j
          ≤ ∫ s in U0..U1, kU s := hmass_mid
      _ ≤ (∫ s in τ..U0, kU s) + (∫ s in U0..U1, kU s) := by
        linarith
      _ = ∫ s in τ..U1, kU s := hadd1
      _ ≤ (∫ s in τ..U1, kU s) + (∫ s in U1..W, kU s) := by
        linarith
      _ = ∫ s in τ..W, kU s := hadd2
  exact Real.exp_le_exp.mpr (by linarith)

/-- Settled-window u drift.  The only dynamical input carried here is the
finite box `|z-u|≤Bzu`; the j-dependent decay is discharged by the qPulse
offphase envelope `δuSettled`, whose limit is `0`. -/
theorem u_drift_on_settled_window
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : SelectorReplicatorDynSol d_U B_U UniversalLocalView bgpParams38 selectorSchedule
      branchU
      (fun t => ((1 + Real.cos t) / 2) ^ Mcy)
      (fun t => ((1 + Real.sin t) / 2) ^ Mcy)
      (fun _ => (κ₀ : ℝ))
      (fun t => (g₀ : ℝ) * Real.exp (bgpParams38.cα * t))
      (universalPval eta heta))
    (j : ℕ) (i : Fin d_U) {Bzu : ℝ} (hBzu0 : 0 ≤ Bzu)
    (hdom : ∀ t : ℝ, 0 ≤ t → t ∈ selectorSchedule.domain)
    (hzu : ∀ t ∈ Icc (selectorMUWriteHoldTime j) (selectorMUWriteReadTime j),
      |sol.z t i - sol.u t i| ≤ Bzu) :
    ∀ t ∈ Icc (selectorMUWriteHoldTime j) (selectorMUWriteReadTime j),
      |sol.u t i - sol.u (selectorMUWriteHoldTime j) i| ≤ δuSettled Bzu j := by
  intro t ht
  have ha0 : 0 ≤ selectorMUWriteHoldTime j := by
    unfold selectorMUWriteHoldTime
    positivity
  have hat : selectorMUWriteHoldTime j ≤ t := ht.1
  have hfield :
      ∀ τ ∈ Icc (selectorMUWriteHoldTime j) t,
        |bgpParams38.A * sol.α τ * bGateU bgpParams38.L (sol.μ τ) τ *
          (sol.z τ i - sol.u τ i)|
          ≤ Bzu *
            Real.exp (-(selectorUSettledRate * selectorMUWriteHoldTime j)) := by
    intro τ hτ
    have hτ_full :
        τ ∈ Icc (selectorMUWriteHoldTime j) (selectorMUWriteReadTime j) :=
      ⟨hτ.1, le_trans hτ.2 ht.2⟩
    have hτ0 : 0 ≤ τ := le_trans ha0 hτ.1
    have hατ : sol.α τ = Real.exp (bgpParams38.cα * τ) :=
      sol.alpha_eq_exp hdom hτ0
    have hμτ : sol.μ τ = bgpParams38.cμ * τ := by
      rw [sol.mu_eq_linear hdom hτ0, sol.μ_at_zero, zero_add]
    have hsin : (1 : ℝ) / 2 ≤ Real.sin τ :=
      sin_window_ge j
        (by
          have hselect_le_hold :
              2 * Real.pi * (j : ℝ) + Real.pi / 6 ≤ selectorMUWriteHoldTime j := by
            unfold selectorMUWriteHoldTime
            linarith [Real.pi_pos]
          exact le_trans hselect_le_hold hτ_full.1)
        (by simpa [selectorMUWriteReadTime] using hτ_full.2)
    have hcoef0 :
        0 ≤ bgpParams38.A * sol.α τ * bGateU bgpParams38.L (sol.μ τ) τ := by
      rw [hατ]
      exact mul_nonneg (mul_nonneg (by norm_num [bgpParams38]) (Real.exp_pos _).le)
        (bGateU_pos bgpParams38.L (sol.μ τ) τ).le
    have hcoef_le :
        bgpParams38.A * sol.α τ * bGateU bgpParams38.L (sol.μ τ) τ
          ≤ Real.exp (-(selectorUSettledRate * τ)) := by
      have h :=
        gateU_integrand_le_settled_exp_repl
          (sol := sol) (A := (1 : ℝ)) (cμ := bgpParams38.cμ)
          (cα := bgpParams38.cα)
          hτ0 (by norm_num) (by norm_num [bgpParams38]) (by norm_num [bgpParams38])
          hατ hμτ hsin
      simpa [selectorUSettledRate, bgpParams38] using h
    have hdec :
        Real.exp (-(selectorUSettledRate * τ))
          ≤ Real.exp (-(selectorUSettledRate * selectorMUWriteHoldTime j)) := by
      apply Real.exp_le_exp.mpr
      have hmul : selectorUSettledRate * selectorMUWriteHoldTime j
          ≤ selectorUSettledRate * τ :=
        mul_le_mul_of_nonneg_left hτ.1 selectorUSettledRate_pos.le
      linarith
    calc
      |bgpParams38.A * sol.α τ * bGateU bgpParams38.L (sol.μ τ) τ *
          (sol.z τ i - sol.u τ i)|
          = (bgpParams38.A * sol.α τ * bGateU bgpParams38.L (sol.μ τ) τ) *
              |sol.z τ i - sol.u τ i| := by
            rw [abs_mul, abs_of_nonneg hcoef0]
      _ ≤ Real.exp (-(selectorUSettledRate * τ)) * Bzu :=
            mul_le_mul hcoef_le (hzu τ hτ_full) (abs_nonneg _) (Real.exp_pos _).le
      _ ≤ Real.exp (-(selectorUSettledRate * selectorMUWriteHoldTime j)) * Bzu :=
            mul_le_mul_of_nonneg_right hdec hBzu0
      _ = Bzu * Real.exp (-(selectorUSettledRate * selectorMUWriteHoldTime j)) := by
            ring
  have hhold := hold_bound
    (fun τ => sol.u τ i)
    (fun τ =>
      bgpParams38.A * sol.α τ * bGateU bgpParams38.L (sol.μ τ) τ *
        (sol.z τ i - sol.u τ i))
    (Bzu * Real.exp (-(selectorUSettledRate * selectorMUWriteHoldTime j)))
    (selectorMUWriteHoldTime j) t hat
    (fun τ hτ => sol.u_hasDeriv τ
      (hdom τ (le_trans ha0 hτ.1)) i)
    hfield
  have hlen : t - selectorMUWriteHoldTime j ≤ Real.pi / 3 := by
    have hread :
        selectorMUWriteReadTime j - selectorMUWriteHoldTime j = Real.pi / 3 := by
      unfold selectorMUWriteReadTime selectorMUWriteHoldTime
      ring
    calc
      t - selectorMUWriteHoldTime j
          ≤ selectorMUWriteReadTime j - selectorMUWriteHoldTime j :=
            sub_le_sub_right ht.2 _
      _ = Real.pi / 3 := hread
  have hη0 :
      0 ≤ Bzu * Real.exp (-(selectorUSettledRate * selectorMUWriteHoldTime j)) :=
    mul_nonneg hBzu0 (Real.exp_pos _).le
  calc
    |sol.u t i - sol.u (selectorMUWriteHoldTime j) i|
        ≤ (Bzu * Real.exp (-(selectorUSettledRate * selectorMUWriteHoldTime j))) *
            (t - selectorMUWriteHoldTime j) := hhold
    _ ≤ (Bzu * Real.exp (-(selectorUSettledRate * selectorMUWriteHoldTime j))) *
          (Real.pi / 3) :=
        mul_le_mul_of_nonneg_left hlen hη0
    _ = δuSettled Bzu j := by
        dsimp [δuSettled]
        ring

/-- Prefix-window u drift.  This is the write-prefix analogue of
`u_drift_on_settled_window`: the only dynamical input is a finite box
`|z-u|≤Bzu` on `[selectorMUWriteStartTime j, selectorMUWriteHoldTime j]`. -/
theorem u_drift_on_write_prefix_window
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : SelectorReplicatorDynSol d_U B_U UniversalLocalView bgpParams38 selectorSchedule
      branchU
      (fun t => ((1 + Real.cos t) / 2) ^ Mcy)
      (fun t => ((1 + Real.sin t) / 2) ^ Mcy)
      (fun _ => (κ₀ : ℝ))
      (fun t => (g₀ : ℝ) * Real.exp (bgpParams38.cα * t))
      (universalPval eta heta))
    (j : ℕ) (i : Fin d_U) {Bzu : ℝ} (hBzu0 : 0 ≤ Bzu)
    (hdom : ∀ t : ℝ, 0 ≤ t → t ∈ selectorSchedule.domain)
    (hzu : ∀ t ∈ Icc (selectorMUWriteStartTime j) (selectorMUWriteHoldTime j),
      |sol.z t i - sol.u t i| ≤ Bzu) :
    ∀ t ∈ Icc (selectorMUWriteStartTime j) (selectorMUWriteHoldTime j),
      |sol.u t i - sol.u (selectorMUWriteStartTime j) i| ≤
        δuWritePrefix Bzu j := by
  intro t ht
  have ha0 : 0 ≤ selectorMUWriteStartTime j :=
    selectorMUWriteStartTime_nonneg j
  have hat : selectorMUWriteStartTime j ≤ t := ht.1
  have hfield :
      ∀ τ ∈ Icc (selectorMUWriteStartTime j) t,
        |bgpParams38.A * sol.α τ * bGateU bgpParams38.L (sol.μ τ) τ *
          (sol.z τ i - sol.u τ i)|
          ≤ Bzu *
            Real.exp (-(selectorUSettledRate * selectorMUWriteStartTime j)) := by
    intro τ hτ
    have hτ_full :
        τ ∈ Icc (selectorMUWriteStartTime j) (selectorMUWriteHoldTime j) :=
      ⟨hτ.1, le_trans hτ.2 ht.2⟩
    have hτ0 : 0 ≤ τ := le_trans ha0 hτ.1
    have hατ : sol.α τ = Real.exp (bgpParams38.cα * τ) :=
      sol.alpha_eq_exp hdom hτ0
    have hμτ : sol.μ τ = bgpParams38.cμ * τ := by
      rw [sol.mu_eq_linear hdom hτ0, sol.μ_at_zero, zero_add]
    have hsin : (1 : ℝ) / 2 ≤ Real.sin τ :=
      sin_window_ge j
        (by simpa [selectorMUWriteStartTime] using hτ_full.1)
        (by
          have hτ_read : τ ≤ selectorMUWriteReadTime j :=
            le_trans hτ_full.2 (selectorMUWriteHold_le_read j)
          simpa [selectorMUWriteReadTime] using hτ_read)
    have hcoef0 :
        0 ≤ bgpParams38.A * sol.α τ * bGateU bgpParams38.L (sol.μ τ) τ := by
      rw [hατ]
      exact mul_nonneg (mul_nonneg (by norm_num [bgpParams38]) (Real.exp_pos _).le)
        (bGateU_pos bgpParams38.L (sol.μ τ) τ).le
    have hcoef_le :
        bgpParams38.A * sol.α τ * bGateU bgpParams38.L (sol.μ τ) τ
          ≤ Real.exp (-(selectorUSettledRate * τ)) := by
      have h :=
        gateU_integrand_le_settled_exp_repl
          (sol := sol) (A := (1 : ℝ)) (cμ := bgpParams38.cμ)
          (cα := bgpParams38.cα)
          hτ0 (by norm_num) (by norm_num [bgpParams38]) (by norm_num [bgpParams38])
          hατ hμτ hsin
      simpa [selectorUSettledRate, bgpParams38] using h
    have hdec :
        Real.exp (-(selectorUSettledRate * τ))
          ≤ Real.exp (-(selectorUSettledRate * selectorMUWriteStartTime j)) := by
      apply Real.exp_le_exp.mpr
      have hmul : selectorUSettledRate * selectorMUWriteStartTime j
          ≤ selectorUSettledRate * τ :=
        mul_le_mul_of_nonneg_left hτ.1 selectorUSettledRate_pos.le
      linarith
    calc
      |bgpParams38.A * sol.α τ * bGateU bgpParams38.L (sol.μ τ) τ *
          (sol.z τ i - sol.u τ i)|
          = (bgpParams38.A * sol.α τ * bGateU bgpParams38.L (sol.μ τ) τ) *
              |sol.z τ i - sol.u τ i| := by
            rw [abs_mul, abs_of_nonneg hcoef0]
      _ ≤ Real.exp (-(selectorUSettledRate * τ)) * Bzu :=
            mul_le_mul hcoef_le (hzu τ hτ_full) (abs_nonneg _) (Real.exp_pos _).le
      _ ≤ Real.exp (-(selectorUSettledRate * selectorMUWriteStartTime j)) * Bzu :=
            mul_le_mul_of_nonneg_right hdec hBzu0
      _ = Bzu * Real.exp (-(selectorUSettledRate * selectorMUWriteStartTime j)) := by
            ring
  have hhold := hold_bound
    (fun τ => sol.u τ i)
    (fun τ =>
      bgpParams38.A * sol.α τ * bGateU bgpParams38.L (sol.μ τ) τ *
        (sol.z τ i - sol.u τ i))
    (Bzu * Real.exp (-(selectorUSettledRate * selectorMUWriteStartTime j)))
    (selectorMUWriteStartTime j) t hat
    (fun τ hτ => sol.u_hasDeriv τ
      (hdom τ (le_trans ha0 hτ.1)) i)
    hfield
  have hlen : t - selectorMUWriteStartTime j ≤ Real.pi / 3 := by
    have hhold :
        selectorMUWriteHoldTime j - selectorMUWriteStartTime j = Real.pi / 3 := by
      unfold selectorMUWriteHoldTime selectorMUWriteStartTime
      ring
    calc
      t - selectorMUWriteStartTime j
          ≤ selectorMUWriteHoldTime j - selectorMUWriteStartTime j :=
            sub_le_sub_right ht.2 _
      _ = Real.pi / 3 := hhold
  have hη0 :
      0 ≤ Bzu * Real.exp (-(selectorUSettledRate * selectorMUWriteStartTime j)) :=
    mul_nonneg hBzu0 (Real.exp_pos _).le
  calc
    |sol.u t i - sol.u (selectorMUWriteStartTime j) i|
        ≤ (Bzu * Real.exp (-(selectorUSettledRate * selectorMUWriteStartTime j))) *
            (t - selectorMUWriteStartTime j) := hhold
    _ ≤ (Bzu * Real.exp (-(selectorUSettledRate * selectorMUWriteStartTime j))) *
          (Real.pi / 3) :=
        mul_le_mul_of_nonneg_left hlen hη0
    _ = δuWritePrefix Bzu j := by
        dsimp [δuWritePrefix]
        ring

/-- Uniform prefix drift from a uniform prefix `|z-u|` envelope. -/
theorem u_drift_on_write_prefix_window_uniform
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : SelectorReplicatorDynSol d_U B_U UniversalLocalView bgpParams38 selectorSchedule
      branchU
      (fun t => ((1 + Real.cos t) / 2) ^ Mcy)
      (fun t => ((1 + Real.sin t) / 2) ^ Mcy)
      (fun _ => (κ₀ : ℝ))
      (fun t => (g₀ : ℝ) * Real.exp (bgpParams38.cα * t))
      (universalPval eta heta))
    {Bzu : ℝ} (hBzu0 : 0 ≤ Bzu)
    (hdom : ∀ t : ℝ, 0 ≤ t → t ∈ selectorSchedule.domain)
    (hzu : ∀ j i, ∀ t ∈ Icc (selectorMUWriteStartTime j) (selectorMUWriteHoldTime j),
      |sol.z t i - sol.u t i| ≤ Bzu) :
    ∀ j i, ∀ t ∈ Icc (selectorMUWriteStartTime j) (selectorMUWriteHoldTime j),
      |sol.u t i - sol.u (selectorMUWriteStartTime j) i| ≤
        δuWritePrefix Bzu 0 := by
  intro j i t ht
  exact (u_drift_on_write_prefix_window sol j i hBzu0 hdom
    (hzu j i) t ht).trans (δuWritePrefix_le_initial hBzu0 j)

/-! ## Settled z-write mass -/

/-- End of the settled z-write lower-bound subwindow: `2πj + 3π/4`. -/
def selectorMUSettledWriteSubEnd (j : ℕ) : ℝ :=
  (2 : ℝ) * Real.pi * (j : ℝ) + (3 : ℝ) * Real.pi / 4

/-- Explicit settled z-write lower bound on `[π/2, 3π/4]`. -/
def selectorSettledWriteIntLower (j : ℕ) : ℝ :=
  Real.exp ((300 : ℝ) * selectorMUWriteHoldTime j) *
    Real.exp (-((1000 : ℝ) * selectorMUSettledWriteSubEnd j *
      ((1 - Real.sqrt 2 / 2) / 2))) *
      (Real.pi / 4)

/-- Start of the tight early z-write subwindow inside
`[selectorMUWriteStartTime j, selectorMUWriteHoldTime j]`. -/
def selectorMUEarlyWriteSubStart (j : ℕ) : ℝ :=
  (2 : ℝ) * Real.pi * (j : ℝ) + Real.pi / 4

/-- Explicit lower bound on the early z-write subwindow
`[2πj + π/4, 2πj + π/2]`. -/
def selectorEarlyWriteIntLower (j : ℕ) : ℝ :=
  Real.exp ((300 : ℝ) * selectorMUEarlyWriteSubStart j) *
    Real.exp (-((1000 : ℝ) * selectorMUWriteHoldTime j *
      ((1 - Real.sqrt 2 / 2) / 2))) *
      (Real.pi / 4)

/-- Closed exponential form of the settled write-integral lower bound. -/
theorem selectorSettledWriteIntLower_eq_exp (j : ℕ) :
    let rmax : ℝ := (1 - Real.sqrt 2 / 2) / 2
    let s : ℝ := 2 * Real.pi * ((300 : ℝ) - (1000 : ℝ) * rmax)
    let c0 : ℝ := (300 : ℝ) * (Real.pi / 2) -
      (1000 : ℝ) * (3 * Real.pi / 4) * rmax
    selectorSettledWriteIntLower j =
      (Real.pi / 4) * Real.exp (s * (j : ℝ) + c0) := by
  dsimp
  unfold selectorSettledWriteIntLower selectorMUWriteHoldTime
    selectorMUSettledWriteSubEnd
  rw [← Real.exp_add]
  ring_nf

/-- Closed exponential form of the early write-integral lower bound. -/
theorem selectorEarlyWriteIntLower_eq_exp (j : ℕ) :
    let rmax : ℝ := (1 - Real.sqrt 2 / 2) / 2
    let s : ℝ := 2 * Real.pi * ((300 : ℝ) - (1000 : ℝ) * rmax)
    let c0 : ℝ := (300 : ℝ) * (Real.pi / 4) -
      (1000 : ℝ) * (Real.pi / 2) * rmax
    selectorEarlyWriteIntLower j =
      (Real.pi / 4) * Real.exp (s * (j : ℝ) + c0) := by
  dsimp
  unfold selectorEarlyWriteIntLower selectorMUEarlyWriteSubStart
    selectorMUWriteHoldTime
  rw [← Real.exp_add]
  ring_nf

theorem selectorSettledWriteIntLower_pos (j : ℕ) :
    0 < selectorSettledWriteIntLower j := by
  unfold selectorSettledWriteIntLower
  positivity

theorem selectorEarlyWriteIntLower_pos (j : ℕ) :
    0 < selectorEarlyWriteIntLower j := by
  unfold selectorEarlyWriteIntLower
  positivity

/-- The settled write lower bound pointwise dominates the Hoff exponent used in
the canonical hold envelope. -/
theorem selectorSettledWriteIntLower_ge_hoffExponent
    (j : ℕ) :
    (1 / 8 : ℝ) * (2 * Real.pi * (j : ℝ) + Real.pi) ≤
      selectorSettledWriteIntLower j := by
  let rmax : ℝ := (1 - Real.sqrt 2 / 2) / 2
  let s : ℝ := 2 * Real.pi * ((300 : ℝ) - (1000 : ℝ) * rmax)
  let c0 : ℝ := (300 : ℝ) * (Real.pi / 2) -
    (1000 : ℝ) * (3 * Real.pi / 4) * rmax
  have hsqrt_ge : (4 / 3 : ℝ) ≤ Real.sqrt 2 := by
    have hsqrt_nonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    have hsqr : (Real.sqrt 2) ^ 2 = (2 : ℝ) := by
      rw [Real.sq_sqrt] <;> norm_num
    nlinarith
  have hrmax_le : rmax ≤ (1 / 6 : ℝ) := by
    dsimp [rmax]
    nlinarith [hsqrt_ge]
  have hs_ge_one : (1 : ℝ) ≤ s := by
    dsimp [s]
    nlinarith [Real.pi_gt_three, hrmax_le]
  have hc0_nonneg : 0 ≤ c0 := by
    dsimp [c0]
    nlinarith [Real.pi_pos, hrmax_le]
  have hj : 0 ≤ (j : ℝ) := by exact_mod_cast Nat.zero_le j
  have hs_j : (j : ℝ) ≤ s * (j : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_right hs_ge_one hj
    simpa [one_mul] using hmul
  have hbase :
      (1 / 8 : ℝ) * (2 * Real.pi * (j : ℝ) + Real.pi) ≤
        (Real.pi / 4) * (1 + (j : ℝ)) := by
    nlinarith [Real.pi_pos, hj]
  have hright :
      (Real.pi / 4) * (1 + (j : ℝ)) ≤
        (Real.pi / 4) * (1 + (s * (j : ℝ) + c0)) := by
    nlinarith [Real.pi_pos, hj, hs_j, hc0_nonneg]
  have hlin :
      (1 / 8 : ℝ) * (2 * Real.pi * (j : ℝ) + Real.pi) ≤
        (Real.pi / 4) * (1 + (s * (j : ℝ) + c0)) :=
    le_trans hbase hright
  have hexp :
      1 + (s * (j : ℝ) + c0) ≤ Real.exp (s * (j : ℝ) + c0) := by
    simpa [add_comm] using Real.add_one_le_exp (s * (j : ℝ) + c0)
  have hmul :
      (Real.pi / 4) * (1 + (s * (j : ℝ) + c0)) ≤
        (Real.pi / 4) * Real.exp (s * (j : ℝ) + c0) :=
    mul_le_mul_of_nonneg_left hexp (by positivity)
  calc
    (1 / 8 : ℝ) * (2 * Real.pi * (j : ℝ) + Real.pi)
        ≤ (Real.pi / 4) * (1 + (s * (j : ℝ) + c0)) := hlin
    _ ≤ (Real.pi / 4) * Real.exp (s * (j : ℝ) + c0) := hmul
    _ = selectorSettledWriteIntLower j := by
      rw [selectorSettledWriteIntLower_eq_exp]

/-- The settled-write contraction term is pointwise bounded by the canonical
Hoff exponential rate. -/
theorem exp_neg_selectorSettledWriteIntLower_le_hoffRate
    (j : ℕ) :
    Real.exp (-selectorSettledWriteIntLower j) ≤
      Real.exp (-((1 / 8 : ℝ) * (2 * Real.pi * (j : ℝ) + Real.pi))) :=
  Real.exp_le_exp.mpr
    (neg_le_neg (selectorSettledWriteIntLower_ge_hoffExponent j))

theorem selectorMUWriteHold_le_settledSubEnd (j : ℕ) :
    selectorMUWriteHoldTime j ≤ selectorMUSettledWriteSubEnd j := by
  unfold selectorMUWriteHoldTime selectorMUSettledWriteSubEnd
  linarith [Real.pi_pos]

theorem selectorMUWriteStart_le_earlySubStart (j : ℕ) :
    selectorMUWriteStartTime j ≤ selectorMUEarlyWriteSubStart j := by
  unfold selectorMUWriteStartTime selectorMUEarlyWriteSubStart
  linarith [Real.pi_pos]

theorem selectorMUEarlySubStart_le_writeHold (j : ℕ) :
    selectorMUEarlyWriteSubStart j ≤ selectorMUWriteHoldTime j := by
  unfold selectorMUEarlyWriteSubStart selectorMUWriteHoldTime
  linarith [Real.pi_pos]

theorem selectorMUSettledSubEnd_le_read (j : ℕ) :
    selectorMUSettledWriteSubEnd j ≤ selectorMUWriteReadTime j := by
  unfold selectorMUSettledWriteSubEnd selectorMUWriteReadTime
  linarith [Real.pi_pos]

theorem selectorSettledWriteIntLower_tendsto_atTop :
    Tendsto selectorSettledWriteIntLower atTop atTop := by
  have hπ := Real.pi_pos
  set rmax : ℝ := (1 - Real.sqrt 2 / 2) / 2 with hrmax
  set s : ℝ := 2 * Real.pi * ((300 : ℝ) - (1000 : ℝ) * rmax) with hs
  set c0 : ℝ := (300 : ℝ) * (Real.pi / 2) -
    (1000 : ℝ) * (3 * Real.pi / 4) * rmax with hc0
  have hsqrt_ge : (4 / 3 : ℝ) ≤ Real.sqrt 2 := by
    have hsqrt_nonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    have hsqr : (Real.sqrt 2) ^ 2 = (2 : ℝ) := by
      rw [Real.sq_sqrt] <;> norm_num
    nlinarith
  have hrmax_le : rmax ≤ (1 / 6 : ℝ) := by
    rw [hrmax]
    nlinarith [hsqrt_ge]
  have hrate : (0 : ℝ) < (300 : ℝ) - (1000 : ℝ) * rmax := by
    nlinarith [hrmax_le]
  have hrw : ∀ j : ℕ, selectorSettledWriteIntLower j =
      (Real.pi / 4) * Real.exp (s * (j : ℝ) + c0) := by
    intro j
    unfold selectorSettledWriteIntLower selectorMUWriteHoldTime selectorMUSettledWriteSubEnd
    rw [← Real.exp_add]
    rw [hs, hc0, hrmax]
    ring_nf
  have hs_pos : 0 < s := by
    rw [hs, hrmax]
    nlinarith [Real.pi_pos, hrate]
  have hlin :
      Tendsto (fun j : ℕ => s * (j : ℝ) + c0) atTop atTop := by
    apply Filter.Tendsto.atTop_add _ tendsto_const_nhds
    exact Filter.Tendsto.const_mul_atTop hs_pos tendsto_natCast_atTop_atTop
  have hexp :
      Tendsto (fun j : ℕ => Real.exp (s * (j : ℝ) + c0)) atTop atTop :=
    Real.tendsto_exp_atTop.comp hlin
  have hmul :
      Tendsto (fun j : ℕ => (Real.pi / 4) * Real.exp (s * (j : ℝ) + c0))
        atTop atTop :=
    Filter.Tendsto.const_mul_atTop (by positivity) hexp
  refine hmul.congr' ?_
  filter_upwards [] with j
  exact (hrw j).symm

/-- The explicit early z-write lower bound tends to infinity. -/
theorem selectorEarlyWriteIntLower_tendsto_atTop :
    Tendsto selectorEarlyWriteIntLower atTop atTop := by
  set rmax : ℝ := (1 - Real.sqrt 2 / 2) / 2 with hrmax
  set s : ℝ := 2 * Real.pi * ((300 : ℝ) - (1000 : ℝ) * rmax) with hs
  set c0 : ℝ := (300 : ℝ) * (Real.pi / 4) -
    (1000 : ℝ) * (Real.pi / 2) * rmax with hc0
  have hsqrt_ge : (4 / 3 : ℝ) ≤ Real.sqrt 2 := by
    have hsqrt_nonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    have hsqr : (Real.sqrt 2) ^ 2 = (2 : ℝ) := by
      rw [Real.sq_sqrt] <;> norm_num
    nlinarith
  have hrmax_le : rmax ≤ (1 / 6 : ℝ) := by
    rw [hrmax]
    nlinarith [hsqrt_ge]
  have hrate : (0 : ℝ) < (300 : ℝ) - (1000 : ℝ) * rmax := by
    nlinarith [hrmax_le]
  have hrw : ∀ j : ℕ, selectorEarlyWriteIntLower j =
      (Real.pi / 4) * Real.exp (s * (j : ℝ) + c0) := by
    intro j
    unfold selectorEarlyWriteIntLower selectorMUEarlyWriteSubStart
      selectorMUWriteHoldTime
    rw [← Real.exp_add]
    rw [hs, hc0, hrmax]
    ring_nf
  have hs_pos : 0 < s := by
    rw [hs, hrmax]
    nlinarith [Real.pi_pos, hrate]
  have hlin :
      Tendsto (fun j : ℕ => s * (j : ℝ) + c0) atTop atTop := by
    apply Filter.Tendsto.atTop_add _ tendsto_const_nhds
    exact Filter.Tendsto.const_mul_atTop hs_pos tendsto_natCast_atTop_atTop
  have hexp :
      Tendsto (fun j : ℕ => Real.exp (s * (j : ℝ) + c0)) atTop atTop :=
    Real.tendsto_exp_atTop.comp hlin
  have hmul :
      Tendsto (fun j : ℕ => (Real.pi / 4) * Real.exp (s * (j : ℝ) + c0))
        atTop atTop :=
    Filter.Tendsto.const_mul_atTop (by positivity) hexp
  refine hmul.congr' ?_
  filter_upwards [] with j
  exact (hrw j).symm

/-- Replicator sibling of `write_Z_integral_lower`. -/
theorem write_Z_integral_lower_repl
    {d B : ℕ} {V : Type} [Fintype V]
    {p : DynGateParams} {sched : PhaseSchedule} {branch : V → BranchData d B}
    {chiResetF chiGateF kappaF gainF : ℝ → ℝ} {Pv : V → (Fin d → ℝ) → ℝ}
    (sol : SelectorReplicatorDynSol d B V p sched branch chiResetF chiGateF kappaF gainF Pv)
    {a b cμ cα A : ℝ} (hab : a ≤ b) (ha0 : 0 ≤ a) (hA : 0 ≤ A)
    (hcμ : 0 ≤ cμ) (hcα : 0 ≤ cα)
    (hpA : p.A = A) (hpL : p.L = 1)
    (hg_cont : Continuous (fun t => p.A * sol.α t * bGateZ p.L (sol.μ t) t))
    (hα : ∀ t ∈ Icc a b, sol.α t = Real.exp (cα * t))
    (hμ : ∀ t ∈ Icc a b, sol.μ t = cμ * t)
    (hsin : ∀ t ∈ Icc a b, Real.sqrt 2 / 2 ≤ Real.sin t) :
    A * Real.exp (cα * a) * Real.exp (-(cμ * b * ((1 - Real.sqrt 2 / 2) / 2))) *
        (b - a)
      ≤ ∫ t in a..b, p.A * sol.α t * bGateZ p.L (sol.μ t) t := by
  set rmax : ℝ := (1 - Real.sqrt 2 / 2) / 2 with hrmax
  have hrmax0 : 0 ≤ rmax := by
    have h2 : Real.sqrt 2 ≤ 2 := by
      have := Real.sqrt_le_sqrt (by norm_num : (2 : ℝ) ≤ 4)
      simpa [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq] using this
    rw [hrmax]
    nlinarith [Real.sqrt_nonneg 2]
  set φ : ℝ → ℝ := fun t => p.A * sol.α t * bGateZ p.L (sol.μ t) t with hφdef
  have hφc : Continuous φ := hg_cont
  have hlb : ∀ t ∈ Icc a b,
      A * Real.exp (cα * a) * Real.exp (-(cμ * b * rmax)) ≤ φ t := by
    intro t ht
    have hat : a ≤ t := ht.1
    have htb : t ≤ b := ht.2
    have ht0 : 0 ≤ t := le_trans ha0 hat
    rw [hφdef]
    simp only
    rw [hpA, hα t ht]
    have hαle : Real.exp (cα * a) ≤ Real.exp (cα * t) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_left hat hcα
    have hgate : Real.exp (-(cμ * b * rmax)) ≤ bGateZ p.L (sol.μ t) t := by
      rw [hpL, hμ t ht]
      have hsint : Real.sqrt 2 / 2 ≤ Real.sin t := hsin t ht
      have hrp : rPulse 1 t ≤ rmax := rPulse_le_sqrt2_window hsint
      have hμt : cμ * t ≤ cμ * b := mul_le_mul_of_nonneg_left htb hcμ
      have hμt0 : 0 ≤ cμ * t := mul_nonneg hcμ ht0
      calc
        Real.exp (-(cμ * b * rmax))
            ≤ Real.exp (-(cμ * t * rPulse 1 t)) := by
              apply Real.exp_le_exp.mpr
              have hrp0 : 0 ≤ rPulse 1 t := rPulse_nonneg 1 t
              nlinarith [mul_nonneg hμt0 hrp0]
        _ = bGateZ 1 (cμ * t) t := by
              unfold bGateZ
              ring_nf
    have hmul := mul_le_mul hαle hgate (Real.exp_pos _).le (Real.exp_pos _).le
    have hfin := mul_le_mul_of_nonneg_left hmul hA
    calc
      A * Real.exp (cα * a) * Real.exp (-(cμ * b * rmax))
          = A * (Real.exp (cα * a) * Real.exp (-(cμ * b * rmax))) := by ring
      _ ≤ A * (Real.exp (cα * t) * bGateZ p.L (sol.μ t) t) := hfin
      _ = A * Real.exp (cα * t) * bGateZ p.L (sol.μ t) t := by ring
  have hconst : (∫ _t in a..b, A * Real.exp (cα * a) * Real.exp (-(cμ * b * rmax)))
      = A * Real.exp (cα * a) * Real.exp (-(cμ * b * rmax)) * (b - a) := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
    ring
  calc
    A * Real.exp (cα * a) * Real.exp (-(cμ * b * rmax)) * (b - a)
        = ∫ _t in a..b, A * Real.exp (cα * a) * Real.exp (-(cμ * b * rmax)) :=
          hconst.symm
    _ ≤ ∫ t in a..b, φ t :=
        intervalIntegral.integral_mono_on hab _root_.intervalIntegrable_const
          (hφc.intervalIntegrable a b) hlb

/-- The early z-write integral dominates the explicit lower bound on the full
prefix-to-hold interval. -/
theorem selector_early_writeIntegral_lower_lbd_repl
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : SelectorReplicatorDynSol d_U B_U UniversalLocalView bgpParams38 selectorSchedule
      branchU
      (fun t => ((1 + Real.cos t) / 2) ^ Mcy)
      (fun t => ((1 + Real.sin t) / 2) ^ Mcy)
      (fun _ => (κ₀ : ℝ))
      (fun t => (g₀ : ℝ) * Real.exp (bgpParams38.cα * t))
      (universalPval eta heta))
    (j : ℕ)
    (hdom : ∀ t : ℝ, 0 ≤ t → t ∈ selectorSchedule.domain)
    (hg_cont : Continuous (fun t => bgpParams38.A * sol.α t *
      bGateZ bgpParams38.L (sol.μ t) t)) :
    selectorEarlyWriteIntLower j
      ≤ ∫ t in selectorMUWriteStartTime j..selectorMUWriteHoldTime j,
          bgpParams38.A * sol.α t * bGateZ bgpParams38.L (sol.μ t) t := by
  let a := selectorMUEarlyWriteSubStart j
  let b := selectorMUWriteHoldTime j
  have ha0 : 0 ≤ a := by
    dsimp [a, selectorMUEarlyWriteSubStart]
    positivity
  have hab : a ≤ b := by
    dsimp [a, b]
    exact selectorMUEarlySubStart_le_writeHold j
  have hα : ∀ t ∈ Icc a b, sol.α t = Real.exp ((300 : ℝ) * t) := by
    intro t ht
    rw [sol.alpha_eq_exp hdom (le_trans ha0 ht.1)]
    norm_num [bgpParams38]
  have hμ : ∀ t ∈ Icc a b, sol.μ t = (1000 : ℝ) * t := by
    intro t ht
    rw [sol.mu_eq_linear hdom (le_trans ha0 ht.1), sol.μ_at_zero]
    norm_num [bgpParams38]
  have hsin : ∀ t ∈ Icc a b, Real.sqrt 2 / 2 ≤ Real.sin t := by
    intro t ht
    exact sin_window_ge_sqrt2 j
      (by simpa [a, selectorMUEarlyWriteSubStart] using ht.1)
      (by
        have hright : selectorMUWriteHoldTime j ≤
            2 * Real.pi * (j : ℝ) + 3 * Real.pi / 4 := by
          unfold selectorMUWriteHoldTime
          linarith [Real.pi_pos]
        exact le_trans (by simpa [b] using ht.2) hright)
  have hsub :=
    write_Z_integral_lower_repl
      (sol := sol) (a := a) (b := b)
      (cμ := (1000 : ℝ)) (cα := (300 : ℝ)) (A := (1 : ℝ))
      hab ha0 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [bgpParams38]) (by norm_num [bgpParams38])
      hg_cont hα hμ hsin
  have hid :
      (1 : ℝ) * Real.exp ((300 : ℝ) * a) *
          Real.exp (-((1000 : ℝ) * b * ((1 - Real.sqrt 2 / 2) / 2))) *
          (b - a) = selectorEarlyWriteIntLower j := by
    dsimp [a, b]
    unfold selectorEarlyWriteIntLower selectorMUEarlyWriteSubStart
      selectorMUWriteHoldTime
    ring
  have hsub' :
      selectorEarlyWriteIntLower j ≤ ∫ t in a..b,
        bgpParams38.A * sol.α t * bGateZ bgpParams38.L (sol.μ t) t := by
    rwa [hid] at hsub
  have hcont_int : ∀ a b : ℝ,
      IntervalIntegrable
        (fun t : ℝ => bgpParams38.A * sol.α t *
          bGateZ bgpParams38.L (sol.μ t) t)
        MeasureTheory.volume a b :=
    fun a b => hg_cont.intervalIntegrable a b
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (hcont_int (selectorMUWriteStartTime j) a)
    (hcont_int a b)
  have hprefix_nonneg :
      0 ≤ ∫ t in selectorMUWriteStartTime j..a,
        bgpParams38.A * sol.α t * bGateZ bgpParams38.L (sol.μ t) t := by
    apply intervalIntegral.integral_nonneg
      (by
        dsimp [a]
        exact selectorMUWriteStart_le_earlySubStart j)
    intro t ht
    have ht0 : 0 ≤ t :=
      le_trans (selectorMUWriteStartTime_nonneg j) ht.1
    exact selector_replicator_gateZ_integrand_nonneg sol hdom
      (by norm_num [bgpParams38]) ht0
  calc
    selectorEarlyWriteIntLower j
        ≤ ∫ t in a..b,
            bgpParams38.A * sol.α t * bGateZ bgpParams38.L (sol.μ t) t := hsub'
    _ ≤ (∫ t in selectorMUWriteStartTime j..a,
            bgpParams38.A * sol.α t * bGateZ bgpParams38.L (sol.μ t) t) +
          ∫ t in a..b,
            bgpParams38.A * sol.α t * bGateZ bgpParams38.L (sol.μ t) t := by
      linarith
    _ = ∫ t in selectorMUWriteStartTime j..selectorMUWriteHoldTime j,
          bgpParams38.A * sol.α t * bGateZ bgpParams38.L (sol.μ t) t := by
      simpa [a, b] using hadd

/-- The early z-write subwindow `[selectorMUEarlyWriteSubStart j,
selectorMUWriteHoldTime j]` alone dominates the explicit early lower bound. -/
theorem selector_early_writeIntegral_lower_sub_lbd_repl
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : SelectorReplicatorDynSol d_U B_U UniversalLocalView bgpParams38 selectorSchedule
      branchU
      (fun t => ((1 + Real.cos t) / 2) ^ Mcy)
      (fun t => ((1 + Real.sin t) / 2) ^ Mcy)
      (fun _ => (κ₀ : ℝ))
      (fun t => (g₀ : ℝ) * Real.exp (bgpParams38.cα * t))
      (universalPval eta heta))
    (j : ℕ)
    (hdom : ∀ t : ℝ, 0 ≤ t → t ∈ selectorSchedule.domain)
    (hg_cont : Continuous (fun t => bgpParams38.A * sol.α t *
      bGateZ bgpParams38.L (sol.μ t) t)) :
    selectorEarlyWriteIntLower j
      ≤ ∫ t in selectorMUEarlyWriteSubStart j..selectorMUWriteHoldTime j,
          bgpParams38.A * sol.α t * bGateZ bgpParams38.L (sol.μ t) t := by
  let a := selectorMUEarlyWriteSubStart j
  let b := selectorMUWriteHoldTime j
  have ha0 : 0 ≤ a := by
    dsimp [a, selectorMUEarlyWriteSubStart]
    positivity
  have hab : a ≤ b := by
    dsimp [a, b]
    exact selectorMUEarlySubStart_le_writeHold j
  have hα : ∀ t ∈ Icc a b, sol.α t = Real.exp ((300 : ℝ) * t) := by
    intro t ht
    rw [sol.alpha_eq_exp hdom (le_trans ha0 ht.1)]
    norm_num [bgpParams38]
  have hμ : ∀ t ∈ Icc a b, sol.μ t = (1000 : ℝ) * t := by
    intro t ht
    rw [sol.mu_eq_linear hdom (le_trans ha0 ht.1), sol.μ_at_zero]
    norm_num [bgpParams38]
  have hsin : ∀ t ∈ Icc a b, Real.sqrt 2 / 2 ≤ Real.sin t := by
    intro t ht
    exact sin_window_ge_sqrt2 j
      (by simpa [a, selectorMUEarlyWriteSubStart] using ht.1)
      (by
        have hright : selectorMUWriteHoldTime j ≤
            2 * Real.pi * (j : ℝ) + 3 * Real.pi / 4 := by
          unfold selectorMUWriteHoldTime
          linarith [Real.pi_pos]
        exact le_trans (by simpa [b] using ht.2) hright)
  have hsub :=
    write_Z_integral_lower_repl
      (sol := sol) (a := a) (b := b)
      (cμ := (1000 : ℝ)) (cα := (300 : ℝ)) (A := (1 : ℝ))
      hab ha0 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [bgpParams38]) (by norm_num [bgpParams38])
      hg_cont hα hμ hsin
  have hid :
      (1 : ℝ) * Real.exp ((300 : ℝ) * a) *
          Real.exp (-((1000 : ℝ) * b * ((1 - Real.sqrt 2 / 2) / 2))) *
          (b - a) = selectorEarlyWriteIntLower j := by
    dsimp [a, b]
    unfold selectorEarlyWriteIntLower selectorMUEarlyWriteSubStart
      selectorMUWriteHoldTime
    ring
  rwa [hid] at hsub

/-- The terminal z-write kernel puts exponentially small mass before the early
subwindow. -/
theorem selector_early_write_kernel_prefix_mass_le_exp
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : SelectorReplicatorDynSol d_U B_U UniversalLocalView bgpParams38 selectorSchedule
      branchU
      (fun t => ((1 + Real.cos t) / 2) ^ Mcy)
      (fun t => ((1 + Real.sin t) / 2) ^ Mcy)
      (fun _ => (κ₀ : ℝ))
      (fun t => (g₀ : ℝ) * Real.exp (bgpParams38.cα * t))
      (universalPval eta heta))
    (j : ℕ)
    (hdom : ∀ t : ℝ, 0 ≤ t → t ∈ selectorSchedule.domain)
    (hg_cont : Continuous (fun t => bgpParams38.A * sol.α t *
      bGateZ bgpParams38.L (sol.μ t) t)) :
    (∫ t in selectorMUWriteStartTime j..selectorMUEarlyWriteSubStart j,
        Real.exp (-(∫ s in t..selectorMUWriteHoldTime j,
          bgpParams38.A * sol.α s * bGateZ bgpParams38.L (sol.μ s) s)) *
          (bgpParams38.A * sol.α t * bGateZ bgpParams38.L (sol.μ t) t))
      ≤ Real.exp (-(selectorEarlyWriteIntLower j)) := by
  let k : ℝ → ℝ := fun t =>
    bgpParams38.A * sol.α t * bGateZ bgpParams38.L (sol.μ t) t
  have hprefix :=
    terminal_kernel_prefix_mass_le_exp k
      (selectorMUWriteStartTime j) (selectorMUEarlyWriteSubStart j)
      (selectorMUWriteHoldTime j)
      (selectorMUWriteStart_le_earlySubStart j)
      (by simpa [k] using hg_cont)
  have htail_lbd :
      selectorEarlyWriteIntLower j ≤
        ∫ s in selectorMUEarlyWriteSubStart j..selectorMUWriteHoldTime j,
          k s := by
    simpa [k] using
      selector_early_writeIntegral_lower_sub_lbd_repl sol j hdom hg_cont
  have htail_exp :
      Real.exp (-(∫ s in selectorMUEarlyWriteSubStart j..selectorMUWriteHoldTime j,
          k s)) ≤ Real.exp (-(selectorEarlyWriteIntLower j)) :=
    Real.exp_le_exp.mpr (neg_le_neg htail_lbd)
  exact le_trans (by simpa [k] using hprefix) htail_exp

/-- The early-prefix terminal z-write kernel mass tends to zero. -/
theorem selector_early_write_kernel_prefix_mass_tendsto_zero
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : SelectorReplicatorDynSol d_U B_U UniversalLocalView bgpParams38 selectorSchedule
      branchU
      (fun t => ((1 + Real.cos t) / 2) ^ Mcy)
      (fun t => ((1 + Real.sin t) / 2) ^ Mcy)
      (fun _ => (κ₀ : ℝ))
      (fun t => (g₀ : ℝ) * Real.exp (bgpParams38.cα * t))
      (universalPval eta heta))
    (hdom : ∀ t : ℝ, 0 ≤ t → t ∈ selectorSchedule.domain)
    (hg_cont : Continuous (fun t => bgpParams38.A * sol.α t *
      bGateZ bgpParams38.L (sol.μ t) t)) :
    Tendsto
      (fun j : ℕ =>
        ∫ t in selectorMUWriteStartTime j..selectorMUEarlyWriteSubStart j,
          Real.exp (-(∫ s in t..selectorMUWriteHoldTime j,
            bgpParams38.A * sol.α s * bGateZ bgpParams38.L (sol.μ s) s)) *
            (bgpParams38.A * sol.α t * bGateZ bgpParams38.L (sol.μ t) t))
      atTop (𝓝 0) := by
  have hupper :
      Tendsto (fun j : ℕ => Real.exp (-(selectorEarlyWriteIntLower j)))
        atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp
      (tendsto_neg_atBot_iff.mpr selectorEarlyWriteIntLower_tendsto_atTop)
  refine squeeze_zero' ?_ ?_ hupper
  · filter_upwards [] with j
    apply intervalIntegral.integral_nonneg (selectorMUWriteStart_le_earlySubStart j)
    intro t ht
    have ht0 : 0 ≤ t := le_trans (selectorMUWriteStartTime_nonneg j) ht.1
    exact mul_nonneg (Real.exp_nonneg _)
      (selector_replicator_gateZ_integrand_nonneg sol hdom
        (by norm_num [bgpParams38]) ht0)
  · filter_upwards [] with j
    exact selector_early_write_kernel_prefix_mass_le_exp sol j hdom hg_cont

/-- The settled subwindow integral dominates the explicit lower bound. -/
theorem selector_settled_writeIntegral_lower_lbd_repl
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : SelectorReplicatorDynSol d_U B_U UniversalLocalView bgpParams38 selectorSchedule
      branchU
      (fun t => ((1 + Real.cos t) / 2) ^ Mcy)
      (fun t => ((1 + Real.sin t) / 2) ^ Mcy)
      (fun _ => (κ₀ : ℝ))
      (fun t => (g₀ : ℝ) * Real.exp (bgpParams38.cα * t))
      (universalPval eta heta))
    (j : ℕ)
    (hdom : ∀ t : ℝ, 0 ≤ t → t ∈ selectorSchedule.domain)
    (hg_cont : Continuous (fun t => bgpParams38.A * sol.α t *
      bGateZ bgpParams38.L (sol.μ t) t)) :
    selectorSettledWriteIntLower j
      ≤ ∫ t in selectorMUWriteHoldTime j..selectorMUSettledWriteSubEnd j,
          bgpParams38.A * sol.α t * bGateZ bgpParams38.L (sol.μ t) t := by
  have ha0 : 0 ≤ selectorMUWriteHoldTime j := by
    unfold selectorMUWriteHoldTime
    positivity
  have hab := selectorMUWriteHold_le_settledSubEnd j
  have hα : ∀ t ∈ Icc (selectorMUWriteHoldTime j) (selectorMUSettledWriteSubEnd j),
      sol.α t = Real.exp ((300 : ℝ) * t) := by
    intro t ht
    rw [sol.alpha_eq_exp hdom (le_trans ha0 ht.1)]
    norm_num [bgpParams38]
  have hμ : ∀ t ∈ Icc (selectorMUWriteHoldTime j) (selectorMUSettledWriteSubEnd j),
      sol.μ t = (1000 : ℝ) * t := by
    intro t ht
    rw [sol.mu_eq_linear hdom (le_trans ha0 ht.1), sol.μ_at_zero]
    norm_num [bgpParams38]
  have hsin : ∀ t ∈ Icc (selectorMUWriteHoldTime j) (selectorMUSettledWriteSubEnd j),
      Real.sqrt 2 / 2 ≤ Real.sin t := by
    intro t ht
    exact sin_window_ge_sqrt2 j
      (by
        have hleft : 2 * Real.pi * (j : ℝ) + Real.pi / 4 ≤
            selectorMUWriteHoldTime j := by
          unfold selectorMUWriteHoldTime
          linarith [Real.pi_pos]
        exact le_trans hleft ht.1)
      (by simpa [selectorMUSettledWriteSubEnd] using ht.2)
  have h :=
    write_Z_integral_lower_repl
      (sol := sol) (a := selectorMUWriteHoldTime j)
      (b := selectorMUSettledWriteSubEnd j)
      (cμ := (1000 : ℝ)) (cα := (300 : ℝ)) (A := (1 : ℝ))
      hab ha0 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [bgpParams38]) (by norm_num [bgpParams38])
      hg_cont hα hμ hsin
  have hid :
      (1 : ℝ) * Real.exp ((300 : ℝ) * selectorMUWriteHoldTime j) *
          Real.exp (-((1000 : ℝ) * selectorMUSettledWriteSubEnd j *
            ((1 - Real.sqrt 2 / 2) / 2))) *
          (selectorMUSettledWriteSubEnd j - selectorMUWriteHoldTime j)
        = selectorSettledWriteIntLower j := by
    unfold selectorSettledWriteIntLower selectorMUWriteHoldTime selectorMUSettledWriteSubEnd
    ring
  rwa [hid] at h

/-- Gain-weighted settled z-write mass diverges on
`[selectorMUWriteHoldTime j, selectorMUWriteReadTime j]`. -/
theorem z_write_settled_mass_tendsto_atTop
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : SelectorReplicatorDynSol d_U B_U UniversalLocalView bgpParams38 selectorSchedule
      branchU
      (fun t => ((1 + Real.cos t) / 2) ^ Mcy)
      (fun t => ((1 + Real.sin t) / 2) ^ Mcy)
      (fun _ => (κ₀ : ℝ))
      (fun t => (g₀ : ℝ) * Real.exp (bgpParams38.cα * t))
      (universalPval eta heta))
    (hdom : ∀ t : ℝ, 0 ≤ t → t ∈ selectorSchedule.domain)
    (hg_cont : Continuous (fun t => bgpParams38.A * sol.α t *
      bGateZ bgpParams38.L (sol.μ t) t))
    (hg0 : ∀ t : ℝ, 0 ≤ t →
      0 ≤ bgpParams38.A * sol.α t * bGateZ bgpParams38.L (sol.μ t) t) :
    Tendsto
      (fun j : ℕ =>
        ∫ t in (selectorMUWriteHoldTime j)..(selectorMUWriteReadTime j),
          bgpParams38.A * sol.α t * bGateZ bgpParams38.L (sol.μ t) t)
      atTop atTop := by
  refine tendsto_atTop_mono' atTop ?_ selectorSettledWriteIntLower_tendsto_atTop
  filter_upwards [] with j
  have hsub := selector_settled_writeIntegral_lower_lbd_repl sol j hdom hg_cont
  have hcont_int :
      ∀ a b : ℝ,
        IntervalIntegrable
          (fun t : ℝ => bgpParams38.A * sol.α t *
            bGateZ bgpParams38.L (sol.μ t) t)
          MeasureTheory.volume a b := by
    intro a b
    exact hg_cont.intervalIntegrable a b
  have hadd :
      (∫ t in selectorMUWriteHoldTime j..selectorMUSettledWriteSubEnd j,
          bgpParams38.A * sol.α t * bGateZ bgpParams38.L (sol.μ t) t)
        + (∫ t in selectorMUSettledWriteSubEnd j..selectorMUWriteReadTime j,
          bgpParams38.A * sol.α t * bGateZ bgpParams38.L (sol.μ t) t)
        =
        ∫ t in selectorMUWriteHoldTime j..selectorMUWriteReadTime j,
          bgpParams38.A * sol.α t * bGateZ bgpParams38.L (sol.μ t) t :=
    intervalIntegral.integral_add_adjacent_intervals
      (hcont_int (selectorMUWriteHoldTime j) (selectorMUSettledWriteSubEnd j))
      (hcont_int (selectorMUSettledWriteSubEnd j) (selectorMUWriteReadTime j))
  have htail_nonneg :
      0 ≤ ∫ t in selectorMUSettledWriteSubEnd j..selectorMUWriteReadTime j,
          bgpParams38.A * sol.α t * bGateZ bgpParams38.L (sol.μ t) t := by
    apply intervalIntegral.integral_nonneg (selectorMUSettledSubEnd_le_read j)
    intro t ht
    have ht0 : 0 ≤ t := by
      have hleft : 0 ≤ selectorMUSettledWriteSubEnd j := by
        unfold selectorMUSettledWriteSubEnd
        positivity
      exact le_trans hleft ht.1
    exact hg0 t ht0
  calc
    selectorSettledWriteIntLower j
        ≤ ∫ t in selectorMUWriteHoldTime j..selectorMUSettledWriteSubEnd j,
            bgpParams38.A * sol.α t * bGateZ bgpParams38.L (sol.μ t) t := hsub
    _ ≤ (∫ t in selectorMUWriteHoldTime j..selectorMUSettledWriteSubEnd j,
            bgpParams38.A * sol.α t * bGateZ bgpParams38.L (sol.μ t) t)
          + (∫ t in selectorMUSettledWriteSubEnd j..selectorMUWriteReadTime j,
            bgpParams38.A * sol.α t * bGateZ bgpParams38.L (sol.μ t) t) :=
        le_add_of_nonneg_right htail_nonneg
    _ = ∫ t in selectorMUWriteHoldTime j..selectorMUWriteReadTime j,
          bgpParams38.A * sol.α t * bGateZ bgpParams38.L (sol.μ t) t := hadd

/-! ## Settled z endpoint and δw radius -/

/-- Settled z-write endpoint at `readStart`, using the uniform settled mixture
radius over `[writeStart, readStart]`. -/
theorem z_write_settled_endpoint
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : SelectorReplicatorDynSol d_U B_U UniversalLocalView bgpParams38 selectorSchedule
      branchU
      (fun t => ((1 + Real.cos t) / 2) ^ Mcy)
      (fun t => ((1 + Real.sin t) / 2) ^ Mcy)
      (fun _ => (κ₀ : ℝ))
      (fun t => (g₀ : ℝ) * Real.exp (bgpParams38.cα * t))
      (universalPval eta heta))
    (cfg : ℕ → UConf) (ΛSettled Bz δwSettled : ℕ → ℝ) (j : ℕ) (i : Fin d_U)
    (hdom_write : ∀ t ∈ Icc (selectorMUWriteHoldTime j) (selectorMUWriteReadTime j),
      t ∈ selectorSchedule.domain)
    (hgZ_cont : Continuous fun t : ℝ =>
      bgpParams38.A * sol.α t * bGateZ bgpParams38.L (sol.μ t) t)
    (hgZ0 : ∀ t ∈ Icc (selectorMUWriteHoldTime j) (selectorMUWriteReadTime j),
      0 ≤ bgpParams38.A * sol.α t * bGateZ bgpParams38.L (sol.μ t) t)
    (hmix_settled : ∀ t ∈ Icc (selectorMUWriteHoldTime j) (selectorMUWriteReadTime j),
      |selectorMixTarget branchU sol.u sol.lam t i -
        stackMachineEncodingU.enc (cfg (j + 1)) i| ≤ δwSettled j)
    (hz_start :
      |sol.z (selectorMUWriteHoldTime j) i -
        stackMachineEncodingU.enc (cfg (j + 1)) i| ≤ Bz j)
    (hΛ_lower :
      ΛSettled j ≤ ∫ τ in selectorMUWriteHoldTime j..selectorMUWriteReadTime j,
        bgpParams38.A * sol.α τ * bGateZ bgpParams38.L (sol.μ τ) τ) :
    |sol.z (selectorMUWriteReadTime j) i -
        stackMachineEncodingU.enc (cfg (j + 1)) i|
      ≤ Real.exp (-(ΛSettled j)) * Bz j + δwSettled j := by
  have hzh_zero :
      ∀ t ∈ Icc (selectorMUWriteReadTime j) (selectorMUWriteReadTime j),
        |sol.z t i - sol.z (selectorMUWriteReadTime j) i| ≤ (0 : ℝ) := by
    intro t ht
    have ht_eq : t = selectorMUWriteReadTime j := le_antisymm ht.2 ht.1
    simp [ht_eq]
  have hz_after :=
    z_after_write_bound_repl
      (sol := sol) (s := i)
      (a := selectorMUWriteHoldTime j) (m := selectorMUWriteReadTime j)
      (b := selectorMUWriteReadTime j)
      (M := stackMachineEncodingU.enc (cfg (j + 1)) i)
      (δw := δwSettled j) (δzh := 0)
      (selectorMUWriteHold_le_read j) hdom_write hgZ_cont hgZ0 hmix_settled hzh_zero
  have hz_raw :
      |sol.z (selectorMUWriteReadTime j) i -
          stackMachineEncodingU.enc (cfg (j + 1)) i|
        ≤ 0 + (Real.exp (-(∫ τ in selectorMUWriteHoldTime j..selectorMUWriteReadTime j,
            bgpParams38.A * sol.α τ * bGateZ bgpParams38.L (sol.μ τ) τ)) *
            |sol.z (selectorMUWriteHoldTime j) i -
              stackMachineEncodingU.enc (cfg (j + 1)) i| + δwSettled j) :=
    hz_after (selectorMUWriteReadTime j) ⟨le_rfl, le_rfl⟩
  have hctr :
      Real.exp (-(∫ τ in selectorMUWriteHoldTime j..selectorMUWriteReadTime j,
          bgpParams38.A * sol.α τ * bGateZ bgpParams38.L (sol.μ τ) τ)) *
          |sol.z (selectorMUWriteHoldTime j) i -
            stackMachineEncodingU.enc (cfg (j + 1)) i|
        ≤ Real.exp (-(ΛSettled j)) * Bz j :=
    exp_neg_mul_abs_le_exp_neg_lbd_mul hΛ_lower hz_start
  linarith

/-- Settled mixture radius: branch-spread concentration plus the carried
u-tube and the discharged settled u-drift. -/
def δwSettled (Rspread mult : ℝ) (epsLamSettled ρu δu : ℕ → ℝ) (j : ℕ) : ℝ :=
  Rspread * epsLamSettled j + mult * (ρu j + δu j)

theorem δw_settled_tendsto_zero
    {Rspread mult : ℝ} {epsLamSettled ρu δu : ℕ → ℝ}
    (hepsLam : Tendsto epsLamSettled atTop (𝓝 0))
    (hρu : Tendsto ρu atTop (𝓝 0))
    (hδu : Tendsto δu atTop (𝓝 0)) :
    Tendsto (δwSettled Rspread mult epsLamSettled ρu δu) atTop (𝓝 0) := by
  simpa [δwSettled] using
    (Filter.Tendsto.const_mul Rspread hepsLam).add
      (Filter.Tendsto.const_mul mult (hρu.add hδu))

/-- Propagate all-coordinate `z-u` from the settled read endpoint to the next
true write-start.  The only remaining analytic input is the weighted
inter-read z-source integral. -/
theorem selector_replicator_writeStart_zu_of_read_zu_and_interRead_source
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀)
    (w j : ℕ) {Bread Bsrc : ℝ}
    (hread : ∀ i : Fin d_U,
      |(sol w).z (selectorMUWriteReadTime j) i -
        (sol w).u (selectorMUWriteReadTime j) i| ≤ Bread)
    (hsource : ∀ i : Fin d_U,
      (∫ τ in (selectorMUWriteReadTime j)..(selectorMUWriteStartTime (j + 1)),
        Real.exp (-(∫ s in τ..(selectorMUWriteStartTime (j + 1)),
          bgpParams38.A * (sol w).α s *
            bGateU bgpParams38.L ((sol w).μ s) s)) *
        |bgpParams38.A * (sol w).α τ *
          bGateZ bgpParams38.L ((sol w).μ τ) τ *
          (selectorMixTarget branchU (sol w).u (sol w).lam τ i -
            (sol w).z τ i)|) ≤ Bsrc) :
    ∀ i : Fin d_U,
      |(sol w).z (selectorMUWriteStartTime (j + 1)) i -
        (sol w).u (selectorMUWriteStartTime (j + 1)) i| ≤
        Real.exp (-(∫ s in (selectorMUWriteReadTime j)..
          (selectorMUWriteStartTime (j + 1)),
            bgpParams38.A * (sol w).α s *
              bGateU bgpParams38.L ((sol w).μ s) s)) * Bread + Bsrc := by
  intro i
  let a : ℝ := selectorMUWriteReadTime j
  let b : ℝ := selectorMUWriteStartTime (j + 1)
  let kU : ℝ → ℝ := fun t =>
    bgpParams38.A * (sol w).α t * bGateU bgpParams38.L ((sol w).μ t) t
  let src : ℝ → ℝ := fun t =>
    bgpParams38.A * (sol w).α t *
      bGateZ bgpParams38.L ((sol w).μ t) t *
      (selectorMixTarget branchU (sol w).u (sol w).lam t i - (sol w).z t i)
  let e : ℝ → ℝ := fun t => (sol w).z t i - (sol w).u t i
  have hab : a ≤ b := by
    dsimp [a, b]
    unfold selectorMUWriteReadTime selectorMUWriteStartTime
    push_cast
    linarith [Real.pi_pos]
  have hk_cont : Continuous kU := by
    have hq : Continuous fun t : ℝ => qPulse bgpParams38.L t := by
      simp only [qPulse]
      exact ((continuous_const.add Real.continuous_sin).div_const 2).pow
        bgpParams38.L
    have hgateU : Continuous fun t : ℝ =>
        bGateU bgpParams38.L ((sol w).μ t) t := by
      simp only [bGateU]
      exact Real.continuous_exp.comp ((((sol w).cont_μ).mul hq).neg)
    simpa [kU, mul_assoc] using
      ((continuous_const.mul ((sol w).cont_α)).mul hgateU)
  have hsrc_cont : Continuous src := by
    have hr : Continuous fun t : ℝ => rPulse bgpParams38.L t := by
      simp only [rPulse]
      exact ((continuous_const.sub Real.continuous_sin).div_const 2).pow
        bgpParams38.L
    have hgateZ : Continuous fun t : ℝ =>
        bGateZ bgpParams38.L ((sol w).μ t) t := by
      simp only [bGateZ]
      exact Real.continuous_exp.comp ((((sol w).cont_μ).mul hr).neg)
    have hAα : Continuous fun t : ℝ => bgpParams38.A * (sol w).α t :=
      continuous_const.mul ((sol w).cont_α)
    have hdiff : Continuous fun t : ℝ =>
        selectorMixTarget branchU (sol w).u (sol w).lam t i -
          (sol w).z t i :=
      ((sol w).cont_mixTarget i).sub ((sol w).cont_z i)
    dsimp [src]
    exact (hAα.mul hgateZ).mul hdiff
  have he_deriv : ∀ t ∈ Set.Icc a b,
      HasDerivAt e (-(kU t) * e t + src t) t := by
    intro t ht
    have ha0 : 0 ≤ a := by
      dsimp [a]
      unfold selectorMUWriteReadTime
      positivity
    have ht0 : 0 ≤ t := le_trans ha0 ht.1
    have hdom : t ∈ selectorSchedule.domain :=
      selectorSchedule_domain_of_nonneg_structural t ht0
    have hz := (sol w).z_hasDeriv t hdom i
    have hu := (sol w).u_hasDeriv t hdom i
    have hsub := hz.sub hu
    convert hsub using 1
    simp only [e, kU, src]
    ring
  have hbase :=
    abs_inhomogeneous_decay_bound e src kU
      (a := a) (b := b) (E0 := Bread) (S := Bsrc)
      hab hk_cont hsrc_cont he_deriv
      (by simpa [e, a] using hread i)
      (by simpa [src, kU, a, b] using hsource i)
  simpa [e, kU, a, b] using hbase

#print axioms selectorUSettledRate
#print axioms δuSettled
#print axioms selectorUSettledRate_pos
#print axioms δuSettled_tendsto_zero
#print axioms δuSettled_nonneg
#print axioms δuSettled_tendsto_zero_of_eventually_bounded
#print axioms δuSettled_tendsto_zero_of_uniform_bound
#print axioms gateU_integrand_le_settled_exp_repl
#print axioms gateU_integral_le_settled_exp_repl
#print axioms u_drift_on_settled_window
#print axioms selectorMUSettledWriteSubEnd
#print axioms selectorSettledWriteIntLower
#print axioms selectorMUEarlyWriteSubStart
#print axioms selectorEarlyWriteIntLower
#print axioms selectorMUWriteHold_le_settledSubEnd
#print axioms selectorMUWriteStart_le_earlySubStart
#print axioms selectorMUEarlySubStart_le_writeHold
#print axioms selectorMUSettledSubEnd_le_read
#print axioms selectorSettledWriteIntLower_tendsto_atTop
#print axioms selectorEarlyWriteIntLower_tendsto_atTop
#print axioms write_Z_integral_lower_repl
#print axioms selector_early_writeIntegral_lower_lbd_repl
#print axioms selector_settled_writeIntegral_lower_lbd_repl
#print axioms z_write_settled_mass_tendsto_atTop
#print axioms z_write_settled_endpoint
#print axioms δwSettled
#print axioms δw_settled_tendsto_zero

end Ripple.BoundedUniversality.BGP
