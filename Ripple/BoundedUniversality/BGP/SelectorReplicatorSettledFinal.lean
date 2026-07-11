import Ripple.BoundedUniversality.BGP.SelectorReplicatorFinal
import Ripple.BoundedUniversality.BGP.SelectorReplicatorSelfHold
import Ripple.BoundedUniversality.BGP.FlagHmixConstant
import Ripple.BoundedUniversality.BGP.BGPParams38

/-!
Ripple.BoundedUniversality.BGP.SelectorReplicatorSettledFinal
------------------------------------------
Integration layer for the settled-window replicator headline.

This file wires the batch-1/2/3 settled facts into the F8
`*_hold_repl_of_tendsto` endpoints.  The carried residual is the satisfiable
settled concentration/tube bundle and the local ODE/gate realization facts; no
uniform full-tile mix stability hypothesis is carried.
-/

noncomputable section

namespace Ripple.BoundedUniversality.BGP

open Set MachineInstance
open Filter
open scoped BigOperators Topology

/-- Settled loser-mass radius attached to a concentration-input bundle. -/
def solMUReplSettledEpsLam
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    {cfg : ℕ → ℕ → UConf}
    (inputs : SelectorReplicatorConcInputs sol cfg) (w j : ℕ) : ℝ :=
  epsLamSettled (V := UniversalLocalView)
    (inputs.Lmin w j) (inputs.gap w j) (inputs.R0 w j) (inputs.Kreset w j)
    (sol w).G (selectorMUWriteStartTime j) (selectorMUWriteHoldTime j)

/-- Halt-coordinate concentration inputs.

This is the subset of `SelectorReplicatorConcInputs` needed to bound the
loser λ-mass at the halt coordinate.  It intentionally omits branch-spread
data, since the halt branch target is controlled by a separate
coordinate-specific lemma. -/
structure SelectorReplicatorHaltConcInputs
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀)
    (cfg : ℕ → ℕ → UConf) where
  Lmin : ℕ → ℕ → ℝ
  gap : ℕ → ℕ → ℝ
  R0 : ℕ → ℕ → ℝ
  Kreset : ℕ → ℕ → ℝ
  hLmin_pos : ∀ w j, 0 < Lmin w j
  hqL : ∀ w j, ∀ t ∈ Icc (selectorMUWriteStartTime j) (selectorMUWriteReadTime j),
    Lmin w j ≤ (sol w).lam (localViewU (cfg w j)) t
  hgap : ∀ w j, ∀ v : UniversalLocalView, v ≠ localViewU (cfg w j) →
    ∀ t ∈ Ico (selectorMUWriteStartTime j) (selectorMUWriteReadTime j),
      universalPval eta heta v ((sol w).u t)
        - universalPval eta heta (localViewU (cfg w j)) ((sol w).u t) ≤
          -gap w j
  hRa : ∀ w j, ∀ v : UniversalLocalView, v ≠ localViewU (cfg w j) →
    (sol w).lam v (selectorMUWriteStartTime j) /
        (sol w).lam (localViewU (cfg w j)) (selectorMUWriteStartTime j) ≤
      R0 w j
  hKreset : ∀ w j,
    (∫ t in (selectorMUWriteStartTime j)..(selectorMUWriteHoldTime j),
      Real.exp (gap w j * ((sol w).G t - (sol w).G (selectorMUWriteStartTime j))) *
        (((1 + Real.cos t) / 2) ^ Mcy * (κ₀ : ℝ))) ≤ Kreset w j

/-- Settled loser-mass radius attached to a halt-only input bundle. -/
def solMUReplSettledHaltEpsLam
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    {cfg : ℕ → ℕ → UConf}
    (inputs : SelectorReplicatorHaltConcInputs sol cfg) (w j : ℕ) : ℝ :=
  epsLamSettled (V := UniversalLocalView)
    (inputs.Lmin w j) (inputs.gap w j) (inputs.R0 w j) (inputs.Kreset w j)
    (sol w).G (selectorMUWriteStartTime j) (selectorMUWriteHoldTime j)

/-- Prefix reset integral for the halt-only concentration bundle. -/
def solMUReplHaltPreForwardResetIntegral
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    {cfg : ℕ → ℕ → UConf}
    (inputs : SelectorReplicatorHaltConcInputs sol cfg) (w j : ℕ) : ℝ :=
  ∫ t in (selectorMUWriteStartTime j)..(selectorMUWriteHoldTime j),
    Real.exp (inputs.gap w j *
      ((sol w).G t - (sol w).G (selectorMUWriteStartTime j))) *
      (((1 + Real.cos t) / 2) ^ Mcy * (κ₀ : ℝ))

/-- Settled write radius used by F8. -/
def solMUReplSettledRho (Λ Bz δw : ℕ → ℝ) (j : ℕ) : ℝ :=
  Real.exp (-(Λ j)) * Bz j + δw j

/-- Halt-coordinate settled mixture radius.  Unlike `δwSettled`, this carries
no u-tube term because the halt branch target is independent of `u`. -/
def solMUReplSettledHaltDelta
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    {cfg : ℕ → ℕ → UConf}
    (inputs : SelectorReplicatorHaltConcInputs sol cfg) (w j : ℕ) : ℝ :=
  (Fintype.card UniversalLocalView : ℝ) * solMUReplSettledHaltEpsLam inputs w j

/-- Finite-prefix patch for the hold radius.  It is eventually equal to the
batch-3 self-hold radius, so the limit is unchanged. -/
def solMUReplSettledHoldRadius
    (N : ℕ) (δnext ρ holdPrefix : ℕ → ℝ) (j : ℕ) : ℝ :=
  if N ≤ j then selectorMUSelfHoldDelta δnext ρ j else holdPrefix j

/-- Batch-1 asymptotic discharge for the settled loser-mass radius. -/
theorem solMURepl_settled_epsLam_tendsto_zero
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    {cfg : ℕ → ℕ → UConf}
    (inputs : SelectorReplicatorConcInputs sol cfg) (w : ℕ)
    (hg₀ : 0 < (g₀ : ℝ))
    {gap0 Lmin0 R0max Cratio : ℝ}
    (hgap0 : 0 < gap0)
    (hgap_lb : ∀ᶠ j in atTop, gap0 ≤ inputs.gap w j)
    (hLmin0_pos : 0 < Lmin0)
    (hLmin_lb : ∀ᶠ j in atTop, Lmin0 ≤ inputs.Lmin w j)
    (hR0_nonneg : ∀ᶠ j in atTop, 0 ≤ inputs.R0 w j)
    (hR0_bound : ∀ᶠ j in atTop, inputs.R0 w j ≤ R0max)
    (hKreset_eq :
      ∀ j, inputs.Kreset w j = solMUReplPreForwardResetIntegral inputs w j)
    (hκ₀_nonneg : 0 ≤ (κ₀ : ℝ))
    (hCratio_nonneg : 0 ≤ Cratio)
    (hratio_bound : ∀ j, ∀ t ∈
      Icc (selectorMUWriteStartTime j) (selectorMUWriteHoldTime j),
        (((1 + Real.cos t) / 2) ^ Mcy * (κ₀ : ℝ)) ≤
          (Cratio * Real.exp (-(bgpParams38.cα * selectorMUWriteStartTime j))) *
            (((1 + Real.sin t) / 2) ^ Mcy *
              ((g₀ : ℝ) * Real.exp (bgpParams38.cα * t)))) :
    Tendsto (fun j => solMUReplSettledEpsLam inputs w j) atTop (𝓝 0) := by
  simpa [solMUReplSettledEpsLam] using
    solMURepl_epsLamSettled_pre_tendsto_zero_duhamel
      (inputs := inputs) (w := w) hg₀
      (Kreset := fun j => inputs.Kreset w j)
      hgap0 hgap_lb hLmin0_pos hLmin_lb hR0_nonneg hR0_bound
      hKreset_eq hκ₀_nonneg hCratio_nonneg hratio_bound

/-- Halt-only prefix-integral Duhamel residual.

This is the same schedule proof as
`solMURepl_preForwardResetIntegral_duhamel_tendsto_zero`, specialized to the
skinny halt concentration input. -/
theorem solMURepl_haltPreForwardResetIntegral_duhamel_tendsto_zero
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    {cfg : ℕ → ℕ → UConf}
    (inputs : SelectorReplicatorHaltConcInputs sol cfg) (w : ℕ)
    {gap0 Cratio : ℝ}
    (hgap0 : 0 < gap0)
    (hgap_lb : ∀ᶠ j in atTop, gap0 ≤ inputs.gap w j)
    (hκ₀_nonneg : 0 ≤ (κ₀ : ℝ))
    (hCratio_nonneg : 0 ≤ Cratio)
    (hratio_bound : ∀ j, ∀ t ∈
      Icc (selectorMUWriteStartTime j) (selectorMUWriteHoldTime j),
        (((1 + Real.cos t) / 2) ^ Mcy * (κ₀ : ℝ)) ≤
          (Cratio * Real.exp (-(bgpParams38.cα * selectorMUWriteStartTime j))) *
            (((1 + Real.sin t) / 2) ^ Mcy *
              ((g₀ : ℝ) * Real.exp (bgpParams38.cα * t)))) :
    Tendsto
      (fun j =>
        solMUReplHaltPreForwardResetIntegral inputs w j *
          Real.exp
            (-(inputs.gap w j *
              ((sol w).G (selectorMUWriteHoldTime j)
                - (sol w).G (selectorMUWriteStartTime j)))))
      atTop (𝓝 0) := by
  have hcα : 0 < bgpParams38.cα := by norm_num [bgpParams38]
  have hstart_atTop :
      Tendsto (fun j : ℕ => selectorMUWriteStartTime j) atTop atTop := by
    have hlin : Tendsto (fun j : ℕ => (2 * Real.pi) * (j : ℝ)) atTop atTop :=
      Filter.Tendsto.const_mul_atTop (by positivity : (0 : ℝ) < 2 * Real.pi)
        tendsto_natCast_atTop_atTop
    have hadd :
        Tendsto (fun j : ℕ => (2 * Real.pi) * (j : ℝ) + Real.pi / 6) atTop atTop := by
      exact Filter.tendsto_atTop_add_const_right atTop (Real.pi / 6) hlin
    simpa [selectorMUWriteStartTime, mul_assoc] using hadd
  have hscaled :
      Tendsto (fun j : ℕ => bgpParams38.cα * selectorMUWriteStartTime j) atTop atTop :=
    hstart_atTop.const_mul_atTop hcα
  have hdecay :
      Tendsto (fun j : ℕ =>
        Real.exp (-(bgpParams38.cα * selectorMUWriteStartTime j))) atTop (𝓝 0) := by
    have hneg :
        Tendsto (fun j : ℕ => -(bgpParams38.cα * selectorMUWriteStartTime j))
          atTop atBot :=
      Filter.tendsto_neg_atBot_iff.mpr hscaled
    exact Real.tendsto_exp_atBot.comp hneg
  have hupper :
      Tendsto (fun j : ℕ =>
        (Cratio / gap0) *
          Real.exp (-(bgpParams38.cα * selectorMUWriteStartTime j))) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hdecay
  refine squeeze_zero' ?_ ?_ hupper
  · filter_upwards [hgap_lb] with j hgapj
    have hgap_pos : 0 < inputs.gap w j := lt_of_lt_of_le hgap0 hgapj
    have hCj_nonneg :
        0 ≤ Cratio * Real.exp (-(bgpParams38.cα * selectorMUWriteStartTime j)) :=
      mul_nonneg hCratio_nonneg (Real.exp_pos _).le
    have hreset_nonneg :
        ∀ t ∈ Icc (selectorMUWriteStartTime j) (selectorMUWriteHoldTime j),
          0 ≤ (((1 + Real.cos t) / 2) ^ Mcy * (κ₀ : ℝ)) := by
      intro t _ht
      have hcos : 0 ≤ (1 + Real.cos t) / 2 := by
        nlinarith [Real.neg_one_le_cos t]
      exact mul_nonneg (pow_nonneg hcos Mcy) hκ₀_nonneg
    have hbound := forward_reset_integral_mul_decay_le
      (a := selectorMUWriteStartTime j)
      (b := selectorMUWriteHoldTime j)
      (gap := inputs.gap w j)
      (C := Cratio * Real.exp (-(bgpParams38.cα * selectorMUWriteStartTime j)))
      (G := (sol w).G)
      (cg := fun t =>
        ((1 + Real.sin t) / 2) ^ Mcy *
          ((g₀ : ℝ) * Real.exp (bgpParams38.cα * t)))
      (reset := fun t => ((1 + Real.cos t) / 2) ^ Mcy * (κ₀ : ℝ))
      (selectorMUWriteStart_le_hold j) hgap_pos hCj_nonneg
      (sol w).cont_G
      (fun t ht => (sol w).G_hasDeriv t (selectorMU_hdom_writeHold w j t ht))
      (by fun_prop) (by fun_prop) hreset_nonneg
      (fun t ht => by simpa [mul_assoc] using hratio_bound j t ht)
    simpa [solMUReplHaltPreForwardResetIntegral] using hbound.1
  · filter_upwards [hgap_lb] with j hgapj
    have hgap_pos : 0 < inputs.gap w j := lt_of_lt_of_le hgap0 hgapj
    have hCj_nonneg :
        0 ≤ Cratio * Real.exp (-(bgpParams38.cα * selectorMUWriteStartTime j)) :=
      mul_nonneg hCratio_nonneg (Real.exp_pos _).le
    have hreset_nonneg :
        ∀ t ∈ Icc (selectorMUWriteStartTime j) (selectorMUWriteHoldTime j),
          0 ≤ (((1 + Real.cos t) / 2) ^ Mcy * (κ₀ : ℝ)) := by
      intro t _ht
      have hcos : 0 ≤ (1 + Real.cos t) / 2 := by
        nlinarith [Real.neg_one_le_cos t]
      exact mul_nonneg (pow_nonneg hcos Mcy) hκ₀_nonneg
    have hbound := forward_reset_integral_mul_decay_le
      (a := selectorMUWriteStartTime j)
      (b := selectorMUWriteHoldTime j)
      (gap := inputs.gap w j)
      (C := Cratio * Real.exp (-(bgpParams38.cα * selectorMUWriteStartTime j)))
      (G := (sol w).G)
      (cg := fun t =>
        ((1 + Real.sin t) / 2) ^ Mcy *
          ((g₀ : ℝ) * Real.exp (bgpParams38.cα * t)))
      (reset := fun t => ((1 + Real.cos t) / 2) ^ Mcy * (κ₀ : ℝ))
      (selectorMUWriteStart_le_hold j) hgap_pos hCj_nonneg
      (sol w).cont_G
      (fun t ht => (sol w).G_hasDeriv t (selectorMU_hdom_writeHold w j t ht))
      (by fun_prop) (by fun_prop) hreset_nonneg
      (fun t ht => by simpa [mul_assoc] using hratio_bound j t ht)
    have hle_gap :
        (Cratio * Real.exp (-(bgpParams38.cα * selectorMUWriteStartTime j))) /
            inputs.gap w j ≤
          (Cratio * Real.exp (-(bgpParams38.cα * selectorMUWriteStartTime j))) / gap0 := by
      have hinv : 1 / inputs.gap w j ≤ 1 / gap0 :=
        one_div_le_one_div_of_le hgap0 hgapj
      have hmul := mul_le_mul_of_nonneg_left hinv hCj_nonneg
      simpa [div_eq_mul_inv, one_div, mul_assoc] using hmul
    have hrewrite :
        (Cratio * Real.exp (-(bgpParams38.cα * selectorMUWriteStartTime j))) / gap0 =
          (Cratio / gap0) *
            Real.exp (-(bgpParams38.cα * selectorMUWriteStartTime j)) := by
      field_simp [hgap0.ne']
    calc
      solMUReplHaltPreForwardResetIntegral inputs w j *
          Real.exp
            (-(inputs.gap w j *
              ((sol w).G (selectorMUWriteHoldTime j)
                - (sol w).G (selectorMUWriteStartTime j))))
          ≤
            (Cratio * Real.exp (-(bgpParams38.cα * selectorMUWriteStartTime j))) /
              inputs.gap w j := by
              simpa [solMUReplHaltPreForwardResetIntegral] using hbound.2
      _ ≤
            (Cratio * Real.exp (-(bgpParams38.cα * selectorMUWriteStartTime j))) /
              gap0 := hle_gap
      _ =
            (Cratio / gap0) *
              Real.exp (-(bgpParams38.cα * selectorMUWriteStartTime j)) := hrewrite

/-- Duhamel discharge for a halt-only carried prefix `Kreset`. -/
theorem solMURepl_haltPreKreset_duhamel_tendsto_zero
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    {cfg : ℕ → ℕ → UConf}
    (inputs : SelectorReplicatorHaltConcInputs sol cfg) (w : ℕ)
    {Kreset : ℕ → ℝ} {gap0 Cratio : ℝ}
    (hgap0 : 0 < gap0)
    (hgap_lb : ∀ᶠ j in atTop, gap0 ≤ inputs.gap w j)
    (hKreset_eq : ∀ j, Kreset j = solMUReplHaltPreForwardResetIntegral inputs w j)
    (hκ₀_nonneg : 0 ≤ (κ₀ : ℝ))
    (hCratio_nonneg : 0 ≤ Cratio)
    (hratio_bound : ∀ j, ∀ t ∈
      Icc (selectorMUWriteStartTime j) (selectorMUWriteHoldTime j),
        (((1 + Real.cos t) / 2) ^ Mcy * (κ₀ : ℝ)) ≤
          (Cratio * Real.exp (-(bgpParams38.cα * selectorMUWriteStartTime j))) *
            (((1 + Real.sin t) / 2) ^ Mcy *
              ((g₀ : ℝ) * Real.exp (bgpParams38.cα * t)))) :
    Tendsto
      (fun j =>
        Kreset j *
          Real.exp
            (-(inputs.gap w j *
              ((sol w).G (selectorMUWriteHoldTime j)
                - (sol w).G (selectorMUWriteStartTime j)))))
      atTop (𝓝 0) := by
  have hstandalone :=
    solMURepl_haltPreForwardResetIntegral_duhamel_tendsto_zero
      (inputs := inputs) (w := w) hgap0 hgap_lb hκ₀_nonneg
      hCratio_nonneg hratio_bound
  refine hstandalone.congr' ?_
  filter_upwards [] with j
  simp [hKreset_eq j]

/-- Batch-1 asymptotic discharge for the halt-only settled loser-mass radius. -/
theorem solMURepl_settled_haltEpsLam_tendsto_zero
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    {cfg : ℕ → ℕ → UConf}
    (inputs : SelectorReplicatorHaltConcInputs sol cfg) (w : ℕ)
    (hg₀ : 0 < (g₀ : ℝ))
    {gap0 Lmin0 R0max Cratio : ℝ}
    (hgap0 : 0 < gap0)
    (hgap_lb : ∀ᶠ j in atTop, gap0 ≤ inputs.gap w j)
    (hLmin0_pos : 0 < Lmin0)
    (hLmin_lb : ∀ᶠ j in atTop, Lmin0 ≤ inputs.Lmin w j)
    (hR0_nonneg : ∀ᶠ j in atTop, 0 ≤ inputs.R0 w j)
    (hR0_bound : ∀ᶠ j in atTop, inputs.R0 w j ≤ R0max)
    (hKreset_eq :
      ∀ j, inputs.Kreset w j = solMUReplHaltPreForwardResetIntegral inputs w j)
    (hκ₀_nonneg : 0 ≤ (κ₀ : ℝ))
    (hCratio_nonneg : 0 ≤ Cratio)
    (hratio_bound : ∀ j, ∀ t ∈
      Icc (selectorMUWriteStartTime j) (selectorMUWriteHoldTime j),
        (((1 + Real.cos t) / 2) ^ Mcy * (κ₀ : ℝ)) ≤
          (Cratio * Real.exp (-(bgpParams38.cα * selectorMUWriteStartTime j))) *
            (((1 + Real.sin t) / 2) ^ Mcy *
              ((g₀ : ℝ) * Real.exp (bgpParams38.cα * t)))) :
    Tendsto (fun j => solMUReplSettledHaltEpsLam inputs w j) atTop (𝓝 0) := by
  haveI : Nonempty UniversalLocalView := ⟨defaultLocalViewU⟩
  have hDuhamel_pre :
      Tendsto
        (fun j =>
          inputs.Kreset w j *
            Real.exp
              (-inputs.gap w j *
                ((sol w).G (selectorMUWriteHoldTime j)
                  - (sol w).G (selectorMUWriteStartTime j))))
        atTop (𝓝 0) := by
    simpa [neg_mul] using
      solMURepl_haltPreKreset_duhamel_tendsto_zero
        (inputs := inputs) (w := w) hgap0 hgap_lb hKreset_eq
        hκ₀_nonneg hCratio_nonneg hratio_bound
  have hcore :=
    epsLamSettled_tendsto_zero_duhamel (V := UniversalLocalView)
      (Lmin := fun j => inputs.Lmin w j)
      (gap := fun j => inputs.gap w j)
      (R0 := fun j => inputs.R0 w j)
      (Kreset := fun j => inputs.Kreset w j)
      (deltaG := fun j =>
        (sol w).G (selectorMUWriteHoldTime j)
          - (sol w).G (selectorMUWriteStartTime j))
      hgap0 hgap_lb (solMURepl_deltaG_pre_tendsto_atTop sol hg₀ w)
      hLmin0_pos hLmin_lb hR0_nonneg hR0_bound hDuhamel_pre
  simpa [solMUReplSettledHaltEpsLam, epsLamSettled, selectorSettledRatioEps]
    using hcore

/-- The settled endpoint start fact and its F8 radius limit. -/
theorem solMURepl_settled_hstart
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    {cfg : ℕ → ℕ → UConf}
    (inputs : SelectorReplicatorConcInputs sol cfg) (w : ℕ)
    (Λ Bz ρu : ℕ → ℝ) {Rspread mult Bzu Bzmax : ℝ}
    (hdom_nonneg : ∀ t : ℝ, 0 ≤ t → t ∈ selectorSchedule.domain)
    (hdom_write : ∀ j, ∀ t ∈ Icc (selectorMUWriteHoldTime j)
        (selectorMUWriteReadTime j), t ∈ selectorSchedule.domain)
    (hgZ_cont : Continuous fun t : ℝ =>
      bgpParams38.A * (sol w).α t * bGateZ bgpParams38.L ((sol w).μ t) t)
    (hgZ0 : ∀ j, ∀ t ∈ Icc (selectorMUWriteHoldTime j)
        (selectorMUWriteReadTime j),
      0 ≤ bgpParams38.A * (sol w).α t * bGateZ bgpParams38.L ((sol w).μ t) t)
    (hcfg_step : ∀ j, M_U.step (cfg w j) = cfg w (j + 1))
    (hmult0 : 0 ≤ mult)
    (hmultbound : ∀ j, ∀ i,
      stackMachineEncodingU.coordMultiplier (cfg w j) i ≤ mult)
    (hsum : ∀ j, ∀ t ∈ Icc (selectorMUWriteHoldTime j)
        (selectorMUWriteReadTime j),
      (∑ v : UniversalLocalView, (sol w).lam v t) = 1)
    (hlam_nonneg : ∀ j, ∀ t ∈ Icc (selectorMUWriteHoldTime j)
        (selectorMUWriteReadTime j), ∀ v : UniversalLocalView,
      0 ≤ (sol w).lam v t)
    (hloser : ∀ j, ∀ t ∈ Icc (selectorMUWriteHoldTime j)
        (selectorMUWriteReadTime j),
      (Finset.univ.filter (fun v : UniversalLocalView =>
        v ≠ localViewU (cfg w j))).sum (fun v => (sol w).lam v t) ≤
          solMUReplSettledEpsLam inputs w j)
    (hRspread_nonneg : 0 ≤ Rspread)
    (hspread : ∀ j, ∀ t ∈ Icc (selectorMUWriteHoldTime j)
        (selectorMUWriteReadTime j), ∀ i, ∀ v : UniversalLocalView,
      v ≠ localViewU (cfg w j) →
        |BranchData.evalBranch (branchU v) ((sol w).u t) i
          - BranchData.evalBranch (branchU (localViewU (cfg w j)))
              ((sol w).u t) i| ≤ Rspread)
    (hutube_write : ∀ j, ∀ i,
      |(sol w).u (selectorMUWriteHoldTime j) i -
        stackMachineEncodingU.enc (cfg w j) i| ≤ ρu j)
    (hBzu0 : 0 ≤ Bzu)
    (hzu : ∀ j, ∀ t ∈ Icc (selectorMUWriteHoldTime j)
        (selectorMUWriteReadTime j), ∀ i,
      |(sol w).z t i - (sol w).u t i| ≤ Bzu)
    (hz_start : ∀ j,
      |(sol w).z (selectorMUWriteHoldTime j) haltCoordU -
        stackMachineEncodingU.enc (cfg w (j + 1)) haltCoordU| ≤ Bz j)
    (hΛ_lower : ∀ j,
      Λ j ≤ ∫ τ in selectorMUWriteHoldTime j..selectorMUWriteReadTime j,
        bgpParams38.A * (sol w).α τ * bGateZ bgpParams38.L ((sol w).μ τ) τ)
    (hΛ : Tendsto Λ atTop atTop)
    (hBz_nonneg : ∀ j, 0 ≤ Bz j)
    (hBz_bdd : ∀ᶠ j in atTop, Bz j ≤ Bzmax)
    (hepsLam : Tendsto (fun j => solMUReplSettledEpsLam inputs w j) atTop (𝓝 0))
    (hρu : Tendsto ρu atTop (𝓝 0))
    (hδw_nonneg : ∀ j,
      0 ≤ δwSettled Rspread mult (fun j => solMUReplSettledEpsLam inputs w j)
        ρu (δuSettled Bzu) j) :
    (∀ (j : ℕ),
      |(sol w).z (2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6) haltCoordU -
        stackMachineEncodingU.enc (cfg w (j + 1)) haltCoordU| ≤
          solMUReplSettledRho Λ Bz
            (δwSettled Rspread mult (fun j => solMUReplSettledEpsLam inputs w j)
              ρu (δuSettled Bzu)) j) ∧
    Tendsto
      (solMUReplSettledRho Λ Bz
        (δwSettled Rspread mult (fun j => solMUReplSettledEpsLam inputs w j)
          ρu (δuSettled Bzu))) atTop (𝓝 0) ∧
    (∀ j, 0 ≤
      solMUReplSettledRho Λ Bz
        (δwSettled Rspread mult (fun j => solMUReplSettledEpsLam inputs w j)
          ρu (δuSettled Bzu)) j) := by
  have hδu : Tendsto (δuSettled Bzu) atTop (𝓝 0) :=
    δuSettled_tendsto_zero Bzu
  have hδw :
      Tendsto
        (δwSettled Rspread mult (fun j => solMUReplSettledEpsLam inputs w j)
          ρu (δuSettled Bzu)) atTop (𝓝 0) :=
    δw_settled_tendsto_zero hepsLam hρu hδu
  have hctr :
      Tendsto (fun j : ℕ => selectorZWriteContraction Λ Bz j) atTop (𝓝 0) := by
    simpa using
      solMURepl_expNegLambda_Bz0_tendsto_zero (Λ := fun _ : ℕ => Λ)
        (Bz0 := fun _ : ℕ => Bz) (w := 0) hΛ
        (Filter.Eventually.of_forall hBz_nonneg) hBz_bdd
  refine ⟨?_, ?_, ?_⟩
  · intro j
    have hudrift_all : ∀ j', ∀ t ∈ Icc (selectorMUWriteHoldTime j')
        (selectorMUWriteReadTime j'), ∀ i,
        |(sol w).u t i - (sol w).u (selectorMUWriteHoldTime j') i| ≤
          δuSettled Bzu j' := by
      intro j' t ht i
      exact u_drift_on_settled_window (sol w) j' i hBzu0 hdom_nonneg
        (fun s hs => hzu j' s hs i) t ht
    have hmix_raw :=
      mixTarget_near_next_on_settled_window (sol w) (cfg w)
        selectorMUWriteHoldTime selectorMUWriteReadTime
        (fun j => solMUReplSettledEpsLam inputs w j)
        (fun _ => Rspread) ρu (δuSettled Bzu)
        hmult0 hmultbound hsum hlam_nonneg hloser
        (fun _ => hRspread_nonneg) hspread hutube_write
        hudrift_all j
    have hmix : ∀ t ∈ Icc (selectorMUWriteHoldTime j)
        (selectorMUWriteReadTime j),
        |selectorMixTarget branchU (sol w).u (sol w).lam t haltCoordU -
          stackMachineEncodingU.enc (cfg w (j + 1)) haltCoordU| ≤
            δwSettled Rspread mult
              (fun j => solMUReplSettledEpsLam inputs w j) ρu (δuSettled Bzu) j := by
      intro t ht
      simpa [δwSettled, hcfg_step j] using hmix_raw t ht haltCoordU
    have hendpoint :=
      z_write_settled_endpoint (sol w) (cfg w) Λ Bz
        (δwSettled Rspread mult (fun j => solMUReplSettledEpsLam inputs w j)
          ρu (δuSettled Bzu)) j haltCoordU
        (hdom_write j) hgZ_cont (hgZ0 j) hmix (hz_start j) (hΛ_lower j)
    simpa [solMUReplSettledRho, selectorMUWriteReadTime] using hendpoint
  · simpa [solMUReplSettledRho, selectorZWriteContraction] using hctr.add hδw
  · intro j
    dsimp [solMUReplSettledRho]
    exact add_nonneg (mul_nonneg (Real.exp_pos (-(Λ j))).le (hBz_nonneg j))
      (hδw_nonneg j)

/-- Halt-only settled endpoint start fact.

This is the shape-correct variant of `solMURepl_settled_hstart`: the settled
mix radius is just λ loser mass at the halt coordinate, with no carried u-tube
or u-drift contribution.
-/
theorem solMURepl_settled_hstart_haltOnly
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    {cfg : ℕ → ℕ → UConf}
    (inputs : SelectorReplicatorHaltConcInputs sol cfg) (w : ℕ)
    (Λ Bz : ℕ → ℝ) {Bzmax : ℝ}
    (hdom_write : ∀ j, ∀ t ∈ Icc (selectorMUWriteHoldTime j)
        (selectorMUWriteReadTime j), t ∈ selectorSchedule.domain)
    (hgZ_cont : Continuous fun t : ℝ =>
      bgpParams38.A * (sol w).α t * bGateZ bgpParams38.L ((sol w).μ t) t)
    (hgZ0 : ∀ j, ∀ t ∈ Icc (selectorMUWriteHoldTime j)
        (selectorMUWriteReadTime j),
      0 ≤ bgpParams38.A * (sol w).α t * bGateZ bgpParams38.L ((sol w).μ t) t)
    (hcfg_step : ∀ j, M_U.step (cfg w j) = cfg w (j + 1))
    (hsum : ∀ j, ∀ t ∈ Icc (selectorMUWriteHoldTime j)
        (selectorMUWriteReadTime j),
      (∑ v : UniversalLocalView, (sol w).lam v t) = 1)
    (hlam_nonneg : ∀ j, ∀ t ∈ Icc (selectorMUWriteHoldTime j)
        (selectorMUWriteReadTime j), ∀ v : UniversalLocalView,
      0 ≤ (sol w).lam v t)
    (hloser : ∀ j, ∀ t ∈ Icc (selectorMUWriteHoldTime j)
        (selectorMUWriteReadTime j),
      (Finset.univ.filter (fun v : UniversalLocalView =>
        v ≠ localViewU (cfg w j))).sum (fun v => (sol w).lam v t) ≤
          solMUReplSettledHaltEpsLam inputs w j)
    (hz_start : ∀ j,
      |(sol w).z (selectorMUWriteHoldTime j) haltCoordU -
        stackMachineEncodingU.enc (cfg w (j + 1)) haltCoordU| ≤ Bz j)
    (hΛ_lower : ∀ j,
      Λ j ≤ ∫ τ in selectorMUWriteHoldTime j..selectorMUWriteReadTime j,
        bgpParams38.A * (sol w).α τ * bGateZ bgpParams38.L ((sol w).μ τ) τ)
    (hΛ : Tendsto Λ atTop atTop)
    (hBz_nonneg : ∀ j, 0 ≤ Bz j)
    (hBz_bdd : ∀ᶠ j in atTop, Bz j ≤ Bzmax)
    (hepsLam : Tendsto (fun j => solMUReplSettledHaltEpsLam inputs w j) atTop (𝓝 0)) :
    (∀ (j : ℕ),
      |(sol w).z (2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6) haltCoordU -
        stackMachineEncodingU.enc (cfg w (j + 1)) haltCoordU| ≤
          solMUReplSettledRho Λ Bz (solMUReplSettledHaltDelta inputs w) j) ∧
    Tendsto (solMUReplSettledRho Λ Bz (solMUReplSettledHaltDelta inputs w))
      atTop (𝓝 0) ∧
    (∀ j, 0 ≤ solMUReplSettledRho Λ Bz (solMUReplSettledHaltDelta inputs w) j) := by
  have heps_nonneg : ∀ j, 0 ≤ solMUReplSettledHaltEpsLam inputs w j := by
    intro j
    have ht : selectorMUWriteHoldTime j ∈
        Icc (selectorMUWriteHoldTime j) (selectorMUWriteReadTime j) :=
      ⟨le_rfl, selectorMUWriteHold_le_read j⟩
    have hsum_nonneg :
        0 ≤
          (Finset.univ.filter (fun v : UniversalLocalView =>
            v ≠ localViewU (cfg w j))).sum (fun v => (sol w).lam v (selectorMUWriteHoldTime j)) :=
      Finset.sum_nonneg (fun v _ => hlam_nonneg j (selectorMUWriteHoldTime j) ht v)
    exact le_trans hsum_nonneg (hloser j (selectorMUWriteHoldTime j) ht)
  have hδw :
      Tendsto (solMUReplSettledHaltDelta inputs w) atTop (𝓝 0) := by
    simpa [solMUReplSettledHaltDelta] using
      Filter.Tendsto.const_mul (Fintype.card UniversalLocalView : ℝ) hepsLam
  have hctr :
      Tendsto (fun j : ℕ => selectorZWriteContraction Λ Bz j) atTop (𝓝 0) := by
    simpa using
      solMURepl_expNegLambda_Bz0_tendsto_zero (Λ := fun _ : ℕ => Λ)
        (Bz0 := fun _ : ℕ => Bz) (w := 0) hΛ
        (Filter.Eventually.of_forall hBz_nonneg) hBz_bdd
  refine ⟨?_, ?_, ?_⟩
  · intro j
    have hmix : ∀ t ∈ Icc (selectorMUWriteHoldTime j)
        (selectorMUWriteReadTime j),
        |selectorMixTarget branchU (sol w).u (sol w).lam t haltCoordU -
          stackMachineEncodingU.enc (cfg w (j + 1)) haltCoordU| ≤
            solMUReplSettledHaltDelta inputs w j := by
      intro t ht
      have hwrong : ∀ v : UniversalLocalView, v ≠ localViewU (cfg w j) →
          (sol w).lam v t ≤ solMUReplSettledHaltEpsLam inputs w j := by
        intro v hv
        have hsingle :
            (sol w).lam v t ≤
              (Finset.univ.filter (fun u : UniversalLocalView =>
                u ≠ localViewU (cfg w j))).sum (fun u => (sol w).lam u t) :=
          Finset.single_le_sum (fun u _ => hlam_nonneg j t ht u) (by simp [hv])
        exact le_trans hsingle (hloser j t ht)
      have hraw :=
        selectorMixTarget_halt_to_next_of_concentration (sol w).u (sol w).lam
          t (cfg w j) (heps_nonneg j) (hsum j t ht)
          (fun v => hlam_nonneg j t ht v) hwrong
      simpa [solMUReplSettledHaltDelta, hcfg_step j] using hraw
    have hendpoint :=
      z_write_settled_endpoint (sol w) (cfg w) Λ Bz
        (solMUReplSettledHaltDelta inputs w) j haltCoordU
        (hdom_write j) hgZ_cont (hgZ0 j) hmix (hz_start j) (hΛ_lower j)
    simpa [solMUReplSettledRho, selectorMUWriteReadTime] using hendpoint
  · simpa [solMUReplSettledRho, selectorZWriteContraction] using hctr.add hδw
  · intro j
    dsimp [solMUReplSettledRho, solMUReplSettledHaltDelta]
    exact add_nonneg
      (mul_nonneg (Real.exp_pos (-(Λ j))).le (hBz_nonneg j))
      (mul_nonneg (Nat.cast_nonneg _) (heps_nonneg j))

/-- Halting self-hold, with a finite-prefix patch and batch-3 tail. -/
theorem solMURepl_settled_hhold_of_halts
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : SelectorReplicatorDynSol d_U B_U UniversalLocalView bgpParams38
      selectorSchedule branchU
      (fun t => ((1 + Real.cos t) / 2) ^ Mcy)
      (fun t => ((1 + Real.sin t) / 2) ^ Mcy)
      (fun _ => (κ₀ : ℝ))
      (fun t => (g₀ : ℝ) * Real.exp (bgpParams38.cα * t))
      (universalPval eta heta))
    (w : ℕ) (hw : M_U.haltsOn w)
    (cfg : ℕ → UConf) (hcfg : ∀ j, cfg j = M_U.step^[j] (M_U.init w))
    (ρ δnext holdPrefix : ℕ → ℝ)
    (hρ_nonneg : ∀ j, 0 ≤ ρ j)
    (hδnext_nonneg : ∀ j, 0 ≤ δnext j)
    (hholdPrefix_nonneg : ∀ j, 0 ≤ holdPrefix j)
    (hρ : Tendsto ρ atTop (𝓝 0))
    (hδnext : Tendsto δnext atTop (𝓝 0))
    (hstart : ∀ j,
      |sol.z (selectorMUInterReadStart j) haltCoordU -
        stackMachineEncodingU.enc (cfg (j + 1)) haltCoordU| ≤ ρ j)
    (hoff : ∀ j, selectorMUHaltEncConst cfg j → ∀ t ∈
        Icc (selectorMUInterReadStart j) (selectorMUNextWriteStart j),
      |sol.z t haltCoordU - sol.z (selectorMUInterReadStart j) haltCoordU| ≤
        selectorReplicatorHoldEnvelope j)
    (hnextWrite : ∀ j, ∀ t ∈
        Icc (selectorMUNextWriteStart j) (selectorMUNextRead j),
      |sol.z t haltCoordU - stackMachineEncodingU.enc (cfg (j + 2)) haltCoordU| ≤
        δnext j)
    (hfiniteHold : ∀ j, ∀ t ∈ Icc (selectorMUInterReadStart j)
        (selectorMUNextRead j),
      |sol.z t haltCoordU - sol.z (selectorMUInterReadStart j) haltCoordU| ≤
        holdPrefix j) :
    ∃ δhold : ℕ → ℝ,
      (∀ (j : ℕ), ∀ t ∈ Icc (2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6)
          (2 * Real.pi * ((j : ℝ) + 1) + 5 * Real.pi / 6),
        |sol.z t haltCoordU -
          sol.z (2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6) haltCoordU| ≤
            δhold j) ∧
      Tendsto δhold atTop (𝓝 0) ∧
      (∀ j, 0 ≤ δhold j) := by
  obtain ⟨N, htail⟩ :=
    z_self_hold_on_inter_read_of_halts sol w hw cfg hcfg δnext ρ
      hδnext_nonneg hρ_nonneg hstart hoff hnextWrite
  refine ⟨solMUReplSettledHoldRadius N δnext ρ holdPrefix, ?_, ?_, ?_⟩
  · intro j t ht
    by_cases hj : N ≤ j
    · have h := htail j hj t (by
        simpa [selectorMUInterReadStart, selectorMUNextRead,
          selectorMUWriteReadTime] using ht)
      simpa [solMUReplSettledHoldRadius, hj, selectorMUInterReadStart,
        selectorMUWriteReadTime] using h
    · have h := hfiniteHold j t (by
        simpa [selectorMUInterReadStart, selectorMUNextRead,
          selectorMUWriteReadTime] using ht)
      simpa [solMUReplSettledHoldRadius, hj, selectorMUInterReadStart,
        selectorMUWriteReadTime] using h
  · have hself : Tendsto (selectorMUSelfHoldDelta δnext ρ) atTop (𝓝 0) :=
      selectorMUSelfHoldDelta_tendsto_zero hδnext hρ
    refine hself.congr' ?_
    have hev : ∀ᶠ j in atTop, N ≤ j :=
      Filter.eventually_atTop.mpr ⟨N, fun j hj => hj⟩
    filter_upwards [hev] with j hj
    simp [solMUReplSettledHoldRadius, hj]
  · intro j
    by_cases hj : N ≤ j
    · have henv : 0 ≤ selectorReplicatorHoldEnvelope j := by
        exact selectorReplicatorHoldEnvelope_nonneg j
      simp [solMUReplSettledHoldRadius, hj, selectorMUSelfHoldDelta]
      linarith [henv, hδnext_nonneg j, hρ_nonneg j]
    · simp [solMUReplSettledHoldRadius, hj, hholdPrefix_nonneg j]

theorem halt_flag_target_const_cfg_succ_succ_of_nonhalts
    {w : ℕ} (hw : ¬ M_U.haltsOn w)
    (cfg : ℕ → UConf) (hcfg : ∀ j, cfg j = M_U.step^[j] (M_U.init w)) :
    ∀ j, selectorMUHaltEncConst cfg j := by
  intro j
  have h2 :
      stackMachineEncodingU.enc (cfg (j + 2)) haltCoordU = (0 : ℝ) := by
    rw [hcfg (j + 2)]
    simpa [Nat.add_assoc] using flag_target_zero_of_not_halts hw (j + 1)
  have h1 :
      stackMachineEncodingU.enc (cfg (j + 1)) haltCoordU = (0 : ℝ) := by
    rw [hcfg (j + 1)]
    exact flag_target_zero_of_not_halts hw j
  unfold selectorMUHaltEncConst
  rw [h2, h1]

/-- Nonhalting self-hold: the halt flag target is globally constant at zero. -/
theorem solMURepl_settled_hhold_of_nonhalts
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : SelectorReplicatorDynSol d_U B_U UniversalLocalView bgpParams38
      selectorSchedule branchU
      (fun t => ((1 + Real.cos t) / 2) ^ Mcy)
      (fun t => ((1 + Real.sin t) / 2) ^ Mcy)
      (fun _ => (κ₀ : ℝ))
      (fun t => (g₀ : ℝ) * Real.exp (bgpParams38.cα * t))
      (universalPval eta heta))
    (w : ℕ) (hw : ¬ M_U.haltsOn w)
    (cfg : ℕ → UConf) (hcfg : ∀ j, cfg j = M_U.step^[j] (M_U.init w))
    (ρ δnext : ℕ → ℝ)
    (hρ_nonneg : ∀ j, 0 ≤ ρ j)
    (hδnext_nonneg : ∀ j, 0 ≤ δnext j)
    (hρ : Tendsto ρ atTop (𝓝 0))
    (hδnext : Tendsto δnext atTop (𝓝 0))
    (hstart : ∀ j,
      |sol.z (selectorMUInterReadStart j) haltCoordU -
        stackMachineEncodingU.enc (cfg (j + 1)) haltCoordU| ≤ ρ j)
    (hoff : ∀ j, selectorMUHaltEncConst cfg j → ∀ t ∈
        Icc (selectorMUInterReadStart j) (selectorMUNextWriteStart j),
      |sol.z t haltCoordU - sol.z (selectorMUInterReadStart j) haltCoordU| ≤
        selectorReplicatorHoldEnvelope j)
    (hnextWrite : ∀ j, ∀ t ∈
        Icc (selectorMUNextWriteStart j) (selectorMUNextRead j),
      |sol.z t haltCoordU - stackMachineEncodingU.enc (cfg (j + 2)) haltCoordU| ≤
        δnext j) :
    (∀ (j : ℕ), ∀ t ∈ Icc (2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6)
        (2 * Real.pi * ((j : ℝ) + 1) + 5 * Real.pi / 6),
      |sol.z t haltCoordU -
        sol.z (2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6) haltCoordU| ≤
          selectorMUSelfHoldDelta δnext ρ j) ∧
    Tendsto (selectorMUSelfHoldDelta δnext ρ) atTop (𝓝 0) ∧
    (∀ j, 0 ≤ selectorMUSelfHoldDelta δnext ρ j) := by
  have hconst := halt_flag_target_const_cfg_succ_succ_of_nonhalts hw cfg hcfg
  have htail :=
    z_self_hold_on_inter_read sol cfg δnext ρ 0
      (fun j _ => hδnext_nonneg j) (fun j _ => hρ_nonneg j)
      (fun j _ => hconst j) (fun j _ => hstart j)
      (fun j _ henc => hoff j henc) (fun j _ => hnextWrite j)
  refine ⟨?_, selectorMUSelfHoldDelta_tendsto_zero hδnext hρ, ?_⟩
  · intro j t ht
    have h := htail j (Nat.zero_le j) t (by
      simpa [selectorMUInterReadStart, selectorMUNextRead,
        selectorMUWriteReadTime] using ht)
    simpa [selectorMUInterReadStart, selectorMUWriteReadTime] using h
  · intro j
    have henv : 0 ≤ selectorReplicatorHoldEnvelope j := by
      exact selectorReplicatorHoldEnvelope_nonneg j
    simp [selectorMUSelfHoldDelta]
    linarith [henv, hδnext_nonneg j, hρ_nonneg j]

/-- Halt-coordinate settled residual carried by the final headline.

This is the shape-correct interface for the flag headline: it carries the
settled λ-concentration, z-write, and self-hold data actually used at
`haltCoordU`, but no u-tube or branch-spread fields.
-/
structure MUReplicatorSettledHaltFacts
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀) where
  cfg : ℕ → ℕ → UConf
  hcfg : ∀ w j, cfg w j = M_U.step^[j] (M_U.init w)
  hcfg_step : ∀ w j, M_U.step (cfg w j) = cfg w (j + 1)
  inputs : SelectorReplicatorHaltConcInputs sol cfg
  Λ : ℕ → ℕ → ℝ
  Bz : ℕ → ℕ → ℝ
  δnext : ℕ → ℕ → ℝ
  holdPrefix : ℕ → ℕ → ℝ
  Bzmax : ℝ
  R0max : ℝ
  hg₀ : 0 < (g₀ : ℝ)
  hgap0 : 0 < selectorReplicatorGapVal eta heta
  hgap_lb : ∀ w, ∀ᶠ j in atTop, selectorReplicatorGapVal eta heta ≤ inputs.gap w j
  hLmin_lb : ∀ w, ∀ᶠ j in atTop,
    (1 / (Fintype.card UniversalLocalView : ℝ)) ≤ inputs.Lmin w j
  hR0_nonneg : ∀ w, ∀ᶠ j in atTop, 0 ≤ inputs.R0 w j
  hR0_bound : ∀ w, ∀ᶠ j in atTop, inputs.R0 w j ≤ R0max
  hKreset_eq : ∀ w j,
    inputs.Kreset w j = solMUReplHaltPreForwardResetIntegral inputs w j
  hκ₀_nonneg : 0 ≤ (κ₀ : ℝ)
  hCratio_nonneg : 0 ≤ (1 : ℝ)
  hratio_bound : ∀ (w : ℕ) j, ∀ t ∈
    Icc (selectorMUWriteStartTime j) (selectorMUWriteHoldTime j),
      (((1 + Real.cos t) / 2) ^ Mcy * (κ₀ : ℝ)) ≤
        ((1 : ℝ) * Real.exp (-(bgpParams38.cα * selectorMUWriteStartTime j))) *
          (((1 + Real.sin t) / 2) ^ Mcy *
            ((g₀ : ℝ) * Real.exp (bgpParams38.cα * t)))
  hdom_write : ∀ (w : ℕ) j, ∀ t ∈ Icc (selectorMUWriteHoldTime j)
      (selectorMUWriteReadTime j), t ∈ selectorSchedule.domain
  hgZ_cont : ∀ w, Continuous fun t : ℝ =>
    bgpParams38.A * (sol w).α t * bGateZ bgpParams38.L ((sol w).μ t) t
  hgZ0 : ∀ w j, ∀ t ∈ Icc (selectorMUWriteHoldTime j)
      (selectorMUWriteReadTime j),
    0 ≤ bgpParams38.A * (sol w).α t * bGateZ bgpParams38.L ((sol w).μ t) t
  hsum : ∀ w j, ∀ t ∈ Icc (selectorMUWriteHoldTime j)
      (selectorMUWriteReadTime j),
    (∑ v : UniversalLocalView, (sol w).lam v t) = 1
  hlam_nonneg : ∀ w j, ∀ t ∈ Icc (selectorMUWriteHoldTime j)
      (selectorMUWriteReadTime j), ∀ v : UniversalLocalView, 0 ≤ (sol w).lam v t
  hloser : ∀ w j, ∀ t ∈ Icc (selectorMUWriteHoldTime j)
      (selectorMUWriteReadTime j),
    (Finset.univ.filter (fun v : UniversalLocalView =>
      v ≠ localViewU (cfg w j))).sum (fun v => (sol w).lam v t) ≤
        solMUReplSettledHaltEpsLam inputs w j
  hz_start : ∀ w j,
    |(sol w).z (selectorMUWriteHoldTime j) haltCoordU -
      stackMachineEncodingU.enc (cfg w (j + 1)) haltCoordU| ≤ Bz w j
  hΛ_lower : ∀ w j,
    Λ w j ≤ ∫ τ in selectorMUWriteHoldTime j..selectorMUWriteReadTime j,
      bgpParams38.A * (sol w).α τ * bGateZ bgpParams38.L ((sol w).μ τ) τ
  hΛ : ∀ w, Tendsto (Λ w) atTop atTop
  hBz_nonneg : ∀ w j, 0 ≤ Bz w j
  hBz_bdd : ∀ w, ∀ᶠ j in atTop, Bz w j ≤ Bzmax
  hδnext : ∀ w, Tendsto (δnext w) atTop (𝓝 0)
  hδnext_nonneg : ∀ w j, 0 ≤ δnext w j
  hholdPrefix_nonneg : ∀ w j, 0 ≤ holdPrefix w j
  hoff : ∀ w j, selectorMUHaltEncConst (cfg w) j → ∀ t ∈
      Icc (selectorMUInterReadStart j) (selectorMUNextWriteStart j),
    |(sol w).z t haltCoordU - (sol w).z (selectorMUInterReadStart j) haltCoordU| ≤
      selectorReplicatorHoldEnvelope j
  hnextWrite : ∀ w j, ∀ t ∈ Icc (selectorMUNextWriteStart j) (selectorMUNextRead j),
    |(sol w).z t haltCoordU - stackMachineEncodingU.enc (cfg w (j + 2)) haltCoordU| ≤
      δnext w j
  hfiniteHold : ∀ w j, ∀ t ∈ Icc (selectorMUInterReadStart j) (selectorMUNextRead j),
    |(sol w).z t haltCoordU - (sol w).z (selectorMUInterReadStart j) haltCoordU| ≤
      holdPrefix w j

/-- Halt-only settled read-start package carried by `MUReplicatorSettledHaltFacts`. -/
theorem MUReplicatorSettledHaltFacts.hstart_haltOnly
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (settled : MUReplicatorSettledHaltFacts sol) (w : ℕ) :
    (∀ (j : ℕ),
      |(sol w).z (2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6) haltCoordU -
        stackMachineEncodingU.enc (settled.cfg w (j + 1)) haltCoordU| ≤
          solMUReplSettledRho (settled.Λ w) (settled.Bz w)
            (solMUReplSettledHaltDelta settled.inputs w) j) ∧
    Tendsto
      (solMUReplSettledRho (settled.Λ w) (settled.Bz w)
        (solMUReplSettledHaltDelta settled.inputs w))
      atTop (𝓝 0) ∧
    (∀ j,
      0 ≤ solMUReplSettledRho (settled.Λ w) (settled.Bz w)
        (solMUReplSettledHaltDelta settled.inputs w) j) := by
  have hepsLam :
      Tendsto (fun j => solMUReplSettledHaltEpsLam settled.inputs w j)
        atTop (𝓝 0) :=
    solMURepl_settled_haltEpsLam_tendsto_zero settled.inputs w settled.hg₀
      settled.hgap0 (settled.hgap_lb w) solMURepl_concLmin_floor
      (settled.hLmin_lb w) (settled.hR0_nonneg w) (settled.hR0_bound w)
      (settled.hKreset_eq w) settled.hκ₀_nonneg settled.hCratio_nonneg
      (settled.hratio_bound w)
  exact
    solMURepl_settled_hstart_haltOnly (Bzmax := settled.Bzmax)
      settled.inputs w (settled.Λ w) (settled.Bz w)
      (settled.hdom_write w) (settled.hgZ_cont w) (settled.hgZ0 w)
      (settled.hcfg_step w) (settled.hsum w) (settled.hlam_nonneg w)
      (settled.hloser w)
      (settled.hz_start w) (settled.hΛ_lower w) (settled.hΛ w)
      (settled.hBz_nonneg w) (settled.hBz_bdd w) hepsLam

/-- Selector/MU-side late-start read-start residual.

This is deliberately not a `Paper3Main` residual: it packages the read-start
bound for a `MUReplicatorSolFamily`, before any bridge to the final
`DynContractIteratorSol` representation.
-/
structure MUReplicatorLateStartReadStartResidual
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀) where
  Bz_read : ℕ → ℕ → ℝ
  hz_read_start : ∀ (w j : ℕ),
    |(sol w).z (2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6) haltCoordU -
      stackMachineEncodingU.enc (M_U.step^[j + 1] (M_U.init w)) haltCoordU| ≤
        Bz_read w j
  hBz_read_tendsto : ∀ w, Tendsto (Bz_read w) atTop (𝓝 0)
  hBz_read_nonneg : ∀ w j, 0 ≤ Bz_read w j

/-- Settled halt facts produce the selector/MU late-start read-start residual. -/
def mu_replicator_late_start_read_start_of_settled_facts
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (settled : MUReplicatorSettledHaltFacts sol) :
    MUReplicatorLateStartReadStartResidual sol where
  Bz_read := fun w j =>
    solMUReplSettledRho (settled.Λ w) (settled.Bz w)
      (solMUReplSettledHaltDelta settled.inputs w) j
  hz_read_start := by
    intro w j
    have hstart := settled.hstart_haltOnly w
    simpa [settled.hcfg w (j + 1)] using hstart.1 j
  hBz_read_tendsto := by
    intro w
    exact (settled.hstart_haltOnly w).2.1
  hBz_read_nonneg := by
    intro w j
    exact (settled.hstart_haltOnly w).2.2 j

/-- Halt-coordinate final data after the read-start bound has already been
proved.

This is the interface used by rate-shaped concentration producers: the final
halt/nonhalt argument needs a vanishing read-start radius, the `hoff` hold
bridge, the next-write window bound, and a finite-prefix hold patch.  It does
not need the particular concentration formula used by
`MUReplicatorSettledHaltFacts.hstart_haltOnly`. -/
structure MUReplicatorLateStartHaltFacts
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀) where
  cfg : ℕ → ℕ → UConf
  hcfg : ∀ w j, cfg w j = M_U.step^[j] (M_U.init w)
  readStart : MUReplicatorLateStartReadStartResidual sol
  δnext : ℕ → ℕ → ℝ
  holdPrefix : ℕ → ℕ → ℝ
  hδnext : ∀ w, Tendsto (δnext w) atTop (𝓝 0)
  hδnext_nonneg : ∀ w j, 0 ≤ δnext w j
  hholdPrefix_nonneg : ∀ w j, 0 ≤ holdPrefix w j
  hoff : ∀ w j, selectorMUHaltEncConst (cfg w) j → ∀ t ∈ Icc (selectorMUInterReadStart j)
      (selectorMUNextWriteStart j),
    |(sol w).z t haltCoordU - (sol w).z (selectorMUInterReadStart j) haltCoordU| ≤
      selectorReplicatorHoldEnvelope j
  hnextWrite : ∀ w j, ∀ t ∈ Icc (selectorMUNextWriteStart j)
      (selectorMUNextRead j),
    |(sol w).z t haltCoordU -
      stackMachineEncodingU.enc (cfg w (j + 2)) haltCoordU| ≤
        δnext w j
  hfiniteHold : ∀ w j, ∀ t ∈ Icc (selectorMUInterReadStart j)
      (selectorMUNextRead j),
    |(sol w).z t haltCoordU - (sol w).z (selectorMUInterReadStart j) haltCoordU| ≤
      holdPrefix w j

/-- Legacy full settled residual bundle.  This still carries stack/tube fields
needed by older adapters; the public final headline consumes
`MUReplicatorSettledHaltFacts`. -/
structure MUReplicatorSettledFacts
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀) where
  cfg : ℕ → ℕ → UConf
  hcfg : ∀ w j, cfg w j = M_U.step^[j] (M_U.init w)
  hcfg_step : ∀ w j, M_U.step (cfg w j) = cfg w (j + 1)
  inputs : SelectorReplicatorConcInputs sol cfg
  Λ : ℕ → ℕ → ℝ
  Bz : ℕ → ℕ → ℝ
  ρu : ℕ → ℕ → ℝ
  δnext : ℕ → ℕ → ℝ
  holdPrefix : ℕ → ℕ → ℝ
  Rspread : ℝ
  mult : ℝ
  Bzu : ℝ
  Bzmax : ℝ
  R0max : ℝ
  hg₀ : 0 < (g₀ : ℝ)
  hgap0 : 0 < selectorReplicatorGapVal eta heta
  hgap_lb : ∀ w, ∀ᶠ j in atTop, selectorReplicatorGapVal eta heta ≤ inputs.gap w j
  hLmin_lb : ∀ w, ∀ᶠ j in atTop,
    (1 / (Fintype.card UniversalLocalView : ℝ)) ≤ inputs.Lmin w j
  hR0_nonneg : ∀ w, ∀ᶠ j in atTop, 0 ≤ inputs.R0 w j
  hR0_bound : ∀ w, ∀ᶠ j in atTop, inputs.R0 w j ≤ R0max
  hKreset_eq : ∀ w j, inputs.Kreset w j = solMUReplPreForwardResetIntegral inputs w j
  -- Note: ConcInputs.hKreset bounds ∫ writeStart..writeHold ≤ Kreset (prefix, not full)
  hκ₀_nonneg : 0 ≤ (κ₀ : ℝ)
  hCratio_nonneg : 0 ≤ (1 : ℝ)
  hratio_bound : ∀ (w : ℕ) j, ∀ t ∈
    Icc (selectorMUWriteStartTime j) (selectorMUWriteHoldTime j),
      (((1 + Real.cos t) / 2) ^ Mcy * (κ₀ : ℝ)) ≤
        ((1 : ℝ) * Real.exp (-(bgpParams38.cα * selectorMUWriteStartTime j))) *
          (((1 + Real.sin t) / 2) ^ Mcy *
            ((g₀ : ℝ) * Real.exp (bgpParams38.cα * t)))
  hdom_nonneg : ∀ t : ℝ, 0 ≤ t → t ∈ selectorSchedule.domain
  hdom_write : ∀ (w : ℕ) j, ∀ t ∈ Icc (selectorMUWriteHoldTime j)
      (selectorMUWriteReadTime j), t ∈ selectorSchedule.domain
  hgZ_cont : ∀ w, Continuous fun t : ℝ =>
    bgpParams38.A * (sol w).α t * bGateZ bgpParams38.L ((sol w).μ t) t
  hgZ0 : ∀ w j, ∀ t ∈ Icc (selectorMUWriteHoldTime j)
      (selectorMUWriteReadTime j),
    0 ≤ bgpParams38.A * (sol w).α t * bGateZ bgpParams38.L ((sol w).μ t) t
  hmult0 : 0 ≤ mult
  hmultbound : ∀ w j, ∀ i, stackMachineEncodingU.coordMultiplier (cfg w j) i ≤ mult
  hsum : ∀ w j, ∀ t ∈ Icc (selectorMUWriteHoldTime j)
      (selectorMUWriteReadTime j),
    (∑ v : UniversalLocalView, (sol w).lam v t) = 1
  hlam_nonneg : ∀ w j, ∀ t ∈ Icc (selectorMUWriteHoldTime j)
      (selectorMUWriteReadTime j), ∀ v : UniversalLocalView, 0 ≤ (sol w).lam v t
  hloser : ∀ w j, ∀ t ∈ Icc (selectorMUWriteHoldTime j)
      (selectorMUWriteReadTime j),
    (Finset.univ.filter (fun v : UniversalLocalView =>
      v ≠ localViewU (cfg w j))).sum (fun v => (sol w).lam v t) ≤
        solMUReplSettledEpsLam inputs w j
  hRspread_nonneg : 0 ≤ Rspread
  hspread : ∀ w j, ∀ t ∈ Icc (selectorMUWriteHoldTime j)
      (selectorMUWriteReadTime j), ∀ i, ∀ v : UniversalLocalView,
    v ≠ localViewU (cfg w j) →
      |BranchData.evalBranch (branchU v) ((sol w).u t) i
        - BranchData.evalBranch (branchU (localViewU (cfg w j)))
            ((sol w).u t) i| ≤ Rspread
  hutube_write : ∀ w j, ∀ i,
    |(sol w).u (selectorMUWriteHoldTime j) i -
      stackMachineEncodingU.enc (cfg w j) i| ≤ ρu w j
  hBzu0 : 0 ≤ Bzu
  hzu : ∀ w j, ∀ t ∈ Icc (selectorMUWriteHoldTime j)
      (selectorMUWriteReadTime j), ∀ i,
    |(sol w).z t i - (sol w).u t i| ≤ Bzu
  hz_start : ∀ w j,
    |(sol w).z (selectorMUWriteHoldTime j) haltCoordU -
      stackMachineEncodingU.enc (cfg w (j + 1)) haltCoordU| ≤ Bz w j
  hΛ_lower : ∀ w j,
    Λ w j ≤ ∫ τ in selectorMUWriteHoldTime j..selectorMUWriteReadTime j,
      bgpParams38.A * (sol w).α τ * bGateZ bgpParams38.L ((sol w).μ τ) τ
  hΛ : ∀ w, Tendsto (Λ w) atTop atTop
  hBz_nonneg : ∀ w j, 0 ≤ Bz w j
  hBz_bdd : ∀ w, ∀ᶠ j in atTop, Bz w j ≤ Bzmax
  hρu : ∀ w, Tendsto (ρu w) atTop (𝓝 0)
  hδw_nonneg : ∀ w j,
    0 ≤ δwSettled Rspread mult (fun j => solMUReplSettledEpsLam inputs w j)
      (ρu w) (δuSettled Bzu) j
  hδnext : ∀ w, Tendsto (δnext w) atTop (𝓝 0)
  hδnext_nonneg : ∀ w j, 0 ≤ δnext w j
  hholdPrefix_nonneg : ∀ w j, 0 ≤ holdPrefix w j
  hoff : ∀ w j, selectorMUHaltEncConst (cfg w) j → ∀ t ∈
      Icc (selectorMUInterReadStart j) (selectorMUNextWriteStart j),
    |(sol w).z t haltCoordU - (sol w).z (selectorMUInterReadStart j) haltCoordU| ≤
      selectorReplicatorHoldEnvelope j
  hnextWrite : ∀ w j, ∀ t ∈ Icc (selectorMUNextWriteStart j) (selectorMUNextRead j),
    |(sol w).z t haltCoordU - stackMachineEncodingU.enc (cfg w (j + 2)) haltCoordU| ≤
      δnext w j
  hfiniteHold : ∀ w j, ∀ t ∈ Icc (selectorMUInterReadStart j) (selectorMUNextRead j),
    |(sol w).z t haltCoordU - (sol w).z (selectorMUInterReadStart j) haltCoordU| ≤
      holdPrefix w j

def MUReplicatorSettledFacts.toHaltFacts
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (settled : MUReplicatorSettledFacts sol) : MUReplicatorSettledHaltFacts sol :=
  let hinputs : SelectorReplicatorHaltConcInputs sol settled.cfg :=
    { Lmin := settled.inputs.Lmin
      gap := settled.inputs.gap
      R0 := settled.inputs.R0
      Kreset := settled.inputs.Kreset
      hLmin_pos := settled.inputs.hLmin_pos
      hqL := settled.inputs.hqL
      hgap := settled.inputs.hgap
      hRa := settled.inputs.hRa
      hKreset := settled.inputs.hKreset }
  { cfg := settled.cfg
    hcfg := settled.hcfg
    hcfg_step := settled.hcfg_step
    inputs := hinputs
    Λ := settled.Λ
    Bz := settled.Bz
    δnext := settled.δnext
    holdPrefix := settled.holdPrefix
    Bzmax := settled.Bzmax
    R0max := settled.R0max
    hg₀ := settled.hg₀
    hgap0 := settled.hgap0
    hgap_lb := settled.hgap_lb
    hLmin_lb := settled.hLmin_lb
    hR0_nonneg := settled.hR0_nonneg
    hR0_bound := settled.hR0_bound
    hKreset_eq := by
      intro w j
      simpa [hinputs, solMUReplHaltPreForwardResetIntegral,
        solMUReplPreForwardResetIntegral] using settled.hKreset_eq w j
    hκ₀_nonneg := settled.hκ₀_nonneg
    hCratio_nonneg := settled.hCratio_nonneg
    hratio_bound := settled.hratio_bound
    hdom_write := settled.hdom_write
    hgZ_cont := settled.hgZ_cont
    hgZ0 := settled.hgZ0
    hsum := settled.hsum
    hlam_nonneg := settled.hlam_nonneg
    hloser := by
      intro w j t ht
      simpa [hinputs, solMUReplSettledHaltEpsLam, solMUReplSettledEpsLam] using
        settled.hloser w j t ht
    hz_start := settled.hz_start
    hΛ_lower := settled.hΛ_lower
    hΛ := settled.hΛ
    hBz_nonneg := settled.hBz_nonneg
    hBz_bdd := settled.hBz_bdd
    hδnext := settled.hδnext
    hδnext_nonneg := settled.hδnext_nonneg
    hholdPrefix_nonneg := settled.hholdPrefix_nonneg
    hoff := settled.hoff
    hnextWrite := settled.hnextWrite
    hfiniteHold := settled.hfiniteHold }

set_option maxHeartbeats 800000 in
-- The final assembled proof replays the end-to-end halt/nonhalt construction.
theorem bgp_MU_replicator_settled
    (eta : ℚ) (heta : 0 < eta) (M : ℕ) (κ₀ g₀ : ℚ)
    (HP : MvPolynomial (Fin d_U) ℚ) (Kq : ℚ) (R : ℕ)
    (hfin : ∀ w,
      Ripple.FiniteHorizonBound (selectorMUReplicatorField eta heta M κ₀ g₀ HP Kq R)
        (selectorMUReplicatorInit selectorInitX0 w g₀))
    (hgateZ : ∀ w,
      ∀ y : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        y 0 = selectorMUReplicatorInit selectorInitX0 w g₀ →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y (selectorMUReplicatorField eta heta M κ₀ g₀ HP Kq R (y t)) t) →
        ∀ t : ℝ, 0 ≤ t →
          y t (selOfContract UniversalLocalView (contractGateZ d_U)) =
            bGateZ 1 (y t (selOfContract UniversalLocalView (contractMu d_U))) t)
    (hgateU : ∀ w,
      ∀ y : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        y 0 = selectorMUReplicatorInit selectorInitX0 w g₀ →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y (selectorMUReplicatorField eta heta M κ₀ g₀ HP Kq R (y t)) t) →
        ∀ t : ℝ, 0 ≤ t →
          y t (selOfContract UniversalLocalView (contractGateU d_U)) =
            bGateU 1 (y t (selOfContract UniversalLocalView (contractMu d_U))) t)
    (h_chiReset : ∀ w,
      ∀ y : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        y 0 = selectorMUReplicatorInit selectorInitX0 w g₀ →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y (selectorMUReplicatorField eta heta M κ₀ g₀ HP Kq R (y t)) t) →
        ∀ t : ℝ, 0 ≤ t →
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t)
            (selChiResetPoly d_U UniversalLocalView M) =
              ((1 + Real.cos t) / 2) ^ M)
    (h_chiGate : ∀ w,
      ∀ y : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        y 0 = selectorMUReplicatorInit selectorInitX0 w g₀ →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y (selectorMUReplicatorField eta heta M κ₀ g₀ HP Kq R (y t)) t) →
        ∀ t : ℝ, 0 ≤ t →
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t)
            (selChiGatePoly d_U UniversalLocalView M) =
              ((1 + Real.sin t) / 2) ^ M)
    (h_kappa : ∀ w,
      ∀ y : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        y 0 = selectorMUReplicatorInit selectorInitX0 w g₀ →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y (selectorMUReplicatorField eta heta M κ₀ g₀ HP Kq R (y t)) t) →
        ∀ t : ℝ, 0 ≤ t →
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t)
            (selKappaPoly d_U UniversalLocalView κ₀) = (κ₀ : ℝ))
    (h_gain : ∀ w,
      ∀ y : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        y 0 = selectorMUReplicatorInit selectorInitX0 w g₀ →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y (selectorMUReplicatorField eta heta M κ₀ g₀ HP Kq R (y t)) t) →
        ∀ t : ℝ, 0 ≤ t →
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t)
            (selGainPoly d_U UniversalLocalView) =
              (g₀ : ℝ) * Real.exp (bgpParams38.cα * t))
    (h_P : ∀ w,
      ∀ y : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        y 0 = selectorMUReplicatorInit selectorInitX0 w g₀ →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y (selectorMUReplicatorField eta heta M κ₀ g₀ HP Kq R (y t)) t) →
        ∀ (v : UniversalLocalView) (t : ℝ), 0 ≤ t →
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t)
            ((muReadoutPoly eta heta) v) =
              universalPval eta heta v (fun i => y t (selU UniversalLocalView i)))
    (init_presented :
      ∃ f : ℕ → Fin (selectorDim d_U UniversalLocalView + 1) → ℤ × ℕ,
        Computable f ∧
        ∀ w i, (f w i).2 ≠ 0 ∧
          selectorReplicatorSphereInitQ d_U UniversalLocalView selectorInitX0 w g₀ i =
            (f w i).1 / ((f w i).2 : ℚ))
    (init_zero :
      ∀ (w : ℕ)
        (La : SelectorReplicatorHaltLatchSol
          ((solMURepl eta heta M κ₀ g₀ HP Kq R selectorInitX0 hfin hgateZ hgateU
            h_chiReset h_chiGate h_kappa h_gain h_P) w)
          (fun _ : (Fin d_U → ℝ) => (0 : ℝ)) 0 R),
          ((selectorReplicatorSphereInitQ d_U UniversalLocalView selectorInitX0 w g₀ 0 : ℚ) : ℝ) =
            ((∑ i : Fin (selectorDim d_U UniversalLocalView),
                selectorReplicatorTupleTraj
                  ((solMURepl eta heta M κ₀ g₀ HP Kq R selectorInitX0 hfin hgateZ hgateU
                    h_chiReset h_chiGate h_kappa h_gain h_P) w) La (g₀ : ℝ) 0 i ^ 2) - 1) /
              ((∑ i : Fin (selectorDim d_U UniversalLocalView),
                selectorReplicatorTupleTraj
                  ((solMURepl eta heta M κ₀ g₀ HP Kq R selectorInitX0 hfin hgateZ hgateU
                    h_chiReset h_chiGate h_kappa h_gain h_P) w) La (g₀ : ℝ) 0 i ^ 2) + 1))
    (init_succ :
      ∀ (w : ℕ)
        (La : SelectorReplicatorHaltLatchSol
          ((solMURepl eta heta M κ₀ g₀ HP Kq R selectorInitX0 hfin hgateZ hgateU
            h_chiReset h_chiGate h_kappa h_gain h_P) w)
          (fun _ : (Fin d_U → ℝ) => (0 : ℝ)) 0 R)
        (i : Fin (selectorDim d_U UniversalLocalView)),
          ((selectorReplicatorSphereInitQ d_U UniversalLocalView selectorInitX0 w g₀ i.succ : ℚ) : ℝ) =
            2 * selectorReplicatorTupleTraj
              ((solMURepl eta heta M κ₀ g₀ HP Kq R selectorInitX0 hfin hgateZ hgateU
                h_chiReset h_chiGate h_kappa h_gain h_P) w) La (g₀ : ℝ) 0 i /
              ((∑ k : Fin (selectorDim d_U UniversalLocalView),
                selectorReplicatorTupleTraj
                  ((solMURepl eta heta M κ₀ g₀ HP Kq R selectorInitX0 hfin hgateZ hgateU
                    h_chiReset h_chiGate h_kappa h_gain h_P) w) La (g₀ : ℝ) 0 k ^ 2) + 1))
    (boxInputs : MUReplicatorBoxInputs eta heta M κ₀ g₀
      (solMURepl eta heta M κ₀ g₀ HP Kq R selectorInitX0 hfin hgateZ hgateU
        h_chiReset h_chiGate h_kappa h_gain h_P))
    (settled : MUReplicatorSettledHaltFacts
      (solMURepl eta heta M κ₀ g₀ HP Kq R selectorInitX0 hfin hgateZ hgateU
        h_chiReset h_chiGate h_kappa h_gain h_P)) :
    ∃ P : Ripple.BoundedUniversality.GPAC.PIVP ℚ,
      Nonempty (EventualThresholdSimulation P UniversalMachine.undecidableMachine) := by
  classical
  haveI : Nonempty UniversalLocalView := ⟨defaultLocalViewU⟩
  let sol : MUReplicatorSolFamily eta heta M κ₀ g₀ :=
    solMURepl eta heta M κ₀ g₀ HP Kq R selectorInitX0 hfin hgateZ hgateU
      h_chiReset h_chiGate h_kappa h_gain h_P
  have hforward_boxes : ∀ w,
      (∀ t : ℝ, 0 ≤ t →
        selectorMixTarget branchU (sol w).u (sol w).lam t haltCoordU ∈ Icc (0 : ℝ) 1) ∧
      (∀ t : ℝ, 0 ≤ t → (sol w).z t haltCoordU ≤ 1) ∧
      (∀ t : ℝ, 0 ≤ t → 0 ≤ (sol w).z t haltCoordU) := by
    intro w
    have hode : ∀ v : UniversalLocalView, ∀ t : ℝ, 0 ≤ t →
        HasDerivAt ((sol w).lam v)
          ((((1 + Real.cos t) / 2) ^ M * (κ₀ : ℝ)) *
              (1 / (Fintype.card UniversalLocalView : ℝ) - (sol w).lam v t)
            + (((1 + Real.sin t) / 2) ^ M *
                ((g₀ : ℝ) * Real.exp (bgpParams38.cα * t))) *
              (sol w).lam v t *
                (universalPval eta heta v ((sol w).u t)
                  - ∑ u : UniversalLocalView,
                      (sol w).lam u t * universalPval eta heta u ((sol w).u t))) t := by
      intro v t ht
      simpa [selectorSchedule] using
        (sol w).lam_hasDeriv v t (by simpa [selectorSchedule] using ht)
    have hsum : ∀ t : ℝ, 0 ≤ t →
        (∑ v : UniversalLocalView, (sol w).lam v t) = 1 :=
      replicator_sum_lam_eq_one
        (lam := fun v t => (sol w).lam v t)
        (P := fun v t => universalPval eta heta v ((sol w).u t))
        (cr := fun t => ((1 + Real.cos t) / 2) ^ M * (κ₀ : ℝ))
        (cg := fun t =>
          ((1 + Real.sin t) / 2) ^ M *
            ((g₀ : ℝ) * Real.exp (bgpParams38.cα * t)))
        boxInputs.hcr_cont boxInputs.hcg_cont
        (fun v => (sol w).cont_lam v)
        (boxInputs.hP_cont w) hode (boxInputs.hlam_sum0 w)
    have hlam_nonneg_forward :
        ∀ v : UniversalLocalView, ∀ t : ℝ, 0 ≤ t → 0 ≤ (sol w).lam v t :=
      replicator_lam_nonneg
        (lam := fun v t => (sol w).lam v t)
        (P := fun v t => universalPval eta heta v ((sol w).u t))
        (cr := fun t => ((1 + Real.cos t) / 2) ^ M * (κ₀ : ℝ))
        (cg := fun t =>
          ((1 + Real.sin t) / 2) ^ M *
            ((g₀ : ℝ) * Real.exp (bgpParams38.cα * t)))
        boxInputs.hcr_cont boxInputs.hcg_cont
        (fun v => (sol w).cont_lam v)
        (boxInputs.hP_cont w) boxInputs.hcr_nonneg hode
        (boxInputs.hlam_init_nonneg w)
    have hmix : ∀ t : ℝ, 0 ≤ t →
        selectorMixTarget branchU (sol w).u (sol w).lam t haltCoordU ∈ Icc (0 : ℝ) 1 := by
      intro t ht
      exact selectorMixTarget_haltCoord_mem_Icc_of_lam_sum_eq_one
        (sol w).u (sol w).lam t
        (fun v => hlam_nonneg_forward v t ht)
        (hsum t ht)
    have hzbox :=
      selector_replicator_flag_box_on_nonneg_repl (sol w)
        boxInputs.hcr_cont boxInputs.hcg_cont (boxInputs.hP_cont w)
        boxInputs.hcr_nonneg (boxInputs.hlam_sum0 w)
        (boxInputs.hlam_init_nonneg w) (boxInputs.hz0 w)
    exact ⟨hmix, hzbox.1, hzbox.2⟩
  have correct_halt_z :
      ∀ w, UniversalMachine.undecidableMachine.toDiscreteMachine.haltsOn w →
        ∃ T : ℝ, ∀ t ≥ T, 3 / 4 ≤ (sol w).z t haltCoordU ∧
          (sol w).z t haltCoordU ≤ 1 := by
    intro w hw
    have hwU : M_U.haltsOn w := by
      simpa using hw
    have hstart := settled.hstart_haltOnly w
    have hhold :=
      solMURepl_settled_hhold_of_halts (sol w) w hwU (settled.cfg w)
        (settled.hcfg w)
        (solMUReplSettledRho (settled.Λ w) (settled.Bz w)
          (solMUReplSettledHaltDelta settled.inputs w))
        (settled.δnext w) (settled.holdPrefix w)
        hstart.2.2 (settled.hδnext_nonneg w) (settled.hholdPrefix_nonneg w)
        hstart.2.1 (settled.hδnext w) hstart.1
        (settled.hoff w) (settled.hnextWrite w) (settled.hfiniteHold w)
    obtain ⟨δhold, hhold_all, hδhold, hδhold_nonneg⟩ := hhold
    exact selector_correct_halt_endtoend_hold_repl_of_tendsto (sol w) w hwU
      (settled.cfg w) (settled.hcfg w)
      (solMUReplSettledRho (settled.Λ w) (settled.Bz w)
        (solMUReplSettledHaltDelta settled.inputs w))
      δhold hstart.1 hhold_all (hforward_boxes w).2.1
      hstart.2.1 hδhold hstart.2.2 hδhold_nonneg
  have correct_nonhalt_z :
      ∀ w, ¬ UniversalMachine.undecidableMachine.toDiscreteMachine.haltsOn w →
        ∃ T : ℝ, ∀ t ≥ T, 0 ≤ (sol w).z t haltCoordU ∧
          (sol w).z t haltCoordU ≤ 1 / 4 := by
    intro w hw
    have hwU : ¬ M_U.haltsOn w := by
      simpa using hw
    have hstart := settled.hstart_haltOnly w
    have hhold :=
      solMURepl_settled_hhold_of_nonhalts (sol w) w hwU (settled.cfg w)
        (settled.hcfg w)
        (solMUReplSettledRho (settled.Λ w) (settled.Bz w)
          (solMUReplSettledHaltDelta settled.inputs w))
        (settled.δnext w)
        hstart.2.2 (settled.hδnext_nonneg w) hstart.2.1
        (settled.hδnext w) hstart.1 (settled.hoff w) (settled.hnextWrite w)
    exact selector_correct_nonhalt_endtoend_hold_repl_of_tendsto (sol w) w hwU
      (settled.cfg w) (settled.hcfg w)
      (solMUReplSettledRho (settled.Λ w) (settled.Bz w)
        (solMUReplSettledHaltDelta settled.inputs w))
      (selectorMUSelfHoldDelta (settled.δnext w)
        (solMUReplSettledRho (settled.Λ w) (settled.Bz w)
          (solMUReplSettledHaltDelta settled.inputs w)))
      hstart.1 hhold.1 (hforward_boxes w).2.2
      hstart.2.1 hhold.2.1 hstart.2.2 hhold.2.2
  exact main_assembled_mu_selector_zreadout_nolatch_repl_of_sol_init
    eta heta M κ₀ g₀ R selectorInitX0 init_presented sol
    (fun w => init_zero w (selector_replicator_zero_latch_solution (sol w) R))
    (fun w i => init_succ w (selector_replicator_zero_latch_solution (sol w) R) i)
    correct_halt_z correct_nonhalt_z

set_option maxHeartbeats 800000 in
-- This mirrors `bgp_MU_replicator_settled` with a different read-start source.
/-- Final selector/MU headline with the read-start bound supplied directly.

This is the same halt/nonhalt endgame as `bgp_MU_replicator_settled`, but the
read-start radius is an input package rather than being produced from the
old fixed `solMUReplSettledHaltEpsLam` concentration formula. -/
theorem bgp_MU_replicator_settled_late_start
    (eta : ℚ) (heta : 0 < eta) (M : ℕ) (κ₀ g₀ : ℚ)
    (HP : MvPolynomial (Fin d_U) ℚ) (Kq : ℚ) (R : ℕ)
    (hfin : ∀ w,
      Ripple.FiniteHorizonBound (selectorMUReplicatorField eta heta M κ₀ g₀ HP Kq R)
        (selectorMUReplicatorInit selectorInitX0 w g₀))
    (hgateZ : ∀ w,
      ∀ y : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        y 0 = selectorMUReplicatorInit selectorInitX0 w g₀ →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y (selectorMUReplicatorField eta heta M κ₀ g₀ HP Kq R (y t)) t) →
        ∀ t : ℝ, 0 ≤ t →
          y t (selOfContract UniversalLocalView (contractGateZ d_U)) =
            bGateZ 1 (y t (selOfContract UniversalLocalView (contractMu d_U))) t)
    (hgateU : ∀ w,
      ∀ y : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        y 0 = selectorMUReplicatorInit selectorInitX0 w g₀ →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y (selectorMUReplicatorField eta heta M κ₀ g₀ HP Kq R (y t)) t) →
        ∀ t : ℝ, 0 ≤ t →
          y t (selOfContract UniversalLocalView (contractGateU d_U)) =
            bGateU 1 (y t (selOfContract UniversalLocalView (contractMu d_U))) t)
    (h_chiReset : ∀ w,
      ∀ y : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        y 0 = selectorMUReplicatorInit selectorInitX0 w g₀ →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y (selectorMUReplicatorField eta heta M κ₀ g₀ HP Kq R (y t)) t) →
        ∀ t : ℝ, 0 ≤ t →
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t)
            (selChiResetPoly d_U UniversalLocalView M) =
              ((1 + Real.cos t) / 2) ^ M)
    (h_chiGate : ∀ w,
      ∀ y : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        y 0 = selectorMUReplicatorInit selectorInitX0 w g₀ →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y (selectorMUReplicatorField eta heta M κ₀ g₀ HP Kq R (y t)) t) →
        ∀ t : ℝ, 0 ≤ t →
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t)
            (selChiGatePoly d_U UniversalLocalView M) =
              ((1 + Real.sin t) / 2) ^ M)
    (h_kappa : ∀ w,
      ∀ y : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        y 0 = selectorMUReplicatorInit selectorInitX0 w g₀ →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y (selectorMUReplicatorField eta heta M κ₀ g₀ HP Kq R (y t)) t) →
        ∀ t : ℝ, 0 ≤ t →
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t)
            (selKappaPoly d_U UniversalLocalView κ₀) = (κ₀ : ℝ))
    (h_gain : ∀ w,
      ∀ y : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        y 0 = selectorMUReplicatorInit selectorInitX0 w g₀ →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y (selectorMUReplicatorField eta heta M κ₀ g₀ HP Kq R (y t)) t) →
        ∀ t : ℝ, 0 ≤ t →
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t)
            (selGainPoly d_U UniversalLocalView) =
              (g₀ : ℝ) * Real.exp (bgpParams38.cα * t))
    (h_P : ∀ w,
      ∀ y : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        y 0 = selectorMUReplicatorInit selectorInitX0 w g₀ →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y (selectorMUReplicatorField eta heta M κ₀ g₀ HP Kq R (y t)) t) →
        ∀ (v : UniversalLocalView) (t : ℝ), 0 ≤ t →
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t)
            ((muReadoutPoly eta heta) v) =
              universalPval eta heta v (fun i => y t (selU UniversalLocalView i)))
    (init_presented :
      ∃ f : ℕ → Fin (selectorDim d_U UniversalLocalView + 1) → ℤ × ℕ,
        Computable f ∧
        ∀ w i, (f w i).2 ≠ 0 ∧
          selectorReplicatorSphereInitQ d_U UniversalLocalView selectorInitX0 w g₀ i =
            (f w i).1 / ((f w i).2 : ℚ))
    (init_zero :
      ∀ (w : ℕ)
        (La : SelectorReplicatorHaltLatchSol
          ((solMURepl eta heta M κ₀ g₀ HP Kq R selectorInitX0 hfin hgateZ hgateU
            h_chiReset h_chiGate h_kappa h_gain h_P) w)
          (fun _ : (Fin d_U → ℝ) => (0 : ℝ)) 0 R),
          ((selectorReplicatorSphereInitQ d_U UniversalLocalView selectorInitX0 w g₀ 0 : ℚ) : ℝ) =
            ((∑ i : Fin (selectorDim d_U UniversalLocalView),
                selectorReplicatorTupleTraj
                  ((solMURepl eta heta M κ₀ g₀ HP Kq R selectorInitX0 hfin hgateZ hgateU
                    h_chiReset h_chiGate h_kappa h_gain h_P) w) La (g₀ : ℝ) 0 i ^ 2) - 1) /
              ((∑ i : Fin (selectorDim d_U UniversalLocalView),
                selectorReplicatorTupleTraj
                  ((solMURepl eta heta M κ₀ g₀ HP Kq R selectorInitX0 hfin hgateZ hgateU
                    h_chiReset h_chiGate h_kappa h_gain h_P) w) La (g₀ : ℝ) 0 i ^ 2) + 1))
    (init_succ :
      ∀ (w : ℕ)
        (La : SelectorReplicatorHaltLatchSol
          ((solMURepl eta heta M κ₀ g₀ HP Kq R selectorInitX0 hfin hgateZ hgateU
            h_chiReset h_chiGate h_kappa h_gain h_P) w)
          (fun _ : (Fin d_U → ℝ) => (0 : ℝ)) 0 R)
        (i : Fin (selectorDim d_U UniversalLocalView)),
          ((selectorReplicatorSphereInitQ d_U UniversalLocalView selectorInitX0
            w g₀ i.succ : ℚ) : ℝ) =
            2 * selectorReplicatorTupleTraj
              ((solMURepl eta heta M κ₀ g₀ HP Kq R selectorInitX0 hfin hgateZ hgateU
                h_chiReset h_chiGate h_kappa h_gain h_P) w) La (g₀ : ℝ) 0 i /
              ((∑ k : Fin (selectorDim d_U UniversalLocalView),
                selectorReplicatorTupleTraj
                  ((solMURepl eta heta M κ₀ g₀ HP Kq R selectorInitX0 hfin hgateZ hgateU
                    h_chiReset h_chiGate h_kappa h_gain h_P) w) La (g₀ : ℝ) 0 k ^ 2) + 1))
    (boxInputs : MUReplicatorBoxInputs eta heta M κ₀ g₀
      (solMURepl eta heta M κ₀ g₀ HP Kq R selectorInitX0 hfin hgateZ hgateU
        h_chiReset h_chiGate h_kappa h_gain h_P))
    (late : MUReplicatorLateStartHaltFacts
      (solMURepl eta heta M κ₀ g₀ HP Kq R selectorInitX0 hfin hgateZ hgateU
        h_chiReset h_chiGate h_kappa h_gain h_P)) :
    ∃ P : Ripple.BoundedUniversality.GPAC.PIVP ℚ,
      Nonempty (EventualThresholdSimulation P UniversalMachine.undecidableMachine) := by
  classical
  haveI : Nonempty UniversalLocalView := ⟨defaultLocalViewU⟩
  let sol : MUReplicatorSolFamily eta heta M κ₀ g₀ :=
    solMURepl eta heta M κ₀ g₀ HP Kq R selectorInitX0 hfin hgateZ hgateU
      h_chiReset h_chiGate h_kappa h_gain h_P
  have hforward_boxes : ∀ w,
      (∀ t : ℝ, 0 ≤ t →
        selectorMixTarget branchU (sol w).u (sol w).lam t haltCoordU ∈ Icc (0 : ℝ) 1) ∧
      (∀ t : ℝ, 0 ≤ t → (sol w).z t haltCoordU ≤ 1) ∧
      (∀ t : ℝ, 0 ≤ t → 0 ≤ (sol w).z t haltCoordU) := by
    intro w
    have hode : ∀ v : UniversalLocalView, ∀ t : ℝ, 0 ≤ t →
        HasDerivAt ((sol w).lam v)
          ((((1 + Real.cos t) / 2) ^ M * (κ₀ : ℝ)) *
              (1 / (Fintype.card UniversalLocalView : ℝ) - (sol w).lam v t)
            + (((1 + Real.sin t) / 2) ^ M *
                ((g₀ : ℝ) * Real.exp (bgpParams38.cα * t))) *
              (sol w).lam v t *
                (universalPval eta heta v ((sol w).u t)
                  - ∑ u : UniversalLocalView,
                      (sol w).lam u t * universalPval eta heta u ((sol w).u t))) t := by
      intro v t ht
      simpa [selectorSchedule] using
        (sol w).lam_hasDeriv v t (by simpa [selectorSchedule] using ht)
    have hsum : ∀ t : ℝ, 0 ≤ t →
        (∑ v : UniversalLocalView, (sol w).lam v t) = 1 :=
      replicator_sum_lam_eq_one
        (lam := fun v t => (sol w).lam v t)
        (P := fun v t => universalPval eta heta v ((sol w).u t))
        (cr := fun t => ((1 + Real.cos t) / 2) ^ M * (κ₀ : ℝ))
        (cg := fun t =>
          ((1 + Real.sin t) / 2) ^ M *
            ((g₀ : ℝ) * Real.exp (bgpParams38.cα * t)))
        boxInputs.hcr_cont boxInputs.hcg_cont
        (fun v => (sol w).cont_lam v)
        (boxInputs.hP_cont w) hode (boxInputs.hlam_sum0 w)
    have hlam_nonneg_forward :
        ∀ v : UniversalLocalView, ∀ t : ℝ, 0 ≤ t → 0 ≤ (sol w).lam v t :=
      replicator_lam_nonneg
        (lam := fun v t => (sol w).lam v t)
        (P := fun v t => universalPval eta heta v ((sol w).u t))
        (cr := fun t => ((1 + Real.cos t) / 2) ^ M * (κ₀ : ℝ))
        (cg := fun t =>
          ((1 + Real.sin t) / 2) ^ M *
            ((g₀ : ℝ) * Real.exp (bgpParams38.cα * t)))
        boxInputs.hcr_cont boxInputs.hcg_cont
        (fun v => (sol w).cont_lam v)
        (boxInputs.hP_cont w) boxInputs.hcr_nonneg hode
        (boxInputs.hlam_init_nonneg w)
    have hmix : ∀ t : ℝ, 0 ≤ t →
        selectorMixTarget branchU (sol w).u (sol w).lam t haltCoordU ∈ Icc (0 : ℝ) 1 := by
      intro t ht
      exact selectorMixTarget_haltCoord_mem_Icc_of_lam_sum_eq_one
        (sol w).u (sol w).lam t
        (fun v => hlam_nonneg_forward v t ht)
        (hsum t ht)
    have hzbox :=
      selector_replicator_flag_box_on_nonneg_repl (sol w)
        boxInputs.hcr_cont boxInputs.hcg_cont (boxInputs.hP_cont w)
        boxInputs.hcr_nonneg (boxInputs.hlam_sum0 w)
        (boxInputs.hlam_init_nonneg w) (boxInputs.hz0 w)
    exact ⟨hmix, hzbox.1, hzbox.2⟩
  have correct_halt_z :
      ∀ w, UniversalMachine.undecidableMachine.toDiscreteMachine.haltsOn w →
        ∃ T : ℝ, ∀ t ≥ T, 3 / 4 ≤ (sol w).z t haltCoordU ∧
          (sol w).z t haltCoordU ≤ 1 := by
    intro w hw
    have hwU : M_U.haltsOn w := by
      simpa using hw
    have hstart_cfg : ∀ j,
        |(sol w).z (selectorMUInterReadStart j) haltCoordU -
          stackMachineEncodingU.enc (late.cfg w (j + 1)) haltCoordU| ≤
            late.readStart.Bz_read w j := by
      intro j
      simpa [selectorMUInterReadStart, late.hcfg w (j + 1)] using
        late.readStart.hz_read_start w j
    have hhold :=
      solMURepl_settled_hhold_of_halts (sol w) w hwU (late.cfg w)
        (late.hcfg w) (late.readStart.Bz_read w)
        (late.δnext w) (late.holdPrefix w)
        (late.readStart.hBz_read_nonneg w) (late.hδnext_nonneg w)
        (late.hholdPrefix_nonneg w)
        (late.readStart.hBz_read_tendsto w) (late.hδnext w)
        hstart_cfg (late.hoff w) (late.hnextWrite w) (late.hfiniteHold w)
    obtain ⟨δhold, hhold_all, hδhold, hδhold_nonneg⟩ := hhold
    exact selector_correct_halt_endtoend_hold_repl_of_tendsto (sol w) w hwU
      (late.cfg w) (late.hcfg w)
      (late.readStart.Bz_read w) δhold hstart_cfg hhold_all
      (hforward_boxes w).2.1
      (late.readStart.hBz_read_tendsto w) hδhold
      (late.readStart.hBz_read_nonneg w) hδhold_nonneg
  have correct_nonhalt_z :
      ∀ w, ¬ UniversalMachine.undecidableMachine.toDiscreteMachine.haltsOn w →
        ∃ T : ℝ, ∀ t ≥ T, 0 ≤ (sol w).z t haltCoordU ∧
          (sol w).z t haltCoordU ≤ 1 / 4 := by
    intro w hw
    have hwU : ¬ M_U.haltsOn w := by
      simpa using hw
    have hstart_cfg : ∀ j,
        |(sol w).z (selectorMUInterReadStart j) haltCoordU -
          stackMachineEncodingU.enc (late.cfg w (j + 1)) haltCoordU| ≤
            late.readStart.Bz_read w j := by
      intro j
      simpa [selectorMUInterReadStart, late.hcfg w (j + 1)] using
        late.readStart.hz_read_start w j
    have hhold :=
      solMURepl_settled_hhold_of_nonhalts (sol w) w hwU (late.cfg w)
        (late.hcfg w) (late.readStart.Bz_read w) (late.δnext w)
        (late.readStart.hBz_read_nonneg w) (late.hδnext_nonneg w)
        (late.readStart.hBz_read_tendsto w) (late.hδnext w)
        hstart_cfg (late.hoff w) (late.hnextWrite w)
    exact selector_correct_nonhalt_endtoend_hold_repl_of_tendsto (sol w) w hwU
      (late.cfg w) (late.hcfg w)
      (late.readStart.Bz_read w)
      (selectorMUSelfHoldDelta (late.δnext w) (late.readStart.Bz_read w))
      hstart_cfg hhold.1 (hforward_boxes w).2.2
      (late.readStart.hBz_read_tendsto w) hhold.2.1
      (late.readStart.hBz_read_nonneg w) hhold.2.2
  exact main_assembled_mu_selector_zreadout_nolatch_repl_of_sol_init
    eta heta M κ₀ g₀ R selectorInitX0 init_presented sol
    (fun w => init_zero w (selector_replicator_zero_latch_solution (sol w) R))
    (fun w i => init_succ w (selector_replicator_zero_latch_solution (sol w) R) i)
    correct_halt_z correct_nonhalt_z

#print axioms solMUReplSettledEpsLam
#print axioms solMUReplSettledHaltEpsLam
#print axioms solMUReplHaltPreForwardResetIntegral
#print axioms solMUReplSettledRho
#print axioms solMUReplSettledHaltDelta
#print axioms solMUReplSettledHoldRadius
#print axioms solMURepl_settled_epsLam_tendsto_zero
#print axioms solMURepl_haltPreForwardResetIntegral_duhamel_tendsto_zero
#print axioms solMURepl_haltPreKreset_duhamel_tendsto_zero
#print axioms solMURepl_settled_haltEpsLam_tendsto_zero
#print axioms solMURepl_settled_hstart
#print axioms solMURepl_settled_hstart_haltOnly
#print axioms MUReplicatorSettledHaltFacts.hstart_haltOnly
#print axioms MUReplicatorLateStartReadStartResidual
#print axioms mu_replicator_late_start_read_start_of_settled_facts
#print axioms MUReplicatorLateStartHaltFacts
#print axioms bgp_MU_replicator_settled_late_start
#print axioms solMURepl_settled_hhold_of_halts
#print axioms halt_flag_target_const_cfg_succ_succ_of_nonhalts
#print axioms solMURepl_settled_hhold_of_nonhalts
#print axioms MUReplicatorSettledHaltFacts
#print axioms MUReplicatorSettledFacts.toHaltFacts
#print axioms bgp_MU_replicator_settled

end Ripple.BoundedUniversality.BGP
