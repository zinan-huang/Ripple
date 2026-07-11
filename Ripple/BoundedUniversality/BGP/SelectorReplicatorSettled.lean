import Ripple.BoundedUniversality.BGP.SelectorReplicatorDuhamel
import Ripple.BoundedUniversality.BGP.SelectorReplicatorHStart
import Ripple.BoundedUniversality.BGP.BGPParams38

/-!
Ripple.BoundedUniversality.BGP.SelectorReplicatorSettled
-------------------------------------

Foundational settled-window concentration estimates for the replicator selector.

This file is deliberately additive.  The window endpoints are parameters, so the
current `selectorMUWriteStartTime` wiring is not changed here.  The main loser
mass lemma proves settled-window concentration by prefix-instantiating the
existing ratio comparison from the select endpoint to each settled time and then
using the monotone gate mass to compare the explicit ratio radius with the
write-start radius.
-/

noncomputable section

open Filter
open scoped BigOperators Topology

namespace Ripple.BoundedUniversality.BGP

open Set MachineInstance

/-- Coefficient in the loser/winner ratio radius, before the gate-decay factor. -/
def selectorSettledRatioCoeff {V : Type} [Fintype V]
    (Lmin R0 Kreset : ℝ) : ℝ :=
  R0 + Kreset / ((Fintype.card V : ℝ) * Lmin)

/-- Explicit loser/winner ratio radius at endpoint `b`, measured from select endpoint `a`. -/
def selectorSettledRatioEps {V : Type} [Fintype V]
    (Lmin gap R0 Kreset : ℝ) (G : ℝ → ℝ) (a b : ℝ) : ℝ :=
  selectorSettledRatioCoeff (V := V) Lmin R0 Kreset *
    Real.exp (-gap * (G b - G a))

/-- Settled loser-mass radius obtained from the explicit ratio radius. -/
def epsLamSettled {V : Type} [Fintype V]
    (Lmin gap R0 Kreset : ℝ) (G : ℝ → ℝ) (selectStart writeStart : ℝ) : ℝ :=
  ((Fintype.card V : ℝ) - 1) *
    selectorSettledRatioEps (V := V) Lmin gap R0 Kreset G selectStart writeStart

/-- With the canonical floor `1 / |V|`, the settled radius has the closed form
`(|V|-1) * (R0+K) * exp(-gap*ΔG)`. -/
theorem epsLamSettled_card_inv {V : Type} [Fintype V] [Nonempty V]
    (gap R0 K : ℝ) (G : ℝ → ℝ) (a b : ℝ) :
    epsLamSettled (V := V) (1 / (Fintype.card V : ℝ)) gap R0 K G a b =
      ((Fintype.card V : ℝ) - 1) *
        ((R0 + K) * Real.exp (-(gap * (G b - G a)))) := by
  unfold epsLamSettled selectorSettledRatioEps selectorSettledRatioCoeff
  have hN : (Fintype.card V : ℝ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Fintype.card_pos_iff.mpr inferInstance)
  field_simp [hN]

/-- Write-start mixture radius obtained by multiplying loser mass by branch spread. -/
def epsmixPre {V : Type} [Fintype V]
    (Lmin gap R0 Kreset Rspread : ℝ) (G : ℝ → ℝ)
    (selectStart writeStart : ℝ) : ℝ :=
  Rspread * epsLamSettled (V := V) Lmin gap R0 Kreset G selectStart writeStart

private lemma selectorSettledRatioCoeff_nonneg {V : Type} [Fintype V] [Nonempty V]
    {Lmin R0 Kreset : ℝ}
    (hLmin_pos : 0 < Lmin) (hR0_nonneg : 0 ≤ R0) (hKreset_nonneg : 0 ≤ Kreset) :
    0 ≤ selectorSettledRatioCoeff (V := V) Lmin R0 Kreset := by
  have hcard_pos_nat : 0 < Fintype.card V := Fintype.card_pos_iff.mpr inferInstance
  have hcard_pos : 0 < (Fintype.card V : ℝ) := by exact_mod_cast hcard_pos_nat
  have hden_pos : 0 < (Fintype.card V : ℝ) * Lmin := mul_pos hcard_pos hLmin_pos
  exact add_nonneg hR0_nonneg (div_nonneg hKreset_nonneg hden_pos.le)

private lemma card_sub_one_nonneg {V : Type} [Fintype V] [Nonempty V] :
    0 ≤ (Fintype.card V : ℝ) - 1 := by
  have hcard_pos_nat : 0 < Fintype.card V := Fintype.card_pos_iff.mpr inferInstance
  have hcard_one : (1 : ℝ) ≤ Fintype.card V := by exact_mod_cast hcard_pos_nat
  linarith

/-- Duhamel form of settled loser-mass radius decay.

The reset coefficient `Kreset` is not required to be bounded.  The reset
contribution is carried only through the satisfiable residual
`Kreset j * exp (-gap j * ΔG_pre j) → 0`.  Algebraically the radius is
`(card V - 1) * (R0 j * E_j + D_j / (card V * Lmin j))`, where
`E_j = exp (-gap j * ΔG_pre j)` and `D_j = Kreset j * E_j`. -/
theorem epsLamSettled_tendsto_zero_duhamel {V : Type} [Fintype V] [Nonempty V]
    {Lmin gap R0 Kreset deltaG : ℕ → ℝ} {gap0 Lmin0 R0max : ℝ}
    (hgap0 : 0 < gap0)
    (hgap_lb : ∀ᶠ j in atTop, gap0 ≤ gap j)
    (hdeltaG : Tendsto deltaG atTop atTop)
    (hLmin0_pos : 0 < Lmin0)
    (hLmin_lb : ∀ᶠ j in atTop, Lmin0 ≤ Lmin j)
    (hR0_nonneg : ∀ᶠ j in atTop, 0 ≤ R0 j)
    (hR0_bound : ∀ᶠ j in atTop, R0 j ≤ R0max)
    (hDuhamel_pre : Tendsto
      (fun j => Kreset j * Real.exp (-gap j * deltaG j)) atTop (𝓝 0)) :
    Tendsto
      (fun j =>
        ((Fintype.card V : ℝ) - 1) *
          (selectorSettledRatioCoeff (V := V) (Lmin j) (R0 j) (Kreset j) *
            Real.exp (-gap j * deltaG j))) atTop (𝓝 0) := by
  let E : ℕ → ℝ := fun j => Real.exp (-gap j * deltaG j)
  let N : ℝ := Fintype.card V
  have hN_nat : 0 < Fintype.card V := Fintype.card_pos_iff.mpr inferInstance
  have hN_pos : 0 < N := Nat.cast_pos.mpr hN_nat
  have hNm1_nonneg : 0 ≤ N - 1 := by
    have hN_ge_one_nat : 1 ≤ Fintype.card V := Nat.succ_le_of_lt hN_nat
    have hN_ge_one : (1 : ℝ) ≤ N := Nat.one_le_cast.mpr hN_ge_one_nat
    linarith
  have hgap0_deltaG : Tendsto (fun j => gap0 * deltaG j) atTop atTop :=
    hdeltaG.const_mul_atTop hgap0
  have hgap_deltaG : Tendsto (fun j => gap j * deltaG j) atTop atTop := by
    refine tendsto_atTop_mono' atTop ?_ hgap0_deltaG
    filter_upwards [hgap_lb, hdeltaG.eventually_ge_atTop 0] with j hgapj hdeltaG_nonneg
    exact mul_le_mul_of_nonneg_right hgapj hdeltaG_nonneg
  have hdecay_paren :
      Tendsto (fun j => Real.exp (-(gap j * deltaG j))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hgap_deltaG)
  have hdecay : Tendsto E atTop (𝓝 0) := by
    show Tendsto (fun j => Real.exp (-gap j * deltaG j)) atTop (𝓝 0)
    simpa only [neg_mul] using hdecay_paren
  have hR0term :
      Tendsto (fun j => R0 j * E j) atTop (𝓝 0) :=
    bdd_le_mul_tendsto_zero hR0_nonneg hR0_bound hdecay
  have hresetFactor_nonneg :
      ∀ᶠ j in atTop, 0 ≤ 1 / (N * Lmin j) := by
    filter_upwards [hLmin_lb] with j hLmin
    exact one_div_nonneg.mpr
      (mul_nonneg hN_pos.le (le_trans hLmin0_pos.le hLmin))
  have hresetFactor_bound :
      ∀ᶠ j in atTop, 1 / (N * Lmin j) ≤ 1 / (N * Lmin0) := by
    filter_upwards [hLmin_lb] with j hLmin
    have hden_pos : 0 < N * Lmin0 := mul_pos hN_pos hLmin0_pos
    have hden_le : N * Lmin0 ≤ N * Lmin j :=
      mul_le_mul_of_nonneg_left hLmin hN_pos.le
    exact one_div_le_one_div_of_le hden_pos hden_le
  have hDterm_raw :
      Tendsto
        (fun j => (1 / (N * Lmin j)) *
          (Kreset j * Real.exp (-gap j * deltaG j))) atTop (𝓝 0) :=
    bdd_le_mul_tendsto_zero hresetFactor_nonneg hresetFactor_bound hDuhamel_pre
  have hDterm :
      Tendsto
        (fun j => (Kreset j * Real.exp (-gap j * deltaG j)) / (N * Lmin j))
        atTop (𝓝 0) := by
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hDterm_raw
  have hbracket :
      Tendsto
        (fun j =>
          R0 j * E j + (Kreset j * Real.exp (-gap j * deltaG j)) / (N * Lmin j))
        atTop (𝓝 0) := by
    simpa [E] using hR0term.add hDterm
  have hprod :
      Tendsto
        (fun j =>
          (N - 1) *
            (R0 j * E j + (Kreset j * Real.exp (-gap j * deltaG j)) / (N * Lmin j)))
        atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hbracket
  refine hprod.congr' ?_
  filter_upwards [] with j
  dsimp [selectorSettledRatioCoeff, E, N]
  ring

/-- Duhamel form of write-start mixture radius decay.  This is just the
settled loser-mass Duhamel radius multiplied by an eventually bounded branch
spread. -/
theorem epsmixPre_tendsto_zero_duhamel {V : Type} [Fintype V] [Nonempty V]
    {Lmin gap R0 Kreset Rspread deltaG : ℕ → ℝ} {gap0 Lmin0 R0max Rmax : ℝ}
    (hgap0 : 0 < gap0)
    (hgap_lb : ∀ᶠ j in atTop, gap0 ≤ gap j)
    (hdeltaG : Tendsto deltaG atTop atTop)
    (hLmin0_pos : 0 < Lmin0)
    (hLmin_lb : ∀ᶠ j in atTop, Lmin0 ≤ Lmin j)
    (hR0_nonneg : ∀ᶠ j in atTop, 0 ≤ R0 j)
    (hR0_bound : ∀ᶠ j in atTop, R0 j ≤ R0max)
    (hRspread_nonneg : ∀ᶠ j in atTop, 0 ≤ Rspread j)
    (hRspread_bound : ∀ᶠ j in atTop, Rspread j ≤ Rmax)
    (hDuhamel_pre : Tendsto
      (fun j => Kreset j * Real.exp (-gap j * deltaG j)) atTop (𝓝 0)) :
    Tendsto
      (fun j =>
        Rspread j *
          (((Fintype.card V : ℝ) - 1) *
            (selectorSettledRatioCoeff (V := V) (Lmin j) (R0 j) (Kreset j) *
              Real.exp (-gap j * deltaG j)))) atTop (𝓝 0) := by
  have hLam :=
    epsLamSettled_tendsto_zero_duhamel (V := V)
      (Lmin := Lmin) (gap := gap) (R0 := R0) (Kreset := Kreset)
      (deltaG := deltaG) hgap0 hgap_lb hdeltaG hLmin0_pos hLmin_lb
      hR0_nonneg hR0_bound hDuhamel_pre
  exact bdd_le_mul_tendsto_zero hRspread_nonneg hRspread_bound hLam

/-- Concrete prefix settled loser-mass radius decay for `solMURepl`.

The Duhamel residual is discharged inside this theorem by identifying `Kreset`
with the actual forward reset integral over `[π/6,π/2]` and applying
`solMURepl_preKreset_duhamel_tendsto_zero`. -/
theorem solMURepl_epsLamSettled_pre_tendsto_zero_duhamel
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    {cfg : ℕ → ℕ → UConf}
    (inputs : SelectorReplicatorConcInputs sol cfg) (w : ℕ)
    (hg₀ : 0 < (g₀ : ℝ))
    {Kreset : ℕ → ℝ} {gap0 Lmin0 R0max Cratio : ℝ}
    (hgap0 : 0 < gap0)
    (hgap_lb : ∀ᶠ j in atTop, gap0 ≤ inputs.gap w j)
    (hLmin0_pos : 0 < Lmin0)
    (hLmin_lb : ∀ᶠ j in atTop, Lmin0 ≤ inputs.Lmin w j)
    (hR0_nonneg : ∀ᶠ j in atTop, 0 ≤ inputs.R0 w j)
    (hR0_bound : ∀ᶠ j in atTop, inputs.R0 w j ≤ R0max)
    (hKreset_eq : ∀ j, Kreset j = solMUReplPreForwardResetIntegral inputs w j)
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
        epsLamSettled (V := UniversalLocalView)
          (inputs.Lmin w j) (inputs.gap w j) (inputs.R0 w j) (Kreset j)
          (sol w).G (selectorMUWriteStartTime j) (selectorMUWriteHoldTime j))
      atTop (𝓝 0) := by
  haveI : Nonempty UniversalLocalView := ⟨defaultLocalViewU⟩
  have hDuhamel_pre :
      Tendsto
        (fun j =>
          Kreset j *
            Real.exp
              (-inputs.gap w j *
                ((sol w).G (selectorMUWriteHoldTime j)
                  - (sol w).G (selectorMUWriteStartTime j))))
        atTop (𝓝 0) :=
    by
      simpa [neg_mul] using
        solMURepl_preKreset_duhamel_tendsto_zero
          (inputs := inputs) (w := w) hgap0 hgap_lb hKreset_eq
          hκ₀_nonneg hCratio_nonneg hratio_bound
  have hcore :=
    epsLamSettled_tendsto_zero_duhamel (V := UniversalLocalView)
      (Lmin := fun j => inputs.Lmin w j)
      (gap := fun j => inputs.gap w j)
      (R0 := fun j => inputs.R0 w j)
      (Kreset := Kreset)
      (deltaG := fun j =>
        (sol w).G (selectorMUWriteHoldTime j)
          - (sol w).G (selectorMUWriteStartTime j))
      hgap0 hgap_lb (solMURepl_deltaG_pre_tendsto_atTop sol hg₀ w)
      hLmin0_pos hLmin_lb hR0_nonneg hR0_bound hDuhamel_pre
  simpa [epsLamSettled, selectorSettledRatioEps] using hcore

/-- Concrete prefix write-start mix-radius decay for `solMURepl`, routed through
the Duhamel residual rather than a bounded reset coefficient. -/
theorem solMURepl_epsmixPre_tendsto_zero_duhamel
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    {cfg : ℕ → ℕ → UConf}
    (inputs : SelectorReplicatorConcInputs sol cfg) (w : ℕ)
    (hg₀ : 0 < (g₀ : ℝ))
    {Kreset Rspread : ℕ → ℝ} {gap0 Lmin0 R0max Rmax Cratio : ℝ}
    (hgap0 : 0 < gap0)
    (hgap_lb : ∀ᶠ j in atTop, gap0 ≤ inputs.gap w j)
    (hLmin0_pos : 0 < Lmin0)
    (hLmin_lb : ∀ᶠ j in atTop, Lmin0 ≤ inputs.Lmin w j)
    (hR0_nonneg : ∀ᶠ j in atTop, 0 ≤ inputs.R0 w j)
    (hR0_bound : ∀ᶠ j in atTop, inputs.R0 w j ≤ R0max)
    (hRspread_nonneg : ∀ᶠ j in atTop, 0 ≤ Rspread j)
    (hRspread_bound : ∀ᶠ j in atTop, Rspread j ≤ Rmax)
    (hKreset_eq : ∀ j, Kreset j = solMUReplPreForwardResetIntegral inputs w j)
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
        epsmixPre (V := UniversalLocalView)
          (inputs.Lmin w j) (inputs.gap w j) (inputs.R0 w j) (Kreset j)
          (Rspread j) (sol w).G (selectorMUWriteStartTime j) (selectorMUWriteHoldTime j))
      atTop (𝓝 0) := by
  haveI : Nonempty UniversalLocalView := ⟨defaultLocalViewU⟩
  have hDuhamel_pre :
      Tendsto
        (fun j =>
          Kreset j *
            Real.exp
              (-inputs.gap w j *
                ((sol w).G (selectorMUWriteHoldTime j)
                  - (sol w).G (selectorMUWriteStartTime j))))
        atTop (𝓝 0) :=
    by
      simpa [neg_mul] using
        solMURepl_preKreset_duhamel_tendsto_zero
          (inputs := inputs) (w := w) hgap0 hgap_lb hKreset_eq
          hκ₀_nonneg hCratio_nonneg hratio_bound
  have hcore :=
    epsmixPre_tendsto_zero_duhamel (V := UniversalLocalView)
      (Lmin := fun j => inputs.Lmin w j)
      (gap := fun j => inputs.gap w j)
      (R0 := fun j => inputs.R0 w j)
      (Kreset := Kreset)
      (Rspread := Rspread)
      (deltaG := fun j =>
        (sol w).G (selectorMUWriteHoldTime j)
          - (sol w).G (selectorMUWriteStartTime j))
      hgap0 hgap_lb (solMURepl_deltaG_pre_tendsto_atTop sol hg₀ w)
      hLmin0_pos hLmin_lb hR0_nonneg hR0_bound
      hRspread_nonneg hRspread_bound hDuhamel_pre
  simpa [epsmixPre, epsLamSettled, selectorSettledRatioEps] using hcore

/-- Settled-window loser mass bound.

For each `t ∈ [writeStart, readStart]`, the proof prefix-instantiates
`replicator_ratio_bound` on `[selectStart,t]`.  The final comparison with the
write-start radius uses only monotonicity of the accumulated gate mass and a
single prefix reset bound, not a carried settled-window concentration
hypothesis. -/
theorem loser_mass_small_on_settled_window
    {d B : ℕ} {V : Type} [Fintype V] [DecidableEq V] [Nonempty V]
    {p : DynGateParams} {sched : PhaseSchedule} {branch : V → BranchData d B}
    {chiReset chiGate kappa gain : ℝ → ℝ} {readoutP : V → (Fin d → ℝ) → ℝ}
    (sol : SelectorReplicatorDynSol d B V p sched branch
      chiReset chiGate kappa gain readoutP)
    (vstar : V) {selectStart writeStart readStart Lmin gap R0 Kreset : ℝ}
    (hselect_write : selectStart ≤ writeStart)
    (hwrite_read : writeStart ≤ readStart)
    (hLmin_pos : 0 < Lmin)
    (hgap_nonneg : 0 ≤ gap)
    (hR0_nonneg : 0 ≤ R0)
    (hKreset_nonneg : 0 ≤ Kreset)
    (hdom : ∀ t ∈ Icc selectStart readStart, t ∈ sched.domain)
    (hcr_cont : Continuous fun t : ℝ => chiReset t * kappa t)
    (hqL : ∀ t ∈ Icc selectStart readStart, Lmin ≤ sol.lam vstar t)
    (hlam_nonneg_Icc : ∀ w : V, ∀ t ∈ Icc selectStart readStart, 0 ≤ sol.lam w t)
    (hsum : ∀ t ∈ Icc selectStart readStart, (∑ w : V, sol.lam w t) = 1)
    (hcr_nonneg : ∀ t ∈ Ico selectStart readStart, 0 ≤ chiReset t * kappa t)
    (hcg_nonneg : ∀ t ∈ Ico selectStart readStart, 0 ≤ chiGate t * gain t)
    (hgap : ∀ v : V, v ≠ vstar → ∀ t ∈ Ico selectStart readStart,
      readoutP v (sol.u t) - readoutP vstar (sol.u t) ≤ -gap)
    (hRa : ∀ v : V, v ≠ vstar → sol.lam v selectStart / sol.lam vstar selectStart ≤ R0)
    (hKreset_prefix : ∀ t ∈ Icc writeStart readStart,
      (∫ s in selectStart..t,
        Real.exp (gap * (sol.G s - sol.G selectStart)) * (chiReset s * kappa s)) ≤ Kreset)
    (hG_mono_from_write : ∀ t ∈ Icc writeStart readStart,
      sol.G writeStart - sol.G selectStart ≤ sol.G t - sol.G selectStart) :
    ∀ t ∈ Icc writeStart readStart,
      (Finset.univ.filter (fun v : V => v ≠ vstar)).sum (fun v => sol.lam v t)
        ≤ epsLamSettled (V := V) Lmin gap R0 Kreset sol.G selectStart writeStart := by
  intro t ht
  have hselect_t : selectStart ≤ t := le_trans hselect_write ht.1
  have ht_big : t ∈ Icc selectStart readStart := ⟨hselect_t, ht.2⟩
  let ratioEps :=
    selectorSettledRatioEps (V := V) Lmin gap R0 Kreset sol.G selectStart writeStart
  have hcoeff_nonneg :
      0 ≤ selectorSettledRatioCoeff (V := V) Lmin R0 Kreset :=
    selectorSettledRatioCoeff_nonneg hLmin_pos hR0_nonneg hKreset_nonneg
  have hexp_le :
      Real.exp (-gap * (sol.G t - sol.G selectStart)) ≤
        Real.exp (-gap * (sol.G writeStart - sol.G selectStart)) := by
    refine Real.exp_le_exp.mpr ?_
    have hmul := mul_le_mul_of_nonneg_left (hG_mono_from_write t ht) hgap_nonneg
    nlinarith
  have hratio :
      ∀ v : V, v ≠ vstar → sol.lam v t / sol.lam vstar t ≤ ratioEps := by
    intro v hv
    have hraw :=
      replicator_ratio_bound
        (lam := sol.lam)
        (P := fun v t => readoutP v (sol.u t))
        (cr := fun t => chiReset t * kappa t)
        (cg := fun t => chiGate t * gain t)
        (G := sol.G)
        (vstar := vstar) (v := v)
        (a := selectStart) (b := t)
        (Lmin := Lmin) (gap := gap) (R0 := R0) (Kreset := Kreset)
        hselect_t hLmin_pos sol.cont_G hcr_cont
        (fun w => (sol.cont_lam w).continuousOn)
        (fun w s hs => by
          have hs_big : s ∈ Icc selectStart readStart :=
            ⟨hs.1, le_trans (le_of_lt hs.2) ht.2⟩
          simpa [mul_assoc] using sol.lam_hasDeriv w s (hdom s hs_big))
        (fun s hs => by
          have hs_big : s ∈ Icc selectStart readStart :=
            ⟨hs.1, le_trans (le_of_lt hs.2) ht.2⟩
          exact (sol.G_hasDeriv s (hdom s hs_big)).hasDerivWithinAt)
        (fun s hs => hqL s ⟨hs.1, le_trans hs.2 ht.2⟩)
        (fun w s hs => hlam_nonneg_Icc w s ⟨hs.1, le_trans hs.2 ht.2⟩)
        (fun s hs => hcr_nonneg s ⟨hs.1, lt_of_lt_of_le hs.2 ht.2⟩)
        (fun s hs => hcg_nonneg s ⟨hs.1, lt_of_lt_of_le hs.2 ht.2⟩)
        (fun s hs => hgap v hv s ⟨hs.1, lt_of_lt_of_le hs.2 ht.2⟩)
        (hRa v hv)
        (hKreset_prefix t ht)
    exact le_trans hraw (mul_le_mul_of_nonneg_left hexp_le hcoeff_nonneg)
  have hq_pos_t : 0 < sol.lam vstar t := lt_of_lt_of_le hLmin_pos (hqL t ht_big)
  have hloser :=
    replicator_loser_mass_bound
      (lam := sol.lam) (vstar := vstar)
      (b := t) (eps := ratioEps)
      (hsum t ht_big)
      (fun w => hlam_nonneg_Icc w t ht_big)
      hq_pos_t hratio
  simpa [ratioEps, epsLamSettled, selectorSettledRatioEps] using hloser

/-- Endpoint `εmix` at write start, obtained by re-instantiating the existing
replicator mix-close lemma on the select-to-write prefix. -/
theorem epsmix_at_writestart
    {d B : ℕ} {V : Type} [Fintype V] [DecidableEq V] [Nonempty V]
    {p : DynGateParams} {sched : PhaseSchedule} {branch : V → BranchData d B}
    {chiReset chiGate kappa gain : ℝ → ℝ} {readoutP : V → (Fin d → ℝ) → ℝ}
    (sol : SelectorReplicatorDynSol d B V p sched branch
      chiReset chiGate kappa gain readoutP)
    (vstar : V) (i : Fin d) {selectStart writeStart Lmin gap R0 Kreset Rspread : ℝ}
    (hselect_write : selectStart ≤ writeStart)
    (hLmin_pos : 0 < Lmin)
    (hdom : ∀ t ∈ Icc selectStart writeStart, t ∈ sched.domain)
    (hcr_cont : Continuous fun t : ℝ => chiReset t * kappa t)
    (hqL : ∀ t ∈ Icc selectStart writeStart, Lmin ≤ sol.lam vstar t)
    (hlam_nonneg_Icc : ∀ w : V, ∀ t ∈ Icc selectStart writeStart, 0 ≤ sol.lam w t)
    (hsum_write : (∑ w : V, sol.lam w writeStart) = 1)
    (hcr_nonneg : ∀ t ∈ Ico selectStart writeStart, 0 ≤ chiReset t * kappa t)
    (hcg_nonneg : ∀ t ∈ Ico selectStart writeStart, 0 ≤ chiGate t * gain t)
    (hgap : ∀ v : V, v ≠ vstar → ∀ t ∈ Ico selectStart writeStart,
      readoutP v (sol.u t) - readoutP vstar (sol.u t) ≤ -gap)
    (hRa : ∀ v : V, v ≠ vstar →
      sol.lam v selectStart / sol.lam vstar selectStart ≤ R0)
    (hKreset : (∫ t in selectStart..writeStart,
      Real.exp (gap * (sol.G t - sol.G selectStart)) * (chiReset t * kappa t)) ≤ Kreset)
    (hRspread_nonneg : 0 ≤ Rspread)
    (hspread : ∀ v : V, v ≠ vstar →
      |BranchData.evalBranch (branch v) (sol.u writeStart) i
        - BranchData.evalBranch (branch vstar) (sol.u writeStart) i| ≤ Rspread) :
    |selectorMixTarget branch sol.u sol.lam writeStart i
        - BranchData.evalBranch (branch vstar) (sol.u writeStart) i| ≤
      epsmixPre (V := V) Lmin gap R0 Kreset Rspread sol.G selectStart writeStart := by
  have hcore :=
    selector_replicator_mix_close_of_concentration
      (sol := sol) (vstar := vstar) (i := i)
      (a := selectStart) (b := writeStart)
      (Lmin := Lmin) (gap := gap) (R0 := R0)
      (Kreset := Kreset) (Rspread := Rspread)
      hselect_write hLmin_pos hdom hcr_cont hqL hlam_nonneg_Icc hsum_write
      hcr_nonneg hcg_nonneg hgap hRa hKreset hRspread_nonneg hspread
  simpa [epsmixPre, epsLamSettled, selectorSettledRatioEps, selectorSettledRatioCoeff,
    mul_assoc] using hcore

/-- Pure algebraic settled-window mix target estimate.

The split is direct:
`mix(t)-enc(step c) = (mix(t)-evalBranch(vstar)(u t))
  + (evalBranch(vstar)(u t)-enc(step c))`.
The first term is `Rspread * loser_mass(t)`, and the second is the branch
diagonal estimate fed by the write-start tube plus the settled `u` drift. -/
theorem mixTarget_near_next_on_settled_window
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : SelectorReplicatorDynSol d_U B_U UniversalLocalView bgpParams38 selectorSchedule
      branchU
      (fun t => ((1 + Real.cos t) / 2) ^ Mcy)
      (fun t => ((1 + Real.sin t) / 2) ^ Mcy)
      (fun _ => (κ₀ : ℝ))
      (fun t => (g₀ : ℝ) * Real.exp (bgpParams38.cα * t))
      (universalPval eta heta))
    (cfg : ℕ → UConf) (writeStart readStart : ℕ → ℝ)
    (epsLamSettled Rspread ρu δuSettled : ℕ → ℝ) {mult : ℝ}
    (hmult0 : 0 ≤ mult)
    (hmultbound : ∀ j, ∀ i,
      stackMachineEncodingU.coordMultiplier (cfg j) i ≤ mult)
    (hsum : ∀ j, ∀ t ∈ Icc (writeStart j) (readStart j),
      (∑ v : UniversalLocalView, sol.lam v t) = 1)
    (hlam_nonneg : ∀ j, ∀ t ∈ Icc (writeStart j) (readStart j),
      ∀ v : UniversalLocalView, 0 ≤ sol.lam v t)
    (hloser : ∀ j, ∀ t ∈ Icc (writeStart j) (readStart j),
      (Finset.univ.filter (fun v : UniversalLocalView => v ≠ localViewU (cfg j))).sum
        (fun v => sol.lam v t) ≤ epsLamSettled j)
    (hRspread_nonneg : ∀ j, 0 ≤ Rspread j)
    (hspread : ∀ j, ∀ t ∈ Icc (writeStart j) (readStart j), ∀ i,
      ∀ v : UniversalLocalView, v ≠ localViewU (cfg j) →
        |BranchData.evalBranch (branchU v) (sol.u t) i
          - BranchData.evalBranch (branchU (localViewU (cfg j))) (sol.u t) i|
            ≤ Rspread j)
    (hutube_write : ∀ j, ∀ i,
      |sol.u (writeStart j) i - stackMachineEncodingU.enc (cfg j) i| ≤ ρu j)
    (hudrift : ∀ j, ∀ t ∈ Icc (writeStart j) (readStart j), ∀ i,
      |sol.u t i - sol.u (writeStart j) i| ≤ δuSettled j) :
    ∀ j, ∀ t ∈ Icc (writeStart j) (readStart j), ∀ i,
      |selectorMixTarget branchU sol.u sol.lam t i
        - stackMachineEncodingU.enc (M_U.step (cfg j)) i| ≤
          Rspread j * epsLamSettled j + mult * (ρu j + δuSettled j) := by
  intro j t ht i
  let vstar : UniversalLocalView := localViewU (cfg j)
  have hmix_raw :=
    replicator_mix_error_of_loser_mass
      (vstar := vstar)
      (lam := fun v : UniversalLocalView => sol.lam v t)
      (A := fun v : UniversalLocalView => BranchData.evalBranch (branchU v) (sol.u t) i)
      (Rspread := Rspread j) (loserBound := epsLamSettled j)
      (hRspread_nonneg j)
      (hsum j t ht)
      (fun v => hlam_nonneg j t ht v)
      (hspread j t ht i)
      (by simpa [vstar] using hloser j t ht)
  have hmix :
      |selectorMixTarget branchU sol.u sol.lam t i
        - BranchData.evalBranch (branchU vstar) (sol.u t) i|
          ≤ Rspread j * epsLamSettled j := by
    simpa [selectorMixTarget, selectorF, vstar] using hmix_raw
  have hut :
      |sol.u t i - stackMachineEncodingU.enc (cfg j) i| ≤ ρu j + δuSettled j := by
    calc
      |sol.u t i - stackMachineEncodingU.enc (cfg j) i|
          ≤ |sol.u t i - sol.u (writeStart j) i|
            + |sol.u (writeStart j) i - stackMachineEncodingU.enc (cfg j) i| :=
              abs_sub_le _ _ _
      _ ≤ δuSettled j + ρu j := add_le_add (hudrift j t ht i) (hutube_write j i)
      _ = ρu j + δuSettled j := by ring
  have hdiag_raw :=
    selector_MU_hdiag (cfg j) (sol.u t) (hmultbound j) i
  have hdiag :
      |BranchData.evalBranch (branchU vstar) (sol.u t) i
        - stackMachineEncodingU.enc (M_U.step (cfg j)) i|
          ≤ mult * (ρu j + δuSettled j) := by
    calc
      |BranchData.evalBranch (branchU vstar) (sol.u t) i
        - stackMachineEncodingU.enc (M_U.step (cfg j)) i|
          ≤ mult * |sol.u t i - stackMachineEncodingU.enc (cfg j) i| := by
            simpa [vstar] using hdiag_raw
      _ ≤ mult * (ρu j + δuSettled j) :=
            mul_le_mul_of_nonneg_left hut hmult0
  calc
    |selectorMixTarget branchU sol.u sol.lam t i
        - stackMachineEncodingU.enc (M_U.step (cfg j)) i|
        ≤ |selectorMixTarget branchU sol.u sol.lam t i
            - BranchData.evalBranch (branchU vstar) (sol.u t) i|
          + |BranchData.evalBranch (branchU vstar) (sol.u t) i
            - stackMachineEncodingU.enc (M_U.step (cfg j)) i| := abs_sub_le _ _ _
    _ ≤ Rspread j * epsLamSettled j + mult * (ρu j + δuSettled j) :=
      add_le_add hmix hdiag

/-- A charged class that excludes the winner has mass bounded by total
outside-winner mass. -/
theorem chargedMass_le_outside_winner
    {V : Type} [Fintype V] [DecidableEq V]
    (charged : V → Prop) [DecidablePred charged]
    (Λ : V → ℝ) (vstar : V)
    (hstar_not_charged : ¬ charged vstar)
    (hΛ_nonneg : ∀ v : V, 0 ≤ Λ v) :
    (Finset.univ.filter charged).sum Λ ≤
      (Finset.univ.filter (fun v : V => v ≠ vstar)).sum Λ := by
  classical
  refine Finset.sum_le_sum_of_subset_of_nonneg ?hsubset ?hnonneg
  · intro v hv
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ v, fun hvstar =>
        hstar_not_charged (by simpa [hvstar] using (Finset.mem_filter.mp hv).2)⟩
  · intro v _hvoutside _hvcharged
    exact hΛ_nonneg v

/-- Same charged-class bridge, composed with an outside-winner mass bound. -/
theorem chargedMass_le_loser_bound
    {V : Type} [Fintype V] [DecidableEq V]
    (charged : V → Prop) [DecidablePred charged]
    (Λ : V → ℝ) (vstar : V) {eps : ℝ}
    (hstar_not_charged : ¬ charged vstar)
    (hΛ_nonneg : ∀ v : V, 0 ≤ Λ v)
    (hloser :
      (Finset.univ.filter (fun v : V => v ≠ vstar)).sum Λ ≤ eps) :
    (Finset.univ.filter charged).sum Λ ≤ eps :=
  le_trans
    (chargedMass_le_outside_winner charged Λ vstar hstar_not_charged hΛ_nonneg)
    hloser

/-- A one-time card-radius ratio bound from a winner floor and simplex. -/
theorem ratio_at_floor_card_bound
    {V : Type} [Fintype V] [Nonempty V]
    (Λ : V → ℝ) (vstar : V)
    (hsum : (∑ v : V, Λ v) = 1)
    (hΛ_nonneg : ∀ v : V, 0 ≤ Λ v)
    (hfloor : 1 / (Fintype.card V : ℝ) ≤ Λ vstar) :
    ∀ v : V, v ≠ vstar →
      Λ v / Λ vstar ≤ (Fintype.card V : ℝ) := by
  intro v _hv
  have hcard_pos_nat : 0 < Fintype.card V := Fintype.card_pos_iff.mpr inferInstance
  have hcard_pos : 0 < (Fintype.card V : ℝ) := by exact_mod_cast hcard_pos_nat
  have hfloor_pos : 0 < 1 / (Fintype.card V : ℝ) := one_div_pos.mpr hcard_pos
  have hvstar_pos : 0 < Λ vstar := lt_of_lt_of_le hfloor_pos hfloor
  have hv_le_one : Λ v ≤ 1 := by
    have hle_sum : Λ v ≤ ∑ w : V, Λ w :=
      Finset.single_le_sum (fun w _hw => hΛ_nonneg w) (Finset.mem_univ v)
    simpa [hsum] using hle_sum
  calc
    Λ v / Λ vstar ≤ 1 / Λ vstar :=
      div_le_div_of_nonneg_right hv_le_one hvstar_pos.le
    _ ≤ 1 / (1 / (Fintype.card V : ℝ)) :=
      one_div_le_one_div_of_le hfloor_pos hfloor
    _ = (Fintype.card V : ℝ) := by
      field_simp [ne_of_gt hcard_pos]

/-- Pointwise prefix wrapper around `loser_mass_small_on_settled_window`.

For every `t ∈ [a,b]`, this instantiates the settled-window theorem on the
single endpoint interval `[a,t]` by taking `writeStart = readStart = t`. -/
theorem loser_mass_small_on_prefix_pointwise
    {d B : ℕ} {V : Type} [Fintype V] [DecidableEq V] [Nonempty V]
    {p : DynGateParams} {sched : PhaseSchedule} {branch : V → BranchData d B}
    {chiReset chiGate kappa gain : ℝ → ℝ} {readoutP : V → (Fin d → ℝ) → ℝ}
    (sol : SelectorReplicatorDynSol d B V p sched branch
      chiReset chiGate kappa gain readoutP)
    (vstar : V) {a b Lmin gap R0 : ℝ}
    (hLmin_pos : 0 < Lmin)
    (hgap_nonneg : 0 ≤ gap)
    (hR0_nonneg : 0 ≤ R0)
    (hdom : ∀ t ∈ Icc a b, t ∈ sched.domain)
    (hcr_cont : Continuous fun t : ℝ => chiReset t * kappa t)
    (hqL : ∀ t ∈ Icc a b, Lmin ≤ sol.lam vstar t)
    (hlam_nonneg_Icc : ∀ w : V, ∀ t ∈ Icc a b, 0 ≤ sol.lam w t)
    (hsum : ∀ t ∈ Icc a b, (∑ w : V, sol.lam w t) = 1)
    (hcr_nonneg : ∀ t ∈ Icc a b, 0 ≤ chiReset t * kappa t)
    (hcg_nonneg : ∀ t ∈ Icc a b, 0 ≤ chiGate t * gain t)
    (hgap : ∀ v : V, v ≠ vstar → ∀ t ∈ Ico a b,
      readoutP v (sol.u t) - readoutP vstar (sol.u t) ≤ -gap)
    (hRa : ∀ v : V, v ≠ vstar → sol.lam v a / sol.lam vstar a ≤ R0) :
    ∀ t ∈ Icc a b,
      (Finset.univ.filter (fun v : V => v ≠ vstar)).sum (fun v => sol.lam v t)
        ≤ epsLamSettled (V := V) Lmin gap R0
          (∫ s in a..t,
            Real.exp (gap * (sol.G s - sol.G a)) * (chiReset s * kappa s))
          sol.G a t := by
  intro t ht
  let Kt : ℝ :=
    ∫ s in a..t,
      Real.exp (gap * (sol.G s - sol.G a)) * (chiReset s * kappa s)
  have hKt_nonneg : 0 ≤ Kt := by
    dsimp [Kt]
    apply intervalIntegral.integral_nonneg ht.1
    intro s hs
    exact
      mul_nonneg (Real.exp_pos _).le
        (hcr_nonneg s ⟨hs.1, le_trans hs.2 ht.2⟩)
  have h :=
    loser_mass_small_on_settled_window
      (sol := sol) (vstar := vstar)
      (selectStart := a) (writeStart := t) (readStart := t)
      (Lmin := Lmin) (gap := gap) (R0 := R0) (Kreset := Kt)
      ht.1 (le_refl t) hLmin_pos hgap_nonneg hR0_nonneg hKt_nonneg
      (fun s hs => hdom s ⟨hs.1, le_trans hs.2 ht.2⟩)
      hcr_cont
      (fun s hs => hqL s ⟨hs.1, le_trans hs.2 ht.2⟩)
      (fun w s hs => hlam_nonneg_Icc w s ⟨hs.1, le_trans hs.2 ht.2⟩)
      (fun s hs => hsum s ⟨hs.1, le_trans hs.2 ht.2⟩)
      (fun s hs => hcr_nonneg s ⟨hs.1, le_trans (le_of_lt hs.2) ht.2⟩)
      (fun s hs => hcg_nonneg s ⟨hs.1, le_trans (le_of_lt hs.2) ht.2⟩)
      (fun v hv s hs => hgap v hv s ⟨hs.1, lt_of_lt_of_le hs.2 ht.2⟩)
      hRa
      (fun r hr => by
        have hrt : r = t := le_antisymm hr.2 hr.1
        subst r
        simp [Kt])
      (fun r hr => by
        have hrt : r = t := le_antisymm hr.2 hr.1
        subst r
        exact le_rfl)
  simpa [Kt] using h t ⟨le_rfl, le_rfl⟩

#print axioms selectorSettledRatioCoeff
#print axioms selectorSettledRatioEps
#print axioms epsLamSettled
#print axioms epsmixPre
#print axioms epsLamSettled_tendsto_zero_duhamel
#print axioms epsmixPre_tendsto_zero_duhamel
#print axioms solMURepl_epsLamSettled_pre_tendsto_zero_duhamel
#print axioms solMURepl_epsmixPre_tendsto_zero_duhamel
#print axioms loser_mass_small_on_settled_window
#print axioms epsmix_at_writestart
#print axioms mixTarget_near_next_on_settled_window

end Ripple.BoundedUniversality.BGP
