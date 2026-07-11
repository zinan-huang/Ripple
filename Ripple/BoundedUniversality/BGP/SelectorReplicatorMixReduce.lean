import Ripple.BoundedUniversality.BGP.SelectorReplicatorFinal
import Ripple.BoundedUniversality.BGP.SelectorReplicatorHStartStructural
import Ripple.BoundedUniversality.BGP.BGPParams38

/-!
Ripple.BoundedUniversality.BGP.SelectorReplicatorMixReduce
---------------------------------------
Make the write-time replicator mixture residual explicit.

The bundle below keeps the genuine per-cycle concentration inputs.  The simplex
side conditions needed by `selector_replicator_mix_close_of_concentration` are
not fields: total λ-mass and λ-nonnegativity are rederived from the abstract
replicator conservation lemmas and the concrete box inputs.
-/

noncomputable section

open Filter
open scoped BigOperators Topology

namespace Ripple.BoundedUniversality.BGP

open Set MachineInstance

/-- Per-`(w,j)` concentration data for the concrete `M_U` replicator write
window.

The selected branch is not a stored field: it is definitionally
`localViewU (cfg w j)`.  The remaining fields are exactly the concentration
parameters and comparison estimates consumed by
`selector_replicator_mix_close_of_concentration`. -/
structure SelectorReplicatorConcInputs
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀)
    (cfg : ℕ → ℕ → UConf) where
  Lmin : ℕ → ℕ → ℝ
  gap : ℕ → ℕ → ℝ
  R0 : ℕ → ℕ → ℝ
  Kreset : ℕ → ℕ → ℝ
  Rspread : ℕ → ℕ → ℝ
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
  hRspread_nonneg : ∀ w j, 0 ≤ Rspread w j
  hspread : ∀ w j, ∀ i, ∀ v : UniversalLocalView,
    v ≠ localViewU (cfg w j) →
      |BranchData.evalBranch (branchU v) ((sol w).u (selectorMUWriteHoldTime j)) i
        - BranchData.evalBranch (branchU (localViewU (cfg w j)))
            ((sol w).u (selectorMUWriteHoldTime j)) i| ≤ Rspread w j

/-- The bounded prefactor in the explicit write-time replicator mix radius. -/
def εmixExplicitCoeff
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    {cfg : ℕ → ℕ → UConf}
    (inputs : SelectorReplicatorConcInputs sol cfg) (w j : ℕ) : ℝ :=
  inputs.Rspread w j * ((Fintype.card UniversalLocalView : ℝ) - 1) *
    (inputs.R0 w j
      + inputs.Kreset w j /
          ((Fintype.card UniversalLocalView : ℝ) * inputs.Lmin w j))

/-- The explicit residual replacing the raw write-time `εmix` assumption. -/
def εmixExplicit
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    {cfg : ℕ → ℕ → UConf}
    (inputs : SelectorReplicatorConcInputs sol cfg) (w j : ℕ) : ℝ :=
  εmixExplicitCoeff inputs w j *
    Real.exp
      (-(inputs.gap w j *
        ((sol w).G (selectorMUWriteHoldTime j)
          - (sol w).G (selectorMUWriteStartTime j))))

/-- Duhamel residual for the reset contribution after multiplying by the
backward concentration factor.  This is the quantity that must vanish in the
concrete schedule; `Kreset` itself is not expected to stay bounded. -/
def εmixDuhamelResidual
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    {cfg : ℕ → ℕ → UConf}
    (inputs : SelectorReplicatorConcInputs sol cfg) (w j : ℕ) : ℝ :=
  inputs.Kreset w j *
    Real.exp
      (-(inputs.gap w j *
        ((sol w).G (selectorMUWriteHoldTime j)
          - (sol w).G (selectorMUWriteStartTime j))))

/-- The concrete gate coefficient `χ_gate · gain` is nonnegative when `g₀ ≥ 0`. -/
lemma selector_replicator_chiGate_gain_nonneg
    {Mcy : ℕ} {g₀ : ℚ} (hg₀_nonneg : 0 ≤ (g₀ : ℝ)) :
    ∀ t : ℝ,
      0 ≤ ((1 + Real.sin t) / 2) ^ Mcy *
        ((g₀ : ℝ) * Real.exp (bgpParams38.cα * t)) := by
  intro t
  have hsin_base : 0 ≤ (1 + Real.sin t) / 2 := by
    have hsin : -1 ≤ Real.sin t := Real.neg_one_le_sin t
    linarith
  have hpulse : 0 ≤ ((1 + Real.sin t) / 2) ^ Mcy :=
    pow_nonneg hsin_base Mcy
  have hgain : 0 ≤ (g₀ : ℝ) * Real.exp (bgpParams38.cα * t) :=
    mul_nonneg hg₀_nonneg (le_of_lt (Real.exp_pos _))
  exact mul_nonneg hpulse hgain

/-- Discharge the raw write-time `hmix` residual from concentration inputs. -/
theorem selector_replicator_hmix_of_concInputs
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    {cfg : ℕ → ℕ → UConf}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (hg₀_nonneg : 0 ≤ (g₀ : ℝ))
    (inputs : SelectorReplicatorConcInputs sol cfg) :
    ∀ w j, ∀ i,
      |selectorMixTarget branchU (sol w).u (sol w).lam (selectorMUWriteHoldTime j) i
        - BranchData.evalBranch (branchU (localViewU (cfg w j)))
            ((sol w).u (selectorMUWriteHoldTime j)) i| ≤ εmixExplicit inputs w j := by
  intro w j i
  haveI : Nonempty UniversalLocalView := ⟨defaultLocalViewU⟩
  have hode : ∀ v : UniversalLocalView, ∀ t : ℝ, 0 ≤ t →
      HasDerivAt ((sol w).lam v)
        ((((1 + Real.cos t) / 2) ^ Mcy * (κ₀ : ℝ)) *
            (1 / (Fintype.card UniversalLocalView : ℝ) - (sol w).lam v t)
          + (((1 + Real.sin t) / 2) ^ Mcy *
              ((g₀ : ℝ) * Real.exp (bgpParams38.cα * t))) *
            (sol w).lam v t *
              (universalPval eta heta v ((sol w).u t)
                - ∑ u : UniversalLocalView,
                    (sol w).lam u t * universalPval eta heta u ((sol w).u t))) t := by
    intro v t ht
    simpa [selectorSchedule] using
      (sol w).lam_hasDeriv v t (by simpa [selectorSchedule] using ht)
  have hsum_forward : ∀ t : ℝ, 0 ≤ t →
      (∑ v : UniversalLocalView, (sol w).lam v t) = 1 :=
    replicator_sum_lam_eq_one
      (lam := fun v t => (sol w).lam v t)
      (P := fun v t => universalPval eta heta v ((sol w).u t))
      (cr := fun t => ((1 + Real.cos t) / 2) ^ Mcy * (κ₀ : ℝ))
      (cg := fun t =>
        ((1 + Real.sin t) / 2) ^ Mcy *
          ((g₀ : ℝ) * Real.exp (bgpParams38.cα * t)))
      boxInputs.hcr_cont boxInputs.hcg_cont
      (fun v => (sol w).cont_lam v)
      (boxInputs.hP_cont w) hode (boxInputs.hlam_sum0 w)
  have hlam_nonneg_forward :
      ∀ v : UniversalLocalView, ∀ t : ℝ, 0 ≤ t → 0 ≤ (sol w).lam v t :=
    replicator_lam_nonneg
      (lam := fun v t => (sol w).lam v t)
      (P := fun v t => universalPval eta heta v ((sol w).u t))
      (cr := fun t => ((1 + Real.cos t) / 2) ^ Mcy * (κ₀ : ℝ))
      (cg := fun t =>
        ((1 + Real.sin t) / 2) ^ Mcy *
          ((g₀ : ℝ) * Real.exp (bgpParams38.cα * t)))
      boxInputs.hcr_cont boxInputs.hcg_cont
      (fun v => (sol w).cont_lam v)
      (boxInputs.hP_cont w) boxInputs.hcr_nonneg hode
      (boxInputs.hlam_init_nonneg w)
  have hθ_nonneg : 0 ≤ selectorMUWriteHoldTime j :=
    le_trans (selectorMUWriteStartTime_nonneg j) (selectorMUWriteStart_le_hold j)
  have hcore :=
    selector_replicator_mix_close_of_concentration
      (sol := sol w)
      (vstar := localViewU (cfg w j))
      (i := i)
      (a := selectorMUWriteStartTime j)
      (b := selectorMUWriteHoldTime j)
      (Lmin := inputs.Lmin w j)
      (gap := inputs.gap w j)
      (R0 := inputs.R0 w j)
      (Kreset := inputs.Kreset w j)
      (Rspread := inputs.Rspread w j)
      (selectorMUWriteStart_le_hold j)
      (inputs.hLmin_pos w j)
      (selectorMU_hdom_writeHold w j)
      boxInputs.hcr_cont
      (fun t ht => inputs.hqL w j t ⟨ht.1, le_trans ht.2 (selectorMUWriteHold_le_read j)⟩)
      (fun v t ht => hlam_nonneg_forward v t
        (le_trans (selectorMUWriteStartTime_nonneg j) ht.1))
      (hsum_forward (selectorMUWriteHoldTime j) hθ_nonneg)
      (fun t _ht => boxInputs.hcr_nonneg t)
      (fun t _ht => selector_replicator_chiGate_gain_nonneg
        (Mcy := Mcy) (g₀ := g₀) hg₀_nonneg t)
      (fun v hv t ht => inputs.hgap w j v hv t ⟨ht.1, lt_of_lt_of_le ht.2 (selectorMUWriteHold_le_read j)⟩)
      (inputs.hRa w j)
      (inputs.hKreset w j)
      (inputs.hRspread_nonneg w j)
      (fun v hv => inputs.hspread w j i v hv)
  have hcore' := hcore
  rw [show
      -inputs.gap w j *
          ((sol w).G (selectorMUWriteHoldTime j)
            - (sol w).G (selectorMUWriteStartTime j)) =
        -(inputs.gap w j *
          ((sol w).G (selectorMUWriteHoldTime j)
            - (sol w).G (selectorMUWriteStartTime j))) by ring] at hcore'
  simpa [εmixExplicit, εmixExplicitCoeff, mul_assoc] using hcore'

/-- The exponential concentration factor tends to zero from a uniform positive
gap and an unbounded gate gain integral. -/
lemma selector_replicator_exp_decay_tendsto_zero
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    {cfg : ℕ → ℕ → UConf}
    (inputs : SelectorReplicatorConcInputs sol cfg) (w : ℕ)
    {gap0 : ℝ}
    (hgap0 : 0 < gap0)
    (hgap_lb : ∀ᶠ j in atTop, gap0 ≤ inputs.gap w j)
    (hΔG : Tendsto
      (fun j => (sol w).G (selectorMUWriteHoldTime j)
        - (sol w).G (selectorMUWriteStartTime j)) atTop atTop) :
    Tendsto
      (fun j =>
        Real.exp
          (-(inputs.gap w j *
            ((sol w).G (selectorMUWriteHoldTime j)
              - (sol w).G (selectorMUWriteStartTime j)))))
      atTop (𝓝 0) := by
  have hgap0ΔG :
      Tendsto
        (fun j => gap0 *
          ((sol w).G (selectorMUWriteHoldTime j)
            - (sol w).G (selectorMUWriteStartTime j)))
        atTop atTop :=
    hΔG.const_mul_atTop hgap0
  have hgapΔG :
      Tendsto
        (fun j => inputs.gap w j *
          ((sol w).G (selectorMUWriteHoldTime j)
            - (sol w).G (selectorMUWriteStartTime j)))
        atTop atTop := by
    refine tendsto_atTop_mono' atTop ?_ hgap0ΔG
    filter_upwards [hgap_lb, hΔG.eventually_ge_atTop 0] with j hgap hΔG_nonneg
    exact mul_le_mul_of_nonneg_right hgap hΔG_nonneg
  exact Real.tendsto_exp_atBot.comp
    (tendsto_neg_atTop_atBot.comp hgapΔG)

/-- General bounded-prefactor decay lemma.

This is valid only for abstract inputs where `εmixExplicitCoeff` itself is
eventually bounded.  The concrete `solMURepl` schedule must use
`εmixExplicit_tendsto_zero_duhamel`, because its reset coefficient `Kreset`
grows with the forward variation-of-constants weight. -/
theorem εmixExplicit_tendsto_zero
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    {cfg : ℕ → ℕ → UConf}
    (inputs : SelectorReplicatorConcInputs sol cfg) (w : ℕ)
    {gap0 C : ℝ}
    (hgap0 : 0 < gap0)
    (hgap_lb : ∀ᶠ j in atTop, gap0 ≤ inputs.gap w j)
    (hΔG : Tendsto
      (fun j => (sol w).G (selectorMUWriteHoldTime j)
        - (sol w).G (selectorMUWriteStartTime j)) atTop atTop)
    (hcoef_nonneg : ∀ᶠ j in atTop, 0 ≤ εmixExplicitCoeff inputs w j)
    (hcoef_bound : ∀ᶠ j in atTop, εmixExplicitCoeff inputs w j ≤ C) :
    Tendsto (fun j => εmixExplicit inputs w j) atTop (𝓝 0) := by
  have hdecay :=
    selector_replicator_exp_decay_tendsto_zero
      (inputs := inputs) (w := w) hgap0 hgap_lb hΔG
  simpa [εmixExplicit] using
    bdd_le_mul_tendsto_zero hcoef_nonneg hcoef_bound hdecay

/-- Duhamel form of the explicit mix-radius decay.

The reset input is not required to be bounded.  Instead the reset contribution
is carried in the satisfiable residual
`Kreset w j * exp (-(gap w j * ΔG_j))`.  Algebraically,
`exp (gap*(G(t)-G(a))) * exp (-gap*(G(b)-G(a))) =
exp (-gap*(G(b)-G(t)))`, so the concrete residual is a backward-weighted reset
integral rather than the forward variation-of-constants coefficient. -/
theorem εmixExplicit_tendsto_zero_duhamel
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    {cfg : ℕ → ℕ → UConf}
    (inputs : SelectorReplicatorConcInputs sol cfg) (w : ℕ)
    {gap0 Lmin0 R0max Rmax : ℝ}
    (hgap0 : 0 < gap0)
    (hgap_lb : ∀ᶠ j in atTop, gap0 ≤ inputs.gap w j)
    (hΔG : Tendsto
      (fun j => (sol w).G (selectorMUWriteHoldTime j)
        - (sol w).G (selectorMUWriteStartTime j)) atTop atTop)
    (hLmin0_pos : 0 < Lmin0)
    (hLmin_lb : ∀ᶠ j in atTop, Lmin0 ≤ inputs.Lmin w j)
    (hR0_nonneg : ∀ᶠ j in atTop, 0 ≤ inputs.R0 w j)
    (hR0_bound : ∀ᶠ j in atTop, inputs.R0 w j ≤ R0max)
    (hRspread_bound : ∀ᶠ j in atTop, inputs.Rspread w j ≤ Rmax)
    (hDuhamel : Tendsto (fun j => εmixDuhamelResidual inputs w j) atTop (𝓝 0)) :
    Tendsto (fun j => εmixExplicit inputs w j) atTop (𝓝 0) := by
  let ΔG : ℕ → ℝ := fun j =>
    (sol w).G (selectorMUWriteHoldTime j)
      - (sol w).G (selectorMUWriteStartTime j)
  let E : ℕ → ℝ := fun j =>
    Real.exp (-(inputs.gap w j * ΔG j))
  let N : ℝ := Fintype.card UniversalLocalView
  have hN_nat : 0 < Fintype.card UniversalLocalView :=
    Fintype.card_pos_iff.mpr ⟨defaultLocalViewU⟩
  have hN_pos : 0 < N := Nat.cast_pos.mpr hN_nat
  have hNm1_nonneg : 0 ≤ N - 1 := by
    have hN_ge_one_nat : 1 ≤ Fintype.card UniversalLocalView :=
      Nat.succ_le_of_lt hN_nat
    have hN_ge_one : (1 : ℝ) ≤ N := Nat.one_le_cast.mpr hN_ge_one_nat
    linarith
  have hdecay : Tendsto E atTop (𝓝 0) := by
    simpa [E, ΔG] using
      selector_replicator_exp_decay_tendsto_zero
        (inputs := inputs) (w := w) hgap0 hgap_lb hΔG
  have hR0term : Tendsto (fun j => inputs.R0 w j * E j) atTop (𝓝 0) :=
    bdd_le_mul_tendsto_zero hR0_nonneg hR0_bound hdecay
  have hresetFactor_nonneg :
      ∀ᶠ j in atTop, 0 ≤ 1 / (N * inputs.Lmin w j) := by
    filter_upwards [hLmin_lb] with j hLmin
    exact one_div_nonneg.mpr
      (mul_nonneg hN_pos.le (le_trans hLmin0_pos.le hLmin))
  have hresetFactor_bound :
      ∀ᶠ j in atTop, 1 / (N * inputs.Lmin w j) ≤ 1 / (N * Lmin0) := by
    filter_upwards [hLmin_lb] with j hLmin
    have hden_pos : 0 < N * Lmin0 := mul_pos hN_pos hLmin0_pos
    have hden_le : N * Lmin0 ≤ N * inputs.Lmin w j :=
      mul_le_mul_of_nonneg_left hLmin hN_pos.le
    exact one_div_le_one_div_of_le hden_pos hden_le
  have hDterm_raw :
      Tendsto
        (fun j => (1 / (N * inputs.Lmin w j)) *
          εmixDuhamelResidual inputs w j) atTop (𝓝 0) :=
    bdd_le_mul_tendsto_zero hresetFactor_nonneg hresetFactor_bound hDuhamel
  have hDterm :
      Tendsto
        (fun j => εmixDuhamelResidual inputs w j / (N * inputs.Lmin w j))
        atTop (𝓝 0) := by
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hDterm_raw
  have hbracket :
      Tendsto
        (fun j =>
          inputs.R0 w j * E j
            + εmixDuhamelResidual inputs w j / (N * inputs.Lmin w j))
        atTop (𝓝 0) := by
    simpa using hR0term.add hDterm
  have hmult_nonneg :
      ∀ᶠ j in atTop, 0 ≤ inputs.Rspread w j * (N - 1) := by
    filter_upwards [] with j
    exact mul_nonneg (inputs.hRspread_nonneg w j) hNm1_nonneg
  have hmult_bound :
      ∀ᶠ j in atTop, inputs.Rspread w j * (N - 1) ≤ Rmax * (N - 1) := by
    filter_upwards [hRspread_bound] with j hRspread
    exact mul_le_mul_of_nonneg_right hRspread hNm1_nonneg
  have hprod :
      Tendsto
        (fun j =>
          (inputs.Rspread w j * (N - 1)) *
            (inputs.R0 w j * E j
              + εmixDuhamelResidual inputs w j / (N * inputs.Lmin w j)))
        atTop (𝓝 0) :=
    bdd_le_mul_tendsto_zero hmult_nonneg hmult_bound hbracket
  refine hprod.congr' ?_
  filter_upwards [] with j
  dsimp [εmixExplicit, εmixExplicitCoeff, εmixDuhamelResidual, E, ΔG, N]
  ring

#print axioms SelectorReplicatorConcInputs
#print axioms εmixExplicitCoeff
#print axioms εmixExplicit
#print axioms εmixDuhamelResidual
#print axioms selector_replicator_chiGate_gain_nonneg
#print axioms selector_replicator_hmix_of_concInputs
#print axioms selector_replicator_exp_decay_tendsto_zero
#print axioms εmixExplicit_tendsto_zero
#print axioms εmixExplicit_tendsto_zero_duhamel

end Ripple.BoundedUniversality.BGP
