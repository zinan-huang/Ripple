import Ripple.BoundedUniversality.BGP.SelectorReplicatorMargin
import Ripple.BoundedUniversality.BGP.SelectorFinalAssembly
import Ripple.BoundedUniversality.BGP.SelectorOneHotDischarge
import Ripple.BoundedUniversality.BGP.BGPParams38

/-!
Ripple.BoundedUniversality.BGP.SelectorReplicatorConcSchedule
-----------------------------------------
Schedule-side inputs for the replicator concentration radius.

This file discharges the part that is independent of the configuration tube:
the growing gate integral `G θ_j - G a_j → ∞`.  It also records the algebraic
constant-range wrappers for the non-asymptotic concentration parameters.  The
actual winner margin and any branch/floor facts that depend on `sol.u` remain
explicit hypotheses.
-/

noncomputable section

namespace Ripple.BoundedUniversality.BGP

open Filter
open Set MachineInstance
open scoped BigOperators Topology

section GainGrowth

variable {d B : ℕ} {V : Type} [Fintype V]
    {p : DynGateParams} {sched : PhaseSchedule} {branch : V → BranchData d B}
    {chiResetF chiGateF kappaF gainF : ℝ → ℝ} {Pv : V → (Fin d → ℝ) → ℝ}

/-- Replicator version of the FTC gain-accumulation lower bound. -/
theorem selector_replicator_gain_accumulation
    (sol : SelectorReplicatorDynSol d B V p sched branch chiResetF chiGateF kappaF gainF Pv)
    {a b : ℝ} (hab : a ≤ b) (lb : ℝ → ℝ)
    (hdom : ∀ t ∈ Icc a b, t ∈ sched.domain)
    (hcont : Continuous fun t => chiGateF t * gainF t)
    (hlbcont : Continuous lb)
    (hlb : ∀ t ∈ Icc a b, lb t ≤ chiGateF t * gainF t) :
    (∫ t in a..b, lb t) ≤ sol.G b - sol.G a := by
  have huicc : uIcc a b = Icc a b := uIcc_of_le hab
  have hG : (∫ t in a..b, chiGateF t * gainF t) = sol.G b - sol.G a := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => ?_)
      (hcont.intervalIntegrable a b)
    rw [huicc] at ht
    exact sol.G_hasDeriv t (hdom t ht)
  rw [← hG]
  exact intervalIntegral.integral_mono_on hab (hlbcont.intervalIntegrable a b)
    (hcont.intervalIntegrable a b) hlb

/-- Exponential lower bound for a replicator gate window. -/
theorem selector_replicator_gain_lower_exp
    (sol : SelectorReplicatorDynSol d B V p sched branch chiResetF chiGateF kappaF gainF Pv)
    {a b g₀ cα ℓ : ℝ} (hab : a ≤ b) (hcα : 0 < cα) (hℓ : 0 ≤ ℓ) (hg₀ : 0 ≤ g₀)
    (hdom : ∀ t ∈ Icc a b, t ∈ sched.domain)
    (hgain : ∀ t, gainF t = g₀ * Real.exp (cα * t))
    (hcont : Continuous fun t => chiGateF t * gainF t)
    (hchi : ∀ t ∈ Icc a b, ℓ ≤ chiGateF t) :
    ℓ * g₀ * Real.exp (cα * a) * (b - a) ≤ sol.G b - sol.G a := by
  have hlb : ∀ t ∈ Icc a b, ℓ * g₀ * Real.exp (cα * a) ≤ chiGateF t * gainF t := by
    intro t ht
    have h1 : ℓ ≤ chiGateF t := hchi t ht
    have h2 : Real.exp (cα * a) ≤ Real.exp (cα * t) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.1 hcα.le)
    calc
      ℓ * g₀ * Real.exp (cα * a)
          = ℓ * (g₀ * Real.exp (cα * a)) := by ring
      _ ≤ chiGateF t * (g₀ * Real.exp (cα * t)) :=
          mul_le_mul h1 (mul_le_mul_of_nonneg_left h2 hg₀)
            (mul_nonneg hg₀ (Real.exp_pos _).le) (le_trans hℓ h1)
      _ = chiGateF t * gainF t := by rw [hgain t]
  have hconst : (∫ _t in a..b, ℓ * g₀ * Real.exp (cα * a))
      = ℓ * g₀ * Real.exp (cα * a) * (b - a) := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
    ring
  have hacc := selector_replicator_gain_accumulation sol hab
    (fun _ => ℓ * g₀ * Real.exp (cα * a)) hdom hcont continuous_const hlb
  rwa [hconst] at hacc

/-- Per-cycle linear growth of the replicator gate integral. -/
theorem selector_replicator_gain_linear_growth
    (sol : SelectorReplicatorDynSol d B V p sched branch chiResetF chiGateF kappaF gainF Pv)
    {g₀ cα ℓ a₀ w : ℝ} (aw bw : ℕ → ℝ)
    (hcα : 0 < cα) (hℓ : 0 < ℓ) (hg₀ : 0 < g₀) (hw : 0 < w) (ha₀ : 0 ≤ a₀)
    (ha : ∀ j : ℕ, 2 * Real.pi * (j : ℝ) + a₀ ≤ aw j)
    (hbw : ∀ j, w ≤ bw j - aw j)
    (hab : ∀ j, aw j ≤ bw j)
    (hdom : ∀ j, ∀ t ∈ Icc (aw j) (bw j), t ∈ sched.domain)
    (hgain : ∀ t, gainF t = g₀ * Real.exp (cα * t))
    (hcont : Continuous fun t => chiGateF t * gainF t)
    (hchi : ∀ j, ∀ t ∈ Icc (aw j) (bw j), ℓ ≤ chiGateF t) :
    ∀ j : ℕ, (ℓ * g₀ * Real.exp (cα * a₀) * w * (2 * Real.pi * cα)) * (j : ℝ)
        ≤ sol.G (bw j) - sol.G (aw j) := by
  intro j
  have hglb := selector_replicator_gain_lower_exp sol (hab j) hcα hℓ.le hg₀.le
    (fun t ht => hdom j t ht) hgain hcont (fun t ht => hchi j t ht)
  refine le_trans ?_ hglb
  have he1 :
      Real.exp (cα * a₀) * (2 * Real.pi * cα * (j : ℝ)) ≤ Real.exp (cα * aw j) := by
    calc
      Real.exp (cα * a₀) * (2 * Real.pi * cα * (j : ℝ))
          ≤ Real.exp (cα * a₀) * Real.exp (2 * Real.pi * cα * (j : ℝ)) := by
            refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
            have := Real.add_one_le_exp (2 * Real.pi * cα * (j : ℝ))
            linarith
      _ = Real.exp (cα * a₀ + 2 * Real.pi * cα * (j : ℝ)) :=
            (Real.exp_add _ _).symm
      _ ≤ Real.exp (cα * aw j) := by
            refine Real.exp_le_exp.mpr ?_
            have heq : cα * a₀ + 2 * Real.pi * cα * (j : ℝ)
                = cα * (2 * Real.pi * (j : ℝ) + a₀) := by ring
            rw [heq]
            exact mul_le_mul_of_nonneg_left (ha j) hcα.le
  calc
    (ℓ * g₀ * Real.exp (cα * a₀) * w * (2 * Real.pi * cα)) * (j : ℝ)
        = (ℓ * g₀) * (Real.exp (cα * a₀) *
            (2 * Real.pi * cα * (j : ℝ))) * w := by ring
    _ ≤ (ℓ * g₀) * Real.exp (cα * aw j) * w := by
          refine mul_le_mul_of_nonneg_right ?_ hw.le
          exact mul_le_mul_of_nonneg_left he1 (by positivity)
    _ ≤ (ℓ * g₀) * Real.exp (cα * aw j) * (bw j - aw j) := by
          refine mul_le_mul_of_nonneg_left (hbw j) ?_
          positivity
    _ = ℓ * g₀ * Real.exp (cα * aw j) * (bw j - aw j) := by ring

end GainGrowth

private theorem selectorSchedule_domain_nonneg_replConcSchedule :
    ∀ t : ℝ, 0 ≤ t → t ∈ selectorSchedule.domain := by
  intro t ht
  simpa [selectorSchedule] using ht

private theorem selector_replicator_gate_gain_nonneg
    {Mcy : ℕ} {g₀ : ℝ} (hg₀ : 0 ≤ g₀) (t : ℝ) :
    0 ≤ ((1 + Real.sin t) / 2) ^ Mcy * (g₀ * Real.exp (bgpParams38.cα * t)) := by
  have hsin_base : 0 ≤ (1 + Real.sin t) / 2 := by
    have hsin : -1 ≤ Real.sin t := Real.neg_one_le_sin t
    linarith
  exact mul_nonneg (pow_nonneg hsin_base Mcy)
    (mul_nonneg hg₀ (Real.exp_pos _).le)

/-- Linear lower bound for the concrete replicator schedule over the prefix
gate window `[2πj+π/6, 2πj+π/2]`. -/
theorem selector_replicator_clock_gain_growth_to_hold
    {d B : ℕ} {V : Type} [Fintype V] {branch : V → BranchData d B}
    {Pv : V → (Fin d → ℝ) → ℝ} {p : DynGateParams}
    {chiResetF kappaF : ℝ → ℝ} (Mcy : ℕ) {g₀ : ℝ}
    (hg₀ : 0 < g₀)
    (sol : SelectorReplicatorDynSol d B V p selectorSchedule branch
      chiResetF (fun t => ((1 + Real.sin t) / 2) ^ Mcy) kappaF
      (fun t => g₀ * Real.exp (bgpParams38.cα * t)) Pv) :
    ∀ j : ℕ,
      ((3 / 4 : ℝ) ^ Mcy * g₀ * Real.exp (bgpParams38.cα * (Real.pi / 6)) *
          (Real.pi / 3) * (2 * Real.pi * bgpParams38.cα)) * (j : ℝ)
        ≤ sol.G (selectorMUWriteHoldTime j) - sol.G (selectorMUWriteStartTime j) := by
  have hcα : 0 < bgpParams38.cα := by norm_num [bgpParams38]
  have hℓ : (0 : ℝ) < (3 / 4 : ℝ) ^ Mcy := by positivity
  intro j
  have hlinear := selector_replicator_gain_linear_growth
      (sol := sol)
      (g₀ := g₀) (cα := bgpParams38.cα)
      (aw := fun j => 2 * Real.pi * (j : ℝ) + Real.pi / 6)
      (bw := fun j => 2 * Real.pi * (j : ℝ) + Real.pi / 2)
      (ℓ := (3 / 4 : ℝ) ^ Mcy) (a₀ := Real.pi / 6) (w := Real.pi / 3)
      (hcα := hcα) (hℓ := hℓ) (hg₀ := hg₀)
      (hw := by linarith [Real.pi_pos])
      (ha₀ := by linarith [Real.pi_pos])
      (ha := by intro j; linarith)
      (hbw := by
        intro j
        have : (2 * Real.pi * (j : ℝ) + Real.pi / 2)
            - (2 * Real.pi * (j : ℝ) + Real.pi / 6) = Real.pi / 3 := by ring
        linarith)
      (hab := by intro j; linarith [Real.pi_pos])
      (hdom := by
        intro j t ht
        refine selectorSchedule_domain_nonneg_replConcSchedule t ?_
        have hleft : 0 ≤ 2 * Real.pi * (j : ℝ) + Real.pi / 6 := by positivity
        exact le_trans hleft ht.1)
      (hgain := fun _ => rfl) (hcont := by fun_prop)
      (hchi := by
        intro j t ht
        have hsin := sin_ge_half_of_gate_window j ht
        have hchi := chiGate_lb (s0 := (1 / 2 : ℝ)) Mcy hsin (by norm_num)
        have heq : ((1 + (1 / 2 : ℝ)) / 2) ^ Mcy = (3 / 4 : ℝ) ^ Mcy := by
          norm_num
        rwa [heq] at hchi)
  simpa [selectorMUWriteStartTime, selectorMUWriteHoldTime] using hlinear j

/-- Linear lower bound for the concrete replicator schedule up to the write-read
time `2πj+5π/6`. -/
theorem selector_replicator_clock_gain_growth_to_read
    {d B : ℕ} {V : Type} [Fintype V] {branch : V → BranchData d B}
    {Pv : V → (Fin d → ℝ) → ℝ} {p : DynGateParams}
    {chiResetF kappaF : ℝ → ℝ} (Mcy : ℕ) {g₀ : ℝ}
    (hg₀ : 0 < g₀)
    (sol : SelectorReplicatorDynSol d B V p selectorSchedule branch
      chiResetF (fun t => ((1 + Real.sin t) / 2) ^ Mcy) kappaF
      (fun t => g₀ * Real.exp (bgpParams38.cα * t)) Pv) :
    ∀ j : ℕ,
      ((3 / 4 : ℝ) ^ Mcy * g₀ * Real.exp (bgpParams38.cα * (Real.pi / 6)) *
          (Real.pi / 3) * (2 * Real.pi * bgpParams38.cα)) * (j : ℝ)
        ≤ sol.G (selectorMUWriteReadTime j) - sol.G (selectorMUWriteStartTime j) := by
  intro j
  have hmid :
      ((3 / 4 : ℝ) ^ Mcy * g₀ * Real.exp (bgpParams38.cα * (Real.pi / 6)) *
          (Real.pi / 3) * (2 * Real.pi * bgpParams38.cα)) * (j : ℝ)
        ≤ sol.G (selectorMUWriteHoldTime j)
          - sol.G (selectorMUWriteStartTime j) := by
    exact selector_replicator_clock_gain_growth_to_hold
      (Mcy := Mcy) (g₀ := g₀) hg₀ sol j
  have htail : 0 ≤ sol.G (selectorMUWriteReadTime j)
      - sol.G (selectorMUWriteHoldTime j) := by
    have hab : selectorMUWriteHoldTime j ≤ selectorMUWriteReadTime j :=
      selectorMUWriteHold_le_read j
    have hacc := selector_replicator_gain_accumulation sol hab (fun _ => (0 : ℝ))
      (fun t ht => by
        refine selectorSchedule_domain_nonneg_replConcSchedule t ?_
        have hleft : 0 ≤ selectorMUWriteHoldTime j := by
          exact le_trans (selectorMUWriteStartTime_nonneg j) (selectorMUWriteStart_le_hold j)
        exact le_trans hleft ht.1)
      (by fun_prop) continuous_const
      (fun t _ht => selector_replicator_gate_gain_nonneg hg₀.le t)
    simpa using hacc
  linarith

/-- For every concrete `M_U` replicator solution family, the gate integral over
the write window diverges in the cycle index. -/
theorem solMURepl_deltaG_tendsto_atTop
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀)
    (hg₀ : 0 < (g₀ : ℝ)) (w : ℕ) :
    Tendsto
      (fun j => (sol w).G (selectorMUWriteReadTime j)
        - (sol w).G (selectorMUWriteStartTime j)) atTop atTop := by
  let c : ℝ :=
    (3 / 4 : ℝ) ^ Mcy * (g₀ : ℝ) * Real.exp (bgpParams38.cα * (Real.pi / 6)) *
      (Real.pi / 3) * (2 * Real.pi * bgpParams38.cα)
  have hcα : 0 < bgpParams38.cα := by norm_num [bgpParams38]
  have hc : 0 < c := by
    have hpow : 0 < (3 / 4 : ℝ) ^ Mcy := by positivity
    have hpi3 : 0 < Real.pi / 3 := by positivity
    have h2pic : 0 < 2 * Real.pi * bgpParams38.cα := by nlinarith [Real.pi_pos, hcα]
    dsimp [c]
    positivity
  refine selectorOneHotDeltaG_tendsto_atTop_of_linear (c := c) hc ?_
  intro j
  simpa [c] using
    selector_replicator_clock_gain_growth_to_read (Mcy := Mcy) (g₀ := (g₀ : ℝ)) hg₀ (sol w) j

/-- For every concrete `M_U` replicator solution family, the gate integral over
the prefix select-to-hold window `[π/6, π/2]` diverges in the cycle index. -/
theorem solMURepl_deltaG_pre_tendsto_atTop
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀)
    (hg₀ : 0 < (g₀ : ℝ)) (w : ℕ) :
    Tendsto
      (fun j => (sol w).G (selectorMUWriteHoldTime j)
        - (sol w).G (selectorMUWriteStartTime j)) atTop atTop := by
  let c : ℝ :=
    (3 / 4 : ℝ) ^ Mcy * (g₀ : ℝ) * Real.exp (bgpParams38.cα * (Real.pi / 6)) *
      (Real.pi / 3) * (2 * Real.pi * bgpParams38.cα)
  have hcα : 0 < bgpParams38.cα := by norm_num [bgpParams38]
  have hc : 0 < c := by
    have hpow : 0 < (3 / 4 : ℝ) ^ Mcy := by positivity
    have hpi3 : 0 < Real.pi / 3 := by positivity
    have h2pic : 0 < 2 * Real.pi * bgpParams38.cα := by nlinarith [Real.pi_pos, hcα]
    dsimp [c]
    positivity
  refine selectorOneHotDeltaG_tendsto_atTop_of_linear (c := c) hc ?_
  intro j
  simpa [c] using
    selector_replicator_clock_gain_growth_to_hold (Mcy := Mcy) (g₀ := (g₀ : ℝ)) hg₀ (sol w) j

section ConstantRanges

/-- The fixed positive simplex floor value.  Whether this floor holds through a
write window is a separate dynamical/tube invariant. -/
theorem solMURepl_concLmin_floor :
    0 < (1 / (Fintype.card UniversalLocalView : ℝ)) := by
  have hcard : 0 < (Fintype.card UniversalLocalView : ℝ) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ⟨defaultLocalViewU⟩ :
      0 < Fintype.card UniversalLocalView)
  positivity

/-- Uniform λ-initialization gives loser/winner ratio exactly `1` at `t = 0`
for the Euclidean initial vector.  This does not assert the same equality at
the later write-start time. -/
theorem solMURepl_concR0_eq_one
    (x₀ : ℕ → Fin d_U → ℚ) (w : ℕ) (g₀ : ℚ) (v vstar : UniversalLocalView) :
    selectorMUReplicatorInit x₀ w g₀ (selLamCoord v) /
        selectorMUReplicatorInit x₀ w g₀ (selLamCoord vstar) = (1 : ℝ) := by
  have hN : (Fintype.card UniversalLocalView : ℝ) ≠ 0 := by
    exact_mod_cast
      (ne_of_gt (Fintype.card_pos_iff.mpr ⟨defaultLocalViewU⟩ :
        0 < Fintype.card UniversalLocalView))
  simp [selectorMUReplicatorInit, selectorReplicatorEuclInitQ, selLamCoord]
  field_simp [hN]

/-- A usable fixed `R0` bound from a carried winner floor and the simplex
invariants.  The exact value `1` at write-start is not derivable from the
current `solMURepl` interface. -/
theorem solMURepl_concR0_card_bound
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    {cfg : ℕ → ℕ → UConf}
    (w j : ℕ)
    (hqL : (1 / (Fintype.card UniversalLocalView : ℝ)) ≤
      (sol w).lam (localViewU (cfg w j)) (selectorMUWriteStartTime j)) :
    ∀ v : UniversalLocalView, v ≠ localViewU (cfg w j) →
      (sol w).lam v (selectorMUWriteStartTime j) /
          (sol w).lam (localViewU (cfg w j)) (selectorMUWriteStartTime j)
        ≤ (Fintype.card UniversalLocalView : ℝ) := by
  classical
  intro v _hv
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
  let a := selectorMUWriteStartTime j
  have ha0 : 0 ≤ a := by simpa [a] using selectorMUWriteStartTime_nonneg j
  have hN_pos : 0 < (Fintype.card UniversalLocalView : ℝ) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ⟨defaultLocalViewU⟩ :
      0 < Fintype.card UniversalLocalView)
  have hden_pos : 0 < (sol w).lam (localViewU (cfg w j)) a := by
    exact lt_of_lt_of_le solMURepl_concLmin_floor (by simpa [a] using hqL)
  have hnum_le_one : (sol w).lam v a ≤ 1 := by
    have hle_sum : (sol w).lam v a ≤ ∑ u : UniversalLocalView, (sol w).lam u a :=
      Finset.single_le_sum (fun u _ => hlam_nonneg_forward u a ha0) (Finset.mem_univ v)
    simpa [hsum_forward a ha0] using hle_sum
  rw [div_le_iff₀ hden_pos]
  have hmul_floor :
      (1 : ℝ) ≤ (Fintype.card UniversalLocalView : ℝ) *
        (sol w).lam (localViewU (cfg w j)) a := by
    have hmul := mul_le_mul_of_nonneg_left (by simpa [a] using hqL) hN_pos.le
    have hone :
        (Fintype.card UniversalLocalView : ℝ) *
            (1 / (Fintype.card UniversalLocalView : ℝ)) = 1 := by
      field_simp [ne_of_gt hN_pos]
    simpa [hone] using hmul
  exact le_trans hnum_le_one hmul_floor

/-- Branch-spread algebra from a uniform absolute branch bound.  The absolute
bound itself is supplied by the `u`-tube/bounded-branch invariant. -/
theorem solMURepl_concRspread_bound
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    {cfg : ℕ → ℕ → UConf} {Rbr : ℝ}
    (hRbr_nonneg : 0 ≤ Rbr)
    (hbranch : ∀ w j i v,
      |BranchData.evalBranch (branchU v) ((sol w).u (selectorMUWriteReadTime j)) i| ≤ Rbr) :
    ∀ w j i v, v ≠ localViewU (cfg w j) →
      |BranchData.evalBranch (branchU v) ((sol w).u (selectorMUWriteReadTime j)) i
        - BranchData.evalBranch (branchU (localViewU (cfg w j)))
            ((sol w).u (selectorMUWriteReadTime j)) i| ≤ 2 * Rbr := by
  intro w j i v _hv
  have htri :
      |BranchData.evalBranch (branchU v) ((sol w).u (selectorMUWriteReadTime j)) i
        - BranchData.evalBranch (branchU (localViewU (cfg w j)))
            ((sol w).u (selectorMUWriteReadTime j)) i|
        ≤ |BranchData.evalBranch (branchU v) ((sol w).u (selectorMUWriteReadTime j)) i|
          + |BranchData.evalBranch (branchU (localViewU (cfg w j)))
            ((sol w).u (selectorMUWriteReadTime j)) i| := by
    simpa [sub_eq_add_neg, abs_neg] using abs_add_le
      (BranchData.evalBranch (branchU v) ((sol w).u (selectorMUWriteReadTime j)) i)
      (-(BranchData.evalBranch (branchU (localViewU (cfg w j)))
        ((sol w).u (selectorMUWriteReadTime j)) i))
  have hsum :
      |BranchData.evalBranch (branchU v) ((sol w).u (selectorMUWriteReadTime j)) i|
          + |BranchData.evalBranch (branchU (localViewU (cfg w j)))
            ((sol w).u (selectorMUWriteReadTime j)) i|
        ≤ Rbr + Rbr := add_le_add (hbranch w j i v) (hbranch w j i (localViewU (cfg w j)))
  linarith

/-- The concrete schedule supplies `ΔG → ∞`; the remaining asymptotic reset
content is the Duhamel residual
`Kreset w j * exp (-(gap w j * ΔG_j)) → 0`, not a bound on `Kreset`.

For the real `solMURepl` schedule this residual is satisfiable: multiplying
the forward reset coefficient by `exp (-gap*(G(b)-G(a)))` converts the reset
integral to the backward weight
`exp (-gap*(G(b)-G(t)))`.  Since the gate rate `cg = χ_gate * gain` grows
exponentially on the write window, this backward kernel concentrates on a
vanishing `G`-window near `b`, while the effective reset rate `cr/cg` tends to
zero.  The old `εmixExplicitCoeff ≤ C` route would require `Kreset` itself to
stay bounded and is not satisfiable for the concrete reset coefficient. -/
theorem solMURepl_εmixExplicit_tendsto_zero
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    {cfg : ℕ → ℕ → UConf}
    (inputs : SelectorReplicatorConcInputs sol cfg) (w : ℕ)
    (hg₀ : 0 < (g₀ : ℝ))
    {gap0 Lmin0 R0max Rmax : ℝ}
    (hgap0 : 0 < gap0)
    (hgap_lb : ∀ᶠ j in atTop, gap0 ≤ inputs.gap w j)
    (hLmin0_pos : 0 < Lmin0)
    (hLmin_lb : ∀ᶠ j in atTop, Lmin0 ≤ inputs.Lmin w j)
    (hR0_nonneg : ∀ᶠ j in atTop, 0 ≤ inputs.R0 w j)
    (hR0_bound : ∀ᶠ j in atTop, inputs.R0 w j ≤ R0max)
    (hRspread_bound : ∀ᶠ j in atTop, inputs.Rspread w j ≤ Rmax)
    (hDuhamel : Tendsto (fun j => εmixDuhamelResidual inputs w j) atTop (𝓝 0)) :
    Tendsto (fun j => εmixExplicit inputs w j) atTop (𝓝 0) := by
  exact εmixExplicit_tendsto_zero_duhamel inputs w hgap0 hgap_lb
    (solMURepl_deltaG_pre_tendsto_atTop sol hg₀ w) hLmin0_pos hLmin_lb
    hR0_nonneg hR0_bound hRspread_bound hDuhamel

end ConstantRanges

#print axioms selector_replicator_gain_accumulation
#print axioms selector_replicator_gain_lower_exp
#print axioms selector_replicator_gain_linear_growth
#print axioms selector_replicator_clock_gain_growth_to_hold
#print axioms selector_replicator_clock_gain_growth_to_read
#print axioms solMURepl_deltaG_tendsto_atTop
#print axioms solMURepl_deltaG_pre_tendsto_atTop
#print axioms solMURepl_concLmin_floor
#print axioms solMURepl_concR0_eq_one
#print axioms solMURepl_concR0_card_bound
#print axioms solMURepl_concRspread_bound
#print axioms solMURepl_εmixExplicit_tendsto_zero

end Ripple.BoundedUniversality.BGP
