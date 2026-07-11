/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `ClockLayerBAmplification` — concrete epidemic-amplification tail (Layer-B item 2).

Replaces the free `AmpGoodAtEnd` / `hMGF` shell of `ClockLayerB.epidemic_amplification_window` by a
STOPPED-kernel exp-MGF supermartingale, mirroring `GhostSmallConc` exactly (`ClimbTail.mgf_one_step`
+ `geometric_drift_tail`).  The clean-above count `cleanCount T = clockCleanAbove T` plays the role
of `clockTaintedCount`; the multiplicative epidemic rate `2·Y·(C₀−Y)/(n(n−1))` (the corrected mixed
`2κY/n`, NOT `2Y/n` nor `2κ²Y/n`) is made uniformly cappable by adding `Y ≤ Rcap` to the state-local
active gate `AmpActive` (so the constant-rate `geometric_drift_tail` applies).  The endpoint event is
the fixed-budget `AmpGoodAtEndBudget` (the `∀ immFrac` shell shape was too strong).

The genuine remaining content is THREE state-local, satisfiable, refutation-checkable obligations
(NO false ∀c — exactly the `GhostSmallConc` hsub/hincr/hqcap pattern):
* `CleanRiseAtMostOne` — one marked step raises `cleanCount` by ≤ 1 (pair-update combinatorics);
* `CleanRiseProbBound` — one-step clean-rise prob ≤ `qImm + 2Y(C₀−Y)/(n(n−1))` (pair classification);
* `CleanRiseRateCap` — the symbolic uniform cap `qImm + epiRate ≤ qAmp` on the active region.

The stopped-kernel → `markedK` gate-exit charge belongs in Layer D's first-exit union (`ClockLayerD`).

Source: ChatGPT family2 second-pass draft @ed3e4c1 (task 56710d4b), audited + verified here.
NEW file; no existing file edited; no sorry/admit/axiom/native_decide.
Reference: `DOCTRINE_THM69_CA.md` Round 4/5 (amplification MGF); Doty et al. (arXiv:2106.10201v2) §6.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ClockLayerB
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.GhostSmallConc
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ClimbTail

namespace ExactMajority
namespace ClockLayerB

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real BigOperators
open ClockRealKernel
open EarlyDripMarked
open ClockFrontMixed
open ClockTaintMixed
open Classical

variable {L K : ℕ}

/-- Alias for the clean-above count used in the MGF. -/
def cleanCount (T : ℕ) (mc : MCfg L K) : ℕ :=
  clockCleanAbove (L := L) (K := K) T mc

/-- Exponential potential `exp(λ · cleanCount)`. -/
noncomputable def AmpPot (T : ℕ) (lam : ℝ) (mc : MCfg L K) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (lam * (cleanCount (L := L) (K := K) T mc : ℝ)))

theorem AmpPot_measurable (T : ℕ) (lam : ℝ) :
    Measurable (AmpPot (L := L) (K := K) T lam) :=
  Measurable.of_discrete

/--
Exact finite-`n` epidemic-copy rate for clean clocks above `T`.  `Y = cleanCount T mc`; the rate is
`2 * Y * (C₀ - Y) / (n * (n - 1))` (the corrected mixed-kernel rate, not `2Y/n`, not `2κ²Y/n`). -/
noncomputable def cleanEpiRate (n C₀ T : ℕ) (mc : MCfg L K) : ℝ :=
  let Y : ℝ := cleanCount (L := L) (K := K) T mc
  (2 : ℝ) * Y * ((C₀ : ℝ) - Y) / ((n : ℝ) * ((n : ℝ) - 1))

/--
State-local active gate for amplification: extends `Active63` only by the current clean-count cap
`Y ≤ Rcap`.  No future/window-good event appears here. -/
def AmpActive (C₀ T : ℕ) (θ ρ η Rcap : ℝ) (Aux : MCfg L K → Prop)
    (mc : MCfg L K) : Prop :=
  Active63 (L := L) (K := K) C₀ T θ ρ η Aux mc ∧
    (cleanCount (L := L) (K := K) T mc : ℝ) ≤ Rcap

def ampActiveSet (C₀ T : ℕ) (θ ρ η Rcap : ℝ) (Aux : MCfg L K → Prop) :
    Set (MCfg L K) :=
  {mc | AmpActive (L := L) (K := K) C₀ T θ ρ η Rcap Aux mc}

/-- Stopped marked kernel for amplification: run `markedK` on the active region, self-loop off it. -/
noncomputable def KampStar (T θn C₀ : ℕ) (θ ρ η Rcap : ℝ)
    (Aux : MCfg L K → Prop) : Kernel (MCfg L K) (MCfg L K) :=
  Kernel.piecewise
    (DiscreteMeasurableSpace.forall_measurableSet
      (ampActiveSet (L := L) (K := K) C₀ T θ ρ η Rcap Aux))
    (markedK (L := L) (K := K) T θn)
    Kernel.id

instance (T θn C₀ : ℕ) (θ ρ η Rcap : ℝ) (Aux : MCfg L K → Prop) :
    IsMarkovKernel (KampStar (L := L) (K := K) T θn C₀ θ ρ η Rcap Aux) := by
  unfold KampStar
  infer_instance

/-- Concrete endpoint amplification event for a fixed immigration allowance. -/
def AmpGoodAtEndBudget (C₀ T : ℕ) (γ : ℝ) (mc₀ : MCfg L K) (immFrac : ℝ)
    (mc₁ : MCfg L K) : Prop :=
  AmplificationGood (L := L) (K := K) C₀ T γ mc₀ mc₁ immFrac

/--
One-step clean-rise probability bound (state-local): on `AmpActive`, the probability that
`cleanCount` rises is bounded by `qImm + cleanEpiRate`. -/
def CleanRiseProbBound
    (n C₀ T θn : ℕ) (θ ρ η Rcap qImm : ℝ) (Aux : MCfg L K → Prop) : Prop :=
  ∀ mc : MCfg L K,
    AmpActive (L := L) (K := K) C₀ T θ ρ η Rcap Aux mc →
      markedK (L := L) (K := K) T θn mc
        {mc' | cleanCount (L := L) (K := K) T mc
              < cleanCount (L := L) (K := K) T mc'} ≤
        ENNReal.ofReal (qImm + cleanEpiRate (L := L) (K := K) n C₀ T mc)

/--
One marked step raises the clean-above count by at most one (clean-count analogue of the `+1`
increment in `GhostSmallConc`; pair-update analysis). -/
def CleanRiseAtMostOne (T θn : ℕ) : Prop :=
  ∀ mc : MCfg L K,
    ∀ᵐ mc' ∂(markedK (L := L) (K := K) T θn mc),
      cleanCount (L := L) (K := K) T mc'
        ≤ cleanCount (L := L) (K := K) T mc + 1

/--
Uniform symbolic rate cap on the stopped active region (e.g.
`qAmp = qImm + 2·Rcap·C₀/(n(n−1))`, with `0 ≤ Rcap ≤ C₀`). -/
def CleanRiseRateCap
    (n C₀ T : ℕ) (θ ρ η Rcap qImm qAmp : ℝ) (Aux : MCfg L K → Prop) : Prop :=
  ∀ mc : MCfg L K,
    AmpActive (L := L) (K := K) C₀ T θ ρ η Rcap Aux mc →
      qImm + cleanEpiRate (L := L) (K := K) n C₀ T mc ≤ qAmp

/--
Unconditional exponential drift for the stopped amplification kernel (concrete analogue of
`GhostSmallConc.ghost_exp_drift`, `cleanCount` replacing `clockTaintedCount`). -/
theorem amp_exp_drift
    (n C₀ T θn : ℕ) (θ ρ η Rcap qImm qAmp : ℝ)
    (Aux : MCfg L K → Prop)
    {lam : ℝ} (hlam : 0 ≤ lam)
    (hqAmp0 : 0 ≤ qAmp)
    (hRise : CleanRiseProbBound
      (L := L) (K := K) n C₀ T θn θ ρ η Rcap qImm Aux)
    (hIncr : CleanRiseAtMostOne (L := L) (K := K) T θn)
    (hCap : CleanRiseRateCap
      (L := L) (K := K) n C₀ T θ ρ η Rcap qImm qAmp Aux) :
    ∀ mc, ∫⁻ mc', AmpPot (L := L) (K := K) T lam mc'
        ∂((KampStar (L := L) (K := K) T θn C₀ θ ρ η Rcap Aux) mc)
      ≤ ENNReal.ofReal (Real.exp (qAmp * (Real.exp lam - 1)))
          * AmpPot (L := L) (K := K) T lam mc := by
  intro mc
  classical
  set rr : ℝ≥0∞ := ENNReal.ofReal (Real.exp (qAmp * (Real.exp lam - 1))) with hrr
  have hrr_one : (1 : ℝ≥0∞) ≤ rr := by
    rw [hrr]
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp]
    apply ENNReal.ofReal_le_ofReal
    apply Real.one_le_exp
    have hnonneg : 0 ≤ Real.exp lam - 1 := by
      have h := Real.one_le_exp hlam
      linarith
    exact mul_nonneg hqAmp0 hnonneg
  unfold KampStar
  rw [Kernel.piecewise_apply]
  by_cases hx : mc ∈ ampActiveSet (L := L) (K := K) C₀ T θ ρ η Rcap Aux
  · rw [if_pos hx]
    have hact : AmpActive (L := L) (K := K) C₀ T θ ρ η Rcap Aux mc := hx
    haveI : IsProbabilityMeasure (markedK (L := L) (K := K) T θn mc) :=
      (inferInstance :
        IsMarkovKernel (markedK (L := L) (K := K) T θn)).isProbabilityMeasure mc
    set N := cleanCount (L := L) (K := K) T mc with hN
    have hprob :
        markedK (L := L) (K := K) T θn mc
          {mc' | N < cleanCount (L := L) (K := K) T mc'} ≤ ENNReal.ofReal qAmp := by
      have h0 := hRise mc hact
      have h1 : qImm + cleanEpiRate (L := L) (K := K) n C₀ T mc ≤ qAmp :=
        hCap mc hact
      refine le_trans h0 ?_
      exact ENNReal.ofReal_le_ofReal h1
    have hmgf := ClimbTail.mgf_one_step
      (markedK (L := L) (K := K) T θn mc)
      lam hlam
      (cleanCount (L := L) (K := K) T)
      N
      (by simpa [hN] using hIncr mc)
      qAmp hqAmp0 hprob
    have hmono :
        (1 : ℝ) + qAmp * (Real.exp lam - 1)
          ≤ Real.exp (qAmp * (Real.exp lam - 1)) := by
      have h := Real.add_one_le_exp (qAmp * (Real.exp lam - 1))
      linarith
    calc
      ∫⁻ mc', AmpPot (L := L) (K := K) T lam mc'
          ∂(markedK (L := L) (K := K) T θn mc)
          =
        ∫⁻ mc', ENNReal.ofReal
          (Real.exp (lam * (cleanCount (L := L) (K := K) T mc' : ℝ)))
          ∂(markedK (L := L) (K := K) T θn mc) := rfl
      _ ≤ ENNReal.ofReal
          ((1 + qAmp * (Real.exp lam - 1)) * Real.exp (lam * (N : ℝ))) := hmgf
      _ ≤ rr * AmpPot (L := L) (K := K) T lam mc := by
        rw [hrr]
        unfold AmpPot
        rw [hN, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
        apply ENNReal.ofReal_le_ofReal
        exact mul_le_mul_of_nonneg_right hmono (Real.exp_pos _).le
  · rw [if_neg hx, Kernel.id_apply, lintegral_dirac]
    calc
      AmpPot (L := L) (K := K) T lam mc
          = 1 * AmpPot (L := L) (K := K) T lam mc := (one_mul _).symm
      _ ≤ rr * AmpPot (L := L) (K := K) T lam mc := by
        gcongr

/--
Chernoff tail for the stopped amplification kernel.  `Rcap = C₀·γ·(CleanFrac C₀ T mc₀ + immFrac)`;
the theorem states the actual amplification bad event, not a free predicate. -/
theorem epidemic_amplification_tail_stopped
    (n C₀ T θn Lwin : ℕ)
    (θ ρ η γ immFrac Rcap qImm qAmp : ℝ)
    (Aux : MCfg L K → Prop)
    {lam : ℝ} (hlam : 0 ≤ lam)
    (hqAmp0 : 0 ≤ qAmp)
    (mc₀ : MCfg L K)
    (hRcap :
      Rcap = (C₀ : ℝ) * γ *
        (CleanFrac (L := L) (K := K) C₀ T mc₀ + immFrac))
    (hC₀pos : (0 : ℝ) < (C₀ : ℝ))
    (hRise : CleanRiseProbBound
      (L := L) (K := K) n C₀ T θn θ ρ η Rcap qImm Aux)
    (hIncr : CleanRiseAtMostOne (L := L) (K := K) T θn)
    (hCap : CleanRiseRateCap
      (L := L) (K := K) n C₀ T θ ρ η Rcap qImm qAmp Aux) :
    ((KampStar (L := L) (K := K) T θn C₀ θ ρ η Rcap Aux) ^ Lwin) mc₀
      {mc₁ | ¬ AmpGoodAtEndBudget (L := L) (K := K) C₀ T γ mc₀ immFrac mc₁}
      ≤
        ENNReal.ofReal (Real.exp (qAmp * (Real.exp lam - 1))) ^ Lwin
          * AmpPot (L := L) (K := K) T lam mc₀
          / ENNReal.ofReal (Real.exp (lam * Rcap)) := by
  classical
  have hsub_set :
      {mc₁ : MCfg L K |
        ¬ AmpGoodAtEndBudget (L := L) (K := K) C₀ T γ mc₀ immFrac mc₁}
        ⊆
      {mc₁ : MCfg L K |
        ENNReal.ofReal (Real.exp (lam * Rcap))
          ≤ AmpPot (L := L) (K := K) T lam mc₁} := by
    intro mc₁ hbad
    rw [Set.mem_setOf_eq] at hbad ⊢
    unfold AmpGoodAtEndBudget AmplificationGood CleanFrac at hbad
    unfold AmpPot cleanCount
    push Not at hbad
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_left ?_ hlam
    have hCne : (C₀ : ℝ) ≠ 0 := hC₀pos.ne'
    have key : (C₀ : ℝ) * γ * (CleanFrac (L := L) (K := K) C₀ T mc₀ + immFrac)
        ≤ (clockCleanAbove (L := L) (K := K) T mc₁ : ℝ) := by
      unfold CleanFrac
      rw [mul_assoc]
      have h := mul_le_mul_of_nonneg_left (le_of_lt hbad) hC₀pos.le
      refine h.trans (le_of_eq ?_)
      field_simp
    rw [hRcap]
    exact key
  refine le_trans (measure_mono hsub_set) ?_
  have hθ0 : ENNReal.ofReal (Real.exp (lam * Rcap)) ≠ 0 := by
    simp [ENNReal.ofReal_eq_zero, not_le, Real.exp_pos]
  have hθtop : ENNReal.ofReal (Real.exp (lam * Rcap)) ≠ ∞ :=
    ENNReal.ofReal_ne_top
  exact geometric_drift_tail
    (KampStar (L := L) (K := K) T θn C₀ θ ρ η Rcap Aux)
    (AmpPot (L := L) (K := K) T lam)
    (AmpPot_measurable (L := L) (K := K) T lam)
    (ENNReal.ofReal (Real.exp (qAmp * (Real.exp lam - 1))))
    (amp_exp_drift
      (L := L) (K := K)
      n C₀ T θn θ ρ η Rcap qImm qAmp Aux
      hlam hqAmp0 hRise hIncr hCap)
    Lwin mc₀
    (ENNReal.ofReal (Real.exp (lam * Rcap)))
    hθ0 hθtop

/--
A symbolic budgeted version of the amplification tail (instantiate `γ = 6/5`, `w = 9/100`,
`λ = log n / 100`); the arithmetic obligation `hBudget` says the MGF compensator is dominated by the
desired probability budget. -/
theorem epidemic_amplification_window_budget
    (n C₀ T θn Lwin : ℕ)
    (θ ρ η γ immFrac Rcap qImm qAmp : ℝ)
    (Aux : MCfg L K → Prop)
    {lam : ℝ} (hlam : 0 ≤ lam)
    (hqAmp0 : 0 ≤ qAmp)
    (mc₀ : MCfg L K)
    (hRcap :
      Rcap = (C₀ : ℝ) * γ *
        (CleanFrac (L := L) (K := K) C₀ T mc₀ + immFrac))
    (hC₀pos : (0 : ℝ) < (C₀ : ℝ))
    (hRise : CleanRiseProbBound
      (L := L) (K := K) n C₀ T θn θ ρ η Rcap qImm Aux)
    (hIncr : CleanRiseAtMostOne (L := L) (K := K) T θn)
    (hCap : CleanRiseRateCap
      (L := L) (K := K) n C₀ T θ ρ η Rcap qImm qAmp Aux)
    (εAmp : ℝ≥0∞)
    (hBudget :
      ENNReal.ofReal (Real.exp (qAmp * (Real.exp lam - 1))) ^ Lwin
          * AmpPot (L := L) (K := K) T lam mc₀
          / ENNReal.ofReal (Real.exp (lam * Rcap))
        ≤ εAmp) :
    ((KampStar (L := L) (K := K) T θn C₀ θ ρ η Rcap Aux) ^ Lwin) mc₀
      {mc₁ | ¬ AmpGoodAtEndBudget (L := L) (K := K) C₀ T γ mc₀ immFrac mc₁}
      ≤ εAmp :=
  le_trans
    (epidemic_amplification_tail_stopped
      (L := L) (K := K)
      n C₀ T θn Lwin θ ρ η γ immFrac Rcap qImm qAmp Aux
      hlam hqAmp0 mc₀ hRcap hC₀pos hRise hIncr hCap)
    hBudget

/--
**Immigration is subsumed into the amplification budget.**  Witnessing `WindowCleanGood` with the
START-fixed allowance `immFrac = b·p·X(mc₀)²`, `DripImmigrationGood` follows DETERMINISTICALLY from
parent growth (`X(mc₀) ≤ a·X(mc₁)` with `a ≤ 1` gives `X(mc₀)² ≤ X(mc₁)²`, hence
`b·p·X(mc₀)² ≤ b·p·X(mc₁)²`), and the amplification clause is exactly `AmplificationGood` at that
allowance — proved whp by `epidemic_amplification_window_budget` (whose MGF rate `qAmp = qImm +
cleanEpiRate` already accounts for the immigration drips).  So NO separate Bennett immigration tail /
counter kernel is needed: the immigration's probabilistic content lives in `qImm`, and its budget is
this fixed `immFrac`. -/
theorem windowCleanGood_of_amp_budget (C₀ T : ℕ) (p a b γ : ℝ) (mc₀ mc₁ : MCfg L K)
    (hp0 : 0 ≤ p) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b)
    (hparent : ParentGrowthGood (L := L) (K := K) C₀ T a mc₀ mc₁)
    (hamp : AmplificationGood (L := L) (K := K) C₀ T γ mc₀ mc₁
      (b * p * (X (L := L) (K := K) C₀ T mc₀) ^ 2)) :
    WindowCleanGood (L := L) (K := K) C₀ T p b γ mc₀ mc₁ := by
  refine ⟨b * p * (X (L := L) (K := K) C₀ T mc₀) ^ 2, ?_, ?_, hamp⟩
  · have hX0 : 0 ≤ X (L := L) (K := K) C₀ T mc₀ := by unfold X ClockFrac; positivity
    positivity
  · -- `b·p·X(mc₀)² ≤ b·p·X(mc₁)²` via `X(mc₀) ≤ a·X(mc₁) ≤ X(mc₁)`.
    have hX0 : 0 ≤ X (L := L) (K := K) C₀ T mc₀ := by unfold X ClockFrac; positivity
    have hX1 : 0 ≤ X (L := L) (K := K) C₀ T mc₁ := by unfold X ClockFrac; positivity
    have hkey : X (L := L) (K := K) C₀ T mc₀ ≤ X (L := L) (K := K) C₀ T mc₁ := by
      have hpar : X (L := L) (K := K) C₀ T mc₀ ≤ a * X (L := L) (K := K) C₀ T mc₁ := hparent
      nlinarith [hpar, ha1, hX1]
    have hsq : (X (L := L) (K := K) C₀ T mc₀) ^ 2 ≤ (X (L := L) (K := K) C₀ T mc₁) ^ 2 := by
      nlinarith [hkey, hX0, hX1]
    nlinarith [hsq, mul_nonneg hb0 hp0]

end ClockLayerB
end ExactMajority
