import Ripple.PopulationProtocol.ExactMajority.Probability.TraceDrain
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockProducer

/-!
# Stopped actual-trace drift for Phase-3 averaging

This file supplies the stopping-time lifting of a kernel drift estimate.
It does not assert the protocol-specific mixed-mass or immigration drift:
those hypotheses must be proved for the full implemented transition.

All measures below are the original pair-log law. Intersecting the bad event
with clock success only restricts that event; it does not condition the law
on clock success.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal BigOperators MeasureTheory ProbabilityTheory

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeAveragingStops

open TimeTheorem PairLog TraceDrain PhaseOneDrain
open StageEventSpec PhaseThreeClockProducer

variable {L K : ℕ}

/-- Monotonicity on the actual trace, for a quantity valued in any preorder. -/
theorem trace_value_le_of_window {α : Type*} [Preorder α]
    (init : Cfg L K) (ω : Ω L K) (f : Cfg L K → α)
    (W : Cfg L K → Prop)
    (hstep : ∀ c, W c → ∀ d, f (applyDraw c d) ≤ f c)
    (u v : ℕ) (huv : u ≤ v)
    (hW : ∀ k, u ≤ k → k < v → W (trace init ω k)) :
    f (trace init ω v) ≤ f (trace init ω u) := by
  induction v, huv using Nat.le_induction with
  | base => exact le_rfl
  | succ v huv ih =>
      rw [TraceDrain.trace_succ]
      exact (hstep _ (hW v huv (Nat.lt_succ_self v)) _).trans
        (ih fun k hk hk' => hW k hk (by omega))

/-- The corresponding persistence statement for a nondecreasing credit. -/
theorem trace_value_ge_of_window {α : Type*} [Preorder α]
    (init : Cfg L K) (ω : Ω L K) (f : Cfg L K → α)
    (W : Cfg L K → Prop)
    (hstep : ∀ c, W c → ∀ d, f c ≤ f (applyDraw c d))
    (u v : ℕ) (huv : u ≤ v)
    (hW : ∀ k, u ≤ k → k < v → W (trace init ω k)) :
    f (trace init ω u) ≤ f (trace init ω v) := by
  induction v, huv using Nat.le_induction with
  | base => exact le_rfl
  | succ v huv ih =>
      rw [TraceDrain.trace_succ]
      exact (ih fun k hk hk' => hW k hk (by omega)).trans
        (hstep _ (hW v huv (Nat.lt_succ_self v)) _)

/-- A finite observed start, a bounded initial potential, gate survival, and
a positive potential at the fixed offset. -/
def driftFailureAt (init : Cfg L K) (σ : Ω L K → WithTop ℕ)
    (ψ : Cfg L K → ℕ) (W : Cfg L K → Prop) (N Ψ : ℕ) :
    Set (Ω L K) :=
  {ω | ∃ s : ℕ, σ ω = (s : WithTop ℕ) ∧
    ψ (trace init ω s) ≤ Ψ ∧
    (∀ u, s ≤ u → u < s + N → W (trace init ω u)) ∧
    1 ≤ ψ (trace init ω (s + N))}

/-- Splice the prefix drift bound over the disjoint finite values of a
pair-log stopping time. There is no factor counting possible start times. -/
theorem potential_drift_tail_at_pastTime
    (init : Cfg L K) (σ : Ω L K → WithTop ℕ)
    (hσ : PairLogPastTime σ)
    (ψ : Cfg L K → ℕ) (W : Cfg L K → Prop) (ρ : ℝ≥0∞)
    (hdrift : ∀ c, W c →
      ∫⁻ c', (ψ c' : ℝ≥0∞)
          ∂(NonuniformMajority L K).transitionKernel c ≤
        (1 - ρ) * ψ c)
    (N Ψ : ℕ) :
    law init (driftFailureAt init σ ψ W N Ψ) ≤
      (1 - ρ) ^ N * Ψ := by
  refine PhaseThreeClockProducer.splice_of_local (law init) σ
    (driftFailureAt init σ ψ W N Ψ) ((1 - ρ) ^ N * Ψ)
    (fun s => (pairLogFiltration L K).le s _ (hσ s)) ?_ ?_
  · intro ω hω
    obtain ⟨s, hs, -, -, -⟩ := hω
    rw [hs]
    exact WithTop.coe_ne_top
  · intro s
    have hσs := hσ s
    rw [pairLogFiltration_eq_comap] at hσs
    obtain ⟨Aσ, -, hAσ⟩ := hσs
    let A : Set ((k : Finset.Iic s) → Draw L K) :=
      {p | p ∈ Aσ ∧ ψ (prefixCfg init s p) ≤ Ψ}
    have hmem (ω : Ω L K) :
        frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ Aσ ↔
          σ ω = (s : WithTop ℕ) := by
      change ω ∈ frestrictLe (π := fun _ : ℕ => Draw L K) s ⁻¹' Aσ ↔
        ω ∈ {ω | σ ω = (s : WithTop ℕ)}
      rw [hAσ]
    calc
      law init
          (driftFailureAt init σ ψ W N Ψ ∩
            {ω | σ ω = (s : WithTop ℕ)}) ≤
          law init {ω |
            frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A ∧
            (∀ u, s ≤ u → u < s + N → W (trace init ω u)) ∧
            1 ≤ ψ (trace init ω (s + N))} := by
              apply measure_mono
              rintro ω ⟨⟨s', hs', hstart, hwindow, hfinal⟩, hs⟩
              have hss : s' = s :=
                WithTop.coe_injective (hs'.symm.trans hs)
              subst s'
              exact ⟨⟨(hmem ω).mpr hs, hstart⟩, hwindow, hfinal⟩
      _ ≤ (1 - ρ) ^ N * Ψ *
          law init {ω |
            frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A} :=
        TraceDrain.potential_drift_tail_from init ψ W ρ hdrift
          s N A Ψ (fun _ hp => hp.2)
      _ ≤ ((1 - ρ) ^ N * Ψ) *
          law init {ω | σ ω = (s : WithTop ℕ)} :=
        mul_le_mul_left'
          (measure_mono fun ω hω => (hmem ω).mp hω.1) _

/-- Adding any future event gives a joint-event bound under the same law.
No measurability or independence assumption on that event is needed. -/
theorem potential_drift_tail_on_event
    (init : Cfg L K) (σ : Ω L K → WithTop ℕ)
    (hσ : PairLogPastTime σ)
    (ψ : Cfg L K → ℕ) (W : Cfg L K → Prop) (ρ : ℝ≥0∞)
    (hdrift : ∀ c, W c →
      ∫⁻ c', (ψ c' : ℝ≥0∞)
          ∂(NonuniformMajority L K).transitionKernel c ≤
        (1 - ρ) * ψ c)
    (N Ψ : ℕ) (G : Set (Ω L K)) :
    law init (G ∩ driftFailureAt init σ ψ W N Ψ) ≤
      (1 - ρ) ^ N * Ψ :=
  (measure_mono Set.inter_subset_right).trans
    (potential_drift_tail_at_pastTime init σ hσ ψ W ρ hdrift N Ψ)

/-- A specialization at the genuine first Phase-3 seed. The input event is
exactly the complement of the plan's clock failure event. This complement
also contains paths outside the entry event; extracting a ClockHistory requires
entry success separately. -/
theorem potential_drift_tail_on_clock_success
    {n : ℕ} (init : InputCfg n)
    (ψ : Cfg (PhaseThreeModel.Numeric.hourIndex n) 256 → ℕ)
    (W : Cfg (PhaseThreeModel.Numeric.hourIndex n) 256 → Prop)
    (ρ : ℝ≥0∞)
    (hdrift : ∀ c, W c →
      ∫⁻ c', (ψ c' : ℝ≥0∞)
          ∂(NonuniformMajority
            (PhaseThreeModel.Numeric.hourIndex n) 256).transitionKernel c ≤
        (1 - ρ) * ψ c)
    (N Ψ : ℕ) :
    law init
      ((phaseClockFailure (reviewedStageEvents n init))ᶜ ∩
        driftFailureAt init (seedTime init 3) ψ W N Ψ) ≤
      (1 - ρ) ^ N * Ψ :=
  potential_drift_tail_on_event init (seedTime init 3)
    (seedTime_pastTime init 3) ψ W ρ hdrift N Ψ
    ((phaseClockFailure (reviewedStageEvents n init))ᶜ)

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeAveragingStops

end
