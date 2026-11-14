-- Ripple/PopulationProtocol/ExactMajority/Probability/LateMixedFiveSixWindowFirstExitWf.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.LateMixedFiveSixReachableWf

/-!
# Reachable-Wf first exit for the Phase-5/6 no-overshoot window

The old first-exit theorem used a false global deterministic bridge.  This
file restricts the first-exit invariant to configurations that are reachable
from a valid initial configuration and whose phases are at least two.  Inside
`NoOvershoot p`, with `p ≤ 8`, `LateMixedFiveSixReachableWf` then supplies
`Wf`, so the genuine per-configuration bridge from `AdvanceOvershootSource` applies.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

namespace Ripple.PopulationProtocol.ExactMajority.LateMixedFiveSixWindowFirstExitWf

open TimeTheorem PairLog
open PhaseOneDrainStopping TraceDrain
open AdvanceNoOvershoot
open LateMixedFiveSixReachableWf

variable {L K : ℕ}

/-- The restricted first-exit invariant. -/
def ReachableNoOvershootWindow
    (init : Config (AgentState L K)) (p : ℕ)
    (c : Config (AgentState L K)) : Prop :=
  NoOvershoot (L := L) (K := K) p c ∧
    (NonuniformMajority L K).Reachable init c ∧
      ∀ a ∈ c, 2 ≤ a.phase.val

/-- Every recorded finite prefix is genuinely reachable from its initial
configuration. -/
theorem prefixCfg_reachable
    (init : Config (AgentState L K)) (s : ℕ)
    (a : (k : Finset.Iic s) → Draw L K) :
    (NonuniformMajority L K).Reachable init (prefixCfg init s a) := by
  induction s with
  | zero =>
      exact Relation.ReflTransGen.refl
  | succ s ih =>
      let b := restrictPrefix (Nat.le_succ s) a
      change (NonuniformMajority L K).Reachable init
        (applyDraw (prefixCfg init s b)
          (a ⟨s + 1, Finset.mem_Iic.mpr le_rfl⟩))
      exact (ih b).trans (applyDraw_reachable _ _)

/-- The upper-bound check: `NoOvershoot 5` is much stronger than
phase `≤ 9`; it gives phase `< 7`. -/
theorem noOvershoot_five_phase_le_nine
    (c : Config (AgentState L K))
    (hno : NoOvershoot (L := L) (K := K) 5 c) :
    ∀ a ∈ c, a.phase.val ≤ 9 := by
  intro a ha
  have h := hno a ha
  omega

/-- `LateMixedFiveSixReachableWf` turns the restricted invariant into the
well-formedness needed by the genuine overshoot-source bridge. -/
theorem reachableNoOvershootWindow_wf
    (init c : Config (AgentState L K)) (p : ℕ)
    (hvalid : validInitial init) (hp : p ≤ 8)
    (hwindow : ReachableNoOvershootWindow init p c) :
    Wf (L := L) (K := K) c := by
  exact wf_of_reachable_phase_range
    hvalid hwindow.2.1 hwindow.2.2
    (fun a ha => by
      have hupper := hwindow.1 a ha
      omega)

/-- Reachability and the phase lower bound are one-step invariants.  Thus a
chosen-pair update can leave the restricted window only by leaving
`NoOvershoot`. -/
theorem reachableNoOvershootWindow_step_of_noOvershoot
    (init c : Config (AgentState L K)) (p : ℕ)
    (hwindow : ReachableNoOvershootWindow init p c)
    (r₁ r₂ : AgentState L K)
    (hnext : NoOvershoot (L := L) (K := K) p
      (Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂)) :
    ReachableNoOvershootWindow init p
      (Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂) := by
  have hreach := Protocol.reachable_stepOrSelf
    (P := NonuniformMajority L K) c r₁ r₂
  refine ⟨hnext, hwindow.2.1.trans hreach, ?_⟩
  exact phase_lower_reachable
    (L := L) (K := K) 2 c
    (Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂)
    hreach hwindow.2.2

/-- Kernel form for the restricted invariant.  Under the safe precursor
condition, a one-step kernel transition has zero mass outside the restricted
window. -/
theorem transitionKernel_not_reachableNoOvershootWindow_eq_zero
    (init : Config (AgentState L K))
    (hvalid : validInitial init)
    (p : ℕ) (hp : p ≤ 8)
    (hq : CounterResetDest (p + 1))
    (c : Config (AgentState L K))
    (hwindow : ReachableNoOvershootWindow init p c)
    (hsafe : ¬ AtRiskClockZero (L := L) (K := K) p c) :
    (NonuniformMajority L K).transitionKernel c
      {c' | ¬ ReachableNoOvershootWindow init p c'} = 0 := by
  have hwf := reachableNoOvershootWindow_wf
    init c p hvalid hp hwindow
  change ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
      {c' | ¬ ReachableNoOvershootWindow init p c'} = 0
  rw [PMF.toMeasure_apply_eq_zero_iff _
    (DiscreteMeasurableSpace.forall_measurableSet _)]
  rw [Set.disjoint_left]
  intro c' hsupp hbad
  change ¬ ReachableNoOvershootWindow init p c' at hbad
  unfold Protocol.stepDistOrSelf at hsupp
  by_cases hc2 : 2 ≤ c.card
  · rw [dif_pos hc2] at hsupp
    obtain ⟨⟨r₁, r₂⟩, hr⟩ :=
      Protocol.stepDist_support _ c hc2 c' hsupp
    have heq :
        Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂ = c' := by
      rw [show Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂ =
          Protocol.scheduledStep (NonuniformMajority L K) c (r₁, r₂) from rfl,
        hr]
    have hexit :
        ¬ NoOvershoot (L := L) (K := K) p
          (Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂) := by
      intro hnext
      apply hbad
      rw [← heq]
      exact reachableNoOvershootWindow_step_of_noOvershoot
        init c p hwindow r₁ r₂ hnext
    exact hsafe
      (overshoot_forces_zeroClock_of_wf
        p hq c r₁ r₂ hwf hwindow.1 hexit)
  · rw [dif_neg hc2, PMF.mem_support_pure_iff] at hsupp
    subst c'
    exact hbad hwindow

/-- Per-configuration replacement for the false global bridge. -/
theorem transitionKernel_not_noOvershoot_eq_zero_wf
    (init : Config (AgentState L K))
    (hvalid : validInitial init)
    (p : ℕ) (hp : p ≤ 8)
    (hq : CounterResetDest (p + 1))
    (c : Config (AgentState L K))
    (hreach : (NonuniformMajority L K).Reachable init c)
    (hlower : ∀ a ∈ c, 2 ≤ a.phase.val)
    (hno : NoOvershoot (L := L) (K := K) p c)
    (hsafe : ¬ AtRiskClockZero (L := L) (K := K) p c) :
    (NonuniformMajority L K).transitionKernel c
      {c' | ¬ NoOvershoot (L := L) (K := K) p c'} = 0 := by
  have hwindow : ReachableNoOvershootWindow init p c :=
    ⟨hno, hreach, hlower⟩
  have hz := transitionKernel_not_reachableNoOvershootWindow_eq_zero
    init hvalid p hp hq c hwindow hsafe
  apply le_antisymm
  · calc
      (NonuniformMajority L K).transitionKernel c
          {c' | ¬ NoOvershoot (L := L) (K := K) p c'} ≤
        (NonuniformMajority L K).transitionKernel c
          {c' | ¬ ReachableNoOvershootWindow init p c'} := by
            apply measure_mono
            intro d hd
            change ¬ NoOvershoot (L := L) (K := K) p d at hd
            change ¬ ReachableNoOvershootWindow init p d
            intro hA
            exact hd hA.1
      _ = 0 := hz
  · exact zero_le

/-- First-exit prefix union with the reachable invariant.  The public left
side remains the desired no-overshoot failure event; reachability and the
phase lower bound cannot be the first lost conjunct. -/
theorem noOvershoot_window_le_prefix_sum_wf
    (init : Config (AgentState L K))
    (hvalid : validInitial init)
    (p : ℕ) (hp : p ≤ 8)
    (hq : CounterResetDest (p + 1))
    (t : ℕ) (c₀ : Config (AgentState L K))
    (hreach : (NonuniformMajority L K).Reachable init c₀)
    (hlower : ∀ a ∈ c₀, 2 ≤ a.phase.val)
    (h0 : NoOvershoot (L := L) (K := K) p c₀) :
    ((NonuniformMajority L K).transitionKernel ^ t) c₀
        {c | ¬ NoOvershoot (L := L) (K := K) p c} ≤
      ∑ τ ∈ Finset.range t,
        ((NonuniformMajority L K).transitionKernel ^ τ) c₀
          {c | ¬ ¬ AtRiskClockZero (L := L) (K := K) p c} := by
  have hfirst :=
    Phase0Window.prefix_union_first_exit
      (NonuniformMajority L K).transitionKernel
      (ReachableNoOvershootWindow (L := L) (K := K) init p)
      (fun c => ¬ AtRiskClockZero (L := L) (K := K) p c)
      (fun x hA hG =>
        transitionKernel_not_reachableNoOvershootWindow_eq_zero
          init hvalid p hp hq x hA hG)
      t c₀ ⟨h0, hreach, hlower⟩
  refine (measure_mono ?_).trans hfirst
  intro d hd
  change ¬ NoOvershoot (L := L) (K := K) p d at hd
  change ¬ ReachableNoOvershootWindow init p d
  intro hA
  exact hd hA.1

/-!
THEOREM LIST
* `prefixCfg_reachable`
* `noOvershoot_five_phase_le_nine`
* `reachableNoOvershootWindow_wf`
* `reachableNoOvershootWindow_step_of_noOvershoot`
* `transitionKernel_not_reachableNoOvershootWindow_eq_zero`
* `transitionKernel_not_noOvershoot_eq_zero_wf`
* `noOvershoot_window_le_prefix_sum_wf`

CLOSES
* The per-configuration replacement for the false global
  `OvershootForcesZeroClock 5` use.
* The restricted first-exit invariant and proof that only `NoOvershoot` can be
  its first lost conjunct.
* Automatic `Wf` from valid-initial reachability, phase lower bound two, and
  `NoOvershoot p` for `p ≤ 8`.

UNFINISHED
* Nothing in the first-exit bridge.  The Phase-6 dispatch fact remains an
  explicit input of the tail module.
END
-/

end Ripple.PopulationProtocol.ExactMajority.LateMixedFiveSixWindowFirstExitWf

end
