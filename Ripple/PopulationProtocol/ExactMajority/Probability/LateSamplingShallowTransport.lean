-- Ripple/PopulationProtocol/ExactMajority/Probability/LateSamplingShallowTransport.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.LateSeedMixedPositive
import Ripple.PopulationProtocol.ExactMajority.Probability.LateF6OriginalLaw

/-!
# Shallow-majority transport through the actual Phase-3/4/5 window

For a pair whose maximum phase is at least four, the actual transition
preserves each participant's role and bias. Since every input agent is already
at phase at least three and phase is monotone, `mixedShallowAgent` is then
exactly invariant.

If the maximum input phase is below four, both inputs are in Phase 3. The
existing Phase-3 dispatcher theorem gives the required nonincrease.

The resulting trace theorem discharges the
`hshallowTransport` premise of `LateSamplingClassReceiptArithmetic` without any additional probabilistic or
future-dependent input.
-/

noncomputable section

namespace Ripple.PopulationProtocol.ExactMajority.LateSamplingShallowTransport

open TimeTheorem PairLog
open LateStrengthening LateF6Acceptance LateF6OriginalLaw

variable {L n : ℕ}

/-- Once a mixed-window interaction has maximum input phase at least four,
the left participant's shallow contribution is exactly preserved. -/
theorem mixedShallowAgent_left_eq_of_freeze
    (σ : Sign) (ell : ℕ) (s t : AgentState L 256)
    (hs : Window s) (ht : Window t)
    (hmax : 4 ≤ max s.phase.val t.phase.val) :
    mixedShallowAgent σ ell (Transition L 256 s t).1 =
      mixedShallowAgent σ ell s := by
  have hs3 : 3 ≤ s.phase.val := hs.1
  have ht3 : 3 ≤ t.phase.val := ht.1
  have hfields := transition_freeze_fields s t hs ht hmax
  have hmono :
      s.phase.val ≤ (Transition L 256 s t).1.phase.val :=
    (Transition_phase_monotone (L := L) (K := 256) s t).1
  have hsource : ¬ s.phase.val < 3 := by
    omega
  have houtput : ¬ (Transition L 256 s t).1.phase.val < 3 := by
    omega
  simp only [mixedShallowAgent, if_neg houtput, if_neg hsource,
    activeShallowAgent, hfields.1, hfields.2.1]

/-- Once a mixed-window interaction has maximum input phase at least four,
the right participant's shallow contribution is exactly preserved. -/
theorem mixedShallowAgent_right_eq_of_freeze
    (σ : Sign) (ell : ℕ) (s t : AgentState L 256)
    (hs : Window s) (ht : Window t)
    (hmax : 4 ≤ max s.phase.val t.phase.val) :
    mixedShallowAgent σ ell (Transition L 256 s t).2 =
      mixedShallowAgent σ ell t := by
  have hs3 : 3 ≤ s.phase.val := hs.1
  have ht3 : 3 ≤ t.phase.val := ht.1
  have hfields := transition_freeze_fields s t hs ht hmax
  have hmono :
      t.phase.val ≤ (Transition L 256 s t).2.phase.val :=
    (Transition_phase_monotone (L := L) (K := 256) s t).2
  have hsource : ¬ t.phase.val < 3 := by
    omega
  have houtput : ¬ (Transition L 256 s t).2.phase.val < 3 := by
    omega
  simp only [mixedShallowAgent, if_neg houtput, if_neg hsource,
    activeShallowAgent, hfields.2.2.1, hfields.2.2.2]

/-- Every actual pair interaction inside the Phase-3/4/5 window is
nonincreasing for the pending-aware shallow-majority charge. -/
theorem transition_mixedShallow_pair_le_of_window
    (σ : Sign) (ell : ℕ) (s t : AgentState L 256)
    (hs : Window s) (ht : Window t) :
    mixedShallowAgent σ ell (Transition L 256 s t).1 +
        mixedShallowAgent σ ell (Transition L 256 s t).2 ≤
      mixedShallowAgent σ ell s + mixedShallowAgent σ ell t := by
  have hs3 : 3 ≤ s.phase.val := hs.1
  have ht3 : 3 ≤ t.phase.val := ht.1
  by_cases hfreeze : 4 ≤ max s.phase.val t.phase.val
  · rw [
      mixedShallowAgent_left_eq_of_freeze
        (L := L) σ ell s t hs ht hfreeze,
      mixedShallowAgent_right_eq_of_freeze
        (L := L) σ ell s t hs ht hfreeze]
  · have hlt : max s.phase.val t.phase.val < 4 := by
      omega
    have hsmax : s.phase.val ≤ max s.phase.val t.phase.val :=
      le_max_left _ _
    have htmax : t.phase.val ≤ max s.phase.val t.phase.val :=
      le_max_right _ _
    have hsphase : s.phase.val = 3 := by
      omega
    have htphase : t.phase.val = 3 := by
      omega
    have hepi :=
      ClockRealKernel.phaseEpidemicUpdate_eq_self_p3
        s t hsphase htphase
    have hleft :
        (phaseEpidemicUpdate L 256 s t).1.phase.val = 3 := by
      rw [hepi]
      exact hsphase
    have hright :
        (phaseEpidemicUpdate L 256 s t).2.phase.val = 3 := by
      rw [hepi]
      exact htphase
    have hpair :=
      transition_shallow_le_epidemic σ ell s t hleft hright
    rw [hepi] at hpair
    exact hpair

/-- Configuration form for one selected unordered pair. The inapplicable
case is the identity branch of `stepOrSelf`. -/
theorem mixedShallowPositive_stepOrSelf_of_window
    (σ : Sign) (ell : ℕ) (c : Cfg L 256)
    (s t : AgentState L 256)
    (hwindow : ∀ a ∈ c, Window a) :
    mixedShallowPositive σ ell
        (Protocol.stepOrSelf (NonuniformMajority L 256) c s t) ≤
      mixedShallowPositive σ ell c := by
  classical
  by_cases happ : Protocol.Applicable c s t
  · have hs : s ∈ c :=
      Multiset.mem_of_le happ (by simp)
    have ht : t ∈ c :=
      Multiset.mem_of_le happ (by simp)
    have hstep :
        Protocol.stepOrSelf (NonuniformMajority L 256) c s t =
          c - {s, t} +
            {(Transition L 256 s t).1,
              (Transition L 256 s t).2} := by
      unfold Protocol.stepOrSelf
      rw [if_pos happ]
      rfl
    have hpair :=
      transition_mixedShallow_pair_le_of_window
        σ ell s t (hwindow s hs) (hwindow t ht)
    have hsplit :
        c = c - {s, t} +
          ({s, t} : Multiset (AgentState L 256)) := by
      rw [Multiset.sub_add_cancel
        (show ({s, t} : Multiset (AgentState L 256)) ≤ c from happ)]
    rw [hstep, mixedShallowPositive_add_pair]
    conv_rhs => rw [hsplit]
    rw [mixedShallowPositive_add_pair]
    exact add_le_add le_rfl hpair
  · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]

/-- Draw-level form, including the no-draw identity case. -/
theorem mixedShallowPositive_draw_of_window
    (σ : Sign) (ell : ℕ) (c : Cfg L 256) (d : Draw L 256)
    (hwindow : ∀ a ∈ c, Window a) :
    mixedShallowPositive σ ell (applyDraw c d) ≤
      mixedShallowPositive σ ell c := by
  cases d with
  | none =>
      exact le_rfl
  | some p =>
      exact mixedShallowPositive_stepOrSelf_of_window
        σ ell c p.1.1 p.2.1 hwindow

/-- Generic trace transport through a window known at every pre-step
configuration. No scheduler or stopping-time probability is used. -/
theorem mixedShallowPositive_trace_le_of_window
    (σ : Sign) (ell : ℕ)
    (init : Cfg L 256) (ω : Ω L 256)
    (s t : ℕ) (hst : s ≤ t)
    (hwindow : ∀ u, s ≤ u → u < t →
      ∀ a ∈ trace init ω u, Window a) :
    mixedShallowPositive σ ell (trace init ω t) ≤
      mixedShallowPositive σ ell (trace init ω s) := by
  revert hwindow
  induction t, hst using Nat.le_induction with
  | base =>
      intro _
      exact le_rfl
  | succ t hst ih =>
      intro hwindow
      have hprev :=
        ih (fun u hsu hut =>
          hwindow u hsu (by omega))
      have hnext :
          mixedShallowPositive σ ell (trace init ω (t + 1)) ≤
            mixedShallowPositive σ ell (trace init ω t) := by
        rw [TimeTheorem.trace_succ]
        exact mixedShallowPositive_draw_of_window
          σ ell (trace init ω t) (ω (t + 1))
          (hwindow t hst (by omega))
      exact hnext.trans hprev

/-- Any two observed snapshots in one actual pre-Phase-6 prefix satisfy
shallow-majority monotonicity. -/
theorem scaledShallowPositive_observed_mono
    {init : InputCfg n} {ω : InputLog n}
    {a s t u v ell : ℕ} {σ : Sign}
    (hpath : Prefix init ω a s t)
    (hsu : s ≤ u) (huv : u ≤ v) (hvt : v ≤ t) :
    scaledShallowPositive σ ell (trace init ω v) ≤
      scaledShallowPositive σ ell (trace init ω u) := by
  have hmix :=
    mixedShallowPositive_trace_le_of_window
      (L := PhaseThreeModel.Numeric.hourIndex n)
      σ ell init ω u v huv
      (fun r hur hrv x hx =>
        hpath.window r
          (hpath.start_order.trans (hsu.trans hur))
          ((Nat.le_of_lt hrv).trans hvt) x hx)
  have hsource :
      ∀ x ∈ trace init ω u, 3 ≤ x.phase.val := by
    intro x hx
    exact
      (hpath.window u
        (hpath.start_order.trans hsu)
        (huv.trans hvt) x hx).1
  have htarget :
      ∀ x ∈ trace init ω v, 3 ≤ x.phase.val := by
    intro x hx
    exact
      (hpath.window v
        (hpath.start_order.trans (hsu.trans huv))
        hvt x hx).1
  calc
    scaledShallowPositive σ ell (trace init ω v) =
        mixedShallowPositive σ ell (trace init ω v) :=
      (mixedShallowPositive_eq_scaledShallowPositive
        σ ell (trace init ω v) htarget).symm
    _ ≤ mixedShallowPositive σ ell (trace init ω u) :=
      hmix
    _ = scaledShallowPositive σ ell (trace init ω u) :=
      mixedShallowPositive_eq_scaledShallowPositive
        σ ell (trace init ω u) hsource

/-- The exact input required by `LateSamplingClassReceiptArithmetic`: the shallow-majority readout at any later
actual snapshot is bounded by its value at the genuine Phase-4 seed. -/
theorem scaledShallowPositive_seed_mono
    {init : InputCfg n} {ω : InputLog n}
    {a s t v ell : ℕ} {σ : Sign}
    (hpath : Prefix init ω a s t)
    (hsv : s ≤ v) (hvt : v ≤ t) :
    scaledShallowPositive σ ell (trace init ω v) ≤
      scaledShallowPositive σ ell (trace init ω s) :=
  scaledShallowPositive_observed_mono
    (u := s) (v := v) (ell := ell) (σ := σ)
    hpath le_rfl hsv hvt

end Ripple.PopulationProtocol.ExactMajority.LateSamplingShallowTransport

end
