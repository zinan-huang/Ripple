-- Ripple/PopulationProtocol/ExactMajority/Probability/LateThresholdAcceptedCounterCoupling.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.LateSamplingRowTwoCounterRepair

/-!
# Threshold-aware accepted-counter coupling and terminal retention

This file supersedes the pathwise part of `LateAcceptedCounterCoupling` for the
row-two zero slot.  The event and bad rectangles are unchanged.  Only the
absorbing gate is replaced by `ThresholdAcceptedGate`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder Set
open scoped ENNReal BigOperators

namespace Ripple.PopulationProtocol.ExactMajority.LateThresholdAcceptedCounterCoupling

open TimeTheorem PairLog PairLogAuxiliary
open LateF6Acceptance LateF6Hazards LateF6OriginalLaw
open LateAcceptedRectangleHazard LateSamplingCounterTail
open LateSamplingEarlyRoles LateSamplingFirstHit
open LateSamplingClassGates LateFrozenPoolOriginalLaw
open LateAcceptedCounterCoupling
open LateSamplingRowTwoCounterRepair

variable {L K n : ℕ}

private theorem label_mem_trace
    (init : Cfg L K) (ω : Ω L K) (u : ℕ) (i : Fin init.card) :
    labelsAt init ω u i ∈ trace init ω u := by
  rw [← labelsAt_config init ω u]
  exact Multiset.mem_map.mpr ⟨i, by simp, rfl⟩

/-- The repaired counter never counts an accepted write absent from the
actual accepted pool. -/
theorem thresholdAcceptedCounter_count_le_actual
    {init : InputCfg n} {ω : InputLog n} {a s T : ℕ}
    (h : Prefix init ω a s T)
    (k M A : ℕ)
    (J : Finset (Fin (PhaseThreeModel.Numeric.hourIndex n + 1)))
    (γ : ℝ) (u : ℕ) (hsu : s ≤ u) (huT : u ≤ T) :
    ((thresholdAcceptedCounter init s k M A J γ).state ω u).1 ≤
      acceptedCount (labelsAt init ω u) := by
  set Q := thresholdAcceptedCounter init s k M A J γ with hQ
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hsu
  revert huT
  induction d with
  | zero =>
      intro _
      simp only [Nat.add_zero]
      rw [Q.state_before_start ω s
        (by simp [hQ, thresholdAcceptedCounter])]
      simp
  | succ d ih =>
      intro hT
      have hi := ih (by omega)
      have hw0 := h.window (s + d) (h.start_order.trans (by omega)) (by omega)
      have hw : ∀ i, Window (labelsAt init ω (s + d) i) :=
        fun i => hw0 _ (label_mem_trace init ω (s + d) i)
      have hc := h.canonical (s + d) (h.start_order.trans (by omega)) (by omega)
      have hstep := acceptedCount_step (labelsAt init ω (s + d)) hw hc
        (ω (s + d + 1))
      have hbit : Q.eventBit (s + d) ω ≤
          bitNat (chosen acceptedRectangle
            (labelsAt init ω (s + d)) (ω (s + d + 1))) := by
        unfold CounterSpec.eventBit
        apply bitNat_mono
        rintro ⟨_, i, j, hsel, hlate⟩
        change k ≤ frozenCount (labelsAt init ω (s + d)) ∧
          acceptedRectangle (labelsAt init ω (s + d)) i j at hlate
        exact ⟨i, j, hsel, hlate.2⟩
      rw [show s + (d + 1) = (s + d) + 1 by omega,
        Q.count_succ, labelsAt_succ, hstep]
      omega

/-- Bad-counter counterpart of
`thresholdAcceptedCounter_count_le_actual`. -/
theorem thresholdAcceptedCounter_bad_le_actual
    {init : InputCfg n} {ω : InputLog n} {a s T : ℕ}
    (h : Prefix init ω a s T)
    (k M A : ℕ)
    (J : Finset (Fin (PhaseThreeModel.Numeric.hourIndex n + 1)))
    (γ : ℝ) (u : ℕ) (hsu : s ≤ u) (huT : u ≤ T) :
    ((thresholdAcceptedCounter init s k M A J γ).state ω u).2.1 ≤
      badSampleCount J (labelsAt init ω u) := by
  set Q := thresholdAcceptedCounter init s k M A J γ with hQ
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hsu
  revert huT
  induction d with
  | zero =>
      intro _
      simp only [Nat.add_zero]
      rw [Q.state_before_start ω s
        (by simp [hQ, thresholdAcceptedCounter])]
      simp
  | succ d ih =>
      intro hT
      have hi := ih (by omega)
      have hw0 := h.window (s + d) (h.start_order.trans (by omega)) (by omega)
      have hw : ∀ i, Window (labelsAt init ω (s + d) i) :=
        fun i => hw0 _ (label_mem_trace init ω (s + d) i)
      have hc := h.canonical (s + d) (h.start_order.trans (by omega)) (by omega)
      have hstep := badSampleCount_step J (labelsAt init ω (s + d)) hw hc
        (ω (s + d + 1))
      have hbit : Q.badBit (s + d) ω ≤
          bitNat (chosen (badAcceptedRectangle (indexClass J))
            (labelsAt init ω (s + d)) (ω (s + d + 1))) := by
        unfold CounterSpec.badBit
        apply bitNat_mono
        rintro ⟨_, i, j, hsel, hlate⟩
        change k ≤ frozenCount (labelsAt init ω (s + d)) ∧
          badAcceptedRectangle (indexClass J)
            (labelsAt init ω (s + d)) i j at hlate
        exact ⟨i, j, hsel, hlate.2⟩
      rw [show s + (d + 1) = (s + d) + 1 by omega,
        Q.bad_succ, labelsAt_succ, hstep]
      omega

/-- A surviving threshold-aware receipt makes the repaired counter live at
all raw prefixes before the observed endpoint. -/
theorem thresholdAcceptedCounter_active
    {init : InputCfg n} {ω : InputLog n} {a s T : ℕ}
    (h : Prefix init ω a s T)
    (k M A : ℕ)
    (J : Finset (Fin (PhaseThreeModel.Numeric.hourIndex n + 1)))
    (γ : ℝ)
    (hgate : ∀ u, s ≤ u → u < T →
      ThresholdAcceptedGate k M A J γ (labelsAt init ω u)) :
    ∀ u, s ≤ u → u < T →
      (thresholdAcceptedCounter init s k M A J γ).active u ω := by
  set Q := thresholdAcceptedCounter init s k M A J γ with hQ
  intro u hsu huT
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hsu
  revert huT
  induction d with
  | zero =>
      intro hsT
      unfold CounterSpec.active CounterSpec.Enabled
      simp only [Nat.add_zero]
      rw [Q.state_before_start ω s
        (by simp [hQ, thresholdAcceptedCounter])]
      refine ⟨by simp [hQ, thresholdAcceptedCounter], rfl, ?_, ?_, ?_⟩
      · simpa [Q, thresholdAcceptedCounter, labelsAt] using
          hgate s le_rfl hsT
      · simp [Q, thresholdAcceptedCounter]
      · simp [Q, thresholdAcceptedCounter]
  | succ d ih =>
      intro hT
      have hprev := ih (by omega) (by omega)
      have hlive := Q.live_succ ω (s + d) hprev
      have hcount : (Q.state ω (s + d + 1)).1 ≤
          acceptedCount (labelsAt init ω (s + d + 1)) :=
        thresholdAcceptedCounter_count_le_actual h k M A J γ
          (s + d + 1) (by omega) (by omega)
      have hbad : (Q.state ω (s + d + 1)).2.1 ≤
          badSampleCount J (labelsAt init ω (s + d + 1)) :=
        thresholdAcceptedCounter_bad_le_actual h k M A J γ
          (s + d + 1) (by omega) (by omega)
      have hcountCard :=
        acceptedCount_le_card (labelsAt init ω (s + d + 1))
      have hbadCard :=
        badSampleCount_le_card J (labelsAt init ω (s + d + 1))
      rw [show s + (d + 1) = (s + d) + 1 by omega]
      unfold CounterSpec.active CounterSpec.Enabled
      refine ⟨by show s ≤ s + d + 1; omega, hlive, ?_, ?_, ?_⟩
      · simpa [Q, thresholdAcceptedCounter, labelsAt] using
          hgate (s + d + 1) (by omega) (by omega)
      · change (Q.state ω (s + d + 1)).1 < init.card + 1
        omega
      · change (Q.state ω (s + d + 1)).2.1 ≤ init.card
        omega

/-- Simultaneous threshold-aware pathwise coupling.  This is the corrected
replacement for `actual_counts_le_stopped_add_earlyCap`. -/
theorem threshold_actual_counts_le_stopped_add_earlyCap
    {init : InputCfg n} {ω : InputLog n} {a s T M R k A : ℕ}
    (h : Prefix init ω a s T)
    (J : Finset (Fin (PhaseThreeModel.Numeric.hourIndex n + 1)))
    (γ : ℝ)
    (hM : mainCount (labelsAt init ω s) = M)
    (hR : reserveCount (labelsAt init ω s) = R)
    (hk : 0 < k)
    (hgate : ∀ u, s ≤ u → u < T →
      ThresholdAcceptedGate k M A J γ (labelsAt init ω u))
    (hnot : ω ∉ EarlyRoleEvent init s M R k)
    (u : ℕ) (hsu : s ≤ u) (huT : u ≤ T) :
    acceptedCount (labelsAt init ω u) ≤
        ((thresholdAcceptedCounter init s k M A J γ).state ω u).1 + k ∧
      badSampleCount J (labelsAt init ω u) ≤
        ((thresholdAcceptedCounter init s k M A J γ).state ω u).2.1 + k := by
  set Q := thresholdAcceptedCounter init s k M A J γ with hQ
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hsu
  revert huT
  induction d with
  | zero =>
      intro _
      have hzero := prefix_start_counts_zero h
      have hbadzero := prefix_start_bad_counts_zero h (indexClass J) J
      simp only [Nat.add_zero]
      rw [Q.state_before_start ω s
        (by simp [hQ, thresholdAcceptedCounter])]
      omega
  | succ d ih =>
      intro hT
      have hi := ih (by omega)
      have hw0 := h.window (s + d) (h.start_order.trans (by omega)) (by omega)
      have hw : ∀ i, Window (labelsAt init ω (s + d) i) :=
        fun i => hw0 _ (label_mem_trace init ω (s + d) i)
      have hc := h.canonical (s + d) (h.start_order.trans (by omega)) (by omega)
      have haccStep := acceptedCount_step (labelsAt init ω (s + d)) hw hc
        (ω (s + d + 1))
      have hbadStep := badSampleCount_step J (labelsAt init ω (s + d)) hw hc
        (ω (s + d + 1))
      by_cases hlate : k ≤ frozenCount (labelsAt init ω (s + d))
      · have hactive := thresholdAcceptedCounter_active h k M A J γ hgate
          (s + d) (by omega) (by omega)
        have heventProp :
            (Q.active (s + d) ω ∧
              chosen Q.event (labelsAt init ω (s + d)) (ω (s + d + 1))) ↔
            chosen acceptedRectangle
              (labelsAt init ω (s + d)) (ω (s + d + 1)) := by
          constructor
          · rintro ⟨_, i, j, hsel, hpred⟩
            change k ≤ frozenCount (labelsAt init ω (s + d)) ∧
              acceptedRectangle (labelsAt init ω (s + d)) i j at hpred
            exact ⟨i, j, hsel, hpred.2⟩
          · rintro ⟨i, j, hsel, hpred⟩
            refine ⟨hactive, i, j, hsel, ?_⟩
            exact ⟨hlate, hpred⟩
        have hbadProp :
            (Q.active (s + d) ω ∧
              chosen Q.bad (labelsAt init ω (s + d)) (ω (s + d + 1))) ↔
            chosen (badAcceptedRectangle (indexClass J))
              (labelsAt init ω (s + d)) (ω (s + d + 1)) := by
          constructor
          · rintro ⟨_, i, j, hsel, hpred⟩
            change k ≤ frozenCount (labelsAt init ω (s + d)) ∧
              badAcceptedRectangle (indexClass J)
                (labelsAt init ω (s + d)) i j at hpred
            exact ⟨i, j, hsel, hpred.2⟩
          · rintro ⟨i, j, hsel, hpred⟩
            refine ⟨hactive, i, j, hsel, ?_⟩
            exact ⟨hlate, hpred⟩
        have hevent : Q.eventBit (s + d) ω =
            bitNat (chosen acceptedRectangle
              (labelsAt init ω (s + d)) (ω (s + d + 1))) := by
          unfold CounterSpec.eventBit
          exact congrArg bitNat (propext heventProp)
        have hbadbit : Q.badBit (s + d) ω =
            bitNat (chosen (badAcceptedRectangle (indexClass J))
              (labelsAt init ω (s + d)) (ω (s + d + 1))) := by
          unfold CounterSpec.badBit
          exact congrArg bitNat (propext hbadProp)
        constructor
        · rw [show s + (d + 1) = (s + d) + 1 by omega,
            labelsAt_succ, haccStep, Q.count_succ, hevent]
          omega
        · rw [show s + (d + 1) = (s + d) + 1 by omega,
            labelsAt_succ, hbadStep, Q.bad_succ, hbadbit]
          omega
      · have hpre := acceptedCount_lt_earlyCap h hM hR hnot
          (s + d) (by omega) (by omega) (by omega)
        have hbit := bitNat_zero_one
          (chosen acceptedRectangle
            (labelsAt init ω (s + d)) (ω (s + d + 1)))
        have hpost : acceptedCount (labelsAt init ω (s + d + 1)) ≤ k := by
          rw [labelsAt_succ, haccStep]
          omega
        have hbadpost := badSampleCount_le_accepted J
          (labelsAt init ω (s + d + 1))
        rw [show s + (d + 1) = (s + d) + 1 by omega]
        constructor <;> omega

/-- Consumer form requested by row two: actual bad samples are bounded by the
repaired stopped late-bad counter plus the shared early cap. -/
theorem threshold_actual_bad_le_stopped_late_bad_add_earlyCap
    {init : InputCfg n} {ω : InputLog n} {a s T M R k A : ℕ}
    (h : Prefix init ω a s T)
    (J : Finset (Fin (PhaseThreeModel.Numeric.hourIndex n + 1)))
    (γ : ℝ)
    (hM : mainCount (labelsAt init ω s) = M)
    (hR : reserveCount (labelsAt init ω s) = R)
    (hk : 0 < k)
    (hgate : ∀ u, s ≤ u → u < T →
      ThresholdAcceptedGate k M A J γ (labelsAt init ω u))
    (hnot : ω ∉ EarlyRoleEvent init s M R k) :
    badSampleCount J (labelsAt init ω T) ≤
      ((thresholdAcceptedCounter init s k M A J γ).state ω T).2.1 + k :=
  (threshold_actual_counts_le_stopped_add_earlyCap h J γ hM hR hk
    hgate hnot T h.observed le_rfl).2

/-- Restrict a legal observed prefix to an earlier endpoint. -/
theorem prefix_restrict_endpoint
    {init : InputCfg n} {ω : InputLog n} {a s T U : ℕ}
    (h : Prefix init ω a s U) (hsT : s ≤ T) (hTU : T ≤ U) :
    Prefix init ω a s T := by
  exact
    { all_start := h.all_start
      four_start := h.four_start
      start_order := h.start_order
      observed := hsT
      all_three := h.all_three
      before_six := fun u hau huT => h.before_six u hau (huT.trans hTU) }

private theorem acceptedCount_le_reserveCount
    (f : Fin n → AgentState L K) :
    acceptedCount f ≤ reserveCount f := by
  change (pool f AcceptedReserve).card ≤
    (pool f (fun x => reserveRole x.role)).card
  exact pool_mono f AcceptedReserve (fun x => reserveRole x.role)
    (fun _ hx => hx.1)

/-- Once all `R` Reserve samples are written, the actual accepted count stays
exactly `R` throughout every later legal prefix. -/
theorem acceptedCount_eq_after_complete
    {init : InputCfg n} {ω : InputLog n}
    {a s T U V R : ℕ}
    (h : Prefix init ω a s U)
    (hR : reserveCount (labelsAt init ω s) = R)
    (hsT : s ≤ T) (hTV : T ≤ V) (hVU : V ≤ U)
    (haccepted : acceptedCount (labelsAt init ω T) = R) :
    acceptedCount (labelsAt init ω V) = R := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hTV
  revert hVU
  induction d with
  | zero =>
      intro _
      simpa using haccepted
  | succ d ih =>
      intro hU
      have hprev := ih (by omega) (by omega)
      have hw0 := h.window (T + d)
        (h.start_order.trans (hsT.trans (by omega))) (by omega)
      have hw : ∀ i, Window (labelsAt init ω (T + d) i) :=
        fun i => hw0 _ (label_mem_trace init ω (T + d) i)
      have hc := h.canonical (T + d)
        (h.start_order.trans (hsT.trans (by omega))) (by omega)
      have hstep := acceptedCount_step (labelsAt init ω (T + d)) hw hc
        (ω (T + d + 1))
      have hnext :
          acceptedCount (labelsAt init ω (T + d + 1)) =
            acceptedCount (labelsAt init ω (T + d)) +
              bitNat (chosen acceptedRectangle
                (labelsAt init ω (T + d)) (ω (T + d + 1))) := by
        rw [labelsAt_succ, hstep]
      have hreserve : reserveCount (labelsAt init ω (T + d + 1)) = R :=
        (prefix_reserve_count h (hsT.trans (by omega)) (by omega)).trans hR
      have hupper :=
        acceptedCount_le_reserveCount (labelsAt init ω (T + d + 1))
      rw [hreserve] at hupper
      rw [hprev] at hnext
      show acceptedCount (labelsAt init ω (T + d + 1)) = R
      omega

/-- Exact terminal retention.  At completion every later actual accepted bit
is zero; the repaired event bit is a sub-bit of it, and the bad bit is a
sub-bit of the event bit. -/
theorem thresholdAcceptedCounter_counts_retained_after_complete
    {init : InputCfg n} {ω : InputLog n}
    {a s T U V M R k A : ℕ}
    (h : Prefix init ω a s U)
    (J : Finset (Fin (PhaseThreeModel.Numeric.hourIndex n + 1)))
    (γ : ℝ)
    (hR : reserveCount (labelsAt init ω s) = R)
    (hsT : s ≤ T) (hTV : T ≤ V) (hVU : V ≤ U)
    (haccepted : acceptedCount (labelsAt init ω T) = R) :
    ((thresholdAcceptedCounter init s k M A J γ).state ω V).1 =
        ((thresholdAcceptedCounter init s k M A J γ).state ω T).1 ∧
      ((thresholdAcceptedCounter init s k M A J γ).state ω V).2.1 =
        ((thresholdAcceptedCounter init s k M A J γ).state ω T).2.1 := by
  set Q := thresholdAcceptedCounter init s k M A J γ with hQ
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hTV
  revert hVU
  induction d with
  | zero =>
      intro _
      simp
  | succ d ih =>
      intro hU
      have hstate := ih (by omega) (by omega)
      have hacceptedPrev := acceptedCount_eq_after_complete h hR hsT
        (show T ≤ T + d by omega) (by omega) haccepted
      have hacceptedNext : acceptedCount (labelsAt init ω (T + d + 1)) = R :=
        acceptedCount_eq_after_complete h hR hsT
          (show T ≤ T + (d + 1) by omega) hU haccepted
      have hw0 := h.window (T + d)
        (h.start_order.trans (hsT.trans (by omega))) (by omega)
      have hw : ∀ i, Window (labelsAt init ω (T + d) i) :=
        fun i => hw0 _ (label_mem_trace init ω (T + d) i)
      have hc := h.canonical (T + d)
        (h.start_order.trans (hsT.trans (by omega))) (by omega)
      have hstep := acceptedCount_step (labelsAt init ω (T + d)) hw hc
        (ω (T + d + 1))
      have hactualStep :
          acceptedCount (labelsAt init ω (T + d + 1)) =
            acceptedCount (labelsAt init ω (T + d)) +
              bitNat (chosen acceptedRectangle
                (labelsAt init ω (T + d)) (ω (T + d + 1))) := by
        rw [labelsAt_succ, hstep]
      have hactualZero :
          bitNat (chosen acceptedRectangle
            (labelsAt init ω (T + d)) (ω (T + d + 1))) = 0 := by
        rw [hacceptedPrev, hacceptedNext] at hactualStep
        omega
      have hcounterBit : Q.eventBit (T + d) ω ≤
          bitNat (chosen acceptedRectangle
            (labelsAt init ω (T + d)) (ω (T + d + 1))) := by
        unfold CounterSpec.eventBit
        apply bitNat_mono
        rintro ⟨_, i, j, hsel, hlate⟩
        change k ≤ frozenCount (labelsAt init ω (T + d)) ∧
          acceptedRectangle (labelsAt init ω (T + d)) i j at hlate
        exact ⟨i, j, hsel, hlate.2⟩
      have heventZero : Q.eventBit (T + d) ω = 0 := by omega
      have hbadZero : Q.badBit (T + d) ω = 0 := by
        have hsubset := Q.bits_subset (T + d) ω
        omega
      constructor
      · rw [show T + (d + 1) = (T + d) + 1 by omega,
          Q.count_succ, heventZero, add_zero, hstate.1]
      · rw [show T + (d + 1) = (T + d) + 1 by omega,
          Q.bad_succ, hbadZero, add_zero, hstate.2]

/-!
THEOREM LIST
* `thresholdAcceptedCounter_count_le_actual`
* `thresholdAcceptedCounter_bad_le_actual`
* `thresholdAcceptedCounter_active`
* `threshold_actual_counts_le_stopped_add_earlyCap`
* `threshold_actual_bad_le_stopped_late_bad_add_earlyCap`
* `prefix_restrict_endpoint`
* `acceptedCount_eq_after_complete`
* `thresholdAcceptedCounter_counts_retained_after_complete`

CLOSES
* Reinstantiation of the actual/stopped accepted-count coupling with the
  threshold-aware gate from `LateSamplingRowTwoCounterRepair`.
* The requested actual-bad bound by stopped late-bad count plus early cap.
* Exact retention of both counter coordinates from genuine completion to a
  later fixed horizon.

UNFINISHED
* Producing `ThresholdAcceptedGate` from the three row-two class receipts.
* Producing the legal fixed-horizon prefix from the timer item.
* The protected-class sentinel boundary `ell + 2 = L`.
END
-/

end Ripple.PopulationProtocol.ExactMajority.LateThresholdAcceptedCounterCoupling

end
