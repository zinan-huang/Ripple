-- Ripple/PopulationProtocol/ExactMajority/Probability/LateTimerRouteProof.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.LateTimerLabelStep
import Ripple.PopulationProtocol.ExactMajority.Probability.LateTimerProtectionOriginalLaw
import Ripple.PopulationProtocol.ExactMajority.Probability.LateTimerProtectionGuarded
import Ripple.PopulationProtocol.ExactMajority.Probability.LateMixedFiveSixReachableWf

/-!
# The guarded deterministic route for the late timers (p = 5, ..., 8)

For `omega` from a valid initial configuration with `allThreeStart < s`, the first
phase-`p` seed at `s` and a phase `>= p+1` agent at `r <= s + protectionHorizon n`,
some persistent label has at least `50 clockHours + 1` participations in the draws
`s+1 ... r`.  Proof: the label-level counter inequality of `LateTimerLabelStep`
is an invariant of the draws `s+1 ... r-1` (every Clock at phase `p` has
`counter + participations >= 50 (L+1)`), and the draw `r` is a zero test
(`timer_left_advance` / `timer_right_advance`).
-/

noncomputable section

namespace Ripple.PopulationProtocol.ExactMajority.LateTimerRouteProof

open TimeTheorem PairLog StageEventSpec LateF6OriginalLaw
open LateTimerPrefixScalar LateTimerProtectionOriginalLaw LateTimerLabelStep
open LateTimerProtectionGuarded AdvanceNoOvershoot PhaseThreeScalar Preorder PhaseOneDrainStopping LateMixedFiveSixReachableWf

variable {n : ℕ}

private theorem label_mem_trace
    (init : InputCfg n) (omega : InputLog n) (t : ℕ) (i : Fin init.card) :
    labelsAt init omega t i ∈ trace init omega t := by
  rw [← PairLog.labelsAt_config init omega t]
  exact Multiset.mem_map.mpr ⟨i, by simp, rfl⟩

/-- Participation count of label `i` in the draws `s+1 ... s+k`. -/
noncomputable def partCount (init : InputCfg n) (i : Fin init.card) (s k : ℕ)
    (omega : InputLog n) : ℕ :=
  ∑ u ∈ Finset.range k,
    participates (labelsAt init omega (s + u)) (omega (s + u + 1)) i

theorem labelParticipation_eq (init : InputCfg n) (i : Fin init.card) (s t : ℕ)
    (omega : InputLog n) :
    labelParticipation init i s t omega =
      ((participates (labelsAt init omega (s + t)) (omega (s + t + 1)) i : ℕ) : ℝ) := by
  classical
  unfold participates
  change (if ∃ j : Fin init.card, j ≠ i ∧
        (PairLog.selectLabels (labelsAt init omega (s + t)) (omega (s + t + 1)) = some (i, j) ∨
         PairLog.selectLabels (labelsAt init omega (s + t)) (omega (s + t + 1)) = some (j, i))
      then (1 : ℝ) else 0) = _
  by_cases h : ∃ j : Fin init.card, j ≠ i ∧
      (PairLog.selectLabels (labelsAt init omega (s + t)) (omega (s + t + 1)) = some (i, j) ∨
       PairLog.selectLabels (labelsAt init omega (s + t)) (omega (s + t + 1)) = some (j, i))
  · simp [h]
  · simp [h]

theorem partCount_le_bernoulli (init : InputCfg n) (i : Fin init.card) (s k N : ℕ)
    (hk : k ≤ N) (omega : InputLog n) :
    (partCount init i s k omega : ℝ) ≤
      bernoulliCount (labelParticipation init i s) N omega := by
  unfold partCount bernoulliCount
  push_cast
  calc
    ∑ u ∈ Finset.range k,
        ((participates (labelsAt init omega (s + u)) (omega (s + u + 1)) i : ℕ) : ℝ)
        = ∑ u ∈ Finset.range k, labelParticipation init i s u omega := by
          apply Finset.sum_congr rfl
          intro u _
          rw [labelParticipation_eq]
    _ ≤ ∑ u ∈ Finset.range N, labelParticipation init i s u omega := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hk)
          intro u _ _
          rw [labelParticipation_eq]
          exact Nat.cast_nonneg _


/-- Facts about a log that is genuinely in the guarded window. -/
structure WindowFacts (init : InputCfg n) (omega : InputLog n) (p s r a0 : ℕ) : Prop where
  seed : firstHit (someGE (n := n) p) (trace init omega) s
  allThree : firstHit (allGE (n := n) 3) (trace init omega) a0
  a0_lt : a0 < s
  below : ∀ t, t < r → ¬ someGE (n := n) (p + 1) (trace init omega t)

theorem window_ge3 {init : InputCfg n} {omega : InputLog n} {p s r a0 : ℕ}
    (W : WindowFacts init omega p s r a0) {t : ℕ} (ht : a0 ≤ t) :
    ∀ k : Fin init.card, 3 ≤ (labelsAt init omega t k).phase.val := by
  intro k
  have hreach := trace_reachable init omega ht
  exact phase_lower_reachable 3 (trace init omega a0) (trace init omega t) hreach
    (fun a ha => W.allThree.1 a ha) _ (label_mem_trace init omega t k)

theorem window_up {init : InputCfg n} {omega : InputLog n} {p s r a0 : ℕ}
    (W : WindowFacts init omega p s r a0) {t : ℕ} (ht : t < r) :
    ∀ k : Fin init.card, (labelsAt init omega t k).phase.val ≤ p := by
  intro k
  by_contra hgt
  apply W.below t ht
  exact ⟨_, label_mem_trace init omega t k, by omega⟩

theorem window_wf {init : InputCfg n} (hvalid : validInitial init)
    {omega : InputLog n} {p s r a0 : ℕ} (hp8 : p ≤ 8)
    (W : WindowFacts init omega p s r a0) {t : ℕ} (ha0 : a0 ≤ t) (ht : t < r) :
    ∀ k : Fin init.card, WfAgent (labelsAt init omega t k) := by
  intro k
  have hreach := trace_reachable init omega (Nat.zero_le t)
  rw [trace_zero] at hreach
  exact wfAgent_of_reachable_phase_range hvalid hreach (label_mem_trace init omega t k)
    (by have := window_ge3 W ha0 k; omega)
    (by have := window_up W ht k; omega)

/-- The Clock counter invariant on the draws `s+1 ... r-1`. -/
theorem timer_invariant (p : ℕ) (hp5 : 5 ≤ p) (hp8 : p ≤ 8)
    {init : InputCfg n} (hvalid : validInitial init)
    {omega : InputLog n} {s r a0 : ℕ}
    (W : WindowFacts init omega p s r a0) (hsr : s < r) :
    ∀ t, s ≤ t → t < r → ∀ i : Fin init.card,
      (labelsAt init omega t i).role = .clock →
      (labelsAt init omega t i).phase.val = p →
      50 * (PhaseThreeModel.Numeric.hourIndex n + 1) ≤
        (labelsAt init omega t i).counter.val + partCount init i s (t - s) omega := by
  intro t hst
  induction t, hst using Nat.le_induction with
  | base =>
      intro _ i hclock hph
      obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by have := W.a0_lt; omega⟩
      have hs'lt : s' < s' + 1 := Nat.lt_succ_self s'
      have hall : ∀ k : Fin init.card, (labelsAt init omega s' k).phase.val < p := by
        intro k
        by_contra hge
        exact W.seed.2 s' hs'lt ⟨_, label_mem_trace init omega s' k, by omega⟩
      have hgt : a0 ≤ s' := by have := W.a0_lt; omega
      have hwf : ∀ k : Fin init.card, WfAgent (labelsAt init omega s' k) := by
        intro k
        have hreach := trace_reachable init omega (Nat.zero_le s')
        rw [trace_zero] at hreach
        exact wfAgent_of_reachable_phase_range hvalid hreach
          (label_mem_trace init omega s' k)
          (by have := window_ge3 W hgt k; omega) (by have := hall k; omega)
      have hstep := label_step p hp5 hp8 (labelsAt init omega s') (omega (s' + 1))
        hwf (fun k => by have := hall k; omega) (window_ge3 W hgt) i
        (by rw [← labelsAt_succ]; exact hclock) (by rw [← labelsAt_succ]; exact hph)
      have := hstep.2.2.2 hall
      rw [← labelsAt_succ] at this
      omega
  | succ t hst ih =>
      intro htr i hclock hph
      have hgt : a0 ≤ t := by have := W.a0_lt; omega
      have htr' : t < r := by omega
      have hwf := window_wf hvalid hp8 W hgt htr'
      have hstep := label_step p hp5 hp8 (labelsAt init omega t) (omega (t + 1))
        hwf (window_up W htr') (window_ge3 W hgt) i
        (by rw [← labelsAt_succ]; exact hclock) (by rw [← labelsAt_succ]; exact hph)
      rw [← labelsAt_succ] at hstep
      obtain ⟨hfc, h1, h2, -⟩ := hstep
      have hpart : partCount init i s (t + 1 - s) omega =
          partCount init i s (t - s) omega +
            participates (labelsAt init omega t) (omega (t + 1)) i := by
        have hts : t + 1 - s = (t - s) + 1 := by omega
        rw [hts]
        unfold partCount
        rw [Finset.sum_range_succ]
        have hst' : s + (t - s) = t := by omega
        rw [hst']
      rw [hpart]
      have hupt := window_up W htr' i
      rcases Nat.lt_or_ge (labelsAt init omega t i).phase.val p with hlt | hge
      · have := h2 hlt; omega
      · have heq : (labelsAt init omega t i).phase.val = p := by omega
        have h1' := h1 heq
        have hih := ih htr' i hfc heq
        omega


private theorem exists_label_of_mem
    (init : InputCfg n) (omega : InputLog n) (t : ℕ)
    {a : AgentState (PhaseThreeModel.Numeric.hourIndex n) 256} (ha : a ∈ trace init omega t) :
    ∃ i : Fin init.card, labelsAt init omega t i = a := by
  rw [← PairLog.labelsAt_config init omega t] at ha
  rcases Multiset.mem_map.mp ha with ⟨i, _, hi⟩
  exact ⟨i, hi⟩

/-- **The guarded deterministic route** for the late timers `p = 5, ..., 8`, from a valid
initial configuration. -/
theorem lateCounterRouteGuarded (p : ℕ) (hp5 : 5 ≤ p) (hp8 : p ≤ 8)
    (init : InputCfg n) (hvalid : validInitial init) :
    LateCounterRouteGuarded init p := by
  refine ⟨?_⟩
  intro omega s hs hall hnext
  have hseed : firstHit (someGE (n := n) p) (trace init omega) s :=
    (phaseSeedTime_eq_iff init p omega s).mp hs
  -- the all-three time
  have hne : allThreeStart init omega ≠ ⊤ := ne_top_of_lt hall
  obtain ⟨a0, ha0eq⟩ := WithTop.ne_top_iff_exists.mp hne
  have ha0time : allThreeStart init omega = (a0 : WithTop ℕ) := ha0eq.symm
  have ha0lt : a0 < s := by
    have : (a0 : WithTop ℕ) < (s : WithTop ℕ) := by rw [← ha0time]; exact hall
    exact WithTop.coe_lt_coe.mp this
  have hallFirst : firstHit (allGE (n := n) 3) (trace init omega) a0 :=
    (PhaseOneDrainStopping.exitTime_eq_iff_firstHit init (allGE (n := n) 3) omega a0).mp
      (by simpa only [allThreeStart] using ha0time)
  -- the next seed time
  have hfin : phaseSeedTime init (p + 1) omega ≠ ⊤ :=
    ne_top_of_le_ne_top WithTop.coe_ne_top hnext
  obtain ⟨r, hreq⟩ := WithTop.ne_top_iff_exists.mp hfin
  have hrtime : phaseSeedTime init (p + 1) omega = (r : WithTop ℕ) := hreq.symm
  have hrle : r ≤ s + protectionHorizon n := by
    have : (r : WithTop ℕ) ≤ ((s + protectionHorizon n : ℕ) : WithTop ℕ) := by
      rw [← hrtime]; exact hnext
    exact WithTop.coe_le_coe.mp this
  have hrfirst : firstHit (someGE (n := n) (p + 1)) (trace init omega) r :=
    (phaseSeedTime_eq_iff init (p + 1) omega r).mp hrtime
  have W : WindowFacts init omega p s r a0 :=
    ⟨hseed, hallFirst, ha0lt, fun t ht => hrfirst.2 t ht⟩
  -- r = r' + 1
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := by
    refine ⟨r - 1, ?_⟩
    have : r ≠ 0 := by
      intro h0
      subst h0
      obtain ⟨a, ha, hph⟩ := hrfirst.1
      rw [trace_zero] at ha
      have := (hvalid a ha).1
      have h0' : a.phase.val = 0 := by rw [this]
      omega
    omega
  have hr'lt : r' < r' + 1 := Nat.lt_succ_self r'
  have hup := window_up W hr'lt
  -- `s <= r`, hence `a0 <= r'`
  have hsr : s ≤ r' + 1 := by
    by_contra h
    exact hseed.2 (r' + 1) (by omega) ⟨_, hrfirst.1.choose_spec.1, by
      have := hrfirst.1.choose_spec.2; omega⟩
  have hgt0 : a0 ≤ r' := by omega
  have hwf := window_wf hvalid hp8 W hgt0 hr'lt
  have hge3 := window_ge3 W hgt0
  -- the agent that reaches phase p+1
  obtain ⟨ag, hagmem, hagph⟩ := hrfirst.1
  obtain ⟨k, hk⟩ := exists_label_of_mem init omega (r' + 1) hagmem
  have hg : labelsAt init omega (r' + 1) =
      stepLabels (labelsAt init omega r') (omega (r' + 1)) := labelsAt_succ init omega r'
  have hkph : p + 1 ≤ (stepLabels (labelsAt init omega r') (omega (r' + 1)) k).phase.val := by
    rw [← hg, hk]; exact hagph
  -- a Clock at phase `p` with counter `0` takes part in the draw `r'+1`
  have key : ∃ i0 : Fin init.card,
      (labelsAt init omega r' i0).role = .clock ∧
      (labelsAt init omega r' i0).phase.val = p ∧
      (labelsAt init omega r' i0).counter.val = 0 ∧
      participates (labelsAt init omega r') (omega (r' + 1)) i0 = 1 := by
    unfold stepLabels at hkph
    cases hsel : selectLabels (labelsAt init omega r') (omega (r' + 1)) with
    | none =>
        rw [hsel] at hkph
        simp only at hkph
        have := hup k
        omega
    | some pair =>
        obtain ⟨a, b⟩ := pair
        rw [hsel] at hkph
        simp only at hkph
        have hab := selectLabels_distinct _ _ a b hsel
        by_cases hka : k = a
        · subst hka
          have hupd : updateLabels (labelsAt init omega r') k b k =
              ((NonuniformMajority _ 256).δ (labelsAt init omega r' k)
                (labelsAt init omega r' b)).1 := by
            unfold updateLabels
            rw [Function.update_of_ne hab, Function.update_self]
          rw [hupd] at hkph
          change p + 1 ≤ (Transition _ 256 (labelsAt init omega r' k)
            (labelsAt init omega r' b)).1.phase.val at hkph
          obtain ⟨h1, h2, h3⟩ := timer_left_advance p hp5 hp8 _ _ (hwf k) (hwf b)
            (hup k) (hup b) hkph
          exact ⟨k, h1, h2, h3, participates_of_left _ _ k b hsel⟩
        · by_cases hkb : k = b
          · subst hkb
            have hupd : updateLabels (labelsAt init omega r') a k k =
                ((NonuniformMajority _ 256).δ (labelsAt init omega r' a)
                  (labelsAt init omega r' k)).2 := by
              unfold updateLabels
              rw [Function.update_self]
            rw [hupd] at hkph
            change p + 1 ≤ (Transition _ 256 (labelsAt init omega r' a)
              (labelsAt init omega r' k)).2.phase.val at hkph
            obtain ⟨h1, h2, h3⟩ := timer_right_advance p hp5 hp8 _ _ (hwf a) (hwf k)
              (hup a) (hup k) hkph
            exact ⟨k, h1, h2, h3, participates_of_right _ _ a k hsel⟩
          · have hupd : updateLabels (labelsAt init omega r') a b k =
                labelsAt init omega r' k := by
              unfold updateLabels
              rw [Function.update_of_ne hkb, Function.update_of_ne hka]
            rw [hupd] at hkph
            have := hup k
            omega
  obtain ⟨i0, hclock, hphase, hzero, hpart⟩ := key
  have hsr' : s ≤ r' := by
    by_contra h
    exact hseed.2 r' (by omega) ⟨_, label_mem_trace init omega r' i0, by omega⟩
  have hinv := timer_invariant p hp5 hp8 hvalid W (by omega : s < r' + 1) r' hsr'
    hr'lt i0 hclock hphase
  rw [hzero] at hinv
  have hcount : 50 * (PhaseThreeModel.Numeric.hourIndex n + 1) + 1 ≤
      partCount init i0 s (r' - s + 1) omega := by
    unfold partCount
    rw [Finset.sum_range_succ]
    have hs' : s + (r' - s) = r' := by omega
    rw [hs', hpart]
    unfold partCount at hinv
    omega
  refine ⟨i0, ?_⟩
  change ((invocationThreshold n : ℕ) : ℝ) ≤
    bernoulliCount (labelParticipation init i0 s) (protectionHorizon n) omega
  have hbound := partCount_le_bernoulli init i0 s (r' - s + 1) (protectionHorizon n)
    (by omega) omega
  refine le_trans ?_ hbound
  unfold invocationThreshold
  have hclockHours : PhaseThreeModel.Numeric.clockHours n =
      PhaseThreeModel.Numeric.hourIndex n + 1 := rfl
  rw [hclockHours]
  exact_mod_cast hcount

/-- The guarded early-next-seed event has original-law probability at most `n^(-2.06)`,
from `GoodInput` alone. -/
theorem law_timerProtectionFailureGuarded_tail_of_goodInput
    (init : InputCfg n) (hinput : ThresholdEpidemic.GoodInput n init)
    (p : ℕ) (hp : LateTimedPhase p) :
    law init (timerProtectionFailureGuarded init p) ≤
      ENNReal.ofReal (Real.rpow (n : ℝ) (-(103 / 50 : ℝ))) :=
  law_timerProtectionFailureGuarded_tail init hinput p hp
    (lateCounterRouteGuarded p hp.1 hp.2 init hinput.2.1)

/-- The unguarded failure event is charged by the guarded tail plus the separate event
that the phase-`p` seed occurs no later than the first all-agents-at-phase-3 time. -/
theorem law_timerProtectionFailure_le_of_goodInput
    (init : InputCfg n) (hinput : ThresholdEpidemic.GoodInput n init)
    (p : ℕ) (hp : LateTimedPhase p) :
    law init (timerProtectionFailure init p) ≤
      ENNReal.ofReal (Real.rpow (n : ℝ) (-(103 / 50 : ℝ))) +
        law init (earlySeedBeforeAllThree init p) :=
  law_timerProtectionFailure_le_guarded_add_early init hinput p hp
    (lateCounterRouteGuarded p hp.1 hp.2 init hinput.2.1)

end Ripple.PopulationProtocol.ExactMajority.LateTimerRouteProof

end
