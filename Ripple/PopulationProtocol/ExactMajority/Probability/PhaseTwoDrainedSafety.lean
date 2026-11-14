import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseTwoEntryProducer
import Ripple.PopulationProtocol.ExactMajority.Probability.AdvanceOvershootSource
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseTwoActivation

/-!
# Safety from the genuine drained boundary

The carrier range {2,3,4} of smallBias is closed under every transition
after Phase 0. Reachable well-formedness then supplies the non-mcr fact
needed by the pinned no-overshoot lemmas. In particular the genuine first
threshold crossing at 2 or 3 has exactly that threshold, rather than a
jump to the backup phase.

The final producer removes the backup alternative from the actual
drained-start outcome tail. It adds no probability assumption.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Ripple.PopulationProtocol.ExactMajority.PhaseTwoDrainedSafety

open TimeTheorem PairLog PhaseOneDrain PhaseOneDrainStopping PhaseOneTimer
open PhaseTwoThresholds PhaseTwoSeedProfile PhaseTwoEntryProducer

variable {L K : ℕ}

def SmallSafe (a : AgentState L K) : Prop :=
  2 ≤ a.smallBias.val ∧ a.smallBias.val ≤ 4

def AllSmallSafe (c : Cfg L K) : Prop :=
  ∀ a ∈ c, SmallSafe a

theorem avg_small_safe (x y : Fin 7)
    (hx : 2 ≤ x.val ∧ x.val ≤ 4) (hy : 2 ≤ y.val ∧ y.val ≤ 4) :
    (2 ≤ (avgFin7 x y).1.val ∧ (avgFin7 x y).1.val ≤ 4) ∧
      (2 ≤ (avgFin7 x y).2.val ∧ (avgFin7 x y).2.val ≤ 4) := by
  dsimp [avgFin7]
  omega

theorem phase_one_pair_small_safe (s t : AgentState L K)
    (hs : s.phase.val = 1) (ht : t.phase.val = 1)
    (hss : SmallSafe s) (hts : SmallSafe t) :
    SmallSafe (Transition L K s t).1 ∧ SmallSafe (Transition L K s t).2 := by
  classical
  have hlocal : SmallSafe (Phase1Transition L K s t).1 ∧
      SmallSafe (Phase1Transition L K s t).2 := by
    by_cases hmain : s.role = .main ∧ t.role = .main
    · simpa [Phase1Transition, SmallSafe, hmain] using
        (avg_small_safe s.smallBias t.smallBias hss hts)
    · simpa [Phase1Transition, SmallSafe, hmain] using And.intro hss hts
  have hepi := Phase1Convergence.phaseEpidemicUpdate_eq_self_of_phase1
    (L := L) (K := K) s t hs ht
  have hphase : s.phase = ⟨1, by decide⟩ := Fin.ext hs
  simpa only [SmallSafe, Transition, hepi, hphase, finishPhase10Entry_smallBias]
    using hlocal

theorem transition_small_safe (s t : AgentState L K)
    (hs : 1 ≤ s.phase.val) (ht : 1 ≤ t.phase.val)
    (hss : SmallSafe s) (hts : SmallSafe t) :
    SmallSafe (Transition L K s t).1 ∧ SmallSafe (Transition L K s t).2 := by
  by_cases hone : s.phase.val = 1 ∧ t.phase.val = 1
  · exact phase_one_pair_small_safe s t hone.1 hone.2 hss hts
  · have hmax : 2 ≤ max s.phase.val t.phase.val := by omega
    have hdispatch : 2 ≤ (phaseEpidemicUpdate L K s t).1.phase.val :=
      hmax.trans (phaseEpidemicUpdate_left_phase_ge_max (L := L) (K := K) s t)
    have hleft := Transition_preserves_epidemic_smallBias_left_of_phase_ge_two
      (L := L) (K := K) s t hdispatch
    have hright := Transition_preserves_epidemic_smallBias_right_of_dispatch_phase_ge_two
      (L := L) (K := K) s t hdispatch
    have hbias := phaseEpidemicUpdate_preserves_smallBias (L := L) (K := K) s t
    constructor
    · simpa only [SmallSafe, hleft, hbias.1] using hss
    · simpa only [SmallSafe, hright, hbias.2] using hts

theorem small_safe_stepRel (c c' : Cfg L K)
    (hstep : (NonuniformMajority L K).StepRel c c')
    (hlo : ∀ a ∈ c, 1 ≤ a.phase.val) (hsafe : AllSmallSafe c) :
    AllSmallSafe c' := by
  classical
  rcases hstep with ⟨r, q, happ, hc'⟩
  dsimp [Protocol.Applicable, NonuniformMajority] at happ hc'
  have hr : r ∈ c := Multiset.mem_of_le happ (by simp)
  have hq : q ∈ c := Multiset.mem_of_le happ (by simp)
  have hpair := transition_small_safe r q (hlo r hr) (hlo q hq)
    (hsafe r hr) (hsafe q hq)
  rw [hc']
  intro a ha
  simp only [Multiset.mem_add, Multiset.mem_cons, Multiset.mem_singleton] at ha
  rcases ha with hold | hnew
  · exact hsafe a (Multiset.mem_of_le (Multiset.sub_le_self c {r, q}) hold)
  · rcases hnew with hnew | hnew
    · simpa only [hnew] using hpair.1
    · simpa only [hnew] using hpair.2

theorem small_safe_reachable (c c' : Cfg L K)
    (hreach : (NonuniformMajority L K).Reachable c c')
    (hlo : ∀ a ∈ c, 1 ≤ a.phase.val) (hsafe : AllSmallSafe c) :
    AllSmallSafe c' := by
  revert hlo hsafe
  induction hreach with
  | refl =>
      exact fun _ h => h
  | tail hprev hstep ih =>
      intro hlo hsafe
      exact small_safe_stepRel _ _ hstep
        (phase_lower_reachable 1 _ _ hprev hlo) (ih hlo hsafe)

theorem reachable_small_safe_wf (init c : Cfg L K)
    (hvalid : validInitial init)
    (hreach : (NonuniformMajority L K).Reachable init c)
    (hlo : ∀ a ∈ c, 1 ≤ a.phase.val)
    (hhi : ∀ a ∈ c, a.phase.val ≤ 9)
    (hsafe : AllSmallSafe c) :
    AdvanceNoOvershoot.Wf c := by
  intro a ha
  have hwf := reachable_preserves_well_formed_agents
    (L := L) (K := K) init c hvalid hreach a ha
  exact ⟨hwf.not_mcr_of_intermediate_phase (hlo a ha) (hhi a ha), hsafe a ha⟩

/-- A one-step upper bound usable before both the first seed and activation.
For input phases at most three it gives output phases at most four. -/
theorem transition_phase_upper_succ (p : ℕ) (hp : p ≤ 8)
    (s t : AgentState L K)
    (hs : AdvanceNoOvershoot.WfAgent s) (ht : AdvanceNoOvershoot.WfAgent t)
    (hsp : s.phase.val ≤ p) (htp : t.phase.val ≤ p) :
    (Transition L K s t).1.phase.val ≤ p + 1 ∧
      (Transition L K s t).2.phase.val ≤ p + 1 := by
  have hmax : max s.phase.val t.phase.val ≤ p := max_le hsp htp
  have hleft := AdvanceNoOvershoot.Transition_left_phase_le_ep_succ_of_wf
    s t hs ht (hsp.trans hp) (htp.trans hp)
  have hright := AdvanceNoOvershoot.Transition_right_phase_le_ep_succ_of_wf
    s t hs ht (hsp.trans hp) (htp.trans hp)
  have hepi := AdvanceNoOvershoot.phaseEpidemicUpdate_right_phase_eq_max_of_wf
    s t hs ht (by omega) (by omega)
  rw [hepi] at hright
  exact ⟨hleft.trans (Nat.add_le_add_right hmax 1),
    hright.trans (Nat.add_le_add_right hmax 1)⟩

theorem phase_upper_succ_stepRel (p : ℕ) (hp : p ≤ 8)
    (c c' : Cfg L K) (hstep : (NonuniformMajority L K).StepRel c c')
    (hwf : AdvanceNoOvershoot.Wf c)
    (hupper : ∀ a ∈ c, a.phase.val ≤ p) :
    ∀ a ∈ c', a.phase.val ≤ p + 1 := by
  classical
  rcases hstep with ⟨r, q, happ, hc'⟩
  dsimp [Protocol.Applicable, NonuniformMajority] at happ hc'
  have hr : r ∈ c := Multiset.mem_of_le happ (by simp)
  have hq : q ∈ c := Multiset.mem_of_le happ (by simp)
  have hpair := transition_phase_upper_succ p hp r q (hwf r hr) (hwf q hq)
    (hupper r hr) (hupper q hq)
  rw [hc']
  intro a ha
  simp only [Multiset.mem_add, Multiset.mem_cons, Multiset.mem_singleton] at ha
  rcases ha with hold | hnew
  · exact (hupper a (Multiset.mem_of_le (Multiset.sub_le_self c {r, q}) hold)).trans
      (Nat.le_succ p)
  · rcases hnew with hnew | hnew
    · simpa only [hnew] using hpair.1
    · simpa only [hnew] using hpair.2

theorem phase_upper_succ_stepOrSelf (p : ℕ) (hp : p ≤ 8)
    (c : Cfg L K) (hwf : AdvanceNoOvershoot.Wf c)
    (hupper : ∀ a ∈ c, a.phase.val ≤ p) (s t : AgentState L K) :
    ∀ a ∈ Protocol.stepOrSelf (NonuniformMajority L K) c s t,
      a.phase.val ≤ p + 1 := by
  classical
  by_cases happ : Protocol.Applicable c s t
  · have hstep : (NonuniformMajority L K).StepRel c
        (Protocol.stepOrSelf (NonuniformMajority L K) c s t) := by
      refine ⟨s, t, happ, ?_⟩
      unfold Protocol.stepOrSelf
      rw [if_pos happ] <;> rfl
    exact phase_upper_succ_stepRel p hp _ _ hstep hwf hupper
  · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]
    intro a ha
    exact (hupper a ha).trans (Nat.le_succ p)

theorem phase_upper_succ_applyDraw (p : ℕ) (hp : p ≤ 8)
    (c : Cfg L K) (hwf : AdvanceNoOvershoot.Wf c)
    (hupper : ∀ a ∈ c, a.phase.val ≤ p) (d : Draw L K) :
    ∀ a ∈ applyDraw c d, a.phase.val ≤ p + 1 := by
  cases d with
  | none =>
      intro a ha
      exact (hupper a ha).trans (Nat.le_succ p)
  | some pair =>
      exact phase_upper_succ_stepOrSelf p hp c hwf hupper pair.1.1 pair.2.1

/-- At the genuine first threshold hit, no phase overshoots the threshold.
Only observed starting safety and actual initial reachability are used. -/
theorem first_threshold_upper {n : ℕ}
    (init : InputCfg n) (hvalid : validInitial init) (ω : InputLog n)
    (s t q : ℕ) (hqlo : 2 ≤ q) (hqhi : q ≤ 9)
    (hstart : ∀ a ∈ trace init ω s, a.phase.val = 1)
    (hsafe : AllSmallSafe (trace init ω s)) (hst : s ≤ t)
    (hfirst : StageEventSpec.firstHit (StageEventSpec.someGE (n := n) q)
      (trace init ω) t) :
    ∀ a ∈ trace init ω t, a.phase.val ≤ q := by
  have hslt : s < t := by
    by_contra h
    have heq : s = t := by omega
    obtain ⟨a, ha, hqa⟩ := hfirst.1
    have hone : a.phase.val = 1 := hstart a (by simpa only [heq] using ha)
    omega
  let u := t - 1
  have hsu : s ≤ u := by dsimp [u]; omega
  have hut : u < t := by dsimp [u]; omega
  have hutime : u + 1 = t := by dsimp [u]; omega
  have hreach := TimeTheorem.trace_reachable init ω hsu
  have hlo : ∀ a ∈ trace init ω u, 1 ≤ a.phase.val :=
    phase_lower_reachable 1 _ _ hreach (fun a ha => (hstart a ha).symm.le)
  have hpre : ∀ a ∈ trace init ω u, a.phase.val ≤ q - 1 := by
    intro a ha
    have hnot : ¬ q ≤ a.phase.val := fun h => hfirst.2 u hut ⟨a, ha, h⟩
    omega
  have hsafeu := small_safe_reachable _ _ hreach
    (fun a ha => (hstart a ha).symm.le) hsafe
  have hwf : AdvanceNoOvershoot.Wf (trace init ω u) :=
    reachable_small_safe_wf init _ hvalid
      (PhaseZeroEntry.phase_zero_trace_reachable init ω u)
      hlo (fun a ha => (hpre a ha).trans (by omega)) hsafeu
  have hnext := phase_upper_succ_applyDraw (q - 1) (by omega)
    (trace init ω u) hwf hpre (ω (u + 1))
  have htrace : trace init ω t =
      applyDraw (trace init ω u) (ω (u + 1)) := by
    rw [← hutime, TimeTheorem.trace_succ]
  intro a ha
  rw [htrace] at ha
  have hbound := hnext a ha
  omega

theorem readyProfile_small_safe {n : ℕ} {init c : InputCfg n}
    (hp : PhaseOneReadyProfile init c) : AllSmallSafe c := by
  intro a ha
  have h := hp.drained.2.1 a ha
  simp only [Finset.mem_insert, Finset.mem_singleton] at h
  unfold SmallSafe
  omega

theorem readyProfile_small_safe_future {n : ℕ}
    (init : InputCfg n) (ω : InputLog n) (s u : ℕ)
    (hp : PhaseOneReadyProfile init (trace init ω s)) (hsu : s ≤ u) :
    AllSmallSafe (trace init ω u) :=
  small_safe_reachable _ _ (TimeTheorem.trace_reachable init ω hsu)
    (fun a ha => (hp.all_one a ha).symm.le) (readyProfile_small_safe hp)

theorem ready_firstLater_exact_seed {n : ℕ}
    (init : InputCfg n) (ω : InputLog n) (s t : ℕ)
    (hp : PhaseOneReadyProfile init (trace init ω s)) (hst : s ≤ t)
    (ht : firstLater init ω = (t : WithTop ℕ)) :
    firstPhaseSeed init 2 t ω := by
  have hfirst := (firstLater_eq_iff init ω t).1 ht
  have hupper := first_threshold_upper init hp.valid_initial ω s t 2
    (by decide) (by decide) hp.all_one (readyProfile_small_safe hp) hst hfirst
  constructor
  · obtain ⟨a, ha, hphase⟩ := hfirst.1
    exact ⟨a, ha, Nat.le_antisymm (hupper a ha) hphase⟩
  · intro u hu a ha
    exact Nat.lt_of_not_ge (fun h => hfirst.2 u hu ⟨a, ha, h⟩)

theorem ready_first_crossing_no_backup {n : ℕ}
    (init : InputCfg n) (ω : InputLog n) (s t : ℕ)
    (hp : PhaseOneReadyProfile init (trace init ω s)) (hst : s ≤ t)
    (hfirst : StageEventSpec.firstHit (StageEventSpec.someGE (n := n) 3)
      (trace init ω) t) :
    ∀ a ∈ trace init ω t, a.phase.val ≠ 10 := by
  have hupper := first_threshold_upper init hp.valid_initial ω s t 3
    (by decide) (by decide) hp.all_one (readyProfile_small_safe hp) hst hfirst
  intro a ha hten
  have hbound := hupper a ha
  omega

theorem ready_first_crossing_seed_profile {n : ℕ}
    (init : InputCfg n) (ω : InputLog n) (s t : ℕ)
    (hp : PhaseOneReadyProfile init (trace init ω s)) (hst : s ≤ t)
    (hfirst : StageEventSpec.firstHit (StageEventSpec.someGE (n := n) 3)
      (trace init ω) t) :
    StageEventSpec.SeedProfile n init (trace init ω t) :=
  (seed_profile_and_counts_from_phase_one init ω s t hp.valid_initial hp.card_eq
    hp.all_one hp.role_good hst hfirst
    (ready_first_crossing_no_backup init ω s t hp hst hfirst)).1

def SeedOrStableBy {n : ℕ} (init : InputCfg n) (ω : InputLog n)
    (s N : ℕ) : Prop :=
  (∃ u, s ≤ u ∧ u ≤ s + N ∧ trace init ω u ∈
    StableDone (PhaseThreeModel.Numeric.hourIndex n) 256 init) ∨
  ∃ t, s ≤ t ∧ t ≤ s + N ∧
    StageEventSpec.firstHit (StageEventSpec.someGE (n := n) 3) (trace init ω) t ∧
    StageEventSpec.SeedProfile n init (trace init ω t)

theorem ready_profiled_outcome_is_seed_or_stable {n : ℕ}
    (init : InputCfg n) (ω : InputLog n) (s N : ℕ)
    (hp : PhaseOneReadyProfile init (trace init ω s))
    (hout : ProfiledOutcomeBy init ω s N) :
    SeedOrStableBy init ω s N := by
  rcases hout with hdone | ⟨t, hst, htN, hfirst, _⟩
  · exact Or.inl hdone
  · exact Or.inr ⟨t, hst, htN, hfirst,
      ready_first_crossing_seed_profile init ω s t hp hst hfirst⟩

/-- Actual drained-start production of a fresh first Phase-3 seed or
correct stable output, under the original pair-log law. -/
theorem drained_seed_or_stable_tail_at_past_time {n : ℕ}
    (init : InputCfg n) (hinput : ThresholdEpidemic.GoodInput n init) (hn : 2 ≤ n)
    (σ : InputLog n → WithTop ℕ) (hσ : PairLogPastTime σ) :
    law init {ω | ∃ s : ℕ, σ ω = (s : WithTop ℕ) ∧
      PhaseOneReadyProfile init (trace init ω s) ∧
      ¬ SeedOrStableBy init ω s (outcomeHorizon init hn)} ≤ outcomeBudget n := by
  refine (measure_mono ?_).trans
    (drained_outcome_tail_at_past_time init hinput hn σ hσ)
  rintro ω ⟨s, hs, hp, hbad⟩
  refine ⟨s, hs, hp, ?_⟩
  intro hout
  exact hbad (ready_profiled_outcome_is_seed_or_stable init ω s
    (outcomeHorizon init hn) hp hout)


/-- The exact Phase-2 seed, at its genuine global first threshold hit. -/
def FirstTwoSeedBy {n : ℕ} (init : InputCfg n) (ω : InputLog n) (s : ℕ) : Prop :=
  ∃ r : ℕ, s ≤ r ∧ r ≤ s + timerHorizon n ∧ firstPhaseSeed init 2 r ω

theorem drained_first_two_seed_tail_at_past_time {n : ℕ}
    (init : InputCfg n) (hn : 2 ≤ n)
    (σ : InputLog n → WithTop ℕ) (hσ : PairLogPastTime σ) :
    law init {ω | ∃ s : ℕ, σ ω = (s : WithTop ℕ) ∧
      PhaseOneReadyProfile init (trace init ω s) ∧ ¬ FirstTwoSeedBy init ω s} ≤
        1 / (n : ℝ≥0∞) ^ 5 := by
  refine (measure_mono ?_).trans
    (phase_one_timer_conditional_producer init hn σ hσ)
  rintro ω ⟨s, hs, hp, hbad⟩
  by_contra hgood
  obtain ⟨r, hr, hsr, hrbound⟩ := exists_firstLater_of_not_failure init σ ω s hs
    (readyProfile_timerEntry (by omega) hp) hgood
  exact hbad ⟨r, hsr, hrbound, ready_firstLater_exact_seed init ω s r hp hsr hr⟩

/-- The all-GE-2 endpoint is a threshold event; it may already contain
Phase 3. No pure-Phase-2 endpoint claim is made. -/
def FirstTwoAndAllBy {n : ℕ} (init : InputCfg n) (ω : InputLog n) (s : ℕ) : Prop :=
  ∃ r t : ℕ, s ≤ r ∧ r ≤ s + timerHorizon n ∧ firstPhaseSeed init 2 r ω ∧
    StageEventSpec.firstHit (StageEventSpec.allGE (n := n) 2) (trace init ω) t ∧
    r ≤ t ∧ t ≤ r + StageEventSpec.activationHorizon n

theorem first_two_and_all_failure_cover {n : ℕ}
    (init : InputCfg n) (hn : 2 ≤ n) (σ : InputLog n → WithTop ℕ) :
    {ω | ∃ s : ℕ, σ ω = (s : WithTop ℕ) ∧
      PhaseOneReadyProfile init (trace init ω s) ∧ ¬ FirstTwoAndAllBy init ω s} ⊆
        timerFailure init σ ∪ thresholdFailureAt init n 2
          (StageEventSpec.activationHorizon n) (firstLater init) := by
  classical
  rintro ω ⟨s, hs, hp, hbad⟩
  by_cases htimer : ω ∈ timerFailure init σ
  · exact Or.inl htimer
  by_cases hflood : ω ∈ thresholdFailureAt init n 2
      (StageEventSpec.activationHorizon n) (firstLater init)
  · exact Or.inr hflood
  exfalso
  obtain ⟨r, hr, hsr, hrbound⟩ := exists_firstLater_of_not_failure init σ ω s hs
    (readyProfile_timerEntry (by omega) hp) htimer
  have hrfirst := (firstLater_eq_iff init ω r).1 hr
  have hrseed := ready_firstLater_exact_seed init ω s r hp hsr hr
  have hcardr : (trace init ω r).card = n :=
    (Protocol.reachable_card_eq (TimeTheorem.trace_reachable init ω hsr)).trans hp.card_eq
  have hflooded : ∀ a ∈ trace init ω (r + StageEventSpec.activationHorizon n),
      2 ≤ a.phase.val := by
    by_contra hno
    exact hflood ⟨r, hr, hcardr, hrfirst.1, hno⟩
  obtain ⟨t, htfirst, hrt, htbound⟩ :=
    exists_first_all_after_first_seed init ω n 2 r (StageEventSpec.activationHorizon n)
      (by omega) hcardr hrseed hflooded
  exact hbad ⟨r, t, hsr, hrbound, hrseed, htfirst, hrt, htbound⟩

theorem drained_first_two_and_all_tail_at_past_time {n : ℕ}
    (init : InputCfg n) (hn : 2 ≤ n)
    (σ : InputLog n → WithTop ℕ) (hσ : PairLogPastTime σ) :
    law init {ω | ∃ s : ℕ, σ ω = (s : WithTop ℕ) ∧
      PhaseOneReadyProfile init (trace init ω s) ∧ ¬ FirstTwoAndAllBy init ω s} ≤
        3 / (n : ℝ≥0∞) ^ 5 := by
  have htimer := phase_one_timer_conditional_producer init hn σ hσ
  have hflood := (threshold_spread_at_past_time init hn 2 (by decide)
    (StageEventSpec.activationHorizon n) (firstLater init) (firstLater_past init)).trans
      (activation_thresholdBudget_le hn)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hcast : ENNReal.ofReal (2 / (n : ℝ) ^ 5) = 2 / (n : ℝ≥0∞) ^ 5 := by
    rw [ENNReal.ofReal_div_of_pos (pow_pos hnpos 5),
      ENNReal.ofReal_pow (Nat.cast_nonneg n), ENNReal.ofReal_natCast]
    norm_num
  rw [hcast] at hflood
  calc
    law init {ω | ∃ s : ℕ, σ ω = (s : WithTop ℕ) ∧
        PhaseOneReadyProfile init (trace init ω s) ∧ ¬ FirstTwoAndAllBy init ω s} ≤
      law init (timerFailure init σ ∪ thresholdFailureAt init n 2
        (StageEventSpec.activationHorizon n) (firstLater init)) :=
      measure_mono (first_two_and_all_failure_cover init hn σ)
    _ ≤ law init (timerFailure init σ) + law init (thresholdFailureAt init n 2
        (StageEventSpec.activationHorizon n) (firstLater init)) := measure_union_le _ _
    _ ≤ 1 / (n : ℝ≥0∞) ^ 5 + 2 / (n : ℝ≥0∞) ^ 5 :=
      add_le_add htimer hflood
    _ = 3 / (n : ℝ≥0∞) ^ 5 := by
      simp only [div_eq_mul_inv]
      ring

/-- A current-state height callback suffices for safe activation. The proof
first excludes a backup output using the unconditional small-bias invariant,
then uses the active-Clock ceiling to exclude a Phase-4 output. -/
theorem safe_activation_range_trace (init : Cfg L 256) (hvalid : validInitial init)
    (ω : Ω L 256) (s t : ℕ) (hst : s ≤ t)
    (hstart : ∀ a ∈ trace init ω s, 1 ≤ a.phase.val ∧ a.phase.val ≤ 3)
    (hsafe : AllSmallSafe (trace init ω s))
    (hlow : ∀ u, s ≤ u → u < t →
      (∀ a ∈ trace init ω u, a.phase.val ≠ 10) →
        PhaseTwoActivation.ActiveClockBelow (trace init ω u)) :
    ∀ a ∈ trace init ω t, 1 ≤ a.phase.val ∧ a.phase.val ≤ 3 := by
  revert hlow
  induction t, hst using Nat.le_induction with
  | base =>
      intro _
      exact hstart
  | succ t hst ih =>
      intro hlow
      have hprevious := ih (fun u hsu hut hno => hlow u hsu (by omega) hno)
      have hnoprev : ∀ a ∈ trace init ω t, a.phase.val ≠ 10 := by
        intro a ha hten
        have hcap := (hprevious a ha).2
        omega
      have hclock := hlow t hst (Nat.lt_succ_self t) hnoprev
      have hsafeCurrent := small_safe_reachable _ _
        (TimeTheorem.trace_reachable init ω hst)
        (fun a ha => (hstart a ha).1) hsafe
      have hactual : (NonuniformMajority L 256).Reachable init (trace init ω t) := by
        simpa only [TraceDrain.trace_zero] using
          (TimeTheorem.trace_reachable init ω (Nat.zero_le t))
      have hwf := reachable_small_safe_wf init _ hvalid hactual
        (fun a ha => (hprevious a ha).1)
        (fun a ha => (hprevious a ha).2.trans (by decide)) hsafeCurrent
      have hfour := phase_upper_succ_applyDraw 3 (by decide) (trace init ω t) hwf
        (fun a ha => (hprevious a ha).2) (ω (t + 1))
      rw [TimeTheorem.trace_succ]
      apply PhaseTwoActivation.activation_range_draw _ (ω (t + 1)) hprevious hclock
      intro a ha hten
      have hcap := hfour a ha
      omega

theorem safe_activation_window (init : Cfg L 256) (hvalid : validInitial init)
    (ω : Ω L 256) (s t : ℕ)
    (hstart : ∀ a ∈ trace init ω s, 1 ≤ a.phase.val ∧ a.phase.val ≤ 3)
    (hsafe : AllSmallSafe (trace init ω s))
    (hlow : ∀ u, s ≤ u → u ≤ t →
      (∀ a ∈ trace init ω u, a.phase.val ≠ 10) →
        PhaseTwoActivation.ActiveClockBelow (trace init ω u)) :
    (∀ u, s ≤ u → u ≤ t → ∀ a ∈ trace init ω u,
      1 ≤ a.phase.val ∧ a.phase.val ≤ 3) ∧
    (∀ u, s ≤ u → u ≤ t →
      PhaseTwoActivation.ActiveClockBelow (trace init ω u)) := by
  have hwindow : ∀ u, s ≤ u → u ≤ t → ∀ a ∈ trace init ω u,
      1 ≤ a.phase.val ∧ a.phase.val ≤ 3 := by
    intro u hsu hut
    exact safe_activation_range_trace init hvalid ω s u hsu hstart hsafe
      (fun v hsv hvu hno => hlow v hsv (hvu.le.trans hut) hno)
  refine ⟨hwindow, ?_⟩
  intro u hsu hut
  apply hlow u hsu hut
  intro a ha hten
  have hcap := (hwindow u hsu hut a ha).2
  omega

theorem drained_async_entry_of_low_clock {n : ℕ}
    (init : InputCfg n) (ω : InputLog n) (d s t : ℕ)
    (hp : PhaseOneReadyProfile init (trace init ω d)) (hds : d ≤ s)
    (hseedFirst : StageEventSpec.firstHit (StageEventSpec.someGE (n := n) 3)
      (trace init ω) s)
    (hallFirst : StageEventSpec.firstHit (StageEventSpec.allGE (n := n) 3)
      (trace init ω) t)
    (hst : s ≤ t) (hdeadline : t ≤ s + StageEventSpec.activationHorizon n)
    (hseed : StageEventSpec.SeedProfile n init (trace init ω s))
    (hlow : ∀ u, s ≤ u → u ≤ t →
      (∀ a ∈ trace init ω u, a.phase.val ≠ 10) →
        PhaseTwoActivation.ActiveClockBelow (trace init ω u)) :
    StageEventSpec.AsyncEntry init ω s t := by
  have hsafe := readyProfile_small_safe_future init ω d s hp hds
  have hwindow := safe_activation_window init hp.valid_initial ω s t
    hseed.phase_range hsafe hlow
  exact PhaseTwoActivation.async_entry_of_window init hp.valid_initial ω s t
    hseedFirst hallFirst hst hdeadline hseed hwindow.1 hwindow.2

end Ripple.PopulationProtocol.ExactMajority.PhaseTwoDrainedSafety

end
