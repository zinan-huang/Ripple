-- Ripple/PopulationProtocol/ExactMajority/Probability/StrongContinuationTimer.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseOneTimer
import Ripple.PopulationProtocol.ExactMajority.Probability.UniformRecovery

/-!
Upper timers in the four actual late timed phases.  The observable
potential is the existing sum of 2^counter over Clocks, killed when the
population leaves the homogeneous phase.  No lower survival allowance
or fresh-counter premise is used.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal BigOperators

namespace Ripple.PopulationProtocol.ExactMajority.StrongContinuationTimer

open TimeTheorem PairLog PhaseOneDrain PhaseOneDrainStopping UniformRecovery
  PhaseOneTimer

variable {L K : ℕ}

def TimedPhase (p : ℕ) : Prop := p ∈ ({5, 6, 7, 8} : Finset ℕ)

theorem timed_bounds {p : ℕ} (hp : TimedPhase p) : 3 ≤ p ∧ p < 10 := by
  unfold TimedPhase at hp
  fin_cases hp <;> omega

theorem timed_mem {p : ℕ} (hp : TimedPhase p) :
    p ∈ ({1, 5, 6, 7, 8} : Finset ℕ) := by
  unfold TimedPhase at hp
  fin_cases hp <;> simp

open Classical in
def timedPotential (p : ℕ) (c : Cfg L K) : ℕ :=
  if PurePhase p c then rawPotential c else 0

def TimedWindow (p n : ℕ) (c : Cfg L K) : Prop :=
  c.card = n ∧ PurePhase p c

def HigherSeed (p : ℕ) (c : Cfg L K) : Prop :=
  ∃ a ∈ c, p < a.phase.val

theorem timedPotential_le_card (p : ℕ) (c : Cfg L K) :
    timedPotential p c ≤ c.card * 2 ^ (50 * (L + 1)) := by
  classical
  by_cases h : PurePhase p c
  · simpa only [timedPotential, if_pos h] using rawPotential_le_card c
  · simp only [timedPotential, if_neg h, zero_le]

theorem zero_clock_advances (p : ℕ) (hp : TimedPhase p)
    (a : AgentState L K) (hphase : a.phase.val = p)
    (hzero : a.counter.val = 0) :
    p < (finishPhase10Entry L K a (stdCounterSubroutine L K a)).phase.val := by
  rw [finishPhase10Entry_phase_val, stdCounterSubroutine, dif_pos hzero]
  have hadv : (advancePhase L K a).phase.val = p + 1 := by
    simp [advancePhase, hphase, (timed_bounds hp).2]
  change p < (phaseInit L K (advancePhase L K a).phase (advancePhase L K a)).phase.val
  have hnondec := phaseInit_phase_nondec L K
    (advancePhase L K a).phase (advancePhase L K a)
  rw [hadv] at hnondec
  omega

theorem timed_pair_halving (p : ℕ) (hp : TimedPhase p)
    (s t : AgentState L K)
    (hs : s.phase.val = p) (ht : t.phase.val = p)
    (hsout : (Transition L K s t).1.phase.val = p)
    (htout : (Transition L K s t).2.phase.val = p) :
    2 * (clockWeight (Transition L K s t).1 +
      clockWeight (Transition L K s t).2) = clockWeight s + clockWeight t := by
  classical
  have hpall := timed_mem hp
  have hpge := (timed_bounds hp).1
  have hleft : 2 * clockWeight (Transition L K s t).1 = clockWeight s := by
    by_cases hc : s.role = .clock
    · have hz : s.counter.val ≠ 0 := by
        intro hzero
        have he := zero_clock_advances p hp s hs hzero
        rw [← timed_transition_left_clock p hpall s t hs ht hc, hsout] at he
        exact (lt_irrefl _ he)
      have hpow : 2 * 2 ^ (s.counter.val - 1) = 2 ^ s.counter.val := by
        rw [mul_comm, ← pow_succ]
        congr 1
        omega
      rw [timed_transition_left_clock p hpall s t hs ht hc]
      simpa only [clockWeight, finishPhase10Entry_role, finishPhase10Entry_counter,
        stdCounterSubroutine, dif_neg hz, hc, if_pos] using hpow
    · have hout := MixedWindowClosure.Transition_first_no_clock_creation_of_phase_ge_3
        s t (by omega) (by omega) hc
      simp only [clockWeight, if_neg hc, if_neg hout, mul_zero]
  have hright : 2 * clockWeight (Transition L K s t).2 = clockWeight t := by
    by_cases hc : t.role = .clock
    · have hz : t.counter.val ≠ 0 := by
        intro hzero
        have he := zero_clock_advances p hp t ht hzero
        rw [← timed_transition_right_clock p hpall s t hs ht hc, htout] at he
        exact (lt_irrefl _ he)
      have hpow : 2 * 2 ^ (t.counter.val - 1) = 2 ^ t.counter.val := by
        rw [mul_comm, ← pow_succ]
        congr 1
        omega
      rw [timed_transition_right_clock p hpall s t hs ht hc]
      simpa only [clockWeight, finishPhase10Entry_role, finishPhase10Entry_counter,
        stdCounterSubroutine, dif_neg hz, hc, if_pos] using hpow
    · have hout := MixedWindowClosure.Transition_second_no_clock_creation_of_phase_ge_3
        s t (by omega) (by omega) hc
      simp only [clockWeight, if_neg hc, if_neg hout, mul_zero]
  omega

theorem timedPotential_pair_drop (p : ℕ) (hp : TimedPhase p)
    (c : Cfg L K) (h : PurePhase p c)
    (s t : AgentState L K) (happ : Protocol.Applicable c s t) :
    2 * timedPotential p (Protocol.stepOrSelf (NonuniformMajority L K) c s t) +
      clockWeight s + clockWeight t ≤ 2 * timedPotential p c := by
  classical
  have hs : s ∈ c := Multiset.mem_of_le happ (by simp)
  have ht : t ∈ c := Multiset.mem_of_le happ (by simp)
  have hstep : Protocol.stepOrSelf (NonuniformMajority L K) c s t =
      c - {s, t} + {(Transition L K s t).1, (Transition L K s t).2} := by
    unfold Protocol.stepOrSelf
    rw [if_pos happ]
    rfl
  by_cases hout : PurePhase p (Protocol.stepOrSelf (NonuniformMajority L K) c s t)
  · have hsout : (Transition L K s t).1.phase.val = p := by
      apply hout
      rw [hstep]
      simp
    have htout : (Transition L K s t).2.phase.val = p := by
      apply hout
      rw [hstep]
      simp
    have hpair := timed_pair_halving p hp s t (h s hs) (h t ht) hsout htout
    simp only [timedPotential, if_pos h, if_pos hout]
    rw [rawPotential_step_split c s t happ, rawPotential_pair_split c s t happ]
    omega
  · simp only [timedPotential, if_pos h, if_neg hout, mul_zero, zero_add]
    rw [rawPotential_pair_split c s t happ]
    omega

theorem timedPotential_step_le (p : ℕ) (hp : TimedPhase p)
    (c : Cfg L K) (h : PurePhase p c) (s t : AgentState L K) :
    timedPotential p (Protocol.stepOrSelf (NonuniformMajority L K) c s t) ≤
      timedPotential p c := by
  classical
  by_cases happ : Protocol.Applicable c s t
  · have hdrop := timedPotential_pair_drop p hp c h s t happ
    omega
  · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]

theorem applicable_of_positive_count
    (c : Cfg L K) (s t : AgentState L K)
    (h : 0 < c.interactionCount s t) : Protocol.Applicable c s t := by
  classical
  change {s, t} ≤ c
  rw [Multiset.le_iff_count]
  intro a
  simp only [Config.interactionCount, Config.count] at h
  simp only [Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton]
  by_cases heq : s = t
  · subst heq
    simp only [ite_true] at h
    have htwo : 2 ≤ Multiset.count s c := by
      by_contra hlt
      have hle : Multiset.count s c ≤ 1 := by omega
      have hzero : Multiset.count s c * (Multiset.count s c - 1) = 0 := by
        rcases Nat.eq_zero_or_pos (Multiset.count s c) with hz | hp
        · simp [hz]
        · have hone : Multiset.count s c = 1 := by omega
          simp [hone]
      omega
    by_cases ha : a = s <;> simp_all
  · simp only [if_neg heq] at h
    have hspos : 0 < Multiset.count s c :=
      pos_of_mul_pos_left h (Nat.zero_le _)
    have htpos : 0 < Multiset.count t c :=
      pos_of_mul_pos_right h (Nat.zero_le _)
    by_cases has : a = s <;> by_cases hat : a = t <;> simp_all <;> omega


theorem timed_weighted_pair_drop (p : ℕ) (hp : TimedPhase p)
    (c : Cfg L K) (h : PurePhase p c) (s t : AgentState L K) :
    (((clockWeight s : ℝ≥0∞) + (clockWeight t : ℝ≥0∞)) / 2) *
        c.interactionProb s t ≤
      ((timedPotential p c : ℝ≥0∞) -
        (timedPotential p (Protocol.stepOrSelf (NonuniformMajority L K) c s t) : ℝ≥0∞)) *
          c.interactionProb s t := by
  classical
  by_cases happ : Protocol.Applicable c s t
  · have hpair := timedPotential_pair_drop p hp c h s t happ
    have hm := timedPotential_step_le p hp c h s t
    have hn : clockWeight s + clockWeight t ≤
        2 * (timedPotential p c -
          timedPotential p (Protocol.stepOrSelf (NonuniformMajority L K) c s t)) := by omega
    have he : ((clockWeight s : ℝ≥0∞) + (clockWeight t : ℝ≥0∞)) / 2 ≤
        (timedPotential p c : ℝ≥0∞) -
          (timedPotential p (Protocol.stepOrSelf (NonuniformMajority L K) c s t) : ℝ≥0∞) := by
      apply (ENNReal.div_le_iff' (by norm_num) (by norm_num)).2
      have hcast : ((clockWeight s + clockWeight t : ℕ) : ℝ≥0∞) ≤
          ((2 * (timedPotential p c -
            timedPotential p (Protocol.stepOrSelf (NonuniformMajority L K) c s t)) : ℕ) : ℝ≥0∞) :=
        by exact_mod_cast hn
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, ENNReal.natCast_sub] using hcast
    exact mul_le_mul_right' he _
  · have hz : c.interactionCount s t = 0 := by
      apply Nat.eq_zero_of_not_pos
      intro hpos
      exact happ (applicable_of_positive_count c s t hpos)
    simp only [Config.interactionProb, hz, Nat.cast_zero, ENNReal.zero_div, mul_zero, le_refl]

theorem timed_weighted_drop (p : ℕ) (hp : TimedPhase p)
    (n : ℕ) (hn : 2 ≤ n) (c : Cfg L K) (hwin : TimedWindow p n c) :
    (1 / (n : ℝ≥0∞)) * timedPotential p c ≤
      WeightedDriftDropSum.weightedDropSum (NonuniformMajority L K) (timedPotential p) c := by
  classical
  have hc : 2 ≤ c.card := by rw [hwin.1]; exact hn
  let w : AgentState L K → ℝ≥0∞ := fun a => clockWeight a
  have hmass : Config.sumOf w c = (timedPotential p c : ℝ≥0∞) := by
    rw [timedPotential, if_pos hwin.2]
    exact rawPotential_cast c
  have hsum :
      (∑ z : AgentState L K × AgentState L K,
        ((w z.1 + w z.2) / 2) * c.interactionProb z.1 z.2) =
      (timedPotential p c : ℝ≥0∞) / (n : ℝ≥0∞) := by
    calc
      _ = (∑ z : AgentState L K × AgentState L K,
          (w z.1 + w z.2) * c.interactionProb z.1 z.2) / 2 := by
        simp only [div_eq_mul_inv, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro z _
        ring
      _ = (Config.sumOf w c / (c.card : ℝ≥0∞) +
          Config.sumOf w c / (c.card : ℝ≥0∞)) / 2 := by
        simp_rw [add_mul]
        rw [Finset.sum_add_distrib, Phase0Window.sum_fst_interactionProb c hc,
          Phase0Window.sum_snd_interactionProb c hc]
      _ = _ := by rw [hmass, hwin.1, ENNReal.add_div, ENNReal.add_halves]
  calc
    _ = (timedPotential p c : ℝ≥0∞) / (n : ℝ≥0∞) := by
      rw [div_eq_mul_inv, div_eq_mul_inv, one_mul, mul_comm]
    _ = ∑ z : AgentState L K × AgentState L K,
        ((w z.1 + w z.2) / 2) * c.interactionProb z.1 z.2 := hsum.symm
    _ ≤ _ := by
      unfold WeightedDriftDropSum.weightedDropSum
      apply Finset.sum_le_sum
      intro z _
      exact timed_weighted_pair_drop p hp c hwin.2 z.1 z.2

theorem timedPotential_drift (p : ℕ) (hp : TimedPhase p)
    (n : ℕ) (hn : 2 ≤ n) (c : Cfg L K) (hwin : TimedWindow p n c) :
    (∫⁻ c', (timedPotential p c' : ℝ≥0∞)
      ∂(NonuniformMajority L K).transitionKernel c) ≤
        (1 - 1 / (n : ℝ≥0∞)) * timedPotential p c := by
  have hc : 2 ≤ c.card := by rw [hwin.1]; exact hn
  have hnzero : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  exact WeightedDriftDropSum.weighted_dyadic_mass_drift_of_dropSum
    (NonuniformMajority L K) (timedPotential p) c hc (1 / (n : ℝ≥0∞))
    (ENNReal.div_ne_top (by norm_num) hnzero)
    (fun z => timedPotential_step_le p hp c hwin.2 z.1 z.2)
    (timed_weighted_drop p hp n hn c hwin)

theorem no_higher_window (init : Cfg L K) (hinit : validInitial init)
    (p : ℕ) (hp : TimedPhase p) (ω : Ω L K)
    (n : ℕ) (hn : 2 ≤ n) (s N : ℕ)
    (he : TimedWindow p n (trace init ω s))
    (hno : ¬ HigherSeed p (trace init ω (s + N))) :
    (∀ u, s ≤ u → u ≤ s + N →
      TimedWindow p n (trace init ω u)) ∧
      1 ≤ timedPotential p (trace init ω (s + N)) := by
  classical
  have hlo := phase_lower_reachable p _ _
    (trace_reachable init ω (Nat.le_add_right s N))
    (fun a ha => (he.2 a ha).symm.le)
  have hend : PurePhase p (trace init ω (s + N)) := by
    intro a ha
    have hu : a.phase.val ≤ p := by
      by_contra h
      exact hno ⟨a, ha, by omega⟩
    have hl := hlo a ha
    omega
  have hwin : ∀ u, s ≤ u → u ≤ s + N →
      TimedWindow p n (trace init ω u) := by
    intro u hsu hut
    refine ⟨(Protocol.reachable_card_eq (trace_reachable init ω hsu)).trans he.1, ?_⟩
    exact phase_eq_between init ω p s u (s + N) hsu hut he.2 hend
  refine ⟨hwin, ?_⟩
  have hreach : ReachableFrom L K init (trace init ω (s + N)) := by
    simpa only [trace_zero] using
      trace_reachable init ω (s := 0) (t := s + N) (Nat.zero_le _)
  have hcard : (trace init ω (s + N)).card = n := (hwin _ (by omega) le_rfl).1
  have hcp : 0 < (trace init ω (s + N)).card := by omega
  obtain ⟨a, b, hab, ha, hb⟩ :=
    reachable_positive_phase_has_clockPair init _ hinit hreach hcp p
      (by have := (timed_bounds hp).1; omega) hend
  have hclock : 1 ≤ RoleSplitConcentration.clockCount (trace init ω (s + N)) := by
    apply Nat.succ_le_of_lt
    exact Multiset.countP_pos.mpr ⟨a, Multiset.mem_of_le hab (by simp), ha⟩
  rw [timedPotential, if_pos hend]
  exact hclock.trans (clockCount_le_rawPotential _)

/-- A genuine observed prefix, with no future survival premise. -/
theorem timed_tail_from_prefix (init : Cfg L K) (hinit : validInitial init)
    (p : ℕ) (hp : TimedPhase p) (n : ℕ) (hn : 2 ≤ n)
    (s N : ℕ) (A : Set ((k : Finset.Iic s) → Draw L K))
    (hentry : ∀ a ∈ A, TimedWindow p n (prefixCfg init s a)) :
    law init {ω | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A ∧
      ¬ HigherSeed p (trace init ω (s + N))} ≤
      (1 - 1 / (n : ℝ≥0∞)) ^ N *
        ((n * 2 ^ (50 * (L + 1)) : ℕ) : ℝ≥0∞) *
          law init {ω | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A} := by
  have hbound : ∀ a ∈ A,
      timedPotential p (prefixCfg init s a) ≤ n * 2 ^ (50 * (L + 1)) := by
    intro a ha
    simpa only [(hentry a ha).1] using timedPotential_le_card p (prefixCfg init s a)
  have ht := TraceDrain.potential_drift_tail_from init (timedPotential p)
    (TimedWindow p n) (1 / (n : ℝ≥0∞))
    (fun c hc => timedPotential_drift p hp n hn c hc) s N A
    (n * 2 ^ (50 * (L + 1))) hbound
  apply (measure_mono ?_).trans ht
  rintro ω ⟨hA, hno⟩
  have hw := no_higher_window init hinit p hp ω n hn s N (hentry _ hA) hno
  exact ⟨hA, fun u hu hu' => hw.1 u hu hu'.le, hw.2⟩

theorem timed_tail_calibrated {n : ℕ} (init : InputCfg n)
    (hinit : validInitial init) (p : ℕ) (hp : TimedPhase p) (hn : 2 ≤ n)
    (s : ℕ) (A : Set ((k : Finset.Iic s) → Draw (PhaseThreeModel.Numeric.hourIndex n) 256))
    (hentry : ∀ a ∈ A, TimedWindow p n (prefixCfg init s a)) :
    law init {ω | frestrictLe (π := fun _ : ℕ => Draw _ _) s ω ∈ A ∧
      ¬ HigherSeed p (trace init ω (s + timerHorizon n))} ≤
      ENNReal.ofReal (1 / (n : ℝ) ^ 5) *
        law init {ω | frestrictLe (π := fun _ : ℕ => Draw _ _) s ω ∈ A} := by
  have ht := timed_tail_from_prefix init hinit p hp n hn s (timerHorizon n) A hentry
  have hbudget := timerBudget_le n hn
  have hcast : (1 : ℝ≥0∞) / (n : ℝ≥0∞) ^ 5 =
      ENNReal.ofReal (1 / (n : ℝ) ^ 5) := by
    rw [ENNReal.ofReal_div_of_pos (by
      have : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      positivity), ENNReal.ofReal_one,
      ENNReal.ofReal_pow (Nat.cast_nonneg n), ENNReal.ofReal_natCast]
  change law init _ ≤ timerBudget n * law init _ at ht
  exact ht.trans (mul_le_mul_right' (hbudget.trans_eq hcast) _)

end Ripple.PopulationProtocol.ExactMajority.StrongContinuationTimer

end
