import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseOneDrainStopping
import Ripple.PopulationProtocol.ExactMajority.Probability.WeightedDriftDropSum

/-!
# The phase-one timer on the actual recorded-pair execution

The natural potential is the sum of 2^counter over Clocks, killed as soon as
the configuration is no longer entirely in phase one. A positive selected
Clock halves its weight. Selecting a zero-counter Clock kills the potential.
The scheduler's two exact marginals therefore give contraction 1 - 1/n.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal BigOperators

namespace Ripple.PopulationProtocol.ExactMajority.PhaseOneTimer

open TimeTheorem PairLog PhaseOneDrain PhaseOneDrainStopping

variable {L K : ℕ}

def AllOne (c : Cfg L K) : Prop := ∀ a ∈ c, a.phase.val = 1

open Classical in
def clockWeight (a : AgentState L K) : ℕ :=
  if a.role = .clock then 2 ^ a.counter.val else 0

def rawPotential (c : Cfg L K) : ℕ := (c.map clockWeight).sum

open Classical in
def timerPotential (c : Cfg L K) : ℕ :=
  if AllOne c then rawPotential c else 0

theorem rawPotential_cast (c : Cfg L K) :
    Config.sumOf (fun a => (clockWeight a : ℝ≥0∞)) c =
      (rawPotential c : ℝ≥0∞) := by
  unfold Config.sumOf rawPotential
  induction c using Multiset.induction with
  | empty => simp
  | cons a c ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons, Nat.cast_add, ih]

theorem clockWeight_le (a : AgentState L K) :
    clockWeight a ≤ 2 ^ (50 * (L + 1)) := by
  classical
  by_cases hc : a.role = .clock
  · rw [clockWeight, if_pos hc]
    exact Nat.pow_le_pow_right (by norm_num) (by
      have hb := a.counter.isLt
      omega)
  · simp [clockWeight, hc]

theorem rawPotential_le_card (c : Cfg L K) :
    rawPotential c ≤ c.card * 2 ^ (50 * (L + 1)) := by
  unfold rawPotential
  induction c using Multiset.induction with
  | empty => simp
  | cons a c ih =>
      rw [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons]
      have ha := clockWeight_le a
      nlinarith

theorem timerPotential_le_card (c : Cfg L K) :
    timerPotential c ≤ c.card * 2 ^ (50 * (L + 1)) := by
  classical
  by_cases h : AllOne c
  · simpa only [timerPotential, if_pos h] using rawPotential_le_card c
  · simp only [timerPotential, if_neg h, zero_le]

theorem clockCount_le_rawPotential (c : Cfg L K) :
    RoleSplitConcentration.clockCount c ≤ rawPotential c := by
  classical
  unfold RoleSplitConcentration.clockCount rawPotential
  induction c using Multiset.induction with
  | empty => simp
  | cons a c ih =>
      rw [Multiset.countP_cons, Multiset.map_cons, Multiset.sum_cons]
      by_cases hc : a.role = .clock
      · have hw : 1 ≤ 2 ^ a.counter.val := Nat.one_le_two_pow
        simp only [hc, if_pos, clockWeight] at *
        omega
      · have h0 : clockWeight a = 0 := by simp [clockWeight, hc]
        rw [if_neg hc, h0]
        omega

theorem clockCounterStep_ge_two_of_zero (a : AgentState L K)
    (hp : a.phase.val = 1) (hc : a.role = .clock)
    (hz : a.counter.val = 0) :
    2 ≤ (clockCounterStep L K a).phase.val := by
  simp [clockCounterStep, hc, stdCounterSubroutine, hz]
  change 2 ≤ (phaseInit L K (advancePhase L K a).phase
    (advancePhase L K a)).phase.val
  have hb : (advancePhase L K a).phase.val = 2 := by
    simp [advancePhase, hp]
  exact hb.symm.le.trans
    (phaseInit_phase_nondec L K (advancePhase L K a).phase (advancePhase L K a))

theorem phase_pair_eq_phaseOneTransition (s t : AgentState L K)
    (hs : s.phase.val = 1) (ht : t.phase.val = 1) :
    (Transition L K s t).1.phase.val = (Phase1Transition L K s t).1.phase.val ∧
      (Transition L K s t).2.phase.val = (Phase1Transition L K s t).2.phase.val := by
  have hepi := Phase1Convergence.phaseEpidemicUpdate_eq_self_of_phase1
    (L := L) (K := K) s t hs ht
  have hphase : s.phase = ⟨1, by decide⟩ := Fin.ext hs
  constructor
  · simp only [Transition, hepi, hphase]
    rw [finishPhase10Entry_phase_val]
  · simp only [Transition, hepi, hphase]
    rw [finishPhase10Entry_phase_val]

theorem positive_counters_of_phase_one_outputs (s t : AgentState L K)
    (hs : s.phase.val = 1) (ht : t.phase.val = 1)
    (hsout : (Transition L K s t).1.phase.val = 1)
    (htout : (Transition L K s t).2.phase.val = 1) :
    (s.role = .clock → 0 < s.counter.val) ∧
      (t.role = .clock → 0 < t.counter.val) := by
  have hp := phase_pair_eq_phaseOneTransition s t hs ht
  constructor
  · intro hc
    by_contra hpos
    have hz : s.counter.val = 0 := by omega
    have hnb : ¬ (s.role = .main ∧ t.role = .main) := by
      intro hm
      rw [hc] at hm
      cases hm.1
    have hraw : (Phase1Transition L K s t).1.phase.val = 1 :=
      hp.1.symm.trans hsout
    rw [PhaseOnlyWindows.Phase1Transition_eq_of_not_both_main s t hnb] at hraw
    have hge := clockCounterStep_ge_two_of_zero s hs hc hz
    change (clockCounterStep L K s).phase.val = 1 at hraw
    omega
  · intro hc
    by_contra hpos
    have hz : t.counter.val = 0 := by omega
    have hnb : ¬ (s.role = .main ∧ t.role = .main) := by
      intro hm
      rw [hc] at hm
      cases hm.2
    have hraw : (Phase1Transition L K s t).2.phase.val = 1 :=
      hp.2.symm.trans htout
    rw [PhaseOnlyWindows.Phase1Transition_eq_of_not_both_main s t hnb] at hraw
    have hge := clockCounterStep_ge_two_of_zero t ht hc hz
    change (clockCounterStep L K t).phase.val = 1 at hraw
    omega

theorem weight_pair_halving (s t : AgentState L K)
    (hs : s.phase.val = 1) (ht : t.phase.val = 1)
    (hsout : (Transition L K s t).1.phase.val = 1)
    (htout : (Transition L K s t).2.phase.val = 1) :
    2 * (clockWeight (Transition L K s t).1 +
      clockWeight (Transition L K s t).2) = clockWeight s + clockWeight t := by
  classical
  have hc := positive_counters_of_phase_one_outputs s t hs ht hsout htout
  have hr := PhaseOnlyWindows.Transition_role_phase1 s t hs ht
  have hf : 2 * clockWeight (Transition L K s t).1 = clockWeight s := by
    by_cases hsclock : s.role = .clock
    · have hpos : 0 < s.counter.val := hc.1 hsclock
      have hcounter :=
        Phase1ClockDepthStopped.transition_fst_clock_counter_eq_sub_one
          s t hs ht hsclock hpos hc.2
      have hp : 2 * 2 ^ (s.counter.val - 1) = 2 ^ s.counter.val := by
        calc
          2 * 2 ^ (s.counter.val - 1) = 2 ^ (s.counter.val - 1 + 1) := by
            rw [pow_succ]
            ac_rfl
          _ = 2 ^ s.counter.val := by congr 1; omega
      simpa only [clockWeight, hr.1, hsclock, if_pos, hcounter] using hp
    · simp only [clockWeight, hr.1, if_neg hsclock, mul_zero]
  have hg : 2 * clockWeight (Transition L K s t).2 = clockWeight t := by
    by_cases htclock : t.role = .clock
    · have hpos : 0 < t.counter.val := hc.2 htclock
      have hcounter :=
        Phase1ClockDepthStopped.transition_snd_clock_counter_eq_sub_one
          s t hs ht hc.1 htclock hpos
      have hp : 2 * 2 ^ (t.counter.val - 1) = 2 ^ t.counter.val := by
        calc
          2 * 2 ^ (t.counter.val - 1) = 2 ^ (t.counter.val - 1 + 1) := by
            rw [pow_succ]
            ac_rfl
          _ = 2 ^ t.counter.val := by congr 1; omega
      simpa only [clockWeight, hr.2, htclock, if_pos, hcounter] using hp
    · simp only [clockWeight, hr.2, if_neg htclock, mul_zero]
  omega

theorem rawPotential_pair_split (c : Cfg L K) (s t : AgentState L K)
    (happ : Protocol.Applicable c s t) :
    rawPotential c = rawPotential (c - {s, t}) +
      (clockWeight s + clockWeight t) := by
  unfold rawPotential
  rw [← Multiset.sub_add_cancel happ, Multiset.map_add, Multiset.sum_add]
  simp

theorem rawPotential_step_split (c : Cfg L K) (s t : AgentState L K)
    (happ : Protocol.Applicable c s t) :
    rawPotential (Protocol.stepOrSelf (NonuniformMajority L K) c s t) =
      rawPotential (c - {s, t}) +
        (clockWeight (Transition L K s t).1 + clockWeight (Transition L K s t).2) := by
  unfold Protocol.stepOrSelf
  rw [if_pos happ]
  unfold rawPotential
  rw [Multiset.map_add, Multiset.sum_add]
  have hδ : (NonuniformMajority L K).δ s t = Transition L K s t := rfl
  rw [hδ]
  simp

theorem timerPotential_pair_drop (c : Cfg L K) (h : AllOne c)
    (s t : AgentState L K) (happ : Protocol.Applicable c s t) :
    2 * timerPotential (Protocol.stepOrSelf (NonuniformMajority L K) c s t) +
      clockWeight s + clockWeight t ≤ 2 * timerPotential c := by
  classical
  have hs : s ∈ c := Multiset.mem_of_le happ (by simp)
  have ht : t ∈ c := Multiset.mem_of_le happ (by simp)
  have hstep : Protocol.stepOrSelf (NonuniformMajority L K) c s t =
      c - {s, t} + {(Transition L K s t).1, (Transition L K s t).2} := by
    unfold Protocol.stepOrSelf
    rw [if_pos happ] <;> rfl
  by_cases hout : AllOne (Protocol.stepOrSelf (NonuniformMajority L K) c s t)
  · have hsout : (Transition L K s t).1.phase.val = 1 := by
      apply hout
      rw [hstep]
      simp
    have htout : (Transition L K s t).2.phase.val = 1 := by
      apply hout
      rw [hstep]
      simp
    have hpair := weight_pair_halving s t (h s hs) (h t ht) hsout htout
    simp only [timerPotential, if_pos h, if_pos hout]
    rw [rawPotential_step_split c s t happ, rawPotential_pair_split c s t happ]
    omega
  · simp only [timerPotential, if_pos h, if_neg hout, mul_zero, zero_add]
    rw [rawPotential_pair_split c s t happ]
    omega

theorem timerPotential_step_le (c : Cfg L K) (h : AllOne c)
    (s t : AgentState L K) :
    timerPotential (Protocol.stepOrSelf (NonuniformMajority L K) c s t) ≤
      timerPotential c := by
  classical
  by_cases happ : Protocol.Applicable c s t
  · have hdrop := timerPotential_pair_drop c h s t happ
    omega
  · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]

private theorem applicable_of_pos_interactionCount
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

private theorem interactionProb_zero_of_not_applicable
    (c : Cfg L K) (s t : AgentState L K) (h : ¬ Protocol.Applicable c s t) :
    c.interactionProb s t = 0 := by
  have hz : c.interactionCount s t = 0 := by
    apply Nat.eq_zero_of_not_pos
    intro hp
    exact h (applicable_of_pos_interactionCount c s t hp)
  simp [Config.interactionProb, hz]

theorem weighted_pair_drop (c : Cfg L K) (h : AllOne c)
    (s t : AgentState L K) :
    (((clockWeight s : ℝ≥0∞) + (clockWeight t : ℝ≥0∞)) / 2) *
        c.interactionProb s t ≤
      ((timerPotential c : ℝ≥0∞) -
        (timerPotential (Protocol.stepOrSelf (NonuniformMajority L K) c s t) : ℝ≥0∞)) *
          c.interactionProb s t := by
  classical
  by_cases happ : Protocol.Applicable c s t
  · have hpair := timerPotential_pair_drop c h s t happ
    have hm := timerPotential_step_le c h s t
    have hn : clockWeight s + clockWeight t ≤
        2 * (timerPotential c -
          timerPotential (Protocol.stepOrSelf (NonuniformMajority L K) c s t)) := by
      omega
    have he : ((clockWeight s : ℝ≥0∞) + (clockWeight t : ℝ≥0∞)) / 2 ≤
        (timerPotential c : ℝ≥0∞) -
          (timerPotential (Protocol.stepOrSelf (NonuniformMajority L K) c s t) : ℝ≥0∞) := by
      apply (ENNReal.div_le_iff' (by norm_num) (by norm_num)).2
      have hcast : ((clockWeight s + clockWeight t : ℕ) : ℝ≥0∞) ≤
          ((2 * (timerPotential c -
            timerPotential (Protocol.stepOrSelf (NonuniformMajority L K) c s t)) : ℕ) : ℝ≥0∞) :=
        by exact_mod_cast hn
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, ENNReal.natCast_sub] using hcast
    exact mul_le_mul_right' he _
  · simp only [interactionProb_zero_of_not_applicable c s t happ, mul_zero, le_refl]

theorem timer_weighted_drop (n : ℕ) (hn : 2 ≤ n) (c : Cfg L K)
    (hwin : PhaseOnlyWindows.Phase1Win n c) :
    (1 / (n : ℝ≥0∞)) * timerPotential c ≤
      WeightedDriftDropSum.weightedDropSum (NonuniformMajority L K) timerPotential c := by
  classical
  have hc : 2 ≤ c.card := by rw [hwin.1]; exact hn
  have hall : AllOne c := hwin.2
  let w : AgentState L K → ℝ≥0∞ := fun a => clockWeight a
  have hmass : Config.sumOf w c = (timerPotential c : ℝ≥0∞) := by
    rw [timerPotential, if_pos hall]
    exact rawPotential_cast c
  have hsum :
      (∑ p : AgentState L K × AgentState L K,
        ((w p.1 + w p.2) / 2) * c.interactionProb p.1 p.2) =
      (timerPotential c : ℝ≥0∞) / (n : ℝ≥0∞) := by
    calc
      (∑ p : AgentState L K × AgentState L K,
          ((w p.1 + w p.2) / 2) * c.interactionProb p.1 p.2) =
          (∑ p : AgentState L K × AgentState L K,
            (w p.1 + w p.2) * c.interactionProb p.1 p.2) / 2 := by
        simp only [div_eq_mul_inv, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro p _
        ring
      _ = (Config.sumOf w c / (c.card : ℝ≥0∞) +
          Config.sumOf w c / (c.card : ℝ≥0∞)) / 2 := by
        simp_rw [add_mul]
        rw [Finset.sum_add_distrib, Phase0Window.sum_fst_interactionProb c hc,
          Phase0Window.sum_snd_interactionProb c hc]
      _ = (timerPotential c : ℝ≥0∞) / (n : ℝ≥0∞) := by
        rw [hmass, hwin.1, ENNReal.add_div, ENNReal.add_halves]
  calc
    (1 / (n : ℝ≥0∞)) * timerPotential c =
        (timerPotential c : ℝ≥0∞) / (n : ℝ≥0∞) := by
      rw [div_eq_mul_inv, div_eq_mul_inv, one_mul, mul_comm]
    _ = ∑ p : AgentState L K × AgentState L K,
        ((w p.1 + w p.2) / 2) * c.interactionProb p.1 p.2 := hsum.symm
    _ ≤ WeightedDriftDropSum.weightedDropSum (NonuniformMajority L K) timerPotential c := by
      unfold WeightedDriftDropSum.weightedDropSum
      apply Finset.sum_le_sum
      intro p _
      exact weighted_pair_drop c hall p.1 p.2

theorem timerPotential_drift (n : ℕ) (hn : 2 ≤ n) (c : Cfg L K)
    (hwin : PhaseOnlyWindows.Phase1Win n c) :
    (∫⁻ c', (timerPotential c' : ℝ≥0∞)
      ∂(NonuniformMajority L K).transitionKernel c) ≤
        (1 - 1 / (n : ℝ≥0∞)) * timerPotential c := by
  have hc : 2 ≤ c.card := by rw [hwin.1]; exact hn
  have hnzero : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  exact WeightedDriftDropSum.weighted_dyadic_mass_drift_of_dropSum
    (NonuniformMajority L K) timerPotential c hc (1 / (n : ℝ≥0∞))
    (ENNReal.div_ne_top (by norm_num) hnzero)
    (fun p => timerPotential_step_le c hwin.2 p.1 p.2)
    (timer_weighted_drop n hn c hwin)


/-- Only an observed phase-one configuration and one actual Clock are needed. -/
def TimerEntry (n : ℕ) (c : Cfg L K) : Prop :=
  PhaseOnlyWindows.Phase1Win n c ∧ 1 ≤ RoleSplitConcentration.clockCount c

def LaterPhase (c : Cfg L K) : Prop := ∃ a ∈ c, 2 ≤ a.phase.val

theorem no_later_phase_window (init : Cfg L K) (ω : Ω L K)
    (n s N : ℕ) (he : TimerEntry n (trace init ω s))
    (hno : ¬ LaterPhase (trace init ω (s + N))) :
    (∀ u, s ≤ u → u ≤ s + N →
      PhaseOnlyWindows.Phase1Win n (trace init ω u)) ∧
      1 ≤ timerPotential (trace init ω (s + N)) := by
  classical
  have hlo := phase_lower_reachable 1 _ _
    (trace_reachable init ω (Nat.le_add_right s N))
    (fun a ha => (he.1.2 a ha).symm.le)
  have hend : AllOne (trace init ω (s + N)) := by
    intro a ha
    have hlt : a.phase.val < 2 := by
      by_contra h
      exact hno ⟨a, ha, by omega⟩
    have hge := hlo a ha
    omega
  have hwin : ∀ u, s ≤ u → u ≤ s + N →
      PhaseOnlyWindows.Phase1Win n (trace init ω u) := by
    intro u hsu hut
    refine ⟨(Protocol.reachable_card_eq (trace_reachable init ω hsu)).trans he.1.1, ?_⟩
    exact phase_eq_between init ω 1 s u (s + N) hsu hut he.1.2 hend
  refine ⟨hwin, ?_⟩
  have hcount : RoleSplitConcentration.clockCount (trace init ω (s + N)) =
      RoleSplitConcentration.clockCount (trace init ω s) := by
    exact PhaseOneDrainProducer.trace_eq_of_window init ω
      RoleSplitConcentration.clockCount (PhaseOnlyWindows.Phase1Win n)
      (fun c hc d => by
        simpa only [RoleSplitConcentration.clockCount] using
          role_count_applyDraw_phase_one .clock n c hc d)
      s (s + N) (Nat.le_add_right s N)
      (fun u hu hu' => hwin u hu hu'.le)
  rw [timerPotential, if_pos hend]
  calc
    1 ≤ RoleSplitConcentration.clockCount (trace init ω (s + N)) := by
      rw [hcount]
      exact he.2
    _ ≤ rawPotential (trace init ω (s + N)) :=
      clockCount_le_rawPotential _

/-- The full recorded prefix is retained in this local timer estimate. -/
theorem timer_tail_from (init : Cfg L K) (n : ℕ) (hn : 2 ≤ n)
    (s N : ℕ) (A : Set ((k : Finset.Iic s) → Draw L K))
    (hentry : ∀ p ∈ A, TimerEntry n (prefixCfg init s p)) :
    law init {ω | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A ∧
        ¬ LaterPhase (trace init ω (s + N))} ≤
      (1 - 1 / (n : ℝ≥0∞)) ^ N *
        ((n * 2 ^ (50 * (L + 1)) : ℕ) : ℝ≥0∞) *
          law init {ω | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A} := by
  have hΨ : ∀ p ∈ A,
      timerPotential (prefixCfg init s p) ≤ n * 2 ^ (50 * (L + 1)) := by
    intro p hp
    simpa only [(hentry p hp).1.1] using timerPotential_le_card (prefixCfg init s p)
  have htail := TraceDrain.potential_drift_tail_from init timerPotential
    (PhaseOnlyWindows.Phase1Win n) (1 / (n : ℝ≥0∞))
    (fun c hc => timerPotential_drift n hn c hc) s N A
    (n * 2 ^ (50 * (L + 1))) hΨ
  apply le_trans (measure_mono ?_) htail
  rintro ω ⟨hA, hno⟩
  have hw := no_later_phase_window init ω n s N (hentry _ hA) hno
  exact ⟨hA, fun u hu hu' => hw.1 u hu hu'.le, hw.2⟩

def timerHorizon (n : ℕ) : ℕ :=
  40 * n * PhaseThreeModel.Numeric.clockHours n

def timerBudget (n : ℕ) : ℝ≥0∞ :=
  (1 - 1 / (n : ℝ≥0∞)) ^ timerHorizon n *
    ((n * 2 ^ (50 * PhaseThreeModel.Numeric.clockHours n) : ℕ) : ℝ≥0∞)

/-- The sharper available logarithm bound preserves the literal 40nH deadline. -/
theorem timer_budget_real (n : ℕ) (hn : 2 ≤ n) :
    (1 - 1 / (n : ℝ)) ^ timerHorizon n * (n : ℝ) *
      (2 : ℝ) ^ (50 * PhaseThreeModel.Numeric.clockHours n) ≤
        1 / (n : ℝ) ^ 5 := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hbase : 0 ≤ 1 - 1 / (n : ℝ) := by
    have hdiv : 1 / (n : ℝ) ≤ 1 := (div_le_one hnpos).2 (by linarith)
    linarith
  have hdecay : (1 - 1 / (n : ℝ)) ^ timerHorizon n ≤
      Real.exp (-40 * (PhaseThreeModel.Numeric.clockHours n : ℝ)) := by
    calc
      (1 - 1 / (n : ℝ)) ^ timerHorizon n ≤
          (Real.exp (-(1 / (n : ℝ)))) ^ timerHorizon n :=
        pow_le_pow_left₀ hbase
          (by linarith [Real.add_one_le_exp (-(1 / (n : ℝ)))]) _
      _ = Real.exp (-40 * (PhaseThreeModel.Numeric.clockHours n : ℝ)) := by
        rw [← Real.exp_nat_mul]
        congr 1
        unfold timerHorizon
        push_cast
        field_simp [hnpos.ne']
        <;> ring
  have htwo : (2 : ℝ) ^ (50 * PhaseThreeModel.Numeric.clockHours n) =
      Real.exp (((50 * PhaseThreeModel.Numeric.clockHours n : ℕ) : ℝ) * Real.log 2) := by
    rw [← Real.log_pow, Real.exp_log (by positivity)]
  have hhour := clock_hour_log_lower n
  have hlog : 56 * Real.log 2 ≤ (40 : ℝ) := by
    linarith only [PhaseThreeModel.Numeric.log_two_bounds.2]
  have hscaled := mul_le_mul_of_nonneg_right hlog
    (Nat.cast_nonneg (PhaseThreeModel.Numeric.clockHours n) : (0 : ℝ) ≤ _)
  have hexponent :
      -40 * (PhaseThreeModel.Numeric.clockHours n : ℝ) + Real.log (n : ℝ) +
          ((50 * PhaseThreeModel.Numeric.clockHours n : ℕ) : ℝ) * Real.log 2 ≤
        -(5 : ℝ) * Real.log (n : ℝ) := by
    push_cast
    nlinarith only [hhour, hscaled]
  calc
    (1 - 1 / (n : ℝ)) ^ timerHorizon n * (n : ℝ) *
        (2 : ℝ) ^ (50 * PhaseThreeModel.Numeric.clockHours n) ≤
      Real.exp (-40 * (PhaseThreeModel.Numeric.clockHours n : ℝ)) * (n : ℝ) *
        (2 : ℝ) ^ (50 * PhaseThreeModel.Numeric.clockHours n) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hdecay hnpos.le) (by positivity)
    _ = Real.exp (-40 * (PhaseThreeModel.Numeric.clockHours n : ℝ)) *
        Real.exp (Real.log (n : ℝ)) *
        Real.exp (((50 * PhaseThreeModel.Numeric.clockHours n : ℕ) : ℝ) * Real.log 2) := by
      rw [Real.exp_log hnpos, ← htwo]
    _ = Real.exp
        (-40 * (PhaseThreeModel.Numeric.clockHours n : ℝ) + Real.log (n : ℝ) +
          ((50 * PhaseThreeModel.Numeric.clockHours n : ℕ) : ℝ) * Real.log 2) := by
      rw [← Real.exp_add, ← Real.exp_add]
    _ ≤ Real.exp (-(5 : ℝ) * Real.log (n : ℝ)) := Real.exp_le_exp.mpr hexponent
    _ = 1 / (n : ℝ) ^ 5 := by
      rw [show -(5 : ℝ) * Real.log (n : ℝ) =
          -((5 : ℝ) * Real.log (n : ℝ)) by ring, Real.exp_neg]
      rw [show (5 : ℝ) * Real.log (n : ℝ) = Real.log ((n : ℝ) ^ 5) by
          rw [Real.log_pow]; norm_num,
        Real.exp_log (by positivity), one_div]

theorem timerBudget_le (n : ℕ) (hn : 2 ≤ n) :
    timerBudget n ≤ 1 / (n : ℝ≥0∞) ^ 5 := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hbase : 0 ≤ 1 - 1 / (n : ℝ) := by
    have hdiv : 1 / (n : ℝ) ≤ 1 := (div_le_one hnpos).2 (by linarith)
    linarith
  have hrate : 1 - 1 / (n : ℝ≥0∞) = ENNReal.ofReal (1 - 1 / (n : ℝ)) := by
    rw [ENNReal.ofReal_sub _ (by positivity), ENNReal.ofReal_one,
      ENNReal.ofReal_div_of_pos hnpos, ENNReal.ofReal_one, ENNReal.ofReal_natCast]
  unfold timerBudget
  rw [hrate, ← ENNReal.ofReal_pow hbase,
    ← ENNReal.ofReal_natCast (n * 2 ^ (50 * PhaseThreeModel.Numeric.clockHours n)),
    ← ENNReal.ofReal_mul (pow_nonneg hbase _)]
  calc
    ENNReal.ofReal ((1 - 1 / (n : ℝ)) ^ timerHorizon n *
        ((n * 2 ^ (50 * PhaseThreeModel.Numeric.clockHours n) : ℕ) : ℝ)) ≤
      ENNReal.ofReal (1 / (n : ℝ) ^ 5) :=
        ENNReal.ofReal_le_ofReal (by
          simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, mul_assoc] using
            timer_budget_real n hn)
    _ = 1 / (n : ℝ≥0∞) ^ 5 := by
      rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_one,
        ENNReal.ofReal_pow (Nat.cast_nonneg n), ENNReal.ofReal_natCast]

/-- Failure is a joint event at a genuine observed start; the later clause is
the bad event being estimated, and is never part of the conditioning prefix. -/
def timerFailure {n : ℕ} (init : InputCfg n)
    (σ : InputLog n → WithTop ℕ) : Set (InputLog n) :=
  {ω | ∃ s : ℕ, σ ω = (s : WithTop ℕ) ∧
    TimerEntry n (trace init ω s) ∧
      ¬ LaterPhase (trace init ω (s + timerHorizon n))}

theorem timerFailure_measurable {n : ℕ} (init : InputCfg n)
    (σ : InputLog n → WithTop ℕ) (hσ : PairLogPastTime σ) :
    MeasurableSet (timerFailure init σ) := by
  have htime (s : ℕ) : MeasurableSet {ω | σ ω = (s : WithTop ℕ)} :=
    (pairLogFiltration _ _).le s _ (hσ s)
  have hentry (s : ℕ) : MeasurableSet {ω | TimerEntry n (trace init ω s)} :=
    (show MeasurableSet {c : InputCfg n | TimerEntry n c} from
      (Set.to_countable _).measurableSet).preimage
        ((measurable_pi_apply s).comp (measurable_trace init))
  have hbad (s : ℕ) : MeasurableSet
      {ω | ¬ LaterPhase (trace init ω (s + timerHorizon n))} :=
    (show MeasurableSet {c : InputCfg n | ¬ LaterPhase c} from
      (Set.to_countable _).measurableSet).preimage
        ((measurable_pi_apply (s + timerHorizon n)).comp (measurable_trace init))
  have heq : timerFailure init σ =
      ⋃ s : ℕ, {ω | σ ω = (s : WithTop ℕ)} ∩
        ({ω | TimerEntry n (trace init ω s)} ∩
          {ω | ¬ LaterPhase (trace init ω (s + timerHorizon n))}) := by
    ext ω
    simp only [timerFailure, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff]
  rw [heq]
  exact MeasurableSet.iUnion fun s => (htime s).inter ((hentry s).inter (hbad s))

/-- Actual protocol timer producer: no independent counter-tail assumption. -/
theorem phase_one_timer_conditional_producer {n : ℕ} (init : InputCfg n)
    (hn : 2 ≤ n) (σ : InputLog n → WithTop ℕ) (hσ : PairLogPastTime σ) :
    law init (timerFailure init σ) ≤ 1 / (n : ℝ≥0∞) ^ 5 := by
  refine (genuine_seed_splice (law init) σ (timerFailure init σ) (timerBudget n)
    (timerFailure_measurable init σ hσ)
    (fun s => (pairLogFiltration _ _).le s _ (hσ s))
    (fun ω hω => ?_) (fun s => ?_)).trans (timerBudget_le n hn)
  · obtain ⟨s, hs, -, -⟩ := hω
    rw [hs]
    exact WithTop.coe_ne_top
  · have hσs := hσ s
    rw [pairLogFiltration_eq_comap] at hσs
    obtain ⟨Aσ, -, hAσ⟩ := hσs
    let A : Set ((k : Finset.Iic s) → Draw (PhaseThreeModel.Numeric.hourIndex n) 256) :=
      {p | p ∈ Aσ ∧ TimerEntry n (prefixCfg init s p)}
    have hmemσ : ∀ ω,
        frestrictLe (π := fun _ : ℕ => Draw _ _) s ω ∈ Aσ ↔
          σ ω = (s : WithTop ℕ) := by
      intro ω
      change ω ∈ frestrictLe (π := fun _ : ℕ => Draw _ _) s ⁻¹' Aσ ↔
        ω ∈ {ω | σ ω = (s : WithTop ℕ)}
      rw [hAσ]
    have hcomp := timer_tail_from init n hn s (timerHorizon n) A
      (fun p hp => hp.2)
    change law init {ω | frestrictLe (π := fun _ : ℕ => Draw _ _) s ω ∈ A ∧
        ¬ LaterPhase (trace init ω (s + timerHorizon n))} ≤
      timerBudget n * law init {ω | frestrictLe (π := fun _ : ℕ => Draw _ _) s ω ∈ A}
      at hcomp
    calc
      law init (timerFailure init σ ∩ {ω | σ ω = (s : WithTop ℕ)}) ≤
        law init {ω | frestrictLe (π := fun _ : ℕ => Draw _ _) s ω ∈ A ∧
          ¬ LaterPhase (trace init ω (s + timerHorizon n))} := by
        apply measure_mono
        rintro ω ⟨⟨s', hs', he, hbad⟩, hs⟩
        have hss : s' = s := WithTop.coe_injective (hs'.symm.trans hs)
        subst hss
        exact ⟨⟨(hmemσ ω).2 hs, he⟩, hbad⟩
      _ ≤ timerBudget n *
          law init {ω | frestrictLe (π := fun _ : ℕ => Draw _ _) s ω ∈ A} := hcomp
      _ ≤ timerBudget n * law init {ω | σ ω = (s : WithTop ℕ)} :=
        mul_le_mul_left' (measure_mono fun ω hω => (hmemσ ω).1 hω.1) _

noncomputable def firstLater (init : Cfg L K) : Ω L K → WithTop ℕ :=
  TraceDrain.exitTime init LaterPhase

theorem firstLater_past (init : Cfg L K) : PairLogPastTime (firstLater init) :=
  exitTime_pairLogPastTime init LaterPhase

theorem firstLater_isStoppingTime (init : Cfg L K) :
    IsStoppingTime (pairLogFiltration L K) (firstLater init) :=
  TraceDrain.exitTime_isStoppingTime init LaterPhase

theorem firstLater_eq_iff {n : ℕ} (init : InputCfg n) (ω : InputLog n) (t : ℕ) :
    firstLater init ω = (t : WithTop ℕ) ↔
      StageEventSpec.firstHit (StageEventSpec.someGE (n := n) 2) (trace init ω) t :=
  exitTime_eq_iff_firstHit init LaterPhase ω t

theorem exists_firstLater_between (init : Cfg L K) (ω : Ω L K)
    (s N : ℕ) (hs : AllOne (trace init ω s))
    (hhit : LaterPhase (trace init ω (s + N))) :
    ∃ t : ℕ, firstLater init ω = (t : WithTop ℕ) ∧ s ≤ t ∧ t ≤ s + N := by
  classical
  have hex : ∃ t, LaterPhase (trace init ω t) := ⟨s + N, hhit⟩
  let t := Nat.find hex
  have hfirst : StageEventSpec.firstHit LaterPhase (trace init ω) t :=
    ⟨Nat.find_spec hex, fun u hu => Nat.find_min hex hu⟩
  have hst : s ≤ t := by
    by_contra hle
    have hupper := phase_upper_reachable 1 _ _
      (trace_reachable init ω (by omega : t ≤ s))
      (fun a ha => (hs a ha).le)
    obtain ⟨a, ha, hp⟩ := hfirst.1
    have hu := hupper a ha
    omega
  exact ⟨t, (exitTime_eq_iff_firstHit init LaterPhase ω t).2 hfirst,
    hst, Nat.find_min' hex hhit⟩

theorem exists_firstLater_of_not_failure {n : ℕ} (init : InputCfg n)
    (σ : InputLog n → WithTop ℕ) (ω : InputLog n) (s : ℕ)
    (hs : σ ω = (s : WithTop ℕ)) (he : TimerEntry n (trace init ω s))
    (hgood : ω ∉ timerFailure init σ) :
    ∃ t : ℕ, firstLater init ω = (t : WithTop ℕ) ∧
      s ≤ t ∧ t ≤ s + timerHorizon n := by
  classical
  have hhit : LaterPhase (trace init ω (s + timerHorizon n)) := by
    by_contra hno
    exact hgood ⟨s, hs, he, hno⟩
  exact exists_firstLater_between init ω s (timerHorizon n) he.1.2 hhit

theorem readyProfile_timerEntry {n : ℕ} {init c : InputCfg n}
    (hn : 1 ≤ n) (h : PhaseOneReadyProfile init c) : TimerEntry n c := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hclockpos : (0 : ℝ) < (RoleSplitConcentration.clockCount c : ℝ) :=
    (by positivity : (0 : ℝ) < (97 / 400 : ℝ) * (n : ℝ)).trans_le h.clock_lower
  have hclock : 0 < RoleSplitConcentration.clockCount c := by exact_mod_cast hclockpos
  exact ⟨⟨h.card_eq, h.all_one⟩, hclock⟩

theorem entryProfile_timerEntry {n : ℕ} (init : InputCfg n)
    (hinput : ThresholdEpidemic.GoodInput n init) (ω : InputLog n) (s : ℕ)
    (h : PhaseZeroEntry.PhaseOneEntryProfile init ω s) :
    TimerEntry n (trace init ω s) := by
  have hn : 40 ≤ n := (time_population_bounds hinput.1).2
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hclockpos : (0 : ℝ) < (RoleSplitConcentration.clockCount (trace init ω s) : ℝ) :=
    (by positivity : (0 : ℝ) < (97 / 400 : ℝ) * (n : ℝ)).trans_le h.clock_lower
  have hclock : 0 < RoleSplitConcentration.clockCount (trace init ω s) := by
    exact_mod_cast hclockpos
  refine ⟨⟨?_, h.all_one⟩, hclock⟩
  exact (Protocol.reachable_card_eq
    (PhaseZeroEntry.phase_zero_trace_reachable init ω s)).trans hinput.2.2

theorem DrainedPrefix.firstLater_exists {n : ℕ} {init : InputCfg n}
    {ω : InputLog n} {s t : ℕ} (h : DrainedPrefix init ω s t)
    (hinput : ThresholdEpidemic.GoodInput n init)
    (hgood : ω ∉ timerFailure init (firstDrained init)) :
    ∃ u : ℕ, firstLater init ω = (u : WithTop ℕ) ∧
      t ≤ u ∧ u ≤ t + timerHorizon n := by
  have hn : 40 ≤ n := (time_population_bounds hinput.1).2
  exact exists_firstLater_of_not_failure init (firstDrained init) ω t h.drain_eq
    (readyProfile_timerEntry (by omega) (h.ready_profile hinput)) hgood

end Ripple.PopulationProtocol.ExactMajority.PhaseOneTimer

end
