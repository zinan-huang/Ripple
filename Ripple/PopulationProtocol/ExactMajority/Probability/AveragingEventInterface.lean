import Ripple.PopulationProtocol.ExactMajority.Probability.StageEventSpec
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockProducer
import Ripple.PopulationProtocol.ExactMajority.Probability.MixedWindowClosure
import Mathlib.Tactic

/-!
# Exact event interfaces and deterministic terminal arithmetic for N13

This file does not assert the averaging producer. It identifies its exact clock
event, discharges the strong-gap readout, constructs the strict-small scale,
and records the terminal credit arithmetic. Its final measure inequality
explicitly retains the two missing estimates: safe sparse entry and local
averaging failure. Neither estimate is discharged by an event rewrite.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Ripple.PopulationProtocol.ExactMajority.AveragingEventInterface

open TimeTheorem PairLog StageEventSpec

variable {L K n : ℕ}

theorem clockBy_subset_entryBy {init : InputCfg n} (E : StageEvents n init) :
    clockBy E ⊆ entryBy E := by
  rintro ω ⟨S, T, ρ, hT, hentry, hclock⟩
  exact ⟨S, T, hT, hentry⟩

theorem averageBy_subset_clockBy {init : InputCfg n} (E : StageEvents n init) :
    averageBy E ⊆ clockBy E := by
  rintro ω ⟨S, T, ρ, hT, hentry, hclock, havg⟩
  exact ⟨S, T, ρ, hT, hentry, hclock⟩

/-- The literal complement of the N12 failure event. Outside entryBy,
this event holds without asserting that a clock history exists. -/
theorem clockSuccess_eq {init : InputCfg n} (E : StageEvents n init) :
    (phaseClockFailure E)ᶜ = (entryBy E)ᶜ ∪ clockBy E := by
  classical
  ext ω
  change ¬ (ω ∈ entryBy E ∧ ω ∉ clockBy E) ↔
    ω ∉ entryBy E ∨ ω ∈ clockBy E
  tauto

/-- On the entry event, clock success is exactly existence of the reviewed
clock history. This is the restriction needed before consuming clock fields. -/
theorem clockSuccess_on_entry {init : InputCfg n} (E : StageEvents n init) :
    entryBy E ∩ (phaseClockFailure E)ᶜ = clockBy E := by
  classical
  ext ω
  constructor
  · rintro ⟨hentry, hgood⟩
    by_contra hclock
    exact hgood ⟨hentry, hclock⟩
  · intro hclock
    exact ⟨clockBy_subset_entryBy E hclock, fun hbad => hbad.2 hclock⟩

theorem averagingFailure_eq {init : InputCfg n} (E : StageEvents n init) :
    phaseAveragingFailure E =
      (entryBy E ∩ (phaseClockFailure E)ᶜ) \ averageBy E := by
  rw [clockSuccess_on_entry]
  rfl

theorem clock_and_averaging_failures {init : InputCfg n} (E : StageEvents n init) :
    entryBy E \ averageBy E = phaseClockFailure E ∪ phaseAveragingFailure E := by
  classical
  ext ω
  constructor
  · rintro ⟨hentry, hnotavg⟩
    by_cases hclock : ω ∈ clockBy E
    · exact Or.inr ⟨hclock, hnotavg⟩
    · exact Or.inl ⟨hentry, hclock⟩
  · rintro (⟨hentry, hnotclock⟩ | ⟨hclock, hnotavg⟩)
    · exact ⟨hentry, fun havg => hnotclock (averageBy_subset_clockBy E havg)⟩
    · exact ⟨clockBy_subset_entryBy E hclock, hnotavg⟩

/-- Global phase monotonicity, lifted to every draw, including a null draw. -/
theorem phase_lower_applyDraw (c : Cfg L K) (o : Draw L K) (p : ℕ)
    (hphase : ∀ a ∈ c, p ≤ a.phase.val) :
    ∀ a ∈ applyDraw c o, p ≤ a.phase.val := by
  classical
  cases o with
  | none => exact hphase
  | some q =>
    change ∀ a ∈ Protocol.stepOrSelf (NonuniformMajority L K) c q.1.1 q.2.1,
      p ≤ a.phase.val
    by_cases happ : Protocol.Applicable c q.1.1 q.2.1
    · have hs := hphase q.1.1 (Multiset.mem_of_le happ (by simp))
      have ht := hphase q.2.1 (Multiset.mem_of_le happ (by simp))
      have houtleft : p ≤ (Transition L K q.1.1 q.2.1).1.phase.val :=
        hs.trans ((le_max_left _ _).trans (Transition_left_phase_ge_pair_max _ _))
      have houtright : p ≤ (Transition L K q.1.1 q.2.1).2.phase.val :=
        ht.trans ((le_max_right _ _).trans (Transition_right_phase_ge_pair_max _ _))
      have heq : Protocol.stepOrSelf (NonuniformMajority L K) c q.1.1 q.2.1 =
          c - {q.1.1, q.2.1} +
            {(Transition L K q.1.1 q.2.1).1, (Transition L K q.1.1 q.2.1).2} := by
        unfold Protocol.stepOrSelf
        rw [if_pos happ]
        rfl
      rw [heq]
      intro a ha
      rcases Multiset.mem_add.mp ha with ha | ha
      · exact hphase a (Multiset.mem_of_le (Multiset.sub_le_self _ _) ha)
      · have hcases : a = (Transition L K q.1.1 q.2.1).1 ∨
            a = (Transition L K q.1.1 q.2.1).2 := by
          simpa using ha
        rcases hcases with rfl | rfl
        · exact houtleft
        · exact houtright
    · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]
      exact hphase

/-- Canonicalize the decidability argument of a count without changing its
predicate. This bridges the classical counts in StageEventSpec and the
decidable role-equality counts in older transition lemmas. -/
theorem countP_classical {α : Type*} (P : α → Prop)
    [d : DecidablePred P] (c : Multiset α) :
    c.countP P =
      @Multiset.countP α P (fun a => Classical.propDecidable (P a)) c := by
  exact congrArg
    (fun inst : DecidablePred P => @Multiset.countP α P inst c)
    (Subsingleton.elim d (fun a => Classical.propDecidable (P a)))

/-- Exact clock-count preservation once every input phase is at least three. -/
theorem clockCount_applyDraw_of_allGE (c : InputCfg n)
    (o : Draw (PhaseThreeModel.Numeric.hourIndex n) 256)
    (hphase : allGE 3 c) :
    StageEventSpec.clockCount (applyDraw c o) = StageEventSpec.clockCount c := by
  classical
  cases o with
  | none => rfl
  | some q =>
    change StageEventSpec.clockCount
      (Protocol.stepOrSelf (NonuniformMajority _ 256) c q.1.1 q.2.1) = _
    by_cases happ : Protocol.Applicable c q.1.1 q.2.1
    · have hs := hphase q.1.1 (Multiset.mem_of_le happ (by simp))
      have ht := hphase q.2.1 (Multiset.mem_of_le happ (by simp))
      have heq : Protocol.stepOrSelf (NonuniformMajority _ 256) c q.1.1 q.2.1 =
          c - {q.1.1, q.2.1} +
            {(Transition _ 256 q.1.1 q.2.1).1, (Transition _ 256 q.1.1 q.2.1).2} := by
        unfold Protocol.stepOrSelf
        rw [if_pos happ]
        rfl
      have hpair : StageEventSpec.clockCount
          {(Transition _ 256 q.1.1 q.2.1).1, (Transition _ 256 q.1.1 q.2.1).2} =
          StageEventSpec.clockCount {q.1.1, q.2.1} := by
        unfold StageEventSpec.clockCount
        simpa only [countP_classical] using
          MixedWindowClosure.clockCount_pair_eq q.1.1 q.2.1 hs ht
      have hle : StageEventSpec.clockCount {q.1.1, q.2.1} ≤
          StageEventSpec.clockCount c := by
        unfold StageEventSpec.clockCount
        simpa only [countP_classical] using
          Multiset.countP_le_of_le (fun a => a.role = Role.clock) happ
      unfold StageEventSpec.clockCount at hpair hle ⊢
      rw [heq, Multiset.countP_add, Multiset.countP_sub happ, hpair]
      omega
    · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]

theorem clockHistory_seed_lt_exit {init : InputCfg n} {ω : InputLog n}
    {S T ρ : ℕ} {w : ClockTimes init}
    (h : ClockHistory init ω S T ρ w) : S ≤ T ∧ T < ρ := by
  have hcap : w.cap < ρ := lt_of_le_of_lt (Nat.le_add_right _ _) h.protected_settling
  exact ⟨h.entry.order, lt_of_le_of_lt h.all_before_cap hcap⟩

/-- The strong/equality branch has a deterministic readout at the first
Phase-4 seed. No averaging tail and no post-Phase-4 stable-output theorem is
used here. -/
theorem strong_readout_of_clockHistory {init : InputCfg n} {ω : InputLog n}
    {S T ρ : ℕ} {w : ClockTimes init} (hn : 0 < n)
    (h : ClockHistory init ω S T ρ w)
    (hgap : timeMainCount (trace init ω S) ≤ 40 * gapMagnitude init) :
    StrongReadout init (timeMainCount (trace init ω S)) (trace init ω ρ) := by
  classical
  have hST := clockHistory_seed_lt_exit h
  have hρ : 0 < ρ := by omega
  have hpred : ρ - 1 + 1 = ρ := by omega
  have hSpre : S ≤ ρ - 1 := by omega
  have hTpre : T ≤ ρ - 1 := by omega
  have hpre : ρ - 1 < ρ := by omega
  have hall : allGE 3 (trace init ω (ρ - 1)) := by
    intro a ha
    exact (h.all_three (ρ - 1) hTpre hpre a ha).ge
  have hstep : trace init ω ρ =
      applyDraw (trace init ω (ρ - 1)) (ω ρ) := by
    simpa only [hpred] using (TimeTheorem.trace_succ init ω (ρ - 1))
  have hphase : ∀ a ∈ trace init ω ρ, 3 ≤ a.phase.val := by
    rw [hstep]
    exact phase_lower_applyDraw (trace init ω (ρ - 1)) (ω ρ) 3 hall
  have hcount : StageEventSpec.clockCount (trace init ω ρ) =
      StageEventSpec.clockCount (trace init ω (ρ - 1)) := by
    rw [hstep]
    exact clockCount_applyDraw_of_allGE _ _ hall
  have hden := h.density (ρ - 1) hSpre hpre
  have hcpos : 0 < StageEventSpec.clockCount (trace init ω ρ) := by
    rw [hcount]
    omega
  have hclock : ∃ a ∈ trace init ω ρ, a.role = Role.clock := by
    simpa only [StageEventSpec.clockCount, Multiset.countP_pos] using hcpos
  have hmain := (h.density S le_rfl (lt_of_le_of_lt hST.1 hST.2)).1
  refine ⟨hgap, h.entry.mass_cap, ?_, hphase, h.first_exit.1, hclock, ?_⟩
  · simpa only [TimeTheorem.trace_zero] using
      (TimeTheorem.trace_reachable init ω (s := 0) (t := ρ) (Nat.zero_le ρ))
  · omega

theorem strong_averageReadout_of_clockHistory {init : InputCfg n}
    {ω : InputLog n} {S T ρ : ℕ} {w : ClockTimes init}
    (hn : 0 < n) (h : ClockHistory init ω S T ρ w)
    (hgap : timeMainCount (trace init ω S) ≤ 40 * gapMagnitude init) :
    averageReadout init (timeMainCount (trace init ω S)) (trace init ω ρ) :=
  Or.inr (Or.inr (strong_readout_of_clockHistory hn h hgap))

/-- A clock history witnessing an averaging failure cannot lie in the
deterministic strong/equality branch. This keeps that branch out of the
safe sparse-entry error charge. -/
theorem averagingFailure_small_gap {init : InputCfg n} {ω : InputLog n}
    {S T ρ : ℕ} {w : ClockTimes init} (hn : 0 < n)
    (hbad : ω ∈ phaseAveragingFailure (reviewedStageEvents n init))
    (hT : T ≤ earlyHorizon n)
    (hclock : ClockHistory init ω S T ρ w) :
    40 * gapMagnitude init < timeMainCount (trace init ω S) := by
  by_contra hgap
  have hM : timeMainCount (trace init ω S) ≤ 40 * gapMagnitude init := by
    omega
  have havg := strong_averageReadout_of_clockHistory hn hclock hM
  exact hbad.2 ⟨S, T, ρ, hT, hclock.entry, ⟨w, hclock⟩, havg⟩

theorem gap_above_main_count_excluded {init : InputCfg n} {ω : InputLog n}
    {S T ρ : ℕ} (h : reviewedClockGood init ω S T ρ) :
    ¬ timeMainCount (trace init ω S) < gapMagnitude init := by
  obtain ⟨w, hw⟩ := h
  exact not_lt_of_ge hw.entry.mass_cap

/-- Integer construction of the terminal scale. The upper bound on the
population is the only logarithmic fact needed here. -/
theorem small_gap_dominant_level_in_range {n M d L : ℕ}
    (hd : 0 < d) (hsmall : 40 * d < M)
    (hmain : 25 * M ≤ 13 * n) (hcap : n ≤ 2 ^ L) :
    ∃ ell : ℕ, 5 ≤ ell ∧ ell + 2 ≤ L ∧
      2 * M ≤ 5 * 2 ^ ell * d ∧ 5 * 2 ^ ell * d < 4 * M := by
  have hdunit : 1 ≤ d := hd
  have hpd : 2 ^ L ≤ 2 ^ L * d := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (2 ^ L) hdunit
  have hlarge : 2 * M ≤ 5 * 2 ^ L * d := by
    nlinarith
  have hex : ∃ ell : ℕ, 2 * M ≤ 5 * 2 ^ ell * d := ⟨L, hlarge⟩
  let ell := Nat.find hex
  have hlower : 2 * M ≤ 5 * 2 ^ ell * d := Nat.find_spec hex
  have hell : 5 ≤ ell := by
    by_contra h
    have hellsmall : ell ≤ 4 := by omega
    have hp : 2 ^ ell ≤ (16 : ℕ) := by
      simpa using Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) hellsmall
    have hmul := Nat.mul_le_mul_right d hp
    nlinarith
  have hprev : 5 * 2 ^ (ell - 1) * d < 2 * M :=
    Nat.lt_of_not_ge (Nat.find_min hex (by omega : ell - 1 < ell))
  have hupper : 5 * 2 ^ ell * d < 4 * M := by
    have heq : ell = (ell - 1) + 1 := by omega
    calc
      5 * 2 ^ ell * d = 2 * (5 * 2 ^ (ell - 1) * d) := by
        conv_lhs => rw [heq, pow_succ]
        ring
      _ < 4 * M := by omega
  have hrange : ell + 2 ≤ L := by
    by_contra h
    have hL : L ≤ ell + 1 := by omega
    have hp : 2 ^ L ≤ 2 * 2 ^ ell := by
      simpa only [pow_succ, Nat.mul_comm] using
        Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) hL
    have hmul : 2 ^ ell ≤ 2 ^ ell * d := by
      simpa only [Nat.mul_one] using Nat.mul_le_mul_left (2 ^ ell) hdunit
    have hpos : 0 < (2 : ℕ) ^ ell := by positivity
    nlinarith
  exact ⟨ell, hell, hrange, hlower, hupper⟩

/-- Specialize the scale construction to the counts of an actual reviewed
clock history. -/
theorem small_gap_scale_of_clockHistory {init : InputCfg n} {ω : InputLog n}
    {S T ρ : ℕ} {w : ClockTimes init} (h : ClockHistory init ω S T ρ w)
    (hd : 0 < gapMagnitude init)
    (hsmall : 40 * gapMagnitude init < timeMainCount (trace init ω S)) :
    ∃ ell : ℕ, 5 ≤ ell ∧ ell + 2 ≤ PhaseThreeModel.Numeric.hourIndex n ∧
      2 * timeMainCount (trace init ω S) ≤ 5 * 2 ^ ell * gapMagnitude init ∧
      5 * 2 ^ ell * gapMagnitude init < 4 * timeMainCount (trace init ω S) := by
  have hST := clockHistory_seed_lt_exit h
  apply small_gap_dominant_level_in_range hd hsmall
  · exact (h.density S le_rfl (lt_of_le_of_lt hST.1 hST.2)).2.1
  · simpa only [PhaseThreeModel.Numeric.hourIndex] using
      (Nat.le_pow_clog (by norm_num : 1 < (2 : ℕ)) n)

/-- Numerical part of the permanent two-level majority-partner floor.
The mass decomposition itself remains a separate configuration lemma. -/
theorem terminal_majority_partner_floor {M U A : ℚ} (hM : 0 < M)
    (hmass : (199 / 500 : ℚ) * M ≤ A)
    (hcapacity : A ≤ U + (M - U) / 4) :
    (19 / 100 : ℚ) * M < U := by
  linarith

/-- The debt-ledger and count decomposition imply the produced credit margin. -/
theorem protected_credit_margin {M P Y E A : ℚ}
    (hdecomp : M - P ≤ Y + E + A)
    (hY : Y ≤ (7 / 200 : ℚ) * M)
    (hE : E ≤ (3 / 1250 : ℚ) * M)
    (hA : A ≤ (1 / 1000 : ℚ) * M) :
    (601 / 625 : ℚ) * M ≤ P := by
  linarith

/-- A protected credit yields the persistent .9232 M band. This is stronger
than the .92 M readout. -/
theorem majority_band_of_protected_credit {M P F D Q : ℚ}
    (hD : 0 ≤ D) (hcredit : P = F - D)
    (hcapacity : F ≤ Q + (M - Q) / 2)
    (hmargin : (601 / 625 : ℚ) * M ≤ P) :
    (577 / 625 : ℚ) * M ≤ Q := by
  linarith

theorem majority_band_readout_of_protected_credit {M P F D Q : ℚ}
    (hM : 0 ≤ M) (hD : 0 ≤ D) (hcredit : P = F - D)
    (hcapacity : F ≤ Q + (M - Q) / 2)
    (hmargin : (601 / 625 : ℚ) * M ≤ P) :
    92 * M ≤ 100 * Q := by
  have hband := majority_band_of_protected_credit hD hcredit hcapacity hmargin
  linarith

/-- Split the actual averaging bad event at a candidate safe sparse-entry
event G. Both terms remain restricted to averaging failure, so the deterministic
strong branch need not be charged as an entry error. This supplies neither
of the two required probability estimates. -/
theorem averaging_failure_split (init : InputCfg n) (G : Set (InputLog n)) :
    law init (phaseAveragingFailure (reviewedStageEvents n init)) ≤
      law init (phaseAveragingFailure (reviewedStageEvents n init) \ G) +
        law init (phaseAveragingFailure (reviewedStageEvents n init) ∩ G) := by
  classical
  calc
    law init (phaseAveragingFailure (reviewedStageEvents n init)) ≤
        law init ((phaseAveragingFailure (reviewedStageEvents n init) \ G) ∪
          (phaseAveragingFailure (reviewedStageEvents n init) ∩ G)) := by
      apply measure_mono
      intro ω hω
      by_cases hG : ω ∈ G
      · exact Or.inr ⟨hω, hG⟩
      · exact Or.inl ⟨hω, hG⟩
    _ ≤ law init (phaseAveragingFailure (reviewedStageEvents n init) \ G) +
        law init (phaseAveragingFailure (reviewedStageEvents n init) ∩ G) :=
      measure_union_le _ _

/-- The arithmetic budget after the two actual probability estimates have
been supplied. The N12 charge is absent because the bad event is already
restricted to clockBy. -/
theorem averaging_error_budget {x : ℝ} (hx : 2 ≤ x) :
    2 / x ^ 2 + 2 / x ^ 4 ≤ 3 / x ^ 2 := by
  have hxpos : 0 < x := by linarith
  have hdrop : 2 / x ^ 4 ≤ 1 / x ^ 2 := by
    rw [div_le_div_iff₀ (pow_pos hxpos 4) (pow_pos hxpos 2)]
    have hbase : (2 : ℝ) ≤ x ^ 2 := by nlinarith
    calc
      2 * x ^ 2 ≤ x ^ 2 * x ^ 2 :=
        mul_le_mul_of_nonneg_right hbase (sq_nonneg x)
      _ = 1 * x ^ 4 := by ring
  calc
    2 / x ^ 2 + 2 / x ^ 4 ≤ 2 / x ^ 2 + 1 / x ^ 2 :=
      add_le_add le_rfl hdrop
    _ = 3 / x ^ 2 := by ring

/-- The same two-term budget in the codomain of the original-law measure. -/
theorem averaging_error_budget_ennreal {n : ℕ} (hn : 2 ≤ n) :
    ENNReal.ofReal (2 / (n : ℝ) ^ 2) +
        ENNReal.ofReal (2 / (n : ℝ) ^ 4) ≤
      ENNReal.ofReal (3 / (n : ℝ) ^ 2) := by
  calc
    ENNReal.ofReal (2 / (n : ℝ) ^ 2) +
        ENNReal.ofReal (2 / (n : ℝ) ^ 4) =
        ENNReal.ofReal (2 / (n : ℝ) ^ 2 + 2 / (n : ℝ) ^ 4) := by
          rw [ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ ENNReal.ofReal (3 / (n : ℝ) ^ 2) :=
      ENNReal.ofReal_le_ofReal
        (averaging_error_budget (by exact_mod_cast hn))

end Ripple.PopulationProtocol.ExactMajority.AveragingEventInterface

end
