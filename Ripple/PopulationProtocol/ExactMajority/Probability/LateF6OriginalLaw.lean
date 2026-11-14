-- Ripple/PopulationProtocol/ExactMajority/Probability/LateF6OriginalLaw.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.LateF6Acceptance
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseOneDrainStopping

/-!
# F6 freezing and sample locking on the original pair-log law

The start and first threshold hits below are genuine stopping times.  The
localization is a finite observed prefix: all agents have reached Phase 3,
the first threshold-4 hit has occurred, and no Phase-6 state has yet appeared.
There is no conditioning on timer survival, completion, or a future class size.

The zero tail is deterministic.  In particular, the proof applies to the
guarded reconstruction of every pair log, including logs of measure zero.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal

namespace Ripple.PopulationProtocol.ExactMajority.LateF6OriginalLaw

open TimeTheorem PairLog PhaseOneDrain PhaseOneDrainStopping
open LateF6Acceptance

variable {L K : ℕ}

private theorem label_mem_trace (init : Cfg L K) (ω : Ω L K)
    (u : ℕ) (i : Fin init.card) :
    labelsAt init ω u i ∈ trace init ω u := by
  rw [← labelsAt_config init ω u]
  exact Multiset.mem_map.mpr ⟨i, by simp, rfl⟩

/-- Lift any two-output relation through the actual guarded label update.
The unselected-label case is part of the statement. -/
private theorem stepLabels_relation {m : ℕ}
    (f : Fin m → AgentState L K) (d : Draw L K)
    (R : AgentState L K → AgentState L K → Prop)
    (hself : ∀ i, R (f i) (f i))
    (hpair : ∀ i j,
      R (f i) (Transition L K (f i) (f j)).1 ∧
      R (f j) (Transition L K (f i) (f j)).2)
    (x : Fin m) :
    R (f x) (stepLabels f d x) := by
  classical
  cases hsel : selectLabels f d with
  | none =>
      simpa only [stepLabels, hsel] using hself x
  | some pair =>
      rcases pair with ⟨i, j⟩
      have hij := selectLabels_distinct f d i j hsel
      simp only [stepLabels, hsel]
      by_cases hxi : x = i
      · subst x
        simpa [updateLabels, NonuniformMajority, hij] using (hpair i j).1
      · by_cases hxj : x = j
        · subst x
          simpa [updateLabels, NonuniformMajority] using (hpair i j).2
        · simpa [updateLabels, hxi, hxj] using hself x

/-- The exact per-label statements needed by the asynchronous sampling
construction.  The phase hypothesis on a locked sample is explicit. -/
structure LabelStep (before after : AgentState L K) : Prop where
  role_eq : after.role = before.role
  phase_le : before.phase.val ≤ after.phase.val
  main_freeze : before.role = .main → 4 ≤ after.phase.val →
    after.bias = before.bias
  sample_lock : before.role = .reserve → before.phase.val = 5 →
    before.hour.val ≠ L →
    after.role = .reserve ∧ after.phase.val = 5 ∧ after.hour = before.hour

private theorem labelStep_self (a : AgentState L K) : LabelStep a a :=
  ⟨rfl, le_rfl, fun _ _ => rfl, fun hr hp _ => ⟨hr, hp, rfl⟩⟩

private theorem labelStep_pair (s t : AgentState L K)
    (hs : Window s) (ht : Window t) :
    LabelStep s (Transition L K s t).1 ∧
      LabelStep t (Transition L K s t).2 := by
  have hr := transition_roles s t hs ht
  have hp : s.phase.val ≤ (Transition L K s t).1.phase.val ∧
      t.phase.val ≤ (Transition L K s t).2.phase.val :=
    Transition_phase_monotone (L := L) (K := K) s t
  exact
    ⟨⟨hr.1, hp.1, transition_main_freeze_left s t hs ht,
        transition_locked_left s t hs ht⟩,
      ⟨hr.2, hp.2, transition_main_freeze_right s t hs ht,
        transition_locked_right s t hs ht⟩⟩

theorem labelStep_at (init : Cfg L K) (ω : Ω L K) (u : ℕ)
    (hwin : ∀ a ∈ trace init ω u, Window a) (i : Fin init.card) :
    LabelStep (labelsAt init ω u i) (labelsAt init ω (u + 1) i) := by
  rw [labelsAt_succ]
  exact stepLabels_relation (labelsAt init ω u) (ω (u + 1)) LabelStep
    (fun j => labelStep_self _)
    (fun j k => labelStep_pair _ _
      (hwin _ (label_mem_trace init ω u j))
      (hwin _ (label_mem_trace init ω u k))) i

private theorem canonical_step (init : Cfg L K) (ω : Ω L K) (u : ℕ)
    (hwin : ∀ a ∈ trace init ω u, Window a)
    (hcanonical : ∀ i : Fin init.card,
      Eligible (labelsAt init ω u i) →
        4 ≤ (labelsAt init ω u i).phase.val →
          (labelsAt init ω u i).phase.val = 5) :
    ∀ i : Fin init.card,
      Eligible (labelsAt init ω (u + 1) i) →
        4 ≤ (labelsAt init ω (u + 1) i).phase.val →
          (labelsAt init ω (u + 1) i).phase.val = 5 := by
  intro i
  rw [labelsAt_succ]
  apply stepLabels_relation (labelsAt init ω u) (ω (u + 1))
    (fun _ b => Eligible b → 4 ≤ b.phase.val → b.phase.val = 5)
    hcanonical
  intro j k
  exact
    ⟨transition_frozen_eligible_left _ _
        (hwin _ (label_mem_trace init ω u j))
        (hwin _ (label_mem_trace init ω u k)),
      transition_frozen_eligible_right _ _
        (hwin _ (label_mem_trace init ω u j))
        (hwin _ (label_mem_trace init ω u k))⟩

/-- The two actual acceptance rectangles, with the already-active Reserve
and the newly activated Reserve kept separate. -/
def SamplingRectangle (r m : AgentState L K) : Prop :=
  r.role = .reserve ∧
    ((r.phase.val = 5 ∧ r.hour.val = L ∧ Eligible m) ∨
      (r.phase.val < 5 ∧ m.phase.val = 5 ∧ Eligible m))

/-- The equivalent pool form used by the frozen-prefix urn argument. -/
def FrozenSamplingRectangle (r m : AgentState L K) : Prop :=
  r.role = .reserve ∧
    ((r.phase.val = 5 ∧ r.hour.val = L ∧ Eligible m) ∨
      (r.phase.val < 5 ∧ 4 ≤ m.phase.val ∧ Eligible m))

theorem samplingRectangle_iff_frozen (r m : AgentState L K)
    (hcanonical : Eligible m → 4 ≤ m.phase.val → m.phase.val = 5) :
    SamplingRectangle r m ↔ FrozenSamplingRectangle r m := by
  constructor
  · rintro ⟨hr, hactive | hnew⟩
    · exact ⟨hr, Or.inl hactive⟩
    · have hp := hnew.2.1
      exact ⟨hr, Or.inr ⟨hnew.1, by omega, hnew.2.2⟩⟩
  · rintro ⟨hr, hactive | hnew⟩
    · exact ⟨hr, Or.inl hactive⟩
    · exact ⟨hr, Or.inr ⟨hnew.1,
        hcanonical hnew.2.2 hnew.2.1, hnew.2.2⟩⟩

theorem selected_acceptance_left (init : Cfg L K) (ω : Ω L K) (u : ℕ)
    (hwin : ∀ a ∈ trace init ω u, Window a)
    (i j : Fin init.card)
    (hsel : drawLabels init ω (u + 1) = some (i, j)) :
    Accepted (labelsAt init ω u i) (labelsAt init ω (u + 1) i) ↔
      SamplingRectangle (labelsAt init ω u i) (labelsAt init ω u j) := by
  have hpair := labelsAt_selected_transition init ω u i j hsel
  rw [hpair.2.1]
  exact transition_accept_left _ _
    (hwin _ (label_mem_trace init ω u i))
    (hwin _ (label_mem_trace init ω u j))

theorem selected_acceptance_right (init : Cfg L K) (ω : Ω L K) (u : ℕ)
    (hwin : ∀ a ∈ trace init ω u, Window a)
    (i j : Fin init.card)
    (hsel : drawLabels init ω (u + 1) = some (i, j)) :
    Accepted (labelsAt init ω u j) (labelsAt init ω (u + 1) j) ↔
      SamplingRectangle (labelsAt init ω u j) (labelsAt init ω u i) := by
  have hpair := labelsAt_selected_transition init ω u i j hsel
  rw [hpair.2.2.1]
  exact transition_accept_right _ _
    (hwin _ (label_mem_trace init ω u i))
    (hwin _ (label_mem_trace init ω u j))

/-- The accepted stored index is the actual partner's index, not merely some
visible index.  This is the receipt needed for class-count trials. -/
theorem selected_sample_index_left (init : Cfg L K) (ω : Ω L K) (u : ℕ)
    (hwin : ∀ a ∈ trace init ω u, Window a)
    (i j : Fin init.card)
    (hsel : drawLabels init ω (u + 1) = some (i, j))
    (hacc : Accepted (labelsAt init ω u i) (labelsAt init ω (u + 1) i)) :
    (labelsAt init ω (u + 1) i).hour =
      exponentOf L (labelsAt init ω u j).bias := by
  have hpair := labelsAt_selected_transition init ω u i j hsel
  rw [hpair.2.1] at hacc ⊢
  exact transition_accepted_index_left _ _
    (hwin _ (label_mem_trace init ω u i))
    (hwin _ (label_mem_trace init ω u j)) hacc

theorem selected_sample_index_right (init : Cfg L K) (ω : Ω L K) (u : ℕ)
    (hwin : ∀ a ∈ trace init ω u, Window a)
    (i j : Fin init.card)
    (hsel : drawLabels init ω (u + 1) = some (i, j))
    (hacc : Accepted (labelsAt init ω u j) (labelsAt init ω (u + 1) j)) :
    (labelsAt init ω (u + 1) j).hour =
      exponentOf L (labelsAt init ω u i).bias := by
  have hpair := labelsAt_selected_transition init ω u i j hsel
  rw [hpair.2.2.1] at hacc ⊢
  exact transition_accepted_index_right _ _
    (hwin _ (label_mem_trace init ω u i))
    (hwin _ (label_mem_trace init ω u j)) hacc

theorem selected_ineligible_left (init : Cfg L K) (ω : Ω L K) (u : ℕ)
    (hwin : ∀ a ∈ trace init ω u, Window a)
    (i j : Fin init.card)
    (hsel : drawLabels init ω (u + 1) = some (i, j))
    (hineligible : ¬ Eligible (labelsAt init ω u j)) :
    ¬ Accepted (labelsAt init ω u i) (labelsAt init ω (u + 1) i) := by
  intro hacc
  have hr := (selected_acceptance_left init ω u hwin i j hsel).mp hacc
  rcases hr.2 with hactive | hnew
  · exact hineligible hactive.2.2
  · exact hineligible hnew.2.2

theorem selected_ineligible_right (init : Cfg L K) (ω : Ω L K) (u : ℕ)
    (hwin : ∀ a ∈ trace init ω u, Window a)
    (i j : Fin init.card)
    (hsel : drawLabels init ω (u + 1) = some (i, j))
    (hineligible : ¬ Eligible (labelsAt init ω u i)) :
    ¬ Accepted (labelsAt init ω u j) (labelsAt init ω (u + 1) j) := by
  intro hacc
  have hr := (selected_acceptance_right init ω u hwin i j hsel).mp hacc
  rcases hr.2 with hactive | hnew
  · exact hineligible hactive.2.2
  · exact hineligible hnew.2.2

variable {n : ℕ}

/-- First homogeneous threshold-3 hit.  Its exact Phase-3 profile is recorded
separately in `Prefix`; no homogeneous state is substituted retrospectively. -/
def allThreeStart (init : InputCfg n) : InputLog n → WithTop ℕ :=
  TraceDrain.exitTime init (StageEventSpec.allGE (n := n) 3)

/-- Genuine first threshold-4 hit. -/
def firstFourStart (init : InputCfg n) : InputLog n → WithTop ℕ :=
  TraceDrain.exitTime init (StageEventSpec.someGE (n := n) 4)

/-- Genuine first threshold-6 hit, used as the sample-locking barrier. -/
def firstSixStart (init : InputCfg n) : InputLog n → WithTop ℕ :=
  TraceDrain.exitTime init (StageEventSpec.someGE (n := n) 6)

theorem allThreeStart_isStoppingTime (init : InputCfg n) :
    IsStoppingTime (pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256)
      (allThreeStart init) :=
  TraceDrain.exitTime_isStoppingTime init (StageEventSpec.allGE (n := n) 3)

theorem firstFourStart_isStoppingTime (init : InputCfg n) :
    IsStoppingTime (pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256)
      (firstFourStart init) :=
  TraceDrain.exitTime_isStoppingTime init (StageEventSpec.someGE (n := n) 4)

theorem firstSixStart_isStoppingTime (init : InputCfg n) :
    IsStoppingTime (pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256)
      (firstSixStart init) :=
  TraceDrain.exitTime_isStoppingTime init (StageEventSpec.someGE (n := n) 6)

theorem allThreeStart_past (init : InputCfg n) :
    PairLogPastTime (allThreeStart init) :=
  exitTime_pairLogPastTime init (StageEventSpec.allGE (n := n) 3)

theorem firstFourStart_past (init : InputCfg n) :
    PairLogPastTime (firstFourStart init) :=
  exitTime_pairLogPastTime init (StageEventSpec.someGE (n := n) 4)

theorem firstSixStart_past (init : InputCfg n) :
    PairLogPastTime (firstSixStart init) :=
  exitTime_pairLogPastTime init (StageEventSpec.someGE (n := n) 6)

/-- An observed finite prefix.  Its upper phase bound is checked only through
the current endpoint `t`. -/
structure Prefix (init : InputCfg n) (ω : InputLog n) (a s t : ℕ) : Prop where
  all_start : allThreeStart init ω = (a : WithTop ℕ)
  four_start : firstFourStart init ω = (s : WithTop ℕ)
  start_order : a ≤ s
  observed : s ≤ t
  all_three : ∀ b ∈ trace init ω a, b.phase.val = 3
  before_six : ∀ u, a ≤ u → u ≤ t →
    ∀ b ∈ trace init ω u, b.phase.val ≤ 5

theorem prefix_measurable (init : InputCfg n) (a s t : ℕ) :
    MeasurableSet[pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256 t]
      {ω | Prefix init ω a s t} := by
  by_cases has : a ≤ s
  · by_cases hst : s ≤ t
    · have hat : a ≤ t := has.trans hst
      have ha :
          MeasurableSet[pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256 t]
            {ω | allThreeStart init ω = (a : WithTop ℕ)} :=
        ((pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256).mono hat)
          _ (allThreeStart_past init a)
      have hs :
          MeasurableSet[pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256 t]
            {ω | firstFourStart init ω = (s : WithTop ℕ)} :=
        ((pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256).mono hst)
          _ (firstFourStart_past init s)
      have hthree :
          MeasurableSet[pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256 t]
            {ω | ∀ b ∈ trace init ω a, b.phase.val = 3} :=
        (show MeasurableSet {c : InputCfg n | ∀ b ∈ c, b.phase.val = 3}
          from (Set.to_countable _).measurableSet).preimage
            (measurable_trace_at_of_le init hat)
      have hpiece (u : ℕ) :
          MeasurableSet[pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256 t]
            {ω | a ≤ u → u ≤ t →
              ∀ b ∈ trace init ω u, b.phase.val ≤ 5} := by
        by_cases hau : a ≤ u
        · by_cases hut : u ≤ t
          · simpa only [hau, hut, true_implies] using
              (show MeasurableSet {c : InputCfg n | ∀ b ∈ c, b.phase.val ≤ 5}
                from (Set.to_countable _).measurableSet).preimage
                  (measurable_trace_at_of_le init hut)
          · simp only [hau, true_implies, hut, false_implies, Set.setOf_true]
            exact MeasurableSet.univ
        · simp only [hau, false_implies, Set.setOf_true]
          exact MeasurableSet.univ
      have hupper :
          MeasurableSet[pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256 t]
            {ω | ∀ u, a ≤ u → u ≤ t →
              ∀ b ∈ trace init ω u, b.phase.val ≤ 5} := by
        have heq :
            {ω : InputLog n | ∀ u, a ≤ u → u ≤ t →
              ∀ b ∈ trace init ω u, b.phase.val ≤ 5} =
              ⋂ u : ℕ, {ω | a ≤ u → u ≤ t →
                ∀ b ∈ trace init ω u, b.phase.val ≤ 5} := by
          ext ω
          simp only [Set.mem_setOf_eq, Set.mem_iInter]
        rw [heq]
        exact MeasurableSet.iInter hpiece
      have heq :
          {ω | Prefix init ω a s t} =
            {ω | allThreeStart init ω = (a : WithTop ℕ)} ∩
            ({ω | firstFourStart init ω = (s : WithTop ℕ)} ∩
            ({ω | ∀ b ∈ trace init ω a, b.phase.val = 3} ∩
             {ω | ∀ u, a ≤ u → u ≤ t →
               ∀ b ∈ trace init ω u, b.phase.val ≤ 5})) := by
        ext ω
        constructor
        · intro h
          exact ⟨h.all_start, h.four_start, h.all_three, h.before_six⟩
        · rintro ⟨hfirst, hfour, hthree, hupper⟩
          exact ⟨hfirst, hfour, has, hst, hthree, hupper⟩
      rw [heq]
      exact ha.inter (hs.inter (hthree.inter hupper))
    · have heq : {ω | Prefix init ω a s t} = ∅ := by
        ext ω
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        exact fun h => hst h.observed
      rw [heq]
      exact MeasurableSpace.measurableSet_empty _
  · have heq : {ω | Prefix init ω a s t} = ∅ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      exact fun h => has h.start_order
    rw [heq]
    exact MeasurableSpace.measurableSet_empty _

theorem Prefix.window {init : InputCfg n} {ω : InputLog n} {a s t : ℕ}
    (h : Prefix init ω a s t) (u : ℕ) (hau : a ≤ u) (hut : u ≤ t) :
    ∀ b ∈ trace init ω u, Window b := by
  have hlo := phase_lower_reachable 3 _ _ (trace_reachable init ω hau)
    (fun b hb => (h.all_three b hb).ge)
  intro b hb
  exact ⟨hlo b hb, h.before_six u hau hut b hb⟩

theorem Prefix.step {init : InputCfg n} {ω : InputLog n} {a s t : ℕ}
    (h : Prefix init ω a s t) (u : ℕ) (hau : a ≤ u) (hut : u < t)
    (i : Fin init.card) :
    LabelStep (labelsAt init ω u i) (labelsAt init ω (u + 1) i) :=
  labelStep_at init ω u (h.window u hau hut.le) i

theorem Prefix.role_between {init : InputCfg n} {ω : InputLog n} {a s t : ℕ}
    (h : Prefix init ω a s t) (u v : ℕ)
    (hau : a ≤ u) (huv : u ≤ v) (hvt : v ≤ t) (i : Fin init.card) :
    (labelsAt init ω v i).role = (labelsAt init ω u i).role := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le huv
  clear huv
  revert hvt
  induction k with
  | zero =>
      intro _
      rfl
  | succ k ih =>
      intro hvt
      have hs := h.step (u + k) (by omega) (by omega) i
      exact hs.role_eq.trans (ih (by omega))

theorem Prefix.frozen_between {init : InputCfg n} {ω : InputLog n} {a s t : ℕ}
    (h : Prefix init ω a s t) (u v : ℕ)
    (hau : a ≤ u) (huv : u ≤ v) (hvt : v ≤ t) (i : Fin init.card)
    (hm : (labelsAt init ω u i).role = .main)
    (hf : 4 ≤ (labelsAt init ω u i).phase.val) :
    (labelsAt init ω v i).role = .main ∧
      4 ≤ (labelsAt init ω v i).phase.val ∧
      (labelsAt init ω v i).bias = (labelsAt init ω u i).bias := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le huv
  clear huv
  revert hvt
  induction k with
  | zero =>
      intro _
      exact ⟨hm, hf, rfl⟩
  | succ k ih =>
      intro hvt
      have hi := ih (by omega)
      have hs := h.step (u + k) (by omega) (by omega) i
      have hfnext := hi.2.1.trans hs.phase_le
      exact ⟨hs.role_eq.trans hi.1, hfnext,
        (hs.main_freeze hi.1 hfnext).trans hi.2.2⟩

theorem Prefix.locked_between {init : InputCfg n} {ω : InputLog n} {a s t : ℕ}
    (h : Prefix init ω a s t) (u v : ℕ)
    (hau : a ≤ u) (huv : u ≤ v) (hvt : v ≤ t) (i : Fin init.card)
    (hr : (labelsAt init ω u i).role = .reserve)
    (hp : (labelsAt init ω u i).phase.val = 5)
    (hh : (labelsAt init ω u i).hour.val ≠ PhaseThreeModel.Numeric.hourIndex n) :
    (labelsAt init ω v i).role = .reserve ∧
      (labelsAt init ω v i).phase.val = 5 ∧
      (labelsAt init ω v i).hour = (labelsAt init ω u i).hour := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le huv
  clear huv
  revert hvt
  induction k with
  | zero =>
      intro _
      exact ⟨hr, hp, rfl⟩
  | succ k ih =>
      intro hvt
      have hi := ih (by omega)
      have hs := h.step (u + k) (by omega) (by omega) i
      have hne : (labelsAt init ω (u + k) i).hour.val ≠
          PhaseThreeModel.Numeric.hourIndex n := by
        rw [hi.2.2]
        exact hh
      have hn := hs.sample_lock hi.1 hi.2.1 hne
      exact ⟨hn.1, hn.2.1, hn.2.2.trans hi.2.2⟩

theorem Prefix.canonical {init : InputCfg n} {ω : InputLog n} {a s t : ℕ}
    (h : Prefix init ω a s t) (u : ℕ) (hau : a ≤ u) (hut : u ≤ t) :
    ∀ i : Fin init.card, Eligible (labelsAt init ω u i) →
      4 ≤ (labelsAt init ω u i).phase.val →
        (labelsAt init ω u i).phase.val = 5 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hau
  clear hau
  revert hut
  induction k with
  | zero =>
      intro _ i _ hf
      have hp := h.all_three _ (label_mem_trace init ω a i)
      change 4 ≤ (labelsAt init ω a i).phase.val at hf
      omega
  | succ k ih =>
      intro hut
      exact canonical_step init ω (a + k)
        (h.window (a + k) (by omega) (by omega))
        (ih (by omega))

theorem Prefix.accepted_frozen_left
    {init : InputCfg n} {ω : InputLog n} {a s t : ℕ}
    (h : Prefix init ω a s t) (u : ℕ) (hau : a ≤ u) (hut : u < t)
    (i j : Fin init.card)
    (hsel : drawLabels init ω (u + 1) = some (i, j)) :
    Accepted (labelsAt init ω u i) (labelsAt init ω (u + 1) i) ↔
      FrozenSamplingRectangle (labelsAt init ω u i) (labelsAt init ω u j) :=
  (selected_acceptance_left init ω u (h.window u hau hut.le) i j hsel).trans
    (samplingRectangle_iff_frozen _ _ (h.canonical u hau hut.le j))

theorem Prefix.accepted_frozen_right
    {init : InputCfg n} {ω : InputLog n} {a s t : ℕ}
    (h : Prefix init ω a s t) (u : ℕ) (hau : a ≤ u) (hut : u < t)
    (i j : Fin init.card)
    (hsel : drawLabels init ω (u + 1) = some (i, j)) :
    Accepted (labelsAt init ω u j) (labelsAt init ω (u + 1) j) ↔
      FrozenSamplingRectangle (labelsAt init ω u j) (labelsAt init ω u i) :=
  (selected_acceptance_right init ω u (h.window u hau hut.le) i j hsel).trans
    (samplingRectangle_iff_frozen _ _ (h.canonical u hau hut.le i))

theorem Prefix.class_at_freeze {init : InputCfg n} {ω : InputLog n} {a s t : ℕ}
    (h : Prefix init ω a s t) (u : ℕ) (hau : a ≤ u) (hut : u < t)
    (i : Fin init.card) (σ : Sign)
    (j : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (hf : 4 ≤ (labelsAt init ω (u + 1) i).phase.val) :
    Phase5Convergence.biasedMainClass σ j (labelsAt init ω (u + 1) i) ↔
      Phase5Convergence.biasedMainClass σ j (labelsAt init ω u i) := by
  have hs := h.step u hau hut i
  unfold Phase5Convergence.biasedMainClass
  rw [hs.role_eq]
  by_cases hm : (labelsAt init ω u i).role = .main
  · rw [hs.main_freeze hm hf]
  · simp only [hm, false_and]

theorem Prefix.frozen_class {init : InputCfg n} {ω : InputLog n} {a s t : ℕ}
    (h : Prefix init ω a s t) (u v : ℕ)
    (hau : a ≤ u) (huv : u ≤ v) (hvt : v ≤ t)
    (i : Fin init.card) (σ : Sign)
    (j : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (hf : 4 ≤ (labelsAt init ω u i).phase.val) :
    Phase5Convergence.biasedMainClass σ j (labelsAt init ω v i) ↔
      Phase5Convergence.biasedMainClass σ j (labelsAt init ω u i) := by
  have hr := h.role_between u v hau huv hvt i
  unfold Phase5Convergence.biasedMainClass
  rw [hr]
  by_cases hm : (labelsAt init ω u i).role = .main
  · rw [(h.frozen_between u v hau huv hvt i hm hf).2.2]
  · simp only [hm, false_and]

/-- Consumer-facing path contract.  The class equivalence at the freezing
step is separate from preservation after freezing, as required by the review. -/
structure Contract (init : InputCfg n) (ω : InputLog n) (a t : ℕ) : Prop where
  roles_fixed : ∀ u, a ≤ u → u ≤ t → ∀ i : Fin init.card,
    (labelsAt init ω u i).role = (labelsAt init ω a i).role
  class_at_freeze : ∀ u, a ≤ u → u < t → ∀ i : Fin init.card,
    ∀ σ : Sign, ∀ j : Fin (PhaseThreeModel.Numeric.hourIndex n + 1),
    4 ≤ (labelsAt init ω (u + 1) i).phase.val →
    (Phase5Convergence.biasedMainClass σ j (labelsAt init ω (u + 1) i) ↔
      Phase5Convergence.biasedMainClass σ j (labelsAt init ω u i))
  class_after_freeze : ∀ u v, a ≤ u → u ≤ v → v ≤ t →
    ∀ i : Fin init.card, ∀ σ : Sign,
    ∀ j : Fin (PhaseThreeModel.Numeric.hourIndex n + 1),
    4 ≤ (labelsAt init ω u i).phase.val →
    (Phase5Convergence.biasedMainClass σ j (labelsAt init ω v i) ↔
      Phase5Convergence.biasedMainClass σ j (labelsAt init ω u i))
  samples_locked : ∀ u v, a ≤ u → u ≤ v → v ≤ t → ∀ i : Fin init.card,
    (labelsAt init ω u i).role = .reserve →
    (labelsAt init ω u i).phase.val = 5 →
    (labelsAt init ω u i).hour.val ≠ PhaseThreeModel.Numeric.hourIndex n →
    (labelsAt init ω v i).role = .reserve ∧
      (labelsAt init ω v i).phase.val = 5 ∧
      (labelsAt init ω v i).hour = (labelsAt init ω u i).hour
  eligible_frozen : ∀ u, a ≤ u → u ≤ t → ∀ i : Fin init.card,
    Eligible (labelsAt init ω u i) →
    (4 ≤ (labelsAt init ω u i).phase.val ↔
      (labelsAt init ω u i).phase.val = 5)
  acceptance_left : ∀ u, a ≤ u → u < t → ∀ i j : Fin init.card,
    drawLabels init ω (u + 1) = some (i, j) →
    (Accepted (labelsAt init ω u i) (labelsAt init ω (u + 1) i) ↔
      SamplingRectangle (labelsAt init ω u i) (labelsAt init ω u j))
  acceptance_right : ∀ u, a ≤ u → u < t → ∀ i j : Fin init.card,
    drawLabels init ω (u + 1) = some (i, j) →
    (Accepted (labelsAt init ω u j) (labelsAt init ω (u + 1) j) ↔
      SamplingRectangle (labelsAt init ω u j) (labelsAt init ω u i))
  sample_index_left : ∀ u, a ≤ u → u < t → ∀ i j : Fin init.card,
    drawLabels init ω (u + 1) = some (i, j) →
    Accepted (labelsAt init ω u i) (labelsAt init ω (u + 1) i) →
    (labelsAt init ω (u + 1) i).hour =
      exponentOf (PhaseThreeModel.Numeric.hourIndex n) (labelsAt init ω u j).bias
  sample_index_right : ∀ u, a ≤ u → u < t → ∀ i j : Fin init.card,
    drawLabels init ω (u + 1) = some (i, j) →
    Accepted (labelsAt init ω u j) (labelsAt init ω (u + 1) j) →
    (labelsAt init ω (u + 1) j).hour =
      exponentOf (PhaseThreeModel.Numeric.hourIndex n) (labelsAt init ω u i).bias

theorem Prefix.contract {init : InputCfg n} {ω : InputLog n} {a s t : ℕ}
    (h : Prefix init ω a s t) : Contract init ω a t := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u hau hut i
    exact h.role_between a u le_rfl hau hut i
  · exact h.class_at_freeze
  · exact h.frozen_class
  · exact h.locked_between
  · intro u hau hut i he
    constructor
    · exact h.canonical u hau hut i he
    · intro hp
      omega

  · intro u hau hut i j hsel
    exact selected_acceptance_left init ω u (h.window u hau hut.le) i j hsel
  · intro u hau hut i j hsel
    exact selected_acceptance_right init ω u (h.window u hau hut.le) i j hsel
  · intro u hau hut i j hsel hacc
    exact selected_sample_index_left init ω u (h.window u hau hut.le) i j hsel hacc
  · intro u hau hut i j hsel hacc
    exact selected_sample_index_right init ω u (h.window u hau hut.le) i j hsel hacc

/-- Row one has a zero original-law error at every observed prefix event.
The additional event `B` can be any past event; no conditional measure occurs. -/
theorem law_prefix_failure_zero (init : InputCfg n) (a s t : ℕ)
    (B : Set (InputLog n)) :
    law init {ω | ω ∈ B ∧ Prefix init ω a s t ∧ ¬ Contract init ω a t} = 0 := by
  have heq :
      {ω | ω ∈ B ∧ Prefix init ω a s t ∧ ¬ Contract init ω a t} = ∅ := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨_, hp, hnot⟩
    exact hnot hp.contract
  rw [heq, measure_empty]

/-- The same zero tail simultaneously covers every finite realized stopping
fibre and every later observed endpoint before the Phase-6 barrier. -/
theorem law_stopping_failure_zero (init : InputCfg n) :
    law init {ω | ∃ a s t : ℕ, Prefix init ω a s t ∧
      ¬ Contract init ω a t} = 0 := by
  have heq :
      {ω | ∃ a s t : ℕ, Prefix init ω a s t ∧ ¬ Contract init ω a t} = ∅ := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨a, s, t, hp, hnot⟩
    exact hnot hp.contract
  rw [heq, measure_empty]

theorem firstFourStart_eq_of_firstPhaseSeed (init : InputCfg n)
    (ω : InputLog n) (s : ℕ) (h : firstPhaseSeed init 4 s ω) :
    firstFourStart init ω = (s : WithTop ℕ) := by
  apply (exitTime_eq_iff_firstHit init (StageEventSpec.someGE (n := n) 4) ω s).2
  constructor
  · rcases h.1 with ⟨b, hb, hp⟩
    exact ⟨b, hb, hp.ge⟩
  · intro u hu hsome
    rcases hsome with ⟨b, hb, hp⟩
    have hlt := h.2 u hu b hb
    omega

/-- The canonical clock history supplies the actual starting witnesses.
Only the currently observed pre-6 prefix is added. -/
theorem prefix_of_clockHistory (init : InputCfg n) (ω : InputLog n)
    (S a s t : ℕ) (w : StageEventSpec.ClockTimes init)
    (hc : StageEventSpec.ClockHistory init ω S a s w)
    (hst : s ≤ t)
    (hupper : ∀ u, a ≤ u → u ≤ t →
      ∀ b ∈ trace init ω u, b.phase.val ≤ 5) :
    Prefix init ω a s t := by
  have has : a ≤ s := by
    have ha := hc.all_before_cap
    have hs := hc.protected_settling
    omega
  exact
    ⟨(exitTime_eq_iff_firstHit init (StageEventSpec.allGE (n := n) 3) ω a).2
        hc.entry.all_first,
      firstFourStart_eq_of_firstPhaseSeed init ω s hc.first_exit,
      has, hst, hc.entry.advanced_profile.all_three, hupper⟩

theorem prefix_of_clockHistory_before_firstSix (init : InputCfg n)
    (ω : InputLog n) (S a s t : ℕ) (w : StageEventSpec.ClockTimes init)
    (hc : StageEventSpec.ClockHistory init ω S a s w) (hst : s ≤ t)
    (hbarrier : (t : WithTop ℕ) < firstSixStart init ω) :
    Prefix init ω a s t := by
  apply prefix_of_clockHistory init ω S a s t w hc hst
  have hnot := TraceDrain.not_of_lt_exitTime init
    (StageEventSpec.someGE (n := n) 6) ω t hbarrier
  intro u _ hut b hb
  have hlt : b.phase.val < 6 := by
    by_contra h
    exact hnot u hut ⟨b, hb, by omega⟩
  omega

/-- The roles in the late contract are also the original seed roles.  In
particular, original Main counts need not be redefined at the frozen snapshot. -/
theorem role_eq_original_seed (init : InputCfg n) (ω : InputLog n)
    (S a s t : ℕ) (w : StageEventSpec.ClockTimes init)
    (hc : StageEventSpec.ClockHistory init ω S a s w)
    (hp : Prefix init ω a s t)
    (u : ℕ) (hau : a ≤ u) (hut : u ≤ t) (i : Fin init.card) :
    (labelsAt init ω u i).role = (labelsAt init ω S i).role := by
  have has : a < s := by
    have ha := hc.all_before_cap
    have hs := hc.protected_settling
    omega
  exact (hp.role_between a u le_rfl hau hut i).trans
    (hc.roles_fixed a hc.entry.order has i)

end Ripple.PopulationProtocol.ExactMajority.LateF6OriginalLaw

end
