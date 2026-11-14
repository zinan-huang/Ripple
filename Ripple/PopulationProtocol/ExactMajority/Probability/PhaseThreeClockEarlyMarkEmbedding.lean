-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockEarlyMarkEmbedding.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockEarlyMarks
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockActivationSeed

/-!
# The natural marks stay in their actual virtual upper front

The proof uses the gated max-copy/drip update, including contacts with an
inactive Clock. No all-Phase-3 premise is imposed. A finite current phase
cap supplies the no-backup guard; on genuine seed prefixes the carrier,
phase lower bound, and fixed physical Clock mask are discharged explicitly.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal BigOperators MeasureTheory ProbabilityTheory

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockEarlyMarkEmbedding

open TimeTheorem PairLog PairLogAuxiliary PhaseThreeClockVirtual
  PhaseThreeClockGatedLaw PhaseThreeClockGatedLevelOne PhaseThreeClockEmbedding
  PhaseThreeClockEmbeddingBridge PhaseThreeClockEarlyMarks
  PhaseThreeClockActivationLaw PhaseThreeClockActivationSeed PhaseThreeClockSeedTails

variable {L K m : ℕ}

theorem phase_three_of_effMinute_pos (a : AgentState L K)
    (hcap : a.phase.val ≤ 3) (hp : 0 < effMinute a) :
    a.phase.val = 3 := by
  by_cases ha : 3 ≤ a.phase.val
  · omega
  · have hz : effMinute a = 0 := by simp [effMinute, ha]
    omega

theorem clock_pair_outputs_above (s t : AgentState L K) (hK : 0 < K)
    (hs : ClockRegime s) (ht : ClockRegime t) (r : ℕ) (hr : 1 ≤ r)
    (hsource : r ≤ effMinute s ∨ r ≤ effMinute t) :
    ((virtualRule s t).1.role = .clock ∧ r ≤ effMinute (virtualRule s t).1) ∧
      ((virtualRule s t).2.role = .clock ∧ r ≤ effMinute (virtualRule s t).2) := by
  have hact : s.phase.val = 3 ∨ t.phase.val = 3 := by
    rcases hsource with hs' | ht'
    · exact Or.inl (phase_three_of_effMinute_pos s hs.phase_le (by omega))
    · exact Or.inr (phase_three_of_effMinute_pos t ht.phase_le (by omega))
  obtain ⟨har, hbr, ha, hb, ham, hbm⟩ :=
    virtualRule_clock_pair_some_active s t hK hs ht hact
  have hmax : r ≤ max (effMinute s) (effMinute t) := by
    rcases hsource with hs' | ht'
    · exact hs'.trans (le_max_left _ _)
    · exact ht'.trans (le_max_right _ _)
  have hleft : max (effMinute s) (effMinute t) ≤ (virtualRule s t).1.minute.val := by
    rw [ham]
    by_cases hne : effMinute s ≠ effMinute t
    · simpa only [if_pos hne] using (le_refl (max (effMinute s) (effMinute t)))
    · rw [if_neg hne]
      have heq : effMinute s = effMinute t := not_ne_iff.mp hne
      rw [heq, max_self]
      split_ifs <;> omega
  have hright : max (effMinute s) (effMinute t) ≤ (virtualRule s t).2.minute.val := by
    rw [hbm]
    by_cases hne : effMinute s ≠ effMinute t
    · rw [if_pos hne]
    · rw [if_neg hne]
      have heq : effMinute s = effMinute t := not_ne_iff.mp hne
      rw [heq, max_self]
  exact ⟨⟨har, by simpa [effMinute, ha] using hmax.trans hleft⟩,
    ⟨hbr, by simpa [effMinute, hb] using hmax.trans hright⟩⟩

theorem ruleUpdate_above_subset (f : Fin m → AgentState L K)
    (hK : 0 < K) (henv : ClockEnvironment f) (i j : Fin m) (hij : i ≠ j)
    (hpost : ∀ k, (ruleUpdate virtualRule f i j k).phase.val ≤ 3)
    (r : ℕ) (hr : 1 ≤ r) :
    aboveSet f r ⊆ aboveSet (ruleUpdate virtualRule f i j) r := by
  have hl : (virtualRule (f i) (f j)).1.phase.val ≤ 3 := by
    simpa only [ruleUpdate, Function.update_of_ne hij, Function.update_self] using hpost i
  have hjout : (virtualRule (f i) (f j)).2.phase.val ≤ 3 := by
    simpa only [ruleUpdate, Function.update_self] using hpost j
  have hnb := virtualRule_no_backup_of_phase_le_three (f i) (f j) hl hjout
  intro k hk
  simp only [aboveSet, Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
  by_cases hkj : k = j
  · subst k
    by_cases hi : (f i).role = .clock
    · have h := (clock_pair_outputs_above (f i) (f j) hK
        (henv.clock_regime i hi) (henv.clock_regime j hk.1) r hr (Or.inr hk.2)).2
      simpa only [ruleUpdate, Function.update_self] using h
    · have h := virtualRule_nonclock_clock (f i) (f j) (henv.clock_regime j hk.1)
        hi (henv.phase_range i).1 (henv.phase_range i).2 hnb
      have hout : (virtualRule (f i) (f j)).2.role = .clock ∧
          r ≤ effMinute (virtualRule (f i) (f j)).2 := ⟨h.1, h.2.1.symm ▸ hk.2⟩
      simpa only [ruleUpdate, Function.update_self] using hout
  · by_cases hki : k = i
    · subst k
      by_cases hj : (f j).role = .clock
      · have h := (clock_pair_outputs_above (f i) (f j) hK
          (henv.clock_regime i hk.1) (henv.clock_regime j hj) r hr (Or.inl hk.2)).1
        simpa only [ruleUpdate, Function.update_of_ne hij, Function.update_self] using h
      · have h := virtualRule_clock_nonclock (f i) (f j) (henv.clock_regime i hk.1)
          hj (henv.phase_range j).1 (henv.phase_range j).2 hnb
        have hout : (virtualRule (f i) (f j)).1.role = .clock ∧
            r ≤ effMinute (virtualRule (f i) (f j)).1 := ⟨h.1, h.2.1.symm ▸ hk.2⟩
        simpa only [ruleUpdate, Function.update_of_ne hij, Function.update_self] using hout
    · simpa only [ruleUpdate, Function.update_of_ne hkj, Function.update_of_ne hki] using hk

theorem earlyDrip_initiator_above (f : Fin m → AgentState L K)
    (hK : 0 < K) (henv : ClockEnvironment f) (ℓ cutoff : ℕ) (hℓ : 1 ≤ ℓ)
    (i j : Fin m) (hij : i ≠ j) (he : EarlyDrip (clockSet f) f ℓ cutoff i j) :
    i ∈ aboveSet (ruleUpdate virtualRule f i j) (ℓ + 1) := by
  have hi : (f i).role = .clock ∧ effMinute (f i) = ℓ := by
    simpa only [sourceSet, clockSet, Finset.mem_filter, Finset.mem_univ, true_and] using he.2.2.1
  have hj : (f j).role = .clock ∧ effMinute (f j) = ℓ := by
    simpa only [sourceSet, clockSet, Finset.mem_filter, Finset.mem_univ, true_and] using he.2.2.2
  have ha : (f i).phase.val = 3 :=
    phase_three_of_effMinute_pos _ (henv.phase_range i).2 (by omega)
  obtain ⟨har, -, hp, -, hm, -⟩ := virtualRule_clock_pair_some_active (f i) (f j) hK
    (henv.clock_regime i hi.1) (henv.clock_regime j hj.1) (Or.inl ha)
  have hminute : (virtualRule (f i) (f j)).1.minute.val = ℓ + 1 := by
    simpa [hi.2, hj.2, he.2.1] using hm
  simp only [aboveSet, Finset.mem_filter, Finset.mem_univ, true_and,
    ruleUpdate, Function.update_of_ne hij, Function.update_self]
  exact ⟨har, by simp [effMinute, hp, hminute]⟩

theorem markUpdate_subset_above (C M : Finset (Fin m)) (f : Fin m → AgentState L K)
    (hK : 0 < K) (henv : ClockEnvironment f) (hmask : C = clockSet f)
    (ℓ cutoff : ℕ) (hℓ : 1 ≤ ℓ)
    (hM : M ⊆ aboveSet f (ℓ + 1)) (i j : Fin m) (hij : i ≠ j)
    (hpost : ∀ k, (ruleUpdate virtualRule f i j k).phase.val ≤ 3) :
    markUpdate C f ℓ cutoff M i j ⊆ aboveSet (ruleUpdate virtualRule f i j) (ℓ + 1) := by
  classical
  subst C
  have hold := hM.trans (ruleUpdate_above_subset f hK henv i j hij hpost (ℓ + 1) (by omega))
  by_cases he : EarlyDrip (clockSet f) f ℓ cutoff i j
  · rw [markUpdate, if_pos he]
    exact Finset.insert_subset_iff.mpr ⟨earlyDrip_initiator_above f hK henv ℓ cutoff hℓ i j hij he, hold⟩
  · rw [markUpdate, if_neg he]
    by_cases hp : Propagation (clockSet f) M i j
    · rw [if_pos hp]
      have hclock : (f i).role = .clock ∧ (f j).role = .clock := by
        rcases hp with ⟨hi, hj⟩ | ⟨hi, hj⟩
        · have hi' : (f i).role = .clock ∧ ℓ + 1 ≤ effMinute (f i) := by
            simpa only [aboveSet, Finset.mem_filter, Finset.mem_univ, true_and] using hM hi
          have hj' : (f j).role = .clock := by
            simpa only [clockSet, Finset.mem_filter, Finset.mem_univ, true_and] using
              (Finset.mem_sdiff.mp hj).1
          exact ⟨hi'.1, hj'⟩
        · have hi' : (f i).role = .clock := by
            simpa only [clockSet, Finset.mem_filter, Finset.mem_univ, true_and] using
              (Finset.mem_sdiff.mp hi).1
          have hj' : (f j).role = .clock ∧ ℓ + 1 ≤ effMinute (f j) := by
            simpa only [aboveSet, Finset.mem_filter, Finset.mem_univ, true_and] using hM hj
          exact ⟨hi', hj'.1⟩
      have hsource : ℓ + 1 ≤ effMinute (f i) ∨ ℓ + 1 ≤ effMinute (f j) := by
        rcases hp with ⟨hi, -⟩ | ⟨-, hj⟩
        · have hi' := hM hi
          simp only [aboveSet, Finset.mem_filter, Finset.mem_univ, true_and] at hi'
          exact Or.inl hi'.2
        · have hj' := hM hj
          simp only [aboveSet, Finset.mem_filter, Finset.mem_univ, true_and] at hj'
          exact Or.inr hj'.2
      have hout := clock_pair_outputs_above (f i) (f j) hK
        (henv.clock_regime i hclock.1) (henv.clock_regime j hclock.2) (ℓ + 1) (by omega) hsource
      have hiout : i ∈ aboveSet (ruleUpdate virtualRule f i j) (ℓ + 1) := by
        simpa only [aboveSet, Finset.mem_filter, Finset.mem_univ, true_and,
          ruleUpdate, Function.update_of_ne hij, Function.update_self] using hout.1
      have hjout : j ∈ aboveSet (ruleUpdate virtualRule f i j) (ℓ + 1) := by
        simpa only [aboveSet, Finset.mem_filter, Finset.mem_univ, true_and,
          ruleUpdate, Function.update_self] using hout.2
      exact Finset.insert_subset_iff.mpr ⟨hiout, Finset.insert_subset_iff.mpr ⟨hjout, hold⟩⟩
    · rw [if_neg hp]
      exact hold


theorem markedAt_step_subset_above (init : Cfg L K) (hK : 0 < K)
    (C : Finset (Fin init.card)) (ℓ cutoff s t : ℕ) (ω : Ω L K)
    (hst : s ≤ t) (hℓ : 1 ≤ ℓ)
    (henv : ClockEnvironment (virtualLabels init ω t))
    (hmask : C = clockSet (virtualLabels init ω t))
    (hM : markedAt init C ℓ cutoff s ω t ⊆ aboveSet (virtualLabels init ω t) (ℓ + 1))
    (hpost : ∀ k, (virtualLabels init ω (t + 1) k).phase.val ≤ 3) :
    markedAt init C ℓ cutoff s ω (t + 1) ⊆
      aboveSet (virtualLabels init ω (t + 1)) (ℓ + 1) := by
  rw [markedAt_succ, if_pos hst]
  cases hd : drawLabels init ω (t + 1) with
  | none =>
      rw [virtualLabels_succ, hd]
      exact hM
  | some ij =>
      rcases ij with ⟨i, j⟩
      have hij := (labelsAt_selected_transition init ω t i j hd).1
      have hc : ∀ k, (ruleUpdate virtualRule (virtualLabels init ω t) i j k).phase.val ≤ 3 := by
        intro k
        simpa only [virtualLabels_succ, hd, auxStep] using hpost k
      rw [virtualLabels_succ, hd]
      exact markUpdate_subset_above C _ _ hK henv hmask ℓ cutoff hℓ hM i j hij hc

variable {n : ℕ}

/-- On an observed seed prefix, an endpoint phase cap discharges every
finite-window guard needed to keep the natural marks in the upper front. -/
theorem markedAt_subset_above_of_seedPrefix (init : InputCfg n) (ω : InputLog n)
    (C : Finset (Fin init.card)) (ℓ cutoff s u : ℕ)
    (hseed : ω ∈ seedPrefix init s) (hsu : s ≤ u) (hℓ : 1 ≤ ℓ)
    (hmask : C = clockSet (labelsAt init ω s))
    (hcap : ∀ i, (virtualLabels init ω u i).phase.val ≤ 3) :
    markedAt init C ℓ cutoff s ω u ⊆ aboveSet (virtualLabels init ω u) (ℓ + 1) := by
  have henv (t : ℕ) (hst : s ≤ t) (htu : t ≤ u) :
      ClockEnvironment (virtualLabels init ω t) := by
    refine ⟨?_, virtual_carrier_from_seedPrefix init ω s hseed t hst⟩
    intro i
    exact ⟨virtual_phase_floor_from_seedPrefix init ω s t hseed hst i,
      (virtualLabels_phase_mono init ω i htu).trans (hcap i)⟩
  have hall : ∀ t, s ≤ t → t ≤ u →
      markedAt init C ℓ cutoff s ω t ⊆ aboveSet (virtualLabels init ω t) (ℓ + 1) := by
    intro t hst
    induction t, hst using Nat.le_induction with
    | base =>
        intro _
        rw [markedAt_empty_before_seed init C ℓ cutoff s ω s le_rfl]
        exact Finset.empty_subset _
    | succ t hst ih =>
        intro htu
        have hcur := henv t hst (by omega)
        have hnext := henv (t + 1) (by omega) htu
        have hmaskt : C = clockSet (virtualLabels init ω t) :=
          hmask.trans (virtual_clockSet_eq_seed_of_current_phase_cap init ω s t hseed hst
            (fun i => (hcur.phase_range i).2)).symm
        exact markedAt_step_subset_above init (by decide) C ℓ cutoff s t ω hst hℓ
          hcur hmaskt (ih (by omega)) (fun i => (hnext.phase_range i).2)
  exact hall u hsu le_rfl

theorem markedAt_card_le_front_of_seedPrefix (init : InputCfg n) (ω : InputLog n)
    (C : Finset (Fin init.card)) (ℓ cutoff s u : ℕ)
    (hseed : ω ∈ seedPrefix init s) (hsu : s ≤ u) (hℓ : 1 ≤ ℓ)
    (hmask : C = clockSet (labelsAt init ω s))
    (hcap : ∀ i, (virtualLabels init ω u i).phase.val ≤ 3) :
    (markedAt init C ℓ cutoff s ω u).card ≤ frontCount (virtualLabels init ω u) (ℓ + 1) :=
  Finset.card_le_card
    (markedAt_subset_above_of_seedPrefix init ω C ℓ cutoff s u hseed hsu hℓ hmask hcap)

theorem markedAt_card_le_active_of_seedPrefix (init : InputCfg n) (ω : InputLog n)
    (C : Finset (Fin init.card)) (ℓ cutoff s u : ℕ)
    (hseed : ω ∈ seedPrefix init s) (hsu : s ≤ u) (hℓ : 1 ≤ ℓ)
    (hmask : C = clockSet (labelsAt init ω s))
    (hcap : ∀ i, (virtualLabels init ω u i).phase.val ≤ 3) :
    (markedAt init C ℓ cutoff s ω u).card ≤
      PhaseThreeClockActivationLaw.activeCount (virtualLabels init ω u) := by
  apply Finset.card_le_card
  intro i hi
  have hup := markedAt_subset_above_of_seedPrefix init ω C ℓ cutoff s u
    hseed hsu hℓ hmask hcap hi
  simp only [aboveSet, Finset.mem_filter, Finset.mem_univ, true_and] at hup
  have hp : 0 < effMinute (virtualLabels init ω u i) := by omega
  have hthree := phase_three_of_effMinute_pos _ (hcap i) hp
  simp only [activeSet, Finset.mem_filter, Finset.mem_univ, true_and]
  exact hthree.ge


theorem markedAt_source_disjoint_of_seedPrefix (init : InputCfg n) (ω : InputLog n)
    (C : Finset (Fin init.card)) (ℓ cutoff s t : ℕ)
    (hseed : ω ∈ seedPrefix init s) (hst : s ≤ t) (hℓ : 1 ≤ ℓ)
    (hmask : C = clockSet (labelsAt init ω s))
    (hcap : ∀ i, (virtualLabels init ω t i).phase.val ≤ 3) :
    Disjoint (markedAt init C ℓ cutoff s ω t)
      (sourceSet C (virtualLabels init ω t) ℓ) :=
  marks_source_disjoint C _ _ ℓ
    (markedAt_subset_above_of_seedPrefix init ω C ℓ cutoff s t
      hseed hst hℓ hmask hcap)

/-- The actual mark count has the immigration-plus-propagation ledger.
Its current invariant is proved from the observed seed and current phase
cap, rather than supplied as a new stochastic producer hypothesis. -/
theorem markedAt_card_step_of_seedPrefix (init : InputCfg n) (ω : InputLog n)
    (C : Finset (Fin init.card)) (ℓ cutoff s t : ℕ)
    (hseed : ω ∈ seedPrefix init s) (hst : s ≤ t) (hℓ : 1 ≤ ℓ)
    (hmask : C = clockSet (labelsAt init ω s))
    (hcap : ∀ i, (virtualLabels init ω t i).phase.val ≤ 3) :
    ((markedAt init C ℓ cutoff s ω (t + 1)).card : ℝ) =
      ((markedAt init C ℓ cutoff s ω t).card : ℝ) +
        immigrationIndicator init C ℓ cutoff t ω +
        propagationIndicator init C ℓ cutoff s t ω := by
  classical
  have hnat := markedAt_card_step init C ℓ cutoff s t ω hst
    (markedAt_source_disjoint_of_seedPrefix init ω C ℓ cutoff s t
      hseed hst hℓ hmask hcap)
  rw [hnat, Nat.cast_add, Nat.cast_add]
  simp only [immigrationIndicator, propagationIndicator]
  split_ifs <;> norm_num

theorem markedAt_card_step_le_of_seedPrefix (init : InputCfg n) (ω : InputLog n)
    (C : Finset (Fin init.card)) (ℓ cutoff s t : ℕ)
    (hseed : ω ∈ seedPrefix init s) (hst : s ≤ t) (hℓ : 1 ≤ ℓ)
    (hmask : C = clockSet (labelsAt init ω s))
    (hcap : ∀ i, (virtualLabels init ω t i).phase.val ≤ 3) :
    (markedAt init C ℓ cutoff s ω (t + 1)).card ≤
      (markedAt init C ℓ cutoff s ω t).card + 1 :=
  markedAt_card_step_le_add_one init C ℓ cutoff s t ω hst
    (markedAt_source_disjoint_of_seedPrefix init ω C ℓ cutoff s t
      hseed hst hℓ hmask hcap)

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockEarlyMarkEmbedding

end
