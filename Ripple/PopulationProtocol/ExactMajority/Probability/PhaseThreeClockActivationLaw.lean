-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockActivationLaw.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockProbabilityFloors

/-!
# The actual threshold-activation law on the virtual continuation

Activation means phase at least three. The virtual saturated-counter branch
preserves the epidemic phase, so every phase threshold is still copied across
a selected pair. In particular activation is monotone, each step adds at most
two active labels, and a mixed active/inactive pair adds exactly one.

The conditional probability is under the original pair-log law. Backup labels
count as activated in these statements; excluding backup is a separate terminal
alternative when these laws are used for the all-Phase-3 event.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal BigOperators MeasureTheory ProbabilityTheory

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockActivationLaw

open TimeTheorem PairLog PairLogAuxiliary PhaseThreeClockVirtual
  PhaseThreeClockGatedLaw PhaseThreeClockProbabilityFloors

variable {L K m : ℕ}

theorem virtualRule_left_phase_ge_pair_max (s t : AgentState L K) :
    max s.phase.val t.phase.val ≤ (virtualRule s t).1.phase.val := by
  by_cases hc : CapCounterPair s t
  · simpa only [virtualRule, if_pos hc, saturatedCounterStep_phase] using
      phaseEpidemicUpdate_left_phase_ge_max (L := L) (K := K) s t
  · simpa only [virtualRule, if_neg hc] using
      Transition_left_phase_ge_pair_max s t

theorem virtualRule_right_phase_ge_pair_max (s t : AgentState L K) :
    max s.phase.val t.phase.val ≤ (virtualRule s t).2.phase.val := by
  by_cases hc : CapCounterPair s t
  · simpa only [virtualRule, if_pos hc, saturatedCounterStep_phase] using
      phaseEpidemicUpdate_right_phase_ge_max (L := L) (K := K) s t
  · simpa only [virtualRule, if_neg hc] using
      Transition_right_phase_ge_pair_max s t

theorem virtualRule_threshold_copy (s t : AgentState L K) (q : ℕ)
    (hq : q ≤ s.phase.val ∨ q ≤ t.phase.val) :
    q ≤ (virtualRule s t).1.phase.val ∧ q ≤ (virtualRule s t).2.phase.val := by
  have hmax : q ≤ max s.phase.val t.phase.val := by
    rcases hq with hs | ht
    · exact hs.trans (le_max_left _ _)
    · exact ht.trans (le_max_right _ _)
  exact ⟨hmax.trans (virtualRule_left_phase_ge_pair_max s t),
    hmax.trans (virtualRule_right_phase_ge_pair_max s t)⟩

theorem ruleUpdate_virtual_phase_ge (f : Fin m → AgentState L K)
    (i j k : Fin m) :
    (f k).phase.val ≤ (ruleUpdate virtualRule f i j k).phase.val := by
  by_cases hkj : k = j
  · subst k
    simpa only [ruleUpdate, Function.update_self] using
      (le_max_right (f i).phase.val (f j).phase.val).trans
        (virtualRule_right_phase_ge_pair_max (f i) (f j))
  · by_cases hki : k = i
    · subst k
      simpa only [ruleUpdate, Function.update_of_ne hkj, Function.update_self] using
        (le_max_left (f i).phase.val (f j).phase.val).trans
          (virtualRule_left_phase_ge_pair_max (f i) (f j))
    · simp only [ruleUpdate, Function.update_of_ne hkj, Function.update_of_ne hki,
        le_refl]

theorem virtualLabels_phase_succ_le (init : Cfg L K) (ω : Ω L K)
    (t : ℕ) (i : Fin init.card) :
    (virtualLabels init ω t i).phase.val ≤
      (virtualLabels init ω (t + 1) i).phase.val := by
  rw [virtualLabels_succ]
  cases hd : drawLabels init ω (t + 1) with
  | none => exact le_rfl
  | some ij =>
      rcases ij with ⟨j, k⟩
      exact ruleUpdate_virtual_phase_ge _ j k i

theorem virtualLabels_phase_mono (init : Cfg L K) (ω : Ω L K)
    (i : Fin init.card) :
    Monotone (fun t => (virtualLabels init ω t i).phase.val) :=
  monotone_nat_of_le_succ (fun t => virtualLabels_phase_succ_le init ω t i)

def activeSet (f : Fin m → AgentState L K) : Finset (Fin m) :=
  Finset.univ.filter (fun i => 3 ≤ (f i).phase.val)

def dormantSet (f : Fin m → AgentState L K) : Finset (Fin m) :=
  Finset.univ.filter (fun i => ¬ 3 ≤ (f i).phase.val)

def activeCount (f : Fin m → AgentState L K) : ℕ := (activeSet f).card

def activeInd (a : AgentState L K) : ℕ := if 3 ≤ a.phase.val then 1 else 0

def MixedActivation (f : Fin m → AgentState L K) (i j : Fin m) : Prop :=
  (i ∈ activeSet f ∧ j ∈ dormantSet f) ∨
    (i ∈ dormantSet f ∧ j ∈ activeSet f)

theorem activeCount_eq_sum (f : Fin m → AgentState L K) :
    activeCount f = ∑ i, activeInd (f i) := by
  unfold activeCount activeSet activeInd
  rw [Finset.card_filter]

theorem activeCount_le_card (f : Fin m → AgentState L K) :
    activeCount f ≤ m := by
  have h := Finset.card_le_card
    (Finset.filter_subset (fun i : Fin m => 3 ≤ (f i).phase.val) Finset.univ)
  simpa only [activeCount, activeSet, Finset.card_univ, Fintype.card_fin] using h

theorem activeCount_eq_card_iff (f : Fin m → AgentState L K) :
    activeCount f = m ↔ ∀ i, 3 ≤ (f i).phase.val := by
  constructor
  · intro h
    have hset : activeSet f = Finset.univ := by
      apply Finset.eq_of_subset_of_card_le
        (Finset.filter_subset (fun i : Fin m => 3 ≤ (f i).phase.val) Finset.univ)
      simpa only [Finset.card_univ, Fintype.card_fin, activeCount] using h.ge
    intro i
    have hi : i ∈ activeSet f := by rw [hset]; exact Finset.mem_univ i
    simpa only [activeSet, Finset.mem_filter, Finset.mem_univ, true_and] using hi
  · intro h
    have hset : activeSet f = Finset.univ := by
      ext i
      simp [activeSet, h i]
    simp only [activeCount, hset, Finset.card_univ, Fintype.card_fin]

/-- All threshold-activated labels are in Phase 3 if the current state
also excludes phases above 3. No global future guard is assumed. -/
theorem phase_three_of_activeCount_eq_card (f : Fin m → AgentState L K)
    (hfull : activeCount f = m) (hcap : ∀ i, (f i).phase.val ≤ 3) :
    ∀ i, (f i).phase.val = 3 :=
  fun i => le_antisymm (hcap i) ((activeCount_eq_card_iff f).1 hfull i)

theorem activeCount_virtualLabels_stronglyMeasurable (init : Cfg L K) (t : ℕ) :
    StronglyMeasurable[pairLogFiltration L K t]
      (fun ω => (activeCount (virtualLabels init ω t) : ℝ)) :=
  ((measurable_of_countable (fun f : Fin init.card → AgentState L K =>
    (activeCount f : ℝ))).comp (measurable_virtualLabels init t)).stronglyMeasurable

theorem dormantSet_card (f : Fin m → AgentState L K) :
    (dormantSet f).card = m - activeCount f := by
  have h := Finset.filter_card_add_filter_neg_card_eq_card
    (s := (Finset.univ : Finset (Fin m))) (fun i => 3 ≤ (f i).phase.val)
  simp only [Finset.card_univ, Fintype.card_fin] at h
  change (dormantSet f).card = m - (activeSet f).card
  change (activeSet f).card + (dormantSet f).card = m at h
  omega

theorem active_dormant_disjoint (f : Fin m → AgentState L K) :
    Disjoint (activeSet f) (dormantSet f) := by
  apply Finset.disjoint_left.mpr
  intro i ha hd
  simp only [activeSet, dormantSet, Finset.mem_filter, Finset.mem_univ, true_and] at ha hd
  exact hd ha

theorem goodPairs_mixedActivation (f : Fin m → AgentState L K) :
    goodPairs MixedActivation f =
      (activeSet f ×ˢ dormantSet f) ∪ (dormantSet f ×ˢ activeSet f) := by
  classical
  ext ⟨i, j⟩
  simp only [goodPairs, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_union, Finset.mem_product, MixedActivation]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    intro hij
    subst j
    rcases h with ⟨ha, hd⟩ | ⟨hd, ha⟩ <;>
      exact Finset.disjoint_left.mp (active_dormant_disjoint f) ha hd

theorem goodPairs_mixedActivation_card (f : Fin m → AgentState L K) :
    (goodPairs MixedActivation f).card = 2 * activeCount f * (m - activeCount f) := by
  have hdisj :
      Disjoint (activeSet f ×ˢ dormantSet f) (dormantSet f ×ˢ activeSet f) := by
    apply Finset.disjoint_left.mpr
    intro ij hleft hright
    exact Finset.disjoint_left.mp (active_dormant_disjoint f)
      (Finset.mem_product.mp hleft).1 (Finset.mem_product.mp hright).1
  rw [goodPairs_mixedActivation, Finset.card_union_of_disjoint hdisj,
    Finset.card_product, Finset.card_product, dormantSet_card]
  change activeCount f * (m - activeCount f) +
    (m - activeCount f) * activeCount f = _
  ring

theorem activeCount_ruleUpdate_mono (f : Fin m → AgentState L K) (i j : Fin m) :
    activeCount f ≤ activeCount (ruleUpdate virtualRule f i j) := by
  apply Finset.card_le_card
  intro k hk
  simp only [activeSet, Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
  exact hk.trans (ruleUpdate_virtual_phase_ge f i j k)

theorem activeCount_ruleUpdate_le_add_two (f : Fin m → AgentState L K)
    (i j : Fin m) (hij : i ≠ j) :
    activeCount (ruleUpdate virtualRule f i j) ≤ activeCount f + 2 := by
  have hsum := sum_update_pair activeInd f i j hij
    (virtualRule (f i) (f j)).1 (virtualRule (f i) (f j)).2
  have ha : activeInd (virtualRule (f i) (f j)).1 ≤ 1 := by
    unfold activeInd
    split_ifs <;> omega
  have hb : activeInd (virtualRule (f i) (f j)).2 ≤ 1 := by
    unfold activeInd
    split_ifs <;> omega
  rw [activeCount_eq_sum, activeCount_eq_sum]
  unfold ruleUpdate
  omega

theorem activeCount_ruleUpdate_mixed (f : Fin m → AgentState L K)
    (i j : Fin m) (hij : i ≠ j) (hmixed : MixedActivation f i j) :
    activeCount (ruleUpdate virtualRule f i j) = activeCount f + 1 := by
  have hsum := sum_update_pair activeInd f i j hij
    (virtualRule (f i) (f j)).1 (virtualRule (f i) (f j)).2
  have hm :
      (3 ≤ (f i).phase.val ∧ ¬ 3 ≤ (f j).phase.val) ∨
      (¬ 3 ≤ (f i).phase.val ∧ 3 ≤ (f j).phase.val) := by
    simpa only [MixedActivation, activeSet, dormantSet, Finset.mem_filter,
      Finset.mem_univ, true_and] using hmixed
  have hout := virtualRule_threshold_copy (f i) (f j) 3
    (hm.elim (fun h => Or.inl h.1) (fun h => Or.inr h.2))
  have ha : activeInd (virtualRule (f i) (f j)).1 = 1 := by
    simp only [activeInd, if_pos hout.1]
  have hb : activeInd (virtualRule (f i) (f j)).2 = 1 := by
    simp only [activeInd, if_pos hout.2]
  have hold : activeInd (f i) + activeInd (f j) = 1 := by
    rcases hm with ⟨hi, hj⟩ | ⟨hi, hj⟩ <;>
      simp [activeInd, hi, hj]
  rw [activeCount_eq_sum, activeCount_eq_sum]
  unfold ruleUpdate
  omega

theorem activeCount_virtualLabels_succ_bounds (init : Cfg L K)
    (ω : Ω L K) (t : ℕ) :
    activeCount (virtualLabels init ω t) ≤ activeCount (virtualLabels init ω (t + 1)) ∧
      activeCount (virtualLabels init ω (t + 1)) ≤ activeCount (virtualLabels init ω t) + 2 := by
  rw [virtualLabels_succ]
  cases hd : drawLabels init ω (t + 1) with
  | none => exact ⟨le_rfl, Nat.le_add_right _ _⟩
  | some ij =>
      rcases ij with ⟨i, j⟩
      have hij := (labelsAt_selected_transition init ω t i j hd).1
      exact ⟨activeCount_ruleUpdate_mono _ i j, activeCount_ruleUpdate_le_add_two _ i j hij⟩

theorem activeCount_virtualLabels_mono (init : Cfg L K) (ω : Ω L K) :
    Monotone (fun t => activeCount (virtualLabels init ω t)) :=
  monotone_nat_of_le_succ (fun t => (activeCount_virtualLabels_succ_bounds init ω t).1)

open Classical in
/-- The actual mixed-pair indicator is a lower bound on the virtual activation increment. -/
theorem activeCount_virtualLabels_increment (init : Cfg L K)
    (ω : Ω L K) (t : ℕ) :
    (activeCount (virtualLabels init ω t) : ℝ) +
        (if ∃ i j, drawLabels init ω (t + 1) = some (i, j) ∧
          MixedActivation (virtualLabels init ω t) i j then (1 : ℝ) else 0) ≤
      (activeCount (virtualLabels init ω (t + 1)) : ℝ) := by
  by_cases he : ∃ i j, drawLabels init ω (t + 1) = some (i, j) ∧
      MixedActivation (virtualLabels init ω t) i j
  · rw [if_pos he]
    obtain ⟨i, j, hd, hm⟩ := he
    have hij := (labelsAt_selected_transition init ω t i j hd).1
    have h := activeCount_ruleUpdate_mixed (virtualLabels init ω t) i j hij hm
    rw [virtualLabels_succ, hd]
    exact_mod_cast h.ge
  · rw [if_neg he, add_zero]
    exact_mod_cast (activeCount_virtualLabels_succ_bounds init ω t).1

open Classical in
theorem mixedActivation_conditional_law (init : Cfg L K)
    (hc : 2 ≤ init.card) (t : ℕ) :
    (law init)[fun ω =>
      if ∃ i j, drawLabels init ω (t + 1) = some (i, j) ∧
          MixedActivation (virtualLabels init ω t) i j
      then (1 : ℝ) else 0 | pairLogFiltration L K t] =ᵐ[law init]
      fun ω =>
        ((2 * activeCount (virtualLabels init ω t) *
          (init.card - activeCount (virtualLabels init ω t)) : ℕ) : ℝ) /
          ((init.card : ℝ) * ((init.card : ℝ) - 1)) := by
  simpa only [goodPairs_mixedActivation_card, virtualLabels] using
    aux_pair_conditional_probability init hc virtualRule MixedActivation t

open Classical in
theorem mixedActivation_stronglyMeasurable (init : Cfg L K) (t : ℕ) :
    StronglyMeasurable[pairLogFiltration L K (t + 1)] (fun ω =>
      if ∃ i j, drawLabels init ω (t + 1) = some (i, j) ∧
          MixedActivation (virtualLabels init ω t) i j
      then (1 : ℝ) else 0) := by
  simpa only [virtualLabels] using
    stronglyMeasurable_aux_pair_indicator init virtualRule MixedActivation t

/-- The reciprocal potential used in the first half of activation has the
full exponential rate 1/m under the exact two-orientation epidemic law. -/
theorem activation_reciprocal_rate (m A : ℝ)
    (hm : 2 ≤ m) (hA : 1 ≤ A) (hhalf : 2 * A ≤ m) :
    1 / m ≤
      (2 * A * (m - A) / (m * (m - 1))) * (2 / (2 * A + 1)) := by
  have hm0 : 0 < m := by linarith
  have hmone : 0 < m - 1 := by linarith
  have hAone : 0 < 2 * A + 1 := by linarith
  have hden : 0 < m * (m - 1) * (2 * A + 1) := by positivity
  have hprod := mul_nonneg (by linarith : 0 ≤ A - 1)
    (by linarith : 0 ≤ m - 2 * A)
  have hquad : (m - 1) * (2 * A + 1) ≤ 4 * A * (m - A) := by
    nlinarith
  rw [show (2 * A * (m - A) / (m * (m - 1))) * (2 / (2 * A + 1)) =
    (4 * A * (m - A)) / (m * (m - 1) * (2 * A + 1)) by
      rw [div_mul_div_comm]; congr 1; ring]
  apply (div_le_div_iff₀ hm0 hden).2
  have hscaled := mul_le_mul_of_nonneg_left hquad hm0.le
  nlinarith only [hscaled]

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockActivationLaw

end
