-- Ripple/PopulationProtocol/ExactMajority/Probability/LateF6ActualHazards.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.LateF6PairHazards

noncomputable section
open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal BigOperators

namespace Ripple.PopulationProtocol.ExactMajority.LateF6Hazards

open TimeTheorem PairLog PairLogAuxiliary LateF6Acceptance

variable {L K n : ℕ}

def Main (a : AgentState L K) : Prop := a.role = .main
def FreshMain (a : AgentState L K) : Prop := Main a ∧ a.phase.val < 4
def FrozenMain (a : AgentState L K) : Prop := Main a ∧ 4 ≤ a.phase.val
def Infected (a : AgentState L K) : Prop := 4 ≤ a.phase.val
def MainClass (C : Bias L → Prop) (a : AgentState L K) : Prop := Main a ∧ C a.bias
def FreshBad (C : Bias L → Prop) (a : AgentState L K) : Prop :=
  FreshMain a ∧ ¬ C a.bias
def FrozenBad (C : Bias L → Prop) (a : AgentState L K) : Prop :=
  FrozenMain a ∧ ¬ C a.bias

def mainCount (f : Fin n → AgentState L K) : ℕ := (pool f Main).card
def frozenCount (f : Fin n → AgentState L K) : ℕ := (pool f FrozenMain).card
def classCount (C : Bias L → Prop) (f : Fin n → AgentState L K) : ℕ :=
  (pool f (MainClass C)).card
def freshBadCount (C : Bias L → Prop) (f : Fin n → AgentState L K) : ℕ :=
  (pool f (FreshBad C)).card
def frozenBadCount (C : Bias L → Prop) (f : Fin n → AgentState L K) : ℕ :=
  (pool f (FrozenBad C)).card

def AcceptedReserve (a : AgentState L K) : Prop :=
  a.role = .reserve ∧ a.phase.val = 5 ∧ a.hour.val < L
def BadSample (J : Finset (Fin (L + 1))) (a : AgentState L K) : Prop :=
  AcceptedReserve a ∧ a.hour ∉ J
def acceptedCount (f : Fin n → AgentState L K) : ℕ := (pool f AcceptedReserve).card
def badSampleCount (J : Finset (Fin (L + 1))) (f : Fin n → AgentState L K) : ℕ :=
  (pool f (BadSample J)).card

private theorem nonclock_three_left (s t : AgentState L K)
    (hs : s.phase.val = 3) (ht : t.phase.val = 3) (hnc : s.role ≠ .clock) :
    (Transition L K s t).1.phase.val = 3 := by
  have hepi := ClockRealKernel.phaseEpidemicUpdate_eq_self_p3 s t hs ht
  have hsp : s.phase = ⟨3, by decide⟩ := Fin.ext hs
  have hl := (Phase3Transition_left_output_eq_rule1 L K s t s (by simp [hnc])).2
  unfold Transition
  rw [hepi]
  simp only [hsp, finishPhase10Entry_phase_val]
  exact (congrArg Fin.val hl).trans hs

private theorem nonclock_three_right (s t : AgentState L K)
    (hs : s.phase.val = 3) (ht : t.phase.val = 3) (hnc : t.role ≠ .clock) :
    (Transition L K s t).2.phase.val = 3 := by
  have hepi := ClockRealKernel.phaseEpidemicUpdate_eq_self_p3 s t hs ht
  have hsp : s.phase = ⟨3, by decide⟩ := Fin.ext hs
  have hl := (Phase3Transition_right_output_eq_rule1 L K s t t (by simp [hnc])).2
  unfold Transition
  rw [hepi]
  simp only [hsp, finishPhase10Entry_phase_val]
  exact (congrArg Fin.val hl).trans ht

theorem nonclock_freezes_left (s t : AgentState L K)
    (hs : Window s) (ht : Window t) (hnc : s.role ≠ .clock) :
    (s.phase.val < 4 ∧ 4 ≤ (Transition L K s t).1.phase.val) ↔
      (s.phase.val < 4 ∧ Infected t) := by
  constructor
  · rintro ⟨hbefore, hafter⟩
    refine ⟨hbefore, ?_⟩
    by_contra h
    have hlo := hs.1
    have hlo' := ht.1
    have hs' : s.phase.val = 3 := by omega
    have ht' : t.phase.val = 3 := by
      change ¬ 4 ≤ t.phase.val at h
      omega
    have hp := nonclock_three_left s t hs' ht' hnc
    omega
  · rintro ⟨hbefore, hpartner⟩
    refine ⟨hbefore, ?_⟩
    have hm := (phaseEpidemicUpdate_left_phase_ge_max L K s t).trans
      (phaseEpidemicUpdate_phase_le_Transition_phase L K s t).1
    exact hpartner.trans ((le_max_right _ _).trans hm)

theorem nonclock_freezes_right (s t : AgentState L K)
    (hs : Window s) (ht : Window t) (hnc : t.role ≠ .clock) :
    (t.phase.val < 4 ∧ 4 ≤ (Transition L K s t).2.phase.val) ↔
      (t.phase.val < 4 ∧ Infected s) := by
  constructor
  · rintro ⟨hbefore, hafter⟩
    refine ⟨hbefore, ?_⟩
    by_contra h
    have hlo := hs.1
    have hlo' := ht.1
    have hs' : s.phase.val = 3 := by
      change ¬ 4 ≤ s.phase.val at h
      omega
    have ht' : t.phase.val = 3 := by omega
    have hp := nonclock_three_right s t hs' ht' hnc
    omega
  · rintro ⟨hbefore, hpartner⟩
    refine ⟨hbefore, ?_⟩
    have hm := (phaseEpidemicUpdate_right_phase_ge_max L K s t).trans
      (phaseEpidemicUpdate_phase_le_Transition_phase L K s t).2
    exact hpartner.trans ((le_max_left _ _).trans hm)

def freezePair (C : Bias L → Prop)
    (f : Fin n → AgentState L K) (i j : Fin n) : Prop :=
  (FreshMain (f i) ∧ C (f i).bias ∧
    4 ≤ (Transition L K (f i) (f j)).1.phase.val) ∨
  (FreshMain (f j) ∧ C (f j).bias ∧
    4 ≤ (Transition L K (f i) (f j)).2.phase.val)

theorem freezePair_iff_contact (C : Bias L → Prop)
    (f : Fin n → AgentState L K) (hw : ∀ i, Window (f i)) (i j : Fin n) :
    freezePair C f i j ↔
      contact (fun a => FreshMain a ∧ C a.bias) Infected f i j := by
  have hnci (h : FreshMain (f i)) : (f i).role ≠ .clock := by
    rw [h.1]
    decide
  have hncj (h : FreshMain (f j)) : (f j).role ≠ .clock := by
    rw [h.1]
    decide
  constructor
  · rintro (⟨hf, hc, hp⟩ | ⟨hf, hc, hp⟩)
    · exact Or.inl ⟨⟨hf, hc⟩,
        ((nonclock_freezes_left _ _ (hw i) (hw j) (hnci hf)).mp ⟨hf.2, hp⟩).2⟩
    · exact Or.inr ⟨
        ((nonclock_freezes_right _ _ (hw i) (hw j) (hncj hf)).mp ⟨hf.2, hp⟩).2,
        ⟨hf, hc⟩⟩
  · rintro (⟨⟨hf, hc⟩, hp⟩ | ⟨hp, ⟨hf, hc⟩⟩)
    · exact Or.inl ⟨hf, hc,
        ((nonclock_freezes_left _ _ (hw i) (hw j) (hnci hf)).mpr ⟨hf.2, hp⟩).2⟩
    · exact Or.inr ⟨hf, hc,
        ((nonclock_freezes_right _ _ (hw i) (hw j) (hncj hf)).mpr ⟨hf.2, hp⟩).2⟩

theorem freezePair_goodPairs (C : Bias L → Prop)
    (f : Fin n → AgentState L K) (hw : ∀ i, Window (f i)) :
    goodPairs (freezePair C) f =
      goodPairs (contact (fun a => FreshMain a ∧ C a.bias) Infected) f := by
  classical
  apply Finset.filter_congr
  intro ij _
  exact and_congr_right fun _ => freezePair_iff_contact C f hw ij.1 ij.2

theorem freezePair_card (C : Bias L → Prop)
    (f : Fin n → AgentState L K) (hw : ∀ i, Window (f i)) :
    (goodPairs (freezePair C) f).card =
      2 * (pool f (fun a => FreshMain a ∧ C a.bias)).card * (pool f Infected).card := by
  rw [freezePair_goodPairs C f hw]
  apply contact_card
  intro a h h'
  exact Nat.not_lt_of_ge h' h.1.2

theorem fresh_frozen_count (f : Fin n → AgentState L K) :
    (pool f FreshMain).card + frozenCount f = mainCount f := by
  simpa only [FreshMain, FrozenMain, frozenCount, mainCount, not_lt] using
    pool_partition f Main (fun a => a.phase.val < 4)

theorem class_bad_count (C : Bias L → Prop) (f : Fin n → AgentState L K) :
    classCount C f + freshBadCount C f + frozenBadCount C f = mainCount f := by
  have hc := pool_partition f Main (fun a => C a.bias)
  have hb := pool_partition f (fun a => Main a ∧ ¬ C a.bias)
    (fun a => a.phase.val < 4)
  have hbf : (pool f (fun a => (Main a ∧ ¬ C a.bias) ∧ a.phase.val < 4)).card =
      freshBadCount C f := by
    change (pool f (fun a => (Main a ∧ ¬ C a.bias) ∧ a.phase.val < 4)).card =
      (pool f (FreshBad C)).card
    apply congrArg Finset.card
    ext i
    simp only [mem_pool, FreshBad, FreshMain]
    tauto
  have hbb : (pool f (fun a => (Main a ∧ ¬ C a.bias) ∧ ¬ a.phase.val < 4)).card =
      frozenBadCount C f := by
    change (pool f (fun a => (Main a ∧ ¬ C a.bias) ∧ ¬ a.phase.val < 4)).card =
      (pool f (FrozenBad C)).card
    apply congrArg Finset.card
    ext i
    simp only [mem_pool, FrozenBad, FrozenMain, not_lt]
    tauto
  rw [hbf, hbb] at hb
  change classCount C f + (pool f (fun a => Main a ∧ ¬ C a.bias)).card = mainCount f at hc
  omega

theorem freshBad_bound (C : Bias L → Prop) (f : Fin n → AgentState L K)
    (A : ℕ) (hA : A ≤ classCount C f) :
    freshBadCount C f ≤ mainCount f - A - frozenBadCount C f := by
  have h := class_bad_count C f
  omega

theorem frozenBad_bound (C : Bias L → Prop) (f : Fin n → AgentState L K)
    (A : ℕ) (hA : A ≤ classCount C f) :
    frozenBadCount C f ≤ mainCount f - A := by
  have h := class_bad_count C f
  omega

end Ripple.PopulationProtocol.ExactMajority.LateF6Hazards
end
