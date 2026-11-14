-- Ripple/PopulationProtocol/ExactMajority/Probability/LateF6CountSteps.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.LateF6ActualHazards

noncomputable section
namespace Ripple.PopulationProtocol.ExactMajority.LateF6Hazards

open PairLog LateF6Acceptance

variable {L K n : ℕ}

theorem bitNat_or_of_disjoint (P Q : Prop) (h : P → Q → False) :
    bitNat (P ∨ Q) = bitNat P + bitNat Q := by
  classical
  by_cases hP : P <;> by_cases hQ : Q
  · exact False.elim (h hP hQ)
  · simp [bitNat, hP, hQ]
  · simp [bitNat, hP, hQ]
  · simp [bitNat, hP, hQ]

theorem bitNat_add_of_iff (R P Q : Prop) (hr : R ↔ P ∨ Q)
    (h : P → Q → False) : bitNat R = bitNat P + bitNat Q := by
  rw [propext hr]
  exact bitNat_or_of_disjoint P Q h

theorem bitNat_contact (f : Fin n → AgentState L K) (i j : Fin n)
    (P Q : AgentState L K → Prop) (hd : ∀ a, P a → Q a → False) :
    bitNat (contact P Q f i j) =
      bitNat (P (f i) ∧ Q (f j)) + bitNat (Q (f i) ∧ P (f j)) := by
  apply bitNat_or_of_disjoint
  intro h h'
  exact hd (f i) h.1 h'.1

private theorem max_phase_left (s t : AgentState L K) :
    max s.phase.val t.phase.val ≤ (Transition L K s t).1.phase.val :=
  (phaseEpidemicUpdate_left_phase_ge_max L K s t).trans
    (phaseEpidemicUpdate_phase_le_Transition_phase L K s t).1

private theorem max_phase_right (s t : AgentState L K) :
    max s.phase.val t.phase.val ≤ (Transition L K s t).2.phase.val :=
  (phaseEpidemicUpdate_right_phase_ge_max L K s t).trans
    (phaseEpidemicUpdate_phase_le_Transition_phase L K s t).2

theorem frozenMain_left_iff (s t : AgentState L K) (hs : Window s) (ht : Window t) :
    FrozenMain (Transition L K s t).1 ↔
      FrozenMain s ∨ (FreshMain s ∧ Infected t) := by
  have hr := (transition_roles s t hs ht).1
  constructor
  · intro h
    have hm : Main s := hr.symm.trans h.1
    by_cases hp : 4 ≤ s.phase.val
    · exact Or.inl ⟨hm, hp⟩
    · have hlt : s.phase.val < 4 := by omega
      have hnc : s.role ≠ .clock := by rw [hm]; decide
      exact Or.inr ⟨⟨hm, hlt⟩,
        ((nonclock_freezes_left s t hs ht hnc).mp ⟨hlt, h.2⟩).2⟩
  · rintro (h | h)
    · exact ⟨hr.trans h.1, h.2.trans ((le_max_left _ _).trans (max_phase_left s t))⟩
    · have hnc : s.role ≠ .clock := by rw [h.1.1]; decide
      exact ⟨hr.trans h.1.1,
        ((nonclock_freezes_left s t hs ht hnc).mpr ⟨h.1.2, h.2⟩).2⟩

theorem frozenMain_right_iff (s t : AgentState L K) (hs : Window s) (ht : Window t) :
    FrozenMain (Transition L K s t).2 ↔
      FrozenMain t ∨ (Infected s ∧ FreshMain t) := by
  have hr := (transition_roles s t hs ht).2
  constructor
  · intro h
    have hm : Main t := hr.symm.trans h.1
    by_cases hp : 4 ≤ t.phase.val
    · exact Or.inl ⟨hm, hp⟩
    · have hlt : t.phase.val < 4 := by omega
      have hnc : t.role ≠ .clock := by rw [hm]; decide
      exact Or.inr ⟨
        ((nonclock_freezes_right s t hs ht hnc).mp ⟨hlt, h.2⟩).2, ⟨hm, hlt⟩⟩
  · rintro (h | h)
    · exact ⟨hr.trans h.1, h.2.trans ((le_max_right _ _).trans (max_phase_right s t))⟩
    · have hnc : t.role ≠ .clock := by rw [h.2.1]; decide
      exact ⟨hr.trans h.2.1,
        ((nonclock_freezes_right s t hs ht hnc).mpr ⟨h.2.2, h.1⟩).2⟩

theorem frozenBad_left_iff (C : Bias L → Prop) (s t : AgentState L K)
    (hs : Window s) (ht : Window t) :
    FrozenBad C (Transition L K s t).1 ↔
      FrozenBad C s ∨ (FreshBad C s ∧ Infected t) := by
  constructor
  · intro h
    have hm : Main s := (transition_roles s t hs ht).1.symm.trans h.1.1
    have hb := transition_main_freeze_left s t hs ht hm h.1.2
    have hc : ¬ C s.bias := by simpa only [hb] using h.2
    rcases (frozenMain_left_iff s t hs ht).mp h.1 with hf | hf
    · exact Or.inl ⟨hf, hc⟩
    · exact Or.inr ⟨⟨hf.1, hc⟩, hf.2⟩
  · rintro (h | h)
    · have hf := (frozenMain_left_iff s t hs ht).mpr (Or.inl h.1)
      have hb := transition_main_freeze_left s t hs ht h.1.1 hf.2
      exact ⟨hf, by simpa only [hb] using h.2⟩
    · have hf := (frozenMain_left_iff s t hs ht).mpr (Or.inr ⟨h.1.1, h.2⟩)
      have hb := transition_main_freeze_left s t hs ht h.1.1.1 hf.2
      exact ⟨hf, by simpa only [hb] using h.1.2⟩

theorem frozenBad_right_iff (C : Bias L → Prop) (s t : AgentState L K)
    (hs : Window s) (ht : Window t) :
    FrozenBad C (Transition L K s t).2 ↔
      FrozenBad C t ∨ (Infected s ∧ FreshBad C t) := by
  constructor
  · intro h
    have hm : Main t := (transition_roles s t hs ht).2.symm.trans h.1.1
    have hb := transition_main_freeze_right s t hs ht hm h.1.2
    have hc : ¬ C t.bias := by simpa only [hb] using h.2
    rcases (frozenMain_right_iff s t hs ht).mp h.1 with hf | hf
    · exact Or.inl ⟨hf, hc⟩
    · exact Or.inr ⟨hf.1, ⟨hf.2, hc⟩⟩
  · rintro (h | h)
    · have hf := (frozenMain_right_iff s t hs ht).mpr (Or.inl h.1)
      have hb := transition_main_freeze_right s t hs ht h.1.1 hf.2
      exact ⟨hf, by simpa only [hb] using h.2⟩
    · have hf := (frozenMain_right_iff s t hs ht).mpr (Or.inr ⟨h.1, h.2.1⟩)
      have hb := transition_main_freeze_right s t hs ht h.2.1.1 hf.2
      exact ⟨hf, by simpa only [hb] using h.2.2⟩

theorem frozenCount_update (f : Fin n → AgentState L K)
    (hw : ∀ i, Window (f i)) (i j : Fin n) (hij : i ≠ j) :
    frozenCount (updateLabels f i j) =
      frozenCount f + bitNat (freezePair (fun _ => True) f i j) := by
  have h := pool_updateLabels_balance f FrozenMain i j hij
  change frozenCount (updateLabels f i j) +
      bitNat (FrozenMain (f i)) + bitNat (FrozenMain (f j)) =
    frozenCount f + bitNat (FrozenMain (Transition L K (f i) (f j)).1) +
      bitNat (FrozenMain (Transition L K (f i) (f j)).2) at h
  have hl := bitNat_add_of_iff _ _ _
    (frozenMain_left_iff (f i) (f j) (hw i) (hw j))
    (fun h h' => Nat.not_lt_of_ge h.2 h'.1.2)
  have hr := bitNat_add_of_iff _ _ _
    (frozenMain_right_iff (f i) (f j) (hw i) (hw j))
    (fun h h' => Nat.not_lt_of_ge h.2 h'.2.2)
  rw [hl, hr] at h
  have hc := bitNat_contact f i j FreshMain Infected
    (fun _ h h' => Nat.not_lt_of_ge h' h.2)
  have hf : freezePair (fun _ => True) f i j ↔ contact FreshMain Infected f i j := by
    simpa only [and_true] using freezePair_iff_contact (fun _ => True) f hw i j
  rw [propext hf]
  omega

theorem frozenBadCount_update (C : Bias L → Prop) (f : Fin n → AgentState L K)
    (hw : ∀ i, Window (f i)) (i j : Fin n) (hij : i ≠ j) :
    frozenBadCount C (updateLabels f i j) =
      frozenBadCount C f + bitNat (freezePair (fun b => ¬ C b) f i j) := by
  have h := pool_updateLabels_balance f (FrozenBad C) i j hij
  change frozenBadCount C (updateLabels f i j) +
      bitNat (FrozenBad C (f i)) + bitNat (FrozenBad C (f j)) =
    frozenBadCount C f + bitNat (FrozenBad C (Transition L K (f i) (f j)).1) +
      bitNat (FrozenBad C (Transition L K (f i) (f j)).2) at h
  have hl := bitNat_add_of_iff _ _ _
    (frozenBad_left_iff C (f i) (f j) (hw i) (hw j))
    (fun h h' => Nat.not_lt_of_ge h.1.2 h'.1.1.2)
  have hr := bitNat_add_of_iff _ _ _
    (frozenBad_right_iff C (f i) (f j) (hw i) (hw j))
    (fun h h' => Nat.not_lt_of_ge h.1.2 h'.2.1.2)
  rw [hl, hr] at h
  have hc := bitNat_contact f i j (FreshBad C) Infected
    (fun _ h h' => Nat.not_lt_of_ge h' h.1.2)
  have hf : freezePair (fun b => ¬ C b) f i j ↔
      contact (FreshBad C) Infected f i j :=
    freezePair_iff_contact (fun b => ¬ C b) f hw i j
  rw [propext hf]
  omega

theorem bitNat_zero_one (P : Prop) : bitNat P = 0 ∨ bitNat P = 1 := by
  classical
  by_cases h : P <;> simp [bitNat, h]

theorem bitNat_mono {P Q : Prop} (h : P → Q) : bitNat P ≤ bitNat Q := by
  classical
  by_cases hP : P
  · simp [bitNat, hP, h hP]
  · simp [bitNat, hP]

theorem freezePair_class_implies (C : Bias L → Prop)
    (f : Fin n → AgentState L K) (i j : Fin n) :
    freezePair C f i j → freezePair (fun _ => True) f i j := by
  unfold freezePair
  tauto

end Ripple.PopulationProtocol.ExactMajority.LateF6Hazards
end
