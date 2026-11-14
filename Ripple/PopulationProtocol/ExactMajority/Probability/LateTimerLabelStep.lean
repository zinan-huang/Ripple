-- Ripple/PopulationProtocol/ExactMajority/Probability/LateTimerLabelStep.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.LateTimerCounterStep
import Ripple.PopulationProtocol.ExactMajority.Probability.MixedWindowClosure

/-!
# One draw of the pair-log, seen label by label

For the persistent label vector `f : Fin m -> AgentState L K` and one draw `d`,
the Clock counters at phase `p` (`5 <= p <= 8`) after `stepLabels f d` satisfy the
participation inequalities of `LateTimerCounterStep`, where the participation
indicator `delta i` of label `i` is `1` exactly when `i` is one of the two selected
labels.
-/

noncomputable section

namespace Ripple.PopulationProtocol.ExactMajority

open TimeTheorem PairLog
open AdvanceNoOvershoot

namespace LateTimerLabelStep

variable {L K m : ℕ}

open Classical in
/-- Participation of label `i` in the draw `d` on the label vector `f`. -/
noncomputable def participates (f : Fin m → AgentState L K) (d : Draw L K)
    (i : Fin m) : ℕ :=
  if ∃ j : Fin m, j ≠ i ∧
      (selectLabels f d = some (i, j) ∨ selectLabels f d = some (j, i))
  then 1 else 0

theorem participates_of_left (f : Fin m → AgentState L K) (d : Draw L K)
    (i j : Fin m) (h : selectLabels f d = some (i, j)) :
    participates f d i = 1 := by
  classical
  have hij := selectLabels_distinct f d i j h
  unfold participates
  rw [if_pos ⟨j, Ne.symm hij, Or.inl h⟩]

theorem participates_of_right (f : Fin m → AgentState L K) (d : Draw L K)
    (i j : Fin m) (h : selectLabels f d = some (i, j)) :
    participates f d j = 1 := by
  classical
  have hij := selectLabels_distinct f d i j h
  unfold participates
  rw [if_pos ⟨i, hij, Or.inr h⟩]

theorem participates_of_none (f : Fin m → AgentState L K) (d : Draw L K)
    (h : selectLabels f d = none) (i : Fin m) :
    participates f d i = 0 := by
  classical
  unfold participates
  rw [if_neg]
  rintro ⟨j, -, hj | hj⟩ <;> simp [h] at hj

theorem participates_of_other (f : Fin m → AgentState L K) (d : Draw L K)
    (a b i : Fin m) (h : selectLabels f d = some (a, b))
    (hia : i ≠ a) (hib : i ≠ b) : participates f d i = 0 := by
  classical
  unfold participates
  rw [if_neg]
  rintro ⟨j, -, hj | hj⟩ <;> simp [h] at hj <;> omega

theorem participates_le_one (f : Fin m → AgentState L K) (d : Draw L K)
    (i : Fin m) : participates f d i ≤ 1 := by
  classical
  unfold participates
  split_ifs <;> omega

/-- The label-level counter step. -/
theorem label_step (p : ℕ) (hp5 : 5 ≤ p) (hp8 : p ≤ 8)
    (f : Fin m → AgentState L K) (d : Draw L K)
    (hwf : ∀ k, WfAgent (L := L) (K := K) (f k))
    (hup : ∀ k, (f k).phase.val ≤ p)
    (hge3 : ∀ k, 3 ≤ (f k).phase.val)
    (i : Fin m)
    (hclock : (stepLabels f d i).role = .clock)
    (hph : (stepLabels f d i).phase.val = p) :
    (f i).role = .clock ∧
      ((f i).phase.val = p →
        (f i).counter.val ≤ (stepLabels f d i).counter.val + participates f d i) ∧
      ((f i).phase.val < p →
        50 * (L + 1) ≤ (stepLabels f d i).counter.val + participates f d i) ∧
      ((∀ k, (f k).phase.val < p) →
        50 * (L + 1) ≤ (stepLabels f d i).counter.val) := by
  classical
  unfold stepLabels at hclock hph ⊢
  cases hsel : selectLabels f d with
  | none =>
      rw [hsel] at hclock hph
      simp only at hclock hph ⊢
      refine ⟨hclock, ?_, ?_, ?_⟩
      · intro _; omega
      · intro h; omega
      · intro hall; have := hall i; omega
  | some pair =>
      obtain ⟨a, b⟩ := pair
      rw [hsel] at hclock hph
      simp only at hclock hph ⊢
      have hab := selectLabels_distinct f d a b hsel
      by_cases hia : i = a
      · subst hia
        have hupd : updateLabels f i b i =
            ((NonuniformMajority L K).δ (f i) (f b)).1 := by
          unfold updateLabels
          rw [Function.update_of_ne hab, Function.update_self]
        rw [hupd] at hclock hph ⊢
        change (Transition L K (f i) (f b)).1.role = .clock at hclock
        change (Transition L K (f i) (f b)).1.phase.val = p at hph
        have hfc : (f i).role = .clock := by
          by_contra hnc
          exact MixedWindowClosure.Transition_first_no_clock_creation_of_phase_ge_3 (f i) (f b)
            (hge3 i) (hge3 b) hnc hclock
        have hpar := participates_of_left f d i b hsel
        obtain ⟨hr, h1, h2, h3⟩ :=
          timer_left_counter_step p hp5 hp8 (f i) (f b) (hwf i) (hwf b)
            (hup i) (hup b) hfc hph
        refine ⟨hfc, ?_, ?_, ?_⟩
        · intro hp; have := h1 hp; show _ ≤ (Transition L K (f i) (f b)).1.counter.val + _; omega
        · intro hlt; have := h2 hlt; show _ ≤ (Transition L K (f i) (f b)).1.counter.val + _; omega
        · intro hall
          have := h3 (by have := hall i; have := hall b; omega)
          show _ ≤ (Transition L K (f i) (f b)).1.counter.val
          omega
      · by_cases hib : i = b
        · subst hib
          have hupd : updateLabels f a i i =
              ((NonuniformMajority L K).δ (f a) (f i)).2 := by
            unfold updateLabels
            rw [Function.update_self]
          rw [hupd] at hclock hph ⊢
          change (Transition L K (f a) (f i)).2.role = .clock at hclock
          change (Transition L K (f a) (f i)).2.phase.val = p at hph
          have hfc : (f i).role = .clock := by
            by_contra hnc
            exact MixedWindowClosure.Transition_second_no_clock_creation_of_phase_ge_3 (f a) (f i)
              (hge3 a) (hge3 i) hnc hclock
          have hpar := participates_of_right f d a i hsel
          obtain ⟨hr, h1, h2, h3⟩ :=
            timer_right_counter_step p hp5 hp8 (f a) (f i) (hwf a) (hwf i)
              (hup a) (hup i) hfc hph
          refine ⟨hfc, ?_, ?_, ?_⟩
          · intro hp; have := h1 hp; show _ ≤ (Transition L K (f a) (f i)).2.counter.val + _; omega
          · intro hlt; have := h2 hlt; show _ ≤ (Transition L K (f a) (f i)).2.counter.val + _; omega
          · intro hall
            have := h3 (by have := hall i; have := hall a; omega)
            show _ ≤ (Transition L K (f a) (f i)).2.counter.val
            omega
        · have hupd : updateLabels f a b i = f i := by
            unfold updateLabels
            rw [Function.update_of_ne hib, Function.update_of_ne hia]
          rw [hupd] at hclock hph ⊢
          refine ⟨hclock, ?_, ?_, ?_⟩
          · intro _; omega
          · intro h; omega
          · intro hall; have := hall i; omega

end LateTimerLabelStep

end Ripple.PopulationProtocol.ExactMajority

end
