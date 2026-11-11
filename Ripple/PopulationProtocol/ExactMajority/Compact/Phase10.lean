/-
# Phase 10 respects the live table

At phase 10 every `Θ(log n)` field is dead. `Phase10Transition` reads only `full` and
`output` and writes only those two fields, so it commutes with any change of the dead
fields (`phase10_update`), and the normal form of its result is the normal form of the
result on the normal forms.
-/

import Ripple.PopulationProtocol.ExactMajority.Compact.Inits

namespace Ripple.PopulationProtocol.ExactMajority

namespace Compact

variable {L K : ℕ}

/-- At phase 10 the normal form resets `bias`, `hour`, `minute` and `counter`. -/
lemma phase10_normalize_eq (a : AgentState L K) (hp : a.phase.val = 10) :
    normalize a = { a with
      bias := .zero, hour := hourDefault, minute := minuteDefault, counter := counterDefault } := by
  rcases a with ⟨i, o, ph, r, g, b, sb, h, m, f, op, c⟩
  simp only at hp
  simp [normalize, normalizeAtVal, liveBias, liveHour, liveMinute, liveCounter, hp]

/-- At phase 10 the normal form does not see the four dead fields. -/
lemma phase10_normalize_update (a : AgentState L K) (hp : a.phase.val = 10) (b : Bias L)
    (h : Fin (L + 1)) (m : Fin (K * (L + 1) + 1)) (c : Fin (50 * (L + 1) + 1)) :
    normalize { a with bias := b, hour := h, minute := m, counter := c } = normalize a := by
  rcases a with ⟨i, o, ph, r, g, b₀, sb, h₀, m₀, f, op, c₀⟩
  simp only at hp
  simp [normalize, normalizeAtVal, liveBias, liveHour, liveMinute, liveCounter, hp]

/-- `Phase10Transition` commutes with a change of the dead fields. -/
lemma phase10_update (s t : AgentState L K) (b b' : Bias L) (h h' : Fin (L + 1))
    (m m' : Fin (K * (L + 1) + 1)) (c c' : Fin (50 * (L + 1) + 1)) :
    Phase10Transition L K { s with bias := b, hour := h, minute := m, counter := c }
        { t with bias := b', hour := h', minute := m', counter := c' } =
      ({ (Phase10Transition L K s t).1 with bias := b, hour := h, minute := m, counter := c },
       { (Phase10Transition L K s t).2 with
          bias := b', hour := h', minute := m', counter := c' }) := by
  simp only [Phase10Transition]
  split_ifs <;> rfl

lemma phase10_phase_fst (s t : AgentState L K) :
    (Phase10Transition L K s t).1.phase = s.phase := by
  simp only [Phase10Transition]
  split_ifs <;> rfl

lemma phase10_phase_snd (s t : AgentState L K) :
    (Phase10Transition L K s t).2.phase = t.phase := by
  simp only [Phase10Transition]
  split_ifs <;> rfl

/-- Phase 10 respects the live table (nothing is live) and preserves the invariant. -/
theorem phase10_normalize (s t : AgentState L K) (hs : s.phase.val = 10) (ht : t.phase.val = 10)
    (hgs : Good s) (hgt : Good t) :
    normalize (Phase10Transition L K s t).1 =
        normalize (Phase10Transition L K (normalize s) (normalize t)).1 ∧
      normalize (Phase10Transition L K s t).2 =
        normalize (Phase10Transition L K (normalize s) (normalize t)).2 ∧
      Good (Phase10Transition L K s t).1 ∧ Good (Phase10Transition L K s t).2 := by
  have hp1 : (Phase10Transition L K s t).1.phase.val = 10 := by
    rw [phase10_phase_fst]; exact hs
  have hp2 : (Phase10Transition L K s t).2.phase.val = 10 := by
    rw [phase10_phase_snd]; exact ht
  rw [phase10_normalize_eq s hs, phase10_normalize_eq t ht,
    phase10_update s t .zero .zero hourDefault hourDefault minuteDefault minuteDefault
      counterDefault counterDefault]
  exact ⟨(phase10_normalize_update _ hp1 _ _ _ _).symm,
    (phase10_normalize_update _ hp2 _ _ _ _).symm,
    good_of_phase_ne_three _ (by omega), good_of_phase_ne_three _ (by omega)⟩

end Compact

end Ripple.PopulationProtocol.ExactMajority
