/-
# Phase 8 respects the live table

At phase 8 a Main keeps `bias`, a Clock keeps `counter`, every other role keeps nothing.
`absorbConsume` reads the biases and the `O(1)` flag `full` of two Mains and writes only
those fields, so it commutes with a change of the three dead fields of a Main
(`absorbConsume_update`); the Clock counter is `stdCounterSubroutine_normalize`.
-/

import Ripple.PopulationProtocol.ExactMajority.Compact.Inits

namespace Ripple.PopulationProtocol.ExactMajority

namespace Compact

variable {L K : ℕ}

/-- At phases 7 and 8 the normal form of a Main keeps the bias and resets the rest. -/
lemma phase8_normalize_main (a : AgentState L K) (hp : a.phase.val = 7 ∨ a.phase.val = 8)
    (hr : a.role = .main) :
    normalize a = { a with
      hour := hourDefault, minute := minuteDefault, counter := counterDefault } := by
  rcases a with ⟨i, o, ph, r, g, b, sb, h, m, f, op, c⟩
  simp only at hp hr
  subst hr
  rcases hp with hp | hp <;>
    simp [normalize, normalizeAtVal, liveBias, liveHour, liveMinute, liveCounter, hp]

/-- At phases 7 and 8 the normal form of a Main does not see `hour`, `minute`, `counter`. -/
lemma phase8_normalize_main_update (a : AgentState L K)
    (hp : a.phase.val = 7 ∨ a.phase.val = 8) (hr : a.role = .main)
    (h : Fin (L + 1)) (m : Fin (K * (L + 1) + 1)) (c : Fin (50 * (L + 1) + 1)) :
    normalize { a with hour := h, minute := m, counter := c } = normalize a := by
  rcases a with ⟨i, o, ph, r, g, b, sb, h₀, m₀, f, op, c₀⟩
  simp only at hp hr
  subst hr
  rcases hp with hp | hp <;>
    simp [normalize, normalizeAtVal, liveBias, liveHour, liveMinute, liveCounter, hp]

/-- The per-agent clock rule of the timed phases 7 and 8. -/
lemma phase8_timed_single (a : AgentState L K) (hp : a.phase.val = 7 ∨ a.phase.val = 8)
    (hg : Good a) :
    normalize (if a.role = .clock then stdCounterSubroutine L K a else a) =
        normalize (if a.role = .clock then stdCounterSubroutine L K (normalize a)
          else normalize a) ∧
      Good (if a.role = .clock then stdCounterSubroutine L K a else a) := by
  by_cases hc : a.role = .clock
  · simp only [if_pos hc]
    exact stdCounterSubroutine_normalize a hc hg
      (by rcases hp with hp | hp <;> simp [liveCounter, hp, hc])
  · simp only [if_neg hc]
    exact ⟨(normalize_normalize a).symm, hg⟩

/-- `absorbConsume` commutes with a change of `hour`, `minute`, `counter`. -/
lemma absorbConsume_update (s t : AgentState L K) (h h' : Fin (L + 1))
    (m m' : Fin (K * (L + 1) + 1)) (c c' : Fin (50 * (L + 1) + 1)) :
    absorbConsume L K { s with hour := h, minute := m, counter := c }
        { t with hour := h', minute := m', counter := c' } =
      ({ (absorbConsume L K s t).1 with hour := h, minute := m, counter := c },
       { (absorbConsume L K s t).2 with hour := h', minute := m', counter := c' }) := by
  rcases s with ⟨i, o, ph, r, g, b, sb, h₀, m₀, f, op, c₀⟩
  rcases t with ⟨i', o', ph', r', g', b', sb', h₀', m₀', f', op', c₀'⟩
  rcases b with _ | ⟨sg, k⟩ <;> rcases b' with _ | ⟨sg', k'⟩ <;>
    (try cases sg) <;> (try cases sg') <;> simp only [absorbConsume] <;>
    (try split_ifs) <;> rfl

lemma absorbConsume_phase_fst (s t : AgentState L K) :
    (absorbConsume L K s t).1.phase = s.phase := by
  rcases s with ⟨i, o, ph, r, g, b, sb, h, m, f, op, c⟩
  rcases t with ⟨i', o', ph', r', g', b', sb', h', m', f', op', c'⟩
  rcases b with _ | ⟨sg, k⟩ <;> rcases b' with _ | ⟨sg', k'⟩ <;>
    (try cases sg) <;> (try cases sg') <;> simp only [absorbConsume] <;>
    (try split_ifs) <;> rfl

lemma absorbConsume_phase_snd (s t : AgentState L K) :
    (absorbConsume L K s t).2.phase = t.phase := by
  rcases s with ⟨i, o, ph, r, g, b, sb, h, m, f, op, c⟩
  rcases t with ⟨i', o', ph', r', g', b', sb', h', m', f', op', c'⟩
  rcases b with _ | ⟨sg, k⟩ <;> rcases b' with _ | ⟨sg', k'⟩ <;>
    (try cases sg) <;> (try cases sg') <;> simp only [absorbConsume] <;>
    (try split_ifs) <;> rfl

/-- The Main–Main rule of phase 8. -/
lemma phase8_absorb (s t : AgentState L K) (hs : s.phase.val = 8) (ht : t.phase.val = 8)
    (hsm : s.role = .main) (htm : t.role = .main) :
    normalize (absorbConsume L K s t).1 =
        normalize (absorbConsume L K (normalize s) (normalize t)).1 ∧
      normalize (absorbConsume L K s t).2 =
        normalize (absorbConsume L K (normalize s) (normalize t)).2 ∧
      Good (absorbConsume L K s t).1 ∧ Good (absorbConsume L K s t).2 := by
  have hp1 : (absorbConsume L K s t).1.phase.val = 8 := by
    rw [absorbConsume_phase_fst]; exact hs
  have hp2 : (absorbConsume L K s t).2.phase.val = 8 := by
    rw [absorbConsume_phase_snd]; exact ht
  have hr1 : (absorbConsume L K s t).1.role = .main := by
    rw [absorbConsume_role_fst]; exact hsm
  have hr2 : (absorbConsume L K s t).2.role = .main := by
    rw [absorbConsume_role_snd]; exact htm
  rw [phase8_normalize_main s (Or.inr hs) hsm, phase8_normalize_main t (Or.inr ht) htm,
    absorbConsume_update s t hourDefault hourDefault minuteDefault minuteDefault
      counterDefault counterDefault]
  exact ⟨(phase8_normalize_main_update _ (Or.inr hp1) hr1 _ _ _).symm,
    (phase8_normalize_main_update _ (Or.inr hp2) hr2 _ _ _).symm,
    good_of_phase_ne_three _ (by omega), good_of_phase_ne_three _ (by omega)⟩

/-- Phase 8 respects the live table (Main: bias; Clock: counter) and preserves the
invariant. -/
theorem phase8_normalize (s t : AgentState L K) (hs : s.phase.val = 8) (ht : t.phase.val = 8)
    (hgs : Good s) (hgt : Good t) :
    normalize (Phase8Transition L K s t).1 =
        normalize (Phase8Transition L K (normalize s) (normalize t)).1 ∧
      normalize (Phase8Transition L K s t).2 =
        normalize (Phase8Transition L K (normalize s) (normalize t)).2 ∧
      Good (Phase8Transition L K s t).1 ∧ Good (Phase8Transition L K s t).2 := by
  simp only [Phase8Transition, normalize_role]
  by_cases hmm : s.role = .main ∧ t.role = .main
  · have h1 : ¬ (absorbConsume L K s t).1.role = .clock := by simp [hmm.1]
    have h2 : ¬ (absorbConsume L K s t).2.role = .clock := by simp [hmm.2]
    have h1' : ¬ (absorbConsume L K (normalize s) (normalize t)).1.role = .clock := by
      simp [hmm.1]
    have h2' : ¬ (absorbConsume L K (normalize s) (normalize t)).2.role = .clock := by
      simp [hmm.2]
    simp only [if_pos hmm, if_neg h1, if_neg h2, if_neg h1', if_neg h2']
    exact phase8_absorb s t hs ht hmm.1 hmm.2
  · simp only [if_neg hmm]
    exact ⟨(phase8_timed_single s (Or.inr hs) hgs).1, (phase8_timed_single t (Or.inr ht) hgt).1,
      (phase8_timed_single s (Or.inr hs) hgs).2, (phase8_timed_single t (Or.inr ht) hgt).2⟩

end Compact

end Ripple.PopulationProtocol.ExactMajority
