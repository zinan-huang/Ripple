/-
# Phase 7 respects the live table

At phase 7 a Main keeps `bias`, a Clock keeps `counter`, every other role keeps nothing.
`cancelSplit` reads the biases of two Mains and writes only their biases, so it commutes
with a change of the three dead fields of a Main (`cancelSplit_update`); the Clock counter
is `stdCounterSubroutine_normalize`.
-/

import Ripple.PopulationProtocol.ExactMajority.Compact.Inits

namespace Ripple.PopulationProtocol.ExactMajority

namespace Compact

variable {L K : ℕ}

/-- At phases 7 and 8 the normal form of a Main keeps the bias and resets the rest. -/
lemma phase7_normalize_main (a : AgentState L K) (hp : a.phase.val = 7 ∨ a.phase.val = 8)
    (hr : a.role = .main) :
    normalize a = { a with
      hour := hourDefault, minute := minuteDefault, counter := counterDefault } := by
  rcases a with ⟨i, o, ph, r, g, b, sb, h, m, f, op, c⟩
  simp only at hp hr
  subst hr
  rcases hp with hp | hp <;>
    simp [normalize, normalizeAtVal, liveBias, liveHour, liveMinute, liveCounter, hp]

/-- At phases 7 and 8 the normal form of a Main does not see `hour`, `minute`, `counter`. -/
lemma phase7_normalize_main_update (a : AgentState L K)
    (hp : a.phase.val = 7 ∨ a.phase.val = 8) (hr : a.role = .main)
    (h : Fin (L + 1)) (m : Fin (K * (L + 1) + 1)) (c : Fin (50 * (L + 1) + 1)) :
    normalize { a with hour := h, minute := m, counter := c } = normalize a := by
  rcases a with ⟨i, o, ph, r, g, b, sb, h₀, m₀, f, op, c₀⟩
  simp only at hp hr
  subst hr
  rcases hp with hp | hp <;>
    simp [normalize, normalizeAtVal, liveBias, liveHour, liveMinute, liveCounter, hp]

/-- The per-agent clock rule of the timed phases 7 and 8. -/
lemma phase7_timed_single (a : AgentState L K) (hp : a.phase.val = 7 ∨ a.phase.val = 8)
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

/-- `cancelSplit` commutes with a change of `hour`, `minute`, `counter`. -/
lemma cancelSplit_update (s t : AgentState L K) (h h' : Fin (L + 1))
    (m m' : Fin (K * (L + 1) + 1)) (c c' : Fin (50 * (L + 1) + 1)) :
    cancelSplit L K { s with hour := h, minute := m, counter := c }
        { t with hour := h', minute := m', counter := c' } =
      ({ (cancelSplit L K s t).1 with hour := h, minute := m, counter := c },
       { (cancelSplit L K s t).2 with hour := h', minute := m', counter := c' }) := by
  rcases s with ⟨i, o, ph, r, g, b, sb, h₀, m₀, f, op, c₀⟩
  rcases t with ⟨i', o', ph', r', g', b', sb', h₀', m₀', f', op', c₀'⟩
  cases b <;> cases b' <;> simp only [cancelSplit] <;> (try split_ifs) <;> rfl

lemma cancelSplit_phase_fst (s t : AgentState L K) :
    (cancelSplit L K s t).1.phase = s.phase := by
  rcases s with ⟨i, o, ph, r, g, b, sb, h, m, f, op, c⟩
  rcases t with ⟨i', o', ph', r', g', b', sb', h', m', f', op', c'⟩
  cases b <;> cases b' <;> simp only [cancelSplit] <;> (try split_ifs) <;> rfl

lemma cancelSplit_phase_snd (s t : AgentState L K) :
    (cancelSplit L K s t).2.phase = t.phase := by
  rcases s with ⟨i, o, ph, r, g, b, sb, h, m, f, op, c⟩
  rcases t with ⟨i', o', ph', r', g', b', sb', h', m', f', op', c'⟩
  cases b <;> cases b' <;> simp only [cancelSplit] <;> (try split_ifs) <;> rfl

/-- The Main–Main rule of phase 7. -/
lemma phase7_cancel (s t : AgentState L K) (hs : s.phase.val = 7) (ht : t.phase.val = 7)
    (hsm : s.role = .main) (htm : t.role = .main) :
    normalize (cancelSplit L K s t).1 =
        normalize (cancelSplit L K (normalize s) (normalize t)).1 ∧
      normalize (cancelSplit L K s t).2 =
        normalize (cancelSplit L K (normalize s) (normalize t)).2 ∧
      Good (cancelSplit L K s t).1 ∧ Good (cancelSplit L K s t).2 := by
  have hp1 : (cancelSplit L K s t).1.phase.val = 7 := by rw [cancelSplit_phase_fst]; exact hs
  have hp2 : (cancelSplit L K s t).2.phase.val = 7 := by rw [cancelSplit_phase_snd]; exact ht
  have hr1 : (cancelSplit L K s t).1.role = .main := by rw [cancelSplit_role_fst]; exact hsm
  have hr2 : (cancelSplit L K s t).2.role = .main := by rw [cancelSplit_role_snd]; exact htm
  rw [phase7_normalize_main s (Or.inl hs) hsm, phase7_normalize_main t (Or.inl ht) htm,
    cancelSplit_update s t hourDefault hourDefault minuteDefault minuteDefault
      counterDefault counterDefault]
  exact ⟨(phase7_normalize_main_update _ (Or.inl hp1) hr1 _ _ _).symm,
    (phase7_normalize_main_update _ (Or.inl hp2) hr2 _ _ _).symm,
    good_of_phase_ne_three _ (by omega), good_of_phase_ne_three _ (by omega)⟩

/-- Phase 7 respects the live table (Main: bias; Clock: counter) and preserves the
invariant. -/
theorem phase7_normalize (s t : AgentState L K) (hs : s.phase.val = 7) (ht : t.phase.val = 7)
    (hgs : Good s) (hgt : Good t) :
    normalize (Phase7Transition L K s t).1 =
        normalize (Phase7Transition L K (normalize s) (normalize t)).1 ∧
      normalize (Phase7Transition L K s t).2 =
        normalize (Phase7Transition L K (normalize s) (normalize t)).2 ∧
      Good (Phase7Transition L K s t).1 ∧ Good (Phase7Transition L K s t).2 := by
  simp only [Phase7Transition, normalize_role]
  by_cases hmm : s.role = .main ∧ t.role = .main
  · have h1 : ¬ (cancelSplit L K s t).1.role = .clock := by simp [hmm.1]
    have h2 : ¬ (cancelSplit L K s t).2.role = .clock := by simp [hmm.2]
    have h1' : ¬ (cancelSplit L K (normalize s) (normalize t)).1.role = .clock := by
      simp [hmm.1]
    have h2' : ¬ (cancelSplit L K (normalize s) (normalize t)).2.role = .clock := by
      simp [hmm.2]
    simp only [if_pos hmm, if_neg h1, if_neg h2, if_neg h1', if_neg h2']
    exact phase7_cancel s t hs ht hmm.1 hmm.2
  · simp only [if_neg hmm]
    exact ⟨(phase7_timed_single s (Or.inl hs) hgs).1, (phase7_timed_single t (Or.inl ht) hgt).1,
      (phase7_timed_single s (Or.inl hs) hgs).2, (phase7_timed_single t (Or.inl ht) hgt).2⟩

end Compact

end Ripple.PopulationProtocol.ExactMajority
