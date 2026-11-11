/-
# Phase 0 respects the live table

At phase 0 the only live `Θ(log n)` field is a Clock's `counter` (table in `Live.lean`).
Rules 1–4 of `Phase0Transition` read and write only `role`, `assigned`, `smallBias` (`O(1)`
fields, always kept by `normalize`); rule 4 writes the new Clock's `counter` explicitly; rule 5
runs `stdCounterSubroutine` on two Clocks, and only a pair of Clocks reaches it. The two-Clock
pair goes through `stdCounterSubroutine_normalize`; the other 24 role pairs are a finite
computation on the records.
-/

import Ripple.PopulationProtocol.ExactMajority.Compact.Inits

namespace Ripple.PopulationProtocol.ExactMajority

namespace Compact

variable {L K : ℕ}

/-- Two Clocks only run the counter subroutine (rules 1–4 need an MCR or a CR). -/
lemma Phase0Transition_clock_clock (s t : AgentState L K) (hs : s.role = .clock)
    (ht : t.role = .clock) :
    Phase0Transition L K s t = (stdCounterSubroutine L K s, stdCounterSubroutine L K t) := by
  simp [Phase0Transition, hs, ht]

/-- A Clock's counter is live at phase 0. -/
lemma liveCounter_zero_clock (a : AgentState L K) (hp : a.phase.val = 0)
    (hc : a.role = .clock) :
    liveCounter a.phase.val a.role (a.minute.val = K * (L + 1)) := by
  simp [liveCounter, hp, hc]

/-- Phase 0 reads only the live fields and preserves `Good`. -/
theorem phase0_normalize (s t : AgentState L K) (hs : s.phase.val = 0) (ht : t.phase.val = 0)
    (hgs : Good s) (hgt : Good t) :
    normalize (Phase0Transition L K s t).1 =
        normalize (Phase0Transition L K (normalize s) (normalize t)).1 ∧
      normalize (Phase0Transition L K s t).2 =
        normalize (Phase0Transition L K (normalize s) (normalize t)).2 ∧
      Good (Phase0Transition L K s t).1 ∧ Good (Phase0Transition L K s t).2 := by
  by_cases hcc : s.role = .clock ∧ t.role = .clock
  · rw [Phase0Transition_clock_clock s t hcc.1 hcc.2,
      Phase0Transition_clock_clock (normalize s) (normalize t)
        ((normalize_role s).trans hcc.1) ((normalize_role t).trans hcc.2)]
    obtain ⟨h₁, h₂⟩ := stdCounterSubroutine_normalize s hcc.1 hgs
      (liveCounter_zero_clock s hs hcc.1)
    obtain ⟨h₃, h₄⟩ := stdCounterSubroutine_normalize t hcc.2 hgt
      (liveCounter_zero_clock t ht hcc.2)
    exact ⟨h₁, h₃, h₂, h₄⟩
  · clear hgs hgt
    rcases s with ⟨i, o, ⟨ph, hph⟩, r, g, b, sb, h, m, f, op, c⟩
    rcases t with ⟨i', o', ⟨ph', hph'⟩, r', g', b', sb', h', m', f', op', c'⟩
    simp only [Fin.val_mk] at hs ht
    subst hs ht
    simp only at hcc
    cases r <;> cases r' <;> cases g <;> cases g' <;>
      simp [Phase0Transition, normalize, normalizeAtVal, liveBias, liveHour, liveMinute,
        liveCounter, Good, GoodAtVal] at hcc ⊢ <;>
      (try split_ifs) <;> simp_all

end Compact

end Ripple.PopulationProtocol.ExactMajority
