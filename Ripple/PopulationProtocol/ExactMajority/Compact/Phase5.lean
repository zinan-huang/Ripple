/-
# Phase 5 respects the live table

`Phase5Transition`: a Reserve whose `hour` is still `L` (the unset sample) copies the exponent
of a biased Main's `bias` into `hour`; Clocks run the standard counter subroutine. Live fields
at phase 5: Main `bias`, Reserve `hour`, Clock `counter`.
-/

import Ripple.PopulationProtocol.ExactMajority.Compact.Inits

namespace Ripple.PopulationProtocol.ExactMajority

namespace Compact

variable {L K : ℕ}

/-- The normal form keeps a live bias. -/
lemma phase5_normalize_bias_of_live (a : AgentState L K) (h : liveBias a.phase.val a.role) :
    (normalize a).bias = a.bias := by
  simp [normalize, normalizeAtVal, h]

/-- The normal form keeps a live hour. -/
lemma phase5_normalize_hour_of_live (a : AgentState L K)
    (h : liveHour a.phase.val a.role (a.bias = .zero)) :
    (normalize a).hour = a.hour := by
  simp [normalize, normalizeAtVal, h]

/-- The counter of a phase-5 Clock is live. -/
lemma phase5_liveCounter (a : AgentState L K) (ha : a.phase.val = 5) (hc : a.role = .clock) :
    liveCounter a.phase.val a.role (a.minute.val = K * (L + 1)) := by
  simp [liveCounter, ha, hc]

/-- The final Clock step of the transition respects the live table (any phase, given that the
counter is live when the agent is a Clock). -/
lemma phase5_clock_step (a : AgentState L K) (hg : Good a)
    (hlive : a.role = .clock → liveCounter a.phase.val a.role (a.minute.val = K * (L + 1))) :
    normalize (if a.role = .clock then stdCounterSubroutine L K a else a) =
        normalize (if (normalize a).role = .clock then stdCounterSubroutine L K (normalize a)
          else normalize a) ∧
      Good (if a.role = .clock then stdCounterSubroutine L K a else a) := by
  by_cases hc : a.role = .clock
  · have hc' : (normalize a).role = .clock := by rw [normalize_role]; exact hc
    rw [if_pos hc, if_pos hc']
    exact stdCounterSubroutine_normalize a hc hg (hlive hc)
  · have hc' : ¬ (normalize a).role = .clock := by rw [normalize_role]; exact hc
    rw [if_neg hc, if_neg hc']
    exact ⟨(normalize_normalize a).symm, hg⟩

/-- Writing the sample into a phase-5 Reserve: the result's normal form does not depend on the
dead fields. -/
lemma phase5_normalize_reserve_hour (r : AgentState L K) (hr : r.phase.val = 5)
    (hrr : r.role = .reserve) (e : Fin (L + 1)) :
    normalize { r with hour := e } = normalize { normalize r with hour := e } := by
  rcases r with ⟨i, o, ph, ro, g, b, sb, h, m, f, op, c⟩
  simp only at hr hrr
  subst hrr
  first
    | (simp [normalize, normalizeAtVal, liveBias, liveHour, liveMinute, liveCounter, hr]; done)
    | (simp [normalize, normalizeAtVal, liveBias, liveHour, liveMinute, liveCounter, hr] <;>
        split_ifs <;> simp_all)
    | (simp [normalize, normalizeAtVal, liveBias, liveHour, liveMinute, liveCounter, hr] <;>
        simp_all)

/-- The sampling rule, Reserve `r` from Main `m`, followed by the Clock step. -/
lemma phase5_sample_step (r m : AgentState L K) (hr : r.phase.val = 5) (hm : m.phase.val = 5)
    (hrr : r.role = .reserve) (hmm : m.role = .main) (hgm : Good m) (e : Fin (L + 1)) :
    normalize (if ({ r with hour := e } : AgentState L K).role = .clock then
          stdCounterSubroutine L K { r with hour := e } else { r with hour := e }) =
        normalize (if ({ normalize r with hour := e } : AgentState L K).role = .clock then
          stdCounterSubroutine L K { normalize r with hour := e }
          else { normalize r with hour := e }) ∧
      normalize (if m.role = .clock then stdCounterSubroutine L K m else m) =
        normalize (if (normalize m).role = .clock then stdCounterSubroutine L K (normalize m)
          else normalize m) ∧
      Good (if ({ r with hour := e } : AgentState L K).role = .clock then
          stdCounterSubroutine L K { r with hour := e } else { r with hour := e }) ∧
      Good (if m.role = .clock then stdCounterSubroutine L K m else m) := by
  have h1 : ¬ ({ r with hour := e } : AgentState L K).role = .clock := by
    show ¬ r.role = .clock
    simp [hrr]
  have h1' : ¬ ({ normalize r with hour := e } : AgentState L K).role = .clock := by
    show ¬ (normalize r).role = .clock
    simp [hrr]
  have hmc : ¬ m.role = .clock := by simp [hmm]
  have km := phase5_clock_step m hgm (fun hc => absurd hc hmc)
  rw [if_neg h1, if_neg h1']
  exact ⟨phase5_normalize_reserve_hour r hr hrr e, km.1,
    good_of_phase_ne_three _ (by show r.phase.val ≠ 3; omega), km.2⟩

/-- At phase 5 the transition reads Main `bias`, Reserve `hour` and Clock `counter` only. -/
theorem phase5_normalize (s t : AgentState L K) (hs : s.phase.val = 5) (ht : t.phase.val = 5)
    (hgs : Good s) (hgt : Good t) :
    normalize (Phase5Transition L K s t).1 =
        normalize (Phase5Transition L K (normalize s) (normalize t)).1 ∧
      normalize (Phase5Transition L K s t).2 =
        normalize (Phase5Transition L K (normalize s) (normalize t)).2 ∧
      Good (Phase5Transition L K s t).1 ∧ Good (Phase5Transition L K s t).2 := by
  have hls : s.role = .clock → liveCounter s.phase.val s.role (s.minute.val = K * (L + 1)) :=
    phase5_liveCounter s hs
  have hlt : t.role = .clock → liveCounter t.phase.val t.role (t.minute.val = K * (L + 1)) :=
    phase5_liveCounter t ht
  have ks := phase5_clock_step s hgs hls
  have kt := phase5_clock_step t hgt hlt
  by_cases h1 : s.role = .reserve ∧ t.role = .main ∧ (t.bias ≠ .zero)
  · have ⟨hsr, htm, htb⟩ := h1
    have hbt : (normalize t).bias = t.bias :=
      phase5_normalize_bias_of_live t (by simp [liveBias, ht, htm])
    have hhs : (normalize s).hour = s.hour :=
      phase5_normalize_hour_of_live s (by simp [liveHour, hs, hsr])
    have h1' : (normalize s).role = .reserve ∧ (normalize t).role = .main ∧
        ((normalize t).bias ≠ .zero) := by
      rw [normalize_role, normalize_role, hbt]; exact h1
    simp only [Phase5Transition]
    simp only [if_pos h1, if_pos h1']
    simp only [hbt, hhs]
    by_cases hL : s.hour.val = L
    · simp only [if_pos hL]
      exact phase5_sample_step s t hs ht hsr htm hgt (exponentOf L t.bias)
    · simp only [if_neg hL]
      exact ⟨ks.1, kt.1, ks.2, kt.2⟩
  · by_cases h2 : t.role = .reserve ∧ s.role = .main ∧ (s.bias ≠ .zero)
    · have ⟨htr, hsm, hsb⟩ := h2
      have hbs : (normalize s).bias = s.bias :=
        phase5_normalize_bias_of_live s (by simp [liveBias, hs, hsm])
      have hht : (normalize t).hour = t.hour :=
        phase5_normalize_hour_of_live t (by simp [liveHour, ht, htr])
      have h1' : ¬ ((normalize s).role = .reserve ∧ (normalize t).role = .main ∧
          ((normalize t).bias ≠ .zero)) := by
        rintro ⟨a, _, _⟩
        rw [normalize_role, hsm] at a
        exact absurd a (by decide)
      have h2' : (normalize t).role = .reserve ∧ (normalize s).role = .main ∧
          ((normalize s).bias ≠ .zero) := by
        rw [normalize_role, normalize_role, hbs]; exact h2
      simp only [Phase5Transition]
      simp only [if_neg h1, if_pos h2, if_neg h1', if_pos h2']
      simp only [hbs, hht]
      by_cases hL : t.hour.val = L
      · simp only [if_pos hL]
        have key := phase5_sample_step t s ht hs htr hsm hgs (exponentOf L s.bias)
        exact ⟨key.2.1, key.1, key.2.2.2, key.2.2.1⟩
      · simp only [if_neg hL]
        exact ⟨ks.1, kt.1, ks.2, kt.2⟩
    · have h1' : ¬ ((normalize s).role = .reserve ∧ (normalize t).role = .main ∧
          ((normalize t).bias ≠ .zero)) := by
        rintro ⟨a, b, c⟩
        rw [normalize_role] at a b
        rw [phase5_normalize_bias_of_live t (by simp [liveBias, ht, b])] at c
        exact h1 ⟨a, b, c⟩
      have h2' : ¬ ((normalize t).role = .reserve ∧ (normalize s).role = .main ∧
          ((normalize s).bias ≠ .zero)) := by
        rintro ⟨a, b, c⟩
        rw [normalize_role] at a b
        rw [phase5_normalize_bias_of_live s (by simp [liveBias, hs, b])] at c
        exact h2 ⟨a, b, c⟩
      simp only [Phase5Transition]
      simp only [if_neg h1, if_neg h2, if_neg h1', if_neg h2']
      exact ⟨ks.1, kt.1, ks.2, kt.2⟩

end Compact

end Ripple.PopulationProtocol.ExactMajority
