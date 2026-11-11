/-
# Phase 6 respects the live table

`Phase6Transition`: a Reserve whose sample (`hour`) is set and below a biased Main's exponent
splits with it (`doSplit`: the Reserve becomes a Main carrying half of the Main's bias); Clocks
run the standard counter subroutine. Live fields at phase 6: Main `bias`, Reserve `hour`,
Clock `counter`.
-/

import Ripple.PopulationProtocol.ExactMajority.Compact.Inits

namespace Ripple.PopulationProtocol.ExactMajority

namespace Compact

variable {L K : ℕ}

/-- The normal form keeps a live bias. -/
lemma phase6_normalize_bias_of_live (a : AgentState L K) (h : liveBias a.phase.val a.role) :
    (normalize a).bias = a.bias := by
  simp [normalize, normalizeAtVal, h]

/-- The normal form keeps a live hour. -/
lemma phase6_normalize_hour_of_live (a : AgentState L K)
    (h : liveHour a.phase.val a.role (a.bias = .zero)) :
    (normalize a).hour = a.hour := by
  simp [normalize, normalizeAtVal, h]

/-- The counter of a phase-6 Clock is live. -/
lemma phase6_liveCounter (a : AgentState L K) (ha : a.phase.val = 6) (hc : a.role = .clock) :
    liveCounter a.phase.val a.role (a.minute.val = K * (L + 1)) := by
  simp [liveCounter, ha, hc]

/-- The final Clock step of the transition respects the live table (any phase, given that the
counter is live when the agent is a Clock). -/
lemma phase6_clock_step (a : AgentState L K) (hg : Good a)
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

/-- A phase-6 Reserve turned into a Main with bias `b`: its `hour` becomes dead, so the normal
form does not depend on the dead fields of the Reserve. -/
lemma phase6_normalize_reserve_to_main (r : AgentState L K) (hr : r.phase.val = 6)
    (hrr : r.role = .reserve) (b : Bias L) :
    normalize { r with role := .main, bias := b } =
      normalize { normalize r with role := .main, bias := b } := by
  rcases r with ⟨i, o, ph, ro, g, b₀, sb, h, m, f, op, c⟩
  simp only at hr hrr
  subst hrr
  first
    | (simp [normalize, normalizeAtVal, liveBias, liveHour, liveMinute, liveCounter, hr]; done)
    | (simp [normalize, normalizeAtVal, liveBias, liveHour, liveMinute, liveCounter, hr] <;>
        split_ifs <;> simp_all)
    | (simp [normalize, normalizeAtVal, liveBias, liveHour, liveMinute, liveCounter, hr] <;>
        simp_all)

/-- A phase-6 Main with a new bias `b`. -/
lemma phase6_normalize_main_bias (a : AgentState L K) (ha : a.phase.val = 6)
    (hm : a.role = .main) (b : Bias L) :
    normalize { a with bias := b } = normalize { normalize a with bias := b } := by
  rcases a with ⟨i, o, ph, ro, g, b₀, sb, h, m, f, op, c⟩
  simp only at ha hm
  subst hm
  first
    | (simp [normalize, normalizeAtVal, liveBias, liveHour, liveMinute, liveCounter, ha]; done)
    | (simp [normalize, normalizeAtVal, liveBias, liveHour, liveMinute, liveCounter, ha] <;>
        split_ifs <;> simp_all)
    | (simp [normalize, normalizeAtVal, liveBias, liveHour, liveMinute, liveCounter, ha] <;>
        simp_all)

/-- `doSplit` on a Main with bias `dyadic sgn j`, written as nested `if`s. -/
lemma phase6_doSplit_eq (r m : AgentState L K) (sgn : Sign) (j : Fin (L + 1))
    (hb : m.bias = .dyadic sgn j) :
    doSplit L K r m =
      if r.hour.val ≠ L ∧ r.hour.val > j.val then
        if h : j.val < L then
          ({ r with role := .main, bias := .dyadic sgn ⟨j.val + 1, by omega⟩ },
           { m with bias := .dyadic sgn ⟨j.val + 1, by omega⟩ })
        else (r, m)
      else (r, m) := by
  first
    | (unfold doSplit; simp only [hb]; done)
    | (unfold doSplit; simp only [hb]; rfl)
    | (unfold doSplit; rw [hb]; done)
    | (unfold doSplit; rw [hb]; rfl)
    | (simp [doSplit, hb]; done)
    | (unfold doSplit; split <;> simp_all)

/-- The split rule, Reserve `r` with Main `m`, both results followed by the Clock step. -/
lemma phase6_split_step (r m : AgentState L K) (hr : r.phase.val = 6) (hm : m.phase.val = 6)
    (hrr : r.role = .reserve) (hmm : m.role = .main) (b : Bias L) :
    normalize (if ({ r with role := .main, bias := b } : AgentState L K).role = .clock then
          stdCounterSubroutine L K { r with role := .main, bias := b }
          else { r with role := .main, bias := b }) =
        normalize (if ({ normalize r with role := .main, bias := b } : AgentState L K).role =
            .clock then
          stdCounterSubroutine L K { normalize r with role := .main, bias := b }
          else { normalize r with role := .main, bias := b }) ∧
      normalize (if ({ m with bias := b } : AgentState L K).role = .clock then
          stdCounterSubroutine L K { m with bias := b } else { m with bias := b }) =
        normalize (if ({ normalize m with bias := b } : AgentState L K).role = .clock then
          stdCounterSubroutine L K { normalize m with bias := b }
          else { normalize m with bias := b }) ∧
      Good (if ({ r with role := .main, bias := b } : AgentState L K).role = .clock then
          stdCounterSubroutine L K { r with role := .main, bias := b }
          else { r with role := .main, bias := b }) ∧
      Good (if ({ m with bias := b } : AgentState L K).role = .clock then
          stdCounterSubroutine L K { m with bias := b } else { m with bias := b }) := by
  have h1 : ¬ ({ r with role := .main, bias := b } : AgentState L K).role = .clock := by
    show ¬ Role.main = .clock
    decide
  have h1' : ¬ ({ normalize r with role := .main, bias := b } : AgentState L K).role =
      .clock := by
    show ¬ Role.main = .clock
    decide
  have h2 : ¬ ({ m with bias := b } : AgentState L K).role = .clock := by
    show ¬ m.role = .clock
    simp [hmm]
  have h2' : ¬ ({ normalize m with bias := b } : AgentState L K).role = .clock := by
    show ¬ (normalize m).role = .clock
    simp [hmm]
  rw [if_neg h1, if_neg h1', if_neg h2, if_neg h2']
  exact ⟨phase6_normalize_reserve_to_main r hr hrr b, phase6_normalize_main_bias m hm hmm b,
    good_of_phase_ne_three _ (by show r.phase.val ≠ 3; omega),
    good_of_phase_ne_three _ (by show m.phase.val ≠ 3; omega)⟩

/-- At phase 6 the transition reads Main `bias`, Reserve `hour` and Clock `counter` only. -/
theorem phase6_normalize (s t : AgentState L K) (hs : s.phase.val = 6) (ht : t.phase.val = 6)
    (hgs : Good s) (hgt : Good t) :
    normalize (Phase6Transition L K s t).1 =
        normalize (Phase6Transition L K (normalize s) (normalize t)).1 ∧
      normalize (Phase6Transition L K s t).2 =
        normalize (Phase6Transition L K (normalize s) (normalize t)).2 ∧
      Good (Phase6Transition L K s t).1 ∧ Good (Phase6Transition L K s t).2 := by
  have hls : s.role = .clock → liveCounter s.phase.val s.role (s.minute.val = K * (L + 1)) :=
    phase6_liveCounter s hs
  have hlt : t.role = .clock → liveCounter t.phase.val t.role (t.minute.val = K * (L + 1)) :=
    phase6_liveCounter t ht
  have ks := phase6_clock_step s hgs hls
  have kt := phase6_clock_step t hgt hlt
  by_cases h1 : s.role = .reserve ∧ t.role = .main ∧ (t.bias ≠ .zero)
  · have ⟨hsr, htm, htb⟩ := h1
    have hbt : (normalize t).bias = t.bias :=
      phase6_normalize_bias_of_live t (by simp [liveBias, ht, htm])
    have hhs : (normalize s).hour = s.hour :=
      phase6_normalize_hour_of_live s (by simp [liveHour, hs, hsr])
    have h1' : (normalize s).role = .reserve ∧ (normalize t).role = .main ∧
        ((normalize t).bias ≠ .zero) := by
      rw [normalize_role, normalize_role, hbt]; exact h1
    obtain ⟨sgn, j, hb⟩ : ∃ sgn j, t.bias = Bias.dyadic sgn j := by
      cases h : t.bias with
      | zero => exact absurd h htb
      | dyadic sg i => exact ⟨sg, i, by simp [h]⟩
    simp only [Phase6Transition]
    simp only [if_pos h1, if_pos h1']
    rw [phase6_doSplit_eq s t sgn j hb, phase6_doSplit_eq (normalize s) (normalize t) sgn j
      (hbt.trans hb)]
    by_cases hg : s.hour.val ≠ L ∧ s.hour.val > j.val
    · have hg' : (normalize s).hour.val ≠ L ∧ (normalize s).hour.val > j.val := by
        rw [hhs]; exact hg
      by_cases hj : j.val < L
      · simp only [if_pos hg, if_pos hg', dif_pos hj]
        exact phase6_split_step s t hs ht hsr htm (Bias.dyadic sgn ⟨j.val + 1, by omega⟩)
      · simp only [if_pos hg, if_pos hg', dif_neg hj]
        exact ⟨ks.1, kt.1, ks.2, kt.2⟩
    · have hg' : ¬ ((normalize s).hour.val ≠ L ∧ (normalize s).hour.val > j.val) := by
        rw [hhs]; exact hg
      simp only [if_neg hg, if_neg hg']
      exact ⟨ks.1, kt.1, ks.2, kt.2⟩
  · by_cases h2 : t.role = .reserve ∧ s.role = .main ∧ (s.bias ≠ .zero)
    · have ⟨htr, hsm, hsb⟩ := h2
      have hbs : (normalize s).bias = s.bias :=
        phase6_normalize_bias_of_live s (by simp [liveBias, hs, hsm])
      have hht : (normalize t).hour = t.hour :=
        phase6_normalize_hour_of_live t (by simp [liveHour, ht, htr])
      have h1' : ¬ ((normalize s).role = .reserve ∧ (normalize t).role = .main ∧
          ((normalize t).bias ≠ .zero)) := by
        rintro ⟨a, _, _⟩
        rw [normalize_role, hsm] at a
        exact absurd a (by decide)
      have h2' : (normalize t).role = .reserve ∧ (normalize s).role = .main ∧
          ((normalize s).bias ≠ .zero) := by
        rw [normalize_role, normalize_role, hbs]; exact h2
      obtain ⟨sgn, j, hb⟩ : ∃ sgn j, s.bias = Bias.dyadic sgn j := by
        cases h : s.bias with
        | zero => exact absurd h hsb
        | dyadic sg i => exact ⟨sg, i, by simp [h]⟩
      simp only [Phase6Transition]
      simp only [if_neg h1, if_pos h2, if_neg h1', if_pos h2']
      rw [phase6_doSplit_eq t s sgn j hb, phase6_doSplit_eq (normalize t) (normalize s) sgn j
        (hbs.trans hb)]
      by_cases hg : t.hour.val ≠ L ∧ t.hour.val > j.val
      · have hg' : (normalize t).hour.val ≠ L ∧ (normalize t).hour.val > j.val := by
          rw [hht]; exact hg
        by_cases hj : j.val < L
        · simp only [if_pos hg, if_pos hg', dif_pos hj]
          have key := phase6_split_step t s ht hs htr hsm
            (Bias.dyadic sgn ⟨j.val + 1, by omega⟩)
          exact ⟨key.2.1, key.1, key.2.2.2, key.2.2.1⟩
        · simp only [if_pos hg, if_pos hg', dif_neg hj]
          exact ⟨ks.1, kt.1, ks.2, kt.2⟩
      · have hg' : ¬ ((normalize t).hour.val ≠ L ∧ (normalize t).hour.val > j.val) := by
          rw [hht]; exact hg
        simp only [if_neg hg, if_neg hg']
        exact ⟨ks.1, kt.1, ks.2, kt.2⟩
    · have h1' : ¬ ((normalize s).role = .reserve ∧ (normalize t).role = .main ∧
          ((normalize t).bias ≠ .zero)) := by
        rintro ⟨a, b, c⟩
        rw [normalize_role] at a b
        rw [phase6_normalize_bias_of_live t (by simp [liveBias, ht, b])] at c
        exact h1 ⟨a, b, c⟩
      have h2' : ¬ ((normalize t).role = .reserve ∧ (normalize s).role = .main ∧
          ((normalize s).bias ≠ .zero)) := by
        rintro ⟨a, b, c⟩
        rw [normalize_role] at a b
        rw [phase6_normalize_bias_of_live s (by simp [liveBias, hs, b])] at c
        exact h2 ⟨a, b, c⟩
      simp only [Phase6Transition]
      simp only [if_neg h1, if_neg h2, if_neg h1', if_neg h2']
      exact ⟨ks.1, kt.1, ks.2, kt.2⟩

end Compact

end Ripple.PopulationProtocol.ExactMajority
