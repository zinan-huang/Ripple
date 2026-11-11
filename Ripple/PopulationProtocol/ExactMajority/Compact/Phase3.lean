/-
# Phase 3 respects the live table

`Phase3Transition` reads only the fields that the live table of `Live.lean` keeps at phase 3:
a Clock's `minute`, and its `counter` once the minute is at its maximum; a Main's `bias`, and
its `hour` while the bias is zero; nothing of a Reserve, MCR or CR. On good agents the normal
form of the result depends only on the normal forms of the inputs, and `Good` is preserved.

The proof is one lemma per rule and role pair: Clock–Clock (minute epidemic, drip, counter
subroutine), Main–Clock and Clock–Main (hour drag), Main–Main (`phase3CancelSplit`), and the
pairs on which the transition does nothing.
-/

import Ripple.PopulationProtocol.ExactMajority.Compact.Inits

namespace Ripple.PopulationProtocol.ExactMajority

namespace Compact

variable {L K : ℕ}

/-! ### Normal forms at phase 3 -/

/-- A phase-3 Main keeps `bias`, keeps `hour` iff the bias is zero, and resets `minute` and
`counter`. -/
lemma normalize_main_three (a : AgentState L K) (hp : a.phase.val = 3) (hr : a.role = .main) :
    normalize a = { a with
      hour := if a.bias = .zero then a.hour else hourDefault
      minute := minuteDefault
      counter := counterDefault } := by
  rcases a with ⟨i, o, ph, r, g, b, sb, hh, m, f, op, c⟩
  simp only at hp hr
  subst hr
  simp [normalize, normalizeAtVal, liveBias, liveHour, liveMinute, liveCounter, hp]

/-- A good phase-3 Clock keeps everything but `hour`: its bias is already zero and its counter
is already the default while the minute is below the maximum. -/
lemma normalize_clock_three (a : AgentState L K) (hp : a.phase.val = 3) (hr : a.role = .clock)
    (hg : Good a) : normalize a = { a with hour := hourDefault } := by
  obtain ⟨hb, hc⟩ := hg hp hr
  have hcd : a.counter = counterDefault ∨ a.minute.val = K * (L + 1) := by
    by_cases hm : a.minute.val < K * (L + 1)
    · exact Or.inl (Fin.ext (by simp [counterDefault, hc hm]))
    · exact Or.inr (by have := a.minute.2; omega)
  rcases a with ⟨i, o, ph, r, g, b, sb, hh, m, f, op, c⟩
  simp only at hp hr hb hcd
  subst hr hb
  rcases hcd with hcd | hcd
  · subst hcd
    simp [normalize, normalizeAtVal, liveBias, liveHour, liveMinute, liveCounter, hp]
  · simp [normalize, normalizeAtVal, liveBias, liveHour, liveMinute, liveCounter, hp, hcd]

/-! ### The transition on each role pair -/

/-- Clock–Clock: only Rule 1 fires (minute epidemic, drip, or the counter subroutine). -/
lemma phase3_clock_clock_eq (s t : AgentState L K) (hs : s.role = .clock)
    (ht : t.role = .clock) :
    Phase3Transition L K s t =
      if s.minute ≠ t.minute then
        ({ s with minute := max s.minute t.minute }, { t with minute := max s.minute t.minute })
      else if h : s.minute.val < K * (L + 1) then
        ({ s with minute := ⟨s.minute.val + 1, by omega⟩ }, t)
      else (stdCounterSubroutine L K s, stdCounterSubroutine L K t) := by
  have hsc := stdCounterSubroutine_clock_role_eq L K s hs
  have htc := stdCounterSubroutine_clock_role_eq L K t ht
  unfold Phase3Transition
  simp [hs, ht]
  try (split_ifs <;> simp_all)

/-- Main–Clock: only the hour drag of Rule 2 fires, and only when the Main is unbiased. -/
lemma phase3_main_clock_eq (s t : AgentState L K) (hs : s.role = .main) (ht : t.role = .clock) :
    Phase3Transition L K s t =
      (if s.bias = .zero then
        { s with hour := ⟨max s.hour.val (min L (t.minute.val / K)),
            (Nat.max_lt).mpr ⟨s.hour.2, Nat.lt_succ_of_le (Nat.min_le_left _ _)⟩⟩ }
       else s, t) := by
  unfold Phase3Transition
  simp [hs, ht]
  try (split_ifs <;> simp_all)

/-- Clock–Main: the mirror image of `phase3_main_clock_eq`. -/
lemma phase3_clock_main_eq (s t : AgentState L K) (hs : s.role = .clock) (ht : t.role = .main) :
    Phase3Transition L K s t =
      (s, if t.bias = .zero then
        { t with hour := ⟨max t.hour.val (min L (s.minute.val / K)),
            (Nat.max_lt).mpr ⟨t.hour.2, Nat.lt_succ_of_le (Nat.min_le_left _ _)⟩⟩ }
       else t) := by
  unfold Phase3Transition
  simp [hs, ht]
  try (split_ifs <;> simp_all)

/-- Main–Main: only Rules 3 and 4 (`phase3CancelSplit`) fire. -/
lemma phase3_main_main_eq (s t : AgentState L K) (hs : s.role = .main) (ht : t.role = .main) :
    Phase3Transition L K s t = phase3CancelSplit L K s t := by
  unfold Phase3Transition
  simp [hs, ht]
  try (split_ifs <;> simp_all)

/-- A Reserve, MCR or CR on the left: nothing fires. -/
lemma phase3_eq_self_of_left (s t : AgentState L K)
    (hs : s.role = .reserve ∨ s.role = .mcr ∨ s.role = .cr) :
    Phase3Transition L K s t = (s, t) := by
  unfold Phase3Transition
  rcases hs with hs | hs | hs <;> simp [hs] <;> (try (split_ifs <;> simp_all))

/-- A Reserve, MCR or CR on the right: nothing fires. -/
lemma phase3_eq_self_of_right (s t : AgentState L K)
    (ht : t.role = .reserve ∨ t.role = .mcr ∨ t.role = .cr) :
    Phase3Transition L K s t = (s, t) := by
  unfold Phase3Transition
  rcases ht with ht | ht | ht <;> simp [ht] <;> (try (split_ifs <;> simp_all))

/-! ### Normal forms of the results, per role pair -/

/-- Clock–Clock: the minute epidemic and the drip read only `minute`; the counter subroutine
runs only with both minutes at the maximum, where `counter` is live. `Good` is preserved
because the minute never decreases. -/
lemma phase3_clock_clock_normalize (s t : AgentState L K) (hs3 : s.phase.val = 3)
    (ht3 : t.phase.val = 3) (hs : s.role = .clock) (ht : t.role = .clock)
    (hgs : Good s) (hgt : Good t) :
    normalize (Phase3Transition L K s t).1 =
        normalize (Phase3Transition L K (normalize s) (normalize t)).1 ∧
      normalize (Phase3Transition L K s t).2 =
        normalize (Phase3Transition L K (normalize s) (normalize t)).2 ∧
      Good (Phase3Transition L K s t).1 ∧ Good (Phase3Transition L K s t).2 := by
  have hns := normalize_clock_three s hs3 hs hgs
  have hnt := normalize_clock_three t ht3 ht hgt
  have hms : (normalize s).minute = s.minute := by rw [hns]
  have hmt : (normalize t).minute = t.minute := by rw [hnt]
  obtain ⟨hbs, hcs⟩ := hgs hs3 hs
  obtain ⟨hbt, hct⟩ := hgt ht3 ht
  have hsm := s.minute.2
  have htm := t.minute.2
  have hM1 : s.minute.val ≤ (max s.minute t.minute).val := le_max_left _ _
  have hM2 : t.minute.val ≤ (max s.minute t.minute).val := le_max_right _ _
  rw [phase3_clock_clock_eq s t hs ht,
    phase3_clock_clock_eq (normalize s) (normalize t) (by simp [hs]) (by simp [ht])]
  simp only [hms, hmt]
  split_ifs with hne hlt
  · -- minute epidemic
    simp only [hns, hnt]
    clear hns hnt hms hmt hgs hgt
    rcases s with ⟨i, o, ph, r, g, b, sb, hh, m, f, op, c⟩
    rcases t with ⟨i', o', ph', r', g', b', sb', hh', m', f', op', c'⟩
    simp only at *
    subst hs ht hbs hbt
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      simp [*, normalize, normalizeAtVal, liveBias, liveHour, liveMinute, liveCounter,
        Good, GoodAtVal] <;>
      omega
  · -- drip: only the left Clock changes, and only its minute
    refine ⟨?_, (normalize_normalize t).symm, ?_, hgt⟩
    all_goals
      try simp only [hns]
      rcases s with ⟨i, o, ph, r, g, b, sb, hh, m, f, op, c⟩
      simp only at *
      subst hs hbs
      simp [*, normalize, normalizeAtVal, liveBias, liveHour, liveMinute, liveCounter,
        Good, GoodAtVal]
      try omega
  · -- counter subroutine: both minutes at the maximum, so both counters are live
    have heq : s.minute = t.minute := by simpa using hne
    have hsmax : s.minute.val = K * (L + 1) := by omega
    have htmax : t.minute.val = K * (L + 1) := by rw [← heq]; exact hsmax
    have hlive_s : liveCounter s.phase.val s.role (s.minute.val = K * (L + 1)) := by
      rw [hs3, hs]
      unfold liveCounter
      exact ⟨rfl, Or.inr (Or.inr (Or.inl ⟨rfl, hsmax⟩))⟩
    have hlive_t : liveCounter t.phase.val t.role (t.minute.val = K * (L + 1)) := by
      rw [ht3, ht]
      unfold liveCounter
      exact ⟨rfl, Or.inr (Or.inr (Or.inl ⟨rfl, htmax⟩))⟩
    obtain ⟨h1, g1⟩ := stdCounterSubroutine_normalize s hs hgs hlive_s
    obtain ⟨h2, g2⟩ := stdCounterSubroutine_normalize t ht hgt hlive_t
    exact ⟨h1, h2, g1, g2⟩

/-- Main–Clock: the hour drag reads the Main's `bias`, its `hour` (only when the bias is zero)
and the Clock's `minute`; it writes the Main's `hour` while the bias stays zero. -/
lemma phase3_main_clock_normalize (s t : AgentState L K) (hs3 : s.phase.val = 3)
    (ht3 : t.phase.val = 3) (hs : s.role = .main) (ht : t.role = .clock)
    (hgs : Good s) (hgt : Good t) :
    normalize (Phase3Transition L K s t).1 =
        normalize (Phase3Transition L K (normalize s) (normalize t)).1 ∧
      normalize (Phase3Transition L K s t).2 =
        normalize (Phase3Transition L K (normalize s) (normalize t)).2 ∧
      Good (Phase3Transition L K s t).1 ∧ Good (Phase3Transition L K s t).2 := by
  rw [phase3_main_clock_eq s t hs ht,
    phase3_main_clock_eq (normalize s) (normalize t) (by simp [hs]) (by simp [ht])]
  refine ⟨?_, (normalize_normalize t).symm, ?_, hgt⟩
  · rw [normalize_main_three s hs3 hs, normalize_clock_three t ht3 ht hgt]
    clear hgs hgt
    rcases s with ⟨i, o, ph, r, g, b, sb, hh, m, f, op, c⟩
    rcases t with ⟨i', o', ph', r', g', b', sb', hh', m', f', op', c'⟩
    simp only at *
    subst hs ht
    cases b <;>
      simp [normalize, normalizeAtVal, liveBias, liveHour, liveMinute, liveCounter, hs3, ht3]
  · apply good_of_role_ne_clock
    split_ifs <;> simp [hs]

/-- Clock–Main: the mirror image of `phase3_main_clock_normalize`. -/
lemma phase3_clock_main_normalize (s t : AgentState L K) (hs3 : s.phase.val = 3)
    (ht3 : t.phase.val = 3) (hs : s.role = .clock) (ht : t.role = .main)
    (hgs : Good s) (hgt : Good t) :
    normalize (Phase3Transition L K s t).1 =
        normalize (Phase3Transition L K (normalize s) (normalize t)).1 ∧
      normalize (Phase3Transition L K s t).2 =
        normalize (Phase3Transition L K (normalize s) (normalize t)).2 ∧
      Good (Phase3Transition L K s t).1 ∧ Good (Phase3Transition L K s t).2 := by
  rw [phase3_clock_main_eq s t hs ht,
    phase3_clock_main_eq (normalize s) (normalize t) (by simp [hs]) (by simp [ht])]
  refine ⟨(normalize_normalize s).symm, ?_, hgs, ?_⟩
  · rw [normalize_clock_three s hs3 hs hgs, normalize_main_three t ht3 ht]
    clear hgs hgt
    rcases s with ⟨i, o, ph, r, g, b, sb, hh, m, f, op, c⟩
    rcases t with ⟨i', o', ph', r', g', b', sb', hh', m', f', op', c'⟩
    simp only at *
    subst hs ht
    cases b' <;>
      simp [normalize, normalizeAtVal, liveBias, liveHour, liveMinute, liveCounter, hs3, ht3]
  · apply good_of_role_ne_clock
    split_ifs <;> simp [ht]

/-- Main–Main: cancel and split read both biases and the hour of the unbiased partner; cancel
writes `hour` (live, since the bias becomes zero) and split kills the hour by making the bias
dyadic. -/
lemma phase3_main_main_normalize (s t : AgentState L K) (hs3 : s.phase.val = 3)
    (ht3 : t.phase.val = 3) (hs : s.role = .main) (ht : t.role = .main)
    (hgs : Good s) (hgt : Good t) :
    normalize (Phase3Transition L K s t).1 =
        normalize (Phase3Transition L K (normalize s) (normalize t)).1 ∧
      normalize (Phase3Transition L K s t).2 =
        normalize (Phase3Transition L K (normalize s) (normalize t)).2 ∧
      Good (Phase3Transition L K s t).1 ∧ Good (Phase3Transition L K s t).2 := by
  rw [phase3_main_main_eq s t hs ht,
    phase3_main_main_eq (normalize s) (normalize t) (by simp [hs]) (by simp [ht]),
    normalize_main_three s hs3 hs, normalize_main_three t ht3 ht]
  clear hgs hgt
  rcases s with ⟨i, o, ph, r, g, b, sb, hh, m, f, op, c⟩
  rcases t with ⟨i', o', ph', r', g', b', sb', hh', m', f', op', c'⟩
  simp only at *
  subst hs ht
  rcases b with _ | ⟨sg, bi⟩ <;> rcases b' with _ | ⟨sg', bi'⟩ <;> (try cases sg) <;>
    (try cases sg') <;>
    simp only [phase3CancelSplit, eq_self_iff_true, ite_true, reduceCtorEq, ite_false] <;>
    (try split_ifs) <;>
    simp_all [normalize, normalizeAtVal, liveBias, liveHour, liveMinute, liveCounter, Good,
      GoodAtVal]

/-- Any pair with a Reserve, MCR or CR: the transition is the identity. -/
lemma phase3_other_normalize (s t : AgentState L K) (hgs : Good s) (hgt : Good t)
    (hrole : (s.role = .reserve ∨ s.role = .mcr ∨ s.role = .cr) ∨
      (t.role = .reserve ∨ t.role = .mcr ∨ t.role = .cr)) :
    normalize (Phase3Transition L K s t).1 =
        normalize (Phase3Transition L K (normalize s) (normalize t)).1 ∧
      normalize (Phase3Transition L K s t).2 =
        normalize (Phase3Transition L K (normalize s) (normalize t)).2 ∧
      Good (Phase3Transition L K s t).1 ∧ Good (Phase3Transition L K s t).2 := by
  have h1 : Phase3Transition L K s t = (s, t) := by
    rcases hrole with h | h
    · exact phase3_eq_self_of_left s t h
    · exact phase3_eq_self_of_right s t h
  have h2 : Phase3Transition L K (normalize s) (normalize t) = (normalize s, normalize t) := by
    rcases hrole with h | h
    · exact phase3_eq_self_of_left _ _ (by simpa using h)
    · exact phase3_eq_self_of_right _ _ (by simpa using h)
  rw [h1, h2]
  exact ⟨(normalize_normalize s).symm, (normalize_normalize t).symm, hgs, hgt⟩

/-! ### Assembly -/

/-- **Phase 3 respects the live table.** On good phase-3 agents the normal form of
`Phase3Transition` depends only on the normal forms of the inputs, and `Good` is preserved. -/
theorem phase3_normalize (s t : AgentState L K) (hs : s.phase.val = 3) (ht : t.phase.val = 3)
    (hgs : Good s) (hgt : Good t) :
    normalize (Phase3Transition L K s t).1 =
        normalize (Phase3Transition L K (normalize s) (normalize t)).1 ∧
      normalize (Phase3Transition L K s t).2 =
        normalize (Phase3Transition L K (normalize s) (normalize t)).2 ∧
      Good (Phase3Transition L K s t).1 ∧ Good (Phase3Transition L K s t).2 := by
  cases hsr : s.role <;> cases htr : t.role
  all_goals first
    | exact phase3_main_main_normalize s t hs ht hsr htr hgs hgt
    | exact phase3_main_clock_normalize s t hs ht hsr htr hgs hgt
    | exact phase3_clock_main_normalize s t hs ht hsr htr hgs hgt
    | exact phase3_clock_clock_normalize s t hs ht hsr htr hgs hgt
    | exact phase3_other_normalize s t hgs hgt (Or.inl (Or.inl hsr))
    | exact phase3_other_normalize s t hgs hgt (Or.inl (Or.inr (Or.inl hsr)))
    | exact phase3_other_normalize s t hgs hgt (Or.inl (Or.inr (Or.inr hsr)))
    | exact phase3_other_normalize s t hgs hgt (Or.inr (Or.inl htr))
    | exact phase3_other_normalize s t hgs hgt (Or.inr (Or.inr (Or.inl htr)))
    | exact phase3_other_normalize s t hgs hgt (Or.inr (Or.inr (Or.inr htr)))

end Compact

end Ripple.PopulationProtocol.ExactMajority
