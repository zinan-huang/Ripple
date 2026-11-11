/-
# The Init chain respects the live table

`phaseEpidemicUpdate` sets an agent's phase to the pair maximum and then runs the Init blocks of
every phase in between (`runInitsBetween`). This file shows that the chain reads only live
fields: two agents with the same normal form at phase `j` have the same normal form at phase
`j + m` after the Inits `j+1, …, j+m`, and the phase-3 Clock invariant `GoodAt` is established
by the phase-3 Init. The same step gives the congruence for `advancePhaseWithInit` and
`stdCounterSubroutine` (timed-phase counters) and for `enterPhase10`.
-/

import Ripple.PopulationProtocol.ExactMajority.Compact.Live

namespace Ripple.PopulationProtocol.ExactMajority

namespace Compact

variable {L K : ℕ}

/-! ### One Init step, phase by phase -/

/-- The common statement of the ten Init steps: from phase index `j` to `k = j + 1`. -/
def InitStep (j k : Fin 11) : Prop :=
  ∀ (x x' : AgentState L K), normalizeAt j x = normalizeAt j x' → GoodAt j x → GoodAt j x' →
    normalizeAt k (phaseInit L K k x) = normalizeAt k (phaseInit L K k x') ∧
      GoodAt k (phaseInit L K k x) ∧
      ((phaseInit L K k x).phase = x.phase ∨ (phaseInit L K k x).phase.val = 10)

/-- Destructure both agents and the normal-form hypothesis; every Init step then is a case
split on the role. -/
local macro "init_step_tac" : tactic => `(tactic| (
  intro x x' h hg hg'
  rcases x with ⟨i, o, ph, r, g, b, sb, hr, m, f, op, c⟩
  rcases x' with ⟨i', o', ph', r', g', b', sb', hr', m', f', op', c'⟩
  simp only [normalizeAt, normalizeAtVal, AgentState.mk.injEq] at h
  obtain ⟨e1, e2, e3, e4, e5, hb, e6, hh, hm, e7, e8, hc⟩ := h
  subst e1 e2 e3 e4 e5 e6 e7 e8
  simp only [GoodAt, GoodAtVal] at hg hg' ⊢
  cases r <;>
    simp [phaseInit, enterPhase10, normalizeAt, normalizeAtVal, liveBias, liveHour, liveMinute,
      liveCounter, phase10, counterDefault, hourDefault, minuteDefault] at hb hh hm hc hg hg' ⊢ <;>
    (try split_ifs) <;> simp_all <;> (try omega)))

theorem initStep_one : InitStep (L := L) (K := K) 0 1 := by init_step_tac
theorem initStep_two : InitStep (L := L) (K := K) 1 2 := by init_step_tac
theorem initStep_three : InitStep (L := L) (K := K) 2 3 := by init_step_tac
theorem initStep_four : InitStep (L := L) (K := K) 3 4 := by init_step_tac
theorem initStep_five : InitStep (L := L) (K := K) 4 5 := by init_step_tac
theorem initStep_six : InitStep (L := L) (K := K) 5 6 := by init_step_tac
theorem initStep_seven : InitStep (L := L) (K := K) 6 7 := by init_step_tac
theorem initStep_eight : InitStep (L := L) (K := K) 7 8 := by init_step_tac
theorem initStep_nine : InitStep (L := L) (K := K) 8 9 := by init_step_tac
theorem initStep_ten : InitStep (L := L) (K := K) 9 10 := by init_step_tac

/-- One Init step: from phase index `j` to `j + 1`. -/
theorem init_step (j k : Fin 11) (hjk : j.val + 1 = k.val) : InitStep (L := L) (K := K) j k := by
  rcases j with ⟨j, hj⟩
  rcases k with ⟨k, hk⟩
  simp only at hjk
  obtain rfl : k = j + 1 := by omega
  have hj' : j < 10 := by omega
  interval_cases j
  · exact initStep_one
  · exact initStep_two
  · exact initStep_three
  · exact initStep_four
  · exact initStep_five
  · exact initStep_six
  · exact initStep_seven
  · exact initStep_eight
  · exact initStep_nine
  · exact initStep_ten

/-! ### The chain -/

/-- The Init chain over a list of phase indices (the fold of `runInitsBetween`). -/
def initFold (lst : List ℕ) (x : AgentState L K) : AgentState L K :=
  lst.foldl (fun acc k => if h : k < 11 then phaseInit L K ⟨k, h⟩ acc else acc) x

@[simp] lemma initFold_nil (x : AgentState L K) : initFold [] x = x := rfl

lemma initFold_cons (k : ℕ) (lst : List ℕ) (x : AgentState L K) :
    initFold (k :: lst) x = initFold lst (if h : k < 11 then phaseInit L K ⟨k, h⟩ x else x) := rfl

lemma runInitsBetween_eq_initFold (p q : ℕ) (x : AgentState L K) :
    runInitsBetween L K p q x =
      initFold ((List.range 11).filter (fun k => decide (p < k ∧ k ≤ q))) x := rfl

/-- The Init chain from phase index `j` over `m` further phases respects the live table. -/
theorem initFold_range'_normalize (m : ℕ) :
    ∀ (j : ℕ), j + m ≤ 10 → ∀ (x x' : AgentState L K),
      normalizeAtVal j x = normalizeAtVal j x' → GoodAtVal j x → GoodAtVal j x' →
      normalizeAtVal (j + m) (initFold (List.range' (j + 1) m) x) =
          normalizeAtVal (j + m) (initFold (List.range' (j + 1) m) x') ∧
        GoodAtVal (j + m) (initFold (List.range' (j + 1) m) x) ∧
        ((initFold (List.range' (j + 1) m) x).phase = x.phase ∨
          (initFold (List.range' (j + 1) m) x).phase.val = 10) := by
  induction m with
  | zero =>
    intro j _ x x' h hg hg'
    simp only [List.range'_zero, initFold_nil, Nat.add_zero]
    exact ⟨h, hg, by simp⟩
  | succ m ih =>
    intro j hjm x x' h hg hg'
    have hk : j + 1 < 11 := by omega
    rw [List.range'_succ, initFold_cons, initFold_cons, dif_pos hk, dif_pos hk,
      show j + (m + 1) = j + 1 + m by omega]
    have hstep := init_step (L := L) (K := K) ⟨j, by omega⟩ ⟨j + 1, hk⟩ rfl x x' h hg hg'
    have hstep' := init_step (L := L) (K := K) ⟨j, by omega⟩ ⟨j + 1, hk⟩ rfl x' x h.symm hg' hg
    have hrec := ih (j + 1) (by omega) (phaseInit L K ⟨j + 1, hk⟩ x) (phaseInit L K ⟨j + 1, hk⟩ x')
      hstep.1 hstep.2.1 hstep'.2.1
    refine ⟨hrec.1, hrec.2.1, ?_⟩
    rcases hrec.2.2 with h1 | h1
    · rcases hstep.2.2 with h2 | h2
      · exact Or.inl (h1.trans h2)
      · exact Or.inr (by rw [h1]; exact h2)
    · exact Or.inr h1

/-- The filter in `runInitsBetween` is the interval `p+1, …, q`. -/
lemma filter_range_eq_range' :
    ∀ (p q : Fin 11), p ≤ q →
      (List.range 11).filter (fun k => decide (p.val < k ∧ k ≤ q.val)) =
        List.range' (p.val + 1) (q.val - p.val) := by
  decide

/-- `runInitsBetween` respects the live table: from phase `p` to phase `q` (`p ≤ q ≤ 10`). -/
theorem runInitsBetween_normalize (p q : ℕ) (hpq : p ≤ q) (hq : q ≤ 10)
    (x x' : AgentState L K)
    (h : normalizeAtVal p x = normalizeAtVal p x') (hg : GoodAtVal p x) (hg' : GoodAtVal p x') :
    normalizeAtVal q (runInitsBetween L K p q x) = normalizeAtVal q (runInitsBetween L K p q x') ∧
      GoodAtVal q (runInitsBetween L K p q x) ∧
      ((runInitsBetween L K p q x).phase = x.phase ∨
        (runInitsBetween L K p q x).phase.val = 10) := by
  have hfilt : (List.range 11).filter (fun k => decide (p < k ∧ k ≤ q)) =
      List.range' (p + 1) (q - p) := by
    have := filter_range_eq_range' ⟨p, by omega⟩ ⟨q, by omega⟩ (by simpa [Fin.le_def] using hpq)
    simpa using this
  have hchain := initFold_range'_normalize (L := L) (K := K) (q - p) p (by omega) x x' h hg hg'
  rw [runInitsBetween_eq_initFold, runInitsBetween_eq_initFold, hfilt]
  rwa [show p + (q - p) = q by omega] at hchain

/-! ### Entry into phase 10 -/

/-- `enterPhase10` reads only `input`; its result is at phase 10 where every big field is dead. -/
theorem enterPhase10_normalize (y y' : AgentState L K) (h : normalize y = normalize y') :
    normalize (enterPhase10 L K y) = normalize (enterPhase10 L K y') := by
  have hin : y.input = y'.input := by
    have := congrArg AgentState.input h; simpa using this
  have hrole : y.role = y'.role := by
    have := congrArg AgentState.role h; simpa using this
  have hasg : y.assigned = y'.assigned := by
    have := congrArg AgentState.assigned h; simpa using this
  have hsb : y.smallBias = y'.smallBias := by
    have := congrArg AgentState.smallBias h; simpa using this
  have hop : y.opinions = y'.opinions := by
    have := congrArg AgentState.opinions h; simpa using this
  unfold normalize
  rw [enterPhase10_phase_val, enterPhase10_phase_val]
  exact normalizeAtVal_ten_eq _ _ (by simp [hin]) (by simp [hin]) (by simp [enterPhase10])
    (by simp [hrole]) (by simp [hasg]) (by simp [hsb]) (by simp) (by simp [hop])

theorem good_enterPhase10 (y : AgentState L K) : Good (enterPhase10 L K y) :=
  good_of_phase_ne_three _ (by simp)

/-! ### Setting the phase field -/

/-- `normalizeAtVal` at a fixed index ignores the phase field: the normal form of `a` with its
phase set to `q` equals the normal form of `normalize a` with its phase set to `q`. -/
lemma normalizeAtVal_set_phase_normalize (a : AgentState L K) (q : Fin 11) :
    normalizeAtVal a.phase.val { a with phase := q } =
      normalizeAtVal a.phase.val { normalize a with phase := q } := by
  change ({ normalizeAtVal a.phase.val a with phase := q } : AgentState L K) =
    { normalizeAtVal a.phase.val (normalizeAtVal a.phase.val a) with phase := q }
  rw [normalizeAtVal_normalizeAtVal]

lemma goodAtVal_set_phase (j : ℕ) (x : AgentState L K) (q : Fin 11) :
    GoodAtVal j { x with phase := q } ↔ GoodAtVal j x := Iff.rfl

lemma advancePhase_eq_of_lt (x : AgentState L K) (hlt : x.phase.val < 10) :
    advancePhase L K x =
      { x with phase := ⟨x.phase.val.succ, by have := x.phase.2; omega⟩ } := by
  unfold advancePhase
  rw [dif_pos hlt]

lemma advancePhase_eq_of_not_lt (x : AgentState L K) (hlt : ¬ x.phase.val < 10) :
    advancePhase L K x = x := by
  unfold advancePhase
  rw [dif_neg hlt]

/-- `advancePhaseWithInit` respects the live table on good agents. -/
theorem advancePhaseWithInit_normalize (x : AgentState L K) (hg : Good x) :
    normalize (advancePhaseWithInit L K x) =
        normalize (advancePhaseWithInit L K (normalize x)) ∧
      Good (advancePhaseWithInit L K x) := by
  unfold advancePhaseWithInit
  by_cases hlt : x.phase.val < 10
  · have hlt' : (normalize x).phase.val < 10 := by simpa using hlt
    rw [advancePhase_eq_of_lt x hlt, advancePhase_eq_of_lt (normalize x) hlt']
    simp only [normalize_phase]
    have hq : (⟨x.phase.val.succ, by have := x.phase.2; omega⟩ : Fin 11).val = x.phase.val + 1 :=
      rfl
    set q : Fin 11 := ⟨x.phase.val.succ, by have := x.phase.2; omega⟩ with hqdef
    have hx : normalizeAt x.phase { x with phase := q } =
        normalizeAt x.phase { normalize x with phase := q } :=
      normalizeAtVal_set_phase_normalize x q
    have hstep := init_step (L := L) (K := K) x.phase q (by rw [hq]) _ _ hx
      ((goodAtVal_set_phase _ _ _).mpr hg) ((goodAtVal_set_phase _ _ _).mpr (good_normalize x))
    refine ⟨?_, ?_⟩
    · apply normalize_eq_of_normalizeAt_eq q _ _ hstep.1
      rcases hstep.2.2 with h1 | h1
      · left; rw [h1]
      · right; exact h1
    · rcases hstep.2.2 with h1 | h1
      · have h2 := hstep.2.1
        simp only [GoodAt] at h2
        unfold Good
        rw [h1]
        exact h2
      · exact good_of_phase_ne_three _ (by rw [h1]; omega)
  · have hlt' : ¬ (normalize x).phase.val < 10 := by simpa using hlt
    rw [advancePhase_eq_of_not_lt x hlt, advancePhase_eq_of_not_lt (normalize x) hlt']
    have h10 : x.phase.val = 10 := by have := x.phase.2; omega
    have hph : x.phase = phase10 := Fin.ext (by simp [phase10, h10])
    have hinit : ∀ y : AgentState L K, y.phase = phase10 →
        phaseInit L K y.phase y = enterPhase10 L K y := by
      intro y hy
      rw [hy]
      simp [phaseInit, phase10]
    have hinit' : phaseInit L K (normalize x).phase (normalize x) =
        enterPhase10 L K (normalize x) :=
      hinit (normalize x) (by simpa using hph)
    rw [hinit x hph, hinit']
    exact ⟨enterPhase10_normalize _ _ (normalize_normalize x).symm, good_enterPhase10 _⟩

/-- `stdCounterSubroutine` respects the live table on a Clock whose counter is live. -/
theorem stdCounterSubroutine_normalize (x : AgentState L K) (hc : x.role = .clock) (hg : Good x)
    (hlive : liveCounter x.phase.val x.role (x.minute.val = K * (L + 1))) :
    normalize (stdCounterSubroutine L K x) =
        normalize (stdCounterSubroutine L K (normalize x)) ∧
      Good (stdCounterSubroutine L K x) := by
  have hcnt : (normalize x).counter = x.counter := by
    simp [normalize, normalizeAtVal, hlive]
  unfold stdCounterSubroutine
  by_cases h0 : x.counter.val = 0
  · simp only [hcnt, h0, dite_true]
    exact advancePhaseWithInit_normalize x hg
  · simp only [hcnt, h0, dite_false]
    refine ⟨?_, ?_⟩
    · rcases x with ⟨i, o, ph, r, g, b, sb, hr, m, f, op, c⟩
      simp only at hc
      subst hc
      simp only [normalize, normalizeAtVal, liveBias, liveHour, liveMinute, liveCounter] at hlive ⊢
      simp only [AgentState.mk.injEq, true_and]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> split_ifs <;> simp_all
    · intro h3 _
      try simp only at h3 ⊢
      refine ⟨bias_eq_zero_of_good x hg h3 hc, ?_⟩
      intro hm
      try simp only at hm
      exfalso
      simp [liveCounter, hc, h3] at hlive
      omega

/-! ### The phase epidemic -/

/-- The phase epidemic respects the live table and preserves the invariant; both agents leave
it in the same phase. -/
theorem phaseEpidemicUpdate_normalize (s t : AgentState L K) (hgs : Good s) (hgt : Good t) :
    normalize (phaseEpidemicUpdate L K s t).1 =
        normalize (phaseEpidemicUpdate L K (normalize s) (normalize t)).1 ∧
      normalize (phaseEpidemicUpdate L K s t).2 =
        normalize (phaseEpidemicUpdate L K (normalize s) (normalize t)).2 ∧
      Good (phaseEpidemicUpdate L K s t).1 ∧ Good (phaseEpidemicUpdate L K s t).2 ∧
      (phaseEpidemicUpdate L K s t).1.phase = (phaseEpidemicUpdate L K s t).2.phase := by
  -- the two chains
  have chain : ∀ (a : AgentState L K) (q : Fin 11), Good a → a.phase ≤ q →
      normalize (runInitsBetween L K a.phase.val q.val { a with phase := q }) =
          normalize (runInitsBetween L K a.phase.val q.val { normalize a with phase := q }) ∧
        Good (runInitsBetween L K a.phase.val q.val { a with phase := q }) ∧
        ((runInitsBetween L K a.phase.val q.val { a with phase := q }).phase.val = q.val ∨
          (runInitsBetween L K a.phase.val q.val { a with phase := q }).phase.val = 10) := by
    intro a q hga haq
    have hr := runInitsBetween_normalize (L := L) (K := K) a.phase.val q.val haq
      (by have := q.2; omega) _ _ (normalizeAtVal_set_phase_normalize a q)
      ((goodAtVal_set_phase _ _ _).mpr hga)
      ((goodAtVal_set_phase _ _ _).mpr (good_normalize a))
    have hph : (runInitsBetween L K a.phase.val q.val { a with phase := q }).phase.val = q.val ∨
        (runInitsBetween L K a.phase.val q.val { a with phase := q }).phase.val = 10 := by
      rcases hr.2.2 with h1 | h1
      · left; rw [h1]
      · right; exact h1
    refine ⟨?_, ?_, hph⟩
    · exact normalize_eq_of_normalizeAt_eq ⟨q.val, q.2⟩ _ _ hr.1 hph
    · rcases hph with h1 | h1
      · have h2 := hr.2.1
        unfold Good
        rw [h1]
        exact h2
      · exact good_of_phase_ne_three _ (by rw [h1]; omega)
  have cs := chain s (max s.phase t.phase) hgs (le_max_left _ _)
  have ct := chain t (max s.phase t.phase) hgt (le_max_right _ _)
  simp only [phaseEpidemicUpdate, normalize_phase]
  generalize hS : runInitsBetween L K s.phase.val (max s.phase t.phase).val
    { s with phase := max s.phase t.phase } = S at cs ⊢
  generalize hS' : runInitsBetween L K s.phase.val (max s.phase t.phase).val
    { normalize s with phase := max s.phase t.phase } = S' at cs ⊢
  generalize hT : runInitsBetween L K t.phase.val (max s.phase t.phase).val
    { t with phase := max s.phase t.phase } = T at ct ⊢
  generalize hT' : runInitsBetween L K t.phase.val (max s.phase t.phase).val
    { normalize t with phase := max s.phase t.phase } = T' at ct ⊢
  have hSph : S'.phase = S.phase := by
    have := congrArg AgentState.phase cs.1; simpa using this.symm
  have hTph : T'.phase = T.phase := by
    have := congrArg AgentState.phase ct.1; simpa using this.symm
  rw [hSph, hTph]
  have hqs : s.phase.val ≤ (max s.phase t.phase).val := Fin.le_def.mp (le_max_left _ _)
  have hqt : t.phase.val ≤ (max s.phase t.phase).val := Fin.le_def.mp (le_max_right _ _)
  have hqmax : (max s.phase t.phase).val = s.phase.val ∨
      (max s.phase t.phase).val = t.phase.val := by
    rcases le_total s.phase t.phase with h | h
    · right; rw [max_eq_right h]
    · left; rw [max_eq_left h]
  have hSv := cs.2.2
  have hTv := ct.2.2
  have h10 : ∀ y : AgentState L K, y.phase.val ≤ 10 := fun y => by have := y.phase.2; omega
  have h10s := h10 s
  have h10t := h10 t
  split_ifs with hcond
  · simp only [phase10EpidemicEntry, normalize_phase]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · split_ifs
      · exact enterPhase10_normalize _ _ cs.1
      · exact cs.1
    · split_ifs
      · exact enterPhase10_normalize _ _ ct.1
      · exact ct.1
    · split_ifs
      · exact good_enterPhase10 _
      · exact cs.2.1
    · split_ifs
      · exact good_enterPhase10 _
      · exact ct.2.1
    · apply Fin.ext
      by_cases h1 : s.phase.val < 10 <;> by_cases h2 : t.phase.val < 10 <;>
        simp only [h1, h2, if_true, if_false, enterPhase10_phase_val] <;> omega
  · refine ⟨cs.1, ct.1, cs.2.1, ct.2.1, ?_⟩
    apply Fin.ext
    dsimp only
    omega

end Compact

end Ripple.PopulationProtocol.ExactMajority
