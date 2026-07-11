/-
Phase monotonicity for the ExactMajority transition function.

This file isolates the top-level `Transition_phase_monotone` theorem from
`Analysis.Invariants` so phase convergence files can use it without importing
the full invariants development.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Protocol.Transition

namespace ExactMajority

variable {L K : ℕ}

/-!
The base helpers `phaseInit_phase_nondec` and
`Phase0Transition_phase_nondec` through `Phase10Transition_phase_nondec` are
provided by `Protocol.Transition`.
-/

set_option linter.flexible false in
lemma runInitsBetween_phase_nondec (oldP newP : ℕ) (a : AgentState L K) :
    a.phase.val ≤ (runInitsBetween L K oldP newP a).phase.val := by
  unfold runInitsBetween
  let lst := (List.range 11).filter (fun k => oldP < k ∧ k ≤ newP)
  have h_ind : ∀ (a' : AgentState L K), a'.phase.val ≤
      (lst.foldl (fun (acc : AgentState L K) (k : ℕ) =>
        if h : k < 11 then phaseInit L K ⟨k, h⟩ acc else acc) a').phase.val := by
    induction lst with
    | nil => exact fun a' => le_refl _
    | cons k l IH =>
      intro a'
      simp [List.foldl]
      by_cases hk : k < 11
      · simp [hk]
        have h1 : a'.phase.val ≤ (phaseInit L K ⟨k, hk⟩ a').phase.val :=
          phaseInit_phase_nondec L K ⟨k, hk⟩ a'
        have h2 : (phaseInit L K ⟨k, hk⟩ a').phase.val ≤
          (l.foldl (fun (acc : AgentState L K) (k : ℕ) =>
            if h : k < 11 then phaseInit L K ⟨k, h⟩ acc else acc)
            (phaseInit L K ⟨k, hk⟩ a')).phase.val :=
          IH (phaseInit L K ⟨k, hk⟩ a')
        exact le_trans h1 h2
      · simp [hk]; exact IH a'
  exact h_ind a

lemma phaseEpidemicUpdate_phase_nondec (s t : AgentState L K) :
    s.phase.val ≤ (phaseEpidemicUpdate L K s t).1.phase.val ∧
    t.phase.val ≤ (phaseEpidemicUpdate L K s t).2.phase.val := by
  unfold phaseEpidemicUpdate
  dsimp
  set p := max s.phase t.phase with hp
  have hp_s : s.phase.val ≤ p.val := Nat.le_max_left _ _
  have hp_t : t.phase.val ≤ p.val := Nat.le_max_right _ _
  have h_s' :
      s.phase.val ≤ (runInitsBetween L K s.phase.val p.val ({ s with phase := p })).phase.val := by
    calc
      s.phase.val ≤ p.val := hp_s
      _ = ({ s with phase := p }).phase.val := by simp
      _ ≤ (runInitsBetween L K s.phase.val p.val ({ s with phase := p })).phase.val :=
        runInitsBetween_phase_nondec _ _ _
  have h_t' :
      t.phase.val ≤ (runInitsBetween L K t.phase.val p.val ({ t with phase := p })).phase.val := by
    calc
      t.phase.val ≤ p.val := hp_t
      _ = ({ t with phase := p }).phase.val := by simp
      _ ≤ (runInitsBetween L K t.phase.val p.val ({ t with phase := p })).phase.val :=
        runInitsBetween_phase_nondec _ _ _
  generalize hs0 :
      runInitsBetween L K s.phase.val p.val ({ s with phase := p }) = s0
  generalize ht0 :
      runInitsBetween L K t.phase.val p.val ({ t with phase := p }) = t0
  have hs0_ge : s.phase.val ≤ s0.phase.val := by
    simpa [hs0] using h_s'
  have ht0_ge : t.phase.val ≤ t0.phase.val := by
    simpa [ht0] using h_t'
  by_cases h10 :
      (s.phase.val < 10 ∨ t.phase.val < 10) ∧
        (s0.phase.val = 10 ∨ t0.phase.val = 10)
  · constructor
    · by_cases hs_phase : s.phase.val = 10
      · by_cases ht_lt : t.phase.val < 10
        · simpa [h10, hs_phase, ht_lt] using hs0_ge
        · simpa [h10, hs_phase, ht_lt] using hs0_ge
      · by_cases hs_lt : s.phase.val < 10
        · simp [h10, hs_phase, hs_lt, phase10]
          omega
        · have hbad : s.phase.val = 10 := by
            have := s.phase.2
            omega
          exact False.elim (hs_phase hbad)
    · by_cases ht_phase : t.phase.val = 10
      · by_cases hs_lt : s.phase.val < 10
        · simpa [h10, ht_phase, hs_lt] using ht0_ge
        · simpa [h10, ht_phase, hs_lt] using ht0_ge
      · by_cases ht_lt : t.phase.val < 10
        · simp [h10, ht_phase, ht_lt, phase10]
          omega
        · have hbad : t.phase.val = 10 := by
            have := t.phase.2
            omega
          exact False.elim (ht_phase hbad)
  · simp [h10, hs0_ge, ht0_ge]

set_option maxHeartbeats 2000000 in
-- The top-level dispatcher proof unfolds all phase cases and composes the
-- per-phase monotonicity lemmas, which exceeds the default tactic heartbeat.
/-- Top-level phase monotonicity. -/
theorem Transition_phase_monotone (s t : AgentState L K) :
    let (s', t') := Transition L K s t
    s.phase.val ≤ s'.phase.val ∧ t.phase.val ≤ t'.phase.val := by
  simp only []
  rcases phaseEpidemicUpdate_phase_nondec (L := L) (K := K) s t with ⟨h_ep_s, h_ep_t⟩
  unfold Transition
  rcases hpe : phaseEpidemicUpdate L K s t with ⟨s', t'⟩
  simp only [hpe] at h_ep_s h_ep_t ⊢
  let out :=
    match s'.phase with
    | ⟨0, _⟩ => Phase0Transition L K s' t'
    | ⟨1, _⟩ => Phase1Transition L K s' t'
    | ⟨2, _⟩ => Phase2Transition L K s' t'
    | ⟨3, _⟩ => Phase3Transition L K s' t'
    | ⟨4, _⟩ => Phase4Transition L K s' t'
    | ⟨5, _⟩ => Phase5Transition L K s' t'
    | ⟨6, _⟩ => Phase6Transition L K s' t'
    | ⟨7, _⟩ => Phase7Transition L K s' t'
    | ⟨8, _⟩ => Phase8Transition L K s' t'
    | ⟨9, _⟩ => Phase9Transition L K s' t'
    | ⟨10, _⟩ => Phase10Transition L K s' t'
    | _ => (s', t')
  change s.phase.val ≤ (finishPhase10Entry L K s' out.1).phase.val ∧
    t.phase.val ≤ (finishPhase10Entry L K t' out.2).phase.val
  have hdispatch : s'.phase.val ≤ out.1.phase.val ∧ t'.phase.val ≤ out.2.phase.val := by
    dsimp [out]
    rcases h_phase : s'.phase with ⟨n, hn⟩
    match n, hn with
    | 0, _ =>
      simpa [h_phase] using Phase0Transition_phase_nondec L K s' t'
    | 1, _ =>
      simpa [h_phase] using Phase1Transition_phase_nondec L K s' t'
    | 2, _ =>
      simpa [h_phase] using Phase2Transition_phase_nondec L K s' t'
    | 3, _ =>
      simpa [h_phase] using Phase3Transition_phase_nondec L K s' t'
    | 4, _ =>
      simpa [h_phase] using Phase4Transition_phase_nondec L K s' t'
    | 5, _ =>
      simpa [h_phase] using Phase5Transition_phase_nondec L K s' t'
    | 6, _ =>
      simpa [h_phase] using Phase6Transition_phase_nondec L K s' t'
    | 7, _ =>
      simpa [h_phase] using Phase7Transition_phase_nondec L K s' t'
    | 8, _ =>
      simpa [h_phase] using Phase8Transition_phase_nondec L K s' t'
    | 9, _ =>
      simpa [h_phase] using Phase9Transition_phase_nondec L K s' t'
    | 10, _ =>
      simpa [h_phase] using Phase10Transition_phase_nondec L K s' t'
    | n + 11, hn => omega
  exact ⟨le_trans h_ep_s (by simpa using hdispatch.1),
    le_trans h_ep_t (by simpa using hdispatch.2)⟩

end ExactMajority
