/-
Endpoint Repair: prove AllResettingUniformToInSswapResAnsPhiZero via the safe
ResAns-maintenance route (all_resetting_uniform_to_InSswap_ResAns).

Route: NOT ranking_field_proof (black box, doesn't track answers).
Instead: hRecruit (even: trivial, odd: counting) + hSelect (green).
-/

import Ripple.PopulationProtocol.Majority.SSEM.Convergence.BurmanConvergenceFinal

namespace SSEM

variable {n : ℕ}

/-! ### Execution ↔ runPairs conversion -/

/-- Lift an `execution`-form result into `∃ L, runPairs`-form.
Every deterministic execution `execution P C γ t` can be expressed as
`runPairs P C L` for `L = [γ 0, γ 1, ..., γ (t-1)]`. -/
theorem exists_runPairs_of_execution
    [Inhabited (Fin n × Fin n)]
    {Q X Y : Type*} (P : Protocol Q X Y)
    (C : Config Q X n) {Goal : Config Q X n → Prop}
    (γ : DetScheduler n) (t : ℕ) (h : Goal (execution P C γ t)) :
    ∃ L : List (Fin n × Fin n), Goal (runPairs P C L) := by
  suffices key : ∀ t' (C' : Config Q X n),
      execution P C' γ t' = runPairs P C' ((List.range t').map γ) by
    exact ⟨(List.range t).map γ, key t C ▸ h⟩
  intro t'
  induction t' with
  | zero => intro C'; rfl
  | succ t' ih =>
    intro C'
    simp only [execution, List.range_succ, List.map_append, List.map_cons,
      List.map_nil, runPairs_append, runPairs_cons, runPairs_nil, ih]

-- phase4_propagate unfolds deeply
set_option maxHeartbeats 800000 in
/-- `phase4_propagate` preserves ResAns: output answers ∈ {m₀, .phi} whenever
input answers are. Propagation only copies one input answer to the other side. -/
theorem phase4_propagate_preserves_ResAns_pair
    {Rmax : ℕ} {m₀ : Answer} {b₀ b₁ : AgentState n}
    (h₀ : AnswerInResAns m₀ b₀.answer)
    (h₁ : AnswerInResAns m₀ b₁.answer) :
    AnswerInResAns m₀ (phase4_propagate n Rmax b₀ b₁).1.answer ∧
    AnswerInResAns m₀ (phase4_propagate n Rmax b₀ b₁).2.answer := by
  unfold phase4_propagate AnswerInResAns at *
  repeat split_ifs <;> simp_all

/-- `phase4_propagate` preserves both answers when NEITHER agent is at `ceilHalf n`. -/
theorem phase4_propagate_answer_inert_of_no_ceilHalf
    {b₀ b₁ : AgentState n} {Rmax : ℕ}
    (hb₀ : b₀.rank.val + 1 ≠ ceilHalf n)
    (hb₁ : b₁.rank.val + 1 ≠ ceilHalf n) :
    (phase4_propagate n Rmax b₀ b₁).1.answer = b₀.answer ∧
    (phase4_propagate n Rmax b₀ b₁).2.answer = b₁.answer := by
  unfold phase4_propagate
  rw [if_neg hb₀, if_neg hb₁]
  exact ⟨rfl, rfl⟩

/-- `phase4_decide` is the identity when NEITHER agent is at a median rank. -/
theorem phase4_decide_identity_of_no_median
    {b₀ b₁ : AgentState n} {x₀ x₁ : Opinion}
    (hb₀_odd : ¬ n % 2 = 0 → b₀.rank.val + 1 ≠ ceilHalf n)
    (hb₁_odd : ¬ n % 2 = 0 → b₁.rank.val + 1 ≠ ceilHalf n)
    (hb_even1 : n % 2 = 0 → ¬ (b₀.rank.val + 1 = n / 2 ∧ b₁.rank.val + 1 = n / 2 + 1))
    (hb_even2 : n % 2 = 0 → ¬ (b₁.rank.val + 1 = n / 2 ∧ b₀.rank.val + 1 = n / 2 + 1)) :
    phase4_decide n b₀ b₁ x₀ x₁ = (b₀, b₁) := by
  unfold phase4_decide
  by_cases hpar : n % 2 = 0
  · rw [if_pos hpar, if_neg (hb_even1 hpar), if_neg (hb_even2 hpar)]
  · rw [if_neg hpar, if_neg (hb₀_odd hpar), if_neg (hb₁_odd hpar)]

/-- `Config.step` preserves answer at agents not in the pair. -/
theorem step_preserves_answer_at_other
    {P : Protocol (AgentState n × Opinion) Opinion Output}
    {C : Config (AgentState n × Opinion) Opinion n}
    {u v w : Fin n} (huv : u ≠ v) (hwu : w ≠ u) (hwv : w ≠ v) :
    C.step P u v w = C w := by
  simp only [Config.step, if_neg huv, show ¬(w = u) from fun h => hwu h,
    ite_false, show ¬(w = v) from fun h => hwv h]

/-- For even n≥4, a recruit pair NEVER forms the (n/2, n/2+1) median pair. -/
theorem even_recruit_not_median_pair
    {p_rank children : ℕ}
    (hn4 : 4 ≤ n)
    (hchildren : children < 2)
    (_hvalid : 2 * p_rank + children + 1 < n)
    (hpar : n % 2 = 0) :
    ¬ (p_rank + 1 = n / 2 ∧ (2 * p_rank + children + 1) + 1 = n / 2 + 1) ∧
    ¬ ((2 * p_rank + children + 1) + 1 = n / 2 ∧ p_rank + 1 = n / 2 + 1) := by
  have hndvd : 2 ∣ n := Nat.dvd_of_mod_eq_zero hpar
  have hn2 : n / 2 * 2 = n := Nat.div_mul_cancel hndvd
  constructor
  · intro ⟨h1, h2⟩
    have hp : p_rank = n / 2 - 1 := by omega
    have htgt : 2 * p_rank + children + 2 = n / 2 + 1 := by omega
    have h2eq : n / 2 * 2 = n := Nat.div_mul_cancel hndvd
    have : 2 * (n / 2) = n := by omega
    omega
  · intro ⟨_, h2⟩
    have hp : p_rank = n / 2 := by omega
    have h2eq : n / 2 * 2 = n := Nat.div_mul_cancel hndvd
    have : 2 * (n / 2) = n := by omega
    omega

-- rankDeltaOSSR + transitionPEM + phase4 unfolding chain
set_option maxHeartbeats 8000000 in
/-- **`PairResAnsSafe` for a recruit pair (Settled parent x Unsettled child) when
n is even and n >= 4.** Uses rankDeltaOSSR_answer_preserved, transitionPEM_prePhase4_resAns,
even_recruit_not_median_pair, and phase4_propagate_preserves_ResAns_pair. -/
theorem recruit_PairResAnsSafe_even
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hpar : n % 2 = 0)
    {D : Config (AgentState n) Opinion n} {m₀ : Answer}
    {p child : Fin n}
    (hpS : (D p).1.role = .Settled)
    (hcU : (D child).1.role = .Unsettled)
    (hchildren : (D p).1.children < 2)
    (hvalid : 2 * (D p).1.rank.val + (D p).1.children + 1 < n)
    (hRes : ResAns m₀ D) :
    PairResAnsSafe (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      (hn := hn) m₀ D p child := by
  -- Route: prePhase4 preserves {m₀,.phi} → phase4 preserves {m₀,.phi}
  -- because decide is identity (even_recruit_not_median_pair) and
  -- propagate preserves {m₀,.phi} (phase4_propagate_preserves_ResAns_pair).
  unfold PairResAnsSafe AnswerInResAns
  simp only [transitionPEM_eq]
  -- prePhase4 preserves answers in {m₀, .phi}
  have hpre := transitionPEM_prePhase4_resAns
    (trank := Rmax) (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
    (s₀ := (D p).1) (s₁ := (D child).1) (x₀ := (D p).2) (x₁ := (D child).2)
    (m := m₀)
    (by have := (rankDeltaOSSR_answer_preserved (Rmax := Rmax) (Emax := Emax)
        (Dmax := Dmax) (hn := hn) (D p).1 (D child).1).1; rw [this]; exact hRes p)
    (by have := (rankDeltaOSSR_answer_preserved (Rmax := Rmax) (Emax := Emax)
        (Dmax := Dmax) (hn := hn) (D p).1 (D child).1).2; rw [this]; exact hRes child)
  set pre := transitionPEM_prePhase4 n Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    (D p).1 (D child).1 (D p).2 (D child).2
  -- phase4: if not both Settled, output = prePhase4 output → done from hpre
  -- if both Settled: swap preserves answer set, decide is identity (even non-median),
  -- propagate preserves {m₀,.phi}
  by_cases hboth : pre.1.role = .Settled ∧ pre.2.role = .Settled
  · -- Phase4 fires. transitionPEM_phase4 = propagate(decide(swap(...)))
    -- Rewrite phase4 using hboth.
    rw [show transitionPEM_phase4 n Rmax pre (D p).2 (D child).2 =
      (let (b₀, b₁) := phase4_swap pre.1 pre.2 (D p).2 (D child).2
       let (b₀, b₁) := phase4_decide n b₀ b₁ (D p).2 (D child).2
       phase4_propagate n Rmax b₀ b₁) from by
        unfold transitionPEM_phase4; simp [hboth]]
    -- swap preserves the set of answer values (just reorders)
    set sw := phase4_swap pre.1 pre.2 (D p).2 (D child).2
    have hsw_ans : AnswerInResAns m₀ sw.1.answer ∧ AnswerInResAns m₀ sw.2.answer := by
      simp only [sw, phase4_swap, AnswerInResAns]
      split_ifs
      · exact ⟨hpre.2, hpre.1⟩
      · exact hpre
    -- Establish prePhase4 rank values for even_recruit_not_median_pair.
    have hstruct := transitionPEM_prePhase4_structural
      (trank := Rmax) (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
      (s₀ := (D p).1) (s₁ := (D child).1) (x₀ := (D p).2) (x₁ := (D child).2)
    have h_not_reset : ¬ ((D p).1.role = .Resetting ∨ (D child).1.role = .Resetting) := by
      rw [hpS, hcU]; decide
    have h_not_both_settled : ¬ ((D p).1.role = .Settled ∧ (D child).1.role = .Settled ∧
        (D p).1.rank = (D child).1.rank) := by
      rintro ⟨_, hcS, _⟩; rw [hcU] at hcS; exact absurd hcS (by decide)
    have hpre1_rankv : pre.1.rank.val = (D p).1.rank.val := by
      have h : pre.1.rank = (rankDeltaOSSR Rmax Emax Dmax hn ((D p).1, (D child).1)).1.rank :=
        hstruct.2.2.1
      unfold rankDeltaOSSR at h
      simp only [hpS, hcU, hchildren, hvalid, dite_true, and_self] at h
      simp [h]
    have hpre2_rankv : pre.2.rank.val = 2 * (D p).1.rank.val + (D p).1.children + 1 := by
      have h : pre.2.rank = (rankDeltaOSSR Rmax Emax Dmax hn ((D p).1, (D child).1)).2.rank :=
        hstruct.2.2.2.2.2.2.2.2.1
      unfold rankDeltaOSSR at h
      simp only [hpS, hcU, hchildren, hvalid, dite_true, and_self] at h
      simp [h]
    -- sw rank values
    have hsw_ranks : (sw.1.rank.val = (D p).1.rank.val ∧
        sw.2.rank.val = 2 * (D p).1.rank.val + (D p).1.children + 1) ∨
      (sw.1.rank.val = 2 * (D p).1.rank.val + (D p).1.children + 1 ∧
        sw.2.rank.val = (D p).1.rank.val) := by
      simp only [sw, phase4_swap]
      split_ifs
      · exact Or.inr ⟨hpre2_rankv, hpre1_rankv⟩
      · exact Or.inl ⟨hpre1_rankv, hpre2_rankv⟩
    -- phase4_decide is identity (even, non-boundary pair)
    have hnotmed := even_recruit_not_median_pair hn4 hchildren hvalid hpar
    have hdec_id : phase4_decide n sw.1 sw.2 (D p).2 (D child).2 = (sw.1, sw.2) := by
      apply phase4_decide_identity_of_no_median
      · intro hodd; exact absurd hpar hodd
      · intro hodd; exact absurd hpar hodd
      · intro _
        rcases hsw_ranks with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [h1, h2]; exact hnotmed.1
        · rw [h1, h2]; exact hnotmed.2
      · intro _
        rcases hsw_ranks with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [h1, h2]; exact fun ⟨a, b⟩ => hnotmed.2 ⟨a, b⟩
        · rw [h1, h2]; exact fun ⟨a, b⟩ => hnotmed.1 ⟨a, b⟩
    -- Final: propagate preserves {m₀,.phi} on decide output (= swap output).
    -- Goal has match-destructuring on sw. Reduce using Prod.mk.eta.
    have hgoal : (phase4_propagate n Rmax
        (phase4_decide n sw.1 sw.2 (D p).2 (D child).2).1
        (phase4_decide n sw.1 sw.2 (D p).2 (D child).2).2).1.answer = m₀ ∨
      (phase4_propagate n Rmax
        (phase4_decide n sw.1 sw.2 (D p).2 (D child).2).1
        (phase4_decide n sw.1 sw.2 (D p).2 (D child).2).2).1.answer = .phi := by
      rw [hdec_id]
      exact (phase4_propagate_preserves_ResAns_pair hsw_ans.1 hsw_ans.2).1
    have hgoal2 : (phase4_propagate n Rmax
        (phase4_decide n sw.1 sw.2 (D p).2 (D child).2).1
        (phase4_decide n sw.1 sw.2 (D p).2 (D child).2).2).2.answer = m₀ ∨
      (phase4_propagate n Rmax
        (phase4_decide n sw.1 sw.2 (D p).2 (D child).2).1
        (phase4_decide n sw.1 sw.2 (D p).2 (D child).2).2).2.answer = .phi := by
      rw [hdec_id]
      exact (phase4_propagate_preserves_ResAns_pair hsw_ans.1 hsw_ans.2).2
    exact ⟨hgoal, hgoal2⟩
  · -- Phase4 doesn't fire → output = prePhase4 output
    rw [show transitionPEM_phase4 n Rmax pre (D p).2 (D child).2 = pre from
      transitionPEM_phase4_of_not_both_settled hboth]
    exact hpre

end SSEM
