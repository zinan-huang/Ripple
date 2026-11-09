/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Silence of P_EM (Kanaya et al. 2025, Lemma 6 and Theorem 4, qualitative part)

Source: arXiv:2503.17652v1, §5.2 (`ref/Kanaya-2025-SSEM-2503.17652v1.pdf`). Lemma 6 says the
set `S_em` of final configurations is a set of silent configurations; Theorem 4 says `P_EM` is a
silent self-stabilizing exact-majority protocol.

In the Lean protocol `protocolPEM`, a consensus configuration (`IsConsensusConfig`: all agents
Settled with a bijective ranking sorted by input and the correct answer) changes under exactly
one kind of interaction: the median agent, meeting the agent of rank `n`, decrements its timer
(`phase4_propagate`). Hence:

* `transitionPEM_consensus_pair_eq`: on a consensus pair, one transition only applies
  `medianTick` to the two states;
* `IsSilentConsensus.isSilent`: a consensus configuration whose median timer is `0` is silent
  (this is `S_em`);
* `reach_silentConsensus_of_consensus`: from a consensus configuration, letting the median meet
  the rank-`n` agent `timer` times reaches a silent consensus configuration;
* `P_EM_solves_silent_SSEM_linear`: the concrete `P_EM` solves *silent* SSEM for `n ≥ 4`.

The quantitative part of Theorem 4 (O(n) expected and O(n log n) w.h.p. silence time, O(n)
states) is not formalized; see `OPEN_PROBLEMS.md`.
-/

import Ripple.PopulationProtocol.SSEM.Convergence.BurmanConvergenceLinear
import Ripple.PopulationProtocol.SSEM.Defs.Silent

namespace Ripple.PopulationProtocol.SSEM

variable {n : ℕ}

/-- The only change `phase4_propagate` makes on a consensus pair: the median agent, meeting the
agent of rank `n`, decrements its timer. -/
def medianTick (n : ℕ) (a b : AgentState n) : AgentState n :=
  if a.rank.val + 1 = ceilHalf n ∧ b.rank.val + 1 = n then { a with timer := a.timer - 1 } else a

theorem AgentState.with_answer_eq_self {s : AgentState n} {v : Answer} (h : v = s.answer) :
    ({ s with answer := v } : AgentState n) = s := by
  subst h
  rfl

theorem AgentState.with_timer_eq_self {s : AgentState n} {t : ℕ} (h : t = s.timer) :
    ({ s with timer := t } : AgentState n) = s := by
  subst h
  rfl

/-- On a consensus pair the decision phase rewrites answers with the values they already have. -/
theorem phase4_decide_consensus_pair {a : Answer} {nA : ℕ} {s₀ s₁ : AgentState n}
    {x₀ x₁ : Opinion} (hpair : ConsensusPair s₀ s₁ x₀ x₁ a nA) :
    phase4_decide n s₀ s₁ x₀ x₁ = (s₀, s₁) := by
  unfold phase4_decide
  by_cases hev : n % 2 = 0
  · rw [if_pos hev]
    by_cases h1 : s₀.rank.val + 1 = n / 2 ∧ s₁.rank.val + 1 = n / 2 + 1
    · rw [if_pos h1]
      by_cases hxx : x₀ = x₁
      · rw [if_pos hxx]
        have e := hpair.decision_even_same_lower hev h1.1 h1.2 hxx
        exact Prod.ext (AgentState.with_answer_eq_self (e.trans hpair.answer₀.symm))
          (AgentState.with_answer_eq_self (e.trans hpair.answer₁.symm))
      · rw [if_neg hxx]
        have e := hpair.decision_even_diff_lower hev h1.1 h1.2 hxx
        exact Prod.ext (AgentState.with_answer_eq_self (e.symm.trans hpair.answer₀.symm))
          (AgentState.with_answer_eq_self (e.symm.trans hpair.answer₁.symm))
    · rw [if_neg h1]
      by_cases h2 : s₁.rank.val + 1 = n / 2 ∧ s₀.rank.val + 1 = n / 2 + 1
      · rw [if_pos h2]
        by_cases hxx : x₁ = x₀
        · rw [if_pos hxx]
          have e := hpair.decision_even_same_upper hev h2.1 h2.2 hxx
          exact Prod.ext (AgentState.with_answer_eq_self (e.trans hpair.answer₀.symm))
            (AgentState.with_answer_eq_self (e.trans hpair.answer₁.symm))
        · rw [if_neg hxx]
          have e := hpair.decision_even_diff_upper hev h2.1 h2.2 hxx
          exact Prod.ext (AgentState.with_answer_eq_self (e.symm.trans hpair.answer₀.symm))
            (AgentState.with_answer_eq_self (e.symm.trans hpair.answer₁.symm))
      · rw [if_neg h2]
  · rw [if_neg hev]
    have hm := hpair.decision_odd_match hev
    refine Prod.ext ?_ ?_
    · show (if s₀.rank.val + 1 = ceilHalf n then { s₀ with answer := opinionToAnswer x₀ }
        else s₀) = s₀
      split_ifs with h
      · exact AgentState.with_answer_eq_self ((hm.1 h).trans hpair.answer₀.symm)
      · rfl
    · show (if s₁.rank.val + 1 = ceilHalf n then { s₁ with answer := opinionToAnswer x₁ }
        else s₁) = s₁
      split_ifs with h
      · exact AgentState.with_answer_eq_self ((hm.2 h).trans hpair.answer₁.symm)
      · rfl

/-- With equal answers and distinct ranks, the propagation phase only ticks the median timer. -/
theorem phase4_propagate_of_answer_eq {Rmax : ℕ} {s₀ s₁ : AgentState n}
    (hans : s₀.answer = s₁.answer) (hne : s₀.rank ≠ s₁.rank) :
    phase4_propagate n Rmax s₀ s₁ = (medianTick n s₀ s₁, medianTick n s₁ s₀) := by
  have hl0 := s₀.rank.isLt
  have hl1 := s₁.rank.isLt
  have hc : ceilHalf n = (n + 1) / 2 := rfl
  unfold phase4_propagate medianTick
  by_cases h0 : s₀.rank.val + 1 = ceilHalf n <;>
    by_cases h1 : s₁.rank.val + 1 = ceilHalf n <;>
    by_cases hr0 : s₀.rank.val + 1 = n <;>
    by_cases hr1 : s₁.rank.val + 1 = n <;>
    first
      | (exfalso; exact hne (Fin.ext (by omega)))
      | (exfalso; omega)
      | ((first | replace h0 := eq_false h0 | replace h0 := eq_true h0)
         (first | replace h1 := eq_false h1 | replace h1 := eq_true h1)
         (first | replace hr0 := eq_false hr0 | replace hr0 := eq_true hr0)
         (first | replace hr1 := eq_false hr1 | replace hr1 := eq_true hr1)
         simp only [h0, h1, hr0, hr1, hans, ↓reduceIte, true_and, and_true, false_and,
           and_false, ne_eq, eq_self_iff_true, not_true_eq_false, not_false_eq_true])

/-- **One transition on a consensus pair.** It applies `medianTick` to both states and changes
nothing else. -/
theorem transitionPEM_consensus_pair_eq {trank Rmax nA : ℕ} {a : Answer}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    {s₀ s₁ : AgentState n} {x₀ x₁ : Opinion}
    (hpair : ConsensusPair s₀ s₁ x₀ x₁ a nA)
    (hne : s₀.rank ≠ s₁.rank) :
    transitionPEM n trank Rmax rankDelta ((s₀, x₀), (s₁, x₁)) =
      (medianTick n s₀ s₁, medianTick n s₁ s₀) := by
  have hRD : rankDelta (s₀, s₁) = (s₀, s₁) :=
    hRank s₀ s₁ hpair.settled₀ hpair.settled₁ hne
  rw [transitionPEM_eq_phase4_of_settled_fix hRD hpair.settled₀ hpair.settled₁]
  have hswap : phase4_swap s₀ s₁ x₀ x₁ = (s₀, s₁) := by
    unfold phase4_swap
    rw [if_neg hpair.swap_fails]
  simp only [transitionPEM_phase4, hpair.settled₀, hpair.settled₁, eq_self_iff_true, and_self,
    ↓reduceIte,
    hswap, phase4_decide_consensus_pair hpair]
  exact phase4_propagate_of_answer_eq (hpair.answer₀.trans hpair.answer₁.symm) hne

/-- One interaction of distinct agents in a consensus configuration. -/
theorem consensus_step_apply {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n} (hC : IsConsensusConfig C)
    {u v : Fin n} (huv : u ≠ v) (w : Fin n) :
    (C.step (protocolPEM n trank Rmax rankDelta) u v) w =
      if w = u then (medianTick n (C u).1 (C v).1, (C u).2)
      else if w = v then (medianTick n (C v).1 (C u).1, (C v).2) else C w := by
  have hne : (C u).1.rank ≠ (C v).1.rank := fun h => huv (hC.ranks_inj h)
  have hT : (protocolPEM n trank Rmax rankDelta).δ (C u, C v) =
      (medianTick n (C u).1 (C v).1, medianTick n (C v).1 (C u).1) :=
    transitionPEM_consensus_pair_eq (trank := trank) (Rmax := Rmax) hRank
      (consensus_pair_of_config hC u v) hne
  unfold Config.step
  rw [if_neg huv]
  simp only [hT]

/-- **The final configurations `S_em`:** consensus with the median timer at zero. -/
def IsSilentConsensus (C : Config (AgentState n) Opinion n) : Prop :=
  IsConsensusConfig C ∧
    ∀ v : Fin n, (C v).1.rank.val + 1 = ceilHalf n → (C v).1.timer = 0

theorem medianTick_eq_self_of_timer {a b : AgentState n}
    (h : a.rank.val + 1 = ceilHalf n → a.timer = 0) :
    medianTick n a b = a := by
  unfold medianTick
  split_ifs with hc
  · have h0 := h hc.1
    exact AgentState.with_timer_eq_self (by omega)
  · rfl

/-- **Lemma 6 (Kanaya et al.).** A consensus configuration with median timer `0` is silent. -/
theorem IsSilentConsensus.isSilent {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n} (hC : IsSilentConsensus C) :
    C.isSilent (protocolPEM n trank Rmax rankDelta) := by
  intro u v
  by_cases huv : u = v
  · subst huv
    simp [Config.step]
  funext w
  rw [consensus_step_apply hRank hC.1 huv w]
  split_ifs with hwu hwv
  · subst hwu
    rw [medianTick_eq_self_of_timer (hC.2 w)]
  · subst hwv
    rw [medianTick_eq_self_of_timer (hC.2 w)]
  · rfl

/-- From a consensus configuration on `n ≥ 2` agents, some schedule reaches a silent consensus
configuration: the median agent meets the agent of rank `n` until its timer is `0`. -/
theorem reach_silentConsensus_of_consensus {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta) (hn2 : 2 ≤ n)
    {C : Config (AgentState n) Opinion n} (hC : IsConsensusConfig C) :
    ∃ (γ : DetScheduler n) (t : ℕ),
      IsSilentConsensus (execution (protocolPEM n trank Rmax rankDelta) C γ t) := by
  have hsurj : Function.Surjective (fun v => (C v).1.rank) :=
    Finite.injective_iff_surjective.mp hC.ranks_inj
  have hceil : ceilHalf n < n := by unfold ceilHalf; omega
  obtain ⟨μ, hμ⟩ := hsurj ⟨ceilHalf n - 1, by omega⟩
  obtain ⟨ν, hν⟩ := hsurj ⟨n - 1, by omega⟩
  have hμr : (C μ).1.rank.val + 1 = ceilHalf n := by
    have := congr_arg Fin.val hμ
    simp only at this
    have := ceilHalf_pos (show n > 0 by omega)
    omega
  have hνr : (C ν).1.rank.val + 1 = n := by
    have := congr_arg Fin.val hν
    simp only at this
    omega
  have hμν : μ ≠ ν := by
    intro h
    rw [h] at hμr
    omega
  -- induction on the median timer
  have main : ∀ k : ℕ, ∀ D : Config (AgentState n) Opinion n, IsConsensusConfig D →
      (D μ).1.rank.val + 1 = ceilHalf n → (D ν).1.rank.val + 1 = n →
      (D μ).1.timer = k →
      ∃ (γ : DetScheduler n) (t : ℕ),
        IsSilentConsensus (execution (protocolPEM n trank Rmax rankDelta) D γ t) := by
    intro k
    induction k with
    | zero =>
        intro D hD hDμ _ hk
        refine ⟨fun _ => (μ, ν), 0, hD, ?_⟩
        intro v hv
        change (D v).1.rank.val + 1 = ceilHalf n at hv
        change (D v).1.timer = 0
        have hvμ : v = μ := hD.ranks_inj (Fin.ext (by
          show (D v).1.rank.val = (D μ).1.rank.val
          omega))
        subst hvμ
        exact hk
    | succ k ih =>
        intro D hD hDμ hDν hk
        set D' := D.step (protocolPEM n trank Rmax rankDelta) μ ν with hD'
        have hD'c : IsConsensusConfig D' := step_preserves_consensus hRank hD μ ν
        have hD'μ : D' μ = (medianTick n (D μ).1 (D ν).1, (D μ).2) := by
          rw [hD', consensus_step_apply hRank hD hμν μ, if_pos rfl]
        have hD'ν : D' ν = (medianTick n (D ν).1 (D μ).1, (D ν).2) := by
          rw [hD', consensus_step_apply hRank hD hμν ν, if_neg (Ne.symm hμν), if_pos rfl]
        have htickμ : medianTick n (D μ).1 (D ν).1 =
            { (D μ).1 with timer := (D μ).1.timer - 1 } := by
          unfold medianTick
          rw [if_pos ⟨hDμ, hDν⟩]
        have htickν : medianTick n (D ν).1 (D μ).1 = (D ν).1 := by
          unfold medianTick
          rw [if_neg (show ¬ ((D ν).1.rank.val + 1 = ceilHalf n ∧
            (D μ).1.rank.val + 1 = n) by omega)]
        obtain ⟨γ, t, hγ⟩ := ih D' hD'c
          (by rw [hD'μ, htickμ]; exact hDμ)
          (by rw [hD'ν, htickν]; exact hDν)
          (by rw [hD'μ, htickμ]; show (D μ).1.timer - 1 = k; omega)
        refine ⟨concatScheduler (fun _ => (μ, ν)) 1 γ, 1 + t, ?_⟩
        rw [execution_concat]
        exact hγ
  exact main _ C hC hμr hνr rfl

/-- If every configuration can reach a consensus configuration, `P_EM` is silent. -/
theorem P_EM_silent_of_consensus_reachable {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta) (hn2 : 2 ≤ n)
    (hReach : ∀ C₀ : Config (AgentState n) Opinion n,
      ∃ (γ : DetScheduler n) (t : ℕ),
        IsConsensusConfig (execution (protocolPEM n trank Rmax rankDelta) C₀ γ t)) :
    SilentProtocol (protocolPEM n trank Rmax rankDelta) n := by
  intro C₀
  obtain ⟨γ₁, t₁, hC⟩ := hReach C₀
  obtain ⟨γ₂, t₂, hS⟩ := reach_silentConsensus_of_consensus (trank := trank) (Rmax := Rmax)
    hRank hn2 hC
  refine ⟨concatScheduler γ₁ t₁ γ₂, t₁ + t₂, ?_⟩
  rw [execution_concat]
  exact hS.isSilent hRank

/-- **`P_EM` is silent** (Kanaya Theorem 4, silence; concrete protocol, `n ≥ 4`): from every
configuration some schedule reaches a silent configuration. -/
theorem P_EM_silent_linear
    [Inhabited (Fin n × Fin n)]
    {Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n)
    (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax) :
    SilentProtocol (protocolPEM n n n (rankDeltaOSSR n Emax Dmax hn)) n :=
  P_EM_silent_of_consensus_reachable rankDeltaOSSR_satisfies_fix (by omega)
    (P_EM_consensus_reachable_of_BurmanConvergence rankDeltaOSSR_satisfies_fix hn4
      (burmanConvergence_concrete hn4 hEmax hDmax le_rfl))

/-- **Kanaya Theorem 4, qualitative part.** The concrete `P_EM` solves *silent*
self-stabilizing exact majority on `n ≥ 4` agents: from every configuration a safe configuration
with the majority output is reachable (`P_EM_solves_SSEM_linear`) and so is a silent one
(`P_EM_silent_linear`). The time and state bounds of Theorem 4 are not part of this statement. -/
theorem P_EM_solves_silent_SSEM_linear
    [Inhabited (Fin n × Fin n)]
    {Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n)
    (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax) :
    SolvesSilentSSEM (protocolPEM n n n (rankDeltaOSSR n Emax Dmax hn)) n :=
  ⟨P_EM_solves_SSEM_linear hn4 hEmax hDmax, P_EM_silent_linear hn4 hEmax hDmax⟩

/-- Non-vacuity: the hypotheses of `P_EM_solves_silent_SSEM_linear` hold at `n = 4`. -/
example : SolvesSilentSSEM (protocolPEM 4 4 4 (rankDeltaOSSR 4 4 4 (by norm_num))) 4 :=
  P_EM_solves_silent_SSEM_linear le_rfl le_rfl le_rfl

end Ripple.PopulationProtocol.SSEM
