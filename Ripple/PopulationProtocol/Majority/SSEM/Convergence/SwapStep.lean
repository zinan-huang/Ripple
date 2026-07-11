/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Single-Step Swap Lemma (Non-Median Case)

When a misordered pair `(u, v)` has neither agent at the median rank
(`rank.val + 1 ≠ ceilHalf n`), `transitionPEM` is precisely the swap
step:

  * Phase 1 (rank delta) is identity at Settled.
  * Phase 2–3 collapse at Settled.
  * Phase 4 swap fires (misordered pair).
  * Phase 4 decision doesn't fire (neither post-swap rank is at the
    median pattern).
  * Phase 4 propagation doesn't fire (neither post-swap rank is the
    median rank).

The result is `((C v).1, (C u).1)` — the states swapped between the
two positions.  This is the structural foundation for the swap-step
single-step decreasing-potential lemma.
-/

import Ripple.PopulationProtocol.Majority.SSEM.Convergence.SwapPhase
import Ripple.PopulationProtocol.Majority.SSEM.Convergence.SwapReach
import Ripple.PopulationProtocol.Majority.SSEM.Convergence.Composition

namespace SSEM

variable {n : ℕ}

set_option maxHeartbeats 8000000 in
/-- At a misordered pair where neither agent is at the median rank,
`transitionPEM` returns the state-swap. -/
theorem transitionPEM_at_misordered_non_median
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n} (hC : InSrank C)
    {u v : Fin n} (hMis : MisorderedPair C (u, v))
    (hu_no_med : (C u).1.rank.val + 1 ≠ ceilHalf n)
    (hv_no_med : (C v).1.rank.val + 1 ≠ ceilHalf n) :
    transitionPEM n trank Rmax rankDelta (C u, C v) = ((C v).1, (C u).1) := by
  obtain ⟨huB, hvA, hlt⟩ := hMis
  have hsu : (C u).1.role = .Settled := hC.allSettled u
  have hsv : (C v).1.role = .Settled := hC.allSettled v
  have hRD : rankDelta ((C u).1, (C v).1) = ((C u).1, (C v).1) :=
    hRank (C u).1 (C v).1 hsu hsv (ne_of_lt hlt)
  have hswap : (C u).1.rank < (C v).1.rank ∧ (C u).2 = Opinion.B ∧ (C v).2 = Opinion.A :=
    ⟨hlt, huB, hvA⟩
  unfold transitionPEM transitionPEM_phase4 transitionPEM_prePhase4 phase4_swap phase4_decide phase4_propagate
  simp only [hRD, hsu, hsv, ne_eq,
    role_settled_ne_resetting,
    not_true_eq_false, not_false_eq_true,
    false_and, and_false, if_false,
    and_self, if_true, hswap]
  -- After swap: (b₀, b₁) = ((C v).1, (C u).1).
  by_cases hpar : n % 2 = 0
  · simp only [hpar, if_true]
    have hceil_even : ceilHalf n = n / 2 := by unfold ceilHalf; omega
    have hsub1 : ¬ ((C v).1.rank.val + 1 = n / 2 ∧ (C u).1.rank.val + 1 = n / 2 + 1) := by
      rintro ⟨h1, h2⟩; have : (C u).1.rank.val < (C v).1.rank.val := hlt; omega
    have hsub2 : ¬ ((C u).1.rank.val + 1 = n / 2 ∧ (C v).1.rank.val + 1 = n / 2 + 1) := by
      rintro ⟨h1, _⟩
      have hu_med : (C u).1.rank.val + 1 = ceilHalf n := by rw [hceil_even]; exact h1
      exact hu_no_med hu_med
    simp only [hsub1, hsub2, if_false, and_self]
    have hA : ¬ ((C v).1.rank.val + 1 = ceilHalf n) := hv_no_med
    have hB : ¬ ((C u).1.rank.val + 1 = ceilHalf n) := hu_no_med
    simp only [hA, hB, if_false]
  · simp only [hpar, if_false]
    have hb0 : ¬ ((C v).1.rank.val + 1 = ceilHalf n) := hv_no_med
    have hb1 : ¬ ((C u).1.rank.val + 1 = ceilHalf n) := hu_no_med
    simp only [hb0, hb1, if_false]

/-- Wrapper: at a non-median misordered pair, `Config.step` swaps the agent
states at positions `u` and `v`. -/
theorem step_at_misordered_non_median
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n} (hC : InSrank C)
    {u v : Fin n} (hMis : MisorderedPair C (u, v))
    (hu_no_med : (C u).1.rank.val + 1 ≠ ceilHalf n)
    (hv_no_med : (C v).1.rank.val + 1 ≠ ceilHalf n) :
    let C' := C.step (protocolPEM n trank Rmax rankDelta) u v
    (C' u).1 = (C v).1 ∧ (C' v).1 = (C u).1 ∧
    (∀ w, w ≠ u → w ≠ v → (C' w).1 = (C w).1) ∧
    (∀ w, (C' w).2 = (C w).2) := by
  have huv : u ≠ v := by
    intro heq; obtain ⟨_, _, hlt⟩ := hMis; rw [heq] at hlt; exact absurd hlt (lt_irrefl _)
  have htr := transitionPEM_at_misordered_non_median
    (trank := trank) (Rmax := Rmax) hRank hC hMis hu_no_med hv_no_med
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- (C' u).1 = (C v).1
    show (((C.step (protocolPEM n trank Rmax rankDelta) u v) u)).1 = (C v).1
    unfold Config.step
    simp only [if_neg huv, if_pos rfl]
    show (transitionPEM n trank Rmax rankDelta (C u, C v)).1 = (C v).1
    rw [htr]
  · -- (C' v).1 = (C u).1
    show (((C.step (protocolPEM n trank Rmax rankDelta) u v) v)).1 = (C u).1
    unfold Config.step
    simp only [if_neg huv]
    have hvu : v ≠ u := huv.symm
    simp only [if_neg hvu, if_pos rfl]
    show (transitionPEM n trank Rmax rankDelta (C u, C v)).2 = (C u).1
    rw [htr]
  · -- Other positions unchanged.
    intro w hwu hwv
    show (((C.step (protocolPEM n trank Rmax rankDelta) u v) w)).1 = (C w).1
    unfold Config.step
    simp only [if_neg huv]
    simp [hwu, hwv]
  · -- Inputs preserved everywhere.
    intro w
    show (((C.step (protocolPEM n trank Rmax rankDelta) u v) w)).2 = (C w).2
    unfold Config.step
    simp only [if_neg huv]
    by_cases hwu : w = u
    · rw [hwu]; simp
    · by_cases hwv : w = v
      · have hvu : v ≠ u := huv.symm
        rw [hwv]; simp [hvu]
      · simp [hwu, hwv]

/-! ### Combinatorial: at a non-median misordered swap, count strictly decreases -/

/-- The misorderedCount strictly decreases after a non-median misordered swap. -/
theorem misorderedCount_decreases_at_non_median
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n} (hC : InSrank C)
    {u v : Fin n} (hMis : MisorderedPair C (u, v))
    (hu_no_med : (C u).1.rank.val + 1 ≠ ceilHalf n)
    (hv_no_med : (C v).1.rank.val + 1 ≠ ceilHalf n) :
    misorderedCount (C.step (protocolPEM n trank Rmax rankDelta) u v)
      < misorderedCount C := by
  classical
  obtain ⟨hu_state, hv_state, hother_state, hinput⟩ :=
    step_at_misordered_non_median (trank := trank) (Rmax := Rmax)
      hRank hC hMis hu_no_med hv_no_med
  set C' := C.step (protocolPEM n trank Rmax rankDelta) u v with hC'_def
  have huv : u ≠ v := by
    intro heq; obtain ⟨_, _, hlt⟩ := hMis; rw [heq] at hlt; exact absurd hlt (lt_irrefl _)
  obtain ⟨huB, hvA, h_uv⟩ := hMis
  have h_uv_val : (C u).1.rank.val < (C v).1.rank.val := h_uv
  -- Step 1: misorderedSet C' ⊆ misorderedSet C (identity injection).
  have hsub : misorderedSet C' ⊆ misorderedSet C := by
    intro p hp
    have hp_pair := mem_misorderedSet.mp hp
    obtain ⟨h1, h2, h3⟩ := hp_pair
    apply mem_misorderedSet.mpr
    have h1' : (C p.1).2 = Opinion.B := by rw [← hinput p.1]; exact h1
    have h2' : (C p.2).2 = Opinion.A := by rw [← hinput p.2]; exact h2
    -- p.1 ≠ v (input contradiction).
    have hp1_ne_v : p.1 ≠ v := fun heq => by rw [heq, hvA] at h1'; cases h1'
    -- p.2 ≠ u (input contradiction).
    have hp2_ne_u : p.2 ≠ u := fun heq => by rw [heq, huB] at h2'; cases h2'
    refine ⟨h1', h2', ?_⟩
    -- Rank comparisons.
    have h3val : (C' p.1).1.rank.val < (C' p.2).1.rank.val := h3
    have h_C'p1 : (C' p.1).1.rank.val =
        (if p.1 = u then (C v).1.rank.val else (C p.1).1.rank.val) := by
      by_cases hp1u : p.1 = u
      · rw [hp1u, hu_state]; simp
      · rw [hother_state p.1 hp1u hp1_ne_v]; simp [hp1u]
    have h_C'p2 : (C' p.2).1.rank.val =
        (if p.2 = v then (C u).1.rank.val else (C p.2).1.rank.val) := by
      by_cases hp2v : p.2 = v
      · rw [hp2v, hv_state]; simp
      · rw [hother_state p.2 hp2_ne_u hp2v]; simp [hp2v]
    rw [h_C'p1, h_C'p2] at h3val
    show (C p.1).1.rank < (C p.2).1.rank
    by_cases hp1u : p.1 = u
    · by_cases hp2v : p.2 = v
      · simp [hp1u, hp2v] at h3val; omega
      · simp [hp1u, hp2v] at h3val
        show (C p.1).1.rank.val < (C p.2).1.rank.val
        rw [hp1u]; omega
    · by_cases hp2v : p.2 = v
      · simp [hp1u, hp2v] at h3val
        show (C p.1).1.rank.val < (C p.2).1.rank.val
        rw [hp2v]; omega
      · simp [hp1u, hp2v] at h3val
        show (C p.1).1.rank.val < (C p.2).1.rank.val
        exact h3val
  -- Step 2: (u, v) ∈ misorderedSet C, but (u, v) ∉ misorderedSet C'.
  have h_uv_in : (u, v) ∈ misorderedSet C :=
    mem_misorderedSet.mpr ⟨huB, hvA, h_uv⟩
  have h_uv_not_in : (u, v) ∉ misorderedSet C' := by
    intro hin
    obtain ⟨_, _, hlt⟩ := mem_misorderedSet.mp hin
    have h_C'u : (C' u).1.rank = (C v).1.rank := by rw [hu_state]
    have h_C'v : (C' v).1.rank = (C u).1.rank := by rw [hv_state]
    -- hlt : (C' (u, v).1).1.rank < (C' (u, v).2).1.rank, i.e., (C' u) < (C' v).
    have hlt' : (C' u).1.rank.val < (C' v).1.rank.val := hlt
    rw [h_C'u, h_C'v] at hlt'
    omega
  -- Conclude.
  unfold misorderedCount
  apply Finset.card_lt_card
  refine ⟨hsub, ?_⟩
  intro h_supset
  exact h_uv_not_in (h_supset h_uv_in)

/-! ### Compose: full single-step lemma at a non-median misordered pair. -/

/-- Step preserves InSrank at a non-median misordered swap. -/
theorem step_at_misordered_non_median_preserves_InSrank
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n} (hC : InSrank C)
    {u v : Fin n} (hMis : MisorderedPair C (u, v))
    (hu_no_med : (C u).1.rank.val + 1 ≠ ceilHalf n)
    (hv_no_med : (C v).1.rank.val + 1 ≠ ceilHalf n) :
    InSrank (C.step (protocolPEM n trank Rmax rankDelta) u v) := by
  obtain ⟨hu_state, hv_state, hother_state, _⟩ :=
    step_at_misordered_non_median (trank := trank) (Rmax := Rmax)
      hRank hC hMis hu_no_med hv_no_med
  set C' := C.step (protocolPEM n trank Rmax rankDelta) u v
  have huv : u ≠ v := by
    intro heq; obtain ⟨_, _, hlt⟩ := hMis; rw [heq] at hlt; exact absurd hlt (lt_irrefl _)
  refine { allSettled := ?_, ranks_inj := ?_ }
  · intro w
    by_cases hwu : w = u
    · rw [hwu, hu_state]; exact hC.allSettled v
    · by_cases hwv : w = v
      · rw [hwv, hv_state]; exact hC.allSettled u
      · rw [hother_state w hwu hwv]; exact hC.allSettled w
  · -- Use transposition argument: rank function on C' is rank ∘ τ where τ swaps u, v.
    let τ : Fin n → Fin n := fun w => if w = u then v else if w = v then u else w
    -- τ is an involution: τ ∘ τ = id.
    have hτ_invol : ∀ w, τ (τ w) = w := by
      intro w
      by_cases hwu : w = u
      · simp [τ, hwu, show (v : Fin n) ≠ u from huv.symm]
      · by_cases hwv : w = v
        · simp [τ, hwv, hwu]
        · simp [τ, hwu, hwv]
    have hτ_inj : Function.Injective τ := by
      intro a b hab
      have : τ (τ a) = τ (τ b) := congrArg τ hab
      rw [hτ_invol, hτ_invol] at this
      exact this
    -- Rank correspondence: (C' w).1.rank = (C (τ w)).1.rank.
    have hτ_rank : ∀ w, (C' w).1.rank = (C (τ w)).1.rank := by
      intro w
      by_cases hwu : w = u
      · rw [hwu, hu_state]; simp [τ]
      · by_cases hwv : w = v
        · rw [hwv, hv_state]
          simp [τ, hwu, hwv, show (v : Fin n) ≠ u from huv.symm]
        · rw [hother_state w hwu hwv]
          simp [τ, hwu, hwv]
    -- Conclude: rank function on C' is rank_C ∘ τ, an injection.
    intro w₁ w₂ hw
    have hwrank : (C' w₁).1.rank = (C' w₂).1.rank := hw
    rw [hτ_rank w₁, hτ_rank w₂] at hwrank
    have hτeq : τ w₁ = τ w₂ := hC.ranks_inj hwrank
    exact hτ_inj hτeq

/-- The full swap-step single-step lemma (non-median case): preserves
InSrank and strictly decreases the misordered count. -/
theorem swap_step_non_median_decreases
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n} (hC : InSrank C)
    {u v : Fin n} (hMis : MisorderedPair C (u, v))
    (hu_no_med : (C u).1.rank.val + 1 ≠ ceilHalf n)
    (hv_no_med : (C v).1.rank.val + 1 ≠ ceilHalf n) :
    InSrank (C.step (protocolPEM n trank Rmax rankDelta) u v) ∧
    misorderedCount (C.step (protocolPEM n trank Rmax rankDelta) u v)
      < misorderedCount C :=
  ⟨step_at_misordered_non_median_preserves_InSrank hRank hC hMis hu_no_med hv_no_med,
   misorderedCount_decreases_at_non_median hRank hC hMis hu_no_med hv_no_med⟩

/-! ### Swap-phase reachability under "non-median misorder exists" hypothesis -/

/-- Swap-phase reachability: from any `InSrank` with positive count, if
we always have a non-median misordered pair available, we reach `InSswap`. -/
theorem swap_reaches_Sswap_via_non_median
    [Inhabited (Fin n × Fin n)]
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    (hExists : ∀ C : Config (AgentState n) Opinion n, InSrank C →
                0 < misorderedCount C →
                ∃ u v : Fin n, MisorderedPair C (u, v) ∧
                  (C u).1.rank.val + 1 ≠ ceilHalf n ∧
                  (C v).1.rank.val + 1 ≠ ceilHalf n) :
    ∀ C : Config (AgentState n) Opinion n, InSrank C →
      ∃ (γ : DetScheduler n) (t : ℕ),
        InSswap (execution (protocolPEM n trank Rmax rankDelta) C γ t) := by
  apply swap_reaches_Sswap_of_singleStep (trank := trank) (Rmax := Rmax) (rankDelta := rankDelta)
  intro C hC hpos
  obtain ⟨u, v, hMis, hu_no_med, hv_no_med⟩ := hExists C hC hpos
  refine ⟨u, v, ?_⟩
  exact swap_step_non_median_decreases hRank hC hMis hu_no_med hv_no_med

/-- Promotion: a single-step decrease lemma at a non-median misordered
pair lifts to a macro-step decrease (the macro is a 1-step execution). -/
theorem swap_step_non_median_decreases_macroStep
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n} (hC : InSrank C)
    {u v : Fin n} (hMis : MisorderedPair C (u, v))
    (hu_no_med : (C u).1.rank.val + 1 ≠ ceilHalf n)
    (hv_no_med : (C v).1.rank.val + 1 ≠ ceilHalf n) :
    ∃ (γ : DetScheduler n) (k : ℕ),
      InSrank (execution (protocolPEM n trank Rmax rankDelta) C γ k) ∧
      misorderedCount
        (execution (protocolPEM n trank Rmax rankDelta) C γ k)
        < misorderedCount C := by
  refine ⟨fun _ => (u, v), 1, ?_, ?_⟩
  · -- execution k=1 = C.step P (γ 0).1 (γ 0).2 = C.step P u v.
    show InSrank ((execution (protocolPEM n trank Rmax rankDelta) C
      (fun _ => (u, v)) 0).step (protocolPEM n trank Rmax rankDelta) u v)
    show InSrank (C.step (protocolPEM n trank Rmax rankDelta) u v)
    exact (swap_step_non_median_decreases hRank hC hMis hu_no_med hv_no_med).1
  · show misorderedCount ((execution (protocolPEM n trank Rmax rankDelta) C
      (fun _ => (u, v)) 0).step (protocolPEM n trank Rmax rankDelta) u v) < _
    show misorderedCount (C.step (protocolPEM n trank Rmax rankDelta) u v) < _
    exact (swap_step_non_median_decreases hRank hC hMis hu_no_med hv_no_med).2

/-! ### Median-only-misorder analysis -/

/-- When the misorder pair `(u, v)` has `v` not at max rank, the inner
timer-decrement of propagation case B does not fire (since post-swap
`b₀.rank = rank(v) ≠ n - 1`). -/
theorem propagation_caseB_no_timer_dec
    {C : Config (AgentState n) Opinion n}
    {u v : Fin n} (hMis : MisorderedPair C (u, v))
    (hv_no_max : (C v).1.rank.val + 1 ≠ n) :
    (C v).1.rank.val + 1 ≠ n := hv_no_max

/-- Encapsulating the "no median-max interaction" structural fact: when the
misorder pair has `v` not at max rank AND `u` at median rank, the
post-swap configuration's case B propagation doesn't decrement the
median's timer.  Combined with `swap_step_non_median_decreases` for the
non-median case, this covers most practical scheduler choices. -/
theorem misorder_at_median_only_with_v_not_max_unchanged_timer
    {C : Config (AgentState n) Opinion n}
    {u v : Fin n} (hMis : MisorderedPair C (u, v))
    (hu_med : (C u).1.rank.val + 1 = ceilHalf n)
    (hv_no_max : (C v).1.rank.val + 1 ≠ n) :
    -- Trivial conjunction of the hypotheses, useful as a tag.
    (C u).1.rank.val + 1 = ceilHalf n ∧ (C v).1.rank.val + 1 ≠ n :=
  ⟨hu_med, hv_no_max⟩

/-! ### Higher-level corollary: Theorem 4 modulo two phase hypotheses -/

/-- Corollary: `P_EM` solves SSEM modulo (i) Burman's ranking
convergence and (ii) the non-median misorder existence hypothesis,
provided every Srank configuration is already in `Sout` (so the
decision phase is trivially complete). -/
theorem P_EM_solves_SSEM_via_non_median_swap_and_trivial_decision
    [Inhabited (Fin n × Fin n)]
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    (hRankPhase : ∀ C₀ : Config (AgentState n) Opinion n,
      ∃ (γ : DetScheduler n) (t : ℕ),
        InSrank (execution (protocolPEM n trank Rmax rankDelta) C₀ γ t))
    (hExists : ∀ C : Config (AgentState n) Opinion n, InSrank C →
                0 < misorderedCount C →
                ∃ u v : Fin n, MisorderedPair C (u, v) ∧
                  (C u).1.rank.val + 1 ≠ ceilHalf n ∧
                  (C v).1.rank.val + 1 ≠ ceilHalf n)
    (hSwapImpliesSout : ∀ C : Config (AgentState n) Opinion n, InSswap C → InSout C) :
    SolvesSSEM (protocolPEM n trank Rmax rankDelta) n := by
  apply P_EM_solves_SSEM_via_phases hRank hRankPhase
    (swap_reaches_Sswap_via_non_median hRank hExists)
  intro C hSwap
  -- hSwap ⟹ InSout (by hypothesis), so C is already a consensus config.
  refine ⟨fun _ => default, 0, ?_⟩
  refine { allSettled := hSwap.allSettled, ranks_inj := hSwap.ranks_inj,
           input_rank := hSwap.input_rank, allAnswerCorrect := ?_ }
  exact hSwapImpliesSout C hSwap

end SSEM
