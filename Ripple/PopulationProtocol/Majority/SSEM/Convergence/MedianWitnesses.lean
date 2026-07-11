/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Median-Wrong Witnesses

Discharges the `hOddCase` / `hEvenCase` hypotheses of
`P_EM_solves_SSEM_full_modulo_burman` by constructing concrete witness
pairs `(μ, v)` whenever the median is wrong.

For odd `n ≥ 3` and InSswap C with the median wrong: pick `μ` at
median rank, `v` at rank 0 (exists via the rank bijection).  Then
all the structural conditions (v non-median, v non-max, rank_v < rank_μ,
μ ≠ v) are satisfied; timer ≥ 1 is taken as an external assumption.

Even-n case is structurally similar — median pair (lower at n/2, upper
at n/2 + 1) — needs both medians to exist and an inputs-agree witness.
-/

import Ripple.PopulationProtocol.Majority.SSEM.Convergence.MasterModuloBurman
import Ripple.PopulationProtocol.Majority.SSEM.Convergence.SwapVMedian
import Mathlib.Data.Fintype.EquivFin

namespace SSEM

variable {n : ℕ}

/-! ### Existence of an agent at any specific rank in InSrank -/

/-- Under `InSrank` with `n > 0`, for any rank `r < n` there exists an
agent occupying that rank. -/
theorem InSrank.exists_at_rank {C : Config (AgentState n) Opinion n}
    (hC : InSrank C) (hn : 0 < n) (r : Fin n) :
    ∃ v : Fin n, (C v).1.rank = r := by
  have hsurj : Function.Surjective (fun v => (C v).1.rank) :=
    Finite.injective_iff_surjective.mp hC.ranks_inj
  exact hsurj r

/-! ### Odd-n median-wrong witness -/

/-- For odd `n ≥ 3` and `InSswap C` with the median wrong AND the median's
timer ≥ 1, we construct the witness pair required by `hOddCase` of
`P_EM_solves_SSEM_full_modulo_burman`. -/
theorem oddCase_witness_when_median_wrong_with_timer
    {C : Config (AgentState n) Opinion n} (hC : InSswap C)
    (hpar : ¬ n % 2 = 0) (hn3 : 3 ≤ n)
    (h_med_wrong : ∃ μ : Fin n, (C μ).1.rank.val + 1 = ceilHalf n ∧
                                 (C μ).1.answer ≠ majorityAnswer C)
    (h_med_timer : ∀ μ : Fin n, (C μ).1.rank.val + 1 = ceilHalf n →
                                 1 ≤ (C μ).1.timer) :
    ∃ μ v : Fin n, μ ≠ v ∧
      (C μ).1.rank.val + 1 = ceilHalf n ∧
      (C v).1.rank.val + 1 ≠ ceilHalf n ∧
      (C v).1.rank.val + 1 ≠ n ∧
      (C v).1.rank < (C μ).1.rank ∧
      1 ≤ (C μ).1.timer ∧
      (C μ).1.answer ≠ majorityAnswer C := by
  obtain ⟨μ, hμ_med, hμ_wrong⟩ := h_med_wrong
  -- ceilHalf n for odd n = (n+1)/2 ≥ 2 for n ≥ 3.
  have h_ceil_ge_2 : 2 ≤ ceilHalf n := by unfold ceilHalf; omega
  -- Rank 0 < n for n ≥ 3.
  have h_n_pos : 0 < n := by omega
  -- Get the agent at rank 0.
  obtain ⟨v, hv_rank⟩ := hC.exists_at_rank h_n_pos ⟨0, by omega⟩
  refine ⟨μ, v, ?_, hμ_med, ?_, ?_, ?_, ?_, hμ_wrong⟩
  · -- μ ≠ v: μ at rank ceilHalf n - 1 ≥ 1, v at rank 0.
    intro h_eq
    rw [h_eq, hv_rank] at hμ_med
    -- hμ_med : (0 : Fin n).val + 1 = ceilHalf n, but (0 : Fin n).val = 0.
    simp at hμ_med
    omega
  · -- v not at median.
    rw [hv_rank]; simp; omega
  · -- v not at max (rank.val + 1 = 1 ≠ n for n ≥ 3).
    rw [hv_rank]; simp; omega
  · -- rank_v < rank_μ: 0 < ceilHalf n - 1.
    rw [hv_rank]
    apply Fin.mk_lt_of_lt_val
    show 0 < (C μ).1.rank.val
    omega
  · exact h_med_timer μ hμ_med

/-! ### Even-n median-pair witness -/

/-- For even `n ≥ 4` and `InSswap C` with strict majority and at least one
median (lower or upper) wrong, we construct the witness pair required by
`hEvenCase` of `P_EM_solves_SSEM_full_modulo_burman`. -/
theorem evenCase_witness_when_median_wrong
    {C : Config (AgentState n) Opinion n} (hC : InSswap C)
    (hpar : n % 2 = 0) (hn4 : 4 ≤ n)
    (hne : nAOf C ≠ nBOf C)
    (h_med_wrong : ∃ μ : Fin n, (C μ).1.rank.val + 1 = ceilHalf n ∧
                                 (C μ).1.answer ≠ majorityAnswer C) :
    ∃ u v : Fin n, u ≠ v ∧
      (C u).1.rank.val + 1 = n / 2 ∧
      (C v).1.rank.val + 1 = n / 2 + 1 ∧
      (C u).2 = (C v).2 ∧
      ((C u).1.answer ≠ majorityAnswer C ∨
       (C v).1.answer ≠ majorityAnswer C) := by
  -- Lower median = rank n/2 - 1; upper median = rank n/2.
  have h_n_pos : 0 < n := by omega
  -- ceilHalf n = n/2 for even n.
  have hceil : ceilHalf n = n / 2 := by unfold ceilHalf; omega
  -- Get the two median agents.
  have h_lower_lt : n / 2 - 1 < n := by omega
  have h_upper_lt : n / 2 < n := by omega
  obtain ⟨u, hu_rank⟩ := hC.exists_at_rank h_n_pos ⟨n / 2 - 1, h_lower_lt⟩
  obtain ⟨v, hv_rank⟩ := hC.exists_at_rank h_n_pos ⟨n / 2, h_upper_lt⟩
  -- u and v are distinct because their ranks differ.
  have huv : u ≠ v := by
    intro h_eq
    rw [h_eq] at hu_rank
    have h_v_eq : (C v).1.rank.val = n / 2 - 1 := by rw [hu_rank]
    have h_v_eq' : (C v).1.rank.val = n / 2 := by rw [hv_rank]
    omega
  -- u at lower median rank.
  have hu_med : (C u).1.rank.val + 1 = n / 2 := by
    rw [hu_rank]; simp; omega
  -- v at upper median rank.
  have hv_upper : (C v).1.rank.val + 1 = n / 2 + 1 := by
    rw [hv_rank]
  -- Inputs agree because both medians' inputs match the strict-majority side.
  -- Use input_rank: (C u).2 = .A iff rank_u < nAOf C.
  -- For strict majority: nA > n/2 or nB > n/2.
  -- Lower median rank = n/2 - 1 < nA (when nA majority) or ≥ nA (when nB majority).
  -- Upper median rank = n/2 < nA (when nA strict majority) or ≥ nA (otherwise).
  have h_inputs_agree : (C u).2 = (C v).2 := by
    have h_nA_total : nAOf C + nBOf C = n := nAOf_add_nBOf C
    have hu_rank_val : (C u).1.rank.val = n / 2 - 1 := by rw [hu_rank]
    have hv_rank_val : (C v).1.rank.val = n / 2 := by rw [hv_rank]
    by_cases h_nA_maj : nAOf C > n / 2
    · -- Strict A majority: both lower and upper median at rank < nA, so both .A.
      have hu_A : (C u).2 = Opinion.A := by
        apply (hC.input_rank u).mpr
        rw [hu_rank_val]; omega
      have hv_A : (C v).2 = Opinion.A := by
        apply (hC.input_rank v).mpr
        rw [hv_rank_val]; omega
      rw [hu_A, hv_A]
    · -- Not strict A majority.  Combined with nA ≠ nB and even n: nB > n/2.
      have h_nB_maj : nBOf C > n / 2 := by omega
      -- For nB strict majority: nA < n/2, so lower median rank n/2 - 1 ≥ nA, both .B.
      have h_nA_lt : nAOf C < n / 2 := by omega
      have hu_B : (C u).2 = Opinion.B := by
        rcases h_u_input : (C u).2 with _ | _
        · -- (C u).2 = .A → rank_u < nA
          have h_lt := (hC.input_rank u).mp h_u_input
          rw [hu_rank_val] at h_lt; omega
        · rfl
      have hv_B : (C v).2 = Opinion.B := by
        rcases h_v_input : (C v).2 with _ | _
        · have h_lt := (hC.input_rank v).mp h_v_input
          rw [hv_rank_val] at h_lt; omega
        · rfl
      rw [hu_B, hv_B]
  -- At least one of u, v is wrong.  We have h_med_wrong giving SOME agent at
  -- ceilHalf n rank = n/2 rank, which corresponds to u (lower median).
  obtain ⟨μ, hμ_med, hμ_wrong⟩ := h_med_wrong
  -- μ at ceilHalf n = n/2, i.e., rank.val + 1 = n/2.  Lower median rank
  -- value = n/2 - 1, so μ = u (by ranks_inj).
  have hu_rank_val : (C u).1.rank.val = n / 2 - 1 := by rw [hu_rank]
  have hμu : μ = u := by
    apply hC.ranks_inj
    apply Fin.eq_of_val_eq
    show (C μ).1.rank.val = (C u).1.rank.val
    rw [hu_rank_val, hceil] at *
    omega
  refine ⟨u, v, huv, hu_med, hv_upper, h_inputs_agree, Or.inl ?_⟩
  rw [← hμu]; exact hμ_wrong

/-! ### 5-way swap-step existence: covers ALL misorder patterns under timer ≥ 2 -/

/-- Discharges a 5-way version of `hSwapExists`: given InSrank, positive
misorderedCount, and median timer ≥ 2 (odd n only — the even-n median
pair is handled by the original four-way), every misorder pair admits
one of the five swap-step lemmas:
  (i) non-median misorder
  (ii) odd-n, u at median, v not max, timer ≥ 1
  (iii) odd-n, u at median, v at max, timer ≥ 2
  (v) odd-n, v at median, timer ≥ 1 (NEW)

The four-way disjunction's case (iv) (even-n median pair) is omitted
here — for odd n only. -/
theorem swap_step_exists_5way_odd_with_timer
    {C : Config (AgentState n) Opinion n} (hC : InSrank C)
    (hpar : ¬ n % 2 = 0) (hn3 : 3 ≤ n)
    (hpos : 0 < misorderedCount C)
    (h_med_timer_ge_2 :
      ∀ μ : Fin n, (C μ).1.rank.val + 1 = ceilHalf n → 2 ≤ (C μ).1.timer) :
    ∃ u v : Fin n, MisorderedPair C (u, v) ∧
      (((C u).1.rank.val + 1 ≠ ceilHalf n ∧
        (C v).1.rank.val + 1 ≠ ceilHalf n) ∨
       ((C u).1.rank.val + 1 = ceilHalf n ∧
        (C v).1.rank.val + 1 ≠ n ∧ 1 ≤ (C u).1.timer) ∨
       ((C u).1.rank.val + 1 = ceilHalf n ∧
        (C v).1.rank.val + 1 = n ∧ 2 ≤ (C u).1.timer) ∨
       ((C v).1.rank.val + 1 = ceilHalf n ∧ 1 ≤ (C v).1.timer)) := by
  -- Pick any misorder pair.
  obtain ⟨u, v, hMis⟩ := exists_misordered_of_pos_count hpos
  obtain ⟨huB, hvA, hlt⟩ := hMis
  refine ⟨u, v, ⟨huB, hvA, hlt⟩, ?_⟩
  -- Case analysis on whether u, v are at median.
  by_cases hu_med : (C u).1.rank.val + 1 = ceilHalf n
  · -- u at median.  Either v at max → case (iii), or v not at max → case (ii).
    have hu_timer : 2 ≤ (C u).1.timer := h_med_timer_ge_2 u hu_med
    by_cases hv_max : (C v).1.rank.val + 1 = n
    · -- Case (iii).
      right; right; left
      exact ⟨hu_med, hv_max, hu_timer⟩
    · -- Case (ii): timer ≥ 2 ⟹ ≥ 1.
      right; left
      exact ⟨hu_med, hv_max, by omega⟩
  · -- u not at median.  Check whether v at median.
    by_cases hv_med : (C v).1.rank.val + 1 = ceilHalf n
    · -- Case (v): v at median.
      have hv_timer : 2 ≤ (C v).1.timer := h_med_timer_ge_2 v hv_med
      right; right; right
      exact ⟨hv_med, by omega⟩
    · -- Case (i): non-median.
      left
      exact ⟨hu_med, hv_med⟩

/-! ### 8-way swap-step existence: parity-combined under timer ≥ 2 -/

/-- Under `InSrank ∧ misorderedCount > 0 ∧ median.timer ≥ 2` (and `n ≥ 4`
to handle even-n median pair structurally), every misorder pair admits one
of the eight sub-case disjuncts.  This is the parity-combined unconditional
existence theorem, discharging the 8-way variant of `hSwapExists`. -/
theorem swap_step_exists_8way_with_timer
    {C : Config (AgentState n) Opinion n} (hC : InSrank C)
    (hn4 : 4 ≤ n)
    (hpos : 0 < misorderedCount C)
    (h_med_timer_ge_2 :
      ∀ μ : Fin n, (C μ).1.rank.val + 1 = ceilHalf n → 2 ≤ (C μ).1.timer) :
    ∃ u v : Fin n, MisorderedPair C (u, v) ∧
      (((C u).1.rank.val + 1 ≠ ceilHalf n ∧
        (C v).1.rank.val + 1 ≠ ceilHalf n) ∨
       (¬ n % 2 = 0 ∧ (C u).1.rank.val + 1 = ceilHalf n ∧
        (C v).1.rank.val + 1 ≠ n ∧ 1 ≤ (C u).1.timer) ∨
       (¬ n % 2 = 0 ∧ (C u).1.rank.val + 1 = ceilHalf n ∧
        (C v).1.rank.val + 1 = n ∧ 2 ≤ (C u).1.timer) ∨
       (n % 2 = 0 ∧ (C u).1.rank.val + 1 = n / 2 ∧
        (C v).1.rank.val + 1 = n / 2 + 1 ∧ 4 ≤ n) ∨
       (¬ n % 2 = 0 ∧ (C v).1.rank.val + 1 = ceilHalf n ∧
        1 ≤ (C v).1.timer) ∨
       (n % 2 = 0 ∧ (C v).1.rank.val + 1 = n / 2 ∧
        1 ≤ (C v).1.timer ∧ 4 ≤ n) ∨
       (n % 2 = 0 ∧ (C u).1.rank.val + 1 = n / 2 ∧
        (C v).1.rank.val + 1 ≠ n / 2 + 1 ∧ (C v).1.rank.val + 1 ≠ n ∧
        1 ≤ (C u).1.timer ∧ 4 ≤ n) ∨
       (n % 2 = 0 ∧ (C u).1.rank.val + 1 = n / 2 ∧
        (C v).1.rank.val + 1 = n ∧ 2 ≤ (C u).1.timer ∧ 4 ≤ n)) := by
  obtain ⟨u, v, hMis⟩ := exists_misordered_of_pos_count hpos
  obtain ⟨huB, hvA, hlt⟩ := hMis
  refine ⟨u, v, ⟨huB, hvA, hlt⟩, ?_⟩
  -- Parity case-split.
  by_cases hpar : n % 2 = 0
  · -- Even n.  ceilHalf n = n / 2.
    have hceil : ceilHalf n = n / 2 := by unfold ceilHalf; omega
    by_cases hu_med : (C u).1.rank.val + 1 = ceilHalf n
    · -- u at lower median.  hu_med (in n/2 form): (C u).1.rank.val + 1 = n/2.
      have hu_med' : (C u).1.rank.val + 1 = n / 2 := by rw [← hceil]; exact hu_med
      have hu_timer : 2 ≤ (C u).1.timer := h_med_timer_ge_2 u hu_med
      -- v.rank > u.rank means v.rank ≥ n/2.
      by_cases hv_upper : (C v).1.rank.val + 1 = n / 2 + 1
      · -- (iv).
        right; right; right; left
        exact ⟨hpar, hu_med', hv_upper, hn4⟩
      · by_cases hv_max : (C v).1.rank.val + 1 = n
        · -- (viii).
          right; right; right; right; right; right; right
          exact ⟨hpar, hu_med', hv_max, hu_timer, hn4⟩
        · -- (vii).
          right; right; right; right; right; right; left
          exact ⟨hpar, hu_med', hv_upper, hv_max, by omega, hn4⟩
    · by_cases hv_med : (C v).1.rank.val + 1 = ceilHalf n
      · -- v at lower median.  (vi).
        have hv_med' : (C v).1.rank.val + 1 = n / 2 := by rw [← hceil]; exact hv_med
        have hv_timer : 2 ≤ (C v).1.timer := h_med_timer_ge_2 v hv_med
        right; right; right; right; right; left
        exact ⟨hpar, hv_med', by omega, hn4⟩
      · -- Both non-median.  (i).
        left
        exact ⟨hu_med, hv_med⟩
  · -- Odd n.  Use the 5-way odd-only lemma's logic.
    have hn3 : 3 ≤ n := by omega
    by_cases hu_med : (C u).1.rank.val + 1 = ceilHalf n
    · have hu_timer : 2 ≤ (C u).1.timer := h_med_timer_ge_2 u hu_med
      by_cases hv_max : (C v).1.rank.val + 1 = n
      · right; right; left
        exact ⟨hpar, hu_med, hv_max, hu_timer⟩
      · right; left
        exact ⟨hpar, hu_med, hv_max, by omega⟩
    · by_cases hv_med : (C v).1.rank.val + 1 = ceilHalf n
      · have hv_timer : 2 ≤ (C v).1.timer := h_med_timer_ge_2 v hv_med
        right; right; right; right; left
        exact ⟨hpar, hv_med, by omega⟩
      · left
        exact ⟨hu_med, hv_med⟩

/-! ### Fully-discharged swap-phase reachability (modulo median.timer ≥ 2 invariant) -/

/-- The 8-way existence theorem combined with the 8-way reachability lift
gives a swap-phase reachability that requires only the structural invariant
"every InSrank intermediate state has median timer ≥ 2".

This is the closest to "unconditional" swap-phase reachability we can get
without the macro-step reset cycle (which is needed when timer drops to 0). -/
theorem swap_reaches_Sswap_via_8way_with_timer_invariant
    [Inhabited (Fin n × Fin n)]
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    (hn4 : 4 ≤ n)
    (h_med_timer : ∀ C : Config (AgentState n) Opinion n, InSrank C →
                    ∀ μ : Fin n, (C μ).1.rank.val + 1 = ceilHalf n →
                    2 ≤ (C μ).1.timer) :
    ∀ C : Config (AgentState n) Opinion n, InSrank C →
      ∃ (γ : DetScheduler n) (t : ℕ),
        InSswap (execution (protocolPEM n trank Rmax rankDelta) C γ t) :=
  swap_reaches_Sswap_via_eight_way hRank
    (fun C hC hpos =>
      swap_step_exists_8way_with_timer hC hn4 hpos (h_med_timer C hC))

/-! ### Fully-discharged Theorem 4 (modulo Burman + invariants only) -/

/-- Theorem 4 with maximally discharged hypotheses (odd `n ≥ 3` version):
  * `RankDeltaSettledFix` (trivial),
  * Burman ranking convergence (`h_burman_ranking`),
  * `BurmanMacroDecision` (residual macro-step),
  * Two structural invariants on intermediate states.

The swap-step and decision-step witnesses are FULLY discharged via the
existence theorems; only the structural invariants and Burman remain
as parameters.

This bypasses the 4-way `P_EM_solves_SSEM_full_odd_modulo_burman` and
directly composes 8-way swap reachability with the existing decision
reachability via the unified phase-composition. -/
theorem P_EM_solves_SSEM_fully_discharged_odd_modulo_burman
    [Inhabited (Fin n × Fin n)]
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    (hpar : ¬ n % 2 = 0)
    (hn4 : 4 ≤ n)
    (hBurman : BurmanMacroDecision trank Rmax rankDelta)
    (h_burman_ranking : ∀ C₀ : Config (AgentState n) Opinion n,
      ∃ (γ : DetScheduler n) (t : ℕ),
        InSrank (execution (protocolPEM n trank Rmax rankDelta) C₀ γ t))
    -- Invariant 1: InSrank intermediates have median.timer ≥ 2.
    (h_inv_swap : ∀ C : Config (AgentState n) Opinion n, InSrank C →
                    ∀ μ : Fin n, (C μ).1.rank.val + 1 = ceilHalf n →
                    2 ≤ (C μ).1.timer)
    -- Invariant 2: InSswap intermediates have median.timer ≥ 1.
    (h_inv_dec : ∀ C : Config (AgentState n) Opinion n, InSswap C →
                  ∀ μ : Fin n, (C μ).1.rank.val + 1 = ceilHalf n →
                  1 ≤ (C μ).1.timer) :
    SolvesSSEM (protocolPEM n trank Rmax rankDelta) n := by
  have hn3 : 3 ≤ n := by omega
  apply P_EM_solves_SSEM_via_phases hRank h_burman_ranking
    (swap_reaches_Sswap_via_8way_with_timer_invariant hRank hn4 h_inv_swap)
  intro C hC
  have h_med_correct_or_wrong : (∀ μ : Fin n, (C μ).1.rank.val + 1 = ceilHalf n →
                                  (C μ).1.answer = majorityAnswer C) ∨
                                 (∃ μ : Fin n, (C μ).1.rank.val + 1 = ceilHalf n ∧
                                              (C μ).1.answer ≠ majorityAnswer C) := by
    classical
    by_cases h : ∃ μ : Fin n, (C μ).1.rank.val + 1 = ceilHalf n ∧
                              (C μ).1.answer ≠ majorityAnswer C
    · exact Or.inr h
    · push_neg at h
      exact Or.inl h
  rcases h_med_correct_or_wrong with h_med_correct | h_med_wrong
  · -- Median is correct.  Use Burman macro.
    by_cases h_consensus : wrongAnswerCount C = 0
    · -- Already consensus.
      refine ⟨fun _ => default, 0, ?_⟩
      exact isConsensusConfig_of_InSswap_of_wrongAnswerCount_zero hC h_consensus
    · -- Use BurmanMacroDecision.
      have hpos : 0 < wrongAnswerCount C := by omega
      have hMacro : ∀ C' : Config (AgentState n) Opinion n,
          InSswap C' → 0 < wrongAnswerCount C' →
          ∃ (γ : DetScheduler n) (k : ℕ),
            InSswap (execution (protocolPEM n trank Rmax rankDelta) C' γ k) ∧
            wrongAnswerCount (execution (protocolPEM n trank Rmax rankDelta) C' γ k)
              < wrongAnswerCount C' := by
        intro C' hC' hpos'
        classical
        by_cases h_med' : ∃ μ : Fin n, (C' μ).1.rank.val + 1 = ceilHalf n ∧
                                       (C' μ).1.answer ≠ majorityAnswer C'
        · -- Use median-wrong single-step.
          obtain ⟨μ, v, hμv, hμ_med, hv_no_med, hv_no_max, h_rank_gt, h_timer, hμ_wrong⟩ :=
            oddCase_witness_when_median_wrong_with_timer hC' hpar hn3 h_med' (h_inv_dec C' hC')
          refine ⟨fun _ => (μ, v), 1, ?_, ?_⟩
          · show InSswap (C'.step (protocolPEM n trank Rmax rankDelta) μ v)
            exact (decision_step_at_median_no_swap_odd_decreases
              hRank hC' hμv hpar hμ_med hv_no_med hv_no_max h_rank_gt h_timer hμ_wrong).1
          · show wrongAnswerCount (C'.step (protocolPEM n trank Rmax rankDelta) μ v) < _
            exact (decision_step_at_median_no_swap_odd_decreases
              hRank hC' hμv hpar hμ_med hv_no_med hv_no_max h_rank_gt h_timer hμ_wrong).2
        · push_neg at h_med'
          exact hBurman C' hC' hpos' h_med'
      exact decision_reaches_consensus_of_macroStep
        (trank := trank) (Rmax := Rmax) (rankDelta := rankDelta) hMacro C hC
  · -- Median is wrong.  Use E2 + decision_step.
    by_cases h_consensus : wrongAnswerCount C = 0
    · refine ⟨fun _ => default, 0, ?_⟩
      exact isConsensusConfig_of_InSswap_of_wrongAnswerCount_zero hC h_consensus
    · have hpos : 0 < wrongAnswerCount C := by omega
      -- Same macro-step argument as above.
      have hMacro : ∀ C' : Config (AgentState n) Opinion n,
          InSswap C' → 0 < wrongAnswerCount C' →
          ∃ (γ : DetScheduler n) (k : ℕ),
            InSswap (execution (protocolPEM n trank Rmax rankDelta) C' γ k) ∧
            wrongAnswerCount (execution (protocolPEM n trank Rmax rankDelta) C' γ k)
              < wrongAnswerCount C' := by
        intro C' hC' hpos'
        classical
        by_cases h_med' : ∃ μ : Fin n, (C' μ).1.rank.val + 1 = ceilHalf n ∧
                                       (C' μ).1.answer ≠ majorityAnswer C'
        · obtain ⟨μ, v, hμv, hμ_med, hv_no_med, hv_no_max, h_rank_gt, h_timer, hμ_wrong⟩ :=
            oddCase_witness_when_median_wrong_with_timer hC' hpar hn3 h_med' (h_inv_dec C' hC')
          refine ⟨fun _ => (μ, v), 1, ?_, ?_⟩
          · show InSswap (C'.step (protocolPEM n trank Rmax rankDelta) μ v)
            exact (decision_step_at_median_no_swap_odd_decreases
              hRank hC' hμv hpar hμ_med hv_no_med hv_no_max h_rank_gt h_timer hμ_wrong).1
          · show wrongAnswerCount (C'.step (protocolPEM n trank Rmax rankDelta) μ v) < _
            exact (decision_step_at_median_no_swap_odd_decreases
              hRank hC' hμv hpar hμ_med hv_no_med hv_no_max h_rank_gt h_timer hμ_wrong).2
        · push_neg at h_med'
          exact hBurman C' hC' hpos' h_med'
      exact decision_reaches_consensus_of_macroStep
        (trank := trank) (Rmax := Rmax) (rankDelta := rankDelta) hMacro C hC

/-! ### Even-n companion: maximally discharged Theorem 4 -/

/-- Even `n ≥ 4` companion of `P_EM_solves_SSEM_fully_discharged_odd_modulo_burman`.
Same structure but uses even-n median pair for the median-wrong decision case
and requires a strict-majority hypothesis (so the median pair's input
matches the majority side). -/
theorem P_EM_solves_SSEM_fully_discharged_even_modulo_burman
    [Inhabited (Fin n × Fin n)]
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    (hpar : n % 2 = 0)
    (hn4 : 4 ≤ n)
    (hStrictMajority : ∀ C : Config (AgentState n) Opinion n,
                          InSswap C → nAOf C ≠ nBOf C)
    (hBurman : BurmanMacroDecision trank Rmax rankDelta)
    (h_burman_ranking : ∀ C₀ : Config (AgentState n) Opinion n,
      ∃ (γ : DetScheduler n) (t : ℕ),
        InSrank (execution (protocolPEM n trank Rmax rankDelta) C₀ γ t))
    (h_inv_swap : ∀ C : Config (AgentState n) Opinion n, InSrank C →
                    ∀ μ : Fin n, (C μ).1.rank.val + 1 = ceilHalf n →
                    2 ≤ (C μ).1.timer) :
    SolvesSSEM (protocolPEM n trank Rmax rankDelta) n := by
  apply P_EM_solves_SSEM_via_phases hRank h_burman_ranking
    (swap_reaches_Sswap_via_8way_with_timer_invariant hRank hn4 h_inv_swap)
  intro C hC
  -- Use the macro-step decision interface with case-split on median wrong/correct.
  have hMacro : ∀ C' : Config (AgentState n) Opinion n,
      InSswap C' → 0 < wrongAnswerCount C' →
      ∃ (γ : DetScheduler n) (k : ℕ),
        InSswap (execution (protocolPEM n trank Rmax rankDelta) C' γ k) ∧
        wrongAnswerCount (execution (protocolPEM n trank Rmax rankDelta) C' γ k)
          < wrongAnswerCount C' := by
    intro C' hC' hpos'
    classical
    by_cases h_med' : ∃ μ : Fin n, (C' μ).1.rank.val + 1 = ceilHalf n ∧
                                   (C' μ).1.answer ≠ majorityAnswer C'
    · -- Use even-n median-pair witness + decision step.
      obtain ⟨u, v, huv, hu_med, hv_upper, h_inputs_agree, h_one_wrong⟩ :=
        evenCase_witness_when_median_wrong hC' hpar hn4 (hStrictMajority C' hC') h_med'
      refine ⟨fun _ => (u, v), 1, ?_, ?_⟩
      · show InSswap (C'.step (protocolPEM n trank Rmax rankDelta) u v)
        exact (decision_step_at_median_pair_even_decreases
          hRank hC' huv hpar hu_med hv_upper h_inputs_agree
          (hStrictMajority C' hC') hn4 h_one_wrong).1
      · show wrongAnswerCount (C'.step (protocolPEM n trank Rmax rankDelta) u v) < _
        exact (decision_step_at_median_pair_even_decreases
          hRank hC' huv hpar hu_med hv_upper h_inputs_agree
          (hStrictMajority C' hC') hn4 h_one_wrong).2
    · push_neg at h_med'
      exact hBurman C' hC' hpos' h_med'
  exact decision_reaches_consensus_of_macroStep
    (trank := trank) (Rmax := Rmax) (rankDelta := rankDelta) hMacro C hC

/-! ### Combined parity-agnostic version -/

/-- Combined fully-discharged Theorem 4 (parity-agnostic, n ≥ 4):
case-splits on parity internally and dispatches to the appropriate
parity-specific master.  The strict-majority hypothesis is only needed
for even `n` (carried unconditionally as a hypothesis here for simplicity). -/
theorem P_EM_solves_SSEM_fully_discharged_modulo_burman
    [Inhabited (Fin n × Fin n)]
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    (hn4 : 4 ≤ n)
    (hStrictMajority : ∀ C : Config (AgentState n) Opinion n,
                          InSswap C → nAOf C ≠ nBOf C)
    (hBurman : BurmanMacroDecision trank Rmax rankDelta)
    (h_burman_ranking : ∀ C₀ : Config (AgentState n) Opinion n,
      ∃ (γ : DetScheduler n) (t : ℕ),
        InSrank (execution (protocolPEM n trank Rmax rankDelta) C₀ γ t))
    (h_inv_swap : ∀ C : Config (AgentState n) Opinion n, InSrank C →
                    ∀ μ : Fin n, (C μ).1.rank.val + 1 = ceilHalf n →
                    2 ≤ (C μ).1.timer)
    (h_inv_dec : ∀ C : Config (AgentState n) Opinion n, InSswap C →
                  ∀ μ : Fin n, (C μ).1.rank.val + 1 = ceilHalf n →
                  1 ≤ (C μ).1.timer) :
    SolvesSSEM (protocolPEM n trank Rmax rankDelta) n := by
  by_cases hpar : n % 2 = 0
  · exact P_EM_solves_SSEM_fully_discharged_even_modulo_burman
      hRank hpar hn4 hStrictMajority hBurman h_burman_ranking h_inv_swap
  · exact P_EM_solves_SSEM_fully_discharged_odd_modulo_burman
      hRank hpar hn4 hBurman h_burman_ranking h_inv_swap h_inv_dec

end SSEM
