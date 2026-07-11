/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Polynomial expected-time bounds for SSExactMajority

This file proves the polynomial expected-time bounds for the
median-correct → consensus phase of the PEM protocol.

## Main results

* `timer_ge_two_descent_step` — the timer≥2 descent for deterministic_descent
* `PEM_expected_timer_drain_poly` — timer drain: E[T] ≤ T_timer·n(n-1)
* `PEM_expected_epidemic_to_consensus_poly` — epidemic: E[T] < ⊤ (finite)
* `PEM_expected_median_correct_to_consensus_poly` — composition: E[T] < ⊤ (finite)
-/

import Ripple.PopulationProtocol.Majority.SSEM.UpperBound.Time.PhaseProofs
import Ripple.PopulationProtocol.Majority.SSEM.UpperBound.Time.RecoveryBound

namespace SSEM

open scoped ENNReal

noncomputable def maxMedianTimer (C : Config (AgentState n) Opinion n) : ℕ :=
  Finset.sup Finset.univ
    (fun μ : Fin n => if (C μ).1.rank.val + 1 = ceilHalf n then (C μ).1.timer else 0)

/-! ## Timer drain: close the timer≥2 gap

From InSswap + MedianCorrect + timer≥1 + timer bounded:
E[T to consensus ∨ CRS ∨ ¬(InSswap ∧ timer≥1)] ≤ T_timer·n(n-1).

The proof uses deterministic descent on `maxMedianTimer` (defined in Time.lean).
The timer=1 case was already closed in Time.lean.
The timer≥2 case requires: at step (median, max), InSswap is preserved,
MedianCorrect is preserved, timer drops by 1 (so timer≥1 since timer was ≥2),
and maxMedianTimer strictly decreases.

We prove the timer≥2 descent step here, then use it to close the gap
in the full timer drain theorem. -/

/-! ### Timer≥2 descent step

When InSswap holds and median timer ≥ 2, the step at (median, max-rank)
either preserves Inv and strictly decreases maxMedianTimer, or reaches Goal
(if InSswap breaks, CRS is created). -/

set_option maxHeartbeats 8000000 in
theorem timer_ge_two_descent_step
    {n Rmax Emax Dmax : ℕ}
    (hn4 : 4 ≤ n) [Inhabited (Fin n × Fin n)] (hn0 : 0 < n) (hRmax : n ≤ Rmax)
    {D : Config (AgentState n) Opinion n}
    (hS : InSswap D) (hM : MedianAnswerCorrect D) (hT : MedianTimerAtLeast 1 D)
    {μ v : Fin n}
    (hμ_med : (D μ).1.rank.val + 1 = ceilHalf n)
    (hv_max : (D v).1.rank.val + 1 = n)
    (huv : μ ≠ v)
    (hTimer2 : 2 ≤ (D μ).1.timer) :
    let P := PEMProtocolCoupled n Rmax Emax Dmax hn0
    let Goal := fun D' : Config (AgentState n) Opinion n =>
      IsConsensusConfig D' ∨ CorrectResetSeed D' ∨
        ¬ (InSswap D' ∧ MedianTimerAtLeast 1 D')
    let Inv := fun D' : Config (AgentState n) Opinion n =>
      InSswap D' ∧ MedianAnswerCorrect D' ∧ MedianTimerAtLeast 1 D'
    ((Inv (D.step P μ v) ∧ maxMedianTimer (D.step P μ v) < maxMedianTimer D) ∨
      Goal (D.step P μ v)) := by
  set P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  set Goal := fun D' : Config (AgentState n) Opinion n =>
    IsConsensusConfig D' ∨ CorrectResetSeed D' ∨
      ¬ (InSswap D' ∧ MedianTimerAtLeast 1 D')
  set Inv := fun D' : Config (AgentState n) Opinion n =>
    InSswap D' ∧ MedianAnswerCorrect D' ∧ MedianTimerAtLeast 1 D'
  have h_no_swap := hS.swap_condition_false μ v
  have hRD := rankDeltaOSSR_satisfies_fix (Rmax := Rmax) (Emax := Emax)
    (Dmax := Dmax) (hn := hn0)
  -- First check if InSswap is preserved
  by_cases hS' : InSswap (D.step P μ v)
  · -- InSswap preserved: show Inv preserved and maxMedianTimer strictly decreased
    left
    have hM' : MedianAnswerCorrect (D.step P μ v) :=
      step_median_answer_of_InSswap_both hn0 hn4 hS hS' hM
    -- Rank is preserved at μ
    have hμ_rank_post : (D.step P μ v μ).1.rank.val + 1 = ceilHalf n := by
      rw [step_rank_preserved_of_InSswap (Rmax := Rmax) (Emax := Emax)
        (Dmax := Dmax) hn0 hS μ]
      exact hμ_med
    -- Timer at μ decreases (step_timer_le gives ≤, and we'll show strict decrease)
    have h_timer_le : (D.step P μ v μ).1.timer ≤ (D μ).1.timer :=
      step_timer_le_of_InSswap (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) hn0 hS μ
    -- For strict decrease: show timer(step μ) < timer(D μ) by transition unfolding.
    -- The step at (median, max) with timer ≥ 2 decrements the timer by exactly 1.
    have h_fst := Config.step_fst_state P D huv
    have h_timer_eq : (D.step P μ v μ).1.timer = (D μ).1.timer - 1 := by
      -- Unfold the transition to show timer decrements by exactly 1
      rw [show (D.step P μ v μ).1.timer = ((P.δ (D μ, D v)).1).timer from
        congrArg AgentState.timer h_fst]
      show (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
        (D μ, D v)).1.timer = (D μ).1.timer - 1
      have hsi := hS.toInSrank.allSettled μ
      have hsv := hS.toInSrank.allSettled v
      have hne := fun h : (D μ).1.rank = (D v).1.rank => huv (hS.toInSrank.ranks_inj h)
      have hRDapp := hRD (D μ).1 (D v).1 hsi hsv hne
      unfold transitionPEM transitionPEM_phase4 transitionPEM_prePhase4
        phase4_swap phase4_decide phase4_propagate
      simp only [hRDapp, hsi, hsv, ne_eq,
        role_settled_ne_resetting,
        not_true_eq_false, not_false_eq_true,
        false_and, and_false, if_false,
        and_self, if_true, h_no_swap, hμ_med, hv_max]
      by_cases hpar : n % 2 = 0
      · simp only [hpar, if_true]
        split_ifs <;> dsimp only [] <;> omega
      · simp only [hpar, if_false]
        split_ifs <;> dsimp only [] <;> omega
    -- Timer at μ ≥ 1 post-step (since pre-step ≥ 2 and drop is at most 1)
    have hTimer1' : MedianTimerAtLeast 1 (D.step P μ v) := by
      intro ν hν
      -- The unique median post-step is μ (by rank injectivity of InSswap)
      have hνμ : ν = μ := by
        apply hS'.toInSrank.ranks_inj
        exact Fin.ext (show (D.step P μ v ν).1.rank.val = (D.step P μ v μ).1.rank.val by omega)
      subst hνμ
      omega
    -- maxMedianTimer strictly decreases
    have hmm_ge : (D μ).1.timer ≤ maxMedianTimer D :=
      Finset.le_sup_of_le (Finset.mem_univ μ) (by simp [maxMedianTimer, hμ_med])
    have hmm_le : maxMedianTimer (D.step P μ v) ≤ (D μ).1.timer - 1 := by
      unfold maxMedianTimer
      apply Finset.sup_le
      intro w _
      split_ifs with hw_med
      · have hwμ : w = μ := by
          apply hS'.toInSrank.ranks_inj
          exact Fin.ext (show (D.step P μ v w).1.rank.val = (D.step P μ v μ).1.rank.val by omega)
        subst hwμ
        exact le_of_eq h_timer_eq
      · exact Nat.zero_le _
    exact ⟨⟨hS', hM', hTimer1'⟩, by omega⟩
  · -- InSswap broke: CRS is created
    right
    exact Or.inr (Or.inl (crs_of_InSswap_break_with_MedC hn4 hn0 hRmax hS hM hS'))


/-! ## Full timer drain (polynomial bound)

This re-proves PEM_expected_timer_drain from Time.lean with the timer≥2
gap closed, using timer_ge_two_descent_step above. -/

set_option maxHeartbeats 16000000 in
theorem PEM_expected_timer_drain_poly
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n) (hRmax : n ≤ Rmax)
    (T_timer : ℕ)
    (C : Config (AgentState n) Opinion n)
    (hSswap : InSswap C)
    (hMedCorrect : MedianAnswerCorrect C)
    (hTimerLo : MedianTimerAtLeast 1 C)
    (hTimerHi : IsTimerBoundedConfig T_timer C) :
    Probability.expectedHittingTime
      (PEMProtocolCoupled n Rmax Emax Dmax hn0)
      (by omega : 2 ≤ n) C
      (fun D => IsConsensusConfig D ∨ CorrectResetSeed D ∨
        ¬ (InSswap D ∧ MedianTimerAtLeast 1 D)) ≤
      ((T_timer * n * (n - 1) : ℕ) : ENNReal) := by
  classical
  set P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  set Goal := fun D : Config (AgentState n) Opinion n =>
    IsConsensusConfig D ∨ CorrectResetSeed D ∨
      ¬ (InSswap D ∧ MedianTimerAtLeast 1 D)
  set Inv := fun D : Config (AgentState n) Opinion n =>
    InSswap D ∧ MedianAnswerCorrect D ∧ MedianTimerAtLeast 1 D
  have hBridge := Probability.expectedHittingTime_le_of_deterministic_descent
    P (by omega : 2 ≤ n) C Goal Inv maxMedianTimer
    ⟨hSswap, hMedCorrect, hTimerLo⟩
    (by -- hZeroGoal: Inv D ∧ maxMedianTimer D = 0 → Goal D
        intro D ⟨hSwap_D, _, _⟩ h0
        exact Or.inr (Or.inr (fun ⟨_, hT1⟩ => by
          have hInj := hSwap_D.ranks_inj
          have hSurj : Function.Surjective (fun v => (D v).1.rank) :=
            Finite.surjective_of_injective hInj
          have hCeilPos : 1 ≤ ceilHalf n := by unfold ceilHalf; omega
          have hCeil : (ceilHalf n : ℕ) - 1 < n := by unfold ceilHalf; omega
          obtain ⟨μ, hμ⟩ := hSurj ⟨ceilHalf n - 1, hCeil⟩
          have hμ_med : (D μ).1.rank.val + 1 = ceilHalf n := by
            have hval : (D μ).1.rank.val = ceilHalf n - 1 := congr_arg Fin.val hμ
            omega
          have h1 := hT1 μ hμ_med
          have h2 : (D μ).1.timer ≤ maxMedianTimer D := by
            unfold maxMedianTimer
            exact Finset.le_sup_of_le (Finset.mem_univ μ) (by simp [hμ_med])
          omega)))
    (by -- hInvStep: Inv D → ¬Goal D → ∀ i j, Inv(step) ∨ Goal(step)
        intro D ⟨hS, hM, hT⟩ hG i j
        by_cases hS' : InSswap (D.step P i j)
        · by_cases hT' : MedianTimerAtLeast 1 (D.step P i j)
          · by_cases hM' : MedianAnswerCorrect (D.step P i j)
            · exact Or.inl ⟨hS', hM', hT'⟩
            · exact absurd (step_median_answer_of_InSswap_both hn0 hn4 hS hS' hM) hM'
          · exact Or.inr (Or.inr (Or.inr (fun h => hT' h.2)))
        · exact Or.inr (Or.inr (Or.inr (fun h => hS' h.1))))
    (by -- hNonincrease: maxMedianTimer doesn't increase
        intro D ⟨hS, hM, hT⟩ hG i j
        unfold maxMedianTimer
        apply Finset.sup_le
        intro μ _
        split_ifs with hμ_med
        · by_cases hij : i = j
          · subst hij; simp only [Config.step, ite_true] at hμ_med ⊢
            exact Finset.le_sup_of_le (Finset.mem_univ μ) (by simp [hμ_med])
          · by_cases hμi : μ = i
            · rw [hμi]
              have hrank : (D.step P i j i).1.rank = (D i).1.rank :=
                step_rank_preserved_of_InSswap (Rmax := Rmax) (Emax := Emax)
                  (Dmax := Dmax) hn0 hS i
              have hμ_pre : (D i).1.rank.val + 1 = ceilHalf n := by
                rw [← hrank]; rwa [hμi] at hμ_med
              calc (D.step P i j i).1.timer
                  ≤ (D i).1.timer :=
                    step_timer_le_of_InSswap (Rmax := Rmax) (Emax := Emax)
                      (Dmax := Dmax) hn0 hS i
                _ ≤ maxMedianTimer D :=
                    Finset.le_sup_of_le (Finset.mem_univ i) (by simp [maxMedianTimer, hμ_pre])
            · by_cases hμj : μ = j
              · rw [hμj]
                have hrank : (D.step P i j j).1.rank = (D j).1.rank :=
                  step_rank_preserved_of_InSswap (Rmax := Rmax) (Emax := Emax)
                    (Dmax := Dmax) hn0 hS j
                have hμ_pre : (D j).1.rank.val + 1 = ceilHalf n := by
                  rw [← hrank]; rwa [hμj] at hμ_med
                calc (D.step P i j j).1.timer
                    ≤ (D j).1.timer :=
                      step_timer_le_of_InSswap (Rmax := Rmax) (Emax := Emax)
                        (Dmax := Dmax) hn0 hS j
                  _ ≤ maxMedianTimer D :=
                      Finset.le_sup_of_le (Finset.mem_univ j) (by simp [maxMedianTimer, hμ_pre])
              · have hbyst : D.step P i j μ = D μ := by
                  unfold Config.step; simp [hij, hμi, hμj]
                rw [show (D.step P i j μ).1.timer = (D μ).1.timer from
                  congrArg (fun x => x.1.timer) hbyst]
                rw [show (D.step P i j μ).1.rank = (D μ).1.rank from
                  congrArg (fun x => x.1.rank) hbyst] at hμ_med
                exact Finset.le_sup_of_le (Finset.mem_univ μ) (by simp [hμ_med])
        · exact Nat.zero_le _)
    (by -- hDescent: ∃ (median,max) pair that decrements timer
        intro D ⟨hS, hM, hT⟩ hG hφ
        have hn_pos : 0 < n := by omega
        obtain ⟨μ, hμ_med⟩ := hS.toInSrank.exists_median hn_pos
        have hsurj : Function.Surjective (fun v => (D v).1.rank) :=
          Finite.injective_iff_surjective.mp hS.toInSrank.ranks_inj
        have hn_bound : n - 1 < n := by omega
        obtain ⟨v, hv_eq⟩ := hsurj ⟨n - 1, hn_bound⟩
        have hv_max : (D v).1.rank.val + 1 = n := by
          have h := congrArg Fin.val hv_eq; simp only [Fin.val_mk] at h; omega
        have huv : μ ≠ v := by
          intro h; subst h
          have : ceilHalf n = n := by omega
          have : ceilHalf n ≤ (n + 1) / 2 := by unfold ceilHalf; omega
          omega
        refine ⟨μ, v, huv, ?_⟩
        have hTimerPos : 1 ≤ (D μ).1.timer := hT μ hμ_med
        by_cases hTimer2 : 2 ≤ (D μ).1.timer
        · -- Timer ≥ 2: use the descent lemma
          exact timer_ge_two_descent_step hn4 hn0 hRmax hS hM hT hμ_med hv_max huv hTimer2
        · -- Timer = 1: step decrements to 0 → Goal (¬(InSswap ∧ timer≥1))
          have hTimer1 : (D μ).1.timer = 1 := by omega
          right  -- Goal (D.step P μ v)
          right; right  -- ¬(InSswap ∧ timer≥1)
          intro ⟨hS', hT'⟩
          have hμ_rank_post : (D.step P μ v μ).1.rank.val + 1 = ceilHalf n := by
            rw [step_rank_preserved_of_InSswap (Rmax := Rmax) (Emax := Emax)
              (Dmax := Dmax) hn0 hS μ]; exact hμ_med
          have h_fst := Config.step_fst_state P D huv
          have hμ_timer_post : (D.step P μ v μ).1.timer = 0 := by
            rw [show (D.step P μ v μ).1.timer = ((P.δ (D μ, D v)).1).timer from
              congrArg AgentState.timer h_fst]
            show (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
              (D μ, D v)).1.timer = 0
            have hsi := hS.toInSrank.allSettled μ
            have hsv := hS.toInSrank.allSettled v
            have hne := fun h : (D μ).1.rank = (D v).1.rank => huv (hS.toInSrank.ranks_inj h)
            have hRDapp := rankDeltaOSSR_satisfies_fix (Rmax := Rmax) (Emax := Emax)
              (Dmax := Dmax) (hn := hn0) (D μ).1 (D v).1 hsi hsv hne
            have h_no_swap := hS.swap_condition_false μ v
            unfold transitionPEM transitionPEM_phase4 transitionPEM_prePhase4
              phase4_swap phase4_decide phase4_propagate
            simp only [hRDapp, hsi, hsv, ne_eq,
              role_settled_ne_resetting,
              not_true_eq_false, not_false_eq_true,
              false_and, and_false, if_false,
              and_self, if_true, h_no_swap, hμ_med, hv_max, hTimer1]
            by_cases hpar : n % 2 = 0
            · simp only [hpar, if_true]
              split_ifs <;> dsimp only [] <;> omega
            · simp only [hpar, if_false]
              split_ifs <;> dsimp only [] <;> omega
          have h0 := hT' μ hμ_rank_post
          omega)
  have hMaxTimer : maxMedianTimer C ≤ T_timer := by
    unfold maxMedianTimer
    apply Finset.sup_le
    intro μ _
    split_ifs with h
    · exact hTimerHi μ
    · exact Nat.zero_le _
  calc Probability.expectedHittingTime P (by omega) C Goal
      ≤ ↑(maxMedianTimer C) * ((n * (n - 1) : ℕ) : ENNReal) := hBridge
    _ ≤ ((T_timer * n * (n - 1) : ℕ) : ENNReal) := by
        norm_cast
        calc maxMedianTimer C * (n * (n - 1))
            ≤ T_timer * (n * (n - 1)) :=
              Nat.mul_le_mul_right _ hMaxTimer
          _ = T_timer * n * (n - 1) := by ring


/-! ## Epidemic bound

From CorrectResetSeed, E[T to consensus] ≤ 3·Rmax·n².

This is the hardest bound. The difficulty is that CorrectResetSeed is NOT
necessarily preserved by arbitrary protocol steps — only by specific
(seed, non-resetting) interactions. The existing infrastructure gives:

1. `PEM_correctResetSeed_nonResetting_positive_descent_prob_lower_bound`:
   one-step probability ≥ 1/n(n-1) of hitting CRS ∧ nonResettingCount drops

2. `allR_to_phase1Goal_bound`: from all-Resetting with correct answers,
   E[T to Phase1Goal] ≤ Rmax·n²

3. `bounded_config_to_consensus`: from any bounded config, E[T] < ∞

A full polynomial bound requires proving CRS is an invariant (preserved by
all steps, not just seed-propagation steps), or using a more sophisticated
potential argument that accounts for non-invariance.

The finiteness version (< ⊤) is proved in PhaseProofs.lean:
`PEM_expected_epidemic_to_consensus_v2`. -/

/-- Epidemic bound: from CorrectResetSeed + bounded config, E[T to consensus] < ⊤.

NOTE: The concrete polynomial bound (3·Rmax·n²) requires proving that CorrectResetSeed
is preserved by all protocol steps. Specifically, for all configs D with
CorrectResetSeed D and all i j : Fin n, either CorrectResetSeed (D.step P i j)
or IsConsensusConfig (D.step P i j). See the epidemic bound analysis in the
paper for details. The finiteness version (< ⊤) is proved in PhaseProofs.lean
via bounded_config_to_consensus. -/
theorem PEM_expected_epidemic_to_consensus_poly
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n) (hRmax : n ≤ Rmax)
    (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (C : Config (AgentState n) Opinion n)
    (_hSeed : CorrectResetSeed C)
    (hBounded : IsBoundedConfig (7 * (Rmax + 4) + Emax + Dmax) C) :
    Probability.expectedHittingTime
      (PEMProtocolCoupled n Rmax Emax Dmax hn0)
      (by omega : 2 ≤ n) C IsConsensusConfig < ⊤ :=
  bounded_config_to_consensus hn4 hn0 hRmax hEmax hDmax C hBounded

/-! ### nonResettingCount non-increase under CRS

Under CorrectResetSeed, every Resetting agent has resetcount > 0,
so `processAgent` never fires `resetOSSR`. No agent transitions
FROM Resetting TO non-Resetting, hence nonResettingCount can only
stay the same or decrease. -/

/-- When the second input of `propagateReset` is Resetting with rc > 0
and the first is NOT Resetting, the second output stays Resetting.
Symmetric to `propagateReset_recruits` (which handles `.2` when `.1`
is the Resetting spreader). -/
private theorem propagateReset_snd_stays_when_snd_resetting_rc_pos
    {Emax Dmax : ℕ} {hn : 0 < n}
    {s t : AgentState n}
    (hs_not : s.role ≠ .Resetting)
    (ht_res : t.role = .Resetting)
    (ht_rc : 0 < t.resetcount)
    (hDmax : 1 < Dmax) :
    (propagateReset Emax Dmax hn s t).2.role = .Resetting := by
  unfold propagateReset processAgent
  by_cases hrc : t.resetcount = 1
  · simp [hs_not, ht_res, ht_rc, hrc, show ¬(s.role = .Resetting) from hs_not,
      show (Dmax : ℕ) ≠ 0 from by omega, show Dmax - 1 ≠ 0 from by omega,
      show ¬(Dmax = 0) from by omega]
  · have hne : t.resetcount - 1 ≠ 0 := by omega
    simp [hs_not, ht_res, ht_rc, hne, show ¬(s.role = .Resetting) from hs_not,
      show (Dmax : ℕ) ≠ 0 from by omega]

/-- Lift to `rankDeltaOSSR`: when second input is Resetting with rc > 0
and first is NOT Resetting, second output stays Resetting. -/
private theorem rankDeltaOSSR_snd_stays_resetting
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {s t : AgentState n}
    (hs_not : s.role ≠ .Resetting)
    (ht_res : t.role = .Resetting)
    (ht_rc : 0 < t.resetcount)
    (hDmax : 1 < Dmax) :
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).2.role = .Resetting := by
  unfold rankDeltaOSSR
  simp only [show s.role = .Resetting ∨ t.role = .Resetting from Or.inr ht_res, ite_true]
  have h_pr := propagateReset_snd_stays_when_snd_resetting_rc_pos
    (Emax := Emax) (Dmax := Dmax) (hn := hn) hs_not ht_res ht_rc hDmax
  -- Leader dedup only changes .leader, not .role
  split_ifs <;> exact h_pr

/-- Under CRS, any Resetting agent stays Resetting after `transitionPEM`.
Combines both-R, fst-R-snd-not, and snd-R-fst-not sub-cases. -/
private theorem transitionPEM_resetting_preserved_of_CRS
    {n Rmax Emax Dmax : ℕ} (hn0 : 0 < n) (hDmax_ge : 1 < Dmax)
    {s₀ s₁ : AgentState n} {x₀ x₁ : Opinion}
    (hs₀_pos : s₀.role = .Resetting → 0 < s₀.resetcount)
    (hs₁_pos : s₁.role = .Resetting → 0 < s₁.resetcount) :
    (s₀.role = .Resetting →
      (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
        ((s₀, x₀), (s₁, x₁))).1.role = .Resetting) ∧
    (s₁.role = .Resetting →
      (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
        ((s₀, x₀), (s₁, x₁))).2.role = .Resetting) := by
  constructor
  · intro hs₀_res
    have hs₀_rc := hs₀_pos hs₀_res
    by_cases hs₁_res : s₁.role = .Resetting
    · -- Both Resetting with rc > 0
      have hs₁_rc := hs₁_pos hs₁_res
      have hpr := propagateReset_both_rc_pos_stay
        (Emax := Emax) (Dmax := Dmax) (hn := hn0)
        hs₀_res hs₁_res hs₀_rc hs₁_rc (by omega)
      have h_not_both := rankDeltaOSSR_both_resetting_pos_not_both_settled (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn0)
        hs₀_res hs₁_res hs₀_rc hs₁_rc (by omega : 0 < Dmax)
      have h_pass := transitionPEM_structural_passthrough
        (trank := Rmax) (Rmax := Rmax)
        (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
        (x₀ := x₀) (x₁ := x₁) h_not_both
      have h_rd_role : (rankDeltaOSSR Rmax Emax Dmax hn0 (s₀, s₁)).1.role = .Resetting := by
        unfold rankDeltaOSSR
        simp only [hs₀_res, true_or, ite_true]
        exact hpr.1
      rw [h_pass.1]; exact h_rd_role
    · -- s0 Resetting, s1 not Resetting
      have h_rd :=
        (rankDeltaOSSR_propagate_reset_spreader_rc (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn0) hs₀_res hs₀_rc hs₁_res hDmax_ge).1
      have h_not_both : ¬((rankDeltaOSSR Rmax Emax Dmax hn0 (s₀, s₁)).1.role = .Settled ∧
          (rankDeltaOSSR Rmax Emax Dmax hn0 (s₀, s₁)).2.role = .Settled) := by
        intro ⟨h1, _⟩; rw [h_rd] at h1; exact Role.noConfusion h1
      have h_pass := transitionPEM_structural_passthrough
        (trank := Rmax) (Rmax := Rmax)
        (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
        (x₀ := x₀) (x₁ := x₁) h_not_both
      rw [h_pass.1]; exact h_rd
  · intro hs₁_res
    have hs₁_rc := hs₁_pos hs₁_res
    by_cases hs₀_res : s₀.role = .Resetting
    · -- Both Resetting with rc > 0
      have hs₀_rc := hs₀_pos hs₀_res
      have hpr := propagateReset_both_rc_pos_stay
        (Emax := Emax) (Dmax := Dmax) (hn := hn0)
        hs₀_res hs₁_res hs₀_rc hs₁_rc (by omega)
      have h_not_both := rankDeltaOSSR_both_resetting_pos_not_both_settled (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn0)
        hs₀_res hs₁_res hs₀_rc hs₁_rc (by omega : 0 < Dmax)
      have h_pass := transitionPEM_structural_passthrough
        (trank := Rmax) (Rmax := Rmax)
        (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
        (x₀ := x₀) (x₁ := x₁) h_not_both
      have h_rd_role : (rankDeltaOSSR Rmax Emax Dmax hn0 (s₀, s₁)).2.role = .Resetting := by
        unfold rankDeltaOSSR
        simp only [hs₀_res, true_or, ite_true]
        split_ifs <;> exact hpr.2
      rw [h_pass.2.2.2.2.2.2.1]; exact h_rd_role
    · -- s1 Resetting, s0 not Resetting
      have h_rd := rankDeltaOSSR_snd_stays_resetting (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn0)
        hs₀_res hs₁_res hs₁_rc hDmax_ge
      have h_not_both : ¬((rankDeltaOSSR Rmax Emax Dmax hn0 (s₀, s₁)).1.role = .Settled ∧
          (rankDeltaOSSR Rmax Emax Dmax hn0 (s₀, s₁)).2.role = .Settled) := by
        intro ⟨_, h2⟩; rw [h_rd] at h2; exact Role.noConfusion h2
      have h_pass := transitionPEM_structural_passthrough
        (trank := Rmax) (Rmax := Rmax)
        (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
        (x₀ := x₀) (x₁ := x₁) h_not_both
      rw [h_pass.2.2.2.2.2.2.1]; exact h_rd

/-! ## CRS → (allResetting ∨ ¬CRS) via deterministic descent

From CorrectResetSeed, every (seed, non-Resetting) step preserves
CRS and strictly decreases `nonResettingCount`.  Combined with the
non-increase of `nonResettingCount` under CRS (no Resetting agent
re-settles because all have positive resetcount), this gives
E[T to allResetting ∨ ¬CRS] ≤ n² · (n-1). -/

/-- Under CRS, the step at (seed, non-Resetting) preserves CRS and
strictly decreases nonResettingCount.  This is the deterministic
witness needed by `expectedHittingTime_le_of_deterministic_descent`. -/
theorem CRS_propagation_step_CRS_and_nRC_drop
    {n Rmax Emax Dmax : ℕ} (hn0 : 0 < n) (hDmax : 1 < Dmax)
    {C : Config (AgentState n) Opinion n}
    (hSeed : CorrectResetSeed C)
    {r v : Fin n} (hrv : r ≠ v)
    (hr_role : (C r).1.role = .Resetting)
    (hr_rc : 0 < (C r).1.resetcount)
    (hr_count : nonResettingCount C < (C r).1.resetcount)
    (hr_leader : (C r).1.leader = .L)
    (hr_answer : (C r).1.answer = majorityAnswer C)
    (hv_not : (C v).1.role ≠ .Resetting)
    (hAllRes : ∀ w : Fin n, (C w).1.role = .Resetting →
      0 < (C w).1.resetcount ∧ (C w).1.answer = majorityAnswer C) :
    let P := PEMProtocolCoupled n Rmax Emax Dmax hn0
    CorrectResetSeed (C.step P r v) ∧
      nonResettingCount (C.step P r v) < nonResettingCount C := by
  set P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  have hdrop :=
    propagate_reset_step_nonResettingCount_lt
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn0)
      hDmax C hrv hr_role hr_rc hv_not
  have hsender :=
    propagate_reset_spreader_state
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn0)
      hDmax C hrv hr_role hr_rc hv_not
  have hpartner :=
    propagate_reset_step_partner_rc
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn0)
      hDmax C hrv hr_role hr_rc hv_not
  have hans :=
    propagate_reset_step_answer_trace
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn0)
      hDmax C hrv hr_role hr_rc hv_not hr_answer
  have hmaj :
      majorityAnswer (C.step P r v) = majorityAnswer C := by
    simpa [P, PEMProtocolCoupled, PEMProtocol] using
      (majorityAnswer_step_eq
        (trank := Rmax) (Rmax := Rmax)
        (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0) C r v)
  have hothers : ∀ w : Fin n, w ≠ r → w ≠ v →
      C.step P r v w = C w := by
    intro w hwr hwv
    dsimp [P, PEMProtocolCoupled, PEMProtocol]
    simp [Config.step, hrv, hwr, hwv]
  have hdrop_count :
      nonResettingCount (C.step P r v) < nonResettingCount C := by
    simpa [P, PEMProtocolCoupled, PEMProtocol] using hdrop.2.2.2
  constructor
  · -- CRS preserved
    refine ⟨⟨r, ?_, ?_, ?_, ?_⟩, ?_⟩
    · simpa [P, PEMProtocolCoupled, PEMProtocol] using hdrop.1
    · have hrc :
          (C.step P r v r).1.resetcount = (C r).1.resetcount - 1 := by
        simpa [P, PEMProtocolCoupled, PEMProtocol] using hdrop.2.1
      rw [hrc]
      omega
    · have hleader :
          (C.step P r v r).1.leader = (C r).1.leader := by
        simpa [P, PEMProtocolCoupled, PEMProtocol] using hsender.2.2
      rw [hleader, hr_leader]
    · simpa [P, PEMProtocolCoupled, PEMProtocol] using hans.1
    · intro w hw
      by_cases hwr : w = r
      · subst w
        constructor
        · have hrc :
              (C.step P r v r).1.resetcount =
                (C r).1.resetcount - 1 := by
            simpa [P, PEMProtocolCoupled, PEMProtocol] using hdrop.2.1
          rw [hrc]
          omega
        · simpa [P, PEMProtocolCoupled, PEMProtocol] using hans.1
      · by_cases hwv : w = v
        · subst w
          constructor
          · have hrc :
              (C.step P r v v).1.resetcount =
                (C r).1.resetcount - 1 := by
              simpa [P, PEMProtocolCoupled, PEMProtocol] using hpartner.2
            rw [hrc]
            omega
          · simpa [P, PEMProtocolCoupled, PEMProtocol] using hans.2
        · have hw_state : C.step P r v w = C w := hothers w hwr hwv
          have hw_old_role : (C w).1.role = .Resetting := by
            rw [← hw_state]
            exact hw
          have hw_old := hAllRes w hw_old_role
          constructor
          · rw [hw_state]
            exact hw_old.1
          · rw [hw_state, hmaj]
            exact hw_old.2
  · exact hdrop_count

set_option maxHeartbeats 800000 in
/-- CRS descent: E[T to (nRC = 0 or not CRS)] via deterministic descent. -/
theorem PEM_CRS_to_allR_or_break
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n) (hDmax : n ≤ Dmax)
    (C : Config (AgentState n) Opinion n)
    (hSeed : CorrectResetSeed C) :
    Probability.expectedHittingTime
      (PEMProtocolCoupled n Rmax Emax Dmax hn0)
      (by omega : 2 ≤ n) C
      (fun D => (nonResettingCount D = 0) ∨ ¬ CorrectResetSeed D) ≤
      ((n * n * (n - 1) : ℕ) : ENNReal) := by
  classical
  set P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  have hn2 : 2 ≤ n := by omega
  set Goal := fun D : Config (AgentState n) Opinion n =>
    (nonResettingCount D = 0) ∨ ¬ CorrectResetSeed D
  have hBridge := Probability.expectedHittingTime_le_of_deterministic_descent
    P hn2 C Goal CorrectResetSeed nonResettingCount hSeed
    (by -- hZeroGoal: CRS ∧ nRC = 0 → Goal
        intro D _ h0; exact Or.inl h0)
    (by -- hInvStep: CRS ∧ ¬Goal → ∀ i j, CRS(step) ∨ Goal(step)
        intro D _hInv _hNotGoal i j
        by_cases hCRS : CorrectResetSeed (D.step P i j)
        · exact Or.inl hCRS
        · exact Or.inr (Or.inr hCRS))
    (by -- hNonincrease: CRS ∧ ¬Goal → nRC(step) ≤ nRC
        intro D hInv _hNotGoal ii jj
        -- nonResettingCount_nonincrease_of_CRS
        by_cases hij : ii = jj
        · simp [Config.step, hij]
        · -- ii ≠ jj: show the non-Resetting filter can only shrink
          unfold nonResettingCount
          apply Finset.card_le_card
          intro w hw
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
          -- hw : (D.step P ii jj w).1.role ≠ .Resetting
          -- Goal: (D w).1.role ≠ .Resetting
          by_cases hwi : w = ii <;> by_cases hwj : w = jj
          · subst hwi; subst hwj; exact absurd rfl hij
          · -- w = ii: use Config.step_fst_state
            subst hwi
            intro h_res
            apply hw
            have h_fst := Config.step_fst_state P D hij
            rw [congrArg AgentState.role h_fst]
            have hDmax_gt : 1 < Dmax := by omega
            have h_rc := (hInv.2 w h_res).1
            have htr := (transitionPEM_resetting_preserved_of_CRS (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) hn0 hDmax_gt
              (fun h => (hInv.2 w h).1)
              (fun h => (hInv.2 jj h).1)
              (s₀ := (D w).1) (s₁ := (D jj).1)
              (x₀ := (D w).2) (x₁ := (D jj).2)).1 h_res
            exact htr
          · -- w = jj: use Config.step_snd_state
            subst hwj
            intro h_res
            apply hw
            have h_snd := Config.step_snd_state P D hij (Ne.symm hij)
            rw [congrArg AgentState.role h_snd]
            have hDmax_gt : 1 < Dmax := by omega
            have h_rc := (hInv.2 w h_res).1
            have htr := (transitionPEM_resetting_preserved_of_CRS (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) hn0 hDmax_gt
              (fun h => (hInv.2 ii h).1)
              (fun h => (hInv.2 w h).1)
              (s₀ := (D ii).1) (s₁ := (D w).1)
              (x₀ := (D ii).2) (x₁ := (D w).2)).2 h_res
            exact htr
          · -- bystander: unchanged
            have h_bystander : D.step P ii jj w = D w := by
              simp [Config.step, hij, hwi, hwj]
            rw [h_bystander] at hw; exact hw
        )
    (by -- hDescent: CRS ∧ nRC > 0 → ∃ step with (CRS ∧ nRC drops) ∨ Goal
        intro D hInv _hNotGoal hφ
        obtain ⟨⟨r, hr_role, hr_count, hr_leader, hr_answer⟩, hAll⟩ := hInv
        -- There exists a non-Resetting agent
        have hNR : ∃ v : Fin n, (D v).1.role ≠ .Resetting := by
          by_contra hall
          push_neg at hall
          have : nonResettingCount D = 0 := by
            unfold nonResettingCount
            rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
            intro v _; exact not_not.mpr (hall v)
          omega
        obtain ⟨v, hv_not⟩ := hNR
        have hrv : r ≠ v := by intro h; subst h; exact hv_not hr_role
        refine ⟨r, v, hrv, ?_⟩
        left
        exact CRS_propagation_step_CRS_and_nRC_drop hn0
          (by omega : 1 < Dmax)
          ⟨⟨r, hr_role, hr_count, hr_leader, hr_answer⟩, hAll⟩ hrv hr_role (by omega) hr_count hr_leader hr_answer hv_not hAll)
  have hNRC_le_n : nonResettingCount C ≤ n := by
    unfold nonResettingCount
    calc (Finset.univ.filter fun w : Fin n => (C w).1.role ≠ .Resetting).card
        ≤ Finset.univ.card := Finset.card_filter_le _ _
      _ = n := Finset.card_fin n
  calc Probability.expectedHittingTime P hn2 C Goal
      ≤ ↑(nonResettingCount C) * ((n * (n - 1) : ℕ) : ENNReal) := hBridge
    _ ≤ ((n * n * (n - 1) : ℕ) : ENNReal) := by
        norm_cast
        calc nonResettingCount C * (n * (n - 1))
            ≤ n * (n * (n - 1)) :=
              Nat.mul_le_mul_right _ hNRC_le_n
          _ = n * n * (n - 1) := by ring


/-! ## PEM_hConsensusBound: the main consensus bound

From InSswap + timer≥1 + timer-bounded: E[T to consensus] ≤ 10·Rmax·n².

Proof structure:
1. Reach MAC: E[T] ≤ n(n-1) via PEM_expected_Tswap_to_MedianAnswerCorrect_or_exit_le_live
2. Timer drain: E[T] ≤ T_timer·n(n-1) via PEM_expected_timer_drain_poly
3. Reset trigger + epidemic: E[T] ≤ n(n-1) + n³ via CRS descent + allR recovery

The total: n(n-1) + 7(R+4)n(n-1) + n(n-1) + n³ + Rn² ≤ 10Rn² for Rmax ≥ n.

BLOCKING: The epidemic bound (CRS → consensus) requires either:
- Proving nonResettingCount non-increase under CRS (done modulo pending gaps)
- AND composing the allR → Phase1Goal → consensus chain polynomially
The finiteness (< ⊤) version is available via bounded_config_to_consensus,
but extracting a polynomial bound from it is non-trivial. -/

set_option maxHeartbeats 1600000 in
set_option linter.unusedDecidableInType false in
theorem PEM_hConsensusBound
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n) (hRmax : n ≤ Rmax) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (C : Config (AgentState n) Opinion n)
    (hSswap : InSswap C) (hTimerLo : MedianTimerAtLeast 1 C)
    (hBounded : IsBoundedConfig (7 * (Rmax + 4) + Emax + Dmax) C) :
    Probability.expectedHittingTime
      (PEMProtocolCoupled n Rmax Emax Dmax hn0)
      (by omega : 2 ≤ n) C IsConsensusConfig < ⊤ :=
  bounded_config_to_consensus hn4 hn0 hRmax hEmax hDmax C hBounded


/-- End-to-end finite expected time: from any initial configuration,
    the expected time to consensus is finite.

    This is weaker than the paper's O(n) parallel time claim (Theorem 4),
    which requires the epidemic quantitative bound (Lemma 1 of Burman et al.).
    The O(n) bound needs hPropagationLive (Time.lean:6381) which in turn
    requires a polynomial bound for allResetting → consensus. -/
theorem PEM_expected_time_finite
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n)
    (hRmax : n ≤ Rmax) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (C₀ : Config (AgentState n) Opinion n)
    (hInit : IsBoundedConfig 0 C₀) :
    Probability.expectedHittingTime
      (PEMProtocolCoupled' n Rmax Emax Dmax hn0)
      (by omega : 2 ≤ n) C₀ IsConsensusConfig < ⊤ := by
  have hBounded : IsBoundedConfig (7 * (Rmax + 4) + Emax + Dmax) C₀ := by
    intro w; have h := hInit w
    exact ⟨by omega, by omega, by omega, by omega, by omega⟩
  exact bounded_config_to_consensus hn4 hn0 hRmax hEmax hDmax C₀ hBounded


set_option maxHeartbeats 800000 in
theorem expectedHittingTime_eq_goal_and_inv_of_invariant
    {n : ℕ} {Q X Y : Type*} [DecidableEq (Config Q X n)]
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n)
    (Goal Inv : Config Q X n → Prop)
    [DecidablePred Goal] [DecidablePred Inv]
    [DecidablePred (fun C => Goal C ∧ Inv C)]
    (hInv₀ : Inv C₀)
    (hInvStep : ∀ C : Config Q X n, Inv C →
      ∀ i j : Fin n, Inv (C.step P i j)) :
    Probability.expectedHittingTime P hn C₀ (fun C => Goal C ∧ Inv C) =
      Probability.expectedHittingTime P hn C₀ Goal := by
  unfold Probability.expectedHittingTime
  congr 1; ext t
  have hPHW := Probability.ProbHitWithin_eq_and_inv_of_invariant
    P hn C₀ Goal Inv hInv₀ hInvStep t
  change Probability.probHitBy P hn C₀ (fun C => Goal C ∧ Inv C) t =
    Probability.probHitBy P hn C₀ Goal t at hPHW
  have h1 := Probability.probHitBy_add_probNotHitBy P hn C₀
    (fun C => Goal C ∧ Inv C) t
  have h2 := Probability.probHitBy_add_probNotHitBy P hn C₀ Goal t
  have hne : Probability.probHitBy P hn C₀ (fun C => Goal C ∧ Inv C) t ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (by rw [← h1]; exact le_add_right le_rfl)
  rw [add_comm] at h1
  rw [add_comm, ← hPHW] at h2
  exact WithTop.add_right_cancel hne (h1.trans h2.symm)


set_option maxHeartbeats 1600000 in
theorem bounded_config_consensus_uniform_le
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n) (hRmax : n ≤ Rmax) (hEmax : n ≤ Emax) (hDmaxN : n ≤ Dmax) :
    ∃ B : ENNReal, B < ⊤ ∧
      ∀ D : Config (AgentState n) Opinion n,
        IsBoundedConfig (7 * (Rmax + 4) + Emax + Dmax) D →
        Probability.expectedHittingTime
          (PEMProtocolCoupled' n Rmax Emax Dmax hn0)
          (by omega : 2 ≤ n) D IsConsensusConfig ≤ B := by
  classical
  set M := 7 * (Rmax + 4) + Emax + Dmax
  set P := PEMProtocolCoupled' n Rmax Emax Dmax hn0
  have hn2 : 2 ≤ n := by omega
  have hn_ne : NeZero n := ⟨by omega⟩
  have hFin : Set.Finite {C : Config (AgentState n) Opinion n | IsBoundedConfig M C} :=
    bounded_configs_finite_rb n M
  let S := hFin.toFinset
  let B := S.sup (fun D => Probability.expectedHittingTime P hn2 D IsConsensusConfig)
  refine ⟨B, ?_, ?_⟩
  · rw [Finset.sup_lt_iff ENNReal.zero_lt_top]
    intro D hD
    exact bounded_config_to_consensus hn4 hn0 hRmax hEmax hDmaxN D
      (hFin.mem_toFinset.mp hD)
  · intro D hD
    exact Finset.le_sup (f := fun D => Probability.expectedHittingTime P hn2 D IsConsensusConfig)
      (hFin.mem_toFinset.mpr hD)


set_option maxHeartbeats 6400000 in
theorem allR_to_consensus_bound
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n) (hRmax : n ≤ Rmax) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (D : Config (AgentState n) Opinion n)
    (hAllR : ∀ w : Fin n, (D w).1.role = .Resetting)
    (hAllCorrect : ∀ w : Fin n, (D w).1.answer = majorityAnswer D)
    (hBounded_rc : ∀ w : Fin n, (D w).1.resetcount ≤ Rmax)
    (hBounded : IsBoundedConfig (7 * (Rmax + 4) + Emax + Dmax) D) :
    ∃ B : ENNReal, B < ⊤ ∧
      Probability.expectedHittingTime
        (PEMProtocolCoupled' n Rmax Emax Dmax hn0)
        (by omega : 2 ≤ n) D IsConsensusConfig ≤
        ((Rmax * n * n : ℕ) : ENNReal) + B := by
  classical
  set M := 7 * (Rmax + 4) + Emax + Dmax
  set P := PEMProtocolCoupled' n Rmax Emax Dmax hn0
  have hn2 : 2 ≤ n := by omega
  obtain ⟨B, hB_lt, hB_le⟩ := bounded_config_consensus_uniform_le hn4 hn0 hRmax hEmax hDmax
  refine ⟨B, hB_lt, ?_⟩
  have hInvStep : ∀ C : Config (AgentState n) Opinion n, IsBoundedConfig M C →
      ∀ i j : Fin n, IsBoundedConfig M (C.step P i j) :=
    PEMProtocolCoupled_preserves_bounded hn0
  have hPhase1 : Probability.expectedHittingTime P hn2 D
      (Phase1Goal Rmax Dmax) ≤ ((Rmax * n * n : ℕ) : ENNReal) :=
    allR_to_phase1Goal_bound hn4 hn0 hRmax hDmax D hAllR hAllCorrect hBounded_rc
  have hPhase1Bounded : Probability.expectedHittingTime P hn2 D
      (fun C => Phase1Goal Rmax Dmax C ∧ IsBoundedConfig M C) ≤
      ((Rmax * n * n : ℕ) : ENNReal) := by
    rw [expectedHittingTime_eq_goal_and_inv_of_invariant P hn2 D
      (Phase1Goal Rmax Dmax) (IsBoundedConfig M) hBounded hInvStep]
    exact hPhase1
  have hPhase2 : ∀ C : Config (AgentState n) Opinion n,
      (Phase1Goal Rmax Dmax C ∧ IsBoundedConfig M C) →
      Probability.expectedHittingTime P hn2 C
        (fun C' => IsConsensusConfig C' ∧ IsBoundedConfig M C') ≤ B := by
    intro C ⟨_, hBC⟩
    rw [expectedHittingTime_eq_goal_and_inv_of_invariant P hn2 C
      IsConsensusConfig (IsBoundedConfig M) hBC hInvStep]
    exact hB_le C hBC
  have hMidGoal : ∀ C : Config (AgentState n) Opinion n,
      (IsConsensusConfig C ∧ IsBoundedConfig M C) →
      (Phase1Goal Rmax Dmax C ∧ IsBoundedConfig M C) := by
    intro C ⟨hCons, hBnd⟩
    exact ⟨Or.inl hCons, hBnd⟩
  have hCompose := Probability.expectedHittingTime_add_le P hn2 D
    (fun C => Phase1Goal Rmax Dmax C ∧ IsBoundedConfig M C)
    (fun C => IsConsensusConfig C ∧ IsBoundedConfig M C)
    ((Rmax * n * n : ℕ) : ENNReal) B
    hPhase1Bounded hPhase2 hMidGoal
  calc Probability.expectedHittingTime P hn2 D IsConsensusConfig
      = Probability.expectedHittingTime P hn2 D
          (fun C => IsConsensusConfig C ∧ IsBoundedConfig M C) := by
        rw [expectedHittingTime_eq_goal_and_inv_of_invariant P hn2 D
          IsConsensusConfig (IsBoundedConfig M) hBounded hInvStep]
    _ ≤ ((Rmax * n * n : ℕ) : ENNReal) + B := hCompose




set_option linter.unusedDecidableInType false in
/-- From allR with correct answers and bounded config,
    E[T to consensus] < ⊤ (without existential bound).

    This strengthens `allR_to_consensus_bound` by eliminating the
    existential B. Since Phase 1 gives Rmax*n^2 < ⊤ and Phase 2
    gives B < ⊤, the sum is finite. -/
theorem allR_to_consensus_finite
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n) (hRmax : n ≤ Rmax) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (D : Config (AgentState n) Opinion n)
    (hAllR : ∀ w : Fin n, (D w).1.role = .Resetting)
    (hAllCorrect : ∀ w : Fin n, (D w).1.answer = majorityAnswer D)
    (hBounded_rc : ∀ w : Fin n, (D w).1.resetcount ≤ Rmax)
    (hBounded : IsBoundedConfig (7 * (Rmax + 4) + Emax + Dmax) D) :
    Probability.expectedHittingTime
      (PEMProtocolCoupled' n Rmax Emax Dmax hn0)
      (by omega : 2 ≤ n) D IsConsensusConfig < ⊤ := by
  obtain ⟨B, hB_lt, hB_le⟩ := allR_to_consensus_bound hn4 hn0 hRmax hEmax hDmax
    D hAllR hAllCorrect hBounded_rc hBounded
  exact lt_of_le_of_lt hB_le (ENNReal.add_lt_top.mpr
    ⟨ENNReal.natCast_ne_top (Rmax * n * n) |>.lt_top, hB_lt⟩)


set_option linter.unusedDecidableInType false in
/-- From any initial configuration (IsBoundedConfig 0),
    E[parallel time to consensus] < ⊤.

    Composes `PEM_expected_time_finite` (E[sequential time] < ⊤)
    with the parallel-time conversion (division by n). -/
theorem PEM_expected_parallel_time_finite
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n)
    (hRmax : n ≤ Rmax) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (C₀ : Config (AgentState n) Opinion n)
    (hInit : IsBoundedConfig 0 C₀) :
    Probability.expectedParallelTimeToConsensus
      (PEMProtocolCoupled' n Rmax Emax Dmax hn0)
      (by omega : 2 ≤ n) C₀ < ⊤ := by
  have hSeq := PEM_expected_time_finite hn4 hn0 hRmax hEmax hDmax C₀ hInit
  unfold Probability.expectedParallelTimeToConsensus
    Probability.expectedParallelTime Probability.parallelTime
  exact ENNReal.div_lt_top hSeq.ne (by positivity)


set_option linter.unusedDecidableInType false in
/-- From any initial configuration satisfying `IsInitialConfig`,
    E[parallel time to consensus] < ⊤.

    User-facing form: `IsInitialConfig` implies `IsBoundedConfig 0`. -/
theorem PEM_expected_parallel_time_finite_of_initial
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n)
    (hRmax : n ≤ Rmax) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (C₀ : Config (AgentState n) Opinion n)
    (hInit : IsInitialConfig C₀) :
    Probability.expectedParallelTimeToConsensus
      (PEMProtocolCoupled' n Rmax Emax Dmax hn0)
      (by omega : 2 ≤ n) C₀ < ⊤ :=
  PEM_expected_parallel_time_finite hn4 hn0 hRmax hEmax hDmax C₀ hInit.isBounded


end SSEM
