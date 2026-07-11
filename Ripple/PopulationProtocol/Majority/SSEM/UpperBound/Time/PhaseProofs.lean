import Ripple.PopulationProtocol.Majority.SSEM.UpperBound.Time.HeavyProofs
import Ripple.PopulationProtocol.Majority.SSEM.UpperBound.Time.CRSOdd
import Ripple.PopulationProtocol.Majority.SSEM.UpperBound.Time.CRSEven
import Ripple.PopulationProtocol.Majority.SSEM.UpperBound.Time.RecoveryBound

namespace SSEM

open scoped ENNReal

/-! Stage 2: Reset trigger. From InSswap + MedianCorrect + timer=0 +
wrongAnswer > 0: trigger_correct_reset_from_InSrank gives a deterministic
pair that creates CorrectResetSeed.
E[T] ≤ n(n-1) via ProbHitWithin_one_lower_bound_of_step. -/

theorem PEM_expected_reset_trigger_v2
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n) (hRmax : n ≤ Rmax)
    (_hEmax : n ≤ Emax) (_hDmax : n ≤ Dmax)
    (C : Config (AgentState n) Opinion n)
    (hSswap : InSswap C)
    (hMedCorrect : MedianAnswerCorrect C)
    (hWrong : 0 < wrongAnswerCount C)
    (hTimer0 : ∀ μ : Fin n, (C μ).1.rank.val + 1 = ceilHalf n →
      (C μ).1.timer = 0) :
    Probability.expectedHittingTime
      (PEMProtocolCoupled n Rmax Emax Dmax hn0)
      (by omega : 2 ≤ n) C
      (fun D => IsConsensusConfig D ∨ CorrectResetSeed D) ≤
      ((n * (n - 1) : ℕ) : ENNReal) := by
  classical
  set P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  set Goal := fun D : Config (AgentState n) Opinion n =>
    IsConsensusConfig D ∨ CorrectResetSeed D
  -- Use the invariant-based one-step lemma: the bound only needs to hold
  -- under the InSswap invariant, not for arbitrary configs.
  set Inv := fun D : Config (AgentState n) Opinion n =>
    InSswap D ∧ MedianAnswerCorrect D ∧
      (∀ μ : Fin n, (D μ).1.rank.val + 1 = ceilHalf n → (D μ).1.timer = 0)
  refine (Probability.expectedHittingTime_le_inv_of_local_one_lower_bound_until_goal
    P (by omega) C Goal Inv ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ?_ ?_ ?_).trans
    (by rw [inv_inv])
  · -- hInv₀: Inv C
    exact ⟨hSswap, hMedCorrect, hTimer0⟩
  · -- hInvStep: Inv D → ¬Goal D → ∀ i j, Inv(step) ∨ Goal(step)
    intro D ⟨hS, hM, hT⟩ _hGoalD i j
    by_cases hS' : InSswap (D.step P i j)
    · -- InSswap preserved → check other invariant components
      have hM' := step_median_answer_of_InSswap_both_v2 hn0 hn4 hS hS' hM
      left
      refine ⟨hS', hM', ?_⟩
      -- Timer at median: step_timer_le gives timer ≤ old timer = 0
      intro μ hμ
      have hrank : (D.step P i j μ).1.rank = (D μ).1.rank :=
        step_rank_preserved_of_InSswap (Rmax := Rmax) (Emax := Emax)
          (Dmax := Dmax) hn0 hS μ
      have hμ_pre : (D μ).1.rank.val + 1 = ceilHalf n := by
        rwa [← show (D.step P i j μ).1.rank.val = (D μ).1.rank.val from
          congrArg Fin.val hrank]
      have h0 := hT μ hμ_pre
      have hle : (D.step P i j μ).1.timer ≤ (D μ).1.timer :=
        step_timer_le_of_InSswap (Rmax := Rmax) (Emax := Emax)
          (Dmax := Dmax) hn0 hS (i := i) (j := j) μ
      omega
    · -- InSswap broke → phase4_propagate created Resetting agents → CorrectResetSeed
      exact Or.inr (Or.inr (step_InSswap_break_creates_CorrectResetSeed hn4 hn0 hRmax hS hM hT hS'))
  · -- hwin: one-step bound under Inv
    intro D ⟨hS, hM, hT⟩ hGoalD
    have hNotCons : ¬ IsConsensusConfig D := fun h => hGoalD (Or.inl h)
    have hWrongExists : ∃ v : Fin n, (D v).1.answer ≠ majorityAnswer D := by
      by_contra h; push_neg at h; exact hNotCons ⟨hS.allSettled, hS.toInSrank.ranks_inj, hS.input_rank, h⟩
    obtain ⟨μ, hμ_med⟩ := hS.toInSrank.exists_median (by omega : 0 < n)
    have hμ_correct : (D μ).1.answer = majorityAnswer D := hM μ hμ_med
    have hμ_timer : (D μ).1.timer = 0 := hT μ hμ_med
    -- Find a wrong-answer agent that is NOT the upper-median (rank n/2+1).
    -- If such exists, one step creates CorrectResetSeed (propagate fires).
    -- If no such exists, the ONLY wrong agent is the upper-median; step fixes it → consensus.
    by_cases hNonUpper : ∃ v : Fin n, (D v).1.answer ≠ majorityAnswer D ∧
        (D v).1.rank.val + 1 ≠ n / 2 + 1
    · obtain ⟨v, hv_wrong, hv_no_upper⟩ := hNonUpper
      have hμv : μ ≠ v := fun h => by subst h; exact hv_wrong hμ_correct
      apply Probability.ProbHitWithin_one_lower_bound_of_step P (by omega) D Goal
        (fun h => hGoalD h) hμv
      exact Or.inr (step_timer_zero_median_wrong_nonupper_creates_CorrectResetSeed
        hn4 hn0 hRmax hS hμv hμ_med hμ_timer hμ_correct hv_wrong hv_no_upper)
    · -- Only wrong agent has rank n/2+1 (upper median for even n).
      -- Step at (median, upper_median) via phase4_decide corrects its answer.
      -- Since it's the sole wrong agent, post-step has allAnswerCorrect → IsConsensusConfig.
      push_neg at hNonUpper
      obtain ⟨v, hv_wrong⟩ := hWrongExists
      have hμv : μ ≠ v := fun h => by subst h; exact hv_wrong hμ_correct
      apply Probability.ProbHitWithin_one_lower_bound_of_step P (by omega) D Goal
        (fun h => hGoalD h) hμv
      -- From hNonUpper applied to v with hv_wrong, v has rank+1 = n/2+1.
      have hv_upper : (D v).1.rank.val + 1 = n / 2 + 1 :=
        hNonUpper v hv_wrong
      -- For odd n, n/2+1 = ceilHalf n = median rank ⇒ v = μ. Contradicts μ ≠ v.
      -- So we're in even case.
      have hpar : n % 2 = 0 := by
        by_contra h
        push_neg at h
        have hceil : ceilHalf n = n / 2 + 1 := by unfold ceilHalf; omega
        apply hμv
        apply (hS.toInSrank.ranks_inj (Fin.ext ?_)).symm
        show (D v).1.rank.val = (D μ).1.rank.val
        have h1 : (D v).1.rank.val + 1 = (D μ).1.rank.val + 1 := by
          rw [hv_upper, hμ_med, hceil]
        omega
      -- Even case: μ at lower median, v at upper median. Step → IsConsensusConfig.
      left  -- IsConsensusConfig
      have hceil : ceilHalf n = n / 2 := by unfold ceilHalf; omega
      have hμ_lower : (D μ).1.rank.val + 1 = n / 2 := by rw [← hceil]; exact hμ_med
      have hsμ : (D μ).1.role = .Settled := hS.allSettled μ
      have hsv : (D v).1.role = .Settled := hS.allSettled v
      have h_maj : majorityAnswer (D.step P μ v) = majorityAnswer D := by
        simpa [P, PEMProtocolCoupled, PEMProtocol] using
          majorityAnswer_step_eq (trank := Rmax) (Rmax := Rmax)
            (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0) D μ v
      -- Case split on input agreement at (μ, v)
      by_cases hxeq : (D μ).2 = (D v).2
      · -- Agreed inputs (strict majority case)
        have hSwap' : InSswap (D.step P μ v) :=
          step_at_median_pair_even_preserves_InSswap
            (trank := Rmax) (Rmax := Rmax)
            (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
            rankDeltaOSSR_satisfies_fix hS hμv hpar hμ_lower hv_upper hxeq hn4
        have hC'_eq := step_at_median_pair_even_agreed_inputs
            (trank := Rmax) (Rmax := Rmax)
            (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
            rankDeltaOSSR_satisfies_fix hμv hsμ hsv hpar hμ_lower hv_upper hxeq hn4
        -- Derive strict majority (hne) from input agreement
        have h_sum := nAOf_add_nBOf D
        have hμ_rank : (D μ).1.rank.val = n / 2 - 1 := by omega
        have hv_rank : (D v).1.rank.val = n / 2 := by omega
        have hne : nAOf D ≠ nBOf D := by
          rcases hx : (D μ).2 with _ | _
          · -- x_μ = .A
            have hxv : (D v).2 = Opinion.A := by rw [← hxeq]; exact hx
            have h2 : (D v).1.rank.val < nAOf D := (hS.input_rank v).mp hxv
            intro h; omega
          · -- x_μ = .B
            have hxv : (D v).2 = Opinion.B := by rw [← hxeq]; exact hx
            have h1 : ¬ ((D μ).1.rank.val < nAOf D) := by
              intro hh; have := (hS.input_rank μ).mpr hh
              rw [hx] at this; cases this
            have h2 : ¬ ((D v).1.rank.val < nAOf D) := by
              intro h; have := (hS.input_rank v).mpr h
              rw [hxv] at this; cases this
            intro h; omega
        have h_μ_eq_maj : opinionToAnswer (D μ).2 = majorityAnswer D :=
          opinionToAnswer_lower_median_eq_majorityAnswer_even hS hμ_lower hpar hne
        -- Build allAnswerCorrect post-step
        refine ⟨hSwap'.allSettled, hSwap'.ranks_inj, hSwap'.input_rank, ?_⟩
        intro w
        rw [h_maj]
        have h_step_w : D.step P μ v w = (
            fun w => if w = μ then ({(D μ).1 with answer := opinionToAnswer (D μ).2}, (D μ).2)
                     else if w = v then ({(D v).1 with answer := opinionToAnswer (D μ).2}, (D v).2)
                     else D w) w := by rw [hC'_eq]
        by_cases hwμ : w = μ
        · subst hwμ; rw [h_step_w]; simp [h_μ_eq_maj]
        · by_cases hwv : w = v
          · subst hwv; rw [h_step_w]; simp [hwμ, h_μ_eq_maj]
          · rw [h_step_w]; simp [hwμ, hwv]
            -- w ≠ μ, w ≠ v: by hNonUpper, w has correct answer
            by_cases hw_ans : (D w).1.answer = majorityAnswer D
            · exact hw_ans
            · exfalso; apply hwv
              apply hS.toInSrank.ranks_inj
              exact Fin.ext (Nat.add_right_cancel ((hNonUpper w hw_ans).trans hv_upper.symm))
      · -- Disagreed inputs (tie case)
        have h_no_swap_disagree : ¬ ((D μ).2 = Opinion.B ∧ (D v).2 = Opinion.A) := by
          intro ⟨hxμB, hxvA⟩
          have h1 : ¬ ((D μ).1.rank.val < nAOf D) := by
            intro h; have := (hS.input_rank μ).mpr h
            rw [hxμB] at this; cases this
          have h2 : (D v).1.rank.val < nAOf D := (hS.input_rank v).mp hxvA
          have h_sum := nAOf_add_nBOf D
          omega
        have h_step := step_at_median_pair_even_disagreed_inputs
            (trank := Rmax) (Rmax := Rmax)
            (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
            rankDeltaOSSR_satisfies_fix hμv hsμ hsv hpar hμ_lower hv_upper hxeq
            h_no_swap_disagree hn4
        obtain ⟨h_μ_post, h_v_post, h_others_post, h_inputs_post⟩ := h_step
        -- Tie case: majorityAnswer D = .outT
        have hTie : nAOf D = nBOf D := by
          have h_sum := nAOf_add_nBOf D
          -- Derive from disagreed inputs at lower-median μ and upper-median v
          rcases hxμ : (D μ).2 with _ | _
          · have hxvB : (D v).2 = Opinion.B := by
              cases hxv : (D v).2 with
              | A => exfalso; apply hxeq; rw [hxμ, hxv]
              | B => rfl
            have h1 : (D μ).1.rank.val < nAOf D := (hS.input_rank μ).mp hxμ
            have h2 : ¬ ((D v).1.rank.val < nAOf D) := by
              intro h; have := (hS.input_rank v).mpr h
              rw [hxvB] at this; cases this
            omega
          · have hxvA : (D v).2 = Opinion.A := by
              cases hxv : (D v).2 with
              | A => rfl
              | B => exfalso; apply hxeq; rw [hxμ, hxv]
            have h1 : ¬ ((D μ).1.rank.val < nAOf D) := by
              intro h; have := (hS.input_rank μ).mpr h
              rw [hxμ] at this; cases this
            have h2 : (D v).1.rank.val < nAOf D := (hS.input_rank v).mp hxvA
            omega
        have hMaj_outT : majorityAnswer D = .outT := majorityAnswer_eq_outT_of_tie hTie
        -- Build IsConsensusConfig
        constructor
        · -- allSettled
          intro w
          by_cases hwμ : w = μ
          · rw [hwμ, h_μ_post]; exact hsμ
          · by_cases hwv : w = v
            · rw [hwv, h_v_post]; exact hsv
            · rw [show (D.step P μ v w).1 = (D w).1 from
                congrArg Prod.fst (h_others_post w hwμ hwv)]
              exact hS.allSettled w
        · -- ranks_inj
          intro w1 w2 heq
          have h_rank_w : ∀ w, (D.step P μ v w).1.rank = (D w).1.rank := by
            intro w
            by_cases hwμ : w = μ
            · rw [hwμ, h_μ_post]
            · by_cases hwv : w = v
              · rw [hwv, h_v_post]
              · rw [show (D.step P μ v w).1 = (D w).1 from
                  congrArg Prod.fst (h_others_post w hwμ hwv)]
          simp only [h_rank_w] at heq
          exact hS.toInSrank.ranks_inj heq
        · -- input_rank
          intro w
          have h_nA : nAOf (D.step P μ v) = nAOf D := by
            unfold nAOf Config.agentsWithInput Config.inputOf
            congr 1; ext w'
            simp only [Finset.mem_filter]
            refine ⟨fun ⟨hm, hh⟩ => ⟨hm, by rw [h_inputs_post w'] at hh; exact hh⟩,
                    fun ⟨hm, hh⟩ => ⟨hm, by rw [h_inputs_post w']; exact hh⟩⟩
          have h_rank_w : (D.step P μ v w).1.rank = (D w).1.rank := by
            by_cases hwμ : w = μ
            · rw [hwμ, h_μ_post]
            · by_cases hwv : w = v
              · rw [hwv, h_v_post]
              · rw [show (D.step P μ v w).1 = (D w).1 from
                  congrArg Prod.fst (h_others_post w hwμ hwv)]
          rw [h_inputs_post w, h_rank_w, h_nA]
          exact hS.input_rank w
        · -- allAnswerCorrect
          intro w
          rw [h_maj, hMaj_outT]
          by_cases hwμ : w = μ
          · rw [hwμ]
            show (D.step P μ v μ).1.answer = .outT
            rw [h_μ_post]
          · by_cases hwv : w = v
            · rw [hwv]
              show (D.step P μ v v).1.answer = .outT
              rw [h_v_post]
            · -- w ≠ μ, w ≠ v: by hNonUpper, w has correct answer
              rw [show (D.step P μ v w).1 = (D w).1 from
                congrArg Prod.fst (h_others_post w hwμ hwv)]
              by_cases hw_ans : (D w).1.answer = majorityAnswer D
              · rw [hw_ans, hMaj_outT]
              · exfalso; apply hwv
                apply hS.toInSrank.ranks_inj
                exact Fin.ext (Nat.add_right_cancel ((hNonUpper w hw_ans).trans hv_upper.symm))

/-! ### Axioms for proved helper theorems (proofs in TimerPosCRS.lean + Phase2Helper.lean) -/

/-- Proved in TimerPosCRS.lean.
InSswap + MedC + ¬InSswap(step) → CRS, without needing timer=0. -/
theorem crs_of_InSswap_break_with_MedC
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n) (hRmax : n ≤ Rmax)
    {D : Config (AgentState n) Opinion n}
    (hS : InSswap D) (hM : MedianAnswerCorrect D)
    {i j : Fin n}
    (hS' : ¬ InSswap (D.step (PEMProtocolCoupled n Rmax Emax Dmax hn0) i j)) :
    CorrectResetSeed (D.step (PEMProtocolCoupled n Rmax Emax Dmax hn0) i j) := by
  by_cases hpar : n % 2 = 0
  · obtain ⟨μ, hμ_med⟩ := hS.toInSrank.exists_median (by omega : 0 < n)
    by_cases hT0 : (D μ).1.timer = 0
    · have hT : ∀ μ'' : Fin n, (D μ'').1.rank.val + 1 = ceilHalf n → (D μ'').1.timer = 0 := by
        intro μ'' hμ''_med
        have := hS.toInSrank.ranks_inj (Fin.ext (Nat.add_right_cancel (hμ_med.trans hμ''_med.symm)))
        subst this; exact hT0
      exact step_InSswap_break_creates_CorrectResetSeed hn4 hn0 hRmax hS hM hT hS'
    · have hT_le : MedianTimerAtLeast 1 D := by
        intro μ'' hμ''_med
        have := hS.toInSrank.ranks_inj (Fin.ext (Nat.add_right_cancel (hμ_med.trans hμ''_med.symm)))
        subst this; omega
      exact step_InSswap_break_creates_CorrectResetSeed_even_timer_pos
        hn4 hn0 hRmax hS hM hpar hT_le hS'
  · exact step_InSswap_break_creates_CorrectResetSeed_odd hn4 hn0 hRmax hS hpar hS'
/-! Stage 3: Epidemic propagation. From CorrectResetSeed:
E[T to consensus] via nonResettingCount descent + re-ranking. -/

theorem PEM_expected_epidemic_to_consensus_v2
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n) (hRmax : n ≤ Rmax) (hEmax : n ≤ Emax) (hDmaxN : n ≤ Dmax)
    (C : Config (AgentState n) Opinion n)
    (hSeed : CorrectResetSeed C)
    (hBounded : IsBoundedConfig (7 * (Rmax + 4) + Emax + Dmax) C) :
    Probability.expectedHittingTime
      (PEMProtocolCoupled n Rmax Emax Dmax hn0)
      (by omega : 2 ≤ n) C IsConsensusConfig < ⊤ :=
  bounded_config_to_consensus hn4 hn0 hRmax hEmax hDmaxN C hBounded


/-! Full median-correct → consensus via Strong Markov on stages 1-3. -/

theorem PEM_expected_median_correct_to_consensus_v2
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n)
    (hRmax : n ≤ Rmax) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (C : Config (AgentState n) Opinion n)
    (hSswap : InSswap C)
    (hMedCorrect : MedianAnswerCorrect C)
    (hTimerLo : MedianTimerAtLeast 1 C)
    (hTimerHi : IsTimerBoundedConfig (7 * (Rmax + 4)) C)
    (hBounded : IsBoundedConfig (7 * (Rmax + 4) + Emax + Dmax) C)
:
    Probability.expectedHittingTime
      (PEMProtocolCoupled n Rmax Emax Dmax hn0)
      (by omega : 2 ≤ n) C IsConsensusConfig < ⊤ :=
  bounded_config_to_consensus hn4 hn0 hRmax hEmax hDmax C hBounded

/-! Phase C assembly: compose median-wrong descent + median-correct via
strong Markov to get the full hConsensusBound. -/


/-! Phase C assembly: compose median-wrong descent + median-correct via
strong Markov to get the full hConsensusBound. -/

theorem PEM_hConsensusBound_from_bridge_v2
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n)
    (hRmax : n ≤ Rmax) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (C : Config (AgentState n) Opinion n)
    (hSswap : InSswap C)
    (hTimerLo : MedianTimerAtLeast 1 C)
    (hTimerHi : IsTimerBoundedConfig (7 * (Rmax + 4)) C)
    (hBounded : IsBoundedConfig (7 * (Rmax + 4) + Emax + Dmax) C) :
    Probability.expectedHittingTime
      (PEMProtocolCoupled n Rmax Emax Dmax hn0)
      (by omega : 2 ≤ n) C IsConsensusConfig < ⊤ :=
  bounded_config_to_consensus hn4 hn0 hRmax hEmax hDmax C hBounded

end SSEM
