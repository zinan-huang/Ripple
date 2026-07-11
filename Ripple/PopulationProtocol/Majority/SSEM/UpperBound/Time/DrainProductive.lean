import Ripple.PopulationProtocol.Majority.SSEM.UpperBound.Time.PolynomialBound
import Ripple.PopulationProtocol.Majority.SSEM.UpperBound.Time.PhaseProofs

/-!
# Refined timer-drain (productive endpoint)

`timer_drain_to_zero_productive`: from `InSswap ∧ MAC ∧ timer≥1`, the expected time to reach
`consensus ∨ CorrectResetSeed ∨ (InSswap ∧ MAC ∧ maxMedianTimer = 0)` is
`≤ T_timer·n(n-1)` for any ambient timer cap `T_timer`.

Unlike `PEM_expected_timer_drain_poly` (whose exit disjunct is `¬live`), this isolates the
PRODUCTIVE endpoint: the timer drains to 0 STAYING in `InSswap ∧ MAC` (no disruption in InSswap),
or a reset fires producing a `CorrectResetSeed`. This feeds the consensus renewal without the
circular `¬live` exit.
-/

namespace SSEM

open scoped ENNReal

variable {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
  [DecidableEq (Config (AgentState n) Opinion n)]

set_option maxHeartbeats 16000000 in
theorem timer_drain_to_zero_productive
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
        (InSswap D ∧ MedianAnswerCorrect D ∧ maxMedianTimer D = 0)) ≤
      ((T_timer * n * (n - 1) : ℕ) : ENNReal) := by
  classical
  set P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  set Goal := fun D : Config (AgentState n) Opinion n =>
    IsConsensusConfig D ∨ CorrectResetSeed D ∨
      (InSswap D ∧ MedianAnswerCorrect D ∧ maxMedianTimer D = 0)
  set Inv := fun D : Config (AgentState n) Opinion n =>
    InSswap D ∧ MedianAnswerCorrect D ∧ MedianTimerAtLeast 1 D
  -- helper: in InSswap, the unique median means `¬ MedianTimerAtLeast 1` ↔ `maxMedianTimer = 0`
  have hmax_zero_of_not_live :
      ∀ D : Config (AgentState n) Opinion n, InSswap D →
        ¬ MedianTimerAtLeast 1 D → maxMedianTimer D = 0 := by
    intro D hSD hnl
    rw [MedianTimerAtLeast] at hnl
    push_neg at hnl
    obtain ⟨ν, hν_med, hν_lt⟩ := hnl
    have hν0 : (D ν).1.timer = 0 := by omega
    unfold maxMedianTimer
    apply Nat.le_zero.mp
    apply Finset.sup_le
    intro μ _
    split_ifs with hμ_med
    · -- μ and ν are both medians → μ = ν (unique rank) → timer = 0
      have hrank_eq : (D μ).1.rank = (D ν).1.rank := by
        apply Fin.ext
        have h1 : (D μ).1.rank.val + 1 = ceilHalf n := hμ_med
        have h2 : (D ν).1.rank.val + 1 = ceilHalf n := hν_med
        omega
      have hμν : μ = ν := hSD.toInSrank.ranks_inj hrank_eq
      rw [hμν, hν0]
    · exact Nat.zero_le 0
  have hBridge := Probability.expectedHittingTime_le_of_deterministic_descent
    P (by omega : 2 ≤ n) C Goal Inv maxMedianTimer
    ⟨hSswap, hMedCorrect, hTimerLo⟩
    (by -- hZeroGoal: Inv D ∧ maxMedianTimer D = 0 → Goal D  (contradiction: median timer ≥ 1)
        intro D ⟨hSwap_D, hM_D, hT_D⟩ h0
        exact Or.inr (Or.inr ⟨hSwap_D, hM_D, h0⟩))
    (by -- hInvStep
        intro D ⟨hS, hM, hT⟩ hG i j
        by_cases hS' : InSswap (D.step P i j)
        · have hM' : MedianAnswerCorrect (D.step P i j) :=
            step_median_answer_of_InSswap_both hn0 hn4 hS hS' hM
          by_cases hT' : MedianTimerAtLeast 1 (D.step P i j)
          · exact Or.inl ⟨hS', hM', hT'⟩
          · exact Or.inr (Or.inr (Or.inr ⟨hS', hM', hmax_zero_of_not_live _ hS' hT'⟩))
        · exact Or.inr (Or.inr (Or.inl (crs_of_InSswap_break_with_MedC hn4 hn0 hRmax hS hM hS'))))
    (by -- hNonincrease : maxMedianTimer non-increasing (identical to PEM_expected_timer_drain_poly)
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
    (by -- hDescent
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
        · -- timer ≥ 2: reuse the proven descent; map its (orig-Goal) right disjunct to refined Goal
          have hstep := timer_ge_two_descent_step (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
            hn4 hn0 hRmax hS hM hT hμ_med hv_max huv hTimer2
          simp only [] at hstep
          rcases hstep with hleft | hright
          · exact Or.inl hleft
          · -- hright : IsConsensusConfig ∨ CorrectResetSeed ∨ ¬(InSswap ∧ timer≥1)
            rcases hright with hc | hcrs | hnl
            · exact Or.inr (Or.inl hc)
            · exact Or.inr (Or.inr (Or.inl hcrs))
            · -- ¬live at the step: InSswap holds → ¬timer≥1 → third disjunct; else break → CRS
              by_cases hS' : InSswap (D.step P μ v)
              · have hM' : MedianAnswerCorrect (D.step P μ v) :=
                  step_median_answer_of_InSswap_both hn0 hn4 hS hS' hM
                have hnt : ¬ MedianTimerAtLeast 1 (D.step P μ v) := fun ht => hnl ⟨hS', ht⟩
                exact Or.inr (Or.inr (Or.inr ⟨hS', hM', hmax_zero_of_not_live _ hS' hnt⟩))
              · exact Or.inr (Or.inr (Or.inl (crs_of_InSswap_break_with_MedC hn4 hn0 hRmax hS hM hS')))
        · -- timer = 1
          have hTimer1 : (D μ).1.timer = 1 := by omega
          by_cases hS' : InSswap (D.step P μ v)
          · -- stayed in swap: median timer drained to 0 → maxMedianTimer = 0
            have hM' : MedianAnswerCorrect (D.step P μ v) :=
              step_median_answer_of_InSswap_both hn0 hn4 hS hS' hM
            have hμ_rank_post : (D.step P μ v μ).1.rank.val + 1 = ceilHalf n := by
              rw [step_rank_preserved_of_InSswap (Rmax := Rmax) (Emax := Emax)
                (Dmax := Dmax) hn0 hS μ]; exact hμ_med
            have hμ_timer_post : (D.step P μ v μ).1.timer = 0 := by
              rw [show (D.step P μ v μ).1.timer = ((P.δ (D μ, D v)).1).timer from
                congrArg AgentState.timer (Config.step_fst_state P D huv)]
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
            refine Or.inr (Or.inr (Or.inr ⟨hS', hM', ?_⟩))
            apply hmax_zero_of_not_live _ hS'
            rw [MedianTimerAtLeast]; push_neg
            exact ⟨μ, hμ_rank_post, by rw [hμ_timer_post]; norm_num⟩
          · -- broke swap → CRS
            exact Or.inr (Or.inr (Or.inl
              (crs_of_InSswap_break_with_MedC hn4 hn0 hRmax hS hM hS'))))
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

-- From a live MAC swap, the expected time to `consensus ∨ CorrectResetSeed` is polynomial.
set_option maxHeartbeats 1000000 in
theorem MAClive_to_consensus_or_crs
    (hn4 : 4 ≤ n) (hn0 : 0 < n) (hRmax : n ≤ Rmax) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (T_timer : ℕ)
    (C : Config (AgentState n) Opinion n)
    (hSswap : InSswap C)
    (hMedCorrect : MedianAnswerCorrect C)
    (hTimerLo : MedianTimerAtLeast 1 C)
    (hTimerHi : IsTimerBoundedConfig T_timer C) :
    Probability.expectedHittingTime
      (PEMProtocolCoupled n Rmax Emax Dmax hn0)
      (by omega : 2 ≤ n) C
      (fun D => IsConsensusConfig D ∨ CorrectResetSeed D) ≤
      ((T_timer * n * (n - 1) + n * (n - 1) : ℕ) : ENNReal) := by
  classical
  set P := PEMProtocolCoupled n Rmax Emax Dmax hn0 with hP
  have hMid : Probability.expectedHittingTime P (by omega : 2 ≤ n) C
      (fun D => IsConsensusConfig D ∨ CorrectResetSeed D ∨
        (InSswap D ∧ MedianAnswerCorrect D ∧ maxMedianTimer D = 0)) ≤
      ((T_timer * n * (n - 1) : ℕ) : ENNReal) :=
    timer_drain_to_zero_productive hn4 hn0 hRmax T_timer C hSswap hMedCorrect hTimerLo hTimerHi
  have hGoal : ∀ D : Config (AgentState n) Opinion n,
      (IsConsensusConfig D ∨ CorrectResetSeed D ∨
        (InSswap D ∧ MedianAnswerCorrect D ∧ maxMedianTimer D = 0)) →
      Probability.expectedHittingTime P (by omega : 2 ≤ n) D
        (fun D => IsConsensusConfig D ∨ CorrectResetSeed D) ≤
        ((n * (n - 1) : ℕ) : ENNReal) := by
    intro D hMidD
    rcases hMidD with hc | hcrs | ⟨hSD, hMD, hmax0⟩
    · exact le_of_eq_of_le
        (Probability.expectedHittingTime_eq_zero_of_goal P (by omega : 2 ≤ n) D _ (Or.inl hc))
        zero_le
    · exact le_of_eq_of_le
        (Probability.expectedHittingTime_eq_zero_of_goal P (by omega : 2 ≤ n) D _ (Or.inr hcrs))
        zero_le
    · have hTimer0 : ∀ μ : Fin n, (D μ).1.rank.val + 1 = ceilHalf n → (D μ).1.timer = 0 := by
        intro μ hμ
        have hle : (if (D μ).1.rank.val + 1 = ceilHalf n then (D μ).1.timer else 0)
            ≤ maxMedianTimer D := by
          unfold maxMedianTimer
          exact Finset.le_sup
            (f := fun μ => if (D μ).1.rank.val + 1 = ceilHalf n then (D μ).1.timer else 0)
            (Finset.mem_univ μ)
        rw [hmax0, if_pos hμ] at hle
        omega
      by_cases hw : 0 < wrongAnswerCount D
      · exact PEM_expected_reset_trigger_v2 hn4 hn0 hRmax hEmax hDmax D hSD hMD hw hTimer0
      · have hw0 : wrongAnswerCount D = 0 := by omega
        exact le_of_eq_of_le
          (Probability.expectedHittingTime_eq_zero_of_goal P (by omega : 2 ≤ n) D _
            (Or.inl (isConsensusConfig_of_InSswap_of_wrongAnswerCount_zero hSD hw0)))
          zero_le
  have hMidGoal : ∀ D : Config (AgentState n) Opinion n,
      (IsConsensusConfig D ∨ CorrectResetSeed D) →
      (IsConsensusConfig D ∨ CorrectResetSeed D ∨
        (InSswap D ∧ MedianAnswerCorrect D ∧ maxMedianTimer D = 0)) := by
    intro D hD
    rcases hD with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  have hadd := Probability.expectedHittingTime_add_le P (by omega : 2 ≤ n) C
    (fun D => IsConsensusConfig D ∨ CorrectResetSeed D ∨
      (InSswap D ∧ MedianAnswerCorrect D ∧ maxMedianTimer D = 0))
    (fun D => IsConsensusConfig D ∨ CorrectResetSeed D)
    ((T_timer * n * (n - 1) : ℕ) : ENNReal) ((n * (n - 1) : ℕ) : ENNReal)
    hMid hGoal hMidGoal
  refine hadd.trans ?_
  rw [← Nat.cast_add]

end SSEM
