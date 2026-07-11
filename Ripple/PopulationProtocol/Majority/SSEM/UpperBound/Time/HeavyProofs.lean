import Ripple.PopulationProtocol.Majority.SSEM.UpperBound.Time.Bridge
import Ripple.PopulationProtocol.Majority.SSEM.UpperBound.Time.CRSOdd
import Ripple.PopulationProtocol.Majority.SSEM.UpperBound.Time.CRSEvenTimerPos

namespace SSEM

open scoped ENNReal

/-! Strategy sketch for hConsensusBound using the bridge lemma:

Step 1: E[T from InSswap to DecisionProgressFull] ≤ n(n-1)
  Use expectedHittingTime_mono_goal on PEM_expected_Tswap_..._or_exit_le
  (needs exit_target_subset_DecisionProgress — protocol-specific)

Step 2: E[T from DecisionProgressFull to IsConsensusConfig]
  Case MedianAnswerCorrect:
    Use epidemic_timer_branch_to_consensus (deterministic) +
    expectedHittingTime_le_of_deterministic_descent (bridge lemma)
    → E[T] ≤ wrongAnswerCount · n(n-1) ≤ n · n(n-1) = n²(n-1)
  Case CorrectResetSeed:
    Use reset epidemic propagation (nonResettingCount descent)
    → E[T] ≤ nonResettingCount · n(n-1) ≤ n · n(n-1) = n²(n-1)

Step 3: Strong Markov composition
  E[T to consensus] ≤ n(n-1) + n²(n-1) ≤ 2n³ ≤ 10·Rmax·n²
  (since Rmax ≥ n → 10·Rmax·n² ≥ 10n³ ≥ 2n³) -/

/-! General step properties (moved to Bridge.lean). -/

set_option maxRecDepth 65536 in
set_option maxHeartbeats 800000000 in
theorem step_median_answer_of_InSswap_both_v2
    {n Rmax Emax Dmax : ℕ} (hn0 : 0 < n) (hn4 : 4 ≤ n)
    {D : Config (AgentState n) Opinion n}
    (hS : InSswap D) {i j : Fin n}
    (hS' : InSswap (D.step (PEMProtocolCoupled n Rmax Emax Dmax hn0) i j))
    (hM : MedianAnswerCorrect D) :
    MedianAnswerCorrect (D.step (PEMProtocolCoupled n Rmax Emax Dmax hn0) i j) := by
  set P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  have hmaj : majorityAnswer (D.step P i j) = majorityAnswer D := by
    simpa [P, PEMProtocolCoupled, PEMProtocol] using
      majorityAnswer_step_eq (trank := Rmax) (Rmax := Rmax)
        (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0) D i j
  intro ν hν; rw [hmaj]
  have hν_pre : (D ν).1.rank.val + 1 = ceilHalf n := by
    rw [← step_rank_preserved_of_InSswap (Rmax := Rmax) (Emax := Emax)
      (Dmax := Dmax) hn0 hS ν]; exact hν
  -- XHUANG_PROOF_V2_SENTINEL: do not overwrite
  by_cases hij : i = j
  · subst hij; simp [Config.step]; exact hM ν hν_pre
  have hsi := hS.toInSrank.allSettled i
  have hsj := hS.toInSrank.allSettled j
  have hrij : (D i).1.rank ≠ (D j).1.rank :=
    fun h => hij (hS.toInSrank.ranks_inj h)
  have hRD := rankDeltaOSSR_satisfies_fix (Rmax := Rmax) (Emax := Emax)
    (Dmax := Dmax) (hn := hn0) (D i).1 (D j).1 hsi hsj hrij
  have h_no_swap := hS.swap_condition_false i j
  have h_tie_outT : ∀ (μ ν' : Fin n),
      (D μ).1.rank.val + 1 = n / 2 → (D ν').1.rank.val + 1 = n / 2 + 1 →
      n % 2 = 0 → (D μ).2 ≠ (D ν').2 → majorityAnswer D = .outT := by
    intro μ ν' hμR hν'R hpar hdis
    have h_sum := nAOf_add_nBOf D
    have hnA : nAOf D = n / 2 := by
      rcases hxμ : (D μ).2 with _ | _
      · have h1 : (D μ).1.rank.val < nAOf D := (hS.input_rank μ).mp hxμ
        have hxν' : (D ν').2 = Opinion.B := by
          cases hν2 : (D ν').2 with
          | A => exfalso; apply hdis; rw [hxμ, hν2]
          | B => rfl
        have h2 : ¬ ((D ν').1.rank.val < nAOf D) := by
          intro h; have := (hS.input_rank ν').mpr h
          rw [hxν'] at this; cases this
        omega
      · have h1 : ¬ ((D μ).1.rank.val < nAOf D) := by
          intro h; have := (hS.input_rank μ).mpr h
          rw [hxμ] at this; cases this
        have hxν' : (D ν').2 = Opinion.A := by
          cases hν2 : (D ν').2 with
          | A => rfl
          | B => exfalso; apply hdis; rw [hxμ, hν2]
        have h2 : (D ν').1.rank.val < nAOf D := (hS.input_rank ν').mp hxν'
        omega
    have hnB : nBOf D = n / 2 := by omega
    unfold majorityAnswer; simp [hnA, hnB]
  have h_agree_majA : ∀ (μ ν' : Fin n),
      (D μ).1.rank.val + 1 = n / 2 → (D ν').1.rank.val + 1 = n / 2 + 1 →
      n % 2 = 0 → (D μ).2 = (D ν').2 → (D μ).2 = Opinion.A →
      nAOf D > nBOf D := by
    intro μ ν' hμR hν'R hpar hag hA
    have h_sum := nAOf_add_nBOf D
    have hν'A : (D ν').2 = Opinion.A := by rw [← hag]; exact hA
    have hν'_lt : (D ν').1.rank.val < nAOf D := (hS.input_rank ν').mp hν'A
    omega
  have h_agree_majB : ∀ (μ ν' : Fin n),
      (D μ).1.rank.val + 1 = n / 2 → (D ν').1.rank.val + 1 = n / 2 + 1 →
      n % 2 = 0 → (D μ).2 = (D ν').2 → (D μ).2 = Opinion.B →
      nBOf D > nAOf D := by
    intro μ ν' hμR hν'R hpar hag hB
    have h_sum := nAOf_add_nBOf D
    have hμB : (D μ).2 = Opinion.B := hB
    have hμ_not_A : ¬ ((D μ).1.rank.val < nAOf D) := by
      intro h; have := (hS.input_rank μ).mpr h
      rw [hμB] at this; cases this
    omega
  by_cases hνi : ν = i
  · subst hνi
    have h_fst := Config.step_fst_state P D hij
    rw [show (D.step P ν j ν).1.answer = ((P.δ (D ν, D j)).1).answer from
      congrArg AgentState.answer h_fst]
    show (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
      (D ν, D j)).1.answer = majorityAnswer D
    have hrank_νj : (D ν).1.rank.val ≠ (D j).1.rank.val := by
      intro h; apply hij
      exact hS.toInSrank.ranks_inj (Fin.ext h)
    by_cases hpar : n % 2 = 0
    · have hceil : ceilHalf n = n / 2 := by unfold ceilHalf; omega
      have hνR : (D ν).1.rank.val + 1 = n / 2 := by rw [← hceil]; exact hν_pre
      have hνR_ceil : (D ν).1.rank.val + 1 = ceilHalf n := hν_pre
      have hN_ne1 : ¬ (n / 2 + 1 = n / 2) := by omega
      have hN_ne2 : ¬ (n / 2 = n / 2 + 1) := by omega
      by_cases hjR : (D j).1.rank.val + 1 = n / 2 + 1
      · by_cases hxeq : (D ν).2 = (D j).2
        · have htr := transitionPEM_at_median_pair_even_agreed_inputs
            (trank := Rmax) (Rmax := Rmax)
            (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
            (rankDeltaOSSR_satisfies_fix (Rmax := Rmax) (Emax := Emax)
              (Dmax := Dmax) (hn := hn0)) hsi hsj hpar hνR hjR hxeq hn4
          rw [show (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
            (D ν, D j)).1.answer = opinionToAnswer (D ν).2 from
            congrArg AgentState.answer (congrArg Prod.fst htr)]
          exact opinionToAnswer_lower_median_eq_majorityAnswer_even
            hS hνR hpar (by
              rcases hx : (D ν).2 with _ | _
              · have := h_agree_majA ν j hνR hjR hpar hxeq hx; omega
              · have := h_agree_majB ν j hνR hjR hpar hxeq hx; omega)
        · have h_no_swap_disagree : ¬ ((D ν).2 = Opinion.B ∧ (D j).2 = Opinion.A) := by
            intro ⟨hxνB, hxjA⟩
            have h_nA_lo : ¬ ((D ν).1.rank.val < nAOf D) := by
              intro h; have := (hS.input_rank ν).mpr h
              rw [hxνB] at this; cases this
            have h_nA_hi : (D j).1.rank.val < nAOf D := (hS.input_rank j).mp hxjA
            omega
          have htr := transitionPEM_at_median_pair_even_disagreed_inputs
            (trank := Rmax) (Rmax := Rmax)
            (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
            (rankDeltaOSSR_satisfies_fix (Rmax := Rmax) (Emax := Emax)
              (Dmax := Dmax) (hn := hn0)) hsi hsj hpar hνR hjR hxeq
            h_no_swap_disagree hn4
          rw [show (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
            (D ν, D j)).1.answer = .outT from
            congrArg AgentState.answer (congrArg Prod.fst htr)]
          exact (h_tie_outT ν j hνR hjR hpar hxeq).symm
      · have hM_ν := hM ν hν_pre
        have hjR_no_lower : ¬ ((D j).1.rank.val + 1 = n / 2) := by
          intro h; apply hrank_νj; omega
        have hjR_no_med_ceil : ¬ ((D j).1.rank.val + 1 = ceilHalf n) := by
          rw [hceil]; exact hjR_no_lower
        unfold transitionPEM transitionPEM_phase4 transitionPEM_prePhase4
          phase4_swap phase4_decide phase4_propagate
        simp only [hRD, hsi, hsj, ne_eq,
          role_settled_ne_resetting,
          not_true_eq_false, not_false_eq_true,
          false_and, and_false, if_false,
          and_self, if_true, h_no_swap, hpar, hνR, hjR, hN_ne1, hN_ne2,
          hνR_ceil, hjR_no_lower, hjR_no_med_ceil]
        (first | exact hM_ν | (split_ifs <;> (first | exact hM_ν | (exfalso; simp_all; omega))))
    · have hjR_no_med : ¬ ((D j).1.rank.val + 1 = ceilHalf n) := by
        intro h; apply hrank_νj
        have : (D ν).1.rank.val + 1 = (D j).1.rank.val + 1 := by rw [hν_pre, h]
        omega
      unfold transitionPEM transitionPEM_phase4 transitionPEM_prePhase4
        phase4_swap phase4_decide phase4_propagate
      simp only [hRD, hsi, hsj, ne_eq,
        role_settled_ne_resetting,
        not_true_eq_false, not_false_eq_true,
        false_and, and_false, if_false,
        and_self, if_true, h_no_swap, hpar, hν_pre, hjR_no_med]
      have hOdd := opinionToAnswer_median_eq_majorityAnswer_odd hS hν_pre hpar
      (first | exact hOdd | (split_ifs <;> (first | exact hOdd | (exfalso; simp_all; omega))))
  by_cases hνj : ν = j
  · subst hνj
    have h_snd := Config.step_snd_state P D hij (Ne.symm hij)
    rw [show (D.step P i ν ν).1.answer = ((P.δ (D i, D ν)).2).answer from
      congrArg AgentState.answer h_snd]
    show (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
      (D i, D ν)).2.answer = majorityAnswer D
    have hrank_iν : (D i).1.rank.val ≠ (D ν).1.rank.val := by
      intro h; apply hij
      exact hS.toInSrank.ranks_inj (Fin.ext h)
    by_cases hpar : n % 2 = 0
    · have hceil : ceilHalf n = n / 2 := by unfold ceilHalf; omega
      have hνR : (D ν).1.rank.val + 1 = n / 2 := by rw [← hceil]; exact hν_pre
      have hνR_ceil : (D ν).1.rank.val + 1 = ceilHalf n := hν_pre
      have hN_ne1 : ¬ (n / 2 + 1 = n / 2) := by omega
      have hN_ne2 : ¬ (n / 2 = n / 2 + 1) := by omega
      by_cases hiR : (D i).1.rank.val + 1 = n / 2 + 1
      · have hiR_no_med : ¬ ((D i).1.rank.val + 1 = ceilHalf n) := by
          rw [hceil]; omega
        have hiR_no_max : ¬ ((D i).1.rank.val + 1 = n) := by omega
        unfold transitionPEM transitionPEM_phase4 transitionPEM_prePhase4
          phase4_swap phase4_decide phase4_propagate
        simp only [hRD, hsi, hsj, ne_eq,
          role_settled_ne_resetting,
          not_true_eq_false, not_false_eq_true,
          false_and, and_false, if_false,
          and_self, if_true, h_no_swap, hpar, hνR, hiR, hN_ne1, hN_ne2,
          hνR_ceil, hiR_no_med, hiR_no_max]
        by_cases hxeq : (D i).2 = (D ν).2
        · simp only [hxeq, if_true]
          have hAns := opinionToAnswer_lower_median_eq_majorityAnswer_even
            hS hνR hpar (by
              rcases hx : (D ν).2 with _ | _
              · have := h_agree_majA ν i hνR hiR hpar hxeq.symm hx; omega
              · have := h_agree_majB ν i hνR hiR hpar hxeq.symm hx; omega)
          (first | exact hAns | (split_ifs <;> (first | exact hAns | (exfalso; simp_all; omega))))
        · have hxsym : (D ν).2 ≠ (D i).2 := Ne.symm hxeq
          simp only [hxsym, if_false]
          have hOutT := (h_tie_outT ν i hνR hiR hpar (Ne.symm hxeq)).symm
          (first | exact hOutT | (split_ifs <;> (first | exact hOutT | (exfalso; simp_all; omega))))
      · have hM_ν := hM ν hν_pre
        have hiR_ne_med : ¬ ((D i).1.rank.val + 1 = n / 2) := by
          intro h; apply hrank_iν
          have : (D i).1.rank.val + 1 = (D ν).1.rank.val + 1 := by rw [h, hνR]
          omega
        have hiR_ne_med_ceil : ¬ ((D i).1.rank.val + 1 = ceilHalf n) := by
          rw [hceil]; exact hiR_ne_med
        unfold transitionPEM transitionPEM_phase4 transitionPEM_prePhase4
          phase4_swap phase4_decide phase4_propagate
        simp only [hRD, hsi, hsj, ne_eq,
          role_settled_ne_resetting,
          not_true_eq_false, not_false_eq_true,
          false_and, and_false, if_false,
          and_self, if_true, h_no_swap, hpar, hνR, hiR, hN_ne1, hN_ne2,
          hνR_ceil, hiR_ne_med, hiR_ne_med_ceil]
        (first | exact hM_ν | (split_ifs <;> (first | exact hM_ν | (exfalso; simp_all; omega))))
    · have hiR_no_med : ¬ ((D i).1.rank.val + 1 = ceilHalf n) := by
        intro h; apply hrank_iν
        have : (D i).1.rank.val + 1 = (D ν).1.rank.val + 1 := by rw [h, hν_pre]
        omega
      unfold transitionPEM transitionPEM_phase4 transitionPEM_prePhase4
        phase4_swap phase4_decide phase4_propagate
      simp only [hRD, hsi, hsj, ne_eq,
        role_settled_ne_resetting,
        not_true_eq_false, not_false_eq_true,
        false_and, and_self, if_false,
        and_false, if_true, h_no_swap, hpar, hν_pre, hiR_no_med]
      have hOdd := opinionToAnswer_median_eq_majorityAnswer_odd hS hν_pre hpar
      (first | exact hOdd | (split_ifs <;> (first | exact hOdd | (exfalso; simp_all; omega))))
  · have hbyst : D.step P i j ν = D ν := by
      unfold Config.step; simp [hij, hνi, hνj]
    rw [show (D.step P i j ν).1.answer = (D ν).1.answer from
      congrArg (fun x => x.1.answer) hbyst]
    exact hM ν hν_pre

/-! Phase C.2: Median-correct sub-phase (timer drain → seed → epidemic).
From InSswap + MedianAnswerCorrect + timer≥1 + wrongAnswer > 0:
E[T to consensus] ≤ O(Rmax·n²). Uses epidemic reachability. -/

/-! Phase C.2 sub-decomposition (median correct → consensus):

Sub-phase C.2a: Timer drain. From InSswap + MedianCorrect + timer≥1:
  potential = medianTimer, descent at (median,max) pair.
  E[T to timer=0 ∨ consensus] ≤ timer · n(n-1) ≤ 7(Rmax+4) · n(n-1)

Sub-phase C.2b: Reset seed creation. When timer=0 + answers disagree:
  One (median,max) interaction triggers reset → CorrectResetSeed.
  E[T to CorrectResetSeed ∨ consensus] ≤ n(n-1)

Sub-phase C.2c: Epidemic propagation. From CorrectResetSeed:
  potential = nonResettingCount, descent via propagate-reset.
  E[T to all-resetting ∨ consensus] ≤ n · n(n-1)

Sub-phase C.2d: Re-ranking + consensus. From all-resetting with correct answer:
  potential = resetFuel → ranking → InSswap → consensus.
  E[T] ≤ O(Rmax · n²)

Total: O(Rmax · n²). -/

/-! Stage 1: Timer drain. Inv = InSswap ∧ MedianCorrect ∧ timer≥1,
φ = medianTimer. Each (median,max) step decreases timer. -/

/-! φ for timer drain: max timer across all median-rank agents.
In InSswap there is exactly one, but we define it for all configs. -/
set_option maxHeartbeats 800000000 in
theorem step_timer_zero_median_wrong_nonupper_creates_CorrectResetSeed
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n) (hRmax : n ≤ Rmax)
    {D : Config (AgentState n) Opinion n}
    (hS : InSswap D)
    {μ v : Fin n} (hμv : μ ≠ v)
    (hμ_med : (D μ).1.rank.val + 1 = ceilHalf n)
    (hμ_timer : (D μ).1.timer = 0)
    (hμ_correct : (D μ).1.answer = majorityAnswer D)
    (hv_wrong : (D v).1.answer ≠ majorityAnswer D)
    (hv_no_upper : (D v).1.rank.val + 1 ≠ n / 2 + 1) :
    let P := PEMProtocolCoupled n Rmax Emax Dmax hn0
    CorrectResetSeed (D.step P μ v) := by
  classical
  set P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  have hv_no_med : (D v).1.rank.val + 1 ≠ ceilHalf n := by
    intro h; apply hμv; apply hS.toInSrank.ranks_inj
    exact Fin.ext (Nat.add_right_cancel (hμ_med.trans h.symm))
  have hsi := hS.toInSrank.allSettled μ
  have hsv := hS.toInSrank.allSettled v
  have hrij : (D μ).1.rank ≠ (D v).1.rank := fun h => hμv (hS.toInSrank.ranks_inj h)
  have hRD := rankDeltaOSSR_satisfies_fix (Rmax := Rmax) (Emax := Emax)
    (Dmax := Dmax) (hn := hn0) (D μ).1 (D v).1 hsi hsv hrij
  have h_no_swap := hS.swap_condition_false μ v
  have h_post_diff : (D μ).1.answer ≠ (D v).1.answer := by
    rw [hμ_correct]; exact fun h => hv_wrong h.symm
  have h_fst := Config.step_fst_state P D hμv
  have h_snd := Config.step_snd_state P D hμv (Ne.symm hμv)
  by_cases hpar : n % 2 = 0
  · -- EVEN parity
    have hceil : ceilHalf n = n / 2 := by unfold ceilHalf; omega
    have hμ_lower : (D μ).1.rank.val + 1 = n / 2 := by rw [← hceil]; exact hμ_med
    have hv_not_lower : (D v).1.rank.val + 1 ≠ n / 2 := by
      rw [← hceil]; exact hv_no_med
    have htr := propagation_reset_fires_even_lower_timer_zero_no_swap_trace
      (trank := Rmax) (Rmax := Rmax) (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
      rankDeltaOSSR_satisfies_fix hS.toInSrank hμv hpar hμ_lower hv_not_lower
      hv_no_upper hμ_timer h_no_swap h_post_diff
    have h_post_μ : (D.step P μ v μ).1 =
        { (D μ).1 with role := .Resetting, leader := .L, resetcount := Rmax } := by
      rw [h_fst]; show (transitionPEM _ _ _ _ _).1 = _; rw [htr]
    have h_post_v : (D.step P μ v v).1 =
        { (D v).1 with role := .Resetting, leader := .L, resetcount := Rmax, answer := (D μ).1.answer } := by
      rw [h_snd]; show (transitionPEM _ _ _ _ _).2 = _; rw [htr]
    have h_post_others : ∀ w, w ≠ μ → w ≠ v → (D.step P μ v w) = D w := by
      intro w hw hwv; unfold Config.step; simp [hμv, hw, hwv]
    have h_maj : majorityAnswer (D.step P μ v) = majorityAnswer D := by
      simpa [P, PEMProtocolCoupled, PEMProtocol] using
        majorityAnswer_step_eq (trank := Rmax) (Rmax := Rmax)
          (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0) D μ v
    have h_nrc : nonResettingCount (D.step P μ v) ≤ n - 2 := by
      unfold nonResettingCount
      set S := Finset.univ.filter (fun w : Fin n => (D.step P μ v w).1.role ≠ .Resetting)
      have hμ_not : μ ∉ S := by simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_not]; rw [h_post_μ]
      have hv_not : v ∉ S := by simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_not]; rw [h_post_v]
      have hS_sub : S ⊆ (Finset.univ \ {μ, v}) := by
        intro w hw; simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨fun h => hμ_not (h ▸ hw), fun h => hv_not (h ▸ hw)⟩
      calc S.card ≤ (Finset.univ \ ({μ, v} : Finset (Fin n))).card := Finset.card_le_card hS_sub
        _ = n - 2 := by rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin, Finset.card_pair hμv]
    refine ⟨⟨μ, ?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [h_post_μ]
    · rw [h_post_μ]; exact lt_of_le_of_lt h_nrc (lt_of_lt_of_le (by omega) hRmax)
    · rw [h_post_μ]
    · rw [h_post_μ]; simp [h_maj, hμ_correct]
    · intro w hw_res
      by_cases hwμ : w = μ
      · subst hwμ; rw [h_post_μ]; exact ⟨by simp; omega, by simp [h_maj, hμ_correct]⟩
      · by_cases hwv : w = v
        · subst hwv; rw [h_post_v]; exact ⟨by simp; omega, by simp [h_maj, hμ_correct]⟩
        · exfalso; rw [show (D.step P μ v w).1 = (D w).1 from congrArg Prod.fst (h_post_others w hwμ hwv)] at hw_res
          rw [hS.allSettled w] at hw_res; exact Role.noConfusion hw_res
  · -- ODD parity
    have hμ_ans_eq : opinionToAnswer (D μ).2 = (D μ).1.answer := by
      rw [opinionToAnswer_median_eq_majorityAnswer_odd hS hμ_med hpar, hμ_correct]
    have h_post_diff_odd : opinionToAnswer (D μ).2 ≠ (D v).1.answer := by
      rw [hμ_ans_eq]; exact h_post_diff
    have htr := propagation_reset_fires_no_swap_trace
      (trank := Rmax) (Rmax := Rmax) (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
      rankDeltaOSSR_satisfies_fix hS.toInSrank hμv hμ_med hv_no_med
      hμ_timer h_no_swap hpar h_post_diff_odd
    have h_post_μ : (D.step P μ v μ).1 =
        { (D μ).1 with role := .Resetting, leader := .L, resetcount := Rmax, answer := opinionToAnswer (D μ).2 } := by
      rw [h_fst]; show (transitionPEM _ _ _ _ _).1 = _; rw [htr]
    have h_post_v : (D.step P μ v v).1 =
        { (D v).1 with role := .Resetting, leader := .L, resetcount := Rmax, answer := opinionToAnswer (D μ).2 } := by
      rw [h_snd]; show (transitionPEM _ _ _ _ _).2 = _; rw [htr]
    have h_post_others : ∀ w, w ≠ μ → w ≠ v → (D.step P μ v w) = D w := by
      intro w hw hwv; unfold Config.step; simp [hμv, hw, hwv]
    have h_maj : majorityAnswer (D.step P μ v) = majorityAnswer D := by
      simpa [P, PEMProtocolCoupled, PEMProtocol] using
        majorityAnswer_step_eq (trank := Rmax) (Rmax := Rmax)
          (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0) D μ v
    have h_nrc : nonResettingCount (D.step P μ v) ≤ n - 2 := by
      unfold nonResettingCount
      set S := Finset.univ.filter (fun w : Fin n => (D.step P μ v w).1.role ≠ .Resetting)
      have hμ_not : μ ∉ S := by simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_not]; rw [h_post_μ]
      have hv_not : v ∉ S := by simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_not]; rw [h_post_v]
      have hS_sub : S ⊆ (Finset.univ \ {μ, v}) := by
        intro w hw; simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨fun h => hμ_not (h ▸ hw), fun h => hv_not (h ▸ hw)⟩
      calc S.card ≤ (Finset.univ \ ({μ, v} : Finset (Fin n))).card := Finset.card_le_card hS_sub
        _ = n - 2 := by rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin, Finset.card_pair hμv]
    refine ⟨⟨μ, ?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [h_post_μ]
    · rw [h_post_μ]; exact lt_of_le_of_lt h_nrc (lt_of_lt_of_le (by omega) hRmax)
    · rw [h_post_μ]
    · rw [h_post_μ]; simp [h_maj, hμ_ans_eq, hμ_correct]
    · intro w hw_res
      by_cases hwμ : w = μ
      · subst hwμ; rw [h_post_μ]; exact ⟨by simp; omega, by simp [h_maj, hμ_ans_eq, hμ_correct]⟩
      · by_cases hwv : w = v
        · subst hwv; rw [h_post_v]; exact ⟨by simp; omega, by simp [h_maj, hμ_ans_eq, hμ_correct]⟩
        · exfalso; rw [show (D.step P μ v w).1 = (D w).1 from congrArg Prod.fst (h_post_others w hwμ hwv)] at hw_res
          rw [hS.allSettled w] at hw_res; exact Role.noConfusion hw_res

end SSEM
