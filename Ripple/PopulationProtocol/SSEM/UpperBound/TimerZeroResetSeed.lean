import Ripple.PopulationProtocol.SSEM.UpperBound
import Ripple.PopulationProtocol.SSEM.UpperBound.CRSOdd
import Ripple.PopulationProtocol.SSEM.UpperBound.CRSEvenTimerPos

namespace Ripple.PopulationProtocol.SSEM

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

/-! General step properties (moved out of this file). -/

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

end Ripple.PopulationProtocol.SSEM
