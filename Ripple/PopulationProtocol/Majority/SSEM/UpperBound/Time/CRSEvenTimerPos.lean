import Ripple.PopulationProtocol.Majority.SSEM.UpperBound.Time.Bridge
import Ripple.PopulationProtocol.Majority.SSEM.UpperBound.Time.TransitionLemmas

namespace SSEM

open scoped ENNReal

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000000 in
theorem step_timer_le_one_median_max_creates_CorrectResetSeed
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n) (hRmax : n ≤ Rmax)
    {D : Config (AgentState n) Opinion n}
    (hS : InSswap D)
    {μ v : Fin n} (hμv : μ ≠ v)
    (hμ_med : (D μ).1.rank.val + 1 = ceilHalf n)
    (hμ_timer : (D μ).1.timer ≤ 1)
    (hv_max : (D v).1.rank.val + 1 = n)
    (hμ_correct : (D μ).1.answer = majorityAnswer D)
    (hv_wrong : (D v).1.answer ≠ majorityAnswer D) :
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
  -- Derive post-step states via trace lemmas (dispatch by parity × timer)
  -- In all cases, both μ and v become Resetting with Rmax resetcount
  have hv_not_upper : (D v).1.rank.val + 1 ≠ n / 2 + 1 := by omega
  by_cases hpar : n % 2 = 0
  · -- EVEN
    have hceil : ceilHalf n = n / 2 := by unfold ceilHalf; omega
    have hμ_lower : (D μ).1.rank.val + 1 = n / 2 := by rw [← hceil]; exact hμ_med
    have hv_not_lower : (D v).1.rank.val + 1 ≠ n / 2 := by omega
    by_cases hTimer0 : (D μ).1.timer = 0
    · -- timer = 0: use timer_zero trace
      have htr := propagation_reset_fires_even_lower_timer_zero_no_swap_trace
        (trank := Rmax) (Rmax := Rmax) (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
        rankDeltaOSSR_satisfies_fix hS.toInSrank hμv hpar hμ_lower hv_not_lower
        hv_not_upper hTimer0 h_no_swap h_post_diff
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
        classical
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
    · -- timer = 1: use timer_one trace
      have hTimer1 : (D μ).1.timer = 1 := by omega
      have htr := propagation_reset_fires_even_lower_timer_one_max_no_swap_trace
        (trank := Rmax) (Rmax := Rmax) (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
        rankDeltaOSSR_satisfies_fix hS.toInSrank hn4 hμv hpar hμ_lower hv_max
        hTimer1 h_no_swap h_post_diff
      have h_post_μ : (D.step P μ v μ).1 =
          { (D μ).1 with timer := 0, role := .Resetting, leader := .L, resetcount := Rmax } := by
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
        classical
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
  · -- ODD
    have hμ_ans_eq : opinionToAnswer (D μ).2 = (D μ).1.answer := by
      rw [opinionToAnswer_median_eq_majorityAnswer_odd hS hμ_med hpar, hμ_correct]
    have h_post_diff_odd : opinionToAnswer (D μ).2 ≠ (D v).1.answer := by
      rw [hμ_ans_eq]; exact h_post_diff
    by_cases hTimer0 : (D μ).1.timer = 0
    · have htr := propagation_reset_fires_no_swap_trace
        (trank := Rmax) (Rmax := Rmax) (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
        rankDeltaOSSR_satisfies_fix hS.toInSrank hμv hμ_med hv_no_med
        hTimer0 h_no_swap hpar h_post_diff_odd
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
        classical
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
    · have hTimer1 : (D μ).1.timer = 1 := by omega
      have htr := propagation_reset_fires_no_swap_max_timer_one_trace
        (trank := Rmax) (Rmax := Rmax) (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
        rankDeltaOSSR_satisfies_fix hS.toInSrank hn4 hμv hμ_med hv_max
        hTimer1 h_no_swap hpar h_post_diff_odd
      have h_post_μ : (D.step P μ v μ).1 =
          { (D μ).1 with role := .Resetting, leader := .L, resetcount := Rmax, answer := opinionToAnswer (D μ).2, timer := 0 } := by
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
        classical
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

/-! ### Both-Settled → InSswap preserved (even) -/

private theorem InSswap_preserved_of_output_settled_even_tp
    {n Rmax Emax Dmax : ℕ} (hn0 : 0 < n)
    {D : Config (AgentState n) Opinion n} (hS : InSswap D)
    {i j : Fin n} (hij : i ≠ j)
    (hri : (D.step (PEMProtocolCoupled n Rmax Emax Dmax hn0) i j i).1.role = .Settled)
    (hrj : (D.step (PEMProtocolCoupled n Rmax Emax Dmax hn0) i j j).1.role = .Settled) :
    InSswap (D.step (PEMProtocolCoupled n Rmax Emax Dmax hn0) i j) := by
  set P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  have h_rank_w : ∀ w, (D.step P i j w).1.rank = (D w).1.rank :=
    fun w => step_rank_preserved_of_InSswap hn0 hS w
  have h_input_w := fun w => step_input_preserved P D i j w
  have h_nA : nAOf (D.step P i j) = nAOf D := by
    simp only [P, PEMProtocolCoupled, PEMProtocol]
    exact nAOf_step_eq (trank := Rmax) (Rmax := Rmax)
      (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0) D i j
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro w
    by_cases hwi : w = i
    · exact hwi ▸ hri
    · by_cases hwj : w = j
      · exact hwj ▸ hrj
      · have : D.step P i j w = D w := by unfold Config.step; simp [hij, hwi, hwj]
        rw [this]; exact hS.allSettled w
  · intro w₁ w₂ heq
    have : (D w₁).1.rank = (D w₂).1.rank := by
      rw [← h_rank_w w₁, ← h_rank_w w₂]; exact heq
    exact hS.ranks_inj this
  · intro w; rw [h_input_w, h_rank_w, h_nA]; exact hS.input_rank w

/-! ### Main theorem: even InSswap break with MedianAnswerCorrect + timer ≥ 1 → CRS -/

set_option maxRecDepth 65536 in
set_option maxHeartbeats 800000000 in
theorem step_InSswap_break_creates_CorrectResetSeed_even_timer_pos
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n) (hRmax : n ≤ Rmax)
    {D : Config (AgentState n) Opinion n}
    (hS : InSswap D)
    (hM : MedianAnswerCorrect D)
    (hPar : n % 2 = 0)
    (hT : MedianTimerAtLeast 1 D)
    {i j : Fin n}
    (hS' : ¬ InSswap (D.step (PEMProtocolCoupled n Rmax Emax Dmax hn0) i j)) :
    CorrectResetSeed (D.step (PEMProtocolCoupled n Rmax Emax Dmax hn0) i j) := by
  classical
  set P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  -- Step 1: i = j → contradiction
  by_cases hij : i = j
  · exfalso; apply hS'; subst hij; simp [Config.step]; exact hS
  -- Step 2: basic setup
  have hsi : (D i).1.role = .Settled := hS.toInSrank.allSettled i
  have hsj : (D j).1.role = .Settled := hS.toInSrank.allSettled j
  have hrij : (D i).1.rank ≠ (D j).1.rank :=
    fun h => hij (hS.toInSrank.ranks_inj h)
  have hFix : RankDeltaSettledFix (rankDeltaOSSR Rmax Emax Dmax hn0) :=
    rankDeltaOSSR_satisfies_fix
  have hP_δ : ∀ p, P.δ p = transitionPEM n Rmax Rmax
      (rankDeltaOSSR Rmax Emax Dmax hn0) p := fun _ => rfl
  have h_fst := Config.step_fst_state P D hij
  have h_snd := Config.step_snd_state P D hij (Ne.symm hij)
  have h_no_swap := hS.swap_condition_false i j
  -- Step 3: role disjunction
  have hRoles := transitionPEM_role_settled_or_resetting_of_InSswap
    (trank := Rmax) (Rmax := Rmax) (x₀ := (D i).2) (x₁ := (D j).2)
    hFix hsi hsj hrij
  have h_role_i : (D.step P i j i).1.role = .Settled ∨
      (D.step P i j i).1.role = .Resetting := by
    rw [congrArg AgentState.role h_fst, hP_δ]; exact hRoles.1
  have h_role_j : (D.step P i j j).1.role = .Settled ∨
      (D.step P i j j).1.role = .Resetting := by
    rw [congrArg AgentState.role h_snd, hP_δ]; exact hRoles.2
  -- Step 4: case analysis on output roles
  rcases h_role_i with h_i_set | h_i_res
  · -- i stays Settled
    rcases h_role_j with h_j_set | h_j_res
    · -- Both Settled → InSswap preserved → contradiction
      exfalso; apply hS'
      exact InSswap_preserved_of_output_settled_even_tp hn0 hS hij h_i_set h_j_set
    · -- i Settled, j Resetting → fst must also be Resetting → contradiction
      exfalso
      have h_snd_res : (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
          (D i, D j)).2.role = .Resetting := by
        rw [← hP_δ, ← congrArg AgentState.role h_snd]; exact h_j_res
      have h_fst_res := transitionPEM_snd_resetting_implies_fst_of_InSswap
        (trank := Rmax) (x₀ := (D i).2) (x₁ := (D j).2)
        hFix hsi hsj hrij h_snd_res
      have h_i_set' : (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
          (D i, D j)).1.role = .Settled := by
        rw [← hP_δ, ← congrArg AgentState.role h_fst]; exact h_i_set
      rw [h_fst_res] at h_i_set'; exact Role.noConfusion h_i_set'
  · -- i becomes Resetting → j must also be Resetting
    have h_i_res' : (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
        (D i, D j)).1.role = .Resetting := by
      rw [← hP_δ, ← congrArg AgentState.role h_fst]; exact h_i_res
    have h_snd_res := transitionPEM_fst_resetting_implies_snd_of_InSswap
      (trank := Rmax) (x₀ := (D i).2) (x₁ := (D j).2)
      hFix hsi hsj hrij h_i_res'
    have h_j_res : (D.step P i j j).1.role = .Resetting := by
      rw [congrArg AgentState.role h_snd, hP_δ]; exact h_snd_res
    -- Step 5: both Resetting → determine who is median
    have h_med := transitionPEM_fst_resetting_implies_some_median_even
      (trank := Rmax) (x₀ := (D i).2) (x₁ := (D j).2)
      hFix hsi hsj hrij h_no_swap hPar h_i_res'
    rcases h_med with h_i_med | h_j_med
    · -- i is the median agent
      have hv_no_med : (D j).1.rank.val + 1 ≠ ceilHalf n :=
        fun h => hrij (Fin.ext (Nat.add_right_cancel (h_i_med.trans h.symm)))
      -- Determine that j must be at max rank
      -- (otherwise timer = 0, contradicting timer ≥ 1)
      by_cases hv_max : (D j).1.rank.val + 1 = n
      · -- j at max rank: use the first theorem
        -- Get timer ≤ 1
        have h_tl := transitionPEM_fst_resetting_s0_med_max_even_timer_le_one
          (trank := Rmax) (x₀ := (D i).2) (x₁ := (D j).2)
          hFix hsi hsj hrij h_no_swap hPar hn4 h_i_med hv_no_med hv_max h_i_res'
        -- Get answer diff (at answer level, not opinionToAnswer)
        have h_ans_diff := transitionPEM_fst_resetting_s0_med_max_even_answer_diff
          (trank := Rmax) (x₀ := (D i).2) (x₁ := (D j).2)
          hFix hsi hsj hrij h_no_swap hPar hn4 h_i_med hv_no_med hv_max h_i_res'
        -- MedianAnswerCorrect gives i has correct answer
        have hμ_correct : (D i).1.answer = majorityAnswer D := hM i h_i_med
        -- j has wrong answer
        have hv_wrong : (D j).1.answer ≠ majorityAnswer D := by
          intro heq; exact h_ans_diff (by rw [hμ_correct, heq])
        -- Delegate to the first theorem
        exact step_timer_le_one_median_max_creates_CorrectResetSeed
          hn4 hn0 hRmax hS hij h_i_med h_tl hv_max hμ_correct hv_wrong
      · -- j NOT at max rank → timer must be 0, contradicting timer ≥ 1
        exfalso
        have h_timer_zero := transitionPEM_fst_resetting_s0_med_no_max_even_timer_zero
          (trank := Rmax) (x₀ := (D i).2) (x₁ := (D j).2)
          hFix hsi hsj hrij h_no_swap hPar h_i_med hv_no_med hv_max h_i_res'
        -- MedianTimerAtLeast 1 says timer ≥ 1 for the median agent
        have h_timer_ge_1 := hT i h_i_med
        omega
    · -- j is the median agent: needs symmetric trace (same gap as CRSOdd)
      -- j is the median agent (responder), even parity
      have hi_no_med : (D i).1.rank.val + 1 ≠ ceilHalf n :=
        fun h => hrij (Fin.ext (Nat.add_right_cancel (h.trans h_j_med.symm)))
      -- Case split on whether i is at max rank
      by_cases hi_max : (D i).1.rank.val + 1 = n
      · -- i at max rank: timer ≤ 1, answer diff, build CRS from trace
        have h_tl := transitionPEM_fst_resetting_s1_med_max_even_timer_le_one
          (trank := Rmax) (x₀ := (D i).2) (x₁ := (D j).2)
          hFix hsi hsj hrij h_no_swap hPar hn4 hi_no_med h_j_med hi_max h_i_res'
        have h_ans_diff := transitionPEM_fst_resetting_s1_med_even_answer_diff
          (trank := Rmax) (x₀ := (D i).2) (x₁ := (D j).2)
          hFix hsi hsj hrij h_no_swap hPar hn4 hi_no_med h_j_med h_i_res'
        -- MedianAnswerCorrect gives j has correct answer
        have hj_correct : (D j).1.answer = majorityAnswer D := hM j h_j_med
        -- i has wrong answer
        have hi_wrong : (D i).1.answer ≠ majorityAnswer D := by
          intro heq; exact h_ans_diff (by rw [hj_correct, heq])
        -- Even parity: ceilHalf n = n/2
        have hceil : ceilHalf n = n / 2 := by unfold ceilHalf; omega
        have hj_lower : (D j).1.rank.val + 1 = n / 2 := by rw [← hceil]; exact h_j_med
        by_cases hTimer0 : (D j).1.timer = 0
        · -- timer = 0: use existing responder-median even trace
          have hi_no_lower : (D i).1.rank.val + 1 ≠ n / 2 := by rw [← hceil]; exact hi_no_med
          have hi_not_upper : (D i).1.rank.val + 1 ≠ n / 2 + 1 := by omega
          have htr := propagation_reset_fires_even_no_swap_responder_median_trace
            (trank := Rmax) (Rmax := Rmax) (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
            rankDeltaOSSR_satisfies_fix hS.toInSrank hij hPar hj_lower hi_no_lower
            hi_not_upper hTimer0 h_no_swap (h_ans_diff)
          have h_post_i : (D.step P i j i).1 =
              { (D i).1 with role := .Resetting, leader := .L, resetcount := Rmax,
                             answer := (D j).1.answer } := by
            rw [h_fst]; show (transitionPEM _ _ _ _ _).1 = _; rw [htr]
          have h_post_j : (D.step P i j j).1 =
              { (D j).1 with role := .Resetting, leader := .L, resetcount := Rmax } := by
            rw [h_snd]; show (transitionPEM _ _ _ _ _).2 = _; rw [htr]
          have h_post_others : ∀ w, w ≠ i → w ≠ j → (D.step P i j w) = D w := by
            intro w hw hwv; unfold Config.step; simp [hij, hw, hwv]
          have h_maj : majorityAnswer (D.step P i j) = majorityAnswer D := by
            simpa [P, PEMProtocolCoupled, PEMProtocol] using
              majorityAnswer_step_eq (trank := Rmax) (Rmax := Rmax)
                (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0) D i j
          have h_nrc : nonResettingCount (D.step P i j) ≤ n - 2 := by
            classical
            unfold nonResettingCount
            set S := Finset.univ.filter (fun w : Fin n => (D.step P i j w).1.role ≠ .Resetting)
            have hi_not : i ∉ S := by simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_not]; rw [h_post_i]
            have hj_not : j ∉ S := by simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_not]; rw [h_post_j]
            have hS_sub : S ⊆ (Finset.univ \ {i, j}) := by
              intro w hw; simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton, not_or]
              exact ⟨fun h => hi_not (h ▸ hw), fun h => hj_not (h ▸ hw)⟩
            calc S.card ≤ (Finset.univ \ ({i, j} : Finset (Fin n))).card := Finset.card_le_card hS_sub
              _ = n - 2 := by rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin, Finset.card_pair hij]
          refine ⟨⟨i, ?_, ?_, ?_, ?_⟩, ?_⟩
          · rw [h_post_i]
          · rw [h_post_i]; exact lt_of_le_of_lt h_nrc (lt_of_lt_of_le (by omega) hRmax)
          · rw [h_post_i]
          · rw [h_post_i]; simp [h_maj, hj_correct]
          · intro w hw_res
            by_cases hwi : w = i
            · subst hwi; rw [h_post_i]; exact ⟨by simp; omega, by simp [h_maj, hj_correct]⟩
            · by_cases hwj : w = j
              · subst hwj; rw [h_post_j]; exact ⟨by simp; omega, by simp [h_maj, hj_correct]⟩
              · exfalso; rw [show (D.step P i j w).1 = (D w).1 from congrArg Prod.fst (h_post_others w hwi hwj)] at hw_res
                rw [hS.allSettled w] at hw_res; exact Role.noConfusion hw_res
        · -- timer = 1: use new responder-median even max timer_one trace
          have hTimer1 : (D j).1.timer = 1 := by omega
          have htr := propagation_reset_fires_even_no_swap_responder_median_max_timer_one_trace
            (trank := Rmax) (Rmax := Rmax) (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
            rankDeltaOSSR_satisfies_fix hS.toInSrank hn4 hij hPar hj_lower hi_max
            hTimer1 h_no_swap (h_ans_diff)
          have h_post_i : (D.step P i j i).1 =
              { (D i).1 with role := .Resetting, leader := .L, resetcount := Rmax,
                             answer := (D j).1.answer } := by
            rw [h_fst]; show (transitionPEM _ _ _ _ _).1 = _; rw [htr]
          have h_post_j : (D.step P i j j).1 =
              { (D j).1 with role := .Resetting, leader := .L, resetcount := Rmax,
                             timer := 0 } := by
            rw [h_snd]; show (transitionPEM _ _ _ _ _).2 = _; rw [htr]
          have h_post_others : ∀ w, w ≠ i → w ≠ j → (D.step P i j w) = D w := by
            intro w hw hwv; unfold Config.step; simp [hij, hw, hwv]
          have h_maj : majorityAnswer (D.step P i j) = majorityAnswer D := by
            simpa [P, PEMProtocolCoupled, PEMProtocol] using
              majorityAnswer_step_eq (trank := Rmax) (Rmax := Rmax)
                (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0) D i j
          have h_nrc : nonResettingCount (D.step P i j) ≤ n - 2 := by
            classical
            unfold nonResettingCount
            set S := Finset.univ.filter (fun w : Fin n => (D.step P i j w).1.role ≠ .Resetting)
            have hi_not : i ∉ S := by simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_not]; rw [h_post_i]
            have hj_not : j ∉ S := by simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_not]; rw [h_post_j]
            have hS_sub : S ⊆ (Finset.univ \ {i, j}) := by
              intro w hw; simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton, not_or]
              exact ⟨fun h => hi_not (h ▸ hw), fun h => hj_not (h ▸ hw)⟩
            calc S.card ≤ (Finset.univ \ ({i, j} : Finset (Fin n))).card := Finset.card_le_card hS_sub
              _ = n - 2 := by rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin, Finset.card_pair hij]
          refine ⟨⟨i, ?_, ?_, ?_, ?_⟩, ?_⟩
          · rw [h_post_i]
          · rw [h_post_i]; exact lt_of_le_of_lt h_nrc (lt_of_lt_of_le (by omega) hRmax)
          · rw [h_post_i]
          · rw [h_post_i]; simp [h_maj, hj_correct]
          · intro w hw_res
            by_cases hwi : w = i
            · subst hwi; rw [h_post_i]; exact ⟨by simp; omega, by simp [h_maj, hj_correct]⟩
            · by_cases hwj : w = j
              · subst hwj; rw [h_post_j]; exact ⟨by simp; omega, by simp [h_maj, hj_correct]⟩
              · exfalso; rw [show (D.step P i j w).1 = (D w).1 from congrArg Prod.fst (h_post_others w hwi hwj)] at hw_res
                rw [hS.allSettled w] at hw_res; exact Role.noConfusion hw_res
      · -- i NOT at max rank → timer must be 0, contradicting timer ≥ 1
        exfalso
        have h_timer_zero := transitionPEM_fst_resetting_s1_med_no_max_even_timer_zero
          (trank := Rmax) (x₀ := (D i).2) (x₁ := (D j).2)
          hFix hsi hsj hrij h_no_swap hPar hi_no_med h_j_med hi_max h_i_res'
        -- MedianTimerAtLeast 1 says timer ≥ 1 for the median agent
        have h_timer_ge_1 := hT j h_j_med
        omega

end SSEM
