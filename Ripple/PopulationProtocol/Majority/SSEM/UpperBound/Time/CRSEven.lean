import Ripple.PopulationProtocol.Majority.SSEM.UpperBound.Time.Bridge
import Ripple.PopulationProtocol.Majority.SSEM.UpperBound.Time.TransitionLemmas
import Ripple.PopulationProtocol.Majority.SSEM.UpperBound.Time.CRSOdd

namespace SSEM

open scoped ENNReal

/-! ### phase4_propagate stays Settled when answers agree -/

set_option maxRecDepth 4096 in
private theorem phase4_propagate_fst_settled_of_eq_answer
    {n Rmax : ℕ} {b₀ b₁ : AgentState n}
    (hs₀ : b₀.role = .Settled) (heq : b₀.answer = b₁.answer) :
    (phase4_propagate n Rmax b₀ b₁).1.role = .Settled := by
  simp only [phase4_propagate]
  by_cases h1 : b₀.rank.val + 1 = ceilHalf n
  · simp only [h1, ite_true]
    by_cases h2 : b₁.rank.val + 1 = n
    · simp only [h2, ite_true]; split_ifs with hg
      · exfalso; exact hg.2 heq
      · exact hs₀
    · simp only [h2, ite_false]; split_ifs with hg
      · exfalso; exact hg.2 heq
      · exact hs₀
  · simp only [h1, ite_false]
    by_cases h3 : b₁.rank.val + 1 = ceilHalf n
    · simp only [h3, ite_true]
      by_cases h4 : b₀.rank.val + 1 = n
      · simp only [h4, ite_true]; split_ifs with hg
        · exfalso; exact hg.2 heq.symm
        · exact hs₀
      · simp only [h4, ite_false]; split_ifs with hg
        · exfalso; exact hg.2 heq.symm
        · exact hs₀
    · simp only [h3, ite_false]; exact hs₀

/-! ### Helper: InSswap preserved when both outputs stay Settled -/

private theorem InSswap_preserved_of_output_settled_even
    {n Rmax Emax Dmax : ℕ} (hn0 : 0 < n)
    {D : Config (AgentState n) Opinion n} (hS : InSswap D)
    {i j : Fin n} (hij : i ≠ j)
    (hri : (D.step (PEMProtocolCoupled n Rmax Emax Dmax hn0) i j i).1.role = .Settled)
    (hrj : (D.step (PEMProtocolCoupled n Rmax Emax Dmax hn0) i j j).1.role = .Settled) :
    InSswap (D.step (PEMProtocolCoupled n Rmax Emax Dmax hn0) i j) := by
  set P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  have h_rank_w : ∀ w, (D.step P i j w).1.rank = (D w).1.rank := fun w => step_rank_preserved_of_InSswap hn0 hS w
  have h_input_w := fun w => step_input_preserved P D i j w
  have h_nA : nAOf (D.step P i j) = nAOf D := by
    simp only [P, PEMProtocolCoupled, PEMProtocol]
    exact nAOf_step_eq (trank := Rmax) (Rmax := Rmax) (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0) D i j
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
      have h1 := h_rank_w w₁; have h2 := h_rank_w w₂; simp only [h1, h2] at heq; exact heq
    exact hS.ranks_inj this
  · intro w; rw [h_input_w, h_rank_w, h_nA]; exact hS.input_rank w

/-! ### Helper: CRS from even trace -/

set_option maxRecDepth 65536 in
set_option maxHeartbeats 800000000 in
private theorem CRS_from_even_trace
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    (hn0 : 0 < n) (hRmax : n ≤ Rmax)
    {D : Config (AgentState n) Opinion n}
    (hS : InSswap D) (hM : MedianAnswerCorrect D)
    {μ v : Fin n} (hμv : μ ≠ v)
    (hμ_med : (D μ).1.rank.val + 1 = ceilHalf n)
    {out₁ out₂ : AgentState n}
    (htr : transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0) (D μ, D v) = (out₁, out₂))
    (h1r : out₁.role = .Resetting) (h1c : out₁.resetcount = Rmax)
    (h1l : out₁.leader = .L) (h1a : out₁.answer = (D μ).1.answer)
    (h2r : out₂.role = .Resetting) (h2c : out₂.resetcount = Rmax)
    (h2a : out₂.answer = (D μ).1.answer) :
    CorrectResetSeed (D.step (PEMProtocolCoupled n Rmax Emax Dmax hn0) μ v) := by
  classical
  set P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  have hf := Config.step_fst_state P D hμv
  have hs := Config.step_snd_state P D hμv (Ne.symm hμv)
  have hsμ : (D.step P μ v μ).1 = out₁ := by rw [hf]; show (transitionPEM _ _ _ _ _).1 = _; rw [htr]
  have hsv : (D.step P μ v v).1 = out₂ := by rw [hs]; show (transitionPEM _ _ _ _ _).2 = _; rw [htr]
  have hmaj : majorityAnswer (D.step P μ v) = majorityAnswer D := by
    simpa [P, PEMProtocolCoupled, PEMProtocol] using
      majorityAnswer_step_eq (trank := Rmax) (Rmax := Rmax) (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0) D μ v
  have hcor : (D μ).1.answer = majorityAnswer D := hM μ hμ_med
  have hoth : ∀ w, w ≠ μ → w ≠ v → (D.step P μ v w) = D w := by
    intro w hw hwv; unfold Config.step; simp [hμv, hw, hwv]
  have hnrc : nonResettingCount (D.step P μ v) ≤ n - 2 := by
    unfold nonResettingCount
    set S := Finset.univ.filter (fun w : Fin n => (D.step P μ v w).1.role ≠ .Resetting)
    have hμ_not : μ ∉ S := by simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_not]; rw [hsμ]; exact h1r
    have hv_not : v ∉ S := by simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_not]; rw [hsv]; exact h2r
    calc S.card ≤ (Finset.univ \ ({μ, v} : Finset (Fin n))).card := by
          apply Finset.card_le_card; intro w hw
          simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨fun h => hμ_not (h ▸ hw), fun h => hv_not (h ▸ hw)⟩
      _ = n - 2 := by rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin, Finset.card_pair hμv]
  refine ⟨⟨μ, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [hsμ]; exact h1r
  · rw [hsμ, h1c]; exact lt_of_le_of_lt hnrc (lt_of_lt_of_le (by omega) hRmax)
  · rw [hsμ]; exact h1l
  · rw [hsμ, h1a, hcor, hmaj]
  · intro w hw
    by_cases hwμ : w = μ
    · subst hwμ; exact ⟨by rw [hsμ, h1c]; omega, by rw [hsμ, h1a, hcor, hmaj]⟩
    · by_cases hwv : w = v
      · subst hwv; exact ⟨by rw [hsv, h2c]; omega, by rw [hsv, h2a, hcor, hmaj]⟩
      · exfalso; rw [show (D.step P μ v w).1 = (D w).1 from congrArg Prod.fst (hoth w hwμ hwv)] at hw
        rw [hS.allSettled w] at hw; exact Role.noConfusion hw

/-! ### Both Resetting → CRS (even parity) -/

set_option maxRecDepth 65536 in
set_option maxHeartbeats 800000000 in
private theorem CRS_of_both_resetting_even
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n) (hRmax : n ≤ Rmax)
    {D : Config (AgentState n) Opinion n}
    (hS : InSswap D) (hM : MedianAnswerCorrect D)
    (hT : ∀ μ : Fin n, (D μ).1.rank.val + 1 = ceilHalf n → (D μ).1.timer = 0)
    (hpar : n % 2 = 0)
    {i j : Fin n} (hij : i ≠ j)
    (hir : (D.step (PEMProtocolCoupled n Rmax Emax Dmax hn0) i j i).1.role = .Resetting)
    (hjr : (D.step (PEMProtocolCoupled n Rmax Emax Dmax hn0) i j j).1.role = .Resetting) :
    CorrectResetSeed (D.step (PEMProtocolCoupled n Rmax Emax Dmax hn0) i j) := by
  classical
  set P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  have hsi := hS.toInSrank.allSettled i; have hsj := hS.toInSrank.allSettled j
  have hrij : (D i).1.rank ≠ (D j).1.rank := fun h => hij (hS.toInSrank.ranks_inj h)
  have hFix := rankDeltaOSSR_satisfies_fix (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn0)
  have hns := hS.swap_condition_false i j
  have hceil : ceilHalf n = n / 2 := by unfold ceilHalf; omega
  have hirr : (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0) (D i, D j)).1.role = .Resetting := by
    have hf := Config.step_fst_state P D hij
    rw [← show ∀ p, P.δ p = transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0) p from fun _ => rfl,
        ← congrArg AgentState.role hf]; exact hir
  -- Helper: contradiction from equal answers (propagate doesn't fire)
  have ans_eq_contra : ∀ {a₀ a₁ : AgentState n},
      a₀.role = .Settled → a₀.answer = a₁.answer →
      (phase4_propagate n Rmax a₀ a₁).1.role = .Resetting → False :=
    fun hs he hr => absurd (phase4_propagate_fst_settled_of_eq_answer (Rmax := Rmax) hs he) (by rw [hr]; exact Role.noConfusion)
  by_cases him : (D i).1.rank.val + 1 = ceilHalf n
  · -- i is ceilHalf median
    have hjnm : (D j).1.rank.val + 1 ≠ ceilHalf n :=
      fun h => hrij (Fin.ext (Nat.add_right_cancel (him.trans h.symm)))
    have hti := hT i him
    have hil : (D i).1.rank.val + 1 = n / 2 := by rw [← hceil]; exact him
    have hjnl : (D j).1.rank.val + 1 ≠ n / 2 := fun h => hrij (Fin.ext (Nat.add_right_cancel (hil.trans h.symm)))
    by_cases hju : (D j).1.rank.val + 1 = n / 2 + 1
    · -- j is upper-median → contradiction via equal answers after phase4_decide
      exfalso
      simp only [transitionPEM] at hirr
      rw [transitionPEM_prePhase4_eq_of_settled_distinct hFix hsi hsj hrij] at hirr
      unfold transitionPEM_phase4 at hirr; simp only [hsi, hsj, and_self, ite_true] at hirr
      unfold phase4_swap at hirr; simp only [hns, ite_false] at hirr
      -- phase4_decide produces equal answers → propagate stays Settled → contradiction
      have hd : phase4_decide n (D i).1 (D j).1 (D i).2 (D j).2 =
        if (D i).2 = (D j).2 then
          ({ (D i).1 with answer := opinionToAnswer (D i).2 },
           { (D j).1 with answer := opinionToAnswer (D i).2 })
        else
          ({ (D i).1 with answer := .outT }, { (D j).1 with answer := .outT }) := by
        simp only [phase4_decide, hpar, ite_true]
        simp [hil, show ↑(D j).1.rank = n / 2 from by omega]
      rw [hd] at hirr; split_ifs at hirr
      · exact absurd
          (phase4_propagate_fst_settled_of_eq_answer (Rmax := Rmax)
            (b₀ := { (D i).1 with answer := opinionToAnswer (D i).2 })
            (b₁ := { (D j).1 with answer := opinionToAnswer (D i).2 })
            hsi rfl)
          (by rw [hirr]; exact Role.noConfusion)
      · exact absurd
          (phase4_propagate_fst_settled_of_eq_answer (Rmax := Rmax)
            (b₀ := { (D i).1 with answer := .outT })
            (b₁ := { (D j).1 with answer := .outT })
            hsi rfl)
          (by rw [hirr]; exact Role.noConfusion)
    · -- j NOT upper-median → answers must differ → use trace lemma
      have hdiff : (D i).1.answer ≠ (D j).1.answer := by
        by_contra heq
        simp only [transitionPEM] at hirr
        rw [transitionPEM_prePhase4_eq_of_settled_distinct hFix hsi hsj hrij] at hirr
        unfold transitionPEM_phase4 at hirr; simp only [hsi, hsj, and_self, ite_true] at hirr
        unfold phase4_swap at hirr; simp only [hns, ite_false] at hirr
        unfold phase4_decide at hirr; simp only [hpar, ite_true, hil, hju] at hirr
        -- After resolve: neither lower+upper nor upper+lower pair → identity
        have hjnl2 : ¬ ((D j).1.rank.val + 1 = n / 2) := by omega
        simp only [hjnl2, ite_false] at hirr
        have heq_pos : (D i).1.answer = (D j).1.answer := by tauto
        exact ans_eq_contra hsi heq_pos hirr
      exact CRS_from_even_trace hn0 hRmax hS hM hij him
        (propagation_reset_fires_even_lower_timer_zero_no_swap_trace
          hFix hS.toInSrank hij hpar hil hjnl (fun h => hju (by omega)) hti hns hdiff)
        (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
  · by_cases hjm : (D j).1.rank.val + 1 = ceilHalf n
    · -- j is ceilHalf median (snd position)
      have hinm : (D i).1.rank.val + 1 ≠ ceilHalf n := him
      have hjl : (D j).1.rank.val + 1 = n / 2 := by rw [← hceil]; exact hjm
      have hinl : (D i).1.rank.val + 1 ≠ n / 2 := by rw [← hceil]; exact hinm
      have htj := hT j hjm
      by_cases hiu : (D i).1.rank.val + 1 = n / 2 + 1
      · -- i at upper median → phase4_decide equalizes answers → propagate doesn't fire → contradiction
        exfalso
        simp only [transitionPEM] at hirr
        rw [transitionPEM_prePhase4_eq_of_settled_distinct hFix hsi hsj hrij] at hirr
        unfold transitionPEM_phase4 at hirr; simp only [hsi, hsj, and_self, ite_true] at hirr
        unfold phase4_swap at hirr; simp only [hns, ite_false] at hirr
        unfold phase4_decide at hirr
        have hm : (D j).1.rank.val + 1 = n / 2 ∧ (D i).1.rank.val + 1 = n / 2 + 1 := ⟨hjl, hiu⟩
        simp only [hpar, ite_true, hinl, ite_false, hm, ite_true] at hirr
        exact ans_eq_contra (by simp [phase4_decide, hpar]; split_ifs <;> simp_all) (by simp [phase4_decide, hpar]; split_ifs <;> simp_all) hirr
      · -- i NOT at upper → use responder-median trace lemma
        have hdiff : (D j).1.answer ≠ (D i).1.answer := by
          by_contra heq
          -- Neither median pair condition matches → phase4_decide is identity
          have h_not_dec1 : ¬((D i).1.rank.val + 1 = n / 2 ∧ (D j).1.rank.val + 1 = n / 2 + 1) :=
            fun ⟨ha, _⟩ => hinl ha
          have h_not_dec2 : ¬((D j).1.rank.val + 1 = n / 2 ∧ (D i).1.rank.val + 1 = n / 2 + 1) :=
            fun ⟨_, hb⟩ => hiu hb
          simp only [transitionPEM] at hirr
          rw [transitionPEM_prePhase4_eq_of_settled_distinct hFix hsi hsj hrij] at hirr
          unfold transitionPEM_phase4 at hirr; simp only [hsi, hsj, and_self, ite_true] at hirr
          unfold phase4_swap at hirr; simp only [hns, ite_false] at hirr
          have hd : phase4_decide n (D i).1 (D j).1 (D i).2 (D j).2 = ((D i).1, (D j).1) := by
            simp only [phase4_decide, hpar, ite_true]
            have h_nd1 : ¬(↑(D i).1.rank + 1 = n / 2 ∧ ↑(D j).1.rank = n / 2) :=
              fun ⟨ha, _⟩ => h_not_dec1 ⟨ha, by omega⟩
            have h_nd2 : ¬(↑(D j).1.rank + 1 = n / 2 ∧ ↑(D i).1.rank = n / 2) :=
              fun ⟨ha, hb⟩ => h_not_dec2 ⟨ha, by omega⟩
            simp [h_nd1, h_nd2]
          rw [hd] at hirr; simp only [Prod.fst, Prod.snd] at hirr
          exact ans_eq_contra hsi heq.symm hirr
        have htr := propagation_reset_fires_even_no_swap_responder_median_trace (trank := Rmax) (Rmax := Rmax)
          hFix hS.toInSrank hij hpar hjl hinl hiu htj hns hdiff
        -- Construct CRS from trace
        have hf := Config.step_fst_state P D hij
        have hs := Config.step_snd_state P D hij (Ne.symm hij)
        have hmaj : majorityAnswer (D.step P i j) = majorityAnswer D := by
          simpa [P, PEMProtocolCoupled, PEMProtocol] using
            majorityAnswer_step_eq (trank := Rmax) (Rmax := Rmax)
              (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0) D i j
        have hcor : (D j).1.answer = majorityAnswer D := hM j hjm
        have hsi_out : (D.step P i j i).1 =
            { (D i).1 with role := .Resetting, leader := .L, resetcount := Rmax,
                           answer := (D j).1.answer } := by
          rw [hf]; show (transitionPEM _ _ _ _ _).1 = _; rw [htr]
        have hsj_out : (D.step P i j j).1 =
            { (D j).1 with role := .Resetting, leader := .L, resetcount := Rmax } := by
          rw [hs]; show (transitionPEM _ _ _ _ _).2 = _; rw [htr]
        have hoth : ∀ w, w ≠ i → w ≠ j → (D.step P i j w) = D w := by
          intro w hw hwv; unfold Config.step; simp [hij, hw, hwv]
        have hnrc : nonResettingCount (D.step P i j) ≤ n - 2 := by
          unfold nonResettingCount
          set S := Finset.univ.filter (fun w : Fin n => (D.step P i j w).1.role ≠ .Resetting)
          have hi_not : i ∉ S := by
            simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_not]; rw [hsi_out]
          have hj_not : j ∉ S := by
            simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_not]; rw [hsj_out]
          have hS_sub : S ⊆ Finset.univ \ {i, j} := by
            intro w hw; simp only [Finset.mem_sdiff, Finset.mem_univ, true_and,
              Finset.mem_insert, Finset.mem_singleton, not_or]
            exact ⟨fun h => hi_not (h ▸ hw), fun h => hj_not (h ▸ hw)⟩
          calc S.card ≤ (Finset.univ \ ({i, j} : Finset (Fin n))).card := Finset.card_le_card hS_sub
            _ = n - 2 := by rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),
                              Finset.card_univ, Fintype.card_fin, Finset.card_pair hij]
        refine ⟨⟨j, ?_, ?_, ?_, ?_⟩, ?_⟩
        · rw [hsj_out]
        · rw [hsj_out]; simp; exact lt_of_le_of_lt hnrc (lt_of_lt_of_le (by omega) hRmax)
        · rw [hsj_out]
        · rw [hsj_out, hmaj]; simp [hcor]
        · intro w hw_res
          by_cases hwi : w = i
          · subst hwi; rw [hsi_out] at hw_res ⊢
            exact ⟨by simp; omega, by simp [hmaj, hcor]⟩
          · by_cases hwj : w = j
            · subst hwj; rw [hsj_out] at hw_res ⊢
              exact ⟨by simp; omega, by simp [hmaj, hcor]⟩
            · exfalso; rw [show (D.step P i j w).1 = (D w).1 from
                congrArg Prod.fst (hoth w hwi hwj)] at hw_res
              rw [hS.allSettled w] at hw_res; exact Role.noConfusion hw_res
    · -- Neither is median → contradiction
      exfalso
      -- Neither agent is ceilHalf → phase4_propagate is identity → stays Settled
      simp only [transitionPEM] at hirr
      rw [transitionPEM_prePhase4_eq_of_settled_distinct hFix hsi hsj hrij] at hirr
      unfold transitionPEM_phase4 at hirr; simp only [hsi, hsj, and_self, ite_true] at hirr
      -- After swap+decide, neither has ceilHalf rank → propagate is identity
      have hsw₀ : (phase4_swap (D i).1 (D j).1 (D i).2 (D j).2).1.role = .Settled := by
        unfold phase4_swap; split_ifs <;> assumption
      have hdr₀ : (phase4_decide n (phase4_swap (D i).1 (D j).1 (D i).2 (D j).2).1
          (phase4_swap (D i).1 (D j).1 (D i).2 (D j).2).2 (D i).2 (D j).2).1.role = .Settled := by
        simp only [phase4_decide]; split_ifs <;> simp_all
      have hswR₀ : (phase4_swap (D i).1 (D j).1 (D i).2 (D j).2).1.rank = (D i).1.rank ∨
          (phase4_swap (D i).1 (D j).1 (D i).2 (D j).2).1.rank = (D j).1.rank := by
        unfold phase4_swap; split_ifs <;> simp
      have hswR₁ : (phase4_swap (D i).1 (D j).1 (D i).2 (D j).2).2.rank = (D j).1.rank ∨
          (phase4_swap (D i).1 (D j).1 (D i).2 (D j).2).2.rank = (D i).1.rank := by
        unfold phase4_swap; split_ifs <;> simp
      have hdR₀ : (phase4_decide n (phase4_swap (D i).1 (D j).1 (D i).2 (D j).2).1 (phase4_swap (D i).1 (D j).1 (D i).2 (D j).2).2 (D i).2 (D j).2).1.rank = (phase4_swap (D i).1 (D j).1 (D i).2 (D j).2).1.rank := by
        simp only [phase4_decide]; split_ifs <;> simp
      have hdR₁ : (phase4_decide n (phase4_swap (D i).1 (D j).1 (D i).2 (D j).2).1 (phase4_swap (D i).1 (D j).1 (D i).2 (D j).2).2 (D i).2 (D j).2).2.rank = (phase4_swap (D i).1 (D j).1 (D i).2 (D j).2).2.rank := by
        simp only [phase4_decide]; split_ifs <;> simp
      have hp₀ : ¬ ((phase4_decide n (phase4_swap (D i).1 (D j).1 (D i).2 (D j).2).1 (phase4_swap (D i).1 (D j).1 (D i).2 (D j).2).2 (D i).2 (D j).2).1.rank.val + 1 = ceilHalf n) := by
        rw [hdR₀]; rcases hswR₀ with h | h <;> rw [h] <;> assumption
      have hp₁ : ¬ ((phase4_decide n (phase4_swap (D i).1 (D j).1 (D i).2 (D j).2).1 (phase4_swap (D i).1 (D j).1 (D i).2 (D j).2).2 (D i).2 (D j).2).2.rank.val + 1 = ceilHalf n) := by
        rw [hdR₁]; rcases hswR₁ with h | h <;> rw [h] <;> assumption
      simp only [phase4_propagate, hp₀, ite_false, hp₁] at hirr
      rw [hdr₀] at hirr; exact Role.noConfusion hirr

/-! ### Main theorem -/

set_option maxRecDepth 65536 in
set_option maxHeartbeats 800000000 in
theorem step_InSswap_break_creates_CorrectResetSeed
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n) (hRmax : n ≤ Rmax)
    {D : Config (AgentState n) Opinion n}
    (hS : InSswap D) (hM : MedianAnswerCorrect D)
    (hT : ∀ μ : Fin n, (D μ).1.rank.val + 1 = ceilHalf n → (D μ).1.timer = 0)
    {i j : Fin n}
    (hS' : ¬ InSswap (D.step (PEMProtocolCoupled n Rmax Emax Dmax hn0) i j)) :
    CorrectResetSeed (D.step (PEMProtocolCoupled n Rmax Emax Dmax hn0) i j) := by
  by_cases hpar : n % 2 = 0
  · set P := PEMProtocolCoupled n Rmax Emax Dmax hn0
    by_cases hij : i = j
    · exfalso; apply hS'; subst hij; simp [Config.step]; exact hS
    have hsi := hS.toInSrank.allSettled i; have hsj := hS.toInSrank.allSettled j
    have hrij : (D i).1.rank ≠ (D j).1.rank := fun h => hij (hS.toInSrank.ranks_inj h)
    have hFix : RankDeltaSettledFix (rankDeltaOSSR Rmax Emax Dmax hn0) := rankDeltaOSSR_satisfies_fix
    have hPδ : ∀ p, P.δ p = transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0) p := fun _ => rfl
    have hf := Config.step_fst_state P D hij
    have hs := Config.step_snd_state P D hij (Ne.symm hij)
    have hR := transitionPEM_role_settled_or_resetting_of_InSswap
      (trank := Rmax) (Rmax := Rmax) (x₀ := (D i).2) (x₁ := (D j).2) hFix hsi hsj hrij
    have hri : (D.step P i j i).1.role = .Settled ∨ (D.step P i j i).1.role = .Resetting := by
      rw [congrArg AgentState.role hf, hPδ]; exact hR.1
    have hrj : (D.step P i j j).1.role = .Settled ∨ (D.step P i j j).1.role = .Resetting := by
      rw [congrArg AgentState.role hs, hPδ]; exact hR.2
    rcases hri with his | hir
    · rcases hrj with hjs | hjr
      · exfalso; apply hS'; exact InSswap_preserved_of_output_settled_even hn0 hS hij his hjs
      · exfalso
        have h2r : (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0) (D i, D j)).2.role = .Resetting := by
          rw [← hPδ, ← congrArg AgentState.role hs]; exact hjr
        have h1r := transitionPEM_snd_resetting_implies_fst_of_InSswap
          (trank := Rmax) (x₀ := (D i).2) (x₁ := (D j).2) hFix hsi hsj hrij h2r
        rw [show (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0) (D i, D j)).1.role = .Settled
          from by rw [← hPδ, ← congrArg AgentState.role hf]; exact his] at h1r
        exact Role.noConfusion h1r
    · have h1r : (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0) (D i, D j)).1.role = .Resetting := by
        rw [← hPδ, ← congrArg AgentState.role hf]; exact hir
      have h2r := transitionPEM_fst_resetting_implies_snd_of_InSswap
        (trank := Rmax) (x₀ := (D i).2) (x₁ := (D j).2) hFix hsi hsj hrij h1r
      have hjr : (D.step P i j j).1.role = .Resetting := by
        rw [congrArg AgentState.role hs, hPδ]; exact h2r
      exact CRS_of_both_resetting_even hn4 hn0 hRmax hS hM hT hpar hij hir hjr
  · exact step_InSswap_break_creates_CorrectResetSeed_odd hn4 hn0 hRmax hS hpar hS'

end SSEM
