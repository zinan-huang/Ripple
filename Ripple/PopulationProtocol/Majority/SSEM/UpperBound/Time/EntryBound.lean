import Ripple.PopulationProtocol.Majority.SSEM.UpperBound.Time.RecoveryBound

namespace SSEM

open scoped ENNReal

variable {n : ℕ}

theorem rcLevelPotential_eq_zero_of_awakening
    (C : Config (AgentState n) Opinion n)
    (hAwake : IsAwakeningConfig C) :
    rcLevelPotential C = 0 := by
  classical
  have hmax0 : maxRC C = 0 := by
    apply Nat.eq_zero_of_le_zero
    apply maxRC_le_of_all_le
    intro w hwR
    rcases hAwake with ⟨_hUnique, hLeaderOK, hFollowerOK⟩
    cases hwL : (C w).1.leader with
    | L =>
        have hwSettled := (hLeaderOK w hwL).1
        rw [hwR] at hwSettled
        cases hwSettled
    | F =>
        rcases hFollowerOK w hwL with hwUnsettled | hwReset
        · rw [hwR] at hwUnsettled
          cases hwUnsettled
        · exact Nat.le_of_eq hwReset.2
  unfold rcLevelPotential
  rw [if_pos hmax0]

theorem awakeningResettingFollowers_card_zero_of_fresh
    (C : Config (AgentState n) Opinion n)
    (hFresh : FreshRankingStart C) :
    (awakeningResettingFollowers C).card = 0 := by
  classical
  rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro w hw
  obtain ⟨root, hrootRole, _hrootRank, _hrootChildren, hothers⟩ := hFresh
  have hwR : (C w).1.role = .Resetting := (Finset.mem_filter.mp hw).2.2
  by_cases hwr : w = root
  · subst w
    rw [hrootRole] at hwR
    cases hwR
  · have hwUnsettled := hothers w hwr
    rw [hwUnsettled] at hwR
    cases hwR

theorem freshRankingStart_of_awakening_no_resetting_followers
    (C : Config (AgentState n) Opinion n)
    (hAwake : IsAwakeningConfig C)
    (hNoFollowers : (awakeningResettingFollowers C).card = 0) :
    FreshRankingStart C := by
  classical
  rcases hAwake with ⟨hUnique, hLeaderOK, hFollowerOK⟩
  obtain ⟨root, hrootL, hrootUnique⟩ := hUnique
  have hrootOK := hLeaderOK root hrootL
  refine ⟨root, hrootOK.1, hrootOK.2.1, hrootOK.2.2, ?_⟩
  intro w hwroot
  have hwF : (C w).1.leader = .F := by
    cases hwL : (C w).1.leader with
    | L =>
        exact False.elim (hwroot (hrootUnique w hwL))
    | F => rfl
  rcases hFollowerOK w hwF with hwUnsettled | hwReset
  · exact hwUnsettled
  · exfalso
    have hmem : w ∈ awakeningResettingFollowers C := by
      dsimp [awakeningResettingFollowers]
      simp [hwF, hwReset.1]
    have hpos : 0 < (awakeningResettingFollowers C).card :=
      Finset.card_pos.mpr ⟨w, hmem⟩
    omega

theorem freshRankingStart_iff_awakeningResettingFollowers_card_zero_of_awakening
    (C : Config (AgentState n) Opinion n)
    (hAwake : IsAwakeningConfig C) :
    FreshRankingStart C ↔ (awakeningResettingFollowers C).card = 0 := by
  constructor
  · exact awakeningResettingFollowers_card_zero_of_fresh C
  · exact freshRankingStart_of_awakening_no_resetting_followers C hAwake

theorem awakening_step_descent_of_resetting_follower
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n)
    (C : Config (AgentState n) Opinion n)
    (hAwake : IsAwakeningConfig C)
    {root w : Fin n}
    (hrootL : (C root).1.leader = .L)
    (hwBad : w ∈ awakeningResettingFollowers C) :
    root ≠ w ∧
      let P := PEMProtocolCoupled' n Rmax Emax Dmax hn
      let C' := C.step P root w
      IsAwakeningConfig C' ∧
        (awakeningResettingFollowers C').card <
          (awakeningResettingFollowers C).card := by
  classical
  rcases hAwake with ⟨hUnique, hLeaderOK, hFollowerOK⟩
  obtain ⟨root0, _hroot0L, hroot0Unique⟩ := hUnique
  have hrootUnique : ∀ y : Fin n, (C y).1.leader = .L → y = root := by
    intro y hyL
    exact (hroot0Unique y hyL).trans (hroot0Unique root hrootL).symm
  have hwF : (C w).1.leader = .F := (Finset.mem_filter.mp hwBad).2.1
  have hwR : (C w).1.role = .Resetting := (Finset.mem_filter.mp hwBad).2.2
  have hwRc : (C w).1.resetcount = 0 := by
    rcases hFollowerOK w hwF with hwUnsettled | hwReset
    · rw [hwUnsettled] at hwR
      cases hwR
    · exact hwReset.2
  have hrootNeW : root ≠ w := by
    intro hrw
    subst w
    rw [hrootL] at hwF
    cases hwF
  let P := PEMProtocolCoupled' n Rmax Emax Dmax hn
  let C' : Config (AgentState n) Opinion n := C.step P root w
  have hrootOK := hLeaderOK root hrootL
  have htrace := by
    simpa [P, PEMProtocolCoupled', C'] using
      (transitionPEM_settled_meets_dormant_trace
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 (C := C) (ℓ := root) (w := w) hrootNeW
        hrootOK.1 hrootOK.2.1 hrootOK.2.2 hrootL
        hwR hwRc hwF)
  have hOthers : ∀ x : Fin n, x ≠ root → x ≠ w → C' x = C x := by
    intro x hxroot hxw
    dsimp [C', P, PEMProtocolCoupled']
    simp [Config.step, hrootNeW, hxroot, hxw]
  have hAwake' : IsAwakeningConfig C' := by
    refine ⟨?_, ?_, ?_⟩
    · refine ⟨root, htrace.2.2.2.1, ?_⟩
      intro y hyL
      by_cases hyroot : y = root
      · exact hyroot
      · by_cases hyw : y = w
        · subst y
          rw [htrace.2.2.2.2.2] at hyL
          cases hyL
        · have hyOld : (C y).1.leader = .L := by
            have hyState := hOthers y hyroot hyw
            rw [hyState] at hyL
            exact hyL
          exact hrootUnique y hyOld
    · intro y hyL
      have hyroot : y = root := by
        by_cases hyroot : y = root
        · exact hyroot
        · by_cases hyw : y = w
          · subst y
            rw [htrace.2.2.2.2.2] at hyL
            cases hyL
          · have hyOld : (C y).1.leader = .L := by
              have hyState := hOthers y hyroot hyw
              rw [hyState] at hyL
              exact hyL
            exact hrootUnique y hyOld
      subst y
      exact ⟨htrace.1, htrace.2.1, htrace.2.2.1⟩
    · intro y hyF
      by_cases hyroot : y = root
      · subst y
        rw [htrace.2.2.2.1] at hyF
        cases hyF
      · by_cases hyw : y = w
        · subst y
          exact Or.inl htrace.2.2.2.2.1
        · have hyOldF : (C y).1.leader = .F := by
            have hyState := hOthers y hyroot hyw
            rw [hyState] at hyF
            exact hyF
          rw [hOthers y hyroot hyw]
          exact hFollowerOK y hyOldF
  have hsubset :
      awakeningResettingFollowers C' ⊆ (awakeningResettingFollowers C).erase w := by
    intro x hx
    have hxF : (C' x).1.leader = .F := (Finset.mem_filter.mp hx).2.1
    have hxR : (C' x).1.role = .Resetting := (Finset.mem_filter.mp hx).2.2
    have hxNeW : x ≠ w := by
      intro hxw
      subst x
      rw [htrace.2.2.2.2.1] at hxR
      cases hxR
    have hxNeRoot : x ≠ root := by
      intro hxroot
      subst x
      rw [htrace.1] at hxR
      cases hxR
    have hxOldState := hOthers x hxNeRoot hxNeW
    have hxOld : x ∈ awakeningResettingFollowers C := by
      dsimp [awakeningResettingFollowers]
      rw [hxOldState] at hxF hxR
      simp [hxF, hxR]
    exact Finset.mem_erase.mpr ⟨hxNeW, hxOld⟩
  have hcardLt : (awakeningResettingFollowers C').card <
      (awakeningResettingFollowers C).card := by
    have hle := Finset.card_le_card hsubset
    have herase : ((awakeningResettingFollowers C).erase w).card =
        (awakeningResettingFollowers C).card - 1 :=
      Finset.card_erase_of_mem hwBad
    have hposCard : 0 < (awakeningResettingFollowers C).card :=
      Finset.card_pos.mpr ⟨w, hwBad⟩
    rw [herase] at hle
    omega
  exact ⟨hrootNeW, hAwake', hcardLt⟩

theorem awakening_step_descent_witness
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n)
    (C : Config (AgentState n) Opinion n)
    (hAwake : IsAwakeningConfig C)
    (hpos : 0 < (awakeningResettingFollowers C).card) :
    ∃ root w : Fin n, root ≠ w ∧
      let P := PEMProtocolCoupled' n Rmax Emax Dmax hn
      let C' := C.step P root w
      IsAwakeningConfig C' ∧
        (awakeningResettingFollowers C').card <
          (awakeningResettingFollowers C).card := by
  classical
  obtain ⟨root, hrootL, _hrootUnique⟩ := hAwake.1
  obtain ⟨w, hwBad⟩ := Finset.card_pos.mp hpos
  have hdesc :=
    awakening_step_descent_of_resetting_follower
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 C hAwake (root := root) (w := w) hrootL hwBad
  exact ⟨root, w, hdesc.1, hdesc.2.1, hdesc.2.2⟩

theorem awakening_step_descent_prob
    [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n)
    (k : ℕ) (hk : 0 < k)
    (C : Config (AgentState n) Opinion n)
    (hAwake : IsAwakeningConfig C)
    (hcard : (awakeningResettingFollowers C).card = k) :
    (((n * (n - 1) : ℕ) : ENNReal)⁻¹) ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled' n Rmax Emax Dmax hn)
        (by omega : 2 ≤ n) C
        (fun D =>
          FreshRankingStart D ∨
            (IsAwakeningConfig D ∧
              (awakeningResettingFollowers D).card < k)) 1 := by
  classical
  let Goal : Config (AgentState n) Opinion n → Prop :=
    fun D =>
      FreshRankingStart D ∨
        (IsAwakeningConfig D ∧
          (awakeningResettingFollowers D).card < k)
  have hpos : 0 < (awakeningResettingFollowers C).card := by
    rw [hcard]
    exact hk
  obtain ⟨root, w, hrootNeW, hAwake', hlt⟩ :=
    awakening_step_descent_witness
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 C hAwake hpos
  have hstep : Goal (C.step (PEMProtocolCoupled' n Rmax Emax Dmax hn) root w) := by
    right
    exact ⟨hAwake', by simpa [hcard] using hlt⟩
  by_cases hGoal : Goal C
  · have hzero :
        Probability.ProbHitWithin
          (PEMProtocolCoupled' n Rmax Emax Dmax hn)
          (by omega : 2 ≤ n) C Goal 0 = 1 :=
      Probability.probHitBy_zero_of_goal
        (PEMProtocolCoupled' n Rmax Emax Dmax hn)
        (by omega : 2 ≤ n) C Goal hGoal
    calc
      (((n * (n - 1) : ℕ) : ENNReal)⁻¹) ≤ 1 := by
        exact ENNReal.inv_le_one.mpr (by
          have hn1 : 1 ≤ n := by omega
          have hpred1 : 1 ≤ n - 1 := by omega
          exact_mod_cast (Nat.mul_le_mul hn1 hpred1))
      _ = Probability.ProbHitWithin
            (PEMProtocolCoupled' n Rmax Emax Dmax hn)
            (by omega : 2 ≤ n) C Goal 0 := hzero.symm
      _ ≤ Probability.ProbHitWithin
            (PEMProtocolCoupled' n Rmax Emax Dmax hn)
            (by omega : 2 ≤ n) C Goal 1 :=
          Probability.ProbHitWithin_mono_time
            (PEMProtocolCoupled' n Rmax Emax Dmax hn)
            (by omega : 2 ≤ n) C Goal (by omega)
  · exact Probability.ProbHitWithin_one_lower_bound_of_step
      (PEMProtocolCoupled' n Rmax Emax Dmax hn)
      (by omega : 2 ≤ n) C Goal hGoal hrootNeW hstep

theorem awakening_step_descent_prob_sharp
    [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n)
    (k : ℕ) (hk : 0 < k)
    (C : Config (AgentState n) Opinion n)
    (hAwake : IsAwakeningConfig C)
    (hcard : (awakeningResettingFollowers C).card = k) :
    ((k : ENNReal) / ((n * (n - 1) : ℕ) : ENNReal)) ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled' n Rmax Emax Dmax hn)
        (by omega : 2 ≤ n) C
        (fun D =>
          FreshRankingStart D ∨
            (IsAwakeningConfig D ∧
              (awakeningResettingFollowers D).card < k) ∨
            ¬ IsAwakeningConfig D) 1 := by
  classical
  have _ : 0 < k := hk
  let P := PEMProtocolCoupled' n Rmax Emax Dmax hn
  let Goal : Config (AgentState n) Opinion n → Prop :=
    fun D =>
      FreshRankingStart D ∨
        (IsAwakeningConfig D ∧
          (awakeningResettingFollowers D).card < k) ∨
        ¬ IsAwakeningConfig D
  change ((k : ENNReal) / ((n * (n - 1) : ℕ) : ENNReal)) ≤
    Probability.ProbHitWithin P (by omega : 2 ≤ n) C Goal 1
  obtain ⟨root, hrootL, _hrootUnique⟩ := hAwake.1
  let S : Finset (Fin n × Fin n) :=
    (awakeningResettingFollowers C).image fun w => (root, w)
  have hS_card : S.card = k := by
    dsimp [S]
    rw [Finset.card_image_of_injective]
    · exact hcard
    · intro a b h
      exact congrArg Prod.snd h
  have hS_sub : S ⊆ Probability.OffDiagonalPairs n := by
    intro p hp
    dsimp [S] at hp
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hp
    have hdesc :=
      awakening_step_descent_of_resetting_follower
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 C hAwake (root := root) (w := w) hrootL hw
    exact (Probability.mem_offDiagonalPairs n (root, w)).mpr hdesc.1
  have hstep : ∀ p ∈ S, Goal (C.step P p.1 p.2) := by
    intro p hp
    dsimp [S] at hp
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hp
    have hdesc :=
      awakening_step_descent_of_resetting_follower
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 C hAwake (root := root) (w := w) hrootL hw
    right
    left
    exact ⟨by simpa [P] using hdesc.2.1,
      by simpa [P, hcard] using hdesc.2.2⟩
  have hmass :
      Probability.pairSetMass n (by omega : 2 ≤ n) S =
        (k : ENNReal) * ((n * (n - 1) : ℕ) : ENNReal)⁻¹ := by
    rw [Probability.pairSetMass_eq_card_mul_inv_of_subset
      n (by omega : 2 ≤ n) S hS_sub, hS_card]
  by_cases hGoal : Goal C
  · have hzero :
        Probability.ProbHitWithin P (by omega : 2 ≤ n) C Goal 0 = 1 :=
      Probability.probHitBy_zero_of_goal P (by omega : 2 ≤ n) C Goal hGoal
    have hmass_le_one :
        (k : ENNReal) * ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ≤ 1 := by
      calc
        (k : ENNReal) * ((n * (n - 1) : ℕ) : ENNReal)⁻¹
            = Probability.pairSetMass n (by omega : 2 ≤ n) S := hmass.symm
        _ ≤ Probability.pairSetMass n (by omega : 2 ≤ n)
              (Probability.OffDiagonalPairs n) :=
            Probability.pairSetMass_mono n (by omega : 2 ≤ n) hS_sub
        _ = 1 :=
            Probability.pairSetMass_offDiagonalPairs n (by omega : 2 ≤ n)
    calc
      ((k : ENNReal) / ((n * (n - 1) : ℕ) : ENNReal))
          = (k : ENNReal) * ((n * (n - 1) : ℕ) : ENNReal)⁻¹ := by
            rw [div_eq_mul_inv]
      _ ≤ 1 := hmass_le_one
      _ = Probability.ProbHitWithin P (by omega : 2 ≤ n) C Goal 0 := hzero.symm
      _ ≤ Probability.ProbHitWithin P (by omega : 2 ≤ n) C Goal 1 :=
          Probability.ProbHitWithin_mono_time P (by omega : 2 ≤ n) C Goal
            (by omega)
  · calc
      ((k : ENNReal) / ((n * (n - 1) : ℕ) : ENNReal))
          = (k : ENNReal) * ((n * (n - 1) : ℕ) : ENNReal)⁻¹ := by
            rw [div_eq_mul_inv]
      _ = Probability.pairSetMass n (by omega : 2 ≤ n) S := hmass.symm
      _ ≤ Probability.ProbHitWithin P (by omega : 2 ≤ n) C Goal 1 :=
          Probability.ProbHitWithin_one_lower_bound_of_pairSet
            P (by omega : 2 ≤ n) C Goal hGoal S hS_sub hstep

private theorem transitionPEM_resetting_leader_of_pre_both_settled
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    {s₀ s₁ : AgentState n} {x₀ x₁ : Opinion}
    (hpre₀ :
      (transitionPEM_prePhase4 n trank rankDelta s₀ s₁ x₀ x₁).1.role =
        .Settled)
    (hpre₁ :
      (transitionPEM_prePhase4 n trank rankDelta s₀ s₁ x₀ x₁).2.role =
        .Settled) :
    let r := transitionPEM n trank Rmax rankDelta ((s₀, x₀), (s₁, x₁))
    (r.1.role = .Resetting → r.1.leader = .L) ∧
      (r.2.role = .Resetting → r.2.leader = .L) := by
  classical
  have hphase :=
    phase4_resetting_leader
      (n := n) (Rmax := Rmax)
      (a := transitionPEM_prePhase4 n trank rankDelta s₀ s₁ x₀ x₁)
      (x₀ := x₀) (x₁ := x₁) hpre₀ hpre₁
  constructor
  · intro hR
    simpa [transitionPEM] using
      hphase.1 (by simpa [transitionPEM] using hR)
  · intro hR
    simpa [transitionPEM] using
      hphase.2 (by simpa [transitionPEM] using hR)

private theorem transitionPEM_recruit_ab_resetting_leader
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {s t : AgentState n} {x y : Opinion}
    (hs : s.role = .Settled) (ht : t.role = .Unsettled)
    (hchildren : s.children < 2)
    (hvalid : 2 * s.rank.val + s.children + 1 < n) :
    let r :=
      transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
        ((s, x), (t, y))
    (r.1.role = .Resetting → r.1.leader = .L) ∧
      (r.2.role = .Resetting → r.2.leader = .L) := by
  classical
  let rankDelta := rankDeltaOSSR Rmax Emax Dmax hn
  have hrd :=
    rankDeltaOSSR_recruits
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hs ht hchildren hvalid
  have hpre :=
    transitionPEM_prePhase4_structural
      (n := n) (trank := Rmax) (rankDelta := rankDelta)
      (s₀ := s) (s₁ := t) (x₀ := x) (x₁ := y)
  have hpre₀ :
      (transitionPEM_prePhase4 n Rmax rankDelta s t x y).1.role =
        .Settled := by
    rw [hpre.1]
    exact hrd.1
  have hpre₁ :
      (transitionPEM_prePhase4 n Rmax rankDelta s t x y).2.role =
        .Settled := by
    rw [hpre.2.2.2.2.2.2.1]
    exact hrd.2.2.2.1
  simpa [rankDelta] using
    transitionPEM_resetting_leader_of_pre_both_settled
      (n := n) (trank := Rmax) (Rmax := Rmax)
      (rankDelta := rankDelta) (s₀ := s) (s₁ := t)
      (x₀ := x) (x₁ := y) hpre₀ hpre₁

private theorem transitionPEM_recruit_ba_resetting_leader
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {s t : AgentState n} {x y : Opinion}
    (hs : s.role = .Unsettled) (ht : t.role = .Settled)
    (hchildren : t.children < 2)
    (hvalid : 2 * t.rank.val + t.children + 1 < n) :
    let r :=
      transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
        ((s, x), (t, y))
    (r.1.role = .Resetting → r.1.leader = .L) ∧
      (r.2.role = .Resetting → r.2.leader = .L) := by
  classical
  let rankDelta := rankDeltaOSSR Rmax Emax Dmax hn
  have hrd :=
    rankDeltaOSSR_recruit_ba
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hs ht hchildren hvalid
  have hpre :=
    transitionPEM_prePhase4_structural
      (n := n) (trank := Rmax) (rankDelta := rankDelta)
      (s₀ := s) (s₁ := t) (x₀ := x) (x₁ := y)
  have hpre₀ :
      (transitionPEM_prePhase4 n Rmax rankDelta s t x y).1.role =
        .Settled := by
    rw [hpre.1]
    change (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1.role = .Settled
    rw [hrd]
  have hpre₁ :
      (transitionPEM_prePhase4 n Rmax rankDelta s t x y).2.role =
        .Settled := by
    rw [hpre.2.2.2.2.2.2.1]
    change (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).2.role = .Settled
    rw [hrd]
    exact ht
  simpa [rankDelta] using
    transitionPEM_resetting_leader_of_pre_both_settled
      (n := n) (trank := Rmax) (Rmax := Rmax)
      (rankDelta := rankDelta) (s₀ := s) (s₁ := t)
      (x₀ := x) (x₁ := y) hpre₀ hpre₁

private theorem transitionPEM_unsettled_left_resetting_leader_of_partner_not_resetting
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {s t : AgentState n} {x y : Opinion}
    (hs : s.role = .Unsettled) (ht : t.role ≠ .Resetting) :
    let r :=
      transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
        ((s, x), (t, y))
    (r.1.role = .Resetting → r.1.leader = .L) ∧
      (r.2.role = .Resetting → r.2.leader = .L) := by
  classical
  let rankDelta := rankDeltaOSSR Rmax Emax Dmax hn
  let p := transitionPEM_prePhase4 n Rmax rankDelta s t x y
  have hrd_leader :=
    rankDeltaOSSR_unsettled_no_resetting_reset_leader
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      (s := s) (t := t) hs ht
  have hpre :=
    transitionPEM_prePhase4_structural
      (n := n) (trank := Rmax) (rankDelta := rankDelta)
      (s₀ := s) (s₁ := t) (x₀ := x) (x₁ := y)
  by_cases hboth :
      (rankDelta (s, t)).1.role = .Settled ∧
      (rankDelta (s, t)).2.role = .Settled
  · have hp₁ : p.1.role = .Settled := by
      simpa [p] using hpre.1.trans hboth.1
    have hp₂ : p.2.role = .Settled := by
      simpa [p] using hpre.2.2.2.2.2.2.1.trans hboth.2
    have hphase :=
      phase4_resetting_leader
        (n := n) (Rmax := Rmax) (a := p) (x₀ := x) (x₁ := y) hp₁ hp₂
    simpa [transitionPEM, rankDelta, p] using hphase
  · have hpass :=
      transitionPEM_structural_passthrough
        (n := n) (trank := Rmax) (Rmax := Rmax)
        (rankDelta := rankDelta)
        (s₀ := s) (s₁ := t) (x₀ := x) (x₁ := y) hboth
    dsimp [rankDelta] at hrd_leader
    rcases hpass with
      ⟨hrole₁, hleader₁, _, _, _, _, hrole₂, hleader₂, _, _, _, _, _, _⟩
    refine ⟨?_, ?_⟩
    · intro hreset
      rw [hleader₁]
      exact hrd_leader.1 (by
        rw [← hrole₁]
        exact hreset)
    · intro hreset
      rw [hleader₂]
      exact hrd_leader.2 (by
        rw [← hrole₂]
        exact hreset)

set_option maxHeartbeats 200000000 in
private theorem awakening_endpoint_resetting_follower_old_of_step
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (C : Config (AgentState n) Opinion n)
    (hAwake : IsAwakeningConfig C)
    {i j x : Fin n}
    (hx : x = i ∨ x = j)
    (hxF :
      (C.step (PEMProtocolCoupled' n Rmax Emax Dmax hn) i j x).1.leader = .F)
    (hxR :
      (C.step (PEMProtocolCoupled' n Rmax Emax Dmax hn) i j x).1.role = .Resetting) :
    (C x).1.leader = .F ∧ (C x).1.role = .Resetting := by
  classical
  by_cases hij : i = j
  · subst j
    have hxstate :
        C.step (PEMProtocolCoupled' n Rmax Emax Dmax hn) i i x = C x := by
      simp [Config.step]
    rw [hxstate] at hxF hxR
    exact ⟨hxF, hxR⟩
  · rcases hAwake with ⟨hUnique, hLeaderOK, hFollowerOK⟩
    obtain ⟨root, _hrootL, hrootUnique⟩ := hUnique
    let P := PEMProtocolCoupled' n Rmax Emax Dmax hn
    have hn_gt1 : 1 < n := by
      by_contra hlt
      have hnle : n ≤ 1 := by omega
      have hi0 : (i : ℕ) = 0 := by omega
      have hj0 : (j : ℕ) = 0 := by omega
      exact hij (Fin.ext (by rw [hi0, hj0]))
    rcases hx with hxi | hxj
    · subst x
      have hfst := Config.step_fst_state P C hij
      rw [hfst] at hxF hxR
      have hiLocal :
          ((P.δ (C i, C j)).1.leader = .F ∧
              (P.δ (C i, C j)).1.role = .Resetting) →
            (C i).1.leader = .F ∧ (C i).1.role = .Resetting := by
        intro hnew
        rcases hnew with ⟨hnewF, hnewR⟩
        cases hiLeader : (C i).1.leader with
        | L =>
            have hiOK := hLeaderOK i hiLeader
            cases hjLeader : (C j).1.leader with
            | L =>
                have hiRoot : i = root := hrootUnique i hiLeader
                have hjRoot : j = root := hrootUnique j hjLeader
                have hij' : i = j := hiRoot.trans hjRoot.symm
                exact False.elim (hij hij')
            | F =>
                rcases hFollowerOK j hjLeader with hjUn | hjReset
                · have hlocal :
                      ¬ ((P.δ (C i, C j)).1.leader = .F ∧
                          (P.δ (C i, C j)).1.role = .Resetting) := by
                    intro hbad
                    have hchildren : (C i).1.children < 2 := by
                      rw [hiOK.2.2]
                      omega
                    have hvalid :
                        2 * (C i).1.rank.val + (C i).1.children + 1 < n := by
                      rw [hiOK.2.1, hiOK.2.2]
                      omega
                    have hlead :=
                      (transitionPEM_recruit_ab_resetting_leader
                        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
                        (hn := hn) (s := (C i).1) (t := (C j).1)
                        (x := (C i).2) (y := (C j).2)
                        hiOK.1 hjUn hchildren hvalid).1 hbad.2
                    change (P.δ (C i, C j)).1.leader = .L at hlead
                    rw [hbad.1] at hlead
                    cases hlead
                  exact False.elim (hlocal ⟨hnewF, hnewR⟩)
                · have hlocal :
                      ¬ ((P.δ (C i, C j)).1.leader = .F ∧
                          (P.δ (C i, C j)).1.role = .Resetting) := by
                    dsimp [P, PEMProtocolCoupled', protocolPEM, transitionPEM,
                      transitionPEM_prePhase4, transitionPEM_phase4, phase4_swap,
                      phase4_decide, phase4_propagate, rankDeltaOSSR, propagateReset,
                      processAgent, resetOSSR]
                    simp [hiOK.1, hiOK.2.1, hiLeader, hjLeader,
                      hjReset.1, hjReset.2]
                  exact False.elim (hlocal ⟨hnewF, hnewR⟩)
        | F =>
            rcases hFollowerOK i hiLeader with hiUn | hiReset
            · cases hjLeader : (C j).1.leader with
              | L =>
                  have hjOK := hLeaderOK j hjLeader
                  have hlocal :
                      ¬ ((P.δ (C i, C j)).1.leader = .F ∧
                          (P.δ (C i, C j)).1.role = .Resetting) := by
                    intro hbad
                    have hchildren : (C j).1.children < 2 := by
                      rw [hjOK.2.2]
                      omega
                    have hvalid :
                        2 * (C j).1.rank.val + (C j).1.children + 1 < n := by
                      rw [hjOK.2.1, hjOK.2.2]
                      omega
                    have hlead :=
                      (transitionPEM_recruit_ba_resetting_leader
                        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
                        (hn := hn) (s := (C i).1) (t := (C j).1)
                        (x := (C i).2) (y := (C j).2)
                        hiUn hjOK.1 hchildren hvalid).1 hbad.2
                    change (P.δ (C i, C j)).1.leader = .L at hlead
                    rw [hbad.1] at hlead
                    cases hlead
                  exact False.elim (hlocal ⟨hnewF, hnewR⟩)
              | F =>
                  rcases hFollowerOK j hjLeader with hjUn | hjReset
                  · have hlocal :
                        ¬ ((P.δ (C i, C j)).1.leader = .F ∧
                            (P.δ (C i, C j)).1.role = .Resetting) := by
                      intro hbad
                      have hjNotReset : (C j).1.role ≠ .Resetting := by
                        rw [hjUn]
                        decide
                      have hlead :=
                        (transitionPEM_unsettled_left_resetting_leader_of_partner_not_resetting
                          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
                          (hn := hn) (s := (C i).1) (t := (C j).1)
                          (x := (C i).2) (y := (C j).2)
                          hiUn hjNotReset).1 hbad.2
                      change (P.δ (C i, C j)).1.leader = .L at hlead
                      rw [hbad.1] at hlead
                      cases hlead
                    exact False.elim (hlocal ⟨hnewF, hnewR⟩)
                  · have hlocal :
                        ¬ ((P.δ (C i, C j)).1.leader = .F ∧
                            (P.δ (C i, C j)).1.role = .Resetting) := by
                      dsimp [P, PEMProtocolCoupled', protocolPEM, transitionPEM,
                        transitionPEM_prePhase4, transitionPEM_phase4, phase4_swap,
                        phase4_decide, phase4_propagate, rankDeltaOSSR, propagateReset,
                        processAgent, resetOSSR]
                      simp [hiLeader, hiUn, hjLeader, hjReset.1, hjReset.2]
                    exact False.elim (hlocal ⟨hnewF, hnewR⟩)
            · exact ⟨rfl, hiReset.1⟩
      exact hiLocal ⟨hxF, hxR⟩
    · subst x
      have hsnd := Config.step_snd_state P C hij (fun hji => hij hji.symm)
      rw [hsnd] at hxF hxR
      have hjLocal :
          ((P.δ (C i, C j)).2.leader = .F ∧
              (P.δ (C i, C j)).2.role = .Resetting) →
            (C j).1.leader = .F ∧ (C j).1.role = .Resetting := by
        intro hnew
        rcases hnew with ⟨hnewF, hnewR⟩
        cases hjLeader : (C j).1.leader with
        | L =>
            have hjOK := hLeaderOK j hjLeader
            cases hiLeader : (C i).1.leader with
            | L =>
                have hiRoot : i = root := hrootUnique i hiLeader
                have hjRoot : j = root := hrootUnique j hjLeader
                have hij' : i = j := hiRoot.trans hjRoot.symm
                exact False.elim (hij hij')
            | F =>
                rcases hFollowerOK i hiLeader with hiUn | hiReset
                · have hlocal :
                      ¬ ((P.δ (C i, C j)).2.leader = .F ∧
                          (P.δ (C i, C j)).2.role = .Resetting) := by
                    intro hbad
                    have hchildren : (C j).1.children < 2 := by
                      rw [hjOK.2.2]
                      omega
                    have hvalid :
                        2 * (C j).1.rank.val + (C j).1.children + 1 < n := by
                      rw [hjOK.2.1, hjOK.2.2]
                      omega
                    have hlead :=
                      (transitionPEM_recruit_ba_resetting_leader
                        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
                        (hn := hn) (s := (C i).1) (t := (C j).1)
                        (x := (C i).2) (y := (C j).2)
                        hiUn hjOK.1 hchildren hvalid).2 hbad.2
                    change (P.δ (C i, C j)).2.leader = .L at hlead
                    rw [hbad.1] at hlead
                    cases hlead
                  exact False.elim (hlocal ⟨hnewF, hnewR⟩)
                · have hlocal :
                      ¬ ((P.δ (C i, C j)).2.leader = .F ∧
                          (P.δ (C i, C j)).2.role = .Resetting) := by
                    dsimp [P, PEMProtocolCoupled', protocolPEM, transitionPEM,
                      transitionPEM_prePhase4, transitionPEM_phase4, phase4_swap,
                      phase4_decide, phase4_propagate, rankDeltaOSSR, propagateReset,
                      processAgent, resetOSSR]
                    simp [hiLeader, hiReset.1, hiReset.2, hjOK.1,
                      hjOK.2.1, hjLeader]
                  exact False.elim (hlocal ⟨hnewF, hnewR⟩)
        | F =>
            rcases hFollowerOK j hjLeader with hjUn | hjReset
            · cases hiLeader : (C i).1.leader with
              | L =>
                  have hiOK := hLeaderOK i hiLeader
                  have hlocal :
                      ¬ ((P.δ (C i, C j)).2.leader = .F ∧
                          (P.δ (C i, C j)).2.role = .Resetting) := by
                    intro hbad
                    have hchildren : (C i).1.children < 2 := by
                      rw [hiOK.2.2]
                      omega
                    have hvalid :
                        2 * (C i).1.rank.val + (C i).1.children + 1 < n := by
                      rw [hiOK.2.1, hiOK.2.2]
                      omega
                    have hlead :=
                      (transitionPEM_recruit_ab_resetting_leader
                        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
                        (hn := hn) (s := (C i).1) (t := (C j).1)
                        (x := (C i).2) (y := (C j).2)
                        hiOK.1 hjUn hchildren hvalid).2 hbad.2
                    change (P.δ (C i, C j)).2.leader = .L at hlead
                    rw [hbad.1] at hlead
                    cases hlead
                  exact False.elim (hlocal ⟨hnewF, hnewR⟩)
                | F =>
                    rcases hFollowerOK i hiLeader with hiUn | hiReset
                    · have hlocal :
                          ¬ ((P.δ (C i, C j)).2.leader = .F ∧
                              (P.δ (C i, C j)).2.role = .Resetting) := by
                        intro hbad
                        have hjNotReset : (C j).1.role ≠ .Resetting := by
                          rw [hjUn]
                          decide
                        have hlead :=
                          (transitionPEM_unsettled_left_resetting_leader_of_partner_not_resetting
                            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
                            (hn := hn) (s := (C i).1) (t := (C j).1)
                            (x := (C i).2) (y := (C j).2)
                            hiUn hjNotReset).2 hbad.2
                        change (P.δ (C i, C j)).2.leader = .L at hlead
                        rw [hbad.1] at hlead
                        cases hlead
                      exact False.elim (hlocal ⟨hnewF, hnewR⟩)
                    · have hlocal :
                          ¬ ((P.δ (C i, C j)).2.leader = .F ∧
                              (P.δ (C i, C j)).2.role = .Resetting) := by
                        dsimp [P, PEMProtocolCoupled', protocolPEM, transitionPEM,
                          transitionPEM_prePhase4, transitionPEM_phase4, phase4_swap,
                          phase4_decide, phase4_propagate, rankDeltaOSSR, propagateReset,
                          processAgent, resetOSSR]
                        simp [hiLeader, hiReset.1, hiReset.2, hjLeader, hjUn]
                      exact False.elim (hlocal ⟨hnewF, hnewR⟩)
            · exact ⟨rfl, hjReset.1⟩
      exact hjLocal ⟨hxF, hxR⟩

private theorem awakeningResettingFollowers_subset_of_step
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (C : Config (AgentState n) Opinion n)
    (hAwake : IsAwakeningConfig C)
    (i j : Fin n) :
    awakeningResettingFollowers
        (C.step (PEMProtocolCoupled' n Rmax Emax Dmax hn) i j) ⊆
      awakeningResettingFollowers C := by
  classical
  intro x hx
  have hxF :
      (C.step (PEMProtocolCoupled' n Rmax Emax Dmax hn) i j x).1.leader = .F :=
    (Finset.mem_filter.mp hx).2.1
  have hxR :
      (C.step (PEMProtocolCoupled' n Rmax Emax Dmax hn) i j x).1.role = .Resetting :=
    (Finset.mem_filter.mp hx).2.2
  by_cases hxi : x = i
  · have hold :=
      awakening_endpoint_resetting_follower_old_of_step
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        C hAwake (i := i) (j := j) (x := x) (Or.inl hxi)
        hxF hxR
    dsimp [awakeningResettingFollowers]
    simp [hold.1, hold.2]
  · by_cases hxj : x = j
    · have hold :=
        awakening_endpoint_resetting_follower_old_of_step
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          C hAwake (i := i) (j := j) (x := x) (Or.inr hxj)
          hxF hxR
      dsimp [awakeningResettingFollowers]
      simp [hold.1, hold.2]
    · have hxstate :
          C.step (PEMProtocolCoupled' n Rmax Emax Dmax hn) i j x = C x := by
        by_cases hij : i = j
        · subst j
          simp [Config.step]
        · simp [Config.step, hij, hxi, hxj]
      dsimp [awakeningResettingFollowers]
      rw [hxstate] at hxF hxR
      simp [hxF, hxR]

theorem awakeningResettingFollowers_card_step_le_of_awakening
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (C : Config (AgentState n) Opinion n)
    (hAwake : IsAwakeningConfig C)
    (i j : Fin n) :
    (awakeningResettingFollowers
        (C.step (PEMProtocolCoupled' n Rmax Emax Dmax hn) i j)).card ≤
      (awakeningResettingFollowers C).card := by
  exact Finset.card_le_card
    (awakeningResettingFollowers_subset_of_step
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      C hAwake i j)

theorem awakening_to_goal_or_exit_expected_le
    [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (C : Config (AgentState n) Opinion n)
    (hAwake : IsAwakeningConfig C) :
    Probability.expectedHittingTime
      (PEMProtocolCoupled' n Rmax Emax Dmax hn) (by omega : 2 ≤ n) C
      (fun D =>
        FreshRankingStart D ∨
          (∃ k, 2 ≤ k ∧ HeapPrefix D k) ∨
          IsConsensusConfig D ∨
          ¬ IsAwakeningConfig D)
      ≤ (((awakeningResettingFollowers C).card * (n * (n - 1)) : ℕ) : ENNReal) := by
  classical
  let P := PEMProtocolCoupled' n Rmax Emax Dmax hn
  let Goal : Config (AgentState n) Opinion n → Prop :=
    fun D =>
      FreshRankingStart D ∨
        (∃ k, 2 ≤ k ∧ HeapPrefix D k) ∨
        IsConsensusConfig D ∨
        ¬ IsAwakeningConfig D
  let Inv : Config (AgentState n) Opinion n → Prop := IsAwakeningConfig
  let φ : Config (AgentState n) Opinion n → ℕ :=
    fun D => (awakeningResettingFollowers D).card
  let pRate : ℕ → ENNReal :=
    fun _ => (((n * (n - 1) : ℕ) : ENNReal)⁻¹)
  have hBound :=
    Probability.expectedHittingTime_le_of_variable_descent_until_goal
      P (by omega : 2 ≤ n) C Goal Inv φ pRate hAwake
      (by
        intro D hInvD hφ
        left
        exact
          (freshRankingStart_iff_awakeningResettingFollowers_card_zero_of_awakening
            D hInvD).2 hφ)
      (by
        intro D _hInvD _hNotGoal i j
        by_cases h :
            IsAwakeningConfig (D.step P i j)
        · exact Or.inl h
        · exact Or.inr (Or.inr (Or.inr (Or.inr h))))
      (by
        intro D hInvD hNotGoal i j
        simpa [P, φ] using
          awakeningResettingFollowers_card_step_le_of_awakening
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            D hInvD i j)
      (by
        intro k hk D hInvD hφ
        let SmallGoal : Config (AgentState n) Opinion n → Prop :=
          fun E =>
            FreshRankingStart E ∨
              (IsAwakeningConfig E ∧
                (awakeningResettingFollowers E).card < k)
        let BigGoal : Config (AgentState n) Opinion n → Prop :=
          fun E => Goal E ∨ (Inv E ∧ φ E < k)
        have hsmall :
            (((n * (n - 1) : ℕ) : ENNReal)⁻¹) ≤
              Probability.ProbHitWithin P (by omega : 2 ≤ n) D SmallGoal 1 := by
          simpa [P, SmallGoal] using
            awakening_step_descent_prob
              (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
              hn4 k hk D hInvD hφ
        have hmono : ∀ E : Config (AgentState n) Opinion n,
            SmallGoal E → BigGoal E := by
          intro E hE
          rcases hE with hFresh | hDesc
          · exact Or.inl (Or.inl hFresh)
          · exact Or.inr ⟨hDesc.1, by simpa [φ] using hDesc.2⟩
        have hprob :
            Probability.ProbHitWithin P (by omega : 2 ≤ n) D SmallGoal 1 ≤
              Probability.ProbHitWithin P (by omega : 2 ≤ n) D BigGoal 1 :=
          Probability.ProbHitWithin_mono_goal P (by omega : 2 ≤ n) D
            SmallGoal BigGoal hmono 1
        exact hsmall.trans (by simpa [BigGoal, Goal, Inv, φ] using hprob))
  calc
    Probability.expectedHittingTime P (by omega : 2 ≤ n) C Goal
        ≤ ∑ _k ∈ Finset.range (φ C), (pRate (_k + 1))⁻¹ := hBound
    _ = ∑ _k ∈ Finset.range (φ C),
          ((n * (n - 1) : ℕ) : ENNReal) := by
          apply Finset.sum_congr rfl
          intro k hk
          simp [pRate, inv_inv]
    _ = ((φ C : ℕ) : ENNReal) *
          ((n * (n - 1) : ℕ) : ENNReal) := by
          simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ = (((awakeningResettingFollowers C).card *
          (n * (n - 1)) : ℕ) : ENNReal) := by
          simp [φ]

theorem awakening_to_goal_or_exit_expected_le_sharp
    [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (C : Config (AgentState n) Opinion n)
    (hAwake : IsAwakeningConfig C) :
    Probability.expectedHittingTime
      (PEMProtocolCoupled' n Rmax Emax Dmax hn) (by omega : 2 ≤ n) C
      (fun D =>
        FreshRankingStart D ∨
          (∃ k, 2 ≤ k ∧ HeapPrefix D k) ∨
          IsConsensusConfig D ∨
          ¬ IsAwakeningConfig D)
      ≤ ∑ k ∈ Finset.range (awakeningResettingFollowers C).card,
          (((k + 1 : ℕ) : ENNReal) /
            ((n * (n - 1) : ℕ) : ENNReal))⁻¹ := by
  classical
  let P := PEMProtocolCoupled' n Rmax Emax Dmax hn
  let Goal : Config (AgentState n) Opinion n → Prop :=
    fun D =>
      FreshRankingStart D ∨
        (∃ k, 2 ≤ k ∧ HeapPrefix D k) ∨
        IsConsensusConfig D ∨
        ¬ IsAwakeningConfig D
  let Inv : Config (AgentState n) Opinion n → Prop := IsAwakeningConfig
  let φ : Config (AgentState n) Opinion n → ℕ :=
    fun D => (awakeningResettingFollowers D).card
  let pRate : ℕ → ENNReal :=
    fun k => (k : ENNReal) / ((n * (n - 1) : ℕ) : ENNReal)
  have hBound :=
    Probability.expectedHittingTime_le_of_variable_descent_until_goal
      P (by omega : 2 ≤ n) C Goal Inv φ pRate hAwake
      (by
        intro D hInvD hφ
        left
        exact
          (freshRankingStart_iff_awakeningResettingFollowers_card_zero_of_awakening
            D hInvD).2 hφ)
      (by
        intro D _hInvD _hNotGoal i j
        by_cases h :
            IsAwakeningConfig (D.step P i j)
        · exact Or.inl h
        · exact Or.inr (Or.inr (Or.inr (Or.inr h))))
      (by
        intro D hInvD hNotGoal i j
        simpa [P, φ] using
          awakeningResettingFollowers_card_step_le_of_awakening
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            D hInvD i j)
      (by
        intro k hk D hInvD hφ
        let SmallGoal : Config (AgentState n) Opinion n → Prop :=
          fun E =>
            FreshRankingStart E ∨
              (IsAwakeningConfig E ∧
                (awakeningResettingFollowers E).card < k) ∨
              ¬ IsAwakeningConfig E
        let BigGoal : Config (AgentState n) Opinion n → Prop :=
          fun E => Goal E ∨ (Inv E ∧ φ E < k)
        have hsmall :
            pRate k ≤
              Probability.ProbHitWithin P (by omega : 2 ≤ n) D SmallGoal 1 := by
          simpa [P, SmallGoal, pRate] using
            awakening_step_descent_prob_sharp
              (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
              hn4 k hk D hInvD hφ
        have hmono : ∀ E : Config (AgentState n) Opinion n,
            SmallGoal E → BigGoal E := by
          intro E hE
          rcases hE with hFresh | hRest
          · exact Or.inl (Or.inl hFresh)
          · rcases hRest with hDesc | hExit
            · exact Or.inr ⟨hDesc.1, by simpa [φ] using hDesc.2⟩
            · exact Or.inl (Or.inr (Or.inr (Or.inr hExit)))
        have hprob :
            Probability.ProbHitWithin P (by omega : 2 ≤ n) D SmallGoal 1 ≤
              Probability.ProbHitWithin P (by omega : 2 ≤ n) D BigGoal 1 :=
          Probability.ProbHitWithin_mono_goal P (by omega : 2 ≤ n) D
            SmallGoal BigGoal hmono 1
        exact hsmall.trans (by simpa [BigGoal, Goal, Inv, φ] using hprob))
  simpa [P, Goal, φ, pRate] using hBound

end SSEM
