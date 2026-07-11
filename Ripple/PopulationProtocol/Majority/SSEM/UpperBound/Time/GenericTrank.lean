import Ripple.PopulationProtocol.Majority.SSEM.UpperBound.Time
import Ripple.PopulationProtocol.Majority.SSEM.UpperBound.Time.TransitionLemmas
import Ripple.PopulationProtocol.Majority.SSEM.UpperBound.Time.DecisionTiming
import Ripple.PopulationProtocol.Majority.SSEM.UpperBound.Time.PhaseProofs
import Ripple.PopulationProtocol.Majority.SSEM.UpperBound.Time.PolynomialBound

/-!
# Generic `trank` time-window restatements

This file keeps the legacy `PEMProtocolCoupled` window stack intact and adds
generic-`trank` wrappers for the paper's constant-timer regime.
-/

namespace SSEM

open scoped ENNReal

attribute [local instance] Classical.propDecidable

section TimerPreservation

private def GenericAgentTimerBounded (K : ℕ) (s : AgentState n) : Prop :=
  s.timer ≤ K

private def GenericPairTimerBounded (K : ℕ) (p : AgentState n × AgentState n) : Prop :=
  GenericAgentTimerBounded K p.1 ∧ GenericAgentTimerBounded K p.2

private theorem generic_resetOSSR_preserves_timer_bound
    {n Emax K : ℕ} {hn : 0 < n} {s : AgentState n}
    (hs : GenericAgentTimerBounded K s) :
    GenericAgentTimerBounded K (resetOSSR Emax hn s) := by
  rcases s with ⟨role, rank, leader, resetcount, answer, timer, children,
    errorcount, delaytimer⟩
  cases leader <;> simpa [GenericAgentTimerBounded, resetOSSR] using hs

private theorem generic_processAgent_preserves_timer_bound
    {n Emax Dmax K : ℕ} {hn : 0 < n} {s : AgentState n}
    {oldRc : ℕ} {partnerResetting : Bool}
    (hs : GenericAgentTimerBounded K s) :
    GenericAgentTimerBounded K
      (processAgent Emax Dmax hn s oldRc partnerResetting) := by
  unfold processAgent
  by_cases hmain : s.role = .Resetting ∧ s.resetcount = 0
  · rw [if_pos hmain]
    by_cases hold : 0 < oldRc
    · rw [if_pos hold]
      by_cases hfire :
          ({s with delaytimer := Dmax} : AgentState n).delaytimer = 0 ∨
            !partnerResetting
      · rw [if_pos hfire]
        exact generic_resetOSSR_preserves_timer_bound (s := {s with delaytimer := Dmax}) hs
      · rw [if_neg hfire]
        exact hs
    · rw [if_neg hold]
      by_cases hfire :
          ({s with delaytimer := s.delaytimer - 1} : AgentState n).delaytimer = 0 ∨
            !partnerResetting
      · rw [if_pos hfire]
        exact generic_resetOSSR_preserves_timer_bound
          (s := {s with delaytimer := s.delaytimer - 1}) hs
      · rw [if_neg hfire]
        exact hs
  · rw [if_neg hmain]
    exact hs

private theorem generic_propagateReset_recruit_preserves_timer_bound
    {n Emax Dmax K : ℕ} {a b : AgentState n}
    (ha : GenericAgentTimerBounded K a) (hb : GenericAgentTimerBounded K b) :
    GenericPairTimerBounded K
      (if a.role = .Resetting ∧ 0 < a.resetcount ∧ b.role ≠ .Resetting then
        (a, { b with role := .Resetting, resetcount := 0, delaytimer := Dmax })
      else if b.role = .Resetting ∧ 0 < b.resetcount ∧ a.role ≠ .Resetting then
        ({ a with role := .Resetting, resetcount := 0, delaytimer := Dmax }, b)
      else (a, b)) := by
  unfold GenericPairTimerBounded
  split_ifs <;> simp_all [GenericAgentTimerBounded]

private theorem generic_propagateReset_sync_preserves_timer_bound
    {n K : ℕ} {a b : AgentState n}
    (ha : GenericAgentTimerBounded K a) (hb : GenericAgentTimerBounded K b) :
    GenericPairTimerBounded K
      (if a.role = .Resetting ∧ b.role = .Resetting then
        let newRc := max (a.resetcount - 1) (b.resetcount - 1)
        ({ a with resetcount := newRc }, { b with resetcount := newRc })
      else (a, b)) := by
  unfold GenericPairTimerBounded
  split_ifs <;> simp_all [GenericAgentTimerBounded]

private theorem generic_propagateReset_preserves_timer_bound
    {n Emax Dmax K : ℕ} {hn : 0 < n} {a b : AgentState n}
    (ha : GenericAgentTimerBounded K a) (hb : GenericAgentTimerBounded K b) :
    GenericAgentTimerBounded K (propagateReset Emax Dmax hn a b).1 ∧
    GenericAgentTimerBounded K (propagateReset Emax Dmax hn a b).2 := by
  unfold propagateReset
  let p₁ :=
    if a.role = .Resetting ∧ 0 < a.resetcount ∧ b.role ≠ .Resetting then
      (a, { b with role := .Resetting, resetcount := 0, delaytimer := Dmax })
    else if b.role = .Resetting ∧ 0 < b.resetcount ∧ a.role ≠ .Resetting then
      ({ a with role := .Resetting, resetcount := 0, delaytimer := Dmax }, b)
    else (a, b)
  have hp₁ : GenericPairTimerBounded K p₁ := by
    simpa [p₁] using
      generic_propagateReset_recruit_preserves_timer_bound
        (Emax := Emax) (Dmax := Dmax) ha hb
  let oldRcA := p₁.1.resetcount
  let oldRcB := p₁.2.resetcount
  let p₂ :=
    if p₁.1.role = .Resetting ∧ p₁.2.role = .Resetting then
      let newRc := max (p₁.1.resetcount - 1) (p₁.2.resetcount - 1)
      ({ p₁.1 with resetcount := newRc }, { p₁.2 with resetcount := newRc })
    else p₁
  have hp₂ : GenericPairTimerBounded K p₂ := by
    exact generic_propagateReset_sync_preserves_timer_bound hp₁.1 hp₁.2
  simpa [p₁, oldRcA, oldRcB, p₂, GenericPairTimerBounded] using
    And.intro
      (generic_processAgent_preserves_timer_bound
        (Emax := Emax) (Dmax := Dmax) (hn := hn) hp₂.1)
      (generic_processAgent_preserves_timer_bound
        (Emax := Emax) (Dmax := Dmax) (hn := hn) hp₂.2)

set_option maxHeartbeats 800000 in
private theorem generic_rankDeltaOSSR_preserves_timer_bound
    {n Rmax Emax Dmax K : ℕ} {hn : 0 < n} {a b : AgentState n}
    (ha : GenericAgentTimerBounded K a) (hb : GenericAgentTimerBounded K b) :
    GenericAgentTimerBounded K (rankDeltaOSSR Rmax Emax Dmax hn (a, b)).1 ∧
    GenericAgentTimerBounded K (rankDeltaOSSR Rmax Emax Dmax hn (a, b)).2 := by
  unfold rankDeltaOSSR
  by_cases hReset : a.role = .Resetting ∨ b.role = .Resetting
  · simp [hReset]
    have hpr :=
      generic_propagateReset_preserves_timer_bound
        (Emax := Emax) (Dmax := Dmax) (hn := hn) ha hb
    split_ifs <;> simp_all [GenericAgentTimerBounded]
  · simp [hReset]
    repeat' split_ifs <;> simp_all [GenericAgentTimerBounded]

set_option maxHeartbeats 800000 in
private theorem generic_transitionPEM_prePhase4_preserves_timer_bound
    {n trank K : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    {s₀ s₁ : AgentState n} {x₀ x₁ : Opinion}
    (hK : 7 * (trank + 4) ≤ K)
    (hRankDelta :
      GenericAgentTimerBounded K (rankDelta (s₀, s₁)).1 ∧
      GenericAgentTimerBounded K (rankDelta (s₀, s₁)).2) :
    GenericAgentTimerBounded K
        (transitionPEM_prePhase4 n trank rankDelta s₀ s₁ x₀ x₁).1 ∧
      GenericAgentTimerBounded K
        (transitionPEM_prePhase4 n trank rankDelta s₀ s₁ x₀ x₁).2 := by
  unfold transitionPEM_prePhase4
  rcases hrd : rankDelta (s₀, s₁) with ⟨r₀, r₁⟩
  simp [hrd] at hRankDelta ⊢
  repeat' split_ifs <;> simp_all [GenericAgentTimerBounded] <;> omega

private theorem generic_phase4_swap_preserves_timer_bound
    {n K : ℕ} {a b : AgentState n} {x₀ x₁ : Opinion}
    (ha : GenericAgentTimerBounded K a) (hb : GenericAgentTimerBounded K b) :
    GenericAgentTimerBounded K (phase4_swap a b x₀ x₁).1 ∧
    GenericAgentTimerBounded K (phase4_swap a b x₀ x₁).2 := by
  unfold phase4_swap
  split_ifs <;> simp_all [GenericAgentTimerBounded]

private theorem generic_phase4_decide_preserves_timer_bound
    {n K : ℕ} {a b : AgentState n} {x₀ x₁ : Opinion}
    (ha : GenericAgentTimerBounded K a) (hb : GenericAgentTimerBounded K b) :
    GenericAgentTimerBounded K (phase4_decide n a b x₀ x₁).1 ∧
    GenericAgentTimerBounded K (phase4_decide n a b x₀ x₁).2 := by
  unfold phase4_decide
  repeat' split_ifs <;> simp_all [GenericAgentTimerBounded]

set_option maxHeartbeats 800000 in
private theorem generic_phase4_propagate_preserves_timer_bound
    {n Rmax K : ℕ} {a b : AgentState n}
    (ha : GenericAgentTimerBounded K a) (hb : GenericAgentTimerBounded K b) :
    GenericAgentTimerBounded K (phase4_propagate n Rmax a b).1 ∧
    GenericAgentTimerBounded K (phase4_propagate n Rmax a b).2 := by
  unfold phase4_propagate
  by_cases haMed : a.rank.val + 1 = ceilHalf n
  · by_cases hbLast : b.rank.val + 1 = n
    · by_cases hReset :
        ({ a with timer := a.timer - 1 } : AgentState n).timer = 0 ∧
          ({ a with timer := a.timer - 1 } : AgentState n).answer ≠ b.answer
      · simp [haMed, hbLast, hReset, GenericAgentTimerBounded] at * <;> omega
      · simp [haMed, hbLast, hReset, GenericAgentTimerBounded] at * <;> omega
    · by_cases hReset : a.timer = 0 ∧ a.answer ≠ b.answer
      · simp [haMed, hbLast, hReset, GenericAgentTimerBounded] at * <;> omega
      · simp [haMed, hbLast, hReset, GenericAgentTimerBounded] at * <;> omega
  · by_cases hbMed : b.rank.val + 1 = ceilHalf n
    · by_cases haLast : a.rank.val + 1 = n
      · by_cases hReset :
          ({ b with timer := b.timer - 1 } : AgentState n).timer = 0 ∧
            ({ b with timer := b.timer - 1 } : AgentState n).answer ≠ a.answer
        · have hn_ne_ceil : n ≠ ceilHalf n := by
            intro h
            exact haMed (by omega)
          simp [hn_ne_ceil, hbMed, haLast, hReset, GenericAgentTimerBounded] at * <;>
            omega
        · have hn_ne_ceil : n ≠ ceilHalf n := by
            intro h
            exact haMed (by omega)
          simp [hn_ne_ceil, hbMed, haLast, hReset, GenericAgentTimerBounded] at * <;>
            omega
      · by_cases hReset : b.timer = 0 ∧ b.answer ≠ a.answer
        · simp [haMed, hbMed, haLast, hReset, GenericAgentTimerBounded] at * <;> omega
        · simp [haMed, hbMed, haLast, hReset, GenericAgentTimerBounded] at * <;> omega
    · simp [haMed, hbMed, GenericAgentTimerBounded] at * <;> omega

private theorem generic_transitionPEM_phase4_preserves_timer_bound
    {n Rmax K : ℕ} {a : AgentState n × AgentState n} {x₀ x₁ : Opinion}
    (ha : GenericAgentTimerBounded K a.1) (hb : GenericAgentTimerBounded K a.2) :
    GenericAgentTimerBounded K (transitionPEM_phase4 n Rmax a x₀ x₁).1 ∧
    GenericAgentTimerBounded K (transitionPEM_phase4 n Rmax a x₀ x₁).2 := by
  by_cases hSettled : a.1.role = .Settled ∧ a.2.role = .Settled
  · let sw := phase4_swap a.1 a.2 x₀ x₁
    have hsw : GenericAgentTimerBounded K sw.1 ∧ GenericAgentTimerBounded K sw.2 :=
      generic_phase4_swap_preserves_timer_bound (x₀ := x₀) (x₁ := x₁) ha hb
    let dec := phase4_decide n sw.1 sw.2 x₀ x₁
    have hdec : GenericAgentTimerBounded K dec.1 ∧ GenericAgentTimerBounded K dec.2 :=
      generic_phase4_decide_preserves_timer_bound (x₀ := x₀) (x₁ := x₁) hsw.1 hsw.2
    have hprop :
        GenericAgentTimerBounded K (phase4_propagate n Rmax dec.1 dec.2).1 ∧
        GenericAgentTimerBounded K (phase4_propagate n Rmax dec.1 dec.2).2 :=
      generic_phase4_propagate_preserves_timer_bound hdec.1 hdec.2
    simpa [transitionPEM_phase4, hSettled, sw, dec] using hprop
  · simpa [transitionPEM_phase4, hSettled] using And.intro ha hb

private theorem generic_transitionPEM_preserves_timer_bound
    {n trank Rmax Emax Dmax K : ℕ} {hn : 0 < n}
    {s₀ s₁ : AgentState n} {x₀ x₁ : Opinion}
    (hK : 7 * (trank + 4) ≤ K)
    (hs₀ : GenericAgentTimerBounded K s₀)
    (hs₁ : GenericAgentTimerBounded K s₁) :
      GenericAgentTimerBounded K
          ((PEMProtocol n trank Rmax Emax Dmax hn).δ ((s₀, x₀), (s₁, x₁))).1 ∧
        GenericAgentTimerBounded K
          ((PEMProtocol n trank Rmax Emax Dmax hn).δ ((s₀, x₀), (s₁, x₁))).2 := by
  have hrd :=
    generic_rankDeltaOSSR_preserves_timer_bound (hn := hn)
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) hs₀ hs₁
  have hpre :=
    generic_transitionPEM_prePhase4_preserves_timer_bound
      (trank := trank) (K := K) (x₀ := x₀) (x₁ := x₁) hK hrd
  simpa [PEMProtocol, protocolPEM, transitionPEM] using
    generic_transitionPEM_phase4_preserves_timer_bound
      (x₀ := x₀) (x₁ := x₁) hpre.1 hpre.2

theorem generic_timer_preservation
    {n trank Rmax Emax Dmax K : ℕ} (hn : 0 < n)
    (hK : 7 * (trank + 4) ≤ K) :
    ∀ C : Config (AgentState n) Opinion n,
      IsTimerBoundedConfig K C →
      ∀ i j : Fin n,
        IsTimerBoundedConfig K
          (C.step (PEMProtocol n trank Rmax Emax Dmax hn) i j) := by
  intro C hC i j μ
  have hi : GenericAgentTimerBounded K (C i).1 := hC i
  have hj : GenericAgentTimerBounded K (C j).1 := hC j
  by_cases hij : i = j
  · subst j
    simpa [Config.step, GenericAgentTimerBounded, IsTimerBoundedConfig] using hC μ
  · by_cases hμi : μ = i
    · subst μ
      have hpair :=
        generic_transitionPEM_preserves_timer_bound
          (trank := trank) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
          (hn := hn) (K := K) (x₀ := (C i).2) (x₁ := (C j).2) hK hi hj
      simpa [Config.step, hij, GenericAgentTimerBounded, IsTimerBoundedConfig]
        using hpair.1
    · by_cases hμj : μ = j
      · subst μ
        have hpair :=
          generic_transitionPEM_preserves_timer_bound
            (trank := trank) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
            (hn := hn) (K := K) (x₀ := (C i).2) (x₁ := (C j).2) hK hi hj
        simpa [Config.step, hij, hμi, GenericAgentTimerBounded, IsTimerBoundedConfig]
          using hpair.2
      · simpa [Config.step, hij, hμi, hμj, GenericAgentTimerBounded, IsTimerBoundedConfig]
          using hC μ

end TimerPreservation

section CoupledTransfer

variable {n trank Rmax Emax Dmax : ℕ}

private theorem generic_transition_eq_coupled_of_settled_distinct
    (hn0 : 0 < n) {s₀ s₁ : AgentState n} {x₀ x₁ : Opinion}
    (hs₀ : s₀.role = .Settled) (hs₁ : s₁.role = .Settled)
    (hne : s₀.rank ≠ s₁.rank) :
    transitionPEM n trank Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
        ((s₀, x₀), (s₁, x₁)) =
      transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
        ((s₀, x₀), (s₁, x₁)) := by
  have hFix := rankDeltaOSSR_satisfies_fix
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn0)
  simp only [transitionPEM_eq]
  rw [transitionPEM_prePhase4_eq_of_settled_distinct
      (trank := trank) hFix hs₀ hs₁ hne]
  rw [transitionPEM_prePhase4_eq_of_settled_distinct
      (trank := Rmax) hFix hs₀ hs₁ hne]

theorem generic_step_eq_coupled_of_InSrank
    (hn0 : 0 < n) {C : Config (AgentState n) Opinion n}
    (hSrank : InSrank C) (i j : Fin n) :
    C.step (PEMProtocol n trank Rmax Emax Dmax hn0) i j =
      C.step (PEMProtocolCoupled n Rmax Emax Dmax hn0) i j := by
  funext w
  by_cases hij : i = j
  · subst j
    simp [Config.step]
  · have hsi : (C i).1.role = .Settled := hSrank.allSettled i
    have hsj : (C j).1.role = .Settled := hSrank.allSettled j
    have hne : (C i).1.rank ≠ (C j).1.rank := by
      intro h
      exact hij (hSrank.ranks_inj h)
    have hδ :=
      generic_transition_eq_coupled_of_settled_distinct
        (trank := trank) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        (x₀ := (C i).2) (x₁ := (C j).2)
        hn0 hsi hsj hne
    by_cases hwi : w = i
    · subst w
      unfold Config.step
      simp only [PEMProtocolCoupled, PEMProtocol, hij, ↓reduceIte]
      exact congrArg (fun p => (p.1, (C i).2)) hδ
    · by_cases hwj : w = j
      · subst w
        unfold Config.step
        simp only [PEMProtocolCoupled, PEMProtocol, hij, hwi, ↓reduceIte]
        exact congrArg (fun p => (p.2, (C j).2)) hδ
      · unfold Config.step
        simp [PEMProtocolCoupled, PEMProtocol, hij, hwi, hwj]

private theorem generic_step_eq_coupled_of_not_bad
    (hn0 : 0 < n)
    {Bad : Config (AgentState n) Opinion n → Prop}
    (hBad : ∀ C : Config (AgentState n) Opinion n, ¬ Bad C → InSrank C)
    {C : Config (AgentState n) Opinion n} (hC : ¬ Bad C) (i j : Fin n) :
    C.step (PEMProtocol n trank Rmax Emax Dmax hn0) i j =
      C.step (PEMProtocolCoupled n Rmax Emax Dmax hn0) i j :=
  generic_step_eq_coupled_of_InSrank
    (trank := trank) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
    hn0 (hBad C hC) i j

private theorem generic_probHitBy_succ_eq_tsum_step_of_not_goal
    {Q X Y : Type*} {n : ℕ} [DecidableEq (Config Q X n)]
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop)
    [DecidablePred Goal] (hGoal : ¬ Goal C₀) (t : ℕ) :
    Probability.probHitBy P hn C₀ Goal (t + 1) =
      ∑' C : Config Q X n,
        Probability.stepDist P hn C₀ C *
          Probability.probHitBy P hn C Goal t := by
  classical
  rw [Probability.probHitBy_eq_hitFlagDist_toOuterMeasure]
  rw [Probability.hitFlagDist_eq_hitFlagDistFrom]
  simp only [hGoal, decide_false]
  rw [show t + 1 = 1 + t by omega]
  rw [Probability.hitFlagDistFrom_add]
  simp only [Probability.hitFlagDistFrom, PMF.pure_bind]
  rw [Probability.hitFlagStepDist, PMF.bind_map]
  simp only [Bool.false_or]
  rw [PMF.toOuterMeasure_bind_apply]
  apply tsum_congr
  intro C
  simp only [Function.comp_apply]
  have hdec :
      @decide (Goal C) (Classical.propDecidable (Goal C)) =
        @decide (Goal C) (inferInstance : Decidable (Goal C)) := by
    by_cases h : Goal C <;> simp [h]
  rw [hdec]
  have hhit :
      (Probability.hitFlagDistFrom P hn Goal (C, decide (Goal C)) t).toOuterMeasure
          {T : Config Q X n × Bool | T.2 = true} =
        Probability.probHitBy P hn C Goal t := by
    rw [Probability.probHitBy_eq_hitFlagDist_toOuterMeasure,
      Probability.hitFlagDist_eq_hitFlagDistFrom P hn C Goal t]
  exact congrArg (fun x => Probability.stepDist P hn C₀ C * x) hhit

private theorem generic_ProbHitWithin_eq_of_step_eq_until
    [DecidableEq (Config (AgentState n) Opinion n)]
    (hn2 : 2 ≤ n) (hn0 : 0 < n)
    (Bad : Config (AgentState n) Opinion n → Prop) [DecidablePred Bad]
    (hstep :
      ∀ C : Config (AgentState n) Opinion n, ¬ Bad C →
        ∀ i j : Fin n,
          C.step (PEMProtocol n trank Rmax Emax Dmax hn0) i j =
            C.step (PEMProtocolCoupled n Rmax Emax Dmax hn0) i j)
    (C : Config (AgentState n) Opinion n) (t : ℕ) :
    Probability.ProbHitWithin
        (PEMProtocol n trank Rmax Emax Dmax hn0) hn2 C Bad t =
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C Bad t := by
  classical
  let Pg := PEMProtocol n trank Rmax Emax Dmax hn0
  let Pc := PEMProtocolCoupled n Rmax Emax Dmax hn0
  induction t generalizing C with
  | zero =>
      by_cases hC : Bad C
      · rw [Probability.ProbHitWithin, Probability.ProbHitWithin,
          Probability.probHitBy_zero_of_goal Pg hn2 C Bad hC,
          Probability.probHitBy_zero_of_goal Pc hn2 C Bad hC]
      · rw [Probability.ProbHitWithin, Probability.ProbHitWithin,
          Probability.probHitBy_zero_of_not_goal Pg hn2 C Bad hC,
          Probability.probHitBy_zero_of_not_goal Pc hn2 C Bad hC]
  | succ t ih =>
      by_cases hC : Bad C
      · have hg0 :
            Probability.ProbHitWithin Pg hn2 C Bad 0 = 1 := by
          exact Probability.probHitBy_zero_of_goal Pg hn2 C Bad hC
        have hc0 :
            Probability.ProbHitWithin Pc hn2 C Bad 0 = 1 := by
          exact Probability.probHitBy_zero_of_goal Pc hn2 C Bad hC
        have hg_le :
            (1 : ENNReal) ≤ Probability.ProbHitWithin Pg hn2 C Bad (t + 1) := by
          rw [← hg0]
          exact Probability.ProbHitWithin_mono_time Pg hn2 C Bad (Nat.zero_le _)
        have hc_le :
            (1 : ENNReal) ≤ Probability.ProbHitWithin Pc hn2 C Bad (t + 1) := by
          rw [← hc0]
          exact Probability.ProbHitWithin_mono_time Pc hn2 C Bad (Nat.zero_le _)
        have hg :
            Probability.ProbHitWithin Pg hn2 C Bad (t + 1) = 1 :=
          le_antisymm (Probability.ProbHitWithin_le_one Pg hn2 C Bad (t + 1)) hg_le
        have hc :
            Probability.ProbHitWithin Pc hn2 C Bad (t + 1) = 1 :=
          le_antisymm (Probability.ProbHitWithin_le_one Pc hn2 C Bad (t + 1)) hc_le
        rw [hg, hc]
      · have hstepDist :
            Probability.stepDist Pg hn2 C = Probability.stepDist Pc hn2 C := by
          unfold Probability.stepDist
          congr 1
          funext p
          exact hstep C hC p.1 p.2
        rw [Probability.ProbHitWithin, Probability.ProbHitWithin,
          generic_probHitBy_succ_eq_tsum_step_of_not_goal Pg hn2 C Bad hC t,
          generic_probHitBy_succ_eq_tsum_step_of_not_goal Pc hn2 C Bad hC t]
        apply tsum_congr
        intro D
        have hih := ih D
        change Probability.probHitBy Pg hn2 D Bad t =
          Probability.probHitBy Pc hn2 D Bad t at hih
        rw [hstepDist, hih]

private theorem generic_probNotHitBy_succ_eq_tsum_step_of_not_goal
    {Q X Y : Type*} {n : ℕ} [DecidableEq (Config Q X n)]
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop)
    [DecidablePred Goal] (hGoal : ¬ Goal C₀) (t : ℕ) :
    Probability.probNotHitBy P hn C₀ Goal (t + 1) =
      ∑' C : Config Q X n,
        Probability.stepDist P hn C₀ C *
          Probability.probNotHitBy P hn C Goal t := by
  classical
  rw [← Probability.probNotHitFrom_initial_eq_probNotHitBy P hn C₀ Goal (t + 1)]
  simp only [hGoal, decide_false]
  rw [show t + 1 = 1 + t by omega]
  rw [Probability.probNotHitFrom_eq_toOuterMeasure, Probability.hitFlagDistFrom_add]
  simp only [Probability.hitFlagDistFrom, PMF.pure_bind]
  rw [Probability.hitFlagStepDist, PMF.bind_map]
  simp only [Bool.false_or]
  rw [PMF.toOuterMeasure_bind_apply]
  apply tsum_congr
  intro C
  simp only [Function.comp_apply]
  have hdec :
      @decide (Goal C) (Classical.propDecidable (Goal C)) =
        @decide (Goal C) (inferInstance : Decidable (Goal C)) := by
    by_cases h : Goal C <;> simp [h]
  rw [hdec]
  have htail :
      (Probability.hitFlagDistFrom P hn Goal (C, decide (Goal C)) t).toOuterMeasure
          {T : Config Q X n × Bool | T.2 = false} =
        Probability.probNotHitBy P hn C Goal t := by
    rw [← Probability.probNotHitFrom_eq_toOuterMeasure P hn Goal
      (C, decide (Goal C)) t]
    rw [Probability.probNotHitFrom_initial_eq_probNotHitBy P hn C Goal t]
  exact congrArg (fun x => Probability.stepDist P hn C₀ C * x) htail

private theorem generic_probNotHitBy_eq_of_step_eq_until
    [DecidableEq (Config (AgentState n) Opinion n)]
    (hn2 : 2 ≤ n) (hn0 : 0 < n)
    (Goal : Config (AgentState n) Opinion n → Prop) [DecidablePred Goal]
    (hstep :
      ∀ C : Config (AgentState n) Opinion n, ¬ Goal C →
        ∀ i j : Fin n,
          C.step (PEMProtocol n trank Rmax Emax Dmax hn0) i j =
            C.step (PEMProtocolCoupled n Rmax Emax Dmax hn0) i j)
    (C : Config (AgentState n) Opinion n) (t : ℕ) :
    Probability.probNotHitBy
        (PEMProtocol n trank Rmax Emax Dmax hn0) hn2 C Goal t =
      Probability.probNotHitBy
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C Goal t := by
  classical
  let Pg := PEMProtocol n trank Rmax Emax Dmax hn0
  let Pc := PEMProtocolCoupled n Rmax Emax Dmax hn0
  induction t generalizing C with
  | zero =>
      by_cases hC : Goal C
      · rw [Probability.probNotHitBy_zero_of_goal Pg hn2 C Goal hC,
          Probability.probNotHitBy_zero_of_goal Pc hn2 C Goal hC]
      · rw [Probability.probNotHitBy_zero_of_not_goal Pg hn2 C Goal hC,
          Probability.probNotHitBy_zero_of_not_goal Pc hn2 C Goal hC]
  | succ t ih =>
      by_cases hC : Goal C
      · have hg0 :
            Probability.probNotHitBy Pg hn2 C Goal 0 = 0 :=
          Probability.probNotHitBy_zero_of_goal Pg hn2 C Goal hC
        have hc0 :
            Probability.probNotHitBy Pc hn2 C Goal 0 = 0 :=
          Probability.probNotHitBy_zero_of_goal Pc hn2 C Goal hC
        have hg_le :
            Probability.probNotHitBy Pg hn2 C Goal (t + 1) ≤ 0 := by
          simpa [hg0] using
            (Probability.probNotHitBy_le_of_le Pg hn2 C Goal
              (Nat.zero_le (t + 1)))
        have hc_le :
            Probability.probNotHitBy Pc hn2 C Goal (t + 1) ≤ 0 := by
          simpa [hc0] using
            (Probability.probNotHitBy_le_of_le Pc hn2 C Goal
              (Nat.zero_le (t + 1)))
        have hg :
            Probability.probNotHitBy Pg hn2 C Goal (t + 1) = 0 :=
          le_antisymm hg_le zero_le
        have hc :
            Probability.probNotHitBy Pc hn2 C Goal (t + 1) = 0 :=
          le_antisymm hc_le zero_le
        rw [hg, hc]
      · have hstepDist :
            Probability.stepDist Pg hn2 C = Probability.stepDist Pc hn2 C := by
          unfold Probability.stepDist
          congr 1
          funext p
          exact hstep C hC p.1 p.2
        rw [
          generic_probNotHitBy_succ_eq_tsum_step_of_not_goal Pg hn2 C Goal hC t,
          generic_probNotHitBy_succ_eq_tsum_step_of_not_goal Pc hn2 C Goal hC t]
        apply tsum_congr
        intro D
        have hih := ih D
        rw [hstepDist, hih]

theorem generic_expectedHittingTime_eq_of_step_eq_until
    [DecidableEq (Config (AgentState n) Opinion n)]
    (hn2 : 2 ≤ n) (hn0 : 0 < n)
    (Goal : Config (AgentState n) Opinion n → Prop) [DecidablePred Goal]
    (hstep :
      ∀ C : Config (AgentState n) Opinion n, ¬ Goal C →
        ∀ i j : Fin n,
          C.step (PEMProtocol n trank Rmax Emax Dmax hn0) i j =
            C.step (PEMProtocolCoupled n Rmax Emax Dmax hn0) i j)
    (C : Config (AgentState n) Opinion n) :
    Probability.expectedHittingTime
        (PEMProtocol n trank Rmax Emax Dmax hn0) hn2 C Goal =
      Probability.expectedHittingTime
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C Goal := by
  classical
  rw [Probability.expectedHittingTime, Probability.expectedHittingTime]
  apply tsum_congr
  intro t
  exact
    generic_probNotHitBy_eq_of_step_eq_until
      (n := n) (trank := trank) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      hn2 hn0 Goal hstep C t

end CoupledTransfer

section GenericStepHelpers

variable {n trank Rmax Emax Dmax : ℕ}

theorem generic_step_rank_preserved_of_InSswap
    (hn0 : 0 < n)
    {D : Config (AgentState n) Opinion n}
    (hS : InSswap D) {i j : Fin n}
    (w : Fin n) :
    (D.step (PEMProtocol n trank Rmax Emax Dmax hn0) i j w).1.rank =
      (D w).1.rank := by
  have hEq :=
    generic_step_eq_coupled_of_InSrank
      (trank := trank) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      hn0 hS.toInSrank i j
  rw [hEq]
  exact
    step_rank_preserved_of_InSswap
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) hn0 hS w

theorem generic_step_timer_le_of_InSswap
    (hn0 : 0 < n)
    {D : Config (AgentState n) Opinion n}
    (hS : InSswap D) {i j : Fin n}
    (w : Fin n) :
    (D.step (PEMProtocol n trank Rmax Emax Dmax hn0) i j w).1.timer ≤
      (D w).1.timer := by
  have hEq :=
    generic_step_eq_coupled_of_InSrank
      (trank := trank) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      hn0 hS.toInSrank i j
  rw [hEq]
  exact
    step_timer_le_of_InSswap
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) hn0 hS w

theorem generic_step_median_answer_of_InSswap_both
    [Inhabited (Fin n × Fin n)]
    (hn0 : 0 < n) (hn4 : 4 ≤ n)
    {D : Config (AgentState n) Opinion n}
    (hS : InSswap D) {i j : Fin n}
    (hS' :
      InSswap
        (D.step (PEMProtocol n trank Rmax Emax Dmax hn0) i j))
    (hM : MedianAnswerCorrect D) :
    MedianAnswerCorrect
      (D.step (PEMProtocol n trank Rmax Emax Dmax hn0) i j) := by
  let P := PEMProtocol n trank Rmax Emax Dmax hn0
  let Pc := PEMProtocolCoupled n Rmax Emax Dmax hn0
  have hEq : D.step P i j = D.step Pc i j :=
    generic_step_eq_coupled_of_InSrank
      (trank := trank) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      hn0 hS.toInSrank i j
  have hS'_coupled : InSswap (D.step Pc i j) := by
    simpa [P, Pc, hEq] using hS'
  have hCoupled :
      MedianAnswerCorrect (D.step Pc i j) :=
    step_median_answer_of_InSswap_both
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      hn0 hn4 hS hS'_coupled hM
  simpa [P, Pc, hEq] using hCoupled

theorem generic_crs_of_InSswap_break_with_MedC
    [Inhabited (Fin n × Fin n)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n) (hRmax : n ≤ Rmax)
    {D : Config (AgentState n) Opinion n}
    (hS : InSswap D) (hM : MedianAnswerCorrect D)
    {i j : Fin n}
    (hS' : ¬ InSswap
      (D.step (PEMProtocol n trank Rmax Emax Dmax hn0) i j)) :
    CorrectResetSeed
      (D.step (PEMProtocol n trank Rmax Emax Dmax hn0) i j) := by
  have hEq :=
    generic_step_eq_coupled_of_InSrank
      (trank := trank) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      hn0 hS.toInSrank i j
  have hBreakCoupled :
      ¬ InSswap
        (D.step (PEMProtocolCoupled n Rmax Emax Dmax hn0) i j) := by
    intro hCoupled
    exact hS' (by simpa [hEq] using hCoupled)
  have hSeedCoupled :
      CorrectResetSeed
        (D.step (PEMProtocolCoupled n Rmax Emax Dmax hn0) i j) :=
    crs_of_InSswap_break_with_MedC
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      hn4 hn0 hRmax hS hM hBreakCoupled
  simpa [hEq] using hSeedCoupled

private theorem generic_step_InSswap_of_InSswap_of_post_InSrank
    (hn0 : 0 < n)
    {D : Config (AgentState n) Opinion n}
    (hS : InSswap D) {i j : Fin n}
    (hRank' :
      InSrank
        (D.step (PEMProtocol n trank Rmax Emax Dmax hn0) i j)) :
    InSswap
      (D.step (PEMProtocol n trank Rmax Emax Dmax hn0) i j) := by
  classical
  let P := PEMProtocol n trank Rmax Emax Dmax hn0
  have hInput :
      ∀ w : Fin n, (D.step P i j w).2 = (D w).2 := by
    intro w
    exact step_input_preserved P D i j w
  have hRank :
      ∀ w : Fin n, (D.step P i j w).1.rank = (D w).1.rank := by
    intro w
    simpa [P] using
      generic_step_rank_preserved_of_InSswap
        (trank := trank) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        hn0 hS w
  have hnA : nAOf (D.step P i j) = nAOf D := by
    simpa [P, PEMProtocol] using
      (nAOf_step_eq (trank := trank) (Rmax := Rmax)
        (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0) D i j)
  refine { toInSrank := hRank', input_rank := ?_ }
  intro w
  constructor
  · intro hA
    have hA_old : (D w).2 = Opinion.A := by
      rw [hInput w] at hA
      exact hA
    have hlt_old : (D w).1.rank.val < nAOf D :=
      (hS.input_rank w).mp hA_old
    rw [hRank w, hnA]
    exact hlt_old
  · intro hlt
    have hlt_old : (D w).1.rank.val < nAOf D := by
      rw [hRank w, hnA] at hlt
      exact hlt
    have hA_old : (D w).2 = Opinion.A :=
      (hS.input_rank w).mpr hlt_old
    rw [hInput w]
    exact hA_old

end GenericStepHelpers

section GenericExitWindow

variable {n trank Rmax Emax Dmax : ℕ}

theorem generic_PEM_srank_or_timer_failure_prob_le_quarter_short35_no_counter
    [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n)
    (C : Config (AgentState n) Opinion n)
    (hSrank : InSrank C)
    (hTimer : MedianTimerAtLeast 35 C) :
    Probability.ProbHitWithin
      (PEMProtocol n trank Rmax Emax Dmax hn0)
      (by omega : 2 ≤ n) C
      (fun D => ¬ InSrank D ∨ ¬ MedianTimerAtLeast 1 D)
      (4 * n * (n - 1)) ≤ ((4 : ENNReal)⁻¹) := by
  classical
  let Bad : Config (AgentState n) Opinion n → Prop :=
    fun D => ¬ InSrank D ∨ ¬ MedianTimerAtLeast 1 D
  have hstep :
      ∀ D : Config (AgentState n) Opinion n, ¬ Bad D →
        ∀ i j : Fin n,
          D.step (PEMProtocol n trank Rmax Emax Dmax hn0) i j =
            D.step (PEMProtocolCoupled n Rmax Emax Dmax hn0) i j := by
    intro D hD i j
    have hRank : InSrank D := by
      by_contra hNot
      exact hD (Or.inl hNot)
    exact
      generic_step_eq_coupled_of_InSrank
        (trank := trank) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        hn0 hRank i j
  have hn2 : 2 ≤ n := by omega
  have hEq :=
    generic_ProbHitWithin_eq_of_step_eq_until
      (n := n) (trank := trank) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      hn2 hn0 Bad hstep C (4 * n * (n - 1))
  have hCoupled :
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0)
        hn2 C Bad (4 * n * (n - 1)) ≤ ((4 : ENNReal)⁻¹) := by
    simpa [Bad] using
      (PEM_srank_or_timer_failure_prob_le_quarter_short35_no_counter
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        hn4 hn0 C hSrank hTimer)
  simpa [Bad] using (le_of_eq_of_le hEq hCoupled)

theorem generic_PEM_srank_or_timer_failure_prob_le_quarter_short35
    [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n)
    (_hRmax : n ≤ Rmax) (_hEmax : n ≤ Emax) (_hDmax : n ≤ Dmax)
    (C : Config (AgentState n) Opinion n)
    (hSrank : InSrank C)
    (hTimer : MedianTimerAtLeast 35 C) :
    Probability.ProbHitWithin
      (PEMProtocol n trank Rmax Emax Dmax hn0)
      (by omega : 2 ≤ n) C
      (fun D => ¬ InSrank D ∨ ¬ MedianTimerAtLeast 1 D)
      (4 * n * (n - 1)) ≤ ((4 : ENNReal)⁻¹) :=
  generic_PEM_srank_or_timer_failure_prob_le_quarter_short35_no_counter
    (n := n) (trank := trank) (Rmax := Rmax) (Emax := Emax)
    (Dmax := Dmax) hn4 hn0 C hSrank hTimer

end GenericExitWindow

section GenericLiveExit

variable {n trank Rmax Emax Dmax : ℕ}

private theorem generic_toOuterMeasure_le_of_support_imp
    {α : Type*} (μ : PMF α) (A B : Set α)
    (h : ∀ a : α, μ a ≠ 0 → a ∈ A → a ∈ B) :
    μ.toOuterMeasure A ≤ μ.toOuterMeasure B := by
  rw [PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply]
  apply ENNReal.tsum_le_tsum
  intro a
  by_cases hA : a ∈ A
  · rw [Set.indicator_of_mem hA]
    by_cases hB : a ∈ B
    · rw [Set.indicator_of_mem hB]
    · rw [Set.indicator_of_notMem hB]
      have hzero : μ a = 0 := by
        by_contra hne
        exact hB (h a hne hA)
      simp [hzero]
  · rw [Set.indicator_of_notMem hA]
    exact zero_le

private theorem generic_hitTwoFlagDist_live_exit_bad_stopped
    (hn0 : 0 < n) (hn2 : 2 ≤ n)
    (C₀ : Config (AgentState n) Opinion n)
    (hLive₀ : InSswap C₀ ∧ MedianTimerAtLeast 1 C₀) :
    let P := PEMProtocol n trank Rmax Emax Dmax hn0
    let Exit : Config (AgentState n) Opinion n → Prop :=
      fun D => ¬ (InSswap D ∧ MedianTimerAtLeast 1 D)
    let Bad : Config (AgentState n) Opinion n → Prop :=
      fun D => ¬ InSrank D ∨ ¬ MedianTimerAtLeast 1 D
    ∀ t : ℕ, ∀ S : Config (AgentState n) Opinion n × (Bool × Bool),
      S ∈ (Probability.hitTwoFlagDist P hn2 C₀ Exit Bad t).support →
        S.2.2 = false →
          (InSswap S.1 ∧ MedianTimerAtLeast 1 S.1) ∧ S.2.1 = false := by
  classical
  intro P Exit Bad t
  induction t with
  | zero =>
      intro S hSupp _hBadFalse
      rw [Probability.hitTwoFlagDist, PMF.support_pure] at hSupp
      subst S
      constructor
      · exact hLive₀
      · simp [Exit, hLive₀]
  | succ t ih =>
      intro S hSupp hBadFalse
      rw [Probability.hitTwoFlagDist, PMF.mem_support_bind_iff] at hSupp
      obtain ⟨T, hT, hStep⟩ := hSupp
      rcases T with ⟨D, flags⟩
      rw [Probability.hitTwoFlagStepDist, PMF.support_map] at hStep
      obtain ⟨D', hD', hEq⟩ := hStep
      subst S
      rw [Probability.stepDist, PMF.support_map] at hD'
      obtain ⟨p, _hp, hpEq⟩ := hD'
      subst D'
      have hBadStep :
          (flags.2 || decide (Bad (D.step P p.1 p.2))) = false := by
        simpa using hBadFalse
      have hBadOldFalse : flags.2 = false := by
        cases hflags : flags.2
        · rfl
        · have hContra : False := by
            simp [hflags] at hBadStep
          exact False.elim hContra
      have hNotBadStep : ¬ Bad (D.step P p.1 p.2) := by
        intro hBad
        have hContra : False := by
          simp [hBadOldFalse, hBad] at hBadStep
        exact False.elim hContra
      obtain ⟨hLiveD, hExitOldFalse⟩ := ih (D, flags) hT hBadOldFalse
      have hExitOldFalse' : flags.1 = false := by
        simpa using hExitOldFalse
      have hRankStep : InSrank (D.step P p.1 p.2) := by
        by_contra hNotRank
        exact hNotBadStep (Or.inl hNotRank)
      have hTimerStep : MedianTimerAtLeast 1 (D.step P p.1 p.2) := by
        by_contra hNotTimer
        exact hNotBadStep (Or.inr hNotTimer)
      have hSwapStep : InSswap (D.step P p.1 p.2) := by
        simpa [P] using
          (generic_step_InSswap_of_InSswap_of_post_InSrank
            (trank := trank) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
            hn0 hLiveD.1 hRankStep)
      have hLiveStep :
          InSswap (D.step P p.1 p.2) ∧
            MedianTimerAtLeast 1 (D.step P p.1 p.2) :=
        ⟨hSwapStep, hTimerStep⟩
      constructor
      · exact hLiveStep
      · have hNotExitStep : ¬ Exit (D.step P p.1 p.2) := by
          intro hExitStep
          exact hExitStep hLiveStep
        have hExitStepFalse : decide (Exit (D.step P p.1 p.2)) = false := by
          exact decide_eq_false hNotExitStep
        simpa [hExitOldFalse', hExitStepFalse]

theorem generic_live_exit_ProbHitWithin_le_bad
    (hn0 : 0 < n) (hn2 : 2 ≤ n)
    (C₀ : Config (AgentState n) Opinion n)
    (hLive₀ : InSswap C₀ ∧ MedianTimerAtLeast 1 C₀) (t : ℕ) :
    let P := PEMProtocol n trank Rmax Emax Dmax hn0
    Probability.ProbHitWithin P hn2 C₀
        (fun D => ¬ (InSswap D ∧ MedianTimerAtLeast 1 D)) t ≤
      Probability.ProbHitWithin P hn2 C₀
        (fun D => ¬ InSrank D ∨ ¬ MedianTimerAtLeast 1 D) t := by
  classical
  intro P
  let Exit : Config (AgentState n) Opinion n → Prop :=
    fun D => ¬ (InSswap D ∧ MedianTimerAtLeast 1 D)
  let Bad : Config (AgentState n) Opinion n → Prop :=
    fun D => ¬ InSrank D ∨ ¬ MedianTimerAtLeast 1 D
  let μ := Probability.hitTwoFlagDist P hn2 C₀ Exit Bad t
  have hExitEq :
      Probability.ProbHitWithin P hn2 C₀ Exit t =
        μ.toOuterMeasure
          {S : Config (AgentState n) Opinion n × (Bool × Bool) |
            S.2.1 = true} := by
    rw [Probability.ProbHitWithin, Probability.probHitBy_eq_hitFlagDist_toOuterMeasure,
      ← Probability.hitTwoFlagDist_map_left P hn2 C₀ Exit Bad t,
      PMF.toOuterMeasure_map_apply]
    rfl
  have hBadEq :
      Probability.ProbHitWithin P hn2 C₀ Bad t =
        μ.toOuterMeasure
          {S : Config (AgentState n) Opinion n × (Bool × Bool) |
            S.2.2 = true} := by
    rw [Probability.ProbHitWithin, Probability.probHitBy_eq_hitFlagDist_toOuterMeasure,
      ← Probability.hitTwoFlagDist_map_right P hn2 C₀ Exit Bad t,
      PMF.toOuterMeasure_map_apply]
    rfl
  rw [hExitEq, hBadEq]
  apply generic_toOuterMeasure_le_of_support_imp
  intro S hμ hExitHit
  by_cases hBadHit : S.2.2 = true
  · exact hBadHit
  · have hBadFalse : S.2.2 = false := by
      cases h : S.2.2
      · rfl
      · exact False.elim (hBadHit h)
    have hSupp : S ∈ μ.support := by
      simpa [μ, PMF.mem_support_iff] using hμ
    have hStopped :=
      generic_hitTwoFlagDist_live_exit_bad_stopped
        (trank := trank) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        hn0 hn2 C₀ hLive₀ t S hSupp hBadFalse
    have hExitTrue : S.2.1 = true := hExitHit
    rw [hStopped.2] at hExitTrue
    cases hExitTrue

end GenericLiveExit

private theorem generic_card_Fin_filter_val_lt {n k : ℕ} (hk : k ≤ n) :
    (Finset.univ.filter (fun i : Fin n => i.val < k)).card = k := by
  classical
  let toFin : Fin k → Fin n := fun i => ⟨i.val, lt_of_lt_of_le i.isLt hk⟩
  have hinj : Function.Injective toFin := by
    intro i j h
    have : i.val = j.val := congrArg (fun x : Fin n => x.val) h
    exact Fin.ext this
  have himg : (Finset.univ : Finset (Fin k)).image toFin
            = Finset.univ.filter (fun i : Fin n => i.val < k) := by
    ext i
    rw [Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨j, _, hfj⟩
      refine ⟨Finset.mem_univ _, ?_⟩
      have : (toFin j).val = i.val := congrArg Fin.val hfj
      have hj : j.val < k := j.isLt
      exact this ▸ hj
    · rintro ⟨_, hi⟩
      refine ⟨⟨i.val, hi⟩, Finset.mem_univ _, ?_⟩
      apply Fin.eq_of_val_eq
      rfl
  rw [← himg, Finset.card_image_of_injective _ hinj, Finset.card_univ,
      Fintype.card_fin]

private theorem generic_card_filter_rank_lt {C : Config (AgentState n) Opinion n}
    (hRank : InSrank C) {k : ℕ} (hk : k ≤ n) :
    (Finset.univ.filter (fun u : Fin n => (C u).1.rank.val < k)).card = k := by
  classical
  have hinj : Function.Injective (fun u : Fin n => (C u).1.rank) := hRank.ranks_inj
  have hsurj : Function.Surjective (fun u : Fin n => (C u).1.rank) :=
    Finite.injective_iff_surjective.mp hinj
  have himg : (Finset.univ.filter (fun u : Fin n => (C u).1.rank.val < k)).image
                (fun u => (C u).1.rank)
            = Finset.univ.filter (fun i : Fin n => i.val < k) := by
    ext i
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact hu
    · intro hi
      obtain ⟨u, hu⟩ := hsurj i
      refine ⟨u, ?_, hu⟩
      rw [show (C u).1.rank.val = i.val from congrArg Fin.val hu]
      exact hi
  rw [← Finset.card_image_of_injective _ hinj, himg, generic_card_Fin_filter_val_lt hk]

section DecisionWindow

variable {n trank Rmax Emax Dmax : ℕ}

theorem generic_PEM_even_median_wrong_to_MedianAnswerCorrect_prob_lower_bound
    (hn2 : 2 ≤ n) (hn0 : 0 < n) (hn4 : 4 ≤ n)
    {C : Config (AgentState n) Opinion n} (hC : InSswap C)
    (hpar : n % 2 = 0)
    (h_med_wrong : ∃ μ : Fin n, (C μ).1.rank.val + 1 = ceilHalf n ∧
      (C μ).1.answer ≠ majorityAnswer C) :
    ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ≤
      Probability.ProbHitWithin
        (PEMProtocol n trank Rmax Emax Dmax hn0) hn2 C
        (fun D => InSswap D ∧ MedianAnswerCorrect D) 1 := by
  classical
  let P := PEMProtocol n trank Rmax Emax Dmax hn0
  have hRankFix := rankDeltaOSSR_satisfies_fix
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn0)
  have hceil : ceilHalf n = n / 2 := ceilHalf_eq_half_of_even hpar
  have htarget_not : ¬ (InSswap C ∧ MedianAnswerCorrect C) := by
    intro hTarget
    rcases h_med_wrong with ⟨μ, hμ, hwrong⟩
    exact hwrong (hTarget.2 μ hμ)
  by_cases hTie : nAOf C = nBOf C
  · obtain ⟨u, v, huv, hu_med, hv_upper, h_disagree, h_wrong⟩ :=
      evenCase_witness_when_median_wrong_tie hC hpar hn4 hTie h_med_wrong
    have hsu := hC.allSettled u
    have hsv := hC.allSettled v
    have h_no_swap : ¬((C u).2 = Opinion.B ∧ (C v).2 = Opinion.A) := by
      intro h
      rcases h with ⟨huB, _hvA⟩
      have hsum := nAOf_add_nBOf C
      have hu_low : (C u).1.rank.val < nAOf C := by omega
      have huA : (C u).2 = Opinion.A := (hC.input_rank u).mpr hu_low
      rw [huA] at huB
      cases huB
    obtain ⟨h_u, _h_v, _h_others, _h_inputs⟩ :=
      step_at_median_pair_even_disagreed_inputs
        (trank := trank) (Rmax := Rmax)
        hRankFix huv hsu hsv hpar hu_med hv_upper h_disagree h_no_swap hn4
    have hSwap' : InSswap (C.step P u v) := by
      have hdec := decision_step_at_median_pair_even_tie_decreases
        (n := n) (trank := trank) (Rmax := Rmax)
        (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
        hRankFix hC huv hpar hu_med hv_upper h_disagree hTie hn4 h_wrong
      simpa [P, PEMProtocol] using hdec.1
    have hmaj : majorityAnswer (C.step P u v) = majorityAnswer C := by
      simpa [P, PEMProtocol] using
        (majorityAnswer_step_eq
          (trank := trank) (Rmax := Rmax)
          (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0) C u v)
    have h_u_correct : (C.step P u v u).1.answer = majorityAnswer (C.step P u v) := by
      have h_outT : majorityAnswer C = .outT := majorityAnswer_eq_outT_of_tie hTie
      have hu_state : (C.step P u v u).1 = {(C u).1 with answer := .outT} := by
        simpa [P, PEMProtocol] using h_u
      rw [hmaj, h_outT, hu_state]
    have h_u_med' : (C.step P u v u).1.rank.val + 1 = ceilHalf n := by
      have hu_state : (C.step P u v u).1 = {(C u).1 with answer := .outT} := by
        simpa [P, PEMProtocol] using h_u
      rw [hu_state, hceil]
      simpa using hu_med
    have hGoal : InSswap (C.step P u v) ∧ MedianAnswerCorrect (C.step P u v) := by
      refine ⟨hSwap', ?_⟩
      intro η hη
      have hηu : η = u := by
        apply hSwap'.ranks_inj
        apply Fin.eq_of_val_eq
        have hηval : (C.step P u v η).1.rank.val = ceilHalf n - 1 := by omega
        have huval : (C.step P u v u).1.rank.val = ceilHalf n - 1 := by omega
        exact hηval.trans huval.symm
      subst η
      exact h_u_correct
    exact Probability.ProbHitWithin_one_lower_bound_of_step
      (P := P) hn2 C (fun D => InSswap D ∧ MedianAnswerCorrect D)
      htarget_not huv hGoal
  · obtain ⟨u, v, huv, hu_med, hv_upper, h_agree, h_wrong⟩ :=
      evenCase_witness_when_median_wrong hC hpar hn4 hTie h_med_wrong
    have hsu := hC.allSettled u
    have hsv := hC.allSettled v
    have hC'_eq := step_at_median_pair_even_agreed_inputs
      (n := n) (trank := trank) (Rmax := Rmax)
      (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
      hRankFix huv hsu hsv hpar hu_med hv_upper h_agree hn4
    have hSwap' : InSswap (C.step P u v) := by
      have hdec := decision_step_at_median_pair_even_decreases
        (n := n) (trank := trank) (Rmax := Rmax)
        (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
        hRankFix hC huv hpar hu_med hv_upper h_agree hTie hn4 h_wrong
      simpa [P, PEMProtocol] using hdec.1
    have hmaj : majorityAnswer (C.step P u v) = majorityAnswer C := by
      simpa [P, PEMProtocol] using
        (majorityAnswer_step_eq
          (trank := trank) (Rmax := Rmax)
          (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0) C u v)
    have h_correct : opinionToAnswer (C u).2 = majorityAnswer C :=
      opinionToAnswer_lower_median_eq_majorityAnswer_even hC hu_med hpar hTie
    have h_u_correct : (C.step P u v u).1.answer = majorityAnswer (C.step P u v) := by
      rw [hmaj]
      have hval := congrFun hC'_eq u
      rw [show (C.step P u v u) =
          (if u = u then ({(C u).1 with answer := opinionToAnswer (C u).2}, (C u).2)
            else if u = v then ({(C v).1 with answer := opinionToAnswer (C u).2}, (C v).2)
            else C u) by simpa [P, PEMProtocol] using hval]
      simp [h_correct]
    have h_u_med' : (C.step P u v u).1.rank.val + 1 = ceilHalf n := by
      have hval := congrFun hC'_eq u
      rw [show (C.step P u v u) =
          (if u = u then ({(C u).1 with answer := opinionToAnswer (C u).2}, (C u).2)
            else if u = v then ({(C v).1 with answer := opinionToAnswer (C u).2}, (C v).2)
            else C u) by simpa [P, PEMProtocol] using hval]
      simp [hceil, hu_med]
    have hGoal : InSswap (C.step P u v) ∧ MedianAnswerCorrect (C.step P u v) := by
      refine ⟨hSwap', ?_⟩
      intro η hη
      have hηu : η = u := by
        apply hSwap'.ranks_inj
        apply Fin.eq_of_val_eq
        have hηval : (C.step P u v η).1.rank.val = ceilHalf n - 1 := by omega
        have huval : (C.step P u v u).1.rank.val = ceilHalf n - 1 := by omega
        exact hηval.trans huval.symm
      subst η
      exact h_u_correct
    exact Probability.ProbHitWithin_one_lower_bound_of_step
      (P := P) hn2 C (fun D => InSswap D ∧ MedianAnswerCorrect D)
      htarget_not huv hGoal

theorem generic_PEM_odd_median_wrong_to_MedianAnswerCorrect_prob_lower_bound
    (hn2 : 2 ≤ n) (hn0 : 0 < n)
    {C : Config (AgentState n) Opinion n} (hC : InSswap C)
    {μ : Fin n}
    (hpar : ¬ n % 2 = 0)
    (hμ_med : (C μ).1.rank.val + 1 = ceilHalf n)
    (h_timer : 1 ≤ (C μ).1.timer)
    (h_μ_wrong : (C μ).1.answer ≠ majorityAnswer C) :
    (((ceilHalf n - 1 : ℕ) : ENNReal) *
        ((n * (n - 1) : ℕ) : ENNReal)⁻¹) ≤
      Probability.ProbHitWithin
        (PEMProtocol n trank Rmax Emax Dmax hn0) hn2 C
        (fun D => InSswap D ∧ MedianAnswerCorrect D) 1 := by
  classical
  let P := PEMProtocol n trank Rmax Emax Dmax hn0
  let lowerSet : Finset (Fin n) :=
    Finset.univ.filter fun v : Fin n => (C v).1.rank.val < (C μ).1.rank.val
  let S : Finset (Fin n × Fin n) := lowerSet.image fun v => (μ, v)
  have hμ_rank : (C μ).1.rank.val = ceilHalf n - 1 := by omega
  have hcardLower : lowerSet.card = ceilHalf n - 1 := by
    have hk : (C μ).1.rank.val ≤ n := Nat.le_of_lt (C μ).1.rank.isLt
    have hcard := generic_card_filter_rank_lt hC.toInSrank (k := (C μ).1.rank.val) hk
    simpa [lowerSet, hμ_rank] using hcard
  have hS_card : S.card = ceilHalf n - 1 := by
    dsimp [S]
    rw [Finset.card_image_of_injective]
    · exact hcardLower
    · intro a b h
      exact congrArg Prod.snd h
  have hS_sub : S ⊆ Probability.OffDiagonalPairs n := by
    intro p hp
    dsimp [S] at hp
    rw [Finset.mem_image] at hp
    rcases hp with ⟨v, hv, hpv⟩
    rw [Probability.mem_offDiagonalPairs]
    rw [← hpv]
    intro hμv
    have hv_lt : (C v).1.rank.val < (C μ).1.rank.val :=
      (Finset.mem_filter.mp hv).2
    have hμ_eq_v : μ = v := by
      simpa using hμv
    subst v
    exact (Nat.lt_irrefl (C μ).1.rank.val) hv_lt
  have hstep : ∀ p ∈ S,
      InSswap (C.step P p.1 p.2) ∧ MedianAnswerCorrect (C.step P p.1 p.2) := by
    intro p hp
    dsimp [S] at hp
    rw [Finset.mem_image] at hp
    rcases hp with ⟨v, hv, hpv⟩
    rw [← hpv]
    have hv_lt_val : (C v).1.rank.val < (C μ).1.rank.val :=
      (Finset.mem_filter.mp hv).2
    have hμv : μ ≠ v := by
      intro h
      subst v
      exact (Nat.lt_irrefl (C μ).1.rank.val) hv_lt_val
    have hv_no_med : (C v).1.rank.val + 1 ≠ ceilHalf n := by
      omega
    have hv_no_max : (C v).1.rank.val + 1 ≠ n := by
      have hv_lt_ceil : (C v).1.rank.val + 1 < ceilHalf n := by omega
      omega
    have h_rank_gt : (C v).1.rank < (C μ).1.rank := by
      exact_mod_cast hv_lt_val
    have hRankFix := rankDeltaOSSR_satisfies_fix
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn0)
    have hSwap' : InSswap (C.step P μ v) := by
      simpa [P, PEMProtocol] using
        (step_at_median_no_swap_odd_preserves_InSswap
          (n := n) (trank := trank) (Rmax := Rmax)
          (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
          hRankFix hC hμv hpar hμ_med hv_no_med hv_no_max
          h_rank_gt h_timer)
    have hC'_eq :
        C.step P μ v =
          fun w =>
            if w = μ then
              ({(C μ).1 with answer := opinionToAnswer (C μ).2}, (C μ).2)
            else if w = v then
              ((C v).1, (C v).2)
            else C w := by
      simpa [P, PEMProtocol] using
        (step_at_median_no_swap_odd_v_not_max
          (n := n) (trank := trank) (Rmax := Rmax)
          (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
          hRankFix hμv (hC.allSettled μ) (hC.allSettled v) hpar
          hμ_med hv_no_med hv_no_max h_rank_gt h_timer)
    have hmaj :
        majorityAnswer (C.step P μ v) = majorityAnswer C := by
      simpa [P, PEMProtocol] using
        (majorityAnswer_step_eq
          (trank := trank) (Rmax := Rmax)
          (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0) C μ v)
    have hμ_correct :
        (C.step P μ v μ).1.answer = majorityAnswer (C.step P μ v) := by
      rw [hmaj, hC'_eq]
      simp [opinionToAnswer_median_eq_majorityAnswer_odd hC hμ_med hpar]
    have hμ_med' :
        (C.step P μ v μ).1.rank.val + 1 = ceilHalf n := by
      rw [hC'_eq]
      simp [hμ_med]
    refine ⟨hSwap', ?_⟩
    intro η hη
    have hημ : η = μ := by
      apply hSwap'.ranks_inj
      apply Fin.eq_of_val_eq
      have hη_med' :
          (C.step P μ v η).1.rank.val + 1 = ceilHalf n := by
        simpa using hη
      have hηval :
          (C.step P μ v η).1.rank.val = ceilHalf n - 1 := by omega
      have hμval :
          (C.step P μ v μ).1.rank.val = ceilHalf n - 1 := by omega
      exact hηval.trans hμval.symm
    subst η
    exact hμ_correct
  have hmass :
      Probability.pairSetMass n hn2 S =
        (((ceilHalf n - 1 : ℕ) : ENNReal) *
          ((n * (n - 1) : ℕ) : ENNReal)⁻¹) := by
    rw [Probability.pairSetMass_eq_card_mul_inv_of_subset n hn2 S hS_sub,
      hS_card]
  calc
    (((ceilHalf n - 1 : ℕ) : ENNReal) *
        ((n * (n - 1) : ℕ) : ENNReal)⁻¹)
        = Probability.pairSetMass n hn2 S := hmass.symm
    _ ≤ Probability.ProbHitWithin P hn2 C
        (fun D => InSswap D ∧ MedianAnswerCorrect D) 1 :=
          Probability.ProbHitWithin_one_lower_bound_of_pairSet
            P hn2 C
            (fun D => InSswap D ∧ MedianAnswerCorrect D)
            (by
              intro hGoal
              exact h_μ_wrong (hGoal.2 μ hμ_med))
            S hS_sub hstep

theorem generic_PEM_median_wrong_to_MedianAnswerCorrect_prob_lower_bound
    (hn2 : 2 ≤ n) (hn0 : 0 < n) (hn4 : 4 ≤ n)
    {C : Config (AgentState n) Opinion n} (hC : InSswap C)
    (h_med_timer : MedianTimerAtLeast 1 C)
    (h_med_wrong : ∃ μ : Fin n, (C μ).1.rank.val + 1 = ceilHalf n ∧
      (C μ).1.answer ≠ majorityAnswer C) :
    ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ≤
      Probability.ProbHitWithin
        (PEMProtocol n trank Rmax Emax Dmax hn0) hn2 C
        (fun D => InSswap D ∧ MedianAnswerCorrect D) 1 := by
  by_cases hpar : n % 2 = 0
  · exact generic_PEM_even_median_wrong_to_MedianAnswerCorrect_prob_lower_bound
      (trank := trank) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      hn2 hn0 hn4 hC hpar h_med_wrong
  · obtain ⟨μ, hμ_med, hμ_wrong⟩ := h_med_wrong
    have hodd :=
      generic_PEM_odd_median_wrong_to_MedianAnswerCorrect_prob_lower_bound
        (trank := trank) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        hn2 hn0 hC hpar hμ_med (h_med_timer μ hμ_med) hμ_wrong
    have hcoef : (1 : ENNReal) ≤ ((ceilHalf n - 1 : ℕ) : ENNReal) := by
      have hnat : 1 ≤ ceilHalf n - 1 := by
        unfold ceilHalf
        omega
      exact_mod_cast hnat
    calc
      ((n * (n - 1) : ℕ) : ENNReal)⁻¹
          = (1 : ENNReal) *
              ((n * (n - 1) : ℕ) : ENNReal)⁻¹ := by simp
      _ ≤ ((ceilHalf n - 1 : ℕ) : ENNReal) *
          ((n * (n - 1) : ℕ) : ENNReal)⁻¹ := by
            exact mul_le_mul_left hcoef _
      _ ≤ Probability.ProbHitWithin
          (PEMProtocol n trank Rmax Emax Dmax hn0) hn2 C
          (fun D => InSswap D ∧ MedianAnswerCorrect D) 1 := hodd

theorem generic_PEM_expected_Tswap_to_MedianAnswerCorrect_or_exit_le
    (hn2 : 2 ≤ n) (hn0 : 0 < n) (hn4 : 4 ≤ n)
    {C : Config (AgentState n) Opinion n}
    (hC : InSswap C)
    (h_med_timer : MedianTimerAtLeast 1 C)
    (h_not_dec : ¬ MedianAnswerCorrect C) :
    Probability.expectedHittingTime
      (PEMProtocol n trank Rmax Emax Dmax hn0) hn2 C
      (fun D =>
        (InSswap D ∧ MedianAnswerCorrect D) ∨
          ¬ (InSswap D ∧ MedianTimerAtLeast 1 D)) ≤
      (((n * (n - 1) : ℕ) : ENNReal)⁻¹)⁻¹ := by
  classical
  let P := PEMProtocol n trank Rmax Emax Dmax hn0
  apply Probability.expectedHittingTime_le_inv_of_local_one_lower_bound
    (P := P) (hn := hn2) (C₀ := C)
    (Region := fun D => InSswap D ∧ MedianTimerAtLeast 1 D)
    (Goal := fun D => InSswap D ∧ MedianAnswerCorrect D)
    (p := ((n * (n - 1) : ℕ) : ENNReal)⁻¹)
  · exact ⟨hC, h_med_timer⟩
  · intro hGoal
    exact h_not_dec hGoal.2
  · intro D hRegionD hGoalD
    have h_med_wrong :
        ∃ μ : Fin n, (D μ).1.rank.val + 1 = ceilHalf n ∧
          (D μ).1.answer ≠ majorityAnswer D := by
      rw [← not_MedianAnswerCorrect_iff_exists_median_wrong]
      intro hDec
      exact hGoalD ⟨hRegionD.1, hDec⟩
    have hbase :
        ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ≤
          Probability.ProbHitWithin P hn2 D
            (fun E => InSswap E ∧ MedianAnswerCorrect E) 1 := by
      simpa [P] using
        (generic_PEM_median_wrong_to_MedianAnswerCorrect_prob_lower_bound
          (trank := trank) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
          hn2 hn0 hn4 hRegionD.1 hRegionD.2 h_med_wrong)
    have hTargetD :
        ¬ ((fun E =>
          (InSswap E ∧ MedianAnswerCorrect E) ∨
            ¬ (InSswap E ∧ MedianTimerAtLeast 1 E)) D) := by
      intro hTarget
      rcases hTarget with hGoal | hExit
      · exact hGoalD hGoal
      · exact hExit hRegionD
    have hmono :
        Probability.ProbHitWithin P hn2 D
            (fun E => InSswap E ∧ MedianAnswerCorrect E) 1 ≤
          Probability.ProbHitWithin P hn2 D
            (fun E =>
              (InSswap E ∧ MedianAnswerCorrect E) ∨
                ¬ (InSswap E ∧ MedianTimerAtLeast 1 E)) 1 :=
      Probability.ProbHitWithin_one_mono_goal
        (P := P) (hn := hn2) (C₀ := D)
        (Goal₁ := fun E => InSswap E ∧ MedianAnswerCorrect E)
        (Goal₂ := fun E =>
          (InSswap E ∧ MedianAnswerCorrect E) ∨
            ¬ (InSswap E ∧ MedianTimerAtLeast 1 E))
        hGoalD hTargetD (fun E h => Or.inl h)
    exact le_trans hbase hmono

theorem generic_decision_window
    (hn4 : 4 ≤ n) (hn0 : 0 < n)
    (C : Config (AgentState n) Opinion n) (hC : InSswap C)
    (hT : MedianTimerAtLeast 1 C) (hND : ¬ MedianAnswerCorrect C) :
    ((2 : ENNReal)⁻¹) ≤
      Probability.ProbHitWithin (PEMProtocol n trank Rmax Emax Dmax hn0)
        (by omega : 2 ≤ n) C
        (fun D => (InSswap D ∧ MedianAnswerCorrect D) ∨
          ¬ (InSswap D ∧ MedianTimerAtLeast 1 D))
        (2 * (n * (n - 1))) := by
  have hM := generic_PEM_expected_Tswap_to_MedianAnswerCorrect_or_exit_le
    (trank := trank) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
    (by omega : 2 ≤ n) hn0 hn4 hC hT hND
  rw [inv_inv] at hM
  exact Probability.ProbHitWithin_ge_half_of_expectedHittingTime_le
    (PEMProtocol n trank Rmax Emax Dmax hn0) (by omega : 2 ≤ n) C _ hM (by omega)

end DecisionWindow

section GenericDecisionTiming

variable {n trank Rmax Emax Dmax : ℕ}

private theorem generic_ennreal_inv_two_eq_inv_four_add_inv_four :
    ((2 : ENNReal)⁻¹) = ((4 : ENNReal)⁻¹) + ((4 : ENNReal)⁻¹) := by
  have h2 : ((2 : ENNReal)⁻¹) ≠ ⊤ := by
    rw [ENNReal.inv_ne_top]
    norm_num
  have h4 : ((4 : ENNReal)⁻¹) ≠ ⊤ := by
    rw [ENNReal.inv_ne_top]
    norm_num
  have hsum : ((4 : ENNReal)⁻¹ + (4 : ENNReal)⁻¹) ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨h4, h4⟩
  rw [← ENNReal.toReal_eq_toReal_iff' h2 hsum]
  rw [ENNReal.toReal_add h4 h4]
  simp [ENNReal.toReal_inv]
  norm_num

private theorem generic_ProbHitWithin_left_ge_inv4_of_or_ge_half_and_right_le_inv4
    {n : ℕ} (P : Protocol (AgentState n) Opinion Output) (hn : 2 ≤ n)
    (C₀ : Config (AgentState n) Opinion n)
    (A B : Config (AgentState n) Opinion n → Prop)
    [DecidablePred A] [DecidablePred B] (t : ℕ)
    (hor : ((2 : ENNReal)⁻¹) ≤
      Probability.ProbHitWithin P hn C₀ (fun C => A C ∨ B C) t)
    (hB : Probability.ProbHitWithin P hn C₀ B t ≤ (4 : ENNReal)⁻¹) :
    ((4 : ENNReal)⁻¹) ≤ Probability.ProbHitWithin P hn C₀ A t := by
  let x := Probability.ProbHitWithin P hn C₀ A t
  let y := Probability.ProbHitWithin P hn C₀ B t
  have hOr :
      Probability.ProbHitWithin P hn C₀ (fun C => A C ∨ B C) t ≤ x + y := by
    simpa [x, y] using Probability.ProbHitWithin_union_le P hn C₀ A B t
  have hhalf_le : ((2 : ENNReal)⁻¹) ≤ x + (4 : ENNReal)⁻¹ := by
    calc
      ((2 : ENNReal)⁻¹)
          ≤ Probability.ProbHitWithin P hn C₀ (fun C => A C ∨ B C) t := hor
      _ ≤ x + y := hOr
      _ ≤ x + (4 : ENNReal)⁻¹ := by
        exact add_le_add_right (show y ≤ (4 : ENNReal)⁻¹ from hB) x
  have hquarter_ne_top : ((4 : ENNReal)⁻¹) ≠ ⊤ := by
    rw [ENNReal.inv_ne_top]
    norm_num
  rw [generic_ennreal_inv_two_eq_inv_four_add_inv_four] at hhalf_le
  rw [add_comm x ((4 : ENNReal)⁻¹)] at hhalf_le
  exact (ENNReal.add_le_add_iff_left hquarter_ne_top).mp hhalf_le

theorem generic_decision_before_timer_zero_of_exit_le_quarter
    (hn4 : 4 ≤ n) (hn0 : 0 < n)
    (C : Config (AgentState n) Opinion n)
    (hS : InSswap C) (hT : MedianTimerAtLeast 1 C)
    (hExit :
      Probability.ProbHitWithin
        (PEMProtocol n trank Rmax Emax Dmax hn0)
        (by omega : 2 ≤ n) C
        (fun D => ¬ (InSswap D ∧ MedianTimerAtLeast 1 D))
        (decisionWindow n) ≤ (4 : ENNReal)⁻¹) :
    (4 : ENNReal)⁻¹ ≤
      Probability.ProbHitWithin
        (PEMProtocol n trank Rmax Emax Dmax hn0)
        (by omega : 2 ≤ n) C
        (DecisionProductiveTarget : Config (AgentState n) Opinion n → Prop)
        (decisionWindow n) := by
  classical
  let P := PEMProtocol n trank Rmax Emax Dmax hn0
  let LiveDecision : Config (AgentState n) Opinion n → Prop :=
    fun D => InSswap D ∧ MedianAnswerCorrect D ∧ MedianTimerAtLeast 1 D
  let Exit : Config (AgentState n) Opinion n → Prop :=
    fun D => ¬ (InSswap D ∧ MedianTimerAtLeast 1 D)
  have hn2 : 2 ≤ n := by omega
  by_cases hMAC : MedianAnswerCorrect C
  · have hGoal : DecisionProductiveTarget C := Or.inl ⟨hS, hMAC, hT⟩
    have hZero :
        Probability.ProbHitWithin P hn2 C
          (DecisionProductiveTarget : Config (AgentState n) Opinion n → Prop)
          0 = 1 := by
      exact Probability.probHitBy_zero_of_goal P hn2 C
        (DecisionProductiveTarget : Config (AgentState n) Opinion n → Prop) hGoal
    have hOne :
        (1 : ENNReal) ≤
          Probability.ProbHitWithin P hn2 C
            (DecisionProductiveTarget : Config (AgentState n) Opinion n → Prop)
            (decisionWindow n) := by
      rw [← hZero]
      exact Probability.ProbHitWithin_mono_time P hn2 C
        (DecisionProductiveTarget : Config (AgentState n) Opinion n → Prop)
        (Nat.zero_le _)
    exact le_trans (by norm_num : ((4 : ENNReal)⁻¹) ≤ 1) hOne
  · have hGoalEq :
        (fun D : Config (AgentState n) Opinion n =>
            (InSswap D ∧ MedianAnswerCorrect D) ∨ Exit D) =
          (fun D => LiveDecision D ∨ Exit D) := by
      funext D
      apply propext
      constructor
      · intro h
        rcases h with hdec | hexit
        · by_cases htimer : MedianTimerAtLeast 1 D
          · exact Or.inl ⟨hdec.1, hdec.2, htimer⟩
          · exact Or.inr (fun hLive => htimer hLive.2)
        · exact Or.inr hexit
      · intro h
        rcases h with hdec | hexit
        · exact Or.inl ⟨hdec.1, hdec.2.1⟩
        · exact Or.inr hexit
    have hor :
        ((2 : ENNReal)⁻¹) ≤
          Probability.ProbHitWithin P hn2 C
            (fun D => (InSswap D ∧ MedianAnswerCorrect D) ∨ Exit D)
            (decisionWindow n) := by
      simpa [P, Exit, decisionWindow, Nat.mul_assoc] using
        (generic_decision_window
          (n := n) (trank := trank) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
          hn4 hn0 C hS hT hMAC)
    have hDecision :
        ((4 : ENNReal)⁻¹) ≤
          Probability.ProbHitWithin P hn2 C LiveDecision (decisionWindow n) :=
      generic_ProbHitWithin_left_ge_inv4_of_or_ge_half_and_right_le_inv4
        P hn2 C LiveDecision Exit (decisionWindow n)
        (by simpa [hGoalEq] using hor)
        (by simpa [P, Exit] using hExit)
    exact hDecision.trans
      (Probability.ProbHitWithin_mono_goal P hn2 C
        LiveDecision
        (DecisionProductiveTarget : Config (AgentState n) Opinion n → Prop)
        (fun D hD => Or.inl hD) (decisionWindow n))

theorem generic_decision_before_timer_zero
    [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n)
    (hRmax : n ≤ Rmax) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (C : Config (AgentState n) Opinion n)
    (hS : InSswap C) (hT : MedianTimerAtLeast 35 C) :
    (4 : ENNReal)⁻¹ ≤
      Probability.ProbHitWithin
        (PEMProtocol n trank Rmax Emax Dmax hn0)
        (by omega : 2 ≤ n) C
        (DecisionProductiveTarget : Config (AgentState n) Opinion n → Prop)
        (decisionWindow n) := by
  classical
  let P := PEMProtocol n trank Rmax Emax Dmax hn0
  let Bad : Config (AgentState n) Opinion n → Prop :=
    fun D => ¬ InSrank D ∨ ¬ MedianTimerAtLeast 1 D
  have hn2 : 2 ≤ n := by omega
  have hT1 : MedianTimerAtLeast 1 C :=
    MedianTimerAtLeast.mono (n := n) (a := 1) (b := 35) (by norm_num) hT
  have hBadBig :
      Probability.ProbHitWithin P hn2 C Bad
          (4 * n * (n - 1)) ≤ (4 : ENNReal)⁻¹ := by
    simpa [P, Bad] using
      (generic_PEM_srank_or_timer_failure_prob_le_quarter_short35
        (n := n) (trank := trank) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        hn4 hn0 hRmax hEmax hDmax C hS.toInSrank hT)
  have hBadSmall :
      Probability.ProbHitWithin P hn2 C Bad
          (decisionWindow n) ≤ (4 : ENNReal)⁻¹ := by
    exact
      (Probability.ProbHitWithin_mono_time P hn2 C Bad
        (by
          dsimp [decisionWindow]
          nlinarith [Nat.zero_le (n * (n - 1))])).trans hBadBig
  have hExitSmall :
      Probability.ProbHitWithin P hn2 C
          (fun D => ¬ (InSswap D ∧ MedianTimerAtLeast 1 D))
          (decisionWindow n) ≤ (4 : ENNReal)⁻¹ := by
    exact
      (generic_live_exit_ProbHitWithin_le_bad
        (trank := trank) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        hn0 hn2 C ⟨hS, hT1⟩ (decisionWindow n)).trans
        (by simpa [P, Bad] using hBadSmall)
  exact
    generic_decision_before_timer_zero_of_exit_le_quarter
      (trank := trank) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      hn4 hn0 C hS hT1 hExitSmall

end GenericDecisionTiming

section GenericTimerDrain

variable {n trank Rmax Emax Dmax : ℕ}

theorem generic_timer_ge_two_descent_step
    (hn4 : 4 ≤ n) [Inhabited (Fin n × Fin n)] (hn0 : 0 < n)
    (hRmax : n ≤ Rmax)
    {D : Config (AgentState n) Opinion n}
    (hS : InSswap D) (hM : MedianAnswerCorrect D) (hT : MedianTimerAtLeast 1 D)
    {μ v : Fin n}
    (hμ_med : (D μ).1.rank.val + 1 = ceilHalf n)
    (hv_max : (D v).1.rank.val + 1 = n)
    (huv : μ ≠ v)
    (hTimer2 : 2 ≤ (D μ).1.timer) :
    let P := PEMProtocol n trank Rmax Emax Dmax hn0
    let Goal := fun D' : Config (AgentState n) Opinion n =>
      IsConsensusConfig D' ∨ CorrectResetSeed D' ∨
        ¬ (InSswap D' ∧ MedianTimerAtLeast 1 D')
    let Inv := fun D' : Config (AgentState n) Opinion n =>
      InSswap D' ∧ MedianAnswerCorrect D' ∧ MedianTimerAtLeast 1 D'
    ((Inv (D.step P μ v) ∧ maxMedianTimer (D.step P μ v) < maxMedianTimer D) ∨
      Goal (D.step P μ v)) := by
  let Pg := PEMProtocol n trank Rmax Emax Dmax hn0
  let Pc := PEMProtocolCoupled n Rmax Emax Dmax hn0
  have hEq : D.step Pg μ v = D.step Pc μ v :=
    generic_step_eq_coupled_of_InSrank
      (trank := trank) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      hn0 hS.toInSrank μ v
  have hCoupled :=
    timer_ge_two_descent_step
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      hn4 hn0 hRmax hS hM hT hμ_med hv_max huv hTimer2
  simpa [Pg, Pc, hEq] using hCoupled

theorem generic_PEM_expected_timer_drain_poly
    [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n) (hRmax : n ≤ Rmax)
    (T_timer : ℕ)
    (C : Config (AgentState n) Opinion n)
    (hSswap : InSswap C)
    (hMedCorrect : MedianAnswerCorrect C)
    (hTimerLo : MedianTimerAtLeast 1 C)
    (hTimerHi : IsTimerBoundedConfig T_timer C) :
    Probability.expectedHittingTime
      (PEMProtocol n trank Rmax Emax Dmax hn0)
      (by omega : 2 ≤ n) C
      (fun D => IsConsensusConfig D ∨ CorrectResetSeed D ∨
        ¬ (InSswap D ∧ MedianTimerAtLeast 1 D)) ≤
      ((T_timer * n * (n - 1) : ℕ) : ENNReal) := by
  classical
  let P := PEMProtocol n trank Rmax Emax Dmax hn0
  let Pc := PEMProtocolCoupled n Rmax Emax Dmax hn0
  let Goal : Config (AgentState n) Opinion n → Prop :=
    fun D => IsConsensusConfig D ∨ CorrectResetSeed D ∨
      ¬ (InSswap D ∧ MedianTimerAtLeast 1 D)
  have hn2 : 2 ≤ n := by omega
  have hstep :
      ∀ D : Config (AgentState n) Opinion n, ¬ Goal D →
        ∀ i j : Fin n, D.step P i j = D.step Pc i j := by
    intro D hD i j
    have hLive : InSswap D ∧ MedianTimerAtLeast 1 D := by
      by_contra hNotLive
      exact hD (Or.inr (Or.inr hNotLive))
    exact
      generic_step_eq_coupled_of_InSrank
        (trank := trank) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        hn0 hLive.1.toInSrank i j
  have hEq :
      Probability.expectedHittingTime P hn2 C Goal =
        Probability.expectedHittingTime Pc hn2 C Goal :=
    generic_expectedHittingTime_eq_of_step_eq_until
      (n := n) (trank := trank) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      hn2 hn0 Goal hstep C
  have hCoupled :
      Probability.expectedHittingTime Pc hn2 C Goal ≤
        ((T_timer * n * (n - 1) : ℕ) : ENNReal) := by
    simpa [Pc, Goal] using
      (PEM_expected_timer_drain_poly
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        hn4 hn0 hRmax T_timer C hSswap hMedCorrect hTimerLo hTimerHi)
  simpa [P, Goal] using (le_of_eq_of_le hEq hCoupled)

theorem generic_timer_drain_window
    [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n) (hRmax : n ≤ Rmax)
    (T_timer : ℕ)
    (C : Config (AgentState n) Opinion n) (hC : InSswap C)
    (hMAC : MedianAnswerCorrect C) (hTLo : MedianTimerAtLeast 1 C)
    (hTHi : IsTimerBoundedConfig T_timer C) :
    ((2 : ENNReal)⁻¹) ≤
      Probability.ProbHitWithin (PEMProtocol n trank Rmax Emax Dmax hn0)
        (by omega : 2 ≤ n) C
        (fun D => IsConsensusConfig D ∨ CorrectResetSeed D ∨
          ¬ (InSswap D ∧ MedianTimerAtLeast 1 D))
        (2 * (T_timer * n * (n - 1))) :=
  Probability.ProbHitWithin_ge_half_of_expectedHittingTime_le
    (PEMProtocol n trank Rmax Emax Dmax hn0) (by omega : 2 ≤ n) C _
    (generic_PEM_expected_timer_drain_poly
      (trank := trank) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      hn4 hn0 hRmax T_timer C hC hMAC hTLo hTHi)
    (by omega)

set_option maxHeartbeats 16000000 in
theorem generic_timer_drain_to_zero_productive
    [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n) (hRmax : n ≤ Rmax)
    (T_timer : ℕ)
    (C : Config (AgentState n) Opinion n)
    (hSswap : InSswap C)
    (hMedCorrect : MedianAnswerCorrect C)
    (hTimerLo : MedianTimerAtLeast 1 C)
    (hTimerHi : IsTimerBoundedConfig T_timer C) :
    Probability.expectedHittingTime
      (PEMProtocol n trank Rmax Emax Dmax hn0)
      (by omega : 2 ≤ n) C
      (fun D => IsConsensusConfig D ∨ CorrectResetSeed D ∨
        (InSswap D ∧ MedianAnswerCorrect D ∧ maxMedianTimer D = 0)) ≤
      ((T_timer * n * (n - 1) : ℕ) : ENNReal) := by
  classical
  set P := PEMProtocol n trank Rmax Emax Dmax hn0
  set Goal := fun D : Config (AgentState n) Opinion n =>
    IsConsensusConfig D ∨ CorrectResetSeed D ∨
      (InSswap D ∧ MedianAnswerCorrect D ∧ maxMedianTimer D = 0)
  set Inv := fun D : Config (AgentState n) Opinion n =>
    InSswap D ∧ MedianAnswerCorrect D ∧ MedianTimerAtLeast 1 D
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
    · have hrank_eq : (D μ).1.rank = (D ν).1.rank := by
        apply Fin.ext
        have h1 : (D μ).1.rank.val + 1 = ceilHalf n := hμ_med
        have h2 : (D ν).1.rank.val + 1 = ceilHalf n := hν_med
        omega
      have hμν : μ = ν := hSD.toInSrank.ranks_inj hrank_eq
      rw [hμν, hν0]
    · exact Nat.zero_le 0
  have hBridge :
      Probability.expectedHittingTime P (by omega : 2 ≤ n) C Goal ≤
        ↑(maxMedianTimer C) * ((n * (n - 1) : ℕ) : ENNReal) := by
    refine Probability.expectedHittingTime_le_of_deterministic_descent
      P (by omega : 2 ≤ n) C Goal Inv maxMedianTimer
      ⟨hSswap, hMedCorrect, hTimerLo⟩ ?_ ?_ ?_ ?_
    ·
        intro D ⟨hSwap_D, hM_D, _hT_D⟩ h0
        exact Or.inr (Or.inr ⟨hSwap_D, hM_D, h0⟩)
    ·
        intro D ⟨hS, hM, hT⟩ _hG i j
        by_cases hS' : InSswap (D.step P i j)
        · have hM' : MedianAnswerCorrect (D.step P i j) :=
            generic_step_median_answer_of_InSswap_both
              (trank := trank) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
              hn0 hn4 hS hS' hM
          by_cases hT' : MedianTimerAtLeast 1 (D.step P i j)
          · exact Or.inl ⟨hS', hM', hT'⟩
          · exact Or.inr (Or.inr (Or.inr ⟨hS', hM', hmax_zero_of_not_live _ hS' hT'⟩))
        · exact Or.inr (Or.inr (Or.inl
            (generic_crs_of_InSswap_break_with_MedC
              (trank := trank) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
              hn4 hn0 hRmax hS hM hS')))
    ·
        intro D ⟨hS, _hM, _hT⟩ _hG i j
        unfold maxMedianTimer
        apply Finset.sup_le
        intro μ _
        split_ifs with hμ_med
        · by_cases hij : i = j
          · subst hij
            simp only [Config.step, ite_true] at hμ_med ⊢
            exact Finset.le_sup_of_le (Finset.mem_univ μ) (by simp [hμ_med])
          · by_cases hμi : μ = i
            · rw [hμi]
              have hrank : (D.step P i j i).1.rank = (D i).1.rank :=
                generic_step_rank_preserved_of_InSswap
                  (trank := trank) (Rmax := Rmax) (Emax := Emax)
                  (Dmax := Dmax) hn0 hS i
              have hμ_pre : (D i).1.rank.val + 1 = ceilHalf n := by
                rw [← hrank]; rwa [hμi] at hμ_med
              calc (D.step P i j i).1.timer
                  ≤ (D i).1.timer :=
                    generic_step_timer_le_of_InSswap
                      (trank := trank) (Rmax := Rmax) (Emax := Emax)
                      (Dmax := Dmax) hn0 hS i
                _ ≤ maxMedianTimer D :=
                    Finset.le_sup_of_le (Finset.mem_univ i) (by simp [maxMedianTimer, hμ_pre])
            · by_cases hμj : μ = j
              · rw [hμj]
                have hrank : (D.step P i j j).1.rank = (D j).1.rank :=
                  generic_step_rank_preserved_of_InSswap
                    (trank := trank) (Rmax := Rmax) (Emax := Emax)
                    (Dmax := Dmax) hn0 hS j
                have hμ_pre : (D j).1.rank.val + 1 = ceilHalf n := by
                  rw [← hrank]; rwa [hμj] at hμ_med
                calc (D.step P i j j).1.timer
                    ≤ (D j).1.timer :=
                      generic_step_timer_le_of_InSswap
                        (trank := trank) (Rmax := Rmax) (Emax := Emax)
                        (Dmax := Dmax) hn0 hS j
                  _ ≤ maxMedianTimer D :=
                      Finset.le_sup_of_le (Finset.mem_univ j) (by simp [maxMedianTimer, hμ_pre])
              · have hbyst : D.step P i j μ = D μ := by
                  unfold Config.step
                  simp [P, hij, hμi, hμj]
                rw [show (D.step P i j μ).1.timer = (D μ).1.timer from
                  congrArg (fun x => x.1.timer) hbyst]
                rw [show (D.step P i j μ).1.rank = (D μ).1.rank from
                  congrArg (fun x => x.1.rank) hbyst] at hμ_med
                exact Finset.le_sup_of_le (Finset.mem_univ μ) (by simp [hμ_med])
        · exact Nat.zero_le _
    ·
        intro D ⟨hS, hM, hT⟩ _hG _hφ
        have hn_pos : 0 < n := by omega
        obtain ⟨μ, hμ_med⟩ := hS.toInSrank.exists_median hn_pos
        have hsurj : Function.Surjective (fun v => (D v).1.rank) :=
          Finite.injective_iff_surjective.mp hS.toInSrank.ranks_inj
        have hn_bound : n - 1 < n := by omega
        obtain ⟨v, hv_eq⟩ := hsurj ⟨n - 1, hn_bound⟩
        have hv_max : (D v).1.rank.val + 1 = n := by
          have h := congrArg Fin.val hv_eq
          simp only [Fin.val_mk] at h
          omega
        have huv : μ ≠ v := by
          intro h
          subst h
          have : ceilHalf n = n := by omega
          have : ceilHalf n ≤ (n + 1) / 2 := by
            unfold ceilHalf
            omega
          omega
        refine ⟨μ, v, huv, ?_⟩
        have hTimerPos : 1 ≤ (D μ).1.timer := hT μ hμ_med
        by_cases hTimer2 : 2 ≤ (D μ).1.timer
        · have hstep := generic_timer_ge_two_descent_step
            (trank := trank) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
            hn4 hn0 hRmax hS hM hT hμ_med hv_max huv hTimer2
          simp only [] at hstep
          rcases hstep with hleft | hright
          · exact Or.inl hleft
          · rcases hright with hc | hcrs | hnl
            · exact Or.inr (Or.inl hc)
            · exact Or.inr (Or.inr (Or.inl hcrs))
            · by_cases hS' : InSswap (D.step P μ v)
              · have hM' : MedianAnswerCorrect (D.step P μ v) :=
                  generic_step_median_answer_of_InSswap_both
                    (trank := trank) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
                    hn0 hn4 hS hS' hM
                have hnt : ¬ MedianTimerAtLeast 1 (D.step P μ v) := fun ht => hnl ⟨hS', ht⟩
                exact Or.inr (Or.inr (Or.inr ⟨hS', hM', hmax_zero_of_not_live _ hS' hnt⟩))
              · exact Or.inr (Or.inr (Or.inl
                  (generic_crs_of_InSswap_break_with_MedC
                    (trank := trank) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
                    hn4 hn0 hRmax hS hM hS')))
        · have hTimer1 : (D μ).1.timer = 1 := by omega
          by_cases hv_wrong : (D v).1.answer ≠ majorityAnswer D
          · let Pc := PEMProtocolCoupled n Rmax Emax Dmax hn0
            have hSeedCoupled : CorrectResetSeed (D.step Pc μ v) := by
              simpa [Pc] using
                step_timer_le_one_median_max_creates_CorrectResetSeed
                  (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
                  hn4 hn0 hRmax hS huv hμ_med (by omega) hv_max
                  (hM μ hμ_med) hv_wrong
            have hEqStep : D.step P μ v = D.step Pc μ v := by
              simpa [P, Pc] using
                generic_step_eq_coupled_of_InSrank
                  (trank := trank) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
                  hn0 hS.toInSrank μ v
            exact Or.inr (Or.inr (Or.inl (by rw [hEqStep]; exact hSeedCoupled)))
          · have hv_correct : (D v).1.answer = majorityAnswer D := by
              by_contra h
              exact hv_wrong h
            by_cases hpar : n % 2 = 0
            · have hceil : ceilHalf n = n / 2 := by
                unfold ceilHalf
                omega
              have hμ_lower : (D μ).1.rank.val + 1 = n / 2 := by
                rw [← hceil]
                exact hμ_med
              have h_post_same : (D μ).1.answer = (D v).1.answer := by
                rw [hM μ hμ_med, hv_correct]
              let Pc := PEMProtocolCoupled n Rmax Emax Dmax hn0
              have hclean := insswap_drain_median_timer_one_step
                (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn0)
                hS hn4 huv hpar hμ_lower hv_max hTimer1
                (hS.swap_condition_false μ v) h_post_same
              have hEqStep : D.step P μ v = D.step Pc μ v := by
                simpa [P, Pc] using
                  generic_step_eq_coupled_of_InSrank
                    (trank := trank) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
                    hn0 hS.toInSrank μ v
              have hS' : InSswap (D.step P μ v) := by
                rw [hEqStep]
                simpa [Pc, PEMProtocolCoupled, PEMProtocol] using hclean.1
              have hM' : MedianAnswerCorrect (D.step P μ v) :=
                generic_step_median_answer_of_InSswap_both
                  (trank := trank) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
                  hn0 hn4 hS hS' hM
              have hμ_timer_post : (D.step P μ v μ).1.timer = 0 := by
                rw [hEqStep]
                simpa [Pc, PEMProtocolCoupled, PEMProtocol] using hclean.2.1
              have hμ_rank_post : (D.step P μ v μ).1.rank.val + 1 = ceilHalf n := by
                rw [hEqStep, hceil]
                simpa [Pc, PEMProtocolCoupled, PEMProtocol] using hclean.2.2.2
              refine Or.inr (Or.inr (Or.inr ⟨hS', hM', ?_⟩))
              apply hmax_zero_of_not_live _ hS'
              rw [MedianTimerAtLeast]
              push_neg
              exact ⟨μ, hμ_rank_post, by rw [hμ_timer_post]; norm_num⟩
            · have h_no_swap := hS.swap_condition_false μ v
              have h_post_same : opinionToAnswer (D μ).2 = (D v).1.answer := by
                rw [opinionToAnswer_median_eq_majorityAnswer_odd hS hμ_med hpar,
                  hv_correct]
              have hclean := step_at_median_max_timer_one_no_reset_explicit
                (trank := trank) (Rmax := Rmax)
                (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
                rankDeltaOSSR_satisfies_fix hS hn4 huv hμ_med hv_max hpar
                h_no_swap hTimer1 h_post_same
              have hS' : InSswap (D.step P μ v) := by
                simpa [P, PEMProtocol] using hclean.1
              have hM' : MedianAnswerCorrect (D.step P μ v) :=
                generic_step_median_answer_of_InSswap_both
                  (trank := trank) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
                  hn0 hn4 hS hS' hM
              have hμ_timer_post : (D.step P μ v μ).1.timer = 0 := by
                simpa [P, PEMProtocol] using hclean.2.1
              have hμ_rank_post : (D.step P μ v μ).1.rank.val + 1 = ceilHalf n := by
                simpa [P, PEMProtocol] using hclean.2.2.2.1
              refine Or.inr (Or.inr (Or.inr ⟨hS', hM', ?_⟩))
              apply hmax_zero_of_not_live _ hS'
              rw [MedianTimerAtLeast]
              push_neg
              exact ⟨μ, hμ_rank_post, by rw [hμ_timer_post]; norm_num⟩
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

theorem generic_PEM_expected_reset_trigger_v2
    [Inhabited (Fin n × Fin n)]
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
      (PEMProtocol n trank Rmax Emax Dmax hn0)
      (by omega : 2 ≤ n) C
      (fun D => IsConsensusConfig D ∨ CorrectResetSeed D) ≤
      ((n * (n - 1) : ℕ) : ENNReal) := by
  classical
  set P := PEMProtocol n trank Rmax Emax Dmax hn0
  set Goal := fun D : Config (AgentState n) Opinion n =>
    IsConsensusConfig D ∨ CorrectResetSeed D
  set Inv := fun D : Config (AgentState n) Opinion n =>
    InSswap D ∧ MedianAnswerCorrect D ∧
      (∀ μ : Fin n, (D μ).1.rank.val + 1 = ceilHalf n → (D μ).1.timer = 0)
  refine (Probability.expectedHittingTime_le_inv_of_local_one_lower_bound_until_goal
    P (by omega) C Goal Inv ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ?_ ?_ ?_).trans
    (by rw [inv_inv])
  · exact ⟨hSswap, hMedCorrect, hTimer0⟩
  · intro D ⟨hS, hM, hT⟩ _hGoalD i j
    by_cases hS' : InSswap (D.step P i j)
    · have hM' :=
        generic_step_median_answer_of_InSswap_both
          (trank := trank) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
          hn0 hn4 hS hS' hM
      left
      refine ⟨hS', hM', ?_⟩
      intro μ hμ
      have hrank : (D.step P i j μ).1.rank = (D μ).1.rank :=
        generic_step_rank_preserved_of_InSswap
          (trank := trank) (Rmax := Rmax) (Emax := Emax)
          (Dmax := Dmax) hn0 hS μ
      have hμ_pre : (D μ).1.rank.val + 1 = ceilHalf n := by
        rwa [← show (D.step P i j μ).1.rank.val = (D μ).1.rank.val from
          congrArg Fin.val hrank]
      have h0 := hT μ hμ_pre
      have hle : (D.step P i j μ).1.timer ≤ (D μ).1.timer :=
        generic_step_timer_le_of_InSswap
          (trank := trank) (Rmax := Rmax) (Emax := Emax)
          (Dmax := Dmax) hn0 hS (i := i) (j := j) μ
      omega
    · exact Or.inr (Or.inr
        (generic_crs_of_InSswap_break_with_MedC
          (trank := trank) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
          hn4 hn0 hRmax hS hM hS'))
  · intro D ⟨hS, hM, hT⟩ hGoalD
    have hNotCons : ¬ IsConsensusConfig D := fun h => hGoalD (Or.inl h)
    have hWrongExists : ∃ v : Fin n, (D v).1.answer ≠ majorityAnswer D := by
      by_contra h
      push_neg at h
      exact hNotCons ⟨hS.allSettled, hS.toInSrank.ranks_inj, hS.input_rank, h⟩
    obtain ⟨μ, hμ_med⟩ := hS.toInSrank.exists_median (by omega : 0 < n)
    have hμ_correct : (D μ).1.answer = majorityAnswer D := hM μ hμ_med
    have hμ_timer : (D μ).1.timer = 0 := hT μ hμ_med
    by_cases hNonUpper : ∃ v : Fin n, (D v).1.answer ≠ majorityAnswer D ∧
        (D v).1.rank.val + 1 ≠ n / 2 + 1
    · obtain ⟨v, hv_wrong, hv_no_upper⟩ := hNonUpper
      have hμv : μ ≠ v := fun h => by
        subst h
        exact hv_wrong hμ_correct
      apply Probability.ProbHitWithin_one_lower_bound_of_step P (by omega) D Goal
        (fun h => hGoalD h) hμv
      let Pc := PEMProtocolCoupled n Rmax Emax Dmax hn0
      have hSeedCoupled : CorrectResetSeed (D.step Pc μ v) := by
        simpa [Pc] using
          step_timer_zero_median_wrong_nonupper_creates_CorrectResetSeed
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
            hn4 hn0 hRmax hS hμv hμ_med hμ_timer hμ_correct
            hv_wrong hv_no_upper
      have hEqStep : D.step P μ v = D.step Pc μ v := by
        simpa [P, Pc] using
          generic_step_eq_coupled_of_InSrank
            (trank := trank) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
            hn0 hS.toInSrank μ v
      exact Or.inr (by rw [hEqStep]; exact hSeedCoupled)
    · push_neg at hNonUpper
      obtain ⟨v, hv_wrong⟩ := hWrongExists
      have hμv : μ ≠ v := fun h => by
        subst h
        exact hv_wrong hμ_correct
      apply Probability.ProbHitWithin_one_lower_bound_of_step P (by omega) D Goal
        (fun h => hGoalD h) hμv
      have hv_upper : (D v).1.rank.val + 1 = n / 2 + 1 :=
        hNonUpper v hv_wrong
      have hpar : n % 2 = 0 := by
        by_contra h
        push_neg at h
        have hceil : ceilHalf n = n / 2 + 1 := by
          unfold ceilHalf
          omega
        apply hμv
        apply (hS.toInSrank.ranks_inj (Fin.ext ?_)).symm
        show (D v).1.rank.val = (D μ).1.rank.val
        have h1 : (D v).1.rank.val + 1 = (D μ).1.rank.val + 1 := by
          rw [hv_upper, hμ_med, hceil]
        omega
      left
      have hceil : ceilHalf n = n / 2 := by
        unfold ceilHalf
        omega
      have hμ_lower : (D μ).1.rank.val + 1 = n / 2 := by
        rw [← hceil]
        exact hμ_med
      have hsμ : (D μ).1.role = .Settled := hS.allSettled μ
      have hsv : (D v).1.role = .Settled := hS.allSettled v
      have h_maj : majorityAnswer (D.step P μ v) = majorityAnswer D := by
        simpa [P, PEMProtocol] using
          majorityAnswer_step_eq (trank := trank) (Rmax := Rmax)
            (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0) D μ v
      by_cases hxeq : (D μ).2 = (D v).2
      · have hSwap' : InSswap (D.step P μ v) :=
          step_at_median_pair_even_preserves_InSswap
            (trank := trank) (Rmax := Rmax)
            (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
            rankDeltaOSSR_satisfies_fix hS hμv hpar hμ_lower hv_upper hxeq hn4
        have hC'_eq := step_at_median_pair_even_agreed_inputs
            (trank := trank) (Rmax := Rmax)
            (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
            rankDeltaOSSR_satisfies_fix hμv hsμ hsv hpar hμ_lower hv_upper hxeq hn4
        have h_sum := nAOf_add_nBOf D
        have hμ_rank : (D μ).1.rank.val = n / 2 - 1 := by omega
        have hv_rank : (D v).1.rank.val = n / 2 := by omega
        have hne : nAOf D ≠ nBOf D := by
          rcases hx : (D μ).2 with _ | _
          · have hxv : (D v).2 = Opinion.A := by
              rw [← hxeq]
              exact hx
            have h2 : (D v).1.rank.val < nAOf D := (hS.input_rank v).mp hxv
            intro h
            omega
          · have hxv : (D v).2 = Opinion.B := by
              rw [← hxeq]
              exact hx
            have h1 : ¬ ((D μ).1.rank.val < nAOf D) := by
              intro hh
              have := (hS.input_rank μ).mpr hh
              rw [hx] at this
              cases this
            have h2 : ¬ ((D v).1.rank.val < nAOf D) := by
              intro h
              have := (hS.input_rank v).mpr h
              rw [hxv] at this
              cases this
            intro h
            omega
        have h_μ_eq_maj : opinionToAnswer (D μ).2 = majorityAnswer D :=
          opinionToAnswer_lower_median_eq_majorityAnswer_even hS hμ_lower hpar hne
        refine ⟨hSwap'.allSettled, hSwap'.ranks_inj, hSwap'.input_rank, ?_⟩
        intro w
        rw [h_maj]
        have h_step_w : D.step P μ v w = (
            fun w => if w = μ then ({(D μ).1 with answer := opinionToAnswer (D μ).2}, (D μ).2)
                     else if w = v then ({(D v).1 with answer := opinionToAnswer (D μ).2}, (D v).2)
                     else D w) w := by
          rw [hC'_eq]
        by_cases hwμ : w = μ
        · subst hwμ
          rw [h_step_w]
          simp [h_μ_eq_maj]
        · by_cases hwv : w = v
          · subst hwv
            rw [h_step_w]
            simp [hwμ, h_μ_eq_maj]
          · rw [h_step_w]
            simp [hwμ, hwv]
            by_cases hw_ans : (D w).1.answer = majorityAnswer D
            · exact hw_ans
            · exfalso
              apply hwv
              apply hS.toInSrank.ranks_inj
              exact Fin.ext (Nat.add_right_cancel ((hNonUpper w hw_ans).trans hv_upper.symm))
      · have h_no_swap_disagree : ¬ ((D μ).2 = Opinion.B ∧ (D v).2 = Opinion.A) := by
          intro ⟨hxμB, hxvA⟩
          have h1 : ¬ ((D μ).1.rank.val < nAOf D) := by
            intro h
            have := (hS.input_rank μ).mpr h
            rw [hxμB] at this
            cases this
          have h2 : (D v).1.rank.val < nAOf D := (hS.input_rank v).mp hxvA
          have h_sum := nAOf_add_nBOf D
          omega
        have h_step := step_at_median_pair_even_disagreed_inputs
            (trank := trank) (Rmax := Rmax)
            (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
            rankDeltaOSSR_satisfies_fix hμv hsμ hsv hpar hμ_lower hv_upper hxeq
            h_no_swap_disagree hn4
        obtain ⟨h_μ_post, h_v_post, h_others_post, h_inputs_post⟩ := h_step
        have hTie : nAOf D = nBOf D := by
          have h_sum := nAOf_add_nBOf D
          rcases hxμ : (D μ).2 with _ | _
          · have hxvB : (D v).2 = Opinion.B := by
              cases hxv : (D v).2 with
              | A => exfalso; apply hxeq; rw [hxμ, hxv]
              | B => rfl
            have h1 : (D μ).1.rank.val < nAOf D := (hS.input_rank μ).mp hxμ
            have h2 : ¬ ((D v).1.rank.val < nAOf D) := by
              intro h
              have := (hS.input_rank v).mpr h
              rw [hxvB] at this
              cases this
            omega
          · have hxvA : (D v).2 = Opinion.A := by
              cases hxv : (D v).2 with
              | A => rfl
              | B => exfalso; apply hxeq; rw [hxμ, hxv]
            have h1 : ¬ ((D μ).1.rank.val < nAOf D) := by
              intro h
              have := (hS.input_rank μ).mpr h
              rw [hxμ] at this
              cases this
            have h2 : (D v).1.rank.val < nAOf D := (hS.input_rank v).mp hxvA
            omega
        have hMaj_outT : majorityAnswer D = .outT := majorityAnswer_eq_outT_of_tie hTie
        constructor
        · intro w
          by_cases hwμ : w = μ
          · rw [hwμ, h_μ_post]
            exact hsμ
          · by_cases hwv : w = v
            · rw [hwv, h_v_post]
              exact hsv
            · rw [show (D.step P μ v w).1 = (D w).1 from
                congrArg Prod.fst (h_others_post w hwμ hwv)]
              exact hS.allSettled w
        · intro w1 w2 heq
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
        · intro w
          have h_nA : nAOf (D.step P μ v) = nAOf D := by
            unfold nAOf Config.agentsWithInput Config.inputOf
            congr 1
            ext w'
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
        · intro w
          rw [h_maj, hMaj_outT]
          by_cases hwμ : w = μ
          · rw [hwμ]
            show (D.step P μ v μ).1.answer = .outT
            rw [h_μ_post]
          · by_cases hwv : w = v
            · rw [hwv]
              show (D.step P μ v v).1.answer = .outT
              rw [h_v_post]
            · rw [show (D.step P μ v w).1 = (D w).1 from
                congrArg Prod.fst (h_others_post w hwμ hwv)]
              by_cases hw_ans : (D w).1.answer = majorityAnswer D
              · rw [hw_ans, hMaj_outT]
              · exfalso
                apply hwv
                apply hS.toInSrank.ranks_inj
                exact Fin.ext (Nat.add_right_cancel ((hNonUpper w hw_ans).trans hv_upper.symm))

theorem generic_MAClive_to_consensus_or_crs
    [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n)
    (hRmax : n ≤ Rmax) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (T_timer : ℕ)
    (C : Config (AgentState n) Opinion n)
    (hSswap : InSswap C)
    (hMedCorrect : MedianAnswerCorrect C)
    (hTimerLo : MedianTimerAtLeast 1 C)
    (hTimerHi : IsTimerBoundedConfig T_timer C) :
    Probability.expectedHittingTime
      (PEMProtocol n trank Rmax Emax Dmax hn0)
      (by omega : 2 ≤ n) C
      (fun D => IsConsensusConfig D ∨ CorrectResetSeed D) ≤
      ((T_timer * n * (n - 1) + n * (n - 1) : ℕ) : ENNReal) := by
  classical
  set P := PEMProtocol n trank Rmax Emax Dmax hn0 with hP
  have hMid : Probability.expectedHittingTime P (by omega : 2 ≤ n) C
      (fun D => IsConsensusConfig D ∨ CorrectResetSeed D ∨
        (InSswap D ∧ MedianAnswerCorrect D ∧ maxMedianTimer D = 0)) ≤
      ((T_timer * n * (n - 1) : ℕ) : ENNReal) :=
    generic_timer_drain_to_zero_productive
      (trank := trank) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      hn4 hn0 hRmax T_timer C hSswap hMedCorrect hTimerLo hTimerHi
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
    · have hTimer0 : ∀ μ : Fin n, (D μ).1.rank.val + 1 = ceilHalf n →
          (D μ).1.timer = 0 := by
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
      · exact
          generic_PEM_expected_reset_trigger_v2
            (trank := trank) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
            hn4 hn0 hRmax hEmax hDmax D hSD hMD hw hTimer0
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

theorem generic_MAClive_to_consensus_or_crs_window
    [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n)
    (hRmax : n ≤ Rmax) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (T_timer : ℕ)
    (C : Config (AgentState n) Opinion n)
    (hC : InSswap C) (hMAC : MedianAnswerCorrect C)
    (hTLo : MedianTimerAtLeast 1 C)
    (hTHi : IsTimerBoundedConfig T_timer C) :
    ((2 : ENNReal)⁻¹) ≤
      Probability.ProbHitWithin (PEMProtocol n trank Rmax Emax Dmax hn0)
        (by omega : 2 ≤ n) C
        (fun D => IsConsensusConfig D ∨ CorrectResetSeed D)
        (2 * (T_timer * n * (n - 1) + n * (n - 1))) := by
  have hM :=
    generic_MAClive_to_consensus_or_crs
      (trank := trank) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      hn4 hn0 hRmax hEmax hDmax T_timer C hC hMAC hTLo hTHi
  exact Probability.ProbHitWithin_ge_half_of_expectedHittingTime_le
    (PEMProtocol n trank Rmax Emax Dmax hn0) (by omega : 2 ≤ n) C _
    hM
    (by omega)

theorem generic_swap_live_to_cons_or_crs_or_break
    [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n) (hRmax : n ≤ Rmax)
    (T_timer : ℕ)
    (hTimerStep : ∀ D : Config (AgentState n) Opinion n,
      IsTimerBoundedConfig T_timer D → ∀ i j : Fin n,
        IsTimerBoundedConfig T_timer
          (D.step (PEMProtocol n trank Rmax Emax Dmax hn0) i j))
    (C : Config (AgentState n) Opinion n) (hC : InSswap C)
    (hT : MedianTimerAtLeast 1 C) (hB : IsTimerBoundedConfig T_timer C) :
    ((4 : ENNReal)⁻¹) ≤
      Probability.ProbHitWithin (PEMProtocol n trank Rmax Emax Dmax hn0)
        (by omega : 2 ≤ n) C
        (fun D => IsConsensusConfig D ∨ CorrectResetSeed D ∨
          ¬ (InSswap D ∧ MedianTimerAtLeast 1 D))
        (2 * (n * (n - 1)) + 2 * (T_timer * n * (n - 1))) := by
  have hn2 : (2 : ℕ) ≤ n := by omega
  set P := PEMProtocol n trank Rmax Emax Dmax hn0 with hP
  set Inv : Config (AgentState n) Opinion n → Prop :=
    fun D => IsTimerBoundedConfig T_timer D with hInvDef
  set Goal : Config (AgentState n) Opinion n → Prop :=
    fun D => IsConsensusConfig D ∨ CorrectResetSeed D ∨
      ¬ (InSswap D ∧ MedianTimerAtLeast 1 D)
    with hGoalDef
  have hInvStep : ∀ D, Inv D → ∀ i j, Inv (D.step P i j) :=
    fun D hD i j => by
      simpa [P, Inv] using hTimerStep D hD i j
  by_cases hMAC : MedianAnswerCorrect C
  · refine le_trans ?_ (Probability.ProbHitWithin_mono_time P hn2 C Goal
      (m := 2 * (T_timer * n * (n - 1))) (by omega))
    refine le_trans ?_ (generic_timer_drain_window
      (trank := trank) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      hn4 hn0 hRmax T_timer C hC hMAC hT hB)
    rw [ENNReal.inv_le_inv]
    norm_num
  · set dG : Config (AgentState n) Opinion n → Prop :=
      fun D => (InSswap D ∧ MedianAnswerCorrect D) ∨
        ¬ (InSswap D ∧ MedianTimerAtLeast 1 D)
      with hdGDef
    set Mid : Config (AgentState n) Opinion n → Prop :=
      fun D => dG D ∧ Inv D with hMidDef
    have hMid : ((2 : ENNReal)⁻¹) ≤
        Probability.ProbHitWithin P hn2 C Mid (2 * (n * (n - 1))) := by
      rw [hMidDef,
        Probability.ProbHitWithin_eq_and_inv_of_invariant P hn2 C dG Inv hB hInvStep]
      exact
        generic_decision_window
          (trank := trank) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
          hn4 hn0 C hC hT hMAC
    have hGoal : ∀ C' : Config (AgentState n) Opinion n, Mid C' →
        ((2 : ENNReal)⁻¹) ≤
          Probability.ProbHitWithin P hn2 C' Goal (2 * (T_timer * n * (n - 1))) := by
      intro C' hC'
      obtain ⟨hdg, hinv⟩ := hC'
      by_cases hlive : InSswap C' ∧ MedianTimerAtLeast 1 C'
      · have hmac : MedianAnswerCorrect C' := by
          rcases hdg with ⟨_, hm⟩ | hexit
          · exact hm
          · exact absurd hlive hexit
        exact generic_timer_drain_window
          (trank := trank) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
          hn4 hn0 hRmax T_timer C' hlive.1 hmac hlive.2 hinv
      · have hgC' : Goal C' := Or.inr (Or.inr hlive)
        have h1 : (1 : ENNReal) ≤
            Probability.ProbHitWithin P hn2 C' Goal (2 * (T_timer * n * (n - 1))) := by
          calc (1 : ENNReal) = Probability.probReached P hn2 C' Goal 0 :=
                (Probability.probReached_zero_of_goal P hn2 C' Goal hgC').symm
            _ ≤ Probability.ProbHitWithin P hn2 C' Goal 0 :=
                Probability.probReached_le_ProbHitWithin P hn2 C' Goal 0
            _ ≤ Probability.ProbHitWithin P hn2 C' Goal (2 * (T_timer * n * (n - 1))) :=
                Probability.ProbHitWithin_mono_time P hn2 C' Goal (Nat.zero_le _)
        exact le_trans (by norm_num : ((2 : ENNReal)⁻¹) ≤ 1) h1
    have hchain := Probability.ProbHitWithin_add_ge_mul P hn2 C Mid Goal
      (2 * (n * (n - 1))) (2 * (T_timer * n * (n - 1)))
      ((2 : ENNReal)⁻¹) ((2 : ENNReal)⁻¹) hMid hGoal
    have harith : ((2 : ENNReal)⁻¹) * ((2 : ENNReal)⁻¹) = ((4 : ENNReal)⁻¹) := by
      rw [← ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num))]
      norm_num
    rwa [harith] at hchain

end GenericTimerDrain

end SSEM
