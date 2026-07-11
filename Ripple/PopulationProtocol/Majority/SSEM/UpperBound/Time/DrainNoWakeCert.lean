import Ripple.PopulationProtocol.Majority.SSEM.UpperBound.Time.DrainNoWakeProtocol

namespace SSEM

open scoped BigOperators ENNReal

variable {n : ℕ}

/-!
# Wake-load certificate along a no-wake PEM prefix

This file proves the value-side certificate invariant corresponding to the
role-side no-wake witness in `DrainNoWakeProtocol.lean`.

The key additional fact is that, along an all-Resetting pre-state, a selected
endpoint's `delaytimer` is either freshly reset to at least `Dmax`, or drops by
at most one.  Non-selected agents are unchanged by `Config.step`.

Potentially delicate semantic branch:
`processAgent` may also wake through `!partnerResetting`; along the no-wake
prefix, the pre-state is all Resetting, so the selected partner is Resetting
and that branch is blocked in the `propagateReset` unfold.
-/

set_option maxHeartbeats 2000000 in
/-- In an all-resetting interaction, the first endpoint's delaytimer after
`propagateReset` is either fresh (`≥ Dmax`) or has dropped by at most one.

This is the value analogue of
`propagateReset_all_resetting_fst_stays_of_delay_gt_one` from
`DrainNoWakeProtocol.lean`. -/
theorem propagateReset_all_resetting_fst_delaytimer_fresh_or_drop_by_one
    {Emax Dmax : ℕ} {hn : 0 < n}
    {s0 s1 : AgentState n}
    (hDmax : 0 < Dmax)
    (hs0 : s0.role = .Resetting)
    (hs1 : s1.role = .Resetting) :
    Dmax ≤ (propagateReset Emax Dmax hn s0 s1).1.delaytimer ∨
      s0.delaytimer ≤
        (propagateReset Emax Dmax hn s0 s1).1.delaytimer + 1 := by
  unfold propagateReset processAgent
  simp only [hs0, hs1, ne_eq, not_true_eq_false, and_false,
    and_self, ite_false, ite_true]
  repeat' split_ifs <;> simp_all [resetOSSR] <;> omega

set_option maxHeartbeats 2000000 in
/-- Symmetric value lemma for the second endpoint of `propagateReset`. -/
theorem propagateReset_all_resetting_snd_delaytimer_fresh_or_drop_by_one
    {Emax Dmax : ℕ} {hn : 0 < n}
    {s0 s1 : AgentState n}
    (hDmax : 0 < Dmax)
    (hs0 : s0.role = .Resetting)
    (hs1 : s1.role = .Resetting) :
    Dmax ≤ (propagateReset Emax Dmax hn s0 s1).2.delaytimer ∨
      s1.delaytimer ≤
        (propagateReset Emax Dmax hn s0 s1).2.delaytimer + 1 := by
  unfold propagateReset processAgent
  simp only [hs0, hs1, ne_eq, not_true_eq_false, and_false,
    and_self, ite_false, ite_true]
  repeat' split_ifs <;> simp_all [resetOSSR] <;> omega

/-- Push the first-endpoint delaytimer value lemma through `rankDeltaOSSR`.

The leader-deduplication post-processing in `rankDeltaOSSR` only changes the
second endpoint's `leader`, so it does not affect the first endpoint's
delaytimer. -/
theorem rankDeltaOSSR_all_resetting_fst_delaytimer_fresh_or_drop_by_one
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {s0 s1 : AgentState n}
    (hDmax : 0 < Dmax)
    (hs0 : s0.role = .Resetting)
    (hs1 : s1.role = .Resetting) :
    Dmax ≤ (rankDeltaOSSR Rmax Emax Dmax hn (s0, s1)).1.delaytimer ∨
      s0.delaytimer ≤
        (rankDeltaOSSR Rmax Emax Dmax hn (s0, s1)).1.delaytimer + 1 := by
  have hpr :=
    propagateReset_all_resetting_fst_delaytimer_fresh_or_drop_by_one
      (Emax := Emax) (Dmax := Dmax) (hn := hn)
      (s0 := s0) (s1 := s1) hDmax hs0 hs1
  simpa [rankDeltaOSSR, hs0, hs1] using hpr

set_option maxHeartbeats 2000000 in
/-- Symmetric value lemma through `rankDeltaOSSR`.

The possible leader-deduplication update on the second endpoint preserves
`delaytimer`. -/
theorem rankDeltaOSSR_all_resetting_snd_delaytimer_fresh_or_drop_by_one
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {s0 s1 : AgentState n}
    (hDmax : 0 < Dmax)
    (hs0 : s0.role = .Resetting)
    (hs1 : s1.role = .Resetting) :
    Dmax ≤ (rankDeltaOSSR Rmax Emax Dmax hn (s0, s1)).2.delaytimer ∨
      s1.delaytimer ≤
        (rankDeltaOSSR Rmax Emax Dmax hn (s0, s1)).2.delaytimer + 1 := by
  have hpr :=
    propagateReset_all_resetting_snd_delaytimer_fresh_or_drop_by_one
      (Emax := Emax) (Dmax := Dmax) (hn := hn)
      (s0 := s0) (s1 := s1) hDmax hs0 hs1
  unfold rankDeltaOSSR
  simp only [hs0, hs1, true_or, ite_true]
  rcases hprop : propagateReset Emax Dmax hn s0 s1 with ⟨p0, p1⟩
  simp [hprop] at hpr ⊢
  repeat' split_ifs <;> simp_all

set_option maxHeartbeats 2000000 in
/-- If a positive-resetcount first endpoint becomes dormant in an all-resetting
`propagateReset` interaction, its delaytimer has been refreshed to `Dmax`. -/
theorem propagateReset_all_resetting_fst_delaytimer_fresh_of_rc_ne_zero_of_post_dormant
    {Emax Dmax : ℕ} {hn : 0 < n}
    {s0 s1 : AgentState n}
    (hs0 : s0.role = .Resetting)
    (hs1 : s1.role = .Resetting)
    (hrc : s0.resetcount ≠ 0)
    (hpost :
      (propagateReset Emax Dmax hn s0 s1).1.role = .Resetting ∧
      (propagateReset Emax Dmax hn s0 s1).1.resetcount = 0) :
    Dmax ≤ (propagateReset Emax Dmax hn s0 s1).1.delaytimer := by
  unfold propagateReset processAgent at hpost ⊢
  simp only [hs0, hs1, ne_eq, not_true_eq_false, and_false,
    and_self, ite_false, ite_true] at hpost ⊢
  repeat' split_ifs at hpost ⊢ <;> simp_all [resetOSSR] <;> omega

set_option maxHeartbeats 2000000 in
/-- Symmetric positive-resetcount fresh-delay lemma for the second endpoint. -/
theorem propagateReset_all_resetting_snd_delaytimer_fresh_of_rc_ne_zero_of_post_dormant
    {Emax Dmax : ℕ} {hn : 0 < n}
    {s0 s1 : AgentState n}
    (hs0 : s0.role = .Resetting)
    (hs1 : s1.role = .Resetting)
    (hrc : s1.resetcount ≠ 0)
    (hpost :
      (propagateReset Emax Dmax hn s0 s1).2.role = .Resetting ∧
      (propagateReset Emax Dmax hn s0 s1).2.resetcount = 0) :
    Dmax ≤ (propagateReset Emax Dmax hn s0 s1).2.delaytimer := by
  unfold propagateReset processAgent at hpost ⊢
  simp only [hs0, hs1, ne_eq, not_true_eq_false, and_false,
    and_self, ite_false, ite_true] at hpost ⊢
  repeat' split_ifs at hpost ⊢ <;> simp_all [resetOSSR] <;> omega

/-- RankDelta version of the positive-resetcount fresh-delay lemma for the
first endpoint. -/
theorem rankDeltaOSSR_all_resetting_fst_delaytimer_fresh_of_rc_ne_zero_of_post_dormant
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {s0 s1 : AgentState n}
    (hs0 : s0.role = .Resetting)
    (hs1 : s1.role = .Resetting)
    (hrc : s0.resetcount ≠ 0)
    (hpost :
      (rankDeltaOSSR Rmax Emax Dmax hn (s0, s1)).1.role = .Resetting ∧
      (rankDeltaOSSR Rmax Emax Dmax hn (s0, s1)).1.resetcount = 0) :
    Dmax ≤ (rankDeltaOSSR Rmax Emax Dmax hn (s0, s1)).1.delaytimer := by
  have hpr :
      Dmax ≤ (propagateReset Emax Dmax hn s0 s1).1.delaytimer :=
    propagateReset_all_resetting_fst_delaytimer_fresh_of_rc_ne_zero_of_post_dormant
      (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hs0 hs1 hrc (by simpa [rankDeltaOSSR, hs0, hs1] using hpost)
  simpa [rankDeltaOSSR, hs0, hs1] using hpr

set_option maxHeartbeats 2000000 in
/-- RankDelta version of the positive-resetcount fresh-delay lemma for the
second endpoint. -/
theorem rankDeltaOSSR_all_resetting_snd_delaytimer_fresh_of_rc_ne_zero_of_post_dormant
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {s0 s1 : AgentState n}
    (hs0 : s0.role = .Resetting)
    (hs1 : s1.role = .Resetting)
    (hrc : s1.resetcount ≠ 0)
    (hpost :
      (rankDeltaOSSR Rmax Emax Dmax hn (s0, s1)).2.role = .Resetting ∧
      (rankDeltaOSSR Rmax Emax Dmax hn (s0, s1)).2.resetcount = 0) :
    Dmax ≤ (rankDeltaOSSR Rmax Emax Dmax hn (s0, s1)).2.delaytimer := by
  unfold rankDeltaOSSR at hpost ⊢
  simp only [hs0, hs1, true_or, ite_true] at hpost ⊢
  rcases hprop : propagateReset Emax Dmax hn s0 s1 with ⟨p0, p1⟩
  simp [hprop] at hpost ⊢
  have hpost_pr : p1.role = .Resetting ∧ p1.resetcount = 0 := by
    by_cases hflip :
        p0.leader = .L ∧ p1.leader = .L ∧
          p0.role = .Resetting ∧ p1.role = .Resetting
    · simpa [hflip] using hpost
    · simpa [hflip] using hpost
  have hpr_full :
      Dmax ≤ (propagateReset Emax Dmax hn s0 s1).2.delaytimer :=
    propagateReset_all_resetting_snd_delaytimer_fresh_of_rc_ne_zero_of_post_dormant
      (Emax := Emax) (Dmax := Dmax) (hn := hn)
      (s0 := s0) (s1 := s1) hs0 hs1 hrc (by
        simpa [hprop] using hpost_pr)
  have hpr : Dmax ≤ p1.delaytimer := by
    simpa [hprop] using hpr_full
  by_cases hflip :
      p0.leader = .L ∧ p1.leader = .L ∧
        p0.role = .Resetting ∧ p1.role = .Resetting
  · simpa [hflip] using hpr
  · simpa [hflip] using hpr

set_option maxHeartbeats 2000000 in
/-- `transitionPEM_prePhase4` preserves the first endpoint's `delaytimer`
from the ranking output.  It only changes `answer` and `timer`. -/
theorem transitionPEM_prePhase4_fst_delaytimer_eq_rankDelta
    {n trank : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    {s0 s1 : AgentState n} {x0 x1 : Opinion} :
    (transitionPEM_prePhase4 n trank rankDelta s0 s1 x0 x1).1.delaytimer =
      (rankDelta (s0, s1)).1.delaytimer := by
  unfold transitionPEM_prePhase4
  rcases hrd : rankDelta (s0, s1) with ⟨r0, r1⟩
  simp [hrd]
  repeat' split_ifs <;> simp_all

set_option maxHeartbeats 2000000 in
/-- `transitionPEM_prePhase4` preserves the first endpoint's `resetcount`
from the ranking output. -/
theorem transitionPEM_prePhase4_fst_resetcount_eq_rankDelta
    {n trank : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    {s0 s1 : AgentState n} {x0 x1 : Opinion} :
    (transitionPEM_prePhase4 n trank rankDelta s0 s1 x0 x1).1.resetcount =
      (rankDelta (s0, s1)).1.resetcount := by
  unfold transitionPEM_prePhase4
  rcases hrd : rankDelta (s0, s1) with ⟨r0, r1⟩
  simp [hrd]
  repeat' split_ifs <;> simp_all

set_option maxHeartbeats 2000000 in
/-- Symmetric resetcount preservation lemma for the second endpoint. -/
theorem transitionPEM_prePhase4_snd_resetcount_eq_rankDelta
    {n trank : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    {s0 s1 : AgentState n} {x0 x1 : Opinion} :
    (transitionPEM_prePhase4 n trank rankDelta s0 s1 x0 x1).2.resetcount =
      (rankDelta (s0, s1)).2.resetcount := by
  unfold transitionPEM_prePhase4
  rcases hrd : rankDelta (s0, s1) with ⟨r0, r1⟩
  simp [hrd]
  repeat' split_ifs <;> simp_all

set_option maxHeartbeats 2000000 in
/-- Symmetric delaytimer preservation lemma for the second endpoint. -/
theorem transitionPEM_prePhase4_snd_delaytimer_eq_rankDelta
    {n trank : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    {s0 s1 : AgentState n} {x0 x1 : Opinion} :
    (transitionPEM_prePhase4 n trank rankDelta s0 s1 x0 x1).2.delaytimer =
      (rankDelta (s0, s1)).2.delaytimer := by
  unfold transitionPEM_prePhase4
  rcases hrd : rankDelta (s0, s1) with ⟨r0, r1⟩
  simp [hrd]
  repeat' split_ifs <;> simp_all

/-- If the first ranking output is Resetting, the full PEM transition preserves
the first endpoint's `delaytimer` from the ranking output.

Reason: pre-phase-4 preserves `delaytimer`; phase 4 is disabled because the
first pre-phase-4 endpoint is Resetting, hence not both endpoints are Settled. -/
theorem transitionPEM_fst_delaytimer_eq_rankDelta_of_rankDelta_fst_role_resetting
    {n trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    {q0 q1 : AgentState n × Opinion}
    (hr :
      (rankDelta (q0.1, q1.1)).1.role = .Resetting) :
    (transitionPEM n trank Rmax rankDelta (q0, q1)).1.delaytimer =
      (rankDelta (q0.1, q1.1)).1.delaytimer := by
  rcases q0 with ⟨s0, x0⟩
  rcases q1 with ⟨s1, x1⟩
  let pre := transitionPEM_prePhase4 n trank rankDelta s0 s1 x0 x1
  have hpreRole : pre.1.role = .Resetting := by
    simpa [pre] using
      transitionPEM_prePhase4_fst_role_resetting_of_rankDelta_fst_role_resetting
        (n := n) (trank := trank) (rankDelta := rankDelta)
        (s0 := s0) (s1 := s1) (x0 := x0) (x1 := x1) hr
  have hpreDelay :
      pre.1.delaytimer = (rankDelta (s0, s1)).1.delaytimer := by
    simpa [pre] using
      transitionPEM_prePhase4_fst_delaytimer_eq_rankDelta
        (n := n) (trank := trank) (rankDelta := rankDelta)
        (s0 := s0) (s1 := s1) (x0 := x0) (x1 := x1)
  have hnot : ¬(pre.1.role = .Settled ∧ pre.2.role = .Settled) := by
    rintro ⟨hsett, _⟩
    rw [hpreRole] at hsett
    cases hsett
  simp only [transitionPEM_eq]
  change
    (transitionPEM_phase4 n Rmax pre x0 x1).1.delaytimer =
      (rankDelta (s0, s1)).1.delaytimer
  rw [transitionPEM_phase4_of_not_both_settled hnot]
  exact hpreDelay

/-- Symmetric delaytimer preservation through full PEM transition. -/
theorem transitionPEM_snd_delaytimer_eq_rankDelta_of_rankDelta_snd_role_resetting
    {n trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    {q0 q1 : AgentState n × Opinion}
    (hr :
      (rankDelta (q0.1, q1.1)).2.role = .Resetting) :
    (transitionPEM n trank Rmax rankDelta (q0, q1)).2.delaytimer =
      (rankDelta (q0.1, q1.1)).2.delaytimer := by
  rcases q0 with ⟨s0, x0⟩
  rcases q1 with ⟨s1, x1⟩
  let pre := transitionPEM_prePhase4 n trank rankDelta s0 s1 x0 x1
  have hpreRole : pre.2.role = .Resetting := by
    simpa [pre] using
      transitionPEM_prePhase4_snd_role_resetting_of_rankDelta_snd_role_resetting
        (n := n) (trank := trank) (rankDelta := rankDelta)
        (s0 := s0) (s1 := s1) (x0 := x0) (x1 := x1) hr
  have hpreDelay :
      pre.2.delaytimer = (rankDelta (s0, s1)).2.delaytimer := by
    simpa [pre] using
      transitionPEM_prePhase4_snd_delaytimer_eq_rankDelta
        (n := n) (trank := trank) (rankDelta := rankDelta)
        (s0 := s0) (s1 := s1) (x0 := x0) (x1 := x1)
  have hnot : ¬(pre.1.role = .Settled ∧ pre.2.role = .Settled) := by
    rintro ⟨_, hsett⟩
    rw [hpreRole] at hsett
    cases hsett
  simp only [transitionPEM_eq]
  change
    (transitionPEM_phase4 n Rmax pre x0 x1).2.delaytimer =
      (rankDelta (s0, s1)).2.delaytimer
  rw [transitionPEM_phase4_of_not_both_settled hnot]
  exact hpreDelay

/-- If the first ranking output is Resetting, the full PEM transition preserves
the first endpoint's resetcount from the ranking output. -/
theorem transitionPEM_fst_resetcount_eq_rankDelta_of_rankDelta_fst_role_resetting
    {n trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    {q0 q1 : AgentState n × Opinion}
    (hr :
      (rankDelta (q0.1, q1.1)).1.role = .Resetting) :
    (transitionPEM n trank Rmax rankDelta (q0, q1)).1.resetcount =
      (rankDelta (q0.1, q1.1)).1.resetcount := by
  rcases q0 with ⟨s0, x0⟩
  rcases q1 with ⟨s1, x1⟩
  let pre := transitionPEM_prePhase4 n trank rankDelta s0 s1 x0 x1
  have hpreRole : pre.1.role = .Resetting := by
    simpa [pre] using
      transitionPEM_prePhase4_fst_role_resetting_of_rankDelta_fst_role_resetting
        (n := n) (trank := trank) (rankDelta := rankDelta)
        (s0 := s0) (s1 := s1) (x0 := x0) (x1 := x1) hr
  have hpreRc :
      pre.1.resetcount = (rankDelta (s0, s1)).1.resetcount := by
    simpa [pre] using
      transitionPEM_prePhase4_fst_resetcount_eq_rankDelta
        (n := n) (trank := trank) (rankDelta := rankDelta)
        (s0 := s0) (s1 := s1) (x0 := x0) (x1 := x1)
  have hnot : ¬(pre.1.role = .Settled ∧ pre.2.role = .Settled) := by
    rintro ⟨hsett, _⟩
    rw [hpreRole] at hsett
    cases hsett
  simp only [transitionPEM_eq]
  change
    (transitionPEM_phase4 n Rmax pre x0 x1).1.resetcount =
      (rankDelta (s0, s1)).1.resetcount
  rw [transitionPEM_phase4_of_not_both_settled hnot]
  exact hpreRc

/-- Symmetric resetcount preservation through full PEM transition. -/
theorem transitionPEM_snd_resetcount_eq_rankDelta_of_rankDelta_snd_role_resetting
    {n trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    {q0 q1 : AgentState n × Opinion}
    (hr :
      (rankDelta (q0.1, q1.1)).2.role = .Resetting) :
    (transitionPEM n trank Rmax rankDelta (q0, q1)).2.resetcount =
      (rankDelta (q0.1, q1.1)).2.resetcount := by
  rcases q0 with ⟨s0, x0⟩
  rcases q1 with ⟨s1, x1⟩
  let pre := transitionPEM_prePhase4 n trank rankDelta s0 s1 x0 x1
  have hpreRole : pre.2.role = .Resetting := by
    simpa [pre] using
      transitionPEM_prePhase4_snd_role_resetting_of_rankDelta_snd_role_resetting
        (n := n) (trank := trank) (rankDelta := rankDelta)
        (s0 := s0) (s1 := s1) (x0 := x0) (x1 := x1) hr
  have hpreRc :
      pre.2.resetcount = (rankDelta (s0, s1)).2.resetcount := by
    simpa [pre] using
      transitionPEM_prePhase4_snd_resetcount_eq_rankDelta
        (n := n) (trank := trank) (rankDelta := rankDelta)
        (s0 := s0) (s1 := s1) (x0 := x0) (x1 := x1)
  have hnot : ¬(pre.1.role = .Settled ∧ pre.2.role = .Settled) := by
    rintro ⟨_, hsett⟩
    rw [hpreRole] at hsett
    cases hsett
  simp only [transitionPEM_eq]
  change
    (transitionPEM_phase4 n Rmax pre x0 x1).2.resetcount =
      (rankDelta (s0, s1)).2.resetcount
  rw [transitionPEM_phase4_of_not_both_settled hnot]
  exact hpreRc

/-- Pair-shaped first-endpoint PEM delaytimer value lemma under all-resetting
pre-state and pre-delaytimer `> 1`.

The `> 1` hypothesis guarantees, by the role-side lemma already proved in
`DrainNoWakeProtocol.lean`, that the endpoint is still Resetting after
`rankDeltaOSSR`; therefore PEM phase 4 is disabled for this endpoint and the
rankDelta value lemma transports to the full transition. -/
theorem transitionPEM_all_resetting_fst_delaytimer_fresh_or_drop_by_one_of_delay_gt_one
    {Rmax Emax Dmax trank : ℕ} {hn : 0 < n}
    {q0 q1 : AgentState n × Opinion}
    (hDmax : 0 < Dmax)
    (h0 : q0.1.role = .Resetting)
    (h1 : q1.1.role = .Resetting)
    (hdelay : 1 < q0.1.delaytimer) :
    Dmax ≤
        (transitionPEM n trank Rmax
          (rankDeltaOSSR Rmax Emax Dmax hn) (q0, q1)).1.delaytimer ∨
      q0.1.delaytimer ≤
        (transitionPEM n trank Rmax
          (rankDeltaOSSR Rmax Emax Dmax hn) (q0, q1)).1.delaytimer + 1 := by
  have hrdRole :
      (rankDeltaOSSR Rmax Emax Dmax hn (q0.1, q1.1)).1.role =
        .Resetting :=
    rankDeltaOSSR_all_resetting_fst_stays_of_delay_gt_one
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hDmax h0 h1 hdelay
  have hEq :
      (transitionPEM n trank Rmax
        (rankDeltaOSSR Rmax Emax Dmax hn) (q0, q1)).1.delaytimer =
        (rankDeltaOSSR Rmax Emax Dmax hn (q0.1, q1.1)).1.delaytimer :=
    transitionPEM_fst_delaytimer_eq_rankDelta_of_rankDelta_fst_role_resetting
      (n := n) (trank := trank) (Rmax := Rmax)
      (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
      (q0 := q0) (q1 := q1) hrdRole
  have hrdVal :=
    rankDeltaOSSR_all_resetting_fst_delaytimer_fresh_or_drop_by_one
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hDmax h0 h1
  rcases hrdVal with hfresh | hdrop
  · left
    simpa [hEq] using hfresh
  · right
    simpa [hEq] using hdrop

/-- Symmetric pair-shaped PEM delaytimer value lemma. -/
theorem transitionPEM_all_resetting_snd_delaytimer_fresh_or_drop_by_one_of_delay_gt_one
    {Rmax Emax Dmax trank : ℕ} {hn : 0 < n}
    {q0 q1 : AgentState n × Opinion}
    (hDmax : 0 < Dmax)
    (h0 : q0.1.role = .Resetting)
    (h1 : q1.1.role = .Resetting)
    (hdelay : 1 < q1.1.delaytimer) :
    Dmax ≤
        (transitionPEM n trank Rmax
          (rankDeltaOSSR Rmax Emax Dmax hn) (q0, q1)).2.delaytimer ∨
      q1.1.delaytimer ≤
        (transitionPEM n trank Rmax
          (rankDeltaOSSR Rmax Emax Dmax hn) (q0, q1)).2.delaytimer + 1 := by
  have hrdRole :
      (rankDeltaOSSR Rmax Emax Dmax hn (q0.1, q1.1)).2.role =
        .Resetting :=
    rankDeltaOSSR_all_resetting_snd_stays_of_delay_gt_one
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hDmax h0 h1 hdelay
  have hEq :
      (transitionPEM n trank Rmax
        (rankDeltaOSSR Rmax Emax Dmax hn) (q0, q1)).2.delaytimer =
        (rankDeltaOSSR Rmax Emax Dmax hn (q0.1, q1.1)).2.delaytimer :=
    transitionPEM_snd_delaytimer_eq_rankDelta_of_rankDelta_snd_role_resetting
      (n := n) (trank := trank) (Rmax := Rmax)
      (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
      (q0 := q0) (q1 := q1) hrdRole
  have hrdVal :=
    rankDeltaOSSR_all_resetting_snd_delaytimer_fresh_or_drop_by_one
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hDmax h0 h1
  rcases hrdVal with hfresh | hdrop
  · left
    simpa [hEq] using hfresh
  · right
    simpa [hEq] using hdrop

set_option maxHeartbeats 8000000 in
/-- One concrete PEM step from an all-Resetting pre-state satisfies the abstract
`WakeDelaytimerStepOK` condition.

Selected endpoints use the PEM delaytimer value lemmas above.  Non-endpoints
are unchanged by `Config.step`.  If a selected endpoint has pre-delaytimer
`≤ 1`, the drop-by-one side is immediate by arithmetic.  If it has
pre-delaytimer `> 1`, the concrete `processAgent`/PEM value lemma applies. -/
theorem wakeDelaytimerStepOK_PEM_of_all_resetting
    {n Rmax Emax Dmax d : ℕ} (hn : 0 < n) (hDmax : 0 < Dmax)
    (hd : d ≤ Dmax)
    (γ : DetScheduler n) (t : ℕ)
    (C : Config (AgentState n) Opinion n)
    (hall : AllAgentsResetting C) :
    WakeDelaytimerStepOK d γ t C
      (C.step (PEMProtocol n 1 Rmax Emax Dmax hn) (γ t).1 (γ t).2) := by
  classical
  intro a haPost
  by_cases hau : a = (γ t).1
  · subst a
    by_cases huv : (γ t).1 = (γ t).2
    · right
      constructor
      · simpa [DormantResetting, Config.step, huv] using haPost
      · have hsel : selectedAt γ (γ t).1 t := Or.inl rfl
        rw [if_pos hsel]
        simp [Config.step, huv]
    · by_cases hrc : (C (γ t).1).1.resetcount = 0
      · have hDormOld : DormantResetting C (γ t).1 :=
          ⟨hall (γ t).1, hrc⟩
        by_cases hsmall : (C (γ t).1).1.delaytimer ≤ 1
        · right
          constructor
          · exact hDormOld
          · have hsel : selectedAt γ (γ t).1 t := Or.inl rfl
            rw [if_pos hsel]
            omega
        · have hgt : 1 < (C (γ t).1).1.delaytimer := by omega
          have hor :=
            transitionPEM_all_resetting_fst_delaytimer_fresh_or_drop_by_one_of_delay_gt_one
              (n := n) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
              (trank := 1) (hn := hn)
              (q0 := C (γ t).1) (q1 := C (γ t).2)
              hDmax (hall (γ t).1) (hall (γ t).2) hgt
          rcases hor with hfresh | hdrop
          · left
            exact hd.trans (by simpa [Config.step, huv, PEMProtocol] using hfresh)
          · right
            constructor
            · exact hDormOld
            · have hsel : selectedAt γ (γ t).1 t := Or.inl rfl
              rw [if_pos hsel]
              simpa [Config.step, huv, PEMProtocol] using hdrop
      · left
        have hfresh :
            Dmax ≤
              ((C.step (PEMProtocol n 1 Rmax Emax Dmax hn)
                (γ t).1 (γ t).2 (γ t).1).1.delaytimer) := by
          let rd :=
            rankDeltaOSSR Rmax Emax Dmax hn
              ((C (γ t).1).1, (C (γ t).2).1)
          have hrdRole : rd.1.role = .Resetting := by
            simpa [rd] using
              rankDeltaOSSR_all_resetting_fst_stays_of_resetcount_ne_zero
                (n := n) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
                (hn := hn) hDmax (hall (γ t).1) (hall (γ t).2) hrc
          have hDelayEq :
              (transitionPEM n 1 Rmax
                (rankDeltaOSSR Rmax Emax Dmax hn)
                (C (γ t).1, C (γ t).2)).1.delaytimer =
                rd.1.delaytimer := by
            simpa [rd] using
              transitionPEM_fst_delaytimer_eq_rankDelta_of_rankDelta_fst_role_resetting
                (n := n) (trank := 1) (Rmax := Rmax)
                (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
                (q0 := C (γ t).1) (q1 := C (γ t).2) (by simpa [rd] using hrdRole)
          have hRcEq :
              (transitionPEM n 1 Rmax
                (rankDeltaOSSR Rmax Emax Dmax hn)
                (C (γ t).1, C (γ t).2)).1.resetcount =
                rd.1.resetcount := by
            simpa [rd] using
              transitionPEM_fst_resetcount_eq_rankDelta_of_rankDelta_fst_role_resetting
                (n := n) (trank := 1) (Rmax := Rmax)
                (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
                (q0 := C (γ t).1) (q1 := C (γ t).2) (by simpa [rd] using hrdRole)
          have hrdRc : rd.1.resetcount = 0 := by
            rw [← hRcEq]
            simpa [DormantResetting, Config.step, huv, PEMProtocol] using haPost.2
          have hrdFresh : Dmax ≤ rd.1.delaytimer := by
            simpa [rd] using
              rankDeltaOSSR_all_resetting_fst_delaytimer_fresh_of_rc_ne_zero_of_post_dormant
                (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
                (s0 := (C (γ t).1).1) (s1 := (C (γ t).2).1)
                (hall (γ t).1) (hall (γ t).2) hrc ⟨by simpa [rd] using hrdRole, hrdRc⟩
          have hFinalDelayEq :
              ((C.step (PEMProtocol n 1 Rmax Emax Dmax hn)
                (γ t).1 (γ t).2 (γ t).1).1.delaytimer) =
                rd.1.delaytimer := by
            simpa [Config.step, huv, PEMProtocol] using hDelayEq
          simpa [hFinalDelayEq] using hrdFresh
        exact hd.trans hfresh
  · by_cases hav : a = (γ t).2
    · subst a
      have huv : (γ t).1 ≠ (γ t).2 := by
        intro h
        exact hau h.symm
      by_cases hrc : (C (γ t).2).1.resetcount = 0
      · have hDormOld : DormantResetting C (γ t).2 :=
          ⟨hall (γ t).2, hrc⟩
        by_cases hsmall : (C (γ t).2).1.delaytimer ≤ 1
        · right
          constructor
          · exact hDormOld
          · have hsel : selectedAt γ (γ t).2 t := Or.inr rfl
            rw [if_pos hsel]
            omega
        · have hgt : 1 < (C (γ t).2).1.delaytimer := by omega
          have hor :=
            transitionPEM_all_resetting_snd_delaytimer_fresh_or_drop_by_one_of_delay_gt_one
              (n := n) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
              (trank := 1) (hn := hn)
              (q0 := C (γ t).1) (q1 := C (γ t).2)
              hDmax (hall (γ t).1) (hall (γ t).2) hgt
          rcases hor with hfresh | hdrop
          · left
            exact hd.trans
              (by simpa [Config.step, huv, hau, PEMProtocol] using hfresh)
          · right
            constructor
            · exact hDormOld
            · have hsel : selectedAt γ (γ t).2 t := Or.inr rfl
              rw [if_pos hsel]
              simpa [Config.step, huv, hau, PEMProtocol] using hdrop
      · left
        have hfresh :
            Dmax ≤
              ((C.step (PEMProtocol n 1 Rmax Emax Dmax hn)
                (γ t).1 (γ t).2 (γ t).2).1.delaytimer) := by
          let rd :=
            rankDeltaOSSR Rmax Emax Dmax hn
              ((C (γ t).1).1, (C (γ t).2).1)
          have hrdRole : rd.2.role = .Resetting := by
            simpa [rd] using
              rankDeltaOSSR_all_resetting_snd_stays_of_resetcount_ne_zero
                (n := n) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
                (hn := hn) hDmax (hall (γ t).1) (hall (γ t).2) hrc
          have hDelayEq :
              (transitionPEM n 1 Rmax
                (rankDeltaOSSR Rmax Emax Dmax hn)
                (C (γ t).1, C (γ t).2)).2.delaytimer =
                rd.2.delaytimer := by
            simpa [rd] using
              transitionPEM_snd_delaytimer_eq_rankDelta_of_rankDelta_snd_role_resetting
                (n := n) (trank := 1) (Rmax := Rmax)
                (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
                (q0 := C (γ t).1) (q1 := C (γ t).2) (by simpa [rd] using hrdRole)
          have hRcEq :
              (transitionPEM n 1 Rmax
                (rankDeltaOSSR Rmax Emax Dmax hn)
                (C (γ t).1, C (γ t).2)).2.resetcount =
                rd.2.resetcount := by
            simpa [rd] using
              transitionPEM_snd_resetcount_eq_rankDelta_of_rankDelta_snd_role_resetting
                (n := n) (trank := 1) (Rmax := Rmax)
                (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
                (q0 := C (γ t).1) (q1 := C (γ t).2) (by simpa [rd] using hrdRole)
          have hrdRc : rd.2.resetcount = 0 := by
            rw [← hRcEq]
            simpa [DormantResetting, Config.step, huv, hau, PEMProtocol] using haPost.2
          have hrdFresh : Dmax ≤ rd.2.delaytimer := by
            simpa [rd] using
              rankDeltaOSSR_all_resetting_snd_delaytimer_fresh_of_rc_ne_zero_of_post_dormant
                (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
                (s0 := (C (γ t).1).1) (s1 := (C (γ t).2).1)
                (hall (γ t).1) (hall (γ t).2) hrc ⟨by simpa [rd] using hrdRole, hrdRc⟩
          have hFinalDelayEq :
              ((C.step (PEMProtocol n 1 Rmax Emax Dmax hn)
                (γ t).1 (γ t).2 (γ t).2).1.delaytimer) =
                rd.2.delaytimer := by
            simpa [Config.step, huv, hau, PEMProtocol] using hDelayEq
          simpa [hFinalDelayEq] using hrdFresh
        exact hd.trans hfresh
    · right
      constructor
      · have hnotSel : ¬ selectedAt γ a t := by
          intro hsel
          rcases hsel with hsel | hsel
          · exact hau hsel
          · exact hav hsel
        by_cases huv : (γ t).1 = (γ t).2
        · simpa [DormantResetting, Config.step, huv] using haPost
        · simpa [DormantResetting, Config.step, huv, hau, hav] using haPost
      · have hnotSel : ¬ selectedAt γ a t := by
          intro hsel
          rcases hsel with hsel | hsel
          · exact hau hsel
          · exact hav hsel
        rw [if_neg hnotSel]
        by_cases huv : (γ t).1 = (γ t).2
        · simp [Config.step, huv]
        · simp [Config.step, huv, hau, hav]

/-- On a no-wake prefix of the concrete PEM execution, the wake-load certificate
holds at every time `t ≤ K`.

This is the requested induction:
* base: `initial_wake_load_certificate`, using the fresh Resetting delaytimer;
* step: convert `¬ SomeAgentAwake` at time `t` to `AllAgentsResetting`,
  discharge `WakeDelaytimerStepOK` for the concrete PEM step, then apply
  `WakeLoadCertificateAt.step`. -/
theorem wake_load_certificate_PEM_on_no_wake_prefix
    {n Rmax Emax Dmax K d : ℕ}
    (hn : 0 < n) (hDmax : 0 < Dmax) (hd : d ≤ Dmax)
    (C0 : Config (AgentState n) Opinion n)
    (γ : DetScheduler n)
    (hAll : AllAgentsResetting C0)
    (hDormantBudget :
      ∀ a : Fin n, (C0 a).1.resetcount = 0 → d ≤ (C0 a).1.delaytimer)
    (hNoAwakePrefix :
      ∀ s, s ≤ K →
        ¬ SomeAgentAwake
          (execution (PEMProtocol n 1 Rmax Emax Dmax hn) C0 γ s)) :
    ∀ t, t ≤ K →
      WakeLoadCertificateAt d γ t
        (execution (PEMProtocol n 1 Rmax Emax Dmax hn) C0 γ t) := by
  intro t
  induction t with
  | zero =>
      intro _ht
      apply initial_wake_load_certificate
      intro a ha
      exact hDormantBudget a ha.2
  | succ t ih =>
      intro htK
      have htK' : t ≤ K := Nat.le_trans (Nat.le_succ t) htK
      have hcert_t :
          WakeLoadCertificateAt d γ t
            (execution (PEMProtocol n 1 Rmax Emax Dmax hn) C0 γ t) :=
        ih htK'
      have hall_t :
          AllAgentsResetting
            (execution (PEMProtocol n 1 Rmax Emax Dmax hn) C0 γ t) :=
        (not_someAgentAwake_iff_allAgentsResetting
          (execution (PEMProtocol n 1 Rmax Emax Dmax hn) C0 γ t)).mp
          (hNoAwakePrefix t htK')
      have hstep :
          WakeDelaytimerStepOK d γ t
            (execution (PEMProtocol n 1 Rmax Emax Dmax hn) C0 γ t)
            ((execution (PEMProtocol n 1 Rmax Emax Dmax hn) C0 γ t).step
              (PEMProtocol n 1 Rmax Emax Dmax hn) (γ t).1 (γ t).2) :=
        wakeDelaytimerStepOK_PEM_of_all_resetting
          (n := n) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
          (d := d) hn hDmax hd γ t
          (execution (PEMProtocol n 1 Rmax Emax Dmax hn) C0 γ t)
          hall_t
      simpa [execution] using
        WakeLoadCertificateAt.step
          (d := d) (γ := γ) (t := t)
          (C := execution (PEMProtocol n 1 Rmax Emax Dmax hn) C0 γ t)
          (C' :=
            (execution (PEMProtocol n 1 Rmax Emax Dmax hn) C0 γ t).step
              (PEMProtocol n 1 Rmax Emax Dmax hn) (γ t).1 (γ t).2)
          hcert_t hstep

end SSEM
