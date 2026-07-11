import Ripple.PopulationProtocol.Majority.SSEM.UpperBound.Time.DrainNoWake
import Ripple.PopulationProtocol.Majority.SSEM.UpperBound.Time

namespace SSEM

open scoped BigOperators ENNReal

variable {n : ℕ}

/-!
# Concrete PEM witness for `SomeAgentAwakeStepWitness`

This file discharges the protocol-semantic hook left by `DrainNoWake.lean`.

The key semantic facts are:

* `Config.step` changes only the two selected endpoints.
* Along an all-resetting pre-state, the `rankDeltaOSSR` branch is
  `propagateReset`.
* If a selected resetting endpoint with `delaytimer > 1` is processed with a
  resetting partner and `0 < Dmax`, then it is still `Resetting` after
  `propagateReset`, hence after `rankDeltaOSSR`, hence after `transitionPEM`.
* Therefore, if a first awake agent appears, it is selected and its pre-step
  delaytimer is at most `1`.
-/

set_option maxHeartbeats 2000000 in
/-- In an all-resetting interaction, the first endpoint cannot wake through the
delay branch if its pre-step delaytimer is still greater than `1`.  This proof
unfolds the concrete `propagateReset`/`processAgent` code.

The hypothesis `0 < Dmax` rules out the fresh `oldRc > 0` branch waking
immediately after resetting the delaytimer to `Dmax`. -/
theorem propagateReset_all_resetting_fst_stays_of_delay_gt_one
    {Emax Dmax : ℕ} {hn : 0 < n}
    {s0 s1 : AgentState n}
    (hDmax : 0 < Dmax)
    (hs0 : s0.role = .Resetting)
    (hs1 : s1.role = .Resetting)
    (hdelay : 1 < s0.delaytimer) :
    (propagateReset Emax Dmax hn s0 s1).1.role = .Resetting := by
  unfold propagateReset processAgent
  simp only [hs0, hs1, ne_eq, not_true_eq_false, and_false,
    and_self, ite_false, ite_true]
  repeat' split_ifs <;> simp_all [resetOSSR] <;> omega

set_option maxHeartbeats 2000000 in
/-- Symmetric version for the second endpoint. -/
theorem propagateReset_all_resetting_snd_stays_of_delay_gt_one
    {Emax Dmax : ℕ} {hn : 0 < n}
    {s0 s1 : AgentState n}
    (hDmax : 0 < Dmax)
    (hs0 : s0.role = .Resetting)
    (hs1 : s1.role = .Resetting)
    (hdelay : 1 < s1.delaytimer) :
    (propagateReset Emax Dmax hn s0 s1).2.role = .Resetting := by
  unfold propagateReset processAgent
  simp only [hs0, hs1, ne_eq, not_true_eq_false, and_false,
    and_self, ite_false, ite_true]
  repeat' split_ifs <;> simp_all [resetOSSR] <;> omega

set_option maxHeartbeats 2000000 in
/-- Positive-resetcount first endpoint cannot wake in an all-resetting
interaction. If synchronization makes it dormant, `processAgent` refreshes its
delaytimer to `Dmax`, so `0 < Dmax` keeps it Resetting. -/
theorem propagateReset_all_resetting_fst_stays_of_resetcount_ne_zero
    {Emax Dmax : ℕ} {hn : 0 < n}
    {s0 s1 : AgentState n}
    (hDmax : 0 < Dmax)
    (hs0 : s0.role = .Resetting)
    (hs1 : s1.role = .Resetting)
    (hrc : s0.resetcount ≠ 0) :
    (propagateReset Emax Dmax hn s0 s1).1.role = .Resetting := by
  unfold propagateReset processAgent
  simp only [hs0, hs1, ne_eq, not_true_eq_false, and_false,
    and_self, ite_false, ite_true]
  repeat' split_ifs <;> simp_all [resetOSSR] <;> omega

set_option maxHeartbeats 2000000 in
/-- Symmetric positive-resetcount no-wake lemma for the second endpoint. -/
theorem propagateReset_all_resetting_snd_stays_of_resetcount_ne_zero
    {Emax Dmax : ℕ} {hn : 0 < n}
    {s0 s1 : AgentState n}
    (hDmax : 0 < Dmax)
    (hs0 : s0.role = .Resetting)
    (hs1 : s1.role = .Resetting)
    (hrc : s1.resetcount ≠ 0) :
    (propagateReset Emax Dmax hn s0 s1).2.role = .Resetting := by
  unfold propagateReset processAgent
  simp only [hs0, hs1, ne_eq, not_true_eq_false, and_false,
    and_self, ite_false, ite_true]
  repeat' split_ifs <;> simp_all [resetOSSR] <;> omega

/-- The first endpoint remains resetting after the concrete ranking subprotocol
when all endpoints were resetting and its delaytimer was still greater than
`1`. -/
theorem rankDeltaOSSR_all_resetting_fst_stays_of_delay_gt_one
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {s0 s1 : AgentState n}
    (hDmax : 0 < Dmax)
    (hs0 : s0.role = .Resetting)
    (hs1 : s1.role = .Resetting)
    (hdelay : 1 < s0.delaytimer) :
    (rankDeltaOSSR Rmax Emax Dmax hn (s0, s1)).1.role = .Resetting := by
  have hpr :
      (propagateReset Emax Dmax hn s0 s1).1.role = .Resetting :=
    propagateReset_all_resetting_fst_stays_of_delay_gt_one
      (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hDmax hs0 hs1 hdelay
  simpa [rankDeltaOSSR, hs0, hs1] using hpr

set_option maxHeartbeats 2000000 in
/-- Symmetric version for the second endpoint. -/
theorem rankDeltaOSSR_all_resetting_snd_stays_of_delay_gt_one
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {s0 s1 : AgentState n}
    (hDmax : 0 < Dmax)
    (hs0 : s0.role = .Resetting)
    (hs1 : s1.role = .Resetting)
    (hdelay : 1 < s1.delaytimer) :
    (rankDeltaOSSR Rmax Emax Dmax hn (s0, s1)).2.role = .Resetting := by
  have hpr :
      (propagateReset Emax Dmax hn s0 s1).2.role = .Resetting :=
    propagateReset_all_resetting_snd_stays_of_delay_gt_one
      (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hDmax hs0 hs1 hdelay
  unfold rankDeltaOSSR
  simp only [hs0, hs1, true_or, ite_true]
  repeat' split_ifs <;> simp_all

/-- The first endpoint remains resetting after the concrete ranking subprotocol
when all endpoints were resetting and its resetcount was positive. -/
theorem rankDeltaOSSR_all_resetting_fst_stays_of_resetcount_ne_zero
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {s0 s1 : AgentState n}
    (hDmax : 0 < Dmax)
    (hs0 : s0.role = .Resetting)
    (hs1 : s1.role = .Resetting)
    (hrc : s0.resetcount ≠ 0) :
    (rankDeltaOSSR Rmax Emax Dmax hn (s0, s1)).1.role = .Resetting := by
  have hpr :
      (propagateReset Emax Dmax hn s0 s1).1.role = .Resetting :=
    propagateReset_all_resetting_fst_stays_of_resetcount_ne_zero
      (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hDmax hs0 hs1 hrc
  simpa [rankDeltaOSSR, hs0, hs1] using hpr

set_option maxHeartbeats 2000000 in
/-- Symmetric rankDelta positive-resetcount no-wake lemma. -/
theorem rankDeltaOSSR_all_resetting_snd_stays_of_resetcount_ne_zero
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {s0 s1 : AgentState n}
    (hDmax : 0 < Dmax)
    (hs0 : s0.role = .Resetting)
    (hs1 : s1.role = .Resetting)
    (hrc : s1.resetcount ≠ 0) :
    (rankDeltaOSSR Rmax Emax Dmax hn (s0, s1)).2.role = .Resetting := by
  have hpr :
      (propagateReset Emax Dmax hn s0 s1).2.role = .Resetting :=
    propagateReset_all_resetting_snd_stays_of_resetcount_ne_zero
      (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hDmax hs0 hs1 hrc
  unfold rankDeltaOSSR
  simp only [hs0, hs1, true_or, ite_true]
  repeat' split_ifs <;> simp_all

set_option maxHeartbeats 2000000 in
/-- If the first rankDelta output is `Resetting`, then PEM pre-phase-4 leaves
the first role `Resetting`.  Pre-phase-4 may clear answers, initialize timers,
or copy answers between resetting agents, but it does not change this role. -/
theorem transitionPEM_prePhase4_fst_role_resetting_of_rankDelta_fst_role_resetting
    {n trank : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    {s0 s1 : AgentState n} {x0 x1 : Opinion}
    (hr :
      (rankDelta (s0, s1)).1.role = .Resetting) :
    (transitionPEM_prePhase4 n trank rankDelta s0 s1 x0 x1).1.role =
      .Resetting := by
  unfold transitionPEM_prePhase4
  rcases hrd : rankDelta (s0, s1) with ⟨r0, r1⟩
  simp [hrd] at hr ⊢
  repeat' split_ifs <;> simp_all

set_option maxHeartbeats 2000000 in
/-- Symmetric pre-phase-4 role lemma for the second endpoint. -/
theorem transitionPEM_prePhase4_snd_role_resetting_of_rankDelta_snd_role_resetting
    {n trank : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    {s0 s1 : AgentState n} {x0 x1 : Opinion}
    (hr :
      (rankDelta (s0, s1)).2.role = .Resetting) :
    (transitionPEM_prePhase4 n trank rankDelta s0 s1 x0 x1).2.role =
      .Resetting := by
  unfold transitionPEM_prePhase4
  rcases hrd : rankDelta (s0, s1) with ⟨r0, r1⟩
  simp [hrd] at hr ⊢
  repeat' split_ifs <;> simp_all

/-- If the first rankDelta output is `Resetting`, then the full PEM transition
leaves the first role `Resetting`: phase 4 is guarded by both endpoints being
`Settled`, which is impossible when the first pre-phase-4 role is `Resetting`. -/
theorem transitionPEM_fst_role_resetting_of_rankDelta_fst_role_resetting
    {n trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    {s0 s1 : AgentState n} {x0 x1 : Opinion}
    (hr :
      (rankDelta (s0, s1)).1.role = .Resetting) :
    (transitionPEM n trank Rmax rankDelta ((s0, x0), (s1, x1))).1.role =
      .Resetting := by
  let pre := transitionPEM_prePhase4 n trank rankDelta s0 s1 x0 x1
  have hpre : pre.1.role = .Resetting := by
    simpa [pre] using
      transitionPEM_prePhase4_fst_role_resetting_of_rankDelta_fst_role_resetting
        (n := n) (trank := trank) (rankDelta := rankDelta)
        (s0 := s0) (s1 := s1) (x0 := x0) (x1 := x1) hr
  have hnot : ¬(pre.1.role = .Settled ∧ pre.2.role = .Settled) := by
    rintro ⟨hsett, _⟩
    rw [hpre] at hsett
    cases hsett
  simp only [transitionPEM_eq]
  change (transitionPEM_phase4 n Rmax pre x0 x1).1.role = .Resetting
  rw [transitionPEM_phase4_of_not_both_settled hnot]
  exact hpre

/-- Symmetric full-transition role lemma for the second endpoint. -/
theorem transitionPEM_snd_role_resetting_of_rankDelta_snd_role_resetting
    {n trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    {s0 s1 : AgentState n} {x0 x1 : Opinion}
    (hr :
      (rankDelta (s0, s1)).2.role = .Resetting) :
    (transitionPEM n trank Rmax rankDelta ((s0, x0), (s1, x1))).2.role =
      .Resetting := by
  let pre := transitionPEM_prePhase4 n trank rankDelta s0 s1 x0 x1
  have hpre : pre.2.role = .Resetting := by
    simpa [pre] using
      transitionPEM_prePhase4_snd_role_resetting_of_rankDelta_snd_role_resetting
        (n := n) (trank := trank) (rankDelta := rankDelta)
        (s0 := s0) (s1 := s1) (x0 := x0) (x1 := x1) hr
  have hnot : ¬(pre.1.role = .Settled ∧ pre.2.role = .Settled) := by
    rintro ⟨_, hsett⟩
    rw [hpre] at hsett
    cases hsett
  simp only [transitionPEM_eq]
  change (transitionPEM_phase4 n Rmax pre x0 x1).2.role = .Resetting
  rw [transitionPEM_phase4_of_not_both_settled hnot]
  exact hpre

/-- Pair-shaped version matching `Config.step`: if all selected endpoints are
resetting and the first endpoint has delaytimer greater than `1`, then the full
concrete PEM transition keeps the first endpoint resetting. -/
theorem transitionPEM_all_resetting_fst_stays_of_delay_gt_one
    {Rmax Emax Dmax trank : ℕ} {hn : 0 < n}
    {q0 q1 : AgentState n × Opinion}
    (hDmax : 0 < Dmax)
    (h0 : q0.1.role = .Resetting)
    (h1 : q1.1.role = .Resetting)
    (hdelay : 1 < q0.1.delaytimer) :
    (transitionPEM n trank Rmax
      (rankDeltaOSSR Rmax Emax Dmax hn) (q0, q1)).1.role = .Resetting := by
  rcases q0 with ⟨s0, x0⟩
  rcases q1 with ⟨s1, x1⟩
  have hrd :
      (rankDeltaOSSR Rmax Emax Dmax hn (s0, s1)).1.role =
        .Resetting :=
    rankDeltaOSSR_all_resetting_fst_stays_of_delay_gt_one
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hDmax h0 h1 hdelay
  exact
    transitionPEM_fst_role_resetting_of_rankDelta_fst_role_resetting
      (n := n) (trank := trank) (Rmax := Rmax)
      (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
      (s0 := s0) (s1 := s1) (x0 := x0) (x1 := x1) hrd

/-- Symmetric pair-shaped version for the second endpoint. -/
theorem transitionPEM_all_resetting_snd_stays_of_delay_gt_one
    {Rmax Emax Dmax trank : ℕ} {hn : 0 < n}
    {q0 q1 : AgentState n × Opinion}
    (hDmax : 0 < Dmax)
    (h0 : q0.1.role = .Resetting)
    (h1 : q1.1.role = .Resetting)
    (hdelay : 1 < q1.1.delaytimer) :
    (transitionPEM n trank Rmax
      (rankDeltaOSSR Rmax Emax Dmax hn) (q0, q1)).2.role = .Resetting := by
  rcases q0 with ⟨s0, x0⟩
  rcases q1 with ⟨s1, x1⟩
  have hrd :
      (rankDeltaOSSR Rmax Emax Dmax hn (s0, s1)).2.role =
        .Resetting :=
    rankDeltaOSSR_all_resetting_snd_stays_of_delay_gt_one
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hDmax h0 h1 hdelay
  exact
    transitionPEM_snd_role_resetting_of_rankDelta_snd_role_resetting
      (n := n) (trank := trank) (Rmax := Rmax)
      (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
      (s0 := s0) (s1 := s1) (x0 := x0) (x1 := x1) hrd

/-- Positive-resetcount first endpoint remains Resetting through the full PEM
transition in an all-resetting interaction. -/
theorem transitionPEM_all_resetting_fst_stays_of_resetcount_ne_zero
    {Rmax Emax Dmax trank : ℕ} {hn : 0 < n}
    {q0 q1 : AgentState n × Opinion}
    (hDmax : 0 < Dmax)
    (h0 : q0.1.role = .Resetting)
    (h1 : q1.1.role = .Resetting)
    (hrc : q0.1.resetcount ≠ 0) :
    (transitionPEM n trank Rmax
      (rankDeltaOSSR Rmax Emax Dmax hn) (q0, q1)).1.role = .Resetting := by
  rcases q0 with ⟨s0, x0⟩
  rcases q1 with ⟨s1, x1⟩
  have hrd :
      (rankDeltaOSSR Rmax Emax Dmax hn (s0, s1)).1.role =
        .Resetting :=
    rankDeltaOSSR_all_resetting_fst_stays_of_resetcount_ne_zero
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hDmax h0 h1 hrc
  exact
    transitionPEM_fst_role_resetting_of_rankDelta_fst_role_resetting
      (n := n) (trank := trank) (Rmax := Rmax)
      (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
      (s0 := s0) (s1 := s1) (x0 := x0) (x1 := x1) hrd

/-- Symmetric full PEM positive-resetcount no-wake lemma. -/
theorem transitionPEM_all_resetting_snd_stays_of_resetcount_ne_zero
    {Rmax Emax Dmax trank : ℕ} {hn : 0 < n}
    {q0 q1 : AgentState n × Opinion}
    (hDmax : 0 < Dmax)
    (h0 : q0.1.role = .Resetting)
    (h1 : q1.1.role = .Resetting)
    (hrc : q1.1.resetcount ≠ 0) :
    (transitionPEM n trank Rmax
      (rankDeltaOSSR Rmax Emax Dmax hn) (q0, q1)).2.role = .Resetting := by
  rcases q0 with ⟨s0, x0⟩
  rcases q1 with ⟨s1, x1⟩
  have hrd :
      (rankDeltaOSSR Rmax Emax Dmax hn (s0, s1)).2.role =
        .Resetting :=
    rankDeltaOSSR_all_resetting_snd_stays_of_resetcount_ne_zero
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hDmax h0 h1 hrc
  exact
    transitionPEM_snd_role_resetting_of_rankDelta_snd_role_resetting
      (n := n) (trank := trank) (Rmax := Rmax)
      (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
      (s0 := s0) (s1 := s1) (x0 := x0) (x1 := x1) hrd

/-- Concrete protocol-semantic discharge of `SomeAgentAwakeStepWitness` for the
`protocolPEM` spelling.

This is the direct hook needed by `wake_before_K_implies_high_load`: from an
all-resetting pre-state, if one concrete PEM step creates an awake agent, then
some selected endpoint had pre-step delaytimer at most `1`. -/
theorem someAgentAwakeStepWitness_protocolPEM
    {n Rmax Emax Dmax : ℕ} (hn : 0 < n) (hDmax : 0 < Dmax)
    (γ : DetScheduler n) (t : ℕ)
    (C : Config (AgentState n) Opinion n) :
    SomeAgentAwakeStepWitness γ t C
      (C.step
        (protocolPEM n 1 Rmax (rankDeltaOSSR Rmax Emax Dmax hn))
        (γ t).1 (γ t).2) := by
  classical
  intro hnotAwake hAwake
  have hall : AllAgentsResetting C :=
    (not_someAgentAwake_iff_allAgentsResetting C).mp hnotAwake
  rcases hAwake with ⟨w, hwAwake⟩

  by_cases hwu : w = (γ t).1
  · refine ⟨w, ?_⟩
    unfold WakeTimeoutSelectedAt
    by_cases hrc : (C w).1.resetcount = 0
    · refine ⟨Or.inl hwu, ⟨hall w, hrc⟩, ?_⟩
      by_contra hle
      have hgt : 1 < (C w).1.delaytimer := by omega
      subst w
      have hpostRole :
          ((C.step
            (protocolPEM n 1 Rmax (rankDeltaOSSR Rmax Emax Dmax hn))
            (γ t).1 (γ t).2 (γ t).1).1.role = .Resetting) := by
        by_cases huv : (γ t).1 = (γ t).2
        · simpa [Config.step, huv] using hall (γ t).1
        · simpa [Config.step, huv, protocolPEM] using
            transitionPEM_all_resetting_fst_stays_of_delay_gt_one
              (n := n) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
              (trank := 1) (hn := hn)
              (q0 := C (γ t).1) (q1 := C (γ t).2)
              hDmax (hall (γ t).1) (hall (γ t).2) hgt
      exact hwAwake hpostRole
    · exfalso
      subst w
      have hpostRole :
          ((C.step
            (protocolPEM n 1 Rmax (rankDeltaOSSR Rmax Emax Dmax hn))
            (γ t).1 (γ t).2 (γ t).1).1.role = .Resetting) := by
        by_cases huv : (γ t).1 = (γ t).2
        · simpa [Config.step, huv] using hall (γ t).1
        · simpa [Config.step, huv, protocolPEM] using
            transitionPEM_all_resetting_fst_stays_of_resetcount_ne_zero
              (n := n) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
              (trank := 1) (hn := hn)
              (q0 := C (γ t).1) (q1 := C (γ t).2)
              hDmax (hall (γ t).1) (hall (γ t).2) hrc
      exact hwAwake hpostRole

  · by_cases hwv : w = (γ t).2
    · refine ⟨w, ?_⟩
      unfold WakeTimeoutSelectedAt
      by_cases hrc : (C w).1.resetcount = 0
      · refine ⟨Or.inr hwv, ⟨hall w, hrc⟩, ?_⟩
        by_contra hle
        have hgt : 1 < (C w).1.delaytimer := by omega
        subst w
        have huv : (γ t).1 ≠ (γ t).2 := by
          intro h
          exact hwu h.symm
        have hpostRole :
            ((C.step
              (protocolPEM n 1 Rmax (rankDeltaOSSR Rmax Emax Dmax hn))
              (γ t).1 (γ t).2 (γ t).2).1.role = .Resetting) := by
          simpa [Config.step, huv, hwu, protocolPEM] using
            transitionPEM_all_resetting_snd_stays_of_delay_gt_one
              (n := n) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
              (trank := 1) (hn := hn)
              (q0 := C (γ t).1) (q1 := C (γ t).2)
              hDmax (hall (γ t).1) (hall (γ t).2) hgt
        exact hwAwake hpostRole
      · exfalso
        subst w
        have huv : (γ t).1 ≠ (γ t).2 := by
          intro h
          exact hwu h.symm
        have hpostRole :
            ((C.step
              (protocolPEM n 1 Rmax (rankDeltaOSSR Rmax Emax Dmax hn))
              (γ t).1 (γ t).2 (γ t).2).1.role = .Resetting) := by
          simpa [Config.step, huv, hwu, protocolPEM] using
            transitionPEM_all_resetting_snd_stays_of_resetcount_ne_zero
              (n := n) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
              (trank := 1) (hn := hn)
              (q0 := C (γ t).1) (q1 := C (γ t).2)
              hDmax (hall (γ t).1) (hall (γ t).2) hrc
        exact hwAwake hpostRole

    · exfalso
      have hpostRole :
          ((C.step
            (protocolPEM n 1 Rmax (rankDeltaOSSR Rmax Emax Dmax hn))
            (γ t).1 (γ t).2 w).1.role = .Resetting) := by
        by_cases huv : (γ t).1 = (γ t).2
        · simpa [Config.step, huv] using hall w
        · simpa [Config.step, huv, hwu, hwv] using hall w
      exact hwAwake hpostRole

/-- Same witness lemma in the time-layer `PEMProtocol` abbreviation requested
by the upper-bound files. -/
theorem someAgentAwakeStepWitness_PEM
    {n Rmax Emax Dmax : ℕ} (hn : 0 < n) (hDmax : 0 < Dmax)
    (γ : DetScheduler n) (t : ℕ)
    (C : Config (AgentState n) Opinion n) :
    SomeAgentAwakeStepWitness γ t C
      (C.step (PEMProtocol n 1 Rmax Emax Dmax hn) (γ t).1 (γ t).2) := by
  simpa [PEMProtocol] using
    someAgentAwakeStepWitness_protocolPEM
      (n := n) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      hn hDmax γ t C

end SSEM
