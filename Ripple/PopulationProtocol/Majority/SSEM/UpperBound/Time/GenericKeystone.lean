import Ripple.PopulationProtocol.Majority.SSEM.UpperBound.Time.GenericTrank
import Ripple.PopulationProtocol.Majority.SSEM.UpperBound.Time.OptimalWindows

set_option linter.style.header false

/-!
# Generic-trank faithful reset keystone

This file assembles the faithful reset-completion contract with the generic
`trank` phase windows.  The reset contract is stated directly for
`PEMProtocol n trank Rmax`; no coupled median-timer scale is used in the
keystone.
-/

namespace SSEM

open scoped BigOperators ENNReal

attribute [local instance] Classical.propDecidable

section

variable {n trank Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]

/-- Per-agent structural bounds for the `Nat` counters whose paper versions
live in bounded ranges.  The `children` field is included because the ranking
subprotocol's recruitment budget is also range-bounded in reachable states. -/
def AgentWellFormed (Rmax Emax Dmax : ℕ) (s : AgentState n) : Prop :=
  s.resetcount ≤ Rmax ∧
  s.errorcount ≤ Emax ∧
  s.delaytimer ≤ Dmax ∧
  s.children ≤ 2

/-- Well-formed configurations: protocol timer range plus bounded structural
counter fields. -/
def WellFormed (trank Rmax Emax Dmax : ℕ)
    (C : Config (AgentState n) Opinion n) : Prop :=
  IsTimerBoundedConfig (7 * (trank + 4)) C ∧
  ∀ v : Fin n, AgentWellFormed Rmax Emax Dmax (C v).1

private theorem resetOSSR_preserves_agent_wellformed
    {n Rmax Emax Dmax : ℕ} {hn : 0 < n} {s : AgentState n}
    (hs : AgentWellFormed Rmax Emax Dmax s) :
    AgentWellFormed Rmax Emax Dmax (resetOSSR Emax hn s) := by
  rcases s with ⟨role, rank, leader, resetcount, answer, timer, children,
    errorcount, delaytimer⟩
  cases leader <;> simp [AgentWellFormed, resetOSSR] at * <;> omega

set_option maxHeartbeats 800000 in
-- Concrete OSSR process-agent case split needs extra heartbeats for record fields.
private theorem processAgent_preserves_agent_wellformed
    {n Rmax Emax Dmax : ℕ} {hn : 0 < n} {s : AgentState n}
    {oldRc : ℕ} {partnerResetting : Bool}
    (hs : AgentWellFormed Rmax Emax Dmax s) :
    AgentWellFormed Rmax Emax Dmax
      (processAgent Emax Dmax hn s oldRc partnerResetting) := by
  unfold processAgent
  by_cases hmain : s.role = .Resetting ∧ s.resetcount = 0
  · rw [if_pos hmain]
    let t : AgentState n :=
      if 0 < oldRc then
        { s with delaytimer := Dmax }
      else
        { s with delaytimer := s.delaytimer - 1 }
    have ht : AgentWellFormed Rmax Emax Dmax t := by
      by_cases hold : 0 < oldRc
      · simp [t, hold, AgentWellFormed] at *
        omega
      · simp [t, hold, AgentWellFormed] at *
        omega
    change AgentWellFormed Rmax Emax Dmax
      (if t.delaytimer = 0 ∨ !partnerResetting then resetOSSR Emax hn t else t)
    cases partnerResetting <;>
      by_cases hfire : t.delaytimer = 0 <;>
      simp [hfire, resetOSSR_preserves_agent_wellformed ht, ht]
  · rw [if_neg hmain]
    exact hs

private theorem propagateReset_recruit_preserves_agent_wellformed
    {n Rmax Emax Dmax : ℕ} {a b : AgentState n}
    (ha : AgentWellFormed Rmax Emax Dmax a)
    (hb : AgentWellFormed Rmax Emax Dmax b) :
    AgentWellFormed Rmax Emax Dmax
        (if a.role = .Resetting ∧ 0 < a.resetcount ∧ b.role ≠ .Resetting then
          (a, { b with role := .Resetting, resetcount := 0, delaytimer := Dmax })
        else if b.role = .Resetting ∧ 0 < b.resetcount ∧ a.role ≠ .Resetting then
          ({ a with role := .Resetting, resetcount := 0, delaytimer := Dmax }, b)
        else (a, b)).1 ∧
      AgentWellFormed Rmax Emax Dmax
        (if a.role = .Resetting ∧ 0 < a.resetcount ∧ b.role ≠ .Resetting then
          (a, { b with role := .Resetting, resetcount := 0, delaytimer := Dmax })
        else if b.role = .Resetting ∧ 0 < b.resetcount ∧ a.role ≠ .Resetting then
          ({ a with role := .Resetting, resetcount := 0, delaytimer := Dmax }, b)
        else (a, b)).2 := by
  split_ifs <;> simp_all [AgentWellFormed]

private theorem propagateReset_sync_preserves_agent_wellformed
    {n Rmax Emax Dmax : ℕ} {a b : AgentState n}
    (ha : AgentWellFormed Rmax Emax Dmax a)
    (hb : AgentWellFormed Rmax Emax Dmax b) :
    AgentWellFormed Rmax Emax Dmax
        (if a.role = .Resetting ∧ b.role = .Resetting then
          let newRc := max (a.resetcount - 1) (b.resetcount - 1)
          ({ a with resetcount := newRc }, { b with resetcount := newRc })
        else (a, b)).1 ∧
      AgentWellFormed Rmax Emax Dmax
        (if a.role = .Resetting ∧ b.role = .Resetting then
          let newRc := max (a.resetcount - 1) (b.resetcount - 1)
          ({ a with resetcount := newRc }, { b with resetcount := newRc })
        else (a, b)).2 := by
  split_ifs <;> simp_all [AgentWellFormed]
  omega

private theorem propagateReset_preserves_agent_wellformed
    {n Rmax Emax Dmax : ℕ} {hn : 0 < n} {a b : AgentState n}
    (ha : AgentWellFormed Rmax Emax Dmax a)
    (hb : AgentWellFormed Rmax Emax Dmax b) :
    AgentWellFormed Rmax Emax Dmax (propagateReset Emax Dmax hn a b).1 ∧
    AgentWellFormed Rmax Emax Dmax (propagateReset Emax Dmax hn a b).2 := by
  unfold propagateReset
  let p₁ :=
    if a.role = .Resetting ∧ 0 < a.resetcount ∧ b.role ≠ .Resetting then
      (a, { b with role := .Resetting, resetcount := 0, delaytimer := Dmax })
    else if b.role = .Resetting ∧ 0 < b.resetcount ∧ a.role ≠ .Resetting then
      ({ a with role := .Resetting, resetcount := 0, delaytimer := Dmax }, b)
    else (a, b)
  have hp₁ :
      AgentWellFormed Rmax Emax Dmax p₁.1 ∧
      AgentWellFormed Rmax Emax Dmax p₁.2 := by
    simpa [p₁] using
      propagateReset_recruit_preserves_agent_wellformed
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) ha hb
  let oldRcA := p₁.1.resetcount
  let oldRcB := p₁.2.resetcount
  let p₂ :=
    if p₁.1.role = .Resetting ∧ p₁.2.role = .Resetting then
      let newRc := max (p₁.1.resetcount - 1) (p₁.2.resetcount - 1)
      ({ p₁.1 with resetcount := newRc }, { p₁.2 with resetcount := newRc })
    else p₁
  have hp₂ :
      AgentWellFormed Rmax Emax Dmax p₂.1 ∧
      AgentWellFormed Rmax Emax Dmax p₂.2 := by
    simpa [p₂] using
      propagateReset_sync_preserves_agent_wellformed hp₁.1 hp₁.2
  simpa [p₁, oldRcA, oldRcB, p₂] using
    And.intro
      (processAgent_preserves_agent_wellformed hp₂.1)
      (processAgent_preserves_agent_wellformed hp₂.2)

set_option maxHeartbeats 800000 in
-- Concrete OSSR rank-delta case split needs extra heartbeats for record fields.
private theorem rankDeltaOSSR_preserves_agent_wellformed
    {n Rmax Emax Dmax : ℕ} {hn : 0 < n} {a b : AgentState n}
    (ha : AgentWellFormed Rmax Emax Dmax a)
    (hb : AgentWellFormed Rmax Emax Dmax b) :
    AgentWellFormed Rmax Emax Dmax
        (rankDeltaOSSR Rmax Emax Dmax hn (a, b)).1 ∧
      AgentWellFormed Rmax Emax Dmax
        (rankDeltaOSSR Rmax Emax Dmax hn (a, b)).2 := by
  unfold rankDeltaOSSR
  by_cases hReset : a.role = .Resetting ∨ b.role = .Resetting
  · simp [hReset]
    have hpr := propagateReset_preserves_agent_wellformed (hn := hn) ha hb
    split_ifs <;> simp_all [AgentWellFormed]
  · simp [hReset]
    repeat' split_ifs <;> simp_all [AgentWellFormed] <;> omega

private theorem transitionPEM_prePhase4_preserves_agent_wellformed
    {n trank Rmax Emax Dmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    {s₀ s₁ : AgentState n} {x₀ x₁ : Opinion}
    (hRankDelta :
      AgentWellFormed Rmax Emax Dmax (rankDelta (s₀, s₁)).1 ∧
      AgentWellFormed Rmax Emax Dmax (rankDelta (s₀, s₁)).2) :
    AgentWellFormed Rmax Emax Dmax
        (transitionPEM_prePhase4 n trank rankDelta s₀ s₁ x₀ x₁).1 ∧
      AgentWellFormed Rmax Emax Dmax
        (transitionPEM_prePhase4 n trank rankDelta s₀ s₁ x₀ x₁).2 := by
  unfold transitionPEM_prePhase4
  rcases hrd : rankDelta (s₀, s₁) with ⟨r₀, r₁⟩
  simp [hrd] at hRankDelta ⊢
  repeat' split_ifs <;> simp_all [AgentWellFormed]

private theorem phase4_swap_preserves_agent_wellformed
    {n Rmax Emax Dmax : ℕ} {a b : AgentState n} {x₀ x₁ : Opinion}
    (ha : AgentWellFormed Rmax Emax Dmax a)
    (hb : AgentWellFormed Rmax Emax Dmax b) :
    AgentWellFormed Rmax Emax Dmax (phase4_swap a b x₀ x₁).1 ∧
    AgentWellFormed Rmax Emax Dmax (phase4_swap a b x₀ x₁).2 := by
  unfold phase4_swap
  split_ifs <;> simp_all [AgentWellFormed]

private theorem phase4_decide_preserves_agent_wellformed
    {n Rmax Emax Dmax : ℕ} {a b : AgentState n} {x₀ x₁ : Opinion}
    (ha : AgentWellFormed Rmax Emax Dmax a)
    (hb : AgentWellFormed Rmax Emax Dmax b) :
    AgentWellFormed Rmax Emax Dmax (phase4_decide n a b x₀ x₁).1 ∧
    AgentWellFormed Rmax Emax Dmax (phase4_decide n a b x₀ x₁).2 := by
  unfold phase4_decide
  repeat' split_ifs <;> simp_all [AgentWellFormed]

set_option maxHeartbeats 800000 in
-- Phase-4 propagation has nested timer/reset branches over record updates.
private theorem phase4_propagate_preserves_agent_wellformed
    {n Rmax Emax Dmax : ℕ} {a b : AgentState n}
    (ha : AgentWellFormed Rmax Emax Dmax a)
    (hb : AgentWellFormed Rmax Emax Dmax b) :
    AgentWellFormed Rmax Emax Dmax (phase4_propagate n Rmax a b).1 ∧
    AgentWellFormed Rmax Emax Dmax (phase4_propagate n Rmax a b).2 := by
  unfold phase4_propagate
  by_cases haMed : a.rank.val + 1 = ceilHalf n
  · by_cases hbLast : b.rank.val + 1 = n
    · by_cases hReset :
        ({ a with timer := a.timer - 1 } : AgentState n).timer = 0 ∧
          ({ a with timer := a.timer - 1 } : AgentState n).answer ≠ b.answer
      · simp [haMed, hbLast, hReset, AgentWellFormed] at *
        omega
      · simp [haMed, hbLast, hReset, AgentWellFormed] at *
        omega
    · by_cases hReset : a.timer = 0 ∧ a.answer ≠ b.answer
      · simp [haMed, hbLast, hReset, AgentWellFormed] at *
        omega
      · simp [haMed, hbLast, hReset, AgentWellFormed] at *
        omega
  · by_cases hbMed : b.rank.val + 1 = ceilHalf n
    · by_cases haLast : a.rank.val + 1 = n
      · by_cases hReset :
          ({ b with timer := b.timer - 1 } : AgentState n).timer = 0 ∧
            ({ b with timer := b.timer - 1 } : AgentState n).answer ≠ a.answer
        · have hn_ne_ceil : n ≠ ceilHalf n := by
            intro h
            exact haMed (by omega)
          simp [hn_ne_ceil, hbMed, haLast, hReset, AgentWellFormed] at *
          omega
        · have hn_ne_ceil : n ≠ ceilHalf n := by
            intro h
            exact haMed (by omega)
          simp [hn_ne_ceil, hbMed, haLast, hReset, AgentWellFormed] at *
          omega
      · by_cases hReset : b.timer = 0 ∧ b.answer ≠ a.answer
        · simp [haMed, hbMed, haLast, hReset, AgentWellFormed] at *
          omega
        · simp [haMed, hbMed, haLast, hReset, AgentWellFormed] at *
          omega
    · simp [haMed, hbMed, AgentWellFormed] at *
      omega

private theorem transitionPEM_phase4_preserves_agent_wellformed
    {n Rmax Emax Dmax : ℕ} {a : AgentState n × AgentState n} {x₀ x₁ : Opinion}
    (ha : AgentWellFormed Rmax Emax Dmax a.1)
    (hb : AgentWellFormed Rmax Emax Dmax a.2) :
    AgentWellFormed Rmax Emax Dmax (transitionPEM_phase4 n Rmax a x₀ x₁).1 ∧
    AgentWellFormed Rmax Emax Dmax (transitionPEM_phase4 n Rmax a x₀ x₁).2 := by
  by_cases hSettled : a.1.role = .Settled ∧ a.2.role = .Settled
  · let sw := phase4_swap a.1 a.2 x₀ x₁
    have hsw :
        AgentWellFormed Rmax Emax Dmax sw.1 ∧
        AgentWellFormed Rmax Emax Dmax sw.2 :=
      phase4_swap_preserves_agent_wellformed (x₀ := x₀) (x₁ := x₁) ha hb
    let dec := phase4_decide n sw.1 sw.2 x₀ x₁
    have hdec :
        AgentWellFormed Rmax Emax Dmax dec.1 ∧
        AgentWellFormed Rmax Emax Dmax dec.2 :=
      phase4_decide_preserves_agent_wellformed (x₀ := x₀) (x₁ := x₁) hsw.1 hsw.2
    have hprop :
        AgentWellFormed Rmax Emax Dmax (phase4_propagate n Rmax dec.1 dec.2).1 ∧
        AgentWellFormed Rmax Emax Dmax (phase4_propagate n Rmax dec.1 dec.2).2 :=
      phase4_propagate_preserves_agent_wellformed hdec.1 hdec.2
    simpa [transitionPEM_phase4, hSettled, sw, dec] using hprop
  · simpa [transitionPEM_phase4, hSettled] using And.intro ha hb

set_option maxHeartbeats 800000 in
-- Full transition combines rank-delta and phase-4 structural invariants.
private theorem transitionPEM_preserves_agent_wellformed
    {n trank Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {s₀ s₁ : AgentState n} {x₀ x₁ : Opinion}
    (hs₀ : AgentWellFormed Rmax Emax Dmax s₀)
    (hs₁ : AgentWellFormed Rmax Emax Dmax s₁) :
    AgentWellFormed Rmax Emax Dmax
        ((PEMProtocol n trank Rmax Emax Dmax hn).δ ((s₀, x₀), (s₁, x₁))).1 ∧
      AgentWellFormed Rmax Emax Dmax
        ((PEMProtocol n trank Rmax Emax Dmax hn).δ ((s₀, x₀), (s₁, x₁))).2 := by
  have hrd :=
    rankDeltaOSSR_preserves_agent_wellformed
      (hn := hn) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) hs₀ hs₁
  have hpre :=
    transitionPEM_prePhase4_preserves_agent_wellformed
      (trank := trank) (x₀ := x₀) (x₁ := x₁) hrd
  simpa [PEMProtocol, protocolPEM, transitionPEM] using
    transitionPEM_phase4_preserves_agent_wellformed
      (x₀ := x₀) (x₁ := x₁) hpre.1 hpre.2

theorem WellFormed_step
    {n trank Rmax Emax Dmax : ℕ} (hn : 0 < n)
    (C : Config (AgentState n) Opinion n)
    (hC : WellFormed trank Rmax Emax Dmax C) :
    ∀ i j : Fin n,
      WellFormed trank Rmax Emax Dmax
        (C.step (PEMProtocol n trank Rmax Emax Dmax hn) i j) := by
  intro i j
  constructor
  · simpa [PEMProtocol, WellFormed] using
      generic_timer_preservation
        (n := n) (trank := trank) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        hn (by omega : 7 * (trank + 4) ≤ 7 * (trank + 4))
        C hC.1 i j
  · intro μ
    have hi : AgentWellFormed Rmax Emax Dmax (C i).1 := hC.2 i
    have hj : AgentWellFormed Rmax Emax Dmax (C j).1 := hC.2 j
    by_cases hij : i = j
    · subst j
      simpa [Config.step, WellFormed] using hC.2 μ
    · by_cases hμi : μ = i
      · subst μ
        have hpair :=
          transitionPEM_preserves_agent_wellformed
            (n := n) (trank := trank) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
            (hn := hn) (x₀ := (C i).2) (x₁ := (C j).2) hi hj
        simpa [Config.step, hij, WellFormed] using hpair.1
      · by_cases hμj : μ = j
        · subst μ
          have hpair :=
            transitionPEM_preserves_agent_wellformed
              (n := n) (trank := trank) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
              (hn := hn) (x₀ := (C i).2) (x₁ := (C j).2) hi hj
          simpa [Config.step, hij, hμi, WellFormed] using hpair.2
        · simpa [Config.step, hij, hμi, hμj, WellFormed] using hC.2 μ

/-- Generic faithful reset-completion contract.

The reset entry is the [12]-cited probabilistic window from `CorrectResetSeed`
to the completed answer epidemic.  This is the only cited reset obligation:
the race between answer spread and reset-counter drain is part of the cited
reset-completion window, rather than an exposed deterministic invariant over
all `EpidemicRegion` configurations. -/
structure CRSResetCompletion12Generic {n trank Rmax Emax Dmax : ℕ} (hn : 0 < n)
    (p_reset : ENNReal) (C_reset K_reset : ℕ) : Prop where
  resetProb_pos : 0 < p_reset
  resetProb_le_one : p_reset ≤ 1
  resetConstant_pos : 0 < C_reset
  resetWindow_quadratic : K_reset ≤ C_reset * n * n
  resetReach :
    ∀ (hn2 : 2 ≤ n) (C : Config (AgentState n) Opinion n),
      WellFormed trank Rmax Emax Dmax C →
      CorrectResetSeed C →
        p_reset ≤
          Probability.ProbHitWithin
            (PEMProtocol n trank Rmax Emax Dmax hn) hn2 C
            (EpidemicPhiGoal (majorityAnswer C)) K_reset

omit [Inhabited (Fin n × Fin n)] in
/-- Generic faithful CRS-to-silence wrapper retaining the product probability. -/
theorem CRS_to_silence_faithful_product_generic (hn4 : 4 ≤ n)
    (K_reset T_rank : ℕ)
    (p_reset rankProb : ENNReal) (C_reset : ℕ)
    (h12resetCompletion :
      CRSResetCompletion12Generic (n := n) (trank := trank) (Rmax := Rmax)
        (Emax := Emax) (Dmax := Dmax) (by omega : 0 < n)
        p_reset C_reset K_reset)
    (h12rank :
      ∀ (m : Answer) (D : Config (AgentState n) Opinion n),
        EpidemicPhiGoal m D →
        WellFormed trank Rmax Emax Dmax D →
        majorityAnswer D = m →
          rankProb ≤
            Probability.ProbHitWithin
              (PEMProtocol n trank Rmax Emax Dmax (by omega : 0 < n))
              (by omega : 2 ≤ n) D
              (OW_rankedEpidemicEndpoint m) T_rank) :
    ∀ C : Config (AgentState n) Opinion n,
      WellFormed trank Rmax Emax Dmax C →
      CorrectResetSeed C →
        p_reset * ((2 : ENNReal)⁻¹) * rankProb ≤
          Probability.ProbHitWithin
            (PEMProtocol n trank Rmax Emax Dmax (by omega : 0 < n))
            (by omega : 2 ≤ n) C OW_silenceEndpoint
            (K_reset + OW_answerEpidemicWindow n + T_rank) := by
  classical
  intro C hWF hSeed
  have hn0 : 0 < n := by omega
  have hn2 : 2 ≤ n := by omega
  set P := PEMProtocol n trank Rmax Emax Dmax hn0 with hP
  let MajInv : Config (AgentState n) Opinion n → Prop :=
    fun D => majorityAnswer D = majorityAnswer C
  let ChainInv : Config (AgentState n) Opinion n → Prop :=
    fun D => WellFormed trank Rmax Emax Dmax D ∧ MajInv D
  have hWFStep : ∀ D : Config (AgentState n) Opinion n,
      WellFormed trank Rmax Emax Dmax D →
      ∀ i j : Fin n, WellFormed trank Rmax Emax Dmax (D.step P i j) := by
    intro D hD i j
    simpa [P] using
      (WellFormed_step (n := n) (trank := trank) (Rmax := Rmax)
        (Emax := Emax) (Dmax := Dmax) hn0 D hD i j)
  have hMajInvStep : ∀ D : Config (AgentState n) Opinion n, MajInv D →
      ∀ i j : Fin n, MajInv (D.step P i j) := by
    intro D hD i j
    calc
      majorityAnswer (D.step P i j) = majorityAnswer D := by
        simpa [P, PEMProtocol] using
          (majorityAnswer_step_eq
            (trank := trank) (Rmax := Rmax)
            (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0) D i j)
      _ = majorityAnswer C := hD
  have hChainInvStep : ∀ D : Config (AgentState n) Opinion n, ChainInv D →
      ∀ i j : Fin n, ChainInv (D.step P i j) := by
    intro D hD i j
    exact ⟨hWFStep D hD.1 i j, hMajInvStep D hD.2 i j⟩
  have hReset :
      p_reset ≤
        Probability.ProbHitWithin P hn2 C
          (fun D => EpidemicPhiGoal (majorityAnswer C) D ∧ ChainInv D)
          K_reset := by
    have hResetRaw :
        p_reset ≤
          Probability.ProbHitWithin P hn2 C
            (EpidemicPhiGoal (majorityAnswer C)) K_reset := by
      simpa [P] using h12resetCompletion.resetReach hn2 C hWF hSeed
    rw [Probability.ProbHitWithin_eq_and_inv_of_invariant
      P hn2 C (EpidemicPhiGoal (majorityAnswer C)) ChainInv ⟨hWF, rfl⟩
      hChainInvStep K_reset]
    exact hResetRaw
  have hRankToSilence :
      ∀ D : Config (AgentState n) Opinion n,
        (EpidemicPhiGoal (majorityAnswer C) D ∧ ChainInv D) →
          rankProb ≤
            Probability.ProbHitWithin P hn2 D OW_silenceEndpoint T_rank := by
    intro D hD
    have hRankRaw :
        rankProb ≤
          Probability.ProbHitWithin P hn2 D
            (OW_rankedEpidemicEndpoint (majorityAnswer C)) T_rank := by
      simpa [P] using h12rank (majorityAnswer C) D hD.1 hD.2.1 hD.2.2
    exact hRankRaw.trans
      (Probability.ProbHitWithin_mono_goal P hn2 D
        (OW_rankedEpidemicEndpoint (majorityAnswer C)) OW_silenceEndpoint
        (fun E hE => OW_silenceEndpoint_of_rankedEpidemicEndpoint hE)
        T_rank)
  have hStrong :
      p_reset * rankProb ≤
        Probability.ProbHitWithin P hn2 C OW_silenceEndpoint
          (K_reset + T_rank) :=
    Probability.ProbHitWithin_add_ge_mul P hn2 C
      (fun D => EpidemicPhiGoal (majorityAnswer C) D ∧ ChainInv D) OW_silenceEndpoint
      K_reset T_rank p_reset rankProb hReset hRankToSilence
  have hWeak :
      p_reset * ((2 : ENNReal)⁻¹) * rankProb ≤ p_reset * rankProb := by
    have hmul :
        p_reset * ((2 : ENNReal)⁻¹) ≤ p_reset * (1 : ENNReal) := by
      exact mul_le_mul' le_rfl (by norm_num : ((2 : ENNReal)⁻¹) ≤ 1)
    have hmulRank :
        p_reset * ((2 : ENNReal)⁻¹) * rankProb ≤
          p_reset * (1 : ENNReal) * rankProb := by
      exact mul_le_mul' hmul le_rfl
    simpa [mul_assoc] using hmulRank
  have hTime :
      Probability.ProbHitWithin P hn2 C OW_silenceEndpoint (K_reset + T_rank) ≤
        Probability.ProbHitWithin P hn2 C OW_silenceEndpoint
          (K_reset + OW_answerEpidemicWindow n + T_rank) :=
    Probability.ProbHitWithin_mono_time P hn2 C OW_silenceEndpoint (by omega)
  exact hWeak.trans (hStrong.trans hTime)

omit [Inhabited (Fin n × Fin n)] in
/-- Generic faithful CRS-to-consensus wrapper retaining the product probability. -/
theorem CRS_to_consensus_faithful_product_generic (hn4 : 4 ≤ n)
    (K_reset T_rank : ℕ)
    (p_reset rankProb : ENNReal) (C_reset : ℕ)
    (h12resetCompletion :
      CRSResetCompletion12Generic (n := n) (trank := trank) (Rmax := Rmax)
        (Emax := Emax) (Dmax := Dmax) (by omega : 0 < n)
        p_reset C_reset K_reset)
    (h12rank :
      ∀ (m : Answer) (D : Config (AgentState n) Opinion n),
        EpidemicPhiGoal m D →
        WellFormed trank Rmax Emax Dmax D →
        majorityAnswer D = m →
          rankProb ≤
            Probability.ProbHitWithin
              (PEMProtocol n trank Rmax Emax Dmax (by omega : 0 < n))
              (by omega : 2 ≤ n) D
              (OW_rankedEpidemicEndpoint m) T_rank) :
    ∀ C : Config (AgentState n) Opinion n,
      WellFormed trank Rmax Emax Dmax C →
      CorrectResetSeed C →
        p_reset * ((2 : ENNReal)⁻¹) * rankProb ≤
          Probability.ProbHitWithin
            (PEMProtocol n trank Rmax Emax Dmax (by omega : 0 < n))
            (by omega : 2 ≤ n) C IsConsensusConfig
            (K_reset + OW_answerEpidemicWindow n + T_rank) := by
  classical
  intro C hWF hSeed
  have hn0 : 0 < n := by omega
  have hn2 : 2 ≤ n := by omega
  set P := PEMProtocol n trank Rmax Emax Dmax hn0 with hP
  have hSilence :
      p_reset * ((2 : ENNReal)⁻¹) * rankProb ≤
        Probability.ProbHitWithin P hn2 C OW_silenceEndpoint
          (K_reset + OW_answerEpidemicWindow n + T_rank) := by
    simpa [P] using
      (CRS_to_silence_faithful_product_generic
        (n := n) (trank := trank) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        hn4 K_reset T_rank p_reset rankProb C_reset h12resetCompletion h12rank
        C hWF hSeed)
  exact hSilence.trans
    (Probability.ProbHitWithin_mono_goal P hn2 C
      OW_silenceEndpoint IsConsensusConfig
      (fun D hD => isConsensusConfig_of_InSswap_phiCount_zero hD.1 hD.2.1 hD.2.2)
      (K_reset + OW_answerEpidemicWindow n + T_rank))

/-- Generic-trank end-to-end keystone.  This is the coupled keystone with every
phase window taken from `GenericTrank`. -/
theorem PEM_expectedParallelTime_optimal_generic (hn4 : 4 ≤ n)
    (hRmax : n ≤ Rmax) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (C_rank T_timer K_reset T_rank T_rerank : ℕ)
    (p_reset : ENNReal) (C_reset : ℕ)
    (hTimerStep : ∀ D : Config (AgentState n) Opinion n,
      IsTimerBoundedConfig T_timer D → ∀ i j : Fin n,
        IsTimerBoundedConfig T_timer
          (D.step (PEMProtocol n trank Rmax Emax Dmax (by omega : 0 < n)) i j))
    (h12ranking :
      ∀ C : Config (AgentState n) Opinion n,
        WellFormed trank Rmax Emax Dmax C →
          IsTimerBoundedConfig T_timer C →
          Probability.expectedHittingTime
            (PEMProtocol n trank Rmax Emax Dmax (by omega : 0 < n))
            (by omega : 2 ≤ n) C
            (fun D => (InSrank D ∧ MedianTimerAtLeast 35 D ∧
              WellFormed trank Rmax Emax Dmax D ∧
              IsTimerBoundedConfig T_timer D) ∨ IsConsensusConfig D) ≤
            ((C_rank * n * n : ℕ) : ENNReal))
    (h12resetCompletion :
      CRSResetCompletion12Generic (n := n) (trank := trank) (Rmax := Rmax)
        (Emax := Emax) (Dmax := Dmax) (by omega : 0 < n)
        p_reset C_reset K_reset)
    (h12rank :
      ∀ (m : Answer) (D : Config (AgentState n) Opinion n),
        EpidemicPhiGoal m D →
        WellFormed trank Rmax Emax Dmax D →
        majorityAnswer D = m →
          ((2 : ENNReal)⁻¹) ≤
            Probability.ProbHitWithin
              (PEMProtocol n trank Rmax Emax Dmax (by omega : 0 < n))
              (by omega : 2 ≤ n) D
              (OW_rankedEpidemicEndpoint m) T_rank)
    (h12reRank :
      ∀ C : Config (AgentState n) Opinion n,
        WellFormed trank Rmax Emax Dmax C →
        IsTimerBoundedConfig T_timer C →
        ¬ (InSswap C ∧ MedianTimerAtLeast 35 C) →
          ((2 : ENNReal)⁻¹) ≤
            Probability.ProbHitWithin
              (PEMProtocol n trank Rmax Emax Dmax (by omega : 0 < n))
              (by omega : 2 ≤ n) C
              (fun D => (InSswap D ∧ MedianTimerAtLeast 35 D) ∨
                IsConsensusConfig D) T_rerank) :
    ∀ C₀ : Config (AgentState n) Opinion n,
      WellFormed trank Rmax Emax Dmax C₀ →
      IsTimerBoundedConfig T_timer C₀ →
      Probability.expectedParallelTimeToConsensus
        (PEMProtocol n trank Rmax Emax Dmax (by omega : 0 < n))
        (by omega : 2 ≤ n) C₀ ≤
        (((OW_globalWindow n C_rank T_timer K_reset T_rank T_rerank : ℕ) : ENNReal) *
          (p_reset * ((128 : ENNReal)⁻¹))⁻¹ / n) := by
  classical
  intro C₀ hWF₀ hTimerT₀
  have hn0 : 0 < n := by omega
  have hn2 : 2 ≤ n := by omega
  set P := PEMProtocol n trank Rmax Emax Dmax hn0 with hP
  let Inv : Config (AgentState n) Opinion n → Prop :=
    fun C => WellFormed trank Rmax Emax Dmax C ∧
      IsTimerBoundedConfig T_timer C
  let RankTarget : Config (AgentState n) Opinion n → Prop :=
    fun C =>
      InSrank C ∧ MedianTimerAtLeast 35 C ∧
        WellFormed trank Rmax Emax Dmax C ∧
        IsTimerBoundedConfig T_timer C
  let RankOrConsensus : Config (AgentState n) Opinion n → Prop :=
    fun C => RankTarget C ∨ IsConsensusConfig C
  let Live35 : Config (AgentState n) Opinion n → Prop :=
    fun C => InSswap C ∧ MedianTimerAtLeast 35 C
  let LiveOrConsensus : Config (AgentState n) Opinion n → Prop :=
    fun C => Live35 C ∨ IsConsensusConfig C
  let Live35Target : Config (AgentState n) Opinion n → Prop :=
    fun C => Live35 C ∧ Inv C
  let LiveOrConsensusTarget : Config (AgentState n) Opinion n → Prop :=
    fun C => LiveOrConsensus C ∧ Inv C
  let DecisionTarget : Config (AgentState n) Opinion n → Prop :=
    (DecisionProductiveTarget : Config (AgentState n) Opinion n → Prop)
  let DecisionMid : Config (AgentState n) Opinion n → Prop :=
    fun C => DecisionTarget C ∧ Inv C
  let ConsOrCRS : Config (AgentState n) Opinion n → Prop :=
    fun C => IsConsensusConfig C ∨ CorrectResetSeed C
  let ConsOrCRSMid : Config (AgentState n) Opinion n → Prop :=
    fun C => ConsOrCRS C ∧ Inv C
  let KLive : ℕ := OW_liveConsensusWindow n T_timer K_reset T_rank
  let K : ℕ := OW_globalWindow n C_rank T_timer K_reset T_rank T_rerank
  have hKpos : 0 < K := by
    have hDecisionPos : 0 < decisionWindow n := by
      dsimp [decisionWindow]
      exact Nat.mul_pos (Nat.mul_pos (by norm_num) (by omega)) (by omega)
    have hLivePos : 0 < OW_liveConsensusWindow n T_timer K_reset T_rank := by
      dsimp [OW_liveConsensusWindow]
      omega
    dsimp [K, OW_globalWindow]
    omega
  haveI : NeZero K := ⟨Nat.pos_iff_ne_zero.mp hKpos⟩
  have hp_le_one : p_reset * ((128 : ENNReal)⁻¹) ≤ 1 := by
    exact (mul_le_mul' h12resetCompletion.resetProb_le_one
      (by norm_num : ((128 : ENNReal)⁻¹) ≤ 1)).trans (by simp)
  have hInvStep : ∀ C : Config (AgentState n) Opinion n, Inv C →
      ∀ i j : Fin n, Inv (C.step P i j) := by
    intro C hC i j
    constructor
    · simpa [P, Inv] using
        (WellFormed_step (n := n) (trank := trank) (Rmax := Rmax)
          (Emax := Emax) (Dmax := Dmax) hn0 C hC.1 i j)
    · simpa [P, Inv] using hTimerStep C hC.2 i j
  have hConsOrCRSToConsensus :
      ∀ C : Config (AgentState n) Opinion n, ConsOrCRSMid C →
        p_reset * ((4 : ENNReal)⁻¹) ≤
          Probability.ProbHitWithin P hn2 C IsConsensusConfig
            (K_reset + OW_answerEpidemicWindow n + T_rank) := by
    intro C hC
    rcases hC with ⟨hEvent, hInvC⟩
    rcases hEvent with hCons | hSeed
    · have hOne : (1 : ENNReal) ≤
          Probability.ProbHitWithin P hn2 C IsConsensusConfig
            (K_reset + OW_answerEpidemicWindow n + T_rank) := by
        calc
          (1 : ENNReal) = Probability.probReached P hn2 C IsConsensusConfig 0 := by
              exact (Probability.probReached_zero_of_goal P hn2 C IsConsensusConfig hCons).symm
          _ ≤ Probability.ProbHitWithin P hn2 C IsConsensusConfig 0 :=
              Probability.probReached_le_ProbHitWithin P hn2 C IsConsensusConfig 0
          _ ≤ Probability.ProbHitWithin P hn2 C IsConsensusConfig
                (K_reset + OW_answerEpidemicWindow n + T_rank) :=
              Probability.ProbHitWithin_mono_time P hn2 C IsConsensusConfig (Nat.zero_le _)
      have hp4_le_one : p_reset * ((4 : ENNReal)⁻¹) ≤ 1 := by
        exact (mul_le_mul' h12resetCompletion.resetProb_le_one
          (by norm_num : ((4 : ENNReal)⁻¹) ≤ 1)).trans (by simp)
      exact hp4_le_one.trans hOne
    · have hCRS :
          p_reset * ((2 : ENNReal)⁻¹) * ((2 : ENNReal)⁻¹) ≤
            Probability.ProbHitWithin P hn2 C IsConsensusConfig
              (K_reset + OW_answerEpidemicWindow n + T_rank) := by
        simpa [P] using
          (CRS_to_consensus_faithful_product_generic
            (n := n) (trank := trank) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
            hn4 K_reset T_rank p_reset ((2 : ENNReal)⁻¹) C_reset
            h12resetCompletion h12rank C hInvC.1 hSeed)
      have hprod :
          p_reset * ((2 : ENNReal)⁻¹) * ((2 : ENNReal)⁻¹) =
            p_reset * ((4 : ENNReal)⁻¹) := by
        have hhalf :
            ((2 : ENNReal)⁻¹) * ((2 : ENNReal)⁻¹) = ((4 : ENNReal)⁻¹) := by
          rw [← ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num))]
          norm_num
        rw [mul_assoc, hhalf]
      simpa [hprod] using hCRS
  have hDecisionToConsOrCRS :
      ∀ C : Config (AgentState n) Opinion n, DecisionMid C →
        ((2 : ENNReal)⁻¹) ≤
          Probability.ProbHitWithin P hn2 C ConsOrCRSMid
            (OW_macLiveWindow n T_timer) := by
    intro C hC
    rcases hC with ⟨hDecision, hInvC⟩
    rcases hDecision with hMAC | hRest
    · have hBase :
          ((2 : ENNReal)⁻¹) ≤
            Probability.ProbHitWithin P hn2 C ConsOrCRS
              (OW_macLiveWindow n T_timer) := by
        simpa [P, ConsOrCRS, OW_macLiveWindow] using
          (generic_MAClive_to_consensus_or_crs_window
            (n := n) (trank := trank) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
            hn4 hn0 hRmax hEmax hDmax T_timer C
            hMAC.1 hMAC.2.1 hMAC.2.2 hInvC.2)
      rw [Probability.ProbHitWithin_eq_and_inv_of_invariant
        P hn2 C ConsOrCRS Inv hInvC hInvStep (OW_macLiveWindow n T_timer)]
      exact hBase
    · rcases hRest with hCons | hSeed
      · have hGoalC : ConsOrCRSMid C := ⟨Or.inl hCons, hInvC⟩
        have hOne : (1 : ENNReal) ≤
            Probability.ProbHitWithin P hn2 C ConsOrCRSMid
              (OW_macLiveWindow n T_timer) := by
          calc
            (1 : ENNReal) =
                Probability.probReached P hn2 C ConsOrCRSMid 0 := by
                  exact (Probability.probReached_zero_of_goal P hn2 C
                    ConsOrCRSMid hGoalC).symm
            _ ≤ Probability.ProbHitWithin P hn2 C ConsOrCRSMid 0 :=
                Probability.probReached_le_ProbHitWithin P hn2 C ConsOrCRSMid 0
            _ ≤ Probability.ProbHitWithin P hn2 C ConsOrCRSMid
                  (OW_macLiveWindow n T_timer) :=
                Probability.ProbHitWithin_mono_time P hn2 C ConsOrCRSMid
                  (Nat.zero_le _)
        exact le_trans (by norm_num : ((2 : ENNReal)⁻¹) ≤ 1) hOne
      · have hGoalC : ConsOrCRSMid C := ⟨Or.inr hSeed, hInvC⟩
        have hOne : (1 : ENNReal) ≤
            Probability.ProbHitWithin P hn2 C ConsOrCRSMid
              (OW_macLiveWindow n T_timer) := by
          calc
            (1 : ENNReal) =
                Probability.probReached P hn2 C ConsOrCRSMid 0 := by
                  exact (Probability.probReached_zero_of_goal P hn2 C
                    ConsOrCRSMid hGoalC).symm
            _ ≤ Probability.ProbHitWithin P hn2 C ConsOrCRSMid 0 :=
                Probability.probReached_le_ProbHitWithin P hn2 C ConsOrCRSMid 0
            _ ≤ Probability.ProbHitWithin P hn2 C ConsOrCRSMid
                  (OW_macLiveWindow n T_timer) :=
                Probability.ProbHitWithin_mono_time P hn2 C ConsOrCRSMid
                  (Nat.zero_le _)
        exact le_trans (by norm_num : ((2 : ENNReal)⁻¹) ≤ 1) hOne
  have hLiveToConsensus :
      ∀ C : Config (AgentState n) Opinion n, Live35Target C →
        p_reset * ((32 : ENNReal)⁻¹) ≤
          Probability.ProbHitWithin P hn2 C IsConsensusConfig KLive := by
    intro C hLiveTarget
    rcases hLiveTarget with ⟨hLive, hInvC⟩
    have hDecisionBase :
        ((4 : ENNReal)⁻¹) ≤
          Probability.ProbHitWithin P hn2 C DecisionTarget (decisionWindow n) := by
      simpa [P, DecisionTarget] using
        (generic_decision_before_timer_zero
          (n := n) (trank := trank) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
          hn4 hn0 hRmax hEmax hDmax C hLive.1 hLive.2)
    have hDecision :
        ((4 : ENNReal)⁻¹) ≤
          Probability.ProbHitWithin P hn2 C DecisionMid (decisionWindow n) := by
      rw [Probability.ProbHitWithin_eq_and_inv_of_invariant
        P hn2 C DecisionTarget Inv hInvC hInvStep (decisionWindow n)]
      exact hDecisionBase
    have hAB :
        ((4 : ENNReal)⁻¹) * ((2 : ENNReal)⁻¹) ≤
          Probability.ProbHitWithin P hn2 C ConsOrCRSMid
            (decisionWindow n + OW_macLiveWindow n T_timer) :=
      Probability.ProbHitWithin_add_ge_mul P hn2 C DecisionMid ConsOrCRSMid
        (decisionWindow n) (OW_macLiveWindow n T_timer)
        ((4 : ENNReal)⁻¹) ((2 : ENNReal)⁻¹)
        hDecision hDecisionToConsOrCRS
    have hChain :
        (((4 : ENNReal)⁻¹) * ((2 : ENNReal)⁻¹)) *
            (p_reset * ((4 : ENNReal)⁻¹)) ≤
          Probability.ProbHitWithin P hn2 C IsConsensusConfig
            ((decisionWindow n + OW_macLiveWindow n T_timer) +
              (K_reset + OW_answerEpidemicWindow n + T_rank)) :=
      Probability.ProbHitWithin_add_ge_mul P hn2 C ConsOrCRSMid IsConsensusConfig
        (decisionWindow n + OW_macLiveWindow n T_timer)
        (K_reset + OW_answerEpidemicWindow n + T_rank)
        (((4 : ENNReal)⁻¹) * ((2 : ENNReal)⁻¹))
        (p_reset * ((4 : ENNReal)⁻¹))
        hAB hConsOrCRSToConsensus
    have h42 :
        ((4 : ENNReal)⁻¹) * ((2 : ENNReal)⁻¹) = ((8 : ENNReal)⁻¹) := by
      rw [← ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num))]
      norm_num
    have h84 :
        ((8 : ENNReal)⁻¹) * ((4 : ENNReal)⁻¹) = ((32 : ENNReal)⁻¹) := by
      rw [← ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num))]
      norm_num
    have hprod :
        ((4 : ENNReal)⁻¹) * ((2 : ENNReal)⁻¹) *
            (p_reset * ((4 : ENNReal)⁻¹)) =
          p_reset * ((32 : ENNReal)⁻¹) := by
      calc
        ((4 : ENNReal)⁻¹) * ((2 : ENNReal)⁻¹) *
            (p_reset * ((4 : ENNReal)⁻¹))
            = p_reset * (((4 : ENNReal)⁻¹) * ((2 : ENNReal)⁻¹) *
                ((4 : ENNReal)⁻¹)) := by ac_rfl
        _ = p_reset * (((8 : ENNReal)⁻¹) * ((4 : ENNReal)⁻¹)) := by rw [h42]
        _ = p_reset * ((32 : ENNReal)⁻¹) := by rw [h84]
    simpa [KLive, OW_liveConsensusWindow, hprod] using hChain
  have hwin : ∀ C : Config (AgentState n) Opinion n, Inv C →
      ¬ IsConsensusConfig C →
      p_reset * ((128 : ENNReal)⁻¹) ≤
        Probability.ProbHitWithin P hn2 C IsConsensusConfig K := by
    intro C hInvC _hNot
    have hRankE : Probability.expectedHittingTime P hn2 C RankOrConsensus ≤
        ((C_rank * n * n : ℕ) : ENNReal) := by
      simpa [P, RankOrConsensus, RankTarget, Inv] using
        h12ranking C hInvC.1 hInvC.2
    have hRankW : 2 * (C_rank * n * n) ≤ (2 * C_rank * n * n) + 1 := by nlinarith
    have hRankPH : ((2 : ENNReal)⁻¹) ≤
        Probability.ProbHitWithin P hn2 C RankOrConsensus (2 * C_rank * n * n) :=
      Probability.ProbHitWithin_ge_half_of_expectedHittingTime_le
        P hn2 C RankOrConsensus hRankE hRankW
    have hLiveOrConsensusToConsensus :
        ∀ E : Config (AgentState n) Opinion n, LiveOrConsensusTarget E →
          p_reset * ((32 : ENNReal)⁻¹) ≤
            Probability.ProbHitWithin P hn2 E IsConsensusConfig KLive := by
      intro E hE
      rcases hE with ⟨hEvent, hInvE⟩
      rcases hEvent with hLiveE | hConsE
      · exact hLiveToConsensus E ⟨hLiveE, hInvE⟩
      · have hOne : (1 : ENNReal) ≤
            Probability.ProbHitWithin P hn2 E IsConsensusConfig KLive := by
          calc
            (1 : ENNReal) =
                Probability.probReached P hn2 E IsConsensusConfig 0 := by
                  exact (Probability.probReached_zero_of_goal P hn2 E
                    IsConsensusConfig hConsE).symm
            _ ≤ Probability.ProbHitWithin P hn2 E IsConsensusConfig 0 :=
                Probability.probReached_le_ProbHitWithin P hn2 E IsConsensusConfig 0
            _ ≤ Probability.ProbHitWithin P hn2 E IsConsensusConfig KLive :=
                Probability.ProbHitWithin_mono_time P hn2 E IsConsensusConfig
                  (Nat.zero_le _)
        have hp32_le_one : p_reset * ((32 : ENNReal)⁻¹) ≤ 1 := by
          exact (mul_le_mul' h12resetCompletion.resetProb_le_one
            (by norm_num : ((32 : ENNReal)⁻¹) ≤ 1)).trans (by simp)
        exact hp32_le_one.trans hOne
    have hAfterRank :
        ∀ D : Config (AgentState n) Opinion n, RankOrConsensus D →
          p_reset * ((64 : ENNReal)⁻¹) ≤
            Probability.ProbHitWithin P hn2 D IsConsensusConfig (T_rerank + KLive) := by
      intro D hD
      rcases hD with hRankD | hConsD
      · have hInvD : Inv D := hRankD.2.2
        by_cases hLive : Live35 D
        · have hGoalD : Live35Target D := ⟨hLive, hInvD⟩
          have hBase :
              p_reset * ((32 : ENNReal)⁻¹) ≤
                Probability.ProbHitWithin P hn2 D IsConsensusConfig KLive :=
            hLiveToConsensus D hGoalD
          have hBase' :
              p_reset * ((32 : ENNReal)⁻¹) ≤
                Probability.ProbHitWithin P hn2 D IsConsensusConfig
                  (T_rerank + KLive) :=
            hBase.trans
              (Probability.ProbHitWithin_mono_time P hn2 D IsConsensusConfig
                (by omega : KLive ≤ T_rerank + KLive))
          have hweak :
              p_reset * ((64 : ENNReal)⁻¹) ≤
                p_reset * ((32 : ENNReal)⁻¹) :=
            mul_le_mul' le_rfl (by norm_num : ((64 : ENNReal)⁻¹) ≤ ((32 : ENNReal)⁻¹))
          exact hweak.trans hBase'
        · have hBase :
              ((2 : ENNReal)⁻¹) ≤
                Probability.ProbHitWithin P hn2 D LiveOrConsensus T_rerank := by
            simpa [P, LiveOrConsensus, Live35] using
              h12reRank D hInvD.1 hInvD.2 hLive
          have hRerank :
              ((2 : ENNReal)⁻¹) ≤
                Probability.ProbHitWithin P hn2 D LiveOrConsensusTarget T_rerank := by
            rw [Probability.ProbHitWithin_eq_and_inv_of_invariant
              P hn2 D LiveOrConsensus Inv hInvD hInvStep T_rerank]
            exact hBase
          have hChain :
              ((2 : ENNReal)⁻¹) * (p_reset * ((32 : ENNReal)⁻¹)) ≤
                Probability.ProbHitWithin P hn2 D IsConsensusConfig
                  (T_rerank + KLive) :=
            Probability.ProbHitWithin_add_ge_mul P hn2 D
              LiveOrConsensusTarget IsConsensusConfig
              T_rerank KLive
              ((2 : ENNReal)⁻¹) (p_reset * ((32 : ENNReal)⁻¹))
              hRerank hLiveOrConsensusToConsensus
          have hprod :
              ((2 : ENNReal)⁻¹) * (p_reset * ((32 : ENNReal)⁻¹)) =
                p_reset * ((64 : ENNReal)⁻¹) := by
            have h2_32 :
                ((2 : ENNReal)⁻¹) * ((32 : ENNReal)⁻¹) =
                  ((64 : ENNReal)⁻¹) := by
              rw [← ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num))]
              norm_num
            calc
              ((2 : ENNReal)⁻¹) * (p_reset * ((32 : ENNReal)⁻¹))
                  = p_reset * (((2 : ENNReal)⁻¹) * ((32 : ENNReal)⁻¹)) := by
                    ac_rfl
              _ = p_reset * ((64 : ENNReal)⁻¹) := by rw [h2_32]
          simpa [hprod] using hChain
      · have hOne : (1 : ENNReal) ≤
            Probability.ProbHitWithin P hn2 D IsConsensusConfig
              (T_rerank + KLive) := by
          calc
            (1 : ENNReal) =
                Probability.probReached P hn2 D IsConsensusConfig 0 := by
                  exact (Probability.probReached_zero_of_goal P hn2 D
                    IsConsensusConfig hConsD).symm
            _ ≤ Probability.ProbHitWithin P hn2 D IsConsensusConfig 0 :=
                Probability.probReached_le_ProbHitWithin P hn2 D IsConsensusConfig 0
            _ ≤ Probability.ProbHitWithin P hn2 D IsConsensusConfig
                  (T_rerank + KLive) :=
                Probability.ProbHitWithin_mono_time P hn2 D IsConsensusConfig
                  (Nat.zero_le _)
        have hp64_le_one : p_reset * ((64 : ENNReal)⁻¹) ≤ 1 := by
          exact (mul_le_mul' h12resetCompletion.resetProb_le_one
            (by norm_num : ((64 : ENNReal)⁻¹) ≤ 1)).trans (by simp)
        exact hp64_le_one.trans hOne
    have hChain : ((2 : ENNReal)⁻¹) * (p_reset * ((64 : ENNReal)⁻¹)) ≤
        Probability.ProbHitWithin P hn2 C IsConsensusConfig
          (2 * C_rank * n * n + (T_rerank + KLive)) :=
      Probability.ProbHitWithin_add_ge_mul P hn2 C RankOrConsensus IsConsensusConfig
        (2 * C_rank * n * n) (T_rerank + KLive)
        ((2 : ENNReal)⁻¹) (p_reset * ((64 : ENNReal)⁻¹))
        hRankPH hAfterRank
    have hprod :
        ((2 : ENNReal)⁻¹) * (p_reset * ((64 : ENNReal)⁻¹)) =
          p_reset * ((128 : ENNReal)⁻¹) := by
      have h2_64 :
          ((2 : ENNReal)⁻¹) * ((64 : ENNReal)⁻¹) = ((128 : ENNReal)⁻¹) := by
        rw [← ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num))]
        norm_num
      calc
        ((2 : ENNReal)⁻¹) * (p_reset * ((64 : ENNReal)⁻¹))
            = p_reset * (((2 : ENNReal)⁻¹) * ((64 : ENNReal)⁻¹)) := by ac_rfl
        _ = p_reset * ((128 : ENNReal)⁻¹) := by rw [h2_64]
    simpa [K, OW_globalWindow, hprod, Nat.add_assoc, add_assoc] using hChain
  simpa [Probability.expectedParallelTimeToConsensus, P, Inv, K] using
    (Probability.expectedParallelTime_le_window_mul_inv_of_invariant
      P hn2 C₀ IsConsensusConfig Inv K (p_reset * ((128 : ENNReal)⁻¹))
      hp_le_one ⟨hWF₀, hTimerT₀⟩ hInvStep hwin)

/-- Concrete constant timer cap for `trank = 1`. -/
def PEM_trank1_timer : ℕ := 35

/-- Instantiated generic keystone at `trank = 1`, hence `T_timer = 35`. -/
theorem PEM_expectedParallelTime_On (hn4 : 4 ≤ n)
    (hRmax : n ≤ Rmax) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (C_rank K_reset T_rank T_rerank : ℕ)
    (p_reset : ENNReal) (C_reset : ℕ)
    (h12ranking :
      ∀ C : Config (AgentState n) Opinion n,
        WellFormed 1 Rmax Emax Dmax C →
          Probability.expectedHittingTime
            (PEMProtocol n 1 Rmax Emax Dmax (by omega : 0 < n))
            (by omega : 2 ≤ n) C
            (fun D => (InSrank D ∧ MedianTimerAtLeast 35 D ∧
              WellFormed 1 Rmax Emax Dmax D ∧
              IsTimerBoundedConfig PEM_trank1_timer D) ∨ IsConsensusConfig D) ≤
            ((C_rank * n * n : ℕ) : ENNReal))
    (h12resetCompletion :
      CRSResetCompletion12Generic (n := n) (trank := 1) (Rmax := Rmax)
        (Emax := Emax) (Dmax := Dmax) (by omega : 0 < n)
        p_reset C_reset K_reset)
    (h12rank :
      ∀ (m : Answer) (D : Config (AgentState n) Opinion n),
        EpidemicPhiGoal m D →
        WellFormed 1 Rmax Emax Dmax D →
        majorityAnswer D = m →
          ((2 : ENNReal)⁻¹) ≤
            Probability.ProbHitWithin
              (PEMProtocol n 1 Rmax Emax Dmax (by omega : 0 < n))
              (by omega : 2 ≤ n) D
              (OW_rankedEpidemicEndpoint m) T_rank)
    (h12reRank :
      ∀ C : Config (AgentState n) Opinion n,
        WellFormed 1 Rmax Emax Dmax C →
        ¬ (InSswap C ∧ MedianTimerAtLeast 35 C) →
          ((2 : ENNReal)⁻¹) ≤
            Probability.ProbHitWithin
              (PEMProtocol n 1 Rmax Emax Dmax (by omega : 0 < n))
              (by omega : 2 ≤ n) C
              (fun D => (InSswap D ∧ MedianTimerAtLeast 35 D) ∨
                IsConsensusConfig D) T_rerank) :
    ∀ C₀ : Config (AgentState n) Opinion n,
      WellFormed 1 Rmax Emax Dmax C₀ →
      Probability.expectedParallelTimeToConsensus
        (PEMProtocol n 1 Rmax Emax Dmax (by omega : 0 < n))
        (by omega : 2 ≤ n) C₀ ≤
        (((OW_globalWindow n C_rank PEM_trank1_timer K_reset T_rank T_rerank : ℕ) :
            ENNReal) *
          (p_reset * ((128 : ENNReal)⁻¹))⁻¹ / n) := by
  intro C₀ hWF₀
  have hTimerStep : ∀ D : Config (AgentState n) Opinion n,
      IsTimerBoundedConfig PEM_trank1_timer D → ∀ i j : Fin n,
        IsTimerBoundedConfig PEM_trank1_timer
          (D.step (PEMProtocol n 1 Rmax Emax Dmax (by omega : 0 < n)) i j) := by
    intro D hD i j
    simpa [PEM_trank1_timer] using
      (generic_timer_preservation
        (n := n) (trank := 1) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        (by omega : 0 < n) (by norm_num : 7 * (1 + 4) ≤ 35) D hD i j)
  exact
    (PEM_expectedParallelTime_optimal_generic
      (n := n) (trank := 1) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      hn4 hRmax hEmax hDmax C_rank PEM_trank1_timer K_reset T_rank T_rerank
      p_reset C_reset hTimerStep
      (fun C hWF _hT =>
        by
          simpa [PEM_trank1_timer] using h12ranking C hWF)
      h12resetCompletion
      h12rank
      (fun C hWF _hT hNot =>
        by
          simpa [PEM_trank1_timer] using h12reRank C hWF hNot)
      C₀
      (by simpa [PEM_trank1_timer] using hWF₀)
      (by simpa [PEM_trank1_timer, WellFormed] using hWF₀.1))

omit [Inhabited (Fin n × Fin n)] in
/-- Explicit quadratic sequential window for the `trank = 1` instantiation. -/
theorem OW_globalWindow_trank1_quadratic
    {K_reset C_reset T_rank C_T_rank T_rerank C_T_rerank C_rank : ℕ}
    (hK : K_reset ≤ C_reset * n * n)
    (hRank : T_rank ≤ C_T_rank * n * n)
    (hRerank : T_rerank ≤ C_T_rerank * n * n) :
    OW_globalWindow n C_rank PEM_trank1_timer K_reset T_rank T_rerank ≤
      (2 * C_rank + C_reset + C_T_rank + C_T_rerank + 76) * n * n := by
  have hnn : n * (n - 1) ≤ n * n :=
    Nat.mul_le_mul_left n (Nat.sub_le n 1)
  dsimp [OW_globalWindow, OW_liveConsensusWindow, decisionWindow,
    OW_macLiveWindow, OW_answerEpidemicWindow, PEM_trank1_timer]
  nlinarith

omit [Inhabited (Fin n × Fin n)] in
/-- Arithmetic helper for converting a quadratic sequential window into a
linear parallel-time bound after division by `n`. -/
theorem ennreal_quadratic_nat_mul_div_cancel
    {c q n : ℕ} (hn : 0 < n) :
    (((c * n * n : ℕ) : ENNReal) * (q : ENNReal) / n) =
      ((q * c * n : ℕ) : ENNReal) := by
  have hn_ne : (↑n : ENNReal) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hn_ne_top : (↑n : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top n
  rw [show (c * n * n : ℕ) = c * (n * n) from by ring]
  rw [show (q * c * n : ℕ) = q * (c * n) from by ring]
  push_cast [Nat.cast_mul]
  rw [div_eq_mul_inv]
  calc
    ↑c * (↑n * ↑n) * ↑q * (↑n : ENNReal)⁻¹
        = ↑q * ↑c * (↑n * (↑n * (↑n : ENNReal)⁻¹)) := by ac_rfl
    _ = ↑q * ↑c * (↑n * 1) := by
        rw [ENNReal.mul_inv_cancel hn_ne hn_ne_top]
    _ = ↑q * (↑c * ↑n) := by simp [mul_assoc]

omit [Inhabited (Fin n × Fin n)] in
/-- Explicit linear constant for the `trank = 1` end-to-end theorem when the
cited reset success probability is fixed at `1/2`. -/
def PEM_On_explicit_linearConstant
    (C_rank C_reset C_T_rank C_T_rerank : ℕ) : ℕ :=
  256 * (2 * C_rank + C_reset + C_T_rank + C_T_rerank + 76)

/-- Explicit `O(n)` corollary at `trank = 1`.

The reset success probability is fixed to the absolute constant `1/2`; the
four window constants are ordinary natural constants, folded into the explicit
linear coefficient `PEM_On_explicit_linearConstant`. -/
theorem PEM_expectedParallelTime_On_explicit (hn4 : 4 ≤ n)
    (hRmax : n ≤ Rmax) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (C_rank C_reset C_T_rank C_T_rerank K_reset T_rank T_rerank : ℕ)
    (h12ranking :
      ∀ C : Config (AgentState n) Opinion n,
        WellFormed 1 Rmax Emax Dmax C →
          Probability.expectedHittingTime
            (PEMProtocol n 1 Rmax Emax Dmax (by omega : 0 < n))
            (by omega : 2 ≤ n) C
            (fun D => (InSrank D ∧ MedianTimerAtLeast 35 D ∧
              WellFormed 1 Rmax Emax Dmax D ∧
              IsTimerBoundedConfig PEM_trank1_timer D) ∨ IsConsensusConfig D) ≤
            ((C_rank * n * n : ℕ) : ENNReal))
    (h12resetCompletion :
      CRSResetCompletion12Generic (n := n) (trank := 1) (Rmax := Rmax)
        (Emax := Emax) (Dmax := Dmax) (by omega : 0 < n)
        ((2 : ENNReal)⁻¹) C_reset K_reset)
    (h12rank :
      ∀ (m : Answer) (D : Config (AgentState n) Opinion n),
        EpidemicPhiGoal m D →
        WellFormed 1 Rmax Emax Dmax D →
        majorityAnswer D = m →
          ((2 : ENNReal)⁻¹) ≤
            Probability.ProbHitWithin
              (PEMProtocol n 1 Rmax Emax Dmax (by omega : 0 < n))
              (by omega : 2 ≤ n) D
              (OW_rankedEpidemicEndpoint m) T_rank)
    (h12reRank :
      ∀ C : Config (AgentState n) Opinion n,
        WellFormed 1 Rmax Emax Dmax C →
        ¬ (InSswap C ∧ MedianTimerAtLeast 35 C) →
          ((2 : ENNReal)⁻¹) ≤
            Probability.ProbHitWithin
              (PEMProtocol n 1 Rmax Emax Dmax (by omega : 0 < n))
              (by omega : 2 ≤ n) C
              (fun D => (InSswap D ∧ MedianTimerAtLeast 35 D) ∨
                IsConsensusConfig D) T_rerank)
    (hRankWindow : T_rank ≤ C_T_rank * n * n)
    (hRerankWindow : T_rerank ≤ C_T_rerank * n * n) :
    ∀ C₀ : Config (AgentState n) Opinion n,
      WellFormed 1 Rmax Emax Dmax C₀ →
      Probability.expectedParallelTimeToConsensus
        (PEMProtocol n 1 Rmax Emax Dmax (by omega : 0 < n))
        (by omega : 2 ≤ n) C₀ ≤
        ((PEM_On_explicit_linearConstant
          C_rank C_reset C_T_rank C_T_rerank * n : ℕ) : ENNReal) := by
  intro C₀ hWF₀
  have hn0 : 0 < n := by omega
  have hBase :=
    PEM_expectedParallelTime_On
      (n := n) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      hn4 hRmax hEmax hDmax C_rank K_reset T_rank T_rerank
      ((2 : ENNReal)⁻¹) C_reset
      h12ranking h12resetCompletion h12rank h12reRank C₀ hWF₀
  let c : ℕ := 2 * C_rank + C_reset + C_T_rank + C_T_rerank + 76
  have hWindowNat :
      OW_globalWindow n C_rank PEM_trank1_timer K_reset T_rank T_rerank ≤
        c * n * n := by
    simpa [c] using
      (OW_globalWindow_trank1_quadratic
        (n := n) (K_reset := K_reset) (C_reset := C_reset)
        (T_rank := T_rank) (C_T_rank := C_T_rank)
        (T_rerank := T_rerank) (C_T_rerank := C_T_rerank)
        (C_rank := C_rank)
        h12resetCompletion.resetWindow_quadratic hRankWindow hRerankWindow)
  have hWindowENN :
      ((OW_globalWindow n C_rank PEM_trank1_timer K_reset T_rank T_rerank : ℕ) :
          ENNReal) ≤ ((c * n * n : ℕ) : ENNReal) := by
    exact_mod_cast hWindowNat
  have hpInv :
      ((((2 : ENNReal)⁻¹) * ((128 : ENNReal)⁻¹))⁻¹) = (256 : ENNReal) := by
    have hmul :
        ((2 : ENNReal)⁻¹) * ((128 : ENNReal)⁻¹) = ((256 : ENNReal)⁻¹) := by
      rw [← ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num))]
      norm_num
    rw [hmul]
    norm_num
  have hMono :
      (((OW_globalWindow n C_rank PEM_trank1_timer K_reset T_rank T_rerank : ℕ) :
          ENNReal) *
          ((((2 : ENNReal)⁻¹) * ((128 : ENNReal)⁻¹))⁻¹) / n) ≤
        (((c * n * n : ℕ) : ENNReal) * (256 : ENNReal) / n) := by
    rw [hpInv]
    exact ENNReal.div_le_div
      (mul_le_mul' hWindowENN le_rfl) le_rfl
  calc
    Probability.expectedParallelTimeToConsensus
        (PEMProtocol n 1 Rmax Emax Dmax (by omega : 0 < n))
        (by omega : 2 ≤ n) C₀
        ≤ (((OW_globalWindow n C_rank PEM_trank1_timer K_reset T_rank T_rerank : ℕ) :
            ENNReal) *
          (((2 : ENNReal)⁻¹) * ((128 : ENNReal)⁻¹))⁻¹ / n) := hBase
    _ ≤ (((c * n * n : ℕ) : ENNReal) * (256 : ENNReal) / n) := hMono
    _ = ((256 * c * n : ℕ) : ENNReal) :=
        ennreal_quadratic_nat_mul_div_cancel (c := c) (q := 256) hn0
    _ = ((PEM_On_explicit_linearConstant
          C_rank C_reset C_T_rank C_T_rerank * n : ℕ) : ENNReal) := by
        simp [PEM_On_explicit_linearConstant, c, Nat.mul_assoc]

end

end SSEM
