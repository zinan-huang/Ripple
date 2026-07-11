import Ripple.PopulationProtocol.Majority.SSEM.UpperBound.Time

/-!
# Decision timing isolation

This file isolates the productive decision event from the live-region exit
event already used in the Phase-3 timing layer.
-/

namespace SSEM

open scoped ENNReal

attribute [local instance] Classical.propDecidable

section

variable {n Rmax Emax Dmax : ℕ}
  [DecidableEq (Config (AgentState n) Opinion n)]

/-- The Markov decision window used by the expectation-to-window argument. -/
def decisionWindow (n : ℕ) : ℕ :=
  2 * n * (n - 1)

/-- The longer geometric decision window used in the paper-style Phase-3
subtraction argument. -/
def kanayaDecisionWindow (n : ℕ) : ℕ :=
  4 * n * n

/-- Productive decision endpoint: the median decision is complete while the
timer is still live, or the run has already reached consensus / a correct reset
seed. -/
def DecisionProductiveTarget
    (C : Config (AgentState n) Opinion n) : Prop :=
  (InSswap C ∧ MedianAnswerCorrect C ∧ MedianTimerAtLeast 1 C) ∨
    IsConsensusConfig C ∨ CorrectResetSeed C

omit [DecidableEq (Config (AgentState n) Opinion n)] in
private theorem step_InSswap_of_InSswap_of_post_InSrank
    (hn0 : 0 < n)
    {D : Config (AgentState n) Opinion n}
    (hS : InSswap D) {i j : Fin n}
    (hRank' :
      InSrank
        (D.step (PEMProtocolCoupled n Rmax Emax Dmax hn0) i j)) :
    InSswap
      (D.step (PEMProtocolCoupled n Rmax Emax Dmax hn0) i j) := by
  classical
  let P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  have hInput :
      ∀ w : Fin n, (D.step P i j w).2 = (D w).2 := by
    intro w
    exact step_input_preserved P D i j w
  have hRank :
      ∀ w : Fin n, (D.step P i j w).1.rank = (D w).1.rank := by
    intro w
    simpa [P] using
      step_rank_preserved_of_InSswap
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) hn0 hS w
  have hnA : nAOf (D.step P i j) = nAOf D := by
    simpa [P, PEMProtocolCoupled, PEMProtocol] using
      (nAOf_step_eq (trank := Rmax) (Rmax := Rmax)
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

private theorem toOuterMeasure_le_of_support_imp
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

omit [DecidableEq (Config (AgentState n) Opinion n)] in
private theorem hitTwoFlagDist_live_exit_bad_stopped
    (hn0 : 0 < n) (hn2 : 2 ≤ n)
    (C₀ : Config (AgentState n) Opinion n)
    (hLive₀ : InSswap C₀ ∧ MedianTimerAtLeast 1 C₀) :
    let P := PEMProtocolCoupled n Rmax Emax Dmax hn0
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
          (step_InSswap_of_InSswap_of_post_InSrank
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
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

omit [DecidableEq (Config (AgentState n) Opinion n)] in
private theorem live_exit_ProbHitWithin_le_bad
    (hn0 : 0 < n) (hn2 : 2 ≤ n)
    (C₀ : Config (AgentState n) Opinion n)
    (hLive₀ : InSswap C₀ ∧ MedianTimerAtLeast 1 C₀) (t : ℕ) :
    let P := PEMProtocolCoupled n Rmax Emax Dmax hn0
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
  apply toOuterMeasure_le_of_support_imp
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
      hitTwoFlagDist_live_exit_bad_stopped
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        hn0 hn2 C₀ hLive₀ t S hSupp hBadFalse
    have hExitTrue : S.2.1 = true := hExitHit
    rw [hStopped.2] at hExitTrue
    cases hExitTrue

/-- Decision-before-timeout isolation in the short decision window.

The only extra assumption is exactly the missing separation fact: live-region
exit before the decision window has probability at most `1/4`.  Under that
assumption, the existing Phase-3 `decision ∨ exit` bound and the finite-prefix
union subtraction leave a `1/4` productive decision probability. -/
theorem decision_before_timer_zero_of_exit_le_quarter
    (hn4 : 4 ≤ n) (hn0 : 0 < n)
    (C : Config (AgentState n) Opinion n)
    (hS : InSswap C) (hT : MedianTimerAtLeast 1 C)
    (hExit :
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0)
        (by omega : 2 ≤ n) C
        (fun D => ¬ (InSswap D ∧ MedianTimerAtLeast 1 D))
        (decisionWindow n) ≤ (4 : ENNReal)⁻¹) :
    (4 : ENNReal)⁻¹ ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0)
        (by omega : 2 ≤ n) C
        (DecisionProductiveTarget : Config (AgentState n) Opinion n → Prop)
        (decisionWindow n) := by
  classical
  let P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  let LiveDecision : Config (AgentState n) Opinion n → Prop :=
    fun D => InSswap D ∧ MedianAnswerCorrect D ∧ MedianTimerAtLeast 1 D
  have hDecision :
      (4 : ENNReal)⁻¹ ≤
        Probability.ProbHitWithin P (by omega : 2 ≤ n) C LiveDecision
          (decisionWindow n) := by
    simpa [P, LiveDecision, decisionWindow] using
      (PEM_phase3_live_decision_hit_lower_bound_of_exit_le_quarter_from_expected
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        (by omega : 2 ≤ n) hn0 hn4 hS hT
        (by simpa [P, decisionWindow] using hExit))
  exact hDecision.trans
    (Probability.ProbHitWithin_mono_goal P (by omega : 2 ≤ n) C
      LiveDecision
      (DecisionProductiveTarget : Config (AgentState n) Opinion n → Prop)
      (fun D hD => Or.inl hD) (decisionWindow n))

/-- Decision before the median timer can drain in the short decision window.

This is the Kanaya-style closed form currently supported by the time layer:
starting in `Sswap` with median timer at least `35`, the productive endpoint
has probability at least `1/4` within `2*n*(n-1)` interactions.  The timer
tail bound controls `¬InSrank ∨ ¬timer`; a stopped-invariant argument converts
the local `¬(InSswap ∧ timer)` exit used by the decision-window lemma into
that bad event. -/
theorem decision_before_timer_zero
    [Inhabited (Fin n × Fin n)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n)
    (hRmax : n ≤ Rmax) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (C : Config (AgentState n) Opinion n)
    (hS : InSswap C) (hT : MedianTimerAtLeast 35 C) :
    (4 : ENNReal)⁻¹ ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0)
        (by omega : 2 ≤ n) C
        (DecisionProductiveTarget : Config (AgentState n) Opinion n → Prop)
        (decisionWindow n) := by
  classical
  let P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  let Bad : Config (AgentState n) Opinion n → Prop :=
    fun D => ¬ InSrank D ∨ ¬ MedianTimerAtLeast 1 D
  have hT1 : MedianTimerAtLeast 1 C :=
    MedianTimerAtLeast.mono (n := n) (a := 1) (b := 35) (by norm_num) hT
  have hBadBig :
      Probability.ProbHitWithin P (by omega : 2 ≤ n) C Bad
          (4 * n * (n - 1)) ≤ (4 : ENNReal)⁻¹ := by
    simpa [P, Bad] using
      (PEM_srank_or_timer_failure_prob_le_quarter_short35
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        hn4 hn0 hRmax hEmax hDmax C hS.toInSrank hT)
  have hBadSmall :
      Probability.ProbHitWithin P (by omega : 2 ≤ n) C Bad
          (decisionWindow n) ≤ (4 : ENNReal)⁻¹ := by
    exact
      (Probability.ProbHitWithin_mono_time P (by omega : 2 ≤ n) C Bad
        (by
          dsimp [decisionWindow]
          nlinarith [Nat.zero_le (n * (n - 1))])).trans hBadBig
  have hExitSmall :
      Probability.ProbHitWithin P (by omega : 2 ≤ n) C
          (fun D => ¬ (InSswap D ∧ MedianTimerAtLeast 1 D))
          (decisionWindow n) ≤ (4 : ENNReal)⁻¹ := by
    exact
      (live_exit_ProbHitWithin_le_bad
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        hn0 (by omega : 2 ≤ n) C ⟨hS, hT1⟩ (decisionWindow n)).trans
        (by simpa [P, Bad] using hBadSmall)
  exact
    decision_before_timer_zero_of_exit_le_quarter
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      hn4 hn0 C hS hT1 hExitSmall

/-- Paper-style Phase-3 isolation with the `MedianTimerAtLeast 28` entry
condition and the current library's explicit `exit ≤ 1/2` hypothesis.  If the
median answer is already correct, the target is hit at time `0`; otherwise this
is exactly the existing geometric live-or-exit subtraction wrapper, enlarged by
`cons ∨ CRS`. -/
theorem decision_before_timer_zero_kanaya28
    (hn4 : 4 ≤ n) (hn0 : 0 < n)
    (C : Config (AgentState n) Opinion n)
    (hS : InSswap C) (hT : MedianTimerAtLeast 28 C)
    (hExit :
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0)
        (by omega : 2 ≤ n) C
        (fun D => ¬ (InSswap D ∧ MedianTimerAtLeast 1 D))
        (kanayaDecisionWindow n) ≤ (2 : ENNReal)⁻¹) :
    (8 : ENNReal)⁻¹ ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0)
        (by omega : 2 ≤ n) C
        (DecisionProductiveTarget : Config (AgentState n) Opinion n → Prop)
        (kanayaDecisionWindow n) := by
  classical
  let P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  by_cases hMAC : MedianAnswerCorrect C
  · have hT1 : MedianTimerAtLeast 1 C :=
      MedianTimerAtLeast.mono (n := n) (a := 1) (b := 28) (by norm_num) hT
    have hGoal : DecisionProductiveTarget C := Or.inl ⟨hS, hMAC, hT1⟩
    have hOne :
        (1 : ENNReal) ≤
          Probability.ProbHitWithin P (by omega : 2 ≤ n) C
            (DecisionProductiveTarget : Config (AgentState n) Opinion n → Prop)
            (kanayaDecisionWindow n) := by
      calc
        (1 : ENNReal) =
            Probability.probReached P (by omega : 2 ≤ n) C
              (DecisionProductiveTarget : Config (AgentState n) Opinion n → Prop) 0 := by
              exact (Probability.probReached_zero_of_goal P (by omega : 2 ≤ n) C
                (DecisionProductiveTarget : Config (AgentState n) Opinion n → Prop)
                hGoal).symm
        _ ≤ Probability.ProbHitWithin P (by omega : 2 ≤ n) C
              (DecisionProductiveTarget : Config (AgentState n) Opinion n → Prop) 0 :=
              Probability.probReached_le_ProbHitWithin P (by omega : 2 ≤ n) C
                (DecisionProductiveTarget : Config (AgentState n) Opinion n → Prop) 0
        _ ≤ Probability.ProbHitWithin P (by omega : 2 ≤ n) C
              (DecisionProductiveTarget : Config (AgentState n) Opinion n → Prop)
              (kanayaDecisionWindow n) :=
              Probability.ProbHitWithin_mono_time P (by omega : 2 ≤ n) C
                (DecisionProductiveTarget : Config (AgentState n) Opinion n → Prop)
                (Nat.zero_le _)
    exact le_trans (by norm_num : (8 : ENNReal)⁻¹ ≤ 1) hOne
  · exact
      PEM_phase3_live_decision_hit_lower_bound_of_exit_le_half_mono
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        (by omega : 2 ≤ n) hn0 hn4
        (DecisionProductiveTarget : Config (AgentState n) Opinion n → Prop)
        (fun D hD => Or.inl hD)
        hS hT hMAC
        (by simpa [P, kanayaDecisionWindow] using hExit)

end

end SSEM
