import Ripple.PopulationProtocol.Majority.SSEM.UpperBound.Time.OptimalWindows
import Ripple.PopulationProtocol.Majority.SSEM.UpperBound.Time.AnswerEpidemicBridge
import Ripple.PopulationProtocol.Majority.SSEM.UpperBound.Time.GenericKeystone

namespace SSEM

open scoped BigOperators ENNReal

/-- Reachable reset-seed target delivered by the faithful reset-completion
citation: the answer epidemic has a valid seed, all agents are still resetting,
and every dormant agent has remaining wake budget at least `d`.

This replaces the too-strong simultaneous `delaytimer = Dmax` target.  It is the
faithful [12] fresh-seed condition for the implementation: positive-resetcount
agents do not spend delay budget, and whenever an agent becomes dormant through
reset propagation or recruitment, `processAgent`/`propagateReset` refreshes its
delaytimer to `Dmax`, so any budget `d ≤ Dmax` is available to dormant agents. -/
def ResetSeedWithWakeBudget {n : ℕ} (d : ℕ) (m : Answer)
    (C : Config (AgentState n) Opinion n) : Prop :=
  EpidemicRegion m C ∧
    AllAgentsResetting C ∧
      ∀ a : Fin n, (C a).1.resetcount = 0 → d ≤ (C a).1.delaytimer

/-- Faithful [12]-cited reset-completion contract.

The cited reset window delivers a reachable epidemic-region reset seed. It does
not cite the PEM-specific answer-epidemic completion; that completion is
proved separately by `answer_epidemic_bridge_from_fresh_resetting`.

The target is intentionally a wake-budget seed, not simultaneous
`delaytimer = Dmax`: dormant resetting agents are exactly the agents whose
delaytimer can be decremented, while positive-resetcount resetting agents do not
spend delay budget before becoming dormant. -/
structure CRSReset12Faithful {n Rmax Emax Dmax : ℕ} (hn : 0 < n)
    (d : ℕ) (p_reset : ENNReal) (C_reset K_reset : ℕ) : Prop where
  wakeBudget_le_Dmax : d ≤ Dmax
  resetProb_pos : 0 < p_reset
  resetProb_le_one : p_reset ≤ 1
  resetConstant_pos : 0 < C_reset
  resetWindow_quadratic : K_reset ≤ C_reset * n * n
  freshSeedReach :
    ∀ (hn2 : 2 ≤ n) (C : Config (AgentState n) Opinion n),
      WellFormed 1 Rmax Emax Dmax C →
      CorrectResetSeed C →
        p_reset ≤
          Probability.ProbHitWithin
            (PEMProtocol n 1 Rmax Emax Dmax hn) hn2 C
            (ResetSeedWithWakeBudget d (majorityAnswer C)) K_reset

/-- Compose the faithful [12] fresh-reset seed reachability with the proven
answer-epidemic bridge at `trank = 1`. -/
theorem faithful_reset_to_phiGoal
    {n Rmax Emax Dmax K_reset K_bridge C_reset d : ℕ}
    (hn : 0 < n) (hn2 : 2 ≤ n) (hd_pos : 0 < d)
    {p_reset pE : ENNReal}
    (h12reset :
      CRSReset12Faithful (n := n) (Rmax := Rmax) (Emax := Emax)
        (Dmax := Dmax) hn d p_reset C_reset K_reset)
    (epidemicFast :
      StandardEpidemicFastHypothesisPEM
        n Rmax Emax Dmax K_bridge hn hn2 pE)
    (hTail : drainNoWakeTail n K_bridge d ≤ pE / 2) :
    ∀ C : Config (AgentState n) Opinion n,
      WellFormed 1 Rmax Emax Dmax C →
      CorrectResetSeed C →
        p_reset * (pE / 2) ≤
          Probability.ProbHitWithin
            (PEMProtocol n 1 Rmax Emax Dmax hn) hn2 C
            (fun D => EpidemicPhiGoal (majorityAnswer C) D ∧
              AllAgentsResetting D)
            (K_reset + K_bridge) := by
  classical
  intro C hWF hSeed
  let P : Protocol (AgentState n) Opinion Output :=
    PEMProtocol n 1 Rmax Emax Dmax hn
  let Mid : Config (AgentState n) Opinion n → Prop :=
    ResetSeedWithWakeBudget d (majorityAnswer C)
  let Goal : Config (AgentState n) Opinion n → Prop :=
    fun D => EpidemicPhiGoal (majorityAnswer C) D ∧ AllAgentsResetting D
  have hFreshSeed :
      p_reset ≤ Probability.ProbHitWithin P hn2 C Mid K_reset := by
    simpa [P, Mid] using h12reset.freshSeedReach hn2 C hWF hSeed
  have hBridge :
      ∀ D : Config (AgentState n) Opinion n, Mid D →
        pE / 2 ≤ Probability.ProbHitWithin P hn2 D Goal K_bridge := by
    intro D hD
    exact
      answer_epidemic_bridge_from_fresh_resetting
        (n := n) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        (K := K_bridge) (d := d) (C₀ := D) (m := majorityAnswer C)
        (pE := pE) hn hn2 hd_pos h12reset.wakeBudget_le_Dmax
        hD.2.1 hD.2.2 hD.1 hTail epidemicFast
  exact
    Probability.ProbHitWithin_add_ge_mul P hn2 C Mid Goal
      K_reset K_bridge p_reset (pE / 2) hFreshSeed hBridge

/-- Turn the faithful fresh-reset citation plus the proven answer-epidemic
bridge into the generic reset-completion contract expected by the existing
renewal keystone. -/
theorem crsReset12Faithful_to_generic
    {n Rmax Emax Dmax K_reset K_bridge C_reset C_bridge d : ℕ}
    (hn : 0 < n) (hn2 : 2 ≤ n) (hd_pos : 0 < d)
    {p_reset pE : ENNReal}
    (h12reset :
      CRSReset12Faithful (n := n) (Rmax := Rmax) (Emax := Emax)
        (Dmax := Dmax) hn d p_reset C_reset K_reset)
    (epidemicFast :
      StandardEpidemicFastHypothesisPEM
        n Rmax Emax Dmax K_bridge hn hn2 pE)
    (hTail : drainNoWakeTail n K_bridge d ≤ pE / 2)
    (hpE_pos : 0 < pE) (hpE_le_one : pE ≤ 1)
    (hBridgeWindow : K_bridge ≤ C_bridge * n * n) :
    CRSResetCompletion12Generic (n := n) (trank := 1) (Rmax := Rmax)
      (Emax := Emax) (Dmax := Dmax) hn
      (p_reset * (pE / 2)) (C_reset + C_bridge)
      (K_reset + K_bridge) where
  resetProb_pos := by
    have hhalf_pos : 0 < pE / 2 :=
      ENNReal.half_pos (ne_of_gt hpE_pos)
    exact ENNReal.mul_pos (ne_of_gt h12reset.resetProb_pos)
      (ne_of_gt hhalf_pos)
  resetProb_le_one := by
    have hsplit : pE / 2 + pE / 2 = pE := by
      simp
    have hhalf_le_pE : pE / 2 ≤ pE := by
      calc
        pE / 2 ≤ pE / 2 + pE / 2 :=
          (le_self_add : pE / 2 ≤ pE / 2 + pE / 2)
        _ = pE := hsplit
    have hhalf_le_one : pE / 2 ≤ 1 := hhalf_le_pE.trans hpE_le_one
    have hmul :
        p_reset * (pE / 2) ≤ (1 : ENNReal) * 1 :=
      mul_le_mul' h12reset.resetProb_le_one hhalf_le_one
    simpa using hmul
  resetConstant_pos := by
    exact Nat.add_pos_left h12reset.resetConstant_pos C_bridge
  resetWindow_quadratic := by
    calc
      K_reset + K_bridge ≤
          C_reset * n * n + C_bridge * n * n :=
        Nat.add_le_add h12reset.resetWindow_quadratic hBridgeWindow
      _ = (C_reset + C_bridge) * n * n := by
        ring
  resetReach := by
    intro hn2' C hWF hSeed
    have epidemicFast' :
        StandardEpidemicFastHypothesisPEM
          n Rmax Emax Dmax K_bridge hn hn2' pE := by
      have hhn2 : hn2 = hn2' := Subsingleton.elim hn2 hn2'
      cases hhn2
      exact fun {m} {D} hRegion => epidemicFast hRegion
    have hFaithful :
        p_reset * (pE / 2) ≤
          Probability.ProbHitWithin
            (PEMProtocol n 1 Rmax Emax Dmax hn) hn2' C
            (fun D => EpidemicPhiGoal (majorityAnswer C) D ∧
              AllAgentsResetting D)
            (K_reset + K_bridge) :=
      faithful_reset_to_phiGoal
        (n := n) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        (K_reset := K_reset) (K_bridge := K_bridge)
        (C_reset := C_reset) (d := d) hn hn2' hd_pos
        h12reset epidemicFast'
        hTail C hWF hSeed
    exact hFaithful.trans
      (Probability.ProbHitWithin_mono_goal
        (PEMProtocol n 1 Rmax Emax Dmax hn) hn2' C
        (fun D => EpidemicPhiGoal (majorityAnswer C) D ∧
          AllAgentsResetting D)
        (EpidemicPhiGoal (majorityAnswer C))
        (fun D hD => hD.1) (K_reset + K_bridge))

/-- Faithful `trank = 1` O(n) keystone: the reset citation targets only a
fresh reset seed, and the PEM answer-epidemic bridge supplies the formerly
over-cited `EpidemicPhiGoal` reset completion. -/
theorem PEM_expectedParallelTime_On_faithful
    {n Rmax Emax Dmax K_reset K_bridge C_reset C_bridge d : ℕ}
    [Inhabited (Fin n × Fin n)]
    (hn4 : 4 ≤ n) (hRmax : n ≤ Rmax) (hEmax : n ≤ Emax)
    (hDmax : n ≤ Dmax) (hd_pos : 0 < d)
    (C_rank T_rank T_rerank : ℕ)
    {p_reset pE : ENNReal}
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
    (h12reset :
      CRSReset12Faithful (n := n) (Rmax := Rmax) (Emax := Emax)
        (Dmax := Dmax) (by omega : 0 < n) d p_reset C_reset K_reset)
    (epidemicFast :
      StandardEpidemicFastHypothesisPEM
        n Rmax Emax Dmax K_bridge (by omega : 0 < n)
        (by omega : 2 ≤ n) pE)
    (hTail : drainNoWakeTail n K_bridge d ≤ pE / 2)
    (hpE_pos : 0 < pE) (hpE_le_one : pE ≤ 1)
    (hBridgeWindow : K_bridge ≤ C_bridge * n * n)
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
          (((OW_globalWindow n C_rank PEM_trank1_timer
              (K_reset + K_bridge) T_rank T_rerank : ℕ) : ENNReal) *
            ((p_reset * (pE / 2)) * ((128 : ENNReal)⁻¹))⁻¹ / n) := by
  intro C₀ hWF₀
  have hGeneric :=
    crsReset12Faithful_to_generic
      (n := n) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      (K_reset := K_reset) (K_bridge := K_bridge)
      (C_reset := C_reset) (C_bridge := C_bridge)
      (d := d) (by omega : 0 < n) (by omega : 2 ≤ n)
      hd_pos h12reset
      epidemicFast hTail hpE_pos hpE_le_one hBridgeWindow
  exact
    PEM_expectedParallelTime_On
      (n := n) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      hn4 hRmax hEmax hDmax C_rank (K_reset + K_bridge)
      T_rank T_rerank (p_reset * (pE / 2)) (C_reset + C_bridge)
      h12ranking hGeneric h12rank h12reRank C₀ hWF₀

end SSEM
