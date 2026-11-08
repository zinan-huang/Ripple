/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Outcome-aware Phase-2 work adapter

The Phase-2 dispatcher has four branches.  The three consensus branches run
the existing carrier-and-output-cleanup work and finish in `StableDone`; the
mixed-sign branch runs the existing real-kernel advance work and finishes in
`AdvancedPast2`.

The four works have different horizons.  Their targets are absorbing, so this
file pads each branch to one common maximum horizon and packages the result as
one `PhaseConvergenceW`, the type consumed by
`OutcomeFastAssembly.Assembly.work`.

This adapter does not strengthen `AdvancedPast2` to the exact
`Phase23FirstEntry` shell.  That fixed-time producer/refinement is precisely
the named `PastPhase2EntryFirstOrStable` left by `Phase2EntryDispatcher`.
-/

import Ripple.PopulationProtocol.ExactMajority.Probability.Phase2EntryDispatcher
import Ripple.PopulationProtocol.ExactMajority.Probability.OutcomeFastAssembly

namespace Ripple.PopulationProtocol.ExactMajority
namespace Phase2OutcomeWork

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

noncomputable section

variable {L K : ℕ}

/-- The honest common endpoint of the four Phase-2 branches. -/
def Target (init : Config (AgentState L K)) (n : ℕ)
    (c : Config (AgentState L K)) : Prop :=
  c ∈ StableDone L K init ∨
    Phase2AdvanceEpidemic.AdvancedPast2 (L := L) (K := K) n c

/-- The common Phase-2 target is one-step absorbing under the real protocol. -/
theorem target_kernel_absorbing
    (init : Config (AgentState L K)) (n : ℕ)
    (c : Config (AgentState L K))
    (h : Target (L := L) (K := K) init n c) :
    (NonuniformMajority L K).transitionKernel c
        {c' | ¬ Target (L := L) (K := K) init n c'} = 0 := by
  rcases h with hdone | hadv
  · apply measure_mono_null ?_
      (StableDone_kernel_absorbing L K init c hdone)
    intro c' hbad
    change c' ∉ StableDone L K init
    intro hdone'
    exact hbad (Or.inl hdone')
  · apply measure_mono_null ?_
      (Phase2AdvanceEpidemic.real_not_advanced_eq_zero_of_advanced
        (L := L) (K := K) n c hadv)
    intro c' hbad
    change ¬ Phase2AdvanceEpidemic.AdvancedPast2
      (L := L) (K := K) n c'
    intro hadv'
    exact hbad (Or.inr hadv')

/-- The fixed-verdict work, with its stronger outcome-aware precondition. -/
noncomputable def consensusWork
    (init : Config (AgentState L K)) (out : Output)
    (n : ℕ) (hn : 2 ≤ n) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel where
  Pre := Phase2EntryDispatcher.ConsensusEntry
    (L := L) (K := K) init out n
  Post := fun c => c ∈ StableDone L K init
  t := (Phase2ConsensusBranch.convergence
    (L := L) (K := K) out n hn).t
  ε := (Phase2ConsensusBranch.convergence
    (L := L) (K := K) out n hn).ε
  convergence := by
    intro c hpre
    let w := Phase2ConsensusBranch.convergence
      (L := L) (K := K) out n hn
    have hsub :
        {c' : Config (AgentState L K) | c' ∉ StableDone L K init} ⊆
          {c' | ¬ w.Post c'} := by
      intro c' hnot hpost
      exact hnot (hpre.post_mem_stableDone hpost)
    exact le_trans (measure_mono hsub) (w.convergence c hpre.pre)

/-- The mixed-sign real-kernel work, restricted to the concrete dispatcher
precondition. -/
noncomputable def continueWork
    (n : ℕ) (hn : 2 ≤ n) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel where
  Pre := Phase2AdvanceEpidemic.Active2Concrete
    (L := L) (K := K) n
  Post := Phase2AdvanceEpidemic.AdvancedPast2
    (L := L) (K := K) n
  t := (Phase2AdvanceEpidemic.phase2AdvanceConvergence
    (L := L) (K := K) n hn).t
  ε := (Phase2AdvanceEpidemic.phase2AdvanceConvergence
    (L := L) (K := K) n hn).ε
  convergence := by
    intro c hpre
    exact (Phase2AdvanceEpidemic.phase2AdvanceConvergence
      (L := L) (K := K) n hn).convergence c hpre.1

/-- All three consensus instances have definitionally the same horizon. -/
@[simp] theorem consensusWork_t_eq_A
    (init : Config (AgentState L K)) (out : Output)
    (n : ℕ) (hn : 2 ≤ n) :
    (consensusWork (L := L) (K := K) init out n hn).t =
      (consensusWork (L := L) (K := K) init .A n hn).t := by
  rfl

/-- All three consensus instances have definitionally the same budget. -/
@[simp] theorem consensusWork_epsilon_eq_A
    (init : Config (AgentState L K)) (out : Output)
    (n : ℕ) (hn : 2 ≤ n) :
    (consensusWork (L := L) (K := K) init out n hn).ε =
      (consensusWork (L := L) (K := K) init .A n hn).ε := by
  rfl

/-- Common maximum horizon used by the runtime branch merge. -/
def commonHorizon
    (init : Config (AgentState L K)) (n : ℕ) (hn : 2 ≤ n) : ℕ :=
  max (consensusWork (L := L) (K := K) init .A n hn).t
    (continueWork (L := L) (K := K) n hn).t

/-- Common maximum error budget used by the runtime branch merge. -/
def commonBudget
    (init : Config (AgentState L K)) (n : ℕ) (hn : 2 ≤ n) : ℝ≥0 :=
  max (consensusWork (L := L) (K := K) init .A n hn).ε
    (continueWork (L := L) (K := K) n hn).ε

/-- The merged work keeps the larger branch budget; it does not union-bound
the mutually exclusive dispatcher branches. -/
theorem commonBudget_le_inv_sq_nnreal
    (init : Config (AgentState L K)) (n : ℕ) (hn : 2 ≤ n) :
    commonBudget (L := L) (K := K) init n hn ≤
      Real.toNNReal (1 / (n : ℝ) ^ 2) := by
  unfold commonBudget
  apply max_le
  · apply le_of_eq
    apply ENNReal.coe_injective
    have hcons := Phase2ConsensusBranch.convergence_epsilon_eq_inv_sq
      (L := L) (K := K) .A n hn
    calc
      (((consensusWork (L := L) (K := K) init .A n hn).ε : ℝ≥0) :
          ℝ≥0∞) = ENNReal.ofReal (1 / (n : ℝ) ^ 2) := by
            simpa [consensusWork] using hcons
      _ = ((Real.toNNReal (1 / (n : ℝ) ^ 2) : ℝ≥0) : ℝ≥0∞) := by
        rw [ENNReal.coe_nnreal_eq, Real.coe_toNNReal]
        positivity
  · exact Phase2AdvanceEpidemic.advanceTailBudget_le_inv_sq n hn

/-- ENNReal form of the inverse-square budget expected by
`OutcomeFastAssembly.done_tail`. -/
theorem commonBudget_coe_le_inv_sq
    (init : Config (AgentState L K)) (n : ℕ) (hn : 2 ≤ n) :
    ((commonBudget (L := L) (K := K) init n hn : ℝ≥0) : ℝ≥0∞) ≤
      1 / (n : ℝ≥0∞) ^ 2 := by
  have hnn := commonBudget_le_inv_sq_nnreal
    (L := L) (K := K) init n hn
  have hcast :
      ((commonBudget (L := L) (K := K) init n hn : ℝ≥0) : ℝ≥0∞) ≤
        ENNReal.ofReal (1 / (n : ℝ) ^ 2) := by
    have hcast' :
        ((commonBudget (L := L) (K := K) init n hn : ℝ≥0) : ℝ≥0∞) ≤
          ((Real.toNNReal (1 / (n : ℝ) ^ 2) : ℝ≥0) : ℝ≥0∞) := by
      exact_mod_cast hnn
    have hto :
        ((Real.toNNReal (1 / (n : ℝ) ^ 2) : ℝ≥0) : ℝ≥0∞) =
          ENNReal.ofReal (1 / (n : ℝ) ^ 2) := by
      rw [ENNReal.coe_nnreal_eq, Real.coe_toNNReal]
      positivity
    rwa [hto] at hcast'
  have hnR : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast (by omega : 0 < n)
  have hrhs : ENNReal.ofReal (1 / (n : ℝ) ^ 2) =
      1 / (n : ℝ≥0∞) ^ 2 := by
    rw [div_eq_mul_inv, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1)]
    rw [ENNReal.ofReal_inv_of_pos]
    · rw [ENNReal.ofReal_pow (by positivity : 0 ≤ (n : ℝ))]
      norm_num
    · positivity
  rwa [← hrhs]

/-- The common maximum horizon fits the larger, nineteen-unit consensus
constant. -/
theorem commonHorizon_le_nineteen
    (init : Config (AgentState L K)) (n L' : ℕ) (hn : 2 ≤ n)
    (hlogp1 : Real.log (n : ℝ) + 1 ≤ (L' + 1 : ℝ))
    (hnL : n ≤ 2 ^ L') :
    commonHorizon (L := L) (K := K) init n hn ≤
      19 * n * (L' + 1) := by
  unfold commonHorizon
  apply max_le
  · exact Phase2ConsensusBranch.convergence_t_le_nineteen
      (L := L) (K := K) .A n L' hn hlogp1 hnL
  · have h17 := TightEpidemicWork.epiHorizonTight_le_ht_of_logp1
      n L' hn hlogp1
    change TightEpidemicWork.epiHorizonTight n hn ≤ _
    exact h17.trans (by gcongr; norm_num)

private theorem consensus_tail_at_common
    (init : Config (AgentState L K)) (out : Output)
    (n : ℕ) (hn : 2 ≤ n) (c : Config (AgentState L K))
    (hpre : Phase2EntryDispatcher.ConsensusEntry
      (L := L) (K := K) init out n c) :
    ((NonuniformMajority L K).transitionKernel ^
        commonHorizon (L := L) (K := K) init n hn) c
        {c' | ¬ Target (L := L) (K := K) init n c'} ≤
      ((commonBudget (L := L) (K := K) init n hn : ℝ≥0) : ℝ≥0∞) := by
  let w := consensusWork (L := L) (K := K) init out n hn
  have ht : w.t ≤ commonHorizon (L := L) (K := K) init n hn := by
    rw [show w.t =
      (consensusWork (L := L) (K := K) init .A n hn).t by rfl]
    exact Nat.le_max_left _ _
  have hmono := bad_antitone_le
    (NonuniformMajority L K).transitionKernel
    (DiscreteMeasurableSpace.forall_measurableSet
      {c' : Config (AgentState L K) |
        Target (L := L) (K := K) init n c'})
    (fun x hx => target_kernel_absorbing
      (L := L) (K := K) init n x hx)
    c ht
  change
    ((NonuniformMajority L K).transitionKernel ^
        commonHorizon (L := L) (K := K) init n hn) c
        {c' | ¬ Target (L := L) (K := K) init n c'} ≤
      ((NonuniformMajority L K).transitionKernel ^ w.t) c
        {c' | ¬ Target (L := L) (K := K) init n c'} at hmono
  have hsub :
      {c' : Config (AgentState L K) |
        ¬ Target (L := L) (K := K) init n c'} ⊆
        {c' | ¬ w.Post c'} := by
    intro c' hbad hpost
    exact hbad (Or.inl hpost)
  have htail :
      ((NonuniformMajority L K).transitionKernel ^ w.t) c
          {c' | ¬ Target (L := L) (K := K) init n c'} ≤
        ((w.ε : ℝ≥0) : ℝ≥0∞) :=
    le_trans (measure_mono hsub) (w.convergence c hpre)
  have hbudget : w.ε ≤ commonBudget (L := L) (K := K) init n hn := by
    rw [show w.ε =
      (consensusWork (L := L) (K := K) init .A n hn).ε by rfl]
    exact le_max_left _ _
  exact le_trans hmono (le_trans htail (by exact_mod_cast hbudget))

private theorem continue_tail_at_common
    (init : Config (AgentState L K))
    (n : ℕ) (hn : 2 ≤ n) (c : Config (AgentState L K))
    (hpre : Phase2AdvanceEpidemic.Active2Concrete
      (L := L) (K := K) n c) :
    ((NonuniformMajority L K).transitionKernel ^
        commonHorizon (L := L) (K := K) init n hn) c
        {c' | ¬ Target (L := L) (K := K) init n c'} ≤
      ((commonBudget (L := L) (K := K) init n hn : ℝ≥0) : ℝ≥0∞) := by
  let w := continueWork (L := L) (K := K) n hn
  have ht : w.t ≤ commonHorizon (L := L) (K := K) init n hn :=
    Nat.le_max_right _ _
  have hmono := bad_antitone_le
    (NonuniformMajority L K).transitionKernel
    (DiscreteMeasurableSpace.forall_measurableSet
      {c' : Config (AgentState L K) |
        Target (L := L) (K := K) init n c'})
    (fun x hx => target_kernel_absorbing
      (L := L) (K := K) init n x hx)
    c ht
  change
    ((NonuniformMajority L K).transitionKernel ^
        commonHorizon (L := L) (K := K) init n hn) c
        {c' | ¬ Target (L := L) (K := K) init n c'} ≤
      ((NonuniformMajority L K).transitionKernel ^ w.t) c
        {c' | ¬ Target (L := L) (K := K) init n c'} at hmono
  have hsub :
      {c' : Config (AgentState L K) |
        ¬ Target (L := L) (K := K) init n c'} ⊆
        {c' | ¬ w.Post c'} := by
    intro c' hbad hpost
    exact hbad (Or.inr hpost)
  have htail :
      ((NonuniformMajority L K).transitionKernel ^ w.t) c
          {c' | ¬ Target (L := L) (K := K) init n c'} ≤
        ((w.ε : ℝ≥0) : ℝ≥0∞) :=
    le_trans (measure_mono hsub) (w.convergence c hpre)
  have hbudget : w.ε ≤ commonBudget (L := L) (K := K) init n hn :=
    le_max_right _ _
  exact le_trans hmono (le_trans htail (by exact_mod_cast hbudget))

/-- One real-kernel work instance for all four dispatcher outcomes. -/
noncomputable def outcomeWork
    (init : Config (AgentState L K)) (n : ℕ) (hn : 2 ≤ n) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel where
  Pre := Phase2EntryDispatcher.OutcomeDispatch
    (L := L) (K := K) init n
  Post := Target (L := L) (K := K) init n
  t := commonHorizon (L := L) (K := K) init n hn
  ε := commonBudget (L := L) (K := K) init n hn
  convergence := by
    intro c hpre
    cases hpre with
    | doneA h => exact consensus_tail_at_common init .A n hn c h
    | doneB h => exact consensus_tail_at_common init .B n hn c h
    | doneT h => exact consensus_tail_at_common init .T n hn c h
    | continue3 h => exact continue_tail_at_common init n hn c h

/-- The assembled outcome work spends at most one inverse-square budget. -/
theorem outcomeWork_epsilon_le_inv_sq
    (init : Config (AgentState L K)) (n : ℕ) (hn : 2 ≤ n) :
    ((outcomeWork (L := L) (K := K) init n hn).ε : ℝ≥0∞) ≤
      1 / (n : ℝ≥0∞) ^ 2 := by
  simpa [outcomeWork] using
    commonBudget_coe_le_inv_sq (L := L) (K := K) init n hn

/-- The assembled outcome work fits the common nineteen-unit horizon. -/
theorem outcomeWork_t_le_nineteen
    (init : Config (AgentState L K)) (n L' : ℕ) (hn : 2 ≤ n)
    (hlogp1 : Real.log (n : ℝ) + 1 ≤ (L' + 1 : ℝ))
    (hnL : n ≤ 2 ^ L') :
    (outcomeWork (L := L) (K := K) init n hn).t ≤
      19 * n * (L' + 1) := by
  simpa [outcomeWork] using
    commonHorizon_le_nineteen (L := L) (K := K)
      init n L' hn hlogp1 hnL

@[simp] theorem outcomeWork_Pre
    (init : Config (AgentState L K)) (n : ℕ) (hn : 2 ≤ n) :
    (outcomeWork (L := L) (K := K) init n hn).Pre =
      Phase2EntryDispatcher.OutcomeDispatch
        (L := L) (K := K) init n := rfl

@[simp] theorem outcomeWork_Post
    (init : Config (AgentState L K)) (n : ℕ) (hn : 2 ≤ n) :
    (outcomeWork (L := L) (K := K) init n hn).Post =
      Target (L := L) (K := K) init n := rfl

/-- A not-yet-done output of the adapter is exactly the existing real-kernel
Continue3 target.  No exact first-entry conclusion is hidden here. -/
theorem outcomeWork_activePost
    (init : Config (AgentState L K)) (n : ℕ) (hn : 2 ≤ n)
    (c : Config (AgentState L K))
    (hpost : (outcomeWork (L := L) (K := K) init n hn).Post c)
    (hnot : c ∉ StableDone L K init) :
    Phase2AdvanceEpidemic.AdvancedPast2 (L := L) (K := K) n c :=
  hpost.resolve_left hnot

/-- The canonical slot-2 index of the ten-work fast assembly. -/
def phase2Index : Fin 10 := ⟨2, by decide⟩

/-- Replace only work slot 2 by the outcome-aware adapter.  The returned family
has exactly the type of `OutcomeFastAssembly.Assembly.work`; reconstructing the
dependent payload/entry fields of a full assembly remains a separate producer
task. -/
def installPhase2Work
    (init : Config (AgentState L K)) (n : ℕ) (hn : 2 ≤ n)
    (work : Fin 10 →
      PhaseConvergenceW (NonuniformMajority L K).transitionKernel) :
    Fin 10 → PhaseConvergenceW
      (NonuniformMajority L K).transitionKernel :=
  fun k => if k = phase2Index then outcomeWork (L := L) (K := K) init n hn
    else work k

@[simp] theorem installPhase2Work_apply_phase2Index
    (init : Config (AgentState L K)) (n : ℕ) (hn : 2 ≤ n)
    (work : Fin 10 →
      PhaseConvergenceW (NonuniformMajority L K).transitionKernel) :
    installPhase2Work (L := L) (K := K) init n hn work phase2Index =
      outcomeWork (L := L) (K := K) init n hn := by
  simp [installPhase2Work]

@[simp] theorem installPhase2Work_apply_ne
    (init : Config (AgentState L K)) (n : ℕ) (hn : 2 ≤ n)
    (work : Fin 10 →
      PhaseConvergenceW (NonuniformMajority L K).transitionKernel)
    (k : Fin 10) (hk : k ≠ phase2Index) :
    installPhase2Work (L := L) (K := K) init n hn work k = work k := by
  simp [installPhase2Work, hk]

#print axioms target_kernel_absorbing
#print axioms consensusWork
#print axioms continueWork
#print axioms consensusWork_t_eq_A
#print axioms consensusWork_epsilon_eq_A
#print axioms commonBudget_le_inv_sq_nnreal
#print axioms commonBudget_coe_le_inv_sq
#print axioms commonHorizon_le_nineteen
#print axioms outcomeWork_epsilon_le_inv_sq
#print axioms outcomeWork_t_le_nineteen
#print axioms outcomeWork
#print axioms outcomeWork_Pre
#print axioms outcomeWork_Post
#print axioms outcomeWork_activePost
#print axioms installPhase2Work_apply_phase2Index
#print axioms installPhase2Work_apply_ne

end
end Phase2OutcomeWork
end Ripple.PopulationProtocol.ExactMajority
