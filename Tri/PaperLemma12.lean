/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.MultiProductiveAmplificationLift
import Tri.MultiProductiveLinear

/-!
# Paper Lemma 12: proper multi-species stage completion

This file exposes the already proved `288n` productive-slot hitting estimate
in the notation of paper Lemma 12.  It also closes the capped branch: a
pairwise gap of `n` is consensus, and consensus is absorbing for the
productive-event chain.
-/

namespace Tri.Multi

open scoped ENNReal

variable {m n : ℕ}

/-- A population-sized pairwise gap is exactly consensus. -/
theorem pairwiseGap_population_consensus
    {c : Config m n} {X : Species m}
    (hgap : HasPairwiseGap c X n) :
    ConsensusOn c X := by
  unfold ConsensusOn
  apply Nat.le_antisymm
  · exact Nat.le_of_lt_succ (c.1 X).isLt
  · exact pairwiseGap_le_count_of_le_population le_rfl hgap

/-- Consensus supplies every feasible pairwise-gap threshold. -/
theorem consensus_pairwiseGap
    {c : Config m n} {X : Species m} {d : ℕ}
    (hc : ConsensusOn c X) (hdn : d ≤ n) :
    HasPairwiseGap c X d := by
  intro Y hYX
  have hzero := (consensusOn_iff_other_zero c X).1 hc Y hYX
  unfold ConsensusOn at hc
  omega

/-- Consensus has zero productive mass. -/
theorem productiveMass_eq_zero_of_consensus
    (c : Config m n) (X : Species m) (hc : ConsensusOn c X)
    (h3 : 3 ≤ n) :
    productiveMass c h3 = 0 := by
  unfold productiveMass
  apply ENNReal.tsum_eq_zero.mpr
  intro t
  have hnone := classify_eq_none_of_consensus c X hc t
  simp [IsProductiveSample, hnone]

/-- Consensus is absorbing for the total productive-event kernel. -/
theorem productiveStep_consensus
    (h3 : 3 ≤ n) (c : Config m n) (X : Species m)
    (hc : ConsensusOn c X) :
    productiveStep h3 c = PMF.pure c := by
  classical
  unfold productiveStep
  simp [productiveMass_eq_zero_of_consensus c X hc h3]

/-- Consensus is absorbing at every productive-event horizon. -/
theorem iter_productiveStep_consensus
    (h3 : 3 ≤ n) (c : Config m n) (X : Species m)
    (hc : ConsensusOn c X) :
    ∀ T, iter (productiveStep h3) T c = PMF.pure c := by
  intro T
  induction T with
  | zero => rfl
  | succ T ih =>
      rw [iter_succ, productiveStep_consensus h3 c X hc,
        PMF.pure_bind, ih]

/-- Consensus is also absorbing for every stopped no-backsliding kernel. -/
theorem iter_productivePairGapStop_consensus
    (h3 : 3 ≤ n) (c : Config m n) (X : Species m)
    (hc : ConsensusOn c X) (d : ℕ) (hdn : d ≤ n) :
    ∀ T, iter (productivePairGapStop h3 X d) T c = PMF.pure c := by
  have hgap : HasPairwiseGap c X d := consensus_pairwiseGap hc hdn
  intro T
  induction T with
  | zero => rfl
  | succ T ih =>
      have hstep :
          productivePairGapStop h3 X d c = PMF.pure c := by
        unfold productivePairGapStop
        rw [if_pos hgap, productiveStep_consensus h3 c X hc]
      rw [iter_succ, hstep, PMF.pure_bind, ih]

/-- In the capped amplification branch, the hit state is consensus. -/
theorem lemma12_cappedTarget_consensus
    {c : Config m n} {X : Species m} {Δ : ℕ}
    (hcap : n ≤ 4 * Δ)
    (hgap : HasPairwiseGap c X (min (4 * Δ) n)) :
    ConsensusOn c X := by
  rw [min_eq_right hcap] at hgap
  exact pairwiseGap_population_consensus hgap

/-- Paper Lemma 12's exact `288n` hitting component. -/
theorem lemma12_properStage_hitting
    (h3 : 3 ≤ n) (X : Species m) (Δ : ℕ)
    (hΔ4 : 4 ≤ Δ) (hΔn : Δ ≤ n)
    (c0 : Config m n) (hinit : HasPairwiseGap c0 X Δ) :
    let A : Config m n → Prop :=
      fun c => HasPairwiseGap c X (min (4 * Δ) n)
    terminalFailureMass
        (iter (freeze A (productiveStep h3)) (288 * n) c0) A ≤
      (144 : ℝ≥0∞) * productiveAmplificationError m n Δ := by
  simpa using
    productiveStep_properAmplification_hitting
      h3 X Δ hΔ4 hΔn c0 hinit

/-- The exact retained-gap predicate of paper Lemma 12. -/
def Lemma12RetainedGap
    (X : Species m) (Δ : ℕ) (c : Config m n) : Prop :=
  HasPairwiseGap c X (min (2 * Δ) n)

/-- The stronger checkpoint used internally by the proof of paper Lemma 12. -/
def Lemma12HitGap
    (X : Species m) (Δ : ℕ) (c : Config m n) : Prop :=
  HasPairwiseGap c X (min (4 * Δ) n)

noncomputable instance lemma12RetainedGapDecidablePred
    (X : Species m) (Δ : ℕ) :
    DecidablePred (Lemma12RetainedGap (n := n) X Δ) :=
  Classical.decPred _

noncomputable instance lemma12HitGapDecidablePred
    (X : Species m) (Δ : ℕ) :
    DecidablePred (Lemma12HitGap (n := n) X Δ) :=
  Classical.decPred _

/-- Paper Lemma 12's stated hitting conclusion.

The internal proof reaches the stronger checkpoint `min (4Δ) n`.  Freezing on
that checkpoint is a lazy version of the physical productive chain, and the
stronger checkpoint implies the paper target `min (2Δ) n`. -/
theorem lemma12_properStageCompletion_hitting
    (h3 : 3 ≤ n) (X : Species m) (Δ : ℕ)
    (hΔ4 : 4 ≤ Δ) (hΔn : Δ ≤ n)
    (c0 : Config m n) (hinit : HasPairwiseGap c0 X Δ) :
    terminalFailureMass
        (iter
          (freeze (Lemma12RetainedGap X Δ) (productiveStep h3))
          (288 * n) c0)
        (Lemma12RetainedGap X Δ) ≤
      ((288 * m + 144 : ℕ) : ℝ≥0∞) *
        ENNReal.ofReal
          (Real.exp (-((Δ : ℝ) ^ 2 / (82944 * (n : ℝ))))) := by
  classical
  let A : Config m n → Prop := Lemma12RetainedGap X Δ
  let B : Config m n → Prop := Lemma12HitGap X Δ
  let K : Config m n → PMF (Config m n) := productiveStep h3
  have hBA : ∀ c, B c → A c := by
    intro c hc
    exact hasPairwiseGap_of_le (by omega) hc
  have hlazy : IsLazyProjection K (freeze B K) id := by
    intro c
    by_cases hc : B c
    · right
      rw [freeze_of_mem c hc]
      simpa using PMF.map_id (PMF.pure c)
    · left
      rw [freeze_of_not_mem c hc]
      simpa using PMF.map_id (K c)
  have hprojection :=
    targetFreeze_failure_le_lazy_projection
      A K (freeze B K) id hlazy (288 * n) c0
  have hmono :
      terminalFailureMass
          (iter (freeze B K) (288 * n) c0) A ≤
        terminalFailureMass
          (iter (freeze B K) (288 * n) c0) B :=
    terminalFailureMass_mono _ A B hBA
  calc
    terminalFailureMass
        (iter
          (freeze (Lemma12RetainedGap X Δ) (productiveStep h3))
          (288 * n) c0)
        (Lemma12RetainedGap X Δ) ≤
      terminalFailureMass
        (iter (freeze B K) (288 * n) c0) A := by
          simpa [A, K] using hprojection
    _ ≤ terminalFailureMass
        (iter (freeze B K) (288 * n) c0) B := hmono
    _ ≤ (144 : ℝ≥0∞) * productiveAmplificationError m n Δ := by
      simpa [B, K, Lemma12HitGap] using
        lemma12_properStage_hitting
          h3 X Δ hΔ4 hΔn c0 hinit
    _ = ((288 * m + 144 : ℕ) : ℝ≥0∞) *
        ENNReal.ofReal
          (Real.exp (-((Δ : ℝ) ^ 2 / (82944 * (n : ℝ))))) :=
      productiveAmplificationError_144 m n Δ

/-- The no-backsliding error after the internal quadrupled-gap checkpoint. -/
noncomputable def lemma12RetentionError
    (m n Δ : ℕ) : ℝ≥0∞ :=
  (m : ℝ≥0∞) *
    ENNReal.ofReal
      (Real.exp (-(((4 * Δ : ℕ) : ℝ) ^ 2 / (18 * (n : ℝ)))))

/-- Failure mass for paper Lemma 12.

The first kernel is the target-frozen physical productive chain, so its
terminal state is the first `min (4Δ) n` checkpoint whenever that checkpoint
is hit within `288n` slots.  From there the second, failure-frozen kernel
records whether `min (2Δ) n` is ever lost.  The supremum over all finite
future horizons is therefore the paper's "from that point onward" event. -/
noncomputable def lemma12ProperStageFailure
    (h3 : 3 ≤ n) (X : Species m) (Δ : ℕ)
    (c0 : Config m n) : ℝ≥0∞ :=
  ⨆ T : ℕ,
    terminalFailureMass
      ((iter
          (freeze (Lemma12HitGap X Δ) (productiveStep h3))
          (288 * n) c0).bind
        (iter
          (productivePairGapStop h3 X (min (2 * Δ) n))
          T))
      (Lemma12RetainedGap X Δ)

/-- `terminalFailureMass` agrees with the multi-species failure-mass notation. -/
theorem terminalFailureMass_pairwiseGap
    (p : PMF (Config m n)) (X : Species m) (d : ℕ) :
    terminalFailureMass p (fun c => HasPairwiseGap c X d) =
      globalPairGapFailureMass p X d := by
  classical
  unfold terminalFailureMass globalPairGapFailureMass
  apply tsum_congr
  intro c
  by_cases hc : HasPairwiseGap c X d <;> simp [hc]

/-- Finite-future form of the complete paper Lemma 12 estimate. -/
theorem lemma12_properStage_finite
    (h3 : 3 ≤ n) (X : Species m) (Δ : ℕ)
    (hΔ4 : 4 ≤ Δ) (hΔn : Δ ≤ n)
    (c0 : Config m n) (hinit : HasPairwiseGap c0 X Δ)
    (T : ℕ) :
    terminalFailureMass
        ((iter
            (freeze (Lemma12HitGap X Δ) (productiveStep h3))
            (288 * n) c0).bind
          (iter
            (productivePairGapStop h3 X (min (2 * Δ) n))
            T))
        (Lemma12RetainedGap X Δ) ≤
      (144 : ℝ≥0∞) * productiveAmplificationError m n Δ +
        lemma12RetentionError m n Δ := by
  classical
  let p :=
    iter
      (freeze (Lemma12HitGap X Δ) (productiveStep h3))
      (288 * n) c0
  let e := lemma12RetentionError m n Δ
  have hpoint :
      ∀ c : Config m n,
        terminalFailureMass
            (iter
              (productivePairGapStop h3 X (min (2 * Δ) n))
              T c)
            (Lemma12RetainedGap X Δ) ≤
          if Lemma12HitGap X Δ c then e else 1 := by
    intro c
    by_cases hhit : Lemma12HitGap X Δ c
    · rw [if_pos hhit]
      by_cases hcap : n ≤ 4 * Δ
      · have hcons : ConsensusOn c X :=
          lemma12_cappedTarget_consensus hcap hhit
        rw [iter_productivePairGapStop_consensus
          h3 c X hcons (min (2 * Δ) n) (min_le_right _ _) T]
        rw [terminalFailureMass_eq_expect, expect_pure]
        have hsafe :
            Lemma12RetainedGap X Δ c :=
          consensus_pairwiseGap hcons (min_le_right _ _)
        simp [hsafe]
      · have h4Δn : 4 * Δ ≤ n := by omega
        have h2Δn : 2 * Δ ≤ n := by omega
        have hhalf : (4 * Δ) / 2 = 2 * Δ := by omega
        have hret :=
          productivePairGapStop_half_failure_exp
            h3 X (4 * Δ) (by omega) h4Δn T c
            (by
              simpa [Lemma12HitGap, min_eq_left h4Δn] using hhit)
        rw [hhalf] at hret
        unfold Lemma12RetainedGap
        simp only [min_eq_left h2Δn]
        rw [terminalFailureMass_pairwiseGap]
        simpa [e, lemma12RetentionError] using hret
    · rw [if_neg hhit]
      exact terminalFailureMass_le_one _ _
  rw [terminalFailureMass_bind]
  calc
    expect p
        (fun c =>
          terminalFailureMass
            (iter
              (productivePairGapStop h3 X (min (2 * Δ) n))
              T c)
            (Lemma12RetainedGap X Δ)) ≤
        expect p
          (fun c => if Lemma12HitGap X Δ c then e else 1) := by
      unfold expect
      exact ENNReal.tsum_le_tsum fun c =>
        by
          simpa [mul_comm] using
            mul_le_mul_right (hpoint c) (p c)
    _ ≤ terminalFailureMass p (Lemma12HitGap X Δ) + e := by
      unfold expect terminalFailureMass
      calc
        (∑' c, p c *
            (if Lemma12HitGap X Δ c then e else 1)) ≤
            ∑' c,
              ((if Lemma12HitGap X Δ c then 0 else p c) +
                p c * e) := by
              apply ENNReal.tsum_le_tsum
              intro c
              by_cases hc : Lemma12HitGap X Δ c <;> simp [hc]
        _ = (∑' c,
              if Lemma12HitGap X Δ c then 0 else p c) +
              ∑' c, p c * e := ENNReal.tsum_add
        _ = (∑' c,
              if Lemma12HitGap X Δ c then 0 else p c) +
              (∑' c, p c) * e := by rw [ENNReal.tsum_mul_right]
        _ = (∑' c,
              if Lemma12HitGap X Δ c then 0 else p c) + e := by
              rw [PMF.tsum_coe, one_mul]
    _ ≤ (144 : ℝ≥0∞) * productiveAmplificationError m n Δ + e := by
      exact add_le_add
        (by
          simpa [p, Lemma12HitGap] using
            lemma12_properStage_hitting
              h3 X Δ hΔ4 hΔn c0 hinit)
        le_rfl

/-- **Paper Lemma 12 (proper stage completion).**

Within `288n` productive-reaction slots the plurality gap reaches the internal
checkpoint `min (4Δ) n`; from that first hit onward it retains the paper target
`min (2Δ) n` at every future time.  The displayed explicit error is uniform
over the future horizon. -/
theorem lemma12_properStage
    (h3 : 3 ≤ n) (X : Species m) (Δ : ℕ)
    (hΔ4 : 4 ≤ Δ) (hΔn : Δ ≤ n)
    (c0 : Config m n) (hinit : HasPairwiseGap c0 X Δ) :
    lemma12ProperStageFailure h3 X Δ c0 ≤
      (144 : ℝ≥0∞) * productiveAmplificationError m n Δ +
        lemma12RetentionError m n Δ := by
  unfold lemma12ProperStageFailure
  exact iSup_le fun T =>
    lemma12_properStage_finite
      h3 X Δ hΔ4 hΔn c0 hinit T

/-- Paper Lemma 12, with the exact growth condition needed to absorb its
species union-bound prefactor into the printed exponential error. -/
theorem lemma12
    (h3 : 3 ≤ n) (X : Species m) (Δ γ : ℕ)
    (hΔ4 : 4 ≤ Δ) (hΔn : Δ ≤ n)
    (hstage : γ * n * Nat.log 2 n ≤ Δ ^ 2)
    (hm : (((288 * m + 144 : ℕ) : ℝ)) ≤
        Real.exp ((((γ * Nat.log 2 n : ℕ) : ℝ) / 165888)))
    (c0 : Config m n) (hinit : HasPairwiseGap c0 X Δ) :
    terminalFailureMass
        (iter (freeze (Lemma12RetainedGap X Δ) (productiveStep h3))
          (288 * n) c0)
        (Lemma12RetainedGap X Δ) ≤
      ENNReal.ofReal
        (Real.exp (-(((γ * Nat.log 2 n : ℕ) : ℝ) / 165888))) := by
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hstageN : (γ * Nat.log 2 n) * n ≤ Δ ^ 2 := by
    calc (γ * Nat.log 2 n) * n = γ * n * Nat.log 2 n := by ring
      _ ≤ Δ ^ 2 := hstage
  have hstageR :
      (((γ * Nat.log 2 n : ℕ) : ℝ) * (n : ℝ)) ≤ (Δ : ℝ) ^ 2 := by
    exact_mod_cast hstageN
  have hrate :
      (((γ * Nat.log 2 n : ℕ) : ℝ) / 82944) ≤
        (Δ : ℝ) ^ 2 / (82944 * (n : ℝ)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hexp :
      Real.exp (-((Δ : ℝ) ^ 2 / (82944 * (n : ℝ)))) ≤
        Real.exp (-(((γ * Nat.log 2 n : ℕ) : ℝ) / 82944)) :=
    Real.exp_le_exp.mpr (neg_le_neg hrate)
  have habsorb :
      (((288 * m + 144 : ℕ) : ℝ)) *
          Real.exp (-(((γ * Nat.log 2 n : ℕ) : ℝ) / 82944)) ≤
        Real.exp (-(((γ * Nat.log 2 n : ℕ) : ℝ) / 165888)) := by
    calc
      _ ≤ Real.exp ((((γ * Nat.log 2 n : ℕ) : ℝ) / 165888)) *
            Real.exp (-(((γ * Nat.log 2 n : ℕ) : ℝ) / 82944)) :=
        mul_le_mul_of_nonneg_right hm (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hreal :
      (((288 * m + 144 : ℕ) : ℝ)) *
          Real.exp (-((Δ : ℝ) ^ 2 / (82944 * (n : ℝ)))) ≤
        Real.exp (-(((γ * Nat.log 2 n : ℕ) : ℝ) / 165888)) :=
    (mul_le_mul_of_nonneg_left hexp (by positivity)).trans habsorb
  refine (lemma12_properStageCompletion_hitting
    h3 X Δ hΔ4 hΔn c0 hinit).trans ?_
  rw [show ((288 * m + 144 : ℕ) : ℝ≥0∞)
        = ENNReal.ofReal ((288 * m + 144 : ℕ) : ℝ) from
      (ENNReal.ofReal_natCast _).symm,
    ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal hreal

end Tri.Multi

#print axioms Tri.Multi.pairwiseGap_population_consensus
#print axioms Tri.Multi.consensus_pairwiseGap
#print axioms Tri.Multi.productiveMass_eq_zero_of_consensus
#print axioms Tri.Multi.productiveStep_consensus
#print axioms Tri.Multi.iter_productiveStep_consensus
#print axioms Tri.Multi.iter_productivePairGapStop_consensus
#print axioms Tri.Multi.lemma12_cappedTarget_consensus
#print axioms Tri.Multi.lemma12_properStage_hitting
#print axioms Tri.Multi.lemma12_properStageCompletion_hitting
#print axioms Tri.Multi.terminalFailureMass_pairwiseGap
#print axioms Tri.Multi.lemma12_properStage_finite
#print axioms Tri.Multi.lemma12_properStage
#print axioms Tri.Multi.lemma12
