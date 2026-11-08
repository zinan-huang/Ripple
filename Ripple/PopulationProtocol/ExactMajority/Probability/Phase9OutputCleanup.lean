/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Phase-9 output cleanup

Once Phase 9 has the verdict-compatible sign support, every scheduled
interaction writes the verdict to both selected agents.  This file turns that
deterministic pair fact into the exact scheduler identity

  weightedDropSum = 2 * wrongOutputCount / n

and packages the resulting multiplicative cleanup as a `PhaseConvergenceW`.
-/

import Ripple.PopulationProtocol.ExactMajority.Analysis.StableEndpoints
import Ripple.PopulationProtocol.ExactMajority.Probability.WeightedDriftDropSum
import Ripple.PopulationProtocol.ExactMajority.Probability.DriftHorizon

namespace Ripple.PopulationProtocol.ExactMajority
namespace Phase9OutputCleanup

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal Real

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

/-- The Phase-9 sign/opinion support associated with a fixed verdict.  The tie
branch is deliberately exact: absence of both signs would also admit the empty
opinion set, which does not force output `T`. -/
def Phase9SignState (out : Output) (a : AgentState L K) : Prop :=
  match out with
  | .A =>
      a.phase.val = 9 ∧ hasPlusOne a.opinions = true ∧
        hasMinusOne a.opinions = false
  | .B =>
      a.phase.val = 9 ∧ hasMinusOne a.opinions = true ∧
        hasPlusOne a.opinions = false
  | .T =>
      a.phase.val = 9 ∧ a.opinions = phase2OpinionT

/-- Phase 9 has the correct verdict support throughout a population of size
`n`.  Outputs need not yet agree. -/
def Phase9SignsDone (out : Output) (n : ℕ)
    (c : Config (AgentState L K)) : Prop :=
  c.card = n ∧ ∀ a ∈ c, Phase9SignState out a

/-- The number of agents whose output is not yet the fixed verdict. -/
noncomputable def wrongOutputCount9 (out : Output)
    (c : Config (AgentState L K)) : ℕ :=
  Multiset.countP (fun a => a.output ≠ out) c

/-- The terminal Phase-9 cleanup predicate. -/
def Phase9Post (out : Output) (n : ℕ)
    (c : Config (AgentState L K)) : Prop :=
  Phase9SignsDone out n c ∧ wrongOutputCount9 out c = 0

private theorem phaseEpidemicUpdate_eq_self_of_phase9
    (s t : AgentState L K)
    (hs : s.phase.val = 9) (ht : t.phase.val = 9) :
    phaseEpidemicUpdate L K s t = (s, t) := by
  have hs_eq : s.phase = ⟨9, by decide⟩ := Fin.ext hs
  have ht_eq : t.phase = ⟨9, by decide⟩ := Fin.ext ht
  unfold phaseEpidemicUpdate
  rw [hs_eq, ht_eq, max_self]
  simp only [runInitsBetween_self]
  cases s
  cases t
  simp_all

private theorem Transition_phase9_T_exact
    (s t : AgentState L K)
    (hs_phase : s.phase.val = 9) (ht_phase : t.phase.val = 9)
    (hs_op : s.opinions = phase2OpinionT)
    (ht_op : t.opinions = phase2OpinionT) :
    ((Transition L K s t).1.phase.val = 9 ∧
      (Transition L K s t).1.opinions = phase2OpinionT ∧
      (Transition L K s t).1.output = .T) ∧
    ((Transition L K s t).2.phase.val = 9 ∧
      (Transition L K s t).2.opinions = phase2OpinionT ∧
      (Transition L K s t).2.output = .T) := by
  have hs_phase_eq : s.phase = ⟨9, by decide⟩ := Fin.ext hs_phase
  have ht_phase_eq : t.phase = ⟨9, by decide⟩ := Fin.ext ht_phase
  have hepidemic := phaseEpidemicUpdate_eq_self_of_phase9
    (L := L) (K := K) s t hs_phase ht_phase
  simp [Transition, hepidemic, hs_phase_eq, ht_phase_eq, Phase9Transition,
    Phase2Transition, hs_op, ht_op, phase2OpinionT, opinionsUnion,
    hasMinusOne, hasPlusOne]

/-- On any verdict-compatible Phase-9 pair, both transition outputs preserve
the support invariant and carry the fixed verdict. -/
theorem Transition_phase9_sign_pair
    (out : Output) (s t : AgentState L K)
    (hs : Phase9SignState out s) (ht : Phase9SignState out t) :
    (Phase9SignState out (Transition L K s t).1 ∧
      (Transition L K s t).1.output = out) ∧
    (Phase9SignState out (Transition L K s t).2 ∧
      (Transition L K s t).2.output = out) := by
  cases out with
  | A =>
      rcases hs with ⟨hs_phase, hs_plus, hs_minus⟩
      rcases ht with ⟨ht_phase, _ht_plus, ht_minus⟩
      have h := Transition_phase9_A_from_plus (L := L) (K := K) s t
        hs_phase ht_phase hs_plus hs_minus ht_minus
      exact ⟨⟨⟨h.1.1, h.1.2.2.1, h.1.2.2.2⟩, h.1.2.1⟩,
        ⟨⟨h.2.1, h.2.2.2.1, h.2.2.2.2⟩, h.2.2.1⟩⟩
  | B =>
      rcases hs with ⟨hs_phase, hs_minus, hs_plus⟩
      rcases ht with ⟨ht_phase, _ht_minus, ht_plus⟩
      have h := Transition_phase9_B_from_minus (L := L) (K := K) s t
        hs_phase ht_phase hs_minus hs_plus ht_plus
      exact ⟨⟨⟨h.1.1, h.1.2.2.1, h.1.2.2.2⟩, h.1.2.1⟩,
        ⟨⟨h.2.1, h.2.2.2.1, h.2.2.2.2⟩, h.2.2.1⟩⟩
  | T =>
      rcases hs with ⟨hs_phase, hs_op⟩
      rcases ht with ⟨ht_phase, ht_op⟩
      have h := Transition_phase9_T_exact (L := L) (K := K) s t
        hs_phase ht_phase hs_op ht_op
      exact ⟨⟨⟨h.1.1, h.1.2.1⟩, h.1.2.2⟩,
        ⟨⟨h.2.1, h.2.2.1⟩, h.2.2.2⟩⟩

/-- The support invariant is closed under every chosen-pair update. -/
theorem Phase9SignsDone_stepOrSelf
    (out : Output) (n : ℕ) (c : Config (AgentState L K))
    (hInv : Phase9SignsDone out n c) (s t : AgentState L K) :
    Phase9SignsDone out n
      (Protocol.stepOrSelf (NonuniformMajority L K) c s t) := by
  classical
  by_cases happ : Protocol.Applicable c s t
  · have hs_mem : s ∈ c := Multiset.mem_of_le happ (by simp)
    have ht_mem : t ∈ c := Multiset.mem_of_le happ (by simp)
    have hs := hInv.2 s hs_mem
    have ht := hInv.2 t ht_mem
    have hpair := Transition_phase9_sign_pair (L := L) (K := K) out s t hs ht
    have hc' :
        Protocol.stepOrSelf (NonuniformMajority L K) c s t =
          c - {s, t} + {(Transition L K s t).1, (Transition L K s t).2} := by
      unfold Protocol.stepOrSelf
      rw [if_pos happ]
      rfl
    constructor
    · rw [Protocol.stepOrSelf_card_eq]
      exact hInv.1
    · rw [hc']
      intro a ha
      have ha' :
          a = (Transition L K s t).1 ∨
            a ∈ c - {s, t} ∨ a = (Transition L K s t).2 := by
        simpa using ha
      rcases ha' with hfirst | hold | hsecond
      · rw [hfirst]
        exact hpair.1.1
      · exact hInv.2 a (Multiset.mem_of_le (Multiset.sub_le_self c {s, t}) hold)
      · rw [hsecond]
        exact hpair.2.1
  · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]
    exact hInv

/-- ENNReal indicator for an agent whose output is still wrong. -/
def wrongOutputIndicator9 (out : Output) (a : AgentState L K) : ℝ≥0∞ :=
  if a.output = out then 0 else 1

/-- The multiset sum of wrong-output indicators is the cast of the natural
wrong-output count. -/
theorem sumOf_wrongOutputIndicator9 (out : Output)
    (c : Config (AgentState L K)) :
    Config.sumOf (wrongOutputIndicator9 (L := L) (K := K) out) c =
      (wrongOutputCount9 out c : ℝ≥0∞) := by
  classical
  induction c using Multiset.induction_on with
  | empty => simp [Config.sumOf, wrongOutputCount9]
  | @cons a c ih =>
      unfold Config.sumOf wrongOutputCount9 at ih ⊢
      rw [Multiset.map_cons, Multiset.sum_cons, Multiset.countP_cons, ih,
        Nat.cast_add]
      by_cases h : a.output = out <;> simp [wrongOutputIndicator9, h, add_comm]

/-- Exact occurrence ledger for an applicable selected pair.  Each selected
wrong output disappears, and both replacement agents have the fixed output. -/
theorem wrongOutputCount9_stepOrSelf_add_indicators
    (out : Output) (n : ℕ) (c : Config (AgentState L K))
    (hInv : Phase9SignsDone out n c) (s t : AgentState L K)
    (happ : Protocol.Applicable c s t) :
    wrongOutputCount9 out
          (Protocol.stepOrSelf (NonuniformMajority L K) c s t) +
        (if s.output = out then 0 else 1) +
        (if t.output = out then 0 else 1) =
      wrongOutputCount9 out c := by
  classical
  have hs_mem : s ∈ c := Multiset.mem_of_le happ (by simp)
  have ht_mem : t ∈ c := Multiset.mem_of_le happ (by simp)
  have hpair := Transition_phase9_sign_pair (L := L) (K := K) out s t
    (hInv.2 s hs_mem) (hInv.2 t ht_mem)
  have hc' :
      Protocol.stepOrSelf (NonuniformMajority L K) c s t =
        c - {s, t} + {(Transition L K s t).1, (Transition L K s t).2} := by
    unfold Protocol.stepOrSelf
    rw [if_pos happ]
    rfl
  have hremoved_le :
      Multiset.countP (fun a : AgentState L K => a.output ≠ out) {s, t} ≤
        Multiset.countP (fun a : AgentState L K => a.output ≠ out) c :=
    Multiset.countP_le_of_le _ happ
  have hnew_count :
      Multiset.countP (fun a : AgentState L K => a.output ≠ out)
          {(Transition L K s t).1, (Transition L K s t).2} = 0 := by
    rw [show ({(Transition L K s t).1, (Transition L K s t).2} :
      Multiset (AgentState L K)) =
        (Transition L K s t).1 ::ₘ (Transition L K s t).2 ::ₘ 0 from rfl]
    rw [Multiset.countP_cons, Multiset.countP_cons, Multiset.countP_zero]
    simp [hpair.1.2, hpair.2.2]
  have hold_count :
      Multiset.countP (fun a : AgentState L K => a.output ≠ out) {s, t} =
        (if s.output = out then 0 else 1) +
          (if t.output = out then 0 else 1) := by
    rw [show ({s, t} : Multiset (AgentState L K)) = s ::ₘ t ::ₘ 0 from rfl]
    rw [Multiset.countP_cons, Multiset.countP_cons, Multiset.countP_zero]
    by_cases hs : s.output = out <;> by_cases ht : t.output = out <;>
      simp [hs, ht]
  unfold wrongOutputCount9
  rw [hc', Multiset.countP_add, Multiset.countP_sub happ]
  rw [hnew_count, hold_count]
  omega

/-- The wrong-output count never increases under a chosen-pair update while
the Phase-9 sign support holds. -/
theorem wrongOutputCount9_stepOrSelf_le
    (out : Output) (n : ℕ) (c : Config (AgentState L K))
    (hInv : Phase9SignsDone out n c) (s t : AgentState L K) :
    wrongOutputCount9 out
        (Protocol.stepOrSelf (NonuniformMajority L K) c s t) ≤
      wrongOutputCount9 out c := by
  by_cases happ : Protocol.Applicable c s t
  · have h := wrongOutputCount9_stepOrSelf_add_indicators
      (L := L) (K := K) out n c hInv s t happ
    omega
  · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]

/-- At most the whole population can have a wrong output. -/
theorem wrongOutputCount9_le_card (out : Output)
    (c : Config (AgentState L K)) :
    wrongOutputCount9 out c ≤ c.card := by
  unfold wrongOutputCount9
  exact Multiset.countP_le_card _ _

private theorem natCast_wrongOutputIndicator9 (out : Output)
    (a : AgentState L K) :
    (((if a.output = out then 0 else 1) : ℕ) : ℝ≥0∞) =
      wrongOutputIndicator9 out a := by
  by_cases h : a.output = out <;> simp [wrongOutputIndicator9, h]

/-- Positive ordered-pair multiplicity implies that the selected occurrence
pair is present in the configuration. -/
private theorem applicable_of_pos_interactionCount
    (c : Config (AgentState L K)) (s t : AgentState L K)
    (h : 0 < c.interactionCount s t) :
    Protocol.Applicable c s t := by
  change {s, t} ≤ c
  rw [Multiset.le_iff_count]
  intro a
  simp only [Config.interactionCount, Config.count] at h
  simp only [Multiset.insert_eq_cons, Multiset.count_cons,
    Multiset.count_singleton]
  by_cases heq : s = t
  · subst heq
    simp only [ite_true] at h
    have htwo : 2 ≤ Multiset.count s c := by
      by_contra hlt
      have hle : Multiset.count s c ≤ 1 := by omega
      have hzero :
          Multiset.count s c * (Multiset.count s c - 1) = 0 := by
        rcases Nat.eq_zero_or_pos (Multiset.count s c) with h0 | hpos
        · simp [h0]
        · have hone : Multiset.count s c = 1 := by omega
          simp [hone]
      omega
    by_cases ha : a = s <;> simp_all
  · simp only [if_neg heq] at h
    have hspos : 0 < Multiset.count s c :=
      pos_of_mul_pos_left h (Nat.zero_le _)
    have htpos : 0 < Multiset.count t c :=
      pos_of_mul_pos_right h (Nat.zero_le _)
    by_cases has : a = s <;> by_cases hat : a = t <;> simp_all <;> omega

private theorem interactionProb_eq_zero_of_not_applicable
    (c : Config (AgentState L K)) (s t : AgentState L K)
    (happ : ¬Protocol.Applicable c s t) :
    c.interactionProb s t = 0 := by
  have hcount : c.interactionCount s t = 0 := by
    apply Nat.eq_zero_of_not_pos
    intro hpos
    exact happ (applicable_of_pos_interactionCount c s t hpos)
  simp [Config.interactionProb, hcount]

/-- Exact scheduler summand: on a positive-mass pair, the natural potential
drop is precisely the two selected wrong-output indicators. -/
private theorem wrongOutput_weighted_pair_eq
    (out : Output) (n : ℕ) (c : Config (AgentState L K))
    (hInv : Phase9SignsDone out n c) (s t : AgentState L K) :
    (((wrongOutputCount9 out c : ℝ≥0∞) -
          (wrongOutputCount9 out
            (Protocol.stepOrSelf (NonuniformMajority L K) c s t) : ℝ≥0∞)) *
        c.interactionProb s t) =
      (wrongOutputIndicator9 out s + wrongOutputIndicator9 out t) *
        c.interactionProb s t := by
  by_cases happ : Protocol.Applicable c s t
  · have hledger := wrongOutputCount9_stepOrSelf_add_indicators
      (L := L) (K := K) out n c hInv s t happ
    have hmono := wrongOutputCount9_stepOrSelf_le
      (L := L) (K := K) out n c hInv s t
    have hdropNat :
        wrongOutputCount9 out c -
            wrongOutputCount9 out
              (Protocol.stepOrSelf (NonuniformMajority L K) c s t) =
          (if s.output = out then 0 else 1) +
            (if t.output = out then 0 else 1) := by
      omega
    have hcast := congrArg (fun m : ℕ => (m : ℝ≥0∞)) hdropNat
    have hdrop :
        (wrongOutputCount9 out c : ℝ≥0∞) -
            (wrongOutputCount9 out
              (Protocol.stepOrSelf (NonuniformMajority L K) c s t) : ℝ≥0∞) =
          wrongOutputIndicator9 out s + wrongOutputIndicator9 out t := by
      simpa only [ENNReal.natCast_sub, Nat.cast_add,
        natCast_wrongOutputIndicator9] using hcast
    rw [hdrop]
  · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ,
      interactionProb_eq_zero_of_not_applicable c s t happ]
    simp

/-- The Phase-9 cleanup potential has the exact weighted scheduler drop
`2w/n`, with no residual escape or slack term. -/
theorem weightedDropSum_wrongOutputCount9_eq
    (out : Output) (n : ℕ) (hn : 2 ≤ n)
    (c : Config (AgentState L K)) (hInv : Phase9SignsDone out n c) :
    WeightedDriftDropSum.weightedDropSum (NonuniformMajority L K)
        (wrongOutputCount9 out) c =
      2 * (wrongOutputCount9 out c : ℝ≥0∞) / (n : ℝ≥0∞) := by
  classical
  have hc2 : 2 ≤ c.card := by rw [hInv.1]; exact hn
  unfold WeightedDriftDropSum.weightedDropSum
  calc
    (∑ pair : AgentState L K × AgentState L K,
        ((wrongOutputCount9 out c : ℝ≥0∞) -
            (wrongOutputCount9 out
              (Protocol.stepOrSelf (NonuniformMajority L K)
                c pair.1 pair.2) : ℝ≥0∞)) *
          c.interactionProb pair.1 pair.2) =
        ∑ pair : AgentState L K × AgentState L K,
          (wrongOutputIndicator9 out pair.1 +
              wrongOutputIndicator9 out pair.2) *
            c.interactionProb pair.1 pair.2 := by
      refine Finset.sum_congr rfl ?_
      intro pair _
      exact wrongOutput_weighted_pair_eq
        (L := L) (K := K) out n c hInv pair.1 pair.2
    _ = (∑ pair : AgentState L K × AgentState L K,
          wrongOutputIndicator9 out pair.1 *
            c.interactionProb pair.1 pair.2) +
        ∑ pair : AgentState L K × AgentState L K,
          wrongOutputIndicator9 out pair.2 *
            c.interactionProb pair.1 pair.2 := by
      simp_rw [add_mul]
      rw [Finset.sum_add_distrib]
    _ = Config.sumOf (wrongOutputIndicator9 out) c / (c.card : ℝ≥0∞) +
        Config.sumOf (wrongOutputIndicator9 out) c / (c.card : ℝ≥0∞) := by
      rw [Phase0Window.sum_fst_interactionProb c hc2,
        Phase0Window.sum_snd_interactionProb c hc2]
    _ = (wrongOutputCount9 out c : ℝ≥0∞) / (n : ℝ≥0∞) +
        (wrongOutputCount9 out c : ℝ≥0∞) / (n : ℝ≥0∞) := by
      rw [sumOf_wrongOutputIndicator9, hInv.1]
    _ = 2 * (wrongOutputCount9 out c : ℝ≥0∞) / (n : ℝ≥0∞) := by
      simp only [div_eq_mul_inv]
      ring

/-- Real numerator `B` for the exact cleanup fraction
`B/(n(n-1)) = 2/n`. -/
def phase9CleanupB (n : ℕ) : ℝ :=
  2 * ((n : ℝ) - 1)

/-- The one-step multiplicative contraction factor. -/
noncomputable def phase9CleanupRate (n : ℕ) : ℝ≥0∞ :=
  1 - ENNReal.ofReal
    (phase9CleanupB n / ((n : ℝ) * ((n : ℝ) - 1)))

/-- Exact identification of the real horizon fraction with the scheduler's
`2/n` marginal. -/
theorem ofReal_phase9Cleanup_fraction_eq (n : ℕ) (hn : 2 ≤ n) :
    ENNReal.ofReal
        (phase9CleanupB n / ((n : ℝ) * ((n : ℝ) - 1))) =
      2 / (n : ℝ≥0∞) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hnm1 : (0 : ℝ) < (n : ℝ) - 1 := by
    have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hreal :
      phase9CleanupB n / ((n : ℝ) * ((n : ℝ) - 1)) =
        2 / (n : ℝ) := by
    unfold phase9CleanupB
    field_simp
  rw [hreal, ENNReal.ofReal_div_of_pos hn0]
  norm_num

theorem phase9CleanupRate_le_one (n : ℕ) :
    phase9CleanupRate n ≤ 1 := by
  unfold phase9CleanupRate
  exact tsub_le_self

private theorem phase9CleanupB_pos (n : ℕ) (hn : 2 ≤ n) :
    0 < phase9CleanupB n := by
  unfold phase9CleanupB
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  exact mul_pos (by norm_num) (by linarith)

private theorem phase9CleanupB_le (n : ℕ) (hn : 2 ≤ n) :
    phase9CleanupB n ≤ (n : ℝ) * ((n : ℝ) - 1) := by
  unfold phase9CleanupB
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  exact mul_le_mul_of_nonneg_right hnR (by linarith)

/-- Multiplicative `1-2/n` drift of the wrong-output count on the Phase-9
support invariant. -/
theorem wrongOutputCount9_drift
    (out : Output) (n : ℕ) (hn : 2 ≤ n)
    (c : Config (AgentState L K)) (hInv : Phase9SignsDone out n c) :
    ∫⁻ c', (wrongOutputCount9 out c' : ℝ≥0∞)
        ∂((NonuniformMajority L K).transitionKernel c) ≤
      phase9CleanupRate n * (wrongOutputCount9 out c : ℝ≥0∞) := by
  have hc2 : 2 ≤ c.card := by rw [hInv.1]; exact hn
  unfold phase9CleanupRate
  apply WeightedDriftDropSum.weighted_dyadic_mass_drift_of_dropSum
    (NonuniformMajority L K) (wrongOutputCount9 out) c hc2
      (ENNReal.ofReal
        (phase9CleanupB n / ((n : ℝ) * ((n : ℝ) - 1))))
  · exact ENNReal.ofReal_ne_top
  · intro pair
    exact wrongOutputCount9_stepOrSelf_le
      (L := L) (K := K) out n c hInv pair.1 pair.2
  · rw [weightedDropSum_wrongOutputCount9_eq out n hn c hInv,
      ofReal_phase9Cleanup_fraction_eq n hn]
    apply le_of_eq
    simp only [div_eq_mul_inv]
    ac_rfl

/-- The Phase-9 sign support is closed on the one-step scheduler support. -/
theorem Phase9SignsDone_of_stepDistOrSelf_support
    (out : Output) (n : ℕ) (hn : 2 ≤ n)
    (c c' : Config (AgentState L K))
    (hInv : Phase9SignsDone out n c)
    (hsupp : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    Phase9SignsDone out n c' := by
  have hc2 : 2 ≤ c.card := by rw [hInv.1]; exact hn
  rw [show (NonuniformMajority L K).stepDistOrSelf c =
      (NonuniformMajority L K).stepDist c hc2 by
        unfold Protocol.stepDistOrSelf
        rw [dif_pos hc2]] at hsupp
  obtain ⟨⟨s, t⟩, hr⟩ :=
    Protocol.stepDist_support (NonuniformMajority L K) c hc2 c' hsupp
  rw [← hr]
  exact Phase9SignsDone_stepOrSelf out n c hInv s t

/-- The real kernel has zero one-step mass outside the cleanup invariant. -/
theorem Phase9SignsDone_kernel_escape_zero
    (out : Output) (n : ℕ) (hn : 2 ≤ n)
    (c : Config (AgentState L K)) (hInv : Phase9SignsDone out n c) :
    (NonuniformMajority L K).transitionKernel c
        {c' | ¬Phase9SignsDone out n c'} = 0 := by
  change ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
    {c' | ¬Phase9SignsDone out n c'} = 0
  rw [PMF.toMeasure_apply_eq_zero_iff _
    (DiscreteMeasurableSpace.forall_measurableSet _)]
  rw [Set.disjoint_left]
  intro c' hsupp hbad
  exact hbad (Phase9SignsDone_of_stepDistOrSelf_support
    (L := L) (K := K) out n hn c c' hInv hsupp)

/-- Calibrated cleanup horizon. -/
noncomputable def phase9OutputCleanupHorizon (n : ℕ) : ℕ :=
  DriftSurvival.driftHorizon (phase9CleanupB n) n n 2

/-- Raw multiplicative-drift package.  Its precondition is the support
invariant together with the automatic potential ceiling `w ≤ n`. -/
noncomputable def phase9OutputCleanupRaw
    (out : Output) (n : ℕ) (hn : 2 ≤ n) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  DriftSurvival.driftSurvivalPhase
    (NonuniformMajority L K).transitionKernel
    (Phase9SignsDone (L := L) (K := K) out n)
    (wrongOutputCount9 (L := L) (K := K) out)
    (phase9CleanupRate n) (phase9CleanupRate_le_one n)
    (fun c hc => wrongOutputCount9_drift out n hn c hc)
    0 (fun c hc => by
      rw [Phase9SignsDone_kernel_escape_zero out n hn c hc])
    (phase9OutputCleanupHorizon n) n
    (DriftSurvival.driftBudgetNN 2 n) 0
    (by
      exact DriftSurvival.drift_pow_le_budget_sub hn (by omega) (by omega)
        (phase9CleanupB_pos n hn) (phase9CleanupB_le n hn))
    (by simp)

/-- Phase-9 output cleanup with the exact public entry and terminal predicates.
The potential ceiling required by the generic engine is discharged internally
from `wrongOutputCount9 ≤ card = n`. -/
noncomputable def phase9OutputCleanup
    (out : Output) (n : ℕ) (hn : 2 ≤ n) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel where
  Pre := Phase9SignsDone out n
  Post := Phase9Post out n
  t := phase9OutputCleanupHorizon n
  ε := DriftSurvival.driftBudgetNN 2 n
  convergence := by
    intro c hc
    have hpre :
        (phase9OutputCleanupRaw (L := L) (K := K) out n hn).Pre c := by
      change Phase9SignsDone out n c ∧ wrongOutputCount9 out c ≤ n
      refine ⟨hc, ?_⟩
      calc
        wrongOutputCount9 out c ≤ c.card := wrongOutputCount9_le_card out c
        _ = n := hc.1
    have h :=
      (phase9OutputCleanupRaw (L := L) (K := K) out n hn).convergence c hpre
    simpa [phase9OutputCleanupRaw, DriftSurvival.driftSurvivalPhase,
      Phase9Post] using h

/-- The calibrated cleanup horizon fits in `2 n (L+1)` interactions under the
standard power-of-two population ceiling. -/
theorem phase9OutputCleanupHorizon_le_two
    {n L' : ℕ} (hn : 2 ≤ n) (hnL : n ≤ 2 ^ L') :
    phase9OutputCleanupHorizon n ≤ 2 * n * (L' + 1) := by
  rw [phase9OutputCleanupHorizon, DriftSurvival.driftHorizon, Nat.ceil_le]
  have hnpos : 0 < n := by omega
  have hnR0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
  have hnm1 : (0 : ℝ) < (n : ℝ) - 1 := by
    have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hlogN :
      Real.log (n : ℝ) ≤ (L' : ℕ) * Real.log 2 := by
    calc
      Real.log (n : ℝ) ≤ Real.log ((2 : ℝ) ^ L') := by
        apply Real.log_le_log
        · exact hnR0
        · exact_mod_cast hnL
      _ = (L' : ℕ) * Real.log 2 := Real.log_pow 2 L'
  have hTwoNat : 2 * n ^ 2 ≤ 2 ^ (2 * L' + 1) := by
    calc
      2 * n ^ 2 ≤ 2 * (2 ^ L') ^ 2 :=
        Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hnL 2)
      _ = 2 ^ (2 * L' + 1) := by
        rw [← pow_mul, ← pow_succ']
        congr 1
        omega
  have hlogTwo :
      Real.log ((2 : ℝ) * n ^ 2) ≤
        (2 * L' + 1 : ℕ) * Real.log 2 := by
    calc
      Real.log ((2 : ℝ) * n ^ 2) ≤
          Real.log ((2 : ℝ) ^ (2 * L' + 1)) := by
        apply Real.log_le_log
        · positivity
        · exact_mod_cast hTwoNat
      _ = (2 * L' + 1 : ℕ) * Real.log 2 :=
        Real.log_pow 2 (2 * L' + 1)
  have hlogSum :
      Real.log (n : ℝ) + Real.log ((2 : ℝ) * n ^ 2) ≤
        (3 * (L' : ℝ) + 1) * Real.log 2 := by
    calc
      Real.log (n : ℝ) + Real.log ((2 : ℝ) * n ^ 2) ≤
          ((L' : ℕ) : ℝ) * Real.log 2 +
            ((2 * L' + 1 : ℕ) : ℝ) * Real.log 2 :=
        add_le_add hlogN hlogTwo
      _ = (3 * (L' : ℝ) + 1) * Real.log 2 := by
        push_cast
        ring
  have hlogSum0 :
      0 ≤ Real.log (n : ℝ) + Real.log ((2 : ℝ) * n ^ 2) := by
    apply add_nonneg
    · exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
    · apply Real.log_nonneg
      have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      nlinarith [sq_nonneg ((n : ℝ) - 1)]
  have hrate :
      (n : ℝ) * ((n : ℝ) - 1) / phase9CleanupB n = (n : ℝ) / 2 := by
    unfold phase9CleanupB
    field_simp
  have hlogConstant :
      ((3 * (L' : ℝ) + 1) * Real.log 2) / 2 ≤
        2 * ((L' : ℝ) + 1) := by
    have hfactor : 0 ≤ (3 * (L' : ℝ) + 1) / 2 := by positivity
    have hmul :=
      mul_le_mul_of_nonneg_left Real.log_two_lt_d9.le hfactor
    norm_num at hmul ⊢
    nlinarith
  rw [hrate]
  calc
    (n : ℝ) / 2 *
          (Real.log (n : ℝ) + Real.log ((2 : ℝ) * n ^ 2)) ≤
        (n : ℝ) / 2 * ((3 * (L' : ℝ) + 1) * Real.log 2) := by
      exact mul_le_mul_of_nonneg_left hlogSum (by positivity)
    _ = (n : ℝ) * (((3 * (L' : ℝ) + 1) * Real.log 2) / 2) := by ring
    _ ≤ (n : ℝ) * (2 * ((L' : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left hlogConstant (by positivity)
    _ = (2 * n * (L' + 1) : ℕ) := by
      push_cast
      ring

#print axioms Transition_phase9_sign_pair
#print axioms Phase9SignsDone_stepOrSelf
#print axioms wrongOutputCount9_stepOrSelf_add_indicators
#print axioms wrongOutputCount9_stepOrSelf_le
#print axioms weightedDropSum_wrongOutputCount9_eq
#print axioms wrongOutputCount9_drift
#print axioms Phase9SignsDone_kernel_escape_zero
#print axioms phase9OutputCleanupRaw
#print axioms phase9OutputCleanup
#print axioms phase9OutputCleanupHorizon_le_two

end Phase9OutputCleanup
end Ripple.PopulationProtocol.ExactMajority
