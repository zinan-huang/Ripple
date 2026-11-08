/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Outcome-aware fast assembly

This file assembles the genuine nineteen-instance fast prefix

`work₀, seam₀, ..., seam₈, work₉`.

It is intentionally independent of `Theorem31.TerminalAssemblyR`: no Phase-10
work instance and no seam from Phase 9 to Phase 10 occur in its data.  Every
active instance is lifted with the absorbing target `StableDone`.  Thus an
execution that stabilizes in Phase 2 or Phase 4 remains successful throughout
the fixed-length prefix, while an execution that is not done must satisfy the
reachable-scoped seam-entry obligations.
-/

import Ripple.PopulationProtocol.ExactMajority.Probability.OutcomePhase
import Ripple.PopulationProtocol.ExactMajority.Probability.Theorem31

namespace Ripple.PopulationProtocol.ExactMajority
namespace OutcomeFastAssembly

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

attribute [local instance] Classical.propDecidable

noncomputable section

variable {L K : ℕ}

/-- The fixed successful outcome for the fast chain. -/
def Done (init : Config (AgentState L K)) (c : Config (AgentState L K)) : Prop :=
  c ∈ StableDone L K init

/-- `Done` is one-step absorbing under the concrete protocol kernel. -/
theorem done_kernel_absorbing
    (init x : Config (AgentState L K)) (hx : Done (L := L) (K := K) init x) :
    (NonuniformMajority L K).transitionKernel x
        {y | ¬ Done (L := L) (K := K) init y} = 0 := by
  change (NonuniformMajority L K).transitionKernel x
    (StableDone L K init)ᶜ = 0
  exact StableDone_kernel_absorbing L K init x hx

/-- Reachable-scoped one-step seed from an active work outcome into a genuine
seam entry.  Unlike the older global seed constructor, this constructor uses
the reachability hypothesis carried by `PhaseConvergenceWR`. -/
def advanceEntryStepActiveWR
    (init : Config (AgentState L K)) (p n : ℕ)
    (DoneP workPost : Config (AgentState L K) → Prop)
    (hEntry : ∀ c : Config (AgentState L K),
      (NonuniformMajority L K).Reachable init c →
      workPost c → ¬ DoneP c →
      ((NonuniformMajority L K).transitionKernel ^ 1) c
        {c' | ¬ AdvanceEntryNoOvershoot.AdvanceEntry
          (L := L) (K := K) p n c'} = 0)
    (hExact : ∀ c : Config (AgentState L K),
      (NonuniformMajority L K).Reachable init c →
      workPost c → ¬ DoneP c →
      ((NonuniformMajority L K).transitionKernel ^ 1) c
        {c' | ¬ AdvanceEntryPhaseCeiling.AdvanceEntryExactIfReset
          (L := L) (K := K) p n c'} = 0) :
    PhaseConvergenceWR (NonuniformMajority L K) init where
  Pre := fun c => workPost c ∧ ¬ DoneP c
  Post := fun c =>
    AdvanceEntryNoOvershoot.AdvanceEntry (L := L) (K := K) p n c ∧
      AdvanceEntryPhaseCeiling.AdvanceEntryExactIfReset (L := L) (K := K) p n c
  t := 1
  ε := 0
  convergence := by
    intro c hreach hPre
    have hA := hEntry c hreach hPre.1 hPre.2
    have hB := hExact c hreach hPre.1 hPre.2
    have hsub :
        {c' : Config (AgentState L K) |
          ¬ (AdvanceEntryNoOvershoot.AdvanceEntry
              (L := L) (K := K) p n c' ∧
            AdvanceEntryPhaseCeiling.AdvanceEntryExactIfReset
              (L := L) (K := K) p n c')}
          ⊆
        {c' | ¬ AdvanceEntryNoOvershoot.AdvanceEntry
            (L := L) (K := K) p n c'} ∪
          {c' | ¬ AdvanceEntryPhaseCeiling.AdvanceEntryExactIfReset
            (L := L) (K := K) p n c'} := by
      intro c' hc'
      simp only [Set.mem_setOf_eq, Set.mem_union, not_and_or] at hc' ⊢
      exact hc'
    calc
      ((NonuniformMajority L K).transitionKernel ^ 1) c
          {c' | ¬ (AdvanceEntryNoOvershoot.AdvanceEntry
              (L := L) (K := K) p n c' ∧
            AdvanceEntryPhaseCeiling.AdvanceEntryExactIfReset
              (L := L) (K := K) p n c')}
        ≤ ((NonuniformMajority L K).transitionKernel ^ 1) c
            ({c' | ¬ AdvanceEntryNoOvershoot.AdvanceEntry
                (L := L) (K := K) p n c'} ∪
              {c' | ¬ AdvanceEntryPhaseCeiling.AdvanceEntryExactIfReset
                (L := L) (K := K) p n c'}) := measure_mono hsub
      _ ≤ ((NonuniformMajority L K).transitionKernel ^ 1) c
            {c' | ¬ AdvanceEntryNoOvershoot.AdvanceEntry
              (L := L) (K := K) p n c'} +
          ((NonuniformMajority L K).transitionKernel ^ 1) c
            {c' | ¬ AdvanceEntryPhaseCeiling.AdvanceEntryExactIfReset
              (L := L) (K := K) p n c'} := measure_union_le _ _
      _ = 0 := by rw [hA, hB]; simp
      _ ≤ ((0 : ℝ≥0) : ℝ≥0∞) := le_rfl

/-- Data for the outcome-aware nineteen-instance prefix. -/
structure Assembly (n : ℕ) (init : Config (AgentState L K)) where
  /-- Work instances 0 through 9. -/
  work : Fin 10 → PhaseConvergenceW (NonuniformMajority L K).transitionKernel
  /-- Source phase of seams 0 through 8. -/
  seamP : Fin 9 → ℕ
  /-- Horizons of seams 0 through 8. -/
  seamT : Fin 9 → ℕ
  εovershoot : Fin 9 → ℝ≥0
  hDrift : ∀ (k : Fin 9) (c : Config (AgentState L K)),
      AdvanceEntryNoOvershoot.AdvancePre
        (L := L) (K := K) (seamP k) n c →
      ((NonuniformMajority L K).transitionKernel ^ (seamT k)) c
          {c' | ¬ AdvanceEpidemics.allPhaseGe
            (L := L) (K := K) (seamP k + 1) n c'}
        ≤ (Theorem31.advanceHalfBudget n : ℝ≥0∞)
  hNoOvershoot : ∀ (k : Fin 9) (c : Config (AgentState L K)),
      (NonuniformMajority L K).Reachable init c →
      AdvanceEntryNoOvershoot.AdvanceEntry
        (L := L) (K := K) (seamP k) n c →
      AdvanceEntryPhaseCeiling.AdvanceEntryExactIfReset
        (L := L) (K := K) (seamP k) n c →
      ((NonuniformMajority L K).transitionKernel ^ (seamT k)) c
          {c' | ¬ AdvanceNoOvershoot.NoOvershoot
            (L := L) (K := K) (seamP k) c'}
        ≤ (εovershoot k : ℝ≥0∞)
  /-- The existing terminal payload residual, specialized to the nine seams
  of the fast prefix.  This keeps the reachable next-work tail and its budget
  in the same interface used by the terminal assembly. -/
  payload : Theorem31.TerminalAdvancePayloadHypotheses
    (L := L) (K := K) init n 9 work seamP seamT εovershoot
  /-- The work-to-entry seed is required only on reachable, not-yet-done
  outcomes of the current work instance. -/
  hEntry : ∀ (k : Fin 9) (c : Config (AgentState L K)),
      (NonuniformMajority L K).Reachable init c →
      (work k.castSucc).Post c →
      c ∉ StableDone L K init →
      ((NonuniformMajority L K).transitionKernel ^ 1) c
          {c' | ¬ AdvanceEntryNoOvershoot.AdvanceEntry
            (L := L) (K := K) (seamP k) n c'} = 0
  hExact : ∀ (k : Fin 9) (c : Config (AgentState L K)),
      (NonuniformMajority L K).Reachable init c →
      (work k.castSucc).Post c →
      c ∉ StableDone L K init →
      ((NonuniformMajority L K).transitionKernel ^ 1) c
          {c' | ¬ AdvanceEntryPhaseCeiling.AdvanceEntryExactIfReset
            (L := L) (K := K) (seamP k) n c'} = 0

/-- Active part of work `k`: the work postcondition holds and the execution has
not already stabilized. -/
def activePre {n : ℕ} {init : Config (AgentState L K)}
    (asm : Assembly (L := L) (K := K) n init) (k : Fin 9)
    (c : Config (AgentState L K)) : Prop :=
  (asm.work k.castSucc).Post c ∧ c ∉ StableDone L K init

/-- The reachable-scoped one-step seed for seam `k`. -/
def seedInstance {n : ℕ} {init : Config (AgentState L K)}
    (asm : Assembly (L := L) (K := K) n init) (k : Fin 9) :
    PhaseConvergenceWR (NonuniformMajority L K) init :=
  advanceEntryStepActiveWR (L := L) (K := K) init (asm.seamP k) n
    (Done (L := L) (K := K) init) (asm.work k.castSucc).Post
    (asm.hEntry k) (asm.hExact k)

/-- Epidemic/no-overshoot/payload part of seam `k`.  Its postcondition contains
the next work precondition. -/
def advanceCore {n : ℕ} {init : Config (AgentState L K)}
    (asm : Assembly (L := L) (K := K) n init) (k : Fin 9) :
    PhaseConvergenceWR (NonuniformMajority L K) init :=
  Theorem31.advanceEpidemicExactWR (L := L) (K := K)
    init (asm.seamP k) n (asm.seamT k)
    (Theorem31.advanceHalfBudget n) (asm.εovershoot k) (asm.payload.εpayload k)
    (asm.hDrift k) (asm.hNoOvershoot k)
    (asm.work ⟨k.val + 1, by omega⟩).Pre (asm.payload.hNextPre k)

/-- Active seed followed by the reachable seam core. -/
def activeAdvance {n : ℕ} {init : Config (AgentState L K)}
    (asm : Assembly (L := L) (K := K) n init) (k : Fin 9) :
    PhaseConvergenceWR (NonuniformMajority L K) init where
  Pre := activePre asm k
  Post := (advanceCore asm k).Post
  t := 1 + asm.seamT k
  ε := Theorem31.advanceHalfBudget n + asm.εovershoot k + asm.payload.εpayload k
  convergence := by
    intro c hreach hPre
    have hcompose := composeWR_two_phases (NonuniformMajority L K)
      (seedInstance asm k) (advanceCore asm k)
      (fun _ _ hseed => hseed) c hreach hPre
    have hts :
        (seedInstance asm k).t + (advanceCore asm k).t =
          1 + asm.seamT k := rfl
    have hes :
        ((seedInstance asm k).ε : ℝ≥0∞) + ((advanceCore asm k).ε : ℝ≥0∞) =
          ((Theorem31.advanceHalfBudget n + asm.εovershoot k +
              asm.payload.εpayload k : ℝ≥0) :
            ℝ≥0∞) := by
      change (0 : ℝ≥0∞) +
          ((Theorem31.advanceHalfBudget n + asm.εovershoot k +
              asm.payload.εpayload k : ℝ≥0) :
            ℝ≥0∞) = _
      rw [zero_add]
    simpa only [hts, hes] using hcompose

@[simp] theorem activeAdvance_Pre {n : ℕ} {init : Config (AgentState L K)}
    (asm : Assembly (L := L) (K := K) n init) (k : Fin 9) :
    (activeAdvance asm k).Pre = activePre asm k := rfl

@[simp] theorem activeAdvance_Post {n : ℕ} {init : Config (AgentState L K)}
    (asm : Assembly (L := L) (K := K) n init) (k : Fin 9) :
    (activeAdvance asm k).Post = (advanceCore asm k).Post := rfl

/-- A work instance lifted with the absorbing `Done` outcome. -/
def workInstance {n : ℕ} {init : Config (AgentState L K)}
    (asm : Assembly (L := L) (K := K) n init) (k : Fin 10) :
    PhaseConvergenceWR (NonuniformMajority L K) init :=
  PhaseConvergenceWR.withAbsorbingDone
    (NonuniformMajority L K) init (Done (L := L) (K := K) init)
    (done_kernel_absorbing (L := L) (K := K) init)
    (PhaseConvergenceWR.ofW (NonuniformMajority L K) init (asm.work k))

/-- A seam instance lifted with the absorbing `Done` outcome. -/
def advanceInstance {n : ℕ} {init : Config (AgentState L K)}
    (asm : Assembly (L := L) (K := K) n init) (k : Fin 9) :
    PhaseConvergenceWR (NonuniformMajority L K) init :=
  PhaseConvergenceWR.withAbsorbingDone
    (NonuniformMajority L K) init (Done (L := L) (K := K) init)
    (done_kernel_absorbing (L := L) (K := K) init)
    (activeAdvance asm k)

/-- Even fast-prefix index to work index. -/
def workIdx (i : Fin 19) : Fin 10 := ⟨i.val / 2, by omega⟩

/-- Odd fast-prefix index to seam index. -/
def advanceIdx (i : Fin 19) (hodd : i.val % 2 = 1) : Fin 9 :=
  ⟨i.val / 2, by omega⟩

@[simp] theorem workIdx_val (i : Fin 19) : (workIdx i).val = i.val / 2 := rfl

@[simp] theorem advanceIdx_val (i : Fin 19) (hodd : i.val % 2 = 1) :
    (advanceIdx i hodd).val = i.val / 2 := rfl

/-- The outcome-aware nineteen-instance family. -/
def phases {n : ℕ} {init : Config (AgentState L K)}
    (asm : Assembly (L := L) (K := K) n init) :
    Fin 19 → PhaseConvergenceWR (NonuniformMajority L K) init :=
  fun i =>
    if h : i.val % 2 = 0 then workInstance asm (workIdx i)
    else advanceInstance asm (advanceIdx i (by omega))

@[simp] theorem phases_even {n : ℕ} {init : Config (AgentState L K)}
    (asm : Assembly (L := L) (K := K) n init)
    (i : Fin 19) (h : i.val % 2 = 0) :
    phases asm i = workInstance asm (workIdx i) := by
  simp only [phases, dif_pos h]

@[simp] theorem phases_odd {n : ℕ} {init : Config (AgentState L K)}
    (asm : Assembly (L := L) (K := K) n init)
    (i : Fin 19) (h : i.val % 2 = 1) :
    phases asm i = advanceInstance asm (advanceIdx i h) := by
  simp only [phases, dif_neg (by omega : ¬ i.val % 2 = 0)]

/-- Outcome-aware bridge from work `k` to active seam `k`. -/
theorem advanceInstance_pre_of_workInstance_post {n : ℕ} {init : Config (AgentState L K)}
    (asm : Assembly (L := L) (K := K) n init)
    (k : Fin 9) (c : Config (AgentState L K))
    (hreach : (NonuniformMajority L K).Reachable init c)
    (hpost : (workInstance asm k.castSucc).Post c) :
    (advanceInstance asm k).Pre c := by
  apply PhaseConvergenceWR.withAbsorbingDone_chain
    (NonuniformMajority L K) init (Done (L := L) (K := K) init)
    (done_kernel_absorbing (L := L) (K := K) init)
    (PhaseConvergenceWR.ofW (NonuniformMajority L K) init (asm.work k.castSucc))
    (activeAdvance asm k)
  · intro x _ hx
    by_cases hDone : Done (L := L) (K := K) init x
    · exact Or.inl hDone
    · exact Or.inr ⟨hx, hDone⟩
  · exact hreach
  · exact hpost

/-- Outcome-aware bridge from active seam `k` to work `k+1`. -/
theorem workInstance_pre_of_advanceInstance_post {n : ℕ} {init : Config (AgentState L K)}
    (asm : Assembly (L := L) (K := K) n init)
    (k : Fin 9) (c : Config (AgentState L K))
    (hreach : (NonuniformMajority L K).Reachable init c)
    (hpost : (advanceInstance asm k).Post c) :
    (workInstance asm ⟨k.val + 1, by omega⟩).Pre c := by
  apply PhaseConvergenceWR.withAbsorbingDone_chain
    (NonuniformMajority L K) init (Done (L := L) (K := K) init)
    (done_kernel_absorbing (L := L) (K := K) init)
    (activeAdvance asm k)
    (PhaseConvergenceWR.ofW (NonuniformMajority L K) init
      (asm.work ⟨k.val + 1, by omega⟩))
  · intro x _ hx
    exact Or.inr hx.2
  · exact hreach
  · exact hpost

/-- Chain law for the outcome-aware nineteen-instance family. -/
theorem phases_h_chain {n : ℕ} {init : Config (AgentState L K)}
    (asm : Assembly (L := L) (K := K) n init) :
    ∀ (i : Fin 19) (hi : i.val + 1 < 19),
      ∀ x, (NonuniformMajority L K).Reachable init x →
        (phases asm i).Post x →
          (phases asm ⟨i.val + 1, hi⟩).Pre x := by
  intro i hi x hreach hpost
  have hjval : (⟨i.val + 1, hi⟩ : Fin 19).val = i.val + 1 := rfl
  rcases Nat.even_or_odd i.val with hev | hod
  · have hi0 : i.val % 2 = 0 := Nat.even_iff.mp hev
    have hsucc1 : (⟨i.val + 1, hi⟩ : Fin 19).val % 2 = 1 := by
      rw [hjval]
      omega
    rw [phases_even asm i hi0] at hpost
    rw [phases_odd asm ⟨i.val + 1, hi⟩ hsucc1]
    set k : Fin 9 := advanceIdx ⟨i.val + 1, hi⟩ hsucc1 with hkdef
    have hkw : k.castSucc = workIdx i := by
      apply Fin.ext
      have hkval : k.val = i.val / 2 := by
        rw [hkdef, advanceIdx_val, hjval]
        omega
      rw [Fin.val_castSucc, hkval, workIdx_val]
    have hbridge := advanceInstance_pre_of_workInstance_post asm k x hreach
    rw [hkw] at hbridge
    exact hbridge hpost
  · have hi1 : i.val % 2 = 1 := Nat.odd_iff.mp hod
    have hsucc0 : (⟨i.val + 1, hi⟩ : Fin 19).val % 2 = 0 := by
      rw [hjval]
      omega
    rw [phases_odd asm i hi1] at hpost
    rw [phases_even asm ⟨i.val + 1, hi⟩ hsucc0]
    set k : Fin 9 := advanceIdx i hi1 with hkdef
    have hkw : (⟨k.val + 1, by omega⟩ : Fin 10) = workIdx ⟨i.val + 1, hi⟩ := by
      apply Fin.ext
      have hkval : k.val = i.val / 2 := by rw [hkdef, advanceIdx_val]
      rw [Fin.val_mk, hkval, workIdx_val, hjval]
      omega
    have hbridge := workInstance_pre_of_advanceInstance_post asm k x hreach
    rw [hkw] at hbridge
    exact hbridge hpost

/-- The final prefix instance is lifted work 9. -/
theorem phases_last_eq_work9 {n : ℕ} {init : Config (AgentState L K)}
    (asm : Assembly (L := L) (K := K) n init) :
    phases asm ⟨19 - 1, by omega⟩ = workInstance asm ⟨9, by omega⟩ := by
  rw [phases_even asm _ (by norm_num)]
  congr 2

/-- Conditional fast tail to `StableDone`, with an opaque total time and error
sum.  The last active work outcome is required to imply `Done` only on states
reachable from the actual initial configuration. -/
theorem done_tail
    {n : ℕ} {init : Config (AgentState L K)}
    (asm : Assembly (L := L) (K := K) n init)
    (hStart : (asm.work ⟨0, by omega⟩).Pre init)
    (T : ℕ) (Esum : ℝ≥0∞)
    (hT : T = ∑ i : Fin 19, (phases asm i).t)
    (hEsum : Esum = ∑ i : Fin 19, ((phases asm i).ε : ℝ≥0∞))
    (Cphase : Fin 19 → ℕ)
    (ht : ∀ i, (phases asm i).t ≤ Cphase i * n * (L + 1))
    (hε : ∀ i, ((phases asm i).ε : ℝ≥0∞) ≤
      1 / (n : ℝ≥0∞) ^ 2)
    (hWork9Done : ∀ c : Config (AgentState L K),
      (NonuniformMajority L K).Reachable init c →
      (asm.work ⟨9, by omega⟩).Post c →
      c ∈ StableDone L K init) :
    ((NonuniformMajority L K).transitionKernel ^ T) init
        (StableDone L K init)ᶜ
      ≤ (19 : ℝ≥0∞) / (n : ℝ≥0∞) ^ 2
    ∧ T ≤ (∑ i, Cphase i) * n * (L + 1) := by
  have hx₀ : (phases asm ⟨0, by omega⟩).Pre init := by
    rw [phases_even asm _ (by norm_num)]
    exact Or.inr (by simpa [workIdx] using hStart)
  have hreach₀ : (NonuniformMajority L K).Reachable init init :=
    Relation.ReflTransGen.refl
  have hcompose :=
    composeWR_n_phases (NonuniformMajority L K)
      (m := 19) (by omega) (phases asm)
      (phases_h_chain asm) init hreach₀ hx₀
  rw [← hT, ← hEsum] at hcompose
  have hnotReach :
      ((NonuniformMajority L K).transitionKernel ^ T) init
          {c | ¬ (NonuniformMajority L K).Reachable init c} = 0 :=
    Protocol.transitionKernel_pow_not_reachable_eq_zero
      (NonuniformMajority L K) init T
  have hcover :
      (StableDone L K init)ᶜ ⊆
        {c | ¬ (phases asm ⟨19 - 1, by omega⟩).Post c} ∪
          {c | ¬ (NonuniformMajority L K).Reachable init c} := by
    intro c hc
    by_cases hreach : (NonuniformMajority L K).Reachable init c
    · left
      intro hlast
      have hlast9 : (workInstance asm ⟨9, by omega⟩).Post c := by
        rw [phases_even asm _ (by norm_num)] at hlast
        simpa [workIdx] using hlast
      rcases hlast9 with hDone | hwork9
      · exact hc hDone
      · exact hc (hWork9Done c hreach hwork9)
    · exact Or.inr hreach
  have htailEsum :
      ((NonuniformMajority L K).transitionKernel ^ T) init
          (StableDone L K init)ᶜ ≤ Esum := by
    calc
      ((NonuniformMajority L K).transitionKernel ^ T) init
          (StableDone L K init)ᶜ
        ≤ ((NonuniformMajority L K).transitionKernel ^ T) init
            ({c | ¬ (phases asm ⟨19 - 1, by omega⟩).Post c} ∪
              {c | ¬ (NonuniformMajority L K).Reachable init c}) :=
          measure_mono hcover
      _ ≤ ((NonuniformMajority L K).transitionKernel ^ T) init
            {c | ¬ (phases asm ⟨19 - 1, by omega⟩).Post c} +
          ((NonuniformMajority L K).transitionKernel ^ T) init
            {c | ¬ (NonuniformMajority L K).Reachable init c} :=
          measure_union_le _ _
      _ = ((NonuniformMajority L K).transitionKernel ^ T) init
            {c | ¬ (phases asm ⟨19 - 1, by omega⟩).Post c} := by
          rw [hnotReach, add_zero]
      _ ≤ Esum := hcompose
  have hEsumBound : Esum ≤ (19 : ℝ≥0∞) / (n : ℝ≥0∞) ^ 2 := by
    rw [hEsum]
    exact BudgetTightening.sum_inv_sq_le
      (m := 19) (n := n) (fun i => (phases asm i).ε) hε
  refine ⟨htailEsum.trans hEsumBound, ?_⟩
  rw [hT]
  exact total_time_le_W (fun i => (phases asm i).t) Cphase ht

#print axioms advanceEntryStepActiveWR
#print axioms phases_h_chain
#print axioms done_tail

end
end OutcomeFastAssembly
end Ripple.PopulationProtocol.ExactMajority
