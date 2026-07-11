
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.

# RoleSplitC0MicroFacts — deterministic +2 hstep facts and gated C0 micro-fact bundle

This file closes the deterministic half of the C0 MGF atoms:
one population-protocol interaction replaces two agents by two agents, so any
`countP` role-count rises by at most two and drops by at most two.  Therefore all
natural deficits `target - count` rise by at most two as well.

The remaining genuinely probabilistic facts are packaged as one gated structure:
rise-probability bounds (`hrise`) and the postwarm killed-kernel/Janson core.  These
are satisfiable, gated fields, never universal claims over arbitrary configurations.

No `sorry` / `admit` / `axiom` / `native_decide`.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.RoleSplitC0MGF

namespace ExactMajority
namespace RoleSplitFloorDischarge

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real BigOperators

open RoleSplitConcentration
open FloorPrefix

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

/-! ## 1. Generic deterministic `countP` +2 facts -/

private theorem countP_pair_le_two
    {Λ : Type*} [DecidableEq Λ]
    (p : Λ → Prop) [DecidablePred p] (a b : Λ) :
    Multiset.countP p ({a, b} : Multiset Λ) ≤ 2 := by
  rw [show ({a, b} : Multiset Λ) = a ::ₘ b ::ₘ 0 from rfl]
  simp only [Multiset.countP_cons, Multiset.countP_zero]
  by_cases ha : p a <;> by_cases hb : p b <;> simp [ha, hb]

/-- A chosen-pair update can increase any `countP` count by at most two. -/
theorem countP_stepOrSelf_le_add_two
    {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    (P : Protocol Λ) (p : Λ → Prop) [DecidablePred p]
    (c : Config Λ) (r₁ r₂ : Λ) :
    Multiset.countP p (Protocol.stepOrSelf P c r₁ r₂)
      ≤ Multiset.countP p c + 2 := by
  classical
  unfold Protocol.stepOrSelf
  by_cases happ : Protocol.Applicable c r₁ r₂
  · rw [if_pos happ]
    change
      Multiset.countP p
          (c - ({r₁, r₂} : Multiset Λ)
            + ({(P.δ r₁ r₂).1, (P.δ r₁ r₂).2} : Multiset Λ))
        ≤ Multiset.countP p c + 2
    rw [Multiset.countP_add]
    have hbase :
        Multiset.countP p (c - ({r₁, r₂} : Multiset Λ))
          ≤ Multiset.countP p c :=
      Multiset.countP_le_of_le _ (Multiset.sub_le_self _ _)
    have hout :
        Multiset.countP p
          ({(P.δ r₁ r₂).1, (P.δ r₁ r₂).2} : Multiset Λ) ≤ 2 :=
      countP_pair_le_two p _ _
    omega
  · rw [if_neg happ]
    omega

/-- A chosen-pair update can decrease any `countP` count by at most two. -/
theorem countP_le_stepOrSelf_add_two
    {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    (P : Protocol Λ) (p : Λ → Prop) [DecidablePred p]
    (c : Config Λ) (r₁ r₂ : Λ) :
    Multiset.countP p c
      ≤ Multiset.countP p (Protocol.stepOrSelf P c r₁ r₂) + 2 := by
  classical
  unfold Protocol.stepOrSelf
  by_cases happ : Protocol.Applicable c r₁ r₂
  · rw [if_pos happ]
    change
      Multiset.countP p c
        ≤ Multiset.countP p
            (c - ({r₁, r₂} : Multiset Λ)
              + ({(P.δ r₁ r₂).1, (P.δ r₁ r₂).2} : Multiset Λ)) + 2
    have hrestore :
        c - ({r₁, r₂} : Multiset Λ) + ({r₁, r₂} : Multiset Λ) = c :=
      Multiset.sub_add_cancel happ
    have hpair :
        Multiset.countP p ({r₁, r₂} : Multiset Λ) ≤ 2 :=
      countP_pair_le_two p r₁ r₂
    have hbase_le :
        Multiset.countP p (c - ({r₁, r₂} : Multiset Λ))
          ≤ Multiset.countP p
            (c - ({r₁, r₂} : Multiset Λ)
              + ({(P.δ r₁ r₂).1, (P.δ r₁ r₂).2} : Multiset Λ)) := by
      rw [Multiset.countP_add]
      omega
    calc
      Multiset.countP p c
          = Multiset.countP p
              (c - ({r₁, r₂} : Multiset Λ) + ({r₁, r₂} : Multiset Λ)) := by
            rw [hrestore]
      _ = Multiset.countP p (c - ({r₁, r₂} : Multiset Λ))
            + Multiset.countP p ({r₁, r₂} : Multiset Λ) := by
            rw [Multiset.countP_add]
      _ ≤ Multiset.countP p (c - ({r₁, r₂} : Multiset Λ)) + 2 := by
            omega
      _ ≤ Multiset.countP p
            (c - ({r₁, r₂} : Multiset Λ)
              + ({(P.δ r₁ r₂).1, (P.δ r₁ r₂).2} : Multiset Λ)) + 2 := by
            omega
  · rw [if_neg happ]
    omega

/-- Support form: any one-step support successor can increase a `countP` count by at most two. -/
theorem countP_stepDistOrSelf_support_le_add_two
    {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    (P : Protocol Λ) (p : Λ → Prop) [DecidablePred p]
    {c c' : Config Λ}
    (hsupp : c' ∈ (P.stepDistOrSelf c).support) :
    Multiset.countP p c' ≤ Multiset.countP p c + 2 := by
  classical
  unfold Protocol.stepDistOrSelf at hsupp
  by_cases hc : 2 ≤ c.card
  · rw [dif_pos hc] at hsupp
    obtain ⟨pair, hpair⟩ := Protocol.stepDist_support P c hc c' hsupp
    rw [← hpair]
    exact countP_stepOrSelf_le_add_two P p c pair.1 pair.2
  · rw [dif_neg hc] at hsupp
    rw [PMF.mem_support_pure_iff] at hsupp
    subst c'
    omega

/-- Support form: any one-step support successor can decrease a `countP` count by at most two. -/
theorem countP_stepDistOrSelf_support_reverse_le_add_two
    {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    (P : Protocol Λ) (p : Λ → Prop) [DecidablePred p]
    {c c' : Config Λ}
    (hsupp : c' ∈ (P.stepDistOrSelf c).support) :
    Multiset.countP p c ≤ Multiset.countP p c' + 2 := by
  classical
  unfold Protocol.stepDistOrSelf at hsupp
  by_cases hc : 2 ≤ c.card
  · rw [dif_pos hc] at hsupp
    obtain ⟨pair, hpair⟩ := Protocol.stepDist_support P c hc c' hsupp
    rw [← hpair]
    exact countP_le_stepOrSelf_add_two P p c pair.1 pair.2
  · rw [dif_neg hc] at hsupp
    rw [PMF.mem_support_pure_iff] at hsupp
    subst c'
    omega

/-- A.e. kernel form of `countP_stepDistOrSelf_support_le_add_two`. -/
theorem ae_countP_step_le_add_two
    {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    (P : Protocol Λ) (p : Λ → Prop) [DecidablePred p]
    (c : Config Λ) :
    ∀ᵐ c' ∂(P.transitionKernel c),
      Multiset.countP p c' ≤ Multiset.countP p c + 2 := by
  classical
  rw [MeasureTheory.ae_iff]
  change (P.stepDistOrSelf c).toMeasure
      {c' : Config Λ | ¬ Multiset.countP p c' ≤ Multiset.countP p c + 2} = 0
  rw [PMF.toMeasure_apply_eq_zero_iff
    (p := P.stepDistOrSelf c)
    (s := {c' : Config Λ | ¬ Multiset.countP p c' ≤ Multiset.countP p c + 2})
    (DiscreteMeasurableSpace.forall_measurableSet _)]
  rw [Set.disjoint_left]
  intro c' hsupp hbad
  exact hbad (countP_stepDistOrSelf_support_le_add_two P p hsupp)

/-- A.e. kernel form of `countP_stepDistOrSelf_support_reverse_le_add_two`. -/
theorem ae_countP_step_reverse_le_add_two
    {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    (P : Protocol Λ) (p : Λ → Prop) [DecidablePred p]
    (c : Config Λ) :
    ∀ᵐ c' ∂(P.transitionKernel c),
      Multiset.countP p c ≤ Multiset.countP p c' + 2 := by
  classical
  rw [MeasureTheory.ae_iff]
  change (P.stepDistOrSelf c).toMeasure
      {c' : Config Λ | ¬ Multiset.countP p c ≤ Multiset.countP p c' + 2} = 0
  rw [PMF.toMeasure_apply_eq_zero_iff
    (p := P.stepDistOrSelf c)
    (s := {c' : Config Λ | ¬ Multiset.countP p c ≤ Multiset.countP p c' + 2})
    (DiscreteMeasurableSpace.forall_measurableSet _)]
  rw [Set.disjoint_left]
  intro c' hsupp hbad
  exact hbad (countP_stepDistOrSelf_support_reverse_le_add_two P p hsupp)

/-- If a count can drop by at most two, then its natural deficit can rise by at most two. -/
theorem ae_natDeficit_step_le_add_two_of_ae_count_reverse
    (target : ℕ) (N : Config (AgentState L K) → ℕ)
    (c : Config (AgentState L K))
    (h :
      ∀ᵐ c' ∂((NonuniformMajority L K).transitionKernel c),
        N c ≤ N c' + 2) :
    ∀ᵐ c' ∂((NonuniformMajority L K).transitionKernel c),
      natDeficit (L := L) (K := K) target N c'
        ≤ natDeficit (L := L) (K := K) target N c + 2 := by
  filter_upwards [h] with c' hc'
  unfold natDeficit
  omega

/-! ## 2. Deterministic `hstep` facts for C0 role/window counts -/

theorem mainCount_hstep_add_two
    (Gate : Config (AgentState L K) → Prop) :
    ∀ c, Gate c →
      ∀ᵐ c' ∂((NonuniformMajority L K).transitionKernel c),
        mainCount (L := L) (K := K) c'
          ≤ mainCount (L := L) (K := K) c + 2 := by
  intro c _
  simpa [mainCount] using
    ae_countP_step_le_add_two
      (P := NonuniformMajority L K)
      (p := fun a : AgentState L K => a.role = .main) c

theorem mainCount_hstep_reverse_add_two
    (Gate : Config (AgentState L K) → Prop) :
    ∀ c, Gate c →
      ∀ᵐ c' ∂((NonuniformMajority L K).transitionKernel c),
        mainCount (L := L) (K := K) c
          ≤ mainCount (L := L) (K := K) c' + 2 := by
  intro c _
  simpa [mainCount] using
    ae_countP_step_reverse_le_add_two
      (P := NonuniformMajority L K)
      (p := fun a : AgentState L K => a.role = .main) c

theorem clockCount_hstep_add_two
    (Gate : Config (AgentState L K) → Prop) :
    ∀ c, Gate c →
      ∀ᵐ c' ∂((NonuniformMajority L K).transitionKernel c),
        clockCount (L := L) (K := K) c'
          ≤ clockCount (L := L) (K := K) c + 2 := by
  intro c _
  simpa [clockCount] using
    ae_countP_step_le_add_two
      (P := NonuniformMajority L K)
      (p := fun a : AgentState L K => a.role = .clock) c

theorem clockCount_hstep_reverse_add_two
    (Gate : Config (AgentState L K) → Prop) :
    ∀ c, Gate c →
      ∀ᵐ c' ∂((NonuniformMajority L K).transitionKernel c),
        clockCount (L := L) (K := K) c
          ≤ clockCount (L := L) (K := K) c' + 2 := by
  intro c _
  simpa [clockCount] using
    ae_countP_step_reverse_le_add_two
      (P := NonuniformMajority L K)
      (p := fun a : AgentState L K => a.role = .clock) c

theorem reserveCount_hstep_add_two
    (Gate : Config (AgentState L K) → Prop) :
    ∀ c, Gate c →
      ∀ᵐ c' ∂((NonuniformMajority L K).transitionKernel c),
        reserveCount (L := L) (K := K) c'
          ≤ reserveCount (L := L) (K := K) c + 2 := by
  intro c _
  simpa [reserveCount] using
    ae_countP_step_le_add_two
      (P := NonuniformMajority L K)
      (p := fun a : AgentState L K => a.role = .reserve) c

theorem reserveCount_hstep_reverse_add_two
    (Gate : Config (AgentState L K) → Prop) :
    ∀ c, Gate c →
      ∀ᵐ c' ∂((NonuniformMajority L K).transitionKernel c),
        reserveCount (L := L) (K := K) c
          ≤ reserveCount (L := L) (K := K) c' + 2 := by
  intro c _
  simpa [reserveCount] using
    ae_countP_step_reverse_le_add_two
      (P := NonuniformMajority L K)
      (p := fun a : AgentState L K => a.role = .reserve) c

/-- Deterministic `+2` hstep for `assignableCount`. -/
theorem assignableCount_hstep_add_two
    (Gate : Config (AgentState L K) → Prop) :
    ∀ c, Gate c →
      ∀ᵐ c' ∂((NonuniformMajority L K).transitionKernel c),
        assignableCount (L := L) (K := K) c'
          ≤ assignableCount (L := L) (K := K) c + 2 := by
  intro c _
  simpa [assignableCount, isAssignableBool] using
    ae_countP_step_le_add_two
      (P := NonuniformMajority L K)
      (p := fun a : AgentState L K =>
        (decide (a.phase.val = 0) && (!a.assigned) &&
          (decide (a.role = .main) || decide (a.role = .cr))) = true) c

/-- Deterministic reverse `+2` hstep for `assignableCount`. -/
theorem assignableCount_hstep_reverse_add_two
    (Gate : Config (AgentState L K) → Prop) :
    ∀ c, Gate c →
      ∀ᵐ c' ∂((NonuniformMajority L K).transitionKernel c),
        assignableCount (L := L) (K := K) c
          ≤ assignableCount (L := L) (K := K) c' + 2 := by
  intro c _
  simpa [assignableCount, isAssignableBool] using
    ae_countP_step_reverse_le_add_two
      (P := NonuniformMajority L K)
      (p := fun a : AgentState L K =>
        (decide (a.phase.val = 0) && (!a.assigned) &&
          (decide (a.role = .main) || decide (a.role = .cr))) = true) c

/-! ## 3. Deterministic deficit hstep facts -/

theorem mainCount_deficit_hstep_add_two
    (target : ℕ) (Gate : Config (AgentState L K) → Prop) :
    ∀ c, Gate c →
      ∀ᵐ c' ∂((NonuniformMajority L K).transitionKernel c),
        natDeficit (L := L) (K := K) target
            (mainCount (L := L) (K := K)) c'
          ≤ natDeficit (L := L) (K := K) target
              (mainCount (L := L) (K := K)) c + 2 := by
  intro c hc
  exact ae_natDeficit_step_le_add_two_of_ae_count_reverse
    (L := L) (K := K) target (mainCount (L := L) (K := K)) c
    (mainCount_hstep_reverse_add_two (L := L) (K := K) Gate c hc)

theorem clockCount_deficit_hstep_add_two
    (target : ℕ) (Gate : Config (AgentState L K) → Prop) :
    ∀ c, Gate c →
      ∀ᵐ c' ∂((NonuniformMajority L K).transitionKernel c),
        natDeficit (L := L) (K := K) target
            (clockCount (L := L) (K := K)) c'
          ≤ natDeficit (L := L) (K := K) target
              (clockCount (L := L) (K := K)) c + 2 := by
  intro c hc
  exact ae_natDeficit_step_le_add_two_of_ae_count_reverse
    (L := L) (K := K) target (clockCount (L := L) (K := K)) c
    (clockCount_hstep_reverse_add_two (L := L) (K := K) Gate c hc)

theorem reserveCount_deficit_hstep_add_two
    (target : ℕ) (Gate : Config (AgentState L K) → Prop) :
    ∀ c, Gate c →
      ∀ᵐ c' ∂((NonuniformMajority L K).transitionKernel c),
        natDeficit (L := L) (K := K) target
            (reserveCount (L := L) (K := K)) c'
          ≤ natDeficit (L := L) (K := K) target
              (reserveCount (L := L) (K := K)) c + 2 := by
  intro c hc
  exact ae_natDeficit_step_le_add_two_of_ae_count_reverse
    (L := L) (K := K) target (reserveCount (L := L) (K := K)) c
    (reserveCount_hstep_reverse_add_two (L := L) (K := K) Gate c hc)

theorem assignableCount_deficit_hstep_add_two
    (target : ℕ) (Gate : Config (AgentState L K) → Prop) :
    ∀ c, Gate c →
      ∀ᵐ c' ∂((NonuniformMajority L K).transitionKernel c),
        natDeficit (L := L) (K := K) target
            (assignableCount (L := L) (K := K)) c'
          ≤ natDeficit (L := L) (K := K) target
              (assignableCount (L := L) (K := K)) c + 2 := by
  intro c hc
  exact ae_natDeficit_step_le_add_two_of_ae_count_reverse
    (L := L) (K := K) target (assignableCount (L := L) (K := K)) c
    (assignableCount_hstep_reverse_add_two (L := L) (K := K) Gate c hc)

/-! ## 4. Gated rise micro-facts and hdrift instantiators -/

/--
A gated rise-probability micro-fact for a natural count.

This is the remaining genuine interaction-PMF content for a count MGF atom.
It is explicitly gated and satisfiable; it is never asserted on arbitrary configs.
-/
structure GatedCountRiseFact
    (Gate : Config (AgentState L K) → Prop)
    (N : Config (AgentState L K) → ℕ)
    (q : ℝ) where
  hq0 : 0 ≤ q
  hrise :
    ∀ c, Gate c →
      ((NonuniformMajority L K).transitionKernel c)
        {c' | N c < N c'} ≤ ENNReal.ofReal q

/--
A gated rise-probability micro-fact for a natural deficit.
-/
structure GatedDeficitRiseFact
    (Gate : Config (AgentState L K) → Prop)
    (target : ℕ)
    (N : Config (AgentState L K) → ℕ)
    (q : ℝ) where
  hq0 : 0 ≤ q
  hrise :
    ∀ c, Gate c →
      ((NonuniformMajority L K).transitionKernel c)
        {c' |
          natDeficit (L := L) (K := K) target N c
            < natDeficit (L := L) (K := K) target N c'} ≤ ENNReal.ofReal q

/-- `mainCount` upper-tail hdrift from the deterministic hstep and a gated rise fact. -/
theorem mainCount_upper_hdrift_of_rise
    (Gate : Config (AgentState L K) → Prop)
    (lam q : ℝ) (hlam : 0 ≤ lam)
    (R : GatedCountRiseFact (L := L) (K := K)
      Gate (mainCount (L := L) (K := K)) q) :
    ∀ c, Gate c →
      ∫⁻ c',
          countExpPot (L := L) (K := K)
            (mainCount (L := L) (K := K)) lam c'
          ∂((NonuniformMajority L K).transitionKernel c)
        ≤ ENNReal.ofReal (1 + q * (Real.exp (2 * lam) - 1))
            * countExpPot (L := L) (K := K)
                (mainCount (L := L) (K := K)) lam c :=
  mainCount_upper_exp_mgf_drift_add_two
    (L := L) (K := K)
    lam q hlam R.hq0 Gate
    (mainCount_hstep_add_two (L := L) (K := K) Gate)
    R.hrise

/-- `mainCount` lower-tail deficit hdrift from deterministic hstep and gated deficit rise. -/
theorem mainCount_lower_hdrift_of_deficit_rise
    (target : ℕ) (Gate : Config (AgentState L K) → Prop)
    (lam q : ℝ) (hlam : 0 ≤ lam)
    (R : GatedDeficitRiseFact (L := L) (K := K)
      Gate target (mainCount (L := L) (K := K)) q) :
    ∀ c, Gate c →
      ∫⁻ c',
          deficitExpPot (L := L) (K := K) target
            (mainCount (L := L) (K := K)) lam c'
          ∂((NonuniformMajority L K).transitionKernel c)
        ≤ ENNReal.ofReal (1 + q * (Real.exp (2 * lam) - 1))
            * deficitExpPot (L := L) (K := K) target
                (mainCount (L := L) (K := K)) lam c :=
  mainCount_lower_deficit_mgf_drift_add_two
    (L := L) (K := K)
    target lam q hlam R.hq0 Gate
    (mainCount_deficit_hstep_add_two (L := L) (K := K) target Gate)
    R.hrise

/-- `clockCount` lower-tail deficit hdrift from deterministic hstep and gated deficit rise. -/
theorem clockCount_lower_hdrift_of_deficit_rise
    (target : ℕ) (Gate : Config (AgentState L K) → Prop)
    (lam q : ℝ) (hlam : 0 ≤ lam)
    (R : GatedDeficitRiseFact (L := L) (K := K)
      Gate target (clockCount (L := L) (K := K)) q) :
    ∀ c, Gate c →
      ∫⁻ c',
          deficitExpPot (L := L) (K := K) target
            (clockCount (L := L) (K := K)) lam c'
          ∂((NonuniformMajority L K).transitionKernel c)
        ≤ ENNReal.ofReal (1 + q * (Real.exp (2 * lam) - 1))
            * deficitExpPot (L := L) (K := K) target
                (clockCount (L := L) (K := K)) lam c :=
  clockCount_lower_deficit_mgf_drift_add_two
    (L := L) (K := K)
    target lam q hlam R.hq0 Gate
    (clockCount_deficit_hstep_add_two (L := L) (K := K) target Gate)
    R.hrise

/-- `reserveCount` lower-tail deficit hdrift from deterministic hstep and gated deficit rise. -/
theorem reserveCount_lower_hdrift_of_deficit_rise
    (target : ℕ) (Gate : Config (AgentState L K) → Prop)
    (lam q : ℝ) (hlam : 0 ≤ lam)
    (R : GatedDeficitRiseFact (L := L) (K := K)
      Gate target (reserveCount (L := L) (K := K)) q) :
    ∀ c, Gate c →
      ∫⁻ c',
          deficitExpPot (L := L) (K := K) target
            (reserveCount (L := L) (K := K)) lam c'
          ∂((NonuniformMajority L K).transitionKernel c)
        ≤ ENNReal.ofReal (1 + q * (Real.exp (2 * lam) - 1))
            * deficitExpPot (L := L) (K := K) target
                (reserveCount (L := L) (K := K)) lam c :=
  reserveCount_lower_deficit_mgf_drift_add_two
    (L := L) (K := K)
    target lam q hlam R.hq0 Gate
    (reserveCount_deficit_hstep_add_two (L := L) (K := K) target Gate)
    R.hrise

/-- `assignableCount` deficit hdrift from deterministic hstep and gated deficit rise. -/
theorem assignableCount_deficit_hdrift_of_rise
    (target : ℕ) (Gate : Config (AgentState L K) → Prop)
    (lam q : ℝ) (hlam : 0 ≤ lam)
    (R : GatedDeficitRiseFact (L := L) (K := K)
      Gate target (assignableCount (L := L) (K := K)) q) :
    ∀ c, Gate c →
      ∫⁻ c',
          deficitExpPot (L := L) (K := K) target
            (assignableCount (L := L) (K := K)) lam c'
          ∂((NonuniformMajority L K).transitionKernel c)
        ≤ ENNReal.ofReal (1 + q * (Real.exp (2 * lam) - 1))
            * deficitExpPot (L := L) (K := K) target
                (assignableCount (L := L) (K := K)) lam c :=
  assignableCount_deficit_mgf_drift_add_two
    (L := L) (K := K)
    target lam q hlam R.hq0 Gate
    (assignableCount_deficit_hstep_add_two (L := L) (K := K) target Gate)
    R.hrise

/-! ## 5. One explicit gated bundle for the remaining probabilistic C0 micro-facts -/

/--
The remaining genuine C0 probabilistic micro-facts.

All fields are gated.  This is the intended single handoff point for the interaction-PMF
rise/death/Janson calculations if they are not discharged in the same file.

* `mainUpper`, `mainLower`, `clockLower`, `reserveLower`, `assignableLower`
  are the per-step rise-probability bounds consumed by the MGF hdrift builders.
* `postwarmCore` is the killed-kernel/Janson core consumed by `phase0_stage1_postwarm_whp`.

No field is a universal over arbitrary configurations.
-/
structure C0GatedMicroFacts
    (Gate : Config (AgentState L K) → Prop)
    (n a₀ uMin Tstage : ℕ) (hn2 : 2 ≤ n)
    (mainLowerTarget mainUpperQTarget clockTarget reserveTarget assignTarget : ℕ)
    (qMainUpper qMainLower qClockLower qReserveLower qAssignLower : ℝ)
    (εcore εshell εfloorFail : ℝ≥0∞) where
  mainUpper :
    GatedCountRiseFact (L := L) (K := K)
      Gate (mainCount (L := L) (K := K)) qMainUpper
  mainLower :
    GatedDeficitRiseFact (L := L) (K := K)
      Gate mainLowerTarget (mainCount (L := L) (K := K)) qMainLower
  clockLower :
    GatedDeficitRiseFact (L := L) (K := K)
      Gate clockTarget (clockCount (L := L) (K := K)) qClockLower
  reserveLower :
    GatedDeficitRiseFact (L := L) (K := K)
      Gate reserveTarget (reserveCount (L := L) (K := K)) qReserveLower
  assignableLower :
    GatedDeficitRiseFact (L := L) (K := K)
      Gate assignTarget (assignableCount (L := L) (K := K)) qAssignLower

  /-- The corrected postwarm Stage-1 core, gated on `Phase0WarmGood`. -/
  postwarmCore :
    PostwarmStage1Core (L := L) (K := K)
      n a₀ uMin Tstage hn2 εcore εshell εfloorFail

/--
Convenience projection: build the corrected postwarm Stage-1 theorem from the
single gated micro-fact bundle.
-/
theorem postwarm_stage1_from_microfacts
    {Gate : Config (AgentState L K) → Prop}
    {n a₀ uMin Tstage : ℕ} {hn2 : 2 ≤ n}
    {mainLowerTarget mainUpperQTarget clockTarget reserveTarget assignTarget : ℕ}
    {qMainUpper qMainLower qClockLower qReserveLower qAssignLower : ℝ}
    {εcore εshell εfloorFail εstage : ℝ≥0∞}
    (M : C0GatedMicroFacts (L := L) (K := K)
      Gate n a₀ uMin Tstage hn2
      mainLowerTarget mainUpperQTarget clockTarget reserveTarget assignTarget
      qMainUpper qMainLower qClockLower qReserveLower qAssignLower
      εcore εshell εfloorFail)
    (hstageBudget : εcore + (εshell + εfloorFail) ≤ εstage) :
    ∀ y,
      Phase0WarmGood (L := L) (K := K) n a₀ uMin y →
      ((NonuniformMajority L K).transitionKernel ^ Tstage) y
        {z | ¬ roleSplitGoodMile (L := L) (K := K) n hn2 z} ≤ εstage :=
  phase0_stage1_postwarm_whp
    (L := L) (K := K)
    n a₀ uMin Tstage hn2
    εcore εshell εfloorFail εstage
    M.postwarmCore hstageBudget

end RoleSplitFloorDischarge
end ExactMajority
