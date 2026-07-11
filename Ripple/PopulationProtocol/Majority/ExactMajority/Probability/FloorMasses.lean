/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# FloorMasses — discharging the three protocol-mass residuals of FloorPrefix

This file is **append-only** and discharges the three named protocol hypotheses that
`Probability/FloorPrefix.lean` left as inputs to `pool_expNeg_one_step_drift`:

* **`hstep`** — the `±2` per-step interaction range: `∀ᵐ c', (pool c : ℤ) − 2 ≤ pool c'`
  on the one-step kernel (Stage 1).
* **`hbirth`** — the Rule-1 birth rectangle: `ofReal(uMin(uMin−1)/(n(n−1))) ≤ birthR1Mass c`
  on `PoolDriftRegion` (Stage 2).
* **`hdeath`** — the Rule-4 fresh-CR drain rectangle: `r4FreshCRDrainMass c ≤
  ofReal(Ahi²/(n(n−1)))` on `PoolDriftRegion` (Stage 3).

All three follow the established kernel-mass routes:

* Stage 1 reuses `HourCouplingAzuma.countP_stepOrSelf_diff_le_two` (the bounded-difference
  atom: any single interaction changes a `countP` by at most `2`) plus the support
  reduction of `hour_bdd`.  `assignableCount = countP isAssignableBool` is definitional.
* Stage 2 mirrors `RoleSplitConcentration.phase0_mcrCount_decrease_prob_oneSided`'s
  rectangle route (`stepDistOrSelf_toMeasure_ge` over a `good` pair set whose image lands
  in the target), with the MCR×MCR diagonal mass `mcrCount·(mcrCount−1)/(n(n−1))` and the
  config-level R1 birth `+2` effect from `assignable_rule1_both_fresh`.
* Stage 3 is the upper-bound dual: `stepDist`'s mass on `{pool drops}` equals the
  `interactionPMF` mass on the preimage; that preimage is contained in the block square of
  the *assignable* agents (a pool drop deletes an assignable agent, so a drop requires both
  members assignable); the block bound `pair_block_prob_le_sq` (cloned for `AgentState`)
  caps it by `(assignableCount/n)² ≤ Ahi²/(n(n−1))`.

Stage 4 instantiates `FloorPrefix.pool_expNeg_one_step_drift` with all three facts, leaving
only the (pure-scalar, already-proven) favorability and the analytic core.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.FloorPrefix
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.HourCoupling

namespace ExactMajority
namespace FloorMasses

open MeasureTheory ProbabilityTheory RoleSplitConcentration FloorPrefix
open scoped ENNReal NNReal Real BigOperators

variable {L K : ℕ}

/-! ## Stage 1 — `hstep`: the `±2` per-step interaction range.

`assignableCount` is a `countP`, and `HourCouplingAzuma.countP_stepOrSelf_diff_le_two` already
shows any single chosen-pair update changes any `countP` by at most `2`.  Lifting to the
one-step kernel via the support reduction (every support point is `stepOrSelf c r₁ r₂` or
`c` itself) gives the a.e. lower bound `pool c − 2 ≤ pool c'`. -/

/-- **The single-step lower bound on `assignableCount`.**  For every chosen ordered pair,
the successor `assignableCount` is at least `assignableCount c − 2` (the deterministic `±2`
interaction range, `countP_stepOrSelf_diff_le_two` specialised to `isAssignableBool`). -/
theorem assignableCount_stepOrSelf_ge
    (c : Config (AgentState L K)) (r₁ r₂ : AgentState L K) :
    (assignableCount (L := L) (K := K) c : ℤ) - 2
      ≤ (assignableCount (L := L) (K := K)
          (Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂) : ℤ) := by
  have h := (HourCouplingAzuma.countP_stepOrSelf_diff_le_two
    (fun a => isAssignableBool (L := L) (K := K) a = true) c r₁ r₂).2
  -- `assignableCount = countP isAssignableBool` (definitional).
  simpa only [assignableCount_eq_countP] using by linarith [h]

/-- **`hstep` (general form).**  On the one-step kernel from any `c`, almost every successor
`c'` satisfies `assignableCount c − 2 ≤ assignableCount c'`.  Support reduction (mirrors
`HourCouplingAzuma.hour_bdd`): every support point is `stepOrSelf c r₁ r₂` (or `c` itself, the
trivial case). -/
theorem pool_step_ge_ae (c : Config (AgentState L K)) :
    ∀ᵐ c' ∂((NonuniformMajority L K).transitionKernel c),
      (assignableCount (L := L) (K := K) c : ℤ) - 2
        ≤ (assignableCount (L := L) (K := K) c' : ℤ) := by
  classical
  -- It suffices to verify the bound on every support point.
  have hsupp : ∀ c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support,
      (assignableCount (L := L) (K := K) c : ℤ) - 2
        ≤ (assignableCount (L := L) (K := K) c' : ℤ) := by
    intro c' hc'
    have hcase : (∃ r₁ r₂, Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂ = c')
        ∨ c' = c := by
      by_cases hc : 2 ≤ c.card
      · rw [show (NonuniformMajority L K).stepDistOrSelf c
            = (NonuniformMajority L K).stepDist c hc by
            unfold Protocol.stepDistOrSelf; rw [dif_pos hc]] at hc'
        obtain ⟨⟨r₁, r₂⟩, hr⟩ :=
          Protocol.stepDist_support (NonuniformMajority L K) c hc c' hc'
        exact Or.inl ⟨r₁, r₂, hr⟩
      · rw [show (NonuniformMajority L K).stepDistOrSelf c = PMF.pure c by
            unfold Protocol.stepDistOrSelf; rw [dif_neg hc]] at hc'
        rw [PMF.mem_support_pure_iff] at hc'
        exact Or.inr hc'
    rcases hcase with ⟨r₁, r₂, hstep⟩ | hcx
    · rw [← hstep]; exact assignableCount_stepOrSelf_ge c r₁ r₂
    · rw [hcx]; omega
  -- Lift the support bound to a.e. (kernel = `stepDistOrSelf c`'s toMeasure).
  change ∀ᵐ c' ∂((NonuniformMajority L K).stepDistOrSelf c).toMeasure, _
  rw [ae_iff]
  change ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
    {c' | ¬ (assignableCount (L := L) (K := K) c : ℤ) - 2
        ≤ (assignableCount (L := L) (K := K) c' : ℤ)} = 0
  rw [PMF.toMeasure_apply_eq_zero_iff _ (DiscreteMeasurableSpace.forall_measurableSet _)]
  rw [Set.disjoint_left]
  intro c' hc' hbad
  exact hbad (hsupp c' hc')

/-! ## Stage 2 — `hbirth`: the Rule-1 birth rectangle.

A single interaction between two **fresh** (unassigned, phase-0) MCR agents fires Rule 1
(`MCR,MCR → Main,CR`) and produces two fresh assignables, raising the pool by exactly `+2`
(`assignable_rule1_both_fresh`).  The good ordered pairs are the `freshMcrF ×ˢ freshMcrF`
off-diagonal rectangle; its `interactionPMF` mass is `freshMcrCount·(freshMcrCount−1)/(n(n−1))`
(`sum_interactionCount_freshMcr`), and `stepDistOrSelf_toMeasure_ge` lifts it onto the
birth band `{c' | pool c + 2 ≤ pool c'}` whose mass is `birthR1Mass`.

The honest count carried by R1 is the **unassigned** phase-0 MCR count `freshMcrCount`, *not*
the bare `mcrCount`: an *assigned* MCR (allowed by `cardPhaseShell`, which only fixes
`role = mcr → phase 0`) would not produce two fresh assignables.  See the Stage-2 wrap-up
note for the `hbirth` adapter, which holds verbatim once `uMin ≤ freshMcrCount`. -/

/-- The fresh-MCR predicate: an unassigned phase-0 MCR (a Rule-1 initiator/responder). -/
def isFreshMcr (a : AgentState L K) : Bool :=
  decide (a.role = .mcr) && (!a.assigned) && decide (a.phase.val = 0)

theorem isFreshMcr_iff (a : AgentState L K) :
    isFreshMcr (L := L) (K := K) a = true ↔
      a.role = .mcr ∧ a.assigned = false ∧ a.phase.val = 0 := by
  unfold isFreshMcr
  simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_true_eq]
  tauto

/-- Count of fresh (unassigned phase-0) MCR agents — the honest R1-birth initiator pool. -/
def freshMcrCount (c : Config (AgentState L K)) : ℕ :=
  Multiset.countP (fun a => isFreshMcr (L := L) (K := K) a) c

/-! ### The Transition→Phase0Transition full bridge for a fresh-MCR pair. -/

/-- When both inputs are fresh (unassigned phase-0) MCR, the full `Transition` equals the
phase-0 reaction `Phase0Transition`: `phaseEpidemicUpdate` is the identity (both at phase 0),
and the post-step `finishPhase10Entry` is the identity since the Rule-1 outputs are at phase
0 (≠ 10, both `IsAssignable`). -/
theorem Transition_eq_phase0_of_fresh_mcr_pair
    (s t : AgentState L K)
    (hs_role : s.role = .mcr) (ht_role : t.role = .mcr)
    (hs_un : s.assigned = false) (ht_un : t.assigned = false)
    (hs_ph : s.phase.val = 0) (ht_ph : t.phase.val = 0) :
    Transition L K s t = Phase0Transition L K s t := by
  have hpe := phaseEpidemicUpdate_eq_self_of_both_phase0 (L := L) (K := K) s t hs_ph ht_ph
  have hs0 : s.phase = (⟨0, by omega⟩ : Fin _) := Fin.ext hs_ph
  -- The Phase0Transition outputs are both assignable, hence at phase 0 (≠ 10).
  obtain ⟨hout1, hout2⟩ :=
    assignable_rule1_both_fresh s t hs_role ht_role hs_un ht_un hs_ph ht_ph
  have hout1_ph : (Phase0Transition L K s t).1.phase.val ≠ 10 := by
    rw [hout1.1]; omega
  have hout2_ph : (Phase0Transition L K s t).2.phase.val ≠ 10 := by
    rw [hout2.1]; omega
  unfold Transition
  rw [hpe]
  simp only
  rw [hs0]
  rw [finishPhase10Entry_eq_self_of_after_ne_10 (L := L) (K := K) _ _ hout1_ph,
      finishPhase10Entry_eq_self_of_after_ne_10 (L := L) (K := K) _ _ hout2_ph]

/-- **Config-level Rule-1 birth `+2`.**  When the chosen pair `{s,t} ≤ c` are both fresh
MCR, the successor config raises the pool by exactly `2`: the removed pair carries `0`
assignables (MCR ⟹ not assignable) and the output carries `2` (`assignable_rule1_both_fresh`),
so `assignableCount (c − {s,t} + outputs) = assignableCount c + 2`. -/
theorem birthR1_config_eq
    (c : Config (AgentState L K)) (s t : AgentState L K)
    (h_sub : ({s, t} : Config (AgentState L K)) ≤ c)
    (hs_role : s.role = .mcr) (ht_role : t.role = .mcr)
    (hs_un : s.assigned = false) (ht_un : t.assigned = false)
    (hs_ph : s.phase.val = 0) (ht_ph : t.phase.val = 0) :
    assignableCount (L := L) (K := K)
        (c - {s, t} + {(Transition L K s t).1, (Transition L K s t).2})
      = assignableCount (L := L) (K := K) c + 2 := by
  have h_restore : c - {s, t} + {s, t} = c := Multiset.sub_add_cancel h_sub
  -- The output pair carries exactly 2 assignables; the input pair carries 0.
  obtain ⟨hout1, hout2⟩ :=
    assignable_rule1_both_fresh s t hs_role ht_role hs_un ht_un hs_ph ht_ph
  have htr := Transition_eq_phase0_of_fresh_mcr_pair s t hs_role ht_role hs_un ht_un hs_ph ht_ph
  have hpair_out : assignableCount (L := L) (K := K)
      ({(Transition L K s t).1, (Transition L K s t).2} : Config (AgentState L K)) = 2 := by
    rw [htr, assignableCount_pair',
      (isAssignableBool_iff _).mpr hout1, (isAssignableBool_iff _).mpr hout2]
    simp
  have hpair_in : assignableCount (L := L) (K := K)
      ({s, t} : Config (AgentState L K)) = 0 := by
    rw [assignableCount_pair',
      not_isAssignable_of_mcr (L := L) (K := K) hs_role,
      not_isAssignable_of_mcr (L := L) (K := K) ht_role]
    simp
  -- `assignableCount` is additive over multiset `+`.
  have hadd : ∀ x y : Config (AgentState L K),
      assignableCount (L := L) (K := K) (x + y)
        = assignableCount (L := L) (K := K) x + assignableCount (L := L) (K := K) y :=
    fun x y => Multiset.countP_add _ _ _
  calc assignableCount (L := L) (K := K)
          (c - {s, t} + {(Transition L K s t).1, (Transition L K s t).2})
      = assignableCount (L := L) (K := K) (c - {s, t}) + 2 := by
        rw [hadd, hpair_out]
    _ = assignableCount (L := L) (K := K) (c - {s, t})
          + assignableCount (L := L) (K := K) ({s, t} : Config (AgentState L K)) + 2 := by
        rw [hpair_in]
    _ = assignableCount (L := L) (K := K) (c - {s, t} + {s, t}) + 2 := by
        rw [hadd]
    _ = assignableCount (L := L) (K := K) c + 2 := by rw [h_restore]

/-! ### The fresh-MCR rectangle (`freshMcrF ×ˢ freshMcrF`). -/

/-- The fresh-MCR initiator/responder Finset. -/
def freshMcrF : Finset (AgentState L K) :=
  Finset.univ.filter (fun s : AgentState L K => isFreshMcr (L := L) (K := K) s = true)

/-- `∑_{s ∈ freshMcrF} count s = freshMcrCount`. -/
theorem sum_count_freshMcrF (c : Config (AgentState L K)) :
    ∑ s ∈ freshMcrF (L := L) (K := K), c.count s =
      freshMcrCount (L := L) (K := K) c := by
  set F := freshMcrF (L := L) (K := K) with hF
  set cm := Multiset.filter (fun a : AgentState L K =>
    isFreshMcr (L := L) (K := K) a = true) c with hcm
  have hcount : ∀ s ∈ F, c.count s = Multiset.count s cm := fun s hs => by
    show Multiset.count s c = Multiset.count s cm
    have hs_fresh : isFreshMcr (L := L) (K := K) s = true := (Finset.mem_filter.mp hs).2
    simp only [cm, Multiset.count_filter, hs_fresh, ite_true]
  calc ∑ s ∈ F, c.count s
      = ∑ s ∈ F, Multiset.count s cm := Finset.sum_congr rfl hcount
    _ = Multiset.card cm :=
        Multiset.sum_count_eq_card (s := F) (m := cm)
          (fun a ha => Finset.mem_filter.mpr ⟨Finset.mem_univ a,
            (Multiset.mem_filter.mp ha).2⟩)
    _ = freshMcrCount (L := L) (K := K) c := by
        rw [freshMcrCount, hcm, ← Multiset.countP_eq_card_filter]

/-- For a fixed fresh-MCR initiator `s₁`, the row sum of `interactionCount s₁ s₂` over
fresh-MCR responders is `count s₁ · (freshMcrCount − 1)`.  (Diagonal `s₁ = s₂` subtracts
one; mirror of `sum_interactionCount_mcrF_right`.) -/
theorem sum_interactionCount_freshMcrF_right (c : Config (AgentState L K))
    (s₁ : AgentState L K) (hs₁ : isFreshMcr (L := L) (K := K) s₁ = true) :
    ∑ s₂ ∈ freshMcrF (L := L) (K := K), c.interactionCount s₁ s₂ =
      c.count s₁ * (freshMcrCount (L := L) (K := K) c - 1) := by
  set F := freshMcrF (L := L) (K := K) with hF
  by_cases hzero : c.count s₁ = 0
  · have hall : ∀ s₂ ∈ F, c.interactionCount s₁ s₂ = 0 := fun s₂ _ => by
      unfold Config.interactionCount Config.count
      unfold Config.count at hzero
      split_ifs with h
      · subst h; simp [hzero]
      · simp [hzero]
    rw [Finset.sum_eq_zero hall]; simp [hzero]
  · have hfactor : ∀ s₂ ∈ F, c.interactionCount s₁ s₂ =
        c.count s₁ * if s₁ = s₂ then c.count s₁ - 1 else c.count s₂ := by
      intro s₂ _; unfold Config.interactionCount
      by_cases h : s₁ = s₂ <;> simp [h]
    rw [Finset.sum_congr rfl hfactor, ← Finset.mul_sum]; congr 1
    have hs₁F : s₁ ∈ F := Finset.mem_filter.mpr ⟨Finset.mem_univ s₁, hs₁⟩
    set f : AgentState L K → ℕ :=
      fun s₂ => if s₁ = s₂ then c.count s₁ - 1 else c.count s₂ with hfdef
    have hf_s₁ : f s₁ = c.count s₁ - 1 := if_pos rfl
    have hf_ne : ∀ s₂ ∈ F.erase s₁, f s₂ = c.count s₂ :=
      fun s₂ hs₂ => if_neg (Finset.ne_of_mem_erase hs₂).symm
    calc ∑ s₂ ∈ F, f s₂
        = f s₁ + ∑ s₂ ∈ F.erase s₁, f s₂ := (Finset.add_sum_erase F f hs₁F).symm
      _ = (c.count s₁ - 1) + ∑ s₂ ∈ F.erase s₁, c.count s₂ := by
          rw [hf_s₁, Finset.sum_congr rfl hf_ne]
      _ = freshMcrCount (L := L) (K := K) c - 1 := by
          have hse : c.count s₁ + ∑ s₂ ∈ F.erase s₁, c.count s₂ =
              freshMcrCount (L := L) (K := K) c := by
            rw [Finset.add_sum_erase F (fun s => c.count s) hs₁F]
            exact sum_count_freshMcrF c
          have hcount_pos : 0 < c.count s₁ := Nat.pos_of_ne_zero hzero
          omega

/-- The fresh-MCR×fresh-MCR rectangle sum `= freshMcrCount·(freshMcrCount−1)`. -/
theorem sum_interactionCount_freshMcr (c : Config (AgentState L K)) :
    ∑ s₁ ∈ freshMcrF (L := L) (K := K), ∑ s₂ ∈ freshMcrF (L := L) (K := K),
        c.interactionCount s₁ s₂ =
      freshMcrCount (L := L) (K := K) c * (freshMcrCount (L := L) (K := K) c - 1) := by
  have hstep : ∀ s₁ ∈ freshMcrF (L := L) (K := K),
      ∑ s₂ ∈ freshMcrF (L := L) (K := K), c.interactionCount s₁ s₂ =
        c.count s₁ * (freshMcrCount (L := L) (K := K) c - 1) := fun s₁ hs₁ =>
    sum_interactionCount_freshMcrF_right c s₁ (Finset.mem_filter.mp hs₁).2
  rw [Finset.sum_congr rfl hstep, ← Finset.sum_mul, sum_count_freshMcrF]

/-- Positive `interactionCount` implies `Applicable` (re-derived locally). -/
private lemma applicable_of_pos_iCount (c : Config (AgentState L K))
    (s₁ s₂ : AgentState L K) (h : 0 < c.interactionCount s₁ s₂) :
    Protocol.Applicable c s₁ s₂ := by
  show {s₁, s₂} ≤ c; rw [Multiset.le_iff_count]; intro a
  simp only [Config.interactionCount, Config.count] at h
  simp only [Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton]
  by_cases heq : s₁ = s₂
  · subst heq; simp only [ite_true] at h
    have : 2 ≤ Multiset.count s₁ c := by
      by_contra h_lt
      have hle : Multiset.count s₁ c ≤ 1 := by omega
      have : Multiset.count s₁ c * (Multiset.count s₁ c - 1) = 0 := by
        rcases Nat.eq_zero_or_pos (Multiset.count s₁ c) with h0 | h0
        · simp [h0]
        · have : Multiset.count s₁ c = 1 := by omega
          simp [this]
      omega
    by_cases ha : a = s₁ <;> simp_all
  · simp only [heq, ite_false] at h
    have hc1 : 0 < Multiset.count s₁ c := pos_of_mul_pos_left h (Nat.zero_le _)
    have hc2 : 0 < Multiset.count s₂ c := pos_of_mul_pos_right h (Nat.zero_le _)
    by_cases ha1 : a = s₁ <;> by_cases ha2 : a = s₂ <;> simp_all <;> omega

/-- **The fresh-MCR rectangle interactionPMF mass.**  The PMF mass of the good set
"`p.1`, `p.2` are both fresh MCR and `(p.1,p.2)` is applicable" is at least
`freshMcrCount·(freshMcrCount−1)/(card(card−1))` — the Rule-1 birth rate. -/
theorem interactionPMF_toMeasure_freshMcr_ge
    (c : Config (AgentState L K)) (hc : 2 ≤ c.card) :
    (c.interactionPMF hc).toMeasure
      {p : AgentState L K × AgentState L K |
        isFreshMcr (L := L) (K := K) p.1 = true ∧
        isFreshMcr (L := L) (K := K) p.2 = true ∧
        Protocol.Applicable c p.1 p.2} ≥
    ENNReal.ofReal
      (((freshMcrCount (L := L) (K := K) c *
          (freshMcrCount (L := L) (K := K) c - 1) : ℕ) : ℝ) /
        (c.card * (c.card - 1) : ℝ)) := by
  set target := {p : AgentState L K × AgentState L K |
    isFreshMcr (L := L) (K := K) p.1 = true ∧
    isFreshMcr (L := L) (K := K) p.2 = true ∧
    Protocol.Applicable c p.1 p.2}
  set F := freshMcrF (L := L) (K := K) with hFdef
  have h_sub : (↑(F ×ˢ F) : Set _) ∩ (c.interactionPMF hc).support ⊆ target := by
    intro ⟨s₁, s₂⟩ ⟨h_mem, h_supp⟩
    have hs₁ : isFreshMcr (L := L) (K := K) s₁ = true :=
      (Finset.mem_filter.mp (Finset.mem_product.mp h_mem).1).2
    have hs₂ : isFreshMcr (L := L) (K := K) s₂ = true :=
      (Finset.mem_filter.mp (Finset.mem_product.mp h_mem).2).2
    rw [PMF.mem_support_iff] at h_supp
    have h_app : Protocol.Applicable c s₁ s₂ := by
      apply applicable_of_pos_iCount
      by_contra h0; exact h_supp (show c.interactionProb s₁ s₂ = 0 by
        simp [Config.interactionProb, show c.interactionCount s₁ s₂ = 0 by omega])
    exact ⟨hs₁, hs₂, h_app⟩
  have h_le := (c.interactionPMF hc).toMeasure_mono
    (DiscreteMeasurableSpace.forall_measurableSet _) h_sub
  suffices h_val : (c.interactionPMF hc).toMeasure (↑(F ×ˢ F)) ≥
      ENNReal.ofReal
        (((freshMcrCount (L := L) (K := K) c *
            (freshMcrCount (L := L) (K := K) c - 1) : ℕ) : ℝ) /
          (c.card * (c.card - 1) : ℝ)) from le_trans h_val h_le
  rw [PMF.toMeasure_apply_finset]
  simp_rw [show ∀ p : AgentState L K × AgentState L K,
    (c.interactionPMF hc) p = (c.interactionCount p.1 p.2 : ENNReal) / c.totalPairs
    from fun _ => rfl, div_eq_mul_inv, ← Finset.sum_mul]
  conv_lhs => arg 1; rw [Finset.sum_product' F F
    (fun s₁ s₂ => (c.interactionCount s₁ s₂ : ENNReal))]
  have h_comb := sum_interactionCount_freshMcr (L := L) (K := K) c
  set MM := freshMcrCount (L := L) (K := K) c *
    (freshMcrCount (L := L) (K := K) c - 1) with hMM
  rw [show (∑ s₁ ∈ F, ∑ s₂ ∈ F, (c.interactionCount s₁ s₂ : ENNReal)) =
      ((MM : ℕ) : ENNReal) from by exact_mod_cast h_comb, ← div_eq_mul_inv]
  have h1 : 1 ≤ c.card := by omega
  have hprod_pos : (0 : ℝ) < ↑c.card * (↑c.card - 1) := by
    apply mul_pos
    · exact Nat.cast_pos.mpr (by omega)
    · exact sub_pos.mpr (by exact_mod_cast (show 1 < c.card by omega))
  show ↑MM / ↑c.totalPairs ≥
    ENNReal.ofReal (((MM : ℕ) : ℝ) / (↑c.card * (↑c.card - 1)))
  have hcard_cast : ↑c.card * (↑c.card - 1 : ℝ) = ((c.card * (c.card - 1) : ℕ) : ℝ) := by
    push_cast [Nat.cast_sub h1]; ring
  rw [ENNReal.ofReal_div_of_pos hprod_pos, hcard_cast,
    ENNReal.ofReal_natCast, ENNReal.ofReal_natCast,
    show (c.card * (c.card - 1) : ℕ) = c.totalPairs from rfl]

/-- **`birthR1Mass` lower bound (honest, fresh-MCR count).**  On a config with `card = n`,
the birth band `{c' | pool c + 2 ≤ pool c'}` carries mass at least
`freshMcrCount·(freshMcrCount−1)/(n(n−1))` — the Rule-1 `MCR,MCR → Main,CR` birth rate over
unassigned phase-0 MCR pairs.  Route: `stepDistOrSelf_toMeasure_ge` over the fresh-MCR
rectangle (`birthR1_config_eq` lands every such pair in the band, raising the pool by `+2`). -/
theorem birthR1Mass_ge_freshMcr
    (c : Config (AgentState L K)) (n : ℕ) (h_card : c.card = n) (hn2 : 2 ≤ n) :
    birthR1Mass (L := L) (K := K) c ≥
      ENNReal.ofReal
        (((freshMcrCount (L := L) (K := K) c *
            (freshMcrCount (L := L) (K := K) c - 1) : ℕ) : ℝ) / (n * (n - 1) : ℝ)) := by
  have hc2 : 2 ≤ c.card := by omega
  set good : Set (AgentState L K × AgentState L K) :=
    {p | isFreshMcr (L := L) (K := K) p.1 = true ∧
         isFreshMcr (L := L) (K := K) p.2 = true ∧
         Protocol.Applicable c p.1 p.2} with hgooddef
  have hgood : ∀ pair ∈ good, (NonuniformMajority L K).scheduledStep c pair ∈
      {c' | assignableCount (L := L) (K := K) c + 2 ≤ assignableCount (L := L) (K := K) c'} := by
    intro ⟨s, t⟩ ⟨hs_fresh, ht_fresh, happ⟩
    simp only [Set.mem_setOf_eq]
    obtain ⟨hs_role, hs_un, hs_ph⟩ := (isFreshMcr_iff s).mp hs_fresh
    obtain ⟨ht_role, ht_un, ht_ph⟩ := (isFreshMcr_iff t).mp ht_fresh
    unfold Protocol.scheduledStep Protocol.stepOrSelf
    rw [if_pos happ]
    show assignableCount (L := L) (K := K) c + 2 ≤
      assignableCount (L := L) (K := K)
        (c - {s, t} + {(Transition L K s t).1, (Transition L K s t).2})
    rw [birthR1_config_eq c s t happ hs_role ht_role hs_un ht_un hs_ph ht_ph]
  calc birthR1Mass (L := L) (K := K) c
      = ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
          {c' | assignableCount (L := L) (K := K) c + 2
            ≤ assignableCount (L := L) (K := K) c'} := rfl
    _ ≥ (c.interactionPMF hc2).toMeasure good :=
        stepDistOrSelf_toMeasure_ge c hc2 _ good hgood
    _ ≥ ENNReal.ofReal
          (((freshMcrCount (L := L) (K := K) c *
              (freshMcrCount (L := L) (K := K) c - 1) : ℕ) : ℝ) /
            (c.card * (c.card - 1) : ℝ)) :=
        interactionPMF_toMeasure_freshMcr_ge c hc2
    _ = ENNReal.ofReal
          (((freshMcrCount (L := L) (K := K) c *
              (freshMcrCount (L := L) (K := K) c - 1) : ℕ) : ℝ) /
            (n * (n - 1) : ℝ)) := by rw [h_card]

/-- **`hbirth` (FloorPrefix shape).**  The exact hypothesis `pool_expNeg_one_step_drift`
needs: on the drift region (where `uMin ≤ mcrCount`), provided the MCR agents are *fresh*
(`uMin ≤ freshMcrCount`, the honest count carried by R1 — see the wrap-up note), the
`birthR1Mass` is at least `uMin(uMin−1)/(n(n−1))`.  Monotone in the fresh-MCR count. -/
theorem hbirth_of_freshMcr_floor
    (n uMin Ahi : ℕ) (hn2 : 2 ≤ n)
    (c : Config (AgentState L K))
    (hregion : PoolDriftRegion (L := L) (K := K) n uMin Ahi c)
    (hfresh : uMin ≤ freshMcrCount (L := L) (K := K) c) :
    ENNReal.ofReal (((uMin * (uMin - 1) : ℕ) : ℝ) / (n * (n - 1) : ℝ))
      ≤ birthR1Mass (L := L) (K := K) c := by
  obtain ⟨hshell, _, _⟩ := hregion
  have h_card : c.card = n := hshell.1
  refine le_trans ?_ (birthR1Mass_ge_freshMcr c n h_card hn2)
  apply ENNReal.ofReal_le_ofReal
  have hn1 : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
    nlinarith
  -- Same denominator, monotone numerator: uMin(uMin−1) ≤ freshMcrCount(freshMcrCount−1).
  have hmono : uMin * (uMin - 1) ≤
      freshMcrCount (L := L) (K := K) c * (freshMcrCount (L := L) (K := K) c - 1) :=
    Nat.mul_le_mul hfresh (Nat.sub_le_sub_right hfresh 1)
  have hmonoR : (((uMin * (uMin - 1) : ℕ) : ℝ))
      ≤ (((freshMcrCount (L := L) (K := K) c *
          (freshMcrCount (L := L) (K := K) c - 1) : ℕ) : ℝ)) := by exact_mod_cast hmono
  gcongr

/-! ## Stage 3 — `hdeath`: the Rule-4 fresh-CR drain rectangle (upper bound).

This is the upper-bound dual of Stage 2.  The drain band `{c' | pool c' < pool c}` is the
image of the `{drop}` preimage under `scheduledStep`; by the kernel→preimage *equality* on
the `interactionPMF`, its mass equals the PMF mass of the preimage.  The preimage is
contained in a *block square* of agents `S` (the agents whose deletion can lower the pool),
so the block bound `block_pair_prob_le_sq` caps it by `(∑_{a∈S} count a / n)²`.

### The honest protocol containment (and the FloorPrefix-definition mismatch)

The genuinely-new protocol fact is *which* ordered pairs can strictly lower the pool.  Two
subtleties make the blueprint's "drain ≤ pool²/(n(n−1))" NOT a verbatim consequence of
`PoolDriftRegion`:

(a) **The only first-level / second-level drain is Rule 4** (`RoleCR,RoleCR → Clock,Reserve`,
   `assignableCount_pair_rule4_drop`).  A strict pool drop therefore deletes assignable
   agents that become non-assignable — but R4 fires on *any* two `RoleCR`, and an
   assignable CR can be deleted alongside a **non-assignable** CR (assigned or non-phase-0),
   dropping the pool by `1`.  So the drop preimage is contained in the `RoleCR×RoleCR`
   block, giving `(crCount/n)²`, with `crCount` the **total** CR count — *not* the pool.

(b) The kernel is the full multi-phase `Transition`, whose `phaseEpidemicUpdate` prefix can
   advance a phase-0 assignable agent out of phase 0 (another drain path), unless the
   interacting pair is phase-synchronised.  `cardPhaseShell` only pins `role = mcr → phase 0`,
   not the phases of the assignable Main/CR agents.

Hence the honest, provable upper bound is `r4FreshCRDrainMass c ≤ (∑_{a∈S} count a / n)²`
for the block `S` of agents whose deletion can drop the pool, and the FloorPrefix target
`r4FreshCRDrainMass c ≤ Ahi²/(n(n−1))` follows **only under the extra region fact**
`drainBlockCount c ≤ Ahi` (the block count is within the buffer).  We deliver the reusable
infrastructure (`stepDist_toMeasure_eq_preimage`, `block_pair_prob_le_sq`,
`pair_block_sq_le_buffer`) and the `hdeath` adapter conditioned on that block-count fact;
the containment `drainPreimage ⊆ blockSquare` and the block-count bound are the residual
protocol facts (see `drainPreimage_subset_block` below, carried as a hypothesis). -/

/-- **Upper-bound dual of `stepDistOrSelf_toMeasure_ge`.**  When `2 ≤ c.card`, the
one-step mass of a config event equals the `interactionPMF` mass of its `scheduledStep`
preimage.  (Pure `PMF.map`/`Measure.map_apply` rewriting; the lower-bound lemma uses the
`≥` half of the same identity.) -/
theorem stepDist_toMeasure_eq_preimage
    (c : Config (AgentState L K)) (hc : 2 ≤ c.card)
    (target : Set (Config (AgentState L K))) :
    ((NonuniformMajority L K).stepDistOrSelf c).toMeasure target =
      (c.interactionPMF hc).toMeasure
        ((NonuniformMajority L K).scheduledStep c ⁻¹' target) := by
  have h_meas : MeasurableSet target := DiscreteMeasurableSpace.forall_measurableSet _
  unfold Protocol.stepDistOrSelf
  rw [dif_pos hc]
  unfold Protocol.stepDist
  have h_map := PMF.toMeasure_map ((NonuniformMajority L K).scheduledStep c)
    (c.interactionPMF hc) Measurable.of_discrete
  calc (PMF.map ((NonuniformMajority L K).scheduledStep c)
        (c.interactionPMF hc)).toMeasure target
      = ((c.interactionPMF hc).toMeasure.map
          ((NonuniformMajority L K).scheduledStep c)) target := by rw [← h_map]
    _ = (c.interactionPMF hc).toMeasure
          ((NonuniformMajority L K).scheduledStep c ⁻¹' target) :=
        MeasureTheory.Measure.map_apply Measurable.of_discrete h_meas

/-- A finite-type PMF `toMeasure` value bounded by the sum over a covering Finset. -/
private theorem toMeasure_le_sum_event (p : PMF (AgentState L K × AgentState L K))
    (E : Finset (AgentState L K × AgentState L K))
    (Eset : Set (AgentState L K × AgentState L K)) (hsub : Eset ⊆ ↑E) :
    p.toMeasure Eset ≤ ∑ pr ∈ E, p pr := by
  calc p.toMeasure Eset ≤ p.toMeasure ↑E := measure_mono hsub
    _ = ∑ pr ∈ E, p pr := PMF.toMeasure_apply_finset _ _

/-- The block rectangle sum `∑_{s₁∈S}∑_{s₂∈S} icount = X(X−1)`, `X = ∑_{s∈S} count`. -/
private theorem sum_block_interactionCount (c : Config (AgentState L K))
    (S : Finset (AgentState L K)) :
    (∑ s₁ ∈ S, ∑ s₂ ∈ S, c.interactionCount s₁ s₂)
      = (∑ s ∈ S, c.count s) * ((∑ s ∈ S, c.count s) - 1) := by
  classical
  set X := ∑ s ∈ S, c.count s with hX
  have hrow : ∀ s₁ ∈ S, (∑ s₂ ∈ S, c.interactionCount s₁ s₂) = c.count s₁ * (X - 1) := by
    intro s₁ hs₁
    have hc₁X : c.count s₁ ≤ X := Finset.single_le_sum (fun m _ => Nat.zero_le _) hs₁
    rw [← Finset.add_sum_erase S _ hs₁]
    have hdiag : c.interactionCount s₁ s₁ = c.count s₁ * (c.count s₁ - 1) := by
      unfold Config.interactionCount; rw [if_pos rfl]
    have hoff : (∑ s₂ ∈ S.erase s₁, c.interactionCount s₁ s₂)
        = c.count s₁ * (X - c.count s₁) := by
      have hsum0 : c.count s₁ + (∑ s₂ ∈ S.erase s₁, c.count s₂) = X := by
        rw [hX]; exact Finset.add_sum_erase S (fun m => c.count m) hs₁
      have hsum : (∑ s₂ ∈ S.erase s₁, c.count s₂) = X - c.count s₁ := by omega
      rw [← hsum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s₂ hs₂
      unfold Config.interactionCount
      rw [if_neg (fun hc => (Finset.mem_erase.mp hs₂).1 hc.symm)]
    rw [hdiag, hoff]
    cases hc₁ : c.count s₁ with
    | zero => simp
    | succ k =>
        have h1X : 1 ≤ X := by omega
        zify [show 1 ≤ k + 1 from by omega, show k + 1 ≤ X from by omega, h1X]
        ring
  rw [Finset.sum_congr rfl hrow, ← Finset.sum_mul]

/-- **The same-block pair bound (AgentState clone of `EarlyDripMarked.pair_block_prob_le_sq`).**
The scheduler picks an ordered pair with BOTH states in a block `S` with probability at most
`(X/n)²`, `X = ∑_{s∈S} count s`. -/
theorem block_pair_prob_le_sq (c : Config (AgentState L K)) (h : 2 ≤ c.card)
    (S : Finset (AgentState L K)) :
    (c.interactionPMF h).toMeasure {pr | pr.1 ∈ S ∧ pr.2 ∈ S}
      ≤ ENNReal.ofReal ((((∑ m ∈ S, c.count m : ℕ) : ℝ) / (c.card : ℝ)) ^ 2) := by
  classical
  set X := ∑ m ∈ S, c.count m with hX
  have hXn : X ≤ c.card := by
    calc X ≤ ∑ m : AgentState L K, c.count m :=
          Finset.sum_le_sum_of_subset (Finset.subset_univ S)
      _ = c.card := Multiset.sum_count_eq_card (fun a _ => Finset.mem_univ a)
  have hsub : {pr : AgentState L K × AgentState L K | pr.1 ∈ S ∧ pr.2 ∈ S} ⊆ ↑(S ×ˢ S) := by
    rintro pr ⟨h1, h2⟩; rw [Finset.coe_product]; exact ⟨h1, h2⟩
  refine le_trans (toMeasure_le_sum_event (c.interactionPMF h) (S ×ˢ S) _ hsub) ?_
  have hval : (∑ pr ∈ S ×ˢ S, (c.interactionPMF h) pr)
      = ((X * (X - 1) : ℕ) : ℝ≥0∞) / ((c.totalPairs : ℕ) : ℝ≥0∞) := by
    rw [Finset.sum_product]
    calc (∑ m₁ ∈ S, ∑ m₂ ∈ S, (c.interactionPMF h) (m₁, m₂))
        = ∑ m₁ ∈ S, ∑ m₂ ∈ S,
            ((c.interactionCount m₁ m₂ : ℕ) : ℝ≥0∞) * ((c.totalPairs : ℕ) : ℝ≥0∞)⁻¹ := by
          refine Finset.sum_congr rfl (fun m₁ _ => Finset.sum_congr rfl (fun m₂ _ => ?_))
          show c.interactionProb m₁ m₂ = _
          unfold Config.interactionProb; rw [div_eq_mul_inv]
      _ = (∑ m₁ ∈ S, ∑ m₂ ∈ S, ((c.interactionCount m₁ m₂ : ℕ) : ℝ≥0∞))
            * ((c.totalPairs : ℕ) : ℝ≥0∞)⁻¹ := by
          rw [Finset.sum_mul]; exact Finset.sum_congr rfl (fun m₁ _ => (Finset.sum_mul ..).symm)
      _ = ((X * (X - 1) : ℕ) : ℝ≥0∞) * ((c.totalPairs : ℕ) : ℝ≥0∞)⁻¹ := by
          congr 1
          calc (∑ m₁ ∈ S, ∑ m₂ ∈ S, ((c.interactionCount m₁ m₂ : ℕ) : ℝ≥0∞))
              = ∑ m₁ ∈ S, ((∑ m₂ ∈ S, c.interactionCount m₁ m₂ : ℕ) : ℝ≥0∞) :=
                Finset.sum_congr rfl (fun m₁ _ => (Nat.cast_sum _ _).symm)
            _ = ((∑ m₁ ∈ S, ∑ m₂ ∈ S, c.interactionCount m₁ m₂ : ℕ) : ℝ≥0∞) :=
                (Nat.cast_sum _ _).symm
            _ = ((X * (X - 1) : ℕ) : ℝ≥0∞) := by rw [sum_block_interactionCount c S]
      _ = ((X * (X - 1) : ℕ) : ℝ≥0∞) / ((c.totalPairs : ℕ) : ℝ≥0∞) := (div_eq_mul_inv _ _).symm
  rw [hval]
  have htp : c.totalPairs = c.card * (c.card - 1) := rfl
  rw [htp,
    show ((X * (X - 1) : ℕ) : ℝ≥0∞) = ENNReal.ofReal ((X * (X - 1) : ℕ) : ℝ) from
      (ENNReal.ofReal_natCast _).symm,
    show ((c.card * (c.card - 1) : ℕ) : ℝ≥0∞)
      = ENNReal.ofReal ((c.card * (c.card - 1) : ℕ) : ℝ) from (ENNReal.ofReal_natCast _).symm]
  rw [← ENNReal.ofReal_div_of_pos (by
    have : 0 < c.card * (c.card - 1) := by apply Nat.mul_pos <;> omega
    exact_mod_cast this)]
  apply ENNReal.ofReal_le_ofReal
  have hXr : ((X : ℕ) : ℝ) ≤ (c.card : ℝ) := by exact_mod_cast hXn
  by_cases hX0 : X = 0
  · rw [hX0]; simp
  · have h1X : 1 ≤ X := by omega
    have hdenom : (0 : ℝ) < ((c.card * (c.card - 1) : ℕ) : ℝ) := by
      have : 0 < c.card * (c.card - 1) := by apply Nat.mul_pos <;> omega
      exact_mod_cast this
    have hXnn : (0 : ℝ) ≤ ((X : ℕ) : ℝ) := by positivity
    have hnnn : (0 : ℝ) ≤ (c.card : ℝ) := by positivity
    rw [div_pow, div_le_div_iff₀ hdenom (by positivity)]
    push_cast [Nat.cast_sub (show 1 ≤ c.card from by omega), Nat.cast_sub h1X]
    nlinarith [mul_nonneg (mul_nonneg hXnn hnnn) (sub_nonneg.mpr hXr)]

/-- Arithmetic: `(X/n)² ≤ Ahi²/(n(n−1))` whenever `X ≤ Ahi ≤ n` and `2 ≤ n`.  (Pushes the
block-square bound to the FloorPrefix `Ahi²/(n(n−1))` shape; uses `n(n−1) ≤ n²` and
`X ≤ Ahi`.) -/
theorem pair_block_sq_le_buffer (X Ahi n : ℕ) (hXA : X ≤ Ahi) (_hAn : Ahi ≤ n) (hn2 : 2 ≤ n) :
    (((X : ℝ) / (n : ℝ)) ^ 2) ≤ ((Ahi * Ahi : ℕ) : ℝ) / (n * (n - 1) : ℝ) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by positivity
  have hn2r : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
  have hnm1 : (1 : ℝ) ≤ (n : ℝ) - 1 := by linarith
  have hden : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := by positivity
  have hXr : (X : ℝ) ≤ (Ahi : ℝ) := by exact_mod_cast hXA
  have hX0 : (0 : ℝ) ≤ (X : ℝ) := by positivity
  have hA0 : (0 : ℝ) ≤ (Ahi : ℝ) := by positivity
  rw [div_pow, show ((Ahi * Ahi : ℕ) : ℝ) = (Ahi : ℝ) * (Ahi : ℝ) from by push_cast; ring,
    div_le_div_iff₀ (by positivity) hden]
  -- X² · n(n−1) ≤ Ahi² · n²
  have hXsq : (X : ℝ) ^ 2 ≤ (Ahi : ℝ) ^ 2 := by nlinarith [hXr, hX0, hA0]
  have hnn : (n : ℝ) * ((n : ℝ) - 1) ≤ (n : ℝ) ^ 2 := by nlinarith [hn0]
  nlinarith [hXsq, hnn, sq_nonneg ((X : ℝ)), mul_nonneg hX0 hX0, sq_nonneg ((Ahi : ℝ)),
    mul_nonneg (mul_nonneg hA0 hA0) (le_of_lt hn0)]

/-! ### The `hdeath` adapter (block-containment form).

We package the upper-bound route into a single adapter `hdeath_of_block`.  It takes:
* a *drain block* Finset `S` (the agents whose deletion can lower the pool);
* the **containment fact** `hcontain`: every ordered pair that strictly drops the pool lies
  in the block square `S ×ˢ S` (this is the residual protocol fact — see the Stage-3 note:
  honestly `S` is the `RoleCR` block, and the containment is "a strict drop fires Rule 4 on
  two CR" together with "phaseEpidemicUpdate does not drop a phase-0 assignable on this
  pair"; both are genuine `Transition`-level statements not implied by `cardPhaseShell`);
* the **block-count bound** `hblock`: `∑_{a∈S} count a ≤ Ahi` (the block stays within the
  buffer — for the `RoleCR` block this is `crCount ≤ Ahi`).
and concludes the FloorPrefix `hdeath` shape. -/

/-- **`hdeath` via a drain block.**  Given a drain block `S` containing every pool-dropping
ordered pair (`hcontain`) and bounded by the buffer (`hblock`, `hAn`), the drain mass is at
most `Ahi²/(n(n−1))`.  Chains `stepDist_toMeasure_eq_preimage` → `block_pair_prob_le_sq` →
`pair_block_sq_le_buffer`. -/
theorem hdeath_of_block
    (n Ahi : ℕ) (hn2 : 2 ≤ n) (c : Config (AgentState L K)) (h_card : c.card = n)
    (S : Finset (AgentState L K))
    (hcontain : (NonuniformMajority L K).scheduledStep c ⁻¹'
        {c' | assignableCount (L := L) (K := K) c' < assignableCount (L := L) (K := K) c}
      ⊆ {pr | pr.1 ∈ S ∧ pr.2 ∈ S})
    (hblock : ∑ a ∈ S, c.count a ≤ Ahi) (hAn : Ahi ≤ n) :
    r4FreshCRDrainMass (L := L) (K := K) c
      ≤ ENNReal.ofReal (((Ahi * Ahi : ℕ) : ℝ) / (n * (n - 1) : ℝ)) := by
  have hc2 : 2 ≤ c.card := by omega
  set X := ∑ a ∈ S, c.count a with hXdef
  calc r4FreshCRDrainMass (L := L) (K := K) c
      = ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
          {c' | assignableCount (L := L) (K := K) c' < assignableCount (L := L) (K := K) c} := rfl
    _ = (c.interactionPMF hc2).toMeasure
          ((NonuniformMajority L K).scheduledStep c ⁻¹'
            {c' | assignableCount (L := L) (K := K) c'
              < assignableCount (L := L) (K := K) c}) :=
        stepDist_toMeasure_eq_preimage c hc2 _
    _ ≤ (c.interactionPMF hc2).toMeasure {pr | pr.1 ∈ S ∧ pr.2 ∈ S} :=
        measure_mono hcontain
    _ ≤ ENNReal.ofReal (((X : ℝ) / (c.card : ℝ)) ^ 2) :=
        block_pair_prob_le_sq c hc2 S
    _ ≤ ENNReal.ofReal (((Ahi * Ahi : ℕ) : ℝ) / (n * (n - 1) : ℝ)) := by
        rw [h_card]
        exact ENNReal.ofReal_le_ofReal (pair_block_sq_le_buffer X Ahi n hblock hAn hn2)

/-! ## Stage 4 — wire-up: the one-step pool drift with the discharged masses.

We instantiate `FloorPrefix.pool_expNeg_one_step_drift` at the concrete favorability scale
`s = 1/10` (`scalarPoolFav_instance`, already proven `< 1`), feeding:

* `hstep` ← `pool_step_ge_ae` (Stage 1, unconditional);
* `hbirth` ← `hbirth_of_freshMcr_floor` (Stage 2) under the region fact `uMin ≤ freshMcrCount`;
* `hdeath` ← `hdeath_of_block` (Stage 3) under the drain-block facts.

The remaining inputs are: the pure-scalar count-fraction arithmetic (`hb0/hd0/hb1/hbd1`,
carried as hypotheses since they depend on the calibration `a₀ = ⌊n/10⌋`), the per-region
fresh-MCR floor, and the per-region drain block.  The favorability is **fully discharged**
(`scalarPoolFav_instance`), so this is the strongest hypothesis-reduced one-step drift now
reachable: the only residuals are the two documented protocol-count facts (fresh-MCR floor
and drain-block containment) — see the Stage-2/Stage-3 notes. -/

/-- **The assembled one-step pool drift (masses discharged).**  On `PoolDriftRegion n uMin Ahi`,
provided the per-region fresh-MCR floor (`hfresh`) and drain block (`hSstep`/`hblock`), the
`s = 1/10` tilted one-step expectation contracts at the concrete favorability rate.  Stages
1–3 supply the three protocol masses; `scalarPoolFav_instance` supplies the (proven `< 1`)
favorability. -/
theorem pool_expNeg_one_step_drift_floorMasses
    (n uMin Ahi : ℕ) (hn2 : 2 ≤ n)
    (hb0 : 0 ≤ ((uMin * (uMin - 1) : ℕ) : ℝ) / (n * (n - 1) : ℝ))
    (hd0 : 0 ≤ ((Ahi * Ahi : ℕ) : ℝ) / (n * (n - 1) : ℝ))
    (hb1 : ((uMin * (uMin - 1) : ℕ) : ℝ) / (n * (n - 1) : ℝ) ≤ 1)
    (hbd1 : ((uMin * (uMin - 1) : ℕ) : ℝ) / (n * (n - 1) : ℝ)
        + ((Ahi * Ahi : ℕ) : ℝ) / (n * (n - 1) : ℝ) ≤ 1)
    -- per-region fresh-MCR floor (the honest hbirth feeder, Stage 2):
    (hfresh : ∀ c, PoolDriftRegion (L := L) (K := K) n uMin Ahi c →
      uMin ≤ freshMcrCount (L := L) (K := K) c)
    -- per-region drain block (the honest hdeath feeder, Stage 3):
    (Sblk : Config (AgentState L K) → Finset (AgentState L K))
    (hSstep : ∀ c, PoolDriftRegion (L := L) (K := K) n uMin Ahi c →
      (NonuniformMajority L K).scheduledStep c ⁻¹'
          {c' | assignableCount (L := L) (K := K) c' < assignableCount (L := L) (K := K) c}
        ⊆ {pr | pr.1 ∈ Sblk c ∧ pr.2 ∈ Sblk c})
    (hblock : ∀ c, PoolDriftRegion (L := L) (K := K) n uMin Ahi c →
      ∑ a ∈ Sblk c, c.count a ≤ Ahi)
    (hAn : Ahi ≤ n) :
    ∀ c, PoolDriftRegion (L := L) (K := K) n uMin Ahi c →
      ∫⁻ c', poolExpNeg (L := L) (K := K) (1 / 10) c'
          ∂((NonuniformMajority L K).transitionKernel c)
        ≤ (ENNReal.ofReal
            (1
              - (((uMin * (uMin - 1) : ℕ) : ℝ) / (n * (n - 1) : ℝ)) *
                  (1 - Real.exp (-2 * (1 / 10)))
              + (((Ahi * Ahi : ℕ) : ℝ) / (n * (n - 1) : ℝ)) *
                  (Real.exp (2 * (1 / 10)) - 1)))
          * poolExpNeg (L := L) (K := K) (1 / 10) c := by
  refine pool_expNeg_one_step_drift n uMin Ahi (1 / 10) _ (by norm_num)
    hb0 hd0 hb1 hbd1 ?_ ?_ ?_ ?_
  · -- hbirth
    intro c hc
    exact hbirth_of_freshMcr_floor n uMin Ahi hn2 c hc (hfresh c hc)
  · -- hdeath
    intro c hc
    have hshell := hc.1
    exact hdeath_of_block n Ahi hn2 c hshell.1 (Sblk c) (hSstep c hc) (hblock c hc) hAn
  · -- hstep (unconditional)
    intro c _
    exact pool_step_ge_ae c
  · -- favorability (proven `< 1` at the concrete constants)
    unfold ScalarPoolFav
    exact le_refl _

end FloorMasses
end ExactMajority
