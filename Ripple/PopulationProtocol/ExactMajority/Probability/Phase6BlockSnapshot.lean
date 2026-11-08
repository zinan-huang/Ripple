/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Phase-6 endpoint majority-block snapshot

The paper's Lemma 7.3 starts Phase 7 with at least `0.87 |M|` majority
Mains in the fixed levels `l,l+1,l+2`.  The `0.87` does not follow from
`Phase6Convergence.highMass = 0`: that postcondition only confines biased
Mains below `l`.  The actual accounting starts from the Theorem-6.2
`0.92 |M|` majority block and charges every Phase-6 block loss to a
previously sampled Reserve whose sample lies strictly below the protected
three-level block.

This file formalizes that deterministic charge.  The remaining probabilistic
input is exposed explicitly as the endpoint-independent bound saying that at
most `0.05 |M|` such dangerous sampled Reserves exist at Phase-6 entry.
-/

import Ripple.PopulationProtocol.ExactMajority.Probability.PaperRegime
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase5To6FuelProducer
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase7MajorityBlockLedger

namespace Ripple.PopulationProtocol.ExactMajority
namespace Phase6BlockSnapshot

open Phase7BandDefs
open Phase7MajorityBlockLedger
open scoped BigOperators

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

/-- A Reserve capable of pushing a protected-block Main below `l+2`.

The Lean sample index is stored in `hour`; the Phase-6 split guard is
`r.hour > j`.  Thus a split whose target is already at `l+2` can leave the
block only when `l+2 < r.hour`. -/
def dangerousReserveUnit (l : ℕ) (a : AgentState L K) : ℕ :=
  if a.role = Role.reserve ∧ l + 2 < a.hour.val then 1 else 0

/-- Number of not-yet-consumed dangerous sampled Reserves. -/
def dangerousReserveCount (l : ℕ)
    (c : Config (AgentState L K)) : ℕ :=
  Multiset.countP
    (fun a => a.role = Role.reserve ∧ l + 2 < a.hour.val) c

@[simp] theorem dangerousReserveUnit_of_role_ne_reserve
    (l : ℕ) (a : AgentState L K) (h : a.role ≠ Role.reserve) :
    dangerousReserveUnit (L := L) (K := K) l a = 0 := by
  simp [dangerousReserveUnit, h]

@[simp] theorem dangerousReserveUnit_of_role_reserve
    (l : ℕ) (a : AgentState L K) (h : a.role = Role.reserve) :
    dangerousReserveUnit (L := L) (K := K) l a =
      if l + 2 < a.hour.val then 1 else 0 := by
  simp [dangerousReserveUnit, h]

@[simp] theorem dangerousReserveCount_add (l : ℕ)
    (a b : Config (AgentState L K)) :
    dangerousReserveCount (L := L) (K := K) l (a + b) =
      dangerousReserveCount (L := L) (K := K) l a +
        dangerousReserveCount (L := L) (K := K) l b := by
  simp [dangerousReserveCount, Multiset.countP_add]

@[simp] theorem dangerousReserveCount_pair (l : ℕ)
    (a b : AgentState L K) :
    dangerousReserveCount (L := L) (K := K) l
        ({a, b} : Config (AgentState L K)) =
      dangerousReserveUnit (L := L) (K := K) l a +
        dangerousReserveUnit (L := L) (K := K) l b := by
  change Multiset.countP
      (fun x => x.role = Role.reserve ∧ l + 2 < x.hour.val)
        (a ::ₘ b ::ₘ 0) = _
  rw [Multiset.countP_cons, Multiset.countP_cons, Multiset.countP_zero]
  simp [dangerousReserveUnit, add_comm]

/-! ## Minority debt as a signed-Main class profile -/

/-- The Phase-7 debt is a finite weighted sum of exact signed Main classes.
This presentation is the deterministic interface used to transport the
Phase-3 minority-mass estimate through the static Phase-4/5 window. -/
def minorityDebtByClass (sigma : Sign) (l : ℕ)
    (c : Config (AgentState L K)) : ℕ :=
  ∑ i : Fin (L + 1),
    if i.val ≤ l + 4 then
      2 ^ (l + 4 - i.val) *
        Phase5Convergence.biasedMainClassU
          (L := L) (K := K) sigma i c
    else 0

private theorem minorityDebtUnit_eq_sum_classIndicators
    (sigma : Sign) (l : ℕ) (a : AgentState L K) :
    minorityDebtUnit (L := L) (K := K) sigma l a =
      ∑ i : Fin (L + 1),
        if i.val ≤ l + 4 then
          2 ^ (l + 4 - i.val) *
            (if Phase5Convergence.biasedMainClass
                (L := L) (K := K) sigma i a then 1 else 0)
        else 0 := by
  by_cases hm : a.role = Role.main
  · cases hb : a.bias with
    | zero =>
        simp [minorityDebtUnit, hm, hb,
          Phase5Convergence.biasedMainClass]
    | dyadic s j =>
        by_cases hs : s = sigma
        · subst s
          by_cases hj : j.val ≤ l + 4
          · simp [minorityDebtUnit, hm, hb, hj,
              Phase5Convergence.biasedMainClass]
            rw [Finset.sum_eq_single j]
            · simp [hj]
            · intro b _ hbj
              have hne : j ≠ b := fun hjb => hbj hjb.symm
              simp [hne]
            · simp
          · simp [minorityDebtUnit, hm, hb, hj,
              Phase5Convergence.biasedMainClass]
            symm
            apply Finset.sum_eq_zero
            intro i _
            by_cases hi : i.val ≤ l + 4
            · rw [if_pos hi, if_neg]
              intro hji
              subst i
              exact hj hi
            · rw [if_neg hi]
        · simp [minorityDebtUnit, hm, hb, hs,
            Phase5Convergence.biasedMainClass]
  · simp [minorityDebtUnit, hm, Phase5Convergence.biasedMainClass]

/-- Configuration-level identity between the operational debt definition and
the exact signed-class profile. -/
theorem minorityDebt_eq_minorityDebtByClass
    (sigma : Sign) (l : ℕ) (c : Config (AgentState L K)) :
    minorityDebt (L := L) (K := K) sigma l c =
      minorityDebtByClass (L := L) (K := K) sigma l c := by
  induction c using Multiset.induction_on with
  | empty =>
      simp [minorityDebt, minorityDebtByClass,
        Phase5Convergence.biasedMainClassU]
  | @cons a c ih =>
      have hcons :
          minorityDebt (L := L) (K := K) sigma l (a ::ₘ c) =
            minorityDebtUnit (L := L) (K := K) sigma l a +
              minorityDebt (L := L) (K := K) sigma l c := by
        simp [minorityDebt]
      rw [hcons, ih, minorityDebtUnit_eq_sum_classIndicators]
      unfold minorityDebtByClass
      simp only [Phase5Convergence.biasedMainClassU, Multiset.countP_cons]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i.val ≤ l + 4
      · simp [hi, Nat.mul_add, add_comm]
      · simp [hi]

/-- Phase-4/5 reachability transports the whole weighted minority-debt
profile, not merely one exponent class. -/
theorem minorityDebt_eq_of_reachableThroughPhase45
    (sigma : Sign) (l : ℕ)
    (c d : Config (AgentState L K))
    (hreach : Phase5To6FuelProducer.ReachableThroughPhase45
      (L := L) (K := K) c d) :
    minorityDebt (L := L) (K := K) sigma l d =
      minorityDebt (L := L) (K := K) sigma l c := by
  rw [minorityDebt_eq_minorityDebtByClass,
    minorityDebt_eq_minorityDebtByClass]
  unfold minorityDebtByClass
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i.val ≤ l + 4
  · simp only [if_pos hi]
    rw [Phase5To6FuelProducer.biasedMainClassU_eq_of_reachableThroughPhase45
      (L := L) (K := K) sigma i c d hreach]
  · simp [hi]

private theorem debtWeight_cast_eq_scaled_zpow
    (l j : ℕ) (hj : j ≤ l + 4) :
    ((2 ^ (l + 4 - j) : ℕ) : ℝ) =
      (2 : ℝ) ^ (l + 4) * (2 : ℝ) ^ (-(j : ℤ)) := by
  push_cast
  rw [pow_sub₀ (2 : ℝ) (by norm_num) hj]
  simp [zpow_neg, zpow_natCast]

/-- One agent's normalized debt is at most its matching signed dyadic mass,
scaled by `2^(l+4)`.  The inequality is strict only because signed mass also
counts non-Main agents and Main indices above the debt cutoff. -/
private theorem minorityDebtUnit_cast_le_scaled_agentSignMass
    (sigma : Sign) (l : ℕ) (a : AgentState L K) :
    (minorityDebtUnit (L := L) (K := K) sigma l a : ℝ) ≤
      (2 : ℝ) ^ (l + 4) *
        match sigma with
        | .pos => (P3DeterministicAlgebra.agentPosMassQ
            (L := L) (K := K) a : ℝ)
        | .neg => (P3DeterministicAlgebra.agentNegMassQ
            (L := L) (K := K) a : ℝ) := by
  cases sigma with
  | neg =>
      change (minorityDebtUnit (L := L) (K := K) .neg l a : ℝ) ≤
        (2 : ℝ) ^ (l + 4) *
          (P3DeterministicAlgebra.agentNegMassQ
            (L := L) (K := K) a : ℝ)
      cases hb : a.bias with
      | zero =>
          simp [minorityDebtUnit, hb,
            P3DeterministicAlgebra.agentNegMassQ,
            P3DeterministicAlgebra.biasNegMassQ]
      | dyadic s j =>
          cases s with
          | pos =>
              simp [minorityDebtUnit, hb,
                P3DeterministicAlgebra.agentNegMassQ,
                P3DeterministicAlgebra.biasNegMassQ]
          | neg =>
              by_cases hm : a.role = Role.main
              · by_cases hj : j.val ≤ l + 4
                · have hw := debtWeight_cast_eq_scaled_zpow l j.val hj
                  simpa [minorityDebtUnit, hm, hb, hj,
                    P3DeterministicAlgebra.agentNegMassQ,
                    P3DeterministicAlgebra.biasNegMassQ,
                    Phase5To6FuelProducer.cast_weightQ_eq_zpow] using
                      hw.le
                · simp [minorityDebtUnit, hm, hb, hj,
                    P3DeterministicAlgebra.agentNegMassQ,
                    P3DeterministicAlgebra.biasNegMassQ,
                    Phase5To6FuelProducer.cast_weightQ_eq_zpow]
              · simp [minorityDebtUnit, hm, hb,
                  P3DeterministicAlgebra.agentNegMassQ,
                  P3DeterministicAlgebra.biasNegMassQ,
                  Phase5To6FuelProducer.cast_weightQ_eq_zpow]
  | pos =>
      change (minorityDebtUnit (L := L) (K := K) .pos l a : ℝ) ≤
        (2 : ℝ) ^ (l + 4) *
          (P3DeterministicAlgebra.agentPosMassQ
            (L := L) (K := K) a : ℝ)
      cases hb : a.bias with
      | zero =>
          simp [minorityDebtUnit, hb,
            P3DeterministicAlgebra.agentPosMassQ,
            P3DeterministicAlgebra.biasPosMassQ]
      | dyadic s j =>
          cases s with
          | neg =>
              simp [minorityDebtUnit, hb,
                P3DeterministicAlgebra.agentPosMassQ,
                P3DeterministicAlgebra.biasPosMassQ]
          | pos =>
              by_cases hm : a.role = Role.main
              · by_cases hj : j.val ≤ l + 4
                · have hw := debtWeight_cast_eq_scaled_zpow l j.val hj
                  simpa [minorityDebtUnit, hm, hb, hj,
                    P3DeterministicAlgebra.agentPosMassQ,
                    P3DeterministicAlgebra.biasPosMassQ,
                    Phase5To6FuelProducer.cast_weightQ_eq_zpow] using
                      hw.le
                · simp [minorityDebtUnit, hm, hb, hj,
                    P3DeterministicAlgebra.agentPosMassQ,
                    P3DeterministicAlgebra.biasPosMassQ,
                    Phase5To6FuelProducer.cast_weightQ_eq_zpow]
              · simp [minorityDebtUnit, hm, hb,
                  P3DeterministicAlgebra.agentPosMassQ,
                  P3DeterministicAlgebra.biasPosMassQ,
                  Phase5To6FuelProducer.cast_weightQ_eq_zpow]

/-- Summing the pointwise bound shows that normalized debt is at most the
matching signed mass times `2^(l+4)`. -/
theorem minorityDebt_cast_le_scaled_signedMass
    (sigma : Sign) (l : ℕ) (c : Config (AgentState L K)) :
    (minorityDebt (L := L) (K := K) sigma l c : ℝ) ≤
      (2 : ℝ) ^ (l + 4) *
        match sigma with
        | .pos => Phase3Post3.betaPlus (L := L) (K := K) c
        | .neg => Phase3Post3.betaMinus (L := L) (K := K) c := by
  cases sigma with
  | neg =>
      induction c using Multiset.induction_on with
      | empty =>
          simp [minorityDebt, Phase3Post3.betaMinus,
            P3DeterministicAlgebra.betaMinusQ, Config.sumOf]
      | @cons a c ih =>
          have ha := minorityDebtUnit_cast_le_scaled_agentSignMass
            (L := L) (K := K) .neg l a
          simp only [minorityDebt, Multiset.map_cons, Multiset.sum_cons,
            Nat.cast_add, Phase3Post3.betaMinus,
            P3DeterministicAlgebra.betaMinusQ, Config.sumOf,
            Rat.cast_add] at ih ⊢
          rw [mul_add]
          linarith
  | pos =>
      induction c using Multiset.induction_on with
      | empty =>
          simp [minorityDebt, Phase3Post3.betaPlus,
            P3DeterministicAlgebra.betaPlusQ, Config.sumOf]
      | @cons a c ih =>
          have ha := minorityDebtUnit_cast_le_scaled_agentSignMass
            (L := L) (K := K) .pos l a
          simp only [minorityDebt, Multiset.map_cons, Multiset.sum_cons,
            Nat.cast_add, Phase3Post3.betaPlus,
            P3DeterministicAlgebra.betaPlusQ, Config.sumOf,
            Rat.cast_add] at ih ⊢
          rw [mul_add]
          linarith

/-- Majority-orientation form: Phase-7 debt uses the sign opposite to the
Phase-3 snapshot's majority sign. -/
theorem minorityDebt_cast_le_scaled_minorityMass
    (sigmaMajority : Sign) (l : ℕ)
    (c : Config (AgentState L K)) :
    (minorityDebt (L := L) (K := K)
        (Phase3Post3.minoritySignOfMajority sigmaMajority) l c : ℝ) ≤
      (2 : ℝ) ^ (l + 4) *
        Phase3Post3.minorityMass
          (L := L) (K := K) sigmaMajority c := by
  cases sigmaMajority with
  | neg =>
      simpa [Phase3Post3.minoritySignOfMajority,
        Phase3Post3.minorityMass] using
        (minorityDebt_cast_le_scaled_signedMass
          (L := L) (K := K) .pos l c)
  | pos =>
      simpa [Phase3Post3.minoritySignOfMajority,
        Phase3Post3.minorityMass] using
        (minorityDebt_cast_le_scaled_signedMass
          (L := L) (K := K) .neg l c)

private theorem pow_l_add_four_mul_zpow_neg_l (l : ℕ) :
    (2 : ℝ) ^ (l + 4) * (2 : ℝ) ^ (-(l : ℤ)) = 16 := by
  rw [← zpow_natCast]
  rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  norm_num

/-- The sharp Phase-3 minority-mass estimate gives exactly the paper's
`0.064 M` normalized debt cap after any real Phase-3/4 route. -/
theorem minorityDebt_64_of_minorityMass_bound_after_phase34
    (l M : ℕ) (sigmaMajority : Sign)
    {c3 c4 : Config (AgentState L K)}
    (hminor :
      Phase3Post3.minorityMass (L := L) (K := K) sigmaMajority c3 ≤
        (1 / 250 : ℝ) * (M : ℝ) * (2 : ℝ) ^ (-(l : ℤ)))
    (h34 : Phase5To6FuelProducer.ReachableThroughPhase34
      (L := L) (K := K) c3 c4) :
    1000 * minorityDebt (L := L) (K := K)
        (Phase3Post3.minoritySignOfMajority sigmaMajority) l c4 ≤
      64 * M := by
  have hdebt := minorityDebt_cast_le_scaled_minorityMass
    (L := L) (K := K) sigmaMajority l c4
  have hmass := Phase5To6FuelProducer.minorityMass_le_of_reachableThroughPhase34
    (L := L) (K := K) sigmaMajority c3 c4 h34
  have hscale : (0 : ℝ) ≤ (2 : ℝ) ^ (l + 4) := by positivity
  have hreal :
      (minorityDebt (L := L) (K := K)
          (Phase3Post3.minoritySignOfMajority sigmaMajority) l c4 : ℝ) ≤
        (64 / 1000 : ℝ) * (M : ℝ) := by
    calc
      (minorityDebt (L := L) (K := K)
          (Phase3Post3.minoritySignOfMajority sigmaMajority) l c4 : ℝ)
          ≤ (2 : ℝ) ^ (l + 4) *
              Phase3Post3.minorityMass
                (L := L) (K := K) sigmaMajority c4 := hdebt
      _ ≤ (2 : ℝ) ^ (l + 4) *
              ((1 / 250 : ℝ) * (M : ℝ) *
                (2 : ℝ) ^ (-(l : ℤ))) :=
          mul_le_mul_of_nonneg_left (hmass.trans hminor) hscale
      _ = (1 / 250 : ℝ) * (M : ℝ) *
              ((2 : ℝ) ^ (l + 4) * (2 : ℝ) ^ (-(l : ℤ))) := by ring
      _ = (64 / 1000 : ℝ) * (M : ℝ) := by
          rw [pow_l_add_four_mul_zpow_neg_l]
          ring
  have hscaled :
      (1000 : ℝ) *
          (minorityDebt (L := L) (K := K)
            (Phase3Post3.minoritySignOfMajority sigmaMajority) l c4 : ℝ) ≤
        (64 : ℝ) * (M : ℝ) := by
    nlinarith
  exact_mod_cast hscaled

/-! ## One-split charge -/

/-- A Reserve-fuelled split can reduce the fixed majority block only by
consuming a dangerous Reserve.  In subtraction-free form, the block count
plus the *output* dangerous-reserve count is bounded by the output block plus
the *input* dangerous-reserve count. -/
theorem doSplit_block_danger_pair
    (sigma : Sign) (l : ℕ) (r m : AgentState L K)
    (hrR : r.role = Role.reserve) (hmM : m.role = Role.main) :
    majorityBlockUnit (L := L) (K := K) sigma l r +
          majorityBlockUnit (L := L) (K := K) sigma l m +
        (dangerousReserveUnit (L := L) (K := K) l (doSplit L K r m).1 +
          dangerousReserveUnit (L := L) (K := K) l (doSplit L K r m).2) ≤
      majorityBlockUnit (L := L) (K := K) sigma l (doSplit L K r m).1 +
          majorityBlockUnit (L := L) (K := K) sigma l (doSplit L K r m).2 +
        (dangerousReserveUnit (L := L) (K := K) l r +
          dangerousReserveUnit (L := L) (K := K) l m) := by
  classical
  by_cases happ : Phase6Convergence.DoSplitApplicable (L := L) (K := K) r m
  · obtain ⟨sgn, j, hb, hne, hgt, hlt⟩ := happ
    rw [Phase6Convergence.doSplit_apply
      (L := L) (K := K) r m hb hne hgt hlt]
    rcases sigma with _ | _ <;> rcases sgn with _ | _
    all_goals
      simp [majorityBlockUnit, majorityBand3, dangerousReserveUnit,
        hrR, hmM, hb] <;>
      split_ifs <;> simp_all <;> omega
  · rw [Phase6Convergence.doSplit_eq_self_of_not_applicable
      (L := L) (K := K) r m happ]

/-! ## Phase-6 preservation of the future Phase-7 minority debt -/

/-- The normalized Phase-7 debt weight of one minority Main at index `j`.
This local arithmetic presentation is definitionally the nonzero branch of
`minorityDebtUnit`. -/
private def debtWeight6 (l j : ℕ) : ℕ :=
  if j ≤ l + 4 then 2 ^ (l + 4 - j) else 0

/-- Splitting one dyadic Main into two children at the next index does not
increase normalized minority debt.  It conserves debt below the cutoff and
drops debt when the split crosses the cutoff. -/
private theorem debtWeight6_split_le (l j : ℕ) :
    debtWeight6 l (j + 1) + debtWeight6 l (j + 1) ≤
      debtWeight6 l j := by
  by_cases hj : j ≤ l + 4
  · by_cases hsucc : j + 1 ≤ l + 4
    · have hexp : l + 4 - j = (l + 4 - (j + 1)) + 1 := by omega
      rw [debtWeight6, if_pos hsucc, debtWeight6, if_pos hj, hexp, pow_succ]
      omega
    · rw [debtWeight6, if_neg hsucc, debtWeight6, if_pos hj]
      exact Nat.zero_le _
  · have hsucc : ¬ j + 1 ≤ l + 4 := by omega
    rw [debtWeight6, if_neg hsucc, debtWeight6, if_neg hj]

/-- `doSplit` cannot create future Phase-7 minority debt.  On the minority
sign it is the dyadic identity `w(j) = 2 w(j+1)`; on the majority sign every
debt summand is zero. -/
theorem doSplit_minorityDebt_pair_le
    (sigma : Sign) (l : ℕ) (r m : AgentState L K)
    (hrR : r.role = Role.reserve) (hmM : m.role = Role.main) :
    minorityDebtUnit (L := L) (K := K) sigma l (doSplit L K r m).1 +
        minorityDebtUnit (L := L) (K := K) sigma l (doSplit L K r m).2 ≤
      minorityDebtUnit (L := L) (K := K) sigma l r +
        minorityDebtUnit (L := L) (K := K) sigma l m := by
  classical
  by_cases happ : Phase6Convergence.DoSplitApplicable (L := L) (K := K) r m
  · obtain ⟨sgn, j, hb, hne, hgt, hlt⟩ := happ
    rw [Phase6Convergence.doSplit_apply
      (L := L) (K := K) r m hb hne hgt hlt]
    rcases sigma with _ | _ <;> rcases sgn with _ | _
    all_goals
      simp [minorityDebtUnit, hrR, hmM, hb]
    all_goals
      simpa [debtWeight6] using debtWeight6_split_le l j.val
  · rw [Phase6Convergence.doSplit_eq_self_of_not_applicable
      (L := L) (K := K) r m happ]

/-! ## Full Phase-6 pair -/

private theorem clockBranch_blockUnit_eq
    (sigma : Sign) (l : ℕ) (a : AgentState L K)
    (ha : 5 ≤ a.phase.val) :
    majorityBlockUnit (L := L) (K := K) sigma l
        (if a.role = Role.clock then stdCounterSubroutine L K a else a) =
      majorityBlockUnit (L := L) (K := K) sigma l a := by
  by_cases hc : a.role = Role.clock
  · rw [if_pos hc]
    have hout : (stdCounterSubroutine L K a).role ≠ Role.main := by
      rw [Phase6Convergence.stdCounterSubroutine_role_ge_five6
        (L := L) (K := K) a ha, hc]
      decide
    have hin : a.role ≠ Role.main := by rw [hc]; decide
    rw [majorityBlockUnit_of_role_ne_main sigma l _ hout,
      majorityBlockUnit_of_role_ne_main sigma l a hin]
  · rw [if_neg hc]

private theorem clockBranch_dangerousReserveUnit_eq
    (l : ℕ) (a : AgentState L K) (ha : 5 ≤ a.phase.val) :
    dangerousReserveUnit (L := L) (K := K) l
        (if a.role = Role.clock then stdCounterSubroutine L K a else a) =
      dangerousReserveUnit (L := L) (K := K) l a := by
  by_cases hc : a.role = Role.clock
  · rw [if_pos hc]
    have hout : (stdCounterSubroutine L K a).role ≠ Role.reserve := by
      rw [Phase6Convergence.stdCounterSubroutine_role_ge_five6
        (L := L) (K := K) a ha, hc]
      decide
    have hin : a.role ≠ Role.reserve := by rw [hc]; decide
    rw [dangerousReserveUnit_of_role_ne_reserve l _ hout,
      dangerousReserveUnit_of_role_ne_reserve l a hin]
  · rw [if_neg hc]

private theorem clockBranch_minorityDebtUnit_eq
    (sigma : Sign) (l : ℕ) (a : AgentState L K)
    (ha : 5 ≤ a.phase.val) :
    minorityDebtUnit (L := L) (K := K) sigma l
        (if a.role = Role.clock then stdCounterSubroutine L K a else a) =
      minorityDebtUnit (L := L) (K := K) sigma l a := by
  by_cases hc : a.role = Role.clock
  · rw [if_pos hc]
    have hout : (stdCounterSubroutine L K a).role ≠ Role.main := by
      rw [Phase6Convergence.stdCounterSubroutine_role_ge_five6
        (L := L) (K := K) a ha, hc]
      decide
    have hin : a.role ≠ Role.main := by rw [hc]; decide
    rw [minorityDebtUnit_of_role_ne_main sigma l _ hout,
      minorityDebtUnit_of_role_ne_main sigma l a hin]
  · rw [if_neg hc]

/-- The actual `Phase6Transition` pair obeys the same charge inequality.  The
trailing clock-counter update preserves both observables. -/
theorem Phase6Transition_block_danger_pair
    (sigma : Sign) (l : ℕ) (s t : AgentState L K)
    (hs6 : 6 ≤ s.phase.val) (ht6 : 6 ≤ t.phase.val) :
    majorityBlockUnit (L := L) (K := K) sigma l s +
          majorityBlockUnit (L := L) (K := K) sigma l t +
        (dangerousReserveUnit (L := L) (K := K) l (Phase6Transition L K s t).1 +
          dangerousReserveUnit (L := L) (K := K) l (Phase6Transition L K s t).2) ≤
      majorityBlockUnit (L := L) (K := K) sigma l (Phase6Transition L K s t).1 +
          majorityBlockUnit (L := L) (K := K) sigma l (Phase6Transition L K s t).2 +
        (dangerousReserveUnit (L := L) (K := K) l s +
          dangerousReserveUnit (L := L) (K := K) l t) := by
  unfold Phase6Transition
  simp only
  set s1 :=
    (if s.role = Role.reserve ∧ t.role = Role.main ∧ t.bias ≠ Bias.zero then
      (doSplit L K s t).1
    else if t.role = Role.reserve ∧ s.role = Role.main ∧ s.bias ≠ Bias.zero then
      (doSplit L K t s).2
    else s) with hs1def
  set t1 :=
    (if s.role = Role.reserve ∧ t.role = Role.main ∧ t.bias ≠ Bias.zero then
      (doSplit L K s t).2
    else if t.role = Role.reserve ∧ s.role = Role.main ∧ s.bias ≠ Bias.zero then
      (doSplit L K t s).1
    else t) with ht1def
  have hpre :
      majorityBlockUnit (L := L) (K := K) sigma l s +
            majorityBlockUnit (L := L) (K := K) sigma l t +
          (dangerousReserveUnit (L := L) (K := K) l s1 +
            dangerousReserveUnit (L := L) (K := K) l t1) ≤
        majorityBlockUnit (L := L) (K := K) sigma l s1 +
            majorityBlockUnit (L := L) (K := K) sigma l t1 +
          (dangerousReserveUnit (L := L) (K := K) l s +
            dangerousReserveUnit (L := L) (K := K) l t) := by
    rw [hs1def, ht1def]
    split_ifs with h1 h2
    · exact doSplit_block_danger_pair sigma l s t h1.1 h1.2.1
    · have h := doSplit_block_danger_pair sigma l t s h2.1 h2.2.1
      omega
    · exact le_rfl
  have hs1p : 6 ≤ s1.phase.val := by
    rw [hs1def]
    split_ifs with h1 h2
    · rw [Phase6Convergence.doSplit_phase_fst_eq
        (L := L) (K := K) s t]
      exact hs6
    · rw [Phase6Convergence.doSplit_phase_snd_eq
        (L := L) (K := K) t s]
      exact hs6
    · exact hs6
  have ht1p : 6 ≤ t1.phase.val := by
    rw [ht1def]
    split_ifs with h1 h2
    · rw [Phase6Convergence.doSplit_phase_snd_eq
        (L := L) (K := K) s t]
      exact ht6
    · rw [Phase6Convergence.doSplit_phase_fst_eq
        (L := L) (K := K) t s]
      exact ht6
    · exact ht6
  rw [clockBranch_blockUnit_eq sigma l s1 (by omega),
    clockBranch_blockUnit_eq sigma l t1 (by omega),
    clockBranch_dangerousReserveUnit_eq l s1 (by omega),
    clockBranch_dangerousReserveUnit_eq l t1 (by omega)]
  exact hpre

/-- Phase-6's full work transition cannot increase the future Phase-7
minority debt. -/
theorem Phase6Transition_minorityDebt_pair_le
    (sigma : Sign) (l : ℕ) (s t : AgentState L K)
    (hs6 : 6 ≤ s.phase.val) (ht6 : 6 ≤ t.phase.val) :
    minorityDebtUnit (L := L) (K := K) sigma l (Phase6Transition L K s t).1 +
        minorityDebtUnit (L := L) (K := K) sigma l (Phase6Transition L K s t).2 ≤
      minorityDebtUnit (L := L) (K := K) sigma l s +
        minorityDebtUnit (L := L) (K := K) sigma l t := by
  unfold Phase6Transition
  simp only
  set s1 :=
    (if s.role = Role.reserve ∧ t.role = Role.main ∧ t.bias ≠ Bias.zero then
      (doSplit L K s t).1
    else if t.role = Role.reserve ∧ s.role = Role.main ∧ s.bias ≠ Bias.zero then
      (doSplit L K t s).2
    else s) with hs1def
  set t1 :=
    (if s.role = Role.reserve ∧ t.role = Role.main ∧ t.bias ≠ Bias.zero then
      (doSplit L K s t).2
    else if t.role = Role.reserve ∧ s.role = Role.main ∧ s.bias ≠ Bias.zero then
      (doSplit L K t s).1
    else t) with ht1def
  have hpre :
      minorityDebtUnit (L := L) (K := K) sigma l s1 +
          minorityDebtUnit (L := L) (K := K) sigma l t1 ≤
        minorityDebtUnit (L := L) (K := K) sigma l s +
          minorityDebtUnit (L := L) (K := K) sigma l t := by
    rw [hs1def, ht1def]
    split_ifs with h1 h2
    · exact doSplit_minorityDebt_pair_le sigma l s t h1.1 h1.2.1
    · have h := doSplit_minorityDebt_pair_le sigma l t s h2.1 h2.2.1
      omega
    · exact le_rfl
  have hs1p : 6 ≤ s1.phase.val := by
    rw [hs1def]
    split_ifs with h1 h2
    · rw [Phase6Convergence.doSplit_phase_fst_eq
        (L := L) (K := K) s t]
      exact hs6
    · rw [Phase6Convergence.doSplit_phase_snd_eq
        (L := L) (K := K) t s]
      exact hs6
    · exact hs6
  have ht1p : 6 ≤ t1.phase.val := by
    rw [ht1def]
    split_ifs with h1 h2
    · rw [Phase6Convergence.doSplit_phase_snd_eq
        (L := L) (K := K) s t]
      exact ht6
    · rw [Phase6Convergence.doSplit_phase_fst_eq
        (L := L) (K := K) t s]
      exact ht6
    · exact ht6
  rw [clockBranch_minorityDebtUnit_eq sigma l s1 (by omega),
    clockBranch_minorityDebtUnit_eq sigma l t1 (by omega)]
  exact hpre

/-- On an exact Phase-6 pair, the full protocol dispatches to
`Phase6Transition`, so the charge inequality is a statement about the frozen
protocol rather than an auxiliary transition. -/
theorem Transition_block_danger_pair
    (sigma : Sign) (l : ℕ) (s t : AgentState L K)
    (hs6 : s.phase.val = 6) (ht6 : t.phase.val = 6) :
    majorityBlockUnit (L := L) (K := K) sigma l s +
          majorityBlockUnit (L := L) (K := K) sigma l t +
        (dangerousReserveUnit (L := L) (K := K) l (Transition L K s t).1 +
          dangerousReserveUnit (L := L) (K := K) l (Transition L K s t).2) ≤
      majorityBlockUnit (L := L) (K := K) sigma l (Transition L K s t).1 +
          majorityBlockUnit (L := L) (K := K) sigma l (Transition L K s t).2 +
        (dangerousReserveUnit (L := L) (K := K) l s +
          dangerousReserveUnit (L := L) (K := K) l t) := by
  rw [Phase6Convergence.Transition_eq_Phase6Transition_of_phase6
    (L := L) (K := K) s t hs6 ht6]
  exact Phase6Transition_block_danger_pair sigma l s t (by omega) (by omega)

/-- The exact Phase-6 full-protocol dispatch cannot increase the future
Phase-7 minority debt. -/
theorem Transition_minorityDebt_pair_le_of_phase6
    (sigma : Sign) (l : ℕ) (s t : AgentState L K)
    (hs6 : s.phase.val = 6) (ht6 : t.phase.val = 6) :
    minorityDebtUnit (L := L) (K := K) sigma l (Transition L K s t).1 +
        minorityDebtUnit (L := L) (K := K) sigma l (Transition L K s t).2 ≤
      minorityDebtUnit (L := L) (K := K) sigma l s +
        minorityDebtUnit (L := L) (K := K) sigma l t := by
  rw [Phase6Convergence.Transition_eq_Phase6Transition_of_phase6
    (L := L) (K := K) s t hs6 ht6]
  exact Phase6Transition_minorityDebt_pair_le sigma l s t (by omega) (by omega)

/-! ## Mixed Phase-6/7 seam accounting -/

private theorem mem_majorityBand3_iff_of_role_bias_eq
    (sigma : Sign) (l : ℕ) (a b : AgentState L K)
    (hrole : a.role = b.role) (hbias : a.bias = b.bias) :
    a ∈ majorityBand3 (L := L) (K := K) sigma l ↔
      b ∈ majorityBand3 (L := L) (K := K) sigma l := by
  simp only [majorityBand3, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hmain, sgn, j, hne, hb, hlo, hhi⟩
    exact
      ⟨by rw [← hrole]; exact hmain,
       sgn, j, hne, by rw [← hbias]; exact hb, hlo, hhi⟩
  · rintro ⟨hmain, sgn, j, hne, hb, hlo, hhi⟩
    exact
      ⟨by rw [hrole]; exact hmain,
       sgn, j, hne, by rw [hbias]; exact hb, hlo, hhi⟩

private theorem majorityBlockUnit_eq_of_role_bias_eq
    (sigma : Sign) (l : ℕ) (a b : AgentState L K)
    (hrole : a.role = b.role) (hbias : a.bias = b.bias) :
    majorityBlockUnit (L := L) (K := K) sigma l a =
      majorityBlockUnit (L := L) (K := K) sigma l b := by
  have hiff := mem_majorityBand3_iff_of_role_bias_eq sigma l a b hrole hbias
  unfold majorityBlockUnit
  by_cases ha : a ∈ majorityBand3 (L := L) (K := K) sigma l
  · have hb : b ∈ majorityBand3 (L := L) (K := K) sigma l := hiff.mp ha
    simp [ha, hb]
  · have hb : b ∉ majorityBand3 (L := L) (K := K) sigma l := by
      exact fun h => ha (hiff.mpr h)
    simp [ha, hb]

private theorem minorityDebtUnit_eq_of_role_bias_eq
    (sigma : Sign) (l : ℕ) (a b : AgentState L K)
    (hrole : a.role = b.role) (hbias : a.bias = b.bias) :
    minorityDebtUnit (L := L) (K := K) sigma l a =
      minorityDebtUnit (L := L) (K := K) sigma l b := by
  simp [minorityDebtUnit, hrole, hbias]

private theorem dangerousReserveUnit_eq_of_role_hour_eq
    (l : ℕ) (a b : AgentState L K)
    (hrole : a.role = b.role) (hhour : a.hour = b.hour) :
    dangerousReserveUnit (L := L) (K := K) l a =
      dangerousReserveUnit (L := L) (K := K) l b := by
  simp [dangerousReserveUnit, hrole, hhour]

/-- Exact evaluation of the only init fold used by the mixed 6→7 epidemic.
No global well-formedness premise is needed: `phaseInit 7` cannot enter the
error phase and only resets a Clock counter. -/
private theorem runInitsBetween_six_seven_phase
    (a : AgentState L K) (ha : a.phase.val = 7) :
    (runInitsBetween L K 6 7 a).phase.val = 7 := by
  unfold runInitsBetween
  have hlist :
      (List.range 11).filter (fun k => 6 < k ∧ k ≤ 7) = [7] := by decide
  rw [hlist]
  by_cases hc : a.role = Role.clock <;> simp [phaseInit, hc, ha]

private theorem phaseEpidemicUpdate_phases_seven_of_six_seven
    (s t : AgentState L K) (hs : s.phase.val = 6) (ht : t.phase.val = 7) :
    (phaseEpidemicUpdate L K s t).1.phase.val = 7 ∧
      (phaseEpidemicUpdate L K s t).2.phase.val = 7 := by
  unfold phaseEpidemicUpdate
  set p := max s.phase t.phase with hp
  have hpmax : p.val = max s.phase.val t.phase.val := by rw [hp]; rfl
  have hpval : p.val = 7 := by rw [hpmax, hs, ht]; decide
  have hs' :
      (runInitsBetween L K s.phase.val p.val
        ({s with phase := p} : AgentState L K)).phase.val = 7 := by
    rw [hs, hpval]
    exact runInitsBetween_six_seven_phase _ (by simp [hpval])
  have ht' :
      (runInitsBetween L K t.phase.val p.val
        ({t with phase := p} : AgentState L K)).phase.val = 7 := by
    rw [ht, hpval, runInitsBetween_self]
    simp [hpval]
  have herr :
      ¬ ((s.phase.val < 10 ∨ t.phase.val < 10) ∧
        ((runInitsBetween L K s.phase.val p.val
            ({s with phase := p} : AgentState L K)).phase.val = 10 ∨
         (runInitsBetween L K t.phase.val p.val
            ({t with phase := p} : AgentState L K)).phase.val = 10)) := by
    intro h
    rcases h.2 with h | h <;> omega
  simp only [herr, if_false]
  exact ⟨hs', ht'⟩

private theorem phaseEpidemicUpdate_phases_seven_of_seven_six
    (s t : AgentState L K) (hs : s.phase.val = 7) (ht : t.phase.val = 6) :
    (phaseEpidemicUpdate L K s t).1.phase.val = 7 ∧
      (phaseEpidemicUpdate L K s t).2.phase.val = 7 := by
  unfold phaseEpidemicUpdate
  set p := max s.phase t.phase with hp
  have hpmax : p.val = max s.phase.val t.phase.val := by rw [hp]; rfl
  have hpval : p.val = 7 := by rw [hpmax, hs, ht]; decide
  have hs' :
      (runInitsBetween L K s.phase.val p.val
        ({s with phase := p} : AgentState L K)).phase.val = 7 := by
    rw [hs, hpval, runInitsBetween_self]
    simp [hpval]
  have ht' :
      (runInitsBetween L K t.phase.val p.val
        ({t with phase := p} : AgentState L K)).phase.val = 7 := by
    rw [ht, hpval]
    exact runInitsBetween_six_seven_phase _ (by simp [hpval])
  have herr :
      ¬ ((s.phase.val < 10 ∨ t.phase.val < 10) ∧
        ((runInitsBetween L K s.phase.val p.val
            ({s with phase := p} : AgentState L K)).phase.val = 10 ∨
         (runInitsBetween L K t.phase.val p.val
            ({t with phase := p} : AgentState L K)).phase.val = 10)) := by
    intro h
    rcases h.2 with h | h <;> omega
  simp only [herr, if_false]
  exact ⟨hs', ht'⟩

/-- Once the epidemic has placed both agents at Phase 7, dispatching the
original pair is definitionally the same as dispatching that epidemic pair. -/
private theorem Transition_eq_Transition_epidemic_of_phase7
    (s t : AgentState L K)
    (h1 : (phaseEpidemicUpdate L K s t).1.phase.val = 7)
    (h2 : (phaseEpidemicUpdate L K s t).2.phase.val = 7) :
    Transition L K s t =
      Transition L K (phaseEpidemicUpdate L K s t).1
        (phaseEpidemicUpdate L K s t).2 := by
  let ep := phaseEpidemicUpdate L K s t
  have hepid : phaseEpidemicUpdate L K ep.1 ep.2 = ep :=
    Phase7Convergence.phaseEpidemicUpdate_eq_self_of_phase7 ep.1 ep.2 h1 h2
  unfold Transition
  rw [hepid]

private theorem Transition_fst_eq_self_of_phase7_reserve
    (s t : AgentState L K)
    (hs7 : s.phase.val = 7) (ht7 : t.phase.val = 7)
    (hsR : s.role = Role.reserve) :
    (Transition L K s t).1 = s := by
  have hepi := Phase7Convergence.phaseEpidemicUpdate_eq_self_of_phase7
    (L := L) (K := K) s t hs7 ht7
  have hsp : s.phase = ⟨7, by decide⟩ := Fin.ext hs7
  have hboth : ¬ (s.role = Role.main ∧ t.role = Role.main) := by
    intro h
    rw [hsR] at h
    exact (by decide : Role.reserve ≠ Role.main) h.1
  have hp7 : (Phase7Transition L K s t).1 = s := by
    unfold Phase7Transition
    simp only [if_neg hboth]
    rw [if_neg (show s.role ≠ Role.clock by rw [hsR]; decide)]
  unfold Transition
  rw [hepi]
  simp only [hsp]
  rw [finishPhase10Entry_eq_self_of_after_ne_10
    (L := L) (K := K) s _ (by rw [hp7, hs7]; decide)]
  exact hp7

private theorem Transition_snd_eq_self_of_phase7_reserve
    (s t : AgentState L K)
    (hs7 : s.phase.val = 7) (ht7 : t.phase.val = 7)
    (htR : t.role = Role.reserve) :
    (Transition L K s t).2 = t := by
  have hepi := Phase7Convergence.phaseEpidemicUpdate_eq_self_of_phase7
    (L := L) (K := K) s t hs7 ht7
  have hsp : s.phase = ⟨7, by decide⟩ := Fin.ext hs7
  have hboth : ¬ (s.role = Role.main ∧ t.role = Role.main) := by
    intro h
    rw [htR] at h
    exact (by decide : Role.reserve ≠ Role.main) h.2
  have hp7 : (Phase7Transition L K s t).2 = t := by
    unfold Phase7Transition
    simp only [if_neg hboth]
    rw [if_neg (show t.role ≠ Role.clock by rw [htR]; decide)]
  unfold Transition
  rw [hepi]
  simp only [hsp]
  rw [finishPhase10Entry_eq_self_of_after_ne_10
    (L := L) (K := K) t _ (by rw [hp7, ht7]; decide)]
  exact hp7

/-- Phase-7 interactions preserve the dangerous-Reserve count exactly: Main
cancel/split never touches Reserves, while Clock bookkeeping stays a Clock. -/
theorem Transition_dangerousReserveUnit_pair_eq_of_phase7
    (l : ℕ) (s t : AgentState L K)
    (hs7 : s.phase.val = 7) (ht7 : t.phase.val = 7) :
    dangerousReserveUnit (L := L) (K := K) l (Transition L K s t).1 +
        dangerousReserveUnit (L := L) (K := K) l (Transition L K s t).2 =
      dangerousReserveUnit (L := L) (K := K) l s +
        dangerousReserveUnit (L := L) (K := K) l t := by
  obtain ⟨hr1, hr2⟩ :=
    PhaseOnlyWindows.Transition_role_phase7 (L := L) (K := K) s t hs7 ht7
  have hleft :
      dangerousReserveUnit (L := L) (K := K) l (Transition L K s t).1 =
        dangerousReserveUnit (L := L) (K := K) l s := by
    by_cases hsR : s.role = Role.reserve
    · rw [Transition_fst_eq_self_of_phase7_reserve s t hs7 ht7 hsR]
    · have hout : (Transition L K s t).1.role ≠ Role.reserve := by
        rw [hr1]
        exact hsR
      rw [dangerousReserveUnit_of_role_ne_reserve l _ hout,
        dangerousReserveUnit_of_role_ne_reserve l s hsR]
  have hright :
      dangerousReserveUnit (L := L) (K := K) l (Transition L K s t).2 =
        dangerousReserveUnit (L := L) (K := K) l t := by
    by_cases htR : t.role = Role.reserve
    · rw [Transition_snd_eq_self_of_phase7_reserve s t hs7 ht7 htR]
    · have hout : (Transition L K s t).2.role ≠ Role.reserve := by
        rw [hr2]
        exact htR
      rw [dangerousReserveUnit_of_role_ne_reserve l _ hout,
        dangerousReserveUnit_of_role_ne_reserve l t htR]
  rw [hleft, hright]

/-- If the epidemic stage lands both participants in Phase 7, the full mixed
interaction obeys the joint block/debt/danger ledger.  The epidemic itself
preserves exactly the three fields read by these observables. -/
private theorem Transition_block_debt_danger_pair_of_epidemic_phase7
    (sigma : Sign) (l : ℕ) (s t : AgentState L K)
    (hs5 : 5 ≤ s.phase.val) (ht5 : 5 ≤ t.phase.val)
    (hep1 : (phaseEpidemicUpdate L K s t).1.phase.val = 7)
    (hep2 : (phaseEpidemicUpdate L K s t).2.phase.val = 7) :
    majorityBlockUnit (L := L) (K := K) sigma l s +
          majorityBlockUnit (L := L) (K := K) sigma l t +
        minorityDebtUnit (L := L) (K := K) sigma l (Transition L K s t).1 +
        minorityDebtUnit (L := L) (K := K) sigma l (Transition L K s t).2 +
        dangerousReserveUnit (L := L) (K := K) l (Transition L K s t).1 +
        dangerousReserveUnit (L := L) (K := K) l (Transition L K s t).2 ≤
      majorityBlockUnit (L := L) (K := K) sigma l (Transition L K s t).1 +
        majorityBlockUnit (L := L) (K := K) sigma l (Transition L K s t).2 +
        minorityDebtUnit (L := L) (K := K) sigma l s +
        minorityDebtUnit (L := L) (K := K) sigma l t +
        dangerousReserveUnit (L := L) (K := K) l s +
        dangerousReserveUnit (L := L) (K := K) l t := by
  let ep := phaseEpidemicUpdate L K s t
  have htrans : Transition L K s t = Transition L K ep.1 ep.2 :=
    Transition_eq_Transition_epidemic_of_phase7 s t hep1 hep2
  have hledger := Transition_block_debt_pair
    (L := L) (K := K) sigma l ep.1 ep.2 hep1 hep2
  have hdanger := Transition_dangerousReserveUnit_pair_eq_of_phase7
    (L := L) (K := K) l ep.1 ep.2 hep1 hep2
  have hbias := Phase6Convergence.phaseEpidemicUpdate_bias_ge_five
    (L := L) (K := K) s t hs5 ht5
  have hrolehour := ReserveSampling.phaseEpidemicUpdate_role_hour_ge5
    (L := L) (K := K) s t hs5 ht5
  have hblock1 :
      majorityBlockUnit (L := L) (K := K) sigma l ep.1 =
        majorityBlockUnit (L := L) (K := K) sigma l s :=
    majorityBlockUnit_eq_of_role_bias_eq sigma l ep.1 s
      hrolehour.1 hbias.1
  have hblock2 :
      majorityBlockUnit (L := L) (K := K) sigma l ep.2 =
        majorityBlockUnit (L := L) (K := K) sigma l t :=
    majorityBlockUnit_eq_of_role_bias_eq sigma l ep.2 t
      hrolehour.2.2.1 hbias.2
  have hdebt1 :
      minorityDebtUnit (L := L) (K := K) sigma l ep.1 =
        minorityDebtUnit (L := L) (K := K) sigma l s :=
    minorityDebtUnit_eq_of_role_bias_eq sigma l ep.1 s
      hrolehour.1 hbias.1
  have hdebt2 :
      minorityDebtUnit (L := L) (K := K) sigma l ep.2 =
        minorityDebtUnit (L := L) (K := K) sigma l t :=
    minorityDebtUnit_eq_of_role_bias_eq sigma l ep.2 t
      hrolehour.2.2.1 hbias.2
  have hdanger1 :
      dangerousReserveUnit (L := L) (K := K) l ep.1 =
        dangerousReserveUnit (L := L) (K := K) l s :=
    dangerousReserveUnit_eq_of_role_hour_eq l ep.1 s
      hrolehour.1 hrolehour.2.1
  have hdanger2 :
      dangerousReserveUnit (L := L) (K := K) l ep.2 =
        dangerousReserveUnit (L := L) (K := K) l t :=
    dangerousReserveUnit_eq_of_role_hour_eq l ep.2 t
      hrolehour.2.2.1 hrolehour.2.2.2
  rw [htrans]
  omega

/-- Joint per-pair ledger on the whole no-overshoot seam region
`phase ∈ {6,7}`.  The `(6,6)` branch combines the Phase-6 dangerous-fuel
charge with minority-debt nonincrease; every branch containing a Phase-7
agent dispatches through the Phase-7 block/debt ledger after the epidemic. -/
theorem Transition_block_debt_danger_pair_of_phase_six_or_seven
    (sigma : Sign) (l : ℕ) (s t : AgentState L K)
    (hs : s.phase.val = 6 ∨ s.phase.val = 7)
    (ht : t.phase.val = 6 ∨ t.phase.val = 7) :
    majorityBlockUnit (L := L) (K := K) sigma l s +
          majorityBlockUnit (L := L) (K := K) sigma l t +
        minorityDebtUnit (L := L) (K := K) sigma l (Transition L K s t).1 +
        minorityDebtUnit (L := L) (K := K) sigma l (Transition L K s t).2 +
        dangerousReserveUnit (L := L) (K := K) l (Transition L K s t).1 +
        dangerousReserveUnit (L := L) (K := K) l (Transition L K s t).2 ≤
      majorityBlockUnit (L := L) (K := K) sigma l (Transition L K s t).1 +
        majorityBlockUnit (L := L) (K := K) sigma l (Transition L K s t).2 +
        minorityDebtUnit (L := L) (K := K) sigma l s +
        minorityDebtUnit (L := L) (K := K) sigma l t +
        dangerousReserveUnit (L := L) (K := K) l s +
        dangerousReserveUnit (L := L) (K := K) l t := by
  rcases hs with hs6 | hs7 <;> rcases ht with ht6 | ht7
  · have hblock := Transition_block_danger_pair
      (L := L) (K := K) sigma l s t hs6 ht6
    have hdebt := Transition_minorityDebt_pair_le_of_phase6
      (L := L) (K := K) sigma l s t hs6 ht6
    omega
  · obtain ⟨hep1, hep2⟩ :=
      phaseEpidemicUpdate_phases_seven_of_six_seven s t hs6 ht7
    exact Transition_block_debt_danger_pair_of_epidemic_phase7
      sigma l s t (by omega) (by omega) hep1 hep2
  · obtain ⟨hep1, hep2⟩ :=
      phaseEpidemicUpdate_phases_seven_of_seven_six s t hs7 ht6
    exact Transition_block_debt_danger_pair_of_epidemic_phase7
      sigma l s t (by omega) (by omega) hep1 hep2
  · have hledger := Transition_block_debt_pair
      (L := L) (K := K) sigma l s t hs7 ht7
    have hdanger := Transition_dangerousReserveUnit_pair_eq_of_phase7
      (L := L) (K := K) l s t hs7 ht7
    omega

private theorem mem_of_app_left6Block {c : Config (AgentState L K)}
    {r₁ r₂ : AgentState L K} (happ : Protocol.Applicable c r₁ r₂) : r₁ ∈ c :=
  Multiset.mem_of_le
    (show ({r₁, r₂} : Multiset (AgentState L K)) ≤ c from happ) (by simp)

private theorem mem_of_app_right6Block {c : Config (AgentState L K)}
    {r₁ r₂ : AgentState L K} (happ : Protocol.Applicable c r₁ r₂) : r₂ ∈ c :=
  Multiset.mem_of_le
    (show ({r₁, r₂} : Multiset (AgentState L K)) ≤ c from happ) (by simp)

/-- The exact deterministic seam region before Phase 7 becomes homogeneous.
It is deliberately phase-only: all payload preservation is proved from the
frozen transition rather than assumed here. -/
def Phase6To7Window (c : Config (AgentState L K)) : Prop :=
  ∀ a ∈ c, a.phase.val = 6 ∨ a.phase.val = 7

/-- Joint resource invariant through the mixed 6/7 seam.  Remaining dangerous
Reserves are retained in the ledger because two still-Phase-6 agents may split
even after the first Phase-7 seed has appeared. -/
def Phase6To7FuelLedger (sigma : Sign) (l G : ℕ)
    (c : Config (AgentState L K)) : Prop :=
  G + minorityDebt (L := L) (K := K) sigma l c +
      dangerousReserveCount (L := L) (K := K) l c ≤
    majorityBlockCount (L := L) (K := K) sigma l c

/-- The mixed 6/7 fuel ledger survives every scheduled interaction whose
source remains in the no-overshoot seam region. -/
theorem phase6To7FuelLedger_stepOrSelf
    (sigma : Sign) (l G : ℕ) (c : Config (AgentState L K))
    (hwin : Phase6To7Window (L := L) (K := K) c)
    (hledger : Phase6To7FuelLedger (L := L) (K := K) sigma l G c)
    (r₁ r₂ : AgentState L K) :
    Phase6To7FuelLedger (L := L) (K := K) sigma l G
      (Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂) := by
  by_cases happ : Protocol.Applicable c r₁ r₂
  · have hm1 := mem_of_app_left6Block happ
    have hm2 := mem_of_app_right6Block happ
    have hphase1 := hwin r₁ hm1
    have hphase2 := hwin r₂ hm2
    have hsub : ({r₁, r₂} : Multiset (AgentState L K)) ≤ c := happ
    have hcsplit : c = (c - {r₁, r₂}) + {r₁, r₂} :=
      (tsub_add_cancel_of_le hsub).symm
    have hc' : Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂ =
        c - {r₁, r₂} + {(Transition L K r₁ r₂).1,
          (Transition L K r₁ r₂).2} := by
      unfold Protocol.stepOrSelf
      rw [if_pos happ]
      rfl
    have hpair :
        majorityBlockCount (L := L) (K := K) sigma l
              ({r₁, r₂} : Config (AgentState L K)) +
            minorityDebt (L := L) (K := K) sigma l
              ({(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2} :
                Config (AgentState L K)) +
            dangerousReserveCount (L := L) (K := K) l
              ({(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2} :
                Config (AgentState L K)) ≤
          majorityBlockCount (L := L) (K := K) sigma l
              ({(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2} :
                Config (AgentState L K)) +
            minorityDebt (L := L) (K := K) sigma l
              ({r₁, r₂} : Config (AgentState L K)) +
            dangerousReserveCount (L := L) (K := K) l
              ({r₁, r₂} : Config (AgentState L K)) := by
      rw [majorityBlockCount_pair, majorityBlockCount_pair,
        minorityDebt_pair, minorityDebt_pair,
        dangerousReserveCount_pair, dangerousReserveCount_pair]
      simpa [add_assoc] using
        (Transition_block_debt_danger_pair_of_phase_six_or_seven
          sigma l r₁ r₂ hphase1 hphase2)
    have hledger' :
        G +
            (minorityDebt (L := L) (K := K) sigma l (c - {r₁, r₂}) +
              minorityDebt (L := L) (K := K) sigma l
                ({r₁, r₂} : Config (AgentState L K))) +
            (dangerousReserveCount (L := L) (K := K) l (c - {r₁, r₂}) +
              dangerousReserveCount (L := L) (K := K) l
                ({r₁, r₂} : Config (AgentState L K))) ≤
          majorityBlockCount (L := L) (K := K) sigma l (c - {r₁, r₂}) +
            majorityBlockCount (L := L) (K := K) sigma l
              ({r₁, r₂} : Config (AgentState L K)) := by
      rw [← minorityDebt_add, ← dangerousReserveCount_add,
        ← majorityBlockCount_add, ← hcsplit]
      exact hledger
    unfold Phase6To7FuelLedger
    rw [hc', minorityDebt_add, dangerousReserveCount_add, majorityBlockCount_add]
    omega
  · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]
    exact hledger

/-- A successful protocol step inside the mixed Phase-6/7 region. -/
def Phase6To7Step (c c' : Config (AgentState L K)) : Prop :=
  Phase6To7Window (L := L) (K := K) c ∧
    (NonuniformMajority L K).StepRel c c'

/-- Reflexive-transitive real reachability through the mixed Phase-6/7 seam. -/
def Phase6To7Reachable (c c' : Config (AgentState L K)) : Prop :=
  Relation.ReflTransGen (Phase6To7Step (L := L) (K := K)) c c'

theorem phase6To7FuelLedger_of_step
    (sigma : Sign) (l G : ℕ)
    {c c' : Config (AgentState L K)}
    (hstep : Phase6To7Step (L := L) (K := K) c c')
    (hledger : Phase6To7FuelLedger (L := L) (K := K) sigma l G c) :
    Phase6To7FuelLedger (L := L) (K := K) sigma l G c' := by
  rcases hstep with ⟨hwin, r₁, r₂, happ, hc'⟩
  have hs := phase6To7FuelLedger_stepOrSelf
    sigma l G c hwin hledger r₁ r₂
  have heq : c' = Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂ := by
    rw [hc']
    unfold Protocol.stepOrSelf
    rw [if_pos happ]
    rfl
  simpa [heq] using hs

/-- The joint fuel ledger transfers through an arbitrary finite mixed seam. -/
theorem phase6To7FuelLedger_of_reachable
    (sigma : Sign) (l G : ℕ)
    {c₀ c : Config (AgentState L K)}
    (hreach : Phase6To7Reachable (L := L) (K := K) c₀ c)
    (hledger : Phase6To7FuelLedger (L := L) (K := K) sigma l G c₀) :
    Phase6To7FuelLedger (L := L) (K := K) sigma l G c := by
  induction hreach with
  | refl => exact hledger
  | tail _ hlast ih =>
      exact phase6To7FuelLedger_of_step sigma l G hlast ih

/-- Forgetting the nonnegative unspent Reserve fuel yields the public Phase-7
majority-block ledger. -/
theorem majorityBlockLedger_of_phase6To7FuelLedger
    (sigma : Sign) (l G : ℕ) (c : Config (AgentState L K))
    (h : Phase6To7FuelLedger (L := L) (K := K) sigma l G c) :
    MajorityBlockLedger (L := L) (K := K) sigma l G c := by
  unfold Phase6To7FuelLedger at h
  unfold MajorityBlockLedger
  omega

/-- Global one-step charge inequality on the exact Phase-6 work window. -/
theorem block_danger_stepOrSelf
    (n : ℕ) (sigma : Sign) (l : ℕ) (c : Config (AgentState L K))
    (hwin : Phase6Convergence.Phase6Win (L := L) (K := K) n c)
    (r₁ r₂ : AgentState L K) :
    majorityBlockCount (L := L) (K := K) sigma l c +
        dangerousReserveCount (L := L) (K := K) l
          (Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂) ≤
      majorityBlockCount (L := L) (K := K) sigma l
          (Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂) +
        dangerousReserveCount (L := L) (K := K) l c := by
  by_cases happ : Protocol.Applicable c r₁ r₂
  · have hm1 := mem_of_app_left6Block happ
    have hm2 := mem_of_app_right6Block happ
    have h16 : r₁.phase.val = 6 := hwin.2 r₁ hm1
    have h26 : r₂.phase.val = 6 := hwin.2 r₂ hm2
    have hsub : ({r₁, r₂} : Multiset (AgentState L K)) ≤ c := happ
    have hcsplit : c = (c - {r₁, r₂}) + {r₁, r₂} :=
      (tsub_add_cancel_of_le hsub).symm
    have hc' : Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂ =
        c - {r₁, r₂} + {(Transition L K r₁ r₂).1,
          (Transition L K r₁ r₂).2} := by
      unfold Protocol.stepOrSelf
      rw [if_pos happ]
      rfl
    have hpair :
        majorityBlockCount (L := L) (K := K) sigma l
              ({r₁, r₂} : Config (AgentState L K)) +
            dangerousReserveCount (L := L) (K := K) l
              ({(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2} :
                Config (AgentState L K)) ≤
          majorityBlockCount (L := L) (K := K) sigma l
              ({(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2} :
                Config (AgentState L K)) +
            dangerousReserveCount (L := L) (K := K) l
              ({r₁, r₂} : Config (AgentState L K)) := by
      rw [majorityBlockCount_pair, majorityBlockCount_pair,
        dangerousReserveCount_pair, dangerousReserveCount_pair]
      exact Transition_block_danger_pair sigma l r₁ r₂ h16 h26
    have hBsrc :
        majorityBlockCount (L := L) (K := K) sigma l c =
          majorityBlockCount (L := L) (K := K) sigma l (c - {r₁, r₂}) +
            majorityBlockCount (L := L) (K := K) sigma l
              ({r₁, r₂} : Config (AgentState L K)) := by
      conv_lhs => rw [hcsplit]
      rw [majorityBlockCount_add]
    have hDsrc :
        dangerousReserveCount (L := L) (K := K) l c =
          dangerousReserveCount (L := L) (K := K) l (c - {r₁, r₂}) +
            dangerousReserveCount (L := L) (K := K) l
              ({r₁, r₂} : Config (AgentState L K)) := by
      conv_lhs => rw [hcsplit]
      rw [dangerousReserveCount_add]
    rw [hc', majorityBlockCount_add, dangerousReserveCount_add, hBsrc, hDsrc]
    omega
  · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]

/-- One real protocol step whose source still lies in the exact homogeneous
Phase-6 work window.  This is the window used by `phase6Convergence'`; a clock
exit is handled separately by its killed/survival wrapper. -/
def Phase6WorkStep (n : ℕ)
    (c c' : Config (AgentState L K)) : Prop :=
  Phase6Convergence.Phase6Win (L := L) (K := K) n c ∧
    (NonuniformMajority L K).StepRel c c'

/-- Reflexive-transitive work-prefix reachability before a Phase-6 window
escape. -/
def Phase6WorkReachable (n : ℕ)
    (c c' : Config (AgentState L K)) : Prop :=
  Relation.ReflTransGen (Phase6WorkStep (L := L) (K := K) n) c c'

/-- Minority debt is nonincreasing under one scheduled interaction in a
homogeneous Phase-6 work configuration. -/
theorem minorityDebt_stepOrSelf_phase6
    (n : ℕ) (sigma : Sign) (l : ℕ) (c : Config (AgentState L K))
    (hwin : Phase6Convergence.Phase6Win (L := L) (K := K) n c)
    (r₁ r₂ : AgentState L K) :
    minorityDebt (L := L) (K := K) sigma l
        (Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂) ≤
      minorityDebt (L := L) (K := K) sigma l c := by
  by_cases happ : Protocol.Applicable c r₁ r₂
  · have hm1 := mem_of_app_left6Block happ
    have hm2 := mem_of_app_right6Block happ
    have h16 : r₁.phase.val = 6 := hwin.2 r₁ hm1
    have h26 : r₂.phase.val = 6 := hwin.2 r₂ hm2
    have hsub : ({r₁, r₂} : Multiset (AgentState L K)) ≤ c := happ
    have hcsplit : c = (c - {r₁, r₂}) + {r₁, r₂} :=
      (tsub_add_cancel_of_le hsub).symm
    have hc' : Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂ =
        c - {r₁, r₂} + {(Transition L K r₁ r₂).1,
          (Transition L K r₁ r₂).2} := by
      unfold Protocol.stepOrSelf
      rw [if_pos happ]
      rfl
    have hpair := Transition_minorityDebt_pair_le_of_phase6
      (L := L) (K := K) sigma l r₁ r₂ h16 h26
    have hDsrc :
        minorityDebt (L := L) (K := K) sigma l c =
          minorityDebt (L := L) (K := K) sigma l (c - {r₁, r₂}) +
            minorityDebt (L := L) (K := K) sigma l
              ({r₁, r₂} : Config (AgentState L K)) := by
      conv_lhs => rw [hcsplit]
      rw [minorityDebt_add]
    rw [hc', minorityDebt_add, minorityDebt_pair, hDsrc, minorityDebt_pair]
    omega
  · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]

/-- Minority debt is nonincreasing along one successful Phase-6 work step. -/
theorem minorityDebt_of_phase6WorkStep
    (n : ℕ) (sigma : Sign) (l : ℕ)
    {c c' : Config (AgentState L K)}
    (hstep : Phase6WorkStep (L := L) (K := K) n c c') :
    minorityDebt (L := L) (K := K) sigma l c' ≤
      minorityDebt (L := L) (K := K) sigma l c := by
  rcases hstep with ⟨hwin, r₁, r₂, happ, hc'⟩
  have hs := minorityDebt_stepOrSelf_phase6 n sigma l c hwin r₁ r₂
  have heq : c' = Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂ := by
    rw [hc']
    unfold Protocol.stepOrSelf
    rw [if_pos happ]
    rfl
  simpa [heq] using hs

/-- Minority debt is nonincreasing along every homogeneous Phase-6 work
prefix. -/
theorem minorityDebt_of_phase6WorkReachable
    (n : ℕ) (sigma : Sign) (l : ℕ)
    {c₀ c : Config (AgentState L K)}
    (hreach : Phase6WorkReachable (L := L) (K := K) n c₀ c) :
    minorityDebt (L := L) (K := K) sigma l c ≤
      minorityDebt (L := L) (K := K) sigma l c₀ := by
  induction hreach with
  | refl => exact le_rfl
  | tail _ hlast ih =>
      exact (minorityDebt_of_phase6WorkStep n sigma l hlast).trans ih

/-- End-to-end deterministic transport of the sharp Phase-3 minority-mass
bound through the real Phase-3/4 seam, the static Phase-4/5 seam, and a
homogeneous Phase-6 work prefix. -/
theorem minorityDebt_64_after_phase34_phase45_phase6
    (n l M : ℕ) (sigmaMajority : Sign)
    {c3 c4 c5 c6 : Config (AgentState L K)}
    (hminor :
      Phase3Post3.minorityMass (L := L) (K := K) sigmaMajority c3 ≤
        (1 / 250 : ℝ) * (M : ℝ) * (2 : ℝ) ^ (-(l : ℤ)))
    (h34 : Phase5To6FuelProducer.ReachableThroughPhase34
      (L := L) (K := K) c3 c4)
    (h45 : Phase5To6FuelProducer.ReachableThroughPhase45
      (L := L) (K := K) c4 c5)
    (h6 : Phase6WorkReachable (L := L) (K := K) n c5 c6) :
    1000 * minorityDebt (L := L) (K := K)
        (Phase3Post3.minoritySignOfMajority sigmaMajority) l c6 ≤
      64 * M := by
  have h4 := minorityDebt_64_of_minorityMass_bound_after_phase34
    (L := L) (K := K) l M sigmaMajority hminor h34
  have h45eq := minorityDebt_eq_of_reachableThroughPhase45
    (L := L) (K := K)
    (Phase3Post3.minoritySignOfMajority sigmaMajority) l c4 c5 h45
  have h6le := minorityDebt_of_phase6WorkReachable
    (L := L) (K := K) n
    (Phase3Post3.minoritySignOfMajority sigmaMajority) l h6
  omega

/-- Adapter from the actual slot-3 `Post3` object.  Its real mass parameter is
pinned to the natural Main count used by the Phase-6/7 integer ledgers. -/
theorem minorityDebt_64_of_post3_routes
    (n3 n6 l M : ℕ) (sigmaMajority : Sign) (g₀ : ℝ)
    {c3 c4 c5 c6 : Config (AgentState L K)}
    (hpost : Phase3Post3.Post3
      (L := L) (K := K) n3 l (M : ℝ) sigmaMajority g₀ c3)
    (h34 : Phase5To6FuelProducer.ReachableThroughPhase34
      (L := L) (K := K) c3 c4)
    (h45 : Phase5To6FuelProducer.ReachableThroughPhase45
      (L := L) (K := K) c4 c5)
    (h6 : Phase6WorkReachable (L := L) (K := K) n6 c5 c6) :
    1000 * minorityDebt (L := L) (K := K)
        (Phase3Post3.minoritySignOfMajority sigmaMajority) l c6 ≤
      64 * M :=
  minorityDebt_64_after_phase34_phase45_phase6
    (L := L) (K := K) n6 l M sigmaMajority
    hpost.minority_small h34 h45 h6

/-- Equivalent adapter for the internal `Snapshot617` producer. -/
theorem minorityDebt_64_of_snapshot617_routes
    (n3 n6 l M : ℕ) (sigmaMajority : Sign) (g₀ : ℝ)
    {c3 c4 c5 c6 : Config (AgentState L K)}
    (hs : Phase3Post3.Snapshot617
      (L := L) (K := K) n3 l (M : ℝ) g₀ sigmaMajority c3)
    (h34 : Phase5To6FuelProducer.ReachableThroughPhase34
      (L := L) (K := K) c3 c4)
    (h45 : Phase5To6FuelProducer.ReachableThroughPhase45
      (L := L) (K := K) c4 c5)
    (h6 : Phase6WorkReachable (L := L) (K := K) n6 c5 c6) :
    1000 * minorityDebt (L := L) (K := K)
        (Phase3Post3.minoritySignOfMajority sigmaMajority) l c6 ≤
      64 * M :=
  minorityDebt_64_after_phase34_phase45_phase6
    (L := L) (K := K) n6 l M sigmaMajority
    hs.minority_bound h34 h45 h6

theorem block_danger_of_phase6WorkStep
    (n : ℕ) (sigma : Sign) (l : ℕ)
    {c c' : Config (AgentState L K)}
    (hstep : Phase6WorkStep (L := L) (K := K) n c c') :
    majorityBlockCount (L := L) (K := K) sigma l c +
        dangerousReserveCount (L := L) (K := K) l c' ≤
      majorityBlockCount (L := L) (K := K) sigma l c' +
        dangerousReserveCount (L := L) (K := K) l c := by
  rcases hstep with ⟨hwin, r₁, r₂, happ, hc'⟩
  have hs := block_danger_stepOrSelf n sigma l c hwin r₁ r₂
  have heq : c' = Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂ := by
    rw [hc']
    unfold Protocol.stepOrSelf
    rw [if_pos happ]
    rfl
  simpa [heq] using hs

/-- Prefix ledger: block losses over an arbitrary successful Phase-6 work
prefix are no larger than the number of dangerous Reserves consumed. -/
theorem block_danger_of_phase6WorkReachable
    (n : ℕ) (sigma : Sign) (l : ℕ)
    {c₀ c : Config (AgentState L K)}
    (hreach : Phase6WorkReachable (L := L) (K := K) n c₀ c) :
    majorityBlockCount (L := L) (K := K) sigma l c₀ +
        dangerousReserveCount (L := L) (K := K) l c ≤
      majorityBlockCount (L := L) (K := K) sigma l c +
        dangerousReserveCount (L := L) (K := K) l c₀ := by
  induction hreach with
  | refl => exact le_rfl
  | tail hprev hlast ih =>
      have hstep := block_danger_of_phase6WorkStep n sigma l hlast
      omega

/-! ## The `0.92 - 0.05 = 0.87` endpoint arithmetic -/

/-- The paper's two sampling numerics imply the required five-percent cap:
dangerous samples are at most `0.09 |R|`, and `|R| ≤ (5/9)|M|`. -/
theorem dangerousReserve_cap_five_percent
    (M R bad : ℕ)
    (hsample : 100 * bad ≤ 9 * R)
    (hrole : 9 * R ≤ 5 * M) :
    1000 * bad ≤ 50 * M := by
  omega

/-- Deterministic Lemma-7.3 endpoint.  Starting with a `0.92 M` fixed block
and at most `0.05 M` dangerous sampled Reserves leaves a `0.87 M` block after
every successful Phase-6 work prefix. -/
theorem phase6_endpoint_majorityBlock_870
    (n M : ℕ) (sigma : Sign) (l : ℕ)
    {c₀ c : Config (AgentState L K)}
    (hreach : Phase6WorkReachable (L := L) (K := K) n c₀ c)
    (hstart : 920 * M ≤
      1000 * majorityBlockCount (L := L) (K := K) sigma l c₀)
    (hdanger : 1000 * dangerousReserveCount (L := L) (K := K) l c₀ ≤
      50 * M) :
    870 * M ≤
      1000 * majorityBlockCount (L := L) (K := K) sigma l c := by
  have hledger := block_danger_of_phase6WorkReachable
    (L := L) (K := K) n sigma l hreach
  omega

/-! ## Theorem-6.2 start-block adapter -/

/-- The paper's `majorityConfined3` count is contained in the fixed block used
by the Phase-7 ledger.  The definitions use different presentations (a
disjoint sum over three exponent fibers versus one filtered finset), so the
containment is proved explicitly. -/
theorem majorityConfined3_le_majorityBlockCount
    (sigma : Sign) (l : ℕ) (hl : l + 2 < L + 1)
    (c : Config (AgentState L K)) :
    PaperRegime.majorityConfined3 (L := L) (K := K) sigma l hl c ≤
      majorityBlockCount (L := L) (K := K) sigma l c := by
  classical
  rw [majorityBlockCount_eq_sum_count]
  unfold PaperRegime.majorityConfined3
  set band : Finset (AgentState L K) :=
    (PaperRegime.threeLevels (L := L) l hl).biUnion
      (fun i => MarginLedgers.majorityAtExp (L := L) (K := K) sigma i) with hband
  have hdisj :
      (↑(PaperRegime.threeLevels (L := L) l hl) : Set (Fin (L + 1))).PairwiseDisjoint
        (fun i => MarginLedgers.majorityAtExp (L := L) (K := K) sigma i) := by
    intro i _ j _ hij
    simp only [Function.onFun, Finset.disjoint_left]
    intro a hai haj
    simp only [MarginLedgers.majorityAtExp, Finset.mem_filter,
      Finset.mem_univ, true_and] at hai haj
    obtain ⟨_, si, _, hbi⟩ := hai
    obtain ⟨_, sj, _, hbj⟩ := haj
    rw [hbi] at hbj
    injection hbj with _ hidx
    exact hij hidx
  have hsum :
      (∑ i ∈ PaperRegime.threeLevels (L := L) l hl,
        (MarginLedgers.majorityAtExp (L := L) (K := K) sigma i).sum c.count) =
          band.sum c.count := by
    rw [hband, Finset.sum_biUnion hdisj]
  rw [hsum]
  apply Finset.sum_le_sum_of_subset
  intro a ha
  simp only [hband, Finset.mem_biUnion] at ha
  obtain ⟨i, hi, hai⟩ := ha
  simp only [MarginLedgers.majorityAtExp, Finset.mem_filter,
    Finset.mem_univ, true_and] at hai
  obtain ⟨hmain, sgn, hsne, hbias⟩ := hai
  have hirange : l ≤ i.val ∧ i.val < l + 3 := by
    simp only [PaperRegime.threeLevels, Finset.mem_insert,
      Finset.mem_singleton] at hi
    rcases hi with hi | hi | hi
    all_goals
      have hv := congrArg Fin.val hi
      simp at hv
      omega
  rw [majorityBand3, Finset.mem_filter]
  exact ⟨Finset.mem_univ _, hmain, sgn, i, hsne, hbias,
    hirange.1, hirange.2⟩

/-- Integer-scaled `0.92` start block obtained directly from the faithful
Theorem-6.2 object. -/
theorem theorem62Paper_majorityBlock_920
    (sigma : Sign) (l : ℕ) (hl : l + 2 < L + 1) (n : ℕ)
    (c : Config (AgentState L K))
    (hP : PaperRegime.Theorem62Paper
      (L := L) (K := K) sigma l hl n c) :
    920 * RoleSplitConcentration.mainCount (L := L) (K := K) c ≤
      1000 * majorityBlockCount (L := L) (K := K) sigma l c := by
  have hsubset := majorityConfined3_le_majorityBlockCount
    (L := L) (K := K) sigma l hl c
  have hsubsetR :
      ((PaperRegime.majorityConfined3
        (L := L) (K := K) sigma l hl c : ℕ) : ℝ) ≤
        (majorityBlockCount (L := L) (K := K) sigma l c : ℝ) := by
    exact_mod_cast hsubset
  have hscaled :
      (920 : ℝ) *
          (RoleSplitConcentration.mainCount (L := L) (K := K) c : ℝ) ≤
        (1000 : ℝ) *
          (majorityBlockCount (L := L) (K := K) sigma l c : ℝ) := by
    nlinarith [hP.hConfine3]
  exact_mod_cast hscaled

/-- End-to-end deterministic `0.87M` snapshot from the faithful Theorem-6.2
entry object and the five-percent dangerous-sample residual. -/
theorem phase6_endpoint_majorityBlock_870_of_paper
    (sigma : Sign) (l : ℕ) (hl : l + 2 < L + 1) (n : ℕ)
    {c₀ c : Config (AgentState L K)}
    (hP : PaperRegime.Theorem62Paper
      (L := L) (K := K) sigma l hl n c₀)
    (hreach : Phase6WorkReachable (L := L) (K := K) n c₀ c)
    (hdanger :
      1000 * dangerousReserveCount (L := L) (K := K) l c₀ ≤
        50 * RoleSplitConcentration.mainCount (L := L) (K := K) c₀) :
    870 * RoleSplitConcentration.mainCount (L := L) (K := K) c₀ ≤
      1000 * majorityBlockCount (L := L) (K := K) sigma l c := by
  exact phase6_endpoint_majorityBlock_870
    (L := L) (K := K) n
    (RoleSplitConcentration.mainCount (L := L) (K := K) c₀)
    sigma l hreach (theorem62Paper_majorityBlock_920 sigma l hl n c₀ hP) hdanger

/-- Strong Phase-6 endpoint snapshot for the mixed seam.  Unlike the bare
`0.87M` block statement, this keeps every unspent dangerous Reserve on the
left side of the resource ledger; this is exactly what permits subsequent
`(6,6)` interactions after the first Phase-7 seed. -/
theorem phase6_endpoint_fuelLedger_of_paper
    (n M : ℕ) (sigma : Sign) (l : ℕ) (hl : l + 2 < L + 1)
    {c₀ c6 : Config (AgentState L K)}
    (hP : PaperRegime.Theorem62Paper
      (L := L) (K := K) sigma l hl n c₀)
    (hM : RoleSplitConcentration.mainCount (L := L) (K := K) c₀ = M)
    (hwork : Phase6WorkReachable (L := L) (K := K) n c₀ c6)
    (hdanger :
      1000 * dangerousReserveCount (L := L) (K := K) l c₀ ≤ 50 * M)
    (hdebt :
      1000 * minorityDebt (L := L) (K := K) sigma l c6 ≤ 64 * M) :
    Phase6To7FuelLedger (L := L) (K := K) sigma l (4 * M / 5) c6 := by
  have hcharge := block_danger_of_phase6WorkReachable
    (L := L) (K := K) n sigma l hwork
  have h920 := theorem62Paper_majorityBlock_920
    (L := L) (K := K) sigma l hl n c₀ hP
  have hfloor := Nat.div_mul_le_self (4 * M) 5
  unfold Phase6To7FuelLedger
  rw [hM] at h920
  omega

/-! ## Why the current Phase-5 post is insufficient -/

namespace OneClassPostObstruction

def protectedIndex : Fin 5 := ⟨1, by decide⟩

def protectedReserve : AgentState 4 0 :=
  { input := .A
    output := .A
    phase := ⟨5, by decide⟩
    role := .reserve
    assigned := true
    bias := .zero
    smallBias := ⟨3, by decide⟩
    hour := protectedIndex
    minute := ⟨0, by decide⟩
    full := false
    opinions := ⟨0, by decide⟩
    counter := ⟨1, by decide⟩ }

def dangerousReserve : AgentState 4 0 :=
  { protectedReserve with hour := ⟨3, by decide⟩ }

def majorityMain : AgentState 4 0 :=
  { protectedReserve with
      role := .main
      bias := .dyadic .pos ⟨0, by decide⟩
      hour := ⟨0, by decide⟩ }

def c : Config (AgentState 4 0) :=
  {protectedReserve, dangerousReserve, majorityMain}

/-- A concrete current Phase-5 post: every Reserve sampled, and one Reserve
lies in the useful protected class. -/
theorem phase5Post_holds :
    ReserveSampling.Phase5AllWin (L := 4) (K := 0) 3 c ∧
      Phase5Convergence.ReserveSampleGood
        (L := 4) (K := 0) protectedIndex 1 c := by
  constructor
  · constructor
    · rfl
    · intro a ha
      change a ∈ protectedReserve ::ₘ dangerousReserve ::ₘ majorityMain ::ₘ 0 at ha
      simp only [Multiset.mem_cons] at ha
      simp at ha
      rcases ha with ha | ha | ha
      · subst a
        rfl
      · subst a
        rfl
      · subst a
        rfl
  · constructor
    · unfold ReserveSampling.ReserveSampled ReserveSampling.unsampledReserveU
      change Multiset.countP _
        (protectedReserve ::ₘ dangerousReserve ::ₘ majorityMain ::ₘ 0) = 0
      rw [Multiset.countP_cons, Multiset.countP_cons,
        Multiset.countP_cons, Multiset.countP_zero]
      norm_num [ReserveSampling.unsampled, protectedReserve,
        dangerousReserve, majorityMain, protectedIndex]
    · unfold Phase5Convergence.sampledFloor
        Phase5Convergence.sampledReserveClassU
      change 1 ≤ Multiset.countP _
        (protectedReserve ::ₘ dangerousReserve ::ₘ majorityMain ::ₘ 0)
      rw [Multiset.countP_cons, Multiset.countP_cons,
        Multiset.countP_cons, Multiset.countP_zero]
      norm_num [Phase5Convergence.sampledReserveClass, protectedReserve,
        dangerousReserve, majorityMain, protectedIndex]

theorem dangerous_count_eq_one :
    dangerousReserveCount (L := 4) (K := 0) 0 c = 1 := by
  unfold dangerousReserveCount
  change Multiset.countP _
    (protectedReserve ::ₘ dangerousReserve ::ₘ majorityMain ::ₘ 0) = 1
  rw [Multiset.countP_cons, Multiset.countP_cons,
    Multiset.countP_cons, Multiset.countP_zero]
  norm_num [protectedReserve, dangerousReserve, majorityMain, protectedIndex]

theorem main_count_eq_one :
    RoleSplitConcentration.mainCount (L := 4) (K := 0) c = 1 := by
  unfold RoleSplitConcentration.mainCount
  change Multiset.countP _
    (protectedReserve ::ₘ dangerousReserve ::ₘ majorityMain ::ₘ 0) = 1
  rw [Multiset.countP_cons, Multiset.countP_cons,
    Multiset.countP_cons, Multiset.countP_zero]
  simp [protectedReserve, dangerousReserve, majorityMain]

/-- Therefore the one-class `ReserveSampleGood` currently exported by Phase 5
does not imply the five-percent dangerous-sample cap needed for Lemma 7.3. -/
theorem phase5Post_not_enough_for_five_percent :
    ReserveSampling.Phase5AllWin (L := 4) (K := 0) 3 c ∧
      Phase5Convergence.ReserveSampleGood
          (L := 4) (K := 0) protectedIndex 1 c ∧
      ¬ 1000 * dangerousReserveCount (L := 4) (K := 0) 0 c ≤
          50 * RoleSplitConcentration.mainCount (L := 4) (K := 0) c := by
  refine ⟨phase5Post_holds.1, phase5Post_holds.2, ?_⟩
  rw [dangerous_count_eq_one, main_count_eq_one]
  norm_num

end OneClassPostObstruction

/-! ## Why bare majority-block transfer is false -/

namespace BareBlockTransferObstruction

/-- A Phase-6 majority Main at the bottom of the protected block. -/
def majority6 : AgentState 2 0 :=
  { input := .A
    output := .A
    phase := ⟨6, by decide⟩
    role := .main
    assigned := true
    bias := .dyadic .pos ⟨0, by decide⟩
    smallBias := ⟨3, by decide⟩
    hour := ⟨0, by decide⟩
    minute := ⟨0, by decide⟩
    full := false
    opinions := ⟨4, by decide⟩
    counter := ⟨1, by decide⟩ }

/-- An opposite-sign Phase-7 Main at the same exponent. -/
def minority7 : AgentState 2 0 :=
  { majority6 with
      phase := ⟨7, by decide⟩
      bias := .dyadic .neg ⟨0, by decide⟩ }

def source : Config (AgentState 2 0) := {majority6, minority7}

def target : Config (AgentState 2 0) :=
  {(Transition 2 0 majority6 minority7).1,
    (Transition 2 0 majority6 minority7).2}

/-- The epidemic first lifts the Phase-6 Main to Phase 7, after which the
equal-index opposite-sign pair cancels. -/
private theorem transition_eq_zero_pair :
    Transition 2 0 majority6 minority7 =
      ({majority6 with phase := ⟨7, by decide⟩, bias := .zero},
       {minority7 with bias := .zero}) := by
  rfl

theorem source_block_eq_one :
    majorityBlockCount (L := 2) (K := 0) .neg 0 source = 1 := by
  unfold source
  rw [majorityBlockCount_pair]
  rw [majorityBlockUnit_main_dyadic .neg .pos 0 ⟨0, by decide⟩ majority6
    (by rfl) (by rfl)]
  rw [majorityBlockUnit_main_dyadic .neg .neg 0 ⟨0, by decide⟩ minority7
    (by rfl) (by rfl)]
  decide

theorem target_block_eq_zero :
    majorityBlockCount (L := 2) (K := 0) .neg 0 target = 0 := by
  unfold target
  rw [transition_eq_zero_pair, majorityBlockCount_pair]
  rw [majorityBlockUnit_main_zero .neg 0 _ (by rfl) (by rfl)]
  rw [majorityBlockUnit_main_zero .neg 0 _ (by rfl) (by rfl)]

theorem source_step_target :
    (NonuniformMajority 2 0).StepRel source target := by
  refine ⟨majority6, minority7, ?_, ?_⟩
  · exact le_rfl
  · change target = source - {majority6, minority7} +
      {(Transition 2 0 majority6 minority7).1,
        (Transition 2 0 majority6 minority7).2}
    rw [show source = ({majority6, minority7} : Config (AgentState 2 0)) from rfl,
      tsub_self, zero_add]
    rfl

/-- Hence no theorem can transfer the bare block count monotonically across
an arbitrary real mixed Phase-6/7 step.  The block/debt ledger above is the
minimal correction: this cancellation simultaneously pays minority debt. -/
theorem bare_block_transfer_fails :
    (NonuniformMajority 2 0).StepRel source target ∧
      majorityBlockCount (L := 2) (K := 0) .neg 0 target <
        majorityBlockCount (L := 2) (K := 0) .neg 0 source := by
  rw [source_block_eq_one, target_block_eq_zero]
  exact ⟨source_step_target, by decide⟩

end BareBlockTransferObstruction

/-! ## Exact residual surface and Phase-7 ledger wiring -/

/-- Phase-6 entry facts sufficient for the deterministic Lemma-7.3 snapshot.
The five-percent field is intentionally separate from the existing one-class
`ReserveSampleGood`, which the obstruction above shows is insufficient. -/
structure Phase6SnapshotEntry
    (n M : ℕ) (sigma : Sign) (l : ℕ) (hl : l + 2 < L + 1)
    (c : Config (AgentState L K)) : Prop where
  paper : PaperRegime.Theorem62Paper
    (L := L) (K := K) sigma l hl n c
  mainCount_eq : RoleSplitConcentration.mainCount (L := L) (K := K) c = M
  dangerous_five_percent :
    1000 * dangerousReserveCount (L := L) (K := K) l c ≤ 50 * M

/-- Honest remaining seam obligations after the Phase-6 work-prefix ledger.

There is deliberately no bare `block_transfer`: it is false once two Mains
interact during the mixed 6/7 epidemic.  The Phase-3 post and the three real
reachability segments are carried explicitly; the sharp `0.064 M` debt cap is
then a theorem, not a seam assumption. -/
structure Phase6To7SnapshotRoute
    (n M : ℕ) (sigma : Sign) (l : ℕ)
    (c₀ c7 : Config (AgentState L K)) : Prop where
  post_and_reachable :
    ∃ (n3 : ℕ) (g₀ : ℝ) (sigmaMajority : Sign)
        (c3 c4 c6 : Config (AgentState L K)),
      Phase3Post3.Post3
          (L := L) (K := K) n3 l (M : ℝ) sigmaMajority g₀ c3 ∧
        Phase3Post3.minoritySignOfMajority sigmaMajority = sigma ∧
        Phase5To6FuelProducer.ReachableThroughPhase34
          (L := L) (K := K) c3 c4 ∧
        Phase5To6FuelProducer.ReachableThroughPhase45
          (L := L) (K := K) c4 c₀ ∧
        Phase6WorkReachable (L := L) (K := K) n c₀ c6 ∧
        Phase6To7Reachable (L := L) (K := K) c6 c7
  win : PhaseOnlyWindows.Phase7Win (L := L) (K := K) n c7
  cleared : BandClear (L := L) (K := K) sigma l c7

/-- The new snapshot ledger instantiates the Phase-7 seam interface from the
actual deterministic routes and the separately produced dangerous-sample
upper tail. -/
theorem phase6To7LedgerTransfer_of_snapshot
    (n M : ℕ) (sigma : Sign) (l : ℕ) (hl : l + 2 < L + 1) :
    Phase6To7LedgerTransfer
      (L := L) (K := K)
      (Phase6SnapshotEntry (L := L) (K := K) n M sigma l hl)
      (Phase6To7SnapshotRoute (L := L) (K := K) n M sigma l)
      n sigma l (4 * M / 5) := by
  constructor
  · intro c₀ c7 _hentry hseam
    exact hseam.win
  · intro c₀ c7 _hentry hseam
    exact hseam.cleared
  · intro c₀ c7 hentry hseam
    obtain ⟨n3, g₀, sigmaMajority, c3, c4, c6,
      hpost, hsigma, h34, h45, hwork, hreach⟩ := hseam.post_and_reachable
    have hdebtMajority := minorityDebt_64_of_post3_routes
      (L := L) (K := K) n3 n l M sigmaMajority g₀
      hpost h34 h45 hwork
    have hdebt :
        1000 * minorityDebt (L := L) (K := K) sigma l c6 ≤ 64 * M := by
      simpa [hsigma] using hdebtMajority
    have hfuel6 := phase6_endpoint_fuelLedger_of_paper
      (L := L) (K := K) n M sigma l hl hentry.paper hentry.mainCount_eq
      hwork hentry.dangerous_five_percent hdebt
    have hfuel7 := phase6To7FuelLedger_of_reachable
      (L := L) (K := K) sigma l (4 * M / 5) hreach hfuel6
    exact majorityBlockLedger_of_phase6To7FuelLedger
      sigma l (4 * M / 5) c7 hfuel7

#print axioms doSplit_block_danger_pair
#print axioms minorityDebt_eq_of_reachableThroughPhase45
#print axioms minorityDebt_cast_le_scaled_signedMass
#print axioms minorityDebt_64_of_minorityMass_bound_after_phase34
#print axioms Phase6Transition_block_danger_pair
#print axioms Transition_block_danger_pair
#print axioms Transition_block_debt_danger_pair_of_phase_six_or_seven
#print axioms phase6To7FuelLedger_stepOrSelf
#print axioms phase6To7FuelLedger_of_reachable
#print axioms block_danger_stepOrSelf
#print axioms block_danger_of_phase6WorkReachable
#print axioms minorityDebt_of_phase6WorkReachable
#print axioms minorityDebt_64_of_post3_routes
#print axioms dangerousReserve_cap_five_percent
#print axioms phase6_endpoint_majorityBlock_870
#print axioms majorityConfined3_le_majorityBlockCount
#print axioms theorem62Paper_majorityBlock_920
#print axioms phase6_endpoint_majorityBlock_870_of_paper
#print axioms OneClassPostObstruction.phase5Post_not_enough_for_five_percent
#print axioms BareBlockTransferObstruction.bare_block_transfer_fails
#print axioms phase6To7LedgerTransfer_of_snapshot

end Phase6BlockSnapshot
end Ripple.PopulationProtocol.ExactMajority
