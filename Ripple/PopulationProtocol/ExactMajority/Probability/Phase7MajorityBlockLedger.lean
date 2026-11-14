/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Phase-7 majority-block depletion ledger

The fixed majority block at indices `l,l+1,l+2` is not itself invariant:
`cancelSplit` may consume one of its agents.  The paper's Lemma 7.4 pays every
such loss from the bounded minority mass at indices through `l+4`.

This file records that payment as a subtraction-free integer ledger.  A
minority Main at index `j <= l+4` carries debt `2^(l+4-j)`.  Whenever the
majority-block count drops, the debt drops by at least as much.  Hence

  `G + minorityDebt <= majorityBlockCount`

is preserved by Phase 7 and exposes the permanent block floor `G`.  This is
the dynamic replacement for the non-closed static `phase7BandPool` gate.
-/

import Ripple.PopulationProtocol.ExactMajority.Probability.DriftHorizon
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase7BandDropSum
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase7BandStages

namespace Ripple.PopulationProtocol.ExactMajority
namespace Phase7MajorityBlockLedger

open Phase7BandDefs
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

/-- One unit precisely when the agent belongs to the paper's fixed majority
block at indices `l,l+1,l+2`. -/
def majorityBlockUnit (sigma : Sign) (l : ℕ) (a : AgentState L K) : ℕ :=
  if a ∈ majorityBand3 (L := L) (K := K) sigma l then 1 else 0

/-- Future majority-block losses chargeable to one minority agent.

The cutoff `l+4` is the one used in Lemma 7.4.  The weights are the dyadic
mass normalized to the mass of an agent at index `l+4`. -/
def minorityDebtUnit (sigma : Sign) (l : ℕ) (a : AgentState L K) : ℕ :=
  if a.role = Role.main then
    match a.bias with
    | Bias.zero => 0
    | Bias.dyadic s j =>
        if s = sigma ∧ j.val ≤ l + 4 then 2 ^ (l + 4 - j.val) else 0
  else
    0

@[simp] theorem majorityBlockUnit_main_dyadic
    (sigma s : Sign) (l : ℕ) (j : Fin (L + 1)) (a : AgentState L K)
    (hm : a.role = Role.main) (hb : a.bias = Bias.dyadic s j) :
    majorityBlockUnit (L := L) (K := K) sigma l a =
      if s ≠ sigma ∧ l ≤ j.val ∧ j.val < l + 3 then 1 else 0 := by
  have hmem :
      a ∈ majorityBand3 (L := L) (K := K) sigma l ↔
        s ≠ sigma ∧ l ≤ j.val ∧ j.val < l + 3 := by
    rw [majorityBand3, Finset.mem_filter]
    constructor
    · rintro ⟨_, _haMain, ss, k, hss, hbias, hkl, hktop⟩
      rw [hb] at hbias
      injection hbias with hsign hindex
      subst hsign
      subst hindex
      exact ⟨hss, hkl, hktop⟩
    · rintro ⟨hss, hkl, hktop⟩
      exact ⟨Finset.mem_univ _, hm, s, j, hss, hb, hkl, hktop⟩
  unfold majorityBlockUnit
  by_cases h : s ≠ sigma ∧ l ≤ j.val ∧ j.val < l + 3
  · rw [if_pos (hmem.mpr h), if_pos h]
  · rw [if_neg (fun ha => h (hmem.mp ha)), if_neg h]

@[simp] theorem majorityBlockUnit_main_zero
    (sigma : Sign) (l : ℕ) (a : AgentState L K)
    (_hm : a.role = Role.main) (hb : a.bias = Bias.zero) :
    majorityBlockUnit (L := L) (K := K) sigma l a = 0 := by
  unfold majorityBlockUnit
  rw [if_neg]
  intro ha
  rw [majorityBand3, Finset.mem_filter] at ha
  obtain ⟨_, _, ss, j, _, hbias, _⟩ := ha
  rw [hb] at hbias
  contradiction

@[simp] theorem majorityBlockUnit_of_role_ne_main
    (sigma : Sign) (l : ℕ) (a : AgentState L K)
    (hm : a.role ≠ Role.main) :
    majorityBlockUnit (L := L) (K := K) sigma l a = 0 := by
  unfold majorityBlockUnit
  rw [if_neg]
  intro ha
  rw [majorityBand3, Finset.mem_filter] at ha
  exact hm ha.2.1

@[simp] theorem minorityDebtUnit_main_dyadic
    (sigma s : Sign) (l : ℕ) (j : Fin (L + 1)) (a : AgentState L K)
    (hm : a.role = Role.main) (hb : a.bias = Bias.dyadic s j) :
    minorityDebtUnit (L := L) (K := K) sigma l a =
      if s = sigma ∧ j.val ≤ l + 4 then 2 ^ (l + 4 - j.val) else 0 := by
  simp [minorityDebtUnit, hm, hb]

@[simp] theorem minorityDebtUnit_main_zero
    (sigma : Sign) (l : ℕ) (a : AgentState L K)
    (hm : a.role = Role.main) (hb : a.bias = Bias.zero) :
    minorityDebtUnit (L := L) (K := K) sigma l a = 0 := by
  simp [minorityDebtUnit, hm, hb]

@[simp] theorem minorityDebtUnit_of_role_ne_main
    (sigma : Sign) (l : ℕ) (a : AgentState L K)
    (hm : a.role ≠ Role.main) :
    minorityDebtUnit (L := L) (K := K) sigma l a = 0 := by
  simp [minorityDebtUnit, hm]

/-- Count of majority Mains in the fixed three-level block. -/
def majorityBlockCount (sigma : Sign) (l : ℕ)
    (c : Config (AgentState L K)) : ℕ :=
  Multiset.countP
    (fun a => a ∈ majorityBand3 (L := L) (K := K) sigma l) c

/-- Total normalized minority debt through index `l+4`. -/
def minorityDebt (sigma : Sign) (l : ℕ)
    (c : Config (AgentState L K)) : ℕ :=
  (c.map (minorityDebtUnit (L := L) (K := K) sigma l)).sum

/-- `G` majority-block agents remain even after paying all future minority
depletion debt. -/
def MajorityBlockLedger (sigma : Sign) (l G : ℕ)
    (c : Config (AgentState L K)) : Prop :=
  G + minorityDebt (L := L) (K := K) sigma l c ≤
    majorityBlockCount (L := L) (K := K) sigma l c

@[simp] theorem majorityBlockCount_add (sigma : Sign) (l : ℕ)
    (a b : Config (AgentState L K)) :
    majorityBlockCount (L := L) (K := K) sigma l (a + b) =
      majorityBlockCount (L := L) (K := K) sigma l a +
        majorityBlockCount (L := L) (K := K) sigma l b := by
  simp [majorityBlockCount, Multiset.countP_add]

@[simp] theorem minorityDebt_add (sigma : Sign) (l : ℕ)
    (a b : Config (AgentState L K)) :
    minorityDebt (L := L) (K := K) sigma l (a + b) =
      minorityDebt (L := L) (K := K) sigma l a +
        minorityDebt (L := L) (K := K) sigma l b := by
  simp [minorityDebt]

@[simp] theorem majorityBlockCount_pair (sigma : Sign) (l : ℕ)
    (a b : AgentState L K) :
    majorityBlockCount (L := L) (K := K) sigma l
        ({a, b} : Config (AgentState L K)) =
      majorityBlockUnit (L := L) (K := K) sigma l a +
        majorityBlockUnit (L := L) (K := K) sigma l b := by
  change Multiset.countP
      (fun x => x ∈ majorityBand3 (L := L) (K := K) sigma l)
        (a ::ₘ b ::ₘ 0) = _
  rw [Multiset.countP_cons, Multiset.countP_cons, Multiset.countP_zero]
  simp [majorityBlockUnit, add_comm]

@[simp] theorem minorityDebt_pair (sigma : Sign) (l : ℕ)
    (a b : AgentState L K) :
    minorityDebt (L := L) (K := K) sigma l
        ({a, b} : Config (AgentState L K)) =
      minorityDebtUnit (L := L) (K := K) sigma l a +
        minorityDebtUnit (L := L) (K := K) sigma l b := by
  simp [minorityDebt]

/-- The multiset observable agrees with the public fixed-block finset count. -/
theorem majorityBlockCount_eq_sum_count (sigma : Sign) (l : ℕ)
    (c : Config (AgentState L K)) :
    majorityBlockCount (L := L) (K := K) sigma l c =
      (majorityBand3 (L := L) (K := K) sigma l).sum c.count := by
  classical
  unfold majorityBlockCount
  rw [Phase6Convergence.countP_eq_sum_count6]
  congr 1
  ext a
  simp

/-- A block ledger exposes the permanent majority-block floor. -/
theorem majorityBlockFloor_of_ledger
    (sigma : Sign) (l G : ℕ) (c : Config (AgentState L K))
    (h : MajorityBlockLedger (L := L) (K := K) sigma l G c) :
    MajorityBandFloor (L := L) (K := K) sigma l G c := by
  unfold MajorityBandFloor
  rw [← majorityBlockCount_eq_sum_count]
  unfold MajorityBlockLedger at h
  omega

/-- Therefore the dynamic ledger supplies every distance-two stage pool. -/
theorem phase7BandPool_of_ledger
    (sigma : Sign) (l G : ℕ) (c : Config (AgentState L K))
    (h : MajorityBlockLedger (L := L) (K := K) sigma l G c) :
    phase7BandPool (L := L) (K := K) sigma l G c :=
  phase7BandPool_of_majorityBandFloor sigma l G c
    (majorityBlockFloor_of_ledger sigma l G c h)

/-! ## Deterministic entry arithmetic -/

/-- Pure deterministic constructor: a cap on all future minority depletion
and a block floor after reserving that cap produce the ledger.  Establishing
the two inequalities at the random Phase-6/7 seam is a separate probabilistic
snapshot obligation. -/
theorem majorityBlockLedger_of_caps
    (sigma : Sign) (l G Dcap : ℕ) (c : Config (AgentState L K))
    (hdebt : minorityDebt (L := L) (K := K) sigma l c ≤ Dcap)
    (hblock : G + Dcap ≤ majorityBlockCount (L := L) (K := K) sigma l c) :
    MajorityBlockLedger (L := L) (K := K) sigma l G c := by
  unfold MajorityBlockLedger
  omega

/-- Integer-safe Lemmas 7.3/7.4 arithmetic.

`870 M / 1000` is the Phase-6 endpoint block floor and `64 M / 1000`
is the normalized minority-depletion budget through `l+4`.  Their difference
supports the conservative permanent floor `⌊4M/5⌋`.  This theorem is only
the deterministic implication between snapshot fields; it does not assert
that the probabilistic Phase-6/7 seam has produced those fields. -/
theorem majorityBlockLedger_of_paper_scaled_bounds
    (sigma : Sign) (l M : ℕ) (c : Config (AgentState L K))
    (hblock : 870 * M ≤
      1000 * majorityBlockCount (L := L) (K := K) sigma l c)
    (hdebt : 1000 * minorityDebt (L := L) (K := K) sigma l c ≤ 64 * M) :
    MajorityBlockLedger (L := L) (K := K) sigma l (4 * M / 5) c := by
  have hfloor := Nat.div_mul_le_self (4 * M) 5
  unfold MajorityBlockLedger
  omega

/-- Genuine two-configuration Phase-6/7 seam interface for the new gate.
The probabilistic producer must establish `to_ledger` at the endpoint; neither
the source postcondition nor a same-configuration phase rewrite can supply it. -/
structure Phase6To7LedgerTransfer
    (Post6 : Config (AgentState L K) → Prop)
    (Seam : Config (AgentState L K) → Config (AgentState L K) → Prop)
    (n : ℕ) (sigma : Sign) (l G : ℕ) : Prop where
  to_win :
    ∀ c6 c7, Post6 c6 → Seam c6 c7 →
      PhaseOnlyWindows.Phase7Win (L := L) (K := K) n c7
  to_cleared :
    ∀ c6 c7, Post6 c6 → Seam c6 c7 →
      BandClear (L := L) (K := K) sigma l c7
  to_ledger :
    ∀ c6 c7, Post6 c6 → Seam c6 c7 →
      MajorityBlockLedger (L := L) (K := K) sigma l G c7

/-! ## Per-pair depletion accounting -/

private theorem pow_sub_succ_drop (x j : ℕ) (h : j + 1 ≤ x) :
    2 ^ (x - (j + 1)) + 1 ≤ 2 ^ (x - j) := by
  have he : x - j = (x - (j + 1)) + 1 := by omega
  rw [he, pow_succ]
  have hp : 1 ≤ 2 ^ (x - (j + 1)) :=
    Nat.one_le_pow (x - (j + 1)) 2 (by omega)
  omega

private theorem pow_sub_two_succ_drop (x j : ℕ) (h : j + 2 ≤ x) :
    2 ^ (x - (j + 1)) + 2 ^ (x - (j + 2)) + 1 ≤
      2 ^ (x - j) := by
  have he0 : x - j = (x - (j + 2)) + 2 := by omega
  have he1 : x - (j + 1) = (x - (j + 2)) + 1 := by omega
  rw [he0, he1, pow_succ, pow_succ]
  have hp : 1 ≤ 2 ^ (x - (j + 2)) :=
    Nat.one_le_pow (x - (j + 2)) 2 (by omega)
  omega

/-- Pure fixed-block indicator, separated from `AgentState` so that the five
`cancelSplit` index branches reduce to ordinary natural-number arithmetic. -/
private def blockWeight (l j : ℕ) : ℕ :=
  if l ≤ j ∧ j < l + 3 then 1 else 0

/-- Pure normalized minority-debt weight through the paper's `l+4` cutoff. -/
private def debtWeight (l j : ℕ) : ℕ :=
  if j ≤ l + 4 then 2 ^ (l + 4 - j) else 0

private theorem blockWeight_le_debtWeight (l j : ℕ) :
    blockWeight l j ≤ debtWeight l j := by
  by_cases hb : l ≤ j ∧ j < l + 3
  · have hd : j ≤ l + 4 := by omega
    rw [blockWeight, if_pos hb, debtWeight, if_pos hd]
    exact Nat.one_le_two_pow
  · rw [blockWeight, if_neg hb]
    exact Nat.zero_le _

/-- Gap-one branch when the shallower sign is the minority sign. -/
private theorem gapOne_minority_payment (l i : ℕ) :
    blockWeight l (i + 1) + debtWeight l (i + 1) ≤ debtWeight l i := by
  by_cases hnext : i + 1 ≤ l + 4
  · have hi : i ≤ l + 4 := by omega
    have hb : blockWeight l (i + 1) ≤ 1 := by
      unfold blockWeight
      split <;> omega
    have hp := pow_sub_succ_drop (l + 4) i hnext
    rw [debtWeight, if_pos hnext, debtWeight, if_pos hi]
    omega
  · have hb : blockWeight l (i + 1) = 0 := by
      rw [blockWeight, if_neg]
      omega
    have hd : debtWeight l (i + 1) = 0 := by
      rw [debtWeight, if_neg hnext]
    rw [hb, hd]
    exact Nat.zero_le _

/-- Gap-one branch when the shallower sign is the majority sign. -/
private theorem gapOne_majority_payment (l i : ℕ) :
    blockWeight l i ≤ blockWeight l (i + 1) + debtWeight l (i + 1) := by
  by_cases hb : l ≤ i ∧ i < l + 3
  · have hd : i + 1 ≤ l + 4 := by omega
    have hp : 1 ≤ 2 ^ (l + 4 - (i + 1)) := Nat.one_le_two_pow
    rw [blockWeight, if_pos hb, debtWeight, if_pos hd]
    omega
  · rw [blockWeight, if_neg hb]
    exact Nat.zero_le _

/-- Gap-two branch when the shallower sign is the minority sign. -/
private theorem gapTwo_minority_payment (l i : ℕ) :
    blockWeight l (i + 2) + debtWeight l (i + 1) + debtWeight l (i + 2) ≤
      debtWeight l i := by
  by_cases htwo : i + 2 ≤ l + 4
  · have hone : i + 1 ≤ l + 4 := by omega
    have hi : i ≤ l + 4 := by omega
    have hb : blockWeight l (i + 2) ≤ 1 := by
      unfold blockWeight
      split <;> omega
    have hp := pow_sub_two_succ_drop (l + 4) i htwo
    rw [debtWeight, if_pos hone, debtWeight, if_pos htwo,
      debtWeight, if_pos hi]
    omega
  · have hb : blockWeight l (i + 2) = 0 := by
      rw [blockWeight, if_neg]
      omega
    have hdtwo : debtWeight l (i + 2) = 0 := by
      rw [debtWeight, if_neg htwo]
    rw [hb, hdtwo, zero_add, add_zero]
    by_cases hone : i + 1 ≤ l + 4
    · have hi : i ≤ l + 4 := by omega
      have hp := pow_sub_succ_drop (l + 4) i hone
      rw [debtWeight, if_pos hone, debtWeight, if_pos hi]
      omega
    · have hdone : debtWeight l (i + 1) = 0 := by
        rw [debtWeight, if_neg hone]
      rw [hdone]
      exact Nat.zero_le _

/-- Gap-two branch when the shallower sign is the majority sign. -/
private theorem gapTwo_majority_payment (l i : ℕ) :
    blockWeight l i ≤
      blockWeight l (i + 1) + blockWeight l (i + 2) + debtWeight l (i + 2) := by
  by_cases hb : l ≤ i ∧ i < l + 3
  · have hd : i + 2 ≤ l + 4 := by omega
    have hp : 1 ≤ 2 ^ (l + 4 - (i + 2)) := Nat.one_le_two_pow
    rw [blockWeight, if_pos hb, debtWeight, if_pos hd]
    omega
  · rw [blockWeight, if_neg hb]
    exact Nat.zero_le _

private theorem gapOne_minority_payment_of_eq (l i j : ℕ)
    (h : i + 1 = j) :
    blockWeight l j + debtWeight l j ≤ debtWeight l i := by
  subst j
  exact gapOne_minority_payment l i

private theorem gapOne_majority_payment_of_eq (l i j : ℕ)
    (h : i + 1 = j) :
    blockWeight l i ≤ blockWeight l j + debtWeight l j := by
  subst j
  exact gapOne_majority_payment l i

private theorem gapTwo_minority_payment_of_eq (l i j : ℕ)
    (h : i + 2 = j) :
    blockWeight l j + debtWeight l (i + 1) + debtWeight l j ≤ debtWeight l i := by
  subst j
  exact gapTwo_minority_payment l i

private theorem gapTwo_majority_payment_of_eq (l i j : ℕ)
    (h : i + 2 = j) :
    blockWeight l i ≤
      blockWeight l (i + 1) + blockWeight l j + debtWeight l j := by
  subst j
  exact gapTwo_majority_payment l i

/-- Fixed-block weight of a Main agent's bias: `blockWeight` at its index when the sign is
the majority (non-`sigma`) sign. -/
private def biasBlock (sigma : Sign) (l : ℕ) : Bias L → ℕ
  | .zero => 0
  | .dyadic s j => if s ≠ sigma then blockWeight l j.val else 0

/-- Normalized minority debt of a Main agent's bias: `debtWeight` at its index when the
sign is the minority sign `sigma`. -/
private def biasDebt (sigma : Sign) (l : ℕ) : Bias L → ℕ
  | .zero => 0
  | .dyadic s j => if s = sigma then debtWeight l j.val else 0

private theorem majorityBlockUnit_main_eq (sigma : Sign) (l : ℕ) (a : AgentState L K)
    (hm : a.role = Role.main) :
    majorityBlockUnit (L := L) (K := K) sigma l a = biasBlock sigma l a.bias := by
  cases hb : a.bias with
  | zero => simp [majorityBlockUnit_main_zero sigma l a hm hb, biasBlock]
  | dyadic s j =>
      rw [majorityBlockUnit_main_dyadic sigma s l j a hm hb]
      by_cases hs : s = sigma <;> simp [biasBlock, blockWeight, hs]

private theorem minorityDebtUnit_main_eq (sigma : Sign) (l : ℕ) (a : AgentState L K)
    (hm : a.role = Role.main) :
    minorityDebtUnit (L := L) (K := K) sigma l a = biasDebt sigma l a.bias := by
  cases hb : a.bias with
  | zero => simp [minorityDebtUnit, hm, hb, biasDebt]
  | dyadic s j =>
      by_cases hs : s = sigma <;> simp [minorityDebtUnit, hm, hb, biasDebt, debtWeight, hs]

/-- The ledger inequality for `cancelSplit` at the level of the two biases: each of the five
cancel/split branches is one of the gap payments above, at the shallower index. -/
private theorem cancelSplit_bias_block_debt (sigma : Sign) (l : ℕ) (s t : AgentState L K) :
    biasBlock sigma l s.bias + biasBlock sigma l t.bias +
        (biasDebt sigma l (cancelSplit L K s t).1.bias +
          biasDebt sigma l (cancelSplit L K s t).2.bias) ≤
      biasBlock sigma l (cancelSplit L K s t).1.bias +
          biasBlock sigma l (cancelSplit L K s t).2.bias +
        (biasDebt sigma l s.bias + biasDebt sigma l t.bias) := by
  cases hsb : s.bias with
  | zero => simp [cancelSplit, hsb]
  | dyadic ss i =>
      cases htb : t.bias with
      | zero => simp [cancelSplit, hsb, htb]
      | dyadic tt j =>
          have bi := blockWeight_le_debtWeight l i.val
          have bj := blockWeight_le_debtWeight l j.val
          have m1i := gapOne_minority_payment l i.val
          have m1j := gapOne_minority_payment l j.val
          have a1i := gapOne_majority_payment l i.val
          have a1j := gapOne_majority_payment l j.val
          have m2i := gapTwo_minority_payment l i.val
          have m2j := gapTwo_minority_payment l j.val
          have a2i := gapTwo_majority_payment l i.val
          have a2j := gapTwo_majority_payment l j.val
          simp only [cancelSplit, hsb, htb]
          -- five cancel/split branches and the two identity branches; in each, the
          -- signs are decided by cases and the index relation is rewritten by `simp_all`
          split_ifs <;>
            cases ss <;> cases tt <;> cases sigma <;> simp_all [biasBlock, biasDebt] <;> omega

/-- On a Main/Main pair, `cancelSplit` can lose fixed-block agents only by
paying at least the same amount of normalized minority debt. -/
theorem cancelSplit_block_debt_pair
    (sigma : Sign) (l : ℕ) (s t : AgentState L K)
    (hsM : s.role = Role.main) (htM : t.role = Role.main) :
    majorityBlockUnit (L := L) (K := K) sigma l s +
          majorityBlockUnit (L := L) (K := K) sigma l t +
        (minorityDebtUnit (L := L) (K := K) sigma l (cancelSplit L K s t).1 +
          minorityDebtUnit (L := L) (K := K) sigma l (cancelSplit L K s t).2) ≤
      majorityBlockUnit (L := L) (K := K) sigma l (cancelSplit L K s t).1 +
          majorityBlockUnit (L := L) (K := K) sigma l (cancelSplit L K s t).2 +
        (minorityDebtUnit (L := L) (K := K) sigma l s +
          minorityDebtUnit (L := L) (K := K) sigma l t) := by
  have hs' : (cancelSplit L K s t).1.role = Role.main := by
    rw [cancelSplit_role_fst]; exact hsM
  have ht' : (cancelSplit L K s t).2.role = Role.main := by
    rw [cancelSplit_role_snd]; exact htM
  rw [majorityBlockUnit_main_eq sigma l s hsM, majorityBlockUnit_main_eq sigma l t htM,
    majorityBlockUnit_main_eq sigma l _ hs', majorityBlockUnit_main_eq sigma l _ ht',
    minorityDebtUnit_main_eq sigma l s hsM, minorityDebtUnit_main_eq sigma l t htM,
    minorityDebtUnit_main_eq sigma l _ hs', minorityDebtUnit_main_eq sigma l _ ht']
  exact cancelSplit_bias_block_debt sigma l s t

/-- The same depletion inequality for the actual full-protocol transition on
an exact Phase-7 pair.  Mixed-role interactions cannot alter any Main state;
Clock bookkeeping stays outside both ledger observables. -/
theorem Transition_block_debt_pair
    (sigma : Sign) (l : ℕ) (s t : AgentState L K)
    (hs7 : s.phase.val = 7) (ht7 : t.phase.val = 7) :
    majorityBlockUnit (L := L) (K := K) sigma l s +
          majorityBlockUnit (L := L) (K := K) sigma l t +
        (minorityDebtUnit (L := L) (K := K) sigma l (Transition L K s t).1 +
          minorityDebtUnit (L := L) (K := K) sigma l (Transition L K s t).2) ≤
      majorityBlockUnit (L := L) (K := K) sigma l (Transition L K s t).1 +
          majorityBlockUnit (L := L) (K := K) sigma l (Transition L K s t).2 +
        (minorityDebtUnit (L := L) (K := K) sigma l s +
          minorityDebtUnit (L := L) (K := K) sigma l t) := by
  classical
  by_cases hboth : s.role = Role.main ∧ t.role = Role.main
  · rw [Phase7Convergence.Transition_eq_cancelSplit_of_phase7_main
      (L := L) (K := K) s t hs7 ht7 hboth.1 hboth.2]
    exact cancelSplit_block_debt_pair sigma l s t hboth.1 hboth.2
  · obtain ⟨hr1, hr2⟩ :=
      PhaseOnlyWindows.Transition_role_phase7 (L := L) (K := K) s t hs7 ht7
    have hmain_fst : s.role = Role.main → (Transition L K s t).1 = s := by
      intro hsM
      have hepi := Phase7Convergence.phaseEpidemicUpdate_eq_self_of_phase7
        (L := L) (K := K) s t hs7 ht7
      have hsp : s.phase = ⟨7, by decide⟩ := Fin.ext hs7
      have hp7 : (Phase7Transition L K s t).1 = s := by
        unfold Phase7Transition
        simp only [if_neg hboth]
        rw [if_neg (show s.role ≠ Role.clock by rw [hsM]; decide)]
      unfold Transition
      rw [hepi]
      simp only [hsp]
      rw [finishPhase10Entry_eq_self_of_after_ne_10 (L := L) (K := K) s _
        (by rw [hp7, hs7]; decide)]
      exact hp7
    have hmain_snd : t.role = Role.main → (Transition L K s t).2 = t := by
      intro htM
      have hepi := Phase7Convergence.phaseEpidemicUpdate_eq_self_of_phase7
        (L := L) (K := K) s t hs7 ht7
      have hsp : s.phase = ⟨7, by decide⟩ := Fin.ext hs7
      have hp7 : (Phase7Transition L K s t).2 = t := by
        unfold Phase7Transition
        simp only [if_neg hboth]
        rw [if_neg (show t.role ≠ Role.clock by rw [htM]; decide)]
      unfold Transition
      rw [hepi]
      simp only [hsp]
      rw [finishPhase10Entry_eq_self_of_after_ne_10 (L := L) (K := K) t _
        (by rw [hp7, ht7]; decide)]
      exact hp7
    by_cases hsM : s.role = Role.main
    · rw [hmain_fst hsM]
      by_cases htM : t.role = Role.main
      · exact (hboth ⟨hsM, htM⟩).elim
      · have htOut : (Transition L K s t).2.role ≠ Role.main := by
          rw [hr2]
          exact htM
        simp [minorityDebtUnit_of_role_ne_main sigma l t htM,
          minorityDebtUnit_of_role_ne_main sigma l (Transition L K s t).2 htOut,
          majorityBlockUnit_of_role_ne_main sigma l t htM,
          majorityBlockUnit_of_role_ne_main sigma l (Transition L K s t).2 htOut]
    · have hsOut : (Transition L K s t).1.role ≠ Role.main := by
        rw [hr1]
        exact hsM
      by_cases htM : t.role = Role.main
      · rw [hmain_snd htM]
        simp [minorityDebtUnit_of_role_ne_main sigma l s hsM,
          minorityDebtUnit_of_role_ne_main sigma l (Transition L K s t).1 hsOut,
          majorityBlockUnit_of_role_ne_main sigma l s hsM,
          majorityBlockUnit_of_role_ne_main sigma l (Transition L K s t).1 hsOut]
      · have htOut : (Transition L K s t).2.role ≠ Role.main := by
          rw [hr2]
          exact htM
        simp [minorityDebtUnit_of_role_ne_main sigma l s hsM,
          minorityDebtUnit_of_role_ne_main sigma l t htM,
          minorityDebtUnit_of_role_ne_main sigma l (Transition L K s t).1 hsOut,
          minorityDebtUnit_of_role_ne_main sigma l (Transition L K s t).2 htOut,
          majorityBlockUnit_of_role_ne_main sigma l s hsM,
          majorityBlockUnit_of_role_ne_main sigma l t htM,
          majorityBlockUnit_of_role_ne_main sigma l (Transition L K s t).1 hsOut,
          majorityBlockUnit_of_role_ne_main sigma l (Transition L K s t).2 htOut]

private theorem mem_of_app_left7Ledger {c : Config (AgentState L K)}
    {r₁ r₂ : AgentState L K} (happ : Protocol.Applicable c r₁ r₂) : r₁ ∈ c :=
  Multiset.mem_of_le
    (show ({r₁, r₂} : Multiset (AgentState L K)) ≤ c from happ) (by simp)

private theorem mem_of_app_right7Ledger {c : Config (AgentState L K)}
    {r₁ r₂ : AgentState L K} (happ : Protocol.Applicable c r₁ r₂) : r₂ ∈ c :=
  Multiset.mem_of_le
    (show ({r₁, r₂} : Multiset (AgentState L K)) ≤ c from happ) (by simp)

/-- The majority-block ledger is preserved by every scheduled interaction
whose source configuration lies in the exact Phase-7 window. -/
theorem majorityBlockLedger_stepOrSelf
    (sigma : Sign) (l G n : ℕ) (c : Config (AgentState L K))
    (hgenuine : PhaseOnlyWindows.Phase7Win (L := L) (K := K) n c)
    (hledger : MajorityBlockLedger (L := L) (K := K) sigma l G c)
    (r₁ r₂ : AgentState L K) :
    MajorityBlockLedger (L := L) (K := K) sigma l G
      (Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂) := by
  by_cases happ : Protocol.Applicable c r₁ r₂
  · have hm1 := mem_of_app_left7Ledger happ
    have hm2 := mem_of_app_right7Ledger happ
    have h17 : r₁.phase.val = 7 := hgenuine.2 r₁ hm1
    have h27 : r₂.phase.val = 7 := hgenuine.2 r₂ hm2
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
                Config (AgentState L K)) ≤
          majorityBlockCount (L := L) (K := K) sigma l
              ({(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2} :
                Config (AgentState L K)) +
            minorityDebt (L := L) (K := K) sigma l
              ({r₁, r₂} : Config (AgentState L K)) := by
      rw [majorityBlockCount_pair, majorityBlockCount_pair,
        minorityDebt_pair, minorityDebt_pair]
      exact Transition_block_debt_pair sigma l r₁ r₂ h17 h27
    have hledger' :
        G + (minorityDebt (L := L) (K := K) sigma l (c - {r₁, r₂}) +
            minorityDebt (L := L) (K := K) sigma l
              ({r₁, r₂} : Config (AgentState L K))) ≤
          majorityBlockCount (L := L) (K := K) sigma l (c - {r₁, r₂}) +
            majorityBlockCount (L := L) (K := K) sigma l
              ({r₁, r₂} : Config (AgentState L K)) := by
      rw [← minorityDebt_add, ← majorityBlockCount_add, ← hcsplit]
      exact hledger
    unfold MajorityBlockLedger
    rw [hc', minorityDebt_add, majorityBlockCount_add]
    omega
  · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]
    exact hledger

/-! ## The genuine stage gate and its only genuine escape -/

/-- The deterministic part of a Phase-7 stage gate.  Unlike the old static
pool field, both fields are closed during a genuine Phase-7 step. -/
structure Phase7LedgerCore
    (sigma : Sign) (l G : ℕ) (j : Fin (L + 1))
    (c : Config (AgentState L K)) : Prop where
  cleared : BandClear (L := L) (K := K) sigma j.val c
  ledger : MajorityBlockLedger (L := L) (K := K) sigma l G c

/-- A stage gate whose resource premise is the dynamic depletion ledger. -/
structure Phase7LedgerStageReady
    (n : ℕ) (sigma : Sign) (l G : ℕ) (j : Fin (L + 1))
    (c : Config (AgentState L K)) : Prop where
  win : PhaseOnlyWindows.Phase7Win (L := L) (K := K) n c
  core : Phase7LedgerCore (L := L) (K := K) sigma l G j c

/-- At any fixed configuration, the dynamic gate supplies exactly the old
consumer-facing eliminator pool.  The difference is that its producer is now
closed under Phase 7. -/
theorem Phase7LedgerStageReady.toStatic
    {n : ℕ} {sigma : Sign} {l G : ℕ} {j : Fin (L + 1)}
    {c : Config (AgentState L K)}
    (h : Phase7LedgerStageReady (L := L) (K := K) n sigma l G j c) :
    Phase7StageReady (L := L) (K := K) n sigma l G j c :=
  ⟨h.win, h.core.cleared,
    phase7BandPool_of_ledger sigma l G c h.core.ledger⟩

/-- The ledger seam payload constructs the first naturally truncated dynamic
stage gate. -/
theorem firstLedgerStageReady_of_phase6To7LedgerTransfer
    {Post6 : Config (AgentState L K) → Prop}
    {Seam : Config (AgentState L K) → Config (AgentState L K) → Prop}
    {n l G : ℕ} {sigma : Sign} (hlL : l ≤ L)
    (h : Phase6To7LedgerTransfer
      (L := L) (K := K) Post6 Seam n sigma l G)
    {c6 c7 : Config (AgentState L K)}
    (hc6 : Post6 c6) (hseam : Seam c6 c7) :
    Phase7LedgerStageReady (L := L) (K := K) n sigma l G
      (Phase7BandStages.phase7StageIndex (L := L) l hlL
        ⟨0, Phase7BandStages.phase7StageCount_pos (L := L) l hlL⟩) c7 := by
  exact
    ⟨h.to_win c6 c7 hc6 hseam,
      ⟨by simpa using h.to_cleared c6 c7 hc6 hseam,
       h.to_ledger c6 c7 hc6 hseam⟩⟩

/-- The deterministic core survives one scheduled step. -/
theorem phase7LedgerCore_stepOrSelf
    (n : ℕ) (sigma : Sign) (l G : ℕ) (j : Fin (L + 1))
    (c : Config (AgentState L K))
    (hgenuine : PhaseOnlyWindows.Phase7Win (L := L) (K := K) n c)
    (hcore : Phase7LedgerCore (L := L) (K := K) sigma l G j c)
    (r₁ r₂ : AgentState L K) :
    Phase7LedgerCore (L := L) (K := K) sigma l G j
      (Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂) := by
  exact
    ⟨Phase7BandTransition.bandClear_stepOrSelf sigma j.val n c
        hgenuine hcore.cleared r₁ r₂,
      majorityBlockLedger_stepOrSelf sigma l G n c
        hgenuine hcore.ledger r₁ r₂⟩

/-- Every point in the real one-step support preserves the deterministic
stage core. -/
theorem phase7LedgerCore_of_mem_stepDistOrSelf_support
    (n : ℕ) (sigma : Sign) (l G : ℕ) (j : Fin (L + 1))
    (c c' : Config (AgentState L K))
    (hgenuine : PhaseOnlyWindows.Phase7Win (L := L) (K := K) n c)
    (hcore : Phase7LedgerCore (L := L) (K := K) sigma l G j c)
    (hc' : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    Phase7LedgerCore (L := L) (K := K) sigma l G j c' := by
  by_cases hc : 2 ≤ c.card
  · rw [show (NonuniformMajority L K).stepDistOrSelf c =
        (NonuniformMajority L K).stepDist c hc by
      unfold Protocol.stepDistOrSelf
      rw [dif_pos hc]] at hc'
    obtain ⟨⟨r₁, r₂⟩, hr⟩ :=
      Protocol.stepDist_support (NonuniformMajority L K) c hc c' hc'
    rw [← hr]
    exact phase7LedgerCore_stepOrSelf n sigma l G j c
      hgenuine hcore r₁ r₂
  · rw [show (NonuniformMajority L K).stepDistOrSelf c = PMF.pure c by
      unfold Protocol.stepDistOrSelf
      rw [dif_neg hc]] at hc'
    rw [PMF.mem_support_pure_iff] at hc'
    subst c'
    exact hcore

/-- The real one-step kernel gives zero mass to failure of the deterministic
ledger core. -/
theorem transitionKernel_not_phase7LedgerCore_eq_zero
    (n : ℕ) (sigma : Sign) (l G : ℕ) (j : Fin (L + 1))
    (c : Config (AgentState L K))
    (hgenuine : PhaseOnlyWindows.Phase7Win (L := L) (K := K) n c)
    (hcore : Phase7LedgerCore (L := L) (K := K) sigma l G j c) :
    (NonuniformMajority L K).transitionKernel c
      {c' | ¬ Phase7LedgerCore (L := L) (K := K) sigma l G j c'} = 0 := by
  change ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
    {c' | ¬ Phase7LedgerCore (L := L) (K := K) sigma l G j c'} = 0
  rw [PMF.toMeasure_apply_eq_zero_iff _
    (DiscreteMeasurableSpace.forall_measurableSet _)]
  rw [Set.disjoint_left]
  intro c' hsupp hbad
  exact hbad
    (phase7LedgerCore_of_mem_stepDistOrSelf_support
      n sigma l G j c c' hgenuine hcore hsupp)

/-- Consequently a dynamic stage gate can escape only through the genuine
Phase-7 working-window boundary (clock advancement), not through depletion of
a static eliminator floor. -/
theorem transitionKernel_not_ledgerStageReady_le_not_phase7Win
    (n : ℕ) (sigma : Sign) (l G : ℕ) (j : Fin (L + 1))
    (c : Config (AgentState L K))
    (hready : Phase7LedgerStageReady (L := L) (K := K)
      n sigma l G j c) :
    (NonuniformMajority L K).transitionKernel c
        {c' | ¬ Phase7LedgerStageReady (L := L) (K := K)
          n sigma l G j c'} ≤
      (NonuniformMajority L K).transitionKernel c
        {c' | ¬ PhaseOnlyWindows.Phase7Win (L := L) (K := K) n c'} := by
  let μ := (NonuniformMajority L K).transitionKernel c
  let A := {c' | ¬ Phase7LedgerStageReady (L := L) (K := K)
    n sigma l G j c'}
  let B := {c' | ¬ PhaseOnlyWindows.Phase7Win (L := L) (K := K) n c'}
  let C := {c' | ¬ Phase7LedgerCore (L := L) (K := K) sigma l G j c'}
  have hsub : A ⊆ B ∪ C := by
    intro c' hc'
    by_cases hh : PhaseOnlyWindows.Phase7Win (L := L) (K := K) n c'
    · exact Or.inr (fun hcore => hc' ⟨hh, hcore⟩)
    · exact Or.inl hh
  have hzero : μ C = 0 := by
    simpa [μ, C] using
      transitionKernel_not_phase7LedgerCore_eq_zero
        n sigma l G j c hready.win hready.core
  calc
    μ A ≤ μ (B ∪ C) := measure_mono hsub
    _ ≤ μ B + μ C := measure_union_le _ _
    _ = μ B := by rw [hzero, add_zero]

/-! ## Drift consumer with only the genuine window escape -/

/-- The remaining Phase-7 escape obligation is independent of the majority
resource ledger: it is exactly the chance that the phase-only genuine window is
left in one step (in practice, a Clock reaches the phase boundary). -/
structure Phase7WinEscapeBound (n : ℕ) (η : ℝ≥0∞) : Prop where
  hesc :
    ∀ c, PhaseOnlyWindows.Phase7Win (L := L) (K := K) n c →
      (NonuniformMajority L K).transitionKernel c
        {c' | ¬ PhaseOnlyWindows.Phase7Win (L := L) (K := K) n c'} ≤ η

/-- A window-only escape atom bounds escape from every ledger stage gate. -/
theorem ledgerStageReady_escape_le
    (n : ℕ) (sigma : Sign) (l G : ℕ) (j : Fin (L + 1))
    (η : ℝ≥0∞) (hesc : Phase7WinEscapeBound (L := L) (K := K) n η)
    (c : Config (AgentState L K))
    (hready : Phase7LedgerStageReady (L := L) (K := K)
      n sigma l G j c) :
    (NonuniformMajority L K).transitionKernel c
        {c' | ¬ Phase7LedgerStageReady (L := L) (K := K)
          n sigma l G j c'} ≤ η :=
  (transitionKernel_not_ledgerStageReady_le_not_phase7Win
      n sigma l G j c hready).trans (hesc.hesc c hready.win)

/-- The landed scheduler rectangle and drop-sum proof apply unchanged to the
ledger gate, because the ledger supplies the old pointwise pool at each state. -/
theorem phase7_band_weighted_drift_ledger
    (n : ℕ) (sigma : Sign) (l G : ℕ) (j : Fin (L + 1))
    (hn : 2 ≤ n) (hjl : l ≤ j.val) (hjtop : j.val < l + 3) :
    DyadicMassDrainTight.WeightedDyadicMassDrift (L := L) (K := K)
      (fun c => Phase7LedgerStageReady (L := L) (K := K)
        n sigma l G j c)
      (fun c => bandCountN (L := L) (K := K) sigma j c)
      (1 - ENNReal.ofReal (((2 * G : ℕ) : ℝ) /
        ((n : ℝ) * ((n : ℝ) - 1)))) := by
  intro c hc
  exact Phase7BandDropSum.phase7_band_weighted_drift
    (L := L) (K := K) n sigma l G j hn hjl hjtop c hc.toStatic

/-- One exact-band multiplicative-drift stage using the dynamic ledger gate.
Its escape parameter concerns only the genuine Phase-7 window. -/
noncomputable def phase7LedgerBandStageSurvival
    {n : ℕ} (hn : 2 ≤ n)
    (sigma : Sign) (l G : ℕ) (j : Fin (L + 1))
    (hjl : l ≤ j.val) (hjtop : j.val < l + 3)
    (hGpos : 1 ≤ G) (hGtop : 2 * G ≤ n * (n - 1))
    (η : ℝ≥0∞)
    (hesc : Phase7WinEscapeBound (L := L) (K := K) n η)
    (escapeε : ℝ≥0)
    (hescε :
      ((DriftSurvival.driftHorizon ((2 * G : ℕ) : ℝ) n n 6 : ℕ) : ℝ≥0∞) * η
        ≤ (escapeε : ℝ≥0∞)) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel := by
  let Inv : Config (AgentState L K) → Prop :=
    fun c => Phase7LedgerStageReady (L := L) (K := K)
      n sigma l G j c
  let Φ : Config (AgentState L K) → ℕ :=
    fun c => bandCountN (L := L) (K := K) sigma j c
  let r : ℝ≥0∞ :=
    1 - ENNReal.ofReal (((2 * G : ℕ) : ℝ) /
      ((n : ℝ) * ((n : ℝ) - 1)))
  let T : ℕ := DriftSurvival.driftHorizon ((2 * G : ℕ) : ℝ) n n 6
  have hB0 : (0 : ℝ) < ((2 * G : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < 2 * G by omega)
  have hBtop : ((2 * G : ℕ) : ℝ) ≤
      (n : ℝ) * ((n : ℝ) - 1) := by
    calc
      ((2 * G : ℕ) : ℝ) ≤ ((n * (n - 1) : ℕ) : ℝ) := by
        exact_mod_cast hGtop
      _ = (n : ℝ) * ((n : ℝ) - 1) := by
        rw [Nat.cast_mul, Nat.cast_sub (by omega)]
        norm_num
  have hr : r ≤ 1 := by
    dsimp [r]
    exact tsub_le_self
  have hdrift :
      ∀ c, Inv c →
        ∫⁻ c', (Φ c' : ℝ≥0∞) ∂((NonuniformMajority L K).transitionKernel c)
          ≤ r * (Φ c : ℝ≥0∞) := by
    simpa [Inv, Φ, r] using
      (phase7_band_weighted_drift_ledger
        (L := L) (K := K) n sigma l G j hn hjl hjtop)
  have hdrain :
      r ^ T * (n : ℝ≥0∞) ≤
        (DriftSurvival.driftBudgetNN 6 n : ℝ≥0∞) := by
    simpa [r, T] using
      (DriftSurvival.drift_pow_le_budget_sub
        (B := ((2 * G : ℕ) : ℝ)) (n := n) (Φmax := n) (D := 6)
        hn (by omega) (by norm_num) hB0 hBtop)
  let base : PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
    DriftSurvival.driftSurvivalPhase
      (NonuniformMajority L K).transitionKernel Inv Φ r hr hdrift
      η (fun c hc => ledgerStageReady_escape_le
        n sigma l G j η hesc c hc)
      T n (DriftSurvival.driftBudgetNN 6 n) escapeε hdrain
      (by simpa [T] using hescε)
  exact
    { Pre := Inv
      Post := fun c => Inv c ∧ Φ c = 0
      t := T
      ε := DriftSurvival.driftBudgetNN 6 n + escapeε
      convergence := by
        intro c hc
        have hΦ : Φ c ≤ n := by
          exact (bandCountN_le_card (L := L) (K := K) sigma j c).trans_eq
            hc.win.1
        exact base.convergence c ⟨hc, hΦ⟩ }

@[simp] theorem phase7LedgerBandStageSurvival_t
    {n : ℕ} (hn : 2 ≤ n)
    (sigma : Sign) (l G : ℕ) (j : Fin (L + 1))
    (hjl : l ≤ j.val) (hjtop : j.val < l + 3)
    (hGpos : 1 ≤ G) (hGtop : 2 * G ≤ n * (n - 1))
    (η : ℝ≥0∞)
    (hesc : Phase7WinEscapeBound (L := L) (K := K) n η)
    (escapeε : ℝ≥0)
    (hescε :
      ((DriftSurvival.driftHorizon ((2 * G : ℕ) : ℝ) n n 6 : ℕ) : ℝ≥0∞) * η
        ≤ (escapeε : ℝ≥0∞)) :
    (phase7LedgerBandStageSurvival (L := L) (K := K) hn sigma l G j
      hjl hjtop hGpos hGtop η hesc escapeε hescε).t =
      DriftSurvival.driftHorizon ((2 * G : ℕ) : ℝ) n n 6 := rfl

@[simp] theorem phase7LedgerBandStageSurvival_epsilon
    {n : ℕ} (hn : 2 ≤ n)
    (sigma : Sign) (l G : ℕ) (j : Fin (L + 1))
    (hjl : l ≤ j.val) (hjtop : j.val < l + 3)
    (hGpos : 1 ≤ G) (hGtop : 2 * G ≤ n * (n - 1))
    (η : ℝ≥0∞)
    (hesc : Phase7WinEscapeBound (L := L) (K := K) n η)
    (escapeε : ℝ≥0)
    (hescε :
      ((DriftSurvival.driftHorizon ((2 * G : ℕ) : ℝ) n n 6 : ℕ) : ℝ≥0∞) * η
        ≤ (escapeε : ℝ≥0∞)) :
    (phase7LedgerBandStageSurvival (L := L) (K := K) hn sigma l G j
      hjl hjtop hGpos hGtop η hesc escapeε hescε).ε =
      DriftSurvival.driftBudgetNN 6 n + escapeε := rfl

/-- A completed dynamic stage supplies its successor without recreating a
static pool premise. -/
theorem ledgerStageReady_succ_of_post
    {n l G : ℕ} {sigma : Sign} {j j' : Fin (L + 1)}
    {c : Config (AgentState L K)}
    (hnext : j.val + 1 = j'.val)
    (hpost :
      Phase7LedgerStageReady (L := L) (K := K) n sigma l G j c ∧
        bandCountN (L := L) (K := K) sigma j c = 0) :
    Phase7LedgerStageReady (L := L) (K := K) n sigma l G j' c := by
  exact
    ⟨hpost.1.win,
      ⟨by
        rw [← hnext]
        exact bandClear_succ_of_count_zero
          (L := L) (K := K) sigma j c hpost.1.core.cleared hpost.2,
       hpost.1.core.ledger⟩⟩

/-- The final dynamic stage postcondition implies the public cumulative
Phase-7 postcondition. -/
theorem post7Bands_of_ledger_last_stage_post
    {n l G : ℕ} {sigma : Sign} (hlL : l ≤ L)
    {c : Config (AgentState L K)}
    (hpost :
      Phase7LedgerStageReady (L := L) (K := K) n sigma l G
          (Phase7BandStages.phase7LastStageIndex (L := L) l hlL) c ∧
        bandCountN (L := L) (K := K) sigma
          (Phase7BandStages.phase7LastStageIndex (L := L) l hlL) c = 0) :
    Post7Bands (L := L) (K := K) n sigma l c :=
  ⟨hpost.1.win,
    Phase7BandStages.bandClear_add_three_of_last_stage_post
      (L := L) (K := K) l hlL c hpost.1.core.cleared hpost.2⟩

/-- The naturally truncated one-to-three family of dynamic ledger stages. -/
noncomputable def phase7LedgerBandStages
    {n : ℕ} (hn : 2 ≤ n)
    (sigma : Sign) (l G : ℕ) (hlL : l ≤ L)
    (hGpos : 1 ≤ G) (hGtop : 2 * G ≤ n * (n - 1))
    (η : ℝ≥0∞)
    (hesc : Phase7WinEscapeBound (L := L) (K := K) n η)
    (escapeε : ℝ≥0)
    (hescε :
      ((DriftSurvival.driftHorizon ((2 * G : ℕ) : ℝ) n n 6 : ℕ) : ℝ≥0∞) * η
        ≤ (escapeε : ℝ≥0∞)) :
    Fin (Phase7BandStages.phase7StageCount L l) →
      PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  fun q =>
    phase7LedgerBandStageSurvival (L := L) (K := K) hn sigma l G
      (Phase7BandStages.phase7StageIndex (L := L) l hlL q)
      (Phase7BandStages.phase7StageIndex_range (L := L) l hlL q).1
      (Phase7BandStages.phase7StageIndex_range (L := L) l hlL q).2
      hGpos hGtop η hesc escapeε hescε

/-- Compose all naturally available dynamic stages and recut to `Post7Bands`.
No static-pool escape premise appears in this construction. -/
noncomputable def phase7LedgerBandsSurvival
    {n : ℕ} (hn : 2 ≤ n)
    (sigma : Sign) (l G : ℕ) (hlL : l ≤ L)
    (hGpos : 1 ≤ G) (hGtop : 2 * G ≤ n * (n - 1))
    (η : ℝ≥0∞)
    (hesc : Phase7WinEscapeBound (L := L) (K := K) n η)
    (escapeε : ℝ≥0)
    (hescε :
      ((DriftSurvival.driftHorizon ((2 * G : ℕ) : ℝ) n n 6 : ℕ) : ℝ≥0∞) * η
        ≤ (escapeε : ℝ≥0∞)) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel := by
  let m := Phase7BandStages.phase7StageCount L l
  let stages := phase7LedgerBandStages (L := L) (K := K) hn sigma l G hlL
    hGpos hGtop η hesc escapeε hescε
  have hm : 0 < m := Phase7BandStages.phase7StageCount_pos (L := L) l hlL
  have hchain :
      ∀ (q : Fin m) (hq : q.val + 1 < m),
        ∀ c, (stages q).Post c →
          (stages ⟨q.val + 1, hq⟩).Pre c := by
    intro q hq c hc
    apply ledgerStageReady_succ_of_post
      (L := L) (K := K)
      (Phase7BandStages.phase7StageIndex_succ
        (L := L) l hlL q hq).symm
    simpa [stages, phase7LedgerBandStages] using hc
  exact
    { Pre := (stages ⟨0, hm⟩).Pre
      Post := Post7Bands (L := L) (K := K) n sigma l
      t := ∑ q : Fin m, (stages q).t
      ε := ∑ q : Fin m, (stages q).ε
      convergence := by
        intro c hc
        have hcomp := composeW_n_phases
          (K := (NonuniformMajority L K).transitionKernel)
          hm stages hchain c hc
        have hsubset :
            {c' | ¬ Post7Bands (L := L) (K := K) n sigma l c'} ⊆
              {c' | ¬(stages ⟨m - 1, by omega⟩).Post c'} := by
          intro c' hc' hlast
          apply hc'
          apply post7Bands_of_ledger_last_stage_post (L := L) (K := K) hlL
          simpa [stages, phase7LedgerBandStages,
            Phase7BandStages.phase7LastStageIndex] using hlast
        have hε :
            (((∑ q : Fin m, (stages q).ε : ℝ≥0)) : ℝ≥0∞) =
              ∑ q : Fin m, ((stages q).ε : ℝ≥0∞) := by
          push_cast
          rfl
        calc
          ((NonuniformMajority L K).transitionKernel ^
                (∑ q : Fin m, (stages q).t)) c
              {c' | ¬ Post7Bands (L := L) (K := K) n sigma l c'}
              ≤ ((NonuniformMajority L K).transitionKernel ^
                  (∑ q : Fin m, (stages q).t)) c
                {c' | ¬(stages ⟨m - 1, by omega⟩).Post c'} :=
            measure_mono hsubset
          _ ≤ ∑ q : Fin m, ((stages q).ε : ℝ≥0∞) := hcomp
          _ = (((∑ q : Fin m, (stages q).ε : ℝ≥0)) : ℝ≥0∞) := hε.symm }

@[simp] theorem phase7LedgerBandsSurvival_t
    {n : ℕ} (hn : 2 ≤ n)
    (sigma : Sign) (l G : ℕ) (hlL : l ≤ L)
    (hGpos : 1 ≤ G) (hGtop : 2 * G ≤ n * (n - 1))
    (η : ℝ≥0∞)
    (hesc : Phase7WinEscapeBound (L := L) (K := K) n η)
    (escapeε : ℝ≥0)
    (hescε :
      ((DriftSurvival.driftHorizon ((2 * G : ℕ) : ℝ) n n 6 : ℕ) : ℝ≥0∞) * η
        ≤ (escapeε : ℝ≥0∞)) :
    (phase7LedgerBandsSurvival (L := L) (K := K) hn sigma l G hlL
      hGpos hGtop η hesc escapeε hescε).t =
      Phase7BandStages.phase7StageCount L l *
        DriftSurvival.driftHorizon ((2 * G : ℕ) : ℝ) n n 6 := by
  simp [phase7LedgerBandsSurvival, phase7LedgerBandStages]

@[simp] theorem phase7LedgerBandsSurvival_epsilon
    {n : ℕ} (hn : 2 ≤ n)
    (sigma : Sign) (l G : ℕ) (hlL : l ≤ L)
    (hGpos : 1 ≤ G) (hGtop : 2 * G ≤ n * (n - 1))
    (η : ℝ≥0∞)
    (hesc : Phase7WinEscapeBound (L := L) (K := K) n η)
    (escapeε : ℝ≥0)
    (hescε :
      ((DriftSurvival.driftHorizon ((2 * G : ℕ) : ℝ) n n 6 : ℕ) : ℝ≥0∞) * η
        ≤ (escapeε : ℝ≥0∞)) :
    (phase7LedgerBandsSurvival (L := L) (K := K) hn sigma l G hlL
      hGpos hGtop η hesc escapeε hescε).ε =
      (Phase7BandStages.phase7StageCount L l : ℝ≥0) *
        (DriftSurvival.driftBudgetNN 6 n + escapeε) := by
  simp [phase7LedgerBandsSurvival, phase7LedgerBandStages, mul_add]

/-- With one sixth of the inverse-square budget assigned to drift and one
sixth to the genuine window escape in each of at most three stages, the whole
dynamic Phase-7 drain fits `1/n²`. -/
theorem phase7LedgerBandsSurvival_epsilon_le_inv_sq
    {n : ℕ} (hn : 2 ≤ n)
    (sigma : Sign) (l G : ℕ) (hlL : l ≤ L)
    (hGpos : 1 ≤ G) (hGtop : 2 * G ≤ n * (n - 1))
    (η : ℝ≥0∞)
    (hesc : Phase7WinEscapeBound (L := L) (K := K) n η)
    (escapeε : ℝ≥0)
    (hescε :
      ((DriftSurvival.driftHorizon ((2 * G : ℕ) : ℝ) n n 6 : ℕ) : ℝ≥0∞) * η
        ≤ (escapeε : ℝ≥0∞))
    (hescape : escapeε ≤ DriftSurvival.driftBudgetNN 6 n) :
    ((phase7LedgerBandsSurvival (L := L) (K := K) hn sigma l G hlL
      hGpos hGtop η hesc escapeε hescε).ε : ℝ≥0∞) ≤
        1 / (n : ℝ≥0∞) ^ 2 := by
  rw [phase7LedgerBandsSurvival_epsilon, ENNReal.coe_mul, ENNReal.coe_add]
  have hm : (Phase7BandStages.phase7StageCount L l : ℝ≥0∞) ≤ 3 := by
    exact_mod_cast Phase7BandStages.phase7StageCount_le_three L l
  have he : (escapeε : ℝ≥0∞) ≤
      (DriftSurvival.driftBudgetNN 6 n : ℝ≥0∞) := by
    exact_mod_cast hescape
  calc
    (Phase7BandStages.phase7StageCount L l : ℝ≥0∞) *
          ((DriftSurvival.driftBudgetNN 6 n : ℝ≥0∞) +
            (escapeε : ℝ≥0∞))
        ≤ 3 * ((DriftSurvival.driftBudgetNN 6 n : ℝ≥0∞) +
          (DriftSurvival.driftBudgetNN 6 n : ℝ≥0∞)) := by gcongr
    _ = 6 * (DriftSurvival.driftBudgetNN 6 n : ℝ≥0∞) := by ring
    _ = 1 / (n : ℝ≥0∞) ^ 2 :=
      DriftSurvival.natCast_mul_driftBudgetNN_eq_inv_sq
        (D := 6) (n := n) (by norm_num) (by omega)

#print axioms majorityBlockCount_eq_sum_count
#print axioms majorityBlockFloor_of_ledger
#print axioms phase7BandPool_of_ledger
#print axioms cancelSplit_block_debt_pair
#print axioms Transition_block_debt_pair
#print axioms majorityBlockLedger_stepOrSelf
#print axioms transitionKernel_not_phase7LedgerCore_eq_zero
#print axioms transitionKernel_not_ledgerStageReady_le_not_phase7Win
#print axioms phase7_band_weighted_drift_ledger
#print axioms phase7LedgerBandStageSurvival
#print axioms ledgerStageReady_succ_of_post
#print axioms phase7LedgerBandsSurvival
#print axioms phase7LedgerBandsSurvival_t
#print axioms phase7LedgerBandsSurvival_epsilon
#print axioms phase7LedgerBandsSurvival_epsilon_le_inv_sq

end Phase7MajorityBlockLedger
end Ripple.PopulationProtocol.ExactMajority
