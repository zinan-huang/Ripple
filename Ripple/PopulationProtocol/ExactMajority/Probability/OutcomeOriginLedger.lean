/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Outcome-origin interval mass ledger

The paper's key invariant (proof of Theorem 3.1, "the sum of bias across all
Main agents is the initial gap g, and this key invariant is maintained through
all phases") survives Phase 8 only in interval form: an agent with
`full = true` stores a bias `±2^{-i}` that represents a true mass in the
half-open interval between half the stored value and the stored value
(paper: an agent with `opinion = +1, exponent = -i, full = True` represents
`2^{-(i+1)} ≤ bias < 2^{-i}`).

This file packages that invariant witness-freely as two scalar inequalities
`massLoSum c ≤ initialGap c ≤ massHiSum c`, where `massLo`/`massHi` are
per-agent computable interval endpoints (exact below Phase 8, interval at
Phases 8–9, the full `[-3, 3]` bucket at the error Phase 10).

The *seed bridge* (drained all-Phase-8 endpoint + ledger inequalities ⇒
`Phase8OutcomeThread.Seed`) lives in `OutcomeOriginSeedBridge.lean`: it needs
the `Phase8OutcomeThread` import chain, which this core file deliberately
avoids so the ledger defs and the absorb closure verify independently of the
phase-8 drain-engine repair.

Design: `working_notes/verdict_thread_design.md`.
-/

import Ripple.PopulationProtocol.ExactMajority.Analysis.Invariants

namespace Ripple.PopulationProtocol.ExactMajority
namespace OutcomeOriginLedger

variable {L K : ℕ}

/-! ## Per-agent interval endpoints -/

/-- Lower endpoint of the true-mass interval represented by an agent.

* Phases 0–2: the conserved integer `smallBias` (exact).
* Phases 3–7: the dyadic `bias` value (exact; consumption has not started).
* Phases 8–9: exact unless `full`; a positive `full` agent represents at
  least half its stored bias, a negative `full` agent at least its stored
  bias.
* Phase 10: the error bucket `-3` (every other regime lies in `[-3, 3]`). -/
def massLo (a : AgentState L K) : ℚ :=
  if a.phase.val ≤ 2 then (AgentState.smallBiasInt a : ℚ)
  else if a.phase.val ≤ 7 then a.bias.toRat
  else if a.phase.val ≤ 9 then
    if a.full then
      match a.bias with
      | .zero => 0
      | .dyadic .pos i => (1 : ℚ) / 2 ^ (i.val + 1)
      | .dyadic .neg i => -(1 : ℚ) / 2 ^ i.val
    else a.bias.toRat
  else (-3 : ℚ)

/-- Upper endpoint of the true-mass interval represented by an agent;
mirror image of `massLo`. -/
def massHi (a : AgentState L K) : ℚ :=
  if a.phase.val ≤ 2 then (AgentState.smallBiasInt a : ℚ)
  else if a.phase.val ≤ 7 then a.bias.toRat
  else if a.phase.val ≤ 9 then
    if a.full then
      match a.bias with
      | .zero => 0
      | .dyadic .pos i => (1 : ℚ) / 2 ^ i.val
      | .dyadic .neg i => -(1 : ℚ) / 2 ^ (i.val + 1)
    else a.bias.toRat
  else (3 : ℚ)

def massLoSum (c : Config (AgentState L K)) : ℚ :=
  (c.map massLo).sum

def massHiSum (c : Config (AgentState L K)) : ℚ :=
  (c.map massHi).sum

/-- The interval ledger: the conserved initial gap is bracketed by the
per-agent interval endpoints. -/
def MassLedger (c : Config (AgentState L K)) : Prop :=
  massLoSum c ≤ ((initialGap c : ℤ) : ℚ) ∧
    ((initialGap c : ℤ) : ℚ) ≤ massHiSum c

/-! ## Base case at a valid initial configuration -/

private lemma sum_map_intCast (c : Config (AgentState L K)) (f : AgentState L K → ℤ) :
    (c.map (fun a => ((f a : ℤ) : ℚ))).sum = (((c.map f).sum : ℤ) : ℚ) := by
  induction c using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
      rw [Multiset.map_cons, Multiset.sum_cons, Multiset.map_cons,
        Multiset.sum_cons, Int.cast_add, ih]

private lemma massLo_validInitial_agent (a : AgentState L K)
    (hphase : a.phase = ⟨0, by decide⟩)
    (hA : a.input = .A → a.smallBias = ⟨4, by decide⟩)
    (hB : a.input = .B → a.smallBias = ⟨2, by decide⟩) :
    massLo a = ((AgentState.inputBiasInt a : ℤ) : ℚ) := by
  have h0 : a.phase.val = 0 := by rw [hphase]
  cases hinput : a.input with
  | A =>
      have hsb := hA hinput
      simp [massLo, h0, AgentState.smallBiasInt, AgentState.inputBiasInt,
        hsb, hinput]
  | B =>
      have hsb := hB hinput
      simp [massLo, h0, AgentState.smallBiasInt, AgentState.inputBiasInt,
        hsb, hinput]

private lemma massHi_validInitial_agent (a : AgentState L K)
    (hphase : a.phase = ⟨0, by decide⟩)
    (hA : a.input = .A → a.smallBias = ⟨4, by decide⟩)
    (hB : a.input = .B → a.smallBias = ⟨2, by decide⟩) :
    massHi a = ((AgentState.inputBiasInt a : ℤ) : ℚ) := by
  have h0 : a.phase.val = 0 := by rw [hphase]
  cases hinput : a.input with
  | A =>
      have hsb := hA hinput
      simp [massHi, h0, AgentState.smallBiasInt, AgentState.inputBiasInt,
        hsb, hinput]
  | B =>
      have hsb := hB hinput
      simp [massHi, h0, AgentState.smallBiasInt, AgentState.inputBiasInt,
        hsb, hinput]

theorem massLoSum_validInitial (init : Config (AgentState L K))
    (hvalid : validInitial init) :
    massLoSum init = ((initialGap init : ℤ) : ℚ) := by
  unfold massLoSum
  have hcongr : init.map massLo =
      init.map (fun a => ((AgentState.inputBiasInt a : ℤ) : ℚ)) := by
    apply Multiset.map_congr rfl
    intro a ha
    obtain ⟨hphase, _, _, _, hA, hB⟩ := hvalid a ha
    exact massLo_validInitial_agent a hphase hA hB
  rw [hcongr, sum_map_intCast]
  norm_cast
  exact inputBiasSum_initialGap init

theorem massHiSum_validInitial (init : Config (AgentState L K))
    (hvalid : validInitial init) :
    massHiSum init = ((initialGap init : ℤ) : ℚ) := by
  unfold massHiSum
  have hcongr : init.map massHi =
      init.map (fun a => ((AgentState.inputBiasInt a : ℤ) : ℚ)) := by
    apply Multiset.map_congr rfl
    intro a ha
    obtain ⟨hphase, _, _, _, hA, hB⟩ := hvalid a ha
    exact massHi_validInitial_agent a hphase hA hB
  rw [hcongr, sum_map_intCast]
  norm_cast
  exact inputBiasSum_initialGap init

theorem massLedger_validInitial (init : Config (AgentState L K))
    (hvalid : validInitial init) :
    MassLedger init :=
  ⟨le_of_eq (massLoSum_validInitial init hvalid),
    le_of_eq (massHiSum_validInitial init hvalid).symm⟩

/-! ## Phase-8 absorb closure (fixed consumption direction)

The heart of the ledger: under the paper-correct `absorbConsume` (consumer =
smaller index = larger |bias|), each consumption only *widens* the pair's
mass interval — `massLo` pair-sum never increases and `massHi` pair-sum never
decreases.  The four live branches each reduce to the halving inequality
`1/2^j ≤ 1/2^(i+1) ↔ i + 1 ≤ j`. -/

private lemma inv_pow_succ_add (n : ℕ) :
    (1 : ℚ) / 2 ^ (n + 1) + (1 : ℚ) / 2 ^ (n + 1) = 1 / 2 ^ n := by
  rw [pow_succ]
  field_simp
  ring

private lemma inv_pow_le_inv_pow {m n : ℕ} (h : m ≤ n) :
    (1 : ℚ) / 2 ^ n ≤ 1 / 2 ^ m := by
  apply one_div_le_one_div_of_le
  · positivity
  · exact pow_le_pow_right₀ (by norm_num) h

private lemma inv_pow_pos (n : ℕ) : (0 : ℚ) < 1 / 2 ^ n := by positivity

/-- The absorb reaction never increases the `massLo` pair sum. -/
theorem absorbConsume_massLo_pair (s t : AgentState L K)
    (hs8 : s.phase.val = 8) (ht8 : t.phase.val = 8) :
    massLo (absorbConsume L K s t).1 + massLo (absorbConsume L K s t).2 ≤
      massLo s + massLo t := by
  unfold absorbConsume
  rcases hsb : s.bias with _ | ⟨ss, i⟩ <;> rcases htb : t.bias with _ | ⟨ts, j⟩
  · simp
  · simp
  · rcases ss <;> simp
  · rcases ss <;> rcases ts
    -- pos-pos: no-op
    · simp
    -- pos-neg
    · dsimp only
      split_ifs with h1 h2
      · obtain ⟨hij, hsf⟩ := h1
        rcases htf : t.full <;>
            simp only [massLo, hs8, ht8, hsb, htb, hsf, htf, Bias.toRat] <;>
            norm_num <;>
            (
             have hle := inv_pow_le_inv_pow (m := i.val + 1) (n := j.val) (by omega)
             have hsplit := inv_pow_succ_add i.val
             have hpos := inv_pow_pos j.val
             have hpos' := inv_pow_pos (j.val + 1)
             simp only [one_div, neg_div] at *
             linarith)
      · obtain ⟨hji, htf⟩ := h2
        rcases hsf : s.full <;>
            simp only [massLo, hs8, ht8, hsb, htb, hsf, htf, Bias.toRat] <;>
            norm_num <;>
            (
             have hle := inv_pow_le_inv_pow (m := j.val + 1) (n := i.val) (by omega)
             have hsplit := inv_pow_succ_add j.val
             have hpos := inv_pow_pos i.val
             have hpos' := inv_pow_pos (i.val + 1)
             simp only [one_div, neg_div] at *
             linarith)
      · simp
    -- neg-pos
    · dsimp only
      split_ifs with h1 h2
      · obtain ⟨hij, hsf⟩ := h1
        rcases htf : t.full <;>
            simp only [massLo, hs8, ht8, hsb, htb, hsf, htf, Bias.toRat] <;>
            norm_num <;>
            (
             have hle := inv_pow_le_inv_pow (m := i.val + 1) (n := j.val) (by omega)
             have hsplit := inv_pow_succ_add i.val
             have hpos := inv_pow_pos j.val
             have hpos' := inv_pow_pos (i.val + 1)
             simp only [one_div, neg_div] at *
             linarith)
      · obtain ⟨hji, htf⟩ := h2
        rcases hsf : s.full <;>
            simp only [massLo, hs8, ht8, hsb, htb, hsf, htf, Bias.toRat] <;>
            norm_num <;>
            (
             have hle := inv_pow_le_inv_pow (m := j.val + 1) (n := i.val) (by omega)
             have hsplit := inv_pow_succ_add j.val
             have hpos := inv_pow_pos i.val
             have hpos' := inv_pow_pos (i.val + 1)
             simp only [one_div, neg_div] at *
             linarith)
      · simp
    -- neg-neg: no-op
    · simp

/-- The absorb reaction never decreases the `massHi` pair sum. -/
theorem absorbConsume_massHi_pair (s t : AgentState L K)
    (hs8 : s.phase.val = 8) (ht8 : t.phase.val = 8) :
    massHi s + massHi t ≤
      massHi (absorbConsume L K s t).1 + massHi (absorbConsume L K s t).2 := by
  unfold absorbConsume
  rcases hsb : s.bias with _ | ⟨ss, i⟩ <;> rcases htb : t.bias with _ | ⟨ts, j⟩
  · simp
  · simp
  · rcases ss <;> simp
  · rcases ss <;> rcases ts
    -- pos-pos: no-op
    · simp
    -- pos-neg
    · dsimp only
      split_ifs with h1 h2
      · obtain ⟨hij, hsf⟩ := h1
        rcases htf : t.full <;>
            simp only [massHi, hs8, ht8, hsb, htb, hsf, htf, Bias.toRat] <;>
            norm_num <;>
            (
             have hle := inv_pow_le_inv_pow (m := i.val + 1) (n := j.val) (by omega)
             have hsplit := inv_pow_succ_add i.val
             have hpos := inv_pow_pos j.val
             have hpos' := inv_pow_pos (j.val + 1)
             simp only [one_div, neg_div] at *
             linarith)
      · obtain ⟨hji, htf⟩ := h2
        rcases hsf : s.full <;>
            simp only [massHi, hs8, ht8, hsb, htb, hsf, htf, Bias.toRat] <;>
            norm_num <;>
            (
             have hle := inv_pow_le_inv_pow (m := j.val + 1) (n := i.val) (by omega)
             have hsplit := inv_pow_succ_add j.val
             have hpos := inv_pow_pos i.val
             have hpos' := inv_pow_pos (i.val + 1)
             simp only [one_div, neg_div] at *
             linarith)
      · simp
    -- neg-pos
    · dsimp only
      split_ifs with h1 h2
      · obtain ⟨hij, hsf⟩ := h1
        rcases htf : t.full <;>
            simp only [massHi, hs8, ht8, hsb, htb, hsf, htf, Bias.toRat] <;>
            norm_num <;>
            (
             have hle := inv_pow_le_inv_pow (m := i.val + 1) (n := j.val) (by omega)
             have hsplit := inv_pow_succ_add i.val
             have hpos := inv_pow_pos j.val
             have hpos' := inv_pow_pos (i.val + 1)
             simp only [one_div, neg_div] at *
             linarith)
      · obtain ⟨hji, htf⟩ := h2
        rcases hsf : s.full <;>
            simp only [massHi, hs8, ht8, hsb, htb, hsf, htf, Bias.toRat] <;>
            norm_num <;>
            (
             have hle := inv_pow_le_inv_pow (m := j.val + 1) (n := i.val) (by omega)
             have hsplit := inv_pow_succ_add j.val
             have hpos := inv_pow_pos i.val
             have hpos' := inv_pow_pos (i.val + 1)
             simp only [one_div, neg_div] at *
             linarith)
      · simp
    -- neg-neg: no-op
    · simp

#print axioms absorbConsume_massLo_pair
#print axioms absorbConsume_massHi_pair

#print axioms massLedger_validInitial

end OutcomeOriginLedger
end Ripple.PopulationProtocol.ExactMajority
