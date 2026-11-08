/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Phase-5/6 entry certificates for the Reserve-fuel ledger

This file turns the paper's scaled upper-tail mass bounds into the exact
deterministic fuel ledger consumed during Phase 6.  It contains no sampling or
concentration theorem: those producers only need to establish one of the two
explicit count inequalities at the bottom of the file.
-/

import Ripple.PopulationProtocol.ExactMajority.Probability.Lemma615MassAboveDefs
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase6FuelLedger

namespace Ripple.PopulationProtocol.ExactMajority
namespace Phase6FuelEntry

open scoped BigOperators

variable {L K : ℕ}

/-- Paying every split needed to reach index `i` costs no more than the scaled
dyadic mass above `i`: `2^(i-j)-1 ≤ 2^(i-j)` agent by agent. -/
theorem agentDebt_le_agentMassAboveScaledW
    (i : Fin (L + 1)) (a : AgentState L K) :
    Phase6FuelLedger.agentDebt (L := L) (K := K) i a ≤
      Lemma615MassAbove.agentMassAboveScaledW
        (L := L) (K := K) i.val a := by
  unfold Phase6FuelLedger.agentDebt
    Lemma615MassAbove.agentMassAboveScaledW
    Lemma615MassAbove.biasMassAboveScaledW
  by_cases hr : a.role = Role.main
  · simp only [hr, if_pos]
    cases a.bias with
    | zero => simp
    | dyadic sigma j =>
        by_cases hj : j.val < i.val
        · simp only [hj, if_pos]
          exact Nat.sub_le _ _
        · simp [hj]
  · simp [hr]

/-- Configuration-level debt bound by the scaled upper-tail mass. -/
theorem splitDebt_le_massAboveScaled
    (i : Fin (L + 1)) (c : Config (AgentState L K)) :
    Phase6FuelLedger.splitDebt (L := L) (K := K) i c ≤
      Lemma615MassAbove.massAboveScaled
        (L := L) (K := K) i.val c := by
  induction c using Multiset.induction_on with
  | empty => simp [Phase6FuelLedger.splitDebt,
      Lemma615MassAbove.massAboveScaled]
  | cons a c ih =>
      simp only [Phase6FuelLedger.splitDebt,
        Lemma615MassAbove.massAboveScaled, Multiset.map_cons,
        Multiset.sum_cons]
      exact Nat.add_le_add
        (agentDebt_le_agentMassAboveScaledW
          (L := L) (K := K) i a) ih

/-- A sampled-class count that covers the target margin plus scaled upper-tail
mass produces the exact persistent single-level fuel ledger. -/
theorem fuelLedger_of_massAbove_floor
    (i : Fin (L + 1)) (K₀ : ℕ) (c : Config (AgentState L K))
    (hfloor :
      K₀ + Lemma615MassAbove.massAboveScaled
          (L := L) (K := K) i.val c ≤
        Phase6FuelLedger.reserveFuel (L := L) (K := K) i c) :
    Phase6FuelLedger.FuelLedger (L := L) (K := K) i K₀ c := by
  unfold Phase6FuelLedger.FuelLedger
  exact (Nat.add_le_add_left
    (splitDebt_le_massAboveScaled (L := L) (K := K) i c) K₀).trans hfloor

/-- The higher-target scaled mass similarly pays the adjacent-union ledger. -/
theorem unionFuelLedger_of_massAbove_floor
    (l : Fin (L + 1)) (hl : l.val + 2 ≤ L)
    (K₀ : ℕ) (c : Config (AgentState L K))
    (hfloor :
      K₀ + Lemma615MassAbove.massAboveScaled
          (L := L) (K := K)
          (Phase6FuelLedger.highIndex l hl).val c ≤
        Phase6FuelLedger.twoReserveFuel (L := L) (K := K) l c) :
    Phase6FuelLedger.UnionFuelLedger (L := L) (K := K) l K₀ c := by
  unfold Phase6FuelLedger.UnionFuelLedger
  rw [Phase6FuelLedger.unionSplitDebt_eq_splitDebt_high
    (L := L) (K := K) l hl c]
  exact (Nat.add_le_add_left
    (splitDebt_le_massAboveScaled
      (L := L) (K := K) (Phase6FuelLedger.highIndex l hl) c) K₀).trans hfloor

/-- Exact deterministic seam certificate matching paper Lemma 7.2's two
cases.  The probabilistic producer may establish either the lower sampled-class
surplus or the adjacent-union surplus. -/
theorem twoLevelFuelLedger_of_massAbove_cases
    (l : Fin (L + 1)) (hl : l.val + 2 ≤ L)
    (K₀ : ℕ) (c : Config (AgentState L K))
    (hcases :
      K₀ + Lemma615MassAbove.massAboveScaled
          (L := L) (K := K) l.val c ≤
          Phase6FuelLedger.reserveFuel (L := L) (K := K) l c ∨
        K₀ + Lemma615MassAbove.massAboveScaled
          (L := L) (K := K)
          (Phase6FuelLedger.highIndex l hl).val c ≤
          Phase6FuelLedger.twoReserveFuel (L := L) (K := K) l c) :
    Phase6FuelLedger.TwoLevelFuelLedger
      (L := L) (K := K) l K₀ c := by
  rcases hcases with hlower | hunion
  · exact Or.inl (fuelLedger_of_massAbove_floor
      (L := L) (K := K) l K₀ c hlower)
  · exact Or.inr (unionFuelLedger_of_massAbove_floor
      (L := L) (K := K) l hl K₀ c hunion)

#print axioms agentDebt_le_agentMassAboveScaledW
#print axioms splitDebt_le_massAboveScaled
#print axioms fuelLedger_of_massAbove_floor
#print axioms unionFuelLedger_of_massAbove_floor
#print axioms twoLevelFuelLedger_of_massAbove_cases

end Phase6FuelEntry
end Ripple.PopulationProtocol.ExactMajority
