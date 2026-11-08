/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Phase-6 sampled-Reserve fuel ledger

This file isolates the deterministic resource accounting behind Phase 6.  A
sampled Reserve at hour `i` is fuel.  A Main at dyadic index `j < i` carries
the exact number `2^(i-j)-1` of future splits needed to move the whole binary
descendant tree to index `i`.  Whenever hour-`i` fuel is consumed, that debt
drops by exactly one; all other Phase-6 interactions leave the fuel slack
unchanged or improve it.

The entry ledger is deliberately an explicit hypothesis.  In particular,
Phase 5's bare sampled-class floor does not imply it when high Mains are still
present.
-/

import Ripple.PopulationProtocol.ExactMajority.Probability.Phase5Convergence
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase6Convergence

namespace Ripple.PopulationProtocol.ExactMajority
namespace Phase6FuelLedger

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

/-! ## State and configuration observables -/

/-- An hour-`i` Reserve, i.e. one unit of the selected Phase-6 fuel. -/
def IsFuel (i : Fin (L + 1)) (a : AgentState L K) : Prop :=
  a.role = Role.reserve ∧ a.hour.val = i.val

instance (i : Fin (L + 1)) (a : AgentState L K) :
    Decidable (IsFuel (L := L) (K := K) i a) := by
  unfold IsFuel
  infer_instance

/-- Outstanding split work below target index `i`.

A Main at index `j < i` needs `2^(i-j)-1` binary splits to move its entire
descendant tree to index `i`; all other agents carry zero debt. -/
def agentDebt (i : Fin (L + 1)) (a : AgentState L K) : ℕ :=
  if a.role = Role.main then
    match a.bias with
    | Bias.zero => 0
    | Bias.dyadic _ j =>
        if j.val < i.val then 2 ^ (i.val - j.val) - 1 else 0
  else 0

/-- Total outstanding split debt. -/
def splitDebt (i : Fin (L + 1)) (c : Config (AgentState L K)) : ℕ :=
  (c.map (agentDebt (L := L) (K := K) i)).sum

/-- Number of hour-`i` Reserves. -/
def reserveFuel (i : Fin (L + 1)) (c : Config (AgentState L K)) : ℕ :=
  Multiset.countP (IsFuel (L := L) (K := K) i) c

/-- Number of agents that are not hour-`i` Reserves. -/
def nonFuelU (i : Fin (L + 1)) (c : Config (AgentState L K)) : ℕ :=
  Multiset.countP (fun a => ¬ IsFuel (L := L) (K := K) i a) c

/-- Per-agent pressure form of the fuel ledger. -/
def agentPressure (i : Fin (L + 1)) (a : AgentState L K) : ℕ :=
  agentDebt (L := L) (K := K) i a +
    if IsFuel (L := L) (K := K) i a then 0 else 1

/-- Configuration pressure: outstanding debt plus the non-fuel population. -/
def fuelPressure (i : Fin (L + 1)) (c : Config (AgentState L K)) : ℕ :=
  splitDebt (L := L) (K := K) i c + nonFuelU (L := L) (K := K) i c

/-- `K₀` units of selected Reserve fuel remain after paying all outstanding
split debt. -/
def FuelLedger (i : Fin (L + 1)) (K₀ : ℕ)
    (c : Config (AgentState L K)) : Prop :=
  K₀ + splitDebt (L := L) (K := K) i c ≤
    reserveFuel (L := L) (K := K) i c

/-! ## Adjacent-level union ledger

The repair of the printed single-level case split uses the two compatible
Reserve classes `l` and `l+1` together.  Its debt is the work required to move
every Main below the *higher* target `l+1` to that target.  The dynamic theorem
below is only a consumer: producing this ledger at the Phase-5/6 seam remains a
separate sampling-and-mass obligation. -/

/-- A Reserve in either of the adjacent fuel classes `l` or `l+1`. -/
def IsTwoFuel (l : Fin (L + 1)) (a : AgentState L K) : Prop :=
  a.role = Role.reserve ∧
    (a.hour.val = l.val ∨ a.hour.val = l.val + 1)

instance (l : Fin (L + 1)) (a : AgentState L K) :
    Decidable (IsTwoFuel (L := L) (K := K) l a) := by
  unfold IsTwoFuel
  infer_instance

/-- Debt to the higher target `l+1`, written without constructing a `Fin`
successor so that the observable itself has no proof argument. -/
def unionAgentDebt (l : Fin (L + 1)) (a : AgentState L K) : ℕ :=
  if a.role = Role.main then
    match a.bias with
    | Bias.zero => 0
    | Bias.dyadic _ j =>
        if j.val < l.val + 1 then 2 ^ (l.val + 1 - j.val) - 1 else 0
  else 0

/-- Total debt to the higher adjacent target. -/
def unionSplitDebt (l : Fin (L + 1))
    (c : Config (AgentState L K)) : ℕ :=
  (c.map (unionAgentDebt (L := L) (K := K) l)).sum

/-- Number of Reserves in the two adjacent fuel classes. -/
def twoReserveFuel (l : Fin (L + 1))
    (c : Config (AgentState L K)) : ℕ :=
  Multiset.countP (IsTwoFuel (L := L) (K := K) l) c

/-- Number of agents outside the adjacent fuel union. -/
def twoNonFuelU (l : Fin (L + 1))
    (c : Config (AgentState L K)) : ℕ :=
  Multiset.countP (fun a => ¬ IsTwoFuel (L := L) (K := K) l a) c

/-- Pointwise pressure for the adjacent-level union ledger. -/
def twoAgentPressure (l : Fin (L + 1)) (a : AgentState L K) : ℕ :=
  unionAgentDebt (L := L) (K := K) l a +
    if IsTwoFuel (L := L) (K := K) l a then 0 else 1

/-- Union debt plus the population outside the adjacent fuel pool. -/
def twoFuelPressure (l : Fin (L + 1))
    (c : Config (AgentState L K)) : ℕ :=
  unionSplitDebt (L := L) (K := K) l c +
    twoNonFuelU (L := L) (K := K) l c

/-- The adjacent union has `K₀` fuel left after paying all work through target
`l+1`. -/
def UnionFuelLedger (l : Fin (L + 1)) (K₀ : ℕ)
    (c : Config (AgentState L K)) : Prop :=
  K₀ + unionSplitDebt (L := L) (K := K) l c ≤
    twoReserveFuel (L := L) (K := K) l c

/-- The protocol-safe two-level alternative: either the lower class alone pays
the debt through `l`, or the adjacent union pays the debt through `l+1`. -/
def TwoLevelFuelLedger (l : Fin (L + 1)) (K₀ : ℕ)
    (c : Config (AgentState L K)) : Prop :=
  FuelLedger (L := L) (K := K) l K₀ c ∨
    UnionFuelLedger (L := L) (K := K) l K₀ c

/-! ## Counting identities -/

/-- The selected fuel is exactly Phase 5's sampled Reserve class. -/
theorem reserveFuel_eq_sampledReserveClassU
    (i : Fin (L + 1)) (c : Config (AgentState L K)) :
    reserveFuel (L := L) (K := K) i c =
      Phase5Convergence.sampledReserveClassU (L := L) (K := K) i c := by
  rfl

/-- The selected fuel is exactly the count used by the Phase-6 drop rectangle. -/
theorem reserveFuel_eq_reserveAtHour6
    (i : Fin (L + 1)) (c : Config (AgentState L K)) :
    reserveFuel (L := L) (K := K) i c =
      (Phase6Convergence.reserveAtHour6 (L := L) (K := K) i).sum c.count := by
  rw [Phase6Convergence.reserveAtHour6_sum_eq_classU (L := L) (K := K) i c]
  rfl

/-- Fuel plus pressure equals population size plus debt. -/
theorem reserveFuel_add_pressure
    (i : Fin (L + 1)) (c : Config (AgentState L K)) :
    reserveFuel (L := L) (K := K) i c +
        fuelPressure (L := L) (K := K) i c =
      c.card + splitDebt (L := L) (K := K) i c := by
  have hpart := Multiset.card_eq_countP_add_countP
    (p := IsFuel (L := L) (K := K) i) c
  unfold reserveFuel fuelPressure nonFuelU
  omega

/-- Subtraction-free pressure presentation of `FuelLedger`. -/
theorem fuelLedger_iff_pressure
    (i : Fin (L + 1)) (K₀ : ℕ) (c : Config (AgentState L K)) :
    FuelLedger (L := L) (K := K) i K₀ c ↔
      K₀ + fuelPressure (L := L) (K := K) i c ≤ c.card := by
  have hbal := reserveFuel_add_pressure (L := L) (K := K) i c
  unfold FuelLedger
  omega

/-- Split debt is additive over configuration addition. -/
theorem splitDebt_add (i : Fin (L + 1))
    (a b : Config (AgentState L K)) :
    splitDebt (L := L) (K := K) i (a + b) =
      splitDebt (L := L) (K := K) i a +
        splitDebt (L := L) (K := K) i b := by
  unfold splitDebt
  rw [Multiset.map_add, Multiset.sum_add]

/-- Non-fuel count is additive over configuration addition. -/
theorem nonFuelU_add (i : Fin (L + 1))
    (a b : Config (AgentState L K)) :
    nonFuelU (L := L) (K := K) i (a + b) =
      nonFuelU (L := L) (K := K) i a +
        nonFuelU (L := L) (K := K) i b := by
  unfold nonFuelU
  rw [Multiset.countP_add]

@[simp] theorem nonFuelU_singleton (i : Fin (L + 1))
    (x : AgentState L K) :
    nonFuelU (L := L) (K := K) i ({x} : Config (AgentState L K)) =
      if IsFuel (L := L) (K := K) i x then 0 else 1 := by
  unfold nonFuelU
  rw [Multiset.countP_eq_card_filter, Multiset.filter_singleton]
  by_cases hx : IsFuel (L := L) (K := K) i x <;> simp [hx]

/-- Fuel pressure is additive over configuration addition. -/
theorem fuelPressure_add (i : Fin (L + 1))
    (a b : Config (AgentState L K)) :
    fuelPressure (L := L) (K := K) i (a + b) =
      fuelPressure (L := L) (K := K) i a +
        fuelPressure (L := L) (K := K) i b := by
  unfold fuelPressure
  rw [splitDebt_add, nonFuelU_add]
  omega

/-- Pressure of a two-agent configuration is the sum of pointwise pressures. -/
theorem fuelPressure_pair (i : Fin (L + 1))
    (x y : AgentState L K) :
    fuelPressure (L := L) (K := K) i ({x, y} : Config (AgentState L K)) =
      agentPressure (L := L) (K := K) i x +
        agentPressure (L := L) (K := K) i y := by
  classical
  by_cases hx : IsFuel (L := L) (K := K) i x
  · by_cases hy : IsFuel (L := L) (K := K) i y
    · simp [fuelPressure, splitDebt, nonFuelU, agentPressure,
        Multiset.countP_eq_card_filter, Multiset.filter_singleton,
        hx, hy, add_comm]
    · simp [fuelPressure, splitDebt, nonFuelU, agentPressure,
        Multiset.countP_eq_card_filter, Multiset.filter_singleton,
        hx, hy, add_comm]
      omega
  · by_cases hy : IsFuel (L := L) (K := K) i y
    · simp [fuelPressure, splitDebt, nonFuelU, agentPressure,
        Multiset.countP_eq_card_filter, Multiset.filter_singleton,
        hx, hy, add_comm]
      omega
    · simp [fuelPressure, splitDebt, nonFuelU, agentPressure,
        Multiset.countP_eq_card_filter, Multiset.filter_singleton,
        hx, hy, add_comm]
      omega

/-! ### Adjacent-level counting identities -/

/-- The higher target used by the adjacent-level ledger.  The domain condition
keeps both fuel hours strictly below the unset sentinel `L`. -/
def highIndex (l : Fin (L + 1)) (hl : l.val + 2 ≤ L) : Fin (L + 1) :=
  ⟨l.val + 1, by omega⟩

/-- The proof-free union debt is literally the single-level debt at `l+1`. -/
theorem unionAgentDebt_eq_agentDebt_high
    (l : Fin (L + 1)) (hl : l.val + 2 ≤ L) (a : AgentState L K) :
    unionAgentDebt (L := L) (K := K) l a =
      agentDebt (L := L) (K := K) (highIndex l hl) a := by
  unfold unionAgentDebt agentDebt highIndex
  cases a.bias <;> simp

/-- Configuration form of `unionAgentDebt_eq_agentDebt_high`. -/
theorem unionSplitDebt_eq_splitDebt_high
    (l : Fin (L + 1)) (hl : l.val + 2 ≤ L)
    (c : Config (AgentState L K)) :
    unionSplitDebt (L := L) (K := K) l c =
      splitDebt (L := L) (K := K) (highIndex l hl) c := by
  unfold unionSplitDebt splitDebt
  congr 1

/-- The adjacent fuel count is the sum of the two disjoint class counts. -/
theorem twoReserveFuel_eq_reserveFuel_add
    (l : Fin (L + 1)) (hl : l.val + 2 ≤ L)
    (c : Config (AgentState L K)) :
    twoReserveFuel (L := L) (K := K) l c =
      reserveFuel (L := L) (K := K) l c +
        reserveFuel (L := L) (K := K) (highIndex l hl) c := by
  induction c using Multiset.induction_on with
  | empty => simp [twoReserveFuel, reserveFuel]
  | @cons a c ih =>
      unfold twoReserveFuel reserveFuel at ih ⊢
      rw [Multiset.countP_cons, Multiset.countP_cons,
        Multiset.countP_cons, ih]
      by_cases hr : a.role = Role.reserve
      · by_cases hlo : a.hour.val = l.val
        · have hhi : a.hour.val ≠ l.val + 1 := by omega
          simp [IsTwoFuel, IsFuel, highIndex, hr, hlo]
          omega
        · by_cases hhi : a.hour.val = l.val + 1
          · simp [IsTwoFuel, IsFuel, highIndex, hr, hhi]
            omega
          · simp [IsTwoFuel, IsFuel, highIndex, hr, hlo, hhi]
      · simp [IsTwoFuel, IsFuel, highIndex, hr]

/-- The adjacent fuel count is also the sum of the two public Phase-6
`reserveAtHour6` pools. -/
theorem twoReserveFuel_eq_reserveAtHour6_add
    (l : Fin (L + 1)) (hl : l.val + 2 ≤ L)
    (c : Config (AgentState L K)) :
    twoReserveFuel (L := L) (K := K) l c =
      (Phase6Convergence.reserveAtHour6 (L := L) (K := K) l).sum c.count +
        (Phase6Convergence.reserveAtHour6 (L := L) (K := K)
          (highIndex l hl)).sum c.count := by
  rw [twoReserveFuel_eq_reserveFuel_add (L := L) (K := K) l hl c,
    ← reserveFuel_eq_reserveAtHour6 (L := L) (K := K) l c,
    ← reserveFuel_eq_reserveAtHour6 (L := L) (K := K) (highIndex l hl) c]

/-- Adjacent fuel plus adjacent pressure equals population plus higher-target
debt. -/
theorem twoReserveFuel_add_pressure
    (l : Fin (L + 1)) (c : Config (AgentState L K)) :
    twoReserveFuel (L := L) (K := K) l c +
        twoFuelPressure (L := L) (K := K) l c =
      c.card + unionSplitDebt (L := L) (K := K) l c := by
  have hpart := Multiset.card_eq_countP_add_countP
    (p := IsTwoFuel (L := L) (K := K) l) c
  unfold twoReserveFuel twoFuelPressure twoNonFuelU
  omega

/-- Subtraction-free pressure presentation of the adjacent union ledger. -/
theorem unionFuelLedger_iff_pressure
    (l : Fin (L + 1)) (K₀ : ℕ) (c : Config (AgentState L K)) :
    UnionFuelLedger (L := L) (K := K) l K₀ c ↔
      K₀ + twoFuelPressure (L := L) (K := K) l c ≤ c.card := by
  have hbal := twoReserveFuel_add_pressure (L := L) (K := K) l c
  unfold UnionFuelLedger
  omega

theorem unionSplitDebt_add (l : Fin (L + 1))
    (a b : Config (AgentState L K)) :
    unionSplitDebt (L := L) (K := K) l (a + b) =
      unionSplitDebt (L := L) (K := K) l a +
        unionSplitDebt (L := L) (K := K) l b := by
  unfold unionSplitDebt
  rw [Multiset.map_add, Multiset.sum_add]

theorem twoNonFuelU_add (l : Fin (L + 1))
    (a b : Config (AgentState L K)) :
    twoNonFuelU (L := L) (K := K) l (a + b) =
      twoNonFuelU (L := L) (K := K) l a +
        twoNonFuelU (L := L) (K := K) l b := by
  unfold twoNonFuelU
  rw [Multiset.countP_add]

@[simp] theorem twoNonFuelU_singleton (l : Fin (L + 1))
    (x : AgentState L K) :
    twoNonFuelU (L := L) (K := K) l ({x} : Config (AgentState L K)) =
      if IsTwoFuel (L := L) (K := K) l x then 0 else 1 := by
  unfold twoNonFuelU
  rw [Multiset.countP_eq_card_filter, Multiset.filter_singleton]
  by_cases hx : IsTwoFuel (L := L) (K := K) l x <;> simp [hx]

theorem twoFuelPressure_add (l : Fin (L + 1))
    (a b : Config (AgentState L K)) :
    twoFuelPressure (L := L) (K := K) l (a + b) =
      twoFuelPressure (L := L) (K := K) l a +
        twoFuelPressure (L := L) (K := K) l b := by
  unfold twoFuelPressure
  rw [unionSplitDebt_add, twoNonFuelU_add]
  omega

theorem twoFuelPressure_pair (l : Fin (L + 1))
    (x y : AgentState L K) :
    twoFuelPressure (L := L) (K := K) l
        ({x, y} : Config (AgentState L K)) =
      twoAgentPressure (L := L) (K := K) l x +
        twoAgentPressure (L := L) (K := K) l y := by
  classical
  by_cases hx : IsTwoFuel (L := L) (K := K) l x
  · by_cases hy : IsTwoFuel (L := L) (K := K) l y
    · simp [twoFuelPressure, unionSplitDebt, twoNonFuelU, twoAgentPressure,
        Multiset.countP_eq_card_filter, Multiset.filter_singleton,
        hx, hy, add_comm]
    · simp [twoFuelPressure, unionSplitDebt, twoNonFuelU, twoAgentPressure,
        Multiset.countP_eq_card_filter, Multiset.filter_singleton,
        hx, hy, add_comm]
      omega
  · by_cases hy : IsTwoFuel (L := L) (K := K) l y
    · simp [twoFuelPressure, unionSplitDebt, twoNonFuelU, twoAgentPressure,
        Multiset.countP_eq_card_filter, Multiset.filter_singleton,
        hx, hy, add_comm]
      omega
    · simp [twoFuelPressure, unionSplitDebt, twoNonFuelU, twoAgentPressure,
        Multiset.countP_eq_card_filter, Multiset.filter_singleton,
        hx, hy, add_comm]
      omega

/-! ## Exact `doSplit` debt arithmetic -/

/-- An applicable split below target `i` pays exactly one unit of debt. -/
theorem doSplit_agentDebt_pair_drop
    (i : Fin (L + 1)) (r m : AgentState L K)
    {σ : Sign} {j : Fin (L + 1)}
    (hr : r.role = Role.reserve) (hm : m.role = Role.main)
    (hb : m.bias = Bias.dyadic σ j)
    (hne : r.hour.val ≠ L) (hgt : r.hour.val > j.val)
    (hlt : j.val < L) (hji : j.val < i.val) :
    agentDebt (L := L) (K := K) i (doSplit L K r m).1 +
        agentDebt (L := L) (K := K) i (doSplit L K r m).2 + 1 =
      agentDebt (L := L) (K := K) i r +
        agentDebt (L := L) (K := K) i m := by
  rw [Phase6Convergence.doSplit_apply (L := L) (K := K) r m hb hne hgt hlt]
  by_cases hnext : j.val + 1 < i.val
  · have hsub : i.val - j.val = (i.val - (j.val + 1)) + 1 := by omega
    have hp : 1 ≤ (2 : ℕ) ^ (i.val - (j.val + 1)) :=
      one_le_pow₀ (by norm_num)
    simp only [agentDebt]
    simp [hr, hm, hb, hji, hnext, hsub, pow_succ]
    omega
  · have hnextEq : j.val + 1 = i.val := by omega
    have hsub : i.val - j.val = 1 := by omega
    simp [agentDebt, hr, hm, hb, hji, hnextEq, hsub]

/-- A split at or below target `i` carries zero debt before and after. -/
theorem doSplit_agentDebt_pair_eq_of_le
    (i : Fin (L + 1)) (r m : AgentState L K)
    {σ : Sign} {j : Fin (L + 1)}
    (hr : r.role = Role.reserve) (hm : m.role = Role.main)
    (hb : m.bias = Bias.dyadic σ j)
    (hne : r.hour.val ≠ L) (hgt : r.hour.val > j.val)
    (hlt : j.val < L) (hij : i.val ≤ j.val) :
    agentDebt (L := L) (K := K) i (doSplit L K r m).1 +
        agentDebt (L := L) (K := K) i (doSplit L K r m).2 =
      agentDebt (L := L) (K := K) i r +
        agentDebt (L := L) (K := K) i m := by
  rw [Phase6Convergence.doSplit_apply (L := L) (K := K) r m hb hne hgt hlt]
  have hnext : ¬ j.val + 1 < i.val := by omega
  have hj : ¬ j.val < i.val := by omega
  simp [agentDebt, hr, hm, hb, hj, hnext]

/-- Every Reserve-fuelled split is non-increasing for target-`i` debt. -/
theorem doSplit_agentDebt_pair_le
    (i : Fin (L + 1)) (r m : AgentState L K)
    (hr : r.role = Role.reserve) (hm : m.role = Role.main) :
    agentDebt (L := L) (K := K) i (doSplit L K r m).1 +
        agentDebt (L := L) (K := K) i (doSplit L K r m).2 ≤
      agentDebt (L := L) (K := K) i r +
        agentDebt (L := L) (K := K) i m := by
  by_cases happ : Phase6Convergence.DoSplitApplicable (L := L) (K := K) r m
  · obtain ⟨σ, j, hb, hne, hgt, hlt⟩ := happ
    by_cases hji : j.val < i.val
    · have hdrop := doSplit_agentDebt_pair_drop
        (L := L) (K := K) i r m hr hm hb hne hgt hlt hji
      omega
    · exact le_of_eq (doSplit_agentDebt_pair_eq_of_le
        (L := L) (K := K) i r m hr hm hb hne hgt hlt (by omega))
  · rw [Phase6Convergence.doSplit_eq_self_of_not_applicable
      (L := L) (K := K) r m happ]

/-- A Reserve-fuelled split is non-increasing for the subtraction-free pressure.
If the consumed Reserve is selected hour-`i` fuel, debt and fuel both drop by
one; otherwise fuel is unchanged and debt cannot rise. -/
theorem doSplit_agentPressure_pair_le
    (i : Fin (L + 1)) (r m : AgentState L K)
    (hr : r.role = Role.reserve) (hm : m.role = Role.main) :
    agentPressure (L := L) (K := K) i (doSplit L K r m).1 +
        agentPressure (L := L) (K := K) i (doSplit L K r m).2 ≤
      agentPressure (L := L) (K := K) i r +
        agentPressure (L := L) (K := K) i m := by
  by_cases happ : Phase6Convergence.DoSplitApplicable (L := L) (K := K) r m
  · obtain ⟨σ, j, hb, hne, hgt, hlt⟩ := happ
    have happly := Phase6Convergence.doSplit_apply
      (L := L) (K := K) r m hb hne hgt hlt
    by_cases hri : r.hour.val = i.val
    · have hji : j.val < i.val := by omega
      have hdrop := doSplit_agentDebt_pair_drop
        (L := L) (K := K) i r m hr hm hb hne hgt hlt hji
      rw [happly] at hdrop ⊢
      simp only [agentPressure]
      simp [IsFuel, agentDebt, hr, hm, hb, hri] at hdrop ⊢
      omega
    · have hdebt := doSplit_agentDebt_pair_le
        (L := L) (K := K) i r m hr hm
      rw [happly] at hdebt ⊢
      simp only [agentPressure]
      simp [IsFuel, agentDebt, hr, hm, hb, hri] at hdebt ⊢
      omega
  · rw [Phase6Convergence.doSplit_eq_self_of_not_applicable
      (L := L) (K := K) r m happ]

/-! ### Adjacent-level `doSplit` accounting -/

/-- An applicable split below the higher adjacent target pays exactly one unit
of union debt. -/
theorem doSplit_unionAgentDebt_pair_drop
    (l : Fin (L + 1)) (hl : l.val + 2 ≤ L)
    (r m : AgentState L K) {σ : Sign} {j : Fin (L + 1)}
    (hr : r.role = Role.reserve) (hm : m.role = Role.main)
    (hb : m.bias = Bias.dyadic σ j)
    (hne : r.hour.val ≠ L) (hgt : r.hour.val > j.val)
    (hlt : j.val < L) (hji : j.val < l.val + 1) :
    unionAgentDebt (L := L) (K := K) l (doSplit L K r m).1 +
        unionAgentDebt (L := L) (K := K) l (doSplit L K r m).2 + 1 =
      unionAgentDebt (L := L) (K := K) l r +
        unionAgentDebt (L := L) (K := K) l m := by
  simpa only [unionAgentDebt_eq_agentDebt_high (L := L) (K := K) l hl] using
    (doSplit_agentDebt_pair_drop
      (L := L) (K := K) (highIndex l hl) r m hr hm hb hne hgt hlt hji)

/-- Union debt cannot increase under any Reserve-fuelled split. -/
theorem doSplit_unionAgentDebt_pair_le
    (l : Fin (L + 1)) (hl : l.val + 2 ≤ L)
    (r m : AgentState L K)
    (hr : r.role = Role.reserve) (hm : m.role = Role.main) :
    unionAgentDebt (L := L) (K := K) l (doSplit L K r m).1 +
        unionAgentDebt (L := L) (K := K) l (doSplit L K r m).2 ≤
      unionAgentDebt (L := L) (K := K) l r +
        unionAgentDebt (L := L) (K := K) l m := by
  simpa only [unionAgentDebt_eq_agentDebt_high (L := L) (K := K) l hl] using
    (doSplit_agentDebt_pair_le
      (L := L) (K := K) (highIndex l hl) r m hr hm)

/-- Consuming either adjacent fuel class pays one unit of higher-target debt;
consuming any other Reserve cannot increase adjacent pressure. -/
theorem doSplit_twoAgentPressure_pair_le
    (l : Fin (L + 1)) (hl : l.val + 2 ≤ L)
    (r m : AgentState L K)
    (hr : r.role = Role.reserve) (hm : m.role = Role.main) :
    twoAgentPressure (L := L) (K := K) l (doSplit L K r m).1 +
        twoAgentPressure (L := L) (K := K) l (doSplit L K r m).2 ≤
      twoAgentPressure (L := L) (K := K) l r +
        twoAgentPressure (L := L) (K := K) l m := by
  by_cases happ : Phase6Convergence.DoSplitApplicable (L := L) (K := K) r m
  · obtain ⟨σ, j, hb, hne, hgt, hlt⟩ := happ
    have happly := Phase6Convergence.doSplit_apply
      (L := L) (K := K) r m hb hne hgt hlt
    have hmnot : ¬ IsTwoFuel (L := L) (K := K) l m := by
      simp [IsTwoFuel, hm]
    have hout1 : ¬ IsTwoFuel (L := L) (K := K) l (doSplit L K r m).1 := by
      rw [happly]
      simp [IsTwoFuel]
    have hout2 : ¬ IsTwoFuel (L := L) (K := K) l (doSplit L K r m).2 := by
      rw [happly]
      simp [IsTwoFuel, hm]
    by_cases hrfuel : IsTwoFuel (L := L) (K := K) l r
    · have hji : j.val < l.val + 1 := by
        rcases hrfuel.2 with hlo | hhi <;> omega
      have hdrop := doSplit_unionAgentDebt_pair_drop
        (L := L) (K := K) l hl r m hr hm hb hne hgt hlt hji
      simp only [twoAgentPressure]
      simp only [if_pos hrfuel, if_neg hmnot, if_neg hout1, if_neg hout2]
      omega
    · have hdebt := doSplit_unionAgentDebt_pair_le
        (L := L) (K := K) l hl r m hr hm
      simp only [twoAgentPressure]
      simp only [if_neg hrfuel, if_neg hmnot, if_neg hout1, if_neg hout2]
      omega
  · rw [Phase6Convergence.doSplit_eq_self_of_not_applicable
      (L := L) (K := K) r m happ]

/-! ## Phase-6 dispatch -/

/-- The trailing clock branch preserves pressure.  In the active branch the
agent is a Clock both before and after, hence carries neither debt nor fuel. -/
theorem clockBranch_agentPressure_eq
    (i : Fin (L + 1)) (a : AgentState L K) (ha : 5 ≤ a.phase.val) :
    agentPressure (L := L) (K := K) i
        (if a.role = Role.clock then stdCounterSubroutine L K a else a) =
      agentPressure (L := L) (K := K) i a := by
  by_cases hc : a.role = Role.clock
  · rw [if_pos hc]
    have hrole := Phase6Convergence.stdCounterSubroutine_role_ge_five6
      (L := L) (K := K) a ha
    simp [agentPressure, agentDebt, IsFuel, hc]
  · rw [if_neg hc]

/-- Per-pair pressure non-increase under the actual Phase-6 dispatch. -/
theorem Phase6Transition_agentPressure_pair_le
    (i : Fin (L + 1)) (s t : AgentState L K)
    (hs6 : 6 ≤ s.phase.val) (ht6 : 6 ≤ t.phase.val) :
    agentPressure (L := L) (K := K) i (Phase6Transition L K s t).1 +
        agentPressure (L := L) (K := K) i (Phase6Transition L K s t).2 ≤
      agentPressure (L := L) (K := K) i s +
        agentPressure (L := L) (K := K) i t := by
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
      agentPressure (L := L) (K := K) i s1 +
          agentPressure (L := L) (K := K) i t1 ≤
        agentPressure (L := L) (K := K) i s +
          agentPressure (L := L) (K := K) i t := by
    rw [hs1def, ht1def]
    split_ifs with h1 h2
    · exact doSplit_agentPressure_pair_le
        (L := L) (K := K) i s t h1.1 h1.2.1
    · simpa [add_comm] using
        (doSplit_agentPressure_pair_le
          (L := L) (K := K) i t s h2.1 h2.2.1)
    · exact le_rfl
  have hs1p : 6 ≤ s1.phase.val := by
    rw [hs1def]
    split_ifs with h1 h2
    · rw [Phase6Convergence.doSplit_phase_fst_eq (L := L) (K := K) s t]
      exact hs6
    · rw [Phase6Convergence.doSplit_phase_snd_eq (L := L) (K := K) t s]
      exact hs6
    · exact hs6
  have ht1p : 6 ≤ t1.phase.val := by
    rw [ht1def]
    split_ifs with h1 h2
    · rw [Phase6Convergence.doSplit_phase_snd_eq (L := L) (K := K) s t]
      exact ht6
    · rw [Phase6Convergence.doSplit_phase_fst_eq (L := L) (K := K) t s]
      exact ht6
    · exact ht6
  rw [clockBranch_agentPressure_eq (L := L) (K := K) i s1 (by omega),
      clockBranch_agentPressure_eq (L := L) (K := K) i t1 (by omega)]
  exact hpre

/-- On a phase-6 pair, the full protocol transition has non-increasing pressure. -/
theorem Transition_agentPressure_pair_le_of_phase6
    (i : Fin (L + 1)) (s t : AgentState L K)
    (hs : s.phase.val = 6) (ht : t.phase.val = 6) :
    agentPressure (L := L) (K := K) i (Transition L K s t).1 +
        agentPressure (L := L) (K := K) i (Transition L K s t).2 ≤
      agentPressure (L := L) (K := K) i s +
        agentPressure (L := L) (K := K) i t := by
  rw [Phase6Convergence.Transition_eq_Phase6Transition_of_phase6
    (L := L) (K := K) s t hs ht]
  exact Phase6Transition_agentPressure_pair_le
    (L := L) (K := K) i s t (by omega) (by omega)

/-- The trailing clock branch also preserves adjacent-union pressure. -/
theorem clockBranch_twoAgentPressure_eq
    (l : Fin (L + 1)) (a : AgentState L K) (ha : 5 ≤ a.phase.val) :
    twoAgentPressure (L := L) (K := K) l
        (if a.role = Role.clock then stdCounterSubroutine L K a else a) =
      twoAgentPressure (L := L) (K := K) l a := by
  by_cases hc : a.role = Role.clock
  · rw [if_pos hc]
    have hrole := Phase6Convergence.stdCounterSubroutine_role_ge_five6
      (L := L) (K := K) a ha
    simp [twoAgentPressure, unionAgentDebt, IsTwoFuel, hc]
  · rw [if_neg hc]

/-- Adjacent-union pressure is non-increasing under the actual Phase-6
dispatch. -/
theorem Phase6Transition_twoAgentPressure_pair_le
    (l : Fin (L + 1)) (hl : l.val + 2 ≤ L)
    (s t : AgentState L K)
    (hs6 : 6 ≤ s.phase.val) (ht6 : 6 ≤ t.phase.val) :
    twoAgentPressure (L := L) (K := K) l (Phase6Transition L K s t).1 +
        twoAgentPressure (L := L) (K := K) l (Phase6Transition L K s t).2 ≤
      twoAgentPressure (L := L) (K := K) l s +
        twoAgentPressure (L := L) (K := K) l t := by
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
      twoAgentPressure (L := L) (K := K) l s1 +
          twoAgentPressure (L := L) (K := K) l t1 ≤
        twoAgentPressure (L := L) (K := K) l s +
          twoAgentPressure (L := L) (K := K) l t := by
    rw [hs1def, ht1def]
    split_ifs with h1 h2
    · exact doSplit_twoAgentPressure_pair_le
        (L := L) (K := K) l hl s t h1.1 h1.2.1
    · simpa [add_comm] using
        (doSplit_twoAgentPressure_pair_le
          (L := L) (K := K) l hl t s h2.1 h2.2.1)
    · exact le_rfl
  have hs1p : 6 ≤ s1.phase.val := by
    rw [hs1def]
    split_ifs with h1 h2
    · rw [Phase6Convergence.doSplit_phase_fst_eq (L := L) (K := K) s t]
      exact hs6
    · rw [Phase6Convergence.doSplit_phase_snd_eq (L := L) (K := K) t s]
      exact hs6
    · exact hs6
  have ht1p : 6 ≤ t1.phase.val := by
    rw [ht1def]
    split_ifs with h1 h2
    · rw [Phase6Convergence.doSplit_phase_snd_eq (L := L) (K := K) s t]
      exact ht6
    · rw [Phase6Convergence.doSplit_phase_fst_eq (L := L) (K := K) t s]
      exact ht6
    · exact ht6
  rw [clockBranch_twoAgentPressure_eq (L := L) (K := K) l s1 (by omega),
      clockBranch_twoAgentPressure_eq (L := L) (K := K) l t1 (by omega)]
  exact hpre

/-- Full-protocol adjacent pressure non-increase on a phase-6 pair. -/
theorem Transition_twoAgentPressure_pair_le_of_phase6
    (l : Fin (L + 1)) (hl : l.val + 2 ≤ L)
    (s t : AgentState L K)
    (hs : s.phase.val = 6) (ht : t.phase.val = 6) :
    twoAgentPressure (L := L) (K := K) l (Transition L K s t).1 +
        twoAgentPressure (L := L) (K := K) l (Transition L K s t).2 ≤
      twoAgentPressure (L := L) (K := K) l s +
        twoAgentPressure (L := L) (K := K) l t := by
  rw [Phase6Convergence.Transition_eq_Phase6Transition_of_phase6
    (L := L) (K := K) s t hs ht]
  exact Phase6Transition_twoAgentPressure_pair_le
    (L := L) (K := K) l hl s t (by omega) (by omega)

private theorem mem_of_app_left6Fuel {c : Config (AgentState L K)}
    {r₁ r₂ : AgentState L K} (happ : Protocol.Applicable c r₁ r₂) : r₁ ∈ c :=
  Multiset.mem_of_le
    (show ({r₁, r₂} : Multiset (AgentState L K)) ≤ c from happ) (by simp)

private theorem mem_of_app_right6Fuel {c : Config (AgentState L K)}
    {r₁ r₂ : AgentState L K} (happ : Protocol.Applicable c r₁ r₂) : r₂ ∈ c :=
  Multiset.mem_of_le
    (show ({r₁, r₂} : Multiset (AgentState L K)) ≤ c from happ) (by simp)

/-- Fuel pressure is non-increasing under every chosen-pair update starting in
the exact Phase-6 window. -/
theorem fuelPressure_stepOrSelf_le
    (i : Fin (L + 1)) (n : ℕ) (c : Config (AgentState L K))
    (hwin : Phase6Convergence.Phase6Win (L := L) (K := K) n c)
    (r₁ r₂ : AgentState L K) :
    fuelPressure (L := L) (K := K) i
        (Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂) ≤
      fuelPressure (L := L) (K := K) i c := by
  obtain ⟨_, hphase⟩ := hwin
  by_cases happ : Protocol.Applicable c r₁ r₂
  · have hm1 := mem_of_app_left6Fuel happ
    have hm2 := mem_of_app_right6Fuel happ
    have h16 : r₁.phase.val = 6 := hphase r₁ hm1
    have h26 : r₂.phase.val = 6 := hphase r₂ hm2
    have hsub : ({r₁, r₂} : Multiset (AgentState L K)) ≤ c := happ
    have hc' : Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂ =
        c - {r₁, r₂} + {(Transition L K r₁ r₂).1,
          (Transition L K r₁ r₂).2} := by
      unfold Protocol.stepOrSelf
      rw [if_pos happ]
      rfl
    have hcsplit : c = (c - {r₁, r₂}) + {r₁, r₂} :=
      (tsub_add_cancel_of_le hsub).symm
    have hpair : fuelPressure (L := L) (K := K) i
          ({(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2} :
            Config (AgentState L K)) ≤
        fuelPressure (L := L) (K := K) i
          ({r₁, r₂} : Config (AgentState L K)) := by
      rw [fuelPressure_pair, fuelPressure_pair]
      exact Transition_agentPressure_pair_le_of_phase6
        (L := L) (K := K) i r₁ r₂ h16 h26
    rw [hc', fuelPressure_add]
    calc
      fuelPressure (L := L) (K := K) i (c - {r₁, r₂}) +
            fuelPressure (L := L) (K := K) i
              ({(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2} :
                Config (AgentState L K))
          ≤ fuelPressure (L := L) (K := K) i (c - {r₁, r₂}) +
              fuelPressure (L := L) (K := K) i
                ({r₁, r₂} : Config (AgentState L K)) :=
            Nat.add_le_add_left hpair _
      _ = fuelPressure (L := L) (K := K) i c := by
            rw [← fuelPressure_add, ← hcsplit]
  · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]

/-- The selected-fuel ledger is preserved by every chosen-pair update from the
exact Phase-6 window. -/
theorem fuelLedger_stepOrSelf
    (i : Fin (L + 1)) (K₀ n : ℕ) (c : Config (AgentState L K))
    (hwin : Phase6Convergence.Phase6Win (L := L) (K := K) n c)
    (hledger : FuelLedger (L := L) (K := K) i K₀ c)
    (r₁ r₂ : AgentState L K) :
    FuelLedger (L := L) (K := K) i K₀
      (Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂) := by
  rw [fuelLedger_iff_pressure] at hledger ⊢
  have hp := fuelPressure_stepOrSelf_le
    (L := L) (K := K) i n c hwin r₁ r₂
  have hcard := Protocol.stepOrSelf_card_eq
    (P := NonuniformMajority L K) c r₁ r₂
  omega

/-- Adjacent-union pressure is non-increasing under every chosen-pair update in
the exact Phase-6 window. -/
theorem twoFuelPressure_stepOrSelf_le
    (l : Fin (L + 1)) (hl : l.val + 2 ≤ L)
    (n : ℕ) (c : Config (AgentState L K))
    (hwin : Phase6Convergence.Phase6Win (L := L) (K := K) n c)
    (r₁ r₂ : AgentState L K) :
    twoFuelPressure (L := L) (K := K) l
        (Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂) ≤
      twoFuelPressure (L := L) (K := K) l c := by
  obtain ⟨_, hphase⟩ := hwin
  by_cases happ : Protocol.Applicable c r₁ r₂
  · have hm1 := mem_of_app_left6Fuel happ
    have hm2 := mem_of_app_right6Fuel happ
    have h16 : r₁.phase.val = 6 := hphase r₁ hm1
    have h26 : r₂.phase.val = 6 := hphase r₂ hm2
    have hsub : ({r₁, r₂} : Multiset (AgentState L K)) ≤ c := happ
    have hc' : Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂ =
        c - {r₁, r₂} + {(Transition L K r₁ r₂).1,
          (Transition L K r₁ r₂).2} := by
      unfold Protocol.stepOrSelf
      rw [if_pos happ]
      rfl
    have hcsplit : c = (c - {r₁, r₂}) + {r₁, r₂} :=
      (tsub_add_cancel_of_le hsub).symm
    have hpair : twoFuelPressure (L := L) (K := K) l
          ({(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2} :
            Config (AgentState L K)) ≤
        twoFuelPressure (L := L) (K := K) l
          ({r₁, r₂} : Config (AgentState L K)) := by
      rw [twoFuelPressure_pair, twoFuelPressure_pair]
      exact Transition_twoAgentPressure_pair_le_of_phase6
        (L := L) (K := K) l hl r₁ r₂ h16 h26
    rw [hc', twoFuelPressure_add]
    calc
      twoFuelPressure (L := L) (K := K) l (c - {r₁, r₂}) +
            twoFuelPressure (L := L) (K := K) l
              ({(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2} :
                Config (AgentState L K))
          ≤ twoFuelPressure (L := L) (K := K) l (c - {r₁, r₂}) +
              twoFuelPressure (L := L) (K := K) l
                ({r₁, r₂} : Config (AgentState L K)) :=
            Nat.add_le_add_left hpair _
      _ = twoFuelPressure (L := L) (K := K) l c := by
            rw [← twoFuelPressure_add, ← hcsplit]
  · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]

/-- The adjacent union ledger is preserved by each Phase-6 chosen-pair
update. -/
theorem unionFuelLedger_stepOrSelf
    (l : Fin (L + 1)) (hl : l.val + 2 ≤ L)
    (K₀ n : ℕ) (c : Config (AgentState L K))
    (hwin : Phase6Convergence.Phase6Win (L := L) (K := K) n c)
    (hledger : UnionFuelLedger (L := L) (K := K) l K₀ c)
    (r₁ r₂ : AgentState L K) :
    UnionFuelLedger (L := L) (K := K) l K₀
      (Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂) := by
  rw [unionFuelLedger_iff_pressure] at hledger ⊢
  have hp := twoFuelPressure_stepOrSelf_le
    (L := L) (K := K) l hl n c hwin r₁ r₂
  have hcard := Protocol.stepOrSelf_card_eq
    (P := NonuniformMajority L K) c r₁ r₂
  omega

/-- The lower-or-union dichotomy is itself closed by Phase 6. -/
theorem twoLevelFuelLedger_stepOrSelf
    (l : Fin (L + 1)) (hl : l.val + 2 ≤ L)
    (K₀ n : ℕ) (c : Config (AgentState L K))
    (hwin : Phase6Convergence.Phase6Win (L := L) (K := K) n c)
    (hledger : TwoLevelFuelLedger (L := L) (K := K) l K₀ c)
    (r₁ r₂ : AgentState L K) :
    TwoLevelFuelLedger (L := L) (K := K) l K₀
      (Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂) := by
  rcases hledger with hlow | hunion
  · exact Or.inl (fuelLedger_stepOrSelf
      (L := L) (K := K) l K₀ n c hwin hlow r₁ r₂)
  · exact Or.inr (unionFuelLedger_stepOrSelf
      (L := L) (K := K) l hl K₀ n c hwin hunion r₁ r₂)

/-! ## Live pool floors -/

/-- A single-level ledger exposes its selected-class floor. -/
theorem fuelLedger_reserveFuel_floor
    (i : Fin (L + 1)) (K₀ : ℕ) (c : Config (AgentState L K))
    (h : FuelLedger (L := L) (K := K) i K₀ c) :
    K₀ ≤ reserveFuel (L := L) (K := K) i c := by
  unfold FuelLedger at h
  omega

/-- A union ledger exposes its live adjacent-pool floor. -/
theorem unionFuelLedger_twoReserveFuel_floor
    (l : Fin (L + 1)) (K₀ : ℕ) (c : Config (AgentState L K))
    (h : UnionFuelLedger (L := L) (K := K) l K₀ c) :
    K₀ ≤ twoReserveFuel (L := L) (K := K) l c := by
  unfold UnionFuelLedger at h
  omega

/-- The exact consumer-facing dichotomy: either the lower class has the floor,
or the adjacent union has it. -/
theorem twoLevelFuelLedger_floor_dichotomy
    (l : Fin (L + 1)) (K₀ : ℕ) (c : Config (AgentState L K))
    (h : TwoLevelFuelLedger (L := L) (K := K) l K₀ c) :
    K₀ ≤ reserveFuel (L := L) (K := K) l c ∨
      K₀ ≤ twoReserveFuel (L := L) (K := K) l c := by
  rcases h with hlow | hunion
  · exact Or.inl (fuelLedger_reserveFuel_floor
      (L := L) (K := K) l K₀ c hlow)
  · exact Or.inr (unionFuelLedger_twoReserveFuel_floor
      (L := L) (K := K) l K₀ c hunion)

/-- A lower-class floor is in particular an adjacent-union floor. -/
theorem reserveFuel_le_twoReserveFuel
    (l : Fin (L + 1)) (hl : l.val + 2 ≤ L)
    (c : Config (AgentState L K)) :
    reserveFuel (L := L) (K := K) l c ≤
      twoReserveFuel (L := L) (K := K) l c := by
  rw [twoReserveFuel_eq_reserveFuel_add (L := L) (K := K) l hl c]
  omega

/-- Either branch of the two-level ledger therefore supplies the union pool. -/
theorem twoLevelFuelLedger_union_floor
    (l : Fin (L + 1)) (hl : l.val + 2 ≤ L)
    (K₀ : ℕ) (c : Config (AgentState L K))
    (h : TwoLevelFuelLedger (L := L) (K := K) l K₀ c) :
    K₀ ≤ twoReserveFuel (L := L) (K := K) l c := by
  rcases twoLevelFuelLedger_floor_dichotomy
      (L := L) (K := K) l K₀ c h with hlow | hunion
  · exact le_trans hlow (reserveFuel_le_twoReserveFuel
      (L := L) (K := K) l hl c)
  · exact hunion

/-! ## Kernel-support closure -/

/-- Every one-step support point from a Phase-6 ledger state still satisfies
the same ledger. -/
theorem fuelLedger_of_mem_stepDistOrSelf_support
    (i : Fin (L + 1)) (K₀ n : ℕ) (c c' : Config (AgentState L K))
    (hwin : Phase6Convergence.Phase6Win (L := L) (K := K) n c)
    (hledger : FuelLedger (L := L) (K := K) i K₀ c)
    (hc' : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    FuelLedger (L := L) (K := K) i K₀ c' := by
  by_cases hc : 2 ≤ c.card
  · rw [show (NonuniformMajority L K).stepDistOrSelf c =
        (NonuniformMajority L K).stepDist c hc by
      unfold Protocol.stepDistOrSelf
      rw [dif_pos hc]] at hc'
    obtain ⟨⟨r₁, r₂⟩, hr⟩ :=
      Protocol.stepDist_support (NonuniformMajority L K) c hc c' hc'
    rw [← hr]
    exact fuelLedger_stepOrSelf
      (L := L) (K := K) i K₀ n c hwin hledger r₁ r₂
  · rw [show (NonuniformMajority L K).stepDistOrSelf c = PMF.pure c by
      unfold Protocol.stepDistOrSelf
      rw [dif_neg hc]] at hc'
    rw [PMF.mem_support_pure_iff] at hc'
    subst c'
    exact hledger

/-- Every one-step support point preserves the adjacent union ledger. -/
theorem unionFuelLedger_of_mem_stepDistOrSelf_support
    (l : Fin (L + 1)) (hl : l.val + 2 ≤ L)
    (K₀ n : ℕ) (c c' : Config (AgentState L K))
    (hwin : Phase6Convergence.Phase6Win (L := L) (K := K) n c)
    (hledger : UnionFuelLedger (L := L) (K := K) l K₀ c)
    (hc' : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    UnionFuelLedger (L := L) (K := K) l K₀ c' := by
  by_cases hc : 2 ≤ c.card
  · rw [show (NonuniformMajority L K).stepDistOrSelf c =
        (NonuniformMajority L K).stepDist c hc by
      unfold Protocol.stepDistOrSelf
      rw [dif_pos hc]] at hc'
    obtain ⟨⟨r₁, r₂⟩, hr⟩ :=
      Protocol.stepDist_support (NonuniformMajority L K) c hc c' hc'
    rw [← hr]
    exact unionFuelLedger_stepOrSelf
      (L := L) (K := K) l hl K₀ n c hwin hledger r₁ r₂
  · rw [show (NonuniformMajority L K).stepDistOrSelf c = PMF.pure c by
      unfold Protocol.stepDistOrSelf
      rw [dif_neg hc]] at hc'
    rw [PMF.mem_support_pure_iff] at hc'
    subst c'
    exact hledger

/-- Every one-step support point preserves the lower-or-union alternative. -/
theorem twoLevelFuelLedger_of_mem_stepDistOrSelf_support
    (l : Fin (L + 1)) (hl : l.val + 2 ≤ L)
    (K₀ n : ℕ) (c c' : Config (AgentState L K))
    (hwin : Phase6Convergence.Phase6Win (L := L) (K := K) n c)
    (hledger : TwoLevelFuelLedger (L := L) (K := K) l K₀ c)
    (hc' : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    TwoLevelFuelLedger (L := L) (K := K) l K₀ c' := by
  by_cases hc : 2 ≤ c.card
  · rw [show (NonuniformMajority L K).stepDistOrSelf c =
        (NonuniformMajority L K).stepDist c hc by
      unfold Protocol.stepDistOrSelf
      rw [dif_pos hc]] at hc'
    obtain ⟨⟨r₁, r₂⟩, hr⟩ :=
      Protocol.stepDist_support (NonuniformMajority L K) c hc c' hc'
    rw [← hr]
    exact twoLevelFuelLedger_stepOrSelf
      (L := L) (K := K) l hl K₀ n c hwin hledger r₁ r₂
  · rw [show (NonuniformMajority L K).stepDistOrSelf c = PMF.pure c by
      unfold Protocol.stepDistOrSelf
      rw [dif_neg hc]] at hc'
    rw [PMF.mem_support_pure_iff] at hc'
    subst c'
    exact hledger

/-- Support-local consumer form: every successor has either the lower-class
floor or the adjacent-union floor. -/
theorem twoLevelFuelLedger_support_floor_dichotomy
    (l : Fin (L + 1)) (hl : l.val + 2 ≤ L)
    (K₀ n : ℕ) (c c' : Config (AgentState L K))
    (hwin : Phase6Convergence.Phase6Win (L := L) (K := K) n c)
    (hledger : TwoLevelFuelLedger (L := L) (K := K) l K₀ c)
    (hc' : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    K₀ ≤ reserveFuel (L := L) (K := K) l c' ∨
      K₀ ≤ twoReserveFuel (L := L) (K := K) l c' := by
  exact twoLevelFuelLedger_floor_dichotomy
    (L := L) (K := K) l K₀ c'
    (twoLevelFuelLedger_of_mem_stepDistOrSelf_support
      (L := L) (K := K) l hl K₀ n c c' hwin hledger hc')

/-- Support-local union-pool floor, independent of which ledger branch holds. -/
theorem twoLevelFuelLedger_support_union_floor
    (l : Fin (L + 1)) (hl : l.val + 2 ≤ L)
    (K₀ n : ℕ) (c c' : Config (AgentState L K))
    (hwin : Phase6Convergence.Phase6Win (L := L) (K := K) n c)
    (hledger : TwoLevelFuelLedger (L := L) (K := K) l K₀ c)
    (hc' : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    K₀ ≤ twoReserveFuel (L := L) (K := K) l c' := by
  exact twoLevelFuelLedger_union_floor
    (L := L) (K := K) l hl K₀ c'
    (twoLevelFuelLedger_of_mem_stepDistOrSelf_support
      (L := L) (K := K) l hl K₀ n c c' hwin hledger hc')

/-- The real one-step kernel has zero mass on fuel-ledger failure. -/
theorem transitionKernel_not_fuelLedger_eq_zero
    (i : Fin (L + 1)) (K₀ n : ℕ) (c : Config (AgentState L K))
    (hwin : Phase6Convergence.Phase6Win (L := L) (K := K) n c)
    (hledger : FuelLedger (L := L) (K := K) i K₀ c) :
    (NonuniformMajority L K).transitionKernel c
      {c' | ¬ FuelLedger (L := L) (K := K) i K₀ c'} = 0 := by
  change ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
    {c' | ¬ FuelLedger (L := L) (K := K) i K₀ c'} = 0
  rw [PMF.toMeasure_apply_eq_zero_iff _
    (DiscreteMeasurableSpace.forall_measurableSet _)]
  rw [Set.disjoint_left]
  intro c' hsupp hbad
  exact hbad (fuelLedger_of_mem_stepDistOrSelf_support
    (L := L) (K := K) i K₀ n c c' hwin hledger hsupp)

/-- The real one-step kernel has zero mass on adjacent-union ledger failure. -/
theorem transitionKernel_not_unionFuelLedger_eq_zero
    (l : Fin (L + 1)) (hl : l.val + 2 ≤ L)
    (K₀ n : ℕ) (c : Config (AgentState L K))
    (hwin : Phase6Convergence.Phase6Win (L := L) (K := K) n c)
    (hledger : UnionFuelLedger (L := L) (K := K) l K₀ c) :
    (NonuniformMajority L K).transitionKernel c
      {c' | ¬ UnionFuelLedger (L := L) (K := K) l K₀ c'} = 0 := by
  change ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
    {c' | ¬ UnionFuelLedger (L := L) (K := K) l K₀ c'} = 0
  rw [PMF.toMeasure_apply_eq_zero_iff _
    (DiscreteMeasurableSpace.forall_measurableSet _)]
  rw [Set.disjoint_left]
  intro c' hsupp hbad
  exact hbad (unionFuelLedger_of_mem_stepDistOrSelf_support
    (L := L) (K := K) l hl K₀ n c c' hwin hledger hsupp)

/-- The real one-step kernel has zero mass on failure of the complete two-level
alternative. -/
theorem transitionKernel_not_twoLevelFuelLedger_eq_zero
    (l : Fin (L + 1)) (hl : l.val + 2 ≤ L)
    (K₀ n : ℕ) (c : Config (AgentState L K))
    (hwin : Phase6Convergence.Phase6Win (L := L) (K := K) n c)
    (hledger : TwoLevelFuelLedger (L := L) (K := K) l K₀ c) :
    (NonuniformMajority L K).transitionKernel c
      {c' | ¬ TwoLevelFuelLedger (L := L) (K := K) l K₀ c'} = 0 := by
  change ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
    {c' | ¬ TwoLevelFuelLedger (L := L) (K := K) l K₀ c'} = 0
  rw [PMF.toMeasure_apply_eq_zero_iff _
    (DiscreteMeasurableSpace.forall_measurableSet _)]
  rw [Set.disjoint_left]
  intro c' hsupp hbad
  exact hbad (twoLevelFuelLedger_of_mem_stepDistOrSelf_support
    (L := L) (K := K) l hl K₀ n c c' hwin hledger hsupp)

/-! ## Axiom audit -/

#print axioms reserveFuel_add_pressure
#print axioms fuelLedger_iff_pressure
#print axioms doSplit_agentDebt_pair_drop
#print axioms doSplit_agentPressure_pair_le
#print axioms Phase6Transition_agentPressure_pair_le
#print axioms fuelPressure_stepOrSelf_le
#print axioms fuelLedger_stepOrSelf
#print axioms transitionKernel_not_fuelLedger_eq_zero
#print axioms twoReserveFuel_add_pressure
#print axioms unionFuelLedger_iff_pressure
#print axioms doSplit_unionAgentDebt_pair_drop
#print axioms doSplit_twoAgentPressure_pair_le
#print axioms Phase6Transition_twoAgentPressure_pair_le
#print axioms twoFuelPressure_stepOrSelf_le
#print axioms unionFuelLedger_stepOrSelf
#print axioms twoLevelFuelLedger_stepOrSelf
#print axioms twoLevelFuelLedger_support_floor_dichotomy
#print axioms transitionKernel_not_unionFuelLedger_eq_zero
#print axioms transitionKernel_not_twoLevelFuelLedger_eq_zero

end Phase6FuelLedger
end Ripple.PopulationProtocol.ExactMajority
