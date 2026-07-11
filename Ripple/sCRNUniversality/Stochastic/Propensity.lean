import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.NNRat.BigOperators
import Mathlib.Tactic
import Ripple.sCRNUniversality.Core.Run

open scoped BigOperators

namespace Ripple.sCRNUniversality

namespace Reaction

variable {S : Type u} [Fintype S]

def propensity (rho : Reaction S) (z : State S) : Rate :=
  rho.k * Finset.univ.prod (fun s => (Nat.choose (z s) (rho.l s) : Rate))

theorem choose_cast_eq_zero_of_lt {n k : Nat} (h : n < k) :
    (Nat.choose n k : Rate) = 0 := by
  simp [Nat.choose_eq_zero_of_lt h]

theorem choose_cast_coe_pos_of_le {n k : Nat} (h : k <= n) :
    0 < ((Nat.choose n k : Rate) : Rat) := by
  have hNat : 0 < Nat.choose n k := Nat.choose_pos h
  exact_mod_cast hNat

theorem propensity_coe (rho : Reaction S) (z : State S) :
    ((rho.propensity z : Rate) : Rat) =
      (rho.k : Rat) *
        Finset.univ.prod
          (fun s : S => ((Nat.choose (z s) (rho.l s) : Rate) : Rat)) := by
  simp [propensity, NNRat.cast_prod]

theorem propensity_eq_zero_of_not_enabled {rho : Reaction S} {z : State S}
    (hnot : ¬ rho.enabled z) :
    rho.propensity z = 0 := by
  classical
  rcases not_forall.mp hnot with ⟨s, hs⟩
  have hlt : z s < rho.l s := Nat.lt_of_not_ge hs
  have hchoose : (Nat.choose (z s) (rho.l s) : Rate) = 0 :=
    choose_cast_eq_zero_of_lt hlt
  unfold propensity
  rw [Finset.prod_eq_zero (Finset.mem_univ s) hchoose, mul_zero]

theorem propensity_coe_pos_of_enabled_of_positive_rate
    {rho : Reaction S} {z : State S}
    (hen : rho.enabled z) (hk : rho.hasPositiveRate) :
    0 < ((rho.propensity z : Rate) : Rat) := by
  rw [propensity_coe]
  have hkRat : 0 < (rho.k : Rat) := (NNRat.coe_pos).2 hk
  refine mul_pos hkRat ?_
  refine Finset.prod_pos ?_
  intro s _hs
  exact choose_cast_coe_pos_of_le (hen s)

theorem propensity_pos_of_enabled_of_positive_rate
    {rho : Reaction S} {z : State S}
    (hen : rho.enabled z) (hk : rho.hasPositiveRate) :
    0 < rho.propensity z :=
  (NNRat.coe_pos).1
    (propensity_coe_pos_of_enabled_of_positive_rate hen hk)

theorem propensity_ne_zero_of_enabled_of_positive_rate
    {rho : Reaction S} {z : State S}
    (hen : rho.enabled z) (hk : rho.hasPositiveRate) :
    rho.propensity z ≠ 0 :=
  ne_of_gt (propensity_pos_of_enabled_of_positive_rate hen hk)

theorem not_enabled_of_propensity_eq_zero_of_positive_rate
    {rho : Reaction S} {z : State S}
    (hk : rho.hasPositiveRate)
    (hzero : rho.propensity z = 0) :
    ¬ rho.enabled z := by
  intro hen
  exact propensity_ne_zero_of_enabled_of_positive_rate hen hk hzero

theorem propensity_eq_zero_iff_not_enabled_of_positive_rate
    {rho : Reaction S} {z : State S}
    (hk : rho.hasPositiveRate) :
    rho.propensity z = 0 <-> ¬ rho.enabled z := by
  constructor
  · exact not_enabled_of_propensity_eq_zero_of_positive_rate hk
  · exact propensity_eq_zero_of_not_enabled

theorem propensity_ne_zero_iff_enabled_of_positive_rate
    {rho : Reaction S} {z : State S}
    (hk : rho.hasPositiveRate) :
    rho.propensity z ≠ 0 <-> rho.enabled z := by
  constructor
  · intro hne
    by_contra hnot
    exact hne (propensity_eq_zero_of_not_enabled hnot)
  · intro hen
    exact propensity_ne_zero_of_enabled_of_positive_rate hen hk

end Reaction

namespace Network

variable {S : Type u} [Fintype S]

def totalPropensity (N : Network S) (z : State S) : Rate :=
  Finset.univ.sum (fun i : N.I => (N.rxn i).propensity z)

theorem totalPropensity_coe (N : Network S) (z : State S) :
    ((N.totalPropensity z : Rate) : Rat) =
      Finset.univ.sum
        (fun i : N.I => (((N.rxn i).propensity z : Rate) : Rat)) := by
  simp [totalPropensity, NNRat.cast_sum]

theorem totalPropensity_eq_zero_of_terminal
    {N : Network S} {z : State S}
    (hterm : N.Terminal z) :
    N.totalPropensity z = 0 := by
  unfold totalPropensity
  refine Finset.sum_eq_zero ?_
  intro i _hi
  exact Reaction.propensity_eq_zero_of_not_enabled (by
    intro hen
    exact hterm i hen)

theorem terminal_of_totalPropensity_eq_zero_of_positive_rates
    {N : Network S} {z : State S}
    (hpos : N.hasPositiveRates)
    (hzero : N.totalPropensity z = 0) :
    N.Terminal z := by
  intro i hen
  have hsumRat :
      Finset.univ.sum
        (fun j : N.I => (((N.rxn j).propensity z : Rate) : Rat)) = 0 := by
    have hcoe : ((N.totalPropensity z : Rate) : Rat) = 0 := by
      simpa using congrArg (fun q : Rate => ((q : Rate) : Rat)) hzero
    simpa [totalPropensity_coe] using hcoe
  have hEach :
      forall j : N.I,
        j ∈ Finset.univ ->
          (((N.rxn j).propensity z : Rate) : Rat) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (s := Finset.univ)
      (f := fun j : N.I => (((N.rxn j).propensity z : Rate) : Rat))
      (by
        intro j _hj
        exact NNRat.coe_nonneg ((N.rxn j).propensity z))).1 hsumRat
  have hiRat : (((N.rxn i).propensity z : Rate) : Rat) = 0 :=
    hEach i (Finset.mem_univ i)
  have hiZero : (N.rxn i).propensity z = 0 :=
    (NNRat.coe_eq_zero).1 hiRat
  exact Reaction.propensity_ne_zero_of_enabled_of_positive_rate
    hen (hpos i) hiZero

theorem totalPropensity_eq_zero_iff_terminal_of_positive_rates
    {N : Network S} {z : State S}
    (hpos : N.hasPositiveRates) :
    N.totalPropensity z = 0 <-> N.Terminal z := by
  constructor
  · exact terminal_of_totalPropensity_eq_zero_of_positive_rates hpos
  · exact totalPropensity_eq_zero_of_terminal

end Network

end Ripple.sCRNUniversality
