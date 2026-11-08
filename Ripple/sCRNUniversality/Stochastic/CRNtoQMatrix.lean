/-
  CRNtoQMatrix — Bridge between CRN propensity and CTMC jump probabilities.

  A CRN Network N with mass-action kinetics induces a natural transition
  structure on the CRN state space:
    - propensity(i, z) = k_i · ∏_s C(z_s, l_{i,s})
    - totalPropensity(z) = Σ_i propensity(i, z)
    - jumpProbAt(i, z) = propensity(i, z) / totalPropensity(z)

  This module proves:
  1. jumpProbAt sums to 1 at non-terminal states
  2. jumpProbAt is positive iff reaction is enabled
  3. The race-bound value 1 - propensity/total equals 1 - jumpProbAt,
     and its complement form (the non-intended propensity ratio)
-/

import Ripple.sCRNUniversality.Stochastic.Propensity
import Ripple.sCRNUniversality.Stochastic.JumpPathLaw

open scoped BigOperators

namespace Ripple.sCRNUniversality

namespace Stochastic

variable {S : Type u} [Fintype S]

/-! ## Jump probability definition and basic properties -/

section JumpProbAt

variable (N : Network.{u, v} S)

/-- The jump probability of reaction i at state z under mass-action kinetics:
    propensity(i, z) / totalPropensity(z).
    Returns 0 when totalPropensity = 0 (terminal state). -/
noncomputable def jumpProbAt (z : State S) (i : N.I) : NNRat :=
  (N.rxn i).propensity z / N.totalPropensity z

/-- Jump probability is zero when the reaction is not enabled. -/
theorem jumpProbAt_eq_zero_of_not_enabled
    {z : State S} {i : N.I}
    (hnot : ¬ (N.rxn i).enabled z) :
    jumpProbAt N z i = 0 := by
  unfold jumpProbAt
  rw [Reaction.propensity_eq_zero_of_not_enabled hnot, zero_div]

/-- Jump probability is zero at a terminal state. -/
theorem jumpProbAt_eq_zero_of_terminal
    {z : State S}
    (hterm : N.Terminal z) (i : N.I) :
    jumpProbAt N z i = 0 := by
  unfold jumpProbAt
  rw [Network.totalPropensity_eq_zero_of_terminal hterm, div_zero]

/-- totalPropensity is positive at non-terminal states with positive rates. -/
theorem totalPropensity_pos_of_nonTerminal
    (hPos : N.hasPositiveRates)
    {z : State S}
    (hNonTerm : ¬ N.Terminal z) :
    0 < N.totalPropensity z := by
  by_contra h
  push Not at h
  have heq : N.totalPropensity z = 0 := le_antisymm h zero_le'
  exact hNonTerm
    ((Network.totalPropensity_eq_zero_iff_terminal_of_positive_rates hPos).mp heq)

/-- totalPropensity is nonzero at non-terminal states with positive rates. -/
theorem totalPropensity_ne_zero_of_nonTerminal
    (hPos : N.hasPositiveRates)
    {z : State S}
    (hNonTerm : ¬ N.Terminal z) :
    N.totalPropensity z ≠ 0 :=
  ne_of_gt (totalPropensity_pos_of_nonTerminal N hPos hNonTerm)

/-- The jump probabilities sum to 1 when the state is non-terminal. -/
theorem jumpProbAt_sum_eq_one
    (hPos : N.hasPositiveRates)
    {z : State S}
    (hNonTerm : ¬ N.Terminal z) :
    Finset.univ.sum (fun i : N.I => jumpProbAt N z i) = 1 := by
  unfold jumpProbAt
  rw [← Finset.sum_div]
  exact div_self (totalPropensity_ne_zero_of_nonTerminal N hPos hNonTerm)

/-- The propensity of reaction i is at most the total propensity. -/
theorem propensity_le_totalPropensity
    {z : State S} (i : N.I) :
    (N.rxn i).propensity z ≤ N.totalPropensity z :=
  Finset.single_le_sum
    (f := fun j => (N.rxn j).propensity z)
    (fun _ _ => zero_le')
    (Finset.mem_univ i)

/-- Each jump probability is at most 1. -/
theorem jumpProbAt_le_one
    {z : State S} (i : N.I) :
    jumpProbAt N z i ≤ 1 := by
  unfold jumpProbAt
  rcases eq_or_ne (N.totalPropensity z) 0 with hTP | hTP
  · rw [hTP, div_zero]; exact zero_le'
  · exact (div_le_one₀ (pos_iff_ne_zero.mpr hTP)).mpr (propensity_le_totalPropensity N i)

/-- The jump probability cast to Rat equals propensity / totalPropensity. -/
theorem jumpProbAt_coe
    {z : State S} {i : N.I} :
    ((jumpProbAt N z i : NNRat) : Rat) =
      ((N.rxn i).propensity z : Rat) / (N.totalPropensity z : Rat) :=
  NNRat.coe_div _ _

end JumpProbAt

/-! ## Unique enabled reaction (deterministic step) -/

section UniqueEnabled

variable (N : Network.{u, v} S)

/-- When reaction i is the only enabled reaction at state z,
    its jump probability is 1 (deterministic step). -/
theorem jumpProbAt_eq_one_of_unique_enabled [DecidableEq N.I]
    (hPos : N.hasPositiveRates)
    {z : State S} {i : N.I}
    (hEnabled : N.EnabledAt z i)
    (hUnique : ∀ j : N.I, j ≠ i → ¬ N.EnabledAt z j) :
    jumpProbAt N z i = 1 := by
  unfold jumpProbAt
  have hTP : N.totalPropensity z = (N.rxn i).propensity z := by
    unfold Network.totalPropensity
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    have hzeros : (Finset.univ.erase i).sum
        (fun j => (N.rxn j).propensity z) = 0 :=
      Finset.sum_eq_zero fun j hj =>
        Reaction.propensity_eq_zero_of_not_enabled (hUnique _ (Finset.ne_of_mem_erase hj))
    rw [hzeros, add_zero]
  rw [hTP]
  exact div_self (Reaction.propensity_ne_zero_of_enabled_of_positive_rate hEnabled (hPos i))

/-- The non-intended propensity sum equals total minus intended. -/
theorem nonintended_propensity_sum [DecidableEq N.I]
    {z : State S} {intended : N.I} :
    N.totalPropensity z =
      (N.rxn intended).propensity z +
        (Finset.univ.erase intended).sum (fun j => (N.rxn j).propensity z) := by
  unfold Network.totalPropensity
  exact (Finset.add_sum_erase _ _ (Finset.mem_univ intended)).symm

end UniqueEnabled

/-! ## Bridge theorems connecting propensity to race bounds -/

section BridgeTheorem

universe w

variable {N : Network.{u, v} S} {Omega : Type w}

/-- The race bound value equals the complement of the jump probability
    when viewed as rationals. -/
theorem raceBound_value_eq_complement
    {z : State S} {i : N.I} :
    (1 : Rat) - ((N.rxn i).propensity z : Rat) / (N.totalPropensity z : Rat) =
      1 - (jumpProbAt N z i : Rat) := by
  rw [jumpProbAt_coe N]

/-- The complement of jumpProbAt equals the non-intended propensity ratio. -/
theorem complement_jumpProbAt_coe [DecidableEq N.I]
    (hPos : N.hasPositiveRates)
    {z : State S} {intended : N.I}
    (hNonTerm : ¬ N.Terminal z) :
    (1 : Rat) - (jumpProbAt N z intended : Rat) =
      ((Finset.univ.erase intended).sum
        (fun j => (N.rxn j).propensity z) : Rat) /
        (N.totalPropensity z : Rat) := by
  rw [jumpProbAt_coe N]
  have hTP_pos : (0 : Rat) < (N.totalPropensity z : Rat) := by
    exact_mod_cast totalPropensity_pos_of_nonTerminal N hPos hNonTerm
  have hne : (N.totalPropensity z : Rat) ≠ 0 := ne_of_gt hTP_pos
  have hsplit : (N.totalPropensity z : Rat) =
      ((N.rxn intended).propensity z : Rat) +
        ((Finset.univ.erase intended).sum
          (fun j => (N.rxn j).propensity z) : Rat) := by
    rw [nonintended_propensity_sum (N := N)]
    push_cast
    ring
  field_simp
  linarith

end BridgeTheorem

end Stochastic

end Ripple.sCRNUniversality
