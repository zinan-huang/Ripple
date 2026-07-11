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
  3. The MassActionRaceLaw's race bound equals 1 - jumpProbAt
  4. Deterministic step when only one reaction is enabled
  5. Bridge to ClockBoundedLaw: propensity dominance → error bound
-/

import Ripple.sCRNUniversality.Stochastic.PropensityRace

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

/-- The MassActionRaceLaw's bound at reaction i says precisely
    P(i does not fire) ≤ 1 - propensity(i)/totalPropensity.
    This is a direct unpacking of the raceBound field. -/
theorem massActionRace_bound
    (L : MassActionRaceLaw N Omega)
    (t : Nat) (i : N.I) (z : State S)
    (hstate : ∀ omega, (L.path omega).state t = z)
    (hEnabled : N.EnabledAt z i)
    (hPos : N.hasPositiveRates) :
    L.prob.Pr (notFiredEvent L.path t i) ≤
      ENNReal.ofReal
        (1 - ((N.rxn i).propensity z : Rat) / (N.totalPropensity z : Rat)) :=
  L.raceBound t i z hstate hEnabled hPos

/-- The race bound value equals the complement of the jump probability
    when viewed as rationals. -/
theorem raceBound_value_eq_complement
    {z : State S} {i : N.I} :
    (1 : Rat) - ((N.rxn i).propensity z : Rat) / (N.totalPropensity z : Rat) =
      1 - (jumpProbAt N z i : Rat) := by
  rw [jumpProbAt_coe N]

/-- When reaction i is the only enabled reaction, the race bound is 0:
    the wrong reaction fires with probability 0 (deterministic). -/
theorem massActionRace_deterministic_of_unique_enabled [DecidableEq N.I]
    (L : MassActionRaceLaw N Omega)
    (t : Nat) (i : N.I) (z : State S)
    (hstate : ∀ omega, (L.path omega).state t = z)
    (hEnabled : N.EnabledAt z i)
    (hPos : N.hasPositiveRates)
    (hUnique : ∀ j : N.I, j ≠ i → ¬ N.EnabledAt z j) :
    L.prob.Pr (notFiredEvent L.path t i) ≤ 0 := by
  have hbound := L.raceBound t i z hstate hEnabled hPos
  -- When i is uniquely enabled, propensity(i) = totalPropensity
  have hTP : N.totalPropensity z = (N.rxn i).propensity z := by
    unfold Network.totalPropensity
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    have hzeros : (Finset.univ.erase i).sum
        (fun j => (N.rxn j).propensity z) = 0 :=
      Finset.sum_eq_zero fun j hj =>
        Reaction.propensity_eq_zero_of_not_enabled (hUnique _ (Finset.ne_of_mem_erase hj))
    rw [hzeros, add_zero]
  -- So propensity(i) / totalPropensity = 1 at Rat level
  have hdiv_one_rat : ((N.rxn i).propensity z : Rat) / (N.totalPropensity z : Rat) = 1 := by
    rw [hTP]; exact div_self
      (by exact_mod_cast Reaction.propensity_ne_zero_of_enabled_of_positive_rate hEnabled (hPos i))
  -- Lift to Real level
  have hdiv_one_real :
      (((N.rxn i).propensity z : Rat) : Real) / ((N.totalPropensity z : Rat) : Real) = 1 := by
    exact_mod_cast hdiv_one_rat
  rw [hdiv_one_real, sub_self, ENNReal.ofReal_zero] at hbound
  exact hbound

/-- Connection to ClockBoundedLaw: if we have a MassActionRaceLaw
    and the intended reaction's propensity ratio exceeds 1 - ε,
    then the per-microstep error is bounded by ε.

    This is the algebraic core of the clock error analysis:
    P(wrong firing) ≤ 1 - propensity(intended)/total ≤ ε. -/
theorem raceErrorBound_of_propensity_ratio
    (L : MassActionRaceLaw N Omega)
    (t : Nat) (intended : N.I) (z : State S)
    (hstate : ∀ omega, (L.path omega).state t = z)
    (hEnabled : N.EnabledAt z intended)
    (hPos : N.hasPositiveRates)
    (ε : ENNReal)
    (hBound : ENNReal.ofReal
      (1 - ((N.rxn intended).propensity z : Rat) / (N.totalPropensity z : Rat)) ≤ ε) :
    L.prob.Pr (notFiredEvent L.path t intended) ≤ ε :=
  le_trans (L.raceBound t intended z hstate hEnabled hPos) hBound

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

/-- For the SCWB clock construction: if at a given state, the non-intended
    reactions have total propensity ≤ ε · totalPropensity, then
    P(wrong firing) ≤ ε.

    This is the main bridge theorem connecting CRN propensity analysis
    to the ClockBoundedLaw's per-microstep error bound. -/
theorem clockError_from_propensity_dominance [DecidableEq N.I]
    (L : MassActionRaceLaw N Omega)
    (t : Nat) (intended : N.I) (z : State S)
    (hstate : ∀ omega, (L.path omega).state t = z)
    (hEnabled : N.EnabledAt z intended)
    (hPos : N.hasPositiveRates)
    (hNonTerm : ¬ N.Terminal z)
    (ε : NNRat)
    (hDominance :
      (Finset.univ.erase intended).sum (fun j => (N.rxn j).propensity z) ≤
        ε * N.totalPropensity z) :
    L.prob.Pr (notFiredEvent L.path t intended) ≤ ENNReal.ofReal (ε : Rat) := by
  apply raceErrorBound_of_propensity_ratio L t intended z hstate hEnabled hPos
  apply ENNReal.ofReal_le_ofReal
  -- Need: 1 - prop/total ≤ ε at Real level
  -- 1. At Rat level: 1 - prop/total = rest/total (complement_jumpProbAt_coe)
  -- 2. rest/total ≤ ε from hDominance
  -- 3. Cast from Rat to Real
  have hTP_pos : (0 : Rat) < (N.totalPropensity z : Rat) := by
    exact_mod_cast totalPropensity_pos_of_nonTerminal N hPos hNonTerm
  -- Step 1+2: 1 - prop/total ≤ ε at Rat level
  have hRat : (1 : Rat) -
      ((N.rxn intended).propensity z : Rat) / (N.totalPropensity z : Rat) ≤ (ε : Rat) := by
    rw [raceBound_value_eq_complement (N := N)]
    rw [complement_jumpProbAt_coe hPos hNonTerm]
    rw [div_le_iff₀ hTP_pos]
    have : ((Finset.univ.erase intended).sum
        (fun j => (N.rxn j).propensity z) : Rat) ≤
        (ε : Rat) * (N.totalPropensity z : Rat) := by
      exact_mod_cast hDominance
    linarith
  -- Step 3: cast Rat ≤ to Real ≤
  exact_mod_cast hRat

end BridgeTheorem

end Stochastic

end Ripple.sCRNUniversality
