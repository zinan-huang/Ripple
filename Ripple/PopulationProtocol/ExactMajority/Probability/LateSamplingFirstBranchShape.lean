-- Ripple/PopulationProtocol/ExactMajority/Probability/LateSamplingFirstBranchShape.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.LateSamplingShallowCorollary
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingMajorityPartners
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockRegime
import Ripple.PopulationProtocol.ExactMajority.Probability.NonMainBiasZero
import Ripple.PopulationProtocol.ExactMajority.Analysis.MassLedger

/-!
# The first-branch class shape at every actual Phase-3/4/5 snapshot

For the winning sign `σ`, write

* `P = 2^ell * signMass σ c`;
* `S = scaledShallowPositive σ (ell - 1) c`;
* `A = bandCount σ ell 0 c`;
* `B = bandCount σ (ell + 1) 0 c`.

The exact pointwise capacity decomposition is

  `4 P ≤ 8 S + M + 3 A + B`.

Indeed, a winning Main atom has:

* weight accounted by `2 S` below `ell`;
* weight `1` at `ell`;
* weight `1/2` at `ell + 1`;
* weight at most `1/4` above `ell + 1`.

The conserved winning mass and the readout scale give `P ≥ .4 M`.
The original shallow budget, transported by
`scaledShallowPositive_seed_mono`, gives `S ≤ .001 M`.
Consequently

  `1.6 M ≤ 1.008 M + 3 A + B`

and hence `3 A + B ≥ .592 M`.

The old-index cutoff is retained in `FirstBranchShapeData`, but is not
needed for this stronger mass-shape inequality.  It is reserved for the
retrospective exact-level-arrival argument.
-/

noncomputable section

namespace Ripple.PopulationProtocol.ExactMajority.LateSamplingFirstBranchShape

open TimeTheorem StageEventSpec
open LateStrengthening
open LateSamplingSeedReceipt
open LateF6OriginalLaw
open AveragingCreditTransitions
open AveragingTerminalReadout
open AveragingMajorityPartners
open AveragingLiveProduct
open AveragingCheckpointReadout

variable {L K n : ℕ}

/-! ## The corrected integer arithmetic -/

/-- Correct form of the mass-to-shape arithmetic.

The `1008 M` consists of the unit capacity of all `M` Main agents and
the transported `.008 M` contribution of the strict shallow part. -/
theorem first_branch_mass_to_shape_from_capacity
    (M A B : ℕ)
    (hmass :
      1600 * M ≤ 1008 * M + 3000 * A + 1000 * B) :
    592 * M ≤ 3000 * A + 1000 * B := by
  omega

/-! ## Scaled atom functions -/

private theorem scaledWeight_eq_scaledZpow (ell j : ℕ) :
    scaledWeight ell j =
      (2 : ℚ) ^ ell * (2 : ℚ) ^ (-(j : ℤ)) := by
  simp [scaledWeight, zpow_neg, zpow_natCast, div_eq_mul_inv]

private theorem scaledWeight_self_eq_one (ell : ℕ) :
    scaledWeight ell ell = (1 : ℚ) := by
  unfold scaledWeight
  field_simp

private theorem scaledWeight_next_eq_half (ell : ℕ) :
    scaledWeight ell (ell + 1) = (1 / 2 : ℚ) := by
  unfold scaledWeight
  rw [pow_succ]
  have hp : (2 : ℚ) ^ ell ≠ 0 := by
    positivity
  field_simp [hp]

private theorem scaledWeight_twice_previous
    (ell j : ℕ) (hell : 1 ≤ ell) :
    2 * scaledWeight (ell - 1) j = scaledWeight ell j := by
  have hs : ell - 1 + 1 = ell := by
    omega
  unfold scaledWeight
  conv_rhs =>
    rw [← hs, pow_succ]
  ring

/-- Winning-sign mass of one Main atom, scaled by `2^ell`. -/
noncomputable def winningScaledAtom
    (σ : Sign) (ell : ℕ) (a : AgentState L K) : ℚ := by
  classical
  exact
    if a.role = .main then
      match a.bias with
      | .zero => 0
      | .dyadic τ j =>
          if τ = σ then scaledWeight ell j.val else 0
    else 0

/-- Winning-sign mass through index `ell`, scaled by `2^ell`. -/
noncomputable def boundedWinningScaledAtom
    (σ : Sign) (ell : ℕ) (a : AgentState L K) : ℚ := by
  classical
  exact
    if a.role = .main then
      match a.bias with
      | .zero => 0
      | .dyadic τ j =>
          if τ = σ ∧ j.val ≤ ell then
            scaledWeight ell j.val
          else 0
    else 0

/-- Absolute Main mass strictly below `ell`, scaled by `2^ell`. -/
noncomputable def strictAbsoluteScaledAtom
    (ell : ℕ) (a : AgentState L K) : ℚ := by
  classical
  exact
    if a.role = .main then
      match a.bias with
      | .zero => 0
      | .dyadic _ j =>
          if j.val < ell then scaledWeight ell j.val else 0
    else 0

private theorem winningScaledAtom_nonneg
    (σ : Sign) (ell : ℕ) (a : AgentState L K) :
    0 ≤ winningScaledAtom σ ell a := by
  classical
  by_cases hm : a.role = .main
  · cases hb : a.bias with
    | zero =>
        simp [winningScaledAtom, hm, hb]
    | dyadic τ j =>
        by_cases hτ : τ = σ <;>
          simp [winningScaledAtom, hm, hb, hτ, scaledWeight_nonneg]
  · simp [winningScaledAtom, hm]

private theorem boundedWinningScaledAtom_nonneg
    (σ : Sign) (ell : ℕ) (a : AgentState L K) :
    0 ≤ boundedWinningScaledAtom σ ell a := by
  classical
  by_cases hm : a.role = .main
  · cases hb : a.bias with
    | zero =>
        simp [boundedWinningScaledAtom, hm, hb]
    | dyadic τ j =>
        by_cases hτ : τ = σ
        · by_cases hj : j.val ≤ ell <;>
            simp [boundedWinningScaledAtom, hm, hb, hτ, hj,
              scaledWeight_nonneg]
        · simp [boundedWinningScaledAtom, hm, hb, hτ]
  · simp [boundedWinningScaledAtom, hm]

private theorem strictAbsoluteScaledAtom_nonneg
    (ell : ℕ) (a : AgentState L K) :
    0 ≤ strictAbsoluteScaledAtom ell a := by
  classical
  by_cases hm : a.role = .main
  · cases hb : a.bias with
    | zero =>
        simp [strictAbsoluteScaledAtom, hm, hb]
    | dyadic τ j =>
        by_cases hj : j.val < ell <;>
          simp [strictAbsoluteScaledAtom, hm, hb, hj,
            scaledWeight_nonneg]
  · simp [strictAbsoluteScaledAtom, hm]

private theorem winningScaledAtom_eq_term
    (σ : Sign) (ell : ℕ) (a : AgentState L K) :
    winningScaledAtom σ ell a =
      (2 : ℚ) ^ ell *
        (if a.role = .main then
          match a.bias with
          | .zero => 0
          | .dyadic τ j =>
              if τ = σ then
                (2 : ℚ) ^ (-(j.val : ℤ))
              else 0
        else 0) := by
  classical
  by_cases hm : a.role = .main
  · cases hb : a.bias with
    | zero =>
        simp [winningScaledAtom, hm, hb]
    | dyadic τ j =>
        by_cases hτ : τ = σ
        · simp [winningScaledAtom, hm, hb, hτ,
            scaledWeight_eq_scaledZpow]
        · simp [winningScaledAtom, hm, hb, hτ]
  · simp [winningScaledAtom, hm]

private theorem boundedWinningScaledAtom_eq_term
    (σ : Sign) (ell : ℕ) (a : AgentState L K) :
    boundedWinningScaledAtom σ ell a =
      (2 : ℚ) ^ ell *
        (if a.role = .main then
          match a.bias with
          | .zero => 0
          | .dyadic τ j =>
              if τ = σ ∧ j.val ≤ ell then
                (2 : ℚ) ^ (-(j.val : ℤ))
              else 0
        else 0) := by
  classical
  by_cases hm : a.role = .main
  · cases hb : a.bias with
    | zero =>
        simp [boundedWinningScaledAtom, hm, hb]
    | dyadic τ j =>
        by_cases hτ : τ = σ
        · by_cases hj : j.val ≤ ell <;>
            simp [boundedWinningScaledAtom, hm, hb, hτ, hj,
              scaledWeight_eq_scaledZpow]
        · simp [boundedWinningScaledAtom, hm, hb, hτ]
  · simp [boundedWinningScaledAtom, hm]

private theorem strictAbsoluteScaledAtom_eq_term
    (ell : ℕ) (a : AgentState L K) :
    strictAbsoluteScaledAtom ell a =
      (2 : ℚ) ^ ell *
        (if a.role = .main then
          match a.bias with
          | .zero => 0
          | .dyadic _ j =>
              if j.val < ell then
                (2 : ℚ) ^ (-(j.val : ℤ))
              else 0
        else 0) := by
  classical
  by_cases hm : a.role = .main
  · cases hb : a.bias with
    | zero =>
        simp [strictAbsoluteScaledAtom, hm, hb]
    | dyadic τ j =>
        by_cases hj : j.val < ell <;>
          simp [strictAbsoluteScaledAtom, hm, hb, hj,
            scaledWeight_eq_scaledZpow]
  · simp [strictAbsoluteScaledAtom, hm]

private theorem winningScaledAtom_sum
    (σ : Sign) (ell : ℕ) (c : InputCfg n) :
    Config.sumOf (winningScaledAtom σ ell) c =
      (2 : ℚ) ^ ell * signMass σ c := by
  classical
  induction c using Multiset.induction_on with
  | empty =>
      simp [Config.sumOf, signMass]
  | cons a c ih =>
      simp only [Config.sumOf, signMass, Multiset.map_cons,
        Multiset.sum_cons] at ih ⊢
      rw [ih, mul_add]
      congr 1
      by_cases hm : a.role = .main
      · cases hb : a.bias with
        | zero => simp [winningScaledAtom, hm, hb]
        | dyadic τ j =>
            by_cases hτ : τ = σ <;>
              simp [winningScaledAtom, hm, hb, hτ, scaledWeight_eq_scaledZpow]
      · simp [winningScaledAtom, hm]

private theorem boundedWinningScaledAtom_sum
    (σ : Sign) (ell : ℕ) (c : InputCfg n) :
    Config.sumOf (boundedWinningScaledAtom σ ell) c =
      scaledShallowPositive σ ell c := by
  classical
  induction c using Multiset.induction_on with
  | empty =>
      simp [Config.sumOf, scaledShallowPositive]
  | cons a c ih =>
      simp only [Config.sumOf, scaledShallowPositive,
        Multiset.map_cons, Multiset.sum_cons] at ih ⊢
      rw [ih, mul_add]
      congr 1
      by_cases hm : a.role = .main
      · cases hb : a.bias with
        | zero => simp [boundedWinningScaledAtom, hm, hb]
        | dyadic τ j =>
            by_cases hτ : τ = σ
            · by_cases hj : j.val ≤ ell <;>
                simp [boundedWinningScaledAtom, hm, hb, hτ, hj,
                  scaledWeight_eq_scaledZpow]
            · simp [boundedWinningScaledAtom, hm, hb, hτ]
      · simp [boundedWinningScaledAtom, hm]

private theorem strictAbsoluteScaledAtom_sum
    (ell : ℕ) (c : InputCfg n) :
    Config.sumOf (strictAbsoluteScaledAtom ell) c =
      (2 : ℚ) ^ ell * shallowMass ell c := by
  classical
  induction c using Multiset.induction_on with
  | empty =>
      simp [Config.sumOf, shallowMass]
  | cons a c ih =>
      simp only [Config.sumOf, shallowMass, Multiset.map_cons,
        Multiset.sum_cons] at ih ⊢
      rw [ih, mul_add]
      congr 1
      by_cases hm : a.role = .main
      · cases hb : a.bias with
        | zero => simp [strictAbsoluteScaledAtom, hm, hb]
        | dyadic τ j =>
            by_cases hj : j.val < ell <;>
              simp [strictAbsoluteScaledAtom, hm, hb, hj,
                scaledWeight_eq_scaledZpow]
      · simp [strictAbsoluteScaledAtom, hm]

private theorem sumOf_const_mul
    {α : Type*} (r : ℚ) (f : α → ℚ) (c : Multiset α) :
    Config.sumOf (fun a => r * f a) c =
      r * Config.sumOf f c := by
  induction c using Multiset.induction_on with
  | empty =>
      simp [Config.sumOf]
  | cons a c ih =>
      simp only [Config.sumOf, Multiset.map_cons,
        Multiset.sum_cons] at ih ⊢
      rw [ih]
      ring

private theorem sumOf_le_sumOf
    {α : Type*} (f g : α → ℚ) (c : Multiset α)
    (h : ∀ a ∈ c, f a ≤ g a) :
    Config.sumOf f c ≤ Config.sumOf g c := by
  induction c using Multiset.induction_on with
  | empty =>
      simp [Config.sumOf]
  | cons a c ih =>
      have ha := h a (Multiset.mem_cons_self a c)
      have hc := ih
        (fun b hb => h b (Multiset.mem_cons_of_mem hb))
      simp only [Config.sumOf, Multiset.map_cons,
        Multiset.sum_cons] at ha hc ⊢
      linarith

/-! ## Elementary `hlevelWeight` -/

private theorem bandIndicator_le_boundedWinningScaledAtom
    (σ : Sign) (ell : ℕ) (a : AgentState L K) :
    bandIndicator σ ell 0 a ≤
      boundedWinningScaledAtom σ ell a := by
  classical
  by_cases hband : InBand σ ell 0 a
  · obtain ⟨hm, j, hb, hlo, hhi⟩ := id hband
    have hj : j.val = ell := by
      omega
    have hw : scaledWeight ell j.val = (1 : ℚ) := by
      rw [hj]
      exact scaledWeight_self_eq_one ell
    rw [bandIndicator, if_pos hband]
    simp [boundedWinningScaledAtom, hm, hb, hj, hw, scaledWeight_self_eq_one]
  · rw [bandIndicator, if_neg hband]
    exact boundedWinningScaledAtom_nonneg σ ell a

/-- Every exact-`ell` winning Main contributes one full unit to the
scaled shallow-positive potential.

This is a definition-level identity, with no probabilistic input. -/
theorem bandCount_exact_le_scaledShallowPositive
    (σ : Sign) (ell : ℕ) (c : InputCfg n) :
    (bandCount σ ell 0 c : ℚ) ≤
      scaledShallowPositive σ ell c := by
  calc
    (bandCount σ ell 0 c : ℚ) =
        Config.sumOf (bandIndicator σ ell 0) c := by
      rw [sum_bandIndicator]
    _ ≤ Config.sumOf (boundedWinningScaledAtom σ ell) c :=
      sumOf_le_sumOf
        (bandIndicator σ ell 0)
        (boundedWinningScaledAtom σ ell) c
        (fun a _ =>
          bandIndicator_le_boundedWinningScaledAtom σ ell a)
    _ = scaledShallowPositive σ ell c :=
      boundedWinningScaledAtom_sum σ ell c

/-! ## Elementary `hpartition` -/

private theorem dyadicIndex_eq_of_eq
    {τ υ : Sign} {j k : Fin (L + 1)}
    (h : Bias.dyadic τ j = Bias.dyadic υ k) :
    j.val = k.val := by
  have hv := congrArg
    (fun b : Bias L =>
      match b with
      | .zero => 0
      | .dyadic _ r => r.val) h
  simpa using hv

private theorem dyadicSign_eq_of_eq
    {τ υ : Sign} {j k : Fin (L + 1)}
    (h : Bias.dyadic τ j = Bias.dyadic υ k) :
    τ = υ := by
  have hv := congrArg
    (fun b : Bias L =>
      match b with
      | .zero => (none : Option Sign)
      | .dyadic ρ _ => some ρ) h
  simpa using hv

private theorem inBand_zero_iff_index
    (a : AgentState L K) (σ : Sign) (ell : ℕ)
    (j : Fin (L + 1))
    (hm : a.role = .main)
    (hb : a.bias = Bias.dyadic σ j) :
    InBand σ ell 0 a ↔ j.val = ell := by
  constructor
  · rintro ⟨_, k, hk, hlo, hhi⟩
    have hindex := dyadicIndex_eq_of_eq (hb.symm.trans hk)
    omega
  · intro hj
    exact ⟨hm, j, hb, by omega, by omega⟩

private theorem not_inBand_of_wrong_sign
    (a : AgentState L K) (σ τ : Sign)
    (ell width : ℕ) (j : Fin (L + 1))
    (hb : a.bias = Bias.dyadic τ j)
    (hne : τ ≠ σ) :
    ¬ InBand σ ell width a := by
  rintro ⟨_, k, hk, _, _⟩
  have hsign : τ = σ :=
    dyadicSign_eq_of_eq (hb.symm.trans hk)
  exact hne hsign

private theorem inBand_width_one_iff
    (a : AgentState L K) (σ : Sign) (ell : ℕ) :
    InBand σ ell 1 a ↔
      InBand σ ell 0 a ∨
        InBand σ (ell + 1) 0 a := by
  constructor
  · rintro ⟨hm, j, hb, hlo, hhi⟩
    have hj : j.val = ell ∨ j.val = ell + 1 := by
      omega
    rcases hj with hj | hj
    · exact Or.inl ⟨hm, j, hb, by omega, by omega⟩
    · exact Or.inr ⟨hm, j, hb, by omega, by omega⟩
  · rintro (h | h)
    · obtain ⟨hm, j, hb, hlo, hhi⟩ := h
      exact ⟨hm, j, hb, hlo, by omega⟩
    · obtain ⟨hm, j, hb, hlo, hhi⟩ := h
      exact ⟨hm, j, hb, by omega, by omega⟩

private theorem exactBands_disjoint
    (a : AgentState L K) (σ : Sign) (ell : ℕ) :
    ¬ (InBand σ ell 0 a ∧
      InBand σ (ell + 1) 0 a) := by
  rintro ⟨hleft, hright⟩
  obtain ⟨_, j, hj, hlo, hhi⟩ := hleft
  obtain ⟨_, k, hk, hklo, hkhi⟩ := hright
  have hjv : j.val = ell := by
    omega
  have hkv : k.val = ell + 1 := by
    omega
  have hindex := dyadicIndex_eq_of_eq (hj.symm.trans hk)
  omega

private theorem bandIndicator_width_one
    (a : AgentState L K) (σ : Sign) (ell : ℕ) :
    bandIndicator σ ell 1 a =
      bandIndicator σ ell 0 a +
        bandIndicator σ (ell + 1) 0 a := by
  classical
  by_cases hleft : InBand σ ell 0 a
  · have hwide :=
      (inBand_width_one_iff a σ ell).2 (Or.inl hleft)
    have hright : ¬ InBand σ (ell + 1) 0 a := by
      intro h
      exact exactBands_disjoint a σ ell ⟨hleft, h⟩
    simp [bandIndicator, hwide, hleft, hright]
  · by_cases hright : InBand σ (ell + 1) 0 a
    · have hwide :=
        (inBand_width_one_iff a σ ell).2 (Or.inr hright)
      simp [bandIndicator, hwide, hleft, hright]
    · have hwide : ¬ InBand σ ell 1 a := by
        intro h
        rcases (inBand_width_one_iff a σ ell).1 h with h | h
        · exact hleft h
        · exact hright h
      simp [bandIndicator, hwide, hleft, hright]

/-- The width-one band is exactly the disjoint union of exact levels
`ell` and `ell + 1`.

This is a deterministic identity of `bandCount`. -/
theorem bandCount_width_one_partition
    (σ : Sign) (ell : ℕ) (c : InputCfg n) :
    bandCount σ ell 1 c =
      bandCount σ ell 0 c +
        bandCount σ (ell + 1) 0 c := by
  have hsum :
      Config.sumOf (bandIndicator σ ell 1) c =
        Config.sumOf (bandIndicator σ ell 0) c +
          Config.sumOf (bandIndicator σ (ell + 1) 0) c := by
    induction c using Multiset.induction_on with
    | empty =>
        simp [Config.sumOf]
    | cons a c ih =>
        simp only [Config.sumOf, Multiset.map_cons,
          Multiset.sum_cons] at ih ⊢
        rw [bandIndicator_width_one a σ ell, ih]
        ring
  have hq :
      (bandCount σ ell 1 c : ℚ) =
        (bandCount σ ell 0 c : ℚ) +
          (bandCount σ (ell + 1) 0 c : ℚ) := by
    simpa only [sum_bandIndicator] using hsum
  exact_mod_cast hq

/-! ## The original `.002M` shallow budget at scale `ell - 1` -/

private theorem twice_bounded_previous_le_strict_absolute
    (σ : Sign) (ell : ℕ) (hell : 1 ≤ ell)
    (a : AgentState L K) :
    2 * boundedWinningScaledAtom σ (ell - 1) a ≤
      strictAbsoluteScaledAtom ell a := by
  classical
  by_cases hm : a.role = .main
  · cases hb : a.bias with
    | zero =>
        simp [boundedWinningScaledAtom,
          strictAbsoluteScaledAtom, hm, hb]
    | dyadic τ j =>
        by_cases hbound : τ = σ ∧ j.val ≤ ell - 1
        · obtain ⟨hτ, hj⟩ := hbound
          have hlt : j.val < ell := by
            omega
          have hw :=
            scaledWeight_twice_previous ell j.val hell
          simp [boundedWinningScaledAtom,
            strictAbsoluteScaledAtom, hm, hb, hτ, hj, hlt]
          exact le_of_eq hw
        · have hnonneg :=
            strictAbsoluteScaledAtom_nonneg ell a
          simp [boundedWinningScaledAtom, hm, hb, hbound]
          exact hnonneg
  · simp [boundedWinningScaledAtom,
      strictAbsoluteScaledAtom, hm]

/-- Same-sign mass through `ell - 1`, scaled at `ell - 1`, is at most
half the all-sign strict-shallow mass scaled at `ell`. -/
theorem twice_scaledShallowPrevious_le_shallowMass
    (σ : Sign) (ell : ℕ) (c : InputCfg n)
    (hell : 1 ≤ ell) :
    2 * scaledShallowPositive σ (ell - 1) c ≤
      (2 : ℚ) ^ ell * shallowMass ell c := by
  calc
    2 * scaledShallowPositive σ (ell - 1) c =
        2 * Config.sumOf
          (boundedWinningScaledAtom σ (ell - 1)) c := by
      rw [boundedWinningScaledAtom_sum]
    _ = Config.sumOf
        (fun a =>
          2 * boundedWinningScaledAtom σ (ell - 1) a) c := by
      exact
        (sumOf_const_mul 2
          (boundedWinningScaledAtom σ (ell - 1)) c).symm
    _ ≤ Config.sumOf (strictAbsoluteScaledAtom ell) c :=
      sumOf_le_sumOf
        (fun a =>
          2 * boundedWinningScaledAtom σ (ell - 1) a)
        (strictAbsoluteScaledAtom ell) c
        (fun a _ =>
          twice_bounded_previous_le_strict_absolute
            σ ell hell a)
    _ = (2 : ℚ) ^ ell * shallowMass ell c :=
      strictAbsoluteScaledAtom_sum ell c

/-! ## Exact weighted capacity: `4P ≤ 8S + M + 3A + B` -/

private theorem winningScaledAtom_capacity
    (σ : Sign) (ell : ℕ) (hell : 1 ≤ ell)
    (a : AgentState L K) :
    4 * winningScaledAtom σ ell a ≤
      8 * boundedWinningScaledAtom σ (ell - 1) a +
        mainIndicator a +
        3 * bandIndicator σ ell 0 a +
        bandIndicator σ (ell + 1) 0 a := by
  classical
  by_cases hm : a.role = .main
  · cases hb : a.bias with
    | zero =>
        simp [winningScaledAtom,
          boundedWinningScaledAtom, mainIndicator,
          bandIndicator, InBand, hm, hb]
    | dyadic τ j =>
        by_cases hsign : τ = σ
        · subst τ
          have hbandEll :
              InBand σ ell 0 a ↔ j.val = ell :=
            inBand_zero_iff_index a σ ell j hm hb
          have hbandNext :
              InBand σ (ell + 1) 0 a ↔
                j.val = ell + 1 :=
            inBand_zero_iff_index
              a σ (ell + 1) j hm hb
          have hwin :
              winningScaledAtom σ ell a =
                scaledWeight ell j.val := by
            simp [winningScaledAtom, hm, hb]
          have hmain : mainIndicator a = 1 := by
            simp [mainIndicator, hm]
          by_cases hlow : j.val < ell
          · have hpreviousIndex : j.val ≤ ell - 1 := by
              omega
            have hprevious :
                boundedWinningScaledAtom σ (ell - 1) a =
                  scaledWeight (ell - 1) j.val := by
              simp [boundedWinningScaledAtom, hm, hb,
                hpreviousIndex]
            have hlevel : bandIndicator σ ell 0 a = 0 := by
              rw [bandIndicator, if_neg]
              rw [hbandEll]
              omega
            have hnext :
                bandIndicator σ (ell + 1) 0 a = 0 := by
              rw [bandIndicator, if_neg]
              rw [hbandNext]
              omega
            have hw :=
              scaledWeight_twice_previous ell j.val hell
            rw [hwin, hprevious, hmain, hlevel, hnext]
            nlinarith
          · by_cases heq : j.val = ell
            · have hprevious :
                  boundedWinningScaledAtom σ (ell - 1) a = 0 := by
                simp [boundedWinningScaledAtom, hm, hb]
                omega
              have hlevel :
                  bandIndicator σ ell 0 a = 1 := by
                rw [bandIndicator,
                  if_pos ((hbandEll).2 heq)]
              have hnext :
                  bandIndicator σ (ell + 1) 0 a = 0 := by
                rw [bandIndicator, if_neg]
                rw [hbandNext]
                omega
              have hw : scaledWeight ell j.val = 1 := by
                rw [heq]
                exact scaledWeight_self_eq_one ell
              rw [hwin, hprevious, hmain, hlevel, hnext, hw]
              norm_num
            · by_cases hnextIndex : j.val = ell + 1
              · have hprevious :
                    boundedWinningScaledAtom σ (ell - 1) a = 0 := by
                  simp [boundedWinningScaledAtom, hm, hb]
                  omega
                have hlevel :
                    bandIndicator σ ell 0 a = 0 := by
                  rw [bandIndicator, if_neg]
                  rw [hbandEll]
                  exact heq
                have hnext :
                    bandIndicator σ (ell + 1) 0 a = 1 := by
                  rw [bandIndicator,
                    if_pos ((hbandNext).2 hnextIndex)]
                have hw :
                    scaledWeight ell j.val = (1 / 2 : ℚ) := by
                  rw [hnextIndex]
                  exact scaledWeight_next_eq_half ell
                rw [hwin, hprevious, hmain, hlevel, hnext, hw]
                norm_num
              · have hfar : ell + 2 ≤ j.val := by
                  omega
                have hprevious :
                    boundedWinningScaledAtom σ (ell - 1) a = 0 := by
                  simp [boundedWinningScaledAtom, hm, hb]
                  omega
                have hlevel :
                    bandIndicator σ ell 0 a = 0 := by
                  rw [bandIndicator, if_neg]
                  rw [hbandEll]
                  exact heq
                have hnext :
                    bandIndicator σ (ell + 1) 0 a = 0 := by
                  rw [bandIndicator, if_neg]
                  rw [hbandNext]
                  exact hnextIndex
                have hw :
                    scaledWeight ell j.val ≤ (1 / 4 : ℚ) :=
                  scaledWeight_le_quarter_of_two_le hfar
                rw [hwin, hprevious, hmain, hlevel, hnext]
                nlinarith
        · have hwin :
              winningScaledAtom σ ell a = 0 := by
            simp [winningScaledAtom, hm, hb, hsign]
          have hprevious :
              boundedWinningScaledAtom σ (ell - 1) a = 0 := by
            simp [boundedWinningScaledAtom, hm, hb, hsign]
          have hmain : mainIndicator a = 1 := by
            simp [mainIndicator, hm]
          have hlevel :
              bandIndicator σ ell 0 a = 0 := by
            rw [bandIndicator, if_neg]
            exact not_inBand_of_wrong_sign
              a σ τ ell 0 j hb hsign
          have hnext :
              bandIndicator σ (ell + 1) 0 a = 0 := by
            rw [bandIndicator, if_neg]
            exact not_inBand_of_wrong_sign
              a σ τ (ell + 1) 0 j hb hsign
          rw [hwin, hprevious, hmain, hlevel, hnext]
          norm_num
  · have hlevel : ¬ InBand σ ell 0 a := by
      intro h
      exact hm h.1
    have hnext : ¬ InBand σ (ell + 1) 0 a := by
      intro h
      exact hm h.1
    simp [winningScaledAtom, boundedWinningScaledAtom,
      mainIndicator, bandIndicator, hm, hlevel, hnext]

/-- Exact configuration-level capacity decomposition.

Unlike a coarser `A + B` estimate, the exact-level coefficients are
`3` for level `ell` and `1` for level `ell + 1`. -/
theorem winningMass_capacity
    (σ : Sign) (ell : ℕ) (c : InputCfg n)
    (hell : 1 ≤ ell) :
    4 * ((2 : ℚ) ^ ell * signMass σ c) ≤
      8 * scaledShallowPositive σ (ell - 1) c +
        (timeMainCount c : ℚ) +
        3 * (bandCount σ ell 0 c : ℚ) +
        (bandCount σ (ell + 1) 0 c : ℚ) := by
  have hraw :
      4 * Config.sumOf (winningScaledAtom σ ell) c ≤
        8 * Config.sumOf
            (boundedWinningScaledAtom σ (ell - 1)) c +
          Config.sumOf mainIndicator c +
          3 * Config.sumOf (bandIndicator σ ell 0) c +
          Config.sumOf (bandIndicator σ (ell + 1) 0) c := by
    induction c using Multiset.induction_on with
    | empty =>
        simp [Config.sumOf]
    | cons a c ih =>
        have ha :=
          winningScaledAtom_capacity σ ell hell a
        simp only [Config.sumOf, Multiset.map_cons,
          Multiset.sum_cons] at ih ha ⊢
        nlinarith
  simpa only [winningScaledAtom_sum,
    boundedWinningScaledAtom_sum, sum_mainIndicator,
    sum_bandIndicator] using hraw

/-! ## Actual-prefix conservation facts -/

/-- Main-role cardinality is constant throughout the actual prefix. -/
theorem mainCount_at_snapshot
    {init : InputCfg n} {ω : InputLog n}
    {a s t v M ell : ℕ} {σ : Sign}
    (hpath : Prefix init ω a s t)
    (hseed :
      LateSamplingSeedReceipt init M ell σ
        (trace init ω s))
    (hsv : s ≤ v) (hvt : v ≤ t) :
    timeMainCount (trace init ω v) = M := by
  have hrole :
      timeMainCount (trace init ω v) =
        timeMainCount (trace init ω s) := by
    unfold timeMainCount
    rw [← PairLog.labelsAt_config init ω v,
      ← PairLog.labelsAt_config init ω s]
    exact
      PhaseThreeClockRegime.countP_role_labelCfg_eq init
        (fun i =>
          hpath.role_between s v
            hpath.start_order hsv hvt i)
        .main
  exact hrole.trans hseed.main_count

/-- Exact conservation of the signed pre-Phase-4 mass at every actual
Phase-3/4/5 snapshot.

The explicit `validInitial` input is required by the public mass-ledger
theorem. -/
theorem prePhaseFourMass_at_snapshot
    {init : InputCfg n} (hvalid : validInitial init)
    {ω : InputLog n} {a s t v : ℕ}
    (hpath : Prefix init ω a s t)
    (hsv : s ≤ v) (hvt : v ≤ t) :
    prePhase4MassSum (trace init ω v) =
      (initialGap init : ℚ) := by
  have hwindow :=
    hpath.window v (hpath.start_order.trans hsv) hvt
  have hphaseEight :
      ∀ x ∈ trace init ω v, x.phase.val < 8 := by
    intro x hx
    have hw := (hwindow x hx).2
    omega
  have hphaseTen :
      ∀ x ∈ trace init ω v, x.phase.val < 10 := by
    intro x hx
    have hw := (hwindow x hx).2
    omega
  have hreach :=
    PhaseZeroEntry.phase_zero_trace_reachable init ω v
  have hledger :=
    reachable_ledger_bounds
      init (trace init ω v) hvalid hreach hphaseTen
  rw [loSum_eq_prePhase4MassSum_of_phase_lt_eight
      (trace init ω v) hphaseEight,
    hiSum_eq_prePhase4MassSum_of_phase_lt_eight
      (trace init ω v) hphaseEight] at hledger
  exact le_antisymm hledger.1 hledger.2

/-- Reachability and the actual Phase-3/4/5 window remove all
non-Main dyadic carriers. -/
theorem nonmain_bias_zero_at_snapshot
    {init : InputCfg n} (hvalid : validInitial init)
    {ω : InputLog n} {a s t v : ℕ}
    (hpath : Prefix init ω a s t)
    (hsv : s ≤ v) (hvt : v ≤ t) :
    ∀ x ∈ trace init ω v,
      x.role ≠ .main → x.bias = .zero := by
  have hwindow :=
    hpath.window v (hpath.start_order.trans hsv) hvt
  have hreach :=
    PhaseZeroEntry.phase_zero_trace_reachable init ω v
  have hzero :=
    NonMainBiasZero.reachable_nonMainBiasZero
      init (trace init ω v) hvalid hreach
  intro x hx hm
  exact hzero x hx hm
    (hwindow x hx).1
    (by
      have hw := (hwindow x hx).2
      omega)

/-- The winning sign carries at least the magnitude of the conserved
signed gap at every actual snapshot. -/
theorem winningSignMass_at_snapshot
    {init : InputCfg n} (hvalid : validInitial init)
    {ω : InputLog n}
    {a s t v M ell : ℕ} {σ : Sign}
    (hpath : Prefix init ω a s t)
    (hseed :
      LateSamplingSeedReceipt init M ell σ
        (trace init ω s))
    (hsv : s ≤ v) (hvt : v ≤ t) :
    (gapMagnitude init : ℚ) ≤
      signMass σ (trace init ω v) := by
  have hwindow :=
    hpath.window v (hpath.start_order.trans hsv) hvt
  have hphase :
      ∀ x ∈ trace init ω v, 3 ≤ x.phase.val :=
    fun x hx => (hwindow x hx).1
  have hcarrier :=
    nonmain_bias_zero_at_snapshot
      hvalid hpath hsv hvt
  have hmass :=
    prePhaseFourMass_at_snapshot
      hvalid hpath hsv hvt
  have hsub :=
    sideMass_sub (trace init ω v)
  rw [hmass] at hsub
  cases σ with
  | pos =>
      have hwin : 0 < initialGap init := by
        simpa [winningSign] using hseed.winning
      have hcastInt :
          ((gapMagnitude init : ℕ) : ℤ) =
            initialGap init := by
        unfold gapMagnitude
        rw [Int.natCast_natAbs, abs_of_pos hwin]
      have hcast :
          (gapMagnitude init : ℚ) =
            (initialGap init : ℚ) := by
        exact_mod_cast hcastInt
      have hside :=
        sideMass_eq_signMass .pos
          (trace init ω v) hphase hcarrier
      have hnonneg :=
        sideMass_nonneg .neg (trace init ω v)
      rw [← hside, hcast]
      linarith
  | neg =>
      have hwin : initialGap init < 0 := by
        simpa [winningSign] using hseed.winning
      have hcastInt :
          ((gapMagnitude init : ℕ) : ℤ) =
            -initialGap init := by
        unfold gapMagnitude
        rw [Int.natCast_natAbs, abs_of_neg hwin]
      have hcast :
          (gapMagnitude init : ℚ) =
            -(initialGap init : ℚ) := by
        exact_mod_cast hcastInt
      have hside :=
        sideMass_eq_signMass .neg
          (trace init ω v) hphase hcarrier
      have hnonneg :=
        sideMass_nonneg .pos (trace init ω v)
      rw [← hside, hcast]
      linarith

/-- The readout scale and conserved winning mass give the `.4M`
lower bound at every actual snapshot. -/
theorem winningScaledFloor_at_snapshot
    {init : InputCfg n} (hvalid : validInitial init)
    {ω : InputLog n}
    {a s t v M ell : ℕ} {σ : Sign}
    (hpath : Prefix init ω a s t)
    (hseed :
      LateSamplingSeedReceipt init M ell σ
        (trace init ω s))
    (hsv : s ≤ v) (hvt : v ≤ t) :
    (2 / 5 : ℚ) * (M : ℚ) ≤
      (2 : ℚ) ^ ell *
        signMass σ (trace init ω v) := by
  have hgap :=
    winningSignMass_at_snapshot
      hvalid hpath hseed hsv hvt
  have hscaledGap :=
    mul_le_mul_of_nonneg_left hgap
      (show (0 : ℚ) ≤ (2 : ℚ) ^ ell by positivity)
  have hscale :
      (2 : ℚ) * (M : ℚ) ≤
        5 * (2 : ℚ) ^ ell *
          (gapMagnitude init : ℚ) := by
    exact_mod_cast hseed.scaleLower
  nlinarith

/-- The original `.002M` all-sign shallow budget, together with the shallow
transport at cutoff `ell - 1`, gives `S ≤ .001M` at every snapshot. -/
theorem previousShallowBudget_at_snapshot
    {init : InputCfg n} {ω : InputLog n}
    {a s t v M ell : ℕ} {σ : Sign}
    (hpath : Prefix init ω a s t)
    (hseed :
      LateSamplingSeedReceipt init M ell σ
        (trace init ω s))
    (hsv : s ≤ v) (hvt : v ≤ t) :
    (1000 : ℚ) *
        scaledShallowPositive σ (ell - 1)
          (trace init ω v) ≤
      (M : ℚ) := by
  have hell : 1 ≤ ell := by
    have := hseed.levelLower
    omega
  have htransport :=
    LateSamplingShallowTransport.scaledShallowPositive_seed_mono
      (ell := ell - 1) (σ := σ)
      hpath hsv hvt
  have hstrict :=
    twice_scaledShallowPrevious_le_shallowMass
      σ ell (trace init ω s) hell
  have hseedBudget := hseed.shallow
  nlinarith

/-! ## The `hmass` statement -/

/-- The first-branch `.4M` shape inequality at every actual prefix
snapshot.

The old-index cutoff in `hseed` is intentionally not used: the theorem is
stronger than the originally proposed route. -/
theorem firstBranchHmass_at_snapshot
    {init : InputCfg n} (hvalid : validInitial init)
    {ω : InputLog n}
    {a s t v M ell : ℕ} {σ : Sign}
    (hpath : Prefix init ω a s t)
    (hseed :
      LateSamplingSeedReceipt init M ell σ
        (trace init ω s))
    (hsv : s ≤ v) (hvt : v ≤ t) :
    592 * M ≤
      3000 * bandCount σ ell 0 (trace init ω v) +
        1000 * bandCount σ (ell + 1) 0
          (trace init ω v) := by
  have hell : 1 ≤ ell := by
    have := hseed.levelLower
    omega
  have hcount :=
    mainCount_at_snapshot hpath hseed hsv hvt
  have hfloor :=
    winningScaledFloor_at_snapshot
      hvalid hpath hseed hsv hvt
  have hshallow :=
    previousShallowBudget_at_snapshot
      hpath hseed hsv hvt
  have hcapacity :=
    winningMass_capacity
      σ ell (trace init ω v) hell
  rw [hcount] at hcapacity
  have hq :
      (1600 : ℚ) * (M : ℚ) ≤
        1008 * (M : ℚ) +
          3000 *
            (bandCount σ ell 0
              (trace init ω v) : ℚ) +
          1000 *
            (bandCount σ (ell + 1) 0
              (trace init ω v) : ℚ) := by
    nlinarith only [hfloor, hshallow, hcapacity]
  have hnat :
      1600 * M ≤
        1008 * M +
          3000 * bandCount σ ell 0
            (trace init ω v) +
          1000 * bandCount σ (ell + 1) 0
            (trace init ω v) := by
    exact_mod_cast hq
  exact first_branch_mass_to_shape_from_capacity
    M
    (bandCount σ ell 0 (trace init ω v))
    (bandCount σ (ell + 1) 0 (trace init ω v))
    hnat

/-! ## Complete deterministic first-branch receipt -/

/-- All deterministic data discharged in this file.

The cutoff is retained at the genuine seed for the later retrospective
arrival argument. -/
structure FirstBranchShapeData
    {init : InputCfg n} {ω : InputLog n}
    (s v M ell : ℕ) (σ : Sign) : Prop where
  main_count :
    timeMainCount (trace init ω v) = M
  old_index_cutoff_at_seed :
    noIndexBelow (ell - terminalCutoff n)
      (trace init ω s)
  level_weight :
    (bandCount σ ell 0 (trace init ω v) : ℚ) ≤
      scaledShallowPositive σ ell (trace init ω v)
  mass_shape :
    592 * M ≤
      3000 * bandCount σ ell 0 (trace init ω v) +
        1000 * bandCount σ (ell + 1) 0
          (trace init ω v)
  partition :
    bandCount σ ell 1 (trace init ω v) =
      bandCount σ ell 0 (trace init ω v) +
        bandCount σ (ell + 1) 0
          (trace init ω v)

/-- Produce every deterministic input required by the current-snapshot
consumer. -/
theorem firstBranchShapeData_at
    {init : InputCfg n} (hvalid : validInitial init)
    {ω : InputLog n}
    {a s t v M ell : ℕ} {σ : Sign}
    (hpath : Prefix init ω a s t)
    (hseed :
      LateSamplingSeedReceipt init M ell σ
        (trace init ω s))
    (hsv : s ≤ v) (hvt : v ≤ t) :
    FirstBranchShapeData
      (init := init) (ω := ω) s v M ell σ := by
  refine
    { main_count :=
        mainCount_at_snapshot hpath hseed hsv hvt
      old_index_cutoff_at_seed :=
        hseed.old_index_cutoff
      level_weight :=
        bandCount_exact_le_scaledShallowPositive
          σ ell (trace init ω v)
      mass_shape :=
        firstBranchHmass_at_snapshot
          hvalid hpath hseed hsv hvt
      partition :=
        bandCount_width_one_partition
          σ ell (trace init ω v) }

/-- The two-class current-snapshot disjunction with every deterministic
shape premise discharged.

Shallow transport is supplied internally through
`LateSamplingShallowCorollary.two_class_at_of_prefix`. -/
theorem twoClass_at_of_receipt
    {init : InputCfg n} (hvalid : validInitial init)
    {ω : InputLog n}
    {a s t v M ell : ℕ} {σ : Sign}
    (hpath : Prefix init ω a s t)
    (hseed :
      LateSamplingSeedReceipt init M ell σ
        (trace init ω s))
    (hsv : s ≤ v) (hvt : v ≤ t) :
    5698 * M ≤
        10000 * bandCount σ ell 1
          (trace init ω v) ∨
      939 * M ≤
        1000 * bandCount σ ell 1
          (trace init ω v) := by
  have hshape :=
    firstBranchShapeData_at
      hvalid hpath hseed hsv hvt
  exact
    LateSamplingShallowCorollary.two_class_at_of_prefix
      hpath hseed hsv hvt
      hshape.main_count
      hshape.level_weight
      hshape.mass_shape
      hshape.partition

end Ripple.PopulationProtocol.ExactMajority.LateSamplingFirstBranchShape

end
