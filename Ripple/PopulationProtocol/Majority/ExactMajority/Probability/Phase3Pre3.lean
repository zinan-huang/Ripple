import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Phase3TransitionAlgebra
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.RoleSplitConcentration
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.DominantLevelChoice
import Mathlib.Tactic

namespace ExactMajority

open scoped BigOperators

namespace Phase3Pre3

open P3DeterministicAlgebra

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

/-!
Slot-3 `Pre3` is an honest package for the Lemma-5.3 consequences consumed by
the Phase-3 §6 induction.  It consumes the slot-0 role split as
`RoleSplitGood`; it does not restate or re-prove role counts as independent
fields.
-/

/-! ## Phase-3 entry observables -/

/-- Real-valued signed dyadic bias, using the deterministic Phase-3 algebra
observable `biasSumQ = betaPlusQ - betaMinusQ`. -/
noncomputable def signedGap (c : Config (AgentState L K)) : ℝ :=
  (biasSumQ (L := L) (K := K) c : ℝ)

/-- Real-valued weighted dyadic mass `mu = betaPlusQ + betaMinusQ`. -/
noncomputable def weightedMass (c : Config (AgentState L K)) : ℝ :=
  (totalMassQ (L := L) (K := K) c : ℝ)

/-- The signed value represented by a positive gap magnitude and a majority sign. -/
def signedGapOf : Sign → ℝ → ℝ
  | .pos, gap => gap
  | .neg, gap => -gap

@[simp] theorem signedGapOf_pos (gap : ℝ) :
    signedGapOf Sign.pos gap = gap := rfl

@[simp] theorem signedGapOf_neg (gap : ℝ) :
    signedGapOf Sign.neg gap = -gap := rfl

/-! ## Phase-3 initialization fields -/

/-- Phase-3 Init's dyadic interpretation of `smallBias`, matching the
`phaseInit p=3` branch. -/
def phase3BiasOfSmallBias (sb : Fin 7) : Bias L :=
  let zeroFin : Fin (L + 1) := ⟨0, by omega⟩
  if sb.val < 3 then Bias.dyadic Sign.neg zeroFin
  else if sb.val > 3 then Bias.dyadic Sign.pos zeroFin
  else Bias.zero

/-- Pointwise Phase-3 entry state.

The role split itself is not part of this predicate.  It only records the fields
written by the Phase-3 initializer plus the global phase support:
Main agents receive the dyadic sign of `smallBias` at exponent index `0` and
hour `0`; Clock agents receive zero bias and minute `0`; non-Main/Clock roles
receive zero bias. -/
def Phase3EntryAgent (a : AgentState L K) : Prop :=
  a.phase.val = 3 ∧
    match a.role with
    | Role.main =>
        a.bias = phase3BiasOfSmallBias (L := L) a.smallBias ∧ a.hour.val = 0
    | Role.clock =>
        a.bias = Bias.zero ∧ a.minute.val = 0
    | Role.reserve => a.bias = Bias.zero
    | Role.mcr => a.bias = Bias.zero
    | Role.cr => a.bias = Bias.zero

/-- Configuration-level Phase-3 initialization predicate. -/
def Phase3EntryInit (c : Config (AgentState L K)) : Prop :=
  ∀ a ∈ c, Phase3EntryAgent (L := L) (K := K) a

theorem phase_eq_three_of_Phase3EntryInit {c : Config (AgentState L K)}
    (hinit : Phase3EntryInit (L := L) (K := K) c)
    {a : AgentState L K} (ha : a ∈ c) :
    a.phase.val = 3 :=
  (hinit a ha).1

theorem nonMain_bias_zero_of_Phase3EntryAgent {a : AgentState L K}
    (h : Phase3EntryAgent (L := L) (K := K) a) (hm : a.role ≠ Role.main) :
    a.bias = Bias.zero := by
  rcases h with ⟨_, hfields⟩
  cases hr : a.role with
  | main =>
      exact False.elim (hm hr)
  | reserve =>
      rw [hr] at hfields
      exact hfields
  | clock =>
      rw [hr] at hfields
      exact hfields.1
  | mcr =>
      rw [hr] at hfields
      exact hfields
  | cr =>
      rw [hr] at hfields
      exact hfields

theorem clock_minute_zero_of_Phase3EntryAgent {a : AgentState L K}
    (h : Phase3EntryAgent (L := L) (K := K) a) (hc : a.role = Role.clock) :
    a.minute.val = 0 := by
  rcases h with ⟨_, hfields⟩
  rw [hc] at hfields
  exact hfields.2

theorem main_hour_zero_of_Phase3EntryAgent {a : AgentState L K}
    (h : Phase3EntryAgent (L := L) (K := K) a) (hm : a.role = Role.main) :
    a.hour.val = 0 := by
  rcases h with ⟨_, hfields⟩
  rw [hm] at hfields
  exact hfields.2

theorem main_bias_of_Phase3EntryAgent {a : AgentState L K}
    (h : Phase3EntryAgent (L := L) (K := K) a) (hm : a.role = Role.main) :
    a.bias = phase3BiasOfSmallBias (L := L) a.smallBias := by
  rcases h with ⟨_, hfields⟩
  rw [hm] at hfields
  exact hfields.1

/-! ## Majority/tie mode and dominant-level domain -/

/-- Slot-3 entry mode: strict majority with an explicit majority sign, or tie. -/
inductive Pre3Mode where
  | majority (σ : Sign)
  | tie
  deriving DecidableEq, Repr

/-- The early-hour domain is always written without Nat subtraction. -/
def EarlyHour (h ell : ℕ) : Prop :=
  h + 5 ≤ ell

/-- Lemma-5.3 small-gap entry condition.

`gap` is the nonnegative magnitude `|signedGap|`.  In the majority branch it is
strictly positive and below `0.025*M = M/40`, with the mode sign tying it back to
the signed conserved sum.  The tie branch fixes both signed gap and magnitude to
zero. -/
def SmallGapEntry : Pre3Mode → ℝ → ℝ → ℝ → Prop
  | .majority σ, signed, gap, M =>
      signed = signedGapOf σ gap ∧ (1 : ℝ) ≤ gap ∧ gap < (1 / 40 : ℝ) * M
  | .tie, signed, gap, _M =>
      signed = 0 ∧ gap = 0

/-- Dominant-level input, including the explicit `5 <= ell` domain fact.

The majority branch carries `ell + 2 <= L`, needed later for Lemma 6.18's
`end_(ell+2)` domain.  The tie branch uses Doty's convention `ell = L + 5` and
does not manufacture a dummy dominant-level window. -/
structure DominantInput (L : ℕ) (M gap : ℝ) (ell : ℕ) (mode : Pre3Mode) : Prop where
  ell_ge_five : 5 ≤ ell
  mode_domain :
    match mode with
    | .majority _ => ell + 2 ≤ L ∧ DominantLevelChoice.Window M gap ell
    | .tie => ell = L + 5

theorem early_zero_of_ell_ge_five {ell : ℕ} (h : 5 ≤ ell) :
    EarlyHour 0 ell := by
  simpa [EarlyHour] using h

theorem early_zero_of_DominantInput {M gap : ℝ} {ell : ℕ} {mode : Pre3Mode}
    (h : DominantInput L M gap ell mode) :
    EarlyHour 0 ell :=
  early_zero_of_ell_ge_five h.ell_ge_five

theorem dominantWindow_of_DominantInput_majority {M gap : ℝ} {ell : ℕ} {σ : Sign}
    (h : DominantInput L M gap ell (Pre3Mode.majority σ)) :
    DominantLevelChoice.Window M gap ell :=
  h.mode_domain.2

theorem ell_add_two_le_L_of_DominantInput_majority {M gap : ℝ} {ell : ℕ} {σ : Sign}
    (h : DominantInput L M gap ell (Pre3Mode.majority σ)) :
    ell + 2 ≤ L :=
  h.mode_domain.1

theorem ell_eq_L_add_five_of_DominantInput_tie {M gap : ℝ} {ell : ℕ}
    (h : DominantInput L M gap ell Pre3Mode.tie) :
    ell = L + 5 :=
  h.mode_domain

/-! ## The Pre3 bundle -/

/-- The Phase-3 base package consumed by the §6 strong induction.

`M` is tied to the Main-role count, `signed_gap` is tied to the deterministic
Phase-3 algebra's signed mass, and `gap` is tied to `|signed_gap|`.  The mass
bound uses `weightedMass`, i.e. `P3DeterministicAlgebra.totalMassQ`, not a biased
agent count. -/
structure Pre3 (η : ℝ) (n : ℕ) (mode : Pre3Mode) (ell : ℕ)
    (c : Config (AgentState L K)) where
  M : ℝ
  signed_gap : ℝ
  gap : ℝ
  M_def : M = (RoleSplitConcentration.mainCount (L := L) (K := K) c : ℝ)
  signed_gap_def : signed_gap = signedGap (L := L) (K := K) c
  gap_def : gap = |signed_gap|
  roleSplit : RoleSplitConcentration.RoleSplitGood (L := L) (K := K) η n c
  phase3_init : Phase3EntryInit (L := L) (K := K) c
  small_gap : SmallGapEntry mode signed_gap gap M
  mass_bound : weightedMass (L := L) (K := K) c ≤ (3 / 100 : ℝ) * M
  dominant : DominantInput L M gap ell mode

namespace Pre3

variable {η : ℝ} {n ell : ℕ} {mode : Pre3Mode} {c : Config (AgentState L K)}

theorem M_nonneg (h : Pre3 (L := L) (K := K) η n mode ell c) : 0 ≤ h.M := by
  rw [h.M_def]
  exact_mod_cast Nat.zero_le (RoleSplitConcentration.mainCount (L := L) (K := K) c)

theorem ell_ge_five (h : Pre3 (L := L) (K := K) η n mode ell c) :
    5 ≤ ell :=
  h.dominant.ell_ge_five

theorem early_zero (h : Pre3 (L := L) (K := K) η n mode ell c) :
    EarlyHour 0 ell :=
  early_zero_of_DominantInput h.dominant

theorem roleMCR_zero (h : Pre3 (L := L) (K := K) η n mode ell c) :
    RoleSplitConcentration.roleMCRCount (L := L) (K := K) c = 0 :=
  h.roleSplit.1

theorem main_lower_window (h : Pre3 (L := L) (K := K) η n mode ell c) :
    (1 - η) * (n : ℝ) / 2 ≤
      (RoleSplitConcentration.mainCount (L := L) (K := K) c : ℝ) :=
  h.roleSplit.2.1

theorem main_upper_window (h : Pre3 (L := L) (K := K) η n mode ell c) :
    (RoleSplitConcentration.mainCount (L := L) (K := K) c : ℝ) ≤
      (1 + η) * (n : ℝ) / 2 :=
  h.roleSplit.2.2.1

theorem clock_lower_window (h : Pre3 (L := L) (K := K) η n mode ell c) :
    (1 - η) * (n : ℝ) / 4 ≤
      (RoleSplitConcentration.clockCount (L := L) (K := K) c : ℝ) :=
  h.roleSplit.2.2.2.1

theorem reserve_lower_window (h : Pre3 (L := L) (K := K) η n mode ell c) :
    (1 - η) * (n : ℝ) / 4 ≤
      (RoleSplitConcentration.reserveCount (L := L) (K := K) c : ℝ) :=
  h.roleSplit.2.2.2.2

theorem clock_floor (hη : η ≤ 1 / 25)
    (h : Pre3 (L := L) (K := K) η n mode ell c) :
    (n : ℝ) / 5 ≤
      (RoleSplitConcentration.clockCount (L := L) (K := K) c : ℝ) :=
  RoleSplitConcentration.clockCount_linear_of_RoleSplitGood hη h.roleSplit

theorem reserve_floor (hη : η ≤ 1 / 25)
    (h : Pre3 (L := L) (K := K) η n mode ell c) :
    (n : ℝ) / 5 ≤
      (RoleSplitConcentration.reserveCount (L := L) (K := K) c : ℝ) :=
  RoleSplitConcentration.reserveCount_linear_of_RoleSplitGood hη h.roleSplit

theorem main_floor (hη : η ≤ 1 / 25)
    (h : Pre3 (L := L) (K := K) η n mode ell c) :
    (n : ℝ) / 3 ≤
      (RoleSplitConcentration.mainCount (L := L) (K := K) c : ℝ) :=
  RoleSplitConcentration.mainCount_lower_of_RoleSplitGood hη h.roleSplit

theorem all_phase_three
    (h : Pre3 (L := L) (K := K) η n mode ell c)
    {a : AgentState L K} (ha : a ∈ c) :
    a.phase.val = 3 :=
  phase_eq_three_of_Phase3EntryInit h.phase3_init ha

theorem total_mass_base
    (h : Pre3 (L := L) (K := K) η n mode ell c) :
    weightedMass (L := L) (K := K) c ≤ (3 / 100 : ℝ) * h.M :=
  h.mass_bound

theorem majority_signed_gap {σ : Sign}
    (h : Pre3 (L := L) (K := K) η n (Pre3Mode.majority σ) ell c) :
    h.signed_gap = signedGapOf σ h.gap :=
  h.small_gap.1

theorem majority_small_gap {σ : Sign}
    (h : Pre3 (L := L) (K := K) η n (Pre3Mode.majority σ) ell c) :
    (1 : ℝ) ≤ h.gap ∧ h.gap < (1 / 40 : ℝ) * h.M :=
  h.small_gap.2

theorem majority_dominantWindow {σ : Sign}
    (h : Pre3 (L := L) (K := K) η n (Pre3Mode.majority σ) ell c) :
    DominantLevelChoice.Window h.M h.gap ell :=
  h.dominant.mode_domain.2

theorem majority_ell_add_two_le_L {σ : Sign}
    (h : Pre3 (L := L) (K := K) η n (Pre3Mode.majority σ) ell c) :
    ell + 2 ≤ L :=
  h.dominant.mode_domain.1

theorem tie_signed_gap_zero
    (h : Pre3 (L := L) (K := K) η n Pre3Mode.tie ell c) :
    h.signed_gap = 0 :=
  h.small_gap.1

theorem tie_gap_zero
    (h : Pre3 (L := L) (K := K) η n Pre3Mode.tie ell c) :
    h.gap = 0 :=
  h.small_gap.2

theorem tie_ell_eq_L_add_five
    (h : Pre3 (L := L) (K := K) η n Pre3Mode.tie ell c) :
    ell = L + 5 :=
  h.dominant.mode_domain

/-- Feed majority-mode `Pre3` into the existing dominant-level lower-edge
adapter.  The caller supplies the current majority/minority weighted masses in
the same units as `gap`. -/
theorem gapMassLower_of_pre3_majority {σ : Sign}
    (h : Pre3 (L := L) (K := K) η n (Pre3Mode.majority σ) ell c)
    {betaMaj betaMin : ℝ}
    (hgap : h.gap = betaMaj - betaMin) (hmin : 0 ≤ betaMin) :
    (0.4 : ℝ) * h.M * (2 : ℝ) ^ (-(ell : ℤ)) ≤ betaMaj :=
  DominantLevelChoice.gapMassLower_of_dominantLevelChoice ell
    (M := h.M) (g := h.gap) (hM := Pre3.M_nonneg h)
    (hchoice := Pre3.majority_dominantWindow h) hgap hmin

end Pre3

/-! ## Bridge package: explicit constructor inputs -/

/-- Constructor inputs for `Pre3`.

Expected producers:
* `roleSplit_at_phase3`: slot-0 Lemma 5.2 output, transported through the
  phase-1/2 path by role preservation;
* `small_gap`, `mass_bound`, and `dominant`: Lemma 5.3 plus the dominant-level
  construction;
* `phase3_init`: the phase-2-to-3 seam / `phaseInit 3` bridge.
-/
structure Pre3BridgeInputs (η : ℝ) (n : ℕ) (mode : Pre3Mode) (ell : ℕ)
    (c : Config (AgentState L K)) where
  M : ℝ
  signed_gap : ℝ
  gap : ℝ
  M_def : M = (RoleSplitConcentration.mainCount (L := L) (K := K) c : ℝ)
  signed_gap_def : signed_gap = signedGap (L := L) (K := K) c
  gap_def : gap = |signed_gap|
  roleSplit_at_phase3 :
    RoleSplitConcentration.RoleSplitGood (L := L) (K := K) η n c
  phase3_init : Phase3EntryInit (L := L) (K := K) c
  small_gap : SmallGapEntry mode signed_gap gap M
  mass_bound : weightedMass (L := L) (K := K) c ≤ (3 / 100 : ℝ) * M
  dominant : DominantInput L M gap ell mode

/-- The explicit bridge-input package directly constructs `Pre3`. -/
def Pre3.ofBridgeInputs {η : ℝ} {n ell : ℕ} {mode : Pre3Mode}
    {c : Config (AgentState L K)}
    (B : Pre3BridgeInputs (L := L) (K := K) η n mode ell c) :
    Pre3 (L := L) (K := K) η n mode ell c where
  M := B.M
  signed_gap := B.signed_gap
  gap := B.gap
  M_def := B.M_def
  signed_gap_def := B.signed_gap_def
  gap_def := B.gap_def
  roleSplit := B.roleSplit_at_phase3
  phase3_init := B.phase3_init
  small_gap := B.small_gap
  mass_bound := B.mass_bound
  dominant := B.dominant

#print axioms Pre3.clock_lower_window
#print axioms Pre3.reserve_lower_window
#print axioms Pre3.main_lower_window
#print axioms Pre3.total_mass_base
#print axioms Pre3.majority_dominantWindow
#print axioms Pre3.gapMassLower_of_pre3_majority

end Phase3Pre3
end ExactMajority
