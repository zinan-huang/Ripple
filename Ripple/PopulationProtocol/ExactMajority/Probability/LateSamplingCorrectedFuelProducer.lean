-- Ripple/PopulationProtocol/ExactMajority/Probability/LateSamplingCorrectedFuelProducer.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.LateSamplingStrongSeedReceipt
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseZeroEntry
import Mathlib.Tactic.FieldSimp

/-!
# Corrected completed-snapshot fuel producer

This file fills the deterministic obligations left open by
`LateSamplingFuelFeasibilityAudit`:

* the coefficient-one adjacent debt estimate
  `D_(ell+1) ≤ 2 B_ell + A_ell`;
* exact natural floor caps for the tail and minority exact-level class;
* the three corrected row-two branches;
* the finite floor/ceiling slack at the paper constants; and
* conversion of the resulting `CorrectedEntryFuelCertificate` to the actual
  `TwoLevelFuelLedger` entry.

The probability item remains responsible only for supplying the scaled
completed-snapshot inequalities packaged in `CompletedRowTwoFuelSnapshot`.
-/

noncomputable section

namespace Ripple.PopulationProtocol.ExactMajority.LateSamplingCorrectedFuelProducer

open TimeTheorem
open LateSamplingFuelFeasibilityAudit
open LateSamplingStrongSeedReceipt

variable {L K n : ℕ}

abbrev InputCfg (n : ℕ) :=
  Config (AgentState (PhaseThreeModel.Numeric.hourIndex n) 256)

/-- Majority-sign Main count at the selected exact dyadic level. -/
noncomputable def majorityExact
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (σ : Sign) (c : InputCfg n) : ℕ :=
  Phase5Convergence.biasedMainClassU
    (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256) σ ell c

/-- Minority-sign Main count at the selected exact dyadic level. -/
noncomputable def minorityExact
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (σ : Sign) (c : InputCfg n) : ℕ :=
  Phase5Convergence.biasedMainClassU
    (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
    (Phase3Post3.minoritySignOfMajority σ) ell c

/-- Literal natural floors used by the three corrected branches. -/
def lowerDebtCap (M : ℕ) : ℕ := M / 500

def minorityExactCap (M : ℕ) : ℕ := M / 250

def crossoverExactCap (M : ℕ) : ℕ := (696 * M) / 2375

def firstDebtCap (M : ℕ) : ℕ := (191 * M) / 10000

def adjacentDebtCap (M : ℕ) : ℕ :=
  2 * lowerDebtCap M + crossoverExactCap M + minorityExactCap M

/-- The two row-two alternatives in the integer forms consumed below.

The first branch carries the majority exact-level cap `.0111 M` and the
adjacent-union sample floor `.5697 R`.

The second branch carries the exact-class sample inequality with the `.0021 R`
loss and the adjacent-union floor `.9389 R`.  The producer later compares the
actual majority exact-level count with `696 M / 2375`. -/
inductive RowTwoFuelOutcome {n : ℕ}
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (σ : Sign) (M R : ℕ) (c : InputCfg n) : Prop where
  | first
      (majority_scaled :
        10000 * majorityExact ell σ c ≤ 111 * M)
      (union_sample_scaled :
        5697 * R ≤
          10000 * Phase6FuelLedger.twoReserveFuel
            (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256) ell c)
  | second
      (exact_sample_scaled :
        10000 * majorityExact ell σ c * R ≤
          10000 * M * Phase6FuelLedger.reserveFuel
            (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256) ell c +
          21 * M * R)
      (union_sample_scaled :
        9389 * R ≤
          10000 * Phase6FuelLedger.twoReserveFuel
            (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256) ell c)

/-- Exact deterministic payload required from the row-two snapshot producer.
The first two fields are the integer-scaled `.002 M` upper-tail and `.004 M`
minority exact-level estimates. -/
structure CompletedRowTwoFuelSnapshot {n : ℕ}
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (σ : Sign) (M R : ℕ) (c : InputCfg n) : Prop where
  upper_tail_scaled :
    500 * Lemma615MassAbove.massAboveScaled
      (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256) ell.val c ≤ M
  minority_scaled :
    250 * minorityExact ell σ c ≤ M
  outcome : RowTwoFuelOutcome ell σ M R c

/-! ## Sharp coefficient-one debt estimate -/

/-- Agentwise debt plus the exact-level indicator is bounded by the scaled mass
at cutoff `ell+1`.  At `j=ell`, the left side is `1+1` and the right side is
`2`; below `ell` this is just `2^d-1 ≤ 2^d`. -/
theorem union_agent_debt_add_level_le_next_mass
    (ell : Fin (L + 1)) (a : AgentState L K) :
    Phase6FuelLedger.unionAgentDebt (L := L) (K := K) ell a +
        Phase5To6FuelProducer.agentMainAtLevelW
          (L := L) (K := K) ell a ≤
      Lemma615MassAbove.agentMassAboveScaledW
        (L := L) (K := K) (ell.val + 1) a := by
  classical
  unfold Phase6FuelLedger.unionAgentDebt
    Phase5To6FuelProducer.agentMainAtLevelW
    Lemma615MassAbove.agentMassAboveScaledW
    Lemma615MassAbove.biasMassAboveScaledW
  by_cases hm : a.role = Role.main
  · simp only [hm, if_pos]
    cases hb : a.bias with
    | zero =>
        simp [Phase5To6FuelProducer.MainAtLevel, hb]
    | dyadic τ j =>
        simp only [hb]
        by_cases hj : j.val < ell.val + 1
        · by_cases hjeq : j = ell
          · subst j
            have hlevel :
                Phase5To6FuelProducer.MainAtLevel
                  (L := L) (K := K) ell a :=
              ⟨hm, ⟨τ, hb⟩⟩
            simp [hlevel]
          · have hlevel :
                ¬ Phase5To6FuelProducer.MainAtLevel
                  (L := L) (K := K) ell a := by
              intro h
              rcases h.2 with ⟨ρ, hρ⟩
              rw [hb] at hρ
              injection hρ with _ hindex
              exact hjeq hindex
            simp only [hj, if_pos, hlevel, if_neg, add_zero]
            exact Nat.sub_le _ _
        · have hlevel :
              ¬ Phase5To6FuelProducer.MainAtLevel
                (L := L) (K := K) ell a := by
            intro h
            rcases h.2 with ⟨ρ, hρ⟩
            rw [hb] at hρ
            injection hρ with _ hindex
            apply hj
            simpa [hindex] using Nat.lt_succ_self ell.val
          simp [hj, hlevel]
  · simp [hm, Phase5To6FuelProducer.MainAtLevel]

/-- The pointwise coefficient-one form. -/
theorem union_agent_debt_le_two_tail_add_level
    (ell : Fin (L + 1)) (a : AgentState L K) :
    Phase6FuelLedger.unionAgentDebt (L := L) (K := K) ell a ≤
      2 * Lemma615MassAbove.agentMassAboveScaledW
          (L := L) (K := K) ell.val a +
        Phase5To6FuelProducer.agentMainAtLevelW
          (L := L) (K := K) ell a := by
  have hcover := union_agent_debt_add_level_le_next_mass
    (L := L) (K := K) ell a
  have hnext := Phase5To6FuelProducer.agentMassAboveScaledW_succ
    (L := L) (K := K) ell a
  rw [hnext] at hcover
  omega

/-- Configuration-level coefficient-one debt bound
`D_(ell+1) ≤ 2 B_ell + A_ell`. -/
theorem union_split_debt_le_two_tail_add_level
    (ell : Fin (L + 1)) (c : Config (AgentState L K)) :
    Phase6FuelLedger.unionSplitDebt (L := L) (K := K) ell c ≤
      2 * Lemma615MassAbove.massAboveScaled
          (L := L) (K := K) ell.val c +
        Phase5To6FuelProducer.mainAtLevelU
          (L := L) (K := K) ell c := by
  induction c using Multiset.induction_on with
  | empty =>
      simp [Phase6FuelLedger.unionSplitDebt,
        Lemma615MassAbove.massAboveScaled,
        Phase5To6FuelProducer.mainAtLevelU]
  | cons a c ih =>
      simp only [Phase6FuelLedger.unionSplitDebt,
        Lemma615MassAbove.massAboveScaled,
        Phase5To6FuelProducer.mainAtLevelU,
        Multiset.map_cons, Multiset.sum_cons] at ih ⊢
      have ha := union_agent_debt_le_two_tail_add_level
        (L := L) (K := K) ell a
      omega

/-- The exact-level total is the sum of the chosen majority sign and its
minority sign. -/
theorem main_at_level_eq_exact_classes
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (σ : Sign) (c : InputCfg n) :
    Phase5To6FuelProducer.mainAtLevelU
        (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256) ell c =
      majorityExact ell σ c + minorityExact ell σ c := by
  simpa [majorityExact, minorityExact] using
    (Phase5To6FuelProducer.mainAtLevelU_eq_majority_add_minority
      (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256) σ ell c)

/-! ## Integer floor lemmas -/

private theorem upper_tail_le_lower_cap
    {B M : ℕ} (h : 500 * B ≤ M) :
    B ≤ lowerDebtCap M := by
  unfold lowerDebtCap
  apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 500)).2
  simpa [mul_comm] using h

/-- The scaled `.004 M` row-two inequality gives the exact natural floor cap. -/
theorem minority_exact_level_cap
    {N M : ℕ} (h : 250 * N ≤ M) :
    N ≤ minorityExactCap M := by
  unfold minorityExactCap
  apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 250)).2
  simpa [mul_comm] using h

private theorem majority_exact_le_first_floor
    {A M : ℕ} (h : 10000 * A ≤ 111 * M) :
    A ≤ (111 * M) / 10000 := by
  apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 10000)).2
  simpa [mul_comm] using h

private theorem majority_exact_le_crossover_floor
    {A M : ℕ} (h : ¬ 696 * M ≤ 2375 * A) :
    A ≤ crossoverExactCap M := by
  unfold crossoverExactCap
  apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 2375)).2
  omega

/-- Sum of the three first-alternative component floors is bounded by the
single floor `floor(.0191 M)`. -/
theorem first_debt_components_le_first_cap (M : ℕ) :
    2 * lowerDebtCap M + (111 * M) / 10000 + minorityExactCap M ≤
      firstDebtCap M := by
  unfold lowerDebtCap minorityExactCap firstDebtCap
  apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 10000)).2
  have htail := Nat.mul_div_le M 500
  have hmajority := Nat.mul_div_le (111 * M) 10000
  have hminority := Nat.mul_div_le M 250
  omega

private theorem lower_debt_cap_cast_le (M : ℕ) :
    (lowerDebtCap M : ℝ) ≤ (1 / 500 : ℝ) * (M : ℝ) := by
  calc
    (lowerDebtCap M : ℝ) = ((M / 500 : ℕ) : ℝ) := rfl
    _ ≤ (M : ℝ) / (500 : ℝ) := Nat.cast_div_le
    _ = (1 / 500 : ℝ) * (M : ℝ) := by ring

private theorem minority_exact_cap_cast_le (M : ℕ) :
    (minorityExactCap M : ℝ) ≤ (1 / 250 : ℝ) * (M : ℝ) := by
  calc
    (minorityExactCap M : ℝ) = ((M / 250 : ℕ) : ℝ) := rfl
    _ ≤ (M : ℝ) / (250 : ℝ) := Nat.cast_div_le
    _ = (1 / 250 : ℝ) * (M : ℝ) := by ring

private theorem crossover_exact_cap_cast_le (M : ℕ) :
    (crossoverExactCap M : ℝ) ≤ (696 / 2375 : ℝ) * (M : ℝ) := by
  calc
    (crossoverExactCap M : ℝ) =
        ((((696 * M) / 2375) : ℕ) : ℝ) := rfl
    _ ≤ ((696 * M : ℕ) : ℝ) / (2375 : ℝ) := Nat.cast_div_le
    _ = (696 / 2375 : ℝ) * (M : ℝ) := by
      push_cast
      ring

private theorem first_debt_cap_cast_le (M : ℕ) :
    (firstDebtCap M : ℝ) ≤ (191 / 10000 : ℝ) * (M : ℝ) := by
  calc
    (firstDebtCap M : ℝ) =
        ((((191 * M) / 10000) : ℕ) : ℝ) := rfl
    _ ≤ ((191 * M : ℕ) : ℝ) / (10000 : ℝ) := Nat.cast_div_le
    _ = (191 / 10000 : ℝ) * (M : ℝ) := by
      push_cast
      ring

private theorem adjacent_debt_cap_cast_le (M : ℕ) :
    (adjacentDebtCap M : ℝ) ≤
      (2 / 500 + 696 / 2375 + 1 / 250 : ℝ) * (M : ℝ) := by
  have htail := lower_debt_cap_cast_le M
  have hcrossover := crossover_exact_cap_cast_le M
  have hminority := minority_exact_cap_cast_le M
  simp only [adjacentDebtCap, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  nlinarith

/-! ## Explicit finite numerical slack -/

/-- Exact coefficient check.  The lower and adjacent second-alternative
branches have the same residual slack `421 / 4750000`; the first branch has
strictly more. -/
theorem finite_floor_ceiling_slack :
    (687 / 10000 : ℝ) +
          (191 / 10000 : ℝ) * (13 / 25 : ℝ) +
          (421 / 4750000 : ℝ) ≤
        (5697 / 10000 : ℝ) * (6 / 25 : ℝ) ∧
      (687 / 10000 : ℝ) +
          (1 / 500 : ℝ) * (13 / 25 : ℝ) +
          (421 / 4750000 : ℝ) =
        ((696 / 2375 : ℝ) - 21 / 10000) * (6 / 25 : ℝ) ∧
      (687 / 10000 : ℝ) +
          (2 / 500 + 696 / 2375 + 1 / 250 : ℝ) *
            (13 / 25 : ℝ) +
          (421 / 4750000 : ℝ) =
        (9389 / 10000 : ℝ) * (6 / 25 : ℝ) := by
  norm_num

private theorem population_at_least_slack_threshold
    (hn : TimeTheorem.timePopulationThreshold ≤ n) :
    11283 ≤ n := by
  exact (by norm_num : 11283 ≤ 2 ^ 24).trans
    (PhaseZeroEntry.phase_zero_population_lower hn)

private theorem one_le_common_slack
    (hn : 11283 ≤ n) :
    (1 : ℝ) ≤ (421 / 4750000 : ℝ) * (n : ℝ) := by
  have hbase :
      (1 : ℝ) ≤ (421 / 4750000 : ℝ) * (11283 : ℝ) := by
    norm_num
  have hcast : (11283 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hn
  exact hbase.trans
    (mul_le_mul_of_nonneg_left hcast (by norm_num))

/-- The natural ceiling defining `fuelFloor` loses less than one unit. -/
theorem fuel_floor_cast_le (n : ℕ) :
    (LatePotential.fuelFloor n : ℝ) ≤
      (687 / 10000 : ℝ) * (n : ℝ) + 1 := by
  unfold LatePotential.fuelFloor
  exact (Nat.ceil_lt_add_one (by positivity)).le

private theorem strong_main_upper_real
    {n M C R : ℕ} (h : StrongSeedDensity n M C R) :
    (M : ℝ) ≤ (13 / 25 : ℝ) * (n : ℝ) := by
  have hcast : (25 : ℝ) * (M : ℝ) ≤ (13 : ℝ) * (n : ℝ) := by
    exact_mod_cast h.mains_upper
  nlinarith

private theorem strong_reserve_lower_real
    {n M C R : ℕ} (h : StrongSeedDensity n M C R) :
    (6 / 25 : ℝ) * (n : ℝ) ≤ (R : ℝ) := by
  have hcast : (6 : ℝ) * (n : ℝ) ≤ (25 : ℝ) * (R : ℝ) := by
    exact_mod_cast h.reserves_lower
  nlinarith

private theorem first_union_sample_real
    {R S : ℕ} (h : 5697 * R ≤ 10000 * S) :
    (5697 / 10000 : ℝ) * (R : ℝ) ≤ (S : ℝ) := by
  have hcast : (5697 : ℝ) * (R : ℝ) ≤ (10000 : ℝ) * (S : ℝ) := by
    exact_mod_cast h
  nlinarith

private theorem second_union_sample_real
    {R S : ℕ} (h : 9389 * R ≤ 10000 * S) :
    (9389 / 10000 : ℝ) * (R : ℝ) ≤ (S : ℝ) := by
  have hcast : (9389 : ℝ) * (R : ℝ) ≤ (10000 : ℝ) * (S : ℝ) := by
    exact_mod_cast h
  nlinarith

private theorem exact_sample_real_of_scaled
    {M A R S : ℕ} (hM : 0 < M)
    (h : 10000 * A * R ≤ 10000 * M * S + 21 * M * R) :
    ((A : ℝ) / (M : ℝ) - 21 / 10000) * (R : ℝ) ≤ (S : ℝ) := by
  have hMreal : 0 < (M : ℝ) := by
    exact_mod_cast hM
  have hcast :
      (10000 : ℝ) * (A : ℝ) * (R : ℝ) ≤
        (10000 : ℝ) * (M : ℝ) * (S : ℝ) +
          (21 : ℝ) * (M : ℝ) * (R : ℝ) := by
    exact_mod_cast h
  have heq :
      ((A : ℝ) / (M : ℝ) - 21 / 10000) * (R : ℝ) =
        (((A : ℝ) * (R : ℝ) -
            (21 / 10000 : ℝ) * (M : ℝ) * (R : ℝ)) /
          (M : ℝ)) := by
    field_simp [ne_of_gt hMreal]
    <;> ring
  rw [heq, div_le_iff₀ hMreal]
  nlinarith

/-! ## Matching sample floors -/

/-- First alternative: the `.5697 R` adjacent-union floor pays
`fuelFloor n + floor(.0191 M)`. -/
theorem first_alternative_sample_cap
    {n M C R S : ℕ}
    (hn : TimeTheorem.timePopulationThreshold ≤ n)
    (hdensity : StrongSeedDensity n M C R)
    (hsample : 5697 * R ≤ 10000 * S) :
    LatePotential.fuelFloor n + firstDebtCap M ≤ S := by
  have hnlarge := population_at_least_slack_threshold hn
  have hmain := strong_main_upper_real hdensity
  have hreserve := strong_reserve_lower_real hdensity
  have hceil := fuel_floor_cast_le n
  have hcap := first_debt_cap_cast_le M
  have hone := one_le_common_slack hnlarge
  have hsampleReal := first_union_sample_real hsample
  have hcoef := mul_le_mul_of_nonneg_right
    finite_floor_ceiling_slack.1 (by positivity : 0 ≤ (n : ℝ))
  have hreal :
      ((LatePotential.fuelFloor n + firstDebtCap M : ℕ) : ℝ) ≤
        (S : ℝ) := by
    clear hn
    push_cast
    nlinarith
  exact_mod_cast hreal

/-- Second alternative above the crossover: the exact lower-class sample floor
pays `fuelFloor n + floor(.002 M)`. -/
theorem second_alternative_lower_sample_cap
    {n M C R A S : ℕ}
    (hn : TimeTheorem.timePopulationThreshold ≤ n)
    (hdensity : StrongSeedDensity n M C R)
    (hthreshold : 696 * M ≤ 2375 * A)
    (hsample : 10000 * A * R ≤ 10000 * M * S + 21 * M * R) :
    LatePotential.fuelFloor n + lowerDebtCap M ≤ S := by
  have hnlarge := population_at_least_slack_threshold hn
  have hnpos : 0 < n := by omega
  have hMpos : 0 < M := by
    have hmainLower := hdensity.mains_lower
    omega
  have hMreal : 0 < (M : ℝ) := by
    exact_mod_cast hMpos
  have hthresholdReal :
      (696 : ℝ) * (M : ℝ) ≤ (2375 : ℝ) * (A : ℝ) := by
    exact_mod_cast hthreshold
  have hratio :
      (696 / 2375 : ℝ) ≤ (A : ℝ) / (M : ℝ) := by
    apply (le_div_iff₀ hMreal).2
    nlinarith
  have hsampleReal := exact_sample_real_of_scaled hMpos hsample
  have hsampleBase :
      ((696 / 2375 : ℝ) - 21 / 10000) * (R : ℝ) ≤
        (S : ℝ) := by
    have hsub := sub_le_sub_right hratio (21 / 10000 : ℝ)
    have hmul := mul_le_mul_of_nonneg_right hsub
      (by positivity : 0 ≤ (R : ℝ))
    exact hmul.trans hsampleReal
  have hmain := strong_main_upper_real hdensity
  have hreserve := strong_reserve_lower_real hdensity
  have hceil := fuel_floor_cast_le n
  have hcap := lower_debt_cap_cast_le M
  have hone := one_le_common_slack hnlarge
  have hcoef := congrArg (fun x : ℝ => x * (n : ℝ))
    finite_floor_ceiling_slack.2.1
  have hreal :
      ((LatePotential.fuelFloor n + lowerDebtCap M : ℕ) : ℝ) ≤
        (S : ℝ) := by
    clear hn
    push_cast
    nlinarith
  exact_mod_cast hreal

/-- Second alternative below the crossover: the `.9389 R` adjacent-union floor
pays the thresholded adjacent cap. -/
theorem second_alternative_adjacent_sample_cap
    {n M C R S : ℕ}
    (hn : TimeTheorem.timePopulationThreshold ≤ n)
    (hdensity : StrongSeedDensity n M C R)
    (hsample : 9389 * R ≤ 10000 * S) :
    LatePotential.fuelFloor n + adjacentDebtCap M ≤ S := by
  have hnlarge := population_at_least_slack_threshold hn
  have hmain := strong_main_upper_real hdensity
  have hreserve := strong_reserve_lower_real hdensity
  have hceil := fuel_floor_cast_le n
  have hcap := adjacent_debt_cap_cast_le M
  have hone := one_le_common_slack hnlarge
  have hsampleReal := second_union_sample_real hsample
  have hcoef := congrArg (fun x : ℝ => x * (n : ℝ))
    finite_floor_ceiling_slack.2.2
  have hreal :
      ((LatePotential.fuelFloor n + adjacentDebtCap M : ℕ) : ℝ) ≤
        (S : ℝ) := by
    clear hn
    push_cast
    nlinarith
  exact_mod_cast hreal

/-! ## Branch-specific debt caps -/

/-- Lower target debt is paid by `floor(.002 M)`. -/
theorem lower_debt_le_lower_cap
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (M : ℕ) (c : InputCfg n)
    (htail :
      500 * Lemma615MassAbove.massAboveScaled
        (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256) ell.val c ≤ M) :
    Phase6FuelLedger.splitDebt
        (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256) ell c ≤
      lowerDebtCap M := by
  exact (Phase6FuelEntry.splitDebt_le_massAboveScaled
    (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256) ell c).trans
    (upper_tail_le_lower_cap htail)

/-- First alternative debt is paid by the single cap `floor(.0191 M)`. -/
theorem first_alternative_union_debt_cap
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (σ : Sign) (M : ℕ) (c : InputCfg n)
    (htail :
      500 * Lemma615MassAbove.massAboveScaled
        (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256) ell.val c ≤ M)
    (hminority : 250 * minorityExact ell σ c ≤ M)
    (hmajority : 10000 * majorityExact ell σ c ≤ 111 * M) :
    Phase6FuelLedger.unionSplitDebt
        (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256) ell c ≤
      firstDebtCap M := by
  have hsharp := union_split_debt_le_two_tail_add_level
    (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256) ell c
  have hlevel := main_at_level_eq_exact_classes ell σ c
  rw [hlevel] at hsharp
  have htailCap := upper_tail_le_lower_cap htail
  have hmajorityCap := majority_exact_le_first_floor hmajority
  have hminorityCap := minority_exact_level_cap hminority
  have hcomponents := first_debt_components_le_first_cap M
  omega

/-- Below the crossover, adjacent debt is paid by
`2 floor(.002 M) + floor((696/2375) M) + floor(.004 M)`. -/
theorem second_alternative_union_debt_cap
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (σ : Sign) (M : ℕ) (c : InputCfg n)
    (htail :
      500 * Lemma615MassAbove.massAboveScaled
        (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256) ell.val c ≤ M)
    (hminority : 250 * minorityExact ell σ c ≤ M)
    (hbelow : ¬ 696 * M ≤ 2375 * majorityExact ell σ c) :
    Phase6FuelLedger.unionSplitDebt
        (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256) ell c ≤
      adjacentDebtCap M := by
  have hsharp := union_split_debt_le_two_tail_add_level
    (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256) ell c
  have hlevel := main_at_level_eq_exact_classes ell σ c
  rw [hlevel] at hsharp
  have htailCap := upper_tail_le_lower_cap htail
  have hmajorityCap := majority_exact_le_crossover_floor hbelow
  have hminorityCap := minority_exact_level_cap hminority
  unfold adjacentDebtCap
  omega

/-! ## Corrected certificate and ledger producer -/

/-- Select the corrected branch at the completed snapshot and construct the
literal corrected entry-fuel certificate. -/
theorem corrected_entry_fuel_certificate_of_completed_snapshot
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (σ : Sign) (M C R : ℕ) (c : InputCfg n)
    (hn : TimeTheorem.timePopulationThreshold ≤ n)
    (hdensity : StrongSeedDensity n M C R)
    (hsnapshot : CompletedRowTwoFuelSnapshot ell σ M R c) :
    CorrectedEntryFuelCertificate
      (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
      ell (LatePotential.fuelFloor n) c := by
  cases hsnapshot.outcome with
  | first hmajority hsample =>
      refine ⟨.adjacent,
        LatePotential.fuelFloor n + firstDebtCap M, ?_, ?_⟩
      · exact
          { debt_cap := by
              have hdebt := first_alternative_union_debt_cap
                ell σ M c hsnapshot.upper_tail_scaled
                hsnapshot.minority_scaled hmajority
              omega }
      · exact
          { sample_cap :=
              first_alternative_sample_cap hn hdensity hsample }
  | second hexact hunion =>
      by_cases hcross :
          696 * M ≤ 2375 * majorityExact ell σ c
      · refine ⟨.lower,
          LatePotential.fuelFloor n + lowerDebtCap M, ?_, ?_⟩
        · exact
            { debt_cap := by
                have hdebt := lower_debt_le_lower_cap
                  ell M c hsnapshot.upper_tail_scaled
                omega }
        · exact
            { sample_cap :=
                second_alternative_lower_sample_cap
                  hn hdensity hcross hexact }
      · refine ⟨.adjacent,
          LatePotential.fuelFloor n + adjacentDebtCap M, ?_, ?_⟩
        · exact
            { debt_cap := by
                have hdebt := second_alternative_union_debt_cap
                  ell σ M c hsnapshot.upper_tail_scaled
                  hsnapshot.minority_scaled hcross
                omega }
        · exact
            { sample_cap :=
                second_alternative_adjacent_sample_cap
                  hn hdensity hunion }

/-- Final deterministic consumer: the completed snapshot enters Phase 6 with
one of the two persistent ledgers. -/
theorem two_level_fuel_ledger_of_completed_snapshot
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (σ : Sign) (M C R : ℕ) (c : InputCfg n)
    (hn : TimeTheorem.timePopulationThreshold ≤ n)
    (hdensity : StrongSeedDensity n M C R)
    (hsnapshot : CompletedRowTwoFuelSnapshot ell σ M R c) :
    Phase6FuelLedger.TwoLevelFuelLedger
      (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
      ell (LatePotential.fuelFloor n) c := by
  exact LateSamplingFuelFeasibilityAudit.twoLevelFuelLedger_of_corrected_pair
    (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
    ell (LatePotential.fuelFloor n) c
    (corrected_entry_fuel_certificate_of_completed_snapshot
      ell σ M C R c hn hdensity hsnapshot)

/-!
THEOREM LIST
* `majorityExact`, `minorityExact`
* `lowerDebtCap`, `minorityExactCap`, `crossoverExactCap`
* `firstDebtCap`, `adjacentDebtCap`
* `RowTwoFuelOutcome`
* `CompletedRowTwoFuelSnapshot`
* `union_agent_debt_add_level_le_next_mass`
* `union_agent_debt_le_two_tail_add_level`
* `union_split_debt_le_two_tail_add_level`
* `main_at_level_eq_exact_classes`
* `minority_exact_level_cap`
* `first_debt_components_le_first_cap`
* `finite_floor_ceiling_slack`
* `fuel_floor_cast_le`
* `first_alternative_sample_cap`
* `second_alternative_lower_sample_cap`
* `second_alternative_adjacent_sample_cap`
* `lower_debt_le_lower_cap`
* `first_alternative_union_debt_cap`
* `second_alternative_union_debt_cap`
* `corrected_entry_fuel_certificate_of_completed_snapshot`
* `two_level_fuel_ledger_of_completed_snapshot`

CLOSES
* Item 1: all three branch choices and their exact natural caps.
* Item 2: coefficient-one debt, minority floor, and matching sample floors.
* Item 3: `TwoLevelFuelLedger` via
  `twoLevelFuelLedger_of_corrected_pair`.
* Item 4: exact finite floor/ceiling slack, including the shared
  `421 / 4750000` residual and the sufficient threshold `11283 ≤ n`.

UNFINISHED
* The probabilistic row-two item must instantiate
  `CompletedRowTwoFuelSnapshot` at the actual completed configuration.  Its
  fields are precisely the scaled inequalities already identified above; no
  future-success or ledger hypothesis is hidden in the record.
* The strong-seed interface used here is `LateSamplingStrongSeedReceipt.lean`.
* Replacing the old fields of `LateSamplingRowTwoConsumer.CompletionProducer`
  is a downstream wiring change and is intentionally absent from this file.
END
-/

end Ripple.PopulationProtocol.ExactMajority.LateSamplingCorrectedFuelProducer

end
