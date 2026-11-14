-- Ripple/PopulationProtocol/ExactMajority/Probability/AveragingTerminalDebt.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingDebtService
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingTerminalReadout

/-!
# The terminal X/Y debts and their deterministic service floors

X uses the strict hour cutoff k, Y the cutoff k+1. Both retain the pending
Main charge and twice the scaled mixed minority mass. The difference Y-X is
exactly the active exact-hour-k zero count.
-/

noncomputable section

namespace Ripple.PopulationProtocol.ExactMajority.AveragingTerminalDebt

open TimeTheorem P3DeterministicAlgebra AveragingMixedAlgebra AveragingMixedLedgers
open AveragingPendingCredit AveragingCreditTransitions
open AveragingDebtAlgebra AveragingDebtTransitions AveragingDebtService

variable {L K : ℕ}

def minorityMass : Sign → Cfg L K → ℚ
  | .pos, c => mixedNegativeMass c
  | .neg, c => mixedPositiveMass c

def positiveCoefficient : Sign → ℕ → ℚ
  | .pos, _ => 0
  | .neg, k => (2 : ℚ) ^ (k + 1)

def negativeCoefficient : Sign → ℕ → ℚ
  | .pos, k => (2 : ℚ) ^ (k + 1)
  | .neg, _ => 0

def minorityDebt (σ : Sign) (k : ℕ) (c : Cfg L K) : ℚ :=
  (2 : ℚ) ^ k * minorityMass σ c

def debtX (σ : Sign) (k : ℕ) (c : Cfg L K) : ℚ :=
  totalDebt (positiveCoefficient σ k) (negativeCoefficient σ k) k c

def debtY (σ : Sign) (k : ℕ) (c : Cfg L K) : ℚ :=
  totalDebt (positiveCoefficient σ k) (negativeCoefficient σ k) (k + 1) c

def exactZeroWeight (k : ℕ) (s : AgentState L K) : ℕ :=
  if s.role = .main ∧ ¬ s.phase.val < 3 ∧ s.bias = .zero ∧ s.hour.val = k then 1 else 0

def exactZeroCount (k : ℕ) (c : Cfg L K) : ℕ :=
  (c.map (exactZeroWeight k)).sum

theorem coefficients_nonneg (σ : Sign) (k : ℕ) :
    0 ≤ positiveCoefficient σ k ∧ 0 ≤ negativeCoefficient σ k := by
  cases σ <;> simp [positiveCoefficient, negativeCoefficient] <;> positivity

theorem coefficients_sum (σ : Sign) (k : ℕ) :
    positiveCoefficient σ k + negativeCoefficient σ k = (2 : ℚ) ^ (k + 1) := by
  cases σ <;> simp [positiveCoefficient, negativeCoefficient]

theorem massBlend_coefficients (σ : Sign) (k : ℕ) (x : ℚ) :
    massBlend (positiveCoefficient σ k) (negativeCoefficient σ k) x =
      (2 : ℚ) ^ (k + 1) * minorityPart σ x := by
  cases σ <;> simp [massBlend, positiveCoefficient, negativeCoefficient, minorityPart]

theorem minorityMass_nonneg (σ : Sign) (c : Cfg L K) :
    0 ≤ minorityMass σ c := by
  cases σ <;> simp only [minorityMass, mixedPositiveMass, mixedNegativeMass] <;>
    apply Multiset.sum_nonneg <;> intro x hx <;>
    obtain ⟨a, _, rfl⟩ := Multiset.mem_map.mp hx <;> exact le_max_right _ _

theorem debtX_eq (σ : Sign) (k : ℕ) (c : Cfg L K) :
    debtX σ k c = (inactiveMainCount c : ℚ) + (lowHourZeroCount k c : ℚ) +
      2 * minorityDebt σ k c := by
  rw [debtX, totalDebt_eq_counts_and_masses]
  cases σ <;> simp [positiveCoefficient, negativeCoefficient, minorityDebt,
    minorityMass, pow_succ] <;> ring

theorem debtY_eq (σ : Sign) (k : ℕ) (c : Cfg L K) :
    debtY σ k c = (inactiveMainCount c : ℚ) + (lowHourZeroCount (k + 1) c : ℚ) +
      2 * minorityDebt σ k c := by
  rw [debtY, totalDebt_eq_counts_and_masses]
  cases σ <;> simp [positiveCoefficient, negativeCoefficient, minorityDebt,
    minorityMass, pow_succ] <;> ring

theorem lowHourZeroWeight_succ (k : ℕ) (s : AgentState L K) :
    lowHourZeroWeight (k + 1) s = lowHourZeroWeight k s + exactZeroWeight k s := by
  by_cases hm : s.role = .main
  · by_cases hp : s.phase.val < 3
    · simp [lowHourZeroWeight, exactZeroWeight, hm, hp]
    · by_cases hb : s.bias = .zero
      · by_cases hk : s.hour.val < k
        · have hks : s.hour.val < k + 1 := by omega
          have hne : s.hour.val ≠ k := by omega
          simp [lowHourZeroWeight, exactZeroWeight, hm, hp, hb, hk, hks, hne]
        · by_cases he : s.hour.val = k
          · simp [lowHourZeroWeight, exactZeroWeight, hm, hp, hb, hk, he]
          · have hks : ¬ s.hour.val < k + 1 := by omega
            simp [lowHourZeroWeight, exactZeroWeight, hm, hp, hb, hk, hks, he]
      · simp [lowHourZeroWeight, exactZeroWeight, hm, hp, hb]
  · simp [lowHourZeroWeight, exactZeroWeight, hm]

theorem lowHourZeroCount_succ (k : ℕ) (c : Cfg L K) :
    lowHourZeroCount (k + 1) c = lowHourZeroCount k c + exactZeroCount k c := by
  induction c using Multiset.induction_on with
  | empty => simp [lowHourZeroCount, exactZeroCount]
  | cons s c ih =>
      simp only [lowHourZeroCount, exactZeroCount, Multiset.map_cons, Multiset.sum_cons] at ih ⊢
      rw [lowHourZeroWeight_succ]
      omega

theorem debtY_sub_debtX (σ : Sign) (k : ℕ) (c : Cfg L K) :
    debtY σ k c - debtX σ k c = (exactZeroCount k c : ℚ) := by
  rw [debtX_eq, debtY_eq, lowHourZeroCount_succ, Nat.cast_add]
  ring

theorem clock_targets_le_mainCount (k : ℕ) (c : Cfg L K) :
    inactiveMainCount c + lowHourZeroCount k c ≤ RoleSplitConcentration.mainCount c := by
  induction c using Multiset.induction_on with
  | empty => simp [inactiveMainCount, lowHourZeroCount, RoleSplitConcentration.mainCount]
  | cons s c ih =>
      have hs : inactiveMainWeight s + lowHourZeroWeight k s ≤
          if s.role = .main then 1 else 0 := by
        by_cases hm : s.role = .main <;> by_cases hp : s.phase.val < 3 <;>
          simp [inactiveMainWeight, lowHourZeroWeight, hm, hp] <;>
          split_ifs <;> omega
      simp only [inactiveMainCount, lowHourZeroCount, Multiset.map_cons,
        Multiset.sum_cons] at ih ⊢
      simp only [RoleSplitConcentration.mainCount, Multiset.countP_cons] at ih ⊢
      by_cases hm : s.role = .main <;> simp only [hm, if_true, if_false] at hs ⊢ <;> omega

/-- No loss is rounded here: the integer number of service targets dominates
the positive excess over twice the observed minority debt. -/
theorem debtX_service_floor (σ : Sign) (k : ℕ) (c : Cfg L K) (Dstar : ℚ)
    (hD : minorityDebt σ k c ≤ Dstar) :
    max (debtX σ k c - 2 * Dstar) 0 ≤
      (inactiveMainCount c + lowHourZeroCount k c : ℕ) := by
  rw [debtX_eq]
  apply max_le
  · push_cast
    linarith
  · positivity

theorem debtY_service_floor (σ : Sign) (k : ℕ) (c : Cfg L K) (xstar : ℚ)
    (hX : debtX σ k c ≤ xstar) :
    max (debtY σ k c - xstar) 0 ≤ (exactZeroCount k c : ℚ) := by
  have he := debtY_sub_debtX σ k c
  apply max_le
  · linarith
  · positivity

theorem debtX_excess_le_mainCount (σ : Sign) (k : ℕ) (c : Cfg L K) (Dstar : ℚ)
    (hD : minorityDebt σ k c ≤ Dstar) :
    max (debtX σ k c - 2 * Dstar) 0 ≤
      (RoleSplitConcentration.mainCount c : ℚ) := by
  exact (debtX_service_floor σ k c Dstar hD).trans
    (by exact_mod_cast clock_targets_le_mainCount k c)

theorem debtX_trace_le (σ : Sign) (k : ℕ)
    (init : Cfg L 256) (ω : Ω L 256) (s t : ℕ) (hst : s ≤ t)
    (hrange : ∀ u, s ≤ u → u ≤ t → ∀ a ∈ trace init ω u,
      1 ≤ a.phase.val ∧ a.phase.val ≤ 3)
    (hsafe : ∀ u, s ≤ u → u ≤ t → ∀ a ∈ trace init ω u,
      a.smallBias.val ∈ ({2, 3, 4} : Finset ℕ))
    (hcarrier : ∀ u, s ≤ u → u ≤ t → ∀ a ∈ trace init ω u,
      a.role ≠ .main → a.smallBias.val = 3) :
    debtX σ k (trace init ω t) ≤ debtX σ k (trace init ω s) := by
  have hn := coefficients_nonneg σ k
  apply totalDebt_trace_le _ _ k hn.1 hn.2 _ init ω s t hst hrange hsafe hcarrier
  rw [coefficients_sum]
  exact pow_le_pow_right₀ (by norm_num : (1 : ℚ) ≤ 2) (Nat.le_succ k)

theorem debtY_trace_le (σ : Sign) (k : ℕ)
    (init : Cfg L 256) (ω : Ω L 256) (s t : ℕ) (hst : s ≤ t)
    (hrange : ∀ u, s ≤ u → u ≤ t → ∀ a ∈ trace init ω u,
      1 ≤ a.phase.val ∧ a.phase.val ≤ 3)
    (hsafe : ∀ u, s ≤ u → u ≤ t → ∀ a ∈ trace init ω u,
      a.smallBias.val ∈ ({2, 3, 4} : Finset ℕ))
    (hcarrier : ∀ u, s ≤ u → u ≤ t → ∀ a ∈ trace init ω u,
      a.role ≠ .main → a.smallBias.val = 3) :
    debtY σ k (trace init ω t) ≤ debtY σ k (trace init ω s) := by
  have hn := coefficients_nonneg σ k
  apply totalDebt_trace_le _ _ (k + 1) hn.1 hn.2 _ init ω s t hst hrange hsafe hcarrier
  exact le_of_eq (coefficients_sum σ k).symm

theorem minorityDebt_trace_le (σ : Sign) (k : ℕ)
    (init : Cfg L 256) (hinit : validInitial init) (ω : Ω L 256)
    (s t : ℕ) (hst : s ≤ t)
    (hrange : ∀ u, s ≤ u → u ≤ t → ∀ a ∈ trace init ω u,
      1 ≤ a.phase.val ∧ a.phase.val ≤ 3)
    (hsafe : ∀ u, s ≤ u → u ≤ t → ∀ a ∈ trace init ω u,
      a.smallBias.val ∈ ({2, 3, 4} : Finset ℕ))
    (hcarrier : ∀ u, s ≤ u → u ≤ t → ∀ a ∈ trace init ω u,
      a.role ≠ .main → a.smallBias.val = 3) :
    minorityDebt σ k (trace init ω t) ≤ minorityDebt σ k (trace init ω s) := by
  have hsides := trace_mixedSides_le init hinit ω s t hst hrange hsafe hcarrier
  apply mul_le_mul_of_nonneg_left _ (by positivity : (0 : ℚ) ≤ (2 : ℚ) ^ k)
  cases σ
  · exact hsides.2
  · exact hsides.1

end Ripple.PopulationProtocol.ExactMajority.AveragingTerminalDebt

end
