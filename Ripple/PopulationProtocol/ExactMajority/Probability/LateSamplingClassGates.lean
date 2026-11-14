-- Ripple/PopulationProtocol/ExactMajority/Probability/LateSamplingClassGates.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.LateF6HazardBounds

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Ripple.PopulationProtocol.ExactMajority.LateSamplingClassGates

open TimeTheorem PairLog PairLogAuxiliary LateF6Acceptance LateF6Hazards

variable {L K n : ℕ}

def frozenClassCount (C : Bias L → Prop) (f : Fin n → AgentState L K) : ℕ :=
  (pool f (fun a => FrozenMain a ∧ C a.bias)).card

def FrozenFloor (C : Bias L → Prop) (A M : ℕ) (γ : ℝ)
    (f : Fin n → AgentState L K) : Prop :=
  ((A : ℝ) / M - γ) * frozenCount f ≤ frozenClassCount C f

theorem frozen_class_partition (C : Bias L → Prop)
    (f : Fin n → AgentState L K) :
    frozenClassCount C f + frozenBadCount C f = frozenCount f := by
  exact pool_partition f FrozenMain (fun a => C a.bias)

theorem class_le_main (C : Bias L → Prop) (f : Fin n → AgentState L K) :
    classCount C f ≤ mainCount f :=
  pool_mono f (MainClass C) Main (fun _ h => h.1)

theorem frozen_le_main (f : Fin n → AgentState L K) :
    frozenCount f ≤ mainCount f :=
  pool_mono f FrozenMain Main (fun _ h => h.1)

theorem frozen_floor_iff_bad (C : Bias L → Prop)
    (f : Fin n → AgentState L K) {A M : ℕ}
    (hM : 0 < M) (hA : A ≤ M) (γ : ℝ) :
    FrozenFloor C A M γ f ↔
      (frozenBadCount C f : ℝ) ≤
        (((M - A : ℕ) : ℝ) / M + γ) * frozenCount f := by
  have hp : (frozenClassCount C f : ℝ) + frozenBadCount C f = frozenCount f := by
    exact_mod_cast frozen_class_partition C f
  have hMne : (M : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hM)
  have hratio : (((M - A : ℕ) : ℝ) / M) = 1 - (A : ℝ) / M := by
    rw [Nat.cast_sub hA, sub_div, div_self hMne]
  rw [hratio]
  unfold FrozenFloor
  constructor <;> intro h <;> nlinarith

theorem frozen_floor_at_all (C : Bias L → Prop)
    (f : Fin n → AgentState L K) {A M : ℕ}
    (hM : 0 < M) (hmains : mainCount f = M) (hfrozen : frozenCount f = M)
    (hclass : A ≤ classCount C f) {γ : ℝ} (hγ : 0 ≤ γ) :
    FrozenFloor C A M γ f := by
  have hA : A ≤ M := hclass.trans ((class_le_main C f).trans_eq hmains)
  apply (frozen_floor_iff_bad C f hM hA γ).mpr
  have hb : frozenBadCount C f ≤ M - A := by
    simpa only [hmains] using frozenBad_bound C f A hclass
  have hb' : (frozenBadCount C f : ℝ) ≤ (M - A : ℕ) := by exact_mod_cast hb
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  rw [hfrozen, add_mul, div_mul_cancel₀ _ (ne_of_gt hMpos)]
  exact hb'.trans (le_add_of_nonneg_right (mul_nonneg hγ hMpos.le))

theorem freeze_bad_ratio_eq (C : Bias L → Prop)
    (f : Fin n → AgentState L K) {A M : ℕ}
    (hmains : mainCount f = M) (hclass : A ≤ classCount C f) :
    freezeBadRatio C A f =
      (((M - A : ℕ) : ℝ) - frozenBadCount C f) /
        ((M : ℝ) - frozenCount f) := by
  have hb : frozenBadCount C f ≤ M - A := by
    simpa only [hmains] using frozenBad_bound C f A hclass
  have hk : frozenCount f ≤ M := (frozen_le_main f).trans_eq hmains
  unfold freezeBadRatio
  rw [hmains, Nat.cast_sub hb, Nat.cast_sub hk]

end Ripple.PopulationProtocol.ExactMajority.LateSamplingClassGates

end
