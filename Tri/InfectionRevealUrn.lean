/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.InfectionRevealPrefix
import Tri.Lemma14Leaf
import Tri.Emulation

/-!
# Exact urn projection of inactive identity reveals

Uniformly revealing and removing one inactive identity projects exactly to
the remaining-count urn kernel used by the without-replacement tail bound.
The construction is totalized by a self-loop on the empty inactive view.
-/

namespace Tri

open scoped ENNReal

/-- Remaining immutable `X` and `Y` identity counts. -/
def infectionInactiveCounts {n : ℕ}
    (v : InfectionInactiveView n) : ℕ × ℕ :=
  (v.xIds.card, v.yIds.card)

/-- Boolean encoding used by the existing two-colour urn kernel. -/
def infectionLabelOfBool : Bool → InfectionLabel
  | false => .Y
  | true => .X

/-- The mass of revealing an `X` is its fraction of the inactive pool. -/
theorem infectionRevealOneLabelPMF_X
    {n : ℕ} (v : InfectionInactiveView n)
    (h : Nonempty (InfectionInactiveId v)) :
    infectionRevealOneLabelPMF v h .X =
      (v.xIds.card : ℝ≥0∞) / (v.ids.card : ℝ≥0∞) := by
  rw [infectionRevealOneLabelPMF, PMF.map_apply, tsum_fintype]
  simp_rw [infectionRevealOneLabel, infectionRevealOnePMF_apply]
  rw [← Finset.sum_filter]
  rw [Finset.sum_const, nsmul_eq_mul]
  have hcard :
      ((Finset.univ : Finset (InfectionInactiveId v)).filter fun i =>
        InfectionLabel.X = v.initialLabel i.1).card =
        v.xIds.card := by
    rw [Finset.univ_eq_attach]
    rw [Finset.filter_attach
      (fun j : Fin n => InfectionLabel.X = v.initialLabel j) v.ids]
    rw [Finset.card_map, Finset.card_attach]
    simp [InfectionInactiveView.xIds, eq_comm]
  rw [hcard]
  simp [div_eq_mul_inv]

/-- The mass of revealing a `Y` is its fraction of the inactive pool. -/
theorem infectionRevealOneLabelPMF_Y
    {n : ℕ} (v : InfectionInactiveView n)
    (h : Nonempty (InfectionInactiveId v)) :
    infectionRevealOneLabelPMF v h .Y =
      (v.yIds.card : ℝ≥0∞) / (v.ids.card : ℝ≥0∞) := by
  rw [infectionRevealOneLabelPMF, PMF.map_apply, tsum_fintype]
  simp_rw [infectionRevealOneLabel, infectionRevealOnePMF_apply]
  rw [← Finset.sum_filter]
  rw [Finset.sum_const, nsmul_eq_mul]
  have hcard :
      ((Finset.univ : Finset (InfectionInactiveId v)).filter fun i =>
        InfectionLabel.Y = v.initialLabel i.1).card =
        v.yIds.card := by
    rw [Finset.univ_eq_attach]
    rw [Finset.filter_attach
      (fun j : Fin n => InfectionLabel.Y = v.initialLabel j) v.ids]
    rw [Finset.card_map, Finset.card_attach]
    simp [InfectionInactiveView.yIds, eq_comm]
  rw [hcard]
  simp [div_eq_mul_inv]

/-- One revealed label has exactly the direction law of the count urn. -/
theorem infectionRevealOneLabelPMF_eq_productiveDirection
    {n : ℕ} (v : InfectionInactiveView n)
    (h : Nonempty (InfectionInactiveId v))
    (hpos : 0 < v.xIds.card + v.yIds.card) :
    infectionRevealOneLabelPMF v h =
      (productiveDirectionPMF v.xIds.card v.yIds.card hpos).map
        infectionLabelOfBool := by
  have hden :
      (v.ids.card : ℝ≥0∞) =
        (v.xIds.card : ℝ≥0∞) + (v.yIds.card : ℝ≥0∞) := by
    rw [← Nat.cast_add, InfectionInactiveView.xIds_card_add_yIds_card]
  ext ell
  cases ell <;>
    rw [PMF.map_apply, tsum_fintype] <;>
    simp [infectionLabelOfBool, infectionRevealOneLabelPMF_X,
      infectionRevealOneLabelPMF_Y, productiveDirectionPMF_false,
      productiveDirectionPMF_true, hden]

/-- Reveal one uniformly chosen inactive identity and remove it from the
remaining view; the empty view is absorbing. -/
noncomputable def infectionRevealKernel {n : ℕ}
    (v : InfectionInactiveView n) : PMF (InfectionInactiveView n) :=
  if h : 0 < v.ids.card then
    (infectionRevealOnePMF v
      (infectionRevealOne_nonempty_of_card_pos v h)).map v.erase
  else
    PMF.pure v

/-- The identity-level reveal kernel projects exactly to the stopped
remaining-count urn chain. -/
theorem infectionRevealKernel_intertwines_urnChain (n : ℕ) :
    Intertwines (@infectionInactiveCounts n)
      (@infectionRevealKernel n) urnChain := by
  intro v
  unfold infectionRevealKernel
  by_cases hv : 0 < v.ids.card
  · rw [dif_pos hv, PMF.map_comp]
    let hne := infectionRevealOne_nonempty_of_card_pos v hv
    have hpos : 0 < v.xIds.card + v.yIds.card := by
      rw [InfectionInactiveView.xIds_card_add_yIds_card]
      exact hv
    let countNext : InfectionLabel → ℕ × ℕ
      | .X => (v.xIds.card - 1, v.yIds.card)
      | .Y => (v.xIds.card, v.yIds.card - 1)
    have hcounts :
        ∀ i : InfectionInactiveId v,
          infectionInactiveCounts (v.erase i) =
            countNext (infectionRevealOneLabel v i) := by
      intro i
      cases hlabel : v.initialLabel i.1 with
      | X =>
          have hiX : i.1 ∈ v.xIds := by
            simp [InfectionInactiveView.xIds, i.2, hlabel]
          have hiY : i.1 ∉ v.yIds := by
            simp [InfectionInactiveView.yIds, hlabel]
          simp [infectionInactiveCounts, countNext,
            infectionRevealOneLabel, hlabel,
            InfectionInactiveView.erase_xIds,
            InfectionInactiveView.erase_yIds,
            Finset.card_erase_of_mem hiX,
            Finset.erase_eq_of_notMem hiY]
      | Y =>
          have hiX : i.1 ∉ v.xIds := by
            simp [InfectionInactiveView.xIds, hlabel]
          have hiY : i.1 ∈ v.yIds := by
            simp [InfectionInactiveView.yIds, i.2, hlabel]
          simp [infectionInactiveCounts, countNext,
            infectionRevealOneLabel, hlabel,
            InfectionInactiveView.erase_xIds,
            InfectionInactiveView.erase_yIds,
            Finset.erase_eq_of_notMem hiX,
            Finset.card_erase_of_mem hiY]
    calc
      (infectionRevealOnePMF v hne).map
          (infectionInactiveCounts ∘ InfectionInactiveView.erase v) =
          (infectionRevealOnePMF v hne).map
            (countNext ∘ infectionRevealOneLabel v) := by
            congr 1
            funext i
            exact hcounts i
      _ = (infectionRevealOneLabelPMF v hne).map countNext := by
            unfold infectionRevealOneLabelPMF
            rw [PMF.map_comp]
      _ = ((productiveDirectionPMF
              v.xIds.card v.yIds.card hpos).map
              infectionLabelOfBool).map countNext := by
            rw [infectionRevealOneLabelPMF_eq_productiveDirection
              v hne hpos]
      _ = (productiveDirectionPMF
              v.xIds.card v.yIds.card hpos).map
            (fun red =>
              if red then
                (v.xIds.card - 1, v.yIds.card)
              else
                (v.xIds.card, v.yIds.card - 1)) := by
            rw [PMF.map_comp]
            congr 1
            funext red
            cases red <;>
              rfl
      _ = urnChain (infectionInactiveCounts v) := by
            unfold urnChain infectionInactiveCounts
            rw [dif_pos hpos]
  · have hcard : v.ids.card = 0 := by omega
    have hxy := InfectionInactiveView.xIds_card_add_yIds_card v
    have hx : v.xIds.card = 0 := by omega
    have hy : v.yIds.card = 0 := by omega
    rw [dif_neg hv, PMF.pure_map]
    simp [infectionInactiveCounts, urnChain, hx, hy]

/-- Stop identity reveals at the same one-ball floor as `urnStopped`. -/
noncomputable def infectionRevealStopped {n : ℕ} :
    InfectionInactiveView n → PMF (InfectionInactiveView n) :=
  freeze
    (fun v => (infectionInactiveCounts v).1 +
      (infectionInactiveCounts v).2 ≤ 1)
    infectionRevealKernel

/-- Freezing both kernels at the common count floor preserves the exact
projection. -/
theorem infectionRevealStopped_intertwines_urnStopped (n : ℕ) :
    Intertwines (@infectionInactiveCounts n)
      (@infectionRevealStopped n) urnStopped := by
  exact (infectionRevealKernel_intertwines_urnChain n).onFreeze
    (fun q => q.1 + q.2 ≤ 1)

/-- Every finite stopped reveal prefix has exactly the urn endpoint law. -/
theorem infectionRevealStopped_iter_map_counts
    (n T : ℕ) (v : InfectionInactiveView n) :
    (iter (@infectionRevealStopped n) T v).map
        infectionInactiveCounts =
      iter urnStopped T (infectionInactiveCounts v) :=
  iter_map_of_intertwines
    (infectionRevealStopped_intertwines_urnStopped n) T v

end Tri

#print axioms Tri.infectionRevealOneLabelPMF_X
#print axioms Tri.infectionRevealOneLabelPMF_Y
#print axioms Tri.infectionRevealOneLabelPMF_eq_productiveDirection
#print axioms Tri.infectionRevealKernel_intertwines_urnChain
#print axioms Tri.infectionRevealStopped_intertwines_urnStopped
#print axioms Tri.infectionRevealStopped_iter_map_counts
