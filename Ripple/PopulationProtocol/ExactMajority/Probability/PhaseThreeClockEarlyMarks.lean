-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockEarlyMarks.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockPredictablePairs
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockEmbeddingBridge

/-!
# Natural early marks on the recorded virtual continuation

The mark process retains a fixed physical Clock mask. An early equal-minute
drip marks the initiator; a mixed marked/unmarked Clock contact propagates
the mark even when the recipient is already high. It is an auxiliary
process on the original recorded scheduler, with no change of law.

This file proves the set/count update laws and exact original-law
conditional immigration and propagation probabilities. The upper-front
containment premise used by the count ledger is stated explicitly; the
full stopped containment/normal-front barrier and the two-period P5 moment
argument are separate work.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal BigOperators MeasureTheory ProbabilityTheory

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockEarlyMarks

open TimeTheorem PairLog PairLogAuxiliary PhaseThreeClockVirtual
  PhaseThreeClockGatedLaw PhaseThreeClockGatedLevelOne
  PhaseThreeClockEmbeddingBridge PhaseThreeClockPredictablePairs

variable {L K m : ℕ}

def sourceSet (C : Finset (Fin m)) (f : Fin m → AgentState L K) (ℓ : ℕ) :
    Finset (Fin m) :=
  C.filter (fun i => effMinute (f i) = ℓ)

def EarlyDrip (C : Finset (Fin m)) (f : Fin m → AgentState L K)
    (ℓ cutoff : ℕ) (i j : Fin m) : Prop :=
  frontCount f ℓ < cutoff ∧ ℓ < K * (L + 1) ∧
    i ∈ sourceSet C f ℓ ∧ j ∈ sourceSet C f ℓ

def Propagation (C M : Finset (Fin m)) (i j : Fin m) : Prop :=
  (i ∈ M ∧ j ∈ C \ M) ∨ (i ∈ C \ M ∧ j ∈ M)

open Classical in
def markUpdate (C : Finset (Fin m)) (f : Fin m → AgentState L K)
    (ℓ cutoff : ℕ) (M : Finset (Fin m)) (i j : Fin m) : Finset (Fin m) :=
  if EarlyDrip C f ℓ cutoff i j then insert i M
  else if Propagation C M i j then insert i (insert j M) else M

def markStep (C : Finset (Fin m)) (f : Fin m → AgentState L K)
    (ℓ cutoff : ℕ) (M : Finset (Fin m)) :
    Option (Fin m × Fin m) → Finset (Fin m)
  | none => M
  | some ij => markUpdate C f ℓ cutoff M ij.1 ij.2

theorem sourceSet_subset (C : Finset (Fin m)) (f : Fin m → AgentState L K) (ℓ : ℕ) :
    sourceSet C f ℓ ⊆ C :=
  Finset.filter_subset _ _

theorem sourceSet_subset_above (f : Fin m → AgentState L K) (ℓ : ℕ) :
    sourceSet (clockSet f) f ℓ ⊆ aboveSet f ℓ := by
  intro i hi
  simp only [sourceSet, clockSet, Finset.mem_filter, Finset.mem_univ, true_and] at hi
  simp only [aboveSet, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨hi.1, hi.2.ge⟩

theorem sourceSet_card_le_front (f : Fin m → AgentState L K) (ℓ : ℕ) :
    (sourceSet (clockSet f) f ℓ).card ≤ frontCount f ℓ :=
  Finset.card_le_card (sourceSet_subset_above f ℓ)

theorem sourceSet_eq_exactSet (f : Fin m → AgentState L K) (ℓ : ℕ) :
    sourceSet (clockSet f) f ℓ = exactSet f ℓ := by
  ext i
  simp only [sourceSet, clockSet, exactSet, Finset.mem_filter, Finset.mem_univ, true_and]

theorem marks_source_disjoint (C M : Finset (Fin m))
    (f : Fin m → AgentState L K) (ℓ : ℕ) (hM : M ⊆ aboveSet f (ℓ + 1)) :
    Disjoint M (sourceSet C f ℓ) := by
  apply Finset.disjoint_left.mpr
  intro i hi hs
  have hu := hM hi
  simp only [aboveSet, Finset.mem_filter, Finset.mem_univ, true_and] at hu
  have he := (Finset.mem_filter.mp hs).2
  omega

theorem markUpdate_mono (C M : Finset (Fin m)) (f : Fin m → AgentState L K)
    (ℓ cutoff : ℕ) (i j : Fin m) :
    M ⊆ markUpdate C f ℓ cutoff M i j := by
  classical
  unfold markUpdate
  split_ifs
  · exact Finset.subset_insert _ _
  · exact (Finset.subset_insert j M).trans (Finset.subset_insert i (insert j M))
  · exact fun _ h => h

theorem markUpdate_subset_mask (C M : Finset (Fin m)) (f : Fin m → AgentState L K)
    (ℓ cutoff : ℕ) (i j : Fin m) (hM : M ⊆ C) :
    markUpdate C f ℓ cutoff M i j ⊆ C := by
  classical
  unfold markUpdate
  split_ifs with he hp
  · exact Finset.insert_subset_iff.mpr
      ⟨sourceSet_subset C f ℓ he.2.2.1, hM⟩
  · have hi : i ∈ C := by
      rcases hp with ⟨hi, -⟩ | ⟨hi, -⟩
      · exact hM hi
      · exact (Finset.mem_sdiff.mp hi).1
    have hj : j ∈ C := by
      rcases hp with ⟨-, hj⟩ | ⟨-, hj⟩
      · exact (Finset.mem_sdiff.mp hj).1
      · exact hM hj
    exact Finset.insert_subset_iff.mpr
      ⟨hi, Finset.insert_subset_iff.mpr ⟨hj, hM⟩⟩
  · exact hM

theorem earlyDrip_not_propagation (C M : Finset (Fin m))
    (f : Fin m → AgentState L K) (ℓ cutoff : ℕ) (i j : Fin m)
    (hd : Disjoint M (sourceSet C f ℓ)) (he : EarlyDrip C f ℓ cutoff i j) :
    ¬ Propagation C M i j := by
  intro hp
  rcases hp with ⟨hi, -⟩ | ⟨-, hj⟩
  · exact Finset.disjoint_left.mp hd hi he.2.2.1
  · exact Finset.disjoint_left.mp hd hj he.2.2.2

open Classical in
theorem markUpdate_card (C M : Finset (Fin m)) (f : Fin m → AgentState L K)
    (ℓ cutoff : ℕ) (i j : Fin m)
    (hd : Disjoint M (sourceSet C f ℓ)) :
    (markUpdate C f ℓ cutoff M i j).card =
      M.card + (if EarlyDrip C f ℓ cutoff i j then 1 else 0) +
        (if Propagation C M i j then 1 else 0) := by
  by_cases he : EarlyDrip C f ℓ cutoff i j
  · have hi : i ∉ M := fun hi => Finset.disjoint_left.mp hd hi he.2.2.1
    have hp := earlyDrip_not_propagation C M f ℓ cutoff i j hd he
    simp [markUpdate, he, hp, hi]
  · by_cases hp : Propagation C M i j
    · rcases hp with ⟨hi, hj⟩ | ⟨hi, hj⟩
      · have hjn : j ∉ M := (Finset.mem_sdiff.mp hj).2
        have hp : Propagation C M i j := Or.inl ⟨hi, hj⟩
        simp [markUpdate, he, hp, hi, hjn]
      · have hin : i ∉ M := (Finset.mem_sdiff.mp hi).2
        have hp : Propagation C M i j := Or.inr ⟨hi, hj⟩
        simp [markUpdate, he, hp, hin, hj]
    · simp [markUpdate, he, hp]

theorem markUpdate_card_le_add_one (C M : Finset (Fin m))
    (f : Fin m → AgentState L K) (ℓ cutoff : ℕ) (i j : Fin m)
    (hd : Disjoint M (sourceSet C f ℓ)) :
    (markUpdate C f ℓ cutoff M i j).card ≤ M.card + 1 := by
  classical
  rw [markUpdate_card C M f ℓ cutoff i j hd]
  by_cases he : EarlyDrip C f ℓ cutoff i j
  · have hp := earlyDrip_not_propagation C M f ℓ cutoff i j hd he
    simp [he, hp]
  · by_cases hp : Propagation C M i j <;> simp [he, hp]

theorem propagation_pairSet (C M : Finset (Fin m)) :
    pairSet (Propagation C M) = (M ×ˢ (C \ M)) ∪ ((C \ M) ×ˢ M) := by
  classical
  ext ⟨i, j⟩
  simp only [pairSet, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_union, Finset.mem_product, Propagation]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    intro hij
    subst j
    rcases h with ⟨hi, hj⟩ | ⟨hi, hj⟩
    · exact (Finset.mem_sdiff.mp hj).2 hi
    · exact (Finset.mem_sdiff.mp hi).2 hj

theorem propagation_pairSet_card (C M : Finset (Fin m)) (hM : M ⊆ C) :
    (pairSet (Propagation C M)).card = 2 * M.card * (C.card - M.card) := by
  have hd : Disjoint (M ×ˢ (C \ M)) ((C \ M) ×ˢ M) := by
    apply Finset.disjoint_left.mpr
    intro ij hl hr
    exact (Finset.mem_sdiff.mp (Finset.mem_product.mp hr).1).2
      (Finset.mem_product.mp hl).1
  rw [propagation_pairSet, Finset.card_union_of_disjoint hd,
    Finset.card_product, Finset.card_product, Finset.card_sdiff_of_subset hM]
  ring

open Classical in
theorem earlyDrip_pairSet_card (C : Finset (Fin m)) (f : Fin m → AgentState L K)
    (ℓ cutoff : ℕ) :
    (pairSet (EarlyDrip C f ℓ cutoff)).card =
      if frontCount f ℓ < cutoff ∧ ℓ < K * (L + 1)
      then (sourceSet C f ℓ).card * ((sourceSet C f ℓ).card - 1) else 0 := by
  by_cases h : frontCount f ℓ < cutoff ∧ ℓ < K * (L + 1)
  · have heq : pairSet (EarlyDrip C f ℓ cutoff) = (sourceSet C f ℓ).offDiag := by
      ext ⟨i, j⟩
      simp only [pairSet, EarlyDrip, h.1, h.2, true_and, Finset.mem_filter,
        Finset.mem_univ, Finset.mem_offDiag]
      tauto
    rw [if_pos h, heq, Finset.offDiag_card, Nat.mul_sub_one]
  · have hfalse : ∀ i j, ¬ EarlyDrip C f ℓ cutoff i j :=
      fun _ _ he => h ⟨he.1, he.2.1⟩
    have heq : pairSet (EarlyDrip C f ℓ cutoff) = ∅ := by
      ext ⟨i, j⟩
      simp [pairSet, hfalse]
    rw [if_neg h, heq, Finset.card_empty]

/-- Exact finite-prefix recursion. The count is reset to zero before the
chosen seed; afterwards the recorded selected pair drives the mark update. -/
noncomputable def markedPrefix (init : Cfg L K) (C : Finset (Fin init.card))
    (ℓ cutoff s : ℕ) :
    (t : ℕ) → ((k : Finset.Iic t) → Draw L K) → Finset (Fin init.card)
  | 0, _ => ∅
  | t + 1, p =>
      if s ≤ t then
        markStep C
          (auxPrefix init virtualRule t (fun k => p ⟨k.val, Finset.mem_Iic.mpr
            (le_trans (Finset.mem_Iic.mp k.property) (Nat.le_succ t))⟩))
          ℓ cutoff
          (markedPrefix init C ℓ cutoff s t (fun k => p ⟨k.val, Finset.mem_Iic.mpr
            (le_trans (Finset.mem_Iic.mp k.property) (Nat.le_succ t))⟩))
          (selectLabels
            (prefixLabels init t (fun k => p ⟨k.val, Finset.mem_Iic.mpr
              (le_trans (Finset.mem_Iic.mp k.property) (Nat.le_succ t))⟩))
            (p ⟨t + 1, Finset.mem_Iic.mpr le_rfl⟩))
      else ∅

def markedAt (init : Cfg L K) (C : Finset (Fin init.card))
    (ℓ cutoff s : ℕ) (ω : Ω L K) (t : ℕ) : Finset (Fin init.card) :=
  markedPrefix init C ℓ cutoff s t (frestrictLe t ω)

theorem markedAt_succ (init : Cfg L K) (C : Finset (Fin init.card))
    (ℓ cutoff s : ℕ) (ω : Ω L K) (t : ℕ) :
    markedAt init C ℓ cutoff s ω (t + 1) =
      if s ≤ t then markStep C (virtualLabels init ω t) ℓ cutoff
        (markedAt init C ℓ cutoff s ω t) (drawLabels init ω (t + 1)) else ∅ := rfl

theorem markedAt_empty_before_seed (init : Cfg L K) (C : Finset (Fin init.card))
    (ℓ cutoff s : ℕ) (ω : Ω L K) (t : ℕ) (ht : t ≤ s) :
    markedAt init C ℓ cutoff s ω t = ∅ := by
  cases t with
  | zero => rfl
  | succ t => rw [markedAt_succ, if_neg (by omega : ¬ s ≤ t)]

theorem markedAt_subset_mask (init : Cfg L K) (C : Finset (Fin init.card))
    (ℓ cutoff s : ℕ) (ω : Ω L K) (t : ℕ) :
    markedAt init C ℓ cutoff s ω t ⊆ C := by
  induction t with
  | zero => exact Finset.empty_subset _
  | succ t ih =>
      rw [markedAt_succ]
      by_cases ht : s ≤ t
      · rw [if_pos ht]
        cases hd : drawLabels init ω (t + 1) with
        | none => exact ih
        | some ij => exact markUpdate_subset_mask C _ _ ℓ cutoff ij.1 ij.2 ih
      · rw [if_neg ht]
        exact Finset.empty_subset _

theorem markedAt_step_mono (init : Cfg L K) (C : Finset (Fin init.card))
    (ℓ cutoff s : ℕ) (ω : Ω L K) (t : ℕ) :
    markedAt init C ℓ cutoff s ω t ⊆ markedAt init C ℓ cutoff s ω (t + 1) := by
  rw [markedAt_succ]
  by_cases ht : s ≤ t
  · rw [if_pos ht]
    cases hd : drawLabels init ω (t + 1) with
    | none => exact fun _ h => h
    | some ij => exact markUpdate_mono C _ _ ℓ cutoff ij.1 ij.2
  · simpa only [if_neg ht, markedAt_empty_before_seed init C ℓ cutoff s ω t (by omega)]
      using (Finset.empty_subset (∅ : Finset (Fin init.card)))

open Classical in
theorem markedAt_card_step (init : Cfg L K) (C : Finset (Fin init.card))
    (ℓ cutoff s t : ℕ) (ω : Ω L K) (hst : s ≤ t)
    (hd : Disjoint (markedAt init C ℓ cutoff s ω t)
      (sourceSet C (virtualLabels init ω t) ℓ)) :
    (markedAt init C ℓ cutoff s ω (t + 1)).card =
      (markedAt init C ℓ cutoff s ω t).card +
        (if ∃ i j, drawLabels init ω (t + 1) = some (i, j) ∧
          EarlyDrip C (virtualLabels init ω t) ℓ cutoff i j then 1 else 0) +
        (if ∃ i j, drawLabels init ω (t + 1) = some (i, j) ∧
          Propagation C (markedAt init C ℓ cutoff s ω t) i j then 1 else 0) := by
  cases he : drawLabels init ω (t + 1) with
  | none => simp [markedAt_succ, hst, he, markStep]
  | some ij =>
      rcases ij with ⟨i, j⟩
      simpa [markedAt_succ, hst, he, markStep] using
        markUpdate_card C (markedAt init C ℓ cutoff s ω t)
          (virtualLabels init ω t) ℓ cutoff i j hd

theorem markedAt_card_step_le_add_one (init : Cfg L K) (C : Finset (Fin init.card))
    (ℓ cutoff s t : ℕ) (ω : Ω L K) (hst : s ≤ t)
    (hd : Disjoint (markedAt init C ℓ cutoff s ω t)
      (sourceSet C (virtualLabels init ω t) ℓ)) :
    (markedAt init C ℓ cutoff s ω (t + 1)).card ≤
      (markedAt init C ℓ cutoff s ω t).card + 1 := by
  cases he : drawLabels init ω (t + 1) with
  | none => simp [markedAt_succ, hst, he, markStep]
  | some ij =>
      rcases ij with ⟨i, j⟩
      simpa only [markedAt_succ, if_pos hst, he, markStep] using
        markUpdate_card_le_add_one C (markedAt init C ℓ cutoff s ω t)
          (virtualLabels init ω t) ℓ cutoff i j hd

theorem markedPredicate_measurable (init : Cfg L K) (C : Finset (Fin init.card))
    (ℓ cutoff s t : ℕ) (P : Finset (Fin init.card) → Prop) :
    MeasurableSet[pairLogFiltration L K t] {ω | P (markedAt init C ℓ cutoff s ω t)} :=
  (show MeasurableSet {p : (k : Finset.Iic t) → Draw L K |
      P (markedPrefix init C ℓ cutoff s t p)} from
    (Set.to_countable _).measurableSet).preimage (measurable_pairLog_prefix L K t)

open Classical in
def propagationIndicator (init : Cfg L K) (C : Finset (Fin init.card))
    (ℓ cutoff s t : ℕ) (ω : Ω L K) : ℝ :=
  if ∃ i j, drawLabels init ω (t + 1) = some (i, j) ∧
    Propagation C (markedAt init C ℓ cutoff s ω t) i j then 1 else 0

open Classical in
def immigrationIndicator (init : Cfg L K) (C : Finset (Fin init.card))
    (ℓ cutoff t : ℕ) (ω : Ω L K) : ℝ :=
  if ∃ i j, drawLabels init ω (t + 1) = some (i, j) ∧
    EarlyDrip C (virtualLabels init ω t) ℓ cutoff i j then 1 else 0

theorem propagation_conditional_law (init : Cfg L K) (hc : 2 ≤ init.card)
    (C : Finset (Fin init.card)) (ℓ cutoff s t : ℕ) :
    (law init)[propagationIndicator init C ℓ cutoff s t | pairLogFiltration L K t]
      =ᵐ[law init] fun ω =>
        ((2 * (markedAt init C ℓ cutoff s ω t).card *
          (C.card - (markedAt init C ℓ cutoff s ω t).card) : ℕ) : ℝ) /
          ((init.card : ℝ) * ((init.card : ℝ) - 1)) := by
  have h := prefix_pair_conditional_probability init hc t
    (fun p => Propagation C (markedPrefix init C ℓ cutoff s t p))
  filter_upwards [h] with ω hω
  have hc2 := propagation_pairSet_card C _ (markedAt_subset_mask init C ℓ cutoff s ω t)
  have hω' : (law init)[propagationIndicator init C ℓ cutoff s t | pairLogFiltration L K t] ω =
      ((pairSet (Propagation C (markedAt init C ℓ cutoff s ω t))).card : ℝ) /
        ((init.card : ℝ) * ((init.card : ℝ) - 1)) := hω
  rw [hω', hc2]

open Classical in
theorem immigration_conditional_law (init : Cfg L K) (hc : 2 ≤ init.card)
    (C : Finset (Fin init.card)) (ℓ cutoff t : ℕ) :
    (law init)[immigrationIndicator init C ℓ cutoff t | pairLogFiltration L K t]
      =ᵐ[law init] fun ω =>
        (if frontCount (virtualLabels init ω t) ℓ < cutoff ∧ ℓ < K * (L + 1)
          then (((sourceSet C (virtualLabels init ω t) ℓ).card *
            ((sourceSet C (virtualLabels init ω t) ℓ).card - 1) : ℕ) : ℝ) else 0) /
          ((init.card : ℝ) * ((init.card : ℝ) - 1)) := by
  have h := prefix_pair_conditional_probability init hc t
    (fun p => EarlyDrip C (auxPrefix init virtualRule t p) ℓ cutoff)
  filter_upwards [h] with ω hω
  simpa only [immigrationIndicator, virtualLabels, auxLabels,
    earlyDrip_pairSet_card, apply_ite, Nat.cast_zero] using hω

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockEarlyMarks

end
