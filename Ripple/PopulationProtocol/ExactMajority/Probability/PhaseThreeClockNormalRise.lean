-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockNormalRise.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockEarlyMarkEmbedding

/-!
# The concrete normal-high increment and its ordered-pair bound

Normal labels are the upper-front labels outside the natural mark set.
A positive normal-count increment requires an upper-front gated tick with
no mark propagation. Such a pair either has an unmarked high source or
consists of two exact-level labels. Its cardinality is at most X^2+2CY.

The selected-step lemmas are pointwise on explicit pre/post safe states.
The final conditional law is for the observed candidate pair predicate.
A guarded stopped-process adapter is still needed to transfer that law to
the normal increment at a possible next-step safety breach.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal BigOperators MeasureTheory ProbabilityTheory

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockNormalRise

open TimeTheorem PairLog PairLogAuxiliary PhaseThreeClockVirtual
  PhaseThreeClockGatedLaw PhaseThreeClockGatedLevelOne
  PhaseThreeClockEmbeddingBridge PhaseThreeClockPredictablePairs
  PhaseThreeClockEarlyMarks PhaseThreeClockEarlyMarkEmbedding

variable {L K m : ℕ}

def normalSet (f : Fin m → AgentState L K) (M : Finset (Fin m)) (ℓ : ℕ) :
    Finset (Fin m) := aboveSet f (ℓ + 1) \ M

def normalCount (f : Fin m → AgentState L K) (M : Finset (Fin m)) (ℓ : ℕ) : ℕ :=
  (normalSet f M ℓ).card

def NormalRisePair (f : Fin m → AgentState L K) (M : Finset (Fin m))
    (ℓ : ℕ) (i j : Fin m) : Prop :=
  GatedTick (ℓ + 1) f i j ∧ ¬ Propagation (clockSet f) M i j

theorem normalCount_eq_sub (f : Fin m → AgentState L K) (M : Finset (Fin m))
    (ℓ : ℕ) (hM : M ⊆ aboveSet f (ℓ + 1)) :
    normalCount f M ℓ = frontCount f (ℓ + 1) - M.card :=
  Finset.card_sdiff_of_subset hM

theorem normalCount_le_clockCount (f : Fin m → AgentState L K)
    (M : Finset (Fin m)) (ℓ : ℕ) :
    normalCount f M ℓ ≤ clockCount f := by
  apply Finset.card_le_card
  intro i hi
  have hu := (Finset.mem_sdiff.mp hi).1
  have hclock : (f i).role = .clock :=
    (Finset.mem_filter.mp hu).2.1
  simpa only [clockSet, Finset.mem_filter, Finset.mem_univ, true_and] using hclock

theorem normalRisePair_cover (f : Fin m → AgentState L K)
    (M : Finset (Fin m)) (ℓ : ℕ) (hM : M ⊆ aboveSet f (ℓ + 1)) :
    pairSet (NormalRisePair f M ℓ) ⊆
      ((clockSet f ×ˢ normalSet f M ℓ) ∪ (normalSet f M ℓ ×ˢ clockSet f)) ∪
        (sourceSet (clockSet f) f ℓ).offDiag := by
  classical
  rintro ⟨i, j⟩ hp
  have hp' : i ≠ j ∧ NormalRisePair f M ℓ i j := by
    simpa only [pairSet, Finset.mem_filter, Finset.mem_univ, true_and] using hp
  rcases hp'.2.1.1 with hcopy | hcopy | hdrip
  · have hi : (f i).role = .clock ∧ ¬ (ℓ + 1 ≤ effMinute (f i)) := by
      simpa only [belowSet, Finset.mem_filter, Finset.mem_univ, true_and] using hcopy.1
    have hic : i ∈ clockSet f := by
      simpa only [clockSet, Finset.mem_filter, Finset.mem_univ, true_and] using hi.1
    have hin : i ∉ M := by
      intro him
      exact hi.2 (Finset.mem_filter.mp (hM him)).2.2
    have hjn : j ∉ M := by
      intro hjm
      exact hp'.2.2 (Or.inr ⟨Finset.mem_sdiff.mpr ⟨hic, hin⟩, hjm⟩)
    have hjnormal : j ∈ normalSet f M ℓ := Finset.mem_sdiff.mpr ⟨hcopy.2, hjn⟩
    exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
      (Or.inl (Finset.mem_product.mpr ⟨hic, hjnormal⟩))))
  · have hj : (f j).role = .clock ∧ ¬ (ℓ + 1 ≤ effMinute (f j)) := by
      simpa only [belowSet, Finset.mem_filter, Finset.mem_univ, true_and] using hcopy.2
    have hjc : j ∈ clockSet f := by
      simpa only [clockSet, Finset.mem_filter, Finset.mem_univ, true_and] using hj.1
    have hjn : j ∉ M := by
      intro hjm
      exact hj.2 (Finset.mem_filter.mp (hM hjm)).2.2
    have hin : i ∉ M := by
      intro him
      exact hp'.2.2 (Or.inl ⟨him, Finset.mem_sdiff.mpr ⟨hjc, hjn⟩⟩)
    have hinormal : i ∈ normalSet f M ℓ := Finset.mem_sdiff.mpr ⟨hcopy.1, hin⟩
    exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
      (Or.inr (Finset.mem_product.mpr ⟨hinormal, hjc⟩))))
  · have hi : i ∈ sourceSet (clockSet f) f ℓ := by
      rw [sourceSet_eq_exactSet]
      simpa only [Nat.add_sub_cancel] using hdrip.1
    have hj : j ∈ sourceSet (clockSet f) f ℓ := by
      rw [sourceSet_eq_exactSet]
      simpa only [Nat.add_sub_cancel] using hdrip.2
    exact Finset.mem_union.mpr (Or.inr (Finset.mem_offDiag.mpr ⟨hi, hj, hp'.1⟩))

/-- The numerator in P4, obtained by counting actual ordered label pairs. -/
theorem normalRisePair_card_bound (f : Fin m → AgentState L K)
    (M : Finset (Fin m)) (ℓ : ℕ) (hM : M ⊆ aboveSet f (ℓ + 1)) :
    (pairSet (NormalRisePair f M ℓ)).card ≤
      (frontCount f ℓ) ^ 2 + 2 * clockCount f * normalCount f M ℓ := by
  classical
  let A := clockSet f ×ˢ normalSet f M ℓ
  let B := normalSet f M ℓ ×ˢ clockSet f
  let S := sourceSet (clockSet f) f ℓ
  have hdiag : S.offDiag ⊆ S ×ˢ S := by
    intro ij hij
    have h := Finset.mem_offDiag.mp hij
    exact Finset.mem_product.mpr ⟨h.1, h.2.1⟩
  have hsource : S.card ≤ frontCount f ℓ := sourceSet_card_le_front f ℓ
  have hdiagcard : S.offDiag.card ≤ (frontCount f ℓ) ^ 2 := by
    calc
      S.offDiag.card ≤ (S ×ˢ S).card := Finset.card_le_card hdiag
      _ = S.card * S.card := Finset.card_product _ _
      _ ≤ frontCount f ℓ * frontCount f ℓ := Nat.mul_le_mul hsource hsource
      _ = _ := by ring
  calc
    (pairSet (NormalRisePair f M ℓ)).card ≤ ((A ∪ B) ∪ S.offDiag).card :=
      Finset.card_le_card (normalRisePair_cover f M ℓ hM)
    _ ≤ (A ∪ B).card + S.offDiag.card := Finset.card_union_le _ _
    _ ≤ A.card + B.card + S.offDiag.card :=
      add_le_add (Finset.card_union_le A B) le_rfl
    _ ≤ A.card + B.card + (frontCount f ℓ) ^ 2 :=
      add_le_add le_rfl hdiagcard
    _ = _ := by
      simp only [A, B, Finset.card_product, clockCount, normalCount]
      ring

/-- Pointwise safe-step normal-count law for the actual natural marks. -/
theorem normalCount_step_of_selected (init : Cfg L 256)
    (C : Finset (Fin init.card)) (ℓ cutoff s t : ℕ) (ω : Ω L 256)
    (hst : s ≤ t) (hℓ : 1 ≤ ℓ) (hcap : ℓ + 1 ≤ 256 * (L + 1))
    (henv : ClockEnvironment (virtualLabels init ω t))
    (hmask : C = clockSet (virtualLabels init ω t))
    (hM : markedAt init C ℓ cutoff s ω t ⊆ aboveSet (virtualLabels init ω t) (ℓ + 1))
    (hpost : ∀ k, (virtualLabels init ω (t + 1) k).phase.val ≤ 3)
    (i j : Fin init.card) (hd : drawLabels init ω (t + 1) = some (i, j)) :
    normalCount (virtualLabels init ω (t + 1)) (markedAt init C ℓ cutoff s ω (t + 1)) ℓ ≤
        normalCount (virtualLabels init ω t) (markedAt init C ℓ cutoff s ω t) ℓ + 1 ∧
      (normalCount (virtualLabels init ω (t + 1)) (markedAt init C ℓ cutoff s ω (t + 1)) ℓ =
          normalCount (virtualLabels init ω t) (markedAt init C ℓ cutoff s ω t) ℓ + 1 →
        NormalRisePair (virtualLabels init ω t) (markedAt init C ℓ cutoff s ω t) ℓ i j) := by
  classical
  have hMnext := markedAt_step_subset_above init (by decide) C ℓ cutoff s t ω hst hℓ
    henv hmask hM hpost
  have hy := normalCount_eq_sub _ _ ℓ hM
  have hynext := normalCount_eq_sub _ _ ℓ hMnext
  have hMle : (markedAt init C ℓ cutoff s ω t).card ≤
      frontCount (virtualLabels init ω t) (ℓ + 1) := Finset.card_le_card hM
  have hMnle : (markedAt init C ℓ cutoff s ω (t + 1)).card ≤
      frontCount (virtualLabels init ω (t + 1)) (ℓ + 1) := Finset.card_le_card hMnext
  have hmono : (markedAt init C ℓ cutoff s ω t).card ≤
      (markedAt init C ℓ cutoff s ω (t + 1)).card :=
    Finset.card_le_card (markedAt_step_mono init C ℓ cutoff s ω t)
  have hf := frontCount_virtualLabels_succ_of_phase_range init ω t i j hd
    henv.phase_range (fun k hk => henv.carrier k (Or.inr (Or.inr hk)))
    hpost (ℓ + 1) (by omega) hcap
  have hfupper : frontCount (virtualLabels init ω (t + 1)) (ℓ + 1) ≤
      frontCount (virtualLabels init ω t) (ℓ + 1) + 1 := by
    rw [hf]
    split_ifs <;> omega
  have hm :
      (markedAt init C ℓ cutoff s ω (t + 1)).card =
        (markedAt init C ℓ cutoff s ω t).card +
          (if EarlyDrip C (virtualLabels init ω t) ℓ cutoff i j then 1 else 0) +
          (if Propagation C (markedAt init C ℓ cutoff s ω t) i j then 1 else 0) := by
    simpa only [markedAt_succ, if_pos hst, hd, markStep] using
      markUpdate_card C (markedAt init C ℓ cutoff s ω t) (virtualLabels init ω t)
        ℓ cutoff i j (marks_source_disjoint C _ _ ℓ hM)
  refine ⟨by omega, ?_⟩
  intro hrise
  constructor
  · by_contra hg
    rw [if_neg hg] at hf
    omega
  · intro hp
    have hpC : Propagation C (markedAt init C ℓ cutoff s ω t) i j := by
      simpa only [hmask] using hp
    rw [if_pos hpC] at hm
    have hlower : (markedAt init C ℓ cutoff s ω t).card + 1 ≤
        (markedAt init C ℓ cutoff s ω (t + 1)).card := by
      split_ifs at hm <;> omega
    omega

theorem normalCount_delta_cases (init : Cfg L 256)
    (C : Finset (Fin init.card)) (ℓ cutoff s t : ℕ) (ω : Ω L 256)
    (hst : s ≤ t) (hℓ : 1 ≤ ℓ) (hcap : ℓ + 1 ≤ 256 * (L + 1))
    (henv : ClockEnvironment (virtualLabels init ω t))
    (hmask : C = clockSet (virtualLabels init ω t))
    (hM : markedAt init C ℓ cutoff s ω t ⊆ aboveSet (virtualLabels init ω t) (ℓ + 1))
    (hpost : ∀ k, (virtualLabels init ω (t + 1) k).phase.val ≤ 3) :
    ((normalCount (virtualLabels init ω (t + 1))
        (markedAt init C ℓ cutoff s ω (t + 1)) ℓ : ℝ) -
      (normalCount (virtualLabels init ω t) (markedAt init C ℓ cutoff s ω t) ℓ : ℝ) ≤ 0) ∨
    ((normalCount (virtualLabels init ω (t + 1))
        (markedAt init C ℓ cutoff s ω (t + 1)) ℓ : ℝ) -
      (normalCount (virtualLabels init ω t) (markedAt init C ℓ cutoff s ω t) ℓ : ℝ) = 1) := by
  cases hd : drawLabels init ω (t + 1) with
  | none =>
      have hf : virtualLabels init ω (t + 1) = virtualLabels init ω t := by
        simp only [virtualLabels_succ, hd, auxStep]
      have hm : markedAt init C ℓ cutoff s ω (t + 1) = markedAt init C ℓ cutoff s ω t := by
        simp only [markedAt_succ, if_pos hst, hd, markStep]
      simp only [hf, hm, sub_self, le_refl, true_or]
  | some ij =>
      rcases ij with ⟨i, j⟩
      have hupper := (normalCount_step_of_selected init C ℓ cutoff s t ω hst hℓ hcap
        henv hmask hM hpost i j hd).1
      by_cases hdown : normalCount (virtualLabels init ω (t + 1))
          (markedAt init C ℓ cutoff s ω (t + 1)) ℓ ≤
          normalCount (virtualLabels init ω t) (markedAt init C ℓ cutoff s ω t) ℓ
      · left
        have hdownR : (normalCount (virtualLabels init ω (t + 1))
            (markedAt init C ℓ cutoff s ω (t + 1)) ℓ : ℝ) ≤
            (normalCount (virtualLabels init ω t) (markedAt init C ℓ cutoff s ω t) ℓ : ℝ) := by
          exact_mod_cast hdown
        linarith
      · right
        have heq : normalCount (virtualLabels init ω (t + 1))
            (markedAt init C ℓ cutoff s ω (t + 1)) ℓ =
            normalCount (virtualLabels init ω t) (markedAt init C ℓ cutoff s ω t) ℓ + 1 := by omega
        rw [heq, Nat.cast_add, Nat.cast_one]
        ring

open Classical in
def normalRiseIndicator (init : Cfg L K) (C : Finset (Fin init.card))
    (ℓ cutoff s t : ℕ) (ω : Ω L K) : ℝ :=
  if ∃ i j, drawLabels init ω (t + 1) = some (i, j) ∧
    NormalRisePair (virtualLabels init ω t) (markedAt init C ℓ cutoff s ω t) ℓ i j
    then 1 else 0


/-- The actual safe-step positive-increment indicator is dominated by the
candidate-pair indicator. The post-state guard is pointwise here; it is
not used as a future conditioning event. -/
theorem normal_increment_indicator_le_candidate (init : Cfg L 256)
    (C : Finset (Fin init.card)) (ℓ cutoff s t : ℕ) (ω : Ω L 256)
    (hst : s ≤ t) (hℓ : 1 ≤ ℓ) (hcap : ℓ + 1 ≤ 256 * (L + 1))
    (henv : ClockEnvironment (virtualLabels init ω t))
    (hmask : C = clockSet (virtualLabels init ω t))
    (hM : markedAt init C ℓ cutoff s ω t ⊆ aboveSet (virtualLabels init ω t) (ℓ + 1))
    (hpost : ∀ k, (virtualLabels init ω (t + 1) k).phase.val ≤ 3) :
    (if (normalCount (virtualLabels init ω (t + 1))
        (markedAt init C ℓ cutoff s ω (t + 1)) ℓ : ℝ) -
      (normalCount (virtualLabels init ω t) (markedAt init C ℓ cutoff s ω t) ℓ : ℝ) = 1
      then (1 : ℝ) else 0) ≤ normalRiseIndicator init C ℓ cutoff s t ω := by
  classical
  by_cases hdelta : (normalCount (virtualLabels init ω (t + 1))
        (markedAt init C ℓ cutoff s ω (t + 1)) ℓ : ℝ) -
      (normalCount (virtualLabels init ω t) (markedAt init C ℓ cutoff s ω t) ℓ : ℝ) = 1
  · rw [if_pos hdelta]
    have heqR : (normalCount (virtualLabels init ω (t + 1))
        (markedAt init C ℓ cutoff s ω (t + 1)) ℓ : ℝ) =
        (normalCount (virtualLabels init ω t) (markedAt init C ℓ cutoff s ω t) ℓ : ℝ) + 1 := by
      linarith
    have heq : normalCount (virtualLabels init ω (t + 1))
        (markedAt init C ℓ cutoff s ω (t + 1)) ℓ =
        normalCount (virtualLabels init ω t) (markedAt init C ℓ cutoff s ω t) ℓ + 1 := by
      exact_mod_cast heqR
    cases hd : drawLabels init ω (t + 1) with
    | none =>
        have hf : virtualLabels init ω (t + 1) = virtualLabels init ω t := by
          simp only [virtualLabels_succ, hd, auxStep]
        have hm : markedAt init C ℓ cutoff s ω (t + 1) = markedAt init C ℓ cutoff s ω t := by
          simp only [markedAt_succ, if_pos hst, hd, markStep]
        rw [hf, hm] at heq
        omega
    | some ij =>
        rcases ij with ⟨i, j⟩
        have hpair := (normalCount_step_of_selected init C ℓ cutoff s t ω hst hℓ hcap
          henv hmask hM hpost i j hd).2 heq
        have hex : ∃ i j, drawLabels init ω (t + 1) = some (i, j) ∧
            NormalRisePair (virtualLabels init ω t) (markedAt init C ℓ cutoff s ω t) ℓ i j :=
          ⟨i, j, hd, hpair⟩
        simp only [normalRiseIndicator, if_pos hex, le_refl]
  · rw [if_neg hdelta]
    unfold normalRiseIndicator
    split_ifs <;> norm_num

theorem normalRiseIndicator_conditional_law (init : Cfg L K) (hc : 2 ≤ init.card)
    (C : Finset (Fin init.card)) (ℓ cutoff s t : ℕ) :
    (law init)[normalRiseIndicator init C ℓ cutoff s t | pairLogFiltration L K t] =ᵐ[law init]
      fun ω => ((pairSet (NormalRisePair (virtualLabels init ω t)
        (markedAt init C ℓ cutoff s ω t) ℓ)).card : ℝ) /
        ((init.card : ℝ) * ((init.card : ℝ) - 1)) := by
  have h := prefix_pair_conditional_probability init hc t
    (fun p => NormalRisePair (auxPrefix init virtualRule t p)
      (markedPrefix init C ℓ cutoff s t p) ℓ)
  simpa only [normalRiseIndicator, virtualLabels, auxLabels, markedAt] using h

/-- The actual candidate-pair conditional probability has the P4 numerator.
Its antecedent concerns the current observed marked state only. -/
theorem normalRiseIndicator_conditional_upper (init : Cfg L K) (hc : 2 ≤ init.card)
    (C : Finset (Fin init.card)) (ℓ cutoff s t : ℕ) :
    ∀ᵐ ω ∂law init,
      markedAt init C ℓ cutoff s ω t ⊆ aboveSet (virtualLabels init ω t) (ℓ + 1) →
      ((law init)[normalRiseIndicator init C ℓ cutoff s t | pairLogFiltration L K t]) ω ≤
        ((frontCount (virtualLabels init ω t) ℓ : ℝ) ^ 2 +
          2 * (clockCount (virtualLabels init ω t) : ℝ) *
            (normalCount (virtualLabels init ω t) (markedAt init C ℓ cutoff s ω t) ℓ : ℝ)) /
          ((init.card : ℝ) * ((init.card : ℝ) - 1)) := by
  filter_upwards [normalRiseIndicator_conditional_law init hc C ℓ cutoff s t] with ω hce
  intro hM
  have hcard := normalRisePair_card_bound (virtualLabels init ω t)
    (markedAt init C ℓ cutoff s ω t) ℓ hM
  have hcardR :
      ((pairSet (NormalRisePair (virtualLabels init ω t)
        (markedAt init C ℓ cutoff s ω t) ℓ)).card : ℝ) ≤
        (frontCount (virtualLabels init ω t) ℓ : ℝ) ^ 2 +
          2 * (clockCount (virtualLabels init ω t) : ℝ) *
            (normalCount (virtualLabels init ω t) (markedAt init C ℓ cutoff s ω t) ℓ : ℝ) := by
    exact_mod_cast hcard
  have hm : (2 : ℝ) ≤ (init.card : ℝ) := by exact_mod_cast hc
  rw [hce]
  exact div_le_div_of_nonneg_right hcardR
    (mul_nonneg (by linarith) (by linarith))

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockNormalRise

end
