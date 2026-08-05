/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.MultiAggregation

/-!
# The physical multi-species Tri state kernel

A firing sample transfers one molecule from the unique loser species to the
unique winner species. Inert samples are self-loops. The update is first
defined on natural-valued coordinates and then lifted to the conserved finite
configuration type.
-/

namespace Tri.Multi

open scoped BigOperators ENNReal

variable {m n : ℕ}

/-- Natural-valued coordinate update for one directed firing. -/
def transferCount
    (c : Config m n) (winner loser i : Species m) : ℕ :=
  Function.update
    (Function.update (fun j => count c j)
      loser (count c loser - 1))
    winner (count c winner + 1) i

@[simp] theorem transferCount_winner
    (c : Config m n) (winner loser : Species m) :
    transferCount c winner loser winner = count c winner + 1 := by
  simp [transferCount]

@[simp] theorem transferCount_loser
    (c : Config m n) (winner loser : Species m)
    (hne : winner ≠ loser) :
    transferCount c winner loser loser = count c loser - 1 := by
  simp [transferCount, Ne.symm hne]

theorem transferCount_of_ne
    (c : Config m n) (winner loser i : Species m)
    (hiw : i ≠ winner) (hil : i ≠ loser) :
    transferCount c winner loser i = count c i := by
  simp [transferCount, hiw, hil]

theorem sum_transferCount
    (c : Config m n) (winner loser : Species m)
    (hne : winner ≠ loser) (hloser : 0 < count c loser) :
    ∑ i, transferCount c winner loser i = n := by
  classical
  let f : Species m → ℕ := fun i => count c i
  let s : Finset (Species m) := Finset.univ.erase winner
  let r : Finset (Species m) := s.erase loser
  have hwinner : winner ∈ (Finset.univ : Finset (Species m)) := by simp
  have hloserS : loser ∈ s := by
    simp [s, Ne.symm hne]
  have hsumUpdateWinner :
      ∑ i : Species m, transferCount c winner loser i =
        count c winner + 1 +
          ∑ i ∈ s,
            Function.update f loser (count c loser - 1) i := by
    unfold transferCount
    rw [Finset.sum_update_of_mem hwinner]
    simp only [Finset.sdiff_singleton_eq_erase]
    rfl
  have hsumUpdateLoser :
      ∑ i ∈ s, Function.update f loser (count c loser - 1) i =
        count c loser - 1 + ∑ i ∈ r, f i := by
    simpa only [r, Finset.sdiff_singleton_eq_erase] using
      (Finset.sum_update_of_mem hloserS f (count c loser - 1))
  have hsumOriginal :
      ∑ i : Species m, count c i =
        count c winner + count c loser + ∑ i ∈ r, count c i := by
    have hw :=
      Finset.sum_erase_add (Finset.univ : Finset (Species m))
        (fun i => count c i) hwinner
    have hl :=
      Finset.sum_erase_add s (fun i => count c i) hloserS
    dsimp only [s, r, f] at hw hl ⊢
    omega
  rw [hsumUpdateWinner, hsumUpdateLoser]
  dsimp only [f]
  rw [sum_count] at hsumOriginal
  omega

/-- Population transfer on the conserved finite configuration space. -/
noncomputable def transfer
    (c : Config m n) (winner loser : Species m)
    (hne : winner ≠ loser) (hloser : 0 < count c loser) :
    Config m n := by
  classical
  let q : Species m → ℕ := transferCount c winner loser
  have hsum : ∑ i, q i = n := by
    exact sum_transferCount c winner loser hne hloser
  refine ⟨fun i => ⟨q i, ?_⟩, ?_⟩
  · have hi : q i ≤ ∑ j, q j := by
      exact Finset.single_le_sum
        (fun j _ => Nat.zero_le (q j)) (Finset.mem_univ i)
    rw [hsum] at hi
    omega
  · simpa only [Finset.sum_subtype] using hsum

@[simp] theorem count_transfer_winner
    (c : Config m n) (winner loser : Species m)
    (hne : winner ≠ loser) (hloser : 0 < count c loser) :
    count (transfer c winner loser hne hloser) winner =
      count c winner + 1 := by
  simp [transfer, count]

@[simp] theorem count_transfer_loser
    (c : Config m n) (winner loser : Species m)
    (hne : winner ≠ loser) (hloser : 0 < count c loser) :
    count (transfer c winner loser hne hloser) loser =
      count c loser - 1 := by
  simp [transfer, count, hne]

theorem count_transfer_of_ne
    (c : Config m n) (winner loser i : Species m)
    (hne : winner ≠ loser) (hloser : 0 < count c loser)
    (hiw : i ≠ winner) (hil : i ≠ loser) :
    count (transfer c winner loser hne hloser) i = count c i := by
  simp [transfer, count, transferCount_of_ne, hiw, hil]

/-- State reached from one physical triple sample. -/
noncomputable def sampleNext
    (c : Config m n) (t : TripleSample c) : Config m n :=
  match h : classify t with
  | none => c
  | some p =>
      transfer c p.1.1 p.1.2 p.2.1
        (count_pos_of_multiplicity_pos t p.1.2 (by
          rw [p.2.2.2]
          omega))

/-- One raw interaction of the multi-species protocol. -/
noncomputable def multiStep
    (c : Config m n) (h3 : 3 ≤ n) : PMF (Config m n) :=
  (triplePMF c h3).map (sampleNext c)

@[simp] theorem count_sampleNext
    (c : Config m n) (t : TripleSample c) (X : Species m) :
    count (sampleNext c t) X = semanticAggregateNextX X t := by
  classical
  unfold sampleNext semanticAggregateNextX semanticAggregateKind
  cases hclass : classify t with
  | none =>
      simp [Tri.nextX]
  | some p =>
      by_cases hwinner : p.1.1 = X
      · subst X
        simp [Tri.nextX]
      · by_cases hloser : p.1.2 = X
        · subst X
          simp [hwinner, Tri.nextX]
        · have hloserPos : 0 < count c p.1.2 :=
            count_pos_of_multiplicity_pos t p.1.2 (by
              rw [p.2.2.2]
              omega)
          rw [count_transfer_of_ne c p.1.1 p.1.2 X
            p.2.1 hloserPos (Ne.symm hwinner) (Ne.symm hloser)]
          simp [hwinner, hloser, Tri.nextX]

theorem multiStep_map_count
    (c : Config m n) (X : Species m) (h3 : 3 ≤ n) :
    (multiStep c h3).map (fun d => count d X) =
      semanticAggregateSampleStep c X h3 := by
  unfold multiStep semanticAggregateSampleStep
  rw [PMF.map_comp]
  apply congrArg (fun f => PMF.map f (triplePMF c h3))
  funext t
  exact count_sampleNext c t X

theorem collapsedBinarySampleStep_expect_le_multiStep_count
    (c : Config m n) (X : Species m) (h3 : 3 ≤ n)
    (F : ℕ → ℝ≥0∞) (hF : Monotone F) :
    expect (collapsedBinarySampleStep c X h3) F ≤
      expect ((multiStep c h3).map (fun d => count d X)) F := by
  rw [multiStep_map_count]
  exact
    collapsedBinarySampleStep_expect_le_semanticAggregateSampleStep
      c X h3 F hF

theorem classify_eq_none_of_consensus
    (c : Config m n) (X : Species m) (hc : ConsensusOn c X)
    (t : TripleSample c) :
    classify t = none := by
  apply classify_eq_none_of_no_fire
  intro p hp
  rcases p with ⟨winner, loser⟩
  have hzero := (consensusOn_iff_other_zero c X).1 hc
  by_cases hloserX : loser = X
  · have hwinnerX : winner ≠ X := by
      intro hwinnerX
      exact hp.1 (hwinnerX.trans hloserX.symm)
    have hwinnerPos : 0 < count c winner :=
      count_pos_of_multiplicity_pos t winner (by
        rw [hp.2.1]
        omega)
    have hwinnerZero := hzero winner hwinnerX
    omega
  · have hloserPos : 0 < count c loser :=
      count_pos_of_multiplicity_pos t loser (by
        rw [hp.2.2]
        omega)
    have hloserZero := hzero loser hloserX
    omega

theorem sampleNext_eq_self_of_consensus
    (c : Config m n) (X : Species m) (hc : ConsensusOn c X)
    (t : TripleSample c) :
    sampleNext c t = c := by
  unfold sampleNext
  rw [classify_eq_none_of_consensus c X hc t]

theorem multiStep_consensus
    (c : Config m n) (X : Species m) (hc : ConsensusOn c X)
    (h3 : 3 ≤ n) :
    multiStep c h3 = PMF.pure c := by
  unfold multiStep
  rw [show sampleNext c = (fun _ => c) from
    funext (sampleNext_eq_self_of_consensus c X hc)]
  simpa only [Function.const_apply] using
    (PMF.map_const (triplePMF c h3) c)

end Tri.Multi

#print axioms Tri.Multi.sum_transferCount
#print axioms Tri.Multi.count_transfer_winner
#print axioms Tri.Multi.count_transfer_loser
#print axioms Tri.Multi.count_sampleNext
#print axioms Tri.Multi.multiStep_map_count
#print axioms Tri.Multi.collapsedBinarySampleStep_expect_le_multiStep_count
#print axioms Tri.Multi.multiStep_consensus
