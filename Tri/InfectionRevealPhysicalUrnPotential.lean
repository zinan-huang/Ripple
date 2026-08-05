/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.InfectionRevealPhysicalHitting
import Tri.InfectionRevealUrn

/-!
# Urn potentials under genuine physical reveal batches

The remaining inactive view of one physical infection step is a mixture of
zero, one, or two successive uniform reveals.  This file exposes that law in
a form suitable for transporting superharmonic urn potentials through
physical stage kernels.
-/

namespace Tri

open scoped ENNReal

noncomputable section

/-- At a fixed semantic event, the successor inactive view and the remaining
view of the associated batch have the same law. -/
theorem infectionRevealWitnessPMF_map_after_inactive
    {n : ℕ} (s : InfectionRevealPhysicalState n)
    (e : InfectionEvent) :
    (infectionRevealWitnessPMF s e).map
        (fun w =>
          (InfectionRevealRecord.after
            ({ event := e, witness := w } :
              InfectionRevealRecord s)).inactive) =
      (infectionRevealWitnessPMF s e).map
        (fun w =>
          (infectionRevealBatchOf s e w).remaining) := by
  apply PMF.map_change_on_zero_mass
  intro w hdiff
  by_cases he : InfectionEvent.weight s.coarse.1 e = 0
  · cases w with
    | none =>
        exact absurd
          (InfectionRevealRecord.after_inactive_eq_batch_remaining_of_zero_none
            s e he)
          hdiff
    | some w =>
        simp [infectionRevealWitnessPMF, he]
  · cases w with
    | none =>
        exact infectionRevealWitnessPMF_none s e he
    | some w =>
        exact absurd
          (InfectionRevealRecord.after_inactive_eq_batch_remaining_of_some
            s e w he)
          hdiff

/-- Forgetting the physical successor state down to its inactive view gives
exactly the physical batch law pushed through its remaining-view map. -/
theorem infectionRevealPhysicalStep_map_inactive
    (n : ℕ) (h3 : 3 ≤ n)
    (s : InfectionRevealPhysicalState n) :
    (infectionRevealPhysicalStep n h3 s).map
        (fun z => z.inactive) =
      (infectionRevealBatchPMF n h3 s).map
        InfectionRevealBatch.remaining := by
  unfold infectionRevealPhysicalStep
    infectionRevealRecordPMF infectionRevealBatchPMF
  rw [PMF.map_comp, PMF.map_bind, PMF.map_bind]
  simp_rw [PMF.map_comp]
  congr 1
  funext e
  exact infectionRevealWitnessPMF_map_after_inactive s e

/-- Two dependent uniform removals are exactly two iterations of the
ordinary identity-level reveal kernel. -/
theorem infectionSequentialRevealTwoPMF_map_remaining_eq_iter
    {n m : ℕ} (v : InfectionInactiveView n)
    (hcard : m + 2 = v.ids.card) :
    (infectionSequentialRevealTwoPMF v hcard).map
        infectionSequentialRevealRemaining =
      iter (@infectionRevealKernel n) 2 v
    := by
  unfold infectionSequentialRevealTwoPMF
    infectionSequentialRevealRemaining
  rw [PMF.map_bind, iter_succ]
  have hv : 0 < v.ids.card := by omega
  unfold infectionRevealKernel
  rw [dif_pos hv]
  change
    (infectionRevealOnePMF v _).bind
        (fun i =>
          ((infectionRevealOnePMF (v.erase i) _).map
            (infectionSequentialRevealMk (v := v) i)).map
              (fun q => (v.erase q.1).erase q.2)) =
      ((infectionRevealOnePMF v _).map v.erase).bind
        (iter (@infectionRevealKernel n) 1)
  rw [PMF.bind_map]
  congr 1
  funext i
  rw [PMF.map_comp]
  have hverase :
      0 < (v.erase i).ids.card := by
    have hdrop := infectionErase_card_eq_add_one v hcard i
    omega
  simp only [iter, PMF.bind_pure, Function.comp_apply]
  unfold infectionRevealKernel
  rw [dif_pos hverase]
  congr 1

/-- From a pool of size at least three, the first two ordinary urn removals
occur before the stopped urn reaches its frozen floor. -/
theorem iter_urnChain_two_eq_urnStopped
    (q : ℕ × ℕ)
    (hthree : 3 ≤ q.1 + q.2) :
    iter urnChain 2 q = iter urnStopped 2 q := by
  rw [iter_succ, iter_succ]
  have hqLive : ¬ q.1 + q.2 ≤ 1 := by omega
  have hfirst :
      urnStopped q = urnChain q := by
    unfold urnStopped
    rw [freeze_of_not_mem q hqLive]
  rw [hfirst]
  apply PMF.bind_change_on_zero_mass
  intro z hz
  have htotal :=
    urnChain_support_total q (by omega) z hz
  have hzLive : ¬ z.1 + z.2 ≤ 1 := by omega
  simp only [iter, PMF.bind_pure]
  unfold urnStopped
  rw [freeze_of_not_mem z hzLive]

/-- The remaining-count law of a physical batch is a mixture of zero, one,
or two iterations of the stopped urn chain. -/
theorem infectionRevealBatchPMF_map_counts_eq_urnTimeChange
    (n : ℕ) (h3 : 3 ≤ n)
    (s : InfectionRevealPhysicalState n)
    {m : ℕ} (hcard : m + 3 = s.inactive.ids.card) :
    (infectionRevealBatchPMF n h3 s).map
        (infectionInactiveCounts ∘
          InfectionRevealBatch.remaining) =
      (infectionRevealBatchSizePMF n
          s.coarse.1.active s.inactive.ids.card h3
          (infectionReveal_active_add_inactive s)).bind fun
        | .zero =>
            PMF.pure (infectionInactiveCounts s.inactive)
        | .one =>
            iter urnStopped 1
              (infectionInactiveCounts s.inactive)
        | .two =>
            iter urnStopped 2
              (infectionInactiveCounts s.inactive) := by
  rw [infectionRevealBatchPMF_eq_mixture]
  unfold infectionRevealBatchMixturePMF
  rw [PMF.map_bind]
  congr 1
  funext d
  cases d with
  | zero =>
      change
        (PMF.pure InfectionRevealBatch.none).map
            (infectionInactiveCounts ∘
              InfectionRevealBatch.remaining) =
          PMF.pure
            (infectionInactiveCounts s.inactive)
      rw [PMF.pure_map]
      rfl
  | one =>
      have hpos : 0 < s.inactive.ids.card := by omega
      have hne :
          Nonempty (InfectionInactiveId s.inactive) :=
        infectionRevealOne_nonempty_of_card_pos
          s.inactive hpos
      calc
        (infectionRevealGivenBatchSize s .one).map
              (infectionInactiveCounts ∘
                InfectionRevealBatch.remaining) =
            ((infectionRevealGivenBatchSize s .one).map
              InfectionRevealBatch.remaining).map
                infectionInactiveCounts := by
                  rw [PMF.map_comp]
        _ =
            ((infectionRevealOnePMF s.inactive hne).map
              s.inactive.erase).map
                infectionInactiveCounts := by
                  rw [
                    infectionRevealGivenBatchSize_one_map_remaining
                      s hne]
        _ =
            (infectionRevealKernel s.inactive).map
              infectionInactiveCounts := by
                unfold infectionRevealKernel
                rw [dif_pos hpos]
        _ = urnChain
              (infectionInactiveCounts s.inactive) :=
            infectionRevealKernel_intertwines_urnChain
              n s.inactive
        _ = urnStopped
              (infectionInactiveCounts s.inactive) := by
            symm
            unfold urnStopped
            rw [freeze_of_not_mem]
            have hcounts :=
              InfectionInactiveView.xIds_card_add_yIds_card
                s.inactive
            simp only [infectionInactiveCounts]
            omega
        _ = iter urnStopped 1
              (infectionInactiveCounts s.inactive) := by
            simp [iter]
  | two =>
      have hcardTwo :
          (m + 1) + 2 = s.inactive.ids.card := by
        omega
      calc
        (infectionRevealGivenBatchSize s .two).map
              (infectionInactiveCounts ∘
                InfectionRevealBatch.remaining) =
            ((infectionRevealGivenBatchSize s .two).map
              InfectionRevealBatch.remaining).map
                infectionInactiveCounts := by
                  rw [PMF.map_comp]
        _ =
            ((infectionSequentialRevealTwoPMF
              s.inactive hcardTwo).map
                infectionSequentialRevealRemaining).map
                  infectionInactiveCounts := by
                    rw [
                      infectionRevealGivenBatchSize_two_map_remaining
                        s hcardTwo]
        _ =
            (iter infectionRevealKernel 2
              s.inactive).map infectionInactiveCounts := by
                rw [
                  infectionSequentialRevealTwoPMF_map_remaining_eq_iter
                    s.inactive hcardTwo]
        _ =
            iter urnChain 2
              (infectionInactiveCounts s.inactive) :=
          iter_map_of_intertwines
            (infectionRevealKernel_intertwines_urnChain n)
            2 s.inactive
        _ =
            iter urnStopped 2
              (infectionInactiveCounts s.inactive) := by
          apply iter_urnChain_two_eq_urnStopped
          have hcounts :=
            InfectionInactiveView.xIds_card_add_yIds_card
              s.inactive
          simp only [infectionInactiveCounts]
          omega

/-- Every eventual hitting potential of the stopped urn chain remains
superharmonic under one genuine physical infection step while at least three
inactive identities remain. -/
theorem expect_infectionRevealPhysicalStep_urnEverHit_le
    (n : ℕ) (h3 : 3 ≤ n)
    (s : InfectionRevealPhysicalState n)
    {m : ℕ} (hcard : m + 3 = s.inactive.ids.card)
    (Bad : ℕ × ℕ → Prop) [DecidablePred Bad] :
    expect
        (infectionRevealPhysicalStep n h3 s)
        (fun z =>
          everHit Bad urnStopped
            (infectionInactiveCounts z.inactive))
      ≤
        everHit Bad urnStopped
          (infectionInactiveCounts s.inactive) := by
  let V := everHit Bad urnStopped
  let q := infectionInactiveCounts s.inactive
  let sizePMF :=
    infectionRevealBatchSizePMF n
      s.coarse.1.active s.inactive.ids.card h3
      (infectionReveal_active_add_inactive s)
  calc
    expect
        (infectionRevealPhysicalStep n h3 s)
        (fun z => V
          (infectionInactiveCounts z.inactive)) =
      expect
        ((infectionRevealPhysicalStep n h3 s).map
          (fun z => z.inactive))
        (fun v => V (infectionInactiveCounts v)) := by
          rw [expect_map]
    _ =
      expect
        ((infectionRevealBatchPMF n h3 s).map
          InfectionRevealBatch.remaining)
        (fun v => V (infectionInactiveCounts v)) := by
          rw [infectionRevealPhysicalStep_map_inactive]
    _ =
      expect
        (((infectionRevealBatchPMF n h3 s).map
          InfectionRevealBatch.remaining).map
            infectionInactiveCounts)
        V := by
          exact
            (expect_map
              ((infectionRevealBatchPMF n h3 s).map
                InfectionRevealBatch.remaining)
              infectionInactiveCounts
              V).symm
    _ =
      expect
        ((infectionRevealBatchPMF n h3 s).map
          (infectionInactiveCounts ∘
            InfectionRevealBatch.remaining))
        V := by
          rw [PMF.map_comp]
    _ =
      expect
        (sizePMF.bind fun
          | .zero => PMF.pure q
          | .one => iter urnStopped 1 q
          | .two => iter urnStopped 2 q)
        V := by
          rw [
            infectionRevealBatchPMF_map_counts_eq_urnTimeChange
              n h3 s hcard]
    _ =
      ∑' d,
        sizePMF d *
          expect
            (match d with
              | .zero => PMF.pure q
              | .one => iter urnStopped 1 q
              | .two => iter urnStopped 2 q)
            V := by
          rw [expect_bind']
    _ ≤
      ∑' d, sizePMF d * V q := by
        refine ENNReal.tsum_le_tsum fun d => ?_
        apply mul_le_mul_right
        cases d with
        | zero => simp [V]
        | one =>
            exact expect_iter_everHit_le
              Bad urnStopped 1 q
        | two =>
            exact expect_iter_everHit_le
              Bad urnStopped 2 q
    _ = V q := by
      rw [ENNReal.tsum_mul_right, PMF.tsum_coe,
        one_mul]

end

end Tri

#print axioms Tri.infectionRevealWitnessPMF_map_after_inactive
#print axioms Tri.infectionRevealPhysicalStep_map_inactive
#print axioms Tri.infectionSequentialRevealTwoPMF_map_remaining_eq_iter
#print axioms Tri.iter_urnChain_two_eq_urnStopped
#print axioms Tri.infectionRevealBatchPMF_map_counts_eq_urnTimeChange
#print axioms Tri.expect_infectionRevealPhysicalStep_urnEverHit_le
