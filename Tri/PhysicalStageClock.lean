/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Lemma16To19
import Tri.StagedLazyHitting

/-!
# Exact physical clock of activation stages

The counted Lemma 16--19 carriers are bookkeeping refinements of the genuine
identity-refined infection chain.  After forgetting their local ledgers, one
stage is exactly the physical kernel frozen at the block's anchored activation
checkpoint.
-/

namespace Tri

noncomputable section

/-- Active-count checkpoint anchored at the start of one physical block. -/
def PhysicalActivationCheckpoint
    {n : ℕ} (anchor : InfectionRevealPhysicalState n)
    (k : ℕ) (s : InfectionRevealPhysicalState n) : Prop :=
  anchor.coarse.1.active + k ≤ s.coarse.1.active

noncomputable instance physicalActivationCheckpointDecidable
    {n : ℕ} (anchor : InfectionRevealPhysicalState n)
    (k : ℕ) :
    DecidablePred (PhysicalActivationCheckpoint anchor k) :=
  Classical.decPred _

/-- On the reachable path invariant, a counted Lemma 16 step projects to the
physical infection step frozen at its anchored activation checkpoint. -/
theorem lemma16CountedPathStep_map_physical_on_inv
    (n : ℕ) (h3 : 3 ≤ n) (k : ℕ)
    (s : InfectionRevealPhysicalState n)
    (q : Lemma16CountedPathState n)
    (hq : Lemma16CountedPathInv s k q) :
    (lemma16CountedPathStep n h3 k q).map
        (fun z => z.path.current) =
      freeze (PhysicalActivationCheckpoint s k)
        (infectionRevealPhysicalStep n h3)
        q.path.current := by
  have hanchor :
      q.path.anchor.coarse.1.active =
        s.coarse.1.active := by
    rw [hq.1]
  have hledger := q.path.hactiveLedger
  by_cases hreach :
      InfectionRevealPhysicalFirstKReached k q.path
  · have htarget :
        PhysicalActivationCheckpoint s k q.path.current := by
      simp only [InfectionRevealPhysicalFirstKReached] at hreach
      unfold PhysicalActivationCheckpoint
      omega
    unfold lemma16CountedPathStep
    rw [if_pos hreach, PMF.pure_map,
      freeze_of_mem q.path.current htarget]
  · have htarget :
        ¬ PhysicalActivationCheckpoint s k q.path.current := by
      simp only [InfectionRevealPhysicalFirstKReached] at hreach
      unfold PhysicalActivationCheckpoint
      omega
    calc
      (lemma16CountedPathStep n h3 k q).map
          (fun z => z.path.current) =
        ((lemma16CountedPathStep n h3 k q).map
          lemma16CountedPathToPath).map
            infectionRevealPhysicalPathCurrent := by
              rw [PMF.map_comp]
              rfl
      _ =
        (infectionRevealPhysicalFirstKStep n h3 k q.path).map
          infectionRevealPhysicalPathCurrent := by
            rw [lemma16CountedPathStep_map_path]
      _ =
        (infectionRevealPhysicalPathStep n h3 q.path).map
          infectionRevealPhysicalPathCurrent := by
            unfold infectionRevealPhysicalFirstKStep
            rw [freeze_of_not_mem q.path hreach]
      _ = infectionRevealPhysicalStep n h3 q.path.current :=
        infectionRevealPhysicalPathStep_map_current n h3 q.path
      _ =
        freeze (PhysicalActivationCheckpoint s k)
          (infectionRevealPhysicalStep n h3)
          q.path.current := by
            symm
            exact freeze_of_not_mem q.path.current htarget

/-- The exact physical projection persists for the whole stopped block. -/
theorem lemma16CountedPath_iter_map_physical
    (n : ℕ) (h3 : 3 ≤ n) (k T : ℕ)
    (s : InfectionRevealPhysicalState n) :
    (iter (lemma16CountedPathStep n h3 k) T
        (lemma16CountedPathInitial s)).map
          (fun z => z.path.current) =
      iter
        (freeze (PhysicalActivationCheckpoint s k)
          (infectionRevealPhysicalStep n h3))
        T s := by
  have hinit :
      Lemma16CountedPathInv s k
        (lemma16CountedPathInitial s) := by
    constructor
    · rfl
    · simp [lemma16CountedPathInitial,
        infectionRevealPhysicalPathInitial]
  simpa [lemma16CountedPathInitial] using
    iter_map_of_step_map_on_support_invariant
      (lemma16CountedPathStep n h3 k)
      (freeze (PhysicalActivationCheckpoint s k)
        (infectionRevealPhysicalStep n h3))
      (fun z => z.path.current)
      (Lemma16CountedPathInv s k)
      (fun q hq z hz =>
        lemma16CountedPathStep_inv_closed
          n h3 k s q z hq hz)
      (lemma16CountedPathStep_map_physical_on_inv
        n h3 k s)
      T (lemma16CountedPathInitial s) hinit

/-- A projected Lemma 16 stage is exactly an anchored frozen physical block. -/
theorem lemma16PhysicalStageKernel_eq_frozenPhysical
    (n : ℕ) (h3 : 3 ≤ n) (k T : ℕ)
    (s : InfectionRevealPhysicalState n) :
    lemma16PhysicalStageKernel n h3 k T s =
      iter
        (freeze (PhysicalActivationCheckpoint s k)
          (infectionRevealPhysicalStep n h3))
        T s := by
  exact lemma16CountedPath_iter_map_physical n h3 k T s

/-- Every projected Lemma 17, 18, or 19 stage has the same exact anchored
frozen physical clock; the additional reaction ledger does not alter it. -/
theorem lemma17PhysicalStageKernel_eq_frozenPhysical
    (n : ℕ) (h3 : 3 ≤ n) (k A G T : ℕ)
    (s : InfectionRevealPhysicalState n) :
    lemma17PhysicalStageKernel n h3 k A G T s =
      iter
        (freeze (PhysicalActivationCheckpoint s k)
          (infectionRevealPhysicalStep n h3))
        T s := by
  unfold lemma17PhysicalStageKernel
  calc
    (iter (lemma17CountedPathStep n h3 k A G) T
        (lemma17CountedPathInitial s)).map
          (fun q => q.counted.path.current) =
      ((iter (lemma17CountedPathStep n h3 k A G) T
          (lemma17CountedPathInitial s)).map
            lemma17CountedPathToLemma16).map
          (fun q => q.path.current) := by
            rw [PMF.map_comp]
            rfl
    _ =
      (iter (lemma16CountedPathStep n h3 k) T
        (lemma16CountedPathInitial s)).map
          (fun q => q.path.current) := by
            rw [lemma17CountedPath_iter_map_lemma16]
            rfl
    _ =
      iter
        (freeze (PhysicalActivationCheckpoint s k)
          (infectionRevealPhysicalStep n h3))
        T s :=
      lemma16CountedPath_iter_map_physical n h3 k T s

end

end Tri

#print axioms Tri.lemma16CountedPathStep_map_physical_on_inv
#print axioms Tri.lemma16CountedPath_iter_map_physical
#print axioms Tri.lemma16PhysicalStageKernel_eq_frozenPhysical
#print axioms Tri.lemma17PhysicalStageKernel_eq_frozenPhysical
