/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.StagedKernel
import Tri.LazyHitting

/-!
# Hitting comparison for staged frozen kernels

A sequence of block kernels may freeze at a different checkpoint in every
block.  This module flattens such blocks into one micro-step process.  Every
projected micro-step is either a step of the original kernel or a self-loop,
so the original chain has at least the flattened schedule's chance of hitting
any final target within the sum of the block horizons.
-/

namespace Tri

open scoped ENNReal

noncomputable section

variable {α : Type*}

/-- Control state flattening a sequence of frozen blocks into micro-steps. -/
structure StagedFreezeControl (α : Type*) where
  stage : ℕ
  anchor : α
  current : α
  remaining : ℕ

namespace StagedFreezeControl

def initial
    (T : ℕ → ℕ) (j : ℕ) (s : α) :
    StagedFreezeControl α :=
  ⟨j, s, s, T j⟩

def project (q : StagedFreezeControl α) : α :=
  q.current

/-- One flattened micro-step.  The current block's checkpoint is anchored at
the state where that block began. -/
noncomputable def step
    (K : α → PMF α)
    (B : ℕ → α → α → Prop)
    [∀ j a, DecidablePred (B j a)]
    (T : ℕ → ℕ) :
    StagedFreezeControl α → PMF (StagedFreezeControl α)
  | ⟨j, a, s, 0⟩ =>
      PMF.pure ⟨j, a, s, 0⟩
  | ⟨j, a, s, r + 1⟩ =>
      (freeze (B j a) K s).map fun z =>
        if r = 0 then
          initial T (j + 1) z
        else
          ⟨j, a, z, r⟩

@[simp] theorem project_initial
    (T : ℕ → ℕ) (j : ℕ) (s : α) :
    project (initial T j s) = s :=
  rfl

/-- The current-state projection of a live control step is exactly its
checkpoint-frozen physical step. -/
theorem step_map_project
    (K : α → PMF α)
    (B : ℕ → α → α → Prop)
    [∀ j a, DecidablePred (B j a)]
    (T : ℕ → ℕ)
    (q : StagedFreezeControl α) :
    (step K B T q).map project =
      match q.remaining with
      | 0 => PMF.pure q.current
      | _ + 1 => freeze (B q.stage q.anchor) K q.current := by
  rcases q with ⟨j, a, s, r⟩
  cases r with
  | zero =>
      unfold step
      rw [PMF.pure_map]
      rfl
  | succ r =>
      unfold step
      rw [PMF.map_comp]
      have hfun :
          project ∘
              (fun z =>
                if r = 0 then initial T (j + 1) z
                else ⟨j, a, z, r⟩) =
            id := by
        funext z
        by_cases hr : r = 0 <;>
          simp [hr, project, initial]
      rw [hfun, PMF.map_id]

/-- The flattened control process is lazy over the original kernel. -/
theorem isLazyProjection_step
    (K : α → PMF α)
    (B : ℕ → α → α → Prop)
    [∀ j a, DecidablePred (B j a)]
    (T : ℕ → ℕ) :
    IsLazyProjection K (step K B T) project := by
  intro q
  rw [step_map_project]
  cases hrem : q.remaining with
  | zero =>
      right
      rfl
  | succ r =>
      by_cases hB : B q.stage q.anchor q.current
      · right
        exact freeze_of_mem q.current hB
      · left
        exact freeze_of_not_mem q.current hB

/-- Running a positive countdown executes exactly one frozen block and resets
the next block's anchor. -/
theorem iter_countdown
    (K : α → PMF α)
    (B : ℕ → α → α → Prop)
    [∀ j a, DecidablePred (B j a)]
    (T : ℕ → ℕ)
    (j r : ℕ) (a s : α) :
    iter (step K B T) (r + 1)
        ⟨j, a, s, r + 1⟩ =
      (iter (freeze (B j a) K) (r + 1) s).map
        (initial T (j + 1)) := by
  induction r generalizing s with
  | zero =>
      rw [iter_succ, iter_succ, step, PMF.bind_map,
        PMF.map_bind]
      congr 1
      funext z
      simp only [Function.comp_apply, iter]
      rw [PMF.pure_map]
      rfl
  | succ r ih =>
      rw [iter_succ, iter_succ, step]
      simp only [Nat.succ_ne_zero, if_false]
      rw [PMF.bind_map]
      calc
        (freeze (B j a) K s).bind
            (iter (step K B T) (r + 1) ∘
              fun z =>
                ⟨j, a, z, r + 1⟩) =
          (freeze (B j a) K s).bind
            (fun z =>
              (iter (freeze (B j a) K) (r + 1) z).map
                (initial T (j + 1))) := by
                  congr 1
                  funext z
                  simpa [Function.comp_def, Nat.add_assoc] using ih z
        _ =
          ((freeze (B j a) K s).bind
              (iter (freeze (B j a) K) (r + 1))).map
            (initial T (j + 1)) := by
              rw [PMF.map_bind]

theorem iter_block
    (K : α → PMF α)
    (B : ℕ → α → α → Prop)
    [∀ j a, DecidablePred (B j a)]
    (T : ℕ → ℕ)
    (j : ℕ) (s : α)
    (hT : 0 < T j) :
    iter (step K B T) (T j) (initial T j s) =
      (iter (freeze (B j s) K) (T j) s).map
        (initial T (j + 1)) := by
  obtain ⟨r, hr⟩ :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hT)
  simpa [initial, hr] using
    (iter_countdown K B T j r s s)

/-- The endpoint kernel of one anchored frozen block. -/
noncomputable def block
    (K : α → PMF α)
    (B : ℕ → α → α → Prop)
    [∀ j a, DecidablePred (B j a)]
    (T : ℕ → ℕ) :
    ℕ → α → PMF α :=
  fun j s => iter (freeze (B j s) K) (T j) s

/-- The flattened micro-step law at the sum of the block horizons is exactly
the heterogeneous block composition, with its next control state retained. -/
theorem iter_sum_map
    (K : α → PMF α)
    (B : ℕ → α → α → Prop)
    [∀ j a, DecidablePred (B j a)]
    (T : ℕ → ℕ)
    (m : ℕ)
    (hT : ∀ j < m, 0 < T j)
    (s : α) :
    iter (step K B T)
        (∑ j ∈ Finset.range m, T j)
        (initial T 0 s) =
      (stagedIter (block K B T) m s).map
        (initial T m) := by
  induction m with
  | zero =>
      rw [show ∑ j ∈ Finset.range 0, T j = 0 by simp]
      simp only [iter, stagedIter, PMF.pure_map]
  | succ m ih =>
      rw [Finset.sum_range_succ, iter_add]
      rw [ih (fun j hj =>
        hT j (hj.trans (Nat.lt_succ_self m)))]
      calc
        ((stagedIter (block K B T) m s).map
            (initial T m)).bind
              (iter (step K B T) (T m)) =
          (stagedIter (block K B T) m s).bind
            (fun z =>
              iter (step K B T) (T m)
                (initial T m z)) := by
                  rw [PMF.bind_map]
                  rfl
        _ =
          (stagedIter (block K B T) m s).bind
            (fun z =>
              (block K B T m z).map
                (initial T (m + 1))) := by
                  congr 1
                  funext z
                  exact iter_block K B T m z
                    (hT m (Nat.lt_succ_self m))
        _ =
          ((stagedIter (block K B T) m s).bind
              (block K B T m)).map
            (initial T (m + 1)) := by
              rw [PMF.map_bind]
        _ =
          (stagedIter (block K B T) (m + 1) s).map
            (initial T (m + 1)) := rfl

/-- A raw chain run for the sum of all block horizons has no more hitting
failure than the corresponding staged process with adaptive self-loops. -/
theorem targetFreeze_failure_le_stagedFreeze
    (A : α → Prop) [DecidablePred A]
    (K : α → PMF α)
    (B : ℕ → α → α → Prop)
    [∀ j a, DecidablePred (B j a)]
    (T : ℕ → ℕ)
    (m : ℕ)
    (hT : ∀ j < m, 0 < T j)
    (s : α) :
    terminalFailureMass
        (iter (freeze A K)
          (∑ j ∈ Finset.range m, T j) s)
        A
      ≤
    terminalFailureMass
        (stagedIter (block K B T) m s)
        A := by
  have hlazy :=
    isLazyProjection_step K B T
  have hcompare :=
    targetFreeze_failure_le_lazy_projection
      A K (step K B T) project hlazy
      (∑ j ∈ Finset.range m, T j)
      (initial T 0 s)
  rw [iter_sum_map K B T m hT s] at hcompare
  rw [terminalFailureMass_map] at hcompare
  simpa using hcompare

end StagedFreezeControl

/-- Freezing first on a smaller target does nothing when the inner kernel is
already frozen on a larger target. -/
theorem freeze_comp_eq_of_subset
    (A B : α → Prop)
    [DecidablePred A] [DecidablePred B]
    (K : α → PMF α)
    (hAB : ∀ s, A s → B s) :
    freeze A (freeze B K) = freeze B K := by
  funext s
  by_cases hA : A s
  · have hB := hAB s hA
    rw [freeze_of_mem s hA, freeze_of_mem s hB]
  · rw [freeze_of_not_mem s hA]

/-- If a success predicate lies inside a frozen checkpoint, its terminal
failure is antitone in the number of available frozen-kernel steps. -/
theorem terminalFailureMass_iter_freeze_antitone_of_subset
    (A B : α → Prop)
    [DecidablePred A] [DecidablePred B]
    (K : α → PMF α)
    (hAB : ∀ s, A s → B s)
    (T U : ℕ) (hTU : T ≤ U) (s : α) :
    terminalFailureMass (iter (freeze B K) U s) A ≤
      terminalFailureMass (iter (freeze B K) T s) A := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hTU
  induction d with
  | zero =>
      simp
  | succ d ih =>
      have hone :
          terminalFailureMass
              (iter (freeze B K) (T + d + 1) s) A ≤
            terminalFailureMass
              (iter (freeze B K) (T + d) s) A := by
        have hstep :=
          targetFreeze_failure_antitone
            A (freeze B K) (T + d) s
        rw [freeze_comp_eq_of_subset A B K hAB] at hstep
        exact hstep
      exact hone.trans (ih (Nat.le_add_right T d))

end

end Tri

#print axioms Tri.StagedFreezeControl.iter_countdown
#print axioms Tri.StagedFreezeControl.iter_sum_map
#print axioms Tri.StagedFreezeControl.targetFreeze_failure_le_stagedFreeze
#print axioms Tri.freeze_comp_eq_of_subset
#print axioms Tri.terminalFailureMass_iter_freeze_antitone_of_subset
