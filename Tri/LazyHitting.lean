/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Freeze

/-!
# Hitting domination for adaptively paused chains

A lifted process may carry counters, stages, and clocks.  If every lifted step,
after projection, is either one step of the physical kernel or a self-loop,
then pausing cannot improve its probability of hitting a projected target
within a fixed horizon.  This is the bridge needed for blockwise stopped
constructions: it does not identify their terminal laws with the physical
chain.
-/

namespace Tri

open scoped ENNReal

variable {α β : Type*}

/-- Terminal mass outside a decidable target. -/
noncomputable def terminalFailureMass
    (p : PMF α) (A : α → Prop) [DecidablePred A] : ℝ≥0∞ :=
  ∑' z, if A z then 0 else p z

theorem terminalFailureMass_eq_expect
    (p : PMF α) (A : α → Prop) [DecidablePred A] :
    terminalFailureMass p A =
      expect p (fun z => (if A z then 0 else 1 : ℝ≥0∞)) := by
  unfold terminalFailureMass expect
  apply tsum_congr
  intro z
  by_cases hz : A z <;> simp [hz]

theorem terminalFailureMass_le_one
    (p : PMF α) (A : α → Prop) [DecidablePred A] :
    terminalFailureMass p A ≤ 1 := by
  calc
    terminalFailureMass p A ≤ ∑' z, p z := by
      unfold terminalFailureMass
      exact ENNReal.tsum_le_tsum fun z => by
        split_ifs <;> simp
    _ = 1 := PMF.tsum_coe p

/-- Enlarging the success predicate can only decrease terminal failure. -/
theorem terminalFailureMass_mono
    (p : PMF α) (A B : α → Prop)
    [DecidablePred A] [DecidablePred B]
    (hBA : ∀ z, B z → A z) :
    terminalFailureMass p A ≤ terminalFailureMass p B := by
  unfold terminalFailureMass
  exact ENNReal.tsum_le_tsum fun z => by
    by_cases hA : A z
    · simp [hA]
    · have hB : ¬ B z := by
        intro hz
        exact hA (hBA z hz)
      simp [hA, hB]

theorem terminalFailureMass_bind
    (p : PMF α) (f : α → PMF β)
    (A : β → Prop) [DecidablePred A] :
    terminalFailureMass (p.bind f) A =
      expect p (fun a => terminalFailureMass (f a) A) := by
  unfold terminalFailureMass expect
  calc
    (∑' z, if A z then 0 else (p.bind f) z) =
        ∑' z, ∑' a, p a * (if A z then 0 else f a z) := by
      apply tsum_congr
      intro z
      rw [PMF.bind_apply]
      by_cases hz : A z <;> simp [hz]
    _ = ∑' a, ∑' z, p a * (if A z then 0 else f a z) :=
      ENNReal.tsum_comm
    _ = ∑' a, p a * ∑' z, (if A z then 0 else f a z) := by
      apply tsum_congr
      intro a
      rw [ENNReal.tsum_mul_left]

theorem terminalFailureMass_map
    (p : PMF β) (π : β → α)
    (A : α → Prop) [DecidablePred A] :
    terminalFailureMass (p.map π) A =
      terminalFailureMass p (fun z => A (π z)) := by
  rw [terminalFailureMass_eq_expect, terminalFailureMass_eq_expect,
    expect_map]

/-- A target state stays fixed under every iterate of the target-frozen
kernel. -/
theorem iter_targetFreeze_of_mem
    (A : α → Prop) [DecidablePred A] (K : α → PMF α)
    (s : α) (hs : A s) :
    ∀ T, iter (freeze A K) T s = PMF.pure s := by
  intro T
  induction T with
  | zero => rfl
  | succ T ih =>
      rw [iter_succ, freeze_of_mem s hs, PMF.pure_bind, ih]

/-- Once the target is frozen, terminal failure is antitone in the available
number of physical steps. -/
theorem targetFreeze_failure_antitone
    (A : α → Prop) [DecidablePred A] (K : α → PMF α)
    (T : ℕ) (s : α) :
    terminalFailureMass
        (iter (freeze A K) (T + 1) s) A ≤
      terminalFailureMass
        (iter (freeze A K) T s) A := by
  rw [iter_succ', terminalFailureMass_bind]
  let V : α → ℝ≥0∞ := fun a =>
    terminalFailureMass (freeze A K a) A
  let I : α → ℝ≥0∞ := fun a => if A a then 0 else 1
  have hVI : ∀ a, V a ≤ I a := by
    intro a
    by_cases ha : A a
    · dsimp only [V, I]
      rw [freeze_of_mem a ha, terminalFailureMass_eq_expect, expect_pure]
    · dsimp only [V, I]
      rw [if_neg ha]
      exact terminalFailureMass_le_one _ A
  calc
    expect (iter (freeze A K) T s)
        (fun a => terminalFailureMass (freeze A K a) A) =
      expect (iter (freeze A K) T s) V := rfl
    _ ≤ expect (iter (freeze A K) T s) I := by
      unfold expect
      exact ENNReal.tsum_le_tsum fun a =>
        mul_le_mul_right (hVI a) _
    _ = terminalFailureMass (iter (freeze A K) T s) A := by
      rw [terminalFailureMass_eq_expect]

/-- An adaptive lifted kernel is lazy over `K` when every projected step is
either a genuine `K` step or a self-loop. -/
def IsLazyProjection
    (K : α → PMF α) (L : β → PMF β) (π : β → α) : Prop :=
  ∀ s, (L s).map π = K (π s) ∨
    (L s).map π = PMF.pure (π s)

/-- A physical chain frozen on a target has no more terminal failure than any
adaptively paused lift with the same horizon.  Equivalently, the unpaused
physical chain has at least the lifted process's hitting probability. -/
theorem targetFreeze_failure_le_lazy_projection
    (A : α → Prop) [DecidablePred A]
    (K : α → PMF α) (L : β → PMF β) (π : β → α)
    (hlazy : IsLazyProjection K L π) :
    ∀ T s,
      terminalFailureMass
          (iter (freeze A K) T (π s)) A ≤
        terminalFailureMass
          (iter L T s) (fun z => A (π z)) := by
  intro T
  induction T with
  | zero =>
      intro s
      rw [terminalFailureMass_eq_expect, terminalFailureMass_eq_expect]
      simp [iter, expect_pure]
  | succ t ih =>
      intro s
      by_cases hsA : A (π s)
      · rw [iter_targetFreeze_of_mem A K (π s) hsA (t + 1),
          terminalFailureMass_eq_expect, expect_pure]
        simp [hsA]
      · rw [iter_succ, iter_succ, freeze_of_not_mem (π s) hsA,
          terminalFailureMass_bind, terminalFailureMass_bind]
        let F : α → ℝ≥0∞ := fun a =>
          terminalFailureMass (iter (freeze A K) t a) A
        let G : β → ℝ≥0∞ := fun z =>
          terminalFailureMass
            (iter L t z) (fun u => A (π u))
        have hFG : ∀ z, F (π z) ≤ G z := by
          intro z
          exact ih z
        have hExpect :
            expect (L s) (fun z => F (π z)) ≤
              expect (L s) G := by
          unfold expect
          exact ENNReal.tsum_le_tsum fun z =>
            mul_le_mul_right (hFG z) _
        rcases hlazy s with hstep | hpure
        · calc
            expect (K (π s))
                (fun a =>
                  terminalFailureMass
                    (iter (freeze A K) t a) A) =
              expect ((L s).map π) F := by
                rw [hstep]
            _ = expect (L s) (fun z => F (π z)) := by
                rw [expect_map]
            _ ≤ expect (L s) G := hExpect
        · have hmono :=
            targetFreeze_failure_antitone A K t (π s)
          rw [iter_succ, freeze_of_not_mem (π s) hsA,
            terminalFailureMass_bind] at hmono
          calc
            expect (K (π s))
                (fun a =>
                  terminalFailureMass
                    (iter (freeze A K) t a) A) ≤
              F (π s) := by
                simpa only [F] using hmono
            _ = expect ((L s).map π) F := by
                rw [hpure, expect_pure]
            _ = expect (L s) (fun z => F (π z)) := by
                rw [expect_map]
            _ ≤ expect (L s) G := hExpect

end Tri

#print axioms Tri.targetFreeze_failure_antitone
#print axioms Tri.targetFreeze_failure_le_lazy_projection
