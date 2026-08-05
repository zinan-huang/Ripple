/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.StagedLazyHitting
import Tri.Lemma18To19

/-!
# Composing a first hit with an absorbing endpoint

A first-hitting estimate need not place the ordinary chain in the intermediate
set at a prescribed time.  The correct composition freezes at the first hit,
runs the continuation immediately, and compares that adaptively paused process
with the unpaused physical chain.  Extra physical steps can only help once the
final target is absorbing.
-/

namespace Tri

open scoped ENNReal

noncomputable section

variable {α : Type*}

/-- Freezing does not alter a kernel on a set that was already absorbing. -/
theorem freeze_eq_of_absorbing
    (K : α → PMF α) (R : α → Prop) [DecidablePred R]
    (habs : ∀ s, R s → K s = PMF.pure s) :
    freeze R K = K := by
  funext s
  by_cases hs : R s
  · rw [freeze_of_mem s hs, habs s hs]
  · rw [freeze_of_not_mem s hs]

/-- A finite first-hit estimate composes with an ordinary continuation to an
absorbing target.  The first stage may hit `P` at any time up to `T₁`; the
continuation starts at that first hit, and the unpaused chain has at least
`T₂` further physical steps before the displayed total horizon. -/
theorem Reaches.comp_of_frozen_hit
    (K : α → PMF α)
    {A P R : α → Prop}
    [DecidablePred P] [DecidablePred R]
    {T₁ T₂ : ℕ} {ε₁ ε₂ : ℝ≥0∞}
    (hT₁ : 0 < T₁) (hT₂ : 0 < T₂)
    (hhit :
      ∀ s, A s →
        terminalFailureMass
          (iter (freeze P K) T₁ s) P ≤ ε₁)
    (hpost : Reaches K T₂ P R ε₂)
    (habs : ∀ s, R s → K s = PMF.pure s) :
    Reaches K (T₁ + T₂) A R (ε₁ + ε₂) := by
  let B : ℕ → α → α → Prop
    | 0, _, z => P z
    | _ + 1, _, z => R z
  let clock : ℕ → ℕ
    | 0 => T₁
    | _ + 1 => T₂
  letI : ∀ j a, DecidablePred (B j a) := by
    intro j a z
    cases j with
    | zero =>
        exact inferInstanceAs (Decidable (P z))
    | succ j =>
        exact inferInstanceAs (Decidable (R z))
  have hclock :
      ∀ j < 2, 0 < clock j := by
    intro j hj
    interval_cases j <;>
      simp only [clock] <;> assumption
  have hfreeze :
      freeze R K = K :=
    freeze_eq_of_absorbing K R habs
  intro s hs
  have hcompare :=
    StagedFreezeControl.targetFreeze_failure_le_stagedFreeze
      R K B clock 2 hclock s
  have hstaged :
      terminalFailureMass
          ((iter (freeze P K) T₁ s).bind
            (fun z => iter (freeze R K) T₂ z))
          R
        ≤ ε₁ + ε₂ := by
    apply terminalFailureMass_bind_le_add_of_support
      (iter (freeze P K) T₁ s)
      (fun z => iter (freeze R K) T₂ z)
      P R ε₁ ε₂
    · exact hhit s hs
    · intro z hz hP
      rw [hfreeze]
      exact hpost z hP
  rw [hfreeze] at hcompare
  have hsum :
      (∑ j ∈ Finset.range 2, clock j) = T₁ + T₂ := by
    simp [clock, Finset.sum_range_succ]
  have hblock0 :
      StagedFreezeControl.block K B clock 0 =
        fun z => iter (freeze P K) T₁ z := by
    funext z
    simp [StagedFreezeControl.block, B, clock]
  have hblock1 :
      StagedFreezeControl.block K B clock 1 =
        fun z => iter K T₂ z := by
    funext z
    simp [StagedFreezeControl.block, B, clock, hfreeze]
  simp only [stagedIter, PMF.pure_bind] at hcompare
  rw [hsum, hblock0, hblock1] at hcompare
  have hcompare' :
      terminalFailureMass
          (iter K (T₁ + T₂) s) R
        ≤
      terminalFailureMass
          ((iter (freeze P K) T₁ s).bind
            (fun z => iter K T₂ z))
          R := by
    simpa [stagedIter] using hcompare
  rw [hfreeze] at hstaged
  exact hcompare'.trans hstaged

end

end Tri

#print axioms Tri.freeze_eq_of_absorbing
#print axioms Tri.Reaches.comp_of_frozen_hit
