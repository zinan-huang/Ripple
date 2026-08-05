/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.ByzantineAdaptive
import Tri.Compose
import Tri.EscapeSplit

/-!
# Joint history/state law for adaptive Byzantine strategies

`controlledLaw` retains only the terminal physical state.  That is enough for
one-phase expectations, but not for sequential composition: the continuation
chosen by a history-dependent strategy depends on the random transcript
produced by the preceding phase.

Making `(history, state)` the Markov state restores a homogeneous kernel.  Its
iterate has the existing `controlledLaw` as second marginal.  All checkpoint
composition below is therefore ordinary `Reaches.comp`, with the essential
requirement that every continuation estimate be uniform over the entering
history.
-/

namespace Tri.Byzantine

open scoped ENNReal

noncomputable section

variable {n B : ℕ}

/-- Complete state needed to make a history-dependent strategy Markov. -/
abbrev ControlledJointState (n B : ℕ) :=
  History n B × State n B

/-- One adaptive physical interaction, retaining the updated transcript. -/
noncomputable def controlledJointStep
    (σ : Strategy n B) (h3 : 3 ≤ n) :
    ControlledJointState n B → PMF (ControlledJointState n B) :=
  fun q =>
    (adaptiveEventStep σ q.1 q.2 h3).map
      (fun e => (e :: q.1, e.after))

/-- The state marginal of one joint step is the existing adaptive step. -/
theorem controlledJointStep_map_snd
    (σ : Strategy n B) (h3 : 3 ≤ n)
    (q : ControlledJointState n B) :
    (controlledJointStep σ h3 q).map Prod.snd =
      adaptiveStep σ q.1 q.2 h3 := by
  unfold controlledJointStep
  calc
    ((adaptiveEventStep σ q.1 q.2 h3).map
          (fun e => (e :: q.1, e.after))).map Prod.snd =
        (adaptiveEventStep σ q.1 q.2 h3).map Record.after := by
      rw [PMF.map_comp]
      rfl
    _ = adaptiveStep σ q.1 q.2 h3 :=
      adaptiveEventStep_map_after σ q.1 q.2 h3

/-- Exact finite-horizon joint history/state law. -/
noncomputable def controlledJointLaw
    (σ : Strategy n B) (h3 : 3 ≤ n) (T : ℕ) :
    ControlledJointState n B → PMF (ControlledJointState n B) :=
  iter (controlledJointStep σ h3) T

/-- The joint law is, definitionally, the deterministic iterate of the joint
kernel. -/
theorem controlledJointLaw_eq_iter
    (σ : Strategy n B) (h3 : 3 ≤ n)
    (T : ℕ) (q : ControlledJointState n B) :
    controlledJointLaw σ h3 T q =
      iter (controlledJointStep σ h3) T q :=
  rfl

/-- One-step recursion for the joint law. -/
theorem controlledJointLaw_succ
    (σ : Strategy n B) (h3 : 3 ≤ n)
    (T : ℕ) (q : ControlledJointState n B) :
    controlledJointLaw σ h3 (T + 1) q =
      (controlledJointStep σ h3 q).bind
        (controlledJointLaw σ h3 T) :=
  rfl

/-- Deterministic-time splitting for the joint law. -/
theorem controlledJointLaw_add
    (σ : Strategy n B) (h3 : 3 ≤ n)
    (T₁ T₂ : ℕ) (q : ControlledJointState n B) :
    controlledJointLaw σ h3 (T₁ + T₂) q =
      (controlledJointLaw σ h3 T₁ q).bind
        (controlledJointLaw σ h3 T₂) := by
  simpa only [controlledJointLaw] using
    (iter_add (controlledJointStep σ h3) T₁ T₂ q)

/-- Forgetting the transcript recovers exactly the existing `controlledLaw`. -/
theorem controlledJointLaw_map_snd
    (σ : Strategy n B) (h3 : 3 ≤ n) :
    ∀ T (q : ControlledJointState n B),
      (controlledJointLaw σ h3 T q).map Prod.snd =
        controlledLaw σ h3 T q.1 q.2 := by
  intro T
  induction T with
  | zero =>
      rintro ⟨hist, s⟩
      -- At horizon zero both sides are point masses.  `PMF.map` unfolds to a `bind`,
      -- and `PMF.pure_bind` is what actually discharges it (there is no `PMF.map_pure`).
      simp only [controlledJointLaw, controlledLaw, iter_zero, PMF.map,
        PMF.pure_bind, Function.comp]
  | succ T ih =>
      rintro ⟨hist, s⟩
      change
        (((controlledJointStep σ h3 (hist, s)).bind
            (controlledJointLaw σ h3 T)).map Prod.snd) =
          controlledLaw σ h3 (T + 1) hist s
      rw [PMF.map_bind]
      simp_rw [ih]
      rw [controlledLaw]
      unfold controlledJointStep
      rw [PMF.bind_map]
      rfl

/-- Retaining history does not change failure mass for a state predicate. -/
theorem controlledJointLaw_terminalFailureMass
    (σ : Strategy n B) (h3 : 3 ≤ n)
    (T : ℕ) (q : ControlledJointState n B)
    (A : State n B → Prop) [DecidablePred A] :
    terminalFailureMass
        (controlledJointLaw σ h3 T q)
        (fun r => A r.2) =
      terminalFailureMass
        (controlledLaw σ h3 T q.1 q.2) A := by
  calc
    terminalFailureMass
        (controlledJointLaw σ h3 T q)
        (fun r => A r.2) =
      terminalFailureMass
        ((controlledJointLaw σ h3 T q).map Prod.snd) A :=
      (terminalFailureMass_map
        (controlledJointLaw σ h3 T q) Prod.snd A).symm
    _ = terminalFailureMass
          (controlledLaw σ h3 T q.1 q.2) A := by
      rw [controlledJointLaw_map_snd]

/-! ## History-uniform checkpoint composition -/

/-- Compose two stages on the joint kernel.  The second-stage estimate is
explicitly uniform over every history that can enter the checkpoint. -/
theorem controlledJointReaches_comp_uniform
    (σ : Strategy n B) (h3 : 3 ≤ n)
    (P Q R : State n B → Prop)
    [DecidablePred Q] [DecidablePred R]
    {T₁ T₂ : ℕ} {ε₁ ε₂ : ℝ≥0∞}
    (h₁ :
      Reaches (controlledJointStep σ h3) T₁
        (fun q => P q.2)
        (fun q => Q q.2)
        ε₁)
    (h₂ : ∀ hist s, Q s →
      terminalFailureMass
          (controlledJointLaw σ h3 T₂ (hist, s))
          (fun q => R q.2) ≤ ε₂) :
    Reaches (controlledJointStep σ h3) (T₁ + T₂)
      (fun q => P q.2)
      (fun q => R q.2)
      (ε₁ + ε₂) := by
  refine h₁.comp ?_
  rintro ⟨hist, s⟩ hs
  change
    terminalFailureMass
        (controlledJointLaw σ h3 T₂ (hist, s))
        (fun q => R q.2) ≤ ε₂
  exact h₂ hist s hs

/-- State-marginal form of the same contract.  Although the public hypotheses
and conclusion mention the existing `controlledLaw`, the proof composes through
the hidden joint history/state law. -/
theorem controlledLaw_terminalFailure_comp_uniform
    (σ : Strategy n B) (h3 : 3 ≤ n)
    (P Q R : State n B → Prop)
    [DecidablePred Q] [DecidablePred R]
    {T₁ T₂ : ℕ} {ε₁ ε₂ : ℝ≥0∞}
    (h₁ : ∀ hist s, P s →
      terminalFailureMass
          (controlledLaw σ h3 T₁ hist s) Q ≤ ε₁)
    (h₂ : ∀ hist s, Q s →
      terminalFailureMass
          (controlledLaw σ h3 T₂ hist s) R ≤ ε₂) :
    ∀ hist s, P s →
      terminalFailureMass
          (controlledLaw σ h3 (T₁ + T₂) hist s) R ≤
        ε₁ + ε₂ := by
  have hreach₁ :
      Reaches (controlledJointStep σ h3) T₁
        (fun q => P q.2)
        (fun q => Q q.2)
        ε₁ := by
    rintro ⟨hist, s⟩ hs
    change
      terminalFailureMass
          (controlledJointLaw σ h3 T₁ (hist, s))
          (fun q => Q q.2) ≤ ε₁
    calc
      terminalFailureMass
          (controlledJointLaw σ h3 T₁ (hist, s))
          (fun q => Q q.2) =
        terminalFailureMass
          (controlledLaw σ h3 T₁ hist s) Q :=
        controlledJointLaw_terminalFailureMass
          σ h3 T₁ (hist, s) Q
      _ ≤ ε₁ := h₁ hist s hs

  have hreach₂ :
      Reaches (controlledJointStep σ h3) T₂
        (fun q => Q q.2)
        (fun q => R q.2)
        ε₂ := by
    rintro ⟨hist, s⟩ hs
    change
      terminalFailureMass
          (controlledJointLaw σ h3 T₂ (hist, s))
          (fun q => R q.2) ≤ ε₂
    calc
      terminalFailureMass
          (controlledJointLaw σ h3 T₂ (hist, s))
          (fun q => R q.2) =
        terminalFailureMass
          (controlledLaw σ h3 T₂ hist s) R :=
        controlledJointLaw_terminalFailureMass
          σ h3 T₂ (hist, s) R
      _ ≤ ε₂ := h₂ hist s hs

  have hreach := hreach₁.comp hreach₂
  intro hist s hs
  have hjoint := hreach (hist, s) hs
  change
    terminalFailureMass
        (controlledJointLaw σ h3 (T₁ + T₂) (hist, s))
        (fun q => R q.2) ≤ ε₁ + ε₂ at hjoint
  calc
    terminalFailureMass
        (controlledLaw σ h3 (T₁ + T₂) hist s) R =
      terminalFailureMass
        (controlledJointLaw σ h3 (T₁ + T₂) (hist, s))
        (fun q => R q.2) :=
      (controlledJointLaw_terminalFailureMass
        σ h3 (T₁ + T₂) (hist, s) R).symm
    _ ≤ ε₁ + ε₂ := hjoint

end

end Tri.Byzantine
