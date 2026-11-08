/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Outcome-aware reachable phase composition

Linear phase chains are the wrong interface for protocols that may stabilize early.
This file lifts a reachable phase with an absorbing `Done` outcome.  Once `Done`
holds, the lifted phase succeeds with zero additional failure; otherwise it executes
the original phase.  The resulting chain law asks each active postcondition to
produce either `Done` or the next active precondition.
-/

import Ripple.PopulationProtocol.ExactMajority.Probability.ReachablePhaseConvergence
import Ripple.PopulationProtocol.ExactMajority.Probability.ExpectedHitting

namespace Ripple.PopulationProtocol.ExactMajority
namespace PhaseConvergenceWR

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

attribute [local instance] Classical.propDecidable

noncomputable section

/-- Add an absorbing successful outcome to a reachable phase.

`hDoneClosed` is the honest one-step absorption statement.  Its finite-time form is
derived by `pow_compl_inv_eq_zero_eh`; no phase-window closure is assumed. -/
def withAbsorbingDone
    (P : Protocol Λ) (init : Config Λ)
    (Done : Config Λ → Prop)
    (hDoneClosed : ∀ x, Done x →
      P.transitionKernel x {y | ¬ Done y} = 0)
    (phase : PhaseConvergenceWR P init) :
    PhaseConvergenceWR P init where
  Pre := fun x => Done x ∨ phase.Pre x
  Post := fun x => Done x ∨ phase.Post x
  t := phase.t
  ε := phase.ε
  convergence := by
    intro x hreach hx
    rcases hx with hDone | hPre
    · have hpow :
          (P.transitionKernel ^ phase.t) x {y | ¬ Done y} = 0 :=
        pow_compl_inv_eq_zero_eh P.transitionKernel Done hDoneClosed
          x hDone phase.t
      calc
        (P.transitionKernel ^ phase.t) x
            {y | ¬ (Done y ∨ phase.Post y)}
            ≤ (P.transitionKernel ^ phase.t) x {y | ¬ Done y} := by
              apply measure_mono
              intro y hy
              exact fun hDy => hy (Or.inl hDy)
        _ = 0 := hpow
        _ ≤ (phase.ε : ℝ≥0∞) := bot_le
    · calc
        (P.transitionKernel ^ phase.t) x
            {y | ¬ (Done y ∨ phase.Post y)}
            ≤ (P.transitionKernel ^ phase.t) x {y | ¬ phase.Post y} := by
              apply measure_mono
              intro y hy
              exact fun hPy => hy (Or.inr hPy)
        _ ≤ (phase.ε : ℝ≥0∞) := phase.convergence x hreach hPre

@[simp] theorem withAbsorbingDone_Pre
    (P : Protocol Λ) (init : Config Λ)
    (Done : Config Λ → Prop)
    (hDoneClosed : ∀ x, Done x →
      P.transitionKernel x {y | ¬ Done y} = 0)
    (phase : PhaseConvergenceWR P init) (x : Config Λ) :
    (withAbsorbingDone P init Done hDoneClosed phase).Pre x =
      (Done x ∨ phase.Pre x) := rfl

@[simp] theorem withAbsorbingDone_Post
    (P : Protocol Λ) (init : Config Λ)
    (Done : Config Λ → Prop)
    (hDoneClosed : ∀ x, Done x →
      P.transitionKernel x {y | ¬ Done y} = 0)
    (phase : PhaseConvergenceWR P init) (x : Config Λ) :
    (withAbsorbingDone P init Done hDoneClosed phase).Post x =
      (Done x ∨ phase.Post x) := rfl

@[simp] theorem withAbsorbingDone_t
    (P : Protocol Λ) (init : Config Λ)
    (Done : Config Λ → Prop)
    (hDoneClosed : ∀ x, Done x →
      P.transitionKernel x {y | ¬ Done y} = 0)
    (phase : PhaseConvergenceWR P init) :
    (withAbsorbingDone P init Done hDoneClosed phase).t = phase.t := rfl

@[simp] theorem withAbsorbingDone_epsilon
    (P : Protocol Λ) (init : Config Λ)
    (Done : Config Λ → Prop)
    (hDoneClosed : ∀ x, Done x →
      P.transitionKernel x {y | ¬ Done y} = 0)
    (phase : PhaseConvergenceWR P init) :
    (withAbsorbingDone P init Done hDoneClosed phase).ε = phase.ε := rfl

/-- Outcome-aware bridge: an active phase may either stabilize or enter the next
active phase.  A previously stabilized branch is threaded automatically. -/
theorem withAbsorbingDone_chain
    (P : Protocol Λ) (init : Config Λ)
    (Done : Config Λ → Prop)
    (hDoneClosed : ∀ x, Done x →
      P.transitionKernel x {y | ¬ Done y} = 0)
    (phase₁ phase₂ : PhaseConvergenceWR P init)
    (hActive : ∀ x, P.Reachable init x →
      phase₁.Post x → Done x ∨ phase₂.Pre x) :
    ∀ x, P.Reachable init x →
      (withAbsorbingDone P init Done hDoneClosed phase₁).Post x →
      (withAbsorbingDone P init Done hDoneClosed phase₂).Pre x := by
  intro x hreach hx
  rcases hx with hDone | hPost
  · exact Or.inl hDone
  · exact hActive x hreach hPost

#print axioms withAbsorbingDone
#print axioms withAbsorbingDone_chain

end
end PhaseConvergenceWR
end Ripple.PopulationProtocol.ExactMajority
