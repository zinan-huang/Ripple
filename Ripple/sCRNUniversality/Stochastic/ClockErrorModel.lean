/-
  Clock error model for the SCWB CTM construction.

  The SCWB paper's ONLY source of error per CTM microstep is premature
  state transition initiation: the clock module's "tick" fires before
  the current microstep's memory operations complete.

  With the cascade shift (fully deterministic, no race), the error model
  simplifies to: at each of the 4 microsteps per CTM step, the probability
  that the clock ticks prematurely is bounded by some ε_step.

  The clock module guarantees (Lemma A.4, A.8):
    ε_step = O(1 / #A^(l-1))
  where #A is the initial count of accuracy species and l is the clock
  chain length.

  This module defines the error model abstractly: given a per-step
  error bound ε, derive the n-step cumulative error bound.
-/
import Ripple.sCRNUniversality.Stochastic.JumpPathLaw

namespace Ripple.sCRNUniversality.Stochastic

universe u v w

structure ClockBoundedLaw {S : Type u} [Fintype S]
    (N : Network.{u, v} S) (Omega : Type w)
    extends JumpPathLaw N Omega where
  microstepsPerStep : Nat
  perMicrostepError : ENNReal
  microstepBound :
    forall (step : Nat) (microstep : Fin microstepsPerStep)
      (intended : N.I)
      (z : State S)
      (hstate : forall omega, (path omega).state
        (step * microstepsPerStep + microstep.val) = z)
      (hEnabled : N.EnabledAt z intended),
    prob.Pr {omega | (path omega).fired
        (step * microstepsPerStep + microstep.val) ≠ some intended} ≤
      perMicrostepError

namespace ClockBoundedLaw

variable {S : Type u} [Fintype S]
variable {N : Network.{u, v} S} {Omega : Type w}

theorem nStepErrorBound (L : ClockBoundedLaw N Omega)
    (nSteps : Nat) :
    nSteps * L.microstepsPerStep * L.perMicrostepError =
      (nSteps * L.microstepsPerStep : Nat) * L.perMicrostepError := by
  push_cast; ring

noncomputable def nStepFailureBound (L : ClockBoundedLaw N Omega)
    (nSteps : Nat) : ENNReal :=
  (nSteps * L.microstepsPerStep : Nat) * L.perMicrostepError

theorem nStepFailureBound_linear (L : ClockBoundedLaw N Omega) :
    L.nStepFailureBound 1 = L.microstepsPerStep * L.perMicrostepError := by
  simp [nStepFailureBound, Nat.one_mul]

theorem fourPhase_nStepBound (L : ClockBoundedLaw N Omega)
    (hMicrosteps : L.microstepsPerStep = 4)
    (nSteps : Nat) :
    L.nStepFailureBound nSteps = (4 * nSteps : Nat) * L.perMicrostepError := by
  simp [nStepFailureBound, hMicrosteps]; ring

theorem error_le_target (L : ClockBoundedLaw N Omega)
    (hMicrosteps : L.microstepsPerStep = 4)
    (nSteps : Nat)
    (δ : ENNReal)
    (hError : L.perMicrostepError ≤ δ / (4 * nSteps : Nat)) :
    L.nStepFailureBound nSteps ≤ δ := by
  unfold nStepFailureBound
  rw [hMicrosteps]
  calc (nSteps * 4 : Nat) * L.perMicrostepError
      ≤ (nSteps * 4 : Nat) * (δ / (4 * nSteps : Nat)) :=
        mul_le_mul_left' hError _
      _ = (4 * nSteps : Nat) * (δ / (4 * nSteps : Nat)) := by
        congr 1; push_cast; ring
      _ ≤ δ := ENNReal.mul_div_le

end ClockBoundedLaw

end Ripple.sCRNUniversality.Stochastic
