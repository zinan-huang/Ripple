/-
Ripple.BoundedUniversality.GPAC.StrongSemantics
----------------------------
Strong PIVP semantics with HasDerivAt, enabling the chain rule
proof for bounded surrogate compilation.
-/

import Ripple.BoundedUniversality.GPAC.Readout
import Ripple.BoundedUniversality.Core.Computability

namespace Ripple.BoundedUniversality.GPAC

open Ripple.BoundedUniversality.Core

structure StrongPIVPSemantics
    {K : Type*} [Field K] [Algebra K ℝ]
    (P : PIVP K) where
  traj : ℕ → ℝ → Fin P.n → ℝ
  init_at_zero : ∀ w : ℕ, traj w 0 = P.realInit w
  solves_ode : ∀ (w : ℕ) (t : ℝ), 0 ≤ t →
    HasDerivAt (traj w) (P.evalVF (traj w t)) t
  traj_continuous : ∀ w, Continuous (traj w)

def StrongPIVPSemantics.toWeak
    {K : Type*} [Field K] [Algebra K ℝ]
    {P : PIVP K} (S : StrongPIVPSemantics P) :
    PIVPSemantics P where
  traj := S.traj
  init_at_zero := S.init_at_zero
  solves_pivp := ∀ (w : ℕ) (t : ℝ), 0 ≤ t →
    HasDerivAt (S.traj w) (P.evalVF (S.traj w t)) t

structure StrongTMSimulates
    {K : Type*} [Field K] [Algebra K ℝ]
    (P : PIVP K) where
  sem : StrongPIVPSemantics P
  readout : EventualReadout P sem.toWeak
  undecidable_halts : NoComputableBoolDecider readout.halts

def StrongTMSimulates.toWeak
    {K : Type*} [Field K] [Algebra K ℝ]
    {P : PIVP K} (S : StrongTMSimulates P) :
    TMSimulates P where
  sem := S.sem.toWeak
  readout := S.readout
  undecidable_halts := S.undecidable_halts

/-! ## Conversion to certified semantics -/

/-- `StrongPIVPSemantics` already carries `HasDerivAt`, so it
converts directly to `CertifiedPIVPSemantics` (dropping `traj_continuous`). -/
def StrongPIVPSemantics.toCertified
    {K : Type*} [Field K] [Algebra K ℝ]
    {P : PIVP K} (S : StrongPIVPSemantics P) :
    CertifiedPIVPSemantics P where
  traj := S.traj
  solves := ⟨S.init_at_zero, S.solves_ode⟩

/-- The trajectory from `toCertified.toWeak` is the same as from `toWeak`. -/
theorem StrongPIVPSemantics.toCertified_toWeak_traj
    {K : Type*} [Field K] [Algebra K ℝ]
    {P : PIVP K} (S : StrongPIVPSemantics P) :
    S.toCertified.toWeak.traj = S.toWeak.traj :=
  rfl

end Ripple.BoundedUniversality.GPAC
