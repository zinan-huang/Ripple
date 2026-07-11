/-
Ripple.BoundedUniversality.GPAC.Readout
-------------------
Eventual readout, TM simulation, and bounded TM simulation semantics.
-/

import Ripple.BoundedUniversality.GPAC.PIVP
import Ripple.BoundedUniversality.Core.Computability

namespace Ripple.BoundedUniversality.GPAC

open Ripple.BoundedUniversality.Core

structure EventualReadout
    {K : Type*} [Field K] [Algebra K ℝ]
    (P : PIVP K) (S : PIVPSemantics P) where
  Halt : Set (Fin P.n → ℝ)
  Nonhalt : Set (Fin P.n → ℝ)
  haltCoord : Fin P.n
  θ : ℝ
  halt_shape : Halt = {y | y haltCoord > θ}
  nonhalt_shape : Nonhalt = {y | y haltCoord < θ}
  disjoint : Disjoint Halt Nonhalt
  halts : ℕ → Prop
  correct_halt :
    ∀ w : ℕ, halts w ↔ ∃ T : ℝ, ∀ t ≥ T, S.traj w t ∈ Halt
  correct_nonhalt :
    ∀ w : ℕ, ¬ halts w ↔ ∃ T : ℝ, ∀ t ≥ T, S.traj w t ∈ Nonhalt

structure TMSimulates
    {K : Type*} [Field K] [Algebra K ℝ]
    (P : PIVP K) where
  sem : PIVPSemantics P
  readout : EventualReadout P sem
  undecidable_halts : NoComputableBoolDecider readout.halts

structure BoundedTMSimulates
    {K : Type*} [Field K] [Algebra K ℝ]
    (P : PIVP K) where
  sem : PIVPSemantics P
  bounded : UniformlyBounded sem
  readout : EventualReadout P sem
  undecidable_halts : NoComputableBoolDecider readout.halts

def BoundedTMSimulates.toTMSimulates
    {K : Type*} [Field K] [Algebra K ℝ]
    {P : PIVP K} (h : BoundedTMSimulates P) :
    TMSimulates P :=
  ⟨h.sem, h.readout, h.undecidable_halts⟩

/-! ## Certified bounded TM simulation -/

/-- Certified bounded TM simulation: uses `CertifiedPIVPSemantics`
so the trajectory provably solves the ODE. -/
structure CertifiedBoundedTMSimulates {K : Type*} [Field K] [Algebra K ℝ]
    (P : PIVP K) where
  sem : CertifiedPIVPSemantics P
  bounded : UniformlyBounded sem.toWeak
  readout : EventualReadout P sem.toWeak
  undecidable_halts : NoComputableBoolDecider readout.halts

/-- Every certified bounded TM simulation gives a (weak) bounded
TM simulation via `CertifiedPIVPSemantics.toWeak`. -/
def CertifiedBoundedTMSimulates.toWeak
    {K : Type*} [Field K] [Algebra K ℝ]
    {P : PIVP K} (h : CertifiedBoundedTMSimulates P) :
    BoundedTMSimulates P where
  sem := h.sem.toWeak
  bounded := h.bounded
  readout := h.readout
  undecidable_halts := h.undecidable_halts

end Ripple.BoundedUniversality.GPAC
