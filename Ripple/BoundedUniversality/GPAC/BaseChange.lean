/-
Ripple.BoundedUniversality.GPAC.BaseChange
----------------------
Base change of a PIVP along a ring hom `f : ℚ →+* K`.

A PIVP over ℚ embeds into a PIVP over any field K ⊆ ℝ, and ALL the
real-level data (trajectory, ODE solution, readout) transfers
unchanged — because the real vector field `evalVF` factors through
`algebraMap _ ℝ`, and ring homs out of ℚ into ℝ are unique
(`RingHom.ext_rat`), so the diagram ℚ → K → ℝ commutes to ℚ → ℝ.

Consequence: `∃ P : PIVP ℚ, StrongTMSimulates P` implies
`∃ P : PIVP K, StrongTMSimulates P` for every such K. In particular,
the Q(π) BGP universal-simulator existence follows from the rational
fuel construction — the π in Q(π) is not needed for the
undecidability gap.
-/

import Ripple.BoundedUniversality.GPAC.PIVP
import Ripple.BoundedUniversality.GPAC.Readout
import Ripple.BoundedUniversality.GPAC.StrongSemantics

namespace Ripple.BoundedUniversality.GPAC

open Ripple.BoundedUniversality.Core

variable {K : Type*} [Field K] [Algebra K ℝ]

/-- Base change of a rational PIVP along `f : ℚ →+* K`. -/
noncomputable def PIVP.mapField (f : ℚ →+* K) (P : PIVP ℚ) : PIVP K where
  n := P.n
  vf := fun i => (P.vf i).map f
  init := fun w i => f (P.init w i)

/-- The compatibility square ℚ → K → ℝ collapses to ℚ → ℝ:
ring homs out of ℚ are unique. -/
theorem algebraMap_comp_eq (f : ℚ →+* K) :
    (algebraMap K ℝ).comp f = algebraMap ℚ ℝ :=
  RingHom.ext_rat _ _

@[simp] theorem PIVP.mapField_n (f : ℚ →+* K) (P : PIVP ℚ) :
    (P.mapField f).n = P.n := rfl

/-- The real vector field is unchanged by base change. -/
theorem PIVP.mapField_evalVF (f : ℚ →+* K) (P : PIVP ℚ)
    (x : Fin P.n → ℝ) :
    (P.mapField f).evalVF x = P.evalVF x := by
  funext i
  simp only [PIVP.evalVF, PIVP.mapField, MvPolynomial.eval₂_map]
  rw [algebraMap_comp_eq]

/-- The real initial condition is unchanged by base change. -/
theorem PIVP.mapField_realInit (f : ℚ →+* K) (P : PIVP ℚ) (w : ℕ) :
    (P.mapField f).realInit w = P.realInit w := by
  funext i
  simp only [PIVP.realInit, PIVP.mapField, ← RingHom.comp_apply]
  rw [algebraMap_comp_eq]

/-- Strong (HasDerivAt) semantics transfer along base change:
the very same trajectory solves the base-changed ODE. -/
noncomputable def StrongPIVPSemantics.mapField (f : ℚ →+* K) {P : PIVP ℚ}
    (S : StrongPIVPSemantics P) : StrongPIVPSemantics (P.mapField f) where
  traj := S.traj
  init_at_zero := by
    intro w; rw [PIVP.mapField_realInit]; exact S.init_at_zero w
  solves_ode := by
    intro w t ht; rw [PIVP.mapField_evalVF]; exact S.solves_ode w t ht
  traj_continuous := S.traj_continuous

/-- The eventual readout transfers verbatim: same trajectory, same
halt/nonhalt regions, same predicate. -/
def EventualReadout.mapField (f : ℚ →+* K) {P : PIVP ℚ}
    {S : StrongPIVPSemantics P} (R : EventualReadout P S.toWeak) :
    EventualReadout (P.mapField f) (S.mapField f).toWeak where
  Halt := R.Halt
  Nonhalt := R.Nonhalt
  haltCoord := R.haltCoord
  θ := R.θ
  halt_shape := R.halt_shape
  nonhalt_shape := R.nonhalt_shape
  disjoint := R.disjoint
  halts := R.halts
  correct_halt := R.correct_halt
  correct_nonhalt := R.correct_nonhalt

/-- `StrongTMSimulates` transfers along base change. -/
noncomputable def StrongTMSimulates.mapField (f : ℚ →+* K) {P : PIVP ℚ}
    (S : StrongTMSimulates P) : StrongTMSimulates (P.mapField f) where
  sem := S.sem.mapField f
  readout := S.readout.mapField f
  undecidable_halts := S.undecidable_halts

/-- Existence of a rational simulator yields one over any K ⊆ ℝ. -/
theorem strongTMSimulates_baseChange (f : ℚ →+* K)
    (h : ∃ P : PIVP ℚ, Nonempty (StrongTMSimulates P)) :
    ∃ P : PIVP K, Nonempty (StrongTMSimulates P) := by
  obtain ⟨P, ⟨S⟩⟩ := h
  exact ⟨P.mapField f, ⟨S.mapField f⟩⟩

end Ripple.BoundedUniversality.GPAC
