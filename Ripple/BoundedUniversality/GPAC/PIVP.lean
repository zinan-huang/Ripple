/-
Ripple.BoundedUniversality.GPAC.PIVP
----------------
Re-exports Ripple's PIVP infrastructure and adds K-parameterized
extensions for Route 3 (Q(π)-bounded GPAC Turing universality).

Ripple provides:
  - Ripple.PIVP (d : ℕ) — semantic PIVP with ℝ field and init
  - Ripple.PolyPIVP (d : ℕ) — syntactic PIVP with MvPolynomial ℚ coefficients
  - Ripple.PolyPIVP.evalField — evaluate Q-polynomial vector field at ℝ points
  - Ripple.boundedSurrogate — U_{n,m} = f^m/(1+f^n) and its bounds

Ripple.BoundedUniversality adds:
  - PIVP K — parameterized over coefficient field K for Q vs Q(π)
  - PIVPSemantics, UniformlyBounded
-/

import Ripple.Core.PIVP
import Ripple.Core.Compilation
import Mathlib

namespace Ripple.BoundedUniversality.GPAC

/-- A PIVP parameterized over an arbitrary coefficient field K
embedded in ℝ. Generalizes Ripple's PolyPIVP (which fixes K = ℚ). -/
structure PIVP (K : Type*) [Field K] [Algebra K ℝ] where
  n : ℕ
  vf : Fin n → MvPolynomial (Fin n) K
  init : ℕ → Fin n → K

namespace PIVP

noncomputable def evalVF
    {K : Type*} [Field K] [Algebra K ℝ]
    (P : PIVP K) (x : Fin P.n → ℝ) : Fin P.n → ℝ :=
  fun i => MvPolynomial.eval₂ (algebraMap K ℝ) x (P.vf i)

noncomputable def realInit
    {K : Type*} [Field K] [Algebra K ℝ]
    (P : PIVP K) (w : ℕ) : Fin P.n → ℝ :=
  fun i => algebraMap K ℝ (P.init w i)

/-- Convert a Ripple.PolyPIVP to a Ripple.BoundedUniversality PIVP ℚ. -/
noncomputable def ofPolyPIVP (P : Ripple.PolyPIVP d) : PIVP ℚ where
  n := d
  vf := P.field
  init := fun _ i => P.init i

end PIVP

structure PIVPSemantics
    {K : Type*} [Field K] [Algebra K ℝ]
    (P : PIVP K) where
  traj : ℕ → ℝ → Fin P.n → ℝ
  init_at_zero : ∀ w : ℕ, traj w 0 = P.realInit w
  solves_pivp : Prop

def UniformlyBounded
    {K : Type*} [Field K] [Algebra K ℝ]
    {P : PIVP K} (S : PIVPSemantics P) : Prop :=
  ∃ B : ℝ, 0 < B ∧
    ∀ (w : ℕ) (t : ℝ) (i : Fin P.n), |S.traj w t i| ≤ B

/-! ## Certified (ODE-level) semantics -/

/-- ODE-level solving predicate: trajectory starts at the initial
condition and satisfies the ODE for all t ≥ 0. -/
def SolvesPIVP {K : Type*} [Field K] [Algebra K ℝ]
    (P : PIVP K) (traj : ℕ → ℝ → Fin P.n → ℝ) : Prop :=
  (∀ w, traj w 0 = P.realInit w) ∧
  (∀ w t, 0 ≤ t → HasDerivAt (traj w) (P.evalVF (traj w t)) t)

/-- Certified PIVP semantics: the trajectory provably solves the ODE,
not just an arbitrary Prop witness. -/
structure CertifiedPIVPSemantics {K : Type*} [Field K] [Algebra K ℝ]
    (P : PIVP K) where
  traj : ℕ → ℝ → Fin P.n → ℝ
  solves : SolvesPIVP P traj

/-- Every certified semantics gives a weak semantics, with the
`solves_pivp` field set to the real ODE-solving proposition. -/
def CertifiedPIVPSemantics.toWeak
    {K : Type*} [Field K] [Algebra K ℝ]
    {P : PIVP K} (sem : CertifiedPIVPSemantics P) :
    PIVPSemantics P where
  traj := sem.traj
  init_at_zero := sem.solves.1
  solves_pivp := SolvesPIVP P sem.traj

end Ripple.BoundedUniversality.GPAC
