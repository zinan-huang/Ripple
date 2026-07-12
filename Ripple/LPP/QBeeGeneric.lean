/-
  Generic QBee certificate framework.

  A QBee certificate is the algebraic payload emitted by the Python
  quadratization pipeline.  For a concrete polynomial ODE, the generated Lean
  file defines the original field, the quadratized field, the monomial
  embedding, and the chain-rule right-hand sides for the new variables.  The
  correctness fields below are intended to be discharged by `simp` and `ring`.
-/

import Ripple.Core.PIVP

set_option linter.unusedSimpArgs false

namespace Ripple.LPP.QBee

/-- A reusable algebraic QBee quadratization certificate.

`n` is the original dimension and `k` is the number of new QBee variables.
The field `chainRule x j` is the precomputed derivative of the `j`-th new
embedding component along the original vector field:

`d/dt embed(x(t))_{n+j} = chainRule (x(t)) j`

whenever `x'(t) = origField (x(t))`.  The generated certificate proves that
the quadratized field agrees with both the original field and these chain-rule
right-hand sides on the monomial manifold. -/
structure QBeeCertificate (n k : ℕ) where
  /-- Original ODE vector field. -/
  origField : (Fin n → ℝ) → Fin n → ℝ
  /-- QBee quadratized vector field. -/
  quadField : (Fin (n + k) → ℝ) → Fin (n + k) → ℝ
  /-- Monomial embedding from original variables to original plus new variables. -/
  embed : (Fin n → ℝ) → Fin (n + k) → ℝ
  /-- Explicit chain-rule RHS for the new variables along `origField`. -/
  chainRule : (Fin n → ℝ) → Fin k → ℝ
  /-- The first `n` embedded coordinates are the original state. -/
  embed_orig : ∀ x (i : Fin n), embed x (Fin.castAdd k i) = x i
  /-- Original components are preserved on the monomial manifold. -/
  orig_correct : ∀ x (i : Fin n),
    quadField (embed x) (Fin.castAdd k i) = origField x i
  /-- New components agree with the emitted chain-rule RHS on the monomial manifold. -/
  chain_correct : ∀ x (j : Fin k),
    quadField (embed x) (Fin.natAdd n j) = chainRule x j

/-- Backwards-compatible short name for QBee certificates. -/
abbrev Certificate (n k : ℕ) := QBeeCertificate n k

namespace QBeeCertificate

variable {n k : ℕ} (cert : QBeeCertificate n k)

/-- The original PIVP carried by a QBee certificate. -/
noncomputable def origPIVP (init : Fin n → ℝ) (output : Fin n) : PIVP n where
  field := cert.origField
  init := init
  output := output

/-- The quadratized PIVP carried by a QBee certificate. -/
noncomputable def quadPIVP (init : Fin n → ℝ) (output : Fin (n + k)) : PIVP (n + k) where
  field := cert.quadField
  init := cert.embed init
  output := output

/-- Original-component correctness, restated as a theorem for dot notation. -/
theorem quad_orig_component (x : Fin n → ℝ) (i : Fin n) :
    cert.quadField (cert.embed x) (Fin.castAdd k i) = cert.origField x i :=
  cert.orig_correct x i

/-- New-component chain-rule correctness, restated as a theorem for dot notation. -/
theorem quad_new_component (x : Fin n → ℝ) (j : Fin k) :
    cert.quadField (cert.embed x) (Fin.natAdd n j) = cert.chainRule x j :=
  cert.chain_correct x j

end QBeeCertificate

end Ripple.LPP.QBee
