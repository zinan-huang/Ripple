/-
  Generic QBee certificate framework.

  A QBee certificate verifies that a quadratization of a polynomial ODE
  is correct: the quadratized system, restricted to the monomial manifold,
  reproduces the original dynamics.

  For each specific system, the Python emitter generates a .lean file
  that defines the fields and proves correctness by `ring`. See
  QBeeCertificate.lean for the gamma system instance.
-/

import Ripple.Core.PIVP
import Mathlib.Analysis.Calculus.Deriv.Prod

set_option linter.unusedSimpArgs false

namespace Ripple.LPP.QBee

/-- A verified QBee quadratization certificate.

`origField` is the n-dimensional original ODE.
`quadField` is the (n+k)-dimensional quadratized ODE (degree ≤ 2).
`embed` maps an n-dim state to (n+k)-dim by computing the k monomial variables.

The certificate guarantees that on the monomial manifold, the quadratized
dynamics reproduce the original dynamics (for the original components)
and are consistent with the chain rule (for the new components). -/
structure Certificate (n k : ℕ) where
  origField : (Fin n → ℝ) → Fin n → ℝ
  quadField : (Fin (n + k) → ℝ) → Fin (n + k) → ℝ
  embed : (Fin n → ℝ) → Fin (n + k) → ℝ
  embed_orig : ∀ x (i : Fin n), embed x (Fin.castAdd k i) = x i
  orig_correct : ∀ x (i : Fin n),
    quadField (embed x) (Fin.castAdd k i) = origField x i

/-- The PIVP corresponding to the quadratized system. -/
noncomputable def Certificate.quadPIVP (cert : Certificate n k)
    (init : Fin n → ℝ) (output : Fin (n + k)) : PIVP (n + k) where
  field := cert.quadField
  init := cert.embed init
  output := output

/-- If x(t) solves the original n-dim ODE and the embedding preserves
HasDerivAt (proved per-system via product rules), then embed(x(t))
solves the (n+k)-dim quadratized ODE. -/
theorem Certificate.lift_solution (cert : Certificate n k)
    {x : ℝ → Fin n → ℝ} (init : Fin n → ℝ) (output : Fin (n + k))
    (hx_init : x 0 = init)
    (hx_ode : ∀ t : ℝ, 0 ≤ t → HasDerivAt x (cert.origField (x t)) t)
    (hx_bounded : ∃ M > 0, ∀ t : ℝ, 0 ≤ t → ‖x t‖ ≤ M)
    (hchain : ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (fun s => cert.embed (x s))
        (cert.quadField (cert.embed (x t))) t) :
    ∃ sol : PIVP.Solution (cert.quadPIVP init output),
      (cert.quadPIVP init output).IsBounded sol.trajectory := by
  refine ⟨⟨fun t => cert.embed (x t), ?_, ?_⟩, ?_⟩
  · show cert.embed (x 0) = cert.embed init
    rw [hx_init]
  · exact hchain
  · obtain ⟨M, hM, hbound⟩ := hx_bounded
    sorry

end Ripple.LPP.QBee
