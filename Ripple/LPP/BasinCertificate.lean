/-
  Ripple.LPP.BasinCertificate — Bridge from LPP Incremental Contraction to OneSidedContractingOn

  The existing LPP §3 cor:incremental-contraction provides exponential
  stability certificates for the x-side drift. This file bridges that
  structure to the `OneSidedContractingOn` predicate used by the
  stable Gronwall machinery (StableGronwall.lean).
-/

import Ripple.Analysis.StableGronwall
import Ripple.LPP.Defs

namespace Ripple.LPP

open Ripple.Analysis

/-- An incremental contraction certificate on the x-side:
    the drift b satisfies ⟨x - y, b(x) - b(y)⟩ ≤ -η' · ‖x - y‖²
    on a ball B around the equilibrium.

    This matches the form of LPP §3 cor:incremental-contraction. -/
structure IncrementalContractionCertificate
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (b : E → E) (B : Set E) (η' : ℝ) : Prop where
  eta_pos : 0 < η'
  contraction : ∀ x ∈ B, ∀ y ∈ B,
    @inner ℝ E _ (x - y) (b x - b y) ≤ -η' * ‖x - y‖ ^ 2

/-- Bridge: an IncrementalContractionCertificate directly yields
    OneSidedContractingOn on the same set with the same rate. -/
theorem incremental_contraction_to_oneSidedContractingOn
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {b : E → E} {B : Set E} {η' : ℝ}
    (hcert : IncrementalContractionCertificate b B η') :
    OneSidedContractingOn b B η' := by
  intro x y hx hy
  exact hcert.contraction x hx y hy

end Ripple.LPP
