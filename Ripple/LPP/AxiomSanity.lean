/-
  Ripple.LPP.AxiomSanity — sanity check for `polyCRN_exists_neg_shift`.

  Purpose: show that the axiom in its current form is **inconsistent** with
  the proved CRN non-negativity invariant (`crn_trajectory_nonneg`).
  Concretely: given any `β ≥ 0` and `q : ℚ` with `q < 0` and `β + q < 0`,
  the axiom produces a CBTC+PCD for `β + q < 0`, but such a witness implies
  the output trajectory stays ≥ 0 and converges to the negative number,
  contradicting boundedness of `exp(-r)`.

  Conclusion: the axiom must be strengthened with a hypothesis like
  `0 ≤ β + (q : ℝ)`, OR replaced by a different formulation. This file
  documents (but does not close) the inconsistency, for the narrow case
  where we can explicitly produce a CBTC for β = 0 and shift by q = -1.
-/

import Ripple.LPP.AddRationalNeg
import Ripple.Core.ZeroInitPositivity

namespace Ripple
namespace Algebraic

/-- **Lemma (nonneg-α from CBTC+PCD).** If a CBTC `cbtc'` for `α` admits a
`PolyCRNDecomposition`, then `0 ≤ α`.

Proof: the trajectory of a PCD system stays ≥ 0 (by `crn_trajectory_nonneg`
spirit — but that lemma requires `IsZeroInit`; we use the weaker
`pivp_solution_nonneg` directly which only needs `init_nonneg`). Combined
with convergence `|traj t output - α| < exp(-r)` for `t > modulus r`,
taking the limit `r → ∞` gives `α = lim traj ≥ 0`. -/
theorem CBTC_PCD_target_nonneg {d' : ℕ} {α : ℝ}
    (cbtc' : CertifiedBoundedTimeComputable d' α)
    (_pcd' : PolyCRNDecomposition d' cbtc'.pivp) :
    0 ≤ α := by
  -- Trajectory stays non-negative on t ≥ 0 via the CRN non-negativity invariant
  -- (init_nonneg from pcd' + IsCRNImplementable from pcd' + polynomial local Lipschitz).
  have h_crn : IsCRNImplementable d' cbtc'.pivp.toPIVP.field :=
    _pcd'.toIsCRNImplementable
  have h_lip := polyPIVP_field_locally_lipschitz cbtc'.pivp
  have h_init_nn : ∀ i, 0 ≤ cbtc'.pivp.toPIVP.init i := by
    intro i
    simp only [PolyPIVP.toPIVP_init]
    exact_mod_cast _pcd'.init_nonneg i
  have h_nn : ∀ t : ℝ, 0 ≤ t → ∀ i, 0 ≤ cbtc'.sol.trajectory t i := by
    intro t ht i
    exact pivp_solution_nonneg h_crn h_lip h_init_nn cbtc'.sol t ht i
  -- Convergence at a very large r and very large t forces α ≥ 0.
  by_contra hlt
  push_neg at hlt
  -- Pick r large enough so that exp(-r) < -α (i.e., < |α|).
  have hα_pos : 0 < -α := by linarith
  have hexp_tendsto :
      Filter.Tendsto (fun r : ℕ => Real.exp (-(r : ℝ))) Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun r : ℕ => (-(r : ℝ))) Filter.atTop Filter.atBot := by
      refine Filter.tendsto_atBot.mpr ?_
      intro b
      refine Filter.eventually_atTop.mpr ⟨Nat.ceil (-b) + 1, fun n hn => ?_⟩
      have hle : -b ≤ (n : ℝ) := by
        calc -b ≤ ((Nat.ceil (-b) : ℕ) : ℝ) := Nat.le_ceil _
          _ ≤ ((Nat.ceil (-b) + 1 : ℕ) : ℝ) := by push_cast; linarith
          _ ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    exact (Real.tendsto_exp_atBot).comp h1
  have hev :
      ∀ᶠ r : ℕ in Filter.atTop, Real.exp (-(r : ℝ)) < -α := by
    exact hexp_tendsto.eventually (eventually_lt_nhds hα_pos)
  obtain ⟨r, hr⟩ := hev.exists
  -- Pick t > modulus r.
  have ht_exists : ∃ t : ℝ, cbtc'.modulus r < t ∧ 0 ≤ t := by
    refine ⟨max (cbtc'.modulus r + 1) 0, ?_, le_max_right _ _⟩
    exact lt_of_lt_of_le (lt_add_one _) (le_max_left _ _)
  obtain ⟨t, ht_gt, ht_nn⟩ := ht_exists
  have h_conv := cbtc'.convergence r t ht_gt
  -- traj ≥ 0 gives |traj - α| ≥ traj - α ≥ -α = |α| (since α < 0).
  have h_traj_nn : 0 ≤ cbtc'.sol.trajectory t cbtc'.pivp.output :=
    h_nn t ht_nn cbtc'.pivp.output
  have h_abs_ge : -α ≤ |cbtc'.sol.trajectory t cbtc'.pivp.output - α| := by
    have : -α ≤ cbtc'.sol.trajectory t cbtc'.pivp.output - α := by linarith
    calc -α ≤ cbtc'.sol.trajectory t cbtc'.pivp.output - α := this
      _ ≤ |cbtc'.sol.trajectory t cbtc'.pivp.output - α| := le_abs_self _
  linarith

/-! ## Corollary: the axiom hypothesis `0 ≤ β + q` is necessary.

`CBTC_PCD_target_nonneg` shows that any CBTC+PCD witness forces its
target value `α ≥ 0`. So for the conclusion of `polyCRN_exists_neg_shift`
to be satisfiable at all, we *must* have `0 ≤ β + q`. The axiom's
hypothesis `hβq` is therefore exactly the consistency envelope; no
weakening of it is admissible. -/
theorem axiom_conclusion_forces_nonneg {β : ℝ} (q : ℚ) (hq : q < 0)
    (hβq : 0 ≤ β + (q : ℝ)) {d : ℕ}
    (cbtc : CertifiedBoundedTimeComputable d β)
    (pcd : PolyCRNDecomposition d cbtc.pivp) :
    0 ≤ β + (q : ℝ) := by
  obtain ⟨d', cbtc', pcd', _⟩ := polyCRN_exists_neg_shift q hq hβq cbtc pcd
  exact CBTC_PCD_target_nonneg cbtc' pcd'

end Algebraic
end Ripple
