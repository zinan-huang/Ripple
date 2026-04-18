/-
  Ripple.DualRail.BTCReduction — DNA 25 dual-rail at BoundedTimeComputable level.

  Given a zero-init BoundedTimeComputable for α, the [RTCRN2]/DNA 25
  polynomial-scale annihilation dual-rail construction produces a (higher-
  dimensional) BTC for α whose init is zero on every species and whose
  non-output species trajectories are non-negative throughout `[0, ∞)`.
  Time modulus is preserved.

  Architecture. The underlying construction combines:
    (a) the semantic field split `p_i = p_i⁺ − p_i⁻` into non-negative parts
        (syntactic analogue: `posPart/negPart` in `DualRail/ConstantAnnihilation.lean`),
    (b) the dual-rail PIVP `u_i' = p_i⁺(u−v) − u_i·v_i·(p_i⁺+p_i⁻)`,
        `v_i' = p_i⁻(u−v) − u_i·v_i·(p_i⁺+p_i⁻)`, plus a readout species
        `z' = p_o(u − v)` with `z(0) = 0`, giving `z(t) = y_o(t)`, and
    (c) the DNA 25 polynomial-scale boundedness argument (already axiomatized
        at a weaker "bare function" form in
        `Ripple/DualRail/ConstantAnnihilation.lean`).

  Discharging `BoundedTimeComputable.toDualRail` requires strengthening
  `dualRail_polynomial_scale_bounded` to yield a full `PIVP.Solution`
  structure (with `HasDerivAt` on every coordinate), as in the session-27
  pattern (Mathlib-gap decomposition for ODE existence). Left as a research
  gap for now — the axiom's statement is the published DNA 25 theorem at
  the BTC level.

  Reference: [RTCRN2] (Huang-Klinge-Lathrop, DNA 25, 2019).
-/

import Ripple.Core.BoundedTime
import Ripple.Core.InitShift

namespace Ripple

/-- [RTCRN2]/DNA 25 dual-rail BTC reduction: a zero-init BTC for α produces
a (possibly higher-dimensional) BTC for α whose every species starts at 0
and whose non-output species stay non-negative on `[0, ∞)`. Time modulus
is preserved exactly. The underlying construction is polynomial-scale
annihilation dual-rail + readout. -/
axiom BoundedTimeComputable.toDualRail {d : ℕ} {α : ℝ}
    (btc : BoundedTimeComputable d α)
    (_h_zero : ∀ j, btc.pivp.init j = 0) :
    ∃ d' : ℕ, ∃ btc' : BoundedTimeComputable d' α,
      (∀ j, btc'.pivp.init j = 0) ∧
      (∀ t : ℝ, 0 ≤ t → ∀ j, j ≠ btc'.pivp.output →
        0 ≤ btc'.sol.trajectory t j) ∧
      btc'.modulus = btc.modulus

/-! ## Composed DNA 25 reduction: shift + dual-rail -/

/-- DNA 25 semantic reduction at BTC level: every BTC for α reduces, via
change of variables `ẑ = y − y₀`, to a zero-init + non-negative-interior
BTC for `α − y₀`, with the same time modulus. Composes
`BoundedTimeComputable.shiftToZero` with `BoundedTimeComputable.toDualRail`. -/
theorem BoundedTimeComputable.dna25_shift_dualRail {d : ℕ} {α : ℝ}
    (btc : BoundedTimeComputable d α) :
    ∃ β : ℝ, ∃ d' : ℕ, ∃ btc' : BoundedTimeComputable d' (α - β),
      (∀ j, btc'.pivp.init j = 0) ∧
      (∀ t : ℝ, 0 ≤ t → ∀ j, j ≠ btc'.pivp.output →
        0 ≤ btc'.sol.trajectory t j) ∧
      btc'.modulus = btc.modulus := by
  obtain ⟨d', btc', h_init', h_nonneg', h_mod_eq⟩ :=
    btc.shiftToZero.toDualRail (fun j => btc.shiftToZero_pivp_init j)
  exact ⟨btc.pivp.init btc.pivp.output, d', btc', h_init', h_nonneg', h_mod_eq⟩

/-! ## IsRealTimeComputable-level DNA 25 full reduction -/

/-- DNA 25 full reduction at `IsRealTimeComputable` level:
`α` real-time computable ⟹ there exist a shift constant `β` and a zero-init
+ non-negative-interior BTC for `(α − β)` with the same linear modulus.
The missing summand `β` is itself real-time computable by `realtime_const`,
so `realtime_field_add` closes the cycle back to `α`. -/
theorem IsRealTimeComputable.dna25_full_reduction {α : ℝ}
    (ha : IsRealTimeComputable α) :
    ∃ β : ℝ, ∃ d : ℕ, ∃ btc : BoundedTimeComputable d (α - β),
      (∀ j, btc.pivp.init j = 0) ∧
      (∀ t : ℝ, 0 ≤ t → ∀ j, j ≠ btc.pivp.output →
        0 ≤ btc.sol.trajectory t j) ∧
      ∃ C > 0, ∀ r : ℕ, btc.modulus r ≤ C * (↑r + 1) := by
  obtain ⟨d, btc, C, hC, hmod⟩ := ha
  obtain ⟨β, d', btc', h_init', h_nonneg', h_mod_eq⟩ :=
    btc.dna25_shift_dualRail
  refine ⟨β, d', btc', h_init', h_nonneg', C, hC, fun r => ?_⟩
  rw [h_mod_eq]
  exact hmod r

end Ripple
