/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.RelaxedBandScalarConstructor

/-!
# Finite raw-chain theorem for the relaxed protocol

This is the paper-facing finite theorem after isolating the one asymptotic
population inequality.  A fixed strict odds certificate `beta > 1` must hold
at the buffered initial corner.  All productive-scale and raw-clock constants
are then constructed automatically.
-/

namespace Tri

open scoped ENNReal

/-- A buffered initial odds certificate yields exact `X` consensus on the raw
relaxed chain, with an explicit logarithmic number of exponential rung
errors and a linear adaptive horizon. -/
theorem theorem3_relaxed_of_corner
    (r : RelaxedRate) (n x y L : ℕ) (beta : NNReal)
    (hfire : 0 < r.fire)
    (hpop : x + y = n)
    (hy : 1 ≤ y) (hL : 1 ≤ L)
    (hroom : 2 * (y + L) ≤ n)
    (hbeta : 1 < beta)
    (hcorner :
      beta * (y + L - 1 : NNReal) ≤
        r.fire * (x - L + 1 : NNReal)) :
    ∃ E : RelaxedDyadicAdaptiveErrorData r n y,
      terminalFailureMass
          (iter
            (freeze (fun z : ℕ => z = n)
              (relaxedTriChain r n))
            (relaxedDyadicAdaptiveHorizon r n y E.base)
            x)
          (fun z : ℕ => z = n) ≤
        (relaxedDyadicStageCount y : ℝ≥0∞) *
          relaxedDyadicAdaptiveRungEnvelope r n y E ∧
      relaxedDyadicAdaptiveHorizon r n y E.base ≤
        4096 * E.base.C * E.base.R₀ * n *
          (relaxedDyadicStageCount y + 2 * L) := by
  have hbHi :
      relaxedDyadicBHi y L + 1 = y + L - 1 := by
    unfold relaxedDyadicBHi
    omega
  have hlower :
      relaxedDyadicLower n y L + 1 = x - L + 1 := by
    unfold relaxedDyadicLower
    omega
  have hcorner' :
      beta * (relaxedDyadicBHi y L + 1 : NNReal) ≤
        r.fire *
          (relaxedDyadicLower n y L + 1 : NNReal) := by
    have hbHiNN :
        (relaxedDyadicBHi y L + 1 : NNReal) =
          (y + L - 1 : NNReal) := by
      exact_mod_cast hbHi
    have hlowerNN :
        (relaxedDyadicLower n y L + 1 : NNReal) =
          (x - L + 1 : NNReal) := by
      exact_mod_cast hlower
    rw [hbHiNN, hlowerNN]
    exact hcorner
  obtain ⟨E, hEL⟩ :=
    exists_relaxedDyadicAdaptiveErrorData
      r n y L beta hfire hy hL hroom hbeta hcorner'
  refine ⟨E, ?_, ?_⟩
  · have hstart : relaxedDyadicStart n y = x := by
      unfold relaxedDyadicStart
      omega
    simpa only [hstart] using
      relaxedDyadicAdaptive_raw_consensus_exp r n y E
  · simpa only [hEL] using
      relaxedDyadicAdaptiveHorizon_le r n y E.base

end Tri

#print axioms Tri.theorem3_relaxed_of_corner
