/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Canonical linear sampled-class floor

The Phase-6 drift only needs a sampled-class margin `K₀` with
`n ≤ 25 K₀`, `1 ≤ K₀`, and `K₀ ≤ n`.  The concentration theorem should
therefore target the canonical integer threshold `ceil(n/25)` directly instead
of choosing an arbitrary `K₀` and later assuming these arithmetic facts.
-/

import Ripple.PopulationProtocol.ExactMajority.Probability.Phase5Convergence
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase6HorizonBound

namespace Ripple.PopulationProtocol.ExactMajority
namespace Phase5SampleFloorCalibration

/-- `ceil(n/25)` in natural-number arithmetic. -/
def sampleFloorN (n : ℕ) : ℕ := (n + 24) / 25

/-- The exact scalar interface consumed by the Phase-6 horizon proof. -/
structure LinearFloorCalibration (n K₀ : ℕ) : Prop where
  pos : 1 ≤ K₀
  le_population : K₀ ≤ n
  linear : n ≤ 25 * K₀

theorem sampleFloorN_pos {n : ℕ} (hn : 1 ≤ n) :
    1 ≤ sampleFloorN n := by
  unfold sampleFloorN
  omega

theorem sampleFloorN_le {n : ℕ} (hn : 1 ≤ n) :
    sampleFloorN n ≤ n := by
  unfold sampleFloorN
  omega

theorem sampleFloorN_linear (n : ℕ) :
    n ≤ 25 * sampleFloorN n := by
  unfold sampleFloorN
  omega

/-- The paper-regime population assumption supplies the complete calibration
for the canonical threshold. -/
theorem canonical_calibration {n : ℕ} (hn : 2 ≤ n) :
    LinearFloorCalibration n (sampleFloorN n) :=
  ⟨sampleFloorN_pos (by omega), sampleFloorN_le (by omega),
    sampleFloorN_linear n⟩

/-- A sampled-floor theorem instantiated at the canonical threshold exports
the exact linear lower bound needed by the Phase-6 drift horizon. -/
theorem sampledFloor_canonical_linear
    {L K n : ℕ} (i : Fin (L + 1))
    (c : Config (AgentState L K))
    (hfloor : Phase5Convergence.sampledFloor
      (L := L) (K := K) i (sampleFloorN n) c) :
    n ≤ 25 * Phase5Convergence.sampledReserveClassU
      (L := L) (K := K) i c := by
  exact (sampleFloorN_linear n).trans
    (Nat.mul_le_mul_left 25 hfloor)

/-- With the canonical threshold, the Phase-6 display bound has no free
sample-floor arithmetic premise. -/
theorem phase6_driftHorizon_le_87_canonical
    {n L l : ℕ}
    (hn : 2 ≤ n) (hnL : n ≤ 2 ^ L) (hlL : l ≤ L) :
    DriftSurvival.driftHorizon (sampleFloorN n : ℝ) n
        (Phase6PhiPotential.phase6PhiMax n l) 2
      ≤ 87 * n * (L + 1) :=
  phase6_driftHorizon_le_87 hn hnL hlL (sampleFloorN_linear n)

#print axioms sampleFloorN_pos
#print axioms sampleFloorN_le
#print axioms sampleFloorN_linear
#print axioms canonical_calibration
#print axioms sampledFloor_canonical_linear
#print axioms phase6_driftHorizon_le_87_canonical

end Phase5SampleFloorCalibration
end Ripple.PopulationProtocol.ExactMajority
