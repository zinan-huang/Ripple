/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.RelaxedBandPhysicalSchedule

/-!
# Uniform scalar certificates for the relaxed dyadic schedule

A single buffer, productive-quota multiplier, raw-horizon multiplier, and odds
parameter certify every rung.
The only corner inequality is imposed at the initial, largest minority scale;
all later scales have a smaller adverse corner and a larger favorable count.
-/

namespace Tri

open scoped ENNReal

/-- Scalar data sufficient to certify every rung of one dyadic schedule. -/
structure RelaxedDyadicUniformData
    (r : RelaxedRate) (n P : ℕ) where
  L : ℕ
  R : ℕ
  H : ℕ
  beta : NNReal
  hP : 1 ≤ P
  hL : 1 ≤ L
  hR : 1 ≤ R
  hH : 1 ≤ H
  hroom : 2 * (P + L) ≤ n
  hbeta1 : 1 ≤ beta
  hmargin : (1 : NNReal) + 1 / (R : NNReal) ≤ beta
  hcorner :
    beta * (relaxedDyadicBHi P L + 1 : NNReal) ≤
      r.fire * (relaxedDyadicLower n P L + 1 : NNReal)

/-- Extend the active dyadic scale by one beyond the scheduled range, so it
can index an infinite family of certified rung records. -/
def relaxedDyadicActiveScale (P j : ℕ) : ℕ :=
  max 1 (relaxedDyadicScale P j)

theorem relaxedDyadicActiveScale_pos (P j : ℕ) :
    1 ≤ relaxedDyadicActiveScale P j := by
  unfold relaxedDyadicActiveScale
  exact Nat.le_max_left _ _

theorem relaxedDyadicActiveScale_le
    (P j : ℕ) (hP : 1 ≤ P) :
    relaxedDyadicActiveScale P j ≤ P := by
  unfold relaxedDyadicActiveScale relaxedDyadicScale
  apply max_le hP
  exact Nat.div_le_self P (2 ^ j)

theorem relaxedDyadicActiveScale_eq
    (P j : ℕ) (hP : P ≠ 0)
    (hj : j < relaxedDyadicStageCount P) :
    relaxedDyadicActiveScale P j = relaxedDyadicScale P j := by
  unfold relaxedDyadicActiveScale
  exact Nat.max_eq_right
    (relaxedDyadicScale_pos P j hP hj)

/-- The uniform data instantiated at one active dyadic scale. -/
noncomputable def relaxedDyadicUniformRungData
    (r : RelaxedRate) (n P : ℕ)
    (U : RelaxedDyadicUniformData r n P)
    (j : ℕ) :
    RelaxedDyadicRungData r n := by
  let Q := relaxedDyadicActiveScale P j
  have hQ : 1 ≤ Q :=
    relaxedDyadicActiveScale_pos P j
  have hQP : Q ≤ P :=
    relaxedDyadicActiveScale_le P j U.hP
  have hroom : 2 * (Q + U.L) ≤ n := by
    have := U.hroom
    omega
  have hfire : r.fire ≤ U.beta := by
    calc
      r.fire ≤ 1 := by
        rw [← r.add_eq_one]
        exact le_add_right le_rfl
      _ ≤ U.beta := U.hbeta1
  have hbHi :
      relaxedDyadicBHi Q U.L + 1 ≤
        relaxedDyadicBHi P U.L + 1 := by
    unfold relaxedDyadicBHi
    omega
  have hlower :
      relaxedDyadicLower n P U.L + 1 ≤
        relaxedDyadicLower n Q U.L + 1 := by
    unfold relaxedDyadicLower
    omega
  refine
    { P := Q
      L := U.L
      R := U.R
      H := U.H
      beta := U.beta
      slack := 0
      tau := 0
      hP := hQ
      hL := U.hL
      hR := U.hR
      hH := U.hH
      hroom := hroom
      hbeta1 := U.hbeta1
      hslack := ?_
      htau := ?_
      hmargin := ?_
      hcorner := ?_ }
  · simpa using hfire
  · simp
  · simpa using U.hmargin
  · calc
      U.beta * (relaxedDyadicBHi Q U.L + 1 : NNReal) ≤
          U.beta * (relaxedDyadicBHi P U.L + 1 : NNReal) :=
        mul_le_mul_left' (by exact_mod_cast hbHi) _
      _ ≤ r.fire *
          (relaxedDyadicLower n P U.L + 1 : NNReal) :=
        U.hcorner
      _ ≤ r.fire *
          (relaxedDyadicLower n Q U.L + 1 : NNReal) :=
        mul_le_mul_left' (by exact_mod_cast hlower) _

/-- Exact total raw horizon of a uniform dyadic schedule. -/
def relaxedDyadicUniformHorizon
    (n P : ℕ) (H : ℕ) : ℕ :=
  relaxedDyadicStageCount P * relaxedDyadicHorizon H n

/-- Exact finite error sum of a uniform dyadic schedule. -/
noncomputable def relaxedDyadicUniformError
    (r : RelaxedRate) (n P : ℕ)
    (U : RelaxedDyadicUniformData r n P) : ℝ≥0∞ :=
  ∑ j ∈ Finset.range (relaxedDyadicStageCount P),
    relaxedDyadicLadderError r n
      (relaxedDyadicUniformRungData r n P U) j

/-- The block horizons of the uniform schedule have a closed form. -/
theorem relaxedDyadicUniformHorizon_sum
    (r : RelaxedRate) (n P : ℕ)
    (U : RelaxedDyadicUniformData r n P) :
    (∑ j ∈ Finset.range (relaxedDyadicStageCount P),
      relaxedDyadicLadderHorizon n
        (relaxedDyadicUniformRungData r n P U) j) =
      relaxedDyadicUniformHorizon n P U.H := by
  simp [relaxedDyadicLadderHorizon,
    relaxedDyadicUniformRungData,
    relaxedDyadicUniformHorizon]

/-- Uniform scalar data supplies the complete physical schedule and reaches
exact all-`X` consensus. -/
theorem relaxedDyadicUniform_raw_consensus
    (r : RelaxedRate) (n P : ℕ)
    (U : RelaxedDyadicUniformData r n P) :
    terminalFailureMass
        (iter
          (freeze (fun x : ℕ => x = n)
            (relaxedTriChain r n))
          (∑ j ∈ Finset.range (relaxedDyadicStageCount P),
            relaxedDyadicLadderHorizon n
              (relaxedDyadicUniformRungData r n P U) j)
          (relaxedDyadicStart n P))
        (fun x : ℕ => x = n) ≤
      ∑ j ∈ Finset.range (relaxedDyadicStageCount P),
        relaxedDyadicLadderError r n
          (relaxedDyadicUniformRungData r n P U) j := by
  apply relaxedDyadicSchedule_raw_consensus
  intro j hj
  change relaxedDyadicActiveScale P j =
    relaxedDyadicScale P j
  exact relaxedDyadicActiveScale_eq P j
    (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one U.hP)) hj

/-- Closed-form version of the uniform raw consensus theorem. -/
theorem relaxedDyadicUniform_raw_consensus_closed
    (r : RelaxedRate) (n P : ℕ)
    (U : RelaxedDyadicUniformData r n P) :
    terminalFailureMass
        (iter
          (freeze (fun x : ℕ => x = n)
            (relaxedTriChain r n))
          (relaxedDyadicUniformHorizon n P U.H)
          (relaxedDyadicStart n P))
        (fun x : ℕ => x = n) ≤
      relaxedDyadicUniformError r n P U := by
  rw [← relaxedDyadicUniformHorizon_sum r n P U]
  exact relaxedDyadicUniform_raw_consensus r n P U

end Tri

#print axioms Tri.relaxedDyadicActiveScale_pos
#print axioms Tri.relaxedDyadicActiveScale_le
#print axioms Tri.relaxedDyadicActiveScale_eq
#print axioms Tri.relaxedDyadicUniformRungData
#print axioms Tri.relaxedDyadicUniformHorizon_sum
#print axioms Tri.relaxedDyadicUniform_raw_consensus
#print axioms Tri.relaxedDyadicUniform_raw_consensus_closed
