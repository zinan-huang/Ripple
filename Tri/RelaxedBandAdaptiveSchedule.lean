/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.RelaxedBandUniformSchedule
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Scale-adaptive scalar certificates for the relaxed dyadic schedule

A uniform productive-quota multiplier wastes a square in the bias parameter
at the last dyadic rungs.  Here that multiplier grows only as the active
minority scale shrinks:

```
Rⱼ = R₀ * (1 + L / Pⱼ).
```

Thus `Rⱼ ≥ R₀`, while `Rⱼ Pⱼ ≥ R₀ L`.  The first inequality preserves the
directional margin; the second keeps the productive-event threshold large
even at the final scale-one rung.  The raw-clock multiplier is independently
`C * Rⱼ`; this separation lets `C` absorb the fixed inverse firing rate
without reintroducing a square in `Rⱼ`.
-/

namespace Tri

open scoped ENNReal

/-- The productive-quota multiplier used at active minority scale `Q`. -/
def relaxedDyadicAdaptiveMultiplier
    (R₀ L Q : ℕ) : ℕ :=
  R₀ * (1 + L / Q)

/-- The adaptive multiplier is never smaller than its base value. -/
theorem relaxedDyadicAdaptiveMultiplier_ge_base
    (R₀ L Q : ℕ) :
    R₀ ≤ relaxedDyadicAdaptiveMultiplier R₀ L Q := by
  unfold relaxedDyadicAdaptiveMultiplier
  simpa [Nat.add_comm] using
    (Nat.le_mul_of_pos_right R₀ (Nat.succ_pos (L / Q)))

/-- Multiplying the adaptive horizon factor by the active scale absorbs the
fixed buffer. -/
theorem relaxedDyadicAdaptiveMultiplier_mul_scale_ge
    (R₀ L Q : ℕ) (hQ : 1 ≤ Q) :
    R₀ * L ≤ relaxedDyadicAdaptiveMultiplier R₀ L Q * Q := by
  have hstrict : L < Q * (L / Q + 1) :=
    Nat.lt_mul_div_succ L (show 0 < Q by omega)
  have hLQ : L ≤ (1 + L / Q) * Q := by
    simpa [Nat.add_comm, Nat.mul_comm] using Nat.le_of_lt hstrict
  have hmul := Nat.mul_le_mul_left R₀ hLQ
  simpa [relaxedDyadicAdaptiveMultiplier, Nat.mul_assoc] using hmul

/-- A finite sum of dyadic natural quotients is at most twice its numerator. -/
theorem sum_nat_div_pow_two_le (L k : ℕ) :
    (∑ i ∈ Finset.range (k + 1), L / 2 ^ i) ≤ 2 * L := by
  have hreal :
      (∑ i ∈ Finset.range (k + 1),
          ((L / 2 ^ i : ℕ) : ℝ)) ≤
        (2 : ℝ) * L := by
    calc
      (∑ i ∈ Finset.range (k + 1),
          ((L / 2 ^ i : ℕ) : ℝ)) ≤
          ∑ i ∈ Finset.range (k + 1),
            (L : ℝ) / (2 : ℝ) ^ i := by
        apply Finset.sum_le_sum
        intro i hi
        simpa only [Nat.cast_pow, Nat.cast_ofNat] using
          (Nat.cast_div_le
            (α := ℝ) (m := L) (n := 2 ^ i))
      _ = (L : ℝ) *
          ∑ i ∈ Finset.range (k + 1),
            ((1 : ℝ) / 2) ^ i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [one_div, inv_pow]
        ring
      _ ≤ (L : ℝ) * 2 := by
        exact mul_le_mul_of_nonneg_left
          (sum_geometric_two_le (k + 1)) (by positivity)
      _ = (2 : ℝ) * L := by ring
  exact_mod_cast hreal

/-- Reversing a finite dyadic quotient sum preserves the same bound. -/
theorem sum_nat_div_pow_two_reverse_le (L k : ℕ) :
    (∑ j ∈ Finset.range (k + 1),
      L / 2 ^ (k - j)) ≤ 2 * L := by
  calc
    (∑ j ∈ Finset.range (k + 1),
        L / 2 ^ (k - j)) =
        ∑ i ∈ Finset.range (k + 1), L / 2 ^ i := by
      simpa using
        Finset.sum_range_reflect
          (fun i => L / 2 ^ i) (k + 1)
    _ ≤ 2 * L := sum_nat_div_pow_two_le L k

/-- The reverse dyadic power at stage `j` is no larger than the active
minority scale. -/
theorem relaxedDyadicRemainingPower_le_activeScale
    {P j : ℕ} (hP : 1 ≤ P)
    (hj : j < relaxedDyadicStageCount P) :
    2 ^ (Nat.log 2 P - j) ≤
      relaxedDyadicActiveScale P j := by
  rw [relaxedDyadicActiveScale_eq P j
    (Nat.ne_of_gt
      (lt_of_lt_of_le Nat.zero_lt_one hP)) hj]
  have hjle : j ≤ Nat.log 2 P := by
    unfold relaxedDyadicStageCount at hj
    omega
  unfold relaxedDyadicScale
  apply
    (Nat.le_div_iff_mul_le
      (pow_pos (by norm_num) j)).2
  rw [Nat.pow_sub_mul_pow 2 hjle]
  exact Nat.pow_log_le_self 2
    (Nat.ne_of_gt
      (lt_of_lt_of_le Nat.zero_lt_one hP))

/-- The adaptive multipliers have only an additive `2L` overhead over the
number of dyadic stages. -/
theorem relaxedDyadicAdaptiveMultiplier_sum_le
    (R₀ L P : ℕ) (hP : 1 ≤ P) :
    (∑ j ∈ Finset.range (relaxedDyadicStageCount P),
      relaxedDyadicAdaptiveMultiplier R₀ L
        (relaxedDyadicActiveScale P j)) ≤
      R₀ * (relaxedDyadicStageCount P + 2 * L) := by
  calc
    (∑ j ∈ Finset.range (relaxedDyadicStageCount P),
      relaxedDyadicAdaptiveMultiplier R₀ L
        (relaxedDyadicActiveScale P j)) ≤
        ∑ j ∈ Finset.range (relaxedDyadicStageCount P),
          R₀ * (1 +
            L / 2 ^ (Nat.log 2 P - j)) := by
      apply Finset.sum_le_sum
      intro j hj
      have hj' : j < relaxedDyadicStageCount P :=
        Finset.mem_range.mp hj
      have hDpos :
          0 < 2 ^ (Nat.log 2 P - j) :=
        pow_pos (by norm_num) _
      have hdiv :
          L / relaxedDyadicActiveScale P j ≤
            L / 2 ^ (Nat.log 2 P - j) :=
        Nat.div_le_div_left
          (relaxedDyadicRemainingPower_le_activeScale
            hP hj')
          hDpos
      unfold relaxedDyadicAdaptiveMultiplier
      exact Nat.mul_le_mul_left R₀
        (Nat.add_le_add_left hdiv 1)
    _ = R₀ * (relaxedDyadicStageCount P +
          ∑ j ∈ Finset.range
              (relaxedDyadicStageCount P),
            L / 2 ^ (Nat.log 2 P - j)) := by
      simp [Finset.mul_sum, Finset.sum_add_distrib,
        mul_add, Nat.mul_comm]
    _ ≤ R₀ *
        (relaxedDyadicStageCount P + 2 * L) := by
      apply Nat.mul_le_mul_left
      apply Nat.add_le_add_left
      unfold relaxedDyadicStageCount
      exact sum_nat_div_pow_two_reverse_le
        L (Nat.log 2 P)

/-- Scalar data sufficient to certify every adaptive rung.  The corner
condition is imposed only at the initial, largest scale. -/
structure RelaxedDyadicAdaptiveData
    (r : RelaxedRate) (n P : ℕ) where
  L : ℕ
  R₀ : ℕ
  C : ℕ
  beta : NNReal
  hP : 1 ≤ P
  hL : 1 ≤ L
  hR₀ : 1 ≤ R₀
  hC : 1 ≤ C
  hroom : 2 * (P + L) ≤ n
  hbeta1 : 1 ≤ beta
  hmargin : (1 : NNReal) + 1 / (R₀ : NNReal) ≤ beta
  hcorner :
    beta * (relaxedDyadicBHi P L + 1 : NNReal) ≤
      r.fire * (relaxedDyadicLower n P L + 1 : NNReal)

/-- Adaptive scalar data instantiated at one active dyadic scale. -/
noncomputable def relaxedDyadicAdaptiveRungData
    (r : RelaxedRate) (n P : ℕ)
    (A : RelaxedDyadicAdaptiveData r n P)
    (j : ℕ) :
    RelaxedDyadicRungData r n := by
  let Q := relaxedDyadicActiveScale P j
  let R := relaxedDyadicAdaptiveMultiplier A.R₀ A.L Q
  let H := A.C * R
  have hQ : 1 ≤ Q :=
    relaxedDyadicActiveScale_pos P j
  have hQP : Q ≤ P :=
    relaxedDyadicActiveScale_le P j A.hP
  have hroom : 2 * (Q + A.L) ≤ n := by
    have := A.hroom
    omega
  have hR₀RNat : A.R₀ ≤ R := by
    exact relaxedDyadicAdaptiveMultiplier_ge_base A.R₀ A.L Q
  have hR : 1 ≤ R :=
    A.hR₀.trans hR₀RNat
  have hH : 1 ≤ H := by
    dsimp only [H]
    exact Nat.mul_pos
      (lt_of_lt_of_le Nat.zero_lt_one A.hC)
      (lt_of_lt_of_le Nat.zero_lt_one hR)
  have hfire : r.fire ≤ A.beta := by
    calc
      r.fire ≤ 1 := by
        rw [← r.add_eq_one]
        exact le_add_right le_rfl
      _ ≤ A.beta := A.hbeta1
  have hbHi :
      relaxedDyadicBHi Q A.L + 1 ≤
        relaxedDyadicBHi P A.L + 1 := by
    unfold relaxedDyadicBHi
    omega
  have hlower :
      relaxedDyadicLower n P A.L + 1 ≤
        relaxedDyadicLower n Q A.L + 1 := by
    unfold relaxedDyadicLower
    omega
  refine
    { P := Q
      L := A.L
      R := R
      H := H
      beta := A.beta
      slack := 0
      tau := 0
      hP := hQ
      hL := A.hL
      hR := hR
      hH := hH
      hroom := hroom
      hbeta1 := A.hbeta1
      hslack := ?_
      htau := ?_
      hmargin := ?_
      hcorner := ?_ }
  · simpa using hfire
  · simp
  · have hR₀pos : (0 : NNReal) < (A.R₀ : NNReal) := by
      exact_mod_cast
        (show 0 < A.R₀ from
          lt_of_lt_of_le Nat.zero_lt_one A.hR₀)
    have hR₀R : (A.R₀ : NNReal) ≤ (R : NNReal) := by
      exact_mod_cast hR₀RNat
    have hrecip :
        (1 : NNReal) / (R : NNReal) ≤
          1 / (A.R₀ : NNReal) :=
      one_div_le_one_div_of_le hR₀pos hR₀R
    have hadd :
        (1 : NNReal) + 1 / (R : NNReal) ≤
          1 + 1 / (A.R₀ : NNReal) := by
      simpa [add_comm] using add_le_add_left hrecip 1
    simpa using hadd.trans A.hmargin
  · calc
      A.beta * (relaxedDyadicBHi Q A.L + 1 : NNReal) ≤
          A.beta * (relaxedDyadicBHi P A.L + 1 : NNReal) :=
        mul_le_mul_left' (by exact_mod_cast hbHi) _
      _ ≤ r.fire *
          (relaxedDyadicLower n P A.L + 1 : NNReal) :=
        A.hcorner
      _ ≤ r.fire *
          (relaxedDyadicLower n Q A.L + 1 : NNReal) :=
        mul_le_mul_left' (by exact_mod_cast hlower) _

/-- Exact total raw horizon of the adaptive dyadic schedule. -/
noncomputable def relaxedDyadicAdaptiveHorizon
    (r : RelaxedRate) (n P : ℕ)
    (A : RelaxedDyadicAdaptiveData r n P) : ℕ :=
  ∑ j ∈ Finset.range (relaxedDyadicStageCount P),
    relaxedDyadicLadderHorizon n
      (relaxedDyadicAdaptiveRungData r n P A) j

/-- The exact adaptive schedule has a raw horizon linear in both the
productive-quota scale `R₀` and the independent clock factor `C`. -/
theorem relaxedDyadicAdaptiveHorizon_le
    (r : RelaxedRate) (n P : ℕ)
    (A : RelaxedDyadicAdaptiveData r n P) :
    relaxedDyadicAdaptiveHorizon r n P A ≤
      4096 * A.C * A.R₀ * n *
        (relaxedDyadicStageCount P + 2 * A.L) := by
  unfold relaxedDyadicAdaptiveHorizon
  simp only [relaxedDyadicLadderHorizon,
    relaxedDyadicAdaptiveRungData,
    relaxedDyadicHorizon]
  calc
    (∑ j ∈ Finset.range (relaxedDyadicStageCount P),
        4096 * (A.C *
          relaxedDyadicAdaptiveMultiplier A.R₀ A.L
            (relaxedDyadicActiveScale P j)) * n) =
        4096 * A.C * n *
          ∑ j ∈ Finset.range
              (relaxedDyadicStageCount P),
            relaxedDyadicAdaptiveMultiplier A.R₀ A.L
              (relaxedDyadicActiveScale P j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ ≤ 4096 * A.C * n *
        (A.R₀ *
          (relaxedDyadicStageCount P + 2 * A.L)) :=
      Nat.mul_le_mul_left (4096 * A.C * n)
        (relaxedDyadicAdaptiveMultiplier_sum_le
          A.R₀ A.L P A.hP)
    _ = 4096 * A.C * A.R₀ * n *
        (relaxedDyadicStageCount P + 2 * A.L) := by
      ring

/-- Exact finite error sum of the adaptive dyadic schedule. -/
noncomputable def relaxedDyadicAdaptiveError
    (r : RelaxedRate) (n P : ℕ)
    (A : RelaxedDyadicAdaptiveData r n P) : ℝ≥0∞ :=
  ∑ j ∈ Finset.range (relaxedDyadicStageCount P),
    relaxedDyadicLadderError r n
      (relaxedDyadicAdaptiveRungData r n P A) j

/-- Adaptive scalar data supplies the complete physical schedule and reaches
exact all-`X` consensus. -/
theorem relaxedDyadicAdaptive_raw_consensus
    (r : RelaxedRate) (n P : ℕ)
    (A : RelaxedDyadicAdaptiveData r n P) :
    terminalFailureMass
        (iter
          (freeze (fun x : ℕ => x = n)
            (relaxedTriChain r n))
          (relaxedDyadicAdaptiveHorizon r n P A)
          (relaxedDyadicStart n P))
        (fun x : ℕ => x = n) ≤
      relaxedDyadicAdaptiveError r n P A := by
  unfold relaxedDyadicAdaptiveHorizon
  unfold relaxedDyadicAdaptiveError
  apply relaxedDyadicSchedule_raw_consensus
  intro j hj
  change relaxedDyadicActiveScale P j =
    relaxedDyadicScale P j
  exact relaxedDyadicActiveScale_eq P j
    (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one A.hP)) hj

end Tri

#print axioms Tri.relaxedDyadicAdaptiveMultiplier_ge_base
#print axioms Tri.relaxedDyadicAdaptiveMultiplier_mul_scale_ge
#print axioms Tri.sum_nat_div_pow_two_le
#print axioms Tri.sum_nat_div_pow_two_reverse_le
#print axioms Tri.relaxedDyadicRemainingPower_le_activeScale
#print axioms Tri.relaxedDyadicAdaptiveMultiplier_sum_le
#print axioms Tri.relaxedDyadicAdaptiveRungData
#print axioms Tri.relaxedDyadicAdaptiveHorizon_le
#print axioms Tri.relaxedDyadicAdaptive_raw_consensus
