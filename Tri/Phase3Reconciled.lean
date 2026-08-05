/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Phase3Handoff
import Tri.ReconciledRegions

/-!
# The reconciled phase-3 endgame

Phase 3 starts with twice the minority count at most
`gamma * log_2 n`.  Its Feller boundary is the first state at which the
minority exceeds `L := gamma * log_2 n`; thus the exact bad `X`-count is
`aLo`, certified without subtraction by `aLo + L + 1 = n`.

The stopped corrected potential supplies the ordinary geometric error.  The
additional probability of crossing the `L`-boundary is charged separately to
`tri_feller`, with complementary parameter `bHi + 1 = L`.  For a start
`x + y = n`, the exact Feller distance is certified by
`y + k = L + 1`, hence `aLo + k = x`.
-/

namespace Tri

open scoped ENNReal

/-- The corrected-potential contribution to the reconciled phase-3 error.
The initial exponent is the uniform entry bound `L / 2`. -/
noncomputable def phase3ReconciledPotentialError (C₃ n γ : ℕ) : ℝ≥0∞ :=
  phase3Factor n ^ phase3Horizon C₃ n *
    ENNReal.ofReal ((2 : ℝ) ^ ((γ * Nat.log 2 n) / 2) - 1)

/-- The uniform Feller contribution to the reconciled phase-3 error.
Every exact entry distance is at least `L / 2 + 1`. -/
noncomputable def phase3ReconciledFellerError
    (n γ aLo bHi : ℕ) : ℝ≥0∞ :=
  ((bHi : ℝ≥0∞) / (aLo : ℝ≥0∞)) ^
    ((γ * Nat.log 2 n) / 2 + 1)

/-- The reconciled phase-3 error is the corrected-potential term plus the
additive Feller escape term. -/
noncomputable def phase3ReconciledError
    (C₃ n γ aLo bHi : ℕ) : ℝ≥0∞ :=
  phase3ReconciledPotentialError C₃ n γ +
    phase3ReconciledFellerError n γ aLo bHi

/-- The probability that the original chain has reached the dynamic lower
`X`-boundary `aLo` by time `T`.  With `aLo + L + 1 = n`, this is exactly the
event that the minority has reached `L + 1`. -/
noncomputable def phase3ReconciledEscapeMass
    (n T x aLo : ℕ) : ℝ≥0∞ :=
  hitProb (fun z : ℕ => z ≤ aLo) (triChain n) T x

/-- Under the headline guard, an admissible logarithmic threshold is at least
two.  This supplies the two strict positivity hypotheses of `tri_feller`. -/
theorem phase3_reconciled_threshold_two (n γ : ℕ) (h3 : 3 ≤ n)
    (hγ : 1 ≤ γ) (hsize : 6 * γ * Nat.log 2 n ≤ n) :
    2 ≤ γ * Nat.log 2 n := by
  have hlogpos : 0 < Nat.log 2 n :=
    Nat.log_pos (by norm_num) (by omega)
  have hlogle : Nat.log 2 n ≤ γ * Nat.log 2 n := by
    simpa only [one_mul] using Nat.mul_le_mul_right (Nat.log 2 n) hγ
  by_contra hthreshold
  have hthreshold_le : γ * Nat.log 2 n ≤ 1 := by omega
  have hlogeq : Nat.log 2 n = 1 := by omega
  have hγeq : γ = 1 := by
    rw [hlogeq] at hthreshold_le
    simp only [mul_one] at hthreshold_le
    omega
  have hnlt := Nat.lt_pow_succ_log_self (by norm_num : 1 < (2 : ℕ)) n
  rw [hlogeq] at hnlt
  norm_num at hnlt
  rw [hlogeq, hγeq] at hsize
  norm_num at hsize
  omega

/-- Freezing the existing stopped phase-3 chain at the earlier dynamic
`L`-boundary is the same as freezing the original chain there.  Below that
boundary the outer freeze acts first; above it, the only states already frozen
by `phase3Stop` are pure states at or above the population. -/
theorem phase3Stop_reconciled_freeze {n γ aLo : ℕ} (h3 : 3 ≤ n)
    (hsize : 6 * γ * Nat.log 2 n ≤ n)
    (haLo : aLo + γ * Nat.log 2 n + 1 = n) :
    freeze (fun z : ℕ => z ≤ aLo) (phase3Stop n) =
      freeze (fun z : ℕ => z ≤ aLo) (triChain n) := by
  have hsize' : 6 * (γ * Nat.log 2 n) ≤ n := by
    simpa only [Nat.mul_assoc] using hsize
  funext z
  by_cases hzlo : z ≤ aLo
  · rw [freeze_of_mem z hzlo, freeze_of_mem z hzlo]
  · rw [freeze_of_not_mem z hzlo, freeze_of_not_mem z hzlo]
    by_cases hregion : Phase3Region n z
    · rw [phase3Stop, freeze_of_not_mem z (by simpa using hregion)]
    · have hnz : n ≤ z := by
        by_contra hnz
        have hzlt : z < n := by omega
        apply hregion
        unfold Phase3Region
        constructor
        · exact hzlt
        · omega
      rw [phase3Stop, freeze_of_mem z hregion,
        triChain_pure_of_population_le h3 hnz]

/-- Existing stopped escape mass is bounded by the probability of hitting the
earlier dynamic boundary `z <= aLo`.  The displayed boundary certificate is
the subtraction-free form of `aLo = n - L - 1`. -/
theorem phase3EscapeMass_le_reconciled_hitProb {n γ T x aLo : ℕ}
    (h3 : 3 ≤ n) (hx : x ≤ n)
    (hsize : 6 * γ * Nat.log 2 n ≤ n)
    (haLo : aLo + γ * Nat.log 2 n + 1 = n) :
    phase3EscapeMass n T x ≤
      phase3ReconciledEscapeMass n T x aLo := by
  have hsize' : 6 * (γ * Nat.log 2 n) ≤ n := by
    simpa only [Nat.mul_assoc] using hsize
  calc
    phase3EscapeMass n T x ≤
        ∑' z, if z ≤ aLo then iter (phase3Stop n) T x z else 0 := by
      unfold phase3EscapeMass
      refine ENNReal.tsum_le_tsum fun z => ?_
      by_cases hescape : ¬ Phase3Region n z ∧ z ≠ n
      · by_cases hzlo : z ≤ aLo
        · simp [hescape, hzlo]
        · by_cases hzn : z ≤ n
          · have hzlt : z < n := lt_of_le_of_ne hzn hescape.2
            have hregion : Phase3Region n z := by
              unfold Phase3Region
              constructor
              · exact hzlt
              · omega
            exact False.elim (hescape.1 hregion)
          · have hzero := iter_phase3Stop_eq_zero_above n T x z h3 hx
              (by omega)
            simp [hescape, hzlo, hzero]
      · simp [hescape]
    _ = ∑' z, if aLo < z then 0 else iter (phase3Stop n) T x z := by
      apply tsum_congr
      intro z
      by_cases hz : z ≤ aLo
      · simp [hz, Nat.not_lt.mpr hz]
      · simp [hz, Nat.lt_of_not_ge hz]
    _ ≤ ∑' z, if aLo < z then 0 else
          iter (freeze (fun y : ℕ => y ≤ aLo) (phase3Stop n)) T x z := by
      exact failure_le_failure_freeze
        (B := fun y : ℕ => y ≤ aLo)
        (A := fun y : ℕ => aLo < y)
        (K := phase3Stop n) (by omega) T x
    _ = hitProb (fun z : ℕ => z ≤ aLo) (phase3Stop n) T x := by
      unfold hitProb expect ind
      apply tsum_congr
      intro z
      by_cases hz : z ≤ aLo <;> simp [hz]
    _ = phase3ReconciledEscapeMass n T x aLo := by
      unfold phase3ReconciledEscapeMass
      unfold hitProb
      rw [phase3Stop_reconciled_freeze h3 hsize haLo]

namespace Phase3Reconciled

/-- From an exact buffered entry, the mass escaping through minority level
`L + 1` is at most the exact Feller term.  The four equations name the initial
population split, the lower boundary, its complementary parameter, and the
distance to the boundary without natural subtraction. -/
theorem phase3_escape_le_feller
    (n γ T x aLo bHi : ℕ) (h3 : 3 ≤ n) (hγ : 1 ≤ γ)
    (hsize : 6 * γ * Nat.log 2 n ≤ n) (hentry : Phase3Entry n γ x)
    (haLo : aLo + γ * Nat.log 2 n + 1 = n)
    (hbHi : bHi + 1 = γ * Nat.log 2 n) :
    ∃ y k : ℕ,
      x + y = n ∧ y + k = γ * Nat.log 2 n + 1 ∧
        phase3ReconciledEscapeMass n T x aLo ≤
          ((bHi : ℝ≥0∞) / (aLo : ℝ≥0∞)) ^ k := by
  obtain ⟨y, hpop⟩ : ∃ y, x + y = n := by
    exact ⟨n - x, Nat.add_sub_of_le hentry.1⟩
  have hbuffer := phase3Entry_buffered hpop hentry hsize
  obtain ⟨k, hk⟩ : ∃ k, y + k = γ * Nat.log 2 n + 1 := by
    exact ⟨γ * Nat.log 2 n + 1 - y, by omega⟩
  refine ⟨y, k, hpop, hk, ?_⟩
  have hsize' : 6 * (γ * Nat.log 2 n) ≤ n := by
    simpa only [Nat.mul_assoc] using hsize
  have hthreshold := phase3_reconciled_threshold_two n γ h3 hγ hsize
  have hFpop : aLo + bHi + 2 = n := by omega
  have haLoPos : 0 < aLo := by omega
  have hbHiPos : 0 < bHi := by omega
  have hmajority : bHi ≤ aLo := by omega
  have hstart : aLo + k = x := by omega
  calc
    phase3ReconciledEscapeMass n T x aLo =
        hitProb (fun z : ℕ => z ≤ aLo) (triChain n) T x := rfl
    _ = hitProb (fun z : ℕ => z ≤ aLo) (triChain n) T
        (aLo + k) := by rw [hstart]
    _ ≤ ⨆ U : ℕ,
        hitProb (fun z : ℕ => z ≤ aLo) (triChain n) U (aLo + k) :=
      le_iSup (fun U : ℕ =>
        hitProb (fun z : ℕ => z ≤ aLo) (triChain n) U (aLo + k)) T
    _ ≤ ((bHi : ℝ≥0∞) / (aLo : ℝ≥0∞)) ^ k :=
      tri_feller n aLo bHi k h3 hFpop haLoPos hbHiPos hmajority

end Phase3Reconciled

/-- At a buffered phase-3 entry, the killed corrected potential is bounded by
the geometric potential at the uniform minority exponent `L / 2`. -/
theorem phase3StoppedPotential_entry_le {n γ x y : ℕ}
    (hpop : x + y = n) (hentry : Phase3Entry n γ x) :
    phase3StoppedPotential n x ≤
      ENNReal.ofReal ((2 : ℝ) ^ ((γ * Nat.log 2 n) / 2) - 1) := by
  have htwoy : 2 * y ≤ γ * Nat.log 2 n := by
    unfold Phase3Entry at hentry
    omega
  have hy : y ≤ (γ * Nat.log 2 n) / 2 := by omega
  by_cases hregion : Phase3Region n x
  · rw [phase3StoppedPotential_of_mem hregion, phase3Potential_apply hpop]
    exact ENNReal.ofReal_le_ofReal
      (sub_le_sub_right (pow_le_pow_right₀ (by norm_num) hy) 1)
  · rw [phase3StoppedPotential_of_not_mem hregion]
    exact bot_le

/-- The reconciled endgame reaches all-`X` consensus with the sum of the
corrected-potential error and the additive Feller escape error.  The two
boundary equations are arithmetic certificates, not residual hypotheses. -/
theorem phase3_reaches_reconciled
    (C₃ n γ aLo bHi : ℕ) (h3 : 3 ≤ n) (hγ : 1 ≤ γ)
    (hsize : 6 * γ * Nat.log 2 n ≤ n)
    (haLo : aLo + γ * Nat.log 2 n + 1 = n)
    (hbHi : bHi + 1 = γ * Nat.log 2 n) :
    Reaches (triChain n) (phase3Horizon C₃ n) (Phase3Entry n γ)
      (IsXMajority n) (phase3ReconciledError C₃ n γ aLo bHi) := by
  intro x hentry
  obtain ⟨y, k, hpop, hk, hdynamic⟩ :=
    Phase3Reconciled.phase3_escape_le_feller
      n γ (phase3Horizon C₃ n) x aLo bHi h3 hγ hsize hentry haLo hbHi
  have hbuffer := phase3Entry_buffered hpop hentry hsize
  have hy : y ≤ (γ * Nat.log 2 n) / 2 := by omega
  have hkmin : (γ * Nat.log 2 n) / 2 + 1 ≤ k := by omega
  have hsize' : 6 * (γ * Nat.log 2 n) ≤ n := by
    simpa only [Nat.mul_assoc] using hsize
  have hthreshold := phase3_reconciled_threshold_two n γ h3 hγ hsize
  have haLoPos : 0 < aLo := by omega
  have hbHiPos : 0 < bHi := by omega
  have hmajority : bHi ≤ aLo := by omega
  have haLoCast : (aLo : ℝ≥0∞) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    omega
  have haLoTop : (aLo : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top aLo
  have hbase : (bHi : ℝ≥0∞) / (aLo : ℝ≥0∞) ≤ 1 := by
    calc
      (bHi : ℝ≥0∞) / (aLo : ℝ≥0∞) ≤
          (aLo : ℝ≥0∞) / (aLo : ℝ≥0∞) :=
        ENNReal.div_le_div_right (Nat.cast_le.mpr hmajority) _
      _ = 1 := ENNReal.div_self haLoCast haLoTop
  have hpotential :
      expect (iter (phase3Stop n) (phase3Horizon C₃ n) x)
          (phase3StoppedPotential n) ≤
        phase3ReconciledPotentialError C₃ n γ := by
    calc
      expect (iter (phase3Stop n) (phase3Horizon C₃ n) x)
          (phase3StoppedPotential n) ≤
          phase3Factor n ^ phase3Horizon C₃ n *
            phase3StoppedPotential n x :=
        phase3Stop_expect_iter_le n (phase3Horizon C₃ n) x h3
      _ ≤ phase3Factor n ^ phase3Horizon C₃ n *
          ENNReal.ofReal ((2 : ℝ) ^ ((γ * Nat.log 2 n) / 2) - 1) :=
        mul_le_mul_right (phase3StoppedPotential_entry_le hpop hentry) _
      _ = phase3ReconciledPotentialError C₃ n γ := rfl
  have hescapeExact : phase3EscapeMass n (phase3Horizon C₃ n) x ≤
      ((bHi : ℝ≥0∞) / (aLo : ℝ≥0∞)) ^ k :=
    (phase3EscapeMass_le_reconciled_hitProb h3 hentry.1 hsize haLo).trans
      hdynamic
  have hescape : phase3EscapeMass n (phase3Horizon C₃ n) x ≤
      phase3ReconciledFellerError n γ aLo bHi := by
    exact hescapeExact.trans (by
      unfold phase3ReconciledFellerError
      exact pow_le_pow_right_of_le_one' hbase hkmin)
  calc
    (∑' z, if IsXMajority n z then 0 else
        iter (triChain n) (phase3Horizon C₃ n) x z) ≤
        expect (iter (phase3Stop n) (phase3Horizon C₃ n) x)
            (phase3StoppedPotential n) +
          phase3EscapeMass n (phase3Horizon C₃ n) x :=
      phase3_failure_le_expect_add_escape n (phase3Horizon C₃ n) x h3
    _ ≤ phase3ReconciledPotentialError C₃ n γ +
        phase3ReconciledFellerError n γ aLo bHi :=
      add_le_add hpotential hescape
    _ = phase3ReconciledError C₃ n γ aLo bHi := rfl

#print axioms phase3_reconciled_threshold_two
#print axioms phase3Stop_reconciled_freeze
#print axioms phase3EscapeMass_le_reconciled_hitProb
#print axioms Phase3Reconciled.phase3_escape_le_feller
#print axioms phase3StoppedPotential_entry_le
#print axioms phase3_reaches_reconciled

end Tri
