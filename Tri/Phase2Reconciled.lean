/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.PhaseGlue
import Tri.ReconciledRegions

/-!
# The reconciled phase-2 ladder

The phase-2 ladder stops at the first dyadic checkpoint whose minority bound is
at most half of `gamma * lg n`.  This is early enough to avoid the terminal
`y = 1` stage and strong enough to produce `Phase3Entry`.  The existing
`Phase2Bridge` at exactly that stopping count supplies the single genuine
probabilistic residual, with no certificate required beyond the handoff.
-/

namespace Tri

open scoped ENNReal

/-- At the logarithmic stage, the dyadic quotient is zero and hence satisfies
the reconciled half-threshold. -/
theorem phase2StageCount_log_witness (n γ : ℕ) :
    2 * (n / 2 ^ (2 + Nat.log 2 n)) ≤ γ * Nat.log 2 n := by
  have hlt : n < 2 ^ (Nat.log 2 n + 1) := by
    simpa using Nat.lt_pow_succ_log_self (by norm_num : 1 < (2 : ℕ)) n
  have hpow : 2 ^ (Nat.log 2 n + 1) ≤ 2 ^ (2 + Nat.log 2 n) := by
    exact Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) (by omega)
  have hzero : n / 2 ^ (2 + Nat.log 2 n) = 0 :=
    Nat.div_eq_of_lt (hlt.trans_le hpow)
  simp [hzero]

/-- A reconciled stopping stage exists for every population and parameter. -/
theorem phase2StageCount_exists (n γ : ℕ) :
    ∃ k, 2 * (n / 2 ^ (2 + k)) ≤ γ * Nat.log 2 n :=
  ⟨Nat.log 2 n, phase2StageCount_log_witness n γ⟩

/-- The least number of phase-2 halving stages whose final dyadic minority
bound is at most half of `gamma * lg n`. -/
def phase2StageCount (n γ : ℕ) : ℕ :=
  Nat.find (phase2StageCount_exists n γ)

/-- The selected stage count satisfies its defining half-threshold. -/
theorem phase2StageCount_spec (n γ : ℕ) :
    2 * (n / 2 ^ (2 + phase2StageCount n γ)) ≤
      γ * Nat.log 2 n :=
  Nat.find_spec (phase2StageCount_exists n γ)

/-- The reconciled phase-2 ladder never uses more than `lg n` stages. -/
theorem phase2StageCount_le_log (n γ : ℕ) :
    phase2StageCount n γ ≤ Nat.log 2 n := by
  apply Nat.find_le
  exact phase2StageCount_log_witness n γ

/-- A dyadic checkpoint at the reconciled half-threshold lies in the buffered
phase-3 entry region. -/
theorem phase2_stage_to_phase3Entry {n γ s x : ℕ}
    (hthreshold : 2 * (n / 2 ^ s) ≤ γ * Nat.log 2 n)
    (hx : Phase2Stage n s x) : Phase3Entry n γ x := by
  constructor
  · exact hx.1
  · have hk : 0 < 2 ^ s := by positivity
    have hxnZ : (x : ℤ) ≤ n := by
      exact_mod_cast hx.1
    have hstageZ : ((2 ^ s : ℕ) : ℤ) * n ≤
        ((2 ^ s : ℕ) : ℤ) * x + n := by
      exact_mod_cast hx.2
    have hmulZ : ((2 ^ s : ℕ) : ℤ) * ((n : ℤ) - x) ≤ n := by
      nlinarith
    have hmul : 2 ^ s * (n - x) ≤ n := by
      have hsubZ : (((n - x : ℕ) : ℤ)) = (n : ℤ) - x :=
        Nat.cast_sub hx.1
      exact_mod_cast
        (show ((2 ^ s : ℕ) : ℤ) * ((n - x : ℕ) : ℤ) ≤ n by
          rw [hsubZ]
          exact hmulZ)
    have hminority : n - x ≤ n / 2 ^ s := by
      apply (Nat.le_div_iff_mul_le hk).2
      simpa [mul_comm] using hmul
    have hdouble : 2 * (n - x) ≤ γ * Nat.log 2 n :=
      (Nat.mul_le_mul_left 2 hminority).trans hthreshold
    omega

/-- The generic phase-2 ladder at `phase2StageCount` reaches the buffered
phase-3 entry predicate.  A single `Phase2Bridge` supplies precisely the
stopped-recurrence and escape data for the selected stages. -/
theorem phase2_reaches_buffered (n γ : ℕ)
    (B : Phase2Bridge n (phase2StageCount n γ)) :
    Reaches (triChain n) (phase2StageCount n γ * (4 * n))
      (Phase1Exit n) (Phase3Entry n γ)
      (∑ i ∈ Finset.range (phase2StageCount n γ),
        phase2StageError n (2 + i)) := by
  let k := phase2StageCount n γ
  have hrungs : ∀ i < k,
      Reaches (triChain n) (4 * n) (Phase2Stage n (2 + i))
        (Phase2Stage n (2 + (i + 1))) (phase2StageError n (2 + i)) := by
    intro i hi
    simpa [Nat.add_assoc] using
      phase2_halving_stage n (2 + i) (by omega) (B.V i)
        (B.hV0 i hi) (B.hVstep i hi) (B.hfail i hi)
  have hchain := Reaches.chain
    (K := triChain n) (P := fun i => Phase2Stage n (2 + i))
    (T := fun _ => 4 * n) (ε := fun i => phase2StageError n (2 + i)) hrungs
  have hchain' :
      Reaches (triChain n) (k * (4 * n)) (Phase2Stage n 2)
        (Phase2Stage n (2 + k))
        (∑ i ∈ Finset.range k, phase2StageError n (2 + i)) := by
    simpa using hchain
  have hpost := hchain'.mono_post (fun z hz =>
    phase2_stage_to_phase3Entry (phase2StageCount_spec n γ) hz)
  intro x hx
  exact hpost x (phase1_exit_to_phase2_stage hx)

#print axioms phase2StageCount_log_witness
#print axioms phase2StageCount_exists
#print axioms phase2StageCount_spec
#print axioms phase2StageCount_le_log
#print axioms phase2_stage_to_phase3Entry
#print axioms phase2_reaches_buffered

end Tri
