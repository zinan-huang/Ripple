/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Compose

/-!
# Indexed composition of reachability bounds

This module composes a heterogeneous family of finite-horizon reachability
bounds.  Each rung may have its own precondition, postcondition, horizon, and
failure bound.  It also records the two elementary weakening rules needed when
successive rung predicates or error estimates are not stated in exactly the
same form.

## Main results

* `Reaches.chain` composes an indexed family of rungs.
* `Reaches.mono_error` weakens the failure bound.
* `Reaches.mono_post` weakens the postcondition.
* `Reaches.chain_uniform` bounds a ladder with uniform horizons and errors.
-/

namespace Tri

open scoped ENNReal

variable {α : Type*}

/-- An indexed family of successive reachability bounds composes by summing
its horizons and failure bounds. -/
theorem Reaches.chain {K : α → PMF α} {P : ℕ → α → Prop}
    [∀ i, DecidablePred (P i)] {T : ℕ → ℕ} {ε : ℕ → ℝ≥0∞} {k : ℕ}
    (h : ∀ i < k, Reaches K (T i) (P i) (P (i + 1)) (ε i)) :
    Reaches K (∑ i ∈ Finset.range k, T i) (P 0) (P k)
      (∑ i ∈ Finset.range k, ε i) := by
  induction k with
  | zero =>
      simp only [Finset.range_zero, Finset.sum_empty]
      intro s hs
      rw [tsum_eq_single s (by
        intro z hzs
        simp [iter, PMF.pure_apply, hzs])]
      simp [hs]
  | succ k ih =>
      have hprefix : ∀ i < k,
          Reaches K (T i) (P i) (P (i + 1)) (ε i) :=
        fun i hi => h i (Nat.lt_trans hi (Nat.lt_succ_self k))
      have hlast : Reaches K (T k) (P k) (P (k + 1)) (ε k) :=
        h k (Nat.lt_succ_self k)
      simpa only [Finset.sum_range_succ] using (ih hprefix).comp hlast

/-- Increasing the allowed failure bound preserves a reachability result. -/
theorem Reaches.mono_error {K : α → PMF α} {P Q : α → Prop}
    [DecidablePred Q] {T : ℕ} {ε ε' : ℝ≥0∞} (h : Reaches K T P Q ε)
    (hε : ε ≤ ε') : Reaches K T P Q ε' := by
  intro s hs
  exact (h s hs).trans hε

/-- Enlarging the postcondition preserves a reachability result. -/
theorem Reaches.mono_post {K : α → PMF α} {P Q R : α → Prop}
    [DecidablePred Q] [DecidablePred R] {T : ℕ} {ε : ℝ≥0∞}
    (h : Reaches K T P Q ε) (hQR : ∀ z, Q z → R z) :
    Reaches K T P R ε := by
  intro s hs
  calc
    ∑' z, (if R z then 0 else iter K T s z) ≤
        ∑' z, (if Q z then 0 else iter K T s z) := by
          refine ENNReal.tsum_le_tsum fun z => ?_
          by_cases hz : Q z
          · simp [hz, hQR z hz]
          · by_cases hr : R z <;> simp [hz, hr]
    _ ≤ ε := h s hs

/-- Increasing the horizon preserves a reachability bound when the target is
closed under every finite continuation of the kernel. -/
theorem Reaches.mono_horizon_of_closed
    {K : α → PMF α} {P Q : α → Prop}
    [DecidablePred Q] {T U : ℕ} {ε : ℝ≥0∞}
    (h : Reaches K T P Q ε)
    (hTU : T ≤ U)
    (hclosed : ∀ s, Q s → ∀ V z, iter K V s z ≠ 0 → Q z) :
    Reaches K U P Q ε := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hTU
  have hstay : Reaches K d Q Q 0 := by
    intro s hs
    have hzero :
        (∑' z, if Q z then 0 else iter K d s z) = 0 := by
      rw [ENNReal.tsum_eq_zero]
      intro z
      by_cases hz : Q z
      · simp [hz]
      · have hziter : iter K d s z = 0 := by
          by_contra hne
          exact hz (hclosed s hs d z hne)
        simp [hz, hziter]
    rw [hzero]
  simpa using h.comp hstay

/-- If every rung has the same horizon and at most the same failure bound, an
indexed ladder of length `k` takes `k * T₀` steps and fails with probability at
most `k * ε₀`. -/
theorem Reaches.chain_uniform {K : α → PMF α} {P : ℕ → α → Prop}
    [∀ i, DecidablePred (P i)] {T : ℕ → ℕ} {ε : ℕ → ℝ≥0∞}
    {k T₀ : ℕ} {ε₀ : ℝ≥0∞}
    (h : ∀ i < k, Reaches K (T i) (P i) (P (i + 1)) (ε i))
    (hT : ∀ i < k, T i = T₀) (hε : ∀ i < k, ε i ≤ ε₀) :
    Reaches K (k * T₀) (P 0) (P k) (k * ε₀) := by
  have hTsum : ∑ i ∈ Finset.range k, T i = k * T₀ := by
    calc
      ∑ i ∈ Finset.range k, T i = ∑ _i ∈ Finset.range k, T₀ := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hT i (Finset.mem_range.mp hi)
      _ = k * T₀ := by simp
  have hεsum : ∑ i ∈ Finset.range k, ε i ≤ k * ε₀ := by
    calc
      ∑ i ∈ Finset.range k, ε i ≤ ∑ _i ∈ Finset.range k, ε₀ := by
        apply Finset.sum_le_sum
        intro i hi
        exact hε i (Finset.mem_range.mp hi)
      _ = k * ε₀ := by simp
  have hchain := Reaches.chain (K := K) (P := P) (T := T) (ε := ε) h
  rw [hTsum] at hchain
  exact hchain.mono_error hεsum

end Tri

#print axioms Tri.Reaches.mono_horizon_of_closed
