/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Assembly
import Tri.ReconciledRegions
import Tri.Statement
import Tri.Phase1Refactored
import Tri.PhaseGlue
import Tri.Schedule
import Tri.Phase3Feller
import Tri.BudgetArith
import Tri.FinalN0
import Tri.Phase2Additive
import Tri.Phase2AdditiveBudget

/-!
# The reconciled end-to-end assembly

`theorem1b_of_phases` (in `Tri.Assembly`) composes three phase reachability
facts whose intermediate regions are `Phase1Exit` and `Phase2Exit`.  The
reconciled phase-2/phase-3 ladders instead hand off through the *buffered*
region `Phase3Entry n γ` (minority `≤ γ lg n / 2`), which is strictly inside
`Phase2Exit n γ` (minority `≤ γ lg n`).  The buffer is what gives phase 3 the
head-room its endgame analysis needs.

`theorem1b_of_reconciled` is the exact analogue of `theorem1b_of_phases` with
that stronger intermediate region.  Its body is identical — the composition is
generic in the hand-off predicates — but it is the interface the reconciled
ladders actually satisfy.  Discharging its five inputs from the proved
phase lemmas is the remaining work; this theorem fixes the target shape.
-/

namespace Tri

open scoped ENNReal

/-- **Theorem 1(b) from the reconciled phase reachabilities.**

Identical to `theorem1b_of_phases` except that phases 2 and 3 hand off through
the buffered region `Phase3Entry n γ` rather than `Phase2Exit n γ`.  The
composition, padding to the exact horizon `C γ n lg n`, and the absorbing
consensus argument are unchanged; only the intermediate predicate differs. -/
theorem theorem1b_of_reconciled
    (C n₀ : ℕ) (c : ℝ)
    (T₁ T₂ T₃ : ℕ → ℕ → ℕ)
    (ε₁ ε₂ ε₃ : ℕ → ℕ → ℝ≥0∞)
    (hC : 0 < C) (hc : 0 < c) (hn₀ : 3 ≤ n₀)
    (hphase1 : ∀ n γ : ℕ, n₀ ≤ n → 1 ≤ γ →
      6 * γ * Nat.log 2 n ≤ n →
      Reaches (triChain n) (T₁ n γ) (AssemblyInitial n γ) (Phase1Exit n)
        (ε₁ n γ))
    (hphase2 : ∀ n γ : ℕ, n₀ ≤ n → 1 ≤ γ →
      6 * γ * Nat.log 2 n ≤ n →
      Reaches (triChain n) (T₂ n γ) (Phase1Exit n) (Phase3Entry n γ)
        (ε₂ n γ))
    (hphase3 : ∀ n γ : ℕ, n₀ ≤ n → 1 ≤ γ →
      6 * γ * Nat.log 2 n ≤ n →
      Reaches (triChain n) (T₃ n γ) (Phase3Entry n γ) (IsXMajority n)
        (ε₃ n γ))
    (hschedule : ∀ n γ : ℕ, n₀ ≤ n → 1 ≤ γ →
      6 * γ * Nat.log 2 n ≤ n →
      ∃ U : ℕ, T₁ n γ + T₂ n γ + T₃ n γ + U =
        C * γ * n * Nat.log 2 n)
    (hbudget : ∀ n γ : ℕ, n₀ ≤ n → 1 ≤ γ →
      6 * γ * Nat.log 2 n ≤ n →
      ε₁ n γ + ε₂ n γ + ε₃ n γ ≤
        (n : ℝ≥0∞)⁻¹ ^ (c * (γ : ℝ))) :
    Theorem1b_statement := by
  refine ⟨C, n₀, c, hC, hc, hn₀, ?_⟩
  intro n γ x₀ hn hγ hsize hx hgap
  have hreach := Reaches.three
    (hphase1 n γ hn hγ hsize)
    (hphase2 n γ hn hγ hsize)
    (hphase3 n γ hn hγ hsize)
  obtain ⟨U, hU⟩ := hschedule n γ hn hγ hsize
  have hpadded := hreach.pad_of_absorbing (fun s hs => by
    apply consensus_absorbing n s
    right
    exact hs) U
  rw [hU] at hpadded
  exact (hpadded x₀ ⟨hx, hgap⟩).trans (hbudget n γ hn hγ hsize)

/-- **Theorem 1(b) with the phase-1 ladder discharged.**

The phase-1 reachability is supplied by `phase1_reaches_refactored`, so the
phase-1 input collapses to its single genuine residual: the per-rung envelope
estimate `Phase1RefactoredRungBound`, which the paper's Feller-safety plus
Chernoff-progress rung analysis (`phase1_refactored_band_rung_raw` →
`band_rung_bound`) discharges.  What remains open are the phase-2 reconciled
reachability (through `Phase3Entry`), the exact-horizon schedule, and the scalar
error budget — no other probabilistic content. -/
theorem theorem1b_reconciled_reduced
    (C₁ C n₀ : ℕ) (c : ℝ)
    (T₂ T₃ : ℕ → ℕ → ℕ) (ε₂ ε₃ : ℕ → ℕ → ℝ≥0∞)
    (hC : 0 < C) (hc : 0 < c) (hn₀ : 3 ≤ n₀)
    (hn₀log : ∀ n : ℕ, n₀ ≤ n → 12 ≤ Nat.log 2 n)
    (hphase1rung : ∀ n γ : ℕ, n₀ ≤ n → 1 ≤ γ →
      6 * γ * Nat.log 2 n ≤ n → Phase1RefactoredRungBound C₁ n γ)
    (hphase2 : ∀ n γ : ℕ, n₀ ≤ n → 1 ≤ γ →
      6 * γ * Nat.log 2 n ≤ n →
      Reaches (triChain n) (T₂ n γ) (Phase1Exit n) (Phase3Entry n γ)
        (ε₂ n γ))
    (hphase3 : ∀ n γ : ℕ, n₀ ≤ n → 1 ≤ γ →
      6 * γ * Nat.log 2 n ≤ n →
      Reaches (triChain n) (T₃ n γ) (Phase3Entry n γ) (IsXMajority n)
        (ε₃ n γ))
    (hschedule : ∀ n γ : ℕ, n₀ ≤ n → 1 ≤ γ →
      6 * γ * Nat.log 2 n ≤ n →
      ∃ U : ℕ, phase1Horizon C₁ n γ + T₂ n γ + T₃ n γ + U =
        C * γ * n * Nat.log 2 n)
    (hbudget : ∀ n γ : ℕ, n₀ ≤ n → 1 ≤ γ →
      6 * γ * Nat.log 2 n ≤ n →
      phase1RefactoredError C₁ n γ + ε₂ n γ + ε₃ n γ ≤
        (n : ℝ≥0∞)⁻¹ ^ (c * (γ : ℝ))) :
    Theorem1b_statement :=
  theorem1b_of_reconciled C n₀ c
    (phase1Horizon C₁) T₂ T₃
    (phase1RefactoredError C₁) ε₂ ε₃
    hC hc hn₀
    (fun n γ hn hγ hsize =>
      phase1_reaches_refactored C₁ n γ (hn₀log n hn) hγ
        (hphase1rung n γ hn hγ hsize))
    hphase2 hphase3 hschedule hbudget

/-- **Theorem 1(b) with the schedule discharged.**  Fixing the three reconciled
horizons (`C₁ γ n lg n`, `8 n · phase2StageCount`, `16 γ n lg n`), the schedule
input is supplied by `reconciled_schedule` with `C = C₁ + 24`.  What remains are
exactly the three phase reachabilities and the scalar error budget. -/
theorem theorem1b_of_reconciled_scheduled
    (C₁ n₀ : ℕ) (c : ℝ) (ε₂ ε₃ : ℕ → ℕ → ℝ≥0∞)
    (hc : 0 < c) (hn₀ : 3 ≤ n₀)
    (hphase1 : ∀ n γ : ℕ, n₀ ≤ n → 1 ≤ γ →
      6 * γ * Nat.log 2 n ≤ n →
      Reaches (triChain n) (phase1Horizon C₁ n γ) (AssemblyInitial n γ)
        (Phase1Exit n) (phase1RefactoredError C₁ n γ))
    (hphase2 : ∀ n γ : ℕ, n₀ ≤ n → 1 ≤ γ →
      6 * γ * Nat.log 2 n ≤ n →
      Reaches (triChain n) (8 * n * phase2StageCount n γ) (Phase1Exit n)
        (Phase3Entry n γ) (ε₂ n γ))
    (hphase3 : ∀ n γ : ℕ, n₀ ≤ n → 1 ≤ γ →
      6 * γ * Nat.log 2 n ≤ n →
      Reaches (triChain n) (phase3HorizonScaled 16 n γ) (Phase3Entry n γ)
        (IsXMajority n) (ε₃ n γ))
    (hbudget : ∀ n γ : ℕ, n₀ ≤ n → 1 ≤ γ →
      6 * γ * Nat.log 2 n ≤ n →
      phase1RefactoredError C₁ n γ + ε₂ n γ + ε₃ n γ ≤
        (n : ℝ≥0∞)⁻¹ ^ (c * (γ : ℝ))) :
    Theorem1b_statement :=
  theorem1b_of_reconciled (C₁ + 24) n₀ c
    (phase1Horizon C₁) (fun n γ => 8 * n * phase2StageCount n γ)
    (phase3HorizonScaled 16)
    (phase1RefactoredError C₁) ε₂ ε₃
    (by omega) hc hn₀
    hphase1 hphase2 hphase3
    (fun n γ _ hγ _ => reconciled_schedule C₁ n γ hγ)
    hbudget

/-- **Theorem 1(b) reduced to exactly the two dynamical bridges.**

With `n₀ = 2^420` and `c = 1/100`, every arithmetic and interface obligation is
discharged internally:

* phase 1 via `phase1_reaches_refactored` (from the per-rung bound) and its error
  via `phase1RefactoredError_le_of_log_ge_fortysix`;
* phase 3 via `phase3_reaches_scaled_canonical` and
  `canonicalPhase3Error_le_two_inverse`;
* the schedule via `reconciled_schedule`;
* the budget via `reconciled_budget` fed by `theorem1bN₀_package`.

The ONLY remaining inputs are the two probabilistic constructions: the phase-1
per-rung envelope `Phase1RefactoredRungBound`, and the additive phase-2
reachability with its `6 n⁻¹^(γ/50)` error.  Their precise interfaces are the
three hypotheses displayed in the theorem signature below. -/
theorem theorem1b_reconciled_final
    (C₁ : ℕ) (ε₂ : ℕ → ℕ → ℝ≥0∞)
    (hphase1rung : ∀ n γ : ℕ, 2 ^ 420 ≤ n → 1 ≤ γ →
      6 * γ * Nat.log 2 n ≤ n → Phase1RefactoredRungBound C₁ n γ)
    (hphase2 : ∀ n γ : ℕ, 2 ^ 420 ≤ n → 1 ≤ γ →
      6 * γ * Nat.log 2 n ≤ n →
      Reaches (triChain n) (8 * n * phase2StageCount n γ) (Phase1Exit n)
        (Phase3Entry n γ) (ε₂ n γ))
    (hphase2err : ∀ n γ : ℕ, 2 ^ 420 ≤ n → 1 ≤ γ →
      6 * γ * Nat.log 2 n ≤ n →
      ε₂ n γ ≤ 6 * (n : ℝ≥0∞)⁻¹ ^ ((1 / 50 : ℝ) * (γ : ℝ))) :
    Theorem1b_statement := by
  have hn₀3 : 3 ≤ 2 ^ 420 :=
    le_trans (by norm_num : (3 : ℕ) ≤ 2 ^ 2)
      (Nat.pow_le_pow_right (by norm_num) (by norm_num : 2 ≤ 420))
  refine theorem1b_of_reconciled_scheduled C₁ (2 ^ 420) (1 / 100)
    ε₂ canonicalPhase3Error (by norm_num) hn₀3 ?_ hphase2 ?_ ?_
  · -- phase 1 reachability
    intro n γ hn hγ hsize
    obtain ⟨_, h46, _, _, _, _, _⟩ := theorem1bN₀_package hn hγ
    exact phase1_reaches_refactored C₁ n γ (by omega) hγ
      (hphase1rung n γ hn hγ hsize)
  · -- phase 3 reachability
    intro n γ hn hγ hsize
    obtain ⟨h3, _⟩ := theorem1bN₀_package hn hγ
    exact phase3_reaches_scaled_canonical n γ h3 hγ hsize
  · -- budget
    intro n γ hn hγ hsize
    obtain ⟨h3, h46, _, h8, ht1, ht2, ht3⟩ := theorem1bN₀_package hn hγ
    have hn1 : 1 ≤ n := by omega
    have h1 : phase1RefactoredError C₁ n γ ≤ 4 * (n : ℝ≥0∞)⁻¹ ^ ((1 / 34 : ℝ) * (γ : ℝ)) :=
      phase1RefactoredError_le_of_log_ge_fortysix C₁ n γ h46 hγ
    have h3e : canonicalPhase3Error n γ ≤ 2 * (n : ℝ≥0∞)⁻¹ ^ ((1 : ℝ) * (γ : ℝ)) :=
      canonicalPhase3Error_le_two_inverse n γ h3 hγ hsize h8
    refine reconciled_budget n γ hn1 hγ _ _ _ h1 (hphase2err n γ hn hγ hsize) h3e ?_ ?_ ?_
    · rw [show (1 / 34 : ℝ) * (γ : ℝ) - (1 / 100 : ℝ) * (γ : ℝ)
        = (33 / 1700 : ℝ) * (γ : ℝ) by ring]; exact_mod_cast ht1
    · rw [show (1 / 50 : ℝ) * (γ : ℝ) - (1 / 100 : ℝ) * (γ : ℝ)
        = (1 / 100 : ℝ) * (γ : ℝ) by ring]; exact_mod_cast ht2
    · rw [show (1 : ℝ) * (γ : ℝ) - (1 / 100 : ℝ) * (γ : ℝ)
        = (99 / 100 : ℝ) * (γ : ℝ) by ring]; exact_mod_cast ht3

/-- **Theorem 1(b) with phase 2 fully discharged.**  Both the phase-2
reachability (`phase2_reaches_additive`) and its error bound
(`phase2_additive_error_le`) are proved unconditional, so the entire headline
reduces to the single remaining probabilistic input: the phase-1 per-rung
envelope `Phase1RefactoredRungBound`. -/
theorem theorem1b_reconciled_phase2done (C₁ : ℕ)
    (hphase1rung : ∀ n γ : ℕ, 2 ^ 420 ≤ n → 1 ≤ γ →
      6 * γ * Nat.log 2 n ≤ n → Phase1RefactoredRungBound C₁ n γ) :
    Theorem1b_statement := by
  have hn128 : ∀ n : ℕ, 2 ^ 420 ≤ n → 128 ≤ Nat.log 2 n := fun n hn =>
    Nat.le_log_of_pow_le (by norm_num)
      (le_trans (Nat.pow_le_pow_right (by norm_num) (by norm_num : 128 ≤ 420)) hn)
  have hn96 : ∀ n : ℕ, 2 ^ 420 ≤ n → 96 ≤ n := fun n hn =>
    le_trans (le_trans (by norm_num : (96 : ℕ) ≤ 2 ^ 7)
      (Nat.pow_le_pow_right (by norm_num) (by norm_num : 7 ≤ 420))) hn
  refine theorem1b_reconciled_final C₁
    (fun n γ => ∑ i ∈ Finset.range (phase2StageCount n γ),
      phase2AdditiveRungError n (2 + i))
    hphase1rung ?_ ?_
  · intro n γ hn hγ hsize
    exact phase2_reaches_additive n γ (by have := hn96 n hn; omega) (hn96 n hn) hγ hsize
      (hn128 n hn)
  · intro n γ hn hγ hsize
    exact phase2_additive_error_le n γ hγ (by have := hn96 n hn; omega) (hn96 n hn) hsize
      (hn128 n hn)

end Tri

#print axioms Tri.theorem1b_of_reconciled
#print axioms Tri.theorem1b_reconciled_reduced
#print axioms Tri.theorem1b_of_reconciled_scheduled
#print axioms Tri.theorem1b_reconciled_phase2done
#print axioms Tri.theorem1b_reconciled_final
