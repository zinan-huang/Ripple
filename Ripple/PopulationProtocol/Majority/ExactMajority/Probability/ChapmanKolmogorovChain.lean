/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `CKChainBound` — generic finite Chapman–Kolmogorov union over a chain of gated steps (C5c keystone).

The honest Phase-5 / Theorem-6.2 closes (Main-profile confinement over the `O(L)` hours, and the
Main-count floor over Phase-1→5) are NOT pointwise facts at a synthetic config — `Phase5AllWin` is
NOT kernel-closed (`Phase5ClosureFalse`).  They are finite CK unions: a sequence of "good" gates
`Good 0 → Good 1 → … → Good H`, each transition supplied by a per-step block tail
`(κ^hourLen i) y {¬ Good (i+1)} ≤ ηhour i` on the `Good i` states, composed into

  `(κ^(∑ hourLen)) c₀ {¬ Good H} ≤ ∑ ηhour i`.

This file provides the GENERIC, kernel-agnostic plumbing: `ck_bad_extend` (one CK extension step) and
`ck_chain_bad_bound` (the finite iteration), reused by both Brick-A (confinement) and the Main-floor.
The genuine probabilistic content stays in the per-step tails the caller supplies.

NEW file; no existing file edited; no sorry/admit/axiom/native_decide.
Provenance: ChatGPT (family3 task f31c7abd) draft on core C5c, audited against `0f7a9c4`; the
`kernel_pow_le_one` it assumed does not exist as a public lemma — replaced here by `prob_le_one`
under a local kernel-power Markov instance.
Reference: `AUDIT_HEADLINE_THEOREMS.md` (core C5c); Doty et al. (arXiv:2106.10201v2) §6 Thm 6.2 / §7.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ExpectedHitting

namespace ExactMajority

namespace ChapmanKolmogorovChain

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators NNReal

variable {α : Type*} [MeasurableSpace α] [DiscreteMeasurableSpace α]

omit [DiscreteMeasurableSpace α] in
/-- Kernel powers of a Markov kernel are Markov (not found by instance search). -/
theorem isMarkov_pow (κ : Kernel α α) [IsMarkovKernel κ] (m : ℕ) :
    IsMarkovKernel (κ ^ m) := by
  induction m with
  | zero => rw [pow_zero]; exact inferInstanceAs (IsMarkovKernel (Kernel.id : Kernel α α))
  | succ s ih => haveI := ih; rw [pow_succ]; exact inferInstanceAs (IsMarkovKernel ((κ ^ s) ∘ₖ κ))

/-- **One CK extension step.**  If the mass outside `A` at time `m` is `≤ ε`, and from every
`A`-state an `s`-block misses `B` with probability `≤ η`, then the mass outside `B` at time `m + s`
is `≤ ε + η`. -/
theorem ck_bad_extend
    (κ : Kernel α α) [IsMarkovKernel κ]
    (A B : α → Prop)
    (m s : ℕ) (c₀ : α) (ε η : ℝ≥0∞)
    (hprev : (κ ^ m) c₀ {x | ¬ A x} ≤ ε)
    (hstep : ∀ y, A y → (κ ^ s) y {x | ¬ B x} ≤ η) :
    (κ ^ (m + s)) c₀ {x | ¬ B x} ≤ ε + η := by
  classical
  haveI := isMarkov_pow κ m
  haveI := isMarkov_pow κ s
  have hBadB : MeasurableSet {x : α | ¬ B x} :=
    DiscreteMeasurableSpace.forall_measurableSet _
  have hBadA : MeasurableSet {x : α | ¬ A x} :=
    DiscreteMeasurableSpace.forall_measurableSet _
  have hGoodA : MeasurableSet {x : α | A x} :=
    DiscreteMeasurableSpace.forall_measurableSet _
  rw [Kernel.pow_add_apply_eq_lintegral κ m s c₀ hBadB]
  calc
    ∫⁻ y, (κ ^ s) y {x | ¬ B x} ∂((κ ^ m) c₀)
        ≤ ∫⁻ y,
            (Set.indicator {x | ¬ A x} (fun _ => (1 : ℝ≥0∞)) y
              + Set.indicator {x | A x} (fun _ => η) y)
            ∂((κ ^ m) c₀) := by
          apply lintegral_mono
          intro y
          dsimp only
          by_cases hy : A y
          · have hyBad : y ∉ {x : α | ¬ A x} := by simpa using hy
            have hyGood : y ∈ {x : α | A x} := by simpa using hy
            rw [Set.indicator_of_notMem hyBad, Set.indicator_of_mem hyGood]
            simpa using hstep y hy
          · have hyBad : y ∈ {x : α | ¬ A x} := by simpa using hy
            have hyGood : y ∉ {x : α | A x} := by simpa using hy
            rw [Set.indicator_of_mem hyBad, Set.indicator_of_notMem hyGood]
            simpa using (prob_le_one : (κ ^ s) y {x | ¬ B x} ≤ 1)
    _ = (κ ^ m) c₀ {x | ¬ A x} + η * (κ ^ m) c₀ {x | A x} := by
          rw [lintegral_add_left (measurable_const.indicator hBadA)]
          rw [lintegral_indicator hBadA, lintegral_indicator hGoodA]
          simp
    _ ≤ ε + η := by
          have hAone : (κ ^ m) c₀ {x | A x} ≤ 1 := prob_le_one
          calc
            (κ ^ m) c₀ {x | ¬ A x} + η * (κ ^ m) c₀ {x | A x}
                ≤ ε + η * 1 := add_le_add hprev (by gcongr)
            _ = ε + η := by simp

/-- Cumulative prefix length of a sequence of hour lengths. -/
def hourPrefix (hourLen : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => hourPrefix hourLen k + hourLen k

/-- **The finite CK chain bound.**  A sequence of good gates `Good 0 → … → Good H`, each transition
supplied by a per-step block tail on `Good i`, composes into a union bound over the prefix horizon. -/
theorem ck_chain_bad_bound
    (κ : Kernel α α) [IsMarkovKernel κ]
    (Good : ℕ → α → Prop) (hourLen : ℕ → ℕ) (ηhour : ℕ → ℝ≥0∞)
    (htails : ∀ i, ∀ y, Good i y → (κ ^ hourLen i) y {x | ¬ Good (i + 1) x} ≤ ηhour i)
    (c₀ : α) (hGood0 : Good 0 c₀) (H : ℕ) :
    (κ ^ hourPrefix hourLen H) c₀ {x | ¬ Good H x} ≤ ∑ i ∈ Finset.range H, ηhour i := by
  classical
  induction H with
  | zero =>
      rw [hourPrefix, show (κ ^ 0 : Kernel α α) = Kernel.id from pow_zero κ, Kernel.id_apply,
        Measure.dirac_apply' c₀ (DiscreteMeasurableSpace.forall_measurableSet _)]
      have hc₀ : c₀ ∉ {x : α | ¬ Good 0 x} := by simpa using hGood0
      simp [hc₀]
  | succ H ih =>
      have hCK :=
        ck_bad_extend κ (Good H) (Good (H + 1))
          (hourPrefix hourLen H) (hourLen H) c₀
          (∑ i ∈ Finset.range H, ηhour i) (ηhour H)
          ih (htails H)
      have hpref : hourPrefix hourLen (H + 1) = hourPrefix hourLen H + hourLen H := rfl
      rw [hpref, Finset.sum_range_succ]
      exact hCK

/-- **The finite CK chain bound, bounded-index form.**  Same as `ck_chain_bad_bound` but the per-step
tails are only required for the `H` real steps (`∀ i < H`), so the caller need not supply atoms past
the horizon.  This is the form the Phase-5/Thm-6.2 hour iteration consumes. -/
theorem ck_chain_bad_bound_lt
    (κ : Kernel α α) [IsMarkovKernel κ]
    (Good : ℕ → α → Prop) (hourLen : ℕ → ℕ) (ηhour : ℕ → ℝ≥0∞)
    (c₀ : α) (hGood0 : Good 0 c₀) (H : ℕ) :
    (∀ i, i < H → ∀ y, Good i y → (κ ^ hourLen i) y {x | ¬ Good (i + 1) x} ≤ ηhour i) →
      (κ ^ hourPrefix hourLen H) c₀ {x | ¬ Good H x} ≤ ∑ i ∈ Finset.range H, ηhour i := by
  induction H with
  | zero =>
      intro _
      rw [hourPrefix, show (κ ^ 0 : Kernel α α) = Kernel.id from pow_zero κ, Kernel.id_apply,
        Measure.dirac_apply' c₀ (DiscreteMeasurableSpace.forall_measurableSet _)]
      have hc₀ : c₀ ∉ {x : α | ¬ Good 0 x} := by simpa using hGood0
      simp [hc₀]
  | succ H ih =>
      intro htails
      have hprev := ih (fun i hi => htails i (Nat.lt_succ_of_lt hi))
      have hCK :=
        ck_bad_extend κ (Good H) (Good (H + 1))
          (hourPrefix hourLen H) (hourLen H) c₀
          (∑ i ∈ Finset.range H, ηhour i) (ηhour H)
          hprev (htails H (Nat.lt_succ_self H))
      have hpref : hourPrefix hourLen (H + 1) = hourPrefix hourLen H + hourLen H := rfl
      rw [hpref, Finset.sum_range_succ]
      exact hCK

end ChapmanKolmogorovChain

end ExactMajority
