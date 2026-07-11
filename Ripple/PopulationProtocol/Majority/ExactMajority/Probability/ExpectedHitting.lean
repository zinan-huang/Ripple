/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Expected Hitting Time on Transition-Kernel Powers (Generic)

A small, protocol-agnostic toolkit for the **expected hitting time** of a target
("Done") set under iteration of a Markov kernel.

The codebase has no pathwise random variable `T`; everything is expressed through
kernel powers `(K ^ t) c S` and event masses in `ℝ≥0∞`. We therefore formalize the
expectation `E[T]` **directly** as the tail-sum

    expectedHitting K c Done  :=  ∑' t, (K ^ t) c Doneᶜ

where `Doneᶜ` is the "not done yet" event. Under the standard identity
`E[T] = ∑_{t ≥ 0} P(T > t)` and `{T > t} = {not done by time t}` this equals the
mean hitting time of `Done`. Everything below is stated and proved about this
`∑'`-quantity, entirely inside `ℝ≥0∞` (so no convergence side conditions arise).

## Conventions

We work over a generic measurable space `α` with a Markov kernel `K : Kernel α α`,
matching the generic style of `PopProtoCommon/Convergence/GeometricDrift.lean`.
This makes every lemma directly applicable to `(NonuniformMajority L K).transitionKernel`
(an `IsMarkovKernel` on `Config Λ`, a `DiscreteMeasurableSpace`).

`Done` is a **fixed** measurable set; the "bad event" family is the constant family
`Bad t = Doneᶜ`, with the monotonicity `P(Bad (t+1)) ≤ P(Bad t)` coming from
absorption of `Done` (Lemma 0). This fixed-set version is all Phase E needs.

## Main results

* `bad_antitone` — `(K^(t+1)) c Doneᶜ ≤ (K^t) c Doneᶜ` from `Done` absorbing.
* `expectedHitting_le_block` — block form `E[T] ≤ s · ∑' k, P(T > k·s)`.
* `expectedHitting_geometric` — uniform per-block success `q` over a `K`-closed
  class containing the start ⟹ `E[T] ≤ s · (1 - q)⁻¹`.
* `expectedHitting_split` — `E[T] ≤ t₀ + ∑' t, P(T > t₀ + t)`.
* `expectedHitting_split_geometric` — the combined `t₀ + δ·s·(1-q)⁻¹`-shape bound
  consumed by Phase E4.
-/

import Ripple.PopulationProtocol.Majority.PopProtoCommon.Convergence.GeometricDrift
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Logic.Equiv.Fin.Basic

namespace ExactMajority

open scoped ENNReal
open MeasureTheory ProbabilityTheory

variable {α : Type*} [MeasurableSpace α]

/-! ## Part 1 — The expected-hitting tail sum and its monotone bad event -/

/-- The **expected hitting time** of the set `Done` under the kernel `K`, started
at `c`, formalized directly as the tail sum `∑' t, P(not done by time t)`.

Under the standard identity `E[T] = ∑_{t ≥ 0} P(T > t)` with `{T > t}` = "Done not
yet hit by step `t`" (i.e. `(K^t) c Doneᶜ`), this `∑'` equals the mean hitting
time of `Done`. All lemmas in this file are about this quantity. -/
noncomputable def expectedHitting (K : Kernel α α) (c : α) (Done : Set α) : ℝ≥0∞ :=
  ∑' t : ℕ, (K ^ t) c Doneᶜ

/-- **Lemma 0 (monotone bad event).** If `Done` is absorbing
(`K x Doneᶜ = 0` for every `x ∈ Done`), then the "not done by time `t`" mass is
antitone in `t`: `(K^(t+1)) c Doneᶜ ≤ (K^t) c Doneᶜ`.

This is what makes the tail family genuinely decreasing, and underlies the block
bound. -/
theorem bad_antitone (K : Kernel α α) [IsMarkovKernel K]
    {Done : Set α} (hDone : MeasurableSet Done)
    (hAbs : ∀ x ∈ Done, K x Doneᶜ = 0)
    (c : α) (t : ℕ) :
    (K ^ (t + 1)) c Doneᶜ ≤ (K ^ t) c Doneᶜ := by
  have hbad : MeasurableSet (Doneᶜ : Set α) := hDone.compl
  rw [Kernel.pow_succ_apply_eq_lintegral K t c hbad]
  -- Pointwise: K b Doneᶜ ≤ 1_{Doneᶜ}(b).  On Done it is 0; on Doneᶜ it is ≤ 1.
  calc ∫⁻ b, K b Doneᶜ ∂((K ^ t) c)
      ≤ ∫⁻ b, Set.indicator Doneᶜ (fun _ => (1 : ℝ≥0∞)) b ∂((K ^ t) c) := by
        apply lintegral_mono
        intro b
        dsimp only
        by_cases hb : b ∈ Done
        · rw [hAbs b hb]
          exact zero_le'
        · have hb' : b ∈ (Doneᶜ : Set α) := hb
          rw [Set.indicator_of_mem hb']
          exact prob_le_one
    _ = (K ^ t) c Doneᶜ := by
        rw [lintegral_indicator hbad]
        simp

/-- General antitonicity: for `s ≤ t`, `(K^t) c Doneᶜ ≤ (K^s) c Doneᶜ`. -/
theorem bad_antitone_le (K : Kernel α α) [IsMarkovKernel K]
    {Done : Set α} (hDone : MeasurableSet Done)
    (hAbs : ∀ x ∈ Done, K x Doneᶜ = 0)
    (c : α) {s t : ℕ} (hst : s ≤ t) :
    (K ^ t) c Doneᶜ ≤ (K ^ s) c Doneᶜ := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hst
  clear hst
  induction d with
  | zero => simp
  | succ d ih =>
      calc (K ^ (s + (d + 1))) c Doneᶜ
          = (K ^ ((s + d) + 1)) c Doneᶜ := by ring_nf
        _ ≤ (K ^ (s + d)) c Doneᶜ := bad_antitone K hDone hAbs c (s + d)
        _ ≤ (K ^ s) c Doneᶜ := ih

/-! ## Part 2 — Tail sum and block form -/

/-- `expectedHitting` unfolds to the tail sum (definitional restatement). -/
theorem expectedHitting_eq_tsum (K : Kernel α α) (c : α) (Done : Set α) :
    expectedHitting K c Done = ∑' t : ℕ, (K ^ t) c Doneᶜ := rfl

/-- **Block form.** For `s ≠ 0`, the expected hitting time is bounded by `s` times
the tail sum sampled on the block boundaries:
`E[T] ≤ s · ∑' k, P(T > k·s)`.

Each `P(T > t)` for `t` in block `k` (i.e. `k·s ≤ t < (k+1)·s`) is bounded by its
block's left endpoint `P(T > k·s)` via antitonicity, and there are `s` units per
block. -/
theorem expectedHitting_le_block (K : Kernel α α) [IsMarkovKernel K]
    {Done : Set α} (hDone : MeasurableSet Done)
    (hAbs : ∀ x ∈ Done, K x Doneᶜ = 0)
    (c : α) (s : ℕ) (hs : s ≠ 0) :
    expectedHitting K c Done ≤ (s : ℝ≥0∞) * ∑' k : ℕ, (K ^ (k * s)) c Doneᶜ := by
  haveI : NeZero s := ⟨hs⟩
  rw [expectedHitting]
  -- Reindex t ↦ (k, j) with t = k·s + j, j < s, via Nat.divModEquiv.
  rw [← Equiv.tsum_eq (Nat.divModEquiv s).symm (fun t => (K ^ t) c Doneᶜ)]
  rw [ENNReal.tsum_prod']
  -- Bound the inner Fin s sum of P(T > k·s + j) by s · P(T > k·s), then pull `s` out.
  have hinner : ∀ k : ℕ,
      ∑' j : Fin s, (K ^ ((Nat.divModEquiv s).symm (k, j))) c Doneᶜ ≤
        (s : ℝ≥0∞) * (K ^ (k * s)) c Doneᶜ := by
    intro k
    have hkey : ∀ j : Fin s,
        (K ^ ((Nat.divModEquiv s).symm (k, j))) c Doneᶜ ≤ (K ^ (k * s)) c Doneᶜ := by
      intro j
      apply bad_antitone_le K hDone hAbs c
      simp only [Nat.divModEquiv_symm_apply]
      omega
    calc ∑' j : Fin s, (K ^ ((Nat.divModEquiv s).symm (k, j))) c Doneᶜ
        ≤ ∑' _ : Fin s, (K ^ (k * s)) c Doneᶜ := ENNReal.tsum_le_tsum hkey
      _ = (s : ℝ≥0∞) * (K ^ (k * s)) c Doneᶜ := by
          rw [ENNReal.tsum_const]
          simp
  calc ∑' (k : ℕ) (j : Fin s), (K ^ ((Nat.divModEquiv s).symm (k, j))) c Doneᶜ
      ≤ ∑' k : ℕ, (s : ℝ≥0∞) * (K ^ (k * s)) c Doneᶜ := ENNReal.tsum_le_tsum hinner
    _ = (s : ℝ≥0∞) * ∑' k : ℕ, (K ^ (k * s)) c Doneᶜ := by rw [ENNReal.tsum_mul_left]

/-! ## Part 3 — Geometric tail from uniform per-block success -/

/-- `Done` absorbing for one step lifts to absorbing for `m` steps:
`(K^m) x Doneᶜ = 0` for every `x ∈ Done`. -/
theorem pow_absorbing (K : Kernel α α) [IsMarkovKernel K]
    {Done : Set α} (hDone : MeasurableSet Done)
    (hAbs : ∀ x ∈ Done, K x Doneᶜ = 0)
    (m : ℕ) {x : α} (hx : x ∈ Done) :
    (K ^ m) x Doneᶜ = 0 := by
  have hbad : MeasurableSet (Doneᶜ : Set α) := hDone.compl
  induction m generalizing x with
  | zero =>
      -- K^0 = id, dirac x; x ∈ Done so x ∉ Doneᶜ.
      rw [show (K ^ 0) = Kernel.id from pow_zero K, Kernel.id_apply,
        Measure.dirac_apply' x hbad]
      have hxc : x ∉ (Doneᶜ : Set α) := by simpa using hx
      simp [hxc]
  | succ m ih =>
      -- Peel the first step: (K^(1+m)) x Doneᶜ = ∫⁻ b, (K^m) b Doneᶜ ∂(K x).
      rw [show m + 1 = 1 + m from by ring,
        Kernel.pow_add_apply_eq_lintegral K 1 m x hbad, pow_one]
      -- The integrand is 0 on Done (by IH) and K x is supported on Done (x ∈ Done).
      rw [lintegral_eq_zero_iff (Kernel.measurable_coe _ hbad)]
      rw [Filter.eventuallyEq_iff_exists_mem]
      refine ⟨Done, ?_, fun b hb => ih hb⟩
      rw [mem_ae_iff]
      have : K x Doneᶜ = 0 := hAbs x hx
      simpa using this

/-- **One-block geometric contraction (from arbitrary base `m`).** If from every
not-yet-done state the `s`-step kernel fails to reach `Done` with probability `≤ q`
(`∀ b ∈ Doneᶜ, (K^s) b Doneᶜ ≤ q`), and `Done` is absorbing, then appending a block
of `s` steps to any base horizon `m` contracts the not-done mass by a factor `q`:
`(K^(m+s)) c₀ Doneᶜ ≤ q · (K^m) c₀ Doneᶜ`. -/
theorem bad_block_contracts_from (K : Kernel α α) [IsMarkovKernel K]
    {Done : Set α} (hDone : MeasurableSet Done)
    (hAbs : ∀ x ∈ Done, K x Doneᶜ = 0)
    (s : ℕ) (q : ℝ≥0∞)
    (hblock : ∀ b ∈ (Doneᶜ : Set α), (K ^ s) b Doneᶜ ≤ q)
    (c₀ : α) (m : ℕ) :
    (K ^ (m + s)) c₀ Doneᶜ ≤ q * (K ^ m) c₀ Doneᶜ := by
  have hbad : MeasurableSet (Doneᶜ : Set α) := hDone.compl
  -- (K^(m + s)) c₀ Doneᶜ = ∫⁻ b, (K^s) b Doneᶜ ∂(K^m c₀).
  rw [Kernel.pow_add_apply_eq_lintegral K m s c₀ hbad]
  -- Pointwise: (K^s) b Doneᶜ ≤ q · 1_{Doneᶜ}(b).  On Done it is 0; on Doneᶜ it is ≤ q.
  calc ∫⁻ b, (K ^ s) b Doneᶜ ∂((K ^ m) c₀)
      ≤ ∫⁻ b, q * Set.indicator Doneᶜ (fun _ => (1 : ℝ≥0∞)) b ∂((K ^ m) c₀) := by
        apply lintegral_mono
        intro b
        dsimp only
        by_cases hb : b ∈ Done
        · rw [pow_absorbing K hDone hAbs s hb]; exact zero_le'
        · have hb' : b ∈ (Doneᶜ : Set α) := hb
          rw [Set.indicator_of_mem hb', mul_one]
          exact hblock b hb'
    _ = q * (K ^ m) c₀ Doneᶜ := by
        rw [lintegral_const_mul q (by
          exact (measurable_const.indicator hbad))]
        congr 1
        rw [lintegral_indicator hbad]
        simp

/-- One-block contraction along the `k·s` grid (special case of
`bad_block_contracts_from`): `(K^((k+1)·s)) c₀ Doneᶜ ≤ q · (K^(k·s)) c₀ Doneᶜ`. -/
theorem bad_block_contracts (K : Kernel α α) [IsMarkovKernel K]
    {Done : Set α} (hDone : MeasurableSet Done)
    (hAbs : ∀ x ∈ Done, K x Doneᶜ = 0)
    (s : ℕ) (q : ℝ≥0∞)
    (hblock : ∀ b ∈ (Doneᶜ : Set α), (K ^ s) b Doneᶜ ≤ q)
    (c₀ : α) (k : ℕ) :
    (K ^ ((k + 1) * s)) c₀ Doneᶜ ≤ q * (K ^ (k * s)) c₀ Doneᶜ := by
  rw [show (k + 1) * s = k * s + s from by ring]
  exact bad_block_contracts_from K hDone hAbs s q hblock c₀ (k * s)

/-- **Geometric tail.** Under uniform per-block success `q` (from every not-done
state, `s` steps fail to finish with probability `≤ q`) and `Done` absorbing,
the `k`-block not-done mass decays geometrically: `(K^(k·s)) c₀ Doneᶜ ≤ q^k`. -/
theorem bad_block_geometric (K : Kernel α α) [IsMarkovKernel K]
    {Done : Set α} (hDone : MeasurableSet Done)
    (hAbs : ∀ x ∈ Done, K x Doneᶜ = 0)
    (s : ℕ) (q : ℝ≥0∞)
    (hblock : ∀ b ∈ (Doneᶜ : Set α), (K ^ s) b Doneᶜ ≤ q)
    (c₀ : α) (k : ℕ) :
    (K ^ (k * s)) c₀ Doneᶜ ≤ q ^ k := by
  induction k with
  | zero =>
      simp only [Nat.zero_mul, pow_zero, pow_zero]
      calc (K ^ 0) c₀ Doneᶜ ≤ (K ^ 0) c₀ Set.univ := measure_mono (Set.subset_univ _)
        _ = 1 := by
            rw [show (K ^ 0) = Kernel.id from pow_zero K, Kernel.id_apply, measure_univ]
  | succ k ih =>
      calc (K ^ ((k + 1) * s)) c₀ Doneᶜ
          ≤ q * (K ^ (k * s)) c₀ Doneᶜ :=
            bad_block_contracts K hDone hAbs s q hblock c₀ k
        _ ≤ q * q ^ k := by gcongr
        _ = q ^ (k + 1) := by rw [pow_succ]; ring

/-- **Geometric expected-hitting bound.** Combining the block form with the
geometric tail: if `Done` is absorbing and from every not-done state the `s`-step
kernel fails with probability `≤ q` (`s ≠ 0`), then
`E[T] ≤ s · (1 - q)⁻¹`.

This is the backup expected-time shape (`s` = block length, `(1-q)⁻¹` = expected
number of blocks) consumed by Phase E2/E4. -/
theorem expectedHitting_geometric (K : Kernel α α) [IsMarkovKernel K]
    {Done : Set α} (hDone : MeasurableSet Done)
    (hAbs : ∀ x ∈ Done, K x Doneᶜ = 0)
    (s : ℕ) (hs : s ≠ 0) (q : ℝ≥0∞)
    (hblock : ∀ b ∈ (Doneᶜ : Set α), (K ^ s) b Doneᶜ ≤ q)
    (c₀ : α) :
    expectedHitting K c₀ Done ≤ (s : ℝ≥0∞) * (1 - q)⁻¹ := by
  calc expectedHitting K c₀ Done
      ≤ (s : ℝ≥0∞) * ∑' k : ℕ, (K ^ (k * s)) c₀ Doneᶜ :=
        expectedHitting_le_block K hDone hAbs c₀ s hs
    _ ≤ (s : ℝ≥0∞) * ∑' k : ℕ, q ^ k := by
        gcongr with k
        exact bad_block_geometric K hDone hAbs s q hblock c₀ k
    _ = (s : ℝ≥0∞) * (1 - q)⁻¹ := by rw [ENNReal.tsum_geometric]

/-! ## Part 4 — Conditioning-free split and combined corollary -/

/-- The `t`-step kernel mass of any set is `≤ 1`. -/
theorem kernel_pow_le_one (K : Kernel α α) [IsMarkovKernel K]
    (t : ℕ) (x : α) (S : Set α) :
    (K ^ t) x S ≤ 1 := by
  calc (K ^ t) x S ≤ (K ^ t) x Set.univ := measure_mono (Set.subset_univ _)
    _ ≤ 1 := by
        induction t with
        | zero =>
            rw [show (K ^ 0) = Kernel.id from pow_zero K, Kernel.id_apply, measure_univ]
        | succ t ih =>
            rw [Kernel.pow_succ_apply_eq_lintegral K t x MeasurableSet.univ]
            calc ∫⁻ y, K y Set.univ ∂((K ^ t) x)
                ≤ ∫⁻ _ : α, (1 : ℝ≥0∞) ∂((K ^ t) x) := by
                    apply lintegral_mono; intro y; simp [measure_univ]
              _ = (K ^ t) x Set.univ := by simp
              _ ≤ 1 := ih

/-- **Conditioning-free split.** For any horizon `t₀`,
`E[T] ≤ t₀ + ∑' t, P(T > t₀ + t)`.

The first `t₀` tail terms are each `≤ 1`; the remaining tail is shifted by `t₀`. -/
theorem expectedHitting_split (K : Kernel α α) [IsMarkovKernel K]
    (c : α) (Done : Set α) (t₀ : ℕ) :
    expectedHitting K c Done ≤
      (t₀ : ℝ≥0∞) + ∑' t : ℕ, (K ^ (t₀ + t)) c Doneᶜ := by
  rw [expectedHitting]
  -- ∑' t, a t = (∑_{i<t₀} a i) + ∑' t, a (t + t₀)
  rw [← ENNReal.summable.sum_add_tsum_nat_add' (f := fun t => (K ^ t) c Doneᶜ) (k := t₀)]
  gcongr
  · -- ∑_{i < t₀} a i ≤ t₀
    calc ∑ i ∈ Finset.range t₀, (K ^ i) c Doneᶜ
        ≤ ∑ _i ∈ Finset.range t₀, (1 : ℝ≥0∞) :=
          Finset.sum_le_sum (fun i _ => kernel_pow_le_one K i c _)
      _ = (t₀ : ℝ≥0∞) := by simp
  · -- ∑' t, a (t + t₀) = ∑' t, a (t₀ + t)
    rw [Nat.add_comm]

/-- **Block form of the shifted tail.** For `s ≠ 0`,
`∑' t, P(T > t₀ + t) ≤ s · ∑' k, P(T > t₀ + k·s)`. Same block argument as
`expectedHitting_le_block`, shifted by the base horizon `t₀`. -/
theorem tail_le_block (K : Kernel α α) [IsMarkovKernel K]
    {Done : Set α} (hDone : MeasurableSet Done)
    (hAbs : ∀ x ∈ Done, K x Doneᶜ = 0)
    (c : α) (t₀ s : ℕ) (hs : s ≠ 0) :
    ∑' t : ℕ, (K ^ (t₀ + t)) c Doneᶜ ≤
      (s : ℝ≥0∞) * ∑' k : ℕ, (K ^ (t₀ + k * s)) c Doneᶜ := by
  haveI : NeZero s := ⟨hs⟩
  rw [← Equiv.tsum_eq (Nat.divModEquiv s).symm (fun t => (K ^ (t₀ + t)) c Doneᶜ)]
  rw [ENNReal.tsum_prod']
  have hinner : ∀ k : ℕ,
      ∑' j : Fin s, (K ^ (t₀ + (Nat.divModEquiv s).symm (k, j))) c Doneᶜ ≤
        (s : ℝ≥0∞) * (K ^ (t₀ + k * s)) c Doneᶜ := by
    intro k
    have hkey : ∀ j : Fin s,
        (K ^ (t₀ + (Nat.divModEquiv s).symm (k, j))) c Doneᶜ ≤
          (K ^ (t₀ + k * s)) c Doneᶜ := by
      intro j
      apply bad_antitone_le K hDone hAbs c
      simp only [Nat.divModEquiv_symm_apply]
      omega
    calc ∑' j : Fin s, (K ^ (t₀ + (Nat.divModEquiv s).symm (k, j))) c Doneᶜ
        ≤ ∑' _ : Fin s, (K ^ (t₀ + k * s)) c Doneᶜ := ENNReal.tsum_le_tsum hkey
      _ = (s : ℝ≥0∞) * (K ^ (t₀ + k * s)) c Doneᶜ := by rw [ENNReal.tsum_const]; simp
  calc ∑' (k : ℕ) (j : Fin s), (K ^ (t₀ + (Nat.divModEquiv s).symm (k, j))) c Doneᶜ
      ≤ ∑' k : ℕ, (s : ℝ≥0∞) * (K ^ (t₀ + k * s)) c Doneᶜ := ENNReal.tsum_le_tsum hinner
    _ = (s : ℝ≥0∞) * ∑' k : ℕ, (K ^ (t₀ + k * s)) c Doneᶜ := by rw [ENNReal.tsum_mul_left]

/-- **Geometric tail from a base horizon.** Under uniform per-block success `q` and
`Done` absorbing, the not-done mass at time `t₀ + k·s` decays geometrically off its
value `δ := P(T > t₀)` at `t₀`: `(K^(t₀ + k·s)) c₀ Doneᶜ ≤ (K^t₀) c₀ Doneᶜ · q^k`. -/
theorem bad_block_geometric_from (K : Kernel α α) [IsMarkovKernel K]
    {Done : Set α} (hDone : MeasurableSet Done)
    (hAbs : ∀ x ∈ Done, K x Doneᶜ = 0)
    (s : ℕ) (q : ℝ≥0∞)
    (hblock : ∀ b ∈ (Doneᶜ : Set α), (K ^ s) b Doneᶜ ≤ q)
    (c₀ : α) (t₀ k : ℕ) :
    (K ^ (t₀ + k * s)) c₀ Doneᶜ ≤ (K ^ t₀) c₀ Doneᶜ * q ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      calc (K ^ (t₀ + (k + 1) * s)) c₀ Doneᶜ
          = (K ^ ((t₀ + k * s) + s)) c₀ Doneᶜ := by rw [show t₀ + (k + 1) * s = (t₀ + k * s) + s from by ring]
        _ ≤ q * (K ^ (t₀ + k * s)) c₀ Doneᶜ :=
            bad_block_contracts_from K hDone hAbs s q hblock c₀ (t₀ + k * s)
        _ ≤ q * ((K ^ t₀) c₀ Doneᶜ * q ^ k) := by gcongr
        _ = (K ^ t₀) c₀ Doneᶜ * q ^ (k + 1) := by rw [pow_succ]; ring

/-- **Combined split + geometric corollary** (the exact shape Phase E4 consumes).

Suppose `Done` is absorbing and from every not-done state the `s`-step kernel
(`s ≠ 0`) fails to finish with probability `≤ q`. If, in addition, the not-done
mass at a horizon `t₀` is at most `δ` (`(K^t₀) c₀ Doneᶜ ≤ δ`), then

    E[T] ≤ t₀ + δ · s · (1 - q)⁻¹.

Here `t₀ = O(log n)` is the good-event horizon, `δ` is the whp failure
probability, and `s · (1-q)⁻¹` is the backup expected time. -/
theorem expectedHitting_split_geometric (K : Kernel α α) [IsMarkovKernel K]
    {Done : Set α} (hDone : MeasurableSet Done)
    (hAbs : ∀ x ∈ Done, K x Doneᶜ = 0)
    (s : ℕ) (hs : s ≠ 0) (q : ℝ≥0∞)
    (hblock : ∀ b ∈ (Doneᶜ : Set α), (K ^ s) b Doneᶜ ≤ q)
    (c₀ : α) (t₀ : ℕ) (δ : ℝ≥0∞) (hδ : (K ^ t₀) c₀ Doneᶜ ≤ δ) :
    expectedHitting K c₀ Done ≤ (t₀ : ℝ≥0∞) + δ * s * (1 - q)⁻¹ := by
  have htail : ∑' t : ℕ, (K ^ (t₀ + t)) c₀ Doneᶜ ≤ δ * s * (1 - q)⁻¹ := by
    calc ∑' t : ℕ, (K ^ (t₀ + t)) c₀ Doneᶜ
        ≤ (s : ℝ≥0∞) * ∑' k : ℕ, (K ^ (t₀ + k * s)) c₀ Doneᶜ :=
          tail_le_block K hDone hAbs c₀ t₀ s hs
      _ ≤ (s : ℝ≥0∞) * ∑' k : ℕ, δ * q ^ k := by
          gcongr with k
          calc (K ^ (t₀ + k * s)) c₀ Doneᶜ
              ≤ (K ^ t₀) c₀ Doneᶜ * q ^ k :=
                bad_block_geometric_from K hDone hAbs s q hblock c₀ t₀ k
            _ ≤ δ * q ^ k := by gcongr
      _ = (s : ℝ≥0∞) * (δ * (1 - q)⁻¹) := by rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
      _ = δ * s * (1 - q)⁻¹ := by ring
  calc expectedHitting K c₀ Done
      ≤ (t₀ : ℝ≥0∞) + ∑' t : ℕ, (K ^ (t₀ + t)) c₀ Doneᶜ :=
        expectedHitting_split K c₀ Done t₀
    _ ≤ (t₀ : ℝ≥0∞) + δ * s * (1 - q)⁻¹ := by gcongr

/-! ## Part 5 — Per-single-step progress (coupon-collector engine)

The lemmas below specialize the block engine to **single steps** (`s = 1`). They are
the form Phase E2 consumes: a uniform *one-step* success probability `p` over the
not-done class `Doneᶜ` (i.e. from every not-done state the kernel reaches `Done` in
one step with probability `≥ p`, equivalently fails with probability `≤ 1 - p`)
yields the expected-hitting bound `E[T] ≤ p⁻¹`. For a stage potential that strictly
decreases per useful interaction, `p` is the lower bound on the per-step probability
that the useful interaction fires; `p⁻¹` is then the expected number of interactions
for that potential level (the per-level term of the coupon-collector / harmonic sum).
-/

/-- **One-step success ⇒ expected hitting `≤ p⁻¹`.** If `Done` is absorbing and
from every not-done state the kernel reaches `Done` in a single step with
probability `≥ p` (`K b Doneᶜ ≤ 1 - p`), then `E[T] ≤ p⁻¹`.

This is `expectedHitting_geometric` at block length `s = 1` with failure `q = 1 - p`,
using `(1 - (1 - p))⁻¹ = p⁻¹`. -/
theorem expectedHitting_one_step (K : Kernel α α) [IsMarkovKernel K]
    {Done : Set α} (hDone : MeasurableSet Done)
    (hAbs : ∀ x ∈ Done, K x Doneᶜ = 0)
    (p : ℝ≥0∞) (hp : p ≤ 1)
    (hstep : ∀ b ∈ (Doneᶜ : Set α), K b Doneᶜ ≤ 1 - p)
    (c₀ : α) :
    expectedHitting K c₀ Done ≤ p⁻¹ := by
  have hblock : ∀ b ∈ (Doneᶜ : Set α), (K ^ 1) b Doneᶜ ≤ 1 - p := by
    intro b hb; rw [pow_one]; exact hstep b hb
  calc expectedHitting K c₀ Done
      ≤ ((1 : ℕ) : ℝ≥0∞) * (1 - (1 - p))⁻¹ :=
        expectedHitting_geometric K hDone hAbs 1 (by norm_num) (1 - p) hblock c₀
    _ = p⁻¹ := by
        rw [Nat.cast_one, one_mul, ENNReal.sub_sub_cancel (by norm_num) hp]

/-- **Monotone-potential one-step bound (general `p` form).** Same conclusion as
`expectedHitting_one_step` but stated with the success probability supplied as a
hypothesis `q := 1 - p` directly, avoiding the `p > 1` corner: from `Done`
absorbing and `∀ b ∈ Doneᶜ, K b Doneᶜ ≤ q` with `q < 1`,
`E[T] ≤ (1 - q)⁻¹`. -/
theorem expectedHitting_one_step_q (K : Kernel α α) [IsMarkovKernel K]
    {Done : Set α} (hDone : MeasurableSet Done)
    (hAbs : ∀ x ∈ Done, K x Doneᶜ = 0)
    (q : ℝ≥0∞)
    (hstep : ∀ b ∈ (Doneᶜ : Set α), K b Doneᶜ ≤ q)
    (c₀ : α) :
    expectedHitting K c₀ Done ≤ (1 - q)⁻¹ := by
  have hblock : ∀ b ∈ (Doneᶜ : Set α), (K ^ 1) b Doneᶜ ≤ q := by
    intro b hb; rw [pow_one]; exact hstep b hb
  calc expectedHitting K c₀ Done
      ≤ ((1 : ℕ) : ℝ≥0∞) * (1 - q)⁻¹ :=
        expectedHitting_geometric K hDone hAbs 1 (by norm_num) q hblock c₀
    _ = (1 - q)⁻¹ := by rw [Nat.cast_one, one_mul]

/-! ## Part 6 — Occupation of an intermediate set (sequential composition)

The cross-term in the multi-stage chaining `expectedHitting_le_through_mid` is the
occupation `∑' t, (K^t) c (Mid ∩ Doneᶜ)` of the band `Mid ∖ Done`.  We bound it,
**uniformly in the start `c`**, by the supremum over `Mid`-entry configs of the
expected hitting time of `Done`:

    (∀ y ∈ Mid, expectedHitting K y Done ≤ B)  ⟹  ∑' t, (K^t) c (Mid ∩ Doneᶜ) ≤ B.

No absorption hypothesis is needed: the expected hitting time from a `Mid`-state
already counts *all* future "not-Done" time, so re-entry into `Mid` cannot
double-count.  The proof mirrors the truncated-induction `occLevelUpTo_le` route
exactly: induct on a time-truncated occupation, split on `c ∈ Mid` (the truncated
sum is then `≤ ∑' (K^t) c Doneᶜ = expectedHitting K c Done ≤ B`, since
`Mid ∩ Doneᶜ ⊆ Doneᶜ`) vs `c ∉ Mid` (the `t = 0` term vanishes; one
Chapman-Kolmogorov step pushes the remaining sum onto successors where the IH
gives `≤ B` uniformly, integrated against the Markov kernel `K c`).

This is the "strong-Markov restart" the campaign specs for closing the Phase-E2
three-stage chaining cross-term, in fully generic kernel form. -/

/-- The **time-truncated occupation** of `Mid ∩ Doneᶜ`: the partial sum of the
band masses over the first `t` steps. -/
noncomputable def occMidUpTo (K : Kernel α α) (Mid Done : Set α) (t : ℕ) (c : α) :
    ℝ≥0∞ :=
  ∑ i ∈ Finset.range t, (K ^ i) c (Mid ∩ Doneᶜ)

/-- **Uniform truncated occupation bound.** For every truncation `t` and every start
`c`, the truncated `Mid ∩ Doneᶜ` occupation is `≤ B`, given that from every
`Mid`-state the expected hitting time of `Done` is `≤ B`.

Proof by induction on `t`.  If `c ∈ Mid`, the truncated sum is `≤ ∑' (K^t) c Doneᶜ
= expectedHitting K c Done ≤ B` (`Mid ∩ Doneᶜ ⊆ Doneᶜ`).  If `c ∉ Mid`, the `i = 0`
term vanishes (`(K^0) c (Mid ∩ Doneᶜ) = δ_c(Mid ∩ Doneᶜ) = 0`); reindex `i ↦ j+1`,
apply Chapman-Kolmogorov per term, pull the finite sum inside, and bound the
integrand `occMidUpTo … t b ≤ B` by the IH (uniform in `b`). -/
theorem occMidUpTo_le [DiscreteMeasurableSpace α]
    (K : Kernel α α) [IsMarkovKernel K]
    {Mid Done : Set α} (hMid : MeasurableSet Mid) (hDone : MeasurableSet Done)
    (B : ℝ≥0∞) (hB : ∀ y ∈ Mid, expectedHitting K y Done ≤ B)
    (t : ℕ) (c : α) :
    occMidUpTo K Mid Done t c ≤ B := by
  have hband : MeasurableSet (Mid ∩ Doneᶜ : Set α) := hMid.inter hDone.compl
  induction t generalizing c with
  | zero => simp only [occMidUpTo, Finset.range_zero, Finset.sum_empty]; exact zero_le'
  | succ t ih =>
      by_cases hc : c ∈ Mid
      · -- c ∈ Mid: truncated band-sum ≤ full Doneᶜ-tail = expectedHitting ≤ B.
        calc occMidUpTo K Mid Done (t + 1) c
            ≤ ∑' i : ℕ, (K ^ i) c (Doneᶜ : Set α) := by
              rw [occMidUpTo]
              refine le_trans (Finset.sum_le_sum (fun i _ =>
                measure_mono (Set.inter_subset_right))) ?_
              exact ENNReal.sum_le_tsum _
          _ = expectedHitting K c Done := (expectedHitting_eq_tsum K c Done).symm
          _ ≤ B := hB c hc
      · -- c ∉ Mid: the i = 0 band-mass is 0; peel and reindex i = j+1.
        have hzero : (K ^ 0) c (Mid ∩ Doneᶜ) = 0 := by
          rw [show (K ^ 0) = Kernel.id from pow_zero K, Kernel.id_apply,
            Measure.dirac_apply' c hband]
          have : c ∉ (Mid ∩ Doneᶜ : Set α) := fun h => hc h.1
          simp [this]
        have hsplit : occMidUpTo K Mid Done (t + 1) c
            = ∑ j ∈ Finset.range t, (K ^ (j + 1)) c (Mid ∩ Doneᶜ) := by
          rw [occMidUpTo, Finset.sum_range_succ']
          simp only [hzero, add_zero]
        rw [hsplit]
        have hCK : ∀ j : ℕ, (K ^ (j + 1)) c (Mid ∩ Doneᶜ)
            = ∫⁻ b, (K ^ j) b (Mid ∩ Doneᶜ) ∂(K c) := by
          intro j
          rw [show j + 1 = 1 + j from by ring,
            Kernel.pow_add_apply_eq_lintegral K 1 j c hband, pow_one]
        simp only [hCK]
        rw [← lintegral_finsetSum (Finset.range t)
          (fun j _ => Kernel.measurable_coe (K ^ j) hband)]
        calc ∫⁻ b, (∑ j ∈ Finset.range t, (K ^ j) b (Mid ∩ Doneᶜ)) ∂(K c)
            ≤ ∫⁻ _ : α, B ∂(K c) := by
              apply lintegral_mono
              intro b
              simpa only [occMidUpTo] using ih b
          _ = B := by rw [lintegral_const, measure_univ, mul_one]

/-- **Occupation of an intermediate band (sequential composition / strong-Markov
restart).** If from every `Mid`-state the expected hitting time of `Done` is `≤ B`,
then the full occupation of the band `Mid ∩ Doneᶜ` from *any* start `c` is `≤ B`:

    ∑' t, (K^t) c (Mid ∩ Doneᶜ) ≤ B.

The truncated occupations are uniformly `≤ B` (`occMidUpTo_le`) and increase to the
`tsum`, which therefore inherits the bound.  This is the cross-term bound that
closes the additive multi-stage chaining `expectedHitting_le_through_mid`. -/
theorem occupation_mid_le [DiscreteMeasurableSpace α]
    (K : Kernel α α) [IsMarkovKernel K]
    {Mid Done : Set α} (hMid : MeasurableSet Mid) (hDone : MeasurableSet Done)
    (B : ℝ≥0∞) (hB : ∀ y ∈ Mid, expectedHitting K y Done ≤ B)
    (c : α) :
    ∑' t : ℕ, (K ^ t) c (Mid ∩ Doneᶜ) ≤ B := by
  rw [ENNReal.tsum_eq_iSup_nat]
  refine iSup_le (fun t => ?_)
  simpa only [occMidUpTo] using occMidUpTo_le K hMid hDone B hB t c

/-! ### Invariant-relative occupation bound

In the Phase-E2 application the per-`Mid`-state hitting bound `expectedHitting K y
Done ≤ B` is only available for `Mid`-states that *also* satisfy a closed invariant
`J` (e.g. `Mid = {activeBCount = 0}` only gives the stage-2/3 bound when the config
is additionally `S1`, i.e. all-phase-10 with positive signed sum — together making
it `S2`).  From a `J`-start the band occupation lives a.e. on `J`-states
(`InvClosed`), so the `J`-restricted hitting bound suffices.  The invariant
hypothesis is spelled out directly (matching `InvClosed`'s shape) to keep this file
self-contained. -/

/-- **Invariant-relative uniform truncated occupation bound.** Mirrors
`occMidUpTo_le`, threading a one-step-closed invariant `J` (from a `J`-state the
next-step mass on `¬ J` is `0`).  The per-`Mid`-state hitting bound is needed only
at `J ∩ Mid`-states, and the start must satisfy `J`. -/
theorem occMidUpTo_le_on [DiscreteMeasurableSpace α]
    (K : Kernel α α) [IsMarkovKernel K]
    (J : α → Prop) (hClosed : ∀ b : α, J b → K b {x | ¬ J x} = 0)
    {Mid Done : Set α} (hMid : MeasurableSet Mid) (hDone : MeasurableSet Done)
    (B : ℝ≥0∞) (hB : ∀ y : α, J y → y ∈ Mid → expectedHitting K y Done ≤ B)
    (t : ℕ) (c : α) (hJc : J c) :
    occMidUpTo K Mid Done t c ≤ B := by
  have hband : MeasurableSet (Mid ∩ Doneᶜ : Set α) := hMid.inter hDone.compl
  induction t generalizing c with
  | zero => simp only [occMidUpTo, Finset.range_zero, Finset.sum_empty]; exact zero_le'
  | succ t ih =>
      by_cases hc : c ∈ Mid
      · -- c ∈ Mid ∩ J: truncated band-sum ≤ Doneᶜ-tail = expectedHitting ≤ B.
        calc occMidUpTo K Mid Done (t + 1) c
            ≤ ∑' i : ℕ, (K ^ i) c (Doneᶜ : Set α) := by
              rw [occMidUpTo]
              refine le_trans (Finset.sum_le_sum (fun i _ =>
                measure_mono (Set.inter_subset_right))) ?_
              exact ENNReal.sum_le_tsum _
          _ = expectedHitting K c Done := (expectedHitting_eq_tsum K c Done).symm
          _ ≤ B := hB c hJc hc
      · -- c ∉ Mid: the i = 0 band-mass is 0; peel, reindex, CK step, IH on J-successors.
        have hzero : (K ^ 0) c (Mid ∩ Doneᶜ) = 0 := by
          rw [show (K ^ 0) = Kernel.id from pow_zero K, Kernel.id_apply,
            Measure.dirac_apply' c hband]
          have : c ∉ (Mid ∩ Doneᶜ : Set α) := fun h => hc h.1
          simp [this]
        have hsplit : occMidUpTo K Mid Done (t + 1) c
            = ∑ j ∈ Finset.range t, (K ^ (j + 1)) c (Mid ∩ Doneᶜ) := by
          rw [occMidUpTo, Finset.sum_range_succ']
          simp only [hzero, add_zero]
        rw [hsplit]
        have hCK : ∀ j : ℕ, (K ^ (j + 1)) c (Mid ∩ Doneᶜ)
            = ∫⁻ b, (K ^ j) b (Mid ∩ Doneᶜ) ∂(K c) := by
          intro j
          rw [show j + 1 = 1 + j from by ring,
            Kernel.pow_add_apply_eq_lintegral K 1 j c hband, pow_one]
        simp only [hCK]
        rw [← lintegral_finsetSum (Finset.range t)
          (fun j _ => Kernel.measurable_coe (K ^ j) hband)]
        -- a.e. successor b under (K c) satisfies J (closure); IH applies there.
        have hinv_ae : (K c) {x | ¬ J x} = 0 := hClosed c hJc
        calc ∫⁻ b, (∑ j ∈ Finset.range t, (K ^ j) b (Mid ∩ Doneᶜ)) ∂(K c)
            ≤ ∫⁻ _ : α, B ∂(K c) := by
              apply lintegral_mono_ae
              rw [Filter.eventually_iff_exists_mem]
              refine ⟨{x | J x}, ?_, ?_⟩
              · rw [mem_ae_iff]
                have : ({x | J x}ᶜ : Set α) = {x | ¬ J x} := by
                  ext y; simp only [Set.mem_compl_iff, Set.mem_setOf_eq]
                rw [this]; exact hinv_ae
              · intro b hb
                simp only [Set.mem_setOf_eq] at hb
                simpa only [occMidUpTo] using ih b hb
          _ = B := by rw [lintegral_const, measure_univ, mul_one]

/-- **Invariant-relative occupation of an intermediate band.** From a `J`-start `c`
(with `J` one-step-closed), the band occupation is `≤ B`, given the `J`-restricted
per-`Mid`-state hitting bound.  Closes the Phase-E2 chaining cross-term:
`Mid = {activeBCount = 0}`, `J = S1`, `Done = {wrongACount = 0}`, so `J ∩ Mid = S2`
and `B = 2·M·n(n−1)` (stage-2 then stage-3). -/
theorem occupation_mid_le_on [DiscreteMeasurableSpace α]
    (K : Kernel α α) [IsMarkovKernel K]
    (J : α → Prop) (hClosed : ∀ b : α, J b → K b {x | ¬ J x} = 0)
    {Mid Done : Set α} (hMid : MeasurableSet Mid) (hDone : MeasurableSet Done)
    (B : ℝ≥0∞) (hB : ∀ y : α, J y → y ∈ Mid → expectedHitting K y Done ≤ B)
    (c : α) (hJc : J c) :
    ∑' t : ℕ, (K ^ t) c (Mid ∩ Doneᶜ) ≤ B := by
  rw [ENNReal.tsum_eq_iSup_nat]
  refine iSup_le (fun t => ?_)
  simpa only [occMidUpTo] using occMidUpTo_le_on K J hClosed hMid hDone B hB t c hJc

/-! ## Part 7 — Markov's inequality for the hitting time (`P(T > s) ≤ E[T]/s`)

The whp instances need a *tail* bound, not an expectation: `P(T > s)` rather than
`E[T]`.  Markov's inequality `s · P(T > s) ≤ E[T]` is immediate from the tail-sum
form: by antitonicity each of the `s` terms `P(T > t)` for `t < s` dominates the
right endpoint `P(T > s)`, so `∑_{t < s} P(T > t) ≥ s · P(T > s)`, and the partial
sum is `≤ ∑' = E[T]`.  This is the *uniform-over-starts* Markov tail used by the
block restart: applied at any `S1`/`Tie1plus` start with the corresponding
`O(n² log n)` expectation bound, it gives per-block success `≥ 1/2` for `s` twice
the expectation, then `2^{-k}` over `k` blocks. -/

/-- **Markov's inequality (multiplicative form).** If `Done` is absorbing then
`s · P(T > s) ≤ E[T]`, i.e. `(K^s) c Doneᶜ * s ≤ expectedHitting K c Done`. -/
theorem mul_bad_le_expectedHitting (K : Kernel α α) [IsMarkovKernel K]
    {Done : Set α} (hDone : MeasurableSet Done)
    (hAbs : ∀ x ∈ Done, K x Doneᶜ = 0)
    (c : α) (s : ℕ) :
    (K ^ s) c Doneᶜ * (s : ℝ≥0∞) ≤ expectedHitting K c Done := by
  -- The `s` left-block terms each dominate the right endpoint `P(T > s)`.
  have hterm : ∀ t ∈ Finset.range s, (K ^ s) c Doneᶜ ≤ (K ^ t) c Doneᶜ := by
    intro t ht
    exact bad_antitone_le K hDone hAbs c (le_of_lt (Finset.mem_range.mp ht))
  calc (K ^ s) c Doneᶜ * (s : ℝ≥0∞)
      = ∑ _t ∈ Finset.range s, (K ^ s) c Doneᶜ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_comm]
    _ ≤ ∑ t ∈ Finset.range s, (K ^ t) c Doneᶜ := Finset.sum_le_sum hterm
    _ ≤ ∑' t : ℕ, (K ^ t) c Doneᶜ := ENNReal.sum_le_tsum _
    _ = expectedHitting K c Done := (expectedHitting_eq_tsum K c Done).symm

/-- **Markov tail at half the expectation budget.** If `Done` is absorbing and the
expected hitting time from `c` is `≤ E`, then with a block of `s := 2·E'` steps for
any `E' ≥ E` (interpreted via the `Nat` budget) the failure mass is `≤ 1/2`.  Stated
generically: if `E[T] ≤ B` and `B * 2 ≤ s`, then `(K^s) c Doneᶜ ≤ 1/2`.

This is the per-block half-success bound the block restart consumes. -/
theorem bad_le_half_of_expectedHitting (K : Kernel α α) [IsMarkovKernel K]
    {Done : Set α} (hDone : MeasurableSet Done)
    (hAbs : ∀ x ∈ Done, K x Doneᶜ = 0)
    (c : α) (s : ℕ) (hspos : 0 < s) (B : ℝ≥0∞) (hBfin : B ≠ ⊤)
    (hB : expectedHitting K c Done ≤ B)
    (hs : B * 2 ≤ (s : ℝ≥0∞)) :
    (K ^ s) c Doneᶜ ≤ 1 / 2 := by
  -- From `(K^s) c Doneᶜ * s ≤ E[T] ≤ B` and `2·B ≤ s`, conclude `p ≤ 1/2`.
  have hmul : (K ^ s) c Doneᶜ * (s : ℝ≥0∞) ≤ B :=
    le_trans (mul_bad_le_expectedHitting K hDone hAbs c s) hB
  set p : ℝ≥0∞ := (K ^ s) c Doneᶜ with hp
  by_cases hBzero : B = 0
  · -- B = 0, s > 0 ⇒ p * s ≤ 0 ⇒ p = 0 ≤ 1/2.
    have hsne : (s : ℝ≥0∞) ≠ 0 := by
      simp only [ne_eq, Nat.cast_eq_zero]; omega
    have hple0 : p * (s : ℝ≥0∞) ≤ 0 := by rw [hBzero] at hmul; exact hmul
    have hp0 : p = 0 := by
      rcases mul_eq_zero.mp (le_antisymm hple0 zero_le') with h | h
      · exact h
      · exact absurd h hsne
    rw [hp0]; norm_num
  · -- `p * (B*2) ≤ p * s ≤ B = (1/2)·(B*2)`; cancel `B*2` (≠ 0, ≠ ⊤).
    have hstep : p * (B * 2) ≤ (1 / 2) * (B * 2) := by
      calc p * (B * 2) ≤ p * (s : ℝ≥0∞) := by gcongr
        _ ≤ B := hmul
        _ = (1 / 2) * (B * 2) := by
            rw [show (1 / 2 : ℝ≥0∞) * (B * 2) = B * ((1 / 2) * 2) by ring]
            rw [show (1 / 2 : ℝ≥0∞) * 2 = 1 by
              rw [one_div, ENNReal.inv_mul_cancel (by norm_num) (by norm_num)], mul_one]
    have hB2ne : B * 2 ≠ 0 := mul_ne_zero hBzero (by norm_num)
    have hB2fin : B * 2 ≠ ⊤ := ENNReal.mul_ne_top hBfin (by norm_num)
    exact (ENNReal.mul_le_mul_iff_left hB2ne hB2fin).mp hstep

/-! ### Invariant-relative Markov tail

The Phase-10 Done sets `{wrongACount = 0}` / `{wrongTCount = 0}` are absorbing only
*relative to* the closed invariant `J` (= `S1` / `Tie1plus`): the proofs in
`Phase10ExpectedTime` use `occupation_mid_le_on`, never absolute absorption.  We
therefore thread `J` through the Markov tail, mirroring the `_on` occupation
lemmas: `InvClosed K J`, `J`-relative absorption of `Done`, and `J c`. -/

/-- From a `J`-start the `(K^t)`-mass on `¬ J` stays `0` (the invariant holds a.e. at
every time).  Self-contained copy (under a distinct name to avoid clashing with the
identical `Phase10ExpectedTime.pow_not_inv_eq_zero` when both are imported) so this
generic file does not depend on the Phase-10 stages. -/
theorem pow_compl_inv_eq_zero_eh [DiscreteMeasurableSpace α]
    (K : Kernel α α) [IsMarkovKernel K] (J : α → Prop)
    (hClosed : ∀ b : α, J b → K b {x | ¬ J x} = 0) (c : α) (hc : J c) (t : ℕ) :
    (K ^ t) c {x | ¬ J x} = 0 := by
  induction t generalizing c with
  | zero =>
      rw [show (K ^ 0) = Kernel.id from pow_zero K, Kernel.id_apply,
        Measure.dirac_apply' c (DiscreteMeasurableSpace.forall_measurableSet _)]
      have : c ∉ {x | ¬ J x} := by simp only [Set.mem_setOf_eq, not_not]; exact hc
      simp [this]
  | succ t ih =>
      have hbad : MeasurableSet {x : α | ¬ J x} :=
        DiscreteMeasurableSpace.forall_measurableSet _
      rw [show t + 1 = 1 + t from by ring,
        Kernel.pow_add_apply_eq_lintegral K 1 t c hbad, pow_one,
        lintegral_eq_zero_iff (Kernel.measurable_coe _ hbad)]
      rw [Filter.eventuallyEq_iff_exists_mem]
      refine ⟨{y | J y}, ?_, ?_⟩
      · rw [mem_ae_iff]
        have hcompl : ({y | J y}ᶜ : Set α) = {x | ¬ J x} := by
          ext y; simp only [Set.mem_compl_iff, Set.mem_setOf_eq]
        rw [hcompl]; exact hClosed c hc
      · intro y hy; exact ih y hy

/-- **Invariant-relative monotone bad event.** Mirrors `bad_antitone` under a closed
invariant `J`: from a `J`-start the trajectory `(K^t) c` lives a.e. on `J`, where
`Done` is absorbing, so the not-done mass is antitone. -/
theorem bad_antitone_on [DiscreteMeasurableSpace α]
    (K : Kernel α α) [IsMarkovKernel K]
    (J : α → Prop) (hClosed : ∀ b : α, J b → K b {x | ¬ J x} = 0)
    {Done : Set α} (hDone : MeasurableSet Done)
    (hAbs : ∀ x ∈ Done, J x → K x Doneᶜ = 0)
    (c : α) (hJc : J c) (t : ℕ) :
    (K ^ (t + 1)) c Doneᶜ ≤ (K ^ t) c Doneᶜ := by
  have hbad : MeasurableSet (Doneᶜ : Set α) := hDone.compl
  have hJae : (K ^ t) c {x | ¬ J x} = 0 :=
    pow_compl_inv_eq_zero_eh K J hClosed c hJc t
  rw [Kernel.pow_succ_apply_eq_lintegral K t c hbad]
  calc ∫⁻ b, K b Doneᶜ ∂((K ^ t) c)
      ≤ ∫⁻ b, Set.indicator Doneᶜ (fun _ => (1 : ℝ≥0∞)) b ∂((K ^ t) c) := by
        apply lintegral_mono_ae
        -- a.e. (under (K^t) c) the integrand is on a J-state.
        rw [Filter.eventually_iff_exists_mem]
        refine ⟨{x | J x}, ?_, ?_⟩
        · rw [mem_ae_iff]
          have : ({x | J x}ᶜ : Set α) = {x | ¬ J x} := by
            ext y; simp only [Set.mem_compl_iff, Set.mem_setOf_eq]
          rw [this]; exact hJae
        · intro b hbJ
          simp only [Set.mem_setOf_eq] at hbJ
          by_cases hb : b ∈ Done
          · rw [hAbs b hb hbJ]; exact zero_le'
          · have hb' : b ∈ (Doneᶜ : Set α) := hb
            rw [Set.indicator_of_mem hb']; exact prob_le_one
    _ = (K ^ t) c Doneᶜ := by rw [lintegral_indicator hbad]; simp

/-- General invariant-relative antitonicity: for `s ≤ t`, `(K^t) c Doneᶜ ≤
`(K^s) c Doneᶜ`, from a `J`-start. -/
theorem bad_antitone_le_on [DiscreteMeasurableSpace α]
    (K : Kernel α α) [IsMarkovKernel K]
    (J : α → Prop) (hClosed : ∀ b : α, J b → K b {x | ¬ J x} = 0)
    {Done : Set α} (hDone : MeasurableSet Done)
    (hAbs : ∀ x ∈ Done, J x → K x Doneᶜ = 0)
    (c : α) (hJc : J c) {s t : ℕ} (hst : s ≤ t) :
    (K ^ t) c Doneᶜ ≤ (K ^ s) c Doneᶜ := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hst
  clear hst
  induction d with
  | zero => simp
  | succ d ih =>
      calc (K ^ (s + (d + 1))) c Doneᶜ
          = (K ^ ((s + d) + 1)) c Doneᶜ := by ring_nf
        _ ≤ (K ^ (s + d)) c Doneᶜ := bad_antitone_on K J hClosed hDone hAbs c hJc (s + d)
        _ ≤ (K ^ s) c Doneᶜ := ih

/-- **Markov's inequality (multiplicative, invariant-relative).** From a `J`-start
with `Done` `J`-absorbing, `s · P(T > s) ≤ E[T]`. -/
theorem mul_bad_le_expectedHitting_on [DiscreteMeasurableSpace α]
    (K : Kernel α α) [IsMarkovKernel K]
    (J : α → Prop) (hClosed : ∀ b : α, J b → K b {x | ¬ J x} = 0)
    {Done : Set α} (hDone : MeasurableSet Done)
    (hAbs : ∀ x ∈ Done, J x → K x Doneᶜ = 0)
    (c : α) (hJc : J c) (s : ℕ) :
    (K ^ s) c Doneᶜ * (s : ℝ≥0∞) ≤ expectedHitting K c Done := by
  have hterm : ∀ t ∈ Finset.range s, (K ^ s) c Doneᶜ ≤ (K ^ t) c Doneᶜ := by
    intro t ht
    exact bad_antitone_le_on K J hClosed hDone hAbs c hJc
      (le_of_lt (Finset.mem_range.mp ht))
  calc (K ^ s) c Doneᶜ * (s : ℝ≥0∞)
      = ∑ _t ∈ Finset.range s, (K ^ s) c Doneᶜ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_comm]
    _ ≤ ∑ t ∈ Finset.range s, (K ^ t) c Doneᶜ := Finset.sum_le_sum hterm
    _ ≤ ∑' t : ℕ, (K ^ t) c Doneᶜ := ENNReal.sum_le_tsum _
    _ = expectedHitting K c Done := (expectedHitting_eq_tsum K c Done).symm

/-- **Per-block half-success (invariant-relative).** From a `J`-start with
`E[T] ≤ B`, `B ≠ ⊤`, `B * 2 ≤ s` and `s > 0`, the failure mass is `≤ 1/2`. -/
theorem bad_le_half_of_expectedHitting_on [DiscreteMeasurableSpace α]
    (K : Kernel α α) [IsMarkovKernel K]
    (J : α → Prop) (hClosed : ∀ b : α, J b → K b {x | ¬ J x} = 0)
    {Done : Set α} (hDone : MeasurableSet Done)
    (hAbs : ∀ x ∈ Done, J x → K x Doneᶜ = 0)
    (c : α) (hJc : J c) (s : ℕ) (hspos : 0 < s) (B : ℝ≥0∞) (hBfin : B ≠ ⊤)
    (hB : expectedHitting K c Done ≤ B) (hs : B * 2 ≤ (s : ℝ≥0∞)) :
    (K ^ s) c Doneᶜ ≤ 1 / 2 := by
  have hmul : (K ^ s) c Doneᶜ * (s : ℝ≥0∞) ≤ B :=
    le_trans (mul_bad_le_expectedHitting_on K J hClosed hDone hAbs c hJc s) hB
  set p : ℝ≥0∞ := (K ^ s) c Doneᶜ with hp
  by_cases hBzero : B = 0
  · have hsne : (s : ℝ≥0∞) ≠ 0 := by simp only [ne_eq, Nat.cast_eq_zero]; omega
    have hple0 : p * (s : ℝ≥0∞) ≤ 0 := by rw [hBzero] at hmul; exact hmul
    have hp0 : p = 0 := by
      rcases mul_eq_zero.mp (le_antisymm hple0 zero_le') with h | h
      · exact h
      · exact absurd h hsne
    rw [hp0]; norm_num
  · have hstep : p * (B * 2) ≤ (1 / 2) * (B * 2) := by
      calc p * (B * 2) ≤ p * (s : ℝ≥0∞) := by gcongr
        _ ≤ B := hmul
        _ = (1 / 2) * (B * 2) := by
            rw [show (1 / 2 : ℝ≥0∞) * (B * 2) = B * ((1 / 2) * 2) by ring]
            rw [show (1 / 2 : ℝ≥0∞) * 2 = 1 by
              rw [one_div, ENNReal.inv_mul_cancel (by norm_num) (by norm_num)], mul_one]
    have hB2ne : B * 2 ≠ 0 := mul_ne_zero hBzero (by norm_num)
    have hB2fin : B * 2 ≠ ⊤ := ENNReal.mul_ne_top hBfin (by norm_num)
    exact (ENNReal.mul_le_mul_iff_left hB2ne hB2fin).mp hstep

/-- `Done` `J`-absorbing for one step lifts to `m` steps **on `J`-states**:
`(K^m) x Doneᶜ = 0` for `x ∈ Done ∩ J`.  (J-relative `pow_absorbing`.) -/
theorem pow_absorbing_on [DiscreteMeasurableSpace α]
    (K : Kernel α α) [IsMarkovKernel K]
    (J : α → Prop) (hClosed : ∀ b : α, J b → K b {x | ¬ J x} = 0)
    {Done : Set α} (hDone : MeasurableSet Done)
    (hAbs : ∀ x ∈ Done, J x → K x Doneᶜ = 0)
    (m : ℕ) {x : α} (hx : x ∈ Done) (hJx : J x) :
    (K ^ m) x Doneᶜ = 0 := by
  have hbad : MeasurableSet (Doneᶜ : Set α) := hDone.compl
  induction m generalizing x with
  | zero =>
      rw [show (K ^ 0) = Kernel.id from pow_zero K, Kernel.id_apply,
        Measure.dirac_apply' x hbad]
      have hxc : x ∉ (Doneᶜ : Set α) := by simpa using hx
      simp [hxc]
  | succ m ih =>
      rw [show m + 1 = 1 + m from by ring,
        Kernel.pow_add_apply_eq_lintegral K 1 m x hbad, pow_one]
      rw [lintegral_eq_zero_iff (Kernel.measurable_coe _ hbad)]
      rw [Filter.eventuallyEq_iff_exists_mem]
      -- Successors of x are a.e. in Done ∩ J: J by closure, Done since K x Doneᶜ = 0.
      refine ⟨Done ∩ {y | J y}, ?_, fun b hb => ih hb.1 hb.2⟩
      rw [mem_ae_iff]
      have hcompl : ((Done ∩ {y | J y})ᶜ : Set α) ⊆ Doneᶜ ∪ {y | ¬ J y} := by
        intro y hy
        simp only [Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_setOf_eq,
          not_and_or] at hy
        rcases hy with hy | hy
        · exact Or.inl hy
        · exact Or.inr hy
      refine measure_mono_null hcompl ?_
      rw [measure_union_null_iff]
      exact ⟨hAbs x hx hJx, hClosed x hJx⟩

/-- **One-block `J`-relative contraction from base `m`.** Mirrors
`bad_block_contracts_from`, but the block bound is needed only at `J`-states, and the
absorption is `J`-relative; the base `(K^m) c` must live a.e. on `J` (ensured by a
`J`-start, supplied as `hJ_at : (K^m) c {x | ¬ J x} = 0`). -/
theorem bad_block_contracts_from_on [DiscreteMeasurableSpace α]
    (K : Kernel α α) [IsMarkovKernel K]
    (J : α → Prop) (hClosed : ∀ b : α, J b → K b {x | ¬ J x} = 0)
    {Done : Set α} (hDone : MeasurableSet Done)
    (hAbs : ∀ x ∈ Done, J x → K x Doneᶜ = 0)
    (s : ℕ) (q : ℝ≥0∞)
    (hblock : ∀ b : α, J b → b ∈ (Doneᶜ : Set α) → (K ^ s) b Doneᶜ ≤ q)
    (c : α) (m : ℕ) (hJ_at : (K ^ m) c {x | ¬ J x} = 0) :
    (K ^ (m + s)) c Doneᶜ ≤ q * (K ^ m) c Doneᶜ := by
  have hbad : MeasurableSet (Doneᶜ : Set α) := hDone.compl
  rw [Kernel.pow_add_apply_eq_lintegral K m s c hbad]
  calc ∫⁻ b, (K ^ s) b Doneᶜ ∂((K ^ m) c)
      ≤ ∫⁻ b, q * Set.indicator Doneᶜ (fun _ => (1 : ℝ≥0∞)) b ∂((K ^ m) c) := by
        apply lintegral_mono_ae
        -- a.e. b is a J-state; there bound pointwise by q·1_{Doneᶜ}.
        rw [Filter.eventually_iff_exists_mem]
        refine ⟨{x | J x}, ?_, ?_⟩
        · rw [mem_ae_iff]
          have : ({x | J x}ᶜ : Set α) = {x | ¬ J x} := by
            ext y; simp only [Set.mem_compl_iff, Set.mem_setOf_eq]
          rw [this]; exact hJ_at
        · intro b hbJ
          simp only [Set.mem_setOf_eq] at hbJ
          by_cases hb : b ∈ Done
          · rw [pow_absorbing_on K J hClosed hDone hAbs s hb hbJ]; exact zero_le'
          · have hb' : b ∈ (Doneᶜ : Set α) := hb
            rw [Set.indicator_of_mem hb', mul_one]
            exact hblock b hbJ hb'
    _ = q * (K ^ m) c Doneᶜ := by
        rw [lintegral_const_mul q (measurable_const.indicator hbad)]
        congr 1
        rw [lintegral_indicator hbad]; simp

/-- **Block-geometric tail (invariant-relative).** From a `J`-start with `Done`
`J`-absorbing, if every `s`-block from a not-done `J`-state fails with probability
`≤ q`, the `k`-block failure mass decays as `q^k`: `(K^(k·s)) c Doneᶜ ≤ q^k`. -/
theorem bad_block_geometric_on [DiscreteMeasurableSpace α]
    (K : Kernel α α) [IsMarkovKernel K]
    (J : α → Prop) (hClosed : ∀ b : α, J b → K b {x | ¬ J x} = 0)
    {Done : Set α} (hDone : MeasurableSet Done)
    (hAbs : ∀ x ∈ Done, J x → K x Doneᶜ = 0)
    (s : ℕ) (q : ℝ≥0∞)
    (hblock : ∀ b : α, J b → b ∈ (Doneᶜ : Set α) → (K ^ s) b Doneᶜ ≤ q)
    (c : α) (hJc : J c) (k : ℕ) :
    (K ^ (k * s)) c Doneᶜ ≤ q ^ k := by
  induction k with
  | zero =>
      simp only [Nat.zero_mul, pow_zero, pow_zero]
      calc (K ^ 0) c Doneᶜ ≤ (K ^ 0) c Set.univ := measure_mono (Set.subset_univ _)
        _ = 1 := by
            rw [show (K ^ 0) = Kernel.id from pow_zero K, Kernel.id_apply, measure_univ]
  | succ k ih =>
      have hJ_at : (K ^ (k * s)) c {x | ¬ J x} = 0 :=
        pow_compl_inv_eq_zero_eh K J hClosed c hJc (k * s)
      calc (K ^ ((k + 1) * s)) c Doneᶜ
          = (K ^ (k * s + s)) c Doneᶜ := by rw [show (k + 1) * s = k * s + s from by ring]
        _ ≤ q * (K ^ (k * s)) c Doneᶜ :=
            bad_block_contracts_from_on K J hClosed hDone hAbs s q hblock c (k * s) hJ_at
        _ ≤ q * q ^ k := by gcongr
        _ = q ^ (k + 1) := by rw [pow_succ]; ring

end ExactMajority
