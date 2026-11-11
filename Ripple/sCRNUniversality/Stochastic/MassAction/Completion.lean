/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Ripple.sCRNUniversality.Stochastic.MassAction.Lyapunov

/-!
# Almost-sure completion for the mass-action jump chain

`rawLaw N hPos z0` is the law of the *embedded jump chain* of the mass-action CTMC started at
`z0`: the sequence of reaction labels, each drawn in proportion to its propensity at the current
state (`none` with probability one at a terminal state).  No holding times are part of the
sample space; the expected continuous time spent before a target is the occupation functional
`E[Σ_n 1/totalPropensity(Z_n)]` over the jumps before the target, since the mean holding time
at `Z_n` is `1/totalPropensity(Z_n)` (and `∞` at a terminal state).

Three facts turn a safety bound into a completion bound:

* `rawLaw_null_label`: with probability one, no label of mass-action probability zero is drawn;
* `measure_tsum_eq_top`: a measurable nonnegative path functional with finite expectation is
  finite almost surely;
* `measurable_of_frestrictLe`: a function of the first `n + 1` labels is measurable.

Hence, if the total propensity stays below `Λ` on the paths that have not yet reached the
target, and the expected occupation time before the target is finite, the paths that never
reach the target form a null set: each of their jumps costs at least `1/Λ`
(`tsum_eq_top_of_le`).
-/

namespace Ripple.sCRNUniversality.Stochastic.MassAction

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal

universe u v

variable {S : Type u} [Fintype S] [DecidableEq S]
variable (N : Network.{u, v} S) [DecidableEq N.I]

omit [Fintype S] [DecidableEq S] [DecidableEq N.I] in
/-- A function of paths that depends only on the first `n + 1` labels is measurable. -/
theorem measurable_of_frestrictLe {β : Type*} [MeasurableSpace β] (n : ℕ)
    (f : ((k : ℕ) → Option N.I) → β)
    (hf : ∀ ω ω', frestrictLe n ω = frestrictLe n ω' → f ω = f ω') : Measurable f := by
  classical
  let ext : ((i : Finset.Iic n) → Option N.I) → (k : ℕ) → Option N.I :=
    fun p k => if h : k ∈ Finset.Iic n then p ⟨k, h⟩ else none
  have hext : ∀ ω : (k : ℕ) → Option N.I,
      frestrictLe n (ext (frestrictLe n ω)) = frestrictLe n ω := by
    intro ω
    funext i
    simp only [frestrictLe_apply, ext, dif_pos i.2]
  have : f = fun ω => f (ext (frestrictLe n ω)) := funext fun ω => hf ω _ (hext ω).symm
  rw [this]
  exact measurable_comp_frestrictLe N n (fun p => f (ext p))

variable (hPos : N.hasPositiveRates) (z0 : State S)

/-- **No null labels.** With probability one, every label drawn has positive mass-action
probability at the current state. -/
theorem rawLaw_null_label :
    rawLaw N hPos z0 {ω | ∃ n, massActionPMF N hPos (prefixToState N z0 n (frestrictLe n ω))
      (ω (n + 1)) = 0} = 0 := by
  classical
  have hset : {ω : (k : ℕ) → Option N.I | ∃ n,
      massActionPMF N hPos (prefixToState N z0 n (frestrictLe n ω)) (ω (n + 1)) = 0} =
      ⋃ n, {ω | massActionPMF N hPos (prefixToState N z0 n (frestrictLe n ω)) (ω (n + 1)) = 0} := by
    ext ω; simp
  rw [hset]
  refine measure_iUnion_null fun n => ?_
  have hmeas : MeasurableSet {ω : (k : ℕ) → Option N.I |
      massActionPMF N hPos (prefixToState N z0 n (frestrictLe n ω)) (ω (n + 1)) = 0} := by
    have : {ω : (k : ℕ) → Option N.I |
        massActionPMF N hPos (prefixToState N z0 n (frestrictLe n ω)) (ω (n + 1)) = 0} =
        (fun ω => (frestrictLe n ω, ω (n + 1))) ⁻¹'
          {q | massActionPMF N hPos (prefixToState N z0 n q.1) q.2 = 0} := rfl
    rw [this]
    refine ((measurable_frestrictLe n).prodMk (measurable_pi_apply (n + 1))) ?_
    exact (Set.toFinite _).measurableSet
  have h := lintegral_prefix_next N hPos z0 n (fun p o =>
    if massActionPMF N hPos (prefixToState N z0 n p) o = 0 then (1 : ℝ≥0∞) else 0)
  have hzero : ∀ ω : (k : ℕ) → Option N.I,
      (∑ o, massActionPMF N hPos (prefixToState N z0 n (frestrictLe n ω)) o *
        (if massActionPMF N hPos (prefixToState N z0 n (frestrictLe n ω)) o = 0 then (1 : ℝ≥0∞)
          else 0)) = 0 := by
    intro ω
    refine Finset.sum_eq_zero fun o _ => ?_
    split_ifs with h0
    · rw [h0, zero_mul]
    · rw [mul_zero]
  simp only [hzero, lintegral_zero] at h
  calc rawLaw N hPos z0 {ω | massActionPMF N hPos (prefixToState N z0 n (frestrictLe n ω))
          (ω (n + 1)) = 0}
      = ∫⁻ ω, {ω : (k : ℕ) → Option N.I | massActionPMF N hPos
          (prefixToState N z0 n (frestrictLe n ω)) (ω (n + 1)) = 0}.indicator 1 ω
            ∂(rawLaw N hPos z0) :=
        (lintegral_indicator_one hmeas).symm
    _ = ∫⁻ ω, (if massActionPMF N hPos (prefixToState N z0 n (frestrictLe n ω)) (ω (n + 1)) = 0
          then (1 : ℝ≥0∞) else 0) ∂(rawLaw N hPos z0) := by
        congr 1
        funext ω
        simp only [Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply]
    _ = 0 := h

omit [Fintype S] [DecidableEq S] [DecidableEq N.I] in
/-- A measurable nonnegative path functional with finite expectation is finite almost surely. -/
theorem measure_tsum_eq_top {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} (g : ℕ → Ω → ℝ≥0∞)
    (hg : ∀ n, Measurable (g n)) (hfin : ∫⁻ ω, ∑' n, g n ω ∂μ ≠ ⊤) :
    μ {ω | ∑' n, g n ω = ⊤} = 0 := by
  have h := ae_lt_top (Measurable.tsum hg) hfin
  rw [ae_iff] at h
  refine measure_mono_null (fun ω hω => ?_) h
  simp only [Set.mem_setOf_eq, not_lt, top_le_iff] at hω ⊢
  exact hω

omit [Fintype S] [DecidableEq S] [DecidableEq N.I] in
/-- A series of terms bounded below by a positive constant diverges. -/
theorem tsum_eq_top_of_le {f : ℕ → ℝ≥0∞} {ε : ℝ≥0∞} (hε : ε ≠ 0) (h : ∀ n, ε ≤ f n) :
    ∑' n, f n = ⊤ :=
  top_le_iff.mp
    ((ENNReal.tsum_const_eq_top_of_ne_zero hε).symm.le.trans (ENNReal.tsum_le_tsum h))

end Ripple.sCRNUniversality.Stochastic.MassAction
