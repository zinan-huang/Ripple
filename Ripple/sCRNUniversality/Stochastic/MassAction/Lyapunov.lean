/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Ripple.sCRNUniversality.Stochastic.MassAction.PrefixMarginal

/-!
# Lyapunov (drift) bounds for the mass-action jump chain

For the jump chain `rawLaw N hPos z0` we follow an *extended state* `W n ω = (Y n ω, Z n ω)`:
`Z n ω` is the CRN state after `n` jumps and `Y` is updated by a deterministic rule
`Y (n+1) = upd (Y n) (Z n) (ω (n+1))` (a counter of ticks, an error flag, ...).

* `lintegral_prefix_next`: the one-step Markov property in integral form,
  `E[h(prefix_n, ω(n+1))] = E[Σ_o p(Z_n, o) h(prefix_n, o)]`;
* `lintegral_tsum_cost_le` (**drift bound**): if `c(y, z) + Σ_o p(z, o) P(y', z') ≤ P(y, z)` for
  all `(y, z)` (`(y', z')` the successor under label `o`), then `E[Σ_n c(W n)] ≤ P(W 0)`;
* `measure_exists_le_lintegral`: the probability that some step `n` satisfies a condition on
  `(W n, ω (n+1))` is at most the expected sum of the conditional probabilities.

These replace, for the clocked CTM network (`docs/audit/FIX3-SCWB-T32.md`), the continuous-time
arguments of the paper proof (random time change, strong Markov property, independence of the
clock) by potential functions on the jump chain.
-/

namespace Ripple.sCRNUniversality.Stochastic.MassAction

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal

universe u v w

variable {S : Type u} [Fintype S] [DecidableEq S]
variable (N : Network.{u, v} S) [DecidableEq N.I]

omit [Fintype S] [DecidableEq S] [DecidableEq N.I] in
/-- Every function of a finite label prefix is measurable. -/
theorem measurable_prefixFun {β : Type*} [MeasurableSpace β] (n : ℕ)
    (f : ((i : Finset.Iic n) → Option N.I) → β) : Measurable f :=
  fun _ _ => measurableSet_prefixSet N n _

omit [Fintype S] [DecidableEq S] [DecidableEq N.I] in
theorem measurable_comp_frestrictLe {β : Type*} [MeasurableSpace β] (n : ℕ)
    (f : ((i : Finset.Iic n) → Option N.I) → β) :
    Measurable (fun ω : (k : ℕ) → Option N.I => f (frestrictLe n ω)) :=
  (measurable_prefixFun N n f).comp (measurable_frestrictLe n)

variable (hPos : N.hasPositiveRates) (z0 : State S)

/-- **One-step Markov property, integral form.** -/
theorem lintegral_prefix_next (n : ℕ)
    (h : ((i : Finset.Iic n) → Option N.I) → Option N.I → ℝ≥0∞) :
    ∫⁻ ω, h (frestrictLe n ω) (ω (n + 1)) ∂(rawLaw N hPos z0) =
      ∫⁻ ω, ∑ o, massActionPMF N hPos (prefixToState N z0 n (frestrictLe n ω)) o *
        h (frestrictLe n ω) o ∂(rawLaw N hPos z0) := by
  classical
  let A : ((i : Finset.Iic n) → Option N.I) → Option N.I → Set ((k : ℕ) → Option N.I) :=
    fun p o => {ω | frestrictLe n ω ∈ ({p} : Set _) ∧ ω (n + 1) = o}
  let B : ((i : Finset.Iic n) → Option N.I) → Set ((k : ℕ) → Option N.I) :=
    fun p => {ω | frestrictLe n ω ∈ ({p} : Set _)}
  have hA : ∀ p o, MeasurableSet (A p o) := fun p o =>
    (measurable_frestrictLe n (measurableSet_prefixSet N n {p})).inter
      (measurableSet_eq_fun (measurable_pi_apply (n + 1)) measurable_const)
  have hB : ∀ p, MeasurableSet (B p) := fun p =>
    measurable_frestrictLe n (measurableSet_prefixSet N n {p})
  have hL : ∀ ω, h (frestrictLe n ω) (ω (n + 1)) =
      ∑ p, ∑ o, (A p o).indicator (fun _ => h p o) ω := by
    intro ω
    rw [Finset.sum_eq_single (frestrictLe n ω), Finset.sum_eq_single (ω (n + 1))]
    · rw [Set.indicator_of_mem (show ω ∈ A (frestrictLe n ω) (ω (n + 1)) from
        ⟨Set.mem_singleton _, rfl⟩)]
    · intro o _ ho
      rw [Set.indicator_of_notMem]
      exact fun hω => ho hω.2.symm
    · simp
    · intro p _ hp
      refine Finset.sum_eq_zero fun o _ => ?_
      rw [Set.indicator_of_notMem]
      exact fun hω => hp (Set.mem_singleton_iff.mp hω.1).symm
    · simp
  have hR : ∀ ω, (∑ o, massActionPMF N hPos (prefixToState N z0 n (frestrictLe n ω)) o *
      h (frestrictLe n ω) o) = ∑ p, (B p).indicator
        (fun _ => ∑ o, massActionPMF N hPos (prefixToState N z0 n p) o * h p o) ω := by
    intro ω
    rw [Finset.sum_eq_single (frestrictLe n ω)]
    · rw [Set.indicator_of_mem (show ω ∈ B (frestrictLe n ω) from Set.mem_singleton _)]
    · intro p _ hp
      rw [Set.indicator_of_notMem]
      exact fun hω => hp (Set.mem_singleton_iff.mp hω).symm
    · simp
  simp_rw [hL, hR]
  rw [lintegral_finset_sum _ fun p _ => Finset.measurable_sum _ fun o _ =>
      measurable_const.indicator (hA p o),
    lintegral_finset_sum _ fun p _ => measurable_const.indicator (hB p)]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [lintegral_finset_sum _ fun o _ => measurable_const.indicator (hA p o),
    lintegral_indicator_const (hB p), Finset.sum_mul]
  refine Finset.sum_congr rfl fun o _ => ?_
  rw [lintegral_indicator_const (hA p o)]
  have := rawLaw_prefix_next N hPos z0 n {p} (prefixToState N z0 n p)
    (fun p' hp' => by rw [Set.mem_singleton_iff.mp hp']) o
  change rawLaw N hPos z0 (A p o) =
    rawLaw N hPos z0 (B p) * massActionPMF N hPos (prefixToState N z0 n p) o at this
  rw [this]
  ring

/-! ### Extended states -/

variable {X : Type w} (upd : X → State S → Option N.I → X) (x0 : X)

/-- Extended state (auxiliary state and CRN state) after the prefix `p` of length `n`. -/
noncomputable def extOf : (n : ℕ) → ((i : Finset.Iic n) → Option N.I) → X × State S
  | 0, _ => (x0, z0)
  | n + 1, p =>
    let prev := extOf n (fun k => p ⟨k.val,
      Finset.mem_Iic.mpr (le_trans (Finset.mem_Iic.mp k.property) (Nat.le_succ n))⟩)
    (upd prev.1 prev.2 (p ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩),
      stateStep N prev.2 (p ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩))

theorem extOf_snd : ∀ (n : ℕ) (p : (i : Finset.Iic n) → Option N.I),
    (extOf N z0 upd x0 n p).2 = prefixToState N z0 n p
  | 0, _ => rfl
  | n + 1, p => by
    simp only [extOf, prefixToState]
    rw [extOf_snd n]

/-- The extended state after `n` jumps of the path `ω`. -/
noncomputable def extState (n : ℕ) (ω : (k : ℕ) → Option N.I) : X × State S :=
  extOf N z0 upd x0 n (frestrictLe n ω)

theorem extState_zero (ω : (k : ℕ) → Option N.I) : extState N z0 upd x0 0 ω = (x0, z0) := rfl

theorem extState_succ (n : ℕ) (ω : (k : ℕ) → Option N.I) :
    extState N z0 upd x0 (n + 1) ω =
      (upd (extState N z0 upd x0 n ω).1 (extState N z0 upd x0 n ω).2 (ω (n + 1)),
        stateStep N (extState N z0 upd x0 n ω).2 (ω (n + 1))) := rfl

theorem extState_snd (n : ℕ) (ω : (k : ℕ) → Option N.I) :
    (extState N z0 upd x0 n ω).2 = prefixToState N z0 n (frestrictLe n ω) :=
  extOf_snd N z0 upd x0 n _

theorem measurable_extState_comp {β : Type*} [MeasurableSpace β] (n : ℕ) (f : X × State S → β) :
    Measurable (fun ω => f (extState N z0 upd x0 n ω)) :=
  measurable_comp_frestrictLe N n (fun p => f (extOf N z0 upd x0 n p))

/-- One Markov step for a function of the next extended state. -/
theorem lintegral_extState_succ (n : ℕ) (F : X × State S → ℝ≥0∞) :
    ∫⁻ ω, F (extState N z0 upd x0 (n + 1) ω) ∂(rawLaw N hPos z0) =
      ∫⁻ ω, ∑ o, massActionPMF N hPos (extState N z0 upd x0 n ω).2 o *
        F (upd (extState N z0 upd x0 n ω).1 (extState N z0 upd x0 n ω).2 o,
          stateStep N (extState N z0 upd x0 n ω).2 o) ∂(rawLaw N hPos z0) := by
  have h := lintegral_prefix_next N hPos z0 n (fun p o =>
    F (upd (extOf N z0 upd x0 n p).1 (extOf N z0 upd x0 n p).2 o,
      stateStep N (extOf N z0 upd x0 n p).2 o))
  simp only [← extOf_snd N z0 upd x0 n] at h
  exact h

/-- **Drift bound.** A nonnegative potential `P` whose expected value after one jump, plus the
cost `c` of the current extended state, does not exceed its current value, bounds the expected
total cost along the whole path. -/
theorem lintegral_tsum_cost_le (P c : X × State S → ℝ≥0∞)
    (hdrift : ∀ y : X × State S, c y + ∑ o, massActionPMF N hPos y.2 o *
      P (upd y.1 y.2 o, stateStep N y.2 o) ≤ P y) :
    ∫⁻ ω, ∑' n, c (extState N z0 upd x0 n ω) ∂(rawLaw N hPos z0) ≤ P (x0, z0) := by
  haveI := rawLaw_isProbabilityMeasure N hPos z0
  have hmeas : ∀ n (F : X × State S → ℝ≥0∞),
      Measurable (fun ω => F (extState N z0 upd x0 n ω)) :=
    fun n F => measurable_extState_comp N z0 upd x0 n F
  have key : ∀ n, ∫⁻ ω, (∑ k ∈ Finset.range n, c (extState N z0 upd x0 k ω)) +
      P (extState N z0 upd x0 n ω) ∂(rawLaw N hPos z0) ≤ P (x0, z0) := by
    intro n
    induction n with
    | zero =>
      simp only [Finset.range_zero, Finset.sum_empty, zero_add, extState_zero]
      rw [lintegral_const, measure_univ, mul_one]
    | succ n ih =>
      have hsum_meas : Measurable (fun ω =>
          ∑ k ∈ Finset.range n, c (extState N z0 upd x0 k ω)) :=
        Finset.measurable_sum _ fun k _ => hmeas k c
      calc ∫⁻ ω, (∑ k ∈ Finset.range (n + 1), c (extState N z0 upd x0 k ω)) +
              P (extState N z0 upd x0 (n + 1) ω) ∂(rawLaw N hPos z0)
          = ∫⁻ ω, (∑ k ∈ Finset.range n, c (extState N z0 upd x0 k ω)) +
              (c (extState N z0 upd x0 n ω) + P (extState N z0 upd x0 (n + 1) ω))
                ∂(rawLaw N hPos z0) := by
            congr 1; funext ω; rw [Finset.sum_range_succ, add_assoc]
        _ = (∫⁻ ω, ∑ k ∈ Finset.range n, c (extState N z0 upd x0 k ω) ∂(rawLaw N hPos z0)) +
              ((∫⁻ ω, c (extState N z0 upd x0 n ω) ∂(rawLaw N hPos z0)) +
                ∫⁻ ω, P (extState N z0 upd x0 (n + 1) ω) ∂(rawLaw N hPos z0)) := by
            rw [lintegral_add_left hsum_meas, lintegral_add_left (hmeas n c)]
        _ = (∫⁻ ω, ∑ k ∈ Finset.range n, c (extState N z0 upd x0 k ω) ∂(rawLaw N hPos z0)) +
              ∫⁻ ω, (c (extState N z0 upd x0 n ω) +
                ∑ o, massActionPMF N hPos (extState N z0 upd x0 n ω).2 o *
                  P (upd (extState N z0 upd x0 n ω).1 (extState N z0 upd x0 n ω).2 o,
                    stateStep N (extState N z0 upd x0 n ω).2 o)) ∂(rawLaw N hPos z0) := by
            rw [lintegral_extState_succ N hPos z0 upd x0 n P, lintegral_add_left (hmeas n c)]
        _ ≤ (∫⁻ ω, ∑ k ∈ Finset.range n, c (extState N z0 upd x0 k ω) ∂(rawLaw N hPos z0)) +
              ∫⁻ ω, P (extState N z0 upd x0 n ω) ∂(rawLaw N hPos z0) := by
            gcongr with ω
            exact hdrift _
        _ = ∫⁻ ω, (∑ k ∈ Finset.range n, c (extState N z0 upd x0 k ω)) +
              P (extState N z0 upd x0 n ω) ∂(rawLaw N hPos z0) :=
            (lintegral_add_left hsum_meas _).symm
        _ ≤ P (x0, z0) := ih
  rw [lintegral_tsum fun n => (hmeas n c).aemeasurable]
  rw [ENNReal.tsum_eq_iSup_nat]
  refine iSup_le fun n => ?_
  rw [← lintegral_finset_sum _ fun k _ => hmeas k c]
  calc _ ≤ ∫⁻ ω, (∑ k ∈ Finset.range n, c (extState N z0 upd x0 k ω)) +
          P (extState N z0 upd x0 n ω) ∂(rawLaw N hPos z0) :=
        lintegral_mono fun ω => le_self_add
    _ ≤ _ := key n

/-- The probability that some step satisfies `B` is at most the expected sum of the
one-step probabilities. -/
theorem measure_exists_le_lintegral (B : X × State S → Option N.I → Prop) :
    rawLaw N hPos z0 {ω | ∃ n, B (extState N z0 upd x0 n ω) (ω (n + 1))} ≤
      ∫⁻ ω, ∑' n, ∑ o, massActionPMF N hPos (extState N z0 upd x0 n ω).2 o *
        (open Classical in if B (extState N z0 upd x0 n ω) o then 1 else 0)
        ∂(rawLaw N hPos z0) := by
  classical
  have hset : {ω : (k : ℕ) → Option N.I | ∃ n, B (extState N z0 upd x0 n ω) (ω (n + 1))} =
      ⋃ n, {ω | B (extState N z0 upd x0 n ω) (ω (n + 1))} := by
    ext ω; simp
  rw [hset]
  refine (measure_iUnion_le _).trans ?_
  rw [lintegral_tsum fun n => (Finset.measurable_sum _ fun o _ =>
    (measurable_extState_comp N z0 upd x0 n (fun y => massActionPMF N hPos y.2 o *
      (if B y o then 1 else 0)))).aemeasurable]
  refine ENNReal.tsum_le_tsum fun n => le_of_eq ?_
  have h := lintegral_prefix_next N hPos z0 n (fun p o =>
    if B (extOf N z0 upd x0 n p) o then 1 else 0)
  simp only [← extOf_snd N z0 upd x0 n] at h
  have hmeasB : MeasurableSet {ω : (k : ℕ) → Option N.I |
      B (extState N z0 upd x0 n ω) (ω (n + 1))} := by
    have : {ω : (k : ℕ) → Option N.I | B (extState N z0 upd x0 n ω) (ω (n + 1))} =
        (fun ω => (frestrictLe n ω, ω (n + 1))) ⁻¹'
          {q | B (extOf N z0 upd x0 n q.1) q.2} := rfl
    rw [this]
    refine ((measurable_frestrictLe n).prodMk (measurable_pi_apply (n + 1))) ?_
    have hfin : Set.Finite {q : ((i : Finset.Iic n) → Option N.I) × Option N.I |
        B (extOf N z0 upd x0 n q.1) q.2} := Set.toFinite _
    exact hfin.measurableSet
  rw [← lintegral_indicator_one hmeasB]
  convert h using 2

end Ripple.sCRNUniversality.Stochastic.MassAction
