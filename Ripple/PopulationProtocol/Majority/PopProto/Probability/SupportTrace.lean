/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Finite Support Traces

This file packages finite paths through the support of the approximate-majority
Markov kernel.  It lifts one-step support invariants, such as preservation of
having at least one opinionated agent, to finite stochastic executions.
-/

import Ripple.PopulationProtocol.Majority.PopProto.Invariant.Absorbing
import Ripple.PopulationProtocol.Majority.PopProto.Invariant.Gap

namespace PopProto

open MeasureTheory ProbabilityTheory

namespace Config

variable {n : ℕ}

/-- Endpoint of a finite trace whose elements are successive configurations. -/
def supportTraceEndpoint : Config n → List (Config n) → Config n
  | c, [] => c
  | _, c' :: rest => supportTraceEndpoint c' rest

/-- A finite trace through the support of the one-step approximate-majority
kernel. -/
def supportTrace (hn : n ≥ 2) : Config n → List (Config n) → Prop
  | _, [] => True
  | c, c' :: rest => c' ∈ (c.stepDist hn).support ∧ supportTrace hn c' rest

/-- A one-step support-closed predicate holds almost surely after any finite
number of Markov steps.  This is the generic bridge from deterministic
finite-support invariants to the probabilistic kernel. -/
theorem ae_of_stepDist_support_preserved
    (hn : n ≥ 2) (P : Config n → Prop)
    (hstep : ∀ c c' : Config n, P c → c' ∈ (c.stepDist hn).support → P c')
    (c : Config n) (hc : P c) (t : ℕ) :
    ∀ᵐ c' ∂((transitionKernel hn ^ t) c), P c' := by
  induction t with
  | zero =>
      simp only [pow_zero]
      change ∀ᵐ c' ∂(Kernel.id c), P c'
      rw [Kernel.id_apply, MeasureTheory.ae_dirac_iff
        (instDiscreteMeasurableSpaceConfig.forall_measurableSet _)]
      exact hc
  | succ t ih =>
      rw [MeasureTheory.ae_iff]
      have hbad_meas : MeasurableSet {c' : Config n | ¬P c'} :=
        instDiscreteMeasurableSpaceConfig.forall_measurableSet _
      rw [Kernel.pow_succ_apply_eq_lintegral _ _ _ hbad_meas,
        MeasureTheory.lintegral_eq_zero_iff (Kernel.measurable_coe _ hbad_meas)]
      filter_upwards [ih] with c' hc'
      change (c'.stepDist hn).toMeasure {c'' : Config n | ¬P c''} = 0
      rw [PMF.toMeasure_apply_eq_zero_iff
        (p := c'.stepDist hn)
        (s := {c'' : Config n | ¬P c''})
        (instDiscreteMeasurableSpaceConfig.forall_measurableSet _)]
      rw [Set.disjoint_left]
      intro c'' hsupp hbad
      exact hbad (hstep c' c'' hc' hsupp)

/-- Probability-zero form of `ae_of_stepDist_support_preserved`. -/
theorem transitionKernel_pow_not_pred_eq_zero_of_stepDist_support_preserved
    (hn : n ≥ 2) (P : Config n → Prop)
    (hstep : ∀ c c' : Config n, P c → c' ∈ (c.stepDist hn).support → P c')
    (c : Config n) (hc : P c) (t : ℕ) :
    (transitionKernel hn ^ t) c {c' : Config n | ¬P c'} = 0 := by
  have h := ae_of_stepDist_support_preserved hn P hstep c hc t
  rwa [MeasureTheory.ae_iff] at h

/-- Event form of `transitionKernel_pow_not_pred_eq_zero_of_stepDist_support_preserved`:
any set contained in the complement of a support-closed invariant has
probability zero at every finite time. -/
theorem transitionKernel_pow_eq_zero_of_forall_not_pred
    (hn : n ≥ 2) (P : Config n → Prop)
    (hstep : ∀ c c' : Config n, P c → c' ∈ (c.stepDist hn).support → P c')
    (c : Config n) (hc : P c) (t : ℕ) (S : Set (Config n))
    (hS : ∀ c' : Config n, c' ∈ S → ¬P c') :
    (transitionKernel hn ^ t) c S = 0 := by
  refine measure_mono_null ?_
    (transitionKernel_pow_not_pred_eq_zero_of_stepDist_support_preserved
      hn P hstep c hc t)
  intro c' hc'
  exact hS c' hc'

/-- Every one-step support point changes the gap by at most one. -/
theorem gap_of_stepDist_support_bounded
    (hn : n ≥ 2) (c c' : Config n)
    (hsupp : c' ∈ (c.stepDist hn).support) :
    Int.natAbs (c'.gap - c.gap) ≤ 1 := by
  obtain ⟨i, r, hstep⟩ := stepDist_support c hn c' hsupp
  rw [← hstep]
  exact gap_stepOrSelf_bounded c i r

/-- Along a finite support trace, the endpoint gap differs from the starting
gap by at most the trace length. -/
theorem supportTraceEndpoint_gap_bounded
    (hn : n ≥ 2) (c : Config n) (trace : List (Config n))
    (htrace : supportTrace hn c trace) :
    Int.natAbs ((supportTraceEndpoint c trace).gap - c.gap) ≤ trace.length := by
  induction trace generalizing c with
  | nil =>
      simp [supportTraceEndpoint]
  | cons c' rest ih =>
      rcases htrace with ⟨hsupp, hrest⟩
      have hstep := gap_of_stepDist_support_bounded hn c c' hsupp
      have htail := ih c' hrest
      have hdecomp :
          (supportTraceEndpoint c' rest).gap - c.gap =
            ((supportTraceEndpoint c' rest).gap - c'.gap) + (c'.gap - c.gap) := by
        ring
      simp only [supportTraceEndpoint, List.length_cons]
      rw [hdecomp]
      calc
        Int.natAbs
            (((supportTraceEndpoint c' rest).gap - c'.gap) + (c'.gap - c.gap))
            ≤ Int.natAbs ((supportTraceEndpoint c' rest).gap - c'.gap) +
                Int.natAbs (c'.gap - c.gap) :=
              Int.natAbs_add_le _ _
        _ ≤ rest.length + 1 := by omega

/-- The event that the gap has moved by more than the number of elapsed Markov
steps has probability zero. -/
theorem transitionKernel_pow_gap_natAbs_sub_gt_eq_zero
    (hn : n ≥ 2) (c : Config n) (t : ℕ) :
    (transitionKernel hn ^ t) c
        {c' : Config n | t < Int.natAbs (c'.gap - c.gap)} = 0 := by
  induction t with
  | zero =>
      simp only [pow_zero]
      change Kernel.id c {c' : Config n | 0 < Int.natAbs (c'.gap - c.gap)} = 0
      rw [Kernel.id_apply, Measure.dirac_apply' _
        (instDiscreteMeasurableSpaceConfig.forall_measurableSet _)]
      simp
  | succ t ih =>
      have hbad_meas :
          MeasurableSet {c' : Config n | t.succ < Int.natAbs (c'.gap - c.gap)} :=
        instDiscreteMeasurableSpaceConfig.forall_measurableSet _
      have hgood :
          ∀ᵐ c_mid ∂((transitionKernel hn ^ t) c),
            Int.natAbs (c_mid.gap - c.gap) ≤ t := by
        rw [MeasureTheory.ae_iff]
        simpa only [not_le] using ih
      rw [Kernel.pow_succ_apply_eq_lintegral _ _ _ hbad_meas,
        MeasureTheory.lintegral_eq_zero_iff (Kernel.measurable_coe _ hbad_meas)]
      filter_upwards [hgood] with c_mid hmid
      change (c_mid.stepDist hn).toMeasure
        {c' : Config n | t.succ < Int.natAbs (c'.gap - c.gap)} = 0
      rw [PMF.toMeasure_apply_eq_zero_iff
        (p := c_mid.stepDist hn)
        (s := {c' : Config n | t.succ < Int.natAbs (c'.gap - c.gap)})
        (instDiscreteMeasurableSpaceConfig.forall_measurableSet _)]
      rw [Set.disjoint_left]
      intro c' hsupp hbad
      exfalso
      have hstep := gap_of_stepDist_support_bounded hn c_mid c' hsupp
      have hdecomp : c'.gap - c.gap = (c'.gap - c_mid.gap) + (c_mid.gap - c.gap) := by
        ring
      have hle : Int.natAbs (c'.gap - c.gap) ≤ t.succ := by
        rw [hdecomp]
        calc
          Int.natAbs ((c'.gap - c_mid.gap) + (c_mid.gap - c.gap))
            ≤ Int.natAbs (c'.gap - c_mid.gap) + Int.natAbs (c_mid.gap - c.gap) :=
              Int.natAbs_add_le _ _
          _ ≤ t.succ := by omega
      exact not_le_of_gt hbad hle

/-- Any event contained in configurations whose gap differs from the starting
gap by more than `t` has probability zero after `t` Markov steps. -/
theorem transitionKernel_pow_eq_zero_of_forall_gap_natAbs_sub_gt
    (hn : n ≥ 2) (c : Config n) (t : ℕ) (S : Set (Config n))
    (hS : ∀ c' : Config n, c' ∈ S →
      t < Int.natAbs (c'.gap - c.gap)) :
    (transitionKernel hn ^ t) c S = 0 := by
  refine measure_mono_null ?_
    (transitionKernel_pow_gap_natAbs_sub_gt_eq_zero hn c t)
  intro c' hc'
  exact hS c' hc'

/-- From any opinionated starting configuration, finite Markov executions
almost surely preserve an opinionated agent and move the input gap by at most
the number of elapsed steps. -/
theorem transitionKernel_pow_core_invariants
    (hn : n ≥ 2) (c : Config n) (hop : c.hasOpinion) (t : ℕ) :
    ∀ᵐ c' ∂((transitionKernel hn ^ t) c),
      c'.hasOpinion ∧ Int.natAbs (c'.gap - c.gap) ≤ t := by
  have hgap :
      ∀ᵐ c' ∂((transitionKernel hn ^ t) c),
        Int.natAbs (c'.gap - c.gap) ≤ t := by
    rw [MeasureTheory.ae_iff]
    simpa only [not_le] using transitionKernel_pow_gap_natAbs_sub_gt_eq_zero hn c t
  filter_upwards [ae_hasOpinion_transitionKernel_pow c hn hop t, hgap] with c' hop' hgap'
  exact ⟨hop', hgap'⟩

/-- The event that a finite Markov execution from an opinionated configuration
loses all opinionated agents or moves the gap by more than the elapsed time has
probability zero. -/
theorem transitionKernel_pow_core_invariants_fail_eq_zero
    (hn : n ≥ 2) (c : Config n) (hop : c.hasOpinion) (t : ℕ) :
    (transitionKernel hn ^ t) c
        {c' : Config n |
          ¬ (c'.hasOpinion ∧ Int.natAbs (c'.gap - c.gap) ≤ t)} = 0 := by
  have hcore := transitionKernel_pow_core_invariants hn c hop t
  rwa [MeasureTheory.ae_iff] at hcore

/-- Any event contained in the failure of the finite-time core invariants has
probability zero from an opinionated starting configuration. -/
theorem transitionKernel_pow_eq_zero_of_forall_core_invariants_fail
    (hn : n ≥ 2) (c : Config n) (hop : c.hasOpinion) (t : ℕ)
    (S : Set (Config n))
    (hS : ∀ c' : Config n, c' ∈ S →
      ¬ (c'.hasOpinion ∧ Int.natAbs (c'.gap - c.gap) ≤ t)) :
    (transitionKernel hn ^ t) c S = 0 := by
  refine measure_mono_null ?_
    (transitionKernel_pow_core_invariants_fail_eq_zero hn c hop t)
  intro c' hc'
  exact hS c' hc'

/-- Initial-state specialization of the finite-support trace gap bound. -/
theorem initial_supportTraceEndpoint_gap_bounded
    (hn : n ≥ 2) {a : ℕ} (h : a ≤ n)
    (trace : List (Config n))
    (htrace : supportTrace hn (initial n a h) trace) :
    Int.natAbs
      ((supportTraceEndpoint (initial n a h) trace).gap - (initial n a h).gap) ≤
        trace.length :=
  supportTraceEndpoint_gap_bounded hn (initial n a h) trace htrace

/-- Initial-state specialization: after `t` Markov steps, the gap has moved
by more than `t` with probability zero. -/
theorem initial_transitionKernel_pow_gap_natAbs_sub_gt_eq_zero
    (hn : n ≥ 2) {a : ℕ} (h : a ≤ n) (t : ℕ) :
    (transitionKernel hn ^ t) (initial n a h)
        {c' : Config n |
          t < Int.natAbs (c'.gap - (initial n a h).gap)} = 0 :=
  transitionKernel_pow_gap_natAbs_sub_gt_eq_zero hn (initial n a h) t

/-- Initial-state event wrapper for impossible finite-time gap deviations. -/
theorem initial_transitionKernel_pow_eq_zero_of_forall_gap_natAbs_sub_gt
    (hn : n ≥ 2) {a : ℕ} (h : a ≤ n) (t : ℕ) (S : Set (Config n))
    (hS : ∀ c' : Config n, c' ∈ S →
      t < Int.natAbs (c'.gap - (initial n a h).gap)) :
    (transitionKernel hn ^ t) (initial n a h) S = 0 :=
  transitionKernel_pow_eq_zero_of_forall_gap_natAbs_sub_gt
    hn (initial n a h) t S hS

/-- Initial-state finite Markov executions almost surely preserve an
opinionated agent and move the input gap by at most the number of elapsed
steps. -/
theorem initial_transitionKernel_pow_core_invariants
    (hn : n ≥ 2) {a : ℕ} (h : a ≤ n) (t : ℕ) :
    ∀ᵐ c' ∂((transitionKernel hn ^ t) (initial n a h)),
      c'.hasOpinion ∧
        Int.natAbs (c'.gap - (initial n a h).gap) ≤ t := by
  have hgap :
      ∀ᵐ c' ∂((transitionKernel hn ^ t) (initial n a h)),
        Int.natAbs (c'.gap - (initial n a h).gap) ≤ t := by
    rw [MeasureTheory.ae_iff]
    simpa only [not_le] using
      initial_transitionKernel_pow_gap_natAbs_sub_gt_eq_zero hn h t
  filter_upwards
    [ae_hasOpinion_transitionKernel_pow (initial n a h) hn
      (initial_hasOpinion h (by omega)) t,
     hgap] with c' hop hgap'
  exact ⟨hop, hgap'⟩

/-- The event that an initial finite Markov execution loses all opinionated
agents or moves the gap by more than the elapsed time has probability zero. -/
theorem initial_transitionKernel_pow_core_invariants_fail_eq_zero
    (hn : n ≥ 2) {a : ℕ} (h : a ≤ n) (t : ℕ) :
    (transitionKernel hn ^ t) (initial n a h)
        {c' : Config n |
          ¬ (c'.hasOpinion ∧
            Int.natAbs (c'.gap - (initial n a h).gap) ≤ t)} = 0 := by
  have hcore := initial_transitionKernel_pow_core_invariants hn h t
  rwa [MeasureTheory.ae_iff] at hcore

/-- Any event contained in the failure of the initial finite-time core
invariants has probability zero. -/
theorem initial_transitionKernel_pow_eq_zero_of_forall_core_invariants_fail
    (hn : n ≥ 2) {a : ℕ} (h : a ≤ n) (t : ℕ) (S : Set (Config n))
    (hS : ∀ c' : Config n, c' ∈ S →
      ¬ (c'.hasOpinion ∧
        Int.natAbs (c'.gap - (initial n a h).gap) ≤ t)) :
    (transitionKernel hn ^ t) (initial n a h) S = 0 := by
  refine measure_mono_null ?_
    (initial_transitionKernel_pow_core_invariants_fail_eq_zero hn h t)
  intro c' hc'
  exact hS c' hc'

/-- Having at least one opinionated agent is preserved along every finite
support trace. -/
theorem supportTraceEndpoint_hasOpinion
    (hn : n ≥ 2) (c : Config n) (trace : List (Config n))
    (htrace : supportTrace hn c trace) (hop : c.hasOpinion) :
    (supportTraceEndpoint c trace).hasOpinion := by
  induction trace generalizing c with
  | nil =>
      exact hop
  | cons c' rest ih =>
      rcases htrace with ⟨hsupp, hrest⟩
      exact ih c' hrest (hasOpinion_of_stepDist_support c hn hop hsupp)

/-- A finite support trace starting from an opinionated configuration cannot
end at the all-blank configuration. -/
theorem supportTraceEndpoint_not_allB
    (hn : n ≥ 2) (c : Config n) (trace : List (Config n))
    (htrace : supportTrace hn c trace) (hop : c.hasOpinion) :
    ¬(supportTraceEndpoint c trace).allB := by
  intro hallB
  have hop_end := supportTraceEndpoint_hasOpinion hn c trace htrace hop
  unfold hasOpinion opinionated at hop_end
  unfold allB at hallB
  omega

/-- Initial-state specialization: having at least one opinionated agent is
preserved along every finite stochastic support trace. -/
theorem initial_supportTraceEndpoint_hasOpinion
    (hn : n ≥ 2) {a : ℕ} (h : a ≤ n)
    (trace : List (Config n))
    (htrace : supportTrace hn (initial n a h) trace) :
    (supportTraceEndpoint (initial n a h) trace).hasOpinion :=
  supportTraceEndpoint_hasOpinion hn (initial n a h) trace htrace
    (initial_hasOpinion h (by omega))

/-- Initial-state finite support traces preserve the core deterministic facts
used by the approximate-majority convergence proof: an opinion remains present,
and the integer gap moves by at most the trace length. -/
theorem initial_supportTraceEndpoint_core_invariants
    (hn : n ≥ 2) {a : ℕ} (h : a ≤ n)
    (trace : List (Config n))
    (htrace : supportTrace hn (initial n a h) trace) :
    (supportTraceEndpoint (initial n a h) trace).hasOpinion ∧
      Int.natAbs
        ((supportTraceEndpoint (initial n a h) trace).gap -
          (initial n a h).gap) ≤ trace.length :=
  ⟨initial_supportTraceEndpoint_hasOpinion hn h trace htrace,
    initial_supportTraceEndpoint_gap_bounded hn h trace htrace⟩

/-- Initial configurations of positive size stay away from all-blank along
every finite stochastic support trace. -/
theorem initial_supportTraceEndpoint_not_allB
    (hn : n ≥ 2) {a : ℕ} (h : a ≤ n)
    (trace : List (Config n))
    (htrace : supportTrace hn (initial n a h) trace) :
    ¬(supportTraceEndpoint (initial n a h) trace).allB :=
  supportTraceEndpoint_not_allB hn (initial n a h) trace htrace
    (initial_hasOpinion h (by omega))

end Config
end PopProto
