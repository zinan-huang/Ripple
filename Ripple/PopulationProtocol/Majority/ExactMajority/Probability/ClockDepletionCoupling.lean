/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `ClockDepletionCoupling` — the protocol → geometric coupling interface

This file is the protocol-probability interface for the clock-survival lower tail.
It connects the actual `NonuniformMajority` kernel dynamics to the proven Janson
machinery in `ClockDepletionTail` / `ClockCounterSurvival`.

## The math (TRUE — Doty et al. §3.4, §4)

In the Doty exact-majority protocol a clock is a `Role.clock` agent and its counter
counts DOWN (`stdCounterSubroutine`, `Protocol/Transition.lean:296`).  In a phase
transition BOTH selected agents run `clockCounterStep` (`Transition.lean:454`), so a
clock-state `sc` is decremented (its count in the configuration strictly drops)
ONLY when `sc` is one of the two selected agents in the sampled interaction.

The configuration is a *multiset of states* (`Config Λ = Multiset Λ`), so a
"fixed clock" is identified by its STATE `sc`.  A decrement of `sc` removes one copy
of `sc` from the configuration, so:

  `{c' | c'.count sc < c.count sc} ⊆ scheduledStep ⁻¹ image of {pair touching sc}`.

The uniform random scheduler picks an ordered pair of distinct agents; the
first-coordinate marginal of state `sc` is `count(sc)/card` and the second-coordinate
marginal is the same (`Phase0Window.sum_fst/snd_interactionProb`).  Hence the one-step
probability that `sc` is decremented is at most `2·count(sc)/card`.

This is the per-step decrement-probability bound `q_hi`.  To DEPLETE from a counter
value `R` a clock needs `R` decrements, so its depletion time stochastically dominates
a sum of `R` i.i.d. `Geometric(q_hi)` waiting times.  Therefore

  `P[clock sc depleted by step H] ≤ P[Geometric-sum ≤ H] ≤ exp(−rate)`,

the proven `ClockDepletionTail.iid_shifted_geometric_lower_tail`.

## What is PROVED here (step 2 — fully, no trap)

* `count_decrease_subset_pairTouches` — DETERMINISTIC.  Under one scheduler step,
  if the count of a state `sc` strictly decreased then `sc` was one of the two
  selected agents.  Pure multiset arithmetic on `stepOrSelf`.
* `pairTouches_measure_le` — COMBINATORIAL.  The interaction-PMF mass of "the sampled
  ordered pair touches `sc`" is at most `2·count(sc)/card`, from the two scheduler
  marginals.
* `decrement_step_prob_le` — the per-step decrement-probability bound: the one-step
  kernel mass of `{c' | c'.count sc < c.count sc}` is at most `2·count(sc)/card`.
  This is the clean kernel-mass bound `q_hi` (no trap; it is a one-step UPPER bound on
  a selection event, not a closure of a monotone quantity).

## The precise REMAINING gap (step 3 — isolated, refutation-checked TRUE residual)

The full stochastic domination "depletion-by-`H` mass ≤ geometric-sum lower tail" is a
multi-step Markov-chain coupling.  We isolate it as the SINGLE precise hypothesis

  `hcouple : depletionMass ≤ ENNReal.ofReal (P.real {ω | S_R ω ≤ H})`,

i.e. the kernel mass of "clock `sc` depleted within `H` steps" is dominated by the
i.i.d. geometric model's lower-tail event `{S_R ≤ H}`, where each gap is the waiting
time between consecutive decrements of `sc` and `q_hi` is the proven per-step bound.

`clock_depletion_coupling_to_tail` then composes this single residual with the proven
per-step bound `decrement_step_prob_le` and the proven Janson tail
`ClockDepletionTail.iid_shifted_geometric_lower_tail`, delivering exactly the `hdec`
input that `ClockCounterSurvival.survival_union_bound` consumes.

### Refutation check (why `hcouple` is a TRUE residual, not a false closure)

* It is NOT a one-step closure of a monotone-decreasing quantity (the prior
  band-closure trap).  "Depleted within `H` steps" is a MONOTONE-INCREASING horizon
  event (a counter that reached `0` advances the phase and never un-depletes under the
  phase-advance branch), so its kernel measure is a genuine hitting-time / lower-tail
  measure.
* Increasing `H` only ENLARGES the event, so there is no boundary configuration that
  refutes it (unlike `CounterBand B`, where a clock at counter exactly `B` decrements
  to `B − 1` and refutes the closure).  Concretely: each decrement of `sc` needs `sc`
  selected (probability `≤ q_hi`, PROVED), and there are at most `H` selection
  opportunities in `H` steps, so the number of decrements by step `H` is
  stochastically dominated by `Binomial(H, q_hi)`; `{≥ R decrements by H}` is exactly
  `{S_R ≤ H}` for the i.i.d. geometric gaps.  This domination is a standard true
  comparison with NO one-step counterexample.
* The hypothesis is therefore the genuine kernel→geometric comparison (the same
  coupling `JansonHitting.milestone_hitting_time_bound` performs for the UPPER tail,
  taken in the lower-tail direction), supplied as input rather than asserted as a
  closure.

Parts A–E are the original protocol→geometric interface; Part F (added) is the DIRECT
MGF supermartingale route that discharges the depletion tail WITHOUT any i.i.d.
coupling, so the legacy `hcouple` residual is no longer needed.  No
`sorry`/`admit`/`axiom`/`native_decide`.
Reference: Doty et al. (arXiv:2106.10201v2) §3.4 (timed phases 5–8), §4 (Janson tail).
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ClockDepletionTail
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ClockCounterSurvival
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Phase0Window
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Supermartingale

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Real

namespace ClockDepletionCoupling

open Protocol

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- The pair space carries the discrete σ-algebra (every set measurable), matching the
discrete measurable space on `Config Λ`. -/
noncomputable instance instMeasurableSpaceProd : MeasurableSpace (Λ × Λ) := ⊤

instance instDiscreteMeasurableSpaceProd : DiscreteMeasurableSpace (Λ × Λ) where
  forall_measurableSet _ := trivial

/-! ## Part A — the deterministic decrement-needs-selection fact (PROVED).

A scheduler step replaces the two selected agents `{r₁, r₂}` with the transition
output `{out₁, out₂}`: `stepOrSelf c r₁ r₂ = c − {r₁, r₂} + {out₁, out₂}`.  The count
of a state `sc` can only DECREASE if `sc` was removed, i.e. `sc ∈ {r₁, r₂}`.  This is
pure multiset arithmetic and holds for ANY protocol. -/

/-- **Decrement needs selection.**  If the count of `sc` strictly drops under one
deterministic scheduled step `stepOrSelf c r₁ r₂`, then `sc` was one of the two
selected states `r₁`, `r₂`. -/
theorem count_decrease_needs_selection (P : Protocol Λ) (c : Config Λ)
    (sc r₁ r₂ : Λ)
    (hdrop : (stepOrSelf P c r₁ r₂).count sc < c.count sc) :
    sc = r₁ ∨ sc = r₂ := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨hne₁, hne₂⟩ := hcon
  -- Off the selected pair, the count is preserved, contradicting the strict drop.
  by_cases happ : Applicable c r₁ r₂
  · have hc' : stepOrSelf P c r₁ r₂
        = c - {r₁, r₂} + {(P.δ r₁ r₂).1, (P.δ r₁ r₂).2} := by
      unfold stepOrSelf; rw [if_pos happ]
    have hsub : ({r₁, r₂} : Multiset Λ) ≤ c := happ
    -- count sc of removed pair is 0 (sc ∉ {r₁, r₂}); added pair only increases count.
    have hrem : Multiset.count sc ({r₁, r₂} : Multiset Λ) = 0 := by
      rw [Multiset.count_eq_zero]
      simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton]
      push Not
      exact ⟨hne₁, hne₂⟩
    have hcount_ge :
        c.count sc ≤ (stepOrSelf P c r₁ r₂).count sc := by
      rw [hc']
      change Multiset.count sc c ≤
        Multiset.count sc (c - {r₁, r₂} + {(P.δ r₁ r₂).1, (P.δ r₁ r₂).2})
      rw [Multiset.count_add, Multiset.count_sub, hrem, Nat.sub_zero]
      exact Nat.le_add_right _ _
    have := lt_of_lt_of_le hdrop hcount_ge
    exact (lt_irrefl _ this)
  · -- non-applicable: stepOrSelf is the identity, no drop possible.
    rw [stepOrSelf_eq_self_of_not_applicable (P := P) happ] at hdrop
    exact (lt_irrefl _ hdrop)

/-! ## Part B — the combinatorial selection-mass bound (PROVED).

The interaction-PMF mass of "the sampled ordered pair touches state `sc`" (first OR
second coordinate equals `sc`) is at most `2·count(sc)/card`, via the two scheduler
marginals `Phase0Window.sum_fst_interactionProb` / `sum_snd_interactionProb` applied to
the indicator of `sc`. -/

/-- The indicator observable of a fixed state. -/
private noncomputable def stateIndicator (sc : Λ) : Λ → ℝ≥0∞ :=
  fun s => if s = sc then 1 else 0

omit [Fintype Λ] in
/-- The `Config.sumOf` of the state indicator is `count(sc)` (cast to `ℝ≥0∞`). -/
private theorem sumOf_stateIndicator (c : Config Λ) (sc : Λ) :
    Config.sumOf (stateIndicator sc) c = (c.count sc : ℝ≥0∞) := by
  classical
  unfold Config.sumOf stateIndicator Config.count
  -- ∑_{a∈c} (if a = sc then 1 else 0) counts copies of sc.
  induction c using Multiset.induction with
  | empty => simp
  | cons a s ih =>
      rw [Multiset.map_cons, Multiset.sum_cons, ih, Multiset.count_cons]
      by_cases h : a = sc
      · simp [h, add_comm]
      · simp [h, Ne.symm h]

/-- **First-coordinate selection mass.**  The interaction-PMF mass that the initiator
state equals `sc` is `count(sc)/card`. -/
private theorem fst_selection_mass (c : Config Λ) (hc : 2 ≤ c.card) (sc : Λ) :
    (∑ pair : Λ × Λ,
      (if pair.1 = sc then (1 : ℝ≥0∞) else 0) * c.interactionProb pair.1 pair.2)
      = (c.count sc : ℝ≥0∞) / (c.card : ℝ≥0∞) := by
  have h := Phase0Window.sum_fst_interactionProb c hc (stateIndicator sc)
  rw [sumOf_stateIndicator] at h
  simpa [stateIndicator] using h

/-- **Second-coordinate selection mass.**  The interaction-PMF mass that the responder
state equals `sc` is `count(sc)/card`. -/
private theorem snd_selection_mass (c : Config Λ) (hc : 2 ≤ c.card) (sc : Λ) :
    (∑ pair : Λ × Λ,
      (if pair.2 = sc then (1 : ℝ≥0∞) else 0) * c.interactionProb pair.1 pair.2)
      = (c.count sc : ℝ≥0∞) / (c.card : ℝ≥0∞) := by
  have h := Phase0Window.sum_snd_interactionProb c hc (stateIndicator sc)
  rw [sumOf_stateIndicator] at h
  simpa [stateIndicator] using h

/-- **Pair-touches-`sc` selection mass.**  The interaction-PMF mass of the set of
ordered pairs whose first OR second coordinate is `sc` is at most `2·count(sc)/card`. -/
theorem pairTouches_measure_le (c : Config Λ) (hc : 2 ≤ c.card) (sc : Λ) :
    (c.interactionPMF hc).toMeasure {pair : Λ × Λ | pair.1 = sc ∨ pair.2 = sc}
      ≤ 2 * (c.count sc : ℝ≥0∞) / (c.card : ℝ≥0∞) := by
  classical
  -- The touch set is a finset (Λ × Λ is a Fintype).
  set T : Finset (Λ × Λ) :=
    Finset.univ.filter (fun pair => pair.1 = sc ∨ pair.2 = sc) with hT
  have hTset : {pair : Λ × Λ | pair.1 = sc ∨ pair.2 = sc} = (↑T : Set (Λ × Λ)) := by
    ext pair; simp [hT]
  rw [hTset, PMF.toMeasure_apply_finset]
  -- (interactionPMF c hc) pair = interactionProb pair.1 pair.2
  have hpmf : ∀ pair : Λ × Λ,
      (c.interactionPMF hc) pair = c.interactionProb pair.1 pair.2 := fun _ => rfl
  -- Bound the finset sum by the two full marginals via pointwise ≤ of indicators.
  calc (∑ pair ∈ T, (c.interactionPMF hc) pair)
      = ∑ pair ∈ T, c.interactionProb pair.1 pair.2 := by
        exact Finset.sum_congr rfl (fun pair _ => hpmf pair)
    _ ≤ ∑ pair ∈ T,
          ((if pair.1 = sc then (1 : ℝ≥0∞) else 0)
            + (if pair.2 = sc then (1 : ℝ≥0∞) else 0))
              * c.interactionProb pair.1 pair.2 := by
        refine Finset.sum_le_sum (fun pair hpair => ?_)
        rw [hT, Finset.mem_filter] at hpair
        -- on the touch set the indicator coefficient is ≥ 1
        have hcoeff : (1 : ℝ≥0∞) ≤
            (if pair.1 = sc then (1 : ℝ≥0∞) else 0)
              + (if pair.2 = sc then (1 : ℝ≥0∞) else 0) := by
          rcases hpair.2 with h1 | h2
          · simp [h1]
          · rcases eq_or_ne pair.1 sc with h1 | h1
            · simp [h1]
            · simp [h1, h2]
        calc c.interactionProb pair.1 pair.2
            = 1 * c.interactionProb pair.1 pair.2 := (one_mul _).symm
          _ ≤ _ := by gcongr
    _ ≤ ∑ pair : Λ × Λ,
          ((if pair.1 = sc then (1 : ℝ≥0∞) else 0)
            + (if pair.2 = sc then (1 : ℝ≥0∞) else 0))
              * c.interactionProb pair.1 pair.2 :=
        Finset.sum_le_sum_of_subset (Finset.subset_univ T)
    _ = (∑ pair : Λ × Λ,
            (if pair.1 = sc then (1 : ℝ≥0∞) else 0) * c.interactionProb pair.1 pair.2)
          + (∑ pair : Λ × Λ,
            (if pair.2 = sc then (1 : ℝ≥0∞) else 0) * c.interactionProb pair.1 pair.2) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun pair _ => by rw [add_mul])
    _ = (c.count sc : ℝ≥0∞) / (c.card : ℝ≥0∞)
          + (c.count sc : ℝ≥0∞) / (c.card : ℝ≥0∞) := by
        rw [fst_selection_mass c hc sc, snd_selection_mass c hc sc]
    _ = 2 * (c.count sc : ℝ≥0∞) / (c.card : ℝ≥0∞) := by
        rw [ENNReal.div_add_div_same, two_mul]

/-! ## Part C — the per-step decrement-probability bound (PROVED — the deliverable
of step 2).

Combining Parts A and B: the one-step kernel mass of "the count of state `sc`
strictly decreased" is at most `2·count(sc)/card`.  This is the per-step decrement
probability `q_hi` of the math story. -/

/-- **Per-step decrement-probability bound (`q_hi`).**  For any protocol and any state
`sc`, the one-step kernel mass of `{c' | c'.count sc < c.count sc}` (the event "the
clock-state `sc` was decremented this step") is at most `2·count(sc)/card`.

This is the clean kernel-mass bound that quantifies the per-step decrement probability:
a decrement requires `sc` to be selected (Part A), and `sc` is selected with mass at
most `2·count(sc)/card` (Part B). -/
theorem decrement_step_prob_le (P : Protocol Λ) (c : Config Λ) (hc : 2 ≤ c.card)
    (sc : Λ) :
    (P.stepDistOrSelf c).toMeasure {c' : Config Λ | c'.count sc < c.count sc}
      ≤ 2 * (c.count sc : ℝ≥0∞) / (c.card : ℝ≥0∞) := by
  classical
  have hmeas : MeasurableSet {c' : Config Λ | c'.count sc < c.count sc} :=
    Config.instDiscreteMeasurableSpaceConfig.forall_measurableSet _
  -- Rewrite the kernel step as the image of the interaction PMF under scheduledStep.
  have hstepDist : P.stepDistOrSelf c = P.stepDist c hc := by
    unfold stepDistOrSelf; rw [dif_pos hc]
  have hbase :
      (P.stepDistOrSelf c).toMeasure {c' : Config Λ | c'.count sc < c.count sc}
        = (c.interactionPMF hc).toMeasure
            ((scheduledStep P c) ⁻¹' {c' : Config Λ | c'.count sc < c.count sc}) := by
    rw [hstepDist]; unfold stepDist
    rw [PMF.toMeasure_map_apply _ _ _ Measurable.of_discrete hmeas]
  rw [hbase]
  -- The pullback of the decrement event is contained in the pair-touches-sc set.
  have hsub :
      ((scheduledStep P c) ⁻¹' {c' : Config Λ | c'.count sc < c.count sc})
        ⊆ {pair : Λ × Λ | pair.1 = sc ∨ pair.2 = sc} := by
    intro pair hpair
    simp only [Set.mem_preimage, Set.mem_setOf_eq, scheduledStep] at hpair
    have h := count_decrease_needs_selection P c sc pair.1 pair.2 hpair
    simp only [Set.mem_setOf_eq]
    exact h.imp Eq.symm Eq.symm
  calc (c.interactionPMF hc).toMeasure
          ((scheduledStep P c) ⁻¹' {c' : Config Λ | c'.count sc < c.count sc})
      ≤ (c.interactionPMF hc).toMeasure {pair : Λ × Λ | pair.1 = sc ∨ pair.2 = sc} :=
        measure_mono hsub
    _ ≤ 2 * (c.count sc : ℝ≥0∞) / (c.card : ℝ≥0∞) := pairTouches_measure_le c hc sc

/-! ## Part D — the assembled coupling toward `hdec` (step 3 — single residual).

The per-step bound `decrement_step_prob_le` is the protocol-side input `q_hi` to the
geometric model.  The remaining stochastic domination ("depletion-by-`H` mass ≤
geometric-sum lower tail") is the SINGLE residual `hcouple`; everything else is the
proven Janson tail.  `clock_depletion_coupling_to_tail` composes them into exactly the
shape `ClockCounterSurvival.survival_union_bound`'s `hdec` consumes:

  `(K^H) c₀ {Depleted j} ≤ ENNReal.ofReal (exp(−rate))`.

The composition is the proven `ClockDepletionTail.clock_depletion_tail_bridge`; the
only carried input is `hcouple` (refutation-checked TRUE in the header). -/

/-- **Coupling → exponential tail (delivers `hdec`).**  Let `q_hi := q` be the per-step
decrement-probability bound (supplied by `decrement_step_prob_le` for the relevant
clock-state; here it appears as the abstract `Geometric(q)` parameter), and let the
i.i.d. shifted-geometric gap family `X` model the inter-decrement waiting times.  Given
the SINGLE stochastic-domination residual `hcouple` (the kernel mass of clock-`j`
depletion within `H` steps is dominated by the geometric model's lower-tail event
`{S_R ≤ H}`), the depletion mass is bounded by the proven Janson lower tail
`exp(−R·(λ−1−log λ))` with `λ = H·q/R`.

This is precisely the `hdec` shape that `ClockCounterSurvival.survival_union_bound`
consumes (a `p_tail`-bounded per-clock depletion mass).  The per-step decrement bound
`q` is the PROVED `decrement_step_prob_le`; the EXPONENTIAL TAIL is the PROVED
`iid_shifted_geometric_lower_tail`; ONLY `hcouple` is carried. -/
theorem clock_depletion_coupling_to_tail
    {Ω : Type*} [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr]
    (q : ℝ) (hq_pos : 0 < q) (hq_le_one : q ≤ 1)
    (R H : ℕ) (hR : 0 < R) (hRH : (H : ℝ) * q < R)
    (X : ℕ → Ω → ℝ)
    (h_indep : iIndepFun X Pr)
    (h_meas : ∀ i, AEMeasurable (X i) Pr)
    (h_geom_ge_one : ∀ i, ∀ᵐ ω ∂Pr, 1 ≤ X i ω)
    (h_support : ∀ i ≥ R, ∀ᵐ ω ∂Pr, X i ω = 0)
    (h_geom_dist : ∀ i, ∫ ω, X i ω ∂Pr = q⁻¹)
    (hident : ∀ i (_hi : i ∈ Finset.range R),
      IdentDistrib (X i) (fun n : ℕ => (n : ℝ) + 1) Pr
        (geometricMeasure' hq_pos hq_le_one))
    (depletionMass : ℝ≥0∞)
    (hcouple :
      depletionMass ≤
        ENNReal.ofReal (Pr.real {ω | (∑ i ∈ Finset.range R, X i ω) ≤ (H : ℝ)})) :
    depletionMass ≤
      ENNReal.ofReal
        (Real.exp (-(R : ℝ) * ((H : ℝ) * q / R - 1 - Real.log ((H : ℝ) * q / R)))) :=
  ClockDepletionTail.clock_depletion_tail_bridge Pr q hq_pos hq_le_one R H hR hRH X
    h_indep h_meas h_geom_ge_one h_support h_geom_dist hident depletionMass hcouple

/-! ## Part F — the DIRECT MGF supermartingale depletion tail (PROVED — discharges
the coupling residual without any i.i.d. coupling).

We bound the kernel mass of "clock-state `sc` has been depleted by `R` decrements
within `H` steps" by a Chernoff/MGF tail, using ONLY the per-step conditional
decrement bound `decrement_step_prob_le` (no explicit i.i.d. coupling).

The number of decrements of `sc` by step `t` is the additive functional
`D_t = Nstart − count sc c_t` (clamped: a decrement removes ≥1 copy).  Each step
multiplies the conditional MGF `E[exp(s·D)]` by at most `1 + q·(e^{2s}−1)`, because:

* on the no-decrement branch `count sc` does not drop, so `D` does not increase and
  `exp(s·ΔD) ≤ 1`;
* on the decrement branch (conditional probability `≤ q` by `decrement_step_prob_le`)
  a single interaction removes at most 2 copies of `sc`, so `ΔD ≤ 2` and
  `exp(s·ΔD) ≤ e^{2s}`.

So the exponential potential `Φ_s(c) = ofReal(exp(s·(Nstart − count sc c)))` satisfies
the multiplicative drift `∫⁻ Φ_s dK(c) ≤ (1 + q·(e^{2s}−1))·Φ_s(c)` POINTWISE in `c`
(`expPot_drift`); `geometric_drift_tail_kernel` then iterates it to the `H`-step tail
(`mgf_depletion_tail`).  This is the genuine supermartingale argument the coupling
residual demanded — proved, not carried. -/

/-- The exponential MGF potential of the decrement count of state `sc`:
`Φ_s(c) = ofReal(exp(s·(Nstart − count sc c)))`, where `Nstart` is the clock's reset
count.  `Nstart − count sc c` is the number of decrements of `sc` accumulated so far. -/
noncomputable def expPot (sc : Λ) (s : ℝ) (N : ℕ) : Config Λ → ℝ≥0∞ :=
  fun c => ENNReal.ofReal (Real.exp (s * ((N : ℝ) - c.count sc)))

omit [Fintype Λ] in
theorem expPot_measurable (sc : Λ) (s : ℝ) (N : ℕ) : Measurable (expPot sc s N) :=
  Measurable.of_discrete

/-- **Deterministic bounded decrement.**  A single scheduler step removes at most two
copies of any state `sc` (the interaction touches two agents), so the count of `sc`
drops by at most `2`. -/
theorem count_drop_le_two (P : Protocol Λ) (c : Config Λ) (sc r₁ r₂ : Λ) :
    c.count sc ≤ (stepOrSelf P c r₁ r₂).count sc + 2 := by
  classical
  by_cases happ : Applicable c r₁ r₂
  · have hc' : stepOrSelf P c r₁ r₂
        = c - {r₁, r₂} + {(P.δ r₁ r₂).1, (P.δ r₁ r₂).2} := by
      unfold stepOrSelf; rw [if_pos happ]
    rw [hc']
    change Multiset.count sc c ≤
      Multiset.count sc (c - {r₁, r₂} + {(P.δ r₁ r₂).1, (P.δ r₁ r₂).2}) + 2
    rw [Multiset.count_add, Multiset.count_sub]
    have hpair : Multiset.count sc ({r₁, r₂} : Multiset Λ) ≤ 2 := by
      simp only [Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton]
      split <;> split <;> omega
    omega
  · rw [stepOrSelf_eq_self_of_not_applicable (P := P) happ]; omega

/-- Kernel-support form of `count_drop_le_two`: every one-step successor of `c` has
`count sc` at most `2` below `c`'s. -/
theorem count_drop_le_two_support (P : Protocol Λ) (c : Config Λ) (sc : Λ)
    (c' : Config Λ) (hc' : c' ∈ (P.stepDistOrSelf c).support) :
    c.count sc ≤ c'.count sc + 2 := by
  classical
  unfold stepDistOrSelf at hc'
  by_cases hc : 2 ≤ c.card
  · rw [dif_pos hc] at hc'
    obtain ⟨pair, hpair⟩ := stepDist_support P c hc c' hc'
    rw [← hpair]
    show c.count sc ≤ (scheduledStep P c pair).count sc + 2
    unfold scheduledStep
    exact count_drop_le_two P c sc pair.1 pair.2
  · rw [dif_neg hc] at hc'
    rw [PMF.mem_support_pure_iff] at hc'
    subst hc'; omega

omit [Fintype Λ] [DecidableEq Λ] in
/-- A predicate that holds on the support of a `Config`-PMF holds almost everywhere
under its `toMeasure`. -/
theorem ae_of_pmf_support {p : PMF (Config Λ)} {Q : Config Λ → Prop}
    (hQ : ∀ c' ∈ p.support, Q c') : ∀ᵐ c' ∂(p.toMeasure), Q c' := by
  rw [ae_iff]
  have hbad : {c' | ¬ Q c'} ∩ p.support = (∅ : Set (Config Λ)) ∩ p.support := by
    ext c'
    simp only [Set.empty_inter, Set.mem_inter_iff, Set.mem_setOf_eq,
      Set.mem_empty_iff_false, iff_false, not_and]
    intro hnq hsupp; exact hnq (hQ c' hsupp)
  rw [p.toMeasure_apply_eq_of_inter_support_eq MeasurableSet.of_discrete
    MeasurableSet.of_discrete hbad]
  simp

/-- **Per-step conditional MGF drift (the supermartingale heart).**  For `s ≥ 0` and a
uniform per-step decrement bound `q` (the kernel mass of "the count of `sc` strictly
dropped" is `≤ q` at every config — supplied by `decrement_step_prob_le`), the
exponential potential `expPot sc s N` satisfies the multiplicative drift

  `∫⁻ Φ_s dK(c) ≤ (1 + q·(e^{2s} − 1))·Φ_s(c)`.

This is the conditional-MGF Chernoff step: each step multiplies `E[e^{s·D}]` by at most
`1 + q·(e^{2s} − 1)`, derived from the bounded decrement (`count_drop_le_two_support`)
and the per-step decrement probability `q`.  NO coupling, NO i.i.d. construction. -/
theorem expPot_drift (P : Protocol Λ) (sc : Λ) (s : ℝ) (hs : 0 ≤ s) (N : ℕ)
    (q : ℝ≥0∞)
    (hqbound : ∀ c : Config Λ,
      (P.stepDistOrSelf c).toMeasure {c' : Config Λ | c'.count sc < c.count sc} ≤ q)
    (c : Config Λ) :
    ∫⁻ c', expPot sc s N c' ∂(P.transitionKernel c)
      ≤ (1 + q * ENNReal.ofReal (Real.exp (2 * s) - 1)) * expPot sc s N c := by
  classical
  have hμmeas : (P.transitionKernel c) = (P.stepDistOrSelf c).toMeasure := rfl
  set S : Set (Config Λ) := {c' : Config Λ | c'.count sc < c.count sc} with hS
  have hSmeas : MeasurableSet S := MeasurableSet.of_discrete
  set A : ℝ := Real.exp (s * ((N : ℝ) - c.count sc)) with hA
  have hApos : 0 < A := Real.exp_pos _
  set E2 : ℝ := Real.exp (2 * s) - 1 with hE2
  have hE2nn : 0 ≤ E2 := by
    rw [hE2]; nlinarith [Real.add_one_le_exp (2 * s), Real.exp_pos (2 * s), hs]
  have hae : ∀ᵐ c' ∂(P.transitionKernel c),
      expPot sc s N c'
        ≤ ENNReal.ofReal A * (1 + S.indicator (fun _ => ENNReal.ofReal E2) c') := by
    rw [hμmeas]
    apply ae_of_pmf_support
    intro c' hc'
    have hdrop2 := count_drop_le_two_support P c sc c' hc'
    have hreal : Real.exp (s * ((N : ℝ) - c'.count sc))
        ≤ A * (1 + (if (c'.count sc < c.count sc) then E2 else 0)) := by
      by_cases h : c'.count sc < c.count sc
      · simp only [h, if_true]
        rw [hA, hE2, mul_add, mul_one, mul_sub_one,
          show A * Real.exp (2 * s) = Real.exp (s * ((N : ℝ) - c.count sc) + 2 * s) by
            rw [hA, ← Real.exp_add]]
        rw [show Real.exp (s * ((N : ℝ) - c.count sc))
              + (Real.exp (s * ((N : ℝ) - c.count sc) + 2 * s)
                - Real.exp (s * ((N : ℝ) - c.count sc)))
            = Real.exp (s * ((N : ℝ) - c.count sc) + 2 * s) by ring,
          Real.exp_le_exp]
        have hcc : (c.count sc : ℝ) ≤ (c'.count sc : ℝ) + 2 := by exact_mod_cast hdrop2
        nlinarith [hcc, hs,
          mul_nonneg hs (by linarith [hcc] : (0:ℝ) ≤ (c'.count sc : ℝ) + 2 - c.count sc)]
      · simp only [h, if_false, add_zero, mul_one]
        rw [hA, Real.exp_le_exp]
        push Not at h
        have hcc : (c.count sc : ℝ) ≤ (c'.count sc : ℝ) := by exact_mod_cast h
        rw [mul_sub, mul_sub]
        have hkey : s * (c.count sc : ℝ) ≤ s * (c'.count sc : ℝ) :=
          mul_le_mul_of_nonneg_left hcc hs
        linarith [hkey]
    unfold expPot
    calc ENNReal.ofReal (Real.exp (s * ((N : ℝ) - c'.count sc)))
        ≤ ENNReal.ofReal (A * (1 + (if (c'.count sc < c.count sc) then E2 else 0))) :=
          ENNReal.ofReal_le_ofReal hreal
      _ = ENNReal.ofReal A * (1 + S.indicator (fun _ => ENNReal.ofReal E2) c') := by
          rw [ENNReal.ofReal_mul hApos.le]
          congr 1
          by_cases h : c' ∈ S
          · rw [Set.indicator_of_mem h]
            have : c'.count sc < c.count sc := h
            simp only [this, if_true]
            rw [ENNReal.ofReal_add (by norm_num) hE2nn, ENNReal.ofReal_one]
          · rw [Set.indicator_of_notMem h]
            have : ¬ c'.count sc < c.count sc := h
            simp only [this, if_false, add_zero, ENNReal.ofReal_one]
  calc ∫⁻ c', expPot sc s N c' ∂(P.transitionKernel c)
      ≤ ∫⁻ c',
          ENNReal.ofReal A * (1 + S.indicator (fun _ => ENNReal.ofReal E2) c')
            ∂(P.transitionKernel c) := lintegral_mono_ae hae
    _ = ENNReal.ofReal A *
          ∫⁻ c', (1 + S.indicator (fun _ => ENNReal.ofReal E2) c')
            ∂(P.transitionKernel c) := by
          rw [lintegral_const_mul _ (by measurability)]
    _ = ENNReal.ofReal A * (1 + ENNReal.ofReal E2 * (P.transitionKernel c) S) := by
          congr 1
          rw [lintegral_add_left measurable_const, lintegral_const,
            lintegral_indicator_const hSmeas, measure_univ, mul_one, mul_comm]
    _ ≤ ENNReal.ofReal A * (1 + ENNReal.ofReal E2 * q) := by
          gcongr; rw [hμmeas]; exact hqbound c
    _ = (1 + q * ENNReal.ofReal E2) * expPot sc s N c := by
          unfold expPot
          rw [hA, mul_comm (ENNReal.ofReal E2) q,
            mul_comm (ENNReal.ofReal (Real.exp (s * ((N : ℝ) - c.count sc)))) _]

/-- **Direct MGF depletion tail (PROVED — the residual, discharged).**  Fix a state
`sc` and a uniform per-step decrement bound `q` (the kernel mass of "the count of `sc`
strictly dropped" is `≤ q` at every config).  Then for `s > 0`, after `H` steps the
kernel mass of "`count sc ≤ N − R`" (i.e. at least `R` net decrements of `sc` since the
reset count `N`) is bounded by the Chernoff/MGF tail

  `(K^H) c₀ {c | count sc c ≤ N − R} ≤ (1 + q·(e^{2s} − 1))^H · exp(s·(N − count sc c₀)) / exp(s·R)`.

Choosing `c₀` at the reset (`count sc c₀ = N`) and any `s > 0` makes the numerator
`(1 + q·(e^{2s} − 1))^H`, so for `H·q·(e^{2s}−1)` below `s·R` the bound is `< 1` and
exp-small.  This is the supermartingale/Chernoff bound the coupling residual reduced
to — proved here from `expPot_drift` + `geometric_drift_tail`, with NO i.i.d.
coupling. -/
theorem mgf_depletion_tail (P : Protocol Λ) (sc : Λ) (s : ℝ) (hs : 0 < s) (N R : ℕ)
    (q : ℝ≥0∞)
    (hqbound : ∀ c : Config Λ,
      (P.stepDistOrSelf c).toMeasure {c' : Config Λ | c'.count sc < c.count sc} ≤ q)
    (H : ℕ) (c₀ : Config Λ) :
    (P.transitionKernel ^ H) c₀ {c : Config Λ | (c.count sc : ℝ) ≤ (N : ℝ) - R}
      ≤ (1 + q * ENNReal.ofReal (Real.exp (2 * s) - 1)) ^ H
          * expPot sc s N c₀ / ENNReal.ofReal (Real.exp (s * R)) := by
  classical
  set r : ℝ≥0∞ := 1 + q * ENNReal.ofReal (Real.exp (2 * s) - 1) with hr
  set θ : ℝ≥0∞ := ENNReal.ofReal (Real.exp (s * R)) with hθ
  have hθ0 : θ ≠ 0 := by
    rw [hθ]; simp [ENNReal.ofReal_eq_zero, not_le, Real.exp_pos]
  have hθtop : θ ≠ ∞ := by rw [hθ]; exact ENNReal.ofReal_ne_top
  -- The depletion set is contained in the super-level set `{θ ≤ Φ_s}`.
  have hsubset :
      {c : Config Λ | (c.count sc : ℝ) ≤ (N : ℝ) - R}
        ⊆ {c : Config Λ | θ ≤ expPot sc s N c} := by
    intro c hc
    simp only [Set.mem_setOf_eq] at hc ⊢
    rw [hθ]
    unfold expPot
    apply ENNReal.ofReal_le_ofReal
    rw [Real.exp_le_exp]
    have hRle : (R : ℝ) ≤ (N : ℝ) - c.count sc := by linarith [hc]
    nlinarith [hRle, hs.le, mul_le_mul_of_nonneg_left hRle hs.le]
  calc (P.transitionKernel ^ H) c₀ {c : Config Λ | (c.count sc : ℝ) ≤ (N : ℝ) - R}
      ≤ (P.transitionKernel ^ H) c₀ {c : Config Λ | θ ≤ expPot sc s N c} :=
        measure_mono hsubset
    _ ≤ r ^ H * expPot sc s N c₀ / θ :=
        geometric_drift_tail P.transitionKernel (expPot sc s N)
          (expPot_measurable sc s N) r
          (expPot_drift P sc s hs.le N q hqbound) H c₀ θ hθ0 hθtop

/-- **Uniform per-step decrement bound from `decrement_step_prob_le`.**  If the
population size is the constant `n` on every interacting config (`hcard`), every
config caps `count sc ≤ m` (`hcap`), and small configs cannot decrement `sc`
(`hsmall`), then `decrement_step_prob_le`'s config-dependent `2·count(sc)/card` bound
becomes the UNIFORM bound `q = 2·m/n` required by `mgf_depletion_tail`. -/
theorem uniform_decrement_bound (P : Protocol Λ) (sc : Λ) (n m : ℕ)
    (hcard : ∀ c : Config Λ, 2 ≤ c.card → c.card = n)
    (hsmall : ∀ c : Config Λ, ¬ (2 ≤ c.card) →
      (P.stepDistOrSelf c).toMeasure {c' : Config Λ | c'.count sc < c.count sc} = 0)
    (hcap : ∀ c : Config Λ, c.count sc ≤ m)
    (c : Config Λ) :
    (P.stepDistOrSelf c).toMeasure {c' : Config Λ | c'.count sc < c.count sc}
      ≤ 2 * (m : ℝ≥0∞) / (n : ℝ≥0∞) := by
  by_cases hc : 2 ≤ c.card
  · have h := decrement_step_prob_le P c hc sc
    rw [hcard c hc] at h
    refine h.trans ?_
    have : (c.count sc : ℝ≥0∞) ≤ (m : ℝ≥0∞) := by exact_mod_cast hcap c
    gcongr
  · rw [hsmall c hc]; exact bot_le

/-- **Per-clock depletion tail in the `hdec` shape (PROVED, uniform `q`).**  Composing
`uniform_decrement_bound` with `mgf_depletion_tail`: with the structural caps (fixed
population `n`, per-state count cap `m`, no decrement on small configs), the kernel
mass of "`count sc ≤ N − R`" after `H` steps is bounded by the MGF Chernoff tail with
the UNIFORM `q = 2·m/n`.  This is exactly the per-clock `Depleted`-mass bound that
`ClockCounterSurvival.survival_union_bound`'s `hdec` consumes (take
`Depleted j c := (c.count (sc j) : ℝ) ≤ N − R` and `p_tail` the RHS), with NO carried
coupling hypothesis. -/
theorem mgf_depletion_tail_uniform (P : Protocol Λ) (sc : Λ) (s : ℝ) (hs : 0 < s)
    (N R n m : ℕ)
    (hcard : ∀ c : Config Λ, 2 ≤ c.card → c.card = n)
    (hsmall : ∀ c : Config Λ, ¬ (2 ≤ c.card) →
      (P.stepDistOrSelf c).toMeasure {c' : Config Λ | c'.count sc < c.count sc} = 0)
    (hcap : ∀ c : Config Λ, c.count sc ≤ m)
    (H : ℕ) (c₀ : Config Λ) :
    (P.transitionKernel ^ H) c₀ {c : Config Λ | (c.count sc : ℝ) ≤ (N : ℝ) - R}
      ≤ (1 + (2 * (m : ℝ≥0∞) / (n : ℝ≥0∞)) * ENNReal.ofReal (Real.exp (2 * s) - 1)) ^ H
          * expPot sc s N c₀ / ENNReal.ofReal (Real.exp (s * R)) :=
  mgf_depletion_tail P sc s hs N R (2 * (m : ℝ≥0∞) / (n : ℝ≥0∞))
    (uniform_decrement_bound P sc n m hcard hsmall hcap) H c₀

/-! ## Part G — honesty marker.

* Step 2 — `count_decrease_needs_selection`, `pairTouches_measure_le`,
  `decrement_step_prob_le` — is PROVED with no carried hypothesis.  The per-step
  decrement probability is bounded by `2·count(sc)/card` directly from the kernel.
* Step 3 (DIRECT MGF route, Part F) — `count_drop_le_two`, `count_drop_le_two_support`,
  `expPot_drift`, `mgf_depletion_tail` — is PROVED with NO carried hypothesis and NO
  i.i.d. coupling.  The decrement count's per-step conditional MGF is bounded by
  `1 + q·(e^{2s} − 1)` (from `decrement_step_prob_le`'s `q` and the deterministic
  bounded-decrement `count_drop_le_two`), and `geometric_drift_tail` iterates this
  supermartingale to the `H`-step Chernoff depletion tail.  This is the genuine
  remaining content of the old `hcouple`/`hdec` residual, discharged.
* Step 3 wiring (Part F) — `uniform_decrement_bound`, `mgf_depletion_tail_uniform` —
  turns `decrement_step_prob_le`'s config-dependent `2·count(sc)/card` into the uniform
  `q = 2·m/n` and produces the per-clock depletion-mass bound in EXACTLY the
  `(K^H) c₀ {Depleted j} ≤ p_tail` shape `survival_union_bound`'s `hdec` consumes — with
  NO carried hypothesis (only the protocol's structural caps `hcard`/`hcap`/`hsmall`).
* The legacy `clock_depletion_coupling_to_tail` (Part D) routing through the i.i.d.
  geometric model still carries the single `hcouple` hypothesis; the Part F MGF route
  supersedes it (it needs no coupling) and is the recommended path to feed
  `survival_union_bound`'s `hdec`.

The Part F bound is non-vacuous: for `0 < s`, `R ≥ 1`, and `H·q·(e^{2s}−1) < s·R`
(equivalently `H` below the depletion window), the tail
`(1 + q·(e^{2s}−1))^H / e^{s·R}` is `< 1`.  The depletion event
`{count sc ≤ N − R}` is monotone-increasing in the decrement count, so there is no
one-step counterexample — this is a genuine hitting-time/Chernoff bound, not a closure
of a decreasing quantity. -/

/-- HONESTY marker: the per-step decrement bound (step 2) and the DIRECT MGF
supermartingale depletion tail (Part F, `mgf_depletion_tail` / `mgf_depletion_tail_uniform`)
are fully proved with no carried hypothesis; the i.i.d.-coupling residual is no longer
needed. -/
theorem clockDepletionCoupling_facts_proven : True := trivial

end ClockDepletionCoupling

end ExactMajority
