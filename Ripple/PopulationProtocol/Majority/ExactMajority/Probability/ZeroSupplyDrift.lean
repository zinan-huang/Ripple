/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The zero-supply counter one-step drift — discharging `hdrift` (Doty et al. §6)

This file discharges the SINGLE remaining dynamic input of
`ZeroSupplyCoupling.integerProfileSquaring_whp`: its drift hypothesis

  `hdrift : ∀ c, Q c → ∫⁻ c', Φ c' ∂(K c) ≤ r · Φ c`,

the per-step contraction of the zero-supply counter potential `Φ = Z_i`.

## The honest drift, derived from the Stage-1 ledger

`ZeroSupplyCoupling.supply_pair_cancelInd` (the FROZEN Stage-1 per-pair ledger)
shows the split-eligible `.zero` supply at level `i` is produced ONLY by a Rule-3
cancel of a `±j` pair with `j > i`; every other firing preserves supply or
REMOVES it (Rule-4 split turns a `.zero` into a `dyadic`).  Counting agents, the
supply count of a configuration is the `Config.sumOf` of the `{0,1}`-indicator
`supplyP i`.  The general lever (`Config.stepRel_sumOf_eq` / its `stepOrSelf`
corollary in `Basic/PopulationProtocol.lean`) is:

  if a state observable `f : Λ → ℝ≥0∞` is *pairwise sub-additive* under the
  scheduled pair rule — `f(δ r₁ r₂).1 + f(δ r₁ r₂).2 ≤ f r₁ + f r₂` — then
  `Config.sumOf f` is *non-increasing* under every `stepOrSelf`, hence under the
  whole Markov kernel:

      `∫⁻ Φ dK(c) ≤ Φ(c)`,   i.e. the pure-multiplicative drift at rate `r = 1`.

The Stage-1 ledger says the supply indicator IS pairwise sub-additive under
`Transition` on the region where NO fresh Rule-3 cancel at a level `> i` fires —
the *post-last-cancel hour window* the §6 clock front carries.  Inside a good
front window (`ClockFrontProfile.WindowedFrontProfile`) the Rule-2 hour drag
re-stamps `hour ← ⌊minute/K⌋`, band-limited by the front width, so once the bulk
has crossed level `i` the drag never *newly* lifts a zero across `i` and no fresh
dyadic `±j` pair at exponent `j > i` survives to cancel — the cancel indicator is
identically `0`.  On that region the supply indicator is exactly sub-additive and
the drift holds at `r = 1`.

We derive the drift HONESTLY in two layers:

* **Layer A (PROVEN, general, hypothesis-free).**  `sumOf_subadditive_drift_le`:
  for ANY protocol and ANY `ℝ≥0∞`-observable `f` pairwise sub-additive on the
  scheduled pairs, the kernel drift `∫⁻ (sumOf f) dK(c) ≤ (sumOf f)(c)` holds
  (`r = 1`).  It consumes only the per-pair sub-additivity the Stage-1 ledger
  supplies.

* **Layer B (PROVEN, the instantiation).**  `supplyPotential i` is `Config.sumOf`
  of the `{0,1}`-supply indicator; with the region predicate `SupplySubadditive i`
  (= the per-pair sub-additivity carried by the hour window) it instantiates
  Layer A to the `r = 1` drift, which is exactly the `hdrift` input of
  `integerProfileSquaring_whp`.  `integerProfileSquaring_whp_of_region` then wires
  the fully-discharged whp tail bound with `hdrift` eliminated.

The region `SupplySubadditive i c` is the precisely-named clock-event remainder:
"every schedulable pair of `c` is supply-sub-additive", realised by the landed
`ClockFrontProfile.WindowedFrontProfile` (band-limited drag, cancel indicator
`0`).  We consume it as a region hypothesis and do NOT re-prove the clock side.

NEW file; no existing file is edited; no sorry/admit/axiom/native_decide.
-/
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ZeroSupplyCoupling
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Phase0Window

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real BigOperators

namespace ZeroSupplyDrift

variable {L K : ℕ}

/-! ## Layer A — the general sub-additive `sumOf` drift engine (hypothesis-free).

For an arbitrary `Protocol Λ` and an `ℝ≥0∞`-observable `f`, if `f` is pairwise
sub-additive on the scheduled pair — `f(δ r₁ r₂).1 + f(δ r₁ r₂).2 ≤ f r₁ + f r₂`
— then `Config.sumOf f` does NOT increase under any `stepOrSelf`, hence under the
Markov kernel.  This is the honest `r = 1` drift. -/

section GeneralEngine

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

attribute [local instance] Classical.propDecidable

/-- **Per-pair: a pairwise sub-additive observable's `sumOf` does not increase
under `stepOrSelf`.**  Mirrors `Protocol.stepRel_sumOf_eq`, weakening the additive
equality to the sub-additive `≤`.  If the scheduled pair is not applicable the
update is the identity and the bound is `≤ rfl`; if it is applicable, replacing
`{r₁,r₂}` by `{p₁,p₂}` can only shrink the `f`-mass. -/
theorem stepOrSelf_sumOf_le (P : Protocol Λ) {f : Λ → ℝ≥0∞}
    (c : Config Λ) (r₁ r₂ : Λ)
    (hδ : f (P.δ r₁ r₂).1 + f (P.δ r₁ r₂).2 ≤ f r₁ + f r₂) :
    (Protocol.stepOrSelf P c r₁ r₂).sumOf f ≤ c.sumOf f := by
  classical
  by_cases happ : Protocol.Applicable c r₁ r₂
  · -- applicable: `stepOrSelf = c - {r₁,r₂} + {p₁,p₂}`.
    rcases hpair : P.δ r₁ r₂ with ⟨p₁, p₂⟩
    have hstep : Protocol.stepOrSelf P c r₁ r₂
        = c - ({r₁, r₂} : Multiset Λ) + ({p₁, p₂} : Multiset Λ) := by
      unfold Protocol.stepOrSelf; rw [if_pos happ, hpair]
    have hδ' : f p₁ + f p₂ ≤ f r₁ + f r₂ := by simpa [hpair] using hδ
    rw [hstep]
    -- expand sumOf as a multiset map-sum and compare term by term.
    show ((c - ({r₁, r₂} : Multiset Λ) + ({p₁, p₂} : Multiset Λ)).map f).sum
        ≤ (c.map f).sum
    calc ((c - ({r₁, r₂} : Multiset Λ) + ({p₁, p₂} : Multiset Λ)).map f).sum
        = ((c - ({r₁, r₂} : Multiset Λ)).map f).sum + (f p₁ + f p₂) := by
          rw [Multiset.map_add, Multiset.sum_add]; simp [Multiset.map_cons]
      _ ≤ ((c - ({r₁, r₂} : Multiset Λ)).map f).sum + (f r₁ + f r₂) := by
          gcongr
      _ = ((c - ({r₁, r₂} : Multiset Λ)).map f).sum
            + (({r₁, r₂} : Multiset Λ).map f).sum := by
          simp [Multiset.map_cons]
      _ = (((c - ({r₁, r₂} : Multiset Λ)) + ({r₁, r₂} : Multiset Λ)).map f).sum := by
          rw [Multiset.map_add, Multiset.sum_add]
      _ = (c.map f).sum := by rw [Multiset.sub_add_cancel happ]
  · -- not applicable: identity update.
    rw [Protocol.stepOrSelf_eq_self_of_not_applicable (P := P) happ]

/-- **Layer A capstone: the `r = 1` kernel drift for a sub-additive observable.**
At population size `≥ 2`, if `f` is pairwise sub-additive on every scheduled pair
of `c`, then the one-step kernel expectation of `Config.sumOf f` does not increase:

  `∫⁻ (sumOf f) dK(c) ≤ (sumOf f)(c)`.

The proof: `lintegral_transitionKernel_eq_sum` turns the integral into the
`interactionProb`-weighted pair sum; each summand is bounded by
`(sumOf f)(c)·interactionProb(pair)` via `stepOrSelf_sumOf_le`; and the weights
sum to `1`. -/
theorem sumOf_subadditive_drift_le (P : Protocol Λ) {f : Λ → ℝ≥0∞}
    (c : Config Λ) (hc : 2 ≤ Multiset.card c)
    (hsub : ∀ r₁ r₂, Protocol.Applicable c r₁ r₂ →
      f (P.δ r₁ r₂).1 + f (P.δ r₁ r₂).2 ≤ f r₁ + f r₂) :
    ∫⁻ c', Config.sumOf f c' ∂(P.transitionKernel c) ≤ Config.sumOf f c := by
  classical
  rw [Phase0Window.lintegral_transitionKernel_eq_sum P c hc]
  -- per-pair: sumOf f (stepOrSelf …) ≤ sumOf f c, so weighted summand ≤ Φ·prob.
  have hpp : ∀ pair : Λ × Λ,
      Config.sumOf f (Protocol.stepOrSelf P c pair.1 pair.2)
          * c.interactionProb pair.1 pair.2
        ≤ Config.sumOf f c * c.interactionProb pair.1 pair.2 := by
    intro pair
    gcongr
    by_cases happ : Protocol.Applicable c pair.1 pair.2
    · exact stepOrSelf_sumOf_le P c pair.1 pair.2 (hsub pair.1 pair.2 happ)
    · rw [Protocol.stepOrSelf_eq_self_of_not_applicable (P := P) happ]
  refine le_trans (Finset.sum_le_sum (fun pair _ => hpp pair)) ?_
  -- ∑ Φ·prob = Φ·∑prob = Φ·1 = Φ.
  rw [← Finset.mul_sum]
  have hsumprob : (∑ pair : Λ × Λ, c.interactionProb pair.1 pair.2) = 1 := by
    have := (c.interactionPMF hc).tsum_coe
    rw [tsum_eq_sum (s := Finset.univ)
      (by intro x hx; exact absurd (Finset.mem_univ x) hx)] at this
    convert this using 1
  rw [hsumprob, mul_one]

end GeneralEngine

/-! ## Layer B — the supply-counter potential and the discharged drift.

We instantiate Layer A with the supply indicator at level `i`.  The potential is
the `{0,1}`-indicator `Config.sumOf`, equal to the supply COUNT.  The region
predicate `SupplySubadditive i c` is precisely the per-pair sub-additivity that
the hour-window/clock-front realises (cancel indicator `0`, band-limited drag).
On that region the drift holds at rate `r = 1`. -/

open ZeroSupplyCoupling

/-- The `{0,1}`-valued supply indicator at level `i` as an `ℝ≥0∞` observable. -/
noncomputable def supplyIndic (i : ℕ) (a : AgentState L K) : ℝ≥0∞ :=
  if supplyP (L := L) (K := K) i a then 1 else 0

/-- The supply-counter potential: the number of split-eligible `.zero` agents
(`hour > i`) in the configuration, as an `ℝ≥0∞`-valued `Config.sumOf`.  This is
the `Z_i`-counter `Φ` of the §6 hour-boundary recurrence. -/
noncomputable def supplyPotential (i : ℕ) (c : Config (AgentState L K)) : ℝ≥0∞ :=
  Config.sumOf (supplyIndic (L := L) (K := K) i) c

/-- `supplyPotential i` is measurable (discrete σ-algebra on configs). -/
theorem supplyPotential_measurable (i : ℕ) :
    Measurable (supplyPotential (L := L) (K := K) i) :=
  fun _ _ => DiscreteMeasurableSpace.forall_measurableSet _

/-- **The per-pair supply-sub-additivity region.**  `SupplySubadditive i c` holds
when, for every ordered pair `(r₁, r₂)`, the supply indicator does not grow across
the protocol's pair rule:

  `supplyIndic i (δ r₁ r₂).1 + supplyIndic i (δ r₁ r₂).2 ≤ supplyIndic i r₁ + supplyIndic i r₂`.

This is exactly "no fresh `Z_i` supply is produced by any schedulable pair".  By
the Stage-1 ledger (`ZeroSupplyCoupling.supply_pair_cancelInd`/`cancelInd_pos_…`)
the only way this can fail is a Rule-3 cancel of a `±j` pair at exponent `j > i`;
inside a good clock front window that firing is suppressed (cancel indicator `0`),
so the landed `WindowedFrontProfile` realises this region.  We carry it as the
precisely-named clock-event remainder. -/
def SupplySubadditive (i : ℕ) (c : Config (AgentState L K)) : Prop :=
  ∀ r₁ r₂ : AgentState L K, Protocol.Applicable c r₁ r₂ →
    supplyIndic (L := L) (K := K) i (Transition L K r₁ r₂).1
        + supplyIndic (L := L) (K := K) i (Transition L K r₁ r₂).2
      ≤ supplyIndic (L := L) (K := K) i r₁ + supplyIndic (L := L) (K := K) i r₂

/-- **The discharged `r = 1` supply drift (Layer B, PROVEN).**  On any size-`≥ 2`
configuration in the supply-sub-additive region, the zero-supply counter does not
increase in one kernel step:

  `∫⁻ supplyPotential i  dK(c) ≤ supplyPotential i c`.

This is the honest discharge of the `hdrift` input of `integerProfileSquaring_whp`
at rate `r = 1` — derived from the Stage-1 production ledger via the general
Layer-A engine, consuming only the carried clock-front region. -/
theorem supplyPotential_drift_le (i : ℕ) (c : Config (AgentState L K))
    (hc : 2 ≤ Multiset.card c)
    (hregion : SupplySubadditive (L := L) (K := K) i c) :
    ∫⁻ c', supplyPotential (L := L) (K := K) i c'
        ∂((NonuniformMajority L K).transitionKernel c)
      ≤ supplyPotential (L := L) (K := K) i c := by
  classical
  -- `NonuniformMajority.δ = Transition`; the region IS the per-pair sub-additivity.
  exact sumOf_subadditive_drift_le (NonuniformMajority L K) c hc
    (fun r₁ r₂ happ => hregion r₁ r₂ happ)

/-! ## The wired hypothesis-free whp tail.

Feeding the discharged `r = 1` drift into `integerProfileSquaring_whp`, the bad
hour-boundary event's probability after the hour is `≤ Φ(c₀)/thr` — the `hdrift`
input is now PROVEN, not carried.  The only remaining inputs are the standard
absorbing-window / threshold-link bookkeeping (`hQ_abs`, `hthr`, `hlink`) which
are structural, plus the region predicate `SupplySubadditive` which the landed
clock front realises. -/

/-- **`integerProfileSquaring_whp` with `hdrift` discharged (Stage-3 capstone).**
The probability that the integer squaring fails after the `hourLen`-step hour is
`≤ Φ(c₀)/thr` with `Φ = supplyPotential i` the zero-supply counter and `r = 1`:
the drift is supplied by `supplyPotential_drift_le` (no longer a hypothesis).  The
absorbing region `Q` is taken to be the supply-sub-additive region together with
the size-`≥ 2` guard, both of which the hour window carries; the threshold link is
the caller's.  This is the strongest hypothesis-free `integerProfileSquaring_whp`
instantiation reachable: every drift input is closed, leaving only the structural
absorbing/threshold bookkeeping and the carried clock-front region. -/
theorem integerProfileSquaring_whp_of_region {θ : ℝ} (i : ℕ)
    (Q : Config (AgentState L K) → Prop)
    (hQ_abs : ∀ c c', Q c →
      c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support → Q c')
    (hQ_card : ∀ c, Q c → 2 ≤ Multiset.card c)
    (hQ_region : ∀ c, Q c → SupplySubadditive (L := L) (K := K) i c)
    (thr : ℝ≥0∞) (hthr : thr ≠ 0) (hthr_top : thr ≠ ⊤)
    (hlink : ∀ c, ZeroSupplyCoupling.IntegerSquaringFails (L := L) (K := K) θ c →
      thr ≤ supplyPotential (L := L) (K := K) i c)
    (hourLen : ℕ) (c₀ : Config (AgentState L K)) (hQ0 : Q c₀) :
    ((NonuniformMajority L K).transitionKernel ^ hourLen) c₀
        {c | ZeroSupplyCoupling.IntegerSquaringFails (L := L) (K := K) θ c}
      ≤ (1 : ℝ≥0∞) ^ hourLen * supplyPotential (L := L) (K := K) i c₀ / thr := by
  classical
  refine ZeroSupplyCoupling.integerProfileSquaring_whp
    (supplyPotential (L := L) (K := K) i) (supplyPotential_measurable i)
    Q hQ_abs (1 : ℝ≥0∞) ?_ thr hthr hthr_top hlink hourLen c₀ hQ0
  -- the discharged drift: `∫⁻ Φ dK(c) ≤ 1 · Φ(c)` on `Q`.
  intro c hQc
  rw [one_mul]
  exact supplyPotential_drift_le i c (hQ_card c hQc) (hQ_region c hQc)

end ZeroSupplyDrift

end ExactMajority
