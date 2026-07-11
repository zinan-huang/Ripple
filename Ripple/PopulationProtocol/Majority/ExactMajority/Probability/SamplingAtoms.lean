/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# SamplingAtoms — the two remaining inputs of the slot-5 sampling concentration

`SampledClassTail.lean` re-bases the Lemma 7.1 sampled-class concentration on the KILLED gate and
narrows the genuinely-probabilistic residual to two named atoms (its `hConcDemand_of_real_window`):

* **ATOM 1 — `hrfloor`** (the per-step rise-probability rate floor; the genuine Chernoff content);
* **ATOM 2 — the clock-separation escape** (the per-`τ` prefix mass `(K^τ) c₀ {θ ≤ Φ}` that leaving
  `Phase5AllWin` is timing-governed, not a `sampledReserveClassU`-threshold event).

This file (Wave 3, roster #9; append-only, edits NO existing file) discharges the atoms to the
honest depth each genuinely reaches.

## ATOM 1 — `hrfloor`: PRODUCED from {entry class floor + reserve floor + static persistence}.

During phase 5 the Main bias profile is FROZEN (`SampledClassTail`/`biasedMainClassU_support_eq`:
Phase-5 rules do not modify Main biases), so the sampled-class drift's per-step rate is governed by
the ENTRY-time class profile.  The landed Chernoff content is
`Phase5Convergence.sampledReserveClassU_rise_prob_rect5`: on a phase-5 window the one-step rise
probability is `≥ (#unsampledReserves · #classMains_σi) / (n(n−1))` — the cross-rectangle sampling
mass.  We DERIVE the constant rate floor `r := (reserveFloor · classFloor) / (n(n−1))` from:

* **the entry class floor** `classFloor ≤ (classMainStates σ i).sum c.count` — the count of class-`i`
  biased Mains at entry (carried as the named Thm-6.2 `usefulMains`-chain input; FROZEN through
  phase 5 by the static-profile persistence, so the entry bound transports to every step `c`);
* **the reserve floor** `reserveFloor ≤ (unsampledReserves).sum c.count` — the unsampled-Reserve
  count floor (`RoleSplitGood`'s `reserveCount ≥ (1−η)·n/4`-flavored export, restricted to the
  unsampled ones still present at the step `c`);
* **static persistence** — both floors are carried as `∀ c ∈ gate` hypotheses, which IS the
  per-step transport of the entry-time profile through the FROZEN phase-5 rules.

`hrfloor_of_floors` produces the exact `hrfloor` shape `SampledClassTail` consumes from these three
named inputs by `Nat`-product monotonicity into the rise-rectangle floor.  This is the honest
production of ATOM 1: the genuine Chernoff rectangle is `sampledReserveClassU_rise_prob_rect5`
(landed); the constant rate is the carried entry floors transported by the static profile.

## ATOM 2 — the clock-separation escape: HONEST NEGATIVE VERDICT (the seam tail does NOT apply).

The prompt's proposed route — instantiate the `ClockZeroTail`/`SeamNoOvershoot` seam tail with the
`p = 4 → 5` roles swapped, getting the `e^{−40(L+1)}`-flavored budget — is **STRUCTURALLY BLOCKED**,
verified against the FROZEN transition rules:

* The seam tail (`ClockZeroTail.seam_atRiskTail_of_entry`) requires `CounterResetDest (p+1)`, i.e.
  `p+1 ∈ {1,6,7,8}` (`SeamPairAdapter.CounterResetDest`).  For the phase-5 window the destination is
  `p+1 = 5`, and `CounterResetDest 5` is **FALSE** (the set is `CounterTimedPhase` *minus phase 5*).
* The structural reason (`SeamPairBound.lean` FINDING 2, lines 44–53): the predecessor
  `Phase4Transition` advances clocks via `advancePhase` (the big-bias gate), which does NOT run
  `phaseInit` / reset the counter.  A clock counter-advanced from phase 4 into phase 5 keeps its OLD
  (possibly small) counter — its seam summand is up to `1`, NOT `freshVal` — so
  `SeamEntryFullCounter 4` (`ClockZeroTail`: "every phase-`(p+1)` clock at full counter
  `50(L+1)`") is FALSE at phase-5 entry, and `seamClockPotential_init_le`'s hypothesis cannot be
  discharged.  This BREAKS the affine immigration tail for the phase-5 seam.

So the `e^{−40(L+1)}` budget is NOT available for the phase-5 escape through the seam machinery: the
phase-5 counter-drain is governed by the dedicated minute/hour width machinery (`ClockOLogN` /
`ClockReal*`), not the seam no-overshoot tail.  We do NOT manufacture a false `e^{−40(L+1)}`.
Instead ATOM 2 stays a **named carry**: `clockSeparationEscape n s i K₀ t β` is the exact per-`τ`
prefix-mass uniform bound `SampledClassTail.hConcDemand_of_real_window` consumes (`hβ`).  This is
the genuine residual — pinned with its file:line provenance, not behind a wrong instantiation.

## The assembled slot-5 surface.

`hConcDemand_of_atoms` feeds ATOM 1 (produced) into `SampledClassTail.hConcDemand_of_real_window`,
leaving exactly: the entry floors (ATOM 1's named inputs), the exit bridge `hbridge`
(the Phase-5/Phase-6 clock separation), the per-`τ` escape `clockSeparationEscape` (ATOM 2's named
remainder), and the single arithmetic fit `hε`.  `phase5Convergence_of_atoms` then composes with
`EndpointWiring.phase5Convergence_of_hConc` so slot 5 is hypothesis-free but for those inputs.

This file is APPEND-ONLY and edits NO existing file.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.SampledClassTail

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace SamplingAtoms

open Phase5Convergence ReserveSampling GatedDrift SampledClassTail

variable {L K : ℕ}

/-! ## ATOM 1 — the rise-probability rate floor, produced from the entry floors. -/

/-- **`rateFloor`** — the constant per-step rise-probability rate, derived from the entry-time
class floor `classFloor` and the unsampled-reserve floor `reserveFloor`:
`r = (reserveFloor · classFloor) / (n(n−1))`.  This is the static-profile rate the phase-5
sampled-class drift contracts at (the entry-class profile is FROZEN through phase 5). -/
noncomputable def rateFloor (reserveFloor classFloor n : ℕ) : ℝ :=
  ((reserveFloor * classFloor : ℕ) : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))

/-- The rate floor is nonnegative (for `n ≥ 2` the denominator is positive). -/
theorem rateFloor_nonneg (reserveFloor classFloor : ℕ) {n : ℕ} (hn : 2 ≤ n) :
    0 ≤ rateFloor reserveFloor classFloor n := by
  unfold rateFloor
  apply div_nonneg (Nat.cast_nonneg _)
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
  nlinarith

/-- The rate floor is `≤ 1` exactly when the product of the entry floors does not exceed the pair
budget `n(n−1)` — the honest consistency condition on the carried floors (`reserveFloor` and
`classFloor` are disjoint subpopulation counts, so their product is at most the number of ordered
pairs).  This is a pure `Nat` arithmetic fact, carried as `hbudget`. -/
theorem rateFloor_le_one (reserveFloor classFloor : ℕ) {n : ℕ} (hn : 2 ≤ n)
    (hbudget : reserveFloor * classFloor ≤ n * (n - 1)) :
    rateFloor reserveFloor classFloor n ≤ 1 := by
  unfold rateFloor
  have hden_pos : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := by
    have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
    have h2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    nlinarith
  rw [div_le_one hden_pos]
  have hnum : ((reserveFloor * classFloor : ℕ) : ℝ) ≤ ((n * (n - 1) : ℕ) : ℝ) := by
    exact_mod_cast hbudget
  refine le_trans hnum (le_of_eq ?_)
  rw [Nat.cast_mul, Nat.cast_sub (by omega)]; push_cast; ring

/-- **ATOM 1 — `hrfloor` PRODUCED.**  From the two carried entry floors (transported to every
phase-5 step by the FROZEN static profile), the constant rate `r = rateFloor reserveFloor classFloor n`
is a per-step rise-probability floor in exactly the shape `SampledClassTail` consumes:
`∀ c ∈ Phase5AllWin n, ofReal r ≤ stepDist c {sampledReserveClassU i rises by 1}`.

The derivation: `sampledReserveClassU_rise_prob_rect5` lands the genuine cross-rectangle floor
`ofReal((#unsampledReserves · #classMains_σi)/(n(n−1)))`; the carried floors
`reserveFloor ≤ #unsampledReserves` and `classFloor ≤ #classMains_σi` raise the numerator by
`Nat`-product monotonicity, so the constant `r` lower-bounds the genuine floor. -/
theorem hrfloor_of_floors (σ : Sign) (i : Fin (L + 1)) (hiL : i.val < L)
    (n : ℕ) (hn : 2 ≤ n) (reserveFloor classFloor : ℕ)
    (hres : ∀ c, Phase5AllWin (L := L) (K := K) n c →
      reserveFloor ≤ (unsampledReserves (L := L) (K := K)).sum c.count)
    (hcls : ∀ c, Phase5AllWin (L := L) (K := K) n c →
      classFloor ≤ (classMainStates (L := L) (K := K) σ i).sum c.count) :
    ∀ c, Phase5AllWin (L := L) (K := K) n c →
      ENNReal.ofReal (rateFloor reserveFloor classFloor n) ≤
        ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
          {c' | sampledReserveClassU (L := L) (K := K) i c + 1
            ≤ sampledReserveClassU (L := L) (K := K) i c'} := by
  intro c hc
  refine le_trans ?_ (sampledReserveClassU_rise_prob_rect5 (L := L) (K := K) σ i hiL n hn c hc)
  -- raise the rate floor's numerator to the genuine rectangle's numerator.
  apply ENNReal.ofReal_le_ofReal
  unfold rateFloor
  have hden_pos : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := by
    have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
    have h2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    nlinarith
  -- numerator monotonicity: reserveFloor·classFloor ≤ (#unsamp)·(#class) in ℕ, cast up.
  have hnum : ((reserveFloor * classFloor : ℕ) : ℝ) ≤
      (((unsampledReserves (L := L) (K := K)).sum c.count *
        (classMainStates (L := L) (K := K) σ i).sum c.count : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_le_mul (hres c hc) (hcls c hc)
  gcongr

/-! ## ATOM 2 — the clock-separation escape, the named per-`τ` prefix bound.

The seam no-overshoot tail does NOT apply to the `p = 4 → 5` window (see the module doc: phase-5
entry does not reset clocks to full counter, so `SeamEntryFullCounter 4` is false and the
`e^{−40(L+1)}` budget is unavailable through `ClockZeroTail`).  ATOM 2 therefore stays the named
per-`τ` prefix bound that `SampledClassTail.hConcDemand_of_real_window` consumes as `hβ`. -/

/-- **ATOM 2 — the named clock-separation escape bound.**  The exact per-`τ` prefix-mass uniform
bound `SampledClassTail.hConcDemand_of_real_window`'s `hβ` field demands: for every phase-5-window
start `c₀` and every prefix length `τ < t`, the mass of configs whose deficit potential has crossed
the threshold `θ = exp(−s·K₀)` is `≤ β`.  Leaving `Phase5AllWin` is the clock-timing event, NOT a
`sampledReserveClassU`-threshold event, so this bound is the genuine Phase-5/Phase-6 SEPARATION
residual — carried as a named hypothesis, not manufactured. -/
def clockSeparationEscape (n : ℕ) (s : ℝ) (i : Fin (L + 1)) (K₀ t : ℕ) (β : ℝ≥0∞) : Prop :=
  ∀ c₀, Phase5AllWin (L := L) (K := K) n c₀ → ∀ τ ∈ Finset.range t,
    ((NonuniformMajority L K).transitionKernel ^ τ) c₀
      {c | ENNReal.ofReal (Real.exp (-(s * (K₀ : ℝ))))
        ≤ sampledClassPot (L := L) (K := K) i s c} ≤ β

/-! ## Assembly — slot 5 hypothesis-free except the entry floors + named escape. -/

/-- **`hConcDemand_of_atoms`** — the slot-5 `hConcDemand` produced from ATOM 1 (the entry floors)
and ATOM 2 (the named escape).  Feeds the produced `hrfloor` (`hrfloor_of_floors`) and the named
`clockSeparationEscape` bound into `SampledClassTail.hConcDemand_of_real_window`.  The surviving
carried inputs are exactly: the two entry floors `hres`/`hcls` (ATOM 1), the clock-separation exit
bridge `hbridge` and per-`τ` escape `hesc` (ATOM 2), and the arithmetic fit `hε`. -/
theorem hConcDemand_of_atoms (σ : Sign) (i : Fin (L + 1)) (hiL : i.val < L)
    (n : ℕ) (hn : 2 ≤ n) (s : ℝ) (hs : 0 ≤ s) (reserveFloor classFloor : ℕ)
    (hbudget : reserveFloor * classFloor ≤ n * (n - 1))
    (hres : ∀ c, Phase5AllWin (L := L) (K := K) n c →
      reserveFloor ≤ (unsampledReserves (L := L) (K := K)).sum c.count)
    (hcls : ∀ c, Phase5AllWin (L := L) (K := K) n c →
      classFloor ≤ (classMainStates (L := L) (K := K) σ i).sum c.count)
    (K₀ M₀ t : ℕ) (εConc : ℝ≥0)
    (hbridge : ∀ c, Phase5AllWin (L := L) (K := K) n c →
      sampledClassPot (L := L) (K := K) i s c
          < ENNReal.ofReal (Real.exp (-(s * (K₀ : ℝ)))) →
      (NonuniformMajority L K).transitionKernel c
        (sampledClassGate (L := L) (K := K) n)ᶜ = 0)
    (β : ℝ≥0∞)
    (hesc : clockSeparationEscape (L := L) (K := K) n s i K₀ t β)
    (hε : ∀ c₀, Phase5AllWin (L := L) (K := K) n c₀ →
      (ENNReal.ofReal (1 - rateFloor reserveFloor classFloor n * (1 - Real.exp (-s))) ^ t
            * sampledClassPot (L := L) (K := K) i s c₀ + 0)
          / ENNReal.ofReal (Real.exp (-(s * (K₀ : ℝ))))
        + (t : ℝ≥0∞) * β ≤ (εConc : ℝ≥0∞)) :
    ∀ c₀, EndpointWiring.hConcDemand (L := L) (K := K) n i K₀ M₀ t εConc c₀ := by
  have hr0 : 0 ≤ rateFloor reserveFloor classFloor n := rateFloor_nonneg reserveFloor classFloor hn
  have hr1 : rateFloor reserveFloor classFloor n ≤ 1 :=
    rateFloor_le_one reserveFloor classFloor hn hbudget
  have hrfloor := hrfloor_of_floors (L := L) (K := K) σ i hiL n hn reserveFloor classFloor hres hcls
  exact hConcDemand_of_real_window (L := L) (K := K) σ i hiL n hn s hs
    (rateFloor reserveFloor classFloor n) hr0 hr1 hrfloor K₀ M₀ t εConc hbridge β hesc hε

/-- **`phase5Convergence_of_atoms`** — the slot-5 `PhaseConvergenceW`, assembled from the atoms.
Composes `hConcDemand_of_atoms` (ATOM 1 produced + ATOM 2 named) with
`EndpointWiring.phase5Convergence_of_hConc`.  Slot 5 is now hypothesis-free except the entry floors
(ATOM 1's named inputs), the clock-separation bridge/escape (ATOM 2's named remainder), the carried
window closure `hClosed` / drain `hstep`, and the arithmetic fits. -/
noncomputable def phase5Convergence_of_atoms (σ : Sign) (i : Fin (L + 1)) (hiL : i.val < L)
    (n : ℕ) (hn : 2 ≤ n) (s : ℝ) (hs : 0 ≤ s) (reserveFloor classFloor : ℕ)
    (hbudget : reserveFloor * classFloor ≤ n * (n - 1))
    (hres : ∀ c, Phase5AllWin (L := L) (K := K) n c →
      reserveFloor ≤ (unsampledReserves (L := L) (K := K)).sum c.count)
    (hcls : ∀ c, Phase5AllWin (L := L) (K := K) n c →
      classFloor ≤ (classMainStates (L := L) (K := K) σ i).sum c.count)
    (K₀ : ℕ)
    (hClosed : OneSidedCancel.InvClosed (NonuniformMajority L K).transitionKernel
      (fun c => ReserveSampling.Phase5AllWin (L := L) (K := K) n c))
    (q : ℝ≥0∞)
    (hstep : ∀ b : Config (AgentState L K), ReserveSampling.Phase5AllWin (L := L) (K := K) n b →
      1 ≤ ReserveSampling.unsampledReserveU (L := L) (K := K) b →
      (NonuniformMajority L K).transitionKernel b
        (OneSidedCancel.potDone
          (fun c => ReserveSampling.unsampledReserveU (L := L) (K := K) c))ᶜ ≤ q)
    (M₀ t : ℕ) (ε : ℝ≥0) (hε' : (q ^ t : ℝ≥0∞) ≤ (ε : ℝ≥0∞))
    (εConc : ℝ≥0)
    (hbridge : ∀ c, Phase5AllWin (L := L) (K := K) n c →
      sampledClassPot (L := L) (K := K) i s c
          < ENNReal.ofReal (Real.exp (-(s * (K₀ : ℝ)))) →
      (NonuniformMajority L K).transitionKernel c
        (sampledClassGate (L := L) (K := K) n)ᶜ = 0)
    (β : ℝ≥0∞)
    (hesc : clockSeparationEscape (L := L) (K := K) n s i K₀ t β)
    (hεC : ∀ c₀, Phase5AllWin (L := L) (K := K) n c₀ →
      (ENNReal.ofReal (1 - rateFloor reserveFloor classFloor n * (1 - Real.exp (-s))) ^ t
            * sampledClassPot (L := L) (K := K) i s c₀ + 0)
          / ENNReal.ofReal (Real.exp (-(s * (K₀ : ℝ))))
        + (t : ℝ≥0∞) * β ≤ (εConc : ℝ≥0∞)) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  EndpointWiring.phase5Convergence_of_hConc (L := L) (K := K) n i K₀ hClosed q hstep M₀ t ε hε' εConc
    (hConcDemand_of_atoms (L := L) (K := K) σ i hiL n hn s hs reserveFloor classFloor hbudget
      hres hcls K₀ M₀ t εConc hbridge β hesc hεC)

end SamplingAtoms

end ExactMajority
