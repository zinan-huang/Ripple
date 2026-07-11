/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Phase E4 — the timed per-rung phase-advance expected-time bounds (`TimedChainRungs`)

`StableBridges.lean` closed the two Phase-10 stability bridges and RE-SHAPED the timed
regimes' spine: the honest rung target for a timed phase `p` is *next-phase entry*
`timed_phase_chain_target = {AllClockGEpCard (p+1) n}`, NOT `StableDone` (a drained
clock at counter `0` ADVANCES, it does not stabilize).  What it left as the named
Stage-4 timed residual is the per-rung TRANSITION: from the drained state
(`clockCounterSumAt p = 0` hit — every phase-`p` clock at counter `0`), the chain ENTERS
the next regime `AllClockGEpCard (p+1) n`.  **This file supplies the expected-time bound
for that transition.**

## The honest mechanism (the survey)

The counter-drain rung (`ConditionalPhaseProgress.timed_phase_progress_real_tinyClock`)
delivers `E[T to clockCounterSumAt p = 0]` — the INPUT here.  Once drained, the
faithful protocol's universal phase epidemic spreads phase `p+1`: a phase-`p` clock at
counter `0` meeting a phase-`(p+1)` clock advances (the FROZEN `advancePhaseWithInit`
seam), so the advanced count `geCount (p+1)` climbs one by one.  This is EXACTLY the
seam epidemic object: `SeamEpidemics.ge_advance_prob` is the landed per-step advance
probability

  `geCount (p+1) · (n − geCount (p+1)) / (n(n−1)) ≤ K c {geCount (p+1) advances}`.

## Seam EXPECTED-time vs whp

`SeamEpidemics.seamEpidemicW` is the **whp** form (`(K^t) c {¬ allPhaseGe (p+1)} ≤ ε`)
— a `PhaseConvergenceW` carrying the drift hypothesis.  The EXPECTED-time version did
NOT exist; we build it here, exactly as the timed counter-drain engine builds its
expected version, by feeding `ge_advance_prob` into E1's coupon / harmonic
`expectedHitting` machinery (`ConditionalPhaseProgress.Engine.coupon_expectedHitting_le_uniform_on`).

The construction is the standard epidemic `E[T] = O(n log n)` harmonic sum (here in its
crude `O(n²)` uniform form; the `log` is the orthogonal harmonic sharpening — the same
relationship as `coupon_expectedHitting_le_uniform` to the harmonic `H_n`):

* **potential** `Φ c := n − geCount (p+1) c` (the UNADVANCED count);
* **invariant** `AllClockGEpCard p n` (all-clock at phase `≥ p`, fixed card; `InvClosed`
  for `3 ≤ p`, and `⟹ allPhaseGe p n` so `ge_advance_prob` applies);
* **`PotNonincrOn`** — `geCount (p+1)` only rises (`SeamEpidemics.geCount_ge_monotone`),
  so `Φ` only drops;
* **per-level drop** at `Φ b = m` (i.e. `geCount (p+1) b = n − m`, `m` unadvanced): the
  advance rate is `(n−m)·m / (n(n−1))` via `ge_advance_prob`, and the kernel mass on the
  NOT-dropped set is `≤ 1 − (n−m)·m/(n(n−1))`;
* **uniform per-level ceiling** `r = n`: `advance_floor_seam` gives `m·(n−m) ≥ n−1` for
  `1 ≤ m ≤ n−1`, so the waiting time `n(n−1)/((n−m)m) ≤ n(n−1)/(n−1) = n`;
* **result** `E[T] ≤ M · r = n · n = n²` interactions (the epidemic-completion bound).

The drained target `potBelow Φ 1 = {Φ = 0} = {geCount (p+1) ≥ n}` is exactly
`AllClockGEpCard (p+1) n` = `StableBridges.timed_phase_chain_target` on the all-clock
invariant (`seam_potBelow_one_eq_chain_target`).  **This closes the timed per-rung
transition** modulo the entry hypothesis that the rung START is drained-and-in-regime
(the counter-drain rung's OUTPUT, supplied upstream by
`timed_phase_progress_real_tinyClock`).

## Build

Single-file only:
  `lake env lean Ripple/PopulationProtocol/Majority/ExactMajority/Probability/TimedChainRungs.lean`
from the project root (deps as cached oleans).  NEVER local `lake build`.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.RegimeClassification
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.SeamEpidemics
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.StableBridges

namespace ExactMajority
namespace TimedChainRungs

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators NNReal
open ConditionalPhaseProgress SeamEpidemics

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

/-! ## Part 1 — the seam potential and its descent invariants -/

/-- **The unadvanced-clock potential.**  On the all-clock phase-`p` regime, this counts
the agents NOT yet advanced to phase `≥ p+1` — the seam epidemic's deficit. -/
def seamPot (p n : ℕ) (c : Config (AgentState L K)) : ℕ :=
  n - geCount (L := L) (K := K) (p + 1) c

/-- `AllClockGEpCard p n` (all-clock at phase `≥ p`, card `n`) IMPLIES the seam window
`allPhaseGe p n` (card `n`, every agent at phase `≥ p`) — the bridge that lets
`ge_advance_prob` (stated over `allPhaseGe`) fire on the timed-regime invariant. -/
theorem allPhaseGe_of_allClockGEpCard {p n : ℕ} {c : Config (AgentState L K)}
    (h : AllClockGEpCard (L := L) (K := K) p n c) :
    allPhaseGe (L := L) (K := K) p n c :=
  ⟨h.2, fun a ha => (h.1 a ha).2⟩

/-- On a card-`n` config, the advanced count `geCount (p+1)` never exceeds `n`. -/
theorem geCount_le_card {q n : ℕ} {c : Config (AgentState L K)} (hcard : c.card = n) :
    geCount (L := L) (K := K) q c ≤ n := by
  unfold geCount
  rw [← hcard]
  exact Multiset.countP_le_card _ _

/-! ## Part 2 — `PotNonincrOn (AllClockGEpCard p n) K (seamPot p n)`

`geCount (p+1)` is preserved-or-raised on the one-step kernel support
(`SeamEpidemics.geCount_ge_monotone`); `seamPot = n − geCount (p+1)` therefore never
strictly rises.  We package this as the invariant-relative `PotNonincrOn` over the
all-clock invariant (the invariant is used only to keep `geCount ≤ n`, so the subtraction
is faithful — though monotonicity needs no invariant at all). -/

/-- **`seamPot` is non-increasing on the all-clock regime.**  One step never strictly
raises `seamPot p n` from an `AllClockGEpCard p n`-state.  Direct from
`geCount_ge_monotone` (advanced count only climbs) ⟹ `n − geCount` only drops; the
strictly-higher-`seamPot` set carries `0` kernel mass. -/
theorem seamPot_PotNonincrOn (p n : ℕ) :
    Engine.PotNonincrOn (AllClockGEpCard (L := L) (K := K) p n)
      (NonuniformMajority L K).transitionKernel (seamPot (L := L) (K := K) p n) := by
  classical
  intro b hb
  show (NonuniformMajority L K).transitionKernel b
      {x | seamPot (L := L) (K := K) p n b < seamPot (L := L) (K := K) p n x} = 0
  change ((NonuniformMajority L K).stepDistOrSelf b).toMeasure
      {x | seamPot (L := L) (K := K) p n b < seamPot (L := L) (K := K) p n x} = 0
  rw [PMF.toMeasure_apply_eq_zero_iff _ (DiscreteMeasurableSpace.forall_measurableSet _)]
  rw [Set.disjoint_left]
  intro c' hsupp hbad
  -- hbad : seamPot b < seamPot c', i.e. n - geCount(p+1) b < n - geCount(p+1) c'.
  simp only [Set.mem_setOf_eq, seamPot] at hbad
  -- geCount(p+1) is preserved-or-raised on the support, so n - geCount only drops.
  have hge : geCount (L := L) (K := K) (p + 1) b
      ≤ geCount (L := L) (K := K) (p + 1) c' :=
    geCount_ge_monotone (L := L) (K := K) (p + 1) (geCount (L := L) (K := K) (p + 1) b)
      b c' (le_refl _) hsupp
  omega

/-! ## Part 3 — the per-level advance drop (`ge_advance_prob` ⟹ engine `hdrop`)

The coupon engine needs, at every level-`m` state, the NOT-dropped mass
`K b (potBelow seamPot m)ᶜ ≤ q m`.  `potBelow seamPot m = {seamPot < m}` = the dropped
set, so its complement is the not-yet-dropped event.  At `seamPot b = m` (i.e.
`geCount (p+1) b = n − m`) the advance event `{geCount (p+1) b + 1 ≤ geCount (p+1) c'}`
forces `seamPot c' < m`, hence sits inside `potBelow seamPot m`; `ge_advance_prob` lower
bounds its mass by `(n−m)·m / (n(n−1))`, so the complement is `≤ 1 − (n−m)·m/(n(n−1))`. -/

/-- The advance event sits inside the seam-potential drop set: if the advanced count
rises by `≥ 1` from a level-`m` state with `1 ≤ m`, the unadvanced count `seamPot`
strictly drops below `m`.  (At `m = 0` the start is already finished and no advance can
fire; the engine `hdrop` handles `m = 0` by the trivial `≤ 1` ceiling instead.) -/
theorem advance_subset_potBelow (p n : ℕ) (b : Config (AgentState L K))
    (hcard : b.card = n) (m : ℕ) (hm1 : 1 ≤ m)
    (hm : seamPot (L := L) (K := K) p n b = m) :
    {c' | geCount (L := L) (K := K) (p + 1) b + 1 ≤ geCount (L := L) (K := K) (p + 1) c'}
      ⊆ Engine.potBelow (seamPot (L := L) (K := K) p n) m := by
  intro c' hc'
  simp only [Set.mem_setOf_eq] at hc'
  show seamPot (L := L) (K := K) p n c' < m
  -- seamPot c' = n - geCount c'.  At 1 ≤ m: geCount b = n - m ≤ n-1 < n, so geCount b + 1 ≤ n.
  -- If geCount c' ≤ n: n - geCount c' ≤ n - (geCount b + 1) = m - 1 < m.
  -- If geCount c' > n: n - geCount c' = 0 < m.
  have hle : geCount (L := L) (K := K) (p + 1) b ≤ n := geCount_le_card (L := L) (K := K) hcard
  have hb : seamPot (L := L) (K := K) p n b = n - geCount (L := L) (K := K) (p + 1) b := rfl
  rw [hb] at hm
  show n - geCount (L := L) (K := K) (p + 1) c' < m
  omega

/-- **The engine `hdrop` from `ge_advance_prob`.**  On the all-clock regime, at every
level-`m` state, the NOT-dropped kernel mass is `≤ 1 − (n−m)·m / (n(n−1))`.  This is the
seam-epidemic clone of `ConditionalPhaseProgress.clockCounterSumAt_hdrop_of_floor`, with
the advance rate supplied by `SeamEpidemics.ge_advance_prob` instead of the clock-clock
rectangle. -/
theorem seam_hdrop (p n : ℕ) (hn : 2 ≤ n) :
    ∀ m : ℕ, ∀ b : Config (AgentState L K),
      AllClockGEpCard (L := L) (K := K) p n b →
      seamPot (L := L) (K := K) p n b = m →
      (NonuniformMajority L K).transitionKernel b
          (Engine.potBelow (seamPot (L := L) (K := K) p n) m)ᶜ
        ≤ 1 - ENNReal.ofReal
            ((((n - geCount (L := L) (K := K) (p + 1) b)
                * geCount (L := L) (K := K) (p + 1) b : ℕ)) / ((n : ℝ) * ((n : ℝ) - 1))) := by
  classical
  intro m b hb hbm
  have hcard : b.card = n := hb.2
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · -- m = 0: seamPot b = 0, i.e. geCount(p+1) b ≥ n, so (n - geCount) = 0, RHS = 1 - 0 = 1.
    subst hm0
    have hge : seamPot (L := L) (K := K) p n b = n - geCount (L := L) (K := K) (p + 1) b := rfl
    rw [hge] at hbm
    have hnum0 : (n - geCount (L := L) (K := K) (p + 1) b) = 0 := hbm
    rw [hnum0]
    simp only [Nat.zero_mul, Nat.cast_zero, zero_div, ENNReal.ofReal_zero, tsub_zero]
    exact MeasureTheory.prob_le_one
  · -- m ≥ 1: route through ge_advance_prob.
    have hwin : allPhaseGe (L := L) (K := K) p n b := allPhaseGe_of_allClockGEpCard (L := L) (K := K) hb
    -- ge_advance_prob: rate ≤ mass on advance event.
    have hadv := ge_advance_prob (L := L) (K := K) p n hn b hwin
    -- rewrite the rate's numerator into (n - geCount)·geCount (commute the product).
    have hcomm : (geCount (L := L) (K := K) (p + 1) b
          * (n - geCount (L := L) (K := K) (p + 1) b) : ℕ)
        = ((n - geCount (L := L) (K := K) (p + 1) b)
            * geCount (L := L) (K := K) (p + 1) b : ℕ) := by ring
    rw [hcomm] at hadv
    -- advance event ⊆ potBelow seamPot m, so its mass ≤ potBelow mass.
    have hsub := advance_subset_potBelow (L := L) (K := K) p n b hcard m hmpos hbm
    have hmono : ((NonuniformMajority L K).stepDistOrSelf b).toMeasure
          {c' | geCount (L := L) (K := K) (p + 1) b + 1 ≤ geCount (L := L) (K := K) (p + 1) c'}
        ≤ ((NonuniformMajority L K).stepDistOrSelf b).toMeasure
            (Engine.potBelow (seamPot (L := L) (K := K) p n) m) :=
      measure_mono hsub
    -- combine: rate ≤ mass on potBelow.
    have hrate_le : ENNReal.ofReal
          ((((n - geCount (L := L) (K := K) (p + 1) b)
              * geCount (L := L) (K := K) (p + 1) b : ℕ)) / ((n : ℝ) * ((n : ℝ) - 1)))
        ≤ (NonuniformMajority L K).transitionKernel b
            (Engine.potBelow (seamPot (L := L) (K := K) p n) m) := by
      refine le_trans hadv ?_
      change ((NonuniformMajority L K).stepDistOrSelf b).toMeasure _ ≤ _
      exact hmono
    -- complement = 1 - mass; mass ≥ rate ⟹ complement ≤ 1 - rate.
    have hmeas : MeasurableSet (Engine.potBelow (seamPot (L := L) (K := K) p n) m) :=
      Engine.potBelow_measurable _ _
    rw [MeasureTheory.prob_compl_eq_one_sub hmeas]
    exact tsub_le_tsub_left hrate_le 1

/-! ## Part 4 — the per-level uniform ceiling (`r = n`)

`advance_floor_seam` (`m·(n−m) ≥ n−1` for `1 ≤ m ≤ n−1`) bounds every active-level
waiting time `(1 − q m)⁻¹ = n(n−1)/((n−m)m) ≤ n(n−1)/(n−1) = n`.  We supply the engine's
per-level drop family `q m := 1 − (n−m)·m/(n(n−1))` and the ceiling `r = n`. -/

/-- The per-level drop family for the seam epidemic: `q m = 1 − (n−m)·m / (n(n−1))`. -/
noncomputable def seamQ (n : ℕ) (m : ℕ) : ℝ≥0∞ :=
  1 - ENNReal.ofReal (((n - m) * m : ℕ) / ((n : ℝ) * ((n : ℝ) - 1)))

/-- The seam advance rate is `≤ 1` (a probability), so `1 − rate` is a genuine failure
mass and `(1 − (1 − rate))⁻¹ = rate⁻¹`. -/
theorem seam_rate_le_one (n m : ℕ) (hn : 2 ≤ n) (hm : m ≤ n) :
    ENNReal.ofReal (((n - m) * m : ℕ) / ((n : ℝ) * ((n : ℝ) - 1))) ≤ 1 := by
  rw [← ENNReal.ofReal_one]
  apply ENNReal.ofReal_le_ofReal
  rw [div_le_one]
  · -- (n-m)·m ≤ n·(n-1) for m ≤ n.
    have h1 : ((n - m) * m : ℕ) ≤ (n * (n - 1) : ℕ) := by
      rcases Nat.eq_zero_or_pos m with hm0 | hmpos
      · subst hm0; simp
      · have hnm : (n - m) ≤ n - 1 := by omega
        calc ((n - m) * m : ℕ) ≤ (n - 1) * n := Nat.mul_le_mul hnm hm
          _ = n * (n - 1) := by ring
    have hcast : (((n - m) * m : ℕ) : ℝ) = ((n - m : ℕ) : ℝ) * (m : ℝ) := by push_cast; ring
    have hn1 : ((n : ℝ) - 1) = ((n - 1 : ℕ) : ℝ) := by
      have h1' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.one_le_of_lt hn
      push_cast [Nat.cast_sub (Nat.one_le_of_lt hn)]; ring
    rw [hcast, hn1]
    calc ((n - m : ℕ) : ℝ) * (m : ℝ)
        = (((n - m) * m : ℕ) : ℝ) := by push_cast; ring
      _ ≤ ((n * (n - 1) : ℕ) : ℝ) := by exact_mod_cast h1
      _ = (n : ℝ) * ((n - 1 : ℕ) : ℝ) := by push_cast; ring
  · have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hpos : (0 : ℝ) < (n : ℝ) - 1 := by linarith
    have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
    positivity

/-- The active-level seam advance rate is `≥ 1/n`.  `advance_floor_seam` gives
`(n−m)·m ≥ n−1`, so `rate = (n−m)·m/(n(n−1)) ≥ (n−1)/(n(n−1)) = 1/n`. -/
theorem seam_rate_ge_inv_n (n m : ℕ) (hn : 2 ≤ n) (hm1 : 1 ≤ m) (hmn : m ≤ n - 1) :
    (1 : ℝ) / n ≤ (((n - m) * m : ℕ) : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)) := by
  have hmlt : m < n := by omega
  -- (n−m)·m ≥ n−1.
  have hfloor : (n - 1) ≤ (n - m) * m := by
    have h := advance_floor_seam n m hm1 hmlt
    -- advance_floor_seam: n - 1 ≤ m * (n - m); commute.
    calc (n - 1) ≤ m * (n - m) := h
      _ = (n - m) * m := by ring
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hn1pos : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hden_pos : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := mul_pos hnpos hn1pos
  have hn1eq : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    push_cast [Nat.cast_sub (Nat.one_le_of_lt hn)]; ring
  have hfloorR : ((n - 1 : ℕ) : ℝ) ≤ (((n - m) * m : ℕ) : ℝ) := by exact_mod_cast hfloor
  rw [hn1eq] at hfloorR
  rw [div_le_div_iff₀ hnpos hden_pos]
  nlinarith [hfloorR, hnpos, hn1pos]

/-- **The per-level waiting-time ceiling.**  Each active level (`1 ≤ m ≤ n−1`) has
`(1 − seamQ n m)⁻¹ = rate⁻¹ = n(n−1)/((n−m)m) ≤ n` via `advance_floor_seam`. -/
theorem seamQ_inv_le (n : ℕ) (hn : 2 ≤ n) :
    ∀ m : ℕ, 1 ≤ m → m ≤ n - 1 → (1 - seamQ n m)⁻¹ ≤ (n : ℝ≥0∞) := by
  intro m hm1 hmn
  have hmlt : m < n := by omega
  unfold seamQ
  -- 1 - (1 - rate) = rate (rate ≤ 1).
  have hrle : ENNReal.ofReal (((n - m) * m : ℕ) / ((n : ℝ) * ((n : ℝ) - 1))) ≤ 1 :=
    seam_rate_le_one n m hn (by omega)
  rw [ENNReal.sub_sub_cancel (by norm_num) hrle]
  -- rate⁻¹ ≤ n via ofReal(1/n) ≤ ofReal(rate), then antitone inverse.
  set x : ℝ := (((n - m) * m : ℕ) : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)) with hxdef
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hge : (1 : ℝ) / n ≤ x := seam_rate_ge_inv_n n m hn hm1 hmn
  have h1 : ENNReal.ofReal (1 / n) ≤ ENNReal.ofReal x := ENNReal.ofReal_le_ofReal hge
  have h2 : (ENNReal.ofReal x)⁻¹ ≤ (ENNReal.ofReal (1 / n))⁻¹ := ENNReal.inv_le_inv.mpr h1
  refine le_trans h2 ?_
  rw [one_div, ENNReal.ofReal_inv_of_pos hnpos, inv_inv, ENNReal.ofReal_natCast]

/-! ## Part 5 — the assembled per-rung expected-time bound

All engine ingredients are discharged:
* `InvClosed`  — `AllClockGEpCard_InvClosed` (needs `3 ≤ p`);
* `PotNonincrOn` — `seamPot_PotNonincrOn`;
* `hdrop` — `seam_hdrop` (rate `(n−m)·m/(n(n−1))` from `ge_advance_prob`);
* `r = n` ceiling — `seamQ_inv_le` (`advance_floor_seam`);
* start level `seamPot c ≤ n` — `geCount ≥ 0`, `n − geCount ≤ n`.

Plugging into `Engine.coupon_expectedHitting_le_uniform_on` with `M = n` gives
`E[T] ≤ n · n = n²`. -/

/-- The drained seam target `potBelow seamPot 1 = {seamPot = 0} = {geCount (p+1) ≥ n}`
coincides on the card-`n` invariant with `allPhaseGe (p+1) n` (every agent at phase
`≥ p+1`).  This is `seamPot_drained_iff` ⟹ the bridge to the chain target. -/
theorem seamPot_lt_one_iff_geFinished (p n : ℕ) (c : Config (AgentState L K))
    (hcard : c.card = n) :
    seamPot (L := L) (K := K) p n c < 1 ↔ geFinished (L := L) (K := K) p n c := by
  unfold seamPot geFinished
  have hle : geCount (L := L) (K := K) (p + 1) c ≤ n := geCount_le_card (L := L) (K := K) hcard
  omega

/-- **The per-rung seam epidemic expected-time bound (`O(n²)`).**

From any `AllClockGEpCard p n`-start `c` (timed phase `≥ p`, `3 ≤ p`, `n ≥ 2`) WITH the
advance trigger already fired (`1 ≤ geCount (p+1) c` — at least one agent has crossed to
phase `≥ p+1`, the counter-drain rung's deterministic seam advance), the expected number
of interactions for the phase epidemic to advance EVERY agent to phase `≥ p+1` — i.e. to
hit `potBelow (seamPot p n) 1 = {geCount (p+1) ≥ n}` — is at most `n²`.

The trigger hypothesis `htrig` is essential and honest: at the all-unadvanced level
`m = n` (no agent has crossed) the advance rate `(n−m)·m = 0` is `0` and the epidemic is
genuinely stuck (an epidemic needs a seed).  The counter-drain rung delivers the seed: a
phase-`p` clock at counter `0` runs `advancePhaseWithInit` to phase `p+1`, so the drained
output always has `geCount (p+1) ≥ 1`.  The engine therefore runs from level
`M = n − 1` (one seed already advanced), and the uniform ceiling `r = n` gives
`E[T] ≤ (n−1)·n ≤ n²`.

This is the per-rung TRANSITION cap left as the Stage-4 timed residual by
`StableBridges.lean`: it is the seam-epidemic clone of the counter-drain rung
`ConditionalPhaseProgress.timed_phase_progress_real_tinyClock`, with the advance rate
supplied by `SeamEpidemics.ge_advance_prob`.  All engine ingredients are discharged
(`AllClockGEpCard_InvClosed`, `seamPot_PotNonincrOn`, `seam_hdrop`, `seamQ_inv_le`); the
ONLY inputs are the rung-start regime membership `hInvc` and the seed `htrig` (both the
upstream counter-drain output). -/
theorem seam_rung_expectedHitting_le_nsq (p n : ℕ) (hp3 : 3 ≤ p) (hn : 2 ≤ n)
    (c : Config (AgentState L K)) (hInvc : AllClockGEpCard (L := L) (K := K) p n c)
    (htrig : 1 ≤ geCount (L := L) (K := K) (p + 1) c) :
    expectedHitting (NonuniformMajority L K).transitionKernel c
        (Engine.potBelow (seamPot (L := L) (K := K) p n) 1)
      ≤ ((n * n : ℕ) : ℝ≥0∞) := by
  classical
  have hcard : c.card = n := hInvc.2
  -- start level: seamPot c ≤ n - 1 (seed already advanced).
  have hstart : seamPot (L := L) (K := K) p n c ≤ n - 1 := by
    unfold seamPot; omega
  -- the engine produces M · r = (n-1) · n; bound by n · n.
  have hkey :
      expectedHitting (NonuniformMajority L K).transitionKernel c
          (Engine.potBelow (seamPot (L := L) (K := K) p n) 1)
        ≤ ((n - 1 : ℕ) : ℝ≥0∞) * (n : ℝ≥0∞) :=
    Engine.coupon_expectedHitting_le_uniform_on
      (NonuniformMajority L K).transitionKernel
      (AllClockGEpCard (L := L) (K := K) p n)
      (AllClockGEpCard_InvClosed (L := L) (K := K) p n hp3)
      (seamPot (L := L) (K := K) p n)
      (seamPot_PotNonincrOn (L := L) (K := K) p n)
      (seamQ n)
      (by
        -- hdrop with q = seamQ n; seam_hdrop's RHS is definitionally seamQ n m.
        intro m b hb hbm
        have h := seam_hdrop (L := L) (K := K) p n hn m b hb hbm
        -- seamQ n m = 1 - ofReal((n-m)*m/(n(n-1))); rewrite (n-m), m via hbm.
        have hbcard : b.card = n := hb.2
        have hbm' : seamPot (L := L) (K := K) p n b = n - geCount (L := L) (K := K) (p + 1) b := rfl
        rw [hbm'] at hbm
        -- geCount(p+1) b = n - m.
        have hgle : geCount (L := L) (K := K) (p + 1) b ≤ n :=
          geCount_le_card (L := L) (K := K) hbcard
        unfold seamQ
        -- show seam_hdrop RHS = seamQ RHS by matching (n - geCount) = m and geCount = n - m.
        have heqnum : ((n - geCount (L := L) (K := K) (p + 1) b)
              * geCount (L := L) (K := K) (p + 1) b : ℕ)
            = ((n - m) * m : ℕ) := by
          have h1 : n - geCount (L := L) (K := K) (p + 1) b = m := hbm
          have h2 : geCount (L := L) (K := K) (p + 1) b = n - m := by omega
          rw [h1, h2]; ring
        rw [heqnum] at h
        exact h)
      (n - 1) c hstart hInvc
      (n : ℝ≥0∞)
      (fun m hm1 hmn => seamQ_inv_le n hn m hm1 hmn)
  -- (n-1) * n ≤ n * n = (n*n : ℕ).
  refine le_trans hkey ?_
  calc ((n - 1 : ℕ) : ℝ≥0∞) * (n : ℝ≥0∞)
      ≤ (n : ℝ≥0∞) * (n : ℝ≥0∞) := by
        gcongr
        exact_mod_cast Nat.sub_le n 1
    _ = ((n * n : ℕ) : ℝ≥0∞) := by push_cast; ring

/-! ## Part 6 — the chain-target bridge

`StableBridges.timed_phase_chain_target n p = {AllClockGEpCard (p+1) n}` is the honest
rung-1 target.  On the all-clock invariant, the engine's drain target
`potBelow (seamPot p n) 1 = {geCount (p+1) ≥ n}` coincides with this chain target: a
card-`n` state with `geCount (p+1) ≥ n` has EVERY agent at phase `≥ p+1`, and (carrying
the clock-role witness from the start invariant) is `AllClockGEpCard (p+1) n`.  Since the
invariant is `InvClosed`, this is recovered on the hit. -/

/-- Alias for `StableBridges.timed_phase_chain_target` (`{AllClockGEpCard (p+1) n}`),
usable inside `TimedChainRungs`. -/
def StableBridges_timed_phase_chain_target (n p : ℕ) : Set (Config (AgentState L K)) :=
  timed_phase_chain_target (L := L) (K := K) n p

/-- On the card-`n` all-clock invariant, the seam drain target
`{geCount (p+1) ≥ n}` IMPLIES `allPhaseGe (p+1) n` (every agent at phase `≥ p+1`). -/
theorem drained_imp_allPhaseGe_succ (p n : ℕ) (c : Config (AgentState L K))
    (hcard : c.card = n) (hdrain : seamPot (L := L) (K := K) p n c < 1) :
    allPhaseGe (L := L) (K := K) (p + 1) n c := by
  have hfin : geFinished (L := L) (K := K) p n c :=
    (seamPot_lt_one_iff_geFinished (L := L) (K := K) p n c hcard).1 hdrain
  exact (allPhaseGe_succ_iff_geFinished (L := L) (K := K) p n c hcard).2 hfin

/-- **The seam drain target = the chain target (clock-role refinement).**

On an `AllClockGEpCard p n`-start, the engine drain target `potBelow (seamPot p n) 1`
lands every CLOCK agent at phase `≥ p+1` (it lands ALL agents there).  Combined with the
clock-role membership of `AllClockGEp`, the drained state — reached via the `InvClosed`
trajectory that keeps the clock-role structure — satisfies `AllClockGEp (p+1)`, i.e. the
chain target `StableBridges.timed_phase_chain_target n p`.

We state the pointwise refinement: a drained, card-`n` state whose clock agents are all
at phase `≥ p` (the carried invariant) AND every agent at phase `≥ p+1` (the drain) is
`AllClockGEpCard (p+1) n`. -/
theorem drained_invariant_imp_chain_target (p n : ℕ) (c : Config (AgentState L K))
    (hInv : AllClockGEpCard (L := L) (K := K) p n c)
    (hdrain : seamPot (L := L) (K := K) p n c < 1) :
    c ∈ StableBridges_timed_phase_chain_target (L := L) (K := K) (n := n) (p := p) := by
  have hcard : c.card = n := hInv.2
  have hge := drained_imp_allPhaseGe_succ (L := L) (K := K) p n c hcard hdrain
  -- chain target = {AllClockGEpCard (p+1) n}; build it from hge (all agents ≥ p+1) + card.
  unfold StableBridges_timed_phase_chain_target timed_phase_chain_target
  show AllClockGEpCard (L := L) (K := K) (p + 1) n c
  refine ⟨?_, hcard⟩
  intro a ha
  -- every clock at phase ≥ p (carried) is now at phase ≥ p+1 (drained): need role + phase.
  exact ⟨(hInv.1 a ha).1, hge.2 a ha⟩

/-! ## Part 7 — the per-rung bound to the CHAIN TARGET (the assembled spine link)

`seam_rung_expectedHitting_le_nsq` caps `E[T → potBelow (seamPot p n) 1]`, the BARE
drain set.  The honest spine rung-1 target is the chain set
`StableBridges_timed_phase_chain_target n p = {AllClockGEpCard (p+1) n}` — STRICTLY
smaller off-invariant (it carries the clock-role/card refinement).  We route the bound
through the `InvClosed` invariant exactly as `StableBridges.phase10Majority_link_intersected`:
from an `AllClockGEpCard p n`-start the trajectory stays in the invariant (a.e.), so the
first time it hits the bare drain set it ALSO satisfies the refinement, hence lies in the
chain target.  The hitting time of the chain target therefore equals that of the bare
drain set, capped by `n²`. -/

open scoped Classical in
/-- **The per-rung phase-advance expected-time bound, to the chain target (`O(n²)`).**

From an `AllClockGEpCard p n`-start with the advance seed (`1 ≤ geCount (p+1) c`), the
expected number of interactions to reach `StableBridges_timed_phase_chain_target n p`
(`= {AllClockGEpCard (p+1) n}` — every agent advanced to phase `≥ p+1`, the next timed
regime's entry) is at most `n²`.  This is the assembled spine link: the genuine
`AllClockGEpCard p n → AllClockGEpCard (p+1) n` phase-advance rung the timed ladder
telescope consumes.  Proven by routing `seam_rung_expectedHitting_le_nsq` through the
`AllClockGEpCard_InvClosed` invariant (same technique as the Phase-10 intersected link). -/
theorem seam_rung_to_chain_target_le_nsq (p n : ℕ) (hp3 : 3 ≤ p) (hn : 2 ≤ n)
    (c : Config (AgentState L K)) (hInvc : AllClockGEpCard (L := L) (K := K) p n c)
    (htrig : 1 ≤ geCount (L := L) (K := K) (p + 1) c) :
    expectedHitting (NonuniformMajority L K).transitionKernel c
        (StableBridges_timed_phase_chain_target (L := L) (K := K) (n := n) (p := p))
      ≤ ((n * n : ℕ) : ℝ≥0∞) := by
  classical
  set ker := (NonuniformMajority L K).transitionKernel with hker
  set Inv : Config (AgentState L K) → Prop := AllClockGEpCard (L := L) (K := K) p n with hInvdef
  set Chain : Set (Config (AgentState L K)) :=
    StableBridges_timed_phase_chain_target (L := L) (K := K) (n := n) (p := p) with hChain
  set Bare : Set (Config (AgentState L K)) :=
    Engine.potBelow (seamPot (L := L) (K := K) p n) 1 with hBare
  -- InvClosed for AllClockGEpCard (needs 3 ≤ p).
  have hInvClosed : ∀ b : Config (AgentState L K), Inv b → ker b {x | ¬ Inv x} = 0 :=
    AllClockGEpCard_InvClosed (L := L) (K := K) p n hp3
  -- the (ker^t)-mass on ¬Inv is 0 from an Inv-start.
  have hpowInv : ∀ t : ℕ, (ker ^ t) c {x | ¬ Inv x} = 0 :=
    fun t => pow_compl_inv_eq_zero_eh ker Inv hInvClosed c hInvc t
  -- per time-slice: not-Chain mass ≤ not-Bare mass (off ¬Inv, which is null).
  have hslice : ∀ t : ℕ, (ker ^ t) c (Chainᶜ) ≤ (ker ^ t) c (Bareᶜ) := by
    intro t
    have hsub : (Chainᶜ : Set (Config (AgentState L K)))
        ⊆ Bareᶜ ∪ {x | ¬ Inv x} := by
      intro z hz
      by_cases hzInv : Inv z
      · -- z ∈ Inv but z ∉ Chain ⇒ z ∉ Bare (else drained+invariant ⇒ Chain by refinement).
        left
        intro hzBare
        -- hzBare : seamPot p n z < 1; with Inv z ⇒ z ∈ Chain — contradiction.
        exact hz (drained_invariant_imp_chain_target (L := L) (K := K) p n z hzInv hzBare)
      · right; exact hzInv
    calc (ker ^ t) c (Chainᶜ)
        ≤ (ker ^ t) c (Bareᶜ ∪ {x | ¬ Inv x}) := measure_mono hsub
      _ ≤ (ker ^ t) c (Bareᶜ) + (ker ^ t) c {x | ¬ Inv x} := measure_union_le _ _
      _ = (ker ^ t) c (Bareᶜ) := by rw [hpowInv t, add_zero]
  -- sum over t: E[T → Chain] ≤ E[T → Bare] ≤ n².
  calc expectedHitting ker c Chain
      = ∑' t : ℕ, (ker ^ t) c (Chainᶜ) := expectedHitting_eq_tsum ker c Chain
    _ ≤ ∑' t : ℕ, (ker ^ t) c (Bareᶜ) := ENNReal.tsum_le_tsum hslice
    _ = expectedHitting ker c Bare := (expectedHitting_eq_tsum ker c Bare).symm
    _ ≤ ((n * n : ℕ) : ℝ≥0∞) := seam_rung_expectedHitting_le_nsq (L := L) (K := K) p n hp3 hn c hInvc htrig

/-! ## Part 8 — the assembled two-phase chain link (honest cross-term)

The full timed spine telescopes `AllClockGEpCard p n → AllClockGEpCard (p+1) n → … → 10`.
A SINGLE per-rung link is `seam_rung_to_chain_target_le_nsq` (`≤ n²`).  Chaining two
consecutive rungs `p → p+1 → p+2` uses `Phase10ExpectedTime.expectedHitting_le_through_mid`
with `Done = {AllClockGEpCard (p+2) n}`, `Mid = {AllClockGEpCard (p+1) n}` — the inclusion
`Done ⊆ Mid` holds (phase `≥ p+2 ⟹ ≥ p+1`).  The result is

    E[T from p-regime → (p+2)-regime] ≤ E[T → (p+1)-regime] + (band cross-term),

where the band cross-term `∑' t, (K^t) c (Mid ∩ Doneᶜ)` is the time-integrated occupation
of the "advanced to `p+1` but not yet to `p+2`" band — exactly the `(p+1)`-seam epidemic's
running region.  We deliver the through-mid decomposition with the first summand
DISCHARGED by `seam_rung_to_chain_target_le_nsq`; the band cross-term is the honest
cross-phase residual (its closed bound is the occupation-integral form of the next-rung
seam cap, the same band-bookkeeping `expectedHitting_le_through_mid` always leaves open —
not a `seam`-specific gap). -/

/-- `AllClockGEpCard (p+2) n ⊆ AllClockGEpCard (p+1) n` (phase `≥ p+2 ⟹ ≥ p+1`): the
chain-target inclusion that lets two consecutive rungs telescope through `Mid`. -/
theorem chain_target_succ_subset (p n : ℕ) :
    StableBridges_timed_phase_chain_target (L := L) (K := K) (n := n) (p := p + 1)
      ⊆ StableBridges_timed_phase_chain_target (L := L) (K := K) (n := n) (p := p) := by
  intro z hz
  -- hz : AllClockGEpCard (p+2) n z; goal : AllClockGEpCard (p+1) n z.
  have hz' : AllClockGEpCard (L := L) (K := K) (p + 1 + 1) n z := hz
  refine ⟨?_, hz'.2⟩
  intro a ha
  exact ⟨(hz'.1 a ha).1, by have := (hz'.1 a ha).2; omega⟩

/-- **The assembled two-phase chain link (through-mid decomposition).**

From an `AllClockGEpCard p n`-start with the `(p+1)`-seed, the expected time to reach the
`(p+2)`-regime is bounded by the `(p+1)`-regime hitting time (`≤ n²` via
`seam_rung_to_chain_target_le_nsq`) PLUS the honest band cross-term — the time-integrated
occupation of the `(p+1)`-seam band.  This is the genuine spine telescope step; iterating
it through the timed phases `p ∈ {5,6,7,8}` (the `3 ≤ p` seam rungs) assembles the chain to
the Phase-10 backup, closed by `StableBridges`' Phase-10 stability bridges. -/
theorem chain_two_phase_through_mid (p n : ℕ) (hp3 : 3 ≤ p) (hn : 2 ≤ n)
    (c : Config (AgentState L K)) (hInvc : AllClockGEpCard (L := L) (K := K) p n c)
    (htrig : 1 ≤ geCount (L := L) (K := K) (p + 1) c) :
    expectedHitting (NonuniformMajority L K).transitionKernel c
        (StableBridges_timed_phase_chain_target (L := L) (K := K) (n := n) (p := p + 1))
      ≤ ((n * n : ℕ) : ℝ≥0∞)
        + ∑' t : ℕ, ((NonuniformMajority L K).transitionKernel ^ t) c
            (StableBridges_timed_phase_chain_target (L := L) (K := K) (n := n) (p := p)
              ∩ (StableBridges_timed_phase_chain_target (L := L) (K := K) (n := n) (p := p + 1))ᶜ) := by
  classical
  -- through-mid: E[T→Done] ≤ E[T→Mid] + ∑ band, with Done ⊆ Mid.
  have hsub := chain_target_succ_subset (L := L) (K := K) p n
  have hmid := expectedHitting_le_through_mid (NonuniformMajority L K).transitionKernel hsub c
  refine le_trans hmid ?_
  -- bound the Mid hitting time by the per-rung seam cap; leave the band cross-term explicit.
  gcongr
  exact seam_rung_to_chain_target_le_nsq (L := L) (K := K) p n hp3 hn c hInvc htrig

/-! ## Part 9 — the honest chain-end mechanism (survey, no fake bridge)

**Which phases are timed seam rungs.**  The counter-drain engine and this seam engine
require `3 ≤ p` (`AllClockGEpCard_InvClosed`'s role-permanence floor) AND
`p ∈ {0,1,5,6,7,8}` (the counter-timed phases).  The intersection is `p ∈ {5,6,7,8}`: those
four are the seam rungs delivered here, each capped `≤ n²` (Part 7) and telescoped (Part 8).
Phases `0,1` (`p < 3`) and `2,3,4` are NOT counter-timed seam rungs — they are the paper's
"untimed phases that pass by epidemic expected `O(log n)`" (§7), already carried by the
`Phase4Convergence` / `seamEpidemicW` whp machinery upstream, not re-opened here.

**Phase 9 and the Phase-10 entry (the chain end).**  The protocol has NO phase-9 timed
counter and NO universal force-to-phase-10 (the campaign rejected the "all-backup" route as
DISHONEST: clock-less states have no counter-drain route, and `phaseInit 1` can error an
`mcr` to phase 10 only on the seam, not deterministically — `DOTY_POST63_CAMPAIGN.md`
§SeamPairBound finding 2, lines 2906/3384/3807).  The honest chain end is therefore NOT a
timed rung: the `≥`-window epidemic carries the population from phase `8`'s seam exit into
the **Phase-10 backup** (the `AllPhase10` regime), whose ENTRY is the universal phase
epidemic (`Transition_*_phase_ge_pair_max`, the same `max`-spread as every seam), reaching
`S1` / `Tie1plus` whp; from there `StableBridges`' Phase-10 stability bridges
(`phase10Majority_drained_mem_stableDone`, `phase10Tie_drained_mem_stableDone`) close to
`StableDone` at `0` bridge cost.  This phase-`8 → 10` epidemic entry (an `O(n log n)`
backup-stabilization, Lemma 7.7) is the named REMAINDER: it is an epidemic/backup expected
bound, NOT a seam counter-drain rung, so it is honestly outside this file's seam engine and
is supplied by the `Phase10ExpectedTime` backup machinery + `StableBridges` closure. -/

end TimedChainRungs

end ExactMajority
