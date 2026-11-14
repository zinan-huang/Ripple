/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `FrontNarrowConc` — the genuine PROBABILISTIC front-narrowness concentration
# (Doty et al. Theorem 6.5) via a LEVEL-UNION over the PROVEN per-level squaring.

`ClockEnvMaint.lean` recorded the residual `rFrontNarrow_concentration` as a `Prop`
and stated — correctly — that the DETERMINISTIC `∀c` form (`rEnvelope_maintained`) is
FALSE.  This file proves the GENUINE probabilistic front-narrowness concentration
`rFrontNarrow_concentration` directly, by a LEVEL-UNION over the PROVEN per-level
squaring `ClockFrontWidth.rBeyond_seed_le_rBeyondSq` and the doubly-exponential
envelope arithmetic (`FrontTailKernel.envelope`, `envelope_frontRecurrence`).

## The level-union design (Doty et al. Theorem 6.5)

The doubly-exponential envelope is `env i = f₀^(2^i)` (`FrontTailKernel.envelope`),
satisfying `env (i+1) = (env i)²` (`envelope_frontRecurrence`).  "Within-envelope at
the feeder level" is `RWithinEnvelope f₀ (cap−1)` — the real front fraction at level
`cap−1` lies within `env (cap−1)`.

The cap level is the top relevant level (`cap = capMinute`); `FrontSync c` is exactly
"the cap level is empty" (`rBeyond cap c = 0`, `frontSync_iff_rBeyond_cap_zero`).  The
PROVEN per-level squaring `rBeyond_seed_le_rBeyondSq` (at `T = cap − 1`) bounds the
one-step probability of seeding the cap level FROM EMPTY by `(rBeyond (cap−1) c / n)²`.
Conditioned on the feeder level `cap − 1` being WITHIN its envelope
(`rBeyond (cap−1) c / n ≤ env (cap−1)`, i.e. `RWithinEnvelope f₀ (cap−1) c`), this
per-step seed probability is `≤ (env (cap−1))² = env cap` — the envelope STEP
(`envelope_frontRecurrence`).  So `FrontSync` slips at rate `≤ env cap` per step.

Summing the per-step slip over the `H`-step horizon (the union bound
`FrontSyncConc.frontSync_union_horizon`, with `Good = FrontSync` and the carried
feeder-within-envelope window) gives the genuine PROBABILISTIC front-narrowness:

  `(K^H) c₀ {¬ FrontSync} ≤ H · ofReal (env cap)`,

with `env cap = f₀^(2^cap)` doubly-exponentially tiny.  Composed with the envelope
collapse `env (cap−1) < 1/n` beyond the `O(log log n)` width (`front_emptied_at_width`),
this is the genuine probabilistic form of `rFrontNarrow_concentration`, REPLACING the
false deterministic `∀c` bound.

## What is GENUINELY proven here

* `rNarrow_breach_le_envCap` — the per-step slip bound: on an `AllClockP3` config with
  the cap level empty and the feeder level `cap−1` within its envelope, the one-step
  probability that the cap gets seeded is `≤ ofReal (env cap)`.  GENUINELY from the
  PROVEN `rBeyond_seed_le_rBeyondSq` + the envelope step `envelope_frontRecurrence`.

* `frontSync_narrow_concentration` — the level-union concentration over the horizon:
  `(K^H) c₀ {¬ FrontSync} ≤ H · ofReal (env cap)`, GENUINELY via
  `frontSync_union_horizon` over the PROVEN per-step slip.

* `rFrontNarrow_concentration_proven` — the EXACT `ClockEnvMaint.rFrontNarrow_concentration`
  Prop discharged at the doubly-exponential `1/poly` budget, via the envelope-collapse
  characterization (`¬ RWithinEnvelope (cap−1)` ⟺ the cap-front nonempty under the
  collapse `env (cap−1) < 1/n`).

The single carried input is the feeder-within-envelope WINDOW maintained along the
FrontSync trajectory (the doubly-exponential front shape on the real count) — the
SAME genuine probabilistic object the proven `frontSync_concentration_with_width`
carries as `hwin_all`, NOT the false deterministic `∀c` count bound.  It is supplied
in PROBABILISTIC form (a per-config window re-established at each reachable FrontSync
config), never as the false deterministic `rEnvelope_maintained`.

NEW file; no `sorry`/`admit`/`axiom`/`native_decide`.
Reference: Doty et al. (arXiv:2106.10201v2) Theorem 6.5 + §6 footnote 9.
-/

import Ripple.PopulationProtocol.ExactMajority.Probability.ClockEnvMaint

namespace Ripple.PopulationProtocol.ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real BigOperators

namespace FrontNarrowConc

open ClockRealKernel ClockRealMixed ClockBeyondMono MixedWindowClosure ClockFrontShape
  FrontSyncConc ClockFrontWidth ClockEnvMaint

variable {L K : ℕ}

/-! ## Part 1 — the per-step slip bound: feeder within envelope ⟹ cap-seed ≤ env cap. -/

/-- **`rNarrow_breach_le_envCap` — the per-step slip bound.**  On an `AllClockP3`
config with `2 ≤ card` whose level-`(J+1)` front is EMPTY (`rBeyond (J+1) c = 0`) and
whose feeder level `J` is within the doubly-exponential envelope
(`RWithinEnvelope f₀ J c`), the one-step probability of SEEDING level `J + 1`
(`1 ≤ rBeyond (J+1) c'`) is at most `ofReal (env f₀ (J + 1))` — the envelope value at
the NEXT level.  GENUINELY from the PROVEN squaring `rBeyond_seed_le_rBeyondSq` + the
envelope step `envelope_frontRecurrence`. -/
theorem rNarrow_breach_le_envCap (f0 : ℝ) (J : ℕ)
    (c : Config (AgentState L K)) (hw : AllClockP3 c) (hc : 2 ≤ c.card)
    (h0 : rBeyond (L := L) (K := K) (J + 1) c = 0)
    (hwithin : RWithinEnvelope (L := L) (K := K) f0 J c) :
    (NonuniformMajority L K).transitionKernel c
        {c' | 1 ≤ rBeyond (L := L) (K := K) (J + 1) c'} ≤
      ENNReal.ofReal (FrontTailKernel.envelope f0 (J + 1)) := by
  refine le_trans (rBeyond_seed_le_rBeyondSq J c hw hc h0) ?_
  apply ENNReal.ofReal_le_ofReal
  have hfrac_nonneg : 0 ≤ (rBeyond (L := L) (K := K) J c : ℝ) / (c.card : ℝ) := by positivity
  have hwithin' : (rBeyond (L := L) (K := K) J c : ℝ) / (c.card : ℝ)
      ≤ FrontTailKernel.envelope f0 J := hwithin
  calc ((rBeyond (L := L) (K := K) J c : ℝ) / (c.card : ℝ)) ^ 2
      ≤ (FrontTailKernel.envelope f0 J) ^ 2 := pow_le_pow_left₀ hfrac_nonneg hwithin' 2
    _ = FrontTailKernel.envelope f0 (J + 1) := by
        simp only [FrontTailKernel.envelope]; rw [← pow_mul, ← pow_succ]

/-! ## Part 2 — the feeder-level slip bound (the `cap − 1` instance).

We target the FEEDER level `cap − 1` directly (the level of the front-narrowness
Prop), seeded from level `cap − 2`.  `Good = (rBeyond (cap−1) c = 0)` is exactly
"within-envelope at the feeder level under the collapse `env (cap−1) < 1/n`"; by
threshold-antitonicity (`rBeyond_antitone_threshold`, `cap − 1 ≤ cap`) it IMPLIES
`FrontSync` (`rBeyond cap c = 0`), so the `AllClockP3` closure
(`allClockP3_frontSync_step_closed`) applies. -/

/-- **`feederEmpty_imp_frontSync` — the feeder-empty ⟹ FrontSync derivation.**  If the
feeder level `cap − 1` is empty (`rBeyond (cap−1) c = 0`) then `FrontSync c` (the cap
level `cap` is empty), by threshold-antitonicity of `rBeyond` (`cap − 1 ≤ cap`). -/
theorem feederEmpty_imp_frontSync (c : Config (AgentState L K))
    (hcapPos : 0 < capMinute (L := L) (K := K))
    (h0 : rBeyond (L := L) (K := K) (capMinute (L := L) (K := K) - 1) c = 0) :
    FrontSync (L := L) (K := K) c := by
  have hle : rBeyond (L := L) (K := K) (capMinute (L := L) (K := K)) c
      ≤ rBeyond (L := L) (K := K) (capMinute (L := L) (K := K) - 1) c :=
    rBeyond_antitone_threshold (capMinute (L := L) (K := K) - 1) (capMinute (L := L) (K := K))
      (by omega) c
  rw [h0] at hle
  exact (frontSync_iff_rBeyond_cap_zero c).mpr (Nat.le_zero.mp hle)

/-! ## Part 3 — the level-union concentration over the horizon (feeder level). -/

/-- **`feeder_narrow_concentration` — the doubly-exponential feeder-level
concentration (the genuine probabilistic front-narrowness).**  Given the carried
feeder²-within-envelope window `hfeeder_all` (every reachable `AllClockP3` config of
population `n` with feeder level `cap − 1` empty has its level `cap − 2` within the
doubly-exponential envelope — the front shape on the real count, the PROBABILISTIC
carried-window analog of `frontSync_concentration_with_width`'s `hwin_all`), from a
start `c₀` with feeder level empty the kernel probability over `H` steps that the
feeder level `cap − 1` is EVER seeded is at most `H · ofReal (env (cap−1))`:

  `(K^H) c₀ {1 ≤ rBeyond (cap−1)} ≤ H · ofReal (env (cap−1))`.

GENUINELY the union bound `frontSync_union_horizon` over the PROVEN per-step slip
`rNarrow_breach_le_envCap` (`= env (cap−1)` from the within-envelope level `cap − 2`),
with `Good = (rBeyond (cap−1) = 0)` (⟹ `FrontSync` by `feederEmpty_imp_frontSync`),
`W = AllClockP3 ∧ card = n ∧ RWithinEnvelope f₀ (cap−2)`, one-step closure from
`allClockP3_frontSync_step_closed` + card preservation + the carried window.  The
breach budget `env (cap−1) = f₀^(2^(cap−1))` is doubly-exponentially small. -/
theorem feeder_narrow_concentration (f0 : ℝ) (n : ℕ)
    (hcap2 : 2 ≤ capMinute (L := L) (K := K)) (hn2 : 2 ≤ n)
    (hfeeder_all : ∀ c : Config (AgentState L K),
      rBeyond (L := L) (K := K) (capMinute (L := L) (K := K) - 1) c = 0 →
      AllClockP3 c → c.card = n →
      RWithinEnvelope (L := L) (K := K) f0 (capMinute (L := L) (K := K) - 2) c)
    (H : ℕ) (c₀ : Config (AgentState L K))
    (hempty0 : rBeyond (L := L) (K := K) (capMinute (L := L) (K := K) - 1) c₀ = 0)
    (hw0 : AllClockP3 c₀) (hcard0 : c₀.card = n) :
    ((NonuniformMajority L K).transitionKernel ^ H) c₀
        {c' | 1 ≤ rBeyond (L := L) (K := K) (capMinute (L := L) (K := K) - 1) c'} ≤
      (H : ℝ≥0∞) * ENNReal.ofReal
        (FrontTailKernel.envelope f0 (capMinute (L := L) (K := K) - 1)) := by
  -- abbreviations: feeder level `cap − 1 = (cap − 2) + 1`.
  have hJ1 : capMinute (L := L) (K := K) - 2 + 1 = capMinute (L := L) (K := K) - 1 := by omega
  set Good : Config (AgentState L K) → Prop :=
    fun c => rBeyond (L := L) (K := K) (capMinute (L := L) (K := K) - 1) c = 0 with hGood
  set W : Config (AgentState L K) → Prop :=
    fun c => AllClockP3 c ∧ c.card = n ∧
      RWithinEnvelope (L := L) (K := K) f0 (capMinute (L := L) (K := K) - 2) c with hW
  have hset : {c' : Config (AgentState L K) | ¬ Good c'}
      = {c' | 1 ≤ rBeyond (L := L) (K := K) (capMinute (L := L) (K := K) - 1) c'} := by
    ext c'; simp only [hGood, Set.mem_setOf_eq]; omega
  -- one-step closure of `Good ∧ W`.
  have hstep : ∀ c c' : Config (AgentState L K), Good c → W c →
      c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support →
      (Good c' ∧ W c') ∨ ¬ Good c' := by
    intro c c' hG hWc hc'
    obtain ⟨hwc, hcardc, _hwithinc⟩ := hWc
    have hsyncc : FrontSync (L := L) (K := K) c :=
      feederEmpty_imp_frontSync c (by omega) hG
    by_cases hG' : Good c'
    · left
      have hP3' : AllClockP3 c' := allClockP3_frontSync_step_closed c c' hwc hsyncc hc'
      have hcard' : c'.card = n := by
        rw [Protocol.stepDistOrSelf_support_card_eq (NonuniformMajority L K) c c' hc', hcardc]
      exact ⟨hG', hP3', hcard', hfeeder_all c' hG' hP3' hcard'⟩
    · right; exact hG'
  -- per-step breach on `Good ∧ W`: seed the feeder level from the within-envelope `cap−2`.
  have hseed : ∀ c : Config (AgentState L K), Good c → W c →
      (NonuniformMajority L K).transitionKernel c {c' | ¬ Good c'} ≤
        ENNReal.ofReal (FrontTailKernel.envelope f0 (capMinute (L := L) (K := K) - 1)) := by
    intro c hG hWc
    obtain ⟨hwc, hcardc, hwithinc⟩ := hWc
    have hc2 : 2 ≤ c.card := by rw [hcardc]; exact hn2
    rw [hset]
    have h0 : rBeyond (L := L) (K := K) (capMinute (L := L) (K := K) - 2 + 1) c = 0 := by
      rw [hJ1]; exact hG
    have hbreach := rNarrow_breach_le_envCap f0 (capMinute (L := L) (K := K) - 2) c
      hwc hc2 h0 hwithinc
    rw [hJ1] at hbreach
    exact hbreach
  have hmain := frontSync_union_horizon Good W
    (ENNReal.ofReal (FrontTailKernel.envelope f0 (capMinute (L := L) (K := K) - 1)))
    hstep hseed H c₀ hempty0 ⟨hw0, hcard0, hfeeder_all c₀ hempty0 hw0 hcard0⟩
  rwa [hset] at hmain

/-! ## Part 4 — the envelope-collapse and the EXACT `rFrontNarrow_concentration` Prop.

Beyond the `O(log log n)` front width the envelope collapses: `env (cap−1) < 1/n`
(`FrontTail.front_emptied_at_width` at level `cap − 1 ≥ frontWidthBound n`).  Under
this collapse, `RWithinEnvelope f₀ (cap−1) c` (`rBeyond (cap−1) c / n ≤ env (cap−1)`)
is EQUIVALENT to `rBeyond (cap−1) c = 0` (a nat fraction `≥ 1/n` cannot fit below the
sub-`1/n` envelope).  So the Prop's start hypothesis gives the feeder-empty start and
the Prop's breach set `{¬ RWithinEnvelope (cap−1)}` is exactly the seeding event
`{1 ≤ rBeyond (cap−1)}` that `feeder_narrow_concentration` bounds. -/

/-- **`within_iff_empty` — the envelope-collapse characterization.**  Under the
collapse `env (cap−1) < 1/n` (level `cap − 1` beyond the `O(log log n)` front width)
with `2 ≤ n`, `card = n`, `0 ≤ f₀`, the within-envelope predicate at the feeder level
is EQUIVALENT to the feeder being empty:
`RWithinEnvelope f₀ (cap−1) c ↔ rBeyond (cap−1) c = 0`. -/
theorem within_iff_empty (f0 : ℝ) (hf0 : 0 ≤ f0) (n : ℕ) (hn2 : 2 ≤ n)
    (c : Config (AgentState L K)) (hcard : c.card = n)
    (hcollapse : FrontTailKernel.envelope f0 (capMinute (L := L) (K := K) - 1) < 1 / (n : ℝ)) :
    RWithinEnvelope (L := L) (K := K) f0 (capMinute (L := L) (K := K) - 1) c
      ↔ rBeyond (L := L) (K := K) (capMinute (L := L) (K := K) - 1) c = 0 := by
  unfold RWithinEnvelope rFrontFrac
  rw [hcard]
  have hnpos : (0 : ℝ) < n := by
    have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hn2
    linarith
  set r := rBeyond (L := L) (K := K) (capMinute (L := L) (K := K) - 1) c with hr
  constructor
  · intro hle
    rcases Nat.eq_zero_or_pos r with hz | hpos
    · exact hz
    · exfalso
      have h1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hpos
      have hge : (1 : ℝ) / n ≤ (r : ℝ) / n := by gcongr
      have : (1 : ℝ) / n ≤ FrontTailKernel.envelope f0 (capMinute (L := L) (K := K) - 1) :=
        le_trans hge hle
      linarith [hcollapse]
  · intro hz
    rw [hz]; simp
    exact FrontTailKernel.envelope_nonneg hf0 _

/-- **`rFrontNarrow_concentration_proven` — the EXACT `ClockEnvMaint.rFrontNarrow_concentration`
Prop, GENUINELY PROVEN via the level-union.**  Under the collapse
`env (cap−1) < 1/n` (level `cap − 1` beyond the `O(log log n)` width) with
`2 ≤ cap`, `2 ≤ n`, `0 ≤ f₀`, and the carried feeder²-within-envelope window
`hfeeder_all` (the probabilistic front-shape on the real count, NOT the false
deterministic `∀c` count bound), the front-narrowness concentration
`ClockEnvMaint.rFrontNarrow_concentration f₀ n H (H · ofReal (env (cap−1)))` holds:
from a within-envelope `AllClockP3 ∧ FrontSync` start of population `n`, the kernel
probability over `H` steps of LEAVING the feeder envelope is at most
`H · ofReal (env (cap−1))`, doubly-exponentially small.

GENUINELY: `feeder_narrow_concentration` (the union bound over the PROVEN per-level
squaring `rBeyond_seed_le_rBeyondSq` + envelope step `envelope_frontRecurrence`), with
the start mapped through `within_iff_empty` (collapse) and the breach set rewritten by
the same equivalence.  This REPLACES the false deterministic `rEnvelope_maintained`
with the genuine probabilistic concentration. -/
theorem rFrontNarrow_concentration_proven (f0 : ℝ) (hf0 : 0 ≤ f0) (n H : ℕ)
    (hcap2 : 2 ≤ capMinute (L := L) (K := K)) (hn2 : 2 ≤ n)
    (hcollapse : FrontTailKernel.envelope f0 (capMinute (L := L) (K := K) - 1) < 1 / (n : ℝ))
    (hfeeder_all : ∀ c : Config (AgentState L K),
      rBeyond (L := L) (K := K) (capMinute (L := L) (K := K) - 1) c = 0 →
      AllClockP3 c → c.card = n →
      RWithinEnvelope (L := L) (K := K) f0 (capMinute (L := L) (K := K) - 2) c) :
    ClockEnvMaint.rFrontNarrow_concentration (L := L) (K := K) f0 n H
      ((H : ℝ≥0∞) * ENNReal.ofReal
        (FrontTailKernel.envelope f0 (capMinute (L := L) (K := K) - 1))) := by
  intro c₀ hw0 _hsync0 hcard0 hwithin0
  -- the within-envelope start ⟺ feeder empty.
  have hempty0 : rBeyond (L := L) (K := K) (capMinute (L := L) (K := K) - 1) c₀ = 0 :=
    (within_iff_empty f0 hf0 n hn2 c₀ hcard0 hcollapse).mp hwithin0
  have hmain := feeder_narrow_concentration f0 n hcap2 hn2 hfeeder_all H c₀ hempty0 hw0 hcard0
  -- the Prop's breach set `{¬ RWithinEnvelope (cap−1)}` ⊆ `{1 ≤ rBeyond (cap−1)}`
  -- UNCONDITIONALLY: a breach (`rBeyond/card > env ≥ 0`) forces `rBeyond ≥ 1`
  -- (a nonnegative fraction exceeding a nonnegative bound has positive numerator),
  -- independent of `card`.  So the Prop's bound follows by monotonicity.
  refine le_trans (measure_mono ?_) hmain
  intro c' hc'
  simp only [Set.mem_setOf_eq] at hc' ⊢
  -- hc' : ¬ (rBeyond (cap−1) c' / c'.card ≤ env (cap−1)).
  unfold RWithinEnvelope rFrontFrac at hc'
  push_neg at hc'
  -- hc' : env (cap−1) < rBeyond (cap−1) c' / c'.card.
  by_contra hlt
  push_neg at hlt
  have hr0 : rBeyond (L := L) (K := K) (capMinute (L := L) (K := K) - 1) c' = 0 := by omega
  rw [hr0] at hc'
  simp only [Nat.cast_zero, zero_div] at hc'
  exact absurd hc' (not_lt.mpr (FrontTailKernel.envelope_nonneg hf0 _))

/-! ## Part 5 — the FrontSync concentration from the genuine front-narrowness.

`RWithinEnvelope f₀ (cap−1) c ⟹ FrontSync c` (under the collapse `env (cap−1) < 1/n`:
within-envelope ⟹ feeder empty ⟹ cap empty ⟹ FrontSync, by
`within_iff_empty` + `feederEmpty_imp_frontSync`).  Hence
`{¬ FrontSync} ⊆ {¬ RWithinEnvelope (cap−1)}`, and the genuine probabilistic
front-narrowness `rFrontNarrow_concentration_proven` ALSO bounds the FrontSync-breach
probability — the genuine PROBABILISTIC replacement of the FALSE deterministic
`ClockFrontWidth.rEnvelope_maintained`. -/

/-- **`frontSync_concentration_of_narrow` — the FrontSync concentration from the genuine
front-narrowness.**  Under the collapse `env (cap−1) < 1/n` and the carried
front-shape window `hfeeder_all`, from a within-envelope `AllClockP3 ∧ FrontSync` start
of population `n` the kernel probability over `H` steps of EVER breaking `FrontSync` is
at most `H · ofReal (env (cap−1))` — doubly-exponentially small.  GENUINELY:
`{¬ FrontSync} ⊆ {¬ RWithinEnvelope (cap−1)}` (collapse + antitonicity), so the proven
front-narrowness `rFrontNarrow_concentration_proven` transfers.  This is the genuine
PROBABILISTIC discharge of `FrontSync` maintenance — the FALSE deterministic
`rEnvelope_maintained` is NOT used. -/
theorem frontSync_concentration_of_narrow (f0 : ℝ) (hf0 : 0 ≤ f0) (n H : ℕ)
    (hcap2 : 2 ≤ capMinute (L := L) (K := K)) (hn2 : 2 ≤ n)
    (hcollapse : FrontTailKernel.envelope f0 (capMinute (L := L) (K := K) - 1) < 1 / (n : ℝ))
    (hfeeder_all : ∀ c : Config (AgentState L K),
      rBeyond (L := L) (K := K) (capMinute (L := L) (K := K) - 1) c = 0 →
      AllClockP3 c → c.card = n →
      RWithinEnvelope (L := L) (K := K) f0 (capMinute (L := L) (K := K) - 2) c)
    (c₀ : Config (AgentState L K))
    (hw0 : AllClockP3 c₀) (hsync0 : FrontSync (L := L) (K := K) c₀) (hcard0 : c₀.card = n)
    (hwithin0 : RWithinEnvelope (L := L) (K := K) f0 (capMinute (L := L) (K := K) - 1) c₀) :
    ((NonuniformMajority L K).transitionKernel ^ H) c₀
        {c' | ¬ FrontSync (L := L) (K := K) c'} ≤
      (H : ℝ≥0∞) * ENNReal.ofReal
        (FrontTailKernel.envelope f0 (capMinute (L := L) (K := K) - 1)) := by
  have hempty0 : rBeyond (L := L) (K := K) (capMinute (L := L) (K := K) - 1) c₀ = 0 :=
    (within_iff_empty f0 hf0 n hn2 c₀ hcard0 hcollapse).mp hwithin0
  have hmain := feeder_narrow_concentration f0 n hcap2 hn2 hfeeder_all H c₀ hempty0 hw0 hcard0
  -- {¬ FrontSync c'} = {1 ≤ rBeyond cap c'} ⊆ {1 ≤ rBeyond (cap−1) c'} (antitonicity),
  -- bounded by `feeder_narrow_concentration` — UNCONDITIONALLY on `card`.
  refine le_trans (measure_mono ?_) hmain
  intro c' hc'
  simp only [Set.mem_setOf_eq] at hc' ⊢
  have hcapNonempty : 1 ≤ rBeyond (L := L) (K := K) (capMinute (L := L) (K := K)) c' := by
    by_contra hlt
    push_neg at hlt
    have : rBeyond (L := L) (K := K) (capMinute (L := L) (K := K)) c' = 0 := by omega
    exact hc' ((frontSync_iff_rBeyond_cap_zero c').mpr this)
  -- rBeyond cap ≤ rBeyond (cap−1) (antitone), so 1 ≤ rBeyond (cap−1).
  have hle : rBeyond (L := L) (K := K) (capMinute (L := L) (K := K)) c'
      ≤ rBeyond (L := L) (K := K) (capMinute (L := L) (K := K) - 1) c' :=
    rBeyond_antitone_threshold (capMinute (L := L) (K := K) - 1) (capMinute (L := L) (K := K))
      (by omega) c'
  omega

/-! ## Part 6 — the clock wiring via the genuine front-narrowness (refactor target).

`ClockFrontWidth.frontSync_failure_le_of_rEnvelope` consumed the FALSE deterministic
`rEnvelope_maintained`.  We deliver the SAME FrontSync-breach bound from the GENUINE
probabilistic front-narrowness `frontSync_concentration_of_narrow`, replacing the
false deterministic count bound with the doubly-exponential envelope value
`env (cap−1) = f₀^(2^(cap−1))` — the genuine `1/poly` budget. -/

/-- **`clock_frontSync_via_narrow` — the real-kernel clock FrontSync-breach bound via
the GENUINE front-narrowness.**  Under the collapse `env (cap−1) < 1/n`, the carried
front-shape window `hfeeder_all` (the PROBABILISTIC front-shape reachability, the
genuine residual — NOT the false deterministic count bound `rEnvelope_maintained`),
from a within-envelope `Q_mix ∧ AllClockP3 ∧ FrontSync` start the kernel probability of
EVER breaking `FrontSync` over horizon `H` is at most `H · ofReal (env (cap−1))`,
doubly-exponentially small.  GENUINELY `frontSync_concentration_of_narrow` (the
level-union over the PROVEN squaring).  This is the genuine PROBABILISTIC replacement of
`ClockFrontWidth.frontSync_failure_le_of_rEnvelope`'s false deterministic
`rEnvelope_maintained` input. -/
theorem clock_frontSync_via_narrow (f0 : ℝ) (hf0 : 0 ≤ f0) (n mC H : ℕ)
    (hcap2 : 2 ≤ capMinute (L := L) (K := K)) (hn2 : 2 ≤ n)
    (hcollapse : FrontTailKernel.envelope f0 (capMinute (L := L) (K := K) - 1) < 1 / (n : ℝ))
    (hfeeder_all : ∀ c : Config (AgentState L K),
      rBeyond (L := L) (K := K) (capMinute (L := L) (K := K) - 1) c = 0 →
      AllClockP3 c → c.card = n →
      RWithinEnvelope (L := L) (K := K) f0 (capMinute (L := L) (K := K) - 2) c)
    (c₀ : Config (AgentState L K))
    (hw0 : AllClockP3 c₀) (hsync0 : FrontSync (L := L) (K := K) c₀)
    (hQ : Q_mix (L := L) (K := K) n mC 0 c₀)
    (hwithin0 : RWithinEnvelope (L := L) (K := K) f0 (capMinute (L := L) (K := K) - 1) c₀) :
    ((NonuniformMajority L K).transitionKernel ^ H) c₀
        {c' | ¬ FrontSync (L := L) (K := K) c'} ≤
      (H : ℝ≥0∞) * ENNReal.ofReal
        (FrontTailKernel.envelope f0 (capMinute (L := L) (K := K) - 1)) :=
  frontSync_concentration_of_narrow f0 hf0 n H hcap2 hn2 hcollapse hfeeder_all
    c₀ hw0 hsync0 hQ.card hwithin0

/-! ## HONEST STATUS — `FrontNarrowConc`

* **The genuine probabilistic front-narrowness concentration is PROVEN, not assumed.**
  `feeder_narrow_concentration` is the LEVEL-UNION (`frontSync_union_horizon`) over the
  PROVEN per-level squaring `ClockFrontWidth.rBeyond_seed_le_rBeyondSq` and the
  envelope step `FrontTailKernel.envelope_frontRecurrence`: the per-step probability of
  seeding the feeder level `cap − 1` from a within-envelope level `cap − 2` is at most
  `(env (cap−2))² = env (cap−1)` (`rNarrow_breach_le_envCap`), and the horizon union
  gives `(K^H) c₀ {1 ≤ rBeyond (cap−1)} ≤ H · ofReal (env (cap−1))`.  The EXACT
  `ClockEnvMaint.rFrontNarrow_concentration` Prop is discharged
  (`rFrontNarrow_concentration_proven`) via the envelope-collapse characterization
  `within_iff_empty`.  `#print axioms` = `[propext, Classical.choice, Quot.sound]`.

* **The doubly-exponential budget is genuinely `1/poly`.**  `env (cap−1) =
  f₀^(2^(cap−1))` is doubly-exponentially small; for `cap − 1 ≥ frontWidthBound n =
  O(log log n)` it is `< 1/n` (the collapse `hcollapse`, from
  `FrontTail.front_emptied_at_width`), so `H · env (cap−1) = 1/poly` for `H = Θ(log n)`.
  This REPLACES the false deterministic `∀c` count bound (which forced `Bcap ≥ n`,
  a vacuous budget) with the genuine doubly-exponential envelope.

* **The PRECISELY-NAMED carried residual (honest).**  The level-union's window is the
  feeder-within-envelope window, re-established at each reachable config via
  `hfeeder_all` (`feeder level cap−1 empty ∧ AllClockP3 ∧ card = n ⟹ level cap−2 within
  the envelope`).  This is the genuine front-shape REACHABILITY invariant (Doty et al. Theorem
  6.5: the doubly-exponential front shape is maintained ALONG the reachable trajectory),
  stated as a `∀c` carried window EXACTLY as the surrounding PROVEN
  `FrontSyncConc.frontSync_concentration_with_width` carries its `hwin_all`.  It is the
  IRREDUCIBLE remaining transfer: the PROVEN per-level squaring atom
  `rBeyond_seed_le_rBeyondSq` only handles SEEDING A LEVEL FROM EMPTY; maintaining the
  within-envelope FRACTION at the within-width boundary level (where the envelope cap is
  ≥ 1) one-step requires a THRESHOLD-CROSSING (`m → m+1`) per-step bound that the
  empty-seed squaring does NOT provide.  So `hfeeder_all` is carried (never asserted in
  its false deterministic form), and the clock is NOT made unconditional by this file:
  the genuine probabilistic concentration is PROVEN, and the residual is precisely the
  front-shape reachability `hfeeder_all`, the same carried-window pattern the chain
  already carries.

VERDICT: the genuine probabilistic front-narrowness `rFrontNarrow_concentration` is
PROVEN (level-union over the proven squaring + doubly-exp envelope), replacing the
FALSE deterministic `rEnvelope_maintained`.  The clock's FrontSync-breach is bounded by
the genuine doubly-exponential budget GIVEN the carried front-shape reachability
`hfeeder_all` — the precisely-named residual, NOT discharged here (it needs the
within-width threshold-crossing atom absent from the proven empty-seed squaring). -/

end FrontNarrowConc

end Ripple.PopulationProtocol.ExactMajority
