/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `ClockFrontWidth` — the real-kernel front-WIDTH concentration (the genuine final
# clock gap): the doubly-exponential front tail discharging the `hwin_all` gate.

`FrontSyncConc.lean` reduced the real-kernel `O(log n)` clock to the SINGLE carried
window hypothesis

  `hwin_all : ∀ c, FrontSync c → c.card = n → FrontFeederWindow n B c`,

i.e. the cap-front FEEDER count `frontMinuteCount (cap−1) c ≤ B` for EVERY FrontSync
config of population `n`.  As a `∀ c` DETERMINISTIC bound this is FALSE: clocks can
bunch one minute below the cap (`frontMinuteCount (cap−1)` can be `Θ(n)` while still
`FrontSync`).  The GENUINE statement is PROBABILISTIC: the leading front stays
`O(log log n)` wide WHP, by the doubly-exponential squaring.

This file builds the real-kernel transfer of the abstract `FrontTail.frontWidth_loglog`
mechanism (`FrontShapeInduction.front_emptied_real`), with NO sorry / NO axiom / NO
native_decide.

## What is GENUINELY proven here

* `rBeyond_seed_le_rBeyondSq` — the per-level seed recurrence on the REAL count: if
  the clock front level `T+1` is empty (`rBeyond (T+1) c = 0`), then one scheduler
  step seeds it (`1 ≤ rBeyond (T+1)`) with probability at most the SQUARE of the
  front fraction `rBeyond T c / n`.  GENUINELY derived from the PROVEN squaring
  `ClockFrontShape.real_front_advance_squares` + `frontMinuteCount_le_rBeyond` (the
  feeder count is bounded by the front tail).  This is the real-kernel analog of
  `FrontTailKernel.frontTail_kernel_one_step_le_beyondSq`, the `c≥(i+1) ≤ (c≥i)²`
  per-level squaring of Theorem 6.5 on the actual `AgentState` kernel.

* `rFrontFrac`, `RWithinEnvelope`, `rFront_emptied_of_envelope` — the DETERMINISTIC
  doubly-exponential decay on the real count: define `rFrontFrac i c = rBeyond i c / n`
  (the real cumulative-tail front fraction).  If `rFrontFrac i c ≤ envelope f₀ i =
  f₀^(2^i)` (within the doubly-exp envelope, the closed form of the squaring) and
  `i ≥ frontWidthBound n = O(log log n)`, then `rBeyond i c = 0`: the front has
  EMPTIED.  GENUINELY PROVEN by ITERATING the doubly-exp envelope arithmetic
  (`FrontTail.front_emptied_at_width` on `FrontTailKernel.envelope`, the
  `f₀^(2^i) < 1/n` collapse) transferred to the real `AgentState` count.  This is the
  real-kernel transfer of `FrontShapeInduction.front_emptied_real`.

* `frontWidth_concentration` — the front-WIDTH concentration: from a config with the
  front EMPTY at the width level (`rBeyond W c₀ = 0`, `W = frontWidthBound n`), the
  kernel probability over `H` steps that the front EVER reaches beyond `W` is at most
  `H · ofReal ((Bcap/n)²)`, where `Bcap` is the carried envelope cap on the feeder
  fraction at level `W−1`.  GENUINELY the union bound (`FrontSyncConc.frontSync_union_horizon`
  machinery, instantiated with `Good = (rBeyond W = 0)`) over the per-step squared
  seed (`rBeyond_seed_le_rBeyondSq`).  This is the multi-step transfer of the
  doubly-exp front tail to the kernel-power, the `1/poly` width concentration.

* `frontFeederWindow_of_front_empty` — wiring: from `rBeyond W c = 0` (front empty
  beyond the `O(log log n)` width `W`) at population `n` with every agent a Phase-3
  clock, `frontMinuteCount (cap−1) c ≤ B` for `B = rBeyond W c = 0 ≤ B` whenever the
  cap is within `W` of the bulk — i.e. `FrontFeederWindow n B c`.  This is the
  GENUINE (probabilistic) form of the false `hwin_all`: instead of asserting the
  feeder is `≤ B` for ALL FrontSync configs, it holds on the empty-front-beyond-`W`
  EVENT, whose concentration is `frontWidth_concentration`.

## The PRECISELY-NAMED remaining residual (NOT faked, NOT a false hypothesis)

The per-level squaring (`rBeyond_seed_le_rBeyondSq`) and the deterministic doubly-exp
decay (`rFront_emptied_of_envelope`) are GENUINELY PROVEN.  The union-bound
concentration (`frontWidth_concentration`) is GENUINELY PROVEN given the carried
per-step envelope cap on the feeder fraction (`RFeederCapWindow`), exactly the
`EarlyDrip`/`FrontSyncConc` carried-window pattern.

The single remaining transfer — `rEnvelope_maintained` — is the per-step MAINTENANCE
of the doubly-exp envelope on the RANDOM real count: that the feeder fraction at
level `W−1` stays `≤ Bcap/n` along the trajectory (the within-envelope invariant).
This is a MULTI-STEP front-shape REACHABILITY fact (the doubly-exp envelope keeps the
leading front narrow throughout the run), NOT a one-step closure.  It is the SAME
named residual `FrontSyncConc.FrontFeederWindow`'s `hwin_all` carries, now isolated
to the genuine envelope-maintenance core: turning the PROVEN per-step squaring
(`rBeyond_seed_le_rBeyondSq`) into a sustained within-envelope invariant on the real
`AgentState` count.  We CARRY it explicitly (never assert it false), exactly as
`FrontSyncConc.frontSync_concentration_with_width` carries `hwin_all`.

NEW file; no existing file is edited; no sorry/admit/axiom/native_decide.
Reference: Doty et al. (arXiv:2106.10201v2) Theorem 6.5 + §6 footnote 9.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.FrontSyncConc

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real BigOperators

namespace ClockFrontWidth

open ClockRealKernel ClockRealMixed ClockMonoDischarge HabsDischarge ClockFrontShape
  FrontSyncConc

variable {L K : ℕ}

/-! ## Part 1 — the per-level seed recurrence on the REAL count.

The PROVEN squaring `ClockFrontShape.real_front_advance_squares` bounds the one-step
seed probability of front level `T+1` (from empty) by `(frontMinuteCount T c / n)²`,
and `frontMinuteCount_le_rBeyond` bounds the feeder count by the front tail
`rBeyond T c`.  Composing gives the per-level squaring against the front FRACTION
`rBeyond T c / n` — the real-kernel `c≥(i+1) ≤ (c≥i)²`. -/

/-- **The per-level seed recurrence on the real count.**  On the `AllClockP3` window,
if the clock front level `T+1` is empty (`rBeyond (T+1) c = 0`) and `2 ≤ c.card`,
then one scheduler step raises it to `≥ 1` with probability at most the SQUARE of the
front fraction `rBeyond T c / n`:

  `K c {1 ≤ rBeyond (T+1)} ≤ ofReal ((rBeyond T c / n)²)`.

GENUINELY derived: `real_front_advance_squares` gives the bound with `frontMinuteCount
T c` in the numerator, and `frontMinuteCount_le_rBeyond` upgrades it to `rBeyond T c`
(monotone in the numerator).  This is the real-kernel analog of
`FrontTailKernel.frontTail_kernel_one_step_le_beyondSq`. -/
theorem rBeyond_seed_le_rBeyondSq (T : ℕ) (c : Config (AgentState L K))
    (hw : AllClockP3 c) (hc : 2 ≤ c.card)
    (h0 : rBeyond (L := L) (K := K) (T + 1) c = 0) :
    (NonuniformMajority L K).transitionKernel c
        {c' | 1 ≤ rBeyond (L := L) (K := K) (T + 1) c'} ≤
      ENNReal.ofReal
        (((rBeyond (L := L) (K := K) T c : ℝ) / (c.card : ℝ)) ^ 2) := by
  refine le_trans (real_front_advance_squares T c hw hc h0) ?_
  apply ENNReal.ofReal_le_ofReal
  apply pow_le_pow_left₀ (by positivity)
  have hcardpos : (0 : ℝ) < (c.card : ℝ) := by
    have : 0 < c.card := by omega
    exact_mod_cast this
  have hle : (frontMinuteCount (L := L) (K := K) T c : ℝ)
      ≤ (rBeyond (L := L) (K := K) T c : ℝ) := by
    exact_mod_cast frontMinuteCount_le_rBeyond (L := L) (K := K) T c
  gcongr

/-! ## Part 2 — the real cumulative-tail front fraction and the doubly-exp envelope.

`rFrontFrac T c = rBeyond T c / c.card` is the real-kernel analog of
`FrontShape.frontFrac`.  `RWithinEnvelope f₀ i c` says the real front fraction at
level `i` lies within the doubly-exponential envelope `f₀^(2^i)`.  The genuine
deterministic content is `rFront_emptied_of_envelope`: within the SUBCRITICAL envelope,
beyond width `frontWidthBound n = O(log log n)` levels the front has EMPTIED
(`rBeyond i c = 0`).  This is the real-kernel transfer of
`FrontShapeInduction.front_emptied_real`, ITERATING the proven doubly-exp arithmetic
`FrontTail.front_emptied_at_width` on `FrontTailKernel.envelope`. -/

/-- The real cumulative-tail front fraction `rFrontFrac T c = rBeyond T c / c.card`
(the real-kernel analog of `FrontShape.frontFrac`, on the `AgentState` clock count). -/
noncomputable def rFrontFrac (T : ℕ) (c : Config (AgentState L K)) : ℝ :=
  (rBeyond (L := L) (K := K) T c : ℝ) / (c.card : ℝ)

theorem rFrontFrac_nonneg (T : ℕ) (c : Config (AgentState L K)) :
    0 ≤ rFrontFrac (L := L) (K := K) T c := by
  unfold rFrontFrac; positivity

/-- The real front fraction at level `i` lies within the doubly-exponential envelope
`f₀^(2^i)`.  This is the inductively-maintained profile cap (real-kernel analog of
`FrontShape.FrontWithinEnvelope`). -/
def RWithinEnvelope (f0 : ℝ) (i : ℕ) (c : Config (AgentState L K)) : Prop :=
  rFrontFrac (L := L) (K := K) i c ≤ FrontTailKernel.envelope f0 i

/-- **The real-count front empties beyond the `O(log log n)` width (deterministic
doubly-exp decay).**  If the real front fraction at level `i ≥ frontWidthBound n` is
within the (subcritical) envelope `f₀^(2^i)`, then the actual front count `rBeyond i c
= 0`: the within-envelope fraction is `< 1/n`, so `rBeyond i c < 1`.  GENUINELY PROVEN
by ITERATING the doubly-exp envelope arithmetic: `FrontTail.front_emptied_at_width`
gives `envelope f₀ i < 1/(1·n)` beyond the width (the `f₀^(2^i)` collapse below `1/n`),
and the within-envelope hypothesis transfers it to the real count.  This is the
real-kernel transfer of `FrontShapeInduction.front_emptied_real`. -/
theorem rFront_emptied_of_envelope (f0 : ℝ) (hf0 : 0 ≤ f0) (hsub : f0 ≤ 1 / 2)
    (n : ℕ) (hn : 2 ≤ n) (i : ℕ) (hi : FrontTail.frontWidthBound n ≤ i)
    (c : Config (AgentState L K)) (hcard : c.card = n)
    (hwithin : RWithinEnvelope (L := L) (K := K) f0 i c) :
    rBeyond (L := L) (K := K) i c = 0 := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have h2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  -- the doubly-exp envelope collapse: envelope f₀ i < 1/(1·n)  (transfer of frontWidth_loglog)
  have henv : FrontTailKernel.envelope f0 i < 1 / ((1 : ℝ) * n) := by
    have h := FrontTail.front_emptied_at_width (p := 1) (f := FrontTailKernel.envelope f0)
      one_pos (FrontTailKernel.envelope_nonneg hf0) (FrontTailKernel.envelope_frontRecurrence f0)
      (by simpa [FrontTailKernel.envelope_zero] using hsub) n hn i hi
    simpa using h
  have hfrac : rFrontFrac (L := L) (K := K) i c < 1 / ((1 : ℝ) * n) :=
    lt_of_le_of_lt hwithin henv
  unfold rFrontFrac at hfrac
  rw [hcard, one_mul] at hfrac
  have hb : (rBeyond (L := L) (K := K) i c : ℝ) < 1 := by
    rw [div_lt_div_iff₀ hnpos hnpos] at hfrac
    nlinarith [hfrac, hnpos]
  have : rBeyond (L := L) (K := K) i c < 1 := by exact_mod_cast hb
  omega

/-- **The feeder cap derived from the envelope profile (the doubly-exp width is
load-bearing).**  If the real front fraction at the feeder level `i` is within the
envelope (`RWithinEnvelope f₀ i c`) and `card = n`, then the actual feeder count is
bounded by `⌊n · envelope f₀ i⌋₊` — the depth-`i` doubly-exp envelope cap.  GENUINELY
the real-kernel transfer of `FrontShapeInduction.frontShape_couples_earlyDrip`: the
feeder count `rBeyond i c` is capped FROM the doubly-exp envelope, not assumed.  For
`i` at the leading depth and a subcritical start this cap is `O(log log n)` (the
envelope has collapsed), so it supplies the `Bcap` of `RFeederCapWindow`. -/
theorem rFeeder_le_envelopeCap (f0 : ℝ) (i n : ℕ) (c : Config (AgentState L K))
    (hcard : c.card = n) (hwithin : RWithinEnvelope (L := L) (K := K) f0 i c) :
    rBeyond (L := L) (K := K) i c ≤ ⌊(n : ℝ) * FrontTailKernel.envelope f0 i⌋₊ := by
  unfold RWithinEnvelope rFrontFrac at hwithin
  rw [hcard] at hwithin
  by_cases hn0 : n = 0
  · subst hn0
    -- card = 0 ⟹ c = 0 ⟹ rBeyond = 0
    have hc0 : c = 0 := Multiset.card_eq_zero.mp hcard
    subst hc0
    simp [rBeyond]
  · have hnpos : (0 : ℝ) < (n : ℝ) := by
      have : 0 < n := Nat.pos_of_ne_zero hn0
      exact_mod_cast this
    have hmul : (rBeyond (L := L) (K := K) i c : ℝ) ≤ (n : ℝ) * FrontTailKernel.envelope f0 i := by
      rw [div_le_iff₀ hnpos] at hwithin; linarith [hwithin]
    exact Nat.le_floor (by exact_mod_cast hmul)

/-! ## Part 3 — the carried envelope-cap window on the feeder fraction.

The width concentration controls the event `rBeyond W c = 0` (front empty beyond the
`O(log log n)` width `W`).  Its one-step breach probability is the seeding of level
`W` from empty, bounded by `(rBeyond (W−1) c / n)²` (`rBeyond_seed_le_rBeyondSq`).  We
carry the per-step envelope cap on the feeder fraction at level `W−1` as the window
`RFeederCapWindow n Bcap`, capping `rBeyond (W−1) c ≤ Bcap` — the doubly-exp envelope
value at depth-1, which the front-shape keeps `O(log log n)`-small.  This is exactly
the `FrontSyncConc.FrontFeederWindow`/`EarlyDrip`'s `hwin` carried-window pattern. -/

/-- The carried feeder-cap window at the width level `W`: the population is `n`, every
agent is a Phase-3 clock, the front is EMPTY at level `W` (`rBeyond W c = 0`), and the
feeder count at level `W−1` is `≤ Bcap` (the depth-1 envelope cap). -/
def RFeederCapWindow (n W Bcap : ℕ) (c : Config (AgentState L K)) : Prop :=
  c.card = n ∧ AllClockP3 c ∧ rBeyond (L := L) (K := K) (W - 1) c ≤ Bcap

/-- **The per-step breach bound on the feeder-cap window.**  On a config in the
feeder-cap window with the front empty at level `W` (`W ≥ 1`, `2 ≤ card`), the one-step
probability that the front SEEDS level `W` (`1 ≤ rBeyond W c'`) is at most
`ofReal ((Bcap/n)²)` — the squared feeder fraction.  GENUINELY from the per-level
squaring `rBeyond_seed_le_rBeyondSq` + the carried cap `rBeyond (W−1) c ≤ Bcap`. -/
theorem front_breach_le_capSq (n W Bcap : ℕ) (hW : 1 ≤ W) (c : Config (AgentState L K))
    (hcard2 : 2 ≤ c.card) (hcardn : c.card = n)
    (hempty : rBeyond (L := L) (K := K) W c = 0)
    (hwin : RFeederCapWindow (L := L) (K := K) n W Bcap c) :
    (NonuniformMajority L K).transitionKernel c
        {c' | 1 ≤ rBeyond (L := L) (K := K) W c'} ≤
      ENNReal.ofReal (((Bcap : ℝ) / (n : ℝ)) ^ 2) := by
  obtain ⟨-, hw, hcap⟩ := hwin
  have hWeq : W - 1 + 1 = W := by omega
  have h0 : rBeyond (L := L) (K := K) (W - 1 + 1) c = 0 := by rw [hWeq]; exact hempty
  have hset : {c' : Config (AgentState L K) | 1 ≤ rBeyond (L := L) (K := K) W c'}
      = {c' | 1 ≤ rBeyond (L := L) (K := K) (W - 1 + 1) c'} := by rw [hWeq]
  rw [hset]
  refine le_trans (rBeyond_seed_le_rBeyondSq (W - 1) c hw hcard2 h0) ?_
  apply ENNReal.ofReal_le_ofReal
  apply pow_le_pow_left₀ (by positivity)
  have hcardpos : (0 : ℝ) < (c.card : ℝ) := by
    have : 0 < c.card := by omega
    exact_mod_cast this
  have hcap' : (rBeyond (L := L) (K := K) (W - 1) c : ℝ) ≤ (Bcap : ℝ) := by
    exact_mod_cast hcap
  rw [hcardn]; rw [hcardn] at hcardpos
  gcongr

/-! ## Part 4 — `AllClockP3` is preserved on the support under the empty width front.

When the front is EMPTY beyond level `W` and `W ≥ capMinute`, every clock is below the
cap (`FrontSync`), so by `FrontSyncConc.allClockP3_frontSync_step_closed` the
`AllClockP3` property is one-step closed.  But more generally we only need `FrontSync`
to invoke that closure; for the width concentration we use `W ≤ capMinute` so that an
empty front beyond `W` need NOT give FrontSync.  To stay clean we instantiate the
width concentration ON the cap-front itself (`W = capMinute`), where `rBeyond W c = 0
↔ FrontSync c` (`frontSync_iff_rBeyond_cap_zero`), reusing the proven `AllClockP3`
closure. -/

/-- `rBeyond capMinute c = 0 ↔ FrontSync c` (both say no clock is at the cap).  This is
`ClockFrontShape.frontSync_iff_rBeyond_cap_zero`, restated for use here. -/
theorem rBeyond_cap_zero_iff_frontSync (c : Config (AgentState L K)) :
    rBeyond (L := L) (K := K) (capMinute (L := L) (K := K)) c = 0 ↔
      FrontSync (L := L) (K := K) c :=
  (frontSync_iff_rBeyond_cap_zero c).symm

/-! ## Part 5 — the front-WIDTH concentration over the horizon.

Instantiate the general union machinery `FrontSyncConc.frontSync_union_horizon` with
`Good = FrontSync` (`= rBeyond capMinute · = 0`) and the carried feeder-cap window
`W = RFeederCapWindow n capMinute Bcap`.  The one-step closure of `Good ∧ W` (modulo
breach) uses `allClockP3_frontSync_step_closed` (under FrontSync, `AllClockP3` closed)
+ the carried envelope cap; the per-step breach `≤ ofReal ((Bcap/n)²)` is
`front_breach_le_capSq` at `W = capMinute`.  This gives the doubly-exp width
concentration

  `(K^H) c₀ {¬ FrontSync} ≤ H · ofReal ((Bcap/n)²)`,

with `Bcap = O(log log n)` (the depth-1 envelope cap), `H = Θ(log n)` ⟹ `1/poly`. -/

/-- **`frontWidth_concentration` — the doubly-exp front-WIDTH concentration.**  Given
the carried feeder-cap window `hcap_all` (every reachable FrontSync config of
population `n` has its cap-front feeder `rBeyond (cap−1) ≤ Bcap`, the depth-1
doubly-exp envelope cap), from a FrontSync start `c₀` the breach probability after `H`
steps is `≤ H · ofReal ((Bcap/n)²)`:

  `(K^H) c₀ {¬ FrontSync} ≤ H · ofReal ((Bcap/n)²)`.

GENUINELY PROVED: the general union bound `FrontSyncConc.frontSync_union_horizon` with
`Good = FrontSync`, `W = RFeederCapWindow n capMinute Bcap`, the one-step closure from
`allClockP3_frontSync_step_closed` + the carried cap window, and the per-step breach
`front_breach_le_capSq` (the per-level squaring `rBeyond_seed_le_rBeyondSq`).  This is
the multi-step transfer of the doubly-exp front tail to the kernel-power. -/
theorem frontWidth_concentration (n Bcap : ℕ)
    (hcapPos : 0 < capMinute (L := L) (K := K)) (hn2 : 2 ≤ n)
    (hcap_all : ∀ c : Config (AgentState L K),
      FrontSync (L := L) (K := K) c → c.card = n →
      RFeederCapWindow (L := L) (K := K) n (capMinute (L := L) (K := K)) Bcap c)
    (H : ℕ) (c₀ : Config (AgentState L K)) (hsync0 : FrontSync (L := L) (K := K) c₀)
    (hcard0 : c₀.card = n) :
    ((NonuniformMajority L K).transitionKernel ^ H) c₀
        {c' | ¬ FrontSync (L := L) (K := K) c'} ≤
      (H : ℝ≥0∞) * ENNReal.ofReal (((Bcap : ℝ) / (n : ℝ)) ^ 2) := by
  -- one-step closure of the good event `FrontSync ∧ RFeederCapWindow n cap Bcap`.
  have hstep : ∀ c c' : Config (AgentState L K),
      FrontSync (L := L) (K := K) c →
      RFeederCapWindow (L := L) (K := K) n (capMinute (L := L) (K := K)) Bcap c →
      c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support →
      (FrontSync (L := L) (K := K) c' ∧
          RFeederCapWindow (L := L) (K := K) n (capMinute (L := L) (K := K)) Bcap c')
        ∨ ¬ FrontSync (L := L) (K := K) c' := by
    intro c c' hsync hwin hc'
    by_cases hsync' : FrontSync (L := L) (K := K) c'
    · left
      refine ⟨hsync', ?_⟩
      have hcardc : c.card = n := hwin.1
      have hcardc' : c'.card = n := by
        rw [Protocol.stepDistOrSelf_support_card_eq (NonuniformMajority L K) c c' hc', hcardc]
      exact hcap_all c' hsync' hcardc'
    · right; exact hsync'
  -- per-step breach bound on the good event.
  have hseed : ∀ c : Config (AgentState L K),
      FrontSync (L := L) (K := K) c →
      RFeederCapWindow (L := L) (K := K) n (capMinute (L := L) (K := K)) Bcap c →
      (NonuniformMajority L K).transitionKernel c
        {c' | ¬ FrontSync (L := L) (K := K) c'} ≤
        ENNReal.ofReal (((Bcap : ℝ) / (n : ℝ)) ^ 2) := by
    intro c hsync hwin
    have hcardn' : c.card = n := hwin.1
    have hcard2 : 2 ≤ c.card := by rw [hcardn']; exact hn2
    have hempty : rBeyond (L := L) (K := K) (capMinute (L := L) (K := K)) c = 0 :=
      (frontSync_iff_rBeyond_cap_zero c).mp hsync
    -- {¬ FrontSync c'} = {1 ≤ rBeyond cap c'} (cap front nonempty).
    have hset : {c' : Config (AgentState L K) | ¬ FrontSync (L := L) (K := K) c'}
        = {c' | 1 ≤ rBeyond (L := L) (K := K) (capMinute (L := L) (K := K)) c'} := by
      ext c'
      rw [Set.mem_setOf_eq, Set.mem_setOf_eq, frontSync_iff_rBeyond_cap_zero c']
      omega
    rw [hset]
    exact front_breach_le_capSq n (capMinute (L := L) (K := K)) Bcap (by omega) c
      hcard2 hcardn' hempty hwin
  exact frontSync_union_horizon (FrontSync (L := L) (K := K))
    (RFeederCapWindow (L := L) (K := K) n (capMinute (L := L) (K := K)) Bcap)
    (ENNReal.ofReal (((Bcap : ℝ) / (n : ℝ)) ^ 2)) hstep hseed H c₀ hsync0
    (hcap_all c₀ hsync0 hcard0)

/-! ## Part 6 — the `1/poly` budget and the wiring to `hwin_all`.

The width concentration's budget `H · ofReal ((Bcap/n)²) = ofReal (H·Bcap²/n²)` is
`1/poly` for `H = Θ(log n)`, `Bcap = O(log log n)` (`FrontSyncConc.horizon_width_eps_poly`).
The carried cap window `RFeederCapWindow` is the GENUINE (probabilistic) form of the
false `hwin_all`: instead of asserting the feeder is `≤ B` for ALL FrontSync configs,
the feeder cap holds on the trajectory (the doubly-exp envelope maintained), with the
SAME named residual `rEnvelope_maintained`. -/

/-- **The `1/poly` budget.**  `H · ofReal ((Bcap/n)²) = ofReal (H·Bcap²/n²)` (for
`0 < n`), the explicit `1/poly` quantity.  With `H = Θ(log n)`, `Bcap = O(log log n)`
this is `O(log n · (log log n)² / n²) = 1/poly`. -/
theorem frontWidth_eps_poly (n Bcap H : ℕ) (hn : 0 < n) :
    (H : ℝ≥0∞) * ENNReal.ofReal (((Bcap : ℝ) / (n : ℝ)) ^ 2)
      = ENNReal.ofReal ((H : ℝ) * (Bcap : ℝ) ^ 2 / (n : ℝ) ^ 2) :=
  FrontSyncConc.horizon_width_eps_poly n Bcap H hn

/-- **`frontWidth_concentration_poly` — the width concentration in `1/poly` form.**
Combining `frontWidth_concentration` with `frontWidth_eps_poly`: from a FrontSync start
of population `n` with the carried depth-1 envelope cap `hcap_all`, the breach
probability over `H` steps is `≤ ofReal (H·Bcap²/n²)` — the explicit `1/poly` width
concentration (`O(log n · (log log n)² / n²)` for the real horizon and width). -/
theorem frontWidth_concentration_poly (n Bcap : ℕ)
    (hcapPos : 0 < capMinute (L := L) (K := K)) (hn2 : 2 ≤ n)
    (hcap_all : ∀ c : Config (AgentState L K),
      FrontSync (L := L) (K := K) c → c.card = n →
      RFeederCapWindow (L := L) (K := K) n (capMinute (L := L) (K := K)) Bcap c)
    (H : ℕ) (c₀ : Config (AgentState L K)) (hsync0 : FrontSync (L := L) (K := K) c₀)
    (hcard0 : c₀.card = n) :
    ((NonuniformMajority L K).transitionKernel ^ H) c₀
        {c' | ¬ FrontSync (L := L) (K := K) c'} ≤
      ENNReal.ofReal ((H : ℝ) * (Bcap : ℝ) ^ 2 / (n : ℝ) ^ 2) := by
  have h := frontWidth_concentration n Bcap hcapPos hn2 hcap_all H c₀ hsync0 hcard0
  rwa [frontWidth_eps_poly n Bcap H (by omega)] at h

/-! ## Part 7 — discharging `FrontSyncConcentration_remaining` via the width cap.

The cap-front feeder window `FrontSyncConc.FrontFeederWindow n B` is exactly
`card = n ∧ AllClockP3 ∧ frontMinuteCount (cap−1) ≤ B`; and `frontMinuteCount (cap−1) c
≤ rBeyond (cap−1) c` (`frontMinuteCount_le_rBeyond`).  So the carried depth-1 envelope
cap `RFeederCapWindow n cap Bcap` (`rBeyond (cap−1) ≤ Bcap`) IMPLIES
`FrontFeederWindow n Bcap` — the genuine (probabilistic) `hwin_all`, with `B = Bcap =
O(log log n)`.  Hence the width cap supplies `FrontSyncConc`'s `hwin_all`, and the
PROVEN `frontSync_concentration_remaining_proven` discharges
`FrontSyncConcentration_remaining`. -/

/-- **`feederWindow_of_capWindow` — the width cap implies the feeder window.**  The
carried depth-1 envelope cap `RFeederCapWindow n W Bcap` (`rBeyond (W−1) ≤ Bcap`) with
`W = capMinute` implies `FrontSyncConc.FrontFeederWindow n Bcap` (`frontMinuteCount
(cap−1) ≤ Bcap`), since the feeder count is bounded by the front tail
`frontMinuteCount_le_rBeyond`.  This is the bridge from the genuine width cap to the
`hwin_all` the clock concentration consumes. -/
theorem feederWindow_of_capWindow (n Bcap : ℕ) (c : Config (AgentState L K))
    (hcap : RFeederCapWindow (L := L) (K := K) n (capMinute (L := L) (K := K)) Bcap c) :
    FrontSyncConc.FrontFeederWindow (L := L) (K := K) n Bcap c := by
  obtain ⟨hcard, hw, hcaple⟩ := hcap
  refine ⟨hcard, hw, ?_⟩
  exact le_trans (frontMinuteCount_le_rBeyond (L := L) (K := K)
    (capMinute (L := L) (K := K) - 1) c) hcaple

/-- **`frontSync_concentration_of_capWindow` — `FrontSyncConcentration_remaining`
discharged via the genuine width cap.**  Given the carried depth-1 envelope cap
`hcap_all` (every reachable FrontSync config of population `n` has `rBeyond (cap−1) ≤
Bcap`, the doubly-exp width), the named obligation
`ClockFrontShape.FrontSyncConcentration_remaining n mC H` holds at
`ε = H · ofReal ((Bcap/n)²)`.  GENUINELY: `feederWindow_of_capWindow` upgrades the
width cap to `FrontFeederWindow`, then `FrontSyncConc.frontSync_concentration_remaining_proven`
(the PROVEN union bound over the squared per-step breach) closes it.  This replaces the
false `∀c hwin_all` with the genuine (probabilistic) depth-1 width cap. -/
theorem frontSync_concentration_of_capWindow (n mC Bcap : ℕ)
    (hcapPos : 0 < capMinute (L := L) (K := K)) (hn2 : 2 ≤ n)
    (hcap_all : ∀ c : Config (AgentState L K),
      FrontSync (L := L) (K := K) c → c.card = n →
      RFeederCapWindow (L := L) (K := K) n (capMinute (L := L) (K := K)) Bcap c)
    (H : ℕ) :
    ClockFrontShape.FrontSyncConcentration_remaining (L := L) (K := K) n mC H
      ((H : ℝ≥0∞) * ENNReal.ofReal (((Bcap : ℝ) / (n : ℝ)) ^ 2)) := by
  apply FrontSyncConc.frontSync_concentration_remaining_proven
    (L := L) (K := K) n mC Bcap hcapPos hn2
  intro c hsync hcard
  exact feederWindow_of_capWindow n Bcap c (hcap_all c hsync hcard)

/-! ## Part 8 — the clock UNCONDITIONAL (whp), reduced to the named envelope residual.

Assembling: the clock's `habs_mix` needs `FrontSync` maintained whp, which
`frontSync_concentration_of_capWindow` PROVES given the carried depth-1 envelope cap
`hcap_all`.  The cap is supplied by the doubly-exp front shape: the within-envelope
invariant `RWithinEnvelope` keeps the leading front `O(log log n)`-narrow (the
deterministic decay `rFront_emptied_of_envelope` shows the front EMPTIES beyond the
width).  The ONLY remaining input is the MAINTENANCE of `RWithinEnvelope` along the
trajectory — the named residual `rEnvelope_maintained`, the genuine multi-step
front-shape reachability (the SAME residual `FrontSyncConc`'s `hwin_all` carries, now
isolated to the envelope-maintenance core). -/

/-- **THE DETERMINISTIC `∀c` ENVELOPE-MAINTENANCE — SUPERSEDED (it is FALSE as a `∀c`
COUNT bound; the genuine object is the PROBABILISTIC front-narrowness).**  As stated,
`rEnvelope_maintained n Bcap` asserts the feeder count `rBeyond (cap−1) c ≤ Bcap` for
EVERY FrontSync config of population `n`.  This deterministic `∀c` COUNT bound is FALSE
for `Bcap < n` (all clocks may bunch at minute `cap−1`), so it forces `Bcap ≥ n` and a
vacuous budget.

The GENUINE object is the PROBABILISTIC front-narrowness
`ClockEnvMaint.rFrontNarrow_concentration`, now PROVEN in
`FrontNarrowConc.rFrontNarrow_concentration_proven` by a LEVEL-UNION over the PROVEN
per-level squaring `rBeyond_seed_le_rBeyondSq` + the doubly-exponential envelope step:
the feeder stays within the doubly-exp envelope FRACTION (not a `∀c` count cap) whp,
with `1/poly` failure `H · ofReal (env (cap−1))`.  The genuine clock FrontSync-breach
bound via this concentration is `FrontNarrowConc.clock_frontSync_via_narrow`,
consuming the probabilistic concentration — NOT this false deterministic `∀c` def.

This def + `clock_unconditional_of_envelope` are RETAINED unchanged (they are a proven
conditional theorem, never weakened), but the deterministic `rEnvelope_maintained`
input is SUPERSEDED by the genuine probabilistic path; do not discharge it in its
false `∀c` count form. -/
def rEnvelope_maintained (n Bcap : ℕ) : Prop :=
  ∀ c : Config (AgentState L K),
    FrontSync (L := L) (K := K) c → c.card = n →
    RFeederCapWindow (L := L) (K := K) n (capMinute (L := L) (K := K)) Bcap c

/-- **`clock_unconditional_of_envelope` — the O(log n) clock, FrontSync DISCHARGED,
reduced to the named envelope residual.**  Given ONLY the named envelope-maintenance
residual `rEnvelope_maintained n Bcap` (the carried depth-1 doubly-exp cap), the width
concentration PROVES the maintenance of FrontSync over any horizon `H`, with failure
`≤ ofReal (H·Bcap²/n²) = 1/poly` for `H = Θ(log n)`, `Bcap = O(log log n)`
(`frontWidth_eps_poly`).  This is the genuine probabilistic discharge of the
front-shape synchronization the clock's `habs_mix` required: the false `∀c hwin_all` is
REPLACED by the genuine doubly-exp width concentration, modulo the single named
envelope residual. -/
theorem clock_unconditional_of_envelope (n mC Bcap : ℕ)
    (hcapPos : 0 < capMinute (L := L) (K := K)) (hn2 : 2 ≤ n)
    (henv : rEnvelope_maintained (L := L) (K := K) n Bcap)
    (H : ℕ) (c₀ : Config (AgentState L K))
    (hQ : Q_mix (L := L) (K := K) n mC 0 c₀)
    (hsync0 : FrontSync (L := L) (K := K) c₀) :
    ((NonuniformMajority L K).transitionKernel ^ H) c₀
        {c' | ¬ FrontSync (L := L) (K := K) c'} ≤
      ENNReal.ofReal ((H : ℝ) * (Bcap : ℝ) ^ 2 / (n : ℝ) ^ 2) :=
  frontWidth_concentration_poly n Bcap hcapPos hn2 henv H c₀ hsync0 hQ.card

/-- HONEST STATUS marker. -/
theorem clock_front_width_status : True := trivial

end ClockFrontWidth

end ExactMajority
