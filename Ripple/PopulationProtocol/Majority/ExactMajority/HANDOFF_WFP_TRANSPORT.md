# HANDOFF: within-window WFP transport (family letter, task 2e1d56f0, 2026-06-10)

Source: ChatGPT Pro (family, Ripple connector on opus-wip). Delivered 10,459 B
via the NETWORK path (first full E2E WS delivery — bridge v10.28.6). Verbatim below.

---

## STATUS (2026-06-10, opus implementation — `Probability/WidthTransport.lean`)

**Implemented, 0-sorry, axiom-clean (`⊆ [propext, Classical.choice, Quot.sound]`), single-file
`lake env lean` EXIT_0. Two commits.**

| Stage | Lemma (in `WidthTransport.lean`) | Status |
|-------|----------------------------------|--------|
| 1 | `ClockFrontProfile.climbN_chain_le` — t-step support-chain additive front bound (`climbN k c ≤ climbN k c₀ + n` along any `AllClockP3`-window chain), lifting `ClimbTail.climbN_le_succ_on_support` | ✅ proven |
| 1 | `ClockFrontProfile.ae_allClockGE3_pow` — absorbing-window a.e. preservation | ✅ proven |
| 2 | `CrossEmptyClimbGood` + `goodFrontWidth_of_checkpoint_profile_climb_transport` — profile/climb→width transport at widened margin `W₁+W₂+W₃` | ✅ proven |
| 2b | `goodFrontWidth_transport_of_width` — the cleaner checkpoint-`GoodFrontWidth W` → endpoint-`GoodFrontWidth (W+W₃)` transport (matches the `widthFail_chk` event directly) | ✅ proven |
| 3 | `CrossEmptyClimbBad` + `crossEmptyClimb_whp` — finite union of `ClimbTail.climb_real_tail` over `k < Tcap` | ✅ proven |
| 4 | `ae_rBeyond_ge_pow` — iterated within-window `rBeyond` monotone over `r` steps (the `hmono` feeder) | ✅ proven |
| 4 | `widthFail_between_checkpoints` — generic CK reduction (`checkpoint_side_le` at `t=w·j`, `r`) | ✅ proven |
| 4 | `widthFail_between_checkpoints_concrete` — consumer demo: `Entry = {WidthSideP→GoodFrontWidth(W₁+W₂)}`, so `Entryᶜ` = `widthFail_chk`'s event, `εBad` discharged by `CrossHourSide.widthFail_chk_concrete` (= `εWAt_chk`), tail carried as `hTail` (hLocal-shaped) | ✅ proven |

### Blueprint citations verified against the branch
All cited lemmas exist with matching signatures: `transition_p3_minute_le_succ_max`,
`climbN_le_succ_on_support`, `climb_real_tail`, `climbGate`, `climbPot` (`ClimbTail.lean`);
`GoodFrontWidth`, `WindowedFrontProfile`, `ClimbBound`, `goodFrontWidth_of_windowed_profile_and_climb`,
`windowed_floor_crossing` (`ClockFrontProfile.lean`); `rBeyondGE3_ge_monotone`, `AllClockGE3_absorbing`
(`ClockRealKernel.lean`); `rBeyond_antitone_threshold` (`HabsDischarge.lean`); `frontWidthBound`
(`FrontTailDecay.lean`); `climbBound_whp`/`climbBound_bad_subset` (`EarlyDripMarked.lean`).
The deterministic claim (only the equal-minute DRIP branch raises the global max, by +1; SYNC copies
the max) was verified directly in `transition_p3_minute_le_succ_max`'s proof. **No wrong citation.**

### Recorded discrepancies (blueprint vs. faithful Lean)
1. **`CrossEmptyClimbGood` bulk test.** Blueprint wrote `rBeyond k c₁ < n/10` (Nat floor division).
   That is NOT equivalent to the codebase-faithful cardinality form `10·rBeyond k c₁ < n` (e.g.
   `n=15, x=1`: `10<15` true but `1 < 1` false) and using it breaks the floor contradiction in
   Stage 2. We state `CrossEmptyClimbGood` with `10·rBeyond k c₁ < n`, the exact negation of the
   `GoodFrontWidth` conjunct it must contradict.
2. **Stage-4 RHS shape.** The blueprint's flattened RHS re-bases the climb sum at `erase mc₀` over
   `r` steps. That is NOT provable: Chapman–Kolmogorov yields the within-window tail integrated
   against the *checkpoint distribution* `(realκ^{w·j}) (erase mc₀)`, which does not collapse to a
   single start-config climb sum. The honest assembly exposes the tail as the **per-checkpoint-state**
   obligation `hTail` (matching `CrossHourSide.hside_concrete_bounded`'s `hLocal` interface).

### Residual to fully close the per-state tail `hTail` (the one remaining wiring)
`endpoint_widthFail_tail_le`: for a checkpoint-good `y` (scalar `GoodFrontWidth W`, `AllClockGE3`,
`card=n`), bound `(realκ^r) y {WidthSideP ∧ ¬GoodFrontWidth(W+W₃)} ≤ crossEmptyClimb_whp(y,r)`.
The mechanism is: a.e. over `(realκ^r) y`, the endpoint `c'` has `AllClockGE3 c'` and
`rBeyond T y ≤ rBeyond T c'` (`ae_rBeyond_ge_pow`); then `goodFrontWidth_transport_of_width` makes
`¬GoodFrontWidth(W+W₃) c'` force `¬CrossEmptyClimbGood y.card W₃ y c'`, i.e. a `CrossEmptyClimbBad`
witness. **The remaining bridge is the threshold form:** the transport's `CrossEmptyClimbGood` test is
the cardinality form `10·rBeyond k c' < n` (Doty's `0.1n` bulk floor), while `crossEmptyClimb_whp`'s
engine `climb_real_tail` gates on `rBeyond k c' < θn` for a fixed value `θn`. Closing it requires
either instantiating the engine at `θn := n/10` AND reconciling `10·x < n` vs `x < n/10` (Nat
division), or adding a cardinality-form variant of `climb_real_tail`/`climbGate`. This is the single
named residual; everything upstream and downstream of it is proven.

---

## 1. Deterministic route: yes for scalar front speed, no for profile transport

A single interaction can make an **individual** clock jump many minutes by SYNC: in `Phase3Transition`, if two clocks have unequal minutes, both outputs get `max s.minute t.minute`. But that SYNC branch does **not** raise the global maximum. The only branch that can raise the global max is the equal-minute DRIP branch, and it raises by exactly one; the synced-at-cap branch runs the counter subroutine and keeps the minute. fileciteturn44file right per-pair bound:

```lean
theorem transition_p3_minute_le_succ_max (s t : AgentState L K)
    (hsc : s.role = .clock) (htc : t.role = .clock)
    (hs3 : s.phase.val = 3) (ht3 : t.phase.val = 3) :
    (Transition L K s t).1.minute.val ≤ max s.minute.val t.minute.val + 1 ∧
      (Transition L K s t).2.minute.val ≤ max s.minute.val t.minute.val + 1
```

and the already-packaged support-level version:

```lean
theorem climbN_le_succ_on_support (k : ℕ) (c c' : Config (AgentState L K))
    (hw : AllClockP3 (L := L) (K := K) c)
    (hsupp : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    climbN (L := L) (K := K) k c' ≤ climbN (L := L) (K := K) k c + 1
```

fileciteturn61file0L30-L39 fileciterBeyondGE3_ge_monotone` says fixed-threshold cumulative counts do not decrease on one-step support over `AllClockGE3`. fileciteturn54file0L144-L160

But the deterministic `+θn` widening is **not enough** for the actual side consumers. `GoodFrontWidth W` is not a generic “width ≤ w” assertion; the same `W` is consumed in the cap-band test `capMinute - W` inside `frontSync_whp_of_goodFrontWidth`. fileciteturn56file0L111-L121 The current checkpoint side consumer feeds `sidePrefix_le_assembled` with can move **scalar width**, but adding an interaction-count-sized `θn = n^(3/5)` to a minute-width `W = O(log log n)` is dimensionally and mathematically wrong for the cap-band bridge.

`WindowedFrontProfile` also does **not** transport deterministically. It is a same-config recurrence

```lean
def WindowedFrontProfile (θ : ℝ) (c : Config (AgentState L K)) : Prop :=
  ∀ T : ℕ, θ ≤ frac (L := L) (K := K) T c → frac (L := L) (K := K) T c ≤ 1 / 10 →
    frac (L := L) (K := K) (T + 1) c ≤ (frac (L := L) (K := K) T c) ^ 2
```

and monotonicity/shift does not preserve the adjacent-tail squaring inequality.  within-window transport

Use `ClimbTail.climb_real_tail`, not bare `GatedEscape`.

`ClimbTail` already proves the exact type of event needed: while a lower level has not reached a threshold, the front cannot climb `W₂` levels above it except by paying an escape term plus an MGF tail. Its capstone is:

```lean
theorem climb_real_tail (n k B' θn W₂ : ℕ) (hW₂ : 2 ≤ W₂)
    (s : ℝ) (hs : 0 ≤ s) (t : ℕ) (c₀ : Config (AgentState L K)) :
    ((NonuniformMajority L K).transitionKernel ^ t) c₀
        {c | rBeyond (L := L) (K := K) k c < θn ∧
          0 < rBeyond (L := L) (K := K) (k + W₂) c} ≤
      (GatedDrift.killK ((NonuniformMajority L K).transitionKernel)
          (climbGate (L := L) (K := K) n k B' θn) ^ t) (some c₀) {none} +
        (ENNReal.ofReal (1 + ((B' : ℝ) / (n : ℝ)) ^ 2 * (Real.exp s - 1))) ^ t *
          climbPot (L := L) (K := K) k θn s c₀ /
          ENNReal.ofReal (Real.exp (s * ((W₂ : ℝ) - 1)))
```

fileciteturn60file0L70-L79

For this transport, instantiate `θn := n / 10`, because failure of `GoodFrontWidth` is exactly a failure of the `0.1` bulk threshold to be close enough to the front:

```lean
def GoodFrontWidth (W : ℕ) (c : Config (AgentState L K)) : Prop :=
  ∀ i : ℕ, 0 < rBeyond (L := L) (K := K) i c →
    c.card ≤ 10 * rBeyond (L := L) (K := K) (i - W) c
```

filecite the missing event is not “front advances ≤ θn/2” as a raw deterministic count; it is:

> every checkpoint-empty level stays empty `W₃` levels above any endpoint level whose bulk count is still below `n/10`.

That is exactly a finite union of `climb_real_tail`.

---

## 3. Target lemma signatures

### A. Deterministic cross-config transport

```lean
namespace ExactMajority
namespace ClockFrontProfile

open ClockRealKernel

variable {L K : ℕ}

/-- Cross-window empty-level transport: an empty level at checkpoint `c₀`
cannot have a nonempty `W₃`-higher level at endpoint `c₁` unless the
`0.1` bulk threshold has reached the original empty level. -/
def CrossEmptyClimbGood
    (n W₃ : ℕ) (c₀ c₁ : Config (AgentState L K)) : Prop :=
  ∀ k : ℕ,
    rBeyond (L := L) (K := K) k c₀ = 0 →
    rBeyond (L := L) (K := K) k c₁ < n / 10 →
    rBeyond (L := L) (K := K) (k + W₃) c₁ = 0

/-- Checkpoint `WindowedFrontProfile` + checkpoint `ClimbBound` + within-window
empty-climb transport imply endpoint scalar `GoodFrontWidth`.

This avoids transporting `WindowedFrontProfile` itself. -/
theorem goodFrontWidth_of_checkpoint_profile_climb_transport
    (θ : ℝ) (W₂ W₃ : ℕ)
    (c₀ c₁ : Config (AgentState L K))
    (hcard : c₁.card = c₀.card)
    (hcard2 : 2 ≤ c₀.card)
    (hall₀ : AllClockP3 (L := L) (K := K) c₀)
    (hall₁ : AllClockP3 (L := L) (K := K) c₁)
    (hθ : 1 / (c₀.card : ℝ) ≤ θ)
    (hmono : ∀ T,
      rBeyond (L := L) (K := K) T c₀ ≤
      rBeyond (L := L) (K := K) T c₁)
    (hwp₀ : WindowedFrontProfile (L := L) (K := K) θ c₀)
    (hclimb₀ : ClimbBound (L := L) (K := K) θ W₂ c₀)
    (hcross : CrossEmptyClimbGood (L := L) (K := K) c₀.card W₃ c₀ c₁) :
    GoodFrontWidth (L := L) (K := K)
      (FrontTail.frontWidthBound c₀.card + W₂ + W₃) c₁
```

Proof skeleton: copy the structure of `goodFrontWidth_of_windowed_profile_and_climb`. Use `FrontTail.windowed_floor_crossing` at the checkpoint, then checkpoint `ClimbBound` to empty a level, then `CrossEmptyClimbGood` to preserve that emptiness up to `W₃`, and finally `HabsDischarge.rBeyond_antitone_threshold` to contradict endpoint nonemptiness. The existing proof already uses `rBeyond_antitone_threshold` in this final way. fileciteturn40file0L3-L7

### B. Probabilistic finite-union transport

```lean
namespace ExactMajority
namespace EarlyDripMarked

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real BigOperators Classical

variable {L K : ℕ}

/-- The bad event for within-window transport: some checkpoint-empty level `k`
is still below the `0.1n` bulk threshold at the endpoint, but level `k+W₃`
has become nonempty. -/
def CrossEmptyClimbBad
    (n W₃ Tcap : ℕ) (c₀ : Config (AgentState L K)) :
    Set (Config (AgentState L K)) :=
  {c | ∃ k < Tcap,
    rBeyond (L := L) (K := K) k c₀ = 0 ∧
    rBeyond (L := L) (K := K) k c < n / 10 ∧
    0 < rBeyond (L := L) (K := K) (k + W₃) c}

/-- Within-window empty-level climb transport, by unioning `ClimbTail.climb_real_tail`
over levels `k < Tcap`, with the climb threshold instantiated as `n/10`. -/
theorem crossEmptyClimb_whp
    (n W₃ Tcap B' r : ℕ) (hW₃ : 2 ≤ W₃)
    (s : ℝ) (hs : 0 ≤ s)
    (c₀ : Config (AgentState L K)) :
    ((NonuniformMajority L K).transitionKernel ^ r) c₀
        (CrossEmptyClimbBad (L := L) (K := K) n W₃ Tcap c₀)
      ≤
    ∑ k ∈ Finset.range Tcap,
      ((GatedDrift.killK ((NonuniformMajority L K).transitionKernel)
          (ClimbTail.climbGate (L := L) (K := K) n k B' (n / 10)) ^ r)
          (some c₀) {none}
       +
       (ENNReal.ofReal
          (1 + ((B' : ℝ) / (n : ℝ)) ^ 2 * (Real.exp s - 1))) ^ r
        * ClimbTail.climbPot (L := L) (K := K) k (n / 10) s c₀
        / ENNReal.ofReal (Real.exp (s * ((W₃ : ℝ) - 1))))
```

Proof skeleton: show `CrossEmptyClimbBad` is contained in the finite union over `k < Tcap` of `{c | rBeyond k c < n/10 ∧ 0 < rBeyond (k+W₃) c}`; apply `measure_biUnion_finset_le`; each summand is exactly `ClimbTail.climb_real_tail` with `θn := n / 10`.

### C. Final free-time width feeder

```lean
namespace ExactMajority
namespace EarlyDripMarked

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real BigOperators Classical

variable {L K : ℕ}

/-- Free-time width feeder between checkpoints:
checkpoint WFP/climb failure plus within-window transport failure.

This removes the coarse `δRem := 1` term by not trying to prove
`WindowedFrontProfile` at the free endpoint. -/
theorem widthFail_between_checkpoints_concrete
    (n : ℕ) (hn : DotyParams.N₀ ≤ n)
    (mc₀ : Config (MarkedAgent L K))
    (hcard : mc₀.card = n)
    (hge3 : AllClockGE3 (L := L) (K := K)
      (eraseConfig (L := L) (K := K) mc₀))
    (hnotP3 : ¬ AllClockP3 (L := L) (K := K)
      (eraseConfig (L := L) (K := K) mc₀))
    (hclean : ∀ m ∈ mc₀, m.2 = false)
    (Tcap : ℕ) (hcap : ClockFrontShape.capMinute (L := L) (K := K) < Tcap)
    (W₂ W₃ : ℕ) (hW₂ : 2 ≤ W₂) (hW₃ : 2 ≤ W₃)
    (B' : ℕ) (s : ℝ) (hs : 0 ≤ s)
    (j r : ℕ) (hjKK : j ≤ DotyParams.KK L K - 1)
    (hr : r < DotyParams.w n) :
    (ClockKilledMinute.realκ L K ^ (DotyParams.w n * j + r))
        (eraseConfig (L := L) (K := K) mc₀)
        {c | ClockBudgets.WidthSideP (L := L) (K := K) n c ∧
          ¬ GoodFrontWidth (L := L) (K := K)
            (FrontTail.frontWidthBound n + W₂ + W₃) c}
      ≤
      εWAt_chk (L := L) (K := K) n mc₀ Tcap W₂ B' s j
      +
      ∑ k ∈ Finset.range Tcap,
        ((GatedDrift.killK ((NonuniformMajority L K).transitionKernel)
            (ClimbTail.climbGate (L := L) (K := K)
              n k B' (n / 10)) ^ r)
            (some (eraseConfig (L := L) (K := K) mc₀)) {none}
         +
         (ENNReal.ofReal
            (1 + ((B' : ℝ) / (n : ℝ)) ^ 2 * (Real.exp s - 1))) ^ r
          * ClimbTail.climbPot (L := L) (K := K)
              k (n / 10) s
              (eraseConfig (L := L) (K := K) mc₀)
          / ENNReal.ofReal (Real.exp (s * ((W₃ : ℝ) - 1))))
```

Proof skeleton: use Chapman–Kolmogorov at `DotyParams.w n * j` plus remainder `r`; split checkpoint-good and checkpoint-bad. The checkpoint-bad part is `widthFail_chk_concrete`, hence `εWAt_chk`. On checkpoint-good states, use `goodFrontWidth_of_checkpoint_profile_climb_transport`; the failure of its `CrossEmptyClimbGood` hypothesis is bounded by `crossEmptyClimb_whp`.

The monotonicity lemma needed for `hmono` is present as `rBeyondGE3_ge_monotone`; support closure for the all-clock ≥3 window is present as `AllClockGE3_absorbing`. filecite minimal new machinery is exactly:

1. `CrossEmptyClimbGood` plus deterministic `goodFrontWidth_of_checkpoint_profile_climb_transport`.
2. `CrossEmptyClimbBad` plus finite-union wrapper `crossEmptyClimb_whp`.
3. The CK assembly `widthFail_between_checkpoints_concrete`.

No deterministic transport of `WindowedFrontProfile` should be attempted.

## Status (2026-06-10, post-cutoff bookkeeping)

- [x] All 4 stages DONE in Probability/WidthTransport.lean (commits a95dff31 Stage 1–3,
      498dfec0 Stage 4), 0-sorry per file header, built single-file before each commit.
      The agent was cut by the usage limit AFTER the Stage-4 commit, before this record.
- Blueprint discrepancy recorded in-file: the `< n/10` Nat-division bulk test is NOT
  equivalent to the codebase-faithful `10·rBeyond < n` form; the latter is used.
- NOTE: the final #print axioms sweep was not reported by the cut agent — fold into the
  Phase-F audit pass.
