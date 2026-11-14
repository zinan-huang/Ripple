/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `ClockFrontMixed` — the MIXED clock-normalized Layer-A front geometry (Doctrine Round 6)

The existing §6 clock front machinery (`ClockFrontProfile`, `ClockFrontSyncFromWidth`)
is written for the ALL-CLOCK abstract model: it normalizes the cumulative tail by
`c.card` (the full population) and assumes `AllClockP3 c` (EVERY agent is a phase-3
clock).  `AllClockP3` is FALSE in the real mixed protocol (Main/Reserve agents coexist),
so reusing those bridges unchanged makes the proof inapplicable — or silently an
all-clock theorem.  (Hole 1 of the Round-5 adversarial red-team.)

This file is the MIXED re-statement: normalize by `C₀ = clockCount c` (the number of
clock-role agents, `ClockRealMixed.clockCount`) and gate by `ClockP3 c` (only the
CLOCK agents are phase-3 — strictly WEAKER than `AllClockP3`).  The deterministic
arithmetic is the SAME card→C₀ mechanical swap of the proven card-normalized lemmas;
the abstract real-sequence machinery (`FrontTail.*`) is denominator-agnostic and reused
as-is.

## What is proven here (Stage 1, Layer-A geometry + the constant theorem)

* `layerB_constants_ok` — the standalone numeric checkpoint `γ·((9/10)a²+b) ≤ 9/10`
  for the working w=0.09 constant set (a=213/250, b=19/200, γ=6/5).  This is the
  Round-4 constant verdict pinned as a Lean theorem (Hole 6: never refer to the stale
  `(1+2/n)^Lwin` line; use this dedicated theorem).
* `rBeyond_zero_eq_C₀` — `rBeyond 0 c = C₀` (every clock minute is `≥ 0`, so `rBeyond 0`
  counts ALL clocks = `clockCount`).  Does NOT need `ClockP3` (a clock is at minute `≥ 0`
  unconditionally).  This is the mixed replacement for the card-version
  (`rBeyond 0 c = c.card` via `AllClockP3`).
* `rBeyond_eq_zero_of_clockGoodWidth_of_bulk_below` — the general level-`i` emptiness
  from the mixed width invariant: same proof as
  `ClockFrontSyncFromWidth.rBeyond_eq_zero_of_goodWidth_of_bulk_below`, card→C₀.
* `frontSync_of_clockGoodWidth_of_bulk_below` — the cap-safety FrontSync (`i = capMinute`
  instance), via `frontSync_iff_rBeyond_cap_zero`.  CAP-SAFETY uses the bulk BELOW the
  top band (`10·rBeyond(cap−W) < C₀`), the Round-6 corrected condition.

No `sorry` / `admit` / `axiom` / `native_decide`.
-/

import Ripple.PopulationProtocol.ExactMajority.Probability.ClockFrontSyncFromWidth

namespace Ripple.PopulationProtocol.ExactMajority

namespace ClockFrontMixed

open ClockRealKernel ClockRealMixed ClockFrontShape

variable {L K : ℕ}

/-! ## Part 0 — the Layer-B constant checkpoint (Hole 6)

The Round-4 constant verdict: the paper triple `(a,b,γ) = (0.84, 0.11, 1.23)` FAILS the
Layer-B contraction (`γ·(0.9a²+b) ≈ 0.9164 > 0.9`).  The window-in-clock-pair-time fix
gives the SAFE set `w = 9/100`, `a = 213/250`, `b = 19/200`, `γ = 6/5`, for which
`γ·((9/10)a²+b) = 350772/390625 = 0.89798... < 9/10`.  Pin it as a standalone numeric
lemma so the rest of the build never re-derives (or mis-remembers) the constants. -/

/-- **The Layer-B contraction constants are valid (w = 0.09 set).**  With the working
constant triple `a = 213/250`, `b = 19/200`, `γ = 6/5` (the clock-pair-time corrected
set), the contraction `γ·((9/10)·a² + b) ≤ 9/10` holds.  Proven by `norm_num`. -/
theorem layerB_constants_ok :
    (6 / 5 : ℝ) * ((9 / 10) * (213 / 250) ^ 2 + 19 / 200) ≤ 9 / 10 := by
  norm_num

/-! ## Part 1 — the MIXED definitions (clock-normalized by `C₀`, gated by `ClockP3`)

`ClockP3 c` constrains ONLY the clock-role agents to phase 3 — strictly WEAKER than
`AllClockP3` (which also forces every agent to be a clock).  `ClockFrac C₀ T c` and
`ClockGoodFrontWidth C₀ W c` are the card→C₀ restatements of `ClockFrontProfile.frac`
and `ClockFrontProfile.GoodFrontWidth`. -/

/-- **The mixed phase-3 clock window.**  Only the CLOCK-role agents are pinned to phase
exactly 3; Main/Reserve agents are unconstrained.  Strictly weaker than `AllClockP3`. -/
def ClockP3 (c : Config (AgentState L K)) : Prop :=
  ∀ a ∈ c, a.role = .clock → a.phase.val = 3

/-- **The clock-normalized cumulative tail fraction** `rBeyond T c / C₀` (Doty et al.'s `c_{≥i}`,
normalized by the clock population `C₀` rather than the full population `card`). -/
noncomputable def ClockFrac (C₀ T : ℕ) (c : Config (AgentState L K)) : ℝ :=
  (rBeyond (L := L) (K := K) T c : ℝ) / (C₀ : ℝ)

/-- **The mixed moving-frame width invariant** (clock-normalized).  The leading front is
never more than `W` minutes ahead of the `0.1` (clock-)bulk threshold:
`0 < rBeyond i c → C₀ ≤ 10 · rBeyond (i − W) c`.  This is `ClockFrontProfile.GoodFrontWidth`
with `card` replaced by `C₀ = clockCount`. -/
def ClockGoodFrontWidth (C₀ W : ℕ) (c : Config (AgentState L K)) : Prop :=
  ∀ i : ℕ, 0 < rBeyond (L := L) (K := K) i c →
    (C₀ : ℕ) ≤ 10 * rBeyond (L := L) (K := K) (i - W) c

/-! ## Part 2 — `rBeyond 0 c = C₀` (every clock minute is `≥ 0`)

The mixed replacement for the card-version `rBeyond 0 c = c.card` (which used
`AllClockP3`).  Here `rBeyond 0` counts clocks at minute `≥ 0` = ALL clocks =
`clockCount c`; no phase hypothesis is needed (a clock is at minute `≥ 0`
unconditionally). -/

/-- **`rBeyond 0 c = C₀`.**  `rBeyond 0` counts clock-role agents at minute `≥ 0`, which
is EVERY clock (every minute is `≥ 0`), so it equals `clockCount c = C₀`.  Does NOT need
`ClockP3` — a clock is at minute `≥ 0` regardless of phase. -/
theorem rBeyond_zero_eq_C₀ (C₀ : ℕ) (c : Config (AgentState L K))
    (hC₀ : clockCount (L := L) (K := K) c = C₀) :
    rBeyond (L := L) (K := K) 0 c = C₀ := by
  rw [← hC₀]
  unfold rBeyond clockCount
  apply Multiset.countP_congr rfl
  intro a _
  -- clockBeyondP 0 a = (a.role = .clock ∧ 0 ≤ a.minute.val) ⟺ a.role = .clock
  simp only [clockBeyondP, Nat.zero_le, and_true]

/-! ## Part 3 — the mixed level-emptiness + FrontSync from the mixed width invariant

These are the card→C₀ restatements of
`ClockFrontSyncFromWidth.rBeyond_eq_zero_of_goodWidth_of_bulk_below` and the
`i = capMinute` cap-safety, with `c.card` replaced by `C₀`. -/

/-- **General level emptiness (mixed).**  On the mixed good-width event, if the `0.1`
clock-bulk threshold has not reached within `W` minutes of level `i`
(`10·rBeyond(i−W) < C₀`), then level `i` and above are EMPTY.  SAME proof as the
card-version, card→C₀. -/
theorem rBeyond_eq_zero_of_clockGoodWidth_of_bulk_below
    (C₀ W i : ℕ) (c : Config (AgentState L K))
    (hgood : ClockGoodFrontWidth (L := L) (K := K) C₀ W c)
    (hbulk : 10 * rBeyond (L := L) (K := K) (i - W) c < C₀) :
    rBeyond (L := L) (K := K) i c = 0 := by
  by_contra h
  have hpos : 0 < rBeyond (L := L) (K := K) i c := Nat.pos_of_ne_zero h
  have hw := hgood i hpos
  omega

/-- **Cap-safety FrontSync (mixed).**  The `i = capMinute` instance: if the clock-bulk
has not reached within `W` minutes of the cap (`10·rBeyond(capMinute−W) < C₀`), then the
cap is empty, i.e. `FrontSync c`.  The Round-6 corrected cap-safety condition (bulk BELOW
the top band, NOT `capMinute ≤ bulkIdx + width`).  Via `frontSync_iff_rBeyond_cap_zero`
+ `rBeyond_eq_zero_of_clockGoodWidth_of_bulk_below`. -/
theorem frontSync_of_clockGoodWidth_of_bulk_below
    (C₀ W : ℕ) (c : Config (AgentState L K))
    (hgood : ClockGoodFrontWidth (L := L) (K := K) C₀ W c)
    (hbulk : 10 * rBeyond (L := L) (K := K)
        (capMinute (L := L) (K := K) - W) c < C₀) :
    FrontSync (L := L) (K := K) c := by
  rw [frontSync_iff_rBeyond_cap_zero]
  exact rBeyond_eq_zero_of_clockGoodWidth_of_bulk_below C₀ W
    (capMinute (L := L) (K := K)) c hgood hbulk

/-! ## Part 4 — the mixed windowed collapse `ClockGoodFrontWidth ⟸ Windowed ∧ Climb`

The faithful Theorem-6.5 reduction, clock-normalized.  Mechanically the same as
`ClockFrontProfile.goodFrontWidth_of_windowed_profile_and_climb` (card→C₀), reusing the
denominator-agnostic abstract `FrontTail.windowed_floor_crossing` and the threshold
antitonicity `MixedWindowClosure.rBeyond_antitone_threshold`.  The only mixed-specific input is
`rBeyond_zero_eq_C₀` (replacing `rBeyond 0 = card` via `AllClockP3`); the population
positivity is supplied by `0 < C₀` rather than `2 ≤ card`. -/

/-- **The mixed windowed Theorem-6.5 recurrence** (clock-normalized, worst case `p = 1`):
the squaring holds at every level whose clock-tail fraction sits in `[θ, 1/10]`. -/
def ClockWindowedFrontProfile (C₀ : ℕ) (θ : ℝ) (c : Config (AgentState L K)) : Prop :=
  ∀ T : ℕ, θ ≤ ClockFrac (L := L) (K := K) C₀ T c →
    ClockFrac (L := L) (K := K) C₀ T c ≤ 1 / 10 →
    ClockFrac (L := L) (K := K) C₀ (T + 1) c ≤ (ClockFrac (L := L) (K := K) C₀ T c) ^ 2

/-- **The mixed climb bound** (clock-normalized sub-floor half): no level `W₂` or more
above a sub-floor level (`ClockFrac k < θ`) carries any clock. -/
def ClockClimbBound (C₀ : ℕ) (θ : ℝ) (W₂ : ℕ) (c : Config (AgentState L K)) : Prop :=
  ∀ k : ℕ, ClockFrac (L := L) (K := K) C₀ k c < θ →
    rBeyond (L := L) (K := K) (k + W₂) c = 0

/-- **`ClockGoodFrontWidth` from the mixed windowed pair.**  On the mixed clock window
with floor `θ ≥ 1/C₀` and `0 < C₀`, the windowed recurrence collapses the clock profile
from any subcritical start (`< 1/10`) to below the floor within
`W₁ = frontWidthBound C₀` levels (`FrontTail.windowed_floor_crossing`), and the climb
bound empties everything `W₂` levels further up — yielding the mixed moving-frame width
invariant at width `W₁ + W₂`.  The card→C₀ restatement of
`ClockFrontProfile.goodFrontWidth_of_windowed_profile_and_climb`. -/
theorem clockGoodFrontWidth_of_windowed_profile_and_climb_mixed
    (C₀ : ℕ) (θ : ℝ) (W₂ : ℕ) (c : Config (AgentState L K))
    (hC₀card : clockCount (L := L) (K := K) c = C₀) (hC₀ : 2 ≤ C₀)
    (hθ : 1 / (C₀ : ℝ) ≤ θ)
    (hwp : ClockWindowedFrontProfile (L := L) (K := K) C₀ θ c)
    (hcb : ClockClimbBound (L := L) (K := K) C₀ θ W₂ c) :
    ClockGoodFrontWidth (L := L) (K := K) C₀
      (FrontTail.frontWidthBound C₀ + W₂) c := by
  have hC₀pos : 0 < C₀ := by omega
  have hC₀ℝ : (0 : ℝ) < (C₀ : ℝ) := by exact_mod_cast hC₀pos
  set W₁ := FrontTail.frontWidthBound C₀ with hW₁
  intro i hi
  by_cases hiW : i ≤ W₁ + W₂
  · -- i ≤ W₁ + W₂ ⟹ i − (W₁+W₂) = 0 ⟹ rBeyond 0 c = C₀.
    have hzero : i - (W₁ + W₂) = 0 := by omega
    rw [hzero, rBeyond_zero_eq_C₀ C₀ c hC₀card]; omega
  · by_contra hcon
    rw [not_le] at hcon  -- 10 * rBeyond (i − (W₁+W₂)) c < C₀
    set base := i - (W₁ + W₂) with hbase
    set f : ℕ → ℝ := fun j => ClockFrac (L := L) (K := K) C₀ (base + j) c with hfdef
    have hfnn : ∀ j, 0 ≤ f j := by
      intro j; simp only [hfdef, ClockFrac]; positivity
    have hrec : ∀ j, θ ≤ f j → f j ≤ 1 / 10 → f (j + 1) ≤ (f j) ^ 2 := by
      intro j hlo hhi
      simp only [hfdef] at hlo hhi ⊢
      have h := hwp (base + j) hlo hhi
      rwa [show base + (j + 1) = (base + j) + 1 from by ring]
    have hf0 : f 0 ≤ 1 / 10 := by
      simp only [hfdef, Nat.add_zero, ClockFrac]
      rw [div_le_iff₀ hC₀ℝ]
      have : (10 : ℝ) * (rBeyond (L := L) (K := K) base c : ℝ) < (C₀ : ℝ) := by
        exact_mod_cast hcon
      linarith
    -- The windowed collapse must cross the floor within W₁ levels.
    obtain ⟨j₀, hj₀le, hj₀⟩ :=
      FrontTail.windowed_floor_crossing hfnn hrec hf0 C₀ hC₀ hθ
    simp only [hfdef] at hj₀
    -- The climb bound then empties level base + j₀ + W₂ ≤ i; rBeyond is antitone.
    have hclimb := hcb (base + j₀) hj₀
    have hle : base + j₀ + W₂ ≤ i := by omega
    have hanti := MixedWindowClosure.rBeyond_antitone_threshold (L := L) (K := K)
      (base + j₀ + W₂) i hle c
    omega

end ClockFrontMixed

end Ripple.PopulationProtocol.ExactMajority
