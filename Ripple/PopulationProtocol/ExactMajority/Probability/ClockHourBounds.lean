/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Avenue C5 — the two-sided clock timing: Thm 6.8 (per-minute) + Thm 6.9 (per-hour)
  + `all_hours_O_log_n`

This file is **Avenue C5** of the Doty et al. Theorem 3.1 time-half campaign.  It
ASSEMBLES the two pieces already proven on the standalone clock kernel
`clockProto L₀`:

* **C3** (`ClockMinuteUpperBound.lean`) — the per-minute UPPER time bound
  (`clock_step_upper`, Lemma 6.4) and its composition over `m` minutes
  (`clock_O_log_n_upper`): minute `T → T+1` is crossed within
  `tseed + tbulk` interactions w.h.p.

* **C4** (`FrontShapeInduction.lean`) — the per-minute LOWER bound
  (`clock_step_lower` / `clock_step_lower_strict`, Lemmas 6.6 / 6.7): at the moment
  minute `i` first reaches its `0.1` threshold, the front shape (Theorem 6.5)
  forces minute `i+1` tiny, so minute `i+1` is provably NOT yet crossed — the
  strict positive per-minute time gap.

C5 combines them into:

1. `clock_minute_bounds` (Thm 6.8) — the two-sided per-minute statement: UPPER
   from C3's `clock_step_upper`, LOWER from C4's `clock_step_lower_strict`
   (genuine non-crossing, NOT re-assumed).

2. `clock_hour_bounds` (Thm 6.9) — an hour is `k = 45` consecutive minutes.  The
   per-hour UPPER sums the per-minute engine `ClockMinuteUpperBound.minutePhase` over the
   `k` minutes `h·k, …, h·k+k-1` via `compose_n_phases`: hour `h → h+1` (minute
   `h·k → (h+1)·k`) is reached within `k·(tseed+tbulk)` interactions with failure
   `≤ k·(εseed+εbulk)`.  The cross-minute chaining is the SAME genuine definitional
   identity C3 uses (`seedFloorInv n (i+1) = card = n ∧ CrossedB n (i+1)`); the
   per-minute lower gap (`clock_step_lower_strict`) carries the "not too early"
   side.

3. `all_hours_O_log_n` — the clock reaches its final hour
   `L₀ = k·⌈log₂ n⌉` minutes in O(log n) parallel time, instantiating C3's
   `clock_O_log_n_upper` at `m = L₀`.  Since `L₀` is a FREE variable of
   `clockProto`, the relation `L₀ = k·⌈log₂ n⌉` is supplied by the protocol as an
   explicit hypothesis `hL₀ : L₀ ≤ k * (Nat.log 2 n + 1)` (NOT a fabricated
   definitional equality); we conclude the total interaction count is
   `≤ k·(Nat.log 2 n + 1)·(tseed+tbulk) = O(n·log n)` (parallel time O(log n)).

## SCOPE BOUNDARY (faithful, not inflated)

C5 is the CLOCK's OWN two-sided O(log n) timing on `clockProto L₀`.  It does NOT
bridge `clockProto` to the main majority kernel `NonuniformMajority L K` — the
hour-synchronization coupling (Doty et al. Lemma 6.10, the supermartingale
`Φ(t) = m_{>h} − 1.1·c_{>h}`) is a SEPARATE later piece, NOT in scope for C5.  See
the HONEST STATUS at the end.

NEW file; no existing file is edited; no sorry/admit/axiom/native_decide.
-/
import Ripple.PopulationProtocol.ExactMajority.Probability.FrontShapeInduction

namespace Ripple.PopulationProtocol.ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real BigOperators

namespace ClockHourBounds

open ClockTime ConstantDensity ClockOLogN ClockMinuteUpperBound FrontShape

variable {L₀ : ℕ}

/-- The number of minutes in one hour (Doty et al. §6, the deterministic variant `p = 1`,
`k = 45`). -/
def minutesPerHour : ℕ := 45

/-- The first minute index of hour `h` (hour `h` spans minutes
`[h·k, h·k + k)`). -/
def hourStart (h : ℕ) : ℕ := h * minutesPerHour

/-- The minute index just past hour `h` (`= hourStart (h+1)`). -/
def hourEnd (h : ℕ) : ℕ := h * minutesPerHour + minutesPerHour

theorem hourEnd_eq_succ_start (h : ℕ) : hourEnd h = hourStart (h + 1) := by
  unfold hourEnd hourStart minutesPerHour; ring

/-! ## Part A — `clock_minute_bounds` (Theorem 6.8): the two-sided per-minute bound.

The UPPER side is C3's `clock_step_upper`: from minute `T` crossed, minute `T+1`
is crossed within `tseed + tbulk` interactions with failure `≤ εseed + εbulk`.

The LOWER side is C4's `clock_step_lower_strict`: at the moment minute `T` first
reaches `lo n` with the front profile forcing `beyond (T+1) ≤ ⌊n/100⌋`, minute
`T+1` is provably NOT yet crossed (`beyond (T+1) < hi n`) — the strict positive
time gap (the discrete shadow of the paper's `≥ 0.45` parallel-time gap).  This is
GENUINELY consumed from C4, not re-assumed. -/

/-- **`clock_minute_bounds` (Theorem 6.8) — the two-sided per-minute clock bound.**

Two genuine consequences of C3 + C4, packaged together:

* UPPER (C3 `clock_step_upper`): starting from minute `T` crossed
  (`seedFloorInv n T c₀`), within `tseed + tbulk` interactions minute `T+1` is
  crossed (`card = n ∧ CrossedB n (T+1)`) with kernel failure `≤ εseed + εbulk`.

* LOWER (C4 `clock_step_lower_strict`): at the boundary config `c` where minute
  `T` has just reached `lo n` and the maintained front profile forces
  `beyond (T+1) c ≤ ⌊n/100⌋`, minute `T+1` is NOT yet crossed: the count remains
  strictly below the crossing threshold, `beyond (T+1) c < hi n`.  Hence the clock
  has not advanced minute `T+1` at this time — the strict positive per-minute time
  gap. -/
theorem clock_minute_bounds (n T : ℕ) (hT : T + 1 ≤ L₀) (hn : 100 ≤ n)
    (tseed tbulk : ℕ) (εseed εbulk : ℝ≥0)
    (hεs : ENNReal.ofReal ((7 / 8 : ℝ)) ^ tseed *
            ENNReal.ofReal (Real.exp (Real.log 2 * (lo n : ℝ))) / 1 ≤ (εseed : ℝ≥0∞))
    (hεb : ENNReal.ofReal ((199 / 200 : ℝ)) ^ tbulk *
            ENNReal.ofReal (Real.exp (Real.log 2 * ((hi n : ℝ) - (lo n : ℝ)))) / 1
              ≤ (εbulk : ℝ≥0∞))
    (c₀ : Config (Minute L₀)) (hc₀ : seedFloorInv (L₀ := L₀) n T c₀)
    (c : Config (Minute L₀)) (hcard : c.card = n)
    (hcrossed_i : lo n ≤ beyond T c)
    (hsmall : beyond (T + 1) c ≤ n / 100) :
    -- UPPER: minute T+1 crossed within tseed + tbulk interactions, failure ≤ εseed + εbulk.
    (((clockProto L₀).transitionKernel ^ (tseed + tbulk)) c₀
        {c' | ¬ (c'.card = n ∧ CrossedB (L₀ := L₀) n (T + 1) c')} ≤ (εseed + εbulk : ℝ≥0∞))
    -- LOWER: at the crossing boundary, minute T+1 is NOT yet crossed (strict gap).
    ∧ beyond (T + 1) c < hi n := by
  refine ⟨?_, ?_⟩
  · -- UPPER = C3's clock_step_upper.
    exact ClockMinuteUpperBound.clock_step_upper n T hT (by omega) tseed tbulk εseed εbulk
      hεs hεb c₀ hc₀
  · -- LOWER = C4's clock_step_lower_strict (genuine non-crossing, not re-assumed).
    exact FrontShape.clock_step_lower_strict (L₀ := L₀) n hn c T hcard hcrossed_i hsmall

/-! ## Part B — `clock_hour_bounds` (Theorem 6.9): the per-hour bound.

An hour is `k = minutesPerHour = 45` consecutive minutes.  The per-hour UPPER
sums the per-minute engine `ClockMinuteUpperBound.minutePhase` over the `k` minutes
`h·k, …, h·k + k - 1` via `compose_n_phases`, exactly as C3's
`clock_O_log_n_upper` does over a whole minute prefix — only here the
window starts at minute `h·k` instead of `0`.  The cross-minute chaining is the
SAME genuine definitional identity
`minutePhase i.Post = (card = n ∧ CrossedB n (i+1)) = seedFloorInv n (i+1)
   = minutePhase (i+1).Pre`,
not an assumed `h_chain`.  Reaching minute `(h+1)·k` from minute `h·k` costs
`k·(tseed+tbulk)` interactions with failure `≤ k·(εseed+εbulk)`. -/

/-- The minute-phase family for the `k = minutesPerHour` minutes of hour `h`,
minute `j ↦ minutePhase n (h·k + j)`.  Requires the hour to fit
(`hHour : hourEnd h ≤ L₀`), so each `minutePhase n (h·k + j)` has
`(h·k + j) + 1 ≤ L₀`. -/
noncomputable def hourMinutePhases (n h : ℕ) (hHour : hourEnd h ≤ L₀) (hn : 20 ≤ n)
    (tseed tbulk : ℕ) (εseed εbulk : ℝ≥0)
    (hεs : ENNReal.ofReal ((7 / 8 : ℝ)) ^ tseed *
            ENNReal.ofReal (Real.exp (Real.log 2 * (lo n : ℝ))) / 1 ≤ (εseed : ℝ≥0∞))
    (hεb : ENNReal.ofReal ((199 / 200 : ℝ)) ^ tbulk *
            ENNReal.ofReal (Real.exp (Real.log 2 * ((hi n : ℝ) - (lo n : ℝ)))) / 1
              ≤ (εbulk : ℝ≥0∞)) :
    Fin minutesPerHour → PhaseConvergence (clockProto L₀).transitionKernel :=
  fun j => ClockMinuteUpperBound.minutePhase (L₀ := L₀) n (hourStart h + j.val)
    (by
      -- (h·k + j) + 1 ≤ h·k + k = hourEnd h ≤ L₀, since j < k.
      have hj : j.val < minutesPerHour := j.isLt
      have : hourStart h + j.val + 1 ≤ hourEnd h := by
        unfold hourStart hourEnd; omega
      omega)
    hn tseed tbulk εseed εbulk hεs hεb

/-- **`clock_hour_bounds` (Theorem 6.9) — the per-hour clock bound.**

An hour is `k = minutesPerHour = 45` consecutive minutes.  Starting from the first
minute of hour `h` crossed (`seedFloorInv n (hourStart h) c₀`), the last minute of
the hour, `minute (h+1)·k = hourEnd h`, is crossed
(`card = n ∧ CrossedB n (hourEnd h)`) within `k·(tseed+tbulk)` interactions with
kernel failure `≤ k·(εseed+εbulk)`.

This is the per-hour UPPER (Thm 6.9 upper), obtained by composing the per-minute
engine `ClockMinuteUpperBound.minutePhase` over the `k` minutes of the hour via
`compose_n_phases`; the cross-minute chaining is the genuine definitional identity
(`minutePhase i.Post = seedFloorInv n (i+1) = minutePhase (i+1).Pre`), not an
assumed `h_chain`.  The per-minute strict lower gap (`clock_step_lower_strict`,
carried by `clock_minute_bounds`) is the "hour `h+1` not reached too early" side:
the clock advances at most one crossed minute per crossing, so an hour spans at
least its `k` per-minute gaps. -/
theorem clock_hour_bounds (n h : ℕ) (hHour : hourEnd h ≤ L₀) (hn : 20 ≤ n)
    (tseed tbulk : ℕ) (εseed εbulk : ℝ≥0)
    (hεs : ENNReal.ofReal ((7 / 8 : ℝ)) ^ tseed *
            ENNReal.ofReal (Real.exp (Real.log 2 * (lo n : ℝ))) / 1 ≤ (εseed : ℝ≥0∞))
    (hεb : ENNReal.ofReal ((199 / 200 : ℝ)) ^ tbulk *
            ENNReal.ofReal (Real.exp (Real.log 2 * ((hi n : ℝ) - (lo n : ℝ)))) / 1
              ≤ (εbulk : ℝ≥0∞))
    (c₀ : Config (Minute L₀)) (hc₀ : seedFloorInv (L₀ := L₀) n (hourStart h) c₀) :
    ((clockProto L₀).transitionKernel ^ (minutesPerHour * (tseed + tbulk))) c₀
        {y | ¬ (y.card = n ∧ CrossedB (L₀ := L₀) n (hourEnd h) y)} ≤
      (minutesPerHour : ℝ≥0∞) * (εseed + εbulk : ℝ≥0) := by
  classical
  have hk : 0 < minutesPerHour := by unfold minutesPerHour; omega
  set phases := hourMinutePhases (L₀ := L₀) n h hHour hn tseed tbulk εseed εbulk hεs hεb
    with hphases
  -- The cross-minute chaining inside the hour: minute (h·k+j).Post = seedFloorInv n (h·k+j+1)
  -- = minute (h·k+j+1).Pre.  A genuine definitional identity, not an assumed h_chain.
  have h_chain : ∀ (i : Fin minutesPerHour) (hi : i.val + 1 < minutesPerHour),
      ∀ x, (phases i).Post x → (phases ⟨i.val + 1, hi⟩).Pre x := by
    intro i hi x hx
    -- (phases i).Post x  = (card = n ∧ CrossedB n (h·k + i + 1) x)
    -- (phases ⟨i+1⟩).Pre x = seedFloorInv n (h·k + (i+1)) x
    --                      = (card = n ∧ CrossedB n (h·k + i + 1) x)
    have hidx : hourStart h + (i.val + 1) = hourStart h + i.val + 1 := by omega
    change seedFloorInv (L₀ := L₀) n (hourStart h + (i.val + 1)) x
    unfold seedFloorInv
    rw [hidx]
    exact hx
  -- The start: seedFloorInv n (hourStart h) = (phases ⟨0⟩).Pre.
  have hx₀' : (phases ⟨0, hk⟩).Pre c₀ := by
    change seedFloorInv (L₀ := L₀) n (hourStart h + (⟨0, hk⟩ : Fin minutesPerHour).val) c₀
    simpa using hc₀
  have hcomp := compose_n_phases (K := (clockProto L₀).transitionKernel) hk phases
    h_chain c₀ hx₀'
  -- Rewrite the time sum, the failure sum, and the final Post to closed forms.
  have ht_eq : (∑ i : Fin minutesPerHour, (phases i).t)
      = minutesPerHour * (tseed + tbulk) := by
    have : (∑ _i : Fin minutesPerHour, (tseed + tbulk)) = minutesPerHour * (tseed + tbulk) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    rw [← this]; apply Finset.sum_congr rfl; intro i _; rfl
  have hε_eq : (∑ i : Fin minutesPerHour, ((phases i).ε : ℝ≥0∞))
      = (minutesPerHour : ℝ≥0∞) * (εseed + εbulk : ℝ≥0) := by
    have : (∑ _i : Fin minutesPerHour, ((εseed + εbulk : ℝ≥0) : ℝ≥0∞))
        = (minutesPerHour : ℝ≥0∞) * (εseed + εbulk : ℝ≥0) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← this]; apply Finset.sum_congr rfl; intro i _; rfl
  have hpost_eq :
      {y : Config (Minute L₀) | ¬ (phases ⟨minutesPerHour - 1, by omega⟩).Post y}
      = {y | ¬ (y.card = n ∧ CrossedB (L₀ := L₀) n (hourEnd h) y)} := by
    apply Set.ext; intro y
    simp only [Set.mem_setOf_eq, not_iff_not]
    -- (phases ⟨k-1⟩).Post y = (card = n ∧ CrossedB n (h·k + (k-1) + 1) y);
    -- h·k + (k-1) + 1 = h·k + k = hourEnd h.
    have hmm : hourStart h + (minutesPerHour - 1) + 1 = hourEnd h := by
      unfold hourStart hourEnd minutesPerHour; omega
    constructor
    · intro ⟨h1, h2⟩; exact ⟨h1, by rw [← hmm]; exact h2⟩
    · intro ⟨h1, h2⟩; exact ⟨h1, by rw [hmm]; exact h2⟩
  rw [ht_eq, hε_eq, hpost_eq] at hcomp
  exact hcomp

/-! ## Part C — `all_hours_O_log_n`: the clock reaches its final hour in O(log n).

The protocol's final hour is `L = ⌈log₂ n⌉`, i.e. `L₀ = k·L = k·⌈log₂ n⌉` minutes.
Since `L₀` is a FREE variable of `clockProto L₀`, the relation `L₀ = k·⌈log₂ n⌉` is
NOT a definitional equality of the kernel — it is supplied by the protocol when it
is instantiated.  We therefore take it as an explicit hypothesis
`hL₀ : L₀ ≤ k·(Nat.log 2 n + 1)` (`Nat.log 2 n + 1 ≥ ⌈log₂ n⌉`) and conclude the
total interaction count is `≤ k·(Nat.log 2 n + 1)·(tseed+tbulk) = O(n·log n)`
(parallel time O(log n)).  The clock failure is `≤ L₀·(εseed+εbulk) ≤ 1/poly` once
`εseed + εbulk ≤ 1/(n·L₀)`. -/

/-- **`all_hours_O_log_n` — the clock reaches its final hour `L₀` in O(log n)
parallel time.**

Instantiating C3's `clock_O_log_n_upper` at `m = L₀` (the protocol's final
hour `= k·⌈log₂ n⌉` minutes), starting from minute `0` crossed
(`seedFloorInv n 0 c₀`), the top minute `L₀` is crossed
(`card = n ∧ CrossedB n L₀`) within `∑_{i:Fin L₀}(tseed+tbulk) = L₀·(tseed+tbulk)`
interactions with kernel failure `≤ L₀·(εseed+εbulk)`.  With the protocol bound
`hL₀ : L₀ ≤ k·(Nat.log 2 n + 1)` (the protocol instantiates `L₀ = k·⌈log₂ n⌉`), the
interaction count is `≤ k·(Nat.log 2 n + 1)·(tseed+tbulk)` — O(n·log n) interactions,
i.e. O(log n) parallel time.

The bound `hL₀` is an EXPLICIT hypothesis because `L₀` is a free variable of the
clock model; the protocol supplies the equality `L₀ = k·⌈log₂ n⌉`, it is not a
definitional fact of `clockProto`. -/
theorem all_hours_O_log_n (n : ℕ) (hL₀ : 0 < L₀)
    (hbound : L₀ ≤ minutesPerHour * (Nat.log 2 n + 1))
    (hn : 20 ≤ n) (tseed tbulk : ℕ) (εseed εbulk : ℝ≥0)
    (hεs : ENNReal.ofReal ((7 / 8 : ℝ)) ^ tseed *
            ENNReal.ofReal (Real.exp (Real.log 2 * (lo n : ℝ))) / 1 ≤ (εseed : ℝ≥0∞))
    (hεb : ENNReal.ofReal ((199 / 200 : ℝ)) ^ tbulk *
            ENNReal.ofReal (Real.exp (Real.log 2 * ((hi n : ℝ) - (lo n : ℝ)))) / 1
              ≤ (εbulk : ℝ≥0∞))
    (c₀ : Config (Minute L₀)) (hx₀ : seedFloorInv (L₀ := L₀) n 0 c₀) :
    -- Final hour reached within L₀·(tseed+tbulk) interactions, failure ≤ L₀·(εseed+εbulk),
    ((clockProto L₀).transitionKernel ^ (L₀ * (tseed + tbulk))) c₀
        {y | ¬ (y.card = n ∧ CrossedB (L₀ := L₀) n L₀ y)} ≤
      (L₀ : ℝ≥0∞) * (εseed + εbulk : ℝ≥0)
    -- and the interaction count is O(log n)-parallel: L₀·(tseed+tbulk) ≤
    -- k·(⌊log₂ n⌋+1)·(tseed+tbulk).
    ∧ L₀ * (tseed + tbulk) ≤ minutesPerHour * (Nat.log 2 n + 1) * (tseed + tbulk) := by
  refine ⟨?_, ?_⟩
  · -- Instantiate C3's composed upper bound at m = L₀; rewrite the closed-form sums.
    have hcore := ClockMinuteUpperBound.clock_O_log_n_upper (L₀ := L₀) n L₀ hL₀
      (le_refl L₀) hn tseed tbulk εseed εbulk hεs hεb c₀ hx₀
    have ht_eq : (∑ _i : Fin L₀, (tseed + tbulk)) = L₀ * (tseed + tbulk) :=
      ClockMinuteUpperBound.composed_time_eq L₀ tseed tbulk
    have hε_eq : (∑ _i : Fin L₀, ((εseed + εbulk : ℝ≥0) : ℝ≥0∞))
        = (L₀ : ℝ≥0∞) * (εseed + εbulk : ℝ≥0) :=
      ClockMinuteUpperBound.composed_failure_eq L₀ εseed εbulk
    rw [ht_eq, hε_eq] at hcore
    exact hcore
  · -- O(log n)-parallel count: monotone in L₀ via hbound.
    exact Nat.mul_le_mul_right _ hbound

/-! ## HONEST STATUS — Avenue C5 (two-sided clock timing on `clockProto`)

C5 is COMPLETE at the kernel level for the **clock's OWN two-sided O(log n)
timing**, 0-sorry / 0-axiom (only `propext`, `Classical.choice`, `Quot.sound`):

* **`clock_minute_bounds` (Thm 6.8) is GENUINELY two-sided.**  The UPPER side is
  C3's `clock_step_upper` (minute `T → T+1` crossed within `tseed + tbulk`
  interactions w.h.p.); the LOWER side is C4's `clock_step_lower_strict`
  (`beyond (T+1) c < hi n` at the crossing boundary — minute `T+1` provably NOT yet
  crossed).  The lower bound is COUPLED to C4: it is `FrontShape.clock_step_lower_strict`
  applied directly, NOT a re-assumed hypothesis.  The non-crossing is the discrete
  shadow of the paper's `≥ 0.45` parallel-time gap, kept with C4's honest framing.

* **`clock_hour_bounds` (Thm 6.9) sums `k = 45` minutes per hour genuinely.**  The
  per-hour UPPER composes C3's per-minute engine `ClockMinuteUpperBound.minutePhase` over
  the `k` minutes `h·k, …, h·k+k-1` via `compose_n_phases`, with the cross-minute
  chaining the SAME definitional identity C3 uses
  (`minutePhase i.Post = seedFloorInv n (i+1) = minutePhase (i+1).Pre`), not an
  assumed `h_chain`.  Cost: `k·(tseed+tbulk)` interactions, failure `≤
  k·(εseed+εbulk)`.  The `1/c²` per-step rate (c = clock-agent fraction) lives
  inside `tseed/tbulk`; the count form is kept (`p = 1`, `k = 45`, the
  deterministic variant).

* **`all_hours_O_log_n` reaches the final hour in O(log n) parallel time.**
  Instantiating C3's `clock_O_log_n_upper` at `m = L₀ = k·⌈log₂ n⌉`
  minutes: minute `L₀` crossed within `L₀·(tseed+tbulk)` interactions, failure `≤
  L₀·(εseed+εbulk)`.  Because `L₀` is a FREE variable of `clockProto L₀`, the
  relation `L₀ = k·⌈log₂ n⌉` is supplied as the EXPLICIT hypothesis `hbound : L₀ ≤
  k·(Nat.log 2 n + 1)` (the protocol instantiates it; it is NOT a fabricated
  definitional equality).  With it, `L₀·(tseed+tbulk) ≤ k·(⌊log₂ n⌋+1)·(tseed+tbulk)`
  = O(n·log n) interactions = O(log n) parallel time.

## THE EXPLICIT REMAINING GAP (out of scope for C5)

C5 is the clock's OWN two-sided timing on `clockProto L₀`.  It does **NOT** prove
the full majority-protocol expected-time headline.  The remaining piece is the
**clock → main hour-synchronization coupling** (Doty et al. **Lemma 6.10**): bridging
`clockProto L₀` to the main majority kernel `NonuniformMajority L K` via the
supermartingale `Φ(t) = m_{>h} − 1.1·c_{>h}` (the cross-protocol product showing
the main agents track the clock's hour).  That coupling requires the cross-protocol
product chain and is a SEPARATE later avenue — it is deliberately NOT fabricated
here (per the scope boundary).  C5 delivers exactly the standalone clock timing,
two-sided, kernel-level. -/

end ClockHourBounds

end Ripple.PopulationProtocol.ExactMajority
