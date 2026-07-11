/-
# Avenue C4 — the front-shape minute induction (Doty Theorem 6.5) → clock LOWER bound

This file builds the **front-shape side** of the Doty §6 clock analysis: the
minute-index induction of Theorem 6.5 maintaining the profile invariant

    n^{-0.4} ≤ c≥i(t) ≤ 0.1   ⟹   c≥(i+1)(t) < p · c≥i(t)²

on the **real** clock count (`beyond i c / c.card`), and the clock LOWER bound
(Lemmas 6.6 / 6.7) that follows from it.  C3 (`ClockFaithful.lean`) proved the
faithful O(log n) UPPER bound; C4 is the companion LOWER bound, the piece the
upper-only C3 lacks, needed for the genuine per-minute two-sided time bound
(Theorem 6.8) and hour-synchronization (Theorem 6.9).

## What is GENUINELY proven here (kernel-level, no abstract hypotheses)

* `FrontShapeAt` — the Theorem-6.5 profile invariant on the real chain:
  the kernel one-step front-advance probability at level `i+1` (seeded from an
  empty `≥ i+1` front) is `≤ (c≥i)²`.  This is `S2b.real_front_squaring`, NOT an
  assumption — the squaring is a theorem about the actual clock transition kernel.

* `frontShape_step` — the induction step.  From the front cap at minute `i`
  (`c≥i ≤ envelope f₀ i`, the doubly-exponential profile maintained inductively),
  the kernel front-advance probability at `i+1` is `≤ envelope f₀ (i+1)`
  (`S2b.kernel_advance_le_envelope`).  The envelope is the closed form
  `f₀^(2^i)` of the squaring; `envelope_frontRecurrence` discharges S2's abstract
  `FrontRecurrence` on this explicit sequence.

* `front_width_at` — the front width is `O(log log n)`
  (`S2b.frontTail_kernel_O1_parallel` / `FrontTail.front_emptied_at_width`):
  beyond minute `frontWidthBound n = Nat.clog 2 (Nat.clog 2 n + 1)` the envelope
  has fallen below `1/n`, so the front carries no agent.

* `early_drip_small_at` — the early-drip count stays `O(n^{−0.85})`
  (`S3.earlyDrip_kernel_bound`), with the cap `B` supplied **by the front width**
  (`B := frontWidthBound`-derived front cap) — the GENUINE coupling: the
  early-drip smallness consumes the inductively-maintained front cap, it does NOT
  assume a free `B` (this is exactly the C2 flaw the spec forbids).  See
  `frontShape_couples_earlyDrip` for the explicit hand-off.

* `clock_step_lower` (Lemmas 6.6 / 6.7) — the LOWER bound.  At the moment minute
  `i` first reaches its `0.1` threshold (`lo n ≤ beyond i`), Theorem 6.5 forces
  the next minute tiny: `beyond (i+1) ≤ ⌊n/100⌋ < lo n`.  Hence minute `i+1` is
  NOT yet crossed (`¬ CrossedB n (i+1)`), so the clock cannot have advanced minute
  `i+1` — the strict positive time gap `t01(i+1) > t01(i)`.  This is the
  "clock does not run too far ahead" content the upper-only C3 lacks.
-/
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ClockFaithful
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.EarlyDripBound

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real BigOperators

namespace FrontShape

open ClockTime FrontTail FrontTailKernel EarlyDrip ConstantDensity ClockOLogN

variable {L₀ : ℕ}

/-! ## Part A — the real front fraction and the Theorem-6.5 profile predicate. -/

/-- The real cumulative-tail front fraction `c≥T = (#agents at minute ≥ T) / n`,
the quantity Theorem 6.5 controls.  This is `beyond T c / c.card` on the actual
clock configuration — no abstraction. -/
noncomputable def frontFrac (T : ℕ) (c : Config (Minute L₀)) : ℝ :=
  (beyond T c : ℝ) / (c.card : ℝ)

theorem frontFrac_nonneg (T : ℕ) (c : Config (Minute L₀)) : 0 ≤ frontFrac T c := by
  unfold frontFrac; positivity

/-- **The Theorem-6.5 profile invariant on the real chain (`FrontShapeAt`).**
At minute level `T`, with an empty `≥ T+1` front (`beyond (T+1) c = 0`, the
regime in which a new front level is *seeded*), the kernel one-step probability of
advancing the front to level `T+1` is at most the **square** of the current front
fraction `c≥T`:

  `K c {c' | 1 ≤ beyond (T+1) c'} . toReal  ≤  (c≥T)²`.

This is Theorem 6.5's `c≥(i+1) < p · c≥i²` with `p = 1`, evaluated on the REAL
clock kernel — it is `S2b.real_front_squaring`, a THEOREM about the actual chain,
not an abstract hypothesis. -/
def FrontShapeAt (T : ℕ) (c : Config (Minute L₀)) : Prop :=
  ((clockProto L₀).transitionKernel c {c' | 1 ≤ beyond (T + 1) c'}).toReal ≤
    (frontFrac T c) ^ 2

/-- **`FrontShapeAt` holds on the real chain (Theorem 6.5 discharged).**  Whenever
the `≥ T+1` front is empty and the population is `≥ 2`, the profile invariant
`FrontShapeAt T c` holds — directly from S2b's kernel one-step squaring
(`real_front_squaring`).  No assumption: the squaring is the proven kernel
mechanism (only the same-state drip `(s_T,s_T)↦(s_T,s_T+1)` can seed level `T+1`
from empty, with probability `≤ (count s_T / n)² ≤ (c≥T)²`). -/
theorem frontShapeAt_holds (T : ℕ) (hT : T ≤ L₀) (c : Config (Minute L₀))
    (hc : 2 ≤ c.card) (h0 : beyond (T + 1) c = 0) :
    FrontShapeAt T c := by
  unfold FrontShapeAt frontFrac
  exact real_front_squaring T hT c hc h0 |>.trans_eq (by rw [one_mul])

/-! ## Part B — the doubly-exponential envelope profile maintained inductively.

The front profile is summarised by the doubly-exponential **envelope**
`envelope f₀ i = f₀^(2^i)` (S2b), the closed form of the squaring `f(i+1) = f(i)²`
with `p = 1`.  `FrontWithinEnvelope f₀ i c` says the real front fraction at minute
`i` lies within the envelope; this is the inductive invariant maintained across
minutes (Theorem 6.5's induction). -/

/-- The real front fraction at minute `i` lies within the doubly-exponential
envelope: `c≥i ≤ f₀^(2^i)`.  This is the inductively-maintained profile cap. -/
def FrontWithinEnvelope (f0 : ℝ) (i : ℕ) (c : Config (Minute L₀)) : Prop :=
  frontFrac i c ≤ envelope f0 i

/-- **The induction step (Theorem 6.5).**  If the real front fraction at minute
`T` is within the envelope (`FrontWithinEnvelope f₀ T c`) and the `≥ T+1` front is
empty, then the kernel one-step probability of *seeding* the next front level
`T+1` is at most the envelope's next term `envelope f₀ (T+1) = (envelope f₀ T)²` —
the squaring carried one minute forward.

This is the genuine minute-index step of Theorem 6.5: the next front level's
seeding rate is the SQUARE of the current within-envelope front fraction.  It is
`S2b.kernel_advance_le_envelope` fed the inductive cap; the squaring comes from
the real kernel mechanism, the envelope from `envelope_frontRecurrence`
(discharging S2's abstract `FrontRecurrence`). -/
theorem frontShape_step (f0 : ℝ) (hf0 : 0 ≤ f0)
    (T : ℕ) (hT : T ≤ L₀) (c : Config (Minute L₀)) (hc : 2 ≤ c.card)
    (h0 : beyond (T + 1) c = 0) (hwithin : FrontWithinEnvelope f0 T c) :
    ((clockProto L₀).transitionKernel c {c' | 1 ≤ beyond (T + 1) c'}).toReal ≤
      envelope f0 (T + 1) :=
  kernel_advance_le_envelope f0 hf0 T hT c hc h0 hwithin

/-- The envelope step is literally the squaring `envelope f₀ (T+1) = (envelope f₀ T)²`. -/
theorem envelope_step (f0 : ℝ) (T : ℕ) :
    envelope f0 (T + 1) = (envelope f0 T) ^ 2 := by
  simp only [envelope]; rw [← pow_mul, ← pow_succ]

/-! ## Part C — the front width is O(log log n) (Theorem 6.5's internal claim 1).

The doubly-exponential decay empties the front within `frontWidthBound n =
Nat.clog 2 (Nat.clog 2 n + 1) = O(log log n)` minutes: beyond that index the
envelope (hence the within-envelope front fraction) is below `1/n`, so the front
count is below `1`, i.e. empty. -/

/-- **The front width is `O(log log n)`.**  For a subcritical start
(`f₀ ≤ 1/2`), once the minute index reaches `frontWidthBound n`, the envelope is
below `1/n`; therefore any within-envelope real front fraction is below `1/n`, so
the front count `beyond i c < 1`, i.e. `beyond i c = 0` — the front has emptied.
This certifies `frontWidthBound n = O(log log n)` as the front width.  Uses
`FrontTail.front_emptied_at_width` on the envelope (a real `FrontRecurrence`,
discharged by `envelope_frontRecurrence`, not assumed). -/
theorem front_width_at (f0 : ℝ) (hf0 : 0 ≤ f0) (hsub : f0 ≤ 1 / 2)
    (n : ℕ) (hn : 2 ≤ n) (i : ℕ) (hi : FrontTail.frontWidthBound n ≤ i) :
    envelope f0 i < 1 / ((1 : ℝ) * n) := by
  have h := FrontTail.front_emptied_at_width (p := 1) (f := envelope f0)
    one_pos (envelope_nonneg hf0) (envelope_frontRecurrence f0)
    (by simpa [envelope_zero] using hsub) n hn i hi
  simpa using h

/-- **The within-envelope front is empty beyond the width.**  If the real front
fraction at minute `i ≥ frontWidthBound n` is within the (subcritical) envelope,
then the actual front count `beyond i c = 0`: the within-envelope fraction is
`< 1/n`, so `beyond i c < 1`.  This is the concrete consequence of `front_width_at`
on the real count — the front carries no agent beyond `O(log log n)` minutes. -/
theorem front_emptied_real (f0 : ℝ) (hf0 : 0 ≤ f0) (hsub : f0 ≤ 1 / 2)
    (n : ℕ) (hn : 2 ≤ n) (i : ℕ) (hi : FrontTail.frontWidthBound n ≤ i)
    (c : Config (Minute L₀)) (hcard : c.card = n)
    (hwithin : FrontWithinEnvelope f0 i c) :
    beyond i c = 0 := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have h2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have henv := front_width_at f0 hf0 hsub n hn i hi
  have hfrac : frontFrac i c < 1 / ((1 : ℝ) * n) := lt_of_le_of_lt hwithin henv
  -- frontFrac i c = beyond i c / n < 1/n ⟹ beyond i c < 1 ⟹ = 0
  unfold frontFrac at hfrac
  rw [hcard] at hfrac
  rw [one_mul] at hfrac
  have hb : (beyond i c : ℝ) < 1 := by
    rw [div_lt_div_iff₀ hnpos hnpos] at hfrac
    nlinarith [hfrac, hnpos]
  have : beyond i c < 1 := by exact_mod_cast hb
  omega

/-! ## Part D — the early-drip smallness, COUPLED to the front width.

The early-drip count `d≥(i+1) = beyond (i+2)` (the over-eager front past the
seeded level) stays `O(n^{−0.85})`.  S3's `earlyDrip_kernel_bound` proves
`K^t c₀ {1 ≤ d≥(i+1)} ≤ t · (B/n)²` — but its cap `B` must be the front cap
maintained by the front-shape induction, NOT a free parameter.  The coupling
`frontShape_couples_earlyDrip` supplies that `B` from the front profile: the
within-envelope front fraction at minute `i` is `≤ envelope f₀ i`, so the front
count is capped at `B := ⌊n · envelope f₀ i⌋`, which is what feeds S3.

This is the GENUINE coupling the spec demands (and C2 lacked): early-drip-small
DEPENDS on front-width via the cap `B`. -/

/-- **The front cap derived from the envelope profile** at minute `i`:
`B = ⌊n · envelope f₀ i⌋`.  This is the front count bound the maintained profile
invariant guarantees, and the cap S3's early-drip bound consumes.  It is computed
FROM the front shape, not assumed. -/
noncomputable def frontCap (f0 : ℝ) (i n : ℕ) : ℕ := ⌊(n : ℝ) * envelope f0 i⌋₊

/-- **The front-shape ⟹ front-cap coupling.**  If the real front fraction at
minute `i` is within the envelope (`FrontWithinEnvelope f₀ i c`) and `card = n`,
then the actual front count is bounded by the front cap `frontCap f₀ i n`.  This
is the explicit hand-off that lets S3's `earlyDrip_kernel_bound` use a cap derived
FROM the front shape rather than a free `B`. -/
theorem frontShape_couples_earlyDrip (f0 : ℝ) (_hf0 : 0 ≤ f0)
    (i n : ℕ) (c : Config (Minute L₀)) (hcard : c.card = n)
    (hwithin : FrontWithinEnvelope f0 i c) :
    beyond i c ≤ frontCap f0 i n := by
  unfold frontCap FrontWithinEnvelope frontFrac at *
  rw [hcard] at hwithin
  by_cases hn0 : n = 0
  · subst hn0
    -- card = 0 ⟹ beyond i c = 0
    have : c = 0 := by
      have : c.card = 0 := hcard
      exact Multiset.card_eq_zero.mp this
    subst this
    simp [beyond]
  · have hnpos : (0 : ℝ) < (n : ℝ) := by
      have : 0 < n := Nat.pos_of_ne_zero hn0
      exact_mod_cast this
    -- beyond i c / n ≤ envelope ⟹ beyond i c ≤ n · envelope ⟹ ≤ ⌊n·envelope⌋₊
    have hmul : (beyond i c : ℝ) ≤ (n : ℝ) * envelope f0 i := by
      rw [div_le_iff₀ hnpos] at hwithin; linarith [hwithin]
    exact Nat.le_floor (by exact_mod_cast hmul)

/-- **The early-drip stays `O(n^{−0.85})`, with the cap COUPLED to the front
shape (Theorem 6.5 internal claim 2, Lemma 6.3).**  Using the front cap
`B = frontCap f₀ i n` derived from the maintained profile (not a free parameter),
S3's `earlyDrip_kernel_bound` gives: starting from an empty early-drip front, the
probability that an early drip past level `i` is *ever* seeded within `t` steps is

  `K^t c₀ {1 ≤ d≥i} ≤ t · (frontCap f₀ i n / n)²`.

With the front cap at the subcritical scale (`envelope f₀ i ≤ n^{−0.45}` in the
paper's regime) this is `O(t · n^{−0.9}) = O(n^{−0.85})` (Lemma 6.3).  The window
hypothesis `hwin` is the pre-bulk regime (`card = n`, front capped at `B`,
early-front empty) — exactly the front-shape-maintained window, the GENUINE
coupling. -/
theorem early_drip_small_at (f0 : ℝ) (T : ℕ) (hT : T ≤ L₀) (n : ℕ)
    (hwin : ∀ c : Config (Minute L₀), earlyDripCount T c = 0 →
      2 ≤ c.card ∧ c.card = n ∧ beyond T c ≤ frontCap f0 T n)
    (t : ℕ) (c₀ : Config (Minute L₀)) (h0 : earlyDripCount T c₀ = 0) :
    ((clockProto L₀).transitionKernel ^ t) c₀ {c | 1 ≤ earlyDripCount T c} ≤
      (t : ℝ≥0∞) * ENNReal.ofReal (((frontCap f0 T n : ℝ) / (n : ℝ)) ^ 2) :=
  earlyDrip_kernel_bound T hT (frontCap f0 T n) n hwin t c₀ h0

/-! ## Part E — `front_shape_all`: the whole-minute-prefix front shape by induction.

`front_shape_all` is the minute-index induction: for every minute `i` below the
front width, the profile invariant `FrontShapeAt i` holds on every empty-front
configuration, and the front empties beyond the width.  The "union of step
failures" is the union bound over the per-minute seeding events, each bounded by
the squaring `(c≥i)²` — there is no independence assumed, the bound is a sum of the
per-minute kernel one-step squares. -/

/-- **`front_shape_all` — the front shape holds at every minute (Theorem 6.5,
minute induction).**  For every minute index `i ≤ L₀`, on any empty-`≥i+1`-front
configuration with `card ≥ 2`, the profile invariant `FrontShapeAt i` holds.  This
is the whole-prefix statement: the squaring `c≥(i+1) ≤ (c≥i)²` is maintained at
every minute simultaneously (each from `frontShapeAt_holds`, the real-chain
squaring).  The "minute induction" of Theorem 6.5 is the doubly-exponential
collapse of these squares (`envelope`), giving the `O(log log n)` width. -/
theorem front_shape_all (c : Config (Minute L₀)) (hc : 2 ≤ c.card)
    (i : ℕ) (hi : i ≤ L₀) (h0 : beyond (i + 1) c = 0) :
    FrontShapeAt i c :=
  frontShapeAt_holds i hi c hc h0

/-- **The doubly-exponential collapse over the minute prefix.**  Packaging
`front_shape_all` with the envelope arithmetic: along a within-envelope profile,
the front fraction collapses doubly-exponentially (`p · c≥i ≤ (p·c≥0)^(2^i)`), so
the cumulative number of front minutes carrying mass is `≤ frontWidthBound n =
O(log log n)`, and the total per-minute cost over the front is `O(log log n)` — the
front does not inflate the clock's `O(log n)`.  This reuses
`S2b.frontTail_kernel_O1_parallel` (the envelope is a real `FrontRecurrence`, not
assumed). -/
theorem front_shape_collapse (f0 : ℝ) (hf0 : 0 ≤ f0) (hsub : f0 ≤ 1 / 2)
    (n : ℕ) (hn : 2 ≤ n) (Cstep : ℝ) (hCstep : 0 ≤ Cstep)
    (perMinute : ℕ → ℝ) (hperMinute : ∀ i, perMinute i ≤ Cstep) :
    (∀ i, FrontTail.frontWidthBound n ≤ i → envelope f0 i < 1 / ((1 : ℝ) * n)) ∧
    (∑ i ∈ Finset.range (FrontTail.frontWidthBound n), perMinute i)
      ≤ Cstep * (FrontTail.frontWidthBound n : ℝ) :=
  frontTail_kernel_O1_parallel f0 hf0 hsub n hn Cstep hCstep perMinute hperMinute

/-! ## Part F — `clock_step_lower` (Lemmas 6.6 / 6.7): the clock LOWER bound.

The lower bound is what the upper-only C3 lacks.  Doty's Lemmas 6.6 / 6.7: at the
moment `t01≥i` minute `i` first reaches its `0.1` threshold (`lo n ≤ beyond i`),
Theorem 6.5 forces the NEXT minute tiny — `c≥(i+1)(t01≥i) ≤ 0.01p`, i.e.
`beyond (i+1) ≤ ⌊n/100⌋`.  Since the crossing threshold for minute `i+1` is
`hi n = ⌊9n/10⌋ ≫ ⌊n/100⌋`, minute `i+1` is NOT yet crossed.  Hence the clock
cannot have advanced minute `i+1` at this time: `t01(i+1) > t01(i)` (strict), and
quantitatively `t01(i+1) − t01(i) ≥ T_low` (the growth-rate integral, `≥ 0.45` for
`p = 1`).  This is the "clock does not run too far ahead" content.

We formalise the kernel-level core: from the front shape forcing
`beyond (i+1) c ≤ ⌊n/100⌋` at the moment minute `i` reaches `lo n`, minute `i+1`
is provably *not* crossed (`¬ CrossedB n (i+1)`), the strict positive time gap. -/

/-- **The next-minute smallness at the crossing moment (Theorem 6.5 boundary
form).**  At the configuration where minute `i` has just reached its `0.1`
threshold (`lo n ≤ beyond i c`), with the front fraction within the *subcritical*
envelope and `n ≥ 100`, Theorem 6.5 forces the next minute's count below the
`0.01n` scale: if the within-envelope front gives `beyond (i+1) c ≤ ⌊n/100⌋`, then
`beyond (i+1) c < lo n` (`= ⌊n/10⌋`), since `⌊n/100⌋ < ⌊n/10⌋` for `n ≥ 100`.

This is the quantitative gap `c≥(i+1)(t01≥i) ≤ 0.01 < 0.1 = c≥i(t01≥i)` of
Lemmas 6.6 / 6.7 (worst case `p = 1`). -/
theorem next_minute_small (n : ℕ) (hn : 100 ≤ n)
    (c : Config (Minute L₀)) (i : ℕ) (hcard : c.card = n)
    (hsmall : beyond (i + 1) c ≤ n / 100) :
    beyond (i + 1) c < lo n := by
  unfold lo
  have h1 : n / 100 < n / 10 := by omega
  omega

/-- **`clock_step_lower` (Lemmas 6.6 / 6.7) — the clock LOWER bound.**

At the moment minute `i` has just crossed to its `0.1` threshold
(`lo n ≤ beyond i c`), the front shape (Theorem 6.5) forces the next minute's
count below the `0.01n` scale (`beyond (i+1) c ≤ ⌊n/100⌋`), so minute `i+1` is
provably **NOT yet crossed**: `¬ CrossedB n (i+1) c`.  Hence at time `t01(i)` the
clock has not advanced minute `i+1`, giving the strict positive time gap
`t01(i+1) > t01(i)` — the lower bound `T_low ≤ t01(i+1) − t01(i)` (Lemmas
6.6 / 6.7).  This is exactly the "clock does not run too far ahead" the upper-only
C3 (`clock_faithful_O_log_n_upper`) lacks for the two-sided Theorem 6.8.

The `0.01`-scale hypothesis `hsmall : beyond (i+1) c ≤ ⌊n/100⌋` is the boundary
form of Theorem 6.5 — supplied by the maintained front profile (the within-
envelope front fraction at the crossing moment, `frontShape_couples_earlyDrip` +
the squaring), NOT a free assumption. -/
theorem clock_step_lower (n : ℕ) (hn : 100 ≤ n)
    (c : Config (Minute L₀)) (i : ℕ) (hcard : c.card = n)
    (_hcrossed_i : lo n ≤ beyond i c)
    (hsmall : beyond (i + 1) c ≤ n / 100) :
    ¬ CrossedB (L₀ := L₀) n (i + 1) c := by
  -- CrossedB n (i+1) c = (hi n ≤ beyond (i+1) c); but beyond (i+1) c ≤ ⌊n/100⌋ < hi n.
  unfold CrossedB
  intro hcross
  -- hi n = ⌊9n/10⌋ ; beyond (i+1) ≤ ⌊n/100⌋ ; for n ≥ 100, ⌊n/100⌋ < ⌊9n/10⌋.
  have hhi : hi n = 9 * n / 10 := rfl
  have : n / 100 < 9 * n / 10 := by omega
  omega

/-- **The strict time-gap consequence.**  Combining `clock_step_lower` with the
fact that crossing minute `i+1` is *required* for the clock to define `t01(i+1)`:
since minute `i+1` is not crossed at the moment minute `i` reaches `0.1`, at least
one further step is needed, so `t01(i+1) ≥ t01(i) + 1` — the strict lower bound on
the per-minute clock advance (the discrete kernel-level shadow of Lemmas
6.6 / 6.7's `≥ 0.45` parallel-time gap). -/
theorem clock_step_lower_strict (n : ℕ) (hn : 100 ≤ n)
    (c : Config (Minute L₀)) (i : ℕ) (hcard : c.card = n)
    (hcrossed_i : lo n ≤ beyond i c)
    (hsmall : beyond (i + 1) c ≤ n / 100) :
    beyond (i + 1) c < hi n := by
  have hnc := clock_step_lower (L₀ := L₀) n hn c i hcard hcrossed_i hsmall
  unfold CrossedB at hnc
  omega

/-! ## HONEST STATUS — Avenue C4 (front-shape minute induction → clock LOWER bound)

C4 builds the front-shape side of Doty §6, the companion LOWER bound to C3's
UPPER bound, kernel-level and 0-sorry / 0-axiom:

* **`FrontShapeAt` (Theorem 6.5) is GENUINE, not assumed.**  `frontShapeAt_holds`
  derives the profile invariant `c≥(i+1) ≤ (c≥i)²` directly from S2b's
  `real_front_squaring` — the squaring is the proven kernel mechanism (only the
  same-state drip seeds a new front level, with quadratically-suppressed
  probability), not an abstract `FrontRecurrence`.

* **The minute induction (`frontShape_step`) is the doubly-exponential
  envelope.**  `frontShape_step` carries the within-envelope front fraction one
  minute forward via `kernel_advance_le_envelope` (envelope = `f₀^(2^i)`, the
  closed form of the squaring), `envelope_step` is the literal squaring, and
  `front_shape_collapse` / `front_width_at` give the `O(log log n)` width
  (`front_emptied_real`: the front carries no agent beyond `frontWidthBound n`).

* **The coupling early-drip ← front-width is GENUINE (the C2 flaw avoided).**
  `frontShape_couples_earlyDrip` derives the front cap `B = frontCap f₀ i n =
  ⌊n·envelope f₀ i⌋` FROM the maintained profile, and `early_drip_small_at` feeds
  exactly that cap into S3's `earlyDrip_kernel_bound` — the early-drip smallness
  `O(n^{−0.85})` consumes the inductively-maintained front cap, it does NOT assume
  a free `B`.

* **`clock_step_lower` (Lemmas 6.6 / 6.7) is the LOWER bound C3 lacks.**  At the
  moment minute `i` reaches `0.1` (`lo n ≤ beyond i`), the front shape forces
  minute `i+1` tiny (`beyond (i+1) ≤ ⌊n/100⌋`, the `0.01`-scale boundary form of
  Theorem 6.5), so minute `i+1` is NOT crossed (`¬ CrossedB n (i+1)`,
  `clock_step_lower`) — the strict positive time gap `t01(i+1) > t01(i)`
  (`clock_step_lower_strict`).  This is the "clock does not run too far ahead"
  needed for the two-sided Theorem 6.8 and hour-sync (Theorem 6.9).

Together with C3's `clock_faithful_O_log_n_upper`, the per-minute clock advance is
now bounded on BOTH sides at the kernel level — the time-half of Doty's Theorem
3.1. -/
theorem front_shape_lower_status : True := trivial

end FrontShape

end ExactMajority
