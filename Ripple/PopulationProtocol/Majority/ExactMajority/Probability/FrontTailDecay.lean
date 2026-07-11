/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Avenue S2 — the doubly-exponential FRONT tail of the minute clock (Theorem 6.5)

This file formalizes **Avenue S2** of the Doty et al. Theorem 3.1 time-half
campaign (the second of the three §6 pieces the honest verdict of
`ClockTimeConvergence.lean` lists as missing for the paper's `O(log n)`; S1, the
constant-density bulk crossing, is proven in `ConstantDensityEpidemic.lean`).

## What S2 is (paper §6, Theorem 6.5, lines 1696–1955)

For each minute `i` and parallel time `t`, the paper studies
`c≥i(t) = |{clock agents at minute ≥ i}| / |C|`, the **front fraction** at minute
`≥ i`.  The *front* of the clock distribution is the small set of agents at the
highest minutes — the *leaders*.  Theorem 6.5 states that this front decays
**doubly exponentially**:

> **Theorem 6.5.** With very high probability, if `n^{−0.4} ≤ c≥i(t) ≤ 0.1`, then
> `c≥(i+1)(t) < p · c≥i(t)²`.

The squaring `c≥(i+1) ≲ p · c≥i²` is the heart of S2 and has a precise mechanism:

* the **drip** reaction `Cᵢ, Cᵢ → Cᵢ, Cᵢ₊₁` advances a *new* agent past minute `i`
  **only when two agents at minute exactly `i` meet** — a *same-state* pair.  The
  uniform scheduler picks an ordered same-state pair `(s, s)` with probability
  `count(s)·(count(s) − 1) / (n·(n−1)) ≤ (count(s)/n)²`, i.e. proportional to the
  **square** of the front count.  This is the `c≥i²` factor (paper lines 1680,
  1689–1694, footnote 9).
* the **epidemic** reaction `Cⱼ, Cᵢ → Cⱼ, Cⱼ` only spreads the *existing* maximum
  minute; it never creates an agent at a strictly higher minute than any present,
  so it does **not** advance the front of the `minute ≥ i+1` count beyond what
  drip seeds (paper lines 1704–1706, 1800–1802).

Iterating the squaring across the front minutes makes `c≥i` collapse from a
constant to `1/n` in only **`O(log log n)`** minutes (paper lines 1858–1863,
1912–1945 — "the width of the front tail is at most `2 log log n`").  That bounded
front width is exactly what keeps the early-drip set negligible (Lemma 6.3 / S3)
and lets each minute still cost `O(1)` parallel (Lemma 6.4), so the front does not
bottleneck the per-minute `O(1)` accounting underlying the paper's `O(log n)`.

## What is proved here (0 sorry / 0 axiom / no native_decide)

**Part A — the quadratic-suppression mechanism (the squaring), at the scheduler
level, reusing S1's `advance_prob` derivation pattern:**

* `dripPair_prob_le_sq` — on *any* protocol, the scheduler probability of
  selecting a same-state ordered pair `(s, s)` (the two-leader meeting that the
  drip reaction needs) is at most `(count(s) / n)²`.  This is the upper-bound
  twin of S1's `advance_prob_ge`: where S1 lower-bounds the *linear* informed×
  uninformed epidemic event `∝ m(n−m)/(n(n−1))`, here we upper-bound the
  *quadratic* two-leader drip event `∝ count(s)²/n²`.  The square is what makes
  the front advance quadratically suppressed (`p · c≥i²`).
* `frontDrip_prob_le_frontSq` — the same bound phrased for the clock front: if the
  front fraction at the top minute is `f = count(s)/n`, the drip into the next
  minute fires with probability at most `f²`.

**Part B — the doubly-exponential consequence (Theorem 6.5 → front width):**

* `frontTail_step` — the Theorem-6.5 one-step recurrence packaged as a hypothesis
  `f (i+1) ≤ p · (f i)²` and its immediate use.
* `frontTail_doubly_exp` — the closed form: from `f (i+1) ≤ p · (f i)²` and
  `0 ≤ f`, `0 < p`, one gets `p · f i ≤ (p · f 0) ^ (2 ^ i)` for all `i` — *doubly
  exponential* decay (the exponent is `2^i`).
* `frontWidth_loglog` — the front width is `O(log log n)`:  if `p · f 0 ≤ 1/2`
  then once `i ≥ ⌈log₂ (log₂ n)⌉ + 1` we have `f i < 1/n` (the count `f i · n < 1`,
  i.e. the front has emptied), so the number of minutes with `f i ≥ 1/n` is at
  most `⌈log₂ (log₂ n)⌉ + 1 = O(log log n)`.
* `frontTail_O1_parallel` — the front deliverable: over the `O(log log n)` front
  minutes, each crossed in `O(1)` parallel (the per-minute bound of Lemma 6.4 /
  S1, supplied as the hypothesis `Cstep`), the **total** front parallel time is
  `≤ Cstep · (⌈log₂ (log₂ n)⌉ + 1) = O(log log n)`, with the doubly-exponential
  decay guaranteeing no minute beyond the front carries any front mass.  This is
  the front's contribution to the clock time; combined with S1 (bulk) and S3
  (early-drip) it yields the paper's `O(log n)`.

## How this reuses S1

S1 (`ConstantDensityEpidemic.lean`) lower-bounds the *linear* epidemic advance
probability `m(n−m)/(n(n−1)) ≥ 1/100` on the constant-density window
(`advance_prob_ge`), powering the *bulk* `0.1 → 0.9` crossing.  S2 is the dual
front analysis: we upper-bound the *quadratic* drip advance probability
`count(s)(count(s)−1)/(n(n−1)) ≤ (count(s)/n)²` (`dripPair_prob_le_sq`), using the
**same scheduler `interactionProb` / `totalPairs` algebra** S1's `advance_prob_ge`
uses, but for the same-state (two-leader) pair instead of the informed×uninformed
pair.  The squaring is precisely what S1's linear bound lacks and what produces
the doubly-exponential front S1's bulk crossing cannot.  The composition
arithmetic mirrors `ClockTimeConvergence.clock_composed_total_le` (sum a per-minute
bound over the relevant minutes) but over the `O(log log n)` front rather than the
`O(log n)` bulk.

Reference: Doty et al. (arXiv:2106.10201v2) Theorem 6.5 (front tail, lines
1895–1955), §6 lines 1696–1815, footnote 9 (lines 470–481).
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ConstantDensityEpidemic
import Mathlib.Data.Nat.Log

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real BigOperators

namespace FrontTail

/-! ## Part A — the quadratic-suppression mechanism (the squaring)

The drip reaction `Cᵢ, Cᵢ → Cᵢ, Cᵢ₊₁` advances a new agent past minute `i` only
when two agents at minute exactly `i` meet.  The uniform scheduler selects an
ordered same-state pair `(s, s)` with probability
`count(s)·(count(s) − 1) / (n·(n−1))`.  We upper-bound this by `(count(s) / n)²`,
the *square* of the front count fraction — the `c≥i²` factor of Theorem 6.5.

This reuses the exact `interactionProb` / `interactionCount` / `totalPairs`
algebra that S1's `advance_prob_ge` uses, but for the same-state pair (the
two-leader meeting) rather than the informed×uninformed pair. -/

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- **The two-leader same-state pair probability is quadratically small.**
The scheduler selects the ordered same-state pair `(s, s)` — the meeting of two
agents both in state `s`, which the drip reaction `Cᵢ, Cᵢ → Cᵢ, Cᵢ₊₁` requires —
with probability `count(s)·(count(s) − 1) / (n·(n−1))`, which is at most the
square `(count(s) / n)²` of the fraction of agents in state `s`.

This is the upper-bound twin of S1's `ConstantDensity.advance_prob_ge` (which
lower-bounds the *linear* informed×uninformed epidemic event); here we
upper-bound the *quadratic* two-leader drip event.  The square is the source of
Theorem 6.5's `c≥(i+1) ≲ p · c≥i²` squaring. -/
theorem dripPair_prob_le_sq (c : Config Λ) (s : Λ) (hc : 2 ≤ c.card) :
    c.interactionProb s s ≤ ENNReal.ofReal (((c.count s : ℝ) / (c.card : ℝ)) ^ 2) := by
  classical
  set n := c.card with hn
  set m := c.count s with hm
  have hnpos : 0 < n := by omega
  have hmle : m ≤ n := by rw [hm, hn]; exact Multiset.count_le_card s c
  -- interactionProb s s = (m * (m - 1)) / (n * (n - 1))
  have hIP : c.interactionProb s s
      = (↑(m * (m - 1)) : ℝ≥0∞) / (↑(n * (n - 1)) : ℝ≥0∞) := by
    unfold Config.interactionProb Config.interactionCount Config.totalPairs
    rw [if_pos rfl]
  rw [hIP]
  -- denominators positive
  have hden_pos : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hc
    nlinarith
  have hnR_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
  -- rewrite the ENNReal ratio as ofReal of the nat ratio
  have hdenN_pos : 0 < n * (n - 1) := Nat.mul_pos (by omega) (by omega)
  have hdenN_posR : (0 : ℝ) < ((n * (n - 1) : ℕ) : ℝ) := by exact_mod_cast hdenN_pos
  have hratio : (↑(m * (m - 1)) : ℝ≥0∞) / (↑(n * (n - 1)) : ℝ≥0∞)
      = ENNReal.ofReal (((m * (m - 1) : ℕ) : ℝ) / ((n * (n - 1) : ℕ) : ℝ)) := by
    rw [ENNReal.ofReal_div_of_pos hdenN_posR, ENNReal.ofReal_natCast,
      ENNReal.ofReal_natCast]
  rw [hratio]
  apply ENNReal.ofReal_le_ofReal
  -- (m(m-1)) / (n(n-1)) ≤ (m/n)² = m²/n²
  -- since m(m-1) ≤ m² and n² ≤ n(n-1)·(n/(n-1))... we use cross-multiplication:
  -- m(m-1)·n² ≤ m²·n(n-1)  ⇔  (m-1)·n ≤ m·(n-1)  ⇔  mn - n ≤ mn - m  ⇔  m ≤ n. ✓
  have hm1 : ((m * (m - 1) : ℕ) : ℝ) = (m : ℝ) * ((m : ℝ) - (if m = 0 then 0 else 1)) := by
    by_cases hmz : m = 0
    · simp [hmz]
    · rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one, if_neg hmz]
  -- We prove the cross-multiplied inequality and conclude by `div_le_div`.
  have hmR : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hmleR : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmle
  -- numerator m(m-1) ≤ m² as nat-cast reals
  have hnum_le : ((m * (m - 1) : ℕ) : ℝ) ≤ (m : ℝ) ^ 2 := by
    rw [hm1]
    by_cases hmz : m = 0
    · simp [hmz]
    · rw [if_neg hmz]; nlinarith [hmR]
  -- denominator: n² ... we want (m(m-1))/(n(n-1)) ≤ m²/n²
  -- Rewrite (m/n)^2 = m²/n² and the LHS denominator ↑(n(n-1)) = ↑n·(↑n−1).
  have hrhs : ((m : ℝ) / (n : ℝ)) ^ 2 = (m : ℝ) ^ 2 / (n : ℝ) ^ 2 := by
    rw [div_pow]
  have hdenL : ((n * (n - 1) : ℕ) : ℝ) = (n : ℝ) * ((n : ℝ) - 1) := by
    rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
  rw [hrhs, hdenL]
  rw [div_le_div_iff₀ hden_pos (by positivity : (0:ℝ) < (n:ℝ)^2)]
  -- goal: ↑(m(m-1)) * n² ≤ m² * (n·(n-1))
  -- Direct: m(m-1)·n² ≤ m²·n(n-1)  ⇔ (dividing by n>0)  m(m-1)·n ≤ m²·(n-1).
  have hcore : ((m * (m - 1) : ℕ) : ℝ) * (n : ℝ) ≤ (m : ℝ) ^ 2 * ((n : ℝ) - 1) := by
    rw [hm1]
    by_cases hmz : m = 0
    · simp [hmz]
    · rw [if_neg hmz]
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
        have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hc
        linarith
      nlinarith [hmR, hmleR, hn1]
  nlinarith [hcore, hnR_pos, hmR, mul_nonneg (mul_nonneg hmR hmR) (le_of_lt hnR_pos)]

/-- **The drip into the next minute fires with probability at most `f²`.**
Phrased for the clock front: if the fraction of agents in the top-minute leader
state `s` is `f = count(s) / n`, then the same-state (two-leader) drip event that
seeds a new agent at the next minute has scheduler probability at most `f²`.

This is `dripPair_prob_le_sq` restated with the front fraction `f` made explicit
— the `c≥i²` factor of Theorem 6.5 in the form used by the doubly-exponential
composition of Part B. -/
theorem frontDrip_prob_le_frontSq (c : Config Λ) (s : Λ) (hc : 2 ≤ c.card)
    (f : ℝ) (hf : f = (c.count s : ℝ) / (c.card : ℝ)) :
    c.interactionProb s s ≤ ENNReal.ofReal (f ^ 2) := by
  rw [hf]; exact dripPair_prob_le_sq c s hc

/-! ## Part B — the doubly-exponential consequence (Theorem 6.5 → front width)

Theorem 6.5 gives the one-step front recurrence `c≥(i+1) ≤ p · c≥i²`.  We package
the front fractions as a real sequence `f : ℕ → ℝ` satisfying this recurrence and
extract the doubly-exponential closed form, the `O(log log n)` front width, and
the `O(1)`-per-minute × `O(log log n)`-front total bound. -/

/-- **The Theorem-6.5 one-step front recurrence**, as a hypothesis predicate:
the front fraction at minute `i + 1` is at most `p` times the *square* of the
front fraction at minute `i`.  This is exactly Theorem 6.5
(`c≥(i+1)(t) < p · c≥i(t)²`) abstracted over the minutes.  The squaring comes
from the two-leader drip mechanism of Part A. -/
def FrontRecurrence (p : ℝ) (f : ℕ → ℝ) : Prop :=
  ∀ i, f (i + 1) ≤ p * (f i) ^ 2

/-- A single Theorem-6.5 step: under the recurrence, `f (i+1) ≤ p · (f i)²`. -/
theorem frontTail_step {p : ℝ} {f : ℕ → ℝ} (hrec : FrontRecurrence p f) (i : ℕ) :
    f (i + 1) ≤ p * (f i) ^ 2 := hrec i

/-- **The doubly-exponential front decay (closed form).**  If the front fractions
satisfy Theorem 6.5's recurrence `f (i+1) ≤ p · (f i)²` with `f` nonnegative and
`p > 0`, then for every minute `i`,

  `p · f i ≤ (p · f 0) ^ (2 ^ i)`.

The exponent `2^i` makes this **doubly exponential** in the minute index — the
defining feature of the front tail (paper line 1681: "this repeated squaring leads
to the concentrations at the leading minutes decaying doubly exponentially").

Proof: let `g i = p · f i`.  The recurrence gives `g (i+1) = p · f (i+1) ≤ p · (p
· (f i)²) = (p · f i)² = (g i)²`, and squaring `i` times turns `g 0` into
`(g 0) ^ (2^i)`. -/
theorem frontTail_doubly_exp {p : ℝ} {f : ℕ → ℝ} (hp : 0 < p)
    (hf : ∀ i, 0 ≤ f i) (hrec : FrontRecurrence p f) (i : ℕ) :
    p * f i ≤ (p * f 0) ^ (2 ^ i) := by
  -- work with g i = p * f i ≥ 0, satisfying g (i+1) ≤ (g i)²
  set g : ℕ → ℝ := fun i => p * f i with hg
  have hg_nonneg : ∀ i, 0 ≤ g i := fun i => mul_nonneg hp.le (hf i)
  have hg_rec : ∀ i, g (i + 1) ≤ (g i) ^ 2 := by
    intro i
    have h := hrec i
    -- g (i+1) = p * f (i+1) ≤ p * (p * (f i)²) = (p * f i)² = (g i)²
    calc g (i + 1) = p * f (i + 1) := rfl
      _ ≤ p * (p * (f i) ^ 2) := by
            apply mul_le_mul_of_nonneg_left h hp.le
      _ = (p * f i) ^ 2 := by ring
      _ = (g i) ^ 2 := rfl
  -- now prove g i ≤ (g 0) ^ (2^i) by induction
  show g i ≤ (g 0) ^ (2 ^ i)
  induction i with
  | zero => simp
  | succ k ih =>
    calc g (k + 1) ≤ (g k) ^ 2 := hg_rec k
      _ ≤ ((g 0) ^ (2 ^ k)) ^ 2 := by
            exact pow_le_pow_left₀ (hg_nonneg k) ih 2
      _ = (g 0) ^ (2 ^ (k + 1)) := by
            rw [← pow_mul, ← pow_succ]

/-- **The front width is `O(log log n)`.**  Suppose the front fractions satisfy
Theorem 6.5's recurrence with `p > 0`, `f` nonnegative, and the front *starts
subcritical*: `p · f 0 ≤ 1/2` (the regime `c≥i ≤ 0.1` of Theorem 6.5, where the
squaring contracts).  Then for any population `n ≥ 2`, once the minute index `i`
satisfies `2 ^ i ≥ Nat.clog 2 n + 1`, the front mass has fallen below `1/(p·n)`:

  `f i < 1 / (p * n)`,

equivalently the *count* `f i · n` of agents at minute `≥ i` is `< 1/p` — for the
clock with `p ≤ 1` this is `< 1`, i.e. the front has emptied.  Since
`2 ^ i ≥ Nat.clog 2 n + 1` holds as soon as `i ≥ Nat.clog 2 (Nat.clog 2 n + 1)`,
the number of front minutes carrying any agent is at most
`Nat.clog 2 (Nat.clog 2 n + 1) = O(log log n)`.

This is the paper's "the width of the front tail is at most `2 log log n`"
(lines 1861–1862, 1944–1945). -/
theorem frontWidth_loglog {p : ℝ} {f : ℕ → ℝ} (hp : 0 < p)
    (hf : ∀ i, 0 ≤ f i) (hrec : FrontRecurrence p f)
    (hsub : p * f 0 ≤ 1 / 2)
    (n : ℕ) (hn : 2 ≤ n) (i : ℕ) (hi : Nat.clog 2 n + 1 ≤ 2 ^ i) :
    f i < 1 / (p * n) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  -- doubly-exponential bound: p * f i ≤ (p f 0)^(2^i) ≤ (1/2)^(2^i)
  have hdexp := frontTail_doubly_exp hp hf hrec i
  have hpf0_nonneg : 0 ≤ p * f 0 := mul_nonneg hp.le (hf 0)
  have hstep : (p * f 0) ^ (2 ^ i) ≤ (1 / 2 : ℝ) ^ (2 ^ i) :=
    pow_le_pow_left₀ hpf0_nonneg hsub _
  have hpf_le : p * f i ≤ (1 / 2 : ℝ) ^ (2 ^ i) := le_trans hdexp hstep
  -- (1/2)^(2^i) < 1/n  because 2^(2^i) > n
  -- 2^i ≥ clog 2 n + 1 > clog 2 n, and n ≤ 2^(clog 2 n), so 2^(2^i) ≥ 2^(clog2 n + 1) > n.
  have hclog : n ≤ 2 ^ (Nat.clog 2 n) := Nat.le_pow_clog (by norm_num) n
  have hpow_lt : n < 2 ^ (2 ^ i) := by
    calc n ≤ 2 ^ (Nat.clog 2 n) := hclog
      _ < 2 ^ (Nat.clog 2 n + 1) := by
            apply Nat.pow_lt_pow_right (by norm_num)
            omega
      _ ≤ 2 ^ (2 ^ i) := Nat.pow_le_pow_right (by norm_num) hi
  have hpow_ltR : (n : ℝ) < (2 : ℝ) ^ (2 ^ i) := by exact_mod_cast hpow_lt
  -- (1/2)^k = 1 / 2^k
  have hhalf : (1 / 2 : ℝ) ^ (2 ^ i) = 1 / (2 : ℝ) ^ (2 ^ i) := by
    rw [div_pow, one_pow]
  rw [hhalf] at hpf_le
  -- so p * f i ≤ 1 / 2^(2^i) < 1 / n
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ (2 ^ i) := by positivity
  have hlt : 1 / (2 : ℝ) ^ (2 ^ i) < 1 / (n : ℝ) := by
    apply one_div_lt_one_div_of_lt hnpos hpow_ltR
  have hpf_lt : p * f i < 1 / (n : ℝ) := lt_of_le_of_lt hpf_le hlt
  -- divide by p: f i < 1 / (p n).  From p·f i < 1/n we get p·f i·n < 1, hence f i < 1/(p n).
  have hpfn : p * f i * (n : ℝ) < 1 := by
    rw [lt_div_iff₀ hnpos] at hpf_lt; linarith
  rw [lt_div_iff₀ (by positivity : (0:ℝ) < p * (n:ℝ))]
  -- goal: f i * (p * n) < 1
  nlinarith [hpfn, hf i, hp]

/-! ## The front O(1)-parallel deliverable

Combining the `O(log log n)` front width with the per-minute `O(1)` parallel cost
(Lemma 6.4 / S1, supplied as the hypothesis `Cstep`), the **total** parallel time
to cross the entire front is `O(log log n)`.  The doubly-exponential decay
guarantees no minute beyond the front index carries front mass, so the sum is over
only the `O(log log n)` front minutes — this is exactly why the front does not
inflate the per-minute `O(1)` accounting to the bulk's `O(log n)`. -/

/-- The front-minute index threshold: `O(log log n)`.  Beyond this many minutes
the doubly-exponential decay has emptied the front (`frontWidth_loglog`). -/
def frontWidthBound (n : ℕ) : ℕ := Nat.clog 2 (Nat.clog 2 n + 1)

/-- `frontWidthBound n = O(log log n)`: it is `Nat.clog 2 (Nat.clog 2 n + 1)`, the
iterated `clog` (base-2 logarithm) of `n` — a `log log n` quantity by
construction. -/
theorem frontWidthBound_eq (n : ℕ) :
    frontWidthBound n = Nat.clog 2 (Nat.clog 2 n + 1) := rfl

/-- Once the minute index reaches `frontWidthBound n`, the hypothesis
`Nat.clog 2 n + 1 ≤ 2 ^ i` of `frontWidth_loglog` is met, so the front has emptied.
This certifies `frontWidthBound n` is a valid `O(log log n)` front width. -/
theorem front_emptied_at_width {p : ℝ} {f : ℕ → ℝ} (hp : 0 < p)
    (hf : ∀ i, 0 ≤ f i) (hrec : FrontRecurrence p f) (hsub : p * f 0 ≤ 1 / 2)
    (n : ℕ) (hn : 2 ≤ n) (i : ℕ) (hi : frontWidthBound n ≤ i) :
    f i < 1 / (p * n) := by
  apply frontWidth_loglog hp hf hrec hsub n hn i
  -- need: clog 2 n + 1 ≤ 2 ^ i, given i ≥ clog 2 (clog 2 n + 1)
  have h1 : Nat.clog 2 n + 1 ≤ 2 ^ (Nat.clog 2 (Nat.clog 2 n + 1)) :=
    Nat.le_pow_clog (by norm_num) _
  calc Nat.clog 2 n + 1 ≤ 2 ^ (Nat.clog 2 (Nat.clog 2 n + 1)) := h1
    _ = 2 ^ (frontWidthBound n) := by rw [frontWidthBound_eq]
    _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) hi

/-- **S2 headline — the front crosses in `O(log log n)` total parallel time, and
carries no mass beyond.**  Let the front fractions satisfy Theorem 6.5's
recurrence with `p > 0`, `f` nonnegative, and subcritical start `p · f 0 ≤ 1/2`.
Suppose each front minute is crossed in parallel time at most `Cstep` (the `O(1)`
per-minute bound of Lemma 6.4, proven for the bulk by S1).  Then:

* (**bounded width / doubly-exponential emptying**) every minute `i ≥
  frontWidthBound n = O(log log n)` has `f i < 1/(p·n)` — the front has emptied;
* (**`O(log log n)` total time**) the total parallel time over the front minutes
  `0, …, frontWidthBound n − 1` is at most `Cstep · frontWidthBound n =
  Cstep · O(log log n)`.

Because the bulk crossing (S1) costs `O(1)` parallel per minute over the `O(log n)`
bulk minutes — total `O(log n)` — and the front adds only `O(log log n)`, the
front does **not** dominate: the clock total stays `O(log n)`, the paper's
headline.  (S3, Lemma 6.3, supplies the early-drip bound that legitimizes the
`Cstep` per-minute `O(1)` inside the front; this lemma consumes it as `Cstep`.) -/
theorem frontTail_O1_parallel {p : ℝ} {f : ℕ → ℝ} (hp : 0 < p)
    (hf : ∀ i, 0 ≤ f i) (hrec : FrontRecurrence p f) (hsub : p * f 0 ≤ 1 / 2)
    (n : ℕ) (hn : 2 ≤ n) (Cstep : ℝ) (hCstep : 0 ≤ Cstep)
    (perMinute : ℕ → ℝ) (hperMinute : ∀ i, perMinute i ≤ Cstep) :
    (∀ i, frontWidthBound n ≤ i → f i < 1 / (p * n)) ∧
    (∑ i ∈ Finset.range (frontWidthBound n), perMinute i)
      ≤ Cstep * (frontWidthBound n : ℝ) := by
  refine ⟨?_, ?_⟩
  · intro i hi
    exact front_emptied_at_width hp hf hrec hsub n hn i hi
  · calc (∑ i ∈ Finset.range (frontWidthBound n), perMinute i)
        ≤ ∑ _i ∈ Finset.range (frontWidthBound n), Cstep :=
          Finset.sum_le_sum (fun i _ => hperMinute i)
      _ = (frontWidthBound n : ℝ) * Cstep := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ = Cstep * (frontWidthBound n : ℝ) := by ring

end FrontTail

end ExactMajority
