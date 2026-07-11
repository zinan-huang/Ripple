import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ClockFrontShape
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.FrontTailDecay

/-!
# ClockFrontProfile — the paper-faithful moving-frame front invariant (replaces the FALSE `hwin_all`)

This file corrects the front-shape formulation that the O(log n) clock's FrontSync maintenance rests on.

## Why the previous `FrontFeederWindow` / `hwin_all` was the wrong — and FALSE — object

`FrontSyncConc.clock_real_unconditional` proved the clock's FrontSync maintenance over the horizon, with the
single remaining hypothesis
`hwin_all : ∀ c, FrontSync c → c.card = n → FrontFeederWindow n B c`, i.e. the cap−1 feeder count
`frontMinuteCount (capMinute−1) c ≤ B = O(log log n)` at every reachable FrontSync config.

That is NOT a faithful invariant of Doty et al. §6, and as a ∀-reachable statement it is FALSE.  Under
`FrontSync` the minute `capMinute−1` has no upward out-flux — a clock leaving `capMinute−1 → capMinute` is
exactly a FrontSync breach — while the SYNC/epidemic rule lets a lower-minute clock jump up to `capMinute−1`
on meeting a `capMinute−1` clock.  So a reachable schedule can pump `frontMinuteCount(capMinute−1)`
arbitrarily large purely by sync, never scheduling the `capMinute−1 ↔ capMinute−1` DRIP that is the only move
reaching the cap — leaving the cap empty (`FrontSync` still holds) with an arbitrarily large feeder.  Hence
`hwin_all` is false; a feeder-only supermartingale cannot exist (the feeder is a growing submartingale).

## What the paper actually proves (verified against arXiv:2106.10201v2 §6, Doty-2021-exact-majority.pdf)

* Theorem 6.5 (line 2810): `n^{-0.4} ≤ c_{≥i}(t) ≤ 0.1 ⟹ c_{≥i+1}(t) < p · c_{≥i}(t)²`.
* Lemma 6.3 (line 2692): `c_{≥i+1}(t) ≤ 0.9 p c_{≥i}(t)² + d_{≥i+1}(t)` for `n^{-0.45} ≤ c_{≥i}(t) ≤ 0.1`.
* The front-tail WIDTH (number of leading minutes) is `≤ 2 log log n` (line 2829) — NOT the COUNT: a constant
  fraction of agents sits in the top two minutes (line 545).  So the band COUNT is `Θ(n)`, not `O(log log n)`.

Doty's cumulative tail `c_{≥i}(t) = #{a : a.minute ≥ i} / |C|` is EXACTLY `rBeyond i c / c.card`
(`rBeyond` = count of Phase-3 clocks at minute `≥ i`, `ClockRealKernel.rBeyond`).  So the correct object was
already present — only the final hypothesis was mis-stated.

## The correct (TRUE, paper-faithful) invariant: `GoodFrontWidth`

`GoodFrontWidth W c`: the leading front is never more than `W = Θ(log log n)` minutes ahead of the `0.1` bulk
threshold — Doty's "first claim inside the proof of Theorem 6.5" (when the first agent reaches minute `i`, a
`0.1` fraction is already within `2 log log n` minutes behind it).  In cardinality form
(`c_{≥j} ≥ 0.1 ⟺ 10 · rBeyond j c ≥ c.card`):

  `0 < rBeyond i c  →  c.card ≤ 10 · rBeyond (i − W) c`.

From it, the cap-safety `FrontSync` follows DETERMINISTICALLY while the bulk is below the top band — the
correct replacement for the false feeder bound.  The genuine remaining probabilistic content is exactly
`GoodFrontWidth` itself = Doty Theorem 6.5's first claim (a TRUE statement, unlike `hwin_all`).
-/

namespace ExactMajority

/-! ## The WINDOWED doubly-exponential decay (the faithful Theorem 6.5 form)

Theorem 6.5 asserts the squaring recurrence ONLY on the window `n^{-0.4} ≤ c_{≥i} ≤ 0.1`.  The
unrestricted recurrence (`FrontRecurrence` at every level) is NOT what the paper proves, and as a
run-long whp invariant it is genuinely at risk below the window (see the CORRECTION block below).
The faithful iteration is WINDOWED: as long as the fractions stay at or above the window floor `θ`,
the squaring applies and the doubly-exponential collapse goes through; the levels below the floor
are handled by a separate CLIMB bound.  These two lemmas extend the abstract `FrontTail` machinery
of `FrontTailDecay.lean` (same namespace). -/

namespace FrontTail

/-- **The windowed doubly-exponential decay.**  If the squaring `f (j+1) ≤ (f j)²` holds whenever
`θ ≤ f j ≤ 1/10` (the faithful Theorem-6.5 window), the start is subcritical (`f 0 ≤ 1/10`), and
the first `m` values stay at or above the floor (`∀ j < m, θ ≤ f j`), then `f m ≤ (f 0) ^ (2 ^ m)`.
The upper-window side `f j ≤ 1/10` is maintained automatically along the iteration since the
iterates are dominated by the doubly-exponential envelope `(f 0)^(2^j) ≤ f 0 ≤ 1/10`. -/
theorem windowed_doubly_exp {θ : ℝ} {f : ℕ → ℝ}
    (hf : ∀ i, 0 ≤ f i)
    (hrec : ∀ j, θ ≤ f j → f j ≤ 1 / 10 → f (j + 1) ≤ (f j) ^ 2)
    (hf0 : f 0 ≤ 1 / 10) (m : ℕ) (hwin : ∀ j, j < m → θ ≤ f j) :
    f m ≤ (f 0) ^ (2 ^ m) := by
  induction m with
  | zero => simp
  | succ k ih =>
      have hwk : ∀ j, j < k → θ ≤ f j := fun j hj => hwin j (by omega)
      have hk : f k ≤ (f 0) ^ (2 ^ k) := ih hwk
      have hk10 : f k ≤ 1 / 10 := by
        calc f k ≤ (f 0) ^ (2 ^ k) := hk
          _ ≤ (f 0) ^ 1 :=
              pow_le_pow_of_le_one (hf 0) (by linarith) Nat.one_le_two_pow
          _ = f 0 := pow_one _
          _ ≤ 1 / 10 := hf0
      have hgate : θ ≤ f k := hwin k (by omega)
      calc f (k + 1) ≤ (f k) ^ 2 := hrec k hgate hk10
        _ ≤ ((f 0) ^ (2 ^ k)) ^ 2 := pow_le_pow_left₀ (hf k) hk 2
        _ = (f 0) ^ (2 ^ (k + 1)) := by rw [← pow_mul, ← pow_succ]

/-- **The windowed collapse crosses any floor `θ ≥ 1/n` within `frontWidthBound n` levels.**
Under the windowed squaring with subcritical start, the first `frontWidthBound n` values cannot
all stay at or above a floor `θ ≥ 1/n`: some `j ≤ frontWidthBound n` has `f j < θ` (else the
doubly-exponential envelope would push `f (frontWidthBound n)` below `1/n ≤ θ`, contradicting the
floor).  This is the windowed replacement for `front_emptied_at_width`. -/
theorem windowed_floor_crossing {θ : ℝ} {f : ℕ → ℝ}
    (hf : ∀ i, 0 ≤ f i)
    (hrec : ∀ j, θ ≤ f j → f j ≤ 1 / 10 → f (j + 1) ≤ (f j) ^ 2)
    (hf0 : f 0 ≤ 1 / 10)
    (n : ℕ) (hn : 2 ≤ n) (hθ : 1 / (n : ℝ) ≤ θ) :
    ∃ j ≤ frontWidthBound n, f j < θ := by
  by_contra hcon
  push Not at hcon
  -- hcon : ∀ j ≤ frontWidthBound n, θ ≤ f j
  set W := frontWidthBound n with hWdef
  have hwin : ∀ j, j < W → θ ≤ f j := fun j hj => hcon j (by omega)
  have hW := windowed_doubly_exp hf hrec hf0 W hwin
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  -- 2^(2^W) > n, exactly as in `frontWidth_loglog`.
  have hWle : Nat.clog 2 n + 1 ≤ 2 ^ W := by
    calc Nat.clog 2 n + 1 ≤ 2 ^ (Nat.clog 2 (Nat.clog 2 n + 1)) :=
          Nat.le_pow_clog (by norm_num) _
      _ = 2 ^ W := by rw [hWdef, frontWidthBound_eq]
  have hpow_lt : n < 2 ^ (2 ^ W) := by
    calc n ≤ 2 ^ (Nat.clog 2 n) := Nat.le_pow_clog (by norm_num) n
      _ < 2 ^ (Nat.clog 2 n + 1) := by
          apply Nat.pow_lt_pow_right (by norm_num)
          omega
      _ ≤ 2 ^ (2 ^ W) := Nat.pow_le_pow_right (by norm_num) hWle
  -- f W ≤ (1/2)^(2^W) < 1/n ≤ θ ≤ f W: contradiction.
  have hfW : f W ≤ (1 / 2 : ℝ) ^ (2 ^ W) := by
    calc f W ≤ (f 0) ^ (2 ^ W) := hW
      _ ≤ (1 / 10 : ℝ) ^ (2 ^ W) := pow_le_pow_left₀ (hf 0) hf0 _
      _ ≤ (1 / 2 : ℝ) ^ (2 ^ W) := pow_le_pow_left₀ (by norm_num) (by norm_num) _
  have hlt : (1 / 2 : ℝ) ^ (2 ^ W) < 1 / (n : ℝ) := by
    rw [div_pow, one_pow]
    apply one_div_lt_one_div_of_lt hnpos
    exact_mod_cast hpow_lt
  have hθfW : θ ≤ f W := hcon W le_rfl
  linarith

end FrontTail

namespace ClockFrontProfile

open ClockRealKernel ClockFrontShape

variable {L K : ℕ}

/-- **The paper-faithful moving-frame width invariant** (Doty Thm 6.5, "first claim").
The leading front is never more than `W` minutes ahead of the `0.1` bulk threshold.  Cardinality form of
`c_{≥i} > 0 ⟹ c_{≥ i−W} ≥ 0.1`, using `c_{≥j} = rBeyond j c / c.card` and `≥ 0.1 ⟺ 10·rBeyond ≥ card`. -/
def GoodFrontWidth (W : ℕ) (c : Config (AgentState L K)) : Prop :=
  ∀ i : ℕ, 0 < rBeyond (L := L) (K := K) i c →
    c.card ≤ 10 * rBeyond (L := L) (K := K) (i - W) c

/-- **The correct cap-safety, replacing the false `hwin_all`.**  On the good-width event, if the bulk has not
yet reached within `W` minutes of the cap (`c_{≥ capMinute−W} < 0.1`, i.e. `10·rBeyond(capMinute−W) < card`),
then the cap is empty: `FrontSync c`.  This is DETERMINISTIC — the `i = capMinute` instance of the width
invariant's contrapositive — NOT a feeder-count bound.  It is the faithful "top cannot be far ahead of bulk"
statement from the proof of Doty Theorem 6.5. -/
theorem frontSync_of_goodWidth_of_bulk_below
    (W : ℕ) (c : Config (AgentState L K))
    (hgood : GoodFrontWidth (L := L) (K := K) W c)
    (hbulk : 10 * rBeyond (L := L) (K := K) (capMinute (L := L) (K := K) - W) c < c.card) :
    FrontSync (L := L) (K := K) c := by
  rw [frontSync_iff_rBeyond_cap_zero]
  by_contra h
  have hpos : 0 < rBeyond (L := L) (K := K) (capMinute (L := L) (K := K)) c :=
    Nat.pos_of_ne_zero h
  have hw := hgood (capMinute (L := L) (K := K)) hpos
  omega

/-- **Contrapositive view: a nonempty cap forces the bulk into the top band.**  If the cap is nonempty
(`¬ FrontSync`), then on the good-width event the `0.1` bulk threshold has already reached within `W` of the
cap.  This is the genuine coupling: reaching the cap is not a "bad event" — it means the bulk has arrived and
the hour is completing. -/
theorem bulk_in_band_of_cap_nonempty
    (W : ℕ) (c : Config (AgentState L K))
    (hgood : GoodFrontWidth (L := L) (K := K) W c)
    (hcap : ¬ FrontSync (L := L) (K := K) c) :
    c.card ≤ 10 * rBeyond (L := L) (K := K) (capMinute (L := L) (K := K) - W) c := by
  have hpos : 0 < rBeyond (L := L) (K := K) (capMinute (L := L) (K := K)) c := by
    rw [frontSync_iff_rBeyond_cap_zero] at hcap
    exact Nat.pos_of_ne_zero hcap
  exact hgood (capMinute (L := L) (K := K)) hpos

/-! ## The genuine remaining residual (named, TRUE — unlike the false `hwin_all`)

`GoodFrontWidth W c` for the reachable configs over the run is exactly **Doty Theorem 6.5's first claim**:
the high-probability moving-frame width bound (the `0.1` bulk threshold stays within `W = Θ(log log n)`
minutes of the leading front).  Its proof is the §6 induction on the minute index `i`, via Lemma 6.3's
`0.1`-parallel-time-window argument (`c_{≥i+1} ≤ 0.9 p c_{≥i}² + d_{≥i+1}`, early-drip `d_{≥i+1} = O(n^{-0.85})`),
closing with `1.23(0.9p(0.84x)² + 0.11px²) < 0.9px²` ("front slower than bulk").  This is a TRUE statement
(the genuine §6 core), in contrast to the FALSE fixed-cap feeder bound it replaces.  It is the next thing to
formalize; we do NOT state it as a vacuous stub here. -/

/-! ## Reducing `GoodFrontWidth` to the per-config recurrence `GoodFrontProfile` (Doty Thm 6.5)

`GoodFrontWidth` is a WIDTH consequence of the doubly-exponential front decay.  The decay itself is the
per-config recurrence on the cumulative-tail fractions `c_{≥T} = rBeyond T c / card`:

  `GoodFrontProfile c`:  `∀ T, c_{≥T+1} ≤ (c_{≥T})²`   (Doty Theorem 6.5, worst case `p = 1`, paper line 3033).

Given it, the proven abstract doubly-exponential machinery (`FrontTail.front_emptied_at_width`) collapses any
subcritical level (`c_{≥j} < 0.1`) to empty within `W = frontWidthBound card = O(log log n)` levels — which is
exactly `GoodFrontWidth`.  This reduces the clock's residual from `GoodFrontWidth` to `GoodFrontProfile`, the
genuine high-probability Theorem 6.5 recurrence (the §6 core still to be discharged probabilistically). -/

/-- The cumulative-tail fraction `c_{≥T} = rBeyond T c / card` (Doty's `c_{≥i}`). -/
noncomputable def frac (T : ℕ) (c : Config (AgentState L K)) : ℝ :=
  (rBeyond (L := L) (K := K) T c : ℝ) / (c.card : ℝ)

/-- **The per-config front recurrence** (Doty Theorem 6.5, worst case `p = 1`):
`c_{≥T+1} ≤ (c_{≥T})²` at every minute `T`. -/
def GoodFrontProfile (c : Config (AgentState L K)) : Prop :=
  ∀ T : ℕ, frac (L := L) (K := K) (T + 1) c ≤ (frac (L := L) (K := K) T c) ^ 2

/-- **`GoodFrontWidth` from `GoodFrontProfile`.**  The per-config Theorem-6.5 recurrence, on the clock window
(`AllClockP3`) with `W ≥ frontWidthBound card`, deterministically yields the moving-frame width invariant:
any subcritical level collapses to empty within `W = O(log log n)` levels (`FrontTail.front_emptied_at_width`).
Reduces the clock's residual to `GoodFrontProfile` (the true §6 recurrence). -/
theorem goodFrontWidth_of_profile
    (W : ℕ) (c : Config (AgentState L K)) (hcard : 2 ≤ c.card)
    (hall : AllClockP3 (L := L) (K := K) c)
    (hW : FrontTail.frontWidthBound c.card ≤ W)
    (hprof : GoodFrontProfile (L := L) (K := K) c) :
    GoodFrontWidth (L := L) (K := K) W c := by
  have hcardpos : 0 < c.card := by omega
  have hcardℝ : (0 : ℝ) < (c.card : ℝ) := by exact_mod_cast hcardpos
  intro i hi
  by_cases hiW : i ≤ W
  · -- i ≤ W ⟹ i − W = 0 ⟹ rBeyond 0 c = card (all agents are clocks), so 10·rBeyond ≥ card.
    have hzero : i - W = 0 := by omega
    rw [hzero]
    have hr0 : rBeyond (L := L) (K := K) 0 c = c.card := by
      unfold rBeyond
      rw [Multiset.countP_eq_card]
      intro a ha
      exact ⟨(hall a ha).1, Nat.zero_le _⟩
    rw [hr0]; omega
  · -- i > W: apply the doubly-exponential collapse to the window [i−W, i].
    by_contra hcon
    rw [not_le] at hcon  -- 10 * rBeyond (i − W) c < c.card
    set base := i - W with hbase
    set f : ℕ → ℝ := fun j => frac (L := L) (K := K) (base + j) c with hfdef
    have hfnn : ∀ j, 0 ≤ f j := by
      intro j; simp only [hfdef, frac]; positivity
    have hrec : FrontTail.FrontRecurrence 1 f := by
      intro j
      simp only [hfdef]
      have h := hprof (base + j)
      rw [show base + (j + 1) = (base + j) + 1 from by ring, one_mul]
      exact h
    have hsub : (1 : ℝ) * f 0 ≤ 1 / 2 := by
      simp only [hfdef, Nat.add_zero, frac, one_mul]
      rw [div_le_iff₀ hcardℝ]
      have : (10 : ℝ) * (rBeyond (L := L) (K := K) base c : ℝ) < (c.card : ℝ) := by
        exact_mod_cast hcon
      linarith
    have hemp := FrontTail.front_emptied_at_width (f := f) one_pos hfnn hrec hsub
      c.card hcard W hW
    -- f W = frac i c = rBeyond i / card < 1/(1·card) = 1/card ⟹ rBeyond i < 1 ⟹ = 0.
    have hbaseW : base + W = i := by omega
    rw [show f W = frac (L := L) (K := K) i c from by simp only [hfdef]; rw [hbaseW]] at hemp
    simp only [frac, one_mul] at hemp
    rw [div_lt_div_iff₀ hcardℝ hcardℝ] at hemp
    -- (rBeyond i)·card < 1·card ⟹ rBeyond i < 1 ⟹ rBeyond i = 0
    have hri : (rBeyond (L := L) (K := K) i c : ℝ) < 1 := by
      have := hemp; nlinarith [hcardℝ]
    have : rBeyond (L := L) (K := K) i c = 0 := by
      have : rBeyond (L := L) (K := K) i c < 1 := by exact_mod_cast hri
      omega
    omega

/-! ## CORRECTION (2026-06-09) — the unrestricted `GoodFrontProfile` is NOT the faithful residual

`GoodFrontProfile` above demands the squaring at EVERY level `T`, but the paper's Theorem 6.5 asserts it
ONLY on the window `n^{-0.4} ≤ c_{≥i} ≤ 0.1` (paper line 2810).  Below the window the unrestricted
recurrence is genuinely at risk as a run-long whp invariant: the FIRST drip into a fresh level `T+1`
happens at per-interaction rate `(rBeyond T/n)²`, and the level below typically grows through the
borderline count `√n` exactly when the seeding fires — a seed while `rBeyond T = B < √n` gives
`frac (T+1) = 1/n > (B/n)²`, violating the unrestricted recurrence.  Integrating the seeding rate along
the front's growth shows the violation happens Θ(1) times per level, i.e. Θ(log n) times per run — the
unrestricted profile is NOT whp-maintained.  (`goodFrontWidth_of_profile` stays valid as a theorem, but
its hypothesis cannot be discharged whp; do not build on it.)

The paper's actual proof of the width claim (Thm 6.5 "first claim") splits at the window floor:
* ON the window — iterate the WINDOWED recurrence (Lemma 6.3 + early-drip `d`) from the `0.1` bulk
  down to the `n^{-0.4}` floor in `O(log log n)` squarings;
* BELOW the floor — the CLIMB argument: drips above a sub-floor level fire at rate
  `≤ p((n^{-0.4})²)² = p·n^{-1.6}`, so within the `O(log log n)`-time window the front cannot climb
  `log log n` further levels (probability `n^{-ω(1)}`).

The faithful residual is therefore the PAIR `WindowedFrontProfile` + `ClimbBound` below, and the glue
`goodFrontWidth_of_windowed_profile_and_climb` replaces `goodFrontWidth_of_profile`. -/

/-- **The windowed Theorem-6.5 recurrence** (the faithful residual, worst case `p = 1`): the squaring
holds at every level whose tail fraction sits in the window `[θ, 1/10]`.  `θ` is the paper's `n^{-0.4}`
floor (as a fraction); the upper side `1/10` is the paper's `c_{≥i} ≤ 0.1`. -/
def WindowedFrontProfile (θ : ℝ) (c : Config (AgentState L K)) : Prop :=
  ∀ T : ℕ, θ ≤ frac (L := L) (K := K) T c → frac (L := L) (K := K) T c ≤ 1 / 10 →
    frac (L := L) (K := K) (T + 1) c ≤ (frac (L := L) (K := K) T c) ^ 2

/-- **The climb bound** (the sub-floor half of Thm 6.5's first claim): no level `W₂` or more above a
sub-floor level (`frac k < θ`) carries any clock.  `W₂` is the paper's `log log n` climb allowance;
the probabilistic content is the `n^{-1.6}`-rate "not enough time to climb" argument. -/
def ClimbBound (θ : ℝ) (W₂ : ℕ) (c : Config (AgentState L K)) : Prop :=
  ∀ k : ℕ, frac (L := L) (K := K) k c < θ → rBeyond (L := L) (K := K) (k + W₂) c = 0

/-- **`GoodFrontWidth` from the faithful windowed pair.**  On the clock window with floor
`θ ≥ 1/card`, the windowed recurrence collapses the profile from any subcritical start (`< 1/10`)
to below the floor within `W₁ = frontWidthBound card` levels (`FrontTail.windowed_floor_crossing`),
and the climb bound empties everything `W₂` levels further up — yielding the moving-frame width
invariant at width `W₁ + W₂`.  This is the faithful replacement for `goodFrontWidth_of_profile`
(whose unrestricted hypothesis is not whp-dischargeable). -/
theorem goodFrontWidth_of_windowed_profile_and_climb
    (θ : ℝ) (W₂ : ℕ) (c : Config (AgentState L K)) (hcard : 2 ≤ c.card)
    (hall : AllClockP3 (L := L) (K := K) c)
    (hθ : 1 / (c.card : ℝ) ≤ θ)
    (hwp : WindowedFrontProfile (L := L) (K := K) θ c)
    (hcb : ClimbBound (L := L) (K := K) θ W₂ c) :
    GoodFrontWidth (L := L) (K := K) (FrontTail.frontWidthBound c.card + W₂) c := by
  have hcardpos : 0 < c.card := by omega
  have hcardℝ : (0 : ℝ) < (c.card : ℝ) := by exact_mod_cast hcardpos
  set W₁ := FrontTail.frontWidthBound c.card with hW₁
  intro i hi
  by_cases hiW : i ≤ W₁ + W₂
  · -- i ≤ W₁ + W₂ ⟹ i − (W₁+W₂) = 0 ⟹ rBeyond 0 c = card (all agents are clocks).
    have hzero : i - (W₁ + W₂) = 0 := by omega
    rw [hzero]
    have hr0 : rBeyond (L := L) (K := K) 0 c = c.card := by
      unfold rBeyond
      rw [Multiset.countP_eq_card]
      intro a ha
      exact ⟨(hall a ha).1, Nat.zero_le _⟩
    rw [hr0]; omega
  · by_contra hcon
    rw [not_le] at hcon  -- 10 * rBeyond (i − (W₁+W₂)) c < c.card
    set base := i - (W₁ + W₂) with hbase
    set f : ℕ → ℝ := fun j => frac (L := L) (K := K) (base + j) c with hfdef
    have hfnn : ∀ j, 0 ≤ f j := by
      intro j; simp only [hfdef, frac]; positivity
    have hrec : ∀ j, θ ≤ f j → f j ≤ 1 / 10 → f (j + 1) ≤ (f j) ^ 2 := by
      intro j hlo hhi
      simp only [hfdef] at hlo hhi ⊢
      have h := hwp (base + j) hlo hhi
      rwa [show base + (j + 1) = (base + j) + 1 from by ring]
    have hf0 : f 0 ≤ 1 / 10 := by
      simp only [hfdef, Nat.add_zero, frac]
      rw [div_le_iff₀ hcardℝ]
      have : (10 : ℝ) * (rBeyond (L := L) (K := K) base c : ℝ) < (c.card : ℝ) := by
        exact_mod_cast hcon
      linarith
    -- The windowed collapse must cross the floor within W₁ levels.
    obtain ⟨j₀, hj₀le, hj₀⟩ :=
      FrontTail.windowed_floor_crossing hfnn hrec hf0 c.card hcard hθ
    simp only [hfdef] at hj₀
    -- The climb bound then empties level base + j₀ + W₂ ≤ i; rBeyond is antitone.
    have hclimb := hcb (base + j₀) hj₀
    have hle : base + j₀ + W₂ ≤ i := by omega
    have hanti := HabsDischarge.rBeyond_antitone_threshold (L := L) (K := K)
      (base + j₀ + W₂) i hle c
    omega

/-- HONEST STATUS marker: PROVEN here — the deterministic cap-safety glue
(`frontSync_of_goodWidth_of_bulk_below`), the reduction `GoodFrontWidth ⟸ GoodFrontProfile`
(`goodFrontWidth_of_profile`, kept as a theorem but its UNRESTRICTED hypothesis is not
whp-dischargeable — see the CORRECTION block), and the faithful windowed reduction
`GoodFrontWidth ⟸ WindowedFrontProfile ∧ ClimbBound`
(`goodFrontWidth_of_windowed_profile_and_climb`).  The genuine remaining residuals are
`WindowedFrontProfile` (Doty Thm 6.5's windowed recurrence, via Lemma 6.3 + the early-drip set `D`)
and `ClimbBound` (the `n^{-1.6}`-rate climb argument) — both TRUE per the paper's §6. -/
theorem clock_front_profile_status : True := trivial

end ClockFrontProfile

end ExactMajority
