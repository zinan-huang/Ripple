import Ripple.PopulationProtocol.ExactMajority.Probability.ClockSideGood
import Ripple.PopulationProtocol.ExactMajority.Probability.Params

/-!
# ClockBudgets — the explicit unconditional clock budget (Phase B-12)

This is the closing brick of Phase B.  `ClockUnconditional` (B-11) reduced the unconditional
clock to per-minute SIDE PREFIXES `∑_τ (realκ^τ) c₀ Sgood(i+1)ᶜ`, and `sidePrefix_le` decomposed
each per-`τ` mass into FOUR named feeders `εQ + εfloor + εsync + εphase`.  Here we:

1. Decompose `εphase` (`{PhaseGateFail}`) into its four structural conjunct failures — a pure
   union bound (`phaseGateFail_le`), fully proven here.
2. Wire `εsync` (`{¬FrontSync}`) to the §6 width engine via
   `ClockFrontSyncFromWidth.frontSync_whp_of_goodFrontWidth`: `εsync(τ) ≤ εW(τ) + εP(τ) + εB(τ)`,
   the width-failure / side-event / bulk-arrival split, with the per-`τ` width mass `εW(τ)`
   supplied by the §6 engine (`Params.goodFrontWidth_whp_of_escapeMass` at its endpoint horizon; a
   per-`τ` concrete width family at free `τ` is the remaining §6 follow-up — carried here as the
   named family `εW`).
3. Assemble the per-`τ` `Sgood(T)ᶜ` budget `sideEps(τ)` from the available pieces + the named
   inputs (`sidePrefix_le_assembled`).
4. **Sum** `sideEps(τ)` over the per-minute windows `Ico (i·s+tseed) (i·s+tseed+tbulk)` and over
   the `K·(L+1)−1` minutes, and feed the capstone, producing the explicit total budget
   `ε_clock(n)` (`minutes_bulkPost_failure_sum_le_εclock`).

The genuinely-open inputs are NAMED throughout: the per-`τ` width / side / bulk masses
`εW τ`, `εP τ`, `εB τ` and the deterministic-residual phase masses `εge3 τ`, `εno3 τ`,
`εcpos τ`, `εsucc τ`.  Everything else (the inclusions, the unions, the summation arithmetic) is
fully proven here.

ZERO sorry, zero new axiom, zero native_decide.
-/

namespace Ripple.PopulationProtocol.ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real BigOperators Classical

namespace ClockBudgets

open ClockSideGood ClockRealKernel ClockKilledMinute ClockRealBulk ClockRealMixed
open MixedWindowClosure ClockFrontShape ClockFrontSyncFromWidth ClockFrontProfile EarlyDripMarked

variable {L K : ℕ}

/-! ## Part 1 — the `εphase` decomposition (pure union bound, fully proven).

`PhaseGateFail c = ¬allPhaseGE3 c ∨ ¬noPhaseAbove3 c ∨ ¬allClocksCounterPos c ∨
¬(∀ c' on support, noPhaseAbove3 c')`.  The set `{PhaseGateFail}` is the union of the four
per-conjunct failure sets, so its measure is `≤` the sum of the four masses. -/

/-- The four per-conjunct failure sets whose union is `{PhaseGateFail}`. -/
def GE3Fail : Set (Config (AgentState L K)) :=
  {c | ¬ allPhaseGE3 (L := L) (K := K) c}

def NoAbove3Fail : Set (Config (AgentState L K)) :=
  {c | ¬ noPhaseAbove3 (L := L) (K := K) c}

def CposFail : Set (Config (AgentState L K)) :=
  {c | ¬ allClocksCounterPos (L := L) (K := K) c}

def SuccNoAbove3Fail : Set (Config (AgentState L K)) :=
  {c | ¬ (∀ c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support,
      noPhaseAbove3 (L := L) (K := K) c')}

/-- **`phaseGateFail_subset`** — `{PhaseGateFail}` is covered by the union of the four
per-conjunct failures. -/
theorem phaseGateFail_subset :
    {c : Config (AgentState L K) | PhaseGateFail (L := L) (K := K) c} ⊆
      (GE3Fail (L := L) (K := K) ∪ NoAbove3Fail (L := L) (K := K))
        ∪ (CposFail (L := L) (K := K) ∪ SuccNoAbove3Fail (L := L) (K := K)) := by
  intro c hc
  simp only [Set.mem_setOf_eq, PhaseGateFail, Set.mem_union,
    GE3Fail, NoAbove3Fail, CposFail, SuccNoAbove3Fail] at hc ⊢
  tauto

/-- **`phaseGateFail_le`** — the per-`τ` `{PhaseGateFail}` mass is bounded by the sum of the four
named per-conjunct masses.  Pure union bound. -/
theorem phaseGateFail_le (τ : ℕ) (c₀ : Config (AgentState L K))
    (εge3 εno3 εcpos εsucc : ℝ≥0∞)
    (hge3 : (realκ L K ^ τ) c₀ (GE3Fail (L := L) (K := K)) ≤ εge3)
    (hno3 : (realκ L K ^ τ) c₀ (NoAbove3Fail (L := L) (K := K)) ≤ εno3)
    (hcpos : (realκ L K ^ τ) c₀ (CposFail (L := L) (K := K)) ≤ εcpos)
    (hsucc : (realκ L K ^ τ) c₀ (SuccNoAbove3Fail (L := L) (K := K)) ≤ εsucc) :
    (realκ L K ^ τ) c₀ {c | PhaseGateFail (L := L) (K := K) c}
      ≤ εge3 + εno3 + εcpos + εsucc := by
  have hbound : (realκ L K ^ τ) c₀ {c | PhaseGateFail (L := L) (K := K) c}
      ≤ (εge3 + εno3) + (εcpos + εsucc) := by
    refine le_trans (measure_mono (phaseGateFail_subset (L := L) (K := K))) ?_
    refine le_trans (measure_union_le _ _) ?_
    exact add_le_add (le_trans (measure_union_le _ _) (add_le_add hge3 hno3))
      (le_trans (measure_union_le _ _) (add_le_add hcpos hsucc))
  calc (realκ L K ^ τ) c₀ {c | PhaseGateFail (L := L) (K := K) c}
      ≤ (εge3 + εno3) + (εcpos + εsucc) := hbound
    _ = εge3 + εno3 + εcpos + εsucc := by ring

/-! ## Part 2 — the `εsync` wiring to the §6 width engine.

`ClockFrontSyncFromWidth.frontSync_whp_of_goodFrontWidth` bounds `{¬ FrontSync}` at horizon `τ`
by `εW + εP + εB` — the width-failure-on-side mass `εW` (supplied by the §6 engine
`goodFrontWidth_whp`), the side-event failure `εP`, and the bulk-arrival mass `εB`.  `SyncFail`
(from `ClockUnconditional`) is exactly `{c | ¬ FrontSync c}`, and `realκ L K` is definitionally
`(NonuniformMajority L K).transitionKernel`, so the bridge applies directly. -/

/-- **`syncFail_le`** — the per-`τ` `SyncFail` (`{¬ FrontSync}`) mass is `≤ εW + εP + εB`, the
§6 width / side-event / bulk-arrival split.  Direct restatement of
`frontSync_whp_of_goodFrontWidth` in the `realκ`/`SyncFail` shape used by `sidePrefix_le`. -/
theorem syncFail_le (τ W : ℕ) (c₀ : Config (AgentState L K))
    (P : Config (AgentState L K) → Prop) (εW εP εB : ℝ≥0∞)
    (hwidth : (realκ L K ^ τ) c₀
        {c | P c ∧ ¬ GoodFrontWidth (L := L) (K := K) W c} ≤ εW)
    (hP : (realκ L K ^ τ) c₀ {c | ¬ P c} ≤ εP)
    (hbulk : (realκ L K ^ τ) c₀
        {c | ¬ (10 * rBeyond (L := L) (K := K)
            (capMinute (L := L) (K := K) - W) c < c.card)} ≤ εB) :
    (realκ L K ^ τ) c₀ (SyncFail (L := L) (K := K)) ≤ εW + εP + εB :=
  frontSync_whp_of_goodFrontWidth (L := L) (K := K) τ W c₀ P εW εP εB hwidth hP hbulk

/-! ## Part 3 — the assembled per-`τ` `Sgood(T)ᶜ` budget.

Combine `ClockSideGood.sidePrefix_le` (`Sgood(T)ᶜ ≤ εQ + εfloor + εsync + εphase`) with the
Part-2 `εsync = εW + εP + εB` and Part-1 `εphase = εge3 + εno3 + εcpos + εsucc`, producing the
per-`τ` budget entirely in terms of the named feeders.  Every input here is either fully proven
upstream or a genuinely-open named whp mass; the assembly is pure measure arithmetic. -/

/-- The fully assembled per-`τ` side budget: the sum of all NINE named feeders. -/
noncomputable def sideEps (εQ εfloor εW εP εB εge3 εno3 εcpos εsucc : ℝ≥0∞) : ℝ≥0∞ :=
  εQ + εfloor + (εW + εP + εB) + (εge3 + εno3 + εcpos + εsucc)

/-- **`sidePrefix_le_assembled`** — the per-`τ` `Sgood(T)ᶜ` mass `≤ sideEps`, all four
`sidePrefix_le` feeders resolved through their dischargers: `εsync` via `syncFail_le`
(Part 2), `εphase` via `phaseGateFail_le` (Part 1). -/
theorem sidePrefix_le_assembled (n mC T τ W : ℕ) (c₀ : Config (AgentState L K))
    (P : Config (AgentState L K) → Prop)
    (εQ εfloor εW εP εB εge3 εno3 εcpos εsucc : ℝ≥0∞)
    (hQ : (realκ L K ^ τ) c₀ (QmixFail (L := L) (K := K) n mC T) ≤ εQ)
    (hfloor : (realκ L K ^ τ) c₀ (FloorFail (L := L) (K := K) mC T) ≤ εfloor)
    (hwidth : (realκ L K ^ τ) c₀
        {c | P c ∧ ¬ GoodFrontWidth (L := L) (K := K) W c} ≤ εW)
    (hP : (realκ L K ^ τ) c₀ {c | ¬ P c} ≤ εP)
    (hbulk : (realκ L K ^ τ) c₀
        {c | ¬ (10 * rBeyond (L := L) (K := K)
            (capMinute (L := L) (K := K) - W) c < c.card)} ≤ εB)
    (hge3 : (realκ L K ^ τ) c₀ (GE3Fail (L := L) (K := K)) ≤ εge3)
    (hno3 : (realκ L K ^ τ) c₀ (NoAbove3Fail (L := L) (K := K)) ≤ εno3)
    (hcpos : (realκ L K ^ τ) c₀ (CposFail (L := L) (K := K)) ≤ εcpos)
    (hsucc : (realκ L K ^ τ) c₀ (SuccNoAbove3Fail (L := L) (K := K)) ≤ εsucc) :
    (realκ L K ^ τ) c₀ (Sgood (L := L) (K := K) n mC T)ᶜ
      ≤ sideEps εQ εfloor εW εP εB εge3 εno3 εcpos εsucc :=
  sidePrefix_le (L := L) (K := K) n mC T τ c₀
    εQ εfloor (εW + εP + εB) (εge3 + εno3 + εcpos + εsucc)
    hQ hfloor
    (syncFail_le (L := L) (K := K) τ W c₀ P εW εP εB hwidth hP hbulk)
    (phaseGateFail_le (L := L) (K := K) τ c₀ εge3 εno3 εcpos εsucc hge3 hno3 hcpos hsucc)

/-! ## Part 4 — the summation over the minute windows → the explicit `ε_clock(n)`.

The capstone `clock_real_faithful_O_log_n_sideGood` bounds the total failure by
`∑_{i : Fin (K(L+1)−1)} (εbulk + (tbulk·0 + ∑_{τ ∈ Ico (i·s+tseed) (i·s+tseed+tbulk)}
(realκ^τ) c₀ Sgood(i+1)ᶜ))` where `s = tseed + tbulk`.  Given a UNIFORM per-`τ`/per-minute side
bound `εside` (`∀ T τ, (realκ^τ) c₀ Sgood(T)ᶜ ≤ εside` — assembled from `sideEps` once the named
feeders are bounded uniformly), each inner window sum is `≤ tbulk · εside` (a `Finset.Ico` of
length `tbulk`), so the full bound collapses to `(K(L+1)−1) · (εbulk + tbulk · εside)`. -/

/-- The explicit total clock budget: `(#minutes) · (per-minute bulk tail + tbulk · per-step side
mass)`, with `#minutes = K·(L+1) − 1`. -/
noncomputable def εclock (L K tbulk : ℕ) (εbulk εside : ℝ≥0∞) : ℝ≥0∞ :=
  (K * (L + 1) - 1 : ℕ) * (εbulk + (tbulk : ℝ≥0∞) * εside)

/-- **Inner window sum ≤ tbulk · εside.**  A `Finset.Ico a (a+tbulk)` has card `tbulk`; with a
uniform per-`τ` side bound `εside`, the sum is `≤ tbulk · εside`. -/
theorem window_sum_le (n mC T a tbulk : ℕ) (c₀ : Config (AgentState L K)) (εside : ℝ≥0∞)
    (hside : ∀ τ, (realκ L K ^ τ) c₀ (Sgood (L := L) (K := K) n mC T)ᶜ ≤ εside) :
    ∑ τ ∈ Finset.Ico a (a + tbulk),
        (realκ L K ^ τ) c₀ (Sgood (L := L) (K := K) n mC T)ᶜ
      ≤ (tbulk : ℝ≥0∞) * εside := by
  calc ∑ τ ∈ Finset.Ico a (a + tbulk),
        (realκ L K ^ τ) c₀ (Sgood (L := L) (K := K) n mC T)ᶜ
      ≤ ∑ _τ ∈ Finset.Ico a (a + tbulk), εside :=
        Finset.sum_le_sum (fun τ _ => hside τ)
    _ = (Finset.Ico a (a + tbulk)).card • εside := by rw [Finset.sum_const]
    _ = (tbulk : ℝ≥0∞) * εside := by
        rw [Nat.card_Ico, Nat.add_sub_cancel_left, nsmul_eq_mul]

/-- **Per-minute term ≤ εbulk + tbulk · εside.**  Each summand of the capstone RHS is bounded by
`εbulk + tbulk · εside` (the `tbulk·0` escape vanishes; the inner window sum is `window_sum_le`). -/
theorem minute_term_le (n mC tseed tbulk : ℕ) (c₀ : Config (AgentState L K)) (εbulk εside : ℝ≥0∞)
    (i : ℕ)
    (hside : ∀ τ, (realκ L K ^ τ) c₀
        (Sgood (L := L) (K := K) n mC (i + 1))ᶜ ≤ εside) :
    εbulk + ((tbulk : ℝ≥0∞) * 0
        + ∑ τ ∈ Finset.Ico (i * (tseed + tbulk) + tseed)
            (i * (tseed + tbulk) + tseed + tbulk),
            (realκ L K ^ τ) c₀ (Sgood (L := L) (K := K) n mC (i + 1))ᶜ)
      ≤ εbulk + (tbulk : ℝ≥0∞) * εside := by
  have hwin := window_sum_le (L := L) (K := K) n mC (i + 1)
    (i * (tseed + tbulk) + tseed) tbulk c₀ εside hside
  rw [mul_zero, zero_add]
  exact add_le_add (le_refl εbulk) hwin

/-- **The full minute-sum collapse.**  Given a uniform per-`τ`/per-minute side bound `εside`, the
capstone RHS `∑_{i : Fin (K(L+1)−1)} (per-minute term)` is `≤ (K(L+1)−1) · (εbulk + tbulk·εside)
= εclock`. -/
theorem minutes_sum_le (n mC tseed tbulk : ℕ) (c₀ : Config (AgentState L K)) (εbulk εside : ℝ≥0∞)
    (hside : ∀ T τ, (realκ L K ^ τ) c₀ (Sgood (L := L) (K := K) n mC T)ᶜ ≤ εside) :
    ∑ i : Fin (K * (L + 1) - 1), (εbulk + ((tbulk : ℝ≥0∞) * 0
        + ∑ τ ∈ Finset.Ico (i.val * (tseed + tbulk) + tseed)
            (i.val * (tseed + tbulk) + tseed + tbulk),
            (realκ L K ^ τ) c₀ (Sgood (L := L) (K := K) n mC (i.val + 1))ᶜ))
      ≤ εclock L K tbulk εbulk εside := by
  calc ∑ i : Fin (K * (L + 1) - 1), (εbulk + ((tbulk : ℝ≥0∞) * 0
        + ∑ τ ∈ Finset.Ico (i.val * (tseed + tbulk) + tseed)
            (i.val * (tseed + tbulk) + tseed + tbulk),
            (realκ L K ^ τ) c₀ (Sgood (L := L) (K := K) n mC (i.val + 1))ᶜ))
      ≤ ∑ _i : Fin (K * (L + 1) - 1), (εbulk + (tbulk : ℝ≥0∞) * εside) :=
        Finset.sum_le_sum (fun i _ =>
          minute_term_le (L := L) (K := K) n mC tseed tbulk c₀ εbulk εside i.val
            (fun τ => hside (i.val + 1) τ))
    _ = (Finset.univ : Finset (Fin (K * (L + 1) - 1))).card • (εbulk + (tbulk : ℝ≥0∞) * εside) := by
        rw [Finset.sum_const]
    _ = εclock L K tbulk εbulk εside := by
        rw [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; rfl

/-! ## Part 5 — `minutes_bulkPost_failure_sum_le_εclock`: the explicit unconditional clock bound.

The capstone `clock_real_faithful_O_log_n_sideGood` (from `ClockUnconditional`) bounds the
total minute-failure by the per-minute side-prefix sum.  Composed with `minutes_sum_le`, the
total failure is `≤ εclock L K tbulk εbulk εside`, an explicit `(K(L+1)−1) · (εbulk + tbulk·εside)`
budget.  The ONLY remaining input is the uniform per-`τ`/per-minute side bound `εside` — the §6
named family `sideEps` made uniform (its nine feeders bounded uniformly across the run, the
genuinely-open §6 follow-up: per-`τ` concrete width family at free `τ` + the deterministic-residual
phase masses). -/

/-- **`minutes_bulkPost_failure_sum_le_εclock` — the explicit unconditional O(log n) clock budget.**

The `q = 0`, `habs_mix`-free faithful clock with the per-minute side prefixes SUMMED into the
single explicit budget `εclock = (K(L+1)−1) · (εbulk + tbulk · εside)`.  The total minute-failure
mass over all `K(L+1)−1` bulk minutes is `≤ εclock`.

### Hypothesis list (every genuinely-open named input).
* `(n mC : ℕ) (hn : 2 ≤ n) (hmC : 2 ≤ mC) (hLK : 0 < K·(L+1))` — population / clock-size scale.
* `(tseed tbulk : ℕ) (htbulk : 0 < tbulk)` — the per-minute seed/bulk interaction counts.
* `(εbulk : ℝ≥0) (hεb : minuteRate-tail ≤ εbulk)` — the per-minute bulk-crossing tail (B-9).
* `(εside : ℝ≥0∞) (hside : ∀ T τ, (realκ^τ) c₀ Sgood(T)ᶜ ≤ εside)` — **the uniform per-`τ` side
  budget**: the GENUINELY-OPEN input, assembled from `sideEps` (Part 3) once each of its nine
  named feeders (`εQ εfloor εW εP εB εge3 εno3 εcpos εsucc`) is bounded uniformly across the run by
  its discharger (`goodFrontWidth_whp_of_escapeMass` + the `ClockFrontSyncFromWidth` bridges + the
  deterministic phase-gate closures).
* `(c₀ : Cfg L K)` — the protocol start. -/
theorem minutes_bulkPost_failure_sum_le_εclock (n mC : ℕ) (hn : 2 ≤ n) (hmC : 2 ≤ mC)
    (hLK : 0 < K * (L + 1))
    (tseed tbulk : ℕ) (htbulk : 0 < tbulk) (εbulk : ℝ≥0)
    (hεb : minuteRate n mC ^ tbulk *
        ENNReal.ofReal (Real.exp (Real.log 2 * (bulkHi mC : ℝ))) / 1 ≤ (εbulk : ℝ≥0∞))
    (c₀ : Config (AgentState L K)) (εside : ℝ≥0∞)
    (hside : ∀ T τ, (realκ L K ^ τ) c₀ (Sgood (L := L) (K := K) n mC T)ᶜ ≤ εside) :
    ∑ i : Fin (K * (L + 1) - 1),
        ((realκ L K) ^ (i.val * (tseed + tbulk) + tseed + tbulk)) c₀
          {c | ¬ BulkPost (L := L) (K := K) n mC (i.val + 1) c}
      ≤ εclock L K tbulk (εbulk : ℝ≥0∞) εside :=
  le_trans
    (clock_real_faithful_O_log_n_sideGood (L := L) (K := K) n mC hn hmC hLK
      tseed tbulk htbulk εbulk hεb c₀)
    (minutes_sum_le (L := L) (K := K) n mC tseed tbulk c₀ (εbulk : ℝ≥0∞) εside hside)

/-! ## Part 6 — `widthFail_concrete`: the §6 width-failure mass `εW` at the endpoint horizon.

The §6 concrete chain (`Params.goodFrontWidth_whp_of_escapeMass`) delivers the moving-frame width
invariant whp at the SINGLE endpoint horizon `τ = w n · KK L K` (the per-hour window — the
checkpoint machinery is locked to this window structure; a per-`τ` family at free `τ` is the
remaining §6 follow-up).  At that horizon the width-failure-on-side mass `εW` IS supplied
concretely.  Here we name it: with `P` = the §6 side conjunct (`card = n ∧ AllClockP3 ∧ the
neg-taint bound`) and `W = frontWidthBound n + W₂`, the bridge `syncFail_le` consumes exactly this
`εW`.

`widthFail_concrete` is the concrete `εW`: a thin restatement of `goodFrontWidth_whp_of_escapeMass` in the
`realκ`-power shape, fixing `εW := (Tcap·(KK·deltaB + (eB+tB))) + climbB`. -/

/-- The §6 side conjunct `P` carried inside the concrete width event. -/
def WidthSideP (n : ℕ) (c : Config (AgentState L K)) : Prop :=
  c.card = n ∧ AllClockP3 (L := L) (K := K) c ∧
    (∀ T, Params.θ n ≤ ClockFrontProfile.frac (L := L) (K := K) T c →
      (9/10 : ℝ) * (rBeyond (L := L) (K := K) T c : ℝ) ^ 2 / (n : ℝ) + (Params.tt n : ℝ)
        ≤ (rBeyond (L := L) (K := K) T c : ℝ) ^ 2 / (n : ℝ))

/-- **`widthFail_concrete`** — the concrete width-failure-on-side mass `εW` at the endpoint
horizon `w n · KK L K`, from the §6 engine `goodFrontWidth_whp_of_escapeMass`.  This is the genuine
concrete `εW` feeding `syncFail_le` (at `W = frontWidthBound n + W₂`, `P = WidthSideP n`). -/
theorem widthFail_concrete (n : ℕ) (hn : Params.N₀ ≤ n)
    (mc₀ : Config (MarkedAgent L K))
    (hcard : mc₀.card = n)
    (hge3 : AllClockGE3 (L := L) (K := K) (eraseConfig (L := L) (K := K) mc₀))
    (hnotP3 : ¬ AllClockP3 (L := L) (K := K) (eraseConfig (L := L) (K := K) mc₀))
    (hclean : ∀ m ∈ mc₀, m.2 = false)
    (Tcap : ℕ) (hcapT : ClockFrontShape.capMinute (L := L) (K := K) < Tcap)
    (eB tB : ℝ≥0∞)
    (heB : ∀ T < Tcap,
      (GatedDrift.killK (markedK (L := L) (K := K) T (Params.θn n))
          (taintedGate (L := L) (K := K) n) ^ (Params.w n * Params.KK L K))
          (some mc₀) {none} ≤ eB)
    (htB : ∀ T < Tcap,
      ENNReal.ofReal
        (Real.exp (Params.σ (L := L) (K := K) n
            * (1 + 4 / (n : ℝ)) ^ (Params.w n * Params.KK L K)
            * (taintedCount (L := L) (K := K) mc₀ : ℝ)
          + 2 * Params.σ (L := L) (K := K) n
              * (1 + 4 / (n : ℝ)) ^ (Params.w n * Params.KK L K)
              * ((Params.θn n : ℝ) / (n : ℝ)) ^ 2
              * ((Params.w n * Params.KK L K : ℕ) : ℝ)
          - Params.σ (L := L) (K := K) n * ((Params.tt n + 1 : ℕ) : ℝ))) ≤ tB)
    (W₂ : ℕ) (climbB : ℝ≥0∞)
    (hclimbB : (realκ L K ^ (Params.w n * Params.KK L K))
        (eraseConfig (L := L) (K := K) mc₀)
        {c | (c.card = n ∧ AllClockP3 (L := L) (K := K) c)
          ∧ ¬ ClimbBound (L := L) (K := K) (Params.θ n) W₂ c} ≤ climbB) :
    (realκ L K ^ (Params.w n * Params.KK L K))
        (eraseConfig (L := L) (K := K) mc₀)
        {c | WidthSideP (L := L) (K := K) n c ∧
          ¬ GoodFrontWidth (L := L) (K := K) (FrontTail.frontWidthBound n + W₂) c}
      ≤ ((Tcap : ℝ≥0∞) * ((Params.KK L K : ℝ≥0∞) * Params.deltaB n + (eB + tB)))
          + climbB :=
  Params.goodFrontWidth_whp_of_escapeMass (L := L) (K := K) n hn mc₀ hcard hge3 hnotP3 hclean
    Tcap hcapT eB tB heB htB W₂ climbB hclimbB

end ClockBudgets

end Ripple.PopulationProtocol.ExactMajority
