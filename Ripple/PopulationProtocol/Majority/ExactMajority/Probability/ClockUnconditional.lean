import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ClockWeakAssembly
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.FrontSyncConc
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ClockFrontSyncFromWidth

/-!
# ClockUnconditional — the final Phase B wiring (B-11)

This is the last connector of the Phase B campaign.  `ClockWeakAssembly` (B-10) reduced the
unconditional clock to TWO named residuals carried on the endpoint
`clock_real_faithful_O_log_n_W`:

1. `hstep : ∀ T, ∀ x ∈ QbulkSet n mC T, realκ x QbulkSetᶜ ≤ q` — the per-step gate-escape rate;
2. the per-minute side prefixes `∑_{τ} (realκ^τ) c₀ QbulkSet(i)ᶜ` left in the conclusion RHS.

This file wires both to the discharged machinery.

## The honest split (the §6 side-gate audit, settled)

`QbulkSet n mC T = {Q_mix n mC T ∧ mC/10 ≤ rBeyond (T+1)}`, with `Q_mix` = `card ∧ clockPhase3 ∧
clockSize ∧ crossedT`.  The one-step escape `realκ x QbulkSetᶜ` decomposes per conjunct:

* `card`, `clockSize`, `crossedT` (`T ≥ 1`), `allPhaseGE3` close DETERMINISTICALLY on the support
  (`HabsDischarge.habs_mix_deterministic_skeleton`) — they contribute `0` to the escape.
* the `mC/10` floor at `T+1` is MONOTONE on the support
  (`ClockMonoDischarge.hmono_mix_discharged`) — contributes `0`.
* `clockPhase3` (clocks stay at phase EXACTLY 3) closes one step ONLY on the FrontSync-good window
  (`FrontSyncConc.habs_mix_full`): under `allPhaseGE3 ∧ noPhaseAbove3 ∧ allClocksCounterPos ∧
  FrontSync` (with the successor `noPhaseAbove3 c'`), every successor lies in `Q_mix` AND keeps
  `allClocksCounterPos`.  The bare deterministic closure is FALSE (the at-cap `counter = 1`
  witness, `ClockFrontShape.counterPos_one_step_NOT_closed_witness`); FrontSync is the ESSENTIAL
  gate, supplied PROBABILISTICALLY by the §6 width engine.

**The result of the split: `q = 0`.**  We condition the one-step escape on a SIDE EVENT
`HabsGood T` (the full `habs_mix_full` gate, plus the deterministic successor `noPhaseAbove3`
gate folded in).  On `QbulkSet n mC T ∩ HabsGood T`, EVERY successor lies in `QbulkSet n mC T`,
so the one-step escape is exactly `0`.  Per the campaign blueprint's directive
("if it cannot be discharged deterministically, keep it INSIDE the side event and the escape
charges to the side prefix failures instead: then `q = 0` and ALL the cost moves to the side
prefixes"), we charge ALL the cost to the side prefixes by taking the side set
`S = QbulkSet ∩ HabsGood` and `q = 0`.

`ClockWeakAssembly`'s endpoint takes `hstep` with `S = G = QbulkSet` (unconditioned), so to use
the `q = 0` route honestly we restate the assembly with `S = QbulkSet ∩ HabsGood` and the
side-conditioned `hstep` (the campaign-mandated "S-conditioned variant theorem IN YOUR FILE,
do not edit ClockWeakAssembly").  The per-minute side prefix then becomes
`∑_τ (realκ^τ) c₀ (QbulkSet ∩ HabsGood)ᶜ`, whose failure events are exactly the §6 whp pieces
(width / FrontSync / the deterministic phase gates), discharged later by `goodFrontWidth_whp_at`
+ the `ClockFrontSyncFromWidth` bridges + `Params`.

ZERO sorry, zero new axiom, zero native_decide.
-/

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real BigOperators Classical

namespace ClockUnconditional

open ClockRealKernel ClockKilledMinute ClockRealBulk ClockRealMixed
open HabsDischarge ClockFrontShape FrontSyncConc ClockMonoDischarge

variable {L K : ℕ}

/-- The cemetery extension carries the discrete (`⊤`) measurable space (matching
`GatedKillNow`'s / `ClockKilledMinute`'s / `ClockWeakAssembly`'s local instances). -/
local instance instOptionMScu : MeasurableSpace (Option (Cfg L K)) := ⊤
local instance instOptionDMScu : DiscreteMeasurableSpace (Option (Cfg L K)) :=
  ⟨fun _ => trivial⟩

/-! ## Part 1 — the side event `HabsGood` and the `q = 0` one-step escape.

`HabsGood T c` carries EXACTLY the gates `FrontSyncConc.habs_mix_full` needs to close `Q_mix`
one step (plus the maintained `allClocksCounterPos`), PLUS the deterministic successor
`noPhaseAbove3` gate (`∀ c' on support, noPhaseAbove3 c'`).  With these gates the one-step image
of `QbulkSet ∩ HabsGood` lies entirely in `QbulkSet`, so the escape mass on `QbulkSetᶜ` is `0`. -/

/-- The side event under which the one-step gate-escape rate is `0`.  All four conjuncts are
exactly the `habs_mix_full` gate; the last is the deterministic successor `noPhaseAbove3` gate
(the residual deterministic closure that the §6 audit folds into the side event).  NOTE: the
gate is MINUTE-INDEPENDENT (it does not mention `T`) — the §6 side gates are structural, not
per-minute, so a SINGLE side event `HabsGood` serves every minute. -/
def HabsGood (c : Config (AgentState L K)) : Prop :=
  allPhaseGE3 (L := L) (K := K) c ∧
    noPhaseAbove3 (L := L) (K := K) c ∧
    allClocksCounterPos (L := L) (K := K) c ∧
    FrontSync (L := L) (K := K) c ∧
    (∀ c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support,
      noPhaseAbove3 (L := L) (K := K) c')

/-- **The one-step image of `QbulkSet ∩ HabsGood` lands in `QbulkSet` (per config on the
support).**  From `x ∈ QbulkSet ∩ HabsGood T` (with `1 ≤ T`), every support successor `c'`
satisfies `QbulkWin n mC T c'`, i.e. `c' ∈ QbulkSet n mC T`.  `Q_mix c'` is `habs_mix_full`; the
`mC/10` floor is `hmono_mix_discharged`. -/
theorem qbulk_succ_of_sideGood (n mC T : ℕ) (hT : 1 ≤ T)
    (x : Config (AgentState L K))
    (hx : x ∈ QbulkSet (L := L) (K := K) n mC T ∩ {c | HabsGood (L := L) (K := K) c})
    (c' : Config (AgentState L K))
    (hc' : c' ∈ ((NonuniformMajority L K).stepDistOrSelf x).support) :
    c' ∈ QbulkSet (L := L) (K := K) n mC T := by
  classical
  obtain ⟨hQbw, hge, hno, hpos, hsync, hno'all⟩ := hx
  have hQbw : QbulkWin (L := L) (K := K) n mC T x := hQbw
  obtain ⟨hQ, hfloor⟩ := hQbw
  -- successor noPhaseAbove3 (the carried deterministic gate).
  have hno' : noPhaseAbove3 (L := L) (K := K) c' := hno'all c' hc'
  -- Q_mix c' from the FrontSync-gated closure.
  have hclose := habs_mix_full (L := L) (K := K) n mC T hT x c' hQ hge hno hpos hsync hno' hc'
  -- the mC/10 floor at T+1 is monotone on the support.
  have hmono := hmono_mix_discharged (L := L) (K := K) n mC T x c' hQ hc'
  exact ⟨hclose.1, le_trans hfloor hmono⟩

/-- **`hstep_of_sideGood` (q = 0).**  On `x ∈ QbulkSet n mC T ∩ HabsGood T` (with `1 ≤ T`), the
one-step real-kernel escape to `QbulkSetᶜ` is exactly `0`.  This is the honest `hstep` with
`q = 0` and the cost moved entirely to the side event `HabsGood`. -/
theorem hstep_of_sideGood (n mC T : ℕ) (hT : 1 ≤ T)
    (x : Config (AgentState L K))
    (hx : x ∈ QbulkSet (L := L) (K := K) n mC T ∩ {c | HabsGood (L := L) (K := K) c}) :
    realκ L K x (QbulkSet (L := L) (K := K) n mC T)ᶜ = 0 := by
  classical
  show ((NonuniformMajority L K).transitionKernel) x
      (QbulkSet (L := L) (K := K) n mC T)ᶜ = 0
  change ((NonuniformMajority L K).stepDistOrSelf x).toMeasure
      (QbulkSet (L := L) (K := K) n mC T)ᶜ = 0
  rw [PMF.toMeasure_apply_eq_zero_iff _
    (DiscreteMeasurableSpace.forall_measurableSet _)]
  rw [Set.disjoint_left]
  intro c' hsupp hbad
  exact hbad (qbulk_succ_of_sideGood (L := L) (K := K) n mC T hT x hx c' hsupp)

/-! ## Part 2 — the S-conditioned bulk leg + minute (the `q = 0` assembly variant).

`ClockWeakAssembly`'s `clock_real_bulk_leg_avg` is stated with `S = G = QbulkSet` (the
unconditioned `hstep`).  Here we re-derive it with `S = QbulkSet ∩ HabsGood` and `q = 0`,
charging ALL the escape to the side prefix `∑_τ (realκ^τ) c₀ (QbulkSet ∩ HabsGood)ᶜ` (the
campaign-mandated S-conditioned variant; `ClockWeakAssembly` is NOT edited).

The proof mirrors `clock_real_bulk_leg_avg` verbatim, EXCEPT the escape integral is bounded by
`ClockWeakAssembly.leg_escape_global` at `S = QbulkSet ∩ HabsGood`, `q = 0`, with `hstep` =
`hstep_of_sideGood` (the `0 ≤ q` side-conditioned escape) and `hSG : Gᶜ ⊆ Sᶜ` =
`Set.compl_subset_compl.2 Set.inter_subset_left`. -/

/-- The side set: the bulk gate intersected with the structural side event `HabsGood`. -/
def Sgood (n mC T : ℕ) : Set (Config (AgentState L K)) :=
  QbulkSet (L := L) (K := K) n mC T ∩ {c | HabsGood (L := L) (K := K) c}

/-- `Sgood ⊆ QbulkSet`, hence `QbulkSetᶜ ⊆ Sgoodᶜ` (the `hSG` side condition of
`leg_escape_global`). -/
theorem qbulkSet_compl_subset_Sgood_compl (n mC T : ℕ) :
    (QbulkSet (L := L) (K := K) n mC T)ᶜ ⊆ (Sgood (L := L) (K := K) n mC T)ᶜ :=
  Set.compl_subset_compl.2 Set.inter_subset_left

/-- **`clock_real_bulk_leg_avg_sideGood` — the real BULK leg with `q = 0`, escape charged to the
`Sgood` prefix.**  Mirror of `ClockWeakAssembly.clock_real_bulk_leg_avg` at `S = Sgood`,
`q = 0`. -/
theorem clock_real_bulk_leg_avg_sideGood (n mC T : ℕ) (hn : 2 ≤ n) (hmC : 2 ≤ mC)
    (hT1 : 1 ≤ T)
    (hT : T < K * (L + 1)) (M : ℕ) (hM : 0 < M) (εbulk : ℝ≥0)
    (hεb : minuteRate n mC ^ M *
        ENNReal.ofReal (Real.exp (Real.log 2 * (bulkHi mC : ℝ))) / 1 ≤ (εbulk : ℝ≥0∞))
    (Tstart : ℕ) (c₀ : Config (AgentState L K)) :
    (∫⁻ y, ((realκ L K) ^ M) y {c | ¬ BulkPost (L := L) (K := K) n mC T c}
        ∂((realκ L K ^ Tstart) c₀))
      ≤ (εbulk : ℝ≥0∞)
        + ((M : ℝ≥0∞) * 0
          + ∑ τ ∈ Finset.Ico Tstart (Tstart + M),
              (realκ L K ^ τ) c₀ (Sgood (L := L) (K := K) n mC T)ᶜ) := by
  classical
  set bad : Config (AgentState L K) → Prop := fun c => ¬ BulkPost (L := L) (K := K) n mC T c
    with hbad
  set G : Set (Config (AgentState L K)) := QbulkSet (L := L) (K := K) n mC T with hG
  calc ∫⁻ y, ((realκ L K) ^ M) y {c | bad c} ∂((realκ L K ^ Tstart) c₀)
      ≤ ∫⁻ y, ((κQ_now_bulk (L := L) (K := K) n mC T) ^ M) (some y)
          {o | o = none ∨ (∃ c, o = some c ∧ bad c)} ∂((realκ L K ^ Tstart) c₀) := by
        apply lintegral_mono
        intro y
        exact GatedDrift.real_le_killed_now (K := realκ L K) (G := G) bad M y
    _ ≤ ∫⁻ y, (((κQ_now_bulk (L := L) (K := K) n mC T) ^ M) (some y) {(none : Option (Cfg L K))}
          + ((κQ_now_bulk (L := L) (K := K) n mC T) ^ M) (some y)
              {o | ¬ optLift (BulkPost (L := L) (K := K) n mC T) o})
          ∂((realκ L K ^ Tstart) c₀) := by
        apply lintegral_mono
        intro y
        refine le_trans (measure_mono ?_) (measure_union_le _ _)
        intro o ho
        rcases ho with hnone | ⟨c, rfl, hbadc⟩
        · exact Or.inl (by rw [Set.mem_singleton_iff]; exact hnone)
        · exact Or.inr (show ¬ optLift (BulkPost (L := L) (K := K) n mC T) (some c) from hbadc)
    _ = (∫⁻ y, ((κQ_now_bulk (L := L) (K := K) n mC T) ^ M) (some y) {(none : Option (Cfg L K))}
            ∂((realκ L K ^ Tstart) c₀))
        + (∫⁻ y, ((κQ_now_bulk (L := L) (K := K) n mC T) ^ M) (some y)
              {o | ¬ optLift (BulkPost (L := L) (K := K) n mC T) o} ∂((realκ L K ^ Tstart) c₀)) := by
        rw [MeasureTheory.lintegral_add_left (by fun_prop)]
    _ ≤ ((M : ℝ≥0∞) * 0 + ∑ τ ∈ Finset.Ico Tstart (Tstart + M),
            (realκ L K ^ τ) c₀ (Sgood (L := L) (K := K) n mC T)ᶜ) + (εbulk : ℝ≥0∞) := by
        refine add_le_add ?_ ?_
        · exact ClockWeakAssembly.leg_escape_global (K := realκ L K) (G := G)
            (S := Sgood (L := L) (K := K) n mC T) 0
            (fun x hx hxS => le_of_eq (hstep_of_sideGood (L := L) (K := K) n mC T hT1
              x ⟨hx, hxS.2⟩))
            (qbulkSet_compl_subset_Sgood_compl (L := L) (K := K) n mC T) Tstart M c₀
        · exact ClockWeakAssembly.killed_bulk_avg_le (L := L) (K := K) n mC T hn hmC hT M hM
            εbulk hεb Tstart c₀
    _ = (εbulk : ℝ≥0∞) + ((M : ℝ≥0∞) * 0
          + ∑ τ ∈ Finset.Ico Tstart (Tstart + M), (realκ L K ^ τ) c₀
              (Sgood (L := L) (K := K) n mC T)ᶜ) := by
        rw [add_comm]

/-- **`clock_real_minute_avg_sideGood` — the assembled real minute with `q = 0`.**  Mirror of
`ClockWeakAssembly.clock_real_minute_avg`; the minute is the bulk leg started after the seed
phase, escape charged to the `Sgood` prefix. -/
theorem clock_real_minute_avg_sideGood (n mC T : ℕ) (hn : 2 ≤ n) (hmC : 2 ≤ mC)
    (hT1 : 1 ≤ T) (hT : T < K * (L + 1))
    (tseed tbulk : ℕ) (htbulk : 0 < tbulk) (εbulk : ℝ≥0)
    (hεb : minuteRate n mC ^ tbulk *
        ENNReal.ofReal (Real.exp (Real.log 2 * (bulkHi mC : ℝ))) / 1 ≤ (εbulk : ℝ≥0∞))
    (Tstart : ℕ) (c₀ : Config (AgentState L K)) :
    ((realκ L K) ^ (Tstart + tseed + tbulk)) c₀
        {c | ¬ BulkPost (L := L) (K := K) n mC T c}
      ≤ (εbulk : ℝ≥0∞)
        + ((tbulk : ℝ≥0∞) * 0
          + ∑ τ ∈ Finset.Ico (Tstart + tseed) (Tstart + tseed + tbulk),
              (realκ L K ^ τ) c₀ (Sgood (L := L) (K := K) n mC T)ᶜ) := by
  classical
  rw [Kernel.pow_add_apply_eq_lintegral (realκ L K) (Tstart + tseed) tbulk c₀
    (DiscreteMeasurableSpace.forall_measurableSet _)]
  exact clock_real_bulk_leg_avg_sideGood (L := L) (K := K) n mC T hn hmC hT1 hT tbulk htbulk
    εbulk hεb (Tstart + tseed) c₀

/-! ## Part 3 — the all-minutes endpoint (over minutes `T = i.val + 1`, `i : Fin L₀`).

The minute family is indexed over `i : Fin L₀` at level `T = i.val + 1`, so `1 ≤ T` holds for
every member (the §6 `crossedT` deterministic closure needs `1 ≤ T`; minute `0` is the
phase-3-entry boundary, handled by the start conditions, NOT a bulk leg).  Each minute's bound is
the standalone `q = 0` averaged-global bulk-leg bound; "all minutes" is the union bound. -/

/-- **`minuteFailW_sideGood` — the per-minute standalone failure budget (`q = 0`, `Fin L₀`
family at level `T = i.val + 1`).** -/
theorem minuteFailW_sideGood (n mC L₀ : ℕ) (hn : 2 ≤ n) (hmC : 2 ≤ mC)
    (hL₀cap : L₀ < K * (L + 1))
    (tseed tbulk : ℕ) (htbulk : 0 < tbulk) (εbulk : ℝ≥0)
    (hεb : minuteRate n mC ^ tbulk *
        ENNReal.ofReal (Real.exp (Real.log 2 * (bulkHi mC : ℝ))) / 1 ≤ (εbulk : ℝ≥0∞))
    (c₀ : Config (AgentState L K)) (i : Fin L₀) :
    ((realκ L K) ^ (i.val * (tseed + tbulk) + tseed + tbulk)) c₀
        {c | ¬ BulkPost (L := L) (K := K) n mC (i.val + 1) c}
      ≤ (εbulk : ℝ≥0∞)
        + ((tbulk : ℝ≥0∞) * 0
          + ∑ τ ∈ Finset.Ico (i.val * (tseed + tbulk) + tseed)
              (i.val * (tseed + tbulk) + tseed + tbulk),
              (realκ L K ^ τ) c₀ (Sgood (L := L) (K := K) n mC (i.val + 1))ᶜ) :=
  clock_real_minute_avg_sideGood (L := L) (K := K) n mC (i.val + 1) hn hmC
    (by omega) (by have := i.isLt; omega) tseed tbulk htbulk εbulk hεb
    (i.val * (tseed + tbulk)) c₀

/-- **`clock_real_faithful_all_minutes_sideGood` — the all-minutes endpoint with `q = 0`,
union-bounded over minutes `T = i.val + 1`.** -/
theorem clock_real_faithful_all_minutes_sideGood (n mC L₀ : ℕ) (hn : 2 ≤ n) (hmC : 2 ≤ mC)
    (hL₀cap : L₀ < K * (L + 1))
    (tseed tbulk : ℕ) (htbulk : 0 < tbulk) (εbulk : ℝ≥0)
    (hεb : minuteRate n mC ^ tbulk *
        ENNReal.ofReal (Real.exp (Real.log 2 * (bulkHi mC : ℝ))) / 1 ≤ (εbulk : ℝ≥0∞))
    (c₀ : Config (AgentState L K)) :
    ∑ i : Fin L₀, ((realκ L K) ^ (i.val * (tseed + tbulk) + tseed + tbulk)) c₀
        {c | ¬ BulkPost (L := L) (K := K) n mC (i.val + 1) c}
      ≤ ∑ i : Fin L₀, ((εbulk : ℝ≥0∞)
          + ((tbulk : ℝ≥0∞) * 0
            + ∑ τ ∈ Finset.Ico (i.val * (tseed + tbulk) + tseed)
                (i.val * (tseed + tbulk) + tseed + tbulk),
                (realκ L K ^ τ) c₀ (Sgood (L := L) (K := K) n mC (i.val + 1))ᶜ)) :=
  Finset.sum_le_sum (fun i _ =>
    minuteFailW_sideGood (L := L) (K := K) n mC L₀ hn hmC hL₀cap tseed tbulk htbulk εbulk hεb c₀ i)

/-- **`clock_real_faithful_O_log_n_unconditional` — the CAPSTONE.**

The `habs_mix`-free, `q = 0` O(log n) faithful clock.  Instantiates the assembly variant at
`L₀ = K·(L+1) − 1` bulk minutes `T = 1 … K·(L+1)−1` (the §6 `crossedT` deterministic closure
needs `1 ≤ T`, so minute `0` is the phase-3-entry start — handled by the start conditions, not a
bulk leg — and the cap minute `K·(L+1)` is where the clocks arrive together under FrontSync).
Total interactions `(K·(L+1)−1)·(tseed+tbulk) = O(n·log n)` (parallel `/n = O(log n)`).

### Honest verdict (the FINAL Phase B state).

* The FALSE `habs_mix` deterministic window closure is GONE (already retired in `ClockWeakAssembly`).
* The per-step gate-escape rate `q` is now `0` — the entire one-step escape is DISCHARGED
  (`hstep_of_sideGood`, axiom-clean) by conditioning on the structural side event `HabsGood`
  (the §6 FrontSync gate `habs_mix_full` + the deterministic successor `noPhaseAbove3` gate).
  No `q` hypothesis survives.
* In its place, ALL the cost is in the per-minute side prefixes
  `∑_τ (realκ^τ) c₀ (Sgood n mC (i.val+1))ᶜ`, where `Sgood = QbulkSet ∩ {HabsGood}`.  These are
  LEFT in the conclusion's RHS (NOT bounded here).  They are discharged by the §6 whp machinery:
  - `QbulkSet`-failure (the `Q_mix`/floor window) ⟸ `WidthPrefix.goodFrontWidth_whp_at` + the
    `ClockFrontSyncFromWidth` bridges (`frontSync_whp_of_goodFrontWidth` etc.) + `Params`;
  - `HabsGood`-failure (the structural side gates `allPhaseGE3`/`noPhaseAbove3`/
    `allClocksCounterPos`/`FrontSync` + the successor `noPhaseAbove3` gate) ⟸ the same FrontSync
    concentration (`FrontSyncConc.frontSync_concentration_remaining_proven`) for the `FrontSync`
    conjunct, plus the deterministic phase-gate closures for the rest.

### Final hypothesis list.
`(n mC : ℕ) (hn : 2 ≤ n) (hmC : 2 ≤ mC) (hLK : 0 < K*(L+1)) (tseed tbulk : ℕ) (htbulk : 0 < tbulk)
(εbulk : ℝ≥0) (hεb : minuteRate-tail ≤ εbulk) (c₀ : Cfg L K)`.  `q` and `hstep` are GONE; the
per-minute side prefixes are the only un-bounded RHS terms, named for the WidthPrefix/Params
discharge. -/
theorem clock_real_faithful_O_log_n_unconditional (n mC : ℕ) (hn : 2 ≤ n) (hmC : 2 ≤ mC)
    (hLK : 0 < K * (L + 1))
    (tseed tbulk : ℕ) (htbulk : 0 < tbulk) (εbulk : ℝ≥0)
    (hεb : minuteRate n mC ^ tbulk *
        ENNReal.ofReal (Real.exp (Real.log 2 * (bulkHi mC : ℝ))) / 1 ≤ (εbulk : ℝ≥0∞))
    (c₀ : Config (AgentState L K)) :
    ∑ i : Fin (K * (L + 1) - 1),
        ((realκ L K) ^ (i.val * (tseed + tbulk) + tseed + tbulk)) c₀
          {c | ¬ BulkPost (L := L) (K := K) n mC (i.val + 1) c}
      ≤ ∑ i : Fin (K * (L + 1) - 1), ((εbulk : ℝ≥0∞)
          + ((tbulk : ℝ≥0∞) * 0
            + ∑ τ ∈ Finset.Ico (i.val * (tseed + tbulk) + tseed)
                (i.val * (tseed + tbulk) + tseed + tbulk),
                (realκ L K ^ τ) c₀ (Sgood (L := L) (K := K) n mC (i.val + 1))ᶜ)) :=
  clock_real_faithful_all_minutes_sideGood (L := L) (K := K) n mC (K * (L + 1) - 1) hn hmC
    (by omega) tseed tbulk htbulk εbulk hεb c₀

/-! ## Part 4 — the side-prefix discharge (the per-`τ` `Sgoodᶜ` decomposition).

The capstone leaves per-minute side prefixes `∑_τ (realκ^τ) c₀ Sgood(T)ᶜ` un-bounded.  Here we
decompose `Sgoodᶜ` into the §6 named failure events and bound the per-`τ` mass by their sum, so
each piece routes to its discharger.

`Sgood T = QbulkSet T ∩ {HabsGood}` (Part 2), with
`QbulkSet T = {Q_mix n mC T ∧ mC/10 ≤ rBeyond (T+1)}` and `HabsGood = allPhaseGE3 ∧ noPhaseAbove3
∧ allClocksCounterPos ∧ FrontSync ∧ (successor noPhaseAbove3)`.  So `Sgood(T)ᶜ` is the union of
the per-conjunct failures:

* `¬Q_mix T` (the window — `card`/`clockPhase3`/`clockSize`/`crossedT`) and `¬(mC/10 floor)`:
  these failures are covered by the §6 width / FrontSync machinery — `Q_mix`'s structural
  conjuncts hold deterministically from the start facts (`card`, `clockSize`), and `clockPhase3`
  / `crossedT` / the floor are re-established via the drip + width invariant.  Discharged by
  `WidthPrefix.goodFrontWidth_whp_at` + the `ClockFrontSyncFromWidth` bridges + `Params`.
* `¬FrontSync`: the front-shape synchronization, discharged by
  `FrontSyncConc.frontSync_concentration_remaining_proven` / `frontSync_whp_of_goodFrontWidth`
  (`= εW + εP + εB`, the width + side + bulk-arrival split).
* `¬allPhaseGE3` / `¬noPhaseAbove3` / `¬allClocksCounterPos` / the successor `noPhaseAbove3` gate:
  the structural phase gates.  `allPhaseGE3` and `noPhaseAbove3` are deterministic from the
  start (`allPhaseGE3` is one-step-closed — `HabsDischarge.allPhaseGE3_closed`; `noPhaseAbove3`
  is the residual deterministic gate, named); `allClocksCounterPos` is the genuinely-probabilistic
  one (the at-cap `counter = 1` witness), discharged ON the FrontSync-good event by
  `ClockFrontShape.counterPos_closed_of_frontSync`.

We deliver the GENERIC set-inclusion + union bound: `sidePrefix_le` takes the per-`τ` measure of
each failure event as a NAMED INPUT (`εQ`, `εfloor`, `εsync`, `εphase`), supplied by the above
dischargers, and concludes the per-`τ` `Sgood(T)ᶜ` mass `≤ εQ + εfloor + εsync + εphase`.  This
is the honest "assemble εside(τ) from the available pieces + named inputs" deliverable: the
inclusion is fully proven here; which feeder supplies each `εᵢ` is documented above. -/

/-- The four named per-`τ` failure events whose union covers `Sgood(T)ᶜ`.  Each is bounded by its
§6 discharger (see the part-4 docstring). -/
def QmixFail (n mC T : ℕ) : Set (Config (AgentState L K)) :=
  {c | ¬ Q_mix (L := L) (K := K) n mC T c}

def FloorFail (mC T : ℕ) : Set (Config (AgentState L K)) :=
  {c | ¬ (mC / 10 ≤ rBeyond (L := L) (K := K) (T + 1) c)}

def SyncFail : Set (Config (AgentState L K)) :=
  {c | ¬ FrontSync (L := L) (K := K) c}

/-- The structural phase-gate failures + the successor `noPhaseAbove3` gate failure. -/
def PhaseGateFail (c : Config (AgentState L K)) : Prop :=
  ¬ allPhaseGE3 (L := L) (K := K) c ∨
    ¬ noPhaseAbove3 (L := L) (K := K) c ∨
    ¬ allClocksCounterPos (L := L) (K := K) c ∨
    ¬ (∀ c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support,
        noPhaseAbove3 (L := L) (K := K) c')

/-- **The set inclusion `Sgood(T)ᶜ ⊆ QmixFail ∪ FloorFail ∪ SyncFail ∪ {PhaseGateFail}`.**
Every config off the side set fails at least one of the four named events. -/
theorem Sgood_compl_subset (n mC T : ℕ) :
    (Sgood (L := L) (K := K) n mC T)ᶜ ⊆
      ((QmixFail (L := L) (K := K) n mC T ∪ FloorFail (L := L) (K := K) mC T)
        ∪ (SyncFail (L := L) (K := K) ∪ {c | PhaseGateFail (L := L) (K := K) c})) := by
  classical
  intro c hc
  simp only [Sgood, Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_setOf_eq, not_and] at hc
  -- hc : c ∈ QbulkSet → ¬ HabsGood c  (de Morgan on the intersection)
  by_cases hQbulk : c ∈ QbulkSet (L := L) (K := K) n mC T
  · -- in the gate: HabsGood must fail.
    have hH : ¬ HabsGood (L := L) (K := K) c := hc hQbulk
    -- HabsGood = allPhaseGE3 ∧ noPhaseAbove3 ∧ allClocksCounterPos ∧ FrontSync ∧ (succ gate);
    -- its failure is one of {sync} ∪ {phase gates}.
    right
    unfold HabsGood at hH
    by_cases hsync : FrontSync (L := L) (K := K) c
    · -- FrontSync holds, so a phase gate fails.
      right
      simp only [Set.mem_setOf_eq, PhaseGateFail]
      by_contra hng
      push Not at hng
      obtain ⟨hge, hno, hpos, hsucc⟩ := hng
      exact hH ⟨hge, hno, hpos, hsync, hsucc⟩
    · exact Or.inl hsync
  · -- off the gate: ¬QbulkWin = ¬(Q_mix ∧ floor), so QmixFail or FloorFail.
    left
    have hQbw : ¬ QbulkWin (L := L) (K := K) n mC T c := hQbulk
    unfold QbulkWin at hQbw
    by_cases hQm : Q_mix (L := L) (K := K) n mC T c
    · exact Or.inr (show ¬ (mC / 10 ≤ rBeyond (L := L) (K := K) (T + 1) c) from
        fun hfl => hQbw ⟨hQm, hfl⟩)
    · exact Or.inl hQm

/-- **`sidePrefix_le` — the per-`τ` `Sgood(T)ᶜ` budget from the four named feeders.**  Given the
per-`τ` measure of each failure event (supplied by `goodFrontWidth_whp_at` + bridges /
`frontSync_concentration` / the phase-gate closures), the per-`τ` side-prefix mass is
`≤ εQ + εfloor + εsync + εphase`. -/
theorem sidePrefix_le (n mC T τ : ℕ) (c₀ : Config (AgentState L K))
    (εQ εfloor εsync εphase : ℝ≥0∞)
    (hQ : (realκ L K ^ τ) c₀ (QmixFail (L := L) (K := K) n mC T) ≤ εQ)
    (hfloor : (realκ L K ^ τ) c₀ (FloorFail (L := L) (K := K) mC T) ≤ εfloor)
    (hsync : (realκ L K ^ τ) c₀ (SyncFail (L := L) (K := K)) ≤ εsync)
    (hphase : (realκ L K ^ τ) c₀ {c | PhaseGateFail (L := L) (K := K) c} ≤ εphase) :
    (realκ L K ^ τ) c₀ (Sgood (L := L) (K := K) n mC T)ᶜ
      ≤ εQ + εfloor + εsync + εphase := by
  have hbound : (realκ L K ^ τ) c₀ (Sgood (L := L) (K := K) n mC T)ᶜ
      ≤ (εQ + εfloor) + (εsync + εphase) := by
    refine le_trans (measure_mono (Sgood_compl_subset (L := L) (K := K) n mC T)) ?_
    refine le_trans (measure_union_le _ _) ?_
    exact add_le_add (le_trans (measure_union_le _ _) (add_le_add hQ hfloor))
      (le_trans (measure_union_le _ _) (add_le_add hsync hphase))
  -- ENNReal addition is associative: (εQ+εfloor)+(εsync+εphase) = εQ+εfloor+εsync+εphase.
  calc (realκ L K ^ τ) c₀ (Sgood (L := L) (K := K) n mC T)ᶜ
      ≤ (εQ + εfloor) + (εsync + εphase) := hbound
    _ = εQ + εfloor + εsync + εphase := by ring

/-! ## Status (Parts 1–4 complete). -/
theorem clock_unconditional_status : True := trivial

end ClockUnconditional

end ExactMajority
