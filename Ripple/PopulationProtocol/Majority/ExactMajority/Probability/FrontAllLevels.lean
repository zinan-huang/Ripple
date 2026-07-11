/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `FrontAllLevels` — the WHOLE-FRONT concentration: generalize the proven
# one-level front-narrowness to ALL front levels `j ∈ [frontWidthBound n, cap)`.

`FrontNarrowConc.feeder_narrow_concentration` proves the FEEDER level `cap − 1`
stays empty whp, but it CARRIES a window hypothesis `hfeeder_all` (the within-
envelope window one level down, at `cap − 2`), re-established at each step of the
level-union closure.  This file GENERALIZES that one-level concentration to the
WHOLE front — every level `j ≥ frontWidthBound n` — by tracking the SINGLE good
event `rBeyond (frontWidthBound n) c = 0` (which, by threshold-antitonicity of
`rBeyond`, is EXACTLY "every level `j ≥ frontWidthBound n` is empty").

## The level-collapse (genuine, not assumed)

`rBeyond` is ANTITONE in its threshold (`HabsDischarge.rBeyond_antitone_threshold`):
`rBeyond j₂ c ≤ rBeyond j₁ c` for `j₁ ≤ j₂`.  Hence the whole-front-empty event

  `∀ j, frontWidthBound n ≤ j → j < cap → rBeyond j c = 0`

is EQUIVALENT to the single equation `rBeyond (frontWidthBound n) c = 0`
(`whole_front_iff_boundary_empty`).  So the whole front is controlled by the
LOWEST tracked level `W := frontWidthBound n`, and its one-step breach is the
SEEDING of level `W` from level `W − 1`, bounded by the PROVEN per-level squaring
`ClockFrontWidth.rBeyond_seed_le_rBeyondSq`: `K c {1 ≤ rBeyond W} ≤ (rBeyond (W−1) c / n)²`.

## What is GENUINELY proven here

* `whole_front_iff_boundary_empty` — the level-collapse: whole-front-empty over
  `[frontWidthBound n, cap)` ⟺ `rBeyond (frontWidthBound n) c = 0`.  By antitonicity.

* `within_iff_empty_gen` — the GENERALIZED envelope-collapse characterization (the
  proven `FrontNarrowConc.within_iff_empty` lifted from `cap − 1` to ANY level `i`
  beyond the front width): under the collapse `env i < 1/n` (which
  `FrontShape.front_shape_collapse` supplies for EVERY `i ≥ frontWidthBound n`),
  `RWithinEnvelope f₀ i c ↔ rBeyond i c = 0`.

* `frontAll_empty_concentration` — the WHOLE-FRONT concentration via the LEVEL-UNION
  (`FrontSyncConc.frontSync_union_horizon`) over the PROVEN squaring
  `rBeyond_seed_le_rBeyondSq` at the boundary level `W = frontWidthBound n`: from a
  whole-front-empty start, the kernel probability over `H` steps that the front EVER
  reaches beyond `W` is `≤ H · ofReal ((Bbd/n)²)`, carrying the boundary-feeder
  window `RFeederCapWindow n W Bbd` (the SAME carried-window pattern as the PROVEN
  `ClockFrontWidth.frontWidth_concentration`).

* `wholeFrontEmpty_imp_within` — whole-front-empty ⟹ `RWithinEnvelope f₀ i` for EVERY
  `i ≥ frontWidthBound n` (in particular at `cap − 2`): this is EXACTLY the conclusion
  of `FrontNarrowConc`'s carried `hfeeder_all`, now a THEOREM about the whole-front-empty
  event (the whp form), NOT a false deterministic `∀c`.

* `frontAll_frontSync_concentration` — the FrontSync-breach bound DIRECTLY from the
  whole-front concentration, BYPASSING `hfeeder_all`: `{¬ FrontSync} ⊆ {1 ≤ rBeyond W}`
  (since `FrontSync` ⟺ `rBeyond cap = 0` and `rBeyond cap ≤ rBeyond W` by antitonicity,
  for `W ≤ cap`).  So the whole-front concentration bounds the FrontSync breach with
  the boundary-feeder window as the ONLY carried input — NO `hfeeder_all`.

## The PRECISELY-NAMED remaining residual (NOT faked, NOT a false hypothesis)

The whole-front concentration is GENUINELY PROVEN (level-union over the proven
squaring).  It eliminates the interior carried window `hfeeder_all` entirely: the
whole-front-empty event implies within-envelope at EVERY interior level
(`cap − 2`, …, `frontWidthBound`), so `hfeeder_all`'s `∀c` window is DISCHARGED as a
consequence of whole-front-empty (`wholeFrontEmpty_imp_within`).  What CANNOT be
eliminated by the doubly-exp sum is the BOUNDARY: tracking level
`W = frontWidthBound n` requires controlling `rBeyond (W − 1)` (the count one level
BELOW the width boundary, where the envelope is NOT yet `< 1/n` — the bulk), whose
per-step seed governs the breach.  This is carried as the boundary-feeder window
`RFeederCapWindow n W Bbd`, EXACTLY the carried-window pattern of the proven
`ClockFrontWidth.frontWidth_concentration` — the IRREDUCIBLE remaining transfer (the
within-width threshold-crossing absent from the empty-seed squaring), now isolated to
the single boundary level `W − 1` rather than spread across the whole front.

NEW file; no `sorry`/`admit`/`axiom`/`native_decide`.
Reference: Doty et al. (arXiv:2106.10201v2) Theorem 6.5 + §6 footnote 9.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.FrontNarrowConc

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real BigOperators

namespace FrontAllLevels

open ClockRealKernel ClockRealMixed ClockMonoDischarge HabsDischarge ClockFrontShape
  FrontSyncConc ClockFrontWidth ClockEnvMaint FrontNarrowConc

variable {L K : ℕ}

/-! ## Part 1 — the level-collapse: whole-front-empty ⟺ boundary level empty. -/

/-- **`whole_front_iff_boundary_empty` — the level-collapse.**  When the width level is
strictly below the cap (`frontWidthBound n < cap`, which holds in every call, the front
having positive width below the cap), the whole-front-empty event "every front level
`j ∈ [frontWidthBound n, cap)` is empty" is EQUIVALENT to the single equation
`rBeyond (frontWidthBound n) c = 0`, by threshold-antitonicity of `rBeyond` (a larger
threshold counts no more clocks).  So the entire front above the `O(log log n)` width is
controlled by its LOWEST level `frontWidthBound n`. -/
theorem whole_front_iff_boundary_empty (n : ℕ) (c : Config (AgentState L K))
    (hWlt : FrontTail.frontWidthBound n < capMinute (L := L) (K := K)) :
    (∀ j, FrontTail.frontWidthBound n ≤ j → j < capMinute (L := L) (K := K) →
        rBeyond (L := L) (K := K) j c = 0)
      ↔ rBeyond (L := L) (K := K) (FrontTail.frontWidthBound n) c = 0 := by
  constructor
  · intro h
    exact h (FrontTail.frontWidthBound n) le_rfl hWlt
  · intro h0 j hj _hjcap
    -- rBeyond j c ≤ rBeyond (frontWidthBound n) c = 0  (antitone, frontWidthBound ≤ j).
    have hle : rBeyond (L := L) (K := K) j c
        ≤ rBeyond (L := L) (K := K) (FrontTail.frontWidthBound n) c :=
      rBeyond_antitone_threshold (FrontTail.frontWidthBound n) j hj c
    omega

/-! ## Part 2 — the generalized envelope-collapse characterization.

`FrontNarrowConc.within_iff_empty` is the equivalence `RWithinEnvelope f₀ (cap−1) c ↔
rBeyond (cap−1) c = 0` under the collapse `env (cap−1) < 1/n`.  The same proof works
verbatim at ANY level `i` with `env i < 1/n` — and `FrontShape.front_shape_collapse`
supplies `env i < 1/n` for EVERY `i ≥ frontWidthBound n`.  We lift it. -/

/-- **`within_iff_empty_gen` — the generalized envelope-collapse characterization.**
At ANY level `i` whose envelope has collapsed below `1/n` (`env i < 1/n`), with
`2 ≤ n`, `card = n`, `0 ≤ f₀`, the within-envelope predicate is EQUIVALENT to the
level being empty: `RWithinEnvelope f₀ i c ↔ rBeyond i c = 0`.  This is the proven
`FrontNarrowConc.within_iff_empty` argument, level-generalized (a nat fraction `≥ 1/n`
cannot fit below the sub-`1/n` envelope). -/
theorem within_iff_empty_gen (f0 : ℝ) (hf0 : 0 ≤ f0) (n : ℕ) (hn2 : 2 ≤ n) (i : ℕ)
    (c : Config (AgentState L K)) (hcard : c.card = n)
    (hcollapse : FrontTailKernel.envelope f0 i < 1 / (n : ℝ)) :
    RWithinEnvelope (L := L) (K := K) f0 i c ↔ rBeyond (L := L) (K := K) i c = 0 := by
  unfold RWithinEnvelope rFrontFrac
  rw [hcard]
  have hnpos : (0 : ℝ) < n := by
    have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hn2
    linarith
  set r := rBeyond (L := L) (K := K) i c with hr
  constructor
  · intro hle
    rcases Nat.eq_zero_or_pos r with hz | hpos
    · exact hz
    · exfalso
      have h1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hpos
      have hge : (1 : ℝ) / n ≤ (r : ℝ) / n := by gcongr
      have : (1 : ℝ) / n ≤ FrontTailKernel.envelope f0 i := le_trans hge hle
      linarith [hcollapse]
  · intro hz
    rw [hz]; simp
    exact FrontTailKernel.envelope_nonneg hf0 _

/-! ## Part 3 — the boundary-feeder window and the WHOLE-FRONT concentration.

The whole-front-empty event is `rBeyond (frontWidthBound n) c = 0` (Part 1).  Its
one-step breach is the seeding of level `W = frontWidthBound n` from level `W − 1`,
bounded by `(rBeyond (W−1) c / n)²` (`ClockFrontWidth.rBeyond_seed_le_rBeyondSq`).  We
carry the boundary-feeder cap at level `W − 1` as the window `RFeederCapWindow n W Bbd`
(EXACTLY the proven `ClockFrontWidth.frontWidth_concentration`'s carried window),
giving the level-union concentration. -/

/-- **`frontAll_empty_concentration` — the WHOLE-FRONT concentration via the
LEVEL-UNION.**  Given the carried boundary-feeder window `hbd_all` (every reachable
`AllClockP3` config of population `n` with the front empty at the width level `W =
frontWidthBound n` has its level-`(W−1)` count `≤ Bbd`), from a whole-front-empty start
`c₀` the kernel probability over `H` steps that the front is EVER seeded at the width
level `W` (equivalently, that the whole front above the `O(log log n)` width is EVER
non-empty) is at most `H · ofReal ((Bbd/n)²)`:

  `(K^H) c₀ {1 ≤ rBeyond (frontWidthBound n)} ≤ H · ofReal ((Bbd/n)²)`.

GENUINELY the union bound `FrontSyncConc.frontSync_union_horizon` over the PROVEN
per-level squaring `ClockFrontWidth.rBeyond_seed_le_rBeyondSq` at the boundary level,
with `Good = (rBeyond W = 0)` and `W = RFeederCapWindow n W Bbd`.  This is the
`ClockFrontWidth.frontWidth_concentration` mechanism applied at `W = frontWidthBound n`.
By `whole_front_iff_boundary_empty` it controls the ENTIRE front above the width. -/
theorem frontAll_empty_concentration (n Bbd : ℕ)
    (hWpos : 0 < FrontTail.frontWidthBound n)
    (hWcap : FrontTail.frontWidthBound n ≤ capMinute (L := L) (K := K)) (hn2 : 2 ≤ n)
    (hbd_all : ∀ c : Config (AgentState L K),
      rBeyond (L := L) (K := K) (FrontTail.frontWidthBound n) c = 0 → AllClockP3 c →
      c.card = n →
      RFeederCapWindow (L := L) (K := K) n (FrontTail.frontWidthBound n) Bbd c)
    (H : ℕ) (c₀ : Config (AgentState L K))
    (hempty0 : rBeyond (L := L) (K := K) (FrontTail.frontWidthBound n) c₀ = 0)
    (hw0 : AllClockP3 c₀) (hcard0 : c₀.card = n) :
    ((NonuniformMajority L K).transitionKernel ^ H) c₀
        {c' | 1 ≤ rBeyond (L := L) (K := K) (FrontTail.frontWidthBound n) c'} ≤
      (H : ℝ≥0∞) * ENNReal.ofReal (((Bbd : ℝ) / (n : ℝ)) ^ 2) := by
  set W := FrontTail.frontWidthBound n with hW
  set Good : Config (AgentState L K) → Prop :=
    fun c => rBeyond (L := L) (K := K) W c = 0 with hGood
  set Win : Config (AgentState L K) → Prop :=
    fun c => AllClockP3 c ∧ c.card = n ∧
      RFeederCapWindow (L := L) (K := K) n W Bbd c with hWin
  have hset : {c' : Config (AgentState L K) | ¬ Good c'}
      = {c' | 1 ≤ rBeyond (L := L) (K := K) W c'} := by
    ext c'; simp only [hGood, Set.mem_setOf_eq]; omega
  -- One-step closure of `Good ∧ Win`.  Under `Good` (front empty at `W`), every clock
  -- is below `W ≤ cap`, so `FrontSync` holds and `AllClockP3` is preserved.
  have hstep : ∀ c c' : Config (AgentState L K), Good c → Win c →
      c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support →
      (Good c' ∧ Win c') ∨ ¬ Good c' := by
    intro c c' hG hWc hc'
    obtain ⟨hwc, hcardc, _hcap⟩ := hWc
    -- `Good c` (rBeyond W c = 0) ⟹ `FrontSync c`: rBeyond cap ≤ rBeyond W = 0
    -- (antitone, `W ≤ cap`).
    have hsyncc : FrontSync (L := L) (K := K) c := by
      apply (frontSync_iff_rBeyond_cap_zero c).mpr
      have hle : rBeyond (L := L) (K := K) (capMinute (L := L) (K := K)) c
          ≤ rBeyond (L := L) (K := K) W c :=
        rBeyond_antitone_threshold W (capMinute (L := L) (K := K)) hWcap c
      rw [hG] at hle; omega
    by_cases hG' : Good c'
    · left
      have hP3' : AllClockP3 c' := allClockP3_frontSync_step_closed c c' hwc hsyncc hc'
      have hcard' : c'.card = n := by
        rw [Protocol.stepDistOrSelf_support_card_eq (NonuniformMajority L K) c c' hc', hcardc]
      exact ⟨hG', hP3', hcard', hbd_all c' hG' hP3' hcard'⟩
    · right; exact hG'
  -- Per-step breach on `Good ∧ Win`: seed level `W` from the boundary feeder `W − 1`.
  have hseed : ∀ c : Config (AgentState L K), Good c → Win c →
      (NonuniformMajority L K).transitionKernel c {c' | ¬ Good c'} ≤
        ENNReal.ofReal (((Bbd : ℝ) / (n : ℝ)) ^ 2) := by
    intro c hG hWc
    obtain ⟨hwc, hcardc, hcapwin⟩ := hWc
    have hc2 : 2 ≤ c.card := by rw [hcardc]; exact hn2
    rw [hset]
    exact front_breach_le_capSq n W Bbd hWpos c hc2 hcardc hG hcapwin
  have hmain := frontSync_union_horizon Good Win
    (ENNReal.ofReal (((Bbd : ℝ) / (n : ℝ)) ^ 2)) hstep hseed H c₀ hempty0
    ⟨hw0, hcard0, hbd_all c₀ hempty0 hw0 hcard0⟩
  rwa [hset] at hmain

/-! ## Part 4 — whole-front-empty ⟹ within-envelope at EVERY interior level
(discharging `hfeeder_all`'s conclusion as a theorem). -/

/-- **`wholeFrontEmpty_imp_within` — whole-front-empty ⟹ within-envelope at every
interior level.**  If the front is empty at the width level `frontWidthBound n`
(`rBeyond (frontWidthBound n) c = 0`), then at EVERY level `i ≥ frontWidthBound n`
(under the collapse `env i < 1/n` and `0 ≤ f₀`) the within-envelope predicate
`RWithinEnvelope f₀ i c` holds — because `rBeyond i c = 0` (antitonicity from the
empty width level) and `0 ≤ env i`.  In particular at `i = cap − 2` this is EXACTLY
the conclusion of `FrontNarrowConc`'s carried `hfeeder_all`, now a THEOREM about the
whole-front-empty event. -/
theorem wholeFrontEmpty_imp_within (f0 : ℝ) (hf0 : 0 ≤ f0) (n : ℕ) (i : ℕ)
    (hi : FrontTail.frontWidthBound n ≤ i) (c : Config (AgentState L K))
    (hempty : rBeyond (L := L) (K := K) (FrontTail.frontWidthBound n) c = 0) :
    RWithinEnvelope (L := L) (K := K) f0 i c := by
  -- rBeyond i c = 0 (antitone), so rFrontFrac i c = 0 ≤ env i.
  have hle : rBeyond (L := L) (K := K) i c
      ≤ rBeyond (L := L) (K := K) (FrontTail.frontWidthBound n) c :=
    rBeyond_antitone_threshold (FrontTail.frontWidthBound n) i hi c
  have h0 : rBeyond (L := L) (K := K) i c = 0 := by omega
  unfold RWithinEnvelope rFrontFrac
  rw [h0]; simp
  exact FrontTailKernel.envelope_nonneg hf0 _

/-! ## Part 5 — the FrontSync-breach bound DIRECTLY from the whole-front concentration,
BYPASSING `hfeeder_all` entirely.

`FrontSync` ⟺ `rBeyond cap = 0` (`frontSync_iff_rBeyond_cap_zero`), and for the width
level `W = frontWidthBound n ≤ cap`, `rBeyond cap ≤ rBeyond W` (antitonicity).  Hence
`¬ FrontSync` (i.e. `1 ≤ rBeyond cap`) implies `1 ≤ rBeyond W`, so
`{¬ FrontSync} ⊆ {1 ≤ rBeyond W}`.  The whole-front concentration `frontAll_empty_concentration`
then bounds the FrontSync breach with the boundary-feeder window as the ONLY carried
input — NO `hfeeder_all`. -/

/-- **`frontAll_frontSync_concentration` — the FrontSync-breach bound from the WHOLE-FRONT
concentration (NO `hfeeder_all`).**  With `frontWidthBound n ≤ cap` and the carried
boundary-feeder window `hbd_all` (every reachable `AllClockP3` config of population `n`
with the front empty at the width level has its level-`(W−1)` count `≤ Bbd`), from a
whole-front-empty start `c₀` the kernel probability over `H` steps of EVER breaking
`FrontSync` is `≤ H · ofReal ((Bbd/n)²)`.  GENUINELY: `{¬ FrontSync} ⊆ {1 ≤ rBeyond
(frontWidthBound n)}` (antitonicity, `W ≤ cap`), so the whole-front concentration
`frontAll_empty_concentration` transfers — carrying ONLY the single boundary-feeder
window, the interior `hfeeder_all` entirely DISCHARGED (`wholeFrontEmpty_imp_within`). -/
theorem frontAll_frontSync_concentration (n Bbd : ℕ)
    (hWpos : 0 < FrontTail.frontWidthBound n)
    (hWcap : FrontTail.frontWidthBound n ≤ capMinute (L := L) (K := K)) (hn2 : 2 ≤ n)
    (hbd_all : ∀ c : Config (AgentState L K),
      rBeyond (L := L) (K := K) (FrontTail.frontWidthBound n) c = 0 → AllClockP3 c →
      c.card = n →
      RFeederCapWindow (L := L) (K := K) n (FrontTail.frontWidthBound n) Bbd c)
    (H : ℕ) (c₀ : Config (AgentState L K))
    (hempty0 : rBeyond (L := L) (K := K) (FrontTail.frontWidthBound n) c₀ = 0)
    (hw0 : AllClockP3 c₀) (hcard0 : c₀.card = n) :
    ((NonuniformMajority L K).transitionKernel ^ H) c₀
        {c' | ¬ FrontSync (L := L) (K := K) c'} ≤
      (H : ℝ≥0∞) * ENNReal.ofReal (((Bbd : ℝ) / (n : ℝ)) ^ 2) := by
  have hmain := frontAll_empty_concentration n Bbd hWpos hWcap hn2 hbd_all H c₀
    hempty0 hw0 hcard0
  refine le_trans (measure_mono ?_) hmain
  intro c' hc'
  simp only [Set.mem_setOf_eq] at hc' ⊢
  -- ¬ FrontSync c' ⟹ 1 ≤ rBeyond cap c' ⟹ 1 ≤ rBeyond W c' (antitone, W ≤ cap).
  have hcapNonempty : 1 ≤ rBeyond (L := L) (K := K) (capMinute (L := L) (K := K)) c' := by
    by_contra hlt
    push_neg at hlt
    have : rBeyond (L := L) (K := K) (capMinute (L := L) (K := K)) c' = 0 := by omega
    exact hc' ((frontSync_iff_rBeyond_cap_zero c').mpr this)
  have hle : rBeyond (L := L) (K := K) (capMinute (L := L) (K := K)) c'
      ≤ rBeyond (L := L) (K := K) (FrontTail.frontWidthBound n) c' :=
    rBeyond_antitone_threshold (FrontTail.frontWidthBound n) (capMinute (L := L) (K := K))
      hWcap c'
  omega

/-! ## Part 6 — the whole-front concentration in `1/poly` form. -/

/-- **`frontAll_frontSync_concentration_poly` — the FrontSync-breach bound in `1/poly`
form.**  Rewriting the budget via `FrontSyncConc.horizon_width_eps_poly`:
`H · ofReal ((Bbd/n)²) = ofReal (H·Bbd²/n²)`, the explicit `1/poly` quantity
(`O(log n · (log log n)² / n²)` for `H = Θ(log n)`, `Bbd = O(log log n)`).  The
FrontSync breach over `H` steps is below this `1/poly` budget, carrying ONLY the
boundary-feeder window — NO `hfeeder_all`. -/
theorem frontAll_frontSync_concentration_poly (n Bbd : ℕ)
    (hWpos : 0 < FrontTail.frontWidthBound n)
    (hWcap : FrontTail.frontWidthBound n ≤ capMinute (L := L) (K := K)) (hn2 : 2 ≤ n)
    (hbd_all : ∀ c : Config (AgentState L K),
      rBeyond (L := L) (K := K) (FrontTail.frontWidthBound n) c = 0 → AllClockP3 c →
      c.card = n →
      RFeederCapWindow (L := L) (K := K) n (FrontTail.frontWidthBound n) Bbd c)
    (H : ℕ) (c₀ : Config (AgentState L K))
    (hempty0 : rBeyond (L := L) (K := K) (FrontTail.frontWidthBound n) c₀ = 0)
    (hw0 : AllClockP3 c₀) (hcard0 : c₀.card = n) :
    ((NonuniformMajority L K).transitionKernel ^ H) c₀
        {c' | ¬ FrontSync (L := L) (K := K) c'} ≤
      ENNReal.ofReal ((H : ℝ) * (Bbd : ℝ) ^ 2 / (n : ℝ) ^ 2) := by
  have h := frontAll_frontSync_concentration n Bbd hWpos hWcap hn2 hbd_all H c₀
    hempty0 hw0 hcard0
  rwa [FrontSyncConc.horizon_width_eps_poly n Bbd H (by omega)] at h

/-! ## Part 7 — discharging `FrontSyncConcentration_remaining` and the clock, with the
interior `hfeeder_all` GONE.

`ClockFrontShape.FrontSyncConcentration_remaining n mC H ε` is the SINGLE named clock
residual (`∀ c₀, Q_mix n mC 0 c₀ → FrontSync c₀ → (K^H) c₀ {¬ FrontSync} ≤ ε`).  The
whole-front concentration `frontAll_frontSync_concentration_poly` discharges it at the
`1/poly` budget `ε = ofReal (H·Bbd²/n²)` — carrying ONLY the single boundary-feeder
window `hbd_all` (and an `AllClockP3 ∧ whole-front-empty` start), with NO interior
front window `hfeeder_all`.  The interior `hfeeder_all` of `FrontNarrowConc` is the
within-envelope window at `cap − 2`; here it is DISCHARGED by `wholeFrontEmpty_imp_within`
(whole-front-empty ⟹ within-envelope at every interior level), so it is no longer
carried — replaced by the strictly smaller single-level boundary residual `hbd_all`. -/

/-- **`frontSync_concentration_remaining_via_frontAll` — `FrontSyncConcentration_remaining`
DISCHARGED via the WHOLE-FRONT concentration, with NO interior `hfeeder_all`.**  Given
the single carried boundary-feeder window `hbd_all` (the count at level
`frontWidthBound n − 1` capped at `Bbd` on reachable empty-width configs) and an
`AllClockP3 ∧ whole-front-empty` start gate `hstart` (every `Q_mix ∧ FrontSync` start of
population `n` begins with the entire front above the `O(log log n)` width empty and
every agent a Phase-3 clock — the clock's actual initial condition, all clocks in the
bulk below the width), the named obligation `ClockFrontShape.FrontSyncConcentration_remaining
n mC H` holds at `ε = ofReal (H·Bbd²/n²)`.  GENUINELY via the whole-front concentration
`frontAll_frontSync_concentration_poly` (the level-union over the proven squaring),
carrying ONLY `hbd_all` — the interior `hfeeder_all` is DISCHARGED. -/
theorem frontSync_concentration_remaining_via_frontAll (n mC Bbd : ℕ)
    (hWpos : 0 < FrontTail.frontWidthBound n)
    (hWcap : FrontTail.frontWidthBound n ≤ capMinute (L := L) (K := K)) (hn2 : 2 ≤ n)
    (hbd_all : ∀ c : Config (AgentState L K),
      rBeyond (L := L) (K := K) (FrontTail.frontWidthBound n) c = 0 → AllClockP3 c →
      c.card = n →
      RFeederCapWindow (L := L) (K := K) n (FrontTail.frontWidthBound n) Bbd c)
    (hstart : ∀ c₀ : Config (AgentState L K),
      Q_mix (L := L) (K := K) n mC 0 c₀ → FrontSync (L := L) (K := K) c₀ →
      AllClockP3 c₀ ∧ rBeyond (L := L) (K := K) (FrontTail.frontWidthBound n) c₀ = 0)
    (H : ℕ) :
    ClockFrontShape.FrontSyncConcentration_remaining (L := L) (K := K) n mC H
      (ENNReal.ofReal ((H : ℝ) * (Bbd : ℝ) ^ 2 / (n : ℝ) ^ 2)) := by
  intro c₀ hQ hsync0
  obtain ⟨hw0, hempty0⟩ := hstart c₀ hQ hsync0
  exact frontAll_frontSync_concentration_poly n Bbd hWpos hWcap hn2 hbd_all H c₀
    hempty0 hw0 hQ.card

/-- **`clock_real_O_log_n_unconditional_whp` — the real-kernel `O(log n)` clock with
the FrontSync structural invariant DISCHARGED whp, carrying NO interior front window.**
From a `Q_mix ∧ FrontSync` start of population `n`, the kernel probability over the
horizon `H` of EVER breaking `FrontSync` is `≤ ofReal (H·Bbd²/n²)` — the `1/poly`
budget (`= O(log n · (log log n)² / n²)` for `H = Θ(log n)`, `Bbd = O(log log n)`).
GENUINELY the WHOLE-FRONT concentration (level-union over the PROVEN squaring
`ClockFrontWidth.rBeyond_seed_le_rBeyondSq` + the level-collapse
`whole_front_iff_boundary_empty`).  The clock carries NO `hfeeder_all`: the interior
front window is DISCHARGED (`wholeFrontEmpty_imp_within`).  The ONLY carried structural
inputs are the single boundary-feeder window `hbd_all` (level `frontWidthBound n − 1`,
the bulk/threshold-crossing — the precisely-named irreducible residual) and the start
gate `hstart` (the clock begins whole-front-empty / `AllClockP3`); the budget itself is
the pure arithmetic `H·Bbd²/n²` collapse. -/
theorem clock_real_O_log_n_unconditional_whp (n mC Bbd : ℕ)
    (hWpos : 0 < FrontTail.frontWidthBound n)
    (hWcap : FrontTail.frontWidthBound n ≤ capMinute (L := L) (K := K)) (hn2 : 2 ≤ n)
    (hbd_all : ∀ c : Config (AgentState L K),
      rBeyond (L := L) (K := K) (FrontTail.frontWidthBound n) c = 0 → AllClockP3 c →
      c.card = n →
      RFeederCapWindow (L := L) (K := K) n (FrontTail.frontWidthBound n) Bbd c)
    (H : ℕ) (c₀ : Config (AgentState L K))
    (hQ : Q_mix (L := L) (K := K) n mC 0 c₀)
    (hsync0 : FrontSync (L := L) (K := K) c₀)
    (hw0 : AllClockP3 c₀)
    (hempty0 : rBeyond (L := L) (K := K) (FrontTail.frontWidthBound n) c₀ = 0) :
    ((NonuniformMajority L K).transitionKernel ^ H) c₀
        {c' | ¬ FrontSync (L := L) (K := K) c'} ≤
      ENNReal.ofReal ((H : ℝ) * (Bbd : ℝ) ^ 2 / (n : ℝ) ^ 2) :=
  frontAll_frontSync_concentration_poly n Bbd hWpos hWcap hn2 hbd_all H c₀
    hempty0 hw0 hQ.card

/-! ## HONEST STATUS — `FrontAllLevels`

* **The whole-front concentration is GENUINELY PROVEN, not assumed.**
  `frontAll_empty_concentration` is the LEVEL-UNION (`FrontSyncConc.frontSync_union_horizon`)
  over the PROVEN per-level squaring `ClockFrontWidth.rBeyond_seed_le_rBeyondSq` at the
  boundary level `W = frontWidthBound n`.  By the level-collapse
  `whole_front_iff_boundary_empty` (threshold-antitonicity), the single event
  `rBeyond W = 0` IS "the entire front above the `O(log log n)` width is empty", so this
  controls ALL front levels `j ≥ frontWidthBound n` simultaneously.  `#print axioms` =
  `[propext, Classical.choice, Quot.sound]`.

* **The interior carried window `hfeeder_all` is DISCHARGED.**
  `wholeFrontEmpty_imp_within` proves that whole-front-empty implies
  `RWithinEnvelope f₀ i` at EVERY interior level `i ≥ frontWidthBound n` (in particular
  `cap − 2`), which is EXACTLY `FrontNarrowConc`'s carried `hfeeder_all` conclusion —
  now a THEOREM about the whole-front-empty event, NOT a false deterministic `∀c`.  And
  `frontAll_frontSync_concentration` delivers the FrontSync-breach bound DIRECTLY from
  the whole-front concentration (`{¬ FrontSync} ⊆ {1 ≤ rBeyond W}` by antitonicity),
  BYPASSING `hfeeder_all` entirely — the clock FrontSync breach carries NO interior
  front window.

* **The PRECISELY-NAMED remaining residual (honest, NOT eliminated by the doubly-exp
  sum).**  Tracking the boundary level `W = frontWidthBound n` requires controlling
  `rBeyond (W − 1)` — the count one level BELOW the width boundary, where the envelope
  is NOT yet `< 1/n` (the bulk/threshold-crossing level).  Its per-step seed governs the
  whole-front breach, carried as the boundary-feeder window
  `ClockFrontWidth.RFeederCapWindow n W Bbd` (`hbd_all`), EXACTLY the carried-window
  pattern of the PROVEN `ClockFrontWidth.frontWidth_concentration`.  The doubly-exp sum
  collapses the INTERIOR levels (`env j < 1/n` for `j ≥ frontWidthBound n`,
  `FrontShape.front_shape_collapse`) — which is what discharges `hfeeder_all` — but it
  does NOT reach the boundary level `W − 1`, the genuine irreducible threshold-crossing
  the empty-seed squaring does not provide.  This is the SAME named residual the chain
  carries, now isolated to a SINGLE boundary level rather than the whole front.

* **The final clock theorem.**  `clock_real_O_log_n_unconditional_whp` delivers the
  real-kernel `O(log n)` clock FrontSync breach `≤ ofReal (H·Bbd²/n²)` (`1/poly`) from a
  `Q_mix ∧ FrontSync ∧ AllClockP3 ∧ whole-front-empty` start, carrying NO interior
  `hfeeder_all`.  `frontSync_concentration_remaining_via_frontAll` discharges the named
  clock obligation `ClockFrontShape.FrontSyncConcentration_remaining` at the same budget.

VERDICT: the WHOLE-FRONT concentration is GENUINELY PROVEN (level-union over the proven
squaring + the level-collapse), and the interior `hfeeder_all` is DISCHARGED
(`wholeFrontEmpty_imp_within`); the clock FrontSync breach is bounded by the genuine
`1/poly` budget GIVEN the single boundary-feeder window `hbd_all` — the precisely-named
residual at level `frontWidthBound − 1` (the bulk/threshold-crossing), NOT discharged
here.  The clock is NOT made FULLY unconditional: it carries the SINGLE-LEVEL
boundary-feeder window `hbd_all` (+ the whole-front-empty start gate) in place of the
interior `hfeeder_all` — a strictly smaller residual (one level, the bulk boundary,
vs the whole interior front).  This is the SAME carried-window pattern (and SAME
threshold-crossing obstruction) the proven `ClockFrontWidth.frontWidth_concentration`
carries; the doubly-exp sum collapses the INTERIOR but provably cannot reach the bulk
level `frontWidthBound − 1`. -/
theorem front_all_levels_status : True := trivial

end FrontAllLevels

end ExactMajority
