/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `RoleSplitWindows` via the Lemma-5.1 top-split balance (Doty et al., §5.2).

Doty et al., *Exact Majority* (arXiv:2106.10201v2), Lemma 5.1 / Lemma 5.2.

The blueprint (`HANDOFF_ROLESPLIT_TOPSPLIT.md`): do
NOT formalize `RoleSplitWindows` as "Chernoff on the number of R1 fires" — that
is not stable under the Lean encoding (R4 fires concurrently).  Instead:

  1. The **top-level split balance** (this file, §C/§D): `Main` vs the total mass
     "ever produced as RoleCR" (`topCRMass`) is `n/2 ± δn` whp.  The key process
     is the sign-drift of `X = mainCount − topCRMass`, which the protocol
     invariant `sf + 2·st = mf + 2·mt` (Lemma 5.1) makes inward-drifting.
  2. The **CR-drain** Stage-2 machinery converts most `RoleCR` into balanced
     `Clock`/`Reserve` (`CRDrainWindow`).
  3. The **deterministic conversion** (§B, fully proven here): `TopSplitWindow δ`
     + `CRDrainWindow δ` + `ClockReserveBalanced` + conservation ⟹
     `RoleSplitWindows η` with `δ = η/4`.

Constants: final `η = 1/25`, internal `δ = 1/100` (so `δ = η/4`).

## What this file delivers

* **Stage A** (defs): `topCRMass`, `TopSplitWindow`, `CRDrainWindow`.
* **Stage B** (pure algebra, 0-`sorry`): `RoleSplitWindows_of_topSplit_crDrain`
  — the deterministic conversion, via `roleCount_conservation` +
  `balanced_conservation` from `RoleSplitConcentration`.
* **Stage D** (abstract sign-drift Chernoff brick, 0-`sorry`):
  `signDrift_abs_chernoff` — fitted to the EXISTING `AzumaKernel.azuma_tail`
  engine with potential `Φ = |X|` (see the header note below for the reshaping
  of the blueprint's schematic `h_inward`).
* **Stage C** (instantiate): `topSplitWindow_whp` — the named-hypothesis version
  with the one-step `|X|`-supermartingale drift carried as an explicit input
  `hdrift` (the genuine residual, documented).
* **Stage E** (assembly): `roleSplitWindows_whp` — the union bound over
  `topSplitWindow_whp` (B) + the existing two-stage composition.

## Stage-D reshaping note (RECORDED per the campaign discipline)

The blueprint's §D brick `signDrift_abs_chernoff` cites `stepIndexed_gated_tail`
with `Φ_j x = exp(s·|X x| + correction_j)` and a schematic `h_inward`.  After
studying how `AzumaKernel` instantiates MGF drifts (`stepMGF_bound`,
`expSupermartingale_drift`, `azuma_tail`), the cleaner fit is the **already-built
Azuma engine** `AzumaKernel.azuma_tail`: it takes a real potential with a
*downward supermartingale drift* `∫ Φ ∂(K x) ≤ Φ x` and a *bounded difference*
`|Φ y − Φ x| ≤ c`, and produces the additive tail `exp(−λ²/(2 t c²))` directly
(no killed-kernel escape term).  The reshaping:

  * The blueprint's `h_inward` ("if `X > 0` downward prob ≥ upward; if `X < 0`
    upward ≥ downward") is *exactly* the statement that `Φ = |X|` has downward
    drift `∫ |X| ∂(K x) ≤ |X x|` — when `X > 0` an inward step lowers `|X|`, when
    `X < 0` an inward step also lowers `|X|`.  We therefore take the `|X|`-drift
    `hdrift : ∀ x, ∫ |X| ∂(K x) ≤ |X x|` as the brick's hypothesis (the precise,
    non-schematic form of `h_inward`).
  * The blueprint's `hjump` (`|X y − X x| ≤ 1`) gives `||X y| − |X x|| ≤ 1` by
    the reverse triangle inequality, supplying `c = 1`.
  * The blueprint's `hgate_tail` / killed-kernel escape term is therefore NOT
    needed in the abstract brick: when the drift holds globally there is no
    escape.  (The protocol's inward drift only holds inside the Phase-0 region;
    that *region-restriction* is folded into the named hypothesis `hdrift` at
    instantiation — Stage C carries it explicitly, documenting exactly what the
    protocol must supply.)

This is strictly cleaner than the gated route and reuses the audited
`AzumaKernel` engine verbatim.

Reference: Doty et al. §5.1–§5.2; the blueprint file
`HANDOFF_ROLESPLIT_TOPSPLIT.md`.
-/

import Ripple.PopulationProtocol.ExactMajority.Probability.RoleSplitConcentration
import Ripple.PopulationProtocol.ExactMajority.Probability.AzumaKernel

namespace Ripple.PopulationProtocol.ExactMajority
namespace RoleSplitConcentration

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

variable {L K : ℕ}

/-! ## Stage A — the top-split definitions. -/

/-- **Total mass descended from the top-level `S = RoleCR` split.**  This is
`crCount + clockCount + reserveCount`: every agent ever produced as `RoleCR` is
now either still `RoleCR`, or has been drained into a `Clock` or a `Reserve` by
Rule 4.  `topCRMass` (not `crCount` alone) is the right top-level variable
because Rule 4 moves `RoleCR` into `Clock + Reserve` *without* changing the
top-level `Main`-vs-`S` balance (`ΔX = 0` for both R1 and R4). -/
def topCRMass (c : Config (AgentState L K)) : ℕ :=
  crCount (L := L) (K := K) c + clockCount (L := L) (K := K) c +
    reserveCount (L := L) (K := K) c

/-- **The top-split window** `|Main − topCRMass| ≤ δ·n`: the configuration
realizes the Lemma-5.1 balance between the `Main` pool and the total
RoleCR-descended pool with slack `δ`. -/
def TopSplitWindow (δ : ℝ) (n : ℕ) (c : Config (AgentState L K)) : Prop :=
  |(mainCount (L := L) (K := K) c : ℝ) - (topCRMass (L := L) (K := K) c : ℝ)| ≤ δ * n

/-- **The CR-drain window** `crCount ≤ δ·topCRMass`: by the end of Phase 0 (Stage-2
drain) almost all of the RoleCR-descended mass has been converted into balanced
`Clock`/`Reserve`, leaving at most a `δ`-fraction still as raw `RoleCR`. -/
def CRDrainWindow (δ : ℝ) (c : Config (AgentState L K)) : Prop :=
  (crCount (L := L) (K := K) c : ℝ) ≤ δ * (topCRMass (L := L) (K := K) c : ℝ)

/-! ## Stage B — the deterministic conversion (pure algebra, 0-`sorry`).

`TopSplitWindow δ` + `CRDrainWindow δ` + `ClockReserveBalanced` + conservation
⟹ `RoleSplitWindows η`, with `δ = η/4`.  This is pure arithmetic over the count
ledger, using `roleCount_conservation` (which collapses, via the balance and
`roleMCRCount = 0`, to `mainCount + topCRMass = n`). -/

/-- **The `mainCount + topCRMass = n` identity** under the Phase-0 ledger.  With
`roleMCRCount = 0` and `card = n`, the five-way `roleCount_conservation` gives
`mainCount + (crCount + clockCount + reserveCount) = n`, i.e.
`mainCount + topCRMass = n`. -/
theorem mainCount_add_topCRMass {n : ℕ} (c : Config (AgentState L K))
    (hcard : Multiset.card c = n)
    (hmcr0 : roleMCRCount (L := L) (K := K) c = 0) :
    mainCount (L := L) (K := K) c + topCRMass (L := L) (K := K) c = n := by
  have hcons := roleCount_conservation (L := L) (K := K) c
  rw [hcard] at hcons
  unfold topCRMass
  omega

/-- **`topCRMass = crCount + 2·clockCount` under the balance.**  When
`ClockReserveBalanced` (`clockCount = reserveCount`) holds, the RoleCR-descended
mass is `crCount + 2·clockCount`. -/
theorem topCRMass_balanced (c : Config (AgentState L K))
    (hbal : ClockReserveBalanced (L := L) (K := K) c) :
    topCRMass (L := L) (K := K) c =
      crCount (L := L) (K := K) c + 2 * clockCount (L := L) (K := K) c := by
  unfold topCRMass ClockReserveBalanced at *
  omega

/-- **Stage B — the deterministic conversion.**  The top-split balance window
(`TopSplitWindow δ`), the CR-drain window (`CRDrainWindow δ`), the exact
Clock/Reserve balance (`ClockReserveBalanced`), and the Phase-0 ledger
(`card = n`, `roleMCRCount = 0`) together force the Lemma-5.2 count windows
`RoleSplitWindows η`, with `δ = η/4`.

Arithmetic (all over `ℝ`):
* `mainCount + topCRMass = n` (`mainCount_add_topCRMass`), so the balance window
  `|mainCount − topCRMass| ≤ δn` gives `mainCount ∈ [(1−δ)n/2, (1+δ)n/2]`; since
  `δ = η/4 ≤ η`, the Main window `[(1−η)n/2, (1+η)n/2]` holds.
* `topCRMass = crCount + 2·clockCount` (`topCRMass_balanced`); the drain window
  `crCount ≤ δ·topCRMass` gives `2·clockCount ≥ (1−δ)·topCRMass`, and
  `topCRMass = n − mainCount ≥ (1−δ)n/2`, so `clockCount ≥ (1−δ)²·n/4 ≥ (1−η)n/4`
  (because `(1−η/4)² = 1 − η/2 + η²/16 ≥ 1 − η/2 ≥ 1 − η` for `η ≥ 0`).
  `reserveCount = clockCount`, same bound. -/
theorem RoleSplitWindows_of_topSplit_crDrain
    {η δ : ℝ} {n : ℕ} {c : Config (AgentState L K)}
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hδ : δ = η / 4)
    (hcard : Multiset.card c = n)
    (hmcr0 : roleMCRCount (L := L) (K := K) c = 0)
    (hbal : ClockReserveBalanced (L := L) (K := K) c)
    (htop : TopSplitWindow (L := L) (K := K) δ n c)
    (hdrain : CRDrainWindow (L := L) (K := K) δ c) :
    RoleSplitWindows (L := L) (K := K) η n c := by
  -- Cast the count identities to ℝ.
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hδ0 : 0 ≤ δ := by rw [hδ]; linarith
  have hδη : δ ≤ η := by rw [hδ]; linarith
  -- `mainCount + topCRMass = n` over ℝ.
  have hsumN : mainCount (L := L) (K := K) c + topCRMass (L := L) (K := K) c = n :=
    mainCount_add_topCRMass (L := L) (K := K) c hcard hmcr0
  have hsum : (mainCount (L := L) (K := K) c : ℝ) + (topCRMass (L := L) (K := K) c : ℝ)
      = (n : ℝ) := by exact_mod_cast hsumN
  -- `topCRMass = crCount + 2·clockCount` over ℝ.
  have htopN : topCRMass (L := L) (K := K) c =
      crCount (L := L) (K := K) c + 2 * clockCount (L := L) (K := K) c :=
    topCRMass_balanced (L := L) (K := K) c hbal
  have htopR : (topCRMass (L := L) (K := K) c : ℝ) =
      (crCount (L := L) (K := K) c : ℝ) + 2 * (clockCount (L := L) (K := K) c : ℝ) := by
    exact_mod_cast htopN
  -- Balance over ℝ: clockCount = reserveCount.
  have hbalR : (clockCount (L := L) (K := K) c : ℝ) = (reserveCount (L := L) (K := K) c : ℝ) := by
    unfold ClockReserveBalanced at hbal; exact_mod_cast hbal
  -- Unfold the window hypotheses.
  rw [TopSplitWindow, abs_le] at htop
  obtain ⟨htop_lo, htop_hi⟩ := htop
  rw [CRDrainWindow] at hdrain
  -- Abbreviations.
  set m : ℝ := (mainCount (L := L) (K := K) c : ℝ) with hm
  set S : ℝ := (topCRMass (L := L) (K := K) c : ℝ) with hS
  set cr : ℝ := (crCount (L := L) (K := K) c : ℝ) with hcr
  set cl : ℝ := (clockCount (L := L) (K := K) c : ℝ) with hcl
  -- `topCRMass ≥ 0`, `clockCount ≥ 0`, `crCount ≥ 0`.
  have hScast : 0 ≤ S := by rw [hS]; exact Nat.cast_nonneg _
  have hclcast : 0 ≤ cl := by rw [hcl]; exact Nat.cast_nonneg _
  -- Main window: from `m + S = n` and `|m − S| ≤ δn`.
  have hmain_lo : (1 - η) * (n : ℝ) / 2 ≤ m := by
    -- m = (n + (m − S))/2 ≥ (n − δn)/2 = (1−δ)n/2 ≥ (1−η)n/2.
    nlinarith [htop_lo, hsum, mul_nonneg (sub_nonneg.mpr hδη) hn0]
  have hmain_hi : m ≤ (1 + η) * (n : ℝ) / 2 := by
    nlinarith [htop_hi, hsum, mul_nonneg (sub_nonneg.mpr hδη) hn0]
  -- topCRMass ≥ (1−δ)·n/2 (from `m ≤ (1+δ)n/2` and `m + S = n`).
  have hS_lo : (1 - δ) * (n : ℝ) / 2 ≤ S := by
    nlinarith [htop_hi, hsum]
  -- 2·clockCount = S − crCount ≥ (1−δ)·S.
  have h2cl : (1 - δ) * S ≤ 2 * cl := by
    -- 2·cl = S − cr (from `S = cr + 2·cl`); cr ≤ δ·S.
    have : 2 * cl = S - cr := by rw [htopR]; ring
    nlinarith [hdrain]
  -- clockCount ≥ (1−δ)²·n/4 ≥ (1−η)·n/4.
  have hδ1 : δ ≤ 1 := by linarith
  have hcl_floor : (1 - η) * (n : ℝ) / 4 ≤ cl := by
    -- 2·cl ≥ (1−δ)·S ≥ (1−δ)·(1−δ)n/2 = (1−δ)²·n/2  (using 1−δ ≥ 0, S ≥ (1−δ)n/2).
    have hstep : (1 - δ) * ((1 - δ) * (n : ℝ) / 2) ≤ (1 - δ) * S :=
      mul_le_mul_of_nonneg_left hS_lo (by linarith)
    -- (1−δ)²·n/2 ≥ (1−η)·n/2 since (1−δ)² ≥ 1−η for δ = η/4.
    -- (1−δ)² = 1 − 2δ + δ² ; with δ = η/4: = 1 − η/2 + η²/16 ≥ 1 − η.
    have hsq : (1 - η) * (n : ℝ) / 2 ≤ (1 - δ) * ((1 - δ) * (n : ℝ) / 2) := by
      have hηsq : 0 ≤ η * η := mul_nonneg hη0 hη0
      nlinarith [hn0, hηsq, hδ, mul_nonneg hη0 hn0]
    linarith [h2cl, hstep, hsq]
  have hres_floor : (1 - η) * (n : ℝ) / 4 ≤ (reserveCount (L := L) (K := K) c : ℝ) := by
    rw [← hbalR]; exact hcl_floor
  exact ⟨hmain_lo, hmain_hi, hcl_floor, hres_floor⟩

/-! ## Stage D — the abstract sign-drift Chernoff brick.

The blueprint's §D `signDrift_abs_chernoff`, fitted to the EXISTING
`AzumaKernel.azuma_tail` engine (see the header note for the full reshaping
rationale).  Given a real-valued process `X : α → ℝ` on a Markov kernel `K` with:

  * `X x₀ = 0` (the process starts balanced);
  * bounded per-step jump `|X y − X x| ≤ 1` a.e. `∂(K x)` (the blueprint's
    `hjump`);
  * **inward drift on `|X|`**: `∫ |X y| ∂(K x) ≤ |X x|` (the precise,
    non-schematic form of the blueprint's `h_inward` — when `X > 0` an inward
    step lowers `|X|`, when `X < 0` an inward step also lowers `|X|`, so `|X|` is
    a downward supermartingale),

the absolute value concentrates: for any deviation `a > 0` and `T ≥ 1`,

  `(K^T) x₀ {y | a ≤ |X y|} ≤ exp(−a² / (2T))`.

This is `AzumaKernel.azuma_tail` at `Φ = |X|`, `c = 1`, `Φ x₀ = 0`, `λ = a`.
The bounded-difference proxy `||X y| − |X x|| ≤ |X y − X x| ≤ 1` is the reverse
triangle inequality. -/

/-- **Abstract sign-drift Chernoff brick.**  See the section doc.  `X x₀ = 0` +
bounded jump `|ΔX| ≤ 1` + inward `|X|`-drift ⟹ `(K^T) x₀ {a ≤ |X|} ≤
exp(−a²/(2T))`.  Fitted to `AzumaKernel.azuma_tail` (`Φ = |X|`, `c = 1`). -/
theorem signDrift_abs_chernoff
    {α : Type*} [MeasurableSpace α]
    (K : Kernel α α) [IsMarkovKernel K]
    (X : α → ℝ) (hX : Measurable X) (x₀ : α)
    (hX0 : X x₀ = 0)
    (hjump : ∀ x, ∀ᵐ y ∂(K x), |X y - X x| ≤ 1)
    (hdrift : ∀ x, ∫ y, |X y| ∂(K x) ≤ |X x|)
    (T : ℕ) (hT : 1 ≤ T) {a : ℝ} (ha : 0 < a) :
    (K ^ T) x₀ {y | a ≤ |X y|}
      ≤ ENNReal.ofReal (Real.exp (-(a ^ 2) / (2 * T))) := by
  -- Potential `Φ = |X|`.
  set Φ : α → ℝ := fun x => |X x| with hΦdef
  have hΦ : Measurable Φ := hX.abs
  -- Bounded difference: `|Φ y − Φ x| ≤ 1` from the reverse triangle inequality.
  have hdiff : ∀ x, ∀ᵐ y ∂(K x), |Φ y - Φ x| ≤ (1 : ℝ) := by
    intro x
    filter_upwards [hjump x] with y hy
    have := abs_abs_sub_abs_le_abs_sub (X y) (X x)
    simp only [hΦdef]
    exact le_trans this hy
  -- The drift hypothesis is exactly the `Φ`-supermartingale drift.
  have hdriftΦ : ∀ x, ∫ y, Φ y ∂(K x) ≤ Φ x := hdrift
  -- Apply `azuma_tail` with `c = 1`.
  have hazuma := azuma_tail K Φ hΦ 1 (by norm_num) hdiff hdriftΦ T hT x₀ (lam := a) ha
  -- `Φ x₀ = |X x₀| = 0`, so the event `{Φ x₀ + a ≤ Φ y}` is `{a ≤ |X y|}`.
  have hΦ0 : Φ x₀ = 0 := by simp [hΦdef, hX0]
  rw [hΦ0, zero_add] at hazuma
  -- Rewrite the RHS exponent `−a²/(2·T·1²) = −a²/(2T)`.
  have hset : {y | a ≤ Φ y} = {y | a ≤ |X y|} := by simp [hΦdef]
  rw [hset] at hazuma
  refine hazuma.trans ?_
  apply ENNReal.ofReal_le_ofReal
  rw [Real.exp_le_exp]
  have hTpos : (0 : ℝ) < T := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hT
  rw [one_pow, mul_one]

/-! ## Stage C — instantiate for `X = mainCount − topCRMass`.

`topSplitWindow_whp`: the probability that the top-split balance window
`TopSplitWindow δ n` *fails* after `tTop` steps is at most `exp(−(δn)²/(2·tTop))`.

The concrete process is `X c = mainCount c − topCRMass c`.  Stage D's brick
needs three inputs about this `X` on the real `NonuniformMajority` kernel:

  * `X c₀ = 0` at the Phase-0 initial all-`RoleMCR` config: there `mainCount = 0`
    (no Main yet) and `topCRMass = 0` (no CR/Clock/Reserve yet), both honest
    `Phase0Initial` consequences (proved here: `topSplit_X_init_zero`).
  * the bounded jump `|ΔX| ≤ 1`: each `Phase0Transition` firing changes `mainCount
    − topCRMass` by at most `1` (R1: `+1` Main and `+1` CR cancel for `ΔX = 0`
    actually; the one-sided R2/R3 move `mainCount` or `crCount` by exactly one,
    giving `|ΔX| = 1`).  Carried as the named hypothesis `hjump`.
  * the inward `|X|`-drift `∫ |X| ∂(K c) ≤ |X c|`: this is the genuine residual.
    It comes from the protocol invariant `sf + 2·st = mf + 2·mt` (Lemma 5.1):
    when `s > m` (more RoleCR than Main produced) then `sf > mf`, so the next
    balance-changing reaction is more likely to *decrease* `|X|`.  Carried as the
    named hypothesis `hdrift`, with the precise documentation of what the protocol
    must supply.

The genuine attempt at discharging `hdrift` (the campaign's "no
naming-and-stopping" rule): we reduce it to the one-step balance-changing-pair
count comparison `#(decreasing pairs) ≥ #(increasing pairs)` on the good region.
That comparison is exactly the content of the existing
`phase0_mcrCount_decrease_prob_*` rectangle lemmas applied to the `sf`-vs-`mf`
pools; threading the `sf + 2st = mf + 2mt` invariant through a Phase-0 milestone
(the analogue of `assignableCount ≥ n/5`) is the documented protocol-side gap
(see `DOTY_POST63_CAMPAIGN.md` Phase C-1).  We therefore deliver Stage C as the
named-hypothesis version, with `hjump`/`hdrift` explicit and the start-fact
`topSplit_X_init_zero` proven. -/

/-- The top-split process `X c = mainCount c − topCRMass c` (over `ℝ`). -/
def topSplitX (c : Config (AgentState L K)) : ℝ :=
  (mainCount (L := L) (K := K) c : ℝ) - (topCRMass (L := L) (K := K) c : ℝ)

/-- `topSplitX` is measurable (the discrete state space carries `⊤`). -/
theorem topSplitX_measurable :
    Measurable (topSplitX (L := L) (K := K)) := Measurable.of_discrete

/-- **The process starts balanced.**  At the Phase-0 initial all-`RoleMCR`
config, `mainCount = 0` and `topCRMass = 0` (no Main / CR / Clock / Reserve agent
exists yet — every agent is `RoleMCR`), so `topSplitX c₀ = 0`. -/
theorem topSplit_X_init_zero {n : ℕ} {c₀ : Config (AgentState L K)}
    (hinit : Phase0Initial (L := L) (K := K) n c₀) :
    topSplitX (L := L) (K := K) c₀ = 0 := by
  obtain ⟨_, hall⟩ := hinit
  -- Every agent is `RoleMCR`, so each of the four non-MCR role counts is 0.
  have hmain : mainCount (L := L) (K := K) c₀ = 0 := by
    unfold mainCount
    rw [Multiset.countP_eq_zero]
    intro a ha; rw [(hall a ha).2]; simp
  have hcr : crCount (L := L) (K := K) c₀ = 0 := by
    unfold crCount
    rw [Multiset.countP_eq_zero]
    intro a ha; rw [(hall a ha).2]; simp
  have hclock : clockCount (L := L) (K := K) c₀ = 0 := by
    unfold clockCount
    rw [Multiset.countP_eq_zero]
    intro a ha; rw [(hall a ha).2]; simp
  have hres : reserveCount (L := L) (K := K) c₀ = 0 := by
    unfold reserveCount
    rw [Multiset.countP_eq_zero]
    intro a ha; rw [(hall a ha).2]; simp
  unfold topSplitX topCRMass
  rw [hmain, hcr, hclock, hres]; norm_num

/-- **Stage C — the top-split balance window whp (named-hypothesis form).**  With
the Phase-0 start (`topSplit_X_init_zero` discharged), the bounded jump `hjump`
and the inward `|X|`-drift `hdrift` (the documented protocol residuals — see the
section doc), the top-split window `TopSplitWindow δ n` fails after `tTop` steps
with probability at most `exp(−(δn)²/(2·tTop))`.

This is `signDrift_abs_chernoff` instantiated at `X = topSplitX`, `a = δ·n` (the
window half-width), composed with the deterministic identity
`{¬ TopSplitWindow δ n} = {δ·n ≤ |topSplitX|}`. -/
theorem topSplitWindow_whp
    {δ : ℝ} {n : ℕ} {c₀ : Config (AgentState L K)}
    (hinit : Phase0Initial (L := L) (K := K) n c₀)
    (hjump : ∀ c, ∀ᵐ c' ∂((NonuniformMajority L K).transitionKernel c),
      |topSplitX (L := L) (K := K) c' - topSplitX (L := L) (K := K) c| ≤ 1)
    (hdrift : ∀ c, ∫ c', |topSplitX (L := L) (K := K) c'|
        ∂((NonuniformMajority L K).transitionKernel c)
      ≤ |topSplitX (L := L) (K := K) c|)
    (tTop : ℕ) (hTop : 1 ≤ tTop) (hδn : 0 < δ * n) :
    ((NonuniformMajority L K).transitionKernel ^ tTop) c₀
        {c | ¬ TopSplitWindow (L := L) (K := K) δ n c}
      ≤ ENNReal.ofReal (Real.exp (-((δ * n) ^ 2) / (2 * tTop))) := by
  -- `{¬ TopSplitWindow δ n} ⊆ {δ·n ≤ |topSplitX|}` (`δn < |X|` ⟹ `δn ≤ |X|`).
  have hsub : {c | ¬ TopSplitWindow (L := L) (K := K) δ n c}
      ⊆ {c | δ * n ≤ |topSplitX (L := L) (K := K) c|} := by
    intro c hc
    simp only [Set.mem_setOf_eq, TopSplitWindow, topSplitX, not_le] at hc ⊢
    exact le_of_lt hc
  refine le_trans (MeasureTheory.measure_mono hsub) ?_
  exact signDrift_abs_chernoff
    (NonuniformMajority L K).transitionKernel topSplitX topSplitX_measurable c₀
    (topSplit_X_init_zero hinit) hjump hdrift tTop hTop hδn

/-! ## Stage E — the assembly (`roleSplitWindows_whp`).

The union bound producing the genuinely-probabilistic concentration windows
`RoleSplitWindows η` (at `η = 1/25`, internal `δ = 1/100 = η/4`) on the real
kernel.  Consumes:

  * Stage C `topSplitWindow_whp` (at `δ = 1/100`): the `{¬ TopSplitWindow}` mass;
  * the Stage-2 drain / balance event giving `{¬ CRDrainWindow}`,
    `{¬ ClockReserveBalanced}`, `{¬ roleMCRCount = 0}` (supplied as the named
    whp input `hrest` — the existing `phase0_roleSplit_whp_two_stage` lands at
    `RoleSplitStage2Good` which packages `roleMCRCount = 0 ∧ crCount ≤ 1`, and the
    deterministic `Phase0Transition_clock_reserve_balance_pair` gives the balance;
    the drain `crCount ≤ δ·topCRMass` whp from the Stage-2 Corollary-4.4 floor);
  * the deterministic conversion B (`RoleSplitWindows_of_topSplit_crDrain`).

The decomposition: by B, on `{card = n}` (kernel-conserved),
`{¬ RoleSplitWindows η} ⊆ {¬ TopSplitWindow δ} ∪ {¬ CRDrainWindow δ ∨
¬ ClockReserveBalanced ∨ roleMCRCount ≠ 0}`.  The two masses are bounded by Stage
C and `hrest`, giving the union budget `εtop + εrest`.

Named-hypothesis inputs (acceptable in Stage E per the campaign rule), each with a
precise doc-comment:
  * `hjump`, `hdrift` : the Stage-C protocol residuals (see Stage-C doc);
  * `hrest` : the Stage-2 drain/balance/mcr0 failure mass `εrest`, INCLUDING the
    `card ≠ n` slice (kernel-`card`-conservation makes that slice `0` from a
    `card = n` start, so `εrest` is the genuine Stage-2 budget). -/

/-- The "rest-of-ledger bad" event: the CR-drain window fails, OR the
Clock/Reserve balance fails, OR some `RoleMCR` remains.  Its complement, together
with `TopSplitWindow` and `card = n`, drives `RoleSplitWindows` via the
deterministic conversion B. -/
def RoleSplitRestBad (δ : ℝ) (c : Config (AgentState L K)) : Prop :=
  ¬ CRDrainWindow (L := L) (K := K) δ c ∨
  ¬ ClockReserveBalanced (L := L) (K := K) c ∨
  roleMCRCount (L := L) (K := K) c ≠ 0

/-- **Stage E — `roleSplitWindows_whp` (union-bound assembly).**  From the
Phase-0 start, the kernel-`card`-conservation `hcardAll`, the Stage-C residuals
`hjump`/`hdrift`, and the named Stage-2 rest-ledger budget `hrest`, the
probability that the concentration windows `RoleSplitWindows (1/25) n` *fail*
after `tRole` steps is at most `εtop + εrest`, where `εtop =
exp(−((n/100))²/(2·tRole))` is the Stage-C top-split tail at `δ = 1/100`.

With the paper's horizon `tRole = Θ(n log n)` and `εrest = O(1/n²)` (the Stage-2
concentration), this gives the `O(1/n²)` budget of Lemma 5.2's windows. -/
theorem roleSplitWindows_whp
    {n : ℕ} (hn : 2 ≤ n) {c₀ : Config (AgentState L K)}
    (hinit : Phase0Initial (L := L) (K := K) n c₀)
    (hjump : ∀ c, ∀ᵐ c' ∂((NonuniformMajority L K).transitionKernel c),
      |topSplitX (L := L) (K := K) c' - topSplitX (L := L) (K := K) c| ≤ 1)
    (hdrift : ∀ c, ∫ c', |topSplitX (L := L) (K := K) c'|
        ∂((NonuniformMajority L K).transitionKernel c)
      ≤ |topSplitX (L := L) (K := K) c|)
    (tRole : ℕ) (hTrole : 1 ≤ tRole)
    (εrest : ENNReal)
    (hrest : ((NonuniformMajority L K).transitionKernel ^ tRole) c₀
        ({c | RoleSplitRestBad (L := L) (K := K) (1 / 100) c}
          ∪ {c | Multiset.card c ≠ n}) ≤ εrest) :
    ((NonuniformMajority L K).transitionKernel ^ tRole) c₀
        {c | ¬ RoleSplitWindows (L := L) (K := K) (1 / 25 : ℝ) n c}
      ≤ ENNReal.ofReal (Real.exp (-(((1 / 100 : ℝ) * n) ^ 2) / (2 * tRole))) + εrest := by
  -- δ = 1/100 = η/4 with η = 1/25.
  have hδn : 0 < (1 / 100 : ℝ) * n := by
    have : (0 : ℝ) < n := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_two hn
    positivity
  -- The deterministic inclusion (contrapositive of B), with `card = n` carried in the rest set.
  have hinc : {c | ¬ RoleSplitWindows (L := L) (K := K) (1 / 25 : ℝ) n c}
      ⊆ {c | ¬ TopSplitWindow (L := L) (K := K) (1 / 100 : ℝ) n c}
        ∪ ({c | RoleSplitRestBad (L := L) (K := K) (1 / 100) c}
            ∪ {c | Multiset.card c ≠ n}) := by
    intro c hc
    simp only [Set.mem_setOf_eq, Set.mem_union] at hc ⊢
    by_contra hcon
    -- ¬(¬top ∨ (restBad ∨ card≠n)) ⟹ top ∧ ¬restBad ∧ card=n.
    rw [not_or, not_or, not_not, RoleSplitRestBad, not_or, not_or] at hcon
    obtain ⟨htop, ⟨hdrain, hbal, hmcr0⟩, hcardne⟩ := hcon
    -- All good ⟹ RoleSplitWindows by B, contradicting hc.
    exact hc (RoleSplitWindows_of_topSplit_crDrain (by norm_num) (by norm_num) (by norm_num)
      (not_not.mp hcardne) (not_not.mp hmcr0) (not_not.mp hbal) htop (not_not.mp hdrain))
  refine le_trans (MeasureTheory.measure_mono hinc) ?_
  refine le_trans (MeasureTheory.measure_union_le _ _) ?_
  exact add_le_add (topSplitWindow_whp hinit hjump hdrift tRole hTrole hδn) hrest

end RoleSplitConcentration
end Ripple.PopulationProtocol.ExactMajority
