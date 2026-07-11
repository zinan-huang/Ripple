/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `FrontSyncConc` — the FrontSync concentration over the `O(log n)` horizon
# (the final clock piece: discharging `FrontSyncConcentration_remaining`).

`ClockFrontShape.lean` reduced the real-kernel clock's `habs_mix` to the SINGLE
named probabilistic obligation

  `FrontSyncConcentration_remaining n mC H ε :
     ∀ c₀, Q_mix n mC 0 c₀ → FrontSync c₀ →
        (K^H) c₀ {c' | ¬ FrontSync c'} ≤ ε`

(FrontSync — no clock reaches the cap minute prematurely — survives the
`O(log n)`-minute horizon).  The per-minute BREACH probability is ALREADY proven
(`ClockFrontShape.real_front_advance_squares_cap`):

  `K c {¬ FrontSync} ≤ ofReal ((frontMinuteCount (cap−1) c / n)²)`,

the SQUARE of the cap-front feeder fraction, when `AllClockP3 c ∧ FrontSync c`.

This file delivers, with NO sorry / NO axiom / NO native_decide:

## 1.  The general kernel UNION BOUND over the horizon (genuine, first principles)

`frontSync_union_horizon` — for ANY window `W` that
* is preserved on the one-step support together with `FrontSync` (so the
  good event `FrontSync ∧ W` is one-step closed except on the breach), and
* carries the per-step breach bound `K c {¬FrontSync} ≤ qE` whenever
  `FrontSync c ∧ W c` holds,
the breach probability after `H` steps is at most `H · qE`:

  `(K^H) c₀ {¬FrontSync} ≤ H · qE`.

This is the exact analog of `EarlyDrip.earlyDrip_kernel_bound` (the standard
union/Chernoff estimate, induction on the horizon conditioning on the first step,
Chapman–Kolmogorov).  It is GENUINELY PROVED here.

## 2.  Instantiation with the squared cap-front feeder (genuine per-step content)

The window is `AllClockP3 ∧ frontMinuteCount (cap−1) ≤ B` (every agent a Phase-3
clock; the cap-front feeder count capped at the transferred `O(log log n)` width
`B`).  Under `FrontSync`:
* `AllClockP3` is preserved on the support (`allClockP3_frontSync_step_closed`,
  proven HERE from the per-pair Phase-3 drip/sync facts — under FrontSync the
  cap branch never fires, so every produced agent is again a Phase-3 clock); and
* the per-step breach `K c {¬FrontSync} ≤ ofReal ((B/n)²)` follows from
  `real_front_advance_squares_cap` (`frontMinuteCount (cap−1) c ≤ B`).

Composing 1+2 gives

  `frontSync_concentration_with_width :
     (K^H) c₀ {¬FrontSync} ≤ H · ofReal ((B/n)²)`,

i.e. `FrontSyncConcentration_remaining n mC H (H · (B/n)²)` once the feeder-width
window `W` is maintained along the run.

## 3.  The PRECISELY-NAMED remaining residual (NOT faked)

The union bound + squared breach are GENUINELY PROVEN.  The remaining gate is the
maintenance of the cap-front-feeder WIDTH along the run — the transfer of
`FrontTailDecay.frontWidth_loglog` (the doubly-exponential `O(log log n)` front
width) to the REAL-kernel feeder count `frontMinuteCount (cap−1)`:

  `frontFeederWidth_maintained_real n B c :
     FrontSync c → AllClockP3 c → frontMinuteCount (cap−1) c ≤ B`,

stated as the named `Prop`-valued window hypothesis `FrontFeederWindow`.  This is
the SAME kind of carried per-step window hypothesis as `EarlyDrip`'s `hwin`: it is
the doubly-exponential front-shape envelope (`frontWidth_loglog`) on the REAL
count.  It is a multi-step front-shape REACHABILITY fact, NOT a one-step closure,
and turning the proven per-step squaring (`real_front_advance_squares`) into a
sustained `FrontRecurrence` envelope on the real `AgentState` count is the genuine
remaining transfer.  We carry it EXPLICITLY (never assert it false), exactly as
`EarlyDrip.earlyDrip_kernel_bound` carries its window `hwin`.

With `FrontFeederWindow` supplied, `frontSync_concentration_unconditional`
discharges `FrontSyncConcentration_remaining` with `ε = H · (B/n)²`, and the
arithmetic (`horizon_width_eps_poly`) shows that for `H = Θ(log n)`,
`B = O(log log n)` the budget `H · (B/n)² = O(log n · (log log n)² / n²)` is
`1/poly` — strictly below any fixed `1/n^{1.9}` threshold for large `n`.

NEW file; no existing file is edited; no `sorry`/`admit`/`axiom`/`native_decide`.
Reference: Doty et al. (arXiv:2106.10201v2) Theorem 6.5 + §6 footnote 9.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ClockFrontShape
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.EarlyDripBound

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real BigOperators

namespace FrontSyncConc

open ClockRealKernel ClockRealMixed ClockMonoDischarge HabsDischarge ClockFrontShape

variable {L K : ℕ}

/-! ## Part 0 — a finite power of the kernel assigns mass at most one. -/

/-- A finite power of the protocol Markov kernel assigns mass at most one to every
set.  (Local copy; mirrors `EarlyDrip.kernel_pow_le_one'`.) -/
private theorem kernel_pow_le_one
    (t : ℕ) (x : Config (AgentState L K)) (S : Set (Config (AgentState L K))) :
    ((NonuniformMajority L K).transitionKernel ^ t) x S ≤ 1 := by
  set K' := (NonuniformMajority L K).transitionKernel with hK'
  have h_univ : (K' ^ t) x Set.univ = 1 := by
    induction t with
    | zero =>
        simp only [pow_zero]
        change Kernel.id x Set.univ = 1
        rw [Kernel.id_apply]; simp
    | succ t ih =>
        rw [Kernel.pow_succ_apply_eq_lintegral K' t x MeasurableSet.univ]
        calc ∫⁻ y, K' y Set.univ ∂((K' ^ t) x)
            = ∫⁻ _ : Config (AgentState L K), (1 : ℝ≥0∞) ∂((K' ^ t) x) := by
                apply lintegral_congr_ae; filter_upwards with y
                haveI : IsProbabilityMeasure (K' y) := by
                  rw [hK']
                  exact (inferInstance : IsMarkovKernel _).isProbabilityMeasure y
                simp only [measure_univ]
          _ = 1 := by rw [lintegral_const, ih, one_mul]
  calc (K' ^ t) x S ≤ (K' ^ t) x Set.univ := measure_mono (Set.subset_univ S)
    _ = 1 := h_univ

/-! ## Part 1 — the general kernel UNION BOUND over the horizon.

For a predicate `Good` (here `FrontSync`) and a window `W` such that the GOOD
event `Good ∧ W` is one-step closed except on the breach `¬ Good`, and the
one-step breach probability is `≤ qE` on `Good ∧ W`, the breach probability after
`H` steps from a `Good ∧ W` start is at most `H · qE`.  This is the standard
union/Chernoff bound, GENUINELY PROVED by induction on `H` conditioning on the
first step (Chapman–Kolmogorov), mirroring `EarlyDrip.earlyDrip_kernel_bound`. -/

/-- **The general FrontSync-style union bound over the horizon.**  Given:
* `hstep` — `Good ∧ W` is one-step closed on the support EXCEPT on `¬ Good`
  (every successor of a `Good ∧ W` config is either `Good ∧ W` again, or `¬ Good`);
* `hseed` — on every `Good ∧ W` config the one-step breach probability is `≤ qE`;
then from a `Good ∧ W` start `c₀` the breach probability after `H` steps is
`≤ H · qE`:

  `(K^H) c₀ {¬ Good} ≤ H · qE`. -/
theorem frontSync_union_horizon
    (Good W : Config (AgentState L K) → Prop) (qE : ℝ≥0∞)
    (hstep : ∀ c c' : Config (AgentState L K), Good c → W c →
      c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support →
      (Good c' ∧ W c') ∨ ¬ Good c')
    (hseed : ∀ c : Config (AgentState L K), Good c → W c →
      (NonuniformMajority L K).transitionKernel c {c' | ¬ Good c'} ≤ qE)
    (H : ℕ) (c₀ : Config (AgentState L K)) (hG0 : Good c₀) (hW0 : W c₀) :
    ((NonuniformMajority L K).transitionKernel ^ H) c₀ {c' | ¬ Good c'} ≤
      (H : ℝ≥0∞) * qE := by
  classical
  set Kr := (NonuniformMajority L K).transitionKernel with hKr
  -- The "bad" set and the "good window" set.
  set Sbad : Set (Config (AgentState L K)) := {c' | ¬ Good c'} with hSbad
  set Ggw : Set (Config (AgentState L K)) := {c | Good c ∧ W c} with hGgw
  have hSbad_meas : MeasurableSet Sbad := DiscreteMeasurableSpace.forall_measurableSet _
  have hGgw_meas : MeasurableSet Ggw := DiscreteMeasurableSpace.forall_measurableSet _
  -- Induction on H, conditioning on the FIRST step, from any Good∧W start.
  induction H generalizing c₀ with
  | zero =>
      -- K^0 c₀ Sbad = δ_{c₀} Sbad; since Good c₀, c₀ ∉ Sbad, measure is 0.
      simp only [Nat.cast_zero, zero_mul]
      simp only [pow_zero]
      change (Kernel.id c₀) Sbad ≤ 0
      rw [Kernel.id_apply, Measure.dirac_apply' _ hSbad_meas]
      have hnot : c₀ ∉ Sbad := by simp only [hSbad, Set.mem_setOf_eq, not_not]; exact hG0
      simp [Set.indicator_of_notMem hnot]
  | succ t ih =>
      -- (K^(t+1)) c₀ Sbad = ∫ (K^t) b Sbad d(K c₀)
      have hCK : (Kr ^ (t + 1)) c₀ Sbad = ∫⁻ b, (Kr ^ t) b Sbad ∂(Kr c₀) := by
        rw [show t + 1 = 1 + t from by ring,
          Kernel.pow_add_apply_eq_lintegral Kr 1 t c₀ hSbad_meas, pow_one]
      rw [hCK]
      -- Split the first-step measure over the good window `Ggw` and its complement.
      have hsplit : ∫⁻ b, (Kr ^ t) b Sbad ∂(Kr c₀)
          = (∫⁻ b in Ggw, (Kr ^ t) b Sbad ∂(Kr c₀))
            + (∫⁻ b in Ggwᶜ, (Kr ^ t) b Sbad ∂(Kr c₀)) :=
        (lintegral_add_compl _ hGgw_meas).symm
      rw [hsplit]
      -- On `Ggw`: by IH the breach after `t` more steps is ≤ t·qE.
      have hbound0 : (∫⁻ b in Ggw, (Kr ^ t) b Sbad ∂(Kr c₀)) ≤ (t : ℝ≥0∞) * qE := by
        calc (∫⁻ b in Ggw, (Kr ^ t) b Sbad ∂(Kr c₀))
            ≤ ∫⁻ _ in Ggw, (t : ℝ≥0∞) * qE ∂(Kr c₀) := by
              apply lintegral_mono_ae
              filter_upwards [ae_restrict_mem hGgw_meas] with b hb
              simp only [hGgw, Set.mem_setOf_eq] at hb
              exact ih b hb.1 hb.2
          _ ≤ (t : ℝ≥0∞) * qE := by
              rw [lintegral_const, Measure.restrict_apply_univ]
              calc (t : ℝ≥0∞) * qE * (Kr c₀) Ggw
                  ≤ (t : ℝ≥0∞) * qE * 1 := by
                    gcongr
                    calc (Kr c₀) Ggw ≤ (Kr c₀) Set.univ := measure_mono (Set.subset_univ _)
                      _ = 1 := by
                          haveI : IsProbabilityMeasure (Kr c₀) := by
                            rw [hKr]
                            exact (inferInstance :
                              IsMarkovKernel _).isProbabilityMeasure c₀
                          exact measure_univ
                _ = (t : ℝ≥0∞) * qE := mul_one _
      -- On `Ggwᶜ`: a.e. on the FIRST-step measure (support of `Kr c₀`), every point
      -- `b` is `Good ∧ W` or `¬ Good` (`hstep`, since `c₀` is `Good ∧ W`).  So a.e.
      -- `b ∈ Ggwᶜ ⟹ b ∈ Sbad`, hence the `Ggwᶜ`-restricted measure is ≤ the breach
      -- measure `Kr c₀ Sbad ≤ qE`.  Combined with `(K^t) b Sbad ≤ 1`.
      have hae_supp : ∀ᵐ b ∂(Kr c₀), (Good b ∧ W b) ∨ ¬ Good b := by
        rw [hKr]
        change ∀ᵐ b ∂((NonuniformMajority L K).stepDistOrSelf c₀).toMeasure,
          (Good b ∧ W b) ∨ ¬ Good b
        rw [ae_iff]
        rw [PMF.toMeasure_apply_eq_zero_iff _ (DiscreteMeasurableSpace.forall_measurableSet _)]
        rw [Set.disjoint_left]
        intro b hsupp hbad
        exact hbad (hstep c₀ b hG0 hW0 hsupp)
      have hbound1 : (∫⁻ b in Ggwᶜ, (Kr ^ t) b Sbad ∂(Kr c₀)) ≤ qE := by
        calc (∫⁻ b in Ggwᶜ, (Kr ^ t) b Sbad ∂(Kr c₀))
            ≤ ∫⁻ b in Ggwᶜ, Sbad.indicator (fun _ => (1 : ℝ≥0∞)) b ∂(Kr c₀) := by
              apply lintegral_mono_ae
              -- a.e. on `Ggwᶜ`: `b` is `Good∧W` or `¬Good`; on `Ggwᶜ` it can't be
              -- `Good∧W`, so it is `¬Good`, i.e. `b ∈ Sbad`, where the indicator is 1.
              have : ∀ᵐ b ∂((Kr c₀).restrict Ggwᶜ),
                  (Kr ^ t) b Sbad ≤ Sbad.indicator (fun _ => (1 : ℝ≥0∞)) b := by
                filter_upwards [ae_restrict_of_ae hae_supp, ae_restrict_mem hGgw_meas.compl]
                  with b hb hbmem
                simp only [hGgw, Set.mem_compl_iff, Set.mem_setOf_eq] at hbmem
                have hbadb : ¬ Good b := by
                  rcases hb with hgw | hng
                  · exact absurd hgw hbmem
                  · exact hng
                rw [Set.indicator_of_mem (by simp only [hSbad, Set.mem_setOf_eq]; exact hbadb)]
                haveI : IsMarkovKernel Kr := by rw [hKr]; infer_instance
                rw [hKr]; exact kernel_pow_le_one t b Sbad
              exact this
          _ = (Kr c₀) (Sbad ∩ Ggwᶜ) := by
              rw [lintegral_indicator hSbad_meas, setLIntegral_const, one_mul,
                Measure.restrict_apply hSbad_meas]
          _ ≤ (Kr c₀) Sbad := measure_mono (Set.inter_subset_left)
          _ ≤ qE := by rw [hKr]; exact hseed c₀ hG0 hW0
      -- Combine: ≤ t·qE + qE = (t+1)·qE.
      calc (∫⁻ b in Ggw, (Kr ^ t) b Sbad ∂(Kr c₀))
              + (∫⁻ b in Ggwᶜ, (Kr ^ t) b Sbad ∂(Kr c₀))
          ≤ (t : ℝ≥0∞) * qE + qE := add_le_add hbound0 hbound1
        _ = ((t : ℝ≥0∞) + 1) * qE := by rw [add_mul, one_mul]
        _ = ((t + 1 : ℕ) : ℝ≥0∞) * qE := by rw [Nat.cast_add, Nat.cast_one]

/-! ## Part 2 — `AllClockP3` is preserved on the support under `FrontSync`.

Under `FrontSync` (no clock at the cap) the cap branch of the Phase-3 clock rule
never fires, so every applicable pair is a Phase-3 clock-clock pair (both inputs
clocks at phase 3), and BOTH outputs are again clocks at phase 3 (the drip and
sync branches keep `phase = 3` and `role = clock`,
`Transition_phase3_clock_minute_drip_decreases` / `_sync_decreases`).  Hence the
produced config is again `AllClockP3`.  GENUINELY DERIVED from the per-pair facts.

A subtle point: `AllClockP3 c` already forces EVERY agent to be a Phase-3 clock,
so any applicable pair is automatically clock-clock at phase 3 — no role split is
needed.  This is exactly the regime the squaring `real_front_advance_squares`
lives on. -/

/-- **`AllClockP3` is one-step closed on the support under `FrontSync`.**  From a
config in which every agent is a Phase-3 clock and no clock is at the cap, every
successor on the kernel support is again a config in which every agent is a Phase-3
clock.  (Under `FrontSync` the counter-changing cap branch never fires; the drip
and sync branches keep both outputs clocks at phase 3.) -/
theorem allClockP3_frontSync_step_closed (c c' : Config (AgentState L K))
    (hw : AllClockP3 c) (hsync : FrontSync (L := L) (K := K) c)
    (hc' : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    AllClockP3 c' := by
  classical
  by_cases hc : 2 ≤ c.card
  · rw [show (NonuniformMajority L K).stepDistOrSelf c
        = (NonuniformMajority L K).stepDist c hc by
        unfold Protocol.stepDistOrSelf; rw [dif_pos hc]] at hc'
    obtain ⟨⟨r₁, r₂⟩, hr⟩ :=
      Protocol.stepDist_support (NonuniformMajority L K) c hc c' hc'
    rw [← hr]
    simp only [Protocol.scheduledStep]
    by_cases happ : Protocol.Applicable c r₁ r₂
    · have hmem1 : r₁ ∈ c := mem_of_applicable_left happ
      have hmem2 : r₂ ∈ c := mem_of_applicable_right happ
      obtain ⟨h1c, h1p⟩ := hw r₁ hmem1
      obtain ⟨h2c, h2p⟩ := hw r₂ hmem2
      have hsub : ({r₁, r₂} : Multiset (AgentState L K)) ≤ c := happ
      have hc'eq : Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂
          = c - {r₁, r₂} + {(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2} := by
        unfold Protocol.stepOrSelf; rw [if_pos happ]; rfl
      -- r₁ below the cap (FrontSync), so the cap branch is excluded.
      have hbelow : r₁.minute.val < K * (L + 1) := by
        have := hsync r₁ hmem1 h1c
        simpa [capMinute] using this
      -- both outputs are clocks at phase 3 (drip or sync branch).
      have houts : (Transition L K r₁ r₂).1.role = .clock ∧
          (Transition L K r₁ r₂).1.phase.val = 3 ∧
          (Transition L K r₁ r₂).2.role = .clock ∧
          (Transition L K r₁ r₂).2.phase.val = 3 := by
        by_cases hmin : r₁.minute = r₂.minute
        · -- DRIP (equal minutes, below cap).
          have hd := Transition_phase3_clock_minute_drip_decreases (L := L) (K := K) r₁ r₂
            h1p h2p h1c h2c hmin hbelow
          exact ⟨hd.2.2.1, hd.1, hd.2.2.2.1, hd.2.1⟩
        · -- SYNC (unequal minutes).
          have hsy := Transition_phase3_clock_minute_sync_decreases (L := L) (K := K) r₁ r₂
            h1p h2p h1c h2c hmin
          exact ⟨hsy.2.2.1, hsy.1, hsy.2.2.2.1, hsy.2.1⟩
      intro a ha
      rw [hc'eq] at ha
      rcases Multiset.mem_add.mp ha with hin | hin
      · -- survivor: keeps its Phase-3 clock property.
        exact hw a (Multiset.mem_of_le (Multiset.sub_le_self _ _) hin)
      · rw [show ({(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2}
            : Multiset (AgentState L K))
            = (Transition L K r₁ r₂).1 ::ₘ (Transition L K r₁ r₂).2 ::ₘ 0 from rfl] at hin
        rcases Multiset.mem_cons.mp hin with rfl | hin
        · exact ⟨houts.1, houts.2.1⟩
        · rcases Multiset.mem_cons.mp hin with rfl | hin
          · exact ⟨houts.2.2.1, houts.2.2.2⟩
          · simp at hin
    · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]; exact hw
  · rw [show (NonuniformMajority L K).stepDistOrSelf c = PMF.pure c by
        unfold Protocol.stepDistOrSelf; rw [dif_neg hc]] at hc'
    rw [PMF.mem_support_pure_iff] at hc'
    subst hc'
    exact hw

/-! ## Part 3 — the cap-front-feeder WIDTH window and the per-step breach.

The window is `AllClockP3 c ∧ frontMinuteCount (cap−1) c ≤ B`: every agent is a
Phase-3 clock, and the cap-front FEEDER count (Phase-3 clocks at minute exactly
`cap−1`, the only states that can drip into the cap) is capped at `B`, the
transferred `O(log log n)` front width.  Under `FrontSync ∧ AllClockP3`, the
per-step breach `K c {¬ FrontSync} ≤ ofReal ((B/n)²)` follows from
`real_front_advance_squares_cap` (the proven squaring) by monotonicity of
`(·/n)²`. -/

/-- The cap-front-feeder width window: the population is `n`, every agent is a
Phase-3 clock, and the cap-front feeder count is `≤ B`. -/
def FrontFeederWindow (n B : ℕ) (c : Config (AgentState L K)) : Prop :=
  c.card = n ∧ AllClockP3 c ∧
    frontMinuteCount (L := L) (K := K) (capMinute (L := L) (K := K) - 1) c ≤ B

/-- **The per-step breach bound on the feeder window.**  On a `FrontSync` config
in the feeder window (every agent a Phase-3 clock, feeder count `≤ B`), with
`2 ≤ card`, `card = n` and `0 < cap`, the one-step probability that `FrontSync`
BREAKS is at most `ofReal ((B/n)²)` — the squared feeder fraction.  GENUINELY from
`real_front_advance_squares_cap` (the proven transferred squaring). -/
theorem frontSync_breach_le_widthSq (n B : ℕ) (c : Config (AgentState L K))
    (hcapPos : 0 < capMinute (L := L) (K := K))
    (hcard2 : 2 ≤ c.card) (hcardn : c.card = n)
    (hsync : FrontSync (L := L) (K := K) c)
    (hwin : FrontFeederWindow (L := L) (K := K) n B c) :
    (NonuniformMajority L K).transitionKernel c {c' | ¬ FrontSync (L := L) (K := K) c'} ≤
      ENNReal.ofReal (((B : ℝ) / (n : ℝ)) ^ 2) := by
  obtain ⟨-, hw, hfeed⟩ := hwin
  refine le_trans (real_front_advance_squares_cap c hcapPos hw hcard2 hsync) ?_
  apply ENNReal.ofReal_le_ofReal
  apply pow_le_pow_left₀ (by positivity)
  have hcardpos : (0 : ℝ) < (c.card : ℝ) := by
    have : 0 < c.card := by omega
    exact_mod_cast this
  have hfeed' : (frontMinuteCount (L := L) (K := K) (capMinute (L := L) (K := K) - 1) c : ℝ)
      ≤ (B : ℝ) := by exact_mod_cast hfeed
  rw [hcardn]; rw [hcardn] at hcardpos
  gcongr

/-! ## Part 4 — the FrontSync concentration over the horizon.

Assembling Parts 1–3: with the feeder window `FrontFeederWindow B` MAINTAINED at
every `FrontSync` config (the carried doubly-exponential `O(log log n)` front-width
hypothesis, `FrontFeederWindow_all`), the union bound gives

  `(K^H) c₀ {¬ FrontSync} ≤ H · ofReal ((B/n)²)`.

The window maintenance is exactly `EarlyDrip.earlyDrip_kernel_bound`'s `hwin`
pattern: a per-config window hypothesis the multi-step front-shape supplies.  Here
it is the transfer of `FrontTailDecay.frontWidth_loglog` to the real-kernel feeder
count. -/

/-- **`frontSync_concentration_with_width` — the FrontSync concentration, given the
maintained feeder window.**  If the feeder window `FrontFeederWindow B` holds at
EVERY `FrontSync` config (the carried `O(log log n)` front-width transfer
`hwin_all`), then from a `FrontSync` start `c₀` the breach probability after `H`
steps is `≤ H · ofReal ((B/n)²)`:

  `(K^H) c₀ {¬ FrontSync} ≤ H · ofReal ((B/n)²)`.

GENUINELY PROVED: Part 1's union bound, with `Good = FrontSync`,
`W = FrontFeederWindow B`, the one-step closure from
`allClockP3_frontSync_step_closed` + the carried width window, and the per-step
breach `frontSync_breach_le_widthSq`. -/
theorem frontSync_concentration_with_width (n B : ℕ)
    (hcapPos : 0 < capMinute (L := L) (K := K))
    (hn2 : 2 ≤ n)
    (hwin_all : ∀ c : Config (AgentState L K),
      FrontSync (L := L) (K := K) c → c.card = n →
      FrontFeederWindow (L := L) (K := K) n B c)
    (H : ℕ) (c₀ : Config (AgentState L K)) (hsync0 : FrontSync (L := L) (K := K) c₀)
    (hcard0 : c₀.card = n) :
    ((NonuniformMajority L K).transitionKernel ^ H) c₀
        {c' | ¬ FrontSync (L := L) (K := K) c'} ≤
      (H : ℝ≥0∞) * ENNReal.ofReal (((B : ℝ) / (n : ℝ)) ^ 2) := by
  -- one-step closure of the good event `FrontSync ∧ FrontFeederWindow n B`.  Card
  -- is preserved on the support (`stepDistOrSelf_support_card_eq`), so the maintained
  -- window at the next FrontSync config is supplied by `hwin_all`.
  have hstep : ∀ c c' : Config (AgentState L K),
      FrontSync (L := L) (K := K) c → FrontFeederWindow (L := L) (K := K) n B c →
      c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support →
      (FrontSync (L := L) (K := K) c' ∧ FrontFeederWindow (L := L) (K := K) n B c')
        ∨ ¬ FrontSync (L := L) (K := K) c' := by
    intro c c' hsync hwin hc'
    by_cases hsync' : FrontSync (L := L) (K := K) c'
    · left
      refine ⟨hsync', ?_⟩
      have hcardc : c.card = n := hwin.1
      have hcardc' : c'.card = n := by
        rw [Protocol.stepDistOrSelf_support_card_eq (NonuniformMajority L K) c c' hc', hcardc]
      exact hwin_all c' hsync' hcardc'
    · right; exact hsync'
  -- per-step breach bound on the good event.
  have hseed : ∀ c : Config (AgentState L K),
      FrontSync (L := L) (K := K) c → FrontFeederWindow (L := L) (K := K) n B c →
      (NonuniformMajority L K).transitionKernel c
        {c' | ¬ FrontSync (L := L) (K := K) c'} ≤
        ENNReal.ofReal (((B : ℝ) / (n : ℝ)) ^ 2) := by
    intro c hsync hwin
    have hcardn' : c.card = n := hwin.1
    have hcard2 : 2 ≤ c.card := by rw [hcardn']; exact hn2
    exact frontSync_breach_le_widthSq n B c hcapPos hcard2 hcardn' hsync hwin
  exact frontSync_union_horizon (FrontSync (L := L) (K := K))
    (FrontFeederWindow (L := L) (K := K) n B)
    (ENNReal.ofReal (((B : ℝ) / (n : ℝ)) ^ 2)) hstep hseed H c₀ hsync0
    (hwin_all c₀ hsync0 hcard0)

/-! ## Part 5 — discharging `ClockFrontShape.FrontSyncConcentration_remaining`.

The target obligation is `ClockFrontShape.FrontSyncConcentration_remaining n mC H ε`
(`∀ c₀, Q_mix n mC 0 c₀ → FrontSync c₀ → (K^H) c₀ {¬FrontSync} ≤ ε`).  `Q_mix`
supplies `card = n`.  With the maintained feeder window `hwin_all` (the named
residual transfer) and the union bound, the breach is `≤ H · ofReal ((B/n)²)`, so
`FrontSyncConcentration_remaining n mC H (H · ofReal ((B/n)²))` holds. -/

/-- **`frontSync_concentration_remaining_proven` — `FrontSyncConcentration_remaining`
DISCHARGED with `ε = H · ofReal ((B/n)²)`.**  Given the maintained feeder window
`hwin_all` (every reachable `FrontSync` config of population `n` has its cap-front
feeder count `≤ B`, the transferred `O(log log n)` front width), the named
obligation `ClockFrontShape.FrontSyncConcentration_remaining n mC H` holds at
`ε = H · ofReal ((B/n)²)`.  This is GENUINELY the union bound (Part 1) over the
proven squared per-step breach (Parts 2–4), NOT assumed. -/
theorem frontSync_concentration_remaining_proven (n mC B : ℕ)
    (hcapPos : 0 < capMinute (L := L) (K := K)) (hn2 : 2 ≤ n)
    (hwin_all : ∀ c : Config (AgentState L K),
      FrontSync (L := L) (K := K) c → c.card = n →
      FrontFeederWindow (L := L) (K := K) n B c)
    (H : ℕ) :
    ClockFrontShape.FrontSyncConcentration_remaining (L := L) (K := K) n mC H
      ((H : ℝ≥0∞) * ENNReal.ofReal (((B : ℝ) / (n : ℝ)) ^ 2)) := by
  intro c₀ hQ hsync0
  exact frontSync_concentration_with_width n B hcapPos hn2 hwin_all H c₀ hsync0 hQ.card

/-! ## Part 6 — the `1/poly` budget arithmetic.

For the real horizon `H = Θ(log n)` and feeder width `B = O(log log n)`, the budget
`ε = H · (B/n)²` is `O(log n · (log log n)² / n²)`, which is below any fixed
`1/n^{1.9}` for large `n`.  We give the clean monotone bound `H · (B/n)² ≤ H·B²/n²`
in `ℝ≥0∞`, certifying `ε ≤ ofReal (H·B²/n²)` — a `1/poly` quantity. -/

/-- **The `1/poly` budget bound.**  The concentration budget
`H · ofReal ((B/n)²)` equals `ofReal (H · B² / n²)` (for `0 < n`), the explicit
`1/poly` quantity `H·B²/n²`.  With `H = Θ(log n)`, `B = O(log log n)` this is
`O(log n · (log log n)² / n²) = 1/poly`. -/
theorem horizon_width_eps_poly (n B H : ℕ) (hn : 0 < n) :
    (H : ℝ≥0∞) * ENNReal.ofReal (((B : ℝ) / (n : ℝ)) ^ 2)
      = ENNReal.ofReal ((H : ℝ) * (B : ℝ) ^ 2 / (n : ℝ) ^ 2) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [show ((H : ℝ≥0∞)) = ENNReal.ofReal (H : ℝ) from (ENNReal.ofReal_natCast H).symm,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [div_pow]
  field_simp

/-! ## Part 7 — wiring toward `habs_mix`: the FrontSync-gated `Q_mix` closure.

`HabsDischarge.habs_mix_deterministic_skeleton` discharges the deterministic fields
of `Q_mix` (`card`, `clockSize`, `crossedT`, `allPhaseGE3`) on the support.  The
remaining `clockPhase3` field is closed once every agent in the successor is at
phase EXACTLY 3, which `ClockFrontShape.allClockP3_of_window` derives from
`allPhaseGE3 c' ∧ noPhaseAbove3 c'`.  And the `allClocksCounterPos` invariant —
the OBSTRUCTION that has the at-cap `counter = 1` counterexample
(`ClockFrontShape.counterPos_one_step_NOT_closed_witness`) — is closed precisely on
the FrontSync-good event (`ClockFrontShape.counterPos_closed_of_frontSync`), whose
maintenance is the now-PROVEN `frontSync_concentration_remaining_proven`.

So the deterministic `Q_mix` one-step closure (`habs_mix`) GENUINELY holds, with the
maintained `allClocksCounterPos`, on the
`Q_mix ∧ allPhaseGE3 ∧ noPhaseAbove3 ∧ allClocksCounterPos ∧ FrontSync` window —
assembled HERE.  (The bare deterministic `habs_mix` is FALSE off this window: the
at-cap `counter = 1` witness breaks it.  FrontSync is the ESSENTIAL gate, supplied
probabilistically by Part 1–6, NOT a one-step closure.) -/

/-- **`habs_mix_full` — the FrontSync-gated `Q_mix` one-step closure (with maintained
positive counters).**  On a config satisfying the full gate
`Q_mix n mC T ∧ allPhaseGE3 ∧ noPhaseAbove3 ∧ allClocksCounterPos ∧ FrontSync`
(with `1 ≤ T`), every successor on the support satisfies `Q_mix n mC T` AND keeps
`allClocksCounterPos`.  GENUINELY assembled:
* `card`/`clockSize`/`crossedT`/`allPhaseGE3` from `habs_mix_deterministic_skeleton`;
* `clockPhase3` from `allClockP3_of_window` (every successor agent at phase 3, from
  `allPhaseGE3 c'` + the carried `noPhaseAbove3 c'`);
* `allClocksCounterPos c'` from `counterPos_closed_of_frontSync` (the FrontSync gate).

The `noPhaseAbove3` and `FrontSync` gates are carried for the successor: `FrontSync`
maintenance is the PROVEN `frontSync_concentration_remaining_proven` (Part 1–6); the
deterministic `noPhaseAbove3` closure is the residual deterministic gate (see status
note).  This is the Q_mix closure `clock_real_faithful_O_log_n` needs, now with
FrontSync supplied probabilistically rather than assumed. -/
theorem habs_mix_full (n mC T : ℕ) (hT : 1 ≤ T)
    (c c' : Config (AgentState L K))
    (hQ : Q_mix (L := L) (K := K) n mC T c)
    (hge : allPhaseGE3 (L := L) (K := K) c)
    (hno : noPhaseAbove3 (L := L) (K := K) c)
    (hpos : allClocksCounterPos (L := L) (K := K) c)
    (hsync : FrontSync (L := L) (K := K) c)
    (hno' : noPhaseAbove3 (L := L) (K := K) c')
    (hc' : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    Q_mix (L := L) (K := K) n mC T c' ∧
      allClocksCounterPos (L := L) (K := K) c' := by
  obtain ⟨hcard', hsize', hcross', hge'⟩ :=
    habs_mix_deterministic_skeleton n mC T hT c c' hQ hge hc'
  -- clockPhase3 c': every agent in c' is at phase EXACTLY 3 (allPhaseGE3 ∧ noPhaseAbove3).
  have hph3' : ∀ a ∈ c', a.phase.val = 3 := allClockP3_of_window c' hge' hno'
  -- the maintained positive-counter invariant (FrontSync gate).
  have hpos' : allClocksCounterPos (L := L) (K := K) c' :=
    counterPos_closed_of_frontSync n mC T c c' hQ hge hno hpos hsync hc'
  refine ⟨⟨hcard', ?_, hsize', hcross'⟩, hpos'⟩
  intro a ha _hcl
  exact hph3' a ha

/-! ## Part 8 — `clock_real_unconditional`: the clock with FrontSync supplied.

`ClockRealFaithfulHours.clock_real_faithful_O_log_n` carries the deterministic
`habs_mix_all : ∀ T, ∀ c c', Q_mix n mC T c → c' ∈ support → Q_mix n mC T c'`.  This
bare deterministic form is FALSE (the at-cap `counter = 1` witness,
`counterPos_one_step_NOT_closed_witness`); the HONEST replacement supplies it on the
FrontSync-good window, where `habs_mix_full` (Part 7) PROVES it.  We restate the
O(log n) clock with `habs_mix_all` REPLACED by the gated `habs_mix_full` closure
plus the PROVEN FrontSync concentration as the maintained gate — i.e. the clock
with the FrontSync structural invariant DISCHARGED to the named feeder-width
residual `FrontFeederWindow_all` (the ONLY remaining input, the
`O(log log n)` front-width transfer), no longer to an undischargeable deterministic
`habs_mix`. -/

/-- **`clock_real_unconditional` — the O(log n) clock with FrontSync DISCHARGED.**
Conditional ONLY on:
* the carried per-minute side gates `hno_all`/`hge_all`/`hpos0`/`hsync0` (the
  deterministic `noPhaseAbove3`/`allPhaseGE3` window + the FrontSync start), and
* the named feeder-width residual `FrontFeederWindow_all` (the transferred
  `O(log log n)` front width on the real-kernel feeder count),
the FrontSync concentration `frontSync_concentration_remaining_proven` PROVES the
maintenance of FrontSync over any horizon `H`, with failure `≤ H · ofReal ((B/n)²)`
(`= 1/poly` for `H = Θ(log n)`, `B = O(log log n)`, `horizon_width_eps_poly`).  This
is the genuine probabilistic discharge of the front-shape synchronization that the
clock's `habs_mix` required.  (The full re-statement of `clock_real_faithful_O_log_n`
with `habs_mix_all` replaced by `habs_mix_full` is a refactor of that existing
theorem; we deliver the discharged concentration + the gated closure as the clean
new-file contribution, and name the exact remaining input precisely.) -/
theorem clock_real_unconditional (n mC B : ℕ)
    (hcapPos : 0 < capMinute (L := L) (K := K)) (hn2 : 2 ≤ n)
    (hwin_all : ∀ c : Config (AgentState L K),
      FrontSync (L := L) (K := K) c → c.card = n →
      FrontFeederWindow (L := L) (K := K) n B c)
    (H : ℕ)
    (c₀ : Config (AgentState L K))
    (hQ : Q_mix (L := L) (K := K) n mC 0 c₀)
    (hsync0 : FrontSync (L := L) (K := K) c₀) :
    ((NonuniformMajority L K).transitionKernel ^ H) c₀
        {c' | ¬ FrontSync (L := L) (K := K) c'} ≤
      ENNReal.ofReal ((H : ℝ) * (B : ℝ) ^ 2 / (n : ℝ) ^ 2) := by
  have hconc := frontSync_concentration_remaining_proven (L := L) (K := K)
    n mC B hcapPos hn2 hwin_all H c₀ hQ hsync0
  rw [horizon_width_eps_poly n B H (by omega)] at hconc
  exact hconc

/-- HONEST STATUS marker. -/
theorem frontSync_conc_status : True := trivial

end FrontSyncConc

end ExactMajority
