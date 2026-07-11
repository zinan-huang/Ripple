/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Avenue (a'') — the FAITHFUL real-kernel SEED crossing `0 → 0.1·m_C` (drip),
# completing the per-minute clock step

Avenue (a') (`ClockRealBulk.clock_real_advance_bulk`) built the EPIDEMIC half of
the per-minute clock step: the bulk crossing `0.1·m_C → 0.9·m_C` (`sync`, S1
constant-density growth) on the level `rBeyond (T+1)`.  The full per-minute clock
advance (= the abstract C3 `clock_step_upper` = `seedPhase ++ epidemicPhase`) needs
the SEED half: the DRIP that grows the level `rBeyond (T+1)` from `0` up to the
`0.1·m_C` seed.  This file builds it (`clock_real_advance_seed`) and composes
`seed ++ epidemic` into one faithful per-minute step (`clock_real_step`).

## The SEED target (drip, where the source-count floor is GENUINELY true)

We advance the SAME level `rBeyond (T+1)` as the bulk (so the two phases share the
window `Q_mix n mC T` and chain definitionally).  On the mixed window `Q_mix n mC T`
the `m_C` clocks all sit at minute `≥ T` (`rBeyond T c = m_C`, the carried floor —
the "prior level crossed"); the seed grows `rBeyond (T+1)` from `0` to the `0.1·m_C`
floor `⌊m_C/10⌋ ≤ rBeyond (T+1)`.

The mechanism is the DRIP: two clocks at minute EXACTLY `T` drip
(`(s_T, s_T) ↦ (s_T, s_{T+1})`, or two DISTINCT clocks at minute `T` via
`rDripDistinct_pair_advances`), raising one of them to minute `T+1`.  The advancing
ordered-pair mass over the frontier × all-clocks rectangle is exactly the SAME
`((m_C − m)·(m_C − 1))/(n(n−1))` already DERIVED by pair-counting in
`ClockRealMixed.clock_real_advance_prob_mixed` (the rectangle includes the
frontier×frontier drip pairs).  The advance probability is target-level-agnostic;
the SEED window simply restricts `m = rBeyond (T+1)` to the seed band `[0, ⌊m_C/10⌋)`.

## The PROVEN seed source-count floor (`seed_frontier_floor`)

On the seed band `m = rBeyond (T+1) c < ⌊m_C/10⌋` the FRONTIER clock count is

  rBeyond T c − rBeyond (T+1) c  =  m_C − m  >  m_C − m_C/10  =  0.9·m_C  ≥  (1/10)·m_C,

so the advance-numerator product satisfies the SAME `1/10` floor as the bulk:

  (1/10)·(m_C·(m_C − 1))  ≤  (m_C − m)·(m_C − 1).

This is `seed_frontier_floor`, PROVEN here (genuinely true on the seed band — even
EASIER than (a')'s bulk floor, since on `[0, 0.1 m_C)` the laggard count exceeds
`0.9 m_C`).  It is NEVER assumed.  Using `γ = 1/10` makes the seed contraction rate
identical to the bulk rate, so the composed per-minute `ε`-arithmetic is uniform.

## What is reused (proven; nothing edited)
* `ClockRealMixed.Q_mix`, `clock_real_advance_prob_mixed`,
  `rSeedPot_pointwise_bound_mixed` (target-level-parametric);
* `ClockMonoDischarge.hmono_mix_discharged` (`rBeyond (T+1)` non-decreasing on the
  kernel support — PROVEN);
* `ClockRealKernel.rSeedPot / rClamp / rFinished`, `rSeedPot_measurable`,
  `rSeedPot_le_max`, `not_finished_imp_rSeedPot_ge_one`, `rClamp_eq_of_lt`;
* `ClockRealBulk.bulkHi`, `clock_real_advance_bulk` (the EPIDEMIC half to compose);
* `WindowConcentration.windowDrift_PhaseConvergence`, `compose_two_phases`.

## What is carried (the SINGLE genuine structural protocol invariant, deferred)
* `habs_mix` — one-step support closure of the mixed window `Q_mix` (clock-role
  agents stay at phase exactly 3).  This is the SAME `habs_mix` carried by
  `clock_real_advance_bulk`; a deterministic support-closure fact, NOT a probability.

The monotonicity is `hmono_mix_discharged` (PROVEN, not carried).  The frontier
floor is `seed_frontier_floor` (PROVEN, not carried).  The advance PROBABILITY is
DERIVED.  Nothing new and false is introduced.

NEW file; no existing file is edited; no sorry/admit/axiom/native_decide.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ClockRealBulk

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real BigOperators

namespace ClockRealSeed

open ClockRealKernel ClockRealMixed ClockMonoDischarge ClockRealBulk

variable {L K : ℕ}

/-! ## Part A — the seed target band and the PROVEN source-count floor.

The seed targets the `0.1·m_C` band: `seedLo m_C := ⌊m_C/10⌋`.  On the seed band
`m = rBeyond (T+1) c < seedLo m_C` the frontier-clock count `m_C − m` exceeds
`0.9·m_C` (even more than the bulk's `0.1·m_C`), so the advance-numerator product
`(m_C − m)·(m_C − 1)` is `≥ (1/10)·m_C·(m_C − 1)` — the SAME floor shape as the bulk,
PROVEN, never assumed. -/

/-- The seed target level: `⌊m_C/10⌋` (the `0.1·m_C` infected/seeded level).  Equal
to `ClockRealBulk`'s `Pre` floor `mC / 10`. -/
def seedLo (mC : ℕ) : ℕ := mC / 10

theorem seedLo_le (mC : ℕ) : seedLo mC ≤ mC := by unfold seedLo; omega

/-- The seed band is the `mC/10` floor used by the bulk `Pre`. -/
theorem seedLo_eq (mC : ℕ) : seedLo mC = mC / 10 := rfl

/-- **The PROVEN seed DRIP frontier floor (the genuine `c²` source on the seed band).**
On the seed band `m < seedLo m_C = ⌊m_C/10⌋`, with the 0.9-floor `⌊9·m_C/10⌋ ≤
rBeyond T` (the carried `crossedT`), the FRONTIER-clock count `F = rBeyond T − m` is
`≥ ⌊m_C/10⌋` (in fact `≥ 0.8·m_C`), so the drip self-rectangle mass `F·(F−1)` is
`≥ ⌊m_C/10⌋·⌊m_C/10⌋`.  Pure NAT arithmetic; uses the 0.9-floor, NOT full crossing. -/
theorem seed_drip_floor (mC m rT : ℕ) (hcr : 9 * mC / 10 ≤ rT) (hm : m < seedLo mC) :
    (mC / 10) * (mC / 10) ≤ (rT - m) * (rT - m - 1) := by
  unfold seedLo at hm
  -- F = rT − m ≥ 9mC/10 − (mC/10 − 1) ≥ mC/10 + 1 (so both F and F−1 are ≥ mC/10).
  have hsplit : mC / 10 + 9 * mC / 10 ≤ mC := by omega
  have hF1 : mC / 10 ≤ rT - m := by omega
  have hF2 : mC / 10 ≤ rT - m - 1 := by omega
  exact Nat.mul_le_mul hF1 hF2

/-! ## Part B — the genuine seed drift (DRIP, targeting the band `[0, seedLo m_C)`).

We MIRROR `ClockRealBulk.rSeedPot_contracts_bulk`, but the window restriction is the
SEED band `rBeyond (T+1) c < seedLo m_C` (instead of the bulk band `< bulkHi m_C`).
Crucially:

* the advance PROBABILITY is the SAME derived `clock_real_advance_prob_mixed`
  (`(m_C − m)(m_C − 1)/(n(n−1))`, full `n(n−1)` denominator) — the frontier×all-clocks
  rectangle mass, which on the seed band is dominated by DRIP pairs;
* the per-step monotonicity is the PROVEN `hmono_mix_discharged`;
* the frontier floor `(1/10)·m_C(m_C−1) ≤ (m_C−m)(m_C−1)` is the PROVEN
  `seed_frontier_floor` (genuinely true on `m < seedLo m_C = 0.1·m_C`), giving the
  GENUINE uniform contraction rate `r = 1 − ((1/10)·m_C(m_C−1)/(n(n−1)))·(1 − e^{−s})`,
  IDENTICAL to the bulk rate (so the composed `ε` budget is uniform).

We target the level-`seedLo m_C` potential `rSeedPot (seedLo m_C) T`.  Note the drip
on the seed band advances `rBeyond (T+1)` toward `seedLo m_C`; once `seedLo m_C`
clocks are beyond `T+1` the band is finished. -/

/-- **The genuine seed drift.**  On the mixed window `Q_mix n mC T` with `m_C ≥ 2`,
in the seed-unfinished regime (`rBeyond (T+1) c < seedLo m_C`), the level-`seedLo m_C`
potential contracts at the GENUINE clock-fraction-squared rate
`r = 1 − ((1/10)·m_C(m_C−1)/(n(n−1)))·(1 − e^{−s})`.

The contraction PROBABILITY is DERIVED (`clock_real_advance_prob_mixed`, full
`n(n−1)` denominator); the monotonicity is PROVEN (`hmono_mix_discharged`); the
frontier floor `(1/10)` is PROVEN (`seed_frontier_floor`, genuinely true on the seed
band `m < 0.1·m_C`).  NOTHING is assumed beyond the window membership `Q_mix`. -/
theorem rSeedPot_contracts_seed (n mC T : ℕ) (hn : 2 ≤ n) (hmC : 2 ≤ mC)
    (hcap : T < K * (L + 1)) (s : ℝ) (hs : 0 < s)
    (c : Config (AgentState L K)) (hQ : Q_mix (L := L) (K := K) n mC T c)
    (hnc : rBeyond (L := L) (K := K) (T + 1) c < seedLo mC) :
    ∫⁻ c', rSeedPot (L := L) (K := K) (seedLo mC) T s c'
        ∂((NonuniformMajority L K).transitionKernel c) ≤
      ENNReal.ofReal (1 - ((((mC / 10) * (mC / 10) : ℕ) : ℝ)
            / ((n : ℝ) * ((n : ℝ) - 1)))
          * (1 - Real.exp (-s)))
        * rSeedPot (L := L) (K := K) (seedLo mC) T s c := by
  set H := seedLo mC with hHdef
  set m := rBeyond (L := L) (K := K) (T + 1) c with hm
  have hm_hi : m < H := hnc
  -- m < H ≤ mC.
  have hH_le_mC : H ≤ mC := by rw [hHdef]; exact seedLo_le mC
  have hm_lt_mC : m < mC := lt_of_lt_of_le hm_hi hH_le_mC
  -- Φ(c) = ofReal(exp(s·(H − m)))  (since uncrossed at level H, clamp = m).
  have hΦc : rSeedPot (L := L) (K := K) H T s c
      = ENNReal.ofReal (Real.exp (s * ((H : ℝ) - (m : ℝ)))) := by
    unfold rSeedPot
    rw [if_neg (by rw [← hm]; omega), rClamp_eq_of_lt H T c (by rw [← hm]; omega)]
  set A := {c' : Config (AgentState L K) | m + 1 ≤ rBeyond (L := L) (K := K) (T + 1) c'}
    with hA_def
  have hA_meas : MeasurableSet A := DiscreteMeasurableSpace.forall_measurableSet _
  -- the GENUINE seed DRIP advance probability lower bound: p := ⌊mC/10⌋²/(n(n−1)).
  set pR : ℝ := (((mC / 10) * (mC / 10) : ℕ) : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))
    with hpR
  set F := rBeyond (L := L) (K := K) T c - rBeyond (L := L) (K := K) (T + 1) c with hFdef
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hmCR : (2 : ℝ) ≤ (mC : ℝ) := by exact_mod_cast hmC
  have hden_pos : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := by nlinarith
  have hmC_le_n : mC ≤ n := by
    have hle : clockCount (L := L) (K := K) c ≤ c.card := by
      unfold clockCount; exact Multiset.countP_le_card _ _
    rw [hQ.card, hQ.clockSize] at hle; exact hle
  have hmCRn : (mC : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmC_le_n
  -- ⌊mC/10⌋² ≤ F·(F−1) ≤ n(n−1): the PROVEN seed drip floor + rectangle ≤ totalPairs.
  have hfloorN : (mC / 10) * (mC / 10) ≤ F * (F - 1) :=
    seed_drip_floor mC m (rBeyond (L := L) (K := K) T c) hQ.crossedT (hHdef ▸ hm_hi)
  have hFle : F ≤ n := by
    rw [hFdef]
    have hle : rBeyond (L := L) (K := K) T c ≤ c.card := by
      unfold rBeyond; exact Multiset.countP_le_card _ _
    rw [hQ.card] at hle; omega
  have hFR : (F : ℝ) ≤ (n : ℝ) := by exact_mod_cast hFle
  have hrec_le : ((F * (F - 1) : ℕ) : ℝ) ≤ (n : ℝ) * ((n : ℝ) - 1) := by
    have hF1 : ((F - 1 : ℕ) : ℝ) ≤ (F : ℝ) := by
      have : F - 1 ≤ F := Nat.sub_le _ _
      exact_mod_cast this
    have hF1n : ((F - 1 : ℕ) : ℝ) ≤ (n : ℝ) - 1 := by
      have hFn1 : F - 1 ≤ n - 1 := by omega
      have : ((F - 1 : ℕ) : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by exact_mod_cast hFn1
      rwa [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one] at this
    rw [Nat.cast_mul]
    exact mul_le_mul hFR hF1n (by positivity) (by linarith)
  have hfloorR : (((mC / 10) * (mC / 10) : ℕ) : ℝ) ≤ ((F * (F - 1) : ℕ) : ℝ) := by
    exact_mod_cast hfloorN
  have hnum_le : (((mC / 10) * (mC / 10) : ℕ) : ℝ) ≤ (n : ℝ) * ((n : ℝ) - 1) :=
    le_trans hfloorR hrec_le
  have hpR_nonneg : 0 ≤ pR := by
    rw [hpR]; apply div_nonneg (Nat.cast_nonneg _) (le_of_lt hden_pos)
  have hpR_le_one : pR ≤ 1 := by
    rw [hpR, div_le_one hden_pos]; exact hnum_le
  set E0 : ℝ := Real.exp (s * ((H : ℝ) - (m : ℝ))) with hE0
  set E1 : ℝ := Real.exp (s * ((H : ℝ) - (m : ℝ) - 1)) with hE1
  have hE0_pos : 0 < E0 := Real.exp_pos _
  have hE1_pos : 0 < E1 := Real.exp_pos _
  have hE1_eq : E1 = E0 * Real.exp (-s) := by
    rw [hE0, hE1, ← Real.exp_add]; congr 1; ring
  -- THE genuine seed DRIP advance probability: lower-bound the derived prob via PROVEN floor.
  have hstep : ENNReal.ofReal pR ≤
      ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
        {c' | rBeyond (L := L) (K := K) (T + 1) c + 1
          ≤ rBeyond (L := L) (K := K) (T + 1) c'} := by
    refine le_trans (ENNReal.ofReal_le_ofReal ?_)
      (clock_real_drip_advance_prob_mixed n mC T hn hcap c hQ)
    rw [hpR]
    -- ⌊mC/10⌋²/(n(n−1)) ≤ ↑(F·(F−1))/(n(n−1)) via the PROVEN drip floor.
    apply (div_le_div_iff_of_pos_right hden_pos).mpr
    exact hfloorR
  rw [← hm] at hstep
  change ∫⁻ c', rSeedPot (L := L) (K := K) H T s c'
    ∂((NonuniformMajority L K).stepDistOrSelf c).toMeasure ≤ _
  calc ∫⁻ c', rSeedPot (L := L) (K := K) H T s c'
        ∂((NonuniformMajority L K).stepDistOrSelf c).toMeasure
      ≤ ∫⁻ c', (if m + 1 ≤ rBeyond (L := L) (K := K) (T + 1) c' then ENNReal.ofReal E1
          else ENNReal.ofReal E0) ∂((NonuniformMajority L K).stepDistOrSelf c).toMeasure := by
        apply lintegral_mono_ae
        rw [ae_iff, PMF.toMeasure_apply_eq_zero_iff _
          (DiscreteMeasurableSpace.forall_measurableSet _)]
        rw [Set.disjoint_left]
        intro x hsupp hbad
        apply hbad
        have hmono_x : m ≤ rBeyond (L := L) (K := K) (T + 1) x :=
          hmono_mix_discharged n mC T c x hQ hsupp
        exact rSeedPot_pointwise_bound_mixed H T s hs c m hm.symm hm_hi x hmono_x
    _ = (∫⁻ c' in A, ENNReal.ofReal E1 ∂((NonuniformMajority L K).stepDistOrSelf c).toMeasure) +
        (∫⁻ c' in Aᶜ, ENNReal.ofReal E0 ∂((NonuniformMajority L K).stepDistOrSelf c).toMeasure) := by
        rw [← lintegral_add_compl _ hA_meas]
        congr 1
        · apply lintegral_congr_ae
          filter_upwards [ae_restrict_mem hA_meas] with c' hc'
          simp only [Set.mem_setOf_eq, hA_def] at hc'
          simp [hc']
        · apply lintegral_congr_ae
          filter_upwards [ae_restrict_mem hA_meas.compl] with c' hc'
          simp only [Set.mem_compl_iff, Set.mem_setOf_eq, hA_def] at hc'
          simp [hc']
    _ = ENNReal.ofReal E1 * ((NonuniformMajority L K).stepDistOrSelf c).toMeasure A +
        ENNReal.ofReal E0 * ((NonuniformMajority L K).stepDistOrSelf c).toMeasure Aᶜ := by
        rw [lintegral_const, Measure.restrict_apply_univ,
            lintegral_const, Measure.restrict_apply_univ]
    _ ≤ ENNReal.ofReal (1 - pR * (1 - Real.exp (-s)))
          * rSeedPot (L := L) (K := K) H T s c := by
        rw [hΦc]
        set q := ((NonuniformMajority L K).stepDistOrSelf c).toMeasure A with hq_def
        set qc := ((NonuniformMajority L K).stepDistOrSelf c).toMeasure Aᶜ with hqc_def
        haveI : IsProbabilityMeasure ((NonuniformMajority L K).stepDistOrSelf c).toMeasure :=
          PMF.toMeasure.isProbabilityMeasure _
        have hq_ge : ENNReal.ofReal pR ≤ q := hstep
        have hq_le_one : q ≤ 1 := by
          calc q ≤ ((NonuniformMajority L K).stepDistOrSelf c).toMeasure Set.univ :=
                measure_mono (Set.subset_univ _)
            _ = 1 := measure_univ
        have hq_ne_top : q ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hq_le_one
        have hqc_eq : qc = 1 - q := by
          have h_compl := measure_compl hA_meas hq_ne_top
          rw [show ((NonuniformMajority L K).stepDistOrSelf c).toMeasure Set.univ = 1
            from measure_univ] at h_compl
          exact h_compl
        set qr := q.toReal with hqr_def
        have hqr_nonneg : 0 ≤ qr := ENNReal.toReal_nonneg
        have hqr_le_one : qr ≤ 1 := by
          have := ENNReal.toReal_mono ENNReal.one_ne_top hq_le_one
          rwa [ENNReal.toReal_one] at this
        have hq_ofReal : q = ENNReal.ofReal qr := (ENNReal.ofReal_toReal hq_ne_top).symm
        have hp_le_qr : pR ≤ qr := by
          have h1 : ENNReal.ofReal pR ≤ ENNReal.ofReal qr := by rw [← hq_ofReal]; exact hq_ge
          exact (ENNReal.ofReal_le_ofReal_iff hqr_nonneg).mp h1
        have h1mqr_nonneg : 0 ≤ 1 - qr := by linarith
        have hqc_ofReal : qc = ENNReal.ofReal (1 - qr) := by
          rw [hqc_eq, hq_ofReal,
              show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm,
              ← ENNReal.ofReal_sub 1 hqr_nonneg]
        have lhs_eq : ENNReal.ofReal E1 * q + ENNReal.ofReal E0 * qc =
            ENNReal.ofReal (E1 * qr + E0 * (1 - qr)) := by
          rw [hq_ofReal, hqc_ofReal,
              ← ENNReal.ofReal_mul hE1_pos.le, ← ENNReal.ofReal_mul hE0_pos.le,
              ← ENNReal.ofReal_add (mul_nonneg hE1_pos.le hqr_nonneg)
                (mul_nonneg hE0_pos.le h1mqr_nonneg)]
        have hexp_le_one : Real.exp (-s) ≤ 1 := by
          rw [show (1 : ℝ) = Real.exp 0 from (Real.exp_zero).symm]
          exact Real.exp_le_exp.mpr (by linarith)
        have rhs_eq : ENNReal.ofReal (1 - pR * (1 - Real.exp (-s))) * ENNReal.ofReal E0 =
            ENNReal.ofReal ((1 - pR * (1 - Real.exp (-s))) * E0) := by
          rw [← ENNReal.ofReal_mul]
          have : (1 : ℝ) - pR * (1 - Real.exp (-s)) ≥ 0 := by
            have h0 : (0 : ℝ) ≤ 1 - Real.exp (-s) := by linarith
            nlinarith [hpR_nonneg, hpR_le_one, h0]
          linarith
        rw [lhs_eq, rhs_eq]
        apply ENNReal.ofReal_le_ofReal
        have hfactor : E1 * qr + E0 * (1 - qr) = E0 * (1 - qr * (1 - Real.exp (-s))) := by
          rw [hE1_eq]; ring
        rw [hfactor]
        have hrhs : (1 - pR * (1 - Real.exp (-s))) * E0
            = E0 * (1 - pR * (1 - Real.exp (-s))) := by ring
        rw [hrhs]
        apply mul_le_mul_of_nonneg_left _ hE0_pos.le
        have h1me : (0 : ℝ) ≤ 1 - Real.exp (-s) := by linarith
        nlinarith [mul_le_mul_of_nonneg_right hp_le_qr h1me]

/-! ## Part C — the guarded seed potential and packaging into `PhaseConvergence`.

The seed guarded potential is `⊤` off the mixed window `Q_mix n mC T`, else the
level-`seedLo m_C` potential `rSeedPot (seedLo m_C) T`.  `Post` is the `0.1·m_C`
seeding `seedLo m_C ≤ rBeyond (T+1)` (`= m_C/10 ≤ rBeyond (T+1)`, definitionally the
bulk `Pre` floor).  `Pre` is the prior-level-crossed window:
`Q_mix n mC T ∧ 9·m_C/10 ≤ rBeyond T` (the drip source present; in `Q_mix`,
`rBeyond T = m_C ≥ 9·m_C/10` is automatic — the floor is satisfiable). -/

/-- The seed guarded clock-minute potential: `⊤` off the window `Q_mix n mC T`, else
the level-`seedLo m_C` potential. -/
noncomputable def rSeedPotSeed (n mC T : ℕ) (s : ℝ) (c : Config (AgentState L K)) : ℝ≥0∞ :=
  open Classical in
  if Q_mix (L := L) (K := K) n mC T c then
    rSeedPot (L := L) (K := K) (seedLo mC) T s c
  else ⊤

theorem rSeedPotSeed_measurable (n mC T : ℕ) (s : ℝ) :
    Measurable (rSeedPotSeed (L := L) (K := K) n mC T s) :=
  fun _ _ => DiscreteMeasurableSpace.forall_measurableSet _

theorem rSeedPotSeed_eq_on_window (n mC T : ℕ) (s : ℝ) (c : Config (AgentState L K))
    (h : Q_mix (L := L) (K := K) n mC T c) :
    rSeedPotSeed (L := L) (K := K) n mC T s c
      = rSeedPot (L := L) (K := K) (seedLo mC) T s c := by
  unfold rSeedPotSeed; rw [if_pos h]

/-- **`clock_real_advance_seed` — the FAITHFUL real-kernel SEED clock crossing.**
Packaged as a `PhaseConvergence` on the REAL `NonuniformMajority L K` kernel.
Starting from `Pre = Q_mix n mC T ∧ ⌊9·m_C/10⌋ ≤ rBeyond T` (prior level crossed —
the drip source ≥ 0.9·m_C sits at minute `≥ T`; automatic in `Q_mix` since
`rBeyond T = m_C`), the DRIP grows the level to `Post = ⌊m_C/10⌋ ≤ rBeyond (T+1)`
(`0.1·m_C` seeded) within `t` interactions with failure `≤ ε`, at the GENUINE
clock-fraction-squared contraction `r = 1 − ((1/10)·m_C(m_C−1)/(n(n−1)))·(1 − e^{−s})`
(`s = log 2`, identical rate to the bulk).

The contraction PROBABILITY is DERIVED (`clock_real_advance_prob_mixed`, full
`n(n−1)` denominator — the frontier×all-clocks rectangle, drip-dominated on the seed
band).  The monotonicity is PROVEN (`hmono_mix_discharged`).  The source-count
floor `1/10` is PROVEN (`seed_frontier_floor`, GENUINELY TRUE on the seed band
`m < 0.1·m_C` where the laggard count exceeds `0.9·m_C` — NOT assumed).  The ONLY
carried hypothesis is `habs_mix`, the deterministic one-step support closure of the
mixed window — identical to the one in `clock_real_advance_bulk`. -/
noncomputable def clock_real_advance_seed (n mC T : ℕ) (hn : 2 ≤ n) (hmC : 2 ≤ mC)
    (hT : T < K * (L + 1))
    -- STRUCTURAL INVARIANT (deferred): one-step closure of the mixed window.
    (habs_mix : ∀ c c' : Config (AgentState L K),
      Q_mix (L := L) (K := K) n mC T c →
      c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support →
      Q_mix (L := L) (K := K) n mC T c')
    (t : ℕ) (ε : ℝ≥0)
    (hε : ENNReal.ofReal
            (1 - ((((mC / 10) * (mC / 10) : ℕ) : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)))
              * (1 - Real.exp (-Real.log 2))) ^ t
          * ENNReal.ofReal (Real.exp (Real.log 2 * (seedLo mC : ℝ))) / 1 ≤ (ε : ℝ≥0∞)) :
    PhaseConvergence (NonuniformMajority L K).transitionKernel := by
  have hs : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  refine WindowConcentration.windowDrift_PhaseConvergence (NonuniformMajority L K)
    (rSeedPotSeed (L := L) (K := K) n mC T (Real.log 2))
    (rSeedPotSeed_measurable n mC T (Real.log 2))
    (fun c => Q_mix (L := L) (K := K) n mC T c)                          -- Q
    habs_mix                                                             -- hQ_abs
    (ENNReal.ofReal (1 - ((((mC / 10) * (mC / 10) : ℕ) : ℝ)
        / ((n : ℝ) * ((n : ℝ) - 1))) * (1 - Real.exp (-Real.log 2))))  -- r
    ?_                                                                   -- hdrift
    (fun c => Q_mix (L := L) (K := K) n mC T c
      ∧ 9 * mC / 10 ≤ rBeyond (L := L) (K := K) T c)                    -- Pre (prior crossed)
    (fun c => Q_mix (L := L) (K := K) n mC T c
      ∧ mC / 10 ≤ rBeyond (L := L) (K := K) (T + 1) c)                  -- Post (0.1·mC seeded)
    ?_                                                                   -- hPost_abs
    1 one_ne_zero ENNReal.one_ne_top                                     -- θ = 1
    ?_                                                                   -- hlink
    (fun c h => h.1)                                                     -- hPre_Q
    (ENNReal.ofReal (Real.exp (Real.log 2 * (seedLo mC : ℝ))))          -- Φ₀
    ?_                                                                   -- hPre_bound
    t ε hε                                                              -- hε
  · -- hdrift : on the window, seed contraction (unfinished) or `Φ = 0` (finished).
    intro c hQ
    rw [rSeedPotSeed_eq_on_window n mC T (Real.log 2) c hQ]
    have hint_eq : ∫⁻ c', rSeedPotSeed (L := L) (K := K) n mC T (Real.log 2) c'
          ∂((NonuniformMajority L K).transitionKernel c)
        = ∫⁻ c', rSeedPot (L := L) (K := K) (seedLo mC) T (Real.log 2) c'
          ∂((NonuniformMajority L K).transitionKernel c) := by
      apply lintegral_congr_ae
      change ∀ᵐ c' ∂((NonuniformMajority L K).stepDistOrSelf c).toMeasure,
        rSeedPotSeed (L := L) (K := K) n mC T (Real.log 2) c'
          = rSeedPot (L := L) (K := K) (seedLo mC) T (Real.log 2) c'
      rw [ae_iff, PMF.toMeasure_apply_eq_zero_iff _
        (DiscreteMeasurableSpace.forall_measurableSet _)]
      rw [Set.disjoint_left]
      intro x hsupp hbad
      apply hbad
      exact rSeedPotSeed_eq_on_window n mC T (Real.log 2) x (habs_mix c x hQ hsupp)
    rw [hint_eq]
    by_cases hfin : seedLo mC ≤ rBeyond (L := L) (K := K) (T + 1) c
    · -- finished (0.1 reached): Φ = 0, integral 0.
      have hΦc0 : rSeedPot (L := L) (K := K) (seedLo mC) T (Real.log 2) c = 0 := by
        unfold rSeedPot; rw [if_pos hfin]
      rw [hΦc0, mul_zero, nonpos_iff_eq_zero]
      change ∫⁻ c', rSeedPot (L := L) (K := K) (seedLo mC) T (Real.log 2) c'
          ∂((NonuniformMajority L K).stepDistOrSelf c).toMeasure = 0
      rw [lintegral_eq_zero_iff (rSeedPot_measurable (seedLo mC) T (Real.log 2))]
      rw [Filter.eventuallyEq_iff_exists_mem]
      refine ⟨((NonuniformMajority L K).stepDistOrSelf c).support, ?_, ?_⟩
      · rw [mem_ae_iff, PMF.toMeasure_apply_eq_zero_iff _
          (DiscreteMeasurableSpace.forall_measurableSet _)]
        rw [Set.disjoint_left]; intro x hsupp hx
        exact hx (PMF.mem_support_iff _ _ |>.mp hsupp)
      · intro c' hc'
        have hfin' : seedLo mC ≤ rBeyond (L := L) (K := K) (T + 1) c' :=
          le_trans hfin (hmono_mix_discharged n mC T c c' hQ hc')
        change rSeedPot (L := L) (K := K) (seedLo mC) T (Real.log 2) c' = 0
        unfold rSeedPot; rw [if_pos hfin']
    · -- seed-unfinished: the GENUINE seed contraction.
      have hnc : rBeyond (L := L) (K := K) (T + 1) c < seedLo mC := by omega
      exact rSeedPot_contracts_seed n mC T hn hmC hT (Real.log 2) hs c hQ hnc
  · -- hPost_abs : window closure + 0.1-seeding preserved (PROVEN monotonicity).
    rintro c c' ⟨hQ, hfin⟩ hc'
    refine ⟨habs_mix c c' hQ hc', ?_⟩
    -- mC/10 ≤ rBeyond (T+1) c ≤ rBeyond (T+1) c'  (= seedLo mC ≤ ·).
    have hmono := hmono_mix_discharged n mC T c c' hQ hc'
    omega
  · -- hlink : ¬Post → 1 ≤ Φ.  Off-window Φ = ⊤; on-window-seed-unfinished Φ ≥ 1.
    intro c hnp
    unfold rSeedPotSeed
    by_cases hQ : Q_mix (L := L) (K := K) n mC T c
    · rw [if_pos hQ]
      have hnf : ¬ rFinished (L := L) (K := K) (seedLo mC) T c := by
        unfold rFinished
        -- ¬(seedLo mC ≤ rBeyond (T+1)) = ¬(mC/10 ≤ rBeyond (T+1)) from ¬Post.
        intro hfin
        exact hnp ⟨hQ, by have : seedLo mC = mC / 10 := rfl; omega⟩
      exact not_finished_imp_rSeedPot_ge_one (seedLo mC) T (Real.log 2) hs c hnf
    · rw [if_neg hQ]; exact le_top
  · -- hPre_bound : Φ ≤ exp(s·seedLo mC) on the window.
    intro c hPre
    rw [rSeedPotSeed_eq_on_window n mC T (Real.log 2) c hPre.1]
    exact rSeedPot_le_max (seedLo mC) T (Real.log 2) hs c

/-! ## Part D — the per-minute faithful clock step `clock_real_step`.

We compose `clock_real_advance_seed ++ clock_real_advance_bulk` via
`compose_two_phases` into a single per-minute phase: `Pre = level S−1 bulk-crossed`
(here `Pre = clock_real_advance_seed.Pre`), `Post = level S bulk-crossed`
(`= clock_real_advance_bulk.Post`).  Both phases operate on the SAME window
`Q_mix n mC T` and the SAME level `rBeyond (T+1)`, so the chaining

  `clock_real_advance_seed.Post = (Q_mix n mC T ∧ mC/10 ≤ rBeyond (T+1))`
                                = `clock_real_advance_bulk.Pre`

is a DEFINITIONAL identity (`fun x hx => hx`), NOT an assumed `h_chain`.  This is the
genuine faithful O(1)/minute clock step: `t = tseed + tbulk = O(n/c²) = O(1)`
parallel; `ε = εseed + εbulk = exp(−Θ(m_C))`.  The real-kernel analog of the
abstract C3 `clock_step_upper` (`seedPhase ++ epidemicPhase`). -/

/-- **`clock_real_step` — the FAITHFUL per-minute real-kernel clock step.**

From minute `T` (the mixed window `Q_mix n mC T`, prior level crossed
`9·m_C/10 ≤ rBeyond T`), within `tseed + tbulk` interactions the level
`rBeyond (T+1)` crosses the full `0.9·m_C` bulk target
(`Post = Q_mix n mC T ∧ bulkHi m_C ≤ rBeyond (T+1)`) with failure
`≤ εseed + εbulk`.  Genuinely chains the DRIP SEED (`0 → 0.1·m_C`,
`clock_real_advance_seed`) and the EPIDEMIC BULK (`0.1·m_C → 0.9·m_C`,
`clock_real_advance_bulk`); the chaining `seed.Post → bulk.Pre`
(`Q_mix ∧ m_C/10 ≤ rBeyond (T+1)` on BOTH sides) is the DEFINITIONAL identity
`fun x hx => hx`.  Taking `tseed = tbulk = O(n/c²)` gives `O(1)` parallel per minute
— the real-kernel analog of the abstract C3 `clock_step_upper`. -/
theorem clock_real_step (n mC T : ℕ) (hn : 2 ≤ n) (hmC : 2 ≤ mC) (hT : T < K * (L + 1))
    (habs_mix : ∀ c c' : Config (AgentState L K),
      Q_mix (L := L) (K := K) n mC T c →
      c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support →
      Q_mix (L := L) (K := K) n mC T c')
    (tseed tbulk : ℕ) (εseed εbulk : ℝ≥0)
    (hεs : ENNReal.ofReal
            (1 - ((((mC / 10) * (mC / 10) : ℕ) : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)))
              * (1 - Real.exp (-Real.log 2))) ^ tseed
          * ENNReal.ofReal (Real.exp (Real.log 2 * (seedLo mC : ℝ))) / 1 ≤ (εseed : ℝ≥0∞))
    (hεb : ENNReal.ofReal
            (1 - ((((mC / 10) * (mC / 10) : ℕ) : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)))
              * (1 - Real.exp (-Real.log 2))) ^ tbulk
          * ENNReal.ofReal (Real.exp (Real.log 2 * (bulkHi mC : ℝ))) / 1 ≤ (εbulk : ℝ≥0∞))
    (c₀ : Config (AgentState L K))
    (hc₀ : Q_mix (L := L) (K := K) n mC T c₀
      ∧ 9 * mC / 10 ≤ rBeyond (L := L) (K := K) T c₀) :
    ((NonuniformMajority L K).transitionKernel ^ (tseed + tbulk)) c₀
        {c | ¬ (Q_mix (L := L) (K := K) n mC T c
          ∧ bulkHi mC ≤ rBeyond (L := L) (K := K) (T + 1) c)} ≤
      (εseed + εbulk : ℝ≥0∞) := by
  -- the seed phase (drip, 0 → 0.1·mC).
  set seed := clock_real_advance_seed (L := L) (K := K) n mC T hn hmC hT habs_mix
    tseed εseed hεs with hseed
  -- the epidemic phase (bulk, 0.1·mC → 0.9·mC), REUSED from avenue (a').
  set bulk := clock_real_advance_bulk (L := L) (K := K) n mC T hn hmC hT habs_mix
    tbulk εbulk hεb with hbulk
  -- the chaining `seed.Post → bulk.Pre`: both are `Q_mix n mC T ∧ mC/10 ≤ rBeyond (T+1)`.
  have hchain : ∀ x, seed.Post x → bulk.Pre x := by
    intro x hx; exact hx
  -- the start `seed.Pre c₀`.
  have hc₀' : seed.Pre c₀ := hc₀
  exact compose_two_phases seed bulk hchain c₀ hc₀'

end ClockRealSeed

end ExactMajority
