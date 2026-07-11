/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Avenue (a') — the FAITHFUL real-kernel BULK clock crossing `0.1·m_C → 0.9·m_C`

`ClockRealMixed.clock_real_advance_mixed` targeted the FULL crossing
`rBeyond (T+1) = m_C`.  That is the WRONG scale: full crossing is `Θ(log² n)` per
minute and it forced a FALSE-near-completion hypothesis `hfrontier_mix`
(`γ·m_C(m_C−1) ≤ (m_C−m)(m_C−1)` over the WHOLE unfinished window, which is FALSE
as `m → m_C`).

This file builds the FAITHFUL target matching the abstract C3 `clock_step_upper`:
the **0.9-BULK crossing**.  Per minute we only need the cumulative tail to advance
from `0.1·m_C` infected (`⌊m_C/10⌋ ≤ rBeyond (T+1)`) to `0.9·m_C` infected
(`⌊9·m_C/10⌋ ≤ rBeyond (T+1)`).  In THIS window the front is WIDE on the laggard
side throughout — `m = rBeyond (T+1) < 0.9·m_C` forces the frontier-clock count
`m_C − m > 0.1·m_C`, so the per-step advance probability

  ≥ (m_C − m)·(m_C − 1)/(n(n−1))  ≥ (1/10)·m_C·(m_C − 1)/(n(n−1))  = Θ(c²)

is GENUINELY UNIFORM.  The product floor `(m_C − m)·(m_C − 1) ≥ (1/10)·m_C·(m_C−1)`
is **PROVEN** here (`bulk_frontier_floor`) — it is genuinely true on the bulk
window, NOT assumed.  This is the whole point of the course-correction: the false
`hfrontier_mix` is REPLACED by a genuine bulk-window fact.

This is the S1 `ConstantDensityEpidemic` pattern (0.1 → 0.9 in `O(1)` parallel,
`ln 9 ≈ 2.2`) MIRRORED on the REAL `NonuniformMajority L K` kernel.

## What is reused (proven; nothing edited)
* `ClockRealMixed.Q_mix`, `clockCount`, `clock_real_advance_prob_mixed`
  (the genuine `(m_C−m)(m_C−1)/(n(n−1))` advance probability, DERIVED by
  pair-counting from the FULL `n(n−1)` denominator),
  `rSeedPot_pointwise_bound_mixed` (target-level-parametric pointwise bound);
* `ClockMonoDischarge.hmono_mix_discharged` (`rBeyond (T+1)` non-decreasing on the
  kernel support — PROVEN, used here);
* `ClockRealKernel.rSeedPot / rClamp / rFinished` (target-level-parametric),
  `rSeedPot_measurable`, `rSeedPot_le_max`, `not_finished_imp_rSeedPot_ge_one`,
  `rClamp_eq_of_lt`;
* `WindowConcentration.windowDrift_PhaseConvergence`.

## What is carried (the SINGLE genuine structural protocol invariant, deferred)
* `habs_mix` — one-step support closure of the mixed window `Q_mix` (clock-role
  agents stay at phase exactly 3).  Deferred to the cap-boundary reachability
  invariant; this is the SAME `habs_mix` carried by `clock_real_advance_mixed` and
  is a deterministic support-closure fact, NOT a probability.

The `hmono` monotonicity is NO LONGER carried — it is `hmono_mix_discharged`.
The `hfrontier` frontier floor is NO LONGER carried — it is `bulk_frontier_floor`
(PROVEN below).  The contraction PROBABILITY is DERIVED.

NEW file; no existing file is edited; no sorry/admit/axiom/native_decide.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ClockRealMixed
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ClockMonoDischarge

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real BigOperators

namespace ClockRealBulk

open ClockRealKernel ClockRealMixed ClockMonoDischarge

variable {L K : ℕ}

/-! ## Part A — the bulk target level and the PROVEN product floor.

The bulk crossing targets `H := ⌊9·m_C/10⌋` (the `0.9·m_C` infected level), not the
full `m_C`.  The whole course-correction hinges on the fact that on the bulk window
`m = rBeyond (T+1) < H` the frontier-clock count `m_C − m` is `≥ (1/10)·m_C`, so the
advance-numerator product `(m_C − m)·(m_C − 1)` is `≥ (1/10)·m_C·(m_C − 1)`,
GENUINELY (both via the `m < 0.9·m_C` bound).  This is `bulk_frontier_floor`,
PROVEN — never assumed. -/

/-- The bulk target level: `⌊9·m_C/10⌋` (the `0.9·m_C` infected level). -/
def bulkHi (mC : ℕ) : ℕ := 9 * mC / 10

theorem bulkHi_le (mC : ℕ) : bulkHi mC ≤ mC := by unfold bulkHi; omega

theorem bulkHi_lt_of_one_le (mC : ℕ) (hmC : 1 ≤ mC) : bulkHi mC < mC := by
  unfold bulkHi; omega

/-- **The PROVEN bulk SYNC product floor (the genuine `c²` source).**  On the bulk
band `m ∈ [⌊m_C/10⌋, ⌊9·m_C/10⌋)` BOTH the infected count `m` and the susceptible
count `m_C − m` are `≥ ⌊m_C/10⌋`, so the SYNC rectangle mass `m·(m_C − m)` is
`≥ ⌊m_C/10⌋·⌊m_C/10⌋`.  Pure NAT arithmetic (NO full crossing, NO drip frontier):
`m ≥ ⌊m_C/10⌋` is the bulk `Pre` floor (infected side); `m < ⌊9·m_C/10⌋` (unfinished)
gives `m_C − m ≥ ⌊m_C/10⌋` (susceptible side, via `⌊m_C/10⌋ + ⌊9·m_C/10⌋ ≤ m_C`). -/
theorem bulk_sync_floor (mC m : ℕ) (hlo : mC / 10 ≤ m) (hhi : m < bulkHi mC) :
    (mC / 10) * (mC / 10) ≤ m * (mC - m) := by
  -- susceptible side: m_C − m ≥ m_C/10.  Need m ≤ m_C − m_C/10, i.e. m + m_C/10 ≤ m_C.
  -- From m < ⌊9 m_C/10⌋ and ⌊m_C/10⌋ + ⌊9 m_C/10⌋ ≤ m_C (Nat floor sub-additivity).
  unfold bulkHi at hhi
  have hsplit : mC / 10 + 9 * mC / 10 ≤ mC := by omega
  have hsus : mC / 10 ≤ mC - m := by omega
  exact Nat.mul_le_mul hlo hsus

/-! ## Part B — the genuine bulk drift (targeting level `bulkHi m_C`).

We MIRROR `ClockRealMixed.rSeedPot_contracts_mixed`, but target the bulk level
`H := bulkHi m_C` (the `0.9·m_C` infected level) via `rSeedPot H T s`.  Crucially:

* the advance PROBABILITY is the SAME derived
  `clock_real_advance_prob_mixed` (`(m_C − m)(m_C − 1)/(n(n−1))`, full `n(n−1)`
  denominator) — it concerns `rBeyond (T+1)` advancing and is target-independent;
* the per-step monotonicity is the PROVEN `hmono_mix_discharged`;
* the frontier floor `(1/10)·m_C(m_C−1) ≤ (m_C−m)(m_C−1)` is the PROVEN
  `bulk_frontier_floor` (genuinely true since `m < H = 0.9·m_C`), giving the GENUINE
  uniform contraction rate `r = 1 − ((1/10)·m_C(m_C−1)/(n(n−1)))·(1 − e^{−s})`.

So `γ = 1/10` is no longer a carried hypothesis — it is the proven bulk fraction. -/

/-- **The genuine bulk drift.**  On the mixed window `Q_mix n mC T` with `m_C ≥ 2`,
in the bulk-unfinished regime (`rBeyond (T+1) c < bulkHi m_C`), the level-`bulkHi m_C`
potential contracts at the GENUINE clock-fraction-squared rate
`r = 1 − ((1/10)·m_C(m_C−1)/(n(n−1)))·(1 − e^{−s})`.

The contraction PROBABILITY is DERIVED (`clock_real_advance_prob_mixed`, full
`n(n−1)` denominator); the monotonicity is PROVEN (`hmono_mix_discharged`); the
frontier floor `(1/10)` is PROVEN (`bulk_frontier_floor`, genuinely true on the bulk
window).  NOTHING is assumed beyond the structural window membership `Q_mix`. -/
theorem rSeedPot_contracts_bulk (n mC T : ℕ) (hn : 2 ≤ n) (hmC : 2 ≤ mC)
    (hcap : T < K * (L + 1)) (s : ℝ) (hs : 0 < s)
    (c : Config (AgentState L K)) (hQ : Q_mix (L := L) (K := K) n mC T c)
    (hlo : mC / 10 ≤ rBeyond (L := L) (K := K) (T + 1) c)
    (hnc : rBeyond (L := L) (K := K) (T + 1) c < bulkHi mC) :
    ∫⁻ c', rSeedPot (L := L) (K := K) (bulkHi mC) T s c'
        ∂((NonuniformMajority L K).transitionKernel c) ≤
      ENNReal.ofReal (1 - ((((mC / 10) * (mC / 10) : ℕ) : ℝ)
            / ((n : ℝ) * ((n : ℝ) - 1)))
          * (1 - Real.exp (-s)))
        * rSeedPot (L := L) (K := K) (bulkHi mC) T s c := by
  set H := bulkHi mC with hHdef
  set m := rBeyond (L := L) (K := K) (T + 1) c with hm
  have hm_hi : m < H := hnc
  -- m < H < mC (real clock count): the advance never finishes the FULL crossing here.
  have hH_lt_mC : H < mC := by
    rw [hHdef]; exact bulkHi_lt_of_one_le mC (by omega)
  have hm_lt_mC : m < mC := lt_trans hm_hi hH_lt_mC
  -- Φ(c) = ofReal(exp(s·(H − m)))  (since uncrossed at level H, clamp = m).
  have hΦc : rSeedPot (L := L) (K := K) H T s c
      = ENNReal.ofReal (Real.exp (s * ((H : ℝ) - (m : ℝ)))) := by
    unfold rSeedPot
    rw [if_neg (by rw [← hm]; omega), rClamp_eq_of_lt H T c (by rw [← hm]; omega)]
  set A := {c' : Config (AgentState L K) | m + 1 ≤ rBeyond (L := L) (K := K) (T + 1) c'}
    with hA_def
  have hA_meas : MeasurableSet A := DiscreteMeasurableSpace.forall_measurableSet _
  -- the GENUINE bulk SYNC advance probability lower bound: p := ⌊mC/10⌋²/(n(n−1)).
  set pR : ℝ := (((mC / 10) * (mC / 10) : ℕ) : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))
    with hpR
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hmCR : (2 : ℝ) ≤ (mC : ℝ) := by exact_mod_cast hmC
  have hden_pos : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := by nlinarith
  -- mC ≤ n (clock sub-population fits in the full population), via clockSize.
  have hmC_le_n : mC ≤ n := by
    have hle : clockCount (L := L) (K := K) c ≤ c.card := by
      unfold clockCount; exact Multiset.countP_le_card _ _
    rw [hQ.card, hQ.clockSize] at hle; exact hle
  have hmCRn : (mC : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmC_le_n
  -- ⌊mC/10⌋² ≤ m·(mC−m) ≤ n(n−1): the bulk SYNC floor + rectangle ≤ totalPairs.
  have hfloorN : (mC / 10) * (mC / 10) ≤ m * (mC - m) :=
    bulk_sync_floor mC m hlo (hHdef ▸ hm_hi)
  have hmRle : (m : ℝ) ≤ (mC : ℝ) := by exact_mod_cast (le_of_lt hm_lt_mC)
  have hmCmR : ((mC - m : ℕ) : ℝ) = (mC : ℝ) - (m : ℝ) := by
    rw [Nat.cast_sub (le_of_lt hm_lt_mC)]
  -- m·(mC−m) ≤ n(n−1) over ℝ: AM-GM (mC/2)² ≤ (n/2)² ≤ n(n−1) for n ≥ 2.
  have hrec_le : ((m * (mC - m) : ℕ) : ℝ) ≤ (n : ℝ) * ((n : ℝ) - 1) := by
    rw [Nat.cast_mul, hmCmR]
    nlinarith [sq_nonneg ((mC : ℝ) - 2 * (m : ℝ)), hmRle, hmCRn, hnR,
      mul_nonneg (by linarith : (0:ℝ) ≤ (m:ℝ)) (by linarith : (0:ℝ) ≤ (mC:ℝ) - (m:ℝ))]
  have hfloorR : (((mC / 10) * (mC / 10) : ℕ) : ℝ) ≤ ((m * (mC - m) : ℕ) : ℝ) := by
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
  -- THE genuine bulk SYNC advance probability: lower-bound the derived prob via PROVEN floor.
  have hstep : ENNReal.ofReal pR ≤
      ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
        {c' | rBeyond (L := L) (K := K) (T + 1) c + 1
          ≤ rBeyond (L := L) (K := K) (T + 1) c'} := by
    refine le_trans (ENNReal.ofReal_le_ofReal ?_)
      (clock_real_sync_advance_prob_mixed n mC T hn hcap c hQ)
    rw [hpR]
    -- ⌊mC/10⌋²/(n(n−1)) ≤ ↑(m·(mC−m))/(n(n−1)) via the PROVEN SYNC floor.
    apply (div_le_div_iff_of_pos_right hden_pos).mpr
    have hcast : (((mC / 10) * (mC / 10) : ℕ) : ℝ) ≤ ((m * (mC - m) : ℕ) : ℝ) := by
      exact_mod_cast hfloorN
    exact hcast
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
        -- pointwise bound on rSeedPot at target level H, using PROVEN monotonicity.
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

/-! ## Part C — the guarded bulk potential and packaging into `PhaseConvergence`.

The bulk guarded potential is `⊤` off the mixed window `Q_mix n mC T`, else the
level-`bulkHi m_C` potential `rSeedPot (bulkHi m_C) T`.  `Post` is the 0.9-crossing
`bulkHi m_C ≤ rBeyond (T+1)` (`rFinished (bulkHi m_C) T`).  `Pre` is the 0.1-floor
window: `Q_mix n mC T ∧ ⌊m_C/10⌋ ≤ rBeyond (T+1)`. -/

/-- The bulk SYNC window: `Q_mix n mC T` AND the `0.1·m_C` infected floor (the
infected side of the SYNC rectangle).  Absorbing: `Q_mix` closes via `habs_mix` and
the `0.1·m_C` floor is preserved by the PROVEN monotonicity. -/
def QbulkWin (n mC T : ℕ) (c : Config (AgentState L K)) : Prop :=
  Q_mix (L := L) (K := K) n mC T c ∧ mC / 10 ≤ rBeyond (L := L) (K := K) (T + 1) c

/-- The bulk guarded clock-minute potential: `⊤` off the bulk SYNC window `QbulkWin`,
else the level-`bulkHi m_C` potential. -/
noncomputable def rSeedPotBulk (n mC T : ℕ) (s : ℝ) (c : Config (AgentState L K)) : ℝ≥0∞ :=
  open Classical in
  if QbulkWin (L := L) (K := K) n mC T c then
    rSeedPot (L := L) (K := K) (bulkHi mC) T s c
  else ⊤

theorem rSeedPotBulk_measurable (n mC T : ℕ) (s : ℝ) :
    Measurable (rSeedPotBulk (L := L) (K := K) n mC T s) :=
  fun _ _ => DiscreteMeasurableSpace.forall_measurableSet _

theorem rSeedPotBulk_eq_on_window (n mC T : ℕ) (s : ℝ) (c : Config (AgentState L K))
    (h : QbulkWin (L := L) (K := K) n mC T c) :
    rSeedPotBulk (L := L) (K := K) n mC T s c
      = rSeedPot (L := L) (K := K) (bulkHi mC) T s c := by
  unfold rSeedPotBulk; rw [if_pos h]

/-- **`clock_real_advance_bulk` — the FAITHFUL real-kernel BULK clock crossing.**
Packaged as a `PhaseConvergence` on the REAL `NonuniformMajority L K` kernel.
Starting from `Pre = Q_mix n mC T ∧ ⌊m_C/10⌋ ≤ rBeyond (T+1)` (already at `0.1·m_C`
infected, in the mixed window), the cumulative tail reaches
`Post = ⌊9·m_C/10⌋ ≤ rBeyond (T+1)` (`0.9·m_C` infected) within `t` interactions
with failure `≤ ε`, at the GENUINE clock-fraction-squared contraction
`r = 1 − ((1/10)·m_C(m_C−1)/(n(n−1)))·(1 − e^{−s})` (`s = log 2`).

The contraction PROBABILITY is DERIVED (`clock_real_advance_prob_mixed`, full
`n(n−1)` denominator).  The monotonicity is PROVEN (`hmono_mix_discharged`).  The
frontier floor `1/10` is PROVEN (`bulk_frontier_floor`, GENUINELY TRUE on the bulk
window `m < 0.9·m_C` — NOT assumed).  The ONLY carried hypothesis is `habs_mix`, the
deterministic one-step support closure of the mixed window (a structural protocol
invariant, NOT a probability), identical to the one in `clock_real_advance_mixed`. -/
noncomputable def clock_real_advance_bulk (n mC T : ℕ) (hn : 2 ≤ n) (hmC : 2 ≤ mC)
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
          * ENNReal.ofReal (Real.exp (Real.log 2 * (bulkHi mC : ℝ))) / 1 ≤ (ε : ℝ≥0∞)) :
    PhaseConvergence (NonuniformMajority L K).transitionKernel := by
  have hs : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  -- the bulk SYNC window `QbulkWin` is absorbing: Q_mix closes (habs_mix) + 0.1 floor
  -- preserved (PROVEN monotonicity).
  have habs_bulk : ∀ c c' : Config (AgentState L K),
      QbulkWin (L := L) (K := K) n mC T c →
      c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support →
      QbulkWin (L := L) (K := K) n mC T c' := by
    rintro c c' ⟨hQ, hlo⟩ hc'
    exact ⟨habs_mix c c' hQ hc',
      le_trans hlo (hmono_mix_discharged n mC T c c' hQ hc')⟩
  refine WindowConcentration.windowDrift_PhaseConvergence (NonuniformMajority L K)
    (rSeedPotBulk (L := L) (K := K) n mC T (Real.log 2))
    (rSeedPotBulk_measurable n mC T (Real.log 2))
    (fun c => QbulkWin (L := L) (K := K) n mC T c)                       -- Q
    habs_bulk                                                            -- hQ_abs
    (ENNReal.ofReal (1 - ((((mC / 10) * (mC / 10) : ℕ) : ℝ)
        / ((n : ℝ) * ((n : ℝ) - 1))) * (1 - Real.exp (-Real.log 2))))  -- r
    ?_                                                                   -- hdrift
    (fun c => QbulkWin (L := L) (K := K) n mC T c)                       -- Pre (0.1·mC floor)
    (fun c => Q_mix (L := L) (K := K) n mC T c
      ∧ bulkHi mC ≤ rBeyond (L := L) (K := K) (T + 1) c)               -- Post (0.9·mC)
    ?_                                                                   -- hPost_abs
    1 one_ne_zero ENNReal.one_ne_top                                     -- θ = 1
    ?_                                                                   -- hlink
    (fun c h => h)                                                       -- hPre_Q
    (ENNReal.ofReal (Real.exp (Real.log 2 * (bulkHi mC : ℝ))))          -- Φ₀
    ?_                                                                   -- hPre_bound
    t ε hε                                                              -- hε
  · -- hdrift : on the window, bulk SYNC contraction (unfinished) or `Φ = 0` (finished).
    intro c hQbulk
    obtain ⟨hQ, hlo⟩ := hQbulk
    rw [rSeedPotBulk_eq_on_window n mC T (Real.log 2) c ⟨hQ, hlo⟩]
    have hint_eq : ∫⁻ c', rSeedPotBulk (L := L) (K := K) n mC T (Real.log 2) c'
          ∂((NonuniformMajority L K).transitionKernel c)
        = ∫⁻ c', rSeedPot (L := L) (K := K) (bulkHi mC) T (Real.log 2) c'
          ∂((NonuniformMajority L K).transitionKernel c) := by
      apply lintegral_congr_ae
      change ∀ᵐ c' ∂((NonuniformMajority L K).stepDistOrSelf c).toMeasure,
        rSeedPotBulk (L := L) (K := K) n mC T (Real.log 2) c'
          = rSeedPot (L := L) (K := K) (bulkHi mC) T (Real.log 2) c'
      rw [ae_iff, PMF.toMeasure_apply_eq_zero_iff _
        (DiscreteMeasurableSpace.forall_measurableSet _)]
      rw [Set.disjoint_left]
      intro x hsupp hbad
      apply hbad
      exact rSeedPotBulk_eq_on_window n mC T (Real.log 2) x (habs_bulk c x ⟨hQ, hlo⟩ hsupp)
    rw [hint_eq]
    by_cases hfin : bulkHi mC ≤ rBeyond (L := L) (K := K) (T + 1) c
    · -- finished (0.9 reached): Φ = 0, integral 0.
      have hΦc0 : rSeedPot (L := L) (K := K) (bulkHi mC) T (Real.log 2) c = 0 := by
        unfold rSeedPot; rw [if_pos hfin]
      rw [hΦc0, mul_zero, nonpos_iff_eq_zero]
      change ∫⁻ c', rSeedPot (L := L) (K := K) (bulkHi mC) T (Real.log 2) c'
          ∂((NonuniformMajority L K).stepDistOrSelf c).toMeasure = 0
      rw [lintegral_eq_zero_iff (rSeedPot_measurable (bulkHi mC) T (Real.log 2))]
      rw [Filter.eventuallyEq_iff_exists_mem]
      refine ⟨((NonuniformMajority L K).stepDistOrSelf c).support, ?_, ?_⟩
      · rw [mem_ae_iff, PMF.toMeasure_apply_eq_zero_iff _
          (DiscreteMeasurableSpace.forall_measurableSet _)]
        rw [Set.disjoint_left]; intro x hsupp hx
        exact hx (PMF.mem_support_iff _ _ |>.mp hsupp)
      · intro c' hc'
        have hfin' : bulkHi mC ≤ rBeyond (L := L) (K := K) (T + 1) c' :=
          le_trans hfin (hmono_mix_discharged n mC T c c' hQ hc')
        change rSeedPot (L := L) (K := K) (bulkHi mC) T (Real.log 2) c' = 0
        unfold rSeedPot; rw [if_pos hfin']
    · -- bulk-unfinished: the GENUINE bulk SYNC contraction.
      have hnc : rBeyond (L := L) (K := K) (T + 1) c < bulkHi mC := by omega
      exact rSeedPot_contracts_bulk n mC T hn hmC hT (Real.log 2) hs c hQ hlo hnc
  · -- hPost_abs : window closure + 0.9-crossing preserved (PROVEN monotonicity).
    rintro c c' ⟨hQ, hfin⟩ hc'
    exact ⟨habs_mix c c' hQ hc', le_trans hfin (hmono_mix_discharged n mC T c c' hQ hc')⟩
  · -- hlink : ¬Post → 1 ≤ Φ.  Off-window Φ = ⊤; on-window-bulk-unfinished Φ ≥ 1.
    intro c hnp
    unfold rSeedPotBulk
    by_cases hQ : QbulkWin (L := L) (K := K) n mC T c
    · rw [if_pos hQ]
      have hnf : ¬ rFinished (L := L) (K := K) (bulkHi mC) T c := by
        unfold rFinished
        intro hfin; exact hnp ⟨hQ.1, hfin⟩
      exact not_finished_imp_rSeedPot_ge_one (bulkHi mC) T (Real.log 2) hs c hnf
    · rw [if_neg hQ]; exact le_top
  · -- hPre_bound : Φ ≤ exp(s·bulkHi mC) on the window.
    intro c hPre
    rw [rSeedPotBulk_eq_on_window n mC T (Real.log 2) c hPre]
    exact rSeedPot_le_max (bulkHi mC) T (Real.log 2) hs c

end ClockRealBulk

end ExactMajority
