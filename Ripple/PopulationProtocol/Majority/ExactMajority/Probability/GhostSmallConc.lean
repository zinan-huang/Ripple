/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# GhostSmallConc — the per-level GhostSmall concentration via a STOPPED exp-MGF supermartingale

This file builds the §6 GhostSmall bound (Doty et al. ROUND 5/6 doctrine, `DOCTRINE_THM69_CA.md`):
the clock-filtered early-drip ghost count `D_i = clockTaintedCount T mc` stays below the threshold
`R = η·C₀` over a horizon `H` whp, via a **predictable-log-MGF exponential supermartingale on a
STOPPED marked kernel**, reusing the verified machinery rather than rebuilding it.

## Why a stopped kernel and an EXPONENTIAL potential

`D_i` has POSITIVE drift (`E[ΔD_i] ≲ 1_{X_i<ε}·p·X_i² + 2κ·D_i/n`), so it is NOT a supermartingale and
`AzumaKernel.expSupermartingale_drift` does NOT apply to `D_i` directly (and the weak Azuma `t·c²`
exponent is mean-insensitive — useless for a `Θ(n^{0.15})` threshold).  The correct object is the
**exponential potential** `Ψ_i λ mc = exp(λ · D_i mc)` together with a predictable per-step compensator
`r = exp(λ_step)`.  Over one step the rare `+1`-increment MGF contracts:

  `∫ exp(λ·D_i) d(markedK mc) ≤ (1 + q·(e^λ − 1)) · exp(λ·D_i mc) ≤ exp(q(e^λ−1)) · exp(λ·D_i mc)`,

where `q` is the per-step rise rate from `ClockTaintMixed.clockTainted_rise_prob_le_of_subset`
(`P[D_i rises] ≤ (count@T/n)² + 2·taintedCount/n`).  This is EXACTLY `ClimbTail.mgf_one_step` (the
verified generic rare-`+1` MGF contraction), the same engine used for `EarlyDripMarked.taintedPot_drift`.

## The STOPPED kernel (mirrors `Lemma610StoppedAzuma.stoppedK`)

`KghostStar i := Kernel.piecewise {GhostActive i} (markedK T θn) Kernel.id` runs the real marked kernel
on the STATE-LOCAL active gate and freezes (self-loops) off it.  `GhostActive` contains ONLY state-local
predicates (`2 ≤ card`, `ClockP3 (erase)`, the rate gate `count@T ≤ θn`, and the carried auxiliary
unbiased-phase-3 facts `Aux` — NO future/window event, avoiding the vacuity trap of Hole 2).  Then the
exp-supermartingale drift holds UNCONDITIONALLY for `KghostStar` (active: the genuine `mgf_one_step`
contraction; inactive: `∫Ψ dδ_mc = Ψ mc`), exactly mirroring `Lemma610StoppedAzuma.drift_stopped`.

## What is proven (axiom-clean, no sorry/admit/axiom/native_decide)

* `GhostPot`, `GhostActive`, `ghostActiveSet`, `KghostStar` — the potential, state-local gate, stopped kernel.
* `ghost_exp_drift` — the UNCONDITIONAL multiplicative exp-drift `∫⁻ Ψ d(KghostStar mc) ≤ r · Ψ mc`,
  `r = exp(q(e^λ−1))`, by the two-case (active/inactive) split.  CARRIES the per-step ingredients as
  SATISFIABLE hypotheses: the rise-subset obligation `hsub` (the genuine remaining content of
  `ClockTaintMixed`), the per-step `+1`-increment bound `hincr`, and the uniform rate cap `q`.  None is a
  false `∀c`: each is a per-step, state-local, refutation-checked bound (the increment is literally
  satisfiable — a single marked step touches one pair, so any `countP` statistic rises by ≤ 1).
* `ghostSmall_level_whp` — the per-level tail
  `(KghostStar^H) mc₀ {R ≤ D_i} ≤ exp(q(e^λ−1))^H · exp(λ·D_i mc₀) / exp(λ·R)`,
  by `geometric_drift_tail` applied to `Ψ`.  From the clean start (`D_i mc₀ = 0`) and the symbolic numeric
  bound `H·q(e^λ−1) ≤ (λ/2)·R`, this is `exp(−(λ/2)·R)` — at `λ = (log n)/100`, `R = η·C₀ = κn^{0.15}`,
  `q ≤ O(n^{−0.8})`, this is `exp(−Ω(n^{0.15} log n)) ≤ n^{−A}`.

Reference: `DOCTRINE_THM69_CA.md` ROUND 5 family2 (the ghost exp-MGF recipe), ROUND 6 (the
`EarlyDripMarked`/`ClockTaintMixed` reuse, Holes 2 & 3); Doty et al. (arXiv:2106.10201v2) Lemma 6.3/6.5.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ClockTaintMixed
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ClimbTail
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Supermartingale

namespace ExactMajority

namespace GhostSmallConc

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real BigOperators
open ClockRealKernel EarlyDripMarked ClockTaintMixed
open Classical

variable {L K : ℕ}

/-! ## Part 1 — the exponential potential and the state-local active gate. -/

/-- **The exponential ghost potential** `Ψ_i λ mc = exp(λ · clockTaintedCount T mc)`.  This is the
`taintedPot`-style MGF potential, specialized to the clock-filtered ghost count `D_i` and to a single
constant slope `λ` (the per-step compensator is carried as the multiplicative drift rate `r`, exactly
as in `AzumaKernel.expSupermartingale_drift`). -/
noncomputable def GhostPot (T : ℕ) (lam : ℝ) (mc : Config (MarkedAgent L K)) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (lam * (clockTaintedCount (L := L) (K := K) T mc : ℝ)))

theorem GhostPot_measurable (T : ℕ) (lam : ℝ) :
    Measurable (GhostPot (L := L) (K := K) T lam) := Measurable.of_discrete

/-- **The STATE-LOCAL active gate** (Hole-2 safe — NO future/window event).  A marked configuration is
ghost-active at level `T` when:
* it is non-degenerate (`2 ≤ card`), so the marked kernel actually samples a pair;
* the clock-role agents are pinned to phase 3 (`ClockP3` on the erasure) — the mixed window;
* the minute-`T` count is bounded by `θn` (`count@T ≤ θn`), the deterministic rate-controlling gate
  feeding the `(θn/n)²` immigration term;
* the carried auxiliary unbiased-phase-3 Main facts `Aux` hold (whatever the real prefix-FrontSync gate
  supplies for the clock-locality of the taint rise — abstracted as a state-local predicate).

EVERY conjunct is evaluated at the CURRENT state `mc`; none refers to a window/future event. -/
def GhostActive (T θn : ℕ) (Aux : Config (MarkedAgent L K) → Prop)
    (mc : Config (MarkedAgent L K)) : Prop :=
  2 ≤ mc.card ∧
  ClockFrontMixed.ClockP3 (L := L) (K := K) (eraseConfig (L := L) (K := K) mc) ∧
  Multiset.countP (fun m : MarkedAgent L K => m.1.minute.val = T) mc ≤ θn ∧
  Aux mc

/-- The active gate as a (measurable, discrete) set of marked configs. -/
def ghostActiveSet (T θn : ℕ) (Aux : Config (MarkedAgent L K) → Prop) :
    Set (Config (MarkedAgent L K)) :=
  {mc | GhostActive (L := L) (K := K) T θn Aux mc}

/-- **The stopped marked kernel `KghostStar`** (mirrors `Lemma610StoppedAzuma.stoppedK`): run the
marked kernel `markedK T θn` on the state-local active gate, freeze (self-loop) off it. -/
noncomputable def KghostStar (T θn : ℕ) (Aux : Config (MarkedAgent L K) → Prop) :
    Kernel (Config (MarkedAgent L K)) (Config (MarkedAgent L K)) :=
  Kernel.piecewise
    (DiscreteMeasurableSpace.forall_measurableSet (ghostActiveSet (L := L) (K := K) T θn Aux))
    (markedK (L := L) (K := K) T θn) Kernel.id

instance (T θn : ℕ) (Aux : Config (MarkedAgent L K) → Prop) :
    IsMarkovKernel (KghostStar (L := L) (K := K) T θn Aux) := by
  unfold KghostStar; infer_instance

/-! ## Part 2 — the UNCONDITIONAL exponential drift for `KghostStar`. -/

/-- **`ghost_exp_drift` — the UNCONDITIONAL multiplicative exp-supermartingale drift for
`KghostStar`.**  For every `lam ≥ 0` and rate cap `q ≥ 0`:

  `∫⁻ Ψ d(KghostStar mc) ≤ exp(q·(e^lam − 1)) · Ψ mc`.

By the two-case (active/inactive) split exactly mirroring `Lemma610StoppedAzuma.drift_stopped`:
* on the active gate: the genuine rare-`+1` MGF contraction `ClimbTail.mgf_one_step`, fed by the
  per-step `+1`-increment bound `hincr` and the clock-filtered rise rate
  `ClockTaintMixed.clockTainted_rise_prob_le_of_subset` (capped by `q` via `hqcap`);
* off the active gate: the self-loop gives `∫Ψ dδ_mc = Ψ mc ≤ exp(q(e^lam−1))·Ψ mc` since
  `1 ≤ exp(q(e^lam−1))`.

CARRIED (all SATISFIABLE, state-local, per-step — NO false `∀c`):
* `hsub` — the clock-filtered taint-rise subset (the genuine remaining content of `ClockTaintMixed`,
  whose blocker is documented there; it is the MIXED analogue of the PROVEN `tainted_rise_subset`);
* `hincr` — the per-step `+1`-increment bound for `clockTaintedCount` (literally true: a marked step
  touches one sampled pair, so any `countP` statistic rises by at most one — carried to avoid
  re-deriving the markedStep combinatorics for the clock-filtered predicate);
* `hqcap` — a uniform rate cap `(count@T/card)² + 2·taintedCount/card ≤ q` on the active gate. -/
theorem ghost_exp_drift (T θn : ℕ) (Aux : Config (MarkedAgent L K) → Prop)
    {lam : ℝ} (hlam : 0 ≤ lam) {q : ℝ} (hq0 : 0 ≤ q)
    (hsub : ClockTaintedRiseSubset (L := L) (K := K) T θn Aux)
    (hincr : ∀ mc, GhostActive (L := L) (K := K) T θn Aux mc →
      ∀ᵐ mc' ∂(markedK (L := L) (K := K) T θn mc),
        clockTaintedCount (L := L) (K := K) T mc'
          ≤ clockTaintedCount (L := L) (K := K) T mc + 1)
    (hqcap : ∀ mc, GhostActive (L := L) (K := K) T θn Aux mc →
      ((Multiset.countP (fun m : MarkedAgent L K => m.1.minute.val = T) mc : ℝ)
          / (mc.card : ℝ)) ^ 2
        + 2 * ((taintedCount (L := L) (K := K) mc : ℝ) / (mc.card : ℝ)) ≤ q) :
    ∀ mc, ∫⁻ mc', GhostPot (L := L) (K := K) T lam mc'
        ∂((KghostStar (L := L) (K := K) T θn Aux) mc)
      ≤ ENNReal.ofReal (Real.exp (q * (Real.exp lam - 1)))
        * GhostPot (L := L) (K := K) T lam mc := by
  intro mc
  classical
  set rr : ℝ≥0∞ := ENNReal.ofReal (Real.exp (q * (Real.exp lam - 1))) with hrr
  have hrr_one : (1 : ℝ≥0∞) ≤ rr := by
    rw [hrr]
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp]
    apply ENNReal.ofReal_le_ofReal
    apply Real.one_le_exp
    have h1 : (0 : ℝ) ≤ Real.exp lam - 1 := by
      have := Real.one_le_exp hlam; linarith
    positivity
  unfold KghostStar
  rw [Kernel.piecewise_apply]
  by_cases hx : mc ∈ ghostActiveSet (L := L) (K := K) T θn Aux
  · -- ACTIVE: the genuine rare-`+1` MGF contraction.
    rw [if_pos hx]
    have hact : GhostActive (L := L) (K := K) T θn Aux mc := hx
    obtain ⟨hcard2, hP3, hcntT, haux⟩ := hact
    haveI : IsProbabilityMeasure (markedK (L := L) (K := K) T θn mc) :=
      (inferInstance : IsMarkovKernel (markedK (L := L) (K := K) T θn)).isProbabilityMeasure mc
    set N := clockTaintedCount (L := L) (K := K) T mc with hN
    -- the per-step rise rate, capped by `q`.
    have hprob : markedK (L := L) (K := K) T θn mc
        {mc' | N < clockTaintedCount (L := L) (K := K) T mc'} ≤ ENNReal.ofReal q := by
      refine le_trans
        (clockTainted_rise_prob_le_of_subset (L := L) (K := K) T θn Aux hsub mc hcard2 hP3 haux) ?_
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      exact ENNReal.ofReal_le_ofReal (hqcap mc ⟨hcard2, hP3, hcntT, haux⟩)
    -- the generic MGF contraction at this state's rate (`ClimbTail.mgf_one_step`).
    have hmgf := ClimbTail.mgf_one_step (markedK (L := L) (K := K) T θn mc) lam hlam
      (clockTaintedCount (L := L) (K := K) T) N
      (hincr mc ⟨hcard2, hP3, hcntT, haux⟩) q hq0 hprob
    -- read off `GhostPot = ofReal(exp(λ·D))` and bound `1 + q(e^λ−1) ≤ exp(q(e^λ−1))`.
    have hmono : (1 : ℝ) + q * (Real.exp lam - 1)
        ≤ Real.exp (q * (Real.exp lam - 1)) := by
      have := Real.add_one_le_exp (q * (Real.exp lam - 1)); linarith
    calc ∫⁻ mc', GhostPot (L := L) (K := K) T lam mc'
            ∂(markedK (L := L) (K := K) T θn mc)
        = ∫⁻ mc', ENNReal.ofReal
            (Real.exp (lam * (clockTaintedCount (L := L) (K := K) T mc' : ℝ)))
            ∂(markedK (L := L) (K := K) T θn mc) := rfl
      _ ≤ ENNReal.ofReal ((1 + q * (Real.exp lam - 1)) * Real.exp (lam * (N : ℝ))) := hmgf
      _ ≤ rr * GhostPot (L := L) (K := K) T lam mc := by
          rw [hrr]
          unfold GhostPot
          rw [hN, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
          apply ENNReal.ofReal_le_ofReal
          exact mul_le_mul_of_nonneg_right hmono (Real.exp_pos _).le
  · -- INACTIVE: self-loop dirac.
    rw [if_neg hx, Kernel.id_apply, lintegral_dirac]
    calc GhostPot (L := L) (K := K) T lam mc
        = 1 * GhostPot (L := L) (K := K) T lam mc := (one_mul _).symm
      _ ≤ rr * GhostPot (L := L) (K := K) T lam mc := by
          gcongr

/-! ## Part 3 — the per-level GhostSmall tail. -/

/-- **`ghostSmall_level_whp` — the per-level GhostSmall concentration.**  Applying
`geometric_drift_tail` to the exponential potential `Ψ` (whose UNCONDITIONAL drift is
`ghost_exp_drift`) at the threshold `θ = exp(lam·R)`, the probability that the stopped marked chain's
ghost count reaches `R = η·C₀` over the horizon `H` is

  `(KghostStar^H) mc₀ {R ≤ clockTaintedCount T} ≤ exp(q(e^lam−1))^H · exp(lam·D_i mc₀) / exp(lam·R)`.

From a clean start (`D_i mc₀ = 0` — the synchronized entry's `no_ghost`) the numerator is
`exp(H·q(e^lam−1))`, and with the symbolic compensator bound `H·q(e^lam−1) ≤ (lam/2)·R` this is
`exp(−(lam/2)·R)`.  At `lam = (log n)/100`, `R = η·C₀ = κ·n^{0.15}`, `q ≤ O(n^{−0.8})` the bound is
`exp(−Ω(n^{0.15}·log n)) ≤ n^{−A}` — the GhostSmall whp bound. -/
theorem ghostSmall_level_whp (T θn : ℕ) (Aux : Config (MarkedAgent L K) → Prop)
    {lam : ℝ} (hlam : 0 ≤ lam) {q : ℝ} (hq0 : 0 ≤ q)
    (hsub : ClockTaintedRiseSubset (L := L) (K := K) T θn Aux)
    (hincr : ∀ mc, GhostActive (L := L) (K := K) T θn Aux mc →
      ∀ᵐ mc' ∂(markedK (L := L) (K := K) T θn mc),
        clockTaintedCount (L := L) (K := K) T mc'
          ≤ clockTaintedCount (L := L) (K := K) T mc + 1)
    (hqcap : ∀ mc, GhostActive (L := L) (K := K) T θn Aux mc →
      ((Multiset.countP (fun m : MarkedAgent L K => m.1.minute.val = T) mc : ℝ)
          / (mc.card : ℝ)) ^ 2
        + 2 * ((taintedCount (L := L) (K := K) mc : ℝ) / (mc.card : ℝ)) ≤ q)
    (H : ℕ) (mc₀ : Config (MarkedAgent L K)) (R : ℕ) :
    ((KghostStar (L := L) (K := K) T θn Aux) ^ H) mc₀
        {mc | R ≤ clockTaintedCount (L := L) (K := K) T mc} ≤
      ENNReal.ofReal (Real.exp (q * (Real.exp lam - 1))) ^ H
        * GhostPot (L := L) (K := K) T lam mc₀
        / ENNReal.ofReal (Real.exp (lam * (R : ℝ))) := by
  classical
  -- the super-level set `{R ≤ D}` is contained in `{θ ≤ Ψ}` with `θ = exp(lam·R)`.
  have hsub_set : {mc : Config (MarkedAgent L K) | R ≤ clockTaintedCount (L := L) (K := K) T mc}
      ⊆ {mc | ENNReal.ofReal (Real.exp (lam * (R : ℝ))) ≤ GhostPot (L := L) (K := K) T lam mc} := by
    intro mc hmc
    rw [Set.mem_setOf_eq] at hmc ⊢
    unfold GhostPot
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    have hcast : (R : ℝ) ≤ (clockTaintedCount (L := L) (K := K) T mc : ℝ) := by exact_mod_cast hmc
    exact mul_le_mul_of_nonneg_left hcast hlam
  refine le_trans (measure_mono hsub_set) ?_
  -- the geometric-drift tail for `Ψ`, drift supplied by `ghost_exp_drift`.
  have hθ0 : ENNReal.ofReal (Real.exp (lam * (R : ℝ))) ≠ 0 := by
    simp [ENNReal.ofReal_eq_zero, not_le, Real.exp_pos]
  have hθtop : ENNReal.ofReal (Real.exp (lam * (R : ℝ))) ≠ ∞ := ENNReal.ofReal_ne_top
  exact geometric_drift_tail (KghostStar (L := L) (K := K) T θn Aux)
    (GhostPot (L := L) (K := K) T lam) (GhostPot_measurable T lam)
    (ENNReal.ofReal (Real.exp (q * (Real.exp lam - 1))))
    (ghost_exp_drift (L := L) (K := K) T θn Aux hlam hq0 hsub hincr hqcap)
    H mc₀ (ENNReal.ofReal (Real.exp (lam * (R : ℝ)))) hθ0 hθtop

/-- **`ghostSmall_level_clean_start` — the GhostSmall tail from a clean (`D_i mc₀ = 0`) start.**  At the
synchronized entry the ghost count is zero (`no_ghost`), so `GhostPot mc₀ = 1` and the tail collapses to

  `(KghostStar^H) mc₀ {R ≤ clockTaintedCount T} ≤ exp(H·q(e^lam−1) − lam·R)`.

With the symbolic compensator bound `H·q·(e^lam−1) ≤ (lam/2)·R` (the numeric obligation, discharged at
`lam = (log n)/100`, `R = η·C₀`, `q ≤ O(n^{−0.8})`) this is `exp(−(lam/2)·R) = n^{−ω(1)}`. -/
theorem ghostSmall_level_clean_start (T θn : ℕ) (Aux : Config (MarkedAgent L K) → Prop)
    {lam : ℝ} (hlam : 0 ≤ lam) {q : ℝ} (hq0 : 0 ≤ q)
    (hsub : ClockTaintedRiseSubset (L := L) (K := K) T θn Aux)
    (hincr : ∀ mc, GhostActive (L := L) (K := K) T θn Aux mc →
      ∀ᵐ mc' ∂(markedK (L := L) (K := K) T θn mc),
        clockTaintedCount (L := L) (K := K) T mc'
          ≤ clockTaintedCount (L := L) (K := K) T mc + 1)
    (hqcap : ∀ mc, GhostActive (L := L) (K := K) T θn Aux mc →
      ((Multiset.countP (fun m : MarkedAgent L K => m.1.minute.val = T) mc : ℝ)
          / (mc.card : ℝ)) ^ 2
        + 2 * ((taintedCount (L := L) (K := K) mc : ℝ) / (mc.card : ℝ)) ≤ q)
    (H : ℕ) (mc₀ : Config (MarkedAgent L K)) (R : ℕ)
    (hclean : clockTaintedCount (L := L) (K := K) T mc₀ = 0) :
    ((KghostStar (L := L) (K := K) T θn Aux) ^ H) mc₀
        {mc | R ≤ clockTaintedCount (L := L) (K := K) T mc} ≤
      ENNReal.ofReal (Real.exp ((H : ℝ) * (q * (Real.exp lam - 1)) - lam * (R : ℝ))) := by
  refine le_trans
    (ghostSmall_level_whp (L := L) (K := K) T θn Aux hlam hq0 hsub hincr hqcap H mc₀ R) ?_
  -- collapse the numerator at the clean start and combine exponentials.
  have hpot0 : GhostPot (L := L) (K := K) T lam mc₀ = 1 := by
    unfold GhostPot
    rw [hclean]; simp
  rw [hpot0, mul_one]
  rw [← ENNReal.ofReal_pow (Real.exp_pos _).le, ← Real.exp_nat_mul,
    ENNReal.div_eq_inv_mul, ← ENNReal.ofReal_inv_of_pos (Real.exp_pos _),
    ← Real.exp_neg, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  apply le_of_eq
  ring

end GhostSmallConc

end ExactMajority
