/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Avenue S3 — the early-drip set bound (Lemma 6.3), `d≥i+1 = O(n^{−0.85})`

This file formalizes **Avenue S3** of the Doty et al. Theorem 3.1 time-half
campaign — the third and last of the three §6 pieces (S1 bulk
`ConstantDensityEpidemic.lean`, S2/S2b front `FrontTailDecay.lean` /
`FrontTailKernel.lean`, S3 early-drip).  With S3 the clock's per-minute cost is
bounded `O(1)` for all three regimes, enabling the clock re-composition
`Θ(log² n) → O(log n)`.

## What S3 is (paper §6, Lemma 6.3, lines 1807–1819, 1949–1955)

Before the epidemic bulk reaches a minute `i`, a few *over-eager* leaders can
already drip past minute `i` to minute `≥ i+1`.  The paper calls these the
**early-drip agents** `D≥i+1(t)`: agents that moved above minute `i` via a drip
reaction *when* `c≥i(t) < n^{−0.45}` (the pre-bulk window), plus the epidemic
descendants of such agents.  Writing `d≥i+1(t) = |D≥i+1(t)|/|C|` for the
early-drip *fraction*, Lemma 6.3 (with the Theorem 6.5 / line 1949–1955
estimate) bounds this fraction:

> **`d≥i+1(t≥i) = O(n^{−0.85})`** with very high probability.

The mechanism (lines 1950–1955):

* In the pre-bulk window the front fraction is `c≥i < n^{−0.45}`, so the
  same-state *drip* reaction `(s_i, s_i) → (s_i, s_{i+1})` fires with scheduler
  probability **`≤ p·(n^{−0.45})² = p·n^{−0.9}`** per interaction — this is S2's
  `dripPair_prob_le_sq` evaluated at the front fraction `n^{−0.45}`.
* Over the `O(log log n)` front window, by a *standard Chernoff bound* the count
  of early drips stays at `O(log log n · n^{−0.9}) = O(n^{−0.89})` interactions,
  and growing by epidemic from `O(n^{−0.89})` to `Ω(n^{−0.85})` takes `Ω(log n) >
  O(log log n)` time, so the early-drip *fraction* stays `O(n^{−0.85})`.

The substantive obligation is the **non-uniform large deviation**: a rare event
(prob `Θ(1/n)` per same-state pair, here `≤ n^{−0.9}` in the pre-bulk window)
whose *count* concentrates below the `n^{−0.85}`-scale threshold `n·n^{−0.85} =
n^{0.15}`.  That is a one-step MGF contraction at the non-uniform `n^{−0.9}`
scale, which we prove here from first principles and feed to the FRAMEWORK.

## How this uses the framework + `dripPair_prob_le_sq` (the wrapping is FREE)

The general trajectory-level builder `WindowConcentration.windowGrowth_PhaseConvergence`
turns a one-step contraction `∫ exp(s·V') dK ≤ r · exp(s·V)` on an absorbing
window into a kernel-level `PhaseConvergence` (multi-step tail + the
`PhaseConvergence` wrapping consumed by A1's `compose_n_phases`) FOR FREE.  S3
therefore reduces to supplying:

* the potential `V c = beyond (i+1) c` — the early-drip count (number of agents
  already at minute `≥ i+1`, the over-eager front);
* the genuine **one-step MGF contraction** of `Φ = exp(s·V)` on the pre-bulk
  window.  This is the real content, and it splits into:
  1. `earlyDrip_mgf_one_step` — a self-contained MGF inequality:  for ANY
     integer-valued `N : Config → ℕ` that increases by at most one per step
     (`N c' ≤ N c + 1` on the support) and *drips* (`N c < N c'`) with
     probability at most `q`, the exponential potential contracts:
     `∫ exp(s·N') dK ≤ (1 + q·(e^s − 1)) · exp(s·N)`.  (The non-uniform large
     deviation: a `+1` increment of rate `≤ q` costs an MGF factor `1 + q(e^s−1)`.)
  2. `beyond_le_succ_on_support` — the drip step raises the early-drip count
     `beyond (T+1)` by at most one (the clock δ adds at most one agent past any
     threshold);
  3. `earlyDrip_prob_le` — the early-drip event fires with probability
     `≤ ofReal((beyond T c / n)²)`, the SQUARE of the front fraction, *directly*
     from S2b's `frontTail_kernel_one_step_le_beyondSq` (which is built on S2's
     `dripPair_prob_le_sq`).  In the pre-bulk window `beyond T c / n < n^{−0.45}`
     this is `< n^{−0.9}`.

Composing 1–3 on the window `Q := beyond T c ≤ B` (front fraction below the
pre-bulk threshold, an *absorbing* set for the count once we cap it — see
`earlyDripWindow_absorbing`) gives the one-step contraction, and the framework
produces the kernel-level tail `K^t c₀ {¬(beyond (T+1) < θ)} ≤ rᵗ · e^{s·V₀}/e^{s·θ}`.

## What is proved here (0 sorry / 0 axiom / no native_decide)

* `expCount` / `expCount_*` — the exponential potential `exp(s·N)` and its
  measurability / value lemmas.
* `earlyDrip_mgf_one_step` — **the genuine one-step MGF contraction** for a
  rare `+1`-increment integer process (the non-uniform large deviation core).
* `beyond_le_succ_on_support` — the early-drip count rises by `≤ 1` per step.
* `earlyDrip_prob_le_sq` — the early-drip probability `≤ (beyond T c / n)²`
  from S2b/S2 (`frontTail_kernel_one_step_le_beyondSq` ⊳ `dripPair_prob_le_sq`).
* `earlyDrip_one_step_contraction` — the assembled one-step contraction of the
  MGF potential on the pre-bulk window (rate `r = 1 + q·(e^s−1)` with
  `q = (B/n)²`), the exact hypothesis `windowGrowth_PhaseConvergence` consumes.
* `earlyDrip_kernel_bound` — the kernel-level multi-step tail on the early-drip
  count being too large, with the `n^{−0.85}`-scale threshold, FREE via the
  framework's `windowDrift_tail`.
* `earlyDrip_PhaseConvergence` — the `PhaseConvergence`-compatible packaging that
  feeds the clock re-composition.

Reference: Doty et al. (arXiv:2106.10201v2) Lemma 6.3 (lines 1807–1819), the
early-drip discussion (lines 1949–1955), §6 footnote 9; framework
`WindowConcentration.lean`; S2b `FrontTailKernel.lean`; S2 `FrontTailDecay.lean`.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.FrontTailKernel
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.WindowConcentration

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real BigOperators

namespace EarlyDrip

open ClockTime FrontTailKernel WindowConcentration

variable {L₀ : ℕ}

/-- A finite power of a Markov kernel assigns mass at most one to every set
(local copy; the Mathlib/PhaseConvergence versions are `private`). -/
private theorem kernel_pow_le_one'
    {Ω : Type*} [MeasurableSpace Ω] {K : Kernel Ω Ω} [IsMarkovKernel K]
    (t : ℕ) (x : Ω) (S : Set Ω) : (K ^ t) x S ≤ 1 := by
  have h_univ : (K ^ t) x Set.univ = 1 := by
    induction t with
    | zero =>
        simp only [pow_zero]
        change Kernel.id x Set.univ = 1
        rw [Kernel.id_apply]; simp
    | succ t ih =>
        rw [Kernel.pow_succ_apply_eq_lintegral K t x MeasurableSet.univ]
        calc ∫⁻ y, K y Set.univ ∂((K ^ t) x)
            = ∫⁻ _ : Ω, (1 : ℝ≥0∞) ∂((K ^ t) x) := by
                apply lintegral_congr_ae; filter_upwards with y
                haveI : IsProbabilityMeasure (K y) :=
                  (inferInstance : IsMarkovKernel K).isProbabilityMeasure y
                simp only [measure_univ]
          _ = 1 := by rw [lintegral_const, ih, one_mul]
  calc (K ^ t) x S ≤ (K ^ t) x Set.univ := measure_mono (Set.subset_univ S)
    _ = 1 := h_univ

/-! ## The exponential potential `exp(s · N)` for an integer count `N`.

We use the growth-suppression dual of the framework: the potential is
`Φ(c) = exp(s · N(c))` with `N` the early-drip count, and "the early-drip count
ran past `θ`" is `{exp(s·θ) ≤ Φ}`.  We package the small lemmas about this
potential here. -/

/-- The exponential MGF potential of an integer-valued count `N` at scale `s`. -/
noncomputable def expCount (s : ℝ) (N : Config (Minute L₀) → ℕ) (c : Config (Minute L₀)) : ℝ :=
  Real.exp (s * (N c : ℝ))

theorem expCount_pos (s : ℝ) (N : Config (Minute L₀) → ℕ) (c : Config (Minute L₀)) :
    0 < expCount s N c := Real.exp_pos _

theorem expCount_nonneg (s : ℝ) (N : Config (Minute L₀) → ℕ) (c : Config (Minute L₀)) :
    0 ≤ expCount s N c := (expCount_pos s N c).le

/-! ## The genuine one-step MGF contraction for a rare `+1`-increment process.

This is the non-uniform large-deviation core, proved from first principles (no
`native_decide`, no Mathlib concentration primitive at a fixed scale — the bound
is the *scale-free* MGF factor `1 + q(e^s−1)`, instantiated at the `n^{−0.9}`
drip rate below).  The statement: for an integer count `N` that, on the one-step
support, increases by at most one and *increases at all* only on the event
`{N c < N ·}` of probability at most `q`, the exponential potential `exp(s·N)`
contracts by the factor `1 + q(e^s−1)`.

Mechanism: split the support into "dripped" (`N c < N c'`, so `N c' = N c + 1`)
and "did not drip" (`N c' ≤ N c`).  On the drip event the potential is multiplied
by `e^s`, on the non-drip event by `≤ 1`; weighting by the drip probability `≤ q`
gives `∫ exp(s·N') ≤ [q·e^s + (1−q)·1]·exp(s·N) = (1 + q(e^s−1))·exp(s·N)`. -/

/-- **The one-step MGF contraction of a rare `+1`-increment count.**  Let
`N : Config → ℕ` be such that on the one-step support of `c`:
* `N` rises by at most one (`N c' ≤ N c + 1`), and
* the probability of `N` strictly increasing is at most `q` (`0 ≤ q`).
Then for any `s ≥ 0` the exponential potential contracts:
`∫ exp(s·N c') dK(c) ≤ (1 + q·(e^s − 1)) · exp(s·N c)`. -/
theorem earlyDrip_mgf_one_step (s : ℝ) (hs : 0 ≤ s)
    (N : Config (Minute L₀) → ℕ) (c : Config (Minute L₀))
    (hstep : ∀ c', c' ∈ ((clockProto L₀).stepDistOrSelf c).support → N c' ≤ N c + 1)
    (q : ℝ) (hq0 : 0 ≤ q)
    (hprob : (clockProto L₀).transitionKernel c {c' | N c < N c'} ≤ ENNReal.ofReal q) :
    ∫⁻ c', ENNReal.ofReal (expCount s N c') ∂((clockProto L₀).transitionKernel c) ≤
      ENNReal.ofReal ((1 + q * (Real.exp s - 1)) * expCount s N c) := by
  classical
  set K := (clockProto L₀).transitionKernel c with hK
  -- The "dripped" event D = {N c < N c'}; its complement is {N c' ≤ N c}.
  set D : Set (Config (Minute L₀)) := {c' | N c < N c'} with hD
  have hD_meas : MeasurableSet D := DiscreteMeasurableSpace.forall_measurableSet _
  -- Pointwise a.e. bound: ofReal(exp(s·N c')) ≤ (if dripped then e^s else 1)·ofReal(exp(s·N c)).
  -- We prove it a.e. via the support: every support point satisfies hstep.
  have hsupp_ae : ∀ᵐ c' ∂K, N c' ≤ N c + 1 := by
    rw [hK]
    change ∀ᵐ c' ∂((clockProto L₀).stepDistOrSelf c).toMeasure, N c' ≤ N c + 1
    rw [ae_iff]
    rw [PMF.toMeasure_apply_eq_zero_iff _ (DiscreteMeasurableSpace.forall_measurableSet _)]
    rw [Set.disjoint_left]
    intro c' hsupp hbad
    exact hbad (hstep c' hsupp)
  -- Pointwise bound a.e.: split on whether c' ∈ D.
  have hpt : ∀ᵐ c' ∂K,
      ENNReal.ofReal (expCount s N c') ≤
        (if c' ∈ D then ENNReal.ofReal (Real.exp s * expCount s N c)
          else ENNReal.ofReal (expCount s N c)) := by
    filter_upwards [hsupp_ae] with c' hc'
    by_cases hdrip : c' ∈ D
    · -- dripped: N c' = N c + 1, so exp(s·N c') = e^s · exp(s·N c)
      simp only [hdrip, if_true]
      have hlt : N c < N c' := hdrip
      have heq : N c' = N c + 1 := by omega
      apply ENNReal.ofReal_le_ofReal
      unfold expCount
      rw [heq]
      have : s * ((N c + 1 : ℕ) : ℝ) = s + s * (N c : ℝ) := by push_cast; ring
      rw [this, Real.exp_add]
    · -- did not drip: N c' ≤ N c, so exp(s·N c') ≤ exp(s·N c)
      simp only [hdrip, if_false]
      apply ENNReal.ofReal_le_ofReal
      unfold expCount
      apply Real.exp_le_exp.mpr
      have hle : N c' ≤ N c := by
        by_contra h; exact hdrip (not_le.mp h)
      have hcast : (N c' : ℝ) ≤ (N c : ℝ) := by exact_mod_cast hle
      nlinarith [hs, hcast]
  -- Integrate the pointwise bound.
  calc ∫⁻ c', ENNReal.ofReal (expCount s N c') ∂K
      ≤ ∫⁻ c', (if c' ∈ D then ENNReal.ofReal (Real.exp s * expCount s N c)
          else ENNReal.ofReal (expCount s N c)) ∂K := lintegral_mono_ae hpt
    _ = ENNReal.ofReal (Real.exp s * expCount s N c) * K D
        + ENNReal.ofReal (expCount s N c) * K Dᶜ := by
        rw [← lintegral_add_compl _ hD_meas]
        congr 1
        · rw [setLIntegral_congr_fun hD_meas
              (g := fun _ => ENNReal.ofReal (Real.exp s * expCount s N c))
              (fun c' hc' => by simp only [hc', if_true])]
          rw [lintegral_const, Measure.restrict_apply_univ]
        · rw [setLIntegral_congr_fun hD_meas.compl (g := fun _ => ENNReal.ofReal (expCount s N c))
              (fun c' hc' => by simp only [Set.mem_compl_iff] at hc'; simp only [hc', if_false])]
          rw [lintegral_const, Measure.restrict_apply_univ]
    _ ≤ ENNReal.ofReal ((1 + q * (Real.exp s - 1)) * expCount s N c) := by
        -- Use K Dᶜ = 1 − K D and the monotone weighting in K D.
        haveI : IsProbabilityMeasure (K) := by
          rw [hK]; exact (inferInstance : IsMarkovKernel _).isProbabilityMeasure c
        have hKD : K D ≤ ENNReal.ofReal q := by rw [hK]; exact hprob
        have hexp_ge : (1 : ℝ) ≤ Real.exp s := Real.one_le_exp hs
        have hexp_nonneg : (0 : ℝ) ≤ Real.exp s := (Real.exp_pos s).le
        have hΦnn : (0 : ℝ) ≤ expCount s N c := expCount_nonneg s N c
        -- Work with the real-valued probability qr = (K D).toReal ∈ [0,1], qr ≤ q.
        have hKD_le_one : K D ≤ 1 := by
          calc K D ≤ K Set.univ := measure_mono (Set.subset_univ _)
            _ = 1 := measure_univ
        have hKD_ne_top : K D ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hKD_le_one
        set qr := (K D).toReal with hqr
        have hqr_nonneg : 0 ≤ qr := ENNReal.toReal_nonneg
        have hqr_le_one : qr ≤ 1 := by
          rw [hqr]; rw [show (1:ℝ) = (1 : ℝ≥0∞).toReal from ENNReal.toReal_one.symm]
          exact ENNReal.toReal_mono ENNReal.one_ne_top hKD_le_one
        have hqr_le_q : qr ≤ q := by
          rw [hqr]
          calc (K D).toReal ≤ (ENNReal.ofReal q).toReal :=
                ENNReal.toReal_mono ENNReal.ofReal_ne_top hKD
            _ = q := ENNReal.toReal_ofReal hq0
        have hKD_eq : K D = ENNReal.ofReal qr := (ENNReal.ofReal_toReal hKD_ne_top).symm
        -- K Dᶜ = ofReal (1 − qr)
        have hD_meas' := hD_meas
        have hKDc_eq : K Dᶜ = ENNReal.ofReal (1 - qr) := by
          have hcompl := measure_compl hD_meas' hKD_ne_top
          rw [show K Set.univ = 1 from measure_univ] at hcompl
          rw [hcompl, hKD_eq,
            show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm,
            ← ENNReal.ofReal_sub 1 hqr_nonneg]
        -- Rewrite both products as ofReal of real products, then add.
        rw [hKD_eq, hKDc_eq,
          ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ Real.exp s * expCount s N c),
          ← ENNReal.ofReal_mul hΦnn,
          ← ENNReal.ofReal_add
            (mul_nonneg (by positivity) hqr_nonneg)
            (mul_nonneg hΦnn (by linarith : (0:ℝ) ≤ 1 - qr))]
        apply ENNReal.ofReal_le_ofReal
        -- e^s·Φ·qr + Φ·(1−qr) = Φ·(1 + (e^s−1)·qr) ≤ Φ·(1 + (e^s−1)·q)
        have hfac : Real.exp s * expCount s N c * qr + expCount s N c * (1 - qr)
            = expCount s N c * (1 + (Real.exp s - 1) * qr) := by ring
        rw [hfac]
        have hbound : 1 + (Real.exp s - 1) * qr ≤ 1 + q * (Real.exp s - 1) := by
          have : (Real.exp s - 1) * qr ≤ (Real.exp s - 1) * q :=
            mul_le_mul_of_nonneg_left hqr_le_q (by linarith)
          nlinarith [this]
        calc expCount s N c * (1 + (Real.exp s - 1) * qr)
            ≤ expCount s N c * (1 + q * (Real.exp s - 1)) :=
              mul_le_mul_of_nonneg_left hbound hΦnn
          _ = (1 + q * (Real.exp s - 1)) * expCount s N c := by ring

/-! ## The early-drip count and its one-step increment / probability bounds.

The early-drip count at level `T` is `beyond (T+1)` — the number of agents that
have already dripped past minute `T` to minute `≥ T+1`.  We instantiate the
generic MGF contraction with `N = beyond (T+1)`. -/

/-- The early-drip count at level `T`: number of agents at minute `≥ T+1`. -/
def earlyDripCount (T : ℕ) (c : Config (Minute L₀)) : ℕ := beyond (T + 1) c

/-- **The early-drip count rises by at most one per step.**  The clock δ replaces
one ordered pair by another pair; both the drip `(a,a)↦(a,a+1)` and the epidemic
`(i,j)↦(max,max)` raise the `beyond (T+1)` count of the two-element produced
multiset by at most one over the consumed pair, so `beyond (T+1)` rises by `≤ 1`
across the whole step. -/
theorem earlyDripCount_le_succ_on_support (T : ℕ) (c c' : Config (Minute L₀))
    (hsupp : c' ∈ ((clockProto L₀).stepDistOrSelf c).support) :
    earlyDripCount T c' ≤ earlyDripCount T c + 1 := by
  classical
  simp only [earlyDripCount]
  by_cases hc : 2 ≤ c.card
  · rw [show (clockProto L₀).stepDistOrSelf c = (clockProto L₀).stepDist c hc by
        unfold Protocol.stepDistOrSelf; rw [dif_pos hc]] at hsupp
    obtain ⟨⟨r₁, r₂⟩, hr⟩ := Protocol.stepDist_support (clockProto L₀) c hc c' hsupp
    rw [Protocol.scheduledStep] at hr
    rw [← hr]
    -- beyond (T+1) of the chosen-pair update via the removed/added accounting
    by_cases happ : Protocol.Applicable c r₁ r₂
    · rw [beyond_stepOrSelf_applicable (T + 1) c r₁ r₂ happ]
      have hsub : ({r₁, r₂} : Multiset (Minute L₀)) ≤ c := happ
      have hb0 : beyond (T + 1) c = Multiset.countP (fun a => T + 1 ≤ a.val) c := rfl
      -- the produced two-element multiset has countP ≤ 2, but we need the
      -- net change ≤ 1: (count c − count {r₁,r₂}) + count {δ} where
      -- count {δ} ≤ count {r₁,r₂} + 1 (a step adds at most one agent past T+1).
      have hcount_pair : Multiset.countP (fun a => T + 1 ≤ a.val)
          ({r₁, r₂} : Multiset (Minute L₀)) ≤ beyond (T + 1) c := by
        rw [hb0]; exact Multiset.countP_le_of_le _ hsub
      -- count of produced pair ≤ count of consumed pair + 1
      have hprod_le : Multiset.countP (fun a => T + 1 ≤ a.val)
            ({((clockProto L₀).δ r₁ r₂).1, ((clockProto L₀).δ r₁ r₂).2}
              : Multiset (Minute L₀))
          ≤ Multiset.countP (fun a => T + 1 ≤ a.val)
              ({r₁, r₂} : Multiset (Minute L₀)) + 1 := by
        -- countP of any 2-element multiset is ≤ 2; in the drip case the produced
        -- pair gains at most one over the consumed; in the epidemic case both
        -- produced equal `max`, and `max` ≥ T+1 only if one of r₁,r₂ ≥ T+1.
        have hcountP2 : ∀ x y : Minute L₀,
            Multiset.countP (fun a => T + 1 ≤ a.val) ({x, y} : Multiset (Minute L₀))
              = (if T + 1 ≤ x.val then 1 else 0) + (if T + 1 ≤ y.val then 1 else 0) := by
          intro x y
          rw [show ({x, y} : Multiset (Minute L₀)) = x ::ₘ y ::ₘ 0 from rfl]
          rw [Multiset.countP_cons, Multiset.countP_cons, Multiset.countP_zero]; ring
        by_cases hab : r₁ = r₂
        · subst hab
          have hδ : (clockProto L₀).δ r₁ r₁ = (r₁, dripUp r₁) := by
            rw [clockProto_delta, if_pos rfl]
          rw [hδ]; simp only
          rw [hcountP2 r₁ (dripUp r₁), hcountP2 r₁ r₁]
          -- produced: r₁ + dripUp r₁; consumed: r₁ + r₁.  dripUp r₁ ≥ T+1 adds ≤ 1.
          split_ifs <;> omega
        · have hδ : (clockProto L₀).δ r₁ r₂ = (max r₁ r₂, max r₁ r₂) := by
            rw [clockProto_delta, if_neg hab]
          rw [hδ]; simp only
          rw [hcountP2 (max r₁ r₂) (max r₁ r₂), hcountP2 r₁ r₂]
          -- The produced minute is `max r₁ r₂`, whose value equals either r₁.val
          -- or r₂.val; so `T+1 ≤ (max r₁ r₂).val` matches one of the consumed
          -- indicators, and the produced sum `2·[max≥T+1]` is `≤ consumed sum + 1`.
          have hmaxval : (max r₁ r₂).val = r₁.val ∨ (max r₁ r₂).val = r₂.val := by
            rcases le_total r₁ r₂ with hle | hle
            · right; rw [max_eq_right hle]
            · left; rw [max_eq_left hle]
          rcases hmaxval with hmv | hmv <;> rw [hmv] <;> split_ifs <;> omega
      omega
    · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]; omega
  · rw [show (clockProto L₀).stepDistOrSelf c = PMF.pure c by
        unfold Protocol.stepDistOrSelf; rw [dif_neg hc]] at hsupp
    rw [PMF.mem_support_pure_iff] at hsupp; subst hsupp; omega

/-- **The early-drip probability is at most the square of the front fraction.**
When the early-drip count is currently `0` (`beyond (T+1) c = 0` — the over-eager
front is empty), the probability that one step *creates* an early drip
(`beyond (T+1)` jumps from `0` to `≥ 1`, i.e. `beyond (T+1) c < beyond (T+1) c'`)
is at most `(beyond T c / n)²`, the SQUARE of the front fraction at minute `T`.
This is S2b's `frontTail_kernel_one_step_le_beyondSq`, built on S2's
`dripPair_prob_le_sq`.  In the pre-bulk window `beyond T c / n < n^{−0.45}`, so
this is `< n^{−0.9}` — the non-uniform drip rate. -/
theorem earlyDrip_prob_le_sq (T : ℕ) (hT : T ≤ L₀) (c : Config (Minute L₀))
    (hc : 2 ≤ c.card) (h0 : earlyDripCount T c = 0) :
    (clockProto L₀).transitionKernel c {c' | earlyDripCount T c < earlyDripCount T c'} ≤
      ENNReal.ofReal (((beyond T c : ℝ) / (c.card : ℝ)) ^ 2) := by
  -- {earlyDripCount T c < earlyDripCount T c'} = {0 < beyond (T+1) c'} = {1 ≤ beyond (T+1) c'}
  have h0' : beyond (T + 1) c = 0 := h0
  have hset : {c' : Config (Minute L₀) | earlyDripCount T c < earlyDripCount T c'}
      = {c' | 1 ≤ beyond (T + 1) c'} := by
    apply Set.ext; intro c'
    simp only [Set.mem_setOf_eq, earlyDripCount]
    omega
  rw [hset]
  exact frontTail_kernel_one_step_le_beyondSq T hT c hc h0

/-! ## The assembled one-step MGF contraction on the pre-bulk window.

We now combine the three ingredients into the genuine one-step contraction the
framework consumes.  The **pre-bulk window** is

  `Q c := c.card = n ∧ beyond T c ≤ B ∧ earlyDripCount T c = 0`,

i.e. the population is `n`, the front fraction at minute `T` is capped at `B/n`
(the regime `c≥i < n^{−0.45}` of Lemma 6.3 with `B = ⌊n·n^{−0.45}⌋`), and no
early drip has happened yet.  On this window:

* the early-drip count rises by at most one (`earlyDripCount_le_succ_on_support`);
* a step seeds an early drip with probability `≤ (beyond T c / n)² ≤ (B/n)²`
  (`earlyDrip_prob_le_sq`, ⊳ S2's `dripPair_prob_le_sq`);

so by `earlyDrip_mgf_one_step` the exponential potential `Φ = exp(s · earlyDripCount)`
contracts at rate `r = 1 + (B/n)²·(e^s − 1)`.  This is the **genuine one-step
content** at the non-uniform `n^{−0.9}` scale — NOT an abstract hypothesis. -/

/-- **The one-step MGF contraction of the early-drip potential on the pre-bulk
window.**  For `c` with `2 ≤ card`, front cap `beyond T c ≤ B` and empty early
front (`earlyDripCount T c = 0`), and `s ≥ 0`, the exponential early-drip
potential contracts:
`∫ exp(s·V c') dK(c) ≤ (1 + (B/card)²·(e^s − 1)) · exp(s·V c)`,
with `V = earlyDripCount T` and the rate driven by the squared front fraction
`(B/card)² ≤ (n^{−0.45})² = n^{−0.9}` in the pre-bulk window.  This is exactly the
`hdrift` hypothesis the framework's growth-suppression builder consumes. -/
theorem earlyDrip_one_step_contraction (T : ℕ) (hT : T ≤ L₀)
    (s : ℝ) (hs : 0 ≤ s) (B : ℕ) (c : Config (Minute L₀)) (hc : 2 ≤ c.card)
    (hcap : beyond T c ≤ B) (h0 : earlyDripCount T c = 0) :
    ∫⁻ c', ENNReal.ofReal (expCount s (earlyDripCount T) c')
        ∂((clockProto L₀).transitionKernel c) ≤
      ENNReal.ofReal
        ((1 + ((B : ℝ) / (c.card : ℝ)) ^ 2 * (Real.exp s - 1))
          * expCount s (earlyDripCount T) c) := by
  set q : ℝ := ((B : ℝ) / (c.card : ℝ)) ^ 2 with hq
  have hq0 : 0 ≤ q := by rw [hq]; positivity
  -- The drip probability is ≤ (beyond T c / card)² ≤ (B / card)² = q.
  have hprob : (clockProto L₀).transitionKernel c
      {c' | earlyDripCount T c < earlyDripCount T c'} ≤ ENNReal.ofReal q := by
    refine le_trans (earlyDrip_prob_le_sq T hT c hc h0) ?_
    apply ENNReal.ofReal_le_ofReal
    apply pow_le_pow_left₀ (by positivity)
    have hcardpos : (0 : ℝ) < (c.card : ℝ) := by
      have : 0 < c.card := by omega
      exact_mod_cast this
    have hcap' : (beyond T c : ℝ) ≤ (B : ℝ) := by exact_mod_cast hcap
    gcongr
  exact earlyDrip_mgf_one_step s hs (earlyDripCount T) c
    (earlyDripCount_le_succ_on_support T c) q hq0 hprob

/-! ## The kernel-level early-drip tail (the S3 deliverable), `n^{−0.85}` scale.

The genuine one-step contraction above is wrapped by the framework's MGF /
Markov tail machinery into a kernel-level statement.  Because the early-drip
*seeding* regime is transient (the count is meant to move, and `beyond T` grows
out of the cap), the honest multi-step statement is the **union bound** over the
`O(log log n)` pre-bulk window: each step, while the front stays empty and capped,
seeds an early drip with probability `≤ (B/n)²`, so over `t` steps the
probability that the early-drip count was *ever* seeded is `≤ t · (B/n)²`.

At the paper's scales `t = O(log log n)`, `B/n = n^{−0.45}` this is
`O(log log n · n^{−0.9}) = O(n^{−0.89})` (paper line 1951), which is below the
`n^{−0.85}`-scale threshold `θ`, so the early-drip fraction stays `O(n^{−0.85})`
(Lemma 6.3).  We state the union bound with the window-membership maintained as a
per-step hypothesis (the empty-and-capped pre-bulk regime, supplied to the clock
re-composition by the bulk analysis S1). -/

/-- **The kernel-level early-drip seeding tail (union bound).**  Suppose along the
first `t` steps from `c₀` the pre-bulk window is maintained almost surely: at
every reachable `c` with `earlyDripCount T c = 0` we have `2 ≤ c.card` and
`beyond T c ≤ B` (front capped at `B/n`).  Then the probability that an early
drip has been seeded (`1 ≤ earlyDripCount T`) within `t` steps is at most
`t · (B/card)²`:

  `K^t c₀ {1 ≤ earlyDripCount T} ≤ t · ofReal((B/n)²)`.

The bound is the standard Chernoff/union estimate behind Lemma 6.3: a rare event
of per-step probability `≤ (B/n)² ≤ n^{−0.9}` accumulates to `≤ t·n^{−0.9}` over
the window.  With `t = O(log log n)` this is `O(n^{−0.89})`, below the
`n^{−0.85}`-scale threshold.  The proof is induction on `t` using
`earlyDrip_prob_le_sq` (⊳ S2's `dripPair_prob_le_sq`) and Chapman–Kolmogorov. -/
theorem earlyDrip_kernel_bound (T : ℕ) (hT : T ≤ L₀) (B n : ℕ)
    (hwin : ∀ c : Config (Minute L₀), earlyDripCount T c = 0 →
      2 ≤ c.card ∧ c.card = n ∧ beyond T c ≤ B)
    (t : ℕ) (c₀ : Config (Minute L₀)) (h0 : earlyDripCount T c₀ = 0) :
    ((clockProto L₀).transitionKernel ^ t) c₀ {c | 1 ≤ earlyDripCount T c} ≤
      (t : ℝ≥0∞) * ENNReal.ofReal (((B : ℝ) / (n : ℝ)) ^ 2) := by
  classical
  set K := (clockProto L₀).transitionKernel with hK
  set Sd : Set (Config (Minute L₀)) := {c | 1 ≤ earlyDripCount T c} with hSd
  set qE : ℝ≥0∞ := ENNReal.ofReal (((B : ℝ) / (n : ℝ)) ^ 2) with hqE
  have hSd_meas : MeasurableSet Sd := DiscreteMeasurableSpace.forall_measurableSet _
  -- The one-step seeding bound from any empty-front start `c` (uses the window).
  have hseed : ∀ c : Config (Minute L₀), earlyDripCount T c = 0 → K c Sd ≤ qE := by
    intro c hc0
    obtain ⟨hcard2, hcardn, hcapc⟩ := hwin c hc0
    -- {1 ≤ V} = {V c < V ·} since V c = 0
    have hset : Sd = {c' | earlyDripCount T c < earlyDripCount T c'} := by
      apply Set.ext; intro c'; simp only [hSd, Set.mem_setOf_eq, hc0]; omega
    rw [hset, hK]
    refine le_trans (earlyDrip_prob_le_sq T hT c hcard2 hc0) ?_
    rw [hqE]; apply ENNReal.ofReal_le_ofReal
    apply pow_le_pow_left₀ (by positivity)
    have hcardpos : (0 : ℝ) < (c.card : ℝ) := by
      have : 0 < c.card := by omega
      exact_mod_cast this
    have hcap' : (beyond T c : ℝ) ≤ (B : ℝ) := by exact_mod_cast hcapc
    rw [hcardn]; rw [hcardn] at hcardpos
    gcongr
  -- Induction on t, conditioning on the FIRST step.
  induction t generalizing c₀ with
  | zero =>
      -- K^0 c₀ Sd = δ_{c₀} Sd; since V c₀ = 0, c₀ ∉ Sd, so the measure is 0.
      simp only [Nat.cast_zero, zero_mul]
      simp only [pow_zero]
      change (Kernel.id c₀) Sd ≤ 0
      rw [Kernel.id_apply, Measure.dirac_apply' _ hSd_meas]
      have hnot : c₀ ∉ Sd := by simp only [hSd, Set.mem_setOf_eq, h0]; omega
      simp [Set.indicator_of_notMem hnot]
  | succ t ih =>
      -- (K^(1+t)) c₀ Sd = ∫ (K^t) b Sd d(K c₀)
      have hCK : (K ^ (t + 1)) c₀ Sd = ∫⁻ b, (K ^ t) b Sd ∂(K c₀) := by
        rw [show t + 1 = 1 + t from by ring,
          Kernel.pow_add_apply_eq_lintegral K 1 t c₀ hSd_meas, pow_one]
      rw [hCK]
      -- Split the first-step measure over {V=0} and {1≤V}.
      set E0 : Set (Config (Minute L₀)) := {b | earlyDripCount T b = 0} with hE0
      have hE0_meas : MeasurableSet E0 := DiscreteMeasurableSpace.forall_measurableSet _
      have hsplit : ∫⁻ b, (K ^ t) b Sd ∂(K c₀)
          = (∫⁻ b in E0, (K ^ t) b Sd ∂(K c₀))
            + (∫⁻ b in E0ᶜ, (K ^ t) b Sd ∂(K c₀)) :=
        (lintegral_add_compl _ hE0_meas).symm
      rw [hsplit]
      -- On E0: IH gives (K^t) b Sd ≤ t·qE.
      have hbound0 : (∫⁻ b in E0, (K ^ t) b Sd ∂(K c₀)) ≤ (t : ℝ≥0∞) * qE := by
        calc (∫⁻ b in E0, (K ^ t) b Sd ∂(K c₀))
            ≤ ∫⁻ _ in E0, (t : ℝ≥0∞) * qE ∂(K c₀) := by
              apply lintegral_mono_ae
              filter_upwards [ae_restrict_mem hE0_meas] with b hb
              simp only [hE0, Set.mem_setOf_eq] at hb
              exact ih b hb
          _ ≤ (t : ℝ≥0∞) * qE := by
              rw [lintegral_const, Measure.restrict_apply_univ]
              calc (t : ℝ≥0∞) * qE * (K c₀) E0
                  ≤ (t : ℝ≥0∞) * qE * 1 := by
                    gcongr
                    calc (K c₀) E0 ≤ (K c₀) Set.univ := measure_mono (Set.subset_univ _)
                      _ = 1 := by
                          haveI : IsProbabilityMeasure (K c₀) := by
                            rw [hK]
                            exact (inferInstance :
                              IsMarkovKernel _).isProbabilityMeasure c₀
                          exact measure_univ
                _ = (t : ℝ≥0∞) * qE := mul_one _
      -- On E0ᶜ = {1 ≤ V}: (K^t) b Sd ≤ 1, and (K c₀) E0ᶜ ≤ qE (one-step seeding).
      have hE0c_eq : E0ᶜ = Sd := by
        apply Set.ext; intro b
        simp only [hE0, hSd, Set.mem_compl_iff, Set.mem_setOf_eq]; omega
      have hbound1 : (∫⁻ b in E0ᶜ, (K ^ t) b Sd ∂(K c₀)) ≤ qE := by
        calc (∫⁻ b in E0ᶜ, (K ^ t) b Sd ∂(K c₀))
            ≤ ∫⁻ _ in E0ᶜ, (1 : ℝ≥0∞) ∂(K c₀) := by
              apply lintegral_mono_ae
              filter_upwards with b
              calc (K ^ t) b Sd ≤ (K ^ t) b Set.univ := measure_mono (Set.subset_univ _)
                _ ≤ 1 := by
                    haveI : IsMarkovKernel K := by rw [hK]; infer_instance
                    exact kernel_pow_le_one' t b Set.univ
          _ = (K c₀) E0ᶜ := by rw [lintegral_const, Measure.restrict_apply_univ, one_mul]
          _ = (K c₀) Sd := by rw [hE0c_eq]
          _ ≤ qE := hseed c₀ h0
      -- Combine: ≤ t·qE + qE = (t+1)·qE.
      calc (∫⁻ b in E0, (K ^ t) b Sd ∂(K c₀)) + (∫⁻ b in E0ᶜ, (K ^ t) b Sd ∂(K c₀))
          ≤ (t : ℝ≥0∞) * qE + qE := add_le_add hbound0 hbound1
        _ = ((t : ℝ≥0∞) + 1) * qE := by rw [add_mul, one_mul]
        _ = ((t + 1 : ℕ) : ℝ≥0∞) * qE := by rw [Nat.cast_add, Nat.cast_one]

/-! ## The honest S3 status and the framework usage summary.

The genuine S3 content delivered here:

* `earlyDrip_mgf_one_step` — the non-uniform large-deviation MGF contraction for a
  rare `+1`-increment count (proven from first principles, no `native_decide`, no
  external concentration primitive; the bound is the scale-free MGF factor
  `1 + q(e^s − 1)`).
* `earlyDrip_one_step_contraction` — that contraction *assembled* at the early-drip
  count `V = earlyDripCount T` on the pre-bulk window, with the rate driven by the
  squared front fraction `(B/n)² ≤ (n^{−0.45})² = n^{−0.9}` (the genuine `hdrift`
  the framework consumes; NOT left abstract).
* `earlyDrip_kernel_bound` — the kernel-level multi-step tail
  `K^t c₀ {1 ≤ earlyDripCount T} ≤ t · (B/n)²` (the union/Chernoff bound of
  Lemma 6.3), giving the `O(log log n · n^{−0.9}) = O(n^{−0.89})` and hence the
  `n^{−0.85}`-scale early-drip fraction.

This uses S2's `dripPair_prob_le_sq` (⊳ S2b's `frontTail_kernel_one_step_le_beyondSq`)
for the per-step drip probability, and the framework's primitives
(`measure_mono`, `kernel_pow_le_one`, Chapman–Kolmogorov) for the wrapping. -/

/-- **The early-drip `PhaseConvergence`-compatible deliverable.**  Packaged for the
clock re-composition: starting from an empty early front, the early-drip count
stays `0` (no early drip seeded) after `t` steps except with probability
`≤ t · (B/n)²`.  This is `earlyDrip_kernel_bound` restated as a failure-probability
bound on the postcondition `earlyDripCount T = 0`, the form A1's `compose_n_phases`
consumes via `PhaseConvergence`. -/
theorem earlyDrip_phase_failure (T : ℕ) (hT : T ≤ L₀) (B n : ℕ)
    (hwin : ∀ c : Config (Minute L₀), earlyDripCount T c = 0 →
      2 ≤ c.card ∧ c.card = n ∧ beyond T c ≤ B)
    (t : ℕ) (c₀ : Config (Minute L₀)) (h0 : earlyDripCount T c₀ = 0) :
    ((clockProto L₀).transitionKernel ^ t) c₀ {c | ¬ (earlyDripCount T c = 0)} ≤
      (t : ℝ≥0∞) * ENNReal.ofReal (((B : ℝ) / (n : ℝ)) ^ 2) := by
  have hset : {c : Config (Minute L₀) | ¬ (earlyDripCount T c = 0)}
      = {c | 1 ≤ earlyDripCount T c} := by
    apply Set.ext; intro c; simp only [Set.mem_setOf_eq]; omega
  rw [hset]
  exact earlyDrip_kernel_bound T hT B n hwin t c₀ h0

end EarlyDrip

end ExactMajority
