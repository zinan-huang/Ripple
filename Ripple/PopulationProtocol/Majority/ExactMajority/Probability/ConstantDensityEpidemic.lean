/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Avenue S1 — the constant-density rumor epidemic in O(1) PARALLEL time

This file formalizes **Avenue S1** of the Doty et al. Theorem 3.1 time-half
campaign (the keystone-within-the-keystone of `ClockTimeConvergence.lean`'s
honest verdict).

## The gap S1 closes

A0 (`Phase2TimeConvergence.lean`) analyzed the rumor epidemic at **unit
coverage**: `k = n−1` milestones spanning informed counts `1 → n`, each with
per-step probability `epP n i = (i+1)(n−i−1)/(n(n−1))`.  The slowest level (near
`i = 0` or `i = n−2`) has probability `Θ(1/n)`, so `meanTime = Θ(n log n)`
interactions `= Θ(log n)` PARALLEL.  Composing `Θ(log n)` minute levels gives the
SLOW `Θ(log² n)` clock bound (`clock_composed_via_A0`).

The paper's `O(log n)` headline (Theorem 6.9, `ln 9 < 2.2`) needs the
**constant-density bulk crossing**: starting from an informed *fraction* `≥ 1/10`,
reach fraction `≥ 9/10`.  In this window every per-step probability is `Θ(1)` —
a uniformly random pair is informed×uninformed with probability
`j(n−j)/(n(n−1))` and for `n/10 ≤ j ≤ 9n/10` this is `≥ (n/10)(n/10)/(n·n) ≈ 1/100`.
Hence crossing the `Θ(n)`-wide window costs only `Θ(n)` interactions `= O(1)`
PARALLEL.  This is Doty et al. Lemma 4.5 specialized to `a, 1−b, ε` all constant:
by the note after the lemma (paper lines 1378–1383) the failure probability is
then `exp(−Θ(ε²·E[t]·n·c)) = exp(−Θ(n))`.

## The missing primitive and how S1 supplies it

The unit-coverage milestone engine `milestone_hitting_time_bound`
(`JansonHitting.lean`) cannot host a *mid-stream* window: its MGF contraction
must hold at **every** configuration, but the constant-density advance bound
`p ≥ 1/100` holds only on the window `{informed ≥ ⌊n/10⌋}`, which is an
*absorbing* (reachable-from-`Pre`) set, not the whole state space.  The genuinely
missing primitive is therefore a **`Pre`-conditioned geometric decay** — a
multiplicative-drift bound whose contraction hypothesis is required only on an
absorbing set containing the start.  We build it self-contained here
(`lintegral_decay_on_absorbing`, `measure_ge_one_on_absorbing`), using the
already-proven one-step support-closure machinery of `MarkovChain.lean`.

## What is proved here (0 sorry / 0 axiom / no native_decide)

* `lintegral_decay_on_absorbing` / `measure_ge_one_on_absorbing` — the
  `Pre`-conditioned multiplicative-drift decay (the missing primitive);
* `floorInvariant_absorbing` — `{card = n ∧ informed ≥ lo}` is kernel-absorbing;
* `windowPot_contracts_on_floor` — the constant-density window potential
  `Φ(c) = exp(s·(hi − clamp(informed)))·𝟙[informed < hi]` contracts at the
  constant rate `r = 1 − (1/100)(1 − e^{−s})` on the floor-invariant set;
* `constantDensity_tail` — the **one-sided exponential tail at the constant
  scale**: starting from informed `= lo`, the probability the crossing is *not*
  finished after `t` interactions is `≤ exp(−s·t)·exp(s·(hi−lo))`, which for the
  Janson-optimal `s` and `t ≥ λ·Θ(n)` is `exp(−Θ(n))`.  This is exactly the
  hypothesis shape consumed by
  `EpidemicTime.epidemicTime_concentration_of_tail_bounds`;
* `constantDensity_epidemic_O1_parallel` — from `card = n`, informed `= ⌊n/10⌋`,
  the kernel reaches informed `≥ ⌊9n/10⌋` within `t` interactions with failure
  probability `≤ exp(−s·t + s·(hi−lo))`; instantiating `s = log 2` and
  `t = ⌈200·n⌉` gives parallel time `≤ 200 = O(1)` and failure `≤ exp(−Θ(n))`.

This is the missing piece that, fed per-minute into the clock in place of A0's
`Θ(log n)`-per-level engine, upgrades the proven `Θ(log² n)`
(`clock_composed_via_A0`) to the paper's optimal `O(log n)`.

Reference: Doty et al. (arXiv:2106.10201v2) Lemma 4.5 (lines 1344–1383) +
Theorem 6.9 (the `ln 9 < 2.2` bulk crossing).
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Phase2TimeConvergence
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.EpidemicTime
import Ripple.PopulationProtocol.Majority.PopProtoCommon.Convergence.GeometricDrift

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real BigOperators

namespace ConstantDensity

open Phase2Time

/-! ## A `Pre`-conditioned multiplicative-drift decay (the missing primitive)

The standard `PopProtoCommon.measure_potential_ge_one` requires the contraction
`∫ Φ dK(x) ≤ r·Φ(x)` at **every** state `x`.  The constant-density window
contracts only on the absorbing set `{informed ≥ lo}`.  We therefore prove the
contraction restricted to an absorbing predicate `Q` that holds at the start.
The proof mirrors `lintegral_geometric_decay` but threads the a.e. invariance of
`Q` along the trajectory (from `MarkovChain.ae_of_stepDistOrSelf_support_preserved`).
-/

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- **`Pre`-conditioned geometric decay (lintegral form).**  If a measurable
potential `Φ` contracts at rate `r` on every configuration satisfying the
*one-step-support-closed* predicate `Q`, then starting from any `c₀` with `Q c₀`
the `t`-step expectation contracts geometrically:
`∫ Φ d(Kᵗ)(c₀) ≤ rᵗ · Φ(c₀)`. -/
theorem lintegral_decay_on_absorbing (P : Protocol Λ)
    (Φ : Config Λ → ℝ≥0∞) (hΦ : Measurable Φ)
    (Q : Config Λ → Prop)
    (hQ_abs : ∀ c c', Q c → c' ∈ (P.stepDistOrSelf c).support → Q c')
    (r : ℝ≥0∞)
    (hdrift : ∀ c, Q c → ∫⁻ c', Φ c' ∂(P.transitionKernel c) ≤ r * Φ c)
    (t : ℕ) (c₀ : Config Λ) (hQ0 : Q c₀) :
    ∫⁻ c', Φ c' ∂((P.transitionKernel ^ t) c₀) ≤ r ^ t * Φ c₀ := by
  induction t generalizing c₀ with
  | zero =>
    simp only [pow_zero, one_mul]
    change ∫⁻ c', Φ c' ∂(Kernel.id c₀) ≤ Φ c₀
    rw [Kernel.id_apply, lintegral_dirac' c₀ hΦ]
  | succ t ih =>
    change ∫⁻ c', Φ c' ∂(((P.transitionKernel ^ t) ∘ₖ P.transitionKernel) c₀)
      ≤ r ^ (t + 1) * Φ c₀
    rw [Kernel.lintegral_comp _ _ c₀ hΦ]
    -- a.e. over the one-step kernel, the support point still satisfies Q
    have hae : ∀ᵐ b ∂(P.transitionKernel c₀),
        ∫⁻ c', Φ c' ∂((P.transitionKernel ^ t) b) ≤ r ^ t * Φ b := by
      have hsupp_ae : ∀ᵐ b ∂(P.transitionKernel c₀), Q b := by
        have h1 := Protocol.ae_of_stepDistOrSelf_support_preserved P Q hQ_abs c₀ hQ0 1
        simpa [pow_one] using h1
      filter_upwards [hsupp_ae] with b hb
      exact ih b hb
    calc ∫⁻ b, ∫⁻ c', Φ c' ∂((P.transitionKernel ^ t) b) ∂(P.transitionKernel c₀)
        ≤ ∫⁻ b, r ^ t * Φ b ∂(P.transitionKernel c₀) := lintegral_mono_ae hae
      _ = r ^ t * ∫⁻ b, Φ b ∂(P.transitionKernel c₀) := lintegral_const_mul _ hΦ
      _ ≤ r ^ t * (r * Φ c₀) := by gcongr; exact hdrift c₀ hQ0
      _ = r ^ (t + 1) * Φ c₀ := by rw [pow_succ, mul_assoc]

/-- **`Pre`-conditioned Markov tail.**  Under the hypotheses of
`lintegral_decay_on_absorbing`, the probability that `Φ ≥ 1` after `t` steps is
at most `rᵗ · Φ(c₀)`. -/
theorem measure_ge_one_on_absorbing (P : Protocol Λ)
    (Φ : Config Λ → ℝ≥0∞) (hΦ : Measurable Φ)
    (Q : Config Λ → Prop)
    (hQ_abs : ∀ c c', Q c → c' ∈ (P.stepDistOrSelf c).support → Q c')
    (r : ℝ≥0∞)
    (hdrift : ∀ c, Q c → ∫⁻ c', Φ c' ∂(P.transitionKernel c) ≤ r * Φ c)
    (t : ℕ) (c₀ : Config Λ) (hQ0 : Q c₀) :
    (P.transitionKernel ^ t) c₀ {c | 1 ≤ Φ c} ≤ r ^ t * Φ c₀ := by
  have hmarkov := mul_meas_ge_le_lintegral₀ (μ := (P.transitionKernel ^ t) c₀)
    hΦ.aemeasurable (1 : ℝ≥0∞)
  simp only [one_mul] at hmarkov
  exact le_trans hmarkov
    (lintegral_decay_on_absorbing P Φ hΦ Q hQ_abs r hdrift t c₀ hQ0)

/-! ## The constant-density window. -/

/-- Lower window boundary: informed count `⌊n/10⌋` we start from. -/
def lo (n : ℕ) : ℕ := n / 10

/-- Upper window boundary: informed count `⌊9n/10⌋` we cross to. -/
def hi (n : ℕ) : ℕ := 9 * n / 10

theorem lo_lt_hi (n : ℕ) (hn : 20 ≤ n) : lo n < hi n := by unfold lo hi; omega

theorem hi_lt_n (n : ℕ) (hn : 20 ≤ n) : hi n < n := by unfold hi; omega

theorem lo_pos (n : ℕ) (hn : 20 ≤ n) : 0 < lo n := by unfold lo; omega

/-- The clamped informed count, restricted to the window `[lo, hi]`. -/
def clampInf (n : ℕ) (c : Config Bool) : ℕ := min (max (informed c) (lo n)) (hi n)

theorem clampInf_le_hi (n : ℕ) (c : Config Bool) : clampInf n c ≤ hi n := by
  unfold clampInf; omega

theorem clampInf_ge_lo (n : ℕ) (c : Config Bool) : lo n ≤ clampInf n c := by
  unfold clampInf
  have : lo n ≤ hi n := by
    by_cases h : 20 ≤ n
    · exact (lo_lt_hi n h).le
    · unfold lo hi; omega
  omega

/-- On the floor invariant `lo ≤ informed`, the clamp equals `min (informed) hi`. -/
theorem clampInf_eq_of_floor (n : ℕ) (c : Config Bool) (hfl : lo n ≤ informed c) :
    clampInf n c = min (informed c) (hi n) := by
  unfold clampInf; omega

/-! ## The constant-density window potential

`Φ(c) = exp(s·(hi − clampInf c))` while informed `< hi`, and `0` once informed
`≥ hi` (the crossing is done).  The deficit `hi − clampInf c` is at least `1`
exactly when the crossing is unfinished, so `Φ ≥ eˢ > 1` there and `{¬done} =
{1 ≤ Φ}`.  On the floor invariant the clamp tracks `informed` itself in the
window, so one epidemic step shrinks the deficit by one with probability `≥ 1/100`,
giving the constant-rate contraction. -/

/-- The "crossing finished" predicate: informed has reached the upper boundary. -/
def Crossed (n : ℕ) (c : Config Bool) : Prop := hi n ≤ informed c

/-- The window potential. -/
noncomputable def windowPot (n : ℕ) (s : ℝ) (c : Config Bool) : ℝ≥0∞ :=
  if hi n ≤ informed c then 0
  else ENNReal.ofReal (Real.exp (s * ((hi n : ℝ) - (clampInf n c : ℝ))))

theorem windowPot_measurable (n : ℕ) (s : ℝ) : Measurable (windowPot n s) :=
  fun _ _ => DiscreteMeasurableSpace.forall_measurableSet _

/-- On `{¬Crossed}` (informed `< hi`), the window potential is `≥ eˢ`, hence
`≥ 1` for `s ≥ 0`; on `{Crossed}` it is `0`.  Thus `{¬Crossed} = {1 ≤ Φ}`. -/
theorem not_crossed_iff_pot_ge_one (n : ℕ) (s : ℝ) (hs : 0 < s) (c : Config Bool)
    (hfl : lo n ≤ informed c) (hn : 20 ≤ n) :
    ¬ Crossed n c ↔ 1 ≤ windowPot n s c := by
  unfold Crossed windowPot
  constructor
  · intro hnc
    rw [not_le] at hnc
    rw [if_neg (by omega)]
    rw [clampInf_eq_of_floor n c hfl]
    have hmin : min (informed c) (hi n) = informed c := by omega
    rw [hmin]
    -- deficit ≥ 1 ⇒ exp(s·deficit) ≥ exp(s) > 1
    have hdef : (1 : ℝ) ≤ (hi n : ℝ) - (informed c : ℝ) := by
      have : (informed c : ℝ) + 1 ≤ (hi n : ℝ) := by exact_mod_cast (by omega : informed c + 1 ≤ hi n)
      linarith
    have hge : (1 : ℝ) ≤ Real.exp (s * ((hi n : ℝ) - (informed c : ℝ))) := by
      rw [show (1 : ℝ) = Real.exp 0 from (Real.exp_zero).symm]
      apply Real.exp_le_exp.mpr
      have : 0 ≤ s * ((hi n : ℝ) - (informed c : ℝ)) := by positivity
      linarith
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hge
  · intro h1 hc
    rw [if_pos hc] at h1
    simp at h1

/-! ## The floor invariant is absorbing. -/

/-- The floor invariant: exactly `n` agents and informed at least `lo`. -/
def floorInv (n : ℕ) (c : Config Bool) : Prop := c.card = n ∧ lo n ≤ informed c

/-- The floor invariant is one-step-support closed (hence kernel-absorbing):
`card` is preserved and `informed` is non-decreasing under any step. -/
theorem floorInvariant_absorbing (n : ℕ) (c c' : Config Bool)
    (h : floorInv n c) (hc' : c' ∈ (epidemicProto.stepDistOrSelf c).support) :
    floorInv n c' := by
  obtain ⟨hcard, hfl⟩ := h
  refine ⟨?_, ?_⟩
  · rw [Protocol.stepDistOrSelf_support_card_eq epidemicProto c c' hc']; exact hcard
  · exact informed_ge_monotone (lo n) c c' hfl hc'

/-! ## Constant-density per-step advance bound: `p ≥ 1/100` in the window.

When the crossing is unfinished and `lo ≤ informed = m < hi`, the epidemic step
advances `informed` to `m + 1` with probability `≥ m(n−m)/(n(n−1)) ≥ 1/100`,
because `n/10 ≤ m ≤ 9n/10` forces both factors `≥ n/10`. -/

/-- The constant-density advance probability lower bound: for any informed count
`m` with `lo ≤ m < hi`, `m(n−m)/(n(n−1)) ≥ 1/100`. -/
theorem advance_prob_ge (n m : ℕ) (hn : 20 ≤ n) (hm_lo : lo n ≤ m) (hm_hi : m < hi n) :
    (1 : ℝ) / 100 ≤ (m * (n - m) : ℝ) / (n * (n - 1) : ℝ) := by
  -- m ≥ n/10 and n - m ≥ n/10 (since m ≤ hi - 1 ≤ 9n/10 - 1 < 9n/10)
  have hmR0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hnR : (20 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  -- 10 * lo ≥ n - 9, lo ≤ m
  have hlo : 10 * lo n ≥ n - 9 := by unfold lo; omega
  have hloR : (10 : ℝ) * (lo n : ℝ) ≥ (n : ℝ) - 9 := by
    have hc := (Nat.cast_le (α := ℝ)).mpr hlo
    have hsub : ((n - 9 : ℕ) : ℝ) ≥ (n : ℝ) - 9 := by
      rcases Nat.lt_or_ge n 9 with h | h
      · simp only [Nat.sub_eq_zero_of_le (by omega : n ≤ 9), Nat.cast_zero]; linarith
      · rw [Nat.cast_sub h]; push_cast; linarith
    push_cast at hc; linarith
  have hm_loR : (lo n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm_lo
  -- m ≥ n/10 - 9/10, so m + 1 ≥ n/10; we use m ≥ n/10 - 1
  have hm_lower : (n : ℝ) / 10 - 1 ≤ (m : ℝ) := by
    have : (n : ℝ) - 9 ≤ 10 * (m : ℝ) := le_trans hloR (by linarith)
    linarith
  -- hi ≤ 9n/10, m < hi ⇒ m ≤ hi - 1 ⇒ n - m ≥ n - hi + 1 ≥ n/10 + 1
  have hhi : 10 * hi n ≤ 9 * n := by unfold hi; omega
  have hhiR : (hi n : ℝ) ≤ (9 : ℝ) * (n : ℝ) / 10 := by
    have hc := (Nat.cast_le (α := ℝ)).mpr hhi; push_cast at hc; linarith
  have hm_hiR : (m : ℝ) + 1 ≤ (hi n : ℝ) := by exact_mod_cast (by omega : m + 1 ≤ hi n)
  have hm_upper : (m : ℝ) ≤ (9 : ℝ) * (n : ℝ) / 10 - 1 := by linarith
  -- now n - m ≥ n/10 + 1 ≥ n/10, and m ≥ n/10 - 1
  have hnm : (n : ℝ) - (m : ℝ) ≥ (n : ℝ) / 10 := by linarith
  -- denominator
  have hden_pos : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := by nlinarith
  rw [le_div_iff₀ hden_pos]
  -- goal: (1/100)*(n*(n-1)) ≤ m*(n-m)
  -- m ≥ n/10 - 1, n-m ≥ n/10; m·(n-m) ≥ (n/10 - 1)(n/10).  Want ≥ (1/100) n (n-1).
  -- (n/10-1)(n/10) = n²/100 - n/10 = (1/100)(n² - 10n) and (1/100) n(n-1) = (1/100)(n²-n).
  -- Need n²-10n ≥ ... not quite; instead use m ≥ n/10 - 1 with n ≥ 20 ⇒ m ≥ 1, and a direct nlinarith.
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by
    have : (n : ℝ) / 10 - 1 ≥ 1 := by linarith
    linarith
  nlinarith [mul_le_mul hm_lower hnm (by linarith : (0:ℝ) ≤ (n:ℝ)/10) hmR0,
    hm_lower, hnm, hnR, hmR0, hm1]

/-! ## Pointwise one-step bound on the window potential.

On the one-step support, `informed` is non-decreasing, so the window potential
never increases; moreover on the *advance* set `{m+1 ≤ informed}` the deficit
drops by at least one, scaling the potential by `e^{−s}`. -/

/-- For a config `c` with `informed c = m`, every support point `c'` satisfies
`windowPot n s c' ≤ (if m+1 ≤ informed c' then ofReal(e^{s(hi−m−1)}) else
ofReal(e^{s(hi−m)}))`, provided `lo ≤ m < hi` (so both target deficits are
non-negative). -/
theorem windowPot_pointwise_bound (n : ℕ) (s : ℝ) (hs : 0 < s) (c : Config Bool)
    (m : ℕ) (hn : 20 ≤ n) (hm : informed c = m) (hm_lo : lo n ≤ m) (hm_hi : m < hi n)
    (c' : Config Bool) (hsupp : c' ∈ (epidemicProto.stepDistOrSelf c).support) :
    windowPot n s c' ≤
      (if m + 1 ≤ informed c' then
        ENNReal.ofReal (Real.exp (s * ((hi n : ℝ) - (m : ℝ) - 1)))
      else
        ENNReal.ofReal (Real.exp (s * ((hi n : ℝ) - (m : ℝ))))) := by
  -- informed monotone on support: informed c' ≥ m
  have hmono : m ≤ informed c' := by
    have := informed_ge_monotone m c c' (by rw [hm]) hsupp
    exact this
  unfold windowPot clampInf
  by_cases hcross : hi n ≤ informed c'
  · -- crossed ⇒ Φ' = 0 ≤ anything
    rw [if_pos hcross]
    split_ifs <;> positivity
  · rw [if_neg hcross]
    rw [not_le] at hcross
    by_cases hadv : m + 1 ≤ informed c'
    · rw [if_pos hadv]
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      -- clamp c' = min (max (informed c') lo) hi; informed c' ≥ m+1 ≥ lo+1, < hi
      have hclamp : min (max (informed c') (lo n)) (hi n) = informed c' := by omega
      rw [hclamp]
      have : (m : ℝ) + 1 ≤ (informed c' : ℝ) := by exact_mod_cast hadv
      nlinarith [hs, this]
    · rw [if_neg hadv]
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      -- ¬advance ⇒ informed c' = m (since informed c' ≥ m and < m+1)
      have heq : informed c' = m := by omega
      have hclamp : min (max (informed c') (lo n)) (hi n) = informed c' := by omega
      rw [hclamp, heq]

/-! ## The constant-density window contraction (the heart of S1).

On the floor-invariant, uncrossed configurations, the window potential contracts
at the constant rate `r = 1 − (1/100)(1 − e^{−s})`. -/

/-- **Constant-density window contraction.**  For `s > 0`, on every configuration
`c` with `floorInv n c` (so `card = n`, `informed ≥ lo`) and `¬ Crossed n c`
(so `informed < hi`), the window potential contracts at the constant rate
`r := ofReal(1 − (1/100)(1 − e^{−s}))`:
`∫ Φ dK(c) ≤ r · Φ(c)`. -/
theorem windowPot_contracts_on_floor (n : ℕ) (s : ℝ) (hs : 0 < s) (hn : 20 ≤ n)
    (c : Config Bool) (hfl : floorInv n c) (hnc : ¬ Crossed n c) :
    ∫⁻ c', windowPot n s c' ∂(epidemicProto.transitionKernel c) ≤
      ENNReal.ofReal (1 - (1 / 100) * (1 - Real.exp (-s))) * windowPot n s c := by
  obtain ⟨hcard, hfloor⟩ := hfl
  set m := informed c with hm
  have hm_hi : m < hi n := by rw [Crossed, not_le] at hnc; exact hnc
  have hm_lo : lo n ≤ m := hfloor
  -- Φ(c) = ofReal(exp(s(hi - m)))  (since uncrossed, clamp = m)
  have hΦc : windowPot n s c = ENNReal.ofReal (Real.exp (s * ((hi n : ℝ) - (m : ℝ)))) := by
    unfold windowPot
    rw [if_neg (by rw [← hm]; omega)]
    rw [clampInf_eq_of_floor n c hfloor]
    congr 2
    have : min (informed c) (hi n) = m := by rw [← hm]; omega
    rw [this]
  -- The advance set and its measure ≥ 1/100
  set A := {c' : Config Bool | m + 1 ≤ informed c'} with hA_def
  have hA_meas : MeasurableSet A := DiscreteMeasurableSpace.forall_measurableSet _
  -- step_advance_prob: K(A) ≥ ofReal(m(n-m)/(n(n-1)))
  have hc2 : 2 ≤ c.card := by rw [hcard]; omega
  have hm1 : 1 ≤ m := by
    have := lo_pos n hn; omega
  have hmn : m < c.card := by rw [hcard]; exact lt_trans hm_hi (hi_lt_n n hn)
  have hstep := step_advance_prob c m hc2 hm.symm hm1 hmn
  -- transport to the constant lower bound 1/100
  have hp100 : (1 : ℝ) / 100 ≤ (m * (c.card - m) : ℝ) / (c.card * (c.card - 1) : ℝ) := by
    rw [hcard]; exact advance_prob_ge n m hn hm_lo hm_hi
  set E0 : ℝ := Real.exp (s * ((hi n : ℝ) - (m : ℝ))) with hE0
  set E1 : ℝ := Real.exp (s * ((hi n : ℝ) - (m : ℝ) - 1)) with hE1
  have hE0_pos : 0 < E0 := Real.exp_pos _
  have hE1_pos : 0 < E1 := Real.exp_pos _
  -- E1 = E0 * exp(-s)
  have hE1_eq : E1 = E0 * Real.exp (-s) := by
    rw [hE0, hE1, ← Real.exp_add]; congr 1; ring
  -- pointwise integrand bound
  change ∫⁻ c', windowPot n s c' ∂(epidemicProto.stepDistOrSelf c).toMeasure ≤ _
  calc ∫⁻ c', windowPot n s c' ∂(epidemicProto.stepDistOrSelf c).toMeasure
      ≤ ∫⁻ c', (if m + 1 ≤ informed c' then ENNReal.ofReal E1
          else ENNReal.ofReal E0) ∂(epidemicProto.stepDistOrSelf c).toMeasure := by
        apply lintegral_mono_ae
        rw [ae_iff]
        rw [PMF.toMeasure_apply_eq_zero_iff _
          (DiscreteMeasurableSpace.forall_measurableSet _)]
        rw [Set.disjoint_left]
        intro x hsupp hbad
        apply hbad
        exact windowPot_pointwise_bound n s hs c m hn hm.symm hm_lo hm_hi x hsupp
    _ = (∫⁻ c' in A, ENNReal.ofReal E1 ∂(epidemicProto.stepDistOrSelf c).toMeasure) +
        (∫⁻ c' in Aᶜ, ENNReal.ofReal E0 ∂(epidemicProto.stepDistOrSelf c).toMeasure) := by
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
    _ = ENNReal.ofReal E1 * (epidemicProto.stepDistOrSelf c).toMeasure A +
        ENNReal.ofReal E0 * (epidemicProto.stepDistOrSelf c).toMeasure Aᶜ := by
        rw [lintegral_const, Measure.restrict_apply_univ,
            lintegral_const, Measure.restrict_apply_univ]
    _ ≤ ENNReal.ofReal (1 - (1 / 100) * (1 - Real.exp (-s))) * windowPot n s c := by
        rw [hΦc]
        set q := (epidemicProto.stepDistOrSelf c).toMeasure A with hq_def
        set qc := (epidemicProto.stepDistOrSelf c).toMeasure Aᶜ with hqc_def
        haveI : IsProbabilityMeasure (epidemicProto.stepDistOrSelf c).toMeasure :=
          PMF.toMeasure.isProbabilityMeasure _
        -- q ≥ ofReal(1/100)
        have hq_ge : ENNReal.ofReal ((1 : ℝ) / 100) ≤ q := by
          refine le_trans (ENNReal.ofReal_le_ofReal hp100) ?_
          exact hstep
        have hq_le_one : q ≤ 1 := by
          calc q ≤ (epidemicProto.stepDistOrSelf c).toMeasure Set.univ :=
                measure_mono (Set.subset_univ _)
            _ = 1 := measure_univ
        have hq_ne_top : q ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hq_le_one
        have hqc_eq : qc = 1 - q := by
          have h_compl := measure_compl hA_meas hq_ne_top
          rw [show (epidemicProto.stepDistOrSelf c).toMeasure Set.univ = 1 from measure_univ]
            at h_compl
          exact h_compl
        set qr := q.toReal with hqr_def
        have hqr_nonneg : 0 ≤ qr := ENNReal.toReal_nonneg
        have hqr_le_one : qr ≤ 1 := by
          have := ENNReal.toReal_mono ENNReal.one_ne_top hq_le_one
          rwa [ENNReal.toReal_one] at this
        have hq_ofReal : q = ENNReal.ofReal qr := (ENNReal.ofReal_toReal hq_ne_top).symm
        have h100_le_qr : (1 : ℝ) / 100 ≤ qr := by
          have h1 : ENNReal.ofReal ((1 : ℝ) / 100) ≤ ENNReal.ofReal qr := by
            rw [← hq_ofReal]; exact hq_ge
          exact (ENNReal.ofReal_le_ofReal_iff hqr_nonneg).mp h1
        have h1mqr_nonneg : 0 ≤ 1 - qr := by linarith
        have hqc_ofReal : qc = ENNReal.ofReal (1 - qr) := by
          rw [hqc_eq, hq_ofReal,
              show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm,
              ← ENNReal.ofReal_sub 1 hqr_nonneg]
        -- combine into single ofReal
        have lhs_eq : ENNReal.ofReal E1 * q + ENNReal.ofReal E0 * qc =
            ENNReal.ofReal (E1 * qr + E0 * (1 - qr)) := by
          rw [hq_ofReal, hqc_ofReal,
              ← ENNReal.ofReal_mul hE1_pos.le, ← ENNReal.ofReal_mul hE0_pos.le,
              ← ENNReal.ofReal_add (mul_nonneg hE1_pos.le hqr_nonneg)
                (mul_nonneg hE0_pos.le h1mqr_nonneg)]
        have rhs_eq : ENNReal.ofReal (1 - (1 / 100) * (1 - Real.exp (-s))) * ENNReal.ofReal E0 =
            ENNReal.ofReal ((1 - (1 / 100) * (1 - Real.exp (-s))) * E0) := by
          rw [← ENNReal.ofReal_mul]
          have hexp_le_one : Real.exp (-s) ≤ 1 := by
            rw [show (1 : ℝ) = Real.exp 0 from (Real.exp_zero).symm]
            exact Real.exp_le_exp.mpr (by linarith)
          have : (1 : ℝ) - (1 / 100) * (1 - Real.exp (-s)) ≥ 0 := by
            have : (0 : ℝ) ≤ 1 - Real.exp (-s) := by linarith
            nlinarith
          linarith
        rw [lhs_eq, rhs_eq]
        apply ENNReal.ofReal_le_ofReal
        -- E1·qr + E0(1−qr) = E0(1 − qr(1−e^{−s})) ≤ E0(1 − (1/100)(1−e^{−s}))
        have hexp_lt_one : Real.exp (-s) ≤ 1 := by
          rw [show (1 : ℝ) = Real.exp 0 from (Real.exp_zero).symm]
          exact Real.exp_le_exp.mpr (by linarith)
        have hfactor : E1 * qr + E0 * (1 - qr) = E0 * (1 - qr * (1 - Real.exp (-s))) := by
          rw [hE1_eq]; ring
        rw [hfactor]
        have hrhs : (1 - (1 / 100) * (1 - Real.exp (-s))) * E0
            = E0 * (1 - (1 / 100) * (1 - Real.exp (-s))) := by ring
        rw [hrhs]
        apply mul_le_mul_of_nonneg_left _ hE0_pos.le
        -- 1 − qr(1−e^{−s}) ≤ 1 − (1/100)(1−e^{−s})  since qr ≥ 1/100, (1−e^{−s}) ≥ 0
        have h1me : (0 : ℝ) ≤ 1 - Real.exp (-s) := by linarith
        nlinarith [mul_le_mul_of_nonneg_right h100_le_qr h1me]

/-- Globally (for any `s > 0`), an uncrossed configuration has window potential
`≥ 1`: the deficit `hi − clamp(informed) ≥ 1`, so `Φ ≥ eˢ > 1`. -/
theorem not_crossed_imp_pot_ge_one (n : ℕ) (s : ℝ) (hs : 0 < s) (hn : 20 ≤ n)
    (c : Config Bool) (hnc : ¬ Crossed n c) : 1 ≤ windowPot n s c := by
  unfold Crossed at hnc
  rw [not_le] at hnc
  unfold windowPot clampInf
  rw [if_neg (by omega)]
  rw [← ENNReal.ofReal_one]
  apply ENNReal.ofReal_le_ofReal
  rw [show (1 : ℝ) = Real.exp 0 from (Real.exp_zero).symm]
  apply Real.exp_le_exp.mpr
  -- clamp (nat) = min (max informed lo) hi ≤ hi - 1, so deficit ≥ 1
  have hlohi : lo n < hi n := lo_lt_hi n hn
  have hclamp_lt : min (max (informed c) (lo n)) (hi n) ≤ hi n - 1 := by omega
  have h1 : ((min (max (informed c) (lo n)) (hi n) : ℕ) : ℝ) ≤ (hi n : ℝ) - 1 := by
    have h1' : ((min (max (informed c) (lo n)) (hi n) : ℕ) : ℝ) ≤ ((hi n - 1 : ℕ) : ℝ) := by
      exact_mod_cast hclamp_lt
    have h2 : ((hi n - 1 : ℕ) : ℝ) = (hi n : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    linarith
  have hdef : (1 : ℝ) ≤ (hi n : ℝ) - ((min (max (informed c) (lo n)) (hi n) : ℕ) : ℝ) := by
    linarith
  nlinarith [hs, hdef]

/-- The contraction holds on the *entire* floor-invariant set (crossed or not):
on crossed configs `Φ = 0`, and `Crossed` is preserved, so `∫ Φ dK = 0`. -/
theorem windowPot_drift_floorInv (n : ℕ) (s : ℝ) (hs : 0 < s) (hn : 20 ≤ n)
    (c : Config Bool) (hfl : floorInv n c) :
    ∫⁻ c', windowPot n s c' ∂(epidemicProto.transitionKernel c) ≤
      ENNReal.ofReal (1 - (1 / 100) * (1 - Real.exp (-s))) * windowPot n s c := by
  by_cases hnc : Crossed n c
  · -- crossed: Φ(c) = 0, and Φ' = 0 a.e. (Crossed absorbing)
    have hΦc0 : windowPot n s c = 0 := by
      unfold windowPot; rw [if_pos (by exact hnc)]
    rw [hΦc0, mul_zero, nonpos_iff_eq_zero]
    change ∫⁻ c', windowPot n s c' ∂(epidemicProto.stepDistOrSelf c).toMeasure = 0
    rw [lintegral_eq_zero_iff (windowPot_measurable n s)]
    rw [Filter.eventuallyEq_iff_exists_mem]
    refine ⟨(epidemicProto.stepDistOrSelf c).support, ?_, ?_⟩
    · rw [mem_ae_iff, PMF.toMeasure_apply_eq_zero_iff _
        (DiscreteMeasurableSpace.forall_measurableSet _)]
      rw [Set.disjoint_left]; intro x hsupp hx
      exact hx (PMF.mem_support_iff _ _ |>.mp hsupp)
    · intro c' hc'
      -- informed c' ≥ informed c ≥ hi, so Crossed c', Φ' = 0
      have hcr : hi n ≤ informed c' :=
        informed_ge_monotone (hi n) c c' hnc hc'
      show windowPot n s c' = 0
      unfold windowPot; rw [if_pos hcr]
  · exact windowPot_contracts_on_floor n s hs hn c hfl hnc

/-! ## The constant-density one-sided tail (Avenue S1 deliverable). -/

/-- **The constant-density exponential tail.**  Starting from `card = n`,
`informed = lo` (`= ⌊n/10⌋`), the probability that the crossing to
`informed ≥ hi` (`= ⌊9n/10⌋`) is *not* finished within `t` interactions is

  `(Kᵗ) c₀ {¬Crossed} ≤ (1 − (1/100)(1 − e^{−s}))ᵗ · exp(s·(hi − lo))`.

Because `1 − (1/100)(1 − e^{−s}) < 1` and `hi − lo = Θ(n)`, taking `t = Θ(n)`
makes the right side `exp(−Θ(n))`.  This is Doty et al. Lemma 4.5 at the
constant scale (`pMin = Θ(1)`), the one-sided tail consumed by
`epidemicTime_concentration_of_tail_bounds`. -/
theorem constantDensity_tail (n : ℕ) (s : ℝ) (hs : 0 < s) (hn : 20 ≤ n)
    (c₀ : Config Bool) (hcard : c₀.card = n) (hinf : informed c₀ = lo n)
    (t : ℕ) :
    (epidemicProto.transitionKernel ^ t) c₀ {c | ¬ Crossed n c} ≤
      ENNReal.ofReal (1 - (1 / 100) * (1 - Real.exp (-s))) ^ t *
        ENNReal.ofReal (Real.exp (s * ((hi n : ℝ) - (lo n : ℝ)))) := by
  set r : ℝ≥0∞ := ENNReal.ofReal (1 - (1 / 100) * (1 - Real.exp (-s))) with hr
  have hQ0 : floorInv n c₀ := ⟨hcard, by rw [hinf]⟩
  -- {¬Crossed} ⊆ {1 ≤ Φ}
  have hsubset : {c : Config Bool | ¬ Crossed n c} ⊆ {c | 1 ≤ windowPot n s c} := by
    intro c hc
    exact not_crossed_imp_pot_ge_one n s hs hn c hc
  -- Φ(c₀) = ofReal(exp(s(hi - lo)))
  have hΦc0 : windowPot n s c₀ = ENNReal.ofReal (Real.exp (s * ((hi n : ℝ) - (lo n : ℝ)))) := by
    unfold windowPot
    rw [if_neg (by rw [hinf]; have := lo_lt_hi n hn; omega)]
    rw [clampInf_eq_of_floor n c₀ (by rw [hinf])]
    congr 2
    have : min (informed c₀) (hi n) = lo n := by rw [hinf]; have := lo_lt_hi n hn; omega
    rw [this]
  calc (epidemicProto.transitionKernel ^ t) c₀ {c | ¬ Crossed n c}
      ≤ (epidemicProto.transitionKernel ^ t) c₀ {c | 1 ≤ windowPot n s c} :=
        measure_mono hsubset
    _ ≤ r ^ t * windowPot n s c₀ :=
        measure_ge_one_on_absorbing epidemicProto (windowPot n s)
          (windowPot_measurable n s) (floorInv n) (floorInvariant_absorbing n) r
          (windowPot_drift_floorInv n s hs hn) t c₀ hQ0
    _ = r ^ t * ENNReal.ofReal (Real.exp (s * ((hi n : ℝ) - (lo n : ℝ)))) := by rw [hΦc0]

/-! ## The O(1)-parallel crossing theorem (Avenue S1 headline). -/

/-- `hi − lo ≤ n` as reals (the window width is at most the population). -/
theorem hi_sub_lo_le_n (n : ℕ) : (hi n : ℝ) - (lo n : ℝ) ≤ (n : ℝ) := by
  have h1 : hi n ≤ n := by unfold hi; omega
  have h2 : (0 : ℝ) ≤ (lo n : ℝ) := Nat.cast_nonneg _
  have : (hi n : ℝ) ≤ (n : ℝ) := by exact_mod_cast h1
  linarith

/-- The failure probability collapses into a single real exponential. -/
theorem constantDensity_tail_real (n : ℕ) (s : ℝ) (hs : 0 < s) (hn : 20 ≤ n)
    (c₀ : Config Bool) (hcard : c₀.card = n) (hinf : informed c₀ = lo n) (t : ℕ) :
    (epidemicProto.transitionKernel ^ t) c₀ {c | ¬ Crossed n c} ≤
      ENNReal.ofReal
        ((1 - (1 / 100) * (1 - Real.exp (-s))) ^ t *
          Real.exp (s * ((hi n : ℝ) - (lo n : ℝ)))) := by
  have hbase : 0 ≤ 1 - (1 / 100) * (1 - Real.exp (-s)) := by
    have hle : Real.exp (-s) ≤ 1 := by
      rw [show (1 : ℝ) = Real.exp 0 from (Real.exp_zero).symm]
      exact Real.exp_le_exp.mpr (by linarith)
    have hpos : (0 : ℝ) ≤ 1 - Real.exp (-s) := by linarith
    have hexppos : (0 : ℝ) < Real.exp (-s) := Real.exp_pos _
    nlinarith [hpos, hexppos]
  refine le_trans (constantDensity_tail n s hs hn c₀ hcard hinf t) ?_
  rw [ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_pow hbase]

/-- **Avenue S1 — the constant-density epidemic crosses `0.1 → 0.9` in `O(1)`
PARALLEL time with `exp(−Θ(n))` failure.**

Concretely, with the Janson-optimal rate parameter `s = log 2` (so `e^{−s} =
1/2`, contraction rate `r = 199/200`), starting from `card = n`, `informed = lo`
(`= ⌊n/10⌋`), after `t` interactions the probability that the crossing to
`informed ≥ hi` (`= ⌊9n/10⌋`) is unfinished is at most

  `(199/200)ᵗ · 2^{(hi − lo)}  ≤  (199/200)ᵗ · 2ⁿ`.

For `t = ⌈200·n⌉` interactions — i.e. parallel time `t/n ≤ 201 = O(1)` — this is
`exp(200n·log(199/200) + n·log 2) ≤ exp(−Θ(n))`, the paper's Theorem 6.9 bulk
crossing.  We expose the clean kernel-level bound; the asymptotic `exp(−Θ(n))`
follows since `log(199/200) < 0` and `200·log(199/200) + log 2 < 0`. -/
theorem constantDensity_epidemic_O1_parallel (n : ℕ) (hn : 20 ≤ n)
    (c₀ : Config Bool) (hcard : c₀.card = n) (hinf : informed c₀ = lo n) (t : ℕ) :
    (epidemicProto.transitionKernel ^ t) c₀ {c | informed c < hi n} ≤
      ENNReal.ofReal (((199 : ℝ) / 200) ^ t * (2 : ℝ) ^ (hi n - lo n)) := by
  have hs : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  -- e^{-log 2} = 1/2
  have he : Real.exp (-Real.log 2) = 1 / 2 := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0:ℝ) < 2)]; norm_num
  -- the rate becomes 199/200
  have hrate : (1 : ℝ) - (1 / 100) * (1 - Real.exp (-Real.log 2)) = 199 / 200 := by
    rw [he]; norm_num
  -- the potential becomes 2^{hi-lo}
  have hpot : Real.exp (Real.log 2 * ((hi n : ℝ) - (lo n : ℝ))) = (2 : ℝ) ^ (hi n - lo n) := by
    have hcast : ((hi n : ℝ) - (lo n : ℝ)) = ((hi n - lo n : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by have := lo_lt_hi n hn; omega)]
    rw [hcast, mul_comm, Real.exp_nat_mul, Real.exp_log (by norm_num : (0:ℝ) < 2)]
  have hev : {c : Config Bool | informed c < hi n} = {c : Config Bool | ¬ Crossed n c} := by
    ext c; simp only [Set.mem_setOf_eq, Crossed, not_le]
  rw [hev]
  have h := constantDensity_tail_real n (Real.log 2) hs hn c₀ hcard hinf t
  rw [hrate, hpot] at h
  exact h

/-! ## Discharging `epidemicTime_concentration_of_tail_bounds`.

The conditional theorem `EpidemicTime.epidemicTime_concentration_of_tail_bounds`
combines two one-sided tails of the *shape*
`P{…} ≤ (1/2)·exp(−(1/8)·ε²·E·n·c)` — an exponential **in `n`** — into the
two-sided epidemic concentration.  Our `constantDensity_tail_real` supplies
exactly such an exponential-in-`n` one-sided tail at the constant-density scale.
The following bridge records that our bound has the required exponential-in-`n`
form: there is a constant `β > 0` with failure `≤ exp(−β·n)` once
`t = ⌈200·n⌉`, which is the upper-tail hypothesis `h_upper` (the crossing taking
*more* than the constant parallel time is exponentially unlikely).  The
constant-density `pMin = Θ(1)` and window width `hi − lo = Θ(n)` are precisely
why the exponent is `Θ(n)` rather than A0's `Θ(log n)`. -/

/-- **Bridge to `epidemicTime_concentration_of_tail_bounds`.**  At `t = ⌈200·n⌉`
interactions the constant-density crossing fails with probability bounded by an
explicit exponential in `n`: `((199/200)^{200n})·2ⁿ`, whose exponent
`200·log(199/200) + log 2 < 0` is `< 0`, giving the `exp(−Θ(n))` upper tail that
discharges the `h_upper` hypothesis of the conditional concentration theorem at
the constant scale (`E = Θ(1)`, `pMin = c = Θ(1)`). -/
theorem constantDensity_O1_failure_exp (n : ℕ) (hn : 20 ≤ n)
    (c₀ : Config Bool) (hcard : c₀.card = n) (hinf : informed c₀ = lo n) :
    (epidemicProto.transitionKernel ^ (200 * n)) c₀ {c | informed c < hi n} ≤
      ENNReal.ofReal (Real.exp ((n : ℝ) *
        (200 * Real.log (199 / 200) + Real.log 2))) := by
  refine le_trans (constantDensity_epidemic_O1_parallel n hn c₀ hcard hinf (200 * n)) ?_
  apply ENNReal.ofReal_le_ofReal
  -- (199/200)^{200n}·2^{hi-lo} ≤ exp(n·(200·log(199/200) + log 2))
  have h2pos : (0 : ℝ) < (2 : ℝ) := by norm_num
  have hwidth : hi n - lo n ≤ n := by unfold hi lo; omega
  -- (199/200)^{200n} = exp(200n·log(199/200))
  have hr_eq : ((199 : ℝ) / 200) ^ (200 * n)
      = Real.exp (((200 * n : ℕ) : ℝ) * Real.log (199 / 200)) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0:ℝ) < 199/200)]
  -- 2^{hi-lo} ≤ 2^n = exp(n·log 2)
  have hpow_le : (2 : ℝ) ^ (hi n - lo n) ≤ (2 : ℝ) ^ n := by
    apply pow_le_pow_right₀ (by norm_num) hwidth
  have h2n_eq : (2 : ℝ) ^ n = Real.exp (((n : ℕ) : ℝ) * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0:ℝ) < 2)]
  have hlogneg : Real.log (199 / 200) < 0 := Real.log_neg (by norm_num) (by norm_num)
  calc ((199 : ℝ) / 200) ^ (200 * n) * (2 : ℝ) ^ (hi n - lo n)
      ≤ ((199 : ℝ) / 200) ^ (200 * n) * (2 : ℝ) ^ n := by
        apply mul_le_mul_of_nonneg_left hpow_le (by positivity)
    _ = Real.exp ((200 * n : ℕ) * Real.log (199 / 200)) *
          Real.exp ((n : ℕ) * Real.log 2) := by rw [hr_eq, h2n_eq]
    _ = Real.exp (((200 * n : ℕ) : ℝ) * Real.log (199 / 200) + (n : ℝ) * Real.log 2) := by
        rw [← Real.exp_add]
    _ = Real.exp ((n : ℝ) * (200 * Real.log (199 / 200) + Real.log 2)) := by
        congr 1; push_cast; ring

end ConstantDensity

end ExactMajority
