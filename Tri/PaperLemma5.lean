/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.DoubleBAssembly
import Tri.PaperLemma3
import Tri.Phase2CRN
import Tri.Phase3Productive

/-!
# Paper Lemma 5: raw clocks for productive-event budgets

This file contains only the clock conversion part of Lemma 5.  Directional
progress is supplied by Lemma 3 and Corollaries 1--3; the statements here bound
the mass of paths which have not left the relevant live region and have still
seen too few productive interactions by the displayed raw deadline.

The proofs use the adapted lower-tail engine on a stopped productive counter.
No independence of productive indicators is assumed.

## Scope, constants, and where they come from

Lemma 5 is a pure CLOCK lemma; the direction/drift content is Lemma 3 and Corollaries 1–3 and
is kept in separate files.  The productive probability for the tri-molecular model (uniform
unordered triple; productive iff the composition is `XXY` or `XYY`) is
`q(x,y) = 3xy/(n(n−1)) > 3xy/n²`.  A pair-style `2xy/n²` is WRONG for this model.

* **(i) is per phase-1 STAGE, not for the whole phase.**  Phase 1 has `Θ(lg n)` doubling
  stages, so the phase totals `O(n lg n)` raw interactions.  Band `n/2 < x < 7n/8` gives
  `xy > 7n²/64`, hence `q > 21/64`; with `p₁ = 21/64` and `r₁ = ⌈256n/21⌉` one gets
  `r₁p₁/2 ≥ 2n` and failure `≤ exp(−r₁p₁/8) ≤ exp(−n/2)`.  (The true phase boundary is
  sharper — `x − y < 2n/3` forces `x < 5n/6` and `q > 5/12` — but the paper does not exploit
  it and neither do we.)
* **(ii)** at stage `s`: before the lower endpoint `y > n/2^(s+1)`, so
  `p_s = 3(2^(s+1)−1)/2^(2s+2) ≥ 3/2^(s+2)`; with target `K_s = 3n/2^s`,
  `r_s = 2K_s/p_s = 4n·2^(s+1)/(2^(s+1)−1) ≤ 32n/7 < 4.572n` for every `s ≥ 2`, so the uniform
  budget `5n` works, with failure `exp(−3n/(4·2^s))`.
* **(iii)** while phase 3 is unfinished `y ≥ 1`, and under `γ lg n ≤ n/6` the band keeps
  `y < n/2`, so `xy ≥ n−1` and the EXACT floor is `q ≥ 3/n`, attained exactly at `y = 1`.
  With `K₃ = 3γ lg n` and `r₃ = 2γ n lg n`, failure `≤ exp(−3γ lg n/4)`.

## The formalization caveat that must not be skipped

The paper calls the productive indicators "independent trials".  They are NOT — they are
state-dependent.  The sound form, used here, is CONDITIONAL DOMINATION: while the process has
not stopped, each step's conditional productive probability is at least `p`, so the productive
count dominates `Bin(r,p)`; the event is stated as "not stopped AND count below target".  No
independence is assumed anywhere.

## Our own earlier mistake, recorded

An earlier audit of this repository claimed our phase-1 instances were WEAKER than printed
5(i) (a `Θ(γn)` horizon and a gap-scale envelope where the paper has `Θ(n)` and
`exp(−Ω(n))`).  That was a CLOCK-vs-DIRECTION conflation on our side, compounded by reading
5(i) as a whole-phase claim rather than a per-stage one.  It is not a defect of the paper.
-/

namespace Tri

open scoped ENNReal NNReal

variable {α : Type*}

/-! ## A stopped adapted lower-tail wrapper -/

/-- Multiplicative lower tail with the stopped event kept in the bad set.

This is the same scalar optimization as `adapted_multiplicative_lower_tail`,
but it starts from `count_tail_frozen`, so the event is exactly
`not stopped AND count ≤ k`. -/
theorem count_tail_frozen_multiplicative
    (K : α → PMF α) (B : α → Prop) [DecidablePred B] (count : α → ℕ)
    (s₀ : α) (p : ℝ≥0) (hp : p ≤ 1)
    (delta : ℝ) (hdelta0 : 0 ≤ delta) (hdelta1 : delta ≤ 1)
    (N k : ℕ)
    (hk :
      (k : ℝ) ≤
        (1 - delta) * ((N : ℝ) * (p : ℝ)))
    (hB₀ : ¬ B s₀)
    (hcount0 : count s₀ = 0)
    (hstep : ∀ s,
      expect (freeze B K s)
          (fun z => if B z then 0 else
            ENNReal.ofReal (Real.exp (-delta)) ^ count z) ≤
        (((1 - p : ℝ≥0) : ℝ≥0∞) +
            (p : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-delta))) *
          (if B s then 0 else
            ENNReal.ofReal (Real.exp (-delta)) ^ count s)) :
    (∑' z : α,
        (if count z ≤ k ∧ ¬ B z then iter (freeze B K) N s₀ z else 0)) ≤
      ENNReal.ofReal
        (Real.exp
          (-(delta ^ 2 * ((N : ℝ) * (p : ℝ))) / 2)) := by
  let w : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-delta))
  have hw1 : w ≤ 1 := by
    dsimp only [w]
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal <|
      Real.exp_le_one_iff.mpr (neg_nonpos.mpr hdelta0)
  have hw0 : w ≠ 0 := by
    dsimp only [w]
    exact ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos _)
  have hraw :=
    count_tail_frozen K B count w
      (((1 - p : ℝ≥0) : ℝ≥0∞) + (p : ℝ≥0∞) * w)
      hw1 hw0 (by simpa only [w] using hstep) N k s₀
  rw [if_neg hB₀, hcount0, pow_zero, mul_one] at hraw
  refine hraw.trans ?_
  have hp0R : 0 ≤ (p : ℝ) := p.2
  have hp1R : (p : ℝ) ≤ 1 := by exact_mod_cast hp
  have hp'0R : 0 ≤ ((1 - p : ℝ≥0) : ℝ) :=
    (1 - p : ℝ≥0).2
  have hsumR :
      (p : ℝ) + ((1 - p : ℝ≥0) : ℝ) = 1 := by
    rw [NNReal.coe_sub hp]
    exact add_tsub_cancel_of_le hp
  have hbase :
      (((1 - p : ℝ≥0) : ℝ≥0∞) + (p : ℝ≥0∞) * w) =
        ENNReal.ofReal
          (((1 - p : ℝ≥0) : ℝ) +
            (p : ℝ) * Real.exp (-delta)) := by
    dsimp only [w]
    rw [ENNReal.coe_nnreal_eq, ENNReal.coe_nnreal_eq,
      ← ENNReal.ofReal_mul hp0R,
      ← ENNReal.ofReal_add hp'0R
        (mul_nonneg hp0R (Real.exp_nonneg _))]
  rw [hbase,
    ← ENNReal.ofReal_pow
      (add_nonneg hp'0R
        (mul_nonneg hp0R (Real.exp_nonneg _))),
    ← ENNReal.ofReal_pow (Real.exp_nonneg _),
    ← ENNReal.ofReal_div_of_pos (pow_pos (Real.exp_pos _) k)]
  exact ENNReal.ofReal_le_ofReal <|
    bernoulli_multiplicative_lower_ratio
      hp0R hp1R hsumR hdelta0 hdelta1 N k hk

/-- A stopped `triCount` step satisfies a Bernoulli lower-tail moment bound
whenever the live region has a productive-mass floor `p`. -/
theorem triClockStop_count_moment
    (n : ℕ) (h3 : 3 ≤ n)
    (B : ℕ × ℕ → Prop) [DecidablePred B]
    (p : ℝ≥0) (hp : p ≤ 1) (w : ℝ≥0∞) (hw : w ≤ 1)
    (hlive : ∀ x c, ¬ B (x, c) →
      ∃ a b : ℕ, x = a + 1 ∧ a + b + 2 = n)
    (hprod : ∀ a b c, (hpop : a + b + 2 = n) → ¬ B (a + 1, c) →
      (p : ℝ≥0∞) ≤
        triStep (a + 1) (b + 1) (by omega) a +
          triStep (a + 1) (b + 1) (by omega) (a + 2)) :
    ∀ q,
      expect (freeze B (triCount n) q)
          (fun z => if B z then 0 else w ^ z.2) ≤
        (((1 - p : ℝ≥0) : ℝ≥0∞) + (p : ℝ≥0∞) * w) *
          (if B q then 0 else w ^ q.2) := by
  intro q
  have hpSum :
      (p : ℝ≥0∞) + ((1 - p : ℝ≥0) : ℝ≥0∞) = 1 := by
    have hnn : p + (1 - p) = (1 : ℝ≥0) :=
      add_tsub_cancel_of_le hp
    exact_mod_cast hnn
  by_cases hB : B q
  · rw [freeze_of_mem q hB, expect_pure]
    simp [hB]
  · rw [freeze_of_not_mem q hB, if_neg hB]
    obtain ⟨a, b, hx, hpop⟩ := hlive q.1 q.2 hB
    rcases q with ⟨x, c⟩
    simp only at hx
    subst x
    calc
      expect (triCount n (a + 1, c))
          (fun z => if B z then 0 else w ^ z.2) ≤
        expect (triCount n (a + 1, c)) (fun z => w ^ z.2) := by
          unfold expect
          exact ENNReal.tsum_le_tsum fun z =>
            mul_le_mul_right (by
              by_cases hz : B z <;> simp [hz]) _
      _ ≤ (((1 - p : ℝ≥0) : ℝ≥0∞) + (p : ℝ≥0∞) * w) * w ^ c := by
        simpa [add_comm] using
          triCount_step_of_productive_lower
            (n := n) (a := a) (b := b) (c := c) (w := w)
            (p := (p : ℝ≥0∞))
            (p' := ((1 - p : ℝ≥0) : ℝ≥0∞))
            hpop h3 hpSum hw (hprod a b c hpop hB)

/-- Generic stopped clock tail for `triCount`. -/
theorem triClockStop_tail
    (n : ℕ) (h3 : 3 ≤ n)
    (B : ℕ × ℕ → Prop) [DecidablePred B]
    (x₀ : ℕ) (p : ℝ≥0) (hp : p ≤ 1)
    (delta : ℝ) (hdelta0 : 0 ≤ delta) (hdelta1 : delta ≤ 1)
    (N k : ℕ)
    (hk :
      (k : ℝ) ≤
        (1 - delta) * ((N : ℝ) * (p : ℝ)))
    (hB₀ : ¬ B (x₀, 0))
    (hlive : ∀ x c, ¬ B (x, c) →
      ∃ a b : ℕ, x = a + 1 ∧ a + b + 2 = n)
    (hprod : ∀ a b c, (hpop : a + b + 2 = n) → ¬ B (a + 1, c) →
      (p : ℝ≥0∞) ≤
        triStep (a + 1) (b + 1) (by omega) a +
          triStep (a + 1) (b + 1) (by omega) (a + 2)) :
    (∑' q : ℕ × ℕ,
        (if q.2 ≤ k ∧ ¬ B q then
          iter (freeze B (triCount n)) N (x₀, 0) q else 0)) ≤
      ENNReal.ofReal
        (Real.exp
          (-(delta ^ 2 * ((N : ℝ) * (p : ℝ))) / 2)) := by
  exact count_tail_frozen_multiplicative
    (triCount n) B Prod.snd (x₀, 0) p hp delta hdelta0 hdelta1 N k hk
    hB₀ rfl
    (triClockStop_count_moment n h3 B p hp
      (ENNReal.ofReal (Real.exp (-delta)))
      (by
        rw [← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal <|
          Real.exp_le_one_iff.mpr (neg_nonpos.mpr hdelta0))
      hlive hprod)

/-! ## The three paper live regions and constants -/

/-- Raw deadline `⌈256n/21⌉` from Lemma 5(i). -/
def lemma5Phase1RawDeadline (n : ℕ) : ℕ :=
  (256 * n + 20) / 21

/-- Phase-1 stage live band, in the form used by the clock lemma. -/
def Lemma5Phase1Stop (n : ℕ) (q : ℕ × ℕ) : Prop :=
  ¬ (n < 2 * q.1 ∧ 8 * q.1 < 7 * n)

instance lemma5Phase1StopDecidable (n : ℕ) :
    DecidablePred (Lemma5Phase1Stop n) := by
  intro q
  unfold Lemma5Phase1Stop
  infer_instance

/-- Phase-2 stage live band for the clock comparison.  The `n - x` term is
confined to this definition; public theorem statements refer to the named
predicate. -/
def Lemma5Phase2Stop (n s : ℕ) (q : ℕ × ℕ) : Prop :=
  ¬ (q.1 ≤ n ∧ 2 * q.1 ≥ n ∧ 2 ^ (s + 1) * (n - q.1) > n)

instance lemma5Phase2StopDecidable (n s : ℕ) :
    DecidablePred (Lemma5Phase2Stop n s) := by
  intro q
  unfold Lemma5Phase2Stop
  infer_instance

/-- Phase-3 live region for the clock comparison: every mixed physical state. -/
def Lemma5Phase3Stop (n : ℕ) (q : ℕ × ℕ) : Prop :=
  ¬ (q.1 ≤ n ∧ 0 < q.1 ∧ q.1 < n)

instance lemma5Phase3StopDecidable (n : ℕ) :
    DecidablePred (Lemma5Phase3Stop n) := by
  intro q
  unfold Lemma5Phase3Stop
  infer_instance

/-- Productive floor for Lemma 5(i), `21/64`. -/
noncomputable def lemma5Phase1P : ℝ≥0 :=
  (21 : ℝ≥0) / 64

theorem lemma5Phase1P_coe_ennreal :
    (lemma5Phase1P : ℝ≥0∞) = (21 : ℝ≥0∞) / 64 := by
  unfold lemma5Phase1P
  rw [ENNReal.coe_nnreal_eq, NNReal.coe_div]
  rw [ENNReal.ofReal_div_of_pos (by norm_num)]
  norm_num

theorem lemma5Phase1P_le_one : lemma5Phase1P ≤ 1 := by
  unfold lemma5Phase1P
  rw [div_le_one]
  · norm_num
  · norm_num

/-- Productive floor for Lemma 5(ii),
`3(2^(s+1)-1)/2^(2s+2)`. -/
noncomputable def lemma5Phase2P (s : ℕ) : ℝ≥0 :=
  ((3 * (2 ^ (s + 1) - 1 : ℕ) : ℕ) : ℝ≥0) /
    (((2 ^ (2 * s + 2) : ℕ) : ℝ≥0))

theorem lemma5Phase2P_coe_real (s : ℕ) :
    (lemma5Phase2P s : ℝ) =
      (3 * (((2 ^ (s + 1) : ℕ) : ℝ) - 1)) /
        (((2 ^ (2 * s + 2) : ℕ) : ℝ)) := by
  unfold lemma5Phase2P
  have hpow : 1 ≤ 2 ^ (s + 1) :=
    Nat.succ_le_iff.mpr (pow_pos (by norm_num : (0 : ℕ) < 2) (s + 1))
  rw [NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_natCast,
    Nat.cast_mul, Nat.cast_sub hpow]
  ring

theorem lemma5Phase2P_le_one {s : ℕ} (hs : 2 ≤ s) :
    lemma5Phase2P s ≤ 1 := by
  unfold lemma5Phase2P
  rw [div_le_one]
  · exact_mod_cast (by
      let k : ℕ := 2 ^ (s + 1)
      have hk : 8 ≤ k := by
        dsimp [k]
        calc
          8 = 2 ^ 3 := by norm_num
          _ ≤ 2 ^ (s + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hsq : 3 * (k - 1) ≤ k * k := by
        have h3k : 3 ≤ k := by omega
        calc
          3 * (k - 1) ≤ k * (k - 1) := Nat.mul_le_mul_right _ h3k
          _ ≤ k * k := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      have hkpow : k * k = 2 ^ (2 * s + 2) := by
        dsimp [k]
        rw [← pow_add]
        congr 1
        omega
      calc
        3 * (2 ^ (s + 1) - 1) = 3 * (k - 1) := rfl
        _ ≤ k * k := hsq
        _ = 2 ^ (2 * s + 2) := hkpow)
  · exact_mod_cast (show 0 < 2 ^ (2 * s + 2) by positivity)

/-- Productive floor for Lemma 5(iii), `3/n`. -/
noncomputable def lemma5Phase3P (n : ℕ) : ℝ≥0 :=
  (3 : ℝ≥0) / n

theorem lemma5Phase3P_coe_ennreal {n : ℕ} (hn : 0 < n) :
    (lemma5Phase3P n : ℝ≥0∞) = (3 : ℝ≥0∞) / n := by
  unfold lemma5Phase3P
  rw [ENNReal.coe_nnreal_eq, NNReal.coe_div]
  rw [ENNReal.ofReal_div_of_pos (by exact_mod_cast hn)]
  norm_num

theorem lemma5Phase3P_le_one {n : ℕ} (h3 : 3 ≤ n) :
    lemma5Phase3P n ≤ 1 := by
  unfold lemma5Phase3P
  rw [div_le_one]
  · exact_mod_cast h3
  · exact_mod_cast (show 0 < n by omega)

/-! ## Productive-mass floors for the three live regions -/

theorem lemma5_phase1_live
    {n x c : ℕ} (h3 : 3 ≤ n)
    (h : ¬ Lemma5Phase1Stop n (x, c)) :
    ∃ a b : ℕ, x = a + 1 ∧ a + b + 2 = n := by
  unfold Lemma5Phase1Stop at h
  push Not at h
  obtain ⟨hlo, hhi⟩ := h
  refine ⟨x - 1, n - x - 1, ?_, ?_⟩ <;> omega

theorem lemma5_phase1_productive_floor
    {n a b c : ℕ} (h3 : 3 ≤ n) (hpop : a + b + 2 = n)
    (h : ¬ Lemma5Phase1Stop n (a + 1, c)) :
    (lemma5Phase1P : ℝ≥0∞) ≤
      triStep (a + 1) (b + 1) (by omega) a +
        triStep (a + 1) (b + 1) (by omega) (a + 2) := by
  unfold Lemma5Phase1Stop at h
  push Not at h
  rw [lemma5Phase1P_coe_ennreal]
  exact hprod_phase1 a b n h3 hpop h.1 h.2

theorem lemma5_phase2_live
    {n s x c : ℕ} (h3 : 3 ≤ n)
    (h : ¬ Lemma5Phase2Stop n s (x, c)) :
    ∃ a b : ℕ, x = a + 1 ∧ a + b + 2 = n := by
  unfold Lemma5Phase2Stop at h
  push Not at h
  obtain ⟨hxn, _hmajor, hstage⟩ := h
  have hx0 : 0 < x := by omega
  have hnxpos : 0 < n - x := by
    by_contra hnot
    have hzero : n - x = 0 := Nat.eq_zero_of_not_pos hnot
    rw [hzero] at hstage
    omega
  refine ⟨x - 1, n - x - 1, ?_, ?_⟩ <;> omega

theorem lemma5_phase2_productive_floor
    {n s a b c : ℕ} (h3 : 3 ≤ n) (_hs : 2 ≤ s)
    (hpop : a + b + 2 = n)
    (h : ¬ Lemma5Phase2Stop n s (a + 1, c)) :
    (lemma5Phase2P s : ℝ≥0∞) ≤
      triStep (a + 1) (b + 1) (by omega) a +
        triStep (a + 1) (b + 1) (by omega) (a + 2) := by
  unfold Lemma5Phase2Stop at h
  push Not at h
  obtain ⟨_hxn, hmajor, hstageX⟩ := h
  have hstage : 2 ^ (s + 1) * (b + 1) > n := by
    have hxsub : n - (a + 1) = b + 1 := by omega
    simpa [hxsub] using hstageX
  rw [productive_mass_closed a b n h3 hpop]
  rw [← ENNReal.toReal_le_toReal (by finiteness) (by finiteness)]
  rw [ENNReal.coe_toReal, ENNReal.toReal_div,
    ENNReal.toReal_natCast, ENNReal.toReal_natCast]
  rw [lemma5Phase2P_coe_real]
  have hxy := xy_ge_phase2 hstage
    (by omega : (a + 1) + (b + 1) = n) hmajor
  rw [show 2 * s + 2 = (s + 1) + (s + 1) by omega, pow_add] at hxy
  let k : ℕ := 2 ^ (s + 1)
  change k * k * ((a + 1) * (b + 1)) + n * n > k * n * n at hxy
  have hknat : 2 ^ (2 * s + 2) = k * k := by
    dsimp [k]
    rw [← pow_add]
    congr 1
    omega
  have hkpos : (0 : ℝ) < (k : ℝ) := by positivity
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hdenpos : (0 : ℝ) < (n : ℝ) * (((a + b + 1 : ℕ) : ℝ)) := by
    positivity
  rw [hknat]
  rw [show (((2 ^ (s + 1) : ℕ) : ℝ) = (k : ℝ)) by rfl]
  norm_num only [Nat.cast_mul]
  rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < (k : ℝ) * (k : ℝ)) hdenpos]
  have hk_one : 1 ≤ k :=
    Nat.succ_le_iff.mpr (pow_pos (by norm_num : (0 : ℕ) < 2) (s + 1))
  have hkm1R : (k : ℝ) - 1 = ((k - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hk_one]
    ring
  rw [hkm1R]
  have hxyR :
      ((k : ℝ) * (k : ℝ)) * (((a + 1) * (b + 1) : ℕ) : ℝ) >
        ((k - 1 : ℕ) : ℝ) * (n : ℝ) * (n : ℝ) := by
    have hxyR0 :
        (k : ℝ) * (k : ℝ) * (((a + 1) * (b + 1) : ℕ) : ℝ) +
          (n : ℝ) * (n : ℝ) > (k : ℝ) * (n : ℝ) * (n : ℝ) := by
      exact_mod_cast hxy
    rw [← hkm1R]
    nlinarith
  have hnle : (n : ℝ) * (((a + b + 1 : ℕ) : ℝ)) ≤ (n : ℝ) * (n : ℝ) := by
    nlinarith [show (((a + b + 1 : ℕ) : ℝ)) ≤ n by
      exact_mod_cast (by omega : a + b + 1 ≤ n)]
  have hcalc :
      (3 * ((k - 1 : ℕ) : ℝ)) *
          ((n : ℝ) * (((a + b + 1 : ℕ) : ℝ))) ≤
        (3 * (((a + 1) * (b + 1) : ℕ) : ℝ)) *
          ((k : ℝ) * (k : ℝ)) := by
    calc
      (3 * ((k - 1 : ℕ) : ℝ)) * ((n : ℝ) * (((a + b + 1 : ℕ) : ℝ)))
          ≤ (3 : ℝ) * (((k - 1 : ℕ) : ℝ) * ((n : ℝ) * (n : ℝ))) := by
            nlinarith
      _ ≤ (3 * (((a + 1) * (b + 1) : ℕ) : ℝ)) *
          ((k : ℝ) * (k : ℝ)) := by
            nlinarith
  simpa only [Nat.cast_mul] using hcalc

theorem lemma5_phase3_live
    {n x c : ℕ} (h : ¬ Lemma5Phase3Stop n (x, c)) :
    ∃ a b : ℕ, x = a + 1 ∧ a + b + 2 = n := by
  unfold Lemma5Phase3Stop at h
  push Not at h
  obtain ⟨hxn, hx0, hxnlt⟩ := h
  refine ⟨x - 1, n - x - 1, ?_, ?_⟩ <;> omega

theorem lemma5_phase3_productive_floor
    {n a b c : ℕ} (h3 : 3 ≤ n)
    (hpop : a + b + 2 = n)
    (_h : ¬ Lemma5Phase3Stop n (a + 1, c)) :
    (lemma5Phase3P n : ℝ≥0∞) ≤
      triStep (a + 1) (b + 1) (by omega) a +
        triStep (a + 1) (b + 1) (by omega) (a + 2) := by
  rw [lemma5Phase3P_coe_ennreal (by omega : 0 < n)]
  exact productive_mass_ge_interior a b n h3 hpop

/-! ## Paper-strength clock instances -/

/-- Lemma 5(i), per phase-1 stage: within `⌈256n/21⌉` raw interactions,
paths still inside the stage live band but with at most `2n` productive
interactions have mass at most `exp(-n/2)`. -/
theorem lemma5_i_paper (n x₀ : ℕ) (h3 : 3 ≤ n)
    (hstart : ¬ Lemma5Phase1Stop n (x₀, 0)) :
    (∑' q : ℕ × ℕ,
        (if q.2 ≤ 2 * n ∧ ¬ Lemma5Phase1Stop n q then
          iter (freeze (Lemma5Phase1Stop n) (triCount n))
            (lemma5Phase1RawDeadline n) (x₀, 0) q else 0)) ≤
      ENNReal.ofReal (Real.exp (-(n : ℝ) / 2)) := by
  have hceil : 256 * n ≤ 21 * lemma5Phase1RawDeadline n := by
    unfold lemma5Phase1RawDeadline
    omega
  have hk :
      ((2 * n : ℕ) : ℝ) ≤
        (1 - (1 / 2 : ℝ)) *
          (((lemma5Phase1RawDeadline n : ℕ) : ℝ) *
            (lemma5Phase1P : ℝ)) := by
    unfold lemma5Phase1P
    have hceilR : (256 * n : ℝ) ≤ 21 * (lemma5Phase1RawDeadline n : ℝ) := by
      exact_mod_cast hceil
    norm_num at *
    nlinarith
  have htail := triClockStop_tail n h3 (Lemma5Phase1Stop n) x₀
    lemma5Phase1P lemma5Phase1P_le_one (1 / 2) (by norm_num) (by norm_num)
    (lemma5Phase1RawDeadline n) (2 * n) hk hstart
    (fun x c h => lemma5_phase1_live (n := n) (x := x) (c := c) h3 h)
    (fun a b c hpop h =>
      lemma5_phase1_productive_floor (n := n) (a := a) (b := b) (c := c)
        h3 hpop h)
  refine htail.trans ?_
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  unfold lemma5Phase1P
  have hmu : (4 * (n : ℝ)) ≤
      (lemma5Phase1RawDeadline n : ℝ) * (21 / 64 : ℝ) := by
    have hceilR : (256 * n : ℝ) ≤ 21 * (lemma5Phase1RawDeadline n : ℝ) := by
      exact_mod_cast hceil
    nlinarith
  norm_num
  nlinarith

/-- Lemma 5(ii), stage `s` of phase 2: a uniform `5n` raw budget supplies the
paper's `3n/2^s` productive budget with failure `exp(-3n/(4·2^s))`. -/
theorem lemma5_ii_paper (n s x₀ : ℕ) (h3 : 3 ≤ n) (hs : 2 ≤ s)
    (hstart : ¬ Lemma5Phase2Stop n s (x₀, 0)) :
    (∑' q : ℕ × ℕ,
        (if q.2 ≤ (3 * n) / 2 ^ s ∧ ¬ Lemma5Phase2Stop n s q then
          iter (freeze (Lemma5Phase2Stop n s) (triCount n))
            (5 * n) (x₀, 0) q else 0)) ≤
      ENNReal.ofReal (Real.exp (-((3 * n : ℕ) : ℝ) / (4 * (2 ^ s : ℕ)))) := by
  have hk :
      (((3 * n) / 2 ^ s : ℕ) : ℝ) ≤
        (1 - (1 / 2 : ℝ)) *
          (((5 * n : ℕ) : ℝ) * (lemma5Phase2P s : ℝ)) := by
    let k : ℕ := 2 ^ (s + 1)
    have hkpow : 2 ^ (2 * s + 2) = k * k := by
      dsimp [k]
      rw [← pow_add]
      congr 1
      omega
    have hkge : 15 ≤ 6 * (2 ^ s : ℕ) := by
      have : 4 ≤ 2 ^ s := by
        calc
          4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) hs
      omega
    have hdiv : (((3 * n) / 2 ^ s : ℕ) : ℝ) ≤ (3 * n : ℝ) / (2 ^ s : ℕ) := by
      have hpos : (0 : ℝ) < (2 ^ s : ℕ) := by positivity
      rw [le_div_iff₀ hpos]
      have hnat : ((3 * n) / 2 ^ s) * 2 ^ s ≤ 3 * n :=
        Nat.div_mul_le_self (3 * n) (2 ^ s)
      exact_mod_cast hnat
    have hpos2 : (0 : ℝ) < (2 ^ s : ℕ) := by positivity
    rw [lemma5Phase2P_coe_real]
    rw [hkpow]
    rw [show (((2 ^ (s + 1) : ℕ) : ℝ) = (k : ℝ)) by rfl]
    norm_num only [Nat.cast_mul]
    have hmain :
        (3 * (n : ℝ)) / (2 ^ s : ℕ) ≤
          (1 / 2) * ((5 * (n : ℝ)) *
            ((3 * ((k : ℝ) - 1)) / ((k : ℝ) * (k : ℝ)))) := by
      have hkR : (15 : ℝ) ≤ 6 * (2 ^ s : ℕ) := by exact_mod_cast hkge
      have hkdef : (k : ℝ) = 2 * (2 ^ s : ℕ) := by
        dsimp [k]
        rw [pow_succ, Nat.cast_mul]
        ring
      rw [hkdef]
      field_simp [hpos2.ne']
      nlinarith
    exact hdiv.trans hmain
  have htail := triClockStop_tail n h3 (Lemma5Phase2Stop n s) x₀
    (lemma5Phase2P s) (lemma5Phase2P_le_one hs) (1 / 2)
    (by norm_num) (by norm_num) (5 * n) ((3 * n) / 2 ^ s) hk
    hstart
    (fun x c h => lemma5_phase2_live (n := n) (s := s) (x := x) (c := c) h3 h)
    (fun a b c hpop h =>
      lemma5_phase2_productive_floor (n := n) (s := s) (a := a) (b := b) (c := c)
        h3 hs hpop h)
  refine htail.trans ?_
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  rw [lemma5Phase2P_coe_real]
  let k : ℕ := 2 ^ (s + 1)
  have hkpow : 2 ^ (2 * s + 2) = k * k := by
    dsimp [k]
    rw [← pow_add]
    congr 1
    omega
  rw [hkpow]
  rw [show (((2 ^ (s + 1) : ℕ) : ℝ) = (k : ℝ)) by rfl]
  norm_num only [Nat.cast_mul]
  have hkdef : (k : ℝ) = 2 * (2 ^ s : ℕ) := by
    dsimp [k]
    rw [pow_succ, Nat.cast_mul]
    ring
  rw [hkdef]
  field_simp
  nlinarith [show (15 : ℝ) ≤ 6 * (2 ^ s : ℕ) by
    exact_mod_cast (by
      have : 4 ≤ 2 ^ s := by
        calc
          4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) hs
      omega)]

/-- Lemma 5(iii), whole phase 3: `2γ n lg n` raw interactions supply
`3γ lg n` productive interactions with failure `exp(-3γ lg n/4)`. -/
theorem lemma5_iii_paper (n γ x₀ : ℕ) (h3 : 3 ≤ n)
    (hstart : ¬ Lemma5Phase3Stop n (x₀, 0)) :
    (∑' q : ℕ × ℕ,
        (if q.2 ≤ 3 * γ * Nat.log 2 n ∧ ¬ Lemma5Phase3Stop n q then
          iter (freeze (Lemma5Phase3Stop n) (triCount n))
            (2 * γ * n * Nat.log 2 n) (x₀, 0) q else 0)) ≤
      ENNReal.ofReal
        (Real.exp (-((3 * γ * Nat.log 2 n : ℕ) : ℝ) / 4)) := by
  have hk :
      ((3 * γ * Nat.log 2 n : ℕ) : ℝ) ≤
        (1 - (1 / 2 : ℝ)) *
          (((2 * γ * n * Nat.log 2 n : ℕ) : ℝ) *
            (lemma5Phase3P n : ℝ)) := by
    unfold lemma5Phase3P
    have hnpos : (0 : ℝ) < (n : ℕ) := by exact_mod_cast (show 0 < n by omega)
    change ((3 * γ * Nat.log 2 n : ℕ) : ℝ) ≤
      (1 - (1 / 2 : ℝ)) *
        (((2 * γ * n * Nat.log 2 n : ℕ) : ℝ) * ((3 : ℝ) / n))
    field_simp [hnpos.ne']
    norm_num only [Nat.cast_mul]
    ring_nf
    rfl
  have htail := triClockStop_tail n h3 (Lemma5Phase3Stop n) x₀
    (lemma5Phase3P n) (lemma5Phase3P_le_one h3) (1 / 2)
    (by norm_num) (by norm_num)
    (2 * γ * n * Nat.log 2 n) (3 * γ * Nat.log 2 n) hk hstart
    (fun x c h => lemma5_phase3_live (n := n) (x := x) (c := c) h)
    (fun a b c hpop h =>
      lemma5_phase3_productive_floor (n := n) (a := a) (b := b) (c := c)
        h3 hpop h)
  refine htail.trans ?_
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  unfold lemma5Phase3P
  have hnpos : (0 : ℝ) < (n : ℕ) := by exact_mod_cast (show 0 < n by omega)
  change -((1 / 2 : ℝ) ^ 2 *
      (((2 * γ * n * Nat.log 2 n : ℕ) : ℝ) * ((3 : ℝ) / n))) / 2
    ≤ -((3 * γ * Nat.log 2 n : ℕ) : ℝ) / 4
  field_simp [hnpos.ne']
  norm_num only [Nat.cast_mul]
  ring_nf
  rfl

/-- Combined paper Lemma 5 clock package. -/
theorem lemma5_paper (n γ s x₁ x₂ x₃ : ℕ)
    (h3 : 3 ≤ n) (hs : 2 ≤ s)
    (h₁ : ¬ Lemma5Phase1Stop n (x₁, 0))
    (h₂ : ¬ Lemma5Phase2Stop n s (x₂, 0))
    (h₃ : ¬ Lemma5Phase3Stop n (x₃, 0)) :
    (∑' q : ℕ × ℕ,
        (if q.2 ≤ 2 * n ∧ ¬ Lemma5Phase1Stop n q then
          iter (freeze (Lemma5Phase1Stop n) (triCount n))
            (lemma5Phase1RawDeadline n) (x₁, 0) q else 0)) ≤
      ENNReal.ofReal (Real.exp (-(n : ℝ) / 2)) ∧
    (∑' q : ℕ × ℕ,
        (if q.2 ≤ (3 * n) / 2 ^ s ∧ ¬ Lemma5Phase2Stop n s q then
          iter (freeze (Lemma5Phase2Stop n s) (triCount n))
            (5 * n) (x₂, 0) q else 0)) ≤
      ENNReal.ofReal (Real.exp (-((3 * n : ℕ) : ℝ) / (4 * (2 ^ s : ℕ)))) ∧
    (∑' q : ℕ × ℕ,
        (if q.2 ≤ 3 * γ * Nat.log 2 n ∧ ¬ Lemma5Phase3Stop n q then
          iter (freeze (Lemma5Phase3Stop n) (triCount n))
            (2 * γ * n * Nat.log 2 n) (x₃, 0) q else 0)) ≤
      ENNReal.ofReal
        (Real.exp (-((3 * γ * Nat.log 2 n : ℕ) : ℝ) / 4)) := by
  exact ⟨lemma5_i_paper n x₁ h3 h₁,
    lemma5_ii_paper n s x₂ h3 hs h₂,
    lemma5_iii_paper n γ x₃ h3 h₃⟩

/-! ## Inhabitation checks for the conditional statements -/

example : ¬ Lemma5Phase1Stop 8 (5, 0) := by
  unfold Lemma5Phase1Stop
  omega

example : ¬ Lemma5Phase2Stop 16 2 (12, 0) := by
  unfold Lemma5Phase2Stop
  omega

example : ¬ Lemma5Phase3Stop 8 (7, 0) := by
  unfold Lemma5Phase3Stop
  omega

end Tri

#print axioms Tri.count_tail_frozen_multiplicative
#print axioms Tri.triClockStop_count_moment
#print axioms Tri.triClockStop_tail
#print axioms Tri.lemma5_phase1_productive_floor
#print axioms Tri.lemma5_phase2_productive_floor
#print axioms Tri.lemma5_phase3_productive_floor
#print axioms Tri.lemma5_i_paper
#print axioms Tri.lemma5_ii_paper
#print axioms Tri.lemma5_iii_paper
#print axioms Tri.lemma5_paper
