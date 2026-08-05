/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.PaperLemma3
import Tri.PaperLemma7

/-!
# Paper Lemma 6: unequal-rate gap doubling in productive-event time

This file proves the productive-clock version of the paper's unequal-rate
gap-doubling claim.  The rate premise is carried without subtraction as
`α + Δ/(2n) ≥ 1`; on the live half-gap band it gives the conditioned productive
up probability floor used by the adapted Chernoff deadline.

## Constants, and where they come from

* `5 * n` productive events is the paper's own budget and is GENUINE — it hides no
  dependence on the rate parameter.  At the extreme permitted rate `α = 1 − Δ/(2n)`, with
  `β₀ = 1 + Δ/(2n)`, every productive step still has success probability
  `p ≥ β₀/(β₀+1) = 1/2 + Δ/(2(4n+Δ)) ≥ 1/2 + Δ/(10n)`, so over `5n` steps the mean success
  count is `≥ 5n/2 + Δ/2` while gaining `Δ` (each step moving the gap by `±2`) needs only
  `5n/2 + Δ/4` — a margin of exactly `Δ/4`, which is the paper's own.
* The envelope `2 exp(−Δ²/(96n))` is weaker than what the argument can give
  (`2 exp(−Δ²/(40n))` from the deadline branch `exp(−Δ²/(40n))` and the barrier branch
  `(2n/(2n+Δ))^(Δ/4) ≤ exp(−Δ²/(12n))`).  Both are `exp(−Θ(Δ²/n))`, which is what the paper
  claims; `96` is simply the constant this proof route carries.

## Deviations from the printed lemma (see ERRATA.tex)

* **Threshold wording.**  The paper says the gap "increases to `min{2Δ, n}`".  Read as an
  equality that is unreachable: all reachable gaps share the parity of `n` and productive
  reactions move the gap by `2`, so for odd `n` with `2Δ < n` the even target `2Δ` cannot be
  hit (witness `n = 9`, `(x,y) = (5,4)`, `Δ = 1`; reachable gaps are `{1,3,5,7,9}`).  We
  formalize the proof-supported form `≥ min(2Δ, n)`.
* **The rate premise is an INTERVAL condition, not an initial-state one.**  Section 5 allows
  a non-constant rate, so the proof needs `α_t ≥ 1 − Δ/(2n)` at every productive step before
  `τ₊ ∧ τ₋`; an initial-state-only hypothesis is insufficient (one could satisfy it at time
  zero and then set `α_t = 0`).
* **"Independent trials" is not literally true.**  The success probabilities depend on the
  evolving state.  The repair, which changes no constant, is to couple each adapted success
  indicator from below with an i.i.d. Bernoulli at the displayed lower probability, stopped
  at `τ₊ ∧ τ₋`.  This file works with the stopped conditioned trace directly.

## The route NOT to take (verified, do not retry)

There is no uniform `O(n)` RAW-interaction version of this lemma over its full printed range.
The unequal-rate productive probability is `q_α(x,y) ≥ α·3xy/(n(n−1))`, and before consensus
`xy ≥ n−1`, so `q_α ≥ 3α/n` — which is TIGHT: at `y = 1`, `q_α(n−1,1) = 3α/n` exactly.  The
floor is therefore `Θ(1/n)` and converting `5n` productive events to raw time needs
`Θ(n²)` interactions.  A raw-time wrapper is only valid under a stopping hypothesis that
restores a constant floor — e.g. the Byzantine ladder's `gap ≤ n/2` regime, where
`xy ≥ 3n²/16` and `α ≥ 3/4` give `q_α > 27/64`, and `5n` productive events do convert to
`O(n)` raw with `exp(−Ω(n))` clock failure.  That stopped form is what Theorem 4's Phase I
consumes.

## What the proof actually establishes (stronger than the displayed conclusion)

With `G_t` the gap in productive-event time, `τ₊ = inf{t : G_t ≥ min(2Δ,n)}` and
`τ₋ = inf{t : G_t < Δ/2}`, the argument gives the STOPPED event `τ₊ ≤ 5n ∧ τ₊ < τ₋`.  The
no-downcrossing half is not cosmetic: paper Lemma 9's rate bound in the Byzantine application
is valid only while the gap stays above the stage's half-gap barrier, so a stage theorem must
return the hit state together with that history.
-/

namespace Tri

open scoped ENNReal NNReal

/-- Paper Lemma 6's local bias parameter `1 + Δ/(2n)`. -/
noncomputable def lemma6Beta (n Δ : ℕ) : NNReal :=
  1 + (((Δ : ℕ) : NNReal) / (((2 * n : ℕ) : NNReal)))

/-- Uniform productive-up probability floor `1/2 + Δ/(10n)`. -/
noncomputable def lemma6SuccessP (n Δ : ℕ) : NNReal :=
  (((5 * n + Δ : ℕ) : NNReal) / (((10 * n : ℕ) : NNReal)))

/-- Harmonic safety base, equal to `lemma6Beta n Δ` inverted. -/
noncomputable def lemma6SafetyBase (n Δ : ℕ) : ℝ≥0∞ :=
  (((2 * n : ℕ) : ℝ≥0∞) / (((2 * n + Δ : ℕ) : ℝ≥0∞)))

/-- Multiplicative Chernoff deviation for the `5n` productive deadline. -/
noncomputable def lemma6ChernoffDelta (n Δ : ℕ) : ℝ :=
  (Δ : ℝ) / (10 * (n : ℝ) + 2 * (Δ : ℝ))

/-- Largest low-success count that still misses the doubled-gap target. -/
def lemma6SuccessCutoff (n Δ : ℕ) : ℕ :=
  (10 * n + Δ + 3) / 4 - 1

/-- Real coercion of the bias parameter. -/
theorem lemma6Beta_coe (n Δ : ℕ) :
    (lemma6Beta n Δ : ℝ) =
      1 + (Δ : ℝ) / ((2 * n : ℕ) : ℝ) := by
  unfold lemma6Beta
  simp [NNReal.coe_div]

/-- Real coercion of the success floor. -/
theorem lemma6SuccessP_coe (n Δ : ℕ) :
    (lemma6SuccessP n Δ : ℝ) =
      ((5 * n + Δ : ℕ) : ℝ) / (((10 * n : ℕ) : ℝ)) := by
  unfold lemma6SuccessP
  simp [NNReal.coe_div]

theorem lemma6Beta_ge_one (n Δ : ℕ) :
    (1 : NNReal) ≤ lemma6Beta n Δ := by
  unfold lemma6Beta
  exact le_add_right le_rfl

theorem lemma6Beta_pos (n Δ : ℕ) :
    (0 : NNReal) < lemma6Beta n Δ :=
  lt_of_lt_of_le zero_lt_one (lemma6Beta_ge_one n Δ)

theorem lemma6SafetyBase_eq_beta_inv
    {n Δ : ℕ} (hn : 0 < n) :
    lemma6SafetyBase n Δ = ((lemma6Beta n Δ : ℝ≥0∞)⁻¹) := by
  unfold lemma6SafetyBase
  unfold lemma6Beta
  rw [ENNReal.coe_add]
  rw [ENNReal.coe_div]
  swap
  · exact_mod_cast (show (2 * n : ℕ) ≠ 0 by omega)
  have hadd :
      (((2 * n + Δ : ℕ) : ℝ≥0∞)) =
        ((2 * n : ℕ) : ℝ≥0∞) + (Δ : ℝ≥0∞) := by
    exact_mod_cast (show 2 * n + Δ = 2 * n + Δ by rfl)
  rw [hadd]
  norm_num only [ENNReal.coe_one]
  let D : ℝ≥0∞ := ((2 * n : ℕ) : ℝ≥0∞)
  let E : ℝ≥0∞ := (Δ : ℝ≥0∞)
  have hD0 : D ≠ 0 := by
    dsimp [D]
    exact_mod_cast (show (2 * n : ℕ) ≠ 0 by omega)
  have hDtop : D ≠ ⊤ := by
    dsimp [D]
    exact ENNReal.natCast_ne_top _
  change D / (D + E) = (1 + E / D)⁻¹
  calc
    D / (D + E) = ((D + E) / D)⁻¹ := by
      rw [ENNReal.inv_div (Or.inl hDtop) (Or.inl hD0)]
    _ = (D / D + E / D)⁻¹ := by rw [ENNReal.add_div]
    _ = (1 + E / D)⁻¹ := by rw [ENNReal.div_self hD0 hDtop]

theorem lemma6SafetyBase_le_one
    {n Δ : ℕ} (hn : 0 < n) :
    lemma6SafetyBase n Δ ≤ 1 := by
  unfold lemma6SafetyBase
  have hden0 : (((2 * n + Δ : ℕ) : ℝ≥0∞)) ≠ 0 := by
    exact_mod_cast (show 2 * n + Δ ≠ 0 by omega)
  have hdenTop : (((2 * n + Δ : ℕ) : ℝ≥0∞)) ≠ ⊤ :=
    ENNReal.natCast_ne_top _
  apply (ENNReal.div_le_iff hden0 hdenTop).2
  rw [one_mul]
  exact_mod_cast (show 2 * n ≤ 2 * n + Δ by omega)

theorem lemma6SafetyBase_ne_zero
    {n Δ : ℕ} (hn : 0 < n) :
    lemma6SafetyBase n Δ ≠ 0 := by
  unfold lemma6SafetyBase
  simp only [ne_eq, ENNReal.div_eq_zero_iff, not_or]
  constructor
  · exact_mod_cast (show 2 * n ≠ 0 by omega)
  · exact ENNReal.natCast_ne_top _

theorem lemma6SuccessP_le_one
    {n Δ : ℕ} (hΔn : Δ < n) :
    lemma6SuccessP n Δ ≤ 1 := by
  unfold lemma6SuccessP
  rw [div_le_one]
  · exact_mod_cast (show 5 * n + Δ ≤ 10 * n by omega)
  · exact_mod_cast (show 0 < 10 * n by omega)

theorem lemma6SuccessP_add_complement
    {n Δ : ℕ} (hΔn : Δ < n) :
    (lemma6SuccessP n Δ : ℝ≥0∞) +
      ((1 - lemma6SuccessP n Δ : ℝ≥0) : ℝ≥0∞) = 1 := by
  have hp := lemma6SuccessP_le_one hΔn
  have hnn :
      lemma6SuccessP n Δ +
        (1 - lemma6SuccessP n Δ) = (1 : ℝ≥0) :=
    add_tsub_cancel_of_le hp
  exact_mod_cast hnn

theorem lemma6SuccessP_le_beta_prob
    {n Δ : ℕ} (hΔn : Δ < n) :
    lemma6SuccessP n Δ ≤
      (lemma6Beta n Δ / (lemma6Beta n Δ + 1) : NNReal) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast (Nat.zero_lt_of_lt hΔn)
  have hden10 : (0 : ℝ) < ((10 * n : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < 10 * n by omega)
  have hden2 : (0 : ℝ) < ((2 * n : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < 2 * n by omega)
  rw [← NNReal.coe_le_coe]
  rw [lemma6SuccessP_coe, NNReal.coe_div, NNReal.coe_add,
    lemma6Beta_coe]
  field_simp [hden10.ne', hden2.ne']
  norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
    Nat.cast_one] at *
  have hΔnR : (Δ : ℝ) < n := by exact_mod_cast hΔn
  have hΔ0R : (0 : ℝ) ≤ Δ := by positivity
  have hsqle : (Δ : ℝ) ^ 2 ≤ (n : ℝ) * (Δ : ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_right (le_of_lt hΔnR) hΔ0R]
  ring_nf at hsqle ⊢
  norm_num at *
  nlinarith [hsqle]

/-- The paper's subtraction-free rate condition implies a positive firing
rate on every nondegenerate Lemma 6 instance. -/
theorem lemma6_fire_pos
    {r : RelaxedRate} {n Δ : ℕ}
    (hΔ0 : 0 < Δ) (hΔn : Δ < n)
    (hrate :
      (1 : NNReal) ≤
        r.fire + (((Δ : ℕ) : NNReal) /
          (((2 * n : ℕ) : NNReal)))) :
    0 < r.fire := by
  have hdenpos : (0 : NNReal) < (((2 * n : ℕ) : NNReal)) := by
    exact_mod_cast (show 0 < 2 * n by omega)
  have hfrac_lt :
      (((Δ : ℕ) : NNReal) / (((2 * n : ℕ) : NNReal))) < 1 := by
    rw [div_lt_one hdenpos]
    exact_mod_cast (show Δ < 2 * n by omega)
  by_contra hfire
  have hfire0 : r.fire = 0 :=
    le_antisymm (not_lt.mp hfire) bot_le
  have hle :
      (1 : NNReal) ≤
        (((Δ : ℕ) : NNReal) / (((2 * n : ℕ) : NNReal))) := by
    simpa [hfire0] using hrate
  exact (not_le_of_gt hfrac_lt) hle

/-- The half-gap live guard gives the paper bias inequality
`(1+Δ/(2n)) y ≤ α x`. -/
theorem lemma6_live_guard
    {r : RelaxedRate} {n x₀ y₀ Δ a b : ℕ}
    (hpop : x₀ + y₀ = n) (hgap : y₀ + Δ = x₀)
    (hΔ0 : 0 < Δ) (hΔn : Δ < n)
    (hrate :
      (1 : NNReal) ≤
        r.fire + (((Δ : ℕ) : NNReal) /
          (((2 * n : ℕ) : NNReal))))
    (hstate : a + b + 2 = n)
    (hbad : ¬ Lemma3Bad x₀ Δ (a + 1)) :
    lemma6Beta n Δ * (b + 1 : NNReal) ≤
      r.fire * (a + 1 : NNReal) := by
  have hqBounds := lemma3Quarter_bounds Δ
  have hkx : lemma3Quarter Δ ≤ x₀ :=
    (lemma3Quarter_le hΔ0).trans (by omega)
  have hax : x₀ - lemma3Quarter Δ ≤ a := by
    unfold Lemma3Bad at hbad
    omega
  have hcur : 2 * (b + 1) + Δ ≤ 2 * (a + 1) := by
    omega
  have hnR : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast (lt_trans hΔ0 hΔn)
  have hdenR : (0 : ℝ) < ((2 * n : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < 2 * n by omega)
  have hrateR :
      (1 : ℝ) ≤ (r.fire : ℝ) +
        (Δ : ℝ) / ((2 * n : ℕ) : ℝ) := by
    have h : ((1 : NNReal) : ℝ) ≤
        ((r.fire + (((Δ : ℕ) : NNReal) /
          (((2 * n : ℕ) : NNReal)))) : ℝ) := by
      exact_mod_cast hrate
    simpa [NNReal.coe_add, NNReal.coe_div] using h
  have halpha :
      1 - (Δ : ℝ) / ((2 * n : ℕ) : ℝ) ≤ (r.fire : ℝ) := by
    linarith
  have hcurR :
      (Δ : ℝ) ≤
        2 * (((a + 1 : ℕ) : ℝ) - ((b + 1 : ℕ) : ℝ)) := by
    have hcurR' :
        (2 * (b + 1) + Δ : ℝ) ≤ (2 * (a + 1) : ℝ) := by
      exact_mod_cast hcur
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_one] at hcurR' ⊢
    nlinarith
  have hsumR :
      ((a + 1 : ℕ) : ℝ) + ((b + 1 : ℕ) : ℝ) = (n : ℝ) := by
    have h : ((a + b + 2 : ℕ) : ℝ) = (n : ℝ) := by
      exact_mod_cast hstate
    norm_num only [Nat.cast_add, Nat.cast_ofNat] at h ⊢
    linarith
  have hbetaBase :
      (1 + (Δ : ℝ) / ((2 * n : ℕ) : ℝ)) *
          ((b + 1 : ℕ) : ℝ) ≤
        (1 - (Δ : ℝ) / ((2 * n : ℕ) : ℝ)) *
          ((a + 1 : ℕ) : ℝ) := by
    field_simp [hdenR.ne']
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
      Nat.cast_one] at *
    have hkey :
        (n : ℝ) * (Δ : ℝ) ≤
          (2 * (n : ℝ)) *
            (((a : ℝ) + 1) - ((b : ℝ) + 1)) := by
      calc
        (n : ℝ) * (Δ : ℝ) ≤
            (n : ℝ) *
              (2 * (((a : ℝ) + 1) - ((b : ℝ) + 1))) :=
          mul_le_mul_of_nonneg_left hcurR hnR.le
        _ = (2 * (n : ℝ)) *
            (((a : ℝ) + 1) - ((b : ℝ) + 1)) := by
          ring
    ring_nf at hkey ⊢
    nlinarith
  rw [← NNReal.coe_le_coe]
  rw [NNReal.coe_mul, NNReal.coe_mul, lemma6Beta_coe]
  simpa only [Nat.cast_add, Nat.cast_one] using
    hbetaBase.trans
      (mul_le_mul_of_nonneg_right halpha (by positivity))

theorem lemma6_live_productive_nonzero
    (r : RelaxedRate) {n a b : ℕ}
    (h3 : 3 ≤ n) (hstate : a + b + 2 = n)
    (hfire : 0 < r.fire) :
    relaxedTriStep r (a + 1) (b + 1) (by omega) a +
        relaxedTriStep r (a + 1) (b + 1) (by omega) (a + 2) ≠ 0 := by
  intro hzero
  have hlower :=
    relaxed_productive_mass_ge_interior r a b n h3 hstate
  have hfireE0 : (r.fire : ℝ≥0∞) ≠ 0 := by
    simpa [ENNReal.coe_eq_zero] using (ne_of_gt hfire)
  have hthreeDiv0 :
      ((3 : ℝ≥0∞) / (n : ℝ≥0∞)) ≠ 0 := by
    exact ne_of_gt
      (ENNReal.div_pos (by norm_num) (ENNReal.natCast_ne_top n))
  have hleftpos :
      0 < (r.fire : ℝ≥0∞) * ((3 : ℝ≥0∞) / (n : ℝ≥0∞)) :=
    ENNReal.mul_pos hfireE0 hthreeDiv0
  have hle0 :
      (r.fire : ℝ≥0∞) * ((3 : ℝ≥0∞) / (n : ℝ≥0∞)) ≤ 0 := by
    simpa [hzero] using hlower
  exact (not_le_of_gt hleftpos) hle0

/-- The direction of one relaxed productive reaction.  `true` is the
`X`-increasing reaction. -/
noncomputable def relaxedProductiveDirectionPMF
    (r : RelaxedRate) (a b : ℕ)
    (h : 3 ≤ (a + 1) + (b + 1))
    (hprod :
      relaxedTriStep r (a + 1) (b + 1) h a +
          relaxedTriStep r (a + 1) (b + 1) h (a + 2) ≠ 0) :
    PMF Bool := by
  classical
  refine PMF.ofFintype
    (fun up =>
      if up then
        relaxedTriStep r (a + 1) (b + 1) h (a + 2) /
          (relaxedTriStep r (a + 1) (b + 1) h a +
            relaxedTriStep r (a + 1) (b + 1) h (a + 2))
      else
        relaxedTriStep r (a + 1) (b + 1) h a /
          (relaxedTriStep r (a + 1) (b + 1) h a +
            relaxedTriStep r (a + 1) (b + 1) h (a + 2))) ?_
  rw [show (Finset.univ : Finset Bool) = {false, true} by
    ext up
    cases up <;> simp]
  simp only [Finset.sum_insert, Finset.mem_singleton, Bool.false_eq_true,
    not_false_eq_true, Finset.sum_singleton, ↓reduceIte]
  rw [ENNReal.div_add_div_same]
  exact ENNReal.div_self hprod
    (ENNReal.add_ne_top.mpr ⟨PMF.apply_ne_top _ _, PMF.apply_ne_top _ _⟩)

@[simp] theorem relaxedProductiveDirectionPMF_true
    (r : RelaxedRate) (a b : ℕ)
    (h : 3 ≤ (a + 1) + (b + 1))
    (hprod :
      relaxedTriStep r (a + 1) (b + 1) h a +
          relaxedTriStep r (a + 1) (b + 1) h (a + 2) ≠ 0) :
    relaxedProductiveDirectionPMF r a b h hprod true =
      relaxedTriStep r (a + 1) (b + 1) h (a + 2) /
        (relaxedTriStep r (a + 1) (b + 1) h a +
          relaxedTriStep r (a + 1) (b + 1) h (a + 2)) := by
  rfl

@[simp] theorem relaxedProductiveDirectionPMF_false
    (r : RelaxedRate) (a b : ℕ)
    (h : 3 ≤ (a + 1) + (b + 1))
    (hprod :
      relaxedTriStep r (a + 1) (b + 1) h a +
          relaxedTriStep r (a + 1) (b + 1) h (a + 2) ≠ 0) :
    relaxedProductiveDirectionPMF r a b h hprod false =
      relaxedTriStep r (a + 1) (b + 1) h a /
        (relaxedTriStep r (a + 1) (b + 1) h a +
          relaxedTriStep r (a + 1) (b + 1) h (a + 2)) := by
  rfl

theorem relaxedProductiveDirectionPMF_masses
    (r : RelaxedRate) (a b : ℕ)
    (h : 3 ≤ (a + 1) + (b + 1))
    (hprod :
      relaxedTriStep r (a + 1) (b + 1) h a +
          relaxedTriStep r (a + 1) (b + 1) h (a + 2) ≠ 0) :
    relaxedTriStep r (a + 1) (b + 1) h (a + 2) /
          (relaxedTriStep r (a + 1) (b + 1) h a +
            relaxedTriStep r (a + 1) (b + 1) h (a + 2)) +
      relaxedTriStep r (a + 1) (b + 1) h a /
          (relaxedTriStep r (a + 1) (b + 1) h a +
            relaxedTriStep r (a + 1) (b + 1) h (a + 2)) = 1 :=
  relaxedProductiveTriInterior_masses r a b h hprod

/-- Stopped Lemma 6 trace: physical `x`, productive-up successes, and consumed
productive slots. -/
noncomputable def lemma6TraceStep
    (r : RelaxedRate) (n x₀ Δ : ℕ) :
    Lemma3Trace → PMF Lemma3Trace := fun q =>
  if Lemma3Bad x₀ Δ q.x ∨ Lemma3Target n Δ q.x then
    PMF.pure ⟨q.x, q.success + 1, q.clock + 1⟩
  else if hphys : 3 ≤ n ∧ 0 < q.x ∧ q.x < n then
    let a := q.x - 1
    let b := n - q.x - 1
    let hstep : 3 ≤ (a + 1) + (b + 1) := by omega
    if hprod :
        relaxedTriStep r (a + 1) (b + 1) hstep a +
            relaxedTriStep r (a + 1) (b + 1) hstep (a + 2) ≠ 0 then
      (relaxedProductiveDirectionPMF r a b hstep hprod).map
        fun up =>
          ⟨if up then q.x + 1 else q.x - 1,
            if up then q.success + 1 else q.success,
            q.clock + 1⟩
    else
      PMF.pure ⟨q.x, q.success + 1, q.clock + 1⟩
  else
    PMF.pure ⟨q.x, q.success + 1, q.clock + 1⟩

theorem lemma6TraceStep_of_boundary
    (r : RelaxedRate) (n x₀ Δ : ℕ) (q : Lemma3Trace)
    (hq : Lemma3Bad x₀ Δ q.x ∨ Lemma3Target n Δ q.x) :
    lemma6TraceStep r n x₀ Δ q =
      PMF.pure ⟨q.x, q.success + 1, q.clock + 1⟩ := by
  unfold lemma6TraceStep
  rw [if_pos hq]

theorem lemma6TraceStep_of_live
    (r : RelaxedRate) (n x₀ Δ : ℕ) (q : Lemma3Trace)
    (hbound : ¬ (Lemma3Bad x₀ Δ q.x ∨ Lemma3Target n Δ q.x))
    (hphys : 3 ≤ n ∧ 0 < q.x ∧ q.x < n)
    (hprod :
      relaxedTriStep r q.x (n - q.x) (by omega) (q.x - 1) +
          relaxedTriStep r q.x (n - q.x) (by omega) (q.x + 1) ≠ 0) :
    lemma6TraceStep r n x₀ Δ q =
      (relaxedProductiveDirectionPMF r (q.x - 1) (n - q.x - 1)
        (by omega) (by
          simpa only [show q.x - 1 + 1 = q.x by omega,
            show n - q.x - 1 + 1 = n - q.x by omega,
            show q.x - 1 + 2 = q.x + 1 by omega] using hprod)).map
        (fun up =>
          ⟨if up then q.x + 1 else q.x - 1,
            if up then q.success + 1 else q.success,
            q.clock + 1⟩) := by
  unfold lemma6TraceStep
  rw [if_neg hbound, dif_pos hphys]
  dsimp only
  have hprod' :
      relaxedTriStep r (q.x - 1 + 1) (n - q.x - 1 + 1) (by omega) (q.x - 1) +
          relaxedTriStep r (q.x - 1 + 1) (n - q.x - 1 + 1) (by omega)
            (q.x - 1 + 2) ≠ 0 := by
    simpa only [show q.x - 1 + 1 = q.x by omega,
      show n - q.x - 1 + 1 = n - q.x by omega,
      show q.x - 1 + 2 = q.x + 1 by omega] using hprod
  rw [dif_pos hprod']

theorem lemma6TraceStep_clock_of_apply_ne_zero
    (r : RelaxedRate) (n x₀ Δ : ℕ) (q z : Lemma3Trace)
    (hqz : lemma6TraceStep r n x₀ Δ q z ≠ 0) :
    z.clock = q.clock + 1 := by
  classical
  by_cases hbound :
      Lemma3Bad x₀ Δ q.x ∨ Lemma3Target n Δ q.x
  · rw [lemma6TraceStep_of_boundary r n x₀ Δ q hbound,
      PMF.pure_apply] at hqz
    by_cases hz :
        z = (⟨q.x, q.success + 1, q.clock + 1⟩ : Lemma3Trace)
    · subst z
      rfl
    · simp [hz] at hqz
  · by_cases hphys : 3 ≤ n ∧ 0 < q.x ∧ q.x < n
    · by_cases hprod :
        relaxedTriStep r q.x (n - q.x) (by omega) (q.x - 1) +
            relaxedTriStep r q.x (n - q.x) (by omega) (q.x + 1) ≠ 0
      · rw [lemma6TraceStep_of_live r n x₀ Δ q hbound hphys hprod,
          PMF.map_apply, Ne, ENNReal.tsum_eq_zero] at hqz
        push Not at hqz
        obtain ⟨up, hup⟩ := hqz
        let next : Lemma3Trace :=
          ⟨if up then q.x + 1 else q.x - 1,
            if up then q.success + 1 else q.success,
            q.clock + 1⟩
        by_cases hz : z = next
        · subst z
          rfl
        · simp [next, hz] at hup
      · unfold lemma6TraceStep at hqz
        rw [if_neg hbound, dif_pos hphys] at hqz
        dsimp only at hqz
        rw [dif_neg] at hqz
        · by_cases hz :
              z = (⟨q.x, q.success + 1, q.clock + 1⟩ : Lemma3Trace)
          · subst z
            rfl
          · have hzero :
                (PMF.pure
                  (⟨q.x, q.success + 1, q.clock + 1⟩ :
                    Lemma3Trace)) z = 0 := by
              simp [PMF.pure_apply, hz]
            exact False.elim (hqz hzero)
        · intro h
          apply hprod
          simpa only [show q.x - 1 + 1 = q.x by omega,
            show n - q.x - 1 + 1 = n - q.x by omega,
            show q.x - 1 + 2 = q.x + 1 by omega] using h
    · unfold lemma6TraceStep at hqz
      rw [if_neg hbound, dif_neg hphys, PMF.pure_apply] at hqz
      by_cases hz :
          z = (⟨q.x, q.success + 1, q.clock + 1⟩ : Lemma3Trace)
      · subst z
        rfl
      · simp [hz] at hqz

theorem lemma6TraceStep_support
    {r : RelaxedRate} {n x₀ y₀ Δ : ℕ}
    (hpop : x₀ + y₀ = n) (hgap : y₀ + Δ = x₀)
    (hΔ0 : 0 < Δ) (hΔn : Δ < n)
    (hfire : 0 < r.fire)
    (q : Lemma3Trace) (hq : q.Inv n x₀ Δ)
    (z : Lemma3Trace)
    (hqz : lemma6TraceStep r n x₀ Δ q z ≠ 0) :
    z.Inv n x₀ Δ ∧ z.clock = q.clock + 1 := by
  classical
  by_cases hbound :
      Lemma3Bad x₀ Δ q.x ∨ Lemma3Target n Δ q.x
  · rw [lemma6TraceStep_of_boundary r n x₀ Δ q hbound,
      PMF.pure_apply] at hqz
    by_cases hz :
        z = (⟨q.x, q.success + 1, q.clock + 1⟩ : Lemma3Trace)
    · subst z
      constructor
      · rcases hbound with hbad | htarget
        · exact Or.inl hbad
        · exact Or.inr (Or.inl htarget)
      · rfl
    · simp [hz] at hqz
  · have hbad : ¬ Lemma3Bad x₀ Δ q.x := by
      exact fun h => hbound (Or.inl h)
    have htarget : ¬ Lemma3Target n Δ q.x := by
      exact fun h => hbound (Or.inr h)
    have hphys :=
      lemma3_live_physical hpop hgap hΔ0 hΔn hbad htarget
    have hprod :
        relaxedTriStep r q.x (n - q.x) (by omega) (q.x - 1) +
            relaxedTriStep r q.x (n - q.x) (by omega) (q.x + 1) ≠ 0 := by
      have hprod' :=
        lemma6_live_productive_nonzero r
          (n := n) (a := q.x - 1) (b := n - q.x - 1)
          hphys.1 (by omega) hfire
      simpa only [show q.x - 1 + 1 = q.x by omega,
        show n - q.x - 1 + 1 = n - q.x by omega,
        show q.x - 1 + 2 = q.x + 1 by omega] using hprod'
    rw [lemma6TraceStep_of_live r n x₀ Δ q hbound hphys hprod,
      PMF.map_apply, Ne, ENNReal.tsum_eq_zero] at hqz
    push Not at hqz
    obtain ⟨up, hup⟩ := hqz
    let next : Lemma3Trace :=
      ⟨if up then q.x + 1 else q.x - 1,
        if up then q.success + 1 else q.success,
        q.clock + 1⟩
    by_cases hz : z = next
    · subst z
      have hrel :
          q.x + q.clock = x₀ + 2 * q.success := by
        rcases hq with hq | hq | hq
        · exact False.elim (hbad hq)
        · exact False.elim (htarget hq)
        · exact hq
      constructor
      · right
        right
        cases up <;> simp [next] at hrel ⊢ <;> omega
      · simp [next]
    · simp [next, hz] at hup

private theorem lemma6_iter_support_count_add_one
    {α : Type*} (K : α → PMF α) (count : α → ℕ)
    (hstep : ∀ s z, K s z ≠ 0 → count z = count s + 1) :
    ∀ T s z, iter K T s z ≠ 0 → count z = count s + T := by
  intro T
  induction T with
  | zero =>
      intro s z hz
      simp only [iter, PMF.pure_apply] at hz
      by_cases h : z = s
      · subst z
        simp
      · simp [h] at hz
  | succ T ih =>
      intro s z hz
      rw [iter_succ, PMF.bind_apply, Ne, ENNReal.tsum_eq_zero] at hz
      push Not at hz
      obtain ⟨a, ha⟩ := hz
      have hK : K s a ≠ 0 := by
        intro hzero
        simp [hzero] at ha
      have hiter : iter K T a z ≠ 0 := by
        intro hzero
        simp [hzero] at ha
      rw [ih a z hiter, hstep s a hK]
      omega

theorem lemma6Trace_iter_inv
    {r : RelaxedRate} {n x₀ y₀ Δ T : ℕ}
    (hpop : x₀ + y₀ = n) (hgap : y₀ + Δ = x₀)
    (hΔ0 : 0 < Δ) (hΔn : Δ < n)
    (hfire : 0 < r.fire)
    (z : Lemma3Trace)
    (hz :
      iter (lemma6TraceStep r n x₀ Δ) T (lemma3Initial x₀) z ≠ 0) :
    z.Inv n x₀ Δ := by
  apply iter_support_closed
    (lemma6TraceStep r n x₀ Δ) (Lemma3Trace.Inv n x₀ Δ)
      (fun q hq z hqz =>
        (lemma6TraceStep_support hpop hgap hΔ0 hΔn hfire q hq z hqz).1)
      T (lemma3Initial x₀) z
  · exact lemma3Initial_inv n x₀ Δ
  · exact hz

theorem lemma6Trace_iter_clock
    {r : RelaxedRate} {n x₀ Δ T : ℕ}
    (z : Lemma3Trace)
    (hz :
      iter (lemma6TraceStep r n x₀ Δ) T (lemma3Initial x₀) z ≠ 0) :
    z.clock = T := by
  have hclock :=
    lemma6_iter_support_count_add_one
      (lemma6TraceStep r n x₀ Δ) Lemma3Trace.clock
      (lemma6TraceStep_clock_of_apply_ne_zero r n x₀ Δ)
      T (lemma3Initial x₀) z hz
  simpa [lemma3Initial] using hclock

theorem lemma6TraceStep_isLazyProjection
    (r : RelaxedRate) (n x₀ Δ : ℕ) :
    IsLazyProjection (relaxedProductiveTriChain r n)
      (lemma6TraceStep r n x₀ Δ) Lemma3Trace.toX := by
  classical
  intro q
  by_cases hbound :
      Lemma3Bad x₀ Δ q.x ∨ Lemma3Target n Δ q.x
  · rw [lemma6TraceStep_of_boundary r n x₀ Δ q hbound]
    right
    exact PMF.pure_map Lemma3Trace.toX
      ⟨q.x, q.success + 1, q.clock + 1⟩
  · by_cases hphys : 3 ≤ n ∧ 0 < q.x ∧ q.x < n
    · by_cases hprod :
        relaxedTriStep r q.x (n - q.x) (by omega) (q.x - 1) +
            relaxedTriStep r q.x (n - q.x) (by omega) (q.x + 1) ≠ 0
      · rw [lemma6TraceStep_of_live r n x₀ Δ q hbound hphys hprod]
        left
        change _ = relaxedProductiveTriChain r n q.x
        unfold relaxedProductiveTriChain
        rw [dif_pos hphys]
        dsimp only
        have hprod' :
            relaxedTriStep r (q.x - 1 + 1) (n - q.x - 1 + 1) (by omega)
                (q.x - 1) +
              relaxedTriStep r (q.x - 1 + 1) (n - q.x - 1 + 1) (by omega)
                (q.x - 1 + 2) ≠ 0 := by
          simpa only [show q.x - 1 + 1 = q.x by omega,
            show n - q.x - 1 + 1 = n - q.x by omega,
            show q.x - 1 + 2 = q.x + 1 by omega] using hprod
        rw [dif_pos hprod']
        unfold relaxedProductiveTriInterior relaxedProductiveDirectionPMF
        rw [PMF.map_comp]
        apply PMF.ext
        intro y
        rw [PMF.map_apply, PMF.map_apply]
        apply tsum_congr
        intro up
        cases up
        · simp [Lemma3Trace.toX]
        · simp [Lemma3Trace.toX,
            show q.x - 1 + 2 = q.x + 1 by omega]
      · unfold lemma6TraceStep
        rw [if_neg hbound, dif_pos hphys]
        dsimp only
        right
        have hprod' :
            ¬ relaxedTriStep r (q.x - 1 + 1) (n - q.x - 1 + 1) (by omega)
                (q.x - 1) +
              relaxedTriStep r (q.x - 1 + 1) (n - q.x - 1 + 1) (by omega)
                (q.x - 1 + 2) ≠ 0 := by
          intro h
          apply hprod
          simpa only [show q.x - 1 + 1 = q.x by omega,
            show n - q.x - 1 + 1 = n - q.x by omega,
            show q.x - 1 + 2 = q.x + 1 by omega] using h
        rw [dif_neg hprod']
        exact PMF.pure_map Lemma3Trace.toX
          ⟨q.x, q.success + 1, q.clock + 1⟩
    · unfold lemma6TraceStep
      rw [if_neg hbound, dif_neg hphys]
      right
      exact PMF.pure_map Lemma3Trace.toX
        ⟨q.x, q.success + 1, q.clock + 1⟩

theorem lemma6TraceStep_count_moment
    {r : RelaxedRate} {n x₀ y₀ Δ : ℕ}
    (hpop : x₀ + y₀ = n) (hgap : y₀ + Δ = x₀)
    (hΔ0 : 0 < Δ) (hΔn : Δ < n)
    (hfire : 0 < r.fire)
    (hrate :
      (1 : NNReal) ≤
        r.fire + (((Δ : ℕ) : NNReal) /
          (((2 * n : ℕ) : NNReal))))
    (w : ℝ≥0∞) (hw : w ≤ 1) :
    ∀ q,
      expect (lemma6TraceStep r n x₀ Δ q)
          (fun z => w ^ z.success) ≤
        (((1 - lemma6SuccessP n Δ : ℝ≥0) : ℝ≥0∞) +
            (lemma6SuccessP n Δ : ℝ≥0∞) * w) *
          w ^ q.success := by
  intro q
  have hpSum := lemma6SuccessP_add_complement hΔn
  have hpOne :
      (lemma6SuccessP n Δ : ℝ≥0∞) ≤ 1 := by
    exact_mod_cast lemma6SuccessP_le_one hΔn
  by_cases hbound :
      Lemma3Bad x₀ Δ q.x ∨ Lemma3Target n Δ q.x
  · apply count_step_of_masses
      (K := lemma6TraceStep r n x₀ Δ)
      (count := Lemma3Trace.success) (s := q) (w := w)
      (q := 1) (q' := 0)
      (p := (lemma6SuccessP n Δ : ℝ≥0∞))
      (p' := ((1 - lemma6SuccessP n Δ : ℝ≥0) : ℝ≥0∞))
    · simp
    · exact hpSum
    · exact hw
    · exact hpOne
    · rw [lemma6TraceStep_of_boundary r n x₀ Δ q hbound,
        expect_pure]
      simp
  · have hbad : ¬ Lemma3Bad x₀ Δ q.x :=
      fun h => hbound (Or.inl h)
    have htarget : ¬ Lemma3Target n Δ q.x :=
      fun h => hbound (Or.inr h)
    have hphys :=
      lemma3_live_physical hpop hgap hΔ0 hΔn hbad htarget
    obtain ⟨a, ha⟩ : ∃ a, q.x = a + 1 :=
      ⟨q.x - 1, by omega⟩
    obtain ⟨b, hstate⟩ : ∃ b, a + b + 2 = n :=
      ⟨n - a - 2, by omega⟩
    have hbadA : ¬ Lemma3Bad x₀ Δ (a + 1) := by
      simpa [ha] using hbad
    have hprod :
        relaxedTriStep r (a + 1) (b + 1) (by omega) a +
            relaxedTriStep r (a + 1) (b + 1) (by omega) (a + 2) ≠ 0 :=
      lemma6_live_productive_nonzero r hphys.1 hstate hfire
    have hprodRaw :
        relaxedTriStep r q.x (n - q.x) (by omega) (q.x - 1) +
            relaxedTriStep r q.x (n - q.x) (by omega) (q.x + 1) ≠ 0 := by
      simpa [ha, hstate, show n - (a + 1) = b + 1 by omega]
        using hprod
    have hqBeta :
        lemma7DownProb (lemma6Beta n Δ) ≤
          relaxedTriStep r (a + 1) (b + 1) (by omega) (a + 2) /
            (relaxedTriStep r (a + 1) (b + 1) (by omega) a +
              relaxedTriStep r (a + 1) (b + 1) (by omega) (a + 2)) := by
      rw [lemma7DownProb_eq]
      exact relaxed_down_mass_ge r (by omega)
        (by
          have hfire1 : r.fire ≤ 1 := by
            rw [← r.add_eq_one]
            exact le_add_right le_rfl
          exact hfire1.trans (lemma6Beta_ge_one n Δ))
        hprod
        (lemma6_live_guard hpop hgap hΔ0 hΔn hrate hstate hbadA)
    have hpLive :
        (lemma6SuccessP n Δ : ℝ≥0∞) ≤
          relaxedTriStep r (a + 1) (b + 1) (by omega) (a + 2) /
            (relaxedTriStep r (a + 1) (b + 1) (by omega) a +
              relaxedTriStep r (a + 1) (b + 1) (by omega) (a + 2)) := by
      have hpBeta :
          (lemma6SuccessP n Δ : ℝ≥0∞) ≤
            lemma7DownProb (lemma6Beta n Δ) := by
        unfold lemma7DownProb
        exact_mod_cast lemma6SuccessP_le_beta_prob (n := n) (Δ := Δ) hΔn
      exact hpBeta.trans hqBeta
    have hsum :
        relaxedTriStep r (a + 1) (b + 1) (by omega) (a + 2) /
              (relaxedTriStep r (a + 1) (b + 1) (by omega) a +
                relaxedTriStep r (a + 1) (b + 1) (by omega) (a + 2)) +
            relaxedTriStep r (a + 1) (b + 1) (by omega) a /
              (relaxedTriStep r (a + 1) (b + 1) (by omega) a +
                relaxedTriStep r (a + 1) (b + 1) (by omega) (a + 2)) = 1 :=
      relaxedProductiveDirectionPMF_masses r a b (by omega) hprod
    apply count_step_of_masses
      (K := lemma6TraceStep r n x₀ Δ)
      (count := Lemma3Trace.success) (s := q) (w := w)
      (q :=
        relaxedTriStep r (a + 1) (b + 1) (by omega) (a + 2) /
          (relaxedTriStep r (a + 1) (b + 1) (by omega) a +
            relaxedTriStep r (a + 1) (b + 1) (by omega) (a + 2)))
      (q' :=
        relaxedTriStep r (a + 1) (b + 1) (by omega) a /
          (relaxedTriStep r (a + 1) (b + 1) (by omega) a +
            relaxedTriStep r (a + 1) (b + 1) (by omega) (a + 2)))
      (p := (lemma6SuccessP n Δ : ℝ≥0∞))
      (p' := ((1 - lemma6SuccessP n Δ : ℝ≥0) : ℝ≥0∞))
    · exact hsum
    · exact hpSum
    · exact hw
    · exact hpLive
    · rw [lemma6TraceStep_of_live r n x₀ Δ q hbound hphys hprodRaw,
        expect_map]
      unfold expect
      rw [tsum_fintype]
      rw [show (Finset.univ : Finset Bool) = {false, true} by
        ext up
        cases up <;> simp]
      simp [ha, show n - (a + 1) = b + 1 by omega]

theorem lemma6TraceStep_safety_moment
    {r : RelaxedRate} {n x₀ y₀ Δ : ℕ}
    (hpop : x₀ + y₀ = n) (hgap : y₀ + Δ = x₀)
    (hΔ0 : 0 < Δ) (hΔn : Δ < n)
    (hfire : 0 < r.fire)
    (hrate :
      (1 : NNReal) ≤
        r.fire + (((Δ : ℕ) : NNReal) /
          (((2 * n : ℕ) : NNReal)))) :
    ∀ q,
      expect (lemma6TraceStep r n x₀ Δ q)
          (fun z => lemma6SafetyBase n Δ ^ z.x) ≤
        lemma6SafetyBase n Δ ^ q.x := by
  intro q
  by_cases hbound :
      Lemma3Bad x₀ Δ q.x ∨ Lemma3Target n Δ q.x
  · rw [lemma6TraceStep_of_boundary r n x₀ Δ q hbound,
      expect_pure]
  · have hbad : ¬ Lemma3Bad x₀ Δ q.x :=
      fun h => hbound (Or.inl h)
    have htarget : ¬ Lemma3Target n Δ q.x :=
      fun h => hbound (Or.inr h)
    have hphys :=
      lemma3_live_physical hpop hgap hΔ0 hΔn hbad htarget
    obtain ⟨a, ha⟩ : ∃ a, q.x = a + 1 :=
      ⟨q.x - 1, by omega⟩
    obtain ⟨b, hstate⟩ : ∃ b, a + b + 2 = n :=
      ⟨n - a - 2, by omega⟩
    have hbadA : ¬ Lemma3Bad x₀ Δ (a + 1) := by
      simpa [ha] using hbad
    have hprod :
        relaxedTriStep r (a + 1) (b + 1) (by omega) a +
            relaxedTriStep r (a + 1) (b + 1) (by omega) (a + 2) ≠ 0 :=
      lemma6_live_productive_nonzero r hphys.1 hstate hfire
    have hprodRaw :
        relaxedTriStep r q.x (n - q.x) (by omega) (q.x - 1) +
            relaxedTriStep r q.x (n - q.x) (by omega) (q.x + 1) ≠ 0 := by
      simpa [ha, hstate, show n - (a + 1) = b + 1 by omega]
        using hprod
    have hq :
        lemma7DownProb (lemma6Beta n Δ) ≤
          relaxedTriStep r (a + 1) (b + 1) (by omega) (a + 2) /
            (relaxedTriStep r (a + 1) (b + 1) (by omega) a +
              relaxedTriStep r (a + 1) (b + 1) (by omega) (a + 2)) := by
      rw [lemma7DownProb_eq]
      exact relaxed_down_mass_ge r (by omega)
        (by
          have hfire1 : r.fire ≤ 1 := by
            rw [← r.add_eq_one]
            exact le_add_right le_rfl
          exact hfire1.trans (lemma6Beta_ge_one n Δ))
        hprod
        (lemma6_live_guard hpop hgap hΔ0 hΔn hrate hstate hbadA)
    have hsum :
        relaxedTriStep r (a + 1) (b + 1) (by omega) (a + 2) /
              (relaxedTriStep r (a + 1) (b + 1) (by omega) a +
                relaxedTriStep r (a + 1) (b + 1) (by omega) (a + 2)) +
            relaxedTriStep r (a + 1) (b + 1) (by omega) a /
              (relaxedTriStep r (a + 1) (b + 1) (by omega) a +
                relaxedTriStep r (a + 1) (b + 1) (by omega) (a + 2)) = 1 :=
      relaxedProductiveDirectionPMF_masses r a b (by omega) hprod
    have hscalar := lemma7_feller_scalar_step
      (lemma6Beta_ge_one n Δ) hsum hq
    have hbase := lemma6SafetyBase_eq_beta_inv
      (n := n) (Δ := Δ) (lt_trans hΔ0 hΔn)
    rw [lemma6TraceStep_of_live r n x₀ Δ q hbound hphys hprodRaw,
      expect_map]
    unfold expect
    rw [tsum_fintype]
    rw [show (Finset.univ : Finset Bool) = {false, true} by
      ext up
      cases up <;> simp]
    simp [ha, show n - (a + 1) = b + 1 by omega]
    rw [hbase]
    let u : ℝ≥0∞ := ((lemma6Beta n Δ : ℝ≥0∞)⁻¹)
    change
      relaxedTriStep r (a + 1) (b + 1) (by omega) a /
            (relaxedTriStep r (a + 1) (b + 1) (by omega) a +
              relaxedTriStep r (a + 1) (b + 1) (by omega) (a + 2)) *
            u ^ a +
          relaxedTriStep r (a + 1) (b + 1) (by omega) (a + 2) /
            (relaxedTriStep r (a + 1) (b + 1) (by omega) a +
              relaxedTriStep r (a + 1) (b + 1) (by omega) (a + 2)) *
            u ^ (a + 2) ≤
        u ^ (a + 1)
    calc
      relaxedTriStep r (a + 1) (b + 1) (by omega) a /
            (relaxedTriStep r (a + 1) (b + 1) (by omega) a +
              relaxedTriStep r (a + 1) (b + 1) (by omega) (a + 2)) *
            u ^ a +
          relaxedTriStep r (a + 1) (b + 1) (by omega) (a + 2) /
            (relaxedTriStep r (a + 1) (b + 1) (by omega) a +
              relaxedTriStep r (a + 1) (b + 1) (by omega) (a + 2)) *
            u ^ (a + 2)
          =
        u ^ a *
          (relaxedTriStep r (a + 1) (b + 1) (by omega) a /
              (relaxedTriStep r (a + 1) (b + 1) (by omega) a +
                relaxedTriStep r (a + 1) (b + 1) (by omega) (a + 2)) +
            relaxedTriStep r (a + 1) (b + 1) (by omega) (a + 2) /
              (relaxedTriStep r (a + 1) (b + 1) (by omega) a +
                relaxedTriStep r (a + 1) (b + 1) (by omega) (a + 2)) *
              u ^ 2) := by
          rw [show a + 2 = a + 2 by rfl, pow_add]
          ring
      _ ≤ u ^ a * u := by
        simpa [u, mul_comm, mul_left_comm, mul_assoc] using
          (mul_le_mul_left hscalar (u ^ a))
      _ = u ^ (a + 1) := by
        rw [pow_succ]

theorem lemma6Trace_bad_mass
    {r : RelaxedRate} {n x₀ y₀ Δ T : ℕ}
    (hpop : x₀ + y₀ = n) (hgap : y₀ + Δ = x₀)
    (hΔ0 : 0 < Δ) (hΔn : Δ < n)
    (hfire : 0 < r.fire)
    (hrate :
      (1 : NNReal) ≤
        r.fire + (((Δ : ℕ) : NNReal) /
          (((2 * n : ℕ) : NNReal)))) :
    (∑' z : Lemma3Trace,
        if Lemma3Bad x₀ Δ z.x then
          iter (lemma6TraceStep r n x₀ Δ) T
            (lemma3Initial x₀) z
        else 0) ≤
      lemma6SafetyBase n Δ ^ lemma3Quarter Δ := by
  have hkx : lemma3Quarter Δ ≤ x₀ :=
    (lemma3Quarter_le hΔ0).trans (by omega)
  have hxsplit :
      (lemma3Initial x₀).x =
        (x₀ - lemma3Quarter Δ) + lemma3Quarter Δ := by
    simp [lemma3Initial]
    omega
  simpa [Lemma3Bad] using
    ruin_le_u
      (lemma6TraceStep r n x₀ Δ) Lemma3Trace.x
      (lemma6SafetyBase n Δ)
      (lemma6SafetyBase_le_one (lt_trans hΔ0 hΔn))
      (lemma6SafetyBase_ne_zero (lt_trans hΔ0 hΔn))
      (fun q => lemma6SafetyBase n Δ ^ q.x)
      (fun _ => rfl)
      (lemma6TraceStep_safety_moment
        hpop hgap hΔ0 hΔn hfire hrate)
      T (x₀ - lemma3Quarter Δ) (lemma3Quarter Δ)
      (lemma3Initial x₀) hxsplit

theorem lemma6Safety_power_exp
    {n Δ : ℕ} (hΔ0 : 0 < Δ) (hΔn : Δ < n) :
    lemma6SafetyBase n Δ ^ lemma3Quarter Δ ≤
      ENNReal.ofReal
        (Real.exp
          (-((Δ : ℝ) ^ 2 /
            (8 * (n : ℝ) + 4 * (Δ : ℝ))))) := by
  unfold lemma6SafetyBase
  apply ratio_pow_le_ofReal_exp
      (2 * n + Δ) (2 * n) (lemma3Quarter Δ)
      ((Δ : ℝ) ^ 2 /
        (8 * (n : ℝ) + 4 * (Δ : ℝ)))
  · omega
  · omega
  · have hq := (lemma3Quarter_bounds Δ).1
    have hqR :
        (Δ : ℝ) ≤ 4 * (lemma3Quarter Δ : ℝ) := by
      exact_mod_cast hq
    have hnR : (0 : ℝ) < n := by
      exact_mod_cast (lt_trans hΔ0 hΔn)
    have hden :
        (0 : ℝ) < 2 * (n : ℝ) + (Δ : ℝ) := by
      positivity
    have hfactor :
        0 ≤ (Δ : ℝ) /
          (2 * (n : ℝ) + (Δ : ℝ)) := by
      positivity
    have hrewrite :
        (Δ : ℝ) ^ 2 /
            (8 * (n : ℝ) + 4 * (Δ : ℝ)) =
          ((Δ : ℝ) / 4) *
            ((Δ : ℝ) /
              (2 * (n : ℝ) + (Δ : ℝ))) := by
      field_simp [hden.ne']
      ring
    rw [hrewrite]
    calc
      ((Δ : ℝ) / 4) *
            ((Δ : ℝ) /
              (2 * (n : ℝ) + (Δ : ℝ))) ≤
          (lemma3Quarter Δ : ℝ) *
            ((Δ : ℝ) /
              (2 * (n : ℝ) + (Δ : ℝ))) :=
        mul_le_mul_of_nonneg_right (by nlinarith) hfactor
      _ = (lemma3Quarter Δ : ℝ) *
          (((2 * n + Δ : ℕ) : ℝ) -
            ((2 * n : ℕ) : ℝ)) /
          ((2 * n + Δ : ℕ) : ℝ) := by
        norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
        field_simp [hden.ne']
        ring

theorem lemma6ChernoffDelta_nonneg (n Δ : ℕ) :
    0 ≤ lemma6ChernoffDelta n Δ := by
  unfold lemma6ChernoffDelta
  positivity

theorem lemma6ChernoffDelta_le_one
    {n Δ : ℕ} (hΔn : Δ < n) :
    lemma6ChernoffDelta n Δ ≤ 1 := by
  have hnR : (0 : ℝ) < n := by
    exact_mod_cast (Nat.zero_lt_of_lt hΔn)
  unfold lemma6ChernoffDelta
  rw [div_le_iff₀ (by positivity :
    (0 : ℝ) < 10 * (n : ℝ) + 2 * (Δ : ℝ))]
  nlinarith

theorem lemma6Deadline_mean
    {n Δ : ℕ} (hΔ0 : 0 < Δ) (hΔn : Δ < n) :
    (1 - lemma6ChernoffDelta n Δ) *
        (((5 * n : ℕ) : ℝ) * (lemma6SuccessP n Δ : ℝ)) =
      (5 * (n : ℝ)) / 2 + (Δ : ℝ) / 4 := by
  have hnR : (0 : ℝ) < n := by
    exact_mod_cast (lt_trans hΔ0 hΔn)
  rw [lemma6SuccessP_coe]
  unfold lemma6ChernoffDelta
  norm_num [Nat.cast_mul, Nat.cast_add]
  field_simp
  ring

theorem lemma6Deadline_cutoff
    {n Δ : ℕ} (hΔ0 : 0 < Δ) (hΔn : Δ < n) :
    (lemma6SuccessCutoff n Δ : ℝ) ≤
      (1 - lemma6ChernoffDelta n Δ) *
        (((5 * n : ℕ) : ℝ) * (lemma6SuccessP n Δ : ℝ)) := by
  have hfour : 4 * lemma6SuccessCutoff n Δ ≤ 10 * n + Δ := by
    unfold lemma6SuccessCutoff
    omega
  have hfourR :
      (4 : ℝ) * (lemma6SuccessCutoff n Δ : ℝ) ≤
        (10 * n + Δ : ℕ) := by
    exact_mod_cast hfour
  rw [lemma6Deadline_mean hΔ0 hΔn]
  norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hfourR
  nlinarith

theorem lemma6Deadline_exponent
    {n Δ : ℕ} (hΔ0 : 0 < Δ) (hΔn : Δ < n) :
    lemma6ChernoffDelta n Δ ^ 2 *
          (((5 * n : ℕ) : ℝ) *
            (lemma6SuccessP n Δ : ℝ)) / 2 =
      (Δ : ℝ) ^ 2 /
        (80 * (n : ℝ) + 16 * (Δ : ℝ)) := by
  have hnR : (0 : ℝ) < n := by
    exact_mod_cast (lt_trans hΔ0 hΔn)
  rw [lemma6SuccessP_coe]
  unfold lemma6ChernoffDelta
  norm_num [Nat.cast_mul, Nat.cast_add]
  field_simp
  ring

theorem lemma6Trace_low_success
    {r : RelaxedRate} {n x₀ y₀ Δ : ℕ}
    (hpop : x₀ + y₀ = n) (hgap : y₀ + Δ = x₀)
    (hΔ0 : 0 < Δ) (hΔn : Δ < n)
    (hfire : 0 < r.fire)
    (hrate :
      (1 : NNReal) ≤
        r.fire + (((Δ : ℕ) : NNReal) /
          (((2 * n : ℕ) : NNReal)))) :
    (∑' z : Lemma3Trace,
        if z.success ≤ lemma6SuccessCutoff n Δ then
          iter (lemma6TraceStep r n x₀ Δ) (5 * n)
            (lemma3Initial x₀) z
        else 0) ≤
      ENNReal.ofReal
        (Real.exp
          (-((Δ : ℝ) ^ 2 /
            (80 * (n : ℝ) + 16 * (Δ : ℝ))))) := by
  have hraw :=
    adapted_multiplicative_lower_tail
      (lemma6TraceStep r n x₀ Δ) Lemma3Trace.success
      (lemma3Initial x₀)
      (lemma6SuccessP n Δ) (lemma6SuccessP_le_one hΔn)
      (lemma6ChernoffDelta n Δ)
      (lemma6ChernoffDelta_nonneg n Δ)
      (lemma6ChernoffDelta_le_one hΔn)
      (5 * n) (lemma6SuccessCutoff n Δ)
      (lemma6Deadline_cutoff hΔ0 hΔn)
      (by rfl)
      (lemma6TraceStep_count_moment hpop hgap hΔ0 hΔn
        hfire hrate
        (ENNReal.ofReal
          (Real.exp (-lemma6ChernoffDelta n Δ)))
        (by
          rw [← ENNReal.ofReal_one]
          exact ENNReal.ofReal_le_ofReal <|
            Real.exp_le_one_iff.mpr
              (neg_nonpos.mpr
                (lemma6ChernoffDelta_nonneg n Δ))))
  have hneg :
      -(lemma6ChernoffDelta n Δ ^ 2 *
          (((5 * n : ℕ) : ℝ) *
            (lemma6SuccessP n Δ : ℝ))) / 2 =
        -((Δ : ℝ) ^ 2 /
          (80 * (n : ℝ) + 16 * (Δ : ℝ))) := by
    rw [neg_div, lemma6Deadline_exponent hΔ0 hΔn]
  rw [hneg] at hraw
  exact hraw

theorem lemma6Trace_terminal_cover
    {r : RelaxedRate} {n x₀ y₀ Δ : ℕ}
    (hpop : x₀ + y₀ = n) (hgap : y₀ + Δ = x₀)
    (hΔ0 : 0 < Δ) (hΔn : Δ < n)
    (hfire : 0 < r.fire)
    (z : Lemma3Trace)
    (hz :
      iter (lemma6TraceStep r n x₀ Δ) (5 * n)
        (lemma3Initial x₀) z ≠ 0)
    (htarget : ¬ Lemma3Target n Δ z.x) :
    Lemma3Bad x₀ Δ z.x ∨
      z.success ≤ lemma6SuccessCutoff n Δ := by
  have hinv :=
    lemma6Trace_iter_inv hpop hgap hΔ0 hΔn hfire z hz
  have hclock :=
    lemma6Trace_iter_clock z hz
  rcases hinv with hbad | hhit | hrel
  · exact Or.inl hbad
  · exact False.elim (htarget hhit)
  · right
    by_contra hsuccess
    have hs :
        lemma6SuccessCutoff n Δ + 1 ≤ z.success := by
      omega
    have hceil :
        10 * n + Δ ≤ 4 * (lemma6SuccessCutoff n Δ + 1) := by
      unfold lemma6SuccessCutoff
      omega
    have hdouble :
        n + 2 * Δ ≤ 2 * z.x := by
      omega
    apply htarget
    unfold Lemma3Target
    exact (Nat.add_le_add_left (min_le_left (2 * Δ) n) n).trans
      hdouble

theorem lemma6Trace_failure_split
    {r : RelaxedRate} {n x₀ y₀ Δ : ℕ}
    (hpop : x₀ + y₀ = n) (hgap : y₀ + Δ = x₀)
    (hΔ0 : 0 < Δ) (hΔn : Δ < n)
    (hfire : 0 < r.fire) :
    terminalFailureMass
        (iter (lemma6TraceStep r n x₀ Δ) (5 * n)
          (lemma3Initial x₀))
        (fun z => Lemma3Target n Δ z.x) ≤
      (∑' z : Lemma3Trace,
        if Lemma3Bad x₀ Δ z.x then
          iter (lemma6TraceStep r n x₀ Δ) (5 * n)
            (lemma3Initial x₀) z
        else 0) +
      ∑' z : Lemma3Trace,
        if z.success ≤ lemma6SuccessCutoff n Δ then
          iter (lemma6TraceStep r n x₀ Δ) (5 * n)
            (lemma3Initial x₀) z
        else 0 := by
  rw [← ENNReal.tsum_add]
  unfold terminalFailureMass
  refine ENNReal.tsum_le_tsum fun z => ?_
  let mass :=
    iter (lemma6TraceStep r n x₀ Δ) (5 * n)
      (lemma3Initial x₀) z
  by_cases hmass : mass = 0
  · simp [mass, hmass]
  · have hmass' :
        iter (lemma6TraceStep r n x₀ Δ) (5 * n)
          (lemma3Initial x₀) z ≠ 0 := by
      simpa [mass] using hmass
    by_cases htarget : Lemma3Target n Δ z.x
    · simp [htarget]
    · rcases lemma6Trace_terminal_cover
          hpop hgap hΔ0 hΔn hfire z hmass' htarget with hbad | hlow
      · simp [htarget, hbad]
      · simp [htarget, hlow]

theorem lemma6Trace_failure_explicit
    {r : RelaxedRate} {n x₀ y₀ Δ : ℕ}
    (hpop : x₀ + y₀ = n) (hgap : y₀ + Δ = x₀)
    (hΔ0 : 0 < Δ) (hΔn : Δ < n)
    (hfire : 0 < r.fire)
    (hrate :
      (1 : NNReal) ≤
        r.fire + (((Δ : ℕ) : NNReal) /
          (((2 * n : ℕ) : NNReal)))) :
    terminalFailureMass
        (iter (lemma6TraceStep r n x₀ Δ) (5 * n)
          (lemma3Initial x₀))
        (fun z => Lemma3Target n Δ z.x) ≤
      ENNReal.ofReal
          (Real.exp
            (-((Δ : ℝ) ^ 2 /
              (8 * (n : ℝ) + 4 * (Δ : ℝ))))) +
        ENNReal.ofReal
          (Real.exp
            (-((Δ : ℝ) ^ 2 /
              (80 * (n : ℝ) + 16 * (Δ : ℝ))))) := by
  calc
    terminalFailureMass
        (iter (lemma6TraceStep r n x₀ Δ) (5 * n)
          (lemma3Initial x₀))
        (fun z => Lemma3Target n Δ z.x) ≤
      (∑' z : Lemma3Trace,
        if Lemma3Bad x₀ Δ z.x then
          iter (lemma6TraceStep r n x₀ Δ) (5 * n)
            (lemma3Initial x₀) z
        else 0) +
      ∑' z : Lemma3Trace,
        if z.success ≤ lemma6SuccessCutoff n Δ then
          iter (lemma6TraceStep r n x₀ Δ) (5 * n)
            (lemma3Initial x₀) z
        else 0 :=
      lemma6Trace_failure_split hpop hgap hΔ0 hΔn hfire
    _ ≤ lemma6SafetyBase n Δ ^ lemma3Quarter Δ +
        ENNReal.ofReal
          (Real.exp
            (-((Δ : ℝ) ^ 2 /
              (80 * (n : ℝ) + 16 * (Δ : ℝ))))) :=
      add_le_add
        (lemma6Trace_bad_mass
          (T := 5 * n) hpop hgap hΔ0 hΔn hfire hrate)
        (lemma6Trace_low_success hpop hgap hΔ0 hΔn hfire hrate)
    _ ≤ ENNReal.ofReal
          (Real.exp
            (-((Δ : ℝ) ^ 2 /
              (8 * (n : ℝ) + 4 * (Δ : ℝ))))) +
        ENNReal.ofReal
          (Real.exp
            (-((Δ : ℝ) ^ 2 /
              (80 * (n : ℝ) + 16 * (Δ : ℝ))))) :=
      add_le_add (lemma6Safety_power_exp hΔ0 hΔn) le_rfl

theorem lemma6_explicit_errors_le_common
    {n Δ : ℕ} (hΔ0 : 0 < Δ) (hΔn : Δ < n) :
    ENNReal.ofReal
          (Real.exp
            (-((Δ : ℝ) ^ 2 /
              (8 * (n : ℝ) + 4 * (Δ : ℝ))))) +
        ENNReal.ofReal
          (Real.exp
            (-((Δ : ℝ) ^ 2 /
              (80 * (n : ℝ) + 16 * (Δ : ℝ))))) ≤
      (2 : ℝ≥0∞) *
        ENNReal.ofReal
          (Real.exp
            (-((Δ : ℝ) ^ 2 / (96 * (n : ℝ))))) := by
  have hnR : (0 : ℝ) < n := by
    exact_mod_cast (lt_trans hΔ0 hΔn)
  have hΔnR : (Δ : ℝ) < n := by
    exact_mod_cast hΔn
  have h96 : (0 : ℝ) < 96 * (n : ℝ) := by positivity
  have hsafe :
      (0 : ℝ) < 8 * (n : ℝ) + 4 * (Δ : ℝ) := by
    positivity
  have hdeadline :
      (0 : ℝ) < 80 * (n : ℝ) + 16 * (Δ : ℝ) := by
    positivity
  have hsafeDen :
      8 * (n : ℝ) + 4 * (Δ : ℝ) ≤
        96 * (n : ℝ) := by
    linarith
  have hdeadlineDen :
      80 * (n : ℝ) + 16 * (Δ : ℝ) ≤
        96 * (n : ℝ) := by
    linarith
  have hcommonSafety :
      (Δ : ℝ) ^ 2 / (96 * (n : ℝ)) ≤
        (Δ : ℝ) ^ 2 /
          (8 * (n : ℝ) + 4 * (Δ : ℝ)) := by
    rw [div_le_div_iff₀ h96 hsafe]
    exact mul_le_mul_of_nonneg_left hsafeDen (sq_nonneg (Δ : ℝ))
  have hcommonDeadline :
      (Δ : ℝ) ^ 2 / (96 * (n : ℝ)) ≤
        (Δ : ℝ) ^ 2 /
          (80 * (n : ℝ) + 16 * (Δ : ℝ)) := by
    rw [div_le_div_iff₀ h96 hdeadline]
    exact
      mul_le_mul_of_nonneg_left hdeadlineDen (sq_nonneg (Δ : ℝ))
  have hsafety :
      ENNReal.ofReal
          (Real.exp
            (-((Δ : ℝ) ^ 2 /
              (8 * (n : ℝ) + 4 * (Δ : ℝ))))) ≤
        ENNReal.ofReal
          (Real.exp
            (-((Δ : ℝ) ^ 2 / (96 * (n : ℝ))))) :=
    ENNReal.ofReal_le_ofReal <|
      Real.exp_le_exp.mpr (neg_le_neg hcommonSafety)
  have hdeadline' :
      ENNReal.ofReal
          (Real.exp
            (-((Δ : ℝ) ^ 2 /
              (80 * (n : ℝ) + 16 * (Δ : ℝ))))) ≤
        ENNReal.ofReal
          (Real.exp
            (-((Δ : ℝ) ^ 2 / (96 * (n : ℝ))))) :=
    ENNReal.ofReal_le_ofReal <|
      Real.exp_le_exp.mpr (neg_le_neg hcommonDeadline)
  calc
    ENNReal.ofReal
          (Real.exp
            (-((Δ : ℝ) ^ 2 /
              (8 * (n : ℝ) + 4 * (Δ : ℝ))))) +
        ENNReal.ofReal
          (Real.exp
            (-((Δ : ℝ) ^ 2 /
              (80 * (n : ℝ) + 16 * (Δ : ℝ))))) ≤
      ENNReal.ofReal
          (Real.exp
            (-((Δ : ℝ) ^ 2 / (96 * (n : ℝ))))) +
        ENNReal.ofReal
          (Real.exp
            (-((Δ : ℝ) ^ 2 / (96 * (n : ℝ))))) :=
      add_le_add hsafety hdeadline'
    _ = (2 : ℝ≥0∞) *
        ENNReal.ofReal
          (Real.exp
            (-((Δ : ℝ) ^ 2 / (96 * (n : ℝ))))) := by
      ring

/-- **Paper Lemma 6.**  Under the paper rate premise
`α + Δ/(2n) ≥ 1`, a positive binary gap doubles within exactly `5n`
productive reactions, except with exponentially small failure probability. -/
theorem lemma6_paper
    (r : RelaxedRate) (n x₀ y₀ Δ : ℕ)
    (hpop : x₀ + y₀ = n) (hgap : y₀ + Δ = x₀)
    (hΔ0 : 0 < Δ) (hΔn : Δ < n)
    (hrate :
      (1 : NNReal) ≤
        r.fire + (((Δ : ℕ) : NNReal) /
          (((2 * n : ℕ) : NNReal)))) :
    terminalFailureMass
        (iter
          (freeze (Lemma3Target n Δ) (relaxedProductiveTriChain r n))
          (5 * n) x₀)
        (Lemma3Target n Δ) ≤
      (2 : ℝ≥0∞) *
        ENNReal.ofReal
          (Real.exp
            (-((Δ : ℝ) ^ 2 / (96 * (n : ℝ))))) := by
  have hfire := lemma6_fire_pos hΔ0 hΔn hrate
  have hprojection :=
    targetFreeze_failure_le_lazy_projection
      (Lemma3Target n Δ)
      (relaxedProductiveTriChain r n)
      (lemma6TraceStep r n x₀ Δ)
      Lemma3Trace.toX
      (lemma6TraceStep_isLazyProjection r n x₀ Δ)
      (5 * n) (lemma3Initial x₀)
  have htrace :
      terminalFailureMass
          (iter (lemma6TraceStep r n x₀ Δ) (5 * n)
            (lemma3Initial x₀))
          (fun z => Lemma3Target n Δ z.x) ≤
        (2 : ℝ≥0∞) *
          ENNReal.ofReal
            (Real.exp
              (-((Δ : ℝ) ^ 2 / (96 * (n : ℝ))))) :=
    (lemma6Trace_failure_explicit hpop hgap hΔ0 hΔn hfire hrate).trans
      (lemma6_explicit_errors_le_common hΔ0 hΔn)
  calc
    terminalFailureMass
        (iter
          (freeze (Lemma3Target n Δ) (relaxedProductiveTriChain r n))
          (5 * n) x₀)
        (Lemma3Target n Δ) ≤
      terminalFailureMass
          (iter (lemma6TraceStep r n x₀ Δ) (5 * n)
            (lemma3Initial x₀))
          (fun z => Lemma3Target n Δ z.x) := by
      simpa [Lemma3Trace.toX, lemma3Initial] using hprojection
    _ ≤ (2 : ℝ≥0∞) *
        ENNReal.ofReal
          (Real.exp
            (-((Δ : ℝ) ^ 2 / (96 * (n : ℝ))))) :=
      htrace

example :
    terminalFailureMass
        (iter
          (freeze (Lemma3Target 4 2)
            (relaxedProductiveTriChain
              ({ fire := 1, idle := 0, add_eq_one := by norm_num } :
                RelaxedRate) 4))
          (5 * 4) 3)
        (Lemma3Target 4 2) ≤
      (2 : ℝ≥0∞) *
        ENNReal.ofReal
          (Real.exp
            (-(((2 : ℕ) : ℝ) ^ 2 / (96 * ((4 : ℕ) : ℝ))))) := by
  simpa using
    lemma6_paper
      ({ fire := 1, idle := 0, add_eq_one := by norm_num } : RelaxedRate)
      4 3 1 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by
        rw [← NNReal.coe_le_coe]
        norm_num [NNReal.coe_add, NNReal.coe_div])

end Tri

#print axioms Tri.lemma6Beta_coe
#print axioms Tri.lemma6SuccessP_le_beta_prob
#print axioms Tri.lemma6_live_guard
#print axioms Tri.relaxedProductiveDirectionPMF
#print axioms Tri.lemma6TraceStep_clock_of_apply_ne_zero
#print axioms Tri.lemma6TraceStep_support
#print axioms Tri.lemma6TraceStep_isLazyProjection
#print axioms Tri.lemma6TraceStep_count_moment
#print axioms Tri.lemma6TraceStep_safety_moment
#print axioms Tri.lemma6Trace_bad_mass
#print axioms Tri.lemma6Trace_low_success
#print axioms Tri.lemma6Trace_failure_explicit
#print axioms Tri.lemma6_paper
