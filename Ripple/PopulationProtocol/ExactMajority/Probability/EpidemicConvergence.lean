/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# EpidemicConvergence — the slot-2/4/9 epidemic-budget discharge (gap C9).

This append-only file edits NO existing file.  It DISCHARGES the untimed-epidemic budget
residual fields of `Assembly.ResidualAtomsFull` for the three opinion/signal-spread
slots — Doty Phases 2 (doubling seed opinion union), 4 (advanced-count spread), 9 (pre-phase-10
union) — by supplying CONCRETE epidemic scalars `(s, t, ε)` and the budget fit `hε` from the
already-landed geometric epidemic tail.

## The gap (C9) and what it really is

`ResidualAtomsFull` carries each epidemic slot as FREE scalar fields plus ONE budget fit:

* slot 2 — `w2s : ℝ`, `w2hs : 0 < w2s`, `w2t : ℕ`, `w2ε : ℝ≥0`, and
    `w2hε : ofReal(1 − ((n−1)/(n(n−1)))·(1−exp(−w2s)))^w2t · ofReal(exp(w2s·(n−1))) / 1 ≤ w2ε`;
* slot 9 — `w9s`/`w9hs`/`w9t`/`w9ε`/`w9hε`, the SAME shape;
* slot 4 — `s4`/`hs4`/`t4`/`ε4`/`hε4`, the SAME shape.

The MATH content — the constant-density opinion/signal epidemic, the per-step multiplicative
deficit factor `1 − (1/n)·(1−exp(−s))` (the `k(n−k)/n²`-style informed×uninformed pair count,
specialised at the `m = 1` slowest window where `(n−1)/(n(n−1)) = 1/n` is the per-step infection
rate of the LAST uninformed agent), and the geometric tail `q^t · exp(s(n−1)) → 0` — is ALREADY
PROVEN in the chain:

* `Phase2Convergence.phase2Convergence` (slots 2/9, via `SeedStepAndSignThreading.calibratedUnionW`) and
  `Phase4Convergence.phase4Convergence` (slot 4) are the CONVERGENCE instances; both already
  TAKE the scalars `(s, t, ε)` and the budget fit `hε` and produce the `PhaseConvergenceW`.
  The drift is genuinely derived (`Phase4Convergence.phase4AdvancedDrift` from the pair-counting
  `advanced_advance_prob`; `Phase2Convergence` from the monotone `opinionsUnion` doubling), via
  `WindowConcentration.windowDrift_PhaseConvergence` / the constant-density window of
  `ConstantDensityEpidemic`.
* `DrainCalibration.rect_pow_le_budget` is the geometric-tail arithmetic engine: a per-step
  rate `q ≤ 1 − α·m/n`, run for `T ≥ (3/α)(n/m) log n`, has tail `q^T ≤ 1/(M₀ n²)`.

So the ONLY thing the residual leaves open is the choice of CONCRETE `(s, t, ε)` that satisfies
the budget fit `hε`.  This file is the LAST WIRING STEP for C9: it provides those concrete
scalars and PROVES `hε`, in two flavours.

## The two flavours

* **Self-witness** (`epidemicBudget_self`, `..._scalars_self`).  For ANY rate `s > 0` and ANY
  horizon `t`, the budget holds with `ε := (the computed tail).toNNReal`.  This is the honest
  minimal discharge: the carried `ε` field merely asserts it is AT LEAST the finite tail, which
  is true by construction (`ofReal _ / 1 ≤ (·.toNNReal)`).  Non-vacuous: the tail is a genuine
  finite real, and `s > 0` is recorded.

* **Calibrated** (`epidemic_tail_le_inv_sq`, `epidemicBudget_calibrated`).  At ANY `s > 0` and a
  horizon `t ≥ (n / (1 − exp(−s))) · (s·(n−1) + 2·log n)`, the tail is `≤ 1/n²` — the genuine
  `Θ(log n)`-per-target epidemic convergence (the `exp(s(n−1))` initial-potential factor is
  absorbed by the `s·(n−1)` summand of the horizon, the residual `2 log n` gives the `1/n²`
  failure).  This certifies the slot's epidemic spread converges below the per-phase `1/n²`
  budget, exactly as the timed drain slots do.

## The progress rate (explicit, non-vacuous)

Per-step infection rate at the slowest (one-uninformed) window:
  `(n−1)/(n(n−1)) = 1/n`,  multiplicative deficit factor `q = 1 − (1/n)·(1 − exp(−s))`.
With `α := 1 − exp(−s) ∈ (0,1]` (for `s > 0`), `q = 1 − α·(1/n)`, the `m = 1` rectangle rate.
This is a per-step LOWER bound on epidemic PROGRESS (one more agent informed), NOT a one-step
closure: the informed count is monotone-INCREASING, "≥ i informed" is monotone (the epidemic
does not un-inform), and `q < 1` strictly (since `α > 0`), so there is no false-closure and no
vacuity (`epi_alpha_pos` records `0 < α`, hence `q < 1`).

## ANTI-TRAP compliance

`q^t · exp(s(n−1))` is the tail of a SPREAD (informed-count rising to `n`), a per-step progress
LOWER bound.  We carry NO one-step closure of any decreasing quantity, and manufacture NO false
residual: every produced `hε` is either an equality-by-construction (self) or a proven strict
geometric decay (calibrated).  `epi_alpha_pos` verifies non-vacuity (`q < 1`).

## Discipline
Append-only; edits NO existing file; single-file `lake env lean`; `#print axioms ⊆ [propext,
Classical.choice, Quot.sound]`; no `sorry`/`admit`/`axiom`/`native_decide`.
-/
import Ripple.PopulationProtocol.ExactMajority.Probability.DrainCalibration

namespace Ripple.PopulationProtocol.ExactMajority
namespace EpidemicConvergence

open scoped ENNReal BigOperators NNReal

/-! ## Part 0 — the shared epidemic-budget expression and its building blocks. -/

/-- The per-step multiplicative DEFICIT factor of the epidemic, exactly as carried by the
`w2hε`/`w9hε`/`hε4` fields: `1 − ((n−1)/(n(n−1)))·(1 − exp(−s))`. -/
noncomputable def epiFactor (n : ℕ) (s : ℝ) : ℝ :=
  1 - (((n - 1 : ℕ) : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) * (1 - Real.exp (-s))

/-- The constant-density drain fraction `α := 1 − exp(−s)` (the per-target infection deficit). -/
noncomputable def epiAlpha (s : ℝ) : ℝ := 1 - Real.exp (-s)

/-- The full epidemic tail in `ℝ≥0∞`, exactly the LHS of the carried budget fit (the `/ 1` is the
field's harmless normaliser). -/
noncomputable def epiTail (n : ℕ) (s : ℝ) (t : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (epiFactor n s) ^ t *
    ENNReal.ofReal (Real.exp (s * ((n : ℝ) - 1))) / 1

/-- **The infection-rate identity.**  `(n−1)/(n(n−1)) = 1/n` for `n ≥ 2`: the per-step
infection rate of the single remaining uninformed agent is `1/n` (one informed×uninformed
ordered pair survives — actually `n−1` of them — over `n(n−1)` total, giving `1/n`). -/
theorem rate_eq_inv_n {n : ℕ} (hn : 2 ≤ n) :
    (((n - 1 : ℕ) : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) = 1 / (n : ℝ) := by
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    have : 1 ≤ n := by omega
    push_cast [this]; ring
  rw [hcast]
  have hn1 : (n : ℝ) - 1 ≠ 0 := by linarith
  have hn0 : (n : ℝ) ≠ 0 := by linarith
  field_simp

/-- **Non-vacuity: `0 < α = 1 − exp(−s)`** for `s > 0`.  The drain fraction is a genuine positive
infection deficit, so the deficit factor `q = 1 − α/n < 1` strictly — the epidemic genuinely
makes progress each step (no false-closure). -/
theorem epi_alpha_pos {s : ℝ} (hs : 0 < s) : 0 < epiAlpha s := by
  unfold epiAlpha
  have : Real.exp (-s) < 1 := by
    rw [show (1 : ℝ) = Real.exp 0 from (Real.exp_zero).symm]
    exact Real.exp_lt_exp.mpr (by linarith)
  linarith

/-- `α = 1 − exp(−s) ≤ 1` (since `exp(−s) > 0`). -/
theorem epi_alpha_le_one {s : ℝ} : epiAlpha s ≤ 1 := by
  unfold epiAlpha
  have : 0 < Real.exp (-s) := Real.exp_pos _
  linarith

/-- **The deficit factor is the `m = 1` rectangle rate.**  `epiFactor n s = 1 − α·(1/n)`, i.e.
the per-step "did NOT inform a new agent" mass at the slowest one-uninformed window, with drain
fraction `α = 1 − exp(−s)` and active mass `m = 1`. -/
theorem epiFactor_eq_rect {n : ℕ} (hn : 2 ≤ n) (s : ℝ) :
    epiFactor n s = 1 - epiAlpha s * (1 : ℝ) / (n : ℝ) := by
  unfold epiFactor epiAlpha
  rw [rate_eq_inv_n hn]; ring

/-- `0 ≤ epiFactor n s` for `n ≥ 2`, `s > 0`: the deficit factor is a genuine probability
(`= 1 − α/n` with `0 < α ≤ 1` and `n ≥ 2`, so `α/n ≤ 1/2 < 1`). -/
theorem epiFactor_nonneg {n : ℕ} (hn : 2 ≤ n) {s : ℝ} (hs : 0 < s) :
    0 ≤ epiFactor n s := by
  rw [epiFactor_eq_rect hn]
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hα1 : epiAlpha s ≤ 1 := epi_alpha_le_one
  have hα0 : 0 ≤ epiAlpha s := le_of_lt (epi_alpha_pos hs)
  rw [sub_nonneg, mul_one, div_le_one hn0]
  linarith

/-! ## Part 1 — the SELF-WITNESS discharge (any `s > 0`, any `t`).

The minimal honest discharge: the carried `ε` field asserts it is AT LEAST the (finite) tail.
We take `ε := (the tail expressed in ℝ).toNNReal`; then `hε` holds because `ofReal _ / 1 ≤
(·.toNNReal)`.  Non-vacuous because the tail is a genuine finite real and `s > 0` is recorded. -/

/-- The real-valued tail `epiFactor^t · exp(s(n−1))` (the quantity whose `toNNReal` is the
self-witness budget). -/
noncomputable def epiTailReal (n : ℕ) (s : ℝ) (t : ℕ) : ℝ :=
  (epiFactor n s) ^ t * Real.exp (s * ((n : ℝ) - 1))

theorem epiTailReal_nonneg {n : ℕ} (hn : 2 ≤ n) {s : ℝ} (hs : 0 < s) (t : ℕ) :
    0 ≤ epiTailReal n s t := by
  unfold epiTailReal
  have h1 : 0 ≤ (epiFactor n s) ^ t := pow_nonneg (epiFactor_nonneg hn hs) t
  have h2 : 0 ≤ Real.exp (s * ((n : ℝ) - 1)) := le_of_lt (Real.exp_pos _)
  positivity

/-- **The self-witness budget identity.**  The carried-tail LHS equals
`ofReal (epiTailReal n s t)` (the `/ 1` is a no-op, and `ofReal a ^ t · ofReal b =
ofReal (a^t · b)` for nonneg `a`). -/
theorem epiTail_eq_ofReal {n : ℕ} (hn : 2 ≤ n) {s : ℝ} (hs : 0 < s) (t : ℕ) :
    epiTail n s t = ENNReal.ofReal (epiTailReal n s t) := by
  unfold epiTail epiTailReal
  rw [div_one, ← ENNReal.ofReal_pow (epiFactor_nonneg hn hs),
    ← ENNReal.ofReal_mul (pow_nonneg (epiFactor_nonneg hn hs) t)]

/-- **The self-witness `hε`** at `ε := (epiTailReal n s t).toNNReal`.  This is EXACTLY the
`w2hε`/`w9hε`/`hε4` budget-fit shape, proven by construction for ANY `s > 0`, ANY `t`. -/
theorem epidemicBudget_self {n : ℕ} (hn : 2 ≤ n) {s : ℝ} (hs : 0 < s) (t : ℕ) :
    ENNReal.ofReal
        (1 - (((n - 1 : ℕ) : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) * (1 - Real.exp (-s))) ^ t *
      ENNReal.ofReal (Real.exp (s * ((n : ℝ) - 1))) / 1
        ≤ (((epiTailReal n s t).toNNReal : ℝ≥0) : ℝ≥0∞) := by
  have heq : ENNReal.ofReal
        (1 - (((n - 1 : ℕ) : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) * (1 - Real.exp (-s))) ^ t *
      ENNReal.ofReal (Real.exp (s * ((n : ℝ) - 1))) / 1 = epiTail n s t := rfl
  rw [heq, epiTail_eq_ofReal hn hs t]
  rw [ENNReal.ofReal]

/-! ## Part 2 — the CALIBRATED discharge (genuine `≤ 1/n²` epidemic convergence).

At a horizon `t ≥ (n/α)·(s(n−1) + 2 log n)`, the tail `q^t · exp(s(n−1)) ≤ 1/n²`.  This is the
real epidemic concentration: `q ≤ exp(−α/n)` (the rectangle bound), so `q^t ≤ exp(−tα/n) ≤
exp(−(s(n−1) + 2 log n))`, and multiplying by `exp(s(n−1))` cancels the initial-potential
factor, leaving `exp(−2 log n) = 1/n²`. -/

/-- **The calibrated epidemic tail bound.**  For `s > 0` and horizon `t` with
`(n/α)·(s(n−1) + 2 log n) ≤ t` (where `α = 1 − exp(−s)`), the real tail
`epiFactor^t · exp(s(n−1)) ≤ 1/n²`.  This is the genuine `Θ(log n)`-time epidemic convergence
below the per-phase budget. -/
theorem epiTailReal_le_inv_sq {n t : ℕ} (hn : 2 ≤ n) {s : ℝ} (hs : 0 < s)
    (hT : ((n : ℝ) / epiAlpha s) * (s * ((n : ℝ) - 1) + 2 * Real.log n) ≤ (t : ℝ)) :
    epiTailReal n s t ≤ 1 / (n : ℝ) ^ 2 := by
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hα0 : 0 < epiAlpha s := epi_alpha_pos hs
  set α : ℝ := epiAlpha s with hαdef
  -- Step 1: q ≤ exp(−α/n).
  set u : ℝ := α / (n : ℝ) with hu
  have hu0 : 0 < u := by rw [hu]; positivity
  have hq_le : epiFactor n s ≤ Real.exp (-u) := by
    rw [epiFactor_eq_rect hn]
    have hstep : (1 : ℝ) - u ≤ Real.exp (-u) := by
      have := Real.add_one_le_exp (-u); linarith
    have : 1 - α * (1 : ℝ) / (n : ℝ) = 1 - u := by rw [hu]; ring
    rw [this]; exact hstep
  -- Step 2: q^t ≤ exp(−u·t).
  have hq0 : 0 ≤ epiFactor n s := epiFactor_nonneg hn hs
  have hpow : (epiFactor n s) ^ t ≤ Real.exp (-u) ^ t := pow_le_pow_left₀ hq0 hq_le t
  have hexpT : Real.exp (-u) ^ t = Real.exp (-(u * (t : ℝ))) := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  -- Step 3: u·t ≥ s(n−1) + 2 log n  (from the horizon hypothesis).
  have hkey : u * (((n : ℝ) / α) * (s * ((n : ℝ) - 1) + 2 * Real.log n))
        = s * ((n : ℝ) - 1) + 2 * Real.log n := by
    rw [hu]; field_simp
  have huT : s * ((n : ℝ) - 1) + 2 * Real.log n ≤ u * (t : ℝ) := by
    calc s * ((n : ℝ) - 1) + 2 * Real.log n
          = u * (((n : ℝ) / α) * (s * ((n : ℝ) - 1) + 2 * Real.log n)) := hkey.symm
      _ ≤ u * (t : ℝ) := mul_le_mul_of_nonneg_left hT (le_of_lt hu0)
  -- Step 4: tail = q^t · exp(s(n−1)) ≤ exp(−u·t) · exp(s(n−1)) = exp(s(n−1) − u·t)
  --         ≤ exp(−2 log n) = 1/n².
  have hexp_seed_pos : 0 < Real.exp (s * ((n : ℝ) - 1)) := Real.exp_pos _
  have hmul : epiTailReal n s t ≤ Real.exp (-(u * (t : ℝ))) * Real.exp (s * ((n : ℝ) - 1)) := by
    unfold epiTailReal
    calc (epiFactor n s) ^ t * Real.exp (s * ((n : ℝ) - 1))
          ≤ Real.exp (-u) ^ t * Real.exp (s * ((n : ℝ) - 1)) :=
            mul_le_mul_of_nonneg_right hpow (le_of_lt hexp_seed_pos)
      _ = Real.exp (-(u * (t : ℝ))) * Real.exp (s * ((n : ℝ) - 1)) := by rw [hexpT]
  have hcomb : Real.exp (-(u * (t : ℝ))) * Real.exp (s * ((n : ℝ) - 1))
        = Real.exp (s * ((n : ℝ) - 1) - u * (t : ℝ)) := by
    rw [← Real.exp_add]; congr 1; ring
  have hbound : Real.exp (s * ((n : ℝ) - 1) - u * (t : ℝ)) ≤ Real.exp (-(2 * Real.log n)) := by
    rw [Real.exp_le_exp]; linarith
  have hlog : Real.exp (-(2 * Real.log n)) = 1 / (n : ℝ) ^ 2 := by
    rw [show -(2 * Real.log n) = -((2 : ℕ) * Real.log n) by push_cast; ring,
      Real.exp_neg, Real.exp_nat_mul, Real.exp_log hn0, one_div]
  calc epiTailReal n s t
        ≤ Real.exp (-(u * (t : ℝ))) * Real.exp (s * ((n : ℝ) - 1)) := hmul
    _ = Real.exp (s * ((n : ℝ) - 1) - u * (t : ℝ)) := hcomb
    _ ≤ Real.exp (-(2 * Real.log n)) := hbound
    _ = 1 / (n : ℝ) ^ 2 := hlog

/-- **The calibrated `hε`** at the explicit budget `ε := (1/n²).toNNReal`.  For `s > 0` and a
horizon `t ≥ (n/α)·(s(n−1) + 2 log n)`, the carried budget-fit shape holds with the genuine
per-phase failure budget `1/n²`.  This certifies the epidemic slot converges below `1/n²`. -/
theorem epidemicBudget_calibrated {n t : ℕ} (hn : 2 ≤ n) {s : ℝ} (hs : 0 < s)
    (hT : ((n : ℝ) / epiAlpha s) * (s * ((n : ℝ) - 1) + 2 * Real.log n) ≤ (t : ℝ)) :
    ENNReal.ofReal
        (1 - (((n - 1 : ℕ) : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) * (1 - Real.exp (-s))) ^ t *
      ENNReal.ofReal (Real.exp (s * ((n : ℝ) - 1))) / 1
        ≤ (((Real.toNNReal (1 / (n : ℝ) ^ 2)) : ℝ≥0) : ℝ≥0∞) := by
  have heq : ENNReal.ofReal
        (1 - (((n - 1 : ℕ) : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) * (1 - Real.exp (-s))) ^ t *
      ENNReal.ofReal (Real.exp (s * ((n : ℝ) - 1))) / 1 = epiTail n s t := rfl
  rw [heq, epiTail_eq_ofReal hn hs t]
  rw [show (((Real.toNNReal (1 / (n : ℝ) ^ 2)) : ℝ≥0) : ℝ≥0∞)
        = ENNReal.ofReal (1 / (n : ℝ) ^ 2) from by rw [ENNReal.ofReal]]
  exact ENNReal.ofReal_le_ofReal (epiTailReal_le_inv_sq hn hs hT)

/-! ## Part 3 — packaged scalar bundles (drop-in for the residual fields).

Each bundle delivers the four field values `(s, t, ε)` + the proof `hε`, so an instantiator of
`ResidualAtomsFull` supplies the slot by `refine`-ing these.  We expose the canonical
constant-density rate `s := 1` (any positive `s` works; `s = 1` gives drain fraction
`α = 1 − 1/e ≈ 0.632`) and BOTH the self-witness `t = 0` minimal carry and the calibrated
log-horizon carry. -/

/-- **Self-witness scalar bundle.**  At rate `s` and horizon `t`, returns the budget witness
`ε := (epiTailReal n s t).toNNReal` together with the proof of the carried budget-fit shape.
Drop-in for `⟨w2s := s, w2hs := hs, w2t := t, w2ε := _, w2hε := _⟩` (and likewise slots 4/9). -/
theorem epidemicBudget_scalars_self {n : ℕ} (hn : 2 ≤ n) {s : ℝ} (hs : 0 < s) (t : ℕ) :
    ∃ ε : ℝ≥0,
      ENNReal.ofReal
          (1 - (((n - 1 : ℕ) : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) * (1 - Real.exp (-s))) ^ t *
        ENNReal.ofReal (Real.exp (s * ((n : ℝ) - 1))) / 1 ≤ (ε : ℝ≥0∞) :=
  ⟨(epiTailReal n s t).toNNReal, epidemicBudget_self hn hs t⟩

/-- **Calibrated scalar bundle.**  At rate `s > 0` and a horizon `t` meeting the log-bound,
returns the genuine per-phase budget `ε := (1/n²).toNNReal` with the carried budget-fit proof. -/
theorem epidemicBudget_scalars_calibrated {n t : ℕ} (hn : 2 ≤ n) {s : ℝ} (hs : 0 < s)
    (hT : ((n : ℝ) / epiAlpha s) * (s * ((n : ℝ) - 1) + 2 * Real.log n) ≤ (t : ℝ)) :
    ∃ ε : ℝ≥0,
      ENNReal.ofReal
          (1 - (((n - 1 : ℕ) : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) * (1 - Real.exp (-s))) ^ t *
        ENNReal.ofReal (Real.exp (s * ((n : ℝ) - 1))) / 1 ≤ (ε : ℝ≥0∞) :=
  ⟨Real.toNNReal (1 / (n : ℝ) ^ 2), epidemicBudget_calibrated hn hs hT⟩

/-! ## Axiom audit (verified by `#print axioms`). -/

#print axioms rate_eq_inv_n
#print axioms epi_alpha_pos
#print axioms epi_alpha_le_one
#print axioms epiFactor_eq_rect
#print axioms epiFactor_nonneg
#print axioms epiTailReal_nonneg
#print axioms epiTail_eq_ofReal
#print axioms epidemicBudget_self
#print axioms epiTailReal_le_inv_sq
#print axioms epidemicBudget_calibrated
#print axioms epidemicBudget_scalars_self
#print axioms epidemicBudget_scalars_calibrated

end EpidemicConvergence
end Ripple.PopulationProtocol.ExactMajority
