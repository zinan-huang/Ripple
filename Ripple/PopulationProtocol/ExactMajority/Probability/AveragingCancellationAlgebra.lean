import Ripple.PopulationProtocol.ExactMajority.Probability.StageEventSpec
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-!
# Arithmetic for the reviewed averaging argument

This file supplies the logarithmic jump estimate, the worst outside-mass
allocation, the cancellation-table margins, and the complete raw interaction
budget. It does not construct the mixed-phase potential supermartingale or
claim the N13 probability estimate.
-/

noncomputable section

namespace Ripple.PopulationProtocol.ExactMajority.AveragingCancellationAlgebra

open TimeTheorem StageEventSpec

/-- The endpoint of a small downward jump is positive even when the jump crosses
the stopping threshold. The estimate controls the absolute logarithmic jump. -/
theorem log_decrease_abs_le {x y D : ℝ}
    (hx : 0 < x) (hyx : y ≤ x)
    (hdrop : x - y ≤ D) (hsmall : D ≤ x / 2) :
    0 < y ∧ |Real.log y - Real.log x| ≤ 2 * D / x := by
  have hy : 0 < y := by linarith
  have hD : 0 ≤ D := by linarith
  have hhalf : x ≤ 2 * y := by linarith
  have hmul : (x - y) * x ≤ D * x :=
    mul_le_mul_of_nonneg_right hdrop hx.le
  have hmul' : D * x ≤ D * (2 * y) :=
    mul_le_mul_of_nonneg_left hhalf hD
  have hquot : x / y - 1 ≤ 2 * D / x := by
    apply (le_div_iff₀ hx).2
    calc
      (x / y - 1) * x = (x - y) * x / y := by
        field_simp [ne_of_gt hy] <;> ring
      _ ≤ 2 * D := (div_le_iff₀ hy).2 (by nlinarith only [hmul, hmul'])
  have hlog := Real.log_le_sub_one_of_pos (div_pos hx hy)
  rw [Real.log_div (ne_of_gt hx) (ne_of_gt hy)] at hlog
  refine ⟨hy, ?_⟩
  rw [abs_of_nonpos (sub_nonpos.mpr (Real.log_le_log hy hyx))]
  linarith only [hlog, hquot]

/-- Allocating at most δ outside the current level gives the worst product by
putting all that loss on the minority side. Here x is the loss on the majority
side, and A and B are the current-level populations in the same units. -/
theorem cancellation_product_lower {a b δ x A B : ℝ}
    (hab : b ≤ a) (hδb : δ ≤ b) (hx : 0 ≤ x) (hxδ : x ≤ δ)
    (hA : a - x ≤ A) (hB : b - δ + x ≤ B) :
    a * (b - δ) ≤ A * B := by
  have hleft : 0 ≤ a - x := by linarith
  have hright : 0 ≤ b - δ + x := by linarith
  have hconcave : a * (b - δ) ≤ (a - x) * (b - δ + x) := by
    have hproduct : 0 ≤ x * (a - b + δ - x) :=
      mul_nonneg hx (by linarith)
    nlinarith only [hproduct]
  exact hconcave.trans
    (mul_le_mul hA hB hright (hleft.trans hA))

/-- The preceding lower bound also applies when the total outside loss is only
bounded above by δ. -/
theorem cancellation_product_lower_of_outside_bound {a b δ x y A B : ℝ}
    (hab : b ≤ a) (hδb : δ ≤ b) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (houtside : x + y ≤ δ) (hA : a - x ≤ A) (hB : b - y ≤ B) :
    a * (b - δ) ≤ A * B := by
  apply cancellation_product_lower hab hδb hx
    (by linarith) hA
  linarith

/-- The six total-mass rows and five minority-mass rows in AVERAGING Lemma 7. -/
inductive CancellationRegime where
  | early
  | totalFourth
  | totalThird
  | totalSecond
  | totalPrevious
  | totalTerminal
  | minorityFourth
  | minorityThird
  | minoritySecond
  | minorityPrevious
  | minorityTerminal
  deriving DecidableEq

/-- Lower populations A, B and maximum required cancellations d, in units of M. -/
def cancellationParameters : CancellationRegime → ℝ × ℝ × ℝ
  | .early => (625 / 10000, 343 / 10000, 5 / 100)
  | .totalFourth => (77 / 1000, 238 / 10000, 48 / 1000)
  | .totalThird => (115 / 1000, 118 / 10000, 39 / 1000)
  | .totalSecond => (206 / 1000, 28 / 10000, 24 / 1000)
  | .totalPrevious => (404 / 1000, 8 / 10000, 8 / 1000)
  | .totalTerminal => (804 / 1000, 8 / 10000, 4 / 1000)
  | .minorityFourth => (625 / 10000, 343 / 10000, 5 / 100)
  | .minorityThird => (767 / 10000, 235 / 10000, 483 / 10000)
  | .minoritySecond => (1145 / 10000, 113 / 10000, 389 / 10000)
  | .minorityPrevious => (2056 / 10000, 24 / 10000, 234 / 10000)
  | .minorityTerminal => (404 / 1000, 8 / 10000, 72 / 10000)

theorem cancellation_parameters_nonneg (r : CancellationRegime) :
    0 ≤ (cancellationParameters r).1 ∧
      0 ≤ (cancellationParameters r).2.1 ∧
      0 ≤ (cancellationParameters r).2.2 := by
  cases r <;> norm_num [cancellationParameters]

/-- Uniform slack across all eleven rows. The smallest seven-tenths-log margin
is 0.0033576, attained by the penultimate minority row. -/
theorem cancellation_margin (r : CancellationRegime) :
    (3 / 1000 : ℝ) <
      40 * (cancellationParameters r).1 * (cancellationParameters r).2.1 -
        (cancellationParameters r).2.2 * Real.log 2 := by
  have hlog : Real.log 2 < (7 / 10 : ℝ) := by
    linarith [Real.log_two_lt_d9]
  cases r <;> norm_num [cancellationParameters] <;> linarith

/-- Numerical specialization of the exponent in the adapted-success tail.
The hypotheses here are arithmetic work/count bounds, not a claim that the
protocol has already supplied its conditional cancellation probability. -/
theorem cancellation_exponent_bound (r : CancellationRegime)
    {M k N p : ℝ} (hM : 0 ≤ M)
    (hk : k ≤ (cancellationParameters r).2.2 * M)
    (hwork :
      80 * (cancellationParameters r).1 * (cancellationParameters r).2.1 * M ≤
        N * p) :
    Real.exp (k * Real.log 2 - N * p / 2) ≤ Real.exp (-M / 1000) := by
  have hcoeff :
      (cancellationParameters r).2.2 * Real.log 2 -
        40 * (cancellationParameters r).1 * (cancellationParameters r).2.1 ≤
          -(1 / 1000 : ℝ) := by
    linarith [cancellation_margin r]
  have hscaled := mul_le_mul_of_nonneg_right hcoeff hM
  have hklog := mul_le_mul_of_nonneg_right hk
    (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))
  apply Real.exp_le_exp.mpr
  nlinarith only [hscaled, hklog, hwork]

/-- The consecutive warmup, potential-drain and cancellation blocks, counted
in raw ordered-pair draws. Here M and C are counts, not densities. -/
def rawWork (n M C : ℕ) : ℕ :=
  Nat.ceil ((5 : ℝ) * (n : ℝ) ^ 2 / (C : ℝ)) +
    Nat.ceil ((60 : ℝ) * (n : ℝ) ^ 2 / (M : ℝ)) +
    Nat.ceil ((40 : ℝ) * (n : ℝ) ^ 2 / (M : ℝ))

/-- The density bounds leave enough room for all three ceiling errors. -/
theorem raw_work_lt_density_bound {n M C : ℕ}
    (hn : 0 < n) (hC : 0 < C)
    (hmain : 12 * n ≤ 25 * M) (hclock : 25 * C ≤ 7 * n) :
    (rawWork n M C : ℝ) < 70 * (n : ℝ) ^ 2 / (C : ℝ) := by
  have hM : 0 < M := by omega
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt hn)
  have hMR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hCR : (0 : ℝ) < (C : ℝ) := by exact_mod_cast hC
  have hmR : 12 * (n : ℝ) ≤ 25 * (M : ℝ) := by exact_mod_cast hmain
  have hcR : 25 * (C : ℝ) ≤ 7 * (n : ℝ) := by exact_mod_cast hclock
  have hratio : 12 * (C : ℝ) ≤ 7 * (M : ℝ) := by
    nlinarith only [hmR, hcR]
  have hmainBlock :
      100 * (n : ℝ) ^ 2 / (M : ℝ) ≤
        (175 / 3 : ℝ) * (n : ℝ) ^ 2 / (C : ℝ) := by
    apply (div_le_div_iff₀ hMR hCR).2
    have hmul := mul_le_mul_of_nonneg_left hratio
      (show 0 ≤ (25 / 3 : ℝ) * (n : ℝ) ^ 2 by positivity)
    nlinarith only [hmul]
  have hnn : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
    nlinarith only [hnR, sq_nonneg ((n : ℝ) - 1)]
  have hslack : (3 : ℝ) < (20 / 3 : ℝ) * (n : ℝ) ^ 2 / (C : ℝ) := by
    apply (lt_div_iff₀ hCR).2
    nlinarith only [hcR, hnR, hnn]
  have hwarm :
      (Nat.ceil ((5 : ℝ) * (n : ℝ) ^ 2 / (C : ℝ)) : ℝ) <
        (5 : ℝ) * (n : ℝ) ^ 2 / (C : ℝ) + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hpotential :
      (Nat.ceil ((60 : ℝ) * (n : ℝ) ^ 2 / (M : ℝ)) : ℝ) <
        (60 : ℝ) * (n : ℝ) ^ 2 / (M : ℝ) + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hcancel :
      (Nat.ceil ((40 : ℝ) * (n : ℝ) ^ 2 / (M : ℝ)) : ℝ) <
        (40 : ℝ) * (n : ℝ) ^ 2 / (M : ℝ) + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hceil :
      (rawWork n M C : ℝ) <
        5 * (n : ℝ) ^ 2 / (C : ℝ) +
          100 * (n : ℝ) ^ 2 / (M : ℝ) + 3 := by
    dsimp only [rawWork]
    push_cast
    calc
      _ < (5 * (n : ℝ) ^ 2 / (C : ℝ) + 1) +
          (60 * (n : ℝ) ^ 2 / (M : ℝ) + 1) +
          (40 * (n : ℝ) ^ 2 / (M : ℝ) + 1) :=
        add_lt_add (add_lt_add hwarm hpotential) hcancel
      _ = 5 * (n : ℝ) ^ 2 / (C : ℝ) +
          100 * (n : ℝ) ^ 2 / (M : ℝ) + 3 := by ring
  calc
    (rawWork n M C : ℝ) <
        5 * (n : ℝ) ^ 2 / (C : ℝ) +
          100 * (n : ℝ) ^ 2 / (M : ℝ) + 3 := hceil
    _ ≤ 5 * (n : ℝ) ^ 2 / (C : ℝ) +
        (175 / 3 : ℝ) * (n : ℝ) ^ 2 / (C : ℝ) + 3 := by gcongr
    _ < 5 * (n : ℝ) ^ 2 / (C : ℝ) +
        (175 / 3 : ℝ) * (n : ℝ) ^ 2 / (C : ℝ) +
        (20 / 3 : ℝ) * (n : ℝ) ^ 2 / (C : ℝ) := by gcongr
    _ = 70 * (n : ℝ) ^ 2 / (C : ℝ) := by ring

theorem raw_work_fits_window {n M C W : ℕ}
    (hn : 0 < n) (hmain : 12 * n ≤ 25 * M) (hclock : 25 * C ≤ 7 * n)
    (hwidth : 70 * n ^ 2 < C * W) :
    rawWork n M C < W := by
  have hC : 0 < C := by
    by_contra h
    have hzero : C = 0 := by omega
    simp [hzero] at hwidth
  have hCR : (0 : ℝ) < (C : ℝ) := by exact_mod_cast hC
  have hwidthR : 70 * (n : ℝ) ^ 2 < (C : ℝ) * (W : ℝ) := by
    exact_mod_cast hwidth
  have hwidth' : 70 * (n : ℝ) ^ 2 / (C : ℝ) < (W : ℝ) :=
    (div_lt_iff₀ hCR).2 (by nlinarith only [hwidthR])
  exact_mod_cast (raw_work_lt_density_bound hn hC hmain hclock).trans hwidth'

/-- On the exact reviewed clock-success history, all three raw work blocks fit
strictly before the end of each hour. This is a deterministic use of that
history, not conditioning the pair-log law on a future event. -/
theorem clockHistory_raw_work_fits {n : ℕ} {init : InputCfg n}
    {ω : InputLog n} {S T ρ : ℕ} {w : ClockTimes init}
    (H : ClockHistory init ω S T ρ w) (hn : 0 < n)
    (h : ℕ) (hh : h ≤ PhaseThreeModel.Numeric.hourIndex n) :
    w.start h +
      rawWork n (timeMainCount (trace init ω S)) (clockCount (trace init ω S)) <
        w.finish h := by
  have hcap : w.cap < ρ :=
    lt_of_le_of_lt (Nat.le_add_right w.cap (logWindow n 16)) H.protected_settling
  have hS : S < ρ :=
    lt_of_le_of_lt (H.entry.order.trans H.all_before_cap) hcap
  have hdensity := H.density S le_rfl hS
  have hfit := raw_work_fits_window hn hdensity.1 hdensity.2.2.2.1
    (H.raw_width h hh)
  omega

end Ripple.PopulationProtocol.ExactMajority.AveragingCancellationAlgebra

end
