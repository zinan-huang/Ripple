/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Phase3Productive
import Tri.Phase3Level
import Tri.PaperCorollary3

/-!
# Paper Corollary 2 — one phase-2 stage

The paper's stage definition (Natural Computing 19 (2020), p. 256; Springer
PDF p. 8, displayed statement of Corollary 2) is the unambiguous form and is
what is formalized here:

> A typical stage `s` in phase 2 starts with `y ≤ n/2^s` and continues while
> `n/2^(s−1) ≥ y > n/2^(s+1)`.  It completes properly if `y ≤ n/2^(s+1)`.

with the budget from Corollary 2: at most `3n/2^s` **productive** reaction
events.  Writing `P = n/2^s` and `B = n/2^(s+1)` (so `P = 2B`), the stage runs
from `y ≤ P`, escapes if `y > 2P`, and completes at `y ≤ B`, within `3P`
productive events.

**Erratum.**  The printed Corollary 2 says the stage "ends with
`y = min{n/2^(s+1), γ lg n}`".  That `min` is unattainable in either regime;
the project errata gives the exact published location and the corrected
reading.  The stage definition above is used instead.

Drift: on the whole of phase 2 the minority satisfies `y ≤ n/6`, which in
subtraction-free form is the guard `5 b ≤ a` (`5(y−1) ≤ x−1`), giving
`p_down ≥ 5/6` by `productive_down_mass_ge`.  Both scalar steps below are
TIGHT at `q = 5/6`.
-/

namespace Tri

open scoped ENNReal

/-! ### Paper Corollary 2 — stage parameters and the live band -/

/-- Stage completion: the minority is at most `B`.  Subtraction-free form of
`y ≤ B` under `x + y = n`. -/
def Corollary2Target (n B x : ℕ) : Prop := n ≤ x + B

/-- Stage escape: the minority has climbed above `2P` (the stage's upper band
edge `n/2^(s-1)`), or the state is non-physical. -/
def Corollary2Escape (n P x : ℕ) : Prop := x + 2 * P < n ∨ n < x

/-- Stopped for the stage: completed, escaped, or non-physical. -/
def Corollary2Stop (n B P x : ℕ) : Prop :=
  Corollary2Target n B x ∨ Corollary2Escape n P x

instance corollary2TargetDecidable (n B : ℕ) :
    DecidablePred (Corollary2Target n B) := by
  intro x; unfold Corollary2Target; infer_instance

instance corollary2StopDecidable (n B P : ℕ) :
    DecidablePred (Corollary2Stop n B P) := by
  intro x; unfold Corollary2Stop Corollary2Target Corollary2Escape
  infer_instance

/-- Every live stage-2 state is a genuine interior state satisfying the
phase-2 guard `5 b ≤ a`, i.e. `5(y−1) ≤ x−1`, which is what gives
`p_down ≥ 5/6`. -/
theorem corollary2_live_interior {n B P x : ℕ} (h3 : 3 ≤ n)
    (hband : 12 * P ≤ n) (hstop : ¬ Corollary2Stop n B P x) :
    ∃ a b : ℕ, x = a + 1 ∧ a + b + 2 = n ∧ 0 < a + b ∧ 5 * b ≤ a := by
  unfold Corollary2Stop Corollary2Target Corollary2Escape at hstop
  push Not at hstop
  obtain ⟨hdone, hesc, hphys⟩ := hstop
  refine ⟨x - 1, n - x - 1, ?_, ?_, ?_, ?_⟩ <;> omega

/-! ### The two scalar contraction steps -/

/-- Deadline branch: with `5/6 ≤ q`, the potential `(3/4)^x` contracts by
`61/72`.  After factoring `w^a` out of `q' w^a + q w^(a+2) ≤ φ w^(a+1)` with
`w = 3/4`, `φ = 61/72`, the obligation is exactly this.  Tight at `q = 5/6`. -/
theorem corollary2_scalar_step {q q' : ℝ≥0∞}
    (hsum : q + q' = 1) (hq : (5 : ℝ≥0∞) / 6 ≤ q) :
    q' + q * (9 / 16) ≤ 61 / 96 := by
  have hqt : q ≠ ⊤ := by intro h; rw [h] at hsum; simp at hsum
  have hq't : q' ≠ ⊤ := by intro h; rw [h] at hsum; simp at hsum
  have hsumR : q.toReal + q'.toReal = 1 := by
    rw [← ENNReal.toReal_add hqt hq't, hsum, ENNReal.toReal_one]
  have hqR : (5 : ℝ) / 6 ≤ q.toReal := by
    have := (ENNReal.toReal_le_toReal (by finiteness) hqt).mpr hq
    simpa using this
  have hq0 : 0 ≤ q'.toReal := ENNReal.toReal_nonneg
  have hlhs : (q' + q * (9 / 16)).toReal = q'.toReal + q.toReal * (9 / 16) := by
    rw [ENNReal.toReal_add hq't (by finiteness), ENNReal.toReal_mul]
    norm_num
  have hfin : q' + q * (9 / 16) ≠ ⊤ := by finiteness
  rw [← ENNReal.toReal_le_toReal hfin (by finiteness), hlhs]
  norm_num
  linarith

/-- Escape branch: with `5/6 ≤ q`, the ruin potential `(1/2)^x` is a
supermartingale — `q' + q (1/4) ≤ 1/2`. -/
theorem corollary2_feller_scalar_step {q q' : ℝ≥0∞}
    (hsum : q + q' = 1) (hq : (5 : ℝ≥0∞) / 6 ≤ q) :
    q' + q * (1 / 4) ≤ 1 / 2 := by
  have hqt : q ≠ ⊤ := by intro h; rw [h] at hsum; simp at hsum
  have hq't : q' ≠ ⊤ := by intro h; rw [h] at hsum; simp at hsum
  have hsumR : q.toReal + q'.toReal = 1 := by
    rw [← ENNReal.toReal_add hqt hq't, hsum, ENNReal.toReal_one]
  have hqR : (5 : ℝ) / 6 ≤ q.toReal := by
    have := (ENNReal.toReal_le_toReal (by finiteness) hqt).mpr hq
    simpa using this
  have hq0 : 0 ≤ q'.toReal := ENNReal.toReal_nonneg
  have hlhs : (q' + q * (1 / 4)).toReal = q'.toReal + q.toReal * (1 / 4) := by
    rw [ENNReal.toReal_add hq't (by finiteness), ENNReal.toReal_mul]
    norm_num
  have hfin : q' + q * (1 / 4) ≠ ⊤ := by finiteness
  rw [← ENNReal.toReal_le_toReal hfin (by finiteness), hlhs]
  norm_num
  linarith

/-- Band form of the live-interior extraction: only the stage band and
`x ≠ n` are needed, not the completion condition. -/
theorem corollary2_band_interior {n P x : ℕ} (h3 : 3 ≤ n)
    (hband : 12 * P ≤ n) (hin : n ≤ x + 2 * P) (hxn : x ≤ n) (hxne : x ≠ n) :
    ∃ a b : ℕ, x = a + 1 ∧ a + b + 2 = n ∧ 0 < a + b ∧ 5 * b ≤ a := by
  refine ⟨x - 1, n - x - 1, ?_, ?_, ?_, ?_⟩ <;> omega

/-- **The stage deadline potential contraction.**  On the chain frozen at
`Corollary2Stop`, the killed potential `(3/4)^x` contracts by `61/72`. -/
theorem corollary2_stopped_potential_step
    (n B P : ℕ) (h3 : 3 ≤ n) (hband : 12 * P ≤ n) (x : ℕ) :
    expect (freeze (Corollary2Stop n B P) (productiveTriChain n) x)
        (fun z => if Corollary2Stop n B P z then 0 else ((3 : ℝ≥0∞) / 4) ^ z)
      ≤ ((61 : ℝ≥0∞) / 72) *
          (if Corollary2Stop n B P x then 0 else ((3 : ℝ≥0∞) / 4) ^ x) := by
  classical
  by_cases hstop : Corollary2Stop n B P x
  · simp [freeze, hstop]
  · obtain ⟨a, b, hx, hpop, hprod, hguard⟩ :=
      corollary2_live_interior h3 hband hstop
    subst hx
    rw [show freeze (Corollary2Stop n B P) (productiveTriChain n) (a + 1)
          = productiveTriChain n (a + 1) by simp [freeze, hstop],
      productiveTriChain_apply hpop hprod]
    have hdrop : ∀ z : ℕ,
        (if Corollary2Stop n B P z then 0 else ((3 : ℝ≥0∞) / 4) ^ z)
          ≤ ((3 : ℝ≥0∞) / 4) ^ z := by
      intro z; split <;> simp
    refine le_trans
      (expect_mono (productiveTriInterior a b hprod) hdrop) ?_
    rw [expect_productiveTriInterior]
    have hq : (5 : ℝ≥0∞) / 6 ≤ (a : ℝ≥0∞) / ((a : ℝ≥0∞) + (b : ℝ≥0∞)) := by
      have := productive_down_mass_ge (k := 5) hprod hguard
      norm_num at this
      exact this
    have hsum : (a : ℝ≥0∞) / ((a : ℝ≥0∞) + (b : ℝ≥0∞))
        + (b : ℝ≥0∞) / ((a : ℝ≥0∞) + (b : ℝ≥0∞)) = 1 := by
      have := productiveTriInterior_masses a b hprod
      rw [add_comm] at this
      simpa using this
    have hscalar := corollary2_scalar_step hsum hq
    have hsq : ((3 : ℝ≥0∞) / 4) ^ 2 = 9 / 16 := by
      rw [← ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness),
        ENNReal.toReal_pow, ENNReal.toReal_div, ENNReal.toReal_div]
      norm_num
    have hphiw : (61 : ℝ≥0∞) / 72 * (3 / 4) = 61 / 96 := by
      rw [← ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness),
        ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_div,
        ENNReal.toReal_div]
      norm_num
    rw [show ((3 : ℝ≥0∞) / 4) ^ (a + 2) = ((3 : ℝ≥0∞) / 4) ^ a * (9 / 16) by
        rw [pow_add, hsq],
      show ((3 : ℝ≥0∞) / 4) ^ (a + 1) = ((3 : ℝ≥0∞) / 4) ^ a * (3 / 4) by
        rw [pow_succ],
      if_neg hstop]
    calc
      (b : ℝ≥0∞) / ((a : ℝ≥0∞) + (b : ℝ≥0∞)) * ((3 : ℝ≥0∞) / 4) ^ a
          + (a : ℝ≥0∞) / ((a : ℝ≥0∞) + (b : ℝ≥0∞))
              * (((3 : ℝ≥0∞) / 4) ^ a * (9 / 16))
          = ((b : ℝ≥0∞) / ((a : ℝ≥0∞) + (b : ℝ≥0∞))
              + (a : ℝ≥0∞) / ((a : ℝ≥0∞) + (b : ℝ≥0∞)) * (9 / 16))
            * ((3 : ℝ≥0∞) / 4) ^ a := by ring
      _ ≤ (61 / 96) * ((3 : ℝ≥0∞) / 4) ^ a := mul_le_mul_left hscalar _
      _ = (61 : ℝ≥0∞) / 72 * (((3 : ℝ≥0∞) / 4) ^ a * (3 / 4)) := by
          rw [show (61 : ℝ≥0∞) / 72 * (((3 : ℝ≥0∞) / 4) ^ a * (3 / 4))
              = ((61 : ℝ≥0∞) / 72 * (3 / 4)) * ((3 : ℝ≥0∞) / 4) ^ a by ring,
            hphiw]

/-- Largest `X`-count that counts as a stage escape (minority above `2P`). -/
def corollary2EscapeBound (n P : ℕ) : ℕ := n - 2 * P - 1

/-- The stage escape event has the `level ≤ m` shape `feller_ruin_u` consumes.
The level is `phase3Level`, which pushes the non-physical states to the bottom
of the band — the same device as in Corollary 3. -/
theorem corollary2Level_le_iff (n P z : ℕ) (h3 : 3 ≤ n) (hband : 12 * P ≤ n) :
    phase3Level n z ≤ corollary2EscapeBound n P ↔ Corollary2Escape n P z := by
  unfold phase3Level corollary2EscapeBound Corollary2Escape
  by_cases hz : n < z
  · simp only [if_pos hz]
    exact ⟨fun _ => Or.inr hz, fun _ => Nat.zero_le _⟩
  · simp only [if_neg hz]
    constructor
    · intro h; exact Or.inl (by omega)
    · rintro (h | h) <;> omega

/-- **The stage Feller supermartingale.**  On the chain frozen at
`Corollary2Stop`, the ruin potential `(1/2)^x` never increases in expectation.
The stopped set is the full `Stop` (completion included) because
`freeze Escape (freeze Target K) = freeze Stop K`, which is the form
`feller_ruin_u` will be applied through. -/
theorem corollary2_feller_hfroz_stop
    (n B P : ℕ) (h3 : 3 ≤ n) (hband : 12 * P ≤ n) (x : ℕ) :
    expect
        (freeze (Corollary2Stop n B P) (productiveTriChain n) x)
        (fun z => ((1 : ℝ≥0∞) / 2) ^ phase3Level n z)
      ≤ ((1 : ℝ≥0∞) / 2) ^ phase3Level n x := by
  classical
  by_cases hstop : Corollary2Stop n B P x
  · simp [freeze, hstop]
  · obtain ⟨a, b, hx, hpop, hprod, hguard⟩ :=
      corollary2_live_interior h3 hband hstop
    subst hx
    rw [show freeze (Corollary2Stop n B P) (productiveTriChain n) (a + 1)
          = productiveTriChain n (a + 1) by simp [freeze, hstop],
      productiveTriChain_apply hpop hprod, expect_productiveTriInterior]
    have hla : phase3Level n a = a := by
      simp [phase3Level, show ¬ n < a by omega]
    have hla2 : phase3Level n (a + 2) = a + 2 := by
      simp [phase3Level, show ¬ n < a + 2 by omega]
    have hla1 : phase3Level n (a + 1) = a + 1 := by
      simp [phase3Level, show ¬ n < a + 1 by omega]
    rw [hla, hla2, hla1]
    have hq : (5 : ℝ≥0∞) / 6 ≤ (a : ℝ≥0∞) / ((a : ℝ≥0∞) + (b : ℝ≥0∞)) := by
      have := productive_down_mass_ge (k := 5) hprod hguard
      norm_num at this
      exact this
    have hsum : (a : ℝ≥0∞) / ((a : ℝ≥0∞) + (b : ℝ≥0∞))
        + (b : ℝ≥0∞) / ((a : ℝ≥0∞) + (b : ℝ≥0∞)) = 1 := by
      have := productiveTriInterior_masses a b hprod
      rw [add_comm] at this
      simpa using this
    have hscalar := corollary2_feller_scalar_step hsum hq
    have hsq : ((1 : ℝ≥0∞) / 2) ^ 2 = 1 / 4 := by
      rw [← ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness),
        ENNReal.toReal_pow, ENNReal.toReal_div, ENNReal.toReal_div]
      norm_num
    rw [show ((1 : ℝ≥0∞) / 2) ^ (a + 2) = ((1 : ℝ≥0∞) / 2) ^ a * (1 / 4) by
        rw [pow_add, hsq],
      show ((1 : ℝ≥0∞) / 2) ^ (a + 1) = ((1 : ℝ≥0∞) / 2) ^ a * (1 / 2) by
        rw [pow_succ]]
    calc
      (b : ℝ≥0∞) / ((a : ℝ≥0∞) + (b : ℝ≥0∞)) * ((1 : ℝ≥0∞) / 2) ^ a
          + (a : ℝ≥0∞) / ((a : ℝ≥0∞) + (b : ℝ≥0∞))
              * (((1 : ℝ≥0∞) / 2) ^ a * (1 / 4))
          = ((b : ℝ≥0∞) / ((a : ℝ≥0∞) + (b : ℝ≥0∞))
              + (a : ℝ≥0∞) / ((a : ℝ≥0∞) + (b : ℝ≥0∞)) * (1 / 4))
            * ((1 : ℝ≥0∞) / 2) ^ a := by ring
      _ ≤ (1 / 2) * ((1 : ℝ≥0∞) / 2) ^ a := mul_le_mul_left hscalar _
      _ = ((1 : ℝ≥0∞) / 2) ^ a * (1 / 2) := by ring

/-! ### Numeric endgame for the stage -/

/-- The instantiated stage count-tail expression is one rational base to the
`P`-th power:  `(61/72)³ / (3/4) = 226981/279936 ≈ 0.81083`. -/
theorem corollary2_count_tail_base_collapse (P x₀ : ℕ) :
    (61 / 72 : ℝ≥0∞) ^ (3 * P) * (3 / 4 : ℝ≥0∞) ^ x₀
        / (3 / 4 : ℝ≥0∞) ^ (x₀ + P)
      = (226981 / 279936 : ℝ≥0∞) ^ P := by
  have h34ne : (3 / 4 : ℝ≥0∞) ≠ 0 := by simp [ENNReal.div_eq_zero_iff]
  have hden : (3 / 4 : ℝ≥0∞) ^ (x₀ + P) ≠ 0 := pow_ne_zero _ h34ne
  have hnum : (61 / 72 : ℝ≥0∞) ^ (3 * P) * (3 / 4 : ℝ≥0∞) ^ x₀ ≠ ⊤ := by
    finiteness
  have hlhs : (61 / 72 : ℝ≥0∞) ^ (3 * P) * (3 / 4 : ℝ≥0∞) ^ x₀
      / (3 / 4 : ℝ≥0∞) ^ (x₀ + P) ≠ ⊤ :=
    ENNReal.div_ne_top hnum hden
  rw [← ENNReal.toReal_eq_toReal_iff' hlhs (by finiteness)]
  simp only [ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofNat]
  rw [pow_add, pow_mul]
  field_simp
  rw [← mul_pow]
  norm_num

/-- Numeric endgame for the stage count tail. -/
theorem corollary2_count_tail_le_exp (P x₀ : ℕ) :
    (61 / 72 : ℝ≥0∞) ^ (3 * P) * (3 / 4 : ℝ≥0∞) ^ x₀
        / (3 / 4 : ℝ≥0∞) ^ (x₀ + P)
      ≤ ENNReal.ofReal (Real.exp (-((P : ℝ) / 8))) := by
  rw [corollary2_count_tail_base_collapse P x₀]
  have hbase :
      (226981 / 279936 : ℝ≥0∞) ≤ ENNReal.ofReal (1 - (1 / 8 : ℝ)) := by
    rw [show (1 : ℝ) - 1 / 8 = 7 / 8 by norm_num,
      show (226981 / 279936 : ℝ≥0∞)
          = ENNReal.ofReal (226981 / 279936 : ℝ) by
        rw [ENNReal.ofReal_div_of_pos (by norm_num)]
        norm_num]
    exact ENNReal.ofReal_le_ofReal (by norm_num)
  refine le_trans
    (enn_pow_le_ofReal_exp (226981 / 279936 : ℝ≥0∞) (1 / 8 : ℝ) P
      (by norm_num) (by norm_num) hbase) ?_
  apply le_of_eq
  apply congrArg ENNReal.ofReal
  apply congrArg Real.exp
  ring

/-- The stage ruin term is bounded by the same stage exponential error. -/
theorem corollary2_feller_ruin_le_exp (P b : ℕ) (hPb : P ≤ 4 * b) :
    (1 / 2 : ℝ≥0∞) ^ b ≤ ENNReal.ofReal (Real.exp (-((P : ℝ) / 8))) := by
  have hbase : (1 / 2 : ℝ≥0∞) ≤ ENNReal.ofReal (1 - (1 / 2 : ℝ)) := by
    rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num,
      show (1 / 2 : ℝ≥0∞) = ENNReal.ofReal (1 / 2 : ℝ) by
        rw [ENNReal.ofReal_div_of_pos (by norm_num)]
        norm_num]
  refine le_trans
    (enn_pow_le_ofReal_exp (1 / 2 : ℝ≥0∞) (1 / 2 : ℝ) b
      (by norm_num) (by norm_num) hbase) ?_
  refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
  have hPbR : (P : ℝ) ≤ 4 * (b : ℝ) := by exact_mod_cast hPb
  have : (P : ℝ) / 8 ≤ 1 / 2 * (b : ℝ) := by linarith
  linarith


variable {α : Type*}

/-- `hitProb` only depends on the hit set up to pointwise equivalence. -/
theorem hitProb_congr (K : α → PMF α) (P Q : α → Prop)
    [DecidablePred P] [DecidablePred Q] (h : ∀ s, P s ↔ Q s) (T : ℕ) (s₀ : α) :
    hitProb P K T s₀ = hitProb Q K T s₀ := by
  unfold hitProb
  rw [freeze_congr K P Q h]
  congr 1
  funext z
  unfold ind
  by_cases hz : P z
  · rw [if_pos hz, if_pos ((h z).1 hz)]
  · rw [if_neg hz, if_neg (fun hq => hz ((h z).2 hq))]

/-- **Paper Corollary 2** (stage form).  From a phase-2 stage start `y ≤ P`,
`3P` productive reaction events reach the stage target `y ≤ B` (where
`P = 2B`) except with mass `2 exp (-P/8)`. -/
theorem corollary2 (n B P x₀ : ℕ) (h3 : 3 ≤ n) (hPB : P = 2 * B)
    (hband : 12 * P ≤ n) (hx₀n : x₀ ≤ n) (hentry : n ≤ x₀ + P) :
    terminalFailureMass
        (iter (freeze (Corollary2Target n B) (productiveTriChain n)) (3 * P) x₀)
        (Corollary2Target n B)
      ≤ 2 * ENNReal.ofReal (Real.exp (-((P : ℝ) / 8))) := by
  classical
  set K := productiveTriChain n with hK
  set m := corollary2EscapeBound n P with hm
  have hmx : m ≤ x₀ := by
    unfold corollary2EscapeBound at hm; omega
  set b := x₀ - m with hb
  have hs₀ : phase3Level n x₀ = m + b := by
    have : phase3Level n x₀ = x₀ := by
      simp [phase3Level, show ¬ n < x₀ by omega]
    omega
  have hPb : P ≤ 4 * b := by
    unfold corollary2EscapeBound at hm; omega
  -- the stop set is definitionally target-or-escape
  have hstopeq : ∀ s, (Corollary2Target n B s ∨ Corollary2Escape n P s)
      ↔ Corollary2Stop n B P s := fun s => Iff.rfl
  -- ESCAPE BRANCH
  have hescIff : ∀ s, (phase3Level n s ≤ m) ↔ Corollary2Escape n P s :=
    fun s => corollary2Level_le_iff n P s h3 hband
  have hfroz : ∀ s,
      expect (freeze (fun z => phase3Level n z ≤ m)
          (freeze (Corollary2Target n B) K) s)
        (fun z => ((1 : ℝ≥0∞) / 2) ^ phase3Level n z)
        ≤ ((1 : ℝ≥0∞) / 2) ^ phase3Level n s := by
    intro s
    rw [freeze_congr (freeze (Corollary2Target n B) K)
        (fun z => phase3Level n z ≤ m) (Corollary2Escape n P) hescIff,
      show freeze (Corollary2Escape n P) (freeze (Corollary2Target n B) K)
          = freeze (fun z => Corollary2Target n B z ∨ Corollary2Escape n P z) K from
        freeze_escape_freeze_done K (Corollary2Target n B) (Corollary2Escape n P),
      freeze_congr K (fun z => Corollary2Target n B z ∨ Corollary2Escape n P z)
        (Corollary2Stop n B P) hstopeq]
    exact corollary2_feller_hfroz_stop n B P h3 hband s
  have hfeller :
      hitProb (Corollary2Escape n P) (freeze (Corollary2Target n B) K) (3 * P) x₀
        ≤ ENNReal.ofReal (Real.exp (-((P : ℝ) / 8))) := by
    rw [← hitProb_congr (freeze (Corollary2Target n B) K)
      (fun z => phase3Level n z ≤ m) (Corollary2Escape n P) hescIff (3 * P) x₀]
    refine le_trans (le_iSup
      (fun T => hitProb (fun z => phase3Level n z ≤ m)
        (freeze (Corollary2Target n B) K) T x₀) (3 * P)) ?_
    refine le_trans ?_ (corollary2_feller_ruin_le_exp P b hPb)
    exact feller_ruin_u (K := freeze (Corollary2Target n B) K) (phase3Level n)
      m b (1 / 2) (by norm_num) (by simp)
      (fun z => ((1 : ℝ≥0∞) / 2) ^ phase3Level n z) (fun _ => rfl) hfroz x₀ hs₀
  -- DEADLINE BRANCH
  have hsupp : ∀ z, iter (freeze (Corollary2Stop n B P) K) (3 * P) x₀ z ≠ 0 → z ≤ n := by
    intro z hz
    exact iter_support_closed _ (fun s => s ≤ n)
      (freeze_support_closed K (Corollary2Stop n B P) (fun s => s ≤ n)
        (productiveTriChain_support_le n))
      (3 * P) x₀ z hx₀n hz
  have hcount := count_tail_frozen K (Corollary2Stop n B P)
    id ((3 : ℝ≥0∞) / 4) ((61 : ℝ≥0∞) / 72)
    (by rw [ENNReal.div_le_iff_le_mul (Or.inl (by norm_num))
        (Or.inl (by norm_num))]; norm_num) (by simp)
    (corollary2_stopped_potential_step n B P h3 hband)
    (3 * P) (x₀ + P) x₀
  have hlive :
      terminalFailureMass (iter (freeze (Corollary2Stop n B P) K) (3 * P) x₀)
          (Corollary2Stop n B P)
        ≤ ENNReal.ofReal (Real.exp (-((P : ℝ) / 8))) := by
    refine le_trans ?_ (le_trans hcount ?_)
    · unfold terminalFailureMass
      refine ENNReal.tsum_le_tsum fun z => ?_
      by_cases hz : Corollary2Stop n B P z
      · simp [hz]
      · by_cases hzero : iter (freeze (Corollary2Stop n B P) K) (3 * P) x₀ z = 0
        · simp [hz, hzero]
        · have := hsupp z hzero
          simp only [hz, if_false, id, not_false_eq_true, and_true]
          rw [if_pos (show z ≤ x₀ + P by omega)]
    · refine le_trans ?_ (corollary2_count_tail_le_exp P x₀)
      refine ENNReal.div_le_div_right ?_ _
      refine mul_le_mul_right ?_ _
      split <;> simp
  -- ASSEMBLY
  have hsplit := terminalFailureMass_le_escape_add_live K
    (Corollary2Target n B) (Corollary2Escape n P) (3 * P) x₀
  rw [freeze_congr K (fun s => Corollary2Target n B s ∨ Corollary2Escape n P s)
      (Corollary2Stop n B P) hstopeq,
    terminalFailureMass_congr _
      (fun s => Corollary2Target n B s ∨ Corollary2Escape n P s)
      (Corollary2Stop n B P) hstopeq] at hsplit
  refine le_trans hsplit ?_
  rw [two_mul]
  exact add_le_add hfeller hlive

end Tri

#print axioms Tri.corollary2_band_interior
#print axioms Tri.corollary2_stopped_potential_step
#print axioms Tri.corollary2Level_le_iff
#print axioms Tri.corollary2_feller_hfroz_stop
#print axioms Tri.corollary2_count_tail_base_collapse
#print axioms Tri.corollary2_count_tail_le_exp
#print axioms Tri.corollary2_feller_ruin_le_exp
#print axioms Tri.hitProb_congr
#print axioms Tri.corollary2
