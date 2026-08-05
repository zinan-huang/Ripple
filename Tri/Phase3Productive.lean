/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.PaperLemma3
import Tri.RatioExp
import Tri.Freeze

/-!
# Phase-3 productive-clock leaves (towards paper Corollary 3)

Paper Corollary 3 states that phase 3, entered at minority `y ≤ γ lg n`,
completes within `3 γ lg n` **productive** reaction events with failure
`exp(-Θ(γ lg n))`.

The exact conditional law of one productive event, on the `X`-count, is
`productiveTriChain n (a+1) = productiveTriInterior a b` whenever
`a + b + 2 = n`, and it moves to `a + 2` (minority down) with mass
`a / (a+b)` and to `a` (minority up) with mass `b / (a+b)`.  Writing
`x = a+1`, `y = b+1` these are `(x-1)/(n-2)` and `(y-1)/(n-2)`.

The crude band bound `p_down ≥ 2/3`, valid on the whole paper band
`y ≤ 2 γ lg n` under `6 γ lg n ≤ n`, is *not* enough for the `3 γ lg n`
deadline: at `p_down = 2/3` the mean number of down-moves in `3d` steps is
exactly `2d`, leaving no Chernoff slack.  The deadline needs the tighter
guard `2 y ≤ 3 γ lg n`, on which `p_down ≥ 3/4`; that is this file's content
in its subtraction-free form `3 b ≤ a`.
-/


namespace Tri

open scoped ENNReal

/-- On the tight phase-3 guard `3 b ≤ a` (i.e. `3(y-1) ≤ x-1`), a productive
event decreases the minority with conditional probability at least `3/4`. -/
theorem productive_down_mass_ge_three_quarters
    {a b : ℕ} (hprod : 0 < a + b) (hguard : 3 * b ≤ a) :
    (3 : ℝ≥0∞) / 4 ≤ (a : ℝ≥0∞) / ((a : ℝ≥0∞) + (b : ℝ≥0∞)) := by
  have hab : ((a : ℝ≥0∞) + (b : ℝ≥0∞)) = ((a + b : ℕ) : ℝ≥0∞) := by
    push_cast; ring
  rw [hab]
  have hne0 : ((a + b : ℕ) : ℝ≥0∞) ≠ 0 := by exact_mod_cast hprod.ne'
  have hnet : ((a + b : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  rw [ENNReal.le_div_iff_mul_le (Or.inl hne0) (Or.inl hnet)]
  have hnum : (3 : ℝ≥0∞) / 4 * ((a + b : ℕ) : ℝ≥0∞)
      = (3 * ((a + b : ℕ) : ℝ≥0∞)) / 4 := by
    simp [ENNReal.div_eq_inv_mul, mul_comm, mul_assoc]
  rw [hnum, ENNReal.div_le_iff_le_mul (Or.inl (by norm_num)) (Or.inl (by norm_num))]
  have hnat : (3 : ℕ) * (a + b) ≤ a * 4 := by omega
  calc (3 : ℝ≥0∞) * ((a + b : ℕ) : ℝ≥0∞)
      = ((3 * (a + b) : ℕ) : ℝ≥0∞) := by push_cast; ring
    _ ≤ ((a * 4 : ℕ) : ℝ≥0∞) := by exact_mod_cast hnat
    _ = (a : ℝ≥0∞) * 4 := by push_cast; ring

/-- `d = γ lg n`, the phase-3 scale. -/
abbrev phase3Scale (n γ : ℕ) : ℕ := γ * Nat.log 2 n

/-- Paper phase-3 entry: the minority `y` is at most `d = γ lg n`. -/
def Phase3EntryProductive (n γ x : ℕ) : Prop :=
  x ≤ n ∧ n ≤ x + phase3Scale n γ

/-- Proper completion of phase 3. -/
def Phase3Done (n x : ℕ) : Prop := x = n

/-- Stopped states: all-`X` consensus, escape above the tight internal band
`2 y ≤ 3 d`, or a non-physical count.  The third disjunct matters: the
productive chain self-loops off the physical range, so a potential can never
contract there and such states must be frozen. -/
def Phase3Stop (n γ x : ℕ) : Prop :=
  x = n ∨ 2 * x + 3 * phase3Scale n γ < 2 * n ∨ n < x

instance phase3DoneDecidable (n : ℕ) : DecidablePred (Phase3Done n) := by
  intro x; unfold Phase3Done; infer_instance

instance phase3StopDecidable (n γ : ℕ) : DecidablePred (Phase3Stop n γ) := by
  intro x; unfold Phase3Stop; infer_instance

/-- Every live (non-stopped) phase-3 state is a genuine interior state, and it
satisfies the subtraction-free tight-guard inequality `3 b ≤ a`. -/
theorem phase3_live_interior {n γ x : ℕ} (h3 : 3 ≤ n)
    (hsize : 6 * phase3Scale n γ ≤ n) (hstop : ¬ Phase3Stop n γ x) :
    ∃ a b : ℕ, x = a + 1 ∧ a + b + 2 = n ∧ 0 < a + b ∧ 3 * b ≤ a := by
  unfold Phase3Stop at hstop
  push Not at hstop
  obtain ⟨hne, hguard, hxn⟩ := hstop
  refine ⟨x - 1, n - x - 1, ?_, ?_, ?_, ?_⟩ <;> omega

/-- The phase-3 scalar contraction.  With the tight-guard down-mass bound
`3/4 ≤ q`, the two-atom step of the potential `(3/4)^x` contracts by
`43/48`: after factoring `w^a` out of `q' * w^a + q * w^(a+2) ≤ φ * w^(a+1)`
with `w = 3/4` and `φ = 43/48`, the obligation is exactly this. -/
theorem phase3_scalar_step {q q' : ℝ≥0∞}
    (hsum : q + q' = 1) (hq : (3 : ℝ≥0∞) / 4 ≤ q) :
    q' + q * (9 / 16) ≤ 43 / 64 := by
  have hqt : q ≠ ⊤ := by
    intro h
    rw [h] at hsum
    simp at hsum
  have hq't : q' ≠ ⊤ := by
    intro h
    rw [h] at hsum
    simp at hsum
  -- transfer to the reals
  have hsumR : q.toReal + q'.toReal = 1 := by
    rw [← ENNReal.toReal_add hqt hq't, hsum, ENNReal.toReal_one]
  have hqR : (3 : ℝ) / 4 ≤ q.toReal := by
    have := (ENNReal.toReal_le_toReal (by finiteness) hqt).mpr hq
    simpa using this
  have hq0 : 0 ≤ q'.toReal := ENNReal.toReal_nonneg
  have hgoalR : q'.toReal + q.toReal * (9 / 16) ≤ 43 / 64 := by linarith
  have hlhs : (q' + q * (9 / 16)).toReal = q'.toReal + q.toReal * (9 / 16) := by
    rw [ENNReal.toReal_add hq't (by finiteness), ENNReal.toReal_mul]
    norm_num
  have hfin : q' + q * (9 / 16) ≠ ⊤ := by finiteness
  rw [← ENNReal.toReal_le_toReal hfin (by finiteness), hlhs]
  norm_num
  linarith

section

variable {α : Type*}

/-- `expect` is monotone in the integrand. -/
theorem expect_mono (p : PMF α) {V W : α → ℝ≥0∞} (h : ∀ z, V z ≤ W z) :
    expect p V ≤ expect p W := by
  unfold expect
  exact ENNReal.tsum_le_tsum fun z => mul_le_mul_right (h z) (p z)

end

/-- **The phase-3 one-step potential contraction.**  On the chain frozen at
`Phase3Stop`, the killed potential `(3/4)^x` contracts by `43/48` at every
state. -/
theorem phase3_stopped_potential_step
    (n γ : ℕ) (h3 : 3 ≤ n) (hsize : 6 * phase3Scale n γ ≤ n) (x : ℕ) :
    expect (freeze (Phase3Stop n γ) (productiveTriChain n) x)
        (fun z => if Phase3Stop n γ z then 0 else ((3 : ℝ≥0∞) / 4) ^ z)
      ≤ ((43 : ℝ≥0∞) / 48) *
          (if Phase3Stop n γ x then 0 else ((3 : ℝ≥0∞) / 4) ^ x) := by
  classical
  by_cases hstop : Phase3Stop n γ x
  · simp [freeze, hstop]
  · obtain ⟨a, b, hx, hpop, hprod, hguard⟩ :=
      phase3_live_interior h3 hsize hstop
    subst hx
    rw [show freeze (Phase3Stop n γ) (productiveTriChain n) (a + 1)
          = productiveTriChain n (a + 1) by simp [freeze, hstop],
      productiveTriChain_apply hpop hprod]
    have hdrop : ∀ z : ℕ,
        (if Phase3Stop n γ z then 0 else ((3 : ℝ≥0∞) / 4) ^ z)
          ≤ ((3 : ℝ≥0∞) / 4) ^ z := by
      intro z; split <;> simp
    refine le_trans
      (expect_mono (productiveTriInterior a b hprod) hdrop) ?_
    rw [expect_productiveTriInterior]
    have hq : (3 : ℝ≥0∞) / 4 ≤ (a : ℝ≥0∞) / ((a : ℝ≥0∞) + (b : ℝ≥0∞)) :=
      productive_down_mass_ge_three_quarters hprod hguard
    have hsum : (a : ℝ≥0∞) / ((a : ℝ≥0∞) + (b : ℝ≥0∞))
        + (b : ℝ≥0∞) / ((a : ℝ≥0∞) + (b : ℝ≥0∞)) = 1 := by
      have := productiveTriInterior_masses a b hprod
      rw [add_comm] at this
      simpa using this
    have hscalar := phase3_scalar_step hsum hq
    have hsq : ((3 : ℝ≥0∞) / 4) ^ 2 = 9 / 16 := by
      rw [← ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness),
        ENNReal.toReal_pow, ENNReal.toReal_div, ENNReal.toReal_div]
      norm_num
    have hphiw : (43 : ℝ≥0∞) / 48 * (3 / 4) = 43 / 64 := by
      rw [← ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness),
        ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_div,
        ENNReal.toReal_div]
      norm_num
    have hpow2 : ((3 : ℝ≥0∞) / 4) ^ (a + 2)
        = ((3 : ℝ≥0∞) / 4) ^ a * (9 / 16) := by
      rw [pow_add, hsq]
    have hpow1 : ((3 : ℝ≥0∞) / 4) ^ (a + 1)
        = ((3 : ℝ≥0∞) / 4) ^ a * (3 / 4) := by
      rw [pow_succ]
    rw [hpow2, hpow1, if_neg hstop]
    calc
      (b : ℝ≥0∞) / ((a : ℝ≥0∞) + (b : ℝ≥0∞)) * ((3 : ℝ≥0∞) / 4) ^ a
          + (a : ℝ≥0∞) / ((a : ℝ≥0∞) + (b : ℝ≥0∞))
              * (((3 : ℝ≥0∞) / 4) ^ a * (9 / 16))
          = ((b : ℝ≥0∞) / ((a : ℝ≥0∞) + (b : ℝ≥0∞))
              + (a : ℝ≥0∞) / ((a : ℝ≥0∞) + (b : ℝ≥0∞)) * (9 / 16))
            * ((3 : ℝ≥0∞) / 4) ^ a := by ring
      _ ≤ (43 / 64) * ((3 : ℝ≥0∞) / 4) ^ a :=
          mul_le_mul_left hscalar _
      _ = (43 : ℝ≥0∞) / 48 * (((3 : ℝ≥0∞) / 4) ^ a * (3 / 4)) := by
          rw [show (43 : ℝ≥0∞) / 48 * (((3 : ℝ≥0∞) / 4) ^ a * (3 / 4))
              = ((43 : ℝ≥0∞) / 48 * (3 / 4)) * ((3 : ℝ≥0∞) / 4) ^ a by ring,
            hphiw]

/-- The instantiated `count_tail_frozen` expression is one fixed rational base
raised to the `d`-th power. -/
theorem phase3_count_tail_base_collapse (d x₀ : ℕ) :
    (43 / 48 : ℝ≥0∞) ^ (3 * d) * (3 / 4 : ℝ≥0∞) ^ x₀
        / (3 / 4 : ℝ≥0∞) ^ (x₀ + d)
      = (79507 / 82944 : ℝ≥0∞) ^ d := by
  have h34ne : (3 / 4 : ℝ≥0∞) ≠ 0 := by
    simp [ENNReal.div_eq_zero_iff]
  have hden : (3 / 4 : ℝ≥0∞) ^ (x₀ + d) ≠ 0 := pow_ne_zero _ h34ne
  have hnum : (43 / 48 : ℝ≥0∞) ^ (3 * d) * (3 / 4 : ℝ≥0∞) ^ x₀ ≠ ⊤ := by
    finiteness
  have hlhs : (43 / 48 : ℝ≥0∞) ^ (3 * d) * (3 / 4 : ℝ≥0∞) ^ x₀
      / (3 / 4 : ℝ≥0∞) ^ (x₀ + d) ≠ ⊤ :=
    ENNReal.div_ne_top hnum hden
  rw [← ENNReal.toReal_eq_toReal_iff' hlhs (by finiteness)]
  simp only [ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofNat]
  rw [pow_add, pow_mul]
  field_simp
  rw [← mul_pow]
  norm_num

/-- Numeric endgame for the phase-3 productive-count tail. -/
theorem phase3_count_tail_le_exp (d x₀ : ℕ) :
    (43 / 48 : ℝ≥0∞) ^ (3 * d) * (3 / 4 : ℝ≥0∞) ^ x₀
        / (3 / 4 : ℝ≥0∞) ^ (x₀ + d)
      ≤ ENNReal.ofReal (Real.exp (-((d : ℝ) / 72))) := by
  rw [phase3_count_tail_base_collapse d x₀]
  have hbase : (79507 / 82944 : ℝ≥0∞) ≤ ENNReal.ofReal (1 - (1 / 72 : ℝ)) := by
    rw [show (1 : ℝ) - 1 / 72 = 71 / 72 by norm_num,
      show (79507 / 82944 : ℝ≥0∞) = ENNReal.ofReal (79507 / 82944 : ℝ) by
        rw [ENNReal.ofReal_div_of_pos (by norm_num)]
        norm_num]
    exact ENNReal.ofReal_le_ofReal (by norm_num)
  refine le_trans
    (enn_pow_le_ofReal_exp (79507 / 82944 : ℝ≥0∞) (1 / 72 : ℝ) d
      (by norm_num) (by norm_num) hbase) ?_
  apply le_of_eq
  apply congrArg ENNReal.ofReal
  apply congrArg Real.exp
  ring

/-- The Feller ruin term is bounded by the same phase-3 exponential error. -/
theorem phase3_feller_ruin_le_exp (d b : ℕ) (hdb : d ≤ 2 * b) :
    (1 / 3 : ℝ≥0∞) ^ b ≤ ENNReal.ofReal (Real.exp (-((d : ℝ) / 72))) := by
  have hbase : (1 / 3 : ℝ≥0∞) ≤ ENNReal.ofReal (1 - (1 / 36 : ℝ)) := by
    rw [show (1 : ℝ) - 1 / 36 = 35 / 36 by norm_num,
      show (1 / 3 : ℝ≥0∞) = ENNReal.ofReal (1 / 3 : ℝ) by
        rw [ENNReal.ofReal_div_of_pos (by norm_num)]
        norm_num]
    exact ENNReal.ofReal_le_ofReal (by norm_num)
  refine le_trans
    (enn_pow_le_ofReal_exp (1 / 3 : ℝ≥0∞) (1 / 36 : ℝ) b
      (by norm_num) (by norm_num) hbase) ?_
  refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
  have hdbR : (d : ℝ) ≤ 2 * (b : ℝ) := by exact_mod_cast hdb
  have : (d : ℝ) / 72 ≤ 1 / 36 * (b : ℝ) := by linarith
  linarith

/-- The phase-3 Feller scalar step.  With the tight-guard down-mass bound
`3/4 ≤ q`, the ruin potential `(1/3)^x` is a supermartingale: after factoring
`u^a` out of `q' * u^a + q * u^(a+2) ≤ u^(a+1)` with `u = 1/3`, the obligation
is exactly this.  It is tight at `q = 3/4`. -/
theorem phase3_feller_scalar_step {q q' : ℝ≥0∞}
    (hsum : q + q' = 1) (hq : (3 : ℝ≥0∞) / 4 ≤ q) :
    q' + q * (1 / 9) ≤ 1 / 3 := by
  have hqt : q ≠ ⊤ := by
    intro h
    rw [h] at hsum
    simp at hsum
  have hq't : q' ≠ ⊤ := by
    intro h
    rw [h] at hsum
    simp at hsum
  have hsumR : q.toReal + q'.toReal = 1 := by
    rw [← ENNReal.toReal_add hqt hq't, hsum, ENNReal.toReal_one]
  have hqR : (3 : ℝ) / 4 ≤ q.toReal := by
    have := (ENNReal.toReal_le_toReal (by finiteness) hqt).mpr hq
    simpa using this
  have hq0 : 0 ≤ q'.toReal := ENNReal.toReal_nonneg
  have hlhs : (q' + q * (1 / 9)).toReal = q'.toReal + q.toReal * (1 / 9) := by
    rw [ENNReal.toReal_add hq't (by finiteness), ENNReal.toReal_mul]
    norm_num
  have hfin : q' + q * (1 / 9) ≠ ⊤ := by finiteness
  rw [← ENNReal.toReal_le_toReal hfin (by finiteness), hlhs]
  norm_num
  linarith

/-- The largest `X`-count that counts as an escape below the tight phase-3
band `2 y ≤ 3 d`.  Stated as a definition so that the escape event has the
`level z ≤ m` shape that `feller_ruin_u` consumes. -/
def phase3EscapeBound (n γ : ℕ) : ℕ :=
  (2 * n - 3 * phase3Scale n γ - 1) / 2

/-- The escape event really is a `level ≤ m` event. -/
theorem phase3_escape_iff (n γ x : ℕ) (h3 : 3 ≤ n)
    (hsize : 6 * phase3Scale n γ ≤ n) :
    2 * x + 3 * phase3Scale n γ < 2 * n ↔ x ≤ phase3EscapeBound n γ := by
  unfold phase3EscapeBound
  omega

/-- **The phase-3 Feller supermartingale.**  On the chain frozen at the escape
event, the ruin potential `(1/3)^x` never increases in expectation. -/
theorem phase3_feller_hfroz
    (n γ : ℕ) (h3 : 3 ≤ n) (hsize : 6 * phase3Scale n γ ≤ n) (x : ℕ) :
    expect
        (freeze (fun z => z ≤ phase3EscapeBound n γ)
          (productiveTriChain n) x)
        (fun z => ((1 : ℝ≥0∞) / 3) ^ z)
      ≤ ((1 : ℝ≥0∞) / 3) ^ x := by
  classical
  by_cases hesc : x ≤ phase3EscapeBound n γ
  · simp [freeze, hesc]
  · rw [show freeze (fun z => z ≤ phase3EscapeBound n γ)
          (productiveTriChain n) x = productiveTriChain n x by
      simp [freeze, hesc]]
    by_cases hxn : n ≤ x
    · rw [show productiveTriChain n x = PMF.pure x by
        unfold productiveTriChain
        rw [dif_neg (by omega)]]
      simp
    · have hstop : ¬ Phase3Stop n γ x := by
        unfold Phase3Stop
        push Not
        refine ⟨by omega, ?_, by omega⟩
        have := (phase3_escape_iff n γ x h3 hsize).not
        omega
      obtain ⟨a, b, hx, hpop, hprod, hguard⟩ :=
        phase3_live_interior h3 hsize hstop
      subst hx
      rw [productiveTriChain_apply hpop hprod, expect_productiveTriInterior]
      have hq : (3 : ℝ≥0∞) / 4 ≤ (a : ℝ≥0∞) / ((a : ℝ≥0∞) + (b : ℝ≥0∞)) :=
        productive_down_mass_ge_three_quarters hprod hguard
      have hsum : (a : ℝ≥0∞) / ((a : ℝ≥0∞) + (b : ℝ≥0∞))
          + (b : ℝ≥0∞) / ((a : ℝ≥0∞) + (b : ℝ≥0∞)) = 1 := by
        have := productiveTriInterior_masses a b hprod
        rw [add_comm] at this
        simpa using this
      have hscalar := phase3_feller_scalar_step hsum hq
      have hsq : ((1 : ℝ≥0∞) / 3) ^ 2 = 1 / 9 := by
        rw [← ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness),
          ENNReal.toReal_pow, ENNReal.toReal_div, ENNReal.toReal_div]
        norm_num
      rw [show ((1 : ℝ≥0∞) / 3) ^ (a + 2) = ((1 : ℝ≥0∞) / 3) ^ a * (1 / 9) by
          rw [pow_add, hsq],
        show ((1 : ℝ≥0∞) / 3) ^ (a + 1) = ((1 : ℝ≥0∞) / 3) ^ a * (1 / 3) by
          rw [pow_succ]]
      calc
        (b : ℝ≥0∞) / ((a : ℝ≥0∞) + (b : ℝ≥0∞)) * ((1 : ℝ≥0∞) / 3) ^ a
            + (a : ℝ≥0∞) / ((a : ℝ≥0∞) + (b : ℝ≥0∞))
                * (((1 : ℝ≥0∞) / 3) ^ a * (1 / 9))
            = ((b : ℝ≥0∞) / ((a : ℝ≥0∞) + (b : ℝ≥0∞))
                + (a : ℝ≥0∞) / ((a : ℝ≥0∞) + (b : ℝ≥0∞)) * (1 / 9))
              * ((1 : ℝ≥0∞) / 3) ^ a := by ring
        _ ≤ (1 / 3) * ((1 : ℝ≥0∞) / 3) ^ a := mul_le_mul_left hscalar _
        _ = ((1 : ℝ≥0∞) / 3) ^ a * (1 / 3) := by ring

/-- A one-step-closed predicate is closed along the whole iterate.  (A public
copy of the pattern used privately in `Tri/PaperLemma3.lean`.) -/
theorem iter_support_closed
    {α : Type*} (K : α → PMF α) (P : α → Prop)
    (hstep : ∀ s, P s → ∀ z, K s z ≠ 0 → P z) :
    ∀ T s z, P s → iter K T s z ≠ 0 → P z := by
  intro T
  induction T with
  | zero =>
      intro s z hs hz
      simp only [iter, PMF.pure_apply] at hz
      by_cases h : z = s
      · rwa [h]
      · simp [h] at hz
  | succ T ih =>
      intro s z hs hz
      rw [iter_succ, PMF.bind_apply] at hz
      by_contra hzP
      apply hz
      rw [ENNReal.tsum_eq_zero]
      intro a
      by_cases hKa : K s a = 0
      · simp [hKa]
      · have haP := hstep s hs a hKa
        have hiaz : iter K T a z = 0 := by
          by_contra hne
          exact hzP (ih a z haP hne)
        simp [hiaz]

/-- Freezing preserves a one-step-closed predicate. -/
theorem freeze_support_closed
    {α : Type*} (K : α → PMF α) (B P : α → Prop) [DecidablePred B]
    (hstep : ∀ s, P s → ∀ z, K s z ≠ 0 → P z) :
    ∀ s, P s → ∀ z, freeze B K s z ≠ 0 → P z := by
  intro s hs z hz
  unfold freeze at hz
  by_cases hB : B s
  · rw [if_pos hB] at hz
    simp only [PMF.pure_apply] at hz
    by_cases h : z = s
    · rwa [h]
    · simp [h] at hz
  · rw [if_neg hB] at hz
    exact hstep s hs z hz

/-- The productive chain never leaves the physical range `x ≤ n`. -/
theorem productiveTriChain_support_le
    (n : ℕ) : ∀ x, x ≤ n → ∀ z, productiveTriChain n x z ≠ 0 → z ≤ n := by
  intro x hx z hz
  unfold productiveTriChain at hz
  by_cases h : 3 ≤ n ∧ 0 < x ∧ x < n
  · rw [dif_pos h] at hz
    obtain ⟨h3, hx0, hxn⟩ := h
    by_contra hzn
    push Not at hzn
    apply hz
    unfold productiveTriInterior
    rw [PMF.map_apply, ENNReal.tsum_eq_zero]
    intro up
    cases up with
    | false => rw [if_neg (by simp; omega)]
    | true => rw [if_neg (by simp; omega)]
  · rw [dif_neg h] at hz
    simp only [PMF.pure_apply] at hz
    by_cases hzz : z = x
    · omega
    · simp [hzz] at hz

/-- **The general productive down-mass bound.**  On the guard `k b ≤ a` — i.e.
`k (y−1) ≤ x−1` — one productive event decreases the minority with conditional
probability at least `k / (k+1)`.

`k = 3` is the phase-3 tight guard (`2y ≤ 3 γ lg n`); `k = 5` covers the whole
of phase 2 (`y ≤ n/6`, which gives `5(y−1) ≤ x−1` whenever `6y ≤ n + 4`). -/
theorem productive_down_mass_ge
    {k a b : ℕ} (hprod : 0 < a + b) (hguard : k * b ≤ a) :
    (k : ℝ≥0∞) / ((k : ℝ≥0∞) + 1)
      ≤ (a : ℝ≥0∞) / ((a : ℝ≥0∞) + (b : ℝ≥0∞)) := by
  have hab : ((a : ℝ≥0∞) + (b : ℝ≥0∞)) = ((a + b : ℕ) : ℝ≥0∞) := by
    push_cast; ring
  have hk1 : ((k : ℝ≥0∞) + 1) = ((k + 1 : ℕ) : ℝ≥0∞) := by
    push_cast; ring
  rw [hab, hk1]
  have hne0 : ((a + b : ℕ) : ℝ≥0∞) ≠ 0 := by exact_mod_cast hprod.ne'
  have hnet : ((a + b : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hkne0 : ((k + 1 : ℕ) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (Nat.succ_ne_zero k)
  have hknet : ((k + 1 : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  rw [ENNReal.le_div_iff_mul_le (Or.inl hne0) (Or.inl hnet)]
  have hnum : ((k : ℕ) : ℝ≥0∞) / ((k + 1 : ℕ) : ℝ≥0∞) * ((a + b : ℕ) : ℝ≥0∞)
      = (((k : ℕ) : ℝ≥0∞) * ((a + b : ℕ) : ℝ≥0∞)) / ((k + 1 : ℕ) : ℝ≥0∞) := by
    simp [ENNReal.div_eq_inv_mul]
    ring
  rw [hnum, ENNReal.div_le_iff_le_mul (Or.inl hkne0) (Or.inl hknet)]
  have hnat : k * (a + b) ≤ a * (k + 1) := by
    have : k * (a + b) = k * a + k * b := by ring
    have h2 : a * (k + 1) = k * a + a := by ring
    omega
  calc ((k : ℕ) : ℝ≥0∞) * ((a + b : ℕ) : ℝ≥0∞)
      = ((k * (a + b) : ℕ) : ℝ≥0∞) := by push_cast; ring
    _ ≤ ((a * (k + 1) : ℕ) : ℝ≥0∞) := by exact_mod_cast hnat
    _ = (a : ℝ≥0∞) * ((k + 1 : ℕ) : ℝ≥0∞) := by push_cast; ring

/-- **The generic scalar contraction step.**  With `q` the success (minority-
down) mass and `q'` its complement, the one-step factor `q' + q·v` is antitone
in `q` for any `v ≤ 1`.  Hence a uniform lower bound `q₀ ≤ q` on the success
mass immediately gives the closed-form factor at `q₀`.

Every scalar step in the phase-2 and phase-3 developments is an instance:

| instance | `q₀` | `v` | factor |
|---|---|---|---|
| Corollary 3 deadline (`w = 3/4`) | `3/4` | `9/16` | `43/64` |
| Corollary 3 Feller (`u = 1/3`) | `3/4` | `1/9` | `1/3` |
| Corollary 2 deadline (`w = 3/4`) | `5/6` | `9/16` | `61/96` |
| Corollary 2 Feller (`u = 1/2`) | `5/6` | `1/4` | `3/8` |

Stating it once means a symbolic `q₀` — as the `α`-relaxed protocol needs —
costs no more than a numeral one. -/
theorem scalar_step_antitone {q q' q₀ q₀' v : ℝ≥0∞}
    (hsum : q + q' = 1) (hsum₀ : q₀ + q₀' = 1) (hq : q₀ ≤ q) (hv : v ≤ 1) :
    q' + q * v ≤ q₀' + q₀ * v := by
  have hqt : q ≠ ⊤ := by intro h; rw [h] at hsum; simp at hsum
  have hq't : q' ≠ ⊤ := by intro h; rw [h] at hsum; simp at hsum
  have hq₀t : q₀ ≠ ⊤ := by intro h; rw [h] at hsum₀; simp at hsum₀
  have hq₀'t : q₀' ≠ ⊤ := by intro h; rw [h] at hsum₀; simp at hsum₀
  have hvt : v ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hv
  have hsumR : q.toReal + q'.toReal = 1 := by
    rw [← ENNReal.toReal_add hqt hq't, hsum, ENNReal.toReal_one]
  have hsum₀R : q₀.toReal + q₀'.toReal = 1 := by
    rw [← ENNReal.toReal_add hq₀t hq₀'t, hsum₀, ENNReal.toReal_one]
  have hqR : q₀.toReal ≤ q.toReal := (ENNReal.toReal_le_toReal hq₀t hqt).mpr hq
  have hvR : v.toReal ≤ 1 := by
    have := (ENNReal.toReal_le_toReal hvt ENNReal.one_ne_top).mpr hv
    simpa using this
  have hv0 : 0 ≤ v.toReal := ENNReal.toReal_nonneg
  have hlhs : (q' + q * v).toReal = q'.toReal + q.toReal * v.toReal := by
    rw [ENNReal.toReal_add hq't (ENNReal.mul_ne_top hqt hvt), ENNReal.toReal_mul]
  have hrhs : (q₀' + q₀ * v).toReal = q₀'.toReal + q₀.toReal * v.toReal := by
    rw [ENNReal.toReal_add hq₀'t (ENNReal.mul_ne_top hq₀t hvt), ENNReal.toReal_mul]
  rw [← ENNReal.toReal_le_toReal
      (by finiteness) (by finiteness), hlhs, hrhs]
  nlinarith [hqR, hvR, hv0]

-- VERIFICATION that the generic lemma really subsumes the four existing
-- scalar steps: re-derive each from it.

example {q q' : ℝ≥0∞} (hsum : q + q' = 1) (hq : (3 : ℝ≥0∞) / 4 ≤ q) :
    q' + q * (9 / 16) ≤ 43 / 64 := by
  refine le_trans (scalar_step_antitone (q₀ := (3 : ℝ≥0∞) / 4)
    (q₀' := (1 : ℝ≥0∞) / 4) hsum ?_ hq (by
    rw [ENNReal.div_le_iff_le_mul (Or.inl (by norm_num)) (Or.inl (by norm_num))]
    norm_num)) (le_of_eq ?_)
  · rw [← ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness),
      ENNReal.toReal_add (by finiteness) (by finiteness),
      ENNReal.toReal_div, ENNReal.toReal_div, ENNReal.toReal_one]
    norm_num
  · rw [← ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness),
      ENNReal.toReal_add (by finiteness) (by finiteness),
      ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_div,
      ENNReal.toReal_div, ENNReal.toReal_div]
    norm_num

example {q q' : ℝ≥0∞} (hsum : q + q' = 1) (hq : (5 : ℝ≥0∞) / 6 ≤ q) :
    q' + q * (9 / 16) ≤ 61 / 96 := by
  refine le_trans (scalar_step_antitone (q₀ := (5 : ℝ≥0∞) / 6)
    (q₀' := (1 : ℝ≥0∞) / 6) hsum ?_ hq (by
    rw [ENNReal.div_le_iff_le_mul (Or.inl (by norm_num)) (Or.inl (by norm_num))]
    norm_num)) (le_of_eq ?_)
  · rw [← ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness),
      ENNReal.toReal_add (by finiteness) (by finiteness),
      ENNReal.toReal_div, ENNReal.toReal_div, ENNReal.toReal_one]
    norm_num
  · rw [← ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness),
      ENNReal.toReal_add (by finiteness) (by finiteness),
      ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_div,
      ENNReal.toReal_div, ENNReal.toReal_div]
    norm_num

end Tri

#print axioms Tri.productive_down_mass_ge_three_quarters
#print axioms Tri.phase3_live_interior
#print axioms Tri.phase3_scalar_step
#print axioms Tri.expect_mono
#print axioms Tri.phase3_stopped_potential_step
#print axioms Tri.phase3_count_tail_base_collapse
#print axioms Tri.phase3_count_tail_le_exp
#print axioms Tri.phase3_feller_ruin_le_exp
#print axioms Tri.phase3_feller_scalar_step
#print axioms Tri.phase3_escape_iff
#print axioms Tri.phase3_feller_hfroz
#print axioms Tri.iter_support_closed
#print axioms Tri.freeze_support_closed
#print axioms Tri.productiveTriChain_support_le
#print axioms Tri.productive_down_mass_ge
#print axioms Tri.scalar_step_antitone
