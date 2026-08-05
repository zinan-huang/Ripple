/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.InfectionActivationEarly
import Mathlib.Algebra.Order.Ring.GeomSum

/-!
# Common-error activation schedules

Small final activation rungs cannot use their unscaled `exp(-scale)` errors in
a headline union bound. This file assigns each rung the longer multiplier
`L / scale + 1`, making every rung cost at most `exp(-L)`, and composes the
resulting heterogeneous deterministic horizons.
-/

namespace Tri

open scoped ENNReal

/-! ## Budgeted early ladder -/

theorem infectionActivation_doubling_budget_Reaches
    (n a L : ℕ) (h3 : 3 ≤ n) (ha : 1 ≤ a)
    (hquarter : 4 * a ≤ n) :
    Reaches (infectionStateStep n h3)
      (128 * n * infectionStageMultiplier L a)
      (fun s : InfectionState n => a ≤ s.1.active)
      (fun s => 2 * a ≤ s.1.active)
      (ENNReal.ofReal (Real.exp (-(L : ℝ)))) := by
  intro s hs
  exact infectionActivation_doubling_reaches_budget
    n a L h3 ha hquarter s hs

def infectionEarlyBudgetHorizon
    (n a L k : ℕ) : ℕ :=
  ∑ j ∈ Finset.range k,
    128 * n * infectionStageMultiplier L (infectionEarlyLevel a j)

noncomputable def infectionStageBudgetError (L : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-(L : ℝ)))

noncomputable def infectionEarlyBudgetError
    (L k : ℕ) : ℝ≥0∞ :=
  k * infectionStageBudgetError L

theorem infectionEarlyMultiplierSum_le
    (a L k : ℕ) (ha : 1 ≤ a) :
    (∑ j ∈ Finset.range k,
        infectionStageMultiplier L (infectionEarlyLevel a j)) ≤
      2 * L + k := by
  calc
    (∑ j ∈ Finset.range k,
        infectionStageMultiplier L (infectionEarlyLevel a j)) ≤
        ∑ j ∈ Finset.range k, (L / 2 ^ j + 1) := by
      apply Finset.sum_le_sum
      intro j hj
      unfold infectionStageMultiplier infectionEarlyLevel
      apply Nat.add_le_add_right
      apply Nat.div_le_div_left
      · have hpow : 0 < 2 ^ j := by positivity
        nlinarith
      · positivity
    _ = (∑ j ∈ Finset.range k, L / 2 ^ j) + k := by
      rw [Finset.sum_add_distrib]
      simp
    _ ≤ 2 * L + k := by
      exact Nat.add_le_add_right
        (by
          simpa [Nat.mul_comm] using
            (Nat.geom_sum_le (b := 2) (by norm_num) L k))
        k

theorem infectionEarlyBudgetHorizon_le
    (n a L k : ℕ) (ha : 1 ≤ a) :
    infectionEarlyBudgetHorizon n a L k ≤
      128 * n * (2 * L + k) := by
  unfold infectionEarlyBudgetHorizon
  calc
    (∑ j ∈ Finset.range k,
        128 * n *
          infectionStageMultiplier L (infectionEarlyLevel a j)) =
        128 * n *
          ∑ j ∈ Finset.range k,
            infectionStageMultiplier L (infectionEarlyLevel a j) := by
      rw [Finset.mul_sum]
    _ ≤ 128 * n * (2 * L + k) :=
      Nat.mul_le_mul_left _
        (infectionEarlyMultiplierSum_le a L k ha)

theorem infectionActivation_early_budget_ladder
    (n a L k : ℕ) (h3 : 3 ≤ n) (ha : 1 ≤ a)
    (hvalid : ∀ j < k, 4 * infectionEarlyLevel a j ≤ n) :
    Reaches (infectionStateStep n h3)
      (infectionEarlyBudgetHorizon n a L k)
      (fun s : InfectionState n => a ≤ s.1.active)
      (fun s => infectionEarlyLevel a k ≤ s.1.active)
      (infectionEarlyBudgetError L k) := by
  let P : ℕ → InfectionState n → Prop :=
    fun j s => infectionEarlyLevel a j ≤ s.1.active
  let T : ℕ → ℕ := fun j =>
    128 * n * infectionStageMultiplier L (infectionEarlyLevel a j)
  let ε : ℕ → ℝ≥0∞ := fun _ => infectionStageBudgetError L
  have hrungs : ∀ j < k,
      Reaches (infectionStateStep n h3) (T j)
        (P j) (P (j + 1)) (ε j) := by
    intro j hj
    have hstage :=
      infectionActivation_doubling_budget_Reaches
        n (infectionEarlyLevel a j) L h3
        (infectionEarlyLevel_pos a j ha)
        (hvalid j hj)
    simpa only [P, T, ε, infectionEarlyLevel_succ] using hstage
  have hchain :=
    Reaches.chain
      (K := infectionStateStep n h3)
      (P := P) (T := T) (ε := ε) hrungs
  simpa [P, T, ε, infectionEarlyBudgetHorizon,
    infectionEarlyBudgetError] using hchain

theorem infectionActivation_early_budget_to_quarter
    (n a L : ℕ) (h3 : 3 ≤ n) (ha : 1 ≤ a) :
    Reaches (infectionStateStep n h3)
      (infectionEarlyBudgetHorizon n a L
        (infectionEarlyStages n a ha))
      (fun s : InfectionState n => a ≤ s.1.active)
      (fun s => infectionQuarter n ≤ s.1.active)
      (infectionEarlyBudgetError L
        (infectionEarlyStages n a ha)) := by
  have h :=
    infectionActivation_early_budget_ladder
      n a L (infectionEarlyStages n a ha) h3 ha
      (fun j hj => infectionEarlyStages_valid n a ha j hj)
  exact h.mono_post (fun s hs =>
    infectionQuarter_le_of_cover n s.1.active
      ((infectionEarlyStages_quarter n a ha).trans
        (Nat.mul_le_mul_left 4 hs)))

/-! ## Budgeted late ladder -/

theorem infectionActivation_late_budget_Reaches
    (n a i L : ℕ) (h3 : 3 ≤ n) (ha : 2 ≤ a) (hi : 1 ≤ i)
    (hquarter : n ≤ 4 * a) (hroom : a + 2 * i ≤ n + 1) :
    Reaches (infectionStateStep n h3)
      (1024 * n * infectionStageMultiplier L i)
      (fun s : InfectionState n => a ≤ s.1.active)
      (fun s => a + i ≤ s.1.active)
      (infectionStageBudgetError L) := by
  intro s hs
  exact infectionActivation_late_reaches_budget
    n a i L h3 ha hi hquarter hroom s hs

def infectionLateBudgetHorizon
    (n L : ℕ) : ℕ → ℕ
  | 0 => 0
  | r + 1 =>
      let i := ((r + 1) + 1) / 2
      1024 * n * infectionStageMultiplier L i +
        infectionLateBudgetHorizon n L ((r + 1) / 2)
termination_by r => r
decreasing_by omega

/-- Sum of the scale-dependent horizon multipliers in the late schedule. -/
def infectionLateMultiplierSum
    (L : ℕ) : ℕ → ℕ
  | 0 => 0
  | r + 1 =>
      infectionStageMultiplier L (((r + 1) + 1) / 2) +
        infectionLateMultiplierSum L ((r + 1) / 2)
termination_by r => r
decreasing_by omega

/-- Sum of just the division terms in the late multipliers. -/
def infectionLateDivSum
    (L : ℕ) : ℕ → ℕ
  | 0 => 0
  | r + 1 =>
      L / (((r + 1) + 1) / 2) +
        infectionLateDivSum L ((r + 1) / 2)
termination_by r => r
decreasing_by omega

theorem infectionLateMultiplierSum_eq
    (L r : ℕ) :
    infectionLateMultiplierSum L r =
      infectionLateDivSum L r + infectionLateStages r := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
      cases r with
      | zero =>
          simp [infectionLateMultiplierSum,
            infectionLateDivSum, infectionLateStages]
      | succ r =>
          have hlt : (r + 1) / 2 < r + 1 := by omega
          rw [infectionLateMultiplierSum, infectionLateDivSum,
            infectionLateStages, infectionStageMultiplier,
            ih ((r + 1) / 2) hlt]
          omega

private theorem infectionLate_reciprocal_step
    (R i r' : ℕ) (hr' : 0 < r')
    (hi : i = (R + 1) / 2) (hrdef : r' = R / 2) :
    (1 : ℝ) / (i : ℝ) + 2 / (R : ℝ) ≤
      2 / (r' : ℝ) := by
  have hcases :
      (R = 2 * r' ∧ i = r') ∨
        (R = 2 * r' + 1 ∧ i = r' + 1) := by
    omega
  rcases hcases with ⟨hR, hi'⟩ | ⟨hR, hi'⟩
  · rw [hR, hi']
    norm_num only [Nat.cast_mul]
    field_simp
    norm_num
  · rw [hR, hi']
    have hrR : (0 : ℝ) < r' := by exact_mod_cast hr'
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_one]
    field_simp
    nlinarith

private theorem infectionLateDivSum_real_le
    (L r : ℕ) (hr : 0 < r) :
    (infectionLateDivSum L r : ℝ) ≤
      (3 - 2 / (r : ℝ)) * (L : ℝ) := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
      cases r with
      | zero => omega
      | succ r =>
          let R := r + 1
          let i := (R + 1) / 2
          let r' := R / 2
          by_cases hr'zero : r' = 0
          · have hR : R = 1 := by
              dsimp only [r', R] at hr'zero ⊢
              omega
            have hi : i = 1 := by
              dsimp only [i]
              omega
            norm_num [infectionLateDivSum, R, i, hR]
          · have hr'pos : 0 < r' := Nat.pos_of_ne_zero hr'zero
            have hr'lt : r' < R := by
              dsimp only [r', R]
              omega
            have htail :=
              ih r' hr'lt hr'pos
            have hiPos : 0 < i := by
              dsimp only [i, R]
              omega
            have hdiv :
                ((L / i : ℕ) : ℝ) ≤
                  (L : ℝ) / (i : ℝ) :=
              Nat.cast_div_le
            have hrecip :
                (1 : ℝ) / (i : ℝ) + 2 / (R : ℝ) ≤
                  2 / (r' : ℝ) :=
              infectionLate_reciprocal_step R i r'
                hr'pos rfl rfl
            have hcoeff :
                (1 : ℝ) / (i : ℝ) - 2 / (r' : ℝ) ≤
                  -2 / (R : ℝ) := by
              have hx :
                  (1 : ℝ) / (i : ℝ) ≤
                    2 / (r' : ℝ) - 2 / (R : ℝ) :=
                (le_sub_iff_add_le).2 hrecip
              calc
                (1 : ℝ) / (i : ℝ) - 2 / (r' : ℝ) ≤
                    (2 / (r' : ℝ) - 2 / (R : ℝ)) -
                      2 / (r' : ℝ) :=
                  sub_le_sub_right hx _
                _ = -2 / (R : ℝ) := by ring
            calc
              (infectionLateDivSum L R : ℝ) =
                  ((L / i : ℕ) : ℝ) +
                    (infectionLateDivSum L r' : ℝ) := by
                simp only [R, i, r', infectionLateDivSum]
                rw [Nat.cast_add]
              _ ≤ (L : ℝ) / (i : ℝ) +
                    (3 - 2 / (r' : ℝ)) * (L : ℝ) :=
                add_le_add hdiv htail
              _ = (3 + ((1 : ℝ) / (i : ℝ) -
                    2 / (r' : ℝ))) * (L : ℝ) := by
                field_simp
                ring
              _ ≤ (3 - 2 / (R : ℝ)) * (L : ℝ) := by
                apply mul_le_mul_of_nonneg_right
                · linarith
                · positivity

theorem infectionLateDivSum_le
    (L r : ℕ) :
    infectionLateDivSum L r ≤ 3 * L := by
  cases r with
  | zero =>
      simp [infectionLateDivSum]
  | succ r =>
      have hreal :=
        infectionLateDivSum_real_le L (r + 1) (by omega)
      have hcoeff : (3 - 2 / ((r + 1 : ℕ) : ℝ)) ≤ 3 := by
        exact sub_le_self _ (by positivity)
      have hreal' :
          (infectionLateDivSum L (r + 1) : ℝ) ≤
            3 * (L : ℝ) :=
        hreal.trans
          (mul_le_mul_of_nonneg_right hcoeff (by positivity))
      exact_mod_cast hreal'

theorem infectionLateMultiplierSum_le
    (L r : ℕ) :
    infectionLateMultiplierSum L r ≤
      3 * L + infectionLateStages r := by
  rw [infectionLateMultiplierSum_eq]
  exact Nat.add_le_add_right (infectionLateDivSum_le L r) _

theorem infectionLateBudgetHorizon_eq
    (n L r : ℕ) :
    infectionLateBudgetHorizon n L r =
      1024 * n * infectionLateMultiplierSum L r := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
      cases r with
      | zero =>
          simp [infectionLateBudgetHorizon,
            infectionLateMultiplierSum]
      | succ r =>
          have hlt : (r + 1) / 2 < r + 1 := by omega
          rw [infectionLateBudgetHorizon,
            infectionLateMultiplierSum,
            ih ((r + 1) / 2) hlt]
          ring

theorem infectionLateBudgetHorizon_le
    (n L r : ℕ) :
    infectionLateBudgetHorizon n L r ≤
      1024 * n * (3 * L + infectionLateStages r) := by
  rw [infectionLateBudgetHorizon_eq]
  exact Nat.mul_le_mul_left _
    (infectionLateMultiplierSum_le L r)

theorem infectionLateStages_le_log_succ
    (r : ℕ) :
    infectionLateStages r ≤ Nat.log 2 r + 1 := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
      cases r with
      | zero =>
          simp [infectionLateStages]
      | succ r =>
          let R := r + 1
          let r' := R / 2
          by_cases hr'zero : r' = 0
          · have hR : R = 1 := by
              dsimp only [r', R] at hr'zero ⊢
              omega
            simp [infectionLateStages, R, hR]
          · have hr'pos : 0 < r' := Nat.pos_of_ne_zero hr'zero
            have hr'lt : r' < R := by
              dsimp only [r', R]
              omega
            have hih := ih r' hr'lt
            have hlog :
                Nat.log 2 r' = Nat.log 2 R - 1 := by
              dsimp only [r']
              exact Nat.log_div_base 2 R
            have hlogPos : 1 ≤ Nat.log 2 R := by
              apply Nat.log_pos (by norm_num)
              have : 2 ≤ R := by
                dsimp only [r'] at hr'zero
                omega
              exact this
            rw [infectionLateStages]
            change 1 + infectionLateStages r' ≤ Nat.log 2 R + 1
            omega

theorem infectionActivationBudgetHorizon_le
    (n a L : ℕ) (hn : 0 < n) (ha : 1 ≤ a) :
    infectionEarlyBudgetHorizon n a L
          (infectionEarlyStages n a ha) +
        infectionLateBudgetHorizon n L (n - infectionQuarter n) ≤
      1152 * n * (3 * L + Nat.log 2 n + 1) := by
  let k := infectionEarlyStages n a ha
  let r := n - infectionQuarter n
  let C := 3 * L + Nat.log 2 n + 1
  have hk : k ≤ Nat.log 2 n := by
    dsimp only [k]
    exact infectionEarlyStages_le_log n a hn ha
  have hrn : r ≤ n := by
    dsimp only [r]
    exact Nat.sub_le _ _
  have hlogr : Nat.log 2 r ≤ Nat.log 2 n :=
    Nat.log_monotone hrn
  have hstages : infectionLateStages r ≤ Nat.log 2 n + 1 :=
    (infectionLateStages_le_log_succ r).trans
      (Nat.add_le_add_right hlogr 1)
  have hearly :
      infectionEarlyBudgetHorizon n a L k ≤ 128 * n * C := by
    calc
      infectionEarlyBudgetHorizon n a L k ≤
          128 * n * (2 * L + k) :=
        infectionEarlyBudgetHorizon_le n a L k ha
      _ ≤ 128 * n * C := by
        apply Nat.mul_le_mul_left
        dsimp only [C]
        omega
  have hlate :
      infectionLateBudgetHorizon n L r ≤ 1024 * n * C := by
    calc
      infectionLateBudgetHorizon n L r ≤
          1024 * n * (3 * L + infectionLateStages r) :=
        infectionLateBudgetHorizon_le n L r
      _ ≤ 1024 * n * C := by
        apply Nat.mul_le_mul_left
        dsimp only [C]
        omega
  dsimp only [k, r] at hearly hlate ⊢
  calc
    infectionEarlyBudgetHorizon n a L
          (infectionEarlyStages n a ha) +
        infectionLateBudgetHorizon n L (n - infectionQuarter n) ≤
        128 * n * C + 1024 * n * C :=
      Nat.add_le_add hearly hlate
    _ = 1152 * n * C := by ring

noncomputable def infectionLateBudgetError
    (L : ℕ) : ℕ → ℝ≥0∞
  | 0 => 0
  | r + 1 =>
      infectionStageBudgetError L +
        infectionLateBudgetError L ((r + 1) / 2)
termination_by r => r
decreasing_by omega

theorem infectionLateBudgetError_eq_stage_count
    (L r : ℕ) :
    infectionLateBudgetError L r =
      infectionLateStages r * infectionStageBudgetError L := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
      cases r with
      | zero =>
          simp [infectionLateBudgetError, infectionLateStages]
      | succ r =>
          have hlt : (r + 1) / 2 < r + 1 := by omega
          rw [infectionLateBudgetError, infectionLateStages,
            ih ((r + 1) / 2) hlt]
          push_cast
          ring

theorem infectionActivation_late_budget_to_all
    (n r L : ℕ) (h3 : 3 ≤ n) (hrn : r ≤ n)
    (ha : 2 ≤ n - r) (hquarter : n ≤ 4 * (n - r)) :
    Reaches (infectionStateStep n h3)
      (infectionLateBudgetHorizon n L r)
      (fun s : InfectionState n => n - r ≤ s.1.active)
      (fun s => n ≤ s.1.active)
      (infectionLateBudgetError L r) := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
      cases r with
      | zero =>
          intro s hs
          simp only [infectionLateBudgetHorizon,
            infectionLateBudgetError, iter]
          rw [tsum_eq_single s (by
            intro z hzs
            simp [PMF.pure_apply, hzs])]
          simpa using hs
      | succ r =>
          let R := r + 1
          let i := (R + 1) / 2
          let r' := R / 2
          let a := n - R
          have hr'lt : r' < R := by
            dsimp only [r', R]
            omega
          have hiPos : 1 ≤ i := by
            dsimp only [i, R]
            omega
          have hr'n : r' ≤ n := by
            have : r' ≤ R := hr'lt.le
            exact this.trans hrn
          have hlevel : a + i = n - r' := by
            dsimp only [a, i, r', R]
            omega
          have ha2 : 2 ≤ a := by
            dsimp only [a, R]
            exact ha
          have haQuarter : n ≤ 4 * a := by
            dsimp only [a, R]
            exact hquarter
          have hroom : a + 2 * i ≤ n + 1 := by
            dsimp only [a, i, R]
            omega
          have hr'a : 2 ≤ n - r' := by
            rw [← hlevel]
            omega
          have hr'quarter : n ≤ 4 * (n - r') := by
            have har' : a ≤ n - r' := by
              rw [← hlevel]
              omega
            exact haQuarter.trans (Nat.mul_le_mul_left 4 har')
          have hstage :
              Reaches (infectionStateStep n h3)
                (1024 * n * infectionStageMultiplier L i)
                (fun s : InfectionState n => a ≤ s.1.active)
                (fun s => n - r' ≤ s.1.active)
                (infectionStageBudgetError L) := by
            simpa only [hlevel] using
              (infectionActivation_late_budget_Reaches
                n a i L h3 ha2 hiPos haQuarter hroom)
          have hrest :=
            ih r' hr'lt hr'n hr'a hr'quarter
          have hcomp := hstage.comp hrest
          simpa only [R, a, i, r', infectionLateBudgetHorizon,
            infectionLateBudgetError] using hcomp

/-! ## Complete budgeted activation schedule -/

theorem infectionActivation_budget_to_all
    (n a L : ℕ) (h3 : 3 ≤ n) (hn : 5 ≤ n) (ha : 1 ≤ a) :
    Reaches (infectionStateStep n h3)
      (infectionEarlyBudgetHorizon n a L
          (infectionEarlyStages n a ha) +
        infectionLateBudgetHorizon n L (n - infectionQuarter n))
      (fun s : InfectionState n => a ≤ s.1.active)
      (fun s => n ≤ s.1.active)
      (infectionEarlyBudgetError L (infectionEarlyStages n a ha) +
        infectionLateBudgetError L (n - infectionQuarter n)) := by
  let q := infectionQuarter n
  let r := n - q
  have hqn : q ≤ n := by
    dsimp only [q]
    exact infectionQuarter_le n (by omega)
  have hnsub : n - r = q := by
    dsimp only [r]
    exact Nat.sub_sub_self hqn
  have hearly :=
    infectionActivation_early_budget_to_quarter n a L h3 ha
  have hrn : r ≤ n := by
    dsimp only [r]
    exact Nat.sub_le _ _
  have hlate :=
    infectionActivation_late_budget_to_all
      n r L h3 hrn
      (by
        rw [hnsub]
        exact two_le_infectionQuarter n hn)
      (by
        rw [hnsub]
        exact infectionQuarter_covers n)
  have hlateQ :
      Reaches (infectionStateStep n h3)
        (infectionLateBudgetHorizon n L r)
        (fun s : InfectionState n => q ≤ s.1.active)
        (fun s => n ≤ s.1.active)
        (infectionLateBudgetError L r) := by
    simpa only [hnsub] using hlate
  simpa only [q, r] using hearly.comp hlateQ

theorem infectionActivation_budget_error_eq
    (n a L : ℕ) (ha : 1 ≤ a) :
    infectionEarlyBudgetError L (infectionEarlyStages n a ha) +
        infectionLateBudgetError L (n - infectionQuarter n) =
      (infectionEarlyStages n a ha +
          infectionLateStages (n - infectionQuarter n)) *
        infectionStageBudgetError L := by
  rw [infectionLateBudgetError_eq_stage_count]
  unfold infectionEarlyBudgetError
  ring

theorem infectionActivation_budget_stage_count_le
    (n a : ℕ) (hn : 0 < n) (ha : 1 ≤ a) :
    infectionEarlyStages n a ha +
        infectionLateStages (n - infectionQuarter n) ≤
      2 * Nat.log 2 n + 1 := by
  have hearly :=
    infectionEarlyStages_le_log n a hn ha
  have hrn : n - infectionQuarter n ≤ n :=
    Nat.sub_le _ _
  have hlate :
      infectionLateStages (n - infectionQuarter n) ≤
        Nat.log 2 n + 1 :=
    (infectionLateStages_le_log_succ
      (n - infectionQuarter n)).trans
      (Nat.add_le_add_right (Nat.log_monotone hrn) 1)
  omega

theorem infectionActivation_budget_error_le
    (n a L : ℕ) (hn : 0 < n) (ha : 1 ≤ a) :
    infectionEarlyBudgetError L (infectionEarlyStages n a ha) +
        infectionLateBudgetError L (n - infectionQuarter n) ≤
      (2 * Nat.log 2 n + 1) * infectionStageBudgetError L := by
  rw [infectionActivation_budget_error_eq n a L ha]
  have hcast :
      ((infectionEarlyStages n a ha +
          infectionLateStages (n - infectionQuarter n) : ℕ) : ℝ≥0∞) ≤
        ((2 * Nat.log 2 n + 1 : ℕ) : ℝ≥0∞) := by
    exact_mod_cast infectionActivation_budget_stage_count_le n a hn ha
  have hmul :=
    mul_le_mul_right hcast (infectionStageBudgetError L)
  simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one,
    mul_comm] using hmul

end Tri

#print axioms Tri.infectionActivation_early_budget_ladder
#print axioms Tri.infectionEarlyBudgetHorizon_le
#print axioms Tri.infectionLateBudgetHorizon_le
#print axioms Tri.infectionLateStages_le_log_succ
#print axioms Tri.infectionActivationBudgetHorizon_le
#print axioms Tri.infectionLateBudgetError_eq_stage_count
#print axioms Tri.infectionActivation_late_budget_to_all
#print axioms Tri.infectionActivation_budget_to_all
#print axioms Tri.infectionActivation_budget_error_le
