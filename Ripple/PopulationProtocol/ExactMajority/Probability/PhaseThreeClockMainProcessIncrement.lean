-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockMainProcessIncrement.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockMainProcess

/-!
# Bounded increments of the killed Main process

The three nontrivial transitions are treated separately.

* accepted live step: `|ΔΦ| ≤ 2/M + 1.1/C ≤ 35/(4n)` and the discount
  correction is at most `1/n`;
* rejected live step: only the discount correction is paid, at most `1/n`;
* waiting-to-live step: the added guard `front = 1` gives
  `1.1/C < 10/n`.

All other transitions freeze or have value zero.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal BigOperators MeasureTheory ProbabilityTheory

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockMainProcessIncrement

open TimeTheorem PairLog PairLogAuxiliary StageEventSpec
  PhaseThreeClockMainAlgebra PhaseThreeClockMainTerminal
  PhaseThreeClockMainProcess PhaseThreeClockCore PhaseThreeClockVirtual TraceDrain
open PhaseThreeModel.Numeric

variable {n : ℕ} (init : InputCfg n)

/-! ## Seed arithmetic -/

theorem mainSeed_two_le_population (seed : MainSeed init) : 2 ≤ n := by
  have hlarge := seed.2.clock_large
  have hupper := seed.2.clock_upper
  omega

theorem mainSeed_main_pos (seed : MainSeed init) : 0 < mainSeedM init seed := by
  have hn := mainSeed_two_le_population init seed
  have hmain := seed.2.main_lower
  unfold mainSeedM
  omega

theorem mainSeed_clock_pos (seed : MainSeed init) : 0 < mainSeedC init seed := by
  have hlarge := seed.2.clock_large
  unfold mainSeedC
  omega

theorem mainSeed_population_real_pos (seed : MainSeed init) : 0 < (n : ℝ) := by
  have h2 := mainSeed_two_le_population init seed
  exact_mod_cast (show 0 < n by omega)

theorem mainSeed_main_real_pos (seed : MainSeed init) :
    0 < (mainSeedM init seed : ℝ) := by
  exact_mod_cast mainSeed_main_pos init seed

theorem mainSeed_clock_real_pos (seed : MainSeed init) :
    0 < (mainSeedC init seed : ℝ) := by
  exact_mod_cast mainSeed_clock_pos init seed

theorem mainSeed_main_lower_real (seed : MainSeed init) :
    (12 : ℝ) * n ≤ 25 * (mainSeedM init seed : ℝ) := by
  exact_mod_cast seed.2.main_lower

theorem mainSeed_main_upper_real (seed : MainSeed init) :
    25 * (mainSeedM init seed : ℝ) ≤ 13 * n := by
  exact_mod_cast seed.2.main_upper

theorem mainSeed_clock_lower_real (seed : MainSeed init) :
    (6 : ℝ) * n ≤ 25 * (mainSeedC init seed : ℝ) := by
  exact_mod_cast seed.2.clock_lower

/-! ## Discount arithmetic -/

theorem mainPairDenominator_pos (seed : MainSeed init) :
    0 < mainPairDenominator n := by
  unfold mainPairDenominator
  have hn : (2 : ℝ) ≤ n := by exact_mod_cast mainSeed_two_le_population init seed
  exact mul_pos (by linarith) (by linarith)

theorem mainKappa_nonneg (seed : MainSeed init) :
    0 ≤ mainKappa init seed := by
  unfold mainKappa
  exact div_nonneg (by positivity)
    (mul_nonneg (by norm_num) (mainPairDenominator_pos init seed).le)

/-- The deliberately loose bound `κ ≤ 1/n`. -/
theorem mainKappa_le_inv_population (seed : MainSeed init) :
    mainKappa init seed ≤ 1 / (n : ℝ) := by
  have hnNat := mainSeed_two_le_population init seed
  have hn : 0 < (n : ℝ) := mainSeed_population_real_pos init seed
  have hnPred : 0 < (n : ℝ) - 1 := by
    have : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
    linarith
  have hMnat : mainSeedM init seed ≤ n := by
    have h := seed.2.main_upper
    unfold mainSeedM
    omega
  have hM : (mainSeedM init seed : ℝ) ≤ n := by exact_mod_cast hMnat
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hnNat
  have hsmall :
      12 * (mainSeedM init seed : ℝ) ≤ 2500 * ((n : ℝ) - 1) := by
    linarith
  have hmul := mul_le_mul_of_nonneg_right hsmall hn.le
  unfold mainKappa mainPairDenominator
  rw [div_le_div_iff₀
    (mul_pos (by norm_num)
      (mul_pos hn hnPred)) hn]
  simpa only [one_mul] using (by
    calc
      12 * (mainSeedM init seed : ℝ) * (n : ℝ) ≤
          (2500 * ((n : ℝ) - 1)) * (n : ℝ) := hmul
      _ = 2500 * ((n : ℝ) * ((n : ℝ) - 1)) := by ring)

/-- `q⁻¹` lies in `[0,1]`. -/
theorem mainQ_inv_bounds (seed : MainSeed init) :
    0 ≤ (mainQ init seed)⁻¹ ∧ (mainQ init seed)⁻¹ ≤ 1 := by
  have hk := mainKappa_nonneg init seed
  have hqpos : 0 < mainQ init seed := by
    unfold mainQ
    linarith
  have hqone : (1 : ℝ) ≤ mainQ init seed := by
    unfold mainQ
    linarith
  constructor
  · exact inv_nonneg.mpr hqpos.le
  · simpa only [inv_one] using
      (inv_anti₀ (show (0 : ℝ) < 1 by norm_num) hqone)

/-- The per-step discount correction is at most `1/n`. -/
theorem mainInverseQ_gap_le (seed : MainSeed init) :
    |(mainQ init seed)⁻¹ - 1| ≤ 1 / (n : ℝ) := by
  have hk := mainKappa_nonneg init seed
  have hq := mainQ_inv_bounds init seed
  have hqpos : 0 < mainQ init seed := by
    unfold mainQ
    linarith
  have hinv : mainQ init seed * (mainQ init seed)⁻¹ = 1 :=
    mul_inv_cancel₀ (ne_of_gt hqpos)
  have halg :
      1 - (mainQ init seed)⁻¹ =
        mainKappa init seed * (mainQ init seed)⁻¹ := by
    unfold mainQ at hinv ⊢
    nlinarith
  rw [abs_of_nonpos (by linarith [hq.2])]
  have hneg : -((mainQ init seed)⁻¹ - 1) = 1 - (mainQ init seed)⁻¹ := by ring
  rw [hneg, halg]
  exact (mul_le_mul_of_nonneg_left hq.2 hk).trans
    (by simpa only [mul_one] using mainKappa_le_inv_population init seed)

theorem mainDiscount_bounds (seed : MainSeed init) (age : ℕ) :
    0 ≤ mainDiscount init seed age ∧ mainDiscount init seed age ≤ 1 := by
  unfold mainDiscount
  have hq := mainQ_inv_bounds init seed
  exact ⟨pow_nonneg hq.1 age, pow_le_one₀ hq.1 hq.2⟩

theorem mainDiscount_succ (seed : MainSeed init) (age : ℕ) :
    mainDiscount init seed (age + 1) =
      mainDiscount init seed age * (mainQ init seed)⁻¹ := by
  simp only [mainDiscount, pow_succ]

/-! ## Potential and atom bounds -/

theorem mainLivePotential_abs_le_one {h : ℕ} (data : MainLive init h) :
    |mainPotential init data.seed data.credit data.front| ≤ 1 := by
  have hM := mainSeed_main_real_pos init data.seed
  have hC := mainSeed_clock_real_pos init data.seed
  have hA0 : 0 ≤ (data.credit : ℝ) / (mainSeedM init data.seed : ℝ) := by positivity
  have hZ0 : 0 ≤ (data.front : ℝ) / (mainSeedC init data.seed : ℝ) := by positivity
  have hA :
      (data.credit : ℝ) / (mainSeedM init data.seed : ℝ) ≤ (3 / 2500 : ℝ) := by
    apply (div_le_iff₀ hM).2
    have hcast :
        (2500 : ℝ) * data.credit < 3 * (mainSeedM init data.seed : ℝ) := by
      exact_mod_cast data.valid.credit_small
    nlinarith
  have hZ :
      (data.front : ℝ) / (mainSeedC init data.seed : ℝ) ≤ (1 / 1000 : ℝ) := by
    apply (div_le_iff₀ hC).2
    have hcast :
        (data.front : ℝ) < (mainSeedC init data.seed : ℝ) / 1000 := by
      have hfront := data.valid.front_small
      unfold smallThreshold at hfront
      have hfloor :
          (mainSeedC init data.seed / 1000 : ℕ) ≤ mainSeedC init data.seed :=
        Nat.div_le_self _ _
      have h1 : (data.front : ℝ) < ((mainSeedC init data.seed / 1000 : ℕ) : ℝ) := by
        exact_mod_cast hfront
      have h2 : ((mainSeedC init data.seed / 1000 : ℕ) : ℝ) ≤
          (mainSeedC init data.seed : ℝ) / 1000 := Nat.cast_div_le
      linarith
    nlinarith
  have hterm :
      0 ≤ (11 / 10 : ℝ) *
        ((data.front : ℝ) / (mainSeedC init data.seed : ℝ)) := by positivity
  have htriangle := abs_sub_le
    ((data.credit : ℝ) / (mainSeedM init data.seed : ℝ)) 0
    ((11 / 10 : ℝ) * ((data.front : ℝ) / (mainSeedC init data.seed : ℝ)))
  have htriangle' :
      |mainPotential init data.seed data.credit data.front| ≤
        (data.credit : ℝ) / (mainSeedM init data.seed : ℝ) +
          (11 / 10 : ℝ) *
            ((data.front : ℝ) / (mainSeedC init data.seed : ℝ)) := by
    unfold mainPotential
    simpa only [sub_zero, zero_sub, abs_neg, abs_of_nonneg hA0,
      abs_of_nonneg hterm] using htriangle
  exact htriangle'.trans (by nlinarith)

theorem mainLiveValue_abs_le_one {h : ℕ} (data : MainLive init h) :
    |data.value| ≤ 1 := by
  rw [data.valid.value_eq]
  unfold mainLiveValue
  rw [abs_mul]
  have hw := mainDiscount_bounds init data.seed data.age
  have hp := mainLivePotential_abs_le_one init data
  calc
    |mainDiscount init data.seed data.age| *
        |mainPotential init data.seed data.credit data.front| =
        mainDiscount init data.seed data.age *
          |mainPotential init data.seed data.credit data.front| := by
      rw [abs_of_nonneg hw.1]
    _ ≤ 1 * 1 := mul_le_mul hw.2 hp (abs_nonneg _) (by norm_num)
    _ = 1 := by norm_num

theorem mainPairCredit_le_two (h : ℕ) (lab : Lab init)
    (draw : Option (Fin init.card × Fin init.card)) :
    mainPairCredit init h lab draw ≤ 2 := by
  cases draw with
  | none => simp [mainPairCredit]
  | some pair =>
      rcases pair with ⟨i, j⟩
      simpa only [mainPairCredit] using
        step_credit_atom_le_two h (lab i) (lab j)

theorem mainPairRaising_le_one (h : ℕ) (lab : Lab init)
    (draw : Option (Fin init.card × Fin init.card)) :
    mainPairRaising init h lab draw ≤ 1 := by
  classical
  cases draw with
  | none => simp [mainPairRaising]
  | some pair =>
      rcases pair with ⟨i, j⟩
      simp only [mainPairRaising]
      split_ifs <;> omega

def mainPotentialDelta (seed : MainSeed init) (credit front : ℕ) : ℝ :=
  (credit : ℝ) / (mainSeedM init seed : ℝ) -
    (11 / 10 : ℝ) * ((front : ℝ) / (mainSeedC init seed : ℝ))

theorem mainPotential_add (seed : MainSeed init) (credit front dCredit dFront : ℕ) :
    mainPotential init seed (credit + dCredit) (front + dFront) =
      mainPotential init seed credit front +
        mainPotentialDelta init seed dCredit dFront := by
  unfold mainPotential mainPotentialDelta
  push_cast
  ring

theorem mainPotentialDelta_abs_le (seed : MainSeed init)
    {dCredit dFront : ℕ} (hCredit : dCredit ≤ 2) (hFront : dFront ≤ 1) :
    |mainPotentialDelta init seed dCredit dFront| ≤
      35 / (4 * (n : ℝ)) := by
  have hn := mainSeed_population_real_pos init seed
  have hM := mainSeed_main_real_pos init seed
  have hC := mainSeed_clock_real_pos init seed
  have hdCredit : (dCredit : ℝ) ≤ 2 := by exact_mod_cast hCredit
  have hdFront : (dFront : ℝ) ≤ 1 := by exact_mod_cast hFront
  have hCreditM :
      (dCredit : ℝ) / (mainSeedM init seed : ℝ) ≤ 25 / (6 * (n : ℝ)) := by
    calc
      (dCredit : ℝ) / (mainSeedM init seed : ℝ) ≤
          2 / (mainSeedM init seed : ℝ) :=
        div_le_div_of_nonneg_right hdCredit hM.le
      _ ≤ 25 / (6 * (n : ℝ)) := by
        rw [div_le_div_iff₀ hM (mul_pos (by norm_num) hn)]
        nlinarith only [mainSeed_main_lower_real init seed]
  have hFrontC :
      (dFront : ℝ) / (mainSeedC init seed : ℝ) ≤ 25 / (6 * (n : ℝ)) := by
    calc
      (dFront : ℝ) / (mainSeedC init seed : ℝ) ≤
          1 / (mainSeedC init seed : ℝ) :=
        div_le_div_of_nonneg_right hdFront hC.le
      _ ≤ 25 / (6 * (n : ℝ)) := by
        rw [div_le_div_iff₀ hC (mul_pos (by norm_num) hn)]
        nlinarith only [mainSeed_clock_lower_real init seed]
  have hleft : 0 ≤ (dCredit : ℝ) / (mainSeedM init seed : ℝ) := by positivity
  have hright :
      0 ≤ (11 / 10 : ℝ) *
        ((dFront : ℝ) / (mainSeedC init seed : ℝ)) := by positivity
  have htriangle := abs_sub_le
    ((dCredit : ℝ) / (mainSeedM init seed : ℝ)) 0
    ((11 / 10 : ℝ) * ((dFront : ℝ) / (mainSeedC init seed : ℝ)))
  have htriangle' :
      |mainPotentialDelta init seed dCredit dFront| ≤
        (dCredit : ℝ) / (mainSeedM init seed : ℝ) +
          (11 / 10 : ℝ) *
            ((dFront : ℝ) / (mainSeedC init seed : ℝ)) := by
    unfold mainPotentialDelta
    simpa only [sub_zero, zero_sub, abs_neg, abs_of_nonneg hleft,
      abs_of_nonneg hright] using htriangle
  calc
    |mainPotentialDelta init seed dCredit dFront| ≤
        (dCredit : ℝ) / (mainSeedM init seed : ℝ) +
          (11 / 10 : ℝ) *
            ((dFront : ℝ) / (mainSeedC init seed : ℝ)) := htriangle'
    _ ≤ 25 / (6 * (n : ℝ)) +
        (11 / 10 : ℝ) * (25 / (6 * (n : ℝ))) := by
      gcongr
    _ = 35 / (4 * (n : ℝ)) := by
      field_simp [ne_of_gt hn]
      <;> ring

/-! ## A reusable discounted-jump calculation -/

/-- If `w,r ∈ [0,1]`, the raw potential changes by at most `35/(4n)`, the
old potential has absolute value at most one, and `|r-1| ≤ 1/n`, then the
discounted jump is at most `10/n`. -/
theorem discounted_step_bound {population : ℝ} {weight ratio old delta : ℝ}
    (hpopulation : 0 < population)
    (hweight0 : 0 ≤ weight) (hweight1 : weight ≤ 1)
    (hratio0 : 0 ≤ ratio) (hratio1 : ratio ≤ 1)
    (hgap : |ratio - 1| ≤ 1 / population)
    (hold : |old| ≤ 1)
    (hdelta : |delta| ≤ 35 / (4 * population)) :
    |weight * ratio * (old + delta) - weight * old| ≤
      10 / population := by
  have hweightRatio : weight * ratio ≤ 1 := by
    calc
      weight * ratio ≤ 1 * ratio :=
        mul_le_mul_of_nonneg_right hweight1 hratio0
      _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left hratio1 (by norm_num)
      _ = 1 := by norm_num
  have hfirst : |weight * ratio * delta| ≤ 35 / (4 * population) := by
    rw [abs_mul, abs_mul, abs_of_nonneg hweight0, abs_of_nonneg hratio0]
    calc
      weight * ratio * |delta| ≤ 1 * |delta| :=
        mul_le_mul_of_nonneg_right hweightRatio (abs_nonneg delta)
      _ ≤ 35 / (4 * population) := by simpa only [one_mul] using hdelta
  have hweightGap : weight * |ratio - 1| ≤ 1 / population := by
    calc
      weight * |ratio - 1| ≤ 1 * |ratio - 1| :=
        mul_le_mul_of_nonneg_right hweight1 (abs_nonneg _)
      _ ≤ 1 * (1 / population) :=
        mul_le_mul_of_nonneg_left hgap (by norm_num)
      _ = 1 / population := by norm_num
  have hsecond : |weight * (ratio - 1) * old| ≤ 1 / population := by
    rw [abs_mul, abs_mul, abs_of_nonneg hweight0]
    calc
      weight * |ratio - 1| * |old| ≤
          (1 / population) * |old| :=
        mul_le_mul_of_nonneg_right hweightGap (abs_nonneg old)
      _ ≤ (1 / population) * 1 :=
        mul_le_mul_of_nonneg_left hold (by positivity)
      _ = 1 / population := by ring
  have hsplit :
      weight * ratio * (old + delta) - weight * old =
        weight * ratio * delta + weight * (ratio - 1) * old := by ring
  rw [hsplit]
  calc
    |weight * ratio * delta + weight * (ratio - 1) * old| ≤
        |weight * ratio * delta| + |weight * (ratio - 1) * old| :=
      abs_add_le _ _
    _ ≤ 35 / (4 * population) + 1 / population :=
      add_le_add hfirst hsecond
    _ = 39 / (4 * population) := by
      field_simp [ne_of_gt hpopulation]
      <;> ring
    _ ≤ 10 / population := by
      rw [div_le_div_iff₀ (mul_pos (by norm_num) hpopulation) hpopulation]
      nlinarith

/-! ## The three nontrivial transitions -/

/-- Accepted candidate, including the accepted step which first hits a barrier. -/
theorem mainAcceptedValue_increment {h : ℕ} (data : MainLive init h)
    (draw : Option (Fin init.card × Fin init.card)) :
    |mainNextValue init data draw - data.value| ≤ mainJumpBound n := by
  let dCredit := mainPairCredit init h data.lab draw
  let dFront := mainPairRaising init h data.lab draw
  have hdelta := mainPotentialDelta_abs_le init data.seed
    (mainPairCredit_le_two init h data.lab draw)
    (mainPairRaising_le_one init h data.lab draw)
  have hpotential := mainLivePotential_abs_le_one init data
  have hdiscount := mainDiscount_bounds init data.seed data.age
  have hratio := mainQ_inv_bounds init data.seed
  have hgap := mainInverseQ_gap_le init data.seed
  have hn := mainSeed_population_real_pos init data.seed
  rw [data.valid.value_eq]
  unfold mainNextValue mainNextAge mainNextCredit mainNextFront mainLiveValue
  rw [mainDiscount_succ, mainPotential_add]
  change
    |mainDiscount init data.seed data.age * (mainQ init data.seed)⁻¹ *
        (mainPotential init data.seed data.credit data.front +
          mainPotentialDelta init data.seed dCredit dFront) -
      mainDiscount init data.seed data.age *
        mainPotential init data.seed data.credit data.front| ≤ mainJumpBound n
  simpa only [mainJumpBound] using
    discounted_step_bound
      (population := (n : ℝ))
      (weight := mainDiscount init data.seed data.age)
      (ratio := (mainQ init data.seed)⁻¹)
      (old := mainPotential init data.seed data.credit data.front)
      (delta := mainPotentialDelta init data.seed dCredit dFront)
      hn hdiscount.1 hdiscount.2 hratio.1 hratio.2 hgap hpotential hdelta

/-- Rejected live step, killed before installing its candidate credit/front atom. -/
theorem mainKilledValue_increment {h : ℕ} (data : MainLive init h) :
    |mainKillValue init data.seed data.value - data.value| ≤ mainJumpBound n := by
  classical
  have hn := mainSeed_population_real_pos init data.seed
  have hgap := mainInverseQ_gap_le init data.seed
  have hvalue := mainLiveValue_abs_le_one init data
  unfold mainKillValue
  split_ifs with hnonneg
  · have hsplit :
        (mainQ init data.seed)⁻¹ * data.value - data.value =
          ((mainQ init data.seed)⁻¹ - 1) * data.value := by ring
    rw [hsplit, abs_mul]
    have hone : 1 / (n : ℝ) ≤ 10 / (n : ℝ) :=
      div_le_div_of_nonneg_right (by norm_num) hn.le
    exact (mul_le_mul hgap hvalue (abs_nonneg _) (by positivity)).trans
      (by unfold mainJumpBound; linarith [hone])
  · simp only [sub_self, abs_zero]
    exact div_nonneg (by norm_num) hn.le

/-- Waiting-to-live jump.  The globally necessary `front = 1` guard is used here. -/
theorem mainStartValue_increment {h : ℕ} (seed : MainSeed init)
    (lab : Lab init) (front : ℕ)
    (start : MainStartCondition init h seed lab front
      (mainStartValue init seed front)) :
    |mainStartValue init seed front - 0| ≤ mainJumpBound n := by
  have hn := mainSeed_population_real_pos init seed
  have hC := mainSeed_clock_real_pos init seed
  have hclock := mainSeed_clock_lower_real init seed
  have hratio :
      (11 : ℝ) / (10 * (mainSeedC init seed : ℝ)) ≤ 10 / (n : ℝ) := by
    rw [div_le_div_iff₀ (mul_pos (by norm_num) hC) hn]
    nlinarith only [hclock]
  rw [start.front_one]
  have hvalue :
      mainStartValue init seed 1 =
        -(11 : ℝ) / (10 * (mainSeedC init seed : ℝ)) := by
    unfold mainStartValue mainLiveValue mainDiscount mainPotential
    simp only [pow_zero, one_mul, Nat.cast_zero, zero_div, Nat.cast_one]
    field_simp [ne_of_gt hC]
    <;> ring
  rw [hvalue, sub_zero, neg_div, abs_neg, abs_of_nonneg (by positivity)]
  simpa only [mainJumpBound] using hratio

/-! ## The state, pfx, and full-path increment -/

/-- Item 2 at the raw state-transition level. -/
theorem mainProcessStep_increment (h nextTime : ℕ)
    (state : MainProcessState init h)
    (draw : Option (Fin init.card × Fin init.card))
    (nextLab : Lab init) (nextCfg : InputCfg n) :
    |mainStateValue
        (mainProcessStep init h nextTime state draw nextLab nextCfg) -
      mainStateValue state| ≤ mainJumpBound n := by
  cases state with
  | dormant =>
      change |mainStateValue
          (mainMakeSeedState init h nextTime nextLab nextCfg) - 0| ≤ _
      rw [mainMakeSeedState_value_zero]
      simp only [sub_zero, abs_zero]
      exact mainJumpBound_nonneg n
  | waiting data =>
      change |mainStateValue (mainWaitingStep init h data nextLab) - 0| ≤ _
      rcases mainWaitingStep_value_cases init h data nextLab with hzero | hstart
      · rw [hzero]
        simp only [sub_zero, abs_zero]
        exact mainJumpBound_nonneg n
      · obtain ⟨start, hvalue⟩ := hstart
        rw [hvalue]
        exact mainStartValue_increment init data.seed nextLab
          (mainWaitingFront init h nextLab) start
  | live data =>
      change |mainStateValue (mainLiveStep init h data draw nextLab) - data.value| ≤ _
      rcases mainLiveStep_value_cases init h data draw nextLab with haccepted | hkilled
      · rw [haccepted]
        exact mainAcceptedValue_increment init data draw
      · rw [hkilled]
        exact mainKilledValue_increment init data
  | stopped value =>
      simp [mainProcessStep, mainStateValue, mainJumpBound_nonneg]
  | killed value =>
      simp [mainProcessStep, mainStateValue, mainJumpBound_nonneg]

/-- The same estimate directly on a finite pfx. -/
theorem mainPrefixState_increment (h t : ℕ)
    (pfx : (k : Finset.Iic (t + 1)) → MainDraw) :
    |mainStateValue (mainPrefixState init h (t + 1) pfx) -
      mainStateValue
        (mainPrefixState init h t (mainPrefixRestrict pfx))| ≤
      mainJumpBound n := by
  simp only [mainPrefixState]
  exact mainProcessStep_increment init h (t + 1)
    (mainPrefixState init h t (mainPrefixRestrict pfx))
    (mainPrefixDraw init t pfx)
    (auxPrefix init virtualRule (t + 1) pfx)
    (prefixCfg init (t + 1) pfx)

/-- Item 2 in the exact field shape of `HourTerminalCertificate.increment`. -/
theorem mainProcessY_increment (h t : ℕ) (ω : InputLog n) :
    |mainProcessY init h (t + 1) ω - mainProcessY init h t ω| ≤
      mainJumpBound n := by
  change
    |mainStateValue
        (mainPrefixState init h (t + 1) (frestrictLe (t + 1) ω)) -
      mainStateValue (mainPrefixState init h t (frestrictLe t ω))| ≤
      mainJumpBound n
  have hprefix := mainPrefixState_increment init h t (frestrictLe (t + 1) ω)
  simpa only [mainPrefixRestrict, restrictPrefix_frestrictLe] using hprefix

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockMainProcessIncrement

end
