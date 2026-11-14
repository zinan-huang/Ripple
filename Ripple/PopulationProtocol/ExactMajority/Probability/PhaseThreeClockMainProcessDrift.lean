-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockMainProcessDrift.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockMainPairCounts

/-!
# Conditional drift of the killed Main process

For a live state, `mainUpperIncrement` is the candidate accepted increment even when
the sampled pair is rejected.  A rejected pair has no gated raising atom, and
`killed_discount_le` makes the installed killed value no larger than this candidate.
The candidate is a predictable affine combination of the contact, deep-cancellation,
and gated-tick indicators.  Their exact conditional laws are supplied by
`pairInd_condExp`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal BigOperators MeasureTheory ProbabilityTheory

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockMainProcessDrift

open TimeTheorem PairLog PairLogAuxiliary StageEventSpec
  PhaseThreeClockVirtual PhaseThreeClockGatedLaw PhaseThreeClockGatedLevelOne
  PhaseThreeClockMainAlgebra PhaseThreeClockMainTerminal
  PhaseThreeClockMainProcess PhaseThreeClockMainProcessIncrement
  PhaseThreeClockMainPairCounts PhaseThreeClockCapSpread PhaseThreeClockCore
  TraceDrain PhaseThreeClockMainLedger PhaseThreeClockProbabilityFloors
open PhaseThreeModel.Numeric

variable {n : ℕ} (init : InputCfg n)

/-! ## Prefix recursion and indicator identities -/

theorem mainProcessState_succ (h t : ℕ) (ω : InputLog n) :
    mainProcessState init h (t + 1) ω =
      mainProcessStep init h (t + 1) (mainProcessState init h t ω)
        (drawLabels init ω (t + 1)) (virtualLabels init ω (t + 1))
        (prefixCfg init (t + 1) (frestrictLe (t + 1) ω)) := by
  unfold mainProcessState
  simp only [mainPrefixState, mainPrefixRestrict, restrictPrefix_frestrictLe,
    mainPrefixDraw, frestrictLe_apply, virtualLabels, drawLabels]
  rfl

/-- The credit atom is the affine sum of the two pair indicators. -/
theorem mainPairCredit_cast_eq_pairInd (h t : ℕ) (ω : InputLog n) :
    (mainPairCredit init h (virtualLabels init ω t)
        (drawLabels init ω (t + 1)) : ℝ) =
      pairInd init (MainContactPair init h) t ω +
        2 * pairInd init (MainDeepPair init h) t ω := by
  classical
  cases hd : drawLabels init ω (t + 1) with
  | none => simp [mainPairCredit, pairInd, hd]
  | some p =>
      rcases p with ⟨i, j⟩
      simp only [mainPairCredit, pairInd, hd, Option.some.injEq,
        Prod.mk.injEq, exists_eq_left, exists_eq_right]
      unfold MainContactPair MainDeepPair
      have hc := contactInd_le_one h (virtualLabels init ω t i)
        (virtualLabels init ω t j)
      have hd' := deepCancelInd_le_one h (virtualLabels init ω t i)
        (virtualLabels init ω t j)
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hc with h0 | h0 <;>
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hd' with h1 | h1 <;>
        simp [h0, h1] <;> norm_num

/-- The front atom is the gated-tick pair indicator. -/
theorem mainPairRaising_cast_eq_pairInd (h t : ℕ) (ω : InputLog n) :
    (mainPairRaising init h (virtualLabels init ω t)
        (drawLabels init ω (t + 1)) : ℝ) =
      pairInd init (GatedTick (mainLevel h)) t ω := by
  classical
  cases hd : drawLabels init ω (t + 1) with
  | none => simp [mainPairRaising, pairInd, hd]
  | some p =>
      rcases p with ⟨i, j⟩
      simp only [mainPairRaising, pairInd, hd, Option.some.injEq,
        Prod.mk.injEq, exists_eq_left, exists_eq_right]
      split_ifs <;> simp_all

/-! ## Predictable coefficients -/

def mainStateBase {h : ℕ} : MainProcessState init h → ℝ
  | .live data =>
      mainDiscount init data.seed data.age * (mainQ init data.seed)⁻¹ *
        (-(mainKappa init data.seed *
          mainPotential init data.seed data.credit data.front))
  | _ => 0

def mainStateContactCoeff {h : ℕ} : MainProcessState init h → ℝ
  | .live data =>
      mainDiscount init data.seed data.age * (mainQ init data.seed)⁻¹ /
        (mainSeedM init data.seed : ℝ)
  | _ => 0

def mainStateDeepCoeff {h : ℕ} : MainProcessState init h → ℝ
  | .live data =>
      2 * mainDiscount init data.seed data.age * (mainQ init data.seed)⁻¹ /
        (mainSeedM init data.seed : ℝ)
  | _ => 0

def mainStateRaisingCoeff {h : ℕ} : MainProcessState init h → ℝ
  | .live data =>
      -(11 / 10 : ℝ) *
        (mainDiscount init data.seed data.age * (mainQ init data.seed)⁻¹ /
          (mainSeedC init data.seed : ℝ))
  | _ => 0

def mainAffineIncrement (h t : ℕ) (ω : InputLog n) : ℝ :=
  mainStateBase init (mainProcessState init h t ω) +
    mainStateContactCoeff init (mainProcessState init h t ω) *
      pairInd init (MainContactPair init h) t ω +
    mainStateDeepCoeff init (mainProcessState init h t ω) *
      pairInd init (MainDeepPair init h) t ω +
    mainStateRaisingCoeff init (mainProcessState init h t ω) *
      pairInd init (GatedTick (mainLevel h)) t ω

/-- Candidate accepted increment on live states, zero otherwise. -/
def mainUpperIncrement (h t : ℕ) (ω : InputLog n) : ℝ :=
  match mainProcessState init h t ω with
  | .live data =>
      mainNextValue init data (drawLabels init ω (t + 1)) - data.value
  | _ => 0

/-- All four predictable coefficients are bounded by two on every state. -/
theorem mainStateCoeff_abs_le {h : ℕ} (s : MainProcessState init h) :
    |mainStateBase init s| ≤ 2 ∧ |mainStateContactCoeff init s| ≤ 2 ∧
      |mainStateDeepCoeff init s| ≤ 2 ∧ |mainStateRaisingCoeff init s| ≤ 2 := by
  cases s with
  | live data =>
      have hd := mainDiscount_bounds init data.seed data.age
      have hq := mainQ_inv_bounds init data.seed
      have hpot := mainLivePotential_abs_le_one init data
      have hk0 := mainKappa_nonneg init data.seed
      have hk := mainKappa_le_inv_population init data.seed
      have hn2 := mainSeed_two_le_population init data.seed
      have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn2
      have hk1 : mainKappa init data.seed ≤ 1 := by
        refine hk.trans ?_
        rw [div_le_one (by linarith)]
        linarith
      have hM : (1 : ℝ) ≤ (mainSeedM init data.seed : ℝ) := by
        exact_mod_cast mainSeed_main_pos init data.seed
      have hC : (1 : ℝ) ≤ (mainSeedC init data.seed : ℝ) := by
        exact_mod_cast mainSeed_clock_pos init data.seed
      have hdq : 0 ≤ mainDiscount init data.seed data.age * (mainQ init data.seed)⁻¹ :=
        mul_nonneg hd.1 hq.1
      have hdq1 : mainDiscount init data.seed data.age * (mainQ init data.seed)⁻¹ ≤ 1 := by
        calc _ ≤ 1 * 1 := mul_le_mul hd.2 hq.2 hq.1 (by norm_num)
          _ = 1 := by norm_num
      have hdivM : mainDiscount init data.seed data.age * (mainQ init data.seed)⁻¹ /
          (mainSeedM init data.seed : ℝ) ≤ 1 := by
        rw [div_le_one (by linarith)]
        linarith
      have hdivC : mainDiscount init data.seed data.age * (mainQ init data.seed)⁻¹ /
          (mainSeedC init data.seed : ℝ) ≤ 1 := by
        rw [div_le_one (by linarith)]
        linarith
      have hdivM0 : 0 ≤ mainDiscount init data.seed data.age * (mainQ init data.seed)⁻¹ /
          (mainSeedM init data.seed : ℝ) := div_nonneg hdq (by linarith)
      have hdivC0 : 0 ≤ mainDiscount init data.seed data.age * (mainQ init data.seed)⁻¹ /
          (mainSeedC init data.seed : ℝ) := div_nonneg hdq (by linarith)
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp only [mainStateBase]
        rw [abs_mul, abs_of_nonneg hdq, abs_neg, abs_mul, abs_of_nonneg hk0]
        have : mainKappa init data.seed * |mainPotential init data.seed data.credit data.front| ≤ 1 := by
          calc _ ≤ 1 * 1 := mul_le_mul hk1 hpot (abs_nonneg _) (by norm_num)
            _ = 1 := by norm_num
        nlinarith
      · simp only [mainStateContactCoeff]
        rw [abs_of_nonneg hdivM0]
        linarith
      · simp only [mainStateDeepCoeff]
        have : 2 * mainDiscount init data.seed data.age * (mainQ init data.seed)⁻¹ /
            (mainSeedM init data.seed : ℝ) =
            2 * (mainDiscount init data.seed data.age * (mainQ init data.seed)⁻¹ /
              (mainSeedM init data.seed : ℝ)) := by ring
        rw [this, abs_of_nonneg (by positivity)]
        linarith
      · simp only [mainStateRaisingCoeff]
        rw [abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 11 / 10),
          abs_of_nonneg hdivC0]
        linarith
  | dormant => simp [mainStateBase, mainStateContactCoeff, mainStateDeepCoeff, mainStateRaisingCoeff]
  | waiting data => simp [mainStateBase, mainStateContactCoeff, mainStateDeepCoeff, mainStateRaisingCoeff]
  | stopped value => simp [mainStateBase, mainStateContactCoeff, mainStateDeepCoeff, mainStateRaisingCoeff]
  | killed value => simp [mainStateBase, mainStateContactCoeff, mainStateDeepCoeff, mainStateRaisingCoeff]

theorem mainStateFunctional_adapted {h : ℕ}
    (F : MainProcessState init h → ℝ) (t : ℕ) :
    StronglyMeasurable[pairLogFiltration (hourIndex n) 256 t]
      (fun ω => F (mainProcessState init h t ω)) := by
  have hp : Measurable
      (fun pfx : (k : Finset.Iic t) → MainDraw (n := n) =>
        F (mainPrefixState init h t pfx)) := measurable_of_countable _
  exact (hp.comp (measurable_pairLog_prefix (hourIndex n) 256 t)).stronglyMeasurable

/-- A bounded real functional of the pfx state is integrable under the
probability law.  (The bound is needed: the raw draw type is infinite.) -/
theorem mainStateFunctional_integrable {h : ℕ}
    (F : MainProcessState init h → ℝ) (B : ℝ) (hB : ∀ s, |F s| ≤ B) (t : ℕ) :
    Integrable (fun ω => F (mainProcessState init h t ω)) (law init) := by
  have hsm := mainStateFunctional_adapted init F t
  refine Integrable.of_bound
    (hsm.mono ((pairLogFiltration (hourIndex n) 256).le t)).aestronglyMeasurable B ?_
  exact ae_of_all _ fun ω => by
    rw [Real.norm_eq_abs]
    exact hB _

private theorem predictable_mul_integrable {h : ℕ}
    (F : MainProcessState init h → ℝ) (B : ℝ) (hB : ∀ s, |F s| ≤ B)
    (A : Lab init → Fin init.card → Fin init.card → Prop) (t : ℕ) :
    Integrable
      (fun ω => F (mainProcessState init h t ω) * pairInd init A t ω)
      (law init) := by
  have hsmF := (mainStateFunctional_adapted init F t).mono
    ((pairLogFiltration (hourIndex n) 256).mono (Nat.le_succ t))
  have hsmI := pairInd_stronglyMeasurable init A t
  have hm := ((hsmF.mul hsmI).mono
    ((pairLogFiltration (hourIndex n) 256).le (t + 1))).aestronglyMeasurable (μ := law init)
  refine Integrable.of_bound hm B ?_
  exact ae_of_all _ fun ω => by
    rw [Real.norm_eq_abs, abs_mul]
    have hI : |pairInd init A t ω| ≤ 1 := by
      rcases pairInd_zero_one init A t ω with h | h <;> simp [h]
    exact (mul_le_of_le_one_right (abs_nonneg _) hI).trans (hB _)

/-! ## Candidate affine identity and rejected-step domination -/

private theorem mainQ_inv_sub_one (seed : MainSeed init) :
    (mainQ init seed)⁻¹ - 1 =
      -((mainQ init seed)⁻¹ * mainKappa init seed) := by
  have hq : 0 < mainQ init seed := by
    unfold mainQ
    linarith [mainKappa_nonneg init seed]
  have hm := mul_inv_cancel₀ (ne_of_gt hq)
  unfold mainQ at hm ⊢
  nlinarith

theorem mainUpperIncrement_eq_affine (h t : ℕ) (ω : InputLog n) :
    mainUpperIncrement init h t ω = mainAffineIncrement init h t ω := by
  cases hs : mainProcessState init h t ω with
  | dormant => simp [mainUpperIncrement, mainAffineIncrement, mainStateBase,
      mainStateContactCoeff, mainStateDeepCoeff, mainStateRaisingCoeff, hs]
  | waiting data => simp [mainUpperIncrement, mainAffineIncrement, mainStateBase,
      mainStateContactCoeff, mainStateDeepCoeff, mainStateRaisingCoeff, hs]
  | stopped value => simp [mainUpperIncrement, mainAffineIncrement, mainStateBase,
      mainStateContactCoeff, mainStateDeepCoeff, mainStateRaisingCoeff, hs]
  | killed value => simp [mainUpperIncrement, mainAffineIncrement, mainStateBase,
      mainStateContactCoeff, mainStateDeepCoeff, mainStateRaisingCoeff, hs]
  | live data =>
      have hlab := mainProcessState_lab init h t ω
      rw [hs] at hlab
      change data.lab = virtualLabels init ω t at hlab
      have hcredit := mainPairCredit_cast_eq_pairInd init h t ω
      have hraise := mainPairRaising_cast_eq_pairInd init h t ω
      rw [← hlab] at hcredit hraise
      unfold mainUpperIncrement mainAffineIncrement
      rw [hs]
      simp only [mainStateBase, mainStateContactCoeff,
        mainStateDeepCoeff, mainStateRaisingCoeff]
      rw [data.valid.value_eq]
      unfold mainNextValue mainNextAge mainNextCredit mainNextFront mainLiveValue
      rw [mainDiscount_succ, mainPotential_add]
      unfold mainPotentialDelta
      rw [hcredit, hraise]
      linear_combination (mainDiscount init data.seed data.age *
        mainPotential init data.seed data.credit data.front) *
          mainQ_inv_sub_one init data.seed

private theorem mainStartValue_nonpos (seed : MainSeed init)
    (front : ℕ) : mainStartValue init seed front ≤ 0 := by
  have hC := mainSeed_clock_real_pos init seed
  unfold mainStartValue mainLiveValue mainDiscount mainPotential
  simp only [pow_zero, one_mul, Nat.cast_zero, zero_div]
  have h0 : (0 : ℝ) ≤ (front : ℝ) / (mainSeedC init seed : ℝ) := by positivity
  have h1 : (0 : ℝ) ≤ (11 / 10 * (front : ℝ)) / (mainSeedC init seed : ℝ) := by positivity
  nlinarith [h0, h1]

private theorem mainKillValue_le_candidate_of_zero_raise {h : ℕ}
    (data : MainLive init h)
    (draw : Option (Fin init.card × Fin init.card))
    (hzero : mainPairRaising init h data.lab draw = 0) :
    mainKillValue init data.seed data.value ≤ mainNextValue init data draw := by
  have hkill := killed_discount_le (mainQ init data.seed) data.value
    (mainQ_inv_bounds init data.seed).2
  calc
    mainKillValue init data.seed data.value ≤
        (mainQ init data.seed)⁻¹ * data.value := by
      simpa only [mainKillValue] using hkill
    _ = mainDiscount init data.seed data.age * (mainQ init data.seed)⁻¹ *
        mainPotential init data.seed data.credit data.front := by
      rw [data.valid.value_eq]
      unfold mainLiveValue
      ring
    _ ≤ mainDiscount init data.seed data.age * (mainQ init data.seed)⁻¹ *
        (mainPotential init data.seed data.credit data.front +
          (mainPairCredit init h data.lab draw : ℝ) /
            (mainSeedM init data.seed : ℝ)) := by
      have hdq := mul_nonneg (mainDiscount_bounds init data.seed data.age).1
        (mainQ_inv_bounds init data.seed).1
      have hnn : (0 : ℝ) ≤ (mainPairCredit init h data.lab draw : ℝ) /
          (mainSeedM init data.seed : ℝ) := by positivity
      nlinarith [mul_nonneg hdq hnn]
    _ = mainNextValue init data draw := by
      unfold mainNextValue mainNextAge mainNextCredit mainNextFront mainLiveValue
      rw [mainDiscount_succ, mainPotential_add]
      unfold mainPotentialDelta
      rw [hzero]
      simp only [Nat.cast_zero, zero_div, mul_zero, sub_zero]

/-- The installed next value is bounded above by the accepted candidate on live
states and by the old value off live states. -/
theorem mainProcess_increment_le_upper (h t : ℕ) (hh : h ≤ hourIndex n)
    (ω : InputLog n) :
    mainProcessY init h (t + 1) ω - mainProcessY init h t ω ≤
      mainUpperIncrement init h t ω := by
  rw [mainProcessY, mainProcessY, mainProcessState_succ]
  cases hs : mainProcessState init h t ω with
  | dormant =>
      simp only [mainUpperIncrement, hs, mainProcessStep, mainMakeSeedState_value_zero]
      simp [mainStateValue]
  | waiting data =>
      simp only [mainUpperIncrement, hs, mainProcessStep]
      have h0 : mainStateValue (MainProcessState.waiting data) = 0 := rfl
      rw [h0, sub_zero]
      rcases mainWaitingStep_value_cases init h data (virtualLabels init ω (t + 1)) with
        hzero | ⟨start, hstart⟩
      · rw [hzero]
      · rw [hstart]
        exact mainStartValue_nonpos init data.seed _
  | stopped value => simp [mainUpperIncrement, hs, mainStateValue, mainProcessStep]
  | killed value => simp [mainUpperIncrement, hs, mainStateValue, mainProcessStep]
  | live data =>
      simp only [mainUpperIncrement, hs, mainStateValue, mainProcessStep]
      classical
      by_cases haccept : MainAcceptedCondition init h data.seed
          (virtualLabels init ω (t + 1))
          (mainNextCredit init data (drawLabels init ω (t + 1)))
          (mainNextFront init data (drawLabels init ω (t + 1)))
      · unfold mainLiveStep
        rw [dif_pos haccept]
        split_ifs <;> simp [mainStateValue]
      · have hzero :
          mainPairRaising init h data.lab (drawLabels init ω (t + 1)) = 0 := by
          by_contra hne
          have hone : mainPairRaising init h data.lab
              (drawLabels init ω (t + 1)) = 1 := by
            have hle := mainPairRaising_le_one init h data.lab
              (drawLabels init ω (t + 1))
            omega
          cases hd : drawLabels init ω (t + 1) with
          | none => simp [mainPairRaising, hd] at hone
          | some p =>
              rcases p with ⟨i, j⟩
              have hg : GatedTick (mainLevel h) data.lab i j := by
                simpa [mainPairRaising, hd] using hone
              have hij := (labelsAt_selected_transition init ω t i j hd).1
              have hlab := mainProcessState_lab init h t ω
              rw [hs] at hlab
              change data.lab = virtualLabels init ω t at hlab
              have hnext : virtualLabels init ω (t + 1) =
                  ruleUpdate virtualRule data.lab i j := by
                rw [virtualLabels_succ, hd, ← hlab]
                rfl
              apply haccept
              rw [hnext]
              simpa only [hd] using mainAccepted_of_gated init hh data i j hij hg
        unfold mainLiveStep
        rw [dif_neg haccept]
        simp only [mainStateValue]
        exact sub_le_sub_right
          (mainKillValue_le_candidate_of_zero_raise init data
            (drawLabels init ω (t + 1)) hzero) data.value

/-! ## Measurability and integrability of the two increments -/

theorem mainUpperIncrement_abs_le (h t : ℕ) (ω : InputLog n) :
    |mainUpperIncrement init h t ω| ≤ mainJumpBound n := by
  cases hs : mainProcessState init h t ω with
  | live data =>
      simpa only [mainUpperIncrement, hs] using
        mainAcceptedValue_increment init data (drawLabels init ω (t + 1))
  | dormant => simp [mainUpperIncrement, hs, mainJumpBound_nonneg]
  | waiting data => simp [mainUpperIncrement, hs, mainJumpBound_nonneg]
  | stopped value => simp [mainUpperIncrement, hs, mainJumpBound_nonneg]
  | killed value => simp [mainUpperIncrement, hs, mainJumpBound_nonneg]

theorem mainAffineIncrement_stronglyMeasurable (h t : ℕ) :
    StronglyMeasurable[pairLogFiltration (hourIndex n) 256 (t + 1)]
      (mainAffineIncrement init h t) := by
  have hbase := (mainStateFunctional_adapted (h := h) init (mainStateBase init) t).mono
    ((pairLogFiltration (hourIndex n) 256).mono (Nat.le_succ t))
  have hc := (mainStateFunctional_adapted (h := h) init (mainStateContactCoeff init) t).mono
    ((pairLogFiltration (hourIndex n) 256).mono (Nat.le_succ t))
  have hd := (mainStateFunctional_adapted (h := h) init (mainStateDeepCoeff init) t).mono
    ((pairLogFiltration (hourIndex n) 256).mono (Nat.le_succ t))
  have hg := (mainStateFunctional_adapted (h := h) init (mainStateRaisingCoeff init) t).mono
    ((pairLogFiltration (hourIndex n) 256).mono (Nat.le_succ t))
  exact ((hbase.add (hc.mul (pairInd_stronglyMeasurable init
      (MainContactPair init h) t))).add
    (hd.mul (pairInd_stronglyMeasurable init (MainDeepPair init h) t))).add
      (hg.mul (pairInd_stronglyMeasurable init
        (GatedTick (mainLevel h)) t))

theorem mainUpperIncrement_integrable (h t : ℕ) :
    Integrable (mainUpperIncrement init h t) (law init) := by
  have hsm : StronglyMeasurable (mainUpperIncrement init h t) := by
    rw [funext (mainUpperIncrement_eq_affine init h t)]
    exact (mainAffineIncrement_stronglyMeasurable init h t).mono
      ((pairLogFiltration (hourIndex n) 256).le (t + 1))
  refine Integrable.of_bound hsm.aestronglyMeasurable (mainJumpBound n) ?_
  exact ae_of_all _ fun ω => by
    simpa only [Real.norm_eq_abs] using mainUpperIncrement_abs_le init h t ω

theorem mainProcessIncrement_integrable (h t : ℕ) :
    Integrable (fun ω => mainProcessY init h (t + 1) ω -
      mainProcessY init h t ω) (law init) := by
  have hsm : StronglyMeasurable
      (fun ω => mainProcessY init h (t + 1) ω - mainProcessY init h t ω) :=
    ((mainProcessY_adapted init h (t + 1)).sub
      ((mainProcessY_adapted init h t).mono
        ((pairLogFiltration (hourIndex n) 256).mono (Nat.le_succ t)))).mono
          ((pairLogFiltration (hourIndex n) 256).le (t + 1))
  refine Integrable.of_bound hsm.aestronglyMeasurable (mainJumpBound n) ?_
  exact ae_of_all _ fun ω => by
    rw [Real.norm_eq_abs]
    exact mainProcessY_increment init h t ω

/-! ## Predictable affine conditional expectation -/

theorem mainPredictableAffine_condExp (h t : ℕ) :
    (law init)[mainAffineIncrement init h t |
        pairLogFiltration (hourIndex n) 256 t] =ᵐ[law init]
      fun ω =>
        mainStateBase init (mainProcessState init h t ω) +
          mainStateContactCoeff init (mainProcessState init h t ω) *
            ((law init)[pairInd init (MainContactPair init h) t |
              pairLogFiltration (hourIndex n) 256 t]) ω +
          mainStateDeepCoeff init (mainProcessState init h t ω) *
            ((law init)[pairInd init (MainDeepPair init h) t |
              pairLogFiltration (hourIndex n) 256 t]) ω +
          mainStateRaisingCoeff init (mainProcessState init h t ω) *
            ((law init)[pairInd init (GatedTick (mainLevel h)) t |
              pairLogFiltration (hourIndex n) 256 t]) ω := by
  let ℱ := pairLogFiltration (hourIndex n) 256
  let U := fun ω => mainStateBase init (mainProcessState init h t ω)
  let P := fun ω => mainStateContactCoeff init (mainProcessState init h t ω)
  let Q := fun ω => mainStateDeepCoeff init (mainProcessState init h t ω)
  let R := fun ω => mainStateRaisingCoeff init (mainProcessState init h t ω)
  let I := pairInd init (MainContactPair init h) t
  let J := pairInd init (MainDeepPair init h) t
  let K := pairInd init (GatedTick (mainLevel h)) t
  have hU := mainStateFunctional_integrable (h := h) init (mainStateBase init) 2
    (fun s => (mainStateCoeff_abs_le init s).1) t
  have hPI := predictable_mul_integrable (h := h) init (mainStateContactCoeff init) 2
    (fun s => (mainStateCoeff_abs_le init s).2.1)
    (MainContactPair init h) t
  have hQJ := predictable_mul_integrable (h := h) init (mainStateDeepCoeff init) 2
    (fun s => (mainStateCoeff_abs_le init s).2.2.1)
    (MainDeepPair init h) t
  have hRK := predictable_mul_integrable (h := h) init (mainStateRaisingCoeff init) 2
    (fun s => (mainStateCoeff_abs_le init s).2.2.2)
    (GatedTick (mainLevel h)) t
  have hIi := pairInd_integrable init (MainContactPair init h) t
  have hJi := pairInd_integrable init (MainDeepPair init h) t
  have hKi := pairInd_integrable init (GatedTick (mainLevel h)) t
  have hUs := mainStateFunctional_adapted (h := h) init (mainStateBase init) t
  have hPs := mainStateFunctional_adapted (h := h) init (mainStateContactCoeff init) t
  have hQs := mainStateFunctional_adapted (h := h) init (mainStateDeepCoeff init) t
  have hRs := mainStateFunctional_adapted (h := h) init (mainStateRaisingCoeff init) t
  have hcur : (law init)[U | ℱ t] = U :=
    condExp_of_stronglyMeasurable (ℱ.le t) hUs hU
  have hsumOne := condExp_add hU hPI (ℱ t)
  have hsumTwo := condExp_add (hU.add hPI) hQJ (ℱ t)
  have hsumThree := condExp_add ((hU.add hPI).add hQJ) hRK (ℱ t)
  have hpull := condExp_mul_of_stronglyMeasurable_left hPs hPI hIi
  have hqpull := condExp_mul_of_stronglyMeasurable_left hQs hQJ hJi
  have hrpull := condExp_mul_of_stronglyMeasurable_left hRs hRK hKi
  filter_upwards [hsumOne, hsumTwo, hsumThree, hpull, hqpull, hrpull]
    with ω hOne hTwo hThree hp hq hr
  change (law init)[((U + fun ω => P ω * I ω) + fun ω => Q ω * J ω) +
      fun ω => R ω * K ω | ℱ t] ω = _
  rw [hThree, Pi.add_apply, hTwo, Pi.add_apply, hOne, Pi.add_apply]
  try simp only [hcur]
  have hp' : (law init)[fun ω => P ω * I ω | ℱ t] ω =
      P ω * (law init)[I | ℱ t] ω := hp
  have hq' : (law init)[fun ω => Q ω * J ω | ℱ t] ω =
      Q ω * (law init)[J | ℱ t] ω := hq
  have hr' : (law init)[fun ω => R ω * K ω | ℱ t] ω =
      R ω * (law init)[K | ℱ t] ω := hr
  have hcu : (law init)[fun ω => mainStateBase init (mainProcessState init h t ω) | ℱ t] ω =
      mainStateBase init (mainProcessState init h t ω) := congrFun hcur ω
  rw [hcu, hp', hq', hr']

/-! ## Counted conditional drift -/

private theorem current_front_le_seedClock {h : ℕ} (data : MainLive init h) :
    data.front ≤ mainSeedC init data.seed := by
  rw [← data.valid.accepted.front_eq,
    ← mainSeed_clockCount_eq init data.seed data.lab data.valid.accepted.roles]
  exact frontCount_le_clockCount data.lab (mainLevel h)

/-- The conditional affine value is nonpositive on every pfx state. -/
theorem mainAffineConditional_nonpos (h t : ℕ) (hh : h ≤ hourIndex n)
    (ω : InputLog n) :
    mainStateBase init (mainProcessState init h t ω) +
        mainStateContactCoeff init (mainProcessState init h t ω) *
          (((goodPairs (MainContactPair init h) (virtualLabels init ω t)).card : ℝ) /
            ((init.card : ℝ) * ((init.card : ℝ) - 1))) +
        mainStateDeepCoeff init (mainProcessState init h t ω) *
          (((goodPairs (MainDeepPair init h) (virtualLabels init ω t)).card : ℝ) /
            ((init.card : ℝ) * ((init.card : ℝ) - 1))) +
        mainStateRaisingCoeff init (mainProcessState init h t ω) *
          (((goodPairs (GatedTick (mainLevel h)) (virtualLabels init ω t)).card : ℝ) /
            ((init.card : ℝ) * ((init.card : ℝ) - 1))) ≤ 0 := by
  cases hs : mainProcessState init h t ω with
  | dormant => simp [mainStateBase, mainStateContactCoeff,
      mainStateDeepCoeff, mainStateRaisingCoeff, hs]
  | waiting data => simp [mainStateBase, mainStateContactCoeff,
      mainStateDeepCoeff, mainStateRaisingCoeff, hs]
  | stopped value => simp [mainStateBase, mainStateContactCoeff,
      mainStateDeepCoeff, mainStateRaisingCoeff, hs]
  | killed value => simp [mainStateBase, mainStateContactCoeff,
      mainStateDeepCoeff, mainStateRaisingCoeff, hs]
  | live data =>
      have hlab := mainProcessState_lab init h t ω
      rw [hs] at hlab
      change data.lab = virtualLabels init ω t at hlab
      rw [← hlab]
      have hcard : init.card = n := data.seed.2.card_eq
      have hP : 0 < mainPairDenominator n :=
        mainPairDenominator_pos init data.seed
      have hM := mainSeed_main_real_pos init data.seed
      have hC := mainSeed_clock_real_pos init data.seed
      have hcontactNat := goodPairs_mainContact_card_le init data
      have hcontact :
          ((goodPairs (MainContactPair init h) data.lab).card : ℝ) ≤
            2 * (mainSeedM init data.seed : ℝ) * data.front := by
        exact_mod_cast hcontactNat
      have hdeep := weighted_mainDeep_card_le init data
      have hraiseNat := goodPairs_mainRaising_card_ge init data
      have hZC := current_front_le_seedClock init data
      have hraise :
          2 * (data.front : ℝ) *
              ((mainSeedC init data.seed : ℝ) - data.front) ≤
            ((goodPairs (GatedTick (mainLevel h)) data.lab).card : ℝ) := by
        have hcast :
            ((2 * data.front * (mainSeedC init data.seed - data.front) : ℕ) : ℝ) ≤
              ((goodPairs (GatedTick (mainLevel h)) data.lab).card : ℝ) := by
          exact_mod_cast hraiseNat
        simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub hZC] using hcast
      have hcredit :
          2500 * (data.credit : ℝ) ≤ 3 * (mainSeedM init data.seed : ℝ) := by
        exact_mod_cast data.valid.credit_small.le
      have hfrontNat : 1000 * data.front ≤ mainSeedC init data.seed := by
        have hfs := data.valid.front_small
        unfold smallThreshold at hfs
        omega
      have hfront :
          1000 * (data.front : ℝ) ≤ (mainSeedC init data.seed : ℝ) := by
        exact_mod_cast hfrontNat
      have hnorm := normalizedDrift_nonpos
        hM hC hP (Nat.cast_nonneg data.credit) (Nat.cast_nonneg data.front)
        (mainSeed_main_upper_real init data.seed)
        (mainSeed_clock_lower_real init data.seed) hcredit hfront
      have hdenM : 0 < (mainSeedM init data.seed : ℝ) * mainPairDenominator n :=
        mul_pos hM hP
      have hdenC : 0 < (mainSeedC init data.seed : ℝ) * mainPairDenominator n :=
        mul_pos hC hP
      have hcontactTerm :
          ((goodPairs (MainContactPair init h) data.lab).card : ℝ) /
                ((mainSeedM init data.seed : ℝ) * mainPairDenominator n) ≤
            (2 * (mainSeedM init data.seed : ℝ) * data.front) /
                ((mainSeedM init data.seed : ℝ) * mainPairDenominator n) :=
        div_le_div_of_nonneg_right hcontact hdenM.le
      have hdeepTerm :
          2 * ((goodPairs (MainDeepPair init h) data.lab).card : ℝ) /
                ((mainSeedM init data.seed : ℝ) * mainPairDenominator n) ≤
            4 * (data.credit : ℝ) ^ 2 /
                ((mainSeedM init data.seed : ℝ) * mainPairDenominator n) :=
        div_le_div_of_nonneg_right hdeep hdenM.le
      have hraiseTerm :
          -(11 / 10 : ℝ) *
              (((goodPairs (GatedTick (mainLevel h)) data.lab).card : ℝ) /
                ((mainSeedC init data.seed : ℝ) * mainPairDenominator n)) ≤
            -(11 / 10 : ℝ) *
              ((2 * (data.front : ℝ) *
                ((mainSeedC init data.seed : ℝ) - data.front)) /
                ((mainSeedC init data.seed : ℝ) * mainPairDenominator n)) := by
        have hd := div_le_div_of_nonneg_right hraise hdenC.le
        nlinarith
      have hraw :
          ((goodPairs (MainContactPair init h) data.lab).card : ℝ) /
                ((mainSeedM init data.seed : ℝ) * mainPairDenominator n) +
            2 * ((goodPairs (MainDeepPair init h) data.lab).card : ℝ) /
                ((mainSeedM init data.seed : ℝ) * mainPairDenominator n) -
            (11 / 10 : ℝ) *
              (((goodPairs (GatedTick (mainLevel h)) data.lab).card : ℝ) /
                ((mainSeedC init data.seed : ℝ) * mainPairDenominator n)) -
            mainKappa init data.seed *
              mainPotential init data.seed data.credit data.front ≤ 0 := by
        have h3 := add_le_add (add_le_add hcontactTerm hdeepTerm) hraiseTerm
        have hn := hnorm
        unfold normalizedDrift at hn
        unfold mainKappa mainPotential
        have hs : (2 * (mainSeedM init data.seed : ℝ) * (data.front : ℝ) +
              4 * (data.credit : ℝ) ^ 2) / ((mainSeedM init data.seed : ℝ) *
                mainPairDenominator n) =
            2 * (mainSeedM init data.seed : ℝ) * (data.front : ℝ) /
                ((mainSeedM init data.seed : ℝ) * mainPairDenominator n) +
              4 * (data.credit : ℝ) ^ 2 /
                ((mainSeedM init data.seed : ℝ) * mainPairDenominator n) := add_div _ _ _
        linarith [h3, hn, hs]
      have hweight :
          0 ≤ mainDiscount init data.seed data.age *
            (mainQ init data.seed)⁻¹ :=
        mul_nonneg (mainDiscount_bounds init data.seed data.age).1
          (mainQ_inv_bounds init data.seed).1
      have hden : (init.card : ℝ) * ((init.card : ℝ) - 1) = mainPairDenominator n := by
        unfold mainPairDenominator
        rw [hcard]
      rw [hden]
      have heq :
          mainStateBase init (.live data) +
              mainStateContactCoeff init (.live data) *
                (((goodPairs (MainContactPair init h) data.lab).card : ℝ) /
                  mainPairDenominator n) +
              mainStateDeepCoeff init (.live data) *
                (((goodPairs (MainDeepPair init h) data.lab).card : ℝ) /
                  mainPairDenominator n) +
              mainStateRaisingCoeff init (.live data) *
                (((goodPairs (GatedTick (mainLevel h)) data.lab).card : ℝ) /
                  mainPairDenominator n) =
            (mainDiscount init data.seed data.age *
              (mainQ init data.seed)⁻¹) *
              (((goodPairs (MainContactPair init h) data.lab).card : ℝ) /
                    ((mainSeedM init data.seed : ℝ) * mainPairDenominator n) +
                2 * ((goodPairs (MainDeepPair init h) data.lab).card : ℝ) /
                    ((mainSeedM init data.seed : ℝ) * mainPairDenominator n) -
                (11 / 10 : ℝ) *
                  (((goodPairs (GatedTick (mainLevel h)) data.lab).card : ℝ) /
                    ((mainSeedC init data.seed : ℝ) * mainPairDenominator n)) -
                mainKappa init data.seed *
                  mainPotential init data.seed data.credit data.front) := by
        simp only [mainStateBase, mainStateContactCoeff, mainStateDeepCoeff,
          mainStateRaisingCoeff]
        field_simp [ne_of_gt hM, ne_of_gt hC, ne_of_gt hP]
        <;> ring
      rw [heq]
      exact mul_nonpos_of_nonneg_of_nonpos hweight hraw

/-- Item 3 in exactly the field shape of `HourTerminalCertificate.drift`. -/
theorem mainProcessY_drift (h : ℕ) (hh : h ≤ hourIndex n)
    (hc : 2 ≤ init.card) (t : ℕ) :
    (law init)[fun ω => mainProcessY init h (t + 1) ω -
        mainProcessY init h t ω |
      pairLogFiltration (hourIndex n) 256 t] ≤ᵐ[law init]
      fun _ => 0 := by
  have hmono := condExp_mono (m := pairLogFiltration (hourIndex n) 256 t)
    (mainProcessIncrement_integrable init h t)
    (mainUpperIncrement_integrable init h t)
    (ae_of_all _ fun ω => mainProcess_increment_le_upper init h t hh ω)
  have heq :
      (law init)[mainUpperIncrement init h t |
          pairLogFiltration (hourIndex n) 256 t] =ᵐ[law init]
        (law init)[mainAffineIncrement init h t |
          pairLogFiltration (hourIndex n) 256 t] :=
    condExp_congr_ae (ae_of_all _ fun ω => mainUpperIncrement_eq_affine init h t ω)
  have haff := mainPredictableAffine_condExp init h t
  have hcLaw := pairInd_condExp init hc (MainContactPair init h) t
  have hdLaw := pairInd_condExp init hc (MainDeepPair init h) t
  have hgLaw := pairInd_condExp init hc (GatedTick (mainLevel h)) t
  filter_upwards [hmono, heq, haff, hcLaw, hdLaw, hgLaw]
    with ω hmonoω heqω haffω hcω hdω hgω
  rw [heqω, haffω, hcω, hdω, hgω] at hmonoω
  exact hmonoω.trans (mainAffineConditional_nonpos init h t hh ω)

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockMainProcessDrift

end
