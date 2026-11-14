import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockCapPassages

/-!
# The all-cap deadline (N12, step 4, PHASE3 P13)

From the genuine all-Phase-3 time `T`, every level of the virtual front passes the
half-population threshold `b = ⌈C/2⌉` in turn: while `X_i ≥ b > X_{i+1}` at least a fifth
of the ordered Clock pairs raise `X_{i+1}` (PHASE3 (25) minimized at `X_i = b`), so the
compensated product `(10/9)^{[Clock pair]} (1/2)^{[raise]}` has conditional mean at most
one and at most `b` raises occur on the window: more than `4 C` Clock pairs on a
level window has relative probability `e^{0.35 - 0.05 C}` (`half_level_tail`). Hence
all `Q` half passages use at most `4 C Q` Clock pairs, which occur within `rawWindow`
raw steps after `T` except with probability `e^{-(4CQ+1)/4}` (the lower contact tail of
`PhaseThreeClockThinning`); from half capped, each remaining Clock meets a capped Clock
at rate at least `C / (n (n - 1))` per raw step, so all are capped within
`finHalfWindow = ⌈6 n² ln n / C⌉` further steps except with probability `n^{-5}`
(`PhaseThreeClockCapPassages.high_all_tail` at the half threshold).

The fibres are indexed by the seed `s`, the all-three time `T` and the seed Clock set
`C` (`capPrefix`), measurable at `T`; the deterministic bridge `cap_of_good` shows that
outside the bad events the canonical cap satisfies `cap ≤ T + logWindow n 16000` and
`cap ≤ s + logWindow n 20000`, i.e. the cap row holds. The headline
`guarded_cap_tail` is the cap row of `PhaseThreeClockRowsGuarded.GuardedRowTails`
(guarded by the activation, passage and shape rows; only the passage row's `cap_first`
is used).
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators MeasureTheory ProbabilityTheory

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockCapDeadline

open TimeTheorem PairLog PairLogAuxiliary PhaseThreeClockVirtual
  PhaseThreeClockGatedLaw PhaseThreeClockGatedLevelOne PhaseThreeClockEmbedding
  PhaseThreeClockEmbeddingBridge PhaseThreeClockCore PhaseThreeClockRows
  PhaseThreeClockProductTails PhaseThreeScalar PhaseThreeClockPrefixTails
  PhaseThreeClockProbabilityFloors PhaseThreeClockRegime PhaseThreeClockCapSpread
  PhaseThreeClockCapPassages PhaseThreeClockThinning PhaseThreeClockProducer
open StageEventSpec hiding frontCount clockCount
open Classical

variable {n : ℕ} (init : InputCfg n)

/-- The half-population threshold `⌈C/2⌉`. -/
def halfThr (C : ℕ) : ℕ := (C + 1) / 2

theorem halfThr_le (C : ℕ) : halfThr C ≤ C := by
  unfold halfThr
  omega

theorem two_mul_halfThr_ge (C : ℕ) : C ≤ 2 * halfThr C := by
  unfold halfThr
  omega

theorem two_mul_halfThr_le (C : ℕ) : 2 * halfThr C ≤ C + 1 := by
  unfold halfThr
  omega

/-! ## Level counts on the virtual path -/

variable (ω : InputLog n)

/-- `X_ℓ(t)` on the virtual path (current roles). -/
def levelCount (ℓ t : ℕ) : ℕ := frontCount (virtualLabels init ω t) ℓ

theorem levelCount_top (t : ℕ) : levelCount init ω (clockTop n) t = topCount init ω t := rfl

theorem levelCount_zero (t : ℕ) : levelCount init ω 0 t = clockCount (virtualLabels init ω t) :=
  frontCount_zero _

theorem levelCount_le_clockCount (ℓ t : ℕ) :
    levelCount init ω ℓ t ≤ clockCount (virtualLabels init ω t) :=
  frontCount_le_clockCount _ _

theorem levelCount_succ {S T : ℕ} (hentry : AsyncEntry init ω S T) (ℓ : ℕ) (hℓ : 1 ≤ ℓ)
    (hℓQ : ℓ ≤ clockTop n) (t : ℕ) (hSt : S ≤ t) :
    (levelCount init ω ℓ (t + 1) : ℝ) =
      levelCount init ω ℓ t + pairInd init (GatedTick ℓ) t ω := by
  unfold pairInd
  cases hd : drawLabels init ω (t + 1) with
  | none =>
      unfold levelCount
      rw [frontCount_virtualLabels_succ_of_none init ω t hd]
      simp
  | some p =>
      obtain ⟨i, j⟩ := p
      unfold levelCount
      rw [frontCount_virtualLabels_succ_of_asyncEntry init ω S T hentry t hSt i j hd ℓ hℓ hℓQ]
      push_cast
      congr 1
      by_cases hg : GatedTick ℓ (virtualLabels init ω t) i j
      · rw [if_pos hg, if_pos ⟨i, j, rfl, hg⟩]
      · rw [if_neg hg, if_neg]
        rintro ⟨i', j', hd', hg'⟩
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hd')
        exact hg hg'

theorem levelCount_succ_nat {S T : ℕ} (hentry : AsyncEntry init ω S T) (ℓ : ℕ) (hℓ : 1 ≤ ℓ)
    (hℓQ : ℓ ≤ clockTop n) (t : ℕ) (hSt : S ≤ t) :
    levelCount init ω ℓ t ≤ levelCount init ω ℓ (t + 1) ∧
      levelCount init ω ℓ (t + 1) ≤ levelCount init ω ℓ t + 1 := by
  have h := levelCount_succ init ω hentry ℓ hℓ hℓQ t hSt
  rcases pairInd_zero_one init (GatedTick ℓ) t ω with h0 | h1
  · rw [h0, add_zero] at h
    have : levelCount init ω ℓ (t + 1) = levelCount init ω ℓ t := by exact_mod_cast h
    omega
  · rw [h1] at h
    have : levelCount init ω ℓ (t + 1) = levelCount init ω ℓ t + 1 := by exact_mod_cast h
    omega

/-- Every level is monotone after the seed (level `0` is the constant Clock count). -/
theorem levelCount_mono {S T : ℕ} (hentry : AsyncEntry init ω S T) (ℓ : ℕ)
    (hℓQ : ℓ ≤ clockTop n) {t t' : ℕ} (hSt : S ≤ t) (htt : t ≤ t') :
    levelCount init ω ℓ t ≤ levelCount init ω ℓ t' := by
  rcases Nat.eq_zero_or_pos ℓ with h0 | hpos
  · subst h0
    rw [levelCount_zero, levelCount_zero, clockCount_virtual_eq_seed init ω hentry t hSt,
      clockCount_virtual_eq_seed init ω hentry t' (by omega)]
  · induction t', htt using Nat.le_induction with
    | base => exact le_rfl
    | succ t' htt ih =>
        exact ih.trans (levelCount_succ_nat init ω hentry ℓ hpos hℓQ t' (by omega)).1

/-- The pair raising level `ℓ + 1` is a Clock pair. -/
theorem gatedTick_ccPair' (ℓ : ℕ) (f : Lab init) (i j : Fin init.card)
    (h : GatedTick ℓ f i j) : CCPair init f i j := by
  constructor
  · by_contra hc
    exact not_gatedTick_of_not_clock_left _ f i j hc h
  · by_contra hc
    exact not_gatedTick_of_not_clock_right _ f i j hc h

/-! ## The half-passage count floor: at least a fifth of the Clock pairs raise -/

/-- The inactive Clock count vanishes when every Clock is active. -/
theorem inactiveCount_eq_zero (f : Lab init)
    (hact : ∀ k, (f k).role = .clock → 3 ≤ (f k).phase.val) : inactiveCount f = 0 := by
  unfold inactiveCount inactiveSet
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro k _ hk
  have := hact k hk.1
  omega

/-- The gated count at level `i + 1` is the raising count when every Clock is active. -/
theorem goodPairs_gatedTick_level_card (f : Lab init) (i : ℕ)
    (hact : ∀ k, (f k).role = .clock → 3 ≤ (f k).phase.val) :
    (goodPairs (GatedTick (i + 1)) f).card =
      2 * frontCount f (i + 1) * (clockCount f - frontCount f (i + 1)) +
        exactCount f i * (exactCount f i - 1) := by
  rcases Nat.eq_zero_or_pos i with h0 | hpos
  · subst h0
    have h := goodPairs_gatedTick_card_add f
    rw [inactiveCount_eq_zero init f hact] at h
    simpa using h
  · rw [goodPairs_gatedTick_eq_of_two_le f (i + 1) (by omega), goodPairs_raisingTick_card]
    simp only [Nat.add_sub_cancel]

/-- PHASE3 P13: on the half-passage window `X_i ≥ b > X_{i+1}` (with `C ≥ 6`),
`#CC ≤ 5 · #raise`. -/
theorem half_count_floor (f : Lab init) (C : ℕ) (hC : clockCount f = C) (hC6 : 6 ≤ C) (i : ℕ)
    (hact : ∀ k, (f k).role = .clock → 3 ≤ (f k).phase.val)
    (hlo : halfThr C ≤ frontCount f i) (hhi : ¬ halfThr C ≤ frontCount f (i + 1)) :
    ((goodPairs (CCPair init) f).card : ℝ) ≤ 5 * ((goodPairs (GatedTick (i + 1)) f).card : ℝ) := by
  rw [goodPairs_ccPair_card, goodPairs_gatedTick_level_card init f i hact, hC]
  set X := frontCount f (i + 1) with hX
  set Y := exactCount f i with hY
  set b := halfThr C with hb
  have hpred := frontCount_pred f (i + 1) (by omega)
  simp only [Nat.add_sub_cancel] at hpred
  rw [← hX, ← hY] at hpred
  have hXC : X ≤ C := hC ▸ frontCount_le_clockCount f _
  have hXb : X < b := Nat.lt_of_not_le hhi
  have hYb : b ≤ X + Y := by omega
  have h2b : C ≤ 2 * b := two_mul_halfThr_ge C
  have h2b' : 2 * b ≤ C + 1 := two_mul_halfThr_le C
  -- real versions
  have hXR : (X : ℝ) + 1 ≤ b := by exact_mod_cast hXb
  have hYR : (b : ℝ) ≤ X + Y := by exact_mod_cast hYb
  have hXCR : (X : ℝ) ≤ C := by exact_mod_cast hXC
  have h2bR : (C : ℝ) ≤ 2 * b := by exact_mod_cast h2b
  have h2bR' : 2 * (b : ℝ) ≤ C + 1 := by exact_mod_cast h2b'
  have hC6R : (6 : ℝ) ≤ C := by exact_mod_cast hC6
  have hcast : ((2 * X * (C - X) + Y * (Y - 1) : ℕ) : ℝ) =
      2 * (X : ℝ) * ((C : ℝ) - X) + ((Y * (Y - 1) : ℕ) : ℝ) := by
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hXC]
    push_cast
    ring
  have hYY : (Y : ℝ) * ((Y : ℝ) - 1) ≤ ((Y * (Y - 1) : ℕ) : ℝ) := by
    rcases Nat.eq_zero_or_pos Y with hY0 | hYpos
    · rw [hY0]; simp
    · rw [Nat.cast_mul, Nat.cast_sub hYpos]
      push_cast
      exact le_rfl
  have hcc : ((C * (C - 1) : ℕ) : ℝ) = (C : ℝ) * ((C : ℝ) - 1) := by
    rw [Nat.cast_mul, Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [hcast, hcc]
  -- `Y (Y - 1) ≥ (b - X)(b - X - 1)` since `Y ≥ b - X ≥ 1`
  have hYlow : ((b : ℝ) - X) * ((b : ℝ) - X - 1) ≤ (Y : ℝ) * ((Y : ℝ) - 1) := by
    have h1 : (b : ℝ) - X ≤ Y := by linarith
    have h2 : (1 : ℝ) ≤ (b : ℝ) - X := by linarith
    nlinarith
  -- `2X(C-X) + (b-X)(b-X-1) ≥ b(b-1)` and `5 b (b-1) ≥ C (C-1)`
  have hkey : (b : ℝ) * ((b : ℝ) - 1) ≤ 2 * (X : ℝ) * ((C : ℝ) - X) +
      ((b : ℝ) - X) * ((b : ℝ) - X - 1) := by
    have hX0 : (0 : ℝ) ≤ X := Nat.cast_nonneg _
    nlinarith
  have hfive : (C : ℝ) * ((C : ℝ) - 1) ≤ 5 * ((b : ℝ) * ((b : ℝ) - 1)) := by
    nlinarith
  nlinarith

/-! ## The level windows and factors -/

section Level

variable (C : Finset (Fin init.card)) (s : ℕ) (i : ℕ)

/-- The half-passage window of level `i`: all Clocks active, the Clock count fixed,
`X_i ≥ b > X_{i+1}`. -/
def halfWindow (t : ℕ) : Set (InputLog n) :=
  {ω | clockCount (virtualLabels init ω t) = C.card ∧
    (∀ k, (virtualLabels init ω t k).role = .clock → 3 ≤ (virtualLabels init ω t k).phase.val) ∧
    halfThr C.card ≤ levelCount init ω i t ∧ ¬ halfThr C.card ≤ levelCount init ω (i + 1) t}

theorem halfWindow_measurableSet (t : ℕ) :
    MeasurableSet[pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256 t]
      (halfWindow init C i t) :=
  measurableSet_virtual_single init le_rfl (fun f =>
    clockCount f = C.card ∧ (∀ k, (f k).role = .clock → 3 ≤ (f k).phase.val) ∧
      halfThr C.card ≤ frontCount f i ∧ ¬ halfThr C.card ≤ frontCount f (i + 1))

/-- The level factor: `10/9` on a Clock pair, `1/2` on a raise of level `i + 1`. -/
def halfFactor (u : ℕ) : InputLog n → ℝ :=
  windowFactor (halfWindow init C i (s + u))
    (fun ω => affFactor init (10 / 9) (CCPair init) (s + u) ω *
      affFactor init (1 / 2) (GatedTick (i + 1)) (s + u) ω)
    (fun _ => 1)

theorem halfFactor_nonneg (u : ℕ) (ω : InputLog n) : 0 ≤ halfFactor init C s i u ω :=
  windowFactor_nonneg
    (fun ω => mul_nonneg (affFactor_nonneg init (by norm_num) _ _ ω)
      (affFactor_nonneg init (by norm_num) _ _ ω))
    (fun _ => zero_le_one) ω

theorem halfFactor_le (u : ℕ) (ω : InputLog n) : halfFactor init C s i u ω ≤ 2 :=
  windowFactor_le
    (fun ω => by
      have h1 := affFactor_le init (a := (10 / 9 : ℝ)) (b := 2) (by norm_num) (by norm_num)
        (CCPair init) (s + u) ω
      have h2 := affFactor_le init (a := (1 / 2 : ℝ)) (b := 1) (by norm_num) le_rfl
        (GatedTick (i + 1)) (s + u) ω
      have h3 := affFactor_nonneg init (by norm_num : (0 : ℝ) ≤ 10 / 9) (CCPair init) (s + u) ω
      nlinarith)
    (fun _ => by norm_num) ω

theorem halfFactor_stronglyMeasurable (u : ℕ) :
    StronglyMeasurable[shiftedFiltration
      (pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256) s (u + 1)]
      (halfFactor init C s i u) := by
  rw [shiftedFiltration_apply, ← Nat.add_assoc]
  exact windowFactor_two_stronglyMeasurable init _ _ (halfWindow init C i) _ _ (s + u)
    (halfWindow_measurableSet init C i (s + u))

/-- The conditional mean of the level factor is at most one. -/
theorem halfFactor_condExp_le_one (hc : 2 ≤ init.card) (hC6 : 6 ≤ C.card) (u : ℕ) :
    (law init)[halfFactor init C s i u | shiftedFiltration
      (pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256) s u] ≤ᵐ[law init]
      fun _ => 1 := by
  set ℱ := pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256 with hℱ
  rw [shiftedFiltration_apply]
  unfold halfFactor
  have hYeq : (fun ω => affFactor init (10 / 9) (CCPair init) (s + u) ω *
      affFactor init (1 / 2) (GatedTick (i + 1)) (s + u) ω) =
      fun ω => 1 + (10 / 9 - 1) * pairInd init (CCPair init) (s + u) ω +
        (10 / 9) * (1 / 2 - 1) * pairInd init (GatedTick (i + 1)) (s + u) ω := by
    funext ω
    exact affFactor_mul_of_imp init _ _ (gatedTick_ccPair' init (i + 1)) (s + u) ω
  rw [hYeq]
  apply windowFactor_condExp_le_one (halfWindow_measurableSet init C i (s + u))
    (affine_two_integrable init _ _ _ _ _ _) (integrable_const 1) ?_
    (condExp_one_off init _ (s + u))
  filter_upwards [condExp_affine_two init 1 (10 / 9 - 1) ((10 / 9) * (1 / 2 - 1))
      (CCPair init) (GatedTick (i + 1)) (s + u),
    pairInd_condExp init hc (CCPair init) (s + u),
    pairInd_condExp init hc (GatedTick (i + 1)) (s + u)] with ω h1 h2 h3
  intro hW
  rw [h1, h2, h3]
  obtain ⟨hCt, hact, hlo, hhi⟩ := hW
  have hfloor := half_count_floor init _ C.card hCt hC6 i hact hlo hhi
  have hP : (0 : ℝ) < (init.card : ℝ) * ((init.card : ℝ) - 1) := by
    have : (2 : ℝ) ≤ init.card := by exact_mod_cast hc
    nlinarith
  set a : ℝ := ((goodPairs (CCPair init) (virtualLabels init ω (s + u))).card : ℝ) with ha
  set b : ℝ := ((goodPairs (GatedTick (i + 1)) (virtualLabels init ω (s + u))).card : ℝ) with hb
  set P : ℝ := (init.card : ℝ) * ((init.card : ℝ) - 1) with hPdef
  have hident : (10 / 9 - 1 : ℝ) * (a / P) + (10 / 9) * (1 / 2 - 1) * (b / P) =
      (a - 5 * b) / (9 * P) := by
    field_simp
    ring
  have hle : (a - 5 * b) / (9 * P) ≤ 0 :=
    div_nonpos_iff.mpr (Or.inr ⟨by linarith, by positivity⟩)
  linarith

/-- At most `b` raises of level `i + 1` occur on the level window. -/
theorem windowCount_half_raise_le {S T : ℕ} (hentry : AsyncEntry init ω S T) (hSs : S ≤ s)
    (hiQ : i + 1 ≤ clockTop n) (N : ℕ) :
    windowCount (fun t ω => ω ∈ halfWindow init C i t ∧ StepEvent init (GatedTick (i + 1)) t ω)
      s N ω ≤ halfThr C.card := by
  -- the potential `min (X_{i+1}, b)` rises by one at each counted raise
  have hpot : ∀ N, windowCount
      (fun t ω => ω ∈ halfWindow init C i t ∧ StepEvent init (GatedTick (i + 1)) t ω) s N ω +
      min (levelCount init ω (i + 1) s) (halfThr C.card) ≤
      min (levelCount init ω (i + 1) (s + N)) (halfThr C.card) := by
    intro N
    induction N with
    | zero => simp [windowCount_zero]
    | succ N ih =>
        rw [windowCount_succ (fun t ω => ω ∈ halfWindow init C i t ∧
          StepEvent init (GatedTick (i + 1)) t ω) s N ω]
        have hstep := levelCount_succ_nat init ω hentry (i + 1) (by omega) hiQ (s + N) (by omega)
        rw [show s + (N + 1) = s + N + 1 by omega]
        by_cases h : ω ∈ halfWindow init C i (s + N) ∧ StepEvent init (GatedTick (i + 1)) (s + N) ω
        · rw [if_pos h]
          have hlt : levelCount init ω (i + 1) (s + N) < halfThr C.card :=
            Nat.lt_of_not_le h.1.2.2.2
          have hraise : (levelCount init ω (i + 1) (s + N + 1) : ℝ) =
              levelCount init ω (i + 1) (s + N) + 1 := by
            rw [levelCount_succ init ω hentry (i + 1) (by omega) hiQ (s + N) (by omega),
              pairInd_eq_ite, if_pos h.2]
          have hraise' : levelCount init ω (i + 1) (s + N + 1) =
              levelCount init ω (i + 1) (s + N) + 1 := by exact_mod_cast hraise
          omega
        · rw [if_neg h]
          omega
  have h := hpot N
  omega

/-- The level bad event: an entry, the Clock set at the seed, and at least `4 C` Clock
pairs drawn on the level window within the horizon. -/
def halfBad (N : ℕ) : Set (InputLog n) :=
  {ω | (∃ S T, AsyncEntry init ω S T ∧ S ≤ s) ∧ clockCount (virtualLabels init ω s) = C.card ∧
    4 * C.card ≤ windowCount
      (fun t ω => ω ∈ halfWindow init C i t ∧ StepEvent init (CCPair init) t ω) s N ω}

theorem log_ten_div_nine : (1 / 10 : ℝ) ≤ Real.log (10 / 9) := by
  have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 9 / 10 by norm_num)
  have hinv : Real.log ((9 / 10 : ℝ)⁻¹) = - Real.log (9 / 10) := Real.log_inv _
  rw [show ((9 / 10 : ℝ)⁻¹) = 10 / 9 by norm_num] at hinv
  rw [hinv]
  linarith

/-- The level tail: relative probability at most `e^{0.35 - 0.05 C}`. -/
theorem half_level_tail (hc : 2 ≤ init.card) (hC6 : 6 ≤ C.card) (hiQ : i + 1 ≤ clockTop n)
    (N : ℕ) (E : Set (InputLog n))
    (hE : MeasurableSet[pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256 s] E) :
    law init (E ∩ halfBad init C s i N) ≤
      ENNReal.ofReal (Real.exp (35 / 100 - (5 / 100) * C.card)) * law init E := by
  set ℱ := shiftedFiltration (pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256) s
    with hℱ
  have hE' : MeasurableSet[ℱ 0] E := by
    simpa only [hℱ, shiftedFiltration_apply, Nat.add_zero] using hE
  have hr : (0 : ℝ) < (10 / 9) ^ (4 * C.card) * (1 / 2) ^ halfThr C.card := by positivity
  have htail := prefix_product_tail_ennreal (μ := law init) (ℱ := ℱ)
    (halfFactor_stronglyMeasurable init C s i) (halfFactor_nonneg init C s i)
    (halfFactor_le init C s i) (halfFactor_condExp_le_one init C s i hc hC6) E hE' N
    (halfBad init C s i N) hr ?_
  · refine htail.trans (mul_le_mul_right' (ENNReal.ofReal_le_ofReal ?_) _)
    have hlog := log_ten_div_nine
    have hlog2 := PhaseThreeModel.Numeric.log_two_bounds.2
    have hpow1 : ((10 / 9 : ℝ)) ^ (4 * C.card) =
        Real.exp ((4 * C.card : ℕ) * Real.log (10 / 9)) := by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
    have hpow2 : ((1 / 2 : ℝ)) ^ halfThr C.card =
        Real.exp ((halfThr C.card : ℕ) * Real.log (1 / 2)) := by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
    have hl12 : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
      rw [Real.log_div (by norm_num) (by norm_num), Real.log_one]
      ring
    have hbR : 2 * (halfThr C.card : ℝ) ≤ C.card + 1 := by
      exact_mod_cast two_mul_halfThr_le C.card
    rw [hpow1, hpow2, ← Real.exp_add, one_div, ← Real.exp_neg, Real.exp_le_exp, hl12]
    push_cast
    nlinarith [show (0 : ℝ) ≤ C.card from Nat.cast_nonneg _,
      show (0 : ℝ) ≤ halfThr C.card from Nat.cast_nonneg _]
  · rintro ω ⟨-, ⟨S, T, hentry, hSs⟩, hCs, hcount⟩
    have hprod := prefixProduct_window_two init (10 / 9) (1 / 2) (halfWindow init C i)
      (CCPair init) (GatedTick (i + 1)) s N ω
    have hb := windowCount_half_raise_le init ω C s i hentry hSs hiQ N
    calc (10 / 9 : ℝ) ^ (4 * C.card) * (1 / 2) ^ halfThr C.card
        ≤ (10 / 9 : ℝ) ^ windowCount
            (fun t ω => ω ∈ halfWindow init C i t ∧ StepEvent init (CCPair init) t ω) s N ω *
          (1 / 2) ^ windowCount
            (fun t ω => ω ∈ halfWindow init C i t ∧
              StepEvent init (GatedTick (i + 1)) t ω) s N ω :=
          mul_le_mul (pow_le_pow_right₀ (by norm_num) hcount)
            (pow_le_pow_of_le_one (by norm_num) (by norm_num) hb) (by positivity) (by positivity)
      _ = prefixProduct (halfFactor init C s i) N ω := hprod.symm

end Level

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockCapDeadline

end
