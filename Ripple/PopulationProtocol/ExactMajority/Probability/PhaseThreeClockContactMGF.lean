import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockCapPassages

/-!
# The single stopping-time MGF composition of P14 (N12, step 4)

PHASE3 (60)–(62): a tagged Clock `i₀` participates in a Clock pair with probability
`2 (C - 1) / (n (n - 1))` per raw step. On the local cap window (from the first cap
to 90 % capped) its participations are compensated by the observed Clock-pair count,
`2^{[i₀ in the pair]} (C / (C + 2))^{[Clock pair]}`, whose conditional mean is exactly
one; afterwards, through `cap + T_set`, they are compensated by time,
`e^{-q} 2^{[i₀ in the pair]}`, whose conditional mean is at most one. The product is a
supermartingale on the prefix event (`PhaseThreeClockProductTails`), so by Markov the
event "at least `40 (H + 1)` participations on the two windows while the compensators
stay within `R₁` Clock pairs and `D` steps" has relative probability at most
`2^{-40 (H + 1)} (1 + 2/C)^{R₁} e^{q D}` (`tag_budget_tail`). This replaces the
tick/raw thinning of (60) and needs no independence between the two windows.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators MeasureTheory ProbabilityTheory

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockContactMGF

open TimeTheorem PairLog PairLogAuxiliary PhaseThreeClockVirtual
  PhaseThreeClockGatedLaw PhaseThreeClockGatedLevelOne PhaseThreeClockEmbedding
  PhaseThreeClockEmbeddingBridge PhaseThreeClockCore PhaseThreeClockRows
  PhaseThreeClockProductTails PhaseThreeScalar PhaseThreeClockPrefixTails
  PhaseThreeClockProbabilityFloors PhaseThreeClockRegime PhaseThreeClockCapSpread
  PhaseThreeClockCapPassages
open StageEventSpec hiding frontCount clockCount
open Classical

variable {n : ℕ} (init : InputCfg n)

section Tag

variable (C : Finset (Fin init.card)) (s : ℕ) (i₀ : Fin init.card)

/-- The Clock-pair compensation factor `C / (C + 2) = (1 + 2/C)⁻¹`. -/
def pairDiscount : ℝ := (C.card : ℝ) / ((C.card : ℝ) + 2)

theorem pairDiscount_nonneg : 0 ≤ pairDiscount init C := by
  unfold pairDiscount
  have : (0 : ℝ) ≤ C.card := Nat.cast_nonneg _
  exact div_nonneg this (by linarith)

theorem pairDiscount_le_one : pairDiscount init C ≤ 1 := by
  unfold pairDiscount
  rw [div_le_one (by positivity)]
  linarith

/-- The time compensation rate `q = 2 (C - 1) / (n (n - 1))`. -/
def tagRate : ℝ := 2 * ((C.card : ℝ) - 1) / ((init.card : ℝ) * ((init.card : ℝ) - 1))

/-- The local cap window: the Clock count fixed, `i₀` a Clock, some Clock capped, fewer
than 90 % capped. -/
def localWindow (t : ℕ) : Set (InputLog n) :=
  {ω | clockCount (virtualLabels init ω t) = C.card ∧ (virtualLabels init ω t i₀).role = .clock ∧
    ReachedTop init 1 t ω ∧ ¬ ReachedTop init (highThreshold C.card) t ω}

/-- The settling window: the Clock count fixed, `i₀` a Clock, at least 90 % capped, and
before `cap + k`. -/
def settleWindow (k : ℕ) (t : ℕ) : Set (InputLog n) :=
  {ω | clockCount (virtualLabels init ω t) = C.card ∧ (virtualLabels init ω t i₀).role = .clock ∧
    ReachedTop init (highThreshold C.card) t ω ∧ BeforeCapPlus init s k t ω}

theorem localWindow_measurableSet (t : ℕ) :
    MeasurableSet[pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256 t]
      (localWindow init C i₀ t) :=
  measurableSet_virtual_single init le_rfl (fun f =>
    clockCount f = C.card ∧ (f i₀).role = .clock ∧ 1 ≤ frontCount f (clockTop n) ∧
      ¬ highThreshold C.card ≤ frontCount f (clockTop n))

theorem settleWindow_measurableSet {k t : ℕ} (hs : s ≤ t) :
    MeasurableSet[pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256 t]
      (settleWindow init C s i₀ k t) := by
  have hset : settleWindow init C s i₀ k t =
      {ω | clockCount (virtualLabels init ω t) = C.card ∧
        (virtualLabels init ω t i₀).role = .clock ∧
        ReachedTop init (highThreshold C.card) t ω} ∩ {ω | BeforeCapPlus init s k t ω} := by
    ext ω
    simp only [settleWindow, Set.mem_setOf_eq, Set.mem_inter_iff, and_assoc]
  rw [hset]
  exact (measurableSet_virtual_single init le_rfl (fun f =>
    clockCount f = C.card ∧ (f i₀).role = .clock ∧
      highThreshold C.card ≤ frontCount f (clockTop n))).inter
    (beforeCapPlus_measurableSet init hs)

theorem localWindow_settleWindow_disjoint (k t : ℕ) (ω : InputLog n)
    (h1 : ω ∈ localWindow init C i₀ t) (h2 : ω ∈ settleWindow init C s i₀ k t) : False :=
  h1.2.2.2 h2.2.2.1

/-- The tag factor at offset `u`: on the local window
`(C/(C+2))^{[Clock pair]} 2^{[i₀ in the pair]}`, on the settling window
`e^{-q} 2^{[i₀ in the pair]}`, and `1` elsewhere. -/
def tagFactor (k : ℕ) (u : ℕ) : InputLog n → ℝ :=
  windowFactor (localWindow init C i₀ (s + u))
    (fun ω => affFactor init (pairDiscount init C) (CCPair init) (s + u) ω *
      affFactor init 2 (TagPair init i₀) (s + u) ω)
    (windowFactor (settleWindow init C s i₀ k (s + u))
      (fun ω => Real.exp (-(tagRate init C)) * affFactor init 2 (TagPair init i₀) (s + u) ω)
      (fun _ => 1))

theorem tagFactor_nonneg (hc : 2 ≤ init.card) (k u : ℕ) (ω : InputLog n) :
    0 ≤ tagFactor init C s i₀ k u ω := by
  apply windowFactor_nonneg
  · intro ω
    exact mul_nonneg (affFactor_nonneg init (pairDiscount_nonneg init C) _ _ ω)
      (affFactor_nonneg init (by norm_num) _ _ ω)
  · intro ω
    apply windowFactor_nonneg
    · intro ω
      exact mul_nonneg (Real.exp_nonneg _) (affFactor_nonneg init (by norm_num) _ _ ω)
    · intro _
      exact zero_le_one

theorem tagRate_nonneg (hc : 2 ≤ init.card) (hC : 1 ≤ C.card) : 0 ≤ tagRate init C := by
  unfold tagRate
  have h2n : (2 : ℝ) ≤ init.card := by exact_mod_cast hc
  have hC1 : (1 : ℝ) ≤ C.card := by exact_mod_cast hC
  apply div_nonneg (by linarith) (by nlinarith)

theorem tagFactor_le (hc : 2 ≤ init.card) (hC : 1 ≤ C.card) (k u : ℕ) (ω : InputLog n) :
    tagFactor init C s i₀ k u ω ≤ 2 := by
  apply windowFactor_le
  · intro ω
    have h1 := affFactor_le init (a := pairDiscount init C) (b := 1) (pairDiscount_le_one init C) le_rfl
      (CCPair init) (s + u) ω
    have h2 := affFactor_le init (a := (2 : ℝ)) (b := 2) le_rfl (by norm_num)
      (TagPair init i₀) (s + u) ω
    have h3 := affFactor_nonneg init (pairDiscount_nonneg init C) (CCPair init) (s + u) ω
    have h4 := affFactor_nonneg init (by norm_num : (0 : ℝ) ≤ 2) (TagPair init i₀) (s + u) ω
    nlinarith
  · intro ω
    apply windowFactor_le
    · intro ω
      have h2 := affFactor_le init (a := (2 : ℝ)) (b := 2) le_rfl (by norm_num)
        (TagPair init i₀) (s + u) ω
      have h4 := affFactor_nonneg init (by norm_num : (0 : ℝ) ≤ 2) (TagPair init i₀) (s + u) ω
      have he : Real.exp (-(tagRate init C)) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        linarith [tagRate_nonneg init C hc hC]
      have he0 := Real.exp_nonneg (-(tagRate init C))
      nlinarith
    · intro _
      norm_num

theorem tagFactor_stronglyMeasurable (k u : ℕ) :
    StronglyMeasurable[shiftedFiltration
      (pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256) s (u + 1)]
      (tagFactor init C s i₀ k u) := by
  rw [shiftedFiltration_apply, ← Nat.add_assoc]
  have hmono := (pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256).mono
    (Nat.le_succ (s + u))
  apply windowFactor_stronglyMeasurable (hmono _ (localWindow_measurableSet init C i₀ (s + u)))
    ((affFactor_stronglyMeasurable init _ _ _).mul (affFactor_stronglyMeasurable init _ _ _))
  apply windowFactor_stronglyMeasurable
    (hmono _ (settleWindow_measurableSet init C s i₀ (Nat.le_add_right s u)))
    ((affFactor_stronglyMeasurable init _ _ _).const_mul _) stronglyMeasurable_const

theorem tagPair_ccPair (f : Lab init) (i j : Fin init.card) (h : TagPair init i₀ f i j) :
    CCPair init f i j := h.1

/-- The conditional mean of the tag factor is at most one. -/
theorem tagFactor_condExp_le_one (hc : 2 ≤ init.card) (hC : 1 ≤ C.card) (k u : ℕ) :
    (law init)[tagFactor init C s i₀ k u | shiftedFiltration
      (pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256) s u] ≤ᵐ[law init]
      fun _ => 1 := by
  set ℱ := pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256 with hℱ
  rw [shiftedFiltration_apply]
  unfold tagFactor
  have hP : (0 : ℝ) < (init.card : ℝ) * ((init.card : ℝ) - 1) := by
    have : (2 : ℝ) ≤ init.card := by exact_mod_cast hc
    nlinarith
  have hC1 : (1 : ℝ) ≤ C.card := by exact_mod_cast hC
  set β : ℝ := pairDiscount init C with hβ
  set q : ℝ := tagRate init C with hq
  -- the local-window factor
  have hYeq : (fun ω => affFactor init β (CCPair init) (s + u) ω *
      affFactor init 2 (TagPair init i₀) (s + u) ω) =
      fun ω => 1 + (β - 1) * pairInd init (CCPair init) (s + u) ω +
        β * (2 - 1) * pairInd init (TagPair init i₀) (s + u) ω := by
    funext ω
    exact affFactor_mul_of_imp init _ _ (tagPair_ccPair init i₀) (s + u) ω
  -- the settling-window factor
  have hZeq : (fun ω => Real.exp (-q) * affFactor init 2 (TagPair init i₀) (s + u) ω) =
      fun ω => Real.exp (-q) + Real.exp (-q) * pairInd init (TagPair init i₀) (s + u) ω +
        0 * pairInd init (TagPair init i₀) (s + u) ω := by
    funext ω
    unfold affFactor
    ring
  rw [hYeq, hZeq]
  -- conditional bound of the inner (settling) factor, everywhere
  have hinner : (law init)[windowFactor (settleWindow init C s i₀ k (s + u))
      (fun ω => Real.exp (-q) + Real.exp (-q) * pairInd init (TagPair init i₀) (s + u) ω +
        0 * pairInd init (TagPair init i₀) (s + u) ω) (fun _ => 1) | ℱ (s + u)] ≤ᵐ[law init]
      fun _ => 1 := by
    apply windowFactor_condExp_le_one (settleWindow_measurableSet init C s i₀ (Nat.le_add_right s u))
      (affine_two_integrable init _ _ _ _ _ _) (integrable_const 1) ?_
      (condExp_one_off init _ (s + u))
    filter_upwards [condExp_affine_two init (Real.exp (-q)) (Real.exp (-q)) 0
        (TagPair init i₀) (TagPair init i₀) (s + u),
      pairInd_condExp init hc (TagPair init i₀) (s + u)] with ω h1 h2
    intro hW
    rw [h1, h2]
    obtain ⟨hCt, hi₀, -, -⟩ := hW
    have hcount := goodPairs_tagPair_card_le init i₀ _ hi₀
    rw [hCt] at hcount
    have hfrac : ((goodPairs (TagPair init i₀) (virtualLabels init ω (s + u))).card : ℝ) /
        ((init.card : ℝ) * ((init.card : ℝ) - 1)) ≤ q := by
      rw [hq]
      unfold tagRate
      apply div_le_div_of_nonneg_right _ hP.le
      have h1' : ((goodPairs (TagPair init i₀) (virtualLabels init ω (s + u))).card : ℝ) ≤
          ((2 * (C.card - 1) : ℕ) : ℝ) := by exact_mod_cast hcount
      rw [Nat.cast_mul, Nat.cast_sub hC] at h1'
      push_cast at h1'
      linarith
    have hexp : 1 + q ≤ Real.exp q := by
      have := Real.add_one_le_exp q
      linarith
    have he0 := Real.exp_pos (-q)
    have hprod : Real.exp (-q) * Real.exp q = 1 := by
      rw [← Real.exp_add]
      simp
    have hfrac0 : 0 ≤ ((goodPairs (TagPair init i₀) (virtualLabels init ω (s + u))).card : ℝ) /
        ((init.card : ℝ) * ((init.card : ℝ) - 1)) := by positivity
    nlinarith
  apply windowFactor_condExp_le_one (localWindow_measurableSet init C i₀ (s + u))
    (affine_two_integrable init _ _ _ _ _ _) ?_ ?_ (hinner.mono fun _ h _ => h)
  · apply Integrable.add
    · exact (affine_two_integrable init _ _ _ _ _ _).indicator
        ((ℱ.le (s + u)) _ (settleWindow_measurableSet init C s i₀ (Nat.le_add_right s u)))
    · exact (integrable_const (1 : ℝ)).indicator
        ((ℱ.le (s + u)) _ (settleWindow_measurableSet init C s i₀ (Nat.le_add_right s u)).compl)
  filter_upwards [condExp_affine_two init 1 (β - 1) (β * (2 - 1))
      (CCPair init) (TagPair init i₀) (s + u),
    pairInd_condExp init hc (CCPair init) (s + u),
    pairInd_condExp init hc (TagPair init i₀) (s + u)] with ω h1 h2 h3
  intro hW
  rw [h1, h2, h3]
  obtain ⟨hCt, hi₀, -, -⟩ := hW
  have hcount := goodPairs_tagPair_card_le init i₀ _ hi₀
  rw [hCt] at hcount
  rw [goodPairs_ccPair_card, hCt]
  have htag : ((goodPairs (TagPair init i₀) (virtualLabels init ω (s + u))).card : ℝ) ≤
      2 * ((C.card : ℝ) - 1) := by
    have h1' : ((goodPairs (TagPair init i₀) (virtualLabels init ω (s + u))).card : ℝ) ≤
        ((2 * (C.card - 1) : ℕ) : ℝ) := by exact_mod_cast hcount
    rw [Nat.cast_mul, Nat.cast_sub hC] at h1'
    push_cast at h1'
    linarith
  have hcc : ((C.card * (C.card - 1) : ℕ) : ℝ) = (C.card : ℝ) * ((C.card : ℝ) - 1) := by
    rw [Nat.cast_mul, Nat.cast_sub hC]
    push_cast
    ring
  rw [hcc]
  set a : ℝ := ((goodPairs (TagPair init i₀) (virtualLabels init ω (s + u))).card : ℝ) with ha
  set P : ℝ := (init.card : ℝ) * ((init.card : ℝ) - 1) with hPdef
  have hβpos : 0 < (C.card : ℝ) + 2 := by positivity
  have hβ1 : β - 1 = -2 / ((C.card : ℝ) + 2) := by
    rw [hβ]
    unfold pairDiscount
    field_simp
    ring
  have hident : (β - 1) * ((C.card : ℝ) * ((C.card : ℝ) - 1) / P) + β * (2 - 1) * (a / P) =
      (2 * ((C.card : ℝ) - 1) - a) * (-(C.card : ℝ)) / (((C.card : ℝ) + 2) * P) := by
    rw [hβ1, hβ]
    unfold pairDiscount
    field_simp
    ring
  have hle : (2 * ((C.card : ℝ) - 1) - a) * (-(C.card : ℝ)) / (((C.card : ℝ) + 2) * P) ≤ 0 :=
    div_nonpos_iff.mpr (Or.inr ⟨by nlinarith, by positivity⟩)
  linarith [hident, hle]

/-- The product of the tag factors: `2^{A} β^{B} e^{-q D}` with `A` the tagged
participations on the two windows, `B` the Clock pairs on the local window and `D` the
length of the settling window. -/
theorem prefixProduct_tagFactor (k N : ℕ) (ω : InputLog n) :
    prefixProduct (tagFactor init C s i₀ k) N ω =
      2 ^ windowCount (fun t ω =>
          (ω ∈ localWindow init C i₀ t ∨ ω ∈ settleWindow init C s i₀ k t) ∧
            StepEvent init (TagPair init i₀) t ω) s N ω *
        (pairDiscount init C) ^ windowCount
          (fun t ω => ω ∈ localWindow init C i₀ t ∧ StepEvent init (CCPair init) t ω) s N ω *
        Real.exp (-(tagRate init C)) ^ windowCount
          (fun t ω => ω ∈ settleWindow init C s i₀ k t) s N ω := by
  classical
  induction N with
  | zero =>
      simp only [prefixProduct_zero, windowCount_zero, pow_zero, mul_one]
  | succ N ih =>
      rw [prefixProduct_succ, ih,
        windowCount_succ (fun t ω =>
          (ω ∈ localWindow init C i₀ t ∨ ω ∈ settleWindow init C s i₀ k t) ∧
            StepEvent init (TagPair init i₀) t ω) s N ω,
        windowCount_succ (fun t ω => ω ∈ localWindow init C i₀ t ∧
          StepEvent init (CCPair init) t ω) s N ω,
        windowCount_succ (fun t ω => ω ∈ settleWindow init C s i₀ k t) s N ω]
      unfold tagFactor
      by_cases h1 : ω ∈ localWindow init C i₀ (s + N)
      · have h2 : ω ∉ settleWindow init C s i₀ k (s + N) :=
          fun h2 => localWindow_settleWindow_disjoint init C s i₀ k (s + N) ω h1 h2
        rw [windowFactor_of_mem h1, affFactor_eq_ite, affFactor_eq_ite]
        by_cases hcc : StepEvent init (CCPair init) (s + N) ω <;>
          by_cases htag : StepEvent init (TagPair init i₀) (s + N) ω <;>
          simp [h1, h2, hcc, htag, pow_succ] <;> ring
      · rw [windowFactor_of_not_mem h1]
        by_cases h2 : ω ∈ settleWindow init C s i₀ k (s + N)
        · rw [windowFactor_of_mem h2, affFactor_eq_ite]
          by_cases htag : StepEvent init (TagPair init i₀) (s + N) ω <;>
            simp [h1, h2, htag, pow_succ] <;> ring
        · rw [windowFactor_of_not_mem h2]
          simp [h1, h2]

/-- The P14 bad event for the tagged Clock `i₀` on the horizon `N`: at least `B` tagged
participations on the two windows, at most `R₁` Clock pairs on the local window and a
settling window of length at most `D`. -/
def tagBad (k N B R₁ D : ℕ) : Set (InputLog n) :=
  {ω | B ≤ windowCount (fun t ω =>
      (ω ∈ localWindow init C i₀ t ∨ ω ∈ settleWindow init C s i₀ k t) ∧
        StepEvent init (TagPair init i₀) t ω) s N ω ∧
    windowCount
      (fun t ω => ω ∈ localWindow init C i₀ t ∧ StepEvent init (CCPair init) t ω) s N ω ≤ R₁ ∧
    windowCount (fun t ω => ω ∈ settleWindow init C s i₀ k t) s N ω ≤ D}

/-- The algebra of the Markov bound. -/
theorem tag_rate_identity (B R₁ D : ℕ) (c q : ℝ) (hc : 0 < c) :
    1 / (2 ^ B * (c / (c + 2)) ^ R₁ * Real.exp (-q) ^ D) =
      (1 / 2) ^ B * (c + 2) ^ R₁ / c ^ R₁ * Real.exp (q * D) := by
  have hexpD : Real.exp (-q) ^ D = (Real.exp (q * D))⁻¹ := by
    rw [← Real.exp_nat_mul, ← Real.exp_neg]
    congr 1
    ring
  rw [hexpD, div_pow, one_div_pow]
  have h0 : (2 : ℝ) ^ B ≠ 0 := by positivity
  have h1 : (c + 2) ^ R₁ ≠ 0 := by positivity
  have h2 : c ^ R₁ ≠ 0 := by positivity
  have h3 : Real.exp (q * D) ≠ 0 := (Real.exp_pos _).ne'
  field_simp

/-- PHASE3 (62)–(63) for one tagged Clock: the relative probability of the bad event is at
most `2^{-B} (1 + 2/C)^{R₁} e^{q D}`. -/
theorem tag_budget_tail (hc : 2 ≤ init.card) (hC : 1 ≤ C.card) (k N B R₁ D : ℕ)
    (E : Set (InputLog n))
    (hE : MeasurableSet[pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256 s] E) :
    law init (E ∩ tagBad init C s i₀ k N B R₁ D) ≤
      ENNReal.ofReal ((1 / 2) ^ B * ((C.card : ℝ) + 2) ^ R₁ / (C.card : ℝ) ^ R₁ *
        Real.exp (tagRate init C * D)) * law init E := by
  set ℱ := shiftedFiltration (pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256) s
    with hℱ
  have hE' : MeasurableSet[ℱ 0] E := by
    simpa only [hℱ, shiftedFiltration_apply, Nat.add_zero] using hE
  have hβpos : 0 < pairDiscount init C := by
    unfold pairDiscount
    have : (1 : ℝ) ≤ C.card := by exact_mod_cast hC
    positivity
  have hr : (0 : ℝ) < 2 ^ B * (pairDiscount init C) ^ R₁ * Real.exp (-(tagRate init C)) ^ D := by
    positivity
  have htail := prefix_product_tail_ennreal (μ := law init) (ℱ := ℱ)
    (tagFactor_stronglyMeasurable init C s i₀ k) (tagFactor_nonneg init C s i₀ hc k)
    (tagFactor_le init C s i₀ hc hC k) (tagFactor_condExp_le_one init C s i₀ hc hC k) E hE' N
    (tagBad init C s i₀ k N B R₁ D) hr ?_
  · refine htail.trans (mul_le_mul_right' (ENNReal.ofReal_le_ofReal (le_of_eq ?_)) _)
    have hCpos : (0 : ℝ) < C.card := by
      have : (1 : ℝ) ≤ C.card := by exact_mod_cast hC
      linarith
    unfold pairDiscount
    exact tag_rate_identity B R₁ D (C.card : ℝ) (tagRate init C) hCpos
  · rintro ω ⟨-, hB, hR, hD⟩
    rw [prefixProduct_tagFactor]
    have he1 : Real.exp (-(tagRate init C)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      linarith [tagRate_nonneg init C hc hC]
    apply mul_le_mul (mul_le_mul (pow_le_pow_right₀ (by norm_num) hB)
      (pow_le_pow_of_le_one hβpos.le (pairDiscount_le_one init C) hR) (by positivity) (by positivity))
      (pow_le_pow_of_le_one (Real.exp_nonneg _) he1 hD) (by positivity) (by positivity)

end Tag

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockContactMGF

end
