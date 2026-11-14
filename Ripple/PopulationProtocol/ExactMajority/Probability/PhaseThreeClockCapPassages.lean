import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockCapSpread

/-!
# The two top-level passages of P14 (N12, step 4)

PHASE3 P14 charges, on the local cap event, two passages of the top level `Q`:

* from 10 % capped to 90 % capped (P8's `8 C` ticks): here in the form "at most
  `13 C` Clock pairs are drawn while `10 % ≤ X_Q < 90 %`", proved with the compensated
  product `(100/91)^{[Clock pair]} (1/2)^{[raising tick]}`: while `C/10 ≤ X_Q ≤ 9C/10`
  at least `18 %` of the ordered Clock pairs raise `X_Q` (PHASE3 (25)), so the factor has
  conditional mean at most one, and `X_Q` rises at most `C` times (`bulk_high_tail`,
  error `e^{-0.47 C}`);
* from 90 % capped to all capped (the `n^{-6}` row): a tagged uncapped Clock meets a
  capped Clock with probability at least `2 h / (n (n - 1))` per raw step while
  `X_Q ≥ h`, so it is still uncapped after `k` such steps with probability at most
  `e^{-p k}` (`high_all_tail`, factor `(1 - p)^{-1} [no hit]`).

Both are prefix-weighted bounds relative to an initial event `E` measurable at the seed
`s` on which the Clock label set is a fixed `C`; the bad events carry the asynchronous
entry so that the deterministic structure (monotone top count, persistent cap) is
available on them. The raw-time compensation by the observed Clock-pair count replaces
the tick/raw thinning of P14.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators MeasureTheory ProbabilityTheory

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockCapPassages

open TimeTheorem PairLog PairLogAuxiliary PhaseThreeClockVirtual
  PhaseThreeClockGatedLaw PhaseThreeClockGatedLevelOne PhaseThreeClockEmbedding
  PhaseThreeClockEmbeddingBridge PhaseThreeClockCore PhaseThreeClockRows
  PhaseThreeClockProductTails PhaseThreeScalar PhaseThreeClockPrefixTails
  PhaseThreeClockProbabilityFloors PhaseThreeClockCapSpread
open StageEventSpec hiding frontCount clockCount
open Classical

variable {n : ℕ} (init : InputCfg n)

/-! ## Step events and window counts -/

/-- The pair drawn at `t + 1` satisfies `A` at the virtual labelling of time `t`. -/
def StepEvent (A : Lab init → Fin init.card → Fin init.card → Prop) (t : ℕ) (ω : InputLog n) :
    Prop :=
  ∃ i j, drawLabels init ω (t + 1) = some (i, j) ∧ A (virtualLabels init ω t) i j

theorem pairInd_eq_ite (A : Lab init → Fin init.card → Fin init.card → Prop) (t : ℕ)
    (ω : InputLog n) :
    pairInd init A t ω = if StepEvent init A t ω then 1 else 0 := by
  unfold pairInd StepEvent
  congr 1

/-- The number of offsets `u < N` at which `P (s + u)` holds. -/
def windowCount (P : ℕ → InputLog n → Prop) (s N : ℕ) (ω : InputLog n) : ℕ :=
  ∑ u ∈ Finset.range N, if P (s + u) ω then 1 else 0

theorem windowCount_zero (P : ℕ → InputLog n → Prop) (s : ℕ) (ω : InputLog n) :
    windowCount P s 0 ω = 0 := by
  simp [windowCount]

theorem windowCount_succ (P : ℕ → InputLog n → Prop) (s N : ℕ) (ω : InputLog n) :
    windowCount P s (N + 1) ω =
      windowCount P s N ω + if P (s + N) ω then 1 else 0 := by
  unfold windowCount
  rw [Finset.sum_range_succ]

theorem windowCount_mono {P R : ℕ → InputLog n → Prop} (h : ∀ t ω, P t ω → R t ω)
    (s N : ℕ) (ω : InputLog n) :
    windowCount P s N ω ≤ windowCount R s N ω := by
  classical
  unfold windowCount
  apply Finset.sum_le_sum
  intro u _
  split_ifs with hP hR hR
  · exact le_rfl
  · exact absurd (h _ _ hP) hR
  · exact Nat.zero_le _
  · exact le_rfl

theorem windowCount_le (P : ℕ → InputLog n → Prop) (s N : ℕ) (ω : InputLog n) :
    windowCount P s N ω ≤ N := by
  classical
  unfold windowCount
  calc (∑ u ∈ Finset.range N, if P (s + u) ω then 1 else 0) ≤
        ∑ _u ∈ Finset.range N, 1 := by
        apply Finset.sum_le_sum
        intro u _
        split_ifs <;> omega
    _ = N := by simp

/-- Every offset in `[a, b)` (relative to `s`, inside the horizon) satisfying `P` is
counted. -/
theorem le_windowCount_of_forall (P : ℕ → InputLog n → Prop) (s N : ℕ) (ω : InputLog n)
    {a k : ℕ} (hsa : s ≤ a) (hN : a + k ≤ s + N)
    (hP : ∀ t, a ≤ t → t < a + k → P t ω) :
    k ≤ windowCount P s N ω := by
  classical
  unfold windowCount
  have hsub : Finset.Ico (a - s) (a - s + k) ⊆ Finset.range N := by
    intro u hu
    rw [Finset.mem_Ico] at hu
    rw [Finset.mem_range]
    omega
  calc k = ∑ u ∈ Finset.Ico (a - s) (a - s + k), (1 : ℕ) := by simp
    _ = ∑ u ∈ Finset.Ico (a - s) (a - s + k), if P (s + u) ω then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro u hu
        rw [Finset.mem_Ico] at hu
        rw [if_pos (hP (s + u) (by omega) (by omega))]
    _ ≤ ∑ u ∈ Finset.range N, if P (s + u) ω then 1 else 0 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)

/-- A window count of offsets in `[a, b)` is the count over `[a, b)`. -/
theorem windowCount_interval (P : ℕ → InputLog n → Prop) (s N : ℕ) (ω : InputLog n)
    {a b : ℕ} (hsa : s ≤ a) (hab : a ≤ b) (hbN : b ≤ s + N) :
    windowCount (fun t ω => a ≤ t ∧ t < b ∧ P t ω) s N ω =
      ∑ t ∈ Finset.Ico a b, if P t ω then 1 else 0 := by
  classical
  unfold windowCount
  dsimp only
  have hsub : Finset.Ico (a - s) (b - s) ⊆ Finset.range N := by
    intro u hu
    rw [Finset.mem_Ico] at hu
    rw [Finset.mem_range]
    omega
  rw [← Finset.sum_subset hsub (fun u _ hu => by
    rw [Finset.mem_Ico] at hu
    rw [if_neg]
    intro h
    exact hu ⟨by omega, by omega⟩)]
  rw [Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range,
    show b - s - (a - s) = b - a by omega]
  apply Finset.sum_congr rfl
  intro u hu
  rw [Finset.mem_range] at hu
  have hidx : s + (a - s + u) = a + u := by omega
  rw [hidx]
  by_cases hP : P (a + u) ω
  · rw [if_pos ⟨by omega, by omega, hP⟩, if_pos hP]
  · rw [if_neg (fun h => hP h.2.2), if_neg hP]

/-! ## Affine step factors -/

/-- The factor `a` when the step event `A` occurs and `1` otherwise, written as an affine
function of the step indicator. -/
def affFactor (a : ℝ) (A : Lab init → Fin init.card → Fin init.card → Prop) (t : ℕ)
    (ω : InputLog n) : ℝ :=
  1 + (a - 1) * pairInd init A t ω

theorem affFactor_eq_ite (a : ℝ) (A : Lab init → Fin init.card → Fin init.card → Prop)
    (t : ℕ) (ω : InputLog n) :
    affFactor init a A t ω = if StepEvent init A t ω then a else 1 := by
  unfold affFactor
  rw [pairInd_eq_ite]
  split_ifs <;> ring

theorem affFactor_nonneg {a : ℝ} (ha : 0 ≤ a) (A : Lab init → Fin init.card → Fin init.card → Prop)
    (t : ℕ) (ω : InputLog n) : 0 ≤ affFactor init a A t ω := by
  rw [affFactor_eq_ite]
  split_ifs <;> linarith

theorem affFactor_le {a b : ℝ} (hab : a ≤ b) (h1 : 1 ≤ b)
    (A : Lab init → Fin init.card → Fin init.card → Prop) (t : ℕ) (ω : InputLog n) :
    affFactor init a A t ω ≤ b := by
  rw [affFactor_eq_ite]
  split_ifs <;> linarith

theorem affFactor_stronglyMeasurable (a : ℝ)
    (A : Lab init → Fin init.card → Fin init.card → Prop) (t : ℕ) :
    StronglyMeasurable[pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256 (t + 1)]
      (affFactor init a A t) :=
  stronglyMeasurable_const.add ((pairInd_stronglyMeasurable init A t).const_mul (a - 1))

theorem affFactor_integrable (a : ℝ)
    (A : Lab init → Fin init.card → Fin init.card → Prop) (t : ℕ) :
    Integrable (affFactor init a A t) (law init) :=
  (integrable_const (1 : ℝ)).add ((pairInd_integrable init A t).const_mul (a - 1))

/-- The product of two affine factors with nested step events is affine. -/
theorem affFactor_mul_of_imp (a b : ℝ)
    {A B : Lab init → Fin init.card → Fin init.card → Prop}
    (h : ∀ f i j, B f i j → A f i j) (t : ℕ) (ω : InputLog n) :
    affFactor init a A t ω * affFactor init b B t ω =
      1 + (a - 1) * pairInd init A t ω + a * (b - 1) * pairInd init B t ω := by
  rw [affFactor_eq_ite, affFactor_eq_ite, pairInd_eq_ite, pairInd_eq_ite]
  by_cases hB : StepEvent init B t ω
  · have hA : StepEvent init A t ω := by
      obtain ⟨i, j, hd, hij⟩ := hB
      exact ⟨i, j, hd, h _ i j hij⟩
    rw [if_pos hA, if_pos hB, if_pos hA, if_pos hB]
    ring
  · rw [if_neg hB, if_neg hB]
    split_ifs <;> ring

/-- The conditional expectation of an affine combination of two step indicators. -/
theorem condExp_affine_two (c₀ c₁ c₂ : ℝ)
    (A B : Lab init → Fin init.card → Fin init.card → Prop) (t : ℕ) :
    (law init)[fun ω => c₀ + c₁ * pairInd init A t ω + c₂ * pairInd init B t ω |
        pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256 t] =ᵐ[law init]
      fun ω => c₀ + c₁ * ((law init)[pairInd init A t |
          pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256 t]) ω +
        c₂ * ((law init)[pairInd init B t |
          pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256 t]) ω := by
  set ℱ := pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256 with hℱ
  have hA := pairInd_integrable init A t
  have hB := pairInd_integrable init B t
  have hfun : (fun ω => c₀ + c₁ * pairInd init A t ω + c₂ * pairInd init B t ω) =
      ((fun _ => c₀) + c₁ • pairInd init A t) + c₂ • pairInd init B t := by
    funext ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hfun]
  filter_upwards [condExp_add ((integrable_const c₀).add (hA.smul c₁)) (hB.smul c₂) (ℱ t),
    condExp_add (integrable_const c₀) (hA.smul c₁) (ℱ t),
    condExp_smul (m := ℱ t) (μ := law init) c₁ (pairInd init A t),
    condExp_smul (m := ℱ t) (μ := law init) c₂ (pairInd init B t)] with ω h1 h2 h3 h4
  rw [h1]
  simp only [Pi.add_apply]
  rw [h2]
  simp only [Pi.add_apply]
  rw [h3, h4, condExp_const (ℱ.le t) c₀]
  simp only [Pi.smul_apply, smul_eq_mul]

theorem affine_two_integrable (c₀ c₁ c₂ : ℝ)
    (A B : Lab init → Fin init.card → Fin init.card → Prop) (t : ℕ) :
    Integrable (fun ω => c₀ + c₁ * pairInd init A t ω + c₂ * pairInd init B t ω) (law init) := by
  have h := ((integrable_const c₀).add ((pairInd_integrable init A t).const_mul c₁)).add
    ((pairInd_integrable init B t).const_mul c₂)
  exact h

/-! ## Product identities for window factors -/

/-- The product of window factors `a^{[A]} b^{[B]}` on the window `W`, as a function of
the window counts. -/
theorem prefixProduct_window_two (a b : ℝ) (W : ℕ → Set (InputLog n))
    (A B : Lab init → Fin init.card → Fin init.card → Prop) (s N : ℕ) (ω : InputLog n) :
    prefixProduct (fun u => windowFactor (W (s + u))
        (fun ω => affFactor init a A (s + u) ω * affFactor init b B (s + u) ω)
        (fun _ => 1)) N ω =
      a ^ windowCount (fun t ω => ω ∈ W t ∧ StepEvent init A t ω) s N ω *
        b ^ windowCount (fun t ω => ω ∈ W t ∧ StepEvent init B t ω) s N ω := by
  classical
  induction N with
  | zero =>
      simp [prefixProduct_zero, windowCount_zero]
  | succ N ih =>
      rw [prefixProduct_succ, ih,
        windowCount_succ (fun t ω => ω ∈ W t ∧ StepEvent init A t ω) s N ω,
        windowCount_succ (fun t ω => ω ∈ W t ∧ StepEvent init B t ω) s N ω]
      by_cases hW : ω ∈ W (s + N)
      · rw [windowFactor_of_mem hW, affFactor_eq_ite, affFactor_eq_ite]
        by_cases hA : StepEvent init A (s + N) ω <;> by_cases hB : StepEvent init B (s + N) ω <;>
          simp [hA, hB, hW, pow_succ] <;> ring
      · rw [windowFactor_of_not_mem hW]
        simp [hW]

/-- The product of window factors `c · a^{[A]}` on the window `W`. -/
theorem prefixProduct_window_const (c a : ℝ) (W : ℕ → Set (InputLog n))
    (A : Lab init → Fin init.card → Fin init.card → Prop) (s N : ℕ) (ω : InputLog n) :
    prefixProduct (fun u => windowFactor (W (s + u))
        (fun ω => c * affFactor init a A (s + u) ω) (fun _ => 1)) N ω =
      c ^ windowCount (fun t ω => ω ∈ W t) s N ω *
        a ^ windowCount (fun t ω => ω ∈ W t ∧ StepEvent init A t ω) s N ω := by
  classical
  induction N with
  | zero =>
      simp [prefixProduct_zero, windowCount_zero]
  | succ N ih =>
      rw [prefixProduct_succ, ih, windowCount_succ (fun t ω => ω ∈ W t) s N ω,
        windowCount_succ (fun t ω => ω ∈ W t ∧ StepEvent init A t ω) s N ω]
      by_cases hW : ω ∈ W (s + N)
      · rw [windowFactor_of_mem hW, affFactor_eq_ite]
        by_cases hA : StepEvent init A (s + N) ω <;> simp [hA, hW, pow_succ] <;> ring
      · rw [windowFactor_of_not_mem hW]
        simp [hW]

theorem windowFactor_two_stronglyMeasurable (a b : ℝ) (W : ℕ → Set (InputLog n))
    (A B : Lab init → Fin init.card → Fin init.card → Prop) (t : ℕ)
    (hW : MeasurableSet[pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256 t] (W t)) :
    StronglyMeasurable[pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256 (t + 1)]
      (windowFactor (W t) (fun ω => affFactor init a A t ω * affFactor init b B t ω)
        (fun _ => 1)) :=
  windowFactor_stronglyMeasurable
    ((pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256).mono (Nat.le_succ t) _ hW)
    ((affFactor_stronglyMeasurable init a A t).mul (affFactor_stronglyMeasurable init b B t))
    stronglyMeasurable_const

theorem windowFactor_const_stronglyMeasurable (c a : ℝ) (W : ℕ → Set (InputLog n))
    (A : Lab init → Fin init.card → Fin init.card → Prop) (t : ℕ)
    (hW : MeasurableSet[pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256 t] (W t)) :
    StronglyMeasurable[pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256 (t + 1)]
      (windowFactor (W t) (fun ω => c * affFactor init a A t ω) (fun _ => 1)) :=
  windowFactor_stronglyMeasurable
    ((pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256).mono (Nat.le_succ t) _ hW)
    ((affFactor_stronglyMeasurable init a A t).const_mul c)
    stronglyMeasurable_const

/-- The off-window value one has conditional mean one. -/
theorem condExp_one_off (A : Set (InputLog n)) (t : ℕ) :
    ∀ᵐ ω ∂law init, ω ∉ A →
      ((law init)[(fun _ : InputLog n => (1 : ℝ)) |
        pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256 t]) ω ≤ 1 :=
  (condExp_one_le (μ := law init)
    (ℱ := pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256) t).mono fun _ h _ => h

/-! ## The raise count: at most `C` raises after the seed -/

variable (ω : InputLog n)

theorem windowCount_raise_add {S T : ℕ} (hentry : AsyncEntry init ω S T) (N : ℕ) :
    (windowCount (StepEvent init (GatedTick (clockTop n))) S N ω : ℝ) +
      topCount init ω S = topCount init ω (S + N) := by
  classical
  induction N with
  | zero => simp [windowCount_zero]
  | succ N ih =>
      rw [windowCount_succ (StepEvent init (GatedTick (clockTop n))) S N ω, Nat.cast_add,
        Nat.cast_ite, Nat.cast_one (R := ℝ), Nat.cast_zero (R := ℝ),
        show S + (N + 1) = S + N + 1 by omega, topCount_succ init ω hentry (S + N) (by omega),
        ← ih, pairInd_eq_ite]
      ring

theorem windowCount_raise_le {S T : ℕ} (hentry : AsyncEntry init ω S T) (N : ℕ) :
    windowCount (StepEvent init (GatedTick (clockTop n))) S N ω ≤
      clockCount (virtualLabels init ω S) := by
  have h := windowCount_raise_add init ω hentry N
  have h2 := topCount_le_clockCount init ω (S + N)
  rw [clockCount_virtual_eq_seed init ω hentry (S + N) (by omega)] at h2
  have h3 : (windowCount (StepEvent init (GatedTick (clockTop n))) S N ω : ℝ) ≤
      clockCount (virtualLabels init ω S) := by
    have h2' : (topCount init ω (S + N) : ℝ) ≤ clockCount (virtualLabels init ω S) := by
      exact_mod_cast h2
    linarith [show (0 : ℝ) ≤ topCount init ω S from Nat.cast_nonneg _]
  exact_mod_cast h3

/-- Before the seed no Clock is at a positive effective minute. -/
theorem topCount_eq_zero_before_seed {S T : ℕ} (hentry : AsyncEntry init ω S T) (v : ℕ)
    (hvS : v < S) : topCount init ω v = 0 := by
  unfold topCount frontCount aboveSet
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro i _
  rintro ⟨-, hm⟩
  have heq := virtualLabels_eq_labelsAt_through_asyncEntry init ω S T hentry v
    (by have := hentry.order; omega)
  have hlow := hentry.first_phase_seed.2 v hvS _ (labelsAt_mem_trace init ω v i)
  rw [heq] at hm
  unfold effMinute at hm
  rw [if_neg (by omega)] at hm
  have := one_le_clockTop (n := n)
  omega

/-! ## P1: from 10 % to 90 % capped within `13 C` Clock pairs -/

section BulkHigh

variable (C : Finset (Fin init.card)) (s : ℕ)

/-- The window: the top level between the bulk and the high thresholds, with the Clock
count fixed. -/
def bulkHighWindow (t : ℕ) : Set (InputLog n) :=
  {ω | clockCount (virtualLabels init ω t) = C.card ∧
    ReachedTop init (bulkThreshold C.card) t ω ∧ ¬ ReachedTop init (highThreshold C.card) t ω}

theorem bulkHighWindow_measurableSet (t : ℕ) :
    MeasurableSet[pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256 t]
      (bulkHighWindow init C t) :=
  measurableSet_virtual_single init le_rfl (fun f =>
    clockCount f = C.card ∧ bulkThreshold C.card ≤ frontCount f (clockTop n) ∧
      ¬ highThreshold C.card ≤ frontCount f (clockTop n))

/-- The P1 factor: `100/91` on a Clock pair, `1/2` on a raising tick, on the window. -/
def bulkHighFactor (u : ℕ) : InputLog n → ℝ :=
  windowFactor (bulkHighWindow init C (s + u))
    (fun ω => affFactor init (100 / 91) (CCPair init) (s + u) ω *
      affFactor init (1 / 2) (GatedTick (clockTop n)) (s + u) ω)
    (fun _ => 1)

theorem bulkHighFactor_nonneg (u : ℕ) (ω : InputLog n) : 0 ≤ bulkHighFactor init C s u ω :=
  windowFactor_nonneg
    (fun ω => mul_nonneg (affFactor_nonneg init (by norm_num) _ _ ω)
      (affFactor_nonneg init (by norm_num) _ _ ω))
    (fun _ => zero_le_one) ω

theorem bulkHighFactor_le (u : ℕ) (ω : InputLog n) : bulkHighFactor init C s u ω ≤ 2 :=
  windowFactor_le
    (fun ω => by
      have h1 := affFactor_le init (a := (100 / 91 : ℝ)) (b := 2) (by norm_num) (by norm_num)
        (CCPair init) (s + u) ω
      have h2 := affFactor_le init (a := (1 / 2 : ℝ)) (b := 1) (by norm_num) le_rfl
        (GatedTick (clockTop n)) (s + u) ω
      have h3 := affFactor_nonneg init (by norm_num : (0 : ℝ) ≤ 100 / 91) (CCPair init) (s + u) ω
      nlinarith)
    (fun _ => by norm_num) ω

theorem bulkHighFactor_stronglyMeasurable (u : ℕ) :
    StronglyMeasurable[shiftedFiltration
      (pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256) s (u + 1)]
      (bulkHighFactor init C s u) := by
  rw [shiftedFiltration_apply, ← Nat.add_assoc]
  exact windowFactor_two_stronglyMeasurable init _ _ (bulkHighWindow init C) _ _ (s + u)
    (bulkHighWindow_measurableSet init C (s + u))

/-- PHASE3 (25) on the window: at least `18 %` of the ordered Clock pairs raise the top
level, hence `9 · #CC ≤ 50 · #raise`. -/
theorem raise_count_floor (f : Lab init) (hC : clockCount f = C.card)
    (hlo : bulkThreshold C.card ≤ frontCount f (clockTop n))
    (hhi : ¬ highThreshold C.card ≤ frontCount f (clockTop n)) :
    9 * ((goodPairs (CCPair init) f).card : ℝ) ≤
      50 * ((goodPairs (GatedTick (clockTop n)) f).card : ℝ) := by
  rw [goodPairs_ccPair_card, goodPairs_gatedTick_top_card, hC]
  set X := frontCount f (clockTop n) with hX
  have hXC : X ≤ C.card := hC ▸ frontCount_le_clockCount f _
  have hlo' : (C.card : ℝ) / 10 ≤ X := by
    have := Nat.le_ceil ((C.card : ℝ) / 10)
    have hb : (bulkThreshold C.card : ℝ) ≤ X := by exact_mod_cast hlo
    unfold bulkThreshold at hb
    linarith
  have hhi' : (X : ℝ) < 9 * (C.card : ℝ) / 10 := by
    have hlt : X < highThreshold C.card := Nat.lt_of_not_le hhi
    have h1 : (X : ℝ) + 1 ≤ (highThreshold C.card : ℝ) := by exact_mod_cast hlt
    have h2 := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 9 * (C.card : ℝ) / 10 by positivity)
    unfold highThreshold at h1
    linarith
  have hY : (0 : ℝ) ≤ ((exactCount f (clockTop n - 1) *
      (exactCount f (clockTop n - 1) - 1) : ℕ) : ℝ) := Nat.cast_nonneg _
  have hsub : ((2 * X * (C.card - X) + exactCount f (clockTop n - 1) *
      (exactCount f (clockTop n - 1) - 1) : ℕ) : ℝ) =
      2 * (X : ℝ) * ((C.card : ℝ) - X) +
        ((exactCount f (clockTop n - 1) * (exactCount f (clockTop n - 1) - 1) : ℕ) : ℝ) := by
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hXC]
    push_cast
    ring
  have hcc : ((C.card * (C.card - 1) : ℕ) : ℝ) ≤ (C.card : ℝ) * (C.card : ℝ) := by
    rcases Nat.eq_zero_or_pos C.card with h0 | hpos
    · rw [h0]; simp
    · rw [Nat.cast_mul, Nat.cast_sub hpos]
      push_cast
      nlinarith [show (0 : ℝ) ≤ C.card from Nat.cast_nonneg _]
  rw [hsub]
  have hkey : 9 * ((C.card : ℝ) * C.card) ≤ 100 * ((X : ℝ) * ((C.card : ℝ) - X)) := by
    nlinarith
  nlinarith

/-- The conditional mean of the P1 factor is at most one. -/
theorem bulkHighFactor_condExp_le_one (hc : 2 ≤ init.card) (u : ℕ) :
    (law init)[bulkHighFactor init C s u | shiftedFiltration
      (pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256) s u] ≤ᵐ[law init]
      fun _ => 1 := by
  set ℱ := pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256 with hℱ
  rw [shiftedFiltration_apply]
  unfold bulkHighFactor
  have hYeq : (fun ω => affFactor init (100 / 91) (CCPair init) (s + u) ω *
      affFactor init (1 / 2) (GatedTick (clockTop n)) (s + u) ω) =
      fun ω => 1 + (100 / 91 - 1) * pairInd init (CCPair init) (s + u) ω +
        (100 / 91) * (1 / 2 - 1) * pairInd init (GatedTick (clockTop n)) (s + u) ω := by
    funext ω
    exact affFactor_mul_of_imp init _ _ (gatedTick_ccPair init) (s + u) ω
  rw [hYeq]
  apply windowFactor_condExp_le_one (bulkHighWindow_measurableSet init C (s + u))
    (affine_two_integrable init _ _ _ _ _ _) (integrable_const 1) ?_
    (condExp_one_off init _ (s + u))
  filter_upwards [condExp_affine_two init 1 (100 / 91 - 1) ((100 / 91) * (1 / 2 - 1))
      (CCPair init) (GatedTick (clockTop n)) (s + u),
    pairInd_condExp init hc (CCPair init) (s + u),
    pairInd_condExp init hc (GatedTick (clockTop n)) (s + u)] with ω h1 h2 h3
  intro hW
  rw [h1, h2, h3]
  obtain ⟨hC, hlo, hhi⟩ := hW
  have hfloor := raise_count_floor init C _ hC hlo hhi
  have hP : (0 : ℝ) < (init.card : ℝ) * ((init.card : ℝ) - 1) := by
    have : (2 : ℝ) ≤ init.card := by exact_mod_cast hc
    nlinarith
  set a : ℝ := ((goodPairs (CCPair init) (virtualLabels init ω (s + u))).card : ℝ) with ha
  set b : ℝ := ((goodPairs (GatedTick (clockTop n)) (virtualLabels init ω (s + u))).card : ℝ)
    with hb
  set P : ℝ := (init.card : ℝ) * ((init.card : ℝ) - 1) with hPdef
  have hident : (100 / 91 - 1 : ℝ) * (a / P) + (100 / 91) * (1 / 2 - 1) * (b / P) =
      (9 * a - 50 * b) / (91 * P) := by
    field_simp
    ring
  have hle : (9 * a - 50 * b) / (91 * P) ≤ 0 :=
    div_nonpos_iff.mpr (Or.inr ⟨by linarith, by positivity⟩)
  linarith

/-- The P1 bad event on the horizon `N`: an entry at `s`, the Clock set `C` at the seed, and
at least `13 C` Clock pairs drawn while the top level is between the bulk and the high
thresholds. -/
def bulkHighBad (N : ℕ) : Set (InputLog n) :=
  {ω | (∃ T, AsyncEntry init ω s T) ∧ clockCount (virtualLabels init ω s) = C.card ∧
    13 * C.card ≤ windowCount
      (fun t ω => ω ∈ bulkHighWindow init C t ∧ StepEvent init (CCPair init) t ω) s N ω}

theorem log_hundred_div_ninetyone : (9 / 100 : ℝ) ≤ Real.log (100 / 91) := by
  have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 91 / 100 by norm_num)
  have hinv : Real.log ((91 / 100 : ℝ)⁻¹) = - Real.log (91 / 100) := Real.log_inv _
  rw [show ((91 / 100 : ℝ)⁻¹) = 100 / 91 by norm_num] at hinv
  rw [hinv]
  linarith

/-- The P1 tail: on an initial event measurable at the seed, the bad event has relative
probability at most `e^{-0.47 C}`. -/
theorem bulk_high_tail (hc : 2 ≤ init.card) (N : ℕ) (E : Set (InputLog n))
    (hE : MeasurableSet[pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256 s] E) :
    law init (E ∩ bulkHighBad init C s N) ≤
      ENNReal.ofReal (Real.exp (-(47 / 100) * C.card)) * law init E := by
  set ℱ := shiftedFiltration (pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256) s
    with hℱ
  have hE' : MeasurableSet[ℱ 0] E := by
    simpa only [hℱ, shiftedFiltration_apply, Nat.add_zero] using hE
  have hr : (0 : ℝ) < (100 / 91) ^ (13 * C.card) * (1 / 2) ^ C.card := by positivity
  have htail := prefix_product_tail_ennreal (μ := law init) (ℱ := ℱ)
    (bulkHighFactor_stronglyMeasurable init C s) (bulkHighFactor_nonneg init C s)
    (bulkHighFactor_le init C s) (bulkHighFactor_condExp_le_one init C s hc) E hE' N
    (bulkHighBad init C s N) hr ?_
  · refine htail.trans (mul_le_mul_right' (ENNReal.ofReal_le_ofReal ?_) _)
    have hlog := log_hundred_div_ninetyone
    have hlog2 := PhaseThreeModel.Numeric.log_two_bounds.2
    have hpow1 : ((100 / 91 : ℝ)) ^ (13 * C.card) =
        Real.exp ((13 * C.card : ℕ) * Real.log (100 / 91)) := by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
    have hpow2 : ((1 / 2 : ℝ)) ^ C.card = Real.exp ((C.card : ℕ) * Real.log (1 / 2)) := by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
    have hl12 : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
      rw [Real.log_div (by norm_num) (by norm_num), Real.log_one]
      ring
    rw [hpow1, hpow2, ← Real.exp_add, one_div, ← Real.exp_neg, Real.exp_le_exp, hl12]
    push_cast
    nlinarith [show (0 : ℝ) ≤ C.card from Nat.cast_nonneg _]
  · rintro ω ⟨-, ⟨T, hentry⟩, hCs, hcount⟩
    have hprod := prefixProduct_window_two init (100 / 91) (1 / 2) (bulkHighWindow init C)
      (CCPair init) (GatedTick (clockTop n)) s N ω
    have hb : windowCount
        (fun t ω => ω ∈ bulkHighWindow init C t ∧ StepEvent init (GatedTick (clockTop n)) t ω)
          s N ω ≤ C.card := by
      refine (windowCount_mono (fun t ω h => h.2) s N ω).trans ?_
      rw [← hCs]
      exact windowCount_raise_le init ω hentry N
    calc (100 / 91 : ℝ) ^ (13 * C.card) * (1 / 2) ^ C.card
        ≤ (100 / 91 : ℝ) ^ windowCount
            (fun t ω => ω ∈ bulkHighWindow init C t ∧ StepEvent init (CCPair init) t ω) s N ω *
          (1 / 2) ^ windowCount
            (fun t ω => ω ∈ bulkHighWindow init C t ∧
              StepEvent init (GatedTick (clockTop n)) t ω) s N ω :=
          mul_le_mul (pow_le_pow_right₀ (by norm_num) hcount)
            (pow_le_pow_of_le_one (by norm_num) (by norm_num) hb) (by positivity) (by positivity)
      _ = prefixProduct (bulkHighFactor init C s) N ω := hprod.symm

end BulkHigh

/-! ## P2: from a threshold to all capped, one Clock at a time -/

section HighAll

variable (C : Finset (Fin init.card)) (b s₀ s k : ℕ) (j : Fin init.card)

/-- The hit rate: `2 b / (n (n - 1))` with `b` the threshold of capped Clocks. -/
def hitRate : ℝ :=
  2 * (b : ℝ) / ((init.card : ℝ) * ((init.card : ℝ) - 1))

theorem hitRate_nonneg (hc : 2 ≤ init.card) : 0 ≤ hitRate init b := by
  unfold hitRate
  have : (2 : ℝ) ≤ init.card := by exact_mod_cast hc
  apply div_nonneg (by positivity)
  nlinarith

/-- The window: the threshold reached, less than `k` steps ago (relative to the base
`s`), and `j` not yet capped. -/
def highAllWindow (t : ℕ) : Set (InputLog n) :=
  {ω | ReachedTop init b t ω ∧ BeforeHighPlus init s b k t ω ∧
    ¬ Capped init (virtualLabels init ω t) j}

theorem highAllWindow_measurableSet (t : ℕ) :
    MeasurableSet[pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256 t]
      (highAllWindow init b s k j t) :=
  (reachedTop_measurableSet init _ le_rfl).inter
    ((beforeHighPlus_measurableSet init _).inter (capped_measurableSet init j le_rfl).compl)

/-- The P2 factor: `(1 - p)⁻¹` on a step without a hit, `0` on a hit, on the window. -/
def highAllFactor (u : ℕ) : InputLog n → ℝ :=
  windowFactor (highAllWindow init b s k j (s + u))
    (fun ω => (1 - hitRate init b)⁻¹ * affFactor init 0 (HitPair init j) (s + u) ω)
    (fun _ => 1)

theorem highAllFactor_nonneg (hp : hitRate init b < 1) (u : ℕ) (ω : InputLog n) :
    0 ≤ highAllFactor init b s k j u ω :=
  windowFactor_nonneg
    (fun ω => mul_nonneg (inv_nonneg.mpr (by linarith)) (affFactor_nonneg init le_rfl _ _ ω))
    (fun _ => zero_le_one) ω

theorem one_le_inv_one_sub (hc : 2 ≤ init.card) (hp : hitRate init b < 1) :
    1 ≤ (1 - hitRate init b)⁻¹ := by
  have h0 := hitRate_nonneg init b hc
  rw [le_inv_comm₀ (by norm_num) (by linarith)]
  simp only [inv_one]
  linarith

theorem highAllFactor_le (hc : 2 ≤ init.card) (hp : hitRate init b < 1) (u : ℕ)
    (ω : InputLog n) :
    highAllFactor init b s k j u ω ≤ (1 - hitRate init b)⁻¹ :=
  windowFactor_le
    (fun ω => by
      have h1 := affFactor_le init (a := (0 : ℝ)) (b := 1) (by norm_num) le_rfl
        (HitPair init j) (s + u) ω
      have h2 := affFactor_nonneg init (le_refl (0 : ℝ)) (HitPair init j) (s + u) ω
      have h3 : 0 ≤ (1 - hitRate init b)⁻¹ := inv_nonneg.mpr (by linarith)
      nlinarith)
    (fun _ => one_le_inv_one_sub init b hc hp) ω

theorem highAllFactor_stronglyMeasurable (u : ℕ) :
    StronglyMeasurable[shiftedFiltration
      (pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256) s (u + 1)]
      (highAllFactor init b s k j u) := by
  rw [shiftedFiltration_apply, ← Nat.add_assoc]
  exact windowFactor_const_stronglyMeasurable init _ _ (highAllWindow init b s k j) _ (s + u)
    (highAllWindow_measurableSet init b s k j (s + u))

/-- The conditional mean of the P2 factor is at most one. -/
theorem highAllFactor_condExp_le_one (hc : 2 ≤ init.card) (hp : hitRate init b < 1) (u : ℕ) :
    (law init)[highAllFactor init b s k j u | shiftedFiltration
      (pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256) s u] ≤ᵐ[law init]
      fun _ => 1 := by
  set ℱ := pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256 with hℱ
  rw [shiftedFiltration_apply]
  unfold highAllFactor
  set c : ℝ := (1 - hitRate init b)⁻¹ with hcdef
  have hYeq : (fun ω => c * affFactor init 0 (HitPair init j) (s + u) ω) =
      fun ω => c + (-c) * pairInd init (HitPair init j) (s + u) ω +
        0 * pairInd init (HitPair init j) (s + u) ω := by
    funext ω
    unfold affFactor
    ring
  rw [hYeq]
  apply windowFactor_condExp_le_one (highAllWindow_measurableSet init b s k j (s + u))
    (affine_two_integrable init _ _ _ _ _ _) (integrable_const 1) ?_
    (condExp_one_off init _ (s + u))
  filter_upwards [condExp_affine_two init c (-c) 0 (HitPair init j) (HitPair init j) (s + u),
    pairInd_condExp init hc (HitPair init j) (s + u)] with ω h1 h2
  intro hW
  rw [h1, h2]
  obtain ⟨hhigh, -, hcap⟩ := hW
  have hcount := goodPairs_hitPair_card_ge init j _ hcap
  have hX : b ≤ topCount init ω (s + u) := hhigh
  have hP : (0 : ℝ) < (init.card : ℝ) * ((init.card : ℝ) - 1) := by
    have : (2 : ℝ) ≤ init.card := by exact_mod_cast hc
    nlinarith
  have hcpos : 0 < c := inv_pos.mpr (by linarith [hitRate_nonneg init b hc])
  have hfrac : hitRate init b ≤
      ((goodPairs (HitPair init j) (virtualLabels init ω (s + u))).card : ℝ) /
        ((init.card : ℝ) * ((init.card : ℝ) - 1)) := by
    unfold hitRate
    apply div_le_div_of_nonneg_right _ hP.le
    have h1 : (2 * b : ℕ) ≤ (goodPairs (HitPair init j) (virtualLabels init ω (s + u))).card :=
      le_trans (Nat.mul_le_mul_left 2 hX) hcount
    exact_mod_cast h1
  have hc1 : c * (1 - hitRate init b) = 1 := by
    rw [hcdef]
    exact inv_mul_cancel₀ (by linarith)
  nlinarith

/-- The P2 bad event on the horizon `N` (base `s`, entry seed `s₀ ≤ s`): the Clock `j` of
the seed, the threshold first reached (at or after `s`) at `v` with `v + k` inside the
horizon, `j` in Phase 3 from `v` on, and `j` still uncapped at `v + k`. -/
def highAllBad (N : ℕ) : Set (InputLog n) :=
  {ω | (∃ T, AsyncEntry init ω s₀ T) ∧ s₀ ≤ s ∧ (virtualLabels init ω s₀ j).role = .clock ∧
    ∃ v, firstAfter (fun t => ReachedTop init b t ω) s v ∧
      v + k ≤ s + N ∧ (∀ u, v ≤ u → (virtualLabels init ω u j).phase.val = 3) ∧
      ¬ Capped init (virtualLabels init ω (v + k)) j}

/-- The P2 tail: relative probability at most `e^{-p k}`. -/
theorem high_all_tail (hc : 2 ≤ init.card) (hp : hitRate init b < 1) (N : ℕ)
    (E : Set (InputLog n))
    (hE : MeasurableSet[pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256 s] E) :
    law init (E ∩ highAllBad init b s₀ s k j N) ≤
      ENNReal.ofReal (Real.exp (-(hitRate init b * k))) * law init E := by
  set ℱ := shiftedFiltration (pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256) s
    with hℱ
  have hE' : MeasurableSet[ℱ 0] E := by
    simpa only [hℱ, shiftedFiltration_apply, Nat.add_zero] using hE
  set c : ℝ := (1 - hitRate init b)⁻¹ with hcdef
  have hc1 : 1 ≤ c := one_le_inv_one_sub init b hc hp
  have hr : (0 : ℝ) < c ^ k := by positivity
  have htail := prefix_product_tail_ennreal (μ := law init) (ℱ := ℱ)
    (highAllFactor_stronglyMeasurable init b s k j) (highAllFactor_nonneg init b s k j hp)
    (highAllFactor_le init b s k j hc hp) (highAllFactor_condExp_le_one init b s k j hc hp) E hE'
    N (highAllBad init b s₀ s k j N) hr ?_
  · refine htail.trans (mul_le_mul_right' (ENNReal.ofReal_le_ofReal ?_) _)
    have hpos : 0 < 1 - hitRate init b := by linarith
    have hexp : 1 - hitRate init b ≤ Real.exp (-(hitRate init b)) := by
      have := Real.add_one_le_exp (-(hitRate init b))
      linarith
    rw [one_div, hcdef, inv_pow, inv_inv]
    calc (1 - hitRate init b) ^ k ≤ Real.exp (-(hitRate init b)) ^ k :=
          pow_le_pow_left₀ hpos.le hexp k
      _ = Real.exp (-(hitRate init b * k)) := by
          rw [← Real.exp_nat_mul]
          congr 1
          ring
  · rintro ω ⟨-, ⟨T, hentry⟩, hs₀s, hjr, v, hfirst, hvN, hphase, hcap⟩
    have hprod := prefixProduct_window_const init c 0 (highAllWindow init b s k j)
      (HitPair init j) s N ω
    have hsv : s ≤ v := hfirst.1
    have hhv : ReachedTop init b v ω := hfirst.2.1
    -- every time in `[v, v + k)` is in the window
    have hwin : ∀ t, v ≤ t → t < v + k → ω ∈ highAllWindow init b s k j t := by
      intro t hvt htk
      refine ⟨reachedTop_persist init ω hentry _ (by omega) hvt hhv, ?_, ?_⟩
      · intro v' hsv' hv'k hv'
        have hvv' : v ≤ v' := by
          by_contra hlt
          exact hfirst.2.2 v' hsv' (by omega) hv'
        omega
      · intro hcapt
        exact hcap (capped_persist init ω hentry (by omega) (by omega) j hcapt)
    -- no hit on the window
    have hnohit : windowCount
        (fun t ω => ω ∈ highAllWindow init b s k j t ∧ StepEvent init (HitPair init j) t ω)
          s N ω = 0 := by
      classical
      unfold windowCount
      apply Finset.sum_eq_zero
      intro u _
      rw [if_neg]
      rintro ⟨⟨hhigh, hbefore, hcapu⟩, a, b', hd, hhit⟩
      have hvu : v ≤ s + u := by
        by_contra hlt
        exact hfirst.2.2 (s + u) (by omega) (by omega) hhigh
      have hlt : s + u < v + k := by
        by_contra hge
        exact hbefore v hsv (by omega) hhv
      have hroles := virtualLabels_roles_fixed_of_asyncEntry init ω s₀ T hentry
      have hjr' : (virtualLabels init ω (s + u) j).role = .clock := by
        rw [hroles (s + u) (by omega) j, ← hroles s₀ le_rfl j]
        exact hjr
      have hcapped := capped_of_hitPair init ω hentry (s + u) (by omega) j hjr'
        (hphase (s + u) hvu) a b' hd hhit
      exact hcap (capped_persist init ω hentry (by omega) (by omega) j hcapped)
    have hk : k ≤ windowCount (fun t ω => ω ∈ highAllWindow init b s k j t) s N ω :=
      le_windowCount_of_forall _ s N ω hsv hvN hwin
    calc c ^ k ≤ c ^ windowCount (fun t ω => ω ∈ highAllWindow init b s k j t) s N ω :=
          pow_le_pow_right₀ hc1 hk
      _ = c ^ windowCount (fun t ω => ω ∈ highAllWindow init b s k j t) s N ω *
          (0 : ℝ) ^ windowCount
            (fun t ω => ω ∈ highAllWindow init b s k j t ∧
              StepEvent init (HitPair init j) t ω) s N ω := by
          rw [hnohit, pow_zero, mul_one]
      _ = prefixProduct (highAllFactor init b s k j) N ω := hprod.symm

end HighAll

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockCapPassages

end
