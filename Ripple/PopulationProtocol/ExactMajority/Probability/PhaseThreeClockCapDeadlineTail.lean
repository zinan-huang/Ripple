import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockCapDeadline
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockContactBridge
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockRowsGuarded
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockSeedTails

/-!
# The guarded cap-row tail (N12, step 4, PHASE3 P13 row of §11)

The fibres `capPrefix s T C` (seed `s`, all-three time `T`, seed Clock set `C`) are
measurable at `T`. On a fibre, outside the level bad events of
`PhaseThreeClockCapDeadline`, the thinning bad event (fewer than `4CQ + 1` Clock pairs in
`rawWindow` raw steps after `T`) and the coupon bad events (a Clock uncapped
`finHalfWindow` steps after half the Clocks are capped), the canonical cap is at most
`T + rawWindow + finHalfWindow ≤ T + logWindow n 16000` (`cap_of_good`), so the cap row
holds. The tail `guarded_cap_tail` is the cap row of
`PhaseThreeClockRowsGuarded.GuardedRowTails`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators MeasureTheory ProbabilityTheory

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockCapDeadlineTail

open TimeTheorem PairLog PairLogAuxiliary PhaseThreeClockVirtual
  PhaseThreeClockGatedLaw PhaseThreeClockGatedLevelOne PhaseThreeClockEmbedding
  PhaseThreeClockEmbeddingBridge PhaseThreeClockCore PhaseThreeClockRows
  PhaseThreeClockProductTails PhaseThreeScalar PhaseThreeClockPrefixTails
  PhaseThreeClockProbabilityFloors PhaseThreeClockRegime PhaseThreeClockCapSpread
  PhaseThreeClockCapPassages PhaseThreeClockThinning PhaseThreeClockProducer
  PhaseThreeClockCapDeadline PhaseThreeClockContactBridge PhaseThreeClockRowsGuarded
  PhaseThreeClockSeedTails
open StageEventSpec hiding frontCount clockCount
open Classical

variable {n : ℕ} (init : InputCfg n)

/-- The raw-step allowance for `4 C Q + 1` Clock pairs at the Clock-pair rate. -/
def rawWindow (n C : ℕ) : ℕ :=
  Nat.ceil (2 * ((4 * C * clockTop n + 1 : ℕ) : ℝ) / clockMaskRate n C)

/-- The raw-step allowance of the half-to-all cap spread, `⌈6 n² ln n / C⌉`. -/
def finHalfWindow (n C : ℕ) : ℕ :=
  Nat.ceil (6 * (n : ℝ) ^ 2 * Real.log (n : ℝ) / (C : ℝ))

/-! ## The fibres -/

/-- The fibre: the genuine seed `s` with its profile, the genuine all-three time `T`, and
the seed Clock set `C` with the seed density. -/
def capPrefix (s T : ℕ) (C : Finset (Fin init.card)) : Set (InputLog n) :=
  {ω | seedTime init 3 ω = (s : WithTop ℕ) ∧ SeedProfile n init (trace init ω s) ∧
    firstHit (allGE 3) (trace init ω) T ∧ clockSet (virtualLabels init ω s) = C ∧
    6 * n ≤ 25 * C.card ∧ C.card ≤ n ∧ s ≤ T}

theorem firstHit_allGE_measurableSet (T : ℕ) :
    MeasurableSet[pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256 T]
      {ω | firstHit (allGE 3) (trace init ω) T} := by
  have hset : {ω | firstHit (allGE 3) (trace init ω) T} =
      {ω | allGE 3 (trace init ω T)} ∩
        {ω | ∀ u, u ≤ T → ω ∈ {ω | u < T → ¬ allGE 3 (trace init ω u)}} := by
    ext ω
    simp only [firstHit, Set.mem_setOf_eq, Set.mem_inter_iff]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun u _ hu => h2 u hu⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun u hu => h2 u (by omega) hu⟩
  rw [hset]
  refine MeasurableSet.inter ?_ ?_
  · exact (show MeasurableSet {c : InputCfg n | allGE 3 c} from
      (Set.to_countable _).measurableSet).preimage (measurable_trace_at init T)
  · apply measurableSet_forall_le
    intro u hu
    by_cases huT : u < T
    · have hset' : {ω : InputLog n | u < T → ¬ allGE 3 (trace init ω u)} =
          {ω | ¬ allGE 3 (trace init ω u)} := by
        ext ω
        simp only [Set.mem_setOf_eq, huT, true_implies]
      rw [hset']
      exact ((show MeasurableSet {c : InputCfg n | allGE 3 c} from
        (Set.to_countable _).measurableSet).preimage
        (measurable_trace_at_of_le init hu)).compl
    · have hset' : {ω : InputLog n | u < T → ¬ allGE 3 (trace init ω u)} = Set.univ := by
        ext ω
        simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
        intro h
        exact absurd h huT
      rw [hset']
      exact MeasurableSet.univ

theorem capPrefix_measurableSet (s T : ℕ) (C : Finset (Fin init.card)) :
    MeasurableSet[pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256 T]
      (capPrefix init s T C) := by
  by_cases hdens : 6 * n ≤ 25 * C.card ∧ C.card ≤ n ∧ s ≤ T
  · obtain ⟨h1, h2, hsT⟩ := hdens
    have hset : capPrefix init s T C =
        seedPrefix init s ∩
          ({ω | firstHit (allGE 3) (trace init ω) T} ∩
            {ω | clockSet (virtualLabels init ω s) = C}) := by
      ext ω
      simp only [capPrefix, seedPrefix, Set.mem_setOf_eq, Set.mem_inter_iff, h1, h2, hsT,
        and_true, and_assoc]
    rw [hset]
    have hmono := (pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256).mono hsT
    exact (hmono _ (seedPrefix_measurable init s)).inter
      ((firstHit_allGE_measurableSet init T).inter
        (measurableSet_virtual_single init hsT (fun f => clockSet f = C)))
  · have hset : capPrefix init s T C = ∅ := by
      ext ω
      simp only [capPrefix, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨-, -, -, -, h1, h2, h3⟩
      exact hdens ⟨h1, h2, h3⟩
    rw [hset]
    exact @MeasurableSet.empty _ (pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256 T)

theorem capPrefix_disjoint {a b : ℕ × ℕ × Finset (Fin init.card)} (hab : a ≠ b) :
    Disjoint (capPrefix init a.1 a.2.1 a.2.2) (capPrefix init b.1 b.2.1 b.2.2) := by
  rw [Set.disjoint_left]
  rintro ω ⟨ha1, -, ha3, ha4, -, -, -⟩ ⟨hb1, -, hb3, hb4, -, -, -⟩
  have hs : a.1 = b.1 := by
    have := ha1.symm.trans hb1
    exact_mod_cast this
  have hT : a.2.1 = b.2.1 := firstHit_unique ha3 hb3
  apply hab
  apply Prod.ext hs
  apply Prod.ext hT
  rw [← ha4, ← hb4, hs]

/-- On the fibre the virtual and the actual labellings agree at the seed. -/
theorem virtual_eq_actual_at_seed {s T : ℕ} {C : Finset (Fin init.card)} {ω : InputLog n}
    (hω : ω ∈ capPrefix init s T C) :
    virtualLabels init ω s = labelsAt init ω s := by
  obtain ⟨hs, hprof, -, -, -, -, -⟩ := hω
  have hseed := (seedTime_eq_iff init 3 ω s).mp hs
  refine virtualLabels_eq_labelsAt_of_phases_lt_four init ω s (fun u hu i => ?_) s le_rfl
  rcases Nat.lt_or_ge u s with hlt | hge
  · have := hseed.2 u hlt _ (labelsAt_mem_trace init ω u i)
    omega
  · have hus : u = s := by omega
    rw [hus]
    have := (hprof.phase_range _ (labelsAt_mem_trace init ω s i)).2
    omega

/-! ## The bad events of a fibre -/

section Fibre

variable (s T : ℕ) (C : Finset (Fin init.card))

/-- The horizon of the fibre, from `T`. -/
def capHorizon : ℕ := rawWindow n C.card + finHalfWindow n C.card

/-- Fewer than `4 C Q + 1` Clock pairs in the raw window after `T`. -/
def thinBad : Set (InputLog n) :=
  {ω | (StageEventSpec.clockContacts init ω s T (T + rawWindow n C.card) : ℝ) <
    ((4 * C.card * clockTop n + 1 : ℕ) : ℝ)}

/-- The bad event of the fibre. -/
def capBad : Set (InputLog n) :=
  (⋃ i ∈ Finset.range (clockTop n), halfBad init C T i (capHorizon init C)) ∪
    (thinBad init s T C ∪
      ⋃ j ∈ C, highAllBad init (halfThr C.card) s T (finHalfWindow n C.card) j (capHorizon init C))

/-! ## The deterministic bridge -/

variable (ω : InputLog n)

theorem levelCount_anti_level (ℓ ℓ' : ℕ) (h : ℓ ≤ ℓ') (t : ℕ) :
    levelCount init ω ℓ' t ≤ levelCount init ω ℓ t := by
  unfold levelCount frontCount
  apply Finset.card_le_card
  intro i hi
  simp only [aboveSet, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  exact ⟨hi.1, le_trans h hi.2⟩

/-- The row's cap time is the first all-cap time; a half-capped time followed by the coupon
allowance bounds it. -/
theorem cap_of_good {C : Finset (Fin init.card)} (hC : C = clockSet (virtualLabels init ω s))
    (hentry : AsyncEntry init ω s T) (hpass : passageRow init ω s T)
    (hC2 : 2 ≤ C.card)
    (hlevel : ∀ i ∈ Finset.range (clockTop n), ω ∉ halfBad init C T i ((capHorizon init C)))
    (hthin : ω ∉ thinBad init s T C)
    (hcoupon : ∀ j ∈ C, ω ∉ highAllBad init (halfThr C.card) s T ((finHalfWindow n C.card)) j
      ((capHorizon init C))) :
    (virtualTimes init ω s).cap ≤ T + (rawWindow n C.card) + (finHalfWindow n C.card) := by
  have hN'eq : (capHorizon init C) = (rawWindow n C.card) + (finHalfWindow n C.card) := rfl
  have hsT : s ≤ T := hentry.order
  have hcardC := card_eq_clockCount init ω C hC
  have hcapfirst := cap_firstAfter init ω hentry hpass
  have hroles := virtualLabels_roles_fixed_of_asyncEntry init ω s T hentry
  have hvs : virtualLabels init ω s = labelsAt init ω s :=
    virtualLabels_eq_labelsAt_through_asyncEntry init ω s T hentry s hsT
  -- all agents in Phase 3 from `T`
  have hT3 : ∀ i, (virtualLabels init ω T i).phase.val = 3 := by
    intro i
    rw [virtualLabels_eq_labelsAt_through_asyncEntry init ω s T hentry T le_rfl]
    exact hentry.advanced_profile.all_three _ (labelsAt_mem_trace init ω T i)
  have hall3 : ∀ t, T ≤ t → ∀ k, (virtualLabels init ω t k).phase.val = 3 :=
    fun t ht k => virtualLabels_phase_three_of_time init ω T hT3 t ht k
  -- the Clock pairs in the (rawWindow n C.card) window, as a sum
  have hcc : ((4 * C.card * clockTop n + 1 : ℕ) : ℝ) ≤
      (StageEventSpec.clockContacts init ω s T (T + (rawWindow n C.card)) : ℝ) := by
    by_contra hlt
    exact hthin (not_le.mp hlt)
  have hccN : 4 * C.card * clockTop n + 1 ≤
      ∑ t ∈ Finset.Ico T (T + (rawWindow n C.card)), if StepEvent init (CCPair init) t ω then 1 else 0 := by
    have h1 : 4 * C.card * clockTop n + 1 ≤ StageEventSpec.clockContacts init ω s T (T + (rawWindow n C.card)) := by
      exact_mod_cast hcc
    have h2 : StageEventSpec.clockContacts init ω s T (T + (rawWindow n C.card)) =
        clockContactsL init (virtualLabels init ω s) (drawLabels init ω) T (T + (rawWindow n C.card)) := by
      rw [hvs]
      rfl
    rw [h2, clockContactsL_eq_sum init ω hentry hsT] at h1
    exact h1
  -- the level induction
  have hwin : ∀ i, i < clockTop n → ∀ t, T ≤ t → ∀ v, firstAfter
      (fun v => halfThr C.card ≤ levelCount init ω i v) T v →
      (ω ∈ halfWindow init C i t ↔ v ≤ t ∧ ¬ halfThr C.card ≤ levelCount init ω (i + 1) t) := by
    intro i hi t hTt v hv
    unfold halfWindow
    simp only [Set.mem_setOf_eq]
    have hCt := clockCount_eq_at init ω hentry C hC t (le_trans hsT hTt)
    constructor
    · rintro ⟨-, -, hlo, hhi⟩
      refine ⟨?_, hhi⟩
      by_contra hlt
      exact hv.2.2 t hTt (by omega) hlo
    · rintro ⟨hvt, hhi⟩
      refine ⟨hCt, fun k _ => by rw [hall3 t hTt k], ?_, hhi⟩
      exact le_trans hv.2.1 (levelCount_mono init ω hentry i (by omega) (le_trans hsT hv.1) hvt)
  have hind : ∀ i, i ≤ clockTop n → ∃ v, firstAfter
      (fun v => halfThr C.card ≤ levelCount init ω i v) T v ∧ v ≤ T + (rawWindow n C.card) ∧
      (∑ t ∈ Finset.Ico T v, if StepEvent init (CCPair init) t ω then 1 else 0) ≤
        i * (4 * C.card - 1) := by
    intro i
    induction i with
    | zero =>
        intro _
        refine ⟨T, ⟨le_rfl, ?_, fun u hTu hut _ => by omega⟩, by omega, by simp⟩
        show halfThr C.card ≤ levelCount init ω 0 T
        rw [levelCount_zero, clockCount_eq_at init ω hentry C hC T hsT]
        exact halfThr_le _
    | succ i ih =>
        intro hiQ
        obtain ⟨v, hv, hvraw, hcount⟩ := ih (by omega)
        have hi : i < clockTop n := by omega
        -- the window of level `i` starts at `v`
        have hcnt := hlevel i (Finset.mem_range.mpr hi)
        have hcnt' : windowCount
            (fun t ω => ω ∈ halfWindow init C i t ∧ StepEvent init (CCPair init) t ω) T (capHorizon init C) ω <
            4 * C.card := by
          by_contra hge
          exact hcnt ⟨⟨s, T, hentry, hsT⟩, clockCount_eq_at init ω hentry C hC T hsT, by omega⟩
        by_cases hex : ∃ t, T ≤ t ∧ t ≤ T + (rawWindow n C.card) ∧ halfThr C.card ≤ levelCount init ω (i + 1) t
        · obtain ⟨t₀, hTt₀, ht₀raw, ht₀⟩ := hex
          obtain ⟨v', hv'⟩ := exists_firstAfter
            (P := fun v => halfThr C.card ≤ levelCount init ω (i + 1) v) hTt₀ ht₀
          have hv'raw : v' ≤ T + (rawWindow n C.card) := (firstAfter_le_of hv' hTt₀ ht₀).trans ht₀raw
          have hvv' : v ≤ v' := by
            apply firstAfter_le_of hv hv'.1
            exact le_trans hv'.2.1 (levelCount_anti_level init ω i (i + 1) (by omega) v')
          refine ⟨v', hv', hv'raw, ?_⟩
          -- the pairs on `[v, v')` are the window pairs
          have hcongr := windowCount_congr
            (P := fun t ω => ω ∈ halfWindow init C i t ∧ StepEvent init (CCPair init) t ω)
            (R := fun t ω => v ≤ t ∧ t < v' ∧ StepEvent init (CCPair init) t ω)
            T (capHorizon init C) ω (fun t hTt => by
            dsimp only
            rw [hwin i hi t hTt v hv]
            constructor
            · rintro ⟨⟨h1, h2⟩, h3⟩
              refine ⟨h1, ?_, h3⟩
              by_contra hge
              exact h2 (le_trans hv'.2.1 (levelCount_mono init ω hentry (i + 1) hiQ
                (le_trans hsT hv'.1) (by omega)))
            · rintro ⟨h1, h2, h3⟩
              refine ⟨⟨h1, ?_⟩, h3⟩
              intro hle
              exact hv'.2.2 t hTt h2 hle)
          rw [hcongr, windowCount_interval _ T (capHorizon init C) ω hv.1 hvv' (by omega)] at hcnt'
          rw [← Finset.sum_Ico_consecutive _ hv.1 hvv', Nat.succ_mul]
          omega
        · -- no half time of level `i + 1` within the (rawWindow n C.card) window: the window covers
          -- `[v, T + (rawWindow n C.card))` and the Clock pairs contradict the thinning event
          exfalso
          push_neg at hex
          have hcongr := windowCount_congr
            (P := fun t ω => ω ∈ halfWindow init C i t ∧ StepEvent init (CCPair init) t ω)
            (R := fun t ω => (v ≤ t ∧ t < T + (rawWindow n C.card) ∧ StepEvent init (CCPair init) t ω) ∨
                (ω ∈ halfWindow init C i t ∧ T + (rawWindow n C.card) ≤ t ∧
                  StepEvent init (CCPair init) t ω))
            T (capHorizon init C) ω (fun t hTt => by
            dsimp only
            constructor
            · rintro ⟨hw, h3⟩
              obtain ⟨h1, h2⟩ := (hwin i hi t hTt v hv).mp hw
              by_cases hlt : t < T + (rawWindow n C.card)
              · exact Or.inl ⟨h1, hlt, h3⟩
              · exact Or.inr ⟨hw, by omega, h3⟩
            · rintro (⟨h1, h2, h3⟩ | ⟨h1, -, h3⟩)
              · refine ⟨(hwin i hi t hTt v hv).mpr ⟨h1, fun hle => ?_⟩, h3⟩
                have := hex t hTt (by omega)
                omega
              · exact ⟨h1, h3⟩)
          have hsplit : windowCount
              (fun t ω => (v ≤ t ∧ t < T + (rawWindow n C.card) ∧ StepEvent init (CCPair init) t ω) ∨
                (ω ∈ halfWindow init C i t ∧ T + (rawWindow n C.card) ≤ t ∧
                  StepEvent init (CCPair init) t ω)) T (capHorizon init C) ω ≥
              windowCount (fun t ω => v ≤ t ∧ t < T + (rawWindow n C.card) ∧ StepEvent init (CCPair init) t ω)
                T (capHorizon init C) ω :=
            windowCount_mono (fun t ω h => Or.inl h) T (capHorizon init C) ω
          rw [hcongr] at hcnt'
          rw [windowCount_interval _ T (capHorizon init C) ω hv.1 hvraw (by omega)] at hsplit
          have htotal : (∑ t ∈ Finset.Ico T v, if StepEvent init (CCPair init) t ω then 1 else 0) +
              (∑ t ∈ Finset.Ico v (T + (rawWindow n C.card)), if StepEvent init (CCPair init) t ω then 1 else 0) =
              ∑ t ∈ Finset.Ico T (T + (rawWindow n C.card)), if StepEvent init (CCPair init) t ω then 1 else 0 :=
            Finset.sum_Ico_consecutive _ hv.1 hvraw
          have hQ : i + 1 ≤ clockTop n := hiQ
          have hCpos : 1 ≤ C.card := by omega
          -- `(i + 1) (4 C - 1) < 4 C Q + 1`
          have hbound : (i + 1) * (4 * C.card - 1) + 1 ≤ 4 * C.card * clockTop n := by
            have h1 : (i + 1) * (4 * C.card - 1) + 1 ≤ (i + 1) * (4 * C.card) := by
              have hA : i + 1 ≤ (i + 1) * (4 * C.card) := Nat.le_mul_of_pos_right _ (by omega)
              rw [Nat.mul_sub_one]
              omega
            have h2 : (i + 1) * (4 * C.card) ≤ clockTop n * (4 * C.card) :=
              Nat.mul_le_mul_right _ hQ
            nlinarith
          rw [Nat.succ_mul] at hbound
          omega
  obtain ⟨vQ, hvQ, hvQraw, -⟩ := hind (clockTop n) le_rfl
  have hTvQ : T ≤ vQ := hvQ.1
  -- all Clocks capped at `vQ + (finHalfWindow n C.card)`
  have hcapped : ∀ j, (virtualLabels init ω s j).role = .clock →
      Capped init (virtualLabels init ω (vQ + (finHalfWindow n C.card))) j := by
    intro j hj
    have hjC : j ∈ C := by
      rw [hC]
      simp only [clockSet, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hj
    by_contra hnot
    apply hcoupon j hjC
    refine ⟨⟨T, hentry⟩, hsT, hj, vQ, hvQ, by omega, fun u hu => hall3 u (le_trans hTvQ hu) j, hnot⟩
  have hallcap : AllCapAt init s (vQ + (finHalfWindow n C.card)) ω :=
    allCapAt_of_all_capped init ω hentry (vQ + (finHalfWindow n C.card)) (by omega) hcapped
  have := firstAfter_le_of hcapfirst (by omega) hallcap
  omega

end Fibre

/-! ## Numerics at the population threshold -/

section Numerics

theorem log_facts (hn : PhaseThreeModel.Numeric.populationThreshold ≤ n) :
    (4194304 : ℝ) ≤ Real.log (n : ℝ) ∧ Real.exp (Real.log (n : ℝ)) = n ∧
      (Real.log (n : ℝ)) ^ 2 / 2 ≤ n := by
  have hpos : 0 < n := pos_of_threshold hn
  have hposR : (0 : ℝ) < n := by exact_mod_cast hpos
  obtain ⟨-, hx, -, -, -⟩ := PhaseThreeModel.Numeric.logarithmic_inputs hn
    (show (6 / 25 : ℝ) * n ≤ n by linarith) le_rfl
  clear hn
  refine ⟨hx, Real.exp_log hposR, ?_⟩
  have hq := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ Real.log n by linarith)
  rw [Real.exp_log hposR] at hq
  linarith [Real.log_nonneg (show (1 : ℝ) ≤ n by exact_mod_cast hpos)]

theorem hourIndex_le_log (hn : PhaseThreeModel.Numeric.populationThreshold ≤ n) :
    (PhaseThreeModel.Numeric.hourIndex n : ℝ) ≤ 3 / 2 * Real.log (n : ℝ) + 1 := by
  rw [PhaseThreeModel.Numeric.hourIndex_eq_real_ceiling]
  obtain ⟨hL, -, -⟩ := log_facts hn
  clear hn
  have hl2 := PhaseThreeModel.Numeric.log_two_bounds
  have hpos : 0 < Real.log 2 := by linarith
  have h1 : Real.log (n : ℝ) / Real.log 2 ≤ 3 / 2 * Real.log (n : ℝ) := by
    rw [div_le_iff₀ hpos]
    nlinarith
  have h2 := Nat.ceil_lt_add_one (show 0 ≤ Real.log (n : ℝ) / Real.log 2 by positivity)
  linarith

theorem exp_neg_mul_log (hn : PhaseThreeModel.Numeric.populationThreshold ≤ n) (k : ℕ) :
    Real.exp (-((k : ℝ) * Real.log (n : ℝ))) = 1 / (n : ℝ) ^ k := by
  have hpos : (0 : ℝ) < n := by exact_mod_cast pos_of_threshold hn
  rw [show -((k : ℝ) * Real.log (n : ℝ)) = (k : ℕ) * (-Real.log (n : ℝ)) by ring,
    Real.exp_nat_mul, Real.exp_neg, Real.exp_log hpos, inv_pow, one_div]

/-- `rawWindow + finHalfWindow ≤ logWindow n 16000`. -/
theorem raw_fin_le (hn : PhaseThreeModel.Numeric.populationThreshold ≤ n) {C : ℕ}
    (hlo : 6 * n ≤ 25 * C) (hCn : C ≤ n) :
    rawWindow n C + finHalfWindow n C ≤ logWindow n 16000 := by
  obtain ⟨hL, hexp, hquad⟩ := log_facts hn
  have hH := hourIndex_le_log hn
  clear hn
  set L := Real.log (n : ℝ) with hLdef
  have hlo' : (6 : ℝ) * n ≤ 25 * C := by exact_mod_cast hlo
  have hCn' : (C : ℝ) ≤ n := by exact_mod_cast hCn
  have hnR : (2 : ℝ) ^ 57 ≤ n := by
    have hTaylor := Real.pow_div_factorial_le_exp _
      (le_trans (by norm_num) hL) 3
    norm_num [Nat.factorial] at hTaylor
    rw [hexp] at hTaylor
    have hcube := PhaseThreeModel.Numeric.logarithm_cube_lower hL
    rw [show (2 : ℝ) ^ 57 = 144115188075855872 by norm_num]
    linarith only [hTaylor, hcube, hL]
  have hCpos : (2 : ℝ) ≤ C := by nlinarith
  have hQ : (clockTop n : ℝ) ≤ 384 * L + 512 := by
    unfold clockTop
    push_cast
    nlinarith
  -- the raw window
  have hC1 : 1 ≤ C := by
    have : (1 : ℝ) ≤ C := by linarith
    exact_mod_cast this
  have hp : clockMaskRate n C = (C : ℝ) * ((C : ℝ) - 1) / ((n : ℝ) * ((n : ℝ) - 1)) := by
    unfold clockMaskRate
    rw [Nat.cast_mul, Nat.cast_sub hC1]
    push_cast
    ring
  have hppos : 0 < clockMaskRate n C := by
    rw [hp]
    apply div_pos (by nlinarith) (by nlinarith)
  have hraw : (rawWindow n C : ℝ) ≤ (40 * (clockTop n : ℝ) + 10) * n + 1 := by
    unfold rawWindow
    refine (Nat.ceil_lt_add_one (by positivity)).le.trans ?_
    rw [hp]
    have hr : ((4 * C * clockTop n + 1 : ℕ) : ℝ) ≤ (C : ℝ) * (4 * clockTop n + 1) := by
      push_cast
      nlinarith
    have hden : (1 / 5 : ℝ) * n ≤ (C : ℝ) - 1 := by nlinarith
    have hkey : 2 * ((C : ℝ) * (4 * clockTop n + 1)) /
        ((C : ℝ) * ((C : ℝ) - 1) / ((n : ℝ) * ((n : ℝ) - 1))) ≤
        (40 * (clockTop n : ℝ) + 10) * n := by
      rw [div_div_eq_mul_div, div_le_iff₀ (by nlinarith)]
      have hQ0 : (0 : ℝ) ≤ clockTop n := Nat.cast_nonneg _
      have key : (0 : ℝ) ≤ 2 * C * (4 * clockTop n + 1) * n * (5 * ((C : ℝ) - 1) - ((n : ℝ) - 1)) :=
        mul_nonneg (by positivity) (by linarith)
      nlinarith [key]
    have hmono : 2 * ((4 * C * clockTop n + 1 : ℕ) : ℝ) /
        ((C : ℝ) * ((C : ℝ) - 1) / ((n : ℝ) * ((n : ℝ) - 1))) ≤
        2 * ((C : ℝ) * (4 * clockTop n + 1)) /
        ((C : ℝ) * ((C : ℝ) - 1) / ((n : ℝ) * ((n : ℝ) - 1))) := by
      apply div_le_div_of_nonneg_right (by linarith)
      apply div_nonneg (by nlinarith) (by nlinarith)
    linarith
  have hfin : (finHalfWindow n C : ℝ) ≤ 25 * n * L + 1 := by
    unfold finHalfWindow
    refine (Nat.ceil_lt_add_one (by positivity)).le.trans ?_
    have : 6 * (n : ℝ) ^ 2 * L / C ≤ 25 * n * L := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith [mul_le_mul_of_nonneg_right hlo' (show (0 : ℝ) ≤ n * L by positivity)]
    linarith
  have hlw : 16000 * (n : ℝ) * L ≤ (logWindow n 16000 : ℝ) := by
    unfold logWindow
    push_cast
    exact Nat.le_ceil _
  have hsum : (rawWindow n C : ℝ) + finHalfWindow n C ≤ 16000 * (n : ℝ) * L := by
    nlinarith
  have hcast : ((rawWindow n C + finHalfWindow n C : ℕ) : ℝ) ≤ (logWindow n 16000 : ℝ) := by
    push_cast
    linarith
  exact_mod_cast hcast

/-- `2 · logWindow n 6 + logWindow n 16000 ≤ logWindow n 20000`. -/
theorem activation_cap_le (hn : PhaseThreeModel.Numeric.populationThreshold ≤ n) :
    2 * logWindow n 6 + logWindow n 16000 ≤ logWindow n 20000 := by
  obtain ⟨hL, hexp, hquad⟩ := log_facts hn
  clear hn
  set L := Real.log (n : ℝ) with hLdef
  have hnR : (2 : ℝ) ^ 57 ≤ n := by
    have hTaylor := Real.pow_div_factorial_le_exp _
      (le_trans (by norm_num) hL) 3
    norm_num [Nat.factorial] at hTaylor
    rw [hexp] at hTaylor
    have hcube := PhaseThreeModel.Numeric.logarithm_cube_lower hL
    rw [show (2 : ℝ) ^ 57 = 144115188075855872 by norm_num]
    linarith only [hTaylor, hcube, hL]
  have h6 : (logWindow n 6 : ℝ) ≤ 6 * n * L + 1 := by
    unfold logWindow
    push_cast
    exact (Nat.ceil_lt_add_one (by positivity)).le
  have h16 : (logWindow n 16000 : ℝ) ≤ 16000 * n * L + 1 := by
    unfold logWindow
    push_cast
    exact (Nat.ceil_lt_add_one (by positivity)).le
  have h20 : 20000 * (n : ℝ) * L ≤ (logWindow n 20000 : ℝ) := by
    unfold logWindow
    push_cast
    exact Nat.le_ceil _
  have hcast : ((2 * logWindow n 6 + logWindow n 16000 : ℕ) : ℝ) ≤ (logWindow n 20000 : ℝ) := by
    push_cast
    nlinarith
  exact_mod_cast hcast

/-- The fibre budget: `Q e^{0.35 - 0.05 C} + e^{-(4CQ+1)/4} + C e^{-p' · fin} ≤ 3 / n^5`. -/
theorem cap_fibre_budget (hn : PhaseThreeModel.Numeric.populationThreshold ≤ n)
    (hcard : init.card = n) (C : Finset (Fin init.card))
    (hlo : 6 * n ≤ 25 * C.card) (hCn : C.card ≤ n) :
    (clockTop n : ℝ) * Real.exp (35 / 100 - (5 / 100) * C.card) +
      Real.exp (-((4 * C.card * clockTop n + 1 : ℕ) : ℝ) / 4) +
      (C.card : ℝ) * Real.exp (-(hitRate init (halfThr C.card) * finHalfWindow n C.card)) ≤
      3 / (n : ℝ) ^ 5 := by
  obtain ⟨hL, hexp, hquad⟩ := log_facts hn
  have hH := hourIndex_le_log hn
  have e5 := exp_neg_mul_log hn 5
  have hcardR : (init.card : ℝ) = n := by exact_mod_cast hcard
  clear hn
  set L := Real.log (n : ℝ) with hLdef
  have hlo' : (6 : ℝ) * n ≤ 25 * C.card := by exact_mod_cast hlo
  have hCn' : (C.card : ℝ) ≤ n := by exact_mod_cast hCn
  have hnR : (2 : ℝ) ^ 57 ≤ n := by
    have hTaylor := Real.pow_div_factorial_le_exp _
      (le_trans (by norm_num) hL) 3
    norm_num [Nat.factorial] at hTaylor
    rw [hexp] at hTaylor
    have hcube := PhaseThreeModel.Numeric.logarithm_cube_lower hL
    rw [show (2 : ℝ) ^ 57 = 144115188075855872 by norm_num]
    linarith only [hTaylor, hcube, hL]
  have hCpos : (2 : ℝ) ≤ C.card := by nlinarith
  have hQ : (clockTop n : ℝ) ≤ 384 * L + 512 := by
    unfold clockTop
    push_cast
    nlinarith
  have hQ0 : (0 : ℝ) ≤ clockTop n := Nat.cast_nonneg _
  have hQexp : (clockTop n : ℝ) ≤ Real.exp L := by
    rw [hexp]
    nlinarith
  -- term 1
  have h1 : (clockTop n : ℝ) * Real.exp (35 / 100 - (5 / 100) * C.card) ≤ Real.exp (-(5 * L)) := by
    calc (clockTop n : ℝ) * Real.exp (35 / 100 - (5 / 100) * C.card)
        ≤ Real.exp L * Real.exp (-(6 * L)) := by
          apply mul_le_mul hQexp _ (Real.exp_nonneg _) (Real.exp_nonneg _)
          rw [Real.exp_le_exp]
          nlinarith
      _ = Real.exp (-(5 * L)) := by
          rw [← Real.exp_add]
          congr 1
          ring
  -- term 2
  have h2 : Real.exp (-((4 * C.card * clockTop n + 1 : ℕ) : ℝ) / 4) ≤ Real.exp (-(5 * L)) := by
    rw [Real.exp_le_exp]
    have hQ256 : (256 : ℝ) ≤ clockTop n := by
      unfold clockTop
      push_cast
      nlinarith [show (0 : ℝ) ≤ PhaseThreeModel.Numeric.hourIndex n from Nat.cast_nonneg _]
    push_cast
    nlinarith
  -- term 3
  have h3 : (C.card : ℝ) * Real.exp (-(hitRate init (halfThr C.card) * finHalfWindow n C.card)) ≤
      Real.exp (-(5 * L)) := by
    have hrate : 6 * L ≤ hitRate init (halfThr C.card) * finHalfWindow n C.card := by
      unfold hitRate finHalfWindow
      rw [hcardR]
      have hh : (C.card : ℝ) ≤ 2 * (halfThr C.card : ℝ) := by
        exact_mod_cast two_mul_halfThr_ge C.card
      have hf : 6 * (n : ℝ) ^ 2 * L / C.card ≤
          (Nat.ceil (6 * (n : ℝ) ^ 2 * Real.log (n : ℝ) / (C.card : ℝ)) : ℝ) := Nat.le_ceil _
      have hP : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := by nlinarith
      have hlow : (C.card : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)) ≤
          2 * (halfThr C.card : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)) :=
        div_le_div_of_nonneg_right hh hP.le
      have hkey : (C.card : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)) * (6 * (n : ℝ) ^ 2 * L / C.card) =
          6 * L * ((n : ℝ) / ((n : ℝ) - 1)) := by
        field_simp
      have hfrac : (1 : ℝ) ≤ (n : ℝ) / ((n : ℝ) - 1) := by
        rw [le_div_iff₀ (by linarith)]
        linarith
      calc 6 * L ≤ 6 * L * ((n : ℝ) / ((n : ℝ) - 1)) := by
            have : (0 : ℝ) ≤ 6 * L := by positivity
            nlinarith
        _ = _ := hkey.symm
        _ ≤ _ := mul_le_mul hlow hf (by positivity) (by positivity)
    calc (C.card : ℝ) * Real.exp (-(hitRate init (halfThr C.card) * finHalfWindow n C.card))
        ≤ Real.exp L * Real.exp (-(6 * L)) := by
          apply mul_le_mul
          · rw [hexp]; exact_mod_cast hCn
          · rw [Real.exp_le_exp]; linarith
          · exact Real.exp_nonneg _
          · exact Real.exp_nonneg _
      _ = Real.exp (-(5 * L)) := by
          rw [← Real.exp_add]
          congr 1
          ring
  push_cast at e5
  rw [e5] at h1 h2 h3
  have : (3 : ℝ) / (n : ℝ) ^ 5 = 3 * (1 / (n : ℝ) ^ 5) := by ring
  rw [this]
  linarith

theorem hitRate_half_lt_one (hn : PhaseThreeModel.Numeric.populationThreshold ≤ n)
    (hcard : init.card = n) (C : Finset (Fin init.card)) (hCn : C.card ≤ n) :
    hitRate init (halfThr C.card) < 1 := by
  unfold hitRate
  have hcardR : (init.card : ℝ) = n := by exact_mod_cast hcard
  rw [hcardR]
  obtain ⟨hL, hexp, hquad⟩ := log_facts hn
  clear hn
  have hnR : (2 : ℝ) ^ 57 ≤ n := by
    have hTaylor := Real.pow_div_factorial_le_exp _
      (le_trans (by norm_num) hL) 3
    norm_num [Nat.factorial] at hTaylor
    rw [hexp] at hTaylor
    have hcube := PhaseThreeModel.Numeric.logarithm_cube_lower hL
    rw [show (2 : ℝ) ^ 57 = 144115188075855872 by norm_num]
    linarith only [hTaylor, hcube, hL]
  have hh : (halfThr C.card : ℝ) ≤ n := by
    have := (halfThr_le C.card).trans hCn
    exact_mod_cast this
  rw [div_lt_one (by nlinarith)]
  nlinarith

end Numerics

/-! ## The fibre estimate and the headline -/

theorem fibre_tail (hinput : ThresholdEpidemic.GoodInput n init) (s T : ℕ)
    (C : Finset (Fin init.card)) :
    law init (capPrefix init s T C ∩ capBad init s T C) ≤
      ENNReal.ofReal (3 / (n : ℝ) ^ 5) * law init (capPrefix init s T C) := by
  have hn : PhaseThreeModel.Numeric.populationThreshold ≤ n :=
    (time_population_bounds hinput.1).1
  have h40 : 40 ≤ n := (time_population_bounds hinput.1).2
  have hcard : init.card = n := hinput.2.2
  have hc : 2 ≤ init.card := by omega
  by_cases hdens : 6 * n ≤ 25 * C.card ∧ C.card ≤ n ∧ s ≤ T
  · obtain ⟨hlo, hCn, hsT⟩ := hdens
    have hC6 : 6 ≤ C.card := by omega
    have hE := capPrefix_measurableSet init s T C
    set E := capPrefix init s T C with hEdef
    set N' := capHorizon init C with hN'
    have hp := hitRate_half_lt_one init hn hcard C hCn
    have hbudget := cap_fibre_budget init hn hcard C hlo hCn
    have hcm : clockMaskRate init.card C.card = clockMaskRate n C.card :=
      congrArg (fun m => clockMaskRate m C.card) hcard
    clear hn
    -- the three families
    have h1 : ∀ i ∈ Finset.range (clockTop n), law init (E ∩ halfBad init C T i N') ≤
        ENNReal.ofReal (Real.exp (35 / 100 - (5 / 100) * C.card)) * law init E :=
      fun i hi => half_level_tail init C T i hc hC6
        (by have := Finset.mem_range.mp hi; omega) N' E hE
    have h2 : law init (E ∩ thinBad init s T C) ≤
        ENNReal.ofReal (Real.exp (-((4 * C.card * clockTop n + 1 : ℕ) : ℝ) / 4)) * law init E := by
      have hmask : ∀ ω ∈ E, clockSet (labelsAt init ω s) = C := by
        intro ω hω
        rw [← virtual_eq_actual_at_seed init hω]
        exact hω.2.2.2.1
      have hppos : 0 < clockMaskRate init.card C.card := by
        rw [hcm]
        unfold clockMaskRate
        have hCpos : (2 : ℝ) ≤ C.card := by exact_mod_cast hC6.trans' (by norm_num : 2 ≤ 6)
        have hnR : (40 : ℝ) ≤ n := by exact_mod_cast h40
        apply div_pos
        · rw [Nat.cast_mul, Nat.cast_sub (by omega)]
          push_cast
          nlinarith
        · nlinarith
      have hmean : 2 * ((4 * C.card * clockTop n + 1 : ℕ) : ℝ) ≤
          clockMaskRate init.card C.card * (rawWindow n C.card : ℝ) := by
        unfold rawWindow
        rw [hcm]
        rw [hcm] at hppos
        have := Nat.le_ceil (2 * ((4 * C.card * clockTop n + 1 : ℕ) : ℝ) / clockMaskRate n C.card)
        rw [div_le_iff₀ hppos] at this
        linarith
      exact prefix_stageEvent_clockContacts_lower_tail_ennreal init hc C s T (rawWindow n C.card)
        E hE hmask _ (by positivity) hmean
    have h3 : ∀ j ∈ C, law init (E ∩ highAllBad init (halfThr C.card) s T (finHalfWindow n C.card)
        j N') ≤ ENNReal.ofReal (Real.exp (-(hitRate init (halfThr C.card) *
          finHalfWindow n C.card))) * law init E :=
      fun j _ => high_all_tail init (halfThr C.card) s T (finHalfWindow n C.card) j hc hp N' E hE
    -- the union bound
    have hunion : law init (E ∩ capBad init s T C) ≤
        (∑ i ∈ Finset.range (clockTop n), law init (E ∩ halfBad init C T i N')) +
          (law init (E ∩ thinBad init s T C) +
            ∑ j ∈ C, law init (E ∩ highAllBad init (halfThr C.card) s T (finHalfWindow n C.card)
              j N')) := by
      unfold capBad
      rw [Set.inter_union_distrib_left, Set.inter_union_distrib_left]
      refine (measure_union_le _ _).trans (add_le_add ?_ ?_)
      · rw [Set.inter_iUnion₂]
        exact measure_biUnion_finset_le _ _
      · refine (measure_union_le _ _).trans (add_le_add le_rfl ?_)
        rw [Set.inter_iUnion₂]
        exact measure_biUnion_finset_le _ _
    have hsum1 : ∑ i ∈ Finset.range (clockTop n), law init (E ∩ halfBad init C T i N') ≤
        ENNReal.ofReal ((clockTop n : ℝ) * Real.exp (35 / 100 - (5 / 100) * C.card)) *
          law init E := by
      calc ∑ i ∈ Finset.range (clockTop n), law init (E ∩ halfBad init C T i N')
          ≤ ∑ _i ∈ Finset.range (clockTop n),
              ENNReal.ofReal (Real.exp (35 / 100 - (5 / 100) * C.card)) * law init E :=
            Finset.sum_le_sum h1
        _ = ((Finset.range (clockTop n)).card : ℝ≥0∞) *
              (ENNReal.ofReal (Real.exp (35 / 100 - (5 / 100) * C.card)) * law init E) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ = _ := by
            rw [Finset.card_range, ← mul_assoc, ENNReal.ofReal_mul (Nat.cast_nonneg _),
              ENNReal.ofReal_natCast]
    have hsum3 : ∑ j ∈ C, law init (E ∩ highAllBad init (halfThr C.card) s T
        (finHalfWindow n C.card) j N') ≤
        ENNReal.ofReal ((C.card : ℝ) * Real.exp (-(hitRate init (halfThr C.card) *
          finHalfWindow n C.card))) * law init E := by
      calc ∑ j ∈ C, law init (E ∩ highAllBad init (halfThr C.card) s T (finHalfWindow n C.card) j N')
          ≤ ∑ _j ∈ C, ENNReal.ofReal (Real.exp (-(hitRate init (halfThr C.card) *
              finHalfWindow n C.card))) * law init E := Finset.sum_le_sum h3
        _ = (C.card : ℝ≥0∞) * (ENNReal.ofReal (Real.exp (-(hitRate init (halfThr C.card) *
              finHalfWindow n C.card))) * law init E) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ = _ := by
            rw [← mul_assoc, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    have ha : (0 : ℝ) ≤ (clockTop n : ℝ) * Real.exp (35 / 100 - (5 / 100) * C.card) := by
      positivity
    have hb : (0 : ℝ) ≤ Real.exp (-((4 * C.card * clockTop n + 1 : ℕ) : ℝ) / 4) :=
      Real.exp_nonneg _
    have hc' : (0 : ℝ) ≤ (C.card : ℝ) * Real.exp (-(hitRate init (halfThr C.card) *
        finHalfWindow n C.card)) := by positivity
    calc law init (E ∩ capBad init s T C)
        ≤ _ := hunion
      _ ≤ ENNReal.ofReal ((clockTop n : ℝ) * Real.exp (35 / 100 - (5 / 100) * C.card)) *
            law init E +
          (ENNReal.ofReal (Real.exp (-((4 * C.card * clockTop n + 1 : ℕ) : ℝ) / 4)) * law init E +
          ENNReal.ofReal ((C.card : ℝ) * Real.exp (-(hitRate init (halfThr C.card) *
            finHalfWindow n C.card))) * law init E) :=
          add_le_add hsum1 (add_le_add h2 hsum3)
      _ = ENNReal.ofReal ((clockTop n : ℝ) * Real.exp (35 / 100 - (5 / 100) * C.card) +
          (Real.exp (-((4 * C.card * clockTop n + 1 : ℕ) : ℝ) / 4) +
          (C.card : ℝ) * Real.exp (-(hitRate init (halfThr C.card) * finHalfWindow n C.card)))) *
            law init E := by
          rw [ENNReal.ofReal_add ha (add_nonneg hb hc'), ENNReal.ofReal_add hb hc']
          ring
      _ ≤ ENNReal.ofReal (3 / (n : ℝ) ^ 5) * law init E := by
          apply mul_le_mul_right'
          apply ENNReal.ofReal_le_ofReal
          linarith
  · have hempty : capPrefix init s T C = ∅ := by
      ext ω
      simp only [capPrefix, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨-, -, -, -, h1, h2, h3⟩
      exact hdens ⟨h1, h2, h3⟩
    rw [hempty]
    simp

/-- The guarded cap failure lies in the union of the fibre bad events. -/
theorem guardedCap_subset (hn : PhaseThreeModel.Numeric.populationThreshold ≤ n)
    (hcard : init.card = n) :
    guardedFailure init (guardCap init) (capRow init) ⊆
      ⋃ sTC : ℕ × ℕ × Finset (Fin init.card),
        capPrefix init sTC.1 sTC.2.1 sTC.2.2 ∩ capBad init sTC.1 sTC.2.1 sTC.2.2 := by
  rintro ω ⟨s, T, hs, -, hentry, ⟨hact, hpass, hshape⟩, hnot⟩
  set C := clockSet (virtualLabels init ω s) with hC
  have hdens := seed_clock_density init ω hentry
  have hle : C.card ≤ n := by
    have h : C.card ≤ init.card := seed_clock_le init ω (s := s)
    omega
  have hmem : ω ∈ capPrefix init s T C :=
    ⟨hs, hentry.seed_profile, hentry.all_first, rfl, hdens, hle, hentry.order⟩
  refine Set.mem_iUnion.mpr ⟨(s, T, C), hmem, ?_⟩
  by_cases hlevel : ∃ i ∈ Finset.range (clockTop n), ω ∈ halfBad init C T i (capHorizon init C)
  · obtain ⟨i, hi, hbad⟩ := hlevel
    exact Or.inl (Set.mem_iUnion₂.mpr ⟨i, hi, hbad⟩)
  by_cases hthin : ω ∈ thinBad init s T C
  · exact Or.inr (Or.inl hthin)
  by_cases hcoupon : ∃ j ∈ C, ω ∈ highAllBad init (halfThr C.card) s T (finHalfWindow n C.card) j
      (capHorizon init C)
  · obtain ⟨j, hj, hbad⟩ := hcoupon
    exact Or.inr (Or.inr (Set.mem_iUnion₂.mpr ⟨j, hj, hbad⟩))
  push_neg at hlevel hcoupon
  exfalso
  apply hnot
  have hC2 : 2 ≤ C.card := by
    obtain ⟨hL, -, hquad⟩ := log_facts hn
    have hn9 : 9 ≤ n := by
      have h9 : (9 : ℝ) ≤ n := by
        clear hn hcard
        nlinarith
      exact_mod_cast h9
    have hcc : C.card = clockCount (virtualLabels init ω s) := rfl
    omega
  have hcap := cap_of_good init s T ω hC hentry hpass hC2 hlevel hthin hcoupon
  have hraw := raw_fin_le hn (C := C.card) hdens hle
  have hact' := activation_cap_le hn
  have hTs : T ≤ s + activationHorizon n := hentry.deadline
  have hah : activationHorizon n = 2 * logWindow n 6 := rfl
  show RowCap init s T (virtualTimes init ω s)
  exact ⟨by omega, by omega⟩

/-- The guarded cap-row tail: the P13 row of PHASE3 §11, `3 / n^5`. -/
theorem guarded_cap_tail (hinput : ThresholdEpidemic.GoodInput n init) :
    law init (guardedFailure init (guardCap init) (capRow init)) ≤
      ENNReal.ofReal (3 / (n : ℝ) ^ 5) := by
  have hn : PhaseThreeModel.Numeric.populationThreshold ≤ n :=
    (time_population_bounds hinput.1).1
  have hcard : init.card = n := hinput.2.2
  have hdisj : Pairwise (Function.onFun Disjoint
      fun sTC : ℕ × ℕ × Finset (Fin init.card) => capPrefix init sTC.1 sTC.2.1 sTC.2.2) :=
    fun a b hab => capPrefix_disjoint init hab
  have hmeas : ∀ sTC : ℕ × ℕ × Finset (Fin init.card),
      MeasurableSet (capPrefix init sTC.1 sTC.2.1 sTC.2.2) :=
    fun sTC => (pairLogFiltration _ _).le _ _ (capPrefix_measurableSet init sTC.1 sTC.2.1 sTC.2.2)
  have hsum : ∑' sTC : ℕ × ℕ × Finset (Fin init.card),
      law init (capPrefix init sTC.1 sTC.2.1 sTC.2.2) ≤ 1 := by
    rw [← measure_iUnion hdisj hmeas]
    exact prob_le_one
  calc law init (guardedFailure init (guardCap init) (capRow init))
      ≤ law init (⋃ sTC : ℕ × ℕ × Finset (Fin init.card),
          capPrefix init sTC.1 sTC.2.1 sTC.2.2 ∩ capBad init sTC.1 sTC.2.1 sTC.2.2) :=
        measure_mono (guardedCap_subset init hn hcard)
    _ ≤ ∑' sTC : ℕ × ℕ × Finset (Fin init.card),
          law init (capPrefix init sTC.1 sTC.2.1 sTC.2.2 ∩ capBad init sTC.1 sTC.2.1 sTC.2.2) :=
        measure_iUnion_le _
    _ ≤ ∑' sTC : ℕ × ℕ × Finset (Fin init.card),
          ENNReal.ofReal (3 / (n : ℝ) ^ 5) * law init (capPrefix init sTC.1 sTC.2.1 sTC.2.2) :=
        ENNReal.tsum_le_tsum (fun sTC => fibre_tail init hinput sTC.1 sTC.2.1 sTC.2.2)
    _ = ENNReal.ofReal (3 / (n : ℝ) ^ 5) *
          ∑' sTC : ℕ × ℕ × Finset (Fin init.card), law init (capPrefix init sTC.1 sTC.2.1 sTC.2.2) :=
        ENNReal.tsum_mul_left
    _ ≤ ENNReal.ofReal (3 / (n : ℝ) ^ 5) * 1 := mul_le_mul_right hsum _
    _ = ENNReal.ofReal (3 / (n : ℝ) ^ 5) := mul_one _

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockCapDeadlineTail

end
