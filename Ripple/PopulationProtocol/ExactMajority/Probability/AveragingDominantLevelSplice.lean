-- Ripple/PopulationProtocol/ExactMajority/Probability/AveragingDominantLevelSplice.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingFixedSeedHours

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal BigOperators

namespace Ripple.PopulationProtocol.ExactMajority.AveragingDominantLevelSplice

open PhaseThreeClockProducer

open TimeTheorem PairLog PhaseOneDrain StageEventSpec
open AveragingSparseEntry AveragingEventInterface
open AveragingHourEvents AveragingHourPrefix AveragingHourStops
open AveragingObservedHourTails AveragingFixedSeedHours

variable {n : ℕ}

/-- The four inequalities selected from the seed configuration. -/
def DominantScale (init c : InputCfg n) (ell : ℕ) : Prop :=
  5 ≤ ell ∧ ell + 2 ≤ PhaseThreeModel.Numeric.hourIndex n ∧
    2 * timeMainCount c ≤ 5 * 2 ^ ell * gapMagnitude init ∧
    5 * 2 ^ ell * gapMagnitude init < 4 * timeMainCount c

open Classical in
noncomputable def selectedDominantLevel (init c : InputCfg n) : ℕ :=
  if h : ∃ ell, DominantScale init c ell then Nat.find h else 0

open Classical in
theorem selectedDominantLevel_spec (init c : InputCfg n)
    (h : ∃ ell, DominantScale init c ell) :
    DominantScale init c (selectedDominantLevel init c) := by
  rw [selectedDominantLevel, dif_pos h]
  exact Nat.find_spec h

theorem gapMagnitude_eq_zero_iff (init : InputCfg n) :
    gapMagnitude init = 0 ↔ initialGap init = 0 := by
  simp [gapMagnitude]

def selectedSign (init : InputCfg n) : Sign :=
  if 0 < initialGap init then .pos else .neg

theorem selectedSign_winning (init : InputCfg n)
    (hgap : 0 < gapMagnitude init) : winningSign init (selectedSign init) := by
  have hne : initialGap init ≠ 0 := by
    intro hz
    have := (gapMagnitude_eq_zero_iff init).2 hz
    omega
  by_cases hp : 0 < initialGap init
  · simp [selectedSign, hp, winningSign]
  · have hn : initialGap init < 0 := by omega
    simp [selectedSign, hp, winningSign, hn]

/-- The second coordinate is the last hour charged by the global failure bound.  In the tie
 branch the level is deliberately `L+5`, so `ell ≤ N+4` is false. -/
noncomputable def selectedSchedule (init c : InputCfg n) : ℕ × ℕ :=
  if gapMagnitude init = 0 then
    (PhaseThreeModel.Numeric.hourIndex n + 5,
      PhaseThreeModel.Numeric.hourIndex n)
  else
    let ell := selectedDominantLevel init c;
      (ell, ell)

def AdmissibleSchedule (p : ℕ × ℕ) : Prop :=
  5 ≤ p.1 ∧ p.2 ≤ p.1 ∧ p.2 ≤ PhaseThreeModel.Numeric.hourIndex n

theorem selectedSchedule_fibre_measurable (init : InputCfg n) (S : ℕ)
    (p : ℕ × ℕ) :
    MeasurableSet[pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256 S]
      {ω | selectedSchedule init (trace init ω S) = p} := by
  have hm : MeasurableSet
      {c : InputCfg n | selectedSchedule init c = p} :=
    (Set.to_countable _).measurableSet
  exact hm.preimage (measurable_trace_at init S)

def seedPiece (init : InputCfg n) (S : ℕ) : Set (InputLog n) :=
  {ω | S ≤ earlyHorizon n ∧ SafeSparseSeed init ω S}

theorem seedPiece_measurable (init : InputCfg n) (S : ℕ) :
    MeasurableSet[pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256 S]
      (seedPiece init S) := by
  by_cases hS : S ≤ earlyHorizon n
  · simpa only [seedPiece, Set.mem_setOf_eq, hS, true_and] using
      safeSparseSeed_past init S
  · have he : seedPiece init S = ∅ := by
      ext ω
      simp [seedPiece, hS]
    rw [he]
    exact MeasurableSpace.measurableSet_empty _

open Classical in
def scheduledHourFailure (init : InputCfg n) (S : ℕ)
    (p : ℕ × ℕ) : Set (InputLog n) :=
  if AdmissibleSchedule (n := n) p then
    ClockScope init S p.1 p.2 (selectedSign init) ∩
      hourFailure
        (hourSuccess init (seedTime init 3) p.1 (selectedSign init)) p.2
  else ∅

/-- Fixed genuine seed, but random seed-measurable level and last hour. -/
theorem fixed_seed_selected_hour_tail
    (init : InputCfg n) (hvalid : validInitial init) (hcard : init.card = n)
    (hn : timePopulationThreshold ≤ n) (S : ℕ) :
    law init (seedPiece init S ∩
      {ω | ω ∈ scheduledHourFailure init S
        (selectedSchedule init (trace init ω S))}) ≤
      5 * (PhaseThreeModel.Numeric.hourIndex n : ℝ≥0∞) * hourError n *
        law init (seedPiece init S) := by
  let f : InputLog n → ℕ × ℕ :=
    fun ω => selectedSchedule init (trace init ω S)
  let B : ℕ × ℕ → Set (InputLog n) := scheduledHourFailure init S
  apply observable_partition_bound (law init) (seedPiece init S)
    ((pairLogFiltration _ _).le S _ (seedPiece_measurable init S)) f
    (fun p => (pairLogFiltration _ _).le S _
      (selectedSchedule_fibre_measurable init S p)) B
    (5 * (PhaseThreeModel.Numeric.hourIndex n : ℝ≥0∞) * hourError n)
  intro p
  by_cases hp : AdmissibleSchedule (n := n) p
  · let E := seedPiece init S ∩ {ω | f ω = p}
    have hE :
        MeasurableSet[pairLogFiltration
          (PhaseThreeModel.Numeric.hourIndex n) 256 S] E :=
      (seedPiece_measurable init S).inter
        (selectedSchedule_fibre_measurable init S p)
    have hs : ∀ ω ∈ E, SafeSparseSeed init ω S := by
      intro ω hω
      exact hω.1.2
    have ht := fixed_seed_hour_failure_tail init hvalid hcard hn
      S p.1 p.2 (selectedSign init) hp.1 hp.2.1 hp.2.2 E hE hs
    have he :
        ((seedPiece init S ∩ {ω | f ω = p}) ∩ B p) =
          ((E ∩ ClockScope init S p.1 p.2 (selectedSign init)) ∩
            hourFailure
              (hourSuccess init (seedTime init 3) p.1 (selectedSign init)) p.2) := by
      ext ω
      simp only [E, B, scheduledHourFailure, hp, if_pos,
        Set.mem_inter_iff, Set.mem_setOf_eq]
      clear * -
      tauto
    rw [he]
    calc
      _ ≤ 5 * (p.2 : ℝ≥0∞) * hourError n * law init E := ht
      _ ≤ 5 * (PhaseThreeModel.Numeric.hourIndex n : ℝ≥0∞) *
          hourError n * law init E := by
        gcongr
        exact_mod_cast hp.2.2
  · simp [B, scheduledHourFailure, hp]

private theorem weighted_past_fibres {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (E : Set Ω) (τ : Ω → WithTop ℕ)
    (P B : ℕ → Set Ω) (ε : ℝ≥0∞)
    (hP : ∀ s, MeasurableSet (P s))
    (hsub : ∀ s, P s ⊆ E ∩ {ω | τ ω = (s : WithTop ℕ)})
    (ht : ∀ s, μ (P s ∩ B s) ≤ ε * μ (P s)) :
    μ (⋃ s, P s ∩ B s) ≤ ε * μ E := by
  have hd : Pairwise fun s t => Disjoint (P s) (P t) := by
    intro s t hst
    apply Set.disjoint_left.mpr
    intro ω hs ht'
    exact hst (WithTop.coe_injective
      ((hsub s hs).2.symm.trans (hsub t ht').2))
  have hu : (⋃ s, P s) ⊆ E := by
    intro ω hω
    obtain ⟨s, hs⟩ := Set.mem_iUnion.mp hω
    exact (hsub s hs).1
  calc
    μ (⋃ s, P s ∩ B s) ≤ ∑' s, μ (P s ∩ B s) := measure_iUnion_le _
    _ ≤ ∑' s, ε * μ (P s) := ENNReal.tsum_le_tsum ht
    _ = ε * μ (⋃ s, P s) := by
      rw [ENNReal.tsum_mul_left, ← measure_iUnion hd hP]
    _ ≤ ε * μ E := mul_le_mul_left' (measure_mono hu) ε

def globalHourFailure (init : InputCfg n) : Set (InputLog n) :=
  ⋃ S, seedPiece init S ∩
    {ω | ω ∈ scheduledHourFailure init S
      (selectedSchedule init (trace init ω S))}

/-- The union is literally finite: only `S ≤ earlyHorizon n` and
 `ell ≤ L+5` can contribute. -/
theorem globalHourFailure_finite (init : InputCfg n) :
    globalHourFailure init =
      ⋃ S : Fin (earlyHorizon n + 1),
        ⋃ ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 6),
          (seedPiece init S.val ∩
            {ω | (selectedSchedule init (trace init ω S.val)).1 = ell.val}) ∩
          {ω | ω ∈ scheduledHourFailure init S.val
            (selectedSchedule init (trace init ω S.val))} := by
  ext ω
  constructor
  · intro hω
    obtain ⟨S, hS, hbad⟩ := Set.mem_iUnion.mp hω
    have hS1 : S ≤ earlyHorizon n := hS.1
    have hSh : S < earlyHorizon n + 1 := by omega
    let p := selectedSchedule init (trace init ω S)
    have hadm : AdmissibleSchedule (n := n) p := by
      by_contra hnot
      simpa [scheduledHourFailure, p, hnot] using hbad
    have hell : p.1 < PhaseThreeModel.Numeric.hourIndex n + 6 := by
      by_cases hz : gapMagnitude init = 0
      · simp [p, selectedSchedule, hz]
      · have hp1 : p = (selectedDominantLevel init (trace init ω S),
            selectedDominantLevel init (trace init ω S)) := by
          simp only [p, selectedSchedule, hz, ↓reduceIte]
        have h2 := hadm.2.2
        rw [hp1] at h2 ⊢
        exact Nat.lt_of_le_of_lt h2 (Nat.lt_add_of_pos_right (by omega))
    apply Set.mem_iUnion.mpr
    refine ⟨⟨S, hSh⟩, ?_⟩
    apply Set.mem_iUnion.mpr
    refine ⟨⟨p.1, hell⟩, ?_⟩
    exact ⟨⟨hS, rfl⟩, hbad⟩
  · intro hω
    obtain ⟨S, hω⟩ := Set.mem_iUnion.mp hω
    obtain ⟨ell, hpiece, hbad⟩ := Set.mem_iUnion.mp hω
    exact Set.mem_iUnion.mpr ⟨S.val, hpiece.1, hbad⟩

/-- No factor for the possible seed times or selected levels. -/
theorem global_hour_failure_tail
    (init : InputCfg n) (hvalid : validInitial init) (hcard : init.card = n)
    (hn : timePopulationThreshold ≤ n) :
    law init (globalHourFailure init) ≤
      5 * (PhaseThreeModel.Numeric.hourIndex n : ℝ≥0∞) * hourError n := by
  let P : ℕ → Set (InputLog n) := seedPiece init
  let B : ℕ → Set (InputLog n) := fun S =>
    {ω | ω ∈ scheduledHourFailure init S
      (selectedSchedule init (trace init ω S))}
  have ht := weighted_past_fibres (law init) Set.univ (seedTime init 3)
    P B (5 * (PhaseThreeModel.Numeric.hourIndex n : ℝ≥0∞) * hourError n)
    (fun S => (pairLogFiltration _ _).le S _ (seedPiece_measurable init S))
    (fun S ω hω => ⟨Set.mem_univ ω,
      (seedTime_eq_iff init 3 ω S).2 hω.2.1⟩)
    (fun S => fixed_seed_selected_hour_tail init hvalid hcard hn S)
  simpa only [globalHourFailure, P, B, measure_univ, mul_one] using ht

/-- The tie schedule is admissible and lies in the scope of the global failure bound. -/
theorem tie_schedule_scope
    {init : InputCfg n} {ω : InputLog n} {S T ρ : ℕ}
    {w : ClockTimes init} (h : ClockHistory init ω S T ρ w)
    (hgap : initialGap init = 0) :
    let p := selectedSchedule init (trace init ω S);
      AdmissibleSchedule (n := n) p ∧
      ω ∈ ClockScope init S p.1 p.2 (selectedSign init) := by
  have hz : gapMagnitude init = 0 := (gapMagnitude_eq_zero_iff init).2 hgap
  have hST := clockHistory_seed_lt_exit h
  have hM : 0 < timeMainCount (trace init ω S) := by
    have hd := (h.density S le_rfl (lt_of_le_of_lt hST.1 hST.2)).1
    have hn : 0 < n := by
      have h2 := h.entry.seed_profile.exactly_two
      have hc := h.entry.seed_profile.card_eq
      have hle := Multiset.countP_le_card (fun a => a.phase.val = 3) (trace init ω S)
      rw [h2] at hle
      omega
    omega
  simp only [selectedSchedule, hz, ↓reduceIte]
  constructor
  · unfold AdmissibleSchedule
    refine ⟨?_, ?_, ?_⟩ <;> (try dsimp only) <;> omega
  · refine ⟨T, ρ, w, h, ?_, ?_⟩
    · simp only [hz, mul_zero]
      omega
    · intro himpossible
      exact absurd himpossible (by omega)

/-- The strict-small-gap schedule is the seed-measurable selected scale. -/
theorem strict_schedule_scope
    {init : InputCfg n} {ω : InputLog n} {S T ρ : ℕ}
    {w : ClockTimes init} (h : ClockHistory init ω S T ρ w)
    (hgap : 0 < gapMagnitude init)
    (hsmall : 40 * gapMagnitude init < timeMainCount (trace init ω S)) :
    let p := selectedSchedule init (trace init ω S);
      DominantScale init (trace init ω S) p.1 ∧ p.2 = p.1 ∧
      AdmissibleSchedule (n := n) p ∧
      ω ∈ ClockScope init S p.1 p.2 (selectedSign init) := by
  have hex := small_gap_scale_of_clockHistory h hgap hsmall
  have hs := selectedDominantLevel_spec init (trace init ω S) hex
  have hz : gapMagnitude init ≠ 0 := by omega
  simp only [selectedSchedule, hz, ↓reduceIte]
  refine ⟨hs, trivial, ⟨hs.1, le_rfl, by have := hs.2.1; omega⟩, ?_⟩
  refine ⟨T, ρ, w, h, hs.2.2.2, ?_⟩
  intro _
  exact ⟨selectedSign_winning init hgap, hs.2.2.1⟩

end Ripple.PopulationProtocol.ExactMajority.AveragingDominantLevelSplice

end
