-- Ripple/PopulationProtocol/ExactMajority/Probability/AveragingGlobalFailureSplice.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingTerminalPackages

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal BigOperators

namespace Ripple.PopulationProtocol.ExactMajority.AveragingGlobalFailureSplice

open PhaseThreeClockProducer

open TimeTheorem PairLog PhaseOneDrain StageEventSpec
open AveragingSparseEntry AveragingEventInterface
open AveragingDominantLevelSplice AveragingTerminalPackages
open AveragingHourEvents AveragingHourPrefix AveragingHourStops
open AveragingObservedHourTails AveragingFixedSeedHours
open AveragingTerminalDebtDeadlines AveragingProtectedCap AveragingNumerics
open AveragingIntegerPotential AveragingTerminalDebt AveragingTieReadout

variable {n : ℕ}

private theorem weighted_fibres {Ω : Type*} [MeasurableSpace Ω]
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
    rintro ω hω
    obtain ⟨s, hs⟩ := Set.mem_iUnion.mp hω
    exact (hsub s hs).1
  calc
    μ (⋃ s, P s ∩ B s) ≤ ∑' s, μ (P s ∩ B s) := measure_iUnion_le _
    _ ≤ ∑' s, ε * μ (P s) := ENNReal.tsum_le_tsum ht
    _ = ε * μ (⋃ s, P s) := by
      rw [ENNReal.tsum_mul_left, ← measure_iUnion hd hP]
    _ ≤ ε * μ E := mul_le_mul_left' (measure_mono hu) ε

/-- Prefix-preserving form of the two terminal drains. -/
theorem terminal_two_drains_on_observed
    (init : InputCfg n) (E : Set (InputLog n)) (S ell C M : ℕ)
    (hE : MeasurableSet[pairLogFiltration
      (PhaseThreeModel.Numeric.hourIndex n) 256 S] E)
    (hseed : ∀ ω ∈ E, SafeSparseSeed init ω S)
    (hn : timePopulationThreshold ≤ n)
    (hell : ell + 2 ≤ PhaseThreeModel.Numeric.hourIndex n)
    (hC : 0 < C) (hM : 0 < M) (hroles : C + M ≤ n)
    (hmainlo : 12 * n ≤ 25 * M) (hmainhi : 25 * M ≤ 13 * n) :
    let τ := hourStart init (seedTime init 3) (ell + 2);
      law init (E ∩ {ω | ∃ s : ℕ, τ ω = (s : WithTop ℕ) ∧
      ω ∈ terminalFailure init s (selectedSign init) ell
        ((2 / 125 : ℚ) * M) n C M}) ≤
      (2 * hourError n) * law init E := by
  intro τ
  let Bad : ℕ → Set (InputLog n) := fun s =>
    terminalFailure init s (selectedSign init) ell
      ((2 / 125 : ℚ) * M) n C M
  let P : ℕ → Set (InputLog n) := fun s => E ∩ {ω | τ ω = (s : WithTop ℕ)}
  have hτ := hourStart_phaseThreeSeed_pastTime init (ell + 2)
  have hn3 : 3 ≤ n := by
    have := (time_population_bounds hn).2
    omega
  have hPm (s : ℕ) : MeasurableSet[pairLogFiltration
      (PhaseThreeModel.Numeric.hourIndex n) 256 s] (P s) := by
    by_cases hSs : S ≤ s
    · exact (((pairLogFiltration _ _).mono hSs _ hE).inter (hτ s))
    · have hempty : P s = ∅ := by
        ext ω
        simp only [P, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false]
        constructor
        · rintro ⟨he, ht⟩
          have hs := (seedTime_eq_iff init 3 ω S).2 (hseed ω he).1
          have hstart := hourStart_le_iff_of_seed init (seedTime init 3)
            (ell + 2) ω S s hs
          have : S ≤ s := by
            obtain ⟨v, hv, _⟩ := hstart.mp ht.le
            exact hv.1.trans hv.2
          exact (hSs this).elim
        · exact fun hf => hf.elim
      rw [hempty]
      exact MeasurableSpace.measurableSet_empty _
  have hlocal (s : ℕ) :
      law init (P s ∩ Bad s) ≤ (2 * hourError n) * law init (P s) := by
    have hPs := hPm s
    rw [pairLogFiltration_eq_comap] at hPs
    obtain ⟨A, hAm, hA⟩ := hPs
    have hp : {ω | frestrictLe (π := fun _ : ℕ =>
        Draw (PhaseThreeModel.Numeric.hourIndex n) 256) s ω ∈ A} = P s := hA
    have ht := terminal_two_drains_from init s A (selectedSign init) ell hell
      ((2 / 125 : ℚ) * M) n C M hn3 hC hM hroles hmainhi
      (by nlinarith)
    have hs1 := ENNReal.ofReal_le_ofReal
      (faster_mass_tail_le_inverse_power hn hmainlo
        (by norm_num : (0 : ℝ) < 500) (by norm_num : (500 : ℝ) ≤ 1000))
    have hs2 := ENNReal.ofReal_le_ofReal
      (faster_mass_tail_le_inverse_power hn hmainlo
        (by norm_num : (0 : ℝ) < 600) (by norm_num : (600 : ℝ) ≤ 1000))
    have hsum :
        ENNReal.ofReal (Real.exp (-(M : ℝ) / 500)) +
          ENNReal.ofReal (Real.exp (-(M : ℝ) / 600)) ≤
        2 * hourError n := by
      unfold hourError
      calc
        _ ≤ ENNReal.ofReal (1 / (n : ℝ) ^ 20) +
            ENNReal.ofReal (1 / (n : ℝ) ^ 20) := add_le_add hs1 hs2
        _ = 2 * ENNReal.ofReal (1 / (n : ℝ) ^ 20) := by ring
    have hmul := ht.trans (mul_le_mul_right' hsum
      (law init {ω | frestrictLe (π := fun _ : ℕ =>
        Draw (PhaseThreeModel.Numeric.hourIndex n) 256) s ω ∈ A}))
    have hset : {ω | frestrictLe (π := fun _ : ℕ =>
        Draw (PhaseThreeModel.Numeric.hourIndex n) 256) s ω ∈ A ∧
          ω ∈ terminalFailure init s (selectedSign init) ell
            ((2 / 125 : ℚ) * M) n C M} = P s ∩ Bad s := by
      ext ω
      have h1 := Set.ext_iff.mp hp ω
      constructor
      · rintro ⟨h2, h3⟩
        exact ⟨h1.mp h2, h3⟩
      · rintro ⟨h2, h3⟩
        exact ⟨h1.mpr h2, h3⟩
    rw [hset, hp] at hmul
    exact hmul
  have hs := weighted_fibres (law init) E τ P Bad (2 * hourError n)
    (fun s => (pairLogFiltration _ _).le s _ (hPm s))
    (fun s ω hω => ⟨hω.1, hω.2⟩) hlocal
  have he : E ∩ {ω | ∃ s : ℕ, τ ω = (s : WithTop ℕ) ∧ ω ∈ Bad s} =
      ⋃ s, P s ∩ Bad s := by
    ext ω
    constructor
    · rintro ⟨hE', s, hs', hb⟩
      exact Set.mem_iUnion.mpr ⟨s, ⟨hE', hs'⟩, hb⟩
    · intro hω
      obtain ⟨s, ⟨hE', hs'⟩, hb⟩ := Set.mem_iUnion.mp hω
      exact ⟨hE', s, hs', hb⟩
  rw [he]
  exact hs

/-- All random seed counts are selected at the genuine seed; the local drain
 bound is therefore averaged without a count factor. -/
def globalTerminalFailure (init : InputCfg n) : Set (InputLog n) :=
  ⋃ S, seedPiece init S ∩ {ω |
    let p := selectedSchedule init (trace init ω S)
    let counts := seedCounts init S ω
      ∃ s : ℕ, hourStart init (seedTime init 3) (p.1 + 2) ω = (s : WithTop ℕ) ∧
      ω ∈ terminalFailure init s (selectedSign init) p.1
        ((2 / 125 : ℚ) * counts.2) n counts.1 counts.2}

private theorem seedCounts_main_upper (init : InputCfg n) (S : ℕ) (ω : InputLog n)
    (hp : SeedProfile n init (trace init ω S)) :
    25 * (seedCounts init S ω).2 ≤ 13 * n := by
  have hm := hp.role_good.2.2.1
  change (RoleSplitConcentration.mainCount (trace init ω S) : ℝ) ≤
    (1 + (1 / 25 : ℝ)) * (n : ℝ) / 2 at hm
  have hmEq : RoleSplitConcentration.mainCount (trace init ω S) =
      timeMainCount (trace init ω S) := by
    simp only [RoleSplitConcentration.mainCount, timeMainCount,
      AveragingEventInterface.countP_classical]
  rw [hmEq] at hm
  have h : (25 : ℝ) * (timeMainCount (trace init ω S) : ℝ) ≤ 13 * (n : ℝ) := by
    linarith
  exact_mod_cast h

private theorem hourStart_top_of_large (init : InputCfg n) (S h : ℕ)
    (ω : InputLog n) (hseed : seedTime init 3 ω = (S : WithTop ℕ))
    (hC : 0 < clockCount (trace init ω S))
    (hh : PhaseThreeModel.Numeric.hourIndex n + 2 ≤ h) (s : ℕ) :
    hourStart init (seedTime init 3) h ω ≠ (s : WithTop ℕ) := by
  intro heq
  have hle : hourStart init (seedTime init 3) h ω ≤ (s : WithTop ℕ) := heq.le
  obtain ⟨v, _, hv⟩ := (hourStart_le_iff_of_seed init (seedTime init 3) h ω S s hseed).mp hle
  have hh0 : h ≠ 0 := by omega
  unfold HourReached at hv
  rw [if_neg hh0] at hv
  have hzero : StageEventSpec.frontCount init ω S v (256 * h) = 0 := by
    unfold StageEventSpec.frontCount labelCount
    rw [Finset.card_eq_zero]
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
      iff_false]
    intro hi
    have h1 := hi.2
    unfold StageEventSpec.effectiveMinute at h1
    split_ifs at h1 with hact
    · have h2 := (PairLog.labelsAt init ω v i).minute.isLt
      omega
    · omega
  have hpos : 0 < highThreshold (clockCount (trace init ω S)) := by
    unfold highThreshold
    apply Nat.ceil_pos.mpr
    have : (0 : ℝ) < (clockCount (trace init ω S) : ℝ) := by exact_mod_cast hC
    positivity
  rw [hzero] at hv
  omega

theorem global_terminal_failure_tail
    (init : InputCfg n) (hvalid : validInitial init) (hcard : init.card = n)
    (hn : timePopulationThreshold ≤ n) :
    law init (globalTerminalFailure init) ≤ 2 * hourError n := by
  let P : ℕ → Set (InputLog n) := seedPiece init
  let B : ℕ → Set (InputLog n) := fun S => {ω |
    let p := selectedSchedule init (trace init ω S)
    let counts := seedCounts init S ω
      ∃ s : ℕ, hourStart init (seedTime init 3) (p.1 + 2) ω = (s : WithTop ℕ) ∧
      ω ∈ terminalFailure init s (selectedSign init) p.1
        ((2 / 125 : ℚ) * counts.2) n counts.1 counts.2}
  have hnpos : 0 < n := by have := (time_population_bounds hn).2; omega
  have hL2 : 2 ≤ PhaseThreeModel.Numeric.hourIndex n := by
    have h1 := (time_hour_calibration hn).2.2.1
    have h2 := (time_hour_calibration hn).2.2.2.1
    unfold PhaseThreeModel.Numeric.clockHours at h2
    have h3 : (6 : ℝ) ≤ ((PhaseThreeModel.Numeric.hourIndex n + 1 : ℕ) : ℝ) :=
      h1.trans h2
    have h4 : 6 ≤ PhaseThreeModel.Numeric.hourIndex n + 1 := by exact_mod_cast h3
    omega
  have hfixed (S : ℕ) : law init (P S ∩ B S) ≤
      (2 * hourError n) * law init (P S) := by
    let f : InputLog n → (ℕ × ℕ) × (ℕ × ℕ) := fun ω =>
      (selectedSchedule init (trace init ω S), seedCounts init S ω)
    have hfib : ∀ z : (ℕ × ℕ) × (ℕ × ℕ), {ω | f ω = z} =
        {ω | selectedSchedule init (trace init ω S) = z.1} ∩
          {ω | seedCounts init S ω = z.2} := by
      intro z
      ext ω
      simp only [f, Set.mem_setOf_eq, Set.mem_inter_iff, Prod.ext_iff]
    have hfm (z : (ℕ × ℕ) × (ℕ × ℕ)) :
        MeasurableSet[pairLogFiltration
          (PhaseThreeModel.Numeric.hourIndex n) 256 S] {ω | f ω = z} := by
      rw [hfib z]
      exact (selectedSchedule_fibre_measurable init S z.1).inter
        (seedCounts_fibre_measurable init S S le_rfl z.2)
    apply observable_partition_bound (law init) (P S)
      ((pairLogFiltration _ _).le S _ (seedPiece_measurable init S)) f
      (fun z => (pairLogFiltration _ _).le S _ (hfm z))
      (fun z => {ω | ∃ s : ℕ,
        hourStart init (seedTime init 3) (z.1.1 + 2) ω = (s : WithTop ℕ) ∧
        ω ∈ terminalFailure init s (selectedSign init) z.1.1
          ((2 / 125 : ℚ) * z.2.2) n z.2.1 z.2.2})
      (2 * hourError n)
    intro z
    let E := P S ∩ {ω | f ω = z}
    have hE : MeasurableSet[pairLogFiltration
        (PhaseThreeModel.Numeric.hourIndex n) 256 S] E :=
      (seedPiece_measurable init S).inter (hfm z)
    have hs : ∀ ω ∈ E, SafeSparseSeed init ω S := fun ω hω => hω.1.2
    by_cases hne : E.Nonempty
    · obtain ⟨ω, hω⟩ := hne
      have hfz : f ω = z := hω.2
      have hz1 : selectedSchedule init (trace init ω S) = z.1 :=
        (Prod.ext_iff.mp hfz).1
      have hz2 : seedCounts init S ω = z.2 := (Prod.ext_iff.mp hfz).2
      have hprof : SeedProfile n init (trace init ω S) := (hs ω hω).2.1
      have hb := seedCounts_bounds init S ω hnpos hprof
      rw [hz2] at hb
      have hmainhi : 25 * z.2.2 ≤ 13 * n := by
        have := seedCounts_main_upper init S ω hprof
        rwa [hz2] at this
      have hcases : (gapMagnitude init = 0 ∧ z.1.1 = PhaseThreeModel.Numeric.hourIndex n + 5) ∨
          z.1.1 + 2 ≤ PhaseThreeModel.Numeric.hourIndex n := by
        by_cases hz : gapMagnitude init = 0
        · left
          refine ⟨hz, ?_⟩
          rw [← hz1]
          simp only [selectedSchedule, hz, ↓reduceIte]
        · right
          rw [← hz1]
          simp only [selectedSchedule, hz, ↓reduceIte]
          by_cases hex : ∃ ell, DominantScale init (trace init ω S) ell
          · exact (selectedDominantLevel_spec init (trace init ω S) hex).2.1
          · have h0 : selectedDominantLevel init (trace init ω S) = 0 := by
              unfold selectedDominantLevel
              rw [dif_neg hex]
            rw [h0]
            omega
      rcases hcases with ⟨_, hz1L⟩ | hell
      · -- the hour index exceeds the clock range: the terminal event is empty
        have hempty : E ∩ {ω | ∃ s : ℕ,
            hourStart init (seedTime init 3) (z.1.1 + 2) ω = (s : WithTop ℕ) ∧
            ω ∈ terminalFailure init s (selectedSign init) z.1.1
              ((2 / 125 : ℚ) * z.2.2) n z.2.1 z.2.2} = ∅ := by
          ext ω'
          simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false,
            iff_false]
          rintro ⟨hω', s, hs', _⟩
          have hseed' := (seedTime_eq_iff init 3 ω' S).2 (hs ω' hω').1
          have hprof' : SeedProfile n init (trace init ω' S) := (hs ω' hω').2.1
          have hC' : 0 < clockCount (trace init ω' S) :=
            (seedCounts_bounds init S ω' hnpos hprof').1
          exact hourStart_top_of_large init S _ ω' hseed' hC' (by omega) s hs'
        show law init (E ∩ {ω | ∃ s : ℕ,
            hourStart init (seedTime init 3) (z.1.1 + 2) ω = (s : WithTop ℕ) ∧
            ω ∈ terminalFailure init s (selectedSign init) z.1.1
              ((2 / 125 : ℚ) * z.2.2) n z.2.1 z.2.2}) ≤ _
        rw [hempty]
        simp
      · have hmain := terminal_two_drains_on_observed init E S z.1.1 z.2.1 z.2.2 hE hs
          hn hell hb.1 (by have := hb.2.1; omega) hb.2.2 hb.2.1 hmainhi
        exact hmain
    · have hE0 : E = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
      show law init (E ∩ {ω | ∃ s : ℕ,
            hourStart init (seedTime init 3) (z.1.1 + 2) ω = (s : WithTop ℕ) ∧
            ω ∈ terminalFailure init s (selectedSign init) z.1.1
              ((2 / 125 : ℚ) * z.2.2) n z.2.1 z.2.2}) ≤ _
      rw [hE0]
      simp
  have hτ := seedTime_pastTime init 3
  have hs := weighted_fibres (law init) Set.univ (seedTime init 3) P B
    (2 * hourError n)
    (fun S => (pairLogFiltration _ _).le S _ (seedPiece_measurable init S))
    (fun S ω hω => ⟨Set.mem_univ ω,
      (seedTime_eq_iff init 3 ω S).2 hω.2.1⟩) hfixed
  simpa only [globalTerminalFailure, P, B, measure_univ, mul_one] using hs

/-- The protected-cap bad event already contains the produced package, so the
 existing stopped drift theorem applies under the unchanged path law. -/
def globalCapFailure (init : InputCfg n) : Set (InputLog n) :=
  {ω | ∃ S T ρ, ∃ w : ClockTimes init,
    ClockHistory init ω S T ρ w ∧
    capTime init (seedTime init 3) ω = (w.cap : WithTop ℕ) ∧
    initialGap init = 0 ∧
    let M := timeMainCount (trace init ω S);
      1000 * augmentedPhiNat (PhaseThreeModel.Numeric.hourIndex n)
      (trace init ω w.cap) ≤ M ∧
    (∀ v, w.cap ≤ v → v < w.cap + logWindow n 16 →
      CapGate n M (PhaseThreeModel.Numeric.hourIndex n) (trace init ω v)) ∧
    ¬ tieReadout init (trace init ω ρ)}

/-- Drift failure at a stopping time `τ`, with the main count and the cap gate
read from the configuration at the start `s = τ ω` (the main count is constant
on the whole clock window, so this is the main count at the genuine seed). -/
def capSplicedFailure (init : InputCfg n) (τ : InputLog n → WithTop ℕ) :
    Set (InputLog n) :=
  {ω | ∃ s : ℕ, τ ω = (s : WithTop ℕ) ∧
    12 * n ≤ 25 * timeMainCount (trace init ω s) ∧
    timeMainCount (trace init ω s) ≤ n ∧
    augmentedPhiNat (PhaseThreeModel.Numeric.hourIndex n) (trace init ω s) ≤
      timeMainCount (trace init ω s) / 1000 ∧
    (∀ u, s ≤ u → u < s + logWindow n 16 →
      CapGate n (timeMainCount (trace init ω s))
        (PhaseThreeModel.Numeric.hourIndex n) (trace init ω u)) ∧
    1 ≤ augmentedPhiNat (PhaseThreeModel.Numeric.hourIndex n)
      (trace init ω (s + logWindow n 16))}

/-- Lemma `measure_iUnion_seedMainCount_bound`: the cap drift tail splices over the
start time and, inside each start-time fibre, over the main count, with the
prefix-weighted per-count bound `TraceDrain.potential_drift_tail_from`. -/
theorem cap_spliced_failure_tail (init : InputCfg n)
    (hn : timePopulationThreshold ≤ n)
    (τ : InputLog n → WithTop ℕ) (hτ : PairLogPastTime τ) :
    law init (capSplicedFailure init τ) ≤ ENNReal.ofReal (1 / (n : ℝ) ^ 4) := by
  classical
  have hL1 := cap_index_pos hn
  have hn2 : 2 ≤ n := by
    have := (time_population_bounds hn).2
    omega
  refine PhaseThreeClockProducer.splice_of_local (law init) τ
    (capSplicedFailure init τ) _
    (fun s => (pairLogFiltration _ _).le s _ (hτ s)) ?_ ?_
  · rintro ω ⟨s, hs, -⟩
    rw [hs]
    exact WithTop.coe_ne_top
  · intro s
    have hτs := hτ s
    let E : Set (InputLog n) := {ω | τ ω = (s : WithTop ℕ)}
    have hEm : MeasurableSet E := (pairLogFiltration _ _).le s _ hτs
    let f : InputLog n → ℕ := fun ω => timeMainCount (trace init ω s)
    have hfm (M : ℕ) : MeasurableSet {ω | f ω = M} := by
      have hm : MeasurableSet {c : InputCfg n | timeMainCount c = M} :=
        (Set.to_countable _).measurableSet
      exact (pairLogFiltration _ _).le s _ (hm.preimage (measurable_trace_at init s))
    let ψ : InputCfg n → ℕ :=
      augmentedPhiNat (PhaseThreeModel.Numeric.hourIndex n)
    let Bset : ℕ → Set (InputLog n) := fun M =>
      {ω | 12 * n ≤ 25 * M ∧ M ≤ n ∧ ψ (trace init ω s) ≤ M / 1000 ∧
        (∀ u, s ≤ u → u < s + logWindow n 16 →
          CapGate n M (PhaseThreeModel.Numeric.hourIndex n) (trace init ω u)) ∧
        1 ≤ ψ (trace init ω (s + logWindow n 16))}
    have hpart := observable_partition_bound (law init) E hEm f hfm Bset
      (ENNReal.ofReal (1 / (n : ℝ) ^ 4)) (by
        intro M
        by_cases hM : 12 * n ≤ 25 * M ∧ M ≤ n
        · have hτs' := hτs
          rw [pairLogFiltration_eq_comap] at hτs'
          obtain ⟨Aσ, -, hAσ⟩ := hτs'
          have hmem (ω : InputLog n) :
              frestrictLe (π := fun _ : ℕ =>
                Draw (PhaseThreeModel.Numeric.hourIndex n) 256) s ω ∈ Aσ ↔
                τ ω = (s : WithTop ℕ) := by
            change ω ∈ frestrictLe (π := fun _ : ℕ =>
                Draw (PhaseThreeModel.Numeric.hourIndex n) 256) s ⁻¹' Aσ ↔
              ω ∈ {ω | τ ω = (s : WithTop ℕ)}
            rw [hAσ]
          let A : Set ((k : Finset.Iic s) →
              Draw (PhaseThreeModel.Numeric.hourIndex n) 256) :=
            {p | p ∈ Aσ ∧ timeMainCount (prefixCfg init s p) = M ∧
              ψ (prefixCfg init s p) ≤ M / 1000}
          have hdrift : ∀ c, CapGate n M (PhaseThreeModel.Numeric.hourIndex n) c →
              ∫⁻ c', (ψ c' : ℝ≥0∞)
                  ∂(NonuniformMajority (PhaseThreeModel.Numeric.hourIndex n)
                    256).transitionKernel c ≤
                (1 - ENNReal.ofReal (capRate n M)) * ψ c :=
            fun c hc => cap_kernel_drift hn2 hL1 c hc
          have hmain := TraceDrain.potential_drift_tail_from init ψ
            (CapGate n M (PhaseThreeModel.Numeric.hourIndex n))
            (ENNReal.ofReal (capRate n M)) hdrift s (logWindow n 16) A (M / 1000)
            (fun _ hp => hp.2.2)
          have hsub1 : (E ∩ {ω | f ω = M}) ∩ Bset M ⊆
              {ω | frestrictLe (π := fun _ : ℕ =>
                  Draw (PhaseThreeModel.Numeric.hourIndex n) 256) s ω ∈ A ∧
                (∀ u, s ≤ u → u < s + logWindow n 16 →
                  CapGate n M (PhaseThreeModel.Numeric.hourIndex n)
                    (trace init ω u)) ∧
                1 ≤ ψ (trace init ω (s + logWindow n 16))} := by
            rintro ω ⟨⟨hωE, hfM⟩, _, _, hψ, hwin, hfin⟩
            exact ⟨⟨(hmem ω).mpr hωE, hfM, hψ⟩, hwin, hfin⟩
          have hsub2 : {ω | frestrictLe (π := fun _ : ℕ =>
                Draw (PhaseThreeModel.Numeric.hourIndex n) 256) s ω ∈ A} ⊆
              E ∩ {ω | f ω = M} := by
            intro ω hω
            exact ⟨(hmem ω).mp hω.1, hω.2.1⟩
          calc
            law init ((E ∩ {ω | f ω = M}) ∩ Bset M)
                ≤ law init {ω | frestrictLe (π := fun _ : ℕ =>
                    Draw (PhaseThreeModel.Numeric.hourIndex n) 256) s ω ∈ A ∧
                  (∀ u, s ≤ u → u < s + logWindow n 16 →
                    CapGate n M (PhaseThreeModel.Numeric.hourIndex n)
                      (trace init ω u)) ∧
                  1 ≤ ψ (trace init ω (s + logWindow n 16))} := measure_mono hsub1
            _ ≤ (1 - ENNReal.ofReal (capRate n M)) ^ logWindow n 16 *
                  ((M / 1000 : ℕ) : ℝ≥0∞) *
                law init {ω | frestrictLe (π := fun _ : ℕ =>
                    Draw (PhaseThreeModel.Numeric.hourIndex n) 256) s ω ∈ A} := hmain
            _ ≤ ENNReal.ofReal (1 / (n : ℝ) ^ 4) * law init (E ∩ {ω | f ω = M}) :=
              mul_le_mul' (cap_contraction_scalar hn hM.1 hM.2)
                (measure_mono hsub2)
        · have hempty : (E ∩ {ω | f ω = M}) ∩ Bset M = ∅ := by
            ext ω
            simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false,
              iff_false]
            rintro ⟨_, h1, h2, _⟩
            exact hM ⟨h1, h2⟩
          rw [hempty]
          simp)
    refine (measure_mono ?_).trans hpart
    rintro ω ⟨⟨s', hs', h1, h2, h3, h4, h5⟩, hωE⟩
    have hss : s' = s := WithTop.coe_injective (hs'.symm.trans hωE)
    subst hss
    exact ⟨hωE, h1, h2, h3, h4, h5⟩

theorem global_cap_failure_tail
    (init : InputCfg n) (hn : timePopulationThreshold ≤ n) :
    law init (globalCapFailure init) ≤ ENNReal.ofReal (1 / (n : ℝ) ^ 4) := by
  refine (measure_mono ?_).trans (cap_spliced_failure_tail init hn
    (capTime init (seedTime init 3))
    (capTime_past init (seedTime init 3) (seedTime_pastTime init 3)))
  intro ω hω
  obtain ⟨S, T, ρ, w, hclock, htime, hgap, hrest⟩ := hω
  obtain ⟨hstart, hgate, hbad⟩ := hrest
  have hSc : S ≤ w.cap := hclock.cap_first.1
  have hcρ : w.cap < ρ :=
    lt_of_le_of_lt (Nat.le_add_right _ _) hclock.protected_settling
  have hMeq : timeMainCount (trace init ω w.cap) = timeMainCount (trace init ω S) :=
    hclock.main_count w.cap hSc hcρ
  have hd := hclock.density S le_rfl (lt_of_le_of_lt hSc hcρ)
  refine ⟨w.cap, htime, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hMeq]
    exact hd.1
  · rw [hMeq]
    have := hd.2.1
    omega
  · rw [hMeq]
    exact (Nat.le_div_iff_mul_le (by norm_num)).mpr (by omega)
  · rw [hMeq]
    exact hgate
  · by_contra hnot
    have hzero : augmentedPhiNat (PhaseThreeModel.Numeric.hourIndex n)
        (trace init ω (w.cap + logWindow n 16)) = 0 := by omega
    have hTend : T ≤ w.cap + logWindow n 16 :=
      hclock.all_before_cap.trans (Nat.le_add_right _ _)
    have hend : w.cap + logWindow n 16 ≤ ρ :=
      hclock.protected_settling.le
    have hphase : ∀ a ∈ trace init ω (w.cap + logWindow n 16),
        3 ≤ a.phase.val := by
      intro a ha
      exact (hclock.all_three _ hTend hclock.protected_settling a ha).ge
    have hcarrier := nonmainZero_of_clockHistory hclock hTend hend
    have hshallow : shallowPotential (PhaseThreeModel.Numeric.hourIndex n)
        (trace init ω (w.cap + logWindow n 16)) = 0 := by
      rw [← augmentedPhiNat_eq_shallowPotential _ _ hphase hcarrier]
      exact hzero
    exact hbad (tieReadout_at_first_exit_of_zero_potential hclock hgap hTend hend
      hshallow)

/-- On a safe seed and a successful clock, failure of the literal readout is
 covered by exactly the three charged events. -/
theorem safe_failure_cover
    (init : InputCfg n) (hvalid : validInitial init)
    (hn : timePopulationThreshold ≤ n) :
    phaseAveragingFailure (reviewedStageEvents n init) ∩ safeSparseEntry init ⊆
      globalHourFailure init ∪ globalTerminalFailure init ∪ globalCapFailure init := by
  intro ω hbad
  obtain ⟨S, T, ρ, hT, hentry, hclockGood⟩ := hbad.1.1
  obtain ⟨w, H⟩ := hclockGood
  have hseed : SafeSparseSeed init ω S :=
    ⟨H.entry.first_phase_seed, safeSeedState_at_entry H.entry hbad.2⟩
  have hSearly : S ≤ earlyHorizon n := H.entry.order.trans hT
  by_cases hz : gapMagnitude init = 0
  · have hgap0 := (gapMagnitude_eq_zero_iff init).1 hz
    have hs := tie_schedule_scope H hgap0
    let p := selectedSchedule init (trace init ω S)
    by_cases hh : ω ∈ hourFailure
        (hourSuccess init (seedTime init 3) p.1 (selectedSign init)) p.2
    · exact Or.inl (Or.inl (show ω ∈ globalHourFailure init from Set.mem_iUnion.mpr ⟨S, ⟨hSearly, hseed⟩, by
        simpa [scheduledHourFailure, hs.1, p] using ⟨hs.2, hh⟩⟩))
    · have hp := tie_cap_package hvalid hn hseed H hgap0 (by
        simpa [p, selectedSchedule, hz] using hh)
      refine Or.inr ?_
      by_cases htie : tieReadout init (trace init ω ρ)
      · exact (hbad.1.2 ⟨S, T, ρ, hT, hentry, ⟨w, H⟩, Or.inl htie⟩).elim
      · exact ⟨S, T, ρ, w, H, hp.1, hgap0, hp.2.1, hp.2.2, htie⟩
  · have hgap : 0 < gapMagnitude init := by omega
    have hsmall := averagingFailure_small_gap
      (by have := (time_population_bounds hn).2; omega) hbad.1 hT H
    have hs := strict_schedule_scope H hgap hsmall
    let p := selectedSchedule init (trace init ω S)
    by_cases hh : ω ∈ hourFailure
        (hourSuccess init (seedTime init 3) p.1 (selectedSign init)) p.2
    · exact Or.inl (Or.inl (show ω ∈ globalHourFailure init from Set.mem_iUnion.mpr ⟨S, ⟨hSearly, hseed⟩, by
        simpa [scheduledHourFailure, hs.2.2.1, p] using ⟨hs.2.2.2, hh⟩⟩))
    · have hout := small_readout_or_terminalFailure hvalid hn hseed H hgap hsmall
        hs.1 (by simpa [p, hs.2.1] using hh)
      rcases hout with hread | hterm
      · exact (hbad.1.2 ⟨S, T, ρ, hT, hentry, ⟨w, H⟩,
          Or.inr (Or.inl ⟨p.1, selectedSign init, hread⟩)⟩).elim
      · refine Or.inl (Or.inr ?_)
        exact show ω ∈ globalTerminalFailure init from Set.mem_iUnion.mpr ⟨S, ⟨⟨hSearly, hseed⟩, by
          dsimp
          refine ⟨w.start (p.1 + 2), ?_, ?_⟩
          · exact hourStart_phaseThreeSeed_clockHistory H (p.1 + 2)
              (by simpa [p] using hs.1.2.1)
          · simpa [p, hs.2.1, seedCounts] using hterm⟩⟩

/-- Uniform safe-seed averaging estimate, before the final N12/sparse union. -/
theorem uniform_safe_seed_averaging
    (init : InputCfg n) (hvalid : validInitial init) (hcard : init.card = n)
    (hn : timePopulationThreshold ≤ n) :
    law init (phaseAveragingFailure (reviewedStageEvents n init) ∩
      safeSparseEntry init) ≤
      5 * (PhaseThreeModel.Numeric.hourIndex n : ℝ≥0∞) * hourError n +
        2 * hourError n + ENNReal.ofReal (1 / (n : ℝ) ^ 4) := by
  calc
    _ ≤ law init (globalHourFailure init ∪
        globalTerminalFailure init ∪ globalCapFailure init) :=
      measure_mono (safe_failure_cover init hvalid hn)
    _ ≤ law init (globalHourFailure init) +
        law init (globalTerminalFailure init) + law init (globalCapFailure init) := by
      exact (measure_union_le _ _).trans
        (add_le_add (measure_union_le _ _) le_rfl)
    _ ≤ _ := add_le_add
      (add_le_add (global_hour_failure_tail init hvalid hcard hn)
        (global_terminal_failure_tail init hvalid hcard hn))
      (global_cap_failure_tail init hn)

/-- The plan's `Pr(B ∩ G)` formulation. -/
def averagingGoodScope (init : InputCfg n) : Set (InputLog n) :=
  (phaseClockFailure (reviewedStageEvents n init))ᶜ ∩ safeSparseEntry init

theorem averaging_bad_inter_goodScope
    (init : InputCfg n) :
    (entryBy (reviewedStageEvents n init) \
      averageBy (reviewedStageEvents n init)) ∩ averagingGoodScope init =
      phaseAveragingFailure (reviewedStageEvents n init) ∩ safeSparseEntry init := by
  ext ω
  simp only [averagingGoodScope, phaseClockFailure, phaseAveragingFailure,
    Set.mem_inter_iff, Set.mem_diff, Set.mem_compl_iff]
  have hc : ω ∈ clockBy (reviewedStageEvents n init) →
      ω ∈ entryBy (reviewedStageEvents n init) := by
    rintro ⟨S, T, ρ, hT, he, _⟩
    exact ⟨S, T, hT, he⟩
  clear * - hc
  tauto

theorem averaging_bad_goodScope_bound
    (init : InputCfg n) (hvalid : validInitial init) (hcard : init.card = n)
    (hn : timePopulationThreshold ≤ n) :
    law init ((entryBy (reviewedStageEvents n init) \
      averageBy (reviewedStageEvents n init)) ∩ averagingGoodScope init) ≤
      5 * (PhaseThreeModel.Numeric.hourIndex n : ℝ≥0∞) * hourError n +
        2 * hourError n + ENNReal.ofReal (1 / (n : ℝ) ^ 4) := by
  rw [averaging_bad_inter_goodScope]
  exact uniform_safe_seed_averaging init hvalid hcard hn

end Ripple.PopulationProtocol.ExactMajority.AveragingGlobalFailureSplice

end
