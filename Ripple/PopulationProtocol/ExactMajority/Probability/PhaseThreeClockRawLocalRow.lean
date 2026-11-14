-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockRawLocalRow.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockObservedStarts
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockCoreCounts

/-!
# The raw-local Core row on the genuine seed fibre

The two first-passage predicates below are exactly ClockCore.level_first
and ClockCore.level_bulk. They specify the witnesses to which raw_local
refers; they do not assume any passage-duration estimate.

The proof first bounds an observable failure from firstDenseTime. Only
after that bound is established is AsyncEntry intersected into the bad
event. Thus the coefficient is n^(-8) times the original seed-fibre mass.
The theorem covers every correct choice of the first-passage witnesses.
It does not by itself construct the remaining ClockTimes fields.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockRawLocalRow

open TimeTheorem PairLog StageEventSpec PhaseThreeClockProducer
  PhaseThreeClockVirtual PhaseThreeClockCore PhaseThreeClockCoreCounts
  PhaseThreeClockSeedTails PhaseThreeClockActivationSeed
  PhaseThreeClockEmbeddingBridge PhaseThreeClockObservedPassage
  PhaseThreeClockObservedPassageSplice PhaseThreeClockObservedStarts
  PhaseThreeClockBulkFamily

variable {n : ℕ}

def LevelPassages (init : InputCfg n) (ω : InputLog n) (s : ℕ)
    (w : ClockTimes init) : Prop :=
  (∀ ell, 1 ≤ ell → ell ≤ clockTop n →
    firstAfter
      (fun v => 1 ≤ frontCountL init (virtualLabels init ω s)
        (virtualLabels init ω v) ell) s (w.first ell)) ∧
  (∀ ell, 1 ≤ ell → ell ≤ clockTop n →
    firstAfter
      (fun v => bulkThreshold (clockCount (virtualCfg init ω s)) ≤
        frontCountL init (virtualLabels init ω s)
          (virtualLabels init ω v) ell) s (w.bulk ell))

def RawLocalRow (init : InputCfg n) (w : ClockTimes init) : Prop :=
  ∀ ell, 1 ≤ ell → ell ≤ clockTop n →
    w.bulk ell - w.first ell ≤ logWindow n 30

def rawLocalFailureAt (init : InputCfg n) (s : ℕ) : Set (InputLog n) :=
  {ω | seedTime init 3 ω = (s : WithTop ℕ) ∧
    SeedProfile n init (trace init ω s) ∧
    ∃ T, ∃ w : ClockTimes init,
      T ≤ earlyHorizon n ∧ AsyncEntry init ω s T ∧
        LevelPassages init ω s w ∧ ¬ RawLocalRow init w}

theorem levelPassages_of_virtualCore (init : InputCfg n) (ω : InputLog n)
    (s T : ℕ) (w : ClockTimes init) (hcore : VirtualClockCore init ω s T w) :
    LevelPassages init ω s w :=
  ⟨hcore.level_first, hcore.level_bulk⟩

theorem rawLocalRow_of_virtualCore (init : InputCfg n) (ω : InputLog n)
    (s T : ℕ) (w : ClockTimes init) (hcore : VirtualClockCore init ω s T w) :
    RawLocalRow init w :=
  hcore.raw_local

theorem virtualCfg_eq_trace_at_seedPrefix (init : InputCfg n)
    (ω : InputLog n) (s : ℕ) (hseed : ω ∈ seedPrefix init s) :
    virtualCfg init ω s = trace init ω s := by
  change labelCfg (virtualLabels init ω s) = trace init ω s
  rw [virtual_eq_actual_at_seedPrefix init ω s hseed]
  exact labelsAt_config init ω s

theorem virtual_clock_density_of_asyncEntry (init : InputCfg n)
    (ω : InputLog n) (s T : ℕ) (hseed : ω ∈ seedPrefix init s)
    (hentry : AsyncEntry init ω s T) :
    ∀ u, s ≤ u → 6 * init.card ≤
      25 * PhaseThreeClockGatedLaw.clockCount (virtualLabels init ω u) := by
  intro u hsu
  have henv := virtualLabels_clockEnvironment_of_asyncEntry init ω s T hentry u hsu
  rw [virtual_clockCount_eq_seed_of_current_phase_cap init ω s u hseed hsu
    (fun i => (henv.phase_range i).2)]
  exact clock_density_at_seedPrefix init ω s hseed

theorem core_front_eq_current_of_asyncEntry (init : InputCfg n)
    (ω : InputLog n) (s T u ell : ℕ) (hseed : ω ∈ seedPrefix init s)
    (hentry : AsyncEntry init ω s T) (hsu : s ≤ u) :
    frontCountL init (virtualLabels init ω s) (virtualLabels init ω u) ell =
      PhaseThreeClockGatedLaw.frontCount (virtualLabels init ω u) ell := by
  exact frontCountL_virtual_seed init ω s u ell hseed hsu
    (fun i => ((virtualLabels_clockEnvironment_of_asyncEntry
      init ω s T hentry u hsu).phase_range i).2)

theorem firstDenseTime_eq_core_first (init : InputCfg n) (ω : InputLog n)
    (s T ell f : ℕ) (hseed : ω ∈ seedPrefix init s)
    (hentry : AsyncEntry init ω s T)
    (hfirst : firstAfter
      (fun v => 1 ≤ frontCountL init (virtualLabels init ω s)
        (virtualLabels init ω v) ell) s f) :
    firstDenseTime init s ell ω = (f : WithTop ℕ) := by
  apply firstDenseTime_eq_of_firstAfter init s ell f ω
  · refine ⟨hfirst.1, ?_, ?_⟩
    · simpa only [core_front_eq_current_of_asyncEntry init ω s T f ell
        hseed hentry hfirst.1] using hfirst.2.1
    · intro v hsv hvf hv
      apply hfirst.2.2 v hsv hvf
      simpa only [core_front_eq_current_of_asyncEntry init ω s T v ell
        hseed hentry hsv] using hv
  · exact virtual_clock_density_of_asyncEntry init ω s T hseed hentry

theorem firstHitHorizon_eq_logWindow (m : ℕ) :
    PhaseThreeModel.Numeric.firstHitHorizon m = logWindow m 30 := by
  rfl

/-- The only use of future entry success is this pathwise inclusion into
the already estimated observable stopping-time event. -/
theorem long_core_passage_mem_observedFailure (init : InputCfg n)
    (hcard : init.card = n) (ω : InputLog n) (s T ell f b : ℕ)
    (hseed : ω ∈ seedPrefix init s) (hentry : AsyncEntry init ω s T)
    (hfirst : firstAfter
      (fun v => 1 ≤ frontCountL init (virtualLabels init ω s)
        (virtualLabels init ω v) ell) s f)
    (hbulk : firstAfter
      (fun v => bulkThreshold (clockCount (virtualCfg init ω s)) ≤
        frontCountL init (virtualLabels init ω s)
          (virtualLabels init ω v) ell) s b)
    (hlong : logWindow n 30 < b - f) :
    ω ∈ observedBulkFailure init ell (firstDenseTime init s ell) := by
  let N := PhaseThreeModel.Numeric.firstHitHorizon init.card
  have hN : N = logWindow n 30 := by
    dsimp only [N]
    rw [hcard, firstHitHorizon_eq_logWindow]
  have hsf : s ≤ f := hfirst.1
  have hfb : f + N < b := by omega
  have hsfN : s ≤ f + N := by omega
  have henv := virtualLabels_clockEnvironment_of_asyncEntry init ω s T hentry f hfirst.1
  have hcount :
      PhaseThreeClockGatedLaw.clockCount (virtualLabels init ω f) =
        clockCount (virtualCfg init ω s) := by
    rw [virtual_clockCount_eq_seed_of_current_phase_cap init ω s f hseed
      hfirst.1 (fun i => (henv.phase_range i).2),
      clockCount_labelsAt_eq_trace,
      virtualCfg_eq_trace_at_seedPrefix init ω s hseed]
    rfl
  refine ⟨f, firstDenseTime_eq_core_first init ω s T ell f hseed hentry hfirst, ?_⟩
  refine ⟨environmentSpan_of_asyncEntry init ω s T f N hentry hfirst.1, ?_⟩
  apply lt_of_not_ge
  intro hhit
  apply hbulk.2.2 (f + N) hsfN hfb
  simpa only [core_front_eq_current_of_asyncEntry init ω s T (f + N) ell
    hseed hentry hsfN, hcount] using hhit

theorem rawLocalFailureAt_subset (init : InputCfg n) (s : ℕ)
    (hcard : init.card = n) :
    rawLocalFailureAt init s ⊆
      seedPrefix init s ∩ bulkFamilyFailure init
        (Finset.Icc 1 (PhaseThreeModel.Numeric.clockCap n))
        (fun ell => firstDenseTime init s ell) := by
  classical
  rintro ω ⟨hs, hsp, T, w, -, hentry, hpass, hbad⟩
  have hseed : ω ∈ seedPrefix init s := ⟨hs, hsp⟩
  change ¬ (∀ ell, 1 ≤ ell → ell ≤ clockTop n →
    w.bulk ell - w.first ell ≤ logWindow n 30) at hbad
  push_neg at hbad
  obtain ⟨ell, hell, hcap, hlong⟩ := hbad
  refine ⟨hseed, Set.mem_iUnion.mpr ⟨ell, Set.mem_iUnion.mpr ⟨?_, ?_⟩⟩⟩
  · apply Finset.mem_Icc.mpr
    exact ⟨hell, by
      simpa only [clockTop, PhaseThreeModel.Numeric.clockCap,
        PhaseThreeModel.Numeric.clockHours] using hcap⟩
  · exact long_core_passage_mem_observedFailure init hcard ω s T ell
      (w.first ell) (w.bulk ell) hseed hentry
      (hpass.1 ell hell hcap) (hpass.2 ell hell hcap) hlong

/-- The exact raw_local field failure on the first-seed fibre.
The coefficient is measured against the original fibre, not the
conditional probability of a future AsyncEntry event. -/
theorem seed_raw_local_tail (init : InputCfg n) (hm : 20 ≤ init.card)
    (hcard : init.card = n) (hn : PhaseThreeModel.Numeric.populationThreshold ≤ n)
    (s : ℕ) :
    law init (rawLocalFailureAt init s) ≤
      ENNReal.ofReal (1 / (n : ℝ) ^ 8) *
        law init {ω | seedTime init 3 ω = (s : WithTop ℕ)} := by
  calc
    law init (rawLocalFailureAt init s) ≤
        law init (seedPrefix init s ∩ bulkFamilyFailure init
          (Finset.Icc 1 (PhaseThreeModel.Numeric.clockCap n))
          (fun ell => firstDenseTime init s ell)) :=
      measure_mono (rawLocalFailureAt_subset init s hcard)
    _ ≤ ENNReal.ofReal (1 / (init.card : ℝ) ^ 8) *
          law init (seedPrefix init s) :=
      firstDense_bulk_family_prefix_tail init hm hcard hn s
        (seedPrefix init s) (seedPrefix_measurable init s)
    _ ≤ ENNReal.ofReal (1 / (n : ℝ) ^ 8) *
          law init {ω | seedTime init 3 ω = (s : WithTop ℕ)} := by
      rw [hcard]
      exact mul_le_mul_left' (measure_mono (fun _ hω => hω.1)) _

/-- Pointwise witness selection is allowed; no measurability of the selected
ClockTimes is used in this outer-measure bound. -/
theorem seed_selected_raw_local_tail (init : InputCfg n) (hm : 20 ≤ init.card)
    (hcard : init.card = n) (hn : PhaseThreeModel.Numeric.populationThreshold ≤ n)
    (s : ℕ) (chooseT : InputLog n → ℕ)
    (chooseW : InputLog n → ClockTimes init) :
    law init {ω | seedTime init 3 ω = (s : WithTop ℕ) ∧
      SeedProfile n init (trace init ω s) ∧
      chooseT ω ≤ earlyHorizon n ∧ AsyncEntry init ω s (chooseT ω) ∧
      LevelPassages init ω s (chooseW ω) ∧ ¬ RawLocalRow init (chooseW ω)} ≤
      ENNReal.ofReal (1 / (n : ℝ) ^ 8) *
        law init {ω | seedTime init 3 ω = (s : WithTop ℕ)} := by
  apply (measure_mono ?_).trans (seed_raw_local_tail init hm hcard hn s)
  rintro ω ⟨hs, hsp, hT, hentry, hpass, hbad⟩
  exact ⟨hs, hsp, chooseT ω, chooseW ω, hT, hentry, hpass, hbad⟩


/-- Sum the disjoint genuine seed fibres. The shared all-level P3a row
is charged once, with no early-horizon multiplicative factor. -/
theorem raw_local_global_tail (init : InputCfg n) (hm : 20 ≤ init.card)
    (hcard : init.card = n) (hn : PhaseThreeModel.Numeric.populationThreshold ≤ n) :
    law init {ω | ∃ s, ω ∈ rawLocalFailureAt init s} ≤
      ENNReal.ofReal (1 / (n : ℝ) ^ 8) := by
  apply splice_of_local (law init) (seedTime init 3)
    {ω | ∃ s, ω ∈ rawLocalFailureAt init s} _
    (fun s => (pairLogFiltration _ _).le s _ (seedTime_pastTime init 3 s))
  · rintro ω ⟨s, hs⟩
    rw [hs.1]
    exact WithTop.coe_ne_top
  · intro s
    apply (measure_mono ?_).trans (seed_raw_local_tail init hm hcard hn s)
    rintro ω ⟨⟨u, hu⟩, hs⟩
    have hus : u = s := WithTop.coe_injective (hu.1.symm.trans hs)
    subst u
    exact hu

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockRawLocalRow

end
