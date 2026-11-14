-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockCapDeadlineRows.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockRawCapDeadline
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockActivationTime
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockRawLocalRow
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockEarlyMarkEmbedding
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockRows

/-!
The full-activation fibres used below are measurable at their observed
times. Their probabilities sum to at most the seed-prefix probability.
AsyncEntry is used only in the final pathwise inclusion, after the
original-law prefix estimates have already been proved.

This file establishes the two quantitative RowCap fields, independently
of the shape and hour-window estimates. Its coefficient 2/n^11 is
stronger than the compiled RowTails.cap allowance 3/n^5.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockCapDeadlineRows

open TimeTheorem PairLog StageEventSpec PhaseThreeModel.Numeric
open PhaseThreeClockProducer PhaseThreeClockSeedTails PhaseThreeClockVirtual
open PhaseThreeClockCore PhaseThreeClockRows PhaseThreeClockRawLocalRow
open PhaseThreeClockGatedLaw PhaseThreeClockProbabilityFloors
open PhaseThreeClockFirstPositive PhaseThreeClockFirstPositiveSplice
open PhaseThreeClockActivationSeed PhaseThreeClockActivationTime
open PhaseThreeClockEmbeddingBridge PhaseThreeClockNextFrontBirth PhaseThreeClockEarlyMarkEmbedding
open PhaseThreeClockRawCapDeadline

variable {n : ℕ}

theorem activation_cap_windows_add (hn : 2 ≤ n) :
    activationHorizon n + logWindow n 16000 ≤ logWindow n 20000 := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog : (2 / 3 : ℝ) ≤ Real.log (n : ℝ) :=
    log_two_bounds.1.trans (Real.log_le_log (by norm_num) hnR)
  have hprod : (1 : ℝ) ≤ (n : ℝ) * Real.log (n : ℝ) := by nlinarith
  have hceilSmall : (logWindow n 6 : ℝ) ≤
      6 * (n : ℝ) * Real.log (n : ℝ) + 1 :=
    (Nat.ceil_lt_add_one (show 0 ≤ 6 * (n : ℝ) * Real.log (n : ℝ) by positivity)).le
  have hceilLarge : (logWindow n 16000 : ℝ) ≤
      16000 * (n : ℝ) * Real.log (n : ℝ) + 1 :=
    (Nat.ceil_lt_add_one (show 0 ≤ 16000 * (n : ℝ) * Real.log (n : ℝ) by positivity)).le
  apply (Nat.cast_le (α := ℝ)).mp
  calc
    ((activationHorizon n + logWindow n 16000 : ℕ) : ℝ) ≤
        20000 * (n : ℝ) * Real.log (n : ℝ) := by
      simp only [activationHorizon, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
      nlinarith only [hceilSmall, hceilLarge, hprod]
    _ ≤ (logWindow n 20000 : ℝ) := Nat.le_ceil _

/-- Success of the concrete raw cap endpoint gives the canonical RowCap.
No width, shape, or future event is assumed. -/
theorem capRow_of_raw_endpoint (init : InputCfg n)
    (hn : populationThreshold ≤ n) (hcard : init.card = n) (hlarge : 9 ≤ n)
    (ω : InputLog n) (s T : ℕ) (hentry : AsyncEntry init ω s T)
    (hfull : clockCount (virtualLabels init ω T) ≤
      frontCount (virtualLabels init ω (T + rawCapHorizon n)) (clockCap n)) :
    capRow init ω s T := by
  have hseed : ω ∈ seedPrefix init s :=
    ⟨(seedTime_eq_iff init 3 ω s).2 hentry.first_phase_seed, hentry.seed_profile⟩
  have hfibre := mem_safeActivationFibre_of_asyncEntry init ω s T hentry
  have hdense := safeActivationFibre_dense init hlarge s T ω hfibre
  let C := clockCount (virtualLabels init ω T)
  let u := T + rawCapHorizon n
  have hCn : C ≤ n := by
    simpa only [C, hcard] using clockCount_le_card (virtualLabels init ω T)
  have hlo : (6 / 25 : ℝ) * n ≤ C := by
    have hd : 6 * (n : ℝ) ≤ 25 * C := by
      exact_mod_cast (show 6 * n ≤ 25 * C by simpa only [hcard] using hdense.2.2)
    linarith
  have hraw := (raw_cap_numerics C hn hlo hCn).2.2.1
  have hcurrent : clockCount (virtualLabels init ω u) = C :=
    congrArg Finset.card
      (clockSet_fixed_from_homogeneous init ω T hdense.1 u (by dsimp only [u]; omega))
  have hfront : frontCount (virtualLabels init ω u) (clockCap n) = C := by
    apply le_antisymm
    · simpa only [hcurrent] using frontCount_le_clockCount (virtualLabels init ω u) (clockCap n)
    · exact hfull
  have hcount : C = StageEventSpec.clockCount (virtualCfg init ω s) := by
    dsimp only [C]
    rw [virtual_clockCount_eq_seed_of_current_phase_cap init ω s T hseed hentry.order
      (fun i => (hdense.1.1 i).le), clockCount_labelsAt_eq_trace,
      virtualCfg_eq_trace_at_seedPrefix init ω s hseed]
    rfl
  let P : ℕ → Prop := fun v =>
    frontCountL init (virtualLabels init ω s) (virtualLabels init ω v) (clockTop n) =
      StageEventSpec.clockCount (virtualCfg init ω s)
  have hsT : s ≤ T := hentry.order
  have hsu : s ≤ u := by dsimp only [u]; omega
  have hhit : P u := by
    dsimp only [P]
    rw [core_front_eq_current_of_asyncEntry init ω s T u (clockTop n) hseed hentry hsu]
    exact hfront.trans hcount
  have hex : ∃ v, s ≤ v ∧ P v := ⟨u, hsu, hhit⟩
  have hfirst : firstAfter P s (Nat.find hex) := by
    refine ⟨(Nat.find_spec hex).1, (Nat.find_spec hex).2, ?_⟩
    intro v hsv hv hp
    exact (not_lt_of_ge (Nat.find_min' hex ⟨hsv, hp⟩)) hv
  have hcanonical : (virtualTimes init ω s).cap = Nat.find hex := by
    change firstAfterTime P s = Nat.find hex
    exact firstAfterTime_eq hfirst
  have hcap : (virtualTimes init ω s).cap ≤ u := by
    rw [hcanonical]
    exact Nat.find_min' hex ⟨hsu, hhit⟩
  have hactivation : (virtualTimes init ω s).cap ≤ T + logWindow n 16000 := by
    dsimp only [u] at hcap
    omega
  refine ⟨hactivation, ?_⟩
  have hsum := activation_cap_windows_add (n := n) (by omega)
  have hentryDeadline := hentry.deadline
  omega

def rawCapFailureAt (init : InputCfg n) (s : ℕ) : Set (InputLog n) :=
  ⋃ T : ℕ, safeActivationFibre init s T ∩
    {ω | frontCount (virtualLabels init ω (T + rawCapHorizon n)) (clockCap n) <
      clockCount (virtualLabels init ω T)}

/-- The endpoint failure is observable at its own deterministic deadline. -/
theorem raw_cap_activation_fibre_failure_measurable (init : InputCfg n)
    (s T : ℕ) :
    MeasurableSet[pairLogFiltration _ _ (T + rawCapHorizon n)]
      (safeActivationFibre init s T ∩
        {ω | frontCount (virtualLabels init ω (T + rawCapHorizon n)) (clockCap n) <
          clockCount (virtualLabels init ω T)}) := by
  classical
  let ℱ := pairLogFiltration (hourIndex n) 256
  have hE := ((ℱ).mono (by omega : T ≤ T + rawCapHorizon n)) _
    (safeActivationFibre_measurable init s T)
  have hleft : Measurable[ℱ (T + rawCapHorizon n)]
      (fun ω => frontCount (virtualLabels init ω (T + rawCapHorizon n)) (clockCap n)) :=
    (measurable_of_countable (fun f : Fin init.card → AgentState (hourIndex n) 256 =>
      frontCount f (clockCap n))).comp (measurable_virtualLabels init (T + rawCapHorizon n))
  have hright : Measurable[ℱ (T + rawCapHorizon n)]
      (fun ω => clockCount (virtualLabels init ω T)) :=
    ((measurable_of_countable (fun f : Fin init.card → AgentState (hourIndex n) 256 =>
      clockCount f)).comp (measurable_virtualLabels init T)).mono
        ((ℱ).mono (by omega : T ≤ T + rawCapHorizon n)) le_rfl
  exact hE.inter (measurableSet_lt hleft hright)

/-- Splicing only the observed full-activation fibres keeps the original
seed-prefix mass. AsyncEntry is absent from all local estimates. -/
theorem seed_raw_cap_prefix_tail (init : InputCfg n)
    (hn : populationThreshold ≤ n) (hcard : init.card = n) (hlarge : 9 ≤ n) (s : ℕ) :
    law init (rawCapFailureAt init s) ≤
      ENNReal.ofReal (2 / (n : ℝ) ^ 11) * law init (seedPrefix init s) := by
  let A : ℕ → Set (InputLog n) := safeActivationFibre init s
  let B : ℕ → Set (InputLog n) := fun T =>
    {ω | frontCount (virtualLabels init ω (T + rawCapHorizon n)) (clockCap n) <
      clockCount (virtualLabels init ω T)}
  have hdisj : Pairwise (fun T U => Disjoint (A T) (A U)) := by
    intro T U hTU
    apply Set.disjoint_left.mpr
    intro ω hT hU
    exact hTU (WithTop.coe_injective (hT.1.2.symm.trans hU.1.2))
  have hmass : (∑' T, law init (A T)) ≤ law init (seedPrefix init s) := by
    rw [← measure_iUnion hdisj (fun T =>
      (pairLogFiltration _ _).le T _ (safeActivationFibre_measurable init s T))]
    apply measure_mono
    intro ω hω
    obtain ⟨T, hT⟩ := Set.mem_iUnion.mp hω
    exact hT.1.1
  have hlocal (T : ℕ) :
      law init (A T ∩ B T) ≤ ENNReal.ofReal (2 / (n : ℝ) ^ 11) * law init (A T) :=
    raw_cap_dense_prefix_tail init hn hcard T (A T)
      (safeActivationFibre_measurable init s T)
      (fun ω hω => safeActivationFibre_dense init hlarge s T ω hω)
  calc
    _ ≤ ∑' T, law init (A T ∩ B T) := measure_iUnion_le _
    _ ≤ ∑' T, ENNReal.ofReal (2 / (n : ℝ) ^ 11) * law init (A T) :=
      ENNReal.tsum_le_tsum hlocal
    _ = ENNReal.ofReal (2 / (n : ℝ) ^ 11) * ∑' T, law init (A T) := by
      rw [ENNReal.tsum_mul_left]
    _ ≤ _ := mul_le_mul_left' hmass _

/-- Exact seed-fibre form of the quantitative cap row. -/
theorem seed_cap_row_tail (init : InputCfg n)
    (hn : populationThreshold ≤ n) (hcard : init.card = n) (hlarge : 9 ≤ n) (s : ℕ) :
    law init {ω | seedTime init 3 ω = (s : WithTop ℕ) ∧
      SeedProfile n init (trace init ω s) ∧
      ∃ T, T ≤ earlyHorizon n ∧ AsyncEntry init ω s T ∧ ¬ capRow init ω s T} ≤
      ENNReal.ofReal (2 / (n : ℝ) ^ 11) *
        law init {ω | seedTime init 3 ω = (s : WithTop ℕ)} := by
  apply (measure_mono ?_).trans ((seed_raw_cap_prefix_tail init hn hcard hlarge s).trans
    (mul_le_mul_left' (measure_mono (show seedPrefix init s ⊆
      {ω | seedTime init 3 ω = (s : WithTop ℕ)} from fun _ hω => hω.1)) _))
  rintro ω ⟨hs, hp, T, hT, hentry, hbad⟩
  apply Set.mem_iUnion.mpr
  refine ⟨T, mem_safeActivationFibre_of_asyncEntry init ω s T hentry, ?_⟩
  simp only [Set.mem_setOf_eq]
  apply lt_of_not_ge
  intro hfull
  exact hbad (capRow_of_raw_endpoint init hn hcard hlarge ω s T hentry hfull)

theorem cap_row_global_tail (init : InputCfg n)
    (hn : populationThreshold ≤ n) (hcard : init.card = n) (hlarge : 9 ≤ n) :
    law init (rowFailure init (capRow init)) ≤
      ENNReal.ofReal (2 / (n : ℝ) ^ 11) := by
  apply splice_of_local (law init) (seedTime init 3) (rowFailure init (capRow init)) _
    (fun s => (pairLogFiltration _ _).le s _ (seedTime_pastTime init 3 s))
  · rintro ω ⟨s, T, hs, hT, he, hb⟩
    rw [hs]
    exact WithTop.coe_ne_top
  · intro s
    apply (measure_mono ?_).trans (seed_cap_row_tail init hn hcard hlarge s)
    rintro ω ⟨⟨u, T, hu, hT, he, hb⟩, hs⟩
    have hus : u = s := WithTop.coe_injective (hu.symm.trans hs)
    subst u
    exact ⟨hs, he.seed_profile, T, hT, he, hb⟩

theorem cap_budget_calibration (hn : 1 ≤ n) :
    (2 : ℝ) / (n : ℝ) ^ 11 ≤ 3 / (n : ℝ) ^ 5 := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : (0 : ℝ) < (n : ℝ) ^ 5 := by positivity
  have hpow : (n : ℝ) ^ 5 ≤ (n : ℝ) ^ 11 := by
    have hs : (1 : ℝ) ≤ (n : ℝ) ^ 6 := by
      simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hnR 6
    have hmul := mul_le_mul_of_nonneg_left hs hp.le
    simpa only [mul_one, ← pow_add, show (5 + 6 : ℕ) = 11 from rfl] using hmul
  have hfrac := one_div_le_one_div_of_le hp hpow
  have hnonneg : (0 : ℝ) ≤ 1 / (n : ℝ) ^ 5 := by positivity
  have e1 : 2 / (n : ℝ) ^ 11 = 2 * (1 / (n : ℝ) ^ 11) := by ring
  have e2 : 3 / (n : ℝ) ^ 5 = 3 * (1 / (n : ℝ) ^ 5) := by ring
  linarith

/-- The compiled RowTails.cap coefficient, with a strictly stronger
concrete prefix tail underneath it. -/
theorem cap_row_tail (init : InputCfg n)
    (hn : populationThreshold ≤ n) (hcard : init.card = n) (hlarge : 9 ≤ n) :
    law init (rowFailure init (capRow init)) ≤ ENNReal.ofReal (3 / (n : ℝ) ^ 5) :=
  (cap_row_global_tail init hn hcard hlarge).trans
    (ENNReal.ofReal_le_ofReal (cap_budget_calibration (by omega)))

/-- The numerical population hypothesis already implies the small lower
bound used by the observable activation-fibre adapter. -/
theorem cap_population_large (hn : populationThreshold ≤ n) : 9 ≤ n := by
  have hlo : (6 / 25 : ℝ) * n ≤ (n : ℝ) := by
    have hnonneg : (0 : ℝ) ≤ n := by positivity
    linarith
  have hten := (raw_cap_numerics n hn hlo le_rfl).1
  omega

/-- No separate cardinality or small-population premise remains on the
seed-fibre row tail: a nonempty seed prefix supplies the cardinality. -/
theorem seed_cap_row_tail_of_threshold (init : InputCfg n)
    (hn : populationThreshold ≤ n) (s : ℕ) :
    law init {ω | seedTime init 3 ω = (s : WithTop ℕ) ∧
      SeedProfile n init (trace init ω s) ∧
      ∃ T, T ≤ earlyHorizon n ∧ AsyncEntry init ω s T ∧ ¬ capRow init ω s T} ≤
      ENNReal.ofReal (2 / (n : ℝ) ^ 11) *
        law init {ω | seedTime init 3 ω = (s : WithTop ℕ)} := by
  by_cases hcard : init.card = n
  · exact seed_cap_row_tail init hn hcard (cap_population_large hn) s
  · have hempty : {ω | seedTime init 3 ω = (s : WithTop ℕ) ∧
        SeedProfile n init (trace init ω s) ∧
        ∃ T, T ≤ earlyHorizon n ∧ AsyncEntry init ω s T ∧ ¬ capRow init ω s T} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro ω ⟨hs, hp, -⟩
      exact hcard (seedPrefix_card_eq init ω s ⟨hs, hp⟩)
    rw [hempty, measure_empty]
    exact bot_le

/-- The compiled cap-row conclusion under its numerical population
hypothesis alone. No state or probability gate is an additional premise. -/
theorem cap_row_tail_of_threshold (init : InputCfg n)
    (hn : populationThreshold ≤ n) :
    law init (rowFailure init (capRow init)) ≤ ENNReal.ofReal (3 / (n : ℝ) ^ 5) := by
  by_cases hcard : init.card = n
  · exact cap_row_tail init hn hcard (cap_population_large hn)
  · have hempty : rowFailure init (capRow init) = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro ω ⟨s, T, hs, hT, he, hb⟩
      exact hcard (seedPrefix_card_eq init ω s ⟨hs, he.seed_profile⟩)
    rw [hempty, measure_empty]
    exact bot_le

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockCapDeadlineRows

end
