import Ripple.PopulationProtocol.ExactMajority.Probability.Phase9OutputCleanup
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockProducer
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseOneDrainStopping

/-!
# Lemma 14: Phase-9 output cleanup at an observed start

The exact label participation rate is spliced over disjoint stopping-time
fibres. The resulting failure budget is the inverse cube of the population.
The entry hypothesis concerns one state on the actual trace.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal BigOperators

namespace Ripple.PopulationProtocol.ExactMajority.LateLemmaFourteenCleanup

open scoped ENNReal NNReal

/-- A union over all population labels of the geometric miss probability
at the output-cleanup horizon is at most the inverse cube of the population. -/
theorem cleanup_geometric_bound {n : ℕ} (hn : 2 ≤ n) :
    (1 - 2 / (n : ℝ≥0∞)) ^ ⌈2 * (n : ℝ) * Real.log (n : ℝ)⌉₊ * n ≤
      1 / (n : ℝ≥0∞) ^ 3 := by
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hnm : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hrate :
      2 * ((n : ℝ) - 1) / ((n : ℝ) * ((n : ℝ) - 1)) =
        2 / (n : ℝ) := by
    field_simp [hn0.ne', hnm.ne']
  have hscale :
      ((n : ℝ) * ((n : ℝ) - 1)) / (2 * ((n : ℝ) - 1)) =
        (n : ℝ) / 2 := by
    field_simp [hn0.ne', hnm.ne']
  have hhorizon :
      DriftSurvival.driftHorizon (2 * ((n : ℝ) - 1)) n n n =
        ⌈2 * (n : ℝ) * Real.log (n : ℝ)⌉₊ := by
    unfold DriftSurvival.driftHorizon
    rw [hscale, Real.log_mul hn0.ne' (pow_ne_zero 2 hn0.ne'), Real.log_pow]
    congr 1
    ring
  have hcastRate :
      ENNReal.ofReal (2 / (n : ℝ)) = 2 / (n : ℝ≥0∞) := by
    rw [div_eq_mul_inv, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
      ENNReal.ofReal_inv_of_pos hn0]
    simp [div_eq_mul_inv]
  have hfactor :
      ENNReal.ofReal
          (1 - 2 * ((n : ℝ) - 1) / ((n : ℝ) * ((n : ℝ) - 1))) =
        1 - 2 / (n : ℝ≥0∞) := by
    rw [hrate, ENNReal.ofReal_sub (1 : ℝ) (by positivity),
      ENNReal.ofReal_one, hcastRate]
  have hbudget :
      ENNReal.ofReal (1 / ((n : ℝ) * (n : ℝ) ^ 2)) =
        1 / (n : ℝ≥0∞) ^ 3 := by
    have hcube : (n : ℝ) * (n : ℝ) ^ 2 = (n : ℝ) ^ 3 := by ring
    rw [hcube, div_eq_mul_inv,
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1),
      ENNReal.ofReal_inv_of_pos (by positivity),
      ENNReal.ofReal_pow (by positivity : 0 ≤ (n : ℝ))]
    norm_num
  have h := DriftSurvival.drift_pow_le_budget
    (B := 2 * ((n : ℝ) - 1)) (n := n) (Φmax := n) (D := n)
    hn (by omega) (by omega) (by positivity)
    (by nlinarith)
  rw [hhorizon, hfactor, hbudget] at h
  exact h


open TimeTheorem PairLog PhaseOneDrain Phase9OutputCleanup
open PhaseOneDrainStopping

variable {L K : ℕ}

/-- The additional interaction window in Lemma 14. -/
def cleanupWindow (n : ℕ) : ℕ := ⌈2 * (n : ℝ) * Real.log (n : ℝ)⌉₊

/-- Verdict support includes the Phase-9 phase value. -/
theorem signState_phase (out : Output) (a : AgentState L K)
    (h : Phase9SignState out a) : a.phase.val = 9 := by
  cases out <;> exact h.1

/-- The cleanup invariant persists for every recorded draw, including a null draw. -/
theorem signs_applyDraw (out : Output) (n : ℕ) (c : Cfg L K)
    (h : Phase9SignsDone out n c) (d : Draw L K) :
    Phase9SignsDone out n (applyDraw c d) := by
  cases d with
  | none => exact h
  | some p => exact Phase9SignsDone_stepOrSelf out n c h _ _

/-- Lemma 14 sign support persists from the specified state on the actual trace. -/
theorem signs_trace (init : Cfg L K) (out : Output) (n : ℕ)
    (ω : Ω L K) (u v : ℕ) (huv : u ≤ v)
    (hstart : Phase9SignsDone out n (trace init ω u)) :
    Phase9SignsDone out n (trace init ω v) := by
  induction v, huv using Nat.le_induction with
  | base => exact hstart
  | succ v huv ih =>
      rw [TimeTheorem.trace_succ]
      exact signs_applyDraw out n _ ih _

/-- Every later selected pair writes the majority output to both agents. -/
theorem selected_pair_correct (init : Cfg L K) (out : Output) (n : ℕ)
    (ω : Ω L K) (u v : ℕ) (huv : u ≤ v)
    (hstart : Phase9SignsDone out n (trace init ω u))
    (a b : AgentState L K)
    (happ : Protocol.Applicable (trace init ω v) a b) :
    (Transition L K a b).1.output = out ∧
      (Transition L K a b).2.output = out := by
  have h := signs_trace init out n ω u v huv hstart
  have hp := Transition_phase9_sign_pair out a b
    (h.2 a (Multiset.mem_of_le happ (by simp)))
    (h.2 b (Multiset.mem_of_le happ (by simp)))
  exact ⟨hp.1.2, hp.2.2⟩

/-- Correct Phase-9 sign support rules out every opposite-sign advance. -/
theorem signs_locallyStable (out : Output) (n : ℕ) (c : Cfg L K)
    (h : Phase9SignsDone out n c) : phase9LocallyStable c := by
  refine ⟨fun a ha => signState_phase out a (h.2 a ha), ?_⟩
  intro a b happ hbad
  have ha := h.2 a (Multiset.mem_of_le happ (by simp))
  have hb := h.2 b (Multiset.mem_of_le happ (by simp))
  have hstay := signState_phase out _ (Transition_phase9_sign_pair out a b ha hb).1.1
  have hgo := Transition_phase9_advances_of_union_has_opposite_signs a b
    (signState_phase out a ha) (signState_phase out b hb) hbad.1 hbad.2
  omega

/-- Zero wrong-output count means every output equals the fixed verdict. -/
theorem output_eq_of_zero (out : Output) (c : Cfg L K)
    (h : wrongOutputCount9 out c = 0) : ∀ a ∈ c, a.output = out := by
  classical
  intro a ha
  by_contra hne
  have hp : 0 < wrongOutputCount9 out c :=
    Multiset.countP_pos.mpr ⟨a, ha, hne⟩
  omega

/-- The cleaned signed state is the existing Phase-9 consensus endpoint. -/
theorem endpoint_of_clean (init c : Cfg L K) (out : Output) (n : ℕ)
    (hsigned : out = .A ∨ out = .B)
    (hmajor : majorityVerdict init = outputTripleOfOutput out)
    (hpost : Phase9Post out n c) : phase9ConsensusEndpoint init c := by
  have hstable := signs_locallyStable out n c hpost.1
  have hout := output_eq_of_zero out c hpost.2
  rcases hsigned with rfl | rfl
  · exact phase9ConsensusEndpoint_of_A init c hmajor hstable
      (fun a ha => ⟨hout a ha, (hpost.1.2 a ha).2⟩)
  · exact phase9ConsensusEndpoint_of_B init c hmajor hstable
      (fun a ha => ⟨hout a ha, (hpost.1.2 a ha).2⟩)

/-- The first state where all agents have the chosen majority sign in Phase 9. -/
def cleanupStart (init : Cfg L K) (out : Output) (n : ℕ) : Ω L K → WithTop ℕ :=
  TraceDrain.exitTime init (Phase9SignsDone out n)

/-- The canonical entry is a genuine stopping time of the recorded past. -/
theorem cleanupStart_pastTime (init : Cfg L K) (out : Output) (n : ℕ) :
    PairLogPastTime (cleanupStart init out n) :=
  exitTime_pairLogPastTime init (Phase9SignsDone out n)

/-- Finite canonical entry produces the exact state hypothesis used by cleanup. -/
theorem cleanupStart_entry (init : Cfg L K) (out : Output) (n : ℕ)
    (ω : Ω L K) (u : ℕ) (hu : cleanupStart init out n ω = (u : WithTop ℕ)) :
    Phase9SignsDone out n (trace init ω u) :=
  ((exitTime_eq_iff_firstHit init (Phase9SignsDone out n) ω u).mp hu).1


/-- Participation of a persistent physical label in the next interaction. -/
def labelParticipates (init : Cfg L K) (i : Fin init.card) (t : ℕ)
    (ω : Ω L K) : Prop :=
  ∃ j : Fin init.card, j ≠ i ∧
    (drawLabels init ω (t + 1) = some (i, j) ∨
     drawLabels init ω (t + 1) = some (j, i))

/-- The label is missed throughout the next `T` interactions after time `u`. -/
def labelMiss (init : Cfg L K) (i : Fin init.card) (u T : ℕ)
    (ω : Ω L K) : Prop :=
  ∀ k : ℕ, k < T → ¬ labelParticipates init i (u + k) ω

/-- Some persistent label is missed after the finite stopping time. -/
def missedLabelFailure (init : Cfg L K) (σ : Ω L K → WithTop ℕ)
    (T : ℕ) : Set (Ω L K) :=
  {ω | ∃ u : ℕ, σ ω = (u : WithTop ℕ) ∧
    ∃ i : Fin init.card, labelMiss init i u T ω}

private theorem participation_measurable (init : Cfg L K)
    (i : Fin init.card) (t : ℕ) :
    MeasurableSet[pairLogFiltration L K (t + 1)]
      {ω | labelParticipates init i t ω} := by
  have hl : Measurable[pairLogFiltration L K (t + 1)]
      (fun ω => labelsAt init ω t) :=
    ((measurable_prefixLabels init t).comp
      (measurable_pairLog_prefix L K t)).mono
        ((pairLogFiltration L K).mono (Nat.le_succ t)) le_rfl
  have hd : Measurable[pairLogFiltration L K (t + 1)]
      (fun ω : Ω L K => ω (t + 1)) :=
    (measurable_pi_apply (⟨t + 1, Finset.mem_Iic.mpr le_rfl⟩ : Finset.Iic (t + 1))).comp
      (measurable_pairLog_prefix L K (t + 1))
  have hp := hl.prodMk hd
  exact hp ((Set.to_countable
    {z : (Fin init.card → AgentState L K) × Draw L K |
      ∃ j : Fin init.card, j ≠ i ∧
        (selectLabels z.1 z.2 = some (i, j) ∨
         selectLabels z.1 z.2 = some (j, i))}).measurableSet)

private theorem miss_measurable (init : Cfg L K)
    (i : Fin init.card) (u T : ℕ) :
    MeasurableSet[pairLogFiltration L K (u + T)]
      {ω | labelMiss init i u T ω} := by
  have heq : {ω | labelMiss init i u T ω} =
      ⋂ k : Fin T, {ω | ¬ labelParticipates init i (u + k.val) ω} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iInter, labelMiss]
    exact ⟨fun h k => h k.val k.isLt, fun h k hk => h ⟨k, hk⟩⟩
  rw [heq]
  exact MeasurableSet.iInter fun k =>
    (((pairLogFiltration L K).mono (by omega)) _
      (participation_measurable init i (u + k.val))).compl

/-- The event of a missed label at the stopping time is measurable. -/
theorem missedLabelFailure_measurable (init : Cfg L K)
    (σ : Ω L K → WithTop ℕ) (hσ : PairLogPastTime σ) (T : ℕ) :
    MeasurableSet (missedLabelFailure init σ T) := by
  have heq : missedLabelFailure init σ T =
      ⋃ u : ℕ, {ω | σ ω = (u : WithTop ℕ)} ∩
        ⋃ i : Fin init.card, {ω | labelMiss init i u T ω} := by
    ext ω
    simp [missedLabelFailure]
  rw [heq]
  exact MeasurableSet.iUnion fun u =>
    ((pairLogFiltration L K).le u _ (hσ u)).inter
      (MeasurableSet.iUnion fun i =>
        (pairLogFiltration L K).le (u + T) _ (miss_measurable init i u T))

private theorem real_miss_step (init : Cfg L K) (hc : 2 ≤ init.card)
    (i : Fin init.card) (t : ℕ) (A : Set (Ω L K))
    (hA : MeasurableSet[pairLogFiltration L K t] A) :
    (law init).real (A ∩ {ω | ¬ labelParticipates init i t ω}) =
      (1 - 2 / (init.card : ℝ)) * (law init).real A := by
  classical
  let μ := law init
  let ℱ := pairLogFiltration L K
  let X : Ω L K → ℝ := fun ω => if ω ∈ A then 1 else 0
  let Y : Ω L K → ℝ := fun ω => if labelParticipates init i t ω then 1 else 0
  have hXm : StronglyMeasurable[ℱ t] X :=
    (Measurable.ite hA measurable_const measurable_const).stronglyMeasurable
  have hYm : StronglyMeasurable Y :=
    (Measurable.ite ((ℱ.le (t + 1)) _ (participation_measurable init i t))
      measurable_const measurable_const).stronglyMeasurable
  have hXi : Integrable X μ := Integrable.of_bound
    (hXm.mono (ℱ.le t)).aestronglyMeasurable 1
    (ae_of_all μ fun ω => by dsimp only [X]; split_ifs <;> norm_num)
  have hYi : Integrable Y μ := Integrable.of_bound hYm.aestronglyMeasurable 1
    (ae_of_all μ fun ω => by dsimp only [Y]; split_ifs <;> norm_num)
  have hXYi : Integrable (X * Y) μ := Integrable.of_bound
    ((hXm.mono (ℱ.le t)).mul hYm).aestronglyMeasurable 1
    (ae_of_all μ fun ω => by dsimp only [X, Y, Pi.mul_apply]; split_ifs <;> norm_num)
  have hpull := condExp_mul_of_stronglyMeasurable_left hXm hXYi hYi
  have hrate := PhaseZeroEntry.selected_label_participation_conditional_probability
    init hc i t
  have hrate' : μ[Y | ℱ t] =ᵐ[μ]
      (fun _ => 2 / (init.card : ℝ)) := by
    refine (condExp_congr_ae (μ := μ) (m := ℱ t) ?_).trans hrate
    exact ae_of_all μ fun ω => by simp [Y, labelParticipates]
  have hprod : (∫ ω, X ω * Y ω ∂μ) =
      (2 / (init.card : ℝ)) * ∫ ω, X ω ∂μ := by
    calc
      (∫ ω, X ω * Y ω ∂μ) = ∫ ω, μ[X * Y | ℱ t] ω ∂μ :=
        (integral_condExp (ℱ.le t)).symm
      _ = ∫ ω, (2 / (init.card : ℝ)) * X ω ∂μ := by
        apply integral_congr_ae
        filter_upwards [hpull, hrate'] with ω hp hr
        rw [hp]
        change X ω * μ[Y | ℱ t] ω = _
        rw [hr]
        ring
      _ = _ := by rw [integral_const_mul]
  have hint : (∫ ω, X ω ∂μ) = μ.real A := by
    simpa only [X, Set.indicator, Pi.one_apply] using
      (integral_indicator_one (μ := μ) ((ℱ.le t) _ hA))
  have hsurv : (∫ ω, X ω - (X * Y) ω ∂μ) =
      μ.real (A ∩ {ω | ¬ labelParticipates init i t ω}) := by
    have heq : (fun ω => X ω - (X * Y) ω) =
        (A ∩ {ω | ¬ labelParticipates init i t ω}).indicator (fun _ => (1 : ℝ)) := by
      funext ω
      by_cases ha : ω ∈ A <;> by_cases hp : labelParticipates init i t ω <;>
        simp [X, Y, ha, hp]
    rw [heq]
    exact integral_indicator_one
      (((ℱ.le t) _ hA).inter
        (((ℱ.le (t + 1)) _ (participation_measurable init i t)).compl))
  rw [← hsurv, integral_sub hXi hXYi]
  change (∫ ω, X ω ∂μ) - (∫ ω, X ω * Y ω ∂μ) = _
  rw [hprod, hint]
  ring

private theorem label_miss_real (init : Cfg L K) (hc : 2 ≤ init.card)
    (i : Fin init.card) (u : ℕ) (A : Set (Ω L K))
    (hA : MeasurableSet[pairLogFiltration L K u] A) (T : ℕ) :
    (law init).real (A ∩ {ω | labelMiss init i u T ω}) =
      (1 - 2 / (init.card : ℝ)) ^ T * (law init).real A := by
  induction T with
  | zero => simp [labelMiss]
  | succ T ih =>
    have heq : A ∩ {ω | labelMiss init i u (T + 1) ω} =
        (A ∩ {ω | labelMiss init i u T ω}) ∩
          {ω | ¬ labelParticipates init i (u + T) ω} := by
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, labelMiss]
      constructor
      · rintro ⟨ha, hm⟩
        exact ⟨⟨ha, fun k hk => hm k (by omega)⟩, hm T (by omega)⟩
      · rintro ⟨⟨ha, hm⟩, hp⟩
        refine ⟨ha, fun k hk => ?_⟩
        by_cases hkt : k < T
        · exact hm k hkt
        · have : k = T := by omega
          simpa [this] using hp
    rw [heq, real_miss_step init hc i (u + T) _
      ((((pairLogFiltration L K).mono (by omega)) _ hA).inter
        (miss_measurable init i u T)), ih, pow_succ]
    ring

/-- The exact relative geometric bound for one label on any past event. -/
theorem label_miss_bound (init : Cfg L K) (hc : 2 ≤ init.card)
    (i : Fin init.card) (u : ℕ) (A : Set (Ω L K))
    (hA : MeasurableSet[pairLogFiltration L K u] A) (T : ℕ) :
    law init (A ∩ {ω | labelMiss init i u T ω}) =
      (1 - 2 / (init.card : ℝ≥0∞)) ^ T * law init A := by
  have hn0 : (0 : ℝ) < init.card := by exact_mod_cast (show 0 < init.card by omega)
  have hnR : (2 : ℝ) ≤ init.card := by exact_mod_cast hc
  have hq : 0 ≤ 1 - 2 / (init.card : ℝ) := by
    rw [sub_nonneg, div_le_one hn0]
    exact hnR
  have hcast : ENNReal.ofReal (1 - 2 / (init.card : ℝ)) =
      1 - 2 / (init.card : ℝ≥0∞) := by
    rw [ENNReal.ofReal_sub (1 : ℝ) (by positivity), ENNReal.ofReal_one]
    congr 1
    rw [div_eq_mul_inv, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
      ENNReal.ofReal_inv_of_pos hn0]
    simp [div_eq_mul_inv]
  have h := congrArg ENNReal.ofReal (label_miss_real init hc i u A hA T)
  rw [ENNReal.ofReal_mul (pow_nonneg hq _), ENNReal.ofReal_pow hq, hcast] at h
  simpa only [Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _)] using h

/-- Uniform coupon cleanup at a stopping time, retaining the mass of each fibre. -/
theorem missedLabelFailure_bound (init : Cfg L K)
    (σ : Ω L K → WithTop ℕ) (hσ : PairLogPastTime σ)
    {n : ℕ} (hcard : init.card = n) (hn : 2 ≤ n) (T : ℕ) :
    law init (missedLabelFailure init σ T) ≤
      (1 - 2 / (n : ℝ≥0∞)) ^ T * n := by
  have hc : 2 ≤ init.card := by omega
  apply PhaseThreeClockProducer.splice_of_local (law init) σ
    (missedLabelFailure init σ T) _
    (fun u => (pairLogFiltration L K).le u _ (hσ u))
  · rintro ω ⟨u, hu, _⟩
    rw [hu]
    exact WithTop.coe_ne_top
  · intro u
    let A : Set (Ω L K) := {ω | σ ω = (u : WithTop ℕ)}
    have hsub : missedLabelFailure init σ T ∩ A ⊆
        ⋃ i : Fin init.card, A ∩ {ω | labelMiss init i u T ω} := by
      rintro ω ⟨⟨v, hv, i, hi⟩, hu⟩
      have heq : v = u := WithTop.coe_injective (hv.symm.trans hu)
      subst v
      exact Set.mem_iUnion.mpr ⟨i, hu, hi⟩
    calc
      law init (missedLabelFailure init σ T ∩ A) ≤
          law init (⋃ i : Fin init.card, A ∩ {ω | labelMiss init i u T ω}) :=
        measure_mono hsub
      _ ≤ ∑ i : Fin init.card, law init (A ∩ {ω | labelMiss init i u T ω}) :=
        measure_iUnion_fintype_le _ _
      _ = ∑ _i : Fin init.card,
          (1 - 2 / (init.card : ℝ≥0∞)) ^ T * law init A := by
        apply Finset.sum_congr rfl
        intro i _
        exact label_miss_bound init hc i u A (hσ u) T
      _ = ((1 - 2 / (n : ℝ≥0∞)) ^ T * n) * law init A := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul, hcard]
        ring


/-- Every persistent label denotes an occurrence in the current configuration. -/
theorem label_mem_trace (init : Cfg L K) (ω : Ω L K) (t : ℕ)
    (i : Fin init.card) : labelsAt init ω t i ∈ trace init ω t := by
  rw [← labelsAt_config]
  exact Multiset.mem_map.mpr ⟨i, by simp, rfl⟩

/-- Once correct, a label's output remains correct throughout cleanup. -/
theorem label_output_step (init : Cfg L K) (out : Output) (n : ℕ)
    (ω : Ω L K) (t : ℕ) (i : Fin init.card)
    (h : Phase9SignsDone out n (trace init ω t))
    (hi : (labelsAt init ω t i).output = out) :
    (labelsAt init ω (t + 1) i).output = out := by
  rw [labelsAt_succ, stepLabels]
  cases hsel : selectLabels (labelsAt init ω t) (ω (t + 1)) with
  | none => exact hi
  | some pair =>
    obtain ⟨a, b⟩ := pair
    have hp := Transition_phase9_sign_pair out (labelsAt init ω t a)
      (labelsAt init ω t b)
      (h.2 _ (label_mem_trace init ω t a))
      (h.2 _ (label_mem_trace init ω t b))
    simp only [updateLabels, Function.update_apply]
    split_ifs with hib hia
    · exact hp.2.2
    · exact hp.1.2
    · exact hi

/-- Selecting a label during cleanup writes the correct output. -/
theorem label_output_selected (init : Cfg L K) (out : Output) (n : ℕ)
    (ω : Ω L K) (t : ℕ) (i : Fin init.card)
    (h : Phase9SignsDone out n (trace init ω t))
    (hi : labelParticipates init i t ω) :
    (labelsAt init ω (t + 1) i).output = out := by
  rcases hi with ⟨j, hj, hij | hji⟩
  · have hp := labelsAt_selected_transition init ω t i j hij
    rw [hp.2.1]
    exact (Transition_phase9_sign_pair out _ _
      (h.2 _ (label_mem_trace init ω t i))
      (h.2 _ (label_mem_trace init ω t j))).1.2
  · have hp := labelsAt_selected_transition init ω t j i hji
    rw [hp.2.2.1]
    exact (Transition_phase9_sign_pair out _ _
      (h.2 _ (label_mem_trace init ω t j))
      (h.2 _ (label_mem_trace init ω t i))).2.2

/-- A label that has been selected since entry has the correct output at
all later times in the cleanup interval. -/
theorem selected_label_output (init : Cfg L K) (out : Output) (n : ℕ)
    (ω : Ω L K) (u T : ℕ) (i : Fin init.card)
    (hstart : Phase9SignsDone out n (trace init ω u))
    (hi : ¬ labelMiss init i u T ω) :
    (labelsAt init ω (u + T) i).output = out := by
  classical
  obtain ⟨k, hk, hsel⟩ : ∃ k < T, labelParticipates init i (u + k) ω := by
    by_contra hn
    apply hi
    intro k hk hp
    exact hn ⟨k, hk, hp⟩
  have hfirst := label_output_selected init out n ω (u + k) i
    (signs_trace init out n ω u _ (by omega) hstart) hsel
  have hpersist (v : ℕ) (hv : u + k + 1 ≤ v) :
      (labelsAt init ω v i).output = out := by
    induction v, hv using Nat.le_induction with
    | base => exact hfirst
    | succ v hv ih =>
        exact label_output_step init out n ω v i
          (signs_trace init out n ω u v (by omega) hstart) ih
  exact hpersist _ (by omega)

/-- Selecting every persistent label turns the Phase-9 entry state into
the cleaned endpoint state, independently of the earlier execution. -/
theorem post_of_all_selected (init : Cfg L K) (out : Output) (n : ℕ)
    (ω : Ω L K) (u T : ℕ)
    (hstart : Phase9SignsDone out n (trace init ω u))
    (hselected : ∀ i : Fin init.card, ¬ labelMiss init i u T ω) :
    Phase9Post out n (trace init ω (u + T)) := by
  classical
  refine ⟨signs_trace init out n ω u _ (by omega) hstart, ?_⟩
  apply Nat.eq_zero_of_not_pos
  intro hpos
  obtain ⟨a, ha, hwrong⟩ := Multiset.countP_pos.mp hpos
  rw [← labelsAt_config] at ha
  obtain ⟨i, hi, rfl⟩ := Multiset.mem_map.mp ha
  exact hwrong (selected_label_output init out n ω u T i hstart (hselected i))

/-- Lemma 14's endpoint outside the literal missed-label event. -/
theorem endpoint_outside_missed_labels (init : Cfg L K) (out : Output) (n : ℕ)
    (σ : Ω L K → WithTop ℕ) (ω : Ω L K) (u : ℕ)
    (hsigned : out = .A ∨ out = .B)
    (hmajor : majorityVerdict init = outputTripleOfOutput out)
    (hu : σ ω = (u : WithTop ℕ))
    (hstart : Phase9SignsDone out n (trace init ω u))
    (hgood : ω ∉ missedLabelFailure init σ (cleanupWindow n)) :
    Phase9Post out n (trace init ω (u + cleanupWindow n)) ∧
    phase9ConsensusEndpoint init (trace init ω (u + cleanupWindow n)) ∧
    (doutPartition L K).output (majorityVerdict init)
      (trace init ω (u + cleanupWindow n)) ∧
    (NonuniformMajority L K).IsStable (doutPartition L K)
      (trace init ω (u + cleanupWindow n)) ∧
    trace init ω (u + cleanupWindow n) ∈ StableDone L K init ∧
    ω ∈ hitBy init (u + cleanupWindow n) := by
  have hpost := post_of_all_selected init out n ω u (cleanupWindow n) hstart
    (fun i hi => hgood ⟨u, hu, i, hi⟩)
  have hep := endpoint_of_clean init _ out n hsigned hmajor hpost
  have hstable := stable_output_of_phase9ConsensusEndpoint init _ hep
  have hdone : trace init ω (u + cleanupWindow n) ∈ StableDone L K init :=
    Or.inr (Or.inr (Or.inl hep))
  exact ⟨hpost, hep, hstable.1, hstable.2, hdone, _, le_rfl, hdone⟩

/-- Lemma 14's measurable missed-label event has the exact inverse-cube budget
under the original law, at any stopping time. -/
theorem lemma_fourteen_cleanup_at_stop {n : ℕ} (init : InputCfg n)
    (hinput : ThresholdEpidemic.GoodInput n init)
    (σ : Ω (PhaseThreeModel.Numeric.hourIndex n) 256 → WithTop ℕ)
    (hσ : PairLogPastTime σ) :
    MeasurableSet (missedLabelFailure init σ (cleanupWindow n)) ∧
    law init (missedLabelFailure init σ (cleanupWindow n)) ≤
      1 / (n : ℝ≥0∞) ^ 3 := by
  have hn : 40 ≤ n := (time_population_bounds hinput.1).2
  exact ⟨missedLabelFailure_measurable init σ hσ _,
    (missedLabelFailure_bound init σ hσ hinput.2.2 (by omega) _).trans
      (cleanup_geometric_bound (by omega))⟩

/-- The canonical first Phase-9 sign-complete state needs no carried
stopping-time assumption. Its cleanup failure probability is unconditional. -/
theorem lemma_fourteen_cleanup_bound {n : ℕ} (init : InputCfg n)
    (hinput : ThresholdEpidemic.GoodInput n init) (out : Output) :
    MeasurableSet (missedLabelFailure init (cleanupStart init out n) (cleanupWindow n)) ∧
    law init (missedLabelFailure init (cleanupStart init out n) (cleanupWindow n)) ≤
      1 / (n : ℝ≥0∞) ^ 3 :=
  lemma_fourteen_cleanup_at_stop init hinput _ (cleanupStart_pastTime init out n)

/-- Lemma 14's stable endpoint and hitting deadline at the first sign-complete
state. Finiteness of this entry belongs to the preceding invariant and spreads. -/
theorem lemma_fourteen_endpoint {n : ℕ} (init : InputCfg n) (out : Output)
    (ω : Ω (PhaseThreeModel.Numeric.hourIndex n) 256) (u : ℕ)
    (hsigned : out = .A ∨ out = .B)
    (hmajor : majorityVerdict init = outputTripleOfOutput out)
    (hu : cleanupStart init out n ω = (u : WithTop ℕ))
    (hgood : ω ∉ missedLabelFailure init (cleanupStart init out n) (cleanupWindow n)) :
    Phase9Post out n (trace init ω (u + cleanupWindow n)) ∧
    phase9ConsensusEndpoint init (trace init ω (u + cleanupWindow n)) ∧
    (doutPartition (PhaseThreeModel.Numeric.hourIndex n) 256).output
      (majorityVerdict init) (trace init ω (u + cleanupWindow n)) ∧
    (NonuniformMajority (PhaseThreeModel.Numeric.hourIndex n) 256).IsStable
      (doutPartition (PhaseThreeModel.Numeric.hourIndex n) 256)
      (trace init ω (u + cleanupWindow n)) ∧
    trace init ω (u + cleanupWindow n) ∈
      StableDone (PhaseThreeModel.Numeric.hourIndex n) 256 init ∧
    ω ∈ hitBy init (u + cleanupWindow n) :=
  endpoint_outside_missed_labels init out n _ ω u hsigned hmajor hu
    (cleanupStart_entry init out n ω u hu) hgood

end Ripple.PopulationProtocol.ExactMajority.LateLemmaFourteenCleanup
end
