-- Ripple/PopulationProtocol/ExactMajority/Probability/LateSamplingCounterTail.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.LateSamplingScalar
import Ripple.PopulationProtocol.ExactMajority.Probability.LateF6RecordedHazards
import Ripple.PopulationProtocol.ExactMajority.Probability.LateF6CountSteps

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal BigOperators MeasureTheory ProbabilityTheory

namespace Ripple.PopulationProtocol.ExactMajority.LateSamplingCounterTail

open TimeTheorem PairLog PairLogAuxiliary TraceDrain
open AveragingRecordedExpectation LateF6Hazards LateSamplingScalar

variable {L K : ℕ}

abbrev Counters := ℕ × ℕ × Bool

def chosen {n : ℕ}
    (P : (Fin n → AgentState L K) → Fin n → Fin n → Prop)
    (f : Fin n → AgentState L K) (d : Draw L K) : Prop :=
  ∃ i j, selectLabels f d = some (i,j) ∧ P f i j

structure CounterSpec (init : Cfg L K) where
  start : ℕ
  cap : ℕ
  debt : ℕ
  gate : (t : ℕ) → ((i : Finset.Iic t) → Draw L K) → Counters → Prop
  event : (Fin init.card → AgentState L K) → Fin init.card → Fin init.card → Prop
  bad : (Fin init.card → AgentState L K) → Fin init.card → Fin init.card → Prop
  bad_subset : ∀ f i j, bad f i j → event f i j

variable {init : Cfg L K}

def CounterSpec.Enabled (R : CounterSpec init) (t : ℕ)
    (p : (i : Finset.Iic t) → Draw L K) (z : Counters) : Prop :=
  R.start ≤ t ∧ z.2.2 = true ∧ R.gate t p z ∧ z.1 < R.cap ∧ z.2.1 ≤ R.debt

def CounterSpec.advance (R : CounterSpec init) (t : ℕ)
    (p : (i : Finset.Iic t) → Draw L K) (z : Counters) (d : Draw L K) : Counters := by
  classical
  exact if R.start ≤ t then
    if R.Enabled t p z then
      (z.1 + bitNat (chosen R.event (prefixLabels init t p) d),
       z.2.1 + bitNat (chosen R.bad (prefixLabels init t p) d), true)
    else (z.1, z.2.1, false)
  else z

def CounterSpec.prefixState (R : CounterSpec init) :
    (t : ℕ) → ((i : Finset.Iic t) → Draw L K) → Counters
  | 0, _ => (0,0,true)
  | t+1, p =>
      R.advance t (restrictPrefix (Nat.le_succ t) p)
        (R.prefixState t (restrictPrefix (Nat.le_succ t) p))
        (p ⟨t+1, Finset.mem_Iic.mpr le_rfl⟩)

def CounterSpec.state (R : CounterSpec init) (ω : Ω L K) (t : ℕ) : Counters :=
  R.prefixState t (frestrictLe t ω)

def CounterSpec.active (R : CounterSpec init) (t : ℕ) (ω : Ω L K) : Prop :=
  R.Enabled t (frestrictLe t ω) (R.state ω t)

def CounterSpec.eventBit (R : CounterSpec init) (t : ℕ) (ω : Ω L K) : ℕ :=
  bitNat (R.active t ω ∧ chosen R.event (labelsAt init ω t) (ω (t+1)))

def CounterSpec.badBit (R : CounterSpec init) (t : ℕ) (ω : Ω L K) : ℕ :=
  bitNat (R.active t ω ∧ chosen R.bad (labelsAt init ω t) (ω (t+1)))

theorem CounterSpec.state_succ (R : CounterSpec init) (ω : Ω L K) (t : ℕ) :
    R.state ω (t+1) = R.advance t (frestrictLe t ω) (R.state ω t) (ω (t+1)) := rfl

theorem CounterSpec.chosen_subset (R : CounterSpec init)
    (f : Fin init.card → AgentState L K) (d : Draw L K) :
    chosen R.bad f d → chosen R.event f d := by
  rintro ⟨i,j,hij,hb⟩
  exact ⟨i,j,hij,R.bad_subset f i j hb⟩

theorem CounterSpec.bits_subset (R : CounterSpec init) (t : ℕ) (ω : Ω L K) :
    R.badBit t ω ≤ R.eventBit t ω :=
  bitNat_mono (fun h => ⟨h.1,R.chosen_subset _ _ h.2⟩)

theorem CounterSpec.bits_binary (R : CounterSpec init) (t : ℕ) (ω : Ω L K) :
    (R.eventBit t ω = 0 ∨ R.eventBit t ω = 1) ∧
      (R.badBit t ω = 0 ∨ R.badBit t ω = 1) :=
  ⟨bitNat_zero_one _,bitNat_zero_one _⟩

theorem CounterSpec.advance_enabled (R : CounterSpec init) (t : ℕ)
    (p : (i : Finset.Iic t) → Draw L K) (z : Counters) (d : Draw L K)
    (hs : R.start ≤ t) (he : R.Enabled t p z) :
    R.advance t p z d =
      (z.1 + bitNat (chosen R.event (prefixLabels init t p) d),
       z.2.1 + bitNat (chosen R.bad (prefixLabels init t p) d), true) := by
  unfold CounterSpec.advance
  rw [if_pos hs, if_pos he]

theorem CounterSpec.advance_disabled (R : CounterSpec init) (t : ℕ)
    (p : (i : Finset.Iic t) → Draw L K) (z : Counters) (d : Draw L K)
    (hs : R.start ≤ t) (he : ¬ R.Enabled t p z) :
    R.advance t p z d = (z.1, z.2.1, false) := by
  unfold CounterSpec.advance
  rw [if_pos hs, if_neg he]

theorem CounterSpec.advance_before (R : CounterSpec init) (t : ℕ)
    (p : (i : Finset.Iic t) → Draw L K) (z : Counters) (d : Draw L K)
    (hs : ¬ R.start ≤ t) : R.advance t p z d = z := by
  unfold CounterSpec.advance
  rw [if_neg hs]

theorem CounterSpec.count_succ (R : CounterSpec init) (ω : Ω L K) (t : ℕ) :
    (R.state ω (t+1)).1 = (R.state ω t).1 + R.eventBit t ω := by
  classical
  rw [R.state_succ]
  by_cases hs : R.start ≤ t
  · by_cases he : R.active t ω
    · rw [R.advance_enabled _ _ _ _ hs he]
      unfold CounterSpec.eventBit
      have hb : bitNat (R.active t ω ∧ chosen R.event (labelsAt init ω t) (ω (t+1))) =
          bitNat (chosen R.event (prefixLabels init t (frestrictLe t ω)) (ω (t+1))) := by
        unfold bitNat
        simp only [he, true_and, labelsAt]
      rw [hb]
    · rw [R.advance_disabled _ _ _ _ hs he]
      unfold CounterSpec.eventBit
      have hb : bitNat (R.active t ω ∧ chosen R.event (labelsAt init ω t) (ω (t+1))) = 0 := by
        unfold bitNat
        simp [he]
      rw [hb]; rfl
  · have he : ¬ R.active t ω := fun h => hs h.1
    rw [R.advance_before _ _ _ _ hs]
    unfold CounterSpec.eventBit
    have hb : bitNat (R.active t ω ∧ chosen R.event (labelsAt init ω t) (ω (t+1))) = 0 := by
      unfold bitNat
      simp [he]
    rw [hb]; rfl

theorem CounterSpec.bad_succ (R : CounterSpec init) (ω : Ω L K) (t : ℕ) :
    (R.state ω (t+1)).2.1 = (R.state ω t).2.1 + R.badBit t ω := by
  classical
  rw [R.state_succ]
  by_cases hs : R.start ≤ t
  · by_cases he : R.active t ω
    · rw [R.advance_enabled _ _ _ _ hs he]
      unfold CounterSpec.badBit
      have hb : bitNat (R.active t ω ∧ chosen R.bad (labelsAt init ω t) (ω (t+1))) =
          bitNat (chosen R.bad (prefixLabels init t (frestrictLe t ω)) (ω (t+1))) := by
        unfold bitNat
        simp only [he, true_and, labelsAt]
      rw [hb]
    · rw [R.advance_disabled _ _ _ _ hs he]
      unfold CounterSpec.badBit
      have hb : bitNat (R.active t ω ∧ chosen R.bad (labelsAt init ω t) (ω (t+1))) = 0 := by
        unfold bitNat
        simp [he]
      rw [hb]; rfl
  · have he : ¬ R.active t ω := fun h => hs h.1
    rw [R.advance_before _ _ _ _ hs]
    unfold CounterSpec.badBit
    have hb : bitNat (R.active t ω ∧ chosen R.bad (labelsAt init ω t) (ω (t+1))) = 0 := by
      unfold bitNat
      simp [he]
    rw [hb]; rfl

theorem CounterSpec.live_succ (R : CounterSpec init) (ω : Ω L K) (t : ℕ)
    (he : R.active t ω) : (R.state ω (t+1)).2.2 = true := by
  classical
  rw [R.state_succ, R.advance_enabled _ _ _ _ he.1 he]

theorem CounterSpec.state_before_start (R : CounterSpec init) (ω : Ω L K) :
    ∀ t, t ≤ R.start → R.state ω t = (0,0,true) := by
  intro t
  induction t with
  | zero => intro _; rfl
  | succ t ih =>
      intro ht
      have hnot : ¬ R.start ≤ t := by omega
      rw [R.state_succ]
      simp only [CounterSpec.advance, if_neg hnot]
      exact ih (by omega)

theorem CounterSpec.count_bounded (R : CounterSpec init) (ω : Ω L K) (t : ℕ) :
    (R.state ω t).1 ≤ R.cap := by
  induction t with
  | zero => simp [CounterSpec.state, CounterSpec.prefixState]
  | succ t ih =>
      rw [R.count_succ]
      by_cases he : R.active t ω
      · have hc := he.2.2.2.1
        have hb := (R.bits_binary t ω).1
        omega
      · have hz : R.eventBit t ω = 0 := by
          classical
          simp [CounterSpec.eventBit, he, bitNat]
        rw [hz, add_zero]
        exact ih

theorem CounterSpec.count_monotone (R : CounterSpec init) (ω : Ω L K) :
    Monotone (fun t => (R.state ω t).1) := by
  apply monotone_nat_of_le_succ
  intro t
  rw [R.count_succ]
  omega

theorem CounterSpec.bad_monotone (R : CounterSpec init) (ω : Ω L K) :
    Monotone (fun t => (R.state ω t).2.1) := by
  apply monotone_nat_of_le_succ
  intro t
  rw [R.bad_succ]
  omega

def CounterSpec.prefixGate (R : CounterSpec init) (t : ℕ)
    (p : (i : Finset.Iic t) → Draw L K) : Prop :=
  R.Enabled t p (R.prefixState t p)

def CounterSpec.eventTrial (R : CounterSpec init) (u : ℕ) : Ω L K → ℝ :=
  pairIndicator init (R.start+u) (R.prefixGate (R.start+u)) R.event

def CounterSpec.badTrial (R : CounterSpec init) (u : ℕ) : Ω L K → ℝ :=
  pairIndicator init (R.start+u) (R.prefixGate (R.start+u)) R.bad

theorem CounterSpec.eventTrial_eq_bit (R : CounterSpec init) (u : ℕ) (ω : Ω L K) :
    R.eventTrial u ω = (R.eventBit (R.start+u) ω : ℝ) := by
  classical
  simp only [CounterSpec.eventTrial, pairIndicator, CounterSpec.prefixGate,
    CounterSpec.eventBit, CounterSpec.active, CounterSpec.state, chosen,
    drawLabels_succ, labelsAt, bit, bitNat]
  split_ifs <;> norm_num

theorem CounterSpec.badTrial_eq_bit (R : CounterSpec init) (u : ℕ) (ω : Ω L K) :
    R.badTrial u ω = (R.badBit (R.start+u) ω : ℝ) := by
  classical
  simp only [CounterSpec.badTrial, pairIndicator, CounterSpec.prefixGate,
    CounterSpec.badBit, CounterSpec.active, CounterSpec.state, chosen,
    drawLabels_succ, labelsAt, bit, bitNat]
  split_ifs <;> norm_num

theorem CounterSpec.eventCount_eq (R : CounterSpec init) (ω : Ω L K) (N : ℕ) :
    eventCount R.eventTrial N ω = ((R.state ω (R.start+N)).1 : ℝ) := by
  induction N with
  | zero =>
      rw [Nat.add_zero, R.state_before_start ω R.start le_rfl]
      simp [eventCount]
  | succ N ih =>
      simp only [eventCount, Finset.sum_range_succ] at *
      rw [ih, R.eventTrial_eq_bit]
      rw [show R.start + (N+1) = (R.start+N)+1 by omega, R.count_succ, Nat.cast_add]

theorem CounterSpec.eventTrial_measurable (R : CounterSpec init) (u : ℕ) :
    StronglyMeasurable[shiftedPairLog L K R.start (u+1)] (R.eventTrial u) := by
  simpa only [shiftedPairLog, CounterSpec.eventTrial, Nat.add_assoc] using
    pairIndicator_stronglyMeasurable init (R.start+u) (R.prefixGate (R.start+u)) R.event

theorem CounterSpec.badTrial_measurable (R : CounterSpec init) (u : ℕ) :
    StronglyMeasurable[shiftedPairLog L K R.start (u+1)] (R.badTrial u) := by
  simpa only [shiftedPairLog, CounterSpec.badTrial, Nat.add_assoc] using
    pairIndicator_stronglyMeasurable init (R.start+u) (R.prefixGate (R.start+u)) R.bad

def CounterSpec.urnCoefficient (R : CounterSpec init) (M : ℕ) (u : ℕ) (ω : Ω L K) : ℝ := by
  classical
  exact if R.active (R.start+u) ω then
    ((M:ℝ)-R.cap)/((M:ℝ)-(R.state ω (R.start+u)).1-1) else 0

def CounterSpec.urnRatio (R : CounterSpec init) (M : ℕ) (u : ℕ) (ω : Ω L K) : ℝ := by
  classical
  exact if R.active (R.start+u) ω then
    ((R.debt:ℝ)-(R.state ω (R.start+u)).2.1)/((M:ℝ)-(R.state ω (R.start+u)).1) else 0

theorem CounterSpec.urnCoefficient_measurable (R : CounterSpec init) (M u : ℕ) :
    StronglyMeasurable[shiftedPairLog L K R.start u] (R.urnCoefficient M u) := by
  classical
  let F : ((i : Finset.Iic (R.start+u)) → Draw L K) → ℝ := fun p =>
    if R.Enabled (R.start+u) p (R.prefixState (R.start+u) p) then
      ((M:ℝ)-R.cap)/((M:ℝ)-(R.prefixState (R.start+u) p).1-1) else 0
  exact ((measurable_of_countable F).comp
    (measurable_pairLog_prefix L K (R.start+u))).stronglyMeasurable

theorem CounterSpec.urnRatio_measurable (R : CounterSpec init) (M u : ℕ) :
    StronglyMeasurable[shiftedPairLog L K R.start u] (R.urnRatio M u) := by
  classical
  let F : ((i : Finset.Iic (R.start+u)) → Draw L K) → ℝ := fun p =>
    if R.Enabled (R.start+u) p (R.prefixState (R.start+u) p) then
      ((R.debt:ℝ)-(R.prefixState (R.start+u) p).2.1)/
        ((M:ℝ)-(R.prefixState (R.start+u) p).1) else 0
  exact ((measurable_of_countable F).comp
    (measurable_pairLog_prefix L K (R.start+u))).stronglyMeasurable

theorem CounterSpec.urnCoefficient_bounds (R : CounterSpec init) {M : ℕ}
    (hcap : R.cap < M) (u : ℕ) (ω : Ω L K) :
    0 ≤ R.urnCoefficient M u ω ∧ R.urnCoefficient M u ω ≤ 1 := by
  classical
  by_cases he : R.active (R.start+u) ω
  · simp only [CounterSpec.urnCoefficient, if_pos he]
    exact forecast_coefficient_bounds he.2.2.2.1 hcap
  · simp [CounterSpec.urnCoefficient, he]

theorem CounterSpec.urnRatio_nonneg (R : CounterSpec init) {M : ℕ}
    (hcap : R.cap < M) (u : ℕ) (ω : Ω L K) : 0 ≤ R.urnRatio M u ω := by
  classical
  by_cases he : R.active (R.start+u) ω
  · simp only [CounterSpec.urnRatio, if_pos he]
    exact forecast_ratio_nonneg (lt_trans he.2.2.2.1 hcap) he.2.2.2.2
  · simp [CounterSpec.urnRatio, he]

def pairMass (init : Cfg L K)
    (P : (Fin init.card → AgentState L K) → Fin init.card → Fin init.card → Prop)
    (f : Fin init.card → AgentState L K) : ℝ :=
  ((goodPairs P f).card : ℝ) / ((init.card:ℝ)*((init.card:ℝ)-1))

def CounterSpec.UrnHazard (R : CounterSpec init) (M : ℕ) : Prop :=
  ∀ t p z, R.Enabled t p z →
    pairMass init R.bad (prefixLabels init t p) ≤
      (((R.debt:ℝ)-z.2.1)/((M:ℝ)-z.1)) *
        pairMass init R.event (prefixLabels init t p)

theorem CounterSpec.urn_trials (R : CounterSpec init) (hn : 2 ≤ init.card)
    {M : ℕ} (hcap : R.cap < M) (hhazard : R.UrnHazard M)
    (p : (i : Finset.Iic R.start) → Draw L K) :
    Trials (μ := recordedFuture init R.start p) (ℱ := shiftedPairLog L K R.start)
      R.eventTrial R.badTrial (R.urnCoefficient M) (R.urnRatio M) := by
  classical
  refine ⟨R.eventTrial_measurable, R.badTrial_measurable,
    R.urnCoefficient_measurable M, R.urnRatio_measurable M, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u
    exact Filter.Eventually.of_forall fun ω =>
      pairIndicator_zero_one init (R.start+u) (R.prefixGate (R.start+u)) R.event ω
  · intro u
    exact Filter.Eventually.of_forall fun ω =>
      pairIndicator_zero_one init (R.start+u) (R.prefixGate (R.start+u)) R.bad ω
  · intro u
    exact Filter.Eventually.of_forall fun ω => by
      rw [R.eventTrial_eq_bit, R.badTrial_eq_bit]
      exact_mod_cast R.bits_subset (R.start+u) ω
  · intro u
    exact Filter.Eventually.of_forall (R.urnCoefficient_bounds hcap u)
  · intro u
    exact Filter.Eventually.of_forall (R.urnRatio_nonneg hcap u)
  · intro u
    have hstart : R.start ≤ R.start+u := Nat.le_add_right _ _
    filter_upwards
      [pairIndicator_recorded_condExp init hn R.start (R.start+u) hstart p
        (R.prefixGate (R.start+u)) R.bad,
       pairIndicator_recorded_condExp init hn R.start (R.start+u) hstart p
        (R.prefixGate (R.start+u)) R.event] with ω hb ha
    change (recordedFuture init R.start p)[
      pairIndicator init (R.start+u) (R.prefixGate (R.start+u)) R.bad |
        pairLogFiltration L K (R.start+u)] ω ≤
      R.urnRatio M u ω *
        (recordedFuture init R.start p)[
          pairIndicator init (R.start+u) (R.prefixGate (R.start+u)) R.event |
            pairLogFiltration L K (R.start+u)] ω
    rw [hb,ha]
    change (if R.active (R.start+u) ω then
        pairMass init R.bad (labelsAt init ω (R.start+u)) else 0) ≤
      (if R.active (R.start+u) ω then
        ((R.debt:ℝ)-(R.state ω (R.start+u)).2.1) /
          ((M:ℝ)-(R.state ω (R.start+u)).1) else 0) *
      (if R.active (R.start+u) ω then
        pairMass init R.event (labelsAt init ω (R.start+u)) else 0)
    by_cases he : R.active (R.start+u) ω
    · simp only [if_pos he]
      exact hhazard (R.start+u) (frestrictLe (R.start+u) ω) (R.state ω (R.start+u)) he
    · simp only [if_neg he, zero_mul, le_refl]

theorem forecast_bit_increment (M D k j b A B : ℕ)
    (hjk : j < k) (hkM : k < M) (hA : A ≤ 1) (hBA : B ≤ A) :
    forecast M D k (j+A) (b+B) - forecast M D k j b =
      (((M:ℝ)-k)/((M:ℝ)-j-1)) * ((B:ℝ)-((D:ℝ)-b)/((M:ℝ)-j)*(A:ℝ)) := by
  have hcases : A = 0 ∨ A = 1 := by omega
  rcases hcases with hA | hA
  · have hB : B = 0 := by omega
    simp [hA,hB]
  · have hnext : (j:ℝ)+1 < M := by
      exact_mod_cast (lt_of_le_of_lt (Nat.succ_le_iff.mpr hjk) hkM)
    have hden : (M:ℝ)-j ≠ 0 := by linarith
    have hnextden : (M:ℝ)-j-1 ≠ 0 := by linarith
    subst A
    simpa only [Nat.cast_add, Nat.cast_one, mul_one] using
      forecast_increment (M:ℝ) (D:ℝ) (k:ℝ) (j:ℝ) (b:ℝ) (B:ℝ) hden hnextden

theorem CounterSpec.forecast_step (R : CounterSpec init) {M : ℕ}
    (hcap : R.cap < M) (u : ℕ) (ω : Ω L K) :
    forecast M R.debt R.cap (R.state ω ((R.start+u)+1)).1
        (R.state ω ((R.start+u)+1)).2.1 -
      forecast M R.debt R.cap (R.state ω (R.start+u)).1
        (R.state ω (R.start+u)).2.1 =
      R.urnCoefficient M u ω *
        (R.badTrial u ω - R.urnRatio M u ω * R.eventTrial u ω) := by
  classical
  rw [R.count_succ,R.bad_succ,R.eventTrial_eq_bit,R.badTrial_eq_bit]
  by_cases he : R.active (R.start+u) ω
  · simp only [CounterSpec.urnCoefficient, CounterSpec.urnRatio, if_pos he]
    have hA : R.eventBit (R.start+u) ω ≤ 1 := by
      have h := (R.bits_binary (R.start+u) ω).1
      omega
    have hfb := forecast_bit_increment M R.debt R.cap
      (R.state ω (R.start+u)).1 (R.state ω (R.start+u)).2.1
      (R.eventBit (R.start+u) ω) (R.badBit (R.start+u) ω)
      he.2.2.2.1 hcap hA (R.bits_subset (R.start+u) ω)
    push_cast
    exact hfb
  · have hA : R.eventBit (R.start+u) ω = 0 := by
      simp [CounterSpec.eventBit,he,bitNat]
    have hB : R.badBit (R.start+u) ω = 0 := by
      simp [CounterSpec.badBit,he,bitNat]
    simp [CounterSpec.urnCoefficient,CounterSpec.urnRatio,he,hA,hB]

theorem CounterSpec.urn_score_eq (R : CounterSpec init) {M : ℕ}
    (hcap : R.cap < M) (N : ℕ) (ω : Ω L K) :
    score R.eventTrial R.badTrial (R.urnCoefficient M) (R.urnRatio M) N ω =
      forecast M R.debt R.cap (R.state ω (R.start+N)).1
        (R.state ω (R.start+N)).2.1 - (R.debt:ℝ)*R.cap/M := by
  induction N with
  | zero =>
      rw [Nat.add_zero,R.state_before_start ω R.start le_rfl]
      simp [score,forecast_initial]
  | succ N ih =>
      simp only [score,Finset.sum_range_succ] at *
      rw [ih]
      have h := R.forecast_step hcap N ω
      rw [show R.start+(N+1) = (R.start+N)+1 by omega]
      linarith

def CounterSpec.upperEvent (R : CounterSpec init) (r : ℝ) (N : ℕ) : Set (Ω L K) :=
  {ω | R.cap ≤ (R.state ω (R.start+N)).1 ∧ r ≤ ((R.state ω (R.start+N)).2.1 : ℝ)}

theorem CounterSpec.upperEvent_monotone (R : CounterSpec init) (r : ℝ) :
    Monotone (R.upperEvent r) := by
  intro u v huv ω hω
  have htime : R.start+u ≤ R.start+v := Nat.add_le_add_left huv _
  refine ⟨hω.1.trans (R.count_monotone ω htime), ?_⟩
  exact hω.2.trans (by exact_mod_cast R.bad_monotone ω htime)

theorem CounterSpec.urn_finite_tail (R : CounterSpec init) (hn : 2 ≤ init.card)
    {M : ℕ} (hcap : R.cap < M) (hhazard : R.UrnHazard M)
    (p : (i : Finset.Iic R.start) → Draw L K) (γ : ℝ) (hγ : 0 ≤ γ) (N : ℕ) :
    recordedFuture init R.start p
      (R.upperEvent (((R.debt:ℝ)/M+γ)*R.cap) N) ≤
        ENNReal.ofReal (Real.exp (-2*γ^2*R.cap)) := by
  let μ := recordedFuture init R.start p
  have htrials := R.urn_trials hn hcap hhazard p
  have htail := htrials.raw_tail γ (R.cap:ℝ) hγ N
  have hsub : R.upperEvent (((R.debt:ℝ)/M+γ)*R.cap) N ⊆
      {ω | (R.cap:ℝ) ≤ eventCount R.eventTrial N ω ∧
        γ * eventCount R.eventTrial N ω ≤
          score R.eventTrial R.badTrial (R.urnCoefficient M) (R.urnRatio M) N ω} := by
    intro ω hω
    simp only [Set.mem_setOf_eq]
    have hcount : (R.state ω (R.start+N)).1 = R.cap :=
      le_antisymm (R.count_bounded ω _) hω.1
    rw [R.eventCount_eq,R.urn_score_eq hcap,hcount,forecast_terminal]
    refine ⟨le_rfl,?_⟩
    have hr := hω.2
    have e : ((R.debt:ℝ)/M+γ)*R.cap = (R.debt:ℝ)*R.cap/M + γ*R.cap := by ring
    linarith [hr, e]
  have hreal : μ.real (R.upperEvent (((R.debt:ℝ)/M+γ)*R.cap) N) ≤
      Real.exp (-2*γ^2*R.cap) :=
    (measureReal_mono (μ := μ) hsub).trans htail
  calc
    μ (R.upperEvent (((R.debt:ℝ)/M+γ)*R.cap) N) =
        ENNReal.ofReal (μ.real (R.upperEvent (((R.debt:ℝ)/M+γ)*R.cap) N)) :=
      (ENNReal.ofReal_toReal (measure_ne_top μ _)).symm
    _ ≤ ENNReal.ofReal (Real.exp (-2*γ^2*R.cap)) :=
      ENNReal.ofReal_le_ofReal hreal

theorem CounterSpec.urn_tail (R : CounterSpec init) (hn : 2 ≤ init.card)
    {M : ℕ} (hcap : R.cap < M) (hhazard : R.UrnHazard M)
    (p : (i : Finset.Iic R.start) → Draw L K) (γ : ℝ) (hγ : 0 ≤ γ) :
    recordedFuture init R.start p
      {ω | ∃ N, R.cap ≤ (R.state ω (R.start+N)).1 ∧
        ((R.debt:ℝ)/M+γ)*R.cap ≤ ((R.state ω (R.start+N)).2.1 : ℝ)} ≤
      ENNReal.ofReal (Real.exp (-2*γ^2*R.cap)) := by
  have heq :
      {ω | ∃ N, R.cap ≤ (R.state ω (R.start+N)).1 ∧
        ((R.debt:ℝ)/M+γ)*R.cap ≤ ((R.state ω (R.start+N)).2.1 : ℝ)} =
      ⋃ N, R.upperEvent (((R.debt:ℝ)/M+γ)*R.cap) N := by
    ext ω
    simp [CounterSpec.upperEvent]
  rw [heq,(R.upperEvent_monotone (((R.debt:ℝ)/M+γ)*R.cap)).measure_iUnion]
  exact iSup_le (fun N => R.urn_finite_tail hn hcap hhazard p γ hγ N)

def actualSpec (init : Cfg L K) (s cap D : ℕ)
    (W : (Fin init.card → AgentState L K) → Prop)
    (C B : (Fin init.card → AgentState L K) → ℕ)
    (P Q : (Fin init.card → AgentState L K) → Fin init.card → Fin init.card → Prop)
    (hQP : ∀ f i j, Q f i j → P f i j) : CounterSpec init where
  start := s
  cap := cap
  debt := D
  gate := fun t p z =>
    W (prefixLabels init t p) ∧
      z.1 = C (prefixLabels init t p) ∧ z.2.1 = B (prefixLabels init t p)
  event := P
  bad := Q
  bad_subset := hQP

theorem actualSpec_coupling (init : Cfg L K) (s cap D : ℕ)
    (W : (Fin init.card → AgentState L K) → Prop)
    (C B : (Fin init.card → AgentState L K) → ℕ)
    (P Q : (Fin init.card → AgentState L K) → Fin init.card → Fin init.card → Prop)
    (hQP : ∀ f i j, Q f i j → P f i j)
    (hC : ∀ f, W f → ∀ d, C (stepLabels f d) = C f + bitNat (chosen P f d))
    (hB : ∀ f, W f → ∀ d, B (stepLabels f d) = B f + bitNat (chosen Q f d))
    (ω : Ω L K) (T : ℕ) (hsT : s ≤ T)
    (hzeroC : C (labelsAt init ω s) = 0) (hzeroB : B (labelsAt init ω s) = 0)
    (hwindow : ∀ t, s ≤ t → t < T →
      W (labelsAt init ω t) ∧ C (labelsAt init ω t) < cap ∧
        B (labelsAt init ω t) ≤ D) :
    let R := actualSpec init s cap D W C B P Q hQP
    (R.state ω T).1 = C (labelsAt init ω T) ∧
      (R.state ω T).2.1 = B (labelsAt init ω T) ∧ (R.state ω T).2.2 = true := by
  classical
  let R := actualSpec init s cap D W C B P Q hQP
  change (R.state ω T).1 = C (labelsAt init ω T) ∧
    (R.state ω T).2.1 = B (labelsAt init ω T) ∧ (R.state ω T).2.2 = true
  obtain ⟨N,rfl⟩ := Nat.exists_eq_add_of_le hsT
  clear hsT
  have haux : ∀ u, u ≤ N →
      (R.state ω (s+u)).1 = C (labelsAt init ω (s+u)) ∧
      (R.state ω (s+u)).2.1 = B (labelsAt init ω (s+u)) ∧
      (R.state ω (s+u)).2.2 = true := by
    intro u
    induction u with
    | zero =>
        intro _
        have hinit := R.state_before_start ω s (show s ≤ R.start from le_rfl)
        simpa only [Nat.add_zero,hinit,Prod.fst,Prod.snd,hzeroC,hzeroB] using
          (show (0:ℕ)=0 ∧ (0:ℕ)=0 ∧ true=true from ⟨rfl,rfl,rfl⟩)
    | succ u ih =>
        intro hu
        have hi := ih (by omega)
        have hw := hwindow (s+u) (by omega) (by omega)
        have he : R.active (s+u) ω := by
          exact ⟨by show s ≤ s + u; omega,hi.2.2,⟨hw.1,hi.1,hi.2.1⟩,
            by simpa only [hi.1] using hw.2.1,
            by simpa only [hi.2.1] using hw.2.2⟩
        have hevent : R.eventBit (s+u) ω =
            bitNat (chosen P (labelsAt init ω (s+u)) (ω ((s+u)+1))) := by
          simp only [CounterSpec.eventBit,he,true_and]
          rfl
        have hbad : R.badBit (s+u) ω =
            bitNat (chosen Q (labelsAt init ω (s+u)) (ω ((s+u)+1))) := by
          simp only [CounterSpec.badBit,he,true_and]
          rfl
        rw [show s+(u+1) = (s+u)+1 by omega]
        refine ⟨?_,?_,R.live_succ ω (s+u) he⟩
        · rw [R.count_succ,hi.1,hevent,labelsAt_succ,hC _ hw.1]
        · rw [R.bad_succ,hi.2.1,hbad,labelsAt_succ,hB _ hw.1]
  exact haux N le_rfl

theorem actualSpec_urn_hazard (init : Cfg L K) (s cap D M : ℕ)
    (W : (Fin init.card → AgentState L K) → Prop)
    (C B : (Fin init.card → AgentState L K) → ℕ)
    (P Q : (Fin init.card → AgentState L K) → Fin init.card → Fin init.card → Prop)
    (hQP : ∀ f i j, Q f i j → P f i j)
    (hkernel : ∀ f, W f → C f < cap → B f ≤ D →
      pairMass init Q f ≤ (((D:ℝ)-B f)/((M:ℝ)-C f))*pairMass init P f) :
    (actualSpec init s cap D W C B P Q hQP).UrnHazard M := by
  intro t p z hz
  have hgate := hz.2.2.1
  have hcount := hz.2.2.2.1
  have hbad := hz.2.2.2.2
  dsimp only [actualSpec] at hgate hcount hbad ⊢
  rw [hgate.2.1,hgate.2.2]
  exact hkernel _ hgate.1
    (by simpa only [hgate.2.1] using hcount)
    (by simpa only [hgate.2.2] using hbad)

theorem actual_urn_tail (init : Cfg L K) (hn : 2 ≤ init.card)
    (s cap D M : ℕ) (hcap : cap < M)
    (W : (Fin init.card → AgentState L K) → Prop)
    (C B : (Fin init.card → AgentState L K) → ℕ)
    (P Q : (Fin init.card → AgentState L K) → Fin init.card → Fin init.card → Prop)
    (hQP : ∀ f i j, Q f i j → P f i j)
    (hC : ∀ f, W f → ∀ d, C (stepLabels f d) = C f + bitNat (chosen P f d))
    (hB : ∀ f, W f → ∀ d, B (stepLabels f d) = B f + bitNat (chosen Q f d))
    (hkernel : ∀ f, W f → C f < cap → B f ≤ D →
      pairMass init Q f ≤ (((D:ℝ)-B f)/((M:ℝ)-C f))*pairMass init P f)
    (p : (i : Finset.Iic s) → Draw L K) (γ : ℝ) (hγ : 0 ≤ γ) :
    recordedFuture init s p {ω |
      C (labelsAt init ω s) = 0 ∧ B (labelsAt init ω s) = 0 ∧
      ∃ T, s ≤ T ∧
        (∀ t, s ≤ t → t < T →
          W (labelsAt init ω t) ∧ C (labelsAt init ω t) < cap ∧
            B (labelsAt init ω t) ≤ D) ∧
        C (labelsAt init ω T) = cap ∧
        ((D:ℝ)/M+γ)*cap ≤ B (labelsAt init ω T)} ≤
      ENNReal.ofReal (Real.exp (-2*γ^2*cap)) := by
  let R := actualSpec init s cap D W C B P Q hQP
  have hh := actualSpec_urn_hazard init s cap D M W C B P Q hQP hkernel
  have ht := R.urn_tail hn hcap hh p γ hγ
  refine (measure_mono ?_).trans ht
  rintro ω ⟨hzeroC,hzeroB,T,hsT,hw,hcount,hbad⟩
  have hc := actualSpec_coupling init s cap D W C B P Q hQP hC hB
    ω T hsT hzeroC hzeroB hw
  obtain ⟨N,hN⟩ := Nat.exists_eq_add_of_le hsT
  refine ⟨N,?_,?_⟩
  · change cap ≤ (R.state ω (s+N)).1
    rw [← hN,hc.1,hcount]
  · change ((D:ℝ)/M+γ)*cap ≤ ((R.state ω (s+N)).2.1 : ℝ)
    rw [← hN,hc.2.1]
    exact hbad

end Ripple.PopulationProtocol.ExactMajority.LateSamplingCounterTail
end
