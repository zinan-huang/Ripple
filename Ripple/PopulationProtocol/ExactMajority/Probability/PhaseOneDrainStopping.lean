import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseOneDrainProducer
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseZeroEntry

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal

namespace Ripple.PopulationProtocol.ExactMajority.PhaseOneDrainStopping

open TimeTheorem PairLog PhaseOneDrain PhaseZeroEntry

variable {L K : ℕ}

theorem exitTime_eq_iff_firstHit
    (init : Cfg L K) (P : Cfg L K → Prop) (ω : Ω L K) (t : ℕ) :
    TraceDrain.exitTime init P ω = (t : WithTop ℕ) ↔
      StageEventSpec.firstHit P (trace init ω) t := by
  classical
  unfold TraceDrain.exitTime
  split_ifs with hex
  · constructor
    · intro ht
      have heq : Nat.find hex = t := WithTop.coe_injective ht
      subst t
      exact ⟨Nat.find_spec hex, fun u hu => Nat.find_min hex hu⟩
    · intro ht
      have heq : Nat.find hex = t := by
        apply Nat.le_antisymm (Nat.find_min' hex ht.1)
        by_contra hle
        exact ht.2 (Nat.find hex) (Nat.lt_of_not_ge hle) (Nat.find_spec hex)
      exact congrArg (fun u : ℕ => (u : WithTop ℕ)) heq
  · constructor
    · intro ht
      exact (WithTop.coe_ne_top ht.symm).elim
    · intro ht
      exact (hex ⟨t, ht.1⟩).elim

theorem exitTime_pairLogPastTime
    (init : Cfg L K) (P : Cfg L K → Prop) :
    PairLogPastTime (TraceDrain.exitTime init P) := by
  intro t
  have hnow : MeasurableSet[pairLogFiltration L K t]
      {ω | P (trace init ω t)} :=
    (show MeasurableSet {c : Cfg L K | P c} from
      (Set.to_countable _).measurableSet).preimage
        (measurable_trace_at init t)
  have hpast (u : ℕ) : MeasurableSet[pairLogFiltration L K t]
      {ω | u < t → ¬ P (trace init ω u)} := by
    by_cases hu : u < t
    · simpa only [hu, true_implies] using
        (show MeasurableSet {c : Cfg L K | ¬ P c} from
          (Set.to_countable _).measurableSet).preimage
            (measurable_trace_at_of_le init hu.le)
    · simp only [hu, false_implies, Set.setOf_true]
      exact MeasurableSet.univ
  have heq :
      {ω | TraceDrain.exitTime init P ω = (t : WithTop ℕ)} =
        {ω | P (trace init ω t)} ∩
          ⋂ u : ℕ, {ω | u < t → ¬ P (trace init ω u)} := by
    ext ω
    simpa only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter,
      StageEventSpec.firstHit] using exitTime_eq_iff_firstHit init P ω t
  rw [heq]
  exact hnow.inter (MeasurableSet.iInter hpast)

noncomputable def phaseOneStart {n : ℕ} (init : InputCfg n) :
    InputLog n → WithTop ℕ :=
  TraceDrain.exitTime init (StageEventSpec.allGE (n := n) 1)

noncomputable def firstDrained {n : ℕ} (init : InputCfg n) :
    InputLog n → WithTop ℕ :=
  TraceDrain.exitTime init PhaseOneDrained

theorem phaseOneStart_eq_iff {n : ℕ} (init : InputCfg n)
    (ω : InputLog n) (s : ℕ) :
    phaseOneStart init ω = (s : WithTop ℕ) ↔ IsFirstAllPhaseOne init ω s :=
  exitTime_eq_iff_firstHit init (StageEventSpec.allGE (n := n) 1) ω s

theorem firstDrained_eq_iff {n : ℕ} (init : InputCfg n)
    (ω : InputLog n) (t : ℕ) :
    firstDrained init ω = (t : WithTop ℕ) ↔
      StageEventSpec.firstHit PhaseOneDrained (trace init ω) t :=
  exitTime_eq_iff_firstHit init PhaseOneDrained ω t

theorem phaseOneStart_past {n : ℕ} (init : InputCfg n) :
    PairLogPastTime (phaseOneStart init) :=
  exitTime_pairLogPastTime init (StageEventSpec.allGE (n := n) 1)

theorem firstDrained_past {n : ℕ} (init : InputCfg n) :
    PairLogPastTime (firstDrained init) :=
  exitTime_pairLogPastTime init PhaseOneDrained

theorem phaseOneStart_isStoppingTime {n : ℕ} (init : InputCfg n) :
    IsStoppingTime (pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256)
      (phaseOneStart init) :=
  TraceDrain.exitTime_isStoppingTime init (StageEventSpec.allGE (n := n) 1)

theorem firstDrained_isStoppingTime {n : ℕ} (init : InputCfg n) :
    IsStoppingTime (pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256)
      (firstDrained init) :=
  TraceDrain.exitTime_isStoppingTime init PhaseOneDrained

theorem profile_to_drainEntry {n : ℕ} (init : InputCfg n)
    (hinput : ThresholdEpidemic.GoodInput n init) (ω : InputLog n) (s : ℕ)
    (hp : PhaseOneEntryProfile init ω s)
    (hgap : 40 * (initialGap init).natAbs ≤
      RoleSplitConcentration.mainCount (trace init ω s)) :
    PhaseOneDrainEntry n (initialGap init) (trace init ω s) := by
  have hcard : (trace init ω s).card = n :=
    (Protocol.reachable_card_eq
      (phase_zero_trace_reachable init ω s)).trans hinput.2.2
  refine ⟨⟨hcard, hp.all_one⟩, hp.final_roles, ?_, ?_, ?_, ?_, ?_,
    hp.nonmain_zero, ?_, hgap⟩
  · have h : (99 : ℝ) * (n : ℝ) ≤
        200 * (RoleSplitConcentration.mainCount (trace init ω s) : ℝ) := by
      linarith only [hp.main_lower]
    exact_mod_cast h
  · have h : (200 : ℝ) *
        (RoleSplitConcentration.mainCount (trace init ω s) : ℝ) ≤
          101 * (n : ℝ) := by
      linarith only [hp.main_upper]
    exact_mod_cast h
  · have h : (97 : ℝ) * (n : ℝ) ≤
        400 * (RoleSplitConcentration.clockCount (trace init ω s) : ℝ) := by
      linarith only [hp.clock_lower]
    exact_mod_cast h
  · have h : (97 : ℝ) * (n : ℝ) ≤
        400 * (RoleSplitConcentration.reserveCount (trace init ω s) : ℝ) := by
      linarith only [hp.reserve_lower]
    exact_mod_cast h
  · simpa only [PhaseThreeModel.Numeric.clockHours] using hp.clock_counter
  · simpa only [AveragingRate.centredBiasSum, AveragingRate.biasZ,
      mainSmallBiasSum, AgentState.smallBiasInt] using hp.main_mass

structure DrainedPrefix {n : ℕ} (init : InputCfg n)
    (ω : InputLog n) (s t : ℕ) : Prop where
  start_first : IsFirstAllPhaseOne init ω s
  start_profile : PhaseOneEntryProfile init ω s
  weak_gap : 40 * (initialGap init).natAbs ≤
    RoleSplitConcentration.mainCount (trace init ω s)
  drain_first : StageEventSpec.firstHit PhaseOneDrained (trace init ω) t
  order : s ≤ t
  deadline : t ≤ s + weakHorizon n

theorem DrainedPrefix.start_eq {n : ℕ} {init : InputCfg n}
    {ω : InputLog n} {s t : ℕ} (h : DrainedPrefix init ω s t) :
    phaseOneStart init ω = (s : WithTop ℕ) :=
  (phaseOneStart_eq_iff init ω s).2 h.start_first

theorem DrainedPrefix.drain_eq {n : ℕ} {init : InputCfg n}
    {ω : InputLog n} {s t : ℕ} (h : DrainedPrefix init ω s t) :
    firstDrained init ω = (t : WithTop ℕ) :=
  (firstDrained_eq_iff init ω t).2 h.drain_first

theorem DrainedPrefix.finite {n : ℕ} {init : InputCfg n}
    {ω : InputLog n} {s t : ℕ} (h : DrainedPrefix init ω s t) :
    firstDrained init ω ≠ ⊤ := by
  rw [h.drain_eq]
  exact WithTop.coe_ne_top

theorem DrainedPrefix.absolute_deadline {n : ℕ} {init : InputCfg n}
    {ω : InputLog n} {s t : ℕ} (h : DrainedPrefix init ω s t)
    (hs : s ≤ 350 * n * PhaseThreeModel.Numeric.clockHours n) :
    t ≤ 350 * n * PhaseThreeModel.Numeric.clockHours n + weakHorizon n :=
  h.deadline.trans (Nat.add_le_add_right hs _)

theorem drainedPrefix_past {n : ℕ} (init : InputCfg n) (s t : ℕ) :
    MeasurableSet[pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256 t]
      {ω | DrainedPrefix init ω s t} := by
  by_cases hst : s ≤ t
  · by_cases hdeadline : t ≤ s + weakHorizon n
    · have hfirst :
          MeasurableSet[pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256 t]
            {ω | IsFirstAllPhaseOne init ω s} :=
        ((pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256).mono hst)
          _ (first_all_phase_one_measurableSet init s)
      have hprofile :
          MeasurableSet[pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256 t]
            {ω | PhaseOneEntryProfile init ω s} :=
        ((pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256).mono hst)
          _ (phase_one_entry_profile_measurableSet init s)
      have hgap :
          MeasurableSet[pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256 t]
            {ω | 40 * (initialGap init).natAbs ≤
              RoleSplitConcentration.mainCount (trace init ω s)} :=
        (show MeasurableSet {c : InputCfg n |
          40 * (initialGap init).natAbs ≤ RoleSplitConcentration.mainCount c} from
            (Set.to_countable _).measurableSet).preimage
              (measurable_trace_at_of_le init hst)
      have heq :
          {ω | DrainedPrefix init ω s t} =
            {ω | IsFirstAllPhaseOne init ω s} ∩
              ({ω | PhaseOneEntryProfile init ω s} ∩
                ({ω | 40 * (initialGap init).natAbs ≤
                  RoleSplitConcentration.mainCount (trace init ω s)} ∩
                    {ω | firstDrained init ω = (t : WithTop ℕ)})) := by
        ext ω
        constructor
        · intro h
          exact ⟨h.start_first, h.start_profile, h.weak_gap, h.drain_eq⟩
        · rintro ⟨hfirst, hprofile, hgap, ht⟩
          exact ⟨hfirst, hprofile, hgap, (firstDrained_eq_iff init ω t).1 ht,
            hst, hdeadline⟩
      rw [heq]
      exact hfirst.inter (hprofile.inter (hgap.inter (firstDrained_past init t)))
    · have heq : {ω | DrainedPrefix init ω s t} = ∅ := by
        ext ω
        constructor
        · intro h
          exact (hdeadline h.deadline).elim
        · intro h
          exact h.elim
      rw [heq]
      exact @MeasurableSet.empty _ (pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256 t)
  · have heq : {ω | DrainedPrefix init ω s t} = ∅ := by
      ext ω
      constructor
      · intro h
        exact (hst h.order).elim
      · intro h
        exact h.elim
    rw [heq]
    exact @MeasurableSet.empty _ (pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256 t)

theorem exists_firstDrained_of_hit {n : ℕ} (init : InputCfg n)
    (ω : InputLog n) (s k : ℕ) (hs : IsFirstAllPhaseOne init ω s)
    (hk : k ≤ weakHorizon n)
    (hhit : PhaseOneDrained (trace init ω (s + k))) :
    ∃ t : ℕ, firstDrained init ω = (t : WithTop ℕ) ∧
      s ≤ t ∧ t ≤ s + weakHorizon n := by
  classical
  have hex : ∃ t, PhaseOneDrained (trace init ω t) := ⟨s + k, hhit⟩
  let t := Nat.find hex
  have ht : StageEventSpec.firstHit PhaseOneDrained (trace init ω) t :=
    ⟨Nat.find_spec hex, fun u hu => Nat.find_min hex hu⟩
  have hst : s ≤ t := by
    by_contra hle
    apply hs.2 t (Nat.lt_of_not_ge hle)
    intro a ha
    exact le_of_eq (ht.1.1 a ha).symm
  refine ⟨t, (firstDrained_eq_iff init ω t).2 ht, hst, ?_⟩
  exact (Nat.find_min' hex hhit).trans (Nat.add_le_add_left hk s)

def firstDrainedWindowFailure {n : ℕ} (init : InputCfg n) : Set (InputLog n) :=
  {ω | ∃ s : ℕ, phaseOneStart init ω = (s : WithTop ℕ) ∧
    PhaseOneDrainEntry n (initialGap init) (trace init ω s) ∧
    ¬ ∃ t : ℕ, firstDrained init ω = (t : WithTop ℕ) ∧
      s ≤ t ∧ t ≤ s + weakHorizon n}

theorem firstDrainedWindowFailure_eq {n : ℕ} (init : InputCfg n) :
    firstDrainedWindowFailure init =
      phaseOneDrainFailure init n (initialGap init) (phaseOneStart init) := by
  ext ω
  constructor
  · rintro ⟨s, hs, he, hmiss⟩
    refine ⟨s, hs, he, ?_⟩
    intro k hk hhit
    exact hmiss (exists_firstDrained_of_hit init ω s k
      ((phaseOneStart_eq_iff init ω s).1 hs) hk hhit)
  · rintro ⟨s, hs, he, hmiss⟩
    refine ⟨s, hs, he, ?_⟩
    rintro ⟨t, ht, hst, hdeadline⟩
    have hbad := hmiss (t - s) (by omega)
    have hsum : s + (t - s) = t := by omega
    rw [hsum] at hbad
    exact hbad ((firstDrained_eq_iff init ω t).1 ht).1

theorem firstDrainedWindowFailure_measurable {n : ℕ} (init : InputCfg n) :
    MeasurableSet (firstDrainedWindowFailure init) := by
  rw [firstDrainedWindowFailure_eq]
  exact phaseOneDrainFailure_measurable init n (initialGap init)
    (phaseOneStart init) (phaseOneStart_past init)

theorem firstDrainedWindowFailure_le {n : ℕ} (init : InputCfg n)
    (hinput : ThresholdEpidemic.GoodInput n init) :
    law init (firstDrainedWindowFailure init) ≤ 1 / (n : ℝ≥0∞) ^ 2 := by
  rw [firstDrainedWindowFailure_eq]
  exact PhaseOneDrainProducer.phaseOneDrain_conditional_producer init hinput
    (phaseOneStart init) (phaseOneStart_past init)

theorem exists_drainedPrefix_of_not_failure {n : ℕ} (init : InputCfg n)
    (hinput : ThresholdEpidemic.GoodInput n init) (ω : InputLog n) (s : ℕ)
    (hs : IsFirstAllPhaseOne init ω s) (hp : PhaseOneEntryProfile init ω s)
    (hgap : 40 * (initialGap init).natAbs ≤
      RoleSplitConcentration.mainCount (trace init ω s))
    (hgood : ω ∉ firstDrainedWindowFailure init) :
    ∃ t : ℕ, DrainedPrefix init ω s t := by
  classical
  have he := profile_to_drainEntry init hinput ω s hp hgap
  have hstart := (phaseOneStart_eq_iff init ω s).2 hs
  have hhit : ∃ t : ℕ, firstDrained init ω = (t : WithTop ℕ) ∧
      s ≤ t ∧ t ≤ s + weakHorizon n := by
    by_contra hmiss
    exact hgood ⟨s, hstart, he, hmiss⟩
  obtain ⟨t, ht, hst, hdeadline⟩ := hhit
  exact ⟨t, hs, hp, hgap, (firstDrained_eq_iff init ω t).1 ht, hst, hdeadline⟩

def drainOrStrongBy {n : ℕ} (init : InputCfg n) : Set (InputLog n) :=
  {ω | ∃ s ≤ 350 * n * PhaseThreeModel.Numeric.clockHours n,
    IsFirstAllPhaseOne init ω s ∧ PhaseOneEntryProfile init ω s ∧
    (RoleSplitConcentration.mainCount (trace init ω s) <
      40 * (initialGap init).natAbs ∨ ∃ t : ℕ, DrainedPrefix init ω s t)}

theorem drain_or_strong_by_estimate {n : ℕ} (init : InputCfg n)
    (hinput : ThresholdEpidemic.GoodInput n init) :
    law init (drainOrStrongBy init)ᶜ ≤
      law init {ω | ¬ ∃ s ≤ 350 * n * PhaseThreeModel.Numeric.clockHours n,
        IsFirstAllPhaseOne init ω s ∧ PhaseOneEntryProfile init ω s} +
          1 / (n : ℝ≥0∞) ^ 2 := by
  classical
  let F : Set (InputLog n) :=
    {ω | ¬ ∃ s ≤ 350 * n * PhaseThreeModel.Numeric.clockHours n,
      IsFirstAllPhaseOne init ω s ∧ PhaseOneEntryProfile init ω s}
  have hcover : (drainOrStrongBy init)ᶜ ⊆ F ∪ firstDrainedWindowFailure init := by
    intro ω hω
    by_cases hex : ∃ s ≤ 350 * n * PhaseThreeModel.Numeric.clockHours n,
        IsFirstAllPhaseOne init ω s ∧ PhaseOneEntryProfile init ω s
    · right
      obtain ⟨s, hs, hfirst, hp⟩ := hex
      by_cases hgap : 40 * (initialGap init).natAbs ≤
          RoleSplitConcentration.mainCount (trace init ω s)
      · by_contra hgood
        obtain ⟨t, ht⟩ :=
          exists_drainedPrefix_of_not_failure init hinput ω s hfirst hp hgap hgood
        exact hω ⟨s, hs, hfirst, hp, Or.inr ⟨t, ht⟩⟩
      · exact (hω ⟨s, hs, hfirst, hp, Or.inl (Nat.lt_of_not_ge hgap)⟩).elim
    · exact Or.inl hex
  calc
    law init (drainOrStrongBy init)ᶜ ≤
        law init (F ∪ firstDrainedWindowFailure init) := measure_mono hcover
    _ ≤ law init F + law init (firstDrainedWindowFailure init) := measure_union_le _ _
    _ ≤ law init F + 1 / (n : ℝ≥0∞) ^ 2 :=
      add_le_add le_rfl (firstDrainedWindowFailure_le init hinput)

theorem phase_lower_stepRel (p : ℕ) (c c' : Cfg L K)
    (hstep : (NonuniformMajority L K).StepRel c c')
    (hlo : ∀ a ∈ c, p ≤ a.phase.val) :
    ∀ a ∈ c', p ≤ a.phase.val := by
  classical
  rcases hstep with ⟨r, q, happ, hc'⟩
  dsimp [Protocol.Applicable, NonuniformMajority] at happ hc'
  have hr : r ∈ c := Multiset.mem_of_le happ (by simp)
  have hq : q ∈ c := Multiset.mem_of_le happ (by simp)
  have hmono := Transition_phase_monotone (L := L) (K := K) r q
  rw [hc']
  intro a ha
  simp only [Multiset.mem_add, Multiset.mem_cons, Multiset.mem_singleton] at ha
  rcases ha with hold | hnew
  · exact hlo a (Multiset.mem_of_le (Multiset.sub_le_self c {r, q}) hold)
  · rcases hnew with hnew | hnew
    · simpa only [hnew] using (hlo r hr).trans hmono.1
    · simpa only [hnew] using (hlo q hq).trans hmono.2

theorem phase_upper_stepRel (p : ℕ) (c c' : Cfg L K)
    (hstep : (NonuniformMajority L K).StepRel c c')
    (hhi : ∀ a ∈ c', a.phase.val ≤ p) :
    ∀ a ∈ c, a.phase.val ≤ p := by
  classical
  rcases hstep with ⟨r, q, happ, hc'⟩
  dsimp [Protocol.Applicable, NonuniformMajority] at happ hc'
  have hmono := Transition_phase_monotone (L := L) (K := K) r q
  have hrout : (Transition L K r q).1 ∈ c' := by
    rw [hc']
    exact Multiset.mem_add.2 (Or.inr (Multiset.mem_cons_self _ _))
  have hqout : (Transition L K r q).2 ∈ c' := by
    rw [hc']
    exact Multiset.mem_add.2 (Or.inr (Multiset.mem_cons_of_mem (by simp)))
  have hr : r.phase.val ≤ p := hmono.1.trans (hhi _ hrout)
  have hq : q.phase.val ≤ p := hmono.2.trans (hhi _ hqout)
  intro a ha
  by_cases har : a = r
  · simpa only [har] using hr
  by_cases haq : a = q
  · simpa only [haq] using hq
  have hrest : a ∈ c - r ::ₘ {q} := by
    have hfirst : a ∈ c.erase r := (Multiset.mem_erase_of_ne har).2 ha
    have hsecond : a ∈ (c.erase r).erase q :=
      (Multiset.mem_erase_of_ne haq).2 hfirst
    simpa using hsecond
  have ha' : a ∈ c' := by
    rw [hc']
    exact Multiset.mem_add.2 (Or.inl hrest)
  exact hhi a ha'

theorem phase_lower_reachable (p : ℕ) (c c' : Cfg L K)
    (hreach : (NonuniformMajority L K).Reachable c c')
    (hlo : ∀ a ∈ c, p ≤ a.phase.val) :
    ∀ a ∈ c', p ≤ a.phase.val := by
  revert hlo
  induction hreach with
  | refl =>
      exact fun h => h
  | tail hprev hstep ih =>
      intro hlo
      exact phase_lower_stepRel p _ _ hstep (ih hlo)

theorem phase_upper_reachable (p : ℕ) (c c' : Cfg L K)
    (hreach : (NonuniformMajority L K).Reachable c c')
    (hhi : ∀ a ∈ c', a.phase.val ≤ p) :
    ∀ a ∈ c, a.phase.val ≤ p := by
  revert hhi
  induction hreach with
  | refl =>
      exact fun h => h
  | tail hprev hstep ih =>
      intro hhi
      exact ih (phase_upper_stepRel p _ _ hstep hhi)

theorem phase_eq_between (init : Cfg L K) (ω : Ω L K) (p s u t : ℕ)
    (hsu : s ≤ u) (hut : u ≤ t)
    (hs : ∀ a ∈ trace init ω s, a.phase.val = p)
    (ht : ∀ a ∈ trace init ω t, a.phase.val = p) :
    ∀ a ∈ trace init ω u, a.phase.val = p := by
  have hlo := phase_lower_reachable p _ _ (trace_reachable init ω hsu)
    (fun a ha => le_of_eq (hs a ha).symm)
  have hhi := phase_upper_reachable p _ _ (trace_reachable init ω hut)
    (fun a ha => le_of_eq (ht a ha))
  intro a ha
  exact Nat.le_antisymm (hhi a ha) (hlo a ha)

theorem DrainedPrefix.phase_one_window {n : ℕ} {init : InputCfg n}
    {ω : InputLog n} {s t : ℕ} (h : DrainedPrefix init ω s t)
    (hcard : init.card = n) (u : ℕ) (hsu : s ≤ u) (hut : u ≤ t) :
    PhaseOnlyWindows.Phase1Win n (trace init ω u) := by
  refine ⟨(Protocol.reachable_card_eq
    (phase_zero_trace_reachable init ω u)).trans hcard, ?_⟩
  exact phase_eq_between init ω 1 s u t hsu hut
    h.start_profile.all_one h.drain_first.1.1

open Classical in
theorem role_count_step_phase_one (r : Role) (n : ℕ) (c : Cfg L K)
    (hwin : PhaseOnlyWindows.Phase1Win n c) (s t : AgentState L K) :
    (Protocol.stepOrSelf (NonuniformMajority L K) c s t).countP
        (fun a => a.role = r) =
      c.countP (fun a => a.role = r) := by
  by_cases happ : Protocol.Applicable c s t
  · have hs : s ∈ c := Multiset.mem_of_le happ (by simp)
    have ht : t ∈ c := Multiset.mem_of_le happ (by simp)
    have hroles :=
      PhaseOnlyWindows.Transition_role_phase1 s t (hwin.2 s hs) (hwin.2 t ht)
    have hstep : Protocol.stepOrSelf (NonuniformMajority L K) c s t =
        c - {s, t} + {(Transition L K s t).1, (Transition L K s t).2} := by
      unfold Protocol.stepOrSelf
      rw [if_pos happ] <;> rfl
    have hsplit : c = c - {s, t} + ({s, t} : Multiset (AgentState L K)) := by
      rw [Multiset.sub_add_cancel
        (show ({s, t} : Multiset (AgentState L K)) ≤ c from happ)]
    have hpair :
        ({(Transition L K s t).1, (Transition L K s t).2} :
          Multiset (AgentState L K)).countP (fun a => a.role = r) =
        ({s, t} : Multiset (AgentState L K)).countP (fun a => a.role = r) := by
      first
        | (simp only [Multiset.insert_eq_cons, ← Multiset.cons_zero, Multiset.countP_cons,
            Multiset.countP_zero, hroles.1, hroles.2])
        | (by_cases h1 : s.role = r <;> by_cases h2 : t.role = r <;>
            simp [Multiset.countP_cons, h1, h2, hroles.1, hroles.2])
        | simp only [Multiset.insert_eq_cons, Multiset.countP_cons, Multiset.countP_singleton,
            hroles.1, hroles.2]
        | (rw [Multiset.insert_eq_cons, Multiset.insert_eq_cons, Multiset.countP_cons,
            Multiset.countP_cons, hroles.1, hroles.2])
        | (classical simp [Multiset.countP_cons, hroles.1, hroles.2])
        | (simp only [Multiset.countP_eq_card_filter]
           simp [Multiset.filter_cons, hroles.1, hroles.2])
    rw [hstep, Multiset.countP_add]
    conv_rhs => rw [hsplit]
    rw [Multiset.countP_add, hpair]
  · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]

open Classical in
theorem role_count_applyDraw_phase_one (r : Role) (n : ℕ) (c : Cfg L K)
    (hwin : PhaseOnlyWindows.Phase1Win n c) (d : Draw L K) :
    (applyDraw c d).countP (fun a => a.role = r) =
      c.countP (fun a => a.role = r) := by
  cases d with
  | none => rfl
  | some p => exact role_count_step_phase_one r n c hwin p.1.1 p.2.1

open Classical in
theorem DrainedPrefix.role_count {n : ℕ} {init : InputCfg n}
    {ω : InputLog n} {s t : ℕ} (h : DrainedPrefix init ω s t)
    (hcard : init.card = n) (r : Role) (u : ℕ) (hsu : s ≤ u) (hut : u ≤ t) :
    (trace init ω u).countP (fun a => a.role = r) =
      (trace init ω s).countP (fun a => a.role = r) := by
  exact PhaseOneDrainProducer.trace_eq_of_window init ω
    (fun c => c.countP (fun a => a.role = r)) (PhaseOnlyWindows.Phase1Win n)
    (fun c hc d => role_count_applyDraw_phase_one r n c hc d)
    s u hsu (fun k hsk hku => h.phase_one_window hcard k hsk (hku.le.trans hut))

theorem DrainedPrefix.main_count {n : ℕ} {init : InputCfg n}
    {ω : InputLog n} {s t : ℕ} (h : DrainedPrefix init ω s t)
    (hcard : init.card = n) (u : ℕ) (hsu : s ≤ u) (hut : u ≤ t) :
    RoleSplitConcentration.mainCount (trace init ω u) =
      RoleSplitConcentration.mainCount (trace init ω s) := by
  simpa only [RoleSplitConcentration.mainCount] using h.role_count hcard .main u hsu hut

theorem DrainedPrefix.clock_count {n : ℕ} {init : InputCfg n}
    {ω : InputLog n} {s t : ℕ} (h : DrainedPrefix init ω s t)
    (hcard : init.card = n) (u : ℕ) (hsu : s ≤ u) (hut : u ≤ t) :
    RoleSplitConcentration.clockCount (trace init ω u) =
      RoleSplitConcentration.clockCount (trace init ω s) := by
  simpa only [RoleSplitConcentration.clockCount] using h.role_count hcard .clock u hsu hut

theorem DrainedPrefix.reserve_count {n : ℕ} {init : InputCfg n}
    {ω : InputLog n} {s t : ℕ} (h : DrainedPrefix init ω s t)
    (hcard : init.card = n) (u : ℕ) (hsu : s ≤ u) (hut : u ≤ t) :
    RoleSplitConcentration.reserveCount (trace init ω u) =
      RoleSplitConcentration.reserveCount (trace init ω s) := by
  simpa only [RoleSplitConcentration.reserveCount] using h.role_count hcard .reserve u hsu hut

theorem DrainedPrefix.final_roles {n : ℕ} {init : InputCfg n}
    {ω : InputLog n} {s t : ℕ} (h : DrainedPrefix init ω s t)
    (hinput : ThresholdEpidemic.GoodInput n init) (u : ℕ)
    (hsu : s ≤ u) (hut : u ≤ t) :
    StageEventSpec.finalRoles (n := n) (trace init ω u) :=
  phase_one_trace_final_roles init hinput ω u
    (h.phase_one_window hinput.2.2 u hsu hut).2

theorem DrainedPrefix.nonmain_zero {n : ℕ} {init : InputCfg n}
    {ω : InputLog n} {s t : ℕ} (h : DrainedPrefix init ω s t)
    (hinput : ThresholdEpidemic.GoodInput n init) (u : ℕ)
    (hsu : s ≤ u) (hut : u ≤ t) :
    ∀ a ∈ trace init ω u, a.role ≠ .main → a.smallBias.val = 3 :=
  phase_one_trace_nonmain_zero init hinput ω u (h.final_roles hinput u hsu hut)

theorem DrainedPrefix.main_mass {n : ℕ} {init : InputCfg n}
    {ω : InputLog n} {s t : ℕ} (h : DrainedPrefix init ω s t)
    (hinput : ThresholdEpidemic.GoodInput n init) (u : ℕ)
    (hsu : s ≤ u) (hut : u ≤ t) :
    mainSmallBiasSum (trace init ω u) = initialGap init :=
  phase_one_trace_main_mass init hinput ω u (h.final_roles hinput u hsu hut)

structure PhaseOneReadyProfile {n : ℕ} (init c : InputCfg n) : Prop where
  card_eq : c.card = n
  valid_initial : validInitial init
  reachable : (NonuniformMajority (PhaseThreeModel.Numeric.hourIndex n) 256).Reachable init c
  all_one : ∀ a ∈ c, a.phase.val = 1
  final_roles : StageEventSpec.finalRoles (n := n) c
  role_good : RoleSplitConcentration.RoleSplitGood (1 / 25 : ℝ) n c
  main_lower : (99 / 200 : ℝ) * (n : ℝ) ≤ (RoleSplitConcentration.mainCount c : ℝ)
  main_upper : (RoleSplitConcentration.mainCount c : ℝ) ≤ (101 / 200 : ℝ) * (n : ℝ)
  clock_lower : (97 / 400 : ℝ) * (n : ℝ) ≤ (RoleSplitConcentration.clockCount c : ℝ)
  reserve_lower : (97 / 400 : ℝ) * (n : ℝ) ≤ (RoleSplitConcentration.reserveCount c : ℝ)
  nonmain_zero : ∀ a ∈ c, a.role ≠ .main → a.smallBias.val = 3
  main_mass : mainSmallBiasSum c = initialGap init
  drained : PhaseOneDrained c

theorem DrainedPrefix.ready_profile {n : ℕ} {init : InputCfg n}
    {ω : InputLog n} {s t : ℕ} (h : DrainedPrefix init ω s t)
    (hinput : ThresholdEpidemic.GoodInput n init) :
    PhaseOneReadyProfile init (trace init ω t) := by
  have hwin := h.phase_one_window hinput.2.2 t h.order le_rfl
  have hroles := phase_one_trace_final_roles init hinput ω t hwin.2
  have hmain := h.main_count hinput.2.2 t h.order le_rfl
  have hclock := h.clock_count hinput.2.2 t h.order le_rfl
  have hreserve := h.reserve_count hinput.2.2 t h.order le_rfl
  have hmcr : RoleSplitConcentration.roleMCRCount (trace init ω t) =
      RoleSplitConcentration.roleMCRCount (trace init ω s) := by
    simpa only [RoleSplitConcentration.roleMCRCount] using
      h.role_count hinput.2.2 .mcr t h.order le_rfl
  refine
    { card_eq := hwin.1
      valid_initial := hinput.2.1
      reachable := phase_zero_trace_reachable init ω t
      all_one := hwin.2
      final_roles := hroles
      role_good := ?_
      main_lower := ?_
      main_upper := ?_
      clock_lower := ?_
      reserve_lower := ?_
      nonmain_zero := phase_one_trace_nonmain_zero init hinput ω t hroles
      main_mass := phase_one_trace_main_mass init hinput ω t hroles
      drained := h.drain_first.1 }
  · simpa only [RoleSplitConcentration.RoleSplitGood, hmcr, hmain, hclock, hreserve]
      using h.start_profile.role_good
  · simpa only [hmain] using h.start_profile.main_lower
  · simpa only [hmain] using h.start_profile.main_upper
  · simpa only [hclock] using h.start_profile.clock_lower
  · simpa only [hreserve] using h.start_profile.reserve_lower

theorem phaseOneReadyProfile_past {n : ℕ} (init : InputCfg n) (t : ℕ) :
    MeasurableSet[pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256 t]
      {ω | PhaseOneReadyProfile init (trace init ω t)} :=
  (show MeasurableSet {c : InputCfg n | PhaseOneReadyProfile init c} from
    (Set.to_countable _).measurableSet).preimage (measurable_trace_at init t)

end Ripple.PopulationProtocol.ExactMajority.PhaseOneDrainStopping

end
