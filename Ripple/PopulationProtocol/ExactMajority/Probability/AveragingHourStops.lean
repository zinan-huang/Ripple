-- Ripple/PopulationProtocol/ExactMajority/Probability/AveragingHourStops.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockProducer
import Mathlib.Probability.Process.HittingTime

/-!
# Canonical adapted hour starts on the physical-label log

The clock-history witness supplies finite first-hit times. This file constructs
those times as actual stopping-time functions before assuming clock success.
The seed may itself be any pair-log past time. A hit uses the seed's fixed roles
and clock count, and the labels at the candidate time. Hour zero is the reviewed
99-percent activation time; positive hours use the high front threshold.

These declarations do not assert a probability bound for clock success or for
the averaging hour induction.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder

namespace Ripple.PopulationProtocol.ExactMajority.AveragingHourStops

open TimeTheorem PairLog PhaseOneDrain StageEventSpec PhaseThreeClockProducer

variable {L K n : ℕ}

theorem measurable_labelsAt_at (init : Cfg L K) (t : ℕ) :
    Measurable[pairLogFiltration L K t] (fun ω => labelsAt init ω t) :=
  (measurable_prefixLabels init t).comp (measurable_pairLog_prefix L K t)

theorem measurable_labelsAt_at_of_le (init : Cfg L K) {s t : ℕ}
    (hst : s ≤ t) :
    Measurable[pairLogFiltration L K t] (fun ω => labelsAt init ω s) :=
  (measurable_labelsAt_at init s).mono
    ((pairLogFiltration L K).mono hst) le_rfl

theorem measurable_activeCount_at (init : InputCfg n) (t : ℕ) :
    Measurable[pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256 t]
      (fun ω => StageEventSpec.activeCount init ω t) := by
  classical
  have hf : Measurable
      (fun f : Fin init.card → AgentState (PhaseThreeModel.Numeric.hourIndex n) 256 =>
        labelCount init (fun i => 3 ≤ (f i).phase.val)) :=
    measurable_of_countable _
  exact hf.comp (measurable_labelsAt_at init t)

theorem measurable_frontCount_at (init : InputCfg n) {S t : ℕ}
    (hSt : S ≤ t) (ell : ℕ) :
    Measurable[pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256 t]
      (fun ω => frontCount init ω S t ell) := by
  classical
  let Labels := Fin init.card →
    AgentState (PhaseThreeModel.Numeric.hourIndex n) 256
  have hf : Measurable (fun p : Labels × Labels =>
      labelCount init (fun i =>
        (p.1 i).role = .clock ∧
          ell ≤ if 3 ≤ (p.2 i).phase.val then (p.2 i).minute.val else 0)) :=
    measurable_of_countable _
  have heq :
      (fun ω : InputLog n => frontCount init ω S t ell) =
      (fun ω : InputLog n =>
        labelCount init (fun i =>
          (labelsAt init ω S i).role = .clock ∧
            ell ≤ if 3 ≤ (labelsAt init ω t i).phase.val
              then (labelsAt init ω t i).minute.val else 0)) := by
    funext ω
    unfold frontCount
    apply congrArg (labelCount init)
    funext i
    unfold fixedRole effectiveMinute active
    by_cases ha : 3 ≤ (labelsAt init ω t i).phase.val
    · simp only [if_pos ha]
    · simp only [if_neg ha]
  rw [heq]
  exact hf.comp ((measurable_labelsAt_at_of_le init hSt).prodMk
    (measurable_labelsAt_at init t))

/-- The actual reviewed threshold at hour zero or at a positive hour. -/
def HourReached (init : InputCfg n) (S h t : ℕ) (ω : InputLog n) : Prop :=
  if h = 0 then
    Nat.ceil ((99 : ℝ) * (n : ℝ) / 100) ≤ StageEventSpec.activeCount init ω t
  else
    highThreshold (clockCount (trace init ω S)) ≤
      frontCount init ω S t (256 * h)

theorem hourReached_measurableSet (init : InputCfg n) (S h t : ℕ)
    (hSt : S ≤ t) :
    MeasurableSet[pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256 t]
      {ω | HourReached init S h t ω} := by
  by_cases hh : h = 0
  · have hset : MeasurableSet
        {a : ℕ | Nat.ceil ((99 : ℝ) * (n : ℝ) / 100) ≤ a} :=
      (Set.to_countable _).measurableSet
    simpa only [HourReached, if_pos hh] using
      hset.preimage (measurable_activeCount_at init t)
  · have hf : Measurable (fun c : InputCfg n => highThreshold (clockCount c)) :=
      measurable_of_countable _
    have hseed := hf.comp (measurable_trace_at_of_le init hSt)
    have hfront := measurable_frontCount_at init hSt (256 * h)
    have hset : MeasurableSet {p : ℕ × ℕ | p.1 ≤ p.2} :=
      (Set.to_countable _).measurableSet
    simpa only [HourReached, if_neg hh] using
      hset.preimage (hseed.prodMk hfront)

open Classical in
/-- The signal is zero before the recorded seed exists. -/
def hourStartSignal (init : InputCfg n) (σ : InputLog n → WithTop ℕ)
    (h t : ℕ) (ω : InputLog n) : ℕ :=
  if ∃ S : ℕ, S ≤ t ∧ σ ω = (S : WithTop ℕ) ∧
      HourReached init S h t ω then 1 else 0

theorem hourStartSignal_eq_one_iff (init : InputCfg n)
    (σ : InputLog n → WithTop ℕ) (h t : ℕ) (ω : InputLog n) :
    hourStartSignal init σ h t ω = 1 ↔
      ∃ S : ℕ, S ≤ t ∧ σ ω = (S : WithTop ℕ) ∧
        HourReached init S h t ω := by
  classical
  simp [hourStartSignal]

theorem hourStartSignal_adapted (init : InputCfg n)
    (σ : InputLog n → WithTop ℕ) (hσ : PairLogPastTime σ) (h : ℕ) :
    Adapted (pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256)
      (hourStartSignal init σ h) := by
  classical
  intro t
  have hsignal :
      MeasurableSet[pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256 t]
        {ω | ∃ S : ℕ, S ≤ t ∧ σ ω = (S : WithTop ℕ) ∧
          HourReached init S h t ω} := by
    have hset :
        {ω | ∃ S : ℕ, S ≤ t ∧ σ ω = (S : WithTop ℕ) ∧
          HourReached init S h t ω} =
        ⋃ S : ℕ, {ω | S ≤ t ∧ σ ω = (S : WithTop ℕ) ∧
          HourReached init S h t ω} := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    rw [hset]
    refine MeasurableSet.iUnion fun S => ?_
    by_cases hSt : S ≤ t
    · have hs :=
        (pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256).mono
          hSt _ (hσ S)
      have hr := hourReached_measurableSet init S h t hSt
      simpa only [hSt, true_and] using hs.inter hr
    · simp only [hSt, false_and, Set.setOf_false, MeasurableSet.empty]
  exact Measurable.ite hsignal measurable_const measurable_const

/-- The canonical hour-start function, with value top when no hit occurs. -/
def hourStart (init : InputCfg n) (σ : InputLog n → WithTop ℕ)
    (h : ℕ) : InputLog n → WithTop ℕ :=
  hittingAfter (hourStartSignal init σ h) ({1} : Set ℕ) 0

theorem hourStart_isStoppingTime (init : InputCfg n)
    (σ : InputLog n → WithTop ℕ) (hσ : PairLogPastTime σ) (h : ℕ) :
    IsStoppingTime (pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256)
      (hourStart init σ h) :=
  (hourStartSignal_adapted init σ hσ h).isStoppingTime_hittingAfter
    (measurableSet_singleton 1)

theorem hourStart_pastTime (init : InputCfg n)
    (σ : InputLog n → WithTop ℕ) (hσ : PairLogPastTime σ) (h : ℕ) :
    PairLogPastTime (hourStart init σ h) :=
  fun t => (hourStart_isStoppingTime init σ hσ h).measurableSet_eq_of_countable t

theorem hourStartSignal_of_seed (init : InputCfg n)
    (σ : InputLog n → WithTop ℕ) (h t : ℕ) (ω : InputLog n)
    (S : ℕ) (hseed : σ ω = (S : WithTop ℕ)) :
    hourStartSignal init σ h t ω = 1 ↔
      S ≤ t ∧ HourReached init S h t ω := by
  rw [hourStartSignal_eq_one_iff]
  constructor
  · rintro ⟨r, hrt, hr, hreach⟩
    have hrs : r = S := WithTop.coe_injective (hr.symm.trans hseed)
    subst r
    exact ⟨hrt, hreach⟩
  · rintro ⟨hSt, hreach⟩
    exact ⟨S, hSt, hseed, hreach⟩

theorem hourStart_le_iff_of_seed (init : InputCfg n)
    (σ : InputLog n → WithTop ℕ) (h : ℕ) (ω : InputLog n)
    (S t : ℕ) (hseed : σ ω = (S : WithTop ℕ)) :
    hourStart init σ h ω ≤ (t : WithTop ℕ) ↔
      ∃ v ∈ Set.Icc S t, HourReached init S h v ω := by
  change hittingAfter (hourStartSignal init σ h) ({1} : Set ℕ) 0 ω ≤
    (t : WithTop ℕ) ↔ _
  refine (hittingAfter_le_iff (u := hourStartSignal init σ h) (s := ({1} : Set ℕ))
    (n := 0) (ω := ω) (i := t)).trans ?_
  constructor
  · rintro ⟨v, hv, hmem⟩
    have hvhit := (hourStartSignal_of_seed init σ h v ω S hseed).mp
      (show hourStartSignal init σ h v ω = 1 from hmem)
    exact ⟨v, ⟨hvhit.1, hv.2⟩, hvhit.2⟩
  · rintro ⟨v, hv, hreach⟩
    refine ⟨v, ⟨Nat.zero_le v, hv.2⟩, ?_⟩
    exact (hourStartSignal_of_seed init σ h v ω S hseed).mpr ⟨hv.1, hreach⟩

theorem hourStart_eq_iff_of_seed (init : InputCfg n)
    (σ : InputLog n → WithTop ℕ) (h : ℕ) (ω : InputLog n)
    (S t : ℕ) (hseed : σ ω = (S : WithTop ℕ)) :
    hourStart init σ h ω = (t : WithTop ℕ) ↔
      firstAfter (fun v => HourReached init S h v ω) S t := by
  constructor
  · intro ht
    obtain ⟨u, hu, hreach⟩ :=
      (hourStart_le_iff_of_seed init σ h ω S t hseed).mp ht.le
    have htu : t ≤ u := by
      have hu' := (hourStart_le_iff_of_seed init σ h ω S u hseed).mpr
        ⟨u, ⟨hu.1, le_rfl⟩, hreach⟩
      rw [ht] at hu'
      exact_mod_cast hu'
    have hut : u = t := le_antisymm hu.2 htu
    subst u
    refine ⟨hu.1, hreach, ?_⟩
    intro v hSv hvt hv
    have hv' := (hourStart_le_iff_of_seed init σ h ω S v hseed).mpr
      ⟨v, ⟨hSv, le_rfl⟩, hv⟩
    rw [ht] at hv'
    have htv : t ≤ v := by exact_mod_cast hv'
    omega
  · intro ht
    refine le_antisymm
      ((hourStart_le_iff_of_seed init σ h ω S t hseed).mpr
        ⟨t, ⟨ht.1, le_rfl⟩, ht.2.1⟩) ?_
    by_contra hnot
    have hlt : hourStart init σ h ω < (t : WithTop ℕ) := lt_of_not_ge hnot
    change hittingAfter (hourStartSignal init σ h) ({1} : Set ℕ) 0 ω <
      (t : WithTop ℕ) at hlt
    obtain ⟨v, hv, hmem⟩ := hittingAfter_lt_iff.mp hlt
    have hvhit := (hourStartSignal_of_seed init σ h v ω S hseed).mp
      (show hourStartSignal init σ h v ω = 1 from hmem)
    exact ht.2.2 v hvhit.1 hv.2 hvhit.2

/-- A clock-history witness agrees with the canonical time on every recorded path. -/
theorem hourStart_clockHistory {init : InputCfg n} {ω : InputLog n}
    {S T ρ : ℕ} {w : ClockTimes init} (hc : ClockHistory init ω S T ρ w)
    (σ : InputLog n → WithTop ℕ) (h : ℕ)
    (hseed : σ ω = (S : WithTop ℕ))
    (hh : h ≤ PhaseThreeModel.Numeric.hourIndex n) :
    hourStart init σ h ω = (w.start h : WithTop ℕ) := by
  apply (hourStart_eq_iff_of_seed init σ h ω S (w.start h) hseed).mpr
  by_cases hz : h = 0
  · subst h
    have ha := hc.activation_first
    rw [← hc.start_zero] at ha
    simpa [HourReached] using ha
  · have hp := hc.start_positive h (by omega) hh
    simpa only [HourReached, if_neg hz] using hp

/-- Deterministic-seed specialization of the same stopping-time function. -/
def hourStartFrom (init : InputCfg n) (S h : ℕ) : InputLog n → WithTop ℕ :=
  hourStart init (fun _ => (S : WithTop ℕ)) h

theorem hourStartFrom_pastTime (init : InputCfg n) (S h : ℕ) :
    PairLogPastTime (hourStartFrom init S h) := by
  apply hourStart_pastTime init (fun _ => (S : WithTop ℕ)) _ h
  intro t
  exact (isStoppingTime_const
    (pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256) S).measurableSet_eq_of_countable t

theorem hourStartFrom_clockHistory {init : InputCfg n} {ω : InputLog n}
    {S T ρ : ℕ} {w : ClockTimes init} (hc : ClockHistory init ω S T ρ w)
    (h : ℕ) (hh : h ≤ PhaseThreeModel.Numeric.hourIndex n) :
    hourStartFrom init S h ω = (w.start h : WithTop ℕ) :=
  hourStart_clockHistory hc (fun _ => (S : WithTop ℕ)) h rfl hh

theorem hourStart_phaseThreeSeed_pastTime (init : InputCfg n) (h : ℕ) :
    PairLogPastTime (hourStart init (seedTime init 3) h) :=
  hourStart_pastTime init (seedTime init 3) (seedTime_pastTime init 3) h

theorem hourStart_phaseThreeSeed_clockHistory
    {init : InputCfg n} {ω : InputLog n} {S T ρ : ℕ} {w : ClockTimes init}
    (hc : ClockHistory init ω S T ρ w) (h : ℕ)
    (hh : h ≤ PhaseThreeModel.Numeric.hourIndex n) :
    hourStart init (seedTime init 3) h ω = (w.start h : WithTop ℕ) :=
  hourStart_clockHistory hc (seedTime init 3) h
    ((seedTime_eq_iff init 3 ω S).mpr hc.entry.first_phase_seed) hh

end Ripple.PopulationProtocol.ExactMajority.AveragingHourStops

end
