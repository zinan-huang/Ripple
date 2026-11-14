-- Ripple/PopulationProtocol/ExactMajority/Probability/AveragingChangingZeroTail.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingDebtService
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingServiceProbability
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingStoppedDebtLaw

/-!
# The actual changing-zero death tail

The integer process is ceil(F_h - A), killed at the first failed gate.
The gate contains the current mixed-mass budget and the current Clock floor.
The service rectangle is proved from the implemented transition, in both
orientations; it includes pending activation and the same sampled hour drag.
No conditional probability or adapted-process assumption remains as an input.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal

namespace Ripple.PopulationProtocol.ExactMajority.AveragingChangingZeroTail

open TimeTheorem AveragingMixedAlgebra AveragingMixedLedgers
open AveragingDebtAlgebra AveragingDebtTransitions AveragingDebtService
open AveragingPotentialService AveragingStoppedDebt AveragingRecordedExpectation
open AveragingServiceProbability AveragingStoppedDebtLaw PairLog PhaseOneDrain

variable {L : ℕ}

theorem PotentialDomain.preMass_carrier (c : Cfg L 256) (hc : PotentialDomain c) :
    ∀ a ∈ c, a.role ≠ .main → prePhase4Mass a = 0 := by
  intro a ha hm
  by_cases hp : a.phase.val < 3
  · have hs := (hc a ha).small_carrier hm
    simp [prePhase4Mass, hp, AgentState.smallBiasInt, hs]
  · have hphase : a.phase.val = 3 := by
      have hr := (hc a ha).range
      omega
    have hb := (hc a ha).active_carrier hphase hm
    simp [prePhase4Mass, hp, hb, Bias.toRat]

open Classical in
theorem clockTarget_count (h : ℕ) (c : Cfg L 256) :
    c.countP (ClockServiceTarget h) =
      inactiveMainCount c + lowHourZeroCount h c := by
  induction c using Multiset.induction_on with
  | empty => simp [inactiveMainCount, lowHourZeroCount]
  | cons a c ih =>
      have hpt : (if ClockServiceTarget h a then 1 else 0) =
          inactiveMainWeight a + lowHourZeroWeight h a := by
        unfold ClockServiceTarget inactiveMainWeight lowHourZeroWeight
        by_cases hm : a.role = .main <;> by_cases hp : a.phase.val < 3 <;>
          by_cases hz : a.bias = .zero <;> by_cases hh : a.hour.val < h <;>
          simp [hm, hp, hz, hh]
      rw [Multiset.countP_cons, ih]
      simp only [inactiveMainCount, lowHourZeroCount, Multiset.map_cons,
        Multiset.sum_cons]
      rw [hpt]
      ring

theorem clockTarget_disjoint (h : ℕ) (a : AgentState L 256)
    (htarget : ClockServiceTarget h a) : ¬ ClockServiceSource h a := by
  intro hsource
  have hr := htarget.1.symm.trans hsource.2.1
  cases hr

open Classical in
structure FuelGate (h : ℕ) (A : ℚ) (n C : ℕ) (c : Cfg L 256) : Prop where
  population : c.card = n
  domain : PotentialDomain c
  mass : (2 : ℚ) ^ h * mixedAbsoluteMass c ≤ A
  clocks : C ≤ c.countP (ClockServiceSource h)

def clockDeathRate (n C : ℕ) : ℝ :=
  (2 * (C : ℝ)) / ((n * (n - 1) : ℕ) : ℝ)

theorem clockDeathRate_nonneg (n C : ℕ) : 0 ≤ clockDeathRate n C := by
  unfold clockDeathRate
  positivity

theorem clockDeathRate_size_bound (n C M : ℕ) (hn : 2 ≤ n)
    (hsize : 2 * C * M ≤ n * (n - 1)) :
    clockDeathRate n C * M ≤ 1 := by
  have hd : (0 : ℝ) < ((n * (n - 1) : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos (by omega : 0 < n) (by omega : 0 < n - 1)
  unfold clockDeathRate
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hd).2
  have hc : (2 : ℝ) * C * M ≤ ((n * (n - 1) : ℕ) : ℝ) := by
    exact_mod_cast hsize
  simpa only [one_mul] using hc

open Classical in
theorem fuel_excess_le_targets (h : ℕ) (A : ℚ) (n C : ℕ) (c : Cfg L 256)
    (hc : FuelGate h A n C c) :
    Nat.ceil (changingZeroFuel h c - A) ≤ c.countP (ClockServiceTarget h) := by
  apply Nat.ceil_le.mpr
  rw [changingZeroFuel_eq h c (PotentialDomain.preMass_carrier c hc.domain),
    clockTarget_count, Nat.cast_add]
  linarith only [hc.mass]

theorem changingZeroFuel_draw_le (h : ℕ) (c : Cfg L 256)
    (hc : PotentialDomain c) (d : Draw L 256) (hd : PotentialDomain (applyDraw c d)) :
    changingZeroFuel h (applyDraw c d) ≤ changingZeroFuel h c := by
  rw [← totalDebt_eq_changingZeroFuel h (applyDraw c d)
      (PotentialDomain.preMass_carrier _ hd),
    ← totalDebt_eq_changingZeroFuel h c (PotentialDomain.preMass_carrier _ hc)]
  apply totalDebt_draw _ _ h (by positivity) (by positivity)
    (le_add_of_nonneg_right (by positivity)) c d
    (fun a ha => (hc a ha).range)
    (fun a ha => (hc a ha).safe)
    (fun a ha => (hc a ha).small_carrier)
  exact fun a ha => (hd a ha).range.2

open Classical in
/-- The changing-zero ledger supplies an actual unit-service probability.
The current eligible count is the true inactive-plus-low-zero count. -/
theorem changingZeroFuel_service_probability
    (h : ℕ) (hh : h ≤ L) (A : ℚ) (n C : ℕ) (hn : 2 ≤ n)
    (c : Cfg L 256) (hc : FuelGate h A n C c) :
    clockDeathRate n C * (Nat.ceil (changingZeroFuel h c - A) : ℝ) ≤
      ∫ d, (if ¬ FuelGate h A n C (applyDraw c d) ∨
          changingZeroFuel h (applyDraw c d) + 1 ≤ changingZeroFuel h c
        then (1 : ℝ) else 0) ∂(drawLaw c).toMeasure := by
  classical
  have hrectangle := service_rectangle_real c (by rw [hc.population]; exact hn)
    (ClockServiceTarget h) (ClockServiceSource h)
    (fun c' => ¬ FuelGate h A n C c' ∨
      changingZeroFuel h c' + 1 ≤ changingZeroFuel h c)
    (clockTarget_disjoint h) (by
      intro s t happ hrect
      by_cases hnext : FuelGate h A n C
          (Protocol.stepOrSelf (NonuniformMajority L 256) c s t)
      · apply Or.inr
        have hs : s ∈ c := Multiset.mem_of_le happ (by simp)
        have ht : t ∈ c := Multiset.mem_of_le happ (by simp)
        have hpair :
            agentDebt ((2 : ℚ) ^ h) ((2 : ℚ) ^ h) h (Transition L 256 s t).1 +
              agentDebt ((2 : ℚ) ^ h) ((2 : ℚ) ^ h) h (Transition L 256 s t).2 + 1 =
              agentDebt ((2 : ℚ) ^ h) ((2 : ℚ) ^ h) h s +
                agentDebt ((2 : ℚ) ^ h) ((2 : ℚ) ^ h) h t := by
          rcases hrect with hforward | hreverse
          · exact transition_clock_service_left _ _ h hh s t
              (hc.domain s hs).range (hc.domain s hs).safe hforward.1 hforward.2
          · exact transition_clock_service_right _ _ h hh s t
              (hc.domain t ht).range (hc.domain t ht).safe hreverse.1 hreverse.2
        have hstep := totalDebt_step_service _ _ h c s t happ hpair
        rw [totalDebt_eq_changingZeroFuel h _
            (PotentialDomain.preMass_carrier _ hnext.domain),
          totalDebt_eq_changingZeroFuel h c
            (PotentialDomain.preMass_carrier _ hc.domain)] at hstep
        exact hstep.le
      · exact Or.inl hnext)
  have htotal : c.totalPairs = n * (n - 1) := by
    simp only [Config.totalPairs, hc.population]
  beta_reduce at hrectangle
  calc
    clockDeathRate n C * (Nat.ceil (changingZeroFuel h c - A) : ℝ) =
        (2 * (Nat.ceil (changingZeroFuel h c - A) : ℝ) * (C : ℝ)) /
          (c.totalPairs : ℝ) := by
            rw [htotal]
            unfold clockDeathRate
            ring
    _ ≤ (2 * (c.countP (ClockServiceTarget h) : ℝ) *
        (c.countP (ClockServiceSource h) : ℝ)) / (c.totalPairs : ℝ) := by
          gcongr
          · exact_mod_cast fuel_excess_le_targets h A n C c hc
          · exact_mod_cast hc.clocks
    _ ≤ _ := by convert hrectangle

/-- All conditional-process obligations for the actual changing-zero ledger
are discharged before the scalar exponential tail is applied. -/
theorem changingZeroFuel_exponential_tail
    (init : Cfg L 256) (s : ℕ) (p : (i : Finset.Iic s) → Draw L 256)
    (h : ℕ) (hh : h ≤ L) (A : ℚ) (n C M : ℕ) (hn : 2 ≤ n)
    (hsize : 2 * C * M ≤ n * (n - 1)) (a : ℝ) (T : ℕ) :
    (recordedFuture init s p).real
      {ω | DebtLive init s (changingZeroFuel h) A (FuelGate h A n C) M T ω ∧
        a * M ≤ (Nat.ceil (changingZeroFuel h (trace init ω (s + T)) - A) : ℝ)} ≤
      Real.exp
        ((7 * Real.exp (-clockDeathRate n C * T) - a * Real.log 8) * M) := by
  apply stoppedDebt_exponential_tail init s p (changingZeroFuel h) A
    (FuelGate h A n C) M (clockDeathRate n C) a
    (clockDeathRate_nonneg n C) (clockDeathRate_size_bound n C M hn hsize)
  · intro c hc d hd
    exact changingZeroFuel_draw_le h c hc.domain d hd.domain
  · exact changingZeroFuel_service_probability h hh A n C hn

/-- The paper-facing real threshold, still intersected with the observed
prefix gate throughout the actual time interval. -/
theorem changingZeroFuel_threshold_tail
    (init : Cfg L 256) (s : ℕ) (p : (i : Finset.Iic s) → Draw L 256)
    (h : ℕ) (hh : h ≤ L) (A : ℚ) (n C M : ℕ) (hn : 2 ≤ n)
    (hsize : 2 * C * M ≤ n * (n - 1)) (a : ℚ) (T : ℕ) :
    (recordedFuture init s p).real
      {ω | DebtLive init s (changingZeroFuel h) A (FuelGate h A n C) M T ω ∧
        A + a * M < changingZeroFuel h (trace init ω (s + T))} ≤
      Real.exp
        ((7 * Real.exp (-clockDeathRate n C * T) - (a : ℝ) * Real.log 8) * M) := by
  refine (measureReal_mono ?_).trans
    (changingZeroFuel_exponential_tail init s p h hh A n C M hn hsize (a : ℝ) T)
  rintro ω ⟨hlive, hlarge⟩
  refine ⟨hlive, ?_⟩
  have hle : a * (M : ℚ) ≤
      (Nat.ceil (changingZeroFuel h (trace init ω (s + T)) - A) : ℚ) :=
    (show a * (M : ℚ) ≤ changingZeroFuel h (trace init ω (s + T)) - A by
      linarith only [hlarge]).trans (Nat.le_ceil _)
  exact_mod_cast hle

/-- Prefix-event form under the original law. -/
theorem changingZeroFuel_tail_from
    (init : Cfg L 256) (s : ℕ)
    (B : Set ((i : Finset.Iic s) → Draw L 256))
    (h : ℕ) (hh : h ≤ L) (A : ℚ) (n C M : ℕ) (hn : 2 ≤ n)
    (hsize : 2 * C * M ≤ n * (n - 1)) (a : ℝ) (T : ℕ) :
    law init {ω | frestrictLe (π := fun _ : ℕ => Draw L 256) s ω ∈ B ∧
        ω ∈ debtFailure init s (changingZeroFuel h) A (FuelGate h A n C) M a T} ≤
      ENNReal.ofReal
        (Real.exp ((7 * Real.exp (-clockDeathRate n C * T) - a * Real.log 8) * M)) *
        law init {ω | frestrictLe (π := fun _ : ℕ => Draw L 256) s ω ∈ B} :=
  stoppedDebt_tail_from init s B (changingZeroFuel h) A (FuelGate h A n C)
    M (clockDeathRate n C) a (clockDeathRate_nonneg n C)
    (clockDeathRate_size_bound n C M hn hsize)
    (fun c hc d hd => changingZeroFuel_draw_le h c hc.domain d hd.domain)
    (changingZeroFuel_service_probability h hh A n C hn) T

/-- Random observed starts are spliced over their disjoint pair-log fibres.
The tail remains a joint event with every actual gate through the endpoint. -/
theorem changingZeroFuel_tail_at_pastTime
    (init : Cfg L 256) (σ : Ω L 256 → WithTop ℕ) (hσ : PairLogPastTime σ)
    (h : ℕ) (hh : h ≤ L) (A : ℚ) (n C M : ℕ) (hn : 2 ≤ n)
    (hsize : 2 * C * M ≤ n * (n - 1)) (a : ℝ) (T : ℕ) :
    law init {ω | ∃ s : ℕ, σ ω = (s : WithTop ℕ) ∧
        ω ∈ debtFailure init s (changingZeroFuel h) A (FuelGate h A n C) M a T} ≤
      ENNReal.ofReal
        (Real.exp ((7 * Real.exp (-clockDeathRate n C * T) - a * Real.log 8) * M)) :=
  stoppedDebt_tail_at_pastTime init σ hσ (changingZeroFuel h) A (FuelGate h A n C)
    M (clockDeathRate n C) a (clockDeathRate_nonneg n C)
    (clockDeathRate_size_bound n C M hn hsize)
    (fun c hc d hd => changingZeroFuel_draw_le h c hc.domain d hd.domain)
    (changingZeroFuel_service_probability h hh A n C hn) T

end Ripple.PopulationProtocol.ExactMajority.AveragingChangingZeroTail

end
