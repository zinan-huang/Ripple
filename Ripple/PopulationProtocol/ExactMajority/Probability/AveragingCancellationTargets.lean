-- Ripple/PopulationProtocol/ExactMajority/Probability/AveragingCancellationTargets.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingCancellationRecorded
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingNumerics

/-!
# Actual total and minority cancellation target tails

All eleven reviewed rows use the same physical cancellation block. The live
product floor is proved from the current augmented potential, current deep
count, and signed-gap bound. The actual cancellation ledger proves the
target-failure count implication. No conditional rate is an input.

The public bounds are joint events under the original law, from arbitrary
prefix events or pair-log stopping times. Supplying the current gates from
the global hour induction remains a separate obligation.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal BigOperators

namespace Ripple.PopulationProtocol.ExactMajority.AveragingCancellationTargets

open TimeTheorem PairLog PhaseOneDrain P3DeterministicAlgebra StageEventSpec
open AveragingMixedAlgebra AveragingMixedLedgers AveragingLiveProduct
open AveragingCancellationAlgebra AveragingCancellationProbability
open AveragingCancellationLedger AveragingCancellationRecorded
open AveragingRecordedExpectation AveragingRecordedSplice AveragingNumerics

variable {L : ℕ}

inductive TargetKind where
  | total
  | minority

def targetKind : CancellationRegime → TargetKind
  | .early | .totalFourth | .totalThird | .totalSecond |
      .totalPrevious | .totalTerminal => .total
  | .minorityFourth | .minorityThird | .minoritySecond |
      .minorityPrevious | .minorityTerminal => .minority

def previousTarget : CancellationRegime → ℝ
  | .early => 1 / 10
  | .totalFourth => 1 / 10
  | .totalThird => 104 / 1000
  | .totalSecond => 13 / 100
  | .totalPrevious => 212 / 1000
  | .totalTerminal => 408 / 1000
  | .minorityFourth => 4375 / 100000
  | .minorityThird => 375 / 10000
  | .minoritySecond => 267 / 10000
  | .minorityPrevious => 145 / 10000
  | .minorityTerminal => 56 / 10000

def currentTarget : CancellationRegime → ℝ
  | .early => 1 / 10
  | .totalFourth => 104 / 1000
  | .totalThird => 13 / 100
  | .totalSecond => 212 / 1000
  | .totalPrevious => 408 / 1000
  | .totalTerminal => 808 / 1000
  | .minorityFourth => 375 / 10000
  | .minorityThird => 267 / 10000
  | .minoritySecond => 145 / 10000
  | .minorityPrevious => 56 / 10000
  | .minorityTerminal => 4 / 1000

def gapTarget : CancellationRegime → ℝ
  | .early => 25 / 1000
  | .totalFourth | .minorityThird => 5 / 100
  | .totalThird | .minoritySecond => 1 / 10
  | .totalSecond | .minorityPrevious => 2 / 10
  | .totalPrevious | .minorityTerminal => 4 / 10
  | .totalTerminal => 8 / 10
  | .minorityFourth => 25 / 1000

/-- The actual table factors and exact cancellation deficits, including .0483
and .0389 in the minority rows. The exponential margins are already compiled
as cancellation_margin and cancellation_exponent_bound. -/
theorem target_row_parameters (r : CancellationRegime) :
    0 ≤ gapTarget r ∧
      match targetKind r with
      | .total =>
          (4 / 1250 : ℝ) ≤ (currentTarget r - gapTarget r) / 2 ∧
          (currentTarget r + gapTarget r) / 2 = (cancellationParameters r).1 ∧
          (currentTarget r - gapTarget r) / 2 - 4 / 1250 =
            (cancellationParameters r).2.1 ∧
          previousTarget r - currentTarget r / 2 = (cancellationParameters r).2.2
      | .minority =>
          (4 / 1250 : ℝ) ≤ currentTarget r ∧
          currentTarget r + gapTarget r = (cancellationParameters r).1 ∧
          currentTarget r - 4 / 1250 = (cancellationParameters r).2.1 ∧
          2 * previousTarget r - currentTarget r = (cancellationParameters r).2.2 := by
  cases r <;>
    norm_num [targetKind, previousTarget, currentTarget, gapTarget, cancellationParameters]

structure CancellationGate (level : Fin (L + 1)) (M : ℕ) (c : Cfg L 256) : Prop where
  range : ∀ a ∈ c, 1 ≤ a.phase.val ∧ a.phase.val ≤ 3
  safe : ∀ a ∈ c, a.smallBias.val ∈ ({2, 3, 4} : Finset ℕ)
  small_carrier : ∀ a ∈ c, a.role ≠ .main → a.smallBias.val = 3
  bias_carrier : ∀ a ∈ c, a.role ≠ .main → a.bias = .zero
  potential : (1000 : ℚ) * augmentedPhi level.val c ≤ M
  deep : 1250 * deepCount level.val c ≤ 3 * M

def targetQuantity (r : CancellationRegime) (σ : Sign)
    (level : Fin (L + 1)) (c : Cfg L 256) : ℝ :=
  match targetKind r with
  | .total => (2 : ℝ) ^ level.val * (mixedAbsoluteMass c : ℝ)
  | .minority => (2 : ℝ) ^ level.val * (sideMass (oppositeSign σ) c : ℝ)

def targetGap (r : CancellationRegime) (σ : Sign)
    (level : Fin (L + 1)) (M : ℕ) (c : Cfg L 256) : Prop :=
  match targetKind r with
  | .total =>
      |(2 : ℝ) ^ level.val * (prePhase4MassSum c : ℝ)| ≤ gapTarget r * M
  | .minority =>
      gapTarget r * M ≤ (2 : ℝ) ^ level.val *
        ((sideMass σ c : ℝ) - (sideMass (oppositeSign σ) c : ℝ))

def targetStart (r : CancellationRegime) (σ : Sign)
    (level : Fin (L + 1)) (M : ℕ) (c : Cfg L 256) : Prop :=
  targetQuantity r σ level c ≤ 2 * previousTarget r * M

def targetGate (r : CancellationRegime) (σ : Sign)
    (level : Fin (L + 1)) (M : ℕ) (c : Cfg L 256) : Prop :=
  CancellationGate level M c ∧ targetGap r σ level M c

def targetLive (r : CancellationRegime) (σ : Sign)
    (level : Fin (L + 1)) (M : ℕ) (c : Cfg L 256) : Prop :=
  targetGate r σ level M c ∧ currentTarget r * M < targetQuantity r σ level c

/-- Live product floors for every actual total and minority row. -/
theorem target_live_product (r : CancellationRegime) (σ : Sign)
    (level : Fin (L + 1)) (hh : 1 ≤ level.val) (M : ℕ)
    {m : ℕ} (f : Fin m → AgentState L 256)
    (hlive : targetLive r σ level M (labelCfg f)) :
    (cancellationParameters r).1 * (cancellationParameters r).2.1 * (M : ℝ) ^ 2 ≤
      ((levelSet f .pos level).card : ℝ) * (levelSet f .neg level).card := by
  obtain ⟨hg, hrow⟩ := target_row_parameters r
  have hc := hlive.1.1
  cases hm : targetKind r
  · simp only [hm] at hrow
    obtain ⟨hmin, hA, hB, _⟩ := hrow
    have hgap : |(2 : ℝ) ^ level.val * (prePhase4MassSum (labelCfg f) : ℝ)| ≤
        gapTarget r * M := by
      simpa only [targetGap, hm] using hlive.1.2
    have hmass : currentTarget r * M ≤
        (2 : ℝ) ^ level.val * (mixedAbsoluteMass (labelCfg f) : ℝ) := by
      simpa only [targetQuantity, hm] using hlive.2.le
    have hp := labels_product_of_total_mass f level hh M
      (fun a ha => (hc.range a ha).2) hc.bias_carrier hc.potential hc.deep
      hg hmin hmass hgap
    simpa only [hA, hB] using hp
  · simp only [hm] at hrow
    obtain ⟨hmin, hA, hB, _⟩ := hrow
    have hgap : gapTarget r * M ≤ (2 : ℝ) ^ level.val *
        ((sideMass σ (labelCfg f) : ℝ) -
          (sideMass (oppositeSign σ) (labelCfg f) : ℝ)) := by
      simpa only [targetGap, hm] using hlive.1.2
    have hmass : currentTarget r * M ≤ (2 : ℝ) ^ level.val *
        (sideMass (oppositeSign σ) (labelCfg f) : ℝ) := by
      simpa only [targetQuantity, hm] using hlive.2.le
    have hp := labels_product_of_minority σ f level hh M
      (fun a ha => (hc.range a ha).2) hc.bias_carrier hc.potential hc.deep
      hg hmin hmass hgap
    simpa only [hA, hB] using hp

theorem targetQuantity_trace_le (r : CancellationRegime) (σ : Sign)
    (level : Fin (L + 1)) (init : Cfg L 256) (hinit : validInitial init)
    (ω : Ω L 256) (u v : ℕ) (huv : u ≤ v)
    (hrange : ∀ t, u ≤ t → t ≤ v → ∀ a ∈ trace init ω t,
      1 ≤ a.phase.val ∧ a.phase.val ≤ 3)
    (hsafe : ∀ t, u ≤ t → t ≤ v → ∀ a ∈ trace init ω t,
      a.smallBias.val ∈ ({2, 3, 4} : Finset ℕ))
    (hcarrier : ∀ t, u ≤ t → t ≤ v → ∀ a ∈ trace init ω t,
      a.role ≠ .main → a.smallBias.val = 3) :
    targetQuantity r σ level (trace init ω v) ≤
      targetQuantity r σ level (trace init ω u) := by
  cases hm : targetKind r
  · have hp := sideMass_trace_le .pos init hinit ω u v huv hrange hsafe hcarrier
    have hn := sideMass_trace_le .neg init hinit ω u v huv hrange hsafe hcarrier
    have hmass : mixedAbsoluteMass (trace init ω v) ≤ mixedAbsoluteMass (trace init ω u) := by
      rw [← sideMass_add (trace init ω v), ← sideMass_add (trace init ω u)]
      exact add_le_add hp hn
    have hmassR : (mixedAbsoluteMass (trace init ω v) : ℝ) ≤
        (mixedAbsoluteMass (trace init ω u) : ℝ) := by exact_mod_cast hmass
    simpa only [targetQuantity, hm] using
      mul_le_mul_of_nonneg_left hmassR (by positivity : (0 : ℝ) ≤ 2 ^ level.val)
  · have hmass := sideMass_trace_le (oppositeSign σ) init hinit ω u v huv
      hrange hsafe hcarrier
    have hmassR : (sideMass (oppositeSign σ) (trace init ω v) : ℝ) ≤
        (sideMass (oppositeSign σ) (trace init ω u) : ℝ) := by exact_mod_cast hmass
    simpa only [targetQuantity, hm] using
      mul_le_mul_of_nonneg_left hmassR (by positivity : (0 : ℝ) ≤ 2 ^ level.val)

theorem gate_at_absolute (init : Cfg L 256) (ω : Ω L 256) (s N : ℕ)
    (G : Cfg L 256 → Prop)
    (hG : ∀ u, u ≤ N → G (trace init ω (s + u)))
    (v : ℕ) (hsv : s ≤ v) (hvN : v ≤ s + N) :
    G (trace init ω v) := by
  have hv : s + (v - s) = v := by omega
  simpa only [hv] using hG (v - s) (by omega)

/-- The only event tested is an actual starting mass bound, survival of the
current-state gates, and failure of the mass target at the actual endpoint. -/
def targetFailure (init : Cfg L 256) (s : ℕ)
    (r : CancellationRegime) (σ : Sign) (level : Fin (L + 1)) (M : ℕ) :
    Set (Ω L 256) :=
  {ω | targetStart r σ level M (trace init ω s) ∧
    (∀ u, u ≤ cancellationTrials init.card M →
      targetGate r σ level M (trace init ω (s + u))) ∧
    currentTarget r * M <
      targetQuantity r σ level (trace init ω (s + cancellationTrials init.card M))}

theorem measurableSet_trace_predicate (init : Cfg L 256) (t : ℕ)
    (P : Cfg L 256 → Prop) :
    MeasurableSet {ω : Ω L 256 | P (trace init ω t)} :=
  (Set.to_countable {c : Cfg L 256 | P c}).measurableSet.preimage
    ((measurable_trace_at init t).mono ((pairLogFiltration L 256).le t) le_rfl)

theorem measurableSet_targetFailure (init : Cfg L 256) (s : ℕ)
    (r : CancellationRegime) (σ : Sign) (level : Fin (L + 1)) (M : ℕ) :
    MeasurableSet (targetFailure init s r σ level M) := by
  have hs := measurableSet_trace_predicate init s (targetStart r σ level M)
  have hg : MeasurableSet {ω : Ω L 256 |
      ∀ u, u ≤ cancellationTrials init.card M →
        targetGate r σ level M (trace init ω (s + u))} := by
    simp only [Set.setOf_forall]
    exact MeasurableSet.iInter fun u => MeasurableSet.iInter fun _ =>
      measurableSet_trace_predicate init (s + u) (targetGate r σ level M)
  have hf := measurableSet_trace_predicate init (s + cancellationTrials init.card M)
    (fun c => currentTarget r * M < targetQuantity r σ level c)
  exact hs.inter (hg.inter hf)

theorem targetFailure_subset_stop_survival
    (init : Cfg L 256) (hinit : validInitial init) (s : ℕ)
    (r : CancellationRegime) (σ : Sign) (level : Fin (L + 1)) (M : ℕ) :
    targetFailure init s r σ level M ⊆
      {ω | (cancellationTrials init.card M : WithTop ℕ) <
        windowStop init s (targetStart r σ level M) (targetLive r σ level M) ω} := by
  intro ω hω
  apply (windowStop_gt_iff init s _ _ _ ω).2
  refine ⟨hω.1, ?_⟩
  intro u hu
  refine ⟨hω.2.1 u hu, ?_⟩
  have hgate : ∀ v, s ≤ v → v ≤ s + cancellationTrials init.card M →
      CancellationGate level M (trace init ω v) := by
    intro v hsv hv
    exact (gate_at_absolute init ω s (cancellationTrials init.card M) _
      hω.2.1 v hsv hv).1
  have hmono := targetQuantity_trace_le r σ level init hinit ω
    (s + u) (s + cancellationTrials init.card M) (by omega)
    (fun v huv hv => (hgate v (by omega) hv).range)
    (fun v huv hv => (hgate v (by omega) hv).safe)
    (fun v huv hv => (hgate v (by omega) hv).small_carrier)
  exact lt_of_lt_of_le hω.2.2 hmono

theorem target_stop_failure_count
    (init : Cfg L 256) (hinit : validInitial init) (s N : ℕ)
    (r : CancellationRegime) (σ : Sign) (level : Fin (L + 1)) (M : ℕ)
    (ω : Ω L 256)
    (hsurvive : (N : WithTop ℕ) <
      windowStop init s (targetStart r σ level M) (targetLive r σ level M) ω) :
    cancellationCountFrom init level s N ω <
      (cancellationParameters r).2.2 * (M : ℝ) := by
  obtain ⟨hstart, hlive⟩ := (windowStop_gt_iff init s _ _ N ω).1 hsurvive
  have hgate : ∀ v, s ≤ v → v ≤ s + N →
      CancellationGate level M (trace init ω v) := by
    intro v hsv hv
    exact (gate_at_absolute init ω s N _ hlive v hsv hv).1.1
  have hfinal := (hlive N le_rfl).2
  obtain ⟨_, hrow⟩ := target_row_parameters r
  cases hm : targetKind r
  · simp only [hm] at hrow
    have hs : (2 : ℝ) ^ level.val * (mixedAbsoluteMass (trace init ω s) : ℝ) ≤
        2 * previousTarget r * (M : ℝ) := by
      simpa only [targetStart, targetQuantity, hm] using hstart
    have hf : currentTarget r * (M : ℝ) <
        (2 : ℝ) ^ level.val * (mixedAbsoluteMass (trace init ω (s + N)) : ℝ) := by
      simpa only [targetQuantity, hm] using hfinal
    have hcount := total_target_failure_count init hinit level ω s N
      (fun v hsv hv => (hgate v hsv hv).range)
      (fun v hsv hv => (hgate v hsv hv).safe)
      (fun v hsv hv => (hgate v hsv hv).small_carrier) hs hf
    simpa only [hrow.2.2.2] using hcount
  · simp only [hm] at hrow
    have hs : (2 : ℝ) ^ level.val * (sideMass (oppositeSign σ) (trace init ω s) : ℝ) ≤
        2 * previousTarget r * (M : ℝ) := by
      simpa only [targetStart, targetQuantity, hm] using hstart
    have hf : currentTarget r * (M : ℝ) < (2 : ℝ) ^ level.val *
        (sideMass (oppositeSign σ) (trace init ω (s + N)) : ℝ) := by
      simpa only [targetQuantity, hm] using hfinal
    have hcount := minority_target_failure_count σ init hinit level ω s N
      (fun v hsv hv => (hgate v hsv hv).range)
      (fun v hsv hv => (hgate v hsv hv).safe)
      (fun v hsv hv => (hgate v hsv hv).small_carrier) hs hf
    simpa only [hrow.2.2.2] using hcount

/-- Uniform local tail from an arbitrary recorded prefix. Its actual conditional
rate and target-failure implication are both discharged above. -/
theorem recorded_target_tail
    (init : Cfg L 256) (hinit : validInitial init) (hc : 2 ≤ init.card)
    (s : ℕ) (p : (i : Finset.Iic s) → Draw L 256)
    (r : CancellationRegime) (σ : Sign) (level : Fin (L + 1))
    (hh : 1 ≤ level.val) (M : ℕ) (hM : 0 < M) (hMn : M ≤ init.card) :
    recordedFuture init s p (targetFailure init s r σ level M) ≤
      ENNReal.ofReal (Real.exp (-(M : ℝ) / 1000)) := by
  refine (measure_mono (targetFailure_subset_stop_survival init hinit s r σ level M)).trans ?_
  apply recorded_cancellation_regime_tail init hc level r M hM hMn s p
    (windowStop init s (targetStart r σ level M) (targetLive r σ level M))
    (windowStop_isStoppingTime init s _ _)
  · intro t ω hbefore
    have hlive := ((windowStop_gt_iff init s _ _ t ω).1 hbefore).2 t le_rfl
    have hcfg : labelCfg (labelsAt init ω (s + t)) = trace init ω (s + t) :=
      labelsAt_config init ω (s + t)
    exact target_live_product r σ level hh M (labelsAt init ω (s + t))
      (by simpa only [hcfg] using hlive)
  · intro ω hbefore
    exact target_stop_failure_count init hinit s (cancellationTrials init.card M)
      r σ level M ω hbefore

/-- All six total rows and all five minority rows, under the original law and
with the exact prefix-event factor. -/
theorem cancellation_target_tail_from
    (init : Cfg L 256) (hinit : validInitial init) (hc : 2 ≤ init.card)
    (s : ℕ) (A : Set ((i : Finset.Iic s) → Draw L 256))
    (r : CancellationRegime) (σ : Sign) (level : Fin (L + 1))
    (hh : 1 ≤ level.val) (M : ℕ) (hM : 0 < M) (hMn : M ≤ init.card) :
    law init {ω | frestrictLe (π := fun _ : ℕ => Draw L 256) s ω ∈ A ∧
        ω ∈ targetFailure init s r σ level M} ≤
      ENNReal.ofReal (Real.exp (-(M : ℝ) / 1000)) *
        law init {ω | frestrictLe (π := fun _ : ℕ => Draw L 256) s ω ∈ A} :=
  law_prefix_joint_bound init s A _ (measurableSet_targetFailure init s r σ level M) _
    (fun p _ => recorded_target_tail init hinit hc s p r σ level hh M hM hMn)

/-- Random work starts are spliced through their disjoint observed values.
The current gates and endpoint failure remain joint events under law init. -/
theorem cancellation_target_tail_at_pastTime
    (init : Cfg L 256) (hinit : validInitial init) (hc : 2 ≤ init.card)
    (τ : Ω L 256 → WithTop ℕ) (hτ : PairLogPastTime τ)
    (r : CancellationRegime) (σ : Sign) (level : Fin (L + 1))
    (hh : 1 ≤ level.val) (M : ℕ) (hM : 0 < M) (hMn : M ≤ init.card) :
    law init {ω | ∃ s : ℕ, τ ω = (s : WithTop ℕ) ∧
        ω ∈ targetFailure init s r σ level M} ≤
      ENNReal.ofReal (Real.exp (-(M : ℝ) / 1000)) :=
  law_at_past_time_bound init τ hτ (fun s => targetFailure init s r σ level M)
    (fun s => measurableSet_targetFailure init s r σ level M) _
    (fun s p => recorded_target_tail init hinit hc s p r σ level hh M hM hMn)

theorem cancellation_target_polynomial_tail_at_pastTime
    (init : Cfg L 256) (hinit : validInitial init)
    (hn : timePopulationThreshold ≤ init.card)
    (τ : Ω L 256 → WithTop ℕ) (hτ : PairLogPastTime τ)
    (r : CancellationRegime) (σ : Sign) (level : Fin (L + 1))
    (hh : 1 ≤ level.val) (M : ℕ)
    (hdensity : 12 * init.card ≤ 25 * M) (hMn : M ≤ init.card) :
    law init {ω | ∃ s : ℕ, τ ω = (s : WithTop ℕ) ∧
        ω ∈ targetFailure init s r σ level M} ≤
      ENNReal.ofReal (1 / (init.card : ℝ) ^ 20) := by
  have hnlarge := (time_population_bounds hn).2
  have hc : 2 ≤ init.card := by omega
  have hM : 0 < M := by omega
  exact (cancellation_target_tail_at_pastTime init hinit hc τ hτ r σ level hh M hM hMn).trans
    (ENNReal.ofReal_le_ofReal (mass_tail_le_inverse_power hn hdensity))

end Ripple.PopulationProtocol.ExactMajority.AveragingCancellationTargets

end
