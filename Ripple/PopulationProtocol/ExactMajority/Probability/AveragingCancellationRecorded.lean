-- Ripple/PopulationProtocol/ExactMajority/Probability/AveragingCancellationRecorded.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingCancellationLedger
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingRecordedSplice

/-!
# Actual cancellation trials after a recorded prefix

The first failed gate or successful target is a stopping time for the shifted
pair-log filtration. The conditional cancellation probability is computed
under the ordinary recorded continuation, with both ordered orientations.
The scalar hitting theorem fills indicators after that stopping time.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal BigOperators

namespace Ripple.PopulationProtocol.ExactMajority.AveragingCancellationRecorded

open TimeTheorem PairLog PairLogAuxiliary PhaseThreeScalar
open AveragingCancellationAlgebra AveragingCancellationProbability
open AveragingCancellationLedger AveragingRecordedExpectation

variable {L K : ℕ}

open Classical in
/-- The first failure is permanent: a later return to a good state does not
restart this stopping time. -/
def firstFailure {Ω : Type*} (B : ℕ → Ω → Prop) (ω : Ω) : WithTop ℕ :=
  if h : ∃ t, ¬ B t ω then (Nat.find h : WithTop ℕ) else ⊤

theorem firstFailure_gt_iff {Ω : Type*} (B : ℕ → Ω → Prop)
    (t : ℕ) (ω : Ω) :
    (t : WithTop ℕ) < firstFailure B ω ↔ ∀ u, u ≤ t → B u ω := by
  classical
  unfold firstFailure
  split_ifs with hex
  · simp only [Nat.cast_withTop, WithTop.coe_lt_coe]
    constructor
    · intro ht u hu
      by_contra hbad
      have hfirst := Nat.find_min' hex hbad
      omega
    · intro hall
      by_contra hnot
      have hle : Nat.find hex ≤ t := by omega
      exact (Nat.find_spec hex) (hall _ hle)
  · simp only [Nat.cast_withTop, WithTop.coe_lt_top, true_iff]
    intro u _
    by_contra hbad
    exact hex ⟨u, hbad⟩

theorem firstFailure_isStoppingTime {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (ℱ : Filtration ℕ mΩ) (B : ℕ → Ω → Prop)
    (hB : ∀ t, MeasurableSet[ℱ t] {ω | B t ω}) :
    IsStoppingTime ℱ (firstFailure B) := by
  intro t
  have hgt : MeasurableSet[ℱ t] {ω | (t : WithTop ℕ) < firstFailure B ω} := by
    simp only [firstFailure_gt_iff, Set.setOf_forall]
    refine MeasurableSet.iInter fun u => MeasurableSet.iInter fun hu => ?_
    exact (ℱ.mono hu) _ (hB u)
  simpa only [Set.compl_setOf, not_lt] using hgt.compl

def windowStop (init : Cfg L K) (s : ℕ)
    (Start Live : Cfg L K → Prop) : Ω L K → WithTop ℕ :=
  firstFailure fun t ω => Start (trace init ω s) ∧ Live (trace init ω (s + t))

theorem windowStop_gt_iff (init : Cfg L K) (s : ℕ)
    (Start Live : Cfg L K → Prop) (t : ℕ) (ω : Ω L K) :
    (t : WithTop ℕ) < windowStop init s Start Live ω ↔
      Start (trace init ω s) ∧ ∀ u, u ≤ t → Live (trace init ω (s + u)) := by
  rw [windowStop, firstFailure_gt_iff]
  constructor
  · intro h
    exact ⟨(h 0 (Nat.zero_le t)).1, fun u hu => (h u hu).2⟩
  · rintro ⟨hs, hl⟩ u hu
    exact ⟨hs, hl u hu⟩

theorem windowStop_isStoppingTime (init : Cfg L K) (s : ℕ)
    (Start Live : Cfg L K → Prop) :
    IsStoppingTime (shiftedPairLog L K s) (windowStop init s Start Live) := by
  apply firstFailure_isStoppingTime
  intro t
  have hpair :
      Measurable[pairLogFiltration L K (s + t)]
        (fun ω : Ω L K => (trace init ω s, trace init ω (s + t))) :=
    (measurable_trace_at_of_le init (Nat.le_add_right s t)).prodMk
      (measurable_trace_at init (s + t))
  exact (Set.to_countable {z : Cfg L K × Cfg L K | Start z.1 ∧ Live z.2}).measurableSet.preimage hpair

open Classical in
def cancellationNext (init : Cfg L K) (level : Fin (L + 1)) (t : ℕ)
    (q : (i : Finset.Iic t) → Draw L K) (d : Draw L K) : ℝ :=
  if ∃ i j, selectLabels (prefixLabels init t q) d = some (i, j) ∧
      CancellingPair level (prefixLabels init t q) i j then 1 else 0

theorem cancellationNext_bound (init : Cfg L K) (level : Fin (L + 1))
    (t : ℕ) (q : (i : Finset.Iic t) → Draw L K) (d : Draw L K) :
    |cancellationNext init level t q d| ≤ 1 := by
  classical
  unfold cancellationNext
  split_ifs <;> norm_num

theorem recordedNext_cancellation (init : Cfg L K) (level : Fin (L + 1))
    (t : ℕ) :
    recordedNext t (cancellationNext init level t) =
      cancellationIndicator init level t := by
  rfl

theorem cancellationNext_integral (init : Cfg L K) (hc : 2 ≤ init.card)
    (level : Fin (L + 1)) (t : ℕ)
    (q : (i : Finset.Iic t) → Draw L K) :
    (∫ d, cancellationNext init level t q d ∂pairKernel init t q) =
      (2 : ℝ) * (levelSet (prefixLabels init t q) .pos level).card *
          (levelSet (prefixLabels init t q) .neg level).card /
        ((init.card : ℝ) * ((init.card : ℝ) - 1)) := by
  classical
  let A : Set (Draw L K) :=
    {d | ∃ i j, selectLabels (prefixLabels init t q) d = some (i, j) ∧
      CancellingPair level (prefixLabels init t q) i j}
  have hA : MeasurableSet A := (Set.to_countable A).measurableSet
  have hmass :
      pairKernel init t q A =
        ((goodPairs (CancellingPair level) (prefixLabels init t q)).card : ℝ≥0∞) *
          ((init.card * (init.card - 1) : ℕ) : ℝ≥0∞)⁻¹ := by
    change (drawLaw (prefixCfg init t q)).toMeasure A = _
    rw [← prefixLabels_config]
    exact selected_pair_event_mass _ _ hc (CancellingPair level)
  calc
    (∫ d, cancellationNext init level t q d ∂pairKernel init t q) =
        (pairKernel init t q).real A := by
      simpa only [cancellationNext, A, Set.indicator, Pi.one_apply,
        Set.mem_setOf_eq] using (integral_indicator_one (μ := pairKernel init t q) hA)
    _ = (pairKernel init t q A).toReal := rfl
    _ = _ := by
      rw [hmass, goodPairs_cancelling_card, ENNReal.toReal_mul,
        ENNReal.toReal_inv, ENNReal.toReal_natCast, ENNReal.toReal_natCast]
      simp only [Nat.cast_mul, Nat.cast_ofNat,
        Nat.cast_sub (by omega : 1 ≤ init.card), Nat.cast_one, div_eq_mul_inv]

theorem recorded_cancellation_conditional_law (init : Cfg L K)
    (hc : 2 ≤ init.card) (level : Fin (L + 1)) (s t : ℕ)
    (p : (i : Finset.Iic s) → Draw L K) :
    (recordedFuture init s p)[cancellationIndicator init level (s + t) | shiftedPairLog L K s t]
      =ᵐ[recordedFuture init s p]
        (fun ω => (2 : ℝ) *
          (levelSet (labelsAt init ω (s + t)) .pos level).card *
          (levelSet (labelsAt init ω (s + t)) .neg level).card /
            ((init.card : ℝ) * ((init.card : ℝ) - 1))) := by
  have hce := recordedNext_condExp init s (s + t) (Nat.le_add_right s t) p
    (cancellationNext init level (s + t)) 1
    (cancellationNext_bound init level (s + t))
  rw [recordedNext_cancellation] at hce
  filter_upwards [hce] with ω hω
  exact hω.trans (cancellationNext_integral init hc level (s + t) _)

/-- This interface is specialized to actual physical cancellation indicators.
The target theorems discharge both of its deterministic input obligations. -/
theorem recorded_cancellation_regime_tail
    (init : Cfg L K) (hc : 2 ≤ init.card)
    (level : Fin (L + 1)) (r : CancellationRegime) (M : ℕ)
    (hM : 0 < M) (hMn : M ≤ init.card) (s : ℕ)
    (pfx : (i : Finset.Iic s) → Draw L K)
    (τ : Ω L K → WithTop ℕ)
    (hτ : IsStoppingTime (shiftedPairLog L K s) τ)
    (hcounts : ∀ (t : ℕ) ω, (t : WithTop ℕ) < τ ω →
      (cancellationParameters r).1 * (cancellationParameters r).2.1 * (M : ℝ) ^ 2 ≤
        ((levelSet (labelsAt init ω (s + t)) .pos level).card : ℝ) *
          (levelSet (labelsAt init ω (s + t)) .neg level).card)
    (hfail : ∀ ω,
      (cancellationTrials init.card M : WithTop ℕ) < τ ω →
        cancellationCountFrom init level s (cancellationTrials init.card M) ω <
          (cancellationParameters r).2.2 * (M : ℝ)) :
    recordedFuture init s pfx
        {ω | (cancellationTrials init.card M : WithTop ℕ) < τ ω} ≤
      ENNReal.ofReal (Real.exp (-(M : ℝ) / 1000)) := by
  let μ := recordedFuture init s pfx
  let I : ℕ → Ω L K → ℝ := fun t => cancellationIndicator init level (s + t)
  have hI : ∀ t, StronglyMeasurable[shiftedPairLog L K s (t + 1)] (I t) := by
    intro t
    simpa only [I, shiftedPairLog, Nat.add_assoc] using
      cancellationIndicator_adapted init level (s + t)
  have hzeroOne : ∀ t, ∀ᵐ ω ∂μ, I t ω = 0 ∨ I t ω = 1 :=
    fun t => ae_of_all μ (cancellationIndicator_zero_or_one init level (s + t))
  have hnR : (2 : ℝ) ≤ init.card := by exact_mod_cast hc
  have hden : 0 < (init.card : ℝ) * ((init.card : ℝ) - 1) :=
    mul_pos (by linarith) (by linarith)
  have hcond : ∀ t : ℕ, ∀ᵐ ω ∂μ, (t : WithTop ℕ) < τ ω →
      cancellationChance r init.card M ≤
        (μ[I t | shiftedPairLog L K s t]) ω := by
    intro t
    filter_upwards [recorded_cancellation_conditional_law init hc level s t pfx]
      with ω hω hbefore
    change cancellationChance r init.card M ≤
      ((recordedFuture init s pfx)[cancellationIndicator init level (s + t) | shiftedPairLog L K s t]) ω
    rw [hω]
    unfold cancellationChance
    apply (div_le_div_iff_of_pos_right hden).2
    have hprod := hcounts t ω hbefore
    nlinarith only [hprod]
  have htail := adapted_success_hitting_tail hI hzeroOne hτ
    (cancellationChance_le_one r hc hMn) hcond
    (cancellationTrials init.card M) ((cancellationParameters r).2.2 * (M : ℝ))
    (fun ω hω => hfail ω hω)
  have hreal :
      μ.real {ω | (cancellationTrials init.card M : WithTop ℕ) < τ ω} ≤
        Real.exp (-(M : ℝ) / 1000) :=
    htail.trans (cancellation_exponent_bound r (M := (M : ℝ))
      (by positivity) le_rfl (cancellation_work_lower r hc hM))
  rw [← ENNReal.ofReal_toReal (measure_ne_top μ
    {ω | (cancellationTrials init.card M : WithTop ℕ) < τ ω})]
  exact ENNReal.ofReal_le_ofReal hreal

end Ripple.PopulationProtocol.ExactMajority.AveragingCancellationRecorded

end
