import Ripple.PopulationProtocol.ExactMajority.Probability.LateSmallGapTimeChain
import Ripple.PopulationProtocol.ExactMajority.Probability.LateLemmaFourteenInvariant
import Ripple.PopulationProtocol.ExactMajority.Probability.LateLemmaFourteenVerdict

/-!
# Small-gap late-time composition

The fixed input sign selects one majority-bit spread and one cleanup event.
The late-time ledger uses 84 inverse-square units and the three Lemma 14 tails.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace Ripple.PopulationProtocol.ExactMajority.LateSmallGapComposition

open TimeTheorem StageEventSpec LateSmallGapTimeChain
open LateLemmaFourteenSpreads LateLemmaFourteenCleanup
open LateLemmaFourteenInvariant

variable {n : ℕ}

/-- The signed verdict selected once from the initial input gap. -/
def lateOutput (init : InputCfg n) : Output :=
  if 0 < initialGap init then .A else .B

/-- The selected verdict is always a signed output. -/
theorem lateOutput_signed (init : InputCfg n) :
    lateOutput init = .A ∨ lateOutput init = .B := by
  unfold lateOutput
  split_ifs <;> simp

/-- A strict input gap identifies the selected signed verdict. -/
theorem lateOutput_majority (init : InputCfg n) (hgap : 0 < gapMagnitude init) :
    majorityVerdict init = outputTripleOfOutput (lateOutput init) := by
  have hne : initialGap init ≠ 0 := by
    intro hz
    simp [gapMagnitude, hz] at hgap
  unfold lateOutput
  split_ifs with hpos
  · exact majorityVerdict_eq_A_of_initialGap_pos init hpos
  · exact majorityVerdict_eq_B_of_initialGap_neg init (by omega)

/-- The four fixed original-law failure events for the late small-gap branch. -/
def lateSmallGapFailure (init : InputCfg n) : Set (InputLog n) :=
  ((lateSmallGapTimeFailure init ∪ phaseNineSpreadFailure init) ∪
    majorityBitSpreadFailure init (lateOutput init)) ∪
    missedLabelFailure init (cleanupStart init (lateOutput init) n) (cleanupWindow n)

/-- The actual four-event charge, without a union over signs or times. -/
def lateSmallGapCharge (n : ℕ) : ℝ≥0∞ :=
  charge n + LateCompositionBudget.lemmaFourteenCharge n

/-- Both spread laws have the inverse-cube scalar used by the ledger. -/
private theorem epidemic_scalar (n : ℕ) :
    Real.exp 3 * Real.rpow (n : ℝ) (-3 : ℝ) = Real.exp 3 / (n : ℝ) ^ 3 := by
  rw [Real.rpow_eq_pow, Real.rpow_neg (Nat.cast_nonneg n)]
  norm_num [Real.rpow_natCast, div_eq_mul_inv]

/-- The cleanup inverse cube agrees with its real-valued scalar charge. -/
private theorem cleanup_scalar (n : ℕ) (hn : 0 < (n : ℝ)) :
    (1 : ℝ≥0∞) / (n : ℝ≥0∞) ^ 3 = ENNReal.ofReal (1 / (n : ℝ) ^ 3) := by
  simp only [one_div]
  rw [ENNReal.ofReal_inv_of_pos (pow_pos hn 3), ENNReal.ofReal_pow (by positivity)]
  simp

/-- Every event in the fixed late union is measurable. -/
theorem measurableSet_lateSmallGapFailure (init : InputCfg n) :
    MeasurableSet (lateSmallGapFailure init) :=
  (((measurableSet_lateSmallGapTimeFailure init).union
    (measurableSet_phaseNineSpreadFailure init)).union
    (measurableSet_majorityBitSpreadFailure init (lateOutput init))).union
    (missedLabelFailure_measurable init (cleanupStart init (lateOutput init) n)
      (cleanupStart_pastTime init (lateOutput init) n) (cleanupWindow n))

/-- The event union is bounded by exactly the charges proved for its constituents. -/
theorem law_lateSmallGapFailure (init : InputCfg n)
    (hinput : ThresholdEpidemic.GoodInput n init) :
    law init (lateSmallGapFailure init) ≤ lateSmallGapCharge n := by
  have hphase := law_phaseNineSpreadFailure init hinput
  have hbit := law_majorityBitSpreadFailure init (lateOutput init) hinput
  rw [epidemic_scalar] at hphase hbit
  have hclean := (lemma_fourteen_cleanup_bound init hinput (lateOutput init)).2
  rw [cleanup_scalar n (time_hour_calibration hinput.1).2.1] at hclean
  unfold lateSmallGapFailure lateSmallGapCharge LateCompositionBudget.lemmaFourteenCharge
  calc
    _ ≤ ((law init (lateSmallGapTimeFailure init) +
        law init (phaseNineSpreadFailure init)) +
        law init (majorityBitSpreadFailure init (lateOutput init))) +
        law init (missedLabelFailure init (cleanupStart init (lateOutput init) n)
          (cleanupWindow n)) :=
      (measure_union_le _ _).trans (add_le_add
        ((measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)) le_rfl)
    _ ≤ _ := by
      have ht := law_lateSmallGapTimeFailure init hinput
      calc
        _ ≤ ((charge n + ENNReal.ofReal (Real.exp 3 / (n : ℝ)^3)) +
            ENNReal.ofReal (Real.exp 3 / (n : ℝ)^3)) +
            ENNReal.ofReal (1 / (n : ℝ)^3) :=
          add_le_add (add_le_add (add_le_add ht hphase) hbit) hclean
        _ = _ := by ac_rfl

/-- The actual charge is at most 87 inverse-square units. -/
theorem lateSmallGapCharge_le (hn : timePopulationThreshold ≤ n) :
    lateSmallGapCharge n ≤ ENNReal.ofReal (87 / (n : ℝ)^2) := by
  unfold lateSmallGapCharge
  calc
    _ ≤ ENNReal.ofReal (84 / (n : ℝ)^2) +
        ENNReal.ofReal (3 / (n : ℝ)^2) :=
      add_le_add (charge_le hn) (LateCompositionBudget.lemmaFourteenCharge_le hn)
    _ = _ := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring

/-- The fixed failure event fits the requested 100-unit late budget. -/
theorem law_lateSmallGapFailure_le (init : InputCfg n)
    (hinput : ThresholdEpidemic.GoodInput n init) :
    law init (lateSmallGapFailure init) ≤ ENNReal.ofReal (100 / (n : ℝ)^2) :=
  (law_lateSmallGapFailure init hinput).trans (le_of_lt (charge_with_cleanup_lt hinput.1))

/-- Every late failure on a reviewed small-gap history belongs to the fixed union. -/
theorem smallGapLateFailure_subset (init : InputCfg n)
    (hinput : ThresholdEpidemic.GoodInput n init) :
    smallGapLateFailure (reviewedStageEvents n init) ⊆ lateSmallGapFailure init := by
  rintro omega ⟨S, T, rho, hhistory, hgap, hstrict, hmiss⟩
  by_contra hbad
  have htime : omega ∉ lateSmallGapTimeFailure init :=
    fun h => hbad (Or.inl (Or.inl (Or.inl h)))
  have hthreshold : omega ∉ phaseNineSpreadFailure init :=
    fun h => hbad (Or.inl (Or.inl (Or.inr h)))
  have hbit : omega ∉ majorityBitSpreadFailure init (lateOutput init) :=
    fun h => hbad (Or.inl (Or.inr h))
  have hcleanup : omega ∉ missedLabelFailure init
      (cleanupStart init (lateOutput init) n) (cleanupWindow n) :=
    fun h => hbad (Or.inr h)
  have hsmall : omega ∈ LateStrengthening.smallHistory init :=
    ⟨S, T, rho, hhistory, hgap, hstrict⟩
  obtain ⟨completed, seven, homogeneousSeven, eight, homogeneousEight, t, firstNine,
      ell, hell, sigma, tau, M, R, hreceipt, hfirst, hbefore, hdeadline⟩ :=
    lateSmallGapTimeChain hinput hhistory hsmall htime
  have hout : lateOutput init = majorityOutput sigma := by
    have hpre := opinionSpreadPre_of_receipt hreceipt firstNine hinput.2.2 hfirst hthreshold
    have hreach := trace_reachable init omega (s := 0)
      (t := firstNine + logWindow n 4) (Nat.zero_le _)
    rw [trace_zero] at hreach
    have hne : initialGap init ≠ 0 := by
      intro hz
      simp [gapMagnitude, hz] at hgap
    have hsigned : majorityOutput sigma = .A ∨ majorityOutput sigma = .B := by
      cases sigma <;> simp [majorityOutput]
    exact LateLemmaFourteenVerdict.opinionSpreadPre_input_sign init _ _
      hinput.2.1 hreach hpre hsigned hne
  have hle := lemma_fourteen_cleanup_start_le_of_receipt hreceipt firstNine
    hinput.2.2 hfirst hthreshold (by simpa only [hout] using hbit)
  rw [← hout] at hle
  have hfinite : cleanupStart init (lateOutput init) n omega ≠ ⊤ :=
    ne_top_of_le_ne_top WithTop.coe_ne_top hle
  obtain ⟨u, hu⟩ := WithTop.ne_top_iff_exists.mp hfinite
  have hstart : cleanupStart init (lateOutput init) n omega = (u : WithTop ℕ) := hu.symm
  have hule : u ≤ firstNine + logWindow n 4 + logWindow n 4 := by
    rw [hstart] at hle
    exact WithTop.coe_le_coe.mp hle
  have hwindow : cleanupWindow n = logWindow n 2 := by
    rfl
  have hend := lemma_fourteen_endpoint init (lateOutput init) omega u
    (lateOutput_signed init) (lateOutput_majority init hgap) hstart hcleanup
  exact hmiss (hitBy_mono init (by rw [hwindow]; omega) hend.2.2.2.2.2)

/-- The closed late estimate on the strict small-gap branch. -/
theorem smallGap_late_estimate (init : InputCfg n)
    (hinput : ThresholdEpidemic.GoodInput n init) :
    law init (smallGapLateFailure (reviewedStageEvents n init)) ≤
      ENNReal.ofReal (100 / (n : ℝ)^2) :=
  (measure_mono (smallGapLateFailure_subset init hinput)).trans
    (law_lateSmallGapFailure_le init hinput)

end Ripple.PopulationProtocol.ExactMajority.LateSmallGapComposition

end
