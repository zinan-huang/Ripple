-- Ripple/PopulationProtocol/ExactMajority/Probability/LateLemmaTwelveSingleBand.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.LateBiasedResourceCreditPath
import Ripple.PopulationProtocol.ExactMajority.Probability.TraceDrain

/-!
# Lemma 12: one Phase-7 minority band

This file reuses, without duplicating their pair enumeration:

* `Phase7BandDropSum.phase7_band_weighted_drift`, the actual-scheduler
  one-step expected-count contraction;
* `LateBiasedResourceCreditPath.phaseSeven_band_hazard_floor`, the exact
  scaled `.806 M` arithmetic;
* `TraceDrain.potential_drift_tail_from`, the stopped original-law
  supermartingale estimate from a recorded prefix.

The alive predicate carries the exact `PhaseSevenBandConsumer`, rather than
only the rounded ledger floor.  It also carries `BandClear sigma j.val`, so
`j` is the currently lowest uncleared band.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder Set
open scoped ENNReal BigOperators

namespace Ripple.PopulationProtocol.ExactMajority.LateLemmaTwelveSingleBand

open TimeTheorem PairLog
open Phase7BandDefs Phase7BandDropSum Phase7MajorityBlockLedger
open LateBiasedResourceCreditPath

variable {L K n M : ℕ}

/-- One paper block: `⌈6 n ln n⌉` interactions. -/
def phaseSevenBandHorizon (n : ℕ) : ℕ :=
  logWindow n 6

/-- The fixed rate used in the stopped drift.  The actual scheduler hazard is
at least `.77376/(n-1)`; this weaker `.77376/n` is what gives the literal
paper exponent after `6 n ln n` interactions. -/
def phaseSevenBandRate (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal ((2418 / 3125 : ℝ) / (n : ℝ))

/-- `n^(-3.64256)`, with the decimal represented exactly. -/
def phaseSevenSingleBandBudget (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal
    (Real.rpow (n : ℝ) (-(11383 / 3125 : ℝ)))

/-- State carried while one exact band is being cleared. -/
structure SingleBandReady
    (n M : ℕ) (sigma : Sign)
    (ell j : Fin (L + 1))
    (c : Config (AgentState L K)) : Prop where
  consumer :
    PhaseSevenBandConsumer (L := L) (K := K)
      n M sigma ell c
  lower_clear :
    BandClear (L := L) (K := K) sigma j.val c

/-- At a ready state, use the entire current majority block as the static pool
for this one application of the already-proved weighted-drift theorem. -/
private theorem singleBandReady_toStageReady
    (sigma : Sign) (ell j : Fin (L + 1))
    (c : Config (AgentState L K))
    (h : SingleBandReady n M sigma ell j c) :
    Phase7StageReady (L := L) (K := K)
      n sigma ell.val
      (majorityBlockCount (L := L) (K := K) sigma ell.val c)
      j c := by
  refine
    { genuine := h.consumer.genuine
      cleared := h.lower_clear
      pool := ?_ }
  apply phase7BandPool_of_majorityBandFloor
    (L := L) (K := K) sigma ell.val
      (majorityBlockCount (L := L) (K := K) sigma ell.val c) c
  unfold MajorityBandFloor
  simp only [majorityBlockCount_eq_sum_count, le_refl]

/-- The receipt density `M ≥ .48 n`, followed by the exact scaled `.806 M`
block inequality, gives the paper hazard.  The conclusion is already weakened
from `.77376/(n-1)` to `.77376/n`, which is the rate used below. -/
private theorem phaseSevenBandRate_le_blockRate
    (hn : 2 ≤ n) (hM : 12 * n ≤ 25 * M)
    (sigma : Sign) (ell j : Fin (L + 1))
    (c : Config (AgentState L K))
    (h : SingleBandReady n M sigma ell j c) :
    phaseSevenBandRate n ≤
      ENNReal.ofReal
        ((((2 * majorityBlockCount (L := L) (K := K)
            sigma ell.val c : ℕ) : ℝ)) /
          ((n : ℝ) * ((n : ℝ) - 1))) := by
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hnm1pos : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hden : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) :=
    mul_pos hnpos hnm1pos
  have hMreal :
      (12 : ℝ) * (n : ℝ) ≤ 25 * (M : ℝ) := by
    exact_mod_cast hM
  have hMn := mul_le_mul_of_nonneg_left hMreal
    (show (0 : ℝ) ≤ (n : ℝ) by positivity)
  have hweak :
      (2418 / 3125 : ℝ) / (n : ℝ) ≤
        (403 / 250 : ℝ) * (M : ℝ) /
          ((n : ℝ) * ((n : ℝ) - 1)) := by
    apply (div_le_div_iff₀ hnpos hden).2
    nlinarith
  have hN : 0 < n * (n - 1) :=
    Nat.mul_pos (by omega) (by omega)
  have hhazard :=
    phaseSeven_band_hazard_floor
      (L := L) (K := K) (n * (n - 1)) M hN
      sigma ell c
      (PhaseSevenBandConsumer.block_scaled h.consumer)
  have hhazard' :
      (403 / 250 : ℝ) * (M : ℝ) /
          ((n : ℝ) * ((n : ℝ) - 1)) ≤
        2 * (majorityBlockCount (L := L) (K := K)
          sigma ell.val c : ℝ) /
          ((n : ℝ) * ((n : ℝ) - 1)) := by
    simpa only [Nat.cast_mul,
      Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one] using hhazard
  unfold phaseSevenBandRate
  apply ENNReal.ofReal_le_ofReal
  calc
    (2418 / 3125 : ℝ) / (n : ℝ) ≤
        (403 / 250 : ℝ) * (M : ℝ) /
          ((n : ℝ) * ((n : ℝ) - 1)) := hweak
    _ ≤ 2 * (majorityBlockCount (L := L) (K := K)
          sigma ell.val c : ℝ) /
          ((n : ℝ) * ((n : ℝ) - 1)) := hhazard'
    _ = (((2 * majorityBlockCount (L := L) (K := K)
          sigma ell.val c : ℕ) : ℝ)) /
          ((n : ℝ) * ((n : ℝ) - 1)) := by
      norm_num [Nat.cast_mul]

/-- Exact one-step drift used by the original-law block argument.  No scheduler
pair counting is repeated here. -/
theorem phaseSevenSingleBandDrift
    (hn : 2 ≤ n) (hM : 12 * n ≤ 25 * M)
    (sigma : Sign) (ell j : Fin (L + 1))
    (hjl : ell.val ≤ j.val) (hjtop : j.val < ell.val + 3) :
    DyadicMassDrainTight.WeightedDyadicMassDrift
      (L := L) (K := K)
      (fun c => SingleBandReady n M sigma ell j c)
      (fun c => bandCountN (L := L) (K := K) sigma j c)
      (1 - phaseSevenBandRate n) := by
  intro c hc
  let Q := majorityBlockCount (L := L) (K := K) sigma ell.val c
  have hstage :
      Phase7StageReady (L := L) (K := K)
        n sigma ell.val Q j c := by
    simpa [Q] using
      singleBandReady_toStageReady
        (n := n) (M := M) sigma ell j c hc
  have hq :=
    (phase7_band_weighted_drift
      (L := L) (K := K) n sigma ell.val Q j
      hn hjl hjtop) c hstage
  have hrate :
      phaseSevenBandRate n ≤
        ENNReal.ofReal
          (((2 * Q : ℕ) : ℝ) /
            ((n : ℝ) * ((n : ℝ) - 1))) := by
    simpa [Q] using
      phaseSevenBandRate_le_blockRate
        (L := L) (K := K) hn hM sigma ell j c hc
  calc
    (∫⁻ c', (bandCountN (L := L) (K := K) sigma j c' : ℝ≥0∞)
        ∂(NonuniformMajority L K).transitionKernel c) ≤
      (1 - ENNReal.ofReal
        (((2 * Q : ℕ) : ℝ) /
          ((n : ℝ) * ((n : ℝ) - 1)))) *
        bandCountN (L := L) (K := K) sigma j c := hq
    _ ≤ (1 - phaseSevenBandRate n) *
        bandCountN (L := L) (K := K) sigma j c := by
      apply mul_le_mul_right'
      exact tsub_le_tsub_left hrate 1

/-- Named stopped failure event at deterministic time `s`.  It asks that the
exact consumer and lower-band invariant persist until the deadline, but that
the current band is still nonempty at the deadline. -/
def phaseSevenSingleBandFailureAt
    (init : Cfg L K) (n M : ℕ) (sigma : Sign)
    (ell j : Fin (L + 1)) (s : ℕ) : Set (Ω L K) :=
  {omega |
    SingleBandReady n M sigma ell j (trace init omega s) ∧
      (∀ u, s ≤ u → u < s + phaseSevenBandHorizon n →
        SingleBandReady n M sigma ell j (trace init omega u)) ∧
      1 ≤ bandCountN (L := L) (K := K) sigma j
        (trace init omega (s + phaseSevenBandHorizon n))}

private theorem measurableSet_trace_state
    (init : Cfg L K) (t : ℕ) (P : Cfg L K → Prop) :
    MeasurableSet {omega : Ω L K | P (trace init omega t)} :=
  (Set.to_countable {c : Cfg L K | P c}).measurableSet.preimage
    ((measurable_pi_apply t).comp (measurable_trace init))

private theorem measurableSet_singleBandAlive
    (init : Cfg L K) (n M : ℕ) (sigma : Sign)
    (ell j : Fin (L + 1)) (s : ℕ) :
    MeasurableSet
      {omega : Ω L K |
        ∀ u, s ≤ u → u < s + phaseSevenBandHorizon n →
          SingleBandReady n M sigma ell j (trace init omega u)} := by
  rw [show
    {omega : Ω L K |
      ∀ u, s ≤ u → u < s + phaseSevenBandHorizon n →
        SingleBandReady n M sigma ell j (trace init omega u)} =
      ⋂ u : ℕ,
        {omega : Ω L K |
          s ≤ u → u < s + phaseSevenBandHorizon n →
            SingleBandReady n M sigma ell j
              (trace init omega u)} by
    ext omega
    simp]
  apply MeasurableSet.iInter
  intro u
  by_cases hsu : s ≤ u
  · by_cases hut : u < s + phaseSevenBandHorizon n
    · simpa [hsu, hut] using
        measurableSet_trace_state init u
          (fun c => SingleBandReady n M sigma ell j c)
    · simp [hut]
  · simp [hsu]

/-- The named failure event is measurable under the original pair-log
measurable space. -/
theorem measurableSet_phaseSevenSingleBandFailureAt
    (init : Cfg L K) (n M : ℕ) (sigma : Sign)
    (ell j : Fin (L + 1)) (s : ℕ) :
    MeasurableSet
      (phaseSevenSingleBandFailureAt init n M sigma ell j s) := by
  unfold phaseSevenSingleBandFailureAt
  exact
    (measurableSet_trace_state init s
      (fun c => SingleBandReady n M sigma ell j c)).inter
      ((measurableSet_singleBandAlive init n M sigma ell j s).inter
        (measurableSet_trace_state init
          (s + phaseSevenBandHorizon n)
          (fun c => 1 ≤ bandCountN (L := L) (K := K) sigma j c)))

/-- Original-law stopped expected-count bound at a deterministic start time.
This is `TraceDrain.potential_drift_tail_from`, not conditioning on survival. -/
theorem law_phaseSevenSingleBandFailureAt_raw
    (init : Cfg L K)
    (hn : 2 ≤ n) (hM : 12 * n ≤ 25 * M)
    (sigma : Sign) (ell j : Fin (L + 1))
    (hjl : ell.val ≤ j.val) (hjtop : j.val < ell.val + 3)
    (s : ℕ) :
    law init
        (phaseSevenSingleBandFailureAt init n M sigma ell j s) ≤
      (1 - phaseSevenBandRate n) ^ phaseSevenBandHorizon n * n := by
  let W : Cfg L K → Prop :=
    fun c => SingleBandReady n M sigma ell j c
  let A : Set ((k : Finset.Iic s) → Draw L K) :=
    {p | W (prefixCfg init s p)}
  have hcount : ∀ p ∈ A,
      bandCountN (L := L) (K := K) sigma j
          (prefixCfg init s p) ≤ n := by
    intro p hp
    change SingleBandReady n M sigma ell j
      (prefixCfg init s p) at hp
    exact
      (bandCountN_le_card (L := L) (K := K) sigma j
        (prefixCfg init s p)).trans_eq hp.consumer.genuine.1
  have htail :=
    TraceDrain.potential_drift_tail_from init
      (fun c => bandCountN (L := L) (K := K) sigma j c)
      W (phaseSevenBandRate n)
      (phaseSevenSingleBandDrift
        (L := L) (K := K) hn hM sigma ell j hjl hjtop)
      s (phaseSevenBandHorizon n) A n hcount
  have htail' :
      law init
          (phaseSevenSingleBandFailureAt init n M sigma ell j s) ≤
        (1 - phaseSevenBandRate n) ^ phaseSevenBandHorizon n * n *
          law init {omega | W (trace init omega s)} := by
    simpa [phaseSevenSingleBandFailureAt, A, W, TimeTheorem.trace]
      using htail
  calc
    law init
        (phaseSevenSingleBandFailureAt init n M sigma ell j s) ≤
      (1 - phaseSevenBandRate n) ^ phaseSevenBandHorizon n * n *
        law init {omega | W (trace init omega s)} := htail'
    _ ≤ (1 - phaseSevenBandRate n) ^ phaseSevenBandHorizon n * n * 1 := by
      gcongr
      exact prob_le_one
    _ = (1 - phaseSevenBandRate n) ^ phaseSevenBandHorizon n * n := by
      rw [mul_one]

private theorem phaseSevenRealBudgetIdentity
    (n : ℕ) (hn : 2 ≤ n) :
    (n : ℝ) *
        Real.exp (-(2418 / 3125 : ℝ) * 6 * Real.log (n : ℝ)) =
      Real.rpow (n : ℝ) (-(11383 / 3125 : ℝ)) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast (show 0 < n by omega)
  calc
    (n : ℝ) *
        Real.exp (-(2418 / 3125 : ℝ) * 6 * Real.log (n : ℝ)) =
      Real.exp (Real.log (n : ℝ)) *
        Real.exp (-(2418 / 3125 : ℝ) * 6 * Real.log (n : ℝ)) := by
          rw [Real.exp_log hnpos]
    _ = Real.exp
        (Real.log (n : ℝ) +
          (-(2418 / 3125 : ℝ) * 6 * Real.log (n : ℝ))) := by
          rw [Real.exp_add]
    _ = Real.exp
        (Real.log (n : ℝ) * (-(11383 / 3125 : ℝ))) := by
          congr 1
          ring
    _ = Real.rpow (n : ℝ) (-(11383 / 3125 : ℝ)) :=
      (Real.rpow_def_of_pos hnpos (-(11383 / 3125 : ℝ))).symm

/-- The exact identity
`n * exp(-.77376 * 6 * ln n) = n^(-3.64256)`. -/
theorem phaseSevenSingleBandBudget_eq_exp
    (n : ℕ) (hn : 2 ≤ n) :
    phaseSevenSingleBandBudget n =
      ENNReal.ofReal
        ((n : ℝ) *
          Real.exp (-(2418 / 3125 : ℝ) * 6 * Real.log (n : ℝ))) := by
  unfold phaseSevenSingleBandBudget
  rw [← phaseSevenRealBudgetIdentity n hn]

/-- Scalar calibration of one block. -/
theorem phaseSevenSingleBandScalar
    (n : ℕ) (hn : 2 ≤ n) :
    (1 - phaseSevenBandRate n) ^ phaseSevenBandHorizon n * n ≤
      phaseSevenSingleBandBudget n := by
  let r : ℝ := (2418 / 3125 : ℝ) / (n : ℝ)
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hr : 0 ≤ r := by
    dsimp [r]
    positivity
  have hrone : r ≤ 1 := by
    dsimp [r]
    apply (div_le_one hnpos).2
    linarith
  have hbase : 0 ≤ 1 - r := by linarith
  have hcast :
      1 - phaseSevenBandRate n = ENNReal.ofReal (1 - r) := by
    unfold phaseSevenBandRate
    dsimp [r]
    rw [ENNReal.ofReal_sub _ hr, ENNReal.ofReal_one]
  rw [hcast, ← ENNReal.ofReal_pow hbase]
  rw [show (n : ℝ≥0∞) = ENNReal.ofReal (n : ℝ) by
    exact (ENNReal.ofReal_natCast n).symm]
  rw [← ENNReal.ofReal_mul (pow_nonneg hbase _)]
  unfold phaseSevenSingleBandBudget phaseSevenBandHorizon
  apply ENNReal.ofReal_le_ofReal
  have hceil :
      (6 : ℝ) * (n : ℝ) * Real.log (n : ℝ) ≤
        (logWindow n 6 : ℝ) := by
    unfold logWindow
    exact Nat.le_ceil _
  have hprod := mul_le_mul_of_nonneg_left hceil hr
  have hexp :
      (14508 / 3125 : ℝ) * Real.log (n : ℝ) ≤
        r * (logWindow n 6 : ℝ) := by
    have heq :
        r * ((6 : ℝ) * (n : ℝ) * Real.log (n : ℝ)) =
          (14508 / 3125 : ℝ) * Real.log (n : ℝ) := by
      dsimp [r]
      field_simp [hnpos.ne']
      ring
    rwa [heq] at hprod
  calc
    (1 - r) ^ logWindow n 6 * (n : ℝ) ≤
        Real.exp (-r) ^ logWindow n 6 * (n : ℝ) := by
      apply mul_le_mul_of_nonneg_right
      · exact pow_le_pow_left₀ hbase
          (by linarith [Real.add_one_le_exp (-r)]) _
      · positivity
    _ = Real.exp (-(r * (logWindow n 6 : ℝ))) * (n : ℝ) := by
      rw [← Real.exp_nat_mul]
      congr 2
      ring
    _ ≤ Real.exp
          (-(14508 / 3125 : ℝ) * Real.log (n : ℝ)) * (n : ℝ) := by
      apply mul_le_mul_of_nonneg_right
      · exact Real.exp_le_exp.mpr (by linarith only [hexp])
      · positivity
    _ = (n : ℝ) *
        Real.exp (-(2418 / 3125 : ℝ) * 6 * Real.log (n : ℝ)) := by
      rw [mul_comm]
      congr 1
      congr 1
      ring
    _ = Real.rpow (n : ℝ) (-(11383 / 3125 : ℝ)) :=
      phaseSevenRealBudgetIdentity n hn

/-- **Single-band Lemma-12 step under the original law.** -/
theorem law_phaseSevenSingleBandFailureAt
    (init : Cfg L K)
    (hn : 2 ≤ n) (hM : 12 * n ≤ 25 * M)
    (sigma : Sign) (ell j : Fin (L + 1))
    (hjl : ell.val ≤ j.val) (hjtop : j.val < ell.val + 3)
    (s : ℕ) :
    law init
        (phaseSevenSingleBandFailureAt init n M sigma ell j s) ≤
      phaseSevenSingleBandBudget n :=
  (law_phaseSevenSingleBandFailureAt_raw
    (L := L) (K := K) init hn hM sigma ell j hjl hjtop s).trans
      (phaseSevenSingleBandScalar n hn)

/-!
THEOREM LIST
* `phaseSevenSingleBandDrift`
* `phaseSevenSingleBandFailureAt`
* `measurableSet_phaseSevenSingleBandFailureAt`
* `law_phaseSevenSingleBandFailureAt_raw`
* `phaseSevenSingleBandBudget_eq_exp`
* `phaseSevenSingleBandScalar`
* `law_phaseSevenSingleBandFailureAt`

CLOSES
* The actual-scheduler one-step hazard for the currently lowest uncleared band.
* The original pair-log stopped expected-count argument from deterministic
  time `s`.
* Measurability of the named failure set.
* The exact unconditional bound
  `n exp(-.77376 * 6 ln n) = n^(-3.64256)`.

CARRIED PREMISES AND PRODUCERS
* `hn : 2 ≤ n`: population regime.
* `hM : 12*n ≤ 25*M`: exactly
  `StrongSeedDensity.mains_lower`, carried by the Lemma-11 receipt data.
* `hjl`, `hjtop`: the choice `j ∈ {ell,ell+1,ell+2}`.
* `SingleBandReady` at the start and while alive: on the receipt route its
  `PhaseSevenBandConsumer` fields come from `LemmaElevenPathReceipt.simple_at`,
  `fuelLedger_at`, and the actual Phase-7 route; `lower_clear` comes from the
  preceding band stage.
* Persistence is part of the stopped failure event, not a premise quantified
  over all logs or arbitrary configurations.

STOPPING ARGUMENT
* This file uses the supermartingale/expected-count route:
  `TraceDrain.potential_drift_tail_from` at a deterministic recorded time `s`.
  It invokes the original pair-log one-step Markov identity and stops when
  `SingleBandReady` fails.  It does not condition on that future survival.

UNFINISHED
* Splicing the deterministic-time theorem over the genuine stopping time at
  which the preceding band clears.  The intended downstream tool is
  `PairLog.genuine_seed_splice`; no new local tail is needed.
* The union over the three bands, Phase-7 synchronization, timer protection,
  and the `21 n ln n + O(1)` work comparison belong to later Lemma-12 files.
END
-/

end Ripple.PopulationProtocol.ExactMajority.LateLemmaTwelveSingleBand

end
