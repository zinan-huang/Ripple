-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockRareDrips.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockImmigrationTails

/-!
# The original-law rare high-drip count

A high drip is recorded only when its current lower front is below the
cutoff and its current upper front has at most B labels. These guards are
read before the selected pair. The resulting raw-period count has a
prefix-weighted Chernoff bound under the original scheduler law.

This is the stochastic count estimate used in the rare-chain argument.
The deterministic charging of successive maximum increases to these
drips, and the induction that supplies the upper-front guard, are not
asserted here.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal BigOperators MeasureTheory ProbabilityTheory

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockRareDrips

open TimeTheorem PairLog PairLogAuxiliary PhaseThreeScalar
  PhaseThreeClockVirtual PhaseThreeClockGatedLaw
  PhaseThreeClockPredictablePairs PhaseThreeClockEarlyMarks
  PhaseThreeClockEarlyMarkRates PhaseThreeClockPrefixTails
  PhaseThreeClockThinning

variable {L K m : ℕ}

/-- An actual equal-minute, below-cap pair above the lower level, killed
by current observed front bounds. The distinctness of the two labels is
supplied by pairSet and by the selected-pair event. -/
def SparseHighDrip (f : Fin m → AgentState L K)
    (k cutoff B : ℕ) (i j : Fin m) : Prop :=
  frontCount f k < cutoff ∧
    frontCount f (k + 1) ≤ B ∧
    i ∈ aboveSet f (k + 1) ∧
    j ∈ aboveSet f (k + 1) ∧
    effMinute (f i) = effMinute (f j) ∧
    effMinute (f i) < K * (L + 1)

theorem sparseHighDrip_pairSet_card_le (f : Fin m → AgentState L K)
    (k cutoff B : ℕ) :
    (pairSet (SparseHighDrip f k cutoff B)).card ≤ B ^ 2 := by
  classical
  by_cases hguard : frontCount f k < cutoff ∧ frontCount f (k + 1) ≤ B
  · have hsub : pairSet (SparseHighDrip f k cutoff B) ⊆
        aboveSet f (k + 1) ×ˢ aboveSet f (k + 1) := by
      intro ij hij
      have hp := (Finset.mem_filter.mp hij).2.2
      exact Finset.mem_product.mpr ⟨hp.2.2.1, hp.2.2.2.1⟩
    calc
      (pairSet (SparseHighDrip f k cutoff B)).card ≤
          (aboveSet f (k + 1) ×ˢ aboveSet f (k + 1)).card :=
        Finset.card_le_card hsub
      _ = frontCount f (k + 1) ^ 2 := by
        simp only [Finset.card_product, frontCount, pow_two]
      _ ≤ B ^ 2 := by
        simpa only [pow_two] using Nat.mul_le_mul hguard.2 hguard.2
  · have heq : pairSet (SparseHighDrip f k cutoff B) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro ij hij
      have hp := (Finset.mem_filter.mp hij).2.2
      exact hguard ⟨hp.1, hp.2.1⟩
    rw [heq, Finset.card_empty]
    exact Nat.zero_le _

theorem sparseHighDrip_of_earlyDrip (f : Fin m → AgentState L K)
    (k cutoff B ℓ otherCutoff : ℕ) (i j : Fin m)
    (hℓ : k + 1 ≤ ℓ) (hlower : frontCount f k < cutoff)
    (hupper : frontCount f (k + 1) ≤ B)
    (h : EarlyDrip (clockSet f) f ℓ otherCutoff i j) :
    SparseHighDrip f k cutoff B i j := by
  have hi := h.2.2.1
  have hj := h.2.2.2
  simp only [sourceSet, clockSet, Finset.mem_filter, Finset.mem_univ,
    true_and] at hi hj
  refine ⟨hlower, hupper, ?_, ?_, hi.2.trans hj.2.symm, ?_⟩
  · simp only [aboveSet, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hi.1, by rw [hi.2]; exact hℓ⟩
  · simp only [aboveSet, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hj.1, by rw [hj.2]; exact hℓ⟩
  · rw [hi.2]
    exact h.2.1

open Classical in
def rareDripIndicator (init : Cfg L K) (k cutoff B t : ℕ)
    (ω : Ω L K) : ℝ :=
  if ∃ i j, drawLabels init ω (t + 1) = some (i, j) ∧
    SparseHighDrip (virtualLabels init ω t) k cutoff B i j then 1 else 0

open Classical in
theorem rareDripIndicator_prefix (init : Cfg L K) (k cutoff B t : ℕ) :
    rareDripIndicator init k cutoff B t =
      (fun ω => if ∃ i j, drawLabels init ω (t + 1) = some (i, j) ∧
        SparseHighDrip (auxPrefix init virtualRule t (frestrictLe t ω))
          k cutoff B i j then (1 : ℝ) else 0) := by
  classical
  funext ω
  unfold rareDripIndicator
  dsimp only [virtualLabels, auxLabels]
  split_ifs <;> rfl

theorem rareDripIndicator_stronglyMeasurable (init : Cfg L K)
    (k cutoff B t : ℕ) :
    StronglyMeasurable[pairLogFiltration L K (t + 1)]
      (rareDripIndicator init k cutoff B t) := by
  rw [rareDripIndicator_prefix]
  exact prefix_pair_indicator_stronglyMeasurable init t
    (fun p => SparseHighDrip (auxPrefix init virtualRule t p) k cutoff B)

theorem rareDripIndicator_zero_one (init : Cfg L K)
    (k cutoff B t : ℕ) (ω : Ω L K) :
    rareDripIndicator init k cutoff B t ω = 0 ∨
      rareDripIndicator init k cutoff B t ω = 1 := by
  classical
  unfold rareDripIndicator
  split_ifs <;> simp

/-- The law is unconditional: the guards are part of the next indicator,
not hypotheses on a future successful trajectory. -/
theorem rareDripIndicator_conditional_upper (init : Cfg L K)
    (hc : 2 ≤ init.card) (k cutoff B t : ℕ) :
    (law init)[rareDripIndicator init k cutoff B t | pairLogFiltration L K t]
      ≤ᵐ[law init] fun _ => 2 * (B : ℝ) ^ 2 / (init.card : ℝ) ^ 2 := by
  rw [rareDripIndicator_prefix]
  filter_upwards [prefix_pair_conditional_probability init hc t
    (fun p => SparseHighDrip (auxPrefix init virtualRule t p) k cutoff B)]
    with ω hω
  rw [hω]
  apply immigration_rate_le
  · exact_mod_cast hc
  · exact_mod_cast sparseHighDrip_pairSet_card_le
      (auxPrefix init virtualRule t (frestrictLe t ω)) k cutoff B

def rareDripCount (init : Cfg L K) (k cutoff B u N : ℕ)
    (ω : Ω L K) : ℝ :=
  bernoulliCount (fun t => rareDripIndicator init k cutoff B (u + t)) N ω

theorem rareDripCount_stronglyMeasurable (init : Cfg L K)
    (k cutoff B u N : ℕ) :
    StronglyMeasurable[pairLogFiltration L K (u + N)]
      (rareDripCount init k cutoff B u N) := by
  have hI : ∀ t,
      StronglyMeasurable[shiftedFiltration (pairLogFiltration L K) u (t + 1)]
        (rareDripIndicator init k cutoff B (u + t)) := by
    intro t
    simpa only [shiftedFiltration_apply, Nat.add_assoc] using
      rareDripIndicator_stronglyMeasurable init k cutoff B (u + t)
  exact bernoulliCount_stronglyMeasurable hI N

theorem rareDripCount_tail_measurable (init : Cfg L K)
    (k cutoff B u N : ℕ) (r : ℝ) :
    MeasurableSet[pairLogFiltration L K (u + N)]
      {ω | r ≤ rareDripCount init k cutoff B u N ω} :=
  measurableSet_le measurable_const
    (rareDripCount_stronglyMeasurable init k cutoff B u N).measurable

/-- The actual rare-drip count, with any observed starting prefix kept as
a multiplicative probability factor. -/
theorem rareDrip_prefix_exponential_tail (init : Cfg L K)
    (hc : 2 ≤ init.card) (k cutoff B u N : ℕ)
    (E : Set (Ω L K)) (hE : MeasurableSet[pairLogFiltration L K u] E)
    (θ r : ℝ) (hθ : 0 ≤ θ) :
    (law init).real (E ∩ {ω | r ≤ rareDripCount init k cutoff B u N ω}) ≤
      Real.exp ((Real.exp θ - 1) *
        (2 * (B : ℝ) ^ 2 / (init.card : ℝ) ^ 2) * (N : ℝ) - θ * r) *
        (law init).real E := by
  have hI : ∀ t,
      StronglyMeasurable[shiftedFiltration (pairLogFiltration L K) u (t + 1)]
        (rareDripIndicator init k cutoff B (u + t)) := by
    intro t
    simpa only [shiftedFiltration_apply, Nat.add_assoc] using
      rareDripIndicator_stronglyMeasurable init k cutoff B (u + t)
  have hz : ∀ t, ∀ᵐ ω ∂law init,
      rareDripIndicator init k cutoff B (u + t) ω = 0 ∨
        rareDripIndicator init k cutoff B (u + t) ω = 1 :=
    fun t => ae_of_all _ (rareDripIndicator_zero_one init k cutoff B (u + t))
  have hcoef : ∀ t, ∀ᵐ ω ∂law init,
      (Real.exp θ - 1) *
          (law init)[rareDripIndicator init k cutoff B (u + t) |
            shiftedFiltration (pairLogFiltration L K) u t] ω ≤
        (Real.exp θ - 1) * (2 * (B : ℝ) ^ 2 / (init.card : ℝ) ^ 2) := by
    intro t
    filter_upwards [rareDripIndicator_conditional_upper init hc k cutoff B (u + t)]
      with ω hω
    exact mul_le_mul_of_nonneg_left hω
      (sub_nonneg.mpr (Real.one_le_exp hθ))
  have hEs : MeasurableSet[shiftedFiltration (pairLogFiltration L K) u 0] E := by
    simpa only [shiftedFiltration_apply, Nat.add_zero] using hE
  have ht := prefix_bernoulli_exponential_tail_of_coefficient
    hI hz hcoef E hEs r N
  apply (measureReal_mono ?_).trans ht
  rintro ω ⟨hEω, hr⟩
  exact ⟨hEω, mul_le_mul_of_nonneg_left hr hθ⟩

/-- A convenient Chernoff form for a possibly much smaller mean than the
target. Both r and mu are real so no rounding is hidden. -/
theorem rareDrip_prefix_chernoff (init : Cfg L K)
    (hc : 2 ≤ init.card) (k cutoff B u N : ℕ)
    (E : Set (Ω L K)) (hE : MeasurableSet[pairLogFiltration L K u] E)
    (μ r : ℝ) (hμ : 0 < μ) (hμr : μ ≤ r)
    (hmean : (2 * (B : ℝ) ^ 2 / (init.card : ℝ) ^ 2) * (N : ℝ) ≤ μ) :
    law init (E ∩ {ω | r ≤ rareDripCount init k cutoff B u N ω}) ≤
      ENNReal.ofReal ((Real.exp 1 * μ / r) ^ r) * law init E := by
  have hr : 0 < r := hμ.trans_le hμr
  have hratio : 1 ≤ r / μ := (le_div_iff₀ hμ).mpr (by simpa using hμr)
  have hθ : 0 ≤ Real.log (r / μ) := Real.log_nonneg hratio
  have hexp : Real.exp (Real.log (r / μ)) = r / μ :=
    Real.exp_log (div_pos hr hμ)
  have hscaled := mul_le_mul_of_nonneg_left hmean
    (sub_nonneg.mpr hratio)
  have hcancel : (r / μ - 1) * μ = r - μ := by
    field_simp [ne_of_gt hμ]
    <;> ring
  have harg :
      (Real.exp (Real.log (r / μ)) - 1) *
          (2 * (B : ℝ) ^ 2 / (init.card : ℝ) ^ 2) * (N : ℝ) -
        Real.log (r / μ) * r ≤ r - Real.log (r / μ) * r := by
    rw [hexp]
    rw [hcancel] at hscaled
    nlinarith only [hscaled, hμ]
  have hbase : 0 < Real.exp 1 * μ / r :=
    div_pos (mul_pos (Real.exp_pos _) hμ) hr
  have hidentity :
      Real.exp (r - Real.log (r / μ) * r) = (Real.exp 1 * μ / r) ^ r := by
    rw [Real.rpow_def_of_pos hbase,
      Real.log_div (ne_of_gt (mul_pos (Real.exp_pos _) hμ)) (ne_of_gt hr),
      Real.log_mul (ne_of_gt (Real.exp_pos _)) (ne_of_gt hμ),
      Real.log_exp, Real.log_div (ne_of_gt hr) (ne_of_gt hμ)]
    congr 1
    ring
  apply measure_le_of_real_weighted_bound (law init) _ E _
    (Real.rpow_nonneg hbase.le _)
  have ht := rareDrip_prefix_exponential_tail init hc k cutoff B u N
    E hE (Real.log (r / μ)) r hθ
  apply ht.trans
  exact mul_le_mul_of_nonneg_right
    ((Real.exp_le_exp.mpr harg).trans_eq hidentity) ENNReal.toReal_nonneg

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockRareDrips

end
