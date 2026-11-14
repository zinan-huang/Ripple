import Ripple.PopulationProtocol.ExactMajority.Probability.PairLogAuxiliary
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingCancellationAlgebra
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingCreditTransitions
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase3Scalar

/-!
# Actual ordered-pair cancellation probabilities

The counted events involve two already active Phase-3 Mains of opposite sign
at the same index. The rest of the population may still be in earlier phases.
Both ordered orientations are counted, with the full population denominator.

The final stopped bound constructs the physical cancellation indicators and
their conditional probability. Its remaining inputs are the live count floor,
a genuine stopping time, and the deterministic implication from target failure
to too few cancellations. These inputs are not asserted for the hour induction.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal BigOperators MeasureTheory ProbabilityTheory

namespace Ripple.PopulationProtocol.ExactMajority.AveragingCancellationProbability

open TimeTheorem PairLog PairLogAuxiliary
open AveragingCancellationAlgebra PhaseThreeScalar

variable {L K m : ℕ}

/-- Active Main labels of one sign at one index. -/
def levelSet (f : Fin m → AgentState L K) (σ : Sign)
    (level : Fin (L + 1)) : Finset (Fin m) :=
  Finset.univ.filter fun i =>
    (f i).phase.val = 3 ∧ (f i).role = .main ∧
      (f i).bias = .dyadic σ level

theorem levelSets_disjoint (f : Fin m → AgentState L K)
    (level : Fin (L + 1)) :
    Disjoint (levelSet f .pos level) (levelSet f .neg level) := by
  apply Finset.disjoint_left.mpr
  intro i hi hj
  simp only [levelSet, Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
  have he : Bias.dyadic .pos level = Bias.dyadic .neg level :=
    hi.2.2.symm.trans hj.2.2
  cases he

/-- Either orientation of an active opposite-sign pair at the current index. -/
def CancellingPair (level : Fin (L + 1))
    (f : Fin m → AgentState L K) (i j : Fin m) : Prop :=
  (i ∈ levelSet f .pos level ∧ j ∈ levelSet f .neg level) ∨
    (i ∈ levelSet f .neg level ∧ j ∈ levelSet f .pos level)

theorem goodPairs_cancelling (f : Fin m → AgentState L K)
    (level : Fin (L + 1)) :
    goodPairs (CancellingPair level) f =
      (levelSet f .pos level ×ˢ levelSet f .neg level) ∪
        (levelSet f .neg level ×ˢ levelSet f .pos level) := by
  classical
  ext ⟨i, j⟩
  simp only [goodPairs, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_union, Finset.mem_product, CancellingPair]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    intro hij
    subst j
    rcases h with h | h
    · exact (Finset.disjoint_left.mp (levelSets_disjoint f level)) h.1 h.2
    · exact (Finset.disjoint_left.mp (levelSets_disjoint f level)) h.2 h.1

/-- The exact count includes both ordered orientations. -/
theorem goodPairs_cancelling_card (f : Fin m → AgentState L K)
    (level : Fin (L + 1)) :
    (goodPairs (CancellingPair level) f).card =
      2 * (levelSet f .pos level).card * (levelSet f .neg level).card := by
  classical
  rw [goodPairs_cancelling]
  have hd :
      Disjoint (levelSet f .pos level ×ˢ levelSet f .neg level)
        (levelSet f .neg level ×ˢ levelSet f .pos level) := by
    apply Finset.disjoint_left.mpr
    rintro ⟨i, j⟩ hi hj
    have hi' := Finset.mem_product.mp hi
    have hj' := Finset.mem_product.mp hj
    exact (Finset.disjoint_left.mp (levelSets_disjoint f level)) hi'.1 hj'.1
  rw [Finset.card_union_of_disjoint hd, Finset.card_product, Finset.card_product]
  ring

/-- This is a cancellation in the full dispatcher, including its epidemic and
entry wrappers, rather than only in the cancel/split helper. -/
theorem transition_cancel_opposite (s t : AgentState L K)
    (level : Fin (L + 1)) (σ τ : Sign) (hop : σ ≠ τ)
    (hs : s.phase.val = 3) (ht : t.phase.val = 3)
    (hsm : s.role = .main) (htm : t.role = .main)
    (hsb : s.bias = .dyadic σ level) (htb : t.bias = .dyadic τ level) :
    Transition L K s t =
      ({ s with bias := .zero, hour := level }, { t with bias := .zero, hour := level }) := by
  have hepi := ClockRealKernel.phaseEpidemicUpdate_eq_self_p3 s t hs ht
  have hsp : s.phase = ⟨3, by decide⟩ := Fin.ext hs
  have hwork : Phase3Transition L K s t =
      ({ s with bias := .zero, hour := level }, { t with bias := .zero, hour := level }) := by
    cases σ <;> cases τ <;> simp_all [Phase3Transition, phase3CancelSplit]
  unfold Transition
  rw [hepi]
  simp [hsp, hwork, hs, ht]

/-- The physical indicator on the actual pair log. -/
def cancellationIndicator (init : Cfg L K) (level : Fin (L + 1))
    (t : ℕ) (ω : Ω L K) : ℝ := by
  classical
  exact if ∃ i j, drawLabels init ω (t + 1) = some (i, j) ∧
      CancellingPair level (labelsAt init ω t) i j then 1 else 0

theorem cancellationIndicator_zero_or_one
    (init : Cfg L K) (level : Fin (L + 1)) (t : ℕ) (ω : Ω L K) :
    cancellationIndicator init level t ω = 0 ∨
      cancellationIndicator init level t ω = 1 := by
  classical
  unfold cancellationIndicator
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- Every counted event really sends the two selected biases to zero. -/
theorem selected_cancellingPair_bias_zero
    (init : Cfg L K) (level : Fin (L + 1)) (t : ℕ) (ω : Ω L K)
    (i j : Fin init.card)
    (hdraw : drawLabels init ω (t + 1) = some (i, j))
    (hpair : CancellingPair level (labelsAt init ω t) i j) :
    (labelsAt init ω (t + 1) i).bias = .zero ∧
      (labelsAt init ω (t + 1) j).bias = .zero := by
  obtain ⟨-, hi, hj, -⟩ := labelsAt_selected_transition init ω t i j hdraw
  rw [hi, hj]
  change (Transition L K (labelsAt init ω t i) (labelsAt init ω t j)).1.bias = .zero ∧
    (Transition L K (labelsAt init ω t i) (labelsAt init ω t j)).2.bias = .zero
  rcases hpair with hpair | hpair
  · obtain ⟨hip, hjn⟩ := hpair
    simp only [levelSet, Finset.mem_filter, Finset.mem_univ, true_and] at hip hjn
    have hc := transition_cancel_opposite _ _ level .pos .neg (by decide)
      hip.1 hjn.1 hip.2.1 hjn.2.1 hip.2.2 hjn.2.2
    simp [hc]
  · obtain ⟨hin, hjp⟩ := hpair
    simp only [levelSet, Finset.mem_filter, Finset.mem_univ, true_and] at hin hjp
    have hc := transition_cancel_opposite _ _ level .neg .pos (by decide)
      hin.1 hjp.1 hin.2.1 hjp.2.1 hin.2.2 hjp.2.2
    simp [hc]

theorem cancellationIndicator_adapted
    (init : Cfg L K) (level : Fin (L + 1)) (t : ℕ) :
    StronglyMeasurable[pairLogFiltration L K (t + 1)]
      (cancellationIndicator init level t) := by
  classical
  let pre :
      ((k : Finset.Iic (t + 1)) → Draw L K) →
        ((k : Finset.Iic t) → Draw L K) :=
    fun p k => p ⟨k.val, Finset.mem_Iic.mpr
      ((Finset.mem_Iic.mp k.property).trans (Nat.le_succ t))⟩
  let J : ((k : Finset.Iic (t + 1)) → Draw L K) → ℝ :=
    fun p => if ∃ i j,
      selectLabels (prefixLabels init t (pre p))
          (p ⟨t + 1, Finset.mem_Iic.mpr le_rfl⟩) = some (i, j) ∧
        CancellingPair level (prefixLabels init t (pre p)) i j
      then 1 else 0
  have hJ : Measurable J := by
    intro A hA
    exact (Set.to_countable _).measurableSet
  have hm : Measurable[pairLogFiltration L K (t + 1)]
      (cancellationIndicator init level t) := by
    change Measurable[pairLogFiltration L K (t + 1)]
      (fun ω => J (frestrictLe (t + 1) ω))
    exact hJ.comp (measurable_pairLog_prefix L K (t + 1))
  exact hm.stronglyMeasurable

/-- Exact conditional probability under the original pair-log law. It does not
condition on a later clock-success or averaging-success event. -/
theorem cancellation_conditional_law
    (init : Cfg L K) (hc : 2 ≤ init.card)
    (level : Fin (L + 1)) (t : ℕ) :
    (law init)[cancellationIndicator init level t | pairLogFiltration L K t]
      =ᵐ[law init]
    (fun ω =>
      (2 : ℝ) * (levelSet (labelsAt init ω t) .pos level).card *
          (levelSet (labelsAt init ω t) .neg level).card /
        ((init.card : ℝ) * ((init.card : ℝ) - 1))) := by
  classical
  have hh := aux_pair_conditional_probability init hc
    (NonuniformMajority L K).δ (CancellingPair level) t
  refine Filter.EventuallyEq.trans
    (condExp_congr_ae (Filter.Eventually.of_forall fun ω' => ?_))
    (hh.trans (Filter.Eventually.of_forall fun ω => ?_))
  · dsimp only [cancellationIndicator]
    simp only [labelsAt_eq_auxLabels_delta]
    try (split_ifs <;> rfl)
  · simp only [goodPairs_cancelling_card, labelsAt_eq_auxLabels_delta, Nat.cast_mul,
      Nat.cast_ofNat]

/-- A stopped hitting bound for the actual cancellation count. The stopping
time must incorporate target success and any failed required gate. -/
theorem cancellation_stopped_tail
    (init : Cfg L K) (hc : 2 ≤ init.card)
    (level : Fin (L + 1)) (τ : Ω L K → WithTop ℕ)
    (hτ : IsStoppingTime (pairLogFiltration L K) τ)
    {p : ℝ} (hp : p ≤ 1)
    (hproduct : ∀ t : ℕ, ∀ᵐ ω ∂law init, (t : WithTop ℕ) < τ ω →
      p * ((init.card : ℝ) * ((init.card : ℝ) - 1)) ≤
        (2 : ℝ) * (levelSet (labelsAt init ω t) .pos level).card *
          (levelSet (labelsAt init ω t) .neg level).card)
    (N : ℕ) (k : ℝ)
    (hfail : ∀ ω, (N : WithTop ℕ) < τ ω →
      bernoulliCount (cancellationIndicator init level) N ω < k) :
    (law init).real {ω | (N : WithTop ℕ) < τ ω} ≤
      Real.exp (k * Real.log 2 - (N : ℝ) * p / 2) := by
  have hn : (2 : ℝ) ≤ (init.card : ℝ) := by exact_mod_cast hc
  have hden : 0 < (init.card : ℝ) * ((init.card : ℝ) - 1) :=
    mul_pos (by linarith) (by linarith)
  have hcond : ∀ t : ℕ, ∀ᵐ ω ∂law init, (t : WithTop ℕ) < τ ω →
      p ≤ ((law init)[cancellationIndicator init level t |
        pairLogFiltration L K t]) ω := by
    intro t
    filter_upwards [cancellation_conditional_law init hc level t, hproduct t]
      with ω hlaw hprod hbefore
    rw [hlaw]
    exact (le_div_iff₀ hden).2 (hprod hbefore)
  exact adapted_success_hitting_tail
    (cancellationIndicator_adapted init level)
    (fun t => Filter.Eventually.of_forall
      (cancellationIndicator_zero_or_one init level t))
    hτ hp hcond N k hfail

/-- The cancellation block in the reviewed raw-work budget. -/
def cancellationTrials (n M : ℕ) : ℕ :=
  Nat.ceil ((40 : ℝ) * (n : ℝ) ^ 2 / (M : ℝ))

/-- The row probability floor, with the full-population denominator. -/
def cancellationChance (r : CancellationRegime) (n M : ℕ) : ℝ :=
  2 * (cancellationParameters r).1 * (cancellationParameters r).2.1 *
      (M : ℝ) ^ 2 /
    ((n : ℝ) * ((n : ℝ) - 1))

theorem cancellationChance_nonneg (r : CancellationRegime)
    {n M : ℕ} (hn : 2 ≤ n) :
    0 ≤ cancellationChance r n M := by
  obtain ⟨ha, hb, -⟩ := cancellation_parameters_nonneg r
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hpred : 0 < (n : ℝ) - 1 := by linarith
  unfold cancellationChance
  positivity

theorem cancellationChance_le_one (r : CancellationRegime)
    {n M : ℕ} (hn : 2 ≤ n) (hMn : M ≤ n) :
    cancellationChance r n M ≤ 1 := by
  obtain ⟨ha, hb, -⟩ := cancellation_parameters_nonneg r
  have hsmall :
      4 * (cancellationParameters r).1 * (cancellationParameters r).2.1 ≤
        (1 : ℝ) := by
    cases r <;> norm_num [cancellationParameters]
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hden : 0 < (n : ℝ) * ((n : ℝ) - 1) :=
    mul_pos (by linarith) (by linarith)
  have hsq : (M : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (by exact_mod_cast hMn) 2
  have hnsq : (n : ℝ) ^ 2 ≤ 2 * ((n : ℝ) * ((n : ℝ) - 1)) := by
    have hh := mul_nonneg (show (0 : ℝ) ≤ (n : ℝ) by positivity)
      (show 0 ≤ (n : ℝ) - 2 by linarith)
    nlinarith only [hh]
  have hcoef :
      0 ≤ 2 * (cancellationParameters r).1 * (cancellationParameters r).2.1 := by
    positivity
  have hfirst := mul_le_mul_of_nonneg_left hsq hcoef
  have hsecond := mul_le_mul_of_nonneg_left hnsq hcoef
  have hthird := mul_le_mul_of_nonneg_right hsmall hden.le
  unfold cancellationChance
  apply (div_le_iff₀ hden).2
  nlinarith only [hfirst, hsecond, hthird]

theorem cancellation_work_lower (r : CancellationRegime)
    {n M : ℕ} (hn : 2 ≤ n) (hM : 0 < M) :
    80 * (cancellationParameters r).1 * (cancellationParameters r).2.1 *
        (M : ℝ) ≤
      (cancellationTrials n M : ℝ) * cancellationChance r n M := by
  obtain ⟨ha, hb, -⟩ := cancellation_parameters_nonneg r
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hpred : 0 < (n : ℝ) - 1 := by linarith
  have hMR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hden := mul_pos hnpos hpred
  have hratio : 1 ≤ (n : ℝ) ^ 2 / ((n : ℝ) * ((n : ℝ) - 1)) := by
    apply (le_div_iff₀ hden).2
    nlinarith only [hnR]
  have hfactor :
      0 ≤ 80 * (cancellationParameters r).1 * (cancellationParameters r).2.1 *
        (M : ℝ) := by positivity
  have hbase :
      80 * (cancellationParameters r).1 * (cancellationParameters r).2.1 *
          (M : ℝ) ≤
        (40 * (n : ℝ) ^ 2 / (M : ℝ)) * cancellationChance r n M := by
    calc
      _ = (80 * (cancellationParameters r).1 * (cancellationParameters r).2.1 *
            (M : ℝ)) * 1 := by ring
      _ ≤ (80 * (cancellationParameters r).1 * (cancellationParameters r).2.1 *
            (M : ℝ)) *
          ((n : ℝ) ^ 2 / ((n : ℝ) * ((n : ℝ) - 1))) :=
        mul_le_mul_of_nonneg_left hratio hfactor
      _ = _ := by
        unfold cancellationChance
        field_simp [ne_of_gt hnpos, ne_of_gt hpred, ne_of_gt hMR] <;> ring
  have hceil :
      40 * (n : ℝ) ^ 2 / (M : ℝ) ≤ (cancellationTrials n M : ℝ) :=
    Nat.le_ceil _
  exact hbase.trans
    (mul_le_mul_of_nonneg_right hceil (cancellationChance_nonneg r hn))

/-- Every numerical row gives the reviewed exponential bound once its actual
live count-product floor and deterministic failure implication are established.
The only probabilistic law used here is the original pair-log law. -/
theorem cancellation_regime_stopped_tail
    (init : Cfg L K) (hc : 2 ≤ init.card)
    (level : Fin (L + 1)) (r : CancellationRegime) (M : ℕ)
    (hM : 0 < M) (hMn : M ≤ init.card)
    (τ : Ω L K → WithTop ℕ)
    (hτ : IsStoppingTime (pairLogFiltration L K) τ)
    (hcounts : ∀ t : ℕ, ∀ᵐ ω ∂law init, (t : WithTop ℕ) < τ ω →
      (cancellationParameters r).1 * (cancellationParameters r).2.1 *
          (M : ℝ) ^ 2 ≤
        ((levelSet (labelsAt init ω t) .pos level).card : ℝ) *
          (levelSet (labelsAt init ω t) .neg level).card)
    (hfail : ∀ ω,
      (cancellationTrials init.card M : WithTop ℕ) < τ ω →
        bernoulliCount (cancellationIndicator init level)
            (cancellationTrials init.card M) ω <
          (cancellationParameters r).2.2 * (M : ℝ)) :
    (law init).real
        {ω | (cancellationTrials init.card M : WithTop ℕ) < τ ω} ≤
      Real.exp (-(M : ℝ) / 1000) := by
  have hn : (2 : ℝ) ≤ (init.card : ℝ) := by exact_mod_cast hc
  have hnpos : (0 : ℝ) < (init.card : ℝ) := by linarith
  have hpred : 0 < (init.card : ℝ) - 1 := by linarith
  have hproduct : ∀ t : ℕ, ∀ᵐ ω ∂law init, (t : WithTop ℕ) < τ ω →
      cancellationChance r init.card M *
          ((init.card : ℝ) * ((init.card : ℝ) - 1)) ≤
        (2 : ℝ) * (levelSet (labelsAt init ω t) .pos level).card *
          (levelSet (labelsAt init ω t) .neg level).card := by
    intro t
    filter_upwards [hcounts t] with ω hω hbefore
    have heq :
        cancellationChance r init.card M *
            ((init.card : ℝ) * ((init.card : ℝ) - 1)) =
          2 * (cancellationParameters r).1 * (cancellationParameters r).2.1 *
            (M : ℝ) ^ 2 := by
      unfold cancellationChance
      field_simp [ne_of_gt hnpos, ne_of_gt hpred] <;> ring
    rw [heq]
    nlinarith only [hω hbefore]
  exact
    (cancellation_stopped_tail init hc level τ hτ
      (cancellationChance_le_one r hc hMn) hproduct
      (cancellationTrials init.card M)
      ((cancellationParameters r).2.2 * (M : ℝ)) hfail).trans
    (cancellation_exponent_bound r (M := (M : ℝ))
      (by positivity) le_rfl (cancellation_work_lower r hc hM))

end Ripple.PopulationProtocol.ExactMajority.AveragingCancellationProbability

end
