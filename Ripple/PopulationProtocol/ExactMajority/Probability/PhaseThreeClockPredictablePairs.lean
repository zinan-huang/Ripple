-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockPredictablePairs.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockProbabilityFloors

/-!
# Selected-pair laws for an augmented observed prefix

A marked population depends on the full recorded past, not merely on the
current protocol labelling. This file allows the pair predicate to depend
on that entire finite prefix and derives its exact conditional probability
under law init from the actual selected-pair mass formula.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal BigOperators MeasureTheory ProbabilityTheory

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockPredictablePairs

open TimeTheorem PairLog PairLogAuxiliary

variable {L K m : ℕ}

open Classical in
def pairSet (P : Fin m → Fin m → Prop) : Finset (Fin m × Fin m) :=
  Finset.univ.filter (fun ij => ij.1 ≠ ij.2 ∧ P ij.1 ij.2)

open Classical in
theorem prefix_pair_conditional_probability (init : Cfg L K) (hc : 2 ≤ init.card)
    (t : ℕ)
    (P : ((k : Finset.Iic t) → Draw L K) → Fin init.card → Fin init.card → Prop) :
    (law init)[fun ω =>
      if ∃ i j, drawLabels init ω (t + 1) = some (i, j) ∧
        P (frestrictLe t ω) i j then (1 : ℝ) else 0 | pairLogFiltration L K t] =ᵐ[law init]
      fun ω => ((pairSet (P (frestrictLe t ω))).card : ℝ) /
        ((init.card : ℝ) * ((init.card : ℝ) - 1)) := by
  let A : ((k : Finset.Iic t) → Draw L K) → Draw L K → Prop :=
    fun p d => ∃ i j, selectLabels (prefixLabels init t p) d = some (i, j) ∧ P p i j
  let q : ((k : Finset.Iic t) → Draw L K) → ℝ≥0∞ := fun p =>
    ((pairSet (P p)).card : ℝ≥0∞) *
      ((init.card * (init.card - 1) : ℕ) : ℝ≥0∞)⁻¹
  have hmass (p : (k : Finset.Iic t) → Draw L K) :
      (drawLaw (prefixCfg init t p)).toMeasure {d | A p d} = q p := by
    rw [← prefixLabels_config]
    exact selected_pair_event_mass (prefixLabels init t p) (prefixLabels init t p) hc
      (fun _ i j => P p i j)
  have h := pairLog_condExp_indicator_of_prefix_mass init t A q hmass
  have hfun : (fun ω =>
      if ∃ i j, drawLabels init ω (t + 1) = some (i, j) ∧
        P (frestrictLe t ω) i j then (1 : ℝ) else 0) =
      (fun ω => @ite ℝ (A (frestrictLe t ω) (ω (t + 1)))
        (Classical.propDecidable _) 1 0) := by
    funext ω
    congr 1
  rw [hfun]
  filter_upwards [h] with ω hω
  refine hω.trans ?_
  change (((pairSet (P (frestrictLe t ω))).card : ℝ≥0∞) *
    ((init.card * (init.card - 1) : ℕ) : ℝ≥0∞)⁻¹).toReal = _
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    ENNReal.toReal_natCast]
  simp only [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ init.card),
    Nat.cast_one, div_eq_mul_inv]

open Classical in
theorem prefix_pair_indicator_stronglyMeasurable (init : Cfg L K) (t : ℕ)
    (P : ((k : Finset.Iic t) → Draw L K) → Fin init.card → Fin init.card → Prop) :
    StronglyMeasurable[pairLogFiltration L K (t + 1)] (fun ω =>
      if ∃ i j, drawLabels init ω (t + 1) = some (i, j) ∧
        P (frestrictLe t ω) i j then (1 : ℝ) else 0) := by
  let trunc : (Finset.Iic (t + 1) → Draw L K) → (Finset.Iic t → Draw L K) :=
    fun p k => p ⟨k.val, Finset.mem_Iic.mpr
      (le_trans (Finset.mem_Iic.mp k.property) (Nat.le_succ t))⟩
  let H : (Finset.Iic (t + 1) → Draw L K) → ℝ := fun p =>
    if ∃ i j, selectLabels (prefixLabels init t (trunc p))
        (p ⟨t + 1, Finset.mem_Iic.mpr le_rfl⟩) = some (i, j) ∧ P (trunc p) i j
      then 1 else 0
  change StronglyMeasurable[pairLogFiltration L K (t + 1)]
    (fun ω => H (frestrictLe (t + 1) ω))
  exact ((measurable_of_countable H).comp
    (measurable_pairLog_prefix L K (t + 1))).stronglyMeasurable

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockPredictablePairs

end
