import Ripple.PopulationProtocol.Majority.SSEM.UpperBound.Time.DisruptionTail
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Pi

namespace SSEM
namespace Probability

open scoped BigOperators ENNReal

variable {n : ℕ}

/-!
# Selection-count tails for the finite scheduler prefix

The finite scheduler-prefix measure used here is the product PMF on
`SchedulerPrefix n K = Fin K → Fin n × Fin n`, with each coordinate sampled
from `uniformPair n hn`.
-/

/-- Product weight of a concrete scheduler prefix. -/
noncomputable def schedulerPrefixWeight
    (n : ℕ) (hn : 2 ≤ n) (K : ℕ) (σ : SchedulerPrefix n K) : ENNReal :=
  ∏ t : Fin K, uniformPair n hn (σ t)

theorem schedulerPrefixWeight_sum
    (n : ℕ) (hn : 2 ≤ n) (K : ℕ) :
    ∑ σ : SchedulerPrefix n K, schedulerPrefixWeight n hn K σ = 1 := by
  classical
  have hstep :
      ∑ p : Fin n × Fin n, uniformPair n hn p = (1 : ENNReal) := by
    simpa [tsum_fintype] using (uniformPair n hn).tsum_coe
  have hprod :=
    (Finset.prod_univ_sum
      (R := ENNReal)
      (ι := Fin K)
      (κ := fun _ : Fin K => Fin n × Fin n)
      (t := fun _ : Fin K => (Finset.univ : Finset (Fin n × Fin n)))
      (f := fun _ p => uniformPair n hn p)).symm
  calc
    ∑ σ : SchedulerPrefix n K, schedulerPrefixWeight n hn K σ
        = ∏ _t : Fin K, ∑ p : Fin n × Fin n, uniformPair n hn p := by
          simpa [schedulerPrefixWeight, Fintype.piFinset_univ] using hprod
    _ = 1 := by
          simp [hstep]

/-- The `K`-step scheduler-prefix product PMF. -/
noncomputable def schedulerPrefixPMF
    (n : ℕ) (hn : 2 ≤ n) (K : ℕ) : PMF (SchedulerPrefix n K) :=
  PMF.ofFintype (schedulerPrefixWeight n hn K)
    (schedulerPrefixWeight_sum n hn K)

@[simp]
theorem schedulerPrefixPMF_apply
    (n : ℕ) (hn : 2 ≤ n) (K : ℕ) (σ : SchedulerPrefix n K) :
    schedulerPrefixPMF n hn K σ = schedulerPrefixWeight n hn K σ := rfl

theorem uniformPair_apply_ne_zero_iff
    (n : ℕ) (hn : 2 ≤ n) (p : Fin n × Fin n) :
    uniformPair n hn p ≠ 0 ↔ p.1 ≠ p.2 := by
  constructor
  · intro hp hdiag
    rcases p with ⟨i, j⟩
    dsimp at hdiag
    subst j
    exact hp (uniformPair_apply_self n hn i)
  · intro hp
    rw [uniformPair_apply_of_ne n hn hp]
    exact ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _)

theorem schedulerPrefixPMF_support
    (n : ℕ) (hn : 2 ≤ n) (K : ℕ) :
    (schedulerPrefixPMF n hn K).support =
      {σ : SchedulerPrefix n K | ∀ t : Fin K, (σ t).1 ≠ (σ t).2} := by
  classical
  ext σ
  simp only [PMF.mem_support_iff, Set.mem_setOf_eq, schedulerPrefixPMF_apply,
    schedulerPrefixWeight]
  rw [Finset.prod_ne_zero_iff]
  constructor
  · intro h t
    exact (uniformPair_apply_ne_zero_iff n hn (σ t)).mp (h t (Finset.mem_univ t))
  · intro h t _ht
    exact (uniformPair_apply_ne_zero_iff n hn (σ t)).mpr (h t)

/-- Coordinate set for a selected-on-`T` cylinder, intersected with the
off-diagonal support on every coordinate. -/
def selectedOnCoordSet {K : ℕ}
    (n : ℕ) (a : Fin n) (T : Finset (Fin K)) (t : Fin K) :
    Finset (Fin n × Fin n) :=
  if t ∈ T then PairsInvolving n a else OffDiagonalPairs n

/-- Finset of scheduler prefixes in the selected-on-`T` cylinder support. -/
def selectedOnSupportFinset {K : ℕ}
    (n : ℕ) (a : Fin n) (T : Finset (Fin K)) :
    Finset (SchedulerPrefix n K) :=
  Fintype.piFinset (selectedOnCoordSet n a T)

theorem mem_selectedOnSupportFinset_iff {K : ℕ}
    (a : Fin n) (T : Finset (Fin K)) (σ : SchedulerPrefix n K) :
    σ ∈ selectedOnSupportFinset n a T ↔
      PrefixAgentSelectedOn σ a T ∧
        ∀ t : Fin K, (σ t).1 ≠ (σ t).2 := by
  classical
  constructor
  · intro hσ
    have hcoord :
        ∀ t : Fin K, σ t ∈ selectedOnCoordSet n a T t :=
      Fintype.mem_piFinset.mp hσ
    constructor
    · intro t ht
      have htMem : σ t ∈ PairsInvolving n a := by
        simpa [selectedOnCoordSet, ht] using hcoord t
      have htouch := (mem_PairsInvolving n a (σ t)).mp htMem
      rcases htouch.2 with hleft | hright
      · exact Or.inl hleft.symm
      · exact Or.inr hright.symm
    · intro t
      by_cases ht : t ∈ T
      · have htMem : σ t ∈ PairsInvolving n a := by
          simpa [selectedOnCoordSet, ht] using hcoord t
        exact ((mem_PairsInvolving n a (σ t)).mp htMem).1
      · have htMem : σ t ∈ OffDiagonalPairs n := by
          simpa [selectedOnCoordSet, ht] using hcoord t
        exact (mem_offDiagonalPairs n (σ t)).mp htMem
  · intro hσ
    rcases hσ with ⟨hsel, hoff⟩
    apply Fintype.mem_piFinset.mpr
    intro t
    by_cases ht : t ∈ T
    · have htouch := hsel t ht
      rw [selectedOnCoordSet, if_pos ht]
      apply (mem_PairsInvolving n a (σ t)).mpr
      refine ⟨hoff t, ?_⟩
      rcases htouch with hleft | hright
      · exact Or.inl hleft.symm
      · exact Or.inr hright.symm
    · rw [selectedOnCoordSet, if_neg ht]
      exact (mem_offDiagonalPairs n (σ t)).mpr (hoff t)

theorem schedulerPrefix_selectedOn_mass
    (hn : 2 ≤ n) (a : Fin n) {K : ℕ} (T : Finset (Fin K)) :
    (schedulerPrefixPMF n hn K).toOuterMeasure
        {σ : SchedulerPrefix n K | PrefixAgentSelectedOn σ a T} =
      (((2 : ENNReal) * (n : ENNReal)⁻¹) ^ T.card) := by
  classical
  let q : ENNReal := (2 : ENNReal) * (n : ENNReal)⁻¹
  have hsupport :
      (schedulerPrefixPMF n hn K).support =
        {σ : SchedulerPrefix n K | ∀ t : Fin K, (σ t).1 ≠ (σ t).2} :=
    schedulerPrefixPMF_support n hn K
  have hinter :
      ({σ : SchedulerPrefix n K | PrefixAgentSelectedOn σ a T} ∩
          (schedulerPrefixPMF n hn K).support) =
        ((selectedOnSupportFinset n a T : Finset (SchedulerPrefix n K)) : Set _) ∩
          (schedulerPrefixPMF n hn K).support := by
    ext σ
    simp [hsupport, mem_selectedOnSupportFinset_iff, and_left_comm, and_comm]
  have hsum_prod :
      ∑ σ ∈ selectedOnSupportFinset n a T,
          schedulerPrefixWeight n hn K σ =
        ∏ t : Fin K,
          ∑ p ∈ selectedOnCoordSet n a T t, uniformPair n hn p := by
    have hprod :=
      (Finset.prod_univ_sum
        (R := ENNReal)
        (ι := Fin K)
        (κ := fun _ : Fin K => Fin n × Fin n)
        (t := selectedOnCoordSet n a T)
        (f := fun _ p => uniformPair n hn p)).symm
    simpa [selectedOnSupportFinset, schedulerPrefixWeight] using hprod
  have hcoord :
      ∀ t : Fin K,
        (∑ p ∈ selectedOnCoordSet n a T t, uniformPair n hn p) =
          if t ∈ T then q else 1 := by
    intro t
    by_cases ht : t ∈ T
    · rw [selectedOnCoordSet, if_pos ht, if_pos ht]
      change pairSetMass n hn (PairsInvolving n a) = q
      exact pairSetMass_pairsInvolving n hn a
    · rw [selectedOnCoordSet, if_neg ht, if_neg ht]
      change pairSetMass n hn (OffDiagonalPairs n) = (1 : ENNReal)
      exact pairSetMass_offDiagonalPairs n hn
  calc
    (schedulerPrefixPMF n hn K).toOuterMeasure
        {σ : SchedulerPrefix n K | PrefixAgentSelectedOn σ a T}
        =
      (schedulerPrefixPMF n hn K).toOuterMeasure
        (selectedOnSupportFinset n a T) := by
          exact PMF.toOuterMeasure_apply_eq_of_inter_support_eq
            (schedulerPrefixPMF n hn K) hinter
    _ = ∑ σ ∈ selectedOnSupportFinset n a T,
          schedulerPrefixWeight n hn K σ := by
          rw [PMF.toOuterMeasure_apply_finset]
          rfl
    _ = ∏ t : Fin K,
          ∑ p ∈ selectedOnCoordSet n a T t, uniformPair n hn p :=
          hsum_prod
    _ = ∏ t : Fin K, if t ∈ T then q else 1 := by
          exact Finset.prod_congr rfl fun t _ht => hcoord t
    _ = ∏ t ∈ T, q := by
          simp
    _ = q ^ T.card := by
          simp
    _ = (((2 : ENNReal) * (n : ENNReal)⁻¹) ^ T.card) := rfl

/-- Per-step endpoint-selection probability under the scheduler-prefix PMF. -/
theorem schedulerPrefix_selectedAt_step_mass
    (hn : 2 ≤ n) (a : Fin n) {K : ℕ} (t : Fin K) :
    (schedulerPrefixPMF n hn K).toOuterMeasure
        {σ : SchedulerPrefix n K | prefixSelectedAt σ a t} =
      (2 : ENNReal) * (n : ENNReal)⁻¹ := by
  simpa [PrefixAgentSelectedOn] using
    (schedulerPrefix_selectedOn_mass (n := n) hn a ({t} : Finset (Fin K)))

/-- Fixed-cylinder form: selecting `a` on a fixed set of time coordinates has
probability `(2/n) ^ |T|`. This is the cross-step independence statement for
the finite scheduler-prefix product PMF. -/
theorem schedulerPrefix_cylinder_selectedOn
    (hn : 2 ≤ n) (a : Fin n) {K : ℕ} (T : Finset (Fin K)) :
    (schedulerPrefixPMF n hn K).toOuterMeasure
        {σ : SchedulerPrefix n K | PrefixAgentSelectedOn σ a T} =
      (((2 : ENNReal) * (n : ENNReal)⁻¹) ^ T.card) :=
  schedulerPrefix_selectedOn_mass (n := n) hn a T

theorem schedulerPrefix_cylinder_selectedOn_le
    (hn : 2 ≤ n) (a : Fin n) {K r : ℕ}
    (T : Finset (Fin K)) (hT : T.card = r) :
    (schedulerPrefixPMF n hn K).toOuterMeasure
        {σ : SchedulerPrefix n K | PrefixAgentSelectedOn σ a T} ≤
      (((2 : ENNReal) * (n : ENNReal)⁻¹) ^ r) := by
  rw [schedulerPrefix_cylinder_selectedOn (n := n) hn a T, hT]

theorem schedulerPrefix_outerMeasure_iUnion_fintype_le
    (hn : 2 ≤ n) (K : ℕ) {ι : Type*} [Fintype ι]
    (B : ι → Set (SchedulerPrefix n K)) :
    (schedulerPrefixPMF n hn K).toOuterMeasure {σ | ∃ i : ι, σ ∈ B i} ≤
      ∑ i : ι, (schedulerPrefixPMF n hn K).toOuterMeasure (B i) := by
  have hset : {σ : SchedulerPrefix n K | ∃ i : ι, σ ∈ B i} = ⋃ i : ι, B i := by
    ext σ
    simp
  rw [hset]
  exact
    (MeasureTheory.measure_iUnion_fintype_le
      ((schedulerPrefixPMF n hn K).toOuterMeasure) B)

/-- Choose-union upper tail for one fixed agent's prefix selection count. -/
theorem selectionCount_tail_le_choose
    (hn : 2 ≤ n) (a : Fin n) (K r : ℕ) :
    (schedulerPrefixPMF n hn K).toOuterMeasure
        {σ : SchedulerPrefix n K | PrefixAgentHighLoad σ a r} ≤
      (Nat.choose K r : ENNReal) *
        (((2 : ENNReal) * (n : ENNReal)⁻¹) ^ r) := by
  classical
  exact
    prefix_agent_high_load_mass_le_choose
      (n := n) (K := K) (r := r)
      (mass := fun E : Set (SchedulerPrefix n K) =>
        (schedulerPrefixPMF n hn K).toOuterMeasure E)
      (A := fun σ => σ) a
      (fun X Y hXY =>
        MeasureTheory.measure_mono
          (μ := (schedulerPrefixPMF n hn K).toOuterMeasure) hXY)
      (fun B => schedulerPrefix_outerMeasure_iUnion_fintype_le
        (n := n) hn K B)
      (fun T hT => schedulerPrefix_cylinder_selectedOn_le
        (n := n) hn a T hT)

end Probability
end SSEM
