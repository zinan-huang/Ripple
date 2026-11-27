import Ripple.Probability.CountingBridge.Counts
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Independence.InfinitePi

/-! # Uniform words in an infinite iid sequence

`μ α` is the law of an infinite sequence of independent letters, each uniform on the
finite nonempty alphabet `α`. Restriction to the first `T` coordinates has the finite
product law, so each word of length `T` has mass `1 / card α ^ T`. Consequently the
integral of any function of the first `T` letters is its word sum divided by
`card α ^ T`.
-/

namespace Ripple.CountingBridge

open MeasureTheory Words
open scoped ENNReal BigOperators

noncomputable section

variable {α : Type*}

/-- The uniform law on a finite nonempty alphabet. -/
private abbrev letterLaw (α : Type*) [Fintype α] [Nonempty α] [MeasurableSpace α] :
    Measure α :=
  (PMF.uniformOfFintype α).toMeasure

/-- The law of an infinite sequence of independent uniform letters. -/
def μ (α : Type*) [Fintype α] [Nonempty α] [MeasurableSpace α] : Measure (ℕ → α) :=
  Measure.infinitePi fun _ : ℕ => letterLaw α

instance (α : Type*) [Fintype α] [Nonempty α] [MeasurableSpace α] :
    IsProbabilityMeasure (μ α) := by
  unfold μ
  infer_instance

/-- The first `T` letters, starting with the letter at time zero. -/
def «prefix» (T : ℕ) (ω : ℕ → α) : Word α :=
  List.ofFn fun i : Fin T => ω i

/-- Words form a discrete measurable space. -/
scoped instance wordMeasurableSpace (α : Type*) : MeasurableSpace (List α) := ⊤

scoped instance (α : Type*) : DiscreteMeasurableSpace (List α) :=
  inferInstanceAs (@DiscreteMeasurableSpace _ ⊤)

private def coordinates (T : ℕ) (ω : ℕ → α) : Fin T → α :=
  fun i => ω i

private theorem measurable_coordinates [MeasurableSpace α] (T : ℕ) :
    Measurable (coordinates (α := α) T) :=
  measurable_pi_lambda _ fun i => measurable_pi_apply (i : ℕ)

/-- Reading the first `T` letters is measurable. -/
@[fun_prop]
theorem measurable_prefix [MeasurableSpace α] [DiscreteMeasurableSpace α] [Countable α]
    (T : ℕ) : Measurable («prefix» (α := α) T) :=
  (measurable_of_countable (List.ofFn : (Fin T → α) → List α)).comp
    (measurable_coordinates T)

section Uniform

variable [Fintype α] [Nonempty α] [MeasurableSpace α]

private theorem map_coordinates (T : ℕ) :
    (μ α).map (coordinates T) = Measure.pi (fun _ : Fin T => letterLaw α) := by
  rw [show coordinates (α := α) T = fun ω (i : Fin T) => ω i from rfl]
  simpa only [μ, Measure.infinitePi_eq_pi] using
    (Measure.map_infinitePi_infinitePi_of_inj (P := fun _ : ℕ => letterLaw α)
      (f := fun i : Fin T => i.val) Fin.val_injective)

variable [DiscreteMeasurableSpace α]

private theorem tuple_mass {T : ℕ} (v : Fin T → α) :
    Measure.pi (fun _ : Fin T => letterLaw α) {v} = ((Fintype.card α : ℝ≥0∞) ^ T)⁻¹ := by
  rw [Measure.pi_singleton]
  simp only [letterLaw, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.uniformOfFintype_apply, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ENNReal.inv_pow]

private theorem word_mass {T : ℕ} (w : Word α) (hw : w.length = T) :
    μ α («prefix» T ⁻¹' {w}) = ((Fintype.card α : ℝ≥0∞) ^ T)⁻¹ := by
  subst T
  have hset : «prefix» w.length ⁻¹' {w} = coordinates w.length ⁻¹' {w.get} := by
    ext ω
    change List.ofFn (coordinates w.length ω) = w ↔ coordinates w.length ω = w.get
    exact (by rw [List.ofFn_get] : List.ofFn (coordinates w.length ω) = w ↔
      List.ofFn (coordinates w.length ω) = List.ofFn w.get).trans List.ofFn_inj
  rw [hset, ← Measure.map_apply (measurable_coordinates _) (measurableSet_singleton _),
    map_coordinates, tuple_mass]

/-- A cylinder containing exactly the words in `A`, all of length `T`, has mass
`A.card / card α ^ T`. -/
theorem cylinder_measure (T : ℕ) (A : Finset (Word α))
    (hA : ∀ w ∈ A, w.length = T) :
    μ α {ω | «prefix» T ω ∈ A} =
      (A.card : ℝ≥0∞) / (Fintype.card α : ℝ≥0∞) ^ T := by
  classical
  have hset : {ω | «prefix» T ω ∈ A} = ⋃ w ∈ A, «prefix» T ⁻¹' {w} := by
    ext ω
    simp
  rw [hset, measure_biUnion_finset
    (Set.pairwiseDisjoint_fiber («prefix» (α := α) T) (A : Set (Word α)))
    (fun w _ => (measurable_prefix T) (measurableSet_singleton w))]
  calc
    _ = ∑ _w ∈ A, ((Fintype.card α : ℝ≥0∞) ^ T)⁻¹ :=
      Finset.sum_congr rfl fun w hw => word_mass w (hA w hw)
    _ = _ := by simp [nsmul_eq_mul, div_eq_mul_inv]

/-- Integrating a function of the first `T` letters gives its word sum divided by
`card α ^ T`. -/
theorem lintegral_word_function (T : ℕ) (f : Word α → ℕ) :
    (∫⁻ ω, (f («prefix» T ω) : ℝ≥0∞) ∂μ α) =
      (wordSum α T f : ℝ≥0∞) / (Fintype.card α : ℝ≥0∞) ^ T := by
  let F : (Fin T → α) → ℝ≥0∞ := fun v => f (List.ofFn v)
  change (∫⁻ ω, F (coordinates T ω) ∂μ α) = _
  rw [← lintegral_map (measurable_of_countable F) (measurable_coordinates T),
    map_coordinates, lintegral_fintype]
  simp only [tuple_mass, ← Finset.sum_mul, wordSum_eq_sum_tuples, Nat.cast_sum,
    div_eq_mul_inv, F]

end Uniform

end

end Ripple.CountingBridge
