-- Ripple/Kurtz/StrongApprox/CellFamilySimplePoints.lean
import Ripple.Kurtz.StrongApprox.PoissonCellDriverLaw
import Mathlib.Probability.Independence.InfinitePi

/-!
# Probability-one simplicity of every universal Poisson cell

A cell contains a Poisson(1) number of iid uniform positions. It is enough
(and slightly stronger) to require every pair of coordinates in the infinite
position sequence to be distinct after `clip`; the random cell count may then
select any finite prefix.
-/

noncomputable section

namespace Ripple.Kurtz.StrongApprox.CellFamilySimplePoints

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators
open Ripple.Kurtz.StrongApprox

variable {ι : Type*}

/-- Every two labelled positions in one cell are distinct. -/
def SimplePositionSequence (u : ℕ → ℝ) : Prop :=
  ∀ p q : ℕ, p ≠ q → clip (u p) ≠ clip (u q)

/-- Every unit cell in one channel is simple. -/
def SimpleCellArray (a : ℕ → CellSpace) : Prop :=
  ∀ j : ℕ, SimplePositionSequence (a j).2

/-- Every cell of every channel is simple. -/
def SimpleCellFamily (c : CellFamily ι) : Prop :=
  ∀ l : ι, SimpleCellArray (c l)

private theorem unifReal_clip_eq_self_ae :
    ∀ᵐ x ∂unifReal, clip x = x := by
  have hmem : ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 1),
      x ∈ Ioc (0 : ℝ) 1 :=
    ae_restrict_mem measurableSet_Ioc
  simpa only [unifReal] using
    hmem.mono (fun x hx => clip_of_mem hx)

private theorem unifReal_prod_ne_ae :
    ∀ᵐ z : ℝ × ℝ ∂unifReal.prod unifReal, z.1 ≠ z.2 := by
  have hms : MeasurableSet {z : ℝ × ℝ | z.1 = z.2} :=
    measurableSet_eq_fun measurable_fst measurable_snd
  have hsing : ∀ x : ℝ, unifReal {x} = 0 := by
    intro x
    apply le_antisymm _ bot_le
    calc
      unifReal {x} ≤ volume {x} := by
        unfold unifReal
        exact Measure.le_iff'.1 Measure.restrict_le_self {x}
      _ = 0 := by simp
  rw [ae_iff]
  have hdiag :
      (unifReal.prod unifReal) {z : ℝ × ℝ | z.1 = z.2} = 0 := by
    rw [Measure.measure_prod_null hms]
    filter_upwards with x
    have hpre : Prod.mk x ⁻¹' {z : ℝ × ℝ | z.1 = z.2} = {x} := by
      ext y
      simp [eq_comm]
    simp only [hpre, Pi.zero_apply]
    exact hsing x
  simpa only [ne_eq, not_not] using hdiag

private theorem posSeq_coord_raw_ne_ae
    {p q : ℕ} (hpq : p ≠ q) :
    ∀ᵐ u ∂posSeq, u p ≠ u q := by
  let pair : (ℕ → ℝ) → ℝ × ℝ := fun u => (u p, u q)
  have hpair : Measurable pair :=
    (measurable_pi_apply p).prodMk (measurable_pi_apply q)
  have hind : IndepFun (fun u : ℕ → ℝ => u p) (fun u : ℕ → ℝ => u q) posSeq :=
    (iIndepFun_infinitePi (P := fun _ : ℕ => unifReal)
      (X := fun _ (x : ℝ) => x) (fun _ => measurable_id)).indepFun hpq
  have hmap : posSeq.map pair = unifReal.prod unifReal := by
    have h1 := (indepFun_iff_map_prod_eq_prod_map_map
      (measurable_pi_apply p).aemeasurable
      (measurable_pi_apply q).aemeasurable).1 hind
    have hp : posSeq.map (fun u : ℕ → ℝ => u p) = unifReal := by
      simpa only [posSeq] using
        (Measure.infinitePi_map_eval (fun _ : ℕ => unifReal) p)
    have hq : posSeq.map (fun u : ℕ → ℝ => u q) = unifReal := by
      simpa only [posSeq] using
        (Measure.infinitePi_map_eval (fun _ : ℕ => unifReal) q)
    rw [hp, hq] at h1
    exact h1
  exact MeasureTheory.ae_of_ae_map
    (p := fun z : ℝ × ℝ => z.1 ≠ z.2) hpair.aemeasurable
    (by rw [hmap]; exact unifReal_prod_ne_ae)

private theorem posSeq_coord_clip_eq_self_ae (p : ℕ) :
    ∀ᵐ u ∂posSeq, clip (u p) = u p := by
  have hmap : posSeq.map (fun u : ℕ → ℝ => u p) = unifReal := by
    simpa only [posSeq] using
      (Measure.infinitePi_map_eval
        (fun _ : ℕ => unifReal) p)
  exact MeasureTheory.ae_of_ae_map
    (p := fun y : ℝ => clip y = y)
    (measurable_pi_apply p).aemeasurable
    (by rw [hmap]; exact unifReal_clip_eq_self_ae)

private theorem posSeq_coord_ne_ae
    {p q : ℕ} (hpq : p ≠ q) :
    ∀ᵐ u ∂posSeq, clip (u p) ≠ clip (u q) := by
  filter_upwards [posSeq_coord_raw_ne_ae hpq,
    posSeq_coord_clip_eq_self_ae p,
    posSeq_coord_clip_eq_self_ae q]
    with u hne hp hq
  simpa only [hp, hq] using hne

/-- Every labelled uniform position sequence is simple almost surely. -/
theorem simplePositionSequence_ae :
    ∀ᵐ u ∂posSeq, SimplePositionSequence u := by
  unfold SimplePositionSequence
  rw [ae_all_iff]
  intro p
  rw [ae_all_iff]
  intro q
  by_cases hpq : p = q
  · subst q
    exact ae_of_all _ (fun _ h => False.elim (h rfl))
  · exact (posSeq_coord_ne_ae hpq).mono
      (fun _ h _ => h)

/-- The random Poisson count does not affect simplicity of the position
sequence selected by the count. -/
theorem simpleCell_ae :
    ∀ᵐ z ∂cellLaw, SimplePositionSequence z.2 := by
  refine MeasureTheory.ae_of_ae_map
    (p := fun u : ℕ → ℝ => SimplePositionSequence u)
    measurable_snd.aemeasurable ?_
  simpa only [cellLaw, Measure.map_snd_prod,
    measure_univ, one_smul] using simplePositionSequence_ae

/-- Every unit cell in one complete channel is simple almost surely. -/
theorem simpleCellArray_ae :
    ∀ᵐ a ∂cellArrayLaw, SimpleCellArray a := by
  unfold SimpleCellArray
  rw [ae_all_iff]
  intro j
  have hmap : cellArrayLaw.map (fun a => a j) = cellLaw := by
    simpa only [cellArrayLaw] using
      (Measure.infinitePi_map_eval
        (fun _ : ℕ => cellLaw) j)
  exact MeasureTheory.ae_of_ae_map
    (p := fun z : CellSpace => SimplePositionSequence z.2)
    (measurable_pi_apply j).aemeasurable
    (by rw [hmap]; exact simpleCell_ae)

/-- The full universal family is simple in every channel and every cell with
probability one. Countability of the cell index and finiteness/countability
of the channel index are handled by the product-law `ae_all_iff` steps. -/
theorem simpleCellFamily_ae
    [Countable ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] :
    ∀ᵐ c ∂cellFamilyLaw ι, SimpleCellFamily c := by
  unfold SimpleCellFamily
  rw [ae_all_iff]
  intro l
  have hmap : (cellFamilyLaw ι).map (fun c => c l) = cellArrayLaw := by
    simpa only [cellFamilyLaw] using
      (Measure.infinitePi_map_eval
        (fun _ : ι => cellArrayLaw) l)
  exact MeasureTheory.ae_of_ae_map
    (p := fun a : ℕ → CellSpace => SimpleCellArray a)
    (measurable_pi_apply l).aemeasurable
    (by rw [hmap]; exact simpleCellArray_ae)

/-!
THEOREM LIST
* `SimplePositionSequence`
* `SimpleCellArray`
* `SimpleCellFamily`
* `simplePositionSequence_ae`
* `simpleCell_ae`
* `simpleCellArray_ae`
* `simpleCellFamily_ae`

CLOSES
* Route item (1): same-cell simplicity under the actual
  Poisson-count/uniform-position `cellFamilyLaw`.
* Simultaneous simplicity for every cell and channel.

UNFINISHED
* Nothing in this file.
END
-/

end Ripple.Kurtz.StrongApprox.CellFamilySimplePoints

end
