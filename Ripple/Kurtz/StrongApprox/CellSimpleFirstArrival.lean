-- Ripple/Kurtz/StrongApprox/CellSimpleFirstArrival.lean
import Ripple.Kurtz.StrongApprox.CellRecursiveClockEquationProducer
import Ripple.Kurtz.StrongApprox.PoissonStoppingLine
import Ripple.Kurtz.StrongApprox.PoissonPathArrivals

/-!
# A simple cell path has a unit first increment

The finite labelled-arrival representation is used to show that the first
strictly positive increment after an internal line has cardinality one.  The
key deterministic input is injectivity of labelled absolute arrival times;
within one cell this is `SimpleCellArray`, and different cells occupy the
half-open strips `(j,j+1]`.
-/

noncomputable section

namespace Ripple.Kurtz.StrongApprox.CellSimpleFirstArrival

open MeasureTheory ProbabilityTheory Set Finset Filter
open scoped ENNReal NNReal BigOperators
open Ripple.Kurtz.StrongApprox
open CellFamilySimplePoints
open CellRandomTimeEvaluation
open CellExtendedStoppingLine
open CellExtendedRandomTime
open CellExtendedRaceRecursion
open CellZeroAwareExtendedRace

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

private theorem rawArrivalTime_injective_of_simple
    (a : ℕ → CellSpace) (ha : SimpleCellArray a) (U : ℝ) :
    Function.Injective
      (rawArrivalTime canonicalCount U (cellSample a)) := by
  intro x y hxy
  rcases x with ⟨i, p⟩
  rcases y with ⟨j, q⟩
  have htime :
      (i.1 : ℝ) + clip ((a i.1).2 p.1) =
        (j.1 : ℝ) + clip ((a j.1).2 q.1) := by
    simpa [rawArrivalTime, cellSample, canonicalCount] using hxy
  have hij : i.1 = j.1 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hnat : i.1 + 1 ≤ j.1 := Nat.succ_le_iff.mpr hlt
      have hcast : (i.1 : ℝ) + 1 ≤ (j.1 : ℝ) := by
        exact_mod_cast hnat
      have hiUpper :
          (i.1 : ℝ) + clip ((a i.1).2 p.1) ≤ (i.1 : ℝ) + 1 := by
        linarith [clip_le_one ((a i.1).2 p.1)]
      have hjLower :
          (j.1 : ℝ) < (j.1 : ℝ) + clip ((a j.1).2 q.1) := by
        linarith [clip_pos ((a j.1).2 q.1)]
      linarith
    · have hnat : j.1 + 1 ≤ i.1 := Nat.succ_le_iff.mpr hgt
      have hcast : (j.1 : ℝ) + 1 ≤ (i.1 : ℝ) := by
        exact_mod_cast hnat
      have hjUpper :
          (j.1 : ℝ) + clip ((a j.1).2 q.1) ≤ (j.1 : ℝ) + 1 := by
        linarith [clip_le_one ((a j.1).2 q.1)]
      have hiLower :
          (i.1 : ℝ) < (i.1 : ℝ) + clip ((a i.1).2 p.1) := by
        linarith [clip_pos ((a i.1).2 p.1)]
      linarith
  have hijFin : i = j := Fin.ext hij
  subst j
  have hpq : p.1 = q.1 := by
    by_contra hne
    apply ha i.1 p.1 q.1 hne
    linarith
  have hpqFin : p = q := Fin.ext hpq
  subst q
  rfl

private theorem horizonArrivalTime_injective_of_simple
    (a : ℕ → CellSpace) (ha : SimpleCellArray a) (U : ℝ) :
    Function.Injective
      (horizonArrivalTime canonicalCount U (cellSample a)) := by
  intro x y hxy
  apply Subtype.ext
  exact rawArrivalTime_injective_of_simple a ha U hxy

/-- For an injective finite labelled arrival family, if the count is constant
on `[s,t)` and strictly increases at `t`, the increase is exactly one. -/
private theorem finiteArrivalCount_sub_eq_one_of_first
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (arrival : κ → ℝ) (hinjective : Function.Injective arrival)
    {s t : ℝ} (hst : s < t)
    (hfirst : ∀ u, s ≤ u → u < t →
      finiteArrivalCount arrival u = finiteArrivalCount arrival s)
    (hpositive :
      0 < finiteArrivalCount arrival t - finiteArrivalCount arrival s) :
    finiteArrivalCount arrival t - finiteArrivalCount arrival s = 1 := by
  classical
  let before : Finset κ := Finset.univ.filter fun q => arrival q ≤ s
  let after : Finset κ := Finset.univ.filter fun q => arrival q ≤ t
  have hsubset : before ⊆ after := by
    intro q hq
    simp only [before, after, Finset.mem_filter, Finset.mem_univ,
      true_and] at hq ⊢
    exact hq.trans hst.le
  have hdiff :
      finiteArrivalCount arrival t - finiteArrivalCount arrival s =
        (after \ before).card := by
    unfold finiteArrivalCount
    change after.card - before.card = (after \ before).card
    exact (Finset.card_sdiff_of_subset hsubset).symm
  have harrival : ∀ q ∈ after \ before, arrival q = t := by
    intro q hq
    have hmem := Finset.mem_sdiff.mp hq
    have hqt : arrival q ≤ t := by
      exact (Finset.mem_filter.mp hmem.1).2
    have hqs : s < arrival q := by
      apply lt_of_not_ge
      intro hle
      apply hmem.2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ q, hle⟩
    apply le_antisymm hqt
    by_contra hnot
    have hqtStrict : arrival q < t := lt_of_not_ge hnot
    let middle : Finset κ :=
      Finset.univ.filter fun r => arrival r ≤ arrival q
    have hbeforeMiddle : before ⊆ middle := by
      intro r hr
      simp only [before, middle, Finset.mem_filter, Finset.mem_univ,
        true_and] at hr ⊢
      exact hr.trans hqs.le
    have hqMiddle : q ∈ middle := by
      simp [middle]
    have hcardStrict : before.card < middle.card := by
      apply Finset.card_lt_card
      rw [Finset.ssubset_iff_of_subset hbeforeMiddle]
      exact ⟨q, hqMiddle, hmem.2⟩
    have heq := hfirst (arrival q) hqs.le hqtStrict
    have heqCard : middle.card = before.card := by
      simpa [finiteArrivalCount, middle, before] using heq
    omega
  have hcardLe : (after \ before).card ≤ 1 := by
    rw [Finset.card_le_one_iff]
    intro p q hp hq
    apply hinjective
    rw [harrival p hp, harrival q hq]
  have hcardPos : 0 < (after \ before).card := by
    rw [← hdiff]
    exact hpositive
  rw [hdiff]
  omega

/-- At a finite residual wait, a simple channel consumes exactly one labelled
point.  No cross-channel assumption is used here. -/
theorem shiftedCount_at_finite_residual_eq_one
    {σ : CellFamily ι → ι → ℝ≥0}
    {c : CellFamily ι} {l : ι}
    (hsimple : SimpleCellArray (c l))
    {delta : ℝ≥0∞} (hdelta : delta ≠ ∞)
    (hresidual : residualWaitE σ c l = delta) :
    shiftedCount σ c l delta.toNNReal = 1 := by
  have hcoe : (delta.toNNReal : ℝ≥0∞) = delta :=
    ENNReal.coe_toNNReal hdelta
  have hpositive : 0 < shiftedCount σ c l delta.toNNReal := by
    apply (residualWaitE_le_coe_iff_shiftedCount_pos
      σ c l delta.toNNReal).1
    rw [hresidual, hcoe]
  have hdelayPos : 0 < delta.toNNReal := by
    by_contra hnot
    have hzero : delta.toNNReal = 0 :=
      le_antisymm (not_lt.mp hnot) zero_le
    simpa [hzero, shiftedCount] using hpositive
  let s : ℝ := (σ c l : ℝ)
  let t : ℝ := ((σ c l + delta.toNNReal : ℝ≥0) : ℝ)
  let arrival :=
    horizonArrivalTime canonicalCount t (cellSample (c l))
  have hst : s < t := by
    change (σ c l : ℝ) <
      ((σ c l + delta.toNNReal : ℝ≥0) : ℝ)
    exact_mod_cast (lt_add_of_pos_right (σ c l) hdelayPos)
  have hpath (u : ℝ) (hu : u ≤ t) :
      cellPath u (c l) = finiteArrivalCount arrival u := by
    dsimp [arrival]
    rw [cellPath_eq_poisPath]
    exact poisPath_eq_horizonArrivalCount
      canonicalCount hu (cellSample (c l))
  have hfirst : ∀ u, s ≤ u → u < t →
      finiteArrivalCount arrival u = finiteArrivalCount arrival s := by
    intro u hsu hut
    rw [← hpath u hut.le, ← hpath s hst.le]
    let q : ℝ≥0 := Real.toNNReal (u - s)
    have hqcoe : (q : ℝ) = u - s :=
      Real.coe_toNNReal _ (sub_nonneg.mpr hsu)
    have hqLt : q < delta.toNNReal := by
      have hreal : (q : ℝ) < (delta.toNNReal : ℝ) := by
        rw [hqcoe, ENNReal.coe_toNNReal_eq_toReal]
        dsimp [t, s] at hut
        push_cast at hut
        linarith
      exact_mod_cast hreal
    have hnot : ¬ 0 < shiftedCount σ c l q := by
      intro hqPositive
      have hle :=
        (residualWaitE_le_coe_iff_shiftedCount_pos σ c l q).2
          hqPositive
      rw [hresidual, ← hcoe] at hle
      exact (not_le_of_gt (ENNReal.coe_lt_coe.mpr hqLt)) hle
    have hzero : shiftedCount σ c l q = 0 :=
      Nat.eq_zero_of_not_pos hnot
    have hend : (σ c l : ℝ) + (q : ℝ) = u := by
      rw [hqcoe]
      dsimp [s] at hsu ⊢
      linarith
    have hsub : cellPath u (c l) - cellPath s (c l) = 0 := by
      simpa [shiftedCount, s, hend] using hzero
    have hmono := CellRandomTimeEvaluation.cellPath_mono (c l) hsu
    omega
  have hcountPositive :
      0 < finiteArrivalCount arrival t - finiteArrivalCount arrival s := by
    rw [← hpath t le_rfl, ← hpath s hst.le]
    simpa [shiftedCount, s, t, NNReal.coe_add] using hpositive
  have hinjective : Function.Injective arrival :=
    horizonArrivalTime_injective_of_simple (c l) hsimple t
  have hone := finiteArrivalCount_sub_eq_one_of_first
    arrival hinjective hst hfirst hcountPositive
  rw [← hpath t le_rfl, ← hpath s hst.le] at hone
  simpa [shiftedCount, s, t, NNReal.coe_add] using hone

/-- If channel `l` is the strict minimizer of the active race, simplicity of
that channel upgrades positivity of its line increment to exact value one. -/
theorem activeLineIncrement_eq_one_of_simple
    {σ : ExtendedCellLine ι} {rate : ι → ℝ≥0}
    {c : CellFamily ι} {l : ι}
    (hsimple : SimpleCellArray (c l))
    (hline : σ c l ≠ ∞)
    (hresidual : extendedResidualWaitE σ c l ≠ ∞)
    (hwait : activeRaceWaitE σ rate c ≠ ∞)
    (hl : 0 < rate l)
    (hwinner :
      activeRaceWaitE σ rate c = activeRaceTermE σ rate c l) :
    lineIncrement σ (activeNextInternal σ rate) l c = 1 := by
  let delta : ℝ≥0∞ :=
    (rate l : ℝ≥0∞) * activeRaceWaitE σ rate c
  have hdelta : delta ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top hwait
  have hresidualEq : extendedResidualWaitE σ c l = delta := by
    calc
      extendedResidualWaitE σ c l =
          extendedResidualWaitE σ c l /
              (rate l : ℝ≥0∞) * (rate l : ℝ≥0∞) :=
        (ENNReal.div_mul_cancel
          (by exact_mod_cast hl.ne') ENNReal.coe_ne_top).symm
      _ = activeRaceTermE σ rate c l * (rate l : ℝ≥0∞) := by
        simp [activeRaceTermE, hl]
      _ = activeRaceWaitE σ rate c * (rate l : ℝ≥0∞) := by
        rw [← hwinner]
      _ = delta := by
        simp [delta, mul_comm]
  have hfinitePart :
      finitePart (activeNextInternal σ rate) c l =
        finitePart σ c l + delta.toNNReal := by
    change (σ c l + delta).toNNReal =
      (σ c l).toNNReal + delta.toNNReal
    exact ENNReal.toNNReal_add hline hdelta
  have hincrement :
      lineIncrement σ (activeNextInternal σ rate) l c =
        shiftedCount (finitePart σ) c l delta.toNNReal := by
    unfold lineIncrement extendedPathAt shiftedCount
    rw [hfinitePart]
    rfl
  rw [hincrement]
  exact shiftedCount_at_finite_residual_eq_one
    (σ := finitePart σ) hsimple hdelta
      (by simpa [extendedResidualWaitE] using hresidualEq)

/-!
THEOREM LIST
* `shiftedCount_at_finite_residual_eq_one`
* `activeLineIncrement_eq_one_of_simple`

CLOSES
* The same-channel unit-increment lemma at the first finite residual.
* The winning-coordinate exact increment for a strict active race.
* Use of the finite labelled-arrival representation and cell simplicity.

UNFINISHED
* Cross-channel strictness is intentionally not inferred from
  `SimpleCellFamily`; it is a separate probability-one event.
END
-/

end Ripple.Kurtz.StrongApprox.CellSimpleFirstArrival

end
