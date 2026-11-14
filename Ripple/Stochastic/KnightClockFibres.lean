import Ripple.Stochastic.KnightTimeChangePaths
import Mathlib.MeasureTheory.Measure.MeasureSpace

/-!
# Dense-time lifting of constancy on clock fibres

A continuous path and a monotone clock allow
countably many dense-time fibre equalities to determine all fibre equalities.
The almost-sure wrapper intersects countably many full-measure events before
applying this deterministic argument. It does not prove the dense-time
equalities for a stochastic integral.
-/

open Set Filter MeasureTheory
open scoped NNReal Topology

namespace Ripple.ProbabilityTheory

/-- For ordered distinct endpoints of a flat clock interval, dense-time fibre
equalities and path continuity force equality at both endpoints. No continuity
of the clock or positivity of the left endpoint is needed. -/
theorem eq_of_dense_clock_fibres_of_lt
    {A : ℝ≥0 → ℝ≥0} {M : ℝ≥0 → ℝ}
    (d : ℕ → ℝ≥0) (hd : DenseRange d)
    (hM : Continuous M) (hA : Monotone A)
    (hGrid : ∀ i j, A (d i) = A (d j) → M (d i) = M (d j))
    {s t : ℝ≥0} (hst : s < t) (hclock : A s = A t) : M s = M t := by
  have hflat : ∀ u ∈ Ioo s t, A u = A s := by
    intro u hu
    apply le_antisymm
    · calc
        A u ≤ A t := hA hu.2.le
        _ = A s := hclock.symm
    · exact hA hu.1.le
  obtain ⟨u, hsu, hut⟩ := exists_between hst
  obtain ⟨v, hv, ⟨i, hi⟩⟩ :=
    hd.inter_open_nonempty (Ioo s t) isOpen_Ioo ⟨u, hsu, hut⟩
  have hiInterval : d i ∈ Ioo s t := hi.symm ▸ hv
  let C : Set ℝ≥0 := {u | M u = M (d i)}
  have hC : IsClosed C := isClosed_eq hM continuous_const
  have hGridSubset : range d ∩ Ioo s t ⊆ C := by
    rintro v ⟨⟨j, rfl⟩, hj⟩
    exact hGrid j i ((hflat _ hj).trans (hflat _ hiInterval).symm)
  have hDenseInterior : Ioo s t ⊆ closure (range d ∩ Ioo s t) := by
    intro v hv
    refine mem_closure_iff.2 fun U hU hvU => ?_
    obtain ⟨w, hwU, hwRange⟩ := hd.inter_open_nonempty
      (U ∩ Ioo s t) (hU.inter isOpen_Ioo) ⟨v, hvU, hv⟩
    exact ⟨w, hwU.1, hwRange, hwU.2⟩
  have hInterior : Ioo s t ⊆ C :=
    hDenseInterior.trans (closure_minimal hGridSubset hC)
  have hEndpoints : Icc s t ⊆ C := by
    rw [← closure_Ioo hst.ne]
    exact closure_minimal hInterior hC
  have hs : M s = M (d i) := hEndpoints ⟨le_rfl, hst.le⟩
  have ht : M t = M (d i) := hEndpoints ⟨hst.le, le_rfl⟩
  exact hs.trans ht.symm

/-- Constancy on the fibres at a dense sequence upgrades to the installed
all-times predicate. Equal times and intervals starting at zero are included. -/
theorem constantOnClockFibres_of_dense
    {A : ℝ≥0 → ℝ≥0} {M : ℝ≥0 → ℝ}
    (d : ℕ → ℝ≥0) (hd : DenseRange d)
    (hM : Continuous M) (hA : Monotone A)
    (hGrid : ∀ i j, A (d i) = A (d j) → M (d i) = M (d j)) :
    ConstantOnClockFibres A M := by
  intro s t hclock
  rcases lt_trichotomy s t with hst | hst | hts
  · exact eq_of_dense_clock_fibres_of_lt d hd hM hA hGrid hst hclock
  · exact congrArg M hst
  · exact (eq_of_dense_clock_fibres_of_lt d hd hM hA hGrid hts hclock.symm).symm

/-- Countably many pairwise almost-sure fibre equalities produce one event on
which the path is constant on every clock fibre. The pairwise stochastic
equalities remain a separate producer obligation. No probability normalization
or measurability premise on the processes is required for this lifting step. -/
theorem ae_constantOnClockFibres_of_dense
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {A : ℝ≥0 → Ω → ℝ≥0} {M : ℝ≥0 → Ω → ℝ}
    (d : ℕ → ℝ≥0) (hd : DenseRange d)
    (hM : ∀ᵐ ω ∂μ, Continuous (fun t => M t ω))
    (hA : ∀ᵐ ω ∂μ, Monotone (fun t => A t ω))
    (hGrid : ∀ i j, ∀ᵐ ω ∂μ,
      A (d i) ω = A (d j) ω → M (d i) ω = M (d j) ω) :
    ∀ᵐ ω ∂μ, ConstantOnClockFibres (fun t => A t ω) (fun t => M t ω) := by
  have hAll : ∀ᵐ ω ∂μ, ∀ i j,
      A (d i) ω = A (d j) ω → M (d i) ω = M (d j) ω :=
    ae_all_iff.mpr fun i => ae_all_iff.mpr (hGrid i)
  filter_upwards [hM, hA, hAll] with ω hMω hAω hGridω
  exact constantOnClockFibres_of_dense d hd hMω hAω hGridω

end Ripple.ProbabilityTheory
