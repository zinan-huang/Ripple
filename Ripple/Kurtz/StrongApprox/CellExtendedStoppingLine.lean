-- Ripple/Kurtz/StrongApprox/CellExtendedStoppingLine.lean
import Ripple.Kurtz.StrongApprox.CellStoppingLineAdapters
import Mathlib.MeasureTheory.Integral.Indicator

noncomputable section

namespace Ripple.Kurtz.StrongApprox.CellExtendedStoppingLine

open MeasureTheory ProbabilityTheory Set Filter Topology Preorder
open scoped ENNReal NNReal BigOperators Classical
open ExponentialRace
open CellRandomTimeEvaluation CellStoppingLineFreshness
open CellStoppingLineResiduals CellStoppingLineAdapters

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev CellΩ (ι : Type*) := CellFamily ι
abbrev ExtendedCellLine (ι : Type*) := CellΩ ι → ι → ℝ≥0∞

def extendedLineBelow
    (σ : ExtendedCellLine ι) (u : ι → ℝ≥0) : Set (CellΩ ι) :=
  {c | ∀ l, σ c l ≤ (u l : ℝ≥0∞)}

/-- A rectangular stopping line which is allowed to be infinite. -/
structure ExtendedCellStoppingLine
    (σ : ExtendedCellLine ι) : Prop where
  measurable : Measurable σ
  stopping : ∀ u, MeasurableSet[cellPast u] (extendedLineBelow σ u)

/-- The standard stopped past for an extended line. -/
noncomputable def extendedStoppedPast
    (σ : ExtendedCellLine ι) (hσ : ExtendedCellStoppingLine σ) :
    MeasurableSpace (CellΩ ι) where
  MeasurableSet' A :=
    MeasurableSet A ∧
      ∀ u, MeasurableSet[cellPast u] (A ∩ extendedLineBelow σ u)
  measurableSet_empty := by
    refine ⟨MeasurableSet.empty, ?_⟩
    intro u
    simp
  measurableSet_compl := by
    intro A hA
    refine ⟨hA.1.compl, ?_⟩
    intro u
    have hdiff := (hσ.stopping u).diff (hA.2 u)
    have heq :
        Aᶜ ∩ extendedLineBelow σ u =
          extendedLineBelow σ u \ (A ∩ extendedLineBelow σ u) := by
      ext c
      simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_diff]
      tauto
    rw [heq]
    exact hdiff
  measurableSet_iUnion := by
    intro A hA
    refine ⟨MeasurableSet.iUnion fun n => (hA n).1, ?_⟩
    intro u
    have heq :
        (⋃ n, A n) ∩ extendedLineBelow σ u =
          ⋃ n, (A n ∩ extendedLineBelow σ u) := by
      ext c
      simp
    rw [heq]
    exact MeasurableSet.iUnion fun n => (hA n).2 u

theorem extendedStoppedPast_ambient
    {σ : ExtendedCellLine ι} {hσ : ExtendedCellStoppingLine σ}
    {A : Set (CellΩ ι)}
    (hA : MeasurableSet[extendedStoppedPast σ hσ] A) :
    MeasurableSet A := hA.1

theorem extendedStoppedPast_inter_below
    {σ : ExtendedCellLine ι} {hσ : ExtendedCellStoppingLine σ}
    {A : Set (CellΩ ι)}
    (hA : MeasurableSet[extendedStoppedPast σ hσ] A)
    (u : ι → ℝ≥0) :
    MeasurableSet[cellPast u] (A ∩ extendedLineBelow σ u) :=
  hA.2 u

theorem measurable_extendedStoppedPast_ambient
    {E : Type*} [MeasurableSpace E]
    {σ : ExtendedCellLine ι} {hσ : ExtendedCellStoppingLine σ}
    {H : CellΩ ι → E}
    (hH : Measurable[extendedStoppedPast σ hσ] H) :
    Measurable H := by
  intro A hA
  exact extendedStoppedPast_ambient (hH hA)

noncomputable def capCoordinate
    (u : ι → ℝ≥0) (l : ι) (a : ℝ≥0) : ι → ℝ≥0 :=
  Function.update u l (min (u l) a)

theorem capCoordinate_le
    (u : ι → ℝ≥0) (l : ι) (a : ℝ≥0) :
    ∀ j, capCoordinate u l a j ≤ u j := by
  classical
  intro j
  by_cases hj : j = l
  · subst j
    simp [capCoordinate]
  · simp [capCoordinate, Function.update_of_ne hj]

theorem inter_coordinate_le_eq_below
    (σ : ExtendedCellLine ι) (u : ι → ℝ≥0)
    (l : ι) (a : ℝ≥0) :
    {c | σ c l ≤ (a : ℝ≥0∞)} ∩ extendedLineBelow σ u =
      extendedLineBelow σ (capCoordinate u l a) := by
  classical
  ext c
  constructor
  · rintro ⟨hl, hall⟩ j
    by_cases hj : j = l
    · subst j
      simpa [capCoordinate, le_min_iff] using And.intro (hall l) hl
    · simpa [capCoordinate, Function.update_of_ne hj] using hall j
  · intro hall
    have hl := hall l
    have hl' :
        σ c l ≤ (u l : ℝ≥0∞) ∧ σ c l ≤ (a : ℝ≥0∞) := by
      simpa [capCoordinate, le_min_iff] using hl
    refine ⟨hl'.2, ?_⟩
    intro j
    by_cases hj : j = l
    · simpa [hj] using hl'.1
    · simpa [capCoordinate, Function.update_of_ne hj] using hall j

/-- Each coordinate of the line is measurable in its stopped past. -/
theorem measurable_extendedLine_coord_stoppedPast
    {σ : ExtendedCellLine ι} (hσ : ExtendedCellStoppingLine σ) (l : ι) :
    Measurable[extendedStoppedPast σ hσ] (fun c => σ c l) := by
  refine measurable_of_Iic (mδ := extendedStoppedPast σ hσ) ?_
  intro b
  by_cases hb : b = ∞
  · subst b
    simp
  · lift b to ℝ≥0 using hb with a
    refine ⟨((measurable_pi_apply l).comp hσ.measurable) measurableSet_Iic, ?_⟩
    intro u
    have : (fun c => σ c l) ⁻¹' Set.Iic (a : ℝ≥0∞) ∩ extendedLineBelow σ u =
        extendedLineBelow σ (capCoordinate u l a) := inter_coordinate_le_eq_below σ u l a
    rw [this]
    exact (cellPast_mono (capCoordinate_le u l a)) _
      (hσ.stopping (capCoordinate u l a))

/-- The line itself is measurable in its stopped past. -/
theorem measurable_extendedLine_stoppedPast
    {σ : ExtendedCellLine ι} (hσ : ExtendedCellStoppingLine σ) :
    Measurable[extendedStoppedPast σ hσ] σ :=
  @measurable_pi_lambda (CellΩ ι) ι (fun _ => ℝ≥0∞) (extendedStoppedPast σ hσ) _ σ
    (fun l => measurable_extendedLine_coord_stoppedPast hσ l)

/-- A smaller line has a smaller stopped past. -/
theorem extendedStoppedPast_mono
    {σ τ : ExtendedCellLine ι}
    (hσ : ExtendedCellStoppingLine σ)
    (hτ : ExtendedCellStoppingLine τ)
    (hle : ∀ c l, σ c l ≤ τ c l) :
    extendedStoppedPast σ hσ ≤ extendedStoppedPast τ hτ := by
  intro A hA
  refine ⟨hA.1, ?_⟩
  intro u
  have heq :
      A ∩ extendedLineBelow τ u =
        (A ∩ extendedLineBelow σ u) ∩ extendedLineBelow τ u := by
    ext c
    constructor
    · rintro ⟨hcA, hcτ⟩
      exact ⟨⟨hcA, fun l => (hle c l).trans (hcτ l)⟩, hcτ⟩
    · rintro ⟨⟨hcA, _⟩, hcτ⟩
      exact ⟨hcA, hcτ⟩
  rw [heq]
  exact (hA.2 u).inter (hτ.stopping u)

/-- The finite representative used by the earlier finite-line interfaces. -/
noncomputable def finitePart
    (σ : ExtendedCellLine ι) (c : CellΩ ι) : ι → ℝ≥0 :=
  fun l => (σ c l).toNNReal

@[fun_prop]
theorem measurable_finitePart
    {σ : ExtendedCellLine ι} (hσ : Measurable σ) :
    Measurable (finitePart σ) := by
  apply measurable_pi_lambda
  intro l
  exact ENNReal.measurable_toNNReal.comp
    ((measurable_pi_apply l).comp hσ)

@[fun_prop]
theorem measurable_finitePart_stopped
    {σ : ExtendedCellLine ι} (hσ : ExtendedCellStoppingLine σ) :
    Measurable[extendedStoppedPast σ hσ] (finitePart σ) :=
  @measurable_pi_lambda (CellΩ ι) ι (fun _ => ℝ≥0) (extendedStoppedPast σ hσ) _ (finitePart σ)
    (fun l => @Measurable.comp (CellΩ ι) ℝ≥0∞ ℝ≥0 (extendedStoppedPast σ hσ) _ _ _ _
      ENNReal.measurable_toNNReal (measurable_extendedLine_coord_stoppedPast hσ l))

/-- Localize a stopped-past random variable to one finite rectangle. -/
noncomputable def localizeBelow
    {E : Type*} (σ : ExtendedCellLine ι) (u : ι → ℝ≥0)
    (H : CellΩ ι → E) (e0 : E) (c : CellΩ ι) : E :=
  if c ∈ extendedLineBelow σ u then H c else e0

@[fun_prop]
theorem measurable_localizeBelow
    {E : Type*} [MeasurableSpace E]
    {σ : ExtendedCellLine ι} (hσ : ExtendedCellStoppingLine σ)
    {H : CellΩ ι → E}
    (hH : Measurable[extendedStoppedPast σ hσ] H)
    (u : ι → ℝ≥0) (e0 : E) :
    Measurable[cellPast u] (localizeBelow σ u H e0) := by
  intro B hB
  by_cases he : e0 ∈ B
  · have heq :
        localizeBelow σ u H e0 ⁻¹' B =
          (H ⁻¹' B ∩ extendedLineBelow σ u) ∪
            (extendedLineBelow σ u)ᶜ := by
      ext c
      by_cases hc : c ∈ extendedLineBelow σ u <;>
        simp [localizeBelow, hc, he]
    rw [heq]
    exact (hH hB).2 u |>.union (hσ.stopping u).compl
  · have heq :
        localizeBelow σ u H e0 ⁻¹' B =
          H ⁻¹' B ∩ extendedLineBelow σ u := by
      ext c
      by_cases hc : c ∈ extendedLineBelow σ u <;>
        simp [localizeBelow, hc, he]
    rw [heq]
    exact (hH hB).2 u

noncomputable def belowValue
    (σ : ExtendedCellLine ι) (u : ι → ℝ≥0)
    (c : CellΩ ι) (l : ι) : ℝ≥0 :=
  localizeBelow σ u (fun d => finitePart σ d l) 0 c

@[fun_prop]
theorem measurable_belowValue
    {σ : ExtendedCellLine ι} (hσ : ExtendedCellStoppingLine σ)
    (u : ι → ℝ≥0) (l : ι) :
    Measurable[cellPast u] (fun c => belowValue σ u c l) := by
  exact measurable_localizeBelow hσ
    ((measurable_pi_apply l).comp (measurable_finitePart_stopped hσ)) u 0

theorem belowValue_eq_of_mem
    {σ : ExtendedCellLine ι} {u : ι → ℝ≥0}
    {c : CellΩ ι} (hc : c ∈ extendedLineBelow σ u) (l : ι) :
    belowValue σ u c l = finitePart σ c l := by
  simp [belowValue, localizeBelow, hc]

theorem coe_belowValue_eq_of_mem
    {σ : ExtendedCellLine ι} {u : ι → ℝ≥0}
    {c : CellΩ ι} (hc : c ∈ extendedLineBelow σ u) (l : ι) :
    (belowValue σ u c l : ℝ≥0∞) = σ c l := by
  rw [belowValue_eq_of_mem hc]
  exact ENNReal.coe_toNNReal
    (ne_top_of_le_ne_top ENNReal.coe_ne_top (hc l))

theorem belowValue_le
    {σ : ExtendedCellLine ι} (hσ : ExtendedCellStoppingLine σ)
    (u : ι → ℝ≥0) (c : CellΩ ι) (l : ι) :
    belowValue σ u c l ≤ u l := by
  by_cases hc : c ∈ extendedLineBelow σ u
  · rw [belowValue_eq_of_mem hc]
    apply (ENNReal.toNNReal_le_toNNReal
      (ne_top_of_le_ne_top ENNReal.coe_ne_top (hc l)) ENNReal.coe_ne_top).2
    simpa using hc l
  · simp [belowValue, localizeBelow, hc]

def extendedLineFinite
    (σ : ExtendedCellLine ι) : Set (CellΩ ι) :=
  {c | ∀ l, σ c l ≠ ∞}

theorem measurable_extendedLineFinite
    {σ : ExtendedCellLine ι} (hσ : ExtendedCellStoppingLine σ) :
    MeasurableSet (extendedLineFinite σ) := by
  have heq :
      extendedLineFinite σ = ⋂ l, {c | σ c l ≠ ∞} := by
    ext c
    simp [extendedLineFinite]
  rw [heq]
  exact MeasurableSet.iInter fun l =>
    (((measurable_pi_apply l).comp hσ.measurable)
      (measurableSet_singleton (∞ : ℝ≥0∞))).compl

noncomputable def uniformBound (n : ℕ) : ι → ℝ≥0 :=
  fun _ => n

def boundEvent (σ : ExtendedCellLine ι) (n : ℕ) : Set (CellΩ ι) :=
  extendedLineBelow σ (uniformBound n)

theorem boundEvent_mono
    (σ : ExtendedCellLine ι) {m n : ℕ} (hmn : m ≤ n) :
    boundEvent σ m ⊆ boundEvent σ n := by
  intro c hc l
  exact (hc l).trans (by simp only [uniformBound]; exact_mod_cast hmn)

theorem exists_uniform_bound_of_finite
    {σ : ExtendedCellLine ι} {c : CellΩ ι}
    (hc : c ∈ extendedLineFinite σ) :
    ∃ n, c ∈ boundEvent σ n := by
  classical
  let x : ℝ := ∑ l, (σ c l).toReal
  refine ⟨Nat.ceil x, ?_⟩
  intro l
  have hterm : (σ c l).toReal ≤ x := by
    dsimp [x]
    exact Finset.single_le_sum
      (fun j _ => ENNReal.toReal_nonneg) (Finset.mem_univ l)
  have hreal : (σ c l).toReal ≤ (Nat.ceil x : ℝ) :=
    hterm.trans (Nat.le_ceil x)
  rw [← ENNReal.coe_toNNReal (hc l)]
  exact ENNReal.coe_le_coe.mpr (by exact_mod_cast hreal)

theorem eventually_mem_boundEvent
    {σ : ExtendedCellLine ι} {c : CellΩ ι}
    (hc : c ∈ extendedLineFinite σ) :
    ∀ᶠ n : ℕ in atTop, c ∈ boundEvent σ n := by
  obtain ⟨N, hN⟩ := exists_uniform_bound_of_finite hc
  filter_upwards [eventually_ge_atTop N] with n hn
  exact boundEvent_mono σ hn hN

private theorem finitePart_le_iff
    {x : ℝ≥0∞} (hx : x ≠ ∞) (u : ℝ≥0) :
    x.toNNReal ≤ u ↔ x ≤ (u : ℝ≥0∞) := by
  constructor
  · intro h
    calc x = ((x.toNNReal : ℝ≥0) : ℝ≥0∞) := (ENNReal.coe_toNNReal hx).symm
      _ ≤ u := by exact_mod_cast h
  · intro h
    have := ENNReal.toNNReal_mono ENNReal.coe_ne_top h
    simpa using this

/-- Ordinary finite line used at approximation level `n`. -/
noncomputable def boundedLine
    (σ : ExtendedCellLine ι) (n : ℕ) (c : CellΩ ι) : ι → ℝ≥0 :=
  if c ∈ boundEvent σ n then finitePart σ c else uniformBound n

@[fun_prop]
theorem measurable_boundedLine
    {σ : ExtendedCellLine ι} (hσ : ExtendedCellStoppingLine σ)
    (n : ℕ) : Measurable (boundedLine σ n) := by
  have hD : MeasurableSet (boundEvent σ n) :=
    (cellPast_le_ambient (uniformBound n)) _ (hσ.stopping (uniformBound n))
  exact Measurable.ite (p := fun c => c ∈ boundEvent σ n) hD
    (measurable_finitePart hσ.measurable) measurable_const

noncomputable def capBound (n : ℕ) (u : ι → ℝ≥0) : ι → ℝ≥0 :=
  fun l => min (n : ℝ≥0) (u l)

theorem capBound_le (n : ℕ) (u : ι → ℝ≥0) :
    ∀ l, capBound n u l ≤ u l := by
  intro l
  exact min_le_right _ _

theorem lineBelow_boundedLine_eq
    {σ : ExtendedCellLine ι} (n : ℕ) (u : ι → ℝ≥0) :
    lineBelow (boundedLine σ n) u =
      if (∀ l, (n : ℝ≥0) ≤ u l) then Set.univ
      else extendedLineBelow σ (capBound n u) := by
  classical
  by_cases hwide : ∀ l, (n : ℝ≥0) ≤ u l
  · rw [if_pos hwide]
    ext c
    simp only [Set.mem_univ, iff_true]
    intro l
    by_cases hc : c ∈ boundEvent σ n
    · simp only [boundedLine, if_pos hc]
      apply (finitePart_le_iff
        (ne_top_of_le_ne_top ENNReal.coe_ne_top (hc l)) _).2
      exact (hc l).trans (by exact_mod_cast hwide l)
    · simp [boundedLine, hc, uniformBound, hwide l]
  · rw [if_neg hwide]
    ext c
    constructor
    · intro hline
      have hc : c ∈ boundEvent σ n := by
        by_contra hnot
        push_neg at hwide
        obtain ⟨l, hl⟩ := hwide
        have := hline l
        simp [boundedLine, hnot, uniformBound] at this
        exact absurd this (not_le.mpr hl)
      intro l
      have hfinite := ne_top_of_le_ne_top ENNReal.coe_ne_top (hc l)
      have hu : σ c l ≤ (u l : ℝ≥0∞) := by
        apply (finitePart_le_iff hfinite _).1
        simpa [boundedLine, hc] using hline l
      exact le_min (hc l) hu
    · intro hcap
      have hc : c ∈ boundEvent σ n := by
        intro l
        exact (hcap l).trans (by
          exact_mod_cast (min_le_left (n : ℝ≥0) (u l)))
      intro l
      simp only [boundedLine, if_pos hc]
      apply (finitePart_le_iff
        (ne_top_of_le_ne_top ENNReal.coe_ne_top (hc l)) _).2
      exact (hcap l).trans (by
        exact_mod_cast (min_le_right (n : ℝ≥0) (u l)))

/-- Every bounded approximation is an ordinary finite stopping line. -/
theorem boundedLine_isStoppingLine
    {σ : ExtendedCellLine ι} (hσ : ExtendedCellStoppingLine σ)
    (n : ℕ) : CellStoppingLine (boundedLine σ n) := by
  refine ⟨measurable_boundedLine hσ n, ?_⟩
  intro u
  rw [lineBelow_boundedLine_eq]
  split_ifs with hwide
  · exact MeasurableSet.univ
  · exact (cellPast_mono (capBound_le n u)) _
      (hσ.stopping (capBound n u))

/-- Patch an extended-stopped variable outside the bounded line event. -/
noncomputable def patchAtBound
    {E : Type*} (σ : ExtendedCellLine ι) (n : ℕ)
    (H : CellΩ ι → E) (e0 : E) (c : CellΩ ι) : E :=
  if c ∈ boundEvent σ n then H c else e0

@[fun_prop]
theorem measurable_patchAtBound
    {E : Type*} [MeasurableSpace E]
    {σ : ExtendedCellLine ι} (hσ : ExtendedCellStoppingLine σ)
    {H : CellΩ ι → E}
    (hH : Measurable[extendedStoppedPast σ hσ] H)
    (n : ℕ) (e0 : E) :
    Measurable[cellStoppedPast (boundedLine σ n)
      (boundedLine_isStoppingLine hσ n)]
      (patchAtBound σ n H e0) := by
  have hDambient : MeasurableSet (boundEvent σ n) :=
    (cellPast_le_ambient (uniformBound n)) _ (hσ.stopping (uniformBound n))
  intro B hB
  refine ⟨(Measurable.ite hDambient
      (measurable_extendedStoppedPast_ambient hH) measurable_const) hB, ?_⟩
  intro u
  rw [lineBelow_boundedLine_eq]
  by_cases hwide : ∀ l, (n : ℝ≥0) ≤ u l
  · rw [if_pos hwide, Set.inter_univ]
    have hlocal :
        Measurable[cellPast (uniformBound n)]
          (patchAtBound σ n H e0) := by
      simpa [patchAtBound, localizeBelow, boundEvent] using
        (measurable_localizeBelow hσ hH (uniformBound n) e0)
    exact (Measurable.mono hlocal (cellPast_mono hwide) le_rfl) hB
  · rw [if_neg hwide]
    have hsub :
        extendedLineBelow σ (capBound n u) ⊆ boundEvent σ n := by
      intro c hc l
      exact (hc l).trans (by
        exact_mod_cast (min_le_left (n : ℝ≥0) (u l)))
    have heq :
        patchAtBound σ n H e0 ⁻¹' B ∩
            extendedLineBelow σ (capBound n u) =
          H ⁻¹' B ∩ extendedLineBelow σ (capBound n u) := by
      ext c
      by_cases hc : c ∈ extendedLineBelow σ (capBound n u)
      · have hcD := hsub hc
        simp [patchAtBound, hc, hcD]
      · simp [hc]
    rw [heq]
    exact (cellPast_mono (capBound_le n u)) _
      ((hH hB).2 (capBound n u))

noncomputable def patchedRecordAtBound
    {S : Type*} (σ : ExtendedCellLine ι) (n : ℕ)
    (R : CellΩ ι → ℕ → ℝ × S) (base : ℕ → ℝ × S)
    (c : CellΩ ι) (j : ℕ) : ℝ × S :=
  if c ∈ boundEvent σ n then R c j else base j

theorem recordPrefix_patchedRecordAtBound
    {S : Type*} (σ : ExtendedCellLine ι) (n k : ℕ)
    (R : CellΩ ι → ℕ → ℝ × S) (base : ℕ → ℝ × S) :
    recordPrefix (patchedRecordAtBound σ n R base) k =
      patchAtBound σ n (recordPrefix R k) (frestrictLe k base) := by
  funext c j
  by_cases hc : c ∈ boundEvent σ n <;>
    simp [recordPrefix, patchedRecordAtBound, patchAtBound, hc]

@[fun_prop]
theorem measurable_patchedRecordPrefix
    {S : Type*} [MeasurableSpace S]
    {σ : ExtendedCellLine ι} (hσ : ExtendedCellStoppingLine σ)
    {R : CellΩ ι → ℕ → ℝ × S} {k : ℕ}
    (hHistory :
      Measurable[extendedStoppedPast σ hσ] (recordPrefix R k))
    (n : ℕ) (base : ℕ → ℝ × S) :
    Measurable[cellStoppedPast (boundedLine σ n)
      (boundedLine_isStoppingLine hσ n)]
      (recordPrefix (patchedRecordAtBound σ n R base) k) := by
  rw [recordPrefix_patchedRecordAtBound]
  exact measurable_patchAtBound hσ hHistory n (frestrictLe k base)

/-- Pass a product factorization through almost-sure eventual equality of
both the finite history and the residual vector. -/
theorem freshResidualsAt_of_ae_eventuallyEq
    {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {R : Ω → ℕ → ℝ × S} {Rapprox : ℕ → Ω → ℕ → ℝ × S}
    {residual : Ω → ι → ℝ} {residualApprox : ℕ → Ω → ι → ℝ}
    {k : ℕ}
    (hHistory : Measurable (recordPrefix R k))
    (hResidual : Measurable residual)
    (hHistoryApprox : ∀ n, Measurable (recordPrefix (Rapprox n) k))
    (hResidualApprox : ∀ n, Measurable (residualApprox n))
    (hFresh : ∀ n, FreshResidualsAt μ (Rapprox n) (residualApprox n) k)
    (hHistoryLimit : ∀ᵐ ω ∂μ,
      ∀ᶠ n : ℕ in atTop,
        recordPrefix (Rapprox n) k ω = recordPrefix R k ω)
    (hResidualLimit : ∀ᵐ ω ∂μ,
      ∀ᶠ n : ℕ in atTop, residualApprox n ω = residual ω) :
    FreshResidualsAt μ R residual k := by
  refine
    { measurable_history := hHistory
      measurable_residual := hResidual
      joint_law := ?_ }
  refine (Measure.prod_eq ?_).symm
  intro A B hA hB
  let E : ℕ → Set Ω := fun n =>
    {ω | recordPrefix (Rapprox n) k ω ∈ A ∧ residualApprox n ω ∈ B}
  let Elimit : Set Ω :=
    {ω | recordPrefix R k ω ∈ A ∧ residual ω ∈ B}
  have hEm : ∀ n, MeasurableSet (E n) := by
    intro n
    exact ((hHistoryApprox n hA).inter (hResidualApprox n hB))
  have hElimit : MeasurableSet Elimit :=
    (hHistory hA).inter (hResidual hB)
  have hpoint : ∀ᵐ ω ∂μ,
      ∀ᶠ n : ℕ in atTop, ω ∈ E n ↔ ω ∈ Elimit := by
    filter_upwards [hHistoryLimit, hResidualLimit] with ω hh hr
    filter_upwards [hh, hr] with n hhn hrn
    simp only [E, Elimit, Set.mem_setOf_eq, hhn, hrn]
  have hleft : Tendsto (fun n => μ (E n)) atTop (𝓝 (μ Elimit)) :=
    MeasureTheory.tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure
      atTop hElimit hEm hpoint
  have hhistPoint : ∀ᵐ ω ∂μ,
      ∀ᶠ n : ℕ in atTop,
        ω ∈ recordPrefix (Rapprox n) k ⁻¹' A ↔
          ω ∈ recordPrefix R k ⁻¹' A := by
    filter_upwards [hHistoryLimit] with ω hh
    filter_upwards [hh] with n hn
    simp [hn]
  have hhistLimit :
      Tendsto
        (fun n => μ (recordPrefix (Rapprox n) k ⁻¹' A)) atTop
        (𝓝 (μ (recordPrefix R k ⁻¹' A))) :=
    MeasureTheory.tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure
      atTop (hHistory hA) (fun n => hHistoryApprox n hA) hhistPoint
  have hright :
      Tendsto (fun n => μ (E n)) atTop
        (𝓝 (μ (recordPrefix R k ⁻¹' A) * clockLaw ι B)) := by
    have hmul := ENNReal.Tendsto.mul_const hhistLimit (Or.inr (measure_ne_top (clockLaw ι) B))
    apply hmul.congr'
    filter_upwards [] with n
    have h := (hFresh n).measure_history_residual hA hB
    rw [Measure.map_apply (hHistoryApprox n) hA] at h
    exact h.symm
  have hfactor := tendsto_nhds_unique hleft hright
  rw [Measure.map_apply (hHistory.prodMk hResidual) (hA.prod hB),
    Measure.map_apply hHistory hA]
  simpa only [Elimit, Set.mem_setOf_eq, Set.mem_preimage,
    Set.mem_prod] using hfactor

/-- Real residual vector associated with an extended line.  This definition is
used only after the line-finiteness event has been charged. -/
noncomputable def extendedStoppingResidual
    (σ : ExtendedCellLine ι) (c : CellΩ ι) : ι → ℝ :=
  residualVector (finitePart σ) c

@[fun_prop]
theorem measurable_extendedStoppingResidual
    {σ : ExtendedCellLine ι} (hσ : ExtendedCellStoppingLine σ) :
    Measurable (extendedStoppingResidual σ) := by
  exact measurable_residualVector (measurable_finitePart hσ.measurable)

/-- Strong memorylessness at an extended line, on the full-measure event on
which every coordinate of the line is finite. -/
theorem extendedCellStoppingLine_freshResidualsAt
    {S : Type*} [MeasurableSpace S]
    {R : CellΩ ι → ℕ → ℝ × S} {k : ℕ}
    {σ : ExtendedCellLine ι} (hσ : ExtendedCellStoppingLine σ)
    (hHistory :
      Measurable[extendedStoppedPast σ hσ] (recordPrefix R k))
    (hfinite : ∀ᵐ c ∂cellFamilyLaw ι, c ∈ extendedLineFinite σ)
    (base : ℕ → ℝ × S) :
    FreshResidualsAt (cellFamilyLaw ι) R
      (extendedStoppingResidual σ) k := by
  let Rn : ℕ → CellΩ ι → ℕ → ℝ × S :=
    fun n => patchedRecordAtBound σ n R base
  let Zn : ℕ → CellΩ ι → ι → ℝ :=
    fun n => stoppingResidual (boundedLine σ n)
  have hHistoryAmbient : Measurable (recordPrefix R k) :=
    measurable_extendedStoppedPast_ambient hHistory
  have hHistN : ∀ n, Measurable (recordPrefix (Rn n) k) := by
    intro n
    exact measurable_stoppedPast_ambient
      (measurable_patchedRecordPrefix hσ hHistory n base)
  have hZN : ∀ n, Measurable (Zn n) := by
    intro n
    exact measurable_stoppingResidual (boundedLine_isStoppingLine hσ n)
  have hFreshN : ∀ n,
      FreshResidualsAt (cellFamilyLaw ι) (Rn n) (Zn n) k := by
    intro n
    exact cellStoppingLine_freshResidualsAt_final
      (boundedLine_isStoppingLine hσ n)
      (measurable_patchedRecordPrefix hσ hHistory n base)
  have hHistoryEventually : ∀ᵐ c ∂cellFamilyLaw ι,
      ∀ᶠ n : ℕ in atTop,
        recordPrefix (Rn n) k c = recordPrefix R k c := by
    filter_upwards [hfinite] with c hc
    filter_upwards [eventually_mem_boundEvent hc] with n hn
    funext j
    simp [Rn, patchedRecordAtBound, recordPrefix, hn]
  have hResidualEventually : ∀ᵐ c ∂cellFamilyLaw ι,
      ∀ᶠ n : ℕ in atTop,
        Zn n c = extendedStoppingResidual σ c := by
    filter_upwards [hfinite] with c hc
    filter_upwards [eventually_mem_boundEvent hc] with n hn
    have hline : boundedLine σ n c = finitePart σ c := by
      funext l
      simp [boundedLine, hn]
    have hlineFun : ∀ l, boundedLine σ n c l = finitePart σ c l := fun l => by rw [hline]
    show residualVector (boundedLine σ n) c = residualVector (finitePart σ) c
    unfold residualVector CellRandomTimeEvaluation.residualWait residualWaitE shiftedCount
    simp only [hlineFun]
  exact freshResidualsAt_of_ae_eventuallyEq
    hHistoryAmbient (measurable_extendedStoppingResidual hσ)
    hHistN hZN hFreshN hHistoryEventually hResidualEventually

/-- Direct cylinder factorization consumed by record-law proofs. -/
theorem extended_history_residual_factor
    {S : Type*} [MeasurableSpace S]
    {R : CellΩ ι → ℕ → ℝ × S} {k : ℕ}
    {σ : ExtendedCellLine ι} (hσ : ExtendedCellStoppingLine σ)
    (hHistory :
      Measurable[extendedStoppedPast σ hσ] (recordPrefix R k))
    (hfinite : ∀ᵐ c ∂cellFamilyLaw ι, c ∈ extendedLineFinite σ)
    (base : ℕ → ℝ × S)
    {A : Set ((i : Finset.Iic k) → ℝ × S)}
    {B : Set (ι → ℝ)}
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    cellFamilyLaw ι
        {c | recordPrefix R k c ∈ A ∧
          extendedStoppingResidual σ c ∈ B} =
      ((cellFamilyLaw ι).map (recordPrefix R k)) A * clockLaw ι B := by
  exact (extendedCellStoppingLine_freshResidualsAt
    hσ hHistory hfinite base).measure_history_residual hA hB

/-- Formal counterexample showing why line finiteness must be explicit. -/
theorem constantTop_isExtendedStoppingLine :
    ExtendedCellStoppingLine
      (fun (_ : CellΩ ι) (_ : ι) => (∞ : ℝ≥0∞)) := by
  refine ⟨measurable_const, ?_⟩
  intro u
  by_cases hne : Nonempty ι
  · have heq :
        extendedLineBelow
            (fun (_ : CellΩ ι) (_ : ι) => (∞ : ℝ≥0∞)) u = ∅ := by
      ext c
      obtain ⟨l⟩ := hne
      simp only [extendedLineBelow, Set.mem_setOf_eq, Set.mem_empty_iff_false,
        iff_false, not_forall]
      exact ⟨l, by simp⟩
    rw [heq]
    exact @MeasurableSet.empty _ (cellPast u)
  · have heq :
        extendedLineBelow
            (fun (_ : CellΩ ι) (_ : ι) => (∞ : ℝ≥0∞)) u = Set.univ := by
      ext c
      simp only [extendedLineBelow, Set.mem_setOf_eq, Set.mem_univ, iff_true]
      intro l
      exact absurd ⟨l⟩ hne
    rw [heq]
    exact @MeasurableSet.univ _ (cellPast u)

/-- For nonempty `ι` the constant `⊤` line is not almost surely finite.  (For
empty `ι` finiteness is vacuous, so `[Nonempty ι]` is required.) -/
theorem constantTop_not_finite [Nonempty ι] (c : CellΩ ι) :
    c ∉ extendedLineFinite
      (fun (_ : CellΩ ι) (_ : ι) => (∞ : ℝ≥0∞)) := by
  obtain ⟨l⟩ := ‹Nonempty ι›
  intro h
  exact h l rfl

end Ripple.Kurtz.StrongApprox.CellExtendedStoppingLine

end
