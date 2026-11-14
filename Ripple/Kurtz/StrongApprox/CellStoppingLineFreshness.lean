-- Ripple/Kurtz/StrongApprox/CellStoppingLineFreshness.lean
import Ripple.Kurtz.StrongApprox.CellRandomTimeEvaluation
import Mathlib.MeasureTheory.Integral.Indicator

noncomputable section

namespace Ripple.Kurtz.StrongApprox.CellStoppingLineFreshness

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal BigOperators
open CellRandomTimeEvaluation

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev CellΩ (ι : Type*) := CellFamily ι

/-- The literal rectangular natural filtration requested in the question. -/
noncomputable def cellPast (u : ι → ℝ≥0) : MeasurableSpace (CellΩ ι) :=
  ⨆ l : ι, ⨆ s : ℝ≥0, ⨆ (_h : s ≤ u l),
    MeasurableSpace.comap
      (fun c : CellΩ ι => cellPath s (c l))
      inferInstance

theorem cellPast_le_ambient (u : ι → ℝ≥0) :
    cellPast u ≤ (inferInstance : MeasurableSpace (CellΩ ι)) := by
  unfold cellPast
  refine iSup_le fun l => iSup_le fun s => iSup_le fun _ => ?_
  exact ((measurable_cellPath s).comp
    (measurable_pi_apply l)).comap_le

theorem cellPast_mono {u v : ι → ℝ≥0}
    (huv : ∀ l, u l ≤ v l) : cellPast u ≤ cellPast v := by
  unfold cellPast
  refine iSup_le fun l => iSup_le fun s => iSup_le fun hs => ?_
  exact le_iSup_of_le l <| le_iSup_of_le s <|
    le_iSup_of_le (hs.trans (huv l)) le_rfl

@[fun_prop]
theorem measurable_cellPath_cellPast (u : ι → ℝ≥0)
    (l : ι) (s : ℝ≥0) (hs : s ≤ u l) :
    Measurable[cellPast u]
      (fun c : CellΩ ι => cellPath s (c l)) := by
  apply Measurable.of_comap_le
  unfold cellPast
  exact le_iSup_of_le l <| le_iSup_of_le s <|
    le_iSup_of_le hs le_rfl

def lineBelow
    (σ : CellΩ ι → ι → ℝ≥0) (u : ι → ℝ≥0) : Set (CellΩ ι) :=
  {c | ∀ l, σ c l ≤ u l}

/-- Multiparameter stopping line for the rectangular cell filtration. -/
structure CellStoppingLine
    (σ : CellΩ ι → ι → ℝ≥0) : Prop where
  measurable : Measurable σ
  stopping : ∀ u, MeasurableSet[cellPast u] (lineBelow σ u)

/-- The standard stopped σ-algebra: `A ∈ F_σ` iff every stopped rectangle
`A ∩ {σ ≤ u}` belongs to `F_u`. -/
noncomputable def cellStoppedPast
    (σ : CellΩ ι → ι → ℝ≥0) (hσ : CellStoppingLine σ) :
    MeasurableSpace (CellΩ ι) where
  MeasurableSet' A :=
    MeasurableSet A ∧
      ∀ u, MeasurableSet[cellPast u] (A ∩ lineBelow σ u)
  measurableSet_empty := by
    constructor
    · exact MeasurableSet.empty
    · intro u
      simp
  measurableSet_compl := by
    intro A hA
    constructor
    · exact hA.1.compl
    · intro u
      have hdiff := (hσ.stopping u).diff (hA.2 u)
      have heq :
          Aᶜ ∩ lineBelow σ u =
            lineBelow σ u \ (A ∩ lineBelow σ u) := by
        ext c
        simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_diff]
        tauto
      rw [heq]
      exact hdiff
  measurableSet_iUnion := by
    intro A hA
    constructor
    · exact MeasurableSet.iUnion fun n => (hA n).1
    · intro u
      have heq :
          (⋃ n, A n) ∩ lineBelow σ u =
            ⋃ n, (A n ∩ lineBelow σ u) := by
        ext c
        simp
      rw [heq]
      exact MeasurableSet.iUnion fun n => (hA n).2 u

theorem stoppedPast_ambient
    {σ : CellΩ ι → ι → ℝ≥0} {hσ : CellStoppingLine σ}
    {A : Set (CellΩ ι)}
    (hA : MeasurableSet[cellStoppedPast σ hσ] A) :
    MeasurableSet A := by
  exact hA.1

theorem stoppedPast_inter_below
    {σ : CellΩ ι → ι → ℝ≥0} {hσ : CellStoppingLine σ}
    {A : Set (CellΩ ι)}
    (hA : MeasurableSet[cellStoppedPast σ hσ] A)
    (u : ι → ℝ≥0) :
    MeasurableSet[cellPast u] (A ∩ lineBelow σ u) := by
  exact hA.2 u

theorem measurable_stoppedPast_ambient
    {E : Type*} [MeasurableSpace E]
    {σ : CellΩ ι → ι → ℝ≥0} {hσ : CellStoppingLine σ}
    {H : CellΩ ι → E}
    (hH : Measurable[cellStoppedPast σ hσ] H) : Measurable H := by
  intro A hA
  exact stoppedPast_ambient (hH hA)

abbrev GridIndex (ι : Type*) := ι → ℕ

noncomputable def gridVector (m : ℕ) (a : GridIndex ι) : ι → ℝ≥0 :=
  fun l => dyadicGridTime m (a l)

noncomputable def roundedIndex (m : ℕ)
    (σ : CellΩ ι → ι → ℝ≥0) (c : CellΩ ι) : GridIndex ι :=
  fun l => upperDyadicIndex m (σ c l)

noncomputable def roundedLine (m : ℕ)
    (σ : CellΩ ι → ι → ℝ≥0) (c : CellΩ ι) : ι → ℝ≥0 :=
  fun l => upperDyadicTime m (σ c l)

@[fun_prop]
theorem measurable_roundedLine (m : ℕ)
    {σ : CellΩ ι → ι → ℝ≥0} (hσ : Measurable σ) :
    Measurable (roundedLine m σ) := by
  apply measurable_pi_lambda
  intro l
  exact (measurable_upperDyadicTime m).comp
    ((measurable_pi_apply l).comp hσ)

theorem roundedLine_eq_gridVector (m : ℕ)
    (σ : CellΩ ι → ι → ℝ≥0) (c : CellΩ ι) :
    roundedLine m σ c = gridVector m (roundedIndex m σ c) := by
  funext l
  rfl

def roundedFiber (m : ℕ)
    (σ : CellΩ ι → ι → ℝ≥0) (a : GridIndex ι) : Set (CellΩ ι) :=
  {c | roundedIndex m σ c = a}

noncomputable def lowerGridVector (m : ℕ) (a : GridIndex ι) (l : ι) :
    ι → ℝ≥0 :=
  Function.update (gridVector m a) l (dyadicGridTime m (a l - 1))

theorem lowerGridVector_le (m : ℕ) (a : GridIndex ι) (l j : ι) :
    lowerGridVector m a l j ≤ gridVector m a j := by
  classical
  by_cases hj : j = l
  · subst j
    simp only [lowerGridVector, Function.update_self, gridVector]
    unfold dyadicGridTime
    exact div_le_div_of_nonneg_right (by exact_mod_cast Nat.sub_le (a l) 1)
      zero_le
  · simp [lowerGridVector, Function.update_of_ne hj]

private theorem mem_roundedFiber_iff
    (m : ℕ) (σ : CellΩ ι → ι → ℝ≥0)
    (a : GridIndex ι) (c : CellΩ ι) :
    c ∈ roundedFiber m σ a ↔
      c ∈ lineBelow σ (gridVector m a) ∧
        ∀ l, 0 < a l → c ∉ lineBelow σ (lowerGridVector m a l) := by
  classical
  constructor
  · intro h
    have hindex : roundedIndex m σ c = a := h
    constructor
    · intro l
      apply (upperDyadicIndex_le_iff m (a l) (σ c l)).mp
      have hl : upperDyadicIndex m (σ c l) = a l := congrFun hindex l
      exact hl.le
    · intro l hal hlower
      have hle : roundedIndex m σ c l ≤ a l - 1 := by
        apply (upperDyadicIndex_le_iff m (a l - 1) (σ c l)).mpr
        simpa [lowerGridVector] using hlower l
      have hl : roundedIndex m σ c l = a l := congrFun hindex l
      omega
  · rintro ⟨hbase, hproper⟩
    apply funext
    intro l
    have hle : roundedIndex m σ c l ≤ a l :=
      (upperDyadicIndex_le_iff m (a l) (σ c l)).mpr (hbase l)
    by_contra hne
    have hlt : roundedIndex m σ c l < a l := by omega
    have hal : 0 < a l := by omega
    apply hproper l hal
    intro j
    by_cases hj : j = l
    · subst j
      simp only [lowerGridVector, Function.update_self]
      apply (upperDyadicIndex_le_iff m (a l - 1) (σ c l)).mp
      have hri : roundedIndex m σ c l = upperDyadicIndex m (σ c l) := rfl
      omega
    · simp only [lowerGridVector, Function.update_of_ne hj]
      exact hbase j

private theorem roundedFiber_set_eq
    (m : ℕ) (σ : CellΩ ι → ι → ℝ≥0) (a : GridIndex ι) :
    roundedFiber m σ a =
      lineBelow σ (gridVector m a) \
        ⋃ l : ι,
          if 0 < a l then lineBelow σ (lowerGridVector m a l) else ∅ := by
  classical
  have hmem : ∀ c, c ∈ (⋃ l : ι, if 0 < a l then
      lineBelow σ (lowerGridVector m a l) else ∅) ↔
      ∃ l, 0 < a l ∧ c ∈ lineBelow σ (lowerGridVector m a l) := by
    intro c
    simp only [Set.mem_iUnion]
    refine exists_congr fun l => ?_
    by_cases h : 0 < a l <;> simp [h]
  ext c
  rw [mem_roundedFiber_iff, Set.mem_diff, hmem]
  simp only [not_exists, not_and]

/-- The exact rounded fibre is measurable in the rectangular past at its
upper corner.  This is the multiparameter stopping-line step. -/
theorem roundedFiber_measurable
    {σ : CellΩ ι → ι → ℝ≥0} (hσ : CellStoppingLine σ)
    (m : ℕ) (a : GridIndex ι) :
    MeasurableSet[cellPast (gridVector m a)] (roundedFiber m σ a) := by
  classical
  rw [roundedFiber_set_eq]
  apply (hσ.stopping (gridVector m a)).diff
  apply MeasurableSet.iUnion
  intro l
  by_cases hal : 0 < a l
  · rw [if_pos hal]
    exact cellPast_mono (fun j => lowerGridVector_le m a l j) _
      (hσ.stopping (lowerGridVector m a l))
  · rw [if_neg hal]
    exact @MeasurableSet.empty _ (cellPast (gridVector m a))

theorem stoppedPast_inter_fiber_measurable
    {σ : CellΩ ι → ι → ℝ≥0} {hσ : CellStoppingLine σ}
    {A : Set (CellΩ ι)}
    (hA : MeasurableSet[cellStoppedPast σ hσ] A)
    (m : ℕ) (a : GridIndex ι) :
    MeasurableSet[cellPast (gridVector m a)]
      (A ∩ roundedFiber m σ a) := by
  have hsub : roundedFiber m σ a ⊆ lineBelow σ (gridVector m a) := by
    intro c hc
    exact (mem_roundedFiber_iff m σ a c).mp hc |>.1
  have heq :
      A ∩ roundedFiber m σ a =
        (A ∩ lineBelow σ (gridVector m a)) ∩ roundedFiber m σ a := by
    ext c
    simp only [Set.mem_inter_iff]
    tauto
  rw [heq]
  exact (stoppedPast_inter_below hA _).inter
    (roundedFiber_measurable hσ m a)

/-- Deterministic renewal interface supplied by the finite
past/future theorem.  `G u` is a deterministic-time future observable. -/
structure DeterministicFresh
    {F : Type*} [MeasurableSpace F]
    (G : (ι → ℝ≥0) → CellΩ ι → F) (ν : Measure F) : Prop where
  measurable_future : ∀ u, Measurable (G u)
  factor : ∀ u (A : Set (CellΩ ι)) (B : Set F),
    MeasurableSet[cellPast u] A → MeasurableSet B →
      cellFamilyLaw ι (A ∩ G u ⁻¹' B) =
        cellFamilyLaw ι A * ν B

noncomputable def roundedFuture
    {F : Type*} [MeasurableSpace F]
    (G : (ι → ℝ≥0) → CellΩ ι → F)
    (m : ℕ) (σ : CellΩ ι → ι → ℝ≥0) (c : CellΩ ι) : F :=
  G (roundedLine m σ c) c

private theorem roundedFuture_preimage
    {F : Type*} [MeasurableSpace F]
    (G : (ι → ℝ≥0) → CellΩ ι → F)
    (m : ℕ) (σ : CellΩ ι → ι → ℝ≥0) (B : Set F) :
    roundedFuture G m σ ⁻¹' B =
      ⋃ a : GridIndex ι,
        roundedFiber m σ a ∩ G (gridVector m a) ⁻¹' B := by
  ext c
  constructor
  · intro hc
    apply Set.mem_iUnion.mpr
    refine ⟨roundedIndex m σ c, rfl, ?_⟩
    simpa only [roundedFuture, roundedLine_eq_gridVector] using hc
  · intro hc
    obtain ⟨a, hfiber, hfuture⟩ := Set.mem_iUnion.mp hc
    have heq : roundedLine m σ c = gridVector m a := by
      rw [roundedLine_eq_gridVector, hfiber]
    simpa only [Set.mem_preimage, roundedFuture, heq] using hfuture

@[fun_prop]
theorem measurable_roundedFuture
    {F : Type*} [MeasurableSpace F]
    {G : (ι → ℝ≥0) → CellΩ ι → F}
    (hG : ∀ u, Measurable (G u))
    {σ : CellΩ ι → ι → ℝ≥0} (hσ : CellStoppingLine σ)
    (m : ℕ) : Measurable (roundedFuture G m σ) := by
  intro B hB
  rw [roundedFuture_preimage]
  apply MeasurableSet.iUnion
  intro a
  exact (cellPast_le_ambient _ _ (roundedFiber_measurable hσ m a)).inter
    ((hG (gridVector m a)) hB)

private theorem roundedFibres_pairwise
    (m : ℕ) (σ : CellΩ ι → ι → ℝ≥0) :
    Pairwise fun a b : GridIndex ι =>
      Disjoint (roundedFiber m σ a) (roundedFiber m σ b) := by
  intro a b hab
  apply Set.disjoint_left.mpr
  intro c ha hb
  exact hab (ha.symm.trans hb)

private theorem iUnion_roundedFiber
    (m : ℕ) (σ : CellΩ ι → ι → ℝ≥0) :
    (⋃ a : GridIndex ι, roundedFiber m σ a) = Set.univ := by
  ext c
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  exact ⟨roundedIndex m σ c, rfl⟩

/-- Countable dyadic-fibre mixture.  This is the missing random-grid step; it uses no conditioning on a future event. -/
theorem rounded_event_factor
    {F : Type*} [MeasurableSpace F]
    {G : (ι → ℝ≥0) → CellΩ ι → F} {ν : Measure F}
    (hdet : DeterministicFresh G ν)
    {σ : CellΩ ι → ι → ℝ≥0} (hσ : CellStoppingLine σ)
    (m : ℕ) (A : Set (CellΩ ι)) (B : Set F)
    (hA : MeasurableSet[cellStoppedPast σ hσ] A)
    (hB : MeasurableSet B) :
    cellFamilyLaw ι
        (A ∩ roundedFuture G m σ ⁻¹' B) =
      cellFamilyLaw ι A * ν B := by
  classical
  let μ := cellFamilyLaw ι
  let E : GridIndex ι → Set (CellΩ ι) :=
    fun a => A ∩ roundedFiber m σ a
  have hEmeas (a : GridIndex ι) :
      MeasurableSet (E a) :=
    cellPast_le_ambient _ _ (stoppedPast_inter_fiber_measurable hA m a)
  have hEpair : Pairwise fun a b => Disjoint (E a) (E b) := by
    intro a b hab
    exact Disjoint.mono inter_subset_right inter_subset_right
      (roundedFibres_pairwise m σ hab)
  have hEunion : (⋃ a, E a) = A := by
    ext c
    simp only [E, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · rintro ⟨a, hA', _⟩
      exact hA'
    · intro hA'
      exact ⟨roundedIndex m σ c, hA', rfl⟩
  have hunion :
      A ∩ roundedFuture G m σ ⁻¹' B =
        ⋃ a : GridIndex ι,
          E a ∩ G (gridVector m a) ⁻¹' B := by
    rw [roundedFuture_preimage]
    ext c
    simp only [E, Set.mem_inter_iff, Set.mem_iUnion]
    tauto
  have hpiece (a : GridIndex ι) :
      μ (E a ∩ G (gridVector m a) ⁻¹' B) = μ (E a) * ν B := by
    exact hdet.factor (gridVector m a) (E a) B
      (stoppedPast_inter_fiber_measurable hA m a) hB
  rw [hunion, measure_iUnion]
  · calc
      (∑' a, μ (E a ∩ G (gridVector m a) ⁻¹' B)) =
          ∑' a, μ (E a) * ν B := by
        congr 1
        funext a
        exact hpiece a
      _ = (∑' a, μ (E a)) * ν B := ENNReal.tsum_mul_right
      _ = μ A * ν B := by
        rw [← measure_iUnion hEpair hEmeas, hEunion]
  · intro a b hab
    exact Disjoint.mono inter_subset_left inter_subset_left
      (hEpair hab)
  · intro a
    exact (hEmeas a).inter
      ((hdet.measurable_future (gridVector m a)) hB)

/-- A finite cylinder of shifted counts. -/
noncomputable def futureVector
    {κ : Type*} [Fintype κ]
    (u : ι → ℝ≥0) (channel : κ → ι) (delay : κ → ℚ≥0)
    (c : CellΩ ι) : κ → ℕ :=
  fun j =>
    cellPath
        ((u (channel j) : ℝ) + ((delay j : ℝ≥0) : ℝ))
        (c (channel j)) -
      cellPath (u (channel j)) (c (channel j))

@[fun_prop]
theorem measurable_futureVector
    {κ : Type*} [Fintype κ]
    (u : ι → ℝ≥0) (channel : κ → ι) (delay : κ → ℚ≥0) :
    Measurable (futureVector u channel delay) := by
  apply measurable_pi_lambda
  intro j
  exact ((measurable_cellPath _).comp
      (measurable_pi_apply (channel j))).sub
    ((measurable_cellPath _).comp
      (measurable_pi_apply (channel j)))

/-- The same cylinder evaluated after a random line. -/
noncomputable def stoppedFutureVector
    {κ : Type*} [Fintype κ]
    (σ : CellΩ ι → ι → ℝ≥0)
    (channel : κ → ι) (delay : κ → ℚ≥0)
    (c : CellΩ ι) : κ → ℕ :=
  futureVector (σ c) channel delay c

@[fun_prop]
theorem measurable_stoppedFutureVector
    {κ : Type*} [Fintype κ]
    {σ : CellΩ ι → ι → ℝ≥0} (hσ : Measurable σ)
    (channel : κ → ι) (delay : κ → ℚ≥0) :
    Measurable (stoppedFutureVector σ channel delay) := by
  apply measurable_pi_lambda
  intro j
  have hs : Measurable fun c => σ c (channel j) :=
    (measurable_pi_apply (channel j)).comp hσ
  have he : Measurable fun c =>
      σ c (channel j) + (delay j : ℝ≥0) := hs.add measurable_const
  exact (CellRandomTimeEvaluation.measurable_cellFamilyPath_randomTime
      id measurable_id
      (fun c => fun _ => σ c (channel j) + (delay j : ℝ≥0))
      (measurable_pi_lambda _ fun _ => he) (channel j)).sub
    (CellRandomTimeEvaluation.measurable_cellFamilyPath_randomTime
      id measurable_id σ hσ (channel j))

private theorem roundedFutureVector_eventually
    {κ : Type*} [Fintype κ]
    (σ : CellΩ ι → ι → ℝ≥0)
    (channel : κ → ι) (delay : κ → ℚ≥0)
    (c : CellΩ ι) :
    ∀ᶠ m : ℕ in atTop,
      roundedFuture (fun u => futureVector u channel delay) m σ c =
        stoppedFutureVector σ channel delay c := by
  have hcoord (j : κ) :
      ∀ᶠ m : ℕ in atTop,
        roundedFuture (fun u => futureVector u channel delay) m σ c j =
          stoppedFutureVector σ channel delay c j := by
    have hstart := cellPath_upperDyadic_eventually
      (c (channel j)) (σ c (channel j))
    have hend := cellPath_upperDyadic_add_eventually
      (c (channel j)) (σ c (channel j)) (delay j : ℝ≥0)
    filter_upwards [hstart, hend] with m hs he
    simp only [roundedFuture, roundedLine, futureVector,
      stoppedFutureVector]
    rw [hs, he]
  have hall : ∀ᶠ m : ℕ in atTop, ∀ j : κ,
      roundedFuture (fun u => futureVector u channel delay) m σ c j =
        stoppedFutureVector σ channel delay c j := by
    exact Filter.eventually_all.2 hcoord
  filter_upwards [hall] with m hm
  funext j
  exact hm j

/-- **Strong memorylessness on the cell space, finite-cylinder form.**
The right-hand future law is the deterministic zero-start unit-Poisson law.
Finite rational cylinders generate the complete rational skeleton. -/
theorem stoppingLine_futureCylinder
    {κ : Type*} [Fintype κ]
    (channel : κ → ι) (delay : κ → ℚ≥0)
    {σ : CellΩ ι → ι → ℝ≥0} (hσ : CellStoppingLine σ)
    (hdet : DeterministicFresh
      (fun u => futureVector u channel delay)
      ((cellFamilyLaw ι).map
        (futureVector (fun _ => 0) channel delay)))
    (A : Set (CellΩ ι)) (B : Set (κ → ℕ))
    (hA : MeasurableSet[cellStoppedPast σ hσ] A)
    (hB : MeasurableSet B) :
    cellFamilyLaw ι
        (A ∩ stoppedFutureVector σ channel delay ⁻¹' B) =
      cellFamilyLaw ι A *
        ((cellFamilyLaw ι).map
          (futureVector (fun _ => 0) channel delay)) B := by
  let μ := cellFamilyLaw ι
  let G := fun u => futureVector u channel delay
  let ν := μ.map (futureVector (fun _ => 0) channel delay)
  let E : ℕ → Set (CellΩ ι) := fun m =>
    A ∩ roundedFuture G m σ ⁻¹' B
  let Einf : Set (CellΩ ι) :=
    A ∩ stoppedFutureVector σ channel delay ⁻¹' B
  have hEmeas (m : ℕ) : MeasurableSet (E m) :=
    (stoppedPast_ambient hA).inter
      ((measurable_roundedFuture hdet.measurable_future hσ m) hB)
  have hEinfmeas : MeasurableSet Einf :=
    (stoppedPast_ambient hA).inter
      ((measurable_stoppedFutureVector hσ.measurable channel delay) hB)
  have hpoint (c : CellΩ ι) :
      ∀ᶠ m : ℕ in atTop, c ∈ E m ↔ c ∈ Einf := by
    have hfuture := roundedFutureVector_eventually σ channel delay c
    filter_upwards [hfuture] with m hm
    simp only [E, Einf, Set.mem_inter_iff, Set.mem_preimage]
    rw [hm]
  have hlimit : Tendsto (fun m => μ (E m)) atTop (𝓝 (μ Einf)) :=
    MeasureTheory.tendsto_measure_of_tendsto_indicator_of_isFiniteMeasure
      atTop μ hEmeas hpoint
  have hconstant : ∀ m, μ (E m) = μ A * ν B := by
    intro m
    exact rounded_event_factor hdet hσ m A B hA hB
  have hconstLimit : Tendsto (fun m => μ (E m)) atTop
      (𝓝 (μ A * ν B)) := by
    simpa only [hconstant] using tendsto_const_nhds
  exact tendsto_nhds_unique hlimit hconstLimit

/-- Package of all finite rational cylinders.  For the cell paths this is the
full shifted-path statement, because right-continuous integer-valued paths are
determined by their nonnegative rational skeleton. -/
structure FreshShiftedCountingPathsAt
    (σ : CellΩ ι → ι → ℝ≥0) (hσ : CellStoppingLine σ) : Prop where
  cylinder_factor : ∀ {κ : Type*} [Fintype κ]
    (channel : κ → ι) (delay : κ → ℚ≥0),
    DeterministicFresh
      (fun u => futureVector u channel delay)
      ((cellFamilyLaw ι).map
        (futureVector (fun _ => 0) channel delay)) →
    ∀ (A : Set (CellΩ ι)) (B : Set (κ → ℕ)),
      MeasurableSet[cellStoppedPast σ hσ] A → MeasurableSet B →
      cellFamilyLaw ι
          (A ∩ stoppedFutureVector σ channel delay ⁻¹' B) =
        cellFamilyLaw ι A *
          ((cellFamilyLaw ι).map
            (futureVector (fun _ => 0) channel delay)) B

theorem stoppingLine_strongMemorylessness
    {σ : CellΩ ι → ι → ℝ≥0} (hσ : CellStoppingLine σ) :
    FreshShiftedCountingPathsAt σ hσ := by
  refine ⟨?_⟩
  intro κ _ channel delay hdet A B hA hB
  exact stoppingLine_futureCylinder channel delay hσ hdet A B hA hB

end Ripple.Kurtz.StrongApprox.CellStoppingLineFreshness

end
