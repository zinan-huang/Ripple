-- Ripple/Kurtz/StrongApprox/CellStoppingLineCylinders.lean
import Ripple.Kurtz.StrongApprox.CellStoppingLineAdapters

noncomputable section

namespace Ripple.Kurtz.StrongApprox.CellStoppingLineCylinders

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal BigOperators

/-! ### Stationarity of finite increment vectors of one cell path -/

theorem floor_cast_sub {x y : ℕ} (h : y ≤ x) :
    ⌊((x : ℝ) - (y : ℝ))⌋₊ = x - y := by
  rw [← Nat.cast_sub h, Nat.floor_natCast]

/-- Exact Poisson law of the increment over `[s, s+t]`. -/
theorem cellPath_increment_eq (s t : ℝ≥0) (k : ℕ) :
    cellArrayLaw {c | cellPath ((s + t : ℝ≥0) : ℝ) c - cellPath (s : ℝ) c = k} =
      ENNReal.ofReal (poisTerm k (t : ℝ)) := by
  let G : (ℝ → ℕ) → ℕ := fun Y => Y ((s + t : ℝ≥0) : ℝ) - Y (s : ℝ)
  have hG : Measurable G := by
    have : Measurable (fun Y : ℝ → ℕ => (Y ((s + t : ℝ≥0) : ℝ), Y (s : ℝ))) :=
      (measurable_pi_apply _).prodMk (measurable_pi_apply _)
    exact (measurable_of_countable (fun p : ℕ × ℕ => p.1 - p.2)).comp this
  have h := cellArrayLaw_map_path G hG
  have hmeas : MeasurableSet ({k} : Set ℕ) := measurableSet_singleton k
  have h1 := congrArg (fun μ : Measure ℕ => μ {k}) h
  dsimp only at h1
  rw [Measure.map_apply
      (show Measurable (fun c : ℕ → CellSpace => G (fun u => cellPath u c)) from
        hG.comp measurable_cellPathMap) hmeas,
    Measure.map_apply
      (show Measurable (fun x : PathSpace SIPSpace => G (fun u => sipPath u x)) from
        hG.comp (measurable_pathMap measurable_sipN)) hmeas] at h1
  have h2 := sipPathMeasure_increment_eq (s := (s : ℝ)) (t := ((s + t : ℝ≥0) : ℝ))
    s.2 (by simp) k
  calc
    cellArrayLaw {c | cellPath ((s + t : ℝ≥0) : ℝ) c - cellPath (s : ℝ) c = k} =
        cellArrayLaw ((fun c : ℕ → CellSpace => G (fun u => cellPath u c)) ⁻¹' {k}) :=
      rfl
    _ = (pathMeasure sipMeasure)
          ((fun x : PathSpace SIPSpace => G (fun u => sipPath u x)) ⁻¹' {k}) := h1
    _ = (pathMeasure sipMeasure)
          {x | sipPath ((s + t : ℝ≥0) : ℝ) x - sipPath (s : ℝ) x = k} := rfl
    _ = ENNReal.ofReal (poisTerm k (((s + t : ℝ≥0) : ℝ) - s)) := h2
    _ = ENNReal.ofReal (poisTerm k (t : ℝ)) := by
      congr 2
      rw [NNReal.coe_add]
      ring

/-- Increment vector with the default value `0` off `D`. -/
def Vec (a : ℝ≥0) (D : Finset ℝ≥0) (c : ℕ → CellSpace) : ℝ≥0 → ℕ :=
  fun t => if t ∈ D then cellPath ((a + t : ℝ≥0) : ℝ) c - cellPath (a : ℝ) c else 0

theorem measurable_Vec (a : ℝ≥0) (D : Finset ℝ≥0) : Measurable (Vec a D) := by
  apply measurable_pi_lambda
  intro t
  by_cases ht : t ∈ D
  · simp only [Vec, ht, if_true]
    exact (measurable_of_countable (fun p : ℕ × ℕ => p.1 - p.2)).comp
      ((measurable_cellPath _).prodMk (measurable_cellPath _))
  · simp only [Vec, ht, if_false]
    exact measurable_const

/-- The last increment added when the largest delay `m` is inserted. -/
def lastInc (a : ℝ≥0) (D' : Finset ℝ≥0) (m : ℝ≥0) (c : ℕ → CellSpace) : ℕ :=
  cellPath ((a + m : ℝ≥0) : ℝ) c - cellPath ((a + D'.sup id : ℝ≥0) : ℝ) c

theorem measurable_lastInc (a : ℝ≥0) (D' : Finset ℝ≥0) (m : ℝ≥0) :
    Measurable (lastInc a D' m) :=
  (measurable_of_countable (fun p : ℕ × ℕ => p.1 - p.2)).comp
    ((measurable_cellPath _).prodMk (measurable_cellPath _))

/-- Gluing map. -/
def glue (m m' : ℝ≥0) (p : (ℝ≥0 → ℕ) × ℕ) : ℝ≥0 → ℕ :=
  fun t => if t = m then p.1 m' + p.2 else p.1 t

theorem measurable_glue (m m' : ℝ≥0) : Measurable (glue m m') := by
  apply measurable_pi_lambda
  intro t
  by_cases ht : t = m
  · simp only [glue, ht, if_true]
    exact ((measurable_pi_apply m').comp measurable_fst).add measurable_snd
  · simp only [glue, ht, if_false]
    exact (measurable_pi_apply t).comp measurable_fst

theorem Vec_at_sup (a : ℝ≥0) (D' : Finset ℝ≥0) (c : ℕ → CellSpace) :
    Vec a D' c (D'.sup id) =
      cellPath ((a + D'.sup id : ℝ≥0) : ℝ) c - cellPath (a : ℝ) c := by
  rcases D'.eq_empty_or_nonempty with h | h
  · subst h
    simp [Vec]
  · obtain ⟨x, hx, hsup⟩ := Finset.exists_mem_eq_sup D' h id
    have hmem : D'.sup id ∈ D' := by rw [hsup]; exact hx
    simp [Vec, hmem]

theorem Vec_insert (a : ℝ≥0) (D' : Finset ℝ≥0) (m : ℝ≥0)
    (hm : ∀ x ∈ D', x < m) (c : ℕ → CellSpace) :
    Vec a (insert m D') c = glue m (D'.sup id) (Vec a D' c, lastInc a D' m c) := by
  have hm' : D'.sup id ≤ m := Finset.sup_le fun x hx => (hm x hx).le
  funext t
  by_cases ht : t = m
  · subst ht
    have hL : Vec a (insert t D') c t =
        cellPath ((a + t : ℝ≥0) : ℝ) c - cellPath (a : ℝ) c := by
      simp [Vec]
    have h1 : cellPath (a : ℝ) c ≤ cellPath ((a + D'.sup id : ℝ≥0) : ℝ) c :=
      cellPath_mono (by simp) c
    have hle : a + D'.sup id ≤ a + t := by gcongr
    have h2 : cellPath ((a + D'.sup id : ℝ≥0) : ℝ) c ≤ cellPath ((a + t : ℝ≥0) : ℝ) c :=
      cellPath_mono (NNReal.coe_le_coe.mpr hle) c
    simp only [glue, if_true]
    rw [hL, Vec_at_sup a D' c]
    unfold lastInc
    omega
  · simp only [glue, ht, if_false, Vec, Finset.mem_insert, false_or]

theorem Vec_lastInc_indep (a : ℝ≥0) (D' : Finset ℝ≥0) (m : ℝ≥0)
    (hm : ∀ x ∈ D', x < m) :
    IndepFun (Vec a D') (lastInc a D' m) cellArrayLaw := by
  classical
  have hm' : D'.sup id ≤ m := Finset.sup_le fun x hx => (hm x hx).le
  let I : Finset ℝ≥0 := insert a (D'.image fun x => a + x)
  let J : Finset ℝ≥0 := {m - D'.sup id}
  have hind := finite_before_after_indep (a + D'.sup id) I J
  let ψ1 : (I → ℝ) → (ℝ≥0 → ℕ) := fun z t =>
    if h : t ∈ D' then
      ⌊z ⟨a + t, by simp [I, h]⟩ - z ⟨a, by simp [I]⟩⌋₊ else 0
  let ψ2 : (J → ℝ) → ℕ := fun w => ⌊w ⟨m - D'.sup id, by simp [J]⟩⌋₊
  have hψ1 : Measurable ψ1 := by
    apply measurable_pi_lambda
    intro t
    by_cases ht : t ∈ D'
    · simp only [ψ1, ht, dif_pos]
      exact Nat.measurable_floor.comp
        ((measurable_pi_apply (⟨a + t, by simp [I, ht]⟩ : I)).sub
          (measurable_pi_apply (⟨a, by simp [I]⟩ : I)))
    · simp only [ψ1, ht, dif_neg, not_false_eq_true]
      exact measurable_const
  have hψ2 : Measurable ψ2 :=
    Nat.measurable_floor.comp (measurable_pi_apply _)
  have e1 : Vec a D' = ψ1 ∘ (fun (c : ℕ → CellSpace) (i : I) =>
      (cellPath (min (i.1 : ℝ) ((a + D'.sup id : ℝ≥0) : ℝ)) c : ℝ)) := by
    funext c t
    by_cases ht : t ∈ D'
    · simp only [Function.comp_apply, ψ1, Vec, ht, dif_pos, if_true]
      have hle1 : ((a + t : ℝ≥0) : ℝ) ≤ ((a + D'.sup id : ℝ≥0) : ℝ) := by
        have : t ≤ D'.sup id := Finset.le_sup (f := id) ht
        exact NNReal.coe_le_coe.mpr (by gcongr)
      have hle2 : (a : ℝ) ≤ ((a + D'.sup id : ℝ≥0) : ℝ) := by simp
      rw [min_eq_left hle1, min_eq_left hle2]
      exact (floor_cast_sub (cellPath_mono (by simp) c)).symm
    · simp [Vec, ψ1, ht]
  have e2 : lastInc a D' m = ψ2 ∘ (fun (c : ℕ → CellSpace) (j : J) =>
      (cellPath ((a + D'.sup id : ℝ≥0) + j.1 : ℝ) c : ℝ) -
        cellPath ((a + D'.sup id : ℝ≥0) : ℝ) c) := by
    funext c
    simp only [Function.comp_apply, ψ2, lastInc]
    have hcoe : (((a + D'.sup id : ℝ≥0) : ℝ) + ((m - D'.sup id : ℝ≥0) : ℝ)) =
        ((a + m : ℝ≥0) : ℝ) := by
      rw [← NNReal.coe_add]
      congr 1
      rw [add_assoc, add_tsub_cancel_of_le hm']
    rw [hcoe]
    exact (floor_cast_sub (cellPath_mono (by
      exact NNReal.coe_le_coe.mpr (by gcongr)) c)).symm
  have := hind.comp hψ1 hψ2
  rw [← e1, ← e2] at this
  exact this

theorem lastInc_mass (a : ℝ≥0) (D' : Finset ℝ≥0) (m : ℝ≥0)
    (hm : ∀ x ∈ D', x < m) (k : ℕ) :
    cellArrayLaw {c | lastInc a D' m c = k} =
      ENNReal.ofReal (poisTerm k ((m - D'.sup id : ℝ≥0) : ℝ)) := by
  have hm' : D'.sup id ≤ m := Finset.sup_le fun x hx => (hm x hx).le
  have h := cellPath_increment_eq (a + D'.sup id) (m - D'.sup id) k
  have hs : a + D'.sup id + (m - D'.sup id) = a + m := by
    rw [add_assoc, add_tsub_cancel_of_le hm']
  rw [hs] at h
  exact h

theorem lastInc_law (a : ℝ≥0) (D' : Finset ℝ≥0) (m : ℝ≥0)
    (hm : ∀ x ∈ D', x < m) :
    cellArrayLaw.map (lastInc a D' m) = cellArrayLaw.map (lastInc 0 D' m) := by
  apply Measure.ext_of_singleton
  intro k
  rw [Measure.map_apply (measurable_lastInc a D' m) (measurableSet_singleton k),
    Measure.map_apply (measurable_lastInc 0 D' m) (measurableSet_singleton k)]
  have h1 := lastInc_mass a D' m hm k
  have h2 := lastInc_mass 0 D' m hm k
  exact h1.trans h2.symm

theorem Vec_law_insert (a : ℝ≥0) (D' : Finset ℝ≥0) (m : ℝ≥0)
    (hm : ∀ x ∈ D', x < m) :
    cellArrayLaw.map (Vec a (insert m D')) =
      ((cellArrayLaw.map (Vec a D')).prod
        (cellArrayLaw.map (lastInc a D' m))).map (glue m (D'.sup id)) := by
  have hpair : Measurable fun c => (Vec a D' c, lastInc a D' m c) :=
    (measurable_Vec a D').prodMk (measurable_lastInc a D' m)
  have hfun : Vec a (insert m D') =
      glue m (D'.sup id) ∘ (fun c => (Vec a D' c, lastInc a D' m c)) :=
    funext (Vec_insert a D' m hm)
  rw [hfun, ← Measure.map_map (measurable_glue m (D'.sup id)) hpair,
    (indepFun_iff_map_prod_eq_prod_map_map (measurable_Vec a D').aemeasurable
      (measurable_lastInc a D' m).aemeasurable).mp (Vec_lastInc_indep a D' m hm)]

/-- **Stationarity of finite increment vectors.** -/
theorem Vec_stationary (D : Finset ℝ≥0) (a : ℝ≥0) :
    cellArrayLaw.map (Vec a D) = cellArrayLaw.map (Vec 0 D) := by
  induction D using Finset.induction_on_max generalizing a with
  | empty =>
    have h : ∀ b : ℝ≥0, Vec b ∅ = fun _ _ => 0 := by
      intro b
      funext c t
      simp [Vec]
    rw [h a, h 0]
  | insert m D' hm ih =>
    rw [Vec_law_insert a D' m hm, Vec_law_insert 0 D' m hm, ih a,
      lastInc_law a D' m hm]

/-! ### Past/future independence for the whole family -/

section Family

open CellStoppingLineFreshness CellStoppingLineAdapters

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Future processes of all channels after the line `u`. -/
def futProcVec (u : ι → ℝ≥0) (c : CellFamily ι) : ι → ℝ≥0 → ℝ :=
  fun l t => (cellPath ((u l : ℝ) + (t : ℝ)) (c l) : ℝ) - cellPath (u l : ℝ) (c l)

theorem past_future_joint (u : ι → ℝ≥0) :
    (cellFamilyLaw ι).map
        (fun c => (completePast u (flatCellDriver c), futProcVec u c)) =
      ((cellFamilyLaw ι).map (fun c => completePast u (flatCellDriver c))).prod
        ((cellFamilyLaw ι).map (futProcVec u)) := by
  classical
  let past : ι → (ℕ → CellSpace) → (ℝ≥0 → ℝ) := fun l c t =>
    if t ≤ u l then (cellPath (t : ℝ) c : ℝ)
    else (cellPath (u l : ℝ) c : ℝ) + ⌊((t : ℝ) - (u l : ℝ))⌋₊
  let fut : ι → (ℕ → CellSpace) → (ℝ≥0 → ℝ) := fun l c t =>
    (cellPath ((u l : ℝ) + (t : ℝ)) c : ℝ) - cellPath (u l : ℝ) c
  have hpastM : ∀ l, Measurable (past l) := by
    intro l
    apply measurable_pi_lambda
    intro t
    by_cases ht : t ≤ u l
    · simpa [past, ht] using measurable_cellPathR (t : ℝ)
    · simpa [past, ht] using (measurable_cellPathR (u l : ℝ)).add_const _
  have hfutM : ∀ l, Measurable (fut l) := fun l =>
    measurable_pi_lambda _ fun t =>
      (measurable_cellPathR _).sub (measurable_cellPathR _)
  have hindep : ∀ l, IndepFun (past l) (fut l) cellArrayLaw := fun l =>
    indepFun_completePast_shift_one (u l)
  letI (l : ι) : IsProbabilityMeasure (cellArrayLaw.map (past l)) :=
    Measure.isProbabilityMeasure_map (hpastM l).aemeasurable
  letI (l : ι) : IsProbabilityMeasure (cellArrayLaw.map (fut l)) :=
    Measure.isProbabilityMeasure_map (hfutM l).aemeasurable
  have hpair : ∀ l,
      cellArrayLaw.map (fun c => (past l c, fut l c)) =
        (cellArrayLaw.map (past l)).prod (cellArrayLaw.map (fut l)) := fun l =>
    (indepFun_iff_map_prod_eq_prod_map_map (hpastM l).aemeasurable
      (hfutM l).aemeasurable).mp (hindep l)
  let g : CellFamily ι → (ι → (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ)) := fun C l =>
    (past l (C l), fut l (C l))
  let g1 : CellFamily ι → (ι → (ℝ≥0 → ℝ)) := fun C l => past l (C l)
  let g2 : CellFamily ι → (ι → (ℝ≥0 → ℝ)) := fun C l => fut l (C l)
  let Ψ1 : (ι → (ℝ≥0 → ℝ)) → FlatDriver ι := fun w p => w p.1 p.2
  have hΨ1 : Measurable Ψ1 := by
    apply measurable_pi_lambda
    intro p
    exact (measurable_pi_apply p.2).comp (measurable_pi_apply p.1)
  have hflat1 : (fun c => completePast u (flatCellDriver c)) = Ψ1 ∘ g1 := by
    funext C p
    rcases p with ⟨l, t⟩
    simp [completePast, flatCellDriver, Ψ1, g1, past]
  have hflat : (fun c => (completePast u (flatCellDriver c), futProcVec u c)) =
      Prod.map Ψ1 id ∘ (MeasurableEquiv.arrowProdEquivProdArrow
          (ℝ≥0 → ℝ) (ℝ≥0 → ℝ) ι) ∘ g := by
    funext C
    refine Prod.ext ?_ ?_
    · funext p
      rcases p with ⟨l, t⟩
      simp [completePast, flatCellDriver, Ψ1, g, past,
        MeasurableEquiv.arrowProdEquivProdArrow]
    · funext l t
      simp [futProcVec, g, fut, MeasurableEquiv.arrowProdEquivProdArrow]
  have hgM : Measurable g := by
    apply measurable_pi_lambda
    intro l
    exact ((hpastM l).comp (measurable_pi_apply l)).prodMk
      ((hfutM l).comp (measurable_pi_apply l))
  have hg1M : Measurable g1 := by
    apply measurable_pi_lambda
    intro l
    exact (hpastM l).comp (measurable_pi_apply l)
  have hg2M : Measurable g2 := by
    apply measurable_pi_lambda
    intro l
    exact (hfutM l).comp (measurable_pi_apply l)
  have hlawG : (cellFamilyLaw ι).map g =
      Measure.pi (fun l => (cellArrayLaw.map (past l)).prod
        (cellArrayLaw.map (fut l))) := by
    unfold cellFamilyLaw
    rw [Measure.infinitePi_eq_pi]
    have := Measure.pi_map_pi (μ := fun _ : ι => cellArrayLaw)
      (f := fun l c => (past l c, fut l c))
      (fun l => ((hpastM l).prodMk (hfutM l)).aemeasurable)
    simp_rw [hpair] at this
    exact this
  have hlawG1 : (cellFamilyLaw ι).map g1 =
      Measure.pi (fun l => cellArrayLaw.map (past l)) := by
    unfold cellFamilyLaw
    rw [Measure.infinitePi_eq_pi]
    exact Measure.pi_map_pi (μ := fun _ : ι => cellArrayLaw)
      (f := fun l c => past l c) (fun l => (hpastM l).aemeasurable)
  have hlawG2 : (cellFamilyLaw ι).map g2 =
      Measure.pi (fun l => cellArrayLaw.map (fut l)) := by
    unfold cellFamilyLaw
    rw [Measure.infinitePi_eq_pi]
    exact Measure.pi_map_pi (μ := fun _ : ι => cellArrayLaw)
      (f := fun l c => fut l c) (fun l => (hfutM l).aemeasurable)
  have hF : futProcVec u = g2 := rfl
  rw [hflat, hF, hflat1,
    ← Measure.map_map (hΨ1.prodMap measurable_id)
      ((MeasurableEquiv.arrowProdEquivProdArrow (ℝ≥0 → ℝ) (ℝ≥0 → ℝ) ι).measurable.comp hgM),
    ← Measure.map_map (MeasurableEquiv.arrowProdEquivProdArrow
      (ℝ≥0 → ℝ) (ℝ≥0 → ℝ) ι).measurable hgM, hlawG,
    ← Measure.map_map hΨ1 hg1M, hlawG1, hlawG2]
  have hmp := MeasureTheory.measurePreserving_arrowProdEquivProdArrow
    (ℝ≥0 → ℝ) (ℝ≥0 → ℝ) ι (fun l => cellArrayLaw.map (past l))
    (fun l => cellArrayLaw.map (fut l))
  rw [hmp.map_eq, ← Measure.map_prod_map _ _ hΨ1 measurable_id, Measure.map_id]

end Family

/-! ### Cylinder adapter -/

section Cylinder

open CellStoppingLineFreshness CellStoppingLineAdapters

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

/-- Floor readout of a future process at the cylinder delays. -/
def readFut (channel : κ → ι) (delay : κ → ℚ≥0) (f : ι → ℝ≥0 → ℝ) : κ → ℕ :=
  fun j => ⌊f (channel j) ((delay j : ℚ≥0) : ℝ≥0)⌋₊

theorem measurable_readFut (channel : κ → ι) (delay : κ → ℚ≥0) :
    Measurable (readFut channel delay) := by
  apply measurable_pi_lambda
  intro j
  exact Nat.measurable_floor.comp
    ((measurable_pi_apply ((delay j : ℚ≥0) : ℝ≥0)).comp
      (measurable_pi_apply (channel j)))

theorem futureVector_eq_read (u : ι → ℝ≥0) (channel : κ → ι)
    (delay : κ → ℚ≥0) :
    futureVector u channel delay =
      readFut channel delay ∘ futProcVec u := by
  funext c j
  simp only [futureVector, readFut, futProcVec, Function.comp_apply]
  exact (floor_cast_sub (cellPath_mono (by
    have : (0 : ℝ) ≤ (((delay j : ℚ≥0) : ℝ≥0) : ℝ) := NNReal.coe_nonneg _
    linarith) (c (channel j)))).symm

theorem futureVector_stationary (u : ι → ℝ≥0) (channel : κ → ι)
    (delay : κ → ℚ≥0) :
    (cellFamilyLaw ι).map (futureVector u channel delay) =
      (cellFamilyLaw ι).map (futureVector (fun _ => 0) channel delay) := by
  classical
  let D : Finset ℝ≥0 := Finset.univ.image fun j => ((delay j : ℚ≥0) : ℝ≥0)
  let Ψ : (ι → ℝ≥0 → ℕ) → (κ → ℕ) := fun w j =>
    w (channel j) ((delay j : ℚ≥0) : ℝ≥0)
  have hΨ : Measurable Ψ := by
    apply measurable_pi_lambda
    intro j
    exact (measurable_pi_apply _).comp (measurable_pi_apply (channel j))
  have hrep : ∀ v : ι → ℝ≥0, futureVector v channel delay =
      Ψ ∘ (fun (c : CellFamily ι) (l : ι) => Vec (v l) D (c l)) := by
    intro v
    funext c j
    have hj : ((delay j : ℚ≥0) : ℝ≥0) ∈ D := Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
    simp only [futureVector, Function.comp_apply, Ψ, Vec, hj, if_true]
    rw [NNReal.coe_add]
  have hlaw : ∀ v : ι → ℝ≥0,
      (cellFamilyLaw ι).map (fun (c : CellFamily ι) (l : ι) => Vec (v l) D (c l)) =
        Measure.pi (fun l => cellArrayLaw.map (Vec (v l) D)) := by
    intro v
    unfold cellFamilyLaw
    rw [Measure.infinitePi_eq_pi]
    letI (l : ι) : IsProbabilityMeasure (cellArrayLaw.map (Vec (v l) D)) :=
      Measure.isProbabilityMeasure_map (measurable_Vec (v l) D).aemeasurable
    exact Measure.pi_map_pi (μ := fun _ : ι => cellArrayLaw)
      (f := fun l c => Vec (v l) D c) (fun l => (measurable_Vec (v l) D).aemeasurable)
  have hmeas : ∀ v : ι → ℝ≥0,
      Measurable (fun (c : CellFamily ι) (l : ι) => Vec (v l) D (c l)) := by
    intro v
    apply measurable_pi_lambda
    intro l
    exact (measurable_Vec (v l) D).comp (measurable_pi_apply l)
  rw [hrep u, hrep (fun _ => 0), ← Measure.map_map hΨ (hmeas u),
    ← Measure.map_map hΨ (hmeas (fun _ => 0)), hlaw u, hlaw (fun _ => 0)]
  congr 2
  funext l
  exact Vec_stationary D (u l)

/-- **Cylinder adapter.**  The finite-cylinder deterministic renewal interface
holds for the cell family. -/
theorem cylinderFresh (channel : κ → ι) (delay : κ → ℚ≥0) :
    DeterministicFresh (fun u => futureVector u channel delay)
      ((cellFamilyLaw ι).map (futureVector (fun _ => 0) channel delay)) := by
  refine ⟨fun u => measurable_futureVector u channel delay, ?_⟩
  intro u A B hA hB
  let μ := cellFamilyLaw ι
  obtain ⟨A', hA', hAeq⟩ :=
    (MeasurableSpace.measurableSet_comap).1 (cellPast_le_comap u A hA)
  let Φ : CellFamily ι → FlatDriver ι := fun c => completePast u (flatCellDriver c)
  have hΦ : Measurable Φ := (measurable_completePast u).comp measurable_flatCellDriver
  have hFu : Measurable (futProcVec u : CellFamily ι → ι → ℝ≥0 → ℝ) := by
    apply measurable_pi_lambda
    intro l
    apply measurable_pi_lambda
    intro t
    exact ((measurable_cellPathR _).comp (measurable_pi_apply l)).sub
      ((measurable_cellPathR _).comp (measurable_pi_apply l))
  have hread := measurable_readFut channel delay
  have hjoint := past_future_joint u
  have hpairM : Measurable fun c => (Φ c, futProcVec u c) := hΦ.prodMk hFu
  have hset : A ∩ futureVector u channel delay ⁻¹' B =
      (fun c => (Φ c, futProcVec u c)) ⁻¹' (A' ×ˢ (readFut channel delay ⁻¹' B)) := by
    ext c
    rw [futureVector_eq_read]
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_prod, Function.comp_apply]
    rw [← hAeq]
    rfl
  have h1 := congrArg
    (fun ρ : Measure (FlatDriver ι × (ι → ℝ≥0 → ℝ)) =>
      ρ (A' ×ˢ (readFut channel delay ⁻¹' B))) hjoint
  dsimp only at h1
  rw [Measure.map_apply hpairM (hA'.prod (hread hB)), Measure.prod_prod,
    Measure.map_apply hΦ hA', Measure.map_apply hFu (hread hB)] at h1
  have hAmu : μ (Φ ⁻¹' A') = μ A := by rw [← hAeq]
  have hG : μ (futProcVec u ⁻¹' (readFut channel delay ⁻¹' B)) =
      μ.map (futureVector (fun _ => 0) channel delay) B := by
    have := futureVector_stationary u channel delay
    rw [← this, Measure.map_apply (measurable_futureVector u channel delay) hB,
      futureVector_eq_read]
    rfl
  rw [hset]
  calc
    μ ((fun c => (Φ c, futProcVec u c)) ⁻¹' (A' ×ˢ (readFut channel delay ⁻¹' B))) =
        μ (Φ ⁻¹' A') * μ (futProcVec u ⁻¹' (readFut channel delay ⁻¹' B)) := h1
    _ = μ A * (μ.map (futureVector (fun _ => 0) channel delay)) B := by
      rw [hAmu, hG]

/-- Strong memorylessness for finite cylinders with no `DeterministicFresh`
premise left. -/
theorem stoppingLine_futureCylinder_unconditional
    (channel : κ → ι) (delay : κ → ℚ≥0)
    {σ : CellFamily ι → ι → ℝ≥0} (hσ : CellStoppingLine σ)
    (A : Set (CellFamily ι)) (B : Set (κ → ℕ))
    (hA : MeasurableSet[cellStoppedPast σ hσ] A) (hB : MeasurableSet B) :
    cellFamilyLaw ι (A ∩ stoppedFutureVector σ channel delay ⁻¹' B) =
      cellFamilyLaw ι A *
        ((cellFamilyLaw ι).map (futureVector (fun _ => 0) channel delay)) B :=
  stoppingLine_futureCylinder channel delay hσ (cylinderFresh channel delay) A B hA hB

/-- The package `FreshShiftedCountingPathsAt` without any extra premise. -/
theorem freshShiftedCountingPathsAt_unconditional
    {σ : CellFamily ι → ι → ℝ≥0} (hσ : CellStoppingLine σ) :
    FreshShiftedCountingPathsAt σ hσ := by
  refine ⟨?_⟩
  intro κ' _ channel delay _ A B hA hB
  exact stoppingLine_futureCylinder_unconditional channel delay hσ A B hA hB

end Cylinder

end Ripple.Kurtz.StrongApprox.CellStoppingLineCylinders

end
