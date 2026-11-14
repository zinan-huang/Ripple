/-
  Ripple.Kurtz.StrongApprox.PoissonPath — the Poisson representation (PR), part (2a): a unit-rate
  Poisson process as a random counting path, built on a product extension of any probability space
  `(Ω, P)` that carries iid Poisson(1) unit counts `N i` (such as the SIP space): the points of
  cell `i` are the first `N i` entries of an iid uniform position sequence attached to cell `i`.

  The path `poisPath N t x = Σ_{i<⌊t⌋} N i x.1 + #{points of cell ⌊t⌋ at positions ≤ t − ⌊t⌋}`.
  Pointwise (every `x`): `Y(n) = Σ_{i<n} N i` for `n : ℕ` (so the discrete coupling transfers to
  integer times exactly), `Y(t) = 0` for `t ≤ 0`, nondecreasing, integer-valued, right-continuous
  (`poisPath_eventually_right`, `continuousWithinAt_poisPath`), and the cell decomposition
  `poisPath_eq_sum`. Laws under `pathMeasure P = P ⊗ posArray`: independent increments in the
  sense of Mathlib's `HasIndepIncrements` (`hasIndepIncrements_poisPath`), and
  `P{Y(t) − Y(s) = k} = e^{−(t−s)} (t−s)^k/k!` for `0 ≤ s ≤ t` (`pathMeasure_increment_eq`).
  Finitely (or countably) many independent copies: `familyMeasure`, `poisFamily`,
  `iIndepFun_poisFamily`.
-/

import Mathlib
import Ripple.Kurtz.StrongApprox.IndepTools
import Ripple.Kurtz.StrongApprox.UniformThinning

namespace Ripple.Kurtz.StrongApprox

open MeasureTheory ProbabilityTheory Set Finset Filter Topology

/-! ### Positions for every cell, and the extended space -/

/-- One uniform position sequence per cell. -/
abbrev PosArray : Type := ℕ → ℕ → ℝ

/-- iid uniform position sequences, one per cell. -/
noncomputable def posArray : Measure PosArray := Measure.infinitePi (fun _ : ℕ => posSeq)

instance : IsProbabilityMeasure posArray := by
  unfold posArray; infer_instance

theorem posArray_map_eval (i : ℕ) : posArray.map (fun u : PosArray => u i) = posSeq :=
  Measure.infinitePi_map_eval _ i

theorem iIndepFun_posArray : iIndepFun (fun i (u : PosArray) => u i) posArray :=
  iIndepFun_infinitePi (P := fun _ : ℕ => posSeq) (X := fun _ => id) (fun _ => measurable_id)

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The extended space: the base space and the positions. -/
abbrev PathSpace (Ω : Type*) : Type _ := Ω × PosArray

/-- The extended law `P ⊗ posArray`. -/
noncomputable def pathMeasure (P : Measure Ω) : Measure (PathSpace Ω) := P.prod posArray

instance (P : Measure Ω) [IsProbabilityMeasure P] : IsProbabilityMeasure (pathMeasure P) := by
  unfold pathMeasure; infer_instance

/-- The data of cell `i`: its count and its positions. -/
def cellData (N : ℕ → Ω → ℕ) (i : ℕ) (x : PathSpace Ω) : CellSpace := (N i x.1, x.2 i)

theorem measurable_cellData {N : ℕ → Ω → ℕ} (hN : ∀ i, Measurable (N i)) (i : ℕ) :
    Measurable (cellData N i) :=
  ((hN i).comp measurable_fst).prodMk ((measurable_pi_apply i).comp measurable_snd)

/-! ### The counting path -/

/-- The Poisson counting path. -/
noncomputable def poisPath (N : ℕ → Ω → ℕ) (t : ℝ) (x : PathSpace Ω) : ℕ :=
  ∑ i ∈ Finset.range ⌊t⌋₊, N i x.1 + cellHit (Ioc 0 (t - ⌊t⌋₊)) (cellData N ⌊t⌋₊ x)

theorem measurable_poisPath {N : ℕ → Ω → ℕ} (hN : ∀ i, Measurable (N i)) (t : ℝ) :
    Measurable (poisPath N t) :=
  (Finset.measurable_sum _ fun i _ => (hN i).comp measurable_fst).add
    ((measurable_cellHit measurableSet_Ioc).comp (measurable_cellData hN _))

variable (N : ℕ → Ω → ℕ)

/-- **Integer times**: `Y(n) = Σ_{i<n} N i`, pointwise. -/
theorem poisPath_natCast (n : ℕ) (x : PathSpace Ω) : poisPath N n x = ∑ i ∈ Finset.range n, N i x.1 := by
  unfold poisPath cellHit
  rw [Nat.floor_natCast, sub_self, hitCount_Ioc_of_nonpos le_rfl, add_zero]

theorem poisPath_zero (x : PathSpace Ω) : poisPath N 0 x = 0 := by
  have h := poisPath_natCast N 0 x
  rw [Nat.cast_zero] at h
  rw [h]
  simp

theorem poisPath_of_nonpos {t : ℝ} (ht : t ≤ 0) (x : PathSpace Ω) : poisPath N t x = 0 := by
  unfold poisPath cellHit
  rw [Nat.floor_of_nonpos ht]
  simp only [Finset.range_zero, Finset.sum_empty, Nat.cast_zero, sub_zero, zero_add]
  exact hitCount_Ioc_of_nonpos ht _ _

/-- **Cell decomposition**: for `K > t`, `Y(t) = Σ_{i<K} #{points of cell i at positions ≤ t − i}`. -/
theorem poisPath_eq_sum {t : ℝ} {K : ℕ} (hK : t < K) (x : PathSpace Ω) :
    poisPath N t x = ∑ i ∈ Finset.range K, cellHit (Ioc 0 (t - i)) (cellData N i x) := by
  by_cases ht : t < 0
  · rw [poisPath_of_nonpos N ht.le]
    symm
    refine Finset.sum_eq_zero fun i _ => ?_
    exact hitCount_Ioc_of_nonpos (by linarith [(Nat.cast_nonneg i : (0:ℝ) ≤ i)]) _ _
  · push_neg at ht
    unfold poisPath
    set f := ⌊t⌋₊ with hf
    have hfK : f < K := (Nat.floor_lt ht).mpr hK
    have hzero : ∑ i ∈ Finset.Ico (f + 1) K, cellHit (Ioc 0 (t - i)) (cellData N i x) = 0 := by
      refine Finset.sum_eq_zero fun i hi => ?_
      have hi' : f + 1 ≤ i := (Finset.mem_Ico.mp hi).1
      have hle : (f:ℝ) + 1 ≤ i := by exact_mod_cast hi'
      have htf : t < f + 1 := Nat.lt_floor_add_one t
      exact hitCount_Ioc_of_nonpos (by linarith) _ _
    have hsplit : ∑ i ∈ Finset.range K, cellHit (Ioc 0 (t - i)) (cellData N i x) =
        ∑ i ∈ Finset.range f, cellHit (Ioc 0 (t - i)) (cellData N i x) +
          cellHit (Ioc 0 (t - f)) (cellData N f x) := by
      rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le (f + 1)) hfK, hzero,
        add_zero, ← Finset.range_eq_Ico, Finset.sum_range_succ]
    rw [hsplit]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i < f := Finset.mem_range.mp hi
    have hle : (i:ℝ) + 1 ≤ f := by exact_mod_cast hi'
    have hft : (f:ℝ) ≤ t := Nat.floor_le ht
    exact (hitCount_Ioc_of_one_le (by linarith) _ _).symm

/-- **Monotone paths.** -/
theorem poisPath_mono {s t : ℝ} (hst : s ≤ t) (x : PathSpace Ω) :
    poisPath N s x ≤ poisPath N t x := by
  have hK : t < ((⌊t⌋₊ + 1 : ℕ) : ℝ) := by
    push_cast
    exact Nat.lt_floor_add_one t
  rw [poisPath_eq_sum N hK x, poisPath_eq_sum N (hst.trans_lt hK) x]
  exact Finset.sum_le_sum fun i _ => hitCount_Ioc_mono (by linarith) _ _

/-- **Increments** as sums of cell piece counts. -/
theorem poisPath_add_sum {s t : ℝ} (hst : s ≤ t) {K : ℕ} (hK : t < K) (x : PathSpace Ω) :
    poisPath N t x =
      poisPath N s x + ∑ i ∈ Finset.range K, cellHit (Ioc (s - i) (t - i)) (cellData N i x) := by
  rw [poisPath_eq_sum N hK x, poisPath_eq_sum N (hst.trans_lt hK) x, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => hitCount_Ioc_add (by linarith) _ _

theorem poisPath_sub_eq {s t : ℝ} (hst : s ≤ t) {K : ℕ} (hK : t < K) (x : PathSpace Ω) :
    poisPath N t x - poisPath N s x =
      ∑ i ∈ Finset.range K, cellHit (Ioc (s - i) (t - i)) (cellData N i x) := by
  rw [poisPath_add_sum N hst hK x, Nat.add_sub_cancel_left]

theorem poisPath_cast_sub {s t : ℝ} (hst : s ≤ t) (x : PathSpace Ω) :
    ((poisPath N t x - poisPath N s x : ℕ) : ℝ) = (poisPath N t x : ℝ) - poisPath N s x :=
  Nat.cast_sub (poisPath_mono N hst x)

/-- One cell piece count is right-continuous in the right endpoint. -/
theorem cellHit_Ioc_eventually (v : CellSpace) (a b : ℝ) :
    ∀ᶠ b' in 𝓝[≥] b, cellHit (Ioc a b') v = cellHit (Ioc a b) v :=
  hitCount_Ioc_eventually v.1 v.2 a b

/-- **Right-continuity**: the path is constant on a right neighbourhood of every time. -/
theorem poisPath_eventually_right (t : ℝ) (x : PathSpace Ω) :
    ∀ᶠ s in 𝓝[≥] t, poisPath N s x = poisPath N t x := by
  by_cases ht : t < 0
  · have h : ∀ᶠ s in 𝓝[≥] t, s < 0 := (eventually_lt_nhds ht).filter_mono nhdsWithin_le_nhds
    filter_upwards [h] with s hs
    rw [poisPath_of_nonpos N hs.le, poisPath_of_nonpos N ht.le]
  · push_neg at ht
    set f := ⌊t⌋₊ with hf
    have hfloor : ∀ᶠ s in 𝓝[≥] t, ⌊s⌋₊ = f := by
      have h1 : ∀ᶠ s in 𝓝[≥] t, s < (f : ℝ) + 1 :=
        (eventually_lt_nhds (Nat.lt_floor_add_one t)).filter_mono nhdsWithin_le_nhds
      filter_upwards [h1, self_mem_nhdsWithin] with s hs1 hs2
      rw [Nat.floor_eq_iff (ht.trans hs2)]
      exact ⟨(Nat.floor_le ht).trans hs2, hs1⟩
    have hmap : Tendsto (fun s : ℝ => s - f) (𝓝[≥] t) (𝓝[≥] (t - f)) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        (((continuous_sub_right (f:ℝ)).tendsto t).mono_left nhdsWithin_le_nhds)
        (Filter.mem_of_superset self_mem_nhdsWithin fun s (hs : t ≤ s) =>
          (sub_le_sub_right hs _ : t - f ≤ s - f))
    have hcell := hmap.eventually (cellHit_Ioc_eventually (cellData N f x) 0 (t - f))
    filter_upwards [hfloor, hcell] with s hs1 hs2
    unfold poisPath
    rw [← hf, hs1, hs2]

theorem continuousWithinAt_poisPath (t : ℝ) (x : PathSpace Ω) :
    ContinuousWithinAt (fun s => (poisPath N s x : ℝ)) (Ici t) t := by
  have h := poisPath_eventually_right N t x
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [h] with s hs
  rw [hs]

/-! ### Laws -/

variable {N}
variable {P : Measure Ω} [IsProbabilityMeasure P]

theorem map_eq_poisMeasure_of_masses {X : Ω → ℕ} (hX : Measurable X) {l : ℝ}
    (hl : ∀ k, P {ω | X ω = k} = ENNReal.ofReal (poisTerm k l)) : P.map X = poisMeasure l := by
  apply Measure.ext_of_singleton
  intro k
  rw [Measure.map_apply hX (measurableSet_singleton k), poisMeasure_singleton]
  exact hl k

/-- The law of the cell data is `cellLaw`. -/
theorem pathMeasure_map_cellData (hNm : ∀ i, Measurable (N i))
    (hNl : ∀ i k, P {ω | N i ω = k} = ENNReal.ofReal (poisTerm k 1)) (i : ℕ) :
    (pathMeasure P).map (cellData N i) = cellLaw := by
  unfold pathMeasure cellLaw
  rw [← map_eq_poisMeasure_of_masses (hNm i) (hNl i), ← posArray_map_eval i,
    Measure.map_prod_map _ _ (hNm i) (measurable_pi_apply i)]
  congr 1

/-- The cell data of distinct cells are independent. -/
theorem iIndepFun_cellData_path (hNm : ∀ i, Measurable (N i)) (hN : iIndepFun N P) :
    iIndepFun (cellData N) (pathMeasure P) :=
  iIndepFun_prod_pair hN iIndepFun_posArray hNm (fun i => measurable_pi_apply i)

/-- The law of one piece count of one cell. -/
theorem pathMeasure_cellHit_eq (hNm : ∀ i, Measurable (N i))
    (hNl : ∀ i k, P {ω | N i ω = k} = ENNReal.ofReal (poisTerm k 1)) (i : ℕ) {A : Set ℝ}
    (hA : MeasurableSet A) (k : ℕ) :
    pathMeasure P {x | cellHit A (cellData N i x) = k} =
      ENNReal.ofReal (poisTerm k (unifReal A).toReal) := by
  rw [← cellLaw_cellHit_eq hA k, ← pathMeasure_map_cellData hNm hNl i]
  change (pathMeasure P) ((cellData N i) ⁻¹' (cellHit A ⁻¹' {k})) =
    (Measure.map (cellData N i) (pathMeasure P)) (cellHit A ⁻¹' {k})
  rw [Measure.map_apply (measurable_cellData hNm i) (measurable_cellHit hA (measurableSet_singleton k))]

/-- The pieces of cell `i` cut by a grid `t_0 ≤ t_1 ≤ … ≤ t_q`. -/
def gridPiece {q : ℕ} (t : Fin (q + 1) → ℝ) (i : ℕ) (j : Fin q) : Set ℝ :=
  Ioc (t j.castSucc - i) (t j.succ - i)

theorem gridPiece_disjoint {q : ℕ} {t : Fin (q + 1) → ℝ} (ht : Monotone t) (i : ℕ) :
    Pairwise (Function.onFun Disjoint (gridPiece t i)) := by
  have key : ∀ j j' : Fin q, j < j' → Disjoint (gridPiece t i j) (gridPiece t i j') := by
    intro j j' h
    have hle : t j.succ ≤ t j'.castSucc := ht (Fin.succ_le_castSucc_iff.mpr h)
    refine Set.disjoint_left.mpr fun x hx hx' => ?_
    simp only [gridPiece, Set.mem_Ioc] at hx hx'
    linarith [hx.2, hx'.1]
  intro j j' hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact key j j' h
  · exact (key j' j h).symm

/-- The piece counts of all cells along a grid form an independent family. -/
theorem iIndepFun_gridHit (hNm : ∀ i, Measurable (N i)) (hN : iIndepFun N P)
    (hNl : ∀ i k, P {ω | N i ω = k} = ENNReal.ofReal (poisTerm k 1)) {q : ℕ}
    {t : Fin (q + 1) → ℝ} (ht : Monotone t) :
    iIndepFun (fun p : ℕ × Fin q => fun x => cellHit (gridPiece t p.1 p.2) (cellData N p.1 x))
      (pathMeasure P) := by
  refine iIndepFun_cellData (iIndepFun_cellData_path hNm hN) (measurable_cellData hNm)
    (fun p => cellHit (gridPiece t p.1 p.2)) (fun p => measurable_cellHit measurableSet_Ioc) ?_
  intro i
  rw [pathMeasure_map_cellData hNm hNl i]
  exact iIndepFun_cellHit (fun j => gridPiece t i j) (fun j => measurableSet_Ioc)
    (gridPiece_disjoint ht i)

/-- **Independent increments** (Mathlib's `HasIndepIncrements`, `ℕ`-valued). -/
theorem hasIndepIncrements_poisPath (hNm : ∀ i, Measurable (N i)) (hN : iIndepFun N P)
    (hNl : ∀ i k, P {ω | N i ω = k} = ENNReal.ofReal (poisTerm k 1)) :
    HasIndepIncrements (poisPath N) (pathMeasure P) := by
  intro q t ht
  set K : ℕ := ⌊t (Fin.last q)⌋₊ + 1 with hK
  have hKt : ∀ j, t j < K := fun j => by
    calc t j ≤ t (Fin.last q) := ht (Fin.le_last j)
      _ < K := by rw [hK]; push_cast; exact Nat.lt_floor_add_one _
  have hfam := iIndepFun_gridHit hNm hN hNl ht
  have hS : Pairwise (Function.onFun Disjoint
      (fun j : Fin q => (Finset.range K) ×ˢ ({j} : Finset (Fin q)))) := by
    intro j j' hne
    rw [Function.onFun, Finset.disjoint_left]
    rintro ⟨i, j₀⟩ h1 h2
    rw [Finset.mem_product, Finset.mem_singleton] at h1 h2
    exact hne (h1.2.symm.trans h2.2)
  have h := iIndepFun_finsets_comp hfam
    (fun p => (measurable_cellHit measurableSet_Ioc).comp (measurable_cellData hNm p.1))
    (fun j : Fin q => (Finset.range K) ×ˢ ({j} : Finset (Fin q))) hS (fun _ v => ∑ p, v p)
    (fun _ => Finset.measurable_sum _ fun p _ => measurable_pi_apply p)
  have hfun : (fun (j : Fin q) x => poisPath N (t j.succ) x - poisPath N (t j.castSucc) x) =
      fun (j : Fin q) x => ∑ p : ↥((Finset.range K) ×ˢ ({j} : Finset (Fin q))),
        cellHit (gridPiece t (p : ℕ × Fin q).1 (p : ℕ × Fin q).2)
          (cellData N (p : ℕ × Fin q).1 x) := by
    funext j x
    rw [poisPath_sub_eq N (ht (Fin.castSucc_le_succ j)) (hKt j.succ) x,
      Finset.sum_coe_sort ((Finset.range K) ×ˢ ({j} : Finset (Fin q)))
        (fun p : ℕ × Fin q => cellHit (gridPiece t p.1 p.2) (cellData N p.1 x)),
      Finset.sum_product]
    simp only [Finset.sum_singleton]
    rfl
  rw [hfun]
  exact h

/-- **Independent increments**, real-valued path. -/
theorem hasIndepIncrements_poisPath_real (hNm : ∀ i, Measurable (N i)) (hN : iIndepFun N P)
    (hNl : ∀ i k, P {ω | N i ω = k} = ENNReal.ofReal (poisTerm k 1)) :
    HasIndepIncrements (fun t x => (poisPath N t x : ℝ)) (pathMeasure P) := by
  intro q t ht
  have h := (hasIndepIncrements_poisPath hNm hN hNl q t ht).comp (fun _ (n : ℕ) => (n : ℝ))
    (fun _ => measurable_of_countable _)
  have hfun : (fun (j : Fin q) x => (poisPath N (t j.succ) x : ℝ) - poisPath N (t j.castSucc) x) =
      fun j => (fun n : ℕ => (n : ℝ)) ∘ (fun x => poisPath N (t j.succ) x - poisPath N (t j.castSucc) x) := by
    funext j x
    simp only [Function.comp]
    exact (poisPath_cast_sub N (ht (Fin.castSucc_le_succ j)) x).symm
  rw [hfun]
  exact h

/-! ### The law of one increment -/

/-- The clamp of a real number to `[0, 1]`. -/
noncomputable def clamp (y : ℝ) : ℝ := max (min y 1) 0

theorem unifReal_Ioc_toReal_eq {a b : ℝ} (hab : a ≤ b) :
    (unifReal (Ioc a b)).toReal = clamp b - clamp a := by
  rw [unifReal_apply measurableSet_Ioc, Set.Ioc_inter_Ioc, Real.volume_Ioc, ENNReal.toReal_ofReal']
  unfold clamp
  simp only [max_def, min_def]
  split_ifs <;> linarith

theorem sum_clamp_of_le {x : ℝ} {K : ℕ} (hx : (K:ℝ) ≤ x) :
    ∑ i ∈ Finset.range K, clamp (x - i) = K := by
  have hterm : ∀ i ∈ Finset.range K, clamp (x - i) = 1 := by
    intro i hi
    have h1 : (i:ℝ) + 1 ≤ K := by exact_mod_cast Finset.mem_range.mp hi
    unfold clamp
    rw [min_eq_right (by linarith), max_eq_left zero_le_one]
  rw [Finset.sum_congr rfl hterm]
  simp

theorem sum_clamp_eq {x : ℝ} {K : ℕ} (h0 : 0 ≤ x) (hx : x ≤ K) :
    ∑ i ∈ Finset.range K, clamp (x - i) = x := by
  induction K with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, Nat.cast_zero] at hx ⊢
    linarith
  | succ K ih =>
    rw [Finset.sum_range_succ]
    by_cases hK : x ≤ K
    · rw [ih hK]
      unfold clamp
      rw [min_eq_left (by linarith), max_eq_right (by linarith)]
      ring
    · push_neg at hK
      rw [sum_clamp_of_le hK.le]
      push_cast at hx
      unfold clamp
      rw [min_eq_left (by linarith), max_eq_left (by linarith)]
      ring

/-- The lengths of the pieces `(s − i, t − i] ∩ (0, 1]`, `i < K`, add up to `t − s`. -/
theorem sum_piece_length {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) {K : ℕ} (hK : t ≤ K) :
    ∑ i ∈ Finset.range K, (unifReal (Ioc (s - i) (t - i))).toReal = t - s := by
  rw [Finset.sum_congr rfl (fun i _ => unifReal_Ioc_toReal_eq (by linarith)),
    Finset.sum_sub_distrib, sum_clamp_eq (by linarith) hK, sum_clamp_eq hs (hst.trans hK)]

/-- The single-piece counts of all cells are independent. -/
theorem iIndepFun_pieceHit (hNm : ∀ i, Measurable (N i)) (hN : iIndepFun N P)
    (hNl : ∀ i k, P {ω | N i ω = k} = ENNReal.ofReal (poisTerm k 1)) (s t : ℝ) :
    iIndepFun (fun (i : ℕ) x => cellHit (Ioc (s - i) (t - i)) (cellData N i x)) (pathMeasure P) := by
  have h1 := iIndepFun_cellData (iIndepFun_cellData_path hNm hN) (measurable_cellData hNm)
    (fun p : ℕ × Unit => cellHit (Ioc (s - p.1) (t - p.1)))
    (fun p => measurable_cellHit measurableSet_Ioc)
    (fun i => by rw [pathMeasure_map_cellData hNm hNl i]; exact iIndepFun.of_subsingleton)
  exact h1.precomp (g := fun i : ℕ => (i, ())) (fun a b h => (Prod.mk.inj h).1)

/-- **Poisson increments**: `P{Y(t) − Y(s) = k} = e^{−(t−s)} (t−s)^k / k!` for `0 ≤ s ≤ t`. -/
theorem pathMeasure_increment_eq (hNm : ∀ i, Measurable (N i)) (hN : iIndepFun N P)
    (hNl : ∀ i k, P {ω | N i ω = k} = ENNReal.ofReal (poisTerm k 1)) {s t : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) (k : ℕ) :
    pathMeasure P {x | poisPath N t x - poisPath N s x = k} =
      ENNReal.ofReal (poisTerm k (t - s)) := by
  set K : ℕ := ⌊t⌋₊ + 1 with hK
  have hKt : t < K := by rw [hK]; push_cast; exact Nat.lt_floor_add_one t
  have hset : {x : PathSpace Ω | poisPath N t x - poisPath N s x = k} =
      {x | ∑ i ∈ Finset.range K, cellHit (Ioc (s - i) (t - i)) (cellData N i x) = k} := by
    ext x
    simp only [Set.mem_setOf_eq]
    rw [poisPath_sub_eq N hst hKt x]
  rw [hset, poisson_sum_masses (X := fun i x => cellHit (Ioc (s - i) (t - i)) (cellData N i x))
    (fun i => (measurable_cellHit measurableSet_Ioc).comp (measurable_cellData hNm i))
    (iIndepFun_pieceHit hNm hN hNl s t) (lam := fun i => (unifReal (Ioc (s - i) (t - i))).toReal)
    (fun i => ENNReal.toReal_nonneg) (fun i k => pathMeasure_cellHit_eq hNm hNl i measurableSet_Ioc k)
    K k, sum_piece_length hs hst hKt.le]

/-- The law of one value: `Y(t) ~ Poisson(t)` for `t ≥ 0`. -/
theorem pathMeasure_poisPath_eq (hNm : ∀ i, Measurable (N i)) (hN : iIndepFun N P)
    (hNl : ∀ i k, P {ω | N i ω = k} = ENNReal.ofReal (poisTerm k 1)) {t : ℝ} (ht : 0 ≤ t)
    (k : ℕ) :
    pathMeasure P {x | poisPath N t x = k} = ENNReal.ofReal (poisTerm k t) := by
  have h := pathMeasure_increment_eq hNm hN hNl le_rfl ht k
  simp only [poisPath_zero, Nat.sub_zero, sub_zero] at h
  exact h

/-! ### Transfer of almost-sure statements from the base space -/

theorem pathMeasure_map_fst : (pathMeasure P).map Prod.fst = P := by
  unfold pathMeasure
  rw [Measure.map_fst_prod, measure_univ, one_smul]

/-- An almost-sure statement on the base space holds almost surely on the extended space. -/
theorem ae_pathMeasure_of_ae {p : Ω → Prop} (h : ∀ᵐ ω ∂P, p ω) :
    ∀ᵐ x ∂(pathMeasure P), p x.1 := by
  refine ae_of_ae_map measurable_fst.aemeasurable ?_
  rw [pathMeasure_map_fst]
  exact h

/-! ### Independent copies -/

section Family

variable (ι : Type*)

/-- `ι` independent copies of the extended space. -/
noncomputable def familyMeasure (P : Measure Ω) : Measure (ι → PathSpace Ω) :=
  Measure.infinitePi (fun _ : ι => pathMeasure P)

instance : IsProbabilityMeasure (familyMeasure ι P) := by
  unfold familyMeasure; infer_instance

/-- The `l`-th Poisson path of the family. -/
noncomputable abbrev poisFamily (N : ℕ → Ω → ℕ) (l : ι) (t : ℝ) (ω : ι → PathSpace Ω) : ℕ :=
  poisPath N t (ω l)

theorem familyMeasure_map_eval (l : ι) :
    (familyMeasure ι P).map (fun ω => ω l) = pathMeasure P :=
  Measure.infinitePi_map_eval _ l

theorem measurable_pathMap (hNm : ∀ i, Measurable (N i)) :
    Measurable (fun x : PathSpace Ω => fun t : ℝ => poisPath N t x) :=
  measurable_pi_lambda _ fun t => measurable_poisPath hNm t

/-- **The paths of the family are independent** (as random elements of `ℝ → ℕ`). -/
theorem iIndepFun_poisFamily (hNm : ∀ i, Measurable (N i)) :
    iIndepFun (fun l (ω : ι → PathSpace Ω) => fun t => poisFamily ι N l t ω)
      (familyMeasure ι P) :=
  iIndepFun_infinitePi (P := fun _ : ι => pathMeasure P)
    (X := fun _ x => fun t => poisPath N t x) (fun _ => measurable_pathMap hNm)

/-- Events of one path of the family have the single-path law. -/
theorem familyMeasure_eval_preimage (l : ι) {s : Set (PathSpace Ω)} (hs : MeasurableSet s) :
    familyMeasure ι P ((fun ω : ι → PathSpace Ω => ω l) ⁻¹' s) = pathMeasure P s :=
  infinitePi_eval_preimage _ l hs

/-- An almost-sure statement on the extended space holds almost surely for each member. -/
theorem ae_familyMeasure_of_ae (l : ι) {p : PathSpace Ω → Prop}
    (h : ∀ᵐ x ∂(pathMeasure P), p x) : ∀ᵐ ω ∂(familyMeasure ι P), p (ω l) := by
  refine ae_of_ae_map (measurable_pi_apply l).aemeasurable ?_
  rw [familyMeasure_map_eval]
  exact h

/-- Each member has Poisson increments. -/
theorem familyMeasure_increment_eq (hNm : ∀ i, Measurable (N i)) (hN : iIndepFun N P)
    (hNl : ∀ i k, P {ω | N i ω = k} = ENNReal.ofReal (poisTerm k 1)) (l : ι) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) (k : ℕ) :
    familyMeasure ι P {ω | poisFamily ι N l t ω - poisFamily ι N l s ω = k} =
      ENNReal.ofReal (poisTerm k (t - s)) := by
  rw [← pathMeasure_increment_eq hNm hN hNl hs hst k]
  change familyMeasure ι P ((fun ω : ι → PathSpace Ω => ω l) ⁻¹'
      ((fun x => poisPath N t x - poisPath N s x) ⁻¹' {k})) =
    pathMeasure P ((fun x => poisPath N t x - poisPath N s x) ⁻¹' {k})
  exact familyMeasure_eval_preimage ι l
    (((measurable_poisPath hNm t).sub (measurable_poisPath hNm s)) (measurableSet_singleton k))

/-- Independence is preserved under a pushforward: if the family `g j` is independent under
`μ.map φ`, then `g j ∘ φ` is independent under `μ`. -/
theorem iIndepFun_comp_of_map {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {φ : α → β} (hφ : Measurable φ) {κ : Type*} {γ : κ → Type*}
    [∀ j, MeasurableSpace (γ j)] {g : ∀ j, β → γ j} (hg : ∀ j, Measurable (g j))
    (h : iIndepFun g (μ.map φ)) : iIndepFun (fun j a => g j (φ a)) μ := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul] at h ⊢
  intro S sets hsets
  have h1 := h S hsets
  rw [Measure.map_apply hφ (Finset.measurableSet_biInter _ fun j hj => hg j (hsets j hj)),
    Finset.prod_congr rfl (fun j hj => Measure.map_apply hφ (hg j (hsets j hj))),
    Set.preimage_iInter₂] at h1
  exact h1

/-- Each member has independent increments. -/
theorem hasIndepIncrements_poisFamily (hNm : ∀ i, Measurable (N i)) (hN : iIndepFun N P)
    (hNl : ∀ i k, P {ω | N i ω = k} = ENNReal.ofReal (poisTerm k 1)) (l : ι) :
    HasIndepIncrements (poisFamily ι N l) (familyMeasure ι P) := by
  intro q t ht
  have h := hasIndepIncrements_poisPath hNm hN hNl q t ht
  have hmap : (familyMeasure ι P).map (fun ω : ι → PathSpace Ω => ω l) = pathMeasure P :=
    familyMeasure_map_eval ι l
  have hg : ∀ j : Fin q, Measurable (fun x : PathSpace Ω =>
      poisPath N (t j.succ) x - poisPath N (t j.castSucc) x) :=
    fun j => (measurable_poisPath hNm _).sub (measurable_poisPath hNm _)
  have h1 : iIndepFun (fun (j : Fin q) (x : PathSpace Ω) =>
      poisPath N (t j.succ) x - poisPath N (t j.castSucc) x)
      ((familyMeasure ι P).map (fun ω : ι → PathSpace Ω => ω l)) := by
    rw [hmap]; exact h
  have h2 : iIndepFun (fun (j : Fin q) (ω : ι → PathSpace Ω) =>
      poisPath N (t j.succ) (ω l) - poisPath N (t j.castSucc) (ω l)) (familyMeasure ι P) :=
    iIndepFun_comp_of_map (μ := familyMeasure ι P) (φ := fun ω : ι → PathSpace Ω => ω l)
      (measurable_pi_apply l)
      (g := fun (j : Fin q) (x : PathSpace Ω) =>
        poisPath N (t j.succ) x - poisPath N (t j.castSucc) x) hg h1
  exact h2

end Family

end Ripple.Kurtz.StrongApprox
