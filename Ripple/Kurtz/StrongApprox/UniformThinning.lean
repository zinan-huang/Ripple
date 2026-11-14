/-
  Ripple.Kurtz.StrongApprox.UniformThinning — one unit cell of a Poisson process: a Poisson(1)
  count of points placed at iid uniform positions in `(0, 1]`; the numbers of points falling in
  disjoint measurable pieces are independent Poisson variables with means the lengths.

  Objects: the uniform law `unifReal` on `(0, 1]`; `posSeq`, iid uniform positions; `clip`,
  retraction of `ℝ` onto `(0, 1]` (identity on `(0, 1]`, so a.e. invisible, but it makes every
  pointwise identity below exact); `hitCount n u A = #{m < n : clip (u m) ∈ A}`; the cell space
  `CellSpace = ℕ × (ℕ → ℝ)` with `cellLaw = poisMeasure 1 ⊗ posSeq` and `cellHit A (n, u) =
  hitCount n u A`. Headlines: `posSeq_fiber` (multinomial law of the piece counts of `n` uniform
  points), `cellLaw_cellVector` (joint Poisson masses), `iIndepFun_cellHit`,
  `cellLaw_cellHit_eq`.
-/

import Mathlib
import Ripple.Kurtz.StrongApprox.PoissonSplitting

namespace Ripple.Kurtz.StrongApprox

open MeasureTheory ProbabilityTheory Set Finset

/-! ### The uniform law on `(0, 1]` -/

/-- The uniform probability law on `(0, 1]`. -/
noncomputable def unifReal : Measure ℝ := volume.restrict (Ioc (0:ℝ) 1)

theorem unifReal_apply {s : Set ℝ} (hs : MeasurableSet s) : unifReal s = volume (s ∩ Ioc 0 1) :=
  Measure.restrict_apply hs

theorem unifReal_univ : unifReal univ = 1 := by
  rw [unifReal_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Ioc]
  simp

instance : IsProbabilityMeasure unifReal := ⟨unifReal_univ⟩

theorem unifReal_Ioc {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) :
    unifReal (Ioc a b) = ENNReal.ofReal (b - a) := by
  rw [unifReal_apply measurableSet_Ioc, Set.Ioc_inter_Ioc, max_eq_left ha, min_eq_left hb,
    Real.volume_Ioc]

/-- The uniform law of a piece of `(0, 1]`, as a real number. -/
theorem unifReal_Ioc_toReal {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    (unifReal (Ioc a b)).toReal = b - a := by
  rw [unifReal_Ioc ha hb, ENNReal.toReal_ofReal (by linarith)]

/-! ### iid uniform positions -/

/-- iid uniform positions in `(0, 1]`. -/
noncomputable def posSeq : Measure (ℕ → ℝ) := Measure.infinitePi (fun _ : ℕ => unifReal)

instance : IsProbabilityMeasure posSeq := by
  unfold posSeq; infer_instance

/-! ### Clipping to `(0, 1]` -/

/-- Retraction of `ℝ` onto `(0, 1]`: the identity on `(0, 1]`, and `1` elsewhere. -/
noncomputable def clip (x : ℝ) : ℝ := if x ∈ Ioc (0:ℝ) 1 then x else 1

theorem clip_mem (x : ℝ) : clip x ∈ Ioc (0:ℝ) 1 := by
  unfold clip
  split_ifs with h
  · exact h
  · exact ⟨zero_lt_one, le_rfl⟩

theorem clip_pos (x : ℝ) : 0 < clip x := (clip_mem x).1

theorem clip_le_one (x : ℝ) : clip x ≤ 1 := (clip_mem x).2

theorem clip_of_mem {x : ℝ} (hx : x ∈ Ioc (0:ℝ) 1) : clip x = x := by
  unfold clip
  rw [if_pos hx]

theorem measurable_clip : Measurable clip :=
  Measurable.ite measurableSet_Ioc measurable_id measurable_const

theorem unifReal_clip_preimage {A : Set ℝ} (hA : MeasurableSet A) :
    unifReal (clip ⁻¹' A) = unifReal A := by
  rw [unifReal_apply (measurable_clip hA), unifReal_apply hA]
  congr 1
  ext x
  constructor
  · rintro ⟨h1, h2⟩
    rw [Set.mem_preimage, clip_of_mem h2] at h1
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    rw [Set.mem_preimage, clip_of_mem h2]
    exact h1

/-! ### Counting clipped positions in a set -/

/-- Number of the first `n` clipped positions lying in `A`. -/
noncomputable def hitCount (n : ℕ) (u : ℕ → ℝ) (A : Set ℝ) : ℕ :=
  ∑ m ∈ range n, A.indicator (fun _ => (1:ℕ)) (clip (u m))

theorem hitCount_le (n : ℕ) (u : ℕ → ℝ) (A : Set ℝ) : hitCount n u A ≤ n := by
  unfold hitCount
  calc ∑ m ∈ range n, A.indicator (fun _ => (1:ℕ)) (clip (u m))
      ≤ ∑ _m ∈ range n, (1:ℕ) :=
        Finset.sum_le_sum fun m _ => Set.indicator_apply_le' (fun _ => le_rfl) (fun _ => zero_le_one)
    _ = n := by simp

theorem hitCount_mono {A B : Set ℝ} (h : A ⊆ B) (n : ℕ) (u : ℕ → ℝ) :
    hitCount n u A ≤ hitCount n u B :=
  Finset.sum_le_sum fun m _ => Set.indicator_le_indicator_of_subset h (fun _ => zero_le_one) _

theorem hitCount_of_subset {A : Set ℝ} (h : Ioc (0:ℝ) 1 ⊆ A) (n : ℕ) (u : ℕ → ℝ) :
    hitCount n u A = n := by
  unfold hitCount
  rw [Finset.sum_congr rfl (fun m _ => Set.indicator_of_mem (h (clip_mem (u m))) _)]
  simp

theorem hitCount_of_disjoint {A : Set ℝ} (h : Disjoint (Ioc (0:ℝ) 1) A) (n : ℕ) (u : ℕ → ℝ) :
    hitCount n u A = 0 := by
  unfold hitCount
  exact Finset.sum_eq_zero fun m _ =>
    Set.indicator_of_notMem (Set.disjoint_left.mp h (clip_mem (u m))) _

theorem hitCount_union {A B : Set ℝ} (h : Disjoint A B) (n : ℕ) (u : ℕ → ℝ) :
    hitCount n u (A ∪ B) = hitCount n u A + hitCount n u B := by
  unfold hitCount
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun m _ => congrFun (Set.indicator_union_of_disjoint h _) _

/-- Only the part of `A` inside `(0, 1]` matters. -/
theorem hitCount_congr {A B : Set ℝ} (h : A ∩ Ioc 0 1 = B ∩ Ioc 0 1) (n : ℕ) (u : ℕ → ℝ) :
    hitCount n u A = hitCount n u B := by
  unfold hitCount
  refine Finset.sum_congr rfl fun m _ => ?_
  have hx := clip_mem (u m)
  by_cases hA : clip (u m) ∈ A
  · have hB : clip (u m) ∈ B := by
      have h1 : clip (u m) ∈ A ∩ Ioc 0 1 := ⟨hA, hx⟩
      rw [h] at h1
      exact h1.1
    rw [Set.indicator_of_mem hA, Set.indicator_of_mem hB]
  · have hB : clip (u m) ∉ B := by
      intro hB
      have h1 : clip (u m) ∈ B ∩ Ioc 0 1 := ⟨hB, hx⟩
      rw [← h] at h1
      exact hA h1.1
    rw [Set.indicator_of_notMem hA, Set.indicator_of_notMem hB]

theorem hitCount_Ioc_of_nonpos {b : ℝ} (hb : b ≤ 0) (n : ℕ) (u : ℕ → ℝ) :
    hitCount n u (Ioc 0 b) = 0 :=
  hitCount_of_disjoint (Set.disjoint_left.mpr fun x hx hx' => by linarith [hx.1, hx'.2]) n u

theorem hitCount_Ioc_of_one_le {b : ℝ} (hb : 1 ≤ b) (n : ℕ) (u : ℕ → ℝ) :
    hitCount n u (Ioc 0 b) = n :=
  hitCount_of_subset (Set.Ioc_subset_Ioc_right hb) n u

/-- Counts over `(0, t]` split at any `s ≤ t`. -/
theorem hitCount_Ioc_add {s t : ℝ} (hst : s ≤ t) (n : ℕ) (u : ℕ → ℝ) :
    hitCount n u (Ioc 0 t) = hitCount n u (Ioc 0 s) + hitCount n u (Ioc s t) := by
  by_cases hs : 0 ≤ s
  · rw [← Set.Ioc_union_Ioc_eq_Ioc hs hst]
    exact hitCount_union (Set.disjoint_left.mpr fun x hx hx' => (not_lt.mpr hx.2) hx'.1) n u
  · push_neg at hs
    rw [hitCount_Ioc_of_nonpos hs.le, zero_add]
    refine hitCount_congr ?_ n u
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Ioc]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      exact ⟨⟨by linarith, h2⟩, h3, h4⟩
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      exact ⟨⟨h3, h2⟩, h3, h4⟩

theorem hitCount_Ioc_mono {a b b' : ℝ} (h : b ≤ b') (n : ℕ) (u : ℕ → ℝ) :
    hitCount n u (Ioc a b) ≤ hitCount n u (Ioc a b') :=
  hitCount_mono (Set.Ioc_subset_Ioc_right h) n u

/-- Right-continuity of the count in the right endpoint (finitely many points). -/
theorem hitCount_Ioc_eventually (n : ℕ) (u : ℕ → ℝ) (a b : ℝ) :
    ∀ᶠ b' in nhdsWithin b (Ici b), hitCount n u (Ioc a b') = hitCount n u (Ioc a b) := by
  unfold hitCount
  have h : ∀ m ∈ range n, ∀ᶠ b' in nhdsWithin b (Ici b),
      (Ioc a b').indicator (fun _ => (1:ℕ)) (clip (u m)) =
        (Ioc a b).indicator (fun _ => (1:ℕ)) (clip (u m)) := by
    intro m _
    by_cases hb : clip (u m) ≤ b
    · filter_upwards [self_mem_nhdsWithin] with b' hb'
      by_cases ha : a < clip (u m)
      · rw [Set.indicator_of_mem (show clip (u m) ∈ Ioc a b' from ⟨ha, hb.trans hb'⟩),
          Set.indicator_of_mem (show clip (u m) ∈ Ioc a b from ⟨ha, hb⟩)]
      · rw [Set.indicator_of_notMem (show clip (u m) ∉ Ioc a b' from fun hx => ha hx.1),
          Set.indicator_of_notMem (show clip (u m) ∉ Ioc a b from fun hx => ha hx.1)]
    · push_neg at hb
      have hev : ∀ᶠ b' in nhdsWithin b (Ici b), b' < clip (u m) :=
        (eventually_lt_nhds hb).filter_mono nhdsWithin_le_nhds
      filter_upwards [hev] with b' hb'
      rw [Set.indicator_of_notMem (show clip (u m) ∉ Ioc a b' from fun hx => (not_lt.mpr hx.2) hb'),
        Set.indicator_of_notMem (show clip (u m) ∉ Ioc a b from fun hx => (not_lt.mpr hx.2) hb)]
  exact ((Filter.eventually_all_finset (range n)).mpr h).mono fun b' hb' =>
    Finset.sum_congr rfl hb'

theorem measurable_hitCount (n : ℕ) {A : Set ℝ} (hA : MeasurableSet A) :
    Measurable (fun u : ℕ → ℝ => hitCount n u A) :=
  Finset.measurable_sum _ fun m _ =>
    (measurable_const.indicator hA).comp (measurable_clip.comp (measurable_pi_apply m))

/-- Counts over a finite measurable partition of the line add up to `n`. -/
theorem sum_hitCount {Q : ℕ} {A : Fin Q → Set ℝ} (hdisj : Pairwise (Function.onFun Disjoint A))
    (hcov : ∀ x, ∃ j, x ∈ A j) (n : ℕ) (u : ℕ → ℝ) : ∑ j, hitCount n u (A j) = n := by
  unfold hitCount
  rw [Finset.sum_comm]
  have h1 : ∀ m ∈ range n, ∑ j, (A j).indicator (fun _ => (1:ℕ)) (clip (u m)) = 1 := by
    intro m _
    obtain ⟨j₀, hj₀⟩ := hcov (clip (u m))
    rw [Finset.sum_eq_single j₀]
    · exact Set.indicator_of_mem hj₀ _
    · intro j _ hj
      exact Set.indicator_of_notMem (Set.disjoint_right.mp (hdisj hj) hj₀) _
    · intro h
      exact absurd (Finset.mem_univ j₀) h
  rw [Finset.sum_congr rfl h1]
  simp

/-! ### The multinomial law of the piece counts of `n` uniform points -/

/-- **Fibre of the piece-count vector**: for a finite measurable partition `A` of the line and
`n` iid uniform points, `P{∀ j, #{m < n : clip (u m) ∈ A j} = k j} = n!/∏ (k j)! ∏ p_j^{k j}`
when `Σ k = n`, `p_j = unifReal (A j)`. -/
theorem posSeq_fiber {Q n : ℕ} (A : Fin Q → Set ℝ) (hA : ∀ j, MeasurableSet (A j))
    (hdisj : Pairwise (Function.onFun Disjoint A)) (hcov : ∀ x, ∃ j, x ∈ A j) (k : Fin Q → ℕ)
    (hk : ∑ j, k j = n) :
    posSeq {u | ∀ j, hitCount n u (A j) = k j} =
      (Nat.multinomial univ k : ENNReal) * ∏ j, unifReal (A j) ^ k j := by
  classical
  let cyl : (Fin n → Fin Q) → Set (ℕ → ℝ) := fun f =>
    (↑(range n) : Set ℕ).pi (fun m => if h : m < n then clip ⁻¹' A (f ⟨m, h⟩) else univ)
  have hcyl_mem : ∀ f (u : ℕ → ℝ), u ∈ cyl f ↔ ∀ m (h : m < n), clip (u m) ∈ A (f ⟨m, h⟩) := by
    intro f u
    simp only [cyl, Set.mem_pi, Finset.mem_coe, Finset.mem_range]
    constructor
    · intro h m hm
      have := h m hm
      rw [dif_pos hm] at this
      exact this
    · intro h m hm
      rw [dif_pos hm]
      exact h m hm
  have hcyl_meas : ∀ f, MeasurableSet (cyl f) := by
    intro f
    refine MeasurableSet.pi (Finset.countable_toSet _) fun m _ => ?_
    split_ifs
    · exact measurable_clip (hA _)
    · exact MeasurableSet.univ
  have hcyl_measure : ∀ f, posSeq (cyl f) = ∏ j, unifReal (A j) ^ fibCount f j := by
    intro f
    unfold posSeq
    rw [Measure.infinitePi_pi _ (fun m _ => by
      split_ifs
      · exact measurable_clip (hA _)
      · exact MeasurableSet.univ)]
    rw [← Fin.prod_univ_eq_prod_range
      (fun m => unifReal (if h : m < n then clip ⁻¹' A (f ⟨m, h⟩) else univ)) n]
    rw [Finset.prod_congr rfl (fun i _ => by
      rw [dif_pos i.isLt, Fin.eta, unifReal_clip_preimage (hA _)])]
    rw [← Finset.prod_fiberwise_of_maps_to (s := univ) (t := univ) (g := f)
      (fun i _ => Finset.mem_univ _) (fun i => unifReal (A (f i)))]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [Finset.prod_congr rfl (fun i hi => by rw [(Finset.mem_filter.mp hi).2]),
      Finset.prod_const]
    rfl
  have hcount : ∀ f (u : ℕ → ℝ), u ∈ cyl f → ∀ j, hitCount n u (A j) = fibCount f j := by
    intro f u hu j
    rw [hcyl_mem] at hu
    unfold hitCount fibCount
    rw [Finset.card_filter, ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hij : f i = j
    · rw [if_pos hij, Set.indicator_of_mem]
      rw [← hij]
      exact hu i i.isLt
    · rw [if_neg hij, Set.indicator_of_notMem]
      exact Set.disjoint_left.mp (hdisj hij) (hu i i.isLt)
  have hE : {u : ℕ → ℝ | ∀ j, hitCount n u (A j) = k j} = ⋃ f ∈ wordSet n Q k, cyl f := by
    ext u
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
    constructor
    · intro hu
      have hex : ∀ i : Fin n, ∃ j, clip (u i) ∈ A j := fun i => hcov _
      choose f₀ hf₀ using hex
      have hf₀' : u ∈ cyl f₀ := (hcyl_mem f₀ u).mpr fun m h => hf₀ ⟨m, h⟩
      refine ⟨f₀, ?_, hf₀'⟩
      simp only [wordSet, Finset.mem_filter, Finset.mem_univ, true_and]
      intro j
      rw [← hu j, hcount f₀ u hf₀' j]
    · rintro ⟨f, hf, hu⟩
      simp only [wordSet, Finset.mem_filter, Finset.mem_univ, true_and] at hf
      intro j
      rw [hcount f u hu j, hf j]
  have hdisj_cyl : (↑(wordSet n Q k) : Set (Fin n → Fin Q)).PairwiseDisjoint cyl := by
    intro f _ f' _ hne
    refine Set.disjoint_left.mpr fun u hu hu' => hne ?_
    funext i
    by_contra hii
    exact Set.disjoint_left.mp (hdisj hii) ((hcyl_mem f u).mp hu i i.isLt)
      ((hcyl_mem f' u).mp hu' i i.isLt)
  rw [hE, measure_biUnion_finset hdisj_cyl (fun f _ => hcyl_meas f)]
  rw [Finset.sum_congr rfl (fun f hf =>
    (show posSeq (cyl f) = ∏ j, unifReal (A j) ^ k j from by
      rw [hcyl_measure f]
      simp only [wordSet, Finset.mem_filter, Finset.mem_univ, true_and] at hf
      exact Finset.prod_congr rfl fun j _ => by rw [hf j]))]
  rw [Finset.sum_const, nsmul_eq_mul, card_wordSet, if_pos hk]

/-! ### The cell space -/

/-- One unit cell: a point count and a sequence of positions. -/
abbrev CellSpace : Type := ℕ × (ℕ → ℝ)

/-- The cell law: a Poisson(1) count and iid uniform positions. -/
noncomputable def cellLaw : Measure CellSpace := (poisMeasure 1).prod posSeq

instance : IsProbabilityMeasure cellLaw := by
  unfold cellLaw; infer_instance

/-- Number of the cell's points (clipped) in `A`. -/
noncomputable def cellHit (A : Set ℝ) (v : CellSpace) : ℕ := hitCount v.1 v.2 A

theorem cellHit_le (A : Set ℝ) (v : CellSpace) : cellHit A v ≤ v.1 := hitCount_le _ _ _

theorem measurable_cellHit {A : Set ℝ} (hA : MeasurableSet A) : Measurable (cellHit A) := by
  apply measurable_to_countable'
  intro c
  have hset : cellHit A ⁻¹' {c} =
      ⋃ n, ({v : CellSpace | v.1 = n} ∩ {v : CellSpace | hitCount n v.2 A = c}) := by
    ext v
    simp [cellHit]
  rw [hset]
  refine MeasurableSet.iUnion fun n => ?_
  exact (measurable_fst (measurableSet_singleton n)).inter
    (((measurable_hitCount n hA).comp measurable_snd) (measurableSet_singleton c))

theorem poisMeasure_isProbabilityMeasure_of_nonneg {l : ℝ} (hl : 0 ≤ l) :
    IsProbabilityMeasure (poisMeasure l) := by
  haveI : Fact (0 ≤ l) := ⟨hl⟩
  infer_instance

/-- The complement of finitely many pieces. -/
def restSet {q : ℕ} (A : Fin q → Set ℝ) : Set ℝ := (⋃ j, A j)ᶜ

theorem pairwise_disjoint_cons {q : ℕ} {A : Fin q → Set ℝ} {R : Set ℝ}
    (hR : ∀ j, Disjoint R (A j)) (hdisj : Pairwise (Function.onFun Disjoint A)) :
    Pairwise (Function.onFun Disjoint (Fin.cons R A : Fin (q + 1) → Set ℝ)) := by
  intro j j' hne
  induction j using Fin.cases with
  | zero =>
    induction j' using Fin.cases with
    | zero => exact absurd rfl hne
    | succ i =>
      simp only [Function.onFun, Fin.cons_zero, Fin.cons_succ]
      exact hR i
  | succ i =>
    induction j' using Fin.cases with
    | zero =>
      simp only [Function.onFun, Fin.cons_zero, Fin.cons_succ]
      exact (hR i).symm
    | succ i' =>
      simp only [Function.onFun, Fin.cons_succ]
      exact hdisj (fun h => hne (by rw [h]))

/-- The general multinomial–Poisson identity:
`e^{-1}/K! · K!/∏ k_j! · ∏ p_j^{k_j} = ∏ e^{-p_j} p_j^{k_j}/k_j!` when `Σ p_j = 1`, `Σ k_j = K`. -/
theorem poisTerm_mul_multinomial_general {Q K : ℕ} {p : Fin Q → ℝ} (hp : ∀ j, 0 ≤ p j)
    (hsum : ∑ j, p j = 1) (k : Fin Q → ℕ) (hK : ∑ j, k j = K) :
    poisTerm K 1 * ((Nat.multinomial univ k : ℝ) * ∏ j, p j ^ k j) =
      ∏ j, poisTerm (k j) (p j) := by
  have hspec : (∏ j, ((k j).factorial : ℝ)) * (Nat.multinomial univ k : ℝ) =
      (K.factorial : ℝ) := by
    rw [← hK]
    exact_mod_cast Nat.multinomial_spec univ k
  have hprodf : (0:ℝ) < ∏ j, ((k j).factorial : ℝ) :=
    Finset.prod_pos (fun j _ => by exact_mod_cast Nat.factorial_pos _)
  have hM : (Nat.multinomial univ k : ℝ) = (K.factorial : ℝ) / ∏ j, ((k j).factorial : ℝ) := by
    rw [eq_div_iff hprodf.ne', mul_comm]
    exact hspec
  have hexp : ∏ j, Real.exp (-p j) = Real.exp (-1) := by
    rw [← Real.exp_sum, Finset.sum_neg_distrib, hsum]
  unfold poisTerm
  simp only [one_pow, mul_one]
  rw [Finset.prod_div_distrib, Finset.prod_mul_distrib, hexp, hM]
  have hKf : (0:ℝ) < K.factorial := by exact_mod_cast Nat.factorial_pos K
  field_simp

/-! ### The pieces with the rest, their probabilities, and the sliced event -/

section Thinning

variable {q : ℕ}

/-- The pieces `A j` together with the rest `(⋃ A)ᶜ` at index `0`. -/
def consRest (A : Fin q → Set ℝ) : Fin (q + 1) → Set ℝ := Fin.cons (restSet A) A

theorem consRest_zero (A : Fin q → Set ℝ) : consRest A 0 = restSet A := Fin.cons_zero _ _

theorem consRest_succ (A : Fin q → Set ℝ) (j : Fin q) : consRest A j.succ = A j :=
  Fin.cons_succ _ _ _

theorem consRest_measurableSet {A : Fin q → Set ℝ} (hA : ∀ j, MeasurableSet (A j))
    (j : Fin (q + 1)) : MeasurableSet (consRest A j) := by
  induction j using Fin.cases with
  | zero =>
    rw [consRest_zero]
    exact (MeasurableSet.iUnion hA).compl
  | succ i =>
    rw [consRest_succ]
    exact hA i

theorem consRest_disjoint {A : Fin q → Set ℝ} (hdisj : Pairwise (Function.onFun Disjoint A)) :
    Pairwise (Function.onFun Disjoint (consRest A)) :=
  pairwise_disjoint_cons
    (fun j => Set.disjoint_compl_left_iff_subset.mpr (Set.subset_iUnion A j)) hdisj

theorem consRest_cover (A : Fin q → Set ℝ) (x : ℝ) : ∃ j, x ∈ consRest A j := by
  by_cases hx : x ∈ ⋃ j, A j
  · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    exact ⟨i.succ, by rw [consRest_succ]; exact hi⟩
  · exact ⟨0, by rw [consRest_zero]; exact hx⟩

/-- The probability of each piece (the rest at index `0`). -/
noncomputable def pieceProb (A : Fin q → Set ℝ) (j : Fin (q + 1)) : ℝ :=
  (unifReal (consRest A j)).toReal

theorem pieceProb_nonneg (A : Fin q → Set ℝ) (j : Fin (q + 1)) : 0 ≤ pieceProb A j :=
  ENNReal.toReal_nonneg

theorem unifReal_consRest (A : Fin q → Set ℝ) (j : Fin (q + 1)) :
    unifReal (consRest A j) = ENNReal.ofReal (pieceProb A j) :=
  (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm

theorem pieceProb_succ (A : Fin q → Set ℝ) (j : Fin q) :
    pieceProb A j.succ = (unifReal (A j)).toReal := by
  unfold pieceProb
  rw [consRest_succ]

theorem pieceProb_sum {A : Fin q → Set ℝ} (hA : ∀ j, MeasurableSet (A j))
    (hdisj : Pairwise (Function.onFun Disjoint A)) : ∑ j, pieceProb A j = 1 := by
  have h := measure_iUnion (μ := unifReal) (consRest_disjoint hdisj) (consRest_measurableSet hA)
  rw [tsum_fintype, show (⋃ j, consRest A j) = Set.univ from
    Set.eq_univ_of_forall (fun x => Set.mem_iUnion.mpr (consRest_cover A x)), unifReal_univ] at h
  have h' := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_one, ENNReal.toReal_sum (fun j _ => measure_ne_top _ _)] at h'
  exact h'.symm

/-- The count vector with `r` points in the rest. -/
def consCount (r : ℕ) (k : Fin q → ℕ) : Fin (q + 1) → ℕ := Fin.cons r k

theorem consCount_zero (r : ℕ) (k : Fin q → ℕ) : consCount r k 0 = r := Fin.cons_zero _ _

theorem consCount_succ (r : ℕ) (k : Fin q → ℕ) (j : Fin q) : consCount r k j.succ = k j :=
  Fin.cons_succ _ _ _

theorem sum_consCount (r : ℕ) (k : Fin q → ℕ) : ∑ j, consCount r k j = ∑ j, k j + r := by
  rw [Fin.sum_univ_succ, consCount_zero]
  simp only [consCount_succ]
  ring

/-- The slice of the cell event with `r` points in the rest. -/
def cellSlice (A : Fin q → Set ℝ) (k : Fin q → ℕ) (r : ℕ) : Set CellSpace :=
  {n : ℕ | n = ∑ j, k j + r} ×ˢ
    {u : ℕ → ℝ | ∀ j, hitCount (∑ j, k j + r) u (consRest A j) = consCount r k j}

/-- The cell event is the disjoint union of its slices. -/
theorem cellVector_eq_iUnion {A : Fin q → Set ℝ} (hdisj : Pairwise (Function.onFun Disjoint A))
    (k : Fin q → ℕ) :
    {v : CellSpace | ∀ j, cellHit (A j) v = k j} = ⋃ r : ℕ, cellSlice A k r := by
  ext ⟨n, u⟩
  simp only [Set.mem_setOf_eq, Set.mem_iUnion, cellSlice, Set.mem_prod, cellHit]
  constructor
  · intro h
    have hsum := sum_hitCount (consRest_disjoint hdisj) (consRest_cover A) n u
    rw [Fin.sum_univ_succ, consRest_zero] at hsum
    simp only [consRest_succ, h] at hsum
    refine ⟨hitCount n u (restSet A), by omega, ?_⟩
    intro j
    rw [show ∑ j, k j + hitCount n u (restSet A) = n by omega]
    induction j using Fin.cases with
    | zero => rw [consRest_zero, consCount_zero]
    | succ i =>
      rw [consRest_succ, consCount_succ]
      exact h i
  · rintro ⟨r, hn, h⟩ j
    have := h j.succ
    rw [← hn, consRest_succ, consCount_succ] at this
    exact this

theorem measurableSet_cellSlice {A : Fin q → Set ℝ} (hA : ∀ j, MeasurableSet (A j))
    (k : Fin q → ℕ) (r : ℕ) : MeasurableSet (cellSlice A k r) := by
  refine MeasurableSet.prod MeasurableSet.of_discrete ?_
  rw [Set.setOf_forall]
  exact MeasurableSet.iInter fun j =>
    measurable_hitCount _ (consRest_measurableSet hA j) (measurableSet_singleton _)

theorem cellSlice_disjoint (A : Fin q → Set ℝ) (k : Fin q → ℕ) :
    Pairwise (Function.onFun Disjoint (cellSlice A k)) := by
  intro r r' hne
  refine Set.disjoint_left.mpr ?_
  rintro ⟨n, u⟩ ⟨hn, _⟩ ⟨hn', _⟩
  simp only [Set.mem_setOf_eq] at hn hn'
  omega

/-- The law of one slice. -/
theorem cellLaw_cellSlice {A : Fin q → Set ℝ} (hA : ∀ j, MeasurableSet (A j))
    (hdisj : Pairwise (Function.onFun Disjoint A)) (k : Fin q → ℕ) (r : ℕ) :
    cellLaw (cellSlice A k r) =
      ENNReal.ofReal (poisTerm r (pieceProb A 0) * ∏ j, poisTerm (k j) (pieceProb A j.succ)) := by
  unfold cellLaw cellSlice
  rw [Measure.prod_prod, Set.setOf_eq_eq_singleton, poisMeasure_singleton,
    posSeq_fiber (consRest A) (consRest_measurableSet hA) (consRest_disjoint hdisj)
      (consRest_cover A) (consCount r k) (sum_consCount r k)]
  have hreal : poisTerm (∑ j, k j + r) 1 *
      ((Nat.multinomial univ (consCount r k) : ℝ) * ∏ j, pieceProb A j ^ consCount r k j) =
      poisTerm r (pieceProb A 0) * ∏ j, poisTerm (k j) (pieceProb A j.succ) := by
    rw [poisTerm_mul_multinomial_general (pieceProb_nonneg A) (pieceProb_sum hA hdisj)
      (consCount r k) (sum_consCount r k), Fin.prod_univ_succ, consCount_zero]
    simp only [consCount_succ]
  rw [Finset.prod_congr rfl (fun j _ => by
      rw [unifReal_consRest A j, ← ENNReal.ofReal_pow (pieceProb_nonneg A j)]),
    ← ENNReal.ofReal_prod_of_nonneg (fun j _ => pow_nonneg (pieceProb_nonneg A j) _),
    ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
    ← ENNReal.ofReal_mul (poisTerm_nonneg _ zero_le_one), hreal]

/-- The series over the number of points in the rest. -/
theorem tsum_cell_terms (A : Fin q → Set ℝ) (k : Fin q → ℕ) :
    ∑' r : ℕ, ENNReal.ofReal (poisTerm r (pieceProb A 0) *
      ∏ j, poisTerm (k j) (pieceProb A j.succ)) =
      ∏ j, ENNReal.ofReal (poisTerm (k j) (unifReal (A j)).toReal) := by
  have hp0 : 0 ≤ pieceProb A 0 := pieceProb_nonneg A 0
  have hC0 : 0 ≤ ∏ j, poisTerm (k j) (pieceProb A j.succ) :=
    Finset.prod_nonneg fun j _ => poisTerm_nonneg _ (pieceProb_nonneg A _)
  have hsum : HasSum (fun r : ℕ => poisTerm r (pieceProb A 0) *
      ∏ j, poisTerm (k j) (pieceProb A j.succ)) (1 * ∏ j, poisTerm (k j) (pieceProb A j.succ)) :=
    (hasSum_poisTerm hp0).mul_right _
  have h1 : ∀ r : ℕ, 0 ≤ poisTerm r (pieceProb A 0) * ∏ j, poisTerm (k j) (pieceProb A j.succ) :=
    fun r => mul_nonneg (poisTerm_nonneg _ hp0) hC0
  rw [← ENNReal.ofReal_tsum_of_nonneg h1 hsum.summable, hsum.tsum_eq, one_mul,
    ENNReal.ofReal_prod_of_nonneg (fun j _ => poisTerm_nonneg _ (pieceProb_nonneg A _))]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [pieceProb_succ]

/-- **Thinning of one cell**: the numbers of the cell's points in pairwise disjoint measurable
pieces `A j` are independent Poisson variables with means `unifReal (A j)` (joint masses). -/
theorem cellLaw_cellVector (A : Fin q → Set ℝ) (hA : ∀ j, MeasurableSet (A j))
    (hdisj : Pairwise (Function.onFun Disjoint A)) (k : Fin q → ℕ) :
    cellLaw {v | ∀ j, cellHit (A j) v = k j} =
      ∏ j, ENNReal.ofReal (poisTerm (k j) (unifReal (A j)).toReal) := by
  rw [cellVector_eq_iUnion hdisj k, measure_iUnion (cellSlice_disjoint A k)
    (measurableSet_cellSlice hA k)]
  rw [tsum_congr (fun r => cellLaw_cellSlice hA hdisj k r)]
  exact tsum_cell_terms A k

end Thinning

theorem measurable_cellHitVector {q : ℕ} {A : Fin q → Set ℝ} (hA : ∀ j, MeasurableSet (A j)) :
    Measurable (fun v : CellSpace => fun j => cellHit (A j) v) :=
  measurable_pi_lambda _ fun j => measurable_cellHit (hA j)

/-- The law of the piece-count vector is the product of Poisson laws. -/
theorem cellLaw_map_cellVector {q : ℕ} (A : Fin q → Set ℝ) (hA : ∀ j, MeasurableSet (A j))
    (hdisj : Pairwise (Function.onFun Disjoint A)) :
    cellLaw.map (fun v : CellSpace => fun j => cellHit (A j) v) =
      Measure.pi (fun j => poisMeasure (unifReal (A j)).toReal) := by
  haveI : ∀ j, IsProbabilityMeasure (poisMeasure (unifReal (A j)).toReal) := fun j =>
    poisMeasure_isProbabilityMeasure_of_nonneg ENNReal.toReal_nonneg
  apply Measure.ext_of_singleton
  intro k
  rw [Measure.map_apply (measurable_cellHitVector hA) (measurableSet_singleton k),
    Measure.pi_singleton]
  have hset : (fun v : CellSpace => fun j => cellHit (A j) v) ⁻¹' {k} =
      {v | ∀ j, cellHit (A j) v = k j} := by
    ext v
    simp [funext_iff]
  rw [hset, cellLaw_cellVector A hA hdisj k]
  exact Finset.prod_congr rfl fun j _ => (poisMeasure_singleton _ (k j)).symm

theorem cellLaw_map_cellHit {q : ℕ} (A : Fin q → Set ℝ) (hA : ∀ j, MeasurableSet (A j))
    (hdisj : Pairwise (Function.onFun Disjoint A)) (j : Fin q) :
    cellLaw.map (cellHit (A j)) = poisMeasure (unifReal (A j)).toReal := by
  haveI : ∀ j, IsProbabilityMeasure (poisMeasure (unifReal (A j)).toReal) := fun j =>
    poisMeasure_isProbabilityMeasure_of_nonneg ENNReal.toReal_nonneg
  have h1 : cellLaw.map (cellHit (A j)) =
      (cellLaw.map (fun v : CellSpace => fun j => cellHit (A j) v)).map (Function.eval j) := by
    rw [Measure.map_map (measurable_pi_apply j) (measurable_cellHitVector hA)]
    rfl
  rw [h1, cellLaw_map_cellVector A hA hdisj, Measure.pi_map_eval]
  simp

/-- **The piece counts of one cell are independent.** -/
theorem iIndepFun_cellHit {q : ℕ} (A : Fin q → Set ℝ) (hA : ∀ j, MeasurableSet (A j))
    (hdisj : Pairwise (Function.onFun Disjoint A)) :
    iIndepFun (fun j => cellHit (A j)) cellLaw := by
  rw [iIndepFun_iff_map_fun_eq_pi_map (fun j => (measurable_cellHit (hA j)).aemeasurable)]
  rw [cellLaw_map_cellVector A hA hdisj]
  congr 1
  funext j
  exact (cellLaw_map_cellHit A hA hdisj j).symm

/-- `P{#points in A = k} = e^{-p} p^k/k!`, `p = unifReal A`. -/
theorem cellLaw_cellHit_eq {A : Set ℝ} (hA : MeasurableSet A) (k : ℕ) :
    cellLaw {v | cellHit A v = k} = ENNReal.ofReal (poisTerm k (unifReal A).toReal) := by
  have h := cellLaw_cellVector (fun _ : Fin 1 => A) (fun _ => hA) Subsingleton.pairwise
    (fun _ => k)
  rw [Fin.prod_univ_one] at h
  rw [← h]
  congr 1
  ext v
  simp

end Ripple.Kurtz.StrongApprox
