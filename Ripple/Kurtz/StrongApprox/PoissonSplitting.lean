/-
  Ripple.Kurtz.StrongApprox.PoissonSplitting — one coarse block: iid Gaussian cells, the Poisson
  block count obtained by quantile coupling of the standardized block sum, and the split of the
  block count into iid Poisson(1) unit-cell counts by uniform placement.

  Block space `BlockSpace = (ℕ → ℝ) × (ℕ → ℕ)` with `blockMeasure L = gaussSeq.prod (coinSeq L)`:
  the first factor carries iid `N(0,1)` cells `x.1 m`, the second iid uniform coins on
  `{0, …, L−1}`. The block count is `Q = poisCoupling L (Σ_{m<L} x.1 m / √L)`, hence Poisson(L)
  and coupled to the Gaussian block sum with `E(Q − L − Σ Z) = 0`, `E(Q − L − Σ Z)² ≤ 17`; the
  cell counts `N_p = #{m < Q : coin m % L = p}` are iid Poisson(1) with `Σ_{p<L} N_p = Q`.
-/

import Mathlib
import Ripple.Kurtz.StrongApprox.BlockIid
import Ripple.Kurtz.StrongApprox.WordCount
import Ripple.Kurtz.StrongApprox.GaussianBlockSum
import Ripple.Kurtz.StrongApprox.PoissonCouplingMean

namespace Ripple.Kurtz.StrongApprox

open MeasureTheory ProbabilityTheory Set Finset

/-! ### The uniform law on `{0, …, L−1}` and the coin sequence -/

/-- The uniform probability law on `{0, …, L−1} ⊆ ℕ`. -/
noncomputable def unifNat (L : ℕ) : Measure ℕ :=
  (L : ENNReal)⁻¹ • Measure.count.restrict (Set.Iio L)

theorem unifNat_singleton (L c : ℕ) :
    unifNat L {c} = if c < L then (L : ENNReal)⁻¹ else 0 := by
  unfold unifNat
  rw [Measure.smul_apply, Measure.restrict_apply (measurableSet_singleton c), smul_eq_mul]
  by_cases h : c < L
  · rw [if_pos h, Set.inter_eq_left.mpr (by simpa using h), Measure.count_singleton, mul_one]
  · rw [if_neg h, Set.singleton_inter_eq_empty.mpr (by simpa using h), measure_empty, mul_zero]

theorem unifNat_univ (L : ℕ) (hL : 0 < L) : unifNat L univ = 1 := by
  unfold unifNat
  rw [Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, smul_eq_mul,
    ← Finset.coe_range, Measure.count_apply_finset, Finset.card_range]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast hL.ne') (ENNReal.natCast_ne_top L)

instance (L : ℕ) [NeZero L] : IsProbabilityMeasure (unifNat L) :=
  ⟨unifNat_univ L (Nat.pos_of_ne_zero (NeZero.ne L))⟩

theorem unifNat_Ici (L : ℕ) : unifNat L (Set.Ici L) = 0 := by
  unfold unifNat
  rw [Measure.smul_apply, Measure.restrict_apply measurableSet_Ici, Set.Ici_inter_Iio,
    Set.Ico_self, measure_empty, smul_zero]

/-- iid uniform coins. -/
noncomputable def coinSeq (L : ℕ) : Measure (ℕ → ℕ) :=
  Measure.infinitePi (fun _ : ℕ => unifNat L)

instance (L : ℕ) [NeZero L] : IsProbabilityMeasure (coinSeq L) := by
  unfold coinSeq; infer_instance

/-! ### The block space -/

/-- One block: Gaussian cells and coins. -/
abbrev BlockSpace : Type := (ℕ → ℝ) × (ℕ → ℕ)

/-- The block law. -/
noncomputable def blockMeasure (L : ℕ) : Measure BlockSpace := gaussSeq.prod (coinSeq L)

instance (L : ℕ) [NeZero L] : IsProbabilityMeasure (blockMeasure L) := by
  unfold blockMeasure; infer_instance

/-- The Gaussian block sum `Σ_{m<L} Z_m`. -/
noncomputable def gaussSum (L : ℕ) (x : BlockSpace) : ℝ := ∑ m ∈ range L, x.1 m

/-- The standardized block Gaussian `Σ_{m<L} Z_m / √L`. -/
noncomputable def blockGauss (L : ℕ) (x : BlockSpace) : ℝ := gaussSum L x / Real.sqrt L

/-- The Poisson(L) block count, quantile-coupled to the block Gaussian. -/
noncomputable def blockCount (L : ℕ) (x : BlockSpace) : ℕ := poisCoupling L (blockGauss L x)

/-- Number of the first `q` coins (reduced mod `L`) equal to `p`. -/
def coinCount (L q : ℕ) (c : ℕ → ℕ) (p : ℕ) : ℕ :=
  ((range q).filter (fun m => c m % L = p)).card

/-- The unit-cell count of cell `p`. -/
noncomputable def cellCount (L p : ℕ) (x : BlockSpace) : ℕ := coinCount L (blockCount L x) x.2 p

/-- The block discrepancy `Q − L − Σ Z`. -/
noncomputable def blockErr (L : ℕ) (x : BlockSpace) : ℝ :=
  (blockCount L x : ℝ) - L - gaussSum L x

theorem measurable_blockGaussSum (L : ℕ) : Measurable (gaussSum L) :=
  Finset.measurable_sum _ (fun m _ => (measurable_pi_apply m).comp measurable_fst)

theorem measurable_blockGauss (L : ℕ) : Measurable (blockGauss L) := by
  unfold blockGauss
  exact (measurable_blockGaussSum L).div_const _

theorem measurable_blockCount {L : ℕ} (hL : 0 < L) : Measurable (blockCount L) :=
  (measurable_poisCoupling (by exact_mod_cast hL)).comp (measurable_blockGauss L)

theorem measurable_coinCount (L q p : ℕ) : Measurable (fun c : ℕ → ℕ => coinCount L q c p) := by
  unfold coinCount
  simp_rw [Finset.card_filter]
  refine Finset.measurable_sum _ fun m _ => Measurable.ite ?_ measurable_const measurable_const
  exact ((measurable_of_countable (fun n : ℕ => n % L)).comp (measurable_pi_apply m))
    (measurableSet_singleton p)

theorem measurable_cellCount {L : ℕ} (hL : 0 < L) (p : ℕ) : Measurable (cellCount L p) := by
  apply measurable_to_countable'
  intro n
  have hset : cellCount L p ⁻¹' {n} =
      ⋃ q, ({x | blockCount L x = q} ∩ {x : BlockSpace | coinCount L q x.2 p = n}) := by
    ext x
    simp [cellCount]
  rw [hset]
  refine MeasurableSet.iUnion fun q => ?_
  exact (measurable_blockCount hL (measurableSet_singleton q)).inter
    (((measurable_coinCount L q p).comp measurable_snd) (measurableSet_singleton n))

theorem measurable_blockErr {L : ℕ} (hL : 0 < L) : Measurable (blockErr L) := by
  unfold blockErr
  have h1 : Measurable (fun x : BlockSpace => (blockCount L x : ℝ)) :=
    (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp (measurable_blockCount hL)
  exact (h1.sub measurable_const).sub (measurable_blockGaussSum L)

/-! ### Gaussian cells and the block count -/

theorem blockMeasure_map_fst_eval (L : ℕ) [NeZero L] (m : ℕ) :
    (blockMeasure L).map (fun x : BlockSpace => x.1 m) = gaussianReal 0 1 := by
  unfold blockMeasure
  rw [map_comp_fst gaussSeq (coinSeq L) (measurable_pi_apply m), gaussSeq_map_eval]

theorem iIndepFun_blockMeasure_fst (L : ℕ) [NeZero L] :
    iIndepFun (fun m (x : BlockSpace) => x.1 m) (blockMeasure L) :=
  iIndepFun_comp_fst (coinSeq L) iIndepFun_gaussSeq

theorem blockMeasure_map_blockGauss (L : ℕ) [NeZero L] :
    (blockMeasure L).map (blockGauss L) = gaussianReal 0 1 := by
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  unfold blockMeasure blockGauss gaussSum
  rw [map_comp_fst gaussSeq (coinSeq L) (by fun_prop : Measurable
    (fun y : ℕ → ℝ => (∑ m ∈ range L, y m) / Real.sqrt L))]
  exact gaussSeq_map_sum_div_sqrt hL

/-- The block count is Poisson(L). -/
theorem blockMeasure_blockCount_eq (L : ℕ) [NeZero L] (k : ℕ) :
    blockMeasure L {x | blockCount L x = k} = ENNReal.ofReal (poisTerm k L) :=
  measure_poisCoupling_eq (blockMeasure L) (measurable_blockGauss L)
    (blockMeasure_map_blockGauss L) (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)) k

theorem gaussSeq_blockCount_eq {L : ℕ} (hL : 0 < L) (k : ℕ) :
    gaussSeq {y : ℕ → ℝ | poisCoupling L ((∑ m ∈ range L, y m) / Real.sqrt L) = k} =
      ENNReal.ofReal (poisTerm k L) :=
  measure_poisCoupling_eq gaussSeq (by fun_prop) (gaussSeq_map_sum_div_sqrt hL)
    (by exact_mod_cast hL) k

/-! ### (W1) on the block -/

theorem blockErr_eq (L : ℕ) (hL : 0 < L) (x : BlockSpace) :
    blockErr L x = (poisCoupling L (blockGauss L x) : ℝ) - L - Real.sqrt L * blockGauss L x := by
  unfold blockErr blockCount blockGauss
  have : (0:ℝ) < Real.sqrt L := Real.sqrt_pos.mpr (by exact_mod_cast hL)
  rw [mul_div_cancel₀ _ this.ne']

theorem integral_blockErr (L : ℕ) [NeZero L] : ∫ x, blockErr L x ∂(blockMeasure L) = 0 := by
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  simp_rw [blockErr_eq L hL]
  exact integral_poisCoupling_error (blockMeasure L) (measurable_blockGauss L)
    (blockMeasure_map_blockGauss L) (by exact_mod_cast hL)

theorem integral_blockErr_sq_le (L : ℕ) [NeZero L] :
    ∫ x, blockErr L x ^ 2 ∂(blockMeasure L) ≤ 17 := by
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  simp_rw [blockErr_eq L hL]
  exact integral_poisCoupling_error_sq_le (blockMeasure L) (measurable_blockGauss L)
    (blockMeasure_map_blockGauss L) (by exact_mod_cast hL)

theorem abs_blockErr_le (L : ℕ) (hL : 0 < L) (x : BlockSpace) :
    |blockErr L x| ≤ 1 + 2 * blockGauss L x ^ 2 := by
  rw [blockErr_eq L hL]
  exact abs_poisCoupling_sub_le (by exact_mod_cast hL) _

theorem memLp_blockErr (L : ℕ) [NeZero L] : MemLp (blockErr L) 2 (blockMeasure L) := by
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hZ := measurable_blockGauss L
  have hlaw := blockMeasure_map_blockGauss L
  have hg : Integrable (fun x => (1 + 2 * blockGauss L x ^ 2) ^ 2) (blockMeasure L) := by
    have hfun : (fun x => (1 + 2 * blockGauss L x ^ 2) ^ 2) =
        fun x => (1 + 4 * blockGauss L x ^ 2) + 4 * blockGauss L x ^ 4 := by
      funext x; ring
    rw [hfun]
    refine ((integrable_const 1).add ?_).add ?_
    · exact (integrable_pow_of_gaussian hZ hlaw 2).const_mul 4
    · exact (integrable_pow_of_gaussian hZ hlaw 4).const_mul 4
  rw [memLp_two_iff_integrable_sq (measurable_blockErr hL).aestronglyMeasurable]
  refine hg.mono' ((measurable_blockErr hL).pow_const 2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) (abs_blockErr_le L hL x) 2

theorem integrable_blockErr (L : ℕ) [NeZero L] : Integrable (blockErr L) (blockMeasure L) :=
  (memLp_blockErr L).integrable one_le_two

/-! ### The cell counts: sum identity -/

theorem sum_coinCount {L : ℕ} (hL : 0 < L) (q : ℕ) (c : ℕ → ℕ) :
    ∑ p ∈ range L, coinCount L q c p = q := by
  unfold coinCount
  rw [← Finset.card_eq_sum_card_fiberwise (f := fun m => c m % L) (s := range q) (t := range L)
    (fun m _ => by simp [Nat.mod_lt _ hL])]
  exact Finset.card_range q

/-- The cell counts of a block add up to the block count. -/
theorem sum_cellCount {L : ℕ} (hL : 0 < L) (x : BlockSpace) :
    ∑ p ∈ range L, cellCount L p x = blockCount L x :=
  sum_coinCount hL _ _

/-! ### The cell counts: law -/

/-- The Poisson(l) law on `ℕ` as a measure. -/
noncomputable def poisMeasure (l : ℝ) : Measure ℕ :=
  Measure.sum (fun k => ENNReal.ofReal (poisTerm k l) • Measure.dirac k)

theorem poisMeasure_singleton (l : ℝ) (k : ℕ) :
    poisMeasure l {k} = ENNReal.ofReal (poisTerm k l) := by
  unfold poisMeasure
  rw [Measure.sum_apply _ (measurableSet_singleton k)]
  simp only [Measure.smul_apply, Measure.dirac_apply, smul_eq_mul]
  rw [tsum_eq_single k]
  · simp
  · intro j hj
    rw [Set.indicator_of_notMem (by simpa using hj), mul_zero]

instance poisMeasure_isProbabilityMeasure (l : ℝ) [hl : Fact (0 ≤ l)] :
    IsProbabilityMeasure (poisMeasure l) := by
  refine ⟨?_⟩
  unfold poisMeasure
  rw [Measure.sum_apply _ MeasurableSet.univ]
  simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => poisTerm_nonneg k hl.out)
    (hasSum_poisTerm hl.out).summable, (hasSum_poisTerm hl.out).tsum_eq, ENNReal.ofReal_one]

instance : Fact ((0:ℝ) ≤ 1) := ⟨zero_le_one⟩

/-- The coin event `{∀ p, #{m < K : c m % L = p} = k p}` is the union of the word cylinders. -/
theorem coinSeq_fiber (L : ℕ) [NeZero L] {K : ℕ} (k : Fin L → ℕ) (hK : ∑ p, k p = K) :
    coinSeq L {c : ℕ → ℕ | ∀ p : Fin L, coinCount L K c p = k p} =
      (Nat.multinomial univ k : ENNReal) * ((L : ENNReal)⁻¹) ^ K := by
  classical
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  -- the good set: all coins below `L`
  set G : Set (ℕ → ℕ) := {c | ∀ m < K, c m < L} with hG
  have hGnull : coinSeq L Gᶜ = 0 := by
    have hsub : Gᶜ ⊆ ⋃ m ∈ range K, (fun c : ℕ → ℕ => c m) ⁻¹' Set.Ici L := by
      intro c hc
      simp only [hG, mem_compl_iff, mem_setOf_eq, not_forall, not_lt] at hc
      obtain ⟨m, hm, hcm⟩ := hc
      simp only [mem_iUnion, Set.mem_preimage, Set.mem_Ici, Finset.mem_range]
      exact ⟨m, hm, hcm⟩
    refine measure_mono_null hsub (measure_biUnion_null_iff (Finset.countable_toSet _) |>.mpr
      fun m _ => ?_)
    unfold coinSeq
    rw [infinitePi_eval_preimage (fun _ => unifNat L) m measurableSet_Ici, unifNat_Ici]
  -- the cylinder of a word
  let cyl : (Fin K → Fin L) → Set (ℕ → ℕ) := fun f =>
    (↑(range K) : Set ℕ).pi (fun m => if h : m < K then {((f ⟨m, h⟩ : Fin L) : ℕ)} else univ)
  have hcyl_mem : ∀ f (c : ℕ → ℕ), c ∈ cyl f ↔ ∀ m (h : m < K), c m = (f ⟨m, h⟩ : ℕ) := by
    intro f c
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
    · exact measurableSet_singleton _
    · exact MeasurableSet.univ
  have hcyl_measure : ∀ f, coinSeq L (cyl f) = ((L : ENNReal)⁻¹) ^ K := by
    intro f
    unfold coinSeq
    rw [Measure.infinitePi_pi _ (fun m _ => by
      split_ifs
      · exact measurableSet_singleton _
      · exact MeasurableSet.univ)]
    rw [Finset.prod_congr rfl (fun m hm => by
      rw [dif_pos (Finset.mem_range.mp hm), unifNat_singleton, if_pos (Fin.isLt _)])]
    rw [Finset.prod_const, Finset.card_range]
  -- coin counts along a cylinder are the fibre counts of the word
  have hcount : ∀ f (c : ℕ → ℕ), c ∈ cyl f → ∀ p : Fin L, coinCount L K c p = fibCount f p := by
    intro f c hc p
    rw [hcyl_mem] at hc
    unfold coinCount fibCount
    rw [Finset.card_filter, Finset.card_filter, ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [hc m m.isLt, Nat.mod_eq_of_lt (Fin.isLt _)]
    simp [Fin.ext_iff]
  -- the event equals the union of the cylinders over the word set
  have hE : {c : ℕ → ℕ | ∀ p : Fin L, coinCount L K c p = k p} ∩ G =
      ⋃ f ∈ wordSet K L k, cyl f := by
    ext c
    simp only [mem_inter_iff, mem_setOf_eq, mem_iUnion, exists_prop]
    constructor
    · rintro ⟨hc, hcG⟩
      let f₀ : Fin K → Fin L := fun m => ⟨c m, hcG m m.isLt⟩
      have hf₀ : c ∈ cyl f₀ := (hcyl_mem f₀ c).mpr fun m h => rfl
      refine ⟨f₀, ?_, hf₀⟩
      simp only [wordSet, Finset.mem_filter, Finset.mem_univ, true_and]
      intro p
      rw [← hc p, ← hcount f₀ c hf₀ p]
    · rintro ⟨f, hf, hc⟩
      simp only [wordSet, Finset.mem_filter, Finset.mem_univ, true_and] at hf
      refine ⟨fun p => by rw [hcount f c hc p, hf p], fun m hm => ?_⟩
      rw [(hcyl_mem f c).mp hc m hm]
      exact Fin.isLt _
  have hdisj : (↑(wordSet K L k) : Set (Fin K → Fin L)).PairwiseDisjoint cyl := by
    intro f _ f' _ hne
    refine Set.disjoint_left.mpr fun c hc hc' => hne ?_
    funext m
    apply Fin.ext
    rw [← (hcyl_mem f c).mp hc m m.isLt, ← (hcyl_mem f' c).mp hc' m m.isLt]
  rw [← measure_inter_conull hGnull, hE, measure_biUnion_finset hdisj (fun f _ => hcyl_meas f)]
  rw [Finset.sum_congr rfl (fun f _ => hcyl_measure f), Finset.sum_const, nsmul_eq_mul,
    card_wordSet, if_pos hK]

/-- The cell-count vector event is a product event. -/
theorem cellVector_eq_prod {L : ℕ} (hL : 0 < L) (k : Fin L → ℕ) :
    {x : BlockSpace | ∀ p : Fin L, cellCount L p x = k p} =
      {y : ℕ → ℝ | poisCoupling L ((∑ m ∈ range L, y m) / Real.sqrt L) = ∑ p, k p} ×ˢ
        {c : ℕ → ℕ | ∀ p : Fin L, coinCount L (∑ p, k p) c p = k p} := by
  ext ⟨y, c⟩
  simp only [mem_setOf_eq, Set.mem_prod]
  constructor
  · intro h
    have hQ : blockCount L (y, c) = ∑ p, k p := by
      rw [← sum_cellCount hL (y, c), ← Fin.sum_univ_eq_sum_range (fun p => cellCount L p (y, c))]
      exact Finset.sum_congr rfl fun p _ => h p
    refine ⟨hQ, fun p => ?_⟩
    rw [← hQ]
    exact h p
  · rintro ⟨hQ, h⟩ p
    show coinCount L (blockCount L (y, c)) c p = k p
    rw [show blockCount L (y, c) = ∑ p, k p from hQ]
    exact h p

/-- Real identity behind the splitting: `e^{−L} L^K/K! · (K!/∏ k_p!) · L^{−K} = ∏ e^{−1}/k_p!`. -/
theorem poisTerm_mul_multinomial {L K : ℕ} (hL : 0 < L) (k : Fin L → ℕ) (hK : ∑ p, k p = K) :
    poisTerm K L * ((Nat.multinomial univ k : ℝ) * ((L : ℝ)⁻¹) ^ K) = ∏ p, poisTerm (k p) 1 := by
  have hspec : (∏ p, ((k p).factorial : ℝ)) * (Nat.multinomial univ k : ℝ) = (K.factorial : ℝ) := by
    rw [← hK]
    exact_mod_cast Nat.multinomial_spec univ k
  have hprodf : (0:ℝ) < ∏ p, ((k p).factorial : ℝ) :=
    Finset.prod_pos (fun p _ => by exact_mod_cast Nat.factorial_pos _)
  have hM : (Nat.multinomial univ k : ℝ) = (K.factorial : ℝ) / ∏ p, ((k p).factorial : ℝ) := by
    rw [eq_div_iff hprodf.ne', mul_comm]
    exact hspec
  have hexp : ∏ p : Fin L, Real.exp (-1) = Real.exp (-(L:ℝ)) := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.exp_nat_mul]
    ring_nf
  unfold poisTerm
  simp only [one_pow, mul_one]
  rw [Finset.prod_div_distrib, hexp, hM]
  have hL' : (0:ℝ) < L := by exact_mod_cast hL
  have hKf : (0:ℝ) < K.factorial := by exact_mod_cast Nat.factorial_pos K
  rw [inv_pow]
  field_simp

/-- **The cell counts of a block are iid Poisson(1)**: joint point masses. -/
theorem blockMeasure_cellVector (L : ℕ) [NeZero L] (k : Fin L → ℕ) :
    blockMeasure L {x | ∀ p : Fin L, cellCount L p x = k p} =
      ∏ p, ENNReal.ofReal (poisTerm (k p) 1) := by
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hL' : (0:ℝ) < L := by exact_mod_cast hL
  unfold blockMeasure
  rw [cellVector_eq_prod hL k, Measure.prod_prod, gaussSeq_blockCount_eq hL, coinSeq_fiber L k rfl,
    ← ENNReal.ofReal_prod_of_nonneg (fun p _ => poisTerm_nonneg _ zero_le_one),
    ← poisTerm_mul_multinomial hL k rfl,
    ENNReal.ofReal_mul (poisTerm_nonneg _ hL'.le), ENNReal.ofReal_mul (Nat.cast_nonneg _),
    ENNReal.ofReal_natCast, ENNReal.ofReal_pow (inv_nonneg.mpr hL'.le),
    ENNReal.ofReal_inv_of_pos hL', ENNReal.ofReal_natCast]

theorem measurable_cellVector {L : ℕ} (hL : 0 < L) :
    Measurable (fun x : BlockSpace => fun p : Fin L => cellCount L p x) :=
  measurable_pi_lambda _ (fun p => measurable_cellCount hL p)

/-- The law of the cell-count vector is the product of Poisson(1) laws. -/
theorem blockMeasure_map_cellVector (L : ℕ) [NeZero L] :
    (blockMeasure L).map (fun x : BlockSpace => fun p : Fin L => cellCount L p x) =
      Measure.pi (fun _ : Fin L => poisMeasure 1) := by
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  apply Measure.ext_of_singleton
  intro k
  rw [Measure.map_apply (measurable_cellVector hL) (measurableSet_singleton k),
    Measure.pi_singleton]
  have hset : (fun x : BlockSpace => fun p : Fin L => cellCount L p x) ⁻¹' {k} =
      {x | ∀ p : Fin L, cellCount L p x = k p} := by
    ext x
    simp [funext_iff]
  rw [hset, blockMeasure_cellVector L k]
  exact Finset.prod_congr rfl fun p _ => (poisMeasure_singleton 1 (k p)).symm

theorem blockMeasure_map_cellCount (L : ℕ) [NeZero L] (p : Fin L) :
    (blockMeasure L).map (cellCount L p) = poisMeasure 1 := by
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have h1 : (blockMeasure L).map (cellCount L p) =
      ((blockMeasure L).map (fun x : BlockSpace => fun p : Fin L => cellCount L p x)).map
        (Function.eval p) := by
    rw [Measure.map_map (measurable_pi_apply p) (measurable_cellVector hL)]
    rfl
  rw [h1, blockMeasure_map_cellVector, Measure.pi_map_eval]
  simp

/-- `P{N_p = k} = e^{−1}/k!`. -/
theorem blockMeasure_cellCount_eq (L : ℕ) [NeZero L] (p : Fin L) (k : ℕ) :
    blockMeasure L {x | cellCount L p x = k} = ENNReal.ofReal (poisTerm k 1) := by
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  rw [← poisMeasure_singleton, ← blockMeasure_map_cellCount L p,
    Measure.map_apply (measurable_cellCount hL p) (measurableSet_singleton k)]
  rfl

/-- **The cell counts of a block are independent.** -/
theorem iIndepFun_cellCount (L : ℕ) [NeZero L] :
    iIndepFun (fun p : Fin L => cellCount L p) (blockMeasure L) := by
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  rw [iIndepFun_iff_map_fun_eq_pi_map (fun p : Fin L => (measurable_cellCount hL p).aemeasurable)]
  rw [blockMeasure_map_cellVector]
  congr 1
  funext p
  exact (blockMeasure_map_cellCount L p).symm

end Ripple.Kurtz.StrongApprox
