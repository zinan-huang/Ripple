-- Ripple/Kurtz/StrongApprox/AllTimeKMTBrownianLaw.lean
import Ripple.Kurtz.StrongApprox.AllTimeKMTLaws
import Ripple.Kurtz.StrongApprox.BlockIid
import Ripple.Kurtz.StrongApprox.IndepTools

/-!
# The all-time Brownian path satisfies `DyadicBrownianOn` on dyadic horizons

For `H = 2^N` the dyadic cells `[k 2^(N-m), (k+1) 2^(N-m)]`, `k < 2^m`, are
handled in two cases.

* `m ≥ N`: each cell lies inside one closed block, where it is a dyadic cell
  of that block path; cells in different blocks are independent coordinates
  of the infinite product, cells in one block are independent by the block's
  own `DyadicBrownianOn`.
* `m < N`: each cell is a sum of `2^(N-m)` unit increments, which are
  independent standard normals; the sums over disjoint index sets are
  independent.
-/

noncomputable section

namespace Ripple.Kurtz.StrongApprox.AllTimeKMTBrownianLaw

open MeasureTheory ProbabilityTheory Set Finset Filter
open scoped ENNReal NNReal BigOperators Topology
open AllTimeKMT ContinuousFiniteHorizonKMT AllTimeKMTLaws

/-! ## Cells of a dependent product are independent -/

theorem infinitePi_eval_preimage_dep {ι : Type*} {B : ι → Type*}
    [∀ j, MeasurableSpace (B j)] (μ : ∀ j, Measure (B j))
    [∀ j, IsProbabilityMeasure (μ j)] (j : ι) {s : Set (B j)}
    (hs : MeasurableSet s) :
    Measure.infinitePi μ ((fun ω : ∀ i, B i => ω j) ⁻¹' s) = μ j s := by
  rw [← Measure.map_apply (measurable_pi_apply j) hs,
    Measure.infinitePi_map_eval]

/-- Independent families inside each factor of a product of probability spaces
combine into an independent family over all `(factor, cell)` pairs. -/
theorem iIndepFun_sigmaCells {ι : Type*} [DecidableEq ι] {B : ι → Type*}
    [∀ j, MeasurableSpace (B j)] (μ : ∀ j, Measure (B j))
    [∀ j, IsProbabilityMeasure (μ j)] {C : ι → Type*} {β : Type*}
    [MeasurableSpace β] (W : ∀ j, C j → B j → β)
    (hW : ∀ j c, Measurable (W j c))
    (hblk : ∀ j, iIndepFun (fun c : C j => W j c) (μ j)) :
    iIndepFun (fun (p : Σ j, C j) (ω : ∀ j, B j) => W p.1 p.2 (ω p.1))
      (Measure.infinitePi μ) := by
  classical
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S sets hsets
  let I : Finset ι := S.image Sigma.fst
  let T : ∀ j, Finset (C j) := fun j =>
    S.preimage (Sigma.mk j) (sigma_mk_injective.injOn)
  have hS : I.sigma T = S := Finset.sigma_image_fst_preimage_mk S
  let E : ∀ j, Set (B j) := fun j =>
    ⋂ c ∈ T j, (W j c) ⁻¹' sets ⟨j, c⟩
  have hmemT : ∀ j c, c ∈ T j → (⟨j, c⟩ : Σ j, C j) ∈ S := fun j c hc =>
    Finset.mem_preimage.mp hc
  have hEm : ∀ j ∈ I, MeasurableSet (E j) := fun j _ =>
    Finset.measurableSet_biInter _ fun c hc =>
      hW j c (hsets ⟨j, c⟩ (hmemT j c hc))
  have hset : (⋂ p ∈ S, (fun ω : ∀ j, B j => W p.1 p.2 (ω p.1)) ⁻¹' sets p) =
      (↑I : Set ι).pi E := by
    ext ω
    simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_pi, Finset.mem_coe]
    constructor
    · intro h j _
      simp only [E, Set.mem_iInter, Set.mem_preimage]
      intro c hc
      exact h ⟨j, c⟩ (hmemT j c hc)
    · intro h p hp
      have := h p.1 (Finset.mem_image_of_mem _ hp)
      simp only [E, Set.mem_iInter, Set.mem_preimage] at this
      exact this p.2 (Finset.mem_preimage.mpr hp)
  rw [hset, Measure.infinitePi_pi μ hEm]
  have hblock : ∀ j ∈ I, μ j (E j) =
      ∏ c ∈ T j, μ j ((W j c) ⁻¹' sets ⟨j, c⟩) := by
    intro j _
    exact (hblk j).meas_biInter fun c hc =>
      ⟨sets ⟨j, c⟩, hsets ⟨j, c⟩ (hmemT j c hc), rfl⟩
  have hrhs : ∏ p ∈ S, Measure.infinitePi μ
      ((fun ω : ∀ j, B j => W p.1 p.2 (ω p.1)) ⁻¹' sets p) =
      ∏ p ∈ S, μ p.1 ((W p.1 p.2) ⁻¹' sets p) := by
    refine Finset.prod_congr rfl fun p hp => ?_
    exact infinitePi_eval_preimage_dep μ p.1 (hW p.1 p.2 (hsets p hp))
  rw [hrhs, ← hS, Finset.prod_sigma]
  exact Finset.prod_congr rfl hblock

/-! ## Finite sums of independent standard normals -/

theorem map_finset_sum_gaussian {Ω ι : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] [DecidableEq ι]
    {X : ι → Ω → ℝ} (hind : iIndepFun X P) (hX : ∀ i, Measurable (X i))
    (hlaw : ∀ i, P.map (X i) = gaussianReal 0 1) (S : Finset ι) :
    P.map (fun ω => ∑ i ∈ S, X i ω) = gaussianReal 0 (S.card : ℝ≥0) := by
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, Finset.card_empty, Nat.cast_zero]
    rw [Measure.map_const, measure_univ, one_smul, gaussianReal_zero_var]
  | insert a S ha ih =>
    have hind' : IndepFun (∑ i ∈ S, X i) (X a) P :=
      hind.indepFun_finsetSum_of_notMem hX ha
    have hsum : (fun ω => ∑ i ∈ insert a S, X i ω) =
        (∑ i ∈ S, X i) + X a := by
      funext ω
      simp [Finset.sum_insert ha, add_comm]
    have hmeas : Measurable (∑ i ∈ S, X i) := by
      have e : (∑ i ∈ S, X i) = fun ω => ∑ i ∈ S, X i ω := by
        funext ω
        simp
      rw [e]
      exact Finset.measurable_sum _ fun i _ => hX i
    rw [hsum, IndepFun.map_add_eq_map_conv_map hmeas (hX a) hind']
    have h1 : P.map (∑ i ∈ S, X i) = gaussianReal 0 (S.card : ℝ≥0) := by
      rw [← ih]
      congr 1
      funext ω
      simp
    rw [h1, hlaw a, gaussianReal_conv_gaussianReal, add_zero,
      Finset.card_insert_of_notMem ha]
    congr 1
    push_cast
    ring


/-! ## Dyadic cells of the all-time path inside one block -/

/-- A dyadic cell of block `J` at level `m`, as a function of the block
coordinate. -/
def blockCell (J m c : ℕ) (z : ContinuousKMTSpace J) : ℝ :=
  continuousKMTBrownian J (brownianDyadicPoint ((2 : ℝ) ^ J) m (c + 1)) z -
    continuousKMTBrownian J (brownianDyadicPoint ((2 : ℝ) ^ J) m c) z

theorem measurable_blockCell (J m c : ℕ) : Measurable (blockCell J m c) :=
  (measurable_continuousKMTBrownian J _).sub
    (measurable_continuousKMTBrownian J _)

theorem brownianDyadicMesh_pow_add (J e : ℕ) :
    brownianDyadicMesh ((2 : ℝ) ^ J) (J + e) = 1 / (2 : ℝ) ^ e := by
  unfold brownianDyadicMesh
  rw [pow_add]
  field_simp

theorem brownianDyadicPoint_pow_add (J e c : ℕ) :
    brownianDyadicPoint ((2 : ℝ) ^ J) (J + e) c = (c : ℝ) / (2 : ℝ) ^ e := by
  unfold brownianDyadicPoint
  rw [pow_add]
  field_simp

/-- The block of the cell with left end `k / 2^e`. -/
def cellBlock (e k : ℕ) : ℕ := allTimeBlock ((k : ℝ) / (2 : ℝ) ^ e)

/-- The local index of that cell inside its block. -/
def cellLocal (e k : ℕ) : ℕ := k - (2 ^ cellBlock e k - 1) * 2 ^ e

theorem cellBlock_le (e k : ℕ) :
    (2 ^ cellBlock e k - 1) * 2 ^ e ≤ k := by
  have h0 : (0 : ℝ) ≤ (k : ℝ) / (2 : ℝ) ^ e := by positivity
  have h := allTimeBlock_lower h0
  unfold allTimeBlockStart allTimeBlockLength at h
  have hpos : (0 : ℝ) < (2 : ℝ) ^ e := by positivity
  have h2 : ((2 : ℝ) ^ cellBlock e k - 1) * (2 : ℝ) ^ e ≤ k := by
    have := (le_div_iff₀ hpos).mp h
    exact this
  have h1 : 1 ≤ 2 ^ cellBlock e k := Nat.one_le_two_pow
  have : (((2 ^ cellBlock e k - 1) * 2 ^ e : ℕ) : ℝ) ≤ (k : ℝ) := by
    push_cast [Nat.cast_sub h1]
    exact h2
  exact_mod_cast this

theorem cellBlock_lt (e k : ℕ) :
    k < (2 ^ (cellBlock e k + 1) - 1) * 2 ^ e := by
  have h0 : (0 : ℝ) ≤ (k : ℝ) / (2 : ℝ) ^ e := by positivity
  have h := allTimeBlock_upper h0
  unfold allTimeBlockStart allTimeBlockLength at h
  have hpos : (0 : ℝ) < (2 : ℝ) ^ e := by positivity
  have h1 : 1 ≤ 2 ^ (cellBlock e k + 1) := Nat.one_le_two_pow
  have h2 : (k : ℝ) < ((2 : ℝ) ^ (cellBlock e k + 1) - 1) * (2 : ℝ) ^ e :=
    (div_lt_iff₀ hpos).mp h
  have : (k : ℝ) < (((2 ^ (cellBlock e k + 1) - 1) * 2 ^ e : ℕ) : ℝ) := by
    push_cast [Nat.cast_sub h1]
    exact h2
  exact_mod_cast this

theorem cellLocal_lt (e k : ℕ) : cellLocal e k < 2 ^ (cellBlock e k + e) := by
  have h1 := cellBlock_le e k
  have h2 := cellBlock_lt e k
  unfold cellLocal
  have hq : 2 ^ (cellBlock e k + 1) = 2 * 2 ^ cellBlock e k := by ring
  have hr : 2 ^ (cellBlock e k + e) = 2 ^ cellBlock e k * 2 ^ e := by
    rw [pow_add]
  have hJ : 1 ≤ 2 ^ cellBlock e k := Nat.one_le_two_pow
  rw [hq] at h2
  rw [hr]
  have e1 : (2 * 2 ^ cellBlock e k - 1) * 2 ^ e =
      (2 ^ cellBlock e k - 1) * 2 ^ e + 2 ^ cellBlock e k * 2 ^ e := by
    have : 2 * 2 ^ cellBlock e k - 1 =
        (2 ^ cellBlock e k - 1) + 2 ^ cellBlock e k := by omega
    rw [this, add_mul]
  rw [e1] at h2
  omega

theorem cellLocal_add (e k : ℕ) :
    cellLocal e k + (2 ^ cellBlock e k - 1) * 2 ^ e = k := by
  unfold cellLocal
  have := cellBlock_le e k
  omega

/-- Real form of the local index. -/
theorem cellLocal_cast (e k : ℕ) :
    ((cellLocal e k : ℕ) : ℝ) =
      (k : ℝ) - ((2 : ℝ) ^ cellBlock e k - 1) * (2 : ℝ) ^ e := by
  have h1 : 1 ≤ 2 ^ cellBlock e k := Nat.one_le_two_pow
  have := cellLocal_add e k
  have h : (((cellLocal e k + (2 ^ cellBlock e k - 1) * 2 ^ e : ℕ)) : ℝ) = k := by
    exact_mod_cast this
  push_cast [Nat.cast_sub h1] at h
  linarith


/-! ## The family of cells of width `2^(-e)` -/

/-- The cell `[k/2^e, (k+1)/2^e]` of the all-time Brownian path. -/
def cellIncr (e k : ℕ) (ω : AllTimeKMTSpace) : ℝ :=
  allTimeKMTBrownian (((k : ℝ) + 1) / (2 : ℝ) ^ e) ω -
    allTimeKMTBrownian ((k : ℝ) / (2 : ℝ) ^ e) ω

theorem measurable_cellIncr (e k : ℕ) : Measurable (cellIncr e k) :=
  (measurable_allTimeKMTBrownian _).sub (measurable_allTimeKMTBrownian _)

theorem cellIncr_eq_blockCell (e k : ℕ) (ω : AllTimeKMTSpace) :
    cellIncr e k ω =
      blockCell (cellBlock e k) (cellBlock e k + e) (cellLocal e k)
        (ω (cellBlock e k)) := by
  have hpos : (0 : ℝ) < (2 : ℝ) ^ e := by positivity
  set J := cellBlock e k with hJ
  have h1 : 1 ≤ 2 ^ (J + 1) := Nat.one_le_two_pow
  have hlow : allTimeBlockStart J ≤ (k : ℝ) / (2 : ℝ) ^ e :=
    allTimeBlock_lower (by positivity)
  have hM : k + 1 ≤ (2 ^ (J + 1) - 1) * 2 ^ e := cellBlock_lt e k
  have hM' : (k : ℝ) + 1 ≤ ((2 : ℝ) ^ (J + 1) - 1) * (2 : ℝ) ^ e := by
    have : ((k + 1 : ℕ) : ℝ) ≤ (((2 ^ (J + 1) - 1) * 2 ^ e : ℕ) : ℝ) :=
      Nat.cast_le.mpr hM
    push_cast [Nat.cast_sub h1] at this
    exact this
  have hb : ((k : ℝ) + 1) / (2 : ℝ) ^ e ≤ allTimeBlockStart (J + 1) := by
    rw [div_le_iff₀ hpos]
    unfold allTimeBlockStart allTimeBlockLength
    exact hM'
  have hab : (k : ℝ) / (2 : ℝ) ^ e ≤ ((k : ℝ) + 1) / (2 : ℝ) ^ e := by
    apply div_le_div_of_nonneg_right _ hpos.le
    linarith
  unfold cellIncr
  rw [allTimeKMTBrownian_closed_block ω (hlow.trans hab) hb,
    allTimeKMTBrownian_closed_block ω hlow (hab.trans hb)]
  unfold blockCell
  rw [brownianDyadicPoint_pow_add, brownianDyadicPoint_pow_add]
  have hc := cellLocal_cast e k
  have e1 : ((k : ℝ) + 1) / (2 : ℝ) ^ e - allTimeBlockStart J =
      (((cellLocal e k + 1 : ℕ) : ℝ)) / (2 : ℝ) ^ e := by
    unfold allTimeBlockStart allTimeBlockLength
    push_cast
    rw [hc]
    field_simp
    ring
  have e2 : (k : ℝ) / (2 : ℝ) ^ e - allTimeBlockStart J =
      ((cellLocal e k : ℕ) : ℝ) / (2 : ℝ) ^ e := by
    unfold allTimeBlockStart allTimeBlockLength
    rw [hc]
    field_simp
    ring
  rw [e1, e2]
  ring

theorem cellIncr_iIndep (e : ℕ) :
    iIndepFun (fun (k : ℕ) ω => cellIncr e k ω) allTimeKMTMeasure := by
  classical
  let C : ℕ → Type := fun J => Fin (2 ^ (J + e))
  let Wf : ∀ J, C J → ContinuousKMTSpace J → ℝ := fun J c z =>
    blockCell J (J + e) c.1 z
  have hsig := iIndepFun_sigmaCells (fun J => continuousKMTMeasure J) Wf
    (fun J c => measurable_blockCell _ _ _)
    (fun J => (continuousKMTBrownian_dyadicBrownianOn J).cell_independent (J + e))
  let g : ℕ → Σ J, C J := fun k =>
    ⟨cellBlock e k, ⟨cellLocal e k, cellLocal_lt e k⟩⟩
  have hinj : Function.Injective g := by
    intro k k' h
    have h1 : cellBlock e k = cellBlock e k' := congrArg Sigma.fst h
    have h2 : cellLocal e k = cellLocal e k' :=
      congrArg (fun p : Σ J, C J => (p.2 : ℕ)) h
    have a1 := cellLocal_add e k
    have a2 := cellLocal_add e k'
    rw [h1, h2] at a1
    omega
  have hcomp := hsig.precomp hinj
  have hfun : (fun (k : ℕ) ω => cellIncr e k ω) =
      fun k ω => Wf (g k).1 (g k).2 (ω (g k).1) := by
    funext k ω
    exact cellIncr_eq_blockCell e k ω
  rw [hfun]
  exact hcomp

theorem cellIncr_map (e k : ℕ) :
    allTimeKMTMeasure.map (cellIncr e k) =
      gaussianReal 0 (Real.toNNReal (1 / (2 : ℝ) ^ e)) := by
  have hfun : cellIncr e k = fun ω =>
      blockCell (cellBlock e k) (cellBlock e k + e) (cellLocal e k)
        (ω (cellBlock e k)) := by
    funext ω
    exact cellIncr_eq_blockCell e k ω
  rw [hfun]
  have hm := measurable_blockCell (cellBlock e k) (cellBlock e k + e)
    (cellLocal e k)
  calc
    allTimeKMTMeasure.map (fun ω =>
        blockCell (cellBlock e k) (cellBlock e k + e) (cellLocal e k)
          (ω (cellBlock e k))) =
      (allTimeKMTMeasure.map (fun ω : AllTimeKMTSpace => ω (cellBlock e k))).map
        (blockCell (cellBlock e k) (cellBlock e k + e) (cellLocal e k)) :=
      (Measure.map_map hm (measurable_pi_apply (cellBlock e k))).symm
    _ = (continuousKMTMeasure (cellBlock e k)).map
        (blockCell (cellBlock e k) (cellBlock e k + e) (cellLocal e k)) := by
      rw [(allTimeEval_measurePreserving' (cellBlock e k)).map_eq]
    _ = gaussianReal 0 (Real.toNNReal
        (brownianDyadicMesh ((2 : ℝ) ^ cellBlock e k)
          (cellBlock e k + e))) :=
      (continuousKMTBrownian_dyadicBrownianOn (cellBlock e k)).cell_law
        (cellBlock e k + e) ⟨cellLocal e k, cellLocal_lt e k⟩
    _ = _ := by rw [brownianDyadicMesh_pow_add]


/-! ## `DyadicBrownianOn` on a dyadic horizon -/

theorem sum_cellIncr_zero (a b : ℕ) (hab : a ≤ b) (ω : AllTimeKMTSpace) :
    ∑ i ∈ Finset.Ico a b, cellIncr 0 i ω =
      allTimeKMTBrownian (b : ℝ) ω - allTimeKMTBrownian (a : ℝ) ω := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    rw [Finset.sum_Ico_succ_top hab, ih]
    unfold cellIncr
    push_cast
    simp only [pow_zero, div_one]
    ring

theorem brownianDyadicPoint_dyadic_horizon (N m f c : ℕ) (h : N = m + f) :
    brownianDyadicPoint ((2 : ℝ) ^ N) m c = ((c * 2 ^ f : ℕ) : ℝ) := by
  unfold brownianDyadicPoint
  subst h
  rw [pow_add]
  push_cast
  field_simp

theorem cell_eq_cellIncr (N e c : ℕ) (ω : AllTimeKMTSpace) :
    allTimeKMTBrownian (brownianDyadicPoint ((2 : ℝ) ^ N) (N + e) (c + 1)) ω -
      allTimeKMTBrownian (brownianDyadicPoint ((2 : ℝ) ^ N) (N + e) c) ω =
        cellIncr e c ω := by
  rw [brownianDyadicPoint_pow_add, brownianDyadicPoint_pow_add]
  unfold cellIncr
  push_cast
  rfl

theorem cell_eq_sum (N m f : ℕ) (h : N = m + f) (k : ℕ)
    (ω : AllTimeKMTSpace) :
    allTimeKMTBrownian (brownianDyadicPoint ((2 : ℝ) ^ N) m (k + 1)) ω -
      allTimeKMTBrownian (brownianDyadicPoint ((2 : ℝ) ^ N) m k) ω =
        ∑ i ∈ Finset.Ico (k * 2 ^ f) ((k + 1) * 2 ^ f), cellIncr 0 i ω := by
  rw [sum_cellIncr_zero _ _ (Nat.mul_le_mul_right _ (Nat.le_succ k)),
    brownianDyadicPoint_dyadic_horizon N m f _ h,
    brownianDyadicPoint_dyadic_horizon N m f _ h]

theorem Ico_card_pow (k f : ℕ) :
    (Finset.Ico (k * 2 ^ f) ((k + 1) * 2 ^ f)).card = 2 ^ f := by
  rw [Nat.card_Ico, add_mul, one_mul]
  exact Nat.add_sub_cancel_left _ _

theorem Ico_disjoint_pow (f : ℕ) {k k' : ℕ} (hne : k ≠ k') :
    Disjoint (Finset.Ico (k * 2 ^ f) ((k + 1) * 2 ^ f))
      (Finset.Ico (k' * 2 ^ f) ((k' + 1) * 2 ^ f)) := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  rw [Finset.mem_Ico] at hx hx'
  have h1 : x / 2 ^ f = k := Nat.div_eq_of_lt_le hx.1 hx.2
  have h2 : x / 2 ^ f = k' := Nat.div_eq_of_lt_le hx'.1 hx'.2
  exact hne (h1.symm.trans h2)

theorem allTimeKMTBrownian_dyadicBrownianOn (N : ℕ) :
    DyadicBrownianOn allTimeKMTMeasure
      (fun t ω => allTimeKMTBrownian t ω) ((2 : ℝ) ^ N) where
  eval_measurable := fun t => measurable_allTimeKMTBrownian t
  continuous_ae := allTimeKMTBrownian_continuous_ae
  cell_law := by
    intro m k
    by_cases hmN : N ≤ m
    · obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hmN
      have hfun : (fun omega : AllTimeKMTSpace =>
          allTimeKMTBrownian (brownianDyadicPoint ((2 : ℝ) ^ N) (N + e)
            (k.val + 1)) omega -
          allTimeKMTBrownian (brownianDyadicPoint ((2 : ℝ) ^ N) (N + e)
            k.val) omega) = cellIncr e k.val := by
        funext omega
        exact cell_eq_cellIncr N e k.val omega
      show allTimeKMTMeasure.map (fun omega : AllTimeKMTSpace =>
          allTimeKMTBrownian (brownianDyadicPoint ((2 : ℝ) ^ N) (N + e)
            (k.val + 1)) omega -
          allTimeKMTBrownian (brownianDyadicPoint ((2 : ℝ) ^ N) (N + e)
            k.val) omega) = _
      rw [hfun, cellIncr_map, brownianDyadicMesh_pow_add]
    · have hlt : m < N := lt_of_not_ge hmN
      obtain ⟨f, hf⟩ := Nat.exists_eq_add_of_le hlt.le
      have hfun : (fun omega : AllTimeKMTSpace =>
          allTimeKMTBrownian (brownianDyadicPoint ((2 : ℝ) ^ N) m
            (k.val + 1)) omega -
          allTimeKMTBrownian (brownianDyadicPoint ((2 : ℝ) ^ N) m
            k.val) omega) = fun omega =>
          ∑ i ∈ Finset.Ico (k.val * 2 ^ f) ((k.val + 1) * 2 ^ f),
            cellIncr 0 i omega := by
        funext omega
        exact cell_eq_sum N m f hf k.val omega
      show allTimeKMTMeasure.map (fun omega : AllTimeKMTSpace =>
          allTimeKMTBrownian (brownianDyadicPoint ((2 : ℝ) ^ N) m
            (k.val + 1)) omega -
          allTimeKMTBrownian (brownianDyadicPoint ((2 : ℝ) ^ N) m
            k.val) omega) = _
      rw [hfun]
      have hlaw : ∀ i : ℕ, allTimeKMTMeasure.map (cellIncr 0 i) =
          gaussianReal 0 1 := by
        intro i
        simpa using cellIncr_map 0 i
      rw [map_finset_sum_gaussian (cellIncr_iIndep 0)
        (measurable_cellIncr 0) hlaw, Ico_card_pow]
      congr 1
      apply NNReal.coe_injective
      have hmesh : brownianDyadicMesh ((2 : ℝ) ^ N) m = (2 : ℝ) ^ f := by
        unfold brownianDyadicMesh
        subst hf
        rw [pow_add]
        field_simp
      rw [hmesh, Real.coe_toNNReal _ (by positivity)]
      push_cast
      rfl
  cell_independent := by
    intro m
    by_cases hmN : N ≤ m
    · obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hmN
      have hind := (cellIncr_iIndep e).precomp
        (g := fun k : Fin (2 ^ (N + e)) => (k : ℕ)) Fin.val_injective
      have hfun : (fun (k : Fin (2 ^ (N + e))) (omega : AllTimeKMTSpace) =>
          allTimeKMTBrownian (brownianDyadicPoint ((2 : ℝ) ^ N) (N + e)
            (k.val + 1)) omega -
          allTimeKMTBrownian (brownianDyadicPoint ((2 : ℝ) ^ N) (N + e)
            k.val) omega) = fun k omega => cellIncr e k.val omega := by
        funext k omega
        exact cell_eq_cellIncr N e k.val omega
      show iIndepFun (fun (k : Fin (2 ^ (N + e))) (omega : AllTimeKMTSpace) =>
          allTimeKMTBrownian (brownianDyadicPoint ((2 : ℝ) ^ N) (N + e)
            (k.val + 1)) omega -
          allTimeKMTBrownian (brownianDyadicPoint ((2 : ℝ) ^ N) (N + e)
            k.val) omega) allTimeKMTMeasure
      rw [hfun]
      exact hind
    · have hlt : m < N := lt_of_not_ge hmN
      obtain ⟨f, hf⟩ := Nat.exists_eq_add_of_le hlt.le
      classical
      let S : Fin (2 ^ m) → Finset ℕ := fun k =>
        Finset.Ico (k.val * 2 ^ f) ((k.val + 1) * 2 ^ f)
      have hS : Pairwise (Function.onFun Disjoint S) := by
        intro k k' hne
        exact Ico_disjoint_pow f (fun h => hne (Fin.ext h))
      have hcomp := iIndepFun_finsets_comp (P := allTimeKMTMeasure)
        (cellIncr_iIndep 0) (measurable_cellIncr 0) S hS
        (fun k (v : (↥(S k)) → ℝ) => ∑ i, v i)
        (fun k => Finset.measurable_sum _ fun i _ => measurable_pi_apply i)
      have hfun : (fun (k : Fin (2 ^ m)) (omega : AllTimeKMTSpace) =>
          allTimeKMTBrownian (brownianDyadicPoint ((2 : ℝ) ^ N) m
            (k.val + 1)) omega -
          allTimeKMTBrownian (brownianDyadicPoint ((2 : ℝ) ^ N) m
            k.val) omega) = fun k omega =>
          ∑ i : ↥(S k), cellIncr 0 (i : ℕ) omega := by
        funext k omega
        rw [cell_eq_sum N m f hf k.val omega]
        exact (Finset.sum_coe_sort (S k) (fun i => cellIncr 0 i omega)).symm
      show iIndepFun (fun (k : Fin (2 ^ m)) (omega : AllTimeKMTSpace) =>
          allTimeKMTBrownian (brownianDyadicPoint ((2 : ℝ) ^ N) m
            (k.val + 1)) omega -
          allTimeKMTBrownian (brownianDyadicPoint ((2 : ℝ) ^ N) m
            k.val) omega) allTimeKMTMeasure
      rw [hfun]
      exact hcomp

end Ripple.Kurtz.StrongApprox.AllTimeKMTBrownianLaw

end
