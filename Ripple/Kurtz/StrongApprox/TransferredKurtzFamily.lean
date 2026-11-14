import Ripple.Kurtz.StrongApprox.KMTReferenceBrownian
import Ripple.Kurtz.StrongApprox.KMTTransferProduct
import Ripple.Kurtz.StrongApprox.FixedScaleKurtzComparison

/-!
# Kurtz Theorem 3.3(a) for a transferred family of population sizes

One probability space `P` carries, for every population size `N ≥ 2`, a finite family
`(β N l)_l` of independent pre-Brownian paths with continuous sample paths. The KMT cell
paths are attached to all coordinates `(N, l)` at once by the conditional-Poisson marking
`kmtArrayTransferMeasure`. On the marked space we read

* the transferred cell path `transferredCellPath N l`,
* the Brownian path `transferredBrownian β N l` (the `l`th path of the `N`th family),
* the KMT coefficient `transferredXi β N l`.

Given the chain and diffusion equations at every `N ≥ 2` (`FixedScaleKurtzPaths`), the
fixed-size comparison `finiteChannelKurtz_at` applies at every `N`, with the explicit
coefficient `transferredKurtzBeta`. These coefficients are identically distributed in `N`:
the coefficient factors through the joint code of the pairs (Brownian code, Poisson code)
of the `N`th family, and that joint code has the law `Measure.pi (fun _ => kmtReferenceJointLaw)`
for every `N`, by fixed-`N` channel independence and the reference coordinate law. The
identical laws give one exponential moment, uniform in `N`, and the comparison bound holds
for all `N ≥ 2` on one conull set.

The supporting results are:

* `dyadicBrownianOn_of_isPreBrownian`: a pre-Brownian process with continuous paths gives
  the dyadic cell law and independence used by the entropy estimates;
* `dyadicEntropyCommonReal_congr`: the common entropy level reads a path only at dyadic
  points;
* `map_familyPairCode`: the law of the fixed-`N` pair code is a product of reference laws.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace Ripple.Kurtz.StrongApprox.KMTTransfer

open AllTimeKMT AllTimeKurtzMoment AllTimeKMTPoissonLaw KMTTransferGeneral

/-! ## Dyadic Brownian law from a pre-Brownian process -/

section DyadicLaw

variable {Ω : Type*} [MeasurableSpace Ω]

theorem brownianDyadicPoint_nonneg {H : ℝ} (hH : 0 ≤ H) (m k : ℕ) :
    0 ≤ brownianDyadicPoint H m k := by
  unfold brownianDyadicPoint
  exact div_nonneg (mul_nonneg hH (Nat.cast_nonneg _)) (by positivity)

theorem brownianDyadicPoint_mono {H : ℝ} (hH : 0 ≤ H) (m : ℕ) :
    Monotone (fun k : ℕ => brownianDyadicPoint H m k) := by
  intro a b hab
  unfold brownianDyadicPoint
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (by exact_mod_cast hab) hH) (by positivity)

/-- A pre-Brownian process with continuous paths, read on the real line through
`Real.toNNReal`, has the dyadic cell law and cell independence on every horizon `H ≥ 0`. -/
theorem dyadicBrownianOn_of_isPreBrownian
    {P : Measure Ω} {β : ℝ≥0 → Ω → ℝ} [IsPreBrownian β P]
    (hβ : ∀ t, Measurable (β t))
    (hcont : ∀ᵐ ω ∂P, Continuous fun t => β t ω) {H : ℝ} (hH : 0 ≤ H) :
    DyadicBrownianOn P (fun u ω => β u.toNNReal ω) H where
  eval_measurable := fun t => hβ _
  continuous_ae := hcont.mono fun ω h => h.comp continuous_real_toNNReal
  cell_law := by
    intro m k
    have hlaw := (IsPreBrownian.hasLaw_sub (X := β) (P := P)
      (brownianDyadicPoint H m (k.val + 1)).toNNReal
      (brownianDyadicPoint H m k.val).toNNReal).map_eq
    have h0 : 0 ≤ brownianDyadicPoint H m k.val := brownianDyadicPoint_nonneg hH m k.val
    have hle := brownianDyadicPoint_mono hH m (Nat.le_succ k.val)
    have hvar : max ((brownianDyadicPoint H m (k.val + 1)).toNNReal -
        (brownianDyadicPoint H m k.val).toNNReal)
        ((brownianDyadicPoint H m k.val).toNNReal -
          (brownianDyadicPoint H m (k.val + 1)).toNNReal) =
        (brownianDyadicMesh H m).toNNReal := by
      have h1 : 0 ≤ brownianDyadicPoint H m (k.val + 1) := brownianDyadicPoint_nonneg hH m _
      have hmesh : 0 ≤ brownianDyadicMesh H m := by
        unfold brownianDyadicMesh
        exact div_nonneg hH (by positivity)
      have hle' := Real.toNNReal_le_toNNReal hle
      rw [tsub_eq_zero_of_le hle', max_eq_left zero_le]
      apply NNReal.coe_injective
      rw [NNReal.coe_sub hle', Real.coe_toNNReal _ h1, Real.coe_toNNReal _ h0,
        Real.coe_toNNReal _ hmesh]
      unfold brownianDyadicPoint brownianDyadicMesh
      push_cast
      ring
    rw [hvar] at hlaw
    exact hlaw
  cell_independent := by
    intro m
    have hmono : Monotone
        (fun i : Fin (2 ^ m + 1) => (brownianDyadicPoint H m i.val).toNNReal) :=
      fun a b hab => Real.toNNReal_le_toNNReal
        (brownianDyadicPoint_mono hH m (Fin.le_iff_val_le_val.1 hab))
    exact (IsPreBrownian.hasIndepIncrements (X := β) (P := P)) (2 ^ m) _ hmono

/-- A pre-Brownian process stays pre-Brownian when read through a law-preserving first
projection. -/
theorem isPreBrownian_comp_fst {E : Type*} [MeasurableSpace E]
    {P : Measure Ω} {Q : Measure (Ω × E)} (hQ : Q.map Prod.fst = P)
    {β : ℝ≥0 → Ω → ℝ} [IsPreBrownian β P] :
    IsPreBrownian (fun t z => β t z.1) Q :=
  ⟨fun I => (IsPreBrownian.hasLaw (X := β) (P := P) I).comp
    ⟨measurable_fst.aemeasurable, hQ⟩⟩

end DyadicLaw

/-! ## The entropy level reads a path only at dyadic points -/

section Congruence

variable {Ω₁ Ω₂ : Type*}

theorem brownianEntropyLevel_congr {W₁ : ℝ → Ω₁ → ℝ} {W₂ : ℝ → Ω₂ → ℝ} {H : ℝ}
    {ω₁ : Ω₁} {ω₂ : Ω₂}
    (h : ∀ m k : ℕ, W₁ (brownianDyadicPoint H m k) ω₁ = W₂ (brownianDyadicPoint H m k) ω₂) :
    brownianEntropyLevel W₁ H ω₁ = brownianEntropyLevel W₂ H ω₂ := by
  have hf : ∀ a, ω₁ ∈ brownianDyadicFailure W₁ H a ↔ ω₂ ∈ brownianDyadicFailure W₂ H a := by
    intro a
    simp only [brownianDyadicFailure, brownianDyadicLevelFailure, Set.mem_iUnion,
      Set.mem_setOf_eq, h]
  unfold brownianEntropyLevel
  simp only [hf]

theorem dyadicEntropyCommonReal_congr {ι : Type*} [Fintype ι]
    {W₁ : ι → ℝ → Ω₁ → ℝ} {W₂ : ι → ℝ → Ω₂ → ℝ} {ω₁ : Ω₁} {ω₂ : Ω₂}
    (h : ∀ (l : ι) (j m k : ℕ),
      W₁ l (brownianDyadicPoint ((2 : ℝ) ^ j) m k) ω₁ =
        W₂ l (brownianDyadicPoint ((2 : ℝ) ^ j) m k) ω₂) :
    dyadicEntropyCommonReal W₁ ω₁ = dyadicEntropyCommonReal W₂ ω₂ := by
  unfold dyadicEntropyCommonReal dyadicEntropyCommonLevel
  congr 1
  refine iSup_congr fun l => iSup_congr fun j => ?_
  rw [brownianEntropyLevel_congr (h l j)]

end Congruence

/-! ## Reading a Brownian code at real times -/

/-- The value of a Brownian code at a real time; zero off the nonnegative rationals. -/
def codeEval (b : KMTBrownianCode) (t : ℝ) : ℝ :=
  @dite ℝ (∃ q : KMTNonnegRat, ((q.1 : ℚ) : ℝ) = t) (Classical.dec _)
    (fun h => b h.choose) (fun _ => 0)

theorem measurable_codeEval (t : ℝ) : Measurable fun c : KMTBrownianCode => codeEval c t := by
  by_cases h : ∃ q : KMTNonnegRat, ((q.1 : ℚ) : ℝ) = t
  · have hc : (fun c : KMTBrownianCode => codeEval c t) = fun c => c h.choose := by
      funext c
      unfold codeEval
      rw [dif_pos h]
    rw [hc]
    exact measurable_pi_apply _
  · have hc : (fun c : KMTBrownianCode => codeEval c t) = fun _ => 0 := by
      funext c
      unfold codeEval
      rw [dif_neg h]
    rw [hc]
    exact measurable_const

theorem codeEval_brownianCodeOf {Ω : Type*} (β : ℝ≥0 → Ω → ℝ) (ω : Ω) (q : KMTNonnegRat) :
    codeEval (brownianCodeOf β ω) ((q.1 : ℚ) : ℝ) = β (Real.toNNReal ((q.1 : ℚ) : ℝ)) ω := by
  have h : ∃ q' : KMTNonnegRat, ((q'.1 : ℚ) : ℝ) = ((q.1 : ℚ) : ℝ) := ⟨q, rfl⟩
  unfold codeEval
  rw [dif_pos h]
  unfold brownianCodeOf
  rw [← nnrealOfNonnegRat_eq, h.choose_spec]

theorem exists_rat_brownianDyadicPoint (j m k : ℕ) :
    ∃ q : KMTNonnegRat, ((q.1 : ℚ) : ℝ) = brownianDyadicPoint ((2 : ℝ) ^ j) m k := by
  refine ⟨⟨(2 : ℚ) ^ j * k / 2 ^ m, by positivity⟩, ?_⟩
  unfold brownianDyadicPoint
  push_cast
  ring

theorem codeEval_brownianCodeOf_dyadic {Ω : Type*} (β : ℝ≥0 → Ω → ℝ) (ω : Ω) (j m k : ℕ) :
    codeEval (brownianCodeOf β ω) (brownianDyadicPoint ((2 : ℝ) ^ j) m k) =
      β (brownianDyadicPoint ((2 : ℝ) ^ j) m k).toNNReal ω := by
  obtain ⟨q, hq⟩ := exists_rat_brownianDyadicPoint j m k
  rw [← hq]
  exact codeEval_brownianCodeOf β ω q

/-! ## The transferred family -/

section Family

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]

/-- The Brownian codes of all families, indexed by `(N, l)`. -/
def familyBrownianCode (β : ℕ → ι → ℝ≥0 → Ω → ℝ) (ω : Ω) : ℕ × ι → KMTBrownianCode :=
  fun j => brownianCodeOf (β j.1 j.2) ω

omit [Fintype ι] in
theorem measurable_familyBrownianCode {β : ℕ → ι → ℝ≥0 → Ω → ℝ}
    (hβ : ∀ N l t, Measurable (β N l t)) : Measurable (familyBrownianCode β) :=
  measurable_pi_lambda _ fun j => measurable_brownianCodeOf (hβ j.1 j.2)

/-- The marked space carrying every family together with its transferred cell paths. -/
abbrev kmtFamilyMeasure (P : Measure Ω) (β : ℕ → ι → ℝ≥0 → Ω → ℝ)
    (hβ : ∀ N l t, Measurable (β N l t)) : Measure (Ω × (ℕ × ι → KMTPoissonCode)) :=
  kmtArrayTransferMeasure P (familyBrownianCode β) (measurable_familyBrownianCode hβ)

/-- The transferred cell path of channel `l` at population size `N`. -/
def transferredCellPath (N : ℕ) (l : ι) (u : ℝ) (z : Ω × (ℕ × ι → KMTPoissonCode)) : ℝ :=
  (cellPath u (z.2 (N, l)) : ℝ)

/-- The Brownian path of channel `l` at population size `N`, on the real line. -/
def transferredBrownian (β : ℕ → ι → ℝ≥0 → Ω → ℝ) (N : ℕ) (l : ι) (u : ℝ)
    (z : Ω × (ℕ × ι → KMTPoissonCode)) : ℝ :=
  β N l u.toNNReal z.1

/-- The KMT coefficient of channel `l` at population size `N`. -/
def transferredXi (β : ℕ → ι → ℝ≥0 → Ω → ℝ) (N : ℕ) (l : ι)
    (z : Ω × (ℕ × ι → KMTPoissonCode)) : ℝ :=
  (kmtCodeXi (brownianCodeOf (β N l) z.1) (z.2 (N, l))).toReal

/-- The fixed-size comparison coefficient at population size `N`. -/
def transferredKurtzBeta {d : ℕ} (v : ι → Fin d → ℝ) (eps : ι → ℝ) (Gamma M T : ℝ)
    (β : ℕ → ι → ℝ≥0 → Ω → ℝ) (N : ℕ) : Ω × (ℕ × ι → KMTPoissonCode) → ℝ :=
  fixedScaleKurtzBeta v eps Gamma M T (fun l => transferredXi β N l) (transferredBrownian β N)

/-- The pair code (Brownian code, Poisson code) of the `N`th family. -/
def familyPairCode (β : ℕ → ι → ℝ≥0 → Ω → ℝ) (N : ℕ) (z : Ω × (ℕ × ι → KMTPoissonCode)) :
    ι → KMTBrownianCode × KMTPoissonCode :=
  fun l => (brownianCodeOf (β N l) z.1, z.2 (N, l))

/-- The KMT coefficient read on a pair code. -/
def pairCodeXi (l : ι) (p : ι → KMTBrownianCode × KMTPoissonCode) : ℝ :=
  (kmtCodeXi (p l).1 (p l).2).toReal

/-- The Brownian path read on a pair code. -/
def pairCodeBrownian (l : ι) (t : ℝ) (p : ι → KMTBrownianCode × KMTPoissonCode) : ℝ :=
  codeEval (p l).1 t

theorem measurable_pairCodeXi (l : ι) : Measurable (pairCodeXi (ι := ι) l) :=
  (measurable_kmtCodeXi.comp (measurable_pi_apply l)).ennreal_toReal

theorem measurable_pairCodeBrownian (l : ι) (t : ℝ) :
    Measurable (pairCodeBrownian (ι := ι) l t) :=
  (measurable_codeEval t).comp (measurable_fst.comp (measurable_pi_apply l))

theorem measurable_familyPairCode_coord {β : ℕ → ι → ℝ≥0 → Ω → ℝ}
    (hβ : ∀ N l t, Measurable (β N l t)) (N : ℕ) (l : ι) :
    Measurable fun z : Ω × (ℕ × ι → KMTPoissonCode) =>
      (brownianCodeOf (β N l) z.1, z.2 (N, l)) :=
  ((measurable_brownianCodeOf (hβ N l)).comp measurable_fst).prodMk
    ((measurable_pi_apply (N, l)).comp measurable_snd)

theorem measurable_familyPairCode {β : ℕ → ι → ℝ≥0 → Ω → ℝ}
    (hβ : ∀ N l t, Measurable (β N l t)) (N : ℕ) :
    Measurable (familyPairCode β N) :=
  measurable_pi_lambda _ fun l => measurable_familyPairCode_coord hβ N l

theorem measurable_transferredXi {β : ℕ → ι → ℝ≥0 → Ω → ℝ}
    (hβ : ∀ N l t, Measurable (β N l t)) (N : ℕ) (l : ι) :
    Measurable (transferredXi β N l) :=
  (measurable_kmtCodeXi.comp (measurable_familyPairCode_coord hβ N l)).ennreal_toReal

theorem measurable_transferredBrownian {β : ℕ → ι → ℝ≥0 → Ω → ℝ}
    (hβ : ∀ N l t, Measurable (β N l t)) (N : ℕ) (l : ι) (u : ℝ) :
    Measurable (transferredBrownian β N l u) :=
  (hβ N l _).comp measurable_fst

/-- The fixed-size code factors through the pair code of the `N`th family. -/
theorem fixedScaleKurtzCode_transferred (β : ℕ → ι → ℝ≥0 → Ω → ℝ) (N : ℕ)
    (z : Ω × (ℕ × ι → KMTPoissonCode)) :
    fixedScaleKurtzCode (fun l => transferredXi β N l) (transferredBrownian β N) z =
      fixedScaleKurtzCode pairCodeXi pairCodeBrownian (familyPairCode β N z) := by
  refine Prod.ext rfl ?_
  exact dyadicEntropyCommonReal_congr fun l j m k =>
    (codeEval_brownianCodeOf_dyadic (β N l) z.1 j m k).symm

variable {P : Measure Ω} [IsProbabilityMeasure P] {β : ℕ → ι → ℝ≥0 → Ω → ℝ}
  {hβ : ∀ N l t, Measurable (β N l t)}

theorem kmtFamilyMeasure_map_fst : (kmtFamilyMeasure P β hβ).map Prod.fst = P :=
  kmtArray_fst

theorem kmtFamily_coordinate_jointLaw {N : ℕ} {l : ι} [IsPreBrownian (β N l) P] :
    (kmtFamilyMeasure P β hβ).map (fun z => (brownianCodeOf (β N l) z.1, z.2 (N, l))) =
      kmtReferenceJointLaw := by
  have hlaw : P.map (fun ω => familyBrownianCode β ω (N, l)) = kmtBrownianCodeLaw :=
    kmtBrownianCodeLaw_eq (β := β N l)
  unfold kmtFamilyMeasure kmtArrayTransferMeasure
  rw [show (fun z : Ω × (ℕ × ι → KMTPoissonCode) =>
      (brownianCodeOf (β N l) z.1, z.2 (N, l))) =
      fun z => (familyBrownianCode β z.1 (N, l), z.2 (N, l)) from rfl,
    map_marked_coord P kmtConditionalPoisson (familyBrownianCode β)
      (measurable_familyBrownianCode hβ) (N, l), hlaw, kmtConditionalPoisson_disintegrates]

/-- The pair code of the `N`th family has the product of reference laws. -/
theorem map_familyPairCode {N : ℕ} (hB : ∀ l, IsPreBrownian (β N l) P)
    (hind : iIndepFun (fun (l : ι) ω => fun t => β N l t ω) P) :
    (kmtFamilyMeasure P β hβ).map (familyPairCode β N) =
      Measure.pi fun _ : ι => kmtReferenceJointLaw := by
  have hX : iIndepFun (fun (l : ι) ω => familyBrownianCode β ω (N, l)) P :=
    brownianCode_iIndep_of_independentProcesses hind
  have hpairs := iIndepFun_pairs_of_independent_marking P kmtConditionalPoisson
    (familyBrownianCode β) (fun l => (N, l)) (measurable_familyBrownianCode hβ)
    (fun _ _ h => (Prod.mk.inj h).2) hX
  have hmap := hpairs.map_fun_eq_pi_map
    (fun l => (measurable_familyPairCode_coord hβ N l).aemeasurable)
  have hpair : familyPairCode β N =
      fun z l => (familyBrownianCode β z.1 (N, l), z.2 (N, l)) := rfl
  calc (kmtFamilyMeasure P β hβ).map (familyPairCode β N)
      = Measure.pi fun l : ι => (kmtFamilyMeasure P β hβ).map
          (fun z => (brownianCodeOf (β N l) z.1, z.2 (N, l))) := by
        rw [hpair]
        exact hmap
    _ = Measure.pi fun _ : ι => kmtReferenceJointLaw := by
        congr 1
        funext l
        haveI := hB l
        exact kmtFamily_coordinate_jointLaw

/-- The Brownian code of one coordinate is pre-Brownian coded, so its KMT coefficient has the
reference law. -/
theorem kmtFamily_coordinate_Xi_law {N : ℕ} {l : ι} [IsPreBrownian (β N l) P] :
    (kmtFamilyMeasure P β hβ).map
        (fun z => kmtCodeXi (brownianCodeOf (β N l) z.1) (z.2 (N, l))) =
      allTimeKMTMeasure.map allTimeKMTXi := by
  have hm := measurable_familyPairCode_coord hβ N l
  have hu : Measurable (Function.uncurry kmtCodeXi) := measurable_kmtCodeXi
  rw [show (fun z : Ω × (ℕ × ι → KMTPoissonCode) =>
      kmtCodeXi (brownianCodeOf (β N l) z.1) (z.2 (N, l))) =
      Function.uncurry kmtCodeXi ∘
        fun z => (brownianCodeOf (β N l) z.1, z.2 (N, l)) from rfl,
    ← Measure.map_map hu hm, kmtFamily_coordinate_jointLaw]
  unfold kmtReferenceJointLaw
  rw [Measure.map_map hu measurable_referencePair]
  congr 1
  funext ω
  exact kmtCodeXi_reference ω

theorem transferredXi_hasPositiveExpMoment {N : ℕ} {l : ι} [IsPreBrownian (β N l) P] :
    HasPositiveExpMoment (kmtFamilyMeasure P β hβ) (transferredXi β N l) := by
  have hγ := allTimeKurtzGamma_pos
  have hθ0 : 0 < allTimeKurtzGamma / 2 := half_pos hγ
  have hθγ : allTimeKurtzGamma / 2 < allTimeKurtzGamma := half_lt_self hγ
  refine ⟨allTimeKurtzGamma / 2, hθ0, ?_⟩
  have hint := (integral_exp_allTimeKMTXi_le hθ0 hθγ).1
  have hF : Measurable fun x : ℝ≥0∞ => Real.exp (allTimeKurtzGamma / 2 * x.toReal) := by
    fun_prop
  have hg := measurable_kmtCodeXi.comp (measurable_familyPairCode_coord hβ N l)
  have hid : IdentDistrib (fun z : Ω × (ℕ × ι → KMTPoissonCode) =>
      kmtCodeXi (brownianCodeOf (β N l) z.1) (z.2 (N, l))) allTimeKMTXi
      (kmtFamilyMeasure P β hβ) allTimeKMTMeasure :=
    ⟨hg.aemeasurable, measurable_allTimeKMTXi.aemeasurable,
      kmtFamily_coordinate_Xi_law (hβ := hβ) (N := N) (l := l)⟩
  exact (hid.comp hF).integrable_iff.2 hint

/-- The all-time KMT bound for one coordinate `(N, l)` of the marked space. -/
theorem kmtFamily_bound_ae {N : ℕ} {l : ι} [IsPreBrownian (β N l) P]
    (hcont : ∀ᵐ ω ∂P, Continuous fun t => β N l t ω) :
    ∀ᵐ z ∂kmtFamilyMeasure P β hβ, ∀ t : ℝ≥0,
      |(cellPath (t : ℝ) (z.2 (N, l)) : ℝ) - (t : ℝ) - β N l t z.1| ≤
        (kmtCodeXi (brownianCodeOf (β N l) z.1) (z.2 (N, l))).toReal *
          Real.log (max 2 (t : ℝ)) := by
  have hm : Measurable (fun z : Ω × (ℕ × ι → KMTPoissonCode) => (z.1, z.2 (N, l))) :=
    measurable_fst.prodMk ((measurable_pi_apply (N, l)).comp measurable_snd)
  have hmeas : Measurable (brownianCodeOf (β N l)) := measurable_brownianCodeOf (hβ N l)
  have hb' := kmtTransfer_bound_ae_of_preBrownian (hβ N l) hcont
  refine ae_of_ae_map (p := fun w : Ω × KMTPoissonCode => ∀ t : ℝ≥0,
      |(cellPath (t : ℝ) w.2 : ℝ) - (t : ℝ) - β N l t w.1| ≤
        (kmtCodeXi (brownianCodeOf (β N l) w.1) w.2).toReal * Real.log (max 2 (t : ℝ)))
    hm.aemeasurable ?_
  have hT : kmtTransferMeasure P (brownianCodeOf (β N l)) hmeas =
      kmtTransferMeasure P (fun ω => familyBrownianCode β ω (N, l))
        (measurable_coord (measurable_familyBrownianCode hβ) (N, l)) :=
    kmtTransferMeasure_congr rfl
  unfold kmtFamilyMeasure
  rw [kmtArray_coordinate_transfer (N, l), ← hT]
  exact hb'

end Family

/-! ## The family theorem -/

/-- Kurtz Theorem 3.3(a) for every population size `N ≥ 2` on one probability space.

For each `N ≥ 2`, `β N` is a finite family of independent pre-Brownian paths with continuous
sample paths on `P`. The marked space `kmtFamilyMeasure P β hβmeas` attaches the KMT cell paths
`transferredCellPath N l` to every coordinate. The carried premises are the deterministic rate
premises and, at each `N ≥ 2`, the chain and diffusion equations with path regularity
(`FixedScaleKurtzPaths`) for the transferred cell and Brownian paths.

The coefficient `transferredKurtzBeta` is the explicit fixed-size coefficient. Its laws are
derived, not assumed, to coincide for all `N ≥ 2`; it has one exponential moment uniform in
`N`; and the comparison bound holds for all `N ≥ 2` and `t ∈ [0,T]` on one conull set. -/
theorem transferred_finiteChannelKurtz_family
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] {d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (β : ℕ → ι → ℝ≥0 → Ω → ℝ)
    (hβmeas : ∀ N l t, Measurable (β N l t))
    (hβB : ∀ N, 2 ≤ N → ∀ l, IsPreBrownian (β N l) P)
    (hβcont : ∀ N, 2 ≤ N → ∀ l, ∀ᵐ ω ∂P, Continuous fun t => β N l t ω)
    (hβind : ∀ N, 2 ≤ N → iIndepFun (fun (l : ι) ω => fun t => β N l t ω) P)
    (f : ι → (Fin d → ℝ) → ℝ) (fN : ℕ → ι → (Fin d → ℝ) → ℝ)
    (v : ι → Fin d → ℝ) (eps : ι → ℝ) (Gamma M T : ℝ)
    (Xchain Z : ℕ → Ω × (ℕ × ι → KMTPoissonCode) → ℝ → Fin d → ℝ)
    (x0 : ℕ → Ω × (ℕ × ι → KMTPoissonCode) → Fin d → ℝ)
    (heps : ∀ l, 0 ≤ eps l)
    (hGamma : 0 ≤ Gamma) (hM : 0 ≤ M) (hT : 0 ≤ T)
    (hf0 : ∀ l x, 0 ≤ f l x)
    (hfB : ∀ l x, f l x ≤ eps l)
    (h319 : ∀ l x y, |f l x - f l y| ≤ eps l * M * ‖x - y‖)
    (hfN0 : ∀ N, 2 ≤ N → ∀ l x, 0 ≤ fN N l x)
    (h31 : ∀ N, 2 ≤ N → ∀ l x, fN N l x ≤ eps l)
    (h32 : ∀ N, 2 ≤ N → ∀ l x, |f l x - fN N l x| ≤ Gamma * eps l / (N : ℝ))
    (hPaths : ∀ N, 2 ≤ N → ∀ᵐ z ∂kmtFamilyMeasure P β hβmeas,
      FixedScaleKurtzPaths N f (fN N) v T (transferredCellPath N) (transferredBrownian β N)
        (Xchain N) (Z N) (x0 N) z) :
    ∃ lambdaBeta CBeta : ℝ, 0 < lambdaBeta ∧ 0 ≤ CBeta ∧
      (∀ N, 2 ≤ N → Measurable (transferredKurtzBeta v eps Gamma M T β N)) ∧
      (∀ N, 2 ≤ N → ∀ z, 0 ≤ transferredKurtzBeta v eps Gamma M T β N z) ∧
      (∀ N N', 2 ≤ N → 2 ≤ N' →
        IdentDistrib (transferredKurtzBeta v eps Gamma M T β N)
          (transferredKurtzBeta v eps Gamma M T β N')
          (kmtFamilyMeasure P β hβmeas) (kmtFamilyMeasure P β hβmeas)) ∧
      (∀ N, 2 ≤ N →
        Integrable (fun z => Real.exp (lambdaBeta * transferredKurtzBeta v eps Gamma M T β N z))
          (kmtFamilyMeasure P β hβmeas) ∧
        ∫ z, Real.exp (lambdaBeta * transferredKurtzBeta v eps Gamma M T β N z)
          ∂kmtFamilyMeasure P β hβmeas ≤ CBeta) ∧
      (∀ᵐ z ∂kmtFamilyMeasure P β hβmeas, ∀ N, 2 ≤ N → ∀ t ∈ Icc (0 : ℝ) T,
        ‖Xchain N z t - Z N z t‖ ≤
          transferredKurtzBeta v eps Gamma M T β N z * Real.log (N : ℝ) / (N : ℝ)) := by
  classical
  set Q := kmtFamilyMeasure P β hβmeas with hQ
  set betaT := transferredKurtzBeta v eps Gamma M T β with hbetaT
  have hfst : Q.map Prod.fst = P := kmtFamilyMeasure_map_fst
  have hmain : ∀ N, 2 ≤ N →
      Measurable (betaT N) ∧ (∀ z, 0 ≤ betaT N z) ∧ HasPositiveExpMoment Q (betaT N) ∧
      (∀ᵐ z ∂Q, ∀ t ∈ Icc (0 : ℝ) T,
        ‖Xchain N z t - Z N z t‖ ≤ betaT N z * Real.log (N : ℝ) / (N : ℝ)) := by
    intro N hN
    have hW : ∀ l (j : ℕ), DyadicBrownianOn Q (transferredBrownian β N l) ((2 : ℝ) ^ j) := by
      intro l j
      haveI := hβB N hN l
      haveI : IsPreBrownian (fun t z => β N l t z.1) Q := isPreBrownian_comp_fst hfst
      have hcontQ : ∀ᵐ z ∂Q, Continuous fun t => β N l t z.1 := by
        have h := hβcont N hN l
        rw [← hfst] at h
        exact ae_of_ae_map measurable_fst.aemeasurable h
      exact dyadicBrownianOn_of_isPreBrownian
        (β := fun t (z : Ω × (ℕ × ι → KMTPoissonCode)) => β N l t z.1)
        (fun t => (hβmeas N l t).comp measurable_fst) hcontQ (by positivity)
    have hXiExp : ∀ l, HasPositiveExpMoment Q (transferredXi β N l) := by
      intro l
      haveI := hβB N hN l
      exact transferredXi_hasPositiveExpMoment
    have hKMT : ∀ᵐ z ∂Q, ∀ l u, 0 ≤ u →
        |transferredCellPath N l u z - u - transferredBrownian β N l u z| ≤
          transferredXi β N l z * Real.log (max 2 u) := by
      rw [ae_all_iff]
      intro l
      haveI := hβB N hN l
      filter_upwards [kmtFamily_bound_ae (hβ := hβmeas) (hβcont N hN l)] with z hz u hu
      have h := hz u.toNNReal
      rw [Real.coe_toNNReal u hu] at h
      exact h
    exact finiteChannelKurtz_at Q N f (fN N) v eps Gamma M T
      (transferredCellPath N) (transferredBrownian β N) (fun l => transferredXi β N l)
      (Xchain N) (Z N) (x0 N) hN heps hGamma hM hT hf0 hfB (hfN0 N hN) (h31 N hN)
      (h32 N hN) h319 hW (measurable_transferredXi hβmeas N)
      (fun _ _ => ENNReal.toReal_nonneg) hXiExp hKMT (hPaths N hN)
  have hcode : ∀ N, 2 ≤ N →
      Q.map (fixedScaleKurtzCode (fun l => transferredXi β N l) (transferredBrownian β N)) =
        (Measure.pi fun _ : ι => kmtReferenceJointLaw).map
          (fixedScaleKurtzCode pairCodeXi pairCodeBrownian) := by
    intro N hN
    have hG : Measurable (fixedScaleKurtzCode (pairCodeXi (ι := ι)) pairCodeBrownian) :=
      measurable_fixedScaleKurtzCode measurable_pairCodeXi measurable_pairCodeBrownian
    rw [show fixedScaleKurtzCode (fun l => transferredXi β N l) (transferredBrownian β N) =
        fixedScaleKurtzCode pairCodeXi pairCodeBrownian ∘ familyPairCode β N from
          funext (fixedScaleKurtzCode_transferred β N),
      ← Measure.map_map hG (measurable_familyPairCode hβmeas N),
      map_familyPairCode (hβB N hN) (hβind N hN)]
  have hident : ∀ N N', 2 ≤ N → 2 ≤ N' → IdentDistrib (betaT N) (betaT N') Q Q := by
    intro N N' hN hN'
    exact
      { aemeasurable_fst := (hmain N hN).1.aemeasurable
        aemeasurable_snd := (hmain N' hN').1.aemeasurable
        map_eq := fixedScaleKurtzBeta_law_of_code_law Q Q v eps Gamma M T _ _ _ _
          (measurable_transferredXi hβmeas N) (measurable_transferredXi hβmeas N')
          (measurable_transferredBrownian hβmeas N) (measurable_transferredBrownian hβmeas N')
          ((hcode N hN).trans (hcode N' hN').symm) }
  obtain ⟨η, hη, hint2⟩ := (hmain 2 le_rfl).2.2.1
  refine ⟨η, ∫ z, Real.exp (η * betaT 2 z) ∂Q, hη,
    integral_nonneg fun _ => (Real.exp_pos _).le, fun N hN => (hmain N hN).1,
    fun N hN => (hmain N hN).2.1, hident, ?_, ?_⟩
  · intro N hN
    have hu : Measurable fun x : ℝ => Real.exp (η * x) :=
      Real.measurable_exp.comp (measurable_const.mul measurable_id)
    have hid := (hident N 2 hN le_rfl).comp hu
    exact ⟨hid.integrable_iff.2 hint2, hid.integral_eq.le⟩
  · rw [ae_all_iff]
    intro N
    by_cases hN : 2 ≤ N
    · filter_upwards [(hmain N hN).2.2.2] with z hz _ using hz
    · exact Filter.Eventually.of_forall fun z h => absurd h hN

end Ripple.Kurtz.StrongApprox.KMTTransfer
