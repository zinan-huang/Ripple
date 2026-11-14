import Ripple.Stochastic.GaussianChannelExponential
import Ripple.Stochastic.BrownianMotion.Gaussian.BrownianMotion
import Mathlib.MeasureTheory.Order.Group.Lattice

/-!
# Bounded predictable vector Gaussian exponential factors

The coefficient vector may inspect the entire past. The whole fresh Gaussian
increment vector is independent of that past, and its coordinates are mutually
independent. A product-law integral freezes the entire coefficient vector.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace Ripple.Stochastic.VectorStochasticExponential
open GaussianExponentialStep GaussianChannelExponential

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  [IsProbabilityMeasure P] {d : ℕ}

/-- The compensated exponential of one deterministic vector Gaussian step. -/
noncomputable def vectorFactor (a : Fin d → ℝ) (v : Fin d → ℝ≥0)
    (x : Fin d → ℝ) : ℝ := ∏ j, gaussianFactor (a j) (v j) (x j)

/-- The compensated vector factor is a measurable function of the increment vector. -/
theorem measurable_vectorFactor (a : Fin d → ℝ) (v : Fin d → ℝ≥0) :
    Measurable (vectorFactor a v) :=
  Finset.measurable_prod _
    (fun j _ => (measurable_gaussianFactor (a j) (v j)).comp (measurable_pi_apply j))

/-- A coefficient-independent integrable envelope for every bounded vector coefficient. -/
noncomputable def vectorEnvelope (K : ℝ) (x : Fin d → ℝ) : ℝ :=
  ∏ j, (Real.exp (K * x j) + Real.exp (-K * x j))

theorem vectorFactor_nonneg (a : Fin d → ℝ) (v : Fin d → ℝ≥0) (x : Fin d → ℝ) :
    0 ≤ vectorFactor a v x := by
  unfold vectorFactor gaussianFactor
  positivity

theorem vectorEnvelope_nonneg (K : ℝ) (x : Fin d → ℝ) : 0 ≤ vectorEnvelope K x := by
  unfold vectorEnvelope
  positivity

/-- Compensation is nonpositive, and bounded coefficients are dominated coordinatewise. -/
theorem vectorFactor_le_envelope (a : Fin d → ℝ) (v : Fin d → ℝ≥0)
    (x : Fin d → ℝ) {K : ℝ} (ha : ∀ j, |a j| ≤ K) :
    vectorFactor a v x ≤ vectorEnvelope K x := by
  unfold vectorFactor vectorEnvelope
  apply Finset.prod_le_prod
  · intro j hj
    exact (Real.exp_pos _).le
  · intro j hj
    unfold gaussianFactor
    have hfirst : Real.exp (a j * x j - (a j) ^ 2 * (v j : ℝ) / 2) ≤
        Real.exp (a j * x j) := by
      apply Real.exp_le_exp.mpr
      exact sub_le_self _ (div_nonneg
        (mul_nonneg (sq_nonneg (a j)) (v j).coe_nonneg) (by norm_num))
    apply hfirst.trans
    obtain ⟨hlo, hhi⟩ := abs_le.mp (ha j)
    rcases le_total 0 (x j) with hx | hx
    · exact le_add_of_le_of_nonneg
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hhi hx)) (Real.exp_nonneg _)
    · exact le_add_of_nonneg_of_le (Real.exp_nonneg _)
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right hlo hx))

private theorem integrable_comp_law {Y : Ω → ℝ} {ν : Measure ℝ}
    (hY : HasLaw Y ν P) {f : ℝ → ℝ} (hf : Integrable f ν) :
    Integrable (fun ω => f (Y ω)) P :=
  Integrable.comp_aemeasurable (hY.map_eq ▸ hf) hY.aemeasurable

/-- The product envelope is integrable by coordinate independence, before any freezing. -/
theorem vectorEnvelope_integrable (X : Fin d → Ω → ℝ)
    (hX : ∀ j, Measurable (X j)) (v : Fin d → ℝ≥0)
    (hLaw : ∀ j, HasLaw (X j) (gaussianReal 0 (v j)) P)
    (hind : iIndepFun X P) (K : ℝ) :
    Integrable (fun ω => vectorEnvelope K (fun j => X j ω)) P := by
  let G : Fin d → Ω → ℝ := fun j ω => Real.exp (K * X j ω) + Real.exp (-K * X j ω)
  have hG : ∀ j, Measurable (G j) := fun j =>
    ((hX j).const_mul K).exp.add (((hX j).const_mul (-K)).exp)
  have hGint : ∀ j, Integrable (G j) P := fun j =>
    (integrable_comp_law (hLaw j) (integrable_exp_mul_gaussianReal K)).add
      (integrable_comp_law (hLaw j) (integrable_exp_mul_gaussianReal (-K)))
  have hGind : iIndepFun G P := hind.comp
    (fun j x => Real.exp (K * x) + Real.exp (-K * x)) (fun j => by fun_prop)
  exact integrable_prod_of_independent G hG hGint hGind Finset.univ

/-- An arbitrary integrable past weight times the bounded random-coefficient factor is integrable.
The coefficient needs ambient measurability here; only the weight needs past measurability. -/
theorem weighted_vectorFactor_integrable {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    (c : Ω → Fin d → ℝ) (hc : Measurable[mΩ] c) {K : ℝ} (hK : ∀ ω j, |c ω j| ≤ K)
    (U : Ω → ℝ) (hU : StronglyMeasurable[m] U) (hUint : Integrable U P)
    (X : Fin d → Ω → ℝ) (hX : ∀ j, Measurable[mΩ] (X j)) (v : Fin d → ℝ≥0)
    (hLaw : ∀ j, HasLaw (X j) (gaussianReal 0 (v j)) P)
    (hind : iIndepFun X P)
    (hpast : Indep (MeasurableSpace.comap (fun ω j => X j ω) inferInstance) m P) :
    Integrable (fun ω => U ω * vectorFactor (c ω) v (fun j => X j ω)) P := by
  letI : MeasurableSpace Ω := mΩ
  let V : Ω → Fin d → ℝ := fun ω j => X j ω
  let B : Ω → ℝ := fun ω => vectorEnvelope K (V ω)
  have hVm : Measurable V := by fun_prop
  have hBpast : Measurable[MeasurableSpace.comap V inferInstance] B :=
    (by unfold vectorEnvelope; fun_prop : Measurable (vectorEnvelope (d := d) K)).comp
      (fun s hs => ⟨s, hs, rfl⟩ : Measurable[MeasurableSpace.comap V inferInstance] V)
  have hUB : IndepFun (fun ω => |U ω|) B P := by
    apply (IndepFun_iff_Indep _ _ _).mpr
    exact (indep_of_indep_of_le_right
      (indep_of_indep_of_le_left hpast hBpast.comap_le) (measurable_abs.comp hU.measurable).comap_le).symm
  have hBint : Integrable B P := vectorEnvelope_integrable X hX v hLaw hind K
  have hdom : Integrable (fun ω => |U ω| * B ω) P := hUB.integrable_mul hUint.abs hBint
  apply Integrable.mono' hdom
  · have hUm : Measurable U := (hU.mono hm).measurable
    unfold vectorFactor gaussianFactor
    fun_prop
  · apply Eventually.of_forall
    intro ω
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (vectorFactor_nonneg _ _ _)]
    exact mul_le_mul_of_nonneg_left (vectorFactor_le_envelope _ _ _ (hK ω)) (abs_nonneg _)

/-- Freezing identity for a bounded random vector coefficient and an integrable past weight. -/
theorem weighted_vectorFactor_setIntegral {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    (c : Ω → Fin d → ℝ) (hc : Measurable[m] c) {K : ℝ} (hK : ∀ ω j, |c ω j| ≤ K)
    (U : Ω → ℝ) (hU : StronglyMeasurable[m] U) (hUint : Integrable U P)
    (X : Fin d → Ω → ℝ) (hX : ∀ j, Measurable[mΩ] (X j)) (v : Fin d → ℝ≥0)
    (hLaw : ∀ j, HasLaw (X j) (gaussianReal 0 (v j)) P)
    (hind : iIndepFun X P)
    (hpast : Indep (MeasurableSpace.comap (fun ω j => X j ω) inferInstance) m P)
    {A : Set Ω} (hA : MeasurableSet[m] A) :
    (∫ ω in A, U ω * vectorFactor (c ω) v (fun j => X j ω) ∂P) = ∫ ω in A, U ω ∂P := by
  letI : MeasurableSpace Ω := mΩ
  classical
  let V : Ω → Fin d → ℝ := fun ω j => X j ω
  let Y : Ω → (Fin d → ℝ) × ℝ := fun ω => (c ω, A.indicator U ω)
  let H : ((Fin d → ℝ) × ℝ) × (Fin d → ℝ) → ℝ :=
    fun p => p.1.2 * vectorFactor p.1.1 v p.2
  have hAm : MeasurableSet A := hm A hA
  have hcambient : Measurable c := hc.mono hm le_rfl
  have hVm : Measurable V := by fun_prop
  have hYm : Measurable Y := hcambient.prodMk ((hU.mono hm).measurable.indicator hAm)
  have hYpast : Measurable[m] Y := hc.prodMk (hU.measurable.indicator hA)
  have hHm : Measurable H := by unfold H vectorFactor gaussianFactor; fun_prop
  have hYV : IndepFun Y V P :=
    (indep_of_indep_of_le_right hpast hYpast.comap_le).symm
  have hjoint : P.map (fun ω => (Y ω, V ω)) = (P.map Y).prod (P.map V) :=
    (indepFun_iff_map_prod_eq_prod_map_map hYm.aemeasurable hVm.aemeasurable).mp hYV
  have hHVint : Integrable (fun ω => H (Y ω, V ω)) P :=
    weighted_vectorFactor_integrable hm c hcambient hK (A.indicator U)
      (hU.indicator hA) (hUint.indicator hAm) X hX v hLaw hind hpast
  have hHint : Integrable H ((P.map Y).prod (P.map V)) := by
    rw [← hjoint, integrable_map_measure hHm.aestronglyMeasurable
      (hYm.prodMk hVm).aemeasurable]
    exact hHVint
  have hinner (y : (Fin d → ℝ) × ℝ) : (∫ x, H (y, x) ∂(P.map V)) = y.2 := by
    change (∫ x, y.2 * vectorFactor y.1 v x ∂(P.map V)) = y.2
    rw [integral_const_mul, integral_map hVm.aemeasurable
      ((measurable_vectorFactor y.1 v).aestronglyMeasurable :
        AEStronglyMeasurable (vectorFactor y.1 v) (P.map V))]
    have hmean := (gaussian_product_normalized X hX v hLaw hind y.1).2
    change y.2 * (∫ ω, ∏ j, gaussianFactor (y.1 j) (v j) (X j ω) ∂P) = y.2
    rw [hmean, mul_one]
  rw [← integral_indicator hAm, ← integral_indicator hAm]
  have hleft : (A.indicator (fun ω => U ω * vectorFactor (c ω) v (V ω))) =
      fun ω => H (Y ω, V ω) := by
    funext ω
    by_cases hω : ω ∈ A <;> simp [H, Y, hω]
  rw [hleft]
  change (∫ ω, H (Y ω, V ω) ∂P) = ∫ ω, (Y ω).2 ∂P
  rw [← integral_map (hYm.prodMk hVm).aemeasurable hHm.aestronglyMeasurable,
    hjoint, integral_prod H hHint]
  rw [← integral_map hYm.aemeasurable
    (measurable_snd.aestronglyMeasurable :
      AEStronglyMeasurable (fun y : (Fin d → ℝ) × ℝ => y.2) (P.map Y))]
  exact integral_congr_ae (Eventually.of_forall hinner)

/-- Actual conditional Gaussian freezing for arbitrary bounded predictable vector coefficients.
The weight may be any integrable past variable; no MGF or martingale identity is assumed. -/
theorem weighted_vectorFactor_condExp {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    (c : Ω → Fin d → ℝ) (hc : Measurable[m] c) {K : ℝ} (hK : ∀ ω j, |c ω j| ≤ K)
    (U : Ω → ℝ) (hU : StronglyMeasurable[m] U) (hUint : Integrable U P)
    (X : Fin d → Ω → ℝ) (hX : ∀ j, Measurable[mΩ] (X j)) (v : Fin d → ℝ≥0)
    (hLaw : ∀ j, HasLaw (X j) (gaussianReal 0 (v j)) P)
    (hind : iIndepFun X P)
    (hpast : Indep (MeasurableSpace.comap (fun ω j => X j ω) inferInstance) m P) :
    Integrable (fun ω => U ω * vectorFactor (c ω) v (fun j => X j ω)) P ∧
      P[fun ω => U ω * vectorFactor (c ω) v (fun j => X j ω) | m] =ᵐ[P] U := by
  letI : MeasurableSpace Ω := mΩ
  have hint := weighted_vectorFactor_integrable hm c (hc.mono hm le_rfl) hK
    U hU hUint X hX v hLaw hind hpast
  refine ⟨hint, ?_⟩
  apply (ae_eq_condExp_of_forall_setIntegral_eq hm hint
    (fun A _ _ => hUint.integrableOn) (fun A hA _ => ?_) hU.aestronglyMeasurable).symm
  exact (weighted_vectorFactor_setIntegral hm c hc hK U hU hUint X hX v hLaw hind hpast hA).symm

/-- The unweighted normalized vector factor has conditional mean one. -/
theorem vectorFactor_condExp_eq_one {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    (c : Ω → Fin d → ℝ) (hc : Measurable[m] c) {K : ℝ} (hK : ∀ ω j, |c ω j| ≤ K)
    (X : Fin d → Ω → ℝ) (hX : ∀ j, Measurable[mΩ] (X j)) (v : Fin d → ℝ≥0)
    (hLaw : ∀ j, HasLaw (X j) (gaussianReal 0 (v j)) P)
    (hind : iIndepFun X P)
    (hpast : Indep (MeasurableSpace.comap (fun ω j => X j ω) inferInstance) m P) :
    Integrable (fun ω => vectorFactor (c ω) v (fun j => X j ω)) P ∧
      P[fun ω => vectorFactor (c ω) v (fun j => X j ω) | m] =ᵐ[P] fun _ => (1 : ℝ) := by
  letI : MeasurableSpace Ω := mΩ
  simpa only [one_mul] using weighted_vectorFactor_condExp hm c hc hK
    (fun _ => (1 : ℝ)) stronglyMeasurable_const (integrable_const _) X hX v hLaw hind hpast

/-- One vector Brownian increment, with the sum of channel compensators. -/
noncomputable def incrementFactor (B : Fin d → ℝ≥0 → Ω → ℝ)
    (r t : ℝ≥0) (c : Ω → Fin d → ℝ) (ω : Ω) : ℝ :=
  vectorFactor (c ω) (fun _ => t - r) (fun j => B j t ω - B j r ω)

/-- A vector coefficient is held fixed on a time cell and both endpoints are clamped. -/
noncomputable def vectorCell (B : Fin d → ℝ≥0 → Ω → ℝ)
    (a b : ℝ≥0) (c : Ω → Fin d → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  incrementFactor B (min a t) (min b t) c ω

@[simp] theorem incrementFactor_self (B : Fin d → ℝ≥0 → Ω → ℝ)
    (r : ℝ≥0) (c : Ω → Fin d → ℝ) (ω : Ω) : incrementFactor B r r c ω = 1 := by
  simp [incrementFactor, vectorFactor, gaussianFactor]

theorem vectorCell_of_le_left (B : Fin d → ℝ≥0 → Ω → ℝ)
    {a b : ℝ≥0} (hab : a ≤ b) (c : Ω → Fin d → ℝ) {t : ℝ≥0}
    (ht : t ≤ a) (ω : Ω) : vectorCell B a b c t ω = 1 := by
  rw [vectorCell, min_eq_right ht, min_eq_right (ht.trans hab), incrementFactor_self]

theorem vectorCell_of_mem (B : Fin d → ℝ≥0 → Ω → ℝ)
    {a b t : ℝ≥0} (hat : a ≤ t) (htb : t ≤ b) (c : Ω → Fin d → ℝ) (ω : Ω) :
    vectorCell B a b c t ω = incrementFactor B a t c ω := by
  rw [vectorCell, min_eq_left hat, min_eq_right htb]

theorem vectorCell_of_ge_right (B : Fin d → ℝ≥0 → Ω → ℝ)
    {a b : ℝ≥0} (hab : a ≤ b) (c : Ω → Fin d → ℝ) {t : ℝ≥0}
    (hbt : b ≤ t) (ω : Ω) : vectorCell B a b c t ω = incrementFactor B a b c ω := by
  rw [vectorCell, min_eq_left (hab.trans hbt), min_eq_left hbt]

/-- The product formula is the exponential with the actual summed channel bracket. -/
theorem incrementFactor_eq_exp_sum (B : Fin d → ℝ≥0 → Ω → ℝ)
    {r t : ℝ≥0} (hrt : r ≤ t) (c : Ω → Fin d → ℝ) (ω : Ω) :
    incrementFactor B r t c ω =
      Real.exp ((∑ j, c ω j * (B j t ω - B j r ω)) -
        (∑ j, (c ω j) ^ 2 * ((t : ℝ) - (r : ℝ))) / 2) := by
  unfold incrementFactor vectorFactor
  rw [gaussian_product_eq_exp_sum]
  simp only [NNReal.coe_sub hrt]

/-- Splitting a time interval multiplies the compensated factors coordinatewise. -/
theorem incrementFactor_split (B : Fin d → ℝ≥0 → Ω → ℝ)
    {r s t : ℝ≥0} (hrs : r ≤ s) (hst : s ≤ t) (c : Ω → Fin d → ℝ) (ω : Ω) :
    incrementFactor B r t c ω = incrementFactor B r s c ω * incrementFactor B s t c ω := by
  classical
  unfold incrementFactor vectorFactor
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j hj
  unfold gaussianFactor
  rw [NNReal.coe_sub (hrs.trans hst), NNReal.coe_sub hrs, NNReal.coe_sub hst,
    ← Real.exp_add]
  congr 1
  ring

/-- The part of a cell after s is a fresh compensated increment factor. -/
theorem vectorCell_split (B : Fin d → ℝ≥0 → Ω → ℝ)
    {a b s t : ℝ≥0} (has : a ≤ s) (hsb : s ≤ b) (hst : s ≤ t)
    (c : Ω → Fin d → ℝ) (ω : Ω) :
    vectorCell B a b c t ω = vectorCell B a b c s ω * incrementFactor B s (min b t) c ω := by
  rw [vectorCell, min_eq_left (has.trans hst), vectorCell_of_mem B has hsb]
  exact incrementFactor_split B has (le_min hsb hst) c ω

section Brownian

variable {F : Filtration ℝ≥0 mΩ} (B : Fin d → ℝ≥0 → Ω → ℝ)
  (hB : ∀ j, IsFilteredPreBrownian (B j) F P)
  (hcoord : ∀ r t : ℝ≥0, r ≤ t → iIndepFun (fun j ω => B j t ω - B j r ω) P)
  (hpast : ∀ r t : ℝ≥0, r ≤ t →
    Indep (MeasurableSpace.comap (fun ω j => B j t ω - B j r ω) inferInstance) (F r) P)

include hB hcoord hpast in
/-- The Brownian increment vector satisfies the weighted conditional Gaussian identity. -/
theorem brownian_increment_weighted_condExp
    {r t : ℝ≥0} (hrt : r ≤ t) (c : Ω → Fin d → ℝ) (hc : Measurable[F r] c)
    {K : ℝ} (hK : ∀ ω j, |c ω j| ≤ K)
    (U : Ω → ℝ) (hU : StronglyMeasurable[F r] U) (hUint : Integrable U P) :
    Integrable (fun ω => U ω * incrementFactor B r t c ω) P ∧
      P[fun ω => U ω * incrementFactor B r t c ω | F r] =ᵐ[P] U := by
  have hXm : ∀ j, Measurable (fun ω => B j t ω - B j r ω) := fun j =>
    (((hB j).stronglyAdapted t).mono (F.le t)).measurable.sub
      (((hB j).stronglyAdapted r).mono (F.le r)).measurable
  have hLaw : ∀ j, HasLaw (fun ω => B j t ω - B j r ω) (gaussianReal 0 (t - r)) P := by
    intro j
    letI : IsFilteredPreBrownian (B j) F P := hB j
    simpa only [tsub_eq_zero_of_le hrt, max_eq_left (zero_le : (0 : ℝ≥0) ≤ t - r)] using
      (IsPreBrownian.hasLaw_sub (X := B j) (P := P) t r)
  exact weighted_vectorFactor_condExp (F.le r) c hc hK U hU hUint
    (fun j ω => B j t ω - B j r ω) hXm (fun _ => t - r) hLaw
    (hcoord r t hrt) (hpast r t hrt)

include hB hcoord hpast in
/-- In particular the actual random vector factor has conditional mean one. -/
theorem brownian_increment_condExp_eq_one
    {r t : ℝ≥0} (hrt : r ≤ t) (c : Ω → Fin d → ℝ) (hc : Measurable[F r] c)
    {K : ℝ} (hK : ∀ ω j, |c ω j| ≤ K) :
    Integrable (incrementFactor B r t c) P ∧
      P[incrementFactor B r t c | F r] =ᵐ[P] fun _ => (1 : ℝ) := by
  simpa only [one_mul] using brownian_increment_weighted_condExp B hB hcoord hpast hrt c hc hK
    (fun _ => (1 : ℝ)) stronglyMeasurable_const (integrable_const _)

include hB hcoord hpast in
/-- Every single cell is integrable, using its actual fresh vector increment. -/
theorem vectorCell_integrable {a b : ℝ≥0} (hab : a ≤ b)
    (c : Ω → Fin d → ℝ) (hc : Measurable[F a] c)
    {K : ℝ} (hK : ∀ ω j, |c ω j| ≤ K) (t : ℝ≥0) :
    Integrable (vectorCell B a b c t) P := by
  rcases le_total t a with hta | hat
  · simpa only [funext (vectorCell_of_le_left B hab c hta)] using
      (integrable_const (1 : ℝ) : Integrable (fun _ : Ω => (1 : ℝ)) P)
  · have heq : vectorCell B a b c t = incrementFactor B a (min b t) c := by
      funext ω
      rw [vectorCell, min_eq_left hat]
    rw [heq]
    exact (brownian_increment_condExp_eq_one B hB hcoord hpast (le_min hab hat) c hc hK).1

include hB in
/-- A cell is adapted to the common filtration; all channels use that same filtration. -/
theorem vectorCell_stronglyAdapted {a b : ℝ≥0} (hab : a ≤ b)
    (c : Ω → Fin d → ℝ) (hc : Measurable[F a] c) :
    StronglyAdapted F (vectorCell B a b c) := by
  intro t
  rcases le_total a t with hat | hta
  · have hct : Measurable[F t] c := hc.mono (F.mono hat) le_rfl
    have hleft : ∀ j, Measurable[F t] (B j (min a t)) := fun j =>
      ((hB j).stronglyAdapted (min a t)).measurable.mono
        (F.mono (min_le_right a t)) le_rfl
    have hright : ∀ j, Measurable[F t] (B j (min b t)) := fun j =>
      ((hB j).stronglyAdapted (min b t)).measurable.mono
        (F.mono (min_le_right b t)) le_rfl
    apply Measurable.stronglyMeasurable
    unfold vectorCell incrementFactor vectorFactor gaussianFactor
    fun_prop
  · rw [funext (vectorCell_of_le_left B hab c hta)]
    exact stronglyMeasurable_const

include hB hcoord hpast in
/-- The running exponential over one vector-coefficient time cell is a martingale. -/
theorem vectorCell_isMartingale {a b : ℝ≥0} (hab : a ≤ b)
    (c : Ω → Fin d → ℝ) (hc : Measurable[F a] c)
    {K : ℝ} (hK : ∀ ω j, |c ω j| ≤ K) :
    Martingale (vectorCell B a b c) F P := by
  have hadapt := vectorCell_stronglyAdapted B hB hab c hc
  have hint := vectorCell_integrable B hB hcoord hpast hab c hc hK
  refine ⟨hadapt, fun s t hst => ?_⟩
  rcases le_total t a with hta | hat
  · rw [funext (vectorCell_of_le_left B hab c hta),
      funext (vectorCell_of_le_left B hab c (hst.trans hta))]
    exact (condExp_const (F.le s) (1 : ℝ)).eventuallyEq
  rcases le_total b s with hbs | hsb
  · have heqt : vectorCell B a b c t = incrementFactor B a b c :=
      funext (vectorCell_of_ge_right B hab c (hbs.trans hst))
    have heqs : vectorCell B a b c s = incrementFactor B a b c :=
      funext (vectorCell_of_ge_right B hab c hbs)
    rw [heqt, ← heqs]
    exact (condExp_of_stronglyMeasurable (F.le s) (hadapt s) (hint s)).eventuallyEq
  rcases le_total s a with hsa | has
  · have heqt : vectorCell B a b c t = incrementFactor B a (min b t) c := by
      funext ω
      rw [vectorCell, min_eq_left hat]
    have hinner : P[vectorCell B a b c t | F a] =ᵐ[P] fun _ => (1 : ℝ) := by
      rw [heqt]
      exact (brownian_increment_condExp_eq_one B hB hcoord hpast (le_min hab hat) c hc hK).2
    rw [funext (vectorCell_of_le_left B hab c hsa)]
    refine (condExp_condExp_of_le (F.mono hsa) (F.le a)).symm.trans ?_
    exact (condExp_congr_ae hinner).trans (condExp_const (F.le s) (1 : ℝ)).eventuallyEq
  · have hcs : Measurable[F s] c := hc.mono (F.mono has) le_rfl
    have heq : vectorCell B a b c t = fun ω =>
        vectorCell B a b c s ω * incrementFactor B s (min b t) c ω :=
      funext (vectorCell_split B has hsb hst c)
    rw [heq]
    exact (brownian_increment_weighted_condExp B hB hcoord hpast (le_min hsb hst) c hcs hK
      (vectorCell B a b c s) (hadapt s) (hint s)).2

include hB hcoord hpast in
/-- Appending a fresh vector cell preserves a martingale frozen at its start.
Product integrability is produced by the weighted vector freezing theorem. -/
theorem mul_vectorCell_isMartingale {M : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M F P) {p q : ℝ≥0}
    (hMfrozen : ∀ t ω, p ≤ t → M t ω = M p ω) (hpq : p ≤ q)
    (c : Ω → Fin d → ℝ) (hc : Measurable[F p] c)
    {K : ℝ} (hK : ∀ ω j, |c ω j| ≤ K) :
    Martingale (fun t ω => M t ω * vectorCell B p q c t ω) F P := by
  have hG := vectorCell_isMartingale B hB hcoord hpast hpq c hc hK
  have hprodint (t : ℝ≥0) : Integrable (fun ω => M p ω * vectorCell B p q c t ω) P := by
    rcases le_total t p with htp | hpt
    · have heq : (fun ω => M p ω * vectorCell B p q c t ω) = M p := by
        funext ω
        rw [vectorCell_of_le_left B hpq c htp, mul_one]
      rw [heq]
      exact hM.integrable p
    · have heq : vectorCell B p q c t = incrementFactor B p (min q t) c := by
        funext ω
        rw [vectorCell, min_eq_left hpt]
      rw [heq]
      exact (brownian_increment_weighted_condExp B hB hcoord hpast (le_min hpq hpt) c hc hK
        (M p) (hM.stronglyAdapted p) (hM.integrable p)).1
  refine ⟨fun t => (hM.stronglyAdapted t).mul (hG.stronglyAdapted t), fun s t hst => ?_⟩
  change P[fun ω => M t ω * vectorCell B p q c t ω | (F s : MeasurableSpace Ω)]
    =ᵐ[P] fun ω => M s ω * vectorCell B p q c s ω
  rcases le_total p s with hps | hsp
  · have heqt : (fun ω => M t ω * vectorCell B p q c t ω) =
        fun ω => M p ω * vectorCell B p q c t ω := by
      funext ω
      rw [hMfrozen t ω (hps.trans hst)]
    have heqs : (fun ω => M s ω * vectorCell B p q c s ω) =
        fun ω => M p ω * vectorCell B p q c s ω := by
      funext ω
      rw [hMfrozen s ω hps]
    rw [heqt, heqs]
    refine (condExp_mul_of_stronglyMeasurable_left
      ((hM.stronglyAdapted p).mono (F.mono hps)) (hprodint t) (hG.integrable t)).trans ?_
    filter_upwards [hG.condExp_ae_eq hst] with ω hω
    simp only [Pi.mul_apply, hω]
  · rcases le_total t p with htp | hpt
    · have heqt : (fun ω => M t ω * vectorCell B p q c t ω) = M t := by
        funext ω
        rw [vectorCell_of_le_left B hpq c htp, mul_one]
      have heqs : (fun ω => M s ω * vectorCell B p q c s ω) = M s := by
        funext ω
        rw [vectorCell_of_le_left B hpq c (hst.trans htp), mul_one]
      rw [heqt, heqs]
      exact hM.condExp_ae_eq hst
    · have heqs : (fun ω => M s ω * vectorCell B p q c s ω) = M s := by
        funext ω
        rw [vectorCell_of_le_left B hpq c hsp, mul_one]
      have heqt : (fun ω => M t ω * vectorCell B p q c t ω) =
          fun ω => M p ω * vectorCell B p q c t ω := by
        funext ω
        rw [hMfrozen t ω hpt]
      rw [heqt, heqs]
      have hinner : P[fun ω => M p ω * vectorCell B p q c t ω | F p] =ᵐ[P] M p := by
        have heq : vectorCell B p q c t = incrementFactor B p (min q t) c := by
          funext ω
          rw [vectorCell, min_eq_left hpt]
        rw [heq]
        exact (brownian_increment_weighted_condExp B hB hcoord hpast (le_min hpq hpt) c hc hK
          (M p) (hM.stronglyAdapted p) (hM.integrable p)).2
      exact (condExp_condExp_of_le (F.mono hsp) (F.le p)).symm.trans
        ((condExp_congr_ae hinner).trans (hM.condExp_ae_eq hsp))

end Brownian

/-- The actual running elementary stochastic exponential over vector-coefficient cells. -/
noncomputable def vectorSimpleExponential (B : Fin d → ℝ≥0 → Ω → ℝ)
    (s : ℕ → ℝ≥0) (c : ℕ → Ω → Fin d → ℝ) : ℕ → ℝ≥0 → Ω → ℝ
  | 0, _, _ => 1
  | n + 1, t, ω =>
    vectorSimpleExponential B s c n t ω * vectorCell B (s n) (s (n + 1)) (c n) t ω

/-- Earlier factors are constant after the last partition point. -/
theorem vectorSimpleExponential_frozen (B : Fin d → ℝ≥0 → Ω → ℝ)
    (s : ℕ → ℝ≥0) (hs : Monotone s) (c : ℕ → Ω → Fin d → ℝ) :
    ∀ n t ω, s n ≤ t →
      vectorSimpleExponential B s c n t ω = vectorSimpleExponential B s c n (s n) ω := by
  intro n
  induction n with
  | zero => intro t ω ht; rfl
  | succ n ih =>
    intro t ω ht
    have hsn : s n ≤ s (n + 1) := hs (Nat.le_succ n)
    change vectorSimpleExponential B s c n t ω * vectorCell B (s n) (s (n + 1)) (c n) t ω =
      vectorSimpleExponential B s c n (s (n + 1)) ω *
        vectorCell B (s n) (s (n + 1)) (c n) (s (n + 1)) ω
    rw [ih t ω (hsn.trans ht), ih (s (n + 1)) ω hsn,
      vectorCell_of_ge_right B hsn (c n) ht,
      vectorCell_of_ge_right B hsn (c n) (le_refl _)]

/-- Continuous-time elementary vector stochastic exponentials are actual martingales.
All channel coefficients may depend jointly on the common past. -/
theorem vectorSimpleExponential_isMartingale {F : Filtration ℝ≥0 mΩ}
    (B : Fin d → ℝ≥0 → Ω → ℝ) (hB : ∀ j, IsFilteredPreBrownian (B j) F P)
    (hcoord : ∀ r t : ℝ≥0, r ≤ t → iIndepFun (fun j ω => B j t ω - B j r ω) P)
    (hpast : ∀ r t : ℝ≥0, r ≤ t →
      Indep (MeasurableSpace.comap (fun ω j => B j t ω - B j r ω) inferInstance) (F r) P)
    (s : ℕ → ℝ≥0) (hs : Monotone s) (c : ℕ → Ω → Fin d → ℝ)
    (hc : ∀ n, Measurable[F (s n)] (c n)) {K : ℝ}
    (hK : ∀ n ω j, |c n ω j| ≤ K) (n : ℕ) :
    Martingale (vectorSimpleExponential B s c n) F P := by
  induction n with
  | zero => exact martingale_const F P 1
  | succ n ih =>
    exact mul_vectorCell_isMartingale B hB hcoord hpast ih
      (fun t ω ht => vectorSimpleExponential_frozen B s hs c n t ω ht)
      (hs (Nat.le_succ n)) (c n) (hc n) (hK n)

/-- The exponent uses the sum of all channels' quadratic compensators at every cell. -/
theorem vectorSimpleExponential_eq_exp_sum (B : Fin d → ℝ≥0 → Ω → ℝ)
    (s : ℕ → ℝ≥0) (hs : Monotone s) (c : ℕ → Ω → Fin d → ℝ)
    (n : ℕ) (t : ℝ≥0) (ω : Ω) :
    vectorSimpleExponential B s c n t ω =
      Real.exp (∑ i ∈ Finset.range n,
        ((∑ j, c i ω j * (B j (min (s (i + 1)) t) ω - B j (min (s i) t) ω)) -
          (∑ j, (c i ω j) ^ 2 *
            (((min (s (i + 1)) t : ℝ≥0) : ℝ) - (min (s i) t : ℝ))) / 2)) := by
  induction n with
  | zero => simp [vectorSimpleExponential]
  | succ n ih =>
    rw [vectorSimpleExponential, ih, vectorCell,
      incrementFactor_eq_exp_sum B (min_le_min_right t (hs (Nat.le_succ n))),
      ← Real.exp_add, Finset.sum_range_succ]
    simp only [NNReal.coe_min, Nat.succ_eq_add_one]

/-- Continuous Brownian paths give continuous vector-cell paths. -/
theorem vectorCell_continuous (B : Fin d → ℝ≥0 → Ω → ℝ)
    (a b : ℝ≥0) (c : Ω → Fin d → ℝ) (ω : Ω)
    (hBcont : ∀ j, Continuous (fun t : ℝ≥0 => B j t ω)) :
    Continuous (fun t : ℝ≥0 => vectorCell B a b c t ω) := by
  unfold vectorCell incrementFactor vectorFactor gaussianFactor
  fun_prop

/-- Every finite elementary vector exponential has continuous paths on the driver's path event. -/
theorem vectorSimpleExponential_continuous (B : Fin d → ℝ≥0 → Ω → ℝ)
    (s : ℕ → ℝ≥0) (c : ℕ → Ω → Fin d → ℝ) (n : ℕ) (ω : Ω)
    (hBcont : ∀ j, Continuous (fun t : ℝ≥0 => B j t ω)) :
    Continuous (fun t : ℝ≥0 => vectorSimpleExponential B s c n t ω) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih =>
    exact ih.mul (vectorCell_continuous B (s n) (s (n + 1)) (c n) ω hBcont)

/-- One common full-measure event gives continuity of every elementary exponential path. -/
theorem ae_vectorSimpleExponential_continuous (B : Fin d → ℝ≥0 → Ω → ℝ)
    (s : ℕ → ℝ≥0) (c : ℕ → Ω → Fin d → ℝ) (n : ℕ)
    (hBcont : ∀ j, ∀ᵐ ω ∂P, Continuous (fun t : ℝ≥0 => B j t ω)) :
    ∀ᵐ ω ∂P, Continuous (fun t : ℝ≥0 => vectorSimpleExponential B s c n t ω) := by
  have hcommon : ∀ᵐ ω ∂P, ∀ j, Continuous (fun t : ℝ≥0 => B j t ω) :=
    ae_all_iff.mpr hBcont
  filter_upwards [hcommon] with ω hω
  exact vectorSimpleExponential_continuous B s c n ω hω

end Ripple.Stochastic.VectorStochasticExponential
