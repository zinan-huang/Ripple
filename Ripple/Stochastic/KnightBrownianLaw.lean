import Ripple.Stochastic.KnightStepGrid
import Ripple.Stochastic.BrownianMotion.Gaussian.BrownianMotion
import Ripple.Stochastic.IndependentBrownianFiltration
import Mathlib.Probability.Independence.Process.Basic

/-!
# Brownian laws from rectangular increment arrays

A rectangular law tests an arbitrary finite set of disjoint intervals within
each channel. The time grids of different channels need not coincide. Sorted
finite grids and telescoping reconstruct the finite path vectors. Independence
then passes to the entire paths through the native process independence API.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Finset Set
open scoped NNReal ENNReal

namespace Ripple.Stochastic.Knight

variable {ι Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}

/-- All finite rectangular increment arrays have the independent centered
Gaussian laws with variances equal to their interval lengths. -/
def HasRectangularGaussianIncrements (X : ι → ℝ≥0 → Ω → ℝ)
    (P : Measure Ω) : Prop :=
  ∀ (κ : Type) [Fintype κ] (g : IntervalGrid ι κ),
    iIndepFun (fun j ω => X (g.channel j) (g.upper j) ω -
      X (g.channel j) (g.lower j) ω) P ∧
    ∀ j, HasLaw (fun ω => X (g.channel j) (g.upper j) ω -
      X (g.channel j) (g.lower j) ω)
      (gaussianReal 0 (g.upper j - g.lower j)) P

/-- Consecutive intervals along a single monotone time grid. Repeated times
produce zero increments and are included. -/
def monotoneIntervalGrid (i : ι) {n : ℕ} (t : Fin (n + 1) → ℝ≥0)
    (ht : Monotone t) : IntervalGrid ι (Fin n) where
  channel := fun _ => i
  lower := fun j => t j.castSucc
  upper := fun j => t j.succ
  ordered := fun j => ht (Fin.castSucc_le_succ j)
  separated := by
    intro j k hjk _
    rcases lt_or_gt_of_ne hjk with hlt | hgt
    · exact Or.inl (ht (show j.succ ≤ k.castSucc from (by rw [Fin.le_def]; simp only [Fin.val_succ, Fin.coe_castSucc]; have := Fin.lt_def.1 hlt; omega)))
    · exact Or.inr (ht (show k.succ ≤ j.castSucc from (by rw [Fin.le_def]; simp only [Fin.val_succ, Fin.coe_castSucc]; have := Fin.lt_def.1 hgt; omega)))

/-- Rectangular laws imply the native independent-increments property. -/
theorem hasIndepIncrements_of_rectangular
    {X : ι → ℝ≥0 → Ω → ℝ}
    (hrect : HasRectangularGaussianIncrements X P) (i : ι) :
    HasIndepIncrements (X i) P := by
  intro n t ht
  exact (hrect (Fin n) (monotoneIntervalGrid i t ht)).1

/-- The interval from zero to `t` gives the required one-time Gaussian law.
The initial value must be supplied separately: increment laws cannot fix a
random additive constant. -/
theorem hasLaw_eval_of_rectangular
    {X : ι → ℝ≥0 → Ω → ℝ}
    (hrect : HasRectangularGaussianIncrements X P)
    (hzero : ∀ i, ∀ᵐ ω ∂P, X i 0 ω = 0) (i : ι) (t : ℝ≥0) :
    HasLaw (X i t) (gaussianReal 0 t) P := by
  let g : IntervalGrid ι Unit :=
    { channel := fun _ => i
      lower := fun _ => 0
      upper := fun _ => t
      ordered := fun _ => bot_le
      separated := fun j k hjk _ => False.elim (hjk (Subsingleton.elim j k)) }
  have h := (hrect Unit g).2 ()
  have h' : HasLaw (fun ω => X i t ω - X i 0 ω) (gaussianReal 0 t) P := by
    simpa [g] using h
  apply h'.congr
  filter_upwards [hzero i] with ω hω
  simp [hω]

/-- All finite Brownian laws follow from the scalar marginal laws and native
independent increments, rather than being carried as a premise. -/
theorem isPreBrownian_of_rectangular
    {X : ι → ℝ≥0 → Ω → ℝ}
    (hrect : HasRectangularGaussianIncrements X P)
    (hzero : ∀ i, ∀ᵐ ω ∂P, X i 0 ω = 0) (i : ι) :
    IsPreBrownian (X i) P :=
  HasIndepIncrements.isPreBrownian_of_hasLaw
    (hasLaw_eval_of_rectangular hrect hzero i)
    (hasIndepIncrements_of_rectangular hrect i)

section IndependentBlocks

variable {K J β : Type} [MeasurableSpace β]
    {γ : J → Type} [∀ j, MeasurableSpace (γ j)]

/-- Measurable functions of mutually disjoint finite blocks of an independent
family are independent. The output spaces may depend on the block. -/
theorem iIndepFun_disjoint_blocks [IsProbabilityMeasure P]
    [DecidableEq K] [DecidableEq J]
    {f : K → Ω → β} (hf : iIndepFun f P)
    (hfm : ∀ k, Measurable (f k)) (S : J → Finset K)
    (hS : Pairwise (Function.onFun Disjoint S))
    (φ : ∀ j, ((k : S j) → β) → γ j) (hφ : ∀ j, Measurable (φ j)) :
    iIndepFun (fun j ω => φ j (fun k : S j => f k ω)) P := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro T sets hsets
  induction T using Finset.induction_on with
  | empty => simp
  | insert j T hj ih =>
    rw [Finset.set_biInter_insert, Finset.prod_insert hj]
    let U : Finset K := T.biUnion S
    have hdisj : Disjoint (S j) U := by
      rw [Finset.disjoint_biUnion_right]
      intro k hk
      exact hS (fun h => hj (h ▸ hk))
    let F : Ω → ((k : S j) → β) := fun ω k => f k ω
    let G : Ω → ((k : U) → β) := fun ω k => f k ω
    have hind : IndepFun F G P := hf.indepFun_finset (S j) U hdisj hfm
    let res : (k : T) → ((l : U) → β) → ((l : S k.1) → β) :=
      fun k v l => v ⟨l.1, Finset.mem_biUnion.mpr ⟨k.1, k.2, l.2⟩⟩
    have hres : ∀ k, Measurable (res k) := fun k =>
      measurable_pi_lambda _ fun l => measurable_pi_apply _
    let E : Set ((k : U) → β) :=
      ⋂ k : T, (fun v => φ k.1 (res k v)) ⁻¹' sets k.1
    have hE : MeasurableSet E := MeasurableSet.iInter fun k =>
      ((hφ k.1).comp (hres k)) (hsets k.1 (Finset.mem_insert_of_mem k.2))
    have hG : (⋂ k ∈ T, (fun ω => φ k (fun l : S k => f l ω)) ⁻¹' sets k) =
        G ⁻¹' E := by
      ext ω
      simp only [Set.mem_iInter, Set.mem_preimage, E, Subtype.forall]
      rfl
    have hF : ((fun ω => φ j (fun k : S j => f k ω)) ⁻¹' sets j) =
        F ⁻¹' (φ j ⁻¹' sets j) := rfl
    rw [hG, hF, hind.measure_inter_preimage_eq_mul _ _
      ((hφ j) (hsets j (Finset.mem_insert_self _ _))) hE, ← hG, ← hF,
      ih (fun k hk => hsets k (Finset.mem_insert_of_mem hk))]

end IndependentBlocks

/-- The joint interval grid attached to different finite time sets in finitely
many channels. Each channel is sorted separately and starts at zero. -/
def finiteChannelGrid (I : Finset ι) (J : (i : I) → Finset ℝ≥0) :
    IntervalGrid ι (Σ i : I, Fin #(J i)) where
  channel := fun p => p.1.1
  lower := fun p => (J p.1).ofFin' p.2.castSucc
  upper := fun p => (J p.1).ofFin' p.2.succ
  ordered := fun p => (J p.1).monotone_ofFin' (Fin.castSucc_le_succ p.2)
  separated := by
    rintro ⟨i, k⟩ ⟨j, l⟩ hne hchannel
    have hij : i = j := Subtype.ext hchannel
    subst j
    have hkl : k ≠ l := by
      intro h
      subst l
      exact hne rfl
    rcases lt_or_gt_of_ne hkl with hlt | hgt
    · exact Or.inl ((J i).monotone_ofFin' (show k.succ ≤ l.castSucc from (by rw [Fin.le_def]; simp only [Fin.val_succ, Fin.coe_castSucc]; have := Fin.lt_def.1 hlt; omega)))
    · exact Or.inr ((J i).monotone_ofFin' (show l.succ ≤ k.castSucc from (by rw [Fin.le_def]; simp only [Fin.val_succ, Fin.coe_castSucc]; have := Fin.lt_def.1 hgt; omega)))

/-- Finite path vectors in distinct channels are independent, even when their
time sets have different cardinalities and different locations. -/
theorem iIndepFun_finite_paths_of_rectangular [IsProbabilityMeasure P]
    {X : ι → ℝ≥0 → Ω → ℝ}
    (hrect : HasRectangularGaussianIncrements X P)
    (hX : ∀ i t, Measurable (X i t))
    (hzero : ∀ i, ∀ᵐ ω ∂P, X i 0 ω = 0)
    (I : Finset ι) (J : (i : I) → Finset ℝ≥0) :
    iIndepFun (fun (i : I) ω (t : J i) => X i t ω) P := by
  classical
  let K := Σ i : I, Fin #(J i)
  let g := finiteChannelGrid I J
  let D : K → Ω → ℝ := fun p ω =>
    X p.1 ((J p.1).ofFin' p.2.succ) ω -
      X p.1 ((J p.1).ofFin' p.2.castSucc) ω
  have hD : iIndepFun D P := (hrect K g).1
  have hDm : ∀ p, Measurable (D p) := fun p => (hX _ _).sub (hX _ _)
  let S : I → Finset K := fun i => Finset.univ.filter fun p => p.1 = i
  have hmem : ∀ (i : I) (k : Fin #(J i)), (⟨i, k⟩ : K) ∈ S i := by
    intro i k
    simp [S]
  have hS : Pairwise (Function.onFun Disjoint S) := by
    intro i j hij
    apply Finset.disjoint_left.mpr
    intro p hpi hpj
    have hi : p.1 = i := (Finset.mem_filter.mp hpi).2
    have hj : p.1 = j := (Finset.mem_filter.mp hpj).2
    exact hij (hi.symm.trans hj)
  let φ : ∀ i : I, ((p : S i) → ℝ) → ((t : J i) → ℝ) :=
    fun i v t => ∑ k ≤ (J i).toFin t, v ⟨⟨i, k⟩, hmem i k⟩
  have hφ : ∀ i, Measurable (φ i) := by
    intro i
    apply measurable_pi_lambda
    intro t
    exact Finset.measurable_sum _ fun k _ => measurable_pi_apply _
  have hblocks := iIndepFun_disjoint_blocks hD hDm S hS φ hφ
  apply hblocks.congr
  intro i
  have hreconstruct :=
    incrementsToRestrict_increments_ofFin'_ae_eq_restrict ℝ (hzero i) (J i)
  filter_upwards [hreconstruct] with ω hω
  exact hω.symm

/-- Full path independence follows from all finite restrictions through
`iIndepFun.iIndepFun_process`, whose finite restrictions allow unequal grids. -/
theorem iIndepFun_paths_of_rectangular [IsProbabilityMeasure P]
    {X : ι → ℝ≥0 → Ω → ℝ}
    (hrect : HasRectangularGaussianIncrements X P)
    (hX : ∀ i t, Measurable (X i t))
    (hzero : ∀ i, ∀ᵐ ω ∂P, X i 0 ω = 0) :
    iIndepFun (fun i ω t => X i t ω) P := by
  apply iIndepFun.iIndepFun_process hX
  exact iIndepFun_finite_paths_of_rectangular hrect hX hzero

/-- Rectangular Gaussian increments and the zero initial value imply both
Brownian finite-dimensional laws and independence of entire channel paths. -/
theorem brownian_family_of_rectangular [IsProbabilityMeasure P]
    {X : ι → ℝ≥0 → Ω → ℝ}
    (hrect : HasRectangularGaussianIncrements X P)
    (hX : ∀ i t, Measurable (X i t))
    (hzero : ∀ i, ∀ᵐ ω ∂P, X i 0 ω = 0) :
    (∀ i, IsPreBrownian (X i) P) ∧ iIndepFun (fun i ω t => X i t ω) P := by
  exact ⟨isPreBrownian_of_rectangular hrect hzero,
    iIndepFun_paths_of_rectangular hrect hX hzero⟩

/-- A finite array of increments of independent Gaussian channel processes is
jointly Gaussian. The endpoint times may differ for every array entry. -/
theorem hasGaussianLaw_rectangular_increments [Fintype ι] [IsProbabilityMeasure P]
    {X : ι → ℝ≥0 → Ω → ℝ}
    (hX : ∀ i, IsPreBrownian (X i) P)
    (hind : iIndepFun (fun i ω t => X i t ω) P)
    {κ : Type} [Fintype κ] (g : IntervalGrid ι κ) :
    HasGaussianLaw (fun ω j => X (g.channel j) (g.upper j) ω -
      X (g.channel j) (g.lower j) ω) P := by
  classical
  have hg := IndependentBrownianFiltration.tagged_isGaussianProcess
    (fun i => (hX i).isGaussianProcess) hind
  let I : Finset (ι × ℝ≥0) :=
    (Finset.univ.image fun j => (g.channel j, g.upper j)) ∪
      (Finset.univ.image fun j => (g.channel j, g.lower j))
  have hu : ∀ j, (g.channel j, g.upper j) ∈ I := by
    intro j
    exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩)
  have hl : ∀ j, (g.channel j, g.lower j) ∈ I := by
    intro j
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩)
  let L : (I → ℝ) →L[ℝ] (κ → ℝ) :=
    { toFun := fun x j => x ⟨(g.channel j, g.upper j), hu j⟩ -
        x ⟨(g.channel j, g.lower j), hl j⟩
      map_add' := by intros; ext; simp; abel
      map_smul' := by intros; ext; simp; ring
      cont := by fun_prop }
  simpa only [L, Finset.restrict, ContinuousLinearMap.coe_mk', LinearMap.coe_mk,
    AddHom.coe_mk, Function.comp_apply] using (hg.hasGaussianLaw I).map L

/-- For disjoint intervals in the same channel, or intervals in different
independent channels, the two increments are uncorrelated. -/
theorem covariance_rectangular_increments [Fintype ι] [IsProbabilityMeasure P]
    {X : ι → ℝ≥0 → Ω → ℝ}
    (hX : ∀ i, IsPreBrownian (X i) P)
    (hind : iIndepFun (fun i ω t => X i t ω) P)
    {κ : Type} [Fintype κ] (g : IntervalGrid ι κ)
    (j k : κ) (hjk : j ≠ k) :
    cov[fun ω => X (g.channel j) (g.upper j) ω - X (g.channel j) (g.lower j) ω,
      fun ω => X (g.channel k) (g.upper k) ω - X (g.channel k) (g.lower k) ω; P] = 0 := by
  have hLp : ∀ i t, MemLp (X i t) 2 P :=
    fun i t => ((hX i).isGaussianProcess.hasGaussianLaw_eval t).memLp_two
  rw [covariance_fun_sub_left (hLp _ _) (hLp _ _)
      (Z := fun ω => X (g.channel k) (g.upper k) ω - X (g.channel k) (g.lower k) ω)
      ((hLp _ _).sub (hLp _ _)),
    covariance_fun_sub_right (hLp _ _) (hLp _ _) (hLp _ _),
    covariance_fun_sub_right (hLp _ _) (hLp _ _) (hLp _ _)]
  by_cases hchannel : g.channel j = g.channel k
  · simp_rw [← hchannel, (hX (g.channel j)).covariance_fun_eval]
    have hj : g.lower j ≤ g.upper j := g.ordered j
    have hk : g.lower k ≤ g.upper k := g.ordered k
    rcases g.separated j k hjk hchannel with hleft | hright
    · rw [min_eq_left (hleft.trans hk), min_eq_left hleft,
        min_eq_left (hj.trans (hleft.trans hk)), min_eq_left (hj.trans hleft)]
      ring
    · rw [min_eq_right (hright.trans hj), min_eq_right (hk.trans (hright.trans hj)),
        min_eq_right hright, min_eq_right (hk.trans hright)]
      ring
  · rw [IndependentBrownianFiltration.covariance_ne hX hind hchannel,
      IndependentBrownianFiltration.covariance_ne hX hind hchannel,
      IndependentBrownianFiltration.covariance_ne hX hind hchannel,
      IndependentBrownianFiltration.covariance_ne hX hind hchannel]
    ring

/-- Independent Brownian channel paths supply all rectangular Gaussian
increment laws. This discharges the auxiliary Brownian-grid input used when
completing a time change after finite terminal clocks. -/
theorem rectangular_of_brownian_family [Fintype ι] [IsProbabilityMeasure P]
    {X : ι → ℝ≥0 → Ω → ℝ}
    (hX : ∀ i, IsPreBrownian (X i) P)
    (hind : iIndepFun (fun i ω t => X i t ω) P) :
    HasRectangularGaussianIncrements X P := by
  intro κ _ g
  refine ⟨(hasGaussianLaw_rectangular_increments hX hind g).iIndepFun_of_covariance_eq_zero
    (covariance_rectangular_increments hX hind g), ?_⟩
  intro j
  simpa only [tsub_eq_zero_of_le (g.ordered j), _root_.max_zero] using
    (hX (g.channel j)).hasLaw_sub (g.upper j) (g.lower j)

end Ripple.Stochastic.Knight
