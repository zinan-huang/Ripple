/-
  Ripple.Kurtz.StrongApprox.ExponentialMaximal — the exponential (Chernoff-type) maximal inequality
  for partial sums of independent centered variables

  Mathematics: Poisson block oscillation (W5) on a finite grid, by an exponential martingale and a
  first-crossing argument.

  For independent centered `R i` with `e^{θ R_i}` integrable, `θ ≥ 0`, and `S k = Σ_{i<k} R i`:
    `e^{θ z} · P(∃ k ≤ q, S_k > z) ≤ E e^{θ S_q} = Π_{i<q} E e^{θ R_i}`.
  Proof by first crossing: on `A_j = {S_j > z, S_l ≤ z ∀ l < j}`,
  `E[1_{A_j} e^{θ S_q}] = E[1_{A_j} e^{θ S_j}] · E[e^{θ (S_q − S_j)}] ≥ e^{θ z} P(A_j)`, using
  independence of `(R_i)_{i<j}` and `(R_i)_{j≤i<q}` and `E e^{θ D} ≥ 1 + θ E D = 1`.
-/

import Mathlib
import Ripple.Kurtz.StrongApprox.KolmogorovMaximal

namespace Ripple.Kurtz.StrongApprox

open MeasureTheory ProbabilityTheory Set Finset

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-! ### First entrance of the partial sums into a set `B` -/

/-- `A_j = {S_j ∈ B, S_l ∉ B for all l < j}`. -/
def entAt (R : ℕ → Ω → ℝ) (B : Set ℝ) (j : ℕ) : Set Ω :=
  {ω | partialSum R j ω ∈ B ∧ ∀ l < j, partialSum R l ω ∉ B}

theorem measurableSet_ent {α : Type*} [MeasurableSpace α] {f : ℕ → α → ℝ}
    (hf : ∀ l, Measurable (f l)) {B : Set ℝ} (hB : MeasurableSet B) (j : ℕ) :
    MeasurableSet {x | f j x ∈ B ∧ ∀ l < j, f l x ∉ B} := by
  have h1 : MeasurableSet {x | f j x ∈ B} := hf j hB
  have h2 : MeasurableSet {x | ∀ l < j, f l x ∉ B} := by
    have : {x | ∀ l < j, f l x ∉ B} = ⋂ l, ⋂ (_ : l < j), {x | f l x ∈ B}ᶜ := by
      ext x; simp
    rw [this]
    exact MeasurableSet.iInter fun l => MeasurableSet.iInter fun _ => (hf l hB).compl
  exact h1.inter h2

theorem measurableSet_entAt {R : ℕ → Ω → ℝ} (hmeas : ∀ i, Measurable (R i)) {B : Set ℝ}
    (hB : MeasurableSet B) (j : ℕ) : MeasurableSet (entAt R B j) :=
  measurableSet_ent (measurable_partialSum hmeas) hB j

theorem entAt_disjoint {R : ℕ → Ω → ℝ} {B : Set ℝ} {j j' : ℕ} (hne : j ≠ j') {ω : Ω}
    (h1 : ω ∈ entAt R B j) (h2 : ω ∈ entAt R B j') : False := by
  rcases lt_or_gt_of_ne hne with h | h
  · exact h2.2 j h h1.1
  · exact h1.2 j' h h2.1

theorem entAt_pairwiseDisjoint (R : ℕ → Ω → ℝ) (B : Set ℝ) (s : Finset ℕ) :
    (↑s : Set ℕ).PairwiseDisjoint (entAt R B) := by
  intro j _ j' _ hne
  exact Set.disjoint_left.mpr fun ω h1 h2 => entAt_disjoint hne h1 h2

theorem exists_entAt {R : ℕ → Ω → ℝ} {B : Set ℝ} {q : ℕ} {ω : Ω}
    (hex : ∃ k ≤ q, partialSum R k ω ∈ B) : ∃ j ≤ q, ω ∈ entAt R B j := by
  classical
  have hex' : ∃ k, k ≤ q ∧ partialSum R k ω ∈ B := hex
  refine ⟨Nat.find hex', (Nat.find_spec hex').1, (Nat.find_spec hex').2, ?_⟩
  intro l hl hmem
  have hlq : l ≤ q := by have := (Nat.find_spec hex').1; omega
  exact Nat.find_min hex' hl ⟨hlq, hmem⟩

/-- The entrance set in the coordinates `x : ℕ → ℝ`. -/
def entSet (B : Set ℝ) (j : ℕ) : Set (ℕ → ℝ) :=
  {x | (∑ i ∈ range j, x i) ∈ B ∧ ∀ l < j, (∑ i ∈ range l, x i) ∉ B}

theorem measurableSet_entSet {B : Set ℝ} (hB : MeasurableSet B) (j : ℕ) :
    MeasurableSet (entSet B j) :=
  measurableSet_ent (f := fun l (x : ℕ → ℝ) => ∑ i ∈ range l, x i)
    (fun l => Finset.measurable_sum _ fun i _ => measurable_pi_apply i) hB j

theorem mem_entAt_iff (R : ℕ → Ω → ℝ) (B : Set ℝ) (j : ℕ) (ω : Ω) :
    ω ∈ entAt R B j ↔ maskLT R j ω ∈ entSet B j := by
  simp only [entAt, entSet, mem_setOf_eq]
  rw [← partialSum_eq_maskLT R le_rfl ω]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun l hl => by rw [← partialSum_eq_maskLT R hl.le ω]; exact h2 l hl⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun l hl => by rw [partialSum_eq_maskLT R hl.le ω]; exact h2 l hl⟩

/-- `1_{A_j} g(S_j)` and `h(S_q − S_j)` are independent for measurable `g, h`. -/
theorem indepFun_indicator_entAt {R : ℕ → Ω → ℝ} (hmeas : ∀ i, Measurable (R i))
    (hindep : iIndepFun R P) {B : Set ℝ} (hB : MeasurableSet B) {g h : ℝ → ℝ} (hg : Measurable g)
    (hh : Measurable h) {j q : ℕ} (hjq : j ≤ q) :
    IndepFun ((entAt R B j).indicator fun ω => g (partialSum R j ω))
      (fun ω => h (partialSum R q ω - partialSum R j ω)) P := by
  let Φ : (ℕ → ℝ) → ℝ := (entSet B j).indicator fun x => g (∑ i ∈ range j, x i)
  let Ψ : (ℕ → ℝ) → ℝ := fun x => h (∑ i ∈ Finset.Ico j q, x i)
  have hΦ : Measurable Φ :=
    (hg.comp (Finset.measurable_sum _ fun i _ => measurable_pi_apply i)).indicator
      (measurableSet_entSet hB j)
  have hΨ : Measurable Ψ := hh.comp (Finset.measurable_sum _ fun i _ => measurable_pi_apply i)
  have hI := (indepFun_maskLT_maskIco hmeas hindep j q).comp hΦ hΨ
  have e1 : Φ ∘ maskLT R j = (entAt R B j).indicator fun ω => g (partialSum R j ω) := by
    funext ω
    simp only [Function.comp, Φ]
    by_cases hω : ω ∈ entAt R B j
    · rw [Set.indicator_of_mem hω, Set.indicator_of_mem ((mem_entAt_iff R B j ω).mp hω),
        partialSum_eq_maskLT R le_rfl ω]
    · rw [Set.indicator_of_notMem hω,
        Set.indicator_of_notMem (fun h => hω ((mem_entAt_iff R B j ω).mpr h))]
  have e2 : Ψ ∘ maskIco R j q = fun ω => h (partialSum R q ω - partialSum R j ω) := by
    funext ω
    simp only [Function.comp, Ψ]
    rw [sub_partialSum_eq_maskIco R hjq ω]
  rw [e1, e2] at hI
  exact hI

/-! ### The exponential crossing bound -/

theorem integrable_exp_mul_partialSum [IsProbabilityMeasure P] {R : ℕ → Ω → ℝ}
    (hmeas : ∀ i, Measurable (R i))
    (hindep : iIndepFun R P) {θ : ℝ} (hexp : ∀ i, Integrable (fun ω => Real.exp (θ * R i ω)) P)
    (k : ℕ) : Integrable (fun ω => Real.exp (θ * partialSum R k ω)) P := by
  rw [partialSum_eq_sum]
  exact hindep.integrable_exp_mul_sum hmeas fun i _ => hexp i

theorem integrable_exp_mul_sub_partialSum [IsProbabilityMeasure P] {R : ℕ → Ω → ℝ}
    (hmeas : ∀ i, Measurable (R i))
    (hindep : iIndepFun R P) {θ : ℝ} (hexp : ∀ i, Integrable (fun ω => Real.exp (θ * R i ω)) P)
    {j q : ℕ} (hjq : j ≤ q) :
    Integrable (fun ω => Real.exp (θ * (partialSum R q ω - partialSum R j ω))) P := by
  have h := hindep.integrable_exp_mul_sum hmeas (s := Finset.Ico j q) (t := θ) fun i _ => hexp i
  refine h.congr (Filter.Eventually.of_forall fun ω => ?_)
  simp only
  congr 2
  rw [Finset.sum_apply]
  unfold partialSum
  rw [← Finset.sum_range_add_sum_Ico _ hjq, add_sub_cancel_left]

/-- `E e^{θ D} ≥ 1` for centered integrable `D` with integrable `e^{θ D}`. -/
theorem one_le_integral_exp_mul [IsProbabilityMeasure P] {D : Ω → ℝ} (hD : Integrable D P)
    (hmean : ∫ ω, D ω ∂P = 0) {θ : ℝ} (hexp : Integrable (fun ω => Real.exp (θ * D ω)) P) :
    1 ≤ ∫ ω, Real.exp (θ * D ω) ∂P := by
  have h1 : ∫ ω, (1 + θ * D ω) ∂P = 1 := by
    rw [integral_add (integrable_const 1) (hD.const_mul θ), integral_const, integral_const_mul,
      hmean]
    simp [probReal_univ]
  rw [← h1]
  apply integral_mono ((integrable_const 1).add (hD.const_mul θ)) hexp
  intro ω
  show 1 + θ * D ω ≤ Real.exp (θ * D ω)
  linarith [Real.add_one_le_exp (θ * D ω)]

/-- `e^{θ z} P(A_j) ≤ E[1_{A_j} e^{θ S_q}]` for `θ ≥ 0`, `A_j` the first entrance into `(z, ∞)`. -/
theorem entAt_exp_bound [IsProbabilityMeasure P] {R : ℕ → Ω → ℝ} (hmeas : ∀ i, Measurable (R i))
    (hindep : iIndepFun R P) (hint : ∀ i, Integrable (R i) P) (hmean : ∀ i, ∫ ω, R i ω ∂P = 0)
    {θ : ℝ} (hθ : 0 ≤ θ) (hexp : ∀ i, Integrable (fun ω => Real.exp (θ * R i ω)) P) (z : ℝ)
    {j q : ℕ} (hjq : j ≤ q) :
    Real.exp (θ * z) * (P (entAt R (Ioi z) j)).toReal ≤
      ∫ ω, (entAt R (Ioi z) j).indicator (fun ω => Real.exp (θ * partialSum R q ω)) ω ∂P := by
  have hA : MeasurableSet (entAt R (Ioi z) j) := measurableSet_entAt hmeas measurableSet_Ioi j
  have hSm : ∀ k, Measurable (partialSum R k) := measurable_partialSum hmeas
  set D : Ω → ℝ := fun ω => partialSum R q ω - partialSum R j ω with hD_def
  have hDint : Integrable D P := by
    have : ∀ k, Integrable (partialSum R k) P := fun k => by
      unfold partialSum; exact integrable_finsetSum _ fun i _ => hint i
    exact (this q).sub (this j)
  have hDmean : ∫ ω, D ω ∂P = 0 := by
    rw [hD_def]
    simp only
    have hk : ∀ k, ∫ ω, partialSum R k ω ∂P = 0 := by
      intro k; unfold partialSum
      rw [integral_finsetSum _ fun i _ => hint i]
      exact Finset.sum_eq_zero fun i _ => hmean i
    rw [integral_sub, hk, hk, sub_zero]
    · unfold partialSum; exact integrable_finsetSum _ fun i _ => hint i
    · unfold partialSum; exact integrable_finsetSum _ fun i _ => hint i
  have hDexp : Integrable (fun ω => Real.exp (θ * D ω)) P :=
    integrable_exp_mul_sub_partialSum hmeas hindep hexp hjq
  set X : Ω → ℝ := (entAt R (Ioi z) j).indicator fun ω => Real.exp (θ * partialSum R j ω)
    with hX_def
  have hXm : Measurable X := (measurable_const.mul (hSm j)).exp.indicator hA
  have hYm : Measurable fun ω => Real.exp (θ * D ω) := (measurable_const.mul
    ((hSm q).sub (hSm j))).exp
  have hXY : IndepFun X (fun ω => Real.exp (θ * D ω)) P :=
    indepFun_indicator_entAt hmeas hindep measurableSet_Ioi
      (g := fun x => Real.exp (θ * x)) (h := fun x => Real.exp (θ * x))
      (by fun_prop) (by fun_prop) hjq
  have hprod : (fun ω => X ω * Real.exp (θ * D ω)) =
      (entAt R (Ioi z) j).indicator fun ω => Real.exp (θ * partialSum R q ω) := by
    funext ω
    simp only [hX_def, hD_def]
    by_cases hω : ω ∈ entAt R (Ioi z) j
    · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω, ← Real.exp_add]; congr 1; ring
    · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem hω, zero_mul]
  have hint_eq : ∫ ω, (entAt R (Ioi z) j).indicator (fun ω => Real.exp (θ * partialSum R q ω)) ω ∂P
      = (∫ ω, X ω ∂P) * ∫ ω, Real.exp (θ * D ω) ∂P := by
    rw [← hprod]
    have := hXY.integral_mul_eq_mul_integral hXm.aestronglyMeasurable hYm.aestronglyMeasurable
    simpa [Pi.mul_apply] using this
  have hX_int : Integrable X P :=
    (integrable_exp_mul_partialSum hmeas hindep hexp j).indicator hA
  have hXlow : Real.exp (θ * z) * (P (entAt R (Ioi z) j)).toReal ≤ ∫ ω, X ω ∂P := by
    rw [hX_def, integral_indicator hA]
    have h1 : ∫ _ in entAt R (Ioi z) j, Real.exp (θ * z) ∂P ≤
        ∫ ω in entAt R (Ioi z) j, Real.exp (θ * partialSum R j ω) ∂P := by
      apply setIntegral_mono_on (integrable_const _).integrableOn
        (integrable_exp_mul_partialSum hmeas hindep hexp j).integrableOn hA
      intro ω hω
      have hω' : z < partialSum R j ω :=
        (show partialSum R j ω ∈ Ioi z ∧ ∀ l < j, partialSum R l ω ∉ Ioi z from hω).1
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hω'.le hθ)
    rw [setIntegral_const, measureReal_def, smul_eq_mul] at h1
    linarith
  have hX_nonneg : 0 ≤ ∫ ω, X ω ∂P :=
    integral_nonneg fun ω => Set.indicator_nonneg (fun _ _ => (Real.exp_pos _).le) ω
  rw [hint_eq]
  calc Real.exp (θ * z) * (P (entAt R (Ioi z) j)).toReal
      ≤ ∫ ω, X ω ∂P := hXlow
    _ = (∫ ω, X ω ∂P) * 1 := (mul_one _).symm
    _ ≤ (∫ ω, X ω ∂P) * ∫ ω, Real.exp (θ * D ω) ∂P :=
        mul_le_mul_of_nonneg_left (one_le_integral_exp_mul hDint hDmean hDexp) hX_nonneg

/-- **Exponential maximal inequality**: for independent centered `R i` with integrable
`e^{θ R_i}`, `θ ≥ 0`: `e^{θ z} · P(∃ k ≤ q, S_k > z) ≤ E e^{θ S_q}`. -/
theorem exp_maximal [IsProbabilityMeasure P] {R : ℕ → Ω → ℝ} (hmeas : ∀ i, Measurable (R i))
    (hindep : iIndepFun R P) (hint : ∀ i, Integrable (R i) P) (hmean : ∀ i, ∫ ω, R i ω ∂P = 0)
    {θ : ℝ} (hθ : 0 ≤ θ) (hexp : ∀ i, Integrable (fun ω => Real.exp (θ * R i ω)) P) (z : ℝ)
    (q : ℕ) :
    Real.exp (θ * z) * (P {ω | ∃ k ≤ q, z < partialSum R k ω}).toReal ≤
      mgf (partialSum R q) P θ := by
  have hSexp : Integrable (fun ω => Real.exp (θ * partialSum R q ω)) P :=
    integrable_exp_mul_partialSum hmeas hindep hexp q
  have hE : {ω | ∃ k ≤ q, z < partialSum R k ω} = ⋃ j ∈ range (q + 1), entAt R (Ioi z) j := by
    ext ω
    simp only [mem_setOf_eq, mem_iUnion, Finset.mem_range]
    constructor
    · intro h
      obtain ⟨j, hj, hmem⟩ := exists_entAt (B := Ioi z) h
      exact ⟨j, by omega, hmem⟩
    · rintro ⟨j, hj, hmem⟩
      exact ⟨j, by omega, hmem.1⟩
  have hmeasA : ∀ j ∈ range (q + 1), MeasurableSet (entAt R (Ioi z) j) :=
    fun j _ => measurableSet_entAt hmeas measurableSet_Ioi j
  rw [hE, measure_biUnion_finset (entAt_pairwiseDisjoint R _ _) hmeasA,
    ENNReal.toReal_sum (fun j _ => measure_ne_top _ _), Finset.mul_sum]
  have hterm : ∀ j ∈ range (q + 1), Real.exp (θ * z) * (P (entAt R (Ioi z) j)).toReal ≤
      ∫ ω, (entAt R (Ioi z) j).indicator (fun ω => Real.exp (θ * partialSum R q ω)) ω ∂P :=
    fun j hj => entAt_exp_bound hmeas hindep hint hmean hθ hexp z
      (by rw [Finset.mem_range] at hj; omega)
  unfold mgf
  calc ∑ j ∈ range (q + 1), Real.exp (θ * z) * (P (entAt R (Ioi z) j)).toReal
      ≤ ∑ j ∈ range (q + 1),
          ∫ ω, (entAt R (Ioi z) j).indicator (fun ω => Real.exp (θ * partialSum R q ω)) ω ∂P :=
        Finset.sum_le_sum hterm
    _ = ∫ ω, ∑ j ∈ range (q + 1),
          (entAt R (Ioi z) j).indicator (fun ω => Real.exp (θ * partialSum R q ω)) ω ∂P :=
        (integral_finsetSum _ fun j hj => hSexp.indicator (hmeasA j hj)).symm
    _ ≤ ∫ ω, Real.exp (θ * partialSum R q ω) ∂P := by
        apply integral_mono (integrable_finsetSum _ fun j hj => hSexp.indicator (hmeasA j hj)) hSexp
        intro ω
        show ∑ j ∈ range (q + 1),
          (entAt R (Ioi z) j).indicator (fun ω => Real.exp (θ * partialSum R q ω)) ω ≤
          Real.exp (θ * partialSum R q ω)
        by_cases hex : ∃ j ∈ range (q + 1), ω ∈ entAt R (Ioi z) j
        · obtain ⟨j₀, hj₀, hmem⟩ := hex
          rw [Finset.sum_eq_single j₀]
          · rw [Set.indicator_of_mem hmem]
          · intro j _ hne
            rw [Set.indicator_of_notMem]
            intro hmem'
            exact entAt_disjoint hne hmem' hmem
          · intro h; exact absurd hj₀ h
        · push Not at hex
          rw [Finset.sum_eq_zero fun j hj => Set.indicator_of_notMem (hex j hj) _]
          exact (Real.exp_pos _).le

/-- The product form: `E e^{θ S_q} = Π_{i<q} E e^{θ R_i}`. -/
theorem mgf_partialSum {R : ℕ → Ω → ℝ} (hmeas : ∀ i, Measurable (R i)) (hindep : iIndepFun R P)
    (q : ℕ) (θ : ℝ) : mgf (partialSum R q) P θ = ∏ i ∈ range q, mgf (R i) P θ := by
  rw [partialSum_eq_sum]
  exact hindep.mgf_sum hmeas (range q)

end Ripple.Kurtz.StrongApprox
