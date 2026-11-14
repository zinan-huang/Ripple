/-
  Ripple.Kurtz.StrongApprox.KolmogorovMaximal — Kolmogorov's maximal inequality

  For independent, centered, square-integrable `R i` with partial sums `S k = Σ_{i<k} R i`:
    `a² · P(∃ k ≤ q, |S k| > a) ≤ E S_q² = Σ_{i<q} E R_i²`.
  Proof by first crossing: on `A_j = {|S_j| > a, |S_l| ≤ a ∀ l < j}` one has
  `E[1_{A_j} S_q²] ≥ E[1_{A_j} S_j²] + 2 E[1_{A_j} S_j] E[S_q − S_j] ≥ a² P(A_j)`, the middle term
  vanishing by independence of `(R_i)_{i<j}` and `(R_i)_{j≤i<q}`, and the `A_j` are disjoint.
-/

import Mathlib

namespace Ripple.Kurtz.StrongApprox

open MeasureTheory ProbabilityTheory Set Finset

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- Partial sums `S k = Σ_{i<k} R i`. -/
def partialSum (R : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) : ℝ := ∑ i ∈ range k, R i ω

theorem partialSum_eq_sum (R : ℕ → Ω → ℝ) (k : ℕ) : partialSum R k = ∑ i ∈ range k, R i := by
  funext ω; simp [partialSum, Finset.sum_apply]

theorem measurable_partialSum {R : ℕ → Ω → ℝ} (hmeas : ∀ i, Measurable (R i)) (k : ℕ) :
    Measurable (partialSum R k) :=
  Finset.measurable_sum _ fun i _ => hmeas i

theorem memLp_partialSum {R : ℕ → Ω → ℝ} (hL2 : ∀ i, MemLp (R i) 2 P) (k : ℕ) :
    MemLp (partialSum R k) 2 P := by
  rw [partialSum_eq_sum]
  exact memLp_finsetSum' _ fun i _ => hL2 i

theorem integral_partialSum [IsFiniteMeasure P] {R : ℕ → Ω → ℝ} (hL2 : ∀ i, MemLp (R i) 2 P)
    (hmean : ∀ i, ∫ ω, R i ω ∂P = 0) (k : ℕ) : ∫ ω, partialSum R k ω ∂P = 0 := by
  unfold partialSum
  rw [integral_finsetSum _ fun i _ => (hL2 i).integrable one_le_two]
  exact Finset.sum_eq_zero fun i _ => hmean i

/-! ### Masked families and their independence -/

/-- `maskLT R j ω i = R i ω` for `i < j`, else `0`. -/
def maskLT (R : ℕ → Ω → ℝ) (j : ℕ) (ω : Ω) : ℕ → ℝ := fun i => if i < j then R i ω else 0

/-- `maskIco R j q ω i = R i ω` for `j ≤ i < q`, else `0`. -/
def maskIco (R : ℕ → Ω → ℝ) (j q : ℕ) (ω : Ω) : ℕ → ℝ :=
  fun i => if j ≤ i ∧ i < q then R i ω else 0

theorem partialSum_eq_maskLT (R : ℕ → Ω → ℝ) {l j : ℕ} (hlj : l ≤ j) (ω : Ω) :
    partialSum R l ω = ∑ i ∈ range l, maskLT R j ω i := by
  unfold partialSum maskLT
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  rw [if_pos (by omega)]

theorem sub_partialSum_eq_maskIco (R : ℕ → Ω → ℝ) {j q : ℕ} (hjq : j ≤ q) (ω : Ω) :
    partialSum R q ω - partialSum R j ω = ∑ i ∈ Finset.Ico j q, maskIco R j q ω i := by
  unfold partialSum maskIco
  rw [← Finset.sum_range_add_sum_Ico _ hjq, add_sub_cancel_left]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_Ico] at hi
  rw [if_pos hi]

/-- The masked families before and after `j` are independent. -/
theorem indepFun_maskLT_maskIco {R : ℕ → Ω → ℝ} (hmeas : ∀ i, Measurable (R i))
    (hindep : iIndepFun R P) (j q : ℕ) : IndepFun (maskLT R j) (maskIco R j q) P := by
  have hdisj : Disjoint (range j) (Finset.Ico j q) := by
    rw [Finset.disjoint_left]
    intro i hi hi'
    rw [Finset.mem_range] at hi
    rw [Finset.mem_Ico] at hi'
    omega
  have h := hindep.indepFun_finset (range j) (Finset.Ico j q) hdisj hmeas
  let ext₁ : (↥(range j) → ℝ) → (ℕ → ℝ) := fun x i => if h : i ∈ range j then x ⟨i, h⟩ else 0
  let ext₂ : (↥(Finset.Ico j q) → ℝ) → (ℕ → ℝ) := fun x i => if h : i ∈ Finset.Ico j q then x ⟨i, h⟩ else 0
  have hext₁ : Measurable ext₁ := by
    apply measurable_pi_lambda
    intro i
    by_cases hi : i ∈ range j
    · simp only [ext₁, hi, dite_true]; exact measurable_pi_apply _
    · simp only [ext₁, hi, dite_false]; exact measurable_const
  have hext₂ : Measurable ext₂ := by
    apply measurable_pi_lambda
    intro i
    by_cases hi : i ∈ Finset.Ico j q
    · simp only [ext₂, hi, dite_true]; exact measurable_pi_apply _
    · simp only [ext₂, hi, dite_false]; exact measurable_const
  have h2 := h.comp hext₁ hext₂
  have e1 : (ext₁ ∘ fun a (i : ↥(range j)) => R (↑i) a) = maskLT R j := by
    funext ω i
    simp [ext₁, maskLT, Finset.mem_range]
  have e2 : (ext₂ ∘ fun a (i : ↥(Finset.Ico j q)) => R (↑i) a) = maskIco R j q := by
    funext ω i
    simp [ext₂, maskIco, Finset.mem_Ico]
  rw [e1, e2] at h2
  exact h2

/-! ### First-crossing sets -/

theorem measurableSet_cross {α : Type*} [MeasurableSpace α] {f : ℕ → α → ℝ}
    (hf : ∀ l, Measurable (f l)) (a : ℝ) (j : ℕ) :
    MeasurableSet {x | a < |f j x| ∧ ∀ l < j, |f l x| ≤ a} := by
  have h1 : MeasurableSet {x | a < |f j x|} := measurableSet_lt measurable_const (hf j).abs
  have h2 : MeasurableSet {x | ∀ l < j, |f l x| ≤ a} := by
    have : {x | ∀ l < j, |f l x| ≤ a} = ⋂ l, ⋂ (_ : l < j), {x | |f l x| ≤ a} := by
      ext x; simp
    rw [this]
    exact MeasurableSet.iInter fun l => MeasurableSet.iInter fun _ =>
      measurableSet_le (hf l).abs measurable_const
  exact h1.inter h2

/-- `A_j = {|S_j| > a, |S_l| ≤ a for all l < j}`. -/
def crossAt (R : ℕ → Ω → ℝ) (a : ℝ) (j : ℕ) : Set Ω :=
  {ω | a < |partialSum R j ω| ∧ ∀ l < j, |partialSum R l ω| ≤ a}

theorem measurableSet_crossAt {R : ℕ → Ω → ℝ} (hmeas : ∀ i, Measurable (R i)) (a : ℝ) (j : ℕ) :
    MeasurableSet (crossAt R a j) :=
  measurableSet_cross (measurable_partialSum hmeas) a j

theorem crossAt_disjoint {R : ℕ → Ω → ℝ} {a : ℝ} {j j' : ℕ} (hne : j ≠ j') {ω : Ω}
    (h1 : ω ∈ crossAt R a j) (h2 : ω ∈ crossAt R a j') : False := by
  rcases lt_or_gt_of_ne hne with h | h
  · exact absurd (h2.2 j h) (not_le.mpr h1.1)
  · exact absurd (h1.2 j' h) (not_le.mpr h2.1)

theorem crossAt_pairwiseDisjoint (R : ℕ → Ω → ℝ) (a : ℝ) (s : Finset ℕ) :
    (↑s : Set ℕ).PairwiseDisjoint (crossAt R a) := by
  intro j _ j' _ hne
  exact Set.disjoint_left.mpr fun ω h1 h2 => crossAt_disjoint hne h1 h2

theorem exists_crossAt {R : ℕ → Ω → ℝ} {a : ℝ} {q : ℕ} {ω : Ω}
    (hex : ∃ k ≤ q, a < |partialSum R k ω|) : ∃ j ≤ q, ω ∈ crossAt R a j := by
  classical
  have hex' : ∃ k, k ≤ q ∧ a < |partialSum R k ω| := hex
  refine ⟨Nat.find hex', (Nat.find_spec hex').1, (Nat.find_spec hex').2, ?_⟩
  intro l hl
  by_contra hcon
  push Not at hcon
  have hlq : l ≤ q := by have := (Nat.find_spec hex').1; omega
  exact Nat.find_min hex' hl ⟨hlq, hcon⟩

/-- The crossing set in the coordinates `x : ℕ → ℝ` (partial sums of `x`). -/
def crossSet (a : ℝ) (j : ℕ) : Set (ℕ → ℝ) :=
  {x | a < |∑ i ∈ range j, x i| ∧ ∀ l < j, |∑ i ∈ range l, x i| ≤ a}

theorem measurableSet_crossSet (a : ℝ) (j : ℕ) : MeasurableSet (crossSet a j) :=
  measurableSet_cross (f := fun l (x : ℕ → ℝ) => ∑ i ∈ range l, x i)
    (fun l => Finset.measurable_sum _ fun i _ => measurable_pi_apply i) a j

theorem mem_crossAt_iff (R : ℕ → Ω → ℝ) (a : ℝ) (j : ℕ) (ω : Ω) :
    ω ∈ crossAt R a j ↔ maskLT R j ω ∈ crossSet a j := by
  simp only [crossAt, crossSet, mem_setOf_eq]
  rw [← partialSum_eq_maskLT R le_rfl ω]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun l hl => by rw [← partialSum_eq_maskLT R hl.le ω]; exact h2 l hl⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun l hl => by rw [partialSum_eq_maskLT R hl.le ω]; exact h2 l hl⟩

/-- `1_{A_j} S_j` and `S_q − S_j` are independent. -/
theorem indepFun_indicator_partialSum_sub {R : ℕ → Ω → ℝ} (hmeas : ∀ i, Measurable (R i))
    (hindep : iIndepFun R P) (a : ℝ) {j q : ℕ} (hjq : j ≤ q) :
    IndepFun ((crossAt R a j).indicator (partialSum R j))
      (fun ω => partialSum R q ω - partialSum R j ω) P := by
  let Φ : (ℕ → ℝ) → ℝ := (crossSet a j).indicator fun x => ∑ i ∈ range j, x i
  let Ψ : (ℕ → ℝ) → ℝ := fun x => ∑ i ∈ Finset.Ico j q, x i
  have hΦ : Measurable Φ :=
    (Finset.measurable_sum _ fun i _ => measurable_pi_apply i).indicator (measurableSet_crossSet a j)
  have hΨ : Measurable Ψ := Finset.measurable_sum _ fun i _ => measurable_pi_apply i
  have h := (indepFun_maskLT_maskIco hmeas hindep j q).comp hΦ hΨ
  have e1 : Φ ∘ maskLT R j = (crossAt R a j).indicator (partialSum R j) := by
    funext ω
    simp only [Function.comp, Φ]
    by_cases hω : ω ∈ crossAt R a j
    · rw [Set.indicator_of_mem hω, Set.indicator_of_mem ((mem_crossAt_iff R a j ω).mp hω),
        partialSum_eq_maskLT R le_rfl ω]
    · rw [Set.indicator_of_notMem hω,
        Set.indicator_of_notMem (fun h => hω ((mem_crossAt_iff R a j ω).mpr h))]
  have e2 : Ψ ∘ maskIco R j q = fun ω => partialSum R q ω - partialSum R j ω := by
    funext ω
    simp only [Function.comp, Ψ]
    exact (sub_partialSum_eq_maskIco R hjq ω).symm
  rw [e1, e2] at h
  exact h

/-! ### The crossing bound and the maximal inequality -/

/-- `a² P(A_j) ≤ E[1_{A_j} S_q²]`. -/
theorem crossAt_bound [IsProbabilityMeasure P] {R : ℕ → Ω → ℝ} (hmeas : ∀ i, Measurable (R i))
    (hindep : iIndepFun R P) (hL2 : ∀ i, MemLp (R i) 2 P) (hmean : ∀ i, ∫ ω, R i ω ∂P = 0)
    {a : ℝ} (ha : 0 < a) {j q : ℕ} (hjq : j ≤ q) :
    a ^ 2 * (P (crossAt R a j)).toReal ≤
      ∫ ω, (crossAt R a j).indicator (fun ω => partialSum R q ω ^ 2) ω ∂P := by
  have hA : MeasurableSet (crossAt R a j) := measurableSet_crossAt hmeas a j
  have hS : ∀ k, MemLp (partialSum R k) 2 P := memLp_partialSum hL2
  have hSm : ∀ k, Measurable (partialSum R k) := measurable_partialSum hmeas
  set D : Ω → ℝ := fun ω => partialSum R q ω - partialSum R j ω with hD_def
  have hDm : Measurable D := (hSm q).sub (hSm j)
  have hD2 : MemLp D 2 P := (hS q).sub (hS j)
  set X : Ω → ℝ := (crossAt R a j).indicator (partialSum R j) with hX_def
  have hXm : Measurable X := (hSm j).indicator hA
  have hX2 : MemLp X 2 P := (hS j).indicator hA
  have hDmean : ∫ ω, D ω ∂P = 0 := by
    rw [hD_def]
    simp only
    rw [integral_sub ((hS q).integrable one_le_two) ((hS j).integrable one_le_two),
      integral_partialSum hL2 hmean, integral_partialSum hL2 hmean, sub_zero]
  have hXD : IndepFun X D P := indepFun_indicator_partialSum_sub hmeas hindep a hjq
  have hcross : ∫ ω, X ω * D ω ∂P = 0 := by
    have := hXD.integral_mul_eq_mul_integral hXm.aestronglyMeasurable hDm.aestronglyMeasurable
    simp only [Pi.mul_apply] at this
    rw [this, hDmean, mul_zero]
  have hpt : ∀ ω, (crossAt R a j).indicator (fun ω => partialSum R j ω ^ 2) ω + 2 * (X ω * D ω) ≤
      (crossAt R a j).indicator (fun ω => partialSum R q ω ^ 2) ω := by
    intro ω
    by_cases hω : ω ∈ crossAt R a j
    · simp only [hX_def, Set.indicator_of_mem hω]
      have : partialSum R q ω = partialSum R j ω + D ω := by simp [hD_def]
      rw [this]
      nlinarith [sq_nonneg (D ω)]
    · simp [hX_def, Set.indicator_of_notMem hω]
  have hf1 : Integrable ((crossAt R a j).indicator fun ω => partialSum R q ω ^ 2) P :=
    (hS q).integrable_sq.indicator hA
  have hf2 : Integrable ((crossAt R a j).indicator fun ω => partialSum R j ω ^ 2) P :=
    (hS j).integrable_sq.indicator hA
  have hg : Integrable (fun ω => X ω * D ω) P := by
    refine ((hX2.integrable_sq.add hD2.integrable_sq).const_mul (1 / 2)).mono'
      (hXm.mul hDm).aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    simp only [Pi.add_apply]
    nlinarith [sq_nonneg (|X ω| - |D ω|), sq_abs (X ω), sq_abs (D ω), abs_nonneg (X ω),
      abs_nonneg (D ω)]
  have hint_le : ∫ ω, ((crossAt R a j).indicator (fun ω => partialSum R j ω ^ 2) ω +
      2 * (X ω * D ω)) ∂P ≤ ∫ ω, (crossAt R a j).indicator (fun ω => partialSum R q ω ^ 2) ω ∂P :=
    integral_mono (hf2.add (hg.const_mul 2)) hf1 hpt
  rw [integral_add hf2 (hg.const_mul 2), integral_const_mul, hcross, mul_zero, add_zero] at hint_le
  have hlow : a ^ 2 * (P (crossAt R a j)).toReal ≤
      ∫ ω, (crossAt R a j).indicator (fun ω => partialSum R j ω ^ 2) ω ∂P := by
    rw [integral_indicator hA]
    have h1 : ∫ _ in crossAt R a j, (a ^ 2 : ℝ) ∂P ≤ ∫ ω in crossAt R a j, partialSum R j ω ^ 2 ∂P := by
      apply setIntegral_mono_on (integrable_const _).integrableOn (hS j).integrable_sq.integrableOn hA
      intro ω hω
      have hω' : a < |partialSum R j ω| :=
        (show a < |partialSum R j ω| ∧ ∀ l < j, |partialSum R l ω| ≤ a from hω).1
      nlinarith [sq_abs (partialSum R j ω), abs_nonneg (partialSum R j ω)]
    rw [setIntegral_const, measureReal_def, smul_eq_mul] at h1
    linarith
  linarith

/-- **Kolmogorov's maximal inequality**: for independent centered `R i ∈ L²`,
`a² · P(∃ k ≤ q, |S_k| > a) ≤ E S_q²`. -/
theorem kolmogorov_maximal [IsProbabilityMeasure P] {R : ℕ → Ω → ℝ} (hmeas : ∀ i, Measurable (R i))
    (hindep : iIndepFun R P) (hL2 : ∀ i, MemLp (R i) 2 P) (hmean : ∀ i, ∫ ω, R i ω ∂P = 0)
    {a : ℝ} (ha : 0 < a) (q : ℕ) :
    a ^ 2 * (P {ω | ∃ k ≤ q, a < |partialSum R k ω|}).toReal ≤ ∫ ω, partialSum R q ω ^ 2 ∂P := by
  have hS : ∀ k, MemLp (partialSum R k) 2 P := memLp_partialSum hL2
  have hE : {ω | ∃ k ≤ q, a < |partialSum R k ω|} = ⋃ j ∈ range (q + 1), crossAt R a j := by
    ext ω
    simp only [mem_setOf_eq, mem_iUnion, Finset.mem_range]
    constructor
    · intro h
      obtain ⟨j, hj, hmem⟩ := exists_crossAt h
      exact ⟨j, by omega, hmem⟩
    · rintro ⟨j, hj, hmem⟩
      exact ⟨j, by omega, hmem.1⟩
  have hmeasA : ∀ j ∈ range (q + 1), MeasurableSet (crossAt R a j) :=
    fun j _ => measurableSet_crossAt hmeas a j
  rw [hE, measure_biUnion_finset (crossAt_pairwiseDisjoint R a _) hmeasA,
    ENNReal.toReal_sum (fun j _ => measure_ne_top _ _), Finset.mul_sum]
  have hterm : ∀ j ∈ range (q + 1), a ^ 2 * (P (crossAt R a j)).toReal ≤
      ∫ ω, (crossAt R a j).indicator (fun ω => partialSum R q ω ^ 2) ω ∂P := fun j hj =>
    crossAt_bound hmeas hindep hL2 hmean ha (by rw [Finset.mem_range] at hj; omega)
  calc ∑ j ∈ range (q + 1), a ^ 2 * (P (crossAt R a j)).toReal
      ≤ ∑ j ∈ range (q + 1), ∫ ω, (crossAt R a j).indicator (fun ω => partialSum R q ω ^ 2) ω ∂P :=
        Finset.sum_le_sum hterm
    _ = ∫ ω, ∑ j ∈ range (q + 1), (crossAt R a j).indicator (fun ω => partialSum R q ω ^ 2) ω ∂P :=
        (integral_finsetSum _ fun j hj => (hS q).integrable_sq.indicator (hmeasA j hj)).symm
    _ ≤ ∫ ω, partialSum R q ω ^ 2 ∂P := by
        apply integral_mono (integrable_finsetSum _ fun j hj => (hS q).integrable_sq.indicator (hmeasA j hj))
          (hS q).integrable_sq
        intro ω
        show ∑ j ∈ range (q + 1), (crossAt R a j).indicator (fun ω => partialSum R q ω ^ 2) ω ≤
          partialSum R q ω ^ 2
        by_cases hex : ∃ j ∈ range (q + 1), ω ∈ crossAt R a j
        · obtain ⟨j₀, hj₀, hmem⟩ := hex
          rw [Finset.sum_eq_single j₀]
          · rw [Set.indicator_of_mem hmem]
          · intro j _ hne
            rw [Set.indicator_of_notMem]
            intro hmem'
            exact crossAt_disjoint hne hmem' hmem
          · intro h; exact absurd hj₀ h
        · push Not at hex
          rw [Finset.sum_eq_zero fun j hj => Set.indicator_of_notMem (hex j hj) _]
          exact sq_nonneg _

/-- `E S_q² = Σ_{i<q} E R_i²` for independent centered `R i ∈ L²`. -/
theorem integral_partialSum_sq [IsProbabilityMeasure P] {R : ℕ → Ω → ℝ} (hindep : iIndepFun R P)
    (hL2 : ∀ i, MemLp (R i) 2 P) (hmean : ∀ i, ∫ ω, R i ω ∂P = 0) (q : ℕ) :
    ∫ ω, partialSum R q ω ^ 2 ∂P = ∑ i ∈ range q, ∫ ω, R i ω ^ 2 ∂P := by
  have hS : MemLp (∑ i ∈ range q, R i) 2 P := memLp_finsetSum' _ fun i _ => hL2 i
  have hSmean : ∫ ω, (∑ i ∈ range q, R i) ω ∂P = 0 := by
    rw [← partialSum_eq_sum]; exact integral_partialSum hL2 hmean q
  have hv := IndepFun.variance_sum (μ := P) (X := R) (s := range q) (fun i _ => hL2 i)
    (fun i _ j _ hij => hindep.indepFun hij)
  rw [variance_eq_sub hS, hSmean] at hv
  have hvi : ∀ i, variance (R i) P = ∫ ω, R i ω ^ 2 ∂P := by
    intro i
    rw [variance_eq_sub (hL2 i), hmean i]
    simp
  simp only [hvi] at hv
  rw [partialSum_eq_sum]
  simpa using hv

/-- Kolmogorov's maximal inequality with a uniform second-moment bound `E R_i² ≤ C`:
`a² · P(∃ k ≤ q, |S_k| > a) ≤ C q`. -/
theorem kolmogorov_maximal_of_sq_le [IsProbabilityMeasure P] {R : ℕ → Ω → ℝ}
    (hmeas : ∀ i, Measurable (R i)) (hindep : iIndepFun R P) (hL2 : ∀ i, MemLp (R i) 2 P)
    (hmean : ∀ i, ∫ ω, R i ω ∂P = 0) {C : ℝ} (hsq : ∀ i, ∫ ω, R i ω ^ 2 ∂P ≤ C) {a : ℝ}
    (ha : 0 < a) (q : ℕ) :
    a ^ 2 * (P {ω | ∃ k ≤ q, a < |partialSum R k ω|}).toReal ≤ C * q := by
  refine (kolmogorov_maximal hmeas hindep hL2 hmean ha q).trans ?_
  rw [integral_partialSum_sq hindep hL2 hmean q]
  calc ∑ i ∈ range q, ∫ ω, R i ω ^ 2 ∂P ≤ ∑ _i ∈ range q, C := Finset.sum_le_sum fun i _ => hsq i
    _ = C * q := by simp [mul_comm]

end Ripple.Kurtz.StrongApprox
