import Ripple.Kurtz.StrongApprox.SectionFourGaussianLaw

/-!
# Bounds for the constructed fundamental evolution

The evolution is the actual columnwise Volterra construction. Its action on
an arbitrary vector solves the homogeneous equation with that initial vector.
No independently supplied transition matrix or evolution law is assumed.
-/

noncomputable section
open Set MeasureTheory
open scoped BigOperators NNReal

namespace Ripple.Kurtz.StrongApprox.VolterraGaussian

variable {d : ℕ}

/-- The columnwise evolution, bundled as a continuous linear map. -/
def fundamentalCLM (A : ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ))
    (T t s : ℝ) : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) :=
  ∑ j : Fin d, (ContinuousLinearMap.proj j).smulRight
    (fun i => fundamentalMatrix A T t s i j)

@[simp] theorem fundamentalCLM_apply
    (A : ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) (T t s : ℝ) (x : Fin d → ℝ) :
    fundamentalCLM A T t s x =
      ∑ j : Fin d, x j • (fun i => fundamentalMatrix A T t s i j) := by
  simp [fundamentalCLM]

/-- The finite column sum has initial value `x` and solves the genuine
homogeneous equation on the translated interval. -/
theorem fundamentalCLM_solution
    {A : ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)} {T s : ℝ}
    (hA : Continuous A) (hs : s ≤ T) (x : Fin d → ℝ) :
    Analysis.LinearVolterra.IsSolution (fun r => A (s + r)) (fun _ => x)
      (fun r => fundamentalCLM A T (s + r) s x) (T - s) := by
  have hshift : Continuous (fun r => A (s + r)) :=
    hA.comp (continuous_const.add continuous_id)
  have hsum := isSolution_finsetSum Finset.univ hshift
    (fun j _ => isSolution_smul (fundamentalMatrix_column_solution hA hs j) (x j))
  have hforcing : (fun _ : ℝ => ∑ j : Fin d, x j • Pi.single j (1 : ℝ)) =
      (fun _ : ℝ => x) := by
    funext r i
    simp [Pi.single_apply, eq_comm]
  change Analysis.LinearVolterra.IsSolution (fun r => A (s + r))
    (fun _ => ∑ j : Fin d, x j • Pi.single j (1 : ℝ))
    (fun r => ∑ j : Fin d, x j • (fun i => fundamentalMatrix A T (s + r) s i j))
    (T - s) at hsum
  rw [hforcing] at hsum
  simpa only [fundamentalCLM_apply] using hsum

/-- At its initial time the evolution acts as the identity on every vector. -/
theorem fundamentalCLM_diagonal
    {A : ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)} {T s : ℝ}
    (hA : Continuous A) (hs : s ≤ T) : fundamentalCLM A T s s = 1 := by
  apply ContinuousLinearMap.ext
  intro x
  have h := (fundamentalCLM_solution hA hs x).equation 0
    ⟨le_rfl, sub_nonneg.mpr hs⟩
  simpa using h

/-- The chosen evolution agrees with the chosen solver for every constant
forcing, rather than just for the basis columns used to define it. -/
theorem fundamentalCLM_eq_volterraSol
    {A : ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)} {T s : ℝ} {K : ℝ≥0}
    (hA : Continuous A) (hs : s ≤ T)
    (hAb : ∀ r ∈ Icc s T, ‖A r‖ ≤ K) (x : Fin d → ℝ)
    {t : ℝ} (ht : t ∈ Icc s T) :
    fundamentalCLM A T t s x =
      volterraSol (fun r => A (s + r)) (T - s) (fun _ => x) (t - s) := by
  have hshift : Continuous (fun r => A (s + r)) :=
    hA.comp (continuous_const.add continuous_id)
  have hbound : ∀ r ∈ Icc 0 (T - s), ‖A (s + r)‖ ≤ K := by
    intro r hr
    apply hAb
    constructor <;> linarith [hr.1, hr.2]
  have h := Analysis.LinearVolterra.eqOn_of_solution hshift
    (fundamentalCLM_solution hA hs x)
    (volterraSol_spec hshift continuous_const (sub_nonneg.mpr hs))
    (sub_nonneg.mpr hs) K.coe_nonneg hbound
    ⟨sub_nonneg.mpr ht.1, sub_le_sub_right ht.2 s⟩
  simpa using h

/-- The usual exponential bound is derived for the actual column construction. -/
theorem norm_fundamentalCLM_apply_le
    {A : ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)} {T s : ℝ} {K : ℝ≥0}
    (hA : Continuous A) (hs : s ≤ T)
    (hAb : ∀ r ∈ Icc s T, ‖A r‖ ≤ K) (x : Fin d → ℝ)
    {t : ℝ} (ht : t ∈ Icc s T) :
    ‖fundamentalCLM A T t s x‖ ≤ ‖x‖ * Real.exp ((K : ℝ) * (t - s)) := by
  have hshift : Continuous (fun r => A (s + r)) :=
    hA.comp (continuous_const.add continuous_id)
  have hbound : ∀ r ∈ Icc 0 (T - s), ‖A (s + r)‖ ≤ K := by
    intro r hr
    apply hAb
    constructor <;> linarith [hr.1, hr.2]
  have h := Analysis.LinearVolterra.norm_le_exp hshift
    (fundamentalCLM_solution hA hs x) (sub_nonneg.mpr hs)
    (norm_nonneg x) K.coe_nonneg hbound (fun _ _ => le_rfl)
    (t - s) ⟨sub_nonneg.mpr ht.1, sub_le_sub_right ht.2 s⟩
  simpa using h

/-- Operator norm form of the exponential estimate. -/
theorem norm_fundamentalCLM_le
    {A : ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)} {T s : ℝ} {K : ℝ≥0}
    (hA : Continuous A) (hs : s ≤ T)
    (hAb : ∀ r ∈ Icc s T, ‖A r‖ ≤ K)
    {t : ℝ} (ht : t ∈ Icc s T) :
    ‖fundamentalCLM A T t s‖ ≤ Real.exp ((K : ℝ) * (t - s)) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.exp_nonneg _)
  intro x
  simpa only [mul_comm] using norm_fundamentalCLM_apply_le hA hs hAb x ht

/-- Each forward column trajectory is continuous, with no assumption about
the arbitrary values of the selected solver outside its construction window. -/
theorem continuous_fundamentalCLM_forward
    {A : ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)} {T s : ℝ}
    (hA : Continuous A) (hs : s ≤ T) (x : Fin d → ℝ) :
    Continuous (fun t => fundamentalCLM A T t s x) := by
  have h := (fundamentalCLM_solution hA hs x).continuous.comp
    (continuous_id.sub (continuous_const : Continuous fun _ : ℝ => s))
  have h2 : (fun t => fundamentalCLM A T t s x) =
      fun t => fundamentalCLM A T (s + (t - s)) s x := by
    funext t
    rw [add_sub_cancel]
  rw [h2]
  exact h

end Ripple.Kurtz.StrongApprox.VolterraGaussian
