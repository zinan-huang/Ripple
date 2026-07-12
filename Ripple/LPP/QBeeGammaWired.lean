/-
  Ripple.LPP.QBeeGammaWired

  Wiring audit for the QBee gamma certificate and the general LPP stages.
-/

import Ripple.LPP.QBeeGammaDualRail23Square
import Ripple.CTMC.FrozenGeneratorBridge
import Ripple.DualRail.Combination
import Ripple.Core.ODEBox

namespace Ripple.LPP.QBee

open Ripple

/-- The emitted QBee field is not CRN-implementable on the whole
non-negative orthant.  At the `Esym` boundary (`y 9 = 0`), taking `e = 2`
makes the ninth component point out of the orthant. -/
theorem gammaQuadField_not_isCRNImplementable
    (hcrn : IsCRNImplementable 18 gammaQuadField) : False := by
  let y : Fin 18 → ℝ := fun i => if i = 8 then 2 else 0
  have hy : ∀ i, 0 ≤ y i := by
    intro i
    simp only [y]
    split_ifs <;> norm_num
  have hy9 : y 9 = 0 := by simp [y]
  have hinward : 0 ≤ gammaQuadField y 9 :=
    crn_boundary_nonneg hcrn hy hy9
  have hvalue : gammaQuadField y 9 = -1 := by
    change y 9 * y 8 - y 9 - y 8 + 1 = -1
    have hy8 : y 8 = 2 := by simp [y]
    rw [hy9, hy8]
    norm_num
  linarith

/-- A positive constant dilation is only a time rescaling, so it retains the
same outward-pointing boundary component. -/
theorem constantDilation_gammaQuadField_not_isCRNImplementable
    {ε : ℝ} (hε : 0 < ε)
    (hcrn : IsCRNImplementable 18 (constantDilation ε gammaQuadField)) : False := by
  let y : Fin 18 → ℝ := fun i => if i = 8 then 2 else 0
  have hy : ∀ i, 0 ≤ y i := by
    intro i
    simp only [y]
    split_ifs <;> norm_num
  have hy9 : y 9 = 0 := by simp [y]
  have hinward : 0 ≤ constantDilation ε gammaQuadField y 9 :=
    crn_boundary_nonneg hcrn hy hy9
  have hquad : gammaQuadField y 9 = -1 := by
    change y 9 * y 8 - y 9 - y 8 + 1 = -1
    have hy8 : y 8 = 2 := by simp [y]
    rw [hy9, hy8]
    norm_num
  have hvalue : constantDilation ε gammaQuadField y 9 = -ε := by
    simp [constantDilation, hquad]
  linarith

/-! ## Senior-author pipeline: dual rail → CRN → QBee → BD → squaring → Kurtz -/

open Generated.GammaDualRail23

/-- Initial condition of the 14-coordinate gamma GPAC. -/
noncomputable def gammaInit14 : Fin 14 → ℝ :=
  ![0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0]

/-- Tight semantic contract for the journal's compact 14→23 front end.
The initial condition is essential: the five unrailed coordinates are kept
as actual non-negative CRN concentrations. -/
def TightSelectiveSemanticLift : Prop :=
  DualRail.TightSelectiveSemanticSpec gammaField origField
    gammaInit14 0 dualRailDecode

private noncomputable def railSum (z : Fin 23 → ℝ) (j : Fin 9) : ℝ :=
  z ⟨2 * j.val, by have := j.isLt; omega⟩ +
    z ⟨2 * j.val + 1, by have := j.isLt; omega⟩

private noncomputable def railDiff (z : Fin 23 → ℝ) (j : Fin 9) : ℝ :=
  z ⟨2 * j.val, by have := j.isLt; omega⟩ -
    z ⟨2 * j.val + 1, by have := j.isLt; omega⟩

private noncomputable def railD (beta : ℝ) : ℝ := beta + 1
private noncomputable def railB4 (beta : ℝ) : ℝ := railD beta + 3
private noncomputable def railB5 (beta : ℝ) : ℝ :=
  railD beta ^ 2 + railD beta + 4
private noncomputable def railB6 (beta : ℝ) : ℝ :=
  railD beta + 2 * railB4 beta + 3
private noncomputable def railB7 (beta : ℝ) : ℝ :=
  railD beta + railB4 beta + 3
private noncomputable def railB1 (beta : ℝ) : ℝ :=
  railD beta + (railB6 beta + 1) * railB7 beta * (railB4 beta + 1) + 1
private noncomputable def railB3 (beta : ℝ) : ℝ :=
  railD beta + (railB5 beta + 1) * (railB4 beta + 1) + 2
private noncomputable def railB2 (beta : ℝ) : ℝ :=
  railD beta + railB3 beta + railB4 beta + 3
private noncomputable def railB0 (beta : ℝ) : ℝ :=
  railD beta + railB2 beta + 1
private noncomputable def railB8 (beta : ℝ) : ℝ :=
  railD beta + 2 * (beta + 1) + 1

private noncomputable def railBound (beta : ℝ) : Fin 9 → ℝ :=
  ![railB0 beta, railB1 beta, railB2 beta, railB3 beta, railB4 beta,
    railB5 beta, railB6 beta, railB7 beta, railB8 beta]

private noncomputable def selectiveBound (beta : ℝ) : ℝ :=
  beta + 1 + ∑ j : Fin 9, railBound beta j

private theorem railBound_nonneg {beta : ℝ} (hbeta : 0 < beta) :
    ∀ j : Fin 9, 0 ≤ railBound beta j := by
  intro j
  have hD : 0 ≤ railD beta := by simp [railD]; linarith
  have h4 : 0 ≤ railB4 beta := by simp [railB4]; linarith
  have h5 : 0 ≤ railB5 beta := by
    simp [railB5]
    nlinarith [sq_nonneg (railD beta)]
  have h6 : 0 ≤ railB6 beta := by simp [railB6]; linarith
  have h7 : 0 ≤ railB7 beta := by simp [railB7]; linarith
  have h3 : 0 ≤ railB3 beta := by
    have hp : 0 ≤ (railB5 beta + 1) * (railB4 beta + 1) :=
      mul_nonneg (by linarith) (by linarith)
    simp [railB3]
    linarith
  have h2 : 0 ≤ railB2 beta := by simp [railB2]; linarith
  have h0 : 0 ≤ railB0 beta := by simp [railB0]; linarith
  have h1 : 0 ≤ railB1 beta := by
    have hp : 0 ≤ (railB6 beta + 1) * railB7 beta * (railB4 beta + 1) :=
      mul_nonneg (mul_nonneg (by linarith) h7) (by linarith)
    simp [railB1]
    linarith
  have h8 : 0 ≤ railB8 beta := by simp [railB8]; linarith
  fin_cases j <;> simp [railBound] <;> assumption

/-- Exterior-region barrier on a half-open interval.  The endpoint is chosen
strictly before `T`, where the supplied `HasDerivAt` data is available. -/
private theorem upper_barrier_on_Ico {T b : ℝ} (_hT : 0 < T)
    (g gp : ℝ → ℝ) (hg0 : g 0 ≤ b)
    (hderiv : ∀ t ∈ Set.Ico (0 : ℝ) T, HasDerivAt g (gp t) t)
    (hbar : ∀ t ∈ Set.Ico (0 : ℝ) T, b ≤ g t → gp t ≤ 0) :
    ∀ t ∈ Set.Ico (0 : ℝ) T, g t ≤ b := by
  intro t ht
  have hcont : ContinuousOn g (Set.Icc (0 : ℝ) t) := by
    intro s hs
    exact (hderiv s ⟨hs.1, lt_of_le_of_lt hs.2 ht.2⟩).continuousAt.continuousWithinAt
  have hderiv' : ∀ s ∈ Set.Ico (0 : ℝ) t,
      HasDerivWithinAt g (gp s) (Set.Ici s) s := by
    intro s hs
    exact (hderiv s ⟨hs.1, lt_trans hs.2 ht.2⟩).hasDerivWithinAt
  exact scalar_upper_barrier_exterior_on_Icc ht.1 g gp hg0 hcont hderiv'
    (fun s hs ↦ hbar s ⟨hs.1, lt_trans hs.2 ht.2⟩) t ⟨ht.1, le_rfl⟩

/-- A common annihilation term bounds a rail pair once its difference and
the non-annihilation production are bounded. -/
private theorem pair_drift_nonpos
    {u v D P C K drift : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hD : 0 ≤ D)
    (hP : 0 ≤ P) (hC : 0 ≤ C) (hK : 4 ≤ K)
    (hdiff : |u - v| ≤ D)
    (hwall : D + P + C + 1 ≤ u + v)
    (hdrift : drift ≤ P + C * (u + v) - K * u * v) :
    drift ≤ 0 := by
  set s : ℝ := u + v
  have hs0 : 0 ≤ s := add_nonneg hu hv
  have hs1 : 1 ≤ s := by dsimp only [s]; linarith
  have hsq : (u - v) ^ 2 ≤ D ^ 2 := by
    rw [sq_le_sq]
    simpa [abs_of_nonneg hD] using hdiff
  have hA : P + C + 1 ≤ s - D := by dsimp only [s]; linarith
  have hsD : 0 ≤ s - D := by linarith
  have hsDp : 0 ≤ s + D := by linarith
  have hprod : (P + C + 1) * s ≤ (s - D) * (s + D) := by
    calc
      (P + C + 1) * s ≤ (s - D) * s :=
        mul_le_mul_of_nonneg_right hA hs0
      _ ≤ (s - D) * (s + D) :=
        mul_le_mul_of_nonneg_left (by linarith) hsD
  have hPC : P + C * s ≤ (P + C + 1) * s := by
    have hPs : P ≤ P * s := by nlinarith [mul_nonneg hP (sub_nonneg.mpr hs1)]
    nlinarith
  have huv : 0 ≤ u * v := mul_nonneg hu hv
  have hfour : 4 * (u * v) = s ^ 2 - (u - v) ^ 2 := by
    dsimp only [s]
    ring
  have hbase : P + C * s ≤ 4 * (u * v) := by
    rw [hfour]
    nlinarith [hprod]
  have hKann : 4 * (u * v) ≤ K * (u * v) :=
    mul_le_mul_of_nonneg_right hK huv
  dsimp only [s] at hbase
  nlinarith

private theorem gammaField_contDiff : ContDiff ℝ ⊤ gammaField := by
  apply contDiff_pi'
  intro i
  fin_cases i <;> simp [gammaField, Matrix.cons_val_zero,
    Matrix.cons_val_one] <;> fun_prop

private theorem origField_contDiff : ContDiff ℝ ⊤ origField := by
  apply contDiff_pi'
  intro i
  fin_cases i <;> simp [origField, Matrix.cons_val_zero,
    Matrix.cons_val_one] <;> fun_prop

/-- Local semantic half of the selective construction: any candidate
23-coordinate solution starting at zero decodes to the prescribed gamma
trajectory.  Compact-interval ODE uniqueness is sufficient; no a-priori
bound on the candidate is used here. -/
private theorem selective_decode_eq_on_Ico
    {x : ℝ → Fin 14 → ℝ} {y : ℝ → Fin 23 → ℝ} {T : ℝ}
    (_hT : 0 < T) (hinit : x 0 = gammaInit14)
    (hx : ∀ t : ℝ, 0 ≤ t → HasDerivAt x (gammaField (x t)) t)
    (hy0 : y 0 = 0)
    (hy : ∀ t ∈ Set.Ico (0 : ℝ) T,
      HasDerivAt y (origField (y t)) t) :
    ∀ t ∈ Set.Ico (0 : ℝ) T, dualRailDecode (y t) = x t := by
  set z : ℝ → Fin 14 → ℝ := fun t ↦ dualRailDecode (y t) with hz
  have hz0 : z 0 = gammaInit14 := by
    simp [hz, hy0, dualRailDecode, gammaInit14]
  have hzderiv : ∀ t ∈ Set.Ico (0 : ℝ) T,
      HasDerivAt z (gammaField (z t)) t := by
    intro t ht
    exact origField_solution_projects_at (hy t ht)
  have hlip := contDiff_locally_lipschitz gammaField_contDiff
  intro t' ht'
  have ht'0 : 0 ≤ t' := ht'.1
  have ht'T : t' < T := ht'.2
  set t : ℝ := t' + (T - t') / 2 with ht
  have htt : t' ≤ t := by dsimp only [t]; linarith
  have htT : t < T := by dsimp only [t]; linarith
  have ht0 : 0 < t := by dsimp only [t]; linarith
  have hzcont : ContinuousOn z (Set.Icc (0 : ℝ) t) := by
    intro s hs
    exact (hzderiv s ⟨hs.1, lt_of_le_of_lt hs.2 htT⟩).continuousAt.continuousWithinAt
  have hxcont : ContinuousOn x (Set.Icc (0 : ℝ) t) := by
    intro s hs
    exact (hx s hs.1).continuousAt.continuousWithinAt
  obtain ⟨sz, _hsz, hszmax⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.mpr ht0.le) hzcont.norm
  obtain ⟨sx, _hsx, hsxmax⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.mpr ht0.le) hxcont.norm
  set M : ℝ := max ‖z sz‖ ‖x sx‖ + 1 with hM
  have hMpos : 0 < M := by
    dsimp only [M]
    have := norm_nonneg (z sz)
    have := norm_nonneg (x sx)
    linarith [le_max_left ‖z sz‖ ‖x sx‖]
  have hzbound : ∀ s ∈ Set.Icc (0 : ℝ) t, ‖z s‖ ≤ M := by
    intro s hs
    dsimp only [M]
    have hle : ‖z s‖ ≤ ‖z sz‖ := hszmax hs
    exact le_trans hle (le_trans (le_max_left _ _) (by linarith))
  have hxbound : ∀ s ∈ Set.Icc (0 : ℝ) t, ‖x s‖ ≤ M := by
    intro s hs
    dsimp only [M]
    have hle : ‖x s‖ ≤ ‖x sx‖ := hsxmax hs
    exact le_trans hle (le_trans (le_max_right _ _) (by linarith))
  have hzwithin : ∀ s ∈ Set.Icc (0 : ℝ) t,
      HasDerivWithinAt z (gammaField (z s)) (Set.Icc 0 t) s := by
    intro s hs
    exact (hzderiv s ⟨hs.1, lt_of_le_of_lt hs.2 htT⟩).hasDerivWithinAt
  have hxwithin : ∀ s ∈ Set.Icc (0 : ℝ) t,
      HasDerivWithinAt x (gammaField (x s)) (Set.Icc 0 t) s := by
    intro s hs
    exact (hx s hs.1).hasDerivWithinAt
  have heq : Set.EqOn z x (Set.Icc (0 : ℝ) t) :=
    solutions_agree_on_Icc ht0 hMpos.le hlip hz0 hinit
      hzwithin hxwithin hzbound hxbound
  exact heq ⟨ht'.1, htt⟩

private theorem railSum_hasDerivAt
    {y : ℝ → Fin 23 → ℝ} {t : ℝ}
    (hy : HasDerivAt y (origField (y t)) t) (j : Fin 9) :
    HasDerivAt (fun s ↦ railSum (y s) j)
      (origField (y t) ⟨2 * j.val, by have := j.isLt; omega⟩ +
        origField (y t) ⟨2 * j.val + 1, by have := j.isLt; omega⟩) t := by
  exact (hasDerivAt_pi.mp hy _).add (hasDerivAt_pi.mp hy _)

private theorem railDiff_bound_of_decode
    {x : ℝ → Fin 14 → ℝ} {y : ℝ → Fin 23 → ℝ}
    {beta t : ℝ}
    (hdecode : dualRailDecode (y t) = x t)
    (hbound : ∀ i, |x t i| ≤ beta) :
    ∀ j : Fin 9, |railDiff (y t) j| ≤ railD beta := by
  intro j
  have hD : beta ≤ railD beta := by simp [railD]
  fin_cases j
  · change |railDiff (y t) 0| ≤ railD beta
    have h := congrFun hdecode 0
    have heq : railDiff (y t) 0 = x t 0 := by
      simpa [dualRailDecode, railDiff] using h
    rw [heq]
    exact (hbound 0).trans hD
  · change |railDiff (y t) 1| ≤ railD beta
    have h := congrFun hdecode 1
    have heq : railDiff (y t) 1 = x t 1 := by
      simpa [dualRailDecode, railDiff] using h
    rw [heq]
    exact (hbound 1).trans hD
  · change |railDiff (y t) 2| ≤ railD beta
    have h := congrFun hdecode 2
    have heq : railDiff (y t) 2 = x t 2 := by
      simpa [dualRailDecode, railDiff] using h
    rw [heq]
    exact (hbound 2).trans hD
  · change |railDiff (y t) 3| ≤ railD beta
    have h := congrFun hdecode 3
    have heq : railDiff (y t) 3 = x t 3 := by
      simpa [dualRailDecode, railDiff] using h
    rw [heq]
    exact (hbound 3).trans hD
  · change |railDiff (y t) 4| ≤ railD beta
    have h := congrFun hdecode 4
    have heq : railDiff (y t) 4 = x t 4 - 1 := by
      simp [dualRailDecode, railDiff] at h ⊢
      linarith
    rw [heq]
    calc
      |x t 4 - 1| ≤ |x t 4| + |(1 : ℝ)| := abs_sub _ _
      _ ≤ railD beta := by simpa [railD] using add_le_add_right (hbound 4) 1
  · change |railDiff (y t) 5| ≤ railD beta
    have h := congrFun hdecode 5
    have heq : railDiff (y t) 5 = x t 5 - 1 := by
      simp [dualRailDecode, railDiff] at h ⊢
      linarith
    rw [heq]
    calc
      |x t 5 - 1| ≤ |x t 5| + |(1 : ℝ)| := abs_sub _ _
      _ ≤ railD beta := by simpa [railD] using add_le_add_right (hbound 5) 1
  · change |railDiff (y t) 6| ≤ railD beta
    have h := congrFun hdecode 6
    have heq : railDiff (y t) 6 = x t 6 - 1 := by
      simp [dualRailDecode, railDiff] at h ⊢
      linarith
    rw [heq]
    calc
      |x t 6 - 1| ≤ |x t 6| + |(1 : ℝ)| := abs_sub _ _
      _ ≤ railD beta := by simpa [railD] using add_le_add_right (hbound 6) 1
  · change |railDiff (y t) 7| ≤ railD beta
    have h := congrFun hdecode 7
    have heq : railDiff (y t) 7 = x t 7 := by
      simpa [dualRailDecode, railDiff] using h
    rw [heq]
    exact (hbound 7).trans hD
  · change |railDiff (y t) 8| ≤ railD beta
    have h := congrFun hdecode 9
    have heq : railDiff (y t) 8 = x t 9 := by
      simpa [dualRailDecode, railDiff] using h
    rw [heq]
    exact (hbound 9).trans hD

private theorem selective_base_bounds
    {x : ℝ → Fin 14 → ℝ} {y : ℝ → Fin 23 → ℝ}
    {beta T : ℝ} (hbeta : 0 < beta) (hT : 0 < T)
    (hinit : x 0 = gammaInit14)
    (hx : ∀ t : ℝ, 0 ≤ t → HasDerivAt x (gammaField (x t)) t)
    (hbound : ∀ t : ℝ, 0 ≤ t → ∀ i, |x t i| ≤ beta)
    (hy0 : y 0 = 0)
    (hy : ∀ t ∈ Set.Ico (0 : ℝ) T,
      HasDerivAt y (origField (y t)) t) :
    (∀ t ∈ Set.Ico (0 : ℝ) T, dualRailDecode (y t) = x t) ∧
    (∀ t ∈ Set.Ico (0 : ℝ) T, ∀ i, 0 ≤ y t i) ∧
    (∀ t ∈ Set.Ico (0 : ℝ) T, railSum (y t) 4 ≤ railB4 beta) ∧
    (∀ t ∈ Set.Ico (0 : ℝ) T, railSum (y t) 5 ≤ railB5 beta) := by
  have hlip := contDiff_locally_lipschitz origField_contDiff
  have htrack := selective_decode_eq_on_Ico hT hinit hx hy0 hy
  have hnn : ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ i, 0 ≤ y t i := by
    apply crn_local_nonneg origField_crn hlip T hT y
    · intro i
      simp [hy0]
    · exact hy
  have hdiff : ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ j : Fin 9,
      |railDiff (y t) j| ≤ railD beta := by
    intro t ht
    exact railDiff_bound_of_decode (htrack t ht) (hbound t ht.1)
  have hD : 0 ≤ railD beta := by simp [railD]; linarith
  have hs4 : ∀ t ∈ Set.Ico (0 : ℝ) T,
      railSum (y t) 4 ≤ railB4 beta := by
    apply upper_barrier_on_Ico hT
      (fun t ↦ railSum (y t) 4)
      (fun t ↦ origField (y t) 8 + origField (y t) 9)
    · simp [hy0, railSum, railB4, railD]
      linarith
    · intro t ht
      exact railSum_hasDerivAt (hy t ht) 4
    · intro t ht hwall
      refine pair_drift_nonpos
        (u := y t 8) (v := y t 9) (D := railD beta)
        (P := 1) (C := 1) (K := 136)
        (drift := origField (y t) 8 + origField (y t) 9)
        (hnn t ht 8) (hnn t ht 9) hD (by norm_num) (by norm_num)
        (by norm_num) (hdiff t ht 4) ?_ ?_
      · simp [railB4, railSum] at hwall ⊢
        linarith
      · simp [origField]
        ring_nf
        exact le_rfl
  have hs5 : ∀ t ∈ Set.Ico (0 : ℝ) T,
      railSum (y t) 5 ≤ railB5 beta := by
    apply upper_barrier_on_Ico hT
      (fun t ↦ railSum (y t) 5)
      (fun t ↦ origField (y t) 10 + origField (y t) 11)
    · simp [hy0, railSum, railB5, railD]
      nlinarith
    · intro t ht
      exact railSum_hasDerivAt (hy t ht) 5
    · intro t ht hwall
      have hd2 : railDiff (y t) 5 ^ 2 ≤ railD beta ^ 2 := by
        rw [sq_le_sq]
        simpa [abs_of_nonneg hD] using hdiff t ht 5
      refine pair_drift_nonpos
        (u := y t 10) (v := y t 11) (D := railD beta)
        (P := railD beta ^ 2 + 1) (C := 2) (K := 132)
        (drift := origField (y t) 10 + origField (y t) 11)
        (hnn t ht 10) (hnn t ht 11) hD (by positivity) (by norm_num)
        (by norm_num) (hdiff t ht 5) ?_ ?_
      · simp [railB5, railSum] at hwall ⊢
        nlinarith
      · simp [origField, railDiff] at hd2 ⊢
        nlinarith
  exact ⟨htrack, hnn, hs4, hs5⟩

private theorem selective_rail_bounds
    {x : ℝ → Fin 14 → ℝ} {y : ℝ → Fin 23 → ℝ}
    {beta T : ℝ} (hbeta : 0 < beta) (hT : 0 < T)
    (hinit : x 0 = gammaInit14)
    (hx : ∀ t : ℝ, 0 ≤ t → HasDerivAt x (gammaField (x t)) t)
    (hbound : ∀ t : ℝ, 0 ≤ t → ∀ i, |x t i| ≤ beta)
    (hy0 : y 0 = 0)
    (hy : ∀ t ∈ Set.Ico (0 : ℝ) T,
      HasDerivAt y (origField (y t)) t) :
    ∀ j : Fin 9, ∀ t ∈ Set.Ico (0 : ℝ) T,
      railSum (y t) j ≤ railBound beta j := by
  obtain ⟨htrack, hnn, hs4, hs5⟩ :=
    selective_base_bounds hbeta hT hinit hx hbound hy0 hy
  have hdiff : ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ j : Fin 9,
      |railDiff (y t) j| ≤ railD beta := by
    intro t ht
    exact railDiff_bound_of_decode (htrack t ht) (hbound t ht.1)
  have hD : 0 ≤ railD beta := by simp [railD]; linarith
  have hB4 : 0 ≤ railB4 beta := by simp [railB4]; linarith
  have hB5 : 0 ≤ railB5 beta := by
    simp [railB5]
    nlinarith [sq_nonneg (railD beta)]
  have hB6 : 0 ≤ railB6 beta := by simp [railB6]; linarith
  have hB7 : 0 ≤ railB7 beta := by simp [railB7]; linarith
  have hB3 : 0 ≤ railB3 beta := by
    simp [railB3]
    have hp : 0 ≤ (railB5 beta + 1) * (railB4 beta + 1) :=
      mul_nonneg (by linarith) (by linarith)
    linarith
  have hB2 : 0 ≤ railB2 beta := by simp [railB2]; linarith
  have hB0 : 0 ≤ railB0 beta := by simp [railB0]; linarith
  have hs6 : ∀ t ∈ Set.Ico (0 : ℝ) T,
      railSum (y t) 6 ≤ railB6 beta := by
    apply upper_barrier_on_Ico hT
      (fun t ↦ railSum (y t) 6)
      (fun t ↦ origField (y t) 12 + origField (y t) 13)
    · simp [hy0, railSum, railB6, railB4, railD]
      linarith
    · intro t ht
      exact railSum_hasDerivAt (hy t ht) 6
    · intro t ht hwall
      have h4 := hs4 t ht
      have hfac : y t 8 + y t 9 + 1 ≤ railB4 beta + 1 := by
        simp [railSum] at h4
        linarith
      have hnon : 0 ≤ y t 12 + y t 13 + 1 := by
        linarith [hnn t ht 12, hnn t ht 13]
      have hmul := mul_le_mul_of_nonneg_right hfac hnon
      refine pair_drift_nonpos
        (u := y t 12) (v := y t 13) (D := railD beta)
        (P := railB4 beta + 1) (C := railB4 beta + 1) (K := 136)
        (drift := origField (y t) 12 + origField (y t) 13)
        (hnn t ht 12) (hnn t ht 13) hD (by linarith) (by linarith)
        (by norm_num) (hdiff t ht 6) ?_ ?_
      · simp [railB6, railSum] at hwall ⊢
        linarith
      · calc
          origField (y t) 12 + origField (y t) 13 =
              (y t 8 + y t 9 + 1) * (y t 12 + y t 13 + 1) -
                136 * y t 12 * y t 13 := by simp [origField]; ring
          _ ≤ (railB4 beta + 1) * (y t 12 + y t 13 + 1) -
                136 * y t 12 * y t 13 := sub_le_sub_right hmul _
          _ = (railB4 beta + 1) + (railB4 beta + 1) *
                (y t 12 + y t 13) - 136 * y t 12 * y t 13 := by ring
  have hs7 : ∀ t ∈ Set.Ico (0 : ℝ) T,
      railSum (y t) 7 ≤ railB7 beta := by
    apply upper_barrier_on_Ico hT
      (fun t ↦ railSum (y t) 7)
      (fun t ↦ origField (y t) 14 + origField (y t) 15)
    · simp [hy0, railSum, railB7, railB4, railD]
      linarith
    · intro t ht
      exact railSum_hasDerivAt (hy t ht) 7
    · intro t ht hwall
      have h4 := hs4 t ht
      refine pair_drift_nonpos
        (u := y t 14) (v := y t 15) (D := railD beta)
        (P := railB4 beta + 1) (C := 1) (K := 136)
        (drift := origField (y t) 14 + origField (y t) 15)
        (hnn t ht 14) (hnn t ht 15) hD (by linarith) (by norm_num)
        (by norm_num) (hdiff t ht 7) ?_ ?_
      · simp [railB7, railSum] at hwall ⊢
        linarith
      · simp [origField, railSum] at h4 ⊢
        linarith
  have hs3 : ∀ t ∈ Set.Ico (0 : ℝ) T,
      railSum (y t) 3 ≤ railB3 beta := by
    apply upper_barrier_on_Ico hT
      (fun t ↦ railSum (y t) 3)
      (fun t ↦ origField (y t) 6 + origField (y t) 7)
    · simp [hy0, railSum, railB3, railB4, railB5, railD]
      positivity
    · intro t ht
      exact railSum_hasDerivAt (hy t ht) 3
    · intro t ht hwall
      have h4 := hs4 t ht
      have h5 := hs5 t ht
      have hfac4 : y t 8 + y t 9 + 1 ≤ railB4 beta + 1 := by
        simp [railSum] at h4
        linarith
      have hfac5 : y t 10 + y t 11 + 1 ≤ railB5 beta + 1 := by
        simp [railSum] at h5
        linarith
      have hnon4 : 0 ≤ y t 8 + y t 9 + 1 := by
        linarith [hnn t ht 8, hnn t ht 9]
      have hmul : (y t 10 + y t 11 + 1) * (y t 8 + y t 9 + 1) ≤
          (railB5 beta + 1) * (railB4 beta + 1) :=
        mul_le_mul hfac5 hfac4 hnon4 (by linarith)
      refine pair_drift_nonpos
        (u := y t 6) (v := y t 7) (D := railD beta)
        (P := (railB5 beta + 1) * (railB4 beta + 1)) (C := 1) (K := 136)
        (drift := origField (y t) 6 + origField (y t) 7)
        (hnn t ht 6) (hnn t ht 7) hD
          (mul_nonneg (by linarith) (by linarith)) (by norm_num)
        (by norm_num) (hdiff t ht 3) ?_ ?_
      · simp [railB3, railSum] at hwall ⊢
        linarith
      · calc
          origField (y t) 6 + origField (y t) 7 =
              (y t 10 + y t 11 + 1) * (y t 8 + y t 9 + 1) +
                (y t 6 + y t 7) - 136 * y t 6 * y t 7 := by
                  simp [origField]; ring
          _ ≤ (railB5 beta + 1) * (railB4 beta + 1) +
                (y t 6 + y t 7) - 136 * y t 6 * y t 7 := by linarith
          _ = (railB5 beta + 1) * (railB4 beta + 1) +
                1 * (y t 6 + y t 7) - 136 * y t 6 * y t 7 := by ring
  have hs1 : ∀ t ∈ Set.Ico (0 : ℝ) T,
      railSum (y t) 1 ≤ railB1 beta := by
    apply upper_barrier_on_Ico hT
      (fun t ↦ railSum (y t) 1)
      (fun t ↦ origField (y t) 2 + origField (y t) 3)
    · simp [hy0, railSum, railB1, railB4, railB6, railB7, railD]
      positivity
    · intro t ht
      exact railSum_hasDerivAt (hy t ht) 1
    · intro t ht hwall
      have h4 := hs4 t ht
      have h6 := hs6 t ht
      have h7 := hs7 t ht
      have hfac4 : y t 8 + y t 9 + 1 ≤ railB4 beta + 1 := by
        simp [railSum] at h4
        linarith
      have hfac6 : y t 12 + y t 13 + 1 ≤ railB6 beta + 1 := by
        simp [railSum] at h6
        linarith
      have hfac7 : y t 14 + y t 15 ≤ railB7 beta := by
        simpa [railSum] using h7
      have hnon4 : 0 ≤ y t 8 + y t 9 + 1 := by
        linarith [hnn t ht 8, hnn t ht 9]
      have hnon6 : 0 ≤ y t 12 + y t 13 + 1 := by
        linarith [hnn t ht 12, hnn t ht 13]
      have hnon7 : 0 ≤ y t 14 + y t 15 := add_nonneg (hnn t ht 14) (hnn t ht 15)
      have hmul46 : (y t 12 + y t 13 + 1) * (y t 8 + y t 9 + 1) ≤
          (railB6 beta + 1) * (railB4 beta + 1) :=
        mul_le_mul hfac6 hfac4 hnon4 (by linarith)
      have hmul : (y t 12 + y t 13 + 1) * (y t 8 + y t 9 + 1) *
          (y t 14 + y t 15) ≤
          (railB6 beta + 1) * (railB4 beta + 1) * railB7 beta :=
        mul_le_mul hmul46 hfac7 hnon7
          (mul_nonneg (by linarith) (by linarith))
      refine pair_drift_nonpos
        (u := y t 2) (v := y t 3) (D := railD beta)
        (P := (railB6 beta + 1) * railB7 beta * (railB4 beta + 1))
        (C := 0) (K := 136)
        (drift := origField (y t) 2 + origField (y t) 3)
        (hnn t ht 2) (hnn t ht 3) hD
          (mul_nonneg (mul_nonneg (by linarith) hB7) (by linarith))
          (by norm_num)
        (by norm_num) (hdiff t ht 1) ?_ ?_
      · simp [railB1, railSum] at hwall ⊢
        linarith
      · calc
          origField (y t) 2 + origField (y t) 3 =
              (y t 12 + y t 13 + 1) * (y t 8 + y t 9 + 1) *
                (y t 14 + y t 15) - 136 * y t 2 * y t 3 := by
                  simp [origField]; ring
          _ ≤ (railB6 beta + 1) * railB7 beta * (railB4 beta + 1) -
                136 * y t 2 * y t 3 := by nlinarith
          _ = (railB6 beta + 1) * railB7 beta * (railB4 beta + 1) +
                0 * (y t 2 + y t 3) - 136 * y t 2 * y t 3 := by ring
  have hs2 : ∀ t ∈ Set.Ico (0 : ℝ) T,
      railSum (y t) 2 ≤ railB2 beta := by
    apply upper_barrier_on_Ico hT
      (fun t ↦ railSum (y t) 2)
      (fun t ↦ origField (y t) 4 + origField (y t) 5)
    · simpa [hy0, railSum] using hB2
    · intro t ht
      exact railSum_hasDerivAt (hy t ht) 2
    · intro t ht hwall
      have h3 := hs3 t ht
      have h4 := hs4 t ht
      refine pair_drift_nonpos
        (u := y t 4) (v := y t 5) (D := railD beta)
        (P := railB3 beta + railB4 beta + 1) (C := 1) (K := 136)
        (drift := origField (y t) 4 + origField (y t) 5)
        (hnn t ht 4) (hnn t ht 5) hD (by linarith) (by norm_num)
        (by norm_num) (hdiff t ht 2) ?_ ?_
      · simp [railB2, railSum] at hwall ⊢
        linarith
      · simp [origField, railSum] at h3 h4 ⊢
        linarith
  have hs0 : ∀ t ∈ Set.Ico (0 : ℝ) T,
      railSum (y t) 0 ≤ railB0 beta := by
    apply upper_barrier_on_Ico hT
      (fun t ↦ railSum (y t) 0)
      (fun t ↦ origField (y t) 0 + origField (y t) 1)
    · simpa [hy0, railSum] using hB0
    · intro t ht
      exact railSum_hasDerivAt (hy t ht) 0
    · intro t ht hwall
      have h2 := hs2 t ht
      refine pair_drift_nonpos
        (u := y t 0) (v := y t 1) (D := railD beta)
        (P := railB2 beta) (C := 0) (K := 136)
        (drift := origField (y t) 0 + origField (y t) 1)
        (hnn t ht 0) (hnn t ht 1) hD hB2 (by norm_num)
        (by norm_num) (hdiff t ht 0) ?_ ?_
      · simp [railB0, railSum] at hwall ⊢
        linarith
      · simp [origField, railSum] at h2 ⊢
        linarith
  have hs8 : ∀ t ∈ Set.Ico (0 : ℝ) T,
      railSum (y t) 8 ≤ railB8 beta := by
    apply upper_barrier_on_Ico hT
      (fun t ↦ railSum (y t) 8)
      (fun t ↦ origField (y t) 16 + origField (y t) 17)
    · simp [hy0, railSum, railB8, railD]
      linarith
    · intro t ht
      exact railSum_hasDerivAt (hy t ht) 8
    · intro t ht hwall
      have he := congrFun (htrack t ht) 8
      have heq : y t 19 = x t 8 := by simpa [dualRailDecode] using he
      have he_le : y t 19 ≤ beta := by
        rw [heq]
        exact (le_abs_self _).trans (hbound t ht.1 8)
      have hfac : y t 19 + 1 ≤ beta + 1 := by linarith
      have hnon : 0 ≤ y t 16 + y t 17 + 1 := by
        linarith [hnn t ht 16, hnn t ht 17]
      have hmul := mul_le_mul_of_nonneg_right hfac hnon
      refine pair_drift_nonpos
        (u := y t 16) (v := y t 17) (D := railD beta)
        (P := beta + 1) (C := beta + 1) (K := 136)
        (drift := origField (y t) 16 + origField (y t) 17)
        (hnn t ht 16) (hnn t ht 17) hD (by linarith) (by linarith)
        (by norm_num) (hdiff t ht 8) ?_ ?_
      · simp [railB8, railSum] at hwall ⊢
        linarith
      · calc
          origField (y t) 16 + origField (y t) 17 =
              (y t 19 + 1) * (y t 16 + y t 17 + 1) -
                136 * y t 16 * y t 17 := by simp [origField]; ring
          _ ≤ (beta + 1) * (y t 16 + y t 17 + 1) -
                136 * y t 16 * y t 17 := sub_le_sub_right hmul _
          _ = (beta + 1) + (beta + 1) * (y t 16 + y t 17) -
                136 * y t 16 * y t 17 := by ring
  intro j
  fin_cases j
  · simpa [railBound] using hs0
  · simpa [railBound] using hs1
  · simpa [railBound] using hs2
  · simpa [railBound] using hs3
  · simpa [railBound] using hs4
  · simpa [railBound] using hs5
  · simpa [railBound] using hs6
  · simpa [railBound] using hs7
  · simpa [railBound] using hs8

private theorem selective_local_coordinate_bound
    {x : ℝ → Fin 14 → ℝ} {y : ℝ → Fin 23 → ℝ}
    {beta T : ℝ} (hbeta : 0 < beta) (hT : 0 < T)
    (hinit : x 0 = gammaInit14)
    (hx : ∀ t : ℝ, 0 ≤ t → HasDerivAt x (gammaField (x t)) t)
    (hbound : ∀ t : ℝ, 0 ≤ t → ∀ i, |x t i| ≤ beta)
    (hy0 : y 0 = 0)
    (hy : ∀ t ∈ Set.Ico (0 : ℝ) T,
      HasDerivAt y (origField (y t)) t) :
    ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ i,
      0 ≤ y t i ∧ y t i ≤ selectiveBound beta := by
  obtain ⟨htrack, hnn, _hs4, _hs5⟩ :=
    selective_base_bounds hbeta hT hinit hx hbound hy0 hy
  have hrails := selective_rail_bounds hbeta hT hinit hx hbound hy0 hy
  have hrnn := railBound_nonneg hbeta
  have hsum_nn : 0 ≤ ∑ j : Fin 9, railBound beta j :=
    Finset.sum_nonneg (fun j _ ↦ hrnn j)
  intro t ht i
  refine ⟨hnn t ht i, ?_⟩
  have hrailCoord : ∀ j : Fin 9,
      y t ⟨2 * j.val, by have := j.isLt; omega⟩ ≤ selectiveBound beta ∧
      y t ⟨2 * j.val + 1, by have := j.isLt; omega⟩ ≤ selectiveBound beta := by
    intro j
    have hs := hrails j t ht
    have hjSum : railBound beta j ≤ ∑ k : Fin 9, railBound beta k :=
      Finset.single_le_sum (f := railBound beta)
        (fun k _ ↦ hrnn k) (Finset.mem_univ j)
    have hjM : railBound beta j ≤ selectiveBound beta := by
      simp only [selectiveBound]
      linarith
    simp only [railSum] at hs
    constructor
    · linarith [hnn t ht ⟨2 * j.val + 1, by have := j.isLt; omega⟩]
    · linarith [hnn t ht ⟨2 * j.val, by have := j.isLt; omega⟩]
  fin_cases i
  · exact (hrailCoord 0).1
  · exact (hrailCoord 0).2
  · exact (hrailCoord 1).1
  · exact (hrailCoord 1).2
  · exact (hrailCoord 2).1
  · exact (hrailCoord 2).2
  · exact (hrailCoord 3).1
  · exact (hrailCoord 3).2
  · exact (hrailCoord 4).1
  · exact (hrailCoord 4).2
  · exact (hrailCoord 5).1
  · exact (hrailCoord 5).2
  · exact (hrailCoord 6).1
  · exact (hrailCoord 6).2
  · exact (hrailCoord 7).1
  · exact (hrailCoord 7).2
  · exact (hrailCoord 8).1
  · exact (hrailCoord 8).2
  · change y t 18 ≤ selectiveBound beta
    have he := congrFun (htrack t ht) 13
    have heq : y t 18 = x t 13 := by simpa [dualRailDecode] using he
    rw [heq]
    have hxle : x t 13 ≤ beta := (le_abs_self _).trans (hbound t ht.1 13)
    simp only [selectiveBound]
    linarith
  · change y t 19 ≤ selectiveBound beta
    have he := congrFun (htrack t ht) 8
    have heq : y t 19 = x t 8 := by simpa [dualRailDecode] using he
    rw [heq]
    have hxle : x t 8 ≤ beta := (le_abs_self _).trans (hbound t ht.1 8)
    simp only [selectiveBound]
    linarith
  · change y t 20 ≤ selectiveBound beta
    have he := congrFun (htrack t ht) 10
    have heq : y t 20 = x t 10 := by simpa [dualRailDecode] using he
    rw [heq]
    have hxle : x t 10 ≤ beta := (le_abs_self _).trans (hbound t ht.1 10)
    simp only [selectiveBound]
    linarith
  · change y t 21 ≤ selectiveBound beta
    have he := congrFun (htrack t ht) 11
    have heq : y t 21 = x t 11 := by simpa [dualRailDecode] using he
    rw [heq]
    have hxle : x t 11 ≤ beta := (le_abs_self _).trans (hbound t ht.1 11)
    simp only [selectiveBound]
    linarith
  · change y t 22 ≤ selectiveBound beta
    have he := congrFun (htrack t ht) 12
    have heq : y t 22 = x t 12 := by simpa [dualRailDecode] using he
    rw [heq]
    have hxle : x t 12 ≤ beta := (le_abs_self _).trans (hbound t ht.1 12)
    simp only [selectiveBound]
    linarith

private theorem selective_local_norm_bound
    {x : ℝ → Fin 14 → ℝ} {y : ℝ → Fin 23 → ℝ}
    {beta T : ℝ} (hbeta : 0 < beta) (hT : 0 < T)
    (hinit : x 0 = gammaInit14)
    (hx : ∀ t : ℝ, 0 ≤ t → HasDerivAt x (gammaField (x t)) t)
    (hbound : ∀ t : ℝ, 0 ≤ t → ∀ i, |x t i| ≤ beta)
    (hy0 : y 0 = 0)
    (hy : ∀ t ∈ Set.Ico (0 : ℝ) T,
      HasDerivAt y (origField (y t)) t) :
    ∀ t ∈ Set.Ico (0 : ℝ) T, ‖y t‖ ≤ selectiveBound beta := by
  have hcoord := selective_local_coordinate_bound
    hbeta hT hinit hx hbound hy0 hy
  have hM : 0 ≤ selectiveBound beta := by
    simp only [selectiveBound]
    have hs : 0 ≤ ∑ j : Fin 9, railBound beta j :=
      Finset.sum_nonneg (fun j _ ↦ railBound_nonneg hbeta j)
    linarith
  intro t ht
  rw [pi_norm_le_iff_of_nonneg hM]
  intro i
  rw [Real.norm_eq_abs, abs_of_nonneg (hcoord t ht i).1]
  exact (hcoord t ht i).2

/-- The compact 14→23 selective front end is semantically complete: its
trajectory exists globally, solves the CRN ODE, decodes to the original gamma
trajectory, and is non-negative and bounded. -/
theorem qbeeGamma_tightSelectiveSemanticLift : TightSelectiveSemanticLift := by
  intro x beta hinit hbeta hx hbound
  have hlip := contDiff_locally_lipschitz origField_contDiff
  have hsum : 0 ≤ ∑ j : Fin 9, railBound beta j :=
    Finset.sum_nonneg (fun j _ ↦ railBound_nonneg hbeta j)
  have hM : 0 < selectiveBound beta := by
    simp only [selectiveBound]
    linarith
  have hinvariant : ∀ (T : ℝ), 0 < T → ∀ (y : ℝ → Fin 23 → ℝ),
      y 0 = 0 →
      (∀ t ∈ Set.Ico (0 : ℝ) T, HasDerivAt y (origField (y t)) t) →
      ∀ t ∈ Set.Ico (0 : ℝ) T, ‖y t‖ ≤ selectiveBound beta := by
    intro T hT y hy0 hy
    exact selective_local_norm_bound hbeta hT hinit hx hbound hy0 hy
  obtain ⟨y, hy0, hy, _hycont⟩ :=
    locally_lipschitz_bounded_global_ode_proved_continuous
      origField (0 : Fin 23 → ℝ) hlip (selectiveBound beta) hM hinvariant
  refine ⟨y, selectiveBound beta, hM, hy0, hy, ?_, ?_⟩
  · intro t ht
    have hT : 0 < t + 1 := by linarith
    have hy' : ∀ s ∈ Set.Ico (0 : ℝ) (t + 1),
        HasDerivAt y (origField (y s)) s := by
      intro s hs
      exact hy s hs.1
    exact selective_decode_eq_on_Ico hT hinit hx hy0 hy' t ⟨ht, by linarith⟩
  · intro t ht i
    have hT : 0 < t + 1 := by linarith
    have hy' : ∀ s ∈ Set.Ico (0 : ℝ) (t + 1),
        HasDerivAt y (origField (y s)) s := by
      intro s hs
      exact hy s hs.1
    exact selective_local_coordinate_bound hbeta hT hinit hx hbound hy0 hy'
      t ⟨ht, by linarith⟩ i

/-- The tight selective lift, QBee certificate, and dummy-constant solution
lemmas compose without any further gamma-specific ODE algebra. -/
theorem qbeeGamma_frontend_to_dummy34
    (x : ℝ → Fin 14 → ℝ) (beta : ℝ)
    (hinit : x 0 = gammaInit14) (hbeta : 0 < beta)
    (hx : ∀ t : ℝ, 0 ≤ t → HasDerivAt x (gammaField (x t)) t)
    (hbound : ∀ t : ℝ, 0 ≤ t → ∀ i, |x t i| ≤ beta) :
    ∃ (y : ℝ → Fin 23 → ℝ) (B : ℝ),
      0 < B ∧
      y 0 = 0 ∧
      (∀ t : ℝ, 0 ≤ t → HasDerivAt y (origField (y t)) t) ∧
      (∀ t : ℝ, 0 ≤ t → dualRailDecode (y t) = x t) ∧
      (∀ t : ℝ, 0 ≤ t → ∀ i, 0 ≤ y t i ∧ y t i ≤ B) ∧
      (∀ t : ℝ, 0 ≤ t →
        HasDerivAt
          (fun s ↦ homoEmbed (embed (y s)))
          (homoField (homoEmbed (embed (y t)))) t) := by
  obtain ⟨y, B, hB, hy0, hy, htrack, hyBound⟩ :=
    qbeeGamma_tightSelectiveSemanticLift x beta hinit hbeta hx hbound
  refine ⟨y, B, hB, hy0, hy, htrack, hyBound, ?_⟩
  exact homoField_solution_lift (crnQBee_solution_lift hy)

/-- The journal's tight selective dual-rail field is already CRN-safe,
before QBee is applied. -/
noncomputable def qbeeGamma_dualRail23_crn : IsCRNImplementable 23 origField :=
  origField_crn

/-- QBee's ten auxiliaries preserve the selective field on their monomial
manifold, after the guarded equal-on-manifold CRN repair. -/
noncomputable def qbeeGamma_qbee33_crn : IsCRNImplementable 33 crnQuadField :=
  crnQuadField_crn

/-- The explicit dummy-constant coordinate homogenizes constant and linear
terms without changing the first 33 solution coordinates. -/
noncomputable def qbeeGamma_dummy34_crn : IsCRNImplementable 34 homoField :=
  homoField_crn

/-- Existing `balancingDilation_crn` supplies the conservative 35-coordinate
field. -/
noncomputable def qbeeGamma_balanced35_crn : IsCRNImplementable 35 balancedField :=
  balancedField_crn

/-- The rational cubic transfer presentation is extensionally the existing
generic balancing-dilation field. -/
theorem qbeeGamma_balancedTransfers_field :
    balancedTransfers.toField = balancedField :=
  balancedTransfers_toField

/-- The optimized journal certificate has 35 cubic coordinates and hence
630 upper-triangular half-product coordinates. -/
theorem qbeeGamma_squared_dimension : upperPairDim 35 = 630 :=
  symmetricSquare_dimension

/-- The 35-coordinate balanced field is carried to the concrete quadratic
reaction field by the symmetric half-product map. -/
theorem qbeeGamma_squared_solution_lift
    {x : ℝ → Fin 35 → ℝ} {t : ℝ}
    (hx : HasDerivAt x (balancedField (x t)) t) :
    HasDerivAt
      (fun s ↦ halfProduct (x s))
      (squaredReactions.toField (halfProduct (x t))) t :=
  squared_solution_lift hx

/-! ## The non-vacuous 35-coordinate mean-field trajectory -/

/-- The dummy-homogenized initial point before lambda scaling. -/
noncomputable def qbeeGamma_homoInit34 : Fin 34 → ℝ :=
  homoEmbed (embed (fun _ : Fin 23 => 0))

theorem qbeeGamma_homoInit34_apply (i : Fin 34) :
    qbeeGamma_homoInit34 i = if i = 33 then 1 else 0 := by
  fin_cases i <;> simp [qbeeGamma_homoInit34, homoEmbed, embed]

theorem qbeeGamma_homoInit34_nonneg (i : Fin 34) :
    0 ≤ qbeeGamma_homoInit34 i := by
  fin_cases i <;> simp [qbeeGamma_homoInit34, homoEmbed, embed]

theorem qbeeGamma_homoInit34_sum :
    ∑ i, qbeeGamma_homoInit34 i = 1 := by
  rw [Fin.sum_univ_castSucc]
  norm_num [qbeeGamma_homoInit34, homoEmbed, embed, Fin.sum_univ_succ]

/-- The actual Stage-2 simplex initial condition. Its reservoir mass is
`241/242`, and the dummy constant carries mass `1/242`. -/
noncomputable def qbeeGamma_balancedInit35 : Fin 35 → ℝ :=
  stage2_init (1 / 242) qbeeGamma_homoInit34

theorem qbeeGamma_balancedInit35_nonneg (i : Fin 35) :
    0 ≤ qbeeGamma_balancedInit35 i := by
  apply stage2_init_nonneg (c := (1 / 242 : ℝ)) (by norm_num)
    qbeeGamma_homoInit34_nonneg
  rw [qbeeGamma_homoInit34_sum]
  norm_num

theorem qbeeGamma_balancedInit35_sum :
    ∑ i, qbeeGamma_balancedInit35 i = 1 :=
  stage2_init_simplex (1 / 242) qbeeGamma_homoInit34

/-- The tight front end starts the dummy-homogenized trajectory at the exact
initial point subsequently used by balancing dilation. -/
theorem qbeeGamma_frontend_to_stage2_initial
    (x : ℝ → Fin 14 → ℝ) (beta : ℝ)
    (hinit : x 0 = gammaInit14) (hbeta : 0 < beta)
    (hx : ∀ t : ℝ, 0 ≤ t → HasDerivAt x (gammaField (x t)) t)
    (hbound : ∀ t : ℝ, 0 ≤ t → ∀ i, |x t i| ≤ beta) :
    ∃ (y : ℝ → Fin 23 → ℝ) (B : ℝ),
      0 < B ∧ y 0 = 0 ∧
      (∀ t : ℝ, 0 ≤ t → HasDerivAt y (origField (y t)) t) ∧
      (∀ t : ℝ, 0 ≤ t → dualRailDecode (y t) = x t) ∧
      (∀ t : ℝ, 0 ≤ t → ∀ i, 0 ≤ y t i ∧ y t i ≤ B) ∧
      (∀ t : ℝ, 0 ≤ t →
        HasDerivAt
          (fun s ↦ homoEmbed (embed (y s)))
          (homoField (homoEmbed (embed (y t)))) t) ∧
      stage2_init (1 / 242) ((fun s ↦ homoEmbed (embed (y s))) 0) =
        qbeeGamma_balancedInit35 := by
  obtain ⟨y, B, hB, hy0, hy, hdecode, hyBound, hhomo⟩ :=
    qbeeGamma_frontend_to_dummy34 x beta hinit hbeta hx hbound
  refine ⟨y, B, hB, hy0, hy, hdecode, hyBound, hhomo, ?_⟩
  change stage2_init (1 / 242) (homoEmbed (embed (y 0))) =
    qbeeGamma_balancedInit35
  rw [hy0]
  rfl

/-- The 34-coordinate endpoint of the front end, packaged as the PIVP fed to
the existing Stage-2 construction. -/
noncomputable def qbeeGamma_homoPIVP : PIVP 34 where
  field := homoField
  init := qbeeGamma_homoInit34
  output := 18

theorem qbeeGamma_balancedInit35_apply (i : Fin 35) :
    qbeeGamma_balancedInit35 i =
      if i = 0 then 241 / 242 else if i = 34 then 1 / 242 else 0 := by
  refine i.cases ?_ (fun j ↦ ?_)
  · simp [qbeeGamma_balancedInit35, stage2_init, qbeeGamma_homoInit34_sum]
    norm_num
  · simp only [qbeeGamma_balancedInit35, stage2_init, Fin.cons_succ,
      qbeeGamma_homoInit34_apply]
    by_cases hj : j = 33
    · subst j
      norm_num
      rfl
    · have hsucc_ne : j.succ ≠ (34 : Fin 35) := by
        intro h
        apply hj
        apply Fin.ext
        simpa using congrArg Fin.val h
      simp [hj, hsucc_ne]

noncomputable def qbeeGamma_balanced35_tpp :
    IsTPPImplementable 35 balancedField :=
  stage2_field_tpp (o := (18 : Fin 34))
    (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) < 1 / 242)
    homoField_crn

theorem qbeeGamma_balancedField_conservative :
    IsConservative balancedField :=
  qbeeGamma_balanced35_tpp.conservative

theorem qbeeGamma_balancedField_locally_lipschitz :
    ∀ R : ℝ, 0 < R → ∃ L : ℝ, ∀ x y : Fin 35 → ℝ,
      ‖x‖ ≤ R → ‖y‖ ≤ R →
      ‖balancedField x - balancedField y‖ ≤ L * ‖x - y‖ :=
  cubicForm_locally_lipschitz balancedCubicForm

private theorem qbeeGamma_balanced_invariant_bound :
    ∀ (T : ℝ), 0 < T → ∀ (y : ℝ → Fin 35 → ℝ),
      y 0 = qbeeGamma_balancedInit35 →
      (∀ t ∈ Set.Ico (0 : ℝ) T,
        HasDerivAt y (balancedField (y t)) t) →
      ∀ t ∈ Set.Ico (0 : ℝ) T, ‖y t‖ ≤ 1 := by
  intro T hT y hy0 hode t ht
  have hinit_nonneg : ∀ i, 0 ≤ y 0 i := fun i => by
    rw [hy0]
    exact qbeeGamma_balancedInit35_nonneg i
  have h_nonneg : ∀ i, 0 ≤ y t i := fun i =>
    crn_local_nonneg balancedField_crn qbeeGamma_balancedField_locally_lipschitz
      T hT y hinit_nonneg hode t ht i
  have hsum_const : ∑ i, y t i = ∑ i, y 0 i :=
    conservative_local_sum_const qbeeGamma_balancedField_conservative
      T hT y hode t ht
  have hsum : ∑ i, y t i = 1 := by
    rw [hsum_const, hy0]
    exact qbeeGamma_balancedInit35_sum
  exact simplex_norm_le_one (y t) h_nonneg hsum

private theorem qbeeGamma_balanced_exists_continuous_solution :
    ∃ y : ℝ → Fin 35 → ℝ,
      y 0 = qbeeGamma_balancedInit35 ∧
      (∀ t : ℝ, 0 ≤ t → HasDerivAt y (balancedField (y t)) t) ∧
      Continuous y :=
  locally_lipschitz_bounded_global_ode_proved_continuous
    balancedField qbeeGamma_balancedInit35
    qbeeGamma_balancedField_locally_lipschitz 1 one_pos
    qbeeGamma_balanced_invariant_bound

/-- The canonical global balanced trajectory used by the closed capstone. -/
noncomputable def qbeeGamma_balancedSol : ℝ → Fin 35 → ℝ :=
  qbeeGamma_balanced_exists_continuous_solution.choose

theorem qbeeGamma_balancedSol_init :
    qbeeGamma_balancedSol 0 = qbeeGamma_balancedInit35 :=
  qbeeGamma_balanced_exists_continuous_solution.choose_spec.1

theorem qbeeGamma_balancedSol_hasDerivAt (t : ℝ) (ht : 0 ≤ t) :
    HasDerivAt qbeeGamma_balancedSol
      (balancedField (qbeeGamma_balancedSol t)) t :=
  qbeeGamma_balanced_exists_continuous_solution.choose_spec.2.1 t ht

/-- The chosen non-frozen trajectory is literally a solution of the generic
Stage-2 PIVP instantiated by the front-end field and initial point. -/
noncomputable def qbeeGamma_balancedPIVPSolution :
    PIVP.Solution (stage2_pivp 1 (1 / 242) qbeeGamma_homoPIVP) where
  trajectory := qbeeGamma_balancedSol
  init_cond := by
    simpa [qbeeGamma_homoPIVP, qbeeGamma_balancedInit35] using
      qbeeGamma_balancedSol_init
  is_solution := by
    intro t ht
    simpa [qbeeGamma_homoPIVP, balancedField] using
      qbeeGamma_balancedSol_hasDerivAt t ht

theorem qbeeGamma_balancedSol_continuous : Continuous qbeeGamma_balancedSol :=
  qbeeGamma_balanced_exists_continuous_solution.choose_spec.2.2

theorem qbeeGamma_balancedSol_nonneg (t : ℝ) (ht : 0 ≤ t) (i : Fin 35) :
    0 ≤ qbeeGamma_balancedSol t i := by
  have hT : 0 < t + 1 := by linarith
  exact crn_local_nonneg balancedField_crn qbeeGamma_balancedField_locally_lipschitz
    (t + 1) hT qbeeGamma_balancedSol
    (fun j => by rw [qbeeGamma_balancedSol_init]; exact qbeeGamma_balancedInit35_nonneg j)
    (fun s hs => qbeeGamma_balancedSol_hasDerivAt s hs.1)
    t ⟨ht, by linarith⟩ i

theorem qbeeGamma_balancedSol_sum (t : ℝ) (ht : 0 ≤ t) :
    ∑ i, qbeeGamma_balancedSol t i = 1 := by
  have hT : 0 < t + 1 := by linarith
  have hconst := conservative_local_sum_const qbeeGamma_balancedField_conservative
    (t + 1) hT qbeeGamma_balancedSol
    (fun s hs => qbeeGamma_balancedSol_hasDerivAt s hs.1)
    t ⟨ht, by linarith⟩
  rw [qbeeGamma_balancedSol_init, qbeeGamma_balancedInit35_sum] at hconst
  exact hconst

theorem qbeeGamma_balancedSol_norm_le_one (t : ℝ) (ht : 0 ≤ t) :
    ‖qbeeGamma_balancedSol t‖ ≤ 1 :=
  simplex_norm_le_one _ (qbeeGamma_balancedSol_nonneg t ht)
    (qbeeGamma_balancedSol_sum t ht)

/-- Generic normalization turns any balanced trajectory into the exact
mean-field solution consumed by the concrete Kurtz specialization. -/
noncomputable def qbeeGamma_squaredMeanFieldSolution
    (x : ℝ → Fin 35 → ℝ)
    (hx : ∀ t : ℝ, 0 ≤ t → HasDerivAt x (balancedField (x t)) t) :
    Kurtz.MeanFieldSolution (upperPairDim 35) squaredRateSpec :=
  squaredMeanFieldSolution x hx

/-- The concrete 630-coordinate mean-field solution, built from the genuine
non-frozen Stage-2 simplex trajectory and the generic squaring lift. -/
noncomputable def qbeeGamma_meanField :
    Kurtz.MeanFieldSolution (upperPairDim 35) squaredRateSpec :=
  qbeeGamma_squaredMeanFieldSolution qbeeGamma_balancedSol
    qbeeGamma_balancedSol_hasDerivAt

/-- Before the normalization time change internal to `MeanFieldSolution`, the
concrete 630-coordinate trajectory is exactly the generic squaring lift of the
Stage-2 solution. -/
theorem qbeeGamma_balancedSol_squared_hasDerivAt (t : ℝ) (ht : 0 ≤ t) :
    HasDerivAt
      (fun s ↦ halfProduct (qbeeGamma_balancedPIVPSolution.trajectory s))
      (squaredReactions.toField
        (halfProduct (qbeeGamma_balancedPIVPSolution.trajectory t))) t := by
  exact qbeeGamma_squared_solution_lift
    (qbeeGamma_balancedSol_hasDerivAt t ht)

theorem qbeeGamma_meanField_norm_le_one (t : ℝ) (ht : 0 ≤ t) :
    ‖qbeeGamma_meanField.sol t‖ ≤ 1 := by
  change ‖halfProduct (qbeeGamma_balancedSol
    ((balancedTransfers.symmetricLift.toQuadField.normalization : ℝ) * t))‖ ≤ 1
  have hnorm_pos : 0 <
      (balancedTransfers.symmetricLift.toQuadField.normalization : ℝ) := by
    exact_mod_cast balancedTransfers.symmetricLift.toQuadField.normalization_pos
  exact halfProduct_norm_le_one_of_simplex _
    (qbeeGamma_balancedSol_nonneg _ (mul_nonneg hnorm_pos.le ht))
    (qbeeGamma_balancedSol_sum _ (mul_nonneg hnorm_pos.le ht))

theorem qbeeGamma_meanField_continuous : Continuous qbeeGamma_meanField.sol := by
  change Continuous (fun t => halfProduct (qbeeGamma_balancedSol
    ((balancedTransfers.symmetricLift.toQuadField.normalization : ℝ) * t)))
  have htime : Continuous (fun t : ℝ =>
      (balancedTransfers.symmetricLift.toQuadField.normalization : ℝ) * t) :=
    continuous_const.mul continuous_id
  have hsol : Continuous (fun t : ℝ => qbeeGamma_balancedSol
      ((balancedTransfers.symmetricLift.toQuadField.normalization : ℝ) * t)) :=
    qbeeGamma_balancedSol_continuous.comp htime
  apply continuous_pi
  intro k
  simp only [halfProduct]
  exact (continuous_const.mul (continuous_apply _ |>.comp hsol)).mul
    (continuous_apply _ |>.comp hsol)

theorem qbeeGamma_meanField_measurable : Measurable qbeeGamma_meanField.sol :=
  qbeeGamma_meanField_continuous.measurable

theorem qbeeGamma_meanField_drift_intervalIntegrable
    (i : Fin (upperPairDim 35)) {t : ℝ} (ht : 0 ≤ t) :
    IntervalIntegrable
      (fun s : ℝ => (squaredRateSpec.drift (qbeeGamma_meanField.sol s)) i)
      MeasureTheory.volume (0 : ℝ) t := by
  exact squaredRateSpec.drift_intervalIntegrable_of_continuous
    qbeeGamma_meanField.sol qbeeGamma_meanField_continuous i ht

/-! ## Canonical population initial condition -/

/-- The three nonzero half-product masses at time zero. -/
noncomputable def qbeeGamma_massAA : ℝ := 58081 / 58564
noncomputable def qbeeGamma_massAB : ℝ := 482 / 58564
noncomputable def qbeeGamma_massBB : ℝ := 1 / 58564
noncomputable def qbeeGamma_massAAB : ℝ := 58563 / 58564

/-- Encoded half-product states carrying the initial population mass. -/
noncomputable def qbeeGamma_stateAA : Fin (upperPairDim 35) :=
  upperPairFin (0 : Fin 35) 0

noncomputable def qbeeGamma_stateAB : Fin (upperPairDim 35) :=
  upperPairFin (0 : Fin 35) 34

noncomputable def qbeeGamma_stateBB : Fin (upperPairDim 35) :=
  upperPairFin (34 : Fin 35) 34

theorem qbeeGamma_stateAA_ne_stateAB :
    qbeeGamma_stateAA ≠ qbeeGamma_stateAB := by
  simp only [qbeeGamma_stateAA, qbeeGamma_stateAB, ne_eq,
    upperPairFin_eq_iff]
  omega

theorem qbeeGamma_stateAA_ne_stateBB :
    qbeeGamma_stateAA ≠ qbeeGamma_stateBB := by
  simp only [qbeeGamma_stateAA, qbeeGamma_stateBB, ne_eq,
    upperPairFin_eq_iff]
  omega

theorem qbeeGamma_stateAB_ne_stateBB :
    qbeeGamma_stateAB ≠ qbeeGamma_stateBB := by
  simp only [qbeeGamma_stateAB, qbeeGamma_stateBB, ne_eq,
    upperPairFin_eq_iff]
  omega

theorem qbeeGamma_meanField_x₀ :
    qbeeGamma_meanField.x₀ = halfProduct qbeeGamma_balancedInit35 := by
  change halfProduct (qbeeGamma_balancedSol 0) = _
  rw [qbeeGamma_balancedSol_init]

/-- The concrete mean-field initial point is supported on exactly three
upper-pair states. -/
theorem qbeeGamma_meanField_x₀_apply (k : Fin (upperPairDim 35)) :
    qbeeGamma_meanField.x₀ k =
      if k = qbeeGamma_stateAA then qbeeGamma_massAA
      else if k = qbeeGamma_stateAB then qbeeGamma_massAB
      else if k = qbeeGamma_stateBB then qbeeGamma_massBB
      else 0 := by
  let p := (upperPairEquivFin 35).symm k
  let i : Fin 35 := p.1.1
  let j : Fin 35 := p.1.2
  have hij : i ≤ j := p.property
  have hk : upperPairFin i j = k := CubicTransfers.upperPairFin_decode k
  rw [← hk]
  rw [qbeeGamma_meanField_x₀]
  rw [halfProduct_upperPairFin]
  simp_rw [qbeeGamma_balancedInit35_apply]
  by_cases hi0 : i = 0
  · by_cases hj0 : j = 0
    · simp [qbeeGamma_stateAA, qbeeGamma_stateAB, qbeeGamma_stateBB,
        qbeeGamma_massAA, qbeeGamma_massAB, qbeeGamma_massBB,
        upperPairFin_eq_iff, pairScale, hi0, hj0]
      norm_num
    · by_cases hj34 : j = 34
      · simp [qbeeGamma_stateAA, qbeeGamma_stateAB, qbeeGamma_stateBB,
          qbeeGamma_massAA, qbeeGamma_massAB, qbeeGamma_massBB,
          upperPairFin_eq_iff, pairScale, hi0, hj0, hj34]
        norm_num
      · simp [qbeeGamma_stateAA, qbeeGamma_stateAB, qbeeGamma_stateBB,
          upperPairFin_eq_iff, pairScale, hi0, hj0, hj34]
  · by_cases hi34 : i = 34
    · have hj34 : j = 34 := by
        apply Fin.ext
        have hi_val : i.val = 34 := congrArg Fin.val hi34
        omega
      simp [qbeeGamma_stateAA, qbeeGamma_stateAB, qbeeGamma_stateBB,
        qbeeGamma_massAA, qbeeGamma_massAB, qbeeGamma_massBB,
        upperPairFin_eq_iff, pairScale, hi0, hi34, hj34]
      norm_num
    · simp [qbeeGamma_stateAA, qbeeGamma_stateAB, qbeeGamma_stateBB,
        upperPairFin_eq_iff, pairScale, hi0, hi34]

/-- Cumulative floor allocation of the three rational initial masses. -/
noncomputable def qbeeGamma_countAA (N : ℕ) : ℕ :=
  ⌊(N : ℝ) * qbeeGamma_massAA⌋₊

noncomputable def qbeeGamma_countAAB (N : ℕ) : ℕ :=
  ⌊(N : ℝ) * qbeeGamma_massAAB⌋₊

noncomputable def qbeeGamma_countAB (N : ℕ) : ℕ :=
  qbeeGamma_countAAB N - qbeeGamma_countAA N

noncomputable def qbeeGamma_countBB (N : ℕ) : ℕ :=
  N - qbeeGamma_countAAB N

theorem qbeeGamma_countAA_le_countAAB (N : ℕ) :
    qbeeGamma_countAA N ≤ qbeeGamma_countAAB N := by
  apply Nat.floor_mono
  unfold qbeeGamma_massAA qbeeGamma_massAAB
  gcongr
  norm_num

theorem qbeeGamma_countAAB_le (N : ℕ) : qbeeGamma_countAAB N ≤ N := by
  calc
    qbeeGamma_countAAB N
        ≤ ⌊(N : ℝ)⌋₊ := by
          apply Nat.floor_mono
          unfold qbeeGamma_massAAB
          have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
          nlinarith
    _ = N := Nat.floor_natCast N

noncomputable def qbeeGamma_initialCount
    (N : ℕ) (k : Fin (upperPairDim 35)) : ℕ :=
  if k = qbeeGamma_stateAA then qbeeGamma_countAA N
  else if k = qbeeGamma_stateAB then qbeeGamma_countAB N
  else if k = qbeeGamma_stateBB then qbeeGamma_countBB N
  else 0

theorem qbeeGamma_initialCount_le (N : ℕ) (k : Fin (upperPairDim 35)) :
    qbeeGamma_initialCount N k ≤ N := by
  have hAA := qbeeGamma_countAA_le_countAAB N
  have hAAB := qbeeGamma_countAAB_le N
  by_cases hkAA : k = qbeeGamma_stateAA
  · simp [qbeeGamma_initialCount, hkAA]
    omega
  · by_cases hkAB : k = qbeeGamma_stateAB
    · simp [qbeeGamma_initialCount, hkAA, hkAB, qbeeGamma_countAB,
        Ne.symm qbeeGamma_stateAA_ne_stateAB]
      omega
    · by_cases hkBB : k = qbeeGamma_stateBB
      · simp [qbeeGamma_initialCount, hkAA, hkAB, hkBB, qbeeGamma_countBB,
          Ne.symm qbeeGamma_stateAA_ne_stateBB,
          Ne.symm qbeeGamma_stateAB_ne_stateBB]
      · simp [qbeeGamma_initialCount, hkAA, hkAB, hkBB]

private theorem sum_three_ite {d : ℕ} (a b c : Fin d)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (A B C : ℕ) :
    ∑ k, (if k = a then A else if k = b then B else if k = c then C else 0) =
      A + B + C := by
  classical
  have hpoint (k : Fin d) :
      (if k = a then A else if k = b then B else if k = c then C else 0) =
        (if k = a then A else 0) + (if k = b then B else 0) +
          (if k = c then C else 0) := by
    by_cases hka : k = a
    · subst k
      simp [hab, hac]
    · by_cases hkb : k = b
      · subst k
        simp [hka, hab, hbc]
      · by_cases hkc : k = c
        · subst k
          simp [hka, hkb, hac, hbc]
        · simp [hka, hkb, hkc]
  calc
    ∑ k, (if k = a then A else if k = b then B else if k = c then C else 0)
        = ∑ k, ((if k = a then A else 0) + (if k = b then B else 0) +
            (if k = c then C else 0)) :=
          Finset.sum_congr rfl (fun k _ ↦ hpoint k)
    _ = A + B + C := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      simp

theorem qbeeGamma_initialCount_sum (N : ℕ) :
    ∑ k, qbeeGamma_initialCount N k = N := by
  classical
  have hAA := qbeeGamma_countAA_le_countAAB N
  have hAAB := qbeeGamma_countAAB_le N
  change (∑ k, (if k = qbeeGamma_stateAA then qbeeGamma_countAA N
    else if k = qbeeGamma_stateAB then qbeeGamma_countAB N
    else if k = qbeeGamma_stateBB then qbeeGamma_countBB N else 0)) = N
  rw [sum_three_ite qbeeGamma_stateAA qbeeGamma_stateAB qbeeGamma_stateBB
    qbeeGamma_stateAA_ne_stateAB qbeeGamma_stateAA_ne_stateBB
    qbeeGamma_stateAB_ne_stateBB]
  simp only [qbeeGamma_countAB, qbeeGamma_countBB]
  omega

/-- Canonical integer initial state for every population size. -/
noncomputable def qbeeGamma_initialState (N : ℕ) :
    Fin (upperPairDim 35) → Fin (N + 1) :=
  fun k ↦ ⟨qbeeGamma_initialCount N k,
    Nat.lt_succ_of_le (qbeeGamma_initialCount_le N k)⟩

theorem qbeeGamma_initialState_inSimplex (N : ℕ) (hN : 0 < N) :
    (CTMC.DensityDepCTMC.mk N hN squaredRateSpec).InSimplex
      (qbeeGamma_initialState N) := by
  change ∑ k, (qbeeGamma_initialState N k : ℕ) = N
  simpa [qbeeGamma_initialState] using qbeeGamma_initialCount_sum N

private theorem qbeeGamma_countAA_close (N : ℕ) (hN : 0 < N) :
    |(qbeeGamma_countAA N : ℝ) / N - qbeeGamma_massAA| ≤ 1 / N := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hmass : 0 ≤ (N : ℝ) * qbeeGamma_massAA := by
    unfold qbeeGamma_massAA
    positivity
  have hfloor :
      |(qbeeGamma_countAA N : ℝ) -
        (N : ℝ) * qbeeGamma_massAA| ≤ 1 := by
    exact Nat.abs_floor_sub_le hmass
  have heq :
      (qbeeGamma_countAA N : ℝ) / N - qbeeGamma_massAA =
        ((qbeeGamma_countAA N : ℝ) -
          (N : ℝ) * qbeeGamma_massAA) / N := by
    field_simp
  rw [heq, abs_div, abs_of_pos hNr]
  exact (div_le_div_iff_of_pos_right hNr).2 hfloor

private theorem qbeeGamma_countAB_close (N : ℕ) (hN : 0 < N) :
    |(qbeeGamma_countAB N : ℝ) / N - qbeeGamma_massAB| ≤ 1 / N := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hAA := qbeeGamma_countAA_le_countAAB N
  have hmassAA : 0 ≤ (N : ℝ) * qbeeGamma_massAA := by
    unfold qbeeGamma_massAA
    positivity
  have hmassAAB : 0 ≤ (N : ℝ) * qbeeGamma_massAAB := by
    unfold qbeeGamma_massAAB
    positivity
  have hAAlo : (qbeeGamma_countAA N : ℝ) ≤
      (N : ℝ) * qbeeGamma_massAA := Nat.floor_le hmassAA
  have hAAhi : (N : ℝ) * qbeeGamma_massAA ≤
      (qbeeGamma_countAA N : ℝ) + 1 :=
    (Nat.lt_floor_add_one _).le
  have hAABlo : (qbeeGamma_countAAB N : ℝ) ≤
      (N : ℝ) * qbeeGamma_massAAB := Nat.floor_le hmassAAB
  have hAABhi : (N : ℝ) * qbeeGamma_massAAB ≤
      (qbeeGamma_countAAB N : ℝ) + 1 :=
    (Nat.lt_floor_add_one _).le
  have herr :
      |((qbeeGamma_countAAB N : ℝ) -
          (N : ℝ) * qbeeGamma_massAAB) -
        ((qbeeGamma_countAA N : ℝ) -
          (N : ℝ) * qbeeGamma_massAA)| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  have hmass : qbeeGamma_massAB =
      qbeeGamma_massAAB - qbeeGamma_massAA := by
    norm_num [qbeeGamma_massAB, qbeeGamma_massAAB, qbeeGamma_massAA]
  have heq :
      (qbeeGamma_countAB N : ℝ) / N - qbeeGamma_massAB =
        (((qbeeGamma_countAAB N : ℝ) -
            (N : ℝ) * qbeeGamma_massAAB) -
          ((qbeeGamma_countAA N : ℝ) -
            (N : ℝ) * qbeeGamma_massAA)) / N := by
    rw [qbeeGamma_countAB, Nat.cast_sub hAA, hmass]
    field_simp
    ring
  rw [heq, abs_div, abs_of_pos hNr]
  exact (div_le_div_iff_of_pos_right hNr).2 herr

private theorem qbeeGamma_countBB_close (N : ℕ) (hN : 0 < N) :
    |(qbeeGamma_countBB N : ℝ) / N - qbeeGamma_massBB| ≤ 1 / N := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hAAB := qbeeGamma_countAAB_le N
  have hmassAAB : 0 ≤ (N : ℝ) * qbeeGamma_massAAB := by
    unfold qbeeGamma_massAAB
    positivity
  have hfloor :
      |(qbeeGamma_countAAB N : ℝ) -
        (N : ℝ) * qbeeGamma_massAAB| ≤ 1 := by
    exact Nat.abs_floor_sub_le hmassAAB
  have hmass : qbeeGamma_massBB = 1 - qbeeGamma_massAAB := by
    norm_num [qbeeGamma_massBB, qbeeGamma_massAAB]
  have heq :
      (qbeeGamma_countBB N : ℝ) / N - qbeeGamma_massBB =
        ((N : ℝ) * qbeeGamma_massAAB -
          (qbeeGamma_countAAB N : ℝ)) / N := by
    rw [qbeeGamma_countBB, Nat.cast_sub hAAB, hmass]
    field_simp
    ring
  rw [heq, abs_div, abs_of_pos hNr, abs_sub_comm]
  exact (div_le_div_iff_of_pos_right hNr).2 hfloor

theorem qbeeGamma_initialState_close (N : ℕ) (hN : 0 < N) :
    ‖(fun i ↦ ((qbeeGamma_initialState N i : ℕ) : ℝ) / N) -
      qbeeGamma_meanField.x₀‖ ≤ 1 / N := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  rw [pi_norm_le_iff_of_nonneg (one_div_nonneg.mpr hNr.le)]
  intro k
  rw [Real.norm_eq_abs, Pi.sub_apply, qbeeGamma_meanField_x₀_apply]
  by_cases hkAA : k = qbeeGamma_stateAA
  · subst k
    simpa [qbeeGamma_initialState, qbeeGamma_initialCount,
      qbeeGamma_stateAA_ne_stateAB, qbeeGamma_stateAA_ne_stateBB] using
      qbeeGamma_countAA_close N hN
  · by_cases hkAB : k = qbeeGamma_stateAB
    · subst k
      simpa [qbeeGamma_initialState, qbeeGamma_initialCount,
        Ne.symm qbeeGamma_stateAA_ne_stateAB,
        qbeeGamma_stateAB_ne_stateBB] using qbeeGamma_countAB_close N hN
    · by_cases hkBB : k = qbeeGamma_stateBB
      · subst k
        simpa [qbeeGamma_initialState, qbeeGamma_initialCount,
          Ne.symm qbeeGamma_stateAA_ne_stateBB,
          Ne.symm qbeeGamma_stateAB_ne_stateBB] using
          qbeeGamma_countBB_close N hN
      · simp [qbeeGamma_initialState, qbeeGamma_initialCount,
          hkAA, hkAB, hkBB, one_div_nonneg.mpr hNr.le]

/-- Structural hypotheses needed by the generic frozen Kurtz theorem. -/
theorem qbeeGamma_kurtzStructural (N : ℕ) (hN : 0 < N) :
    (CTMC.DensityDepCTMC.mk N hN squaredRateSpec).DriftZeroAtAbsorbingOnSimplex ∧
      (CTMC.DensityDepCTMC.mk N hN squaredRateSpec).ConservativeJumps := by
  simpa [squaredRateSpec, squaredSynPP, squaredReactions] using
    squaredRateSpec_kurtzStructural N hN

/-- The finite-clock Doob constant for the 630-state symmetric square. -/
noncomputable def qbeeGamma_doobConstant : ℝ :=
  CTMC.DensityDepCTMC.frozenMartingalePartDoobL2Constant (upperPairDim 35)

theorem qbeeGamma_doobConstant_pos : 0 < qbeeGamma_doobConstant := by
  exact CTMC.DensityDepCTMC.frozenMartingalePartDoobL2Constant_pos _

/-- Boundary compatibility makes the generator-centered finite-clock Doob
bridge an exact bound for the martingale residual used by Kurtz. -/
theorem qbeeGamma_frozenDoobL2 :
    Kurtz.FrozenDoobL2 squaredRateSpec qbeeGamma_doobConstant := by
  intro N hN x₀ hinit T hT
  letI : NeZero (upperPairDim 35) := ⟨by
    rw [symmetricSquare_dimension]
    norm_num⟩
  let M : CTMC.DensityDepCTMC (upperPairDim 35) :=
    CTMC.DensityDepCTMC.mk N hN squaredRateSpec
  have hcons : M.ConservativeJumps := by
    simpa [M] using (qbeeGamma_kurtzStructural N hN).2
  have hBC : M.BoundaryCompatibleOnSimplex := by
    simpa [M] using squaredRateSpec_boundaryCompatibleOnSimplex N hN
  have heq :=
    M.canonical_frozenMartingalePart_eq_frozenGeneratorMartingalePart_ae
      x₀ hcons hinit hBC
  have hgenerator := Ripple.CTMC.frozenGeneratorMP_bridge_ae M x₀ hinit hT
  have hbridge : ∀ᵐ records ∂M.canonicalRecordMeasure x₀,
      ∃ n, (⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
        ‖M.frozenMartingalePart M.canonicalPathMap s records‖ ^ 2) ≤
      (4 / 3 : ℝ) * M.frozenClockSkeletonSupSq T n records +
        4 * M.frozenTruncatedJumpSqSum T n records := by
    filter_upwards [heq, hgenerator] with records heq_records hgenerator_records
    obtain ⟨n, hn⟩ := hgenerator_records
    refine ⟨n, ?_⟩
    simpa only [heq_records] using hn
  exact M.frozenMartingalePart_DoobL2_of_bridge_exists_ae
    x₀ hinit hT hbridge
    (fun n => M.frozenClockTruncatedQVIntegralSum_le_frozenQV_setIntegral
      x₀ hinit T hT n)

/-- Uniform martingale QV-sup bound for the generated 630-state system. -/
theorem qbeeGamma_mart_sup_bound {T : ℝ} (hT : 0 < T) :
    ∃ C_qv : ℝ, 0 < C_qv ∧
    ∀ (N : ℕ) (hN : 0 < N)
      (x₀ : Fin (upperPairDim 35) → Fin (N + 1))
      (_hinit : (CTMC.DensityDepCTMC.mk N hN squaredRateSpec).InSimplex x₀),
      ∫ records, ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
        ‖(CTMC.DensityDepCTMC.mk N hN squaredRateSpec).frozenMartingalePart
          (CTMC.DensityDepCTMC.mk N hN squaredRateSpec).canonicalPathMap
            s records‖ ^ 2
      ∂(CTMC.DensityDepCTMC.mk N hN squaredRateSpec).canonicalRecordMeasure x₀
      ≤ C_qv * T / ↑N := by
  exact Kurtz.frozen_martingale_qv_bound_uniform_of_doob squaredRateSpec
    qbeeGamma_doobConstant_pos qbeeGamma_frozenDoobL2
    squaredRateSpec.exists_instantQVRate_bound_uniform hT

/-- The generic convergence conclusion specialized to any lattice initial
state within `1/N` of the concrete gamma-QBee mean-field initial point. -/
theorem kurtz_gamma_of_lattice_initial :
    ∀ ε : ℝ, 0 < ε → ∀ η : ℝ, 0 < η → ∀ T : ℝ, 0 < T →
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (hN : 0 < N)
    (x₀ : Fin (upperPairDim 35) → Fin (N + 1))
    (hinit : (CTMC.DensityDepCTMC.mk N hN squaredRateSpec).InSimplex x₀)
    (_hinit_close :
      ‖(fun i => (↑(x₀ i) : ℝ) / ↑N) - qbeeGamma_meanField.x₀‖ ≤ 1 / ↑N),
    (CTMC.DensityDepCTMC.mk N hN squaredRateSpec).canonicalRecordMeasure x₀
      {ω | ⨆ (t : ℝ) (_ : 0 ≤ t ∧ t ≤ T),
        ‖((CTMC.DensityDepCTMC.mk N hN squaredRateSpec).toFrozenDensityProcess x₀
            (qbeeGamma_kurtzStructural N hN).1
            (qbeeGamma_kurtzStructural N hN).2 hinit).process t ω -
          qbeeGamma_meanField.sol t‖ > ε} ≤ ENNReal.ofReal η := by
  intro ε hε η hη T hT
  obtain ⟨C_qv, hC_qv_pos, hqv⟩ := qbeeGamma_mart_sup_bound hT
  exact Kurtz.kurtz_finite_horizon_generic_v3 squaredRateSpec qbeeGamma_meanField
    (fun N hN => (qbeeGamma_kurtzStructural N hN).1)
    (fun N hN => (qbeeGamma_kurtzStructural N hN).2)
    qbeeGamma_meanField_norm_le_one qbeeGamma_meanField_measurable
    qbeeGamma_meanField_drift_intervalIntegrable hT hC_qv_pos
    (fun N hN x₀ hinit _hinit_close => hqv N hN x₀ hinit)
    ε hε η hη

/-- Fully closed finite-horizon convergence theorem for the generated
630-state gamma-QBee population protocol. The process starts from the
canonical cumulative-floor allocation above, so the simplex and `1/N`
initial-approximation obligations are discharged internally. -/
theorem kurtz_gamma :
    ∀ ε : ℝ, 0 < ε → ∀ η : ℝ, 0 < η → ∀ T : ℝ, 0 < T →
    ∃ N₀ : ℕ, ∀ (N : ℕ+), N₀ ≤ (N : ℕ) →
    (CTMC.DensityDepCTMC.mk (N : ℕ) N.2 squaredRateSpec).canonicalRecordMeasure
      (qbeeGamma_initialState (N : ℕ))
      {ω | ⨆ (t : ℝ) (_ : 0 ≤ t ∧ t ≤ T),
        ‖((CTMC.DensityDepCTMC.mk (N : ℕ) N.2 squaredRateSpec).toFrozenDensityProcess
            (qbeeGamma_initialState (N : ℕ))
            (qbeeGamma_kurtzStructural (N : ℕ) N.2).1
            (qbeeGamma_kurtzStructural (N : ℕ) N.2).2
            (qbeeGamma_initialState_inSimplex (N : ℕ) N.2)).process t ω -
          qbeeGamma_meanField.sol t‖ > ε} ≤ ENNReal.ofReal η := by
  intro ε hε η hη T hT
  obtain ⟨N₀, hmain⟩ :=
    kurtz_gamma_of_lattice_initial
      ε hε η hη T hT
  refine ⟨N₀, ?_⟩
  intro N hN_ge
  exact hmain (N : ℕ) hN_ge N.2 (qbeeGamma_initialState (N : ℕ))
    (qbeeGamma_initialState_inSimplex (N : ℕ) N.2)
    (qbeeGamma_initialState_close (N : ℕ) N.2)

#print axioms gammaQuadField_not_isCRNImplementable
#print axioms constantDilation_gammaQuadField_not_isCRNImplementable
#print axioms qbeeGamma_tightSelectiveSemanticLift
#print axioms qbeeGamma_frontend_to_dummy34
#print axioms qbeeGamma_frontend_to_stage2_initial
#print axioms dualRailTangent_origField
#print axioms qbeeGamma_dualRail23_crn
#print axioms crnQBee_solution_lift
#print axioms homoField_solution_lift
#print axioms qbeeGamma_balancedTransfers_field
#print axioms qbeeGamma_squared_solution_lift
#print axioms qbeeGamma_squaredMeanFieldSolution
#print axioms qbeeGamma_balancedPIVPSolution
#print axioms qbeeGamma_balancedSol_squared_hasDerivAt
#print axioms qbeeGamma_kurtzStructural
#print axioms qbeeGamma_frozenDoobL2
#print axioms qbeeGamma_mart_sup_bound
#print axioms qbeeGamma_initialState_close
#print axioms kurtz_gamma_of_lattice_initial
#print axioms kurtz_gamma

end Ripple.LPP.QBee
