-- Ripple/Kurtz/StrongApprox/DyadicTreePointTail.lean
import Ripple.Kurtz.StrongApprox.DyadicSpatialChainBridge
import Ripple.Kurtz.StrongApprox.DyadicChainEstimate
import Ripple.Kurtz.StrongApprox.DyadicFixedChainTails

noncomputable section

open MeasureTheory ProbabilityTheory Set Finset
open scoped BigOperators ENNReal NNReal Nat

namespace Ripple.Kurtz.StrongApprox.DyadicTreePointTail

open DyadicGaussianTree DyadicPoissonTree
open DyadicSpatialSkeleton DyadicSpatialChainBridge
open DyadicChainEstimate DyadicFixedChainTails

/-! ## Raw coordinates selected by one boundary path -/

private def noiseCast {m n : ℕ} (h : m = n)
    (i : DyadicNoise m) : DyadicNoise n :=
  cast (congrArg DyadicNoise h) i

private theorem cast_noiseSpace_apply {m n : ℕ} (h : m = n)
    (x : DyadicNoiseSpace n) (i : DyadicNoise m) :
    (cast (congrArg DyadicNoiseSpace h.symm) x) i =
      x (noiseCast h i) := by
  subst n
  rfl

private theorem rootSource_apply (K : ℕ) (x : DyadicNoiseSpace K)
    (i : DyadicNoise (0 + K)) :
    rootSource K x i = x (noiseCast (Nat.zero_add K) i) := by
  simpa [rootSource, noiseCast] using
    cast_noiseSpace_apply (h := Nat.zero_add K) x i

private theorem reassociateNoise_apply (r d : ℕ)
    (x : DyadicNoiseSpace (r + (d + 1)))
    (i : DyadicNoise ((r + 1) + d)) :
    reassociateNoise r d x i =
      x (noiseCast (by omega : (r + 1) + d = r + (d + 1)) i) := by
  let h : (r + 1) + d = r + (d + 1) := by omega
  simpa [reassociateNoise, noiseCast, h, Nat.add_assoc,
    Nat.add_comm, Nat.add_left_comm] using
    cast_noiseSpace_apply h x i

private def oldNoiseCoordinate : (r d : ℕ) →
    DyadicNoise r → DyadicNoise (r + d)
  | _, 0, i => i
  | r, d + 1, i => Sum.inl (oldNoiseCoordinate r d i)

private def freshNoiseCoordinate (r d : ℕ) (c : DyadicCell r) :
    DyadicNoise (r + (d + 1)) :=
  noiseCast (by omega : (r + 1) + d = r + (d + 1))
    (oldNoiseCoordinate (r + 1) d (Sum.inr c))

private def rootNoiseCoordinate (K : ℕ) : DyadicNoise K :=
  noiseCast (Nat.zero_add K) (oldNoiseCoordinate 0 K ())

private def pathSplitCoordinate : (r d : ℕ) →
    DyadicCell r → ℕ → Fin d → DyadicNoise (r + d)
  | _, 0, _, _, i => Fin.elim0 i
  | r, d + 1, c, t, i =>
      Fin.cases (freshNoiseCoordinate r d c)
        (fun q =>
          if h : t ≤ 2 ^ d then
            noiseCast (by omega : (r + 1) + d = r + (d + 1))
              (pathSplitCoordinate (r + 1) d (Sum.inl c) t q)
          else
            noiseCast (by omega : (r + 1) + d = r + (d + 1))
              (pathSplitCoordinate (r + 1) d (Sum.inr c)
                (t - 2 ^ d) q)) i

/-- `none` is the endpoint coordinate; `some j` is a split at level `j`. -/
def treeNoiseGeneration : (K : ℕ) → DyadicNoise K → Option ℕ
  | 0, _ => none
  | K + 1, Sum.inl i => treeNoiseGeneration K i
  | K + 1, Sum.inr _ => some K

private theorem treeNoiseGeneration_noiseCast {m n : ℕ}
    (h : m = n) (i : DyadicNoise m) :
    treeNoiseGeneration n (noiseCast h i) =
      treeNoiseGeneration m i := by
  subst n
  rfl

private theorem treeNoiseGeneration_oldNoiseCoordinate :
    ∀ r d (i : DyadicNoise r),
      treeNoiseGeneration (r + d) (oldNoiseCoordinate r d i) =
        treeNoiseGeneration r i := by
  intro r d
  induction d with
  | zero => intro i; rfl
  | succ d ih =>
      intro i
      simpa [oldNoiseCoordinate, treeNoiseGeneration] using ih i

private theorem treeNoiseGeneration_freshNoiseCoordinate
    (r d : ℕ) (c : DyadicCell r) :
    treeNoiseGeneration (r + (d + 1))
        (freshNoiseCoordinate r d c) = some r := by
  unfold freshNoiseCoordinate
  rw [treeNoiseGeneration_noiseCast,
    treeNoiseGeneration_oldNoiseCoordinate]
  rfl

private theorem treeNoiseGeneration_rootNoiseCoordinate (K : ℕ) :
    treeNoiseGeneration K (rootNoiseCoordinate K) = none := by
  unfold rootNoiseCoordinate
  rw [treeNoiseGeneration_noiseCast,
    treeNoiseGeneration_oldNoiseCoordinate]
  rfl

private theorem treeNoiseGeneration_pathSplitCoordinate :
    ∀ r d (c : DyadicCell r) (t : ℕ) (i : Fin d),
      treeNoiseGeneration (r + d) (pathSplitCoordinate r d c t i) =
        some (r + i.val) := by
  intro r d
  induction d generalizing r with
  | zero =>
      intro c t i
      exact Fin.elim0 i
  | succ d ih =>
      intro c t i
      refine Fin.cases ?_ (fun q => ?_) i
      · simpa [pathSplitCoordinate] using
          treeNoiseGeneration_freshNoiseCoordinate r d c
      · by_cases h : t ≤ 2 ^ d
        · have hq := ih (r := r + 1) (Sum.inl c) t q
          simp only [pathSplitCoordinate, Fin.cases_succ, dif_pos h]
          rw [treeNoiseGeneration_noiseCast, hq]
          exact congrArg some (by simp; omega)
        · have hq := ih (r := r + 1) (Sum.inr c)
            (t - 2 ^ d) q
          simp only [pathSplitCoordinate, Fin.cases_succ, dif_neg h]
          rw [treeNoiseGeneration_noiseCast, hq]
          exact congrArg some (by simp; omega)

/-- Raw coordinate family `(endpoint, ancestor splits)`. -/
def treePathNoiseCoordinate (K t : ℕ) :
    Fin (K + 1) → DyadicNoise K :=
  Fin.cases (rootNoiseCoordinate K)
    (fun i => noiseCast (Nat.zero_add K)
      (pathSplitCoordinate 0 K () t i))

@[simp] private theorem treeNoiseGeneration_pathNoiseCoordinate_zero
    (K t : ℕ) :
    treeNoiseGeneration K
      (treePathNoiseCoordinate K t (0 : Fin (K + 1))) = none := by
  simpa [treePathNoiseCoordinate] using
    treeNoiseGeneration_rootNoiseCoordinate K

@[simp] private theorem treeNoiseGeneration_pathNoiseCoordinate_succ
    (K t : ℕ) (i : Fin K) :
    treeNoiseGeneration K
      (treePathNoiseCoordinate K t i.succ) = some i.val := by
  simp only [treePathNoiseCoordinate, Fin.cases_succ]
  rw [treeNoiseGeneration_noiseCast,
    treeNoiseGeneration_pathSplitCoordinate]
  simp

/-- The endpoint and all selected split normals are distinct product coordinates. -/
theorem treePathNoiseCoordinate_injective (K t : ℕ) :
    Function.Injective (treePathNoiseCoordinate K t) := by
  intro i j hij
  cases i using Fin.cases with
  | zero =>
      cases j using Fin.cases with
      | zero => rfl
      | succ j =>
          exfalso
          have h := congrArg (treeNoiseGeneration K) hij
          simpa using h
  | succ i =>
      cases j using Fin.cases with
      | zero =>
          exfalso
          have h := congrArg (treeNoiseGeneration K) hij
          simpa using h
      | succ j =>
          apply congrArg Fin.succ
          apply Fin.ext
          have h := congrArg (treeNoiseGeneration K) hij
          simpa using h

/-- The selected raw standard-normal family. -/
def treePathNormal (K t : ℕ) (i : Fin (K + 1))
    (x : DyadicNoiseSpace K) : ℝ :=
  x (treePathNoiseCoordinate K t i)

private theorem treePathNormal_measurable (K t : ℕ)
    (i : Fin (K + 1)) : Measurable (treePathNormal K t i) := by
  exact measurable_pi_apply _

private theorem treePathNormal_map (K t : ℕ)
    (i : Fin (K + 1)) :
    (dyadicNoiseMeasure K).map (treePathNormal K t i) =
      gaussianReal 0 1 := by
  simpa [treePathNormal, dyadicNoiseMeasure] using
    (measurePreserving_eval
      (fun _ : DyadicNoise K => gaussianReal 0 1)
      (treePathNoiseCoordinate K t i)).map_eq

private theorem treePathNormal_iIndep (K t : ℕ) :
    iIndepFun (treePathNormal K t) (dyadicNoiseMeasure K) := by
  have hraw : iIndepFun
      (fun i (x : DyadicNoiseSpace K) => x i)
      (dyadicNoiseMeasure K) := by
    unfold dyadicNoiseMeasure
    simpa using
      (iIndepFun_pi
        (μ := fun _ : DyadicNoise K => gaussianReal 0 1)
        (X := fun _ => (id : ℝ → ℝ))
        (fun _ => measurable_id.aemeasurable))
  simpa [treePathNormal] using
    hraw.precomp (treePathNoiseCoordinate_injective K t)

/-! ## Concrete scalar data along the path -/

private theorem noiseCast_inl {m n : ℕ} (h : m + 1 = n + 1)
    (a : DyadicNoise m) :
    noiseCast h (Sum.inl a : DyadicNoise (m + 1)) =
      Sum.inl (noiseCast (by omega : m = n) a) := by
  obtain rfl : m = n := by omega
  rfl

private theorem oldNoiseCoordinate_left (r d : ℕ)
    (i : DyadicNoise r) :
    noiseCast (by omega : (r + 1) + d = r + (d + 1))
        (oldNoiseCoordinate (r + 1) d (Sum.inl i)) =
      oldNoiseCoordinate r (d + 1) i := by
  induction d with
  | zero => rfl
  | succ d ih =>
      simp only [oldNoiseCoordinate]
      rw [noiseCast_inl]
      exact congrArg Sum.inl (by simpa [oldNoiseCoordinate] using ih)

private theorem horizonNoise_apply_old :
    ∀ r d (x : DyadicNoiseSpace (r + d)) (i : DyadicNoise r),
      horizonNoise r d x i = x (oldNoiseCoordinate r d i) := by
  intro r d
  induction d generalizing r with
  | zero => intro x i; rfl
  | succ d ih =>
      intro x i
      rw [horizonNoise_succ]
      change horizonChildSource r d x (Sum.inl i) =
        x (oldNoiseCoordinate r (d + 1) i)
      unfold horizonChildSource
      rw [ih, reassociateNoise_apply, oldNoiseCoordinate_left]

private theorem freshNoiseCoordinate_apply (r d : ℕ)
    (x : DyadicNoiseSpace (r + (d + 1))) (c : DyadicCell r) :
    x (freshNoiseCoordinate r d c) =
      (dyadicNoiseSplit r (horizonChildSource r d x)).2 c := by
  have h := horizonNoise_apply_old (r + 1) d
    (reassociateNoise r d x) (Sum.inr c)
  rw [reassociateNoise_apply] at h
  simpa [horizonChildSource, freshNoiseCoordinate] using h.symm

private theorem rootNoiseCoordinate_apply (K : ℕ)
    (x : DyadicNoiseSpace K) :
    horizonNoise 0 K (rootSource K x) () =
      x (rootNoiseCoordinate K) := by
  have h := horizonNoise_apply_old 0 K (rootSource K x) ()
  rw [rootSource_apply] at h
  simpa [rootNoiseCoordinate] using h

private def pathCellLength (d j : ℕ) : ℝ :=
  (2 : ℝ) ^ (d - j)

private noncomputable def pathSplit (r d : ℕ)
    (x : DyadicNoiseSpace (r + d)) (c : DyadicCell r)
    (t j : ℕ) : ℝ :=
  if h : j < d then x (pathSplitCoordinate r d c t ⟨j, h⟩) else 0

private noncomputable def pathStandardized : (r d : ℕ) →
    DyadicNoiseSpace (r + d) → DyadicCell r → ℕ → ℕ → ℝ
  | r, d, x, c, _, 0 =>
      horizonGaussian r d x c / Real.sqrt ((2 : ℝ) ^ d)
  | _, 0, _, _, _, _ + 1 => 0
  | r, d + 1, x, c, t, j + 1 =>
      if h : t ≤ 2 ^ d then
        pathStandardized (r + 1) d (reassociateNoise r d x)
          (Sum.inl c) t j
      else
        pathStandardized (r + 1) d (reassociateNoise r d x)
          (Sum.inr c) (t - 2 ^ d) j

private noncomputable def pathParentCount : (r d : ℕ) →
    DyadicNoiseSpace (r + d) → DyadicCell r → ℕ → ℕ → ℝ
  | r, d, x, c, _, 0 => (horizonCount r d x c : ℝ)
  | _, 0, _, _, _, _ + 1 => 0
  | r, d + 1, x, c, t, j + 1 =>
      if h : t ≤ 2 ^ d then
        pathParentCount (r + 1) d (reassociateNoise r d x)
          (Sum.inl c) t j
      else
        pathParentCount (r + 1) d (reassociateNoise r d x)
          (Sum.inr c) (t - 2 ^ d) j

private noncomputable def pathQuantileError : (r d : ℕ) →
    DyadicNoiseSpace (r + d) → DyadicCell r → ℕ → ℕ → ℝ
  | _, 0, _, _, _, _ => 0
  | r, d + 1, x, c, _, 0 =>
      splitQuantileError ((r + 1) + d) r (horizonChildSource r d x) c
  | r, d + 1, x, c, t, j + 1 =>
      if h : t ≤ 2 ^ d then
        pathQuantileError (r + 1) d (reassociateNoise r d x)
          (Sum.inl c) t j
      else
        pathQuantileError (r + 1) d (reassociateNoise r d x)
          (Sum.inr c) (t - 2 ^ d) j

private noncomputable def pathCorrection : (r d : ℕ) →
    DyadicNoiseSpace (r + d) → DyadicCell r → ℕ → ℕ → ℝ
  | _, 0, _, _, _, _ => 0
  | r, d + 1, x, c, _, 0 => horizonCorrection r d x c
  | r, d + 1, x, c, t, j + 1 =>
      if h : t ≤ 2 ^ d then
        pathCorrection (r + 1) d (reassociateNoise r d x)
          (Sum.inl c) t j
      else
        pathCorrection (r + 1) d (reassociateNoise r d x)
          (Sum.inr c) (t - 2 ^ d) j

private noncomputable def pathDiscrepancy : (r d : ℕ) →
    DyadicNoiseSpace (r + d) → DyadicCell r → ℕ → ℕ → ℝ
  | r, d, x, c, _, 0 => horizonError r d x c
  | _, 0, _, _, _, _ + 1 => 0
  | r, d + 1, x, c, t, j + 1 =>
      if h : t ≤ 2 ^ d then
        pathDiscrepancy (r + 1) d (reassociateNoise r d x)
          (Sum.inl c) t j
      else
        pathDiscrepancy (r + 1) d (reassociateNoise r d x)
          (Sum.inr c) (t - 2 ^ d) j

private noncomputable def pathDirection : (r d : ℕ) →
    DyadicNoiseSpace (r + d) → DyadicCell r → ℕ → ℕ → ℝ
  | _, 0, _, _, _, _ => 1
  | _, d + 1, _, _, t, 0 => if t ≤ 2 ^ d then 1 else -1
  | r, d + 1, x, c, t, j + 1 =>
      if h : t ≤ 2 ^ d then
        pathDirection (r + 1) d (reassociateNoise r d x)
          (Sum.inl c) t j
      else
        pathDirection (r + 1) d (reassociateNoise r d x)
          (Sum.inr c) (t - 2 ^ d) j

private theorem pathSplit_zero (r d : ℕ)
    (x : DyadicNoiseSpace (r + (d + 1))) (c : DyadicCell r) (t : ℕ) :
    pathSplit r (d + 1) x c t 0 =
      (dyadicNoiseSplit r (horizonChildSource r d x)).2 c := by
  simpa [pathSplit, pathSplitCoordinate] using
    freshNoiseCoordinate_apply r d x c

private theorem pathSplit_succ_left (r d : ℕ)
    (x : DyadicNoiseSpace (r + (d + 1))) (c : DyadicCell r)
    (t j : ℕ) (hleft : t ≤ 2 ^ d) :
    pathSplit r (d + 1) x c t (j + 1) =
      pathSplit (r + 1) d (reassociateNoise r d x)
        (Sum.inl c) t j := by
  by_cases hj : j < d
  · have hjs : j + 1 < d + 1 := by omega
    rw [pathSplit, dif_pos hjs, pathSplit, dif_pos hj]
    have e : pathSplitCoordinate r (d + 1) c t ⟨j + 1, hjs⟩ =
        noiseCast (by omega : (r + 1) + d = r + (d + 1))
          (pathSplitCoordinate (r + 1) d (Sum.inl c) t ⟨j, hj⟩) := by
      show pathSplitCoordinate r (d + 1) c t (Fin.succ ⟨j, hj⟩) = _
      simp [pathSplitCoordinate, hleft]
    rw [e]
    exact (reassociateNoise_apply r d x _).symm
  · have hjs : ¬j + 1 < d + 1 := by omega
    simp [pathSplit, hjs, hj]

private theorem pathSplit_succ_right (r d : ℕ)
    (x : DyadicNoiseSpace (r + (d + 1))) (c : DyadicCell r)
    (t j : ℕ) (hright : ¬t ≤ 2 ^ d) :
    pathSplit r (d + 1) x c t (j + 1) =
      pathSplit (r + 1) d (reassociateNoise r d x)
        (Sum.inr c) (t - 2 ^ d) j := by
  by_cases hj : j < d
  · have hjs : j + 1 < d + 1 := by omega
    rw [pathSplit, dif_pos hjs, pathSplit, dif_pos hj]
    have e : pathSplitCoordinate r (d + 1) c t ⟨j + 1, hjs⟩ =
        noiseCast (by omega : (r + 1) + d = r + (d + 1))
          (pathSplitCoordinate (r + 1) d (Sum.inr c) (t - 2 ^ d) ⟨j, hj⟩) := by
      show pathSplitCoordinate r (d + 1) c t (Fin.succ ⟨j, hj⟩) = _
      simp [pathSplitCoordinate, hright]
    rw [e]
    exact (reassociateNoise_apply r d x _).symm
  · have hjs : ¬j + 1 < d + 1 := by omega
    simp [pathSplit, hjs, hj]

private theorem horizonGaussian_left (r d : ℕ)
    (x : DyadicNoiseSpace (r + (d + 1))) (c : DyadicCell r) :
    horizonGaussian (r + 1) d (reassociateNoise r d x) (Sum.inl c) =
      (horizonGaussian r (d + 1) x c +
        Real.sqrt ((2 : ℝ) ^ (d + 1)) *
          (dyadicNoiseSplit r (horizonChildSource r d x)).2 c) / 2 := by
  have h := gaussianLevel_left_formula ((r + 1) + d) r
    (horizonChildSource r d x) c
  simpa [horizonGaussian, horizonChildSource, horizonNoise_succ,
    dyadicVariance_offset, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm] using h

private theorem horizonGaussian_right (r d : ℕ)
    (x : DyadicNoiseSpace (r + (d + 1))) (c : DyadicCell r) :
    horizonGaussian (r + 1) d (reassociateNoise r d x) (Sum.inr c) =
      (horizonGaussian r (d + 1) x c -
        Real.sqrt ((2 : ℝ) ^ (d + 1)) *
          (dyadicNoiseSplit r (horizonChildSource r d x)).2 c) / 2 := by
  have h := gaussianLevel_right_formula ((r + 1) + d) r
    (horizonChildSource r d x) c
  simpa [horizonGaussian, horizonChildSource, horizonNoise_succ,
    dyadicVariance_offset, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm] using h

private theorem sqrt_two_pow_succ (d : ℕ) :
    Real.sqrt ((2 : ℝ) ^ (d + 1)) =
      Real.sqrt ((2 : ℝ) ^ d) * Real.sqrt 2 := by
  rw [pow_succ, Real.sqrt_mul (by positivity : 0 ≤ (2 : ℝ) ^ d)]

private theorem normalized_left (d : ℕ) (p z : ℝ) :
    ((p + Real.sqrt ((2 : ℝ) ^ (d + 1)) * z) / 2) /
        Real.sqrt ((2 : ℝ) ^ d) =
      (p / Real.sqrt ((2 : ℝ) ^ (d + 1)) + z) /
        Real.sqrt 2 := by
  have ha : 0 < Real.sqrt ((2 : ℝ) ^ d) := by positivity
  have hb : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hb2 : Real.sqrt (2 : ℝ) * Real.sqrt 2 = 2 :=
    Real.mul_self_sqrt (by norm_num)
  have hsq : Real.sqrt (2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  rw [sqrt_two_pow_succ]
  field_simp [ha.ne', hb.ne']
  first
    | (rw [hsq]; ring)
    | (simp only [hsq]; ring)
    | nlinarith [hsq]

private theorem normalized_right (d : ℕ) (p z : ℝ) :
    ((p - Real.sqrt ((2 : ℝ) ^ (d + 1)) * z) / 2) /
        Real.sqrt ((2 : ℝ) ^ d) =
      (p / Real.sqrt ((2 : ℝ) ^ (d + 1)) - z) /
        Real.sqrt 2 := by
  have ha : 0 < Real.sqrt ((2 : ℝ) ^ d) := by positivity
  have hb : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hb2 : Real.sqrt (2 : ℝ) * Real.sqrt 2 = 2 :=
    Real.mul_self_sqrt (by norm_num)
  have hsq : Real.sqrt (2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  rw [sqrt_two_pow_succ]
  field_simp [ha.ne', hb.ne']
  first
    | (rw [hsq]; ring)
    | (simp only [hsq]; ring)
    | nlinarith [hsq]

private theorem pathDirection_pm :
    ∀ r d (x : DyadicNoiseSpace (r + d)) (c : DyadicCell r)
      (t j : ℕ), j < d →
      pathDirection r d x c t j = 1 ∨
        pathDirection r d x c t j = -1 := by
  intro r d
  induction d generalizing r with
  | zero => intro x c t j hj; omega
  | succ d ih =>
      intro x c t j hj
      cases j with
      | zero =>
          by_cases h : t ≤ 2 ^ d <;> simp [pathDirection, h]
      | succ j =>
          have hjd : j < d := by omega
          by_cases h : t ≤ 2 ^ d
          · simpa [pathDirection, h] using
              ih (r := r + 1) (reassociateNoise r d x)
                (Sum.inl c) t j hjd
          · simpa [pathDirection, h] using
              ih (r := r + 1) (reassociateNoise r d x)
                (Sum.inr c) (t - 2 ^ d) j hjd

private theorem pathStandardized_succ :
    ∀ r d (x : DyadicNoiseSpace (r + d)) (c : DyadicCell r)
      (t j : ℕ), j < d →
      pathStandardized r d x c t (j + 1) =
        (pathStandardized r d x c t j +
          pathDirection r d x c t j * pathSplit r d x c t j) /
            Real.sqrt 2 := by
  intro r d
  induction d generalizing r with
  | zero => intro x c t j hj; omega
  | succ d ih =>
      intro x c t j hj
      cases j with
      | zero =>
          by_cases h : t ≤ 2 ^ d
          · simp only [pathStandardized, pathDirection, dif_pos h, if_pos h]
            rw [pathSplit_zero, horizonGaussian_left, one_mul]
            exact normalized_left d _ _
          · simp only [pathStandardized, pathDirection, h, if_false]
            rw [pathSplit_zero, horizonGaussian_right]
            simpa using normalized_right d
              (horizonGaussian r (d + 1) x c)
              ((dyadicNoiseSplit r (horizonChildSource r d x)).2 c)
      | succ j =>
          have hjd : j < d := by omega
          by_cases h : t ≤ 2 ^ d
          · rw [pathSplit_succ_left r d x c t j h]
            simpa [pathStandardized, pathDirection, h] using
              ih (r := r + 1) (reassociateNoise r d x)
                (Sum.inl c) t j hjd
          · rw [pathSplit_succ_right r d x c t j h]
            simpa [pathStandardized, pathDirection, h] using
              ih (r := r + 1) (reassociateNoise r d x)
                (Sum.inr c) (t - 2 ^ d) j hjd

private theorem pathDiscrepancy_succ :
    ∀ r d (x : DyadicNoiseSpace (r + d)) (c : DyadicCell r)
      (t j : ℕ), j < d →
      pathDiscrepancy r d x c t (j + 1) =
        pathDiscrepancy r d x c t j / 2 +
          pathDirection r d x c t j * pathCorrection r d x c t j := by
  intro r d
  induction d generalizing r with
  | zero => intro x c t j hj; omega
  | succ d ih =>
      intro x c t j hj
      cases j with
      | zero =>
          by_cases h : t ≤ 2 ^ d
          · simpa [pathDiscrepancy, pathDirection, pathCorrection, h] using
              horizonError_left r d x c
          · simpa [pathDiscrepancy, pathDirection, pathCorrection, h] using
              horizonError_right r d x c
      | succ j =>
          have hjd : j < d := by omega
          by_cases h : t ≤ 2 ^ d
          · simpa [pathDiscrepancy, pathDirection, pathCorrection, h] using
              ih (r := r + 1) (reassociateNoise r d x)
                (Sum.inl c) t j hjd
          · simpa [pathDiscrepancy, pathDirection, pathCorrection, h] using
              ih (r := r + 1) (reassociateNoise r d x)
                (Sum.inr c) (t - 2 ^ d) j hjd

private theorem bridgeCorrection_abs_le (K r : ℕ)
    (x : DyadicNoiseSpace (r + 1)) (c : DyadicCell r) :
    |bridgeCorrection K r x c| ≤
      |splitQuantileError K r x c| +
        (|Real.sqrt (poissonLevel K r (dyadicNoiseSplit r x).1 c : ℝ) -
            Real.sqrt (dyadicVariance K r : ℝ)| / 2) *
          |(dyadicNoiseSplit r x).2 c| := by
  dsimp [bridgeCorrection]
  calc
    |splitQuantileError K r x c +
        (Real.sqrt (poissonLevel K r (dyadicNoiseSplit r x).1 c : ℝ) -
          Real.sqrt (dyadicVariance K r : ℝ)) / 2 *
            (dyadicNoiseSplit r x).2 c| ≤
      |splitQuantileError K r x c| +
        |(Real.sqrt (poissonLevel K r (dyadicNoiseSplit r x).1 c : ℝ) -
          Real.sqrt (dyadicVariance K r : ℝ)) / 2 *
            (dyadicNoiseSplit r x).2 c| := abs_add_le _ _
    _ = _ := by
      rw [abs_mul, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]

private theorem pathParentCount_zero_eq (r d : ℕ)
    (x : DyadicNoiseSpace (r + (d + 1))) (c : DyadicCell r) (t : ℕ) :
    (poissonLevel ((r + 1) + d) r
      (dyadicNoiseSplit r (horizonChildSource r d x)).1 c : ℝ) =
        pathParentCount r (d + 1) x c t 0 := by
  simp [pathParentCount, horizonCount, horizonChildSource,
    horizonNoise_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

private theorem pathDiscrepancy_zero_eq (r d : ℕ)
    (x : DyadicNoiseSpace (r + (d + 1))) (c : DyadicCell r) (t : ℕ) :
    bridgeError ((r + 1) + d) r
      (dyadicNoiseSplit r (horizonChildSource r d x)).1 c =
        pathDiscrepancy r (d + 1) x c t 0 := by
  simp [pathDiscrepancy, horizonError, horizonChildSource,
    horizonNoise_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

private theorem pathStandardized_zero_eq (r d : ℕ)
    (x : DyadicNoiseSpace (r + (d + 1))) (c : DyadicCell r) (t : ℕ) :
    standardizedParentIncrement ((r + 1) + d) r
      (horizonChildSource r d x) c =
        pathStandardized r (d + 1) x c t 0 := by
  simp [standardizedParentIncrement, pathStandardized, horizonGaussian,
    horizonChildSource, horizonNoise_succ, dyadicVariance_offset,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

private theorem pathLength_zero_eq (r d : ℕ) :
    (dyadicVariance ((r + 1) + d) r : ℝ) =
      pathCellLength (d + 1) 0 := by
  simpa [pathCellLength, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm] using dyadicVariance_offset r (d + 1)

private theorem pathQuantileError_bound :
    ∀ r d (x : DyadicNoiseSpace (r + d)) (c : DyadicCell r)
      (t j : ℕ), j < d →
      |pathQuantileError r d x c t j| ≤ 1 + pathSplit r d x c t j ^ 2 := by
  intro r d
  induction d generalizing r with
  | zero => intro x c t j hj; omega
  | succ d ih =>
      intro x c t j hj
      cases j with
      | zero =>
          have h := abs_splitQuantileError_le ((r + 1) + d) r
            (horizonChildSource r d x) c
          simpa [pathQuantileError, pathSplit_zero] using h
      | succ j =>
          have hjd : j < d := by omega
          by_cases h : t ≤ 2 ^ d
          · rw [pathSplit_succ_left r d x c t j h]
            simpa [pathQuantileError, h] using
              ih (r := r + 1) (reassociateNoise r d x)
                (Sum.inl c) t j hjd
          · rw [pathSplit_succ_right r d x c t j h]
            simpa [pathQuantileError, h] using
              ih (r := r + 1) (reassociateNoise r d x)
                (Sum.inr c) (t - 2 ^ d) j hjd

private theorem pathCorrection_bound :
    ∀ r d (x : DyadicNoiseSpace (r + d)) (c : DyadicCell r)
      (t j : ℕ), j < d →
      |pathCorrection r d x c t j| ≤
        |pathQuantileError r d x c t j| +
          (|Real.sqrt (pathParentCount r d x c t j) -
              Real.sqrt (pathCellLength d j)| / 2) *
            |pathSplit r d x c t j| := by
  intro r d
  induction d generalizing r with
  | zero => intro x c t j hj; omega
  | succ d ih =>
      intro x c t j hj
      cases j with
      | zero =>
          have h := bridgeCorrection_abs_le ((r + 1) + d) r
            (horizonChildSource r d x) c
          rw [pathParentCount_zero_eq r d x c t,
            pathLength_zero_eq r d] at h
          simpa [pathCorrection, pathQuantileError, horizonCorrection,
            pathSplit_zero] using h
      | succ j =>
          have hjd : j < d := by omega
          by_cases h : t ≤ 2 ^ d
          · rw [pathSplit_succ_left r d x c t j h]
            simpa [pathCorrection, pathQuantileError, pathParentCount,
              pathCellLength, h] using
              ih (r := r + 1) (reassociateNoise r d x)
                (Sum.inl c) t j hjd
          · rw [pathSplit_succ_right r d x c t j h]
            simpa [pathCorrection, pathQuantileError, pathParentCount,
              pathCellLength, h] using
              ih (r := r + 1) (reassociateNoise r d x)
                (Sum.inr c) (t - 2 ^ d) j hjd

private theorem pathSqrtDifference_linear :
    ∀ r d (x : DyadicNoiseSpace (r + d)) (c : DyadicCell r)
      (t j : ℕ), j < d →
      |Real.sqrt (pathParentCount r d x c t j) -
          Real.sqrt (pathCellLength d j)| ≤
        |pathDiscrepancy r d x c t j| /
            Real.sqrt (pathCellLength d j) +
          |pathStandardized r d x c t j| := by
  intro r d
  induction d generalizing r with
  | zero => intro x c t j hj; omega
  | succ d ih =>
      intro x c t j hj
      cases j with
      | zero =>
          have h := bridge_sqrt_linear ((r + 1) + d) r
            (horizonChildSource r d x) c
          rw [pathParentCount_zero_eq r d x c t,
            pathLength_zero_eq r d,
            pathDiscrepancy_zero_eq r d x c t,
            pathStandardized_zero_eq r d x c t] at h
          exact h
      | succ j =>
          have hjd : j < d := by omega
          by_cases h : t ≤ 2 ^ d
          · simpa [pathParentCount, pathCellLength, pathDiscrepancy,
              pathStandardized, h] using
              ih (r := r + 1) (reassociateNoise r d x)
                (Sum.inl c) t j hjd
          · simpa [pathParentCount, pathCellLength, pathDiscrepancy,
              pathStandardized, h] using
              ih (r := r + 1) (reassociateNoise r d x)
                (Sum.inr c) (t - 2 ^ d) j hjd

private theorem pathSqrtDifference_holder :
    ∀ r d (x : DyadicNoiseSpace (r + d)) (c : DyadicCell r)
      (t j : ℕ), j < d →
      |Real.sqrt (pathParentCount r d x c t j) -
          Real.sqrt (pathCellLength d j)| ≤
        Real.sqrt |pathDiscrepancy r d x c t j| +
          Real.sqrt (Real.sqrt (pathCellLength d j)) *
            Real.sqrt |pathStandardized r d x c t j| := by
  intro r d
  induction d generalizing r with
  | zero => intro x c t j hj; omega
  | succ d ih =>
      intro x c t j hj
      cases j with
      | zero =>
          have h := bridge_sqrt_holder ((r + 1) + d) r
            (horizonChildSource r d x) c
          rw [pathParentCount_zero_eq r d x c t,
            pathLength_zero_eq r d,
            pathDiscrepancy_zero_eq r d x c t,
            pathStandardized_zero_eq r d x c t] at h
          exact h
      | succ j =>
          have hjd : j < d := by omega
          by_cases h : t ≤ 2 ^ d
          · simpa [pathParentCount, pathCellLength, pathDiscrepancy,
              pathStandardized, h] using
              ih (r := r + 1) (reassociateNoise r d x)
                (Sum.inl c) t j hjd
          · simpa [pathParentCount, pathCellLength, pathDiscrepancy,
              pathStandardized, h] using
              ih (r := r + 1) (reassociateNoise r d x)
                (Sum.inr c) (t - 2 ^ d) j hjd

private theorem pathStandardized_root_eq_noise (K : ℕ)
    (x : DyadicNoiseSpace K) (t : ℕ) :
    pathStandardized 0 K (rootSource K x) () t 0 =
      horizonNoise 0 K (rootSource K x) () := by
  have hs : 0 < Real.sqrt ((2 : ℝ) ^ K) := by positivity
  unfold pathStandardized horizonGaussian
  simp only [gaussianLevel]
  rw [dyadicVariance_offset 0 K]
  field_simp [hs.ne']

private theorem pathRoot_eq_pathNormal (K : ℕ)
    (x : DyadicNoiseSpace K) (t : ℕ) :
    pathStandardized 0 K (rootSource K x) () t 0 =
      treePathNormal K t (0 : Fin (K + 1)) x := by
  calc
    pathStandardized 0 K (rootSource K x) () t 0 =
        horizonNoise 0 K (rootSource K x) () :=
      pathStandardized_root_eq_noise K x t
    _ = x (rootNoiseCoordinate K) := rootNoiseCoordinate_apply K x
    _ = treePathNormal K t (0 : Fin (K + 1)) x := rfl

private theorem pathSplit_eq_pathNormal (K : ℕ)
    (x : DyadicNoiseSpace K) (t : ℕ) (i : Fin K) :
    pathSplit 0 K (rootSource K x) () t i.val =
      treePathNormal K t i.succ x := by
  unfold pathSplit treePathNormal treePathNoiseCoordinate
  rw [dif_pos i.isLt]
  exact rootSource_apply K x _

/-! ## The concrete bridge chain -/

private noncomputable def treePathGaussianChain
    (K : ℕ) (x : DyadicNoiseSpace K) (t : ℕ) :
    GaussianAncestorChain K where
  root := pathStandardized 0 K (rootSource K x) () t 0
  split := pathSplit 0 K (rootSource K x) () t
  standardized := pathStandardized 0 K (rootSource K x) () t
  direction := pathDirection 0 K (rootSource K x) () t
  standardized_zero := rfl
  direction_pm := fun j hj => pathDirection_pm 0 K
    (rootSource K x) () t j hj
  standardized_succ := fun j hj => pathStandardized_succ 0 K
    (rootSource K x) () t j hj

/-- Concrete bridge chain along the ancestor path selected by integer time `t`. -/
noncomputable def treePathBridgeChain
    (K : ℕ) (x : DyadicNoiseSpace K) (t : ℕ) :
    DyadicBridgeChain K where
  toGaussianAncestorChain := treePathGaussianChain K x t
  parentCount := pathParentCount 0 K (rootSource K x) () t
  quantileError := pathQuantileError 0 K (rootSource K x) () t
  correction := pathCorrection 0 K (rootSource K x) () t
  discrepancy := pathDiscrepancy 0 K (rootSource K x) () t
  branchDirection := pathDirection 0 K (rootSource K x) () t
  branchDirection_pm := fun j hj => pathDirection_pm 0 K
    (rootSource K x) () t j hj
  discrepancy_succ := fun j hj => pathDiscrepancy_succ 0 K
    (rootSource K x) () t j hj
  top_error_bound := by
    have h := root_bridgeError_le (0 + K)
      (horizonNoise 0 K (rootSource K x)) ()
    rw [← pathStandardized_root_eq_noise K x t] at h
    have e : pathDiscrepancy 0 K (rootSource K x) () t 0 =
        horizonError 0 K (rootSource K x) () := by
      simp [pathDiscrepancy]
    simp only [treePathGaussianChain]
    rw [e]
    exact h
  quantile_error_bound := by
    intro j hj
    exact pathQuantileError_bound 0 K (rootSource K x) () t j hj
  correction_bound := by
    intro j hj
    simpa [pathCellLength, dyadicLength] using
      pathCorrection_bound 0 K (rootSource K x) () t j hj
  sqrt_difference_linear := by
    intro j hj
    simpa [pathCellLength, dyadicLength] using
      pathSqrtDifference_linear 0 K (rootSource K x) () t j hj
  sqrt_difference_holder := by
    intro j hj
    simpa [pathCellLength, dyadicLength] using
      pathSqrtDifference_holder 0 K (rootSource K x) () t j hj

/-- The exact normal vector consumed by K16. -/
def treePathAugmentedNormal (K t : ℕ) (i : Fin (K + 1))
    (x : DyadicNoiseSpace K) : ℝ :=
  augmentedNoise K
    (treePathBridgeChain K x t).root
    (treePathBridgeChain K x t).split i

private theorem treePathAugmentedNormal_eq
    (K t : ℕ) (i : Fin (K + 1)) (x : DyadicNoiseSpace K) :
    treePathAugmentedNormal K t i x = treePathNormal K t i x := by
  refine Fin.cases ?_ (fun q => ?_) i
  · simpa [treePathAugmentedNormal, augmentedNoise,
      treePathBridgeChain, treePathGaussianChain] using
      pathRoot_eq_pathNormal K x t
  · simpa [treePathAugmentedNormal, augmentedNoise,
      treePathBridgeChain, treePathGaussianChain] using
      pathSplit_eq_pathNormal K x t q

private theorem treePathAugmentedNormal_funext (K t : ℕ) :
    treePathAugmentedNormal K t = treePathNormal K t := by
  funext i x
  exact treePathAugmentedNormal_eq K t i x

/-- The selected endpoint-plus-split family is iid standard Gaussian. -/
theorem treePathAugmentedNormal_iIndep (K t : ℕ) :
    iIndepFun (treePathAugmentedNormal K t)
      (dyadicNoiseMeasure K) := by
  rw [treePathAugmentedNormal_funext]
  exact treePathNormal_iIndep K t

/-- Every selected normal has law `N(0,1)`. -/
theorem treePathAugmentedNormal_map (K t : ℕ)
    (i : Fin (K + 1)) :
    (dyadicNoiseMeasure K).map (treePathAugmentedNormal K t i) =
      gaussianReal 0 1 := by
  rw [treePathAugmentedNormal_funext]
  exact treePathNormal_map K t i

private theorem treePathAugmentedNormal_measurable (K t : ℕ)
    (i : Fin (K + 1)) :
    Measurable (treePathAugmentedNormal K t i) := by
  rw [treePathAugmentedNormal_funext]
  exact treePathNormal_measurable K t i

private theorem treePath_quadratic_eq_chiSquare
    (K t : ℕ) (x : DyadicNoiseSpace K) :
    quadraticNoise (treePathBridgeChain K x t).toGaussianAncestorChain =
      chiSquareSum (treePathAugmentedNormal K t) x := by
  unfold quadraticNoise chiSquareSum treePathAugmentedNormal
  rw [Fin.sum_univ_succ]
  simp only [augmentedNoise, Fin.cases_zero, Fin.cases_succ]
  rw [Finset.sum_range]

private theorem treePath_linear_eq_weightedAbs
    (K t : ℕ) (L : ℝ) (x : DyadicNoiseSpace K) :
    kmtLinearTerm (treePathBridgeChain K x t).toGaussianAncestorChain L =
      weightedAbsSum (kmtWeight K L)
        (treePathAugmentedNormal K t) x := by
  rfl

private theorem sum_pathCorrection :
    ∀ r d (x : DyadicNoiseSpace (r + d)) (c : DyadicCell r) (t : ℕ),
      (∑ j ∈ Finset.range d, |pathCorrection r d x c t j|) =
        boundaryCorrectionAbs r d x c t := by
  intro r d
  induction d generalizing r with
  | zero => intro x c t; simp [pathCorrection, boundaryCorrectionAbs]
  | succ d ih =>
      intro x c t
      by_cases h : t ≤ 2 ^ d
      · rw [Finset.sum_range_succ']
        simp only [pathCorrection, dif_pos h]
        rw [ih (r := r + 1) (reassociateNoise r d x) (Sum.inl c) t]
        simp [boundaryCorrectionAbs, h, add_comm]
      · rw [Finset.sum_range_succ']
        simp only [pathCorrection, dif_neg h]
        rw [ih (r := r + 1) (reassociateNoise r d x)
          (Sum.inr c) (t - 2 ^ d)]
        simp [boundaryCorrectionAbs, h, add_comm]

private theorem treePathBudget_eq (K : ℕ)
    (x : DyadicNoiseSpace K) (t : ℕ) :
    pathBudget (treePathBridgeChain K x t) =
      |horizonError 0 K (rootSource K x) ()| +
        boundaryCorrectionAbs 0 K (rootSource K x) () t := by
  unfold pathBudget treePathBridgeChain
  rw [sum_pathCorrection]
  show |pathDiscrepancy 0 K (rootSource K x) () t 0| + _ = _
  have e : pathDiscrepancy 0 K (rootSource K x) () t 0 =
      horizonError 0 K (rootSource K x) () := by
    simp [pathDiscrepancy]
  rw [e]

/-- The committed skeleton error satisfies the strong, factor-one K13 bound. -/
def spatialTreeError (K t : ℕ) (x : DyadicNoiseSpace K) : ℝ :=
  |(DyadicSpatialSkeleton.spatialPoissonSkeleton K x t : ℝ) -
      (t : ℝ) - DyadicSpatialSkeleton.spatialGaussianSkeleton K x t|

private theorem spatialTreeError_le_pathBudget
    (K t : ℕ) (ht : t ≤ 2 ^ K) (x : DyadicNoiseSpace K) :
    spatialTreeError K t x ≤ pathBudget (treePathBridgeChain K x t) := by
  unfold spatialTreeError
  rw [← spatialPoissonSkeleton_agree K x ht,
    ← spatialGaussianSkeleton_agree K x ht]
  show |(spatialPoissonPartial 0 K (rootSource K x) () t : ℝ) - (t : ℝ) -
      spatialGaussianPartial 0 K (rootSource K x) () t| ≤ _
  rw [spatialDiscrepancy_eq_bridgePartial 0 K (rootSource K x) () t ht]
  calc
    |spatialBridgePartial 0 K (rootSource K x) () t| ≤
        |horizonError 0 K (rootSource K x) ()| +
          boundaryCorrectionAbs 0 K (rootSource K x) () t :=
      abs_spatialBridgePartial_le 0 K (rootSource K x) () ht
    _ = pathBudget (treePathBridgeChain K x t) :=
      (treePathBudget_eq K x t).symm

/-! ## The common coarse event and H2 -/

/-- Coarse failure, expressed directly on raw split coordinates.  A coordinate
with generation `some j` is exactly the split normal attached to a level-`j`
cell; the endpoint coordinate has generation `none` and is excluded. -/
def treeKMTCoarseFailure (K : ℕ) (L : ℝ) : Set (DyadicNoiseSpace K) :=
  {x | ∃ i : DyadicNoise K, ∃ j : ℕ,
    treeNoiseGeneration K i = some j ∧
      L ≤ dyadicLength K j ∧
        Real.sqrt L / 4 < |x i|}

private theorem treePath_coarse_of_not_failure
    (K t : ℕ) {L : ℝ} (x : DyadicNoiseSpace K)
    (hgood : x ∉ treeKMTCoarseFailure K L) :
    ∀ j, j < K → L ≤ dyadicLength K j →
      |(treePathBridgeChain K x t).split j| ≤ Real.sqrt L / 4 := by
  intro j hj hlength
  apply le_of_not_gt
  intro hlarge
  apply hgood
  let q : Fin K := ⟨j, hj⟩
  refine ⟨treePathNoiseCoordinate K t q.succ, j, ?_, hlength, ?_⟩
  · simpa [q] using treeNoiseGeneration_pathNoiseCoordinate_succ K t q
  · have h2 : (treePathBridgeChain K x t).split j =
        x (treePathNoiseCoordinate K t q.succ) :=
      pathSplit_eq_pathNormal K x t q
    rw [← h2]
    exact hlarge

/-- K18/H2 on the concrete tree, with no abstract probabilistic premise. -/
theorem spatialTreeError_point_tail
    (K t : ℕ) (ht : t ≤ 2 ^ K)
    {L u : ℝ} (hL : 1 ≤ L) (hu : 0 ≤ u) :
    (dyadicNoiseMeasure K).real
        ({x | (68 / 3 : ℝ) * (K + 1 : ℝ) + u < spatialTreeError K t x} \
          treeKMTCoarseFailure K L) ≤
      Real.exp (-(3 * u / 512)) +
        (2 : ℝ) ^ (K + 1) *
          Real.exp (-(9 * u ^ 2 / (128 * L))) := by
  classical
  let v : Fin (K + 1) → ℝ := kmtWeight K L
  let Z : Fin (K + 1) → DyadicNoiseSpace K → ℝ :=
    treePathAugmentedNormal K t
  let envelope : DyadicNoiseSpace K → ℝ := fun x =>
    (4 / 3 : ℝ) * (K + 1 : ℝ) +
      (32 / 3 : ℝ) * chiSquareSum Z x +
      (1 / 6 : ℝ) * Real.sqrt L * weightedAbsSum v Z x
  let G : DyadicNoiseSpace K → ℝ := fun x =>
    if x ∈ treeKMTCoarseFailure K L then envelope x
    else spatialTreeError K t x
  have hZm : ∀ i, Measurable (Z i) := by
    intro i
    simpa [Z] using treePathAugmentedNormal_measurable K t i
  have hZi : iIndepFun Z (dyadicNoiseMeasure K) := by
    simpa [Z] using treePathAugmentedNormal_iIndep K t
  have hZlaw : ∀ i,
      (dyadicNoiseMeasure K).map (Z i) = gaussianReal 0 1 := by
    intro i
    simpa [Z] using treePathAugmentedNormal_map K t i
  have hV : weightSquareMass v ≤ 64 := by
    dsimp [v]
    simpa [weightSquareMass] using
      kmtWeight_sq_sum_le_sixtyFour K L
  have hdet : ∀ x, G x ≤
      (4 / 3 : ℝ) * (K + 1 : ℝ) +
        (32 / 3 : ℝ) * chiSquareSum Z x +
        (1 / 6 : ℝ) * Real.sqrt L * weightedAbsSum v Z x := by
    intro x
    by_cases hbad : x ∈ treeKMTCoarseFailure K L
    · simp [G, envelope, hbad]
    · simp only [G, if_neg hbad]
      calc
        spatialTreeError K t x ≤ pathBudget (treePathBridgeChain K x t) :=
          spatialTreeError_le_pathBudget K t ht x
        _ ≤ (4 / 3 : ℝ) * (K + 1 : ℝ) +
              (32 / 3 : ℝ) *
                quadraticNoise
                  (treePathBridgeChain K x t).toGaussianAncestorChain +
              (1 / 6 : ℝ) * Real.sqrt L *
                kmtLinearTerm
                  (treePathBridgeChain K x t).toGaussianAncestorChain L :=
          pathBudget_le_sharp (treePathBridgeChain K x t) hL
            (treePath_coarse_of_not_failure K t x hbad)
        _ = (4 / 3 : ℝ) * (K + 1 : ℝ) +
              (32 / 3 : ℝ) * chiSquareSum Z x +
              (1 / 6 : ℝ) * Real.sqrt L * weightedAbsSum v Z x := by
          dsimp [Z, v]
          rw [treePath_quadratic_eq_chiSquare,
            treePath_linear_eq_weightedAbs]
  have htail := kmtChainEnvelope_tail
    (μ := dyadicNoiseMeasure K) v Z hZm hZi hZlaw G hL hu hV hdet
  have hsub :
      ({x | (68 / 3 : ℝ) * (K + 1 : ℝ) + u < spatialTreeError K t x} \
          treeKMTCoarseFailure K L) ⊆
        {x | (68 / 3 : ℝ) * (K + 1 : ℝ) + u < G x} := by
    rintro x ⟨hx, hgood⟩
    simpa [G, hgood] using hx
  exact (measureReal_mono hsub).trans htail

/-- The two committed skeletons have the requested iid unit-increment laws. -/
theorem committedSpatialSkeleton_increment_laws (K : ℕ) :
    iIndepFun (spatialGaussianUnitIncrement K) (dyadicNoiseMeasure K) ∧
    (∀ j, (dyadicNoiseMeasure K).map
      (spatialGaussianUnitIncrement K j) = gaussianReal 0 1) ∧
    iIndepFun (spatialPoissonUnitIncrement K) (dyadicNoiseMeasure K) ∧
    (∀ j, (dyadicNoiseMeasure K).map
      (spatialPoissonUnitIncrement K j) = poisMeasure 1) :=
  coupledSpatialLeafLaws K

/-!
THEOREM LIST
* `treePathNoiseCoordinate_injective`
* `treePathBridgeChain`
* `treePathAugmentedNormal_iIndep`
* `treePathAugmentedNormal_map`
* `treeKMTCoarseFailure`
* `spatialTreeError_point_tail`
* `committedSpatialSkeleton_increment_laws`

CLOSES
* Item 2 / H2.  The chain is built from `horizonError`,
  `horizonCorrection`, `splitQuantileError`, and the committed spatial
  skeletons.  K08/K09/K12 are discharged by the landed bridge lemmas.
* The strong factor-one K13 estimate is recovered from
  `spatialDiscrepancy_eq_bridgePartial` and
  `abs_spatialBridgePartial_le`; the weaker factor-two public wrapper is not
  used.
* The K16 normal family is the endpoint coordinate followed by the ancestor
  split coordinates.  `treePathNoiseCoordinate_injective` proves that these
  are distinct, and the product-space law gives iid `N(0,1)`.

UNFINISHED
* Item 1 / H1 is absent.  The next file should union
  `gaussian_abs_tail_le` over raw coordinates satisfying
  `treeNoiseGeneration K i = some j`; this is the same cell event and has at
  most `2^K - 1` contributors.  The case `L > 2^K` is empty because every
  such `j` is below `K` and `dyadicLength K j ≤ 2^K`.
* Item 3 is absent until H1 is supplied and the `DyadicFiniteHorizonUnion`
  file is available for import.
END
-/

end Ripple.Kurtz.StrongApprox.DyadicTreePointTail

end
