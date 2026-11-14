-- Ripple/Kurtz/StrongApprox/DyadicPathChain.lean
import Mathlib
import Ripple.Kurtz.StrongApprox.DyadicBridgeError

noncomputable section

namespace Ripple.Kurtz.StrongApprox

open Set Finset
open scoped NNReal Nat BigOperators
open DyadicGaussianTree DyadicPoissonTree

/-! ## Reading all levels from one depth-`r+d` source -/

/-- Reassociate the horizon index without changing the source. -/
noncomputable def reassociateNoise (r d : ℕ)
    (x : DyadicNoiseSpace (r + (d + 1))) :
    DyadicNoiseSpace ((r + 1) + d) := by
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using x

/-- The level-`r` source extracted from a depth-`r+d` source.
This recursion exposes the next split at level `r` definitionally. -/
noncomputable def horizonNoise : (r d : ℕ) →
    DyadicNoiseSpace (r + d) → DyadicNoiseSpace r
  | r, 0 => fun x => by simpa using x
  | r, d + 1 => fun x =>
      (dyadicNoiseSplit r
        (horizonNoise (r + 1) d (reassociateNoise r d x))).1

/-- The level-`r+1` source immediately below a level-`r` parent. -/
noncomputable def horizonChildSource (r d : ℕ)
    (x : DyadicNoiseSpace (r + (d + 1))) :
    DyadicNoiseSpace (r + 1) :=
  horizonNoise (r + 1) d (reassociateNoise r d x)

@[simp] theorem horizonNoise_succ (r d : ℕ)
    (x : DyadicNoiseSpace (r + (d + 1))) :
    horizonNoise r (d + 1) x =
      (dyadicNoiseSplit r (horizonChildSource r d x)).1 := rfl

/-- Count of a level-`r` cell inside the common horizon tree. -/
def horizonCount (r d : ℕ) (x : DyadicNoiseSpace (r + d))
    (c : DyadicCell r) : ℕ :=
  poissonLevel (r + d) r (horizonNoise r d x) c

/-- Gaussian increment of the same cell. -/
def horizonGaussian (r d : ℕ) (x : DyadicNoiseSpace (r + d))
    (c : DyadicCell r) : ℝ :=
  gaussianLevel (r + d) r (horizonNoise r d x) c

/-- Bridge error of the same cell. -/
def horizonError (r d : ℕ) (x : DyadicNoiseSpace (r + d))
    (c : DyadicCell r) : ℝ :=
  bridgeError (r + d) r (horizonNoise r d x) c

/-- K12 correction attached to the split below this parent. -/
def horizonCorrection (r d : ℕ)
    (x : DyadicNoiseSpace (r + (d + 1))) (c : DyadicCell r) : ℝ :=
  bridgeCorrection ((r + 1) + d) r (horizonChildSource r d x) c

/-- K12 left identity on the common horizon source. -/
theorem horizonError_left (r d : ℕ)
    (x : DyadicNoiseSpace (r + (d + 1))) (c : DyadicCell r) :
    horizonError (r + 1) d (reassociateNoise r d x) (Sum.inl c) =
      horizonError r (d + 1) x c / 2 +
        horizonCorrection r d x c := by
  simpa [horizonError, horizonCorrection, horizonChildSource,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    bridgeError_left ((r + 1) + d) r (horizonChildSource r d x) c

/-- K12 right identity on the common horizon source. -/
theorem horizonError_right (r d : ℕ)
    (x : DyadicNoiseSpace (r + (d + 1))) (c : DyadicCell r) :
    horizonError (r + 1) d (reassociateNoise r d x) (Sum.inr c) =
      horizonError r (d + 1) x c / 2 -
        horizonCorrection r d x c := by
  simpa [horizonError, horizonCorrection, horizonChildSource,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    bridgeError_right ((r + 1) + d) r (horizonChildSource r d x) c

/-- A level-`r` cell in a horizon of depth `r+d` has integer length `2^d`. -/
theorem dyadicVariance_offset (r d : ℕ) :
    (dyadicVariance (r + d) r : ℝ) = (2 : ℝ) ^ d := by
  change (2 : ℝ) ^ (r + d) / (2 : ℝ) ^ r = (2 : ℝ) ^ d
  rw [pow_add]
  field_simp

/-! ## Spatial cell indexing from binary digits -/

/-- Descend from `c` according to the high-to-low binary digits of `j`.
Because `DyadicGaussianTree` stores a new branch in the outer `Sum`, the older/root bit is
inside and the newest/finer bit is outside. -/
def spatialDescendant : (r d : ℕ) →
    DyadicCell r → Fin (2 ^ d) → DyadicCell (r + d)
  | r, 0, c, _ => by simpa using c
  | r, d + 1, c, j =>
      if h : j.val < 2 ^ d then
        by
          have y := spatialDescendant (r + 1) d (Sum.inl c) ⟨j.val, h⟩
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using y
      else
        by
          have hj : j.val - 2 ^ d < 2 ^ d := by
            have hjTop : j.val < 2 ^ (d + 1) := j.isLt
            have h2 : 2 ^ (d + 1) = 2 * 2 ^ d := by ring
            omega
          have y := spatialDescendant (r + 1) d (Sum.inr c)
            ⟨j.val - 2 ^ d, hj⟩
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using y

/-- The leaf ending at integer time `t`; for `t=0` choose the first leaf.
For `t>0` its index is `t-1`. -/
def boundaryLeafIndex (d t : ℕ) (ht : t ≤ 2 ^ d) : Fin (2 ^ d) :=
  ⟨if t = 0 then 0 else t - 1, by
    split_ifs with hz
    · positivity
    · omega⟩

/-- The explicit boundary leaf in the landed recursive cell indexing. -/
def boundaryLeafCell (r d : ℕ) (c : DyadicCell r)
    (t : ℕ) (ht : t ≤ 2 ^ d) : DyadicCell (r + d) :=
  spatialDescendant r d c (boundaryLeafIndex d t ht)

/-- The first binary decision is exactly the high bit of `t-1`. -/
theorem boundaryLeafIndex_high_bit {d t : ℕ}
    (ht : t ≤ 2 ^ (d + 1)) (ht0 : 0 < t) :
    ((boundaryLeafIndex (d + 1) t ht).val < 2 ^ d) ↔
      t ≤ 2 ^ d := by
  simp [boundaryLeafIndex, Nat.ne_of_gt ht0]
  omega

/-- The ancestor chain selected by the binary digits of `t-1`.
At an exact midpoint it takes the last leaf of the left half. -/
def boundaryChain : (r d : ℕ) →
    DyadicCell r → ℕ → List (Σ s : ℕ, DyadicCell s)
  | r, 0, c, _ => [⟨r, c⟩]
  | r, d + 1, c, t =>
      ⟨r, c⟩ ::
        if t ≤ 2 ^ d then
          boundaryChain (r + 1) d (Sum.inl c) t
        else
          boundaryChain (r + 1) d (Sum.inr c) (t - 2 ^ d)

@[simp] theorem boundaryChain_length (r d : ℕ)
    (c : DyadicCell r) (t : ℕ) :
    (boundaryChain r d c t).length = d + 1 := by
  induction d generalizing r c t with
  | zero => simp [boundaryChain]
  | succ d ih =>
      by_cases h : t ≤ 2 ^ d <;> simp [boundaryChain, h, ih]

/-! ## Maximal dyadic cover of `[0,t]` -/

/-- Spatial maximal dyadic cells covering the first `t` unit leaves. -/
def dyadicInitialCover : (r d : ℕ) →
    DyadicCell r → ℕ → List (Σ s : ℕ, DyadicCell s)
  | r, 0, c, t => if t = 0 then [] else [⟨r, c⟩]
  | r, d + 1, c, t =>
      if t = 0 then []
      else if t = 2 ^ (d + 1) then [⟨r, c⟩]
      else if t ≤ 2 ^ d then
        dyadicInitialCover (r + 1) d (Sum.inl c) t
      else
        ⟨r + 1, Sum.inl c⟩ ::
          dyadicInitialCover (r + 1) d (Sum.inr c) (t - 2 ^ d)

/-- Every cell in a cover is at or below the starting level. -/
theorem dyadicInitialCover_scale_ge {r d t : ℕ} {c : DyadicCell r}
    {q : Σ s : ℕ, DyadicCell s}
    (hq : q ∈ dyadicInitialCover r d c t) : r ≤ q.1 := by
  induction d generalizing r c t q with
  | zero =>
      simp [dyadicInitialCover] at hq
      obtain ⟨_, rfl⟩ := hq
      exact le_rfl
  | succ d ih =>
      simp only [dyadicInitialCover] at hq
      split_ifs at hq with hz htop hhalf
      · contradiction
      · simp at hq
        rcases hq with rfl
        exact le_rfl
      · exact le_trans (Nat.le_succ r)
          (ih (r := r + 1) (c := Sum.inl c) hq)
      · simp at hq
        rcases hq with rfl | hq
        · exact Nat.le_succ r
        · exact le_trans (Nat.le_succ r)
            (ih (r := r + 1) (c := Sum.inr c) hq)

/-- A proper nonempty initial segment never uses the root cell. -/
theorem dyadicInitialCover_scale_gt {r d t : ℕ} {c : DyadicCell r}
    (ht0 : 0 < t) (htop : t < 2 ^ d)
    {q : Σ s : ℕ, DyadicCell s}
    (hq : q ∈ dyadicInitialCover r d c t) : r < q.1 := by
  cases d with
  | zero =>
      exfalso
      have : t < 1 := by simpa using htop
      omega
  | succ d =>
      simp only [dyadicInitialCover] at hq
      have hz : t ≠ 0 := Nat.ne_of_gt ht0
      have hfull : t ≠ 2 ^ (d + 1) := Nat.ne_of_lt htop
      by_cases hhalf : t ≤ 2 ^ d
      · simp [hz, hfull, hhalf] at hq
        exact lt_of_lt_of_le (Nat.lt_succ_self r)
          (dyadicInitialCover_scale_ge hq)
      · simp [hz, hfull, hhalf] at hq
        rcases hq with hq | hq
        · rw [hq]
          exact Nat.lt_succ_self r
        · exact lt_of_lt_of_le (Nat.lt_succ_self r)
            (dyadicInitialCover_scale_ge hq)

/-- Hence the maximal cover contains at most one cell at each scale. -/
theorem dyadicInitialCover_scales_nodup {r d t : ℕ}
    {c : DyadicCell r} (ht : t ≤ 2 ^ d) :
    ((dyadicInitialCover r d c t).map fun q => q.1).Nodup := by
  induction d generalizing r c t with
  | zero =>
      by_cases h : t = 0 <;> simp [dyadicInitialCover, h]
  | succ d ih =>
      by_cases hz : t = 0
      · simp [dyadicInitialCover, hz]
      by_cases htop : t = 2 ^ (d + 1)
      · simp [dyadicInitialCover, hz, htop]
      by_cases hhalf : t ≤ 2 ^ d
      · simpa [dyadicInitialCover, hz, htop, hhalf] using
          ih (r := r + 1) (c := Sum.inl c) (t := t) hhalf
      · have hhalfLe : 2 ^ d ≤ t := le_of_not_ge hhalf
        have hres0 : 0 < t - 2 ^ d := by omega
        have hresTop : t - 2 ^ d < 2 ^ d := by
          rw [pow_succ] at ht htop
          omega
        have hresLe : t - 2 ^ d ≤ 2 ^ d := hresTop.le
        have htail := ih (r := r + 1) (c := Sum.inr c)
          (t := t - 2 ^ d) hresLe
        rw [dyadicInitialCover]
        simp only [hz, htop, hhalf, if_false, List.map_cons,
          List.nodup_cons]
        refine ⟨?_, htail⟩
        intro hmem
        obtain ⟨q, hq, hscale⟩ := List.mem_map.mp hmem
        have hgt := dyadicInitialCover_scale_gt
          (r := r + 1) (d := d) hres0 hresTop hq
        have hscale' : q.1 = r + 1 := hscale
        omega

/-- The cover lengths sum to `t`. -/
theorem dyadicInitialCover_length_sum {r d t : ℕ}
    {c : DyadicCell r} (ht : t ≤ 2 ^ d) :
    ((dyadicInitialCover r d c t).map
      (fun q => 2 ^ ((r + d) - q.1))).sum = t := by
  induction d generalizing r c t with
  | zero =>
      have htCases : t = 0 ∨ t = 1 := by omega
      rcases htCases with rfl | rfl <;>
        simp [dyadicInitialCover]
  | succ d ih =>
      by_cases hz : t = 0
      · simp [dyadicInitialCover, hz]
      by_cases htop : t = 2 ^ (d + 1)
      · subst t
        simp [dyadicInitialCover, hz]
      by_cases hhalf : t ≤ 2 ^ d
      · have hrec := ih (r := r + 1) (c := Sum.inl c)
          (t := t) hhalf
        simpa [dyadicInitialCover, hz, htop, hhalf,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hrec
      · have hhalfLe : 2 ^ d ≤ t := le_of_not_ge hhalf
        have hresLe : t - 2 ^ d ≤ 2 ^ d := by
          rw [pow_succ] at ht htop
          omega
        have hrec := ih (r := r + 1) (c := Sum.inr c)
          (t := t - 2 ^ d) hresLe
        rw [dyadicInitialCover]
        simp only [hz, htop, hhalf, if_false, List.map_cons,
          List.sum_cons]
        have hpow :
            2 ^ ((r + (d + 1)) - (r + 1)) = 2 ^ d := by
          congr 1
          omega
        rw [hpow]
        have e : r + (d + 1) = r + 1 + d := by omega
        simp only [e]
        omega

/-! ## Spatial partial sums and their error cover -/

/-- Count in the first `t` spatial unit leaves of a subtree. -/
noncomputable def spatialPoissonPartial : (r d : ℕ) →
    DyadicNoiseSpace (r + d) → DyadicCell r → ℕ → ℕ
  | r, 0, x, c, t => if t = 0 then 0 else horizonCount r 0 x c
  | r, d + 1, x, c, t =>
      let child := reassociateNoise r d x
      if t ≤ 2 ^ d then
        spatialPoissonPartial (r + 1) d child (Sum.inl c) t
      else
        horizonCount (r + 1) d child (Sum.inl c) +
          spatialPoissonPartial (r + 1) d child (Sum.inr c)
            (t - 2 ^ d)

/-- Gaussian value at the same integer boundary. -/
noncomputable def spatialGaussianPartial : (r d : ℕ) →
    DyadicNoiseSpace (r + d) → DyadicCell r → ℕ → ℝ
  | r, 0, x, c, t => if t = 0 then 0 else horizonGaussian r 0 x c
  | r, d + 1, x, c, t =>
      let child := reassociateNoise r d x
      if t ≤ 2 ^ d then
        spatialGaussianPartial (r + 1) d child (Sum.inl c) t
      else
        horizonGaussian (r + 1) d child (Sum.inl c) +
          spatialGaussianPartial (r + 1) d child (Sum.inr c)
            (t - 2 ^ d)

/-- Sum of bridge errors over the maximal dyadic cover. -/
noncomputable def spatialBridgePartial : (r d : ℕ) →
    DyadicNoiseSpace (r + d) → DyadicCell r → ℕ → ℝ
  | r, 0, x, c, t => if t = 0 then 0 else horizonError r 0 x c
  | r, d + 1, x, c, t =>
      let child := reassociateNoise r d x
      if t ≤ 2 ^ d then
        spatialBridgePartial (r + 1) d child (Sum.inl c) t
      else
        horizonError (r + 1) d child (Sum.inl c) +
          spatialBridgePartial (r + 1) d child (Sum.inr c)
            (t - 2 ^ d)

/-- Exact discrepancy identity for the spatial skeleton. -/
theorem spatialDiscrepancy_eq_bridgePartial :
    ∀ (r d : ℕ) (x : DyadicNoiseSpace (r + d))
      (c : DyadicCell r) (t : ℕ), t ≤ 2 ^ d →
      (spatialPoissonPartial r d x c t : ℝ) - (t : ℝ) -
          spatialGaussianPartial r d x c t =
        spatialBridgePartial r d x c t := by
  intro r d
  induction d generalizing r with
  | zero =>
      intro x c t ht
      have htCases : t = 0 ∨ t = 1 := by omega
      rcases htCases with rfl | rfl
      · simp [spatialPoissonPartial, spatialGaussianPartial,
          spatialBridgePartial]
      · simp [spatialPoissonPartial, spatialGaussianPartial,
          spatialBridgePartial, horizonError, bridgeError,
          horizonCount, horizonGaussian, dyadicVariance_offset]
  | succ d ih =>
      intro x c t ht
      let child := reassociateNoise r d x
      by_cases hleft : t ≤ 2 ^ d
      · simpa [spatialPoissonPartial, spatialGaussianPartial,
          spatialBridgePartial, child, hleft] using
          ih (r := r + 1) child (Sum.inl c) t hleft
      · have hhalf : 2 ^ d ≤ t := le_of_not_ge hleft
        have hres : t - 2 ^ d ≤ 2 ^ d := by
          rw [pow_succ] at ht
          omega
        have hrec := ih (r := r + 1) child (Sum.inr c)
          (t - 2 ^ d) hres
        have hv := dyadicVariance_offset (r + 1) d
        have hfull :
            (horizonCount (r + 1) d child (Sum.inl c) : ℝ) -
                (2 ^ d : ℕ) -
                horizonGaussian (r + 1) d child (Sum.inl c) =
              horizonError (r + 1) d child (Sum.inl c) := by
          unfold horizonError bridgeError horizonCount horizonGaussian
          rw [hv]
          push_cast
          ring
        rw [spatialPoissonPartial, spatialGaussianPartial,
          spatialBridgePartial]
        simp only [child, hleft, if_false]
        simp only [child] at hrec hfull
        push_cast at hrec hfull ⊢
        have htDecomp : (t : ℝ) = (2 ^ d : ℝ) + (t - 2 ^ d : ℕ) := by
          exact_mod_cast (Nat.add_sub_of_le hhalf).symm
        linarith [hfull, hrec, htDecomp]

/-! ## One correction per ancestor -/

/-- Sum of `|g|` along the explicit binary ancestor chain. -/
noncomputable def boundaryCorrectionAbs : (r d : ℕ) →
    DyadicNoiseSpace (r + d) → DyadicCell r → ℕ → ℝ
  | _, 0, _, _, _ => 0
  | r, d + 1, x, c, t =>
      let child := reassociateNoise r d x
      |horizonCorrection r d x c| +
        if t ≤ 2 ^ d then
          boundaryCorrectionAbs (r + 1) d child (Sum.inl c) t
        else
          boundaryCorrectionAbs (r + 1) d child (Sum.inr c)
            (t - 2 ^ d)

/-- Exact affine form behind the path-chain estimate.
The coefficient is the fraction of this subtree covered by `[0,t]`. -/
theorem spatialBridgePartial_affine :
    ∀ (r d : ℕ) (x : DyadicNoiseSpace (r + d))
      (c : DyadicCell r) (t : ℕ), t ≤ 2 ^ d →
      ∃ a : ℝ, 0 ≤ a ∧ a ≤ 1 ∧
        |spatialBridgePartial r d x c t - a * horizonError r d x c| ≤
          boundaryCorrectionAbs r d x c t := by
  intro r d
  induction d generalizing r with
  | zero =>
      intro x c t ht
      have htCases : t = 0 ∨ t = 1 := by omega
      rcases htCases with rfl | rfl
      · refine ⟨0, by norm_num, by norm_num, ?_⟩
        simp [spatialBridgePartial, boundaryCorrectionAbs]
      · refine ⟨1, by norm_num, by norm_num, ?_⟩
        simp [spatialBridgePartial, boundaryCorrectionAbs]
  | succ d ih =>
      intro x c t ht
      let child := reassociateNoise r d x
      by_cases hleft : t ≤ 2 ^ d
      · obtain ⟨a, ha0, ha1, ha⟩ :=
          ih (r := r + 1) child (Sum.inl c) t hleft
        refine ⟨a / 2, by positivity, by linarith, ?_⟩
        have hchild := horizonError_left r d x c
        calc
          |spatialBridgePartial r (d + 1) x c t -
              (a / 2) * horizonError r (d + 1) x c| =
              |(spatialBridgePartial (r + 1) d child (Sum.inl c) t -
                  a * horizonError (r + 1) d child (Sum.inl c)) +
                a * horizonCorrection r d x c| := by
                    simp [spatialBridgePartial, child, hleft]
                    rw [hchild]
                    congr 1
                    ring
          _ ≤ |spatialBridgePartial (r + 1) d child (Sum.inl c) t -
                  a * horizonError (r + 1) d child (Sum.inl c)| +
                |a * horizonCorrection r d x c| := abs_add_le _ _
          _ ≤ boundaryCorrectionAbs (r + 1) d child (Sum.inl c) t +
                |horizonCorrection r d x c| := by
              rw [abs_mul, abs_of_nonneg ha0]
              have hag : a * |horizonCorrection r d x c| ≤
                  |horizonCorrection r d x c| := by
                exact mul_le_of_le_one_left (abs_nonneg _) ha1
              linarith
          _ = boundaryCorrectionAbs r (d + 1) x c t := by
              simp [boundaryCorrectionAbs, child, hleft, add_comm]
      · have hhalf : 2 ^ d ≤ t := le_of_not_ge hleft
        have hres : t - 2 ^ d ≤ 2 ^ d := by
          rw [pow_succ] at ht
          omega
        obtain ⟨a, ha0, ha1, ha⟩ :=
          ih (r := r + 1) child (Sum.inr c) (t - 2 ^ d) hres
        refine ⟨(1 + a) / 2, by positivity, by linarith, ?_⟩
        have hleftError := horizonError_left r d x c
        have hrightError := horizonError_right r d x c
        calc
          |spatialBridgePartial r (d + 1) x c t -
              ((1 + a) / 2) * horizonError r (d + 1) x c| =
              |(spatialBridgePartial (r + 1) d child (Sum.inr c)
                    (t - 2 ^ d) -
                  a * horizonError (r + 1) d child (Sum.inr c)) +
                (1 - a) * horizonCorrection r d x c| := by
                    simp [spatialBridgePartial, child, hleft]
                    rw [hleftError, hrightError]
                    congr 1
                    ring
          _ ≤ |spatialBridgePartial (r + 1) d child (Sum.inr c)
                    (t - 2 ^ d) -
                  a * horizonError (r + 1) d child (Sum.inr c)| +
                |(1 - a) * horizonCorrection r d x c| := abs_add_le _ _
          _ ≤ boundaryCorrectionAbs (r + 1) d child (Sum.inr c)
                  (t - 2 ^ d) + |horizonCorrection r d x c| := by
              rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr ha1)]
              have hag : (1 - a) * |horizonCorrection r d x c| ≤
                  |horizonCorrection r d x c| := by
                apply mul_le_of_le_one_left (abs_nonneg _)
                linarith
              linarith
          _ = boundaryCorrectionAbs r (d + 1) x c t := by
              simp [boundaryCorrectionAbs, child, hleft, add_comm]

/-- Strong form of K13: the constants can be one rather than two. -/
theorem abs_spatialBridgePartial_le (r d : ℕ)
    (x : DyadicNoiseSpace (r + d)) (c : DyadicCell r)
    {t : ℕ} (ht : t ≤ 2 ^ d) :
    |spatialBridgePartial r d x c t| ≤
      |horizonError r d x c| + boundaryCorrectionAbs r d x c t := by
  obtain ⟨a, ha0, ha1, ha⟩ :=
    spatialBridgePartial_affine r d x c t ht
  have haD : |a * horizonError r d x c| ≤ |horizonError r d x c| := by
    rw [abs_mul, abs_of_nonneg ha0]
    exact mul_le_of_le_one_left (abs_nonneg _) ha1
  have hdecomp :
      spatialBridgePartial r d x c t =
        (spatialBridgePartial r d x c t - a * horizonError r d x c) +
          a * horizonError r d x c := by ring
  rw [hdecomp]
  have hfin := (abs_add_le (spatialBridgePartial r d x c t - a * horizonError r d x c)
    (a * horizonError r d x c)).trans (add_le_add ha haD)
  linarith

theorem boundaryCorrectionAbs_nonneg :
    ∀ (r d : ℕ) (x : DyadicNoiseSpace (r + d)) (c : DyadicCell r) (t : ℕ),
      0 ≤ boundaryCorrectionAbs r d x c t
  | r, 0, x, c, t => by simp [boundaryCorrectionAbs]
  | r, d + 1, x, c, t => by
      simp only [boundaryCorrectionAbs]
      apply add_nonneg (abs_nonneg _)
      split_ifs
      · exact boundaryCorrectionAbs_nonneg _ _ _ _ _
      · exact boundaryCorrectionAbs_nonneg _ _ _ _ _

/-- The factors with constants two. -/
theorem abs_spatialBridgePartial_le_requested (r d : ℕ)
    (x : DyadicNoiseSpace (r + d)) (c : DyadicCell r)
    {t : ℕ} (ht : t ≤ 2 ^ d) :
    |spatialBridgePartial r d x c t| ≤
      2 * |horizonError r d x c| +
        2 * boundaryCorrectionAbs r d x c t := by
  have h := abs_spatialBridgePartial_le r d x c ht
  have hD := abs_nonneg (horizonError r d x c)
  have hg := boundaryCorrectionAbs_nonneg r d x c t
  linarith

/-! ## Geometrically weighted error of the boundary leaf -/

/-- Error of the leaf selected by the binary boundary chain. -/
noncomputable def boundaryLeafError : (r d : ℕ) →
    DyadicNoiseSpace (r + d) → DyadicCell r → ℕ → ℝ
  | r, 0, x, c, _ => horizonError r 0 x c
  | r, d + 1, x, c, t =>
      let child := reassociateNoise r d x
      if t ≤ 2 ^ d then
        boundaryLeafError (r + 1) d child (Sum.inl c) t
      else
        boundaryLeafError (r + 1) d child (Sum.inr c) (t - 2 ^ d)

/-- Explicit geometric weights generated by iterating K12. -/
noncomputable def geometricCorrectionAbs : (r d : ℕ) →
    DyadicNoiseSpace (r + d) → DyadicCell r → ℕ → ℝ
  | _, 0, _, _, _ => 0
  | r, d + 1, x, c, t =>
      (1 / 2 : ℝ) ^ d * |horizonCorrection r d x c| +
        let child := reassociateNoise r d x
        if t ≤ 2 ^ d then
          geometricCorrectionAbs (r + 1) d child (Sum.inl c) t
        else
          geometricCorrectionAbs (r + 1) d child (Sum.inr c)
            (t - 2 ^ d)

/-- Exact geometric-weight inequality along the ancestor chain. -/
theorem boundaryLeafError_geometric :
    ∀ (r d : ℕ) (x : DyadicNoiseSpace (r + d))
      (c : DyadicCell r) (t : ℕ),
      |boundaryLeafError r d x c t| ≤
        (1 / 2 : ℝ) ^ d * |horizonError r d x c| +
          geometricCorrectionAbs r d x c t := by
  intro r d
  induction d generalizing r with
  | zero =>
      intro x c t
      simp [boundaryLeafError, geometricCorrectionAbs]
  | succ d ih =>
      intro x c t
      let child := reassociateNoise r d x
      by_cases hleft : t ≤ 2 ^ d
      · have hrec := ih (r := r + 1) child (Sum.inl c) t
        have hchild := horizonError_left r d x c
        have habs :
            |horizonError (r + 1) d child (Sum.inl c)| ≤
              |horizonError r (d + 1) x c| / 2 +
                |horizonCorrection r d x c| := by
          rw [hchild]
          exact (abs_add_le _ _).trans_eq (by rw [abs_div]; norm_num)
        calc
          |boundaryLeafError r (d + 1) x c t| ≤
              (1 / 2 : ℝ) ^ d *
                  |horizonError (r + 1) d child (Sum.inl c)| +
                geometricCorrectionAbs (r + 1) d child (Sum.inl c) t := by
              simpa [boundaryLeafError, child, hleft] using hrec
          _ ≤ (1 / 2 : ℝ) ^ d *
                  (|horizonError r (d + 1) x c| / 2 +
                    |horizonCorrection r d x c|) +
                geometricCorrectionAbs (r + 1) d child (Sum.inl c) t := by
              gcongr
          _ = (1 / 2 : ℝ) ^ (d + 1) *
                  |horizonError r (d + 1) x c| +
                geometricCorrectionAbs r (d + 1) x c t := by
              simp [geometricCorrectionAbs, child, hleft, pow_succ]
              ring
      · have hrec := ih (r := r + 1) child (Sum.inr c) (t - 2 ^ d)
        have hchild := horizonError_right r d x c
        have habs :
            |horizonError (r + 1) d child (Sum.inr c)| ≤
              |horizonError r (d + 1) x c| / 2 +
                |horizonCorrection r d x c| := by
          rw [hchild]
          have h := abs_sub (horizonError r (d + 1) x c / 2)
            (horizonCorrection r d x c)
          rw [abs_div, abs_two] at h
          exact h
        calc
          |boundaryLeafError r (d + 1) x c t| ≤
              (1 / 2 : ℝ) ^ d *
                  |horizonError (r + 1) d child (Sum.inr c)| +
                geometricCorrectionAbs (r + 1) d child (Sum.inr c)
                  (t - 2 ^ d) := by
              simpa [boundaryLeafError, child, hleft] using hrec
          _ ≤ (1 / 2 : ℝ) ^ d *
                  (|horizonError r (d + 1) x c| / 2 +
                    |horizonCorrection r d x c|) +
                geometricCorrectionAbs (r + 1) d child (Sum.inr c)
                  (t - 2 ^ d) := by
              gcongr
          _ = (1 / 2 : ℝ) ^ (d + 1) *
                  |horizonError r (d + 1) x c| +
                geometricCorrectionAbs r (d + 1) x c t := by
              simp [geometricCorrectionAbs, child, hleft, pow_succ]
              ring

/-! ## Root wrappers and the exact missing adapter -/

/-- A depth-`K` source viewed at the index `0 + K` expected by the horizon
definitions.  (`0 + K` is not definitionally `K`; the delivered statements
applied `x : DyadicNoiseSpace K` directly, which is ill-typed.) -/
def rootSource (K : ℕ) (x : DyadicNoiseSpace K) : DyadicNoiseSpace (0 + K) :=
  cast (by rw [Nat.zero_add]) x

/-- Spatially ordered Poisson integer skeleton. -/
def spatialPoissonSkeleton (K : ℕ) (x : DyadicNoiseSpace K)
    (t : ℕ) : ℕ :=
  spatialPoissonPartial 0 K (rootSource K x) () t

/-- Spatially ordered Gaussian integer skeleton. -/
def spatialGaussianSkeleton (K : ℕ) (x : DyadicNoiseSpace K)
    (t : ℕ) : ℝ :=
  spatialGaussianPartial 0 K (rootSource K x) () t

/-- Unconditional corrected K13. -/
theorem spatialSkeleton_path_chain (K : ℕ)
    (x : DyadicNoiseSpace K) {t : ℕ} (ht : t ≤ 2 ^ K) :
    |(spatialPoissonSkeleton K x t : ℝ) - (t : ℝ) -
        spatialGaussianSkeleton K x t| ≤
      2 * |horizonError 0 K (rootSource K x) ()| +
        2 * boundaryCorrectionAbs 0 K (rootSource K x) () t := by
  rw [spatialPoissonSkeleton, spatialGaussianSkeleton,
    spatialDiscrepancy_eq_bridgePartial 0 K (rootSource K x) () t ht]
  exact abs_spatialBridgePartial_le_requested 0 K (rootSource K x) () ht

/-- K13 with the K08 root bound substituted. -/
theorem spatialSkeleton_path_chain_with_root (K : ℕ)
    (x : DyadicNoiseSpace K) {t : ℕ} (ht : t ≤ 2 ^ K) :
    |(spatialPoissonSkeleton K x t : ℝ) - (t : ℝ) -
        spatialGaussianSkeleton K x t| ≤
      2 * (1 + 2 * ((horizonNoise 0 K (rootSource K x)) ()) ^ 2) +
        2 * boundaryCorrectionAbs 0 K (rootSource K x) () t := by
  have hchain := spatialSkeleton_path_chain K x ht
  have hroot := root_bridgeError_le (0 + K) (horizonNoise 0 K (rootSource K x)) ()
  have hr : |horizonError 0 K (rootSource K x) ()| ≤
      1 + 2 * ((horizonNoise 0 K (rootSource K x)) ()) ^ 2 := hroot
  linarith

/-- Natural leaf-order condition not supplied by the dyadic tree construction. -/
def SpatialLeafOrderAgreement (K : ℕ) : Prop :=
  ∀ j : Fin (2 ^ K),
    dyadicLeafCell K j =
      cast (by rw [Nat.zero_add]) (spatialDescendant 0 K () j)

/-- Exact condition needed to transfer the corrected theorem to the two landed
integer skeleton definitions. -/
def LandedSkeletonSpatialAgreement (K : ℕ) : Prop :=
  ∀ (x : DyadicNoiseSpace K) (t : ℕ), t ≤ 2 ^ K →
    poissonSkeleton K x t = spatialPoissonSkeleton K x t ∧
      gaussianSkeleton K x t = spatialGaussianSkeleton K x t

/-- Requested K13 for the landed skeletons, under the exact missing condition. -/
theorem landedSkeleton_path_chain (K : ℕ)
    (horder : LandedSkeletonSpatialAgreement K)
    (x : DyadicNoiseSpace K) {t : ℕ} (ht : t ≤ 2 ^ K) :
    |(poissonSkeleton K x t : ℝ) - (t : ℝ) -
        gaussianSkeleton K x t| ≤
      2 * |horizonError 0 K (rootSource K x) ()| +
        2 * boundaryCorrectionAbs 0 K (rootSource K x) () t := by
  obtain ⟨hY, hW⟩ := horder x t ht
  rw [hY, hW]
  exact spatialSkeleton_path_chain K x ht

/-!
THEOREM LIST
* `horizonError_left`, `horizonError_right`, `dyadicVariance_offset`
* `spatialDescendant`, `boundaryLeafIndex`, `boundaryLeafCell`
* `boundaryLeafIndex_high_bit`, `boundaryChain`, `boundaryChain_length`
* `dyadicInitialCover`, `dyadicInitialCover_scales_nodup`
* `dyadicInitialCover_length_sum`
* `spatialDiscrepancy_eq_bridgePartial`
* `spatialBridgePartial_affine`
* `abs_spatialBridgePartial_le`, `abs_spatialBridgePartial_le_requested`
* `boundaryLeafError_geometric`
* `spatialSkeleton_path_chain`, `spatialSkeleton_path_chain_with_root`
* `SpatialLeafOrderAgreement`, `LandedSkeletonSpatialAgreement`
* `landedSkeleton_path_chain`

CLOSES K13, CORRECTED
* Explicit high-to-low binary ancestor chain in the recursive cell indexing of `DyadicGaussianTree`.
* Maximal dyadic cover, with at most one cell per scale and total length `t`.
* Geometrically weighted iteration of K12 down the boundary chain.
* Strong spatial estimate with constants one, hence the requested constants two.
* Exact conditional adapter to the landed skeleton names.

UNFINISHED
* The unconditional theorem for the current landed `poissonSkeleton` and
  `gaussianSkeleton` is intentionally absent: the dyadic tree construction uses an arbitrary
  `Fintype.equivFin` leaf enumeration and supplies neither
  `SpatialLeafOrderAgreement` nor `LandedSkeletonSpatialAgreement`.
* K14 and K15 are outside this round.
END
-/

end Ripple.Kurtz.StrongApprox

end
