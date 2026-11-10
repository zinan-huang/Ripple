import Ripple.Number.Modular.ModularPoly41
import Mathlib.RingTheory.PowerSeries.Substitution

/-!
# Coefficient majorants for integer power series

A priori bounds on the coefficients of polynomial expressions in integer power series, used to
turn a Kronecker-packed evaluation that vanishes into vanishing coefficients (the packed value
determines a coefficient only when it is below the slot size).

* `CoeffDom f g`: `g` has nonnegative coefficients and `|coeff n f| ≤ coeff n g` for all `n`.
  Closed under sums, products, powers, integer multiples (with `|c|`), substitution `q ↦ q^d`, and
  the cleared sparse bivariate evaluation (`coeffDom_evalSparseBivarCleared`, with `|c|` in place
  of every coefficient).
* `wsum r N g = Σ_{m<N} coeff m g · r^m` for `0 ≤ r`: submultiplicative on series with
  nonnegative coefficients (`wsum_mul_le`), and `coeff n g · r^n ≤ wsum r N g` for `n < N`.
-/

namespace Ripple.Number.Modular

open PowerSeries Finset

/-- `g` has nonnegative coefficients. -/
def CoeffNonneg (g : PowerSeries ℤ) : Prop := ∀ n, 0 ≤ coeff n g

/-- `g` dominates `f` coefficientwise. -/
def CoeffDom (f g : PowerSeries ℤ) : Prop := CoeffNonneg g ∧ ∀ n, |coeff n f| ≤ coeff n g

section Dom

variable {f g f₁ f₂ g₁ g₂ : PowerSeries ℤ}

theorem coeffNonneg_zero : CoeffNonneg 0 := fun n => by simp

theorem coeffNonneg_one : CoeffNonneg 1 := fun n => by
  rw [coeff_one]
  split_ifs <;> norm_num

theorem CoeffNonneg.add (h₁ : CoeffNonneg g₁) (h₂ : CoeffNonneg g₂) : CoeffNonneg (g₁ + g₂) :=
  fun n => by rw [map_add]; exact add_nonneg (h₁ n) (h₂ n)

theorem CoeffNonneg.mul (h₁ : CoeffNonneg g₁) (h₂ : CoeffNonneg g₂) : CoeffNonneg (g₁ * g₂) :=
  fun n => by
    rw [coeff_mul]
    exact sum_nonneg fun p _ => mul_nonneg (h₁ _) (h₂ _)

theorem CoeffNonneg.pow (h : CoeffNonneg g) : ∀ k : ℕ, CoeffNonneg (g ^ k)
  | 0 => by rw [pow_zero]; exact coeffNonneg_one
  | k + 1 => by rw [pow_succ]; exact (CoeffNonneg.pow h k).mul h

theorem CoeffNonneg.zsmul {c : ℤ} (hc : 0 ≤ c) (h : CoeffNonneg g) : CoeffNonneg (c • g) :=
  fun n => by rw [map_zsmul, smul_eq_mul]; exact mul_nonneg hc (h n)

theorem coeffNonneg_intCast {c : ℤ} (hc : 0 ≤ c) : CoeffNonneg (c : PowerSeries ℤ) := by
  have h : (c : PowerSeries ℤ) = c • (1 : PowerSeries ℤ) := by rw [zsmul_eq_mul, mul_one]
  rw [h]
  exact coeffNonneg_one.zsmul hc

theorem coeffDom_of_nonneg (h : CoeffNonneg g) : CoeffDom g g :=
  ⟨h, fun n => (abs_of_nonneg (h n)).le⟩

theorem CoeffDom.add (h₁ : CoeffDom f₁ g₁) (h₂ : CoeffDom f₂ g₂) :
    CoeffDom (f₁ + f₂) (g₁ + g₂) :=
  ⟨h₁.1.add h₂.1, fun n => by
    rw [map_add, map_add]
    exact (abs_add_le _ _).trans (add_le_add (h₁.2 n) (h₂.2 n))⟩

theorem CoeffDom.mul (h₁ : CoeffDom f₁ g₁) (h₂ : CoeffDom f₂ g₂) :
    CoeffDom (f₁ * f₂) (g₁ * g₂) :=
  ⟨h₁.1.mul h₂.1, fun n => by
    rw [coeff_mul, coeff_mul]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun p _ => ?_)
    rw [abs_mul]
    exact mul_le_mul (h₁.2 _) (h₂.2 _) (abs_nonneg _) (h₁.1 _)⟩

theorem CoeffDom.pow (h : CoeffDom f g) : ∀ k : ℕ, CoeffDom (f ^ k) (g ^ k)
  | 0 => by rw [pow_zero, pow_zero]; exact coeffDom_of_nonneg coeffNonneg_one
  | k + 1 => by rw [pow_succ, pow_succ]; exact (CoeffDom.pow h k).mul h

theorem CoeffDom.zsmul (c : ℤ) (h : CoeffDom f g) : CoeffDom (c • f) ((|c| : ℤ) • g) :=
  ⟨h.1.zsmul (abs_nonneg c), fun n => by
    rw [map_zsmul, map_zsmul, smul_eq_mul, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (h.2 n) (abs_nonneg c)⟩

theorem coeffDom_intCast (c : ℤ) : CoeffDom (c : PowerSeries ℤ) ((|c| : ℤ) : PowerSeries ℤ) := by
  have h : ∀ a : ℤ, (a : PowerSeries ℤ) = a • (1 : PowerSeries ℤ) := fun a => by
    rw [zsmul_eq_mul, mul_one]
  rw [h c, h |c|]
  exact (coeffDom_of_nonneg coeffNonneg_one).zsmul c

/-- `q ↦ q^d` on integer series. -/
noncomputable def qSubstZ (d : ℕ) (f : PowerSeries ℤ) : PowerSeries ℤ :=
  PowerSeries.subst ((PowerSeries.X : PowerSeries ℤ) ^ d) f

theorem coeff_qSubstZ {d : ℕ} (hd : d ≠ 0) (f : PowerSeries ℤ) (n : ℕ) :
    coeff n (qSubstZ d f) = if d ∣ n then coeff (n / d) f else 0 := by
  simp [qSubstZ, PowerSeries.coeff_subst_X_pow (R := ℤ) (S := ℤ) hd f n]

theorem CoeffNonneg.qSubstZ {d : ℕ} (hd : d ≠ 0) (h : CoeffNonneg g) :
    CoeffNonneg (qSubstZ d g) := fun n => by
  rw [coeff_qSubstZ hd]
  split_ifs
  · exact h _
  · exact le_rfl

theorem CoeffDom.qSubstZ {d : ℕ} (hd : d ≠ 0) (h : CoeffDom f g) :
    CoeffDom (qSubstZ d f) (qSubstZ d g) :=
  ⟨h.1.qSubstZ hd, fun n => by
    rw [coeff_qSubstZ hd, coeff_qSubstZ hd]
    split_ifs
    · exact h.2 _
    · simp⟩

/-- The terms with every coefficient replaced by its absolute value. -/
def absTerms (terms : List SparseBivarTerm) : List SparseBivarTerm :=
  terms.map fun t => ⟨|t.coeff|, t.xPow, t.yPow⟩

theorem absTerms_cons (t : SparseBivarTerm) (ts : List SparseBivarTerm) :
    absTerms (t :: ts) = ⟨|t.coeff|, t.xPow, t.yPow⟩ :: absTerms ts := rfl

theorem coeffDom_evalSparseBivarCleared (xMax yMax : ℕ) {a b c d A B C D : PowerSeries ℤ}
    (ha : CoeffDom a A) (hb : CoeffDom b B) (hc : CoeffDom c C) (hd : CoeffDom d D) :
    ∀ terms : List SparseBivarTerm,
      CoeffDom (evalSparseBivarCleared terms xMax yMax a b c d)
        (evalSparseBivarCleared (absTerms terms) xMax yMax A B C D)
  | [] => by
      simpa [evalSparseBivarCleared, absTerms] using coeffDom_of_nonneg coeffNonneg_zero
  | t :: ts => by
      have hrest := coeffDom_evalSparseBivarCleared xMax yMax ha hb hc hd ts
      have hhead := ((((coeffDom_intCast t.coeff).mul (ha.pow t.xPow)).mul
        (hb.pow (xMax - t.xPow))).mul (hc.pow t.yPow)).mul (hd.pow (yMax - t.yPow))
      rw [absTerms_cons]
      exact hhead.add hrest

end Dom

/-! ### Weighted coefficient sums -/

section Weighted

/-- `Σ_{m<N} coeff m g · r^m`. -/
noncomputable def wsum (r : ℝ) (N : ℕ) (g : PowerSeries ℤ) : ℝ :=
  ∑ m ∈ range N, ((coeff m g : ℤ) : ℝ) * r ^ m

variable {r : ℝ} {N : ℕ} {g g₁ g₂ : PowerSeries ℤ}

theorem wsum_nonneg (hr : 0 ≤ r) (hg : CoeffNonneg g) : 0 ≤ wsum r N g :=
  sum_nonneg fun m _ => mul_nonneg (by exact_mod_cast hg m) (pow_nonneg hr m)

theorem wsum_add : wsum r N (g₁ + g₂) = wsum r N g₁ + wsum r N g₂ := by
  simp only [wsum, map_add, Int.cast_add, add_mul, sum_add_distrib]

theorem wsum_zsmul (c : ℤ) : wsum r N (c • g) = c * wsum r N g := by
  simp only [wsum, map_zsmul, smul_eq_mul, Int.cast_mul, mul_sum, mul_assoc]

theorem wsum_one_le : wsum r N 1 ≤ 1 := by
  rcases N with _ | N
  · simp [wsum]
  · rw [wsum, sum_range_succ']
    have h0 : ∀ m ∈ range N,
        ((coeff (m + 1) (1 : PowerSeries ℤ) : ℤ) : ℝ) * r ^ (m + 1) = 0 := fun m _ => by
      simp [coeff_one]
    rw [sum_eq_zero h0]
    simp [coeff_one]

theorem wsum_intCast (c : ℤ) (hc : 0 ≤ c) : wsum r N (c : PowerSeries ℤ) ≤ c := by
  have h : (c : PowerSeries ℤ) = c • (1 : PowerSeries ℤ) := by rw [zsmul_eq_mul, mul_one]
  rw [h, wsum_zsmul]
  calc (c : ℝ) * wsum r N 1 ≤ (c : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left wsum_one_le (by exact_mod_cast hc)
    _ = c := mul_one _

/-- Truncated weighted sums are submultiplicative on series with nonnegative coefficients. -/
theorem wsum_mul_le (hr : 0 ≤ r) (h₁ : CoeffNonneg g₁) (h₂ : CoeffNonneg g₂) :
    wsum r N (g₁ * g₂) ≤ wsum r N g₁ * wsum r N g₂ := by
  set a : ℕ → ℝ := fun i => ((coeff i g₁ : ℤ) : ℝ) * r ^ i with ha
  set b : ℕ → ℝ := fun j => ((coeff j g₂ : ℤ) : ℝ) * r ^ j with hb
  have ha0 : ∀ i, 0 ≤ a i := fun i => mul_nonneg (by exact_mod_cast h₁ i) (pow_nonneg hr i)
  have hb0 : ∀ j, 0 ≤ b j := fun j => mul_nonneg (by exact_mod_cast h₂ j) (pow_nonneg hr j)
  have hL : wsum r N (g₁ * g₂) =
      ∑ m ∈ range N, ∑ k ∈ range (m + 1), a k * b (m - k) := by
    refine sum_congr rfl fun m _ => ?_
    rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Int.cast_sum, sum_mul]
    refine sum_congr rfl fun k hk => ?_
    have hkm : k ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hk)
    simp only [ha, hb, Int.cast_mul]
    rw [show r ^ m = r ^ k * r ^ (m - k) by rw [← pow_add, Nat.add_sub_cancel' hkm]]
    ring
  have hswap : ∑ m ∈ range N, ∑ k ∈ range (m + 1), a k * b (m - k) =
      ∑ k ∈ range N, ∑ j ∈ range (N - k), a k * b j := by
    rw [sum_sigma', sum_sigma']
    refine sum_nbij' (fun p => ⟨p.2, p.1 - p.2⟩) (fun p => ⟨p.1 + p.2, p.1⟩) ?_ ?_ ?_ ?_ ?_
    · rintro ⟨m, k⟩ h
      simp only [mem_sigma, mem_range] at h ⊢
      omega
    · rintro ⟨k, j⟩ h
      simp only [mem_sigma, mem_range] at h ⊢
      omega
    · rintro ⟨m, k⟩ h
      simp only [mem_sigma, mem_range] at h
      change (⟨k + (m - k), k⟩ : Σ _ : ℕ, ℕ) = ⟨m, k⟩
      rw [Nat.add_sub_cancel' (by omega)]
    · rintro ⟨k, j⟩ _
      change (⟨k, k + j - k⟩ : Σ _ : ℕ, ℕ) = ⟨k, j⟩
      rw [Nat.add_sub_cancel_left]
    · rintro ⟨m, k⟩ _
      rfl
  have hR : wsum r N g₁ * wsum r N g₂ = ∑ k ∈ range N, ∑ j ∈ range N, a k * b j := by
    rw [wsum, wsum, sum_mul_sum]
  rw [hL, hswap, hR]
  refine sum_le_sum fun k _ => sum_le_sum_of_subset_of_nonneg
    (range_subset_range.mpr (Nat.sub_le N k)) fun j _ _ => mul_nonneg (ha0 k) (hb0 j)

theorem wsum_pow_le (hr : 0 ≤ r) (hg : CoeffNonneg g) :
    ∀ k : ℕ, wsum r N (g ^ k) ≤ wsum r N g ^ k
  | 0 => by rw [pow_zero, pow_zero]; exact wsum_one_le
  | k + 1 => by
      rw [pow_succ, pow_succ]
      exact (wsum_mul_le hr (hg.pow k) hg).trans
        (mul_le_mul_of_nonneg_right (wsum_pow_le hr hg k) (wsum_nonneg hr hg))

/-- `wsum` after `q ↦ q^d` is at most `wsum` at `r^d`. -/
theorem wsum_qSubstZ_le (hr : 0 ≤ r) {d : ℕ} (hd : d ≠ 0) (hg : CoeffNonneg g) :
    wsum r N (qSubstZ d g) ≤ wsum (r ^ d) N g := by
  classical
  have hd0 : 0 < d := Nat.pos_of_ne_zero hd
  set s := (range N).filter (fun m => d ∣ m) with hs
  have h1 : wsum r N (qSubstZ d g) = ∑ m ∈ s, ((coeff (m / d) g : ℤ) : ℝ) * r ^ m := by
    rw [wsum, hs, sum_filter]
    refine sum_congr rfl fun m _ => ?_
    rw [coeff_qSubstZ hd]
    split_ifs <;> simp
  have hinj : ∀ x ∈ s, ∀ y ∈ s, x / d = y / d → x = y := by
    intro x hx y hy hxy
    simp only [hs, mem_filter] at hx hy
    rw [← Nat.div_mul_cancel hx.2, ← Nat.div_mul_cancel hy.2, hxy]
  have h2 : ∑ m ∈ s, ((coeff (m / d) g : ℤ) : ℝ) * r ^ m =
      ∑ j ∈ s.image (· / d), ((coeff j g : ℤ) : ℝ) * (r ^ d) ^ j := by
    rw [sum_image hinj]
    refine sum_congr rfl fun m hm => ?_
    dsimp only
    simp only [hs, mem_filter] at hm
    rw [← pow_mul, Nat.mul_div_cancel' hm.2]
  have hsub : s.image (· / d) ⊆ range N := by
    intro j hj
    simp only [mem_image, hs, mem_filter, mem_range] at hj ⊢
    obtain ⟨m, ⟨hm, _⟩, rfl⟩ := hj
    exact lt_of_le_of_lt (Nat.div_le_self m d) hm
  rw [h1, h2]
  exact sum_le_sum_of_subset_of_nonneg hsub fun j _ _ =>
    mul_nonneg (by exact_mod_cast hg j) (pow_nonneg (pow_nonneg hr d) j)

/-- One coefficient against the weighted sum. -/
theorem coeff_mul_pow_le_wsum (hr : 0 ≤ r) (hg : CoeffNonneg g) {n : ℕ} (hn : n < N) :
    ((coeff n g : ℤ) : ℝ) * r ^ n ≤ wsum r N g :=
  single_le_sum (f := fun m => ((coeff m g : ℤ) : ℝ) * r ^ m)
    (fun m _ => mul_nonneg (by exact_mod_cast hg m) (pow_nonneg hr m)) (mem_range.mpr hn)

/-- The weighted sum of a cleared sparse evaluation with nonnegative inputs is at most the same
evaluation (absolute coefficients) at the weighted sums of the inputs. -/
theorem wsum_evalSparseBivarCleared_le (hr : 0 ≤ r) (xMax yMax : ℕ)
    {A B C D : PowerSeries ℤ} (hA : CoeffNonneg A) (hB : CoeffNonneg B) (hC : CoeffNonneg C)
    (hD : CoeffNonneg D) :
    ∀ terms : List SparseBivarTerm,
      wsum r N (evalSparseBivarCleared (absTerms terms) xMax yMax A B C D) ≤
        evalSparseBivarCleared (absTerms terms) xMax yMax (wsum r N A) (wsum r N B)
          (wsum r N C) (wsum r N D)
  | [] => by simp [evalSparseBivarCleared, absTerms, wsum]
  | t :: ts => by
      have hrest := wsum_evalSparseBivarCleared_le hr xMax yMax hA hB hC hD ts
      rw [absTerms_cons]
      change wsum r N (_ + _) ≤ _ + _
      rw [wsum_add]
      refine add_le_add ?_ hrest
      have hc0 : (0 : ℤ) ≤ |t.coeff| := abs_nonneg _
      have hc0' : (0 : ℝ) ≤ ((|t.coeff| : ℤ) : ℝ) := by exact_mod_cast hc0
      have n0 := coeffNonneg_intCast hc0
      have n1 := n0.mul (hA.pow t.xPow)
      have n2 := n1.mul (hB.pow (xMax - t.xPow))
      have n3 := n2.mul (hC.pow t.yPow)
      have wA := wsum_nonneg (N := N) hr hA
      have wB := wsum_nonneg (N := N) hr hB
      have wC := wsum_nonneg (N := N) hr hC
      have wD := wsum_nonneg (N := N) hr hD
      have k1 : wsum r N (((|t.coeff| : ℤ) : PowerSeries ℤ) * A ^ t.xPow) ≤
          ((|t.coeff| : ℤ) : ℝ) * wsum r N A ^ t.xPow :=
        (wsum_mul_le hr n0 (hA.pow _)).trans (mul_le_mul (wsum_intCast _ hc0)
          (wsum_pow_le hr hA _) (wsum_nonneg hr (hA.pow _)) hc0')
      have k2 : wsum r N (((|t.coeff| : ℤ) : PowerSeries ℤ) * A ^ t.xPow * B ^ (xMax - t.xPow)) ≤
          ((|t.coeff| : ℤ) : ℝ) * wsum r N A ^ t.xPow * wsum r N B ^ (xMax - t.xPow) :=
        (wsum_mul_le hr n1 (hB.pow _)).trans (mul_le_mul k1
          (wsum_pow_le hr hB _) (wsum_nonneg hr (hB.pow _))
          (mul_nonneg hc0' (pow_nonneg wA _)))
      have k3 : wsum r N (((|t.coeff| : ℤ) : PowerSeries ℤ) * A ^ t.xPow * B ^ (xMax - t.xPow) *
            C ^ t.yPow) ≤
          ((|t.coeff| : ℤ) : ℝ) * wsum r N A ^ t.xPow * wsum r N B ^ (xMax - t.xPow) *
            wsum r N C ^ t.yPow :=
        (wsum_mul_le hr n2 (hC.pow _)).trans (mul_le_mul k2
          (wsum_pow_le hr hC _) (wsum_nonneg hr (hC.pow _))
          (mul_nonneg (mul_nonneg hc0' (pow_nonneg wA _)) (pow_nonneg wB _)))
      have k4 : wsum r N (((|t.coeff| : ℤ) : PowerSeries ℤ) * A ^ t.xPow * B ^ (xMax - t.xPow) *
            C ^ t.yPow * D ^ (yMax - t.yPow)) ≤
          ((|t.coeff| : ℤ) : ℝ) * wsum r N A ^ t.xPow * wsum r N B ^ (xMax - t.xPow) *
            wsum r N C ^ t.yPow * wsum r N D ^ (yMax - t.yPow) :=
        (wsum_mul_le hr n3 (hD.pow _)).trans (mul_le_mul k3
          (wsum_pow_le hr hD _) (wsum_nonneg hr (hD.pow _))
          (mul_nonneg (mul_nonneg (mul_nonneg hc0' (pow_nonneg wA _)) (pow_nonneg wB _))
            (pow_nonneg wC _)))
      exact k4

end Weighted

/-! ### Real evaluations with absolute coefficients -/

section RealEval

theorem wsum_mono_r {r r' : ℝ} {N : ℕ} {g : PowerSeries ℤ} (hr : 0 ≤ r) (hrr : r ≤ r')
    (hg : CoeffNonneg g) : wsum r N g ≤ wsum r' N g :=
  sum_le_sum fun m _ => mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr hrr m)
    (by exact_mod_cast hg m)

theorem evalSparseBivarCleared_absTerms_nonneg (xMax yMax : ℕ) {a b c d : ℝ} (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    ∀ terms : List SparseBivarTerm,
      0 ≤ evalSparseBivarCleared (absTerms terms) xMax yMax a b c d
  | [] => by simp [evalSparseBivarCleared, absTerms]
  | t :: ts => by
      rw [absTerms_cons]
      change 0 ≤ _ + _
      refine add_nonneg ?_ (evalSparseBivarCleared_absTerms_nonneg xMax yMax ha hb hc hd ts)
      have h0 : (0 : ℝ) ≤ ((|t.coeff| : ℤ) : ℝ) := by exact_mod_cast abs_nonneg t.coeff
      exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg h0 (pow_nonneg ha _))
        (pow_nonneg hb _)) (pow_nonneg hc _)) (pow_nonneg hd _)

theorem evalSparseBivarCleared_absTerms_mono (xMax yMax : ℕ) {a b c d a' b' c' d' : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (ha' : a ≤ a') (hb' : b ≤ b') (hc' : c ≤ c') (hd' : d ≤ d') :
    ∀ terms : List SparseBivarTerm,
      evalSparseBivarCleared (absTerms terms) xMax yMax a b c d ≤
        evalSparseBivarCleared (absTerms terms) xMax yMax a' b' c' d'
  | [] => le_rfl
  | t :: ts => by
      rw [absTerms_cons]
      change _ + _ ≤ _ + _
      refine add_le_add ?_ (evalSparseBivarCleared_absTerms_mono xMax yMax ha hb hc hd
        ha' hb' hc' hd' ts)
      have h0 : (0 : ℝ) ≤ ((|t.coeff| : ℤ) : ℝ) := by exact_mod_cast abs_nonneg t.coeff
      have p1 := pow_le_pow_left₀ ha ha' t.xPow
      have p2 := pow_le_pow_left₀ hb hb' (xMax - t.xPow)
      have p3 := pow_le_pow_left₀ hc hc' t.yPow
      have p4 := pow_le_pow_left₀ hd hd' (yMax - t.yPow)
      have q1 := mul_le_mul_of_nonneg_left p1 h0
      have q2 := mul_le_mul q1 p2 (pow_nonneg hb _)
        (mul_nonneg h0 (pow_nonneg (ha.trans ha') _))
      have q3 := mul_le_mul q2 p3 (pow_nonneg hc _)
        (mul_nonneg (mul_nonneg h0 (pow_nonneg (ha.trans ha') _)) (pow_nonneg (hb.trans hb') _))
      exact mul_le_mul q3 p4 (pow_nonneg hd _)
        (mul_nonneg (mul_nonneg (mul_nonneg h0 (pow_nonneg (ha.trans ha') _))
          (pow_nonneg (hb.trans hb') _)) (pow_nonneg (hc.trans hc') _))

theorem evalSparseBivarCleared_absTerms_filter_le (xMax yMax : ℕ) {a b c d : ℝ} (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (p : SparseBivarTerm → Bool) :
    ∀ terms : List SparseBivarTerm,
      evalSparseBivarCleared (absTerms (terms.filter p)) xMax yMax a b c d ≤
        evalSparseBivarCleared (absTerms terms) xMax yMax a b c d
  | [] => le_rfl
  | t :: ts => by
      have ih := evalSparseBivarCleared_absTerms_filter_le xMax yMax ha hb hc hd p ts
      have h0 : (0 : ℝ) ≤ ((|t.coeff| : ℤ) : ℝ) := by exact_mod_cast abs_nonneg t.coeff
      have hhead : 0 ≤ ((|t.coeff| : ℤ) : ℝ) * a ^ t.xPow * b ^ (xMax - t.xPow) * c ^ t.yPow *
          d ^ (yMax - t.yPow) :=
        mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg h0 (pow_nonneg ha _))
          (pow_nonneg hb _)) (pow_nonneg hc _)) (pow_nonneg hd _)
      rw [absTerms_cons]
      change _ ≤ _ + _
      by_cases hp : p t = true
      · rw [List.filter_cons_of_pos hp, absTerms_cons]
        change _ + _ ≤ _ + _
        exact add_le_add le_rfl ih
      · rw [List.filter_cons_of_neg hp]
        exact ih.trans (le_add_of_nonneg_left hhead)

/-- Scaling the two `x`-inputs by `1/s` scales the evaluation by `1/s^xMax`. -/
theorem evalSparseBivarCleared_absTerms_div_x (xMax yMax : ℕ) {s : ℝ} (hs : s ≠ 0)
    (a b c d : ℝ) :
    ∀ terms : List SparseBivarTerm, (∀ t ∈ terms, t.xPow ≤ xMax) →
      evalSparseBivarCleared (absTerms terms) xMax yMax (a / s) (b / s) c d =
        evalSparseBivarCleared (absTerms terms) xMax yMax a b c d / s ^ xMax
  | [], _ => by simp [evalSparseBivarCleared, absTerms]
  | t :: ts, h => by
      have hx := h t (by simp)
      rw [absTerms_cons]
      change _ + _ = (_ + _) / _
      rw [evalSparseBivarCleared_absTerms_div_x xMax yMax hs a b c d ts
        (fun u hu => h u (by simp [hu])), add_div]
      congr 1
      have e : s ^ xMax = s ^ t.xPow * s ^ (xMax - t.xPow) := by
        rw [← pow_add, Nat.add_sub_cancel' hx]
      rw [e, div_pow, div_pow]
      have h1 : s ^ t.xPow ≠ 0 := pow_ne_zero _ hs
      have h2 : s ^ (xMax - t.xPow) ≠ 0 := pow_ne_zero _ hs
      field_simp

/-- Scaling the two `y`-inputs by `1/s` scales the evaluation by `1/s^yMax`. -/
theorem evalSparseBivarCleared_absTerms_div_y (xMax yMax : ℕ) {s : ℝ} (hs : s ≠ 0)
    (a b c d : ℝ) :
    ∀ terms : List SparseBivarTerm, (∀ t ∈ terms, t.yPow ≤ yMax) →
      evalSparseBivarCleared (absTerms terms) xMax yMax a b (c / s) (d / s) =
        evalSparseBivarCleared (absTerms terms) xMax yMax a b c d / s ^ yMax
  | [], _ => by simp [evalSparseBivarCleared, absTerms]
  | t :: ts, h => by
      have hy := h t (by simp)
      rw [absTerms_cons]
      change _ + _ = (_ + _) / _
      rw [evalSparseBivarCleared_absTerms_div_y xMax yMax hs a b c d ts
        (fun u hu => h u (by simp [hu])), add_div]
      congr 1
      have e : s ^ yMax = s ^ t.yPow * s ^ (yMax - t.yPow) := by
        rw [← pow_add, Nat.add_sub_cancel' hy]
      rw [e, div_pow, div_pow]
      have h1 : s ^ t.yPow ≠ 0 := pow_ne_zero _ hs
      have h2 : s ^ (yMax - t.yPow) ≠ 0 := pow_ne_zero _ hs
      field_simp

end RealEval

end Ripple.Number.Modular
