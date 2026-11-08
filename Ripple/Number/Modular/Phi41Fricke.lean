import Ripple.Number.Modular.Gamma0_41_SturmBound
import Ripple.Number.Modular.Phi41SymmCheck

/-!
# The Fricke involution halves the level-41 Sturm bound

`F = phi41Level41ClearedAsModularForm` is `Δ(τ)^42 Δ(41τ)^42 Φ₄₁(j(41τ), j(τ))`, a form of
weight `1008` on `Γ₀(41)`. Since `Φ₄₁` is symmetric (`Phi41SymmCheck`) and `E₄`, `Δ` transform
under `S` with the factors `z⁴`, `z¹²`, the form satisfies the Fricke identity
`F(S v) = 41^(-504) v^1008 F(v/41)` (`phi41Level41ClearedAsModularForm_S`).

Every `γ ∈ SL(2, ℤ) \ Γ₀(41)` is `h · S T^j` with `h ∈ Γ₀(41)`, so every non-identity factor of
the norm `∏_{Γ₀(41) \ SL(2,ℤ)} F ∣ γ` is `41^(-504) F((τ + j)/41)`. If the first `1765`
coefficients of `F` vanish, `F = O(exp(-2π·1765·y))`, each of the `41` non-identity factors is
`O(exp(-2π·(1765/41)·y))`, and the norm, a level-one form of weight `42336`, is
`O(exp(-2π·3530·y))`. The level-one Sturm bound `42336/12 + 1 = 3529 ≤ 3530` gives norm `= 0`,
hence `F = 0` (`levelGamma0_41_sturm_weight_1008_of_S`). Paper note: `docs/refactor/FRICKE.md`.
-/

namespace Ripple
namespace Number
namespace Modular

open CongruenceSubgroup ModularForm ModularFormClass UpperHalfPlane Filter Asymptotics
open scoped MatrixGroups ModularForm BigOperators

/-! ### Symmetry of `Φ₄₁` -/

theorem length_pushAt (t : SparseBivarTerm) :
    ∀ (i : ℕ) (acc : List (List SparseBivarTerm)), (pushAt t i acc).length = acc.length
  | i, [] => by cases i <;> rfl
  | 0, _ :: _ => rfl
  | i + 1, b :: bs => by simp [pushAt, length_pushAt t i bs]

theorem flatten_pushAt_perm (t : SparseBivarTerm) :
    ∀ (i : ℕ) (acc : List (List SparseBivarTerm)), i < acc.length →
      (pushAt t i acc).flatten.Perm (t :: acc.flatten)
  | _, [], h => absurd h (by simp)
  | 0, b :: bs, _ => by simp [pushAt]
  | i + 1, b :: bs, h => by
      simp only [pushAt, List.flatten_cons]
      have ih := flatten_pushAt_perm t i bs (by simpa using h)
      exact (ih.append_left b).trans List.perm_middle

theorem flatten_foldl_pushAt_perm (key : SparseBivarTerm → ℕ) :
    ∀ (terms : List SparseBivarTerm) (acc : List (List SparseBivarTerm)),
      (∀ t ∈ terms, key t < acc.length) →
      (terms.foldl (fun acc t => pushAt t (key t) acc) acc).flatten.Perm (terms ++ acc.flatten)
  | [], acc, _ => by simp
  | t :: ts, acc, h => by
      rw [List.foldl_cons]
      have hlen := length_pushAt t (key t) acc
      have ih := flatten_foldl_pushAt_perm key ts (pushAt t (key t) acc)
        (fun u hu => hlen ▸ h u (by simp [hu]))
      refine ih.trans ?_
      exact ((flatten_pushAt_perm t (key t) acc (h t (by simp))).append_left ts).trans
        List.perm_middle

/-- The buckets of `bucketBy` are a permutation of the terms, when every key is in range. -/
theorem flatten_bucketBy_perm (key : SparseBivarTerm → ℕ) (n : ℕ) (terms : List SparseBivarTerm)
    (h : ∀ t ∈ terms, key t < n) : (bucketBy key n terms).flatten.Perm terms := by
  have h0 : (List.replicate n ([] : List SparseBivarTerm)).flatten = [] := by
    induction n with
    | zero => rfl
    | succ n ih => simp [List.replicate_succ]
  have := flatten_foldl_pushAt_perm key terms (List.replicate n []) (by simpa using h)
  rw [h0, List.append_nil] at this
  exact this

/-- `Φ₄₁` is a permutation of its swap. -/
theorem phi41SparseTerms_perm_swap :
    (phi41SparseTerms.map swapSparseBivarTerm).Perm phi41SparseTerms := by
  have hx : ∀ t ∈ phi41SparseTerms, t.xPow < 43 :=
    fun t ht => Nat.lt_succ_of_le (phi41SparseTerms_degree_le_42 t ht).1
  have hy : ∀ t ∈ phi41SparseTerms, t.yPow < 43 :=
    fun t ht => Nat.lt_succ_of_le (phi41SparseTerms_degree_le_42 t ht).2
  have hrows := flatten_bucketBy_perm SparseBivarTerm.xPow 43 _ hx
  have hcols := flatten_bucketBy_perm SparseBivarTerm.yPow 43 _ hy
  rw [phi41SparseTerms_rows_eq_swapped_cols, ← List.map_flatten] at hrows
  exact (hcols.map swapSparseBivarTerm).symm.trans hrows

theorem evalSparseBivarCleared_of_perm {R : Type*} [CommRing R]
    {terms terms' : List SparseBivarTerm} (h : terms.Perm terms') (xm ym : ℕ) (a b c d : R) :
    evalSparseBivarCleared terms xm ym a b c d = evalSparseBivarCleared terms' xm ym a b c d := by
  induction h with
  | nil => rfl
  | cons t _ ih => simp [evalSparseBivarCleared, ih]
  | swap t u ts =>
      simp only [evalSparseBivarCleared]
      ring
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem evalSparseBivarCleared_map_swap {R : Type*} [CommRing R] (terms : List SparseBivarTerm)
    (xm ym : ℕ) (a b c d : R) :
    evalSparseBivarCleared (terms.map swapSparseBivarTerm) xm ym a b c d =
      evalSparseBivarCleared terms ym xm c d a b := by
  induction terms with
  | nil => rfl
  | cons t ts ih =>
      simp only [List.map_cons, evalSparseBivarCleared, ih, swapSparseBivarTerm]
      ring

/-- `Φ₄₁(X, Y) = Φ₄₁(Y, X)` for the cleared evaluation. -/
theorem evalSparseBivarCleared_phi41_symm {R : Type*} [CommRing R] (a b c d : R) :
    evalSparseBivarCleared phi41SparseTerms 42 42 a b c d =
      evalSparseBivarCleared phi41SparseTerms 42 42 c d a b :=
  (evalSparseBivarCleared_of_perm phi41SparseTerms_perm_swap 42 42 a b c d).symm.trans
    (evalSparseBivarCleared_map_swap phi41SparseTerms 42 42 a b c d)

/-- Homogeneity of the cleared evaluation in each pair of arguments separately. -/
theorem evalSparseBivarCleared_smul_smul {R : Type*} [CommRing R] (k l a b c d : R) :
    ∀ terms : List SparseBivarTerm, (∀ t ∈ terms, t.xPow ≤ 42 ∧ t.yPow ≤ 42) →
      evalSparseBivarCleared terms 42 42 (k * a) (k * b) (l * c) (l * d) =
        k ^ 42 * l ^ 42 * evalSparseBivarCleared terms 42 42 a b c d
  | [], _ => by simp [evalSparseBivarCleared]
  | t :: ts, h => by
    obtain ⟨hx, hy⟩ := h t (by simp)
    rw [evalSparseBivarCleared, evalSparseBivarCleared,
      evalSparseBivarCleared_smul_smul k l a b c d ts (fun u hu => h u (by simp [hu])), mul_add]
    congr 1
    have ek : k ^ 42 = k ^ t.xPow * k ^ (42 - t.xPow) := by
      rw [← pow_add, Nat.add_sub_cancel' hx]
    have el : l ^ 42 = l ^ t.yPow * l ^ (42 - t.yPow) := by
      rw [← pow_add, Nat.add_sub_cancel' hy]
    rw [ek, el, mul_pow, mul_pow, mul_pow, mul_pow]
    ring

/-! ### The Fricke identity -/

/-- The positive real `1/41`, acting on `ℍ` by `τ ↦ τ / 41`. -/
noncomputable def fricke41Pos : {x : ℝ // 0 < x} := ⟨41⁻¹, by norm_num⟩

theorem pullback41GL_val_det_pos : 0 < pullback41GL.det.val := by
  norm_num [pullback41GL, Matrix.det_fin_two]

theorem coe_pullback41GL_smul (z : ℍ) : ((pullback41GL • z : ℍ) : ℂ) = 41 * (z : ℂ) := by
  rw [UpperHalfPlane.coe_smul_of_det_pos pullback41GL_val_det_pos]
  simp [pullback41GL, UpperHalfPlane.num, UpperHalfPlane.denom]

theorem coe_fricke41Pos_smul (z : ℍ) : ((fricke41Pos • z : ℍ) : ℂ) = (z : ℂ) / 41 := by
  rw [UpperHalfPlane.coe_pos_real_smul, Complex.real_smul]
  simp only [fricke41Pos]
  push_cast
  ring

theorem coe_S_smul (z : ℍ) : ((ModularGroup.S • z : ℍ) : ℂ) = -1 / (z : ℂ) := by
  rw [UpperHalfPlane.modular_S_smul, UpperHalfPlane.coe_mk]
  field_simp

theorem pullback41GL_smul_fricke41Pos (v : ℍ) : pullback41GL • (fricke41Pos • v) = v := by
  ext1
  rw [coe_pullback41GL_smul, coe_fricke41Pos_smul]
  ring

theorem pullback41GL_smul_S_smul (v : ℍ) :
    pullback41GL • (ModularGroup.S • v) = ModularGroup.S • (fricke41Pos • v) := by
  ext1
  rw [coe_pullback41GL_smul, coe_S_smul, coe_S_smul, coe_fricke41Pos_smul]
  have hv : (v : ℂ) ≠ 0 := UpperHalfPlane.ne_zero v
  field_simp

/-- The Fricke identity in `S`-form: `F(S v) = 41^(-504) v^1008 F(v / 41)`. Equivalently
`F(-1/(41u)) = 41^504 u^1008 F(u)`. -/
theorem phi41Level41ClearedAsModularForm_S (v : ℍ) :
    phi41Level41ClearedAsModularForm (ModularGroup.S • v) =
      (41 : ℂ)⁻¹ ^ 504 * (v : ℂ) ^ 1008 *
        phi41Level41ClearedAsModularForm (fricke41Pos • v) := by
  rw [phi41Level41ClearedAsModularForm_apply, phi41Level41ClearedAsModularForm_apply,
    pullback41GL_smul_S_smul, pullback41GL_smul_fricke41Pos, E4_S_transform, E4_S_transform,
    delta_S_transform, delta_S_transform]
  have e3 : ∀ z w : ℂ, (z ^ 4 * w) ^ 3 = z ^ 12 * w ^ 3 := fun z w => by ring
  rw [e3, e3, evalSparseBivarCleared_smul_smul _ _ _ _ _ _ _ phi41SparseTerms_degree_le_42,
    evalSparseBivarCleared_phi41_symm (E4 (fricke41Pos • v) ^ 3), coe_fricke41Pos_smul,
    div_eq_mul_inv]
  generalize (41 : ℂ)⁻¹ = c
  ring

/-! ### The non-identity cosets -/

/-- Every `γ ∉ Γ₀(41)` is `h · S T^j` with `h ∈ Γ₀(41)` (choose `j ≡ d c⁻¹ mod 41`). -/
theorem SL2_eq_gamma0_41_mul_S_T_zpow (γ : SL(2, ℤ)) (hγ : γ ∉ Gamma0 41) :
    ∃ h ∈ Gamma0 41, ∃ j : ℤ, γ = h * (ModularGroup.S * ModularGroup.T ^ j) := by
  haveI : Fact (Nat.Prime 41) := ⟨by norm_num⟩
  rw [Gamma0_mem] at hγ
  obtain ⟨j, hj⟩ : ∃ j : ℤ, ((j : ℤ) : ZMod 41) =
      ((γ 1 1 : ℤ) : ZMod 41) * ((γ 1 0 : ℤ) : ZMod 41)⁻¹ :=
    ⟨((((γ 1 1 : ℤ) : ZMod 41) * ((γ 1 0 : ℤ) : ZMod 41)⁻¹).val : ℤ), by simp⟩
  let δ : SL(2, ℤ) := ⟨!![j, 1; -1, 0], by simp [Matrix.det_fin_two_of]⟩
  have hδ : δ * (ModularGroup.S * ModularGroup.T ^ j) = 1 := by
    ext i k
    fin_cases i <;> fin_cases k <;>
      simp [δ, ModularGroup.S, ModularGroup.coe_T_zpow, Matrix.SpecialLinearGroup.coe_mul,
        Matrix.mul_apply, Fin.sum_univ_two]
  refine ⟨γ * δ, ?_, j, ?_⟩
  · rw [Gamma0_mem]
    have h10 : ((γ * δ) 1 0 : ℤ) = γ 1 0 * j - γ 1 1 := by
      simp [δ, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
      ring
    rw [h10, Int.cast_sub, Int.cast_mul, hj, mul_comm (((γ 1 1 : ℤ) : ZMod 41)), ← mul_assoc,
      mul_inv_cancel₀ hγ, one_mul, sub_self]
  · rw [mul_assoc, hδ, mul_one]

/-- The slash of a function satisfying the `S`-form Fricke identity by `S T^j`. -/
theorem slash_S_T_zpow_apply_of_S (f : ℍ → ℂ) (C : ℂ)
    (hS : ∀ v : ℍ, f (ModularGroup.S • v) = C * (v : ℂ) ^ 1008 * f (fricke41Pos • v))
    (j : ℤ) (τ : ℍ) :
    (f ∣[(1008 : ℤ)] (ModularGroup.S * ModularGroup.T ^ j)) τ =
      C * f (fricke41Pos • (ModularGroup.T ^ j • τ)) := by
  rw [ModularForm.SL_slash_apply, mul_smul, hS, ModularGroup.denom_apply]
  have h10 : (ModularGroup.S * ModularGroup.T ^ j : SL(2, ℤ)) 1 0 = 1 := by
    simp [ModularGroup.S, ModularGroup.coe_T_zpow, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.mul_apply, Fin.sum_univ_two]
  have h11 : (ModularGroup.S * ModularGroup.T ^ j : SL(2, ℤ)) 1 1 = j := by
    simp [ModularGroup.S, ModularGroup.coe_T_zpow, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.mul_apply, Fin.sum_univ_two]
  have hw : ((ModularGroup.T ^ j • τ : ℍ) : ℂ) = (τ : ℂ) + (j : ℂ) := by
    rw [UpperHalfPlane.modular_T_zpow_smul, UpperHalfPlane.coe_vadd]
    push_cast
    ring
  have hne : (τ : ℂ) + (j : ℂ) ≠ 0 := hw ▸ UpperHalfPlane.ne_zero _
  rw [h10, h11, hw]
  push_cast
  rw [one_mul, zpow_neg, zpow_ofNat]
  field_simp

local notation "Gamma0_41NormQuot" => 𝒮ℒ ⧸ Gamma0_41_GL.subgroupOf 𝒮ℒ

/-- Each non-identity factor of the norm is a translate `C · F((τ + j) / 41)`, whatever the
representative of the coset. -/
theorem gamma0_41_quotientFunc_eq_of_ne (f : ModularForm Gamma0_41_GL 1008) (C : ℂ)
    (hS : ∀ v : ℍ, f (ModularGroup.S • v) = C * (v : ℂ) ^ 1008 * f (fricke41Pos • v))
    (q : Gamma0_41NormQuot) (hq : q ≠ QuotientGroup.mk 1) :
    ∃ j : ℤ, SlashInvariantForm.quotientFunc f q =
      fun τ => C * f (fricke41Pos • (ModularGroup.T ^ j • τ)) := by
  induction q using Quotient.inductionOn with
  | h r =>
    have hr : r ∉ Gamma0_41_GL.subgroupOf 𝒮ℒ := by
      intro hmem
      apply hq
      change (QuotientGroup.mk r : Gamma0_41NormQuot) = QuotientGroup.mk 1
      rw [QuotientGroup.eq]
      simpa using inv_mem hmem
    obtain ⟨γ₀, hγ₀⟩ := MonoidHom.mem_range.mp r.property
    have hγ₀' : γ₀ ∉ Gamma0 41 := by
      intro hmem
      apply hr
      rw [Subgroup.mem_subgroupOf]
      change _ ∈ (Gamma0 41).map (Matrix.SpecialLinearGroup.mapGL ℝ)
      exact Subgroup.mem_map.mpr ⟨γ₀, hmem, hγ₀⟩
    obtain ⟨h, hh, j, hdec⟩ := SL2_eq_gamma0_41_mul_S_T_zpow γ₀⁻¹ (fun hm => hγ₀' (by
      simpa using inv_mem hm))
    refine ⟨j, funext fun τ => ?_⟩
    rw [SlashInvariantForm.quotientFunc_mk]
    have hinv : (r : GL (Fin 2) ℝ)⁻¹ =
        Matrix.SpecialLinearGroup.mapGL ℝ h *
          Matrix.SpecialLinearGroup.mapGL ℝ (ModularGroup.S * ModularGroup.T ^ j) := by
      rw [← map_mul, ← hdec, map_inv, hγ₀]
    have hmemh : Matrix.SpecialLinearGroup.mapGL ℝ h ∈ Gamma0_41_GL := by
      change _ ∈ (Gamma0 41).map (Matrix.SpecialLinearGroup.mapGL ℝ)
      exact Subgroup.mem_map.mpr ⟨h, hh, rfl⟩
    rw [hinv, SlashAction.slash_mul, SlashInvariantFormClass.slash_action_eq f _ hmemh]
    exact slash_S_T_zpow_apply_of_S (⇑f) C hS j τ

/-! ### Decay of the translates -/

theorem im_fricke41Pos_T_zpow (j : ℤ) (τ : ℍ) :
    (fricke41Pos • (ModularGroup.T ^ j • τ)).im = τ.im / 41 := by
  rw [UpperHalfPlane.pos_real_im, UpperHalfPlane.modular_T_zpow_smul, UpperHalfPlane.vadd_im]
  simp only [fricke41Pos]
  ring

theorem tendsto_fricke41Pos_T_zpow (j : ℤ) :
    Tendsto (fun τ : ℍ => fricke41Pos • (ModularGroup.T ^ j • τ)) atImInfty atImInfty := by
  change Tendsto _ (Filter.comap UpperHalfPlane.im Filter.atTop)
    (Filter.comap UpperHalfPlane.im Filter.atTop)
  rw [Filter.tendsto_comap_iff]
  have hfun : (UpperHalfPlane.im ∘ fun τ : ℍ => fricke41Pos • (ModularGroup.T ^ j • τ)) =
      fun τ => τ.im / 41 := by
    funext τ
    exact im_fricke41Pos_T_zpow j τ
  rw [hfun]
  exact Filter.Tendsto.atTop_div_const (by norm_num) Filter.tendsto_comap

theorem isBigO_comp_fricke41Pos_T_zpow {g : ℍ → ℂ} {m : ℝ}
    (hg : g =O[atImInfty] fun τ => Real.exp (-2 * Real.pi * m * τ.im)) (j : ℤ) :
    (fun τ => g (fricke41Pos • (ModularGroup.T ^ j • τ))) =O[atImInfty]
      fun τ => Real.exp (-2 * Real.pi * (m / 41) * τ.im) := by
  refine (hg.comp_tendsto (tendsto_fricke41Pos_T_zpow j)).congr_right fun τ => ?_
  simp only [Function.comp_apply, im_fricke41Pos_T_zpow]
  congr 1
  ring

/-! ### The Fricke-halved Sturm theorem -/

/-- Sturm bound for a weight-`1008` form on `Γ₀(41)` satisfying the `S`-form Fricke identity
(any constant `C`): the first `1765` coefficients determine it, half the general bound `3529`.
The bound is sharp: `(Δ(τ)Δ(41τ))^42` satisfies the identity and starts at `q^1764`. -/
theorem levelGamma0_41_sturm_weight_1008_of_S (f : ModularForm Gamma0_41_GL 1008) (C : ℂ)
    (hS : ∀ v : ℍ, f (ModularGroup.S • v) = C * (v : ℂ) ^ 1008 * f (fricke41Pos • v))
    (hcoeff : ∀ n : ℕ, n < 1765 →
      PowerSeries.coeff (R := ℂ) n (ModularFormClass.qExpansion (1 : ℝ) f.toFun) = 0) :
    f = 0 := by
  classical
  letI := Fintype.ofFinite Gamma0_41NormQuot
  let e : Gamma0_41NormQuot := QuotientGroup.mk (1 : 𝒮ℒ)
  let H : ℍ → ℂ :=
    ∏ q ∈ (Finset.univ \ {e}), SlashInvariantForm.quotientFunc f q
  let K : ℕ := 1008 * Nat.card Gamma0_41NormQuot
  have hK_val : K = 42336 := by
    dsimp [K]
    rw [gamma0_41_normQuot_card]
  have horderR : ((K / 12 + 1 : ℕ) : ℝ) = 3529 := by
    rw [hK_val]
    norm_num
  have hfdec₀ := exp_decay_atImInfty_of_qExpansion_coeff_zero f one_pos
    gamma0_41_strictPeriod_one hcoeff
  have hfdec : (f : ℍ → ℂ) =O[atImInfty]
      fun τ : ℍ => Real.exp (-2 * Real.pi * (1765 : ℝ) * τ.im) := by
    refine hfdec₀.congr_right fun τ => ?_
    congr 1
    push_cast
    ring
  have hcard : (Finset.univ \ {e} : Finset Gamma0_41NormQuot).card = 41 := by
    rw [Finset.card_univ_diff, Finset.card_singleton, ← Nat.card_eq_fintype_card,
      gamma0_41_normQuot_card]
  have hfactor : ∀ q ∈ (Finset.univ \ {e} : Finset Gamma0_41NormQuot),
      SlashInvariantForm.quotientFunc f q =O[atImInfty]
        fun τ : ℍ => Real.exp (-2 * Real.pi * ((1765 : ℝ) / 41) * τ.im) := by
    intro q hq
    have hqe : q ≠ e := by simpa using hq
    obtain ⟨j, hj⟩ := gamma0_41_quotientFunc_eq_of_ne f C hS q hqe
    rw [hj]
    exact (isBigO_comp_fricke41Pos_T_zpow hfdec j).const_mul_left C
  have hHdec : H =O[atImInfty] fun τ : ℍ => Real.exp (-2 * Real.pi * (1765 : ℝ) * τ.im) := by
    refine ((Asymptotics.IsBigO.finsetProd hfactor).congr_left fun τ => ?_).congr_right
      fun τ => ?_
    · simp [H, Finset.prod_apply]
    · rw [Finset.prod_const, hcard, ← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
  have hfac : (⇑(ModularForm.norm 𝒮ℒ f) : ℍ → ℂ) = (f : ℍ → ℂ) * H := by
    funext z
    rw [Pi.mul_apply]
    change (SlashInvariantForm.norm 𝒮ℒ f) z = _
    rw [SlashInvariantForm.norm]
    simp only [SlashInvariantForm.coe_mk]
    rw [Finset.prod_eq_mul_prod_diff_singleton_of_mem (Finset.mem_univ e)]
    simp [H, e, Finset.prod_apply, SlashInvariantForm.quotientFunc_mk]
  have hnorm3530 : (⇑(ModularForm.norm 𝒮ℒ f) : ℍ → ℂ) =O[atImInfty]
      fun τ : ℍ => Real.exp (-2 * Real.pi * (1765 : ℝ) * τ.im) *
        Real.exp (-2 * Real.pi * (1765 : ℝ) * τ.im) := by
    rw [hfac]
    exact hfdec.mul hHdec
  have hle : (fun τ : ℍ => Real.exp (-2 * Real.pi * (1765 : ℝ) * τ.im) *
        Real.exp (-2 * Real.pi * (1765 : ℝ) * τ.im)) =O[atImInfty]
      fun τ : ℍ => Real.exp (-(2 * ((K / 12 + 1 : ℕ) : ℝ)) * Real.pi * τ.im) := by
    refine Asymptotics.IsBigO.of_bound 1 (Filter.Eventually.of_forall fun τ => ?_)
    rw [← Real.exp_add, one_mul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _), Real.exp_le_exp, horderR]
    have hpy := mul_pos Real.pi_pos τ.im_pos
    nlinarith
  have hnormdec : (gamma0_41_normLevelOne f : ℍ → ℂ) =O[atImInfty]
      fun τ : ℍ => Real.exp (-(2 * ((K / 12 + 1 : ℕ) : ℝ)) * Real.pi * τ.im) := by
    change (⇑(ModularForm.norm 𝒮ℒ f) : ℍ → ℂ) =O[atImInfty] _
    exact hnorm3530.trans hle
  have hK_pos : 4 ≤ K := by rw [hK_val]; norm_num
  have hK_even : Even K := by rw [hK_val]; norm_num
  have hnorm_zero : gamma0_41_normLevelOne f = 0 :=
    levelOne_modularForm_eq_zero_of_exp_decay hK_pos hK_even (gamma0_41_normLevelOne f) hnormdec
  have hnorm_fun : ⇑(ModularForm.norm 𝒮ℒ f) = 0 := by
    ext z
    have hz := congrArg (fun g : ModularForm 𝒮ℒ (K : ℤ) => g z) hnorm_zero
    change (gamma0_41_normLevelOne f) z = 0 at hz
    change (ModularForm.norm 𝒮ℒ f) z = 0
    simpa [gamma0_41_normLevelOne, asLevelOne, ModularForm.mcast, restrictModularForm,
      ModularForm.norm, SlashInvariantForm.norm] using hz
  have hnorm_zero' : ModularForm.norm 𝒮ℒ f = 0 := by
    ext z
    exact congrFun hnorm_fun z
  have hf_fun : ⇑f = 0 :=
    (ModularForm.norm_eq_zero_iff (ℋ := 𝒮ℒ) (f := f)).mp hnorm_zero'
  ext z
  exact congrFun hf_fun z

end Modular
end Number
end Ripple
