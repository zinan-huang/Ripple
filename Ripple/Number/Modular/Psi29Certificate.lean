import Ripple.Number.Modular.Gamma0_58
import Ripple.Number.Modular.CoeffMajorant
import Ripple.Number.Modular.Psi29PackedEval
import Ripple.Number.Modular.SturmPackedCore

/-!
# The cleared `Ψ₂₉` vanishes on `Γ₀(58)`

`psi29ClearedForm = 0` (`psi29ClearedForm_eq_zero`): the first `3601` coefficients of its
`q`-expansion vanish, by the packed kernel evaluation `p29Final_eq_zero` (`Psi29PackedEval`),
which this file identifies with the packed integer expansion, and the a priori coefficient bounds
that make the packing injective:

* wide side: `|coeff n| ≤ (8/7)^n · Σ |c| Ŵ…` for `n < 3601`, from the coefficient majorants of
  `CoeffMajorant` and the weighted sums of `E₄` at `7/8`, `(7/8)^2`, `1/32 ≥ (7/8)^29`,
  `1/2048 ≥ (7/8)^58`, checked by the kernel (`p29W*_le`, `p29WideBound_lt`);
* compact side (`T_y`, `125` coefficients in `q²⁹`): the same at `1/8` and `1/64`
  (`c29W*_le`, `p29CompactBound_lt`).
-/

namespace Ripple.Number.Modular

open Finset

/-! ### The integer cleared expansion and the bridge to the modular form -/

/-- `P = 248 e² − 616 e f + 3968 f²` over the integer series (`e = E₄`, `f = E₄(q²)`). -/
noncomputable def psi29PZ : PowerSeries ℤ := level2P E4ZSeries (qSubstZ 2 E4ZSeries)

/-- `Q = −e² + 17 e f − 16 f²` over the integer series. -/
noncomputable def psi29QZ : PowerSeries ℤ := level2Q E4ZSeries (qSubstZ 2 E4ZSeries)

/-- The cleared `Ψ₂₉` over the integer series. -/
noncomputable def psi29ClearedZ : PowerSeries ℤ :=
  evalSparseBivarCleared psi29SparseTerms 30 30
    (level2P (qSubstZ 29 E4ZSeries) (qSubstZ 58 E4ZSeries))
    (level2Q (qSubstZ 29 E4ZSeries) (qSubstZ 58 E4ZSeries))
    psi29PZ psi29QZ

theorem map_qSubstZ (d : ℕ) [NeZero d] (f : PowerSeries ℤ) :
    PowerSeries.map (Int.castRingHom ℂ) (qSubstZ d f) =
      qPullbackBy d (PowerSeries.map (Int.castRingHom ℂ) f) := by
  ext n
  rw [PowerSeries.coeff_map, coeff_qSubstZ (NeZero.ne d), coeff_qPullbackBy]
  split_ifs
  · rw [PowerSeries.coeff_map]
  · simp

theorem psi29ClearedForm_qExpansion_eq_map :
    ModularFormClass.qExpansion (1 : ℝ) (psi29ClearedForm : UpperHalfPlane → ℂ) =
      PowerSeries.map (Int.castRingHom ℂ) psi29ClearedZ := by
  rw [psi29ClearedForm_qExpansion, psi29ClearedZ, map_evalSparseBivarCleared]
  simp only [psi29PZ, psi29QZ, level2P, level2Q, map_quadForm, map_qSubstZ, map_E4ZSeries]

/-! ### Generic packing lemmas -/

/-- Substituting `q ↦ q ^ d` corresponds to packing at `x ^ d` with `K ≥ N / d` slots. -/
theorem packEval_qSubstZ {R : Type*} [CommRing R] {x : R} {N K d : ℕ} (hd : 0 < d)
    (hx : x ^ N = 0) (hK : N ≤ d * K) (f : PowerSeries ℤ) :
    packEval x N (qSubstZ d f) = packEval (x ^ d) K f := by
  rw [packEval_eq_sum_of_le hx _ hK, packEval_eq_sum]
  clear hK
  induction K with
  | zero => simp
  | succ K ih =>
    rw [show d * (K + 1) = d * K + d by ring, Finset.sum_range_add, ih,
      Finset.sum_range_succ _ K]
    congr 1
    rw [Finset.sum_eq_single 0]
    · rw [add_zero, coeff_qSubstZ hd.ne', if_pos (dvd_mul_right d K),
        Nat.mul_div_cancel_left K hd, ← pow_mul]
    · intro i hi hi0
      have hnd : ¬ d ∣ d * K + i := by
        rw [Nat.dvd_add_right (dvd_mul_right d K)]
        exact fun h => hi0 (Nat.eq_zero_of_dvd_of_lt h (mem_range.mp hi))
      rw [coeff_qSubstZ hd.ne', if_neg hnd, Int.cast_zero, zero_mul]
    · intro h
      exact absurd (mem_range.mpr hd) h

theorem e4Digit_lt_two_pow_72 {m : ℕ} (hm : m ≤ 4096) : e4Digit m < 2 ^ 72 := by
  have h1 := (sigma_le_pow_succ_aux 3 m).trans (Nat.pow_le_pow_left hm 4)
  unfold e4Digit
  generalize ArithmeticFunction.sigma 3 m = t at h1 ⊢
  norm_num at h1 ⊢
  split_ifs <;> omega

theorem spread_e4Pack_4096 (s fuel n : ℕ) (hn : 0 < n) (hn' : n ≤ 4096) (hfuel : n ≤ 2 ^ fuel) :
    spread 72 s (e4Pack 72 n) fuel 0 n = ∑ m ∈ range n, e4Digit m * 2 ^ (s * m) := by
  rw [e4Pack_eq_sum (by norm_num) hn hn']
  exact spread_of_digits 72 s fuel n e4Digit
    (fun m hm => e4Digit_lt_two_pow_72 (by omega)) hfuel

theorem e4Pack_digit {n m : ℕ} (hn : n ≤ 4096) (hm : m < n) :
    (e4Pack 72 n >>> (72 * m)) % 2 ^ 72 = e4Digit m := by
  rw [e4Pack_eq_sum (by norm_num) (by omega) hn]
  exact digit_of_sum 72 m n e4Digit (fun k hk => e4Digit_lt_two_pow_72 (by omega)) hm

/-! ### The wide ring -/

theorem p29M_eq_pow : p29M = 2 ^ (p29S * p29N) := by
  rw [p29M, Nat.shiftLeft_eq, Nat.one_mul]

theorem p29CM_eq_pow : p29CM = 2 ^ (p29CW * p29K) := by
  rw [p29CM, Nat.shiftLeft_eq, Nat.one_mul]

local notation "ZP" => ZMod p29M
local notation "KZ" => ZMod p29CM

/-- The wide packing point `2 ^ p29S`. -/
def p29X : ZP := 2 ^ p29S

theorem p29X_pow : p29X ^ p29N = 0 :=
  two_pow_pow_eq_zero p29M_eq_pow

theorem cast_p29E : ((p29E : ℕ) : ZP) = packEval p29X p29N E4ZSeries := by
  rw [p29E, spread_e4Pack_4096 p29S 12 p29N (by norm_num [p29N]) (by norm_num [p29N])
    (by norm_num [p29N]), packEval_eq_sum]
  push_cast
  refine sum_congr rfl fun m _ => ?_
  rw [coeff_E4ZSeries, ← e4Digit_cast, p29X]
  push_cast
  ring

theorem cast_p29F : ((p29F : ℕ) : ZP) = packEval p29X p29N (qSubstZ 2 E4ZSeries) := by
  rw [p29F, cast_land_mask p29M_eq_pow p29Mask_eq,
    spread_e4Pack_4096 (2 * p29S) 12 1801 (by norm_num) (by norm_num) (by norm_num),
    packEval_qSubstZ (K := 1801) (by norm_num) p29X_pow (by norm_num [p29N]), packEval_eq_sum]
  push_cast
  refine sum_congr rfl fun m _ => ?_
  rw [coeff_E4ZSeries, ← e4Digit_cast, p29X]
  push_cast
  ring

theorem cast_p29P : ((p29P : ℕ) : ZP) = packEval p29X p29N psi29PZ := by
  rw [psi29PZ, ← packHom_apply p29X p29N p29X_pow, level2P, map_quadForm, packHom_apply,
    packHom_apply, ← cast_p29E, ← cast_p29F, p29P, cast_subM p29M_eq_pow p29Mask_eq]
  simp only [p29EE, p29EF, p29FF, Nat.cast_add, Nat.cast_mul,
    cast_mulM p29M_eq_pow p29Mask_eq, quadForm]
  push_cast
  ring

theorem cast_p29Q : ((p29Q : ℕ) : ZP) = packEval p29X p29N psi29QZ := by
  rw [psi29QZ, ← packHom_apply p29X p29N p29X_pow, level2Q, map_quadForm, packHom_apply,
    packHom_apply, ← cast_p29E, ← cast_p29F, p29Q, cast_subM p29M_eq_pow p29Mask_eq]
  simp only [p29EE, p29EF, p29FF, Nat.cast_add, Nat.cast_mul,
    cast_mulM p29M_eq_pow p29Mask_eq, quadForm]
  push_cast
  ring

/-! ### The compact ring and the grouped sums `T_y` -/

/-- The compact packing point `2 ^ p29CW`. -/
def c29X : KZ := 2 ^ p29CW

theorem c29X_pow : c29X ^ p29K = 0 :=
  two_pow_pow_eq_zero p29CM_eq_pow

theorem cast_c29E : ((c29E : ℕ) : KZ) = packEval c29X p29K E4ZSeries := by
  rw [c29E, e4Pack_eq_sum (w := p29CW) (n := p29K) (by norm_num [p29CW]) (by norm_num [p29K])
    (by norm_num [p29K]), packEval_eq_sum]
  push_cast
  refine sum_congr rfl fun m _ => ?_
  rw [coeff_E4ZSeries, ← e4Digit_cast, c29X]
  push_cast
  ring

theorem cast_c29F : ((c29F : ℕ) : KZ) = packEval c29X p29K (qSubstZ 2 E4ZSeries) := by
  rw [c29F, cast_land_mask p29CM_eq_pow p29CMask_eq,
    e4Pack_eq_sum (w := 2 * p29CW) (n := 63) (by norm_num [p29CW]) (by norm_num) (by norm_num),
    packEval_qSubstZ (K := 63) (by norm_num) c29X_pow (by norm_num [p29K]), packEval_eq_sum]
  push_cast
  refine sum_congr rfl fun m _ => ?_
  rw [coeff_E4ZSeries, ← e4Digit_cast, c29X]
  push_cast
  ring

theorem cast_c29P : ((c29P : ℕ) : KZ) = packEval c29X p29K psi29PZ := by
  rw [psi29PZ, ← packHom_apply c29X p29K c29X_pow, level2P, map_quadForm, packHom_apply,
    packHom_apply, ← cast_c29E, ← cast_c29F, c29P, cast_subM p29CM_eq_pow p29CMask_eq]
  simp only [c29EE, c29EF, c29FF, Nat.cast_add, Nat.cast_mul,
    cast_mulM p29CM_eq_pow p29CMask_eq, quadForm]
  push_cast
  ring

theorem cast_c29Q : ((c29Q : ℕ) : KZ) = packEval c29X p29K psi29QZ := by
  rw [psi29QZ, ← packHom_apply c29X p29K c29X_pow, level2Q, map_quadForm, packHom_apply,
    packHom_apply, ← cast_c29E, ← cast_c29F, c29Q, cast_subM p29CM_eq_pow p29CMask_eq]
  simp only [c29EE, c29EF, c29FF, Nat.cast_add, Nat.cast_mul,
    cast_mulM p29CM_eq_pow p29CMask_eq, quadForm]
  push_cast
  ring

theorem cast_c29L {x : ℕ} (hx : x ≤ 30) :
    ((c29L.getD x 0 : ℕ) : KZ) =
      packEval c29X p29K psi29PZ ^ x * packEval c29X p29K psi29QZ ^ (30 - x) := by
  rw [c29L, getD_map_range (n := 31) (y := x) _ (by omega)]
  try dsimp only
  rw [cast_mulM p29CM_eq_pow p29CMask_eq, c29PowP, c29PowQ,
    cast_powTab_getD p29CM_eq_pow p29CMask_eq c29P 1 31 x (by omega),
    cast_powTab_getD p29CM_eq_pow p29CMask_eq c29Q 1 31 (30 - x) (by omega),
    Nat.cast_one, one_mul, one_mul, cast_c29P, cast_c29Q]

/-- The `y`-group of the cleared expansion on the `q²⁹` side (variable `t = q²⁹`). -/
noncomputable def psi29TSer (y : ℕ) : PowerSeries ℤ :=
  (psi29SparseTerms.map fun t => if t.yPow = y then
    (t.coeff : PowerSeries ℤ) * (psi29PZ ^ t.xPow * psi29QZ ^ (30 - t.xPow)) else 0).sum

theorem packEval_psi29TSer {R : Type*} [CommRing R] {z : R} {n : ℕ} (hz : z ^ n = 0) (y : ℕ) :
    packEval z n (psi29TSer y) =
      (psi29SparseTerms.map fun t => if t.yPow = y then
        (t.coeff : R) * (packEval z n psi29PZ ^ t.xPow * packEval z n psi29QZ ^ (30 - t.xPow))
        else 0).sum := by
  rw [← packHom_apply z n hz, psi29TSer, map_list_sum, List.map_map]
  refine congrArg List.sum (List.map_congr_left fun t _ => ?_)
  simp only [Function.comp_apply]
  split_ifs
  · rw [map_mul, map_mul, map_pow, map_pow, map_intCast, packHom_apply, packHom_apply]
  · exact map_zero _

theorem cast_c29T (y : ℕ) : ((c29T y : ℕ) : KZ) = packEval c29X p29K (psi29TSer y) := by
  rw [c29T, c29Ts, cast_bucketPN p29CM_eq_pow p29CMask_eq _ _ _
    (fun t ht => Nat.lt_succ_of_le (psi29SparseTerms_degree_le_30 t ht).2),
    packEval_psi29TSer c29X_pow]
  refine congrArg List.sum (List.map_congr_left fun t ht => ?_)
  split_ifs
  · rw [cast_c29L (psi29SparseTerms_degree_le_30 t ht).1]
  · rfl

/-! ### Casting helpers (generic exponents, so that no large power is ever evaluated) -/

theorem cast_shift_lt_shift {a b c : ℕ} (h : a <<< b < 1 <<< c) :
    (a : ℝ) * 2 ^ b < 2 ^ c := by
  rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, one_mul] at h
  exact_mod_cast h

theorem cast_wide_lt_shift {a n s : ℕ} (h : a * 8 ^ n < 7 ^ n <<< s) :
    (a : ℝ) * 8 ^ n < 7 ^ n * 2 ^ s := by
  rw [Nat.shiftLeft_eq] at h
  exact_mod_cast h

theorem int_lt_two_pow_of_real {c : ℤ} {k : ℕ} (h : (c : ℝ) < 2 ^ k) : c < 2 ^ k := by
  exact_mod_cast h

theorem div3_mul_cancel {T A C E : ℝ} (hA : A ≠ 0) (hC : C ≠ 0) :
    T / A / A / C * (A * A * (C * E)) = T * E := by
  rw [div_div, div_div, div_mul_eq_mul_div, div_eq_iff (by simp [hA, hC])]
  ring

/-! ### Coefficient bounds -/

theorem coeffNonneg_E4ZSeries : CoeffNonneg E4ZSeries := fun m => by
  rw [coeff_E4ZSeries, ← e4Digit_cast]
  exact Int.natCast_nonneg _

theorem coeffDom_quadForm (a b c : ℤ) {x y X Y : PowerSeries ℤ} (hx : CoeffDom x X)
    (hy : CoeffDom y Y) :
    CoeffDom (quadForm a b c x y) (quadForm |a| |b| |c| X Y) :=
  (((coeffDom_intCast a).mul (hx.pow 2)).add (((coeffDom_intCast b).mul hx).mul hy)).add
    ((coeffDom_intCast c).mul (hy.pow 2))

theorem coeffNonneg_quadForm {a b c : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    {X Y : PowerSeries ℤ} (hX : CoeffNonneg X) (hY : CoeffNonneg Y) :
    CoeffNonneg (quadForm a b c X Y) :=
  (((coeffNonneg_intCast ha).mul (hX.pow 2)).add (((coeffNonneg_intCast hb).mul hX).mul hY)).add
    ((coeffNonneg_intCast hc).mul (hY.pow 2))

theorem wsum_quadForm_le {r : ℝ} {N : ℕ} (hr : 0 ≤ r) {a b c : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) {X Y : PowerSeries ℤ} (hX : CoeffNonneg X) (hY : CoeffNonneg Y) :
    wsum r N (quadForm a b c X Y) ≤
      a * wsum r N X ^ 2 + b * wsum r N X * wsum r N Y + c * wsum r N Y ^ 2 := by
  have wX := wsum_nonneg (N := N) hr hX
  have wY := wsum_nonneg (N := N) hr hY
  have ha' : (0 : ℝ) ≤ a := by exact_mod_cast ha
  have hb' : (0 : ℝ) ≤ b := by exact_mod_cast hb
  rw [quadForm, wsum_add, wsum_add]
  refine add_le_add (add_le_add ?_ ?_) ?_
  · exact (wsum_mul_le hr (coeffNonneg_intCast ha) (hX.pow 2)).trans
      (mul_le_mul (wsum_intCast a ha) (wsum_pow_le hr hX 2) (wsum_nonneg hr (hX.pow 2)) ha')
  · refine (wsum_mul_le hr ((coeffNonneg_intCast hb).mul hX) hY).trans
      (mul_le_mul_of_nonneg_right ?_ wY)
    exact (wsum_mul_le hr (coeffNonneg_intCast hb) hX).trans
      (mul_le_mul_of_nonneg_right (wsum_intCast b hb) wX)
  · exact (wsum_mul_le hr (coeffNonneg_intCast hc) (hY.pow 2)).trans
      (mul_le_mul (wsum_intCast c hc) (wsum_pow_le hr hY 2) (wsum_nonneg hr (hY.pow 2))
        (by exact_mod_cast hc))

/-- The weighted sum of the `E₄` coefficients at `a / 2^k` from the packed digits. -/
theorem wsum_E4ZSeries_eq (a k : ℕ) {n : ℕ} (hn0 : 0 < n) (hn : n ≤ 4096) :
    wsum ((a : ℝ) / 2 ^ k) n E4ZSeries =
      (wsumDig (e4Pack 72 n) a k n : ℝ) / 2 ^ (k * (n - 1)) := by
  rw [wsumDig, treeSum_eq _ 12 0 n (by norm_num; omega), Nat.cast_sum, Finset.sum_div, wsum]
  refine sum_congr rfl fun m hm => ?_
  have hmn : m < n := mem_range.mp hm
  rw [zero_add, e4Pack_digit hn hmn, Nat.shiftLeft_eq, coeff_E4ZSeries, ← e4Digit_cast]
  have h2 : (2 : ℝ) ^ (k * (n - 1)) = ((2 : ℝ) ^ k) ^ m * 2 ^ (k * (n - 1 - m)) := by
    rw [← pow_mul, ← pow_add, ← mul_add, Nat.add_sub_cancel' (by omega)]
  have hpos : (0 : ℝ) < 2 ^ (k * (n - 1 - m)) := by positivity
  rw [h2]
  push_cast
  rw [mul_div_mul_right _ _ hpos.ne']
  ring

/-- `W ≤ U / 2^p29SC` from the kernel inequality `G · 2^p29SC ≤ U · 2^(k(n-1))`. -/
theorem wsum_E4ZSeries_le (a k U : ℕ) {n : ℕ} (hn0 : 0 < n) (hn : n ≤ 4096)
    (h : wsumDig (e4Pack 72 n) a k n <<< p29SC ≤ U <<< (k * (n - 1))) :
    wsum ((a : ℝ) / 2 ^ k) n E4ZSeries ≤ (U : ℝ) / 2 ^ p29SC := by
  rw [wsum_E4ZSeries_eq a k hn0 hn, div_le_div_iff₀ (by positivity) (by positivity)]
  rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq] at h
  exact_mod_cast h

theorem absEvalNat_cast (xMax yMax a b c d : ℕ) :
    ∀ terms : List SparseBivarTerm,
      (absEvalNat xMax yMax a b c d terms : ℝ) =
        evalSparseBivarCleared (absTerms terms) xMax yMax (a : ℝ) b c d
  | [] => by simp [absEvalNat, evalSparseBivarCleared, absTerms]
  | t :: ts => by
      rw [absTerms_cons]
      change _ = _ + _
      rw [absEvalNat, Nat.cast_add, absEvalNat_cast xMax yMax a b c d ts]
      congr 1
      push_cast
      rw [← Int.cast_natCast (R := ℝ) t.coeff.natAbs, Int.natCast_natAbs, Int.cast_abs]

/-- From `c · r^n ≤ B` with `0 < r ≤ 1` and `n ≤ M`: `c ≤ B / r^M`. -/
theorem le_div_pow_of_mul_pow_le {c B r : ℝ} {n M : ℕ} (hr0 : 0 < r) (hr1 : r ≤ 1)
    (hn : n ≤ M) (hB : 0 ≤ B) (h : c * r ^ n ≤ B) : c ≤ B / r ^ M := by
  have hrn : 0 < r ^ n := pow_pos hr0 n
  have hrM : 0 < r ^ M := pow_pos hr0 M
  calc c ≤ B / r ^ n := (le_div_iff₀ hrn).mpr h
    _ ≤ B / r ^ M := div_le_div_of_nonneg_left hB hrM (pow_le_pow_of_le_one hr0.le hr1 hn)

/-- `T̂_y` dominates `T_y`: the list sum with `|c|` and the condition dropped. -/
theorem abs_coeff_listSum_le {P Q P' Q' : PowerSeries ℤ} (hP : CoeffDom P P')
    (hQ : CoeffDom Q Q') (X y m : ℕ) :
    ∀ terms : List SparseBivarTerm,
      |PowerSeries.coeff m ((terms.map fun t => if t.yPow = y then
          (t.coeff : PowerSeries ℤ) * (P ^ t.xPow * Q ^ (X - t.xPow)) else 0).sum)| ≤
        PowerSeries.coeff m (evalSparseBivarCleared (absTerms terms) X 0 P' Q' 1 1)
  | [] => by simp [evalSparseBivarCleared, absTerms]
  | t :: ts => by
      rw [absTerms_cons, List.map_cons, List.sum_cons, map_add]
      change _ ≤ PowerSeries.coeff m (_ + _)
      rw [map_add]
      refine (abs_add_le _ _).trans (add_le_add ?_ (abs_coeff_listSum_le hP hQ X y m ts))
      have hd := (coeffDom_intCast t.coeff).mul ((hP.pow t.xPow).mul (hQ.pow (X - t.xPow)))
      have hone : ((⟨|t.coeff|, t.xPow, t.yPow⟩ : SparseBivarTerm).coeff : PowerSeries ℤ) *
          P' ^ t.xPow * Q' ^ (X - t.xPow) * 1 ^ t.yPow * 1 ^ (0 - t.yPow) =
          ((|t.coeff| : ℤ) : PowerSeries ℤ) * (P' ^ t.xPow * Q' ^ (X - t.xPow)) := by
        simp only [one_pow, mul_one]
        ring
      rw [hone]
      split_ifs
      · exact hd.2 m
      · rw [map_zero, abs_zero]
        exact hd.1 m

theorem quad_mono {a b c x y X Y : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hx : 0 ≤ x)
    (hX : x ≤ X) (hy : 0 ≤ y) (hY : y ≤ Y) :
    a * x ^ 2 + b * x * y + c * y ^ 2 ≤ a * X ^ 2 + b * X * Y + c * Y ^ 2 := by
  have h1 : x ^ 2 ≤ X ^ 2 := pow_le_pow_left₀ hx hX 2
  have h2 : x * y ≤ X * Y := mul_le_mul hX hY hy (hx.trans hX)
  have h3 : y ^ 2 ≤ Y ^ 2 := pow_le_pow_left₀ hy hY 2
  have k1 := mul_le_mul_of_nonneg_left h1 ha
  have k2 := mul_le_mul_of_nonneg_left h2 hb
  have k3 := mul_le_mul_of_nonneg_left h3 hc
  rw [mul_assoc b x y, mul_assoc b X Y]
  linarith

theorem quadNat_div (a b c U V k : ℕ) :
    (quadNat a b c U V : ℝ) / 2 ^ (2 * k) =
      a * ((U : ℝ) / 2 ^ k) ^ 2 + b * ((U : ℝ) / 2 ^ k) * ((V : ℝ) / 2 ^ k) +
        c * ((V : ℝ) / 2 ^ k) ^ 2 := by
  simp only [quadNat]
  push_cast
  ring

/-- Majorant of `P` (absolute coefficients). -/
noncomputable def psi29PhZ : PowerSeries ℤ := quadForm 248 616 3968 E4ZSeries (qSubstZ 2 E4ZSeries)

/-- Majorant of `Q` (absolute coefficients). -/
noncomputable def psi29QhZ : PowerSeries ℤ := quadForm 1 17 16 E4ZSeries (qSubstZ 2 E4ZSeries)

theorem coeffNonneg_qSubstZ_E4 (d : ℕ) [NeZero d] : CoeffNonneg (qSubstZ d E4ZSeries) :=
  coeffNonneg_E4ZSeries.qSubstZ (NeZero.ne d)

theorem coeffDom_psi29PZ : CoeffDom psi29PZ psi29PhZ := by
  simpa [psi29PZ, psi29PhZ, level2P] using
    coeffDom_quadForm 248 (-616) 3968 (coeffDom_of_nonneg coeffNonneg_E4ZSeries)
      (coeffDom_of_nonneg (coeffNonneg_qSubstZ_E4 2))

theorem coeffDom_psi29QZ : CoeffDom psi29QZ psi29QhZ := by
  simpa [psi29QZ, psi29QhZ, level2Q] using
    coeffDom_quadForm (-1) 17 (-16) (coeffDom_of_nonneg coeffNonneg_E4ZSeries)
      (coeffDom_of_nonneg (coeffNonneg_qSubstZ_E4 2))

/-- The compact weight `1/8`. -/
noncomputable def c29Rho : ℝ := ((1 : ℕ) : ℝ) / 2 ^ 3

theorem c29Rho_pos : 0 < c29Rho := by unfold c29Rho; positivity

theorem c29Rho_le_one : c29Rho ≤ 1 := by unfold c29Rho; norm_num

theorem c29_wsum_E : wsum c29Rho p29K E4ZSeries ≤ (c29UE : ℝ) / 2 ^ p29SC :=
  wsum_E4ZSeries_le 1 3 c29UE (by norm_num [p29K]) (by norm_num [p29K]) c29WE_le

theorem c29_wsum_E2 : wsum c29Rho p29K (qSubstZ 2 E4ZSeries) ≤ (c29UE2 : ℝ) / 2 ^ p29SC := by
  refine (wsum_qSubstZ_le c29Rho_pos.le (by norm_num) coeffNonneg_E4ZSeries).trans ?_
  have e : c29Rho ^ 2 = ((1 : ℕ) : ℝ) / 2 ^ 6 := by unfold c29Rho; norm_num
  rw [e]
  exact wsum_E4ZSeries_le 1 6 c29UE2 (by norm_num [p29K]) (by norm_num [p29K]) c29WE2_le

theorem c29_wsum_Ph :
    wsum c29Rho p29K psi29PhZ ≤ (quadNat 248 616 3968 c29UE c29UE2 : ℝ) / 2 ^ (2 * p29SC) := by
  refine (wsum_quadForm_le c29Rho_pos.le (by norm_num) (by norm_num) (by norm_num)
    coeffNonneg_E4ZSeries (coeffNonneg_qSubstZ_E4 2)).trans ?_
  rw [quadNat_div]
  push_cast
  exact quad_mono (by norm_num) (by norm_num) (by norm_num)
    (wsum_nonneg c29Rho_pos.le coeffNonneg_E4ZSeries) c29_wsum_E
    (wsum_nonneg c29Rho_pos.le (coeffNonneg_qSubstZ_E4 2)) c29_wsum_E2

theorem c29_wsum_Qh :
    wsum c29Rho p29K psi29QhZ ≤ (quadNat 1 17 16 c29UE c29UE2 : ℝ) / 2 ^ (2 * p29SC) := by
  refine (wsum_quadForm_le c29Rho_pos.le (by norm_num) (by norm_num) (by norm_num)
    coeffNonneg_E4ZSeries (coeffNonneg_qSubstZ_E4 2)).trans ?_
  rw [quadNat_div]
  push_cast
  exact quad_mono (by norm_num) (by norm_num) (by norm_num)
    (wsum_nonneg c29Rho_pos.le coeffNonneg_E4ZSeries) c29_wsum_E
    (wsum_nonneg c29Rho_pos.le (coeffNonneg_qSubstZ_E4 2)) c29_wsum_E2

/-- The compact majorant: `Σ |c| P̂^x Q̂^(30-x)` over all terms. -/
noncomputable def psi29TMaj : PowerSeries ℤ :=
  evalSparseBivarCleared (absTerms psi29SparseTerms) 30 0 psi29PhZ psi29QhZ 1 1

theorem coeffNonneg_psi29TMaj : CoeffNonneg psi29TMaj :=
  (coeffDom_evalSparseBivarCleared 30 0 (coeffDom_of_nonneg coeffDom_psi29PZ.1)
    (coeffDom_of_nonneg coeffDom_psi29QZ.1) (coeffDom_of_nonneg coeffNonneg_one)
    (coeffDom_of_nonneg coeffNonneg_one) psi29SparseTerms).1

/-- The scaled natural-number bound of the compact majorant. -/
def c29TBound : ℕ :=
  absEvalNat 30 0 (quadNat 248 616 3968 c29UE c29UE2) (quadNat 1 17 16 c29UE c29UE2) 1 1
    psi29SparseTerms

theorem c29_wsum_TMaj :
    wsum c29Rho p29K psi29TMaj ≤ (c29TBound : ℝ) / (2 ^ (2 * p29SC)) ^ 30 := by
  refine (wsum_evalSparseBivarCleared_le c29Rho_pos.le 30 0 coeffDom_psi29PZ.1
    coeffDom_psi29QZ.1 coeffNonneg_one coeffNonneg_one psi29SparseTerms).trans ?_
  refine (evalSparseBivarCleared_absTerms_mono 30 0
    (wsum_nonneg c29Rho_pos.le coeffDom_psi29PZ.1) (wsum_nonneg c29Rho_pos.le coeffDom_psi29QZ.1)
    (wsum_nonneg c29Rho_pos.le coeffNonneg_one) (wsum_nonneg c29Rho_pos.le coeffNonneg_one)
    c29_wsum_Ph c29_wsum_Qh wsum_one_le wsum_one_le psi29SparseTerms).trans (le_of_eq ?_)
  rw [evalSparseBivarCleared_absTerms_div_x 30 0 (by positivity) _ _ _ _ psi29SparseTerms
    (fun t ht => (psi29SparseTerms_degree_le_30 t ht).1), c29TBound, absEvalNat_cast,
    Nat.cast_one]

theorem c29TBound_lt :
    (c29TBound : ℝ) / (2 ^ (2 * p29SC)) ^ 30 / c29Rho ^ (p29K - 1) < 2 ^ (p29CW - 1) := by
  have hltR := cast_shift_lt_shift p29CompactBound_lt
  have e : (c29TBound : ℝ) / (2 ^ (2 * p29SC)) ^ 30 / c29Rho ^ (p29K - 1) =
      (c29TBound : ℝ) * 2 ^ (3 * (p29K - 1)) / 2 ^ (60 * p29SC) := by
    unfold c29Rho
    rw [Nat.cast_one, div_pow, one_pow, div_div_eq_mul_div, div_one, ← pow_mul, ← pow_mul,
      div_mul_eq_mul_div, show 2 * p29SC * 30 = 60 * p29SC by ring]
  rw [e, div_lt_iff₀ (by positivity), ← pow_add]
  exact hltR

theorem psi29TSer_coeff_lt (y : ℕ) {m : ℕ} (hm : m < p29K) :
    |PowerSeries.coeff m (psi29TSer y)| < 2 ^ (p29CW - 1) := by
  have h1 : |PowerSeries.coeff m (psi29TSer y)| ≤ PowerSeries.coeff m psi29TMaj :=
    abs_coeff_listSum_le coeffDom_psi29PZ coeffDom_psi29QZ 30 y m psi29SparseTerms
  have hc := coeff_mul_pow_le_wsum c29Rho_pos.le coeffNonneg_psi29TMaj hm
  have hfin := le_div_pow_of_mul_pow_le c29Rho_pos c29Rho_le_one (Nat.le_sub_one_of_lt hm)
    (le_trans (mul_nonneg (by exact_mod_cast coeffNonneg_psi29TMaj m)
      (pow_nonneg c29Rho_pos.le m)) (hc.trans c29_wsum_TMaj)) (hc.trans c29_wsum_TMaj)
  have hcoeffR : ((|PowerSeries.coeff m (psi29TSer y)| : ℤ) : ℝ) < 2 ^ (p29CW - 1) :=
    lt_of_le_of_lt ((Int.cast_le.mpr h1).trans hfin) c29TBound_lt
  exact int_lt_two_pow_of_real hcoeffR

/-! ### Back to the wide ring -/

theorem c29Bias_eq : c29Bias = 2 ^ (p29CW - 1) * ∑ m ∈ range p29K, 2 ^ (p29CW * m) := by
  rw [c29Bias, one_add_geomF p29CW 7 124 (by norm_num), show (124 : ℕ) + 1 = p29K from rfl]

theorem c29U_eq (y : ℕ) :
    c29U y = ∑ m ∈ range p29K,
      (PowerSeries.coeff m (psi29TSer y) + 2 ^ (p29CW - 1)).toNat * 2 ^ (p29CW * m) := by
  rw [c29U, c29Bias_eq]
  exact biased_digits p29CM_eq_pow (by norm_num [p29CW]) _
    (fun m hm => psi29TSer_coeff_lt y hm) _ (cast_c29T y)

theorem spread_c29U (y : ℕ) :
    spread p29CW (29 * p29S) (c29U y) 7 0 p29K = ∑ m ∈ range p29K,
      (PowerSeries.coeff m (psi29TSer y) + 2 ^ (p29CW - 1)).toNat * 2 ^ (29 * p29S * m) := by
  rw [c29U_eq]
  exact spread_of_digits p29CW (29 * p29S) 7 p29K _
    (fun m hm => biased_digit_lt (by norm_num [p29CW]) (psi29TSer_coeff_lt y hm))
    (by norm_num [p29K])

theorem spread_c29Bias :
    spread p29CW (29 * p29S) c29Bias 7 0 p29K =
      ∑ m ∈ range p29K, 2 ^ (p29CW - 1) * 2 ^ (29 * p29S * m) := by
  rw [c29Bias_eq, Finset.mul_sum]
  exact spread_of_digits p29CW (29 * p29S) 7 p29K (fun _ => 2 ^ (p29CW - 1))
    (fun _ _ => Nat.pow_lt_pow_right (by norm_num) (by norm_num [p29CW])) (by norm_num [p29K])

theorem p29X_pull : p29X ^ 29 = (2 : ZP) ^ (29 * p29S) := by
  rw [p29X, ← pow_mul, mul_comm]

theorem cast_p29SY (y : ℕ) :
    ((p29SY y : ℕ) : ZP) = packEval (p29X ^ 29) p29K (psi29TSer y) := by
  have hterm : ∀ m ∈ range p29K,
      ((((PowerSeries.coeff m (psi29TSer y) + 2 ^ (p29CW - 1)).toNat *
          2 ^ (29 * p29S * m) : ℕ)) : ZP) =
        ((PowerSeries.coeff m (psi29TSer y) : ℤ) : ZP) * ((2 : ZP) ^ (29 * p29S)) ^ m +
          2 ^ (p29CW - 1) * 2 ^ (29 * p29S * m) := by
    intro m hm
    have h0 : 0 ≤ PowerSeries.coeff m (psi29TSer y) + 2 ^ (p29CW - 1) := by
      have := abs_lt.mp (psi29TSer_coeff_lt y (mem_range.mp hm))
      linarith
    rw [Nat.cast_mul,
      ← Int.cast_natCast (PowerSeries.coeff m (psi29TSer y) + 2 ^ (p29CW - 1)).toNat,
      Int.toNat_of_nonneg h0]
    push_cast
    ring
  rw [p29SY, Nat.cast_add, p29NegBias, cast_negM p29M_eq_pow p29Mask_eq, spread_c29U,
    spread_c29Bias, Nat.cast_sum, sum_congr rfl hterm, Finset.sum_add_distrib,
    packEval_eq_sum, p29X_pull, Nat.cast_sum]
  push_cast
  ring

/-- Grouping a cleared sparse evaluation of bidegree `(30, 30)` by the `y`-degree. -/
theorem evalSparseBivarCleared_eq_grouped_y30 {R : Type*} [CommRing R] (a b c d : R) :
    ∀ terms : List SparseBivarTerm, (∀ t ∈ terms, t.yPow ≤ 30) →
      evalSparseBivarCleared terms 30 30 a b c d =
        ∑ y ∈ range 31, c ^ y * d ^ (30 - y) *
          (terms.map fun t => if t.yPow = y then
            (t.coeff : R) * (a ^ t.xPow * b ^ (30 - t.xPow)) else 0).sum
  | [], _ => by simp [evalSparseBivarCleared]
  | t :: ts, h => by
    rw [evalSparseBivarCleared, evalSparseBivarCleared_eq_grouped_y30 a b c d ts
      (fun u hu => h u (by simp [hu]))]
    simp only [List.map_cons, List.sum_cons, mul_add, Finset.sum_add_distrib]
    congr 1
    simp only [mul_ite, mul_zero]
    rw [Finset.sum_ite_eq (range 31) t.yPow, if_pos (mem_range.mpr (by
      have := h t (by simp); omega))]
    ring

theorem p29X29_pow : (p29X ^ 29) ^ p29K = 0 := by
  rw [← pow_mul]
  exact pow_eq_zero_of_le_of_pow_eq_zero p29X_pow (by norm_num [p29N, p29K])

theorem packEval_qSubstZ_29 :
    packEval p29X p29N (qSubstZ 29 E4ZSeries) = packEval (p29X ^ 29) p29K E4ZSeries :=
  packEval_qSubstZ (by norm_num) p29X_pow (by norm_num [p29N, p29K]) _

theorem packEval_qSubstZ_58 :
    packEval p29X p29N (qSubstZ 58 E4ZSeries) =
      packEval (p29X ^ 29) p29K (qSubstZ 2 E4ZSeries) := by
  rw [packEval_qSubstZ (K := 63) (by norm_num) p29X_pow (by norm_num [p29N]),
    packEval_qSubstZ (K := 63) (by norm_num) p29X29_pow (by norm_num [p29K]), ← pow_mul]

theorem packEval_level2P_29 :
    packEval p29X p29N (level2P (qSubstZ 29 E4ZSeries) (qSubstZ 58 E4ZSeries)) =
      packEval (p29X ^ 29) p29K psi29PZ := by
  have e1 := map_quadForm (packHom p29X p29N p29X_pow) 248 (-616) 3968
    (qSubstZ 29 E4ZSeries) (qSubstZ 58 E4ZSeries)
  have e2 := map_quadForm (packHom (p29X ^ 29) p29K p29X29_pow) 248 (-616) 3968
    E4ZSeries (qSubstZ 2 E4ZSeries)
  simp only [packHom_apply] at e1 e2
  rw [level2P, e1, psi29PZ, level2P, e2, packEval_qSubstZ_29, packEval_qSubstZ_58]

theorem packEval_level2Q_29 :
    packEval p29X p29N (level2Q (qSubstZ 29 E4ZSeries) (qSubstZ 58 E4ZSeries)) =
      packEval (p29X ^ 29) p29K psi29QZ := by
  have e1 := map_quadForm (packHom p29X p29N p29X_pow) (-1) 17 (-16)
    (qSubstZ 29 E4ZSeries) (qSubstZ 58 E4ZSeries)
  have e2 := map_quadForm (packHom (p29X ^ 29) p29K p29X29_pow) (-1) 17 (-16)
    E4ZSeries (qSubstZ 2 E4ZSeries)
  simp only [packHom_apply] at e1 e2
  rw [level2Q, e1, psi29QZ, level2Q, e2, packEval_qSubstZ_29, packEval_qSubstZ_58]

theorem cast_p29Final : ((p29Final : ℕ) : ZP) = packEval p29X p29N psi29ClearedZ := by
  have h := map_evalSparseBivarCleared (packHom p29X p29N p29X_pow) psi29SparseTerms 30 30
    (level2P (qSubstZ 29 E4ZSeries) (qSubstZ 58 E4ZSeries))
    (level2Q (qSubstZ 29 E4ZSeries) (qSubstZ 58 E4ZSeries)) psi29PZ psi29QZ
  simp only [packHom_apply] at h
  rw [psi29ClearedZ, h, packEval_level2P_29, packEval_level2Q_29,
    evalSparseBivarCleared_eq_grouped_y30 _ _ _ _ _
      (fun t ht => (psi29SparseTerms_degree_le_30 t ht).2),
    ← cast_p29P, ← cast_p29Q, p29Final, cast_hornerM p29M_eq_pow p29Mask_eq]
  try dsimp only
  conv_rhs => rw [← Finset.sum_range_reflect]
  refine sum_congr rfl fun j hj => ?_
  have hj' : j < 31 := mem_range.mp hj
  rw [p29PowQ, cast_powTab_getD p29M_eq_pow p29Mask_eq p29Q 1 31 j hj', Nat.cast_one, one_mul,
    cast_p29SY, packEval_psi29TSer p29X29_pow, show 31 - 1 - j = 30 - j by omega,
    show 30 - (30 - j) = j by omega]
  ring

/-! ### The wide coefficient bound -/

/-- The wide weight `7/8`. -/
noncomputable def p29Rho : ℝ := ((7 : ℕ) : ℝ) / 2 ^ 3

theorem p29Rho_pos : 0 < p29Rho := by unfold p29Rho; positivity

theorem p29Rho_le_one : p29Rho ≤ 1 := by unfold p29Rho; norm_num

theorem p29_wsum_E : wsum p29Rho p29N E4ZSeries ≤ (p29UE : ℝ) / 2 ^ p29SC :=
  wsum_E4ZSeries_le 7 3 p29UE (by norm_num [p29N]) (by norm_num [p29N]) p29WE_le

theorem p29_wsum_E2 : wsum p29Rho p29N (qSubstZ 2 E4ZSeries) ≤ (p29UE2 : ℝ) / 2 ^ p29SC := by
  refine (wsum_qSubstZ_le p29Rho_pos.le (by norm_num) coeffNonneg_E4ZSeries).trans ?_
  have e : p29Rho ^ 2 = ((49 : ℕ) : ℝ) / 2 ^ 6 := by unfold p29Rho; norm_num
  rw [e]
  exact wsum_E4ZSeries_le 49 6 p29UE2 (by norm_num [p29N]) (by norm_num [p29N]) p29WE2_le

theorem p29_wsum_E29 : wsum p29Rho p29N (qSubstZ 29 E4ZSeries) ≤ (p29U29 : ℝ) / 2 ^ p29SC := by
  refine (wsum_qSubstZ_le p29Rho_pos.le (by norm_num) coeffNonneg_E4ZSeries).trans ?_
  refine (wsum_mono_r (pow_nonneg p29Rho_pos.le _)
    (show p29Rho ^ 29 ≤ ((1 : ℕ) : ℝ) / 2 ^ 5 by unfold p29Rho; norm_num)
    coeffNonneg_E4ZSeries).trans ?_
  exact wsum_E4ZSeries_le 1 5 p29U29 (by norm_num [p29N]) (by norm_num [p29N]) p29W29_le

theorem p29_wsum_E58 : wsum p29Rho p29N (qSubstZ 58 E4ZSeries) ≤ (p29U58 : ℝ) / 2 ^ p29SC := by
  refine (wsum_qSubstZ_le p29Rho_pos.le (by norm_num) coeffNonneg_E4ZSeries).trans ?_
  refine (wsum_mono_r (pow_nonneg p29Rho_pos.le _)
    (show p29Rho ^ 58 ≤ ((1 : ℕ) : ℝ) / 2 ^ 11 by unfold p29Rho; norm_num)
    coeffNonneg_E4ZSeries).trans ?_
  exact wsum_E4ZSeries_le 1 11 p29U58 (by norm_num [p29N]) (by norm_num [p29N]) p29W58_le

/-- Majorant of `P(29τ)`. -/
noncomputable def psi29Ph29Z : PowerSeries ℤ :=
  quadForm 248 616 3968 (qSubstZ 29 E4ZSeries) (qSubstZ 58 E4ZSeries)

/-- Majorant of `Q(29τ)`. -/
noncomputable def psi29Qh29Z : PowerSeries ℤ :=
  quadForm 1 17 16 (qSubstZ 29 E4ZSeries) (qSubstZ 58 E4ZSeries)

theorem coeffDom_P29 :
    CoeffDom (level2P (qSubstZ 29 E4ZSeries) (qSubstZ 58 E4ZSeries)) psi29Ph29Z := by
  simpa [psi29Ph29Z, level2P] using
    coeffDom_quadForm 248 (-616) 3968 (coeffDom_of_nonneg (coeffNonneg_qSubstZ_E4 29))
      (coeffDom_of_nonneg (coeffNonneg_qSubstZ_E4 58))

theorem coeffDom_Q29 :
    CoeffDom (level2Q (qSubstZ 29 E4ZSeries) (qSubstZ 58 E4ZSeries)) psi29Qh29Z := by
  simpa [psi29Qh29Z, level2Q] using
    coeffDom_quadForm (-1) 17 (-16) (coeffDom_of_nonneg (coeffNonneg_qSubstZ_E4 29))
      (coeffDom_of_nonneg (coeffNonneg_qSubstZ_E4 58))

theorem p29_wsum_Ph :
    wsum p29Rho p29N psi29PhZ ≤ (quadNat 248 616 3968 p29UE p29UE2 : ℝ) / 2 ^ (2 * p29SC) := by
  refine (wsum_quadForm_le p29Rho_pos.le (by norm_num) (by norm_num) (by norm_num)
    coeffNonneg_E4ZSeries (coeffNonneg_qSubstZ_E4 2)).trans ?_
  rw [quadNat_div]
  push_cast
  exact quad_mono (by norm_num) (by norm_num) (by norm_num)
    (wsum_nonneg p29Rho_pos.le coeffNonneg_E4ZSeries) p29_wsum_E
    (wsum_nonneg p29Rho_pos.le (coeffNonneg_qSubstZ_E4 2)) p29_wsum_E2

theorem p29_wsum_Qh :
    wsum p29Rho p29N psi29QhZ ≤ (quadNat 1 17 16 p29UE p29UE2 : ℝ) / 2 ^ (2 * p29SC) := by
  refine (wsum_quadForm_le p29Rho_pos.le (by norm_num) (by norm_num) (by norm_num)
    coeffNonneg_E4ZSeries (coeffNonneg_qSubstZ_E4 2)).trans ?_
  rw [quadNat_div]
  push_cast
  exact quad_mono (by norm_num) (by norm_num) (by norm_num)
    (wsum_nonneg p29Rho_pos.le coeffNonneg_E4ZSeries) p29_wsum_E
    (wsum_nonneg p29Rho_pos.le (coeffNonneg_qSubstZ_E4 2)) p29_wsum_E2

theorem p29_wsum_Ph29 :
    wsum p29Rho p29N psi29Ph29Z ≤ (quadNat 248 616 3968 p29U29 p29U58 : ℝ) / 2 ^ (2 * p29SC) := by
  refine (wsum_quadForm_le p29Rho_pos.le (by norm_num) (by norm_num) (by norm_num)
    (coeffNonneg_qSubstZ_E4 29) (coeffNonneg_qSubstZ_E4 58)).trans ?_
  rw [quadNat_div]
  push_cast
  exact quad_mono (by norm_num) (by norm_num) (by norm_num)
    (wsum_nonneg p29Rho_pos.le (coeffNonneg_qSubstZ_E4 29)) p29_wsum_E29
    (wsum_nonneg p29Rho_pos.le (coeffNonneg_qSubstZ_E4 58)) p29_wsum_E58

theorem p29_wsum_Qh29 :
    wsum p29Rho p29N psi29Qh29Z ≤ (quadNat 1 17 16 p29U29 p29U58 : ℝ) / 2 ^ (2 * p29SC) := by
  refine (wsum_quadForm_le p29Rho_pos.le (by norm_num) (by norm_num) (by norm_num)
    (coeffNonneg_qSubstZ_E4 29) (coeffNonneg_qSubstZ_E4 58)).trans ?_
  rw [quadNat_div]
  push_cast
  exact quad_mono (by norm_num) (by norm_num) (by norm_num)
    (wsum_nonneg p29Rho_pos.le (coeffNonneg_qSubstZ_E4 29)) p29_wsum_E29
    (wsum_nonneg p29Rho_pos.le (coeffNonneg_qSubstZ_E4 58)) p29_wsum_E58

/-- The wide majorant. -/
noncomputable def psi29WMaj : PowerSeries ℤ :=
  evalSparseBivarCleared (absTerms psi29SparseTerms) 30 30 psi29Ph29Z psi29Qh29Z psi29PhZ psi29QhZ

theorem coeffDom_psi29ClearedZ : CoeffDom psi29ClearedZ psi29WMaj :=
  coeffDom_evalSparseBivarCleared 30 30 coeffDom_P29 coeffDom_Q29 coeffDom_psi29PZ
    coeffDom_psi29QZ psi29SparseTerms

/-- The scaled natural-number bound of the wide majorant. -/
def p29WBound : ℕ :=
  absEvalNat 30 30 (quadNat 248 616 3968 p29U29 p29U58) (quadNat 1 17 16 p29U29 p29U58)
    (quadNat 248 616 3968 p29UE p29UE2) (quadNat 1 17 16 p29UE p29UE2) psi29SparseTerms

theorem p29_wsum_WMaj :
    wsum p29Rho p29N psi29WMaj ≤
      (p29WBound : ℝ) / (2 ^ (2 * p29SC)) ^ 30 / (2 ^ (2 * p29SC)) ^ 30 := by
  refine (wsum_evalSparseBivarCleared_le p29Rho_pos.le 30 30 coeffDom_P29.1 coeffDom_Q29.1
    coeffDom_psi29PZ.1 coeffDom_psi29QZ.1 psi29SparseTerms).trans ?_
  refine (evalSparseBivarCleared_absTerms_mono 30 30
    (wsum_nonneg p29Rho_pos.le coeffDom_P29.1) (wsum_nonneg p29Rho_pos.le coeffDom_Q29.1)
    (wsum_nonneg p29Rho_pos.le coeffDom_psi29PZ.1) (wsum_nonneg p29Rho_pos.le coeffDom_psi29QZ.1)
    p29_wsum_Ph29 p29_wsum_Qh29 p29_wsum_Ph p29_wsum_Qh psi29SparseTerms).trans (le_of_eq ?_)
  rw [evalSparseBivarCleared_absTerms_div_x 30 30 (by positivity) _ _ _ _ psi29SparseTerms
      (fun t ht => (psi29SparseTerms_degree_le_30 t ht).1),
    evalSparseBivarCleared_absTerms_div_y 30 30 (by positivity) _ _ _ _ psi29SparseTerms
      (fun t ht => (psi29SparseTerms_degree_le_30 t ht).2),
    p29WBound, absEvalNat_cast, div_div]

theorem p29WBound_lt :
    (p29WBound : ℝ) / (2 ^ (2 * p29SC)) ^ 30 / (2 ^ (2 * p29SC)) ^ 30 / p29Rho ^ (p29N - 1) <
      2 ^ p29S := by
  have hltR : (p29WBound : ℝ) * 8 ^ (p29N - 1) < 7 ^ (p29N - 1) * 2 ^ (p29S + 120 * p29SC) := by
    have h := p29WideBound_lt
    generalize hW : absEvalNat 30 30 (quadNat 248 616 3968 p29U29 p29U58)
      (quadNat 1 17 16 p29U29 p29U58) (quadNat 248 616 3968 p29UE p29UE2)
      (quadNat 1 17 16 p29UE p29UE2) psi29SparseTerms = W at h
    generalize hn : p29N - 1 = n at h
    generalize hs : p29S + 120 * p29SC = s at h
    rw [p29WBound, hW]
    exact cast_wide_lt_shift h
  have hr8 : p29Rho ^ (p29N - 1) * 8 ^ (p29N - 1) = 7 ^ (p29N - 1) := by
    rw [← mul_pow, show p29Rho * 8 = 7 by unfold p29Rho; norm_num]
  have hs : ((2 : ℝ) ^ (2 * p29SC)) ^ 30 * (2 ^ (2 * p29SC)) ^ 30 = 2 ^ (120 * p29SC) := by
    rw [← pow_mul, ← pow_add, show 2 * p29SC * 30 + 2 * p29SC * 30 = 120 * p29SC by ring]
  have hpos : 0 < p29Rho ^ (p29N - 1) := pow_pos p29Rho_pos _
  have e : (p29WBound : ℝ) / (2 ^ (2 * p29SC)) ^ 30 / (2 ^ (2 * p29SC)) ^ 30 /
      p29Rho ^ (p29N - 1) =
      (p29WBound : ℝ) * 8 ^ (p29N - 1) / (2 ^ (120 * p29SC) * 7 ^ (p29N - 1)) := by
    rw [eq_div_iff (by positivity), ← hr8, ← hs]
    exact div3_mul_cancel (by positivity) hpos.ne'
  rw [e, div_lt_iff₀ (by positivity)]
  calc (p29WBound : ℝ) * 8 ^ (p29N - 1) < 7 ^ (p29N - 1) * 2 ^ (p29S + 120 * p29SC) := hltR
    _ = 2 ^ p29S * (2 ^ (120 * p29SC) * 7 ^ (p29N - 1)) := by rw [pow_add]; ring

theorem psi29ClearedZ_coeff_lt {n : ℕ} (hn : n < p29N) :
    |PowerSeries.coeff n psi29ClearedZ| < 2 ^ p29S := by
  have hn0 := coeffDom_psi29ClearedZ.1
  have h1 : |PowerSeries.coeff n psi29ClearedZ| ≤ PowerSeries.coeff n psi29WMaj :=
    coeffDom_psi29ClearedZ.2 n
  have hc := coeff_mul_pow_le_wsum p29Rho_pos.le hn0 hn
  have hfin := le_div_pow_of_mul_pow_le p29Rho_pos p29Rho_le_one (Nat.le_sub_one_of_lt hn)
    (le_trans (mul_nonneg (by exact_mod_cast hn0 n) (pow_nonneg p29Rho_pos.le n))
      (hc.trans p29_wsum_WMaj)) (hc.trans p29_wsum_WMaj)
  have hcoeffR : ((|PowerSeries.coeff n psi29ClearedZ| : ℤ) : ℝ) < 2 ^ p29S :=
    lt_of_le_of_lt ((Int.cast_le.mpr h1).trans hfin) p29WBound_lt
  exact int_lt_two_pow_of_real hcoeffR

/-! ### Conclusion -/

theorem psi29ClearedZ_coeff_eq_zero : ∀ n < p29N, PowerSeries.coeff n psi29ClearedZ = 0 := by
  refine coeff_eq_zero_of_packEval_eq_zero p29M_eq_pow (fun n hn => psi29ClearedZ_coeff_lt hn) ?_
  have h := cast_p29Final
  rw [p29Final_eq_zero, Nat.cast_zero] at h
  exact h.symm

/-- **The cleared `Ψ₂₉` vanishes**: `Σ c_{xy} P(29τ)^x Q(29τ)^{30−x} P(τ)^y Q(τ)^{30−y} = 0` as a
modular form of weight `480` on `Γ₀(58)`. -/
theorem psi29ClearedForm_eq_zero : psi29ClearedForm = 0 := by
  refine psi29ClearedForm_eq_zero_of_coeff fun n hn => ?_
  rw [psi29ClearedForm_qExpansion_eq_map, PowerSeries.coeff_map,
    psi29ClearedZ_coeff_eq_zero n (by simpa [p29N] using hn), map_zero]

/-! ### The modular equation -/

open UpperHalfPlane in
/-- The `Γ₀(2)+` Hauptmodul as the quotient `P / Q` of two weight-8 forms in `E₄(τ)`, `E₄(2τ)`
(`= q⁻¹ + 4372 q + …`; `Q = 3600 Δ₂` does not vanish on `ℍ`, proved in the level-2 layer). -/
noncomputable def hauptT58 (τ : ℍ) : ℂ :=
  level2P (E4 τ) (E4 (scaleGL 2 • τ)) / level2Q (E4 τ) (E4 (scaleGL 2 • τ))

open UpperHalfPlane in
theorem scaleGL_smul_scaleGL (d e : ℕ) [NeZero d] [NeZero e] [NeZero (d * e)] (τ : ℍ) :
    scaleGL d • (scaleGL e • τ) = scaleGL (d * e) • τ := by
  ext
  rw [coe_scaleGL_smul, coe_scaleGL_smul, coe_scaleGL_smul]
  push_cast
  ring

open UpperHalfPlane in
/-- The cleared modular equation at every `τ`. -/
theorem psi29_cleared_eq_zero (τ : ℍ) :
    evalSparseBivarCleared psi29SparseTerms 30 30
        (level2P (E4 (scaleGL 29 • τ)) (E4 (scaleGL 58 • τ)))
        (level2Q (E4 (scaleGL 29 • τ)) (E4 (scaleGL 58 • τ)))
        (level2P (E4 τ) (E4 (scaleGL 2 • τ)))
        (level2Q (E4 τ) (E4 (scaleGL 2 • τ))) = 0 := by
  rw [← psi29ClearedForm_apply, psi29ClearedForm_eq_zero]
  rfl

open UpperHalfPlane in
/-- **The degree-29 modular equation**: `Ψ₂₉(T(29τ), T(τ)) = 0` wherever the denominators
`Q(τ)`, `Q(29τ)` do not vanish. -/
theorem psi29_modular_equation (τ : ℍ)
    (hQ : level2Q (E4 τ) (E4 (scaleGL 2 • τ)) ≠ 0)
    (hQ29 : level2Q (E4 (scaleGL 29 • τ)) (E4 (scaleGL 2 • (scaleGL 29 • τ))) ≠ 0) :
    evalSparseBivarC psi29SparseTerms (hauptT58 (scaleGL 29 • τ)) (hauptT58 τ) = 0 := by
  have h := psi29_cleared_eq_zero τ
  rw [← scaleGL_smul_scaleGL 2 29 τ, ← evalSparseBivarClearedC_eq_evalSparseBivarCleared,
    evalSparseBivarClearedC_eq_den_mul_eval _ _ _ _ _ _ _ hQ29 hQ
      psi29SparseTerms_degree_le_30] at h
  rcases mul_eq_zero.mp h with h0 | h0
  · exact absurd h0 (mul_ne_zero (pow_ne_zero _ hQ29) (pow_ne_zero _ hQ))
  · exact h0

end Ripple.Number.Modular
