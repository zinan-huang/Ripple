import Ripple.Number.Modular.SturmPackedEval
import Ripple.Number.Modular.SturmPackedCore
import Ripple.Number.Modular.SturmCRTBound

/-!
# Level-41 Sturm certificate by Kronecker packing

Pack the first `N + 1` coefficients (`N = phi41FrickeSturmBound = 1765`) of
`phi41Level41ClearedEulerQExpansionZ` into one residue modulo `2 ^ (s * (N + 1))` with slot width
`s = 7469 > log₂ phi41HeightBound + 1`. Every series operation becomes one masked big-integer
operation, which the kernel evaluates with GMP (`packFinal_eq_zero`, in `SturmPackedEval`).
The evaluation uses `1728 Δ = E₄³ - E₆²` and scales all four inputs by `1728`, so it computes
`1728 ^ 84` times the packed expansion. That value is `0`; since `1728 ^ 84 = 2 ^ 504 · 27 ^ 84`
and the spare slot absorbs the factor `2 ^ 504`, and every coefficient below `N` is below
`2 ^ s` in absolute value (`phi41_final_coeff_bound`), every coefficient below `N` vanishes
(`phi41Level41FrickeCoefficientCertificate_proof`). The `q⁴¹` side is packed in `44` compact slots
(`41 · 44 ≥ N + 1`). The statements about the first `3529` coefficients follow from this one by the
Fricke-halved Sturm theorem (`Phi41FrickeSturm`).
-/

namespace Ripple.Number.Modular

open Finset

/-! ### Soundness -/

/-- `packM = 2 ^ (packSlot * packN)`, stated in this module so that the power carries the same
instances as the lemmas of `SturmPackedCore` (`SturmPackedEval` does not import Mathlib). -/
theorem packM_eq_pow : packM = 2 ^ (packSlot * packN) := by
  rw [packM, Nat.shiftLeft_eq, Nat.one_mul]

/-- `packCM = 2 ^ (packCW * 44)`, stated here for the same reason. -/
theorem packCM_eq_pow : packCM = 2 ^ (packCW * 44) := by
  rw [packCM, Nat.shiftLeft_eq, Nat.one_mul]

local notation "ZP" => ZMod packM

/-- The packing point `2 ^ s`. -/
def packX : ZP := 2 ^ packSlot

theorem packX_pow : packX ^ packN = 0 :=
  two_pow_pow_eq_zero packM_eq_pow

theorem packN_le : packN ≤ 41 * 44 := by
  norm_num [packN]

theorem packX_pull_pow : (packX ^ 41) ^ 44 = 0 := by
  rw [← pow_mul]
  exact pow_eq_zero_of_le_of_pow_eq_zero packX_pow packN_le

theorem packX_pull : packX ^ 41 = (2 : ZP) ^ (41 * packSlot) := by
  rw [packX, ← pow_mul, mul_comm]

/-- Packed `E₆`: `1 - 504 Σ_{m<n} σ₅(m) xᵐ`. -/
theorem packEval_E6ZSeries {R : Type*} [CommRing R] (x : R) {n : ℕ} (hn : 0 < n) :
    packEval x n E6ZSeries =
      1 - 504 * ∑ m ∈ range n, ((ArithmeticFunction.sigma 5 m : ℕ) : R) * x ^ m := by
  rw [packEval_eq_sum]
  have hterm : ∀ m ∈ range n, ((PowerSeries.coeff m E6ZSeries : ℤ) : R) * x ^ m =
      (if m = 0 then 1 else 0) - 504 * (((ArithmeticFunction.sigma 5 m : ℕ) : R) * x ^ m) := by
    intro m _
    rcases m with _ | m
    · simp [coeff_E6ZSeries, E6CoeffZ]
    · simp only [coeff_E6ZSeries, E6CoeffZ, Nat.add_one_ne_zero, if_false]
      push_cast
      ring
  rw [sum_congr rfl hterm, Finset.sum_sub_distrib, ← Finset.mul_sum]
  congr 1
  simp only [Finset.sum_ite_eq', Finset.mem_range, hn, if_true]

/-- `1728 Δ = E₄³ - E₆²` after packing. -/
theorem packEval_delta_1728 {R : Type*} [CommRing R] {x : R} {n : ℕ} (hx : x ^ n = 0) :
    1728 * packEval x n deltaEulerSeriesZ =
      packEval x n E4ZSeries ^ 3 - packEval x n E6ZSeries ^ 2 := by
  have h := congrArg (packHom x n hx) delta_1728_identity
  simp only [map_sub, map_pow, map_mul, map_ofNat, packHom_apply, zsmul_eq_mul,
    Int.cast_ofNat] at h
  exact h

theorem cast_packE4 : ((packE4 : ℕ) : ZP) = packEval packX packN E4ZSeries := by
  rw [packE4, spread_e4Pack packSlot 12 packN (by norm_num [packN])
    (by norm_num [packN]) (by norm_num [packN]),
    packEval_eq_sum]
  push_cast
  refine sum_congr rfl fun m _ => ?_
  rw [coeff_E4ZSeries, ← e4Digit_cast, packX]
  push_cast
  ring

theorem cast_packE6 : ((packE6 : ℕ) : ZP) = packEval packX packN E6ZSeries := by
  have hs : ((∑ m ∈ range packN,
      ArithmeticFunction.sigma 5 m * 2 ^ (packSlot * m) : ℕ) : ZP) =
      ∑ m ∈ range packN, ((ArithmeticFunction.sigma 5 m : ℕ) : ZP) * packX ^ m := by
    push_cast
    refine sum_congr rfl fun m _ => ?_
    rw [packX, ← pow_mul]
  rw [packE6, cast_subM packM_eq_pow packMask_eq, Nat.cast_mul, packS5,
    spread_sigmaPack5 packSlot 12 packN (by norm_num [packN])
      (by norm_num [packN]), hs,
    packEval_E6ZSeries packX (by norm_num [packN] : 0 < packN), Nat.cast_one, Nat.cast_ofNat]

theorem cast_packC0 : ((packC0 : ℕ) : ZP) = packEval packX packN E4ZSeries ^ 3 := by
  rw [packC0, cast_mulM packM_eq_pow packMask_eq, cast_mulM packM_eq_pow packMask_eq, cast_packE4]
  ring

theorem cast_packC :
    ((packC : ℕ) : ZP) = 1728 * packEval packX packN (E4ZSeries ^ 3) := by
  rw [packC, Nat.cast_mul, cast_packC0, packEval_E4ZSeries_cube packX_pow]
  norm_num

theorem cast_packD :
    ((packD : ℕ) : ZP) = 1728 * packEval packX packN deltaEulerSeriesZ := by
  rw [packD, cast_subM packM_eq_pow packMask_eq, cast_mulM packM_eq_pow packMask_eq, cast_packC0,
    cast_packE6, packEval_delta_1728 packX_pow]
  ring

/-! ### The compact ring and the grouped sums `T_y` -/

local notation "KZ" => ZMod packCM

/-- The compact packing point `2 ^ packCW`. -/
def compX : KZ := 2 ^ packCW

theorem compX_pow : compX ^ 44 = 0 :=
  two_pow_pow_eq_zero packCM_eq_pow

theorem cast_compE4 : ((compE4 : ℕ) : KZ) = packEval compX 44 E4ZSeries := by
  rw [compE4, e4Pack_eq_sum (w := packCW) (n := 44) (by norm_num [packCW]) (by norm_num)
    (by norm_num), packEval_eq_sum]
  push_cast
  refine sum_congr rfl fun m _ => ?_
  rw [coeff_E4ZSeries, ← e4Digit_cast, compX]
  push_cast
  ring

theorem cast_compE6 : ((compE6 : ℕ) : KZ) = packEval compX 44 E6ZSeries := by
  have hs : ((∑ m ∈ range 44,
      ArithmeticFunction.sigma 5 m * 2 ^ (packCW * m) : ℕ) : KZ) =
      ∑ m ∈ range 44, ((ArithmeticFunction.sigma 5 m : ℕ) : KZ) * compX ^ m := by
    push_cast
    refine sum_congr rfl fun m _ => ?_
    rw [compX, ← pow_mul]
  rw [compE6, cast_subM packCM_eq_pow packCMask_eq, Nat.cast_mul,
    sigmaPack_eq 5 packCW (by norm_num [packCW]) (by norm_num), hs,
    packEval_E6ZSeries compX (by norm_num : 0 < 44), Nat.cast_one, Nat.cast_ofNat]

theorem cast_compA0 : ((compA0 : ℕ) : KZ) = packEval compX 44 E4ZSeries ^ 3 := by
  rw [compA0, cast_mulM packCM_eq_pow packCMask_eq, cast_mulM packCM_eq_pow packCMask_eq, cast_compE4]
  ring

theorem cast_compA : ((compA : ℕ) : KZ) = 1728 * packEval compX 44 E4ZSeries ^ 3 := by
  rw [compA, Nat.cast_mul, cast_compA0]
  norm_num

theorem cast_compB : ((compB : ℕ) : KZ) = 1728 * packEval compX 44 deltaEulerSeriesZ := by
  rw [compB, cast_subM packCM_eq_pow packCMask_eq, cast_mulM packCM_eq_pow packCMask_eq, cast_compA0,
    cast_compE6, packEval_delta_1728 compX_pow]
  ring

theorem cast_compL {x : ℕ} (hx : x ≤ 42) :
    ((compL.getD x 0 : ℕ) : KZ) =
      (1728 * packEval compX 44 E4ZSeries ^ 3) ^ x *
        (1728 * packEval compX 44 deltaEulerSeriesZ) ^ (42 - x) := by
  rw [compL, getD_map_range (n := 43) (y := x) _ (by omega)]
  try dsimp only
  rw [cast_mulM packCM_eq_pow packCMask_eq, compPowA, compPowB,
    cast_powTab_getD packCM_eq_pow packCMask_eq compA 1 43 x (by omega),
    cast_powTab_getD packCM_eq_pow packCMask_eq compB 1 43 (42 - x) (by omega),
    Nat.cast_one, one_mul, one_mul, cast_compA, cast_compB]

/-- The `y`-group of the cleared expansion on the `q⁴¹` side (variable `t = q⁴¹`), with the
scaling `1728 ^ 42` of `A = 1728 E₄³` and `B = 1728 Δ`. -/
noncomputable def phi41TSer (y : ℕ) : PowerSeries ℤ :=
  (phi41SparseTerms.map fun t => if t.yPow = y then
    (t.coeff * 1728 ^ 42) • ((E4ZSeries ^ 3) ^ t.xPow * deltaEulerSeriesZ ^ (42 - t.xPow))
    else 0).sum

theorem packEval_phi41TSer {R : Type*} [CommRing R] {z : R} (hz : z ^ 44 = 0) (y : ℕ) :
    packEval z 44 (phi41TSer y) =
      (phi41SparseTerms.map fun t => if t.yPow = y then
        (t.coeff : R) * ((1728 * packEval z 44 E4ZSeries ^ 3) ^ t.xPow *
          (1728 * packEval z 44 deltaEulerSeriesZ) ^ (42 - t.xPow)) else 0).sum := by
  rw [← packHom_apply z 44 hz, phi41TSer, map_list_sum, List.map_map]
  refine congrArg List.sum (List.map_congr_left fun t ht => ?_)
  simp only [Function.comp_apply]
  split_ifs
  · have hx := (phi41SparseTerms_degree_le_42 t ht).1
    rw [map_zsmul, map_mul, map_pow, map_pow, map_pow, packHom_apply, packHom_apply,
      zsmul_eq_mul, mul_pow, mul_pow]
    have e : (1728 : R) ^ 42 = 1728 ^ t.xPow * 1728 ^ (42 - t.xPow) := by
      rw [← pow_add, Nat.add_sub_cancel' hx]
    rw [Int.cast_mul, Int.cast_pow, Int.cast_ofNat, e]
    ring
  · exact map_zero _

theorem natCast_lt_two_pow {a k : ℕ} (h : a < 2 ^ k) : (a : ℤ) < 2 ^ k := by
  have h' := (Nat.cast_lt (α := ℤ)).mpr h
  rwa [Nat.cast_pow, Nat.cast_ofNat] at h'

/-- `Σ |c| · 1728 ^ 42 · 10 ^ 545 < 2 ^ (packCW - 1)` over the sparse terms. Stated in exactly
the form used below: elaborating a definitional unfolding of this sum would evaluate it. -/
theorem phi41Terms_weighted_bound :
    (phi41SparseTerms.map fun t => t.coeff.natAbs * (1728 ^ 42 * 10 ^ 545)).sum <
      2 ^ (packCW - 1) := by
  decide +kernel

theorem phi41TSer_coeff_lt (y : ℕ) {m : ℕ} (hm : m < 44) :
    |PowerSeries.coeff m (phi41TSer y)| < 2 ^ (packCW - 1) := by
  rw [phi41TSer, map_list_sum, List.map_map]
  refine lt_of_le_of_lt (abs_list_sum_map_le _
    (fun t => t.coeff.natAbs * (1728 ^ 42 * 10 ^ 545)) _ ?_) ?_
  · intro t ht
    simp only [Function.comp_apply]
    split_ifs
    · have hx := (phi41SparseTerms_degree_le_42 t ht).1
      have hq := Qrow_bound_pull t.xPow m hx (by
        rw [show (phi41Level41SturmBound + 40) / 41 = 87 by
          norm_num [phi41Level41SturmBound]]
        omega)
      rw [map_zsmul, smul_eq_mul, abs_mul, abs_mul,
        abs_of_pos (by positivity : (0 : ℤ) < 1728 ^ 42)]
      calc |t.coeff| * 1728 ^ 42 * |PowerSeries.coeff m
            ((E4ZSeries ^ 3) ^ t.xPow * deltaEulerSeriesZ ^ (42 - t.xPow))|
          ≤ |t.coeff| * 1728 ^ 42 * (QrowPullBound : ℤ) := by gcongr
        _ = ((t.coeff.natAbs * (1728 ^ 42 * 10 ^ 545) : ℕ) : ℤ) := by
          rw [Int.abs_eq_natAbs, QrowPullBound]
          push_cast
          ring
    · rw [map_zero, abs_zero]
      exact Int.natCast_nonneg _
  · exact natCast_lt_two_pow phi41Terms_weighted_bound

theorem cast_compT (y : ℕ) : ((compT y : ℕ) : KZ) = packEval compX 44 (phi41TSer y) := by
  rw [compT, compTs, cast_bucketPN packCM_eq_pow packCMask_eq _ _ _
    (fun t ht => Nat.lt_succ_of_le (phi41SparseTerms_degree_le_42 t ht).2),
    packEval_phi41TSer compX_pow]
  refine congrArg List.sum (List.map_congr_left fun t ht => ?_)
  split_ifs
  · rw [cast_compL (phi41SparseTerms_degree_le_42 t ht).1]
  · rfl

theorem compBias_eq : compBias = 2 ^ (packCW - 1) * ∑ m ∈ range 44, 2 ^ (packCW * m) := by
  rw [compBias, one_add_geomF packCW 7 43 (by norm_num)]

theorem compU_eq (y : ℕ) :
    compU y = ∑ m ∈ range 44,
      (PowerSeries.coeff m (phi41TSer y) + 2 ^ (packCW - 1)).toNat * 2 ^ (packCW * m) := by
  rw [compU, compBias_eq]
  exact biased_digits packCM_eq_pow (by norm_num [packCW]) _ (fun m hm => phi41TSer_coeff_lt y hm)
    _ (cast_compT y)

/-! ### Back to the wide ring -/

theorem spread_compU (y : ℕ) :
    combSpread (41 * packSlot - packCW) packCW 44 (compU y) = ∑ m ∈ range 44,
      (PowerSeries.coeff m (phi41TSer y) + 2 ^ (packCW - 1)).toNat * 2 ^ (41 * packSlot * m) := by
  rw [compU_eq, combSpread_eq (by norm_num) (by norm_num) (by norm_num [packCW, packSlot])
    (fun m => (PowerSeries.coeff m (phi41TSer y) + 2 ^ (packCW - 1)).toNat)
    (fun m hm => biased_digit_lt (by norm_num [packCW]) (phi41TSer_coeff_lt y hm)),
    show 41 * packSlot - packCW + packCW = 41 * packSlot by norm_num [packCW, packSlot]]

theorem spread_compBias :
    spread packCW (41 * packSlot) compBias 7 0 44 =
      ∑ m ∈ range 44, 2 ^ (packCW - 1) * 2 ^ (41 * packSlot * m) := by
  rw [compBias_eq, Finset.mul_sum]
  exact spread_of_digits packCW (41 * packSlot) 7 44 (fun _ => 2 ^ (packCW - 1))
    (fun _ _ => Nat.pow_lt_pow_right (by norm_num) (by norm_num [packCW])) (by norm_num)

theorem cast_packSY (y : ℕ) :
    ((packSY y : ℕ) : ZP) = packEval (packX ^ 41) 44 (phi41TSer y) := by
  have hterm : ∀ m ∈ range 44,
      ((((PowerSeries.coeff m (phi41TSer y) + 2 ^ (packCW - 1)).toNat *
          2 ^ (41 * packSlot * m) : ℕ)) : ZP) =
        ((PowerSeries.coeff m (phi41TSer y) : ℤ) : ZP) * ((2 : ZP) ^ (41 * packSlot)) ^ m +
          2 ^ (packCW - 1) * 2 ^ (41 * packSlot * m) := by
    intro m hm
    have h0 : 0 ≤ PowerSeries.coeff m (phi41TSer y) + 2 ^ (packCW - 1) := by
      have := abs_lt.mp (phi41TSer_coeff_lt y (mem_range.mp hm))
      linarith
    rw [Nat.cast_mul,
      ← Int.cast_natCast (PowerSeries.coeff m (phi41TSer y) + 2 ^ (packCW - 1)).toNat,
      Int.toNat_of_nonneg h0]
    push_cast
    ring
  rw [packSY, Nat.cast_add, packNegBias, cast_negM packM_eq_pow packMask_eq, spread_compU,
    spread_compBias, Nat.cast_sum, sum_congr rfl hterm, Finset.sum_add_distrib,
    packEval_eq_sum, packX_pull, Nat.cast_sum]
  push_cast
  ring

/-! ### The final value -/

theorem cast_packFinal :
    ((packFinal : ℕ) : ZP) =
      1728 ^ 84 * packEval packX packN phi41Level41ClearedEulerQExpansionZ := by
  have hA : packEval (packX ^ 41) 44 E4ZSeries ^ 3 =
      packEval packX packN (qPullback41Z (E4ZSeries ^ 3)) := by
    rw [packEval_qPullback41Z packX_pow packN_le, packEval_E4ZSeries_cube packX_pull_pow]
  have hB : packEval (packX ^ 41) 44 deltaEulerSeriesZ =
      packEval packX packN (qPullback41Z deltaEulerSeriesZ) := by
    rw [packEval_qPullback41Z packX_pow packN_le]
  have h := map_evalSparseBivarCleared (packHom packX packN packX_pow) phi41SparseTerms 42 42
    (qPullback41Z (E4ZSeries ^ 3)) (qPullback41Z deltaEulerSeriesZ) (E4ZSeries ^ 3)
    deltaEulerSeriesZ
  simp only [packHom_apply] at h
  rw [phi41Level41ClearedEulerQExpansionZ, h,
    ← evalSparseBivarCleared_smul _ _ _ _ _ _ phi41SparseTerms_degree_le_42,
    evalSparseBivarCleared_eq_grouped_y _ _ _ _ _
      (fun t ht => (phi41SparseTerms_degree_le_42 t ht).2),
    ← cast_packC, ← cast_packD, packFinal, cast_hornerM packM_eq_pow packMask_eq]
  try dsimp only
  conv_rhs => rw [← Finset.sum_range_reflect]
  refine sum_congr rfl fun j hj => ?_
  have hj' : j < 43 := mem_range.mp hj
  rw [packPowD, cast_powTab_getD packM_eq_pow packMask_eq packD 1 43 j hj', Nat.cast_one, one_mul,
    cast_packSY, packEval_phi41TSer packX_pull_pow, hA, hB, show 43 - 1 - j = 42 - j by omega,
    show 42 - (42 - j) = j by omega]
  ring

theorem packEval_cleared_eq_zero :
    (1728 : ZP) ^ 84 * packEval packX packN phi41Level41ClearedEulerQExpansionZ = 0 := by
  rw [← cast_packFinal, packFinal_eq_zero, Nat.cast_zero]

theorem phi41HeightBound_lt_two_pow : phi41HeightBound < 2 ^ packSlot := by
  decide +kernel

/-- The Fricke-halved Sturm bound: half the level-41 Sturm bound `3529`, rounded up
(`2 * 1765 ≥ 3529`). `Phi41Fricke` shows that the first `1765` coefficients determine the form. -/
def phi41FrickeSturmBound : ℕ := 1765

/-- The finite certificate needed after the Fricke halving: the first `1765` coefficients of the
cleared level-41 expansion vanish. -/
def phi41Level41FrickeCoefficientCertificate : Prop :=
  ∀ n : ℕ, n < phi41FrickeSturmBound →
    PowerSeries.coeff (R := ℤ) n phi41Level41ClearedEulerQExpansionZ = 0

/-- The packed certificate: the kernel evaluation `packFinal_eq_zero` and the height bound
`phi41_final_coeff_bound` (proved below `3529`, used below `1765`). -/
theorem phi41Level41FrickeCoefficientCertificate_proof :
    phi41Level41FrickeCoefficientCertificate := by
  have hrep :=
    phi41Level41ClearedEulerQExpansionZ_TruncRep_compressedMatrix phi41Level41SturmBound
  have harray :=
    ListArrayEq.phi41Level41CoeffCompressedMatrix_of_derivative_identities
      phi41Level41SturmBound
      (fun j hj => phi41LevelOneDenseRow_derivative_identity_of_base j hj
        (E4ZSeries_cubed_derivative_identity_of_E4_derivative_identity
          E4ZSeries_derivative_identity)
        deltaEulerSeriesZ_derivative_identity)
  refine coeff_eq_zero_of_scaled_packEval_eq_zero packM_eq_pow
    (rfl : packN = phi41FrickeSturmBound + 1) (by norm_num [packSlot]) ?_
    packEval_cleared_eq_zero
  intro n hn
  have hn' : n < phi41Level41SturmBound := by
    unfold phi41FrickeSturmBound at hn
    unfold phi41Level41SturmBound
    omega
  rw [hrep n hn', harray n hn']
  refine lt_of_le_of_lt (phi41_final_coeff_bound n hn') ?_
  exact_mod_cast phi41HeightBound_lt_two_pow

end Ripple.Number.Modular
