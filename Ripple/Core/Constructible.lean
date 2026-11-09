/-
  Ripple.Core.Constructible — [BAC] journal draft §5 (`sec:constructible`): bounded polynomial
  systems computing `1` with prescribed time moduli.

  * `polyFamily n` (Thm 5.1, `thm:poly-constructible`, system `eq:poly-family`):
    `u' = (1/n)(1 − u)^{n+1}`, `x' = (1 − x)(1/n)(1 − u)^{n−1}`, `u(0) = x(0) = 0`; solution
    `u = 1 − (1+t)^{−1/n}`, `1 − x = exp(1 − (1+t)^{1/n})`; exact modulus `(r+1)^n − 1`
    (`polyFamily_certified`, with the matching lower bound, so `μ_n = Θ(r^n)`).
  * `towerPIVP k` (Construction 5.4, `con:tower`): `w_j' = (1 − w_j)² ∏_{i<j} (1 − w_i)`,
    `x₁' = (1 − x₁) ∏_{j≤k} (1 − w_j)`, all initial values `0`.
  * `towerSol` (Prop 5.5, `prop:tower`): `1 − w_j = 1/(1 + L_j)`, `L₀ = t`,
    `L_{j+1} = log(1 + L_j)`, and `1 − x₁ = exp(−L_{k+1})`.
  * `tower_certified` (Thm 5.6, `thm:arbitrary`): exact modulus `E_{k+1}(r)`, the inverse of
    `L_{k+1}` (`E₀ s = s`, `E_{j+1} s = E_j(e^s − 1)`), with the matching lower bound, and
    `exp^{(k+1)}(r − 1) ≤ E_{k+1}(r) ≤ exp^{(k+1)}(r)` for `r ≥ 2`.

  The draft's proofs are complete (BAC2-PAPER.md §5). Its table after Thm 5.6 claims
  `Θ(exp^{(k+1)}(r))`; that holds for `k ≤ 1` only (for `k = 2`, `E₃(r)/exp³(r) → 0`); the
  theorem's `exp^{(k+1)}(r + O(1))` is what is formalized.
-/

import Ripple.Core.BoundedTime
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

namespace Ripple

open MvPolynomial Filter

namespace Constructible

/-! ## Thm 5.1: the polynomial family -/

/-- [BAC] journal draft system `eq:poly-family` (Thm 5.1): state `(u, x)`, output `x`. -/
noncomputable def polyFamily (n : ℕ) : PolyPIVP 2 where
  field := ![C (1 / (n : ℚ)) * (1 - X 0) ^ (n + 1),
    (1 - X 1) * C (1 / (n : ℚ)) * (1 - X 0) ^ (n - 1)]
  init := ![0, 0]
  output := 1

/-- The explicit solution `u = 1 − (1+t)^{−1/n}`, `x = 1 − exp(1 − (1+t)^{1/n})`. -/
noncomputable def polyFamilySol (n : ℕ) (t : ℝ) : Fin 2 → ℝ :=
  ![1 - (1 + t) ^ (-(1 / (n : ℝ))), 1 - Real.exp (1 - (1 + t) ^ (1 / (n : ℝ)))]

theorem rpow_inv_nat_pow {n : ℕ} (hn : 1 ≤ n) {a : ℝ} (ha : 0 ≤ a) :
    (a ^ (1 / (n : ℝ))) ^ n = a := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul ha]
  have hn0 : (n : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  rw [one_div_mul_cancel hn0, Real.rpow_one]

theorem polyFamilySol_hasDerivAt {n : ℕ} (hn : 1 ≤ n) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (polyFamilySol n) ((polyFamily n).toPIVP.field (polyFamilySol n t)) t := by
  have hnR : (n : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have h1t : 0 < 1 + t := by linarith
  have hb : HasDerivAt (fun s => 1 + s) 1 t := (hasDerivAt_id t).const_add 1
  have hu := (hb.rpow_const (p := -(1 / (n : ℝ))) (Or.inl h1t.ne')).const_sub 1
  have hx := ((hb.rpow_const (p := 1 / (n : ℝ)) (Or.inl h1t.ne')).const_sub 1).exp.const_sub 1
  refine hasDerivAt_pi.2 (Fin.forall_fin_two.2 ⟨?_, ?_⟩)
  · refine hu.congr_deriv ?_
    simp only [PolyPIVP.toPIVP, PolyPIVP.evalField, polyFamily, polyFamilySol,
      Matrix.cons_val_zero, eval₂_mul, eval₂_C, eval₂_pow, eval₂_sub, eval₂_one, eval₂_X]
    rw [sub_sub_cancel, ← Real.rpow_natCast, ← Real.rpow_mul h1t.le]
    have he : -(1 / (n : ℝ)) * ((n + 1 : ℕ) : ℝ) = -(1 / (n : ℝ)) - 1 := by
      push_cast
      rw [neg_mul, mul_add, one_div_mul_cancel hnR, mul_one]
      ring
    rw [he]
    simp only [eq_ratCast, Rat.cast_div, Rat.cast_one, Rat.cast_natCast]
    ring
  · refine hx.congr_deriv ?_
    simp only [PolyPIVP.toPIVP, PolyPIVP.evalField, polyFamily, polyFamilySol,
      Matrix.cons_val_one, Matrix.cons_val_zero, eval₂_mul, eval₂_C, eval₂_pow, eval₂_sub,
      eval₂_one, eval₂_X]
    rw [sub_sub_cancel, sub_sub_cancel, ← Real.rpow_natCast, ← Real.rpow_mul h1t.le]
    have he : -(1 / (n : ℝ)) * ((n - 1 : ℕ) : ℝ) = 1 / (n : ℝ) - 1 := by
      rw [Nat.cast_sub hn, Nat.cast_one, neg_mul, mul_sub, one_div_mul_cancel hnR, mul_one]
      ring
    rw [he]
    simp only [eq_ratCast, Rat.cast_div, Rat.cast_one, Rat.cast_natCast]
    ring

/-- [BAC] journal draft Thm 5.1 (`thm:poly-constructible`), for `n ≥ 1`: the system
`eq:poly-family` computes `1` with the exact time modulus `(r+1)^n − 1`: the bound holds past it
and fails at every `t ∈ [0, (r+1)^n − 1]`, so `μ_n(r) = Θ(r^n)`. -/
theorem polyFamily_certified {n : ℕ} (hn : 1 ≤ n) :
    ∃ btc : CertifiedBoundedTimeComputable 2 1, btc.pivp = polyFamily n ∧
      (∀ r : ℕ, btc.modulus r = ((r : ℝ) + 1) ^ n - 1) ∧
      ∀ r : ℕ, ∀ t, 0 ≤ t → t ≤ ((r : ℝ) + 1) ^ n - 1 →
        Real.exp (-(r : ℝ)) ≤ |btc.sol.trajectory t btc.pivp.output - 1| := by
  have hnpos : (0 : ℝ) < 1 / (n : ℝ) := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    positivity
  let sol : PIVP.Solution (polyFamily n).toPIVP :=
    { trajectory := polyFamilySol n
      init_cond := by
        funext i
        fin_cases i <;> simp [polyFamilySol, PolyPIVP.toPIVP, polyFamily]
      is_solution := fun t ht => polyFamilySol_hasDerivAt hn ht }
  have hx : ∀ t, sol.trajectory t (polyFamily n).output - 1 =
      -Real.exp (1 - (1 + t) ^ (1 / (n : ℝ))) := by
    intro t; simp [sol, polyFamilySol, polyFamily]
  have hbd : (polyFamily n).toPIVP.IsBounded sol.trajectory := by
    refine ⟨1, one_pos, fun t ht => (pi_norm_le_iff_of_nonneg zero_le_one).2
      (Fin.forall_fin_two.2 ⟨?_, ?_⟩)⟩
    · have h1t : (1 : ℝ) ≤ 1 + t := by linarith
      have h0 : 0 < (1 + t) ^ (-(1 / (n : ℝ))) := Real.rpow_pos_of_pos (by linarith) _
      have h1 : (1 + t) ^ (-(1 / (n : ℝ))) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos h1t (by linarith)
      show ‖1 - (1 + t) ^ (-(1 / (n : ℝ)))‖ ≤ 1
      rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith
    · have h1t : (1 : ℝ) ≤ 1 + t := by linarith
      have h1 : 1 ≤ (1 + t) ^ (1 / (n : ℝ)) := Real.one_le_rpow h1t hnpos.le
      have h0 : 0 < Real.exp (1 - (1 + t) ^ (1 / (n : ℝ))) := Real.exp_pos _
      have h2 : Real.exp (1 - (1 + t) ^ (1 / (n : ℝ))) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by linarith)
      show ‖1 - Real.exp (1 - (1 + t) ^ (1 / (n : ℝ)))‖ ≤ 1
      rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith
  -- precision `e^{−r}` holds iff `(1+t)^{1/n} > r + 1` iff `t > (r+1)^n − 1`
  have hiff : ∀ (r : ℕ) (t : ℝ), 0 ≤ t →
      ((r : ℝ) + 1 < (1 + t) ^ (1 / (n : ℝ)) ↔ ((r : ℝ) + 1) ^ n - 1 < t) := by
    intro r t ht
    have h1t : 0 ≤ 1 + t := by linarith
    have hr : (0 : ℝ) ≤ (r : ℝ) + 1 := by positivity
    have hp : 0 ≤ (1 + t) ^ (1 / (n : ℝ)) := Real.rpow_nonneg h1t _
    constructor
    · intro h
      have := pow_lt_pow_left₀ h hr (by omega : n ≠ 0)
      rw [rpow_inv_nat_pow hn h1t] at this
      linarith
    · intro h
      by_contra hc
      push_neg at hc
      have := pow_le_pow_left₀ hp hc n
      rw [rpow_inv_nat_pow hn h1t] at this
      linarith
  obtain ⟨btc, hpivp, hmod, heq⟩ := CertifiedBoundedTimeComputable.exists_of_solution
    (α := 1) (polyFamily n) sol hbd (fun r => ((r : ℝ) + 1) ^ n - 1) (fun r t ht => by
      beta_reduce at ht
      have ht0 : 0 ≤ t := by
        have : (1 : ℝ) ≤ ((r : ℝ) + 1) ^ n := one_le_pow₀ (by linarith [Nat.cast_nonneg (α := ℝ) r])
        linarith
      rw [hx, abs_neg, abs_of_pos (Real.exp_pos _), Real.exp_lt_exp]
      have := (hiff r t ht0).2 ht
      linarith)
  refine ⟨btc, hpivp, fun r => ?_, fun r t ht htr => ?_⟩
  · rw [hmod r]
    have : (1 : ℝ) ≤ ((r : ℝ) + 1) ^ n := one_le_pow₀ (by linarith [Nat.cast_nonneg (α := ℝ) r])
    exact max_eq_right (by linarith)
  · rw [heq t ht, hpivp, hx, abs_neg, abs_of_pos (Real.exp_pos _), Real.exp_le_exp]
    have : ¬ ((r : ℝ) + 1 < (1 + t) ^ (1 / (n : ℝ))) := fun h => absurd ((hiff r t ht).1 h)
      (not_lt.mpr htr)
    push_neg at this
    linarith

/-! ## Construction 5.4, Prop 5.5, Thm 5.6: the iterated-logarithm tower -/

/-- `L₀(t) = t`, `L_{j+1}(t) = log(1 + L_j(t))` (Prop 5.5). -/
noncomputable def L : ℕ → ℝ → ℝ
  | 0, t => t
  | j + 1, t => Real.log (1 + L j t)

/-- The inverse of `L_j` on `[0, ∞)`: `E₀(s) = s`, `E_{j+1}(s) = E_j(e^s − 1)`. -/
noncomputable def E : ℕ → ℝ → ℝ
  | 0, s => s
  | j + 1, s => E j (Real.exp s - 1)

/-- `L_j'(t) = ∏_{i<j} (1 + L_i(t))⁻¹`. -/
noncomputable def D (j : ℕ) (t : ℝ) : ℝ := ∏ i ∈ Finset.range j, (1 + L i t)⁻¹

theorem L_zero (j : ℕ) : L j 0 = 0 := by
  induction j with
  | zero => rfl
  | succ j ih => simp [L, ih]

theorem L_nonneg (j : ℕ) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ L j t := by
  induction j with
  | zero => exact ht
  | succ j ih => exact Real.log_nonneg (by linarith)

theorem E_nonneg (j : ℕ) {s : ℝ} (hs : 0 ≤ s) : 0 ≤ E j s := by
  induction j generalizing s with
  | zero => exact hs
  | succ j ih =>
    exact ih (by have := Real.add_one_le_exp s; linarith)

/-- `s < L_j(t) ↔ E_j(s) < t` for `s, t ≥ 0`. -/
theorem lt_L_iff (j : ℕ) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) : s < L j t ↔ E j s < t := by
  induction j generalizing s with
  | zero => rfl
  | succ j ih =>
    have hL := L_nonneg j ht
    have hs' : 0 ≤ Real.exp s - 1 := by have := Real.add_one_le_exp s; linarith
    change s < Real.log (1 + L j t) ↔ E j (Real.exp s - 1) < t
    rw [← ih hs', Real.lt_log_iff_exp_lt (by linarith)]
    constructor <;> intro h <;> linarith

theorem L_hasDerivAt (j : ℕ) {t : ℝ} (ht : 0 ≤ t) : HasDerivAt (L j) (D j t) t := by
  induction j with
  | zero =>
    rw [show D 0 t = 1 by simp [D]]
    exact hasDerivAt_id t
  | succ j ih =>
    have hpos : 0 < 1 + L j t := by linarith [L_nonneg j ht]
    have h := (ih.const_add 1).log hpos.ne'
    refine h.congr_deriv ?_
    simp only [D, Finset.prod_range_succ]
    rw [div_eq_mul_inv]

/-- The tower field ([BAC] journal draft Construction 5.4, `eq:tower`, `eq:tower-readout`) on
`Fin (k + 2)`: coordinates `j ≤ k` are `w_j`, the last one is `x₁`; the field of coordinate `i`
is `(1 − X i)^{e_i} ∏_{j < i} (1 − X j)` with `e_i = 2` for `w`, `e_i = 1` for `x₁`. -/
noncomputable def towerPIVP (k : ℕ) : PolyPIVP (k + 2) where
  field i := (1 - X i) ^ (if i = Fin.last (k + 1) then 1 else 2) *
    ∏ j ∈ Finset.univ.filter (fun j : Fin (k + 2) => j.val < i.val), (1 - X j)
  init _ := 0
  output := Fin.last (k + 1)

/-- The solution of Prop 5.5: `w_j = 1 − 1/(1 + L_j)`, `x₁ = 1 − exp(−L_{k+1})`. -/
noncomputable def towerSol (k : ℕ) (t : ℝ) (i : Fin (k + 2)) : ℝ :=
  if i = Fin.last (k + 1) then 1 - Real.exp (-L (k + 1) t) else 1 - (1 + L i.val t)⁻¹

theorem prod_filter_lt {N m : ℕ} (hm : m ≤ N) (f : ℕ → ℝ) :
    ∏ j ∈ Finset.univ.filter (fun j : Fin N => j.val < m), f j.val =
      ∏ j ∈ Finset.range m, f j := by
  have h : (Finset.univ.filter (fun j : Fin N => j.val < m)).map Fin.valEmbedding =
      Finset.range m := by
    ext x
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.valEmbedding_apply, Finset.mem_range]
    constructor
    · rintro ⟨j, hj, rfl⟩; exact hj
    · intro hx; exact ⟨⟨x, by omega⟩, hx, rfl⟩
  rw [← h, Finset.prod_map]
  rfl

/-- Prop 5.5 (`prop:tower`) and the readout: `towerSol` solves the tower system, and
`∏_{j<i} (1 − w_j) = L_i'`. -/
theorem towerSol_hasDerivAt (k : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (towerSol k) ((towerPIVP k).toPIVP.field (towerSol k t)) t := by
  have hprod : ∀ i : Fin (k + 2),
      ∏ j ∈ Finset.univ.filter (fun j : Fin (k + 2) => j.val < i.val), (1 - towerSol k t j) =
        D i.val t := by
    intro i
    have h1 : ∀ j ∈ Finset.univ.filter (fun j : Fin (k + 2) => j.val < i.val),
        1 - towerSol k t j = (1 + L j.val t)⁻¹ := by
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      have hjl : j ≠ Fin.last (k + 1) := by
        intro h; subst h; have := i.isLt; simp only [Fin.val_last] at hj; omega
      simp [towerSol, hjl]
    rw [Finset.prod_congr rfl h1, prod_filter_lt i.isLt.le (fun j => (1 + L j t)⁻¹)]
    rfl
  refine hasDerivAt_pi.2 fun i => ?_
  simp only [PolyPIVP.toPIVP, PolyPIVP.evalField, towerPIVP, eval₂_mul, eval₂_pow, eval₂_sub,
    eval₂_one, eval₂_X, eval₂_prod]
  rw [hprod i]
  by_cases hi : i = Fin.last (k + 1)
  · subst hi
    have hval : (Fin.last (k + 1)).val = k + 1 := rfl
    simp only [towerSol, if_true, pow_one, hval]
    have h := ((L_hasDerivAt (k + 1) ht).neg.exp).const_sub 1
    refine (h.congr_deriv ?_).congr_of_eventuallyEq ?_
    · simp only [sub_sub_cancel, Pi.neg_apply]; ring
    · exact Filter.Eventually.of_forall fun s => by simp
  · have hpos : 0 < 1 + L i.val t := by linarith [L_nonneg i.val ht]
    have h := (((L_hasDerivAt i.val ht).const_add 1).inv hpos.ne').const_sub 1
    simp only [towerSol, hi, if_false]
    refine (h.congr_deriv ?_).congr_of_eventuallyEq ?_
    · rw [sub_sub_cancel]
      have hne := hpos.ne'
      field_simp
    · exact Filter.Eventually.of_forall fun s => by simp [hi]

/-- [BAC] journal draft Thm 5.6 (`thm:arbitrary`): the depth-`k` tower computes `1` with
`1 − x₁(t) = exp(−L_{k+1}(t))` and the exact time modulus `E_{k+1}(r)` (the bound holds past it
and fails on `[0, E_{k+1}(r)]`); `exp^{(k+1)}(r − 1) ≤ E_{k+1}(r) ≤ exp^{(k+1)}(r)` for `r ≥ 2`
is `tower_modulus_bounds`. -/
theorem tower_certified (k : ℕ) :
    ∃ btc : CertifiedBoundedTimeComputable (k + 2) 1, btc.pivp = towerPIVP k ∧
      (∀ t, 0 ≤ t → btc.sol.trajectory t btc.pivp.output = 1 - Real.exp (-L (k + 1) t)) ∧
      (∀ r : ℕ, btc.modulus r = E (k + 1) r) ∧
      ∀ r : ℕ, ∀ t, 0 ≤ t → t ≤ E (k + 1) r →
        Real.exp (-(r : ℝ)) ≤ |btc.sol.trajectory t btc.pivp.output - 1| := by
  let sol : PIVP.Solution (towerPIVP k).toPIVP :=
    { trajectory := towerSol k
      init_cond := by
        funext i
        by_cases hi : i = Fin.last (k + 1)
        · simp [towerSol, hi, PolyPIVP.toPIVP, towerPIVP, L_zero]
        · simp [towerSol, hi, PolyPIVP.toPIVP, towerPIVP, L_zero]
      is_solution := fun t ht => towerSol_hasDerivAt k ht }
  have hout : ∀ t, sol.trajectory t (towerPIVP k).output = 1 - Real.exp (-L (k + 1) t) := by
    intro t; simp [sol, towerSol, towerPIVP]
  have hbd : (towerPIVP k).toPIVP.IsBounded sol.trajectory := by
    refine ⟨1, one_pos, fun t ht => (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_⟩
    rw [Real.norm_eq_abs, abs_le]
    by_cases hi : i = Fin.last (k + 1)
    · have h0 : 0 < Real.exp (-L (k + 1) t) := Real.exp_pos _
      have h1 : Real.exp (-L (k + 1) t) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by linarith [L_nonneg (k + 1) ht])
      subst hi
      simp only [sol, towerSol, eq_self_iff_true, if_true]
      constructor <;> linarith
    · have hL := L_nonneg i.val ht
      have h0 : 0 < (1 + L i.val t)⁻¹ := inv_pos.mpr (by linarith)
      have h1 : (1 + L i.val t)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
      simp only [sol, towerSol, hi, if_false]
      constructor <;> linarith
  obtain ⟨btc, hpivp, hmod, heq⟩ := CertifiedBoundedTimeComputable.exists_of_solution
    (α := 1) (towerPIVP k) sol hbd (fun r => E (k + 1) r) (fun r t ht => by
      beta_reduce at ht
      have hE := E_nonneg (k + 1) (Nat.cast_nonneg (α := ℝ) r)
      have ht0 : 0 ≤ t := by linarith
      rw [hout, sub_sub_cancel_left, abs_neg, abs_of_pos (Real.exp_pos _), Real.exp_lt_exp]
      have := (lt_L_iff (k + 1) (Nat.cast_nonneg r) ht0).2 ht
      linarith)
  refine ⟨btc, hpivp, fun t ht => by rw [heq t ht, hpivp, hout], fun r => ?_,
    fun r t ht htr => ?_⟩
  · rw [hmod r]
    exact max_eq_right (E_nonneg (k + 1) (Nat.cast_nonneg r))
  · rw [heq t ht, hpivp, hout, sub_sub_cancel_left, abs_neg, abs_of_pos (Real.exp_pos _),
      Real.exp_le_exp]
    have : ¬ ((r : ℝ) < L (k + 1) t) := fun h =>
      absurd ((lt_L_iff (k + 1) (Nat.cast_nonneg r) ht).1 h) (not_lt.mpr htr)
    push_neg at this
    linarith

/-- The modulus of Thm 5.6 is `exp^{(j)}(r + O(1))`: `exp^{(j)}(s − 1) ≤ E_j(s) ≤ exp^{(j)}(s)`
for `s ≥ 2`. -/
theorem tower_modulus_bounds (j : ℕ) {s : ℝ} (hs : 2 ≤ s) :
    Real.exp^[j] (s - 1) ≤ E j s ∧ E j s ≤ Real.exp^[j] s := by
  have hmono : ∀ m : ℕ, Monotone (Real.exp^[m]) := fun m => Real.exp_monotone.iterate m
  induction j generalizing s with
  | zero => simp [E]
  | succ j ih =>
    have he : (2 : ℝ) ≤ Real.exp s - 1 := by
      have h1 := Real.add_one_le_exp s
      have h2 : (Real.exp 1) ≥ 2 := by
        have := Real.add_one_le_exp (1 : ℝ); linarith
      have h3 : Real.exp 1 ≤ Real.exp s := Real.exp_le_exp.mpr (by linarith)
      have h4 : Real.exp 1 * Real.exp 1 ≤ Real.exp s := by
        rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith)
      nlinarith
    obtain ⟨hl, hu⟩ := ih he
    change Real.exp^[j] (Real.exp s - 1 - 1) ≤ E j (Real.exp s - 1) at hl
    refine ⟨?_, ?_⟩
    · rw [Function.iterate_succ_apply]
      refine le_trans (hmono j ?_) hl
      -- `exp(s − 1) ≤ e^s − 2` for `s ≥ 2`
      have h1 : Real.exp s = Real.exp (s - 1) * Real.exp 1 := by
        rw [← Real.exp_add]; congr 1; ring
      have h2 : (Real.exp 1) ≥ 2 := by
        have := Real.add_one_le_exp (1 : ℝ); linarith
      have h3 : Real.exp (s - 1) ≥ 2 := by
        have := Real.add_one_le_exp (s - 1); linarith
      nlinarith
    · rw [Function.iterate_succ_apply]
      exact le_trans hu (hmono j (by linarith))

/-! ## Prop 5.3: the Lambert-`W` system -/

/-- `ψ(s) = s e^s` on `[−1, ∞)`, extended with slope `1` below `−1`: a strictly increasing
bijection of `ℝ`; its inverse is the Lambert function `W` on `[−1/e, ∞)`. -/
noncomputable def lamPsi (s : ℝ) : ℝ := max s (-1) * Real.exp (max s (-1)) + (s - max s (-1))

theorem lamPsi_of_ge {s : ℝ} (hs : -1 ≤ s) : lamPsi s = s * Real.exp s := by
  simp [lamPsi, max_eq_left hs]

theorem lamPsi_continuous : Continuous lamPsi := by
  unfold lamPsi
  have h : Continuous fun s : ℝ => max s (-1) := continuous_id.max continuous_const
  exact (h.mul (Real.continuous_exp.comp h)).add (continuous_id.sub h)

theorem hasDerivAt_mul_exp (s : ℝ) :
    HasDerivAt (fun s => s * Real.exp s) ((1 + s) * Real.exp s) s := by
  have := (hasDerivAt_id s).mul (Real.hasDerivAt_exp s)
  refine this.congr_deriv ?_
  simp only [id]; ring

theorem lamPsi_strictMono : StrictMono lamPsi := by
  have hf : StrictMonoOn (fun m => m * Real.exp m) (Set.Ici (-1)) := by
    refine strictMonoOn_of_deriv_pos (convex_Ici _)
      (Continuous.continuousOn (by fun_prop)) fun x hx => ?_
    rw [interior_Ici, Set.mem_Ioi] at hx
    rw [(hasDerivAt_mul_exp x).deriv]
    exact mul_pos (by linarith) (Real.exp_pos x)
  have hm1 : lamPsi (-1) = -Real.exp (-1) := by rw [lamPsi_of_ge le_rfl]; ring
  have hge : ∀ b, -1 ≤ b → -Real.exp (-1) ≤ lamPsi b := by
    intro b hb
    rw [← hm1, lamPsi_of_ge le_rfl, lamPsi_of_ge hb]
    exact hf.monotoneOn (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hb) hb
  have hlt : ∀ a, a < -1 → lamPsi a = -Real.exp (-1) + (a + 1) := by
    intro a ha
    simp only [lamPsi, max_eq_right ha.le]
    ring
  intro a b hab
  rcases le_or_gt (-1) a with ha | ha
  · rw [lamPsi_of_ge ha, lamPsi_of_ge (by linarith)]
    exact hf (Set.mem_Ici.2 ha) (Set.mem_Ici.2 (by linarith)) hab
  · rcases le_or_gt (-1) b with hb | hb
    · rw [hlt a ha]; linarith [hge b hb]
    · rw [hlt a ha, hlt b hb]; linarith

theorem lamPsi_surjective : Function.Surjective lamPsi := by
  refine lamPsi_continuous.surjective ?_ ?_
  · refine tendsto_atTop_mono' atTop ?_ tendsto_id
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with s hs
    rw [lamPsi_of_ge (by linarith)]
    have := Real.add_one_le_exp s
    simp only [id]
    nlinarith
  · refine tendsto_atBot_mono' atBot ?_ (tendsto_atBot_add_const_right atBot 1 tendsto_id)
    filter_upwards [eventually_le_atBot (-2 : ℝ)] with s hs
    simp only [lamPsi, max_eq_right (by linarith : s ≤ -1), id]
    have := Real.exp_pos (-1)
    linarith

/-- The Lambert function on `[−1/e, ∞)` (extended by the inverse of `lamPsi`). -/
noncomputable def lamW : ℝ ≃o ℝ :=
  (lamPsi_strictMono.orderIsoOfSurjective lamPsi lamPsi_surjective).symm

theorem lamPsi_lamW (t : ℝ) : lamPsi (lamW t) = t :=
  (lamPsi_strictMono.orderIsoOfSurjective lamPsi lamPsi_surjective).apply_symm_apply t

theorem lamW_zero : lamW 0 = 0 :=
  lamPsi_strictMono.injective (by rw [lamPsi_lamW, lamPsi_of_ge (by norm_num)]; simp)

theorem lamW_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ lamW t := by
  rw [← lamW_zero]; exact lamW.monotone ht

theorem lamW_mul_exp {t : ℝ} (ht : 0 ≤ t) : lamW t * Real.exp (lamW t) = t := by
  rw [← lamPsi_of_ge (by linarith [lamW_nonneg ht]), lamPsi_lamW]

theorem lamW_hasDerivAt {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt lamW ((1 + lamW t) * Real.exp (lamW t))⁻¹ t := by
  have hW := lamW_nonneg ht
  have hψ : HasDerivAt lamPsi ((1 + lamW t) * Real.exp (lamW t)) (lamW t) := by
    refine (hasDerivAt_mul_exp (lamW t)).congr_of_eventuallyEq ?_
    filter_upwards [lt_mem_nhds (by linarith : (-1 : ℝ) < lamW t)] with s hs
    exact lamPsi_of_ge hs.le
  exact HasDerivAt.of_local_left_inverse lamW.continuous.continuousAt hψ
    (mul_pos (by linarith) (Real.exp_pos _)).ne' (Filter.Eventually.of_forall lamPsi_lamW)

/-- [BAC] journal draft system `eq:lambert-system` (Prop 5.3): state `(u, v, x₁)`, output `x₁`:
`u' = (1−u)²(1−v)`, `v' = (1−v)³(1−u)`, `x₁' = (1−x₁)(1−v)`, all initial values `0`. -/
noncomputable def lambertPIVP : PolyPIVP 3 where
  field := ![(1 - X 0) ^ 2 * (1 - X 1), (1 - X 1) ^ 3 * (1 - X 0), (1 - X 2) * (1 - X 1)]
  init := ![0, 0, 0]
  output := 2

/-- The solution: `u = 1 − e^{−W}`, `v = W/(1 + W)`, `x₁ = 1 − exp(1 − e^W)`. -/
noncomputable def lambertSol (t : ℝ) : Fin 3 → ℝ :=
  ![1 - Real.exp (-lamW t), lamW t / (1 + lamW t), 1 - Real.exp (1 - Real.exp (lamW t))]

theorem lambertSol_hasDerivAt {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt lambertSol (lambertPIVP.toPIVP.field (lambertSol t)) t := by
  have hW := lamW_hasDerivAt ht
  have hW0 := lamW_nonneg ht
  have h1 : (1 + lamW t) ≠ 0 := by linarith
  have he := Real.exp_pos (lamW t)
  refine hasDerivAt_pi.2 fun i => ?_
  fin_cases i
  · refine (hW.neg.exp.const_sub 1).congr_deriv ?_
    simp [PolyPIVP.toPIVP, PolyPIVP.evalField, lambertPIVP, lambertSol, Real.exp_neg]
    try field_simp
    try ring
  · refine ((hW.div (hW.const_add 1) h1)).congr_deriv ?_
    simp [PolyPIVP.toPIVP, PolyPIVP.evalField, lambertPIVP, lambertSol, Real.exp_neg]
    try field_simp
    try ring
  · refine ((hW.exp.const_sub 1).exp.const_sub 1).congr_deriv ?_
    simp [PolyPIVP.toPIVP, PolyPIVP.evalField, lambertPIVP, lambertSol]
    try field_simp
    try ring

/-- [BAC] journal draft Prop 5.3 (`prop:rlogr`): the system `eq:lambert-system` computes `1` with
the exact time modulus `(r+1) log(r+1)` (the bound holds past it and fails on
`[0, (r+1) log(r+1)]`), so `μ(r) = Θ(r log r)`. -/
theorem lambert_certified :
    ∃ btc : CertifiedBoundedTimeComputable 3 1, btc.pivp = lambertPIVP ∧
      (∀ r : ℕ, btc.modulus r = ((r : ℝ) + 1) * Real.log ((r : ℝ) + 1)) ∧
      ∀ r : ℕ, ∀ t, 0 ≤ t → t ≤ ((r : ℝ) + 1) * Real.log ((r : ℝ) + 1) →
        Real.exp (-(r : ℝ)) ≤ |btc.sol.trajectory t btc.pivp.output - 1| := by
  let sol : PIVP.Solution lambertPIVP.toPIVP :=
    { trajectory := lambertSol
      init_cond := by
        funext i
        fin_cases i <;> simp [lambertSol, PolyPIVP.toPIVP, lambertPIVP, lamW_zero]
      is_solution := fun t ht => lambertSol_hasDerivAt ht }
  have hx : ∀ t, sol.trajectory t lambertPIVP.output - 1 =
      -Real.exp (1 - Real.exp (lamW t)) := by
    intro t; simp [sol, lambertSol, lambertPIVP]
  have hbd : lambertPIVP.toPIVP.IsBounded sol.trajectory := by
    refine ⟨1, one_pos, fun t ht => (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_⟩
    have hW0 := lamW_nonneg ht
    rw [Real.norm_eq_abs, abs_le]
    fin_cases i
    · have h0 := Real.exp_pos (-lamW t)
      have h1 : Real.exp (-lamW t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      show -1 ≤ 1 - Real.exp (-lamW t) ∧ 1 - Real.exp (-lamW t) ≤ 1
      constructor <;> linarith
    · have h1 : 0 < 1 + lamW t := by linarith
      have h2 : 0 ≤ lamW t / (1 + lamW t) := div_nonneg hW0 h1.le
      have h3 : lamW t / (1 + lamW t) ≤ 1 := (div_le_one h1).2 (by linarith)
      show -1 ≤ lamW t / (1 + lamW t) ∧ lamW t / (1 + lamW t) ≤ 1
      constructor <;> linarith
    · have h0 := Real.exp_pos (1 - Real.exp (lamW t))
      have h1 : 1 ≤ Real.exp (lamW t) := Real.one_le_exp hW0
      have h2 : Real.exp (1 - Real.exp (lamW t)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      show -1 ≤ 1 - Real.exp (1 - Real.exp (lamW t)) ∧ 1 - Real.exp (1 - Real.exp (lamW t)) ≤ 1
      constructor <;> linarith
  -- precision `e^{−r}` iff `e^W > r + 1` iff `t > (r+1) log(r+1)`
  have hiff : ∀ (r : ℕ) (t : ℝ), 0 ≤ t →
      ((r : ℝ) + 1 < Real.exp (lamW t) ↔ ((r : ℝ) + 1) * Real.log ((r : ℝ) + 1) < t) := by
    intro r t ht
    have hr : (0 : ℝ) < (r : ℝ) + 1 := by positivity
    have hpsi : lamPsi (Real.log ((r : ℝ) + 1)) = ((r : ℝ) + 1) * Real.log ((r : ℝ) + 1) := by
      rw [lamPsi_of_ge (by linarith [Real.log_nonneg (by linarith : (1 : ℝ) ≤ (r : ℝ) + 1)]),
        Real.exp_log hr]
      ring
    rw [← Real.log_lt_iff_lt_exp hr, ← lamPsi_strictMono.lt_iff_lt, hpsi, lamPsi_lamW]
  have hmod0 : ∀ r : ℕ, 0 ≤ ((r : ℝ) + 1) * Real.log ((r : ℝ) + 1) := fun r =>
    mul_nonneg (by positivity) (Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) r]))
  obtain ⟨btc, hpivp, hmod, heq⟩ := CertifiedBoundedTimeComputable.exists_of_solution
    (α := 1) lambertPIVP sol hbd (fun r => ((r : ℝ) + 1) * Real.log ((r : ℝ) + 1))
    (fun r t ht => by
      beta_reduce at ht
      have ht0 : 0 ≤ t := (hmod0 r).trans ht.le
      rw [hx, abs_neg, abs_of_pos (Real.exp_pos _), Real.exp_lt_exp]
      have := (hiff r t ht0).2 ht
      linarith)
  refine ⟨btc, hpivp, fun r => by rw [hmod r]; exact max_eq_right (hmod0 r),
    fun r t ht htr => ?_⟩
  rw [heq t ht, hpivp, hx, abs_neg, abs_of_pos (Real.exp_pos _), Real.exp_le_exp]
  have : ¬ ((r : ℝ) + 1 < Real.exp (lamW t)) := fun h => absurd ((hiff r t ht).1 h)
    (not_lt.mpr htr)
  push_neg at this
  linarith

/-- Non-vacuity of `polyFamily_certified` at `n = 2` (`μ(r) = (r+1)² − 1`). -/
theorem polyFamily_two : ∃ btc : CertifiedBoundedTimeComputable 2 1,
    btc.pivp = polyFamily 2 ∧ ∀ r : ℕ, btc.modulus r = ((r : ℝ) + 1) ^ 2 - 1 := by
  obtain ⟨btc, h1, h2, -⟩ := polyFamily_certified (n := 2) (by norm_num)
  exact ⟨btc, h1, h2⟩

end Constructible

end Ripple
