/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Ripple.sCRNUniversality.ClockedCTM.Completion
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# SCWB Theorem 3.2 for clocked Turing machines (FIX3-SCWB-T32 §7, Theorem 3.2′)

`scwb_theorem_3_2_ctm`: the network `net C L` (the repaired network `N♯(C, L + 1)`) is fixed
by the CTM `C` and the clock length; for every tape length `n + 3` the count `#A* = f` is fixed;
then for every error bound `δ ∈ (0, 1]`, every initial configuration `c0` and every step bound
`t ≥ 1` there is `a ≥ 2` (`#A = a f`) such that, started from `initState n c0 a f`,

* with probability at least `1 - δ` the simulation is correct and complete up to tick `4 t`
  (`Simulates`: tick `4 t` is drawn, and just before tick `4 j + r + 1` the state is in
  `𝒦_{r+1}(c_j)`, `r < 3`, and just before tick `4 j + 4` in `𝒦_4(q_j, b_j; w_{j+1})`, which
  encodes `c_{j+1}`; see `schCl_three`);
* the expected time before tick `4 t` is at most `8 (3/2)^L t² Θsum n / δ` (units `v/k`).

`Θsum n` is the explicit sum of the four window start bounds (`Run.lean`).  The law is the
embedded jump chain `rawLaw`; `expTime` is its expected holding-time functional before tick
`4 t` (`Completion.lean`).
-/

namespace Ripple.sCRNUniversality.ClockedCTM

open MeasureTheory Stochastic Stochastic.MassAction
open scoped ENNReal

variable {Q : Type} [Fintype Q] [DecidableEq Q] {L : ℕ} (C : CTM Q)

theorem gs_le_ratio {a : ℝ} (ha : 3 ≤ a) (L : ℕ) : gs a L ≤ (3 / 2) ^ L * gs (a - 1) L := by
  unfold gs
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i hi => ?_
  have hi' : i ≤ L := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  calc a ^ i ≤ ((3 / 2) * (a - 1)) ^ i := pow_le_pow_left₀ (by linarith) (by linarith) i
    _ = (3 / 2) ^ i * (a - 1) ^ i := mul_pow _ _ _
    _ ≤ (3 / 2) ^ L * (a - 1) ^ i :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hi')
          (pow_nonneg (by linarith) _)

theorem self_le_gs {a : ℝ} (ha : 0 ≤ a) {L : ℕ} (hL : 1 ≤ L) : a ≤ gs a L := by
  obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
  rw [gs_succ]
  nlinarith [one_le_gs ha L']

theorem Θsum_pos (n : ℕ) : 0 < Θsum n := by
  unfold Θsum
  have h41 : 0 < Θ41 n := by
    unfold Θ41
    have := aut_nonneg (9 * 3 ^ n) 1
    have : (0 : ℝ) < ((9 * 3 ^ n : ℕ) : ℝ) := by positivity
    positivity
  linarith [Θ12_nonneg n, Θ23_nonneg n, Θ34_nonneg n]

/-! ### Asymptotics of `Θsum`: `Θsum n ≤ 30 (1 + ln m)/m`, `m = 9 · 3^n = 3^{s-1}` -/

theorem hrm_eq_harmonic (n : ℕ) : hrm n = (harmonic n : ℝ) := by
  rw [hrm, harmonic, Rat.cast_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [one_div]

/-- `H_n ≤ 1 + ln n`. -/
theorem hrm_le_log (n : ℕ) : hrm n ≤ 1 + Real.log n := by
  rw [hrm_eq_harmonic]
  exact harmonic_le_one_add_log n

/-- `Σ_{1 ≤ k < m} 1/k = H_{m-1}`. -/
theorem sum_Ico_inv (m : ℕ) : ∑ k ∈ Finset.Ico 1 m, 1 / (k : ℝ) = hrm (m - 1) := by
  rw [Finset.sum_Ico_eq_sum_range, hrm]
  refine Finset.sum_congr rfl fun k _ => ?_
  push_cast
  ring

/-- `m · aut m 1 = 2 H_{m-1}` (partial fractions), hence `≤ 2 H_m`. -/
theorem mul_aut_one_le (m : ℕ) : (m : ℝ) * aut m 1 ≤ 2 * hrm m := by
  have hsplit : (m : ℝ) * aut m 1 = ∑ k ∈ Finset.Ico 1 m, 1 / (k : ℝ) +
      ∑ k ∈ Finset.Ico 1 m, 1 / ((m : ℝ) - k) := by
    rw [aut, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_Ico] at hk
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk.1
    have hkm : (k : ℝ) < m := by exact_mod_cast hk.2
    have h1 : (k : ℝ) ≠ 0 := by positivity
    have h2 : (m : ℝ) - k ≠ 0 := by linarith
    field_simp
    ring
  have hrefl : ∑ k ∈ Finset.Ico 1 m, 1 / ((m : ℝ) - k) = ∑ k ∈ Finset.Ico 1 m, 1 / (k : ℝ) := by
    refine Finset.sum_nbij' (fun k => m - k) (fun k => m - k) ?_ ?_ ?_ ?_ ?_
    · intro k hk
      simp only [Finset.mem_Ico, Finset.coe_Ico, Set.mem_Ico] at hk ⊢
      omega
    · intro k hk
      simp only [Finset.mem_Ico, Finset.coe_Ico, Set.mem_Ico] at hk ⊢
      omega
    · intro k hk
      simp only [Finset.mem_Ico, Finset.coe_Ico, Set.mem_Ico] at hk
      show m - (m - k) = k
      omega
    · intro k hk
      simp only [Finset.mem_Ico, Finset.coe_Ico, Set.mem_Ico] at hk
      show m - (m - k) = k
      omega
    · intro k hk
      rw [Finset.mem_Ico] at hk
      rw [Nat.cast_sub hk.2.le]
  rw [hsplit, hrefl, sum_Ico_inv]
  linarith [hrm_mono (Nat.sub_le m 1)]

theorem log_seven_le : Real.log 7 ≤ 3 * Real.log 2 - 1 / 8 := by
  have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 7 / 8 by norm_num)
  have e : Real.log 7 = Real.log ((2 : ℝ) ^ 3) + Real.log (7 / 8) := by
    rw [← Real.log_mul (x := (2 : ℝ) ^ 3) (y := 7 / 8) (by norm_num) (by norm_num)]
    norm_num
  rw [e, Real.log_pow]
  push_cast
  linarith

theorem log_nine_ge : 3 * Real.log 2 + 1 / 9 ≤ Real.log 9 := by
  have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 9 / 8 by norm_num)
  have e : Real.log 9 = Real.log ((2 : ℝ) ^ 3) + Real.log (9 / 8) := by
    rw [← Real.log_mul (x := (2 : ℝ) ^ 3) (y := 9 / 8) (by norm_num) (by norm_num)]
    norm_num
  rw [e, Real.log_pow]
  push_cast
  norm_num at h
  linarith

theorem log_three_le : Real.log 3 ≤ 1.0989 := by
  have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 243 / 256 by norm_num)
  have e : Real.log (243 / 256) = 5 * Real.log 3 - 8 * Real.log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num), show (243 : ℝ) = 3 ^ 5 by norm_num,
      show (256 : ℝ) = 2 ^ 8 by norm_num, Real.log_pow, Real.log_pow]
    push_cast
    ring
  have := Real.log_two_lt_d9
  linarith

/-- `Θsum` as one fraction over `m = 9 · 3^n`. -/
theorem Θsum_eq (n : ℕ) : Θsum n =
    (17 / 2 + 4 * ((9 * 3 ^ n : ℝ) * aut (9 * 3 ^ n) 1) + hrm (7 * (9 * 3 ^ n)) +
      9 / 2 * hrm (20 * 3 ^ n) + 4 * Real.log (1 + ((13 * (9 * 3 ^ n) : ℕ) : ℝ)) +
      4 * Real.log (1 + ((6 * (9 * 3 ^ n) : ℕ) : ℝ))) / (9 * 3 ^ n : ℝ) := by
  unfold Θsum Θ12 Θ23 Θ34 Θ41
  have h3 : (0 : ℝ) < 3 ^ n := by positivity
  rw [show ((9 * 3 ^ n : ℕ) : ℝ) = 9 * 3 ^ n by push_cast; ring,
    show ((2 * 3 ^ n : ℕ) : ℝ) = 2 * 3 ^ n by push_cast; ring]
  field_simp
  ring

/-- **Asymptotics of the start bounds.**  `Θsum n ≤ 30 (1 + ln m)/m` with `m = 9 · 3^n`
(FIX3-SCWB-T32 §5 has `26 (1 + ln m)/m` for the paper's completion times; the window
potentials here give `m Θsum ≤ 21.5 (1 + ln m) + 24.4`). -/
theorem Θsum_le_log (n : ℕ) :
    Θsum n ≤ 30 * (1 + Real.log (9 * 3 ^ n)) / (9 * 3 ^ n) := by
  rw [Θsum_eq]
  have h3n : (1 : ℝ) ≤ 3 ^ n := one_le_pow₀ (by norm_num)
  have hM1 : (1 : ℝ) ≤ 9 * 3 ^ n := by linarith
  have hM : (0 : ℝ) < 9 * 3 ^ n := by linarith
  apply div_le_div_of_nonneg_right _ hM.le
  have hA : (9 * 3 ^ n : ℝ) * aut (9 * 3 ^ n) 1 ≤ 2 * (1 + Real.log (9 * 3 ^ n)) := by
    have h1 := mul_aut_one_le (9 * 3 ^ n)
    have h2 := hrm_le_log (9 * 3 ^ n)
    push_cast at h1 h2
    linarith
  have h7 : hrm (7 * (9 * 3 ^ n)) ≤ 1 + Real.log 7 + Real.log (9 * 3 ^ n) := by
    have h := hrm_le_log (7 * (9 * 3 ^ n))
    push_cast at h
    rw [Real.log_mul (x := 7) (y := 9 * 3 ^ n) (by norm_num) hM.ne'] at h
    linarith
  have h20 : hrm (20 * 3 ^ n) ≤ 1 + Real.log 2 + 1 / 9 + Real.log (9 * 3 ^ n) := by
    have h := hrm_le_log (20 * 3 ^ n)
    push_cast at h
    rw [show (20 : ℝ) * 3 ^ n = 2 * (10 / 9) * (9 * 3 ^ n) by ring,
      Real.log_mul (x := 2 * (10 / 9)) (y := 9 * 3 ^ n) (by norm_num) hM.ne',
      Real.log_mul (x := 2) (y := 10 / 9) (by norm_num) (by norm_num)] at h
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 10 / 9 by norm_num)
    linarith
  have l13 : Real.log (1 + ((13 * (9 * 3 ^ n) : ℕ) : ℝ)) ≤
      Real.log 2 + Real.log 7 + Real.log (9 * 3 ^ n) := by
    push_cast
    rw [← Real.log_mul (x := 2) (y := 7) (by norm_num) (by norm_num),
      ← Real.log_mul (x := 2 * 7) (y := 9 * 3 ^ n) (by norm_num) hM.ne']
    exact Real.log_le_log (by positivity) (by linarith)
  have l6 : Real.log (1 + ((6 * (9 * 3 ^ n) : ℕ) : ℝ)) ≤ Real.log 7 + Real.log (9 * 3 ^ n) := by
    push_cast
    rw [← Real.log_mul (x := 7) (y := 9 * 3 ^ n) (by norm_num) hM.ne']
    exact Real.log_le_log (by positivity) (by linarith)
  have hL9 : Real.log 9 ≤ Real.log (9 * 3 ^ n) := Real.log_le_log (by norm_num) (by linarith)
  have c7 := log_seven_le
  have c9 := log_nine_ge
  have c2 := Real.log_two_lt_d9
  have c2' := Real.log_two_gt_d9
  linarith

/-- `Θsum n ≤ 90 (1 + (n + 2) ln 3)/3^{n+3}` (tape length `s = n + 3`, `m = 3^{s-1}`). -/
theorem Θsum_le_pow (n : ℕ) :
    Θsum n ≤ 90 * (1 + ((n : ℝ) + 2) * Real.log 3) / 3 ^ (n + 3) := by
  have h := Θsum_le_log n
  have e2 : Real.log (9 * 3 ^ n) = ((n : ℝ) + 2) * Real.log 3 := by
    rw [show (9 : ℝ) * 3 ^ n = 3 ^ (n + 2) by ring, Real.log_pow]
    push_cast
    ring
  rw [e2] at h
  refine h.trans_eq ?_
  field_simp
  ring

/-- The target class just before tick `4 j + 4` encodes the configuration `c_{j+1}`: the
state index `q_j` and read bit `b_j` of `U_{q_j, b_j}` give `q_{j+1} = (C.next q_j b_j).1`, and
`#M† = tval w_{j+1}`. -/
theorem schCl_three (n : ℕ) (c0 : Q × List Bool) (j : ℕ) (w : State (Sp Q L)) :
    schCl C n c0 (4 * j + 3) w ↔
      K4 (9 * 3 ^ n) (20 * 3 ^ n) (C.runT c0 j).1 ((C.runT c0 j).2.headD false)
        (tval (C.runT c0 (j + 1)).2) w := by
  unfold schCl cfg
  rw [if_neg (show ¬ (4 * j + 3) % 4 = 0 by omega), if_neg (show ¬ (4 * j + 3) % 4 = 1 by omega),
    if_neg (show ¬ (4 * j + 3) % 4 = 2 by omega), show (4 * j + 3) / 4 = j by omega]
  rfl

/-- **SCWB Theorem 3.2 for clocked Turing machines** (repaired network, FIX3-SCWB-T32
Theorem 3.2′ at the CTM level): with probability at least `1 - δ` the run reaches tick `4 t`
and every tick before it is drawn from its target class (`Simulates`). -/
theorem scwb_theorem_3_2_ctm (L : ℕ) (hL : 1 ≤ L) (n : ℕ) :
    ∃ f : ℕ, 1 ≤ f ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ (c0 : Q × List Bool)
      (hc0 : c0.2.length = n + 3) (t : ℕ), 1 ≤ t → ∃ a : ℕ, 2 ≤ a ∧
        rawLaw (net C L) (net_hasPositiveRates C L) (initState n c0 a f)
            {ω | ¬ Simulates (ctmSched C n c0 hc0) (4 * t) (initState n c0 a f) ω} ≤
          ENNReal.ofReal δ ∧
        ∀ v k : ℝ, 0 < v → 0 < k →
          ENNReal.ofReal (v / k) * expTime C (initState (L := L) n c0 a f) (4 * t) ≤
            ENNReal.ofReal (8 * (3 / 2) ^ L * v * t ^ 2 * Θsum n / (k * δ)) := by
  have hΘ := Θsum_pos n
  set Θ := Θsum n with hΘdef
  have hG2 : (1 : ℝ) ≤ gs 2 L := one_le_gs (by norm_num) L
  refine ⟨⌈gs 2 L / Θ⌉₊, ?_, ?_⟩
  · exact Nat.one_le_iff_ne_zero.mpr (by
      rw [Ne, Nat.ceil_eq_zero, not_le]; positivity)
  intro δ hδ hδ1 c0 hc0 t ht
  set f := ⌈gs 2 L / Θ⌉₊ with hfdef
  have hf1 : 1 ≤ f := Nat.one_le_iff_ne_zero.mpr (by
    rw [hfdef, Ne, Nat.ceil_eq_zero, not_le]; positivity)
  have hfr : (0 : ℝ) < f := by exact_mod_cast hf1
  have hfge : gs 2 L / Θ ≤ f := Nat.le_ceil _
  have htr : (1 : ℝ) ≤ t := by exact_mod_cast ht
  set lam0 := δ / (t * Θ) with hlam0
  have hlam0p : 0 < lam0 := by positivity
  classical
  have hex : ∃ a : ℕ, 2 ≤ a ∧ (f : ℝ) / gs a L ≤ lam0 := by
    refine ⟨max 2 ⌈(f : ℝ) / lam0⌉₊, le_max_left _ _, ?_⟩
    have hA : (f : ℝ) / lam0 ≤ (max 2 ⌈(f : ℝ) / lam0⌉₊ : ℕ) := by
      push_cast
      exact (Nat.le_ceil _).trans (le_max_right _ _)
    have hA2 : (2 : ℝ) ≤ (max 2 ⌈(f : ℝ) / lam0⌉₊ : ℕ) := by push_cast; exact le_max_left _ _
    have hgs := self_le_gs (a := ((max 2 ⌈(f : ℝ) / lam0⌉₊ : ℕ) : ℝ)) (by linarith) hL
    rw [div_le_iff₀ (by linarith)]
    rw [div_le_iff₀ hlam0p] at hA
    nlinarith
  set a := Nat.find hex with hadef
  obtain ⟨ha2, hal⟩ := Nat.find_spec hex
  rw [← hadef] at ha2 hal
  refine ⟨a, ha2, ?_, ?_⟩
  · obtain ⟨herr, -⟩ := ctm_simulates_error_time C hL hc0 t ha2 hf1
    refine herr.trans (ENNReal.ofReal_le_ofReal ?_)
    calc (f : ℝ) / gs a L * (t * Θ) ≤ lam0 * (t * Θ) :=
          mul_le_mul_of_nonneg_right hal (by positivity)
      _ = δ := by rw [hlam0]; field_simp
  · intro v k hv hk
    obtain ⟨-, htime⟩ := ctm_simulates_error_time C hL hc0 t ha2 hf1
    have hGa : (0 : ℝ) < gs a L := by linarith [one_le_gs (Nat.cast_nonneg (α := ℝ) a) L]
    -- `gs a L / f ≤ (3/2)^L / lam0`
    have hkey : gs a L / f ≤ (3 / 2) ^ L / lam0 := by
      have hp1 : (1 : ℝ) ≤ (3 / 2) ^ L := one_le_pow₀ (by norm_num)
      rcases Nat.lt_or_ge a 3 with h3 | h3
      · have ha : a = 2 := by omega
        rw [ha]
        have h1 : gs 2 L / f ≤ Θ := by
          rw [div_le_iff₀ hfr]
          rw [div_le_iff₀ hΘ] at hfge
          linarith
        have h2 : Θ ≤ 1 / lam0 := by
          rw [hlam0, one_div_div, le_div_iff₀ hδ]
          nlinarith
        push_cast
        calc gs 2 L / f ≤ 1 / lam0 := h1.trans h2
          _ ≤ (3 / 2) ^ L / lam0 := by gcongr
      · have hmin := Nat.find_min hex (show a - 1 < a by omega)
        have hnot : ¬ ((f : ℝ) / gs (a - 1 : ℕ) L ≤ lam0) := fun h =>
          hmin ⟨by omega, h⟩
        push_neg at hnot
        have hcast : ((a - 1 : ℕ) : ℝ) = (a : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega)]; simp
        rw [hcast] at hnot
        have hG1 : (0 : ℝ) < gs ((a : ℝ) - 1) L :=
          by linarith [one_le_gs (show (0 : ℝ) ≤ (a : ℝ) - 1 by
            have : (3 : ℝ) ≤ a := by exact_mod_cast h3
            linarith) L]
        have hratio := gs_le_ratio (a := (a : ℝ)) (by exact_mod_cast h3) L
        have h1 : gs ((a : ℝ) - 1) L / f < 1 / lam0 := by
          rw [div_lt_div_iff₀ hfr hlam0p, one_mul]
          rw [lt_div_iff₀ hG1] at hnot
          linarith
        calc gs a L / f ≤ (3 / 2) ^ L * gs ((a : ℝ) - 1) L / f := by gcongr
          _ = (3 / 2) ^ L * (gs ((a : ℝ) - 1) L / f) := by ring
          _ ≤ (3 / 2) ^ L * (1 / lam0) := by gcongr
          _ = (3 / 2) ^ L / lam0 := by ring
    calc ENNReal.ofReal (v / k) * expTime C (initState (L := L) n c0 a f) (4 * t)
        ≤ ENNReal.ofReal (v / k) * ENNReal.ofReal (2 * (4 * t : ℕ) * gs a L / f) := by
          gcongr
      _ = ENNReal.ofReal (v / k * (2 * (4 * t : ℕ) * gs a L / f)) :=
          (ENNReal.ofReal_mul (by positivity)).symm
      _ ≤ ENNReal.ofReal (8 * (3 / 2) ^ L * v * t ^ 2 * Θ / (k * δ)) := by
          apply ENNReal.ofReal_le_ofReal
          have e : v / k * (2 * (4 * t : ℕ) * gs a L / f) = 8 * (v / k) * t * (gs a L / f) := by
            push_cast; ring
          rw [e]
          have hvk : 0 ≤ 8 * (v / k) * t := by positivity
          calc 8 * (v / k) * t * (gs a L / f) ≤ 8 * (v / k) * t * ((3 / 2) ^ L / lam0) :=
                mul_le_mul_of_nonneg_left hkey hvk
            _ = 8 * (3 / 2) ^ L * v * t ^ 2 * Θ / (k * δ) := by
                rw [hlam0]; field_simp

end Ripple.sCRNUniversality.ClockedCTM
