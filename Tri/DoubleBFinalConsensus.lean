/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.DoubleBMiddleConstants
import Tri.DoubleBAssembly

/-!
# Direct Double-B consensus from the logarithmic co-level checkpoint

The target is the absorbing all-`X` state.  Using `noncons_mass_bound` directly
avoids the constant-width upper-return term that appears if one first targets
co-level two at an exact deterministic time.
-/

namespace Tri

open scoped ENNReal

def doubleFinalScale (n γ : ℕ) : ℕ :=
  γ * Nat.log 2 n + 1

def doubleFinalResolutions (n γ : ℕ) : ℕ :=
  64 * doubleFinalScale n γ

def doubleFinalHorizon (n γ : ℕ) : ℕ :=
  65536 * n * doubleFinalScale n γ

instance (n : ℕ) : DecidablePred (@DoubleXConsensus n) := by
  intro z
  unfold DoubleXConsensus
  infer_instance

/-- The fixed lower-boundary productivity floor used in the final direct
consensus block. -/
theorem doubleFinalProductivity_ge
    (n : ℕ) (hn : 2 ≤ n) (hlog : 12 ≤ Nat.log 2 n) :
    2 * ENNReal.ofReal
        ((1 : ℝ) / (64 * (n : ℝ))) ≤
      doubleBandProductivity n (doubleMiddleLower n) (2 * n) := by
  have hnLarge : 4096 ≤ n := phase1_log_twelve_implies_size hlog
  have hnPos : 0 < n := by omega
  let g := n / 20
  let A :=
    (doubleMiddleLower n + 1 - n) *
      (2 * n - (2 * n - 1))
  let B := 2 * Nat.choose n 2
  have h20g : 20 * g ≤ n := by
    dsimp only [g]
    exact Nat.mul_div_le n 20
  have h20u : n < 20 * g + 20 := by
    dsimp only [g]
    have hd := Nat.div_add_mod n 20
    have hm := Nat.mod_lt n (by norm_num : 0 < 20)
    omega
  have hng : n ≤ 21 * g := by omega
  have hA : A = g + 1 := by
    dsimp only [A]
    rw [show 2 * n - (2 * n - 1) = 1 by omega, mul_one]
    unfold doubleMiddleLower
    dsimp only [g]
    omega
  have hB : B = n * (n - 1) := by
    dsimp only [B]
    have h := two_mul_choose_two_succ (n - 1)
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ n)] using h
  have hcross : B ≤ (32 * n) * A := by
    rw [hA, hB]
    have hn1 : n - 1 ≤ 21 * (g + 1) := by omega
    calc
      n * (n - 1) ≤ n * (21 * (g + 1)) :=
        Nat.mul_le_mul_left n hn1
      _ ≤ n * (32 * (g + 1)) := by
        apply Nat.mul_le_mul_left
        exact Nat.mul_le_mul_right (g + 1) (by norm_num)
      _ = (32 * n) * (g + 1) := by ring
  have hleftTop :
      2 * ENNReal.ofReal ((1 : ℝ) / (64 * (n : ℝ))) ≠ ⊤ := by
    finiteness
  have hrightTop :
      doubleBandProductivity n (doubleMiddleLower n) (2 * n) ≠ ⊤ := by
    unfold doubleBandProductivity
    apply ENNReal.div_ne_top
    · exact ENNReal.natCast_ne_top _
    · simp only [ne_eq, Nat.cast_eq_zero, Nat.mul_eq_zero]
      exact not_or_intro (by norm_num)
        (Nat.choose_pos hn).ne'
  rw [← ENNReal.toReal_le_toReal hleftTop hrightTop]
  unfold doubleBandProductivity
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
    ENNReal.toReal_ofNat, ENNReal.toReal_div]
  norm_num only [ENNReal.toReal_ofNat, ENNReal.toReal_natCast]
  change
    2 * ((1 : ℝ) / (64 * (n : ℝ))) ≤
      (A : ℝ) / (B : ℝ)
  have hBR : (0 : ℝ) < B := by
    rw [hB]
    exact_mod_cast Nat.mul_pos hnPos (by omega : 0 < n - 1)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnPos
  have hcrossR : (B : ℝ) ≤ (32 * n : ℕ) * (A : ℝ) := by
    exact_mod_cast hcross
  have hleft :
      2 * ((1 : ℝ) / (64 * (n : ℝ))) =
        (1 : ℝ) / (32 * (n : ℝ)) := by
    field_simp
    ring
  rw [hleft, div_le_div_iff₀ (by positivity : (0 : ℝ) < 32 * n) hBR]
  norm_num only [Nat.cast_mul, Nat.cast_ofNat] at hcrossR ⊢
  nlinarith

/-- The lower-ruin term from any state in the logarithmic checkpoint is
exponentially small in `γ lg n + 1`. -/
theorem doubleFinalSafetyError_le
    (n γ : ℕ) (hlog : 128 ≤ Nat.log 2 n) (hγ : 1 ≤ γ)
    (hsize : 6 * γ * Nat.log 2 n ≤ n)
    (z : DoubleState n)
    (hz : DoubleLateCheckpoint n (2 + phase2StageCount n γ) z) :
    let k := z.1.doubleLevel - doubleMiddleLower n
    (((doubleMiddleLowerR n : ℕ) : ℝ≥0∞) /
        ((doubleMiddleLower n : ℕ) : ℝ≥0∞)) ^ k ≤
      ENNReal.ofReal
        (Real.exp (-(doubleFinalScale n γ : ℝ) / 100)) := by
  have hnLarge : 4096 ≤ n :=
    phase1_log_twelve_implies_size (hlog.trans' (by norm_num))
  let g := n / 20
  let R := doubleFinalScale n γ
  let Q := doubleEndScale n γ
  let a := doubleMiddleLower n
  let b := doubleMiddleLowerR n
  let k := z.1.doubleLevel - a
  have h20g : 20 * g ≤ n := by
    dsimp only [g]
    exact Nat.mul_div_le n 20
  have h20u : n < 20 * g + 20 := by
    dsimp only [g]
    have hd := Nat.div_add_mod n 20
    have hm := Nat.mod_lt n (by norm_num : 0 < 20)
    omega
  have hng : n ≤ 21 * g := by omega
  have hRfive : 5 * R ≤ n := by
    calc
      5 * R = 5 * (γ * Nat.log 2 n + 1) := by
        rfl
      _ ≤ 6 * (γ * Nat.log 2 n) := by
        have hprod : 128 ≤ γ * Nat.log 2 n := by
          calc
            128 = 1 * 128 := by norm_num
            _ ≤ γ * Nat.log 2 n := Nat.mul_le_mul hγ hlog
        omega
      _ = 6 * γ * Nat.log 2 n := by ring
      _ ≤ n := hsize
  have hQ : 2 * Q ≤ γ * Nat.log 2 n :=
    doubleEndScale_le n γ
  have hQR : Q ≤ R := by
    dsimp only [R, doubleFinalScale]
    omega
  have ha : a = n + g := by rfl
  have hb : b = n - g - 2 := by
    dsimp only [b, doubleMiddleLowerR, doubleMiddleLower, g]
    omega
  have hlevel :
      2 * n - Q ≤ z.1.doubleLevel := by
    simpa only [DoubleLateCheckpoint, doubleLateCheckpointLevel, Q,
      doubleEndScale] using hz
  have hak : a + k = z.1.doubleLevel := by
    have haLevel : a ≤ z.1.doubleLevel := by
      rw [ha]
      omega
    dsimp only [k]
    exact Nat.add_sub_of_le haLevel
  have hRk : R ≤ k := by
    rw [← hak, ha] at hlevel
    omega
  have hbPos : 0 < b := by rw [hb]; omega
  have hba : b ≤ a := by rw [ha, hb]; omega
  have hdiff : a ≤ 11 * (a - b) := by
    rw [ha, hb]
    omega
  have hcross : R * a ≤ 100 * k * (a - b) := by
    calc
      R * a ≤ R * (11 * (a - b)) :=
        Nat.mul_le_mul_left R hdiff
      _ = (11 * R) * (a - b) := by ring
      _ ≤ (100 * k) * (a - b) := by
        apply Nat.mul_le_mul_right
        omega
      _ = 100 * k * (a - b) := by ring
  change ((b : ℝ≥0∞) / (a : ℝ≥0∞)) ^ k ≤
    ENNReal.ofReal (Real.exp (-(R : ℝ) / 100))
  have hE :
      (R : ℝ) / 100 ≤
        (k : ℝ) * ((a : ℝ) - (b : ℝ)) / (a : ℝ) := by
    have haR : (0 : ℝ) < a := by
      exact_mod_cast (lt_of_lt_of_le hbPos hba)
    rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 100) haR]
    have hcross' : R * a ≤ k * (a - b) * 100 := by
      calc
        R * a ≤ 100 * k * (a - b) := hcross
        _ = k * (a - b) * 100 := by ring
    exact_mod_cast hcross'
  simpa only [show (-((R : ℝ) / 100)) = -(R : ℝ) / 100 by ring]
    using ratio_pow_le_ofReal_exp a b k ((R : ℝ) / 100)
      hbPos hba hE

/-- The direction term from any non-consensus logarithmic-checkpoint state is
exponentially small in the final scale. -/
theorem doubleFinalDirectionError_le
    (n γ : ℕ) (hlog : 128 ≤ Nat.log 2 n)
    (z : DoubleState n)
    (hz : DoubleLateCheckpoint n (2 + phase2StageCount n γ) z)
    (hncons : ¬ DoubleXConsensus z) :
    phase1RungBase (doubleMiddleLower n) (doubleMiddleLowerD n) ^
        z.1.doubleLevel /
      (phase1RungBase (doubleMiddleLower n) (doubleMiddleLowerD n) ^
          (2 * n - 1) *
        doubleDirectionEta
          (((doubleMiddleLowerD n : ℕ) : ℝ≥0∞) /
            ((doubleMiddleLower n : ℕ) : ℝ≥0∞))
          (phase1RungBase
            (doubleMiddleLower n) (doubleMiddleLowerD n)) ^
              doubleFinalResolutions n γ) ≤
      ENNReal.ofReal
        (Real.exp (-(doubleFinalScale n γ : ℝ) / 100)) := by
  have hnLarge : 4096 ≤ n :=
    phase1_log_twelve_implies_size (hlog.trans' (by norm_num))
  have hnPos : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnPos
  let g := n / 20
  let R := doubleFinalScale n γ
  let Q := doubleEndScale n γ
  let start := z.1.doubleLevel
  let M := doubleFinalResolutions n γ
  have hgLe : g ≤ n := by
    dsimp only [g]
    exact Nat.div_le_self _ _
  have h20g : 20 * g ≤ n := by
    dsimp only [g]
    exact Nat.mul_div_le n 20
  have h20u : n < 20 * g + 20 := by
    dsimp only [g]
    have hd := Nat.div_add_mod n 20
    have hm := Nat.mod_lt n (by norm_num : 0 < 20)
    omega
  have hng : n ≤ 21 * g := by omega
  have hQ : 2 * Q ≤ γ * Nat.log 2 n :=
    doubleEndScale_le n γ
  have hQR : Q ≤ R := by
    dsimp only [R, doubleFinalScale]
    omega
  have hlevel :
      2 * n - Q ≤ start := by
    simpa only [DoubleLateCheckpoint, doubleLateCheckpointLevel, Q,
      doubleEndScale, start] using hz
  have hstartHi : start ≤ 2 * n - 1 := by
    have hlt : z.1.doubleLevel < 2 * n := by
      apply (noncons_iff_level z).1
      intro hc
      exact hncons ⟨hc.1, hc.2.1, hc.2.2⟩
    dsimp only [start]
    omega
  have hLower : doubleMiddleLower n = n + g := by rfl
  have hLowerD : doubleMiddleLowerD n = n - g := by
    unfold doubleMiddleLowerD doubleMiddleLower
    dsimp only [g]
    omega
  have hraw :=
    doubleDirectionError_le_exp n g start (2 * n) M
      hnPos hgLe hstartHi
  rw [← hLower, ← hLowerD] at hraw
  have hbound :
      ((((2 * n - 1 : ℕ) : ℝ) - (start : ℝ)) *
          Real.log (((n + g : ℕ) : ℝ) / (n : ℝ)) -
        (M : ℝ) * (g : ℝ) ^ 2 / (2 * (n : ℝ) ^ 2)) ≤
        -(R : ℝ) / 100 := by
    let D := (2 * n - 1) - start
    have hDcast :
        (((2 * n - 1 : ℕ) : ℝ) - (start : ℝ)) = (D : ℝ) := by
      dsimp only [D]
      rw [Nat.cast_sub hstartHi]
    have hDnat : D ≤ R := by
      dsimp only [D]
      omega
    have hDR : (D : ℝ) ≤ (R : ℝ) := by exact_mod_cast hDnat
    have hratioPos :
        (0 : ℝ) < ((n + g : ℕ) : ℝ) / (n : ℝ) := by
      positivity
    have hlogBase := Real.log_le_sub_one_of_pos hratioPos
    have hratioSub :
        ((n + g : ℕ) : ℝ) / (n : ℝ) - 1 =
          (g : ℝ) / (n : ℝ) := by
      push_cast
      field_simp
      ring
    rw [hratioSub] at hlogBase
    have hratioOne :
        (1 : ℝ) ≤ ((n + g : ℕ) : ℝ) / (n : ℝ) := by
      rw [le_div_iff₀ hnR]
      push_cast
      linarith
    have hlog0 :
        0 ≤ Real.log (((n + g : ℕ) : ℝ) / (n : ℝ)) :=
      Real.log_nonneg hratioOne
    have hgUpper : (g : ℝ) / (n : ℝ) ≤ 1 / 20 := by
      rw [div_le_iff₀ hnR]
      have h20gR : (20 : ℝ) * g ≤ n := by exact_mod_cast h20g
      nlinarith
    have hlogUpper :
        Real.log (((n + g : ℕ) : ℝ) / (n : ℝ)) ≤ 1 / 20 :=
      hlogBase.trans hgUpper
    have hgrowth :
        (D : ℝ) *
            Real.log (((n + g : ℕ) : ℝ) / (n : ℝ)) ≤
          (R : ℝ) / 20 := by
      have hm := mul_le_mul hDR hlogUpper hlog0
        (show (0 : ℝ) ≤ R by positivity)
      nlinarith
    have hgLower : (1 : ℝ) / 21 ≤ (g : ℝ) / (n : ℝ) := by
      rw [le_div_iff₀ hnR]
      have hngR : (n : ℝ) ≤ 21 * g := by exact_mod_cast hng
      nlinarith
    have hsq :
        ((1 : ℝ) / 21) ^ 2 ≤ ((g : ℝ) / (n : ℝ)) ^ 2 := by
      nlinarith [sq_nonneg ((g : ℝ) / (n : ℝ) - 1 / 21)]
    have hM : (M : ℝ) = 64 * (R : ℝ) := by
      dsimp only [M, doubleFinalResolutions, R]
      norm_num
    have hcontract :
        32 * (R : ℝ) / 441 ≤
          (M : ℝ) * (g : ℝ) ^ 2 / (2 * (n : ℝ) ^ 2) := by
      rw [hM]
      calc
        32 * (R : ℝ) / 441 =
            32 * (R : ℝ) * ((1 : ℝ) / 21) ^ 2 := by ring
        _ ≤ 32 * (R : ℝ) * ((g : ℝ) / (n : ℝ)) ^ 2 := by
          gcongr
        _ = 64 * (R : ℝ) * (g : ℝ) ^ 2 /
              (2 * (n : ℝ) ^ 2) := by
          field_simp
          ring
    rw [hDcast]
    nlinarith
  exact hraw.trans
    (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hbound))

/-- The productivity term of the direct final block is exponentially small in
the final logarithmic scale. -/
theorem doubleFinalClockError_le
    (n : ℕ) (hn : 2 ≤ n) (γ : ℕ)
    (hlog : 128 ≤ Nat.log 2 n)
    (z : DoubleState n)
    (hz : DoubleLateCheckpoint n (2 + phase2StageCount n γ) z) :
    let pp :=
      doubleBandProductivity n (doubleMiddleLower n) (2 * n)
    let pp' := 1 - pp
    (pp' + pp * ((1 : ℝ≥0∞) / 2)) ^ doubleFinalHorizon n γ *
        1 / ((1 : ℝ≥0∞) / 2) ^
          (z.1.y + 3 * doubleFinalResolutions n γ) ≤
      ENNReal.ofReal
        (Real.exp (-(doubleFinalScale n γ : ℝ))) := by
  have hnLarge : 4096 ≤ n :=
    phase1_log_twelve_implies_size (hlog.trans' (by norm_num))
  have hnPos : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnPos
  let R := doubleFinalScale n γ
  let Q := doubleEndScale n γ
  let pp :=
    doubleBandProductivity n (doubleMiddleLower n) (2 * n)
  let pp' := 1 - pp
  let x := pp * ((1 : ℝ≥0∞) / 2)
  let δ : ℝ := 1 / (64 * (n : ℝ))
  let δe : ℝ≥0∞ := ENNReal.ofReal δ
  let T := doubleFinalHorizon n γ
  let E := z.1.y + 3 * doubleFinalResolutions n γ
  have hQ : 2 * Q ≤ γ * Nat.log 2 n :=
    doubleEndScale_le n γ
  have hQR : Q ≤ R := by
    dsimp only [R, doubleFinalScale]
    omega
  have hlevel :
      2 * n - Q ≤ z.1.doubleLevel := by
    simpa only [DoubleLateCheckpoint, doubleLateCheckpointLevel, Q,
      doubleEndScale] using hz
  have hco := doubleLevel_add_doubleCoLevel z
  have hyQ : z.1.y ≤ Q := by
    unfold BiCfg.doubleCoLevel at hco
    omega
  have hδ0 : 0 ≤ δ := by
    dsimp only [δ]
    positivity
  have hδ1 : δ ≤ 1 := by
    dsimp only [δ]
    rw [div_le_one (by positivity : (0 : ℝ) < 64 * n)]
    have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hnPos
    nlinarith
  have hwidth :
      doubleMiddleLower n + 2 ≤ 2 * n := by
    unfold doubleMiddleLower
    omega
  have hnLo : n ≤ doubleMiddleLower n + 1 := by
    unfold doubleMiddleLower
    omega
  have hpp1 : pp ≤ 1 := by
    exact doubleBandProductivity_le_one n hn
      (doubleMiddleLower n) (2 * n)
      hnLo hwidth le_rfl
  have hppsum : pp + pp' = 1 := by
    exact doubleBandProductivity_add_compl n hn
      (doubleMiddleLower n) (2 * n)
      hnLo hwidth le_rfl
  have h2δ : 2 * δe ≤ pp := by
    simpa only [δe, δ, pp] using
      doubleFinalProductivity_ge n hn (hlog.trans' (by norm_num))
  have hhalfCancel :
      (2 : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2) = 1 := by
    rw [one_div, ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]
  have hδx : δe ≤ x := by
    calc
      δe = δe * 1 := by rw [mul_one]
      _ = δe * (2 * ((1 : ℝ≥0∞) / 2)) := by rw [hhalfCancel]
      _ = (2 * δe) * ((1 : ℝ≥0∞) / 2) := by ring
      _ ≤ pp * ((1 : ℝ≥0∞) / 2) := by gcongr
      _ = x := rfl
  have hhalfAdd :
      ((1 : ℝ≥0∞) / 2) + ((1 : ℝ≥0∞) / 2) = 1 := by
    calc
      ((1 : ℝ≥0∞) / 2) + ((1 : ℝ≥0∞) / 2) =
          2 * ((1 : ℝ≥0∞) / 2) := by ring
      _ = 1 := hhalfCancel
  have hxx : x + x = pp := by
    dsimp only [x]
    calc
      pp * ((1 : ℝ≥0∞) / 2) +
          pp * ((1 : ℝ≥0∞) / 2) =
          pp * (((1 : ℝ≥0∞) / 2) + (1 / 2)) := by ring
      _ = pp := by rw [hhalfAdd, mul_one]
  have hphiSum : (pp' + x) + δe ≤ 1 := by
    calc
      (pp' + x) + δe ≤ (pp' + x) + x := by
        simpa [add_comm, add_left_comm, add_assoc] using
          add_le_add_left hδx (pp' + x)
      _ = pp' + (x + x) := by ring
      _ = pp' + pp := by rw [hxx]
      _ = 1 := by rw [add_comm, hppsum]
  have hδtop : δe ≠ ⊤ := by
    dsimp only [δe]
    exact ENNReal.ofReal_ne_top
  have hphiSub : pp' + x ≤ 1 - δe :=
    ENNReal.le_sub_of_add_le_right hδtop hphiSum
  have hsub :
      1 - δe = ENNReal.ofReal (1 - δ) := by
    dsimp only [δe]
    rw [ENNReal.ofReal_sub 1 hδ0, ENNReal.ofReal_one]
  have hphi : pp' + x ≤ ENNReal.ofReal (1 - δ) := by
    rwa [← hsub]
  have hnum :
      (pp' + x) ^ T ≤
        ENNReal.ofReal (Real.exp (-(δ * (T : ℝ)))) :=
    enn_pow_le_ofReal_exp (pp' + x) δ T hδ0 hδ1 hphi
  let half : ℝ≥0∞ := (1 : ℝ≥0∞) / 2
  have hdiv :
      (pp' + x) ^ T / half ^ E ≤
        ENNReal.ofReal (Real.exp (-(δ * (T : ℝ)))) /
          half ^ E :=
    ENNReal.div_le_div_right hnum _
  have hhalf :
      half = ENNReal.ofReal (1 / 2 : ℝ) := by
    dsimp only [half]
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have hquot :
      ENNReal.ofReal (Real.exp (-(δ * (T : ℝ)))) /
          half ^ E =
        ENNReal.ofReal
          (Real.exp
            (-(δ * (T : ℝ)) + (E : ℝ) * Real.log 2)) := by
    rw [hhalf, ← ENNReal.ofReal_pow
      (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    rw [← ENNReal.ofReal_div_of_pos
      (by positivity : (0 : ℝ) < (1 / 2 : ℝ) ^ E)]
    congr 2
    have hhalfReal :
        (1 / 2 : ℝ) ^ E =
          Real.exp (-(E : ℝ) * Real.log 2) := by
      rw [← Real.exp_log (by positivity : (0 : ℝ) < (1 / 2 : ℝ) ^ E),
        Real.log_pow]
      have hlogHalf : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
        rw [one_div, Real.log_inv]
      rw [hlogHalf]
      congr 1
      ring
    rw [hhalfReal, ← Real.exp_sub]
    congr 1
    ring
  have hT :
      (T : ℝ) = 65536 * (n : ℝ) * (R : ℝ) := by
    dsimp only [T, doubleFinalHorizon, R]
    norm_num
  have hδT : δ * (T : ℝ) = 1024 * (R : ℝ) := by
    rw [hT]
    dsimp only [δ]
    field_simp
    ring
  have hENat : E ≤ 193 * R := by
    dsimp only [E, doubleFinalResolutions]
    omega
  have hER : (E : ℝ) ≤ 193 * (R : ℝ) := by
    exact_mod_cast hENat
  have hlog2 : Real.log 2 ≤ (0.6931471808 : ℝ) :=
    Real.log_two_lt_d9.le
  have hE0 : (0 : ℝ) ≤ E := by exact_mod_cast Nat.zero_le E
  have hscaledE :
      (E : ℝ) * Real.log 2 ≤
        (193 * (R : ℝ)) * 0.6931471808 := by
    calc
      (E : ℝ) * Real.log 2 ≤ (E : ℝ) * 0.6931471808 :=
        mul_le_mul_of_nonneg_left hlog2 hE0
      _ ≤ (193 * (R : ℝ)) * 0.6931471808 := by gcongr
  have hR0 : (0 : ℝ) ≤ R := by exact_mod_cast Nat.zero_le R
  have hcoef :
      (193 : ℝ) * 0.6931471808 ≤ 134 := by norm_num
  have hexponent :
      -(δ * (T : ℝ)) + (E : ℝ) * Real.log 2 ≤ -(R : ℝ) := by
    rw [hδT]
    calc
      -(1024 * (R : ℝ)) + (E : ℝ) * Real.log 2 ≤
          -(1024 * (R : ℝ)) +
            (193 * (R : ℝ)) * 0.6931471808 :=
        by
          simpa only [add_comm] using
            add_le_add_left hscaledE (-(1024 * (R : ℝ)))
      _ = (-1024 + 193 * 0.6931471808) * (R : ℝ) := by ring
      _ ≤ (-1024 + 134) * (R : ℝ) := by gcongr
      _ = (-890 : ℝ) * (R : ℝ) := by ring
      _ ≤ (-1 : ℝ) * (R : ℝ) :=
        mul_le_mul_of_nonneg_right (by norm_num) hR0
      _ = -(R : ℝ) := by ring
  change (pp' + x) ^ T * 1 / half ^ E ≤ _
  rw [mul_one]
  exact hdiv.trans (hquot.le.trans
    (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hexponent)))

/-- Non-consensus mass agrees before and after projecting the invariant subtype
to physical configurations. -/
theorem doubleState_nonconsensus_mass_eq
    (n : ℕ) (hn : 2 ≤ n) (T : ℕ) (s : DoubleState n) :
    (∑' z : DoubleState n,
        if DoubleXConsensus z then 0
        else iter (doubleStateStep n hn) T s z) =
      ∑' z : BiCfg,
        if BiXConsensus n z then 0
        else iter doubleBChain T s.1 z := by
  rw [masked_eq_expect, masked_eq_expect,
    iter_doubleBChain_eq_map n hn T s, expect_map]
  unfold expect
  apply tsum_congr
  intro z
  congr 1

/-- A single direct block reaches absorbing all-`X` consensus from the
logarithmic co-level checkpoint. -/
theorem doubleFinalConsensus_reaches
    (n : ℕ) (hn : 2 ≤ n) (γ : ℕ)
    (hlog : 128 ≤ Nat.log 2 n) (hγ : 1 ≤ γ)
    (hsize : 6 * γ * Nat.log 2 n ≤ n) :
    Reaches (doubleStateStep n hn) (doubleFinalHorizon n γ)
      (DoubleLateCheckpoint n (2 + phase2StageCount n γ))
      DoubleXConsensus
      (3 * ENNReal.ofReal
        (Real.exp (-(doubleFinalScale n γ : ℝ) / 100))) := by
  intro s hs
  rw [doubleState_nonconsensus_mass_eq n hn
    (doubleFinalHorizon n γ) s]
  by_cases hcons : DoubleXConsensus s
  · have hsval : s.1 = ⟨n, 0, 0⟩ := by
      rcases s with ⟨⟨x, y, b⟩, hinv⟩
      simp only [DoubleXConsensus] at hcons
      simp only
      rcases hcons with ⟨rfl, rfl, rfl⟩
      rfl
    rw [hsval]
    have hiter :
        iter doubleBChain (doubleFinalHorizon n γ) ⟨n, 0, 0⟩ =
          PMF.pure ⟨n, 0, 0⟩ := by
      induction doubleFinalHorizon n γ with
      | zero => rfl
      | succ T ih =>
          rw [iter_succ, doubleBChain_consensusX n hn,
            PMF.pure_bind, ih]
    rw [hiter]
    have hzero :
        (∑' z : BiCfg,
          if BiXConsensus n z then 0
          else PMF.pure ⟨n, 0, 0⟩ z) = 0 := by
      calc
        (∑' z : BiCfg,
          if BiXConsensus n z then 0
          else PMF.pure ⟨n, 0, 0⟩ z) =
            ∑' _z : BiCfg, (0 : ℝ≥0∞) := by
          apply tsum_congr
          intro z
          by_cases hz : z = ⟨n, 0, 0⟩
          · subst z
            simp [BiXConsensus]
          · simp [PMF.pure_apply, hz]
        _ = 0 := tsum_zero
    rw [hzero]
    exact bot_le
  · have hnLarge : 4096 ≤ n :=
      phase1_log_twelve_implies_size (hlog.trans' (by norm_num))
    let g := n / 20
    let a := doubleMiddleLower n
    let bR := doubleMiddleLowerR n
    let bD := doubleMiddleLowerD n
    let k := s.1.doubleLevel - a
    let M := doubleFinalResolutions n γ
    let T := doubleFinalHorizon n γ
    let w := phase1RungBase a bD
    let u : ℝ≥0∞ := (bD : ℝ≥0∞) / (a : ℝ≥0∞)
    let η := doubleDirectionEta u w
    let wp : ℝ≥0∞ := (1 : ℝ≥0∞) / 2
    let pp := doubleBandProductivity n a (2 * n)
    let pp' := 1 - pp
    have h20g : 20 * g ≤ n := by
      dsimp only [g]
      exact Nat.mul_div_le n 20
    have h20u : n < 20 * g + 20 := by
      dsimp only [g]
      have hd := Nat.div_add_mod n 20
      have hm := Nat.mod_lt n (by norm_num : 0 < 20)
      omega
    have ha : a = n + g := by rfl
    have hbR : bR = n - g - 2 := by
      dsimp only [bR, doubleMiddleLowerR, doubleMiddleLower, g]
      omega
    have hbD : bD = n - g := by
      dsimp only [bD, doubleMiddleLowerD, doubleMiddleLower, g]
      omega
    have haLoLt : a < 2 * n := by rw [ha]; omega
    have hpopR : a + bR + 2 = 2 * n := by
      rw [ha, hbR]
      omega
    have haPos : 0 < a := by rw [ha]; omega
    have hbRPos : 0 < bR := by rw [hbR]; omega
    have hmajR : bR ≤ a := by rw [ha, hbR]; omega
    have heqD : a + bD = 2 * n := by rw [ha, hbD]; omega
    have hmajD : bD ≤ a := by rw [ha, hbD]; omega
    have hnLo : n ≤ a + 1 := by rw [ha]; omega
    have hwidth : a + 2 ≤ 2 * n := by rw [ha]; omega
    have hwSpec := phase1RungBase_spec haPos (by
      rw [ha, hbD]
      omega : bD < a)
    have hu0 : 0 < u := by
      unfold u
      apply ENNReal.div_pos
      · simp only [ne_eq, Nat.cast_eq_zero]
        omega
      · exact ENNReal.natCast_ne_top _
    have huw : u < w := by
      simpa only [u, w] using hwSpec.2.2
    have hwlt : w < 1 := by
      simpa only [w] using hwSpec.2.1
    have hηSpec := doubleDirectionEta_spec hu0 huw hwlt
    have hw1 : w ≤ 1 := hwlt.le
    have hw0 : w ≠ 0 := hwSpec.1.ne'
    have hpp1 : pp ≤ 1 := by
      exact doubleBandProductivity_le_one n hn a (2 * n)
        hnLo hwidth le_rfl
    have hppsum : pp + pp' = 1 := by
      exact doubleBandProductivity_add_compl n hn a (2 * n)
        hnLo hwidth le_rfl
    have hppT : pp ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.one_ne_top hpp1
    have hpp'1 : pp' ≤ 1 := tsub_le_self
    have hpp'T : pp' ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.one_ne_top hpp'1
    have hBprod : ∀ q : DoubleTrace n,
        ¬ (q.cfg.1.doubleLevel ≤ a ∨ BiXConsensus n q.cfg.1) →
        pp ≤
          dbPairPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b (by
            have := q.cfg.2
            simp only [BiCfg.DoubleInv] at this
            omega) .xy +
          dbPairPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b (by
            have := q.cfg.2
            simp only [BiCfg.DoubleInv] at this
            omega) .xb +
          dbPairPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b (by
            have := q.cfg.2
            simp only [BiCfg.DoubleInv] at this
            omega) .yb := by
      intro q hq
      apply doubleBandProductivity_le n hn a (2 * n)
        hnLo le_rfl q.cfg
      rw [not_or]
      exact ⟨(not_or.mp hq).1, by
        have hncons : ¬ BiXConsensus n q.cfg.1 := (not_or.mp hq).2
        have hlt := (noncons_iff_level q.cfg).1 hncons
        omega⟩
    have hlevel :
        2 * n - doubleEndScale n γ ≤ s.1.doubleLevel := by
      simpa only [DoubleLateCheckpoint, doubleLateCheckpointLevel,
        doubleEndScale] using hs
    have haLevel : a ≤ s.1.doubleLevel := by
      have hQ := doubleEndScale_le n γ
      have hprod : 128 ≤ γ * Nat.log 2 n := by
        calc
          128 = 1 * 128 := by norm_num
          _ ≤ γ * Nat.log 2 n := Nat.mul_le_mul hγ hlog
      have hsize' : 6 * (γ * Nat.log 2 n) ≤ n := by
        calc
          6 * (γ * Nat.log 2 n) = 6 * γ * Nat.log 2 n := by ring
          _ ≤ n := hsize
      rw [ha]
      omega
    have hstart : s.1.doubleLevel = a + k := by
      dsimp only [k]
      exact (Nat.add_sub_of_le haLevel).symm
    have hraw :=
      noncons_mass_bound n hn a bR bD k M T
        haLoLt hpopR haPos hbRPos hmajR heqD hmajD
        w η u rfl hηSpec.1 hηSpec.2.1 hw1 hw0
        hηSpec.2.2.1 hηSpec.2.2.2
        wp pp pp'
        (by dsimp only [wp]; norm_num)
        (by dsimp only [wp]; norm_num) hppsum
        (by dsimp only [wp]; finiteness) hppT hpp'T hBprod s hstart
    have hsafety :=
      doubleFinalSafetyError_le n γ hlog hγ hsize s hs
    have hdirection :=
      doubleFinalDirectionError_le n γ hlog s hs hcons
    have hclock :=
      doubleFinalClockError_le n hn γ hlog s hs
    let e :=
      ENNReal.ofReal
        (Real.exp (-(doubleFinalScale n γ : ℝ) / 100))
    have hclockEnvelope :
        (pp' + pp * wp) ^ T * 1 /
            wp ^ (s.1.y + 3 * M) ≤ e := by
      have hR0 : (0 : ℝ) ≤ doubleFinalScale n γ := by positivity
      have hexp :
          -(doubleFinalScale n γ : ℝ) ≤
            -(doubleFinalScale n γ : ℝ) / 100 := by
        nlinarith
      exact hclock.trans
        (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hexp))
    refine hraw.trans ?_
    change
      (((bR : ℝ≥0∞) / (a : ℝ≥0∞)) ^ k +
          w ^ s.1.doubleLevel /
            (w ^ (2 * n - 1) * η ^ M) +
        (pp' + pp * wp) ^ T * 1 /
          wp ^ (s.1.y + 3 * M)) ≤ 3 * e
    calc
      _ ≤ (e + e) + e := by
        dsimp only [a, bR, bD, k, M, T, w, u, η, wp, pp, pp', e]
          at hsafety hdirection hclockEnvelope ⊢
        gcongr
      _ = 3 * e := by ring

/-- The final exponential envelope fits the common headline power law. -/
theorem doubleFinalExponential_le_power
    (n γ : ℕ) (hlog : 128 ≤ Nat.log 2 n) :
    ENNReal.ofReal
        (Real.exp (-(doubleFinalScale n γ : ℝ) / 100)) ≤
      (n : ℝ≥0∞)⁻¹ ^ ((1 / 200 : ℝ) * (γ : ℝ)) := by
  have hnPos : 0 < n := by
    have hnLarge : 4096 ≤ n :=
      phase1_log_twelve_implies_size (hlog.trans' (by norm_num))
    omega
  have hrpow :
      (n : ℝ≥0∞)⁻¹ ^ ((1 / 200 : ℝ) * (γ : ℝ)) =
        ENNReal.ofReal
          ((n : ℝ) ^ (-((1 / 200 : ℝ) * (γ : ℝ)))) := by
    rw [ENNReal.inv_rpow, ← ENNReal.ofReal_natCast n,
      ENNReal.ofReal_rpow_of_pos (by exact_mod_cast hnPos),
      ← ENNReal.ofReal_inv_of_pos (by positivity),
      Real.rpow_neg (by positivity)]
  rw [hrpow]
  apply ENNReal.ofReal_le_ofReal
  have hpExp :
      (0 : ℝ) <
        Real.exp (-(doubleFinalScale n γ : ℝ) / 100) :=
    Real.exp_pos _
  have hpPow :
      (0 : ℝ) <
        (n : ℝ) ^ (-((1 / 200 : ℝ) * (γ : ℝ))) :=
    Real.rpow_pos_of_pos (by exact_mod_cast hnPos) _
  have hlogIneq :
      Real.log
          (Real.exp (-(doubleFinalScale n γ : ℝ) / 100)) ≤
        Real.log
          ((n : ℝ) ^ (-((1 / 200 : ℝ) * (γ : ℝ)))) := by
    rw [Real.log_exp, Real.log_rpow (by exact_mod_cast hnPos)]
    have hlog2 : Real.log 2 < (0.6931471808 : ℝ) :=
      Real.log_two_lt_d9
    have hlogn :
        Real.log n ≤
          ((Nat.log 2 n : ℝ) + 1) * Real.log 2 := by
      have hup : n < 2 ^ (Nat.log 2 n + 1) :=
        Nat.lt_pow_succ_log_self (by norm_num) n
      have hlt :
          Real.log n < Real.log (2 ^ (Nat.log 2 n + 1)) :=
        Real.log_lt_log (by exact_mod_cast hnPos)
          (by exact_mod_cast hup)
      rw [Real.log_pow] at hlt
      push_cast at hlt
      linarith
    have hL : (128 : ℝ) ≤ Nat.log 2 n := by exact_mod_cast hlog
    have hfactor :
        ((Nat.log 2 n : ℝ) + 1) * Real.log 2 ≤
          (Nat.log 2 n : ℝ) := by
      have hlog2Nonneg : 0 ≤ Real.log 2 :=
        (Real.log_pos (by norm_num)).le
      nlinarith
    have hgammaLog :
        (γ : ℝ) * Real.log n ≤
          (γ : ℝ) * (Nat.log 2 n : ℝ) := by
      apply mul_le_mul_of_nonneg_left (hlogn.trans hfactor)
      positivity
    have hscale :
        (γ : ℝ) * (Nat.log 2 n : ℝ) ≤
          (doubleFinalScale n γ : ℕ) := by
      unfold doubleFinalScale
      norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_one]
      linarith
    nlinarith
  have hexp := Real.exp_le_exp.mpr hlogIneq
  rwa [Real.exp_log hpExp, Real.exp_log hpPow] at hexp

/-- Power-law form of the direct final consensus block. -/
theorem doubleFinalConsensus_reaches_power
    (n : ℕ) (hn : 2 ≤ n) (γ : ℕ)
    (hlog : 128 ≤ Nat.log 2 n) (hγ : 1 ≤ γ)
    (hsize : 6 * γ * Nat.log 2 n ≤ n) :
    Reaches (doubleStateStep n hn) (doubleFinalHorizon n γ)
      (DoubleLateCheckpoint n (2 + phase2StageCount n γ))
      DoubleXConsensus
      (3 * (n : ℝ≥0∞)⁻¹ ^
        ((1 / 200 : ℝ) * (γ : ℝ))) := by
  apply (doubleFinalConsensus_reaches n hn γ hlog hγ hsize).mono_error
  gcongr
  exact doubleFinalExponential_le_power n γ hlog

end Tri

#print axioms Tri.doubleFinalProductivity_ge
#print axioms Tri.doubleFinalSafetyError_le
#print axioms Tri.doubleFinalDirectionError_le
#print axioms Tri.doubleFinalClockError_le
#print axioms Tri.doubleState_nonconsensus_mass_eq
#print axioms Tri.doubleFinalConsensus_reaches
#print axioms Tri.doubleFinalExponential_le_power
#print axioms Tri.doubleFinalConsensus_reaches_power
