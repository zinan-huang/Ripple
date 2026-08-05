/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.HeavyBLateLadder
import Tri.HeavyBInvariant
import Tri.HeavyBStaged
import Tri.HitThenReaches

/-!
# Direct Heavy-B consensus from the logarithmic co-level checkpoint

The upper boundary of the final Heavy-B band is `n`, i.e. all-`X`
consensus.  Since that boundary is absorbing, freezing there is dynamically
invisible; only the fixed lower ruin boundary contributes an extra error term.
-/

namespace Tri

open scoped ENNReal

def heavyFinalScale (n γ : ℕ) : ℕ :=
  γ * Nat.log 2 n + 1

def heavyFinalResolutions (n γ : ℕ) : ℕ :=
  64 * heavyFinalScale n γ

def heavyFinalHorizon (n γ : ℕ) : ℕ :=
  65536 * n * heavyFinalScale n γ

def heavyFinalThreshold (n : ℕ) : ℕ :=
  n - 1

/-- Non-consensus is exactly being below the maximal Heavy-B level. -/
theorem heavy_noncons_iff_level_lt_n {n : ℕ} (s : HeavyState n) :
    ¬ HeavyXConsensus s ↔ BiCfg.heavyLevel s.1 < n := by
  constructor
  · intro hcons
    have hle : BiCfg.heavyLevel s.1 ≤ n := by
      have hco := BiCfg.heavyLevel_add_coLevel s.2
      omega
    have hne : BiCfg.heavyLevel s.1 ≠ n := by
      intro h
      exact hcons ((heavyLevel_eq_n_iff s).1 h)
    omega
  · intro hlt hcons
    have hlevel := (heavyLevel_eq_n_iff s).2 hcons
    omega

/-- The fixed lower-boundary productivity floor used in the final direct
consensus block. -/
theorem heavyFinalProductivity_ge
    (n : ℕ) (hn : 3 ≤ n) (hlog : 12 ≤ Nat.log 2 n) :
    2 * ENNReal.ofReal
        ((1 : ℝ) / (64 * (n : ℝ))) ≤
      heavyBandProductivity n (heavyMiddleProdGap n) 1 := by
  have hnLarge : 4096 ≤ n := phase1_log_twelve_implies_size hlog
  have hnPos : 0 < n := by omega
  let d := heavyMiddleProdGap n
  let A := d
  let Bc := Nat.choose n 2
  have h2 := Nat.mul_div_le n 2
  have h2u : n < 2 * (n / 2) + 2 := by
    have hd := Nat.div_add_mod n 2
    have hm := Nat.mod_lt n (by norm_num : 0 < 2)
    omega
  have h48 := Nat.mul_div_le n 48
  have h48u : n < 48 * (n / 48) + 48 := by
    have hd := Nat.div_add_mod n 48
    have hm := Nat.mod_lt n (by norm_num : 0 < 48)
    omega
  have hdLower : n ≤ 32 * d := by
    dsimp only [d, heavyMiddleProdGap, heavyMiddleLower]
    omega
  have hchoose : 2 * Bc = n * (n - 1) := by
    dsimp only [Bc]
    have h := two_mul_choose_two_succ (n - 1)
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ n)] using h
  have hcross : Bc ≤ (32 * n) * A := by
    have hB2 : 2 * Bc ≤ 2 * ((32 * n) * A) := by
      rw [hchoose]
      calc
        n * (n - 1) ≤ n * n := Nat.mul_le_mul_left n (by omega : n - 1 ≤ n)
        _ ≤ n * (32 * d) := Nat.mul_le_mul_left n hdLower
        _ = (32 * n) * A := by dsimp only [A]; ring
        _ ≤ 2 * ((32 * n) * A) := by omega
    exact Nat.le_of_mul_le_mul_left hB2 (by norm_num : 0 < 2)
  have hleftTop :
      2 * ENNReal.ofReal ((1 : ℝ) / (64 * (n : ℝ))) ≠ ⊤ := by
    finiteness
  have hrightTop :
      heavyBandProductivity n d 1 ≠ ⊤ := by
    unfold heavyBandProductivity
    apply ENNReal.div_ne_top
    · exact ENNReal.natCast_ne_top _
    · simp only [ne_eq, Nat.cast_eq_zero]
      exact (Nat.choose_pos (by omega : 2 ≤ n)).ne'
  rw [← ENNReal.toReal_le_toReal hleftTop hrightTop]
  unfold heavyBandProductivity
  dsimp only [d, A, Bc]
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
    ENNReal.toReal_ofNat, ENNReal.toReal_div]
  norm_num only [ENNReal.toReal_ofNat, ENNReal.toReal_natCast]
  change
    2 * ((1 : ℝ) / (64 * (n : ℝ))) ≤
      ((heavyMiddleProdGap n * 1 : ℕ) : ℝ) /
        ((Nat.choose n 2 : ℕ) : ℝ)
  have hBR : (0 : ℝ) < (Nat.choose n 2 : ℕ) := by
    exact_mod_cast Nat.choose_pos (by omega : 2 ≤ n)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnPos
  have hleftEq :
      2 * ((1 : ℝ) / (64 * (n : ℝ))) =
        (1 : ℝ) / (32 * (n : ℝ)) := by
    field_simp
    ring
  rw [hleftEq]
  rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 32 * n) hBR]
  have hcrossR :
      ((Nat.choose n 2 : ℕ) : ℝ) ≤
        (((32 * n) * heavyMiddleProdGap n : ℕ) : ℝ) := by
    exact_mod_cast hcross
  norm_num only [Nat.cast_mul, Nat.cast_ofNat] at hcrossR ⊢
  calc
    (1 : ℝ) * (Nat.choose n 2 : ℝ)
        ≤ (32 * n : ℝ) * heavyMiddleProdGap n := by
          simpa only [one_mul] using hcrossR
    _ = (heavyMiddleProdGap n * 1 : ℝ) * (32 * n : ℝ) := by ring

/-- The final checkpoint's dyadic co-level scale. -/
def heavyFinalEntryScale (n γ : ℕ) : ℕ :=
  phase2Scale n (2 + phase2StageCount n γ)

theorem heavyFinalEntryScale_le (n γ : ℕ) :
    2 * heavyFinalEntryScale n γ ≤ γ * Nat.log 2 n := by
  simpa only [heavyFinalEntryScale] using phase2StageCount_spec n γ

/-- The lower-ruin term from any state in the final logarithmic checkpoint is
exponentially small in `γ lg n + 1`. -/
theorem heavyFinalSafetyError_le
    (n γ : ℕ) (hlog : 128 ≤ Nat.log 2 n) (hγ : 1 ≤ γ)
    (hsize : 6 * γ * Nat.log 2 n ≤ n)
    (z : HeavyState n)
    (hz : HeavyLateCheckpoint n (1 + phase2StageCount n γ) z) :
    let k := BiCfg.heavyLevel z.1 - heavyMiddleLower n
    (((heavyMiddleLowerBHi n : ℕ) : ℝ≥0∞) /
        ((heavyMiddleLower n : ℕ) : ℝ≥0∞)) ^ k ≤
      ENNReal.ofReal
        (Real.exp (-(heavyFinalScale n γ : ℝ) / 100)) := by
  have hnLarge : 4096 ≤ n :=
    phase1_log_twelve_implies_size (hlog.trans' (by norm_num))
  let R := heavyFinalScale n γ
  let Q := heavyFinalEntryScale n γ
  let a := heavyMiddleLower n
  let b := heavyMiddleLowerBHi n
  let k := BiCfg.heavyLevel z.1 - a
  have hQ : 2 * Q ≤ γ * Nat.log 2 n :=
    heavyFinalEntryScale_le n γ
  have hQR : Q ≤ R := by
    dsimp only [R, heavyFinalScale]
    omega
  have hlevel :
      n - Q ≤ BiCfg.heavyLevel z.1 := by
    unfold HeavyLateCheckpoint at hz
    have hidx :
        (1 + phase2StageCount n γ) + 1 =
          2 + phase2StageCount n γ := by omega
    rw [hidx] at hz
    change n ≤ BiCfg.heavyLevel z.1 + Q at hz
    omega
  have hprod : 128 ≤ γ * Nat.log 2 n := by
    calc
      128 = 1 * 128 := by norm_num
      _ ≤ γ * Nat.log 2 n := Nat.mul_le_mul hγ hlog
  have hRfive : 5 * R ≤ n := by
    calc
      5 * R = 5 * (γ * Nat.log 2 n + 1) := by rfl
      _ ≤ 6 * (γ * Nat.log 2 n) := by omega
      _ = 6 * γ * Nat.log 2 n := by ring
      _ ≤ n := hsize
  have haThree : 5 * a ≤ 3 * n := by
    dsimp only [a, heavyMiddleLower]
    have h2 := Nat.mul_div_le n 2
    have h48 := Nat.mul_div_le n 48
    omega
  have haLevel : a ≤ BiCfg.heavyLevel z.1 := by
    have h2R : 2 * R ≤ n - a := by omega
    calc
      a ≤ n - 2 * R := by omega
      _ ≤ n - Q := by omega
      _ ≤ BiCfg.heavyLevel z.1 := hlevel
  have hak : a + k = BiCfg.heavyLevel z.1 := by
    dsimp only [k]
    exact Nat.add_sub_of_le haLevel
  have hRk : R ≤ k := by
    rw [← hak] at hlevel
    omega
  have hbPos : 0 < b := by
    rcases heavyMiddle_geometry (hlog.trans' (by norm_num)) with
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hb, _, _, _, _, _, _, _, _, _, _⟩
    simpa only [b] using hb
  have hba : b ≤ a := by
    rcases heavyMiddle_geometry (hlog.trans' (by norm_num)) with
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hmaj, _, _, _, _, _, _, _, _, _⟩
    simpa only [a, b] using hmaj
  have hdiff : a ≤ 13 * (a - b) := by
    dsimp only [a, b, heavyMiddleLower, heavyMiddleLowerBHi]
    omega
  have hcross : R * a ≤ 100 * k * (a - b) := by
    calc
      R * a ≤ R * (13 * (a - b)) :=
        Nat.mul_le_mul_left R hdiff
      _ = (13 * R) * (a - b) := by ring
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

set_option maxHeartbeats 2000000 in
-- The Padé direction estimate reuses the final-band real exponent algebra.
/-- The direction term from any non-consensus final-checkpoint state is
exponentially small in the final logarithmic scale. -/
theorem heavyFinalDirectionError_le
    (n γ : ℕ) (hlog : 128 ≤ Nat.log 2 n)
    (z : HeavyState n)
    (hz : HeavyLateCheckpoint n (1 + phase2StageCount n γ) z)
    (hncons : ¬ HeavyXConsensus z) :
    let w : ℝ≥0∞ := ENNReal.ofReal (heavyBandW (heavyDirA n) (heavyDirB n))
    let η : ℝ≥0∞ := ENNReal.ofReal (heavyBandEta (heavyDirA n) (heavyDirB n))
    w ^ BiCfg.heavyLevel z.1 /
      (w ^ heavyFinalThreshold n * η ^ heavyFinalResolutions n γ) ≤
      ENNReal.ofReal
        (Real.exp (-(heavyFinalScale n γ : ℝ) / 100)) := by
  have hlog12 : 12 ≤ Nat.log 2 n := hlog.trans' (by norm_num)
  rcases heavyMiddle_geometry hlog12 with
    ⟨ha, hB, hparam, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, _, _, _, _, _, _, _⟩
  have hnLarge : 4096 ≤ n := phase1_log_twelve_implies_size hlog12
  have hnPos : 0 < n := by omega
  let a := heavyDirA n
  let B := heavyDirB n
  let wR := heavyBandW a B
  let ηR := heavyBandEta a B
  let R := heavyFinalScale n γ
  let Q := heavyFinalEntryScale n γ
  let start := BiCfg.heavyLevel z.1
  let thr := n - 1
  let M := heavyFinalResolutions n γ
  let D := thr - start
  have hQ : 2 * Q ≤ γ * Nat.log 2 n :=
    heavyFinalEntryScale_le n γ
  have hQR : Q ≤ R := by
    dsimp only [R, heavyFinalScale]
    omega
  have hlevel :
      n - Q ≤ start := by
    unfold HeavyLateCheckpoint at hz
    have hidx :
        (1 + phase2StageCount n γ) + 1 =
          2 + phase2StageCount n γ := by omega
    rw [hidx] at hz
    change n ≤ BiCfg.heavyLevel z.1 + Q at hz
    dsimp only [start]
    omega
  have hstartThr : start ≤ thr := by
    have hlt : start < n := by
      simpa only [start] using (heavy_noncons_iff_level_lt_n z).1 hncons
    dsimp only [thr]
    omega
  have hDadd : start + D = thr := by
    dsimp only [D]
    omega
  have hDle : D ≤ R := by
    dsimp only [D, thr] at hlevel hstartThr ⊢
    omega
  have hwpos : 0 < wR := by
    obtain ⟨hu, huw, _⟩ := heavyBand_tail_regime (a := a) (B := B)
      (by simpa only [a, B] using ha) (by simpa only [a, B] using hB)
    exact hu.trans huw
  have hw0 : 0 ≤ wR := hwpos.le
  have hηpos : 0 < ηR := heavyBandEta_pos
    (by simpa only [a, B] using ha) (by simpa only [a, B] using hB)
  have hη0 : 0 ≤ ηR := hηpos.le
  have hdenpos : 0 < wR ^ thr * ηR ^ M :=
    mul_pos (pow_pos hwpos _) (pow_pos hηpos _)
  change
    ENNReal.ofReal wR ^ start /
      (ENNReal.ofReal wR ^ thr * ENNReal.ofReal ηR ^ M) ≤
      ENNReal.ofReal (Real.exp (-(R : ℝ) / 100))
  rw [← ENNReal.ofReal_pow hw0, ← ENNReal.ofReal_pow hw0,
    ← ENNReal.ofReal_pow hη0,
    ← ENNReal.ofReal_mul (pow_nonneg hw0 thr),
    ← ENNReal.ofReal_div_of_pos hdenpos]
  apply ENNReal.ofReal_le_ofReal
  let x : ℝ := (B : ℝ) / ((a : ℝ) + 2 * (B : ℝ))
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnPos
  have hparamR : (a : ℝ) + 2 * (B : ℝ) = n := by
    exact_mod_cast (by simpa only [a, B] using hparam)
  have hxN : x = (B : ℝ) / (n : ℝ) := by
    dsimp only [x]
    rw [hparamR]
  have hx0 : 0 ≤ x := by
    dsimp only [x]
    positivity
  have h1x : 0 < 1 + x := by positivity
  have hw_eq : wR = 1 / (1 + x) := by
    dsimp only [wR, x, a, B]
    exact heavyBandW_eq_one_div ha hB
  have hlogTerm :
      Real.log (wR ^ start / (wR ^ thr * ηR ^ M)) =
        (D : ℝ) * Real.log (1 + x) - (M : ℝ) * Real.log ηR := by
    rw [Real.log_div (pow_ne_zero _ (ne_of_gt hwpos))
        (ne_of_gt hdenpos),
      Real.log_mul (pow_ne_zero _ (ne_of_gt hwpos))
        (pow_ne_zero _ (ne_of_gt hηpos)),
      Real.log_pow, Real.log_pow, Real.log_pow, hw_eq, one_div,
      Real.log_inv]
    rw [Nat.cast_sub hstartThr]
    ring
  have hlog1x0 : 0 ≤ Real.log (1 + x) :=
    Real.log_nonneg (by
      rw [hxN]
      have hxnonneg : (0 : ℝ) ≤ (B : ℝ) / (n : ℝ) := by positivity
      nlinarith)
  have hDnat : D * n ≤ M * B := by
    have h50u : n < 50 * (n / 50) + 50 := by
      have hd := Nat.div_add_mod n 50
      have hm := Nat.mod_lt n (by norm_num : 0 < 50)
      omega
    have hnB : n ≤ 64 * B := by
      dsimp only [B, heavyDirB]
      omega
    calc
      D * n ≤ R * n := Nat.mul_le_mul_right n hDle
      _ ≤ R * (64 * B) := Nat.mul_le_mul_left R hnB
      _ = (64 * R) * B := by ring
      _ = M * B := by
        dsimp only [M, heavyFinalResolutions, R]
  have hDreal : (D : ℝ) ≤ (M : ℝ) * x := by
    rw [hxN]
    have hDnatR : ((D * n : ℕ) : ℝ) ≤ ((M * B : ℕ) : ℝ) := by
      exact_mod_cast hDnat
    norm_num only [Nat.cast_mul] at hDnatR
    calc
      (D : ℝ) ≤ ((M : ℝ) * (B : ℝ)) / (n : ℝ) := by
        rw [le_div_iff₀ hnR]
        nlinarith
      _ = (M : ℝ) * ((B : ℝ) / (n : ℝ)) := by ring
  have hsharp := heavyBand_deadline_exponent_sharp
    (a := a) (B := B) (by simpa only [a, B] using ha)
    (by simpa only [a, B] using hB)
  change x ^ 2 / 2 ≤ Real.log ηR - x * Real.log (1 + x) at hsharp
  have hgrowth :
      (D : ℝ) * Real.log (1 + x) ≤
        ((M : ℝ) * x) * Real.log (1 + x) :=
    mul_le_mul_of_nonneg_right hDreal hlog1x0
  have hmain :
      (D : ℝ) * Real.log (1 + x) - (M : ℝ) * Real.log ηR ≤
        -((M : ℝ) * (x ^ 2 / 2)) := by
    nlinarith
  have hnHuge : 2 ^ 128 ≤ n := by
    have hpow : 2 ^ 128 ≤ 2 ^ Nat.log 2 n :=
      Nat.pow_le_pow_right (by norm_num) hlog
    exact hpow.trans (Nat.pow_log_le_self 2 hnPos.ne')
  have hn4900 : 4900 ≤ n :=
    (by norm_num : 4900 ≤ 2 ^ 128).trans hnHuge
  have hBsq : n * n ≤ 2560 * (B * B) := by
    have h50u : n < 50 * (n / 50) + 50 := by
      have hd := Nat.div_add_mod n 50
      have hm := Nat.mod_lt n (by norm_num : 0 < 50)
      omega
    have hBbig : 98 ≤ B := by
      dsimp only [B, heavyDirB]
      omega
    have h2nB : 2 * n ≤ 101 * B := by
      dsimp only [B, heavyDirB] at hBbig ⊢
      omega
    have h4sq : 4 * (n * n) ≤ 4 * (2560 * (B * B)) := by
      calc
        4 * (n * n) = (2 * n) * (2 * n) := by ring
        _ ≤ (101 * B) * (101 * B) :=
          Nat.mul_le_mul h2nB h2nB
        _ = 10201 * (B * B) := by ring
        _ ≤ 10240 * (B * B) := by
          exact Nat.mul_le_mul_right (B * B) (by norm_num : 10201 ≤ 10240)
        _ = 4 * (2560 * (B * B)) := by ring
    exact Nat.le_of_mul_le_mul_left h4sq (by norm_num : 0 < 4)
  have hE :
      (R : ℝ) / 100 ≤ (M : ℝ) * (x ^ 2 / 2) := by
    have hBsqR : (n : ℝ) ^ 2 ≤ 2560 * (B : ℝ) ^ 2 := by
      have hBsq' : n ^ 2 ≤ 2560 * B ^ 2 := by
        simpa [pow_two] using hBsq
      exact_mod_cast hBsq'
    have hright :
        (M : ℝ) * (x ^ 2 / 2) =
          32 * (R : ℝ) * (B : ℝ) ^ 2 / (n : ℝ) ^ 2 := by
      dsimp only [M, heavyFinalResolutions]
      rw [hxN]
      dsimp only [R]
      field_simp [hnR.ne']
      norm_num only [Nat.cast_mul, Nat.cast_ofNat]
      ring_nf
    rw [hright]
    rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 100)
      (by positivity : (0 : ℝ) < (n : ℝ) ^ 2)]
    have hmul :=
      mul_le_mul_of_nonneg_left hBsqR
        (by positivity : (0 : ℝ) ≤ (R : ℝ))
    nlinarith
  have hlogBound :
      Real.log (wR ^ start / (wR ^ thr * ηR ^ M)) ≤
        -(R : ℝ) / 100 := by
    rw [hlogTerm]
    nlinarith
  calc
    wR ^ start / (wR ^ thr * ηR ^ M) =
        Real.exp (Real.log (wR ^ start / (wR ^ thr * ηR ^ M))) := by
      rw [Real.exp_log]
      positivity
    _ ≤ Real.exp (-(R : ℝ) / 100) :=
      Real.exp_le_exp.mpr hlogBound

/-- The productivity-clock term of the direct final block is exponentially
small in the final logarithmic scale. -/
theorem heavyFinalClockError_le
    (n : ℕ) (hn : 3 ≤ n) (γ : ℕ)
    (hlog : 128 ≤ Nat.log 2 n) :
    let pp := heavyBandProductivity n (heavyMiddleProdGap n) 1
    let pp' := 1 - pp
    (pp' + pp * ((1 : ℝ≥0∞) / 2)) ^ heavyFinalHorizon n γ /
        ((1 : ℝ≥0∞) / 2) ^
          (heavyFinalEntryScale n γ + 3 * heavyFinalResolutions n γ) ≤
      ENNReal.ofReal
        (Real.exp (-(heavyFinalScale n γ : ℝ))) := by
  have hnLarge : 4096 ≤ n :=
    phase1_log_twelve_implies_size (hlog.trans' (by norm_num))
  have hnPos : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnPos
  let R := heavyFinalScale n γ
  let Q := heavyFinalEntryScale n γ
  let pp := heavyBandProductivity n (heavyMiddleProdGap n) 1
  let pp' := 1 - pp
  let x := pp * ((1 : ℝ≥0∞) / 2)
  let δ : ℝ := 1 / (64 * (n : ℝ))
  let δe : ℝ≥0∞ := ENNReal.ofReal δ
  let T := heavyFinalHorizon n γ
  let E := Q + 3 * heavyFinalResolutions n γ
  have hQ : 2 * Q ≤ γ * Nat.log 2 n :=
    heavyFinalEntryScale_le n γ
  have hQR : Q ≤ R := by
    dsimp only [R, heavyFinalScale]
    omega
  have hδ0 : 0 ≤ δ := by
    dsimp only [δ]
    positivity
  have hδ1 : δ ≤ 1 := by
    dsimp only [δ]
    rw [div_le_one (by positivity : (0 : ℝ) < 64 * n)]
    have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hnPos
    nlinarith
  have hgapProd :
      n + heavyMiddleProdGap n = 2 * (heavyMiddleLower n + 1) := by
    rcases heavyMiddle_geometry (hlog.trans' (by norm_num)) with
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hgap, _, _, _, _, _, _, _, _⟩
    simpa using hgap
  have hcoProd :
      (n - 1) + 1 = n := by omega
  have hwidth :
      heavyMiddleLower n + 1 ≤ n - 1 := by
    unfold heavyMiddleLower
    omega
  have hpp1 : pp ≤ 1 := by
    exact heavyBandProductivity_le_one n hn
      (heavyMiddleLower n) (n - 1)
      (heavyMiddleProdGap n) 1
      hgapProd hcoProd hwidth
  have hppsum : pp + pp' = 1 := by
    rw [add_comm]
    exact tsub_add_cancel_of_le hpp1
  have h2δ : 2 * δe ≤ pp := by
    simpa only [δe, δ, pp] using
      heavyFinalProductivity_ge n hn (hlog.trans' (by norm_num))
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
    dsimp only [T, heavyFinalHorizon, R]
    norm_num
  have hδT : δ * (T : ℝ) = 1024 * (R : ℝ) := by
    rw [hT]
    dsimp only [δ]
    field_simp
    ring
  have hENat : E ≤ 193 * R := by
    dsimp only [E, heavyFinalResolutions]
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
  change (pp' + x) ^ T / half ^ E ≤ _
  exact hdiv.trans (hquot.le.trans
    (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hexponent)))

/-- Raw-chain Heavy-B non-consensus mass from a final-band entry state is
bounded by the stopped-band lower-ruin, direction, and productivity terms.

The upper frozen boundary is `level = n`, hence all-`X` consensus, so it is
dynamically invisible by `heavyStateStep_consensus`. -/
theorem heavy_noncons_mass_bound
    (n : ℕ) (hn : 3 ≤ n)
    (aLo bHi k M K T cL p q : ℕ)
    (haLoLt : aLo < n)
    (hK : K = cL + 3 * M)
    (hpop : aLo + bHi + 2 = n)
    (haLo : 0 < aLo) (hbHi : 0 < bHi) (hmaj : bHi ≤ aLo)
    (hq : q ≠ 0)
    (hguard : ∀ s : HeavyTrace n,
      aLo + 1 ≤ BiCfg.heavyLevel s.cfg.1 →
      BiCfg.heavyLevel s.cfg.1 + 1 ≤ n →
      q * s.cfg.1.y ≤ p * s.cfg.1.x)
    (w η u : ℝ≥0∞)
    (hu : u = (p : ℝ≥0∞) / (q : ℝ≥0∞))
    (hrel : η * (u + w ^ 2) = w * (u + 1)) (hwη : w ≤ η)
    (hw1 : w ≤ 1) (hw0 : w ≠ 0) (hη1 : 1 ≤ η) (hηt : η ≠ ⊤)
    (pp : ℝ≥0∞) (hpp1 : pp ≤ 1)
    (hfloor : ∀ q : HeavyTrace n,
      aLo + 1 ≤ BiCfg.heavyLevel q.cfg.1 →
      BiCfg.heavyLevel q.cfg.1 + 1 ≤ n →
      pp ≤ dbPairPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b
            (heavy_two_entities hn q.cfg) .xy
          + dbPairPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b
            (heavy_two_entities hn q.cfg) .xb
          + dbPairPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b
            (heavy_two_entities hn q.cfg) .yb)
    (s₀ : HeavyState n)
    (hstart : BiCfg.heavyLevel s₀.1 = aLo + k)
    (hy0le : s₀.1.y ≤ cL) :
  ∑' z : BiCfg, (if BiXConsensus n z then 0 else iter heavyBChain T s₀.1 z)
      ≤ ((bHi : ℝ≥0∞) / (aLo : ℝ≥0∞)) ^ k
        + w ^ BiCfg.heavyLevel s₀.1 / (w ^ heavyFinalThreshold n * η ^ M)
        + ((1 - pp) + pp * ((1 : ℝ≥0∞) / 2)) ^ T /
            ((1 : ℝ≥0∞) / 2) ^ K := by
  classical
  let L : HeavyState n → Prop := fun s => BiCfg.heavyLevel s.1 ≤ aLo
  let U : HeavyState n → Prop := fun s => n ≤ BiCfg.heavyLevel s.1
  let q₀ : HeavyTrace n := ⟨s₀, 0, 0, 0⟩
  have hstateEq := heavyState_nonconsensus_mass_eq n hn T s₀
  rw [← hstateEq]
  have hBQ : ∀ s : HeavyState n, L s → ¬ HeavyXConsensus s := by
    intro s hs hcons
    have hlev := (heavyLevel_eq_n_iff s).2 hcons
    dsimp only [L] at hs
    omega
  have hdom := mass_le_freeze (heavyStateStep n) L HeavyXConsensus hBQ T s₀
  have hband_eq_lower :
      heavyStateBandStop n aLo n =
        freeze L (heavyStateStep n) := by
    rw [heavyStateBandStop_eq_freeze_upper_lower]
    apply freeze_eq_of_absorbing
    intro s hU
    have hlevelEq : BiCfg.heavyLevel s.1 = n := by
      have hle : BiCfg.heavyLevel s.1 ≤ n := by
        have hco := BiCfg.heavyLevel_add_coLevel s.2
        omega
      omega
    have hcons : HeavyXConsensus s := (heavyLevel_eq_n_iff s).1 hlevelEq
    have hnL : ¬ L s := by
      change ¬ BiCfg.heavyLevel s.1 ≤ aLo
      omega
    rw [freeze_of_not_mem s hnL]
    exact heavyStateStep_consensus n hn s hcons
  rw [← hband_eq_lower] at hdom
  have htraceEq :=
    heavyStateBand_failure_eq_trace hn aLo n T q₀ HeavyXConsensus
  have hstopped :
      (∑' z : HeavyState n,
        if HeavyXConsensus z then 0
        else iter (heavyStateBandStop n aLo n) T s₀ z)
        =
      ∑' r : HeavyTrace n,
        if HeavyXConsensus r.cfg then 0
        else iter (heavyBandStop n aLo n) T q₀ r := by
    simpa only [q₀] using htraceEq
  have htraceNoncons :
      (∑' r : HeavyTrace n,
        if HeavyXConsensus r.cfg then 0
        else iter (heavyBandStop n aLo n) T q₀ r)
        ≤
      ∑' r : HeavyTrace n,
        (if BiCfg.heavyLevel r.cfg.1 + 1 ≤ n then
          iter (heavyBandStop n aLo n) T q₀ r else 0) := by
    apply ENNReal.tsum_le_tsum
    intro r
    by_cases hr : HeavyXConsensus r.cfg
    · simp [hr]
    · have hlt : BiCfg.heavyLevel r.cfg.1 < n :=
        (heavy_noncons_iff_level_lt_n r.cfg).1 hr
      simp [hr, show BiCfg.heavyLevel r.cfg.1 + 1 ≤ n by omega]
  have hy₀ : q₀.YLedger s₀.1.y := by
    exact HeavyTrace.initial_yLedger s₀
  have hc0 : q₀.fuel + q₀.up + q₀.down = 0 := by
    simp [q₀]
  have hphase :
      (∑' r : HeavyTrace n,
        (if BiCfg.heavyLevel r.cfg.1 + 1 ≤ n then
          iter (heavyBandStop n aLo n) T q₀ r else 0))
        ≤ (∑' r : HeavyTrace n,
            (if BiCfg.heavyLevel r.cfg.1 ≤ aLo then
              iter (heavyBandStop n aLo n) T q₀ r else 0))
          + w ^ BiCfg.heavyLevel q₀.cfg.1 / (w ^ (n - 1) * η ^ M)
          + ((1 - pp) + pp * ((1 : ℝ≥0∞) / 2)) ^ T /
              ((1 : ℝ≥0∞) / 2) ^ K := by
    exact heavyBand_phase_fail n aLo n (n - 1) p q M K T cL
      s₀.1.y hn (by omega) hK hq hguard
      w η u hu hrel hwη hw1 hw0 hη1 hηt
      pp hpp1 hfloor q₀ hy₀ hy0le hc0
  have hruin :
      (∑' r : HeavyTrace n,
        (if BiCfg.heavyLevel r.cfg.1 ≤ aLo then
          iter (heavyBandStop n aLo n) T q₀ r else 0))
        ≤ ((bHi : ℝ≥0∞) / (aLo : ℝ≥0∞)) ^ k := by
    exact heavyBand_ruin_term_le hn aLo bHi n k T haLoLt hpop
      haLo hbHi hmaj q₀ (by simpa [q₀] using hstart)
  calc
    (∑' z : HeavyState n,
        if HeavyXConsensus z then 0
        else iter (heavyStateStep n) T s₀ z)
        ≤ (∑' z : HeavyState n,
          if HeavyXConsensus z then 0
          else iter (heavyStateBandStop n aLo n) T s₀ z) := hdom
    _ = ∑' r : HeavyTrace n,
        if HeavyXConsensus r.cfg then 0
        else iter (heavyBandStop n aLo n) T q₀ r := hstopped
    _ ≤ ∑' r : HeavyTrace n,
        (if BiCfg.heavyLevel r.cfg.1 + 1 ≤ n then
          iter (heavyBandStop n aLo n) T q₀ r else 0) := htraceNoncons
    _ ≤ (∑' r : HeavyTrace n,
            (if BiCfg.heavyLevel r.cfg.1 ≤ aLo then
              iter (heavyBandStop n aLo n) T q₀ r else 0))
          + w ^ BiCfg.heavyLevel q₀.cfg.1 / (w ^ (n - 1) * η ^ M)
          + ((1 - pp) + pp * ((1 : ℝ≥0∞) / 2)) ^ T /
              ((1 : ℝ≥0∞) / 2) ^ K := hphase
    _ ≤ ((bHi : ℝ≥0∞) / (aLo : ℝ≥0∞)) ^ k
          + w ^ BiCfg.heavyLevel s₀.1 / (w ^ (n - 1) * η ^ M)
          + ((1 - pp) + pp * ((1 : ℝ≥0∞) / 2)) ^ T /
              ((1 : ℝ≥0∞) / 2) ^ K := by
        simpa only [q₀] using add_le_add (add_le_add hruin le_rfl) le_rfl

/-- A single direct block reaches absorbing all-`X` consensus from the
logarithmic Heavy-B checkpoint. -/
theorem heavyFinalConsensus_reaches
    (n : ℕ) (hn : 3 ≤ n) (γ : ℕ)
    (hlog : 128 ≤ Nat.log 2 n) (hγ : 1 ≤ γ)
    (hsize : 6 * γ * Nat.log 2 n ≤ n) :
    Reaches (heavyStateStep n) (heavyFinalHorizon n γ)
      (HeavyLateCheckpoint n (1 + phase2StageCount n γ))
      HeavyXConsensus
      (3 * ENNReal.ofReal
        (Real.exp (-(heavyFinalScale n γ : ℝ) / 100))) := by
  intro s hs
  by_cases hcons : HeavyXConsensus s
  · have hiter :
        iter (heavyStateStep n) (heavyFinalHorizon n γ) s =
          PMF.pure s := by
      induction heavyFinalHorizon n γ with
      | zero => rfl
      | succ T ih =>
          rw [iter_succ, heavyStateStep_consensus n hn s hcons,
            PMF.pure_bind, ih]
    rw [hiter]
    have hzero :
        (∑' z : HeavyState n,
          if HeavyXConsensus z then 0 else PMF.pure s z) = 0 := by
      calc
        (∑' z : HeavyState n,
          if HeavyXConsensus z then 0 else PMF.pure s z) =
            ∑' _z : HeavyState n, (0 : ℝ≥0∞) := by
          apply tsum_congr
          intro z
          by_cases hz : z = s
          · subst z
            simp [hcons]
          · simp [PMF.pure_apply, hz]
        _ = 0 := tsum_zero
    rw [hzero]
    exact bot_le
  · let R := heavyFinalScale n γ
    let Q := heavyFinalEntryScale n γ
    let aLo := heavyMiddleLower n
    let bHi := heavyMiddleLowerBHi n
    let k := BiCfg.heavyLevel s.1 - aLo
    let M := heavyFinalResolutions n γ
    let K := Q + 3 * M
    let a := heavyDirA n
    let B := heavyDirB n
    let w : ℝ≥0∞ := ENNReal.ofReal (heavyBandW a B)
    let η : ℝ≥0∞ := ENNReal.ofReal (heavyBandEta a B)
    let u : ℝ≥0∞ := (a : ℝ≥0∞) / ((a + 4 * B : ℕ) : ℝ≥0∞)
    let pp := heavyBandProductivity n (heavyMiddleProdGap n) 1
    have hlog12 : 12 ≤ Nat.log 2 n := hlog.trans' (by norm_num)
    rcases heavyMiddle_geometry hlog12 with
      ⟨ha, hB, hparam, _hquarter, hfloorGuard, _hlohi, _hthrMid,
        _hwidthMid, _hstartEq, _hstartCo, _hKMid, hpop,
        haLo, hbHi, hmaj, hgapProd, _hcoProdMid, _hretPop,
        _hretLo, _hretB, _hretMaj, _hlowerTarget, _htargetHi,
        _hreturnGap⟩
    have hQ : 2 * Q ≤ γ * Nat.log 2 n := by
      simpa only [Q] using heavyFinalEntryScale_le n γ
    have hQR : Q ≤ R := by
      dsimp only [R, heavyFinalScale]
      omega
    have hlevel :
        n - Q ≤ BiCfg.heavyLevel s.1 := by
      unfold HeavyLateCheckpoint at hs
      have hidx :
          (1 + phase2StageCount n γ) + 1 =
            2 + phase2StageCount n γ := by omega
      rw [hidx] at hs
      change n ≤ BiCfg.heavyLevel s.1 + Q at hs
      omega
    have hprod : 128 ≤ γ * Nat.log 2 n := by
      calc
        128 = 1 * 128 := by norm_num
        _ ≤ γ * Nat.log 2 n := Nat.mul_le_mul hγ hlog
    have hRfive : 5 * R ≤ n := by
      calc
        5 * R = 5 * (γ * Nat.log 2 n + 1) := by rfl
        _ ≤ 6 * (γ * Nat.log 2 n) := by omega
        _ = 6 * γ * Nat.log 2 n := by ring
        _ ≤ n := hsize
    have haThree : 5 * aLo ≤ 3 * n := by
      dsimp only [aLo, heavyMiddleLower]
      have h2 := Nat.mul_div_le n 2
      have h48 := Nat.mul_div_le n 48
      omega
    have haLevel : aLo ≤ BiCfg.heavyLevel s.1 := by
      have h2R : 2 * R ≤ n - aLo := by omega
      calc
        aLo ≤ n - 2 * R := by omega
        _ ≤ n - Q := by omega
        _ ≤ BiCfg.heavyLevel s.1 := hlevel
    have hstart : BiCfg.heavyLevel s.1 = aLo + k := by
      dsimp only [k]
      exact (Nat.add_sub_of_le haLevel).symm
    have haLoLt : aLo < n := by
      have hco := BiCfg.heavyLevel_add_coLevel s.2
      omega
    have hcoState := BiCfg.heavyLevel_add_coLevel s.2
    have hyQ : s.1.y ≤ Q := by
      omega
    have hqDen : a + 4 * B ≠ 0 := by
      dsimp only [a, B]
      omega
    have hguard : ∀ r : HeavyTrace n,
        aLo + 1 ≤ BiCfg.heavyLevel r.cfg.1 →
        BiCfg.heavyLevel r.cfg.1 + 1 ≤ n →
        (a + 4 * B) * r.cfg.1.y ≤ a * r.cfg.1.x := by
      intro r hlive _
      exact heavyBand_window_guard_params
        (by simpa only [a, B] using hparam) hfloorGuard r hlive
    have hparams := heavyBand_params_enn
      (n := n) (a := a) (B := B)
      (by simpa only [a, B] using ha)
      (by simpa only [a, B] using hB)
      (by simpa only [a, B] using hparam)
    dsimp only at hparams
    rcases hparams with ⟨hrel, hwη, hw1, hw0, hη1, hηt, _hwt⟩
    have hcoProd :
        (n - 1) + 1 = n := by omega
    have hwidth :
        aLo + 1 ≤ n - 1 := by
      dsimp only [aLo, heavyMiddleLower]
      omega
    have hpp1 : pp ≤ 1 := by
      exact heavyBandProductivity_le_one n hn
        aLo (n - 1) (heavyMiddleProdGap n) 1
        (by simpa only [aLo] using hgapProd) hcoProd hwidth
    have hfloor : ∀ r : HeavyTrace n,
        aLo + 1 ≤ BiCfg.heavyLevel r.cfg.1 →
        BiCfg.heavyLevel r.cfg.1 + 1 ≤ n →
        pp ≤ dbPairPMF r.cfg.1.x r.cfg.1.y r.cfg.1.b
              (heavy_two_entities hn r.cfg) .xy
            + dbPairPMF r.cfg.1.x r.cfg.1.y r.cfg.1.b
              (heavy_two_entities hn r.cfg) .xb
            + dbPairPMF r.cfg.1.x r.cfg.1.y r.cfg.1.b
              (heavy_two_entities hn r.cfg) .yb := by
      intro r hlo hhi
      exact heavyBandProductivity_le n hn aLo n (n - 1)
        (heavyMiddleProdGap n) 1
        (by omega) (by simpa only [aLo] using hgapProd)
        hcoProd r.cfg hlo hhi
    have hraw :=
      heavy_noncons_mass_bound n hn
        aLo bHi k M K (heavyFinalHorizon n γ) Q
        a (a + 4 * B)
        haLoLt rfl
        (by simpa only [aLo, bHi] using hpop)
        (by simpa only [aLo] using haLo)
        (by simpa only [bHi] using hbHi)
        (by simpa only [aLo, bHi] using hmaj)
        hqDen hguard
        w η u rfl hrel hwη hw1 hw0 hη1 hηt
        pp hpp1 hfloor s hstart hyQ
    have hstateEq := heavyState_nonconsensus_mass_eq n hn
      (heavyFinalHorizon n γ) s
    rw [hstateEq]
    have hsafety := heavyFinalSafetyError_le n γ hlog hγ hsize s hs
    have hdirection := heavyFinalDirectionError_le n γ hlog s hs hcons
    have hclock := heavyFinalClockError_le n hn γ hlog
    let e :=
      ENNReal.ofReal
        (Real.exp (-(heavyFinalScale n γ : ℝ) / 100))
    have hclockEnvelope :
        ((1 - pp) + pp * ((1 : ℝ≥0∞) / 2)) ^
              heavyFinalHorizon n γ /
            ((1 : ℝ≥0∞) / 2) ^ K ≤ e := by
      have hR0 : (0 : ℝ) ≤ heavyFinalScale n γ := by positivity
      have hexp :
          -(heavyFinalScale n γ : ℝ) ≤
            -(heavyFinalScale n γ : ℝ) / 100 := by
        nlinarith
      have hclock' :
          ((1 - pp) + pp * ((1 : ℝ≥0∞) / 2)) ^
                heavyFinalHorizon n γ /
              ((1 : ℝ≥0∞) / 2) ^ K ≤
            ENNReal.ofReal (Real.exp (-(heavyFinalScale n γ : ℝ))) := by
        simpa only [pp, K, Q, M] using hclock
      exact hclock'.trans
        (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hexp))
    refine hraw.trans ?_
    change
      (((bHi : ℝ≥0∞) / (aLo : ℝ≥0∞)) ^ k +
          w ^ BiCfg.heavyLevel s.1 / (w ^ heavyFinalThreshold n * η ^ M) +
        ((1 - pp) + pp * ((1 : ℝ≥0∞) / 2)) ^
            heavyFinalHorizon n γ /
          ((1 : ℝ≥0∞) / 2) ^ K) ≤ 3 * e
    calc
      _ ≤ (e + e) + e := by
        dsimp only [aLo, bHi, k, M, K, a, B, w, η, u, pp, e]
          at hsafety hdirection hclockEnvelope ⊢
        gcongr
      _ = 3 * e := by ring

/-- The final exponential envelope fits a power law. -/
theorem heavyFinalExponential_le_power
    (n γ : ℕ) (hlog : 128 ≤ Nat.log 2 n) :
    ENNReal.ofReal
        (Real.exp (-(heavyFinalScale n γ : ℝ) / 100)) ≤
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
        Real.exp (-(heavyFinalScale n γ : ℝ) / 100) :=
    Real.exp_pos _
  have hpPow :
      (0 : ℝ) <
        (n : ℝ) ^ (-((1 / 200 : ℝ) * (γ : ℝ))) :=
    Real.rpow_pos_of_pos (by exact_mod_cast hnPos) _
  have hlogIneq :
      Real.log
          (Real.exp (-(heavyFinalScale n γ : ℝ) / 100)) ≤
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
          (heavyFinalScale n γ : ℕ) := by
      unfold heavyFinalScale
      norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_one]
      linarith
    nlinarith
  have hexp := Real.exp_le_exp.mpr hlogIneq
  rwa [Real.exp_log hpExp, Real.exp_log hpPow] at hexp

/-- Power-law form of the direct final consensus block. -/
theorem heavyFinalConsensus_reaches_power
    (n : ℕ) (hn : 3 ≤ n) (γ : ℕ)
    (hlog : 128 ≤ Nat.log 2 n) (hγ : 1 ≤ γ)
    (hsize : 6 * γ * Nat.log 2 n ≤ n) :
    Reaches (heavyStateStep n) (heavyFinalHorizon n γ)
      (HeavyLateCheckpoint n (1 + phase2StageCount n γ))
      HeavyXConsensus
      (3 * (n : ℝ≥0∞)⁻¹ ^
        ((1 / 200 : ℝ) * (γ : ℝ))) := by
  apply (heavyFinalConsensus_reaches n hn γ hlog hγ hsize).mono_error
  gcongr
  exact heavyFinalExponential_le_power n γ hlog

end Tri

#print axioms Tri.heavy_noncons_iff_level_lt_n
#print axioms Tri.heavyFinalProductivity_ge
#print axioms Tri.heavyFinalEntryScale_le
#print axioms Tri.heavyFinalSafetyError_le
#print axioms Tri.heavyFinalDirectionError_le
#print axioms Tri.heavyFinalClockError_le
#print axioms Tri.heavy_noncons_mass_bound
#print axioms Tri.heavyFinalConsensus_reaches
#print axioms Tri.heavyFinalExponential_le_power
#print axioms Tri.heavyFinalConsensus_reaches_power
