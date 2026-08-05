/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.SingleBWideClock
import Tri.SingleBLevelPhase
import Tri.SingleBClockRung
import Tri.DoubleBDirectionConstants

/-!
# One concrete gap-form Single-B rung

This instantiates the level-form Single-B phase with the wide two-branch
occupation clock and the honest direction constants, at the unit-`u`
parameter table

```
g = 128u,  D = D₂ = u,  climb = 2u,  M = n/8,  T = 256(n+2M),  H = T+1,
```

producing one rung `n + G ≤ 2x+b  →  n + G + u ≤ 2x+b` at the γ-free
horizon `Θ(n)` with error `8·exp(-u²/1024n)`.  The direction deadline runs
through the Double-B symmetric-boundary estimate at effective scale
`N = 2n+g`.
-/

namespace Tri

open scoped ENNReal

variable {n : ℕ}

/-! ## The wide starvation producer -/

/-- The starvation stream of the staged Single-B phase is covered by the
wide joint two-branch clock plus the creation-bad stream. -/
theorem singleBand_hclock_wide
    (hn : 2 ≤ n)
    (aLoΛ hiΛ targetΛ D H g cxCap M K T Hocc : ℕ)
    (htargetHi : targetΛ + 1 ≤ hiΛ)
    (hgap : n + D + g ≤ aLoΛ + 1)
    (hsmall : 4 * (hiΛ + cxCap) ≤ 7 * n)
    (hHT : 2 * Hocc ≤ T) (hK : n + 2 * M ≤ K)
    (hH : 0 < H)
    (s₀ : SingleState n) (hcxCap : s₀.1.y + M ≤ cxCap) :
    ∑' q, (if singleBandStarvation aLoΛ targetΛ H M q then
        iter (singleBandStop n hn aLoΛ hiΛ D H) T
          (⟨s₀, 0, 0, 0, 0⟩ : SingleLedger n) q else 0)
      ≤ (1 / (((32 : ℝ≥0∞) / 31) ^ Hocc * (1 / 2) ^ K) +
          singleBlankW (2 * n) g ^ s₀.1.doubleLevel /
            (singleBlankW (2 * n) g ^ hiΛ *
              singleBlankEta (2 * n) g ^ Hocc))
        + ENNReal.ofReal
            (Real.exp (-((D : ℝ) ^ 2 / (2 * (H : ℝ))))) := by
  have hpoint : ∀ q : SingleLedger n,
      (if singleBandStarvation aLoΛ targetΛ H M q then
          iter (singleBandStop n hn aLoΛ hiΛ D H) T
            (⟨s₀, 0, 0, 0, 0⟩ : SingleLedger n) q else 0) ≤
        (if (¬ SingleBandFrozen n aLoΛ hiΛ D H q) ∧
            q.rx + q.ry < M then
          iter (singleBandStop n hn aLoΛ hiΛ D H) T
            (⟨s₀, 0, 0, 0, 0⟩ : SingleLedger n) q else 0) +
        (if CreationBadY D H q then
          iter (singleBandStop n hn aLoΛ hiΛ D H) T
            (⟨s₀, 0, 0, 0, 0⟩ : SingleLedger n) q else 0) := by
    intro q
    by_cases hs : singleBandStarvation aLoΛ targetΛ H M q
    · by_cases hbad : CreationBadY D H q
      · rw [if_pos hs, if_pos hbad]
        exact le_add_self
      · have hlive : ¬ SingleBandFrozen n aLoΛ hiΛ D H q := by
          intro hB
          rcases hB with hLow | hHigh | hBad | hBoundary
          · unfold singleBandStarvation at hs
            omega
          · unfold singleBandStarvation at hs
            omega
          · exact hbad hBad
          · unfold singleBandStarvation at hs
            unfold singleCreationBoundary at hBoundary
            omega
        have hres : q.rx + q.ry < M := by
          unfold singleBandStarvation at hs
          omega
        rw [if_pos hs, if_neg hbad, if_pos (And.intro hlive hres), add_zero]
    · rw [if_neg hs]
      positivity
  calc
    ∑' q, (if singleBandStarvation aLoΛ targetΛ H M q then
        iter (singleBandStop n hn aLoΛ hiΛ D H) T
          (⟨s₀, 0, 0, 0, 0⟩ : SingleLedger n) q else 0)
        ≤ ∑' q,
            ((if (¬ SingleBandFrozen n aLoΛ hiΛ D H q) ∧
                q.rx + q.ry < M then
              iter (singleBandStop n hn aLoΛ hiΛ D H) T
                (⟨s₀, 0, 0, 0, 0⟩ : SingleLedger n) q else 0) +
            (if CreationBadY D H q then
              iter (singleBandStop n hn aLoΛ hiΛ D H) T
                (⟨s₀, 0, 0, 0, 0⟩ : SingleLedger n) q else 0)) :=
      ENNReal.tsum_le_tsum hpoint
    _ =
        (∑' q, (if (¬ SingleBandFrozen n aLoΛ hiΛ D H q) ∧
            q.rx + q.ry < M then
          iter (singleBandStop n hn aLoΛ hiΛ D H) T
            (⟨s₀, 0, 0, 0, 0⟩ : SingleLedger n) q else 0)) +
        (∑' q, (if CreationBadY D H q then
          iter (singleBandStop n hn aLoΛ hiΛ D H) T
            (⟨s₀, 0, 0, 0, 0⟩ : SingleLedger n) q else 0)) :=
      ENNReal.tsum_add
    _ ≤
        (1 / (((32 : ℝ≥0∞) / 31) ^ Hocc * (1 / 2) ^ K) +
          singleBlankW (2 * n) g ^ s₀.1.doubleLevel /
            (singleBlankW (2 * n) g ^ hiΛ *
              singleBlankEta (2 * n) g ^ Hocc))
        + ENNReal.ofReal
            (Real.exp (-((D : ℝ) ^ 2 / (2 * (H : ℝ))))) :=
      add_le_add
        (singleBand_joint_clock_tail_wide n hn aLoΛ hiΛ D H g cxCap
          hgap hsmall T Hocc M K hHT hK s₀ hcxCap)
        (singleCreationY_stopped_tail hn aLoΛ hiΛ D H T hH s₀)

/-! ## Direction bridging to the Double-B symmetric constants -/

/-- The honest Single-B drift ratio is the Double-B symmetric one at scale
`N = 2n+g`. -/
theorem singleRungDirU_eq (n g : ℕ) (hn : 0 < n) :
    singleRungDirU n g =
      ((2 * n + g - g : ℕ) : ℝ≥0∞) / ((2 * n + g + g : ℕ) : ℝ≥0∞) := by
  rw [show 2 * n + g - g = 2 * n from by omega,
    show 2 * n + g + g = 2 * (n + g) from by ring]
  unfold singleRungDirU
  rw [show ((2 * n : ℕ) : ℝ≥0∞) = 2 * (n : ℝ≥0∞) from by push_cast; ring,
    show ((2 * (n + g) : ℕ) : ℝ≥0∞) = 2 * ((n + g : ℕ) : ℝ≥0∞) from by
      push_cast; ring]
  rw [ENNReal.mul_div_mul_left _ _ (by norm_num) (by norm_num)]

/-- The honest Single-B geometric base is the symmetric midpoint base at
scale `N = 2n+g`. -/
theorem singleRungDirW_eq (n g : ℕ) (hn : 0 < n) :
    singleRungDirW n g = phase1RungBase (2 * n + g + g) (2 * n + g - g) := by
  unfold phase1RungBase singleRungDirW
  rw [show 2 * n + g + g + (2 * n + g - g) = 2 * (2 * n + g) from by omega,
    show 2 * (2 * n + g + g) = 2 * (2 * (n + g)) from by ring]
  rw [show ((2 * (2 * n + g) : ℕ) : ℝ≥0∞) =
      2 * ((2 * n + g : ℕ) : ℝ≥0∞) from by push_cast; ring,
    show ((2 * (2 * (n + g)) : ℕ) : ℝ≥0∞) =
      2 * ((2 * (n + g) : ℕ) : ℝ≥0∞) from by push_cast; ring]
  rw [ENNReal.mul_div_mul_left _ _ (by norm_num) (by norm_num)]

/-- Exponential decay of the honest Single-B direction multiplier over `M`
resolution events, at effective scale `N = 2n+g`. -/
theorem singleRungDirEta_inv_pow_le_exp
    (n g M : ℕ) (hn : 0 < n) :
    1 / singleRungDirEta n g ^ M ≤
      ENNReal.ofReal
        (Real.exp
          (-((M : ℝ) * (g : ℝ) ^ 2 /
            (2 * ((2 * n + g : ℕ) : ℝ) ^ 2)))) := by
  have hη :
      singleRungDirEta n g =
        doubleDirectionEta
          (((2 * n + g - g : ℕ) : ℝ≥0∞) / ((2 * n + g + g : ℕ) : ℝ≥0∞))
          (phase1RungBase (2 * n + g + g) (2 * n + g - g)) := by
    unfold singleRungDirEta
    rw [singleRungDirU_eq n g hn, singleRungDirW_eq n g hn]
  rw [hη]
  exact doubleDirectionEta_inv_pow_le_exp (2 * n + g) g M
    (by omega) (by omega)

/-! ## Concrete scalar stream bounds at unit `u` -/

/-- The concrete rung Gaussian envelope. -/
noncomputable def singleGapEnvelope (n u : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-((u : ℝ) ^ 2 / (1024 * (n : ℝ)))))

/-- Backslide bound: a start buffer of at least `u` under the base
`(2n+g)/(2n+2g)` at `g = 128u` clears the envelope. -/
theorem singleGap_backslide_le
    (n u Bw : ℕ) (hu : 0 < u) (hlar : 131072 * u ≤ n) (hBw : u ≤ Bw) :
    singleRungDirW n (128 * u) ^ Bw ≤ singleGapEnvelope n u := by
  unfold singleRungDirW singleGapEnvelope
  apply ratio_pow_le_ofReal_exp (2 * (n + 128 * u)) (2 * n + 128 * u) Bw
    _ (by omega) (by omega)
  have hnR : (0 : ℝ) < n := by
    have : 0 < n := by omega
    exact_mod_cast this
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  have hlarR : 131072 * (u : ℝ) ≤ n := by exact_mod_cast hlar
  have hBwR : (u : ℝ) ≤ Bw := by exact_mod_cast hBw
  have hsub :
      ((2 * (n + 128 * u) : ℕ) : ℝ) - ((2 * n + 128 * u : ℕ) : ℝ) =
        128 * (u : ℝ) := by
    push_cast
    ring
  rw [hsub]
  rw [div_le_div_iff₀ (mul_pos (by norm_num) hnR)
    (by exact_mod_cast (show 0 < 2 * (n + 128 * u) from by omega) :
      (0 : ℝ) < ((2 * (n + 128 * u) : ℕ) : ℝ))]
  push_cast
  nlinarith [sq_nonneg (u : ℝ), mul_pos huR hnR]

/-- Backslide bound for the wider `g = 256u` middle rung. -/
theorem singleGap_backslide_le_256
    (n u Bw : ℕ) (hu : 0 < u) (hlar : 131072 * u ≤ n) (hBw : u ≤ Bw) :
    singleRungDirW n (256 * u) ^ Bw ≤ singleGapEnvelope n u := by
  unfold singleRungDirW singleGapEnvelope
  apply ratio_pow_le_ofReal_exp (2 * (n + 256 * u)) (2 * n + 256 * u) Bw
    _ (by omega) (by omega)
  have hnR : (0 : ℝ) < n := by
    have : 0 < n := by omega
    exact_mod_cast this
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  have hlarR : 131072 * (u : ℝ) ≤ n := by exact_mod_cast hlar
  have hBwR : (u : ℝ) ≤ Bw := by exact_mod_cast hBw
  have hsub :
      ((2 * (n + 256 * u) : ℕ) : ℝ) - ((2 * n + 256 * u : ℕ) : ℝ) =
        256 * (u : ℝ) := by
    push_cast
    ring
  rw [hsub]
  push_cast
  rw [div_le_div_iff₀ (mul_pos (by norm_num) hnR)
    (by positivity : (0 : ℝ) < 2 * (n + 256 * u))]
  nlinarith [sq_nonneg (u : ℝ), mul_pos huR hnR]

/-- Direction deadline bound at climb `2u`, gap `128u`, budget `M = n/8`. -/
theorem singleGap_deadline_le
    (n u Lentry M : ℕ) (hu : 0 < u) (hlar : 131072 * u ≤ n)
    (hMlow : 16 * n ≤ 255 * M) :
    singleRungDirW n (128 * u) ^ Lentry /
        (singleRungDirW n (128 * u) ^ (Lentry + 2 * u) *
          singleRungDirEta n (128 * u) ^ M) ≤
      singleGapEnvelope n u := by
  have hn : 0 < n := by omega
  have hw0 : singleRungDirW n (128 * u) ≠ 0 := by
    unfold singleRungDirW
    exact ne_of_gt (ENNReal.div_pos
      (by
        simp only [ne_eq, Nat.cast_eq_zero]
        omega)
      (ENNReal.natCast_ne_top _))
  have hwt : singleRungDirW n (128 * u) ≠ ⊤ := by
    unfold singleRungDirW
    exact ENNReal.div_ne_top (ENNReal.natCast_ne_top _)
      (by
        simp only [ne_eq, Nat.cast_eq_zero]
        omega)
  have hsplit :
      singleRungDirW n (128 * u) ^ Lentry /
          (singleRungDirW n (128 * u) ^ (Lentry + 2 * u) *
            singleRungDirEta n (128 * u) ^ M) =
        (singleRungDirW n (128 * u) ^ Lentry /
            singleRungDirW n (128 * u) ^ (Lentry + 2 * u)) *
          (1 / singleRungDirEta n (128 * u) ^ M) := by
    simpa using
      (ENNReal.mul_div_mul_comm
        (a := singleRungDirW n (128 * u) ^ Lentry) (b := 1)
        (c := singleRungDirW n (128 * u) ^ (Lentry + 2 * u))
        (d := singleRungDirEta n (128 * u) ^ M)
        (Or.inl (pow_ne_zero _ hw0))
        (Or.inl (ENNReal.pow_ne_top hwt)))
  rw [hsplit]
  have hratio := base_pow_ratio_le_ofReal_exp (2 * n + 128 * u)
    (2 * (n + 128 * u)) Lentry (Lentry + 2 * u)
    (by omega) (by omega) (by omega)
  have hwform :
      singleRungDirW n (128 * u) =
        ((2 * n + 128 * u : ℕ) : ℝ≥0∞) /
          ((2 * (n + 128 * u) : ℕ) : ℝ≥0∞) := rfl
  rw [← hwform] at hratio
  have hEta := singleRungDirEta_inv_pow_le_exp n (128 * u) M hn
  calc
    (singleRungDirW n (128 * u) ^ Lentry /
        singleRungDirW n (128 * u) ^ (Lentry + 2 * u)) *
        (1 / singleRungDirEta n (128 * u) ^ M)
        ≤ ENNReal.ofReal
            (Real.exp
              ((((Lentry + 2 * u : ℕ) : ℝ) - (Lentry : ℝ)) *
                Real.log (((2 * (n + 128 * u) : ℕ) : ℝ) /
                  ((2 * n + 128 * u : ℕ) : ℝ)))) *
          ENNReal.ofReal
            (Real.exp
              (-((M : ℝ) * ((128 * u : ℕ) : ℝ) ^ 2 /
                (2 * ((2 * n + 128 * u : ℕ) : ℝ) ^ 2)))) :=
      mul_le_mul hratio hEta bot_le bot_le
    _ = ENNReal.ofReal
          (Real.exp
            ((((Lentry + 2 * u : ℕ) : ℝ) - (Lentry : ℝ)) *
                Real.log (((2 * (n + 128 * u) : ℕ) : ℝ) /
                  ((2 * n + 128 * u : ℕ) : ℝ)) -
              (M : ℝ) * ((128 * u : ℕ) : ℝ) ^ 2 /
                (2 * ((2 * n + 128 * u : ℕ) : ℝ) ^ 2))) := by
      rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
      congr 2
    _ ≤ singleGapEnvelope n u := by
      unfold singleGapEnvelope
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn
      have huR : (0 : ℝ) < u := by exact_mod_cast hu
      have hlarR : 131072 * (u : ℝ) ≤ n := by exact_mod_cast hlar
      -- the climb cast
      have hclimb :
          (((Lentry + 2 * u : ℕ) : ℝ) - (Lentry : ℝ)) = 2 * (u : ℝ) := by
        push_cast
        ring
      rw [hclimb]
      set N : ℝ := ((2 * n + 128 * u : ℕ) : ℝ) with hN
      have hNval : N = 2 * (n : ℝ) + 128 * (u : ℝ) := by
        rw [hN]
        push_cast
        ring
      have hNpos : 0 < N := by
        rw [hNval]
        positivity
      -- log bound
      have hlogle :
          Real.log (((2 * (n + 128 * u) : ℕ) : ℝ) / N) ≤
            64 * (u : ℝ) / n := by
        have hrpos :
            (0 : ℝ) < ((2 * (n + 128 * u) : ℕ) : ℝ) / N := by
          apply div_pos
          · have : 0 < 2 * (n + 128 * u) := by omega
            exact_mod_cast this
          · exact hNpos
        have hsub := Real.log_le_sub_one_of_pos hrpos
        have hfrac :
            ((2 * (n + 128 * u) : ℕ) : ℝ) / N - 1 =
              (128 * (u : ℝ)) / N := by
          rw [hN]
          push_cast
          field_simp
          ring
        rw [hfrac] at hsub
        have hND : (128 * (u : ℝ)) / N ≤ 64 * (u : ℝ) / n := by
          rw [div_le_div_iff₀ hNpos hnR, hNval]
          nlinarith
        linarith
      have hlog0 :
          0 ≤ Real.log (((2 * (n + 128 * u) : ℕ) : ℝ) / N) := by
        apply Real.log_nonneg
        rw [le_div_iff₀ hNpos, one_mul, hN]
        have : 2 * n + 128 * u ≤ 2 * (n + 128 * u) := by omega
        exact_mod_cast this
      have hA :
          2 * (u : ℝ) *
              Real.log (((2 * (n + 128 * u) : ℕ) : ℝ) / N) ≤
            128 * (u : ℝ) ^ 2 / n := by
        calc
          2 * (u : ℝ) *
              Real.log (((2 * (n + 128 * u) : ℕ) : ℝ) / N)
              ≤ 2 * (u : ℝ) * (64 * (u : ℝ) / n) := by
            apply mul_le_mul_of_nonneg_left hlogle (by positivity)
          _ = 128 * (u : ℝ) ^ 2 / n := by ring
      have hgcast : ((128 * u : ℕ) : ℝ) = 128 * (u : ℝ) := by
        push_cast
        ring
      have hNsharp : 1024 * N ≤ 2049 * (n : ℝ) := by
        rw [hNval]
        nlinarith
      have hNsq : 1048576 * N ^ 2 ≤ 4198401 * (n : ℝ) ^ 2 := by
        nlinarith [hNsharp, hNpos, hnR]
      have hMlowR : 16 * (n : ℝ) ≤ 255 * (M : ℝ) := by
        exact_mod_cast hMlow
      have hMn : 16 * (n : ℝ) ^ 2 ≤ 255 * (M : ℝ) * (n : ℝ) := by
        nlinarith [mul_le_mul_of_nonneg_right hMlowR hnR.le]
      have hB :
          128 * (u : ℝ) ^ 2 / n + (u : ℝ) ^ 2 / (1024 * n) ≤
            (M : ℝ) * ((128 * u : ℕ) : ℝ) ^ 2 / (2 * N ^ 2) := by
        rw [hgcast]
        have hsum :
            128 * (u : ℝ) ^ 2 / n + (u : ℝ) ^ 2 / (1024 * n) =
              131073 * (u : ℝ) ^ 2 / (1024 * n) := by
          field_simp
          ring
        rw [hsum]
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have hNsqU :=
          mul_le_mul_of_nonneg_right hNsq (sq_nonneg (u : ℝ))
        have hMnU :=
          mul_le_mul_of_nonneg_right hMn (sq_nonneg (u : ℝ))
        nlinarith [hNsqU, hMnU, sq_nonneg ((u : ℝ) * (n : ℝ)),
          mul_pos hnR hnR]
      linarith

/-- Direction deadline bound at climb `2u`, gap `256u`, and a structural
creation quota. -/
theorem singleGap_deadline_le_256
    (n u Lentry M : ℕ) (hu : 0 < u) (hlar : 131072 * u ≤ n)
    (hMlow : 32 * n ≤ 1000 * M) :
    singleRungDirW n (256 * u) ^ Lentry /
        (singleRungDirW n (256 * u) ^ (Lentry + 2 * u) *
          singleRungDirEta n (256 * u) ^ M) ≤
      singleGapEnvelope n u := by
  have hn : 0 < n := by omega
  have hw0 : singleRungDirW n (256 * u) ≠ 0 := by
    unfold singleRungDirW
    exact ne_of_gt (ENNReal.div_pos
      (by
        simp only [ne_eq, Nat.cast_eq_zero]
        omega)
      (ENNReal.natCast_ne_top _))
  have hwt : singleRungDirW n (256 * u) ≠ ⊤ := by
    unfold singleRungDirW
    exact ENNReal.div_ne_top (ENNReal.natCast_ne_top _)
      (by
        simp only [ne_eq, Nat.cast_eq_zero]
        omega)
  have hsplit :
      singleRungDirW n (256 * u) ^ Lentry /
          (singleRungDirW n (256 * u) ^ (Lentry + 2 * u) *
            singleRungDirEta n (256 * u) ^ M) =
        (singleRungDirW n (256 * u) ^ Lentry /
            singleRungDirW n (256 * u) ^ (Lentry + 2 * u)) *
          (1 / singleRungDirEta n (256 * u) ^ M) := by
    simpa using
      (ENNReal.mul_div_mul_comm
        (a := singleRungDirW n (256 * u) ^ Lentry) (b := 1)
        (c := singleRungDirW n (256 * u) ^ (Lentry + 2 * u))
        (d := singleRungDirEta n (256 * u) ^ M)
        (Or.inl (pow_ne_zero _ hw0))
        (Or.inl (ENNReal.pow_ne_top hwt)))
  rw [hsplit]
  have hratio := base_pow_ratio_le_ofReal_exp (2 * n + 256 * u)
    (2 * (n + 256 * u)) Lentry (Lentry + 2 * u)
    (by omega) (by omega) (by omega)
  have hwform :
      singleRungDirW n (256 * u) =
        ((2 * n + 256 * u : ℕ) : ℝ≥0∞) /
          ((2 * (n + 256 * u) : ℕ) : ℝ≥0∞) := rfl
  rw [← hwform] at hratio
  have hEta := singleRungDirEta_inv_pow_le_exp n (256 * u) M hn
  calc
    (singleRungDirW n (256 * u) ^ Lentry /
        singleRungDirW n (256 * u) ^ (Lentry + 2 * u)) *
        (1 / singleRungDirEta n (256 * u) ^ M)
        ≤ ENNReal.ofReal
            (Real.exp
              ((((Lentry + 2 * u : ℕ) : ℝ) - (Lentry : ℝ)) *
                Real.log (((2 * (n + 256 * u) : ℕ) : ℝ) /
                  ((2 * n + 256 * u : ℕ) : ℝ)))) *
          ENNReal.ofReal
            (Real.exp
              (-((M : ℝ) * ((256 * u : ℕ) : ℝ) ^ 2 /
                (2 * ((2 * n + 256 * u : ℕ) : ℝ) ^ 2)))) :=
      mul_le_mul hratio hEta bot_le bot_le
    _ = ENNReal.ofReal
          (Real.exp
            ((((Lentry + 2 * u : ℕ) : ℝ) - (Lentry : ℝ)) *
                Real.log (((2 * (n + 256 * u) : ℕ) : ℝ) /
                  ((2 * n + 256 * u : ℕ) : ℝ)) -
              (M : ℝ) * ((256 * u : ℕ) : ℝ) ^ 2 /
                (2 * ((2 * n + 256 * u : ℕ) : ℝ) ^ 2))) := by
      rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
      congr 2
    _ ≤ singleGapEnvelope n u := by
      unfold singleGapEnvelope
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn
      have huR : (0 : ℝ) < u := by exact_mod_cast hu
      have hlarR : 131072 * (u : ℝ) ≤ n := by exact_mod_cast hlar
      -- the climb cast
      have hclimb :
          (((Lentry + 2 * u : ℕ) : ℝ) - (Lentry : ℝ)) = 2 * (u : ℝ) := by
        push_cast
        ring
      rw [hclimb]
      set N : ℝ := ((2 * n + 256 * u : ℕ) : ℝ) with hN
      have hNval : N = 2 * (n : ℝ) + 256 * (u : ℝ) := by
        rw [hN]
        push_cast
        ring
      have hNpos : 0 < N := by
        rw [hNval]
        positivity
      -- log bound
      have hlogle :
          Real.log (((2 * (n + 256 * u) : ℕ) : ℝ) / N) ≤
            128 * (u : ℝ) / n := by
        have hrpos :
            (0 : ℝ) < ((2 * (n + 256 * u) : ℕ) : ℝ) / N := by
          apply div_pos
          · have : 0 < 2 * (n + 256 * u) := by omega
            exact_mod_cast this
          · exact hNpos
        have hsub := Real.log_le_sub_one_of_pos hrpos
        have hfrac :
            ((2 * (n + 256 * u) : ℕ) : ℝ) / N - 1 =
              (256 * (u : ℝ)) / N := by
          rw [hN]
          push_cast
          field_simp
          ring
        rw [hfrac] at hsub
        have hND : (256 * (u : ℝ)) / N ≤ 128 * (u : ℝ) / n := by
          rw [div_le_div_iff₀ hNpos hnR, hNval]
          nlinarith
        linarith
      have hlog0 :
          0 ≤ Real.log (((2 * (n + 256 * u) : ℕ) : ℝ) / N) := by
        apply Real.log_nonneg
        rw [le_div_iff₀ hNpos, one_mul, hN]
        have : 2 * n + 256 * u ≤ 2 * (n + 256 * u) := by omega
        exact_mod_cast this
      have hA :
          2 * (u : ℝ) *
              Real.log (((2 * (n + 256 * u) : ℕ) : ℝ) / N) ≤
            256 * (u : ℝ) ^ 2 / n := by
        calc
          2 * (u : ℝ) *
              Real.log (((2 * (n + 256 * u) : ℕ) : ℝ) / N)
              ≤ 2 * (u : ℝ) * (128 * (u : ℝ) / n) := by
            apply mul_le_mul_of_nonneg_left hlogle (by positivity)
          _ = 256 * (u : ℝ) ^ 2 / n := by ring
      have hgcast : ((256 * u : ℕ) : ℝ) = 256 * (u : ℝ) := by
        push_cast
        ring
      have hNsharp : 512 * N ≤ 1025 * (n : ℝ) := by
        rw [hNval]
        nlinarith
      have hNsq : 262144 * N ^ 2 ≤ 1050625 * (n : ℝ) ^ 2 := by
        nlinarith [hNsharp, hNpos, hnR]
      have hMlowR : 32 * (n : ℝ) ≤ 1000 * (M : ℝ) := by
        exact_mod_cast hMlow
      have hMn : 32 * (n : ℝ) ^ 2 ≤ 1000 * (M : ℝ) * (n : ℝ) := by
        nlinarith [mul_le_mul_of_nonneg_right hMlowR hnR.le]
      have hB :
          256 * (u : ℝ) ^ 2 / n + (u : ℝ) ^ 2 / (1024 * n) ≤
            (M : ℝ) * ((256 * u : ℕ) : ℝ) ^ 2 / (2 * N ^ 2) := by
        rw [hgcast]
        have hsum :
            256 * (u : ℝ) ^ 2 / n + (u : ℝ) ^ 2 / (1024 * n) =
              262145 * (u : ℝ) ^ 2 / (1024 * n) := by
          field_simp
          ring
        rw [hsum]
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have hNsqU :=
          mul_le_mul_of_nonneg_right hNsq (sq_nonneg (u : ℝ))
        have hMnU :=
          mul_le_mul_of_nonneg_right hMn (sq_nonneg (u : ℝ))
        nlinarith [hNsqU, hMnU, sq_nonneg ((u : ℝ) * (n : ℝ)),
          mul_pos hnR hnR]
      linarith

/-- The wide clock envelope pieces clear the rung envelope. -/
theorem singleGap_clockEnvelope_le
    (n u M : ℕ) (hu : 0 < u) (hlar : 131072 * u ≤ n) :
    singleWideClockEnvelope n (128 * u) M ≤
      2 * singleGapEnvelope n u := by
  unfold singleWideClockEnvelope singleGapEnvelope
  have hn : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  have hlarR : 131072 * (u : ℝ) ≤ n := by exact_mod_cast hlar
  have hnormal :
      ((3 : ℝ≥0∞) / 4) ^ singleClockBudget n M ≤
        ENNReal.ofReal (Real.exp (-((u : ℝ) ^ 2 / (1024 * (n : ℝ))))) := by
    apply ratio_pow_le_ofReal_exp 4 3 (singleClockBudget n M)
      _ (by norm_num) (by norm_num)
    have hbudget : n ≤ singleClockBudget n M := by
      unfold singleClockBudget
      omega
    have hbudgetR : (n : ℝ) ≤ singleClockBudget n M := by
      exact_mod_cast hbudget
    have huN : (u : ℝ) ≤ n := by nlinarith
    push_cast
    rw [div_le_div_iff₀ (mul_pos (by norm_num) hnR)
      (by norm_num : (0 : ℝ) < 4)]
    nlinarith [sq_nonneg (u : ℝ)]
  have hblank :
      ENNReal.ofReal
          (Real.exp (-(((128 * u : ℕ) : ℝ) ^ 2 / (4 * (n : ℝ))))) ≤
        ENNReal.ofReal (Real.exp (-((u : ℝ) ^ 2 / (1024 * (n : ℝ))))) := by
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    have hgcast : ((128 * u : ℕ) : ℝ) = 128 * (u : ℝ) := by
      push_cast
      ring
    rw [hgcast, neg_le_neg_iff]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg (u : ℝ)]
  calc
    ((3 : ℝ≥0∞) / 4) ^ singleClockBudget n M +
          ENNReal.ofReal
            (Real.exp (-(((128 * u : ℕ) : ℝ) ^ 2 / (4 * (n : ℝ)))))
        ≤ ENNReal.ofReal
              (Real.exp (-((u : ℝ) ^ 2 / (1024 * (n : ℝ))))) +
            ENNReal.ofReal
              (Real.exp (-((u : ℝ) ^ 2 / (1024 * (n : ℝ))))) :=
      add_le_add hnormal hblank
    _ = 2 * ENNReal.ofReal
          (Real.exp (-((u : ℝ) ^ 2 / (1024 * (n : ℝ))))) := by
      ring

/-- The wide clock envelope pieces clear the rung envelope for `g = 256u`. -/
theorem singleGap_clockEnvelope_le_256
    (n u M : ℕ) (hu : 0 < u) (hlar : 131072 * u ≤ n) :
    singleWideClockEnvelope n (256 * u) M ≤
      2 * singleGapEnvelope n u := by
  unfold singleWideClockEnvelope singleGapEnvelope
  have hn : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  have hlarR : 131072 * (u : ℝ) ≤ n := by exact_mod_cast hlar
  have hnormal :
      ((3 : ℝ≥0∞) / 4) ^ singleClockBudget n M ≤
        ENNReal.ofReal (Real.exp (-((u : ℝ) ^ 2 / (1024 * (n : ℝ))))) := by
    apply ratio_pow_le_ofReal_exp 4 3 (singleClockBudget n M)
      _ (by norm_num) (by norm_num)
    have hbudget : n ≤ singleClockBudget n M := by
      unfold singleClockBudget
      omega
    have hbudgetR : (n : ℝ) ≤ singleClockBudget n M := by
      exact_mod_cast hbudget
    have huN : (u : ℝ) ≤ n := by nlinarith
    push_cast
    rw [div_le_div_iff₀ (mul_pos (by norm_num) hnR)
      (by norm_num : (0 : ℝ) < 4)]
    nlinarith [sq_nonneg (u : ℝ)]
  have hblank :
      ENNReal.ofReal
          (Real.exp (-(((256 * u : ℕ) : ℝ) ^ 2 / (4 * (n : ℝ))))) ≤
        ENNReal.ofReal (Real.exp (-((u : ℝ) ^ 2 / (1024 * (n : ℝ))))) := by
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    have hgcast : ((256 * u : ℕ) : ℝ) = 256 * (u : ℝ) := by
      push_cast
      ring
    rw [hgcast, neg_le_neg_iff]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg (u : ℝ)]
  calc
    ((3 : ℝ≥0∞) / 4) ^ singleClockBudget n M +
          ENNReal.ofReal
            (Real.exp (-(((256 * u : ℕ) : ℝ) ^ 2 / (4 * (n : ℝ)))))
        ≤ ENNReal.ofReal
              (Real.exp (-((u : ℝ) ^ 2 / (1024 * (n : ℝ))))) +
            ENNReal.ofReal
              (Real.exp (-((u : ℝ) ^ 2 / (1024 * (n : ℝ))))) :=
      add_le_add hnormal hblank
    _ = 2 * ENNReal.ofReal
          (Real.exp (-((u : ℝ) ^ 2 / (1024 * (n : ℝ))))) := by
      ring

/-- The creation tails at deviation `u` and lazy budget `H = T+1` clear the
rung envelope. -/
theorem singleGap_creation_le
    (n u M H : ℕ) (hu : 0 < u) (hlar : 131072 * u ≤ n)
    (hH8 : 8 * M ≤ n) (hHdef : H = singleWideHorizon n M + 1) :
    ENNReal.ofReal (Real.exp (-((u : ℝ) ^ 2 / (2 * (H : ℝ))))) ≤
      singleGapEnvelope n u := by
  unfold singleGapEnvelope
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  rw [neg_le_neg_iff]
  have hn : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hHle : H ≤ 321 * n := by
    rw [hHdef, singleWideHorizon_linear]
    omega
  have hHpos : 0 < H := by
    rw [hHdef]
    omega
  have hHleR : (H : ℝ) ≤ 321 * n := by exact_mod_cast hHle
  have hHposR : (0 : ℝ) < H := by exact_mod_cast hHpos
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [sq_nonneg (u : ℝ)]

/-- The co-level return term at tilt `u/(11n)` and slack `126u` clears the
rung envelope. -/
theorem singleGap_return_le
    (n u sret Bret T M : ℕ) (hu : 0 < u) (hlar : 131072 * u ≤ n)
    (hsret : sret = 126 * u) (hBret : Bret ≤ n)
    (hT : T = singleWideHorizon n M) (hM8 : 8 * M ≤ n) :
    (1 + (ENNReal.ofReal ((u : ℝ) / (11 * (n : ℝ)))) ^ 2 *
          ((Bret : ℝ≥0∞) / ((n - 1 : ℕ) : ℝ≥0∞))) ^ T /
        (1 + ENNReal.ofReal ((u : ℝ) / (11 * (n : ℝ)))) ^ (sret + 1) ≤
      singleGapEnvelope n u := by
  have hn : 2 ≤ n := by omega
  have hnR : (0 : ℝ) < n := by
    have : 0 < n := by omega
    exact_mod_cast this
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  have hlarR : 131072 * (u : ℝ) ≤ n := by exact_mod_cast hlar
  set e : ℝ := (u : ℝ) / (11 * (n : ℝ)) with he
  have he0 : 0 ≤ e := by
    rw [he]
    positivity
  have he1 : e ≤ 1 := by
    rw [he, div_le_one (by positivity)]
    nlinarith
  refine le_trans (singleCoReturn_exp n T sret Bret hn e he0 he1) ?_
  unfold singleGapEnvelope
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  have hden1 : (1 : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by
    have : 1 ≤ n - 1 := by omega
    exact_mod_cast this
  have hden2 : (n : ℝ) ≤ 2 * ((n - 1 : ℕ) : ℝ) := by
    have h2 : n ≤ 2 * (n - 1) := by omega
    exact_mod_cast h2
  have hTle : (T : ℝ) ≤ 321 * n := by
    have hTle' : T ≤ 321 * n := by
      rw [hT, singleWideHorizon_linear]
      omega
    exact_mod_cast hTle'
  have hBretR : (Bret : ℝ) ≤ n := by exact_mod_cast hBret
  have hsretR : (126 : ℝ) * u ≤ ((sret : ℕ) : ℝ) := by
    rw [hsret]
    push_cast
    ring_nf
    exact le_refl _
  -- numerator: T·e²·Bret/(n-1) ≤ 642·u²/(121·n)
  have hnum :
      (T : ℝ) * (e ^ 2 * (Bret : ℝ) / ((n - 1 : ℕ) : ℝ)) ≤
        642 * (u : ℝ) ^ 2 / (121 * n) := by
    rw [he]
    have hBn : (Bret : ℝ) / ((n - 1 : ℕ) : ℝ) ≤ 2 := by
      rw [div_le_iff₀ (by linarith)]
      linarith
    have hstep :
        e ^ 2 * (Bret : ℝ) / ((n - 1 : ℕ) : ℝ) ≤
          ((u : ℝ) / (11 * n)) ^ 2 * 2 := by
      rw [he]
      calc
        ((u : ℝ) / (11 * n)) ^ 2 * (Bret : ℝ) / ((n - 1 : ℕ) : ℝ)
            = ((u : ℝ) / (11 * n)) ^ 2 *
                ((Bret : ℝ) / ((n - 1 : ℕ) : ℝ)) := by ring
        _ ≤ ((u : ℝ) / (11 * n)) ^ 2 * 2 := by
          apply mul_le_mul_of_nonneg_left hBn (by positivity)
    calc
      (T : ℝ) * (e ^ 2 * (Bret : ℝ) / ((n - 1 : ℕ) : ℝ))
          ≤ (321 * (n : ℝ)) * (((u : ℝ) / (11 * n)) ^ 2 * 2) := by
        apply mul_le_mul hTle (by rw [← he]; exact hstep) ?_ (by positivity)
        positivity
      _ = 642 * (u : ℝ) ^ 2 / (121 * n) := by
        field_simp
        ring
  -- denominator: (sret+1)·e/2 ≥ 63·u²/(11·n)
  have hden :
      63 * (u : ℝ) ^ 2 / (11 * n) ≤ ((sret + 1 : ℕ) : ℝ) * e / 2 := by
    rw [he]
    have hs1 : (126 : ℝ) * u ≤ ((sret + 1 : ℕ) : ℝ) := by
      push_cast
      push_cast at hsretR
      linarith
    calc
      63 * (u : ℝ) ^ 2 / (11 * n) =
          (126 * (u : ℝ)) * ((u : ℝ) / (11 * n)) / 2 := by
        field_simp
        ring
      _ ≤ ((sret + 1 : ℕ) : ℝ) * ((u : ℝ) / (11 * n)) / 2 := by
        apply div_le_div_of_nonneg_right _ (by norm_num)
        apply mul_le_mul_of_nonneg_right hs1 (by positivity)
  have hgap :
      642 * (u : ℝ) ^ 2 / (121 * n) + (u : ℝ) ^ 2 / (1024 * n) ≤
        63 * (u : ℝ) ^ 2 / (11 * n) := by
    rw [div_add_div _ _ (by positivity) (by positivity),
      div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg ((u : ℝ) * (n : ℝ)), mul_pos hnR hnR,
      sq_nonneg (u : ℝ)]
  linarith

/-! ## The assembled rung -/

set_option maxHeartbeats 1000000 in
-- The instantiated phase theorem leaves a large scalar absorption goal.
/-- **One structural Single-B gap rung.**  From physical level `n+G` to
`n+G+u`, at the γ-free horizon `256·(n+2M)`, with error
`8·exp(-u²/1024n)`.

The caller supplies the creation quota `M`.  The sharp `CX` mask is
`(n-G)/2+M`; the side condition
`2G+512u+4M≤n` is exactly the wide-clock smallness condition
`4(hiΛ+cxCap)≤7n` after expanding `hiΛ=n+G+128u`. -/
theorem singleGapRung_structural
    (n u G M : ℕ) (hn : 2 ≤ n)
    (hu : 0 < u) (hlar : 131072 * u ≤ n)
    (hG : 130 * u ≤ G)
    (hMdir : 16 * n ≤ 255 * M)
    (hM8 : 8 * M ≤ n)
    (hGsmall : 2 * G + 512 * u + 4 * M ≤ n) :
    Reaches (singleStateStep n hn) (singleWideHorizon n M)
      (fun s => n + G ≤ s.1.doubleLevel)
      (fun s => n + G + u ≤ s.1.doubleLevel)
      (8 * singleGapEnvelope n u) := by
  have hn0 : 0 < n := by omega
  have hg0 : 0 < 128 * u := by omega
  obtain ⟨hrel, hwη, hη1, hηt, hw1, hw0, hwt, hwv⟩ :=
    singleRungDir_params n (128 * u) hn0 hg0
  set T : ℕ := singleWideHorizon n M with hTdef
  set H : ℕ := T + 1 with hHdef
  set g : ℕ := 128 * u with hgdef
  set aLoΛ : ℕ := n + 129 * u - 1 with haLo
  set hiΛ : ℕ := n + G + 128 * u with hhiΛ
  set Bw : ℕ := G + 1 - 129 * u with hBwdef
  set Bret : ℕ := n + 1 - G - u with hBretdef
  set cxCap : ℕ := (n - G) / 2 + M with hcxCapdef
  set εr : ℝ≥0∞ := ENNReal.ofReal ((u : ℝ) / (11 * (n : ℝ))) with hεr
  set εclock : ℝ≥0∞ :=
    singleWideClockEnvelope n g M +
      ENNReal.ofReal (Real.exp (-((u : ℝ) ^ 2 / (2 * (H : ℝ))))) with hεc
  have hgap : n + u + g ≤ aLoΛ + 1 := by
    rw [haLo, hgdef]
    omega
  have hεr1 : εr ≤ 1 := by
    rw [hεr]
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm]
    apply ENNReal.ofReal_le_ofReal
    rw [div_le_one (by positivity)]
    have hu1 : (1 : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu
    have hlarR : 131072 * (u : ℝ) ≤ n := by exact_mod_cast hlar
    nlinarith
  have hsmallW : 4 * (hiΛ + cxCap) ≤ 7 * n := by
    rw [hhiΛ, hcxCapdef]
    have h2 : 2 * ((n - G) / 2) ≤ n - G := Nat.mul_div_le _ 2
    omega
  -- the clock producer
  have hclock : ∀ s : SingleState n, n + G ≤ s.1.doubleLevel →
      ∑' q, (if singleBandStarvation aLoΛ ((n + G + u) + u) H M q then
          iter (singleBandStop n hn aLoΛ hiΛ u H) T
            (⟨s, 0, 0, 0, 0⟩ : SingleLedger n) q else 0)
        ≤ εclock := by
    intro s hs
    have hycap : s.1.y + M ≤ cxCap := by
      have hinv := s.2
      simp only [BiCfg.DoubleInv] at hinv
      simp only [BiCfg.doubleLevel] at hs
      rw [hcxCapdef]
      have hy2 : 2 * s.1.y ≤ n - G := by omega
      have hydiv : s.1.y ≤ (n - G) / 2 := by
        rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
        simpa [mul_comm] using hy2
      omega
    have h1 := singleBand_hclock_wide hn aLoΛ hiΛ ((n + G + u) + u) u H g
      cxCap M (singleClockBudget n M) T (singleWideHalfHorizon n M)
      (by
        rw [hhiΛ]
        omega)
      hgap hsmallW
      (le_of_eq (two_singleWideHalfHorizon n M))
      (le_of_eq rfl)
      (by rw [hHdef]; omega)
      s hycap
    refine h1.trans ?_
    rw [hεc]
    apply add_le_add ?_ le_rfl
    have hblankmono :
        singleBlankW (2 * n) g ^ s.1.doubleLevel ≤
          singleBlankW (2 * n) g ^ (n + G) :=
      pow_le_pow_right_of_le_one'
        (singleBlankW_le_one (2 * n) g (by omega)) hs
    calc
      1 / (((32 : ℝ≥0∞) / 31) ^ singleWideHalfHorizon n M *
            (1 / 2) ^ singleClockBudget n M) +
          singleBlankW (2 * n) g ^ s.1.doubleLevel /
            (singleBlankW (2 * n) g ^ hiΛ *
              singleBlankEta (2 * n) g ^ singleWideHalfHorizon n M)
          ≤ 1 / (((32 : ℝ≥0∞) / 31) ^ singleWideHalfHorizon n M *
              (1 / 2) ^ singleClockBudget n M) +
            singleBlankW (2 * n) g ^ (n + G) /
              (singleBlankW (2 * n) g ^ hiΛ *
                singleBlankEta (2 * n) g ^ singleWideHalfHorizon n M) :=
        add_le_add le_rfl (ENNReal.div_le_div_right hblankmono _)
      _ ≤ singleWideClockEnvelope n g M := by
        apply singleWideClockError_le n g (n + G) hiΛ M hn0
        · rw [hgdef]
          omega
        · rw [hhiΛ]
          omega
        · rw [hhiΛ, hgdef]
  -- the phase theorem
  have hr := singleBand_reaches_level hn aLoΛ hiΛ u u H n (n + g) Bw M T
      (n + G) (n + G + u) (126 * u) Bret
      (by rw [hHdef]; omega)
      (by rw [hHdef]; omega)
      (by omega)
      (singleRungDirW n g) (singleRungDirV n g) (singleRungDirEta n g)
      (singleRungDirU n g) εclock εr hεr1
      rfl hrel hwη hwv hw1 hw0 hη1 hwt hηt
      (singleBand_hlive_ratio (n := n) (aLoΛ := aLoΛ) (hiΛ := hiΛ)
        (D := u) (H := H) (g := g) hgap)
      (by rw [haLo, hBwdef]; omega)
      (by rw [haLo]; omega)
      (by omega)
      (by rw [hBretdef]; omega)
      (by rw [hhiΛ]; omega)
      hclock
  refine hr.mono_error ?_
  -- scalar absorption of the six streams
  unfold singleLevelPhaseError
  rw [show (n + G + u) + u = (n + G) + 2 * u from by ring]
  have hBwu : u ≤ Bw := by
    rw [hBwdef]
    omega
  have hE1 := singleGap_backslide_le n u Bw hu hlar hBwu
  have hE2 := singleGap_deadline_le n u (n + G) M hu hlar hMdir
  have hE3 := singleGap_clockEnvelope_le n u M hu hlar
  have hE4 := singleGap_creation_le n u M H hu hlar hM8
    (by rw [hHdef, hTdef])
  have hE5 := singleGap_return_le n u (126 * u) Bret T M hu hlar rfl
    (by rw [hBretdef]; omega) hTdef hM8
  rw [hεc, hgdef, hεr]
  calc
    ((singleRungDirW n (128 * u) ^ Bw +
          singleRungDirW n (128 * u) ^ (n + G) /
            (singleRungDirW n (128 * u) ^ (n + G + 2 * u) *
              singleRungDirEta n (128 * u) ^ M)) +
        (singleWideClockEnvelope n (128 * u) M +
          ENNReal.ofReal (Real.exp (-((u : ℝ) ^ 2 / (2 * (H : ℝ)))))))
      + ENNReal.ofReal (Real.exp (-((u : ℝ) ^ 2 / (2 * (H : ℝ)))))
      + ENNReal.ofReal (Real.exp (-((u : ℝ) ^ 2 / (2 * (H : ℝ)))))
      + (1 + ENNReal.ofReal ((u : ℝ) / (11 * (n : ℝ))) ^ 2 *
            ((Bret : ℝ≥0∞) / ((n - 1 : ℕ) : ℝ≥0∞))) ^ T /
          (1 + ENNReal.ofReal ((u : ℝ) / (11 * (n : ℝ)))) ^ (126 * u + 1)
        ≤ ((singleGapEnvelope n u + singleGapEnvelope n u) +
            (2 * singleGapEnvelope n u + singleGapEnvelope n u))
          + singleGapEnvelope n u + singleGapEnvelope n u
          + singleGapEnvelope n u := by
      exact add_le_add (add_le_add (add_le_add
        (add_le_add (add_le_add hE1 hE2) (add_le_add hE3 hE4)) hE4) hE4) hE5
    _ = 8 * singleGapEnvelope n u := by ring

/-- **One wider structural Single-B gap rung.**  This is the middle-extension
variant with `g = 256u`.  The larger live gap lets the caller use a smaller
structural creation quota while keeping the same public one-unit climb and
the same `8·exp(-u²/1024n)` envelope. -/
theorem singleGapRung_structural256
    (n u G M : ℕ) (hn : 2 ≤ n)
    (hu : 0 < u) (hlar : 131072 * u ≤ n)
    (hG : 258 * u ≤ G)
    (hMdir : 32 * n ≤ 1000 * M)
    (hM8 : 8 * M ≤ n)
    (hGsmall : 2 * G + 1024 * u + 4 * M ≤ n) :
    Reaches (singleStateStep n hn) (singleWideHorizon n M)
      (fun s => n + G ≤ s.1.doubleLevel)
      (fun s => n + G + u ≤ s.1.doubleLevel)
      (8 * singleGapEnvelope n u) := by
  have hn0 : 0 < n := by omega
  have hg0 : 0 < 256 * u := by omega
  obtain ⟨hrel, hwη, hη1, hηt, hw1, hw0, hwt, hwv⟩ :=
    singleRungDir_params n (256 * u) hn0 hg0
  set T : ℕ := singleWideHorizon n M with hTdef
  set H : ℕ := T + 1 with hHdef
  set g : ℕ := 256 * u with hgdef
  set aLoΛ : ℕ := n + 257 * u - 1 with haLo
  set hiΛ : ℕ := n + G + 256 * u with hhiΛ
  set Bw : ℕ := G + 1 - 257 * u with hBwdef
  set Bret : ℕ := n + 1 - G - u with hBretdef
  set cxCap : ℕ := (n - G) / 2 + M with hcxCapdef
  set εr : ℝ≥0∞ := ENNReal.ofReal ((u : ℝ) / (11 * (n : ℝ))) with hεr
  set εclock : ℝ≥0∞ :=
    singleWideClockEnvelope n g M +
      ENNReal.ofReal (Real.exp (-((u : ℝ) ^ 2 / (2 * (H : ℝ))))) with hεc
  have hgap : n + u + g ≤ aLoΛ + 1 := by
    rw [haLo, hgdef]
    omega
  have hεr1 : εr ≤ 1 := by
    rw [hεr]
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm]
    apply ENNReal.ofReal_le_ofReal
    rw [div_le_one (by positivity)]
    have hu1 : (1 : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu
    have hlarR : 131072 * (u : ℝ) ≤ n := by exact_mod_cast hlar
    nlinarith
  have hsmallW : 4 * (hiΛ + cxCap) ≤ 7 * n := by
    rw [hhiΛ, hcxCapdef]
    have h2 : 2 * ((n - G) / 2) ≤ n - G := Nat.mul_div_le _ 2
    omega
  -- the clock producer
  have hclock : ∀ s : SingleState n, n + G ≤ s.1.doubleLevel →
      ∑' q, (if singleBandStarvation aLoΛ ((n + G + u) + u) H M q then
          iter (singleBandStop n hn aLoΛ hiΛ u H) T
            (⟨s, 0, 0, 0, 0⟩ : SingleLedger n) q else 0)
        ≤ εclock := by
    intro s hs
    have hycap : s.1.y + M ≤ cxCap := by
      have hinv := s.2
      simp only [BiCfg.DoubleInv] at hinv
      simp only [BiCfg.doubleLevel] at hs
      rw [hcxCapdef]
      have hy2 : 2 * s.1.y ≤ n - G := by omega
      have hydiv : s.1.y ≤ (n - G) / 2 := by
        rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
        simpa [mul_comm] using hy2
      omega
    have h1 := singleBand_hclock_wide hn aLoΛ hiΛ ((n + G + u) + u) u H g
      cxCap M (singleClockBudget n M) T (singleWideHalfHorizon n M)
      (by
        rw [hhiΛ]
        omega)
      hgap hsmallW
      (le_of_eq (two_singleWideHalfHorizon n M))
      (le_of_eq rfl)
      (by rw [hHdef]; omega)
      s hycap
    refine h1.trans ?_
    rw [hεc]
    apply add_le_add ?_ le_rfl
    have hblankmono :
        singleBlankW (2 * n) g ^ s.1.doubleLevel ≤
          singleBlankW (2 * n) g ^ (n + G) :=
      pow_le_pow_right_of_le_one'
        (singleBlankW_le_one (2 * n) g (by omega)) hs
    calc
      1 / (((32 : ℝ≥0∞) / 31) ^ singleWideHalfHorizon n M *
            (1 / 2) ^ singleClockBudget n M) +
          singleBlankW (2 * n) g ^ s.1.doubleLevel /
            (singleBlankW (2 * n) g ^ hiΛ *
              singleBlankEta (2 * n) g ^ singleWideHalfHorizon n M)
          ≤ 1 / (((32 : ℝ≥0∞) / 31) ^ singleWideHalfHorizon n M *
              (1 / 2) ^ singleClockBudget n M) +
            singleBlankW (2 * n) g ^ (n + G) /
              (singleBlankW (2 * n) g ^ hiΛ *
                singleBlankEta (2 * n) g ^ singleWideHalfHorizon n M) :=
        add_le_add le_rfl (ENNReal.div_le_div_right hblankmono _)
      _ ≤ singleWideClockEnvelope n g M := by
        apply singleWideClockError_le n g (n + G) hiΛ M hn0
        · rw [hgdef]
          omega
        · rw [hhiΛ]
          omega
        · rw [hhiΛ, hgdef]
  -- the phase theorem
  have hr := singleBand_reaches_level hn aLoΛ hiΛ u u H n (n + g) Bw M T
      (n + G) (n + G + u) (126 * u) Bret
      (by rw [hHdef]; omega)
      (by rw [hHdef]; omega)
      (by omega)
      (singleRungDirW n g) (singleRungDirV n g) (singleRungDirEta n g)
      (singleRungDirU n g) εclock εr hεr1
      rfl hrel hwη hwv hw1 hw0 hη1 hwt hηt
      (singleBand_hlive_ratio (n := n) (aLoΛ := aLoΛ) (hiΛ := hiΛ)
        (D := u) (H := H) (g := g) hgap)
      (by rw [haLo, hBwdef]; omega)
      (by rw [haLo]; omega)
      (by omega)
      (by rw [hBretdef]; omega)
      (by rw [hhiΛ]; omega)
      hclock
  refine hr.mono_error ?_
  -- scalar absorption of the six streams
  unfold singleLevelPhaseError
  rw [show (n + G + u) + u = (n + G) + 2 * u from by ring]
  have hBwu : u ≤ Bw := by
    rw [hBwdef]
    omega
  have hE1 := singleGap_backslide_le_256 n u Bw hu hlar hBwu
  have hE2 := singleGap_deadline_le_256 n u (n + G) M hu hlar hMdir
  have hE3 := singleGap_clockEnvelope_le_256 n u M hu hlar
  have hE4 := singleGap_creation_le n u M H hu hlar hM8
    (by rw [hHdef, hTdef])
  have hE5 := singleGap_return_le n u (126 * u) Bret T M hu hlar rfl
    (by rw [hBretdef]; omega) hTdef hM8
  rw [hεc, hgdef, hεr]
  calc
    ((singleRungDirW n (256 * u) ^ Bw +
          singleRungDirW n (256 * u) ^ (n + G) /
            (singleRungDirW n (256 * u) ^ (n + G + 2 * u) *
              singleRungDirEta n (256 * u) ^ M)) +
        (singleWideClockEnvelope n (256 * u) M +
          ENNReal.ofReal (Real.exp (-((u : ℝ) ^ 2 / (2 * (H : ℝ)))))))
      + ENNReal.ofReal (Real.exp (-((u : ℝ) ^ 2 / (2 * (H : ℝ)))))
      + ENNReal.ofReal (Real.exp (-((u : ℝ) ^ 2 / (2 * (H : ℝ)))))
      + (1 + ENNReal.ofReal ((u : ℝ) / (11 * (n : ℝ))) ^ 2 *
            ((Bret : ℝ≥0∞) / ((n - 1 : ℕ) : ℝ≥0∞))) ^ T /
          (1 + ENNReal.ofReal ((u : ℝ) / (11 * (n : ℝ)))) ^ (126 * u + 1)
        ≤ ((singleGapEnvelope n u + singleGapEnvelope n u) +
            (2 * singleGapEnvelope n u + singleGapEnvelope n u))
          + singleGapEnvelope n u + singleGapEnvelope n u
          + singleGapEnvelope n u := by
      exact add_le_add (add_le_add (add_le_add
        (add_le_add (add_le_add hE1 hE2) (add_le_add hE3 hE4)) hE4) hE4) hE5
    _ = 8 * singleGapEnvelope n u := by ring

/-- Backwards-compatible fixed-quota gap rung used by the early ladder. -/
theorem singleGapRung
    (n u G : ℕ) (hn : 2 ≤ n)
    (hu : 0 < u) (hlar : 131072 * u ≤ n)
    (hG : 130 * u ≤ G)
    (hGsmall : 4 * G + 1032 * u + 8 ≤ n) :
    Reaches (singleStateStep n hn) (singleWideHorizon n (n / 8))
      (fun s => n + G ≤ s.1.doubleLevel)
      (fun s => n + G + u ≤ s.1.doubleLevel)
      (8 * singleGapEnvelope n u) := by
  apply singleGapRung_structural n u G (n / 8) hn hu hlar hG
  · have hdiv := Nat.div_add_mod n 8
    have hmod := Nat.mod_lt n (by norm_num : 0 < 8)
    have hn8 : 8 ≤ n := by omega
    omega
  · exact Nat.mul_div_le n 8
  · have h8 : 8 * (n / 8) ≤ n := Nat.mul_div_le n 8
    omega

end Tri

#print axioms Tri.singleBand_hclock_wide
#print axioms Tri.singleRungDirEta_inv_pow_le_exp
#print axioms Tri.singleGap_backslide_le
#print axioms Tri.singleGap_backslide_le_256
#print axioms Tri.singleGap_deadline_le
#print axioms Tri.singleGap_deadline_le_256
#print axioms Tri.singleGap_clockEnvelope_le
#print axioms Tri.singleGap_clockEnvelope_le_256
#print axioms Tri.singleGap_creation_le
#print axioms Tri.singleGap_return_le
#print axioms Tri.singleGapRung_structural
#print axioms Tri.singleGapRung_structural256
#print axioms Tri.singleGapRung
