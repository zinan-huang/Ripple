/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.MultiProductiveLinear

/-!
# Strict productive-event pair progress

Safety uses the harmonic linear-gap base itself.  Forward progress uses a
distinct, less aggressive tilt and obtains a strict contraction on every
productive reaction relevant to a fixed pair.  Direct reactions have jumps
`±2`; they are handled as two-unit atoms rather than collapsed to Bernoulli
trials.
-/

namespace Tri

open scoped ENNReal

/-- One-unit adverse/favorable atoms contract at a tilt `w` whenever their
odds are bounded by `u` and the displayed scalar bracket is strict. -/
theorem one_jump_strict_pair_real
    {down up u w φ : ℝ}
    (hup : 0 ≤ up) (hw : 0 ≤ w)
    (hφw : φ * w ≤ 1)
    (hodds : down ≤ up * u)
    (hscalar : u + w ^ 2 ≤ φ * w * (u + 1)) :
    down * w + up * w ^ 3 ≤
      φ * (down + up) * w ^ 2 := by
  have hA : 0 ≤ 1 - φ * w := sub_nonneg.mpr hφw
  have hOdds : 0 ≤ up * u - down := sub_nonneg.mpr hodds
  have hB :
      0 ≤ φ * w * (u + 1) - (u + w ^ 2) :=
    sub_nonneg.mpr hscalar
  have hnonneg :
      0 ≤ w * ((1 - φ * w) * (up * u - down) +
        (φ * w * (u + 1) - (u + w ^ 2)) * up) :=
    mul_nonneg hw (add_nonneg (mul_nonneg hA hOdds) (mul_nonneg hB hup))
  nlinarith

/-- Two-unit atoms use the squared odds and squared tilt. -/
theorem two_jump_strict_pair_real
    {down up u w φ : ℝ}
    (hup : 0 ≤ up)
    (hφw : φ * w ^ 2 ≤ 1)
    (hodds : down ≤ up * u ^ 2)
    (hscalar : u ^ 2 + w ^ 4 ≤ φ * w ^ 2 * (u ^ 2 + 1)) :
    down + up * w ^ 4 ≤
      φ * (down + up) * w ^ 2 := by
  have hA : 0 ≤ 1 - φ * w ^ 2 := sub_nonneg.mpr hφw
  have hOdds : 0 ≤ up * u ^ 2 - down := sub_nonneg.mpr hodds
  have hB :
      0 ≤ φ * w ^ 2 * (u ^ 2 + 1) - (u ^ 2 + w ^ 4) :=
    sub_nonneg.mpr hscalar
  have hnonneg :
      0 ≤ (1 - φ * w ^ 2) * (up * u ^ 2 - down) +
        (φ * w ^ 2 * (u ^ 2 + 1) - (u ^ 2 + w ^ 4)) * up :=
    add_nonneg (mul_nonneg hA hOdds) (mul_nonneg hB hup)
  nlinarith

/-- `ℝ≥0∞` transfer of the one-unit strict pair inequality. -/
theorem one_jump_strict_pair
    {down up u w φ : ℝ≥0∞}
    (hdown : down ≤ 1) (hup : up ≤ 1)
    (hu : u ≤ 1) (hw : w ≤ 1) (hφ : φ ≤ 1)
    (hφw : φ * w ≤ 1)
    (hodds : down ≤ up * u)
    (hscalar : u + w ^ 2 ≤ φ * w * (u + 1)) :
    down * w + up * w ^ 3 ≤
      φ * (down + up) * w ^ 2 := by
  have fd := ne_top_of_le_ne_top ENNReal.one_ne_top hdown
  have fu' := ne_top_of_le_ne_top ENNReal.one_ne_top hup
  have fbase := ne_top_of_le_ne_top ENNReal.one_ne_top hu
  have fw := ne_top_of_le_ne_top ENNReal.one_ne_top hw
  have fφ := ne_top_of_le_ne_top ENNReal.one_ne_top hφ
  have fL :
      down * w + up * w ^ 3 ≠ ⊤ :=
    ENNReal.add_ne_top.mpr
      ⟨ENNReal.mul_ne_top fd fw,
        ENNReal.mul_ne_top fu' (ENNReal.pow_ne_top fw)⟩
  have fR :
      φ * (down + up) * w ^ 2 ≠ ⊤ :=
    ENNReal.mul_ne_top
      (ENNReal.mul_ne_top fφ (ENNReal.add_ne_top.mpr ⟨fd, fu'⟩))
      (ENNReal.pow_ne_top fw)
  rw [← ENNReal.toReal_le_toReal fL fR]
  rw [ENNReal.toReal_add
        (ENNReal.mul_ne_top fd fw)
        (ENNReal.mul_ne_top fu' (ENNReal.pow_ne_top fw)),
      ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_add fd fu',
      ENNReal.toReal_pow]
  simp only [ENNReal.toReal_pow]
  apply one_jump_strict_pair_real
      ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  · have h := (ENNReal.toReal_le_toReal
      (ENNReal.mul_ne_top fφ fw) ENNReal.one_ne_top).mpr hφw
    rwa [ENNReal.toReal_mul, ENNReal.toReal_one] at h
  · have h := (ENNReal.toReal_le_toReal fd
      (ENNReal.mul_ne_top fu' fbase)).mpr hodds
    rwa [ENNReal.toReal_mul] at h
  · have fL' : u + w ^ 2 ≠ ⊤ :=
      ENNReal.add_ne_top.mpr ⟨fbase, ENNReal.pow_ne_top fw⟩
    have fR' : φ * w * (u + 1) ≠ ⊤ :=
      ENNReal.mul_ne_top (ENNReal.mul_ne_top fφ fw)
        (ENNReal.add_ne_top.mpr ⟨fbase, ENNReal.one_ne_top⟩)
    have h := (ENNReal.toReal_le_toReal fL' fR').mpr hscalar
    rwa [ENNReal.toReal_add fbase (ENNReal.pow_ne_top fw),
      ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_add fbase ENNReal.one_ne_top,
      ENNReal.toReal_pow, ENNReal.toReal_one] at h

/-- `ℝ≥0∞` transfer of the two-unit strict pair inequality. -/
theorem two_jump_strict_pair
    {down up u w φ : ℝ≥0∞}
    (hdown : down ≤ 1) (hup : up ≤ 1)
    (hu : u ≤ 1) (hw : w ≤ 1) (hφ : φ ≤ 1)
    (hφw : φ * w ^ 2 ≤ 1)
    (hodds : down ≤ up * u ^ 2)
    (hscalar : u ^ 2 + w ^ 4 ≤ φ * w ^ 2 * (u ^ 2 + 1)) :
    down + up * w ^ 4 ≤
      φ * (down + up) * w ^ 2 := by
  have fd := ne_top_of_le_ne_top ENNReal.one_ne_top hdown
  have fu' := ne_top_of_le_ne_top ENNReal.one_ne_top hup
  have fbase := ne_top_of_le_ne_top ENNReal.one_ne_top hu
  have fw := ne_top_of_le_ne_top ENNReal.one_ne_top hw
  have fφ := ne_top_of_le_ne_top ENNReal.one_ne_top hφ
  have fL :
      down + up * w ^ 4 ≠ ⊤ :=
    ENNReal.add_ne_top.mpr
      ⟨fd, ENNReal.mul_ne_top fu' (ENNReal.pow_ne_top fw)⟩
  have fR :
      φ * (down + up) * w ^ 2 ≠ ⊤ :=
    ENNReal.mul_ne_top
      (ENNReal.mul_ne_top fφ (ENNReal.add_ne_top.mpr ⟨fd, fu'⟩))
      (ENNReal.pow_ne_top fw)
  rw [← ENNReal.toReal_le_toReal fL fR]
  rw [ENNReal.toReal_add fd
        (ENNReal.mul_ne_top fu' (ENNReal.pow_ne_top fw)),
      ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_mul, ENNReal.toReal_add fd fu',
      ENNReal.toReal_pow]
  simp only [ENNReal.toReal_pow]
  apply two_jump_strict_pair_real
      ENNReal.toReal_nonneg
  · have h := (ENNReal.toReal_le_toReal
      (ENNReal.mul_ne_top fφ (ENNReal.pow_ne_top fw))
      ENNReal.one_ne_top).mpr hφw
    rwa [ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_one] at h
  · have h := (ENNReal.toReal_le_toReal fd
      (ENNReal.mul_ne_top fu' (ENNReal.pow_ne_top fbase))).mpr hodds
    rwa [ENNReal.toReal_mul, ENNReal.toReal_pow] at h
  · have fL' : u ^ 2 + w ^ 4 ≠ ⊤ :=
      ENNReal.add_ne_top.mpr
        ⟨ENNReal.pow_ne_top fbase, ENNReal.pow_ne_top fw⟩
    have fR' : φ * w ^ 2 * (u ^ 2 + 1) ≠ ⊤ :=
      ENNReal.mul_ne_top
        (ENNReal.mul_ne_top fφ (ENNReal.pow_ne_top fw))
        (ENNReal.add_ne_top.mpr
          ⟨ENNReal.pow_ne_top fbase, ENNReal.one_ne_top⟩)
    have h := (ENNReal.toReal_le_toReal fL' fR').mpr hscalar
    rw [ENNReal.toReal_add (ENNReal.pow_ne_top fbase)
        (ENNReal.pow_ne_top fw),
      ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_add (ENNReal.pow_ne_top fbase) ENNReal.one_ne_top,
      ENNReal.toReal_one] at h
    simpa only [ENNReal.toReal_pow] using h

/-- Lift a strict four-atom MGF inequality to any natural gap at least two. -/
theorem four_jump_geometric_of_core
    {down2 down1 up1 up2 w φ : ℝ≥0∞} {g : ℕ}
    (hg : 2 ≤ g)
    (hcore :
      down2 + down1 * w + up1 * w ^ 3 + up2 * w ^ 4 ≤
        φ * (down2 + down1 + up1 + up2) * w ^ 2) :
    down2 * w ^ (g - 2) +
        down1 * w ^ (g - 1) +
        up1 * w ^ (g + 1) +
        up2 * w ^ (g + 2) ≤
      φ * (down2 + down1 + up1 + up2) * w ^ g := by
  have hgm1 : g - 1 = (g - 2) + 1 := by omega
  have hgp1 : g + 1 = (g - 2) + 3 := by omega
  have hgp2 : g + 2 = (g - 2) + 4 := by omega
  have hpowg : w ^ g = w ^ (g - 2) * w ^ 2 := by
    calc
      w ^ g = w ^ ((g - 2) + 2) :=
        congrArg (fun k : ℕ => w ^ k) (by omega)
      _ = w ^ (g - 2) * w ^ 2 := pow_add _ _ _
  calc
    down2 * w ^ (g - 2) +
          down1 * w ^ (g - 1) +
          up1 * w ^ (g + 1) +
          up2 * w ^ (g + 2) =
        w ^ (g - 2) *
          (down2 + down1 * w + up1 * w ^ 3 + up2 * w ^ 4) := by
      rw [hgm1, hgp1, hgp2, pow_add, pow_add, pow_add]
      simp only [pow_one]
      ring
    _ ≤ w ^ (g - 2) *
        (φ * (down2 + down1 + up1 + up2) * w ^ 2) :=
      mul_le_mul_right hcore _
    _ = φ * (down2 + down1 + up1 + up2) * w ^ g := by
      rw [hpowg]
      ring

end Tri

namespace Tri.Multi

open scoped ENNReal

/-- Tilt halfway between the harmonic linear base and one. -/
noncomputable def pairProgressTilt (n d : ℕ) : ℝ≥0∞ :=
  (4 * n + d : ℕ) / (4 * n + 2 * d : ℕ)

/-- Conservative strict contraction factor for a relevant pair reaction. -/
noncomputable def pairProgressFactor (n d : ℕ) : ℝ≥0∞ :=
  (64 * n ^ 2 : ℕ) / (64 * n ^ 2 + d ^ 2 : ℕ)

theorem pairProgressTilt_le_one
    (n d : ℕ) (hn : 0 < n) :
    pairProgressTilt n d ≤ 1 := by
  unfold pairProgressTilt
  have hden0 : (((4 * n + 2 * d : ℕ) : ℝ≥0∞)) ≠ 0 := by
    exact_mod_cast (by omega : 4 * n + 2 * d ≠ 0)
  have hdenTop : (((4 * n + 2 * d : ℕ) : ℝ≥0∞)) ≠ ⊤ :=
    ENNReal.natCast_ne_top _
  calc
    ((4 * n + d : ℕ) : ℝ≥0∞) /
          ((4 * n + 2 * d : ℕ) : ℝ≥0∞) ≤
        ((4 * n + 2 * d : ℕ) : ℝ≥0∞) /
          ((4 * n + 2 * d : ℕ) : ℝ≥0∞) := by
      exact ENNReal.div_le_div_right (by exact_mod_cast (by omega)) _
    _ = 1 := ENNReal.div_self hden0 hdenTop

theorem pairProgressTilt_ne_zero
    (n d : ℕ) (hn : 0 < n) :
    pairProgressTilt n d ≠ 0 := by
  unfold pairProgressTilt
  simp only [ne_eq, ENNReal.div_eq_zero_iff, not_or]
  exact ⟨by exact_mod_cast (by omega : 4 * n + d ≠ 0),
    ENNReal.natCast_ne_top _⟩

theorem pairProgressFactor_le_one
    (n d : ℕ) (hn : 0 < n) :
    pairProgressFactor n d ≤ 1 := by
  unfold pairProgressFactor
  have hden0 : (((64 * n ^ 2 + d ^ 2 : ℕ) : ℝ≥0∞)) ≠ 0 := by
    exact_mod_cast (by positivity : 64 * n ^ 2 + d ^ 2 ≠ 0)
  have hdenTop : (((64 * n ^ 2 + d ^ 2 : ℕ) : ℝ≥0∞)) ≠ ⊤ :=
    ENNReal.natCast_ne_top _
  calc
    ((64 * n ^ 2 : ℕ) : ℝ≥0∞) /
          ((64 * n ^ 2 + d ^ 2 : ℕ) : ℝ≥0∞) ≤
        ((64 * n ^ 2 + d ^ 2 : ℕ) : ℝ≥0∞) /
          ((64 * n ^ 2 + d ^ 2 : ℕ) : ℝ≥0∞) := by
      exact ENNReal.div_le_div_right
        (by exact_mod_cast (Nat.le_add_right (64 * n ^ 2) (d ^ 2))) _
    _ = 1 := ENNReal.div_self hden0 hdenTop

theorem pairProgressFactor_ne_zero
    (n d : ℕ) (hn : 0 < n) :
    pairProgressFactor n d ≠ 0 := by
  unfold pairProgressFactor
  simp only [ne_eq, ENNReal.div_eq_zero_iff, not_or]
  exact ⟨by
    exact_mod_cast (by positivity : 64 * n ^ 2 ≠ 0),
    ENNReal.natCast_ne_top _⟩

private theorem pairProgress_scalar_one_real
    (N d : ℝ) (hN : 0 < N) (hd0 : 0 ≤ d) (hdN : d ≤ N) :
    N * 2 / (N * 2 + d) +
        ((N * 4 + d) / (N * 4 + d * 2)) ^ 2 ≤
      (N ^ 2 * 64 / (N ^ 2 * 64 + d ^ 2)) *
        ((N * 4 + d) / (N * 4 + d * 2)) *
        (N * 2 / (N * 2 + d) + 1) := by
  have h2 : 0 < N * 2 + d := by positivity
  have h4 : 0 < N * 4 + d * 2 := by positivity
  have h64 : 0 < N ^ 2 * 64 + d ^ 2 := by positivity
  have hNd : N * d ≤ N ^ 2 := by
    nlinarith [mul_nonneg (le_of_lt hN) (sub_nonneg.mpr hdN), sq_nonneg N]
  have hdd : d ^ 2 ≤ N ^ 2 := by nlinarith [sq_nonneg (N - d)]
  have hbracket : 0 ≤ 32 * N ^ 2 - 16 * N * d - d ^ 2 := by
    nlinarith
  have hid :
      (N ^ 2 * 64 / (N ^ 2 * 64 + d ^ 2)) *
            ((N * 4 + d) / (N * 4 + d * 2)) *
            (N * 2 / (N * 2 + d) + 1) -
          (N * 2 / (N * 2 + d) +
            ((N * 4 + d) / (N * 4 + d * 2)) ^ 2) =
        d ^ 2 * (32 * N ^ 2 - 16 * N * d - d ^ 2) /
          (4 * (2 * N + d) ^ 2 * (64 * N ^ 2 + d ^ 2)) := by
    field_simp
    ring
  apply sub_nonneg.mp
  rw [hid]
  positivity

private theorem pairProgress_scalar_two_real
    (N d : ℝ) (hN : 0 < N) (hd0 : 0 ≤ d) (hdN : d ≤ N) :
    (N * 2 / (N * 2 + d)) ^ 2 +
        ((N * 4 + d) / (N * 4 + d * 2)) ^ 4 ≤
      (N ^ 2 * 64 / (N ^ 2 * 64 + d ^ 2)) *
        ((N * 4 + d) / (N * 4 + d * 2)) ^ 2 *
        ((N * 2 / (N * 2 + d)) ^ 2 + 1) := by
  have h2 : 0 < N * 2 + d := by positivity
  have h4 : 0 < N * 4 + d * 2 := by positivity
  have h64 : 0 < N ^ 2 * 64 + d ^ 2 := by positivity
  have hd3 : d ^ 3 ≤ N ^ 3 := by
    gcongr
  have hd4 : d ^ 4 ≤ N ^ 4 := by
    gcongr
  have hNd3 : N * d ^ 3 ≤ N ^ 4 := by
    calc
      N * d ^ 3 ≤ N * N ^ 3 :=
        mul_le_mul_of_nonneg_left hd3 (le_of_lt hN)
      _ = N ^ 4 := by ring
  have hbracket :
      0 ≤ 3584 * N ^ 4 + 1536 * N ^ 3 * d +
        32 * N ^ 2 * d ^ 2 - 16 * N * d ^ 3 - d ^ 4 := by
    nlinarith [mul_nonneg (sq_nonneg N) (sq_nonneg d),
      mul_nonneg (mul_nonneg (sq_nonneg N) (le_of_lt hN)) hd0]
  have hid :
      (N ^ 2 * 64 / (N ^ 2 * 64 + d ^ 2)) *
            ((N * 4 + d) / (N * 4 + d * 2)) ^ 2 *
            ((N * 2 / (N * 2 + d)) ^ 2 + 1) -
          ((N * 2 / (N * 2 + d)) ^ 2 +
            ((N * 4 + d) / (N * 4 + d * 2)) ^ 4) =
        d ^ 2 *
            (3584 * N ^ 4 + 1536 * N ^ 3 * d +
              32 * N ^ 2 * d ^ 2 - 16 * N * d ^ 3 - d ^ 4) /
          (16 * (2 * N + d) ^ 4 * (64 * N ^ 2 + d ^ 2)) := by
    field_simp
    ring
  apply sub_nonneg.mp
  rw [hid]
  positivity

/-- Scalar compatibility for the one-unit atoms. -/
theorem pairProgress_scalar_one
    (n d : ℕ) (hn : 0 < n) (hdn : d ≤ n) :
    pairGapLinearBase n d + pairProgressTilt n d ^ 2 ≤
      pairProgressFactor n d * pairProgressTilt n d *
        (pairGapLinearBase n d + 1) := by
  have hu := pairGapLinearBase_le_one n d hn
  have hw := pairProgressTilt_le_one n d hn
  have hφ := pairProgressFactor_le_one n d hn
  have fu := ne_top_of_le_ne_top ENNReal.one_ne_top hu
  have fw := ne_top_of_le_ne_top ENNReal.one_ne_top hw
  have fφ := ne_top_of_le_ne_top ENNReal.one_ne_top hφ
  have fL : pairGapLinearBase n d + pairProgressTilt n d ^ 2 ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨fu, ENNReal.pow_ne_top fw⟩
  have fR :
      pairProgressFactor n d * pairProgressTilt n d *
          (pairGapLinearBase n d + 1) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top fφ fw)
      (ENNReal.add_ne_top.mpr ⟨fu, ENNReal.one_ne_top⟩)
  have huR :
      (pairGapLinearBase n d).toReal =
        (2 * (n : ℝ)) / (2 * (n : ℝ) + (d : ℝ)) := by
    unfold pairGapLinearBase
    rw [ENNReal.toReal_div]
    norm_num only [ENNReal.toReal_natCast]
    push_cast
    ring
  have hwR :
      (pairProgressTilt n d).toReal =
        (4 * (n : ℝ) + (d : ℝ)) /
          (4 * (n : ℝ) + 2 * (d : ℝ)) := by
    unfold pairProgressTilt
    rw [ENNReal.toReal_div]
    norm_num only [ENNReal.toReal_natCast]
    push_cast
    ring
  have hφR :
      (pairProgressFactor n d).toReal =
        (64 * (n : ℝ) ^ 2) /
          (64 * (n : ℝ) ^ 2 + (d : ℝ) ^ 2) := by
    unfold pairProgressFactor
    rw [ENNReal.toReal_div]
    norm_num only [ENNReal.toReal_natCast]
    push_cast
    ring
  rw [← ENNReal.toReal_le_toReal fL fR]
  rw [ENNReal.toReal_add fu (ENNReal.pow_ne_top fw),
    ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_add fu ENNReal.one_ne_top,
    ENNReal.toReal_one]
  simp_rw [ENNReal.toReal_pow]
  rw [huR, hwR, hφR]
  simpa [mul_comm] using
    pairProgress_scalar_one_real
      (n : ℝ) (d : ℝ)
      (by exact_mod_cast hn) (by positivity) (by exact_mod_cast hdn)

/-- Scalar compatibility for the two-unit atoms. -/
theorem pairProgress_scalar_two
    (n d : ℕ) (hn : 0 < n) (hdn : d ≤ n) :
    pairGapLinearBase n d ^ 2 + pairProgressTilt n d ^ 4 ≤
      pairProgressFactor n d * pairProgressTilt n d ^ 2 *
        (pairGapLinearBase n d ^ 2 + 1) := by
  have hu := pairGapLinearBase_le_one n d hn
  have hw := pairProgressTilt_le_one n d hn
  have hφ := pairProgressFactor_le_one n d hn
  have fu := ne_top_of_le_ne_top ENNReal.one_ne_top hu
  have fw := ne_top_of_le_ne_top ENNReal.one_ne_top hw
  have fφ := ne_top_of_le_ne_top ENNReal.one_ne_top hφ
  have fL :
      pairGapLinearBase n d ^ 2 + pairProgressTilt n d ^ 4 ≠ ⊤ :=
    ENNReal.add_ne_top.mpr
      ⟨ENNReal.pow_ne_top fu, ENNReal.pow_ne_top fw⟩
  have fR :
      pairProgressFactor n d * pairProgressTilt n d ^ 2 *
          (pairGapLinearBase n d ^ 2 + 1) ≠ ⊤ :=
    ENNReal.mul_ne_top
      (ENNReal.mul_ne_top fφ (ENNReal.pow_ne_top fw))
      (ENNReal.add_ne_top.mpr
        ⟨ENNReal.pow_ne_top fu, ENNReal.one_ne_top⟩)
  have huR :
      (pairGapLinearBase n d).toReal =
        (2 * (n : ℝ)) / (2 * (n : ℝ) + (d : ℝ)) := by
    unfold pairGapLinearBase
    rw [ENNReal.toReal_div]
    norm_num only [ENNReal.toReal_natCast]
    push_cast
    ring
  have hwR :
      (pairProgressTilt n d).toReal =
        (4 * (n : ℝ) + (d : ℝ)) /
          (4 * (n : ℝ) + 2 * (d : ℝ)) := by
    unfold pairProgressTilt
    rw [ENNReal.toReal_div]
    norm_num only [ENNReal.toReal_natCast]
    push_cast
    ring
  have hφR :
      (pairProgressFactor n d).toReal =
        (64 * (n : ℝ) ^ 2) /
          (64 * (n : ℝ) ^ 2 + (d : ℝ) ^ 2) := by
    unfold pairProgressFactor
    rw [ENNReal.toReal_div]
    norm_num only [ENNReal.toReal_natCast]
    push_cast
    ring
  rw [← ENNReal.toReal_le_toReal fL fR]
  rw [ENNReal.toReal_add (ENNReal.pow_ne_top fu)
      (ENNReal.pow_ne_top fw),
    ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_add (ENNReal.pow_ne_top fu) ENNReal.one_ne_top,
    ENNReal.toReal_one]
  simp_rw [ENNReal.toReal_pow]
  rw [huR, hwR, hφR]
  simpa [mul_comm] using
    pairProgress_scalar_two_real
      (n : ℝ) (d : ℝ)
      (by exact_mod_cast hn) (by positivity) (by exact_mod_cast hdn)

/-- Every fixed increment fiber has mass at most one. -/
theorem pairDeltaMass_le_one
    (c : Config m n) (h3 : 3 ≤ n)
    (X Y : Species m) (k : ℤ) :
    pairDeltaMass c h3 X Y k ≤ 1 := by
  unfold pairDeltaMass
  calc
    (∑' t : TripleSample c,
        if samplePairDelta t X Y = k then triplePMF c h3 t else 0) ≤
      ∑' t : TripleSample c, triplePMF c h3 t := by
        apply ENNReal.tsum_le_tsum
        intro t
        split_ifs <;> simp
    _ = 1 := PMF.tsum_coe _

/-- The four nonzero pair-gap atoms contract strictly at the progress tilt.
The zero atom is deliberately absent: it consists of reactions irrelevant to
the fixed pair and will leave the relevant-event counter unchanged. -/
theorem pairDeltaMass_relevant_strict_mgf
    (c : Config m n) (h3 : 3 ≤ n)
    (X Y : Species m) (hXY : X ≠ Y)
    (d : ℕ) (hdn : d ≤ n)
    (hgap : HasPairwiseGap c X d) :
    pairDeltaMass c h3 X Y (-2) +
        pairDeltaMass c h3 X Y (-1) * pairProgressTilt n d +
        pairDeltaMass c h3 X Y 1 * pairProgressTilt n d ^ 3 +
        pairDeltaMass c h3 X Y 2 * pairProgressTilt n d ^ 4 ≤
      pairProgressFactor n d *
        (pairDeltaMass c h3 X Y (-2) +
          pairDeltaMass c h3 X Y (-1) +
          pairDeltaMass c h3 X Y 1 +
          pairDeltaMass c h3 X Y 2) *
        pairProgressTilt n d ^ 2 := by
  let u := pairGapLinearBase n d
  let w := pairProgressTilt n d
  let φ := pairProgressFactor n d
  have hn : 0 < n := by omega
  have hu : u ≤ 1 := pairGapLinearBase_le_one n d hn
  have hw : w ≤ 1 := pairProgressTilt_le_one n d hn
  have hφ : φ ≤ 1 := pairProgressFactor_le_one n d hn
  have hφw : φ * w ≤ 1 := by
    calc
      φ * w ≤ 1 * 1 := mul_le_mul hφ hw bot_le bot_le
      _ = 1 := one_mul 1
  have hφw2 : φ * w ^ 2 ≤ 1 := by
    have hw2 : w ^ 2 ≤ 1 := by
      exact pow_le_one₀ (by exact bot_le) hw
    calc
      φ * w ^ 2 ≤ 1 * 1 := mul_le_mul hφ hw2 bot_le bot_le
      _ = 1 := one_mul 1
  have h1 :
      pairDeltaMass c h3 X Y (-1) * w +
          pairDeltaMass c h3 X Y 1 * w ^ 3 ≤
        φ * (pairDeltaMass c h3 X Y (-1) +
          pairDeltaMass c h3 X Y 1) * w ^ 2 := by
    apply Tri.one_jump_strict_pair
      (pairDeltaMass_le_one c h3 X Y (-1))
      (pairDeltaMass_le_one c h3 X Y 1)
      hu hw hφ hφw
    · dsimp only [u]
      rw [pairDeltaMass_neg_one_eq_thirdPartyDownMass_sum
          c h3 X Y hXY,
        pairDeltaMass_one_eq_thirdPartyUpMass_sum
          c h3 X Y hXY]
      exact thirdPartyDownMass_sum_le_up_mul_linearBase
        c h3 X Y hXY d hgap
    · dsimp only [u, w, φ]
      exact pairProgress_scalar_one n d hn hdn
  have h2 :
      pairDeltaMass c h3 X Y (-2) +
          pairDeltaMass c h3 X Y 2 * w ^ 4 ≤
        φ * (pairDeltaMass c h3 X Y (-2) +
          pairDeltaMass c h3 X Y 2) * w ^ 2 := by
    apply Tri.two_jump_strict_pair
      (pairDeltaMass_le_one c h3 X Y (-2))
      (pairDeltaMass_le_one c h3 X Y 2)
      hu hw hφ hφw2
    · dsimp only [u]
      rw [pairDeltaMass_neg_two_eq_directedFireMass
          c h3 X Y hXY,
        pairDeltaMass_two_eq_directedFireMass
          c h3 X Y hXY]
      exact reverse_directedFireMass_le_linearBase_sq
        c h3 X Y hXY d (hgap Y (Ne.symm hXY))
    · dsimp only [u, w, φ]
      exact pairProgress_scalar_two n d hn hdn
  dsimp only [w, φ] at h1 h2 ⊢
  calc
    pairDeltaMass c h3 X Y (-2) +
          pairDeltaMass c h3 X Y (-1) * pairProgressTilt n d +
          pairDeltaMass c h3 X Y 1 * pairProgressTilt n d ^ 3 +
          pairDeltaMass c h3 X Y 2 * pairProgressTilt n d ^ 4 =
        (pairDeltaMass c h3 X Y (-2) +
          pairDeltaMass c h3 X Y 2 * pairProgressTilt n d ^ 4) +
        (pairDeltaMass c h3 X Y (-1) * pairProgressTilt n d +
          pairDeltaMass c h3 X Y 1 * pairProgressTilt n d ^ 3) := by
      ring
    _ ≤ pairProgressFactor n d *
          (pairDeltaMass c h3 X Y (-2) +
            pairDeltaMass c h3 X Y 2) *
            pairProgressTilt n d ^ 2 +
        pairProgressFactor n d *
          (pairDeltaMass c h3 X Y (-1) +
            pairDeltaMass c h3 X Y 1) *
            pairProgressTilt n d ^ 2 :=
      add_le_add h2 h1
    _ = pairProgressFactor n d *
        (pairDeltaMass c h3 X Y (-2) +
          pairDeltaMass c h3 X Y (-1) +
          pairDeltaMass c h3 X Y 1 +
          pairDeltaMass c h3 X Y 2) *
        pairProgressTilt n d ^ 2 := by
      ring

/-- A nonzero pair-gap increment necessarily comes from a productive sample. -/
theorem isProductiveSample_of_pairDelta_ne_zero
    {c : Config m n} (t : TripleSample c) (X Y : Species m)
    (ht : samplePairDelta t X Y ≠ 0) :
    IsProductiveSample t := by
  classical
  unfold IsProductiveSample
  cases hclass : classify t with
  | none =>
      exfalso
      apply ht
      simp [samplePairDelta, hclass]
  | some p =>
      simp

/-- Productive mass whose reaction is irrelevant to the fixed pair. -/
noncomputable def pairIrrelevantProductiveMass
    (c : Config m n) (h3 : 3 ≤ n)
    (X Y : Species m) : ℝ≥0∞ :=
  ∑' t : TripleSample c,
    if IsProductiveSample t ∧ samplePairDelta t X Y = 0 then
      triplePMF c h3 t else 0

/-- Total productive mass of reactions relevant to the fixed pair. -/
noncomputable def pairRelevantMass
    (c : Config m n) (h3 : 3 ≤ n)
    (X Y : Species m) : ℝ≥0∞ :=
  pairDeltaMass c h3 X Y (-2) +
    pairDeltaMass c h3 X Y (-1) +
    pairDeltaMass c h3 X Y 1 +
    pairDeltaMass c h3 X Y 2

/-- Irrelevant and relevant productive fibers partition productive mass. -/
theorem pairIrrelevant_add_relevant_eq_productiveMass
    (c : Config m n) (h3 : 3 ≤ n)
    (X Y : Species m) :
    pairIrrelevantProductiveMass c h3 X Y +
        pairRelevantMass c h3 X Y =
      productiveMass c h3 := by
  classical
  unfold pairIrrelevantProductiveMass pairRelevantMass
    productiveMass pairDeltaMass
  simp only [tsum_fintype]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t _ht
  have hlo := samplePairDelta_lower t X Y
  have hhi := samplePairDelta_upper t X Y
  have hcases :
      samplePairDelta t X Y = -2 ∨
      samplePairDelta t X Y = -1 ∨
      samplePairDelta t X Y = 0 ∨
      samplePairDelta t X Y = 1 ∨
      samplePairDelta t X Y = 2 := by
    omega
  rcases hcases with h | h | h | h | h
  · have hp :=
      isProductiveSample_of_pairDelta_ne_zero t X Y (by omega)
    simp [h, hp]
  · have hp :=
      isProductiveSample_of_pairDelta_ne_zero t X Y (by omega)
    simp [h, hp]
  · by_cases hp : IsProductiveSample t <;> simp [h, hp]
  · have hp :=
      isProductiveSample_of_pairDelta_ne_zero t X Y (by omega)
    simp [h, hp]
  · have hp :=
      isProductiveSample_of_pairDelta_ne_zero t X Y (by omega)
    simp [h, hp]

/-- Productive-event kernel augmented by the number of nonzero fixed-pair
jumps. Zero-productive-mass states are absorbing. -/
noncomputable def productivePairRelevantCount
    (h3 : 3 ≤ n) (X Y : Species m) :
    Config m n × ℕ → PMF (Config m n × ℕ) := by
  classical
  exact fun q => by
    by_cases hprod : productiveMass q.1 h3 ≠ 0
    · exact (productiveSamplePMF q.1 h3 hprod).map fun t =>
        (sampleNext q.1 t,
          if samplePairDelta t X Y = 0 then q.2 else q.2 + 1)
    · exact PMF.pure q

/-- Joint gap/relevant-event potential used for forward progress. -/
noncomputable def pairProgressPotential
    (X Y : Species m) (w φ : ℝ≥0∞)
    (q : Config m n × ℕ) : ℝ≥0∞ :=
  w ^ pairGapNat q.1 X Y * (φ⁻¹) ^ q.2

end Tri.Multi

#print axioms Tri.one_jump_strict_pair
#print axioms Tri.two_jump_strict_pair
#print axioms Tri.Multi.pairProgress_scalar_one
#print axioms Tri.Multi.pairProgress_scalar_two
#print axioms Tri.Multi.pairDeltaMass_relevant_strict_mgf
#print axioms Tri.Multi.pairIrrelevant_add_relevant_eq_productiveMass
