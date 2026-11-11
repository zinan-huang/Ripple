/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.PaperLemma11Modes
import Tri.HitProbMono
import Tri.TimeChangeHitting
import Tri.FiniteHorizonUnion
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Lemma 11: probability bounds for the genuine cumulative mode events


The counters and the unrestricted productive chain are those of
PaperLemma11Modes. Both potentials are stopped at the common first crossing.
The doubled physical gap is retained, so no floor(D/2) loss enters the
rational odds. The direct potential measures its counter in units of two.

The resulting union bound is
  (m-1) * (rD ^ ceil(D/8) + rT ^ ceil(D/4)),
where rD = (2n-D)/(2n+D) and rT = (4n-D)/(4n+D).
It is at most 2(m-1) exp(-D^2/(8n)), and, after using probability <= 1,
at most m exp(-D^2/(16n)). The paper-facing wrappers retain 1/18.

Verification status: proof scripts supplied; no Lean build was run in the
connector-only authoring session. The source contains no proof placeholders.
-/

namespace Tri.Multi

open scoped BigOperators ENNReal

variable {m n : ℕ}

/-- Rational odds corresponding to a symmetric additive bias. -/
noncomputable def modeSharpOdds (N D : ℕ) : ℝ≥0∞ :=
  ((N - D : ℕ) : ℝ≥0∞) / ((N + D : ℕ) : ℝ≥0∞)

theorem lemma11_count_pair_le
    (c : Config m n) (X Y : Species m) (hXY : X ≠ Y) :
    count c X + count c Y ≤ n := by
  classical
  have hY : count c Y ≤ zSum c X := by
    unfold zSum
    exact Finset.single_le_sum
      (fun i _ => Nat.zero_le (count c i))
      (by simp [Ne.symm hXY])
  have ht := count_add_zSum c X
  omega

/-- Sharp direct odds, with a doubled gap to avoid rounding D/2. -/
theorem lemma11_direct_weight_cross
    (N D x y : ℕ)
    (hDN : D ≤ N)
    (hsum : x + y ≤ N)
    (hgap : 2 * y + D ≤ 2 * x) :
    (2 * N + D) * (Nat.choose y 2 * x) ≤
      (2 * N - D) * (Nat.choose x 2 * y) := by
  by_cases hy : y = 0
  · simp [hy]
  have hx : 0 < x := by omega
  have hratio :
      (2 * N + D) * (y - 1) ≤
        (2 * N - D) * (x - 1) := by
    have hsum' : (x - 1) + (y - 1) ≤ N := by omega
    have hgap' : D + 2 * (y - 1) ≤ 2 * (x - 1) := by omega
    have h₁ := Nat.mul_le_mul_left N hgap'
    have h₂ := Nat.mul_le_mul_left D hsum'
    have hsub : 2 * N - D + D = 2 * N :=
      Nat.sub_add_cancel (by omega)
    have h₃ := congrArg (fun a : ℕ => a * (x - 1)) hsub
    nlinarith
  have htwoY : 2 * Nat.choose y 2 = y * (y - 1) :=
    two_mul_choose_two y
  have htwoX : 2 * Nat.choose x 2 = x * (x - 1) :=
    two_mul_choose_two x
  have hscaled :
      2 * ((2 * N + D) * (Nat.choose y 2 * x)) ≤
        2 * ((2 * N - D) * (Nat.choose x 2 * y)) := by
    calc
      2 * ((2 * N + D) * (Nat.choose y 2 * x)) =
          (2 * N + D) * x * (2 * Nat.choose y 2) := by ring
      _ = (2 * N + D) * x * (y * (y - 1)) := by rw [htwoY]
      _ = x * y * ((2 * N + D) * (y - 1)) := by ring
      _ ≤ x * y * ((2 * N - D) * (x - 1)) :=
        Nat.mul_le_mul_left (x * y) hratio
      _ = (2 * N - D) * y * (x * (x - 1)) := by ring
      _ = (2 * N - D) * y * (2 * Nat.choose x 2) := by rw [htwoX]
      _ = 2 * ((2 * N - D) * (Nat.choose x 2 * y)) := by ring
  omega

/-- The exact third-party drift retains a doubled plurality-gap factor. -/
theorem lemma11_doubled_gap_product
    (D x y z : ℕ)
    (hgapY : 2 * y + D ≤ 2 * x)
    (hgapZ : 2 * z + D ≤ 2 * x) :
    D * x ≤ 2 * (x - y) * (x + y - z) := by
  let d := min (x - y) (x - z)
  have hyx : y ≤ x := by omega
  have hzx : z ≤ x := by omega
  have hdy : d ≤ x - y := Nat.min_le_left _ _
  have hdz : d ≤ x - z := Nat.min_le_right _ _
  have hD : D ≤ 2 * d := by
    dsimp only [d]
    omega
  have hg :
      d * x ≤ (x - y) * (x + y - z) :=
    gap_mul_count_le_thirdParty_gap_product
      d x y z (by omega) (by omega)
  calc
    D * x ≤ (2 * d) * x := Nat.mul_le_mul_right x hD
    _ = 2 * (d * x) := by ring
    _ ≤ 2 * ((x - y) * (x + y - z)) :=
      Nat.mul_le_mul_left 2 hg
    _ = 2 * (x - y) * (x + y - z) := by ring

/-- Sharp third-party odds with the without-replacement weights. -/
theorem lemma11_third_weight_cross
    (N D x y z : ℕ)
    (hDN : D ≤ N)
    (hsum : x + y ≤ N)
    (hgapY : 2 * y + D ≤ 2 * x)
    (hgapZ : 2 * z + D ≤ 2 * x) :
    (4 * N + D) *
        (Nat.choose z 2 * x + Nat.choose y 2 * z) ≤
      (4 * N - D) *
        (Nat.choose x 2 * z + Nat.choose z 2 * y) := by
  let L := Nat.choose z 2 * x + Nat.choose y 2 * z
  let U := Nat.choose x 2 * z + Nat.choose z 2 * y
  let G := z * (x - y) * (x + y - z)
  have hyx : y ≤ x := by omega
  have hzx : z ≤ x := by omega
  have hgapIdentity : 2 * U = 2 * L + G := by
    dsimp only [U, L, G]
    exact thirdParty_doubled_gap_identity x y z hyx hzx
  have hsumWeight : U + L ≤ z * N * x := by
    have htwo : 2 * (U + L) ≤ 2 * (z * N * x) := by
      calc
        2 * (U + L) =
            (2 * Nat.choose x 2) * z +
              (2 * Nat.choose z 2) * y +
              ((2 * Nat.choose z 2) * x +
                (2 * Nat.choose y 2) * z) := by
          dsimp only [U, L]
          ring
        _ = x * (x - 1) * z + z * (z - 1) * y +
              (z * (z - 1) * x + y * (y - 1) * z) := by
          simp only [two_mul_choose_two]
        _ ≤ x * x * z + z * z * y +
              (z * z * x + y * y * z) := by
          gcongr <;> omega
        _ ≤ z * (x + y) * (x + z) := by
          have h := Nat.mul_le_mul_right (y * z) hyx
          nlinarith only [h]
        _ ≤ z * N * (2 * x) := by
          gcongr <;> omega
        _ = 2 * (z * N * x) := by ring
    omega
  have hG : z * D * x ≤ 2 * G := by
    calc
      z * D * x = z * (D * x) := by ring
      _ ≤ z * (2 * (x - y) * (x + y - z)) :=
        Nat.mul_le_mul_left z
          (lemma11_doubled_gap_product D x y z hgapY hgapZ)
      _ = 2 * G := by dsimp only [G]; ring
  have hcore : D * (U + L) ≤ 2 * N * G := by
    calc
      D * (U + L) ≤ D * (z * N * x) :=
        Nat.mul_le_mul_left D hsumWeight
      _ = N * (z * D * x) := by ring
      _ ≤ N * (2 * G) := Nat.mul_le_mul_left N hG
      _ = 2 * N * G := by ring
  have hscaled : 4 * N * U = 4 * N * L + 2 * N * G := by
    calc
      4 * N * U = 2 * N * (2 * U) := by ring
      _ = 2 * N * (2 * L + G) := by rw [hgapIdentity]
      _ = 4 * N * L + 2 * N * G := by ring
  have hsub : 4 * N - D + D = 4 * N :=
    Nat.sub_add_cancel (by omega)
  have hrestore := congrArg (fun a : ℕ => a * U) hsub
  change (4 * N + D) * L ≤ (4 * N - D) * U
  nlinarith

theorem reverse_directedFireMass_le_modeSharpOdds
    (c : Config m n) (h3 : 3 ≤ n)
    (X Y : Species m) (hXY : X ≠ Y)
    (D : ℕ) (hDN : D ≤ n)
    (hgap : 2 * count c Y + D ≤ 2 * count c X) :
    directedFireMass c h3 Y X ≤
      directedFireMass c h3 X Y * modeSharpOdds (2 * n) D := by
  rw [directedFireMass_eq c h3 Y X (Ne.symm hXY),
    directedFireMass_eq c h3 X Y hXY]
  apply div_le_div_mul_right
  unfold modeSharpOdds
  have hden0 : (((2 * n + D : ℕ) : ℝ≥0∞)) ≠ 0 := by
    exact_mod_cast (by omega : 2 * n + D ≠ 0)
  have hdenTop : (((2 * n + D : ℕ) : ℝ≥0∞)) ≠ ⊤ :=
    ENNReal.natCast_ne_top _
  rw [← mul_div_assoc,
    ENNReal.le_div_iff_mul_le (Or.inl hden0) (Or.inl hdenTop)]
  exact_mod_cast (by
    simpa [directedFireWeight, mul_comm, mul_left_comm, mul_assoc] using
      lemma11_direct_weight_cross n D (count c X) (count c Y)
        hDN (lemma11_count_pair_le c X Y hXY) hgap)

theorem thirdPartyDownMass_le_upMass_mul_modeSharpOdds
    (c : Config m n) (h3 : 3 ≤ n)
    (X Y Z : Species m)
    (hXY : X ≠ Y) (hXZ : X ≠ Z) (hYZ : Y ≠ Z)
    (D : ℕ) (hDN : D ≤ n)
    (hgapY : 2 * count c Y + D ≤ 2 * count c X)
    (hgapZ : 2 * count c Z + D ≤ 2 * count c X) :
    thirdPartyDownMass c h3 X Y Z ≤
      thirdPartyUpMass c h3 X Y Z * modeSharpOdds (4 * n) D := by
  rw [thirdPartyDownMass_eq c h3 X Y Z (Ne.symm hXZ) hYZ,
    thirdPartyUpMass_eq c h3 X Y Z hXZ (fun h => hYZ h.symm)]
  apply div_le_div_mul_right
  unfold modeSharpOdds
  have hden0 : (((4 * n + D : ℕ) : ℝ≥0∞)) ≠ 0 := by
    exact_mod_cast (by omega : 4 * n + D ≠ 0)
  have hdenTop : (((4 * n + D : ℕ) : ℝ≥0∞)) ≠ ⊤ :=
    ENNReal.natCast_ne_top _
  rw [← mul_div_assoc,
    ENNReal.le_div_iff_mul_le (Or.inl hden0) (Or.inl hdenTop)]
  exact_mod_cast (by
    simpa [thirdPartyDownWeight, thirdPartyUpWeight, directedFireWeight,
      mul_comm, mul_left_comm, mul_assoc] using
      lemma11_third_weight_cross n D
        (count c X) (count c Y) (count c Z)
        hDN (lemma11_count_pair_le c X Y hXY) hgapY hgapZ)

theorem thirdPartyDownMass_sum_le_up_mul_modeSharpOdds
    (c : Config m n) (h3 : 3 ≤ n)
    (X Y : Species m) (hXY : X ≠ Y)
    (D : ℕ) (hDN : D ≤ n)
    (hgap : ∀ Z, Z ≠ X → 2 * count c Z + D ≤ 2 * count c X) :
    (∑ Z ∈ thirdSpecies X Y, thirdPartyDownMass c h3 X Y Z) ≤
      (∑ Z ∈ thirdSpecies X Y, thirdPartyUpMass c h3 X Y Z) *
        modeSharpOdds (4 * n) D := by
  calc
    (∑ Z ∈ thirdSpecies X Y, thirdPartyDownMass c h3 X Y Z) ≤
        ∑ Z ∈ thirdSpecies X Y,
          thirdPartyUpMass c h3 X Y Z * modeSharpOdds (4 * n) D := by
      apply Finset.sum_le_sum
      intro Z hZ
      have hZX : Z ≠ X :=
        (Finset.mem_erase.mp (Finset.mem_erase.mp hZ).2).1
      have hZY : Z ≠ Y := (Finset.mem_erase.mp hZ).1
      exact thirdPartyDownMass_le_upMass_mul_modeSharpOdds
        c h3 X Y Z hXY (Ne.symm hZX) (Ne.symm hZY) D hDN
        (hgap Y (Ne.symm hXY)) (hgap Z hZX)
    _ = (∑ Z ∈ thirdSpecies X Y, thirdPartyUpMass c h3 X Y Z) *
          modeSharpOdds (4 * n) D := by
      rw [Finset.sum_mul]

/-- The repaired exponential comparison for symmetric odds. -/
theorem lemma11_symmetric_ratio_le_exp
    (s : ℝ) (hs : 0 ≤ s) :
    (1 - s) / (1 + s) ≤ Real.exp (-2 * s) := by
  let f : ℝ → ℝ :=
    fun t => (1 - t) - (1 + t) * Real.exp (-2 * t)
  have hd : ∀ t : ℝ,
      HasDerivAt f ((1 + 2 * t) * Real.exp (-2 * t) - 1) t := by
    intro t
    have hm : HasDerivAt (fun z : ℝ => 1 - z) (-1) t := by
      simpa using
        (hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)
    have hp : HasDerivAt (fun z : ℝ => 1 + z) 1 t := by
      simpa using
        (hasDerivAt_const t (1 : ℝ)).add (hasDerivAt_id t)
    have he :
        HasDerivAt (fun z : ℝ => Real.exp (-2 * z))
          (-2 * Real.exp (-2 * t)) t := by
      have h0 := ((hasDerivAt_id t).const_mul (-2)).exp
      simp only [id, mul_one] at h0
      exact h0.congr_deriv (by ring)
    dsimp only [f]
    convert hm.sub (hp.mul he) using 1 <;> ring
  have hnonpos :
      ∀ t : ℝ, (1 + 2 * t) * Real.exp (-2 * t) - 1 ≤ 0 := by
    intro t
    have h := mul_le_mul_of_nonneg_right
      (Real.add_one_le_exp (2 * t)) (Real.exp_pos (-2 * t)).le
    rw [← Real.exp_add,
      show 2 * t + -2 * t = 0 by ring, Real.exp_zero] at h
    nlinarith
  have hanti : Antitone f :=
    antitone_of_hasDerivAt_nonpos hd hnonpos
  have hfs : f s ≤ f 0 := hanti hs
  have hf0 : f 0 = 0 := by simp [f]
  rw [hf0] at hfs
  apply (div_le_iff₀ (by linarith : (0 : ℝ) < 1 + s)).2
  dsimp only [f] at hfs
  nlinarith

theorem mode_sharpOdds_le_exp
    (N D : ℕ) (hN : 0 < N) (hDN : D ≤ N) :
    modeSharpOdds N D ≤
      ENNReal.ofReal (Real.exp (-2 * (D : ℝ) / (N : ℝ))) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hdenR : (0 : ℝ) < (N + D : ℕ) := by
    exact_mod_cast (by omega : 0 < N + D)
  have hdiv :
      (((N - D : ℕ) : ℝ≥0∞) / ((N + D : ℕ) : ℝ≥0∞)) =
        ENNReal.ofReal (((N - D : ℕ) : ℝ) / ((N + D : ℕ) : ℝ)) := by
    rw [ENNReal.ofReal_div_of_pos hdenR,
      ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
  unfold modeSharpOdds
  rw [hdiv]
  apply ENNReal.ofReal_le_ofReal
  rw [Nat.cast_sub hDN, Nat.cast_add]
  have hratio :
      ((N : ℝ) - D) / ((N : ℝ) + D) =
        (1 - (D : ℝ) / N) / (1 + (D : ℝ) / N) := by
    have hden : (N : ℝ) + D ≠ 0 := by positivity
    have hden' : (1 : ℝ) + (D : ℝ) / N ≠ 0 := by positivity
    field_simp [ne_of_gt hNR, hden, hden']
    <;> ring
  rw [hratio]
  simpa only [mul_div_assoc] using
    lemma11_symmetric_ratio_le_exp ((D : ℝ) / N) (by positivity)

end Tri.Multi

namespace Tri.Multi

open scoped BigOperators ENNReal

variable {m n : ℕ}

/-- The shifted natural level; the offset leaves room for a direct -2 jump. -/
def lemma11ModeLevel (D : ℕ) (z : ℤ) : ℕ :=
  (z + (((D + 3) / 4 : ℕ) : ℤ) + 2).toNat

noncomputable def lemma11ThirdPotential
    (u : ℝ≥0∞) (D : ℕ) (Y : Species m)
    (q : PairModeState m n) : ℝ≥0∞ :=
  u ^ lemma11ModeLevel D (q.2.2 Y)

theorem lemma11ModeLevel_le_two
    (D : ℕ) (z : ℤ) (hz : 4 * z ≤ -(D : ℤ)) :
    lemma11ModeLevel D z ≤ 2 := by
  unfold lemma11ModeLevel
  omega

theorem lemma11ModeLevel_ge_two
    (D : ℕ) (z : ℤ) (hz : -(D : ℤ) < 4 * z) :
    2 ≤ lemma11ModeLevel D z := by
  unfold lemma11ModeLevel
  omega

@[simp] theorem lemma11ModeLevel_zero (D : ℕ) :
    lemma11ModeLevel D 0 = (D + 3) / 4 + 2 := by
  unfold lemma11ModeLevel
  omega

/-- Exact five-fiber expectation identity, for any function of the signed
pair increment. No projected-chain Markov assumption is used. -/
theorem expect_multiStep_pairTransitionDelta
    (c : Config m n) (h3 : 3 ≤ n)
    (X Y : Species m) (f : ℤ → ℝ≥0∞) :
    expect (multiStep c h3)
        (fun c' => f (pairTransitionDelta c c' X Y)) =
      pairDeltaMass c h3 X Y (-2) * f (-2) +
      pairDeltaMass c h3 X Y (-1) * f (-1) +
      pairDeltaMass c h3 X Y 0 * f 0 +
      pairDeltaMass c h3 X Y 1 * f 1 +
      pairDeltaMass c h3 X Y 2 * f 2 := by
  classical
  unfold multiStep
  rw [expect_map]
  unfold expect pairDeltaMass
  simp only [tsum_fintype, Finset.sum_mul]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  rw [pairTransitionDelta_sampleNext]
  have hlo := samplePairDelta_lower t X Y
  have hhi := samplePairDelta_upper t X Y
  have hc :
      samplePairDelta t X Y = -2 ∨
      samplePairDelta t X Y = -1 ∨
      samplePairDelta t X Y = 0 ∨
      samplePairDelta t X Y = 1 ∨
      samplePairDelta t X Y = 2 := by omega
  rcases hc with h | h | h | h | h <;> simp [h]

/-- The third-party masked moment lifts to the same augmented productive step. -/
theorem productivePairModeStep_third_conserve_of_core
    (h3 : 3 ≤ n) (X Y : Species m) (D : ℕ)
    (u : ℝ≥0∞) (hu1 : u ≤ 1)
    (q : PairModeState m n)
    (hg : 2 ≤ lemma11ModeLevel D (q.2.2 Y))
    (hcore :
      pairDeltaMass q.1 h3 X Y (-1) * u +
        (pairDeltaMass q.1 h3 X Y (-2) +
          pairDeltaMass q.1 h3 X Y 0 +
          pairDeltaMass q.1 h3 X Y 2) * u ^ 2 +
        pairDeltaMass q.1 h3 X Y 1 * u ^ 3 ≤ u ^ 2) :
    expect (productivePairModeStep h3 X q)
        (lemma11ThirdPotential u D Y) ≤
      lemma11ThirdPotential u D Y q := by
  let g := lemma11ModeLevel D (q.2.2 Y)
  let f : ℤ → ℝ≥0∞ := fun j =>
    u ^ lemma11ModeLevel D
      (q.2.2 Y + if j = 1 ∨ j = -1 then j else 0)
  have hm2 : f (-2) = u ^ g := by norm_num [f, g]
  have hm1 : f (-1) = u ^ (g - 1) := by
    dsimp only [f]
    norm_num
    congr 1
    dsimp only [g, lemma11ModeLevel] at *
    omega
  have h0 : f 0 = u ^ g := by norm_num [f, g]
  have h1 : f 1 = u ^ (g + 1) := by
    dsimp only [f]
    norm_num
    congr 1
    dsimp only [g, lemma11ModeLevel] at *
    omega
  have h2 : f 2 = u ^ g := by norm_num [f, g]
  have hraw :
      expect (multiStep q.1 h3)
        (fun c' => lemma11ThirdPotential u D Y (pairModeNext X q c')) ≤
      lemma11ThirdPotential u D Y q := by
    change expect (multiStep q.1 h3)
        (fun c' => f (pairTransitionDelta q.1 c' X Y)) ≤ u ^ g
    rw [expect_multiStep_pairTransitionDelta, hm2, hm1, h0, h1, h2]
    have h := third_only_geometric_of_core hg hcore
    convert h using 1 <;> simp only [g] <;> ring
  unfold productivePairModeStep
  rw [expect_map]
  have htop : lemma11ThirdPotential u D Y q ≠ ⊤ :=
    ENNReal.pow_ne_top
      (ne_top_of_le_ne_top ENNReal.one_ne_top hu1)
  have hraw' :
      expect (multiStep q.1 h3)
        (fun c' => lemma11ThirdPotential u D Y (pairModeNext X q c')) ≤
      lemma11ThirdPotential u D Y (pairModeNext X q q.1) := by
    simpa only [pairModeNext_self] using hraw
  have hp := productiveStep_conserve_of_multiStep_conserve
    q.1 h3
    (fun c' => lemma11ThirdPotential u D Y (pairModeNext X q c'))
    (by simpa only [pairModeNext_self] using htop) hraw'
  simpa only [pairModeNext_self] using hp

/-- The live augmented state has the exact doubled half-gap, without rounding D. -/
theorem pairModeInvariant_double_gap_of_not_bad
    (c0 : Config m n) (X : Species m) (D : ℕ)
    (q : PairModeState m n)
    (hinit : HasPairwiseGap c0 X D)
    (hinv : PairModeInvariant c0 X q)
    (hsafe : ¬ PairModeBad X D q) :
    ∀ Y, Y ≠ X → 2 * count q.1 Y + D ≤ 2 * count q.1 X := by
  intro Y hYX
  have h0 := hinit Y hYX
  have hrec := hinv Y
  have hd : -(D : ℤ) < 4 * q.2.1 Y := by
    by_contra h
    exact hsafe (Or.inl ⟨Y, hYX, by omega⟩)
  have ht : -(D : ℤ) < 4 * q.2.2 Y := by
    by_contra h
    exact hsafe (Or.inr ⟨Y, hYX, by omega⟩)
  unfold pairGap at hrec
  omega

end Tri.Multi

namespace Tri

open scoped BigOperators ENNReal

attribute [local instance] Classical.propDecidable

/-- Union bound for two unrestricted finite-horizon hitting events. -/
theorem hitProb_or_le_add
    {α : Type*} (K : α → PMF α)
    (B C : α → Prop) [DecidablePred B] [DecidablePred C]
    (T : ℕ) (s : α) :
    hitProb (fun z => B z ∨ C z) K T s ≤
      hitProb B K T s + hitProb C K T s := by
  classical
  induction T generalizing s with
  | zero =>
      by_cases hB : B s <;> by_cases hC : C s <;>
        norm_num [hitProb, iter, expect_pure, ind, hB, hC]
  | succ T ih =>
      by_cases hB : B s
      · rw [hitProb_eq_one_of_mem (fun z => B z ∨ C z) K
            (T + 1) s (Or.inl hB),
          hitProb_eq_one_of_mem B K (T + 1) s hB]
        exact le_add_right le_rfl
      · by_cases hC : C s
        · rw [hitProb_eq_one_of_mem (fun z => B z ∨ C z) K
              (T + 1) s (Or.inr hC),
            hitProb_eq_one_of_mem C K (T + 1) s hC]
          exact le_add_left le_rfl
        · have hBC : ¬ (B s ∨ C s) := by
            rintro (h | h)
            · exact hB h
            · exact hC h
          rw [hitProb_succ_of_not (fun z => B z ∨ C z) K T s hBC,
            hitProb_succ_of_not B K T s hB,
            hitProb_succ_of_not C K T s hC,
            ← ENNReal.tsum_add]
          refine ENNReal.tsum_le_tsum fun z => ?_
          rw [← mul_add]
          exact mul_le_mul_right (ih z) (K s z)

namespace Multi

variable {m n : ℕ}

/-- The finite-horizon union of the two cumulative mode events. -/
noncomputable def productivePairModeHitMass
    (h3 : 3 ≤ n) (X : Species m) (D T : ℕ)
    (c0 : Config m n) : ℝ≥0∞ := by
  classical
  exact hitProb (PairModeBad X D)
    (productivePairModeStep h3 X) T (pairModeInitial c0)

theorem productivePairModeEverMass_eq_iSup
    (h3 : 3 ≤ n) (X : Species m) (D : ℕ)
    (c0 : Config m n) :
    productivePairModeEverMass h3 X D c0 =
      ⨆ T : ℕ, productivePairModeHitMass h3 X D T c0 := rfl

/-- Stopping at the common boundary represents the unrestricted union hit. -/
theorem productivePairModeHitMass_eq_stopped_mass
    (h3 : 3 ≤ n) (X : Species m) (D T : ℕ)
    (c0 : Config m n) :
    productivePairModeHitMass h3 X D T c0 =
      ∑' q : PairModeState m n,
        if PairModeBad X D q then
          iter (freeze (PairModeBad X D) (productivePairModeStep h3 X))
            T (pairModeInitial c0) q
        else 0 := by
  classical
  unfold productivePairModeHitMass hitProb expect ind
  apply tsum_congr
  intro q
  by_cases hq : PairModeBad X D q <;> simp [hq]

theorem productiveDirectModeHitMass_le_pair
    (h3 : 3 ≤ n) (X : Species m) (D T : ℕ)
    (c0 : Config m n) :
    productiveDirectModeHitMass h3 X D T c0 ≤
      productivePairModeHitMass h3 X D T c0 := by
  classical
  exact hitProb_mono_target
    (K := productivePairModeStep h3 X)
    (B := DirectModeBad X D) (C := PairModeBad X D)
    (fun _ h => Or.inl h) T (pairModeInitial c0)

theorem productiveThirdPartyModeHitMass_le_pair
    (h3 : 3 ≤ n) (X : Species m) (D T : ℕ)
    (c0 : Config m n) :
    productiveThirdPartyModeHitMass h3 X D T c0 ≤
      productivePairModeHitMass h3 X D T c0 := by
  classical
  exact hitProb_mono_target
    (K := productivePairModeStep h3 X)
    (B := ThirdPartyModeBad X D) (C := PairModeBad X D)
    (fun _ h => Or.inr h) T (pairModeInitial c0)

theorem productivePairModeHitMass_le_add
    (h3 : 3 ≤ n) (X : Species m) (D T : ℕ)
    (c0 : Config m n) :
    productivePairModeHitMass h3 X D T c0 ≤
      productiveDirectModeHitMass h3 X D T c0 +
        productiveThirdPartyModeHitMass h3 X D T c0 := by
  classical
  unfold productivePairModeHitMass productiveDirectModeHitMass
    productiveThirdPartyModeHitMass
  convert hitProb_or_le_add (productivePairModeStep h3 X)
      (DirectModeBad X D) (ThirdPartyModeBad X D)
      T (pairModeInitial c0) using 2

theorem productivePairModeHitMass_le_one
    (h3 : 3 ≤ n) (X : Species m) (D T : ℕ)
    (c0 : Config m n) :
    productivePairModeHitMass h3 X D T c0 ≤ 1 := by
  classical
  exact hitProb_le_one (PairModeBad X D)
    (productivePairModeStep h3 X) T (pairModeInitial c0)

theorem productiveDirectModeHitMass_le_ever
    (h3 : 3 ≤ n) (X : Species m) (D T : ℕ)
    (c0 : Config m n) :
    productiveDirectModeHitMass h3 X D T c0 ≤
      productiveDirectModeEverMass h3 X D c0 :=
  le_iSup (fun U : ℕ => productiveDirectModeHitMass h3 X D U c0) T

theorem productiveThirdPartyModeHitMass_le_ever
    (h3 : 3 ≤ n) (X : Species m) (D T : ℕ)
    (c0 : Config m n) :
    productiveThirdPartyModeHitMass h3 X D T c0 ≤
      productiveThirdPartyModeEverMass h3 X D c0 :=
  le_iSup (fun U : ℕ => productiveThirdPartyModeHitMass h3 X D U c0) T

theorem productivePairModeHitMass_le_ever
    (h3 : 3 ≤ n) (X : Species m) (D T : ℕ)
    (c0 : Config m n) :
    productivePairModeHitMass h3 X D T c0 ≤
      productivePairModeEverMass h3 X D c0 := by
  rw [productivePairModeEverMass_eq_iSup]
  exact le_iSup (fun U : ℕ => productivePairModeHitMass h3 X D U c0) T

theorem productiveDirectModeEverMass_le_pair
    (h3 : 3 ≤ n) (X : Species m) (D : ℕ)
    (c0 : Config m n) :
    productiveDirectModeEverMass h3 X D c0 ≤
      productivePairModeEverMass h3 X D c0 := by
  refine iSup_le fun T => ?_
  exact (productiveDirectModeHitMass_le_pair h3 X D T c0).trans
    (productivePairModeHitMass_le_ever h3 X D T c0)

theorem productiveThirdPartyModeEverMass_le_pair
    (h3 : 3 ≤ n) (X : Species m) (D : ℕ)
    (c0 : Config m n) :
    productiveThirdPartyModeEverMass h3 X D c0 ≤
      productivePairModeEverMass h3 X D c0 := by
  refine iSup_le fun T => ?_
  exact (productiveThirdPartyModeHitMass_le_pair h3 X D T c0).trans
    (productivePairModeHitMass_le_ever h3 X D T c0)

theorem productivePairModeEverMass_le_add
    (h3 : 3 ≤ n) (X : Species m) (D : ℕ)
    (c0 : Config m n) :
    productivePairModeEverMass h3 X D c0 ≤
      productiveDirectModeEverMass h3 X D c0 +
        productiveThirdPartyModeEverMass h3 X D c0 := by
  rw [productivePairModeEverMass_eq_iSup]
  refine iSup_le fun T => ?_
  exact (productivePairModeHitMass_le_add h3 X D T c0).trans
    (add_le_add
      (productiveDirectModeHitMass_le_ever h3 X D T c0)
      (productiveThirdPartyModeHitMass_le_ever h3 X D T c0))

theorem productivePairModeEverMass_le_one
    (h3 : 3 ≤ n) (X : Species m) (D : ℕ)
    (c0 : Config m n) :
    productivePairModeEverMass h3 X D c0 ≤ 1 := by
  rw [productivePairModeEverMass_eq_iSup]
  exact iSup_le fun T => productivePairModeHitMass_le_one h3 X D T c0

end Multi
end Tri

namespace Tri.Multi

open scoped BigOperators ENNReal

variable {m n : ℕ}

/-- Common first-crossing bound for normalized mode potentials. -/
theorem productivePairModeEverMass_le_of_normalized_potentials
    (h3 : 3 ≤ n) (X : Species m) (D : ℕ) (c0 : Config m n)
    (bD bT : ℝ≥0∞)
    (VD VT : Species m → PairModeState m n → ℝ≥0∞)
    (hDstep : ∀ q, PairModeInvariant c0 X q → ¬ PairModeBad X D q →
      ∀ Y, Y ≠ X →
        expect (productivePairModeStep h3 X q) (VD Y) ≤ VD Y q)
    (hTstep : ∀ q, PairModeInvariant c0 X q → ¬ PairModeBad X D q →
      ∀ Y, Y ≠ X →
        expect (productivePairModeStep h3 X q) (VT Y) ≤ VT Y q)
    (hDbad : ∀ q, PairModeInvariant c0 X q → ∀ Y, Y ≠ X →
      4 * q.2.1 Y ≤ -(D : ℤ) → 1 ≤ VD Y q)
    (hTbad : ∀ q, PairModeInvariant c0 X q → ∀ Y, Y ≠ X →
      4 * q.2.2 Y ≤ -(D : ℤ) → 1 ≤ VT Y q)
    (hDinit : ∀ Y, Y ≠ X → VD Y (pairModeInitial c0) ≤ bD)
    (hTinit : ∀ Y, Y ≠ X → VT Y (pairModeInitial c0) ≤ bT) :
    productivePairModeEverMass h3 X D c0 ≤
      ((m - 1 : ℕ) : ℝ≥0∞) * (bD + bT) := by
  classical
  let K := freeze (PairModeBad X D) (productivePairModeStep h3 X)
  let V : PairModeState m n → ℝ≥0∞ := fun q =>
    ∑ Y ∈ Finset.univ.erase X, (VD Y q + VT Y q)
  have hclosed : ∀ q, PairModeInvariant c0 X q →
      ∀ z, K q z ≠ 0 → PairModeInvariant c0 X z := by
    intro q hq z hqz
    by_cases hb : PairModeBad X D q
    · have hp : K q = PMF.pure q := by simp [K, freeze, hb]
      rw [hp] at hqz
      have hzq : z = q := by
        by_contra hne
        simp [PMF.pure_apply, hne] at hqz
      simpa [hzq] using hq
    · have hk : K q = productivePairModeStep h3 X q := by
        simp [K, freeze, hb]
      rw [hk] at hqz
      exact productivePairModeStep_inv h3 c0 X q z hq hqz
  have hsuper : ∀ q, PairModeInvariant c0 X q → expect (K q) V ≤ V q := by
    intro q hq
    by_cases hb : PairModeBad X D q
    · simp [K, freeze, hb]
    · have hk : K q = productivePairModeStep h3 X q := by
        simp [K, freeze, hb]
      rw [hk]
      change expect (productivePairModeStep h3 X q)
          (fun z => ∑ Y ∈ Finset.univ.erase X, (VD Y z + VT Y z)) ≤
        ∑ Y ∈ Finset.univ.erase X, (VD Y q + VT Y q)
      rw [expect_finset_sum]
      apply Finset.sum_le_sum
      intro Y hY
      have hYX : Y ≠ X := (Finset.mem_erase.mp hY).1
      have hadd :
          expect (productivePairModeStep h3 X q) (fun z => VD Y z + VT Y z) =
            expect (productivePairModeStep h3 X q) (VD Y) +
              expect (productivePairModeStep h3 X q) (VT Y) := by
        unfold expect
        simp_rw [mul_add]
        exact ENNReal.tsum_add
      rw [hadd]
      exact add_le_add (hDstep q hq hb Y hYX) (hTstep q hq hb Y hYX)
  have hcontain : ∀ q, PairModeInvariant c0 X q →
      PairModeBad X D q → 1 ≤ V q := by
    intro q hq hb
    rcases hb with ⟨Y, hYX, hY⟩ | ⟨Y, hYX, hY⟩
    · calc
        (1 : ℝ≥0∞) ≤ VD Y q := hDbad q hq Y hYX hY
        _ ≤ VD Y q + VT Y q := le_add_right le_rfl
        _ ≤ V q := by
          dsimp only [V]
          exact Finset.single_le_sum (f := fun Y => VD Y q + VT Y q)
            (fun j _ => by simp) (by simp [hYX])
    · calc
        (1 : ℝ≥0∞) ≤ VT Y q := hTbad q hq Y hYX hY
        _ ≤ VD Y q + VT Y q := le_add_left le_rfl
        _ ≤ V q := by
          dsimp only [V]
          exact Finset.single_le_sum (f := fun Y => VD Y q + VT Y q)
            (fun j _ => by simp) (by simp [hYX])
  have hv := ville_frozen_of_support_invariant
    K (PairModeBad X D) (PairModeInvariant c0 X) V 1
    (by simp) (by simp) hcontain hclosed hsuper
    (pairModeInitial c0) (pairModeInvariant_initial c0 X)
  have hfreeze : freeze (PairModeBad X D) K = K := by
    funext q
    by_cases hb : PairModeBad X D q <;> simp [K, freeze, hb]
  have hv' : productivePairModeEverMass h3 X D c0 ≤ V (pairModeInitial c0) := by
    simpa only [productivePairModeEverMass, hitProb, hfreeze, K, div_one] using hv
  have hV0 : V (pairModeInitial c0) ≤
      ((m - 1 : ℕ) : ℝ≥0∞) * (bD + bT) := by
    calc
      V (pairModeInitial c0) =
          ∑ Y ∈ Finset.univ.erase X,
            (VD Y (pairModeInitial c0) + VT Y (pairModeInitial c0)) := rfl
      _ ≤ ∑ Y ∈ Finset.univ.erase X, (bD + bT) := by
        apply Finset.sum_le_sum
        intro Y hY
        have hYX : Y ≠ X := (Finset.mem_erase.mp hY).1
        exact add_le_add (hDinit Y hYX) (hTinit Y hYX)
      _ = _ := by simp [Species, mul_add]
  exact hv'.trans hV0

end Tri.Multi

namespace Tri.Multi

open scoped BigOperators ENNReal

variable {m n : ℕ}

/-- Natural level for the direct counter measured in units of two. -/
def lemma11DirectOddsLevel (D : ℕ) (z : ℤ) : ℕ :=
  (z / 2 + (((D + 7) / 8 : ℕ) : ℤ) + 2).toNat

noncomputable def lemma11DirectOddsPotential
    (u : ℝ≥0∞) (D : ℕ) (Y : Species m)
    (q : PairModeState m n) : ℝ≥0∞ :=
  u ^ lemma11DirectOddsLevel D (q.2.1 Y)

theorem lemma11DirectOddsLevel_zero (D : ℕ) :
    lemma11DirectOddsLevel D 0 = (D + 7) / 8 + 2 := by
  unfold lemma11DirectOddsLevel
  omega

theorem lemma11DirectOddsLevel_ge_two
    (D : ℕ) (z : ℤ) (hsafe : ¬ 4 * z ≤ -(D : ℤ)) :
    2 ≤ lemma11DirectOddsLevel D z := by
  unfold lemma11DirectOddsLevel
  omega

theorem lemma11DirectOddsLevel_le_two
    (D : ℕ) (z : ℤ) (hbad : 4 * z ≤ -(D : ℤ)) :
    lemma11DirectOddsLevel D z ≤ 2 := by
  unfold lemma11DirectOddsLevel
  omega

/-- The direct counter divided by two has one-unit moves. -/
theorem productivePairModeStep_directOdds_conserve_of_core
    (h3 : 3 ≤ n) (X Y : Species m) (D : ℕ)
    (u : ℝ≥0∞) (hu1 : u ≤ 1)
    (q : PairModeState m n)
    (hg : 2 ≤ lemma11DirectOddsLevel D (q.2.1 Y))
    (hcore :
      pairDeltaMass q.1 h3 X Y (-2) * u +
        (pairDeltaMass q.1 h3 X Y (-1) +
          pairDeltaMass q.1 h3 X Y 0 +
          pairDeltaMass q.1 h3 X Y 1) * u ^ 2 +
        pairDeltaMass q.1 h3 X Y 2 * u ^ 3 ≤ u ^ 2) :
    expect (productivePairModeStep h3 X q)
        (lemma11DirectOddsPotential u D Y) ≤
      lemma11DirectOddsPotential u D Y q := by
  let g := lemma11DirectOddsLevel D (q.2.1 Y)
  let f : ℤ → ℝ≥0∞ := fun j =>
    u ^ lemma11DirectOddsLevel D
      (q.2.1 Y + if j = 2 ∨ j = -2 then j else 0)
  have hm2 : f (-2) = u ^ (g - 1) := by
    dsimp only [f]
    norm_num
    congr 1
    dsimp only [g, lemma11DirectOddsLevel] at *
    omega
  have hm1 : f (-1) = u ^ g := by norm_num [f, g]
  have h0 : f 0 = u ^ g := by norm_num [f, g]
  have h1 : f 1 = u ^ g := by norm_num [f, g]
  have h2 : f 2 = u ^ (g + 1) := by
    dsimp only [f]
    norm_num
    congr 1
    dsimp only [g, lemma11DirectOddsLevel] at *
    omega
  have hraw :
      expect (multiStep q.1 h3)
          (fun c' => lemma11DirectOddsPotential u D Y (pairModeNext X q c')) ≤
        lemma11DirectOddsPotential u D Y q := by
    change expect (multiStep q.1 h3)
      (fun c' => f (pairTransitionDelta q.1 c' X Y)) ≤ u ^ g
    rw [expect_multiStep_pairTransitionDelta, hm2, hm1, h0, h1, h2]
    have h := third_only_geometric_of_core
      (down2 := pairDeltaMass q.1 h3 X Y (-1))
      (down1 := pairDeltaMass q.1 h3 X Y (-2))
      (stay := pairDeltaMass q.1 h3 X Y 0)
      (up1 := pairDeltaMass q.1 h3 X Y 2)
      (up2 := pairDeltaMass q.1 h3 X Y 1)
      (u := u) (g := g) hg hcore
    simpa only [add_mul, add_assoc] using h
  unfold productivePairModeStep
  rw [expect_map]
  have htop : lemma11DirectOddsPotential u D Y q ≠ ⊤ :=
    ENNReal.pow_ne_top (ne_top_of_le_ne_top ENNReal.one_ne_top hu1)
  have hraw' :
      expect (multiStep q.1 h3)
          (fun c' => lemma11DirectOddsPotential u D Y (pairModeNext X q c')) ≤
        lemma11DirectOddsPotential u D Y (pairModeNext X q q.1) := by
    simpa only [pairModeNext_self] using hraw
  have hp := productiveStep_conserve_of_multiStep_conserve q.1 h3
    (fun c' => lemma11DirectOddsPotential u D Y (pairModeNext X q c'))
    (by simpa only [pairModeNext_self] using htop) hraw'
  simpa only [pairModeNext_self] using hp

theorem lemma11_expect_div_const
    {α : Type*} (p : PMF α) (V : α → ℝ≥0∞) (θ : ℝ≥0∞) :
    expect p (fun q => V q / θ) = expect p V / θ := by
  unfold expect
  simp only [div_eq_mul_inv, ← mul_assoc]
  exact ENNReal.tsum_mul_right

theorem lemma11_pow_add_two_div
    (u : ℝ≥0∞) (hu0 : u ≠ 0) (hu1 : u ≤ 1) (a : ℕ) :
    u ^ (a + 2) / u ^ 2 = u ^ a := by
  have htop : u ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top hu1
  rw [pow_add, mul_div_assoc,
    ENNReal.div_self (pow_ne_zero _ hu0) (ENNReal.pow_ne_top htop), mul_one]

theorem lemma11_modeSharpOdds_le_one
    (N D : ℕ) (hN : 0 < N) :
    modeSharpOdds N D ≤ 1 := by
  unfold modeSharpOdds
  have hd0 : (((N + D : ℕ) : ℝ≥0∞)) ≠ 0 := by
    exact_mod_cast (by omega : N + D ≠ 0)
  have hdtop : (((N + D : ℕ) : ℝ≥0∞)) ≠ ⊤ :=
    ENNReal.natCast_ne_top _
  calc
    (((N - D : ℕ) : ℝ≥0∞)) / (((N + D : ℕ) : ℝ≥0∞)) ≤
        (((N + D : ℕ) : ℝ≥0∞)) / (((N + D : ℕ) : ℝ≥0∞)) :=
      ENNReal.div_le_div_right
        (by exact_mod_cast (by omega : N - D ≤ N + D)) _
    _ = 1 := ENNReal.div_self hd0 hdtop

theorem lemma11_modeSharpOdds_ne_zero
    (N D : ℕ) (hDN : D < N) :
    modeSharpOdds N D ≠ 0 := by
  unfold modeSharpOdds
  simp only [ne_eq, ENNReal.div_eq_zero_iff, not_or]
  exact ⟨by exact_mod_cast (by omega : N - D ≠ 0),
    ENNReal.natCast_ne_top _⟩

/-- Exact rational union bound: the first line of equation (1). -/
theorem productivePairModeEverMass_le_sharpOdds
    (h3 : 3 ≤ n) (X : Species m)
    (D : ℕ) (hDn : D ≤ n)
    (c0 : Config m n) (hinit : HasPairwiseGap c0 X D) :
    productivePairModeEverMass h3 X D c0 ≤
      ((m - 1 : ℕ) : ℝ≥0∞) *
        (modeSharpOdds (2 * n) D ^ ((D + 7) / 8) +
          modeSharpOdds (4 * n) D ^ ((D + 3) / 4)) := by
  classical
  let uD := modeSharpOdds (2 * n) D
  let uT := modeSharpOdds (4 * n) D
  let aD := (D + 7) / 8
  let aT := (D + 3) / 4
  have huD1 : uD ≤ 1 :=
    lemma11_modeSharpOdds_le_one (2 * n) D (by omega)
  have huT1 : uT ≤ 1 :=
    lemma11_modeSharpOdds_le_one (4 * n) D (by omega)
  have huD0 : uD ≠ 0 :=
    lemma11_modeSharpOdds_ne_zero (2 * n) D (by omega)
  have huT0 : uT ≠ 0 :=
    lemma11_modeSharpOdds_ne_zero (4 * n) D (by omega)
  have huDtop : uD ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top huD1
  have huTtop : uT ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top huT1
  change productivePairModeEverMass h3 X D c0 ≤
    ((m - 1 : ℕ) : ℝ≥0∞) * (uD ^ aD + uT ^ aT)
  refine productivePairModeEverMass_le_of_normalized_potentials
    h3 X D c0 (uD ^ aD) (uT ^ aT)
    (fun Y q => lemma11DirectOddsPotential uD D Y q / uD ^ 2)
    (fun Y q => lemma11ThirdPotential uT D Y q / uT ^ 2)
    ?_ ?_ ?_ ?_ ?_ ?_
  · intro q hq hsafe Y hYX
    have hgap := pairModeInvariant_double_gap_of_not_bad
      c0 X D q hinit hq hsafe
    have hmass :
        pairDeltaMass q.1 h3 X Y (-2) ≤
          pairDeltaMass q.1 h3 X Y 2 * uD := by
      rw [pairDeltaMass_neg_two_eq_directedFireMass q.1 h3 X Y (Ne.symm hYX),
        pairDeltaMass_two_eq_directedFireMass q.1 h3 X Y (Ne.symm hYX)]
      exact reverse_directedFireMass_le_modeSharpOdds
        q.1 h3 X Y (Ne.symm hYX) D hDn (hgap Y hYX)
    have hsum :
        pairDeltaMass q.1 h3 X Y (-1) +
          pairDeltaMass q.1 h3 X Y (-2) +
          pairDeltaMass q.1 h3 X Y 0 +
          pairDeltaMass q.1 h3 X Y 2 +
          pairDeltaMass q.1 h3 X Y 1 = 1 := by
      simpa only [add_assoc, add_comm, add_left_comm] using
        pairDeltaMass_five_sum q.1 h3 X Y
    have hcore := third_only_five_jump_mgf_core hsum huD1 hmass
    have hg : 2 ≤ lemma11DirectOddsLevel D (q.2.1 Y) :=
      lemma11DirectOddsLevel_ge_two D (q.2.1 Y)
        (fun hb => hsafe (Or.inl ⟨Y, hYX, hb⟩))
    have hstep := productivePairModeStep_directOdds_conserve_of_core
      h3 X Y D uD huD1 q hg hcore
    rw [lemma11_expect_div_const]
    exact ENNReal.div_le_div_right hstep (uD ^ 2)
  · intro q hq hsafe Y hYX
    have hgap := pairModeInvariant_double_gap_of_not_bad
      c0 X D q hinit hq hsafe
    have hmass :
        pairDeltaMass q.1 h3 X Y (-1) ≤
          pairDeltaMass q.1 h3 X Y 1 * uT := by
      rw [pairDeltaMass_neg_one_eq_thirdPartyDownMass_sum q.1 h3 X Y (Ne.symm hYX),
        pairDeltaMass_one_eq_thirdPartyUpMass_sum q.1 h3 X Y (Ne.symm hYX)]
      exact thirdPartyDownMass_sum_le_up_mul_modeSharpOdds
        q.1 h3 X Y (Ne.symm hYX) D hDn hgap
    have hcore := third_only_five_jump_mgf_core
      (pairDeltaMass_five_sum q.1 h3 X Y) huT1 hmass
    have hcounter : ¬ 4 * q.2.2 Y ≤ -(D : ℤ) :=
      fun hb => hsafe (Or.inr ⟨Y, hYX, hb⟩)
    have hg : 2 ≤ lemma11ModeLevel D (q.2.2 Y) := by
      dsimp only [lemma11ModeLevel]
      omega
    have hstep := productivePairModeStep_third_conserve_of_core
      h3 X Y D uT huT1 q hg hcore
    rw [lemma11_expect_div_const]
    exact ENNReal.div_le_div_right hstep (uT ^ 2)
  · intro q _hq Y _hYX hbad
    have hlevel := lemma11DirectOddsLevel_le_two D (q.2.1 Y) hbad
    have hlower : uD ^ 2 ≤ lemma11DirectOddsPotential uD D Y q :=
      pow_le_pow_right_of_le_one' huD1 hlevel
    calc
      (1 : ℝ≥0∞) = uD ^ 2 / uD ^ 2 :=
        (ENNReal.div_self (pow_ne_zero _ huD0)
          (ENNReal.pow_ne_top huDtop)).symm
      _ ≤ lemma11DirectOddsPotential uD D Y q / uD ^ 2 :=
        ENNReal.div_le_div_right hlower _
  · intro q _hq Y _hYX hbad
    have hlevel : lemma11ModeLevel D (q.2.2 Y) ≤ 2 := by
      dsimp only [lemma11ModeLevel]
      omega
    have hlower : uT ^ 2 ≤ lemma11ThirdPotential uT D Y q :=
      pow_le_pow_right_of_le_one' huT1 hlevel
    calc
      (1 : ℝ≥0∞) = uT ^ 2 / uT ^ 2 :=
        (ENNReal.div_self (pow_ne_zero _ huT0)
          (ENNReal.pow_ne_top huTtop)).symm
      _ ≤ lemma11ThirdPotential uT D Y q / uT ^ 2 :=
        ENNReal.div_le_div_right hlower _
  · intro Y _hYX
    change uD ^ lemma11DirectOddsLevel D 0 / uD ^ 2 ≤ uD ^ aD
    rw [lemma11DirectOddsLevel_zero]
    exact (lemma11_pow_add_two_div uD huD0 huD1 aD).le
  · intro Y _hYX
    change uT ^ lemma11ModeLevel D 0 / uT ^ 2 ≤ uT ^ aT
    have hzero : lemma11ModeLevel D 0 = aT + 2 := by
      dsimp only [lemma11ModeLevel, aT]
      omega
    rw [hzero]
    exact (lemma11_pow_add_two_div uT huT0 huT1 aT).le

theorem productivePairModeHitMass_le_sharpOdds
    (h3 : 3 ≤ n) (X : Species m)
    (D : ℕ) (hDn : D ≤ n)
    (T : ℕ) (c0 : Config m n) (hinit : HasPairwiseGap c0 X D) :
    productivePairModeHitMass h3 X D T c0 ≤
      ((m - 1 : ℕ) : ℝ≥0∞) *
        (modeSharpOdds (2 * n) D ^ ((D + 7) / 8) +
          modeSharpOdds (4 * n) D ^ ((D + 3) / 4)) :=
  (productivePairModeHitMass_le_ever h3 X D T c0).trans
    (productivePairModeEverMass_le_sharpOdds h3 X D hDn c0 hinit)

end Tri.Multi

namespace Tri.Multi

open scoped ENNReal

theorem modeSharpOdds_pow_le_exp
    (N D k : ℕ) (hN : 0 < N) (hDN : D ≤ N) :
    modeSharpOdds N D ^ k ≤
      ENNReal.ofReal
        (Real.exp (-((2 : ℝ) * (k : ℝ) * (D : ℝ) / (N : ℝ)))) := by
  have hbase := mode_sharpOdds_le_exp N D hN hDN
  refine (pow_le_pow_left' hbase k).trans_eq ?_
  rw [← ENNReal.ofReal_pow (Real.exp_pos _).le,
    ← Real.exp_nat_mul]
  apply congrArg ENNReal.ofReal
  apply congrArg Real.exp
  ring

theorem modeSharpOdds_two_pow_eighth_le_gaussian
    (n D : ℕ) (hn : 0 < n) (hDN : D ≤ n) :
    modeSharpOdds (2 * n) D ^ ((D + 7) / 8) ≤
      ENNReal.ofReal
        (Real.exp (-((D : ℝ) ^ 2 / (8 * (n : ℝ))))) := by
  let k : ℕ := (D + 7) / 8
  have hDk : D ≤ 8 * k := by dsimp only [k]; omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hDkR : (D : ℝ) ≤ 8 * (k : ℝ) := by exact_mod_cast hDk
  have hnum : (D : ℝ) ^ 2 ≤ 8 * (k : ℝ) * (D : ℝ) := by
    have h := mul_le_mul_of_nonneg_right hDkR
      (Nat.cast_nonneg D : (0 : ℝ) ≤ D)
    nlinarith
  have hbudget :
      (D : ℝ) ^ 2 / (8 * (n : ℝ)) ≤
        (2 : ℝ) * (k : ℝ) * (D : ℝ) / ((2 * n : ℕ) : ℝ) := by
    push_cast
    calc
      (D : ℝ) ^ 2 / (8 * (n : ℝ)) ≤
          (8 * (k : ℝ) * (D : ℝ)) / (8 * (n : ℝ)) :=
        div_le_div_of_nonneg_right hnum (by positivity)
      _ = (2 : ℝ) * (k : ℝ) * (D : ℝ) / (2 * (n : ℝ)) := by
        field_simp [ne_of_gt hnR] <;> ring
  change modeSharpOdds (2 * n) D ^ k ≤ _
  exact
    (modeSharpOdds_pow_le_exp (2 * n) D k (by omega) (by omega)).trans
      (ENNReal.ofReal_le_ofReal
        (Real.exp_le_exp.mpr (neg_le_neg hbudget)))

theorem modeSharpOdds_four_pow_quarter_le_gaussian
    (n D : ℕ) (hn : 0 < n) (hDN : D ≤ n) :
    modeSharpOdds (4 * n) D ^ ((D + 3) / 4) ≤
      ENNReal.ofReal
        (Real.exp (-((D : ℝ) ^ 2 / (8 * (n : ℝ))))) := by
  let k : ℕ := (D + 3) / 4
  have hDk : D ≤ 4 * k := by dsimp only [k]; omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hDkR : (D : ℝ) ≤ 4 * (k : ℝ) := by exact_mod_cast hDk
  have hnum : (D : ℝ) ^ 2 ≤ 4 * (k : ℝ) * (D : ℝ) := by
    have h := mul_le_mul_of_nonneg_right hDkR
      (Nat.cast_nonneg D : (0 : ℝ) ≤ D)
    nlinarith
  have hbudget :
      (D : ℝ) ^ 2 / (8 * (n : ℝ)) ≤
        (2 : ℝ) * (k : ℝ) * (D : ℝ) / ((4 * n : ℕ) : ℝ) := by
    push_cast
    calc
      (D : ℝ) ^ 2 / (8 * (n : ℝ)) ≤
          (4 * (k : ℝ) * (D : ℝ)) / (8 * (n : ℝ)) :=
        div_le_div_of_nonneg_right hnum (by positivity)
      _ = (2 : ℝ) * (k : ℝ) * (D : ℝ) / (4 * (n : ℝ)) := by
        field_simp [ne_of_gt hnR] <;> ring
  change modeSharpOdds (4 * n) D ^ k ≤ _
  exact
    (modeSharpOdds_pow_le_exp (4 * n) D k (by omega) (by omega)).trans
      (ENNReal.ofReal_le_ofReal
        (Real.exp_le_exp.mpr (neg_le_neg hbudget)))

/-- Use both the exponential bound and the probability ceiling. -/
theorem lemma11_probability_ceiling
    (m : ℕ) (p q : ℝ≥0∞)
    (hp1 : p ≤ 1)
    (hp : p ≤ 2 * ((m - 1 : ℕ) : ℝ≥0∞) * q ^ 2) :
    p ≤ (m : ℝ≥0∞) * q := by
  have hcoefNat : 2 * (m - 1) ≤ m ^ 2 := by
    cases m with
    | zero => norm_num
    | succ k =>
        simp only [Nat.succ_sub_one, Nat.succ_eq_add_one]
        nlinarith
  have hcoef : 2 * ((m - 1 : ℕ) : ℝ≥0∞) ≤ (m : ℝ≥0∞) ^ 2 := by
    exact_mod_cast hcoefNat
  by_cases hB : 1 ≤ (m : ℝ≥0∞) * q
  · exact hp1.trans hB
  · have hB1 : (m : ℝ≥0∞) * q ≤ 1 := le_of_lt (lt_of_not_ge hB)
    calc
      p ≤ 2 * ((m - 1 : ℕ) : ℝ≥0∞) * q ^ 2 := hp
      _ ≤ (m : ℝ≥0∞) ^ 2 * q ^ 2 := mul_le_mul_right' hcoef _
      _ = ((m : ℝ≥0∞) * q) ^ 2 := (mul_pow _ _ _).symm
      _ ≤ (m : ℝ≥0∞) * q := by
        rw [pow_two]
        simpa only [one_mul] using
          mul_le_mul_right' hB1 ((m : ℝ≥0∞) * q)

theorem lemma11_gaussian16_of_gaussian8
    (m n D : ℕ) (hn : 0 < n) (p : ℝ≥0∞)
    (hp1 : p ≤ 1)
    (hp : p ≤ 2 * ((m - 1 : ℕ) : ℝ≥0∞) *
      ENNReal.ofReal (Real.exp (-((D : ℝ) ^ 2 / (8 * (n : ℝ)))))) :
    p ≤ (m : ℝ≥0∞) *
      ENNReal.ofReal (Real.exp (-((D : ℝ) ^ 2 / (16 * (n : ℝ))))) := by
  let q : ℝ≥0∞ :=
    ENNReal.ofReal (Real.exp (-((D : ℝ) ^ 2 / (16 * (n : ℝ)))))
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hq :
      ENNReal.ofReal (Real.exp (-((D : ℝ) ^ 2 / (8 * (n : ℝ))))) = q ^ 2 := by
    dsimp only [q]
    rw [← ENNReal.ofReal_pow (le_of_lt (Real.exp_pos _))]
    congr 1
    rw [← Real.exp_nat_mul]
    congr 1
    field_simp [hn0] <;> ring
  apply lemma11_probability_ceiling m p q hp1
  simpa only [hq] using hp

theorem lemma11_gaussian18_of_gaussian8
    (m n D : ℕ) (hn : 0 < n) (p : ℝ≥0∞)
    (hp1 : p ≤ 1)
    (hp : p ≤ 2 * ((m - 1 : ℕ) : ℝ≥0∞) *
      ENNReal.ofReal (Real.exp (-((D : ℝ) ^ 2 / (8 * (n : ℝ)))))) :
    p ≤ (m : ℝ≥0∞) *
      ENNReal.ofReal (Real.exp (-((D : ℝ) ^ 2 / (18 * (n : ℝ))))) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hratio :
      (D : ℝ) ^ 2 / (18 * (n : ℝ)) ≤
        (D : ℝ) ^ 2 / (16 * (n : ℝ)) :=
    div_le_div_of_nonneg_left (sq_nonneg (D : ℝ))
      (by positivity : 0 < 16 * (n : ℝ)) (by nlinarith)
  exact (lemma11_gaussian16_of_gaussian8 m n D hn p hp1 hp).trans
    (mul_le_mul_left'
      (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (neg_le_neg hratio))) _)

end Tri.Multi

namespace Tri.Multi

open scoped ENNReal

variable {m n : ℕ}

/-- Gaussian form of equation (1), for the unrestricted union event. -/
theorem productivePairModeEverMass_le_exp8
    (h3 : 3 ≤ n) (X : Species m)
    (D : ℕ) (hDn : D ≤ n)
    (c0 : Config m n) (hinit : HasPairwiseGap c0 X D) :
    productivePairModeEverMass h3 X D c0 ≤
      2 * ((m - 1 : ℕ) : ℝ≥0∞) *
        ENNReal.ofReal
          (Real.exp (-((D : ℝ) ^ 2 / (8 * (n : ℝ))))) := by
  have hD := modeSharpOdds_two_pow_eighth_le_gaussian n D (by omega) hDn
  have hT := modeSharpOdds_four_pow_quarter_le_gaussian n D (by omega) hDn
  calc
    productivePairModeEverMass h3 X D c0 ≤
        ((m - 1 : ℕ) : ℝ≥0∞) *
          (modeSharpOdds (2 * n) D ^ ((D + 7) / 8) +
            modeSharpOdds (4 * n) D ^ ((D + 3) / 4)) :=
      productivePairModeEverMass_le_sharpOdds h3 X D hDn c0 hinit
    _ ≤ ((m - 1 : ℕ) : ℝ≥0∞) *
          (ENNReal.ofReal (Real.exp (-((D : ℝ) ^ 2 / (8 * (n : ℝ))))) +
            ENNReal.ofReal (Real.exp (-((D : ℝ) ^ 2 / (8 * (n : ℝ)))))) :=
      mul_le_mul_left' (add_le_add hD hT) _
    _ = _ := by ring

theorem productivePairModeHitMass_le_exp8
    (h3 : 3 ≤ n) (X : Species m)
    (D : ℕ) (hDn : D ≤ n)
    (T : ℕ) (c0 : Config m n) (hinit : HasPairwiseGap c0 X D) :
    productivePairModeHitMass h3 X D T c0 ≤
      2 * ((m - 1 : ℕ) : ℝ≥0∞) *
        ENNReal.ofReal
          (Real.exp (-((D : ℝ) ^ 2 / (8 * (n : ℝ))))) :=
  (productivePairModeHitMass_le_ever h3 X D T c0).trans
    (productivePairModeEverMass_le_exp8 h3 X D hDn c0 hinit)

/-- Equation (2), with the stronger constant 1/16, already for the union. -/
theorem productivePairModeEverMass_le_exp16
    (h3 : 3 ≤ n) (X : Species m)
    (D : ℕ) (hDn : D ≤ n)
    (c0 : Config m n) (hinit : HasPairwiseGap c0 X D) :
    productivePairModeEverMass h3 X D c0 ≤
      (m : ℝ≥0∞) *
        ENNReal.ofReal
          (Real.exp (-((D : ℝ) ^ 2 / (16 * (n : ℝ))))) :=
  lemma11_gaussian16_of_gaussian8 m n D (by omega)
    (productivePairModeEverMass h3 X D c0)
    (productivePairModeEverMass_le_one h3 X D c0)
    (productivePairModeEverMass_le_exp8 h3 X D hDn c0 hinit)

theorem productivePairModeHitMass_le_exp16
    (h3 : 3 ≤ n) (X : Species m)
    (D : ℕ) (hDn : D ≤ n)
    (T : ℕ) (c0 : Config m n) (hinit : HasPairwiseGap c0 X D) :
    productivePairModeHitMass h3 X D T c0 ≤
      (m : ℝ≥0∞) *
        ENNReal.ofReal
          (Real.exp (-((D : ℝ) ^ 2 / (16 * (n : ℝ))))) :=
  (productivePairModeHitMass_le_ever h3 X D T c0).trans
    (productivePairModeEverMass_le_exp16 h3 X D hDn c0 hinit)

theorem productivePairModeEverMass_le_exp18
    (h3 : 3 ≤ n) (X : Species m)
    (D : ℕ) (hDn : D ≤ n)
    (c0 : Config m n) (hinit : HasPairwiseGap c0 X D) :
    productivePairModeEverMass h3 X D c0 ≤
      (m : ℝ≥0∞) *
        ENNReal.ofReal
          (Real.exp (-((D : ℝ) ^ 2 / (18 * (n : ℝ))))) :=
  lemma11_gaussian18_of_gaussian8 m n D (by omega)
    (productivePairModeEverMass h3 X D c0)
    (productivePairModeEverMass_le_one h3 X D c0)
    (productivePairModeEverMass_le_exp8 h3 X D hDn c0 hinit)

theorem productivePairModeHitMass_le_exp18
    (h3 : 3 ≤ n) (X : Species m)
    (D : ℕ) (hDn : D ≤ n)
    (T : ℕ) (c0 : Config m n) (hinit : HasPairwiseGap c0 X D) :
    productivePairModeHitMass h3 X D T c0 ≤
      (m : ℝ≥0∞) *
        ENNReal.ofReal
          (Real.exp (-((D : ℝ) ^ 2 / (18 * (n : ℝ))))) :=
  (productivePairModeHitMass_le_ever h3 X D T c0).trans
    (productivePairModeEverMass_le_exp18 h3 X D hDn c0 hinit)

/-- Unbounded direct-mode bound on the original, unrestricted chain. -/
theorem productiveDirectModeEverMass_le_exp16
    (h3 : 3 ≤ n) (X : Species m)
    (D : ℕ) (hDn : D ≤ n)
    (c0 : Config m n) (hinit : HasPairwiseGap c0 X D) :
    productiveDirectModeEverMass h3 X D c0 ≤
      (m : ℝ≥0∞) *
        ENNReal.ofReal
          (Real.exp (-((D : ℝ) ^ 2 / (16 * (n : ℝ))))) :=
  (productiveDirectModeEverMass_le_pair h3 X D c0).trans
    (productivePairModeEverMass_le_exp16 h3 X D hDn c0 hinit)

/-- Finite-horizon direct-mode bound, uniformly in the horizon. -/
theorem productiveDirectModeHitMass_le_exp16
    (h3 : 3 ≤ n) (X : Species m)
    (D : ℕ) (hDn : D ≤ n)
    (T : ℕ) (c0 : Config m n) (hinit : HasPairwiseGap c0 X D) :
    productiveDirectModeHitMass h3 X D T c0 ≤
      (m : ℝ≥0∞) *
        ENNReal.ofReal
          (Real.exp (-((D : ℝ) ^ 2 / (16 * (n : ℝ))))) :=
  (productiveDirectModeHitMass_le_ever h3 X D T c0).trans
    (productiveDirectModeEverMass_le_exp16 h3 X D hDn c0 hinit)

/-- Unbounded third-party-mode bound on the original, unrestricted chain. -/
theorem productiveThirdPartyModeEverMass_le_exp16
    (h3 : 3 ≤ n) (X : Species m)
    (D : ℕ) (hDn : D ≤ n)
    (c0 : Config m n) (hinit : HasPairwiseGap c0 X D) :
    productiveThirdPartyModeEverMass h3 X D c0 ≤
      (m : ℝ≥0∞) *
        ENNReal.ofReal
          (Real.exp (-((D : ℝ) ^ 2 / (16 * (n : ℝ))))) :=
  (productiveThirdPartyModeEverMass_le_pair h3 X D c0).trans
    (productivePairModeEverMass_le_exp16 h3 X D hDn c0 hinit)

/-- Finite-horizon third-party-mode bound, uniformly in the horizon. -/
theorem productiveThirdPartyModeHitMass_le_exp16
    (h3 : 3 ≤ n) (X : Species m)
    (D : ℕ) (hDn : D ≤ n)
    (T : ℕ) (c0 : Config m n) (hinit : HasPairwiseGap c0 X D) :
    productiveThirdPartyModeHitMass h3 X D T c0 ≤
      (m : ℝ≥0∞) *
        ENNReal.ofReal
          (Real.exp (-((D : ℝ) ^ 2 / (16 * (n : ℝ))))) :=
  (productiveThirdPartyModeHitMass_le_ever h3 X D T c0).trans
    (productiveThirdPartyModeEverMass_le_exp16 h3 X D hDn c0 hinit)

theorem productiveDirectModeEverMass_le_exp18
    (h3 : 3 ≤ n) (X : Species m)
    (D : ℕ) (hDn : D ≤ n)
    (c0 : Config m n) (hinit : HasPairwiseGap c0 X D) :
    productiveDirectModeEverMass h3 X D c0 ≤
      (m : ℝ≥0∞) *
        ENNReal.ofReal
          (Real.exp (-((D : ℝ) ^ 2 / (18 * (n : ℝ))))) :=
  (productiveDirectModeEverMass_le_pair h3 X D c0).trans
    (productivePairModeEverMass_le_exp18 h3 X D hDn c0 hinit)

theorem productiveDirectModeHitMass_le_exp18
    (h3 : 3 ≤ n) (X : Species m)
    (D : ℕ) (hDn : D ≤ n)
    (T : ℕ) (c0 : Config m n) (hinit : HasPairwiseGap c0 X D) :
    productiveDirectModeHitMass h3 X D T c0 ≤
      (m : ℝ≥0∞) *
        ENNReal.ofReal
          (Real.exp (-((D : ℝ) ^ 2 / (18 * (n : ℝ))))) :=
  (productiveDirectModeHitMass_le_ever h3 X D T c0).trans
    (productiveDirectModeEverMass_le_exp18 h3 X D hDn c0 hinit)

theorem productiveThirdPartyModeEverMass_le_exp18
    (h3 : 3 ≤ n) (X : Species m)
    (D : ℕ) (hDn : D ≤ n)
    (c0 : Config m n) (hinit : HasPairwiseGap c0 X D) :
    productiveThirdPartyModeEverMass h3 X D c0 ≤
      (m : ℝ≥0∞) *
        ENNReal.ofReal
          (Real.exp (-((D : ℝ) ^ 2 / (18 * (n : ℝ))))) :=
  (productiveThirdPartyModeEverMass_le_pair h3 X D c0).trans
    (productivePairModeEverMass_le_exp18 h3 X D hDn c0 hinit)

theorem productiveThirdPartyModeHitMass_le_exp18
    (h3 : 3 ≤ n) (X : Species m)
    (D : ℕ) (hDn : D ≤ n)
    (T : ℕ) (c0 : Config m n) (hinit : HasPairwiseGap c0 X D) :
    productiveThirdPartyModeHitMass h3 X D T c0 ≤
      (m : ℝ≥0∞) *
        ENNReal.ofReal
          (Real.exp (-((D : ℝ) ^ 2 / (18 * (n : ℝ))))) :=
  (productiveThirdPartyModeHitMass_le_ever h3 X D T c0).trans
    (productiveThirdPartyModeEverMass_le_exp18 h3 X D hDn c0 hinit)

/-- Corrected paper wrapper: the cumulative direct-mode event. -/
theorem lemma11_twoPartyBacksliding_modes
    (h3 : 3 ≤ n) (X : Species m)
    (D : ℕ) (_hD4 : 4 ≤ D) (hDn : D ≤ n)
    (c0 : Config m n) (hinit : HasPairwiseGap c0 X D) :
    productiveDirectModeEverMass h3 X D c0 ≤
      (m : ℝ≥0∞) *
        ENNReal.ofReal
          (Real.exp (-((D : ℝ) ^ 2 / (18 * (n : ℝ))))) :=
  productiveDirectModeEverMass_le_exp18 h3 X D hDn c0 hinit

/-- Corrected paper wrapper: the cumulative third-party-mode event. -/
theorem lemma11_thirdPartyBacksliding_modes
    (h3 : 3 ≤ n) (X : Species m)
    (D : ℕ) (_hD4 : 4 ≤ D) (hDn : D ≤ n)
    (c0 : Config m n) (hinit : HasPairwiseGap c0 X D) :
    productiveThirdPartyModeEverMass h3 X D c0 ≤
      (m : ℝ≥0∞) *
        ENNReal.ofReal
          (Real.exp (-((D : ℝ) ^ 2 / (18 * (n : ℝ))))) :=
  productiveThirdPartyModeEverMass_le_exp18 h3 X D hDn c0 hinit

/-- Discharge the direct-mode proposition specified in PaperLemma11Modes. -/
theorem lemma11_directModeStatement
    (h3 : 3 ≤ n) (X : Species m) (D : ℕ) (c0 : Config m n) :
    Lemma11DirectModeStatement h3 X D c0 := by
  intro hD4 hDn hinit
  exact lemma11_twoPartyBacksliding_modes h3 X D hD4 hDn c0 hinit

/-- Discharge the third-party proposition specified in PaperLemma11Modes. -/
theorem lemma11_thirdPartyModeStatement
    (h3 : 3 ≤ n) (X : Species m) (D : ℕ) (c0 : Config m n) :
    Lemma11ThirdPartyModeStatement h3 X D c0 := by
  intro hD4 hDn hinit
  exact lemma11_thirdPartyBacksliding_modes h3 X D hD4 hDn c0 hinit

end Tri.Multi

