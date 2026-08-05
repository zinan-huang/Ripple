/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.HeavyBStaged

/-!
# Concrete Heavy-B single-branch band rung

This instantiates the staged Heavy-B phase with the concrete Heavy-B direction
parameters and a level-only productive mass floor.
-/

namespace Tri

open scoped ENNReal

/-- Productive mass floor attached to a Heavy-B level band.  The natural
parameters are witnesses for the lower gap and upper co-level. -/
noncomputable def heavyBandProductivity (n d c : ℕ) : ℝ≥0∞ :=
  (((d * c : ℕ) : ℝ≥0∞) / ((Nat.choose n 2 : ℕ) : ℝ≥0∞))

/-- The level-based Heavy-B productive floor is uniform on the open band. -/
theorem heavyBandProductivity_le
    (n : ℕ) (hn : 3 ≤ n) (aLo hi thr d c : ℕ)
    (hthr : thr + 1 = hi)
    (hgap : n + d = 2 * (aLo + 1))
    (hco : thr + c = n)
    (s : HeavyState n)
    (hliveLo : aLo + 1 ≤ BiCfg.heavyLevel s.1)
    (hliveHi : BiCfg.heavyLevel s.1 + 1 ≤ hi) :
    heavyBandProductivity n d c ≤
      dbPairPMF s.1.x s.1.y s.1.b (heavy_two_entities hn s) .xy
        + dbPairPMF s.1.x s.1.y s.1.b (heavy_two_entities hn s) .xb
        + dbPairPMF s.1.x s.1.y s.1.b (heavy_two_entities hn s) .yb := by
  obtain ⟨dL, hdL⟩ : ∃ dL, n + dL = 2 * BiCfg.heavyLevel s.1 :=
    ⟨2 * BiCfg.heavyLevel s.1 - n, by omega⟩
  obtain ⟨cL, hcL⟩ : ∃ cL, BiCfg.heavyLevel s.1 + cL = n :=
    ⟨s.1.y + s.1.b, by exact BiCfg.heavyLevel_add_coLevel s.2⟩
  have hdle : d ≤ dL := by omega
  have hcle : c ≤ cL := by omega
  calc
    heavyBandProductivity n d c ≤
        (((dL * cL : ℕ) : ℝ≥0∞) /
          ((Nat.choose n 2 : ℕ) : ℝ≥0∞)) := by
      unfold heavyBandProductivity
      exact ENNReal.div_le_div_right
        (by exact_mod_cast Nat.mul_le_mul hdle hcle) _
    _ ≤ dbPairPMF s.1.x s.1.y s.1.b (heavy_two_entities hn s) .xy
        + dbPairPMF s.1.x s.1.y s.1.b (heavy_two_entities hn s) .xb
        + dbPairPMF s.1.x s.1.y s.1.b (heavy_two_entities hn s) .yb :=
      heavyProductive_mass_level_ge hn s dL cL hdL hcL

/-- The concrete band productive floor is a probability. -/
theorem heavyBandProductivity_le_one
    (n : ℕ) (hn : 3 ≤ n) (aLo thr d c : ℕ)
    (hgap : n + d = 2 * (aLo + 1))
    (hco : thr + c = n)
    (hwidth : aLo + 1 ≤ thr) :
    heavyBandProductivity n d c ≤ 1 := by
  have hdc : d + 2 * c ≤ n := by omega
  have hS : ((d : ℝ) + 2 * (c : ℝ)) ≤ (n : ℝ) := by
    exact_mod_cast hdc
  have hSnonneg : 0 ≤ (d : ℝ) + 2 * (c : ℝ) := by positivity
  have hnnonneg : 0 ≤ (n : ℝ) := by positivity
  have hSsq : ((d : ℝ) + 2 * (c : ℝ)) ^ 2 ≤ (n : ℝ) ^ 2 := by
    rw [sq_le_sq]
    rw [abs_of_nonneg hSnonneg, abs_of_nonneg hnnonneg]
    exact hS
  have h8 : 8 * (d : ℝ) * (c : ℝ)
      ≤ ((d : ℝ) + 2 * (c : ℝ)) ^ 2 := by
    nlinarith [sq_nonneg ((d : ℝ) - 2 * (c : ℝ))]
  have hn4 : (n : ℝ) ^ 2 ≤ 4 * (n : ℝ) * ((n : ℝ) - 1) := by
    have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  have hmulR : 2 * (d : ℝ) * (c : ℝ)
      ≤ (n : ℝ) * ((n : ℝ) - 1) := by
    nlinarith
  have hmulR' : ((2 * (d * c) : ℕ) : ℝ)
      ≤ ((n * (n - 1) : ℕ) : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_mul,
      Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
    simpa [mul_assoc] using hmulR
  have hmul2 : 2 * (d * c) ≤ n * (n - 1) := by
    exact_mod_cast hmulR'
  have hchoose : 2 * Nat.choose n 2 = n * (n - 1) := by
    have h := two_mul_choose_two_succ (n - 1)
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ n)] using h
  have hmul : d * c ≤ Nat.choose n 2 := by omega
  have hden0 : ((Nat.choose n 2 : ℕ) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega : 2 ≤ n)).ne'
  have hdenT : ((Nat.choose n 2 : ℕ) : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.natCast_ne_top _
  calc
    heavyBandProductivity n d c ≤
        ((Nat.choose n 2 : ℕ) : ℝ≥0∞) /
          ((Nat.choose n 2 : ℕ) : ℝ≥0∞) := by
      unfold heavyBandProductivity
      exact ENNReal.div_le_div_right (by exact_mod_cast hmul) _
    _ = 1 := ENNReal.div_self hden0 hdenT

/-- The explicit error of one concrete Heavy-B band rung. -/
noncomputable def heavyBandRungError
    (n a B aLo bHiR thr k M K T returnLo bHiRet kRet d c : ℕ) :
    ℝ≥0∞ :=
  let w : ℝ≥0∞ := ENNReal.ofReal (heavyBandW a B)
  let η : ℝ≥0∞ := ENNReal.ofReal (heavyBandEta a B)
  let pp : ℝ≥0∞ := heavyBandProductivity n d c
  ((((bHiR : ℝ≥0∞) / (aLo : ℝ≥0∞)) ^ k
      + w ^ (aLo + k) / (w ^ thr * η ^ M)
      + ((1 - pp) + pp * ((1 : ℝ≥0∞) / 2)) ^ T /
          ((1 : ℝ≥0∞) / 2) ^ K)
    + ((bHiRet : ℝ≥0∞) / (returnLo : ℝ≥0∞)) ^ kRet)

/-- One fully instantiated Heavy-B single-branch band rung. -/
theorem heavyBandRung
    (n : ℕ) (hn : 3 ≤ n)
    (a B : ℕ)
    (ha : 0 < a) (hB : 0 < B)
    (hparam : a + 2 * B = n)
    (aLo bHiR hi thr k M K T cL d c : ℕ)
    (_hquarter : 4 * B ≤ n)
    (hfloorGuard : n + 2 * B ≤ 2 * (aLo + 1))
    (haLohi : aLo < hi)
    (hthr : thr + 1 = hi)
    (hwidth : aLo + 1 ≤ thr)
    (hstartCo : aLo + k + cL = n)
    (hK : K = cL + 3 * M)
    (hpopR : aLo + bHiR + 2 = n)
    (haLo : 0 < aLo) (hbHiR : 0 < bHiR)
    (hmajR : bHiR ≤ aLo)
    (hgapProd : n + d = 2 * (aLo + 1))
    (hcoProd : thr + c = n)
    (returnLo bHiRet kRet : ℕ)
    (hpopRet : returnLo + bHiRet + 2 = n)
    (hreturnLo : 0 < returnLo) (hbHiRet : 0 < bHiRet)
    (hmajRet : bHiRet ≤ returnLo)
    (hlowerTarget : aLo < returnLo + 1)
    (htargetHi : returnLo + 1 ≤ hi)
    (hreturnGap : returnLo + kRet ≤ hi) :
    Reaches (heavyStateStep n) T
      (fun s => aLo + k ≤ BiCfg.heavyLevel s.1)
      (fun s => returnLo + 1 ≤ BiCfg.heavyLevel s.1)
      (heavyBandRungError n a B aLo bHiR thr k M K T
        returnLo bHiRet kRet d c) := by
  let w : ℝ≥0∞ := ENNReal.ofReal (heavyBandW a B)
  let η : ℝ≥0∞ := ENNReal.ofReal (heavyBandEta a B)
  let u : ℝ≥0∞ := (a : ℝ≥0∞) / ((a + 4 * B : ℕ) : ℝ≥0∞)
  let pp : ℝ≥0∞ := heavyBandProductivity n d c
  have hparams := heavyBand_params_enn ha hB hparam
  dsimp only at hparams
  rcases hparams with ⟨hrel, hwη, hw1, hw0, hη1, hηt, _hwt⟩
  have hq : a + 4 * B ≠ 0 := by omega
  have hguard : ∀ s : HeavyTrace n,
      aLo + 1 ≤ BiCfg.heavyLevel s.cfg.1 →
      BiCfg.heavyLevel s.cfg.1 + 1 ≤ hi →
      (a + 4 * B) * s.cfg.1.y ≤ a * s.cfg.1.x := by
    intro s hlive _
    exact heavyBand_window_guard_params hparam hfloorGuard s hlive
  have hpp1 : pp ≤ 1 :=
    heavyBandProductivity_le_one n hn aLo thr d c hgapProd hcoProd hwidth
  have hBprod : ∀ q : HeavyTrace n,
      aLo + 1 ≤ BiCfg.heavyLevel q.cfg.1 →
      BiCfg.heavyLevel q.cfg.1 + 1 ≤ hi →
      pp ≤ dbPairPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b
            (heavy_two_entities hn q.cfg) .xy
          + dbPairPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b
            (heavy_two_entities hn q.cfg) .xb
          + dbPairPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b
            (heavy_two_entities hn q.cfg) .yb := by
    intro q hlo hhi
    exact heavyBandProductivity_le n hn aLo hi thr d c hthr hgapProd
      hcoProd q.cfg hlo hhi
  have hr := heavyState_band_phase_reaches_mono hn
    aLo bHiR hi thr k M K T cL haLohi hthr hstartCo hK
    hpopR haLo hbHiR hmajR
    a (a + 4 * B) hq hguard w η u rfl hrel hwη hw1 hw0 hη1 hηt
    pp hpp1 hBprod
    returnLo bHiRet kRet hpopRet hreturnLo hbHiRet hmajRet
    hlowerTarget htargetHi hreturnGap
  simpa only [heavyBandRungError, w, η, pp] using hr

example :
    Reaches (heavyStateStep 100) 5
      (fun s => 72 ≤ BiCfg.heavyLevel s.1)
      (fun s => 81 ≤ BiCfg.heavyLevel s.1)
      (heavyBandRungError 100 60 20 70 28 84 2 1 31 5
        80 18 5 42 16) := by
  exact heavyBandRung 100 (by norm_num)
    60 20
    (by norm_num) (by norm_num)
    (by norm_num)
    70 28 85 84 2 1 31 5 28 42 16
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    80 18 5
    (by norm_num)
    (by norm_num) (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)

end Tri

#print axioms Tri.heavyBandProductivity_le
#print axioms Tri.heavyBandProductivity_le_one
#print axioms Tri.heavyBandRung
