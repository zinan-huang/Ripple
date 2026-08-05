/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.DoubleBInvariant
import Tri.Decay

/-!
# The Double-B resolution masses and odds domination (Theorem 2)

At an invariant state the two level-changing (resolution) reactions carry masses
`x·b / C(n,2)` (up) and `y·b / C(n,2)` (down).  The key quantitative input to the
Theorem-2 direction argument is that, in the `X`-majority regime, the Double-B
up-fraction `x/(x+y)` dominates the tri-molecular productive up-fraction at
effective population `2n`, level `2x+b`.  Written cross-free this is
`(a/(a+d))·mass ≤ up` with `a = doubleLevel−1`, `d = doubleCoLevel−1`; it reduces
to the integer fact `(b−1)(x−y) ≥ 0`.
-/

namespace Tri

open scoped ENNReal

/-- Resolution-up mass at an invariant Double-B state: `x·b / C(n,2)`. -/
noncomputable def doubleResolveUp {n : ℕ} (s : DoubleState n) : ℝ≥0∞ :=
  ((s.1.x * s.1.b : ℕ) : ℝ≥0∞) / (Nat.choose n 2 : ℝ≥0∞)

/-- Resolution-down mass: `y·b / C(n,2)`. -/
noncomputable def doubleResolveDown {n : ℕ} (s : DoubleState n) : ℝ≥0∞ :=
  ((s.1.y * s.1.b : ℕ) : ℝ≥0∞) / (Nat.choose n 2 : ℝ≥0∞)

/-- Total resolution mass. -/
noncomputable def doubleResolveMass {n : ℕ} (s : DoubleState n) : ℝ≥0∞ :=
  doubleResolveUp s + doubleResolveDown s

/-- **Odds domination.**  In the `X`-majority regime the Double-B resolution
up-fraction `a/(a+d)` (the tri productive up-fraction at effective population
`2n`, level `2x+b = a+1`) times the total resolution mass is at most the up
mass.  Reduces to `(b−1)(x−y) ≥ 0`. -/
theorem doubleResolve_up_lower {n a d : ℕ} (hn : 2 ≤ n) (s : DoubleState n)
    (hL : s.1.doubleLevel = a + 1) (hR : s.1.doubleCoLevel = d + 1) (hmajor : d ≤ a) :
    ((a : ℝ≥0∞) / (a + d : ℝ≥0∞)) * doubleResolveMass s ≤ doubleResolveUp s := by
  have hLx : 2 * s.1.x + s.1.b = a + 1 := by simpa [BiCfg.doubleLevel] using hL
  have hRy : 2 * s.1.y + s.1.b = d + 1 := by simpa [BiCfg.doubleCoLevel] using hR
  have hpart := doubleLevel_add_doubleCoLevel s
  rw [hL, hR] at hpart
  have had : 0 < a + d := by omega
  have haddne : ((a : ℝ≥0∞) + (d : ℝ≥0∞)) ≠ 0 := by
    have : (0 : ℝ≥0∞) < (a : ℝ≥0∞) + (d : ℝ≥0∞) := by rw [← Nat.cast_add]; exact_mod_cast had
    exact this.ne'
  have haddtop : ((a : ℝ≥0∞) + (d : ℝ≥0∞)) ≠ ⊤ := by
    rw [← Nat.cast_add]; exact ENNReal.natCast_ne_top _
  have hmass : doubleResolveMass s
      = ((s.1.x * s.1.b + s.1.y * s.1.b : ℕ) : ℝ≥0∞) / (Nat.choose n 2 : ℝ≥0∞) := by
    unfold doubleResolveMass doubleResolveUp doubleResolveDown
    rw [ENNReal.div_add_div_same]; norm_cast
  rw [hmass, doubleResolveUp, ← mul_div_assoc]
  apply ENNReal.div_le_div_right
  rw [mul_comm, ← mul_div_assoc, ENNReal.div_le_iff_le_mul (Or.inl haddne) (Or.inl haddtop),
    ← Nat.cast_add]
  norm_cast
  have hyx : s.1.y ≤ s.1.x := by omega
  have hLxZ : 2 * (s.1.x : ℤ) + (s.1.b : ℤ) = (a : ℤ) + 1 := by exact_mod_cast hLx
  have hRyZ : 2 * (s.1.y : ℤ) + (s.1.b : ℤ) = (d : ℤ) + 1 := by exact_mod_cast hRy
  have hbb : (0 : ℤ) ≤ (s.1.b : ℤ) * ((s.1.b : ℤ) - 1) := by
    rcases Nat.eq_zero_or_pos s.1.b with h | h
    · simp [h]
    · have : (1 : ℤ) ≤ (s.1.b : ℤ) := by exact_mod_cast h
      nlinarith [this]
  have H : (0 : ℤ) ≤ (s.1.b : ℤ) * ((s.1.b : ℤ) - 1) * ((s.1.x : ℤ) - (s.1.y : ℤ)) :=
    mul_nonneg hbb (sub_nonneg.mpr (by exact_mod_cast hyx))
  have ha : (a : ℤ) = 2 * (s.1.x : ℤ) + (s.1.b : ℤ) - 1 := by linarith [hLxZ]
  have hd : (d : ℤ) = 2 * (s.1.y : ℤ) + (s.1.b : ℤ) - 1 := by linarith [hRyZ]
  zify
  rw [ha, hd]
  nlinarith [H]

/-! ## Per-label effective-level after one reaction (level `= a+1`) -/

/-- `xb` (up) sends level `a+1` to `a+2` when it can fire. -/
theorem nextDS_level_xb (n : ℕ) (s : DoubleState n) (a : ℕ) (ha : s.1.doubleLevel = a + 1)
    (hw : s.1.x * s.1.b ≠ 0) : (PairComp.nextDoubleState s PairComp.xb).1.doubleLevel = a + 2 := by
  have hb : 0 < s.1.b := Nat.pos_of_ne_zero (fun h => hw (by simp [h]))
  rw [PairComp.nextDoubleState, dif_neg (by simpa [PairComp.weight] using hw)]
  simp only [PairComp.next, BiCfg.doubleLevel] at ha ⊢; omega

/-- `yb` (down) sends level `a+1` to `a` when it can fire. -/
theorem nextDS_level_yb (n : ℕ) (s : DoubleState n) (a : ℕ) (ha : s.1.doubleLevel = a + 1)
    (hw : s.1.y * s.1.b ≠ 0) : (PairComp.nextDoubleState s PairComp.yb).1.doubleLevel + 1 = a + 1 := by
  have hb : 0 < s.1.b := Nat.pos_of_ne_zero (fun h => hw (by simp [h]))
  rw [PairComp.nextDoubleState, dif_neg (by simpa [PairComp.weight] using hw)]
  simp only [PairComp.next, BiCfg.doubleLevel] at ha ⊢; omega

/-- `xy` (neutral) keeps level `a+1`. -/
theorem nextDS_level_xy (n : ℕ) (s : DoubleState n) (a : ℕ) (ha : s.1.doubleLevel = a + 1) :
    (PairComp.nextDoubleState s PairComp.xy).1.doubleLevel = a + 1 := by
  rw [PairComp.nextDoubleState]
  by_cases hw : PairComp.weight s.1.x s.1.y s.1.b PairComp.xy = 0
  · rw [dif_pos hw]; simp only [BiCfg.doubleLevel] at ha ⊢; omega
  · rw [dif_neg hw]
    have hx : 0 < s.1.x := Nat.pos_of_ne_zero (fun h => hw (by simp [PairComp.weight, h]))
    simp only [PairComp.next, BiCfg.doubleLevel] at ha ⊢; omega

/-- The inert reactions keep level `a+1`. -/
theorem nextDS_level_inert (n : ℕ) (s : DoubleState n) (a : ℕ) (ha : s.1.doubleLevel = a + 1)
    (k : PairComp) (hk : k = .xx ∨ k = .yy ∨ k = .bb) :
    (PairComp.nextDoubleState s k).1.doubleLevel = a + 1 := by
  rw [PairComp.nextDoubleState]
  by_cases hw : PairComp.weight s.1.x s.1.y s.1.b k = 0
  · rw [dif_pos hw]; rw [ha]
  · rw [dif_neg hw]; rcases hk with h|h|h <;> subst h <;>
      simp only [PairComp.next, BiCfg.doubleLevel] at ha ⊢ <;> omega

/-- The total mass of the neutral reactions (`xy`, `xx`, `yy`, `bb`). -/
noncomputable def doubleNeutralMass {n : ℕ} (hn : 2 ≤ n) (s : DoubleState n) : ℝ≥0∞ :=
  let h : 2 ≤ s.1.x + s.1.y + s.1.b := by have := s.2; simp only [BiCfg.DoubleInv] at this; omega
  dbPairPMF s.1.x s.1.y s.1.b h .xy + dbPairPMF s.1.x s.1.y s.1.b h .xx
    + dbPairPMF s.1.x s.1.y s.1.b h .yy + dbPairPMF s.1.x s.1.y s.1.b h .bb

/-- **The 6-label expectation expansion.**  Against any level potential, one
Double-B step splits into the down/neutral/up masses at levels `a`, `a+1`, `a+2`
(with `doubleLevel = a+1`).  This is the reusable drift identity for the Feller
and direction arguments. -/
theorem doubleStateStep_expect_level (n : ℕ) (hn : 2 ≤ n) (s : DoubleState n) (a : ℕ)
    (ha : s.1.doubleLevel = a + 1) (F : ℕ → ℝ≥0∞) :
    expect (doubleStateStep n hn s) (fun z => F z.1.doubleLevel)
      = doubleResolveDown s * F a + doubleNeutralMass hn s * F (a + 1)
        + doubleResolveUp s * F (a + 2) := by
  have hh : 2 ≤ s.1.x + s.1.y + s.1.b := by have := s.2; simp only [BiCfg.DoubleInv] at this; omega
  have hpop : s.1.x + s.1.y + s.1.b = n := s.2
  have hup : dbPairPMF s.1.x s.1.y s.1.b hh .xb = doubleResolveUp s := by
    unfold doubleResolveUp
    rw [show dbPairPMF s.1.x s.1.y s.1.b hh PairComp.xb
        = ((PairComp.weight s.1.x s.1.y s.1.b PairComp.xb : ℕ):ℝ≥0∞)
          /(Nat.choose (s.1.x+s.1.y+s.1.b) 2:ℝ≥0∞) from rfl, hpop]
    simp [PairComp.weight]
  have hdown : dbPairPMF s.1.x s.1.y s.1.b hh .yb = doubleResolveDown s := by
    unfold doubleResolveDown
    rw [show dbPairPMF s.1.x s.1.y s.1.b hh PairComp.yb
        = ((PairComp.weight s.1.x s.1.y s.1.b PairComp.yb : ℕ):ℝ≥0∞)
          /(Nat.choose (s.1.x+s.1.y+s.1.b) 2:ℝ≥0∞) from rfl, hpop]
    simp [PairComp.weight]
  have hxbT : dbPairPMF s.1.x s.1.y s.1.b hh .xb * F ((PairComp.nextDoubleState s .xb).1.doubleLevel)
      = doubleResolveUp s * F (a + 2) := by
    by_cases hw : s.1.x * s.1.b = 0
    · rw [dbPairPMF_zero_of_weight_zero (by simpa [PairComp.weight] using hw)]
      have h0 : doubleResolveUp s = 0 := by unfold doubleResolveUp; rw [hw]; simp
      rw [h0]; simp
    · rw [nextDS_level_xb n s a ha hw, hup]
  have hybT : dbPairPMF s.1.x s.1.y s.1.b hh .yb * F ((PairComp.nextDoubleState s .yb).1.doubleLevel)
      = doubleResolveDown s * F a := by
    by_cases hw : s.1.y * s.1.b = 0
    · rw [dbPairPMF_zero_of_weight_zero (by simpa [PairComp.weight] using hw)]
      have h0 : doubleResolveDown s = 0 := by unfold doubleResolveDown; rw [hw]; simp
      rw [h0]; simp
    · have hlev : (PairComp.nextDoubleState s .yb).1.doubleLevel = a := by
        have := nextDS_level_yb n s a ha hw; omega
      rw [hlev, hdown]
  unfold doubleStateStep
  rw [expect_map]; unfold expect; rw [tsum_fintype]; simp only [Function.comp_apply]
  rw [show (Finset.univ : Finset PairComp)
      = {PairComp.xx, PairComp.xy, PairComp.yy, PairComp.xb, PairComp.yb, PairComp.bb} from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [nextDS_level_inert n s a ha .xx (by tauto), nextDS_level_xy n s a ha,
    nextDS_level_inert n s a ha .yy (Or.inr (Or.inl rfl)), hxbT, hybT,
    nextDS_level_inert n s a ha .bb (Or.inr (Or.inr rfl))]
  unfold doubleNeutralMass
  ring

/-- **The Feller reduced condition.**  For masses summing to one with the
resolution bias `down ≤ up·u` and `u ≤ 1`, the geometric drift does not increase:
`down + neutral·u + up·u² ≤ u`.  This is the algebraic heart of the Double-B
safety (Feller) estimate; proved over the reals after `toReal`. -/
theorem feller_reduced (down neutral up u : ℝ≥0∞)
    (hsum : down + neutral + up = 1) (hd : down ≤ up * u) (hu : u ≤ 1)
    (hdt : down ≠ ⊤) (hnt : neutral ≠ ⊤) (hut : up ≠ ⊤) :
    down + neutral * u + up * u ^ 2 ≤ u := by
  have hu1 : u ≠ ⊤ := by intro h; rw [h] at hu; exact absurd hu (by simp)
  rw [← ENNReal.toReal_le_toReal (by finiteness) hu1]
  rw [ENNReal.toReal_add (by finiteness) (by finiteness), ENNReal.toReal_add hdt (by finiteness),
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_pow]
  have hsumR : down.toReal + neutral.toReal + up.toReal = 1 := by
    have := congrArg ENNReal.toReal hsum
    rwa [ENNReal.toReal_add (by finiteness) hut, ENNReal.toReal_add hdt hnt, ENNReal.toReal_one] at this
  have hdR : down.toReal ≤ up.toReal * u.toReal := by
    rw [← ENNReal.toReal_mul]; exact (ENNReal.toReal_le_toReal hdt (by finiteness)).mpr hd
  have huR : u.toReal ≤ 1 := by
    rw [← ENNReal.toReal_one]; exact (ENNReal.toReal_le_toReal hu1 (by simp)).mpr hu
  have hu0R : 0 ≤ u.toReal := ENNReal.toReal_nonneg
  have hup0 : 0 ≤ up.toReal := ENNReal.toReal_nonneg
  nlinarith [hsumR, hdR, huR, hu0R, hup0, mul_nonneg hup0 hu0R,
    mul_nonneg (mul_nonneg hup0 hu0R) (sub_nonneg.mpr huR)]

/-- **The resolution and neutral masses sum to one.**  They partition the total
mass of one Double-B step. -/
theorem double_mass_sum (n : ℕ) (hn : 2 ≤ n) (s : DoubleState n) :
    doubleResolveDown s + doubleNeutralMass hn s + doubleResolveUp s = 1 := by
  have hh : 2 ≤ s.1.x + s.1.y + s.1.b := by have := s.2; simp only [BiCfg.DoubleInv] at this; omega
  have hpop : s.1.x + s.1.y + s.1.b = n := s.2
  have hup : dbPairPMF s.1.x s.1.y s.1.b hh .xb = doubleResolveUp s := by
    unfold doubleResolveUp
    rw [show dbPairPMF s.1.x s.1.y s.1.b hh PairComp.xb
        = ((PairComp.weight s.1.x s.1.y s.1.b PairComp.xb : ℕ):ℝ≥0∞)
          /(Nat.choose (s.1.x+s.1.y+s.1.b) 2:ℝ≥0∞) from rfl, hpop]
    simp [PairComp.weight]
  have hdown : dbPairPMF s.1.x s.1.y s.1.b hh .yb = doubleResolveDown s := by
    unfold doubleResolveDown
    rw [show dbPairPMF s.1.x s.1.y s.1.b hh PairComp.yb
        = ((PairComp.weight s.1.x s.1.y s.1.b PairComp.yb : ℕ):ℝ≥0∞)
          /(Nat.choose (s.1.x+s.1.y+s.1.b) 2:ℝ≥0∞) from rfl, hpop]
    simp [PairComp.weight]
  have htot : ∑ k : PairComp, dbPairPMF s.1.x s.1.y s.1.b hh k = 1 := by
    have h := (dbPairPMF s.1.x s.1.y s.1.b hh).tsum_coe; rwa [tsum_fintype] at h
  rw [← hup, ← hdown]
  unfold doubleNeutralMass
  rw [show (Finset.univ : Finset PairComp)
      = {PairComp.xx, PairComp.xy, PairComp.yy, PairComp.xb, PairComp.yb, PairComp.bb} from rfl,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton] at htot
  rw [← htot]; ring

/-- **Resolution bias in the majority region.**  When the effective level is at
least `aLo+1` and the co-level at most `bHi+1` (with `bHi ≤ aLo`), the down mass
is at most `u = bHi/aLo` times the up mass.  This feeds the Feller reduced
condition.  Reduces to `y·b·aLo ≤ x·b·bHi`, i.e. `(b-1)(x-y) ≥ 0` under the region bounds. -/
theorem doubleResolve_down_le (n aLo bHi : ℕ) (hn : 2 ≤ n) (s : DoubleState n)
    (haLo : 0 < aLo) (halo : aLo ≤ s.1.doubleLevel - 1) (hbhi : s.1.doubleCoLevel - 1 ≤ bHi)
    (hmaj : bHi ≤ aLo) :
    doubleResolveDown s ≤ doubleResolveUp s * ((bHi : ℝ≥0∞) / (aLo : ℝ≥0∞)) := by
  have hLv : s.1.doubleLevel = 2 * s.1.x + s.1.b := rfl
  have hCv : s.1.doubleCoLevel = 2 * s.1.y + s.1.b := rfl
  have hloN : aLo ≤ 2 * s.1.x + s.1.b - 1 := by rw [hLv] at halo; exact halo
  have hhiN : 2 * s.1.y + s.1.b - 1 ≤ bHi := by rw [hCv] at hbhi; exact hbhi
  have hlo2 : aLo + 1 ≤ 2 * s.1.x + s.1.b := by omega
  have hhi2 : 2 * s.1.y + s.1.b ≤ bHi + 1 := by omega
  have hCpos : 0 < Nat.choose n 2 := Nat.choose_pos hn
  have hCR : (0:ℝ) < (Nat.choose n 2 : ℝ) := by exact_mod_cast hCpos
  have haLoRpos : (0:ℝ) < (aLo : ℝ) := by exact_mod_cast haLo
  have hkey : s.1.y * s.1.b * aLo ≤ s.1.x * s.1.b * bHi := by
    rcases Nat.eq_zero_or_pos s.1.b with hb | hb
    · simp [hb]
    · have hx : s.1.y ≤ s.1.x := by omega
      have h1 : s.1.y * aLo ≤ s.1.x * bHi := by nlinarith [hb, hx, hloN, hhiN]
      calc s.1.y * s.1.b * aLo = s.1.b * (s.1.y * aLo) := by ring
        _ ≤ s.1.b * (s.1.x * bHi) := Nat.mul_le_mul_left _ h1
        _ = s.1.x * s.1.b * bHi := by ring
  have hdt : doubleResolveDown s ≠ ⊤ :=
    ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (by exact_mod_cast hCpos.ne')
  have hrt : doubleResolveUp s * ((bHi:ℝ≥0∞)/(aLo:ℝ≥0∞)) ≠ ⊤ :=
    ENNReal.mul_ne_top
      (ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (by exact_mod_cast hCpos.ne'))
      (ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (by simp only [ne_eq, Nat.cast_eq_zero]; omega))
  rw [← ENNReal.toReal_le_toReal hdt hrt]
  unfold doubleResolveDown doubleResolveUp
  rw [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_div, ENNReal.toReal_div]
  simp only [ENNReal.toReal_natCast]
  rw [div_mul_div_comm, div_le_div_iff₀ hCR (by positivity)]
  push_cast
  have hkeyR : (s.1.y : ℝ) * s.1.b * aLo ≤ (s.1.x : ℝ) * s.1.b * bHi := by exact_mod_cast hkey
  nlinarith [mul_le_mul_of_nonneg_left hkeyR hCR.le, hCR]

/-- **Feller safety: one-step geometric conservation.**  In the majority region
the geometric potential `u^doubleLevel` (`u = bHi/aLo ≤ 1`) does not increase in
expectation under one Double-B step. -/
theorem doubleState_conserve_on_region (n aLo bHi : Nat) (hn : 2 ≤ n)
    (haLo : 0 < aLo) (hmaj : bHi ≤ aLo) (s : DoubleState n)
    (halo : aLo < s.1.doubleLevel) (hbhi : s.1.doubleCoLevel ≤ bHi + 1) :
    expect (doubleStateStep n hn s) (fun z => ((bHi : ℝ≥0∞)/(aLo : ℝ≥0∞)) ^ z.1.doubleLevel)
      ≤ ((bHi : ℝ≥0∞)/(aLo : ℝ≥0∞)) ^ s.1.doubleLevel := by
  set u : ℝ≥0∞ := (bHi:ℝ≥0∞)/(aLo:ℝ≥0∞) with hu
  have haLone : (aLo:ℝ≥0∞) ≠ 0 := by simp only [ne_eq, Nat.cast_eq_zero]; omega
  have haLotop : (aLo:ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hu1 : u ≤ 1 := by
    rw [hu]; calc (bHi:ℝ≥0∞)/(aLo:ℝ≥0∞) ≤ (aLo:ℝ≥0∞)/(aLo:ℝ≥0∞) :=
        ENNReal.div_le_div_right (by exact_mod_cast hmaj) _
      _ = 1 := ENNReal.div_self haLone haLotop
  have hCpos : 0 < Nat.choose n 2 := Nat.choose_pos hn
  have hCne : ((Nat.choose n 2 : Nat):ℝ≥0∞) ≠ 0 := by exact_mod_cast hCpos.ne'
  have hdt : doubleResolveDown s ≠ ⊤ := ENNReal.div_ne_top (ENNReal.natCast_ne_top _) hCne
  have hut : doubleResolveUp s ≠ ⊤ := ENNReal.div_ne_top (ENNReal.natCast_ne_top _) hCne
  have hnt : doubleNeutralMass hn s ≠ ⊤ := by
    have hsum := double_mass_sum n hn s
    intro h; rw [h] at hsum; simp at hsum
  have hd : doubleResolveDown s ≤ doubleResolveUp s * u := by
    rw [hu]; exact doubleResolve_down_le n aLo bHi hn s haLo (by omega) (by omega) hmaj
  have hred := feller_reduced (doubleResolveDown s) (doubleNeutralMass hn s) (doubleResolveUp s) u
    (double_mass_sum n hn s) hd hu1 hdt hnt hut
  obtain ⟨a, ha⟩ : ∃ a, s.1.doubleLevel = a + 1 := ⟨s.1.doubleLevel - 1, by omega⟩
  rw [doubleStateStep_expect_level n hn s a ha (fun L => u ^ L), ha]
  have hfact : doubleResolveDown s * u ^ a + doubleNeutralMass hn s * u ^ (a + 1)
        + doubleResolveUp s * u ^ (a + 2)
      = u ^ a * (doubleResolveDown s + doubleNeutralMass hn s * u + doubleResolveUp s * u ^ 2) := by
    rw [pow_succ, pow_succ, pow_succ]; ring
  rw [hfact, pow_succ u a]
  exact mul_le_mul_left' hred _

/-! ## Co-level (progress-direction) mirror -/

-- co-level per-label helpers (coLevel = c+1): xb -> c (down), yb -> c+2 (up), neutral -> c+1
theorem nextDS_colevel_xb (n : ℕ) (s : DoubleState n) (c : ℕ) (hc : s.1.doubleCoLevel = c + 1)
    (hw : s.1.x * s.1.b ≠ 0) : (PairComp.nextDoubleState s PairComp.xb).1.doubleCoLevel + 1 = c + 1 := by
  have hb : 0 < s.1.b := Nat.pos_of_ne_zero (fun h => hw (by simp [h]))
  rw [PairComp.nextDoubleState, dif_neg (by simpa [PairComp.weight] using hw)]
  simp only [PairComp.next, BiCfg.doubleCoLevel] at hc ⊢; omega

theorem nextDS_colevel_yb (n : ℕ) (s : DoubleState n) (c : ℕ) (hc : s.1.doubleCoLevel = c + 1)
    (hw : s.1.y * s.1.b ≠ 0) : (PairComp.nextDoubleState s PairComp.yb).1.doubleCoLevel = c + 2 := by
  have hb : 0 < s.1.b := Nat.pos_of_ne_zero (fun h => hw (by simp [h]))
  rw [PairComp.nextDoubleState, dif_neg (by simpa [PairComp.weight] using hw)]
  simp only [PairComp.next, BiCfg.doubleCoLevel] at hc ⊢; omega

theorem nextDS_colevel_xy (n : ℕ) (s : DoubleState n) (c : ℕ) (hc : s.1.doubleCoLevel = c + 1) :
    (PairComp.nextDoubleState s PairComp.xy).1.doubleCoLevel = c + 1 := by
  rw [PairComp.nextDoubleState]
  by_cases hw : PairComp.weight s.1.x s.1.y s.1.b PairComp.xy = 0
  · rw [dif_pos hw]; simp only [BiCfg.doubleCoLevel] at hc ⊢; omega
  · rw [dif_neg hw]
    have hy : 0 < s.1.y := Nat.pos_of_ne_zero (fun h => hw (by simp [PairComp.weight, h]))
    simp only [PairComp.next, BiCfg.doubleCoLevel] at hc ⊢; omega

theorem nextDS_colevel_inert (n : ℕ) (s : DoubleState n) (c : ℕ) (hc : s.1.doubleCoLevel = c + 1)
    (k : PairComp) (hk : k = .xx ∨ k = .yy ∨ k = .bb) :
    (PairComp.nextDoubleState s k).1.doubleCoLevel = c + 1 := by
  rw [PairComp.nextDoubleState]
  by_cases hw : PairComp.weight s.1.x s.1.y s.1.b k = 0
  · rw [dif_pos hw]; rw [hc]
  · rw [dif_neg hw]; rcases hk with h|h|h <;> subst h <;>
      simp only [PairComp.next, BiCfg.doubleCoLevel] at hc ⊢ <;> omega

theorem doubleStateStep_expect_colevel (n : ℕ) (hn : 2 ≤ n) (s : DoubleState n) (c : ℕ)
    (hc : s.1.doubleCoLevel = c + 1) (F : ℕ → ℝ≥0∞) :
    expect (doubleStateStep n hn s) (fun z => F z.1.doubleCoLevel)
      = doubleResolveUp s * F c + doubleNeutralMass hn s * F (c + 1)
        + doubleResolveDown s * F (c + 2) := by
  have hh : 2 ≤ s.1.x + s.1.y + s.1.b := by have := s.2; simp only [BiCfg.DoubleInv] at this; omega
  have hpop : s.1.x + s.1.y + s.1.b = n := s.2
  have hup : dbPairPMF s.1.x s.1.y s.1.b hh .xb = doubleResolveUp s := by
    unfold doubleResolveUp
    rw [show dbPairPMF s.1.x s.1.y s.1.b hh PairComp.xb
        = ((PairComp.weight s.1.x s.1.y s.1.b PairComp.xb : ℕ):ℝ≥0∞)
          /(Nat.choose (s.1.x+s.1.y+s.1.b) 2:ℝ≥0∞) from rfl, hpop]
    simp [PairComp.weight]
  have hdown : dbPairPMF s.1.x s.1.y s.1.b hh .yb = doubleResolveDown s := by
    unfold doubleResolveDown
    rw [show dbPairPMF s.1.x s.1.y s.1.b hh PairComp.yb
        = ((PairComp.weight s.1.x s.1.y s.1.b PairComp.yb : ℕ):ℝ≥0∞)
          /(Nat.choose (s.1.x+s.1.y+s.1.b) 2:ℝ≥0∞) from rfl, hpop]
    simp [PairComp.weight]
  have hxbT : dbPairPMF s.1.x s.1.y s.1.b hh .xb * F ((PairComp.nextDoubleState s .xb).1.doubleCoLevel)
      = doubleResolveUp s * F c := by
    by_cases hw : s.1.x * s.1.b = 0
    · rw [dbPairPMF_zero_of_weight_zero (by simpa [PairComp.weight] using hw)]
      have h0 : doubleResolveUp s = 0 := by unfold doubleResolveUp; rw [hw]; simp
      rw [h0]; simp
    · have hlev : (PairComp.nextDoubleState s .xb).1.doubleCoLevel = c := by
        have := nextDS_colevel_xb n s c hc hw; omega
      rw [hlev, hup]
  have hybT : dbPairPMF s.1.x s.1.y s.1.b hh .yb * F ((PairComp.nextDoubleState s .yb).1.doubleCoLevel)
      = doubleResolveDown s * F (c + 2) := by
    by_cases hw : s.1.y * s.1.b = 0
    · rw [dbPairPMF_zero_of_weight_zero (by simpa [PairComp.weight] using hw)]
      have h0 : doubleResolveDown s = 0 := by unfold doubleResolveDown; rw [hw]; simp
      rw [h0]; simp
    · rw [nextDS_colevel_yb n s c hc hw, hdown]
  unfold doubleStateStep
  rw [expect_map]; unfold expect; rw [tsum_fintype]; simp only [Function.comp_apply]
  rw [show (Finset.univ : Finset PairComp)
      = {PairComp.xx, PairComp.xy, PairComp.yy, PairComp.xb, PairComp.yb, PairComp.bb} from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [nextDS_colevel_inert n s c hc .xx (by tauto), nextDS_colevel_xy n s c hc,
    nextDS_colevel_inert n s c hc .yy (Or.inr (Or.inl rfl)), hxbT, hybT,
    nextDS_colevel_inert n s c hc .bb (Or.inr (Or.inr rfl))]
  unfold doubleNeutralMass
  ring

end Tri
