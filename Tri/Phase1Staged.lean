/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Phase1Inhabit

/-!
# Staged phase-1 progress

The single-base construction in `Tri.Phase1Inhabit` asks one geometric base to
contract from the initial majority boundary all the way to `Phase1Exit`.  This
module instead gives every rung its own base.  If

    lower + bLo + 2 = n       and       bLo < lower,

the harmonic base at the lower edge is `bLo / lower`.  We use the concrete
rational midpoint

    w = (lower + bLo) / (2 * lower).

It lies strictly between `bLo / lower` and `1`.  The up atom is positive at
every live state, so the three-mass geometric expression is strictly smaller
than `w`.  Taking the finite maximum over one rung therefore produces an
explicit `phase1RungPhi < 1`; no signed-contraction hypothesis remains.

The second half of the module composes an arithmetically specified family of
such rungs with `Reaches.chain`.  Each rung has separate safety and upper-return
buffers.  The only input to `phase1_bridge_staged` is consequently a finite
schedule of natural-number boundaries and horizons.  All probabilistic fields,
including `Phase1BandBridge.hband`, are proved here.
-/

namespace Tri

open scoped ENNReal

/-- The rational geometric base assigned to one phase-1 rung. -/
noncomputable def phase1RungBase (lower bLo : ℕ) : ℝ≥0∞ :=
  ((lower + bLo : ℕ) : ℝ≥0∞) / ((2 * lower : ℕ) : ℝ≥0∞)

/-- The weighted down/stay/up expression at one candidate state of a rung.
Invalid population pairs and states outside the open rung contribute zero. -/
noncomputable def phase1RungWeightedMass
    (n lower bLo upper a b : ℕ) : ℝ≥0∞ :=
  if hvalid : 3 ≤ n ∧ a + b + 2 = n ∧
      lower < a + 1 ∧ a + 1 < upper then
    triStep (a + 1) (b + 1) (by omega) a
      + triStep (a + 1) (b + 1) (by omega) (a + 1) *
          phase1RungBase lower bLo
      + triStep (a + 1) (b + 1) (by omega) (a + 2) *
          phase1RungBase lower bLo ^ 2
  else 0

/-- The largest weighted three-mass expression on a finite rung. -/
noncomputable def phase1RungMax
    (n lower bLo upper : ℕ) : ℝ≥0∞ :=
  (Finset.range n).sup fun a =>
    (Finset.range n).sup fun b =>
      phase1RungWeightedMass n lower bLo upper a b

/-- The exact contraction factor of a rung for `phase1RungBase`. -/
noncomputable def phase1RungPhi
    (n lower bLo upper : ℕ) : ℝ≥0∞ :=
  phase1RungMax n lower bLo upper / phase1RungBase lower bLo

/-- Strict three-mass drift over `ℝ≥0∞`: a strict directional inequality and a
base strictly between zero and one give strict geometric contraction. -/
theorem three_mass_strict_contraction {pDown pStay pUp w : ℝ≥0∞}
    (hsum : pDown + pStay + pUp = 1) (hw0 : 0 < w) (hw1 : w < 1)
    (hdir : pDown < pUp * w) :
    pDown + pStay * w + pUp * w ^ 2 < w := by
  have hdownTop : pDown ≠ ⊤ := by
    apply ne_top_of_le_ne_top ENNReal.one_ne_top
    exact (le_add_right (le_add_right le_rfl)).trans_eq hsum
  have hstayTop : pStay ≠ ⊤ := by
    apply ne_top_of_le_ne_top ENNReal.one_ne_top
    exact (le_add_right (le_add_left le_rfl)).trans_eq hsum
  have hupTop : pUp ≠ ⊤ := by
    apply ne_top_of_le_ne_top ENNReal.one_ne_top
    exact (le_add_left le_rfl).trans_eq hsum
  have hwTop : w ≠ ⊤ := ne_top_of_lt (hw1.trans_le le_top)
  have hstayWTop : pStay * w ≠ ⊤ := ENNReal.mul_ne_top hstayTop hwTop
  have hupWTop : pUp * w ^ 2 ≠ ⊤ :=
    ENNReal.mul_ne_top hupTop (ENNReal.pow_ne_top hwTop)
  have hleftTop : pDown + pStay * w + pUp * w ^ 2 ≠ ⊤ :=
    ENNReal.add_ne_top.mpr
      ⟨ENNReal.add_ne_top.mpr ⟨hdownTop, hstayWTop⟩, hupWTop⟩
  rw [← ENNReal.toReal_lt_toReal hleftTop hwTop]
  rw [ENNReal.toReal_add
        (ENNReal.add_ne_top.mpr ⟨hdownTop, hstayWTop⟩) hupWTop,
    ENNReal.toReal_add hdownTop hstayWTop,
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_pow]
  have hsumReal := congrArg ENNReal.toReal hsum
  rw [ENNReal.toReal_add
      (ENNReal.add_ne_top.mpr ⟨hdownTop, hstayTop⟩) hupTop,
    ENNReal.toReal_add hdownTop hstayTop, ENNReal.toReal_one] at hsumReal
  have hdirReal := (ENNReal.toReal_lt_toReal hdownTop
    (ENNReal.mul_ne_top hupTop hwTop)).2 hdir
  rw [ENNReal.toReal_mul] at hdirReal
  have hw0Real : 0 < w.toReal := ENNReal.toReal_pos hw0.ne' hwTop
  have hw1Real : w.toReal < 1 := by
    simpa only [ENNReal.toReal_one] using
      (ENNReal.toReal_lt_toReal hwTop ENNReal.one_ne_top).2 hw1
  nlinarith [show 0 ≤ pDown.toReal from ENNReal.toReal_nonneg,
    show 0 ≤ pStay.toReal from ENNReal.toReal_nonneg,
    show 0 ≤ pUp.toReal from ENNReal.toReal_nonneg]

/-- The rung base is positive, is strictly below one, and is strictly above the
harmonic lower-edge base. -/
theorem phase1RungBase_spec {lower bLo : ℕ} (hlower : 0 < lower)
    (hbias : bLo < lower) :
    0 < phase1RungBase lower bLo ∧ phase1RungBase lower bLo < 1 ∧
      (bLo : ℝ≥0∞) / (lower : ℝ≥0∞) < phase1RungBase lower bLo := by
  have hden0 : ((2 * lower : ℕ) : ℝ≥0∞) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero, Nat.mul_eq_zero]
    omega
  have hdenTop : ((2 * lower : ℕ) : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.natCast_ne_top _
  have hlower0 : (lower : ℝ≥0∞) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    omega
  constructor
  · apply ENNReal.div_pos
    · simp only [ne_eq, Nat.cast_eq_zero]
      omega
    · exact hdenTop
  constructor
  · apply (ENNReal.div_lt_iff (Or.inl hden0) (Or.inl hdenTop)).2
    simp only [one_mul]
    exact_mod_cast (show lower + bLo < 2 * lower by omega)
  · have hleftTop : (bLo : ℝ≥0∞) / (lower : ℝ≥0∞) ≠ ⊤ :=
      ENNReal.div_ne_top (ENNReal.natCast_ne_top _) hlower0
    have hrightTop : phase1RungBase lower bLo ≠ ⊤ :=
      ENNReal.div_ne_top (ENNReal.natCast_ne_top _) hden0
    rw [← ENNReal.toReal_lt_toReal hleftTop hrightTop]
    rw [phase1RungBase, ENNReal.toReal_div, ENNReal.toReal_div]
    simp only [ENNReal.toReal_natCast]
    push_cast
    have hbiasReal : (bLo : ℝ) < lower := by exact_mod_cast hbias
    field_simp
    linarith

/-- At every live state of a majority rung, the chosen weighted expression is
strictly smaller than the rung base. -/
theorem phase1_rung_mass_lt_base
    (n lower bLo a b : ℕ) (h3 : 3 ≤ n)
    (hpopLower : lower + bLo + 2 = n) (hlower : 0 < lower)
    (hbias : bLo < lower) (hpop : a + b + 2 = n)
    (hlive : lower < a + 1) :
    triStep (a + 1) (b + 1) (by omega) a
        + triStep (a + 1) (b + 1) (by omega) (a + 1) *
            phase1RungBase lower bLo
        + triStep (a + 1) (b + 1) (by omega) (a + 2) *
            phase1RungBase lower bLo ^ 2
      < phase1RungBase lower bLo := by
  have haLower : lower ≤ a := by omega
  have hbUpper : b ≤ bLo := by omega
  have hbase := phase1RungBase_spec hlower hbias
  have hdrift := triStep_drift_uniform a b lower bLo (by omega)
    haLower hbUpper hlower
  have hup : 0 < triStep (a + 1) (b + 1) (by omega) (a + 2) := by
    rw [triStep_up]
    apply ENNReal.div_pos
    · push_cast
      exact mul_ne_zero
        (Nat.cast_ne_zero.mpr (Nat.choose_pos (by omega)).ne')
        (add_ne_zero.mpr (Or.inr one_ne_zero))
    · exact ENNReal.natCast_ne_top _
  have hdir : triStep (a + 1) (b + 1) (by omega) a <
      triStep (a + 1) (b + 1) (by omega) (a + 2) *
        phase1RungBase lower bLo :=
    hdrift.trans_lt (ENNReal.mul_lt_mul_right hup.ne'
      (PMF.apply_ne_top _ _) hbase.2.2)
  exact three_mass_strict_contraction
    (triStep_masses_sum a (b + 1) (by omega)) hbase.1 hbase.2.1 hdir

/-- The finite maximum defining a rung remains strictly below its base. -/
theorem phase1RungMax_lt_base
    (n lower bLo upper : ℕ) (h3 : 3 ≤ n)
    (hpopLower : lower + bLo + 2 = n) (hlower : 0 < lower)
    (hbias : bLo < lower) :
    phase1RungMax n lower bLo upper < phase1RungBase lower bLo := by
  have hbase0 := (phase1RungBase_spec hlower hbias).1
  unfold phase1RungMax
  rw [Finset.sup_lt_iff hbase0]
  intro a ha
  rw [Finset.sup_lt_iff hbase0]
  intro b hb
  unfold phase1RungWeightedMass
  split_ifs with hvalid
  · exact phase1_rung_mass_lt_base n lower bLo a b h3 hpopLower
      hlower hbias hvalid.2.1 hvalid.2.2.1
  · exact hbase0

/-- Every majority rung has a genuine contraction factor strictly below one. -/
theorem phase1RungPhi_lt_one
    (n lower bLo upper : ℕ) (h3 : 3 ≤ n)
    (hpopLower : lower + bLo + 2 = n) (hlower : 0 < lower)
    (hbias : bLo < lower) :
    phase1RungPhi n lower bLo upper < 1 := by
  have hbase := phase1RungBase_spec hlower hbias
  have hbaseTop : phase1RungBase lower bLo ≠ ⊤ :=
    ne_top_of_lt (hbase.2.1.trans_le le_top)
  unfold phase1RungPhi
  apply (ENNReal.div_lt_iff (Or.inl hbase.1.ne') (Or.inl hbaseTop)).2
  simpa only [one_mul] using
    phase1RungMax_lt_base n lower bLo upper h3 hpopLower hlower hbias

/-- The finite maximum supplies the exact per-rung `hdir` inequality consumed
by `DirectionProgress.phase1_direction_progress`. -/
theorem phase1_rung_scalar_contraction
    (n lower bLo upper a b : ℕ) (h3 : 3 ≤ n)
    (hpopLower : lower + bLo + 2 = n) (hlower : 0 < lower)
    (hbias : bLo < lower) (hpop : a + b + 2 = n)
    (hliveLower : lower < a + 1) (hliveUpper : a + 1 < upper) :
    triStep (a + 1) (b + 1) (by omega) a
        + triStep (a + 1) (b + 1) (by omega) (a + 1) *
            phase1RungBase lower bLo
        + triStep (a + 1) (b + 1) (by omega) (a + 2) *
            phase1RungBase lower bLo ^ 2
      ≤ phase1RungPhi n lower bLo upper * phase1RungBase lower bLo := by
  have haMem : a ∈ Finset.range n := Finset.mem_range.mpr (by omega)
  have hbMem : b ∈ Finset.range n := Finset.mem_range.mpr (by omega)
  have hmass :
      triStep (a + 1) (b + 1) (by omega) a
          + triStep (a + 1) (b + 1) (by omega) (a + 1) *
              phase1RungBase lower bLo
          + triStep (a + 1) (b + 1) (by omega) (a + 2) *
              phase1RungBase lower bLo ^ 2 =
        phase1RungWeightedMass n lower bLo upper a b := by
    simp [phase1RungWeightedMass, h3, hpop, hliveLower, hliveUpper]
  have hle : phase1RungWeightedMass n lower bLo upper a b ≤
      phase1RungMax n lower bLo upper := by
    have hinner := Finset.le_sup
      (s := Finset.range n)
      (f := phase1RungWeightedMass n lower bLo upper a) hbMem
    have houter := Finset.le_sup
      (s := Finset.range n)
      (f := fun a => (Finset.range n).sup
        (phase1RungWeightedMass n lower bLo upper a)) haMem
    exact hinner.trans houter
  have hbase := phase1RungBase_spec hlower hbias
  have hbaseTop : phase1RungBase lower bLo ≠ ⊤ :=
    ne_top_of_lt (hbase.2.1.trans_le le_top)
  calc
    triStep (a + 1) (b + 1) (by omega) a
          + triStep (a + 1) (b + 1) (by omega) (a + 1) *
              phase1RungBase lower bLo
          + triStep (a + 1) (b + 1) (by omega) (a + 2) *
              phase1RungBase lower bLo ^ 2 =
        phase1RungWeightedMass n lower bLo upper a b := hmass
    _ ≤ phase1RungMax n lower bLo upper := hle
    _ = phase1RungPhi n lower bLo upper * phase1RungBase lower bLo := by
      rw [phase1RungPhi, ENNReal.div_mul_cancel hbase.1.ne' hbaseTop]

/-- The stopped-direction error of one rung, uniformly evaluated at the
smallest allowed starting level. -/
noncomputable def phase1RungDirectionError
    (n lower bLo start upper k T : ℕ) : ℝ≥0∞ :=
  ((bLo : ℝ≥0∞) / (lower : ℝ≥0∞)) ^ k +
    phase1RungPhi n lower bLo upper ^ T *
      phase1RungBase lower bLo ^ start /
        phase1RungBase lower bLo ^ upper

/-- The complete error of one staged rung: stopped signed progress plus the
Feller cost of returning below the next-stage threshold. -/
noncomputable def phase1RungError
    (n lower bLo start next upper k returnLo bReturn kReturn T : ℕ) : ℝ≥0∞ :=
  phase1RungDirectionError n lower bLo start upper k T +
    ((bReturn : ℝ≥0∞) / (returnLo : ℝ≥0∞)) ^ kReturn

/-- One exact-time phase-1 rung on `triChain`.

The contraction factor and base are derived above, rather than assumed.  The
lower buffer controls ruin, while the gap from `returnLo` to `upper` controls
return after the stopped chain first reaches its upper boundary. -/
theorem phase1_staged_rung
    (n lower bLo start next upper k returnLo bReturn kReturn T : ℕ)
    (h3 : 3 ≤ n)
    (hpopLower : lower + bLo + 2 = n) (hlower : 0 < lower)
    (hbLo : 0 < bLo) (hbias : bLo < lower)
    (hstart : lower + k = start) (hk : 0 < k)
    (hadvance : start ≤ next) (hnextUpper : next ≤ upper)
    (hupper : upper ≤ n)
    (hpopReturn : returnLo + bReturn + 2 = n)
    (hreturnLo : 0 < returnLo) (hbReturn : 0 < bReturn)
    (hmajReturn : bReturn ≤ returnLo)
    (hreturnNext : returnLo + 1 = next)
    (hreturnGap : returnLo + kReturn ≤ upper) :
    Reaches (triChain n) T (fun z => start ≤ z) (fun z => next ≤ z)
      (phase1RungError n lower bLo start next upper k
        returnLo bReturn kReturn T) := by
  have hbase := phase1RungBase_spec hlower hbias
  have hbase0 : phase1RungBase lower bLo ≠ 0 := hbase.1.ne'
  have hbase1 : phase1RungBase lower bLo ≤ 1 := hbase.2.1.le
  have hphi := phase1RungPhi_lt_one n lower bLo upper h3 hpopLower
    hlower hbias
  have hphi1 : phase1RungPhi n lower bLo upper ≤ 1 := hphi.le
  have hratio : (bLo : ℝ≥0∞) / (lower : ℝ≥0∞) ≤ 1 := by
    have hlower0 : (lower : ℝ≥0∞) ≠ 0 := by
      simp only [ne_eq, Nat.cast_eq_zero]
      omega
    have hlowerTop : (lower : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
    calc
      (bLo : ℝ≥0∞) / (lower : ℝ≥0∞) ≤
          (lower : ℝ≥0∞) / (lower : ℝ≥0∞) :=
        ENNReal.div_le_div_right (Nat.cast_le.mpr hbias.le) _
      _ = 1 := ENNReal.div_self hlower0 hlowerTop
  intro z hzStart
  have hlowerZ : lower < z := by omega
  have hbandUpper : Reaches (bandCount n lower upper) T
      (fun s => s = (z, 0)) (fun s => upper ≤ s.1)
      (phase1RungDirectionError n lower bLo start upper k T) := by
    intro s hs
    subst s
    by_cases hzUpper : upper ≤ z
    · have hiter : iter (directionStop n lower upper) T z = PMF.pure z :=
        iter_freeze_of_mem z (Or.inr hzUpper) T
      calc
        (∑' q, if upper ≤ q.1 then 0 else
            iter (bandCount n lower upper) T (z, 0) q) =
            ∑' q, if upper ≤ q then 0 else
              iter (directionStop n lower upper) T z q :=
          bandCount_upper_failure_eq_directionStop n lower upper T z 0
        _ = 0 := by
          rw [hiter, ENNReal.tsum_eq_zero]
          intro q
          by_cases hq : upper ≤ q
          · simp [hq]
          · have hqz : q ≠ z := by
              intro hqz
              subst q
              exact hq hzUpper
            simp [hq, PMF.pure_apply, hqz]
        _ ≤ phase1RungDirectionError n lower bLo start upper k T := bot_le
    · have hzUpper' : z < upper := by omega
      obtain ⟨kz, hkz⟩ := Nat.le.dest hlowerZ.le
      obtain ⟨d, hd⟩ := Nat.le.dest hzUpper'.le
      have hkzPos : 0 < kz := by omega
      have hdPos : 0 < d := by omega
      have hkLe : k ≤ kz := by omega
      have hprogress := DirectionProgress.phase1_direction_progress
        n lower bLo kz d T h3 hpopLower hlower hbLo hbias.le
        hkzPos hdPos (by omega) (phase1RungBase lower bLo)
        (phase1RungPhi n lower bLo upper) hbase1 hbase0 (by
          intro a b hpop haLower haUpper
          exact phase1_rung_scalar_contraction n lower bLo upper a b h3
            hpopLower hlower hbias hpop haLower (by omega))
      have hprogress' :
          (∑' q, if upper ≤ q then 0 else
            iter (directionStop n lower upper) T z q) ≤
            ((bLo : ℝ≥0∞) / (lower : ℝ≥0∞)) ^ kz +
              phase1RungPhi n lower bLo upper ^ T *
                phase1RungBase lower bLo ^ z /
                  phase1RungBase lower bLo ^ upper := by
        simpa only [hkz, hd] using hprogress
      have hsafety :
          ((bLo : ℝ≥0∞) / (lower : ℝ≥0∞)) ^ kz ≤
            ((bLo : ℝ≥0∞) / (lower : ℝ≥0∞)) ^ k :=
        pow_le_pow_right_of_le_one' hratio hkLe
      have hstartPow : phase1RungBase lower bLo ^ z ≤
          phase1RungBase lower bLo ^ start :=
        pow_le_pow_right_of_le_one' hbase1 hzStart
      calc
        (∑' q, if upper ≤ q.1 then 0 else
            iter (bandCount n lower upper) T (z, 0) q) =
            ∑' q, if upper ≤ q then 0 else
              iter (directionStop n lower upper) T z q :=
          bandCount_upper_failure_eq_directionStop n lower upper T z 0
        _ ≤ ((bLo : ℝ≥0∞) / (lower : ℝ≥0∞)) ^ kz +
              phase1RungPhi n lower bLo upper ^ T *
                phase1RungBase lower bLo ^ z /
                  phase1RungBase lower bLo ^ upper := hprogress'
        _ ≤ phase1RungDirectionError n lower bLo start upper k T := by
          unfold phase1RungDirectionError
          apply add_le_add hsafety
          exact ENNReal.div_le_div_right
            (mul_le_mul_left' hstartPow _) _
  have hbandNext : Reaches (bandCount n lower upper) T
      (fun s => s = (z, 0)) (fun s => next ≤ s.1)
      (phase1RungDirectionError n lower bLo start upper k T) :=
    hbandUpper.mono_post (by
      intro q hq
      exact hnextUpper.trans hq)
  have htri := Reaches.of_bandCount_upper n lower upper returnLo bReturn
    kReturn T z 0 h3 hpopReturn hreturnLo hbReturn hmajReturn
    hreturnGap (fun q => next ≤ q)
    (phase1RungDirectionError n lower bLo start upper k T)
    (by
      intro q hq
      have hlowerStart : lower < start := by omega
      exact hlowerStart.trans_le (hadvance.trans hq))
    (by
      intro q hq
      omega)
    hbandNext
  simpa only [phase1RungError] using htri z rfl

end Tri
