/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.SingleBStaged
import Tri.DoubleBBandParams

/-!
# Single-B productive-count tail on a stopped band

The productive counter is the oriented ledger total
`CX + CY + RX + RY`.  The tail is masked: the potential vanishes once the band
has frozen or the productive counter has already reached the budget `K`.  This
is the Single-B-specific replacement for the unmasked Heavy-B clock.
-/

namespace Tri

open scoped ENNReal

/-- The oriented Single-B productive counter. -/
def singleLedgerProductiveCount {n : Nat} (q : SingleLedger n) : Nat :=
  q.cx + q.cy + q.rx + q.ry

/-- The aggregate productive mass of the four non-inert Single-B labels. -/
noncomputable def singleLedgerProductiveMass {n : Nat} (hn : 2 <= n)
    (q : SingleLedger n) : ENNReal :=
  singleCompPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b (by
      have h := q.cfg.2
      simp only [BiCfg.DoubleInv] at h
      omega) .xyToX
    + singleCompPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b (by
      have h := q.cfg.2
      simp only [BiCfg.DoubleInv] at h
      omega) .xyToY
    + singleCompPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b (by
      have h := q.cfg.2
      simp only [BiCfg.DoubleInv] at h
      omega) .xb
    + singleCompPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b (by
      have h := q.cfg.2
      simp only [BiCfg.DoubleInv] at h
      omega) .yb

/-- On a supported label, the productive counter advances by the sum of the
four oriented increments. -/
theorem nextSingleLedger_productiveCount {n : Nat}
    (q : SingleLedger n) (k : SingleComp)
    (hw : SingleComp.weight q.cfg.1.x q.cfg.1.y q.cfg.1.b k ≠ 0) :
    singleLedgerProductiveCount (SingleComp.nextSingleLedger q k)
      = singleLedgerProductiveCount q
        + (k.cxInc + k.cyInc + k.rxInc + k.ryInc) := by
  unfold SingleComp.nextSingleLedger singleLedgerProductiveCount
  rw [dif_neg hw]
  cases k <;> simp [SingleComp.cxInc, SingleComp.cyInc,
    SingleComp.rxInc, SingleComp.ryInc] <;> omega

/-- The productive counter is monotone across one guarded event. -/
theorem nextSingleLedger_productiveCount_mono {n : Nat}
    (q : SingleLedger n) (k : SingleComp) :
    singleLedgerProductiveCount q
      <= singleLedgerProductiveCount (SingleComp.nextSingleLedger q k) := by
  unfold SingleComp.nextSingleLedger singleLedgerProductiveCount
  split_ifs with hw
  · rfl
  · cases k <;> simp [SingleComp.cxInc, SingleComp.cyInc,
      SingleComp.rxInc, SingleComp.ryInc]

/-- The productive counter is monotone on the support of one ledger step. -/
theorem singleLedgerStep_productiveCount_mono_of_apply_ne_zero
    {n : Nat} (hn : 2 <= n) (q z : SingleLedger n)
    (hqz : singleLedgerStep n hn q z ≠ 0) :
    singleLedgerProductiveCount q <= singleLedgerProductiveCount z := by
  unfold singleLedgerStep at hqz
  rw [PMF.map_apply, Ne, ENNReal.tsum_eq_zero] at hqz
  push Not at hqz
  obtain ⟨k, hk⟩ := hqz
  split_ifs at hk with hzk
  · rw [hzk]
    exact nextSingleLedger_productiveCount_mono q k
  · exact absurd rfl hk

/-- The productive counter is monotone on the support of one stopped-band step. -/
theorem singleBandStop_productiveCount_mono_of_apply_ne_zero
    {n : Nat} (hn : 2 <= n) (aLoΛ hiΛ D H : Nat)
    (q z : SingleLedger n)
    (hqz : singleBandStop n hn aLoΛ hiΛ D H q z ≠ 0) :
    singleLedgerProductiveCount q <= singleLedgerProductiveCount z := by
  unfold singleBandStop freeze at hqz
  by_cases hB : SingleBandFrozen n aLoΛ hiΛ D H q
  · rw [if_pos hB, PMF.pure_apply] at hqz
    by_cases hzq : z = q
    · rw [hzq]
    · simp [hzq] at hqz
  · rw [if_neg hB] at hqz
    exact singleLedgerStep_productiveCount_mono_of_apply_ne_zero hn q z hqz

/-- The total resolution counter is monotone across one guarded event. -/
theorem nextSingleLedger_resolutionCount_mono {n : Nat}
    (q : SingleLedger n) (k : SingleComp) :
    q.rx + q.ry <=
      (SingleComp.nextSingleLedger q k).rx +
        (SingleComp.nextSingleLedger q k).ry := by
  unfold SingleComp.nextSingleLedger
  split_ifs
  · rfl
  · cases k <;> simp [SingleComp.rxInc, SingleComp.ryInc]

/-- The resolution counter is monotone on the support of one ledger step. -/
theorem singleLedgerStep_resolutionCount_mono_of_apply_ne_zero
    {n : Nat} (hn : 2 <= n) (q z : SingleLedger n)
    (hqz : singleLedgerStep n hn q z ≠ 0) :
    q.rx + q.ry <= z.rx + z.ry := by
  unfold singleLedgerStep at hqz
  rw [PMF.map_apply, Ne, ENNReal.tsum_eq_zero] at hqz
  push Not at hqz
  obtain ⟨k, hk⟩ := hqz
  split_ifs at hk with hzk
  · rw [hzk]
    exact nextSingleLedger_resolutionCount_mono q k
  · exact absurd rfl hk

/-- The resolution counter is monotone on the support of one stopped-band step. -/
theorem singleBandStop_resolutionCount_mono_of_apply_ne_zero
    {n : Nat} (hn : 2 <= n) (aLoΛ hiΛ D H : Nat)
    (q z : SingleLedger n)
    (hqz : singleBandStop n hn aLoΛ hiΛ D H q z ≠ 0) :
    q.rx + q.ry <= z.rx + z.ry := by
  unfold singleBandStop freeze at hqz
  by_cases hB : SingleBandFrozen n aLoΛ hiΛ D H q
  · rw [if_pos hB, PMF.pure_apply] at hqz
    by_cases hzq : z = q
    · rw [hzq]
    · simp [hzq] at hqz
  · rw [if_neg hB] at hqz
    exact singleLedgerStep_resolutionCount_mono_of_apply_ne_zero hn q z hqz

/-- The stopped Single-B band preserves the corrected `X` coordinate on
one-step support. -/
theorem singleBandStop_correctedX_of_apply_ne_zero
    {n x0 : Nat} (hn : 2 <= n) (aLoΛ hiΛ D H : Nat)
    (q z : SingleLedger n) (hx : q.CorrectedX x0)
    (hqz : singleBandStop n hn aLoΛ hiΛ D H q z ≠ 0) :
    z.CorrectedX x0 := by
  unfold singleBandStop freeze at hqz
  by_cases hB : SingleBandFrozen n aLoΛ hiΛ D H q
  · rw [if_pos hB, PMF.pure_apply] at hqz
    by_cases hzq : z = q
    · rwa [hzq]
    · simp [hzq] at hqz
  · rw [if_neg hB] at hqz
    exact singleLedgerStep_correctedX_of_apply_ne_zero hn q hx z hqz

/-- The stopped Single-B band preserves the corrected `X` coordinate along
finite supported trajectories. -/
theorem singleBandStop_iter_correctedX
    {n x0 T : Nat} (hn : 2 <= n) (aLoΛ hiΛ D H : Nat)
    (q z : SingleLedger n) (hx : q.CorrectedX x0)
    (hz : iter (singleBandStop n hn aLoΛ hiΛ D H) T q z ≠ 0) :
    z.CorrectedX x0 :=
  iter_support_closed (singleBandStop n hn aLoΛ hiΛ D H)
    (SingleLedger.CorrectedX x0)
    (fun a ha z haz =>
      singleBandStop_correctedX_of_apply_ne_zero hn aLoΛ hiΛ D H a z ha haz)
    T q z hx hz

/-- The negation of a corrected `X` coordinate is also preserved on one-step
support, since the coordinate is an exact path invariant. -/
theorem singleBandStop_not_correctedX_of_apply_ne_zero
    {n x0 : Nat} (hn : 2 <= n) (aLoΛ hiΛ D H : Nat)
    (q z : SingleLedger n) (hx : ¬ q.CorrectedX x0)
    (hqz : singleBandStop n hn aLoΛ hiΛ D H q z ≠ 0) :
    ¬ z.CorrectedX x0 := by
  unfold singleBandStop freeze at hqz
  by_cases hB : SingleBandFrozen n aLoΛ hiΛ D H q
  · rw [if_pos hB, PMF.pure_apply] at hqz
    by_cases hzq : z = q
    · rwa [hzq]
    · simp [hzq] at hqz
  · rw [if_neg hB] at hqz
    exact singleLedgerStep_not_correctedX_of_apply_ne_zero hn q hx z hqz

/-- The four productive Single-B event masses aggregate to the Double-B-shaped
productive weight over `C(pop,2)`. -/
theorem singleCompPMF_productive_mass (x y b : Nat)
    (h : 2 <= x + y + b) :
    singleCompPMF x y b h .xyToX
        + singleCompPMF x y b h .xyToY
        + singleCompPMF x y b h .xb
        + singleCompPMF x y b h .yb
      =
    ((singleProductiveWeight x y b : Nat) : ENNReal) /
      ((Nat.choose (x + y + b) 2 : Nat) : ENNReal) := by
  have hup := singleCompPMF_up_mass x y b h
  have hdn := singleCompPMF_down_mass x y b h
  calc
    singleCompPMF x y b h .xyToX
        + singleCompPMF x y b h .xyToY
        + singleCompPMF x y b h .xb
        + singleCompPMF x y b h .yb
        = (singleCompPMF x y b h .xyToX
            + singleCompPMF x y b h .xb)
          + (singleCompPMF x y b h .xyToY
            + singleCompPMF x y b h .yb) := by ring
    _ = (((x * y + 2 * (x * b) : Nat) : ENNReal) /
            ((2 * Nat.choose (x + y + b) 2 : Nat) : ENNReal))
          + (((x * y + 2 * (y * b) : Nat) : ENNReal) /
            ((2 * Nat.choose (x + y + b) 2 : Nat) : ENNReal)) := by
        rw [hup, hdn]
    _ = ((singleProductiveWeight x y b : Nat) : ENNReal) /
          ((Nat.choose (x + y + b) 2 : Nat) : ENNReal) := by
        rw [ENNReal.div_add_div_same]
        have hnum :
            x * y + 2 * (x * b) + (x * y + 2 * (y * b))
              = 2 * singleProductiveWeight x y b := by
          unfold singleProductiveWeight
          ring
        rw [← Nat.cast_add, hnum, Nat.cast_mul, Nat.cast_ofNat]
        simpa [Nat.cast_mul] using ennreal_two_mul_div_two_mul
          ((singleProductiveWeight x y b : Nat) : ENNReal)
          ((Nat.choose (x + y + b) 2 : Nat) : ENNReal)

/-- Productive mass on a ledger state, with the ambient denominator. -/
theorem singleLedgerProductiveMass_eq {n : Nat} (hn : 2 <= n)
    (q : SingleLedger n) :
    singleLedgerProductiveMass hn q =
      ((singleProductiveWeight q.cfg.1.x q.cfg.1.y q.cfg.1.b : Nat) : ENNReal) /
        ((Nat.choose n 2 : Nat) : ENNReal) := by
  unfold singleLedgerProductiveMass
  have hq2 : 2 <= q.cfg.1.x + q.cfg.1.y + q.cfg.1.b := by
    have h := q.cfg.2
    simp only [BiCfg.DoubleInv] at h
    omega
  have hpop : q.cfg.1.x + q.cfg.1.y + q.cfg.1.b = n := q.cfg.2
  simpa [hpop] using
    singleCompPMF_productive_mass q.cfg.1.x q.cfg.1.y q.cfg.1.b hq2

/-- Physical Single-B productive floor in witness form. -/
theorem singleProductiveWeight_level_floor
    (n x y b d c : Nat)
    (hinv : x + y + b = n)
    (hgap : y + d <= x)
    (hco : x + c <= n) :
    d * c <= singleProductiveWeight x y b := by
  have hd : d <= x := by omega
  have hc : c <= y + b := by omega
  calc
    d * c <= x * (y + b) := Nat.mul_le_mul hd hc
    _ = x * y + x * b := by ring
    _ <= singleProductiveWeight x y b := by
      unfold singleProductiveWeight
      nlinarith

/-- Productive mass floor for a physical gap and co-level witness. -/
theorem singleProductive_mass_level_ge {n : Nat} (hn : 2 <= n)
    (q : SingleLedger n) (d c : Nat)
    (hgap : q.cfg.1.y + d <= q.cfg.1.x)
    (hco : q.cfg.1.x + c <= n) :
    (((d * c : Nat) : ENNReal) /
        ((Nat.choose n 2 : Nat) : ENNReal))
      <= singleLedgerProductiveMass hn q := by
  rw [singleLedgerProductiveMass_eq hn q]
  have hprod :
      d * c <= singleProductiveWeight q.cfg.1.x q.cfg.1.y q.cfg.1.b :=
    singleProductiveWeight_level_floor n q.cfg.1.x q.cfg.1.y q.cfg.1.b
      d c q.cfg.2 hgap hco
  exact ENNReal.div_le_div_right (by exact_mod_cast hprod) _

/-- Productive mass floor attached to a Single-B corrected band. -/
noncomputable def singleBandProductivity (n d c : Nat) : ENNReal :=
  (((d * c : Nat) : ENNReal) / ((Nat.choose n 2 : Nat) : ENNReal))

/-- The concrete Single-B productivity floor is a probability. -/
theorem singleBandProductivity_le_one
    (n : Nat) (hn : 2 <= n)
    (aLoΛ hiΛ D K d c : Nat)
    (hgap : n + D + d = aLoΛ + 1)
    (hwidth : aLoΛ + 1 <= hiΛ)
    (hco : hiΛ + K + 2 * c <= 2 * n) :
    singleBandProductivity n d c <= 1 := by
  have hdc : d + 2 * c <= n := by omega
  have hS : ((d : Real) + 2 * (c : Real)) <= (n : Real) := by
    exact_mod_cast hdc
  have hSnonneg : 0 <= (d : Real) + 2 * (c : Real) := by positivity
  have hnnonneg : 0 <= (n : Real) := by positivity
  have hSsq : ((d : Real) + 2 * (c : Real)) ^ 2 <= (n : Real) ^ 2 := by
    rw [sq_le_sq]
    rw [abs_of_nonneg hSnonneg, abs_of_nonneg hnnonneg]
    exact hS
  have h8 : 8 * (d : Real) * (c : Real)
      <= ((d : Real) + 2 * (c : Real)) ^ 2 := by
    nlinarith [sq_nonneg ((d : Real) - 2 * (c : Real))]
  have hn4 : (n : Real) ^ 2 <= 4 * (n : Real) * ((n : Real) - 1) := by
    have hnR : (2 : Real) <= n := by exact_mod_cast hn
    nlinarith
  have hmulR : 2 * (d : Real) * (c : Real)
      <= (n : Real) * ((n : Real) - 1) := by
    nlinarith
  have hmulR' : ((2 * (d * c) : Nat) : Real)
      <= ((n * (n - 1) : Nat) : Real) := by
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_mul,
      Nat.cast_sub (by omega : 1 <= n), Nat.cast_one]
    simpa [mul_assoc] using hmulR
  have hmul2 : 2 * (d * c) <= n * (n - 1) := by
    exact_mod_cast hmulR'
  have hchoose : 2 * Nat.choose n 2 = n * (n - 1) := by
    have h := two_mul_choose_two_succ (n - 1)
    simpa only [Nat.sub_add_cancel (by omega : 1 <= n)] using h
  have hmul : d * c <= Nat.choose n 2 := by omega
  have hden0 : ((Nat.choose n 2 : Nat) : ENNReal) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hn).ne'
  have hdenT : ((Nat.choose n 2 : Nat) : ENNReal) ≠ ⊤ :=
    ENNReal.natCast_ne_top _
  calc
    singleBandProductivity n d c
        <= ((Nat.choose n 2 : Nat) : ENNReal) /
          ((Nat.choose n 2 : Nat) : ENNReal) := by
      unfold singleBandProductivity
      exact ENNReal.div_le_div_right (by exact_mod_cast hmul) _
    _ = 1 := ENNReal.div_self hden0 hdenT

/-- The level-based Single-B productive floor is uniform on the masked open
band.  The `K <= H+1` hypothesis lets the creation-balance guard apply on the
`count < K` mask. -/
theorem singleBandProductivity_le
    (n : Nat) (hn : 2 <= n)
    (aLoΛ hiΛ D H K d c : Nat)
    (hgap : n + D + d = aLoΛ + 1)
    (hco : hiΛ + K + 2 * c <= 2 * n)
    (q : SingleLedger n)
    (hlive : ¬ SingleBandFrozen n aLoΛ hiΛ D H q)
    (hcount : singleLedgerProductiveCount q < K) :
    singleBandProductivity n d c <= singleLedgerProductiveMass hn q := by
  have hnotLow :
      ¬ q.cfg.1.doubleLevel + q.cy <= aLoΛ + q.cx := by
    intro h
    exact hlive (Or.inl h)
  have hnotHigh :
      ¬ hiΛ + q.cx <= q.cfg.1.doubleLevel + q.cy := by
    intro h
    exact hlive (Or.inr (Or.inl h))
  have hnotBad : ¬ CreationBadY D H q := by
    intro h
    exact hlive (Or.inr (Or.inr (Or.inl h)))
  have hnotBoundary : ¬ singleCreationBoundary H q := by
    intro h
    exact hlive (Or.inr (Or.inr (Or.inr h)))
  have hlower : aLoΛ + q.cx + 1 <= q.cfg.1.doubleLevel + q.cy := by
    omega
  have hbudget : q.cx + q.cy <= H := by
    unfold singleCreationBoundary at hnotBoundary
    omega
  have hbal : q.cy <= q.cx + D := by
    by_contra hbal
    have hdev : D + q.cx <= q.cy := by omega
    exact hnotBad ⟨hbudget, hdev⟩
  have hcorrGap :
      q.cfg.1.y + q.cx + (d + D) <= q.cfg.1.x + q.cy := by
    have hinv := q.cfg.2
    simp only [BiCfg.doubleLevel, BiCfg.DoubleInv] at hinv hlower
    omega
  have hphysGap : q.cfg.1.y + d <= q.cfg.1.x := by
    have hrec := single_gap_recover (G := d + D) (D := D) q hcorrGap hbal
    omega
  have hupper : q.cfg.1.doubleLevel <= hiΛ + K := by
    unfold singleLedgerProductiveCount at hcount
    omega
  have hcoPhys : q.cfg.1.x + c <= n := by
    have hlevel : 2 * q.cfg.1.x <= hiΛ + K := by
      simp only [BiCfg.doubleLevel] at hupper
      omega
    omega
  unfold singleBandProductivity
  exact singleProductive_mass_level_ge hn q d c hphysGap hcoPhys

/-- Productive mass floor using the current corrected upper band and excluding
the mirror `X`-heavy creation tail.  This is the form needed in late rungs,
where the creation budget is structural and the old `hiΛ + K + 2*c` guard is
too expensive. -/
theorem singleBandProductivity_le_of_live_upper_xguard
    (n : Nat) (hn : 2 <= n)
    (aLoΛ hiΛ D D₂ H d c : Nat)
    (hgap : n + D + d = aLoΛ + 1)
    (hco : hiΛ + D₂ + 2 * c <= 2 * n + 1)
    (q : SingleLedger n)
    (hlive : ¬ SingleBandFrozen n aLoΛ hiΛ D H q)
    (hnotXBad : ¬ CreationBad D₂ H q) :
    singleBandProductivity n d c <= singleLedgerProductiveMass hn q := by
  have hnotLow :
      ¬ q.cfg.1.doubleLevel + q.cy <= aLoΛ + q.cx := by
    intro h
    exact hlive (Or.inl h)
  have hnotHigh :
      ¬ hiΛ + q.cx <= q.cfg.1.doubleLevel + q.cy := by
    intro h
    exact hlive (Or.inr (Or.inl h))
  have hnotBad : ¬ CreationBadY D H q := by
    intro h
    exact hlive (Or.inr (Or.inr (Or.inl h)))
  have hnotBoundary : ¬ singleCreationBoundary H q := by
    intro h
    exact hlive (Or.inr (Or.inr (Or.inr h)))
  have hlower : aLoΛ + q.cx + 1 <= q.cfg.1.doubleLevel + q.cy := by
    omega
  have hbudget : q.cx + q.cy <= H := by
    unfold singleCreationBoundary at hnotBoundary
    omega
  have hbal : q.cy <= q.cx + D := by
    by_contra hbal
    have hdev : D + q.cx <= q.cy := by omega
    exact hnotBad ⟨hbudget, hdev⟩
  have hcorrGap :
      q.cfg.1.y + q.cx + (d + D) <= q.cfg.1.x + q.cy := by
    have hinv := q.cfg.2
    simp only [BiCfg.doubleLevel, BiCfg.DoubleInv] at hinv hlower
    omega
  have hphysGap : q.cfg.1.y + d <= q.cfg.1.x := by
    have hrec := single_gap_recover (G := d + D) (D := D) q hcorrGap hbal
    omega
  have hupper : q.cfg.1.doubleLevel + q.cy < hiΛ + q.cx := by
    exact Nat.lt_of_not_ge hnotHigh
  have hbalX : q.cx <= q.cy + D₂ := by
    by_contra hbalX
    have hdev : D₂ + q.cy <= q.cx := by omega
    exact hnotXBad ⟨hbudget, hdev⟩
  have hlevelUpper : q.cfg.1.doubleLevel + 1 <= hiΛ + D₂ := by
    omega
  have hcoPhys : q.cfg.1.x + c <= n := by
    have hlevel : 2 * q.cfg.1.x + 1 <= hiΛ + D₂ := by
      simp only [BiCfg.doubleLevel] at hlevelUpper
      omega
    omega
  unfold singleBandProductivity
  exact singleProductive_mass_level_ge hn q d c hphysGap hcoPhys

/-- Productive mass floor from a fresh entrance upper bound and the preserved
corrected-`X` coordinate. -/
theorem singleBandProductivity_le_of_start_upper
    (n : Nat) (hn : 2 <= n)
    (aLoΛ hiΛ D H M d c : Nat)
    (hgap : n + D + d = aLoΛ + 1)
    (hco : hiΛ + 2 * M + 2 * c <= 2 * n + 1)
    (s0 : SingleState n)
    (hstartUpper : s0.1.doubleLevel + 1 <= hiΛ)
    (q : SingleLedger n)
    (hlive : ¬ SingleBandFrozen n aLoΛ hiΛ D H q)
    (hres : q.rx + q.ry < M)
    (hx : q.CorrectedX s0.1.x) :
    singleBandProductivity n d c <= singleLedgerProductiveMass hn q := by
  have hnotLow :
      ¬ q.cfg.1.doubleLevel + q.cy <= aLoΛ + q.cx := by
    intro h
    exact hlive (Or.inl h)
  have hnotBad : ¬ CreationBadY D H q := by
    intro h
    exact hlive (Or.inr (Or.inr (Or.inl h)))
  have hnotBoundary : ¬ singleCreationBoundary H q := by
    intro h
    exact hlive (Or.inr (Or.inr (Or.inr h)))
  have hlower : aLoΛ + q.cx + 1 <= q.cfg.1.doubleLevel + q.cy := by
    omega
  have hbudget : q.cx + q.cy <= H := by
    unfold singleCreationBoundary at hnotBoundary
    omega
  have hbal : q.cy <= q.cx + D := by
    by_contra hbal
    have hdev : D + q.cx <= q.cy := by omega
    exact hnotBad ⟨hbudget, hdev⟩
  have hcorrGap :
      q.cfg.1.y + q.cx + (d + D) <= q.cfg.1.x + q.cy := by
    have hinv := q.cfg.2
    simp only [BiCfg.doubleLevel, BiCfg.DoubleInv] at hinv hlower
    omega
  have hphysGap : q.cfg.1.y + d <= q.cfg.1.x := by
    have hrec := single_gap_recover (G := d + D) (D := D) q hcorrGap hbal
    omega
  have hcoPhys : q.cfg.1.x + c <= n := by
    simp only [SingleLedger.CorrectedX, BiCfg.doubleLevel] at hx hstartUpper
    omega
  unfold singleBandProductivity
  exact singleProductive_mass_level_ge hn q d c hphysGap hcoPhys

/-- One-step expansion of the Single-B productive counter. -/
theorem singleLedgerStep_prod_expect
    (n : Nat) (hn : 2 <= n) (q : SingleLedger n) (w : ENNReal) :
    expect (singleLedgerStep n hn q)
        (fun q' => w ^ singleLedgerProductiveCount q')
      =
      (singleCompPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b (by
          have h := q.cfg.2
          simp only [BiCfg.DoubleInv] at h
          omega) .xx
        + singleCompPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b (by
          have h := q.cfg.2
          simp only [BiCfg.DoubleInv] at h
          omega) .yy
        + singleCompPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b (by
          have h := q.cfg.2
          simp only [BiCfg.DoubleInv] at h
          omega) .bb)
        * w ^ singleLedgerProductiveCount q
      + singleLedgerProductiveMass hn q
        * w ^ (singleLedgerProductiveCount q + 1) := by
  have hq2 : 2 <= q.cfg.1.x + q.cfg.1.y + q.cfg.1.b := by
    have h := q.cfg.2
    simp only [BiCfg.DoubleInv] at h
    omega
  have key : forall (h' : 2 <= q.cfg.1.x + q.cfg.1.y + q.cfg.1.b)
      (k : SingleComp),
      singleCompPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b h' k
        * w ^ singleLedgerProductiveCount (SingleComp.nextSingleLedger q k)
      = singleCompPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b h' k
        * w ^ (singleLedgerProductiveCount q
          + (k.cxInc + k.cyInc + k.rxInc + k.ryInc)) := by
    intro h'
    intro k
    by_cases hw : SingleComp.weight q.cfg.1.x q.cfg.1.y q.cfg.1.b k = 0
    · rw [singleCompPMF_zero_of_weight_zero hw]
      simp
    · rw [nextSingleLedger_productiveCount q k hw]
  rw [expect_singleLedgerStep]
  rw [show (Finset.univ : Finset SingleComp) =
      {SingleComp.xx, SingleComp.xyToX, SingleComp.xyToY, SingleComp.yy,
        SingleComp.xb, SingleComp.yb, SingleComp.bb} from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  rw [key _ .xx, key _ .xyToX, key _ .xyToY, key _ .yy,
    key _ .xb, key _ .yb, key _ .bb]
  unfold singleLedgerProductiveMass
  simp only [SingleComp.cxInc, SingleComp.cyInc, SingleComp.rxInc,
    SingleComp.ryInc]
  ring

/-- Single-B productivity supermartingale for the oriented productive count. -/
theorem singleLedger_prod_super
    (n : Nat) (hn : 2 <= n) (q : SingleLedger n)
    (w pp pp' : ENNReal)
    (hw1 : w <= 1) (hpp : pp + pp' = 1)
    (hwt : w ≠ ⊤) (hppT : pp ≠ ⊤) (hpp'T : pp' ≠ ⊤)
    (hprod : pp <= singleLedgerProductiveMass hn q) :
    expect (singleLedgerStep n hn q)
        (fun q' => w ^ singleLedgerProductiveCount q')
      <= (pp' + pp * w) * w ^ singleLedgerProductiveCount q := by
  have hq2 : 2 <= q.cfg.1.x + q.cfg.1.y + q.cfg.1.b := by
    have h := q.cfg.2
    simp only [BiCfg.DoubleInv] at h
    omega
  set c := singleLedgerProductiveCount q
  set xx := singleCompPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b hq2 .xx
  set yy := singleCompPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b hq2 .yy
  set bb := singleCompPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b hq2 .bb
  set prod := singleLedgerProductiveMass hn q
  have hfin : forall k,
      singleCompPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b hq2 k ≠ ⊤ :=
    fun k => PMF.apply_ne_top _ _
  have hit : xx + yy + bb ≠ ⊤ :=
    ENNReal.add_ne_top.mpr
      ⟨ENNReal.add_ne_top.mpr ⟨hfin _, hfin _⟩, hfin _⟩
  have hpt : prod ≠ ⊤ := by
    unfold prod singleLedgerProductiveMass
    exact ENNReal.add_ne_top.mpr
      ⟨ENNReal.add_ne_top.mpr
        ⟨ENNReal.add_ne_top.mpr ⟨hfin _, hfin _⟩, hfin _⟩,
        hfin _⟩
  rw [singleLedgerStep_prod_expect n hn q w]
  have hmass : (xx + yy + bb) + prod = 1 := by
    have hsum := singleCompPMF_sum_seven q.cfg.1.x q.cfg.1.y q.cfg.1.b hq2
    unfold prod singleLedgerProductiveMass
    rw [← hsum]
    ring
  calc
    (xx + yy + bb) * w ^ c + prod * w ^ (c + 1)
        = ((xx + yy + bb) + prod * w) * w ^ c := by
          rw [pow_succ]
          ring
    _ <= (pp' + pp * w) * w ^ c :=
        mul_le_mul_right'
          (prod_scalar (xx + yy + bb) prod w pp pp'
            hmass hpp hprod hw1 hit hpt hwt hppT hpp'T) (w ^ c)

/-- Masked potential for the stopped-band productive clock. -/
noncomputable def singleProductiveMaskedV {n : Nat}
    (aLoΛ hiΛ D H K : Nat) (w : ENNReal)
    (q : SingleLedger n) : ENNReal :=
  if SingleBandFrozen n aLoΛ hiΛ D H q
      ∨ K <= singleLedgerProductiveCount q then
    0
  else
    w ^ singleLedgerProductiveCount q

/-- One-step masked productivity supermartingale on the stopped Single-B band. -/
theorem singleProductiveMasked_step
    (n : Nat) (hn : 2 <= n)
    (aLoΛ hiΛ D H K : Nat)
    (w pp pp' : ENNReal)
    (hw1 : w <= 1) (hpp : pp + pp' = 1)
    (hwt : w ≠ ⊤) (hppT : pp ≠ ⊤) (hpp'T : pp' ≠ ⊤)
    (hfloor : forall q : SingleLedger n,
      ¬ SingleBandFrozen n aLoΛ hiΛ D H q ->
      singleLedgerProductiveCount q < K ->
      pp <= singleLedgerProductiveMass hn q) :
    forall q : SingleLedger n,
      expect (singleBandStop n hn aLoΛ hiΛ D H q)
          (singleProductiveMaskedV aLoΛ hiΛ D H K w)
        <= (pp' + pp * w) *
          singleProductiveMaskedV aLoΛ hiΛ D H K w q := by
  intro q
  by_cases hB : SingleBandFrozen n aLoΛ hiΛ D H q
  · rw [singleBandStop, freeze_of_mem q hB]
    simp [singleProductiveMaskedV, hB]
  · by_cases hK : K <= singleLedgerProductiveCount q
    · have hzero :
          expect (singleBandStop n hn aLoΛ hiΛ D H q)
              (singleProductiveMaskedV aLoΛ hiΛ D H K w) = 0 := by
        unfold expect
        rw [ENNReal.tsum_eq_zero]
        intro z
        by_cases hzstep : singleBandStop n hn aLoΛ hiΛ D H q z = 0
        · simp [hzstep]
        · have hmono :=
            singleBandStop_productiveCount_mono_of_apply_ne_zero hn
              aLoΛ hiΛ D H q z hzstep
          have hzK : K <= singleLedgerProductiveCount z := le_trans hK hmono
          simp [singleProductiveMaskedV, hzK]
      rw [hzero]
      simp [singleProductiveMaskedV, hB, hK]
    · have hcount : singleLedgerProductiveCount q < K := Nat.lt_of_not_ge hK
      rw [singleBandStop, freeze_of_not_mem q hB]
      have hleV :
          expect (singleLedgerStep n hn q)
              (singleProductiveMaskedV aLoΛ hiΛ D H K w)
            <= expect (singleLedgerStep n hn q)
              (fun z => w ^ singleLedgerProductiveCount z) := by
        unfold expect
        refine ENNReal.tsum_le_tsum fun z => ?_
        exact mul_le_mul_left' (by
          unfold singleProductiveMaskedV
          split_ifs <;> simp) _
      calc
        expect (singleLedgerStep n hn q)
            (singleProductiveMaskedV aLoΛ hiΛ D H K w)
            <= expect (singleLedgerStep n hn q)
              (fun z => w ^ singleLedgerProductiveCount z) := hleV
        _ <= (pp' + pp * w) * w ^ singleLedgerProductiveCount q :=
            singleLedger_prod_super n hn q w pp pp' hw1 hpp hwt
              hppT hpp'T (hfloor q hB hcount)
        _ = (pp' + pp * w) *
              singleProductiveMaskedV aLoΛ hiΛ D H K w q := by
            simp [singleProductiveMaskedV, hB, hK]

/-- Masked-count lower tail on `singleBandStop`. -/
theorem singleBand_productive_masked_tail
    (n : Nat) (hn : 2 <= n)
    (aLoΛ hiΛ D H K T : Nat)
    (pp : ENNReal) (hpp1 : pp <= 1)
    (hfloor : forall q : SingleLedger n,
      ¬ SingleBandFrozen n aLoΛ hiΛ D H q ->
      singleLedgerProductiveCount q < K ->
      pp <= singleLedgerProductiveMass hn q)
    (s0 : SingleState n) :
    ∑' q, (if (¬ SingleBandFrozen n aLoΛ hiΛ D H q)
          ∧ singleLedgerProductiveCount q < K then
        iter (singleBandStop n hn aLoΛ hiΛ D H) T
          (⟨s0, 0, 0, 0, 0⟩ : SingleLedger n) q else 0)
      <= ((1 - pp) + pp * ((1 : ENNReal) / 2)) ^ T /
          ((1 : ENNReal) / 2) ^ K := by
  classical
  let w : ENNReal := (1 : ENNReal) / 2
  let pp' : ENNReal := 1 - pp
  let V : SingleLedger n -> ENNReal :=
    singleProductiveMaskedV aLoΛ hiΛ D H K w
  have hw1 : w <= 1 := by norm_num [w]
  have hw0 : w ≠ 0 := by norm_num [w]
  have hwt : w ≠ ⊤ := by norm_num [w]
  have hpp : pp + pp' = 1 := by
    dsimp [pp']
    rw [add_comm]
    exact tsub_add_cancel_of_le hpp1
  have hppT : pp ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hpp1
  have hpp'1 : pp' <= 1 := by
    dsimp [pp']
    exact tsub_le_self
  have hpp'T : pp' ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hpp'1
  set θ : ENNReal := w ^ K with hθ
  have hθ0 : θ ≠ 0 := by rw [hθ]; exact pow_ne_zero _ hw0
  have hθt : θ ≠ ⊤ := by rw [hθ]; exact ENNReal.pow_ne_top hwt
  have hsub : forall q : SingleLedger n,
      (if (¬ SingleBandFrozen n aLoΛ hiΛ D H q)
            ∧ singleLedgerProductiveCount q < K then
          iter (singleBandStop n hn aLoΛ hiΛ D H) T
            (⟨s0, 0, 0, 0, 0⟩ : SingleLedger n) q else 0)
      <= (if θ <= V q then
          iter (singleBandStop n hn aLoΛ hiΛ D H) T
            (⟨s0, 0, 0, 0, 0⟩ : SingleLedger n) q else 0) := by
    intro q
    by_cases hq :
        (¬ SingleBandFrozen n aLoΛ hiΛ D H q)
          ∧ singleLedgerProductiveCount q < K
    · have hV : V q = w ^ singleLedgerProductiveCount q := by
        dsimp [V, singleProductiveMaskedV]
        simp [hq.1, Nat.not_le.mpr hq.2]
      have hθle : θ <= V q := by
        rw [hθ, hV]
        exact pow_le_pow_right_of_le_one' hw1 (Nat.le_of_lt hq.2)
      simp [hq, hθle]
    · simp [hq]
  refine le_trans (ENNReal.tsum_le_tsum hsub) ?_
  refine le_trans (markov_div
    (iter (singleBandStop n hn aLoΛ hiΛ D H) T
      (⟨s0, 0, 0, 0, 0⟩ : SingleLedger n)) V θ hθ0 hθt) ?_
  have hiter := expect_iter_le (singleBandStop n hn aLoΛ hiΛ D H) V
    (pp' + pp * w)
    (singleProductiveMasked_step n hn aLoΛ hiΛ D H K w pp pp'
      hw1 hpp hwt hppT hpp'T hfloor) T
    (⟨s0, 0, 0, 0, 0⟩ : SingleLedger n)
  have hV0 : V (⟨s0, 0, 0, 0, 0⟩ : SingleLedger n) <= 1 := by
    dsimp [V, singleProductiveMaskedV, w]
    split_ifs
    · norm_num
    · simp [singleLedgerProductiveCount]
  calc
    expect (iter (singleBandStop n hn aLoΛ hiΛ D H) T
        (⟨s0, 0, 0, 0, 0⟩ : SingleLedger n)) V / θ
        <= (pp' + pp * w) ^ T *
            V (⟨s0, 0, 0, 0, 0⟩ : SingleLedger n) / θ := by
          exact ENNReal.div_le_div_right hiter θ
    _ <= (pp' + pp * w) ^ T * 1 / θ := by
          exact ENNReal.div_le_div_right
            (mul_le_mul_left' hV0 _) θ
    _ = (pp' + pp * w) ^ T / θ := by rw [mul_one]
    _ = ((1 - pp) + pp * ((1 : ENNReal) / 2)) ^ T /
          ((1 : ENNReal) / 2) ^ K := by
        simp [w, pp', hθ]

/-- Productive-count potential additionally masked by a resolution quota and a
fresh corrected-`X` invariant.  This is the late-rung mask: once either the
resolution quota, the productive-count quota, the stopped band, or the
corrected-`X` invariant fails, the mask remains off. -/
noncomputable def singleProductiveResolvedMaskedV {n : Nat}
    (aLoΛ hiΛ D H M K x0 : Nat) (w : ENNReal)
    (q : SingleLedger n) : ENNReal :=
  if SingleBandFrozen n aLoΛ hiΛ D H q
      ∨ M <= q.rx + q.ry
      ∨ K <= singleLedgerProductiveCount q
      ∨ ¬ q.CorrectedX x0 then
    0
  else
    w ^ singleLedgerProductiveCount q

/-- One-step supermartingale for the resolution-masked productive count. -/
theorem singleProductiveResolvedMasked_step
    (n : Nat) (hn : 2 <= n)
    (aLoΛ hiΛ D H M K x0 : Nat)
    (w pp pp' : ENNReal)
    (hw1 : w <= 1) (hpp : pp + pp' = 1)
    (hwt : w ≠ ⊤) (hppT : pp ≠ ⊤) (hpp'T : pp' ≠ ⊤)
    (hfloor : forall q : SingleLedger n,
      ¬ SingleBandFrozen n aLoΛ hiΛ D H q ->
      q.rx + q.ry < M ->
      singleLedgerProductiveCount q < K ->
      q.CorrectedX x0 ->
      pp <= singleLedgerProductiveMass hn q) :
    forall q : SingleLedger n,
      expect (singleBandStop n hn aLoΛ hiΛ D H q)
          (singleProductiveResolvedMaskedV aLoΛ hiΛ D H M K x0 w)
        <= (pp' + pp * w) *
          singleProductiveResolvedMaskedV aLoΛ hiΛ D H M K x0 w q := by
  intro q
  by_cases hB : SingleBandFrozen n aLoΛ hiΛ D H q
  · rw [singleBandStop, freeze_of_mem q hB]
    simp [singleProductiveResolvedMaskedV, hB]
  · by_cases hM : M <= q.rx + q.ry
    · have hzero :
          expect (singleBandStop n hn aLoΛ hiΛ D H q)
              (singleProductiveResolvedMaskedV aLoΛ hiΛ D H M K x0 w) = 0 := by
        unfold expect
        rw [ENNReal.tsum_eq_zero]
        intro z
        by_cases hzstep : singleBandStop n hn aLoΛ hiΛ D H q z = 0
        · simp [hzstep]
        · have hmono :=
            singleBandStop_resolutionCount_mono_of_apply_ne_zero hn
              aLoΛ hiΛ D H q z hzstep
          have hzM : M <= z.rx + z.ry := le_trans hM hmono
          simp [singleProductiveResolvedMaskedV, hzM]
      rw [hzero]
      simp [singleProductiveResolvedMaskedV, hB, hM]
    · by_cases hK : K <= singleLedgerProductiveCount q
      · have hzero :
            expect (singleBandStop n hn aLoΛ hiΛ D H q)
                (singleProductiveResolvedMaskedV aLoΛ hiΛ D H M K x0 w) = 0 := by
          unfold expect
          rw [ENNReal.tsum_eq_zero]
          intro z
          by_cases hzstep : singleBandStop n hn aLoΛ hiΛ D H q z = 0
          · simp [hzstep]
          · have hmono :=
              singleBandStop_productiveCount_mono_of_apply_ne_zero hn
                aLoΛ hiΛ D H q z hzstep
            have hzK : K <= singleLedgerProductiveCount z := le_trans hK hmono
            simp [singleProductiveResolvedMaskedV, hzK]
        rw [hzero]
        simp [singleProductiveResolvedMaskedV, hB, hM, hK]
      · by_cases hx : q.CorrectedX x0
        · have hres : q.rx + q.ry < M := Nat.lt_of_not_ge hM
          have hcount : singleLedgerProductiveCount q < K := Nat.lt_of_not_ge hK
          rw [singleBandStop, freeze_of_not_mem q hB]
          have hleV :
              expect (singleLedgerStep n hn q)
                  (singleProductiveResolvedMaskedV aLoΛ hiΛ D H M K x0 w)
                <= expect (singleLedgerStep n hn q)
                  (fun z => w ^ singleLedgerProductiveCount z) := by
            unfold expect
            refine ENNReal.tsum_le_tsum fun z => ?_
            exact mul_le_mul_left' (by
              unfold singleProductiveResolvedMaskedV
              split_ifs <;> simp) _
          calc
            expect (singleLedgerStep n hn q)
                (singleProductiveResolvedMaskedV aLoΛ hiΛ D H M K x0 w)
                <= expect (singleLedgerStep n hn q)
                  (fun z => w ^ singleLedgerProductiveCount z) := hleV
            _ <= (pp' + pp * w) * w ^ singleLedgerProductiveCount q :=
                singleLedger_prod_super n hn q w pp pp' hw1 hpp hwt
                  hppT hpp'T (hfloor q hB hres hcount hx)
            _ = (pp' + pp * w) *
                  singleProductiveResolvedMaskedV aLoΛ hiΛ D H M K x0 w q := by
                simp [singleProductiveResolvedMaskedV, hB, hM, hK, hx]
        · have hzero :
              expect (singleBandStop n hn aLoΛ hiΛ D H q)
                  (singleProductiveResolvedMaskedV aLoΛ hiΛ D H M K x0 w) = 0 := by
            unfold expect
            rw [ENNReal.tsum_eq_zero]
            intro z
            by_cases hzstep : singleBandStop n hn aLoΛ hiΛ D H q z = 0
            · simp [hzstep]
            · have hznot :=
                singleBandStop_not_correctedX_of_apply_ne_zero hn
                  aLoΛ hiΛ D H q z hx hzstep
              simp [singleProductiveResolvedMaskedV, hznot]
          rw [hzero]
          simp [singleProductiveResolvedMaskedV, hB, hM, hK, hx]

/-- Lower tail for the late resolution-masked productive clock. -/
theorem singleBand_productive_resolved_masked_tail
    (n : Nat) (hn : 2 <= n)
    (aLoΛ hiΛ D H M K x0 T : Nat)
    (pp : ENNReal) (hpp1 : pp <= 1)
    (hfloor : forall q : SingleLedger n,
      ¬ SingleBandFrozen n aLoΛ hiΛ D H q ->
      q.rx + q.ry < M ->
      singleLedgerProductiveCount q < K ->
      q.CorrectedX x0 ->
      pp <= singleLedgerProductiveMass hn q)
    (s0 : SingleState n) :
    ∑' q, (if (¬ SingleBandFrozen n aLoΛ hiΛ D H q)
          ∧ q.rx + q.ry < M
          ∧ singleLedgerProductiveCount q < K
          ∧ q.CorrectedX x0 then
        iter (singleBandStop n hn aLoΛ hiΛ D H) T
          (⟨s0, 0, 0, 0, 0⟩ : SingleLedger n) q else 0)
      <= ((1 - pp) + pp * ((1 : ENNReal) / 2)) ^ T /
          ((1 : ENNReal) / 2) ^ K := by
  classical
  let w : ENNReal := (1 : ENNReal) / 2
  let pp' : ENNReal := 1 - pp
  let V : SingleLedger n -> ENNReal :=
    singleProductiveResolvedMaskedV aLoΛ hiΛ D H M K x0 w
  have hw1 : w <= 1 := by norm_num [w]
  have hw0 : w ≠ 0 := by norm_num [w]
  have hwt : w ≠ ⊤ := by norm_num [w]
  have hpp : pp + pp' = 1 := by
    dsimp [pp']
    rw [add_comm]
    exact tsub_add_cancel_of_le hpp1
  have hppT : pp ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hpp1
  have hpp'1 : pp' <= 1 := by
    dsimp [pp']
    exact tsub_le_self
  have hpp'T : pp' ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hpp'1
  set θ : ENNReal := w ^ K with hθ
  have hθ0 : θ ≠ 0 := by rw [hθ]; exact pow_ne_zero _ hw0
  have hθt : θ ≠ ⊤ := by rw [hθ]; exact ENNReal.pow_ne_top hwt
  have hsub : forall q : SingleLedger n,
      (if (¬ SingleBandFrozen n aLoΛ hiΛ D H q)
            ∧ q.rx + q.ry < M
            ∧ singleLedgerProductiveCount q < K
            ∧ q.CorrectedX x0 then
          iter (singleBandStop n hn aLoΛ hiΛ D H) T
            (⟨s0, 0, 0, 0, 0⟩ : SingleLedger n) q else 0)
      <= (if θ <= V q then
          iter (singleBandStop n hn aLoΛ hiΛ D H) T
            (⟨s0, 0, 0, 0, 0⟩ : SingleLedger n) q else 0) := by
    intro q
    by_cases hq :
        (¬ SingleBandFrozen n aLoΛ hiΛ D H q)
          ∧ q.rx + q.ry < M
          ∧ singleLedgerProductiveCount q < K
          ∧ q.CorrectedX x0
    · have hV : V q = w ^ singleLedgerProductiveCount q := by
        dsimp [V, singleProductiveResolvedMaskedV]
        simp [hq.1, Nat.not_le.mpr hq.2.1,
          Nat.not_le.mpr hq.2.2.1, hq.2.2.2]
      have hθle : θ <= V q := by
        rw [hθ, hV]
        exact pow_le_pow_right_of_le_one' hw1 (Nat.le_of_lt hq.2.2.1)
      simp [hq, hθle]
    · simp [hq]
  refine le_trans (ENNReal.tsum_le_tsum hsub) ?_
  refine le_trans (markov_div
    (iter (singleBandStop n hn aLoΛ hiΛ D H) T
      (⟨s0, 0, 0, 0, 0⟩ : SingleLedger n)) V θ hθ0 hθt) ?_
  have hiter := expect_iter_le (singleBandStop n hn aLoΛ hiΛ D H) V
    (pp' + pp * w)
    (singleProductiveResolvedMasked_step n hn aLoΛ hiΛ D H M K x0 w pp pp'
      hw1 hpp hwt hppT hpp'T hfloor) T
    (⟨s0, 0, 0, 0, 0⟩ : SingleLedger n)
  have hV0 : V (⟨s0, 0, 0, 0, 0⟩ : SingleLedger n) <= 1 := by
    dsimp [V, singleProductiveResolvedMaskedV, w]
    split_ifs
    · norm_num
    · simp [singleLedgerProductiveCount]
  calc
    expect (iter (singleBandStop n hn aLoΛ hiΛ D H) T
        (⟨s0, 0, 0, 0, 0⟩ : SingleLedger n)) V / θ
        <= (pp' + pp * w) ^ T *
            V (⟨s0, 0, 0, 0, 0⟩ : SingleLedger n) / θ := by
          exact ENNReal.div_le_div_right hiter θ
    _ <= (pp' + pp * w) ^ T * 1 / θ := by
          exact ENNReal.div_le_div_right
            (mul_le_mul_left' hV0 _) θ
    _ = (pp' + pp * w) ^ T / θ := by rw [mul_one]
    _ = ((1 - pp) + pp * ((1 : ENNReal) / 2)) ^ T /
          ((1 : ENNReal) / 2) ^ K := by
        simp [w, pp', hθ]

/-- The stopped Single-B band preserves the oriented blank ledger. -/
theorem singleBandStop_iter_blankLedger
    {n initialBlank T aLoΛ hiΛ D H : Nat} (hn : 2 <= n)
    (q z : SingleLedger n) (hq : q.BlankLedger initialBlank)
    (hz : iter (singleBandStop n hn aLoΛ hiΛ D H) T q z ≠ 0) :
    z.BlankLedger initialBlank := by
  refine iter_support_closed (singleBandStop n hn aLoΛ hiΛ D H)
    (SingleLedger.BlankLedger initialBlank) (fun a ha z haz => ?_) T q z hq hz
  unfold singleBandStop freeze at haz
  by_cases hB : SingleBandFrozen n aLoΛ hiΛ D H a
  · rw [if_pos hB, PMF.pure_apply] at haz
    by_cases hza : z = a
    · rwa [hza]
    · simp [hza] at haz
  · rw [if_neg hB] at haz
    exact singleLedgerStep_blankLedger_of_apply_ne_zero hn a ha z haz

/-- Few resolutions force a small productive count, via the blank ledger. -/
theorem singleLedgerProductiveCount_lt_of_resolutions_lt
    {n initialBlank B0 M K : Nat} (q : SingleLedger n)
    (hq : q.BlankLedger initialBlank)
    (hB0 : B0 <= initialBlank)
    (hK : B0 + K = n + 2 * M)
    (hres : q.rx + q.ry < M) :
    singleLedgerProductiveCount q < K := by
  have hb : q.cfg.1.b <= n := by
    have hinv := q.cfg.2
    simp only [BiCfg.DoubleInv] at hinv
    omega
  unfold SingleLedger.BlankLedger at hq
  unfold singleLedgerProductiveCount
  omega

/-- Productive-clock producer in exactly the `singleBand_phase_reaches`
`hclock` shape. -/
theorem singleBand_hclock
    {n : Nat} (hn : 2 <= n)
    (aLoΛ hiΛ targetΛ D H M K B0 T d c : Nat)
    (htargetHi : targetΛ + 1 <= hiΛ)
    (hDbudget : H < D)
    (hK : B0 + K = n + 2 * M)
    (hgap : n + D + d = aLoΛ + 1)
    (hwidth : aLoΛ + 1 <= hiΛ)
    (hco : hiΛ + K + 2 * c <= 2 * n)
    (s0 : SingleState n)
    (hB0 : B0 <= s0.1.b) :
    ∑' q, (if singleBandStarvation aLoΛ targetΛ H M q then
        iter (singleBandStop n hn aLoΛ hiΛ D H) T
          (⟨s0, 0, 0, 0, 0⟩ : SingleLedger n) q else 0)
      <= ((1 - singleBandProductivity n d c)
            + singleBandProductivity n d c * ((1 : ENNReal) / 2)) ^ T /
          ((1 : ENNReal) / 2) ^ K := by
  classical
  let pp : ENNReal := singleBandProductivity n d c
  have hpp1 : pp <= 1 :=
    singleBandProductivity_le_one n hn aLoΛ hiΛ D K d c
      hgap hwidth hco
  have hfloor : forall q : SingleLedger n,
      ¬ SingleBandFrozen n aLoΛ hiΛ D H q ->
      singleLedgerProductiveCount q < K ->
      pp <= singleLedgerProductiveMass hn q := by
    intro q hq hcount
    exact singleBandProductivity_le n hn aLoΛ hiΛ D H K d c
      hgap hco q hq hcount
  have htail := singleBand_productive_masked_tail n hn aLoΛ hiΛ D H K T
    pp hpp1 hfloor s0
  have hsubStarve :
      (∑' q, (if singleBandStarvation aLoΛ targetΛ H M q then
          iter (singleBandStop n hn aLoΛ hiΛ D H) T
            (⟨s0, 0, 0, 0, 0⟩ : SingleLedger n) q else 0))
        <=
      ∑' q, (if (¬ SingleBandFrozen n aLoΛ hiΛ D H q)
            ∧ singleLedgerProductiveCount q < K then
          iter (singleBandStop n hn aLoΛ hiΛ D H) T
            (⟨s0, 0, 0, 0, 0⟩ : SingleLedger n) q else 0) := by
    refine ENNReal.tsum_le_tsum (fun q => ?_)
    by_cases hs : singleBandStarvation aLoΛ targetΛ H M q
    · by_cases hp0 :
          iter (singleBandStop n hn aLoΛ hiΛ D H) T
            (⟨s0, 0, 0, 0, 0⟩ : SingleLedger n) q = 0
      · simp [hs, hp0]
      · have hblank : q.BlankLedger s0.1.b :=
          singleBandStop_iter_blankLedger hn
            (⟨s0, 0, 0, 0, 0⟩ : SingleLedger n) q
            (SingleLedger.initial_blankLedger s0) hp0
        have hcount :
            singleLedgerProductiveCount q < K :=
          singleLedgerProductiveCount_lt_of_resolutions_lt q hblank hB0 hK
            hs.2.2.1
        have hnotLow :
            ¬ q.cfg.1.doubleLevel + q.cy <= aLoΛ + q.cx := by
          unfold singleBandStarvation at hs
          omega
        have hnotHigh :
            ¬ hiΛ + q.cx <= q.cfg.1.doubleLevel + q.cy := by
          unfold singleBandStarvation at hs
          omega
        have hnotBad : ¬ CreationBadY D H q := by
          intro hbad
          have hDle : D <= H := by
            rcases hbad with ⟨hbudget, hdev⟩
            omega
          omega
        have hnotBoundary : ¬ singleCreationBoundary H q := by
          intro hboundary
          unfold singleBandStarvation at hs
          unfold singleCreationBoundary at hboundary
          omega
        have hnotB : ¬ SingleBandFrozen n aLoΛ hiΛ D H q := by
          intro hB
          rcases hB with hLow | hRest
          · exact hnotLow hLow
          · rcases hRest with hHigh | hRest'
            · exact hnotHigh hHigh
            · rcases hRest' with hBad | hBoundary
              · exact hnotBad hBad
              · exact hnotBoundary hBoundary
        simp [hs, hnotB, hcount]
    · simp [hs]
  exact hsubStarve.trans (by simpa [pp] using htail)

/-- Productive-clock producer with the creation-imbalance stream kept explicit.

This is the structural-budget form used by the late Single-B rungs: the
starvation event is split into the masked productive lower tail plus the
`Y`-heavy creation tail, so no impossible `H < D` side condition is needed. -/
theorem singleBand_hclock_with_creation
    {n : Nat} (hn : 2 <= n)
    (aLoΛ hiΛ targetΛ D H M K B0 T d c : Nat)
    (htargetHi : targetΛ + 1 <= hiΛ)
    (hH : 0 < H)
    (hK : B0 + K = n + 2 * M)
    (hgap : n + D + d = aLoΛ + 1)
    (hwidth : aLoΛ + 1 <= hiΛ)
    (hco : hiΛ + K + 2 * c <= 2 * n)
    (s0 : SingleState n)
    (hB0 : B0 <= s0.1.b) :
    ∑' q, (if singleBandStarvation aLoΛ targetΛ H M q then
        iter (singleBandStop n hn aLoΛ hiΛ D H) T
          (⟨s0, 0, 0, 0, 0⟩ : SingleLedger n) q else 0)
      <= ((1 - singleBandProductivity n d c)
            + singleBandProductivity n d c * ((1 : ENNReal) / 2)) ^ T /
          ((1 : ENNReal) / 2) ^ K
        + ENNReal.ofReal (Real.exp (-((D : ℝ) ^ 2 / (2 * (H : ℝ))))) := by
  classical
  let pp : ENNReal := singleBandProductivity n d c
  have hpp1 : pp <= 1 :=
    singleBandProductivity_le_one n hn aLoΛ hiΛ D K d c
      hgap hwidth hco
  have hfloor : forall q : SingleLedger n,
      ¬ SingleBandFrozen n aLoΛ hiΛ D H q ->
      singleLedgerProductiveCount q < K ->
      pp <= singleLedgerProductiveMass hn q := by
    intro q hq hcount
    exact singleBandProductivity_le n hn aLoΛ hiΛ D H K d c
      hgap hco q hq hcount
  have htail := singleBand_productive_masked_tail n hn aLoΛ hiΛ D H K T
    pp hpp1 hfloor s0
  have hbad := singleCreationY_stopped_tail hn aLoΛ hiΛ D H T hH s0
  have hsubStarve :
      (∑' q, (if singleBandStarvation aLoΛ targetΛ H M q then
          iter (singleBandStop n hn aLoΛ hiΛ D H) T
            (⟨s0, 0, 0, 0, 0⟩ : SingleLedger n) q else 0))
        <=
      (∑' q, (if (¬ SingleBandFrozen n aLoΛ hiΛ D H q)
            ∧ singleLedgerProductiveCount q < K then
          iter (singleBandStop n hn aLoΛ hiΛ D H) T
            (⟨s0, 0, 0, 0, 0⟩ : SingleLedger n) q else 0))
        +
      (∑' q, (if CreationBadY D H q then
          iter (singleBandStop n hn aLoΛ hiΛ D H) T
            (⟨s0, 0, 0, 0, 0⟩ : SingleLedger n) q else 0)) := by
    rw [← ENNReal.tsum_add]
    refine ENNReal.tsum_le_tsum (fun q => ?_)
    by_cases hs : singleBandStarvation aLoΛ targetΛ H M q
    · by_cases hp0 :
          iter (singleBandStop n hn aLoΛ hiΛ D H) T
            (⟨s0, 0, 0, 0, 0⟩ : SingleLedger n) q = 0
      · simp [hs, hp0]
      · by_cases hbadq : CreationBadY D H q
        · simp [hs, hbadq]
        · have hblank : q.BlankLedger s0.1.b :=
            singleBandStop_iter_blankLedger hn
              (⟨s0, 0, 0, 0, 0⟩ : SingleLedger n) q
              (SingleLedger.initial_blankLedger s0) hp0
          have hcount :
              singleLedgerProductiveCount q < K :=
            singleLedgerProductiveCount_lt_of_resolutions_lt q hblank hB0 hK
              hs.2.2.1
          have hnotLow :
              ¬ q.cfg.1.doubleLevel + q.cy <= aLoΛ + q.cx := by
            unfold singleBandStarvation at hs
            omega
          have hnotHigh :
              ¬ hiΛ + q.cx <= q.cfg.1.doubleLevel + q.cy := by
            unfold singleBandStarvation at hs
            omega
          have hnotBoundary : ¬ singleCreationBoundary H q := by
            intro hboundary
            unfold singleBandStarvation at hs
            unfold singleCreationBoundary at hboundary
            omega
          have hnotB : ¬ SingleBandFrozen n aLoΛ hiΛ D H q := by
            intro hB
            rcases hB with hLow | hRest
            · exact hnotLow hLow
            · rcases hRest with hHigh | hRest'
              · exact hnotHigh hHigh
              · rcases hRest' with hBad | hBoundary
                · exact hbadq hBad
                · exact hnotBoundary hBoundary
          simp [hs, hnotB, hcount, hbadq]
    · simp [hs]
  exact hsubStarve.trans
    (add_le_add (by simpa [pp] using htail) hbad)

/-- Late Single-B starvation clock with a structural creation budget and a
resolution mask.  The caller supplies the state-specific productive floor,
typically from the preserved corrected-`X` ledger and the entrance upper band,
so no initial blank lower bound is required. -/
theorem singleBand_hclock_resolved_with_creation
    {n : Nat} (hn : 2 <= n)
    (aLoΛ hiΛ targetΛ D H M K T : Nat)
    (htargetHi : targetΛ + 1 <= hiΛ)
    (hH : 0 < H)
    (hK : H + M <= K)
    (s0 : SingleState n)
    (pp : ENNReal) (hpp1 : pp <= 1)
    (hfloor : forall q : SingleLedger n,
      ¬ SingleBandFrozen n aLoΛ hiΛ D H q ->
      q.rx + q.ry < M ->
      singleLedgerProductiveCount q < K ->
      q.CorrectedX s0.1.x ->
      pp <= singleLedgerProductiveMass hn q) :
    ∑' q, (if singleBandStarvation aLoΛ targetΛ H M q then
        iter (singleBandStop n hn aLoΛ hiΛ D H) T
          (⟨s0, 0, 0, 0, 0⟩ : SingleLedger n) q else 0)
      <= ((1 - pp) + pp * ((1 : ENNReal) / 2)) ^ T /
          ((1 : ENNReal) / 2) ^ K
        + ENNReal.ofReal (Real.exp (-((D : ℝ) ^ 2 / (2 * (H : ℝ))))) := by
  classical
  have htail := singleBand_productive_resolved_masked_tail n hn
    aLoΛ hiΛ D H M K s0.1.x T pp hpp1 hfloor s0
  have hbad := singleCreationY_stopped_tail hn aLoΛ hiΛ D H T hH s0
  have hsubStarve :
      (∑' q, (if singleBandStarvation aLoΛ targetΛ H M q then
          iter (singleBandStop n hn aLoΛ hiΛ D H) T
            (⟨s0, 0, 0, 0, 0⟩ : SingleLedger n) q else 0))
        <=
      (∑' q, (if (¬ SingleBandFrozen n aLoΛ hiΛ D H q)
            ∧ q.rx + q.ry < M
            ∧ singleLedgerProductiveCount q < K
            ∧ q.CorrectedX s0.1.x then
          iter (singleBandStop n hn aLoΛ hiΛ D H) T
            (⟨s0, 0, 0, 0, 0⟩ : SingleLedger n) q else 0))
        +
      (∑' q, (if CreationBadY D H q then
          iter (singleBandStop n hn aLoΛ hiΛ D H) T
            (⟨s0, 0, 0, 0, 0⟩ : SingleLedger n) q else 0)) := by
    rw [← ENNReal.tsum_add]
    refine ENNReal.tsum_le_tsum (fun q => ?_)
    by_cases hs : singleBandStarvation aLoΛ targetΛ H M q
    · by_cases hp0 :
          iter (singleBandStop n hn aLoΛ hiΛ D H) T
            (⟨s0, 0, 0, 0, 0⟩ : SingleLedger n) q = 0
      · simp [hs, hp0]
      · by_cases hbadq : CreationBadY D H q
        · simp [hs, hbadq]
        · have hnotLow :
              ¬ q.cfg.1.doubleLevel + q.cy <= aLoΛ + q.cx := by
            unfold singleBandStarvation at hs
            omega
          have hnotHigh :
              ¬ hiΛ + q.cx <= q.cfg.1.doubleLevel + q.cy := by
            intro hhi
            have htarget : q.cfg.1.doubleLevel + q.cy <= targetΛ + q.cx := by
              unfold singleBandStarvation at hs
              omega
            omega
          have hnotBoundary : ¬ singleCreationBoundary H q := by
            intro hboundary
            unfold singleBandStarvation at hs
            unfold singleCreationBoundary at hboundary
            omega
          have hnotB : ¬ SingleBandFrozen n aLoΛ hiΛ D H q := by
            intro hB
            rcases hB with hLow | hRest
            · exact hnotLow hLow
            · rcases hRest with hHigh | hRest'
              · exact hnotHigh hHigh
              · rcases hRest' with hBad | hBoundary
                · exact hbadq hBad
                · exact hnotBoundary hBoundary
          have hres : q.rx + q.ry < M := by
            unfold singleBandStarvation at hs
            omega
          have hcount : singleLedgerProductiveCount q < K := by
            unfold singleBandStarvation at hs
            unfold singleLedgerProductiveCount
            omega
          have hx : q.CorrectedX s0.1.x :=
            singleBandStop_iter_correctedX hn aLoΛ hiΛ D H
              (⟨s0, 0, 0, 0, 0⟩ : SingleLedger n) q
              (SingleLedger.initial_correctedX s0) hp0
          simp [hs, hbadq, hnotB, hres, hcount, hx]
    · simp [hs]
  exact hsubStarve.trans
    (add_le_add (by simpa using htail) hbad)

/-- If the fresh state is already at the stopped band's corrected upper
boundary, the stopped band is pure and the starvation window is empty. -/
theorem singleBand_starvation_mass_zero_of_start_high
    {n : Nat} (hn : 2 <= n)
    (aLoΛ hiΛ targetΛ D H M T : Nat)
    (htargetHi : targetΛ + 1 <= hiΛ)
    (s0 : SingleState n)
    (hstartHigh : hiΛ <= s0.1.doubleLevel) :
    (∑' q, (if singleBandStarvation aLoΛ targetΛ H M q then
        iter (singleBandStop n hn aLoΛ hiΛ D H) T
          (⟨s0, 0, 0, 0, 0⟩ : SingleLedger n) q else 0)) = 0 := by
  classical
  let q0 : SingleLedger n := ⟨s0, 0, 0, 0, 0⟩
  have hB0 : SingleBandFrozen n aLoΛ hiΛ D H q0 := by
    right
    left
    dsimp [q0]
    simpa using hstartHigh
  have hiter :
      iter (singleBandStop n hn aLoΛ hiΛ D H) T q0 = PMF.pure q0 := by
    simpa [singleBandStop] using
      iter_freeze_of_mem (B := SingleBandFrozen n aLoΛ hiΛ D H)
        (K := singleLedgerStep n hn) q0 hB0 T
  rw [hiter]
  rw [ENNReal.tsum_eq_zero]
  intro q
  by_cases hs : singleBandStarvation aLoΛ targetΛ H M q
  · have hqne : q ≠ q0 := by
      intro hq
      subst q
      unfold singleBandStarvation at hs
      dsimp [q0] at hs
      omega
    simp [hs, PMF.pure_apply, hqne]
  · simp [hs]

/-- Late Single-B starvation clock from an entrance upper bound.  The
productive floor is recovered from the preserved corrected-`X` coordinate,
rather than from an initial blank lower bound. -/
theorem singleBand_hclock_resolved_with_creation_start_upper
    {n : Nat} (hn : 2 <= n)
    (aLoΛ hiΛ targetΛ D H M K T d c : Nat)
    (htargetHi : targetΛ + 1 <= hiΛ)
    (hH : 0 < H)
    (hK : H + M <= K)
    (hgap : n + D + d = aLoΛ + 1)
    (hco : hiΛ + 2 * M + 2 * c <= 2 * n + 1)
    (hpp1 : singleBandProductivity n d c <= 1)
    (s0 : SingleState n)
    (hstartUpper : s0.1.doubleLevel + 1 <= hiΛ) :
    ∑' q, (if singleBandStarvation aLoΛ targetΛ H M q then
        iter (singleBandStop n hn aLoΛ hiΛ D H) T
          (⟨s0, 0, 0, 0, 0⟩ : SingleLedger n) q else 0)
      <= ((1 - singleBandProductivity n d c)
            + singleBandProductivity n d c * ((1 : ENNReal) / 2)) ^ T /
          ((1 : ENNReal) / 2) ^ K
        + ENNReal.ofReal (Real.exp (-((D : ℝ) ^ 2 / (2 * (H : ℝ))))) := by
  let pp : ENNReal := singleBandProductivity n d c
  have hfloor : forall q : SingleLedger n,
      ¬ SingleBandFrozen n aLoΛ hiΛ D H q ->
      q.rx + q.ry < M ->
      singleLedgerProductiveCount q < K ->
      q.CorrectedX s0.1.x ->
      pp <= singleLedgerProductiveMass hn q := by
    intro q hq hres _hcount hx
    exact singleBandProductivity_le_of_start_upper n hn aLoΛ hiΛ D H M d c
      hgap hco s0 hstartUpper q hq hres hx
  simpa [pp] using
    singleBand_hclock_resolved_with_creation hn aLoΛ hiΛ targetΛ D H M K T
      htargetHi hH hK s0 pp hpp1 hfloor

/-- Late Single-B starvation clock with the entrance high case discharged by
the stopped-band freeze and the remaining case handled by the corrected-`X`
productive floor. -/
theorem singleBand_hclock_resolved_with_creation_entry
    {n : Nat} (hn : 2 <= n)
    (aLoΛ hiΛ targetΛ D H M K T d c : Nat)
    (htargetHi : targetΛ + 1 <= hiΛ)
    (hH : 0 < H)
    (hK : H + M <= K)
    (hgap : n + D + d = aLoΛ + 1)
    (hco : hiΛ + 2 * M + 2 * c <= 2 * n + 1)
    (hpp1 : singleBandProductivity n d c <= 1)
    (s0 : SingleState n) :
    ∑' q, (if singleBandStarvation aLoΛ targetΛ H M q then
        iter (singleBandStop n hn aLoΛ hiΛ D H) T
          (⟨s0, 0, 0, 0, 0⟩ : SingleLedger n) q else 0)
      <= ((1 - singleBandProductivity n d c)
            + singleBandProductivity n d c * ((1 : ENNReal) / 2)) ^ T /
          ((1 : ENNReal) / 2) ^ K
        + ENNReal.ofReal (Real.exp (-((D : ℝ) ^ 2 / (2 * (H : ℝ))))) := by
  by_cases hstartHigh : hiΛ <= s0.1.doubleLevel
  · rw [singleBand_starvation_mass_zero_of_start_high hn aLoΛ hiΛ targetΛ D H
      M T htargetHi s0 hstartHigh]
    exact bot_le
  · have hstartUpper : s0.1.doubleLevel + 1 <= hiΛ := by omega
    exact singleBand_hclock_resolved_with_creation_start_upper hn
      aLoΛ hiΛ targetΛ D H M K T d c htargetHi hH hK hgap hco
      hpp1 s0 hstartUpper

end Tri

#print axioms Tri.nextSingleLedger_productiveCount
#print axioms Tri.nextSingleLedger_productiveCount_mono
#print axioms Tri.singleLedgerStep_productiveCount_mono_of_apply_ne_zero
#print axioms Tri.singleBandStop_productiveCount_mono_of_apply_ne_zero
#print axioms Tri.nextSingleLedger_resolutionCount_mono
#print axioms Tri.singleLedgerStep_resolutionCount_mono_of_apply_ne_zero
#print axioms Tri.singleBandStop_resolutionCount_mono_of_apply_ne_zero
#print axioms Tri.singleBandStop_correctedX_of_apply_ne_zero
#print axioms Tri.singleBandStop_iter_correctedX
#print axioms Tri.singleBandStop_not_correctedX_of_apply_ne_zero
#print axioms Tri.singleCompPMF_productive_mass
#print axioms Tri.singleLedgerProductiveMass_eq
#print axioms Tri.singleProductiveWeight_level_floor
#print axioms Tri.singleProductive_mass_level_ge
#print axioms Tri.singleBandProductivity_le_one
#print axioms Tri.singleBandProductivity_le
#print axioms Tri.singleBandProductivity_le_of_live_upper_xguard
#print axioms Tri.singleBandProductivity_le_of_start_upper
#print axioms Tri.singleLedgerStep_prod_expect
#print axioms Tri.singleLedger_prod_super
#print axioms Tri.singleProductiveMasked_step
#print axioms Tri.singleBand_productive_masked_tail
#print axioms Tri.singleProductiveResolvedMasked_step
#print axioms Tri.singleBand_productive_resolved_masked_tail
#print axioms Tri.singleBandStop_iter_blankLedger
#print axioms Tri.singleLedgerProductiveCount_lt_of_resolutions_lt
#print axioms Tri.singleBand_hclock
#print axioms Tri.singleBand_hclock_with_creation
#print axioms Tri.singleBand_hclock_resolved_with_creation
#print axioms Tri.singleBand_starvation_mass_zero_of_start_high
#print axioms Tri.singleBand_hclock_resolved_with_creation_start_upper
#print axioms Tri.singleBand_hclock_resolved_with_creation_entry
