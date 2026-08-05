/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.SingleBClockConstants
import Tri.SingleBFeller

/-!
# A concrete Single-B band rung driven by the joint occupation clock

This instantiates the repaired staged Single-B phase with the two-branch
occupation clock in place of the productive-clock starvation producer, at the
γ-free `Θ(n)` horizon `T = 128(n+2M)` and the lazy creation budget `H = T+1`.

The direction engine gets honest constants: the live guard `(n+g)·y ≤ n·x`
follows from the recovered physical gap `y+g ≤ x`, so `u = n/(n+g) < 1`, the
geometric base is `w = (2n+g)/(2n+2g)` with `u < w < 1`, and
`η = doubleDirectionEta u w > 1`.

The starvation stream is covered by the joint clock plus the creation-bad
stream (the two events may overlap once `D ≤ H`, so the creation tail is paid
twice — the bound is explicit either way).
-/

namespace Tri

open scoped ENNReal

/-! ### Honest direction constants -/

/-- Direction drift ratio `u = n/(n+g)`. -/
noncomputable def singleRungDirU (n g : ℕ) : ℝ≥0∞ :=
  (n : ℝ≥0∞) / ((n + g : ℕ) : ℝ≥0∞)

/-- Direction geometric base `w = (2n+g)/(2n+2g)`, strictly between `u` and
one. -/
noncomputable def singleRungDirW (n g : ℕ) : ℝ≥0∞ :=
  ((2 * n + g : ℕ) : ℝ≥0∞) / ((2 * (n + g) : ℕ) : ℝ≥0∞)

/-- Reciprocal base `v = (2n+2g)/(2n+g)`, with `w·v = 1`. -/
noncomputable def singleRungDirV (n g : ℕ) : ℝ≥0∞ :=
  ((2 * (n + g) : ℕ) : ℝ≥0∞) / ((2 * n + g : ℕ) : ℝ≥0∞)

/-- The event-indexed direction multiplier. -/
noncomputable def singleRungDirEta (n g : ℕ) : ℝ≥0∞ :=
  doubleDirectionEta (singleRungDirU n g) (singleRungDirW n g)

/-- The Single-B rung direction parameters satisfy the complete scalar
hypothesis bundle of the stopped-window direction tail. -/
theorem singleRungDir_params (n g : ℕ) (hn : 0 < n) (hg : 0 < g) :
    singleRungDirEta n g *
        (singleRungDirU n g + singleRungDirW n g ^ 2)
      = singleRungDirW n g * (singleRungDirU n g + 1) ∧
    singleRungDirW n g ≤ singleRungDirEta n g ∧
    1 ≤ singleRungDirEta n g ∧
    singleRungDirEta n g ≠ ⊤ ∧
    singleRungDirW n g ≤ 1 ∧
    singleRungDirW n g ≠ 0 ∧
    singleRungDirW n g ≠ ⊤ ∧
    singleRungDirW n g * singleRungDirV n g = 1 := by
  have hu0 : 0 < singleRungDirU n g := by
    unfold singleRungDirU
    exact ENNReal.div_pos
      (by
        simp only [ne_eq, Nat.cast_eq_zero]
        omega)
      (ENNReal.natCast_ne_top _)
  have huT : singleRungDirU n g ≠ ⊤ := by
    unfold singleRungDirU
    exact ENNReal.div_ne_top (ENNReal.natCast_ne_top _)
      (by
        simp only [ne_eq, Nat.cast_eq_zero]
        omega)
  have hwT : singleRungDirW n g ≠ ⊤ := by
    unfold singleRungDirW
    exact ENNReal.div_ne_top (ENNReal.natCast_ne_top _)
      (by
        simp only [ne_eq, Nat.cast_eq_zero]
        omega)
  have huw : singleRungDirU n g < singleRungDirW n g := by
    rw [← ENNReal.toReal_lt_toReal huT hwT]
    unfold singleRungDirU singleRungDirW
    simp only [ENNReal.toReal_div, ENNReal.toReal_natCast]
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    push_cast
    nlinarith [sq_nonneg (g : ℝ),
      (by exact_mod_cast hg : (0 : ℝ) < (g : ℝ)),
      (by exact_mod_cast hn : (0 : ℝ) < (n : ℝ))]
  have hw1 : singleRungDirW n g < 1 := by
    rw [← ENNReal.toReal_lt_toReal hwT ENNReal.one_ne_top]
    unfold singleRungDirW
    simp only [ENNReal.toReal_div, ENNReal.toReal_natCast,
      ENNReal.toReal_one]
    rw [div_lt_one (by positivity)]
    push_cast
    nlinarith [(by exact_mod_cast hg : (0 : ℝ) < (g : ℝ))]
  obtain ⟨hrel, hwη, hη1, hηT⟩ := doubleDirectionEta_spec hu0 huw hw1
  have hw0 : singleRungDirW n g ≠ 0 := (hu0.trans huw).ne'
  have hwv : singleRungDirW n g * singleRungDirV n g = 1 := by
    have ha0 : ((2 * n + g : ℕ) : ℝ≥0∞) ≠ 0 := by
      exact_mod_cast (by omega : 2 * n + g ≠ 0)
    have hb0 : ((2 * (n + g) : ℕ) : ℝ≥0∞) ≠ 0 := by
      exact_mod_cast (by omega : 2 * (n + g) ≠ 0)
    have haT : ((2 * n + g : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
    have hbT : ((2 * (n + g) : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
    unfold singleRungDirW singleRungDirV
    rw [div_eq_mul_inv, div_eq_mul_inv]
    calc
      ((2 * n + g : ℕ) : ℝ≥0∞) * (((2 * (n + g) : ℕ) : ℝ≥0∞))⁻¹ *
            (((2 * (n + g) : ℕ) : ℝ≥0∞) * (((2 * n + g : ℕ) : ℝ≥0∞))⁻¹)
          = ((2 * n + g : ℕ) : ℝ≥0∞) * (((2 * n + g : ℕ) : ℝ≥0∞))⁻¹ *
              (((2 * (n + g) : ℕ) : ℝ≥0∞) *
                (((2 * (n + g) : ℕ) : ℝ≥0∞))⁻¹) := by
            ring
      _ = 1 := by
            rw [ENNReal.mul_inv_cancel ha0 haT,
              ENNReal.mul_inv_cancel hb0 hbT, one_mul]
  exact ⟨by simpa [singleRungDirEta] using hrel,
    by simpa [singleRungDirEta] using hwη,
    by simpa [singleRungDirEta] using hη1,
    by simpa [singleRungDirEta] using hηT,
    hw1.le, hw0, hwT, hwv⟩

/-- The live-region producer: every live state of the repaired band carries a
corrected-level witness and the ratio guard `(n+g)·y ≤ n·x`. -/
theorem singleBand_hlive_ratio {n aLoΛ hiΛ D H g : ℕ}
    (hgap : n + D + g ≤ aLoΛ + 1) :
    ∀ q : SingleLedger n, ¬ SingleBandFrozen n aLoΛ hiΛ D H q →
      ∃ a : ℕ, q.CorrectedLevel (a + 1) ∧
        (n + g) * q.cfg.1.y ≤ n * q.cfg.1.x := by
  intro q hB
  have hnotLow : ¬ (q.cfg.1.doubleLevel + q.cy ≤ aLoΛ + q.cx) :=
    fun h => hB (Or.inl h)
  obtain ⟨a, ha⟩ :
      ∃ a, q.cfg.1.doubleLevel + q.cy = (a + 1) + q.cx :=
    ⟨q.cfg.1.doubleLevel + q.cy - q.cx - 1, by omega⟩
  have hgapPhys : q.cfg.1.y + g ≤ q.cfg.1.x :=
    singleB_live_gap q hB hgap
  have hy : q.cfg.1.y ≤ n := by
    have hinv := q.cfg.2
    simp only [BiCfg.DoubleInv] at hinv
    omega
  refine ⟨a, ha, ?_⟩
  nlinarith [Nat.mul_le_mul_left n hgapPhys, Nat.mul_le_mul_left g hy]

/-! ### The joint-clock starvation producer -/

/-- The starvation stream of the staged Single-B phase is covered by the joint
two-branch clock plus the creation-bad stream. -/
theorem singleBand_hclock_joint
    {n : ℕ} (hn : 2 ≤ n)
    (aLoΛ hiΛ targetΛ D H g cxCap M K T Hocc : ℕ)
    (htargetHi : targetΛ + 1 ≤ hiΛ)
    (hgap : n + D + g ≤ aLoΛ + 1)
    (hsmall : 8 * (hiΛ + cxCap) ≤ 9 * n)
    (hHT : 2 * Hocc ≤ T) (hK : n + 2 * M ≤ K)
    (hH : 0 < H)
    (s₀ : SingleState n) (hcxCap : s₀.1.y + M ≤ cxCap) :
    ∑' q, (if singleBandStarvation aLoΛ targetΛ H M q then
        iter (singleBandStop n hn aLoΛ hiΛ D H) T
          (⟨s₀, 0, 0, 0, 0⟩ : SingleLedger n) q else 0)
      ≤ (1 / (((32 : ℝ≥0∞) / 31) ^ Hocc * (1 / 2) ^ K) +
          singleBlankW n g ^ s₀.1.doubleLevel /
            (singleBlankW n g ^ hiΛ * singleBlankEta n g ^ Hocc))
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
          singleBlankW n g ^ s₀.1.doubleLevel /
            (singleBlankW n g ^ hiΛ * singleBlankEta n g ^ Hocc))
        + ENNReal.ofReal
            (Real.exp (-((D : ℝ) ^ 2 / (2 * (H : ℝ))))) :=
      add_le_add
        (singleBand_joint_clock_tail n hn aLoΛ hiΛ D H g cxCap hgap hsmall
          T Hocc M K hHT hK s₀ hcxCap)
        (singleCreationY_stopped_tail hn aLoΛ hiΛ D H T hH s₀)

/-! ### The rung -/

/-- The explicit error of one concrete joint-clock Single-B band rung, at the
lazy creation budget `H = 128(n+2M)+1`. -/
noncomputable def singleBandJointRungError
    (n g aLoΛ targetΛ D Bw M returnLo bHiRet kRet : ℕ) : ℝ≥0∞ :=
  ((singleRungDirW n g ^ Bw
      + singleRungDirW n g ^ (aLoΛ + Bw) /
        (singleRungDirW n g ^ targetΛ * singleRungDirEta n g ^ M))
    + (singleJointClockEnvelope n g M
        + ENNReal.ofReal
            (Real.exp
              (-((D : ℝ) ^ 2 /
                (2 * ((singleClockHorizon n M + 1 : ℕ) : ℝ)))))))
  + ENNReal.ofReal
      (Real.exp
        (-((D : ℝ) ^ 2 /
          (2 * ((singleClockHorizon n M + 1 : ℕ) : ℝ)))))
  + ((bHiRet : ℝ≥0∞) / (returnLo : ℝ≥0∞)) ^ kRet

/-- One fully instantiated early Single-B band rung with the joint two-branch
clock: γ-free `Θ(n)` horizon, lazy creation budget `H = T+1`, honest direction
constants, and the joint occupation envelope in place of the productive-clock
starvation term.

**SUPERSEDED (2026-07-29):** as landed, this rung routes its return term
through `singleBand_hruin_trivial`, whose ratio is `≥ 1`, so the assembled
error bound is `≥ 1` — true but contentless; and its `x`-floor exit cannot
re-establish a gap checkpoint for chaining.  The live route is the level-form
phase engine (`Tri/SingleBLevelPhase.lean`) + `singleGapRung`
(`Tri/SingleBGapRung.lean`); the occupation-clock tails in this cluster remain
the real content and are consumed there.  Kept for the record; do not build on
it. -/
theorem singleBandJointRung
    (n : ℕ) (hn : 2 ≤ n)
    (g aLoΛ hiΛ targetΛ D Bw M cxCap returnLo bHiRet kRet : ℕ)
    (hg : 0 < g) (hgn : g ≤ 2 * n)
    (hgap : n + D + g ≤ aLoΛ + 1)
    (htargetHi : targetΛ + 1 ≤ hiΛ)
    (htargetGap : n + D + (returnLo + 1) ≤ targetΛ)
    (hsmall : 8 * (hiΛ + cxCap) ≤ 9 * n)
    (hstartClock : aLoΛ + Bw ≤ hiΛ)
    (hwidthClock : hiΛ ≤ aLoΛ + Bw + g)
    (hreturnLo : 0 < returnLo)
    (hleReturn : returnLo ≤ bHiRet) :
    Reaches (singleStateStep n hn) (singleClockHorizon n M)
      (fun s => s.1.doubleLevel = aLoΛ + Bw ∧ s.1.y + M ≤ cxCap)
      (fun s => returnLo + 1 ≤ s.1.x)
      (singleBandJointRungError n g aLoΛ targetΛ D Bw M
        returnLo bHiRet kRet) := by
  have hn0 : 0 < n := by omega
  obtain ⟨hrel, hwη, hη1, hηt, hw1, hw0, hwt, hwv⟩ :=
    singleRungDir_params n g hn0 hg
  have hHpos : 0 < singleClockHorizon n M + 1 := by omega
  have hTH : singleClockHorizon n M < singleClockHorizon n M + 1 := by omega
  have hq : n + g ≠ 0 := by omega
  have hlive :=
    singleBand_hlive_ratio (n := n) (aLoΛ := aLoΛ) (hiΛ := hiΛ) (D := D)
      (H := singleClockHorizon n M + 1) (g := g) hgap
  have hstart : ∀ s : SingleState n,
      (s.1.doubleLevel = aLoΛ + Bw ∧ s.1.y + M ≤ cxCap) →
        s.1.doubleLevel = aLoΛ + Bw := fun s hs => hs.1
  have hexit :
      ∀ q : SingleLedger n,
        targetΛ + q.cx ≤ q.cfg.1.doubleLevel + q.cy →
        ¬ CreationBadY D (singleClockHorizon n M + 1) q →
        ¬ singleCreationBoundary (singleClockHorizon n M + 1) q →
        returnLo + 1 ≤ q.cfg.1.x := by
    intro q hsucc hnotBad hnotBoundary
    have hbudget : q.cx + q.cy ≤ singleClockHorizon n M + 1 := by
      unfold singleCreationBoundary at hnotBoundary
      omega
    have hbal : q.cy ≤ q.cx + D := by
      by_contra hbal
      exact hnotBad ⟨hbudget, by omega⟩
    have hsucc' :
        n + D + (returnLo + 1) + q.cx ≤ q.cfg.1.doubleLevel + q.cy := by
      omega
    have hcorrGap :
        q.cfg.1.y + q.cx + (D + (returnLo + 1)) ≤ q.cfg.1.x + q.cy := by
      have hinv := q.cfg.2
      simp only [BiCfg.doubleLevel] at hsucc'
      simp only [BiCfg.DoubleInv] at hinv
      omega
    have hrec :=
      single_gap_recover (G := D + (returnLo + 1)) (D := D) q hcorrGap hbal
    omega
  have hfailure : ∀ z : SingleState n,
      ¬ (returnLo + 1 ≤ z.1.x) → z.1.x ≤ returnLo := by
    intro z hz
    omega
  have hclock : ∀ s : SingleState n,
      (s.1.doubleLevel = aLoΛ + Bw ∧ s.1.y + M ≤ cxCap) →
      ∑' q, (if singleBandStarvation aLoΛ targetΛ
            (singleClockHorizon n M + 1) M q then
          iter (singleBandStop n hn aLoΛ hiΛ D
            (singleClockHorizon n M + 1)) (singleClockHorizon n M)
            (⟨s, 0, 0, 0, 0⟩ : SingleLedger n) q else 0)
        ≤ singleJointClockEnvelope n g M
          + ENNReal.ofReal
              (Real.exp
                (-((D : ℝ) ^ 2 /
                  (2 * ((singleClockHorizon n M + 1 : ℕ) : ℝ))))) := by
    intro s hs
    have hstarv := singleBand_hclock_joint hn aLoΛ hiΛ targetΛ D
      (singleClockHorizon n M + 1) g cxCap M
      (singleClockBudget n M) (singleClockHorizon n M)
      (singleClockHalfHorizon n M)
      htargetHi hgap hsmall
      (two_singleClockHalfHorizon n M).le le_rfl hHpos s hs.2
    rw [hs.1] at hstarv
    refine hstarv.trans (add_le_add ?_ le_rfl)
    exact singleJointClockError_le n g (aLoΛ + Bw) hiΛ M hn0 hgn
      hstartClock (by omega)
  have hruin :=
    singleBand_hruin_trivial hn aLoΛ hiΛ D (singleClockHorizon n M + 1)
      returnLo bHiRet kRet hreturnLo hleReturn
      (fun s : SingleState n => returnLo + 1 ≤ s.1.x)
  have hr := singleBand_phase_reaches hn
    aLoΛ hiΛ targetΛ D (singleClockHorizon n M + 1) n (n + g) Bw M
    (singleClockHorizon n M) returnLo bHiRet kRet
    hHpos hTH hq
    (singleRungDirW n g) (singleRungDirV n g) (singleRungDirEta n g)
    (singleRungDirU n g)
    (singleJointClockEnvelope n g M
      + ENNReal.ofReal
          (Real.exp
            (-((D : ℝ) ^ 2 /
              (2 * ((singleClockHorizon n M + 1 : ℕ) : ℝ))))))
    rfl hrel hwη hwv hw1 hw0 hη1 hwt hηt
    (fun s => s.1.doubleLevel = aLoΛ + Bw ∧ s.1.y + M ≤ cxCap)
    (fun s => returnLo + 1 ≤ s.1.x)
    hlive hstart hexit hfailure hclock hruin
  simpa only [singleBandJointRungError] using hr

section Inhabitation

example :
    (⟨⟨15, 8, 137⟩, by norm_num [BiCfg.DoubleInv]⟩ :
        SingleState 160).1.doubleLevel = 166 + 1 ∧
      (⟨⟨15, 8, 137⟩, by norm_num [BiCfg.DoubleInv]⟩ :
        SingleState 160).1.y + 1 ≤ 12 := by
  norm_num [BiCfg.doubleLevel]

example :
    Reaches (singleStateStep 160 (by norm_num)) (singleClockHorizon 160 1)
      (fun s : SingleState 160 =>
        s.1.doubleLevel = 166 + 1 ∧ s.1.y + 1 ≤ 12)
      (fun s : SingleState 160 => 1 + 1 ≤ s.1.x)
      (singleBandJointRungError 160 2 166 167 5 1 1 1 1 1) := by
  exact singleBandJointRung 160 (by norm_num)
    2 166 168 167 5 1 1 12 1 1 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

end Inhabitation

end Tri

#print axioms Tri.singleRungDir_params
#print axioms Tri.singleBand_hlive_ratio
#print axioms Tri.singleBand_hclock_joint
#print axioms Tri.singleBandJointRung
