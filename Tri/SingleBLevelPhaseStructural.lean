/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.SingleBLevelPhase

/-!
# Structural-budget Single-B level phase

This file keeps the creation boundary as an explicit stopped event.  Boundary
mass is not discarded by a lazy `T < H` budget; instead, the boundary part that
is still below a higher corrected-level deadline is routed to a second
resolution-deadline stream.
-/

namespace Tri

open scoped ENNReal

variable {n : ℕ}

/-- Structural level exception: creation imbalance in either direction, or the
creation boundary while the corrected level is still below the high deadline. -/
def SingleLevelStructuralExc (D D₂ H Lhi : ℕ) (q : SingleLedger n) : Prop :=
  (D + q.cx ≤ q.cy) ∨ (D₂ + q.cy ≤ q.cx) ∨
    (singleCreationBoundary H q ∧ singleCorrectedBelow Lhi q)

instance (D D₂ H Lhi : ℕ) :
    DecidablePred (SingleLevelStructuralExc D D₂ H Lhi (n := n)) :=
  fun _ => inferInstanceAs (Decidable (_ ∨ _ ∨ _))

/-- The stopped Single-B band preserves the corrected `Y` coordinate on
one-step support. -/
theorem singleBandStop_correctedY_of_apply_ne_zero {n y₀ : ℕ} (hn : 2 ≤ n)
    (aLoΛ hiΛ D H : ℕ) (q z : SingleLedger n)
    (hy : q.CorrectedY y₀)
    (hqz : singleBandStop n hn aLoΛ hiΛ D H q z ≠ 0) :
    z.CorrectedY y₀ := by
  unfold singleBandStop freeze at hqz
  by_cases hB : SingleBandFrozen n aLoΛ hiΛ D H q
  · rw [if_pos hB, PMF.pure_apply] at hqz
    by_cases hzq : z = q
    · rwa [hzq]
    · simp [hzq] at hqz
  · rw [if_neg hB] at hqz
    exact singleLedgerStep_correctedY_of_apply_ne_zero hn q hy z hqz

/-- The stopped Single-B band preserves the corrected `Y` coordinate along every
finite supported trajectory. -/
theorem singleBandStop_iter_correctedY {n y₀ T : ℕ} (hn : 2 ≤ n)
    (aLoΛ hiΛ D H : ℕ) (q z : SingleLedger n)
    (hy : q.CorrectedY y₀)
    (hz : iter (singleBandStop n hn aLoΛ hiΛ D H) T q z ≠ 0) :
    z.CorrectedY y₀ :=
  iter_support_closed (singleBandStop n hn aLoΛ hiΛ D H)
    (SingleLedger.CorrectedY y₀)
    (fun a ha z haz =>
      singleBandStop_correctedY_of_apply_ne_zero hn aLoΛ hiΛ D H a z ha haz)
    T q z hy hz

/-- Boundary states outside the `Y`-heavy creation tail have already spent the
resolution quota, provided the structural creation boundary is above the current
co-level cap. -/
theorem singleBand_boundary_deadline_of_start_co {n T : ℕ} (hn : 2 ≤ n)
    (aLoΛ hiΛ D H P M : ℕ) (s : SingleState n) (q : SingleLedger n)
    (hco : s.1.doubleCoLevel ≤ P)
    (hH : P + 2 * M + D + 1 ≤ H)
    (hz : iter (singleBandStop n hn aLoΛ hiΛ D H) T
      (⟨s, 0, 0, 0, 0⟩ : SingleLedger n) q ≠ 0)
    (hnotBad : ¬ D + q.cx ≤ q.cy)
    (hboundary : singleCreationBoundary H q) :
    M ≤ q.rx + q.ry := by
  have hy : q.CorrectedY s.1.y :=
    singleBandStop_iter_correctedY hn aLoΛ hiΛ D H
      (⟨s, 0, 0, 0, 0⟩ : SingleLedger n) q
      (SingleLedger.initial_correctedY s) hz
  have hcy : q.cy ≤ D + q.cx := by omega
  have hcx : q.cx ≤ s.1.y + q.ry := by
    simp only [SingleLedger.CorrectedY] at hy
    omega
  have hstartY : 2 * s.1.y ≤ P := by
    simp only [BiCfg.doubleCoLevel] at hco
    omega
  have hboundary' : H ≤ q.cx + q.cy := by
    simpa [singleCreationBoundary] using hboundary
  have hupper : q.cx + q.cy ≤ P + 2 * q.ry + D := by
    omega
  have hquota : P + 2 * M + D + 1 ≤ P + 2 * q.ry + D :=
    hH.trans (hboundary'.trans hupper)
  omega

/-- Failure outside the structural exception is covered by corrected-level
failure, raw `Y`-creation imbalance, boundary-below-high, or the mirror raw
`X`-creation imbalance. -/
theorem singleLevelStructural_failure_split
    (D D₂ H Lexit Lhi : ℕ) (q : SingleLedger n)
    (hLhi : Lexit + D ≤ Lhi)
    (h : ¬ ((Lexit ≤ q.cfg.1.doubleLevel) ∧
        ¬ SingleLevelStructuralExc D D₂ H Lhi q)) :
    (singleCorrectedBelow (Lexit + D) q ∨ (D + q.cx ≤ q.cy) ∨
        (singleCreationBoundary H q ∧ singleCorrectedBelow Lhi q)) ∨
      (D₂ + q.cy ≤ q.cx) := by
  by_cases hE2 : D₂ + q.cy ≤ q.cx
  · exact Or.inr hE2
  by_cases hBoundaryBelow :
      singleCreationBoundary H q ∧ singleCorrectedBelow Lhi q
  · exact Or.inl (Or.inr (Or.inr hBoundaryBelow))
  by_cases hE1 : D + q.cx ≤ q.cy
  · exact Or.inl (Or.inr (Or.inl hE1))
  have hnE : ¬ SingleLevelStructuralExc D D₂ H Lhi q := by
    unfold SingleLevelStructuralExc
    tauto
  have hnA : ¬ Lexit ≤ q.cfg.1.doubleLevel := by
    intro hA
    exact h ⟨hA, hnE⟩
  by_cases hBoundary : singleCreationBoundary H q
  · have hnotBelow : ¬ singleCorrectedBelow Lhi q := by
      intro hbelow
      exact hBoundaryBelow ⟨hBoundary, hbelow⟩
    have hgt : Lhi + q.cx < q.cfg.1.doubleLevel + q.cy := by
      unfold singleCorrectedBelow at hnotBelow
      exact Nat.lt_of_not_ge hnotBelow
    have hcy : q.cy < D + q.cx := by omega
    have hexit : Lexit ≤ q.cfg.1.doubleLevel := by omega
    exact False.elim (hnA hexit)
  · left
    left
    unfold singleCorrectedBelow
    omega

/-- Stopped-band structural split.  Boundary-below-high is charged to a second
deadline stream supplied by `hboundaryDeadline`. -/
theorem singleBand_split_structural {n : ℕ} (hn : 2 ≤ n)
    (aLoΛ hiΛ targetΛ D H M T Lhi Mhi : ℕ) (s₀ : SingleState n)
    (htargetLhi : targetΛ ≤ Lhi)
    (hboundaryDeadline : ∀ q : SingleLedger n,
      iter (singleBandStop n hn aLoΛ hiΛ D H) T
          (⟨s₀, 0, 0, 0, 0⟩ : SingleLedger n) q ≠ 0 →
        ¬ D + q.cx ≤ q.cy →
        singleCreationBoundary H q → singleCorrectedBelow Lhi q →
          Mhi ≤ q.rx + q.ry) :
    ∑' q, (if singleCorrectedBelow targetΛ q ∨ (D + q.cx ≤ q.cy) ∨
          (singleCreationBoundary H q ∧ singleCorrectedBelow Lhi q) then
        iter (singleBandStop n hn aLoΛ hiΛ D H) T
          (⟨s₀, 0, 0, 0, 0⟩ : SingleLedger n) q else 0)
      ≤ (∑' q, (if singleCorrectedBelow aLoΛ q then
            iter (singleBandStop n hn aLoΛ hiΛ D H) T
              (⟨s₀, 0, 0, 0, 0⟩ : SingleLedger n) q else 0))
        + (∑' q, (if singleCorrectedBelow targetΛ q ∧ M ≤ q.rx + q.ry then
            iter (singleBandStop n hn aLoΛ hiΛ D H) T
              (⟨s₀, 0, 0, 0, 0⟩ : SingleLedger n) q else 0))
        + (∑' q, (if singleBandStarvation aLoΛ targetΛ H M q then
            iter (singleBandStop n hn aLoΛ hiΛ D H) T
              (⟨s₀, 0, 0, 0, 0⟩ : SingleLedger n) q else 0))
        + (∑' q, (if CreationBadY D H q then
            iter (singleBandStop n hn aLoΛ hiΛ D H) T
              (⟨s₀, 0, 0, 0, 0⟩ : SingleLedger n) q else 0))
        + (∑' q, (if singleCorrectedBelow Lhi q ∧ Mhi ≤ q.rx + q.ry then
            iter (singleBandStop n hn aLoΛ hiΛ D H) T
              (⟨s₀, 0, 0, 0, 0⟩ : SingleLedger n) q else 0)) := by
  rw [← ENNReal.tsum_add, ← ENNReal.tsum_add, ← ENNReal.tsum_add,
    ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun q => ?_
  set μ := iter (singleBandStop n hn aLoΛ hiΛ D H) T
    (⟨s₀, 0, 0, 0, 0⟩ : SingleLedger n) q with hμ
  by_cases hfail : singleCorrectedBelow targetΛ q ∨ (D + q.cx ≤ q.cy) ∨
      (singleCreationBoundary H q ∧ singleCorrectedBelow Lhi q)
  · rw [if_pos hfail]
    by_cases hlow : singleCorrectedBelow aLoΛ q
    · rw [if_pos hlow]
      calc
        μ ≤ μ + (if singleCorrectedBelow targetΛ q ∧ M ≤ q.rx + q.ry then
              μ else 0) := self_le_add_right _ _
        _ ≤ (μ + (if singleCorrectedBelow targetΛ q ∧ M ≤ q.rx + q.ry then
              μ else 0)) +
            (if singleBandStarvation aLoΛ targetΛ H M q then μ else 0) :=
          self_le_add_right _ _
        _ ≤ ((μ + (if singleCorrectedBelow targetΛ q ∧ M ≤ q.rx + q.ry then
              μ else 0)) +
            (if singleBandStarvation aLoΛ targetΛ H M q then μ else 0)) +
            (if CreationBadY D H q then μ else 0) :=
          self_le_add_right _ _
        _ ≤ (((μ + (if singleCorrectedBelow targetΛ q ∧ M ≤ q.rx + q.ry then
              μ else 0)) +
            (if singleBandStarvation aLoΛ targetΛ H M q then μ else 0)) +
            (if CreationBadY D H q then μ else 0)) +
            (if singleCorrectedBelow Lhi q ∧ Mhi ≤ q.rx + q.ry then
              μ else 0) :=
          self_le_add_right _ _
    · rw [if_neg hlow]
      by_cases hrawBad : D + q.cx ≤ q.cy
      · by_cases hμ0 : μ = 0
        · rw [hμ0]
          positivity
        · have hcap : q.cx + q.cy ≤ H := by
            exact singleBandStop_creation_cap_fresh hn aLoΛ hiΛ D H s₀ q
              (by simpa [hμ] using hμ0)
          have hbad : CreationBadY D H q := ⟨hcap, hrawBad⟩
          rw [if_pos hbad]
          simp only [zero_add]
          calc
            μ ≤ ((if singleCorrectedBelow targetΛ q ∧ M ≤ q.rx + q.ry then
                  μ else 0) +
                (if singleBandStarvation aLoΛ targetΛ H M q then μ else 0)) +
                μ := self_le_add_left _ _
            _ ≤ (((if singleCorrectedBelow targetΛ q ∧ M ≤ q.rx + q.ry then
                  μ else 0) +
                (if singleBandStarvation aLoΛ targetΛ H M q then μ else 0)) +
                μ) +
                (if singleCorrectedBelow Lhi q ∧ Mhi ≤ q.rx + q.ry then
                  μ else 0) := self_le_add_right _ _
      · by_cases hBoundaryBelow :
            singleCreationBoundary H q ∧ singleCorrectedBelow Lhi q
        · by_cases hμ0 : μ = 0
          · rw [hμ0]
            positivity
          · have hresHi : Mhi ≤ q.rx + q.ry :=
              hboundaryDeadline q (by simpa [hμ] using hμ0)
                hrawBad hBoundaryBelow.1 hBoundaryBelow.2
            have hhi :
                (if singleCorrectedBelow Lhi q ∧ Mhi ≤ q.rx + q.ry then
                    μ else 0) = μ := by
              rw [if_pos ⟨hBoundaryBelow.2, hresHi⟩]
            rw [hhi]
            exact self_le_add_left _ _
        · have hcorr : singleCorrectedBelow targetΛ q := by
            rcases hfail with hcorr | hrest
            · exact hcorr
            · rcases hrest with hraw | hb
              · exact absurd hraw hrawBad
              · exact absurd hb hBoundaryBelow
          by_cases hres : M ≤ q.rx + q.ry
          · rw [if_pos ⟨hcorr, hres⟩]
            simp only [zero_add]
            calc
              μ ≤ μ + (if singleBandStarvation aLoΛ targetΛ H M q then
                    μ else 0) := self_le_add_right _ _
              _ ≤ (μ + (if singleBandStarvation aLoΛ targetΛ H M q then
                    μ else 0)) +
                  (if CreationBadY D H q then μ else 0) :=
                self_le_add_right _ _
              _ ≤ ((μ + (if singleBandStarvation aLoΛ targetΛ H M q then
                    μ else 0)) +
                  (if CreationBadY D H q then μ else 0)) +
                  (if singleCorrectedBelow Lhi q ∧ Mhi ≤ q.rx + q.ry then
                    μ else 0) :=
                self_le_add_right _ _
          · have hnotBoundary : ¬ singleCreationBoundary H q := by
              intro hBoundary
              have hbelowHi : singleCorrectedBelow Lhi q := by
                unfold singleCorrectedBelow at hcorr ⊢
                omega
              exact hBoundaryBelow ⟨hBoundary, hbelowHi⟩
            have hnotBoundaryLt : q.cx + q.cy < H := by
              unfold singleCreationBoundary at hnotBoundary
              exact Nat.lt_of_not_ge hnotBoundary
            have hstarve : singleBandStarvation aLoΛ targetΛ H M q := by
              simp only [singleBandStarvation]
              simp only [singleCorrectedBelow] at hlow hcorr
              constructor
              · omega
              · exact ⟨hcorr, by omega, hnotBoundaryLt⟩
            rw [if_neg (by intro h; exact hres h.2), if_pos hstarve]
            simp only [zero_add]
            calc
              μ ≤ (0 + μ) := by simp
              _ ≤ (0 + μ) + (if CreationBadY D H q then μ else 0) :=
                self_le_add_right _ _
              _ ≤ ((0 + μ) + (if CreationBadY D H q then μ else 0)) +
                  (if singleCorrectedBelow Lhi q ∧ Mhi ≤ q.rx + q.ry then
                    μ else 0) :=
                self_le_add_right _ _
              _ = (μ + (if CreationBadY D H q then μ else 0)) +
                  (if singleCorrectedBelow Lhi q ∧ Mhi ≤ q.rx + q.ry then
                    μ else 0) := by simp
  · simp [hfail]

/-- Structural stopped phase failure bound.  The last term is the second
deadline stream that absorbs boundary-below-high states. -/
theorem singleBand_phase_fail_structural {n : ℕ} (hn : 2 ≤ n)
    (aLoΛ hiΛ targetΛ D H p qRat Bw M T Lhi Mhi : ℕ) (hH : 0 < H)
    (hq : qRat ≠ 0) (w v η u ε_clock : ℝ≥0∞)
    (hu : u = (p : ℝ≥0∞) / (qRat : ℝ≥0∞))
    (hrel : η * (u + w ^ 2) = w * (u + 1)) (hwη : w ≤ η)
    (hwv : w * v = 1) (hw1 : w ≤ 1) (hw0 : w ≠ 0)
    (hη1 : 1 ≤ η) (hwt : w ≠ ⊤) (hηt : η ≠ ⊤)
    (hlive : ∀ q, ¬ SingleBandFrozen n aLoΛ hiΛ D H q →
      ∃ a : ℕ, q.CorrectedLevel (a + 1) ∧
        qRat * q.cfg.1.y ≤ p * q.cfg.1.x)
    (s₀ : SingleState n)
    (hstart : s₀.1.doubleLevel = aLoΛ + Bw)
    (htargetLhi : targetΛ ≤ Lhi)
    (hboundaryDeadline : ∀ q : SingleLedger n,
      iter (singleBandStop n hn aLoΛ hiΛ D H) T
          (⟨s₀, 0, 0, 0, 0⟩ : SingleLedger n) q ≠ 0 →
        ¬ D + q.cx ≤ q.cy →
        singleCreationBoundary H q → singleCorrectedBelow Lhi q →
          Mhi ≤ q.rx + q.ry)
    (hclock :
      ∑' q, (if singleBandStarvation aLoΛ targetΛ H M q then
          iter (singleBandStop n hn aLoΛ hiΛ D H) T
            (⟨s₀, 0, 0, 0, 0⟩ : SingleLedger n) q else 0)
        ≤ ε_clock) :
    ∑' q, (if singleCorrectedBelow targetΛ q ∨ (D + q.cx ≤ q.cy) ∨
          (singleCreationBoundary H q ∧ singleCorrectedBelow Lhi q) then
        iter (singleBandStop n hn aLoΛ hiΛ D H) T
          (⟨s₀, 0, 0, 0, 0⟩ : SingleLedger n) q else 0)
      ≤ (((w ^ Bw + w ^ (aLoΛ + Bw) / (w ^ targetΛ * η ^ M))
          + ε_clock)
        + ENNReal.ofReal (Real.exp (-((D : ℝ) ^ 2 / (2 * (H : ℝ)))))
        + w ^ (aLoΛ + Bw) / (w ^ Lhi * η ^ Mhi)) := by
  have hsplit := singleBand_split_structural hn aLoΛ hiΛ targetΛ D H M T
    Lhi Mhi s₀ htargetLhi hboundaryDeadline
  have hback :
      (∑' q, (if singleCorrectedBelow aLoΛ q then
          iter (singleBandStop n hn aLoΛ hiΛ D H) T
            (⟨s₀, 0, 0, 0, 0⟩ : SingleLedger n) q else 0))
        ≤ w ^ Bw := by
    simpa [singleCorrectedBelow] using
      singleWindow_backslide_tail hn aLoΛ hiΛ D H p qRat Bw T hq
        w v η u hu hrel hwη hwv hw1 hw0 hη1 hwt hηt hlive s₀ hstart
  have hdead :
      (∑' q, (if singleCorrectedBelow targetΛ q ∧ M ≤ q.rx + q.ry then
          iter (singleBandStop n hn aLoΛ hiΛ D H) T
            (⟨s₀, 0, 0, 0, 0⟩ : SingleLedger n) q else 0))
        ≤ w ^ (aLoΛ + Bw) / (w ^ targetΛ * η ^ M) := by
    have hmain := singleBandWindow_tail hn aLoΛ hiΛ D H p qRat targetΛ M T hq
      w v η u hu hrel hwη hwv hw1 hw0 hη1 hwt hηt hlive s₀
    simpa [singleCorrectedBelow, hstart] using hmain
  have hbad := singleCreationY_stopped_tail hn aLoΛ hiΛ D H T hH s₀
  have hdeadHi :
      (∑' q, (if singleCorrectedBelow Lhi q ∧ Mhi ≤ q.rx + q.ry then
          iter (singleBandStop n hn aLoΛ hiΛ D H) T
            (⟨s₀, 0, 0, 0, 0⟩ : SingleLedger n) q else 0))
        ≤ w ^ (aLoΛ + Bw) / (w ^ Lhi * η ^ Mhi) := by
    have hmain := singleBandWindow_tail hn aLoΛ hiΛ D H p qRat Lhi Mhi T hq
      w v η u hu hrel hwη hwv hw1 hw0 hη1 hwt hηt hlive s₀
    simpa [singleCorrectedBelow, hstart] using hmain
  calc
    ∑' q, (if singleCorrectedBelow targetΛ q ∨ (D + q.cx ≤ q.cy) ∨
          (singleCreationBoundary H q ∧ singleCorrectedBelow Lhi q) then
        iter (singleBandStop n hn aLoΛ hiΛ D H) T
          (⟨s₀, 0, 0, 0, 0⟩ : SingleLedger n) q else 0)
        ≤ (∑' q, (if singleCorrectedBelow aLoΛ q then
              iter (singleBandStop n hn aLoΛ hiΛ D H) T
                (⟨s₀, 0, 0, 0, 0⟩ : SingleLedger n) q else 0))
          + (∑' q, (if singleCorrectedBelow targetΛ q ∧ M ≤ q.rx + q.ry then
              iter (singleBandStop n hn aLoΛ hiΛ D H) T
                (⟨s₀, 0, 0, 0, 0⟩ : SingleLedger n) q else 0))
          + (∑' q, (if singleBandStarvation aLoΛ targetΛ H M q then
              iter (singleBandStop n hn aLoΛ hiΛ D H) T
                (⟨s₀, 0, 0, 0, 0⟩ : SingleLedger n) q else 0))
          + (∑' q, (if CreationBadY D H q then
              iter (singleBandStop n hn aLoΛ hiΛ D H) T
                (⟨s₀, 0, 0, 0, 0⟩ : SingleLedger n) q else 0))
          + (∑' q, (if singleCorrectedBelow Lhi q ∧ Mhi ≤ q.rx + q.ry then
              iter (singleBandStop n hn aLoΛ hiΛ D H) T
                (⟨s₀, 0, 0, 0, 0⟩ : SingleLedger n) q else 0)) := hsplit
    _ ≤ (((w ^ Bw + w ^ (aLoΛ + Bw) / (w ^ targetΛ * η ^ M))
          + ε_clock)
        + ENNReal.ofReal (Real.exp (-((D : ℝ) ^ 2 / (2 * (H : ℝ)))))
        + w ^ (aLoΛ + Bw) / (w ^ Lhi * η ^ Mhi)) := by
      exact add_le_add (add_le_add (add_le_add (add_le_add hback hdead)
        hclock) hbad) hdeadHi

/-- Explicit error of one structural level-form Single-B band phase. -/
noncomputable def singleLevelPhaseStructuralError
    (w η : ℝ≥0∞) (Bw Lentry targetΛ M : ℕ) (ε_clock : ℝ≥0∞)
    (D D₂ H : ℕ) (Bret sret T n : ℕ) (ε : ℝ≥0∞)
    (Lhi Mhi : ℕ) : ℝ≥0∞ :=
  ((((w ^ Bw + w ^ Lentry / (w ^ targetΛ * η ^ M)) + ε_clock)
    + ENNReal.ofReal (Real.exp (-((D : ℝ) ^ 2 / (2 * (H : ℝ)))))
    + w ^ Lentry / (w ^ Lhi * η ^ Mhi))
    + ENNReal.ofReal (Real.exp (-((D₂ : ℝ) ^ 2 / (2 * (H : ℝ))))))
    + (1 + ε ^ 2 * ((Bret : ℝ≥0∞) / ((n - 1 : ℕ) : ℝ≥0∞))) ^ T /
        (1 + ε) ^ (sret + 1)

/-- Structural level-form reachability.  It replaces the lazy boundary-zero
side condition by a high corrected-level deadline stream. -/
theorem singleBand_reaches_level_structural
    (hn : 2 ≤ n)
    (aLoΛ hiΛ D D₂ H p qRat Bw M T Lentry Lexit sret Bret Lhi Mhi : ℕ)
    (hH : 0 < H) (hq : qRat ≠ 0)
    (w v η u ε_clock : ℝ≥0∞) (ε : ℝ≥0∞) (hε1 : ε ≤ 1)
    (hu : u = (p : ℝ≥0∞) / (qRat : ℝ≥0∞))
    (hrel : η * (u + w ^ 2) = w * (u + 1)) (hwη : w ≤ η)
    (hwv : w * v = 1) (hw1 : w ≤ 1) (hw0 : w ≠ 0)
    (hη1 : 1 ≤ η) (hwt : w ≠ ⊤) (hηt : η ≠ ⊤)
    (hlive : ∀ q, ¬ SingleBandFrozen n aLoΛ hiΛ D H q →
      ∃ a : ℕ, q.CorrectedLevel (a + 1) ∧
        qRat * q.cfg.1.y ≤ p * q.cfg.1.x)
    (hBw : aLoΛ + Bw = Lentry)
    (hvac : aLoΛ + D₂ ≤ Lexit)
    (hLn : n + 1 ≤ Lexit)
    (hBret : Lexit + Bret = 2 * n + 1)
    (hslack : Lexit + sret + D ≤ hiΛ)
    (hLhiReturn : Lexit + sret + D ≤ Lhi)
    (hboundaryDeadline : ∀ s : SingleState n, Lentry ≤ s.1.doubleLevel →
      ∀ q : SingleLedger n,
        iter (singleBandStop n hn aLoΛ hiΛ D H) T
            (⟨s, 0, 0, 0, 0⟩ : SingleLedger n) q ≠ 0 →
          ¬ D + q.cx ≤ q.cy →
          singleCreationBoundary H q → singleCorrectedBelow Lhi q →
            Mhi ≤ q.rx + q.ry)
    (hclock : ∀ s : SingleState n, Lentry ≤ s.1.doubleLevel →
      ∑' q, (if singleBandStarvation aLoΛ (Lexit + D) H M q then
          iter (singleBandStop n hn aLoΛ hiΛ D H) T
            (⟨s, 0, 0, 0, 0⟩ : SingleLedger n) q else 0)
        ≤ ε_clock) :
    Reaches (singleStateStep n hn) T
      (fun s => Lentry ≤ s.1.doubleLevel)
      (fun s => Lexit ≤ s.1.doubleLevel)
      (singleLevelPhaseStructuralError w η Bw Lentry (Lexit + D) M ε_clock
        D D₂ H Bret sret T n ε Lhi Mhi) := by
  intro s hs
  obtain ⟨d, hd⟩ : ∃ d, s.1.doubleLevel = Lentry + d :=
    ⟨s.1.doubleLevel - Lentry, by omega⟩
  set q₀ : SingleLedger n := ⟨s, 0, 0, 0, 0⟩ with hq₀
  have hreturn : ∀ q : SingleLedger n,
      SingleBandFrozen n aLoΛ hiΛ D H q →
      (fun r : SingleLedger n => Lexit ≤ r.cfg.1.doubleLevel) q →
      ¬ SingleLevelStructuralExc D D₂ H Lhi q → ∀ U, U ≤ T →
      (∑' z, if Lexit ≤ z.cfg.1.doubleLevel then 0
          else iter (singleLedgerStep n hn) U q z) ≤
        (1 + ε ^ 2 * ((Bret : ℝ≥0∞) / ((n - 1 : ℕ) : ℝ≥0∞))) ^ T /
          (1 + ε) ^ (sret + 1) := by
    intro q hfr hA hE U hUT
    have hlevel : Lexit + sret ≤ q.cfg.1.doubleLevel := by
      rcases hfr with hLow | hHigh | hBad | hBoundary
      · exfalso
        have hnE2 : ¬ (D₂ + q.cy ≤ q.cx) := fun h =>
          hE (Or.inr (Or.inl h))
        change Lexit ≤ q.cfg.1.doubleLevel at hA
        omega
      · have hnE1 : ¬ (D + q.cx ≤ q.cy) := fun h => hE (Or.inl h)
        omega
      · exact absurd (Or.inl hBad.2) hE
      · have hnE1 : ¬ (D + q.cx ≤ q.cy) := fun h => hE (Or.inl h)
        have hnotBelow : ¬ singleCorrectedBelow Lhi q := by
          intro hbelow
          exact hE (Or.inr (Or.inr ⟨hBoundary, hbelow⟩))
        have hgt : Lhi + q.cx < q.cfg.1.doubleLevel + q.cy := by
          unfold singleCorrectedBelow at hnotBelow
          exact Nat.lt_of_not_ge hnotBelow
        omega
    have hconv :
        (∑' z, if Lexit ≤ z.cfg.1.doubleLevel then 0
            else iter (singleLedgerStep n hn) U q z) =
          ∑' z : SingleState n, if Lexit ≤ z.1.doubleLevel then 0
            else iter (singleStateStep n hn) U q.cfg z :=
      (singleState_failure_eq_ledger n hn U q
        (fun z : SingleState n => Lexit ≤ z.1.doubleLevel)).symm
    rw [hconv]
    exact singleCo_return_raw n hn Lexit sret T U Bret hUT hLn hBret
      ε hε1 q.cfg hlevel
  have htransfer :=
    failure_le_failure_freeze_add_exc
      (B := SingleBandFrozen n aLoΛ hiΛ D H)
      (A := fun q : SingleLedger n => Lexit ≤ q.cfg.1.doubleLevel)
      (E := SingleLevelStructuralExc D D₂ H Lhi)
      (K := singleLedgerStep n hn)
      (δ := (1 + ε ^ 2 * ((Bret : ℝ≥0∞) / ((n - 1 : ℕ) : ℝ≥0∞))) ^ T /
        (1 + ε) ^ (sret + 1))
      (T := T) hreturn T le_rfl q₀
  have htargetLhi : Lexit + D ≤ Lhi := by omega
  have hstopped :
      (∑' q, if (Lexit ≤ q.cfg.1.doubleLevel) ∧
          ¬ SingleLevelStructuralExc D D₂ H Lhi q then 0
          else iter (freeze (SingleBandFrozen n aLoΛ hiΛ D H)
            (singleLedgerStep n hn)) T q₀ q) ≤
        (∑' q, (if singleCorrectedBelow (Lexit + D) q ∨
              (D + q.cx ≤ q.cy) ∨
              (singleCreationBoundary H q ∧ singleCorrectedBelow Lhi q) then
            iter (singleBandStop n hn aLoΛ hiΛ D H) T q₀ q else 0))
          + (∑' q, (if CreationBad D₂ H q then
              iter (singleBandStop n hn aLoΛ hiΛ D H) T q₀ q else 0)) := by
    rw [← ENNReal.tsum_add]
    refine ENNReal.tsum_le_tsum fun q => ?_
    by_cases hA' : (Lexit ≤ q.cfg.1.doubleLevel) ∧
        ¬ SingleLevelStructuralExc D D₂ H Lhi q
    · simp [hA']
    · have hsplit :=
        singleLevelStructural_failure_split D D₂ H Lexit Lhi q htargetLhi hA'
      have hKeq : iter (freeze (SingleBandFrozen n aLoΛ hiΛ D H)
          (singleLedgerStep n hn)) T q₀ q =
          iter (singleBandStop n hn aLoΛ hiΛ D H) T q₀ q := rfl
      rw [if_neg hA', hKeq]
      rcases hsplit with hmain | hE2
      · calc
          iter (singleBandStop n hn aLoΛ hiΛ D H) T q₀ q
              = (if singleCorrectedBelow (Lexit + D) q ∨
                  (D + q.cx ≤ q.cy) ∨
                  (singleCreationBoundary H q ∧ singleCorrectedBelow Lhi q)
                then iter (singleBandStop n hn aLoΛ hiΛ D H) T q₀ q else 0) := by
            rw [if_pos hmain]
          _ ≤ _ := le_add_right le_rfl
      · by_cases hmass :
            iter (singleBandStop n hn aLoΛ hiΛ D H) T q₀ q = 0
        · rw [hmass]
          exact bot_le
        · have hbudget :=
            singleBandStop_creation_cap_fresh hn aLoΛ hiΛ D H s q
              (by simpa [hq₀] using hmass)
          have hbad2 : CreationBad D₂ H q := ⟨hbudget, hE2⟩
          calc
            iter (singleBandStop n hn aLoΛ hiΛ D H) T q₀ q
                = (if CreationBad D₂ H q then
                  iter (singleBandStop n hn aLoΛ hiΛ D H) T q₀ q else 0) := by
              rw [if_pos hbad2]
            _ ≤ _ := le_add_left le_rfl
  have hphase := singleBand_phase_fail_structural hn aLoΛ hiΛ (Lexit + D)
    D H p qRat (Bw + d) M T Lhi Mhi hH hq w v η u ε_clock
    hu hrel hwη hwv hw1 hw0 hη1 hwt hηt hlive s (by omega)
    htargetLhi (hboundaryDeadline s hs) (hclock s hs)
  have hmirror := singleCreationX_stopped_tail hn aLoΛ hiΛ D H D₂ T hH s
  have hmono :
      (w ^ (Bw + d) + w ^ (aLoΛ + (Bw + d)) /
          (w ^ (Lexit + D) * η ^ M)) ≤
        w ^ Bw + w ^ Lentry / (w ^ (Lexit + D) * η ^ M) := by
    apply add_le_add
    · exact pow_le_pow_right_of_le_one' hw1 (by omega)
    · exact ENNReal.div_le_div_right
        (pow_le_pow_right_of_le_one' hw1 (by omega)) _
  have hmonoHi :
      w ^ (aLoΛ + (Bw + d)) / (w ^ Lhi * η ^ Mhi) ≤
        w ^ Lentry / (w ^ Lhi * η ^ Mhi) := by
    exact ENNReal.div_le_div_right
      (pow_le_pow_right_of_le_one' hw1 (by omega)) _
  have hphaseMono :
      w ^ (Bw + d) + w ^ (aLoΛ + (Bw + d)) /
              (w ^ (Lexit + D) * η ^ M) + ε_clock
          + ENNReal.ofReal (Real.exp (-((D : ℝ) ^ 2 / (2 * (H : ℝ)))))
          + w ^ (aLoΛ + (Bw + d)) / (w ^ Lhi * η ^ Mhi)
        ≤ w ^ Bw + w ^ Lentry / (w ^ (Lexit + D) * η ^ M) + ε_clock
          + ENNReal.ofReal (Real.exp (-((D : ℝ) ^ 2 / (2 * (H : ℝ)))))
          + w ^ Lentry / (w ^ Lhi * η ^ Mhi) := by
    exact add_le_add (add_le_add (add_le_add hmono le_rfl) le_rfl) hmonoHi
  have hfail :
      (∑' z, if Lexit ≤ z.1.doubleLevel then 0
          else iter (singleStateStep n hn) T s z) =
        ∑' q, if Lexit ≤ q.cfg.1.doubleLevel then 0
          else iter (singleLedgerStep n hn) T q₀ q :=
    singleState_failure_eq_ledger n hn T q₀
      (fun z : SingleState n => Lexit ≤ z.1.doubleLevel)
  unfold singleLevelPhaseStructuralError
  calc
    (∑' z, if Lexit ≤ z.1.doubleLevel then 0
        else iter (singleStateStep n hn) T s z)
        = ∑' q, if Lexit ≤ q.cfg.1.doubleLevel then 0
            else iter (singleLedgerStep n hn) T q₀ q := hfail
    _ ≤ (∑' q, if (Lexit ≤ q.cfg.1.doubleLevel) ∧
            ¬ SingleLevelStructuralExc D D₂ H Lhi q then 0
            else iter (freeze (SingleBandFrozen n aLoΛ hiΛ D H)
              (singleLedgerStep n hn)) T q₀ q)
          + (1 + ε ^ 2 * ((Bret : ℝ≥0∞) / ((n - 1 : ℕ) : ℝ≥0∞))) ^ T /
              (1 + ε) ^ (sret + 1) := htransfer
    _ ≤ ((∑' q, (if singleCorrectedBelow (Lexit + D) q ∨
              (D + q.cx ≤ q.cy) ∨
              (singleCreationBoundary H q ∧ singleCorrectedBelow Lhi q) then
            iter (singleBandStop n hn aLoΛ hiΛ D H) T q₀ q else 0))
          + (∑' q, (if CreationBad D₂ H q then
              iter (singleBandStop n hn aLoΛ hiΛ D H) T q₀ q else 0)))
          + (1 + ε ^ 2 * ((Bret : ℝ≥0∞) / ((n - 1 : ℕ) : ℝ≥0∞))) ^ T /
              (1 + ε) ^ (sret + 1) :=
      add_le_add hstopped le_rfl
    _ ≤ ((((w ^ (Bw + d) + w ^ (aLoΛ + (Bw + d)) /
              (w ^ (Lexit + D) * η ^ M)) + ε_clock)
          + ENNReal.ofReal (Real.exp (-((D : ℝ) ^ 2 / (2 * (H : ℝ)))))
          + w ^ (aLoΛ + (Bw + d)) / (w ^ Lhi * η ^ Mhi))
          + ENNReal.ofReal (Real.exp (-((D₂ : ℝ) ^ 2 / (2 * (H : ℝ)))))
          + (1 + ε ^ 2 * ((Bret : ℝ≥0∞) / ((n - 1 : ℕ) : ℝ≥0∞))) ^ T /
              (1 + ε) ^ (sret + 1)) :=
      add_le_add (add_le_add hphase hmirror) le_rfl
    _ ≤ ((((w ^ Bw + w ^ Lentry /
              (w ^ (Lexit + D) * η ^ M)) + ε_clock)
          + ENNReal.ofReal (Real.exp (-((D : ℝ) ^ 2 / (2 * (H : ℝ)))))
          + w ^ Lentry / (w ^ Lhi * η ^ Mhi))
          + ENNReal.ofReal (Real.exp (-((D₂ : ℝ) ^ 2 / (2 * (H : ℝ)))))
          + (1 + ε ^ 2 * ((Bret : ℝ≥0∞) / ((n - 1 : ℕ) : ℝ≥0∞))) ^ T /
              (1 + ε) ^ (sret + 1)) :=
      add_le_add (add_le_add hphaseMono le_rfl) le_rfl

section Inhabitation

example :
    let q : SingleLedger 8 :=
      { cfg := ⟨⟨3, 2, 3⟩, by norm_num [BiCfg.DoubleInv]⟩
        cx := 1
        cy := 2
        rx := 0
        ry := 0 }
    SingleLevelStructuralExc 1 3 3 10 q := by
  intro q
  left
  norm_num

example :
    ∃ q : SingleLedger 8,
      singleCreationBoundary 3 q ∧ singleCorrectedBelow 11 q := by
  let q : SingleLedger 8 :=
    { cfg := (⟨⟨3, 2, 3⟩, by norm_num [BiCfg.DoubleInv]⟩ : SingleState 8)
      cx := 2
      cy := 1
      rx := 0
      ry := 0 }
  refine ⟨q, ?_⟩
  norm_num [q, singleCreationBoundary, singleCorrectedBelow, BiCfg.doubleLevel]

end Inhabitation

end Tri

#print axioms Tri.SingleLevelStructuralExc
#print axioms Tri.singleBandStop_correctedY_of_apply_ne_zero
#print axioms Tri.singleBandStop_iter_correctedY
#print axioms Tri.singleBand_boundary_deadline_of_start_co
#print axioms Tri.singleLevelStructural_failure_split
#print axioms Tri.singleBand_split_structural
#print axioms Tri.singleBand_phase_fail_structural
#print axioms Tri.singleLevelPhaseStructuralError
#print axioms Tri.singleBand_reaches_level_structural
