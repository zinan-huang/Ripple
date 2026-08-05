/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.SingleBWindowTail

/-!
# Staged Single-B band assembly

This file packages one stopped Single-B band phase.  The productive/clock
starvation stream is carried as an explicit `hclock` hypothesis; the other
three streams are discharged by the stopped-window direction tail, the lower
backslide specialization, and the mirror creation-imbalance tail.
-/

namespace Tri

open scoped ENNReal

/-- Additive corrected-level lower event. -/
def singleCorrectedBelow {n : ℕ} (thr : ℕ) (q : SingleLedger n) : Prop :=
  q.cfg.1.doubleLevel + q.cy ≤ thr + q.cx

instance {n thr : ℕ} : DecidablePred (singleCorrectedBelow (n := n) thr) :=
  fun _ => inferInstanceAs (Decidable (_ ≤ _))

/-- The unresolved live-clock starvation event used by this stage. -/
def singleBandStarvation {n : ℕ} (aLoΛ targetΛ H M : ℕ)
    (q : SingleLedger n) : Prop :=
  aLoΛ + q.cx + 1 ≤ q.cfg.1.doubleLevel + q.cy ∧
    q.cfg.1.doubleLevel + q.cy ≤ targetΛ + q.cx ∧
      q.rx + q.ry < M ∧ q.cx + q.cy < H

instance {n aLoΛ targetΛ H M : ℕ} :
    DecidablePred (singleBandStarvation (n := n) aLoΛ targetΛ H M) :=
  fun _ => inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- Any terminal event mass is at most one. -/
theorem singleBand_event_mass_le_one {n : ℕ} (hn : 2 ≤ n)
    (aLoΛ hiΛ D H T : ℕ) (s₀ : SingleState n)
    (E : SingleLedger n → Prop) [DecidablePred E] :
    ∑' q, (if E q then
        iter (singleBandStop n hn aLoΛ hiΛ D H) T
          (⟨s₀, 0, 0, 0, 0⟩ : SingleLedger n) q else 0)
      ≤ 1 := by
  calc
    (∑' q, (if E q then
        iter (singleBandStop n hn aLoΛ hiΛ D H) T
          (⟨s₀, 0, 0, 0, 0⟩ : SingleLedger n) q else 0))
      ≤ ∑' q, iter (singleBandStop n hn aLoΛ hiΛ D H) T
          (⟨s₀, 0, 0, 0, 0⟩ : SingleLedger n) q :=
        ENNReal.tsum_le_tsum fun q => by by_cases hq : E q <;> simp [hq]
    _ = 1 := PMF.tsum_coe _

/-- The creation-budget boundary has zero mass from a fresh ledger whenever
the horizon is strictly below the budget. -/
theorem singleBand_boundary_mass_zero {n : ℕ} (hn : 2 ≤ n)
    (aLoΛ hiΛ D H T : ℕ) (s₀ : SingleState n) (hTH : T < H) :
    ∑' q, (if singleCreationBoundary H q then
        iter (singleBandStop n hn aLoΛ hiΛ D H) T
          (⟨s₀, 0, 0, 0, 0⟩ : SingleLedger n) q else 0)
      = 0 := by
  rw [ENNReal.tsum_eq_zero]
  intro q
  by_cases hq : singleCreationBoundary H q
  · by_cases hmass :
        iter (singleBandStop n hn aLoΛ hiΛ D H) T
          (⟨s₀, 0, 0, 0, 0⟩ : SingleLedger n) q = 0
    · simp [hq, hmass]
    · have hsupp :=
        singleBandStop_creation_budget_fresh hn aLoΛ hiΛ D H s₀ q hmass
      have hfalse : False := by
        unfold singleCreationBoundary at hq
        omega
      exact False.elim hfalse
  · simp [hq]

/-- Five-stream stopped-band split: corrected failure below `targetΛ`, the
creation-bad event, or the creation-budget boundary is covered by backslide,
direction deadline, live starvation, creation imbalance, and boundary. -/
theorem singleBand_split {n : ℕ} (hn : 2 ≤ n)
    (aLoΛ hiΛ targetΛ D H M T : ℕ) (s₀ : SingleState n) :
    ∑' q, (if singleCorrectedBelow targetΛ q ∨ CreationBadY D H q ∨
          singleCreationBoundary H q then
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
        + (∑' q, (if singleCreationBoundary H q then
            iter (singleBandStop n hn aLoΛ hiΛ D H) T
              (⟨s₀, 0, 0, 0, 0⟩ : SingleLedger n) q else 0)) := by
  rw [← ENNReal.tsum_add, ← ENNReal.tsum_add, ← ENNReal.tsum_add,
    ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun q => ?_
  set μ := iter (singleBandStop n hn aLoΛ hiΛ D H) T
    (⟨s₀, 0, 0, 0, 0⟩ : SingleLedger n) q with hμ
  by_cases hfail : singleCorrectedBelow targetΛ q ∨ CreationBadY D H q ∨
      singleCreationBoundary H q
  · rw [if_pos hfail]
    by_cases hlow : singleCorrectedBelow aLoΛ q
    · rw [if_pos hlow]
      calc
        μ ≤ μ + (if singleCorrectedBelow targetΛ q ∧ M ≤ q.rx + q.ry then μ else 0) :=
          self_le_add_right _ _
        _ ≤ (μ + (if singleCorrectedBelow targetΛ q ∧ M ≤ q.rx + q.ry then μ else 0))
            + (if singleBandStarvation aLoΛ targetΛ H M q then μ else 0) :=
          self_le_add_right _ _
        _ ≤ ((μ + (if singleCorrectedBelow targetΛ q ∧ M ≤ q.rx + q.ry then μ else 0))
            + (if singleBandStarvation aLoΛ targetΛ H M q then μ else 0))
            + (if CreationBadY D H q then μ else 0) :=
          self_le_add_right _ _
        _ ≤ (((μ + (if singleCorrectedBelow targetΛ q ∧ M ≤ q.rx + q.ry then μ else 0))
            + (if singleBandStarvation aLoΛ targetΛ H M q then μ else 0))
            + (if CreationBadY D H q then μ else 0))
            + (if singleCreationBoundary H q then μ else 0) :=
          self_le_add_right _ _
    · rw [if_neg hlow]
      by_cases hbad : CreationBadY D H q
      · rw [if_pos hbad]
        rw [zero_add]
        calc
          μ ≤ ((if singleCorrectedBelow targetΛ q ∧ M ≤ q.rx + q.ry then μ else 0)
                + (if singleBandStarvation aLoΛ targetΛ H M q then μ else 0))
                + μ :=
            self_le_add_left _ _
          _ ≤ (((if singleCorrectedBelow targetΛ q ∧ M ≤ q.rx + q.ry then μ else 0)
                + (if singleBandStarvation aLoΛ targetΛ H M q then μ else 0))
                + μ)
                + (if singleCreationBoundary H q then μ else 0) :=
            self_le_add_right _ _
      · by_cases hboundary : singleCreationBoundary H q
        · rw [if_pos hboundary, if_neg hbad]
          simp
        · have hcorr : singleCorrectedBelow targetΛ q := by
            rcases hfail with hcorr | hrest
            · exact hcorr
            · rcases hrest with hbad' | hboundary'
              · exact absurd hbad' hbad
              · exact absurd hboundary' hboundary
          have hnotBoundary : q.cx + q.cy < H := by
            unfold singleCreationBoundary at hboundary
            exact Nat.lt_of_not_ge hboundary
          by_cases hres : M ≤ q.rx + q.ry
          · rw [if_pos ⟨hcorr, hres⟩]
            simp only [zero_add]
            calc
              μ ≤ μ + (if singleBandStarvation aLoΛ targetΛ H M q then μ else 0) :=
                self_le_add_right _ _
              _ ≤ (μ + (if singleBandStarvation aLoΛ targetΛ H M q then μ else 0))
                  + (if CreationBadY D H q then μ else 0) :=
                self_le_add_right _ _
              _ ≤ ((μ + (if singleBandStarvation aLoΛ targetΛ H M q then μ else 0))
                  + (if CreationBadY D H q then μ else 0))
                  + (if singleCreationBoundary H q then μ else 0) :=
                self_le_add_right _ _
          · have hstarve : singleBandStarvation aLoΛ targetΛ H M q := by
              simp only [singleBandStarvation, singleCorrectedBelow] at hlow hcorr ⊢
              constructor
              · omega
              · exact ⟨hcorr, by omega, hnotBoundary⟩
            rw [if_neg (by intro h; exact hres h.2), if_pos hstarve, if_neg hbad,
              if_neg hboundary]
            simp
  · rw [if_neg hfail]
    positivity

/-- Stopped trace phase-failure bound: backslide, direction deadline, explicit
clock starvation, creation imbalance, and the zero boundary stream. -/
theorem singleBand_phase_fail {n : ℕ} (hn : 2 ≤ n)
    (aLoΛ hiΛ targetΛ D H p qRat Bw M T : ℕ) (hH : 0 < H)
    (hTH : T < H) (hq : qRat ≠ 0) (w v η u ε_clock : ℝ≥0∞)
    (hu : u = (p : ℝ≥0∞) / (qRat : ℝ≥0∞))
    (hrel : η * (u + w ^ 2) = w * (u + 1)) (hwη : w ≤ η)
    (hwv : w * v = 1) (hw1 : w ≤ 1) (hw0 : w ≠ 0)
    (hη1 : 1 ≤ η) (hwt : w ≠ ⊤) (hηt : η ≠ ⊤)
    (hlive : ∀ q, ¬ SingleBandFrozen n aLoΛ hiΛ D H q →
      ∃ a : ℕ, q.CorrectedLevel (a + 1) ∧
        qRat * q.cfg.1.y ≤ p * q.cfg.1.x)
    (s₀ : SingleState n)
    (hstart : s₀.1.doubleLevel = aLoΛ + Bw)
    (hclock :
      ∑' q, (if singleBandStarvation aLoΛ targetΛ H M q then
          iter (singleBandStop n hn aLoΛ hiΛ D H) T
            (⟨s₀, 0, 0, 0, 0⟩ : SingleLedger n) q else 0)
        ≤ ε_clock) :
    ∑' q, (if singleCorrectedBelow targetΛ q ∨ CreationBadY D H q ∨
          singleCreationBoundary H q then
        iter (singleBandStop n hn aLoΛ hiΛ D H) T
          (⟨s₀, 0, 0, 0, 0⟩ : SingleLedger n) q else 0)
      ≤ ((w ^ Bw + w ^ (aLoΛ + Bw) / (w ^ targetΛ * η ^ M))
          + ε_clock)
        + ENNReal.ofReal (Real.exp (-((D : ℝ) ^ 2 / (2 * (H : ℝ))))) := by
  have hsplit := singleBand_split hn aLoΛ hiΛ targetΛ D H M T s₀
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
  have hboundary :
      (∑' q, (if singleCreationBoundary H q then
          iter (singleBandStop n hn aLoΛ hiΛ D H) T
            (⟨s₀, 0, 0, 0, 0⟩ : SingleLedger n) q else 0))
        ≤ 0 := by
    rw [singleBand_boundary_mass_zero hn aLoΛ hiΛ D H T s₀ hTH]
  calc
    ∑' q, (if singleCorrectedBelow targetΛ q ∨ CreationBadY D H q ∨
          singleCreationBoundary H q then
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
          + (∑' q, (if singleCreationBoundary H q then
              iter (singleBandStop n hn aLoΛ hiΛ D H) T
                (⟨s₀, 0, 0, 0, 0⟩ : SingleLedger n) q else 0)) := hsplit
    _ ≤ (((w ^ Bw + w ^ (aLoΛ + Bw) / (w ^ targetΛ * η ^ M))
          + ε_clock)
        + ENNReal.ofReal (Real.exp (-((D : ℝ) ^ 2 / (2 * (H : ℝ)))))
        + 0) :=
        add_le_add (add_le_add (add_le_add (add_le_add hback hdead) hclock) hbad)
          hboundary
    _ = ((w ^ Bw + w ^ (aLoΛ + Bw) / (w ^ targetΛ * η ^ M))
          + ε_clock)
        + ENNReal.ofReal (Real.exp (-((D : ℝ) ^ 2 / (2 * (H : ℝ))))) := by
        rw [add_zero]

/-- Physical Single-B phase reachability.  The exit conversion is supplied in
the corrected form consumed here: corrected target plus non-creation-bad implies
the physical exit predicate. -/
theorem singleBand_phase_reaches {n : ℕ} (hn : 2 ≤ n)
    (aLoΛ hiΛ targetΛ D H p qRat Bw M T returnLo bHiRet kRet : ℕ)
    (hH : 0 < H) (hTH : T < H) (hq : qRat ≠ 0)
    (w v η u ε_clock : ℝ≥0∞)
    (hu : u = (p : ℝ≥0∞) / (qRat : ℝ≥0∞))
    (hrel : η * (u + w ^ 2) = w * (u + 1)) (hwη : w ≤ η)
    (hwv : w * v = 1) (hw1 : w ≤ 1) (hw0 : w ≠ 0)
    (hη1 : 1 ≤ η) (hwt : w ≠ ⊤) (hηt : η ≠ ⊤)
    (Entry Exit : SingleState n → Prop) [DecidablePred Exit]
    (hlive : ∀ q, ¬ SingleBandFrozen n aLoΛ hiΛ D H q →
      ∃ a : ℕ, q.CorrectedLevel (a + 1) ∧
        qRat * q.cfg.1.y ≤ p * q.cfg.1.x)
    (hstart : ∀ s, Entry s → s.1.doubleLevel = aLoΛ + Bw)
    (hexit : ∀ q : SingleLedger n,
      targetΛ + q.cx ≤ q.cfg.1.doubleLevel + q.cy →
      ¬ CreationBadY D H q → ¬ singleCreationBoundary H q → Exit q.cfg)
    (hfailure : ∀ z, ¬ Exit z → z.1.x ≤ returnLo)
    (hclock : ∀ s, Entry s →
      ∑' q, (if singleBandStarvation aLoΛ targetΛ H M q then
          iter (singleBandStop n hn aLoΛ hiΛ D H) T
            (⟨s, 0, 0, 0, 0⟩ : SingleLedger n) q else 0)
        ≤ ε_clock)
    (hruin : ∀ q : SingleLedger n,
      SingleBandFrozen n aLoΛ hiΛ D H q → Exit q.cfg → ∀ U : ℕ,
        hitProb (fun z : SingleState n => z.1.x ≤ returnLo)
          (singleStateStep n hn) U q.cfg
          ≤ ((bHiRet : ℝ≥0∞) / (returnLo : ℝ≥0∞)) ^ kRet) :
    Reaches (singleStateStep n hn) T Entry Exit
      (((w ^ Bw + w ^ (aLoΛ + Bw) / (w ^ targetΛ * η ^ M))
          + ε_clock)
        + ENNReal.ofReal (Real.exp (-((D : ℝ) ^ 2 / (2 * (H : ℝ)))))
        + ((bHiRet : ℝ≥0∞) / (returnLo : ℝ≥0∞)) ^ kRet) := by
  intro s hs
  let q₀ : SingleLedger n := ⟨s, 0, 0, 0, 0⟩
  have htransfer := singleBand_transfer_upper_of_ruin n hn
    aLoΛ hiΛ D H T returnLo bHiRet kRet q₀ Exit hfailure hruin
  have hphase := singleBand_phase_fail hn aLoΛ hiΛ targetΛ D H p qRat Bw M T
    hH hTH hq w v η u ε_clock hu hrel hwη hwv hw1 hw0 hη1 hwt hηt hlive
    s (hstart s hs) (hclock s hs)
  have hstopped :
      (∑' q, if Exit q.cfg then 0 else
          iter (singleBandStop n hn aLoΛ hiΛ D H) T q₀ q)
        ≤ ∑' q, (if singleCorrectedBelow targetΛ q ∨ CreationBadY D H q ∨
              singleCreationBoundary H q then
            iter (singleBandStop n hn aLoΛ hiΛ D H) T q₀ q else 0) := by
    refine ENNReal.tsum_le_tsum fun q => ?_
    by_cases hE : Exit q.cfg
    · simp [hE]
    · have hunion : singleCorrectedBelow targetΛ q ∨ CreationBadY D H q ∨
          singleCreationBoundary H q := by
        by_cases hbad : CreationBadY D H q
        · exact Or.inr (Or.inl hbad)
        · by_cases hboundary : singleCreationBoundary H q
          · exact Or.inr (Or.inr hboundary)
          · have hnot : ¬ targetΛ + q.cx ≤ q.cfg.1.doubleLevel + q.cy :=
              fun hsucc => hE (hexit q hsucc hbad hboundary)
            have hbelow : singleCorrectedBelow targetΛ q := by
              unfold singleCorrectedBelow
              omega
            exact Or.inl hbelow
      simp [hE, hunion]
  calc
    (∑' z, if Exit z then 0 else iter (singleStateStep n hn) T s z)
        ≤ (∑' q, if Exit q.cfg then 0 else
            iter (singleBandStop n hn aLoΛ hiΛ D H) T q₀ q)
          + ((bHiRet : ℝ≥0∞) / (returnLo : ℝ≥0∞)) ^ kRet := by
          simpa [q₀] using htransfer
    _ ≤ (∑' q, (if singleCorrectedBelow targetΛ q ∨ CreationBadY D H q ∨
              singleCreationBoundary H q then
            iter (singleBandStop n hn aLoΛ hiΛ D H) T q₀ q else 0))
          + ((bHiRet : ℝ≥0∞) / (returnLo : ℝ≥0∞)) ^ kRet :=
        add_le_add hstopped le_rfl
    _ ≤ (((w ^ Bw + w ^ (aLoΛ + Bw) / (w ^ targetΛ * η ^ M))
          + ε_clock)
        + ENNReal.ofReal (Real.exp (-((D : ℝ) ^ 2 / (2 * (H : ℝ)))))
        + ((bHiRet : ℝ≥0∞) / (returnLo : ℝ≥0∞)) ^ kRet) :=
        add_le_add hphase le_rfl

section Inhabitation

example :
    let Entry : SingleState 4 → Prop := fun s => s.1.doubleLevel = 5
    let Exit : SingleState 4 → Prop := fun s => 1 ≤ s.1.x
    ∃ ε_clock δ : ℝ≥0∞,
      (∀ s, Entry s →
        ∑' q, (if singleBandStarvation 3 5 4 1 q then
            iter (singleBandStop 4 (by norm_num) 3 7 2 4) 2
              (⟨s, 0, 0, 0, 0⟩ : SingleLedger 4) q else 0)
          ≤ ε_clock)
      ∧
      (∀ q : SingleLedger 4,
        SingleBandFrozen 4 3 7 2 4 q → Exit q.cfg → ∀ U : ℕ,
          hitProb (fun z : SingleState 4 => z.1.x ≤ 0)
            (singleStateStep 4 (by norm_num)) U q.cfg ≤ δ) := by
  intro Entry Exit
  refine ⟨1, 1, ?_, ?_⟩
  · intro s _hs
    exact singleBand_event_mass_le_one (n := 4) (by norm_num) 3 7 2 4 2 s
      (singleBandStarvation 3 5 4 1)
  · intro q _hB _hExit U
    unfold hitProb expect ind
    calc
      (∑' z, iter (freeze (fun z : SingleState 4 => z.1.x ≤ 0)
            (singleStateStep 4 (by norm_num))) U q.cfg z *
          if (fun z : SingleState 4 => z.1.x ≤ 0) z then 1 else 0)
          ≤ ∑' z, iter (freeze (fun z : SingleState 4 => z.1.x ≤ 0)
              (singleStateStep 4 (by norm_num))) U q.cfg z := by
            exact ENNReal.tsum_le_tsum fun z => by
              by_cases hz : z.1.x ≤ 0 <;> simp [hz]
      _ = 1 := PMF.tsum_coe _

end Inhabitation

end Tri

#print axioms Tri.singleCorrectedBelow
#print axioms Tri.singleBandStarvation
#print axioms Tri.singleBand_event_mass_le_one
#print axioms Tri.singleBand_boundary_mass_zero
#print axioms Tri.singleBand_split
#print axioms Tri.singleBand_phase_fail
#print axioms Tri.singleBand_phase_reaches
