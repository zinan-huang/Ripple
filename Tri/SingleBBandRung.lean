/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.SingleBFeller

/-!
# A concrete Single-B band rung

This file instantiates the repaired Single-B staged phase with the productive
clock and conservative return producers.  The creation-boundary budget is fixed
to `H = T + 1`, so the boundary stream is empty on the horizon-`T` support.
-/

namespace Tri

open scoped ENNReal

/-- The explicit conservative error of one concrete Single-B band rung. -/
noncomputable def singleBandRungError
    (n aLoΛ _hiΛ targetΛ D Bw M K _B0 T d c
      returnLo bHiRet kRet : Nat) : ENNReal :=
  let H : Nat := T + 1
  let epsClock : ENNReal :=
    ((1 - singleBandProductivity n d c)
        + singleBandProductivity n d c * ((1 : ENNReal) / 2)) ^ T /
      ((1 : ENNReal) / 2) ^ K
  ((((1 : ENNReal) ^ Bw
      + (1 : ENNReal) ^ (aLoΛ + Bw) /
        ((1 : ENNReal) ^ targetΛ * (1 : ENNReal) ^ M))
      + epsClock)
    + ENNReal.ofReal (Real.exp (-((D : Real) ^ 2 / (2 * (H : Real)))))
    + ((bHiRet : ENNReal) / (returnLo : ENNReal)) ^ kRet)

/-- One fully instantiated Single-B band rung.

The direction parameters are discharged internally with the conservative
choice `p = qRat = w = v = eta = u = 1`; the corrected lower gap plus the
creation-boundary live guard gives the physical majority ratio needed by the
direction supermartingale.

**SUPERSEDED (2026-07-29):** as landed, this rung's direction parameters are
the trivial `w = η = 1` and its return term routes through the trivial ruin
ratio, so the error bound is `≥ 1` — the statement is true but carries no
content.  The live route is the level-form phase engine
(`Tri/SingleBLevelPhase.lean`) and the concrete `singleGapRung`
(`Tri/SingleBGapRung.lean`).  Kept for the record; do not build on it. -/
theorem singleBandRung
    (n : Nat) (hn : 2 <= n)
    (aLoΛ hiΛ targetΛ D Bw M K B0 T d c
      returnLo bHiRet kRet : Nat)
    (htargetHi : targetΛ + 1 <= hiΛ)
    (hDbudget : T + 1 < D)
    (hK : B0 + K = n + 2 * M)
    (hgap : n + D + d = aLoΛ + 1)
    (hwidth : aLoΛ + 1 <= hiΛ)
    (hco : hiΛ + K + 2 * c <= 2 * n)
    (htargetGap : n + D + (returnLo + 1) <= targetΛ)
    (hreturnLo : 0 < returnLo)
    (hleReturn : returnLo <= bHiRet) :
    Reaches (singleStateStep n hn) T
      (fun s => s.1.doubleLevel = aLoΛ + Bw ∧ B0 <= s.1.b)
      (fun s => returnLo + 1 <= s.1.x)
      (singleBandRungError n aLoΛ hiΛ targetΛ D Bw M K B0 T d c
        returnLo bHiRet kRet) := by
  let H : Nat := T + 1
  let epsClock : ENNReal :=
    ((1 - singleBandProductivity n d c)
        + singleBandProductivity n d c * ((1 : ENNReal) / 2)) ^ T /
      ((1 : ENNReal) / 2) ^ K
  let Entry : SingleState n -> Prop :=
    fun s => s.1.doubleLevel = aLoΛ + Bw ∧ B0 <= s.1.b
  let Exit : SingleState n -> Prop :=
    fun s => returnLo + 1 <= s.1.x
  have hHpos : 0 < H := by
    dsimp [H]
    omega
  have hTH : T < H := by
    dsimp [H]
    omega
  have hlive :
      forall q : SingleLedger n,
        ¬ SingleBandFrozen n aLoΛ hiΛ D H q ->
          exists a : Nat,
            q.CorrectedLevel (a + 1) ∧
              1 * q.cfg.1.y <= 1 * q.cfg.1.x := by
    intro q hnotB
    have hnotLow :
        ¬ q.cfg.1.doubleLevel + q.cy <= aLoΛ + q.cx := by
      intro h
      exact hnotB (Or.inl h)
    have hnotBad : ¬ CreationBadY D H q := by
      intro h
      exact hnotB (Or.inr (Or.inr (Or.inl h)))
    have hnotBoundary : ¬ singleCreationBoundary H q := by
      intro h
      exact hnotB (Or.inr (Or.inr (Or.inr h)))
    have hlower : aLoΛ + q.cx + 1 <= q.cfg.1.doubleLevel + q.cy := by
      omega
    obtain ⟨a, ha⟩ :
        exists a : Nat,
          q.cfg.1.doubleLevel + q.cy = (a + 1) + q.cx := by
      refine ⟨q.cfg.1.doubleLevel + q.cy - q.cx - 1, ?_⟩
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
    refine ⟨a, ?_, ?_⟩
    · unfold SingleLedger.CorrectedLevel
      exact ha
    · omega
  have hstart : forall s, Entry s -> s.1.doubleLevel = aLoΛ + Bw := by
    intro s hs
    exact hs.1
  have hexit :
      forall q : SingleLedger n,
        targetΛ + q.cx <= q.cfg.1.doubleLevel + q.cy ->
        ¬ CreationBadY D H q -> ¬ singleCreationBoundary H q -> Exit q.cfg := by
    intro q hsucc hnotBad hnotBoundary
    have hbudget : q.cx + q.cy <= H := by
      unfold singleCreationBoundary at hnotBoundary
      omega
    have hbal : q.cy <= q.cx + D := by
      by_contra hbal
      have hdev : D + q.cx <= q.cy := by omega
      exact hnotBad ⟨hbudget, hdev⟩
    have hsucc' :
        n + D + (returnLo + 1) + q.cx <= q.cfg.1.doubleLevel + q.cy := by
      omega
    have hcorrGap :
        q.cfg.1.y + q.cx + (D + (returnLo + 1)) <= q.cfg.1.x + q.cy := by
      have hinv := q.cfg.2
      simp only [BiCfg.doubleLevel, BiCfg.DoubleInv] at hinv hsucc'
      omega
    have hrec :=
      single_gap_recover (G := D + (returnLo + 1)) (D := D) q hcorrGap hbal
    dsimp [Exit]
    omega
  have hfailure : forall z : SingleState n, ¬ Exit z -> z.1.x <= returnLo := by
    intro z hz
    dsimp [Exit] at hz
    omega
  have hclock : forall s, Entry s ->
      ∑' q, (if singleBandStarvation aLoΛ targetΛ H M q then
          iter (singleBandStop n hn aLoΛ hiΛ D H) T
            (⟨s, 0, 0, 0, 0⟩ : SingleLedger n) q else 0)
        <= epsClock := by
    intro s hs
    exact singleBand_hclock hn aLoΛ hiΛ targetΛ D H M K B0 T d c
      htargetHi (by simpa [H] using hDbudget) hK hgap hwidth hco s hs.2
  have hruin :
      forall q : SingleLedger n,
        SingleBandFrozen n aLoΛ hiΛ D H q ->
          Exit q.cfg ->
            forall U : Nat,
              hitProb (fun z : SingleState n => z.1.x <= returnLo)
                (singleStateStep n hn) U q.cfg
                <= ((bHiRet : ENNReal) / (returnLo : ENNReal)) ^ kRet :=
    singleBand_hruin_trivial hn aLoΛ hiΛ D H returnLo bHiRet kRet
      hreturnLo hleReturn Exit
  have hr := singleBand_phase_reaches hn
    aLoΛ hiΛ targetΛ D H 1 1 Bw M T returnLo bHiRet kRet
    hHpos hTH (by norm_num) 1 1 1 1 epsClock
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
    Entry Exit hlive hstart hexit hfailure hclock hruin
  simpa [singleBandRungError, H, epsClock, Entry, Exit] using hr

section Inhabitation

example :
    Reaches (singleStateStep 20 (by norm_num)) 2
      (fun s : SingleState 20 => s.1.doubleLevel = 23 ∧ 12 <= s.1.b)
      (fun s : SingleState 20 => 2 <= s.1.x)
      (singleBandRungError 20 23 27 26 4 0 1 10 12 2 0 1 1 1 1) := by
  exact singleBandRung 20 (by norm_num)
    23 27 26 4 0 1 10 12 2 0 1 1 1 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end Inhabitation

end Tri

#print axioms Tri.singleBandRung
