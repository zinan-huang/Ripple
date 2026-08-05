/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.MultiFiber

/-!
# Pairwise gap updates in multi-species Tri

For two tracked species `X` and `Y`, a directed firing changes the integer gap
`count X - count Y` by the winner/loser incidence difference. This single
formula covers both direct `X/Y` reactions, whose increment has magnitude two,
and third-party reactions, whose increment has magnitude at most one.
-/

namespace Tri.Multi

variable {m n : ℕ}

/-- Signed count change of one coordinate under a directed transfer. -/
def speciesDelta
    (winner loser i : Species m) : ℤ :=
  if i = winner then 1 else if i = loser then -1 else 0

/-- Integer gap between two selected species. -/
def pairGap
    (c : Config m n) (X Y : Species m) : ℤ :=
  (count c X : ℤ) - (count c Y : ℤ)

/-- Signed change of the `X-Y` gap under one directed transfer. -/
def directedPairDelta
    (winner loser X Y : Species m) : ℤ :=
  speciesDelta winner loser X - speciesDelta winner loser Y

theorem int_count_transfer
    (c : Config m n) (winner loser i : Species m)
    (hne : winner ≠ loser) (hloser : 0 < count c loser) :
    (count (transfer c winner loser hne hloser) i : ℤ) =
      (count c i : ℤ) + speciesDelta winner loser i := by
  by_cases hiw : i = winner
  · subst i
    simp [speciesDelta]
  · by_cases hil : i = loser
    · subst i
      rw [count_transfer_loser]
      simp only [speciesDelta, if_neg (Ne.symm hne), if_pos]
      omega
    · rw [count_transfer_of_ne c winner loser i hne hloser hiw hil]
      simp [speciesDelta, hiw, hil]

theorem pairGap_transfer
    (c : Config m n) (winner loser X Y : Species m)
    (hne : winner ≠ loser) (hloser : 0 < count c loser) :
    pairGap (transfer c winner loser hne hloser) X Y =
      pairGap c X Y + directedPairDelta winner loser X Y := by
  unfold pairGap
  rw [int_count_transfer c winner loser X hne hloser,
    int_count_transfer c winner loser Y hne hloser]
  unfold directedPairDelta
  ring

/-- Signed pair-gap change determined by one physical sample. -/
noncomputable def samplePairDelta
    {c : Config m n} (t : TripleSample c)
    (X Y : Species m) : ℤ :=
  match classify t with
  | none => 0
  | some p => directedPairDelta p.1.1 p.1.2 X Y

theorem pairGap_sampleNext
    (c : Config m n) (t : TripleSample c)
    (X Y : Species m) :
    pairGap (sampleNext c t) X Y =
      pairGap c X Y + samplePairDelta t X Y := by
  classical
  cases hclass : classify t with
  | none =>
      have hsnext : sampleNext c t = c := by
        unfold sampleNext
        rw [hclass]
      rw [hsnext]
      simp [samplePairDelta, hclass]
  | some p =>
      let hloserPos : 0 < count c p.1.2 :=
        count_pos_of_multiplicity_pos t p.1.2 (by
          rw [p.2.2.2]
          omega)
      have hsnext :
          sampleNext c t =
            transfer c p.1.1 p.1.2 p.2.1 hloserPos := by
        unfold sampleNext
        rw [hclass]
      have htransfer :=
        pairGap_transfer c p.1.1 p.1.2 X Y p.2.1
          hloserPos
      rw [hsnext, htransfer]
      simp only [samplePairDelta, hclass]

theorem speciesDelta_lower
    (winner loser i : Species m) :
    (-1 : ℤ) ≤ speciesDelta winner loser i := by
  unfold speciesDelta
  split_ifs <;> omega

theorem speciesDelta_upper
    (winner loser i : Species m) :
    speciesDelta winner loser i ≤ (1 : ℤ) := by
  unfold speciesDelta
  split_ifs <;> omega

theorem directedPairDelta_direct_up
    {winner loser X Y : Species m}
    (hwinner : winner = X) (hloser : loser = Y)
    (hXY : X ≠ Y) :
    directedPairDelta winner loser X Y = 2 := by
  subst winner
  subst loser
  simp [directedPairDelta, speciesDelta, Ne.symm hXY]

theorem directedPairDelta_direct_down
    {winner loser X Y : Species m}
    (hwinner : winner = Y) (hloser : loser = X)
    (hXY : X ≠ Y) :
    directedPairDelta winner loser X Y = -2 := by
  subst winner
  subst loser
  simp [directedPairDelta, speciesDelta, hXY]

theorem directedPairDelta_X_wins_third
    {winner loser X Y : Species m}
    (hne : winner ≠ loser)
    (hwinner : winner = X) (hloserY : loser ≠ Y)
    (hXY : X ≠ Y) :
    directedPairDelta winner loser X Y = 1 := by
  subst winner
  simp [directedPairDelta, speciesDelta, Ne.symm hXY,
    Ne.symm hloserY]

theorem directedPairDelta_Y_loses_third
    {winner loser X Y : Species m}
    (hne : winner ≠ loser)
    (hloser : loser = Y) (hwinnerX : winner ≠ X)
    (hXY : X ≠ Y) :
    directedPairDelta winner loser X Y = 1 := by
  subst loser
  simp [directedPairDelta, speciesDelta, Ne.symm hwinnerX,
    hXY, Ne.symm hne]

theorem directedPairDelta_Y_wins_third
    {winner loser X Y : Species m}
    (hne : winner ≠ loser)
    (hwinner : winner = Y) (hloserX : loser ≠ X)
    (hXY : X ≠ Y) :
    directedPairDelta winner loser X Y = -1 := by
  subst winner
  simp [directedPairDelta, speciesDelta, hXY,
    Ne.symm hloserX]

theorem directedPairDelta_X_loses_third
    {winner loser X Y : Species m}
    (hne : winner ≠ loser)
    (hloser : loser = X) (hwinnerY : winner ≠ Y)
    (hXY : X ≠ Y) :
    directedPairDelta winner loser X Y = -1 := by
  subst loser
  simp [directedPairDelta, speciesDelta, Ne.symm hne,
    Ne.symm hwinnerY, Ne.symm hXY]

theorem directedPairDelta_away
    {winner loser X Y : Species m}
    (hwinnerX : winner ≠ X) (hloserX : loser ≠ X)
    (hwinnerY : winner ≠ Y) (hloserY : loser ≠ Y) :
    directedPairDelta winner loser X Y = 0 := by
  simp [directedPairDelta, speciesDelta, Ne.symm hwinnerX,
    Ne.symm hloserX, Ne.symm hwinnerY, Ne.symm hloserY]

theorem samplePairDelta_lower
    {c : Config m n} (t : TripleSample c)
    (X Y : Species m) :
    (-2 : ℤ) ≤ samplePairDelta t X Y := by
  classical
  cases hclass : classify t with
  | none =>
      simp [samplePairDelta, hclass]
  | some p =>
      have hX := speciesDelta_lower p.1.1 p.1.2 X
      have hY := speciesDelta_upper p.1.1 p.1.2 Y
      simp only [samplePairDelta, hclass]
      unfold directedPairDelta
      omega

theorem samplePairDelta_upper
    {c : Config m n} (t : TripleSample c)
    (X Y : Species m) :
    samplePairDelta t X Y ≤ (2 : ℤ) := by
  classical
  cases hclass : classify t with
  | none =>
      simp [samplePairDelta, hclass]
  | some p =>
      have hX := speciesDelta_upper p.1.1 p.1.2 X
      have hY := speciesDelta_lower p.1.1 p.1.2 Y
      simp only [samplePairDelta, hclass]
      unfold directedPairDelta
      omega

end Tri.Multi

#print axioms Tri.Multi.int_count_transfer
#print axioms Tri.Multi.pairGap_transfer
#print axioms Tri.Multi.pairGap_sampleNext
#print axioms Tri.Multi.directedPairDelta_direct_up
#print axioms Tri.Multi.directedPairDelta_away
#print axioms Tri.Multi.samplePairDelta_lower
#print axioms Tri.Multi.samplePairDelta_upper
