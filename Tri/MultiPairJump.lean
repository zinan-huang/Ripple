/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.MultiStrictBias

/-!
# Converse classification of fixed-pair jumps

The existing update lemmas identify the jump caused by each named reaction.
For a five-mass decomposition we also need the converses: a jump of size two
is exactly a direct reaction, and a jump of size one is exactly one of the two
third-party directions.
-/

namespace Tri.Multi

variable {m : ℕ}

theorem speciesDelta_eq_one_iff
    (winner loser i : Species m) :
    speciesDelta winner loser i = 1 ↔ i = winner := by
  unfold speciesDelta
  by_cases hiw : i = winner
  · simp [hiw]
  · by_cases hil : i = loser <;> simp [hiw, hil]

theorem speciesDelta_eq_neg_one_iff
    (winner loser i : Species m) (hne : winner ≠ loser) :
    speciesDelta winner loser i = -1 ↔ i = loser := by
  have hne' : loser ≠ winner := Ne.symm hne
  unfold speciesDelta
  by_cases hiw : i = winner
  · subst i
    simp [hne]
  · by_cases hil : i = loser <;> simp [hiw, hil, hne']

theorem speciesDelta_eq_zero_iff
    (winner loser i : Species m) (hne : winner ≠ loser) :
    speciesDelta winner loser i = 0 ↔
      i ≠ winner ∧ i ≠ loser := by
  have hne' : loser ≠ winner := Ne.symm hne
  unfold speciesDelta
  by_cases hiw : i = winner
  · simp [hiw]
  · by_cases hil : i = loser
    · subst i
      simp [hne']
    · simp [hiw, hil]

theorem directedPairDelta_eq_two_iff
    {winner loser X Y : Species m}
    (hne : winner ≠ loser) (hXY : X ≠ Y) :
    directedPairDelta winner loser X Y = 2 ↔
      winner = X ∧ loser = Y := by
  constructor
  · intro h
    have hXlo := speciesDelta_lower winner loser X
    have hXhi := speciesDelta_upper winner loser X
    have hYlo := speciesDelta_lower winner loser Y
    have hYhi := speciesDelta_upper winner loser Y
    have hdx : speciesDelta winner loser X = 1 := by
      unfold directedPairDelta at h
      omega
    have hdy : speciesDelta winner loser Y = -1 := by
      unfold directedPairDelta at h
      omega
    have hxw : X = winner :=
      (speciesDelta_eq_one_iff winner loser X).mp hdx
    have hyl : Y = loser :=
      (speciesDelta_eq_neg_one_iff winner loser Y hne).mp hdy
    exact ⟨hxw.symm, hyl.symm⟩
  · rintro ⟨rfl, rfl⟩
    exact directedPairDelta_direct_up rfl rfl hXY

theorem directedPairDelta_eq_neg_two_iff
    {winner loser X Y : Species m}
    (hne : winner ≠ loser) (hXY : X ≠ Y) :
    directedPairDelta winner loser X Y = -2 ↔
      winner = Y ∧ loser = X := by
  constructor
  · intro h
    have hXlo := speciesDelta_lower winner loser X
    have hXhi := speciesDelta_upper winner loser X
    have hYlo := speciesDelta_lower winner loser Y
    have hYhi := speciesDelta_upper winner loser Y
    have hdx : speciesDelta winner loser X = -1 := by
      unfold directedPairDelta at h
      omega
    have hdy : speciesDelta winner loser Y = 1 := by
      unfold directedPairDelta at h
      omega
    have hxl : X = loser :=
      (speciesDelta_eq_neg_one_iff winner loser X hne).mp hdx
    have hyw : Y = winner :=
      (speciesDelta_eq_one_iff winner loser Y).mp hdy
    exact ⟨hyw.symm, hxl.symm⟩
  · rintro ⟨rfl, rfl⟩
    exact directedPairDelta_direct_down rfl rfl hXY

theorem directedPairDelta_eq_one_iff
    {winner loser X Y : Species m}
    (hne : winner ≠ loser) (hXY : X ≠ Y) :
    directedPairDelta winner loser X Y = 1 ↔
      (winner = X ∧ loser ≠ Y) ∨
      (loser = Y ∧ winner ≠ X) := by
  constructor
  · intro h
    have hXlo := speciesDelta_lower winner loser X
    have hXhi := speciesDelta_upper winner loser X
    have hYlo := speciesDelta_lower winner loser Y
    have hYhi := speciesDelta_upper winner loser Y
    have hcases :
        (speciesDelta winner loser X = 1 ∧
          speciesDelta winner loser Y = 0) ∨
        (speciesDelta winner loser X = 0 ∧
          speciesDelta winner loser Y = -1) := by
      unfold directedPairDelta at h
      omega
    rcases hcases with hcase | hcase
    · have hxw :=
        (speciesDelta_eq_one_iff winner loser X).mp hcase.1
      have hy0 :=
        (speciesDelta_eq_zero_iff winner loser Y hne).mp hcase.2
      exact Or.inl ⟨hxw.symm, fun h => hy0.2 h.symm⟩
    · have hx0 :=
        (speciesDelta_eq_zero_iff winner loser X hne).mp hcase.1
      have hyl :=
        (speciesDelta_eq_neg_one_iff winner loser Y hne).mp hcase.2
      exact Or.inr ⟨hyl.symm, fun h => hx0.1 h.symm⟩
  · intro h
    rcases h with h | h
    · exact directedPairDelta_X_wins_third
        hne h.1 h.2 hXY
    · exact directedPairDelta_Y_loses_third
        hne h.1 h.2 hXY

theorem directedPairDelta_eq_neg_one_iff
    {winner loser X Y : Species m}
    (hne : winner ≠ loser) (hXY : X ≠ Y) :
    directedPairDelta winner loser X Y = -1 ↔
      (winner = Y ∧ loser ≠ X) ∨
      (loser = X ∧ winner ≠ Y) := by
  constructor
  · intro h
    have hXlo := speciesDelta_lower winner loser X
    have hXhi := speciesDelta_upper winner loser X
    have hYlo := speciesDelta_lower winner loser Y
    have hYhi := speciesDelta_upper winner loser Y
    have hcases :
        (speciesDelta winner loser X = 0 ∧
          speciesDelta winner loser Y = 1) ∨
        (speciesDelta winner loser X = -1 ∧
          speciesDelta winner loser Y = 0) := by
      unfold directedPairDelta at h
      omega
    rcases hcases with hcase | hcase
    · have hx0 :=
        (speciesDelta_eq_zero_iff winner loser X hne).mp hcase.1
      have hyw :=
        (speciesDelta_eq_one_iff winner loser Y).mp hcase.2
      exact Or.inl ⟨hyw.symm, fun h => hx0.2 h.symm⟩
    · have hxl :=
        (speciesDelta_eq_neg_one_iff winner loser X hne).mp hcase.1
      have hy0 :=
        (speciesDelta_eq_zero_iff winner loser Y hne).mp hcase.2
      exact Or.inr ⟨hxl.symm, fun h => hy0.1 h.symm⟩
  · intro h
    rcases h with h | h
    · exact directedPairDelta_Y_wins_third
        hne h.1 h.2 hXY
    · exact directedPairDelta_X_loses_third
        hne h.1 h.2 hXY

end Tri.Multi

#print axioms Tri.Multi.directedPairDelta_eq_two_iff
#print axioms Tri.Multi.directedPairDelta_eq_neg_two_iff
#print axioms Tri.Multi.directedPairDelta_eq_one_iff
#print axioms Tri.Multi.directedPairDelta_eq_neg_one_iff
