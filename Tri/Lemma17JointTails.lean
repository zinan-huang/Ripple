/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Lemma17CountedPath

/-!
# Tail transfers to the Lemma 17 joint path

The exact marginals of `Lemma17CountedPathState` transfer the optimized
directional-reaction tail and the cubic all-active exposure tail to one common
physical probability space.
-/

namespace Tri

open scoped ENNReal

noncomputable section

/-- The stopped productive-reaction trace has used at most `H` productive
steps and accumulated adverse type-(2) excess at least `M`. -/
def Lemma17ReactionBad
    {n : ℕ} (H M : ℕ)
    (q : Lemma17CountedPathState n) : Prop :=
  q.reaction.typeOneCount +
        q.reaction.typeTwoCount ≤ H ∧
    q.reaction.typeOneCount + M ≤
      q.reaction.typeTwoCount

noncomputable instance lemma17ReactionBadDecidable
    {n : ℕ} (H M : ℕ) :
    DecidablePred (@Lemma17ReactionBad n H M) :=
  Classical.decPred _

/-- The genuine physical path has accumulated at least `H` all-active
interactions. -/
def Lemma17AllActiveBad
    {n : ℕ} (H : ℕ)
    (q : Lemma17CountedPathState n) : Prop :=
  H ≤ q.counted.allActiveCount

noncomputable instance lemma17AllActiveBadDecidable
    {n : ℕ} (H : ℕ) :
    DecidablePred (@Lemma17AllActiveBad n H) :=
  Classical.decPred _

/-- The optimized stopped reaction tail transfers exactly to the joint
physical path. -/
theorem lemma17CountedPath_reaction_tail
    (n : ℕ) (h3 : 3 ≤ n)
    (a k A G : ℕ)
    (ha : 4 ≤ a)
    (hG : 2 * G ≤ a)
    (s : InfectionRevealPhysicalState n)
    (hstart : a ≤ s.coarse.1.active)
    (hanchorActive : s.coarse.1.active + k = A)
    (T H M : ℕ)
    (hH : 0 < H)
    (hdrift : 4 * G * H ≤ a * M) :
    terminalFailureMass
        (iter (lemma17CountedPathStep n h3 k A G) T
          (lemma17CountedPathInitial s))
        (fun z => ¬ Lemma17ReactionBad H M z)
      ≤
    ENNReal.ofReal
      (Real.exp
        (-((M : ℝ) ^ 2 / (8 * (H : ℝ))))) := by
  let μ :=
    iter (lemma17CountedPathStep n h3 k A G) T
      (lemma17CountedPathInitial s)
  let ν :=
    iter (infectionReactionTraceStep n h3 A G) T
      (⟨s.coarse, 0, 0⟩ :
        InfectionReactionTraceState n)
  let ReactionBad :
      InfectionReactionTraceState n → Prop :=
    fun z =>
      z.typeOneCount + z.typeTwoCount ≤ H ∧
        z.typeOneCount + M ≤ z.typeTwoCount
  have hmap :
      μ.map lemma17CountedPathToReaction = ν := by
    simpa [μ, ν] using
      lemma17CountedPath_iter_map_reaction
        n h3 k A G T s hanchorActive
  calc
    terminalFailureMass μ
        (fun z => ¬ Lemma17ReactionBad H M z) =
      terminalFailureMass
        (μ.map lemma17CountedPathToReaction)
        (fun z => ¬ ReactionBad z) := by
          symm
          simpa [Lemma17ReactionBad, ReactionBad] using
            terminalFailureMass_map μ
              lemma17CountedPathToReaction
              (fun z => ¬ ReactionBad z)
    _ =
      terminalFailureMass ν
        (fun z => ¬ ReactionBad z) := by
          rw [hmap]
    _ =
      ∑' z,
        if z.typeOneCount + z.typeTwoCount ≤ H ∧
            z.typeOneCount + M ≤ z.typeTwoCount
        then ν z
        else 0 := by
          unfold terminalFailureMass
          apply tsum_congr
          intro z
          by_cases hz : ReactionBad z <;>
            simp [ReactionBad, hz]
    _ ≤
      ENNReal.ofReal
        (Real.exp
          (-((M : ℝ) ^ 2 / (8 * (H : ℝ))))) := by
            simpa [ν] using
              infectionReactionTrace_exp_tail_optimized
                n h3 a A G ha hG s.coarse hstart
                T H M hH hdrift

/-- The cubic all-active exposure tail transfers exactly from the Lemma 16
marginal to the joint path. -/
theorem lemma17CountedPath_allActive_tail
    (n : ℕ) (h3 : 3 ≤ n)
    (k A G : ℕ) (hA : A ≤ n)
    (s : InfectionRevealPhysicalState n)
    (hanchorActive : s.coarse.1.active + k = A)
    (w : ℝ≥0∞) (hw1 : 1 ≤ w) (hwt : w ≠ ⊤)
    (T H : ℕ) :
    terminalFailureMass
        (iter (lemma17CountedPathStep n h3 k A G) T
          (lemma17CountedPathInitial s))
        (fun z => ¬ Lemma17AllActiveBad H z)
      ≤
    (infectionAllActiveCubeCompl n A +
        infectionAllActiveCube n A * w) ^ T /
      w ^ H := by
  let μ :=
    iter (lemma17CountedPathStep n h3 k A G) T
      (lemma17CountedPathInitial s)
  let ν :=
    iter (lemma16CountedPathStep n h3 k) T
      (lemma16CountedPathInitial s)
  have hmap :
      μ.map lemma17CountedPathToLemma16 = ν := by
    simpa [μ, ν, lemma17CountedPathInitial,
      lemma17CountedPathToLemma16] using
      lemma17CountedPath_iter_map_lemma16
        n h3 k A G T
        (lemma17CountedPathInitial s)
  calc
    terminalFailureMass μ
        (fun z => ¬ Lemma17AllActiveBad H z) =
      terminalFailureMass
        (μ.map lemma17CountedPathToLemma16)
        (fun z => ¬ H ≤ z.allActiveCount) := by
          symm
          simpa [Lemma17AllActiveBad] using
            terminalFailureMass_map μ
              lemma17CountedPathToLemma16
              (fun z => ¬ H ≤ z.allActiveCount)
    _ =
      terminalFailureMass ν
        (fun z => ¬ H ≤ z.allActiveCount) := by
          rw [hmap]
    _ =
      ∑' z, if H ≤ z.allActiveCount then
          ν z
        else 0 := by
          unfold terminalFailureMass
          apply tsum_congr
          intro z
          by_cases hz : H ≤ z.allActiveCount <;>
            simp [hz]
    _ ≤
      (infectionAllActiveCubeCompl n A +
          infectionAllActiveCube n A * w) ^ T /
        w ^ H := by
          simpa [ν] using
            lemma16CountedPath_allActive_tail
              n h3 A k hA s hanchorActive
              w hw1 hwt T H

end

end Tri

#print axioms Tri.lemma17CountedPath_reaction_tail
#print axioms Tri.lemma17CountedPath_allActive_tail
