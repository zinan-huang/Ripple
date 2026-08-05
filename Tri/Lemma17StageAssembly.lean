/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Lemma17StageDeterministic

/-!
# Probabilistic assembly of one Lemma 17 doubling stage

The joint physical carrier puts the epidemic deadline, immutable-label
window, all-active exposure, and productive-reaction direction estimates on
one deterministic horizon.  Their four exceptional masses are union-bounded;
the deterministic barrier theorem closes every remaining endpoint.
-/

namespace Tri

open scoped ENNReal

noncomputable section

/-- A completed doubling stage has reached its active target without crossing
the prescribed active `Y-X` gap. -/
def Lemma17StageGood
    {n : ℕ} (A G : ℕ)
    (q : Lemma17CountedPathState n) : Prop :=
  A ≤ q.counted.path.current.coarse.1.active ∧
    q.counted.path.current.coarse.1.ay ≤
      q.counted.path.current.coarse.1.ax + G

noncomputable instance lemma17StageGoodDecidable
    {n : ℕ} (A G : ℕ) :
    DecidablePred (@Lemma17StageGood n A G) :=
  Classical.decPred _

/-- The epidemic deadline transfers from the Lemma 16 physical marginal to
the Lemma 17 joint path. -/
theorem lemma17CountedPath_epidemic_deadline
    (n q A k G cStar : ℕ)
    (h3 : 3 ≤ n)
    (hlog : Nat.log 2 n ≤ q)
    (hquarter : 4 * A ≤ n)
    (hcStar : 640 ≤ cStar)
    (s : InfectionRevealPhysicalState n)
    (hstart : 1 ≤ s.coarse.1.active)
    (hanchorActive : s.coarse.1.active + k = A) :
    terminalFailureMass
      (iter (lemma17CountedPathStep n h3 k A G)
        (cStar * q * n)
        (lemma17CountedPathInitial s))
      (fun z => A ≤
        z.counted.path.current.coarse.1.active)
    ≤ lemma16EpidemicError q := by
  let μ :=
    iter (lemma17CountedPathStep n h3 k A G)
      (cStar * q * n)
      (lemma17CountedPathInitial s)
  let ν :=
    iter (lemma16CountedPathStep n h3 k)
      (cStar * q * n)
      (lemma16CountedPathInitial s)
  have hmap :
      μ.map lemma17CountedPathToLemma16 = ν := by
    simpa [μ, ν, lemma17CountedPathInitial,
      lemma17CountedPathToLemma16] using
      lemma17CountedPath_iter_map_lemma16
        n h3 k A G (cStar * q * n)
        (lemma17CountedPathInitial s)
  calc
    terminalFailureMass μ
        (fun z => A ≤
          z.counted.path.current.coarse.1.active) =
      terminalFailureMass
        (μ.map lemma17CountedPathToLemma16)
        (fun z => A ≤
          z.path.current.coarse.1.active) := by
            symm
            simpa using
              terminalFailureMass_map μ
                lemma17CountedPathToLemma16
                (fun z => A ≤
                  z.path.current.coarse.1.active)
    _ =
      terminalFailureMass ν
        (fun z => A ≤
          z.path.current.coarse.1.active) := by
            rw [hmap]
    _ ≤ lemma16EpidemicError q := by
      simpa [ν] using
        lemma16CountedPath_epidemic_deadline
          n q A k cStar h3 hlog hquarter hcStar
          s hstart hanchorActive

/-- Generic one-stage Lemma 17 assembly.  The label-window and epidemic
estimates are explicit inputs; the all-active and directional-reaction tails
are discharged internally on the same physical probability space. -/
theorem lemma17CountedPath_stage
    (n : ℕ) (h3 : 3 ≤ n)
    (a k A G D₀ Dlabel M H T : ℕ)
    (ha : 4 ≤ a)
    (hG : 2 * G ≤ a)
    (hA : A ≤ n)
    (s : InfectionRevealPhysicalState n)
    (hstartActive : a ≤ s.coarse.1.active)
    (hanchorActive : s.coarse.1.active + k = A)
    (hstartGap :
      s.coarse.1.ay ≤ s.coarse.1.ax + D₀)
    (hbudget : D₀ + Dlabel + 2 * M ≤ G)
    (hH : 0 < H)
    (hdrift : 4 * G * H ≤ a * M)
    (w : ℝ≥0∞) (hw1 : 1 ≤ w) (hwt : w ≠ ⊤)
    (εClock εLabel : ℝ≥0∞)
    (hclock :
      terminalFailureMass
          (iter (lemma17CountedPathStep n h3 k A G) T
            (lemma17CountedPathInitial s))
          (fun z => A ≤
            z.counted.path.current.coarse.1.active)
        ≤ εClock)
    (hlabel :
      terminalFailureMass
          (iter (lemma17CountedPathStep n h3 k A G) T
            (lemma17CountedPathInitial s))
          (fun z => ¬ Lemma17LabelBad Dlabel z)
        ≤ εLabel) :
    terminalFailureMass
        (iter (lemma17CountedPathStep n h3 k A G) T
          (lemma17CountedPathInitial s))
        (Lemma17StageGood A G)
      ≤
    εClock + εLabel +
      (infectionAllActiveCubeCompl n A +
          infectionAllActiveCube n A * w) ^ T /
        w ^ (H + 1) +
      ENNReal.ofReal
        (Real.exp
          (-((M : ℝ) ^ 2 / (8 * (H : ℝ))))) := by
  let K := lemma17CountedPathStep n h3 k A G
  let q₀ := lemma17CountedPathInitial s
  let μ := iter K T q₀
  let Reached : Lemma17CountedPathState n → Prop :=
    fun z => A ≤ z.counted.path.current.coarse.1.active
  let LabelBad : Lemma17CountedPathState n → Prop :=
    Lemma17LabelBad Dlabel
  let ActiveBad : Lemma17CountedPathState n → Prop :=
    Lemma17AllActiveBad (H + 1)
  let ReactionBad : Lemma17CountedPathState n → Prop :=
    Lemma17ReactionBad H M
  let εActive :=
    (infectionAllActiveCubeCompl n A +
        infectionAllActiveCube n A * w) ^ T /
      w ^ (H + 1)
  let εReaction :=
    ENNReal.ofReal
      (Real.exp
        (-((M : ℝ) ^ 2 / (8 * (H : ℝ)))))
  have hactive :
      terminalFailureMass μ (fun z => ¬ ActiveBad z) ≤
        εActive := by
    simpa [μ, K, q₀, ActiveBad, εActive] using
      lemma17CountedPath_allActive_tail
        n h3 k A G hA s hanchorActive
        w hw1 hwt T (H + 1)
  have hreaction :
      terminalFailureMass μ (fun z => ¬ ReactionBad z) ≤
        εReaction := by
    simpa [μ, K, q₀, ReactionBad, εReaction] using
      lemma17CountedPath_reaction_tail
        n h3 a k A G ha hG s hstartActive
        hanchorActive T H M hH hdrift
  have hpoint :
      ∀ z,
        (if Lemma17StageGood A G z then
            0
          else μ z) ≤
        (((if Reached z then 0 else μ z) +
          (if LabelBad z then μ z else 0)) +
          (if ActiveBad z then μ z else 0)) +
          (if ReactionBad z then μ z else 0) := by
    intro z
    by_cases hzμ : μ z = 0
    · simp [hzμ]
    have hinv :
        Lemma17CountedPathInv s k A G z := by
      exact
        lemma17CountedPath_iter_inv
          n h3 k A G T s hanchorActive z
          (by simpa [μ, K, q₀] using hzμ)
    have hledger :
        Lemma17ReactionGapLedger z := by
      exact
        lemma17CountedPath_iter_gapLedger
          n h3 k A G T s hanchorActive z
          (by simpa [μ, K, q₀] using hzμ)
    have hleft :
        (if Lemma17StageGood A G z then
            0
          else μ z) ≤ μ z := by
      by_cases hgood :
          Lemma17StageGood A G z <;>
        simp [hgood]
    by_cases hReached : Reached z
    · by_cases hLabel : LabelBad z
      · exact hleft.trans (by
          simp only [hReached, if_pos, hLabel]
          simpa only [zero_add] using
            ((self_le_add_right (μ z)
                (if ActiveBad z then μ z else 0)).trans
              (self_le_add_right
                (μ z +
                  (if ActiveBad z then μ z else 0))
                (if ReactionBad z then μ z else 0))))
      · by_cases hActive : ActiveBad z
        · exact hleft.trans (by
            simp only [hReached, if_pos,
              hLabel, if_false, hActive]
            simpa only [zero_add] using
              (self_le_add_right (μ z)
                (if ReactionBad z then μ z else 0)))
        · by_cases hReaction : ReactionBad z
          · exact hleft.trans (by
              simp [hReached, hLabel,
                hActive, hReaction])
          · have hgap :
                z.counted.path.current.coarse.1.ay ≤
                  z.counted.path.current.coarse.1.ax + G :=
              (lemma17CountedPath_gap_good_of_no_bad
                s k A G D₀ Dlabel M H z
                hinv hledger hstartGap hbudget
                (by simpa [LabelBad] using hLabel)
                (by simpa [ActiveBad] using hActive)
                (by simpa [ReactionBad] using hReaction)).1
            have hgood :
                Lemma17StageGood A G z :=
              ⟨hReached, hgap⟩
            simp [hgood]
    · exact hleft.trans (by
        rw [if_neg hReached]
        exact
          (show μ z ≤
              (((μ z +
                (if LabelBad z then μ z else 0)) +
                (if ActiveBad z then μ z else 0)) +
                (if ReactionBad z then μ z else 0)) by
            calc
              μ z = ((μ z + 0) + 0) + 0 := by simp
              _ ≤
                (((μ z +
                  (if LabelBad z then μ z else 0)) +
                  (if ActiveBad z then μ z else 0)) +
                  (if ReactionBad z then μ z else 0)) :=
                add_le_add
                  (add_le_add
                    (add_le_add le_rfl bot_le)
                    bot_le)
                  bot_le))
  unfold terminalFailureMass
  calc
    (∑' z, if Lemma17StageGood A G z then
        0 else μ z) ≤
      ∑' z,
        ((((if Reached z then 0 else μ z) +
          (if LabelBad z then μ z else 0)) +
          (if ActiveBad z then μ z else 0)) +
          (if ReactionBad z then μ z else 0)) :=
      ENNReal.tsum_le_tsum hpoint
    _ =
      ((∑' z, if Reached z then 0 else μ z) +
        (∑' z, if LabelBad z then μ z else 0)) +
        (∑' z, if ActiveBad z then μ z else 0) +
        (∑' z, if ReactionBad z then μ z else 0) := by
          rw [ENNReal.tsum_add, ENNReal.tsum_add,
            ENNReal.tsum_add]
    _ ≤
      (εClock + εLabel) + εActive + εReaction := by
        exact add_le_add
          (add_le_add
            (add_le_add
              (by simpa [μ, K, q₀, Reached] using hclock)
              (by simpa [μ, K, q₀, LabelBad,
                  terminalFailureMass] using hlabel))
            (by simpa [terminalFailureMass] using hactive))
          (by simpa [terminalFailureMass] using hreaction)
    _ =
      εClock + εLabel +
        (infectionAllActiveCubeCompl n A +
            infectionAllActiveCube n A * w) ^ T /
          w ^ (H + 1) +
        ENNReal.ofReal
          (Real.exp
            (-((M : ℝ) ^ 2 /
              (8 * (H : ℝ))))) := by
        rfl

end

end Tri

#print axioms Tri.lemma17CountedPath_epidemic_deadline
#print axioms Tri.lemma17CountedPath_stage
