/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Lemma19PhysicalStage
import Tri.InfectionActivationConstants

/-!
# Late and full-activation stages for Lemma 19

The late inactive-halving schedule already controls activation on the original
infection chain.  This file transfers any such target deadline to the joint
physical/reaction carrier and instantiates every full-activation estimate
except the maximal immutable-label event.
-/

namespace Tri

open scoped ENNReal

noncomputable section

/-- Any target deadline on the original infection chain transfers to the
joint path stopped at the same activation target. -/
theorem lemma19CountedPath_clock_of_infection
    (n : ℕ) (h3 : 3 ≤ n)
    (k A G T : ℕ)
    (s : InfectionRevealPhysicalState n)
    (hanchorActive : s.coarse.1.active + k = A)
    (ε : ℝ≥0∞)
    (hraw :
      terminalFailureMass
          (iter (infectionStateStep n h3) T s.coarse)
          (fun z => A ≤ z.1.active)
        ≤ ε) :
    terminalFailureMass
        (iter (lemma17CountedPathStep n h3 k A G) T
          (lemma17CountedPathInitial s))
        (fun z =>
          A ≤ z.counted.path.current.coarse.1.active)
      ≤ ε := by
  let Target : InfectionState n → Prop :=
    fun z => A ≤ z.1.active
  let μ :=
    iter (lemma17CountedPathStep n h3 k A G) T
      (lemma17CountedPathInitial s)
  let ν :=
    iter (lemma16CountedPathStep n h3 k) T
      (lemma16CountedPathInitial s)
  have hmap16 :
      μ.map lemma17CountedPathToLemma16 = ν := by
    simpa [μ, ν, lemma17CountedPathInitial,
      lemma17CountedPathToLemma16] using
      lemma17CountedPath_iter_map_lemma16
        n h3 k A G T (lemma17CountedPathInitial s)
  have hinitial :
      Lemma16CountedPathInv s k
        (lemma16CountedPathInitial s) := by
    constructor
    · rfl
    · simp [lemma16CountedPathInitial,
        infectionRevealPhysicalPathInitial]
  have hmapCoarse :
      ν.map lemma16CountedPathToCoarse =
        iter
          (freeze Target (infectionStateStep n h3))
          T s.coarse := by
    simpa [ν, Target] using
      lemma16CountedPath_iter_map_coarse_on_inv
        n h3 A k T s hanchorActive
        (lemma16CountedPathInitial s) hinitial
  have hlazy :
      IsLazyProjection
        (infectionStateStep n h3)
        (infectionStateStep n h3)
        (fun z => z) := by
    intro z
    left
    simpa using PMF.map_id (infectionStateStep n h3 z)
  have hfreeze :
      terminalFailureMass
          (iter
            (freeze Target (infectionStateStep n h3))
            T s.coarse)
          Target
        ≤
      terminalFailureMass
          (iter (infectionStateStep n h3) T s.coarse)
          Target := by
    exact
      targetFreeze_failure_le_lazy_projection
        Target (infectionStateStep n h3)
        (infectionStateStep n h3) (fun z => z)
        hlazy T s.coarse
  calc
    terminalFailureMass μ
          (fun z =>
            A ≤ z.counted.path.current.coarse.1.active)
        =
      terminalFailureMass
          (μ.map lemma17CountedPathToLemma16)
          (fun z => A ≤ z.path.current.coarse.1.active) := by
            symm
            exact terminalFailureMass_map _ _ _
    _ =
      terminalFailureMass ν
          (fun z => A ≤ z.path.current.coarse.1.active) := by
            rw [hmap16]
    _ =
      terminalFailureMass
          (ν.map lemma16CountedPathToCoarse)
          Target := by
            symm
            exact terminalFailureMass_map _ _ _
    _ =
      terminalFailureMass
          (iter
            (freeze Target (infectionStateStep n h3))
            T s.coarse)
          Target := by rw [hmapCoarse]
    _ ≤
      terminalFailureMass
          (iter (infectionStateStep n h3) T s.coarse)
          Target := hfreeze
    _ ≤ ε := by simpa [Target] using hraw

/-- The recursive late inactive-halving schedule reaches full activation on
the joint carrier.  The remaining population is supplied by an additive
witness rather than natural subtraction. -/
theorem lemma19CountedPath_full_activation_clock
    (n r : ℕ) (h3 : 3 ≤ n)
    (s : InfectionRevealPhysicalState n)
    (hanchorActive : s.coarse.1.active + r = n)
    (hactiveTwo : 2 ≤ s.coarse.1.active)
    (hquarter : n ≤ 4 * s.coarse.1.active) :
    terminalFailureMass
        (iter
          (lemma17CountedPathStep n h3 r n 0)
          (infectionLateStages r * (1024 * n))
          (lemma17CountedPathInitial s))
        (fun z =>
          n ≤ z.counted.path.current.coarse.1.active)
      ≤ infectionLateError r := by
  have hrn : r ≤ n := by omega
  have hsub : n - r = s.coarse.1.active := by
    omega
  have hlate :=
    infectionActivation_late_to_all
      n r h3 hrn
      (by simpa [hsub] using hactiveTwo)
      (by simpa [hsub] using hquarter)
  have hraw :
      terminalFailureMass
          (iter (infectionStateStep n h3)
            (infectionLateStages r * (1024 * n))
            s.coarse)
          (fun z => n ≤ z.1.active)
        ≤ infectionLateError r := by
    exact hlate s.coarse (by simpa [hsub])
  exact
    lemma19CountedPath_clock_of_infection
      n h3 r n 0
      (infectionLateStages r * (1024 * n))
      s hanchorActive (infectionLateError r) hraw

/-- Full-activation Lemma 19 assembly with the sole remaining global label
estimate exposed explicitly. -/
theorem lemma19CountedPath_full_activation
    (n r a H Dstart Dlabel M targetGap : ℕ)
    (h3 : 3 ≤ n)
    (ha : 4 ≤ a)
    (hH : 0 < H)
    (s : InfectionRevealPhysicalState n)
    (hstartActive : a ≤ s.coarse.1.active)
    (hanchorActive : s.coarse.1.active + r = n)
    (hquarter : n ≤ 4 * s.coarse.1.active)
    (hstart :
      s.coarse.1.ay + Dstart ≤ s.coarse.1.ax)
    (hbudget :
      targetGap + Dlabel + 2 * M ≤ Dstart)
    (w : ℝ≥0∞) (hw1 : 1 ≤ w) (hwt : w ≠ ⊤)
    (εLabel : ℝ≥0∞)
    (hlabel :
      terminalFailureMass
          (iter
            (lemma17CountedPathStep n h3 r n 0)
            (infectionLateStages r * (1024 * n))
            (lemma17CountedPathInitial s))
          (fun z => ¬ Lemma17LabelBad Dlabel z)
        ≤ εLabel) :
    terminalFailureMass
        (iter
          (lemma17CountedPathStep n h3 r n 0)
          (infectionLateStages r * (1024 * n))
          (lemma17CountedPathInitial s))
        (Lemma19StageGood n targetGap)
      ≤
    ((infectionLateError r + εLabel) +
        (infectionAllActiveCubeCompl n n +
            infectionAllActiveCube n n * w) ^
              (infectionLateStages r * (1024 * n)) /
          w ^ (H + 1)) +
      ENNReal.ofReal
        (Real.exp
          (-((M : ℝ) ^ 2 / (8 * (H : ℝ))))) := by
  have hactiveTwo : 2 ≤ s.coarse.1.active :=
    hstartActive.trans' (by omega)
  have hclock :=
    lemma19CountedPath_full_activation_clock
      n r h3 s hanchorActive hactiveTwo hquarter
  have hactive :=
    lemma17CountedPath_allActive_tail
      n h3 r n 0 le_rfl s hanchorActive
      w hw1 hwt
      (infectionLateStages r * (1024 * n))
      (H + 1)
  have hreaction :=
    lemma17CountedPath_reaction_tail
      n h3 a r n 0 ha (by simp) s
      hstartActive hanchorActive
      (infectionLateStages r * (1024 * n))
      H M hH (by simp)
  exact
    lemma19CountedPath_stage
      n h3 r n
      (infectionLateStages r * (1024 * n))
      H Dstart Dlabel M targetGap s
      hanchorActive hstart hbudget
      (infectionLateError r) εLabel
      ((infectionAllActiveCubeCompl n n +
          infectionAllActiveCube n n * w) ^
            (infectionLateStages r * (1024 * n)) /
        w ^ (H + 1))
      (ENNReal.ofReal
        (Real.exp
          (-((M : ℝ) ^ 2 / (8 * (H : ℝ))))))
      hclock hlabel hactive hreaction

end

end Tri

#print axioms Tri.lemma19CountedPath_clock_of_infection
#print axioms Tri.lemma19CountedPath_full_activation_clock
#print axioms Tri.lemma19CountedPath_full_activation
