/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Lemma17StageMajority

/-!
# The linear raw clock for one Lemma 17 doubling stage

Unlike the initial Lemma 16 activation phase, each Lemma 17 stage starts with
`a` active molecules and only needs to reach `2a`.  The existing epidemic
doubling estimate therefore gives the paper's linear `128n` horizon.
-/

namespace Tri

open scoped ENNReal

noncomputable section

/-- The counted physical path reaches one doubling checkpoint in `128n`
raw interactions. -/
theorem lemma16CountedPath_doubling_deadline
    (n a A k : ℕ)
    (h3 : 3 ≤ n)
    (ha : 1 ≤ a)
    (hquarter : 4 * a ≤ n)
    (hA : A ≤ 2 * a)
    (s : InfectionRevealPhysicalState n)
    (hstart : a ≤ s.coarse.1.active)
    (hanchorActive : s.coarse.1.active + k = A) :
    terminalFailureMass
      (iter (lemma16CountedPathStep n h3 k)
        (128 * n)
        (lemma16CountedPathInitial s))
      (fun z => A ≤ z.path.current.coarse.1.active) ≤
    ENNReal.ofReal (Real.exp (-(a : ℝ))) := by
  let Target : InfectionState n → Prop :=
    fun u => A ≤ u.1.active
  let K := infectionStateStep n h3
  have hinit :
      Lemma16CountedPathInv s k
        (lemma16CountedPathInitial s) := by
    constructor
    · rfl
    · simp [lemma16CountedPathInitial,
        infectionRevealPhysicalPathInitial]
  have hmap :=
    lemma16CountedPath_iter_map_coarse_on_inv
      n h3 A k (128 * n) s hanchorActive
      (lemma16CountedPathInitial s) hinit
  have horiginal :
      terminalFailureMass
        (iter K (128 * n) s.coarse) Target ≤
      ENNReal.ofReal (Real.exp (-(a : ℝ))) := by
    let DoubleTarget : InfectionState n → Prop :=
      fun u => 2 * a ≤ u.1.active
    have hdouble :
        terminalFailureMass
            (iter K (128 * n) s.coarse)
            DoubleTarget
          ≤ ENNReal.ofReal
              (Real.exp (-(a : ℝ))) := by
      simpa [DoubleTarget] using
        infectionActivation_doubling_reaches
          n a h3 ha hquarter s.coarse hstart
    have hmono :
        terminalFailureMass
            (iter K (128 * n) s.coarse) Target
          ≤ terminalFailureMass
              (iter K (128 * n) s.coarse)
              DoubleTarget := by
      apply terminalFailureMass_mono
      intro u hu
      exact hA.trans hu
    exact hmono.trans hdouble
  have hlazy : IsLazyProjection K K (fun u => u) := by
    intro u
    left
    simpa using PMF.map_id (K u)
  have hfreeze :
      terminalFailureMass
        (iter (freeze Target K) (128 * n) s.coarse) Target ≤
      terminalFailureMass
        (iter K (128 * n) s.coarse) Target := by
    simpa [Target, K] using
      targetFreeze_failure_le_lazy_projection
        Target K K (fun u => u) hlazy
        (128 * n) s.coarse
  calc
    terminalFailureMass
        (iter (lemma16CountedPathStep n h3 k)
          (128 * n)
          (lemma16CountedPathInitial s))
        (fun z => A ≤ z.path.current.coarse.1.active) =
      terminalFailureMass
        ((iter (lemma16CountedPathStep n h3 k)
          (128 * n)
          (lemma16CountedPathInitial s)).map
            lemma16CountedPathToCoarse) Target := by
              symm
              exact terminalFailureMass_map _ _ _
    _ =
      terminalFailureMass
        (iter (freeze Target K)
          (128 * n) s.coarse) Target := by
            rw [hmap]
            rfl
    _ ≤ terminalFailureMass
        (iter K (128 * n) s.coarse) Target :=
          hfreeze
    _ ≤ ENNReal.ofReal (Real.exp (-(a : ℝ))) :=
      horiginal

/-- The doubling deadline transfers to the full Lemma 17 joint carrier. -/
theorem lemma17CountedPath_doubling_deadline
    (n a A k G : ℕ)
    (h3 : 3 ≤ n)
    (ha : 1 ≤ a)
    (hquarter : 4 * a ≤ n)
    (hA : A ≤ 2 * a)
    (s : InfectionRevealPhysicalState n)
    (hstart : a ≤ s.coarse.1.active)
    (hanchorActive : s.coarse.1.active + k = A) :
    terminalFailureMass
      (iter (lemma17CountedPathStep n h3 k A G)
        (128 * n)
        (lemma17CountedPathInitial s))
      (fun z => A ≤
        z.counted.path.current.coarse.1.active)
    ≤ ENNReal.ofReal (Real.exp (-(a : ℝ))) := by
  let μ :=
    iter (lemma17CountedPathStep n h3 k A G)
      (128 * n)
      (lemma17CountedPathInitial s)
  let ν :=
    iter (lemma16CountedPathStep n h3 k)
      (128 * n)
      (lemma16CountedPathInitial s)
  have hmap :
      μ.map lemma17CountedPathToLemma16 = ν := by
    simpa [μ, ν, lemma17CountedPathInitial,
      lemma17CountedPathToLemma16] using
      lemma17CountedPath_iter_map_lemma16
        n h3 k A G (128 * n)
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
    _ ≤ ENNReal.ofReal (Real.exp (-(a : ℝ))) := by
      simpa [ν] using
        lemma16CountedPath_doubling_deadline
          n a A k h3 ha hquarter hA s
          hstart hanchorActive

/-- The same joint doubling deadline padded to the paper's `cStar * n`
horizon. -/
theorem lemma17CountedPath_doubling_deadline_padded
    (n a A k G cStar : ℕ)
    (h3 : 3 ≤ n)
    (ha : 1 ≤ a)
    (hquarter : 4 * a ≤ n)
    (hA : A ≤ 2 * a)
    (hcStar : 128 ≤ cStar)
    (s : InfectionRevealPhysicalState n)
    (hstart : a ≤ s.coarse.1.active)
    (hanchorActive : s.coarse.1.active + k = A) :
    terminalFailureMass
      (iter (lemma17CountedPathStep n h3 k A G)
        (cStar * n)
        (lemma17CountedPathInitial s))
      (fun z => A ≤
        z.counted.path.current.coarse.1.active)
    ≤ ENNReal.ofReal (Real.exp (-(a : ℝ))) := by
  let Target : Lemma17CountedPathState n → Prop :=
    fun z => A ≤ z.counted.path.current.coarse.1.active
  let K := lemma17CountedPathStep n h3 k A G
  have hbase :
      terminalFailureMass
        (iter K (128 * n)
          (lemma17CountedPathInitial s)) Target
      ≤ ENNReal.ofReal (Real.exp (-(a : ℝ))) := by
    simpa [K, Target] using
      lemma17CountedPath_doubling_deadline
        n a A k G h3 ha hquarter hA s
        hstart hanchorActive
  have hreach :
      Reaches K (128 * n)
        (fun z => z = lemma17CountedPathInitial s)
        Target
        (ENNReal.ofReal (Real.exp (-(a : ℝ)))) := by
    intro z hz
    subst z
    exact hbase
  have hclosed :
      ∀ z, Target z → ∀ V y,
        iter K V z y ≠ 0 → Target y := by
    intro z hz V y hy
    apply
      iter_support_closed K Target
        (fun x hx z hxz => ?_)
        V z y hz hy
    by_cases hcheckpoint :
        InfectionRevealPhysicalFirstKReached
          k x.counted.path
    · have hzx : z = x := by
        unfold K lemma17CountedPathStep at hxz
        rw [if_pos hcheckpoint] at hxz
        by_contra hne
        simp [PMF.pure_apply, hne] at hxz
      simpa [hzx] using hx
    · unfold K lemma17CountedPathStep at hxz
      rw [if_neg hcheckpoint] at hxz
      have hzmem :
          z ∈
            ((infectionRevealRecordPMF n h3
              x.counted.path.current).map
                (x.afterRecord A G)).support :=
        hxz
      rw [PMF.support_map] at hzmem
      rcases hzmem with ⟨r, hr, rfl⟩
      unfold Target at hx ⊢
      simp only [Lemma17CountedPathState.afterRecord,
        Lemma16CountedPathState.afterRecord,
        InfectionRevealPhysicalPathState.afterRecord]
      have hmono :=
        InfectionEvent.active_le_nextState_active
          x.counted.path.current.coarse r.event
      rw [← r.after_forget] at hmono
      exact hx.trans hmono
  have hpadded :=
    hreach.mono_horizon_of_closed
      (show 128 * n ≤ cStar * n by
        exact Nat.mul_le_mul_right n hcStar)
      hclosed
  exact
    hpadded (lemma17CountedPathInitial s) rfl

end

end Tri

#print axioms Tri.lemma16CountedPath_doubling_deadline
#print axioms Tri.lemma17CountedPath_doubling_deadline
#print axioms Tri.lemma17CountedPath_doubling_deadline_padded
