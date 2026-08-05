/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Lemma17StageRange
import Tri.InfectionRevealPhysicalUrnPotential

/-!
# Urn potentials through Lemma 17 stage kernels

The local counters and stopping rules used by a Lemma 17 stage only insert
holds into the genuine physical reveal process.  Consequently every stopped
urn hitting potential remains superharmonic through a complete stage.
-/

namespace Tri

open scoped ENNReal

noncomputable section

/-- A reachable counted-path state in a stage whose target leaves four
molecules of room still has at least three inactive identities. -/
theorem lemma17CountedPathInv_inactive_three
    (n k A G : ℕ)
    (s : InfectionRevealPhysicalState n)
    (hroom : A + 4 ≤ n)
    (hanchorActive : s.coarse.1.active + k = A)
    (q : Lemma17CountedPathState n)
    (hq : Lemma17CountedPathInv s k A G q) :
    ∃ m, m + 3 =
      q.counted.path.current.inactive.ids.card := by
  have hanchor :
      q.counted.path.anchor = s := hq.1.1
  have hlen :
      q.counted.path.revealed.length ≤ k + 1 :=
    hq.1.2
  have hledger := q.counted.path.hactiveLedger
  rw [hanchor] at hledger
  have hactive :
      q.counted.path.current.coarse.1.active ≤ A + 1 := by
    omega
  have htotal :=
    infectionReveal_active_add_inactive
      q.counted.path.current
  have hthree :
      3 ≤ q.counted.path.current.inactive.ids.card := by
    omega
  obtain ⟨m, hm⟩ :=
    Nat.exists_eq_add_of_le hthree
  exact ⟨m, by omega⟩

/-- The stopped counted-path step preserves every stopped-urn hitting
potential of the current inactive counts. -/
theorem expect_lemma17CountedPathStep_urnEverHit_le
    (n : ℕ) (h3 : 3 ≤ n)
    (k A G : ℕ)
    (s : InfectionRevealPhysicalState n)
    (hroom : A + 4 ≤ n)
    (hanchorActive : s.coarse.1.active + k = A)
    (Bad : ℕ × ℕ → Prop) [DecidablePred Bad]
    (q : Lemma17CountedPathState n)
    (hq : Lemma17CountedPathInv s k A G q) :
    expect
        (lemma17CountedPathStep n h3 k A G q)
        (fun z =>
          everHit Bad urnStopped
            (infectionInactiveCounts
              z.counted.path.current.inactive))
      ≤
        everHit Bad urnStopped
          (infectionInactiveCounts
            q.counted.path.current.inactive) := by
  by_cases hreach :
      InfectionRevealPhysicalFirstKReached
        k q.counted.path
  · unfold lemma17CountedPathStep
    rw [if_pos hreach, expect_pure]
  · obtain ⟨m, hm⟩ :=
      lemma17CountedPathInv_inactive_three
        n k A G s hroom hanchorActive q hq
    let W : InfectionRevealPhysicalState n → ℝ≥0∞ :=
      fun z =>
        everHit Bad urnStopped
          (infectionInactiveCounts z.inactive)
    calc
      expect
          (lemma17CountedPathStep n h3 k A G q)
          (fun z => W z.counted.path.current) =
        expect
          ((lemma17CountedPathStep n h3 k A G q).map
            (fun z => z.counted.path.current))
          W := by
            exact
              (expect_map
                (lemma17CountedPathStep n h3 k A G q)
                (fun z => z.counted.path.current)
                W).symm
      _ =
        expect
          (infectionRevealPhysicalStep n h3
            q.counted.path.current)
          W := by
            congr 1
            unfold lemma17CountedPathStep
              infectionRevealPhysicalStep
            rw [if_neg hreach, PMF.map_comp]
            rfl
      _ ≤
        W q.counted.path.current :=
          expect_infectionRevealPhysicalStep_urnEverHit_le
            n h3 q.counted.path.current hm Bad

/-- A complete Lemma 17 physical stage preserves every stopped-urn hitting
potential, independently of its local counter horizon. -/
theorem expect_lemma17PhysicalStageKernel_urnEverHit_le
    (n : ℕ) (h3 : 3 ≤ n)
    (k A G T : ℕ)
    (s : InfectionRevealPhysicalState n)
    (hroom : A + 4 ≤ n)
    (hanchorActive : s.coarse.1.active + k = A)
    (Bad : ℕ × ℕ → Prop) [DecidablePred Bad] :
    expect
        (lemma17PhysicalStageKernel n h3 k A G T s)
        (fun z =>
          everHit Bad urnStopped
            (infectionInactiveCounts z.inactive))
      ≤
        everHit Bad urnStopped
          (infectionInactiveCounts s.inactive) := by
  let K := lemma17CountedPathStep n h3 k A G
  let P := Lemma17CountedPathInv s k A G
  let V : Lemma17CountedPathState n → ℝ≥0∞ :=
    fun z =>
      everHit Bad urnStopped
        (infectionInactiveCounts
          z.counted.path.current.inactive)
  have hclosed :
      ∀ q, P q → ∀ z, K q z ≠ 0 → P z := by
    intro q hq z hz
    exact
      lemma17CountedPathStep_inv_closed
        n h3 k A G s hanchorActive q z hq hz
  have hstep :
      ∀ q, P q → expect (K q) V ≤ V q := by
    intro q hq
    exact
      expect_lemma17CountedPathStep_urnEverHit_le
        n h3 k A G s hroom hanchorActive Bad q hq
  have hinitial :
      P (lemma17CountedPathInitial s) :=
    lemma17CountedPathInitial_inv s k A G
  have hiter :=
    expect_iter_le_of_support_invariant
      K P V 1 hclosed
      (fun q hq => by simpa using hstep q hq)
      T (lemma17CountedPathInitial s) hinitial
  unfold lemma17PhysicalStageKernel
  rw [expect_map]
  simpa [K, P, V, lemma17CountedPathInitial,
    lemma16CountedPathInitial,
    infectionRevealPhysicalPathInitial] using hiter

/-- A stage requesting no new revealed identities is the identity kernel. -/
theorem lemma17PhysicalStageKernel_zero
    (n : ℕ) (h3 : 3 ≤ n)
    (A G T : ℕ)
    (s : InfectionRevealPhysicalState n) :
    lemma17PhysicalStageKernel n h3 0 A G T s =
      PMF.pure s := by
  have hstep :
      lemma17CountedPathStep n h3 0 A G =
        fun q => PMF.pure q := by
    funext q
    unfold lemma17CountedPathStep
    rw [if_pos]
    simp [InfectionRevealPhysicalFirstKReached]
  have hiter :
      iter (lemma17CountedPathStep n h3 0 A G) T
          (lemma17CountedPathInitial s) =
        PMF.pure (lemma17CountedPathInitial s) := by
    rw [hstep]
    induction T with
    | zero => rfl
    | succ T ih =>
        rw [iter_succ, PMF.pure_bind]
        exact ih
  unfold lemma17PhysicalStageKernel
  rw [hiter, PMF.pure_map]
  rfl

end

end Tri

#print axioms Tri.lemma17CountedPathInv_inactive_three
#print axioms Tri.expect_lemma17CountedPathStep_urnEverHit_le
#print axioms Tri.expect_lemma17PhysicalStageKernel_urnEverHit_le
#print axioms Tri.lemma17PhysicalStageKernel_zero
