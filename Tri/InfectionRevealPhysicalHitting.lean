/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.InfectionRevealPhysicalFirstKTimeChange
import Tri.TimeChangeHitting

/-!
# Hitting domination for the physical reveal clock

A physical activation round reveals zero, one, or two inactive identities.
Consequently, after forgetting the coarse physical coordinate, one physical
round cannot increase the eventual hitting probability of the stopped
one-identity reveal chain.
-/

namespace Tri

open scoped ENNReal

noncomputable section

/-- The explicit zero/one/two reveal time change preserves every eventual
hitting upper bound of the stopped one-at-a-time chain. -/
theorem expect_infectionRevealPrefixTimeChangeLiveStep_everHit_le
    (n : ℕ) (h3 : 3 ≤ n) (k : ℕ)
    (s : InfectionRevealPhysicalState n)
    (word : List (Fin n))
    (B : InfectionRevealPrefixCheckpoint n → Prop)
    [DecidablePred B] :
    expect
        (infectionRevealPrefixTimeChangeLiveStep
          n h3 k s word)
        (everHit B
          (InfectionRevealPrefixCheckpoint.oneStep n k))
      ≤
        everHit B
          (InfectionRevealPrefixCheckpoint.oneStep n k)
          (.live s.inactive word) := by
  let K := InfectionRevealPrefixCheckpoint.oneStep n k
  let q : InfectionRevealPrefixCheckpoint n :=
    .live s.inactive word
  let V := everHit B K
  unfold infectionRevealPrefixTimeChangeLiveStep
  rw [expect_bind']
  calc
    (∑' d,
        infectionRevealBatchSizePMF n
            s.coarse.1.active s.inactive.ids.card h3
            (infectionReveal_active_add_inactive s) d *
          expect
            (match d with
              | .zero => PMF.pure q
              | .one => K q
              | .two => iter K 2 q)
            V)
        ≤
      ∑' d,
        infectionRevealBatchSizePMF n
            s.coarse.1.active s.inactive.ids.card h3
            (infectionReveal_active_add_inactive s) d *
          V q := by
            refine ENNReal.tsum_le_tsum fun d => ?_
            apply mul_le_mul_right
            cases d with
            | zero => simp [V]
            | one =>
                exact expect_everHit_le B K q
            | two =>
                exact expect_iter_everHit_le B K 2 q
    _ = V q := by
      rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- With two inactive identities available, the genuine physical batch step
is dominated by the eventual hitting potential of ordinary stopped reveals. -/
theorem expect_infectionRevealPhysicalCheckpointLiveStep_everHit_le
    (n : ℕ) (h3 : 3 ≤ n) (k : ℕ)
    (s : InfectionRevealPhysicalState n)
    (word : List (Fin n))
    (hword : ¬ k ≤ word.length)
    {m : ℕ} (hcard : m + 2 = s.inactive.ids.card)
    (B : InfectionRevealPrefixCheckpoint n → Prop)
    [DecidablePred B] :
    expect
        (infectionRevealPhysicalCheckpointLiveStep
          n h3 k s word)
        (everHit B
          (InfectionRevealPrefixCheckpoint.oneStep n k))
      ≤
        everHit B
          (InfectionRevealPrefixCheckpoint.oneStep n k)
          (.live s.inactive word) := by
  rw [infectionRevealPhysicalCheckpointLiveStep_eq_timeChange
    n h3 k s word hword hcard]
  exact
    expect_infectionRevealPrefixTimeChangeLiveStep_everHit_le
      n h3 k s word B

/-- The lifted eventual hitting potential is superharmonic for a live physical
quotient state while the prefix and two-reveal room conditions hold. -/
theorem expect_infectionRevealFirstKQuotient_step_everHit_le_live
    (n : ℕ) (h3 : 3 ≤ n) (k : ℕ)
    (s : InfectionRevealPhysicalState n)
    (word : List (Fin n))
    (hword : ¬ k ≤ word.length)
    {m : ℕ} (hcard : m + 2 = s.inactive.ids.card)
    (B : InfectionRevealPrefixCheckpoint n → Prop)
    [DecidablePred B] :
    expect
        (InfectionRevealFirstKQuotient.step n h3 k
          (.live s word))
        (fun q =>
          everHit B
            (InfectionRevealPrefixCheckpoint.oneStep n k)
            (InfectionRevealPrefixCheckpoint.ofPhysical q))
      ≤
        everHit B
          (InfectionRevealPrefixCheckpoint.oneStep n k)
          (.live s.inactive word) := by
  rw [← expect_map]
  rw [infectionRevealFirstKQuotient_step_map_checkpoint_live
    n h3 k s word hword]
  exact
    expect_infectionRevealPhysicalCheckpointLiveStep_everHit_le
      n h3 k s word hword hcard B

/-- Done quotient states preserve every lifted logical potential exactly. -/
theorem expect_infectionRevealFirstKQuotient_step_done
    (n : ℕ) (h3 : 3 ≤ n) (k : ℕ)
    (word : List (Fin n))
    (V : InfectionRevealPrefixCheckpoint n → ℝ≥0∞) :
    expect
        (InfectionRevealFirstKQuotient.step n h3 k
          (.done word))
        (fun q => V
          (InfectionRevealPrefixCheckpoint.ofPhysical q))
      =
        V (.done word) := by
  simp [InfectionRevealFirstKQuotient.step,
    InfectionRevealPrefixCheckpoint.ofPhysical]

/-- The stopped physical path kernel never changes its anchor. -/
theorem infectionRevealPhysicalFirstKStep_anchor_eq_of_ne_zero
    (n : ℕ) (h3 : 3 ≤ n) (k : ℕ)
    (q z : InfectionRevealPhysicalPathState n)
    (hz :
      infectionRevealPhysicalFirstKStep n h3 k q z ≠ 0) :
    z.anchor = q.anchor := by
  by_cases hk : InfectionRevealPhysicalFirstKReached k q
  · have hqz : z = q := by
      unfold infectionRevealPhysicalFirstKStep at hz
      rw [freeze_of_mem q hk] at hz
      by_contra hne
      simp [PMF.pure_apply, hne] at hz
    rw [hqz]
  · unfold infectionRevealPhysicalFirstKStep at hz
    rw [freeze_of_not_mem q hk] at hz
    have hzmem :
        z ∈ (infectionRevealPhysicalPathStep n h3 q).support :=
      hz
    unfold infectionRevealPhysicalPathStep at hzmem
    rw [PMF.support_map] at hzmem
    rcases hzmem with ⟨r, hr, rfl⟩
    rfl

/-- From a path whose anchor leaves two identities beyond the requested
prefix, every live stopped physical step is dominated by the ordinary stopped
reveal eventual-hitting potential. -/
theorem expect_infectionRevealPhysicalFirstKStep_everHit_le
    (n : ℕ) (h3 : 3 ≤ n) (k : ℕ)
    (q : InfectionRevealPhysicalPathState n)
    (hroom : k + 2 ≤ q.anchor.inactive.ids.card)
    (B : InfectionRevealPrefixCheckpoint n → Prop)
    [DecidablePred B] :
    expect
        (infectionRevealPhysicalFirstKStep n h3 k q)
        (fun z =>
          everHit B
            (InfectionRevealPrefixCheckpoint.oneStep n k)
            (InfectionRevealPrefixCheckpoint.ofPhysical
              (InfectionRevealFirstKQuotient.ofPath k z)))
      ≤
        everHit B
          (InfectionRevealPrefixCheckpoint.oneStep n k)
          (InfectionRevealPrefixCheckpoint.ofPhysical
            (InfectionRevealFirstKQuotient.ofPath k q)) := by
  by_cases hk : k ≤ q.revealed.length
  · have hmem : InfectionRevealPhysicalFirstKReached k q := hk
    unfold infectionRevealPhysicalFirstKStep
    rw [freeze_of_mem q hmem, expect_pure]
  · have hcardLedger :=
      q.revealed_length_add_current
    have htwo : 2 ≤ q.current.inactive.ids.card := by
      omega
    obtain ⟨m, hcard⟩ :
        ∃ m, m + 2 = q.current.inactive.ids.card := by
      obtain ⟨m, hm⟩ :=
        Nat.exists_eq_add_of_le htwo
      exact ⟨m, by omega⟩
    have hq :
        InfectionRevealFirstKQuotient.ofPath k q =
          .live q.current q.revealed := by
      simp [InfectionRevealFirstKQuotient.ofPath, hk]
    calc
      expect
          (infectionRevealPhysicalFirstKStep n h3 k q)
          (fun z =>
            everHit B
              (InfectionRevealPrefixCheckpoint.oneStep n k)
              (InfectionRevealPrefixCheckpoint.ofPhysical
                (InfectionRevealFirstKQuotient.ofPath k z))) =
        expect
          ((infectionRevealPhysicalFirstKStep n h3 k q).map
            (InfectionRevealFirstKQuotient.ofPath k))
          (fun z =>
            everHit B
              (InfectionRevealPrefixCheckpoint.oneStep n k)
              (InfectionRevealPrefixCheckpoint.ofPhysical z)) := by
                rw [expect_map]
      _ =
        expect
          (InfectionRevealFirstKQuotient.step n h3 k
            (InfectionRevealFirstKQuotient.ofPath k q))
          (fun z =>
            everHit B
              (InfectionRevealPrefixCheckpoint.oneStep n k)
              (InfectionRevealPrefixCheckpoint.ofPhysical z)) := by
                rw [
                  infectionRevealPhysicalFirstKStep_map_quotient
                    n h3 k q]
      _ ≤
        everHit B
          (InfectionRevealPrefixCheckpoint.oneStep n k)
          (InfectionRevealPrefixCheckpoint.ofPhysical
            (InfectionRevealFirstKQuotient.ofPath k q)) := by
              rw [hq]
              exact
                expect_infectionRevealFirstKQuotient_step_everHit_le_live
                  n h3 k q.current q.revealed hk hcard B

/-- The genuine stopped physical reveal path has no larger eventual
projected hitting probability than the stopped one-at-a-time reveal chain. -/
theorem infectionRevealPhysicalFirstK_everHit_le_logical
    (n : ℕ) (h3 : 3 ≤ n) (k : ℕ)
    (q : InfectionRevealPhysicalPathState n)
    (hroom : k + 2 ≤ q.anchor.inactive.ids.card)
    (B : InfectionRevealPrefixCheckpoint n → Prop)
    [DecidablePred B] :
    everHit
        (fun z =>
          B (InfectionRevealPrefixCheckpoint.ofPhysical
            (InfectionRevealFirstKQuotient.ofPath k z)))
        (infectionRevealPhysicalFirstKStep n h3 k) q
      ≤
        everHit B
          (InfectionRevealPrefixCheckpoint.oneStep n k)
          (InfectionRevealPrefixCheckpoint.ofPhysical
            (InfectionRevealFirstKQuotient.ofPath k q)) := by
  let π :
      InfectionRevealPhysicalPathState n →
        InfectionRevealPrefixCheckpoint n :=
    fun z =>
      InfectionRevealPrefixCheckpoint.ofPhysical
        (InfectionRevealFirstKQuotient.ofPath k z)
  let L :=
    infectionRevealPhysicalFirstKStep n h3 k
  let K :=
    InfectionRevealPrefixCheckpoint.oneStep n k
  let P : InfectionRevealPhysicalPathState n → Prop :=
    fun z => k + 2 ≤ z.anchor.inactive.ids.card
  let V : InfectionRevealPhysicalPathState n → ℝ≥0∞ :=
    fun z => everHit B K (π z)
  have hclosed :
      ∀ s, P s → ∀ z, L s z ≠ 0 → P z := by
    intro s hs z hz
    dsimp only [P] at hs ⊢
    have ha :=
      infectionRevealPhysicalFirstKStep_anchor_eq_of_ne_zero
        n h3 k s z hz
    rw [ha]
    exact hs
  have hsuper :
      ∀ s, P s → expect (L s) V ≤ V s := by
    intro s hs
    exact
      expect_infectionRevealPhysicalFirstKStep_everHit_le
        n h3 k s hs B
  have h :=
    ville_frozen_of_support_invariant
      L (fun z => B (π z)) P V 1
      (by simp) (by simp)
      (fun z hzP hz => by
        rw [show V z = 1 by
          exact everHit_eq_one_of_mem B K (π z) hz])
      hclosed hsuper q hroom
  simpa [everHit, L, K, P, V, π] using h

/-- Initial-state form of physical-to-logical eventual hitting domination. -/
theorem infectionRevealPhysicalFirstK_initial_everHit_le_logical
    (n : ℕ) (h3 : 3 ≤ n) (k : ℕ)
    (s : InfectionRevealPhysicalState n)
    (hk : 0 < k)
    (hroom : k + 2 ≤ s.inactive.ids.card)
    (B : InfectionRevealPrefixCheckpoint n → Prop)
    [DecidablePred B] :
    everHit
        (fun z =>
          B (InfectionRevealPrefixCheckpoint.ofPhysical
            (InfectionRevealFirstKQuotient.ofPath k z)))
        (infectionRevealPhysicalFirstKStep n h3 k)
        (infectionRevealPhysicalPathInitial s)
      ≤
        everHit B
          (InfectionRevealPrefixCheckpoint.oneStep n k)
          (.live s.inactive []) := by
  have h :=
    infectionRevealPhysicalFirstK_everHit_le_logical
      n h3 k (infectionRevealPhysicalPathInitial s)
      hroom B
  have hk0 : ¬ k ≤ ([] : List (Fin n)).length := by
    simp only [List.length_nil]
    omega
  have hkne : k ≠ 0 := by omega
  simpa [InfectionRevealFirstKQuotient.ofPath,
    InfectionRevealPrefixCheckpoint.ofPhysical,
    infectionRevealPhysicalPathInitial, hk0, hkne] using h

end

end Tri

#print axioms Tri.expect_infectionRevealPrefixTimeChangeLiveStep_everHit_le
#print axioms Tri.expect_infectionRevealPhysicalCheckpointLiveStep_everHit_le
#print axioms Tri.expect_infectionRevealFirstKQuotient_step_everHit_le_live
#print axioms Tri.infectionRevealPhysicalFirstKStep_anchor_eq_of_ne_zero
#print axioms Tri.expect_infectionRevealPhysicalFirstKStep_everHit_le
#print axioms Tri.infectionRevealPhysicalFirstK_everHit_le_logical
#print axioms Tri.infectionRevealPhysicalFirstK_initial_everHit_le_logical
