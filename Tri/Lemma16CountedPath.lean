/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Lemma16PhysicalUrn
import Tri.Lemma16ActiveCount
import Tri.Lemma16ActivationClock
import Tri.SameHorizon

/-!
# The joint physical path and all-active counter for Lemma 16

The state below runs the genuine identity-refined raw interaction, stops at
the first `k` newly activated identities, and counts every all-active
interaction before that stop.  It is the common probability space on which
the three Lemma 16 exceptional events are union-bounded.
-/

namespace Tri

open scoped ENNReal

noncomputable section

structure Lemma16CountedPathState (n : ℕ) where
  path : InfectionRevealPhysicalPathState n
  allActiveCount : ℕ

/-- Fresh joint state with no all-active interactions charged. -/
def lemma16CountedPathInitial
    {n : ℕ} (s : InfectionRevealPhysicalState n) :
    Lemma16CountedPathState n where
  path := infectionRevealPhysicalPathInitial s
  allActiveCount := 0

/-- Apply one genuine raw record and charge its all-active indicator. -/
def Lemma16CountedPathState.afterRecord
    {n : ℕ} (q : Lemma16CountedPathState n)
    (r : InfectionRevealRecord q.path.current) :
    Lemma16CountedPathState n where
  path := q.path.afterRecord r
  allActiveCount :=
    q.allActiveCount + r.event.allActiveInc

/-- Stop the joint process after its first `k` revealed identities. -/
noncomputable def lemma16CountedPathStep
    (n : ℕ) (h3 : 3 ≤ n) (k : ℕ) :
    Lemma16CountedPathState n →
      PMF (Lemma16CountedPathState n)
  | q =>
      if InfectionRevealPhysicalFirstKReached k q.path then
        PMF.pure q
      else
        (infectionRevealRecordPMF n h3
          q.path.current).map q.afterRecord

def lemma16CountedPathToPath
    {n : ℕ} (q : Lemma16CountedPathState n) :
    InfectionRevealPhysicalPathState n :=
  q.path

def lemma16CountedPathToCounter
    {n : ℕ} (q : Lemma16CountedPathState n) :
    InfectionState n × ℕ :=
  (q.path.current.coarse, q.allActiveCount)

/-- Forget the path and counter together. -/
def lemma16CountedPathToCoarse
    {n : ℕ} (q : Lemma16CountedPathState n) :
    InfectionState n :=
  q.path.current.coarse

/-- Immutable `X` counts add across disjoint activation batches. -/
theorem infectionRevealWordXCount_append_of_disjoint
    {n : ℕ} (label : Fin n → InfectionLabel)
    (u v : List (Fin n))
    (hdisjoint : Disjoint u.toFinset v.toFinset) :
    infectionRevealWordXCount label (u ++ v) =
      infectionRevealWordXCount label u +
        infectionRevealWordXCount label v := by
  unfold infectionRevealWordXCount
  rw [List.toFinset_append, Finset.filter_union]
  exact Finset.card_union_of_disjoint
    (hdisjoint.mono
      (Finset.filter_subset _ _)
      (Finset.filter_subset _ _))

/-- Immutable `Y` counts add across disjoint activation batches. -/
theorem infectionRevealWordYCount_append_of_disjoint
    {n : ℕ} (label : Fin n → InfectionLabel)
    (u v : List (Fin n))
    (hdisjoint : Disjoint u.toFinset v.toFinset) :
    infectionRevealWordYCount label (u ++ v) =
      infectionRevealWordYCount label u +
        infectionRevealWordYCount label v := by
  unfold infectionRevealWordYCount
  rw [List.toFinset_append, Finset.filter_union]
  exact Finset.card_union_of_disjoint
    (hdisjoint.mono
      (Finset.filter_subset _ _)
      (Finset.filter_subset _ _))

/-- A duplicate-free reveal word is partitioned by its immutable `X` and
`Y` labels. -/
theorem infectionRevealWordXCount_add_YCount
    {n : ℕ} (label : Fin n → InfectionLabel)
    (word : List (Fin n)) (hnodup : word.Nodup) :
    infectionRevealWordXCount label word +
        infectionRevealWordYCount label word =
      word.length := by
  classical
  have hfilter :
      word.toFinset.filter (fun i => ¬ label i = .X) =
        word.toFinset.filter (fun i => label i = .Y) := by
    ext i
    cases hlabel : label i <;> simp [hlabel]
  unfold infectionRevealWordXCount
    infectionRevealWordYCount
  rw [← hfilter]
  rw [Finset.card_filter_add_card_filter_not]
  exact List.toFinset_card_of_nodup hnodup

/-- A record's immutable `X` batch and successor inactive `X` population
partition the source inactive `X` population. -/
theorem InfectionRevealRecord.revealedX_card_add_after
    {n : ℕ} {s : InfectionRevealPhysicalState n}
    (r : InfectionRevealRecord s) :
    infectionRevealWordXCount
        s.inactive.initialLabel r.revealedIds +
      r.after.inactive.xIds.card =
    s.inactive.xIds.card := by
  unfold infectionRevealWordXCount
    InfectionInactiveView.xIds
  rw [r.after_initialLabel,
    ← r.revealedIds_union_after,
    Finset.filter_union]
  have hfiltered :
      Disjoint
        (r.revealedIds.toFinset.filter
          (fun i : Fin n =>
            s.inactive.initialLabel i = .X))
        (r.after.inactive.ids.filter
          (fun i : Fin n =>
            s.inactive.initialLabel i = .X)) :=
    r.revealedIds_disjoint_after.mono
      (Finset.filter_subset _ _)
      (Finset.filter_subset _ _)
  exact (Finset.card_union_of_disjoint
    hfiltered).symm

/-- The analogous immutable `Y` batch ledger. -/
theorem InfectionRevealRecord.revealedY_card_add_after
    {n : ℕ} {s : InfectionRevealPhysicalState n}
    (r : InfectionRevealRecord s) :
    infectionRevealWordYCount
        s.inactive.initialLabel r.revealedIds +
      r.after.inactive.yIds.card =
    s.inactive.yIds.card := by
  unfold infectionRevealWordYCount
    InfectionInactiveView.yIds
  rw [r.after_initialLabel,
    ← r.revealedIds_union_after,
    Finset.filter_union]
  have hfiltered :
      Disjoint
        (r.revealedIds.toFinset.filter
          (fun i : Fin n =>
            s.inactive.initialLabel i = .Y))
        (r.after.inactive.ids.filter
          (fun i : Fin n =>
            s.inactive.initialLabel i = .Y)) :=
    r.revealedIds_disjoint_after.mono
      (Finset.filter_subset _ _)
      (Finset.filter_subset _ _)
  exact (Finset.card_union_of_disjoint
    hfiltered).symm

/-- Coarse arithmetic behind the gap ledger. -/
theorem InfectionEvent.gap_charge_of_inactive_ledgers
    {n : ℕ} (s t : InfectionState n)
    (e : InfectionEvent) (batchX batchY : ℕ)
    (ht : t = InfectionEvent.nextState s e)
    (hx : batchX + t.1.ix = s.1.ix)
    (hy : batchY + t.1.iy = s.1.iy) :
    t.1.ay + s.1.ax + batchX ≤
      t.1.ax + s.1.ay + batchY +
        2 * e.allActiveInc := by
  subst t
  by_cases he : InfectionEvent.weight s.1 e = 0
  · simp [InfectionEvent.nextState, he] at hx hy ⊢
    omega
  · rw [InfectionEvent.nextState, dif_neg he] at hx hy ⊢
    cases e with
    | activeXXX =>
        simp [InfectionEvent.next,
          InfectionEvent.allActiveInc] at hx hy ⊢
        omega
    | activeXXY =>
        have hay : s.1.ay ≠ 0 :=
          (Nat.mul_ne_zero_iff.mp (by
            simpa only [InfectionEvent.weight] using he)).2
        simp [InfectionEvent.next,
          InfectionEvent.allActiveInc] at hx hy ⊢
        omega
    | activeXYY =>
        have hax : s.1.ax ≠ 0 :=
          (Nat.mul_ne_zero_iff.mp (by
            simpa only [InfectionEvent.weight] using he)).1
        simp [InfectionEvent.next,
          InfectionEvent.allActiveInc] at hx hy ⊢
        omega
    | activeYYY =>
        simp [InfectionEvent.next,
          InfectionEvent.allActiveInc] at hx hy ⊢
        omega
    | activateOneX =>
        have hix : s.1.ix ≠ 0 :=
          (Nat.mul_ne_zero_iff.mp (by
            simpa only [InfectionEvent.weight] using he)).2
        simp [InfectionEvent.next,
          InfectionEvent.allActiveInc] at hx hy ⊢
        omega
    | activateOneY =>
        have hiy : s.1.iy ≠ 0 :=
          (Nat.mul_ne_zero_iff.mp (by
            simpa only [InfectionEvent.weight] using he)).2
        simp [InfectionEvent.next,
          InfectionEvent.allActiveInc] at hx hy ⊢
        omega
    | activateTwoXX =>
        have hchoose : Nat.choose s.1.ix 2 ≠ 0 :=
          (Nat.mul_ne_zero_iff.mp (by
            simpa only [InfectionEvent.weight] using he)).2
        have hix : 2 ≤ s.1.ix :=
          Nat.choose_ne_zero_iff.mp hchoose
        simp [InfectionEvent.next,
          InfectionEvent.allActiveInc] at hx hy ⊢
        omega
    | activateTwoXY =>
        have hmul :
            s.1.active * s.1.ix * s.1.iy ≠ 0 := by
          simpa only [InfectionEvent.weight] using he
        have hix : s.1.ix ≠ 0 :=
          (Nat.mul_ne_zero_iff.mp
            (Nat.mul_ne_zero_iff.mp hmul).1).2
        have hiy : s.1.iy ≠ 0 :=
          (Nat.mul_ne_zero_iff.mp hmul).2
        simp [InfectionEvent.next,
          InfectionEvent.allActiveInc] at hx hy ⊢
        omega
    | activateTwoYY =>
        have hchoose : Nat.choose s.1.iy 2 ≠ 0 :=
          (Nat.mul_ne_zero_iff.mp (by
            simpa only [InfectionEvent.weight] using he)).2
        have hiy : 2 ≤ s.1.iy :=
          Nat.choose_ne_zero_iff.mp hchoose
        simp [InfectionEvent.next,
          InfectionEvent.allActiveInc] at hx hy ⊢
        omega
    | inactiveOnly =>
        simp [InfectionEvent.next,
          InfectionEvent.allActiveInc] at hx hy ⊢
        omega

/-- One physical record can worsen the active `Y-X` gap only through an
all-active interaction, charged at two units.  Activation labels themselves
cancel against the immutable-label batch ledger. -/
theorem InfectionRevealRecord.gap_charge
    {n : ℕ} {s : InfectionRevealPhysicalState n}
    (r : InfectionRevealRecord s) :
    r.after.coarse.1.ay + s.coarse.1.ax +
        infectionRevealWordXCount
          s.inactive.initialLabel r.revealedIds ≤
      r.after.coarse.1.ax + s.coarse.1.ay +
        infectionRevealWordYCount
          s.inactive.initialLabel r.revealedIds +
        2 * r.event.allActiveInc := by
  apply InfectionEvent.gap_charge_of_inactive_ledgers
      s.coarse r.after.coarse r.event
      (infectionRevealWordXCount
        s.inactive.initialLabel r.revealedIds)
      (infectionRevealWordYCount
        s.inactive.initialLabel r.revealedIds)
  · exact r.after_forget
  · simpa [r.after.hinactiveX, s.hinactiveX] using
      r.revealedX_card_add_after
  · simpa [r.after.hinactiveY, s.hinactiveY] using
      r.revealedY_card_add_after

/-- Deterministic opinion-gap ledger on the joint path. -/
def Lemma16CountedPathGapLedger
    {n : ℕ} (q : Lemma16CountedPathState n) : Prop :=
  q.path.current.coarse.1.ay +
      q.path.anchor.coarse.1.ax +
      infectionRevealWordXCount
        q.path.anchor.inactive.initialLabel
        q.path.revealed ≤
    q.path.current.coarse.1.ax +
      q.path.anchor.coarse.1.ay +
      infectionRevealWordYCount
        q.path.anchor.inactive.initialLabel
        q.path.revealed +
      2 * q.allActiveCount

/-- The bad immutable-label prefix event pulled back to the counted path. -/
def Lemma16CountedPathPrefixBad
    {n : ℕ} (s : InfectionRevealPhysicalState n)
    (rho k : ℕ) (q : Lemma16CountedPathState n) : Prop :=
  Lemma16LogicalPrefixBad
    s.inactive.initialLabel rho
    (InfectionRevealPrefixCheckpoint.ofPhysical
      (InfectionRevealFirstKQuotient.ofPath k q.path))

noncomputable instance lemma16CountedPathPrefixBadDecidable
    {n : ℕ} (s : InfectionRevealPhysicalState n)
    (rho k : ℕ) :
    DecidablePred (Lemma16CountedPathPrefixBad s rho k) :=
  Classical.decPred _

/-- Lemma 16's terminal active-opinion gap. -/
def Lemma16CountedPathGood
    {n : ℕ} (a rho cStar : ℕ)
    (q : Lemma16CountedPathState n) : Prop :=
  a ≤ q.path.current.coarse.1.active ∧
    q.path.current.coarse.1.active ≤ a + 1 ∧
      q.path.current.coarse.1.ay ≤
        q.path.current.coarse.1.ax + 3 * cStar * rho

noncomputable instance lemma16CountedPathGoodDecidable
    {n : ℕ} (a rho cStar : ℕ) :
    DecidablePred
      (@Lemma16CountedPathGood n a rho cStar) :=
  Classical.decPred _

/-- Applying one record preserves the deterministic gap ledger. -/
theorem Lemma16CountedPathGapLedger.afterRecord
    {n : ℕ} (q : Lemma16CountedPathState n)
    (r : InfectionRevealRecord q.path.current)
    (hq : Lemma16CountedPathGapLedger q) :
    Lemma16CountedPathGapLedger (q.afterRecord r) := by
  have hbatchDisjoint :
      Disjoint q.path.revealed.toFinset
        r.revealedIds.toFinset :=
    q.path.hdisjoint.mono_right
      r.revealedIds_toFinset_subset
  have hX :=
    infectionRevealWordXCount_append_of_disjoint
      q.path.anchor.inactive.initialLabel
      q.path.revealed r.revealedIds
      hbatchDisjoint
  have hY :=
    infectionRevealWordYCount_append_of_disjoint
      q.path.anchor.inactive.initialLabel
      q.path.revealed r.revealedIds
      hbatchDisjoint
  have hcharge := r.gap_charge
  rw [q.path.hinitialLabel] at hcharge
  unfold Lemma16CountedPathGapLedger at hq ⊢
  simp only [Lemma16CountedPathState.afterRecord,
    InfectionRevealPhysicalPathState.afterRecord]
  rw [hX, hY]
  omega

/-- The stopped counted kernel preserves the gap ledger on support. -/
theorem lemma16CountedPathStep_gapLedger_closed
    (n : ℕ) (h3 : 3 ≤ n) (k : ℕ)
    (q z : Lemma16CountedPathState n)
    (hq : Lemma16CountedPathGapLedger q)
    (hz : lemma16CountedPathStep n h3 k q z ≠ 0) :
    Lemma16CountedPathGapLedger z := by
  by_cases hreach :
      InfectionRevealPhysicalFirstKReached k q.path
  · have hzq : z = q := by
      unfold lemma16CountedPathStep at hz
      rw [if_pos hreach] at hz
      by_contra hne
      simp [PMF.pure_apply, hne] at hz
    simpa [hzq] using hq
  · unfold lemma16CountedPathStep at hz
    rw [if_neg hreach] at hz
    have hzmem :
        z ∈
          ((infectionRevealRecordPMF n h3
            q.path.current).map q.afterRecord).support :=
      hz
    rw [PMF.support_map] at hzmem
    rcases hzmem with ⟨r, hr, rfl⟩
    exact hq.afterRecord q r

/-- Every supported terminal state of the joint process satisfies the gap
ledger. -/
theorem lemma16CountedPath_iter_gapLedger
    (n : ℕ) (h3 : 3 ≤ n) (k T : ℕ)
    (s : InfectionRevealPhysicalState n)
    (z : Lemma16CountedPathState n)
    (hz :
      iter (lemma16CountedPathStep n h3 k) T
        (lemma16CountedPathInitial s) z ≠ 0) :
    Lemma16CountedPathGapLedger z := by
  have hinit :
      Lemma16CountedPathGapLedger
        (lemma16CountedPathInitial s) := by
    simp [Lemma16CountedPathGapLedger,
      lemma16CountedPathInitial,
      infectionRevealPhysicalPathInitial,
      infectionRevealWordXCount,
      infectionRevealWordYCount]
    omega
  exact
    iter_support_closed
      (lemma16CountedPathStep n h3 k)
      Lemma16CountedPathGapLedger
      (fun q hq z hz =>
        lemma16CountedPathStep_gapLedger_closed
          n h3 k q z hq hz)
      T (lemma16CountedPathInitial s) z
      hinit hz

/-- Reachable joint states keep their anchor and overshoot the first `k`
prefix by at most one identity. -/
def Lemma16CountedPathInv
    {n : ℕ} (s : InfectionRevealPhysicalState n)
    (k : ℕ) (q : Lemma16CountedPathState n) : Prop :=
  q.path.anchor = s ∧ q.path.revealed.length ≤ k + 1

/-- If the activation checkpoint is reached, the immutable prefix is good,
and the charged all-active counter is below threshold, the terminal active
opinion gap satisfies Lemma 16.  A two-activation crossing can contribute one
overshoot identity beyond the durable first-`k` prefix. -/
theorem lemma16CountedPath_good_of_prefix_and_counter
    (n a k rho cStar : ℕ)
    (s : InfectionRevealPhysicalState n)
    (q : Lemma16CountedPathState n)
    (hk : k + 1 = a)
    (hanchorActive : s.coarse.1.active + k = a)
    (hrho : 1 ≤ rho)
    (hcStar : 9 ≤ cStar)
    (hinv : Lemma16CountedPathInv s k q)
    (hgap : Lemma16CountedPathGapLedger q)
    (hreached : a ≤ q.path.current.coarse.1.active)
    (hprefix :
      ¬ Lemma16CountedPathPrefixBad s rho k q)
    (hcount :
      3 * q.allActiveCount ≤ 4 * cStar * rho) :
    q.path.current.coarse.1.ay ≤
      q.path.current.coarse.1.ax +
        3 * cStar * rho := by
  have hanchor :
      q.path.anchor.coarse.1.active =
        s.coarse.1.active := by
    rw [hinv.1]
  have hactiveLedger := q.path.hactiveLedger
  have hkreached : k ≤ q.path.revealed.length := by
    omega
  have hprefixGood :
      infectionRevealWordYCount
          s.inactive.initialLabel
          (q.path.revealed.take k) ≤
        infectionRevealWordXCount
            s.inactive.initialLabel
            (q.path.revealed.take k) +
          rho := by
    have hnot :
        ¬ (infectionRevealWordXCount
              s.inactive.initialLabel
              (q.path.revealed.take k) +
            rho <
          infectionRevealWordYCount
            s.inactive.initialLabel
            (q.path.revealed.take k)) := by
      simpa [Lemma16CountedPathPrefixBad,
        InfectionRevealFirstKQuotient.ofPath,
        InfectionRevealPrefixCheckpoint.ofPhysical,
        Lemma16LogicalPrefixBad, hkreached] using hprefix
    omega
  let pref := q.path.revealed.take k
  let suff := q.path.revealed.drop k
  have hdecomp :
      pref ++ suff = q.path.revealed := by
    exact List.take_append_drop k q.path.revealed
  have hparts :
      pref.Nodup ∧ suff.Nodup ∧
        Disjoint pref.toFinset suff.toFinset := by
    have hp :
        pref.Nodup ∧ suff.Nodup ∧
          ∀ a ∈ pref, ∀ b ∈ suff, a ≠ b := by
      apply List.nodup_append.mp
      rw [hdecomp]
      exact q.path.hnodup
    refine ⟨hp.1, hp.2.1, ?_⟩
    rw [Finset.disjoint_left]
    intro i hiPref hiSuff
    exact
      (hp.2.2 i (List.mem_toFinset.mp hiPref)
        i (List.mem_toFinset.mp hiSuff)) rfl
  have hXappend :=
    infectionRevealWordXCount_append_of_disjoint
      s.inactive.initialLabel pref suff hparts.2.2
  have hYappend :=
    infectionRevealWordYCount_append_of_disjoint
      s.inactive.initialLabel pref suff hparts.2.2
  have hsuffixLabels :=
    infectionRevealWordXCount_add_YCount
      s.inactive.initialLabel suff hparts.2.1
  have hlengthLimit :
      q.path.revealed.length ≤ k + 1 :=
    hinv.2
  have hsuffixLength : suff.length ≤ 1 := by
    dsimp only [suff]
    rw [List.length_drop]
    omega
  have hprefixGood' :
      infectionRevealWordYCount
          s.inactive.initialLabel pref ≤
        infectionRevealWordXCount
            s.inactive.initialLabel pref +
          rho := by
    simpa [pref] using hprefixGood
  have hfullLabels :
      infectionRevealWordYCount
          s.inactive.initialLabel q.path.revealed ≤
        infectionRevealWordXCount
            s.inactive.initialLabel q.path.revealed +
          rho + 1 := by
    rw [← hdecomp, hXappend, hYappend]
    omega
  have hactiveOne : s.coarse.1.active = 1 := by
    omega
  have hseed :
      s.coarse.1.ay ≤ s.coarse.1.ax + 1 := by
    simp only [InfectionCfg.active] at hactiveOne
    omega
  have hgap' := hgap
  unfold Lemma16CountedPathGapLedger at hgap'
  rw [hinv.1] at hgap'
  have hledger :
      q.path.current.coarse.1.ay ≤
        q.path.current.coarse.1.ax +
          rho + 2 + 2 * q.allActiveCount := by
    omega
  exact
    lemma16_good_of_label_and_counter_overshoot
      q.path.current.coarse.1.ax
      q.path.current.coarse.1.ay
      q.allActiveCount rho cStar
      hrho hcStar hledger hcount

/-- Forgetting the counter gives the genuine physical first-prefix path
kernel exactly. -/
theorem lemma16CountedPathStep_map_path
    (n : ℕ) (h3 : 3 ≤ n) (k : ℕ)
    (q : Lemma16CountedPathState n) :
    (lemma16CountedPathStep n h3 k q).map
        lemma16CountedPathToPath =
      infectionRevealPhysicalFirstKStep n h3 k q.path := by
  by_cases hreach :
      InfectionRevealPhysicalFirstKReached k q.path
  · unfold lemma16CountedPathStep
      infectionRevealPhysicalFirstKStep
    rw [if_pos hreach, freeze_of_mem q.path hreach,
      PMF.pure_map]
    rfl
  · unfold lemma16CountedPathStep
      infectionRevealPhysicalFirstKStep
    rw [if_neg hreach, freeze_of_not_mem q.path hreach,
      PMF.map_comp]
    rfl

/-- The immutable-label prefix tail transfers exactly from the stopped
physical path to the joint counted path. -/
theorem lemma16CountedPath_prefix_tail
    (n : ℕ) (h3 : 3 ≤ n)
    (q rho a k u nu R B : ℕ)
    (s : InfectionRevealPhysicalState n)
    (hqa : q * a ≤ rho ^ 2)
    (hnu : nu + 1 = n)
    (hk : k + 1 = a)
    (huk : u + k + 1 = nu)
    (hRB : R + B = nu)
    (hquarter : 4 * a ≤ n)
    (hmajor : R ≤ B)
    (hx0 : s.inactive.xIds.card = B)
    (hy0 : s.inactive.yIds.card = R)
    (hk0 : 0 < k) :
    everHit
        (Lemma16CountedPathPrefixBad s rho k)
        (lemma16CountedPathStep n h3 k)
        (lemma16CountedPathInitial s)
      ≤ lemma16UrnError q := by
  let Target : InfectionRevealPhysicalPathState n → Prop :=
    fun z =>
      Lemma16LogicalPrefixBad
        s.inactive.initialLabel rho
        (InfectionRevealPrefixCheckpoint.ofPhysical
          (InfectionRevealFirstKQuotient.ofPath k z))
  have htransfer :
      everHit
          (Lemma16CountedPathPrefixBad s rho k)
          (lemma16CountedPathStep n h3 k)
          (lemma16CountedPathInitial s) =
        everHit Target
          (infectionRevealPhysicalFirstKStep n h3 k)
          (infectionRevealPhysicalPathInitial s) := by
    unfold everHit
    simpa [Target, Lemma16CountedPathPrefixBad,
      lemma16CountedPathInitial,
      lemma16CountedPathToPath] using
      iSup_hitProb_transfer
        (lemma16CountedPathStep_map_path n h3 k)
        Target (lemma16CountedPathInitial s)
  rw [htransfer]
  exact
    infectionRevealPhysical_lemma16_prefix_tail
      n h3 q rho a k u nu R B s
      hqa hnu hk huk hRB hquarter hmajor
      hx0 hy0 hk0

/-- Before the prefix stop, the coarse-state/counter projection is the
existing capped all-active counter kernel. -/
theorem lemma16CountedPathStep_map_counter_of_live
    (n : ℕ) (h3 : 3 ≤ n) (k a : ℕ)
    (q : Lemma16CountedPathState n)
    (hlive :
      ¬ InfectionRevealPhysicalFirstKReached k q.path)
    (hactive : ¬ a < q.path.current.coarse.1.active) :
    (lemma16CountedPathStep n h3 k q).map
        lemma16CountedPathToCounter =
      infectionAllActiveCount n h3 a
        (lemma16CountedPathToCounter q) := by
  unfold lemma16CountedPathStep
    infectionAllActiveCount
  rw [if_neg hlive]
  change
    ((infectionRevealRecordPMF n h3
      q.path.current).map q.afterRecord).map
        lemma16CountedPathToCounter =
      if a < q.path.current.coarse.1.active then
        PMF.pure
          (q.path.current.coarse,
            q.allActiveCount)
      else
        (infectionEventPMF
          q.path.current.coarse.1 _).map
            (fun e =>
              (InfectionEvent.nextState
                q.path.current.coarse e,
                q.allActiveCount +
                  e.allActiveInc))
  rw [if_neg hactive, PMF.map_comp]
  change
    (infectionRevealRecordPMF n h3
      q.path.current).map
        (fun r =>
          (r.after.coarse,
            q.allActiveCount + r.event.allActiveInc)) =
      (infectionEventPMF q.path.current.coarse.1 _).map
        (fun e =>
          (InfectionEvent.nextState
            q.path.current.coarse e,
            q.allActiveCount + e.allActiveInc))
  calc
    (infectionRevealRecordPMF n h3
        q.path.current).map
          (fun r =>
            (r.after.coarse,
              q.allActiveCount + r.event.allActiveInc)) =
      (infectionRevealRecordPMF n h3
        q.path.current).map
          ((fun e =>
            (InfectionEvent.nextState
              q.path.current.coarse e,
              q.allActiveCount + e.allActiveInc)) ∘
            InfectionRevealRecord.event) := by
              congr 1
              funext r
              rw [Function.comp_apply,
                ← r.after_forget]
              rfl
    _ =
      ((infectionRevealRecordPMF n h3
        q.path.current).map
          InfectionRevealRecord.event).map
            (fun e =>
              (InfectionEvent.nextState
                q.path.current.coarse e,
                q.allActiveCount + e.allActiveInc)) := by
                  rw [PMF.map_comp]
    _ =
      (infectionEventPMF
        q.path.current.coarse.1 _).map
          (fun e =>
            (InfectionEvent.nextState
              q.path.current.coarse e,
              q.allActiveCount + e.allActiveInc)) := by
                rw [
                  infectionRevealRecordPMF_map_event]

/-- Support closure of the counted-path invariant. -/
theorem lemma16CountedPathStep_inv_closed
    (n : ℕ) (h3 : 3 ≤ n) (k : ℕ)
    (s : InfectionRevealPhysicalState n)
    (q z : Lemma16CountedPathState n)
    (hq : Lemma16CountedPathInv s k q)
    (hz : lemma16CountedPathStep n h3 k q z ≠ 0) :
    Lemma16CountedPathInv s k z := by
  by_cases hreach :
      InfectionRevealPhysicalFirstKReached k q.path
  · have hzq : z = q := by
      unfold lemma16CountedPathStep at hz
      rw [if_pos hreach] at hz
      by_contra hne
      simp [PMF.pure_apply, hne] at hz
    simpa [hzq] using hq
  · unfold lemma16CountedPathStep at hz
    rw [if_neg hreach] at hz
    have hzmem :
        z ∈
          ((infectionRevealRecordPMF n h3
            q.path.current).map q.afterRecord).support :=
      hz
    rw [PMF.support_map] at hzmem
    rcases hzmem with ⟨r, hr, rfl⟩
    refine ⟨hq.1, ?_⟩
    simp only [Lemma16CountedPathState.afterRecord,
      InfectionRevealPhysicalPathState.afterRecord,
      List.length_append]
    have hlt : q.path.revealed.length < k := by
      simpa [InfectionRevealPhysicalFirstKReached] using hreach
    have hbatch : r.revealedIds.length ≤ 2 := by
      rw [r.revealedIds_length]
      exact
        InfectionEvent.realizedActivationInc_le_two
          q.path.current.coarse.1 r.event
    omega

/-- On the reachable anchored fibre, stopping at the first `k` reveals is
exactly stopping the coarse chain at active population `a`. -/
theorem lemma16CountedPathStep_map_coarse_on_inv
    (n : ℕ) (h3 : 3 ≤ n) (a k : ℕ)
    (s : InfectionRevealPhysicalState n)
    (hanchorActive : s.coarse.1.active + k = a)
    (q : Lemma16CountedPathState n)
    (hq : Lemma16CountedPathInv s k q) :
    (lemma16CountedPathStep n h3 k q).map
        lemma16CountedPathToCoarse =
      freeze (fun u : InfectionState n => a ≤ u.1.active)
        (infectionStateStep n h3)
        (lemma16CountedPathToCoarse q) := by
  have hanchor :
      q.path.anchor.coarse.1.active =
        s.coarse.1.active := by
    rw [hq.1]
  have hledger := q.path.hactiveLedger
  by_cases hreach :
      InfectionRevealPhysicalFirstKReached k q.path
  · have htarget :
        a ≤ (lemma16CountedPathToCoarse q).1.active := by
      simp only [lemma16CountedPathToCoarse]
      simp only [InfectionRevealPhysicalFirstKReached] at hreach
      omega
    unfold lemma16CountedPathStep
    rw [if_pos hreach, PMF.pure_map]
    simp [freeze, htarget]
  · have htarget :
        ¬ a ≤ (lemma16CountedPathToCoarse q).1.active := by
      simp only [lemma16CountedPathToCoarse]
      simp only [InfectionRevealPhysicalFirstKReached] at hreach
      omega
    calc
      (lemma16CountedPathStep n h3 k q).map
          lemma16CountedPathToCoarse =
        ((lemma16CountedPathStep n h3 k q).map
          lemma16CountedPathToPath).map
            infectionRevealPhysicalPathForget := by
              rw [PMF.map_comp]
              rfl
      _ =
        (infectionRevealPhysicalFirstKStep n h3 k q.path).map
          infectionRevealPhysicalPathForget := by
            rw [lemma16CountedPathStep_map_path]
      _ =
        (infectionRevealPhysicalPathStep n h3 q.path).map
          infectionRevealPhysicalPathForget := by
            unfold infectionRevealPhysicalFirstKStep
            rw [freeze_of_not_mem q.path hreach]
      _ = infectionStateStep n h3
          (lemma16CountedPathToCoarse q) := by
            exact
              infectionRevealPhysicalPathStep_map_forget
                n h3 q.path
      _ =
        freeze (fun u : InfectionState n => a ≤ u.1.active)
          (infectionStateStep n h3)
          (lemma16CountedPathToCoarse q) := by
            simp [freeze, htarget]

/-- The invariant-restricted coarse projection remains exact at every
horizon. -/
theorem lemma16CountedPath_iter_map_coarse_on_inv
    (n : ℕ) (h3 : 3 ≤ n) (a k T : ℕ)
    (s : InfectionRevealPhysicalState n)
    (hanchorActive : s.coarse.1.active + k = a)
    (q : Lemma16CountedPathState n)
    (hq : Lemma16CountedPathInv s k q) :
    (iter (lemma16CountedPathStep n h3 k) T q).map
        lemma16CountedPathToCoarse =
      iter
        (freeze (fun u : InfectionState n => a ≤ u.1.active)
          (infectionStateStep n h3))
        T (lemma16CountedPathToCoarse q) := by
  exact
    iter_map_of_step_map_on_support_invariant
      (lemma16CountedPathStep n h3 k)
      (freeze (fun u : InfectionState n => a ≤ u.1.active)
        (infectionStateStep n h3))
      lemma16CountedPathToCoarse
      (Lemma16CountedPathInv s k)
      (fun q hq z hz =>
        lemma16CountedPathStep_inv_closed
          n h3 k s q z hq hz)
      (lemma16CountedPathStep_map_coarse_on_inv
        n h3 a k s hanchorActive)
      T q hq

/-- The genuine counted path reaches its first-`k` activation checkpoint by
the Lemma 16 epidemic deadline, except for the epidemic error. -/
theorem lemma16CountedPath_epidemic_deadline
    (n q a k cStar : ℕ)
    (h3 : 3 ≤ n)
    (hlog : Nat.log 2 n ≤ q)
    (hquarter : 4 * a ≤ n)
    (hcStar : 640 ≤ cStar)
    (s : InfectionRevealPhysicalState n)
    (hstart : 1 ≤ s.coarse.1.active)
    (hanchorActive : s.coarse.1.active + k = a) :
    terminalFailureMass
      (iter (lemma16CountedPathStep n h3 k)
        (cStar * q * n)
        (lemma16CountedPathInitial s))
      (fun z => a ≤ z.path.current.coarse.1.active) ≤
    lemma16EpidemicError q := by
  let A : InfectionState n → Prop :=
    fun u => a ≤ u.1.active
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
      n h3 a k (cStar * q * n) s hanchorActive
      (lemma16CountedPathInitial s) hinit
  have horiginal :
      terminalFailureMass
        (iter K (cStar * q * n) s.coarse) A ≤
      lemma16EpidemicError q := by
    exact
      infectionActivation_lemma16_deadline
        n q a cStar h3 hlog hquarter hcStar
        s.coarse hstart
  have hlazy : IsLazyProjection K K (fun u => u) := by
    intro u
    left
    simpa using PMF.map_id (K u)
  have hfreeze :
      terminalFailureMass
        (iter (freeze A K) (cStar * q * n) s.coarse) A ≤
      terminalFailureMass
        (iter K (cStar * q * n) s.coarse) A := by
    simpa [A, K] using
      targetFreeze_failure_le_lazy_projection
        A K K (fun u => u) hlazy
        (cStar * q * n) s.coarse
  calc
    terminalFailureMass
        (iter (lemma16CountedPathStep n h3 k)
          (cStar * q * n)
          (lemma16CountedPathInitial s))
        (fun z => a ≤ z.path.current.coarse.1.active) =
      terminalFailureMass
        ((iter (lemma16CountedPathStep n h3 k)
          (cStar * q * n)
          (lemma16CountedPathInitial s)).map
            lemma16CountedPathToCoarse) A := by
              symm
              exact terminalFailureMass_map _ _ _
    _ =
      terminalFailureMass
        (iter (freeze A K)
          (cStar * q * n) s.coarse) A := by
            rw [hmap]
            rfl
    _ ≤ terminalFailureMass
        (iter K (cStar * q * n) s.coarse) A :=
          hfreeze
    _ ≤ lemma16EpidemicError q := horiginal

/-- The cubic-envelope MGF step holds on the reachable counted-path
invariant. -/
theorem expect_lemma16CountedPathStep_allActive_le
    (n : ℕ) (h3 : 3 ≤ n) (a k : ℕ)
    (ha : a ≤ n)
    (s : InfectionRevealPhysicalState n)
    (hanchorActive : s.coarse.1.active + k = a)
    (w : ℝ≥0∞) (hw1 : 1 ≤ w) (hwt : w ≠ ⊤)
    (q : Lemma16CountedPathState n)
    (hq : Lemma16CountedPathInv s k q) :
    expect
        (lemma16CountedPathStep n h3 k q)
        (fun z => w ^ z.allActiveCount)
      ≤
        (infectionAllActiveCubeCompl n a +
          infectionAllActiveCube n a * w) *
            w ^ q.allActiveCount := by
  let factor :=
    infectionAllActiveCubeCompl n a +
      infectionAllActiveCube n a * w
  have hfactor : 1 ≤ factor := by
    have hmono :=
      upper_step_factor_monotone_ennreal
        (p := infectionAllActiveCube n a)
        (p' := infectionAllActiveCubeCompl n a)
        (q := 0) (q' := 1) (w := w)
        (infectionAllActiveCube_add_compl n a h3 ha)
        (by simp)
        hw1 bot_le hwt
    simpa [factor] using hmono
  by_cases hreach :
      InfectionRevealPhysicalFirstKReached k q.path
  · unfold lemma16CountedPathStep
    rw [if_pos hreach, expect_pure]
    calc
      w ^ q.allActiveCount =
          1 * w ^ q.allActiveCount := by rw [one_mul]
      _ ≤ factor * w ^ q.allActiveCount := by
        simpa [mul_comm] using
        mul_le_mul_right hfactor
          (w ^ q.allActiveCount)
  · have hlt : q.path.revealed.length < k := by
      simpa [InfectionRevealPhysicalFirstKReached] using hreach
    have hactiveLedger := q.path.hactiveLedger
    have hanchor :
        q.path.anchor.coarse.1.active =
          s.coarse.1.active := by rw [hq.1]
    have hactive :
        ¬ a < q.path.current.coarse.1.active := by
      omega
    calc
      expect
          (lemma16CountedPathStep n h3 k q)
          (fun z => w ^ z.allActiveCount) =
        expect
          ((lemma16CountedPathStep n h3 k q).map
            lemma16CountedPathToCounter)
          (fun z => w ^ z.2) := by
              rw [expect_map]
              rfl
      _ =
        expect
          (infectionAllActiveCount n h3 a
            (lemma16CountedPathToCounter q))
          (fun z => w ^ z.2) := by
              rw [
                lemma16CountedPathStep_map_counter_of_live
                  n h3 k a q hreach hactive]
      _ ≤
        (infectionAllActiveCapCompl n a +
          infectionAllActiveCap n a * w) *
            w ^ q.allActiveCount := by
              exact
                infectionAllActiveCount_step
                  n h3 a ha w hw1 hwt
                  (lemma16CountedPathToCounter q)
      _ ≤ factor * w ^ q.allActiveCount := by
              simpa [factor, mul_comm] using
                mul_le_mul_right
                  (infectionAllActive_factor_le_cube
                    n a h3 ha w hw1 hwt)
                  (w ^ q.allActiveCount)

/-- Upper tail for the all-active counter on the genuine stopped physical
path.  The one-step estimate is used only on its reachable invariant. -/
theorem lemma16CountedPath_allActive_tail
    (n : ℕ) (h3 : 3 ≤ n) (a k : ℕ)
    (ha : a ≤ n)
    (s : InfectionRevealPhysicalState n)
    (hanchorActive : s.coarse.1.active + k = a)
    (w : ℝ≥0∞) (hw1 : 1 ≤ w) (hwt : w ≠ ⊤)
    (T M : ℕ) :
    (∑' z, if M ≤ z.allActiveCount then
        iter (lemma16CountedPathStep n h3 k) T
          (lemma16CountedPathInitial s) z
      else 0) ≤
    (infectionAllActiveCubeCompl n a +
        infectionAllActiveCube n a * w) ^ T /
      w ^ M := by
  have hw0 : w ≠ 0 := by
    intro hwz
    rw [hwz] at hw1
    simp at hw1
  let theta : ℝ≥0∞ := w ^ M
  have htheta0 : theta ≠ 0 := pow_ne_zero _ hw0
  have hthetatop : theta ≠ ⊤ := ENNReal.pow_ne_top hwt
  have hinit :
      Lemma16CountedPathInv s k
        (lemma16CountedPathInitial s) := by
    constructor
    · rfl
    · simp [lemma16CountedPathInitial,
        infectionRevealPhysicalPathInitial]
  have hsub : ∀ z,
      (if M ≤ z.allActiveCount then
          iter (lemma16CountedPathStep n h3 k) T
            (lemma16CountedPathInitial s) z
        else 0) ≤
      (if theta ≤ w ^ z.allActiveCount then
          iter (lemma16CountedPathStep n h3 k) T
            (lemma16CountedPathInitial s) z
        else 0) := by
    intro z
    by_cases hz : M ≤ z.allActiveCount
    · have hpow : theta ≤ w ^ z.allActiveCount := by
        dsimp only [theta]
        exact pow_le_pow_right₀ hw1 hz
      simp [hz, hpow]
    · simp [hz]
  refine le_trans (ENNReal.tsum_le_tsum hsub) ?_
  refine le_trans
    (markov_div
      (iter (lemma16CountedPathStep n h3 k) T
        (lemma16CountedPathInitial s))
      (fun z => w ^ z.allActiveCount)
      theta htheta0 hthetatop) ?_
  have hiter :=
    expect_iter_le_of_support_invariant
      (lemma16CountedPathStep n h3 k)
      (Lemma16CountedPathInv s k)
      (fun z => w ^ z.allActiveCount)
      (infectionAllActiveCubeCompl n a +
        infectionAllActiveCube n a * w)
      (fun q hq z hz =>
        lemma16CountedPathStep_inv_closed
          n h3 k s q z hq hz)
      (expect_lemma16CountedPathStep_allActive_le
        n h3 a k ha s hanchorActive w hw1 hwt)
      T (lemma16CountedPathInitial s) hinit
  exact ENNReal.div_le_div_right
    (by simpa [lemma16CountedPathInitial] using hiter)
    theta

/-- The genuine counted physical path has the stronger denominator-20
reaction tail used before normalization. -/
theorem lemma16CountedPath_reaction_tail_twentieth
    (n : ℕ) (h3 : 3 ≤ n)
    (a k : ℕ) (ha : a ≤ n)
    (s : InfectionRevealPhysicalState n)
    (hanchorActive : s.coarse.1.active + k = a)
    (q rho cStar : ℕ)
    (hmean : q * a ^ 3 ≤ rho * n ^ 2) :
    (∑' z, if 4 * cStar * rho < 3 * z.allActiveCount then
        iter (lemma16CountedPathStep n h3 k)
          (cStar * q * n)
          (lemma16CountedPathInitial s) z
      else 0) ≤
    ENNReal.ofReal
      (Real.exp (-(((cStar * rho : ℕ) : ℝ) / 20))) := by
  let m : ℕ := cStar * rho
  let T : ℕ := cStar * q * n
  let M : ℕ := 4 * m / 3 + 1
  let cube : ℝ≥0∞ := infectionAllActiveCube n a
  let cubeCompl : ℝ≥0∞ := infectionAllActiveCubeCompl n a
  have hpartition : cubeCompl + cube = 1 := by
    simpa [cube, cubeCompl, add_comm] using
      infectionAllActiveCube_add_compl n a h3 ha
  have hmu : (T : ℝ≥0∞) * cube ≤ (m : ℝ≥0∞) := by
    simpa [T, m, cube, infectionAllActiveCube] using
      lemma16_cube_mean_le n a q rho cStar h3 hmean
  have hw1 : (1 : ℝ≥0∞) ≤ 4 / 3 := by
    rw [ENNReal.le_div_iff_mul_le
      (Or.inl (by norm_num)) (Or.inl (by norm_num))]
    norm_num
  have hwt : (4 / 3 : ℝ≥0∞) ≠ ⊤ := by
    finiteness
  have hraw :=
    lemma16CountedPath_allActive_tail
      n h3 a k ha s hanchorActive
      ((4 : ℝ≥0∞) / 3) hw1 hwt
      T M
  have hraw' :
      (∑' z, if M ≤ z.allActiveCount then
          iter (lemma16CountedPathStep n h3 k) T
            (lemma16CountedPathInitial s) z
        else 0) ≤
      ((cubeCompl + cube * ((4 : ℝ≥0∞) / 3)) ^ T) /
        (((4 : ℝ≥0∞) / 3) ^ M) := by
    simpa [cube, cubeCompl] using hraw
  calc
    (∑' z, if 4 * cStar * rho < 3 * z.allActiveCount then
        iter (lemma16CountedPathStep n h3 k)
          (cStar * q * n)
          (lemma16CountedPathInitial s) z
      else 0) =
      (∑' z, if M ≤ z.allActiveCount then
          iter (lemma16CountedPathStep n h3 k) T
            (lemma16CountedPathInitial s) z
        else 0) := by
          apply tsum_congr
          intro z
          have hthreshold :
              4 * cStar * rho < 3 * z.allActiveCount ↔
                M ≤ z.allActiveCount := by
            simpa [M, m, Nat.mul_assoc] using
              lemma16_strict_counter_threshold
                (cStar * rho) z.allActiveCount
          simp [T, hthreshold]
    _ ≤ ((cubeCompl + cube * ((4 : ℝ≥0∞) / 3)) ^ T) /
          (((4 : ℝ≥0∞) / 3) ^ M) := hraw'
    _ ≤ ENNReal.ofReal
          (Real.exp (-((m : ℝ) / 20))) := by
            simpa [M] using
              four_thirds_floor_tail_ennreal
                hpartition T m hmu
    _ = ENNReal.ofReal
          (Real.exp
            (-(((cStar * rho : ℕ) : ℝ) / 20))) := by
            rfl

/-- Normalized Lemma 16 reaction error on the genuine stopped physical
path. -/
theorem lemma16CountedPath_reaction_tail
    (n : ℕ) (h3 : 3 ≤ n)
    (a k : ℕ) (ha : a ≤ n)
    (s : InfectionRevealPhysicalState n)
    (hanchorActive : s.coarse.1.active + k = a)
    (q rho cStar : ℕ)
    (hmean : q * a ^ 3 ≤ rho * n ^ 2) :
    (∑' z, if 4 * cStar * rho < 3 * z.allActiveCount then
        iter (lemma16CountedPathStep n h3 k)
          (cStar * q * n)
          (lemma16CountedPathInitial s) z
      else 0) ≤
    lemma16ReactionError cStar rho := by
  calc
    _ ≤ ENNReal.ofReal
        (Real.exp
          (-(((cStar * rho : ℕ) : ℝ) / 20))) :=
      lemma16CountedPath_reaction_tail_twentieth
        n h3 a k ha s hanchorActive
        q rho cStar hmean
    _ ≤ lemma16ReactionError cStar rho := by
      unfold lemma16ReactionError
      apply ENNReal.ofReal_mono
      apply Real.exp_le_exp.mpr
      have hm : 0 ≤ (((cStar * rho : ℕ) : ℝ)) := by
        positivity
      nlinarith

/-- Paper Lemma 16 on the genuine raw-interaction clock.  The terminal active
`Y` excess is controlled by the union of the immutable-prefix, epidemic-clock,
and all-active-reaction exceptional events. -/
theorem lemma16CountedPath
    (n q a k u nu R B rho cStar : ℕ)
    (h3 : 3 ≤ n)
    (hlog : Nat.log 2 n ≤ q)
    (hquarter : 4 * a ≤ n)
    (hcStar : 640 ≤ cStar)
    (hroot : a ^ 5 * q * n ≤ n ^ 5)
    (hqa : q * a ≤ rho ^ 2)
    (hrho : 1 ≤ rho)
    (hnu : nu + 1 = n)
    (hk : k + 1 = a)
    (huk : u + k + 1 = nu)
    (hRB : R + B = nu)
    (hmajor : R ≤ B)
    (s : InfectionRevealPhysicalState n)
    (hx0 : s.inactive.xIds.card = B)
    (hy0 : s.inactive.yIds.card = R)
    (hk0 : 0 < k) :
    terminalFailureMass
        (iter (lemma16CountedPathStep n h3 k)
          (cStar * q * n)
          (lemma16CountedPathInitial s))
        (Lemma16CountedPathGood a rho cStar)
      ≤ lemma16Error q cStar rho := by
  let K := lemma16CountedPathStep n h3 k
  let T := cStar * q * n
  let q₀ := lemma16CountedPathInitial s
  let μ := iter K T q₀
  let Reached : Lemma16CountedPathState n → Prop :=
    fun z => a ≤ z.path.current.coarse.1.active
  let PrefixBad : Lemma16CountedPathState n → Prop :=
    Lemma16CountedPathPrefixBad s rho k
  let CountBad : Lemma16CountedPathState n → Prop :=
    fun z => 4 * cStar * rho < 3 * z.allActiveCount
  have ha : a ≤ n := by
    omega
  have hids :
      s.inactive.ids.card = nu := by
    have hlabels :=
      InfectionInactiveView.xIds_card_add_yIds_card
        s.inactive
    omega
  have htotal := s.coarse.2
  simp only [InfectionCfg.Inv, InfectionCfg.total] at htotal
  have hinactive := s.hinactiveCard
  have hstartEq : s.coarse.1.active = 1 := by
    omega
  have hstart : 1 ≤ s.coarse.1.active := by
    omega
  have hanchorActive :
      s.coarse.1.active + k = a := by
    omega
  have hmean :
      q * a ^ 3 ≤ rho * n ^ 2 :=
    lemma16_active_mean_cap
      (by omega) hroot hqa
  have hinitialInv :
      Lemma16CountedPathInv s k q₀ := by
    constructor
    · rfl
    · simp [q₀, lemma16CountedPathInitial,
        infectionRevealPhysicalPathInitial]
  have hepidemic :
      terminalFailureMass μ Reached ≤
        lemma16EpidemicError q := by
    simpa [μ, K, T, q₀, Reached] using
      lemma16CountedPath_epidemic_deadline
        n q a k cStar h3 hlog hquarter hcStar
        s hstart hanchorActive
  have hprefixEver :
      everHit PrefixBad K q₀ ≤
        lemma16UrnError q := by
    simpa [PrefixBad, K, q₀] using
      lemma16CountedPath_prefix_tail
        n h3 q rho a k u nu R B s
        hqa hnu hk huk hRB hquarter hmajor
        hx0 hy0 hk0
  have hprefixTerminal :
      terminalFailureMass μ
          (fun z => ¬ PrefixBad z) ≤
        lemma16UrnError q := by
    calc
      terminalFailureMass μ (fun z => ¬ PrefixBad z)
          ≤ hitProb PrefixBad K T q₀ := by
            simpa [μ] using
              terminalEventMass_iter_le_hitProb
                PrefixBad K T q₀
      _ ≤ everHit PrefixBad K q₀ := by
            exact le_iSup
              (fun U => hitProb PrefixBad K U q₀) T
      _ ≤ lemma16UrnError q := hprefixEver
  have hreaction :
      terminalFailureMass μ
          (fun z => ¬ CountBad z) ≤
        lemma16ReactionError cStar rho := by
    have heq :
        terminalFailureMass μ
            (fun z => ¬ CountBad z) =
          ∑' z, if CountBad z then μ z else 0 := by
      unfold terminalFailureMass
      apply tsum_congr
      intro z
      by_cases hz : CountBad z <;> simp [hz]
    rw [heq]
    simpa [μ, K, T, q₀, CountBad] using
      lemma16CountedPath_reaction_tail
        n h3 a k ha s hanchorActive
        q rho cStar hmean
  have hpoint :
      ∀ z,
        (if Lemma16CountedPathGood a rho cStar z then
            0
          else μ z) ≤
        (if Reached z then 0 else μ z) +
          (if PrefixBad z then μ z else 0) +
          (if CountBad z then μ z else 0) := by
    intro z
    by_cases hzμ : μ z = 0
    · simp [hzμ]
    have hinv :
        Lemma16CountedPathInv s k z :=
      iter_support_closed K
        (Lemma16CountedPathInv s k)
        (fun x hx y hy =>
          lemma16CountedPathStep_inv_closed
            n h3 k s x y hx hy)
        T q₀ z hinitialInv hzμ
    have hgap :
        Lemma16CountedPathGapLedger z := by
      exact
        lemma16CountedPath_iter_gapLedger
          n h3 k T s z
          (by simpa [μ, K, T, q₀] using hzμ)
    have hleft :
        (if Lemma16CountedPathGood a rho cStar z then
            0
          else μ z) ≤ μ z := by
      by_cases hgood :
          Lemma16CountedPathGood a rho cStar z <;>
        simp [hgood]
    by_cases hReached : Reached z
    · by_cases hPrefix : PrefixBad z
      · exact hleft.trans (by
          simp [hReached, hPrefix])
      · by_cases hCount : CountBad z
        · exact hleft.trans (by
            simp [hReached, hPrefix, hCount])
        · have hCountLe :
              3 * z.allActiveCount ≤
                4 * cStar * rho := by
            simp only [CountBad] at hCount
            omega
          have hgood :
              Lemma16CountedPathGood a rho cStar z := by
            unfold Lemma16CountedPathGood
            have hanchor :
                z.path.anchor.coarse.1.active =
                  s.coarse.1.active := by
              rw [hinv.1]
            have hledger := z.path.hactiveLedger
            have hlength := hinv.2
            have hupper :
                z.path.current.coarse.1.active ≤ a + 1 := by
              omega
            exact ⟨hReached, hupper,
              lemma16CountedPath_good_of_prefix_and_counter
                n a k rho cStar s z hk hanchorActive
                hrho (by omega) hinv hgap hReached
                hPrefix hCountLe⟩
          simp [hgood]
    · exact hleft.trans (by
        rw [if_neg hReached]
        exact
          (show μ z ≤
              (μ z +
                (if PrefixBad z then μ z else 0)) +
                (if CountBad z then μ z else 0) by
            calc
              μ z = (μ z + 0) + 0 := by simp
              _ ≤
                (μ z +
                  (if PrefixBad z then μ z else 0)) +
                  (if CountBad z then μ z else 0) :=
                add_le_add
                  (add_le_add le_rfl bot_le) bot_le))
  unfold terminalFailureMass
  calc
    (∑' z, if Lemma16CountedPathGood a rho cStar z then
        0 else μ z) ≤
      ∑' z,
        ((if Reached z then 0 else μ z) +
          (if PrefixBad z then μ z else 0) +
          (if CountBad z then μ z else 0)) :=
      ENNReal.tsum_le_tsum hpoint
    _ =
      (∑' z, if Reached z then 0 else μ z) +
        (∑' z, if PrefixBad z then μ z else 0) +
        (∑' z, if CountBad z then μ z else 0) := by
          rw [ENNReal.tsum_add, ENNReal.tsum_add]
    _ ≤ lemma16EpidemicError q +
          lemma16UrnError q +
          lemma16ReactionError cStar rho := by
      exact add_le_add
        (add_le_add hepidemic (by
          simpa [terminalFailureMass] using hprefixTerminal))
        (by simpa [terminalFailureMass] using hreaction)
    _ = lemma16Error q cStar rho := by
      unfold lemma16Error
      ac_rfl

/-- Normalized single-exponential form of Lemma 16. -/
theorem lemma16CountedPath_normalized
    (n q a k u nu R B rho cStar : ℕ)
    (h3 : 3 ≤ n)
    (hlog : Nat.log 2 n ≤ q)
    (hquarter : 4 * a ≤ n)
    (hcStar : 640 ≤ cStar)
    (hroot : a ^ 5 * q * n ≤ n ^ 5)
    (hqa : q * a ≤ rho ^ 2)
    (hqaOrder : q ≤ a)
    (hrho : 1 ≤ rho)
    (hnu : nu + 1 = n)
    (hk : k + 1 = a)
    (huk : u + k + 1 = nu)
    (hRB : R + B = nu)
    (hmajor : R ≤ B)
    (s : InfectionRevealPhysicalState n)
    (hx0 : s.inactive.xIds.card = B)
    (hy0 : s.inactive.yIds.card = R)
    (hk0 : 0 < k) :
    terminalFailureMass
        (iter (lemma16CountedPathStep n h3 k)
          (cStar * q * n)
          (lemma16CountedPathInitial s))
        (Lemma16CountedPathGood a rho cStar)
      ≤ 3 * lemma16UrnError q := by
  exact
    (lemma16CountedPath
      n q a k u nu R B rho cStar
      h3 hlog hquarter hcStar hroot hqa hrho
      hnu hk huk hRB hmajor s hx0 hy0 hk0).trans
    (lemma16_error_envelope q cStar rho
      (lemma16_q_le_rho hqaOrder hqa) (by omega))

end

end Tri

#print axioms Tri.lemma16CountedPathStep_map_path
#print axioms Tri.lemma16CountedPathStep_map_counter_of_live
#print axioms Tri.infectionRevealWordXCount_append_of_disjoint
#print axioms Tri.infectionRevealWordXCount_add_YCount
#print axioms Tri.InfectionRevealRecord.revealedX_card_add_after
#print axioms Tri.InfectionRevealRecord.revealedY_card_add_after
#print axioms Tri.InfectionEvent.gap_charge_of_inactive_ledgers
#print axioms Tri.InfectionRevealRecord.gap_charge
#print axioms Tri.Lemma16CountedPathGapLedger.afterRecord
#print axioms Tri.lemma16CountedPathStep_gapLedger_closed
#print axioms Tri.lemma16CountedPath_iter_gapLedger
#print axioms Tri.lemma16CountedPath_good_of_prefix_and_counter
#print axioms Tri.lemma16CountedPath_prefix_tail
#print axioms Tri.lemma16CountedPathStep_inv_closed
#print axioms Tri.lemma16CountedPathStep_map_coarse_on_inv
#print axioms Tri.lemma16CountedPath_iter_map_coarse_on_inv
#print axioms Tri.lemma16CountedPath_epidemic_deadline
#print axioms Tri.expect_lemma16CountedPathStep_allActive_le
#print axioms Tri.lemma16CountedPath_allActive_tail
#print axioms Tri.lemma16CountedPath_reaction_tail_twentieth
#print axioms Tri.lemma16CountedPath_reaction_tail
#print axioms Tri.lemma16CountedPath
#print axioms Tri.lemma16CountedPath_normalized
