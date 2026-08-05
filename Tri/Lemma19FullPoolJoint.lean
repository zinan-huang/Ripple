/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Lemma19FullPoolLabel
import Tri.Lemma19LateStage

/-!
# Full-pool label tail on the Lemma 19 joint carrier

A joint full-activation path is stopped later than the physical prefix needed
by the label estimate.  The first theorem below records the exact earlier
quotient of such a later-stopped path.  The remaining results exclude the
last two prefix lengths deterministically and transfer the full-pool urn tail
to `Lemma17LabelBad`.
-/

namespace Tri

open scoped ENNReal

noncomputable section

/-- Stopping a physical path at a later prefix `r` still projects exactly to
the absorbing first-`k` quotient whenever `k ≤ r`. -/
theorem infectionRevealPhysicalFirstKStep_map_earlierQuotient
    (n : ℕ) (h3 : 3 ≤ n) (k r : ℕ)
    (hkr : k ≤ r)
    (q : InfectionRevealPhysicalPathState n) :
    (infectionRevealPhysicalFirstKStep n h3 r q).map
        (InfectionRevealFirstKQuotient.ofPath k) =
      InfectionRevealFirstKQuotient.step n h3 k
        (InfectionRevealFirstKQuotient.ofPath k q) := by
  by_cases hr : r ≤ q.revealed.length
  · have hreach :
        InfectionRevealPhysicalFirstKReached r q := by
      simpa [InfectionRevealPhysicalFirstKReached] using hr
    have hk : k ≤ q.revealed.length := hkr.trans hr
    unfold infectionRevealPhysicalFirstKStep
    rw [freeze_of_mem q hreach, PMF.pure_map]
    simp [InfectionRevealFirstKQuotient.ofPath,
      InfectionRevealFirstKQuotient.step, hk]
  · have hnot :
        ¬ InfectionRevealPhysicalFirstKReached r q := by
      simpa [InfectionRevealPhysicalFirstKReached] using hr
    unfold infectionRevealPhysicalFirstKStep
    rw [freeze_of_not_mem q hnot]
    by_cases hk : k ≤ q.revealed.length
    · have htake :
          ∀ rec : InfectionRevealRecord q.current,
            (q.revealed ++ rec.revealedIds).take k =
              q.revealed.take k := by
        intro rec
        exact List.take_append_of_le_length hk
      change
        (((infectionRevealRecordPMF n h3 q.current).map
            (InfectionRevealPhysicalPathState.afterRecord q)).map
            (InfectionRevealFirstKQuotient.ofPath k)) =
          InfectionRevealFirstKQuotient.step n h3 k
            (InfectionRevealFirstKQuotient.ofPath k q)
      rw [PMF.map_comp]
      have hfun :
          (InfectionRevealFirstKQuotient.ofPath k ∘
              InfectionRevealPhysicalPathState.afterRecord q) =
            fun _ =>
              InfectionRevealFirstKQuotient.done
                (q.revealed.take k) := by
        funext rec
        simp [Function.comp_apply,
          InfectionRevealFirstKQuotient.ofPath,
          InfectionRevealPhysicalPathState.afterRecord,
          htake rec] <;> omega
      rw [hfun]
      have hqDone :
          InfectionRevealFirstKQuotient.ofPath k q =
            InfectionRevealFirstKQuotient.done
              (q.revealed.take k) := by
        simp [InfectionRevealFirstKQuotient.ofPath, hk]
      rw [hqDone]
      change
        (infectionRevealRecordPMF n h3 q.current).map
            (fun _ =>
              InfectionRevealFirstKQuotient.done
                (q.revealed.take k)) =
          PMF.pure
            (InfectionRevealFirstKQuotient.done
              (q.revealed.take k))
      simpa only [Function.const_def] using
        PMF.map_const
          (infectionRevealRecordPMF n h3 q.current)
          (InfectionRevealFirstKQuotient.done
            (q.revealed.take k))
    · have hq :
          InfectionRevealFirstKQuotient.ofPath k q =
            .live q.current q.revealed := by
        simp [InfectionRevealFirstKQuotient.ofPath, hk]
      rw [hq]
      change
        (((infectionRevealRecordPMF n h3 q.current).map
            (InfectionRevealPhysicalPathState.afterRecord q)).map
            (InfectionRevealFirstKQuotient.ofPath k)) =
          (infectionRevealRecordPMF n h3 q.current).map
            (fun rec =>
              InfectionRevealFirstKQuotient.afterRecord
                (k := k) q.revealed rec)
      rw [PMF.map_comp]
      congr 1

/-- Kernel-level earlier quotient of a later-stopped physical path. -/
theorem infectionRevealPhysicalFirstKStep_intertwines_earlierQuotient
    (n : ℕ) (h3 : 3 ≤ n) (k r : ℕ)
    (hkr : k ≤ r) :
    Intertwines
      (InfectionRevealFirstKQuotient.ofPath k)
      (infectionRevealPhysicalFirstKStep n h3 r)
      (InfectionRevealFirstKQuotient.step n h3 k) :=
  infectionRevealPhysicalFirstKStep_map_earlierQuotient
    n h3 k r hkr

/-- A physical bad-prefix witness cannot occur at either of the last two
prefix lengths of a majority-`X` pool. -/
theorem lemma19PhysicalLabelBad_implies_earlyLogicalMax
    {n : ℕ}
    (D k B R : ℕ)
    (s : InfectionRevealPhysicalState n)
    (q : InfectionRevealPhysicalPathState n)
    (hD : 0 < D)
    (hpool : k + 2 = B + R)
    (hmajor : R ≤ B)
    (hanchor : q.anchor = s)
    (hx0 : s.inactive.xIds.card = B)
    (hy0 : s.inactive.yIds.card = R)
    (hbad :
      ∃ j, j ≤ q.revealed.length ∧
        infectionRevealWordXCount
              q.anchor.inactive.initialLabel
              (q.revealed.take j) + D <
          infectionRevealWordYCount
            q.anchor.inactive.initialLabel
            (q.revealed.take j)) :
    Lemma17LogicalMaxLabelBad
      s.inactive.initialLabel D
      (InfectionRevealPrefixCheckpoint.ofPhysical
        (InfectionRevealFirstKQuotient.ofPath k q)) := by
  rcases hbad with ⟨j, hjLength, hjBad⟩
  let word := q.revealed.take j
  have hwordNodup : word.Nodup :=
    q.hnodup.take
  have hwordLength : word.length = j := by
    dsimp only [word]
    rw [List.length_take, min_eq_left hjLength]
  have hselected :
      infectionRevealWordXCount
            q.anchor.inactive.initialLabel word +
          infectionRevealWordYCount
            q.anchor.inactive.initialLabel word =
        j := by
    rw [infectionRevealWordXCount_add_YCount
      q.anchor.inactive.initialLabel word hwordNodup,
      hwordLength]
  have hYSubset :
      word.toFinset.filter
          (fun i =>
            q.anchor.inactive.initialLabel i = .Y) ⊆
        q.anchor.inactive.yIds := by
    intro i hi
    have hiWord :
        i ∈ word := List.mem_toFinset.mp
          (Finset.mem_of_subset
            (Finset.filter_subset _ _) hi)
    have hiRevealed : i ∈ q.revealed :=
      (List.take_sublist j q.revealed).mem hiWord
    have hiAnchorIds : i ∈ q.anchor.inactive.ids := by
      rw [← q.hpartition]
      exact Finset.mem_union_left _
        (List.mem_toFinset.mpr hiRevealed)
    have hiLabel :
        q.anchor.inactive.initialLabel i = .Y :=
      (Finset.mem_filter.mp hi).2
    simpa [InfectionInactiveView.yIds,
      hiAnchorIds, hiLabel]
  have hYLe :
      infectionRevealWordYCount
          q.anchor.inactive.initialLabel word ≤ R := by
    unfold infectionRevealWordYCount
    calc
      (word.toFinset.filter
          (fun i =>
            q.anchor.inactive.initialLabel i = .Y)).card
          ≤ q.anchor.inactive.yIds.card :=
        Finset.card_le_card hYSubset
      _ = s.inactive.yIds.card := by rw [hanchor]
      _ = R := hy0
  have hj : j ≤ k := by
    by_contra hjk
    have hanchorCard :
        q.anchor.inactive.ids.card = B + R := by
      calc
        q.anchor.inactive.ids.card =
            q.anchor.inactive.xIds.card +
              q.anchor.inactive.yIds.card := by
          rw [
            InfectionInactiveView.xIds_card_add_yIds_card]
        _ = s.inactive.xIds.card +
              s.inactive.yIds.card := by rw [hanchor]
        _ = B + R := by rw [hx0, hy0]
    have hjPool : j ≤ B + R := by
      have hledger := q.revealed_length_add_current
      omega
    dsimp only [word] at hjBad hselected hYLe
    omega
  unfold Lemma17LogicalMaxLabelBad
    lemma17WordPrefixBad
  by_cases hreach : k ≤ q.revealed.length
  · simp only [InfectionRevealFirstKQuotient.ofPath,
      hreach, if_pos,
      InfectionRevealPrefixCheckpoint.ofPhysical,
      InfectionRevealPrefixCheckpoint.word]
    refine ⟨j, ?_, ?_⟩
    · rw [List.length_take, min_eq_left hreach]
      exact hj
    · rw [List.take_take, min_eq_left hj]
      simpa [hanchor] using hjBad
  · simp only [InfectionRevealFirstKQuotient.ofPath,
      hreach, if_neg,
      InfectionRevealPrefixCheckpoint.ofPhysical,
      InfectionRevealPrefixCheckpoint.word]
    refine ⟨j, hjLength, ?_⟩
    simpa [hanchor] using hjBad

/-- Project a joint path to an earlier physical prefix quotient. -/
def lemma19CountedPathToEarlierQuotient
    {n : ℕ} (k : ℕ)
    (q : Lemma17CountedPathState n) :
    InfectionRevealFirstKQuotient n k :=
  InfectionRevealFirstKQuotient.ofPath k
    q.counted.path

/-- A joint path stopped after `r` reveals projects exactly to every earlier
first-`k` physical quotient. -/
theorem lemma17CountedPathStep_map_earlierQuotient
    (n : ℕ) (h3 : 3 ≤ n)
    (k r A G : ℕ) (hkr : k ≤ r)
    (q : Lemma17CountedPathState n) :
    (lemma17CountedPathStep n h3 r A G q).map
        (lemma19CountedPathToEarlierQuotient k) =
      InfectionRevealFirstKQuotient.step n h3 k
        (lemma19CountedPathToEarlierQuotient k q) := by
  calc
    (lemma17CountedPathStep n h3 r A G q).map
        (lemma19CountedPathToEarlierQuotient k) =
      ((lemma17CountedPathStep n h3 r A G q).map
          lemma17CountedPathToPath).map
        (InfectionRevealFirstKQuotient.ofPath k) := by
          rw [PMF.map_comp]
          rfl
    _ =
      (infectionRevealPhysicalFirstKStep
          n h3 r q.counted.path).map
        (InfectionRevealFirstKQuotient.ofPath k) := by
          rw [lemma17CountedPathStep_map_path]
    _ =
      InfectionRevealFirstKQuotient.step n h3 k
        (InfectionRevealFirstKQuotient.ofPath k
          q.counted.path) :=
      infectionRevealPhysicalFirstKStep_map_earlierQuotient
        n h3 k r hkr q.counted.path
    _ =
      InfectionRevealFirstKQuotient.step n h3 k
        (lemma19CountedPathToEarlierQuotient k q) := rfl

/-- Kernel-level joint projection to an earlier physical quotient. -/
theorem lemma17CountedPathStep_intertwines_earlierQuotient
    (n : ℕ) (h3 : 3 ≤ n)
    (k r A G : ℕ) (hkr : k ≤ r) :
    Intertwines
      (lemma19CountedPathToEarlierQuotient k)
      (lemma17CountedPathStep n h3 r A G)
      (InfectionRevealFirstKQuotient.step n h3 k) :=
  lemma17CountedPathStep_map_earlierQuotient
    n h3 k r A G hkr

/-- The full-pool estimate controls the first bad prefix of the genuine
physical reveal word on the joint carrier. -/
theorem lemma19CountedPath_full_physical_label_hitProb
    (n : ℕ) (h3 : 3 ≤ n)
    (L : ℝ) (D k r B R T : ℕ)
    (s : InfectionRevealPhysicalState n)
    (hanchorActive : s.coarse.1.active + r = n)
    (hD : 0 < D)
    (hk : 0 < k)
    (hpool : k + 2 = B + R)
    (hmajor : R ≤ B)
    (hx0 : s.inactive.xIds.card = B)
    (hy0 : s.inactive.yIds.card = R)
    (hscale :
      L * ((B + R : ℕ) : ℝ) ≤
        ((D : ℝ) / 2) ^ 2) :
    hitProb (Lemma17PhysicalLabelBad D)
        (lemma17CountedPathStep n h3 r n 0)
        T (lemma17CountedPathInitial s)
      ≤
    (k + 2 : ℝ≥0∞) *
      (2 * ENNReal.ofReal (Real.exp (-L))) := by
  let K := lemma17CountedPathStep n h3 r n 0
  let q₀ := lemma17CountedPathInitial s
  let PhysicalBad : Lemma17CountedPathState n → Prop :=
    Lemma17PhysicalLabelBad D
  let QuotientBad : InfectionRevealFirstKQuotient n k → Prop :=
    fun z =>
      Lemma17LogicalMaxLabelBad
        s.inactive.initialLabel D
        (InfectionRevealPrefixCheckpoint.ofPhysical z)
  let P : Lemma17CountedPathState n → Prop :=
    Lemma17CountedPathInv s r n 0
  have hrPool : r = B + R := by
    have htotal :=
      infectionReveal_active_add_inactive s
    have hpoolIds :
        s.inactive.ids.card = B + R := by
      calc
        s.inactive.ids.card =
            s.inactive.xIds.card +
              s.inactive.yIds.card := by
          rw [
            InfectionInactiveView.xIds_card_add_yIds_card]
        _ = B + R := by rw [hx0, hy0]
    omega
  have hkr : k ≤ r := by omega
  have hclosed :
      ∀ x, P x → ∀ y, K x y ≠ 0 → P y := by
    intro x hx y hy
    exact
      lemma17CountedPathStep_inv_closed
        n h3 r n 0 s hanchorActive x y hx hy
  have hcontain :
      ∀ z, P z → PhysicalBad z →
        QuotientBad
          (lemma19CountedPathToEarlierQuotient k z) := by
    intro z hz hbad
    exact
      lemma19PhysicalLabelBad_implies_earlyLogicalMax
        D k B R s z.counted.path
        hD hpool hmajor hz.1.1 hx0 hy0
        (by simpa [PhysicalBad, Lemma17PhysicalLabelBad] using hbad)
  have hinitial : P q₀ :=
    lemma17CountedPathInitial_inv s r n 0
  have hmono :
      hitProb PhysicalBad K T q₀ ≤
        hitProb
          (fun z =>
            QuotientBad
              (lemma19CountedPathToEarlierQuotient k z))
          K T q₀ :=
    hitProb_mono_target_of_support_invariant
      K PhysicalBad
      (fun z =>
        QuotientBad
          (lemma19CountedPathToEarlierQuotient k z))
      P hclosed hcontain T q₀ hinitial
  have hintertwines :
      Intertwines
        (lemma19CountedPathToEarlierQuotient k)
        K
        (InfectionRevealFirstKQuotient.step n h3 k) :=
    lemma17CountedPathStep_intertwines_earlierQuotient
      n h3 k r n 0 hkr
  have htransfer :
      hitProb
          (fun z =>
            QuotientBad
              (lemma19CountedPathToEarlierQuotient k z))
          K T q₀ =
        hitProb QuotientBad
          (InfectionRevealFirstKQuotient.step n h3 k)
          T (lemma19CountedPathToEarlierQuotient k q₀) :=
    hitProb_transfer hintertwines QuotientBad T q₀
  have hfinite :
      hitProb QuotientBad
          (InfectionRevealFirstKQuotient.step n h3 k)
          T (lemma19CountedPathToEarlierQuotient k q₀)
        ≤
      everHit QuotientBad
          (InfectionRevealFirstKQuotient.step n h3 k)
          (lemma19CountedPathToEarlierQuotient k q₀) :=
    le_iSup
      (fun U =>
        hitProb QuotientBad
          (InfectionRevealFirstKQuotient.step n h3 k)
          U (lemma19CountedPathToEarlierQuotient k q₀)) T
  have hquotient :
      everHit QuotientBad
          (InfectionRevealFirstKQuotient.step n h3 k)
          (lemma19CountedPathToEarlierQuotient k q₀)
        ≤
      (k + 2 : ℝ≥0∞) *
        (2 * ENNReal.ofReal (Real.exp (-L))) := by
    have hphysical :=
      infectionRevealPhysical_lemma19_full_prefix_tail
        n h3 L D k B R s hD hk hpool hmajor
        hx0 hy0 hscale
    have heq :
        everHit
            (fun z =>
              QuotientBad
                (InfectionRevealFirstKQuotient.ofPath k z))
            (infectionRevealPhysicalFirstKStep n h3 k)
            (infectionRevealPhysicalPathInitial s) =
          everHit QuotientBad
            (InfectionRevealFirstKQuotient.step n h3 k)
            (InfectionRevealFirstKQuotient.ofPath k
              (infectionRevealPhysicalPathInitial s)) := by
      unfold everHit
      exact
        iSup_hitProb_transfer
          (infectionRevealPhysicalFirstKStep_intertwines_quotient
            n h3 k)
          QuotientBad
          (infectionRevealPhysicalPathInitial s)
    have hq₀ :
        lemma19CountedPathToEarlierQuotient k q₀ =
          InfectionRevealFirstKQuotient.ofPath k
            (infectionRevealPhysicalPathInitial s) := by
      rfl
    rw [hq₀, ← heq]
    simpa [QuotientBad] using hphysical
  calc
    hitProb (Lemma17PhysicalLabelBad D)
        (lemma17CountedPathStep n h3 r n 0)
        T (lemma17CountedPathInitial s) =
      hitProb PhysicalBad K T q₀ := rfl
    _ ≤
      hitProb
        (fun z =>
          QuotientBad
            (lemma19CountedPathToEarlierQuotient k z))
        K T q₀ := hmono
    _ =
      hitProb QuotientBad
        (InfectionRevealFirstKQuotient.step n h3 k)
        T (lemma19CountedPathToEarlierQuotient k q₀) :=
      htransfer
    _ ≤
      everHit QuotientBad
        (InfectionRevealFirstKQuotient.step n h3 k)
        (lemma19CountedPathToEarlierQuotient k q₀) :=
      hfinite
    _ ≤
      (k + 2 : ℝ≥0∞) *
        (2 * ENNReal.ofReal (Real.exp (-L))) :=
      hquotient

/-- The maximal immutable-label estimate for a full-activation joint path,
with no remaining probabilistic premise. -/
theorem lemma19CountedPath_full_label_tail
    (n : ℕ) (h3 : 3 ≤ n)
    (L : ℝ) (D k r B R T : ℕ)
    (s : InfectionRevealPhysicalState n)
    (hanchorActive : s.coarse.1.active + r = n)
    (hD : 0 < D)
    (hk : 0 < k)
    (hpool : k + 2 = B + R)
    (hmajor : R ≤ B)
    (hx0 : s.inactive.xIds.card = B)
    (hy0 : s.inactive.yIds.card = R)
    (hscale :
      L * ((B + R : ℕ) : ℝ) ≤
        ((D : ℝ) / 2) ^ 2) :
    terminalFailureMass
        (iter
          (lemma17CountedPathStep n h3 r n 0)
          T (lemma17CountedPathInitial s))
        (fun z => ¬ Lemma17LabelBad D z)
      ≤
    (k + 2 : ℝ≥0∞) *
      (2 * ENNReal.ofReal (Real.exp (-L))) := by
  let K := lemma17CountedPathStep n h3 r n 0
  let q₀ := lemma17CountedPathInitial s
  let μ := iter K T q₀
  let LabelBad : Lemma17CountedPathState n → Prop :=
    Lemma17LabelBad D
  let QuotientBad : InfectionRevealFirstKQuotient n k → Prop :=
    fun z =>
      Lemma17LogicalMaxLabelBad
        s.inactive.initialLabel D
        (InfectionRevealPrefixCheckpoint.ofPhysical z)
  let P : Lemma17CountedPathState n → Prop :=
    fun z =>
      Lemma17CountedPathInv s r n 0 z ∧
        Lemma17ReactionLabelInv n 0 z
  have hpoolIds :
      s.inactive.ids.card = B + R := by
    calc
      s.inactive.ids.card =
          s.inactive.xIds.card +
            s.inactive.yIds.card := by
        rw [
          InfectionInactiveView.xIds_card_add_yIds_card]
      _ = B + R := by rw [hx0, hy0]
  have hrPool : r = B + R := by
    have htotal :=
      infectionReveal_active_add_inactive s
    omega
  have hkr : k ≤ r := by omega
  have hclosed :
      ∀ x, P x → ∀ y, K x y ≠ 0 → P y := by
    intro x hx y hy
    exact
      ⟨lemma17CountedPathStep_inv_closed
          n h3 r n 0 s hanchorActive x y hx.1 hy,
        lemma17CountedPathStep_labelInv_closed
          n h3 r n 0 x y hx.2 hy⟩
  have hcontain :
      ∀ z, P z → LabelBad z →
        QuotientBad
          (lemma19CountedPathToEarlierQuotient k z) := by
    intro z hz hbad
    have hphysical :
        Lemma17PhysicalLabelBad D z :=
      lemma17LabelBad_implies_physical
        n 0 D z hz.2 hbad
    exact
      lemma19PhysicalLabelBad_implies_earlyLogicalMax
        D k B R s z.counted.path
        hD hpool hmajor hz.1.1.1 hx0 hy0
        (by simpa [Lemma17PhysicalLabelBad] using hphysical)
  have hinitial : P q₀ :=
    ⟨lemma17CountedPathInitial_inv s r n 0,
      lemma17CountedPathInitial_labelInv n 0 s⟩
  have hterminal :
      terminalFailureMass μ (fun z => ¬ LabelBad z) ≤
        hitProb LabelBad K T q₀ :=
    terminalEventMass_iter_le_hitProb
      LabelBad K T q₀
  have hmono :
      hitProb LabelBad K T q₀ ≤
        hitProb
          (fun z =>
            QuotientBad
              (lemma19CountedPathToEarlierQuotient k z))
          K T q₀ :=
    hitProb_mono_target_of_support_invariant
      K LabelBad
      (fun z =>
        QuotientBad
          (lemma19CountedPathToEarlierQuotient k z))
      P hclosed hcontain T q₀ hinitial
  have hintertwines :
      Intertwines
        (lemma19CountedPathToEarlierQuotient k)
        K
        (InfectionRevealFirstKQuotient.step n h3 k) :=
    lemma17CountedPathStep_intertwines_earlierQuotient
      n h3 k r n 0 hkr
  have htransfer :
      hitProb
          (fun z =>
            QuotientBad
              (lemma19CountedPathToEarlierQuotient k z))
          K T q₀ =
        hitProb QuotientBad
          (InfectionRevealFirstKQuotient.step n h3 k)
          T (lemma19CountedPathToEarlierQuotient k q₀) :=
    hitProb_transfer hintertwines QuotientBad T q₀
  have hfinite :
      hitProb QuotientBad
          (InfectionRevealFirstKQuotient.step n h3 k)
          T (lemma19CountedPathToEarlierQuotient k q₀)
        ≤
      everHit QuotientBad
          (InfectionRevealFirstKQuotient.step n h3 k)
          (lemma19CountedPathToEarlierQuotient k q₀) :=
    le_iSup
      (fun U =>
        hitProb QuotientBad
          (InfectionRevealFirstKQuotient.step n h3 k)
          U (lemma19CountedPathToEarlierQuotient k q₀)) T
  have hquotient :
      everHit QuotientBad
          (InfectionRevealFirstKQuotient.step n h3 k)
          (lemma19CountedPathToEarlierQuotient k q₀)
        ≤
      (k + 2 : ℝ≥0∞) *
        (2 * ENNReal.ofReal (Real.exp (-L))) := by
    have hphysical :=
      infectionRevealPhysical_lemma19_full_prefix_tail
        n h3 L D k B R s hD hk hpool hmajor
        hx0 hy0 hscale
    have heq :
        everHit
            (fun z =>
              QuotientBad
                (InfectionRevealFirstKQuotient.ofPath k z))
            (infectionRevealPhysicalFirstKStep n h3 k)
            (infectionRevealPhysicalPathInitial s) =
          everHit QuotientBad
            (InfectionRevealFirstKQuotient.step n h3 k)
            (InfectionRevealFirstKQuotient.ofPath k
              (infectionRevealPhysicalPathInitial s)) := by
      unfold everHit
      exact
        iSup_hitProb_transfer
          (infectionRevealPhysicalFirstKStep_intertwines_quotient
            n h3 k)
          QuotientBad
          (infectionRevealPhysicalPathInitial s)
    have hq₀ :
        lemma19CountedPathToEarlierQuotient k q₀ =
          InfectionRevealFirstKQuotient.ofPath k
            (infectionRevealPhysicalPathInitial s) := by
      rfl
    rw [hq₀, ← heq]
    simpa [QuotientBad] using hphysical
  calc
    terminalFailureMass
        (iter
          (lemma17CountedPathStep n h3 r n 0)
          T (lemma17CountedPathInitial s))
        (fun z => ¬ Lemma17LabelBad D z)
        ≤ hitProb LabelBad K T q₀ := by
          simpa [μ, K, q₀, LabelBad] using hterminal
    _ ≤
      hitProb
        (fun z =>
          QuotientBad
            (lemma19CountedPathToEarlierQuotient k z))
        K T q₀ := hmono
    _ =
      hitProb QuotientBad
        (InfectionRevealFirstKQuotient.step n h3 k)
        T (lemma19CountedPathToEarlierQuotient k q₀) :=
      htransfer
    _ ≤
      everHit QuotientBad
        (InfectionRevealFirstKQuotient.step n h3 k)
        (lemma19CountedPathToEarlierQuotient k q₀) :=
      hfinite
    _ ≤
      (k + 2 : ℝ≥0∞) *
        (2 * ENNReal.ofReal (Real.exp (-L))) :=
      hquotient

/-- Full-activation Lemma 19 with its global label estimate discharged. -/
theorem lemma19CountedPath_full_activation_closed
    (n r k B R a H Dstart Dlabel M targetGap : ℕ)
    (L : ℝ)
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
    (hDlabel : 0 < Dlabel)
    (hk : 0 < k)
    (hpool : k + 2 = B + R)
    (hmajor : R ≤ B)
    (hx0 : s.inactive.xIds.card = B)
    (hy0 : s.inactive.yIds.card = R)
    (hscale :
      L * ((B + R : ℕ) : ℝ) ≤
        ((Dlabel : ℝ) / 2) ^ 2)
    (w : ℝ≥0∞) (hw1 : 1 ≤ w) (hwt : w ≠ ⊤) :
    terminalFailureMass
        (iter
          (lemma17CountedPathStep n h3 r n 0)
          (infectionLateStages r * (1024 * n))
          (lemma17CountedPathInitial s))
        (Lemma19StageGood n targetGap)
      ≤
    ((infectionLateError r +
        ((k + 2 : ℝ≥0∞) *
          (2 * ENNReal.ofReal (Real.exp (-L))))) +
        (infectionAllActiveCubeCompl n n +
            infectionAllActiveCube n n * w) ^
              (infectionLateStages r * (1024 * n)) /
          w ^ (H + 1)) +
      ENNReal.ofReal
        (Real.exp
          (-((M : ℝ) ^ 2 / (8 * (H : ℝ))))) := by
  have hlabel :=
    lemma19CountedPath_full_label_tail
      n h3 L Dlabel k r B R
      (infectionLateStages r * (1024 * n))
      s hanchorActive hDlabel hk hpool hmajor
      hx0 hy0 hscale
  exact
    lemma19CountedPath_full_activation
      n r a H Dstart Dlabel M targetGap
      h3 ha hH s hstartActive hanchorActive
      hquarter hstart hbudget w hw1 hwt
      ((k + 2 : ℝ≥0∞) *
        (2 * ENNReal.ofReal (Real.exp (-L))))
      hlabel

/-- Physical endpoint of the closed full-activation Lemma 19 stage. -/
theorem lemma19PhysicalStage_full_activation_closed
    (n r k B R a H Dstart Dlabel M targetGap : ℕ)
    (L : ℝ)
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
    (hDlabel : 0 < Dlabel)
    (hk : 0 < k)
    (hpool : k + 2 = B + R)
    (hmajor : R ≤ B)
    (hx0 : s.inactive.xIds.card = B)
    (hy0 : s.inactive.yIds.card = R)
    (hscale :
      L * ((B + R : ℕ) : ℝ) ≤
        ((Dlabel : ℝ) / 2) ^ 2)
    (w : ℝ≥0∞) (hw1 : 1 ≤ w) (hwt : w ≠ ⊤) :
    terminalFailureMass
        (lemma17PhysicalStageKernel
          n h3 r n 0
          (infectionLateStages r * (1024 * n)) s)
        (Lemma19PhysicalStageRangeGood n targetGap)
      ≤
    ((infectionLateError r +
        ((k + 2 : ℝ≥0∞) *
          (2 * ENNReal.ofReal (Real.exp (-L))))) +
        (infectionAllActiveCubeCompl n n +
            infectionAllActiveCube n n * w) ^
              (infectionLateStages r * (1024 * n)) /
          w ^ (H + 1)) +
      ENNReal.ofReal
        (Real.exp
          (-((M : ℝ) ^ 2 / (8 * (H : ℝ))))) := by
  let ε :=
    ((infectionLateError r +
        ((k + 2 : ℝ≥0∞) *
          (2 * ENNReal.ofReal (Real.exp (-L))))) +
        (infectionAllActiveCubeCompl n n +
            infectionAllActiveCube n n * w) ^
              (infectionLateStages r * (1024 * n)) /
          w ^ (H + 1)) +
      ENNReal.ofReal
        (Real.exp
          (-((M : ℝ) ^ 2 / (8 * (H : ℝ)))))
  apply
    lemma19PhysicalStage_range
      n h3 r n targetGap
      (infectionLateStages r * (1024 * n))
      s hanchorActive ε
  apply
    lemma19PhysicalStage_of_counted
      n h3 r n targetGap
      (infectionLateStages r * (1024 * n))
      s ε
  exact
    lemma19CountedPath_full_activation_closed
      n r k B R a H Dstart Dlabel M targetGap
      L h3 ha hH s hstartActive hanchorActive
      hquarter hstart hbudget hDlabel hk hpool
      hmajor hx0 hy0 hscale w hw1 hwt

end

end Tri

#print axioms Tri.infectionRevealPhysicalFirstKStep_map_earlierQuotient
#print axioms Tri.infectionRevealPhysicalFirstKStep_intertwines_earlierQuotient
#print axioms Tri.lemma19PhysicalLabelBad_implies_earlyLogicalMax
#print axioms Tri.lemma17CountedPathStep_map_earlierQuotient
#print axioms Tri.lemma17CountedPathStep_intertwines_earlierQuotient
#print axioms Tri.lemma19CountedPath_full_physical_label_hitProb
#print axioms Tri.lemma19CountedPath_full_label_tail
#print axioms Tri.lemma19CountedPath_full_activation_closed
#print axioms Tri.lemma19PhysicalStage_full_activation_closed
